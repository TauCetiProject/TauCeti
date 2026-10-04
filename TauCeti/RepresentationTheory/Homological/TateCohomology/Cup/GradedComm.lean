/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex, Claude
-/
module

public import TauCeti.RepresentationTheory.Homological.TateCohomology.Cup.Delta

/-!
# Graded commutativity of the Tate cup product

For a finite group `G`, the tensor braiding identifies the two orders of the Tate cup product up to
the Koszul sign: for classes `x` of degree `p` and `y` of degree `q`,

`β (x ∪ y) = (-1)^(p * q) (y ∪ x)` (`TauCeti.TateCohomology.cup_gradedComm`).

When one class has degree zero the sign is trivial, and the result is built into the construction
of the all-degree product. The product in bidegree `(p, 0)` is `cupH0`, while the product in
bidegree `(0, p)` is its opposite transported through the tensor braiding (`cup0H`). The symmetry
identity for the braiding then gives both edge forms.

The general case follows by induction on the second degree `q`, through the upward and downward
dimension-shifting sequences of the second coefficient representation. On the left, the cup product
with a shifted class satisfies `x ∪ δ y = (-1)^p δ (x ∪ y)` by definition, and the braiding commutes
with the connecting maps. On the right, `δ y ∪ x = δ (y ∪ x)` because the dimension-shifting
sequences split `k`-linearly (`TauCeti.TateCohomology.δ_cup_of_leftInverse`). The extra sign
`(-1)^p` is the change of the Koszul sign from `(-1)^(p * q)` to `(-1)^(p * (q + 1))`.

## Main statements

* `TauCeti.TateCohomology.cupH0_eq_flip_cup0H`: graded commutativity in bidegree `(p, 0)`.
* `TauCeti.TateCohomology.cup0H_eq_flip_cupH0`: graded commutativity in bidegree `(0, q)`.
* `TauCeti.TateCohomology.cup_gradedComm`: graded commutativity in all integer bidegrees.

## References

* E. Artin and J. Tate, *Class Field Theory*, Preliminaries §2.
* K. S. Brown, *Cohomology of Groups*, Chapter VI, §5.
-/

public noncomputable section

universe u

open CategoryTheory MonoidalCategory Rep

namespace TauCeti.TateCohomology

variable {k G : Type u} [CommRing k] [Group G] [Fintype G]

/-- **Graded commutativity in bidegree `(p, 0)`**: after braiding the coefficients, cupping a
degree-`p` class with a degree-zero class agrees with cupping in the opposite order. The Koszul
sign is trivial because the second degree is zero. -/
@[simp]
theorem cupH0_eq_flip_cup0H (M N : Rep k G) (p : ℤ)
    (x : tateCohomology M p) (y : tateCohomology N 0) :
    (tateCohomologyFunctor p).map (β_ M N).hom
        (cupH0 M N p x y) =
      cup0H N M p y x := by
  rw [cup0H_apply]

/-- **Graded commutativity in bidegree `(0, q)`**: after braiding the coefficients, cupping a
degree-zero class with a degree-`q` class agrees with cupping in the opposite order. The Koszul
sign is trivial because the first degree is zero. -/
@[simp]
theorem cup0H_eq_flip_cupH0 (M N : Rep k G) (q : ℤ)
    (x : tateCohomology M 0) (y : tateCohomology N q) :
    (tateCohomologyFunctor q).map (β_ M N).hom
        (cup0H M N q x y) =
      cupH0 N M q y x := by
  rw [cup0H_apply]
  rw [← ModuleCat.comp_apply, ← Functor.map_comp, SymmetricCategory.symmetry]
  simp

/-! ### Graded commutativity in all bidegrees -/

/-- Graded commutativity when the second class has degree zero, in the form used to start the
induction in `cup_gradedComm`. -/
private theorem cup_gradedComm_zero (M N : Rep k G) {p r : ℤ} (h : p + 0 = r)
    (x : tateCohomology M p) (y : tateCohomology N 0) :
    (tateCohomologyFunctor r).map (β_ M N).hom (cup M N p 0 r h x y) =
      (p * 0).negOnePow • cup N M 0 p r (by omega) y x := by
  obtain rfl : p = r := by omega
  rw [cup_zero_right, cup_zero_left, mul_zero, Int.negOnePow_zero, one_smul]
  exact cupH0_eq_flip_cup0H M N p x y

/-- The upward step in the proof of `cup_gradedComm`: graded commutativity in bidegree `(p, q)`
for the upward shift of `N`, where `0 ≤ q`, implies it in bidegree `(p, q + 1)` for `N`. -/
private theorem cup_gradedComm_add_one (M N : Rep k G) {p q r : ℤ} (hq : 0 ≤ q)
    (h : p + q = r) (x : tateCohomology M p)
    (ih : ∀ y : tateCohomology (dimensionShiftUp N) q,
      (tateCohomologyFunctor r).map (β_ M (dimensionShiftUp N)).hom
          (cup M (dimensionShiftUp N) p q r h x y) =
        (p * q).negOnePow • cup (dimensionShiftUp N) M q p r (by omega) y x)
    (y : tateCohomology N (q + 1)) :
    (tateCohomologyFunctor (r + 1)).map (β_ M N).hom (cup M N p (q + 1) (r + 1) (by omega) x y) =
      (p * (q + 1)).negOnePow • cup N M (q + 1) p (r + 1) (by omega) y x := by
  obtain ⟨y, rfl⟩ : ∃ y', (dimensionShiftUpIso N q).hom y' = y :=
    ⟨(dimensionShiftUpIso N q).inv y, Iso.inv_hom_id_apply _ _⟩
  have hD : (ShortComplex.mk (coindBotUnit N) (dimensionShiftUpπ N)
      (coindBotUnit_comp_dimensionShiftUpπ N)).ShortExact := by
    simpa only [dimensionShiftUpSES_def] using dimensionShiftUpSES_shortExact N
  -- The braiding commutes with the connecting maps of the tensor products of the shifting sequence
  -- with `M` on either side.
  have hδ := (ConcreteCategory.congr_hom (_root_.TateCohomology.δ_naturality
    (by simpa only [dimensionShiftUpSES_def] using dimensionShiftUpSES_tensorLeft_shortExact N M)
    (haveI := hD.epi_g; Rep.shortExact_map_tensorRight_of_leftInverse hD.exact M
      (leftInverse_coindBotUnit N))
    (ShortComplex.mapNatTrans _ (BraidedCategory.tensorLeftIsoTensorRight M).hom) r)
    (cup M (dimensionShiftUp N) p q r h x y)).symm
  simp only [ModuleCat.comp_apply, ShortComplex.mapNatTrans_τ₁, ShortComplex.mapNatTrans_τ₃,
    BraidedCategory.tensorLeftIsoTensorRight_hom_app] at hδ
  rw [cup_dimensionShiftUpIso_hom M N hq h rfl, map_zsmul_unit, tensorDimensionShiftUpIso_hom,
    ← hδ, ih, map_zsmul_unit, δ_cup_of_leftInverse hD (leftInverse_coindBotUnit N) M
      (by omega : q + p = r) y x, dimensionShiftUpIso_hom, smul_smul, ← Int.negOnePow_add]
  congr 2
  ring

/-- The downward step in the proof of `cup_gradedComm`: graded commutativity in bidegree
`(p, q + 1)` for the downward shift of `N`, where `q < 0`, implies it in bidegree `(p, q)` for
`N`. -/
private theorem cup_gradedComm_of_add_one (M N : Rep k G) {p q r : ℤ} (hq : q < 0)
    (h : p + q = r) (x : tateCohomology M p)
    (ih : ∀ y : tateCohomology (dimensionShiftDown N) (q + 1),
      (tateCohomologyFunctor (r + 1)).map (β_ M (dimensionShiftDown N)).hom
          (cup M (dimensionShiftDown N) p (q + 1) (r + 1) (by omega) x y) =
        (p * (q + 1)).negOnePow • cup (dimensionShiftDown N) M (q + 1) p (r + 1) (by omega) y x)
    (y : tateCohomology N q) :
    (tateCohomologyFunctor r).map (β_ M N).hom (cup M N p q r h x y) =
      (p * q).negOnePow • cup N M q p r (by omega) y x := by
  have hD : (ShortComplex.mk (dimensionShiftDownι N) (indBotCounit N)
      (dimensionShiftDownι_comp_indBotCounit N)).ShortExact := by
    simpa only [dimensionShiftDownSES_def] using dimensionShiftDownSES_shortExact N
  obtain ⟨ρ, hρ⟩ := Rep.exists_leftInverse_of_rightInverse hD.exact (rightInverse_indBotCounit N)
  have hβ : ∀ {A B : Rep k G} (e : A ≅ B) (n : ℤ) (z : tateCohomology A n),
      (tateCohomologyFunctor n).map e.inv ((tateCohomologyFunctor n).map e.hom z) = z :=
    fun e n z ↦ Iso.hom_inv_id_apply ((tateCohomologyFunctor n).mapIso e) z
  -- The inverse braiding commutes with the connecting maps of the tensor products of the shifting
  -- sequence with `M` on either side.
  have hδ := (ConcreteCategory.congr_hom (_root_.TateCohomology.δ_naturality
    (haveI := hD.epi_g; Rep.shortExact_map_tensorRight_of_leftInverse hD.exact M hρ)
    (by simpa only [dimensionShiftDownSES_def] using
      dimensionShiftDownSES_tensorLeft_shortExact N M)
    (ShortComplex.mapNatTrans _ (BraidedCategory.tensorLeftIsoTensorRight M).inv) r)
    (cup N M q p r (by omega) y x)).symm
  simp only [ModuleCat.comp_apply, ShortComplex.mapNatTrans_τ₁, ShortComplex.mapNatTrans_τ₃,
    BraidedCategory.tensorLeftIsoTensorRight_inv_app] at hδ
  -- Move the braiding to the right-hand side, and compare both sides after the isomorphism
  -- `Ĥʳ(G, M ⊗ N) ≅ Ĥʳ⁺¹(G, M ⊗ dimensionShiftDown N)` given by the downward shift.
  rw [← hβ (β_ M N).symm r ((p * q).negOnePow • _), Iso.symm_inv, Iso.symm_hom, map_zsmul_unit]
  congr 1
  refine (tensorDimensionShiftDownIso N M r (r + 1) rfl).toLinearEquiv.injective ?_
  rw [Iso.toLinearEquiv_apply, Iso.toLinearEquiv_apply, map_zsmul_unit,
    ← negOnePow_smul_negOnePow_smul p ((tensorDimensionShiftDownIso N M r (r + 1) rfl).hom _),
    ← cup_dimensionShiftDownIso_hom M N hq h rfl x y,
    ← hβ (β_ M (dimensionShiftDown N)) (r + 1) (cup M (dimensionShiftDown N) p (q + 1) (r + 1)
      (by omega) x ((dimensionShiftDownIso N q).hom y)), ih,
    map_zsmul_unit, dimensionShiftDownIso_hom, ← δ_cup_of_leftInverse hD hρ M (by omega) y x, ← hδ,
    tensorDimensionShiftDownIso_hom, smul_smul, ← Int.negOnePow_add]
  congr 1
  rw [Int.negOnePow_eq_iff]
  exact ⟨p, by ring⟩

/-- **Graded commutativity of the Tate cup product**: after braiding the coefficients, cupping a
class `x` of degree `p` with a class `y` of degree `q` agrees with cupping in the opposite order up
to the Koszul sign, `β (x ∪ y) = (-1)^(p * q) (y ∪ x)`, in all integer bidegrees. -/
theorem cup_gradedComm (M N : Rep k G) {p q r : ℤ} (h : p + q = r) (x : tateCohomology M p)
    (y : tateCohomology N q) :
    (tateCohomologyFunctor r).map (β_ M N).hom (cup M N p q r h x y) =
      (p * q).negOnePow • cup N M q p r (by omega) y x := by
  rcases le_or_gt 0 q with hq | hq
  · induction q, hq using Int.leInduction generalizing N r with
    | base => exact cup_gradedComm_zero M N h x y
    | succ q hq ih =>
      obtain rfl : r = p + q + 1 := by omega
      exact cup_gradedComm_add_one M N hq rfl x (ih (dimensionShiftUp N) rfl) y
  · obtain ⟨m, rfl⟩ := Int.eq_negSucc_of_lt_zero hq
    clear hq
    induction m generalizing N r with
    | zero =>
      -- `Int.negSucc 0 + 1` is `0` by definition, so the hypothesis of the step is the degree-zero
      -- case.
      exact cup_gradedComm_of_add_one M N (Int.negSucc_lt_zero 0) h x
        (cup_gradedComm_zero M (dimensionShiftDown N) (by omega) x) y
    | succ m ih =>
      exact cup_gradedComm_of_add_one M N (Int.negSucc_lt_zero _) h x
        (ih (dimensionShiftDown N) (by omega)) y

end TauCeti.TateCohomology
