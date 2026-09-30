/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex, Claude
-/
module

public import TauCeti.RepresentationTheory.Homological.TateCohomology.Cup.Delta

/-!
# Associativity of the Tate cup product

For a finite group `G`, the tensor associator identifies the two ways to cup three Tate classes
`x`, `y`, `z` of arbitrary integer degrees `p`, `q`, `s`:
`α ((x ∪ y) ∪ z) = x ∪ (y ∪ z)` (`TauCeti.TateCohomology.cup_assoc`).

When `z` has degree zero both sides are computed by the degree-zero product `cupH0`. The general
case follows by induction on `s`, upwards through the dimension shift
`0 → P → Coind_⊥^G P → dimensionShiftUp P → 0` and downwards through
`0 → dimensionShiftDown P → Ind_⊥^G P → P → 0`. On the left the cup product with `z` satisfies
`(x ∪ y) ∪ δ z = (-1)^(p + q) δ ((x ∪ y) ∪ z)` by its definition, and the associator commutes with
the connecting maps. On the right, `y ∪ δ z = (-1)^q δ (y ∪ z)` by definition, and
`x ∪ δ w = (-1)^p δ (x ∪ w)` for the connecting map `δ` of the tensor product of the shifting
sequence with `N`, which is split `k`-linearly, by `TauCeti.TateCohomology.cup_δ_of_leftInverse`
in all degrees. The two signs agree.

## Main statements

* `TauCeti.TateCohomology.cup_assoc`: associativity of the Tate cup product in all integer
  tridegrees.
* `TauCeti.TateCohomology.cupH0_cup_assoc`, `TauCeti.TateCohomology.cup_cupH0_assoc`,
  `TauCeti.TateCohomology.cupH0_assoc_zero`: its forms with a degree-zero class, in the simp normal
  form where the degree-zero products are written with `cupH0` and `cup0H`.

## References

* E. Artin and J. Tate, *Class Field Theory*, Preliminaries §2.
* K. S. Brown, *Cohomology of Groups*, Chapter VI, §5.
-/

public noncomputable section

universe u

open CategoryTheory Limits MonoidalCategory Rep
open scoped TensorProduct

namespace TauCeti.TateCohomology

variable {k G : Type u} [CommRing k] [Group G] [Fintype G]

/-- Associativity of the Tate cup product when the last class has degree zero. -/
private theorem cup_assoc_zero_right (M N P : Rep k G) {p q r : ℤ} (h : p + q = r)
    (x : tateCohomology M p) (y : tateCohomology N q)
    (z : tateCohomology P 0) :
    (tateCohomologyFunctor r).map (α_ M N P).hom
      (cup (M ⊗ N) P r 0 r (by omega)
        (cup M N p q r h x y) z) =
      cup M (N ⊗ P) p q r h x
        (cup N P q 0 q (by omega) y z) := by
  induction z using H0_induction_on with
  | h z =>
    rw [cup_zero_right, cup_zero_right, cupH0_H0π, cupH0_H0π, cup_map_right,
      ← ModuleCat.comp_apply, ← Functor.map_comp,
      Rep.tensorInvariant_comp_associator]

/-! ### Associativity in all tridegrees -/

/-- The associator commutes with the connecting maps of the tensor products of a short exact
sequence with `M ⊗ N` and with `N` and then `M`. -/
private theorem map_associator_δ (M N : Rep k G) {S : ShortComplex (Rep k G)}
    (h₁ : (S.map (tensorLeft (M ⊗ N))).ShortExact)
    (h₂ : ((S.map (tensorLeft N)).map (tensorLeft M)).ShortExact) (n : ℤ)
    (w : tateCohomology ((M ⊗ N) ⊗ S.X₃) n) :
    (tateCohomologyFunctor (n + 1)).map (α_ M N S.X₁).hom (_root_.TateCohomology.δ h₁ n w) =
      _root_.TateCohomology.δ h₂ n ((tateCohomologyFunctor n).map (α_ M N S.X₃).hom w) :=
  ConcreteCategory.congr_hom
    (_root_.TateCohomology.δ_naturality h₁ h₂ (S.mapNatTrans (tensorLeftTensor M N).hom) n) w

/-- The upward step in the proof of `cup_assoc`: associativity for a last class of degree `s ≥ 0`
in the upward shift of `P` gives associativity for a last class of degree `s + 1` in `P`. -/
private theorem cup_assoc_add_one (M N P : Rep k G) {p q s r₂ r : ℤ} (hs : 0 ≤ s)
    (h₂ : q + s = r₂) (h : p + q + s = r) (x : tateCohomology M p) (y : tateCohomology N q)
    (ih : ∀ z : tateCohomology (dimensionShiftUp P) s,
      (tateCohomologyFunctor r).map (α_ M N (dimensionShiftUp P)).hom
          (cup (M ⊗ N) (dimensionShiftUp P) (p + q) s r h (cup M N p q (p + q) rfl x y) z) =
        cup M (N ⊗ dimensionShiftUp P) p r₂ r (by omega) x
          (cup N (dimensionShiftUp P) q s r₂ h₂ y z))
    (z : tateCohomology P (s + 1)) :
    (tateCohomologyFunctor (r + 1)).map (α_ M N P).hom
        (cup (M ⊗ N) P (p + q) (s + 1) (r + 1) (by omega) (cup M N p q (p + q) rfl x y) z) =
      cup M (N ⊗ P) p (r₂ + 1) (r + 1) (by omega) x
        (cup N P q (s + 1) (r₂ + 1) (by omega) y z) := by
  obtain ⟨z, rfl⟩ : ∃ z', (dimensionShiftUpIso P s).hom z' = z :=
    ⟨(dimensionShiftUpIso P s).inv z, Iso.inv_hom_id_apply _ _⟩
  have hN : ((ShortComplex.mk (coindBotUnit P) (dimensionShiftUpπ P)
      (coindBotUnit_comp_dimensionShiftUpπ P)).map (tensorLeft N)).ShortExact := by
    simpa only [dimensionShiftUpSES_def] using dimensionShiftUpSES_tensorLeft_shortExact P N
  -- On the right, the tensor product of the upward sequence of `P` with `N` is split by
  -- `N ⊗ (evaluation at 1)`, so `x ∪ δ w = (-1)^p δ (x ∪ w)` for its connecting map.
  have hR := cup_δ_of_leftInverse M hN
    (Rep.leftInverse_whiskerLeft N (coindBotUnit P) (leftInverse_coindBotUnit P))
    (show p + r₂ = r by omega) x (cup N (dimensionShiftUp P) q s r₂ h₂ y z)
  -- On the left, the associator commutes with the connecting maps.
  have hL := map_associator_δ M N (S := ShortComplex.mk (coindBotUnit P) (dimensionShiftUpπ P)
      (coindBotUnit_comp_dimensionShiftUpπ P))
    (by simpa only [dimensionShiftUpSES_def] using
      dimensionShiftUpSES_tensorLeft_shortExact P (M ⊗ N))
    (haveI := hN.epi_g; Rep.shortExact_map_tensorLeft_of_leftInverse hN.exact M _
      (Rep.leftInverse_whiskerLeft N (coindBotUnit P) (leftInverse_coindBotUnit P))) r
    (cup (M ⊗ N) (dimensionShiftUp P) (p + q) s r h (cup M N p q (p + q) rfl x y) z)
  rw [cup_dimensionShiftUpIso_hom (M ⊗ N) P hs h rfl, cup_dimensionShiftUpIso_hom N P hs h₂ rfl,
    map_zsmul_unit, map_zsmul_unit, tensorDimensionShiftUpIso_hom, tensorDimensionShiftUpIso_hom]
  dsimp only [ShortComplex.map_X₁, ShortComplex.map_X₃, curriedTensor_obj_obj] at hR
  rw [hL, ih, hR, smul_smul, ← Int.negOnePow_add, add_comm q p]

/-- The downward step in the proof of `cup_assoc`: associativity for a last class of degree
`s + 1` in the downward shift of `P`, where `s < 0`, gives associativity for a last class of
degree `s` in `P`. -/
private theorem cup_assoc_of_add_one (M N P : Rep k G) {p q s r₂ r : ℤ} (hs : s < 0)
    (h₂ : q + s = r₂) (h : p + q + s = r) (x : tateCohomology M p) (y : tateCohomology N q)
    (ih : ∀ z : tateCohomology (dimensionShiftDown P) (s + 1),
      (tateCohomologyFunctor (r + 1)).map (α_ M N (dimensionShiftDown P)).hom
          (cup (M ⊗ N) (dimensionShiftDown P) (p + q) (s + 1) (r + 1) (by omega)
            (cup M N p q (p + q) rfl x y) z) =
        cup M (N ⊗ dimensionShiftDown P) p (r₂ + 1) (r + 1) (by omega) x
          (cup N (dimensionShiftDown P) q (s + 1) (r₂ + 1) (by omega) y z))
    (z : tateCohomology P s) :
    (tateCohomologyFunctor r).map (α_ M N P).hom
        (cup (M ⊗ N) P (p + q) s r h (cup M N p q (p + q) rfl x y) z) =
      cup M (N ⊗ P) p r₂ r (by omega) x (cup N P q s r₂ h₂ y z) := by
  have hD : (ShortComplex.mk (dimensionShiftDownι P) (indBotCounit P)
      (dimensionShiftDownι_comp_indBotCounit P)).ShortExact := by
    simpa only [dimensionShiftDownSES_def] using dimensionShiftDownSES_shortExact P
  have hN : ((ShortComplex.mk (dimensionShiftDownι P) (indBotCounit P)
      (dimensionShiftDownι_comp_indBotCounit P)).map (tensorLeft N)).ShortExact := by
    simpa only [dimensionShiftDownSES_def] using dimensionShiftDownSES_tensorLeft_shortExact P N
  -- The downward sequence of `P` is split, hence so is its tensor product with `N`.
  obtain ⟨ρ, hρ⟩ := Rep.exists_leftInverse_of_rightInverse hD.exact (rightInverse_indBotCounit P)
  have hρN := Rep.leftInverse_whiskerLeft N (dimensionShiftDownι P) hρ
  have hMN : (((ShortComplex.mk (dimensionShiftDownι P) (indBotCounit P)
      (dimensionShiftDownι_comp_indBotCounit P)).map (tensorLeft N)).map
        (tensorLeft M)).ShortExact :=
    haveI := hN.epi_g; Rep.shortExact_map_tensorLeft_of_leftInverse hN.exact M _ hρN
  -- The connecting map of the tensor product of this sequence with `N` and then `M` is injective:
  -- the middle term `M ⊗ (N ⊗ Ind_⊥^G P)` has vanishing Tate cohomology.
  have hz : ∀ i, IsZero (tateCohomology (M ⊗ N ⊗ indBot k G P.V) i) := fun i ↦
    (isZero_tensor_indBot P.V (M ⊗ N) i).of_iso
      ((tateCohomologyFunctor i).mapIso (α_ M N (indBot k G P.V))).symm
  have hinj : Function.Injective (_root_.TateCohomology.δ hMN r) :=
    (ModuleCat.mono_iff_injective _).1
      ((_root_.TateCohomology.map_tateComplexFunctor_shortExact hMN).mono_δ r (r + 1) rfl (hz r))
  refine hinj ?_
  -- On the left, the associator commutes with the connecting maps, and
  -- `δ ((x ∪ y) ∪ z) = (-1)^(p + q) (x ∪ y) ∪ δ z` by the definition of the cup product.
  have hL := map_associator_δ M N (S := ShortComplex.mk (dimensionShiftDownι P) (indBotCounit P)
      (dimensionShiftDownι_comp_indBotCounit P))
    (by simpa only [dimensionShiftDownSES_def] using
      dimensionShiftDownSES_tensorLeft_shortExact P (M ⊗ N)) hMN r
    (cup (M ⊗ N) P (p + q) s r h (cup M N p q (p + q) rfl x y) z)
  have hT := congrArg ((p + q).negOnePow • ·)
    (cup_dimensionShiftDownIso_hom (M ⊗ N) P hs h rfl (cup M N p q (p + q) rfl x y) z)
  rw [negOnePow_smul_negOnePow_smul, tensorDimensionShiftDownIso_hom] at hT
  rw [← hL, ← hT, map_zsmul_unit, ih]
  -- On the right, `δ (x ∪ w) = (-1)^p x ∪ δ w` for the split sequence, and
  -- `δ (y ∪ z) = (-1)^q y ∪ δ z` by the definition of the cup product.
  have hR := congrArg (p.negOnePow • ·)
    (cup_δ_of_leftInverse M hN hρN (show p + r₂ = r by omega) x (cup N P q s r₂ h₂ y z))
  dsimp only [ShortComplex.map_X₁, ShortComplex.map_X₃, curriedTensor_obj_obj] at hR
  have hTN := congrArg (q.negOnePow • ·) (cup_dimensionShiftDownIso_hom N P hs h₂ rfl y z)
  rw [negOnePow_smul_negOnePow_smul] at hR
  rw [negOnePow_smul_negOnePow_smul, tensorDimensionShiftDownIso_hom] at hTN
  rw [← hR, ← hTN, map_zsmul_unit, smul_smul, ← Int.negOnePow_add]

/-- Associativity of the Tate cup product when the last class has nonnegative degree, by
induction on that degree through the upward dimension shift. -/
private theorem cup_assoc_of_nonneg (M N P : Rep k G) {p q s r₂ r : ℤ} (hs : 0 ≤ s)
    (h₂ : q + s = r₂) (h : p + q + s = r) (x : tateCohomology M p) (y : tateCohomology N q)
    (z : tateCohomology P s) :
    (tateCohomologyFunctor r).map (α_ M N P).hom
        (cup (M ⊗ N) P (p + q) s r h (cup M N p q (p + q) rfl x y) z) =
      cup M (N ⊗ P) p r₂ r (by omega) x (cup N P q s r₂ h₂ y z) := by
  induction s, hs using Int.leInduction generalizing P r₂ r with
  | base =>
    obtain rfl : q = r₂ := by omega
    obtain rfl : p + q = r := by omega
    exact cup_assoc_zero_right M N P rfl x y z
  | succ s hs ih =>
    obtain rfl : r₂ = q + s + 1 := by omega
    obtain rfl : r = p + q + s + 1 := by omega
    exact cup_assoc_add_one M N P hs rfl rfl x y (ih (dimensionShiftUp P) rfl rfl) z

/-- Associativity of the Tate cup product when the last class has negative degree, by induction
on that degree through the downward dimension shift. -/
private theorem cup_assoc_of_neg (M N P : Rep k G) {p q s r₂ r : ℤ} (hs : s < 0)
    (h₂ : q + s = r₂) (h : p + q + s = r) (x : tateCohomology M p) (y : tateCohomology N q)
    (z : tateCohomology P s) :
    (tateCohomologyFunctor r).map (α_ M N P).hom
        (cup (M ⊗ N) P (p + q) s r h (cup M N p q (p + q) rfl x y) z) =
      cup M (N ⊗ P) p r₂ r (by omega) x (cup N P q s r₂ h₂ y z) := by
  obtain ⟨n, rfl⟩ := Int.eq_negSucc_of_lt_zero hs
  induction n generalizing P r₂ r with
  | zero =>
    exact cup_assoc_of_add_one M N P hs h₂ h x y
      (cup_assoc_of_nonneg M N (dimensionShiftDown P) (by omega) (by omega) (by omega) x y) z
  | succ n ih =>
    exact cup_assoc_of_add_one M N P hs h₂ h x y
      (ih (dimensionShiftDown P) (Int.negSucc_lt_zero n) (by omega) (by omega)) z

/-- **Associativity of the Tate cup product** in all integer tridegrees: for classes `x`, `y`, `z`
of degrees `p`, `q`, `s`, the tensor associator carries `(x ∪ y) ∪ z` to `x ∪ (y ∪ z)`. -/
@[simp]
theorem cup_assoc (M N P : Rep k G) {p q s r₁ r₂ r : ℤ} (h₁ : p + q = r₁) (h₂ : q + s = r₂)
    (h : r₁ + s = r) (x : tateCohomology M p) (y : tateCohomology N q)
    (z : tateCohomology P s) :
    (tateCohomologyFunctor r).map (α_ M N P).hom
        (cup (M ⊗ N) P r₁ s r h (cup M N p q r₁ h₁ x y) z) =
      cup M (N ⊗ P) p r₂ r (by omega) x (cup N P q s r₂ h₂ y z) := by
  subst h₁
  rcases le_or_gt 0 s with hs | hs
  · exact cup_assoc_of_nonneg M N P hs h₂ h x y z
  · exact cup_assoc_of_neg M N P hs h₂ h x y z

/-- Associativity of the Tate cup product when the middle class has degree zero, in the simp
normal form where the degree-zero cups are written with `cupH0` and `cup0H`. -/
@[simp]
theorem cup_cupH0_assoc (M N P : Rep k G) {p q r : ℤ} (h : p + q = r)
    (x : tateCohomology M p) (y : tateCohomology N 0)
    (z : tateCohomology P q) :
    (tateCohomologyFunctor r).map (α_ M N P).hom
      (cup (M ⊗ N) P p q r h (cupH0 M N p x y) z) =
      cup M (N ⊗ P) p q r h x (cup0H N P q y z) := by
  simpa only [cup_zero_right, cup_zero_left] using cup_assoc M N P (add_zero p) (zero_add q) h x y z

/-- Associativity of the Tate cup product when the last class has degree zero, in the simp normal
form where the degree-zero cups are written with `cupH0`. -/
@[simp]
theorem cupH0_cup_assoc (M N P : Rep k G) {p q r : ℤ} (h : p + q = r)
    (x : tateCohomology M p) (y : tateCohomology N q)
    (z : tateCohomology P 0) :
    (tateCohomologyFunctor r).map (α_ M N P).hom
      (cupH0 (M ⊗ N) P r (cup M N p q r h x y) z) =
      cup M (N ⊗ P) p q r h x (cupH0 N P q y z) := by
  simpa only [cup_zero_right] using cup_assoc M N P h (add_zero q) (add_zero r) x y z

/-- Cup product with two degree-zero Tate classes is associative, after applying the tensor
associator to the coefficient representation. -/
@[simp]
theorem cupH0_assoc_zero (M N P : Rep k G) (p : ℤ)
    (x : tateCohomology M p) (y : tateCohomology N 0)
    (z : tateCohomology P 0) :
    (tateCohomologyFunctor p).map (α_ M N P).hom
      (cupH0 (M ⊗ N) P p (cupH0 M N p x y) z) =
      cupH0 M (N ⊗ P) p x (cupH0 N P 0 y z) := by
  simpa only [cup_zero_right] using cupH0_cup_assoc M N P (q := 0) (add_zero p) x y z

end TauCeti.TateCohomology
