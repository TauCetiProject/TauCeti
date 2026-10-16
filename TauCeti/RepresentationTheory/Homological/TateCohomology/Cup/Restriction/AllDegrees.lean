/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude, Codex
-/
module

public import TauCeti.RepresentationTheory.Homological.TateCohomology.Cup.Delta
public import TauCeti.RepresentationTheory.Homological.TateCohomology.Cup.Restriction.Basic
public import TauCeti.RepresentationTheory.Homological.TateCohomology.Restriction.Delta

/-!
# Restriction of the Tate cup product in all integer bidegrees

For a subgroup `H` of a finite group `G`, restriction preserves the Tate cup product of classes
of arbitrary integer degrees (`TauCeti.TateCohomology.cup_res`). Thus products can be formed before
or after restriction, including products with negative-degree classes in either factor.

The upward and downward dimension-shifting sequences move the second degree away from zero.
Restriction commutes with connecting maps, and the restricted induced middle term remains
Tate-acyclic even after tensoring with the first factor. The downward argument follows
`Cup.Associativity`.

## References

* E. Artin and J. Tate, *Class Field Theory*, Preliminaries, §2.
* K. S. Brown, *Cohomology of Groups*, Chapter VI, §5.
-/

public noncomputable section

universe u

open CategoryTheory Limits MonoidalCategory Rep

namespace TauCeti.TateCohomology

variable {k G : Type u} [CommRing k] [Group G] [Fintype G]

attribute [local instance] Subgroup.fintypeOfFinite

/-- The inductive step: restriction preserves the cup product in bidegree `(p, q + 1)` if it does
in bidegree `(p, q)` for the upward dimension shift of the second factor. -/
private theorem cup_res_add_one (M N : Rep k G) (H : Subgroup G) {p q r : ℤ} (hq : 0 ≤ q)
    (h : p + q = r) (x : tateCohomology M p)
    (ih : ∀ y : tateCohomology (dimensionShiftUp N) q,
      res (M ⊗ dimensionShiftUp N) H r (cup M (dimensionShiftUp N) p q r h x y) =
        cup (Rep.res H.subtype M) (Rep.res H.subtype (dimensionShiftUp N)) p q r h
          (res M H p x) (res (dimensionShiftUp N) H q y))
    (y : tateCohomology N (q + 1)) :
    res (M ⊗ N) H (r + 1) (cup M N p (q + 1) (r + 1) (by omega) x y) =
      cup (Rep.res H.subtype M) (Rep.res H.subtype N) p (q + 1) (r + 1) (by omega)
        (res M H p x) (res N H (q + 1) y) := by
  have hD : (ShortComplex.mk (coindBotUnit N) (dimensionShiftUpπ N)
      (coindBotUnit_comp_dimensionShiftUpπ N)).ShortExact := by
    simpa only [dimensionShiftUpSES_def] using dimensionShiftUpSES_shortExact N
  have hMD : ((ShortComplex.mk (coindBotUnit N) (dimensionShiftUpπ N)
      (coindBotUnit_comp_dimensionShiftUpπ N)).map (tensorLeft M)).ShortExact := by
    simpa only [dimensionShiftUpSES_def] using dimensionShiftUpSES_tensorLeft_shortExact N M
  -- Write `y = δ y'` for the dimension-shifting sequence `0 → N → Coind_⊥^G N → N' → 0`.
  obtain ⟨y, rfl⟩ : ∃ y', (dimensionShiftUpIso N q).hom y' = y :=
    ⟨(dimensionShiftUpIso N q).inv y, Iso.inv_hom_id_apply _ _⟩
  -- On the left, `x ∪ δ y' = (-1)^p δ (x ∪ y')`, and restriction commutes with `δ` and, by
  -- hypothesis, with `x ∪ y'`.
  rw [cup_dimensionShiftUpIso_hom M N hq h rfl, map_zsmul_unit, tensorDimensionShiftUpIso_hom]
  have hL := congr($(δ_comp_res hMD H r) (cup M (dimensionShiftUp N) p q r h x y))
  have hR := congr($(δ_comp_res hD H q) y)
  simp only [ModuleCat.comp_apply] at hL hR
  refine (congrArg (p.negOnePow • ·) (hL.trans (congrArg _ (ih y)))).trans ?_
  -- On the right, restriction commutes with `δ`.
  rw [dimensionShiftUpIso_hom]
  refine Eq.trans ?_ (congrArg (cup _ _ p (q + 1) (r + 1) _ (res M H p x)) hR).symm
  -- The restricted dimension-shifting sequence is still split by evaluation at `1`, so the cup
  -- product over `H` satisfies the same rule for its connecting map.
  have hresD := (shortExact_res H.subtype).2 hD
  exact (cup_δ_of_leftInverse (Rep.res H.subtype M) hresD (leftInverse_coindBotUnit N) h _
    _).symm

/-- Restriction preserves the Tate cup product when the second factor has nonnegative degree. -/
private theorem cup_res_of_nonneg_right (M N : Rep k G) (H : Subgroup G) {p q r : ℤ} (hq : 0 ≤ q)
    (h : p + q = r) (x : tateCohomology M p) (y : tateCohomology N q) :
    res (M ⊗ N) H r (cup M N p q r h x y) =
      cup (Rep.res H.subtype M) (Rep.res H.subtype N) p q r h (res M H p x) (res N H q y) := by
  induction q, hq using Int.leInduction generalizing N r with
  | base =>
    obtain rfl : p = r := by omega
    simpa only [res_zero] using cup_res_zero_right M N H p x y
  | succ q hq ih =>
    obtain rfl : r = p + q + 1 := by omega
    exact cup_res_add_one M N H hq rfl x (ih (dimensionShiftUp N) rfl) y

/-- Restriction in bidegree `(p, q + 1)` for the downward shift of `N` implies restriction
in bidegree `(p, q)` for `N`. -/
private theorem cup_res_of_add_one (M N : Rep k G) (H : Subgroup G) {p q r : ℤ} (hq : q < 0)
    (h : p + q = r) (x : tateCohomology M p)
    (ih : ∀ y : tateCohomology (dimensionShiftDown N) (q + 1),
      res (M ⊗ dimensionShiftDown N) H (r + 1)
          (cup M (dimensionShiftDown N) p (q + 1) (r + 1) (by omega) x y) =
        cup (Rep.res H.subtype M) (Rep.res H.subtype (dimensionShiftDown N)) p (q + 1)
          (r + 1) (by omega) (res M H p x) (res (dimensionShiftDown N) H (q + 1) y))
    (y : tateCohomology N q) :
    res (M ⊗ N) H r (cup M N p q r h x y) =
      cup (Rep.res H.subtype M) (Rep.res H.subtype N) p q r h (res M H p x) (res N H q y) := by
  have hD : (ShortComplex.mk (dimensionShiftDownι N) (indBotCounit N)
      (dimensionShiftDownι_comp_indBotCounit N)).ShortExact := by
    simpa only [dimensionShiftDownSES_def] using dimensionShiftDownSES_shortExact N
  have hMD : ((ShortComplex.mk (dimensionShiftDownι N) (indBotCounit N)
      (dimensionShiftDownι_comp_indBotCounit N)).map (tensorLeft M)).ShortExact := by
    simpa only [dimensionShiftDownSES_def] using dimensionShiftDownSES_tensorLeft_shortExact N M
  have hresD := (shortExact_res H.subtype).2 hD
  have hresMD := (shortExact_res H.subtype).2 hMD
  obtain ⟨ρ, hρ⟩ := Rep.exists_leftInverse_of_rightInverse hD.exact (rightInverse_indBotCounit N)
  -- Restriction of an induced representation is induced from the trivial subgroup of `H`.
  -- Its tensor product with the restricted first factor therefore has vanishing Tate cohomology.
  let e := whiskerLeftIso (Rep.res H.subtype M) (resIndBotIso H N.V)
  have hz : IsZero (tateCohomology (Rep.res H.subtype (M ⊗ indBot k G N.V)) r) :=
    (isZero_tensor_indBot (G := H) (G ⧸ H →₀ N.V) (Rep.res H.subtype M) r).of_iso
      ((tateCohomologyFunctor r).mapIso e)
  have hinj : Function.Injective (_root_.TateCohomology.δ hresMD r) :=
    (ModuleCat.mono_iff_injective _).1
      ((_root_.TateCohomology.map_tateComplexFunctor_shortExact hresMD).mono_δ r (r + 1) rfl hz)
  refine hinj ?_
  have hL := congr($(δ_comp_res hMD H r) (cup M N p q r h x y))
  have hR := congr($(δ_comp_res hD H q) y)
  simp only [ModuleCat.comp_apply] at hL hR
  have hT := congrArg (p.negOnePow • ·) (cup_dimensionShiftDownIso_hom M N hq h rfl x y)
  rw [negOnePow_smul_negOnePow_smul, tensorDimensionShiftDownIso_hom] at hT
  dsimp only [ShortComplex.map_X₁, ShortComplex.map_X₃, curriedTensor_obj_obj] at hL
  rw [← hL, ← hT, map_zsmul_unit, ih, dimensionShiftDownIso_hom, hR]
  have hcup := congrArg (p.negOnePow • ·)
    (cup_δ_of_leftInverse (Rep.res H.subtype M) hresD hρ h (res M H p x) (res N H q y))
  rw [negOnePow_smul_negOnePow_smul] at hcup
  exact hcup

/-- Restriction preserves the Tate cup product in all integer bidegrees. For a subgroup `H`
of a finite group `G`, restricting `x ∪ y` gives the cup product of the restrictions of `x` and
`y`, without any sign or degree restriction. As for `res`, subgroup cohomology uses
`Subgroup.fintypeOfFinite`; a caller with another `Fintype H` must select this instance when
forming the cup product on the restricted classes. -/
@[simp]
theorem cup_res (M N : Rep k G) (H : Subgroup G) {p q r : ℤ}
    (h : p + q = r) (x : tateCohomology M p) (y : tateCohomology N q) :
    res (M ⊗ N) H r (cup M N p q r h x y) =
      cup (Rep.res H.subtype M) (Rep.res H.subtype N) p q r h (res M H p x) (res N H q y) := by
  rcases le_or_gt 0 q with hq | hq
  · exact cup_res_of_nonneg_right M N H hq h x y
  obtain ⟨n, rfl⟩ := Int.eq_negSucc_of_lt_zero hq
  induction n generalizing N r with
  | zero =>
    exact cup_res_of_add_one M N H hq h x
      (cup_res_of_nonneg_right M (dimensionShiftDown N) H (by omega) (by omega) x) y
  | succ n ih =>
    exact cup_res_of_add_one M N H hq h x
      (fun y ↦ ih (dimensionShiftDown N) (r := r + 1) (by omega) y (Int.negSucc_lt_zero n)) y

end TauCeti.TateCohomology
