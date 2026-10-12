/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.TateCohomology.Cup.Delta
public import TauCeti.RepresentationTheory.Homological.TateCohomology.Corestriction.Naturality
public import TauCeti.RepresentationTheory.Homological.TateCohomology.Restriction.Delta

/-!
# The projection formula for Tate cup products

For a subgroup `H` of a finite group `G`, a class `x` of `H` and a class `y` of `G`,

`cor (x ∪ res y) = cor x ∪ y`

in all integer bidegrees. The coefficient modules are restrictions of representations of `G`.
There is no normality assumption on `H`, and the coefficient modules need not be flat.

The degree-zero right factor is represented by an invariant vector, so the formula there is
coefficient naturality of corestriction. Dimension shifting in the second factor extends it
across all degrees, using compatibility of restriction and corestriction with connecting maps.
This is the cup-product compatibility used to transport Tate isomorphisms and reciprocity along
norm maps.

## Main results

* `TauCeti.TateCohomology.cup_projection`: the projection formula with corestriction in the first
  factor.

## References

* K. S. Brown, *Cohomology of Groups*, Chapter VI, §5.
* E. Artin and J. Tate, *Class Field Theory*, Chapter IV, §6 and Chapter XIV, §4.
-/

public noncomputable section

universe u

open CategoryTheory Limits MonoidalCategory Rep

namespace TauCeti.TateCohomology

variable {k G : Type u} [CommRing k] [Group G] [Fintype G]

attribute [local instance] Subgroup.fintypeOfFinite

/-- The projection formula when the right factor has degree zero. -/
private theorem cup_cor_zero_right (M N : Rep k G) (H : Subgroup G) (p : ℤ)
    (x : tateCohomology (Rep.res H.subtype M) p) (y : tateCohomology N 0) :
    cor (M ⊗ N) H p
        (cup (Rep.res H.subtype M) (Rep.res H.subtype N) p 0 p (add_zero p)
          x (res N H 0 y)) =
      cup M N p 0 p (add_zero p) (cor M H p x) y := by
  rw [cup_zero_right, cup_zero_right, res_zero]
  induction y using H0_induction_on with
  | h y =>
    rw [H0π_comp_H0Res_apply, cupH0_H0π, cupH0_H0π]
    have hnat := cor_natural (Rep.tensorInvariant M y) H p
    rw [Rep.resMap_tensorInvariant M N H y] at hnat
    exact ConcreteCategory.congr_hom hnat x

/-- The upward dimension-shifting step for the projection formula. -/
private theorem cup_cor_add_one (M N : Rep k G) (H : Subgroup G) {p q r : ℤ} (hq : 0 ≤ q)
    (h : p + q = r) (x : tateCohomology (Rep.res H.subtype M) p)
    (ih : ∀ y : tateCohomology (dimensionShiftUp N) q,
      cor (M ⊗ dimensionShiftUp N) H r
          (cup (Rep.res H.subtype M) (Rep.res H.subtype (dimensionShiftUp N)) p q r h
            x (res (dimensionShiftUp N) H q y)) =
        cup M (dimensionShiftUp N) p q r h (cor M H p x) y)
    (y : tateCohomology N (q + 1)) :
    cor (M ⊗ N) H (r + 1)
        (cup (Rep.res H.subtype M) (Rep.res H.subtype N) p (q + 1) (r + 1) (by omega)
          x (res N H (q + 1) y)) =
      cup M N p (q + 1) (r + 1) (by omega) (cor M H p x) y := by
  have hD : (ShortComplex.mk (coindBotUnit N) (dimensionShiftUpπ N)
      (coindBotUnit_comp_dimensionShiftUpπ N)).ShortExact := by
    simpa only [dimensionShiftUpSES_def] using dimensionShiftUpSES_shortExact N
  have hMD : ((ShortComplex.mk (coindBotUnit N) (dimensionShiftUpπ N)
      (coindBotUnit_comp_dimensionShiftUpπ N)).map (tensorLeft M)).ShortExact := by
    simpa only [dimensionShiftUpSES_def] using dimensionShiftUpSES_tensorLeft_shortExact N M
  obtain ⟨y, rfl⟩ : ∃ y', (dimensionShiftUpIso N q).hom y' = y :=
    ⟨(dimensionShiftUpIso N q).inv y, Iso.inv_hom_id_apply _ _⟩
  have hres := congr($(δ_comp_res hD H q) y)
  simp only [ModuleCat.comp_apply] at hres
  rw [dimensionShiftUpIso_hom, hres]
  have hcup := cup_δ_of_leftInverse (Rep.res H.subtype M) ((shortExact_res H.subtype).2 hD)
    (leftInverse_coindBotUnit N) h x (res (dimensionShiftUp N) H q y)
  dsimp only [ShortComplex.map_X₁, ShortComplex.map_X₃] at hcup
  refine (congrArg (cor (M ⊗ N) H (r + 1)) hcup).trans ?_
  erw [map_zsmul_unit]
  -- Type the elementwise square explicitly: restriction retains the tensor carrier.
  have hcor : cor (M ⊗ N) H (r + 1)
      (_root_.TateCohomology.δ ((shortExact_res H.subtype).2 hMD) r
        (cup (Rep.res H.subtype M) (Rep.res H.subtype (dimensionShiftUp N)) p q r h
          x (res (dimensionShiftUp N) H q y))) =
    _root_.TateCohomology.δ hMD r
      (cor (M ⊗ dimensionShiftUp N) H r
        (cup (Rep.res H.subtype M) (Rep.res H.subtype (dimensionShiftUp N)) p q r h
          x (res (dimensionShiftUp N) H q y))) :=
    ConcreteCategory.congr_hom (δ_comp_cor hMD H r) _
  refine (congrArg (p.negOnePow • ·) (hcor.trans (congrArg _ (ih y)))).trans ?_
  have htarget := cup_dimensionShiftUpIso_hom M N hq h rfl (cor M H p x) y
  rw [tensorDimensionShiftUpIso_hom, dimensionShiftUpIso_hom] at htarget
  exact htarget.symm

/-- The projection formula with nonnegative right degree. -/
private theorem cup_cor_of_nonneg_right (M N : Rep k G) (H : Subgroup G) {p q r : ℤ}
    (hq : 0 ≤ q) (h : p + q = r) (x : tateCohomology (Rep.res H.subtype M) p)
    (y : tateCohomology N q) :
    cor (M ⊗ N) H r
        (cup (Rep.res H.subtype M) (Rep.res H.subtype N) p q r h x (res N H q y)) =
      cup M N p q r h (cor M H p x) y := by
  induction q, hq using Int.leInduction generalizing N r with
  | base =>
    obtain rfl : p = r := by omega
    exact cup_cor_zero_right M N H p x y
  | succ q hq ih =>
    obtain rfl : r = p + q + 1 := by omega
    exact cup_cor_add_one M N H hq rfl x (ih (dimensionShiftUp N) rfl) y

/-- The downward dimension-shifting step for the projection formula. -/
private theorem cup_cor_of_add_one (M N : Rep k G) (H : Subgroup G) {p q r : ℤ} (hq : q < 0)
    (h : p + q = r) (x : tateCohomology (Rep.res H.subtype M) p)
    (ih : ∀ y : tateCohomology (dimensionShiftDown N) (q + 1),
      cor (M ⊗ dimensionShiftDown N) H (r + 1)
          (cup (Rep.res H.subtype M) (Rep.res H.subtype (dimensionShiftDown N)) p (q + 1)
            (r + 1) (by omega) x (res (dimensionShiftDown N) H (q + 1) y)) =
        cup M (dimensionShiftDown N) p (q + 1) (r + 1) (by omega) (cor M H p x) y)
    (y : tateCohomology N q) :
    cor (M ⊗ N) H r
        (cup (Rep.res H.subtype M) (Rep.res H.subtype N) p q r h x (res N H q y)) =
      cup M N p q r h (cor M H p x) y := by
  have hD : (ShortComplex.mk (dimensionShiftDownι N) (indBotCounit N)
      (dimensionShiftDownι_comp_indBotCounit N)).ShortExact := by
    simpa only [dimensionShiftDownSES_def] using dimensionShiftDownSES_shortExact N
  have hMD : ((ShortComplex.mk (dimensionShiftDownι N) (indBotCounit N)
      (dimensionShiftDownι_comp_indBotCounit N)).map (tensorLeft M)).ShortExact := by
    simpa only [dimensionShiftDownSES_def] using dimensionShiftDownSES_tensorLeft_shortExact N M
  obtain ⟨ρ, hρ⟩ := Rep.exists_leftInverse_of_rightInverse hD.exact (rightInverse_indBotCounit N)
  -- The tensored downward connecting map is an isomorphism, so it detects equality.
  refine (tensorDimensionShiftDownIso N M r (r + 1) rfl).toLinearEquiv.injective ?_
  rw [Iso.toLinearEquiv_apply, Iso.toLinearEquiv_apply, tensorDimensionShiftDownIso_hom]
  -- Give the square its elementwise type before using it across the tensor wrappers.
  have hcor : cor (M ⊗ dimensionShiftDown N) H (r + 1)
      (_root_.TateCohomology.δ ((shortExact_res H.subtype).2 hMD) r
        (cup (Rep.res H.subtype M) (Rep.res H.subtype N) p q r h x (res N H q y))) =
    _root_.TateCohomology.δ hMD r
      (cor (M ⊗ N) H r
        (cup (Rep.res H.subtype M) (Rep.res H.subtype N) p q r h x (res N H q y))) :=
    ConcreteCategory.congr_hom (δ_comp_cor hMD H r) _
  have hres : res (dimensionShiftDown N) H (q + 1) (_root_.TateCohomology.δ hD q y) =
      _root_.TateCohomology.δ ((shortExact_res H.subtype).2 hD) q (res N H q y) :=
    ConcreteCategory.congr_hom (δ_comp_res hD H q) y
  refine hcor.symm.trans ?_
  have hcup := congrArg (p.negOnePow • ·)
    (cup_δ_of_leftInverse (Rep.res H.subtype M) ((shortExact_res H.subtype).2 hD)
      hρ h x (res N H q y))
  dsimp only [ShortComplex.map_X₁, ShortComplex.map_X₃, curriedTensor_obj_obj] at hcup
  rw [negOnePow_smul_negOnePow_smul] at hcup
  refine (congrArg (cor (M ⊗ dimensionShiftDown N) H (r + 1)) hcup.symm).trans ?_
  erw [map_zsmul_unit]
  erw [← hres, ih]
  have htarget := congrArg (p.negOnePow • ·)
    (cup_dimensionShiftDownIso_hom M N hq h rfl (cor M H p x) y)
  rw [negOnePow_smul_negOnePow_smul, dimensionShiftDownIso_hom,
    tensorDimensionShiftDownIso_hom] at htarget
  exact htarget

/-- **The projection formula for Tate cup products in all integer bidegrees.**
Corestricting `x ∪ res y` is `cor x ∪ y`, for arbitrary representations of a finite group
and any subgroup. As in `res` and `cor`, subgroup cohomology uses
`Subgroup.fintypeOfFinite`; callers with another `Fintype H` should select this instance. -/
@[simp]
theorem cup_projection (M N : Rep k G) (H : Subgroup G) {p q r : ℤ}
    (h : p + q = r) (x : tateCohomology (Rep.res H.subtype M) p) (y : tateCohomology N q) :
    cor (M ⊗ N) H r
        (cup (Rep.res H.subtype M) (Rep.res H.subtype N) p q r h x (res N H q y)) =
      cup M N p q r h (cor M H p x) y := by
  rcases le_or_gt 0 q with hq | hq
  · exact cup_cor_of_nonneg_right M N H hq h x y
  obtain ⟨n, rfl⟩ := Int.eq_negSucc_of_lt_zero hq
  induction n generalizing N r with
  | zero =>
    exact cup_cor_of_add_one M N H hq h x
      (cup_cor_of_nonneg_right M (dimensionShiftDown N) H (by omega) (by omega) x) y
  | succ n ih =>
    exact cup_cor_of_add_one M N H hq h x
      (fun y ↦ ih (dimensionShiftDown N) (r := r + 1) (by omega) y (Int.negSucc_lt_zero n)) y

end TauCeti.TateCohomology
