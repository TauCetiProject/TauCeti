/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Prod
public import TauCeti.Algebra.Lie.Abelian
public import TauCeti.Algebra.Lie.Hom
public import TauCeti.Algebra.Lie.KacMoody.Basic
public import TauCeti.LinearAlgebra.Matrix.Cartan.Realization.CentralSplitting

/-!
# Central splittings of presented Kac–Moody algebras

If a realization splits as `H = M ⊕ Z`, with all coroots in `M` and every root vanishing
on `Z`, its presented Lie algebra splits as the product of the algebra of the restricted
realization and the abelian Lie algebra on `Z`. The isomorphism retains the specified
Cartan coordinates and the raising and lowering generators. In particular, applying this
to a minimal sub-realization isolates precisely the extra central directions.

This reduces constructions on an enlarged realization to the algebra of a smaller realization
and an abelian central factor. The splitting `centralSplitting` holds over an arbitrary field
and index type, for any integer matrix, including a singular one;
`exists_isMinimal_restrict_lieEquiv_prod` additionally assumes a finite index type, so that
each realization has a minimal sub-realization.

Reference: V. G. Kac, *Infinite-dimensional Lie algebras*, third edition, §§1.1–1.3.
-/

public section

open LieAlgebra

namespace TauCeti.KacMoody

variable {I K H : Type*} [Field K] [AddCommGroup H] [Module K H]
  {A : Matrix I I ℤ} (R : CartanRealization (A.map (Int.cast : ℤ → K)) H)

section Splitting

variable (M Z : Submodule K H) (hc : R.corootSpan ≤ M)
  (hs : M ⊔ R.cartanCenter = ⊤) (h : IsCompl M Z) (hz : Z ≤ R.cartanCenter)

private theorem inclusionRelations :
    SatisfiesRelations (R.restrict M hc hs) ((cartanElement R).comp M.subtype)
      (positiveGenerator R) (negativeGenerator R) where
  lie_cartan_cartan _ _ := by simp
  lie_cartan_positive _ _ := by simp
  lie_cartan_negative _ _ := by simp
  lie_positive_negative_self _ := by simp
  lie_positive_negative_of_ne _ _ hij := lie_positiveGenerator_negativeGenerator_of_ne R hij
  serre_positive := ad_pow_lie_positiveGenerator_positiveGenerator R
  serre_negative := ad_pow_lie_negativeGenerator_negativeGenerator R

private noncomputable def inclusion :
    PresentedLieAlgebra (R.restrict M hc hs) →ₗ⁅K⁆ PresentedLieAlgebra R :=
  lift (inclusionRelations R M hc hs)

include hz in
private theorem retractionRelations :
    SatisfiesRelations R ((cartanElement (R.restrict M hc hs)).comp (M.projectionOnto Z h))
      (positiveGenerator (R.restrict M hc hs)) (negativeGenerator (R.restrict M hc hs)) where
  lie_cartan_cartan _ _ := by simp
  lie_cartan_positive x j := by
    simp only [LinearMap.comp_apply, lie_cartanElement_positiveGenerator,
      R.restrict_root_apply, Submodule.coe_projectionOnto_apply, R.root_projection h hz]
  lie_cartan_negative x j := by
    simp only [LinearMap.comp_apply, lie_cartanElement_negativeGenerator,
      R.restrict_root_apply, Submodule.coe_projectionOnto_apply, R.root_projection h hz]
  lie_positive_negative_self i := by
    have he : M.projectionOnto Z h (R.coroot i) = (R.restrict M hc hs).coroot i := by
      apply Subtype.ext
      simpa using congrArg Subtype.val
        (Submodule.projectionOnto_apply_of_mem_left h (hc (R.coroot_mem_corootSpan i)))
    simp [he]
  lie_positive_negative_of_ne _ _ hij :=
    lie_positiveGenerator_negativeGenerator_of_ne (R.restrict M hc hs) hij
  serre_positive := ad_pow_lie_positiveGenerator_positiveGenerator (R.restrict M hc hs)
  serre_negative := ad_pow_lie_negativeGenerator_negativeGenerator (R.restrict M hc hs)

private noncomputable def retraction :
    PresentedLieAlgebra R →ₗ⁅K⁆ PresentedLieAlgebra (R.restrict M hc hs) :=
  lift (retractionRelations R M Z hc hs h hz)

include hc in
private theorem centralRelations :
    SatisfiesRelations R ((AbelianLieAlgebra.equiv K Z).symm.toLinearMap.comp
      (Z.projectionOnto M h.symm)) 0 0 where
  lie_cartan_cartan _ _ := by simp [trivial_lie_zero]
  lie_cartan_positive _ _ := by simp
  lie_cartan_negative _ _ := by simp
  lie_positive_negative_self i := by
    simp [Submodule.projectionOnto_apply_of_mem_right h.symm (hc (R.coroot_mem_corootSpan i))]
  lie_positive_negative_of_ne _ _ _ := by simp
  serre_positive _ _ := by simp
  serre_negative _ _ := by simp

private noncomputable def centralProjection :
    PresentedLieAlgebra R →ₗ⁅K⁆ AbelianLieAlgebra Z :=
  lift (centralRelations R M Z hc h)

private noncomputable def splittingHom : PresentedLieAlgebra R →ₗ⁅K⁆
    PresentedLieAlgebra (R.restrict M hc hs) × AbelianLieAlgebra Z :=
  (retraction R M Z hc hs h hz).prod (centralProjection R M Z hc h)

private noncomputable def splittingInv :
    PresentedLieAlgebra (R.restrict M hc hs) × AbelianLieAlgebra Z →ₗ⁅K⁆
      PresentedLieAlgebra R where
  toLinearMap := (inclusion R M hc hs).toLinearMap.coprod
    ((cartanElement R).comp (Z.subtype.comp (AbelianLieAlgebra.equiv K Z).toLinearMap))
  map_lie' {x y} := by
    have hx := cartanElement_mem_center R (hz (AbelianLieAlgebra.equiv K Z x.2).property)
    have hy := cartanElement_mem_center R (hz (AbelianLieAlgebra.equiv K Z y.2).property)
    have hx' := (LieModule.mem_maxTrivSubmodule _ _ _ _).mp hx
    have hy' := (LieModule.mem_maxTrivSubmodule _ _ _ _).mp hy
    simp only [LinearMap.toFun_eq_coe, LinearMap.coprod_apply, LinearMap.comp_apply,
      LinearEquiv.coe_coe, Submodule.subtype_apply, LieHom.coe_toLinearMap,
      LieAlgebra.Prod.bracket_apply, LieHom.map_lie, trivial_lie_zero, map_zero, add_zero,
      add_lie, lie_add, hy']
    rw [← lie_skew (cartanElement R ↑(AbelianLieAlgebra.equiv K Z x.2))
      (inclusion R M hc hs y.1), hx', neg_zero, add_zero]

@[simp]
private theorem splittingInv_apply
    (x : PresentedLieAlgebra (R.restrict M hc hs) × AbelianLieAlgebra Z) :
    splittingInv R M Z hc hs hz x = inclusion R M hc hs x.1 +
      cartanElement R (AbelianLieAlgebra.equiv K Z x.2) := (rfl)

private theorem splittingInv_comp_splittingHom :
    (splittingInv R M Z hc hs hz).comp (splittingHom R M Z hc hs h hz) = LieHom.id := by
  apply hom_ext <;> intro x
  · simp only [LieHom.comp_apply, LieHom.id_apply, splittingHom, LieHom.prod_apply,
      retraction, centralProjection, lift_cartanElement,
      LinearMap.comp_apply, LinearEquiv.coe_coe, splittingInv_apply, inclusion]
    simp only [Submodule.subtype_apply, LinearEquiv.apply_symm_apply, ← map_add]
    exact congrArg (cartanElement R) (Submodule.projection_add_projection_eq_self h x)
  · simp [splittingHom, retraction, centralProjection, inclusion]
  · simp [splittingHom, retraction, centralProjection, inclusion]

private theorem splittingHom_comp_splittingInv :
    (splittingHom R M Z hc hs h hz).comp (splittingInv R M Z hc hs hz) = LieHom.id := by
  apply LieHom.prod_ext
  · apply hom_ext <;> intro x <;>
      simp [splittingHom, retraction, centralProjection, inclusion,
        LieHom.inl_apply]
  · apply LieHom.ext
    intro z
    simp [splittingHom, retraction, centralProjection, inclusion,
      LieHom.inr_apply]

/-- A central complement in the realization splits off as an abelian direct factor of its
presented Lie algebra. The first factor uses the actual restricted roots and coroots. -/
noncomputable def centralSplitting : PresentedLieAlgebra R ≃ₗ⁅K⁆
    PresentedLieAlgebra (R.restrict M hc (R.sup_cartanCenter_eq_top_of_isCompl h hz)) ×
      AbelianLieAlgebra Z :=
  LieEquiv.ofLieHoms (splittingHom R M Z hc _ h hz) (splittingInv R M Z hc _ hz)
    (splittingInv_comp_splittingHom R M Z hc _ h hz)
    (splittingHom_comp_splittingInv R M Z hc _ h hz)

/-- The splitting records the two projections of a Cartan vector. -/
@[simp]
theorem centralSplitting_cartanElement (x : H) :
    centralSplitting R M Z hc h hz (cartanElement R x) =
      (cartanElement (R.restrict M hc (R.sup_cartanCenter_eq_top_of_isCompl h hz))
          (M.projectionOnto Z h x),
        (AbelianLieAlgebra.equiv K Z).symm (Z.projectionOnto M h.symm x)) := by
  simp [centralSplitting, splittingHom, retraction, centralProjection]

/-- Raising generators belong to the smaller algebra factor. -/
@[simp]
theorem centralSplitting_positiveGenerator (i : I) :
    centralSplitting R M Z hc h hz (positiveGenerator R i) =
      (positiveGenerator (R.restrict M hc (R.sup_cartanCenter_eq_top_of_isCompl h hz)) i,
        0) := by
  simp [centralSplitting, splittingHom, retraction, centralProjection]

/-- Lowering generators belong to the smaller algebra factor. -/
@[simp]
theorem centralSplitting_negativeGenerator (i : I) :
    centralSplitting R M Z hc h hz (negativeGenerator R i) =
      (negativeGenerator (R.restrict M hc (R.sup_cartanCenter_eq_top_of_isCompl h hz)) i,
        0) := by
  simp [centralSplitting, splittingHom, retraction, centralProjection]

/-- The inverse splitting sums the two Cartan coordinates. -/
@[simp]
theorem centralSplitting_symm_cartanElement (m : M) (z : AbelianLieAlgebra Z) :
    (centralSplitting R M Z hc h hz).symm
      (cartanElement (R.restrict M hc (R.sup_cartanCenter_eq_top_of_isCompl h hz)) m, z) =
        cartanElement R ((m : H) + AbelianLieAlgebra.equiv K Z z) := by
  apply (centralSplitting R M Z hc h hz).injective
  simp

/-- The inverse splitting sends the abelian factor to central Cartan vectors. -/
@[simp]
theorem centralSplitting_symm_zero_mk (z : AbelianLieAlgebra Z) :
    (centralSplitting R M Z hc h hz).symm (0, z) =
      cartanElement R (AbelianLieAlgebra.equiv K Z z) := by
  apply (centralSplitting R M Z hc h hz).injective
  simp

/-- The inverse splitting preserves raising generators. -/
@[simp]
theorem centralSplitting_symm_positiveGenerator (i : I) :
    (centralSplitting R M Z hc h hz).symm
      (positiveGenerator (R.restrict M hc (R.sup_cartanCenter_eq_top_of_isCompl h hz)) i, 0) =
        positiveGenerator R i := by
  apply (centralSplitting R M Z hc h hz).injective
  simp

/-- The inverse splitting preserves lowering generators. -/
@[simp]
theorem centralSplitting_symm_negativeGenerator (i : I) :
    (centralSplitting R M Z hc h hz).symm
      (negativeGenerator (R.restrict M hc (R.sup_cartanCenter_eq_top_of_isCompl h hz)) i, 0) =
        negativeGenerator R i := by
  apply (centralSplitting R M Z hc h hz).injective
  simp

end Splitting

/-- For a finite index type, the presented algebra of any realization is isomorphic to the
product of the algebra of a minimal sub-realization and the abelian Lie algebra on a
complementary space of central directions; the matrix may be singular. -/
theorem exists_isMinimal_restrict_lieEquiv_prod [Fintype I] :
    ∃ (M Z : Submodule K H) (hc : R.corootSpan ≤ M)
      (hs : M ⊔ R.cartanCenter = ⊤),
      (R.restrict M hc hs).IsMinimal ∧ IsCompl M Z ∧ Z ≤ R.cartanCenter ∧
        Nonempty (PresentedLieAlgebra R ≃ₗ⁅K⁆
          PresentedLieAlgebra (R.restrict M hc hs) × AbelianLieAlgebra Z) := by
  obtain ⟨M, Z, hc, hs, hm, h, hz⟩ := R.exists_isMinimal_restrict_isCompl
  exact ⟨M, Z, hc, hs, hm, h, hz, ⟨centralSplitting R M Z hc h hz⟩⟩

end TauCeti.KacMoody
