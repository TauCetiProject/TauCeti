/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Prod
public import TauCeti.Algebra.Lie.Abelian
public import TauCeti.Algebra.Lie.KacMoody.Basic
public import TauCeti.LinearAlgebra.Matrix.Cartan.Realization.CentralSplitting

/-!
# Central splittings of presented Kac–Moody algebras

If a realization splits as `H = M ⊕ Z`, with all coroots in `M` and every root vanishing
on `Z`, its presented Lie algebra splits as the product of the algebra of the restricted
realization and the abelian Lie algebra on `Z`. The isomorphism retains the specified
Cartan coordinates and the raising and lowering generators. In particular, applying this
to a minimal sub-realization isolates precisely the extra central directions.

The argument uses the universal property of the Serre presentation and does not require
injectivity of the Cartan map or a nonsingular Cartan matrix.

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

include hz in
private theorem root_projection (i : I) (x : H) :
    R.root i (M.projectionOnto Z h x) = R.root i x := by
  have he : (M.projectionOnto Z h x : H) + (Z.projectionOnto M h.symm x : H) = x :=
    Submodule.projection_add_projection_eq_self h x
  have he' := congrArg (R.root i) he
  have hzero := (R.mem_cartanCenter_iff _).mp (hz (Z.projectionOnto M h.symm x).property) i
  simpa only [map_add, hzero, add_zero] using he'

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
      R.restrict_root_apply, root_projection R M Z h hz]
  lie_cartan_negative x j := by
    simp only [LinearMap.comp_apply, lie_cartanElement_negativeGenerator,
      R.restrict_root_apply, root_projection R M Z h hz]
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
    PresentedLieAlgebra (R.restrict M hc hs) × AbelianLieAlgebra Z where
  toLieHom := splittingHom R M Z hc hs h hz
  invFun := splittingInv R M Z hc hs hz
  left_inv x := DFunLike.congr_fun (splittingInv_comp_splittingHom R M Z hc hs h hz) x
  right_inv x := DFunLike.congr_fun (splittingHom_comp_splittingInv R M Z hc hs h hz) x

/-- The splitting records the two projections of a Cartan vector. -/
@[simp]
theorem centralSplitting_cartanElement (x : H) :
    centralSplitting R M Z hc hs h hz (cartanElement R x) =
      (cartanElement (R.restrict M hc hs) (M.projectionOnto Z h x),
        (AbelianLieAlgebra.equiv K Z).symm (Z.projectionOnto M h.symm x)) := by
  simp [centralSplitting, splittingHom, retraction, centralProjection]

/-- Raising generators belong to the smaller algebra factor. -/
@[simp]
theorem centralSplitting_positiveGenerator (i : I) :
    centralSplitting R M Z hc hs h hz (positiveGenerator R i) =
      (positiveGenerator (R.restrict M hc hs) i, 0) := by
  simp [centralSplitting, splittingHom, retraction, centralProjection]

/-- Lowering generators belong to the smaller algebra factor. -/
@[simp]
theorem centralSplitting_negativeGenerator (i : I) :
    centralSplitting R M Z hc hs h hz (negativeGenerator R i) =
      (negativeGenerator (R.restrict M hc hs) i, 0) := by
  simp [centralSplitting, splittingHom, retraction, centralProjection]

/-- The inverse splitting sums the two Cartan coordinates. -/
@[simp]
theorem centralSplitting_symm_cartanElement (m : M) (z : Z) :
    (centralSplitting R M Z hc hs h hz).symm
      (cartanElement (R.restrict M hc hs) m, (AbelianLieAlgebra.equiv K Z).symm z) =
        cartanElement R ((m : H) + z) := by
  apply (centralSplitting R M Z hc hs h hz).injective
  simp

/-- The inverse splitting preserves raising generators. -/
@[simp]
theorem centralSplitting_symm_positiveGenerator (i : I) :
    (centralSplitting R M Z hc hs h hz).symm
      (positiveGenerator (R.restrict M hc hs) i, 0) = positiveGenerator R i := by
  apply (centralSplitting R M Z hc hs h hz).injective
  simp

/-- The inverse splitting preserves lowering generators. -/
@[simp]
theorem centralSplitting_symm_negativeGenerator (i : I) :
    (centralSplitting R M Z hc hs h hz).symm
      (negativeGenerator (R.restrict M hc hs) i, 0) = negativeGenerator R i := by
  apply (centralSplitting R M Z hc hs h hz).injective
  simp

end Splitting

/-- Every realization is a minimal sub-realization together with an abelian central factor
at the level of presented Lie algebras, even for a singular matrix. -/
theorem exists_isMinimal_restrict_centralSplitting [Fintype I] :
    ∃ (M Z : Submodule K H) (hc : R.corootSpan ≤ M)
      (hs : M ⊔ R.cartanCenter = ⊤),
      (R.restrict M hc hs).IsMinimal ∧ IsCompl M Z ∧ Z ≤ R.cartanCenter ∧
        Nonempty (PresentedLieAlgebra R ≃ₗ⁅K⁆
          PresentedLieAlgebra (R.restrict M hc hs) × AbelianLieAlgebra Z) := by
  obtain ⟨M, Z, hc, hs, hm, h, hz⟩ := R.exists_isMinimal_restrict_isCompl
  exact ⟨M, Z, hc, hs, hm, h, hz, ⟨centralSplitting R M Z hc hs h hz⟩⟩

end TauCeti.KacMoody
