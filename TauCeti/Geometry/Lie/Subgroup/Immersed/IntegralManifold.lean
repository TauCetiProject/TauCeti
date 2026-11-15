/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Subgroup.Immersed.Basic
public import TauCeti.Geometry.Manifold.Distribution.IntegralManifold.WeakEmbeddedness
public import TauCeti.Geometry.Manifold.ModelTransport.Diffeomorph
import TauCeti.Geometry.Manifold.ModelWithCorners.ModelHomeomorph
import TauCeti.Geometry.Manifold.ModelWithCorners.RestrictScalars.LinearEquiv
import TauCeti.Geometry.Manifold.Immersion.ModelChange
import Mathlib.Algebra.Group.TransferInstance
import TauCeti.Geometry.Manifold.Algebra.LieGroup
import TauCeti.Geometry.Lie.Basic
import TauCeti.Geometry.Lie.Interior

/-!
# Lie subgroups from integral manifolds

A connected second-countable injective integral immersion whose image is a subgroup yields
a native immersed Lie-subgroup presentation retaining its intrinsic topology. The constructor
`ImmersedLieSubgroupData.ofIntegralManifold` requires no group structure on the source. The
original manifold is diffeomorphic to the presenting manifold, and this identification
intertwines the original immersion and the native homomorphism.

When the source already carries a group structure, `IsIntegralManifold.lieGroup` supplies
smooth multiplication and inversion from an injective homomorphism that is an integral immersion.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, second edition, Springer GTM 218 (2013),
  Theorem 19.17, pp.500–501, and proof of Theorem 19.26, pp.506–507.
-/

public noncomputable section

open Set Function Manifold
open scoped Manifold ContDiff

universe u v w

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField
attribute [local instance] ContMDiffMul.boundarylessManifold

namespace TauCeti

/-- An injective homomorphism which is an integral immersion of an involutive constant-rank
distribution makes its second-countable boundaryless source group a Lie group, with its given
intrinsic topology and smooth structure. No connectedness of the source is required. -/
theorem IsIntegralManifold.lieGroup
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'}
    {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [Group N] [IsManifold J ∞ N]
    [BoundarylessManifold J N] [SecondCountableTopology N]
    {D : ∀ x : G, Submodule ℝ (TangentSpace I x)} {k : ℕ} {f : N →* G}
    (hf : IsIntegralManifold J ∞ D (f : N → G))
    (hinv : IsInvolutiveDistribution I D) (hD : IsContMDiffDistribution I ∞ k D)
    (hi : Injective f) : LieGroup J ∞ N := by
  have hmul : ContMDiff (J.prod J) J ∞ (fun p : N × N ↦ p.1 * p.2) :=
    (hf.contMDiff_iff_comp (r := ∞) (by simp) hi (by simp) hinv hD).mpr (by
      simpa only [Function.comp_def, map_mul] using
        (show ContMDiff (J.prod J) I ∞ (fun p : N × N ↦ f p.1 * f p.2) from
          (hf.contMDiff.comp contMDiff_fst).mul (hf.contMDiff.comp contMDiff_snd)))
  have hinverse : ContMDiff J J ∞ (fun x : N ↦ x⁻¹) :=
    (hf.contMDiff_iff_comp (r := ∞) (by simp) hi (by simp) hinv hD).mpr (by
      simpa only [Function.comp_def, map_inv] using
        (show ContMDiff J I ∞ (fun x : N ↦ (f x)⁻¹) from hf.contMDiff.inv))
  exact
    { toContMDiffMul := { toIsManifold := inferInstance, contMDiff_mul := hmul }
      contMDiff_inv := hinverse }

end TauCeti

namespace TauCeti.Lie.ImmersedLieSubgroupData

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type v} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type w} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'} [J.Boundaryless]
  {N : Type w} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]
  [ConnectedSpace N] [SecondCountableTopology N]

attribute [local instance] ImmersedLieSubgroupData.group
  ImmersedLieSubgroupData.topologicalSpace ImmersedLieSubgroupData.normedAddCommGroup
  ImmersedLieSubgroupData.normedSpace ImmersedLieSubgroupData.finiteDimensional
  ImmersedLieSubgroupData.modelTopology ImmersedLieSubgroupData.chartedSpace
  ImmersedLieSubgroupData.lieGroup

private def integralManifoldData {D : ∀ x : G, Submodule ℝ (TangentSpace I x)} {k : ℕ}
    (hinv : IsInvolutiveDistribution I D) (hD : IsContMDiffDistribution I ∞ k D)
    (K : Subgroup G) {f : N → G} (hf : IsIntegralManifold J ∞ D f)
    (hi : Injective f) (hr : range f = (K : Set G)) :
    Σ d : ImmersedLieSubgroupData I K,
      {φ : N ≃ₘ⟮J, d.I'⟯ d.X // ∀ x, d.toHom (φ x) = f x} := by
  -- Recover the source group and its smooth operations from the integral immersion.
  let p := Classical.choice hf.nonempty
  letI : FiniteDimensional ℝ F :=
    FiniteDimensional.of_injective (mfderiv J I f p).toLinearMap
      (hf.isImmersion.mfderiv_injective (by simp) p)
  let eK : N ≃ K := Equiv.ofBijective (fun x ↦ ⟨f x, hr.subset (mem_range_self x)⟩)
    ⟨fun x y h ↦ hi (congrArg Subtype.val h), by
      intro y
      obtain ⟨x, hx⟩ := hr.symm.subset y.property
      exact ⟨x, Subtype.ext hx⟩⟩
  letI : Group N := eK.group
  let inc : N →* G := K.subtype.comp eK.mulEquiv.toMonoidHom
  -- The transferred group equivalence has the original set map as its underlying function.
  have hinc (x : N) : inc x = f x := rfl
  letI : LieGroup J ∞ N :=
    (show IsIntegralManifold J ∞ D (inc : N → G) from hf).lieGroup hinv hD hi
  -- Fit both model universes while leaving the intrinsic space itself untouched.
  let R := EuclideanSpace ℝ (Fin (Module.finrank ℝ F))
  let V := ULift.{u} R
  let H₁ := ULift.{v} R
  let B : H₁ ≃L[ℝ] V := ContinuousLinearEquiv.ulift.trans ContinuousLinearEquiv.ulift.symm
  let J₁ := (𝓘(ℝ, H₁)).transContinuousLinearEquiv B
  let A : V ≃L[ℝ] F := ContinuousLinearEquiv.ulift.trans
    (ContinuousLinearEquiv.ofFinrankEq (by simp [R]))
  have hA : A '' range J₁ = range J := by
    rw [ModelWithCorners.range_eq_univ, ModelWithCorners.range_eq_univ, image_univ]
    exact A.surjective.range_eq
  let Φ : H' ≃ₘ⟮J, J₁⟯ H₁ := (A.modelDiffeomorph hA).symm
  letI := Φ.toHomeomorph.toOpenPartialHomeomorph.singletonChartedSpace (by simp)
  letI := ChartedSpace.comp H₁ H' N
  letI := Φ.isManifold_chartedSpaceComp N
  let e := Φ.chartedSpaceComp N
  have he (x : N) : e x = x := Φ.chartedSpaceComp_apply N x
  have hes (x : N) : e.symm x = x := Φ.chartedSpaceComp_symm_apply N x
  -- The identity-carrier diffeomorphism e is a local diffeomorphism to the new chart model.
  -- Its identity homomorphism therefore transports the smooth group operations to J₁.
  letI : LieGroup J₁ ∞ N := IsLocalDiffeomorph.lieGroup (I := J) (MonoidHom.id N)
    (by
      have hid : (e : N → N) = (MonoidHom.id N : N → N) := funext he
      exact hid ▸ e.isLocalDiffeomorph)
    Function.surjective_id
  -- Conjugating the original immersion by e.symm changes its source model to J₁.
  -- The equality hfun identifies this conjugate with the presenting homomorphism inc.
  have himm : Manifold.IsImmersion J₁ I ∞ (inc : N → G) := by
    have hfun : f ∘ e.symm = (inc : N → G) := by
      ext x
      simp only [Function.comp_apply, hes, hinc]
    exact Manifold.IsImmersionOfComplement.isImmersion (fun x ↦ hfun ▸
      isImmersionAtOfComplement_comp_diffeomorph_of_image_range_eq A hA e.symm le_rfl
        (hf.isImmersion.isImmersionOfComplement_complement (e.symm x)))
  let d : ImmersedLieSubgroupData I K :=
    { X := N
      E' := V
      H' := H₁
      I' := J₁
      toHom := inc
      injective := hi
      range_eq := SetLike.coe_injective <|
        (MonoidHom.coe_range inc).trans ((congrArg range (funext hinc)).trans hr)
      isImmersion := himm }
  refine ⟨d, e, ?_⟩
  intro x
  -- The private pair stores d.toHom as inc; expose that projection to apply hinc.
  change inc (e x) = f x
  rw [he, hinc]

variable {D : ∀ x : G, Submodule ℝ (TangentSpace I x)} {k : ℕ}
  (hinv : IsInvolutiveDistribution I D) (hD : IsContMDiffDistribution I ∞ k D)
  (K : Subgroup G) {f : N → G} (hf : IsIntegralManifold J ∞ D f)
  (hi : Injective f) (hr : range f = (K : Set G))

/-- An injective connected second-countable integral manifold with subgroup image has a native
immersed Lie-subgroup presentation. The carrier `X` is `N` with its intrinsic topology and the
presenting homomorphism agrees with `f`. Its chart model is changed to Euclidean space of
dimension `finrank ℝ F`, lifted into the ambient model universes. The diffeomorphism
`ofIntegralManifoldDiffeomorph` identifies the original and returned smooth structures. -/
def ofIntegralManifold : ImmersedLieSubgroupData I K :=
  (integralManifoldData hinv hD K hf hi hr).1

/-- The original integral manifold is diffeomorphic to the presenting manifold of the native
immersed subgroup. This identifies its original model with the lifted Euclidean chart model. -/
def ofIntegralManifoldDiffeomorph :
    N ≃ₘ⟮J, (ofIntegralManifold hinv hD K hf hi hr).I'⟯
      (ofIntegralManifold hinv hD K hf hi hr).X :=
  (integralManifoldData hinv hD K hf hi hr).2.1

/-- The intrinsic model comparison intertwines the native presenting homomorphism and the
original integral immersion. -/
@[simp]
theorem toHom_ofIntegralManifoldDiffeomorph (x : N) :
    (ofIntegralManifold hinv hD K hf hi hr).toHom
      (ofIntegralManifoldDiffeomorph hinv hD K hf hi hr x) = f x :=
  (integralManifoldData hinv hD K hf hi hr).2.2 x

/-- The inverse intrinsic model comparison recovers the original integral immersion. -/
theorem toHom_eq_apply_ofIntegralManifoldDiffeomorph_symm
    (x : (ofIntegralManifold hinv hD K hf hi hr).X) :
    (ofIntegralManifold hinv hD K hf hi hr).toHom x =
      f ((ofIntegralManifoldDiffeomorph hinv hD K hf hi hr).symm x) := by
  simpa only [Diffeomorph.apply_symm_apply] using
    (toHom_ofIntegralManifoldDiffeomorph hinv hD K hf hi hr
      ((ofIntegralManifoldDiffeomorph hinv hD K hf hi hr).symm x))

end TauCeti.Lie.ImmersedLieSubgroupData
