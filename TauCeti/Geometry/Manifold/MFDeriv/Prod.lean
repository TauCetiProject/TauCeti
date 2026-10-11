/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
public import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
public import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.LeftInverse

/-!
# Derivatives of maps that factor through a projection

A map `g ∘ Prod.fst` on a product `M × N` depends on the first factor only, and its derivative at
`p` is the derivative of `g` at `p.1` applied to the first component of a tangent vector; similarly
for `g ∘ Prod.snd`. No differentiability hypothesis is needed: when `g` is not differentiable at
`p.1`, neither is `g ∘ Prod.fst` at `p`, since `g` is recovered from it by composing with
`x ↦ (x, p.2)`, so both derivatives vanish.

These are the chain-rule identities used to differentiate functions of one factor along vector
fields on a product manifold.

## Main results

* `TauCeti.mfderiv_comp_fst` and `TauCeti.mfderiv_comp_snd`: the derivative of a map that factors
  through a projection.
* `TauCeti.mvfderiv_comp_fst_apply` and `TauCeti.mvfderiv_comp_snd_apply`: the same for
  vector-valued functions, applied to a tangent vector.
* `MDifferentiableAt.hasLeftInverse_mfderiv_fst_prod_iff`: the differential of a
  parameter-preserving map splits exactly when the differential of its slice splits.
-/

public section

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners 𝕜 E' H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
  {H'' : Type*} [TopologicalSpace H''] {I'' : ModelWithCorners 𝕜 E'' H''}
  {M'' : Type*} [TopologicalSpace M''] [ChartedSpace H'' M'']
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- The derivative of `g ∘ Prod.fst` at `p` is the derivative of `g` at `p.1` applied to the first
component. No differentiability is needed: both sides vanish when `g` is not differentiable. -/
theorem mfderiv_comp_fst (g : M → M'') (p : M × N) :
    mfderiv (I.prod J) I'' (g ∘ Prod.fst) p =
      (mfderiv I I'' g p.1).comp (ContinuousLinearMap.fst 𝕜 (TangentSpace I p.1)
        (TangentSpace J p.2)) := by
  by_cases hg : MDifferentiableAt I I'' g p.1
  · rw [mfderiv_comp p hg mdifferentiableAt_fst, mfderiv_fst]
    -- The sides differ only in the tangent-space index `(g ∘ Prod.fst) p`, which is `g p.1`.
    rfl
  · have hι : MDifferentiableAt I (I.prod J) (fun x : M ↦ (x, p.2)) p.1 :=
      mdifferentiableAt_id.prodMk mdifferentiableAt_const
    have hcomp : ¬MDifferentiableAt (I.prod J) I'' (g ∘ Prod.fst) p := fun h ↦
      hg (h.comp_of_eq _ hι (Prod.mk.eta (p := p)))
    rw [mfderiv_zero_of_not_mdifferentiableAt hg, mfderiv_zero_of_not_mdifferentiableAt hcomp,
      ContinuousLinearMap.zero_comp]
    -- Both zeros live in the same space of linear maps, up to the index of the target tangent
    -- space.
    rfl

/-- The derivative of `g ∘ Prod.snd` at `p` is the derivative of `g` at `p.2` applied to the second
component. No differentiability is needed: both sides vanish when `g` is not differentiable. -/
theorem mfderiv_comp_snd (g : N → M'') (p : M × N) :
    mfderiv (I.prod J) I'' (g ∘ Prod.snd) p =
      (mfderiv J I'' g p.2).comp (ContinuousLinearMap.snd 𝕜 (TangentSpace I p.1)
        (TangentSpace J p.2)) := by
  by_cases hg : MDifferentiableAt J I'' g p.2
  · rw [mfderiv_comp p hg mdifferentiableAt_snd, mfderiv_snd]
    -- The sides differ only in the tangent-space index `(g ∘ Prod.snd) p`, which is `g p.2`.
    rfl
  · have hι : MDifferentiableAt J (I.prod J) (fun y : N ↦ (p.1, y)) p.2 :=
      mdifferentiableAt_const.prodMk mdifferentiableAt_id
    have hcomp : ¬MDifferentiableAt (I.prod J) I'' (g ∘ Prod.snd) p := fun h ↦
      hg (h.comp_of_eq _ hι (Prod.mk.eta (p := p)))
    rw [mfderiv_zero_of_not_mdifferentiableAt hg, mfderiv_zero_of_not_mdifferentiableAt hcomp,
      ContinuousLinearMap.zero_comp]
    -- Both zeros live in the same space of linear maps, up to the index of the target tangent
    -- space.
    rfl

/-- The derivative of a vector-valued function of the first factor, read on a product. -/
theorem mvfderiv_comp_fst_apply (g : M → F) (p : M × N) (v : TangentSpace (I.prod J) p) :
    mvfderiv (I.prod J) (g ∘ Prod.fst) p v = mvfderiv I g p.1 v.1 := by
  rw [mvfderiv, mvfderiv, ContinuousLinearMap.comp_apply, mfderiv_comp_fst]
  -- The identifications `NormedSpace.fromTangentSpace` at `(g ∘ Prod.fst) p` and at `g p.1` agree,
  -- as these points are equal by definition.
  rfl

/-- The derivative of a vector-valued function of the second factor, read on a product. -/
theorem mvfderiv_comp_snd_apply (g : N → F) (p : M × N) (v : TangentSpace (I.prod J) p) :
    mvfderiv (I.prod J) (g ∘ Prod.snd) p v = mvfderiv J g p.2 v.2 := by
  rw [mvfderiv, mvfderiv, ContinuousLinearMap.comp_apply, mfderiv_comp_snd]
  -- The identifications `NormedSpace.fromTangentSpace` at `(g ∘ Prod.snd) p` and at `g p.2` agree,
  -- as these points are equal by definition.
  rfl

end TauCeti

open scoped Manifold

section ParameterPreserving

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E E' F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {H H' G : Type*} [TopologicalSpace H] [TopologicalSpace H'] [TopologicalSpace G]
  {I : ModelWithCorners 𝕜 E H} {I' : ModelWithCorners 𝕜 E' H'}
  {J : ModelWithCorners 𝕜 F G}
  {M M' N : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace M'] [ChartedSpace H' M'] [TopologicalSpace N] [ChartedSpace G N]
  {f : M × M' → N} {p : M × M'}

/-- The differential of a parameter-preserving map has a continuous linear left inverse
if and only if the differential of its slice at the fixed parameter does.
This holds for manifolds with corners and infinite-dimensional models. -/
theorem MDifferentiableAt.hasLeftInverse_mfderiv_fst_prod_iff
    (hf : MDifferentiableAt (I.prod I') J f p) :
    (mfderiv (I.prod I') (I.prod J) (fun q => (q.1, f q)) p).HasLeftInverse ↔
      (mfderiv I' J (fun x => f (p.1, x)) p.2).HasLeftInverse := by
  rw [mfderiv_prodMk mdifferentiableAt_fst hf, mfderiv_fst]
  -- Product tangent spaces use the model product, but their instance definitions
  -- require reducible unfolding to apply the operator-level product criterion.
  erw [ContinuousLinearMap.hasLeftInverse_fst_prod_iff]
  have hι : MDifferentiableAt I' (I.prod I') (fun x : M' => (p.1, x)) p.2 :=
    mdifferentiableAt_const.prodMk mdifferentiableAt_id
  have hslice := mfderiv_comp_of_eq hf hι (Prod.mk.eta (p := p))
  rw [mfderiv_prod_right] at hslice
  -- The composite with the fixed-parameter inclusion is precisely the slice; the
  -- tangent-space indices at `p` and `(p.1, p.2)` agree by the product eta law.
  exact (congrArg ContinuousLinearMap.HasLeftInverse hslice.symm).to_iff

end ParameterPreserving
