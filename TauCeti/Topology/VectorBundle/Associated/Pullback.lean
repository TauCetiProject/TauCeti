/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.Associated.Basic
public import TauCeti.Topology.FiberBundle.Associated.Pullback
public import Mathlib.Topology.VectorBundle.Constructions

/-!
# Pullback of an associated vector bundle

When the structure group acts linearly on the model, the fibrewise comparison
`TauCeti.AssociatedBundle.pullbackEquiv` between associating after pullback and pulling back after
associating is a continuous linear equivalence
(`TauCeti.AssociatedBundle.pullbackContinuousLinearEquiv`). It still sends `[p, v]` to `[p, v]`,
and `simp` reduces it to `TauCeti.AssociatedBundle.pullbackEquiv`
(`TauCeti.AssociatedBundle.pullbackContinuousLinearEquiv_apply`,
`TauCeti.AssociatedBundle.pullbackContinuousLinearEquiv_symm_apply`).

## References

* I. Kolář, P. W. Michor, J. Slovák, *Natural Operations in Differential Geometry*,
  §§10.7 and 10.11.
-/

public section

noncomputable section

open Bundle

namespace TauCeti.AssociatedBundle

variable {𝕜 B B' G F : Type*} [NontriviallyNormedField 𝕜]
  [TopologicalSpace B] [TopologicalSpace B'] [Group G] [TopologicalSpace G]
  {P : B → Type*} [TopologicalSpace (TotalSpace G P)] [∀ b, TopologicalSpace (P b)]
  [FiberBundle G P] [∀ b, Nonempty (P b)] [∀ b, MulAction Gᵐᵒᵖ (P b)] [PrincipalBundle G P]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [DistribMulAction G F] [SMulCommClass G 𝕜 F] [ContinuousSMul G F]
  {K : Type*} [FunLike K B' B] [ContinuousMapClass K B' B] (f : K)

variable (𝕜) in
/-- The pullback comparison `TauCeti.AssociatedBundle.pullbackEquiv` as a continuous linear
equivalence. On classes it sends `[p, v]` to `[p, v]`. -/
def pullbackContinuousLinearEquiv (x : B') :
    AssociatedBundle G ((f : B' → B) *ᵖ P) F x ≃L[𝕜]
      ((f : B' → B) *ᵖ (AssociatedBundle G P F)) x :=
  (mkContinuousLinearEquiv 𝕜 G (P := (f : B' → B) *ᵖ P) (F := F)
      ((FiberBundle.homeomorphAt G P (f x)).symm 1)).symm.trans
    (mkContinuousLinearEquiv 𝕜 G (P := P) (F := F) ((FiberBundle.homeomorphAt G P (f x)).symm 1))

/-- The continuous linear pullback comparison is `TauCeti.AssociatedBundle.pullbackEquiv`. -/
@[simp]
theorem pullbackContinuousLinearEquiv_apply (x : B')
    (u : AssociatedBundle G ((f : B' → B) *ᵖ P) F x) :
    pullbackContinuousLinearEquiv 𝕜 f x u = pullbackEquiv f x u := by
  let p : P (f x) := (FiberBundle.homeomorphAt G P (f x)).symm 1
  let q : ((f : B' → B) *ᵖ P) x := p
  obtain ⟨w, rfl⟩ := (mk_bijective (G := G) (P := (f : B' → B) *ᵖ P) (F := F) q).surjective u
  rw [pullbackEquiv_mk]
  -- The composite applies `mkContinuousLinearEquiv (P := f *ᵖ P)` to the frame `p : P (f x)`,
  -- which is `(f *ᵖ P) x` only at default transparency, so `simp` cannot use
  -- `ContinuousLinearEquiv.trans_apply` here. `change` retypes that frame as `q`.
  change mkContinuousLinearEquiv 𝕜 G (P := P) (F := F) p
      ((mkContinuousLinearEquiv 𝕜 G (P := (f : B' → B) *ᵖ P) (F := F) q).symm (mk G q w)) = _
  simp [p]

/-- The inverse continuous linear pullback comparison is the inverse of
`TauCeti.AssociatedBundle.pullbackEquiv`. -/
@[simp]
theorem pullbackContinuousLinearEquiv_symm_apply (x : B')
    (u : ((f : B' → B) *ᵖ (AssociatedBundle G P F)) x) :
    (pullbackContinuousLinearEquiv 𝕜 f x).symm u = (pullbackEquiv f x).symm u :=
  (pullbackEquiv f x).eq_symm_apply.mpr
    ((pullbackContinuousLinearEquiv_apply f x _).symm.trans
      ((pullbackContinuousLinearEquiv 𝕜 f x).apply_symm_apply u))

end TauCeti.AssociatedBundle
