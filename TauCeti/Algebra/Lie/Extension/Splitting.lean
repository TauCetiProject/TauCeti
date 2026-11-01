/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Extension.Topology
public import TauCeti.Topology.Algebra.Module.LinearTopology.Splitting

/-!
# Cocycle models of split topological extensions

This file builds on `LieAlgebra.Extension.ofTwoCocycleEquiv` from
`TauCeti.Algebra.Lie.Extension.Basic`, the algebraic comparison sending `(x, m)` to
`s x + incl m` for a linear section of a Lie algebra extension with abelian kernel.

For a continuous section and projection with discrete kernel,
`LieAlgebra.Extension.continuous_ofTwoCocycleEquiv` and
`LieAlgebra.Extension.continuous_ofTwoCocycleEquiv_symm` prove continuity in both directions
for the discrete-coefficient topology on the cocycle model.
`LieAlgebra.Extension.ofTwoCocycleContinuousLinearEquiv` bundles the continuous linear
comparison. With a continuous bracket,
`LieAlgebra.Extension.twoCocycleOf_mem_continuousTwoCocycle` proves continuity of the native
cocycle. Finally, `LieAlgebra.Extension.exists_continuous_cocycleModel` supplies continuous
cocycle models for strict surjections from linearly topologized vector spaces with abelian
discrete kernel and jointly continuous bracket. This permits continuous cocycle classification
to be applied to actual extensions, not only to extensions already presented as sheared products.

The cocycle and its induced module structure are consumed directly from Mathlib's
`Algebra.Lie.Extension`; no alternate cocycle or sign convention is introduced.

## References

* E. Frenkel, *Langlands Correspondence for Loop Groups*, §1.3, for continuous
  cocycle models of extensions of formal loop algebras by discrete kernels.
-/

public section

noncomputable section

open Function Topology LieModule.Cohomology

namespace LieAlgebra.Extension

variable {R L M : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  [LieRing M] [LieAlgebra R M] (E : Extension R M L)

variable {s : L →ₗ[R] E.L} (hs : LeftInverse E.proj s) [IsLieAbelian M]

section Topology

variable [TopologicalSpace L] [TopologicalSpace E.L] [IsTopologicalAddGroup E.L]
  [DiscreteTopology E.proj.ker]

omit [IsLieAbelian M] in
/-- The kernel coordinate of a continuous splitting is locally constant when the kernel
is discrete. No topology on the coefficient type `M` is required. -/
theorem isLocallyConstant_splittingCoordinate (hp : Continuous E.proj) (hsc : Continuous s) :
    IsLocallyConstant (E.splittingCoordinate hs) := by
  have hd : Continuous (fun x : E.L ↦
      (⟨x - s (E.proj x), by simp [hs.eq]⟩ : E.proj.ker)) :=
    (continuous_id.sub (hsc.comp hp)).subtype_mk _
  have hcoord : (E.splittingCoordinate hs : E.L → M) =
      E.toKer.symm ∘ (fun x ↦ (⟨x - s (E.proj x), by simp [hs.eq]⟩ : E.proj.ker)) := by
    funext x
    exact E.splittingCoordinate_apply hs x
  rw [hcoord]
  exact (IsLocallyConstant.of_discrete (f := E.toKer.symm)).comp_continuous hd

omit [DiscreteTopology E.proj.ker] in
/-- The comparison from the discrete-coefficient cocycle model is continuous. -/
theorem continuous_ofTwoCocycleEquiv (hsc : Continuous s) :
    letI := E.ringModuleOf
    letI := E.lieModuleOf
    Continuous (E.ofTwoCocycleEquiv hs) := by
  let := E.ringModuleOf
  let := E.lieModuleOf
  refine ((hsc.comp (ofTwoCocycle.continuous_ofProd_symm_fst (E.twoCocycleOf hs))).add
    ((ofTwoCocycle.isLocallyConstant_snd (E.twoCocycleOf hs)).comp E.incl).continuous).congr ?_
  intro v
  obtain ⟨⟨x, m⟩, rfl⟩ := (ofProd (E.twoCocycleOf hs)).surjective v
  simp

/-- For a continuous projection and a continuous section with discrete kernel, the inverse
comparison into the discrete-coefficient cocycle model is continuous. -/
theorem continuous_ofTwoCocycleEquiv_symm (hp : Continuous E.proj) (hsc : Continuous s) :
    letI := E.ringModuleOf
    letI := E.lieModuleOf
    Continuous (E.ofTwoCocycleEquiv hs).symm := by
  let := E.ringModuleOf
  let := E.lieModuleOf
  apply ofTwoCocycle.continuous_iff.mpr
  simpa only [ofTwoCocycleEquiv_symm_apply, Equiv.symm_apply_apply] using
    And.intro hp (E.isLocallyConstant_splittingCoordinate hs hp hsc)

/-- The linear comparison of a continuously split extension with discrete kernel and its
native cocycle model is a continuous linear equivalence. Its underlying map is a Lie
equivalence, `ofTwoCocycleEquiv`. -/
def ofTwoCocycleContinuousLinearEquiv (hp : Continuous E.proj) (hsc : Continuous s) :
    letI := E.ringModuleOf
    letI := E.lieModuleOf
    LieAlgebra.ofTwoCocycle (E.twoCocycleOf hs) ≃L[R] E.L := by
  letI := E.ringModuleOf
  letI := E.lieModuleOf
  exact
    { (E.ofTwoCocycleEquiv hs).toLinearEquiv with
      continuous_toFun := E.continuous_ofTwoCocycleEquiv hs hsc
      continuous_invFun := E.continuous_ofTwoCocycleEquiv_symm hs hp hsc }

@[simp]
theorem coe_ofTwoCocycleContinuousLinearEquiv (hp : Continuous E.proj) (hsc : Continuous s) :
    letI := E.ringModuleOf
    letI := E.lieModuleOf
    ⇑(E.ofTwoCocycleContinuousLinearEquiv hs hp hsc) = E.ofTwoCocycleEquiv hs := (rfl)

@[simp]
theorem coe_ofTwoCocycleContinuousLinearEquiv_symm
    (hp : Continuous E.proj) (hsc : Continuous s) :
    letI := E.ringModuleOf
    letI := E.lieModuleOf
    ⇑(E.ofTwoCocycleContinuousLinearEquiv hs hp hsc).symm =
      (E.ofTwoCocycleEquiv hs).symm := (rfl)

/-- A continuous bracket and a continuous section produce a continuous native cocycle,
with discrete coefficients. -/
theorem twoCocycleOf_mem_continuousTwoCocycle [IsTopologicalAddGroup L]
    (hp : Continuous E.proj) (hsc : Continuous s)
    (hb : Continuous fun p : E.L × E.L ↦ ⁅p.1, p.2⁆) :
    letI := E.ringModuleOf
    letI := E.lieModuleOf
    (E.twoCocycleOf hs : twoCochain R L M) ∈
      TauCeti.LieModule.Cohomology.continuousTwoCocycle R L M := by
  let := E.ringModuleOf
  let := E.lieModuleOf
  let : TopologicalSpace M := ⊥
  have : DiscreteTopology M := ⟨rfl⟩
  refine TauCeti.LieModule.Cohomology.mem_continuousTwoCocycle_iff.mpr ⟨?_,
    (E.twoCocycleOf hs).property⟩
  rw [TauCeti.LieModule.Cohomology.mem_continuousTwoCochain_iff_continuous]
  have hc := (E.isLocallyConstant_splittingCoordinate hs hp hsc).continuous.comp
    (hb.comp (hsc.prodMap hsc))
  exact hc.congr fun p ↦ (E.twoCocycleOf_eq_splittingCoordinate hs p.1 p.2).symm

end Topology

section Strict

variable {K L M : Type*} [Field K] [LieRing L] [LieAlgebra K L]
  [LieRing M] [LieAlgebra K M] [IsLieAbelian M]
  (E : Extension K M L) [TopologicalSpace L] [IsTopologicalAddGroup L]
  [TopologicalSpace E.L] [IsTopologicalAddGroup E.L] [IsLinearTopology K E.L]
  [DiscreteTopology E.proj.ker]

/-- Every strict topological extension with abelian discrete kernel and linearly topologized
middle term with jointly continuous bracket has a continuous cocycle model. The comparison
is a homeomorphism, is over the identity on the quotient, and identifies the inclusion of
the given kernel with `(0, m)`. No finite-dimensionality or completeness hypothesis is required. -/
theorem exists_continuous_cocycleModel
    (hq : IsQuotientMap E.proj) (hb : Continuous fun p : E.L × E.L ↦ ⁅p.1, p.2⁆) :
    letI := E.ringModuleOf
    letI := E.lieModuleOf
    ∃ c : twoCocycle K L M,
      (c : twoCochain K L M) ∈ TauCeti.LieModule.Cohomology.continuousTwoCocycle K L M ∧
      ∃ e : LieAlgebra.ofTwoCocycle c ≃ₗ⁅K⁆ E.L,
        Continuous e ∧ Continuous e.symm ∧
        (∀ m, e (ofProd c (0, m)) = E.incl m) ∧
        ∀ v, E.proj (e v) = ofTwoCocycle.proj c v := by
  let := E.ringModuleOf
  let := E.lieModuleOf
  let p : E.L →L[K] L := ⟨E.proj.toLinearMap, hq.continuous⟩
  have hpker : p.ker = E.proj.ker.toSubmodule := by
    -- Bundling continuity leaves the projection and its kernel unchanged.
    rfl
  let : DiscreteTopology p.ker := by
    rw [hpker]
    exact inferInstanceAs (DiscreteTopology E.proj.ker)
  obtain ⟨s, hs⟩ := p.exists_rightInverse_of_isQuotientMap_of_discreteTopology_ker hq
  have hsProj : LeftInverse E.proj (s : L →ₗ[K] E.L) := by
    -- The continuous linear projection `p` has the same underlying function as `E.proj`.
    exact hs
  refine ⟨E.twoCocycleOf hsProj,
    E.twoCocycleOf_mem_continuousTwoCocycle hsProj hq.continuous s.continuous hb,
    E.ofTwoCocycleEquiv hsProj, E.continuous_ofTwoCocycleEquiv hsProj s.continuous,
    E.continuous_ofTwoCocycleEquiv_symm hsProj hq.continuous s.continuous, ?_,
    E.proj_ofTwoCocycleEquiv hsProj⟩
  intro m
  simp

end Strict

end LieAlgebra.Extension
