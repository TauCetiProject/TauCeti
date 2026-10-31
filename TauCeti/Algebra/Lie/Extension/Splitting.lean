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

A linear section of a Lie algebra extension with abelian kernel identifies the extension
with the cocycle model of Mathlib's `LieAlgebra.Extension.twoCocycleOf`. The identification
sends `(x, m)` to `s x + incl m`, preserves the inclusion and projection, and does not assert
that the section is a Lie homomorphism.

If the section and projection are continuous and the kernel is discrete, this identification
is a homeomorphism for the discrete-coefficient topology on the cocycle model. Continuity of
the bracket then implies continuity of the native cocycle. In particular, strict surjections
from linearly topologized vector spaces with discrete kernel admit such continuous cocycle
models. This permits continuous cocycle classification to be applied to actual extensions,
not only to extensions already presented as sheared products.

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

/-- The kernel equivalence is the inclusion on underlying elements. -/
@[simp]
theorem coe_toKer (m : M) : (E.toKer m : E.L) = E.incl m := (rfl)

/-- Inverting the kernel equivalence recovers the underlying element by inclusion. -/
@[simp]
theorem incl_toKer_symm (v : E.proj.ker) : E.incl (E.toKer.symm v) = v := by
  rw [← coe_toKer, LieEquiv.apply_symm_apply]

variable {s : L →ₗ[R] E.L} (hs : LeftInverse E.proj s)

/-- The kernel coordinate relative to a linear section, namely `x - s (proj x)`. -/
def splittingCoordinate : E.L →ₗ[R] M :=
  E.toKer.symm.toLinearMap.comp
    ((LinearMap.id - s.comp E.proj.toLinearMap).codRestrict E.proj.ker.toSubmodule
      (fun x ↦ by simp [hs.eq]))

/-- Including the kernel coordinate gives the difference from the section. -/
@[simp]
theorem incl_splittingCoordinate (x : E.L) :
    E.incl (E.splittingCoordinate hs x) = x - s (E.proj x) := by
  exact E.incl_toKer_symm _

/-- The kernel coordinate vanishes on the section. -/
@[simp]
theorem splittingCoordinate_section (x : L) : E.splittingCoordinate hs (s x) = 0 := by
  apply E.incl_injective
  simp [hs x]

/-- The kernel coordinate is a retraction of the inclusion. -/
@[simp]
theorem splittingCoordinate_incl (m : M) : E.splittingCoordinate hs (E.incl m) = m := by
  apply E.incl_injective
  simp

variable [IsLieAbelian M]

/-- Including the native cocycle gives the defect of the section from preserving brackets. -/
theorem incl_twoCocycleOf (x y : L) :
    letI := E.ringModuleOf
    letI := E.lieModuleOf
    E.incl ((E.twoCocycleOf hs : L →ₗ[R] L →ₗ[R] M) x y) = ⁅s x, s y⁆ - s ⁅x, y⁆ := by
  exact E.incl_toKer_symm _

/-- The induced quotient action is computed by the bracket with any lift. -/
theorem incl_lie (hs : LeftInverse E.proj s) (x : L) (m : M) :
    letI := E.ringModuleOf
    E.incl ⁅x, m⁆ = ⁅s x, E.incl m⁆ := by
  let := E.ringModuleOf
  have h := E.ringModuleOf_bracket_proj m (s x)
  rw [hs x] at h
  rw [h, incl_toKer_symm]
  rfl

/-- A split extension with abelian kernel is isomorphic to the model of its native cocycle.
The coordinates are `s x + incl m`; the section itself need not preserve brackets. -/
def ofTwoCocycleEquiv :
    letI := E.ringModuleOf
    letI := E.lieModuleOf
    LieAlgebra.ofTwoCocycle (E.twoCocycleOf hs) ≃ₗ⁅R⁆ E.L := by
  letI := E.ringModuleOf
  letI := E.lieModuleOf
  let c := E.twoCocycleOf hs
  exact
    { toFun v := s ((ofProd c).symm v).1 + E.incl ((ofProd c).symm v).2
      invFun x := ofProd c (E.proj x, E.splittingCoordinate hs x)
      map_add' _ _ := by simp; abel
      map_smul' _ _ := by simp [smul_add]
      left_inv v := by
        apply (ofProd c).symm.injective
        simp [hs.eq]
      right_inv x := by simp
      map_lie' {v w} := by
        simp only [bracket_ofTwoCocycle, c, Equiv.symm_apply_apply, map_sub, map_add]
        rw [E.incl_twoCocycleOf hs, E.incl_lie hs, E.incl_lie hs]
        simp only [lie_add, add_lie, ← LieHom.map_lie, trivial_lie_zero M M, map_zero,
          add_zero]
        rw [← lie_skew (s ((ofProd c).symm w).1) (E.incl ((ofProd c).symm v).2)]
        abel }

/-- The comparison sends product coordinates to the section plus the inclusion. -/
@[simp]
theorem ofTwoCocycleEquiv_ofProd (x : L) (m : M) :
    letI := E.ringModuleOf
    letI := E.lieModuleOf
    E.ofTwoCocycleEquiv hs (ofProd (E.twoCocycleOf hs) (x, m)) = s x + E.incl m := (rfl)

/-- The inverse comparison consists of the projection and the kernel coordinate. -/
@[simp]
theorem ofTwoCocycleEquiv_symm_apply (x : E.L) :
    letI := E.ringModuleOf
    letI := E.lieModuleOf
    (E.ofTwoCocycleEquiv hs).symm x =
      ofProd (E.twoCocycleOf hs) (E.proj x, E.splittingCoordinate hs x) := (rfl)

/-- The comparison is over the identity on the quotient. -/
@[simp]
theorem proj_ofTwoCocycleEquiv :
    letI := E.ringModuleOf
    letI := E.lieModuleOf
    ∀ v, E.proj (E.ofTwoCocycleEquiv hs v) = ofTwoCocycle.proj (E.twoCocycleOf hs) v := by
  let := E.ringModuleOf
  let := E.lieModuleOf
  intro v
  obtain ⟨⟨x, m⟩, rfl⟩ := (ofProd (E.twoCocycleOf hs)).surjective v
  simp [hs x]

/-- The native cocycle is the kernel coordinate of the bracket of section elements. -/
theorem twoCocycleOf_eq_splittingCoordinate (x y : L) :
    letI := E.ringModuleOf
    letI := E.lieModuleOf
    (E.twoCocycleOf hs : L →ₗ[R] L →ₗ[R] M) x y =
      E.splittingCoordinate hs ⁅s x, s y⁆ := by
  apply E.incl_injective
  simp [hs.eq, LieHom.map_lie]

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
  exact (IsLocallyConstant.of_discrete (f := E.toKer.symm)).comp_continuous hd

omit [DiscreteTopology E.proj.ker] in
/-- The comparison from the discrete-coefficient cocycle model is continuous. -/
theorem continuous_ofTwoCocycleEquiv (hsc : Continuous s) :
    letI := E.ringModuleOf
    letI := E.lieModuleOf
    Continuous (E.ofTwoCocycleEquiv hs) := by
  let := E.ringModuleOf
  let := E.lieModuleOf
  exact (hsc.comp (ofTwoCocycle.continuous_ofProd_symm_fst _)).add
    ((ofTwoCocycle.isLocallyConstant_snd _).comp E.incl).continuous

/-- The inverse comparison is continuous because its quotient coordinate is continuous
and its kernel coordinate is locally constant. -/
theorem continuous_ofTwoCocycleEquiv_symm (hp : Continuous E.proj) (hsc : Continuous s) :
    letI := E.ringModuleOf
    letI := E.lieModuleOf
    Continuous (E.ofTwoCocycleEquiv hs).symm := by
  let := E.ringModuleOf
  let := E.lieModuleOf
  exact ofTwoCocycle.continuous_iff.mpr
    ⟨hp, E.isLocallyConstant_splittingCoordinate hs hp hsc⟩

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
middle term has a continuous cocycle model. The comparison is a homeomorphism, is over the
identity on the quotient, and identifies the inclusion of the given kernel with `(0, m)`.
No finite-dimensionality or completeness hypothesis is required. -/
theorem exists_continuous_cocycleModel (hp : Continuous E.proj)
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
  let p : E.L →L[K] L := ⟨E.proj.toLinearMap, hp⟩
  let : DiscreteTopology p.ker := inferInstanceAs (DiscreteTopology E.proj.ker)
  obtain ⟨s, hs⟩ := p.exists_rightInverse_of_isQuotientMap_of_discreteTopology_ker hq
  refine ⟨E.twoCocycleOf hs, E.twoCocycleOf_mem_continuousTwoCocycle hs hp s.continuous hb,
    E.ofTwoCocycleEquiv hs, E.continuous_ofTwoCocycleEquiv hs s.continuous,
    E.continuous_ofTwoCocycleEquiv_symm hs hp s.continuous, ?_,
    E.proj_ofTwoCocycleEquiv hs⟩
  intro m
  simp

end Strict

end LieAlgebra.Extension
