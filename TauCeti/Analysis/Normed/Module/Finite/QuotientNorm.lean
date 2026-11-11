/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Group.Quotient
public import TauCeti.Analysis.Normed.Module.Quotient
public import TauCeti.RingTheory.Huber.ClosedSubmodule
public import Mathlib.Topology.MetricSpace.Ultra.Pi

/-!
# Quotient norms on finite modules

A finite presentation of a module over a complete noetherian ultrametric normed ring whose
norm topology is Tate gives it a complete, contractive ultrametric norm. This is the infimum of
the maximum norms of its lifts,
not a choice of a least-norm representative. Its topology is the native `moduleTopology`, so
changing the finite presentation does not change the topology.

`LinearMap.finiteQuotientNorm` constructs this norm from any finite free surjection.
`TauCeti.exists_complete_norm_of_module_finite` supplies a norm without choosing generators at
the call site. The constructions retain the original additive group and scalar action and install
no global norm instance on an algebraic finite module. Only the ultrametricity assertion needs
the ring norm to be ultrametric; the other constructions apply to any normed ring with these
topological Tate, completeness and noetherian hypotheses.

The closedness input is `TauCeti.Huber.isClosed_of_isNoetherian`; the norm and completeness come
from Mathlib's native normed quotient and the first isomorphism theorem.

## References

* S. Bosch, U. Güntzer and R. Remmert, *Non-Archimedean Analysis*, §3.7.
* C. Johansson and J. Newton, *Extended eigenvarieties for overconvergent cohomology*,
  arXiv:1604.07739, §2.1.
-/

public section

namespace LinearMap

variable {R M ι : Type*} [NormedCommRing R]
  [TauCeti.Huber.IsTateRing R] [CompleteSpace R] [IsNoetherianRing R]
  [AddCommGroup M] [Module R M] [Fintype ι]

/-- The quotient norm associated to a finite free surjection, using the maximum norm on its
source. It is an infimum over lifts; no norm-minimising lift is required. -/
noncomputable def finiteQuotientNorm (f : (ι → R) →ₗ[R] M) (hf : Function.Surjective f) :
    AddGroupNorm M := by
  letI : IsClosed (f.ker : Set (ι → R)) := TauCeti.Huber.isClosed_of_isNoetherian f.ker
  let e := (f.quotKerEquivOfSurjective hf).symm
  letI := NormedAddCommGroup.induced M ((ι → R) ⧸ f.ker) e e.injective
  exact normAddGroupNorm M

variable (f : (ι → R) →ₗ[R] M) (hf : Function.Surjective f)

/-- The quotient norm is the native quotient norm transported through the first isomorphism
theorem. -/
theorem finiteQuotientNorm_apply (m : M) :
    f.finiteQuotientNorm hf m = ‖(f.quotKerEquivOfSurjective hf).symm m‖ := by
  rfl

/-- With its quotient norm a finite module is linearly isometric to the native quotient by the
kernel of its presentation. -/
noncomputable def finiteQuotientNormEquiv :
    letI := (f.finiteQuotientNorm hf).toNormedAddCommGroup
    M ≃ₗᵢ[R] ((ι → R) ⧸ f.ker) := by
  letI := (f.finiteQuotientNorm hf).toNormedAddCommGroup
  exact { (f.quotKerEquivOfSurjective hf).symm with
    norm_map' m := (f.finiteQuotientNorm_apply hf m).symm }

/-- The quotient-norm isometry sends a vector to its class under the first isomorphism theorem. -/
@[simp]
theorem finiteQuotientNormEquiv_apply (m : M) :
    letI := (f.finiteQuotientNorm hf).toNormedAddCommGroup
    f.finiteQuotientNormEquiv hf m = (f.quotKerEquivOfSurjective hf).symm m := by
  rfl

/-- The inverse quotient-norm isometry is induced by the presentation map. -/
@[simp]
theorem finiteQuotientNormEquiv_symm_apply (q : (ι → R) ⧸ f.ker) :
    letI := (f.finiteQuotientNorm hf).toNormedAddCommGroup
    (f.finiteQuotientNormEquiv hf).symm q = f.quotKerEquivOfSurjective hf q := by
  rfl

/-- The presentation map is norm-decreasing for its quotient norm. -/
theorem finiteQuotientNorm_apply_le (x : ι → R) :
    f.finiteQuotientNorm hf (f x) ≤ ‖x‖ := by
  rw [finiteQuotientNorm_apply, quotKerEquivOfSurjective_symm_apply]
  exact Submodule.Quotient.norm_mk_le f.ker x

/-- A quotient norm is less than `r` exactly when there is a lift of norm less than `r`.
This also characterises the norm when the infimum is not attained. -/
theorem finiteQuotientNorm_lt_iff (m : M) (r : ℝ) :
    f.finiteQuotientNorm hf m < r ↔ ∃ x : ι → R, f x = m ∧ ‖x‖ < r := by
  rw [finiteQuotientNorm_apply]
  refine (QuotientAddGroup.norm_lt_iff (S := f.ker.toAddSubgroup)
    (x := (f.quotKerEquivOfSurjective hf).symm m)).trans ?_
  refine exists_congr fun x ↦ ?_
  -- Express the additive-subgroup quotient equality in the submodule quotient so that the
  -- linear equivalence rewrite can match its carrier and representative map.
  change (Submodule.Quotient.mk x = (f.quotKerEquivOfSurjective hf).symm m ∧ ‖x‖ < r) ↔ _
  rw [LinearEquiv.eq_symm_apply, quotKerEquivOfSurjective_apply_mk]

/-- Quotient norms on finite modules are ultrametric. -/
theorem isUltrametricDist_finiteQuotientNorm [IsUltrametricDist R] :
    let := (f.finiteQuotientNorm hf).toNormedAddCommGroup
    IsUltrametricDist M := by
  let := (f.finiteQuotientNorm hf).toNormedAddCommGroup
  let e := f.finiteQuotientNormEquiv hf
  exact IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm fun x y ↦ by
    simpa only [← e.norm_map, map_add] using IsUltrametricDist.norm_add_le_max (e x) (e y)

/-- The original scalar action is contractive for the quotient norm. -/
theorem isBoundedSMul_finiteQuotientNorm :
    let := (f.finiteQuotientNorm hf).toNormedAddCommGroup
    IsBoundedSMul R M := by
  let := (f.finiteQuotientNorm hf).toNormedAddCommGroup
  let e := f.finiteQuotientNormEquiv hf
  exact .of_norm_smul_le fun a m ↦ by
    simpa only [← e.norm_map, map_smul] using norm_smul_le a (e m)

/-- The quotient norm is complete because its presentation kernel is closed. -/
theorem completeSpace_finiteQuotientNorm :
    let := (f.finiteQuotientNorm hf).toNormedAddCommGroup
    CompleteSpace M := by
  let := (f.finiteQuotientNorm hf).toNormedAddCommGroup
  exact (f.finiteQuotientNormEquiv hf).toIsometryEquiv.completeSpace

/-- The topology of the quotient norm is the canonical module topology, independently of the
chosen finite free presentation. -/
theorem isModuleTopology_finiteQuotientNorm :
    let := (f.finiteQuotientNorm hf).toNormedAddCommGroup
    IsModuleTopology R M := by
  let := (f.finiteQuotientNorm hf).toNormedAddCommGroup
  have := f.isBoundedSMul_finiteQuotientNorm hf
  have := f.completeSpace_finiteQuotientNorm hf
  have : Module.Finite R M := Module.Finite.of_surjective f hf
  exact TauCeti.Huber.IsTateRing.isModuleTopology

end LinearMap

namespace TauCeti

/-- A finite module over a complete noetherian ultrametric normed ring with Tate topology admits
a complete, contractive ultrametric norm inducing the canonical module topology. The norm is not
installed globally, and the existing additive group and module structure are unchanged. -/
theorem exists_complete_norm_of_module_finite (R M : Type*) [NormedCommRing R] [IsUltrametricDist R]
    [TauCeti.Huber.IsTateRing R] [CompleteSpace R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] :
    ∃ p : AddGroupNorm M, let := p.toNormedAddCommGroup
      CompleteSpace M ∧ IsUltrametricDist M ∧ IsBoundedSMul R M ∧ IsModuleTopology R M := by
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' R M
  exact ⟨f.finiteQuotientNorm hf, f.completeSpace_finiteQuotientNorm hf,
    f.isUltrametricDist_finiteQuotientNorm hf, f.isBoundedSMul_finiteQuotientNorm hf,
    f.isModuleTopology_finiteQuotientNorm hf⟩

end TauCeti
