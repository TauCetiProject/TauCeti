/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Monoidal.Pivotal.Spherical
public import TauCeti.QuantumGroups.UqSl2.Pivotal
public import TauCeti.QuantumGroups.UqSl2.QuantumTrace

/-!
# Spherical finite-dimensional `U_q(sl₂)`-modules

For `q ≠ 0` and `q - q⁻¹ ≠ 0`, the pivotal structure with pivot `K⁻¹` is spherical: its
left and right categorical traces agree on every module endomorphism. The generic Hopf-module
trace formulas identify these traces with `tr(K f)` and `tr(K⁻¹ f)`. Their equality follows
from the defining commutator relation. No semisimplicity assumption is needed; roots of unity
are allowed provided `q ≠ 0` and `q - q⁻¹ ≠ 0`.

The spherical structure uses the named inverse-antipode rigid structure and pivotal structure
of `UqSl2.Pivotal`, installed locally.

## References

* C. Kassel, *Quantum Groups*, Chapter XIV.
-/

public noncomputable section

open CategoryTheory MonoidalCategory

namespace TauCeti.UqSl2

variable (q : ℂ) [Fact (q ≠ 0)]

/-- The finite-dimensional modules of `U_q(sl₂)` are spherical under the pivot `K⁻¹` whenever
`q ≠ 0` and `q - q⁻¹ ≠ 0`, with no semisimplicity assumption. -/
theorem sphericalCategory_finiteModulePivotalCategory (hq : q - q⁻¹ ≠ 0) :
    letI := finiteModuleRigidCategory q
    letI := finiteModulePivotalCategory q
    SphericalCategory (FiniteHopfModuleCat ℂ (UqSl2 q)) := by
  let := finiteModuleRigidCategory q
  let := finiteModulePivotalCategory q
  constructor
  intro M f
  apply FiniteHopfModuleCat.hom_ext
  ext c
  rw [leftTrace_apply, rightTrace_apply]
  rw [trace_lsmul_k_comp_eq_trace_lsmul_kInv_comp hq]

end TauCeti.UqSl2
