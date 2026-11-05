/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Monoidal.Pivotal.Spherical
public import TauCeti.QuantumGroups.UqSl2.LadderModule.Basic
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
of `UqSl2.Pivotal`, installed locally. The right, left and quantum dimensions of the signed
ladder module `L_m^ε` are `ε [m + 1]_q`.

## Main results

* `TauCeti.UqSl2.sphericalCategory_finiteModulePivotalCategory`: the pivotal structure is
  spherical for `q - q⁻¹ ≠ 0`.
* `TauCeti.UqSl2.rightDim_ladderModule`, `TauCeti.UqSl2.leftDim_ladderModule` and
  `TauCeti.UqSl2.quantumDim_ladderModule`: the dimensions of `L_m^ε` are `ε [m + 1]_q`.

## References

* C. Kassel, *Quantum Groups*, Chapter XIV.
* A. Virelizier, *Quantum groups*, Sections 2.3--2.4, for the modules `L_m^ε`.
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

variable {q}

/-- The trace of an element of `UqSl2 q` on a finite-dimensional module isomorphic to `L_m^ε` is
its trace through the ladder representation. -/
private theorem trace_lsmul_eq_trace_rep {m : ℕ} {ε : ℤˣ} {V : FiniteHopfModuleCat ℂ (UqSl2 q)}
    (e : V ≃ₗ[UqSl2 q] LadderModule q m ε) (a : UqSl2 q) :
    LinearMap.trace ℂ V (Algebra.lsmul ℂ ℂ V a) =
      LinearMap.trace ℂ _ (LadderModule.rep q m ε a) := by
  rw [← LinearMap.trace_conj' _ (e.restrictScalars ℂ)]
  congr 1
  ext x
  simp [LinearEquiv.conj_apply, ← LadderModule.smul_def]

/-- The right dimension of the signed ladder module `L_m^ε` is `ε [m + 1]_q`. -/
theorem rightDim_ladderModule (hq : q - q⁻¹ ≠ 0) (m : ℕ) (ε : ℤˣ) :
    letI := finiteModuleRigidCategory q
    letI := finiteModulePivotalCategory q
    rightDim (FiniteHopfModuleCat.of (k := ℂ) (H := UqSl2 q) (LadderModule q m ε)) =
      ((ε : ℂ) * quantumInteger q ((m : ℤ) + 1)) • 𝟙 (𝟙_ (FiniteHopfModuleCat ℂ (UqSl2 q))) := by
  let := finiteModuleRigidCategory q
  let := finiteModulePivotalCategory q
  rw [finiteModulePivotalCategory_def]
  refine (FiniteHopfModuleCat.rightDim_eq_smul (antipode_bijective q) (pivotalElement q)
    (antipode_antipode_eq_pivotalElement_mul_mul_antipode q) _).trans ?_
  rw [pivotalElement_val]
  exact congrArg (· • _) ((trace_lsmul_eq_trace_rep (LinearEquiv.refl _ _) (kInv q)).trans
    (LadderModule.trace_rep_kInv hq))

/-- The left dimension of the signed ladder module `L_m^ε` is `ε [m + 1]_q`. -/
theorem leftDim_ladderModule (hq : q - q⁻¹ ≠ 0) (m : ℕ) (ε : ℤˣ) :
    letI := finiteModuleRigidCategory q
    letI := finiteModulePivotalCategory q
    leftDim (FiniteHopfModuleCat.of (k := ℂ) (H := UqSl2 q) (LadderModule q m ε)) =
      ((ε : ℂ) * quantumInteger q ((m : ℤ) + 1)) • 𝟙 (𝟙_ (FiniteHopfModuleCat ℂ (UqSl2 q))) := by
  let := finiteModuleRigidCategory q
  let := finiteModulePivotalCategory q
  rw [finiteModulePivotalCategory_def]
  refine (FiniteHopfModuleCat.leftDim_eq_smul (antipode_bijective q) (pivotalElement q)
    (antipode_antipode_eq_pivotalElement_mul_mul_antipode q) _).trans ?_
  rw [pivotalElement_val, antipode_kInv]
  exact congrArg (· • _) ((trace_lsmul_eq_trace_rep (LinearEquiv.refl _ _) (k q)).trans
    (LadderModule.trace_rep_k hq))

/-- The quantum dimension of the signed ladder module `L_m^ε` is `ε [m + 1]_q`. -/
@[simp] theorem quantumDim_ladderModule (hq : q - q⁻¹ ≠ 0) (m : ℕ) (ε : ℤˣ) :
    letI := finiteModuleRigidCategory q
    letI := finiteModulePivotalCategory q
    haveI := sphericalCategory_finiteModulePivotalCategory q hq
    quantumDim (FiniteHopfModuleCat.of (k := ℂ) (H := UqSl2 q) (LadderModule q m ε)) =
      ((ε : ℂ) * quantumInteger q ((m : ℤ) + 1)) • 𝟙 (𝟙_ (FiniteHopfModuleCat ℂ (UqSl2 q))) := by
  let := finiteModuleRigidCategory q
  let := finiteModulePivotalCategory q
  have := sphericalCategory_finiteModulePivotalCategory q hq
  rw [quantumDim_eq_rightDim, rightDim_ladderModule hq]

end TauCeti.UqSl2
