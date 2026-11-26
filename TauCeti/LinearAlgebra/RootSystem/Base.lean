/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.RootSystem.Base
public import TauCeti.LinearAlgebra.RootSystem.Basic

/-!
# Bases of root pairings

This file records basic properties of `RootPairing.Base` that depend only on the definition of a
base in Mathlib and `RootPairing.corootKer`.

## Main results

* `RootPairing.Base.ext`: a base is determined by its support, the indices of its simple roots.
* `RootPairing.coroot'_eq_zero_of_forall_mem_support`: a weight killed by the simple coroots is
  killed by every coroot.
* `RootPairing.Base.iInf_ker_coroot'_support_eq_corootKer`: the common kernel of the simple coroot
  functionals equals `P.corootKer`.
-/

public section

namespace RootPairing

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- **A base is determined by its simple roots.** The other fields of a base are propositions about
its support. -/
@[ext]
theorem Base.ext {P : RootPairing ι R M N} {b b' : P.Base} (h : b.support = b'.support) :
    b = b' := by
  cases b
  cases b'
  subst h
  rfl

/-- **A weight killed by the simple coroots is killed by every coroot**, since every coroot is an
integer combination of the simple coroots. -/
theorem coroot'_eq_zero_of_forall_mem_support (P : RootPairing ι R M N) (b : P.Base) {x : M}
    (hx : ∀ i ∈ b.support, P.coroot' i x = 0) (j : ι) : P.coroot' j x = 0 :=
  LinearMap.eqOn_span (R := ℤ) (f := (P.toLinearMap x).toAddMonoidHom.toIntLinearMap) (g := 0)
    (by rintro _ ⟨i, hi, rfl⟩; exact hx i hi) (b.coroot_mem_span_int j)

/-- For any base `b`, the common kernel of the *simple* coroot functionals equals `P.corootKer`. -/
theorem Base.iInf_ker_coroot'_support_eq_corootKer {P : RootPairing ι R M N} (b : P.Base) :
    (⨅ i ∈ b.support, LinearMap.ker (P.coroot' i)) = P.corootKer := by
  ext x
  simp only [Submodule.mem_iInf, LinearMap.mem_ker, RootPairing.mem_corootKer]
  exact ⟨fun hx ↦ P.coroot'_eq_zero_of_forall_mem_support b hx, fun hx i _ ↦ hx i⟩

end RootPairing
