/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.RootSystem.Defs
import Mathlib.RingTheory.Finiteness.Basic

/-!
# Basic facts about root systems

Elementary consequences of the definition of a root pairing or root system that need no further
theory.

## Main definitions

* `RootPairing.corootKer`: the central kernel `⨅ i, LinearMap.ker (P.coroot' i)` of a root
  pairing.

## Main results

* `RootPairing.nonempty_of_isRootSystem`: a root system on a nontrivial module has a root.
* `RootPairing.finite_weight_of_isRootSystem`: the weight module of a finite root system is finitely
  generated.
* `RootPairing.corootKer_eq_bot`: the central kernel of a root system is trivial.
* `RootPairing.reflection_apply_of_mem_corootKer`: every root reflection fixes `P.corootKer`
  pointwise.
-/

public section

namespace RootPairing

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N]
  [Module R N]

/-- A root system on a nontrivial module has a root. -/
lemma nonempty_of_isRootSystem [Nontrivial M] (P : RootPairing ι R M N) [P.IsRootSystem] :
    Nonempty ι := by
  by_contra! h
  have hspan := IsRootSystem.span_root_eq_top (P := P)
  rw [Set.range_eq_empty, Submodule.span_empty] at hspan
  exact bot_ne_top hspan

/-- On a finite root system, the weight module is finitely generated because it is spanned by the
finite set of roots. -/
theorem finite_weight_of_isRootSystem (P : RootPairing ι R M N) [Finite ι] [P.IsRootSystem] :
    Module.Finite R M :=
  Module.finite_def.mpr
    (IsRootSystem.span_root_eq_top (P := P) ▸ Submodule.fg_span (Set.finite_range P.root))

section CorootKer

variable (P : RootPairing ι R M N)

/-- The **central kernel** of a root pairing: the common kernel of all coroot functionals
`P.coroot' i`. -/
def corootKer : Submodule R M :=
  ⨅ i, LinearMap.ker (P.coroot' i)

/-- The defining equation of `RootPairing.corootKer` as an infimum of kernels. -/
theorem corootKer_def : P.corootKer = ⨅ i, LinearMap.ker (P.coroot' i) :=
  (rfl)

variable {P} in
/-- Membership in the central kernel means vanishing under every coroot functional. -/
@[simp]
theorem mem_corootKer {x : M} : x ∈ P.corootKer ↔ ∀ i, P.coroot' i x = 0 := by
  simp [corootKer_def]

/-- The central kernel of a root system is trivial. -/
@[simp]
theorem corootKer_eq_bot [P.IsRootSystem] : P.corootKer = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Submodule.mem_bot]
  apply (LinearMap.IsPerfPair.bijective_left P.toLinearMap).injective
  rw [map_zero]
  exact LinearMap.ext_on_range (IsRootSystem.span_coroot_eq_top (P := P)) fun i ↦
    mem_corootKer.mp hx i

variable {P}

/-- Every root reflection fixes `P.corootKer` pointwise. -/
theorem reflection_apply_of_mem_corootKer {x : M} (hx : x ∈ P.corootKer) (i : ι) :
    P.reflection i x = x := by
  rw [reflection_apply, mem_corootKer.mp hx i, zero_smul, sub_zero]

end CorootKer

end RootPairing
