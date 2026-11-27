/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.RootSystem.Defs
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.RingTheory.Finiteness.Basic

/-!
# Basic facts about root systems

Elementary consequences of the definition of a root pairing or root system that need no further
theory.

## Main definitions

* `RootPairing.corootKer`: the central kernel `⨅ i, LinearMap.ker (P.coroot' i)` of a root
  pairing.

## Main results

* `RootPairing.ext_of_coroot`: two root pairings with the same pairing map, root embedding, and
  coroot embedding are equal.
* `RootPairing.nonempty_of_isRootSystem`: a root system on a nontrivial module has a root.
* `RootPairing.finite_weight_of_isRootSystem`: the weight module of a finite root system is finitely
  generated.
* `RootPairing.not_isOfFinAddOrder_root`: in characteristic zero, a root has infinite additive
  order.
* `RootPairing.reflection_apply_eq_self_of_mem_corootKer`: every root reflection fixes `P.corootKer`
  pointwise.
-/

public section

namespace RootPairing

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N]
  [Module R N]

/-- Two root pairings with the same pairing map, root embedding, and coroot embedding are equal.
Unlike `RootPairing.ext`, no characteristic-zero, domain, or finiteness hypotheses are needed, as
equality of the coroot embeddings directly fixes `reflectionPerm`. -/
theorem ext_of_coroot {P₁ P₂ : RootPairing ι R M N}
    (he : P₁.toLinearMap = P₂.toLinearMap) (hr : P₁.root = P₂.root)
    (hc : P₁.coroot = P₂.coroot) : P₁ = P₂ := by
  have hperm : P₁.reflectionPerm = P₂.reflectionPerm := by
    ext i j
    refine P₂.root.injective ?_
    rw [← hr, ← P₁.reflectionPerm_root, he, hr, hc, P₂.reflectionPerm_root]
  cases P₁
  cases P₂
  simp only at he hr hc hperm
  subst he hr hc hperm
  rfl

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

/-- **A root has infinite additive order** in characteristic zero: `n • α = 0` pairs with `α^∨`
to `2 n = 0`. -/
theorem not_isOfFinAddOrder_root [CharZero R] (P : RootPairing ι R M N) (i : ι) :
    ¬IsOfFinAddOrder (P.root i) := by
  rw [isOfFinAddOrder_iff_nsmul_eq_zero]
  rintro ⟨n, hn, hnα⟩
  have h := congrArg (P.coroot' i) hnα
  simp only [map_nsmul, root_coroot'_eq_pairing, pairing_same, map_zero, nsmul_eq_mul] at h
  have h' : ((n * 2 : ℕ) : R) = 0 := by exact_mod_cast h
  rw [Nat.cast_eq_zero] at h'
  omega

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

variable {P}

/-- Every root reflection fixes `P.corootKer` pointwise. -/
theorem reflection_apply_eq_self_of_mem_corootKer {x : M} (hx : x ∈ P.corootKer) (i : ι) :
    P.reflection i x = x := by
  rw [reflection_apply, mem_corootKer.mp hx i, zero_smul, sub_zero]

end CorootKer

end RootPairing
