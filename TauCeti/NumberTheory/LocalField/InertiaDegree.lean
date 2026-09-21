/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.RamificationInertia.Basic
public import TauCeti.NumberTheory.LocalField.IntegerRing
public import TauCeti.NumberTheory.LocalField.RamificationIndex

/-!
# The residue degree of an extension of local fields, and `e · f = [L : K]`

Let `L/K` be an extension of nonarchimedean local fields whose valuations are compatible, in the
sense of `ValuativeExtension K L`. This file defines the residue degree

`TauCeti.inertiaDegree K L : ℕ`

as the degree of `𝓀[L]` over `𝓀[K]`, the second of the two invariants attached to such an
extension, and proves the fundamental identity `e · f = [L : K]` relating them to the degree.

The identity is Mathlib's `Ideal.sum_ramification_inertia_eq_finrank` for `𝒪[L]` over `𝒪[K]`,
read through three facts: `𝓂[L]` is the only prime of `𝒪[L]` above `𝓂[K]`, by
`IsLocalRing.primesOver_eq`, so the sum has a single term; `𝒪[L]` is a finite free `𝒪[K]`-module
of rank `[L : K]`, by `TauCeti.finrank_integerRing`; and the two intrinsic invariants of `L/K`
are the ideal-theoretic invariants of `𝓂[L]` over `𝒪[K]`. Those comparisons,
`ramificationIndex_eq_ramificationIdx` and `inertiaDegree_eq_inertiaDeg`, are stated separately:
they are what lets Dedekind-level results about `𝒪[K] ⊆ 𝒪[L]` be used on the valuation-theoretic
side, and conversely.

## Main definitions

* `TauCeti.inertiaDegree`: the residue degree `f(L/K)` of an extension of nonarchimedean local
  fields.

## Main results

* `TauCeti.primesOver_maximalIdeal_eq_singleton`: `𝓂[L]` is the unique prime of `𝒪[L]`
  above `𝓂[K]`.
* `TauCeti.inertiaDegree_eq_inertiaDeg`: the intrinsic residue degree agrees with
  `Ideal.inertiaDeg` of `𝓂[L]` over `𝒪[K]`.
* `TauCeti.ramificationIndex_mul_inertiaDegree`: the fundamental identity `e · f = [L : K]`.
* `TauCeti.inertiaDegree_tower`: multiplicativity `f(M/K) = f(L/K) · f(M/L)` in a tower.
* `TauCeti.natCard_residueField`: `#𝓀[L] = #𝓀[K] ^ f(L/K)`.

## References

* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter I, §4.
* J. Neukirch, *Algebraic Number Theory*, Chapter II, §6.
-/

public section
noncomputable section

open ValuativeRel IsLocalRing

namespace TauCeti

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L]

variable (K L) in
/-- The residue degree `f(L/K)` of an extension of nonarchimedean local fields with compatible
valuations: the degree of the residue field of `L` over the residue field of `K`. -/
def inertiaDegree : ℕ := Module.finrank 𝓀[K] 𝓀[L]

variable (K L) in
/-- The defining formula of `inertiaDegree`: the degree of the residue extension. -/
theorem inertiaDegree_def : inertiaDegree K L = Module.finrank 𝓀[K] 𝓀[L] := (rfl)

/-- The residue degree is positive. -/
theorem inertiaDegree_pos : 0 < inertiaDegree K L := Module.finrank_pos

variable (K L) in
/-- **The characteristic property of the residue degree**: the residue field of `L` has
`#𝓀[K] ^ f(L/K)` elements. The residue fields of nonarchimedean local fields are finite, so both
cardinalities here are genuine. -/
theorem natCard_residueField : Nat.card 𝓀[L] = Nat.card 𝓀[K] ^ inertiaDegree K L :=
  Module.natCard_eq_pow_finrank

variable (K L) in
/-- **The residue degree is the ideal-theoretic inertia degree** of `𝓂[L]` over `𝒪[K]`. -/
theorem inertiaDegree_eq_inertiaDeg :
    inertiaDegree K L = 𝓂[L].inertiaDeg 𝒪[K] :=
  (Ideal.inertiaDeg_eq_of_isMaximal 𝓂[K] 𝓂[L]).symm

variable (K L) in
/-- The maximal ideal of `𝒪[L]` is the unique prime above the maximal ideal of `𝒪[K]`. -/
theorem primesOver_maximalIdeal_eq_singleton : Ideal.primesOver 𝓂[K] 𝒪[L] = {𝓂[L]} :=
  IsLocalRing.primesOver_eq 𝒪[L] (IsDiscreteValuationRing.not_a_field 𝒪[K])

variable (K L) in
/-- **The fundamental identity** `e(L/K) · f(L/K) = [L : K]` for an extension of nonarchimedean
local fields with compatible valuations. -/
theorem ramificationIndex_mul_inertiaDegree :
    ramificationIndex K L * inertiaDegree K L = Module.finrank K L := by
  have hs := primesOver_maximalIdeal_eq_singleton K L
  have hmem : 𝓂[L] ∈ Ideal.primesOver 𝓂[K] 𝒪[L] := by rw [hs]; exact Set.mem_singleton _
  -- The sum below is indexed by the primes above `𝓂[K]`, a singleton; any `Fintype` will do.
  let : Fintype ↥(Ideal.primesOver 𝓂[K] 𝒪[L]) := by rw [hs]; infer_instance
  rw [ramificationIndex_eq_ramificationIdx, inertiaDegree_eq_inertiaDeg, ← finrank_integerRing K L,
    ← Ideal.sum_ramification_inertia_eq_finrank 𝓂[K] 𝒪[L]]
  symm
  refine Fintype.sum_eq_single (⟨𝓂[L], hmem⟩ : ↥(Ideal.primesOver 𝓂[K] 𝒪[L])) fun q hq ↦ ?_
  exact absurd (Subtype.ext (by simpa [hs] using q.2)) hq

variable (K L) in
/-- **Multiplicativity of the residue degree in a tower** `M/L/K`: `f(M/K) = f(L/K) · f(M/L)`.

The compatibility of `M` over `K` is a hypothesis rather than a consequence of the two steps
because `f(M/K)` is the degree of the residue extension `𝓀[M] / 𝓀[K]`, which that compatibility
is what produces. -/
theorem inertiaDegree_tower (M : Type*) [Field M] [ValuativeRel M] [TopologicalSpace M]
    [IsNonarchimedeanLocalField M] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
    [ValuativeExtension L M] [ValuativeExtension K M] :
    inertiaDegree K M = inertiaDegree K L * inertiaDegree L M := by
  have := finite_of_valuativeExtension K L
  have := finite_of_valuativeExtension L M
  have key : ramificationIndex K M * inertiaDegree K M =
      ramificationIndex K M * (inertiaDegree K L * inertiaDegree L M) :=
    calc ramificationIndex K M * inertiaDegree K M
        = Module.finrank K L * Module.finrank L M := by
          rw [ramificationIndex_mul_inertiaDegree, Module.finrank_mul_finrank]
      _ = ramificationIndex K L * inertiaDegree K L *
            (ramificationIndex L M * inertiaDegree L M) := by
          rw [ramificationIndex_mul_inertiaDegree, ramificationIndex_mul_inertiaDegree]
      _ = ramificationIndex K M * (inertiaDegree K L * inertiaDegree L M) := by
          rw [ramificationIndex_tower (K := K) (L := L) M]; ring
  exact Nat.eq_of_mul_eq_mul_left ramificationIndex_pos key

end TauCeti
