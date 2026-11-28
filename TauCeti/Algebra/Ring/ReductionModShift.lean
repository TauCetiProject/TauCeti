/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Data.ZMod.ValMinAbs
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Tactic.Ring

/-!
# Reductions modulo `m / k` and shift-invariant maps on `ZMod.valMinAbs`

A ring homomorphism `σ : R →+* S` is a reduction modulo `m / k` (`TauCeti.IsReductionMod σ m k`)
when it kills every `x : R` satisfying `k • x = m • y` for some `y : R`. Over an `O`-algebra `R`
without `k`-torsion, any `μ ∈ O` with `k * μ = m` yields such a reduction `R →+* R ⧸ (μ)` whose
kernel is `μ • R`.

We also prove two congruence principles for additive maps on integer weights:
* If `(m : S) = 0`, an additive map `B : (ι → ℤ) →+ R` composed with `σ` depends only on the
  weights modulo `m`.
* If `σ` is a reduction modulo `m / (2 * k)` and `C : (ZMod m → ℤ) →+ R` kills every shift
  difference `f (· - k) - f`, then `σ (C ZMod.valMinAbs) = 0`.

## Main definitions and results

* `TauCeti.IsReductionMod`: predicate that `σ : R →+* S` kills every `x` with `k • x ∈ m • R`.
* `TauCeti.IsReductionMod.natCast_eq_zero`: `IsReductionMod σ m k` implies `(m : S) = 0`.
* `TauCeti.exists_isReductionMod`: existence of a reduction modulo `m / k` with kernel `μ • R`.
* `TauCeti.map_eq_of_weights_modEq`: weights congruent modulo `m` have equal image under `σ ∘ B`.
* `TauCeti.map_valMinAbs_eq_zero_of_shift`: shift-invariant additive maps kill `ZMod.valMinAbs`
  after a reduction modulo `m / (2 * k)`.

## Provenance

Adapted from `grh-lean` (`https://github.com/lsernau/grh-lean`, commit
`72fead102f663d5c7a407964a13dc0cf9d977207`), file
`src/New/Congruences/FirstOrder/OnePrime.lean` (`New.Patching.IsReductionMod`,
`New.Patching.IsReductionMod.natCast_eq_zero`, `New.Patching.exists_isReductionMod`,
`New.Patching.map_eq_of_weights_modEq`, `New.Patching.map_valMinAbs_eq_zero_of_shift`).
-/

public section

namespace TauCeti

universe u

section ReductionMod

variable {R S : Type*} [Ring R] [Ring S] {σ : R →+* S} {m k : ℕ}

/-- A ring homomorphism `σ : R →+* S` is a reduction modulo `m / k` if it kills every `x : R`
satisfying `k • x = m • y` for some `y : R`. -/
def IsReductionMod (σ : R →+* S) (m k : ℕ) : Prop :=
  ∀ x y : R, k • x = m • y → σ x = 0

/-- A reduction modulo `m / k` sends `m` to `0`. -/
theorem IsReductionMod.natCast_eq_zero (hσ : IsReductionMod σ m k) : (m : S) = 0 := by
  rw [← map_natCast σ]
  exact hσ m k (by rw [nsmul_eq_mul, nsmul_eq_mul, Nat.cast_comm])

/-- Let `R` be an `O`-algebra with no `k`-torsion, and let `μ ∈ O` satisfy `k * μ = m`. There is a
ring homomorphism `σ : R →+* S` that is a reduction modulo `m / k` and whose kernel consists of
multiples of `μ`. -/
theorem exists_isReductionMod {O : Type*} {R : Type u} [CommRing O] [Ring R] [Algebra O R]
    {m k : ℕ} {μ : O} (hμ : (k : O) * μ = (m : O)) (hk : IsSMulRegular R k) :
    ∃ (S : Type u) (_ : Ring S) (σ : R →+* S),
      IsReductionMod σ m k ∧ ∀ a b : R, σ a = σ b → ∃ y : R, a - b = μ • y := by
  let I : Ideal R := Ideal.span {algebraMap O R μ}
  have mem_I (x : R) : x ∈ I ↔ ∃ y : R, x = μ • y := by
    simp only [I, Ideal.mem_span_singleton', ← Algebra.commutes, ← Algebra.smul_def, eq_comm]
  have : I.IsTwoSided := ⟨fun {x} y hx ↦ by
    obtain ⟨x', rfl⟩ : ∃ x' : R, x = μ • x' := (mem_I x).mp hx
    exact (mem_I _).mpr ⟨x' * y, smul_mul_assoc μ x' y⟩⟩
  refine ⟨R ⧸ I, inferInstance, Ideal.Quotient.mk I, fun x y hxy ↦ ?_,
    fun a b hab ↦ (mem_I _).mp (Ideal.Quotient.eq.mp hab)⟩
  have k_smul : k • x = k • μ • y := by
    rw [hxy, ← Nat.cast_smul_eq_nsmul O m, ← Nat.cast_smul_eq_nsmul O k, smul_smul, hμ]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr ((mem_I x).mpr ⟨y, hk k_smul⟩)

end ReductionMod

section ShiftVanishing

variable {R S : Type*} [Ring R] [Ring S]

/-- If `(m : S) = 0`, then an additive map `B : (ι → ℤ) →+ R` composed with `σ : R →+* S` takes
weights that are congruent modulo `m` to the same element of `S`. -/
theorem map_eq_of_weights_modEq {m : ℕ} {σ : R →+* S} (hm : (m : S) = 0) {ι : Type*}
    (B : (ι → ℤ) →+ R) (f g : ι → ℤ) (h_congr : ∀ x : ι, (g x : ZMod m) = f x) :
    σ (B f) = σ (B g) := by
  choose d hd using fun x ↦ (ZMod.intCast_eq_intCast_iff_dvd_sub (g x) (f x) m).mp (h_congr x)
  have h_sub : f = m • d + g := funext fun x ↦ by simp [← hd x]
  rw [h_sub, map_add, map_add, map_nsmul, map_nsmul, nsmul_eq_mul, hm, zero_mul, zero_add]

/-- Let `σ : R →+* S` be a reduction modulo `m / (2 * k)`. If an additive map
`C : (ZMod m → ℤ) →+ R` kills every shift difference `f (· - k) - f`, then `σ` kills
`C ZMod.valMinAbs`. -/
theorem map_valMinAbs_eq_zero_of_shift {m k : ℕ} {σ : R →+* S}
    (hσ : IsReductionMod σ m (2 * k)) (C : (ZMod m → ℤ) →+ R)
    (hC : ∀ f : ZMod m → ℤ, C ((fun x : ZMod m ↦ f (x - k)) - f) = 0) :
    σ (C ZMod.valMinAbs) = 0 := by
  let f (x : ZMod m) : ℤ := ZMod.valMinAbs x * (ZMod.valMinAbs x + k)
  have f_dvd (x : ZMod m) : ∃ d : ℤ, f (x - k) - f x + 2 * k * ZMod.valMinAbs x = m * d :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ m).mp (by push_cast [f, ZMod.coe_valMinAbs]; ring)
  choose d hd using f_dvd
  have f_diff : (fun x ↦ f (x - k)) - f + (2 * k) • ZMod.valMinAbs = m • d :=
    funext fun x ↦ by simpa using hd x
  refine hσ (C ZMod.valMinAbs) (C d) ?_
  rw [← map_nsmul, ← map_nsmul, ← f_diff, map_add, hC, zero_add]

end ShiftVanishing

end TauCeti
