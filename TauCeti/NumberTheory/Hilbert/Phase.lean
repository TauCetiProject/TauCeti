/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.DedekindDomain.Different

/-!
# Cyclotomic trace phases

Let `K` be a field of characteristic zero, `A` and `B` additive subgroups of `K` (that is,
`ℤ`-submodules) and `n` a natural number with `n • B ⊆ A`. For `x` in the trace dual
`Aᵛ = {x | Tr_{K/ℚ}(x a) ∈ ℤ for all a ∈ A}` and `ξ ∈ B`, the rational number
`n · Tr_{K/ℚ}(ξ x)` is an integer, since `n • ξ ∈ A`. This gives the `ℤ`-linear form
`traceExponent hAB x : B →ₗ[ℤ] ℤ`, and for an element `ζ` of a group the additive character

`tracePhase hAB x ζ : B →+ Additive G`, `ξ ↦ ζ ^ (n · Tr_{K/ℚ}(ξ x))`.

No generator of `B` is chosen. When `ζ ^ n = 1`, the character is unchanged when `x` changes by
an element of the trace dual `Bᵛ` (`tracePhase_eq_of_sub_mem`), since every exponent then changes
by a multiple of `n` (`dvd_traceExponent_sub`), but in general not when `x` changes by an element
of `Aᵛ`. The root of unity `ζ` need not be primitive, and the character is
natural in group homomorphisms (`tracePhase_map`), for instance in `Units.map` of a ring
homomorphism.

At a cusp of a Hilbert modular variety, with `K` a totally real field, `A = ab`, `B = ab′` for
fractional ideals `b ⊆ b′` and `n` the exponent of `b′/b`, these are the phases
`q^ξ ↦ ζ_n^{n · Tr(ξ x)} q^ξ` by which a change of the uniformization
`x ∈ (ab)^∨ / (ab′)^∨` acts on the monomials of the completed cusp chart.

## Main definitions

* `TauCeti.CyclotomicPhase.traceExponent`: the integer `n · Tr_{K/ℚ}(ξ x)`, as a `ℤ`-linear form
  in `ξ ∈ B`.
* `TauCeti.CyclotomicPhase.tracePhase`: the additive character `ξ ↦ ζ ^ (n · Tr_{K/ℚ}(ξ x))`.

## Main statements

* `TauCeti.CyclotomicPhase.dvd_traceExponent_sub`: if `x′ - x ∈ Bᵛ`, the two exponents at
  `ξ ∈ B` differ by a multiple of `n`.
* `TauCeti.CyclotomicPhase.tracePhase_eq_of_sub_mem`: if moreover `ζ ^ n = 1`, the two characters
  agree.

## References

* M. Dimitrov, *Compactifications arithmétiques des variétés de Hilbert et formes modulaires de
  Hilbert pour `Γ₁(c, n)`*, in *Geometric aspects of Dwork theory*, de Gruyter (2004),
  Proposition 4.1(ii) and equation (5).
-/

public section

open Algebra Submodule

namespace TauCeti.CyclotomicPhase

variable {K : Type*} [Field K] [Algebra ℚ K] {A B : Submodule ℤ K} {n : ℕ}

/-- The integer `n · Tr_{K/ℚ}(ξ x)`, as a `ℤ`-linear form in `ξ ∈ B`, for `x` in the trace dual
of `A` and `n • B ⊆ A`. It is characterized by `intCast_traceExponent`. It is the pairing of
Mathlib's `LinearMap.BilinForm.dualSubmoduleToDual` for the trace form, restricted along
multiplication by `n`. -/
noncomputable def traceExponent (hAB : ∀ ξ ∈ B, n • ξ ∈ A) (x : traceDual ℤ ℚ A) :
    B →ₗ[ℤ] ℤ :=
  ((traceForm ℚ K).dualSubmoduleToDual A ⟨x, (traceForm ℚ K).mem_dualSubmodule.mpr
    fun a ha ↦ mem_one.mpr (RingHom.mem_range.mp (mem_traceDual.mp x.property a ha))⟩).comp
    ((n • LinearMap.id).restrict hAB)

variable (hAB : ∀ ξ ∈ B, n • ξ ∈ A)

/-- The trace exponent is the integer `n · Tr_{K/ℚ}(ξ x)`. -/
@[simp]
theorem intCast_traceExponent (x : traceDual ℤ ℚ A) (ξ : B) :
    (traceExponent hAB x ξ : ℚ) = n * trace ℚ K (ξ * x) := by
  rw [traceExponent, LinearMap.comp_apply, LinearMap.BilinForm.dualSubmoduleToDual_apply_apply,
    ← eq_intCast (algebraMap ℤ ℚ), LinearMap.BilinForm.dualSubmodulePairing_spec]
  simp [traceForm_apply, mul_comm (x : K), ← nsmul_eq_mul]

/-- An integer is the trace exponent exactly when it equals `n · Tr_{K/ℚ}(ξ x)`. -/
theorem traceExponent_eq_iff (x : traceDual ℤ ℚ A) (ξ : B) (m : ℤ) :
    traceExponent hAB x ξ = m ↔ (m : ℚ) = n * trace ℚ K (ξ * x) := by
  rw [← intCast_traceExponent hAB, eq_comm, Int.cast_inj]

/-- Changing `x` by an element of the trace dual of `B` changes the trace exponent at every
`ξ ∈ B` by a multiple of `n`. The trace dual of `B`, not that of `A`, is the relevant one. -/
theorem dvd_traceExponent_sub {x x' : traceDual ℤ ℚ A} (h : (x' : K) - x ∈ traceDual ℤ ℚ B)
    (ξ : B) : (n : ℤ) ∣ traceExponent hAB x' ξ - traceExponent hAB x ξ := by
  obtain ⟨k, hk⟩ := mem_traceDual.mp h ξ ξ.property
  rw [algebraMap_int_eq, eq_intCast, traceForm_apply] at hk
  refine ⟨k, Int.cast_injective (α := ℚ) ?_⟩
  push_cast
  rw [intCast_traceExponent, intCast_traceExponent, hk]
  simp only [sub_mul, map_sub, mul_comm (ξ : K)]
  ring

variable {G : Type*} [Group G]

/-- The cyclotomic trace phase `ξ ↦ ζ ^ (n · Tr_{K/ℚ}(ξ x))`, an additive character of `B` with
values in `G`, for `x` in the trace dual of `A`, `n • B ⊆ A` and `ζ ∈ G`. When `ζ ^ n = 1` it
depends on `x` only modulo the trace dual of `B` (`tracePhase_eq_of_sub_mem`). -/
noncomputable def tracePhase (x : traceDual ℤ ℚ A) (ζ : G) : B →+ Additive G :=
  (zmultiplesHom (Additive G) (.ofMul ζ)).comp (traceExponent hAB x).toAddMonoidHom

/-- The trace phase at `ξ` is `ζ` raised to the trace exponent `n · Tr_{K/ℚ}(ξ x)`. -/
@[simp]
theorem toMul_tracePhase (x : traceDual ℤ ℚ A) (ζ : G) (ξ : B) :
    (tracePhase hAB x ζ ξ).toMul = ζ ^ traceExponent hAB x ξ := by
  simp [tracePhase]

/-- The trace phase at `ξ` is `ζ ^ m` for any integer `m` equal to `n · Tr_{K/ℚ}(ξ x)`. -/
theorem toMul_tracePhase_of_intCast_eq (x : traceDual ℤ ℚ A) (ζ : G) {ξ : B} {m : ℤ}
    (hm : (m : ℚ) = n * trace ℚ K (ξ * x)) : (tracePhase hAB x ζ ξ).toMul = ζ ^ m := by
  rw [toMul_tracePhase, (traceExponent_eq_iff hAB x ξ m).mpr hm]

/-- If `ζ ^ n = 1`, the trace phase depends on `x` only modulo the trace dual of `B`. -/
theorem tracePhase_eq_of_sub_mem {x x' : traceDual ℤ ℚ A} (h : (x' : K) - x ∈ traceDual ℤ ℚ B)
    {ζ : G} (hζ : ζ ^ n = 1) : tracePhase hAB x ζ = tracePhase hAB x' ζ := by
  ext ξ
  obtain ⟨k, hk⟩ := dvd_traceExponent_sub hAB h ξ
  simp [sub_eq_iff_eq_add'.mp hk, zpow_add, zpow_mul, hζ]

/-- The trivial root of unity gives the trivial character. -/
@[simp]
theorem tracePhase_one (x : traceDual ℤ ℚ A) : tracePhase hAB x (1 : G) = 0 := by
  ext ξ
  simp

/-- The trace phase is natural in group homomorphisms. -/
theorem tracePhase_map {H : Type*} [Group H] (f : G →* H) (x : traceDual ℤ ℚ A) (ζ : G) :
    tracePhase hAB x (f ζ) = (MonoidHom.toAdditive f).comp (tracePhase hAB x ζ) := by
  ext ξ
  simp [map_zpow]

/-- The phase sees `x` modulo the trace dual of `B`, not of `A`: for `K = ℚ`, `A = ℤ`, `B = ¼ℤ`,
`n = 4` and `ζ = -1`, a fourth root of unity, the elements `x = 0` and `x′ = 1` differ by an
element of the trace dual `ℤ` of `A`, but their phases at `¼` are `1` and `-1`. -/
example : ∃ (hAB : ∀ ξ ∈ span ℤ {(1 / 4 : ℚ)}, (4 : ℕ) • ξ ∈ span ℤ {(1 : ℚ)})
    (h1 : (1 : ℚ) ∈ traceDual ℤ ℚ (span ℤ {(1 : ℚ)})),
    tracePhase hAB 0 (-1 : ℚˣ) ≠ tracePhase hAB ⟨1, h1⟩ (-1 : ℚˣ) := by
  have hAB : ∀ ξ ∈ span ℤ {(1 / 4 : ℚ)}, (4 : ℕ) • ξ ∈ span ℤ {(1 : ℚ)} := by
    intro ξ hξ
    obtain ⟨k, rfl⟩ := mem_span_singleton.mp hξ
    exact mem_span_singleton.mpr ⟨k, by ring⟩
  have h1 : (1 : ℚ) ∈ traceDual ℤ ℚ (span ℤ {(1 : ℚ)}) := by
    refine mem_traceDual.mpr fun a ha ↦ ?_
    obtain ⟨k, rfl⟩ := mem_span_singleton.mp ha
    exact ⟨k, by simp [traceForm_apply]⟩
  refine ⟨hAB, h1, fun h ↦ ?_⟩
  have := congr(($h ⟨1 / 4, mem_span_singleton_self _⟩).toMul)
  rw [toMul_tracePhase_of_intCast_eq hAB _ _ (m := 0) (by simp),
    toMul_tracePhase_of_intCast_eq hAB _ _ (m := 1) (by simp), Units.ext_iff] at this
  norm_num at this

end TauCeti.CyclotomicPhase
