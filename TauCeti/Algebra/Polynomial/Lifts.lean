/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.Polynomial.HasseDeriv
public import Mathlib.Algebra.Polynomial.Lifts
public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.RingTheory.Ideal.Defs
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Lifting polynomials along ring maps

Let `f : A →+* B` be a ring map and `S` a set of automorphisms of `B` whose common fixed points
lie in the image of `f`. A polynomial over `B` whose coefficients are fixed by every member of
`S` then lifts along `f`. This is the coefficient step of Galois descent, stated without any
algebraicity or Galois hypothesis on `B` over `A`.

If a ring map `φ : D →+* O` is surjective modulo an ideal `I`, any monic polynomial over `O`
lifts to a monic polynomial over `D` of the same degree whose image agrees with it modulo `I`.

Integral lifts also control denominators of divided derivatives: if the rescaled translate
`P(x + L X)` of a rational polynomial lifts to `ℤ[X]`, then its coefficients
`L ^ m (1 / m!) P⁽ᵐ⁾(x)` are integers. Such integrality of rational numbers transfers to every
subring of a field of characteristic zero.

## Main results

* `Polynomial.mem_lifts_of_forall_map_eq`: a polynomial over `B` fixed by `Polynomial.map σ` for
  every `σ ∈ S` lifts along `f`.
* `Polynomial.exists_monic_map_sub_coeff_mem`: lifting a monic polynomial along a map surjective
  modulo an ideal while preserving the degree.
* `Polynomial.pow_mul_eval_hasseDeriv_mem_range_intCast_of_comp_mem_lifts`: if `P(x + L X)` has
  integral coefficients, then `L ^ m (1 / m!) P⁽ᵐ⁾(x)` is an integer.
* `Subring.pow_mul_eval_hasseDeriv_map_mem`: transfer a rational Hasse-derivative denominator
  bound to any subring of a characteristic-zero field, allowing a larger denominator exponent.
-/

public section

namespace Polynomial

variable {A B : Type*} [Semiring A] [Semiring B] {f : A →+* B}

/-- **Polynomials fixed by a set of automorphisms lift.** Let `S` be a set of automorphisms of
`B` whose common fixed points lie in the image of `f`. A polynomial over `B` fixed by
`Polynomial.map σ` for every `σ ∈ S` lifts along `f`. -/
theorem mem_lifts_of_forall_map_eq {S : Set (B ≃+* B)}
    (hS : ∀ c : B, (∀ σ ∈ S, σ c = c) → c ∈ Set.range f) {p : B[X]}
    (hp : ∀ σ ∈ S, p.map (σ : B →+* B) = p) : p ∈ lifts f :=
  (lifts_iff_coeff_lifts p).mpr fun n ↦ hS _ fun σ hσ ↦ by
    simpa using congr($(hp σ hσ).coeff n)

/-- **Lifting a monic polynomial modulo an ideal.** If `φ : D →+* O` is surjective modulo an
ideal `I`, then any monic `T : O[X]` lifts to a monic `ψ : D[X]` of the same `natDegree`
such that `ψ.map φ - T` has all coefficients in `I`. -/
theorem exists_monic_map_sub_coeff_mem {D O : Type*} [Semiring D] [CommRing O] (φ : D →+* O)
    {I : Ideal O} (hφ : ∀ o : O, ∃ d : D, o - φ d ∈ I)
    {T : O[X]} (hT : T.Monic) :
    ∃ ψ : D[X], ψ.Monic ∧ ψ.natDegree = T.natDegree ∧
      ∀ i, (ψ.map φ - T).coeff i ∈ I := by
  by_cases hI : I = ⊤
  · subst hI
    rcases subsingleton_or_nontrivial D with _ | _
    · have : Subsingleton O := RingHom.codomain_trivial φ
      exact ⟨1, monic_one, by simp [Subsingleton.elim T 0], fun _ ↦ Submodule.mem_top⟩
    · exact ⟨X ^ T.natDegree, monic_X_pow _, natDegree_X_pow _, fun _ ↦ Submodule.mem_top⟩
  let q := Ideal.Quotient.mk I
  have : Nontrivial (O ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI
  have hlifts : T.map q ∈ lifts (q.comp φ) := by
    rw [lifts_iff_coeff_lifts]
    intro i
    obtain ⟨d, hd⟩ := hφ (T.coeff i)
    refine ⟨d, ?_⟩
    rw [RingHom.comp_apply, coeff_map, eq_comm, Ideal.Quotient.mk_eq_mk_iff_sub_mem]
    exact hd
  obtain ⟨ψ, hψ_map, hψ_deg, hψ_monic⟩ := lifts_and_natDegree_eq_and_monic hlifts (hT.map q)
  refine ⟨ψ, hψ_monic, hψ_deg.trans (hT.natDegree_map q), fun i ↦ ?_⟩
  rw [coeff_sub, ← Ideal.Quotient.mk_eq_mk_iff_sub_mem, ← coeff_map, ← coeff_map, map_map]
  exact congrArg (fun p : (O ⧸ I)[X] ↦ p.coeff i) hψ_map

/-- **Denominators of divided derivatives from an integral rescaled translate.** If the
polynomial `P(x + L X)` has integral coefficients, then for every `m` the number
`L ^ m (1 / m!) (d / dX) ^ m P` at `x` is an integer: it is the coefficient of `X ^ m` in
`P(x + L X)`. -/
theorem pow_mul_eval_hasseDeriv_mem_range_intCast_of_comp_mem_lifts {P : ℚ[X]} {x L : ℚ}
    (hP : P.comp (C x + C L * X) ∈ lifts (Int.castRingHom ℚ)) (m : ℕ) :
    L ^ m * (hasseDeriv m P).eval x ∈ Set.range (Int.cast : ℤ → ℚ) := by
  have e : P.comp (C x + C L * X) = (taylor x P).comp (C L * X) := by
    simp [taylor_apply, comp_assoc, add_comm]
  rw [e, lifts_iff_coeff_lifts] at hP
  obtain ⟨z, hz⟩ := hP m
  rw [comp_C_mul_X_coeff, taylor_coeff, eq_intCast] at hz
  exact ⟨z, hz.trans (mul_comm _ _)⟩

end Polynomial

namespace Subring

variable {K : Type*} [Field K] [CharZero K] (A : Subring K)

/-- Transfer a rational Hasse-derivative denominator bound to a subring of a field of
characteristic zero. If `L ^ κ P^{[κ]}(t)` is an integer and `κ ≤ T`, then
`L ^ T (P.map (algebraMap ℚ K))^{[κ]}(t)` belongs to every subring of `K`. -/
theorem pow_mul_eval_hasseDeriv_map_mem {P : Polynomial ℚ} {L t : ℤ} {κ T : ℕ}
    (hP : (L : ℚ) ^ κ * (Polynomial.hasseDeriv κ P).eval (t : ℚ) ∈
      Set.range (Int.cast : ℤ → ℚ)) (hκ : κ ≤ T) :
    (L : K) ^ T * (Polynomial.hasseDeriv κ (P.map (algebraMap ℚ K))).eval (t : K) ∈ A := by
  obtain ⟨z, hz⟩ := hP
  have hz' : (L : K) ^ κ * algebraMap ℚ K
      ((Polynomial.hasseDeriv κ P).eval (t : ℚ)) = z := by
    rw [← map_intCast (algebraMap ℚ K) z, hz, map_mul, map_pow, map_intCast]
  rw [Polynomial.hasseDeriv_map, Polynomial.eval_map, ← map_intCast (algebraMap ℚ K) t,
    Polynomial.eval₂_at_apply, ← Nat.sub_add_cancel hκ, pow_add, mul_assoc, hz']
  exact mul_mem (pow_mem (intCast_mem A _) _) (intCast_mem A _)

end Subring
