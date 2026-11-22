/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharP.Frobenius
public import TauCeti.RingTheory.RingHom.Free
public import TauCeti.RingTheory.SplitAlgebra.Basic

import TauCeti.LinearAlgebra.Dual.Divisibility

/-!
# Hochster's endomorphism criterion for splitting

Let `(R, 𝔪)` be a local ring and `σ : R →+* R` an endomorphism over which `R` is free
(`RingHom.Free σ`), and let `S` be an `R`-algebra with a ring endomorphism `τ` restricting to `σ`
on `R`. If some `R`-linear functional `λ : S → R` has `λ 1 ∉ σʲ(𝔪) R` for some `j`, then `S` is
split over `R`: writing `λ 1` in a basis of `R` over `σʲ`, one coordinate is a unit, and the
corresponding coordinate functional `μ`, which is linear along `σʲ`, gives the retraction
`μ ∘ λ ∘ τʲ`.

Hochster's criterion makes this applicable to every nonzero functional. Suppose that `r ∈ R` is
`0` or a nonzerodivisor with `⋂ₙ rⁿ R = 0` and that `⋂ⱼ σʲ(𝔪) R ⊆ r R`. If every functional
took its value at `1` in `r R`, then, since `λ s` is the value at `1` of `λ ∘ (s * ·)`, every
value of every functional would lie in `r R`; dividing by `r` repeatedly, it would lie in
`⋂ₙ rⁿ R = 0`. So a nonzero functional yields one whose value at `1` lies outside `r R`, hence
outside some `σʲ(𝔪) R`, and `S` is split over `R` as soon as `Hom_R(S, R) ≠ 0`. With `r = 0`
and `σ` the Frobenius this is the splitting criterion behind the direct summand theorem in
characteristic `p`.

No injectivity is asked of `τ` or of the structure map `R → S`; the latter is injective once `S`
is split.

## Main results

* `TauCeti.SplitAlgebra.of_map_one_notMem_map_maximalIdeal`: a functional `λ` with
  `λ 1 ∉ σ(𝔪) R`, for `σ` free and compatible with an endomorphism of `S`, gives a splitting.
* `TauCeti.exists_linearMap_map_one_notMem_span_singleton`: if `r` is `0` or a nonzerodivisor
  with `⋂ₙ rⁿ R = 0`, every algebra with a nonzero functional to `R` has a functional whose value
  at `1` lies outside `r R`.
* `TauCeti.SplitAlgebra.of_ne_zero_of_endomorphism`: Hochster's endomorphism criterion.
* `TauCeti.SplitAlgebra.of_ne_zero_of_frobenius`: the case `r = 0`, `σ` the Frobenius of a local
  ring of characteristic `p` that is free over its Frobenius and has `⋂ⱼ 𝔪^[pʲ] R = 0`.

## References

* M. Hochster, *Contracted ideals from integral extensions of regular rings*, Nagoya Math. J. 51
  (1973), §1, Theorem 2.
* Y. André, *La conjecture du facteur direct*, Publ. Math. IHÉS 127 (2018), Annexe A.3,
  Proposition A.3.1, implication (c) ⇒ (b).
-/

public section

open IsLocalRing

namespace TauCeti

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- Let `(R, 𝔪)` be a local ring that is free over an endomorphism `φ`, and let `τ` be an
endomorphism of the `R`-algebra `S` restricting to `φ` on `R`. If an `R`-linear functional
`l : S → R` has `l 1 ∉ φ(𝔪) R`, then `S` is split over `R`. -/
theorem SplitAlgebra.of_map_one_notMem_map_maximalIdeal [IsLocalRing R] {φ : R →+* R}
    (hφ : φ.Free) {τ : S →+* S} (hτ : ∀ a, τ (algebraMap R S a) = algebraMap R S (φ a))
    {l : S →ₗ[R] R} (hl : l 1 ∉ (maximalIdeal R).map φ) : SplitAlgebra R S := by
  obtain ⟨μ, hμ, hμ1⟩ := hφ.exists_addMonoidHom_eq_one hl
  refine .of_map_one { toFun s := μ (l (τ s)), map_add' := by simp, map_smul' := fun a s ↦ ?_ } ?_
  · rw [RingHom.id_apply, smul_eq_mul, Algebra.smul_def, map_mul, hτ, ← Algebra.smul_def,
      map_smul, smul_eq_mul, hμ]
  · simpa using hμ1

/-- Let `r ∈ R` be `0` or a nonzerodivisor with `⋂ₙ rⁿ R = 0`. If an `R`-algebra `S` has a
nonzero `R`-linear functional `l : S → R`, then some `R`-linear functional takes at `1` a value
outside `r R`. -/
theorem exists_linearMap_map_one_notMem_span_singleton {r : R}
    (hr : ⨅ n, Ideal.span {r} ^ n = ⊥) (hr' : r = 0 ∨ IsSMulRegular R r) {l : S →ₗ[R] R}
    (hl : l ≠ 0) : ∃ l' : S →ₗ[R] R, l' 1 ∉ Ideal.span {r} := by
  by_contra! h
  -- Every value `l' s = (l' ∘ (s * ·)) 1` lies in `r R`.
  have h' (l' : S →ₗ[R] R) (s : S) : l' s ∈ Ideal.span {r} := by
    simpa using h (l' ∘ₗ LinearMap.mulLeft R s)
  refine hl (LinearMap.ext fun s ↦ ?_)
  rcases hr' with rfl | hr'
  · simpa using h' l s
  -- Dividing by `r` repeatedly, every value of every functional lies in every `rⁿ R`.
  have hpow (n : ℕ) : ∀ (l' : S →ₗ[R] R) (s : S), l' s ∈ Ideal.span {r} ^ n := by
    induction n with
    | zero => simp
    | succ n ih =>
      intro l' s
      obtain ⟨μ, rfl⟩ := LinearMap.exists_smul_eq_of_forall_dvd hr'.isLeftRegular
        fun x ↦ Ideal.mem_span_singleton.1 (h' l' x)
      rw [pow_succ', LinearMap.smul_apply, smul_eq_mul]
      exact Ideal.mul_mem_mul (Ideal.mem_span_singleton_self r) (ih μ s)
  simpa [← Ideal.mem_bot, ← hr] using fun n ↦ hpow n l s

/-- **Hochster's endomorphism criterion.** Let `(R, 𝔪)` be a local ring and `σ` an endomorphism
over which `R` is free, and let `r ∈ R` be `0` or a nonzerodivisor with `⋂ₙ rⁿ R = 0` and
`⋂ⱼ σʲ(𝔪) R ⊆ r R`. Let `S` be an `R`-algebra with an endomorphism `τ` restricting to `σ` on `R`.
If some `R`-linear functional `S → R` is nonzero, then `S` is split over `R`. -/
theorem SplitAlgebra.of_ne_zero_of_endomorphism [IsLocalRing R] {r : R}
    (hr : ⨅ n, Ideal.span {r} ^ n = ⊥) (hr' : r = 0 ∨ IsSMulRegular R r) {σ : R →+* R}
    (hσ : σ.Free) (hσr : ⨅ j, (maximalIdeal R).map (σ ^ j) ≤ Ideal.span {r}) {τ : S →+* S}
    (hτ : ∀ a, τ (algebraMap R S a) = algebraMap R S (σ a)) {l : S →ₗ[R] R} (hl : l ≠ 0) :
    SplitAlgebra R S := by
  obtain ⟨l', hl'⟩ := exists_linearMap_map_one_notMem_span_singleton hr hr' hl
  obtain ⟨j, hj⟩ : ∃ j, l' 1 ∉ (maximalIdeal R).map (σ ^ j) := by
    by_contra! h
    exact hl' (hσr (Ideal.mem_iInf.2 h))
  refine of_map_one_notMem_map_maximalIdeal (hσ.pow j) (τ := τ ^ j) (fun a ↦ ?_) hj
  have hsemi : Function.Semiconj (algebraMap R S) σ τ := fun a ↦ (hτ a).symm
  simpa [RingHom.coe_pow] using (hsemi.iterate_right j a).symm

/-- **Hochster's criterion in characteristic `p`.** Let `(R, 𝔪)` be a local ring of exponential
characteristic `p` that is free over its Frobenius, with `⋂ⱼ 𝔪^[pʲ] R = 0`, where `𝔪^[pʲ]` is
generated by the `pʲ`-th powers of elements of `𝔪`. Then every `R`-algebra `S` of exponential
characteristic `p` with a nonzero `R`-linear functional `S → R` is split over `R`. -/
theorem SplitAlgebra.of_ne_zero_of_frobenius [IsLocalRing R] (p : ℕ) [ExpChar R p]
    [ExpChar S p] (hR : (frobenius R p).Free)
    (hm : ⨅ j, (maximalIdeal R).map (iterateFrobenius R p j) = ⊥) {l : S →ₗ[R] R}
    (hl : l ≠ 0) : SplitAlgebra R S :=
  of_ne_zero_of_endomorphism (r := 0) (le_bot_iff.1 (iInf_le_of_le 1 (by simp))) (.inl rfl) hR
    (by simpa [iterateFrobenius_eq_pow] using hm.le) (τ := frobenius S p)
    (fun a ↦ ((algebraMap R S).map_frobenius p a).symm) hl

end TauCeti
