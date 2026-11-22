/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.RingTheory.Ideal.Colon

/-!
# Colon ideals and quotient annihilators

For an `R`-algebra `S`, the ideal `(N : x)` of a submodule `N` of an `S`-module commutes with
restricting scalars to `R`.

For an ideal `I` and an element `f` of a commutative ring, `I ∩ (f) = f · (I : f)`. When `f` is
regular this determines `(I : f)`: generators of `I ∩ (f)`, which an intersection computation
supplies, divided by `f` generate `(I : f)`.

The colon conditions `r I ⊆ J` compose under multiplication of the scalars, and a power
`x ^ (j - i)` of an element of `I` carries `I ^ i` into `I ^ j`. These conditions say when
multiplication by a scalar induces a map between the quotients `M ⧸ I M` and `M ⧸ J M`.

## Main results

* `Submodule.le_annihilator_quotient_iff`: an ideal annihilates a quotient exactly when its
  multiples of the ambient module lie in the submodule.
* `Submodule.comap_colon_singleton`: the ideal `(N : x)` of `R` is the preimage of the ideal
  `(N : x)` of `S`.
* `Ideal.inf_span_singleton_eq_span_singleton_mul_colon`: `I ∩ (f) = f · (I : f)`.
* `Ideal.colon_singleton_eq_of_inf_span_singleton_eq`: for regular `f`, if `I ∩ (f) = f · J`
  then `(I : f) = J`.
* `Ideal.span_singleton_mul_colon_singleton`: a regular principal factor cancels from colon.
* `Ideal.exists_eq_span_pow_mul_colon_not_le`: an ideal not contained in every power of `(f)` is
  `(f ^ k) · (I : f ^ k)` with `(I : f ^ k)` not contained in `(f)`.
* `Ideal.le_colon_singleton_mul`: the conditions `r I ⊆ J` and `s J ⊆ K` give `(s r) I ⊆ K`.
* `Ideal.pow_le_colon_singleton_pow`: for `x ∈ I` and `i ≤ j`, `x ^ (j - i) I ^ i ⊆ I ^ j`.

## References

* D. Cox, J. Little, D. O'Shea, *Ideals, Varieties, and Algorithms*, Chapter 4, §4,
  computing ideal quotients from intersections.
-/

public section

open scoped Pointwise

/-- An ideal annihilates a quotient exactly when its multiples of the ambient module lie in
the submodule being quotiented out. -/
theorem Submodule.le_annihilator_quotient_iff {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    {I : Ideal R} {N : Submodule R M} :
    I ≤ Module.annihilator R (M ⧸ N) ↔ I • (⊤ : Submodule R M) ≤ N := by
  rw [Submodule.annihilator_quotient, Submodule.smul_le]
  simp only [IsConcreteLE.le_iff, Submodule.mem_colon, Submodule.mem_top, Set.mem_univ,
    forall_true_left]

variable {R S M : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S] [AddCommMonoid M]
  [Module R M] [Module S M] [IsScalarTower R S M]

/-- For a submodule `N` of an `S`-module `M` and `x ∈ M`, the ideal `(N : x)` of `R` is the
preimage of the ideal `(N : x)` of `S`. -/
theorem Submodule.comap_colon_singleton (N : Submodule S M) (x : M) :
    (N.colon {x}).comap (algebraMap R S) = (N.restrictScalars R).colon {x} := by
  ext r
  simp [Submodule.mem_colon_singleton]

namespace Ideal

variable {R : Type*} [CommSemiring R] {I J : Ideal R} {f : R}

/-- An ideal is contained in a colon ideal exactly when its product with the denominator
is contained in the numerator. -/
theorem le_colon_iff {I J K : Ideal R} : I ≤ J.colon (K : Set R) ↔ I * K ≤ J := by
  constructor
  · intro h
    exact Ideal.mul_le.mpr fun a ha b hb ↦ Submodule.mem_colon.mp (h ha) b hb
  · intro h a ha
    exact Submodule.mem_colon.mpr fun b hb ↦ h (Ideal.mul_mem_mul ha hb)

/-- The intersection of an ideal `I` with the principal ideal `(f)` is `f` times the colon ideal
`(I : f)`. -/
theorem inf_span_singleton_eq_span_singleton_mul_colon (I : Ideal R) (f : R) :
    I ⊓ span {f} = span {f} * I.colon {f} := by
  ext x
  simp only [mem_inf, mem_span_singleton_mul, mem_span_singleton', Submodule.mem_colon_singleton,
    smul_eq_mul]
  constructor
  · rintro ⟨hx, a, rfl⟩
    exact ⟨a, hx, mul_comm f a⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨mul_comm f a ▸ ha, a, mul_comm a f⟩

/-- **Colon ideals from intersections.** If `f` is regular and `I ∩ (f) = f · J`, then the colon
ideal `(I : f)` is `J`. -/
theorem colon_singleton_eq_of_inf_span_singleton_eq (hf : IsLeftRegular f)
    (h : I ⊓ span {f} = span {f} * J) : I.colon {f} = J := by
  rw [inf_span_singleton_eq_span_singleton_mul_colon, span_singleton_mul_eq_span_singleton_mul]
    at h
  refine le_antisymm (fun x hx ↦ ?_) fun y hy ↦ ?_
  · obtain ⟨y, hy, hxy⟩ := h.1 x hx
    exact hf hxy ▸ hy
  · obtain ⟨x, hx, hxy⟩ := h.2 y hy
    exact hf hxy ▸ hx

/-- A regular principal factor cancels from the corresponding colon ideal. -/
theorem span_singleton_mul_colon_singleton (hf : IsLeftRegular f) (J : Ideal R) :
    (span {f} * J).colon {f} = J :=
  colon_singleton_eq_of_inf_span_singleton_eq hf (inf_eq_left.mpr mul_le_left)

/-- Dividing a principal product by its regular first factor leaves the second factor. -/
theorem span_mul_colon_singleton (hf : IsLeftRegular f) (g : R) :
    (span {f * g}).colon {f} = span {g} := by
  rw [← span_singleton_mul_span_singleton]
  exact span_singleton_mul_colon_singleton hf _

/-- **Extracting a power of a principal ideal.** If an ideal `I` does not lie in every power of
`(f)`, then `I = (f ^ k) · (I : f ^ k)` for some `k`, where the colon ideal `(I : f ^ k)` does not
lie in `(f)`. -/
theorem exists_eq_span_pow_mul_colon_not_le (h : ∃ n, ¬ I ≤ span {f ^ n}) :
    ∃ k, I = span {f ^ k} * I.colon {f ^ k} ∧ ¬ I.colon {f ^ k} ≤ span {f} := by
  classical
  have h' : ∃ k, ¬ I ≤ span {f ^ (k + 1)} := by
    obtain ⟨n, hn⟩ := h
    exact ⟨n, fun hle ↦ hn (hle.trans
      (span_singleton_le_span_singleton.2 (pow_dvd_pow f n.le_succ)))⟩
  have hIk : I ≤ span {f ^ Nat.find h'} := by
    rcases hk : Nat.find h' with _ | j
    · simp
    · exact not_not.1 (Nat.find_min h' (by omega))
  refine ⟨Nat.find h', ?_, fun hle ↦ Nat.find_spec h' fun x hx ↦ ?_⟩
  · rw [← inf_span_singleton_eq_span_singleton_mul_colon, inf_eq_left.2 hIk]
  · obtain ⟨a, rfl⟩ := mem_span_singleton'.1 (hIk hx)
    obtain ⟨d, rfl⟩ := mem_span_singleton'.1 (hle (Submodule.mem_colon_singleton.2 hx))
    exact mem_span_singleton'.2 ⟨d, by ring⟩

/-- Colon conditions compose: if `r I ⊆ J` and `s J ⊆ K`, then `(s r) I ⊆ K`. -/
theorem le_colon_singleton_mul {I J K : Ideal R} {r s : R} (hIJ : I ≤ J.colon {r})
    (hJK : J ≤ K.colon {s}) : I ≤ K.colon {s * r} := fun a ha ↦ by
  have h : a * r * s ∈ K := by simpa using hJK (by simpa using hIJ ha : a * r ∈ J)
  simpa [mul_comm s r, ← mul_assoc] using h

/-- For `x ∈ I` and `i ≤ j`, multiplication by `x ^ (j - i)` carries `I ^ i` into `I ^ j`. -/
theorem pow_le_colon_singleton_pow {x : R} (hx : x ∈ I) {i j : ℕ} (hij : i ≤ j) :
    I ^ i ≤ (I ^ j).colon {x ^ (j - i)} := fun a ha ↦ by
  rw [Submodule.mem_colon_singleton, smul_eq_mul, mul_comm, ← Nat.sub_add_cancel hij, pow_add,
    Nat.add_sub_cancel]
  exact mul_mem_mul (pow_mem_pow hx _) ha

end Ideal
