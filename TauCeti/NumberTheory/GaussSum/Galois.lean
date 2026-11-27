/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.GaussSum
public import Mathlib.RingTheory.Adjoin.Basic
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.NumberTheory.JacobiSum.Basic
import Mathlib.NumberTheory.MulChar.Lemmas
import TauCeti.NumberTheory.GaussSum.Basic
import TauCeti.NumberTheory.LegendreSymbol.AddCharacter
import TauCeti.NumberTheory.MulChar.GaloisOrbit
import TauCeti.RingTheory.RootsOfUnity.Adjoin

/-!
# The field of definition of a Gauss sum and the Galois action on it

Let `χ` be a multiplicative and `ψ` an additive character of a finite commutative ring `R`, with
values in a domain `R'`, such that `χ ^ m = 1` and `ψ ^ n = 1`, and let `μ` and `ζ` be primitive
`m`-th and `n`-th roots of unity in `R'`. Every value of `χ` is `0` or a power of `μ`, and every
value of `ψ` is a power of `ζ`, so the Gauss sum `g(χ, ψ)` lies in `ℤ[μ, ζ]`. Over a finite field
`F` of characteristic `p`, with `ψ` primitive and `m` the order of `χ`, this is `ℤ[ζ_m, ζ_p]`, the
ring of integers of `ℚ(ζ_{mp})` when `R' = ℂ`.

A ring endomorphism `σ` of `R'` with `σ μ = μ ^ t` and `σ ζ = ζ ^ c` acts on the values by
`σ ∘ χ = χ ^ t` and `σ ∘ ψ = ψ ^ c` (`MulChar.ringHomComp_eq_pow`,
`MonoidHom.compAddChar_eq_pow`), and `ψ ^ c` is the shift `x ↦ ψ (c x)`. So if `c` is a unit of
`R`, then `σ (g(χ, ψ)) = (χ ^ t)⁻¹ (c) g(χ ^ t, ψ)`; this needs only the action on the two
characters, for values in any commutative ring. The two special cases are the automorphism
`σ_c` that fixes `μ`, which multiplies `g(χ, ψ)` by `χ⁻¹ (c)`, and the automorphism `τ_t` that
fixes `ζ`, which sends `g(χ, ψ)` to `g(χ ^ t, ψ)`.

Over a finite field, Mathlib's `gaussSum_pow_eq_prod_jacobiSum` writes `g(χ, ψ) ^ m` for a
primitive `ψ` and `m = orderOf χ ≥ 2` as `χ (-1) #F` times a product of Jacobi sums, all of which
lie in `ℤ[μ]`. So `g(χ, ψ) ^ m ∈ ℤ[μ]` whenever `χ ^ m = 1`, and in particular every `σ_c`
fixes `g(χ, ψ) ^ m`.

## Main results

* `TauCeti.gaussSum_mem_algebraAdjoin`: `g(χ, ψ) ∈ ℤ[μ, ζ]`.
* `TauCeti.map_gaussSum_of_ringHomComp_eq_pow`: `σ (g(χ, ψ)) = (χ ^ t)⁻¹ (c) g(χ ^ t, ψ)` if
  `σ ∘ χ = χ ^ t`, `σ ∘ ψ = ψ ^ c` and `c` is a unit of `R`, with values in any commutative ring.
* `TauCeti.map_gaussSum_of_apply_eq_pow`: the same if `σ μ = μ ^ t` and `σ ζ = ζ ^ c`.
* `TauCeti.map_gaussSum_eq_inv_apply_mul`: `σ_c (g(χ, ψ)) = χ⁻¹ (c) g(χ, ψ)` if `σ` fixes `μ`.
* `TauCeti.map_gaussSum_eq_gaussSum_pow`: `τ_t (g(χ, ψ)) = g(χ ^ t, ψ)` if `σ` fixes `ζ`.
* `TauCeti.gaussSum_pow_mem_algebraAdjoin`: over a finite field, `g(χ, ψ) ^ m ∈ ℤ[μ]`.

## References

* K. Ireland and M. Rosen, *A Classical Introduction to Modern Number Theory*, 2nd ed.,
  Chapters 8 and 14.
-/

public section

namespace TauCeti

section FiniteRing

variable {R R' : Type*} [CommRing R] [Fintype R] [CommRing R']

/-- **The Galois action on a Gauss sum.** If a ring endomorphism `σ` of the values sends `χ` to
`χ ^ t` and `ψ` to `ψ ^ c`, and `c` is a unit, then `σ (g(χ, ψ)) = (χ ^ t)⁻¹ (c) g(χ ^ t, ψ)`. -/
theorem map_gaussSum_of_ringHomComp_eq_pow {χ : MulChar R R'} {ψ : AddChar R R'}
    {σ : R' →+* R'} {t c : ℕ} (hχ : χ.ringHomComp σ = χ ^ t)
    (hψ : σ.toMonoidHom.compAddChar ψ = ψ ^ c) (hc : IsUnit (c : R)) :
    σ (gaussSum χ ψ) = (χ ^ t)⁻¹ c * gaussSum (χ ^ t) ψ := by
  rw [← MulChar.gaussSum_ringHomComp, hχ, hψ, AddChar.pow_mulShift, ← hc.unit_spec,
    gaussSum_mulShift_eq]

variable [IsDomain R']

/-- **The field of definition of a Gauss sum.** If `χ ^ m = 1` and `ψ ^ n = 1`, and `μ` and `ζ`
are primitive `m`-th and `n`-th roots of unity, then `g(χ, ψ) ∈ ℤ[μ, ζ]`. -/
theorem gaussSum_mem_algebraAdjoin {χ : MulChar R R'} {ψ : AddChar R R'} {m n : ℕ} [NeZero m]
    [NeZero n] (hχ : χ ^ m = 1) (hψ : ψ ^ n = 1) {μ ζ : R'} (hμ : IsPrimitiveRoot μ m)
    (hζ : IsPrimitiveRoot ζ n) : gaussSum χ ψ ∈ Algebra.adjoin ℤ {μ, ζ} := by
  refine Subalgebra.sum_mem _ fun x _ ↦ Subalgebra.mul_mem _ ?_ ?_
  · by_cases hx : IsUnit x
    · refine Algebra.adjoin_mono (Set.singleton_subset_iff.mpr (Set.mem_insert μ {ζ})) ?_
      refine hμ.mem_algebraAdjoin_of_pow_eq_one ?_
      rw [← hx.unit_spec, ← MulChar.pow_apply_coe, hχ, MulChar.one_apply_coe]
    · rw [χ.map_nonunit hx]
      exact Subalgebra.zero_mem _
  · refine Algebra.adjoin_mono (Set.subset_insert μ {ζ}) ?_
    refine hζ.mem_algebraAdjoin_of_pow_eq_one ?_
    rw [← pow_apply, hψ, one_apply]

/-- **The Galois action on a Gauss sum, read on roots of unity.** Let `χ ^ m = 1` and
`ψ ^ n = 1`, and let `μ` and `ζ` be primitive `m`-th and `n`-th roots of unity. If a ring
endomorphism `σ` sends `μ` to `μ ^ t` and `ζ` to `ζ ^ c`, and `c` is a unit, then
`σ (g(χ, ψ)) = (χ ^ t)⁻¹ (c) g(χ ^ t, ψ)`. -/
theorem map_gaussSum_of_apply_eq_pow {χ : MulChar R R'} {ψ : AddChar R R'} {m n : ℕ} [NeZero m]
    [NeZero n] (hχ : χ ^ m = 1) (hψ : ψ ^ n = 1) {μ ζ : R'} (hμ : IsPrimitiveRoot μ m)
    (hζ : IsPrimitiveRoot ζ n) {σ : R' →+* R'} {t c : ℕ} (hσμ : σ μ = μ ^ t)
    (hσζ : σ ζ = ζ ^ c) (hc : IsUnit (c : R)) :
    σ (gaussSum χ ψ) = (χ ^ t)⁻¹ c * gaussSum (χ ^ t) ψ :=
  map_gaussSum_of_ringHomComp_eq_pow (MulChar.ringHomComp_eq_pow hχ hμ hσμ)
    (MonoidHom.compAddChar_eq_pow hψ hζ (σ := σ.toMonoidHom) hσζ) hc

/-- **The automorphism `σ_c`.** If `σ` fixes the primitive `m`-th root of unity `μ`, with
`χ ^ m = 1`, and sends `ζ` to `ζ ^ c` for a unit `c`, then `σ (g(χ, ψ)) = χ⁻¹ (c) g(χ, ψ)`. -/
theorem map_gaussSum_eq_inv_apply_mul {χ : MulChar R R'} {ψ : AddChar R R'} {m n : ℕ} [NeZero m]
    [NeZero n] (hχ : χ ^ m = 1) (hψ : ψ ^ n = 1) {μ ζ : R'} (hμ : IsPrimitiveRoot μ m)
    (hζ : IsPrimitiveRoot ζ n) {σ : R' →+* R'} {c : ℕ} (hσμ : σ μ = μ) (hσζ : σ ζ = ζ ^ c)
    (hc : IsUnit (c : R)) : σ (gaussSum χ ψ) = χ⁻¹ c * gaussSum χ ψ := by
  simpa using map_gaussSum_of_apply_eq_pow hχ hψ hμ hζ (t := 1) (by rw [hσμ, pow_one]) hσζ hc

/-- **The automorphism `τ_t`.** If `σ` sends the primitive `m`-th root of unity `μ` to `μ ^ t`,
with `χ ^ m = 1`, and fixes `ζ`, then `σ (g(χ, ψ)) = g(χ ^ t, ψ)`. -/
theorem map_gaussSum_eq_gaussSum_pow {χ : MulChar R R'} {ψ : AddChar R R'} {m n : ℕ} [NeZero m]
    [NeZero n] (hχ : χ ^ m = 1) (hψ : ψ ^ n = 1) {μ ζ : R'} (hμ : IsPrimitiveRoot μ m)
    (hζ : IsPrimitiveRoot ζ n) {σ : R' →+* R'} {t : ℕ} (hσμ : σ μ = μ ^ t) (hσζ : σ ζ = ζ) :
    σ (gaussSum χ ψ) = gaussSum (χ ^ t) ψ := by
  simpa using map_gaussSum_of_apply_eq_pow hχ hψ hμ hζ (c := 1) hσμ (by rw [hσζ, pow_one])
    (by simp)

end FiniteRing

/-- **The `m`-th power of a Gauss sum.** Over a finite field, if `χ ^ m = 1` and `μ` is a
primitive `m`-th root of unity, then `g(χ, ψ) ^ m ∈ ℤ[μ]`. -/
theorem gaussSum_pow_mem_algebraAdjoin {F R : Type*} [Field F] [Fintype F] [CommRing R]
    [IsDomain R] {χ : MulChar F R} (ψ : AddChar F R) {m : ℕ} [NeZero m] (hχ : χ ^ m = 1) {μ : R}
    (hμ : IsPrimitiveRoot μ m) : gaussSum χ ψ ^ m ∈ Algebra.adjoin ℤ {μ} := by
  -- Reduce to `m = orderOf χ`, with the primitive root `ν = μ ^ a` for `m = orderOf χ * a`.
  obtain ⟨a, ha⟩ := orderOf_dvd_of_pow_eq_one hχ
  have hν : IsPrimitiveRoot (μ ^ a) (orderOf χ) := hμ.pow (NeZero.pos m) (by rw [ha, mul_comm])
  have hle : Algebra.adjoin ℤ {μ ^ a} ≤ Algebra.adjoin ℤ {μ} := Algebra.adjoin_le <|
    Set.singleton_subset_iff.mpr (Subalgebra.pow_mem _ (Algebra.self_mem_adjoin_singleton ℤ μ) a)
  rw [ha, pow_mul]
  refine Subalgebra.pow_mem _ (hle ?_) a
  have : NeZero (orderOf χ) := ⟨χ.orderOf_pos.ne'⟩
  rcases eq_or_ne ψ 1 with rfl | hψ
  · refine Subalgebra.pow_mem _ (Subalgebra.sum_mem _ fun x _ ↦ ?_) _
    rw [one_apply, mul_one]
    exact MulChar.apply_mem_algebraAdjoin hν x
  rcases (Nat.one_le_iff_ne_zero.mpr (NeZero.ne (orderOf χ))).eq_or_lt with h | h
  · -- For `χ = 1` the Gauss sum is `-1`.
    rw [← h, pow_one, orderOf_eq_one_iff.mp h.symm, gaussSum_one_left hψ]
    exact Subalgebra.neg_mem _ (Subalgebra.one_mem _)
  · rw [gaussSum_pow_eq_prod_jacobiSum h (AddChar.IsPrimitive.of_ne_one hψ)]
    refine Subalgebra.mul_mem _ (Subalgebra.mul_mem _ (MulChar.apply_mem_algebraAdjoin hν _)
      (Subalgebra.natCast_mem _ _)) (Subalgebra.prod_mem _ fun i _ ↦ ?_)
    refine jacobiSum_mem_algebraAdjoin_of_pow_eq_one (pow_orderOf_eq_one χ) ?_ hν
    rw [← pow_mul, mul_comm, pow_mul, pow_orderOf_eq_one, one_pow]

end TauCeti
