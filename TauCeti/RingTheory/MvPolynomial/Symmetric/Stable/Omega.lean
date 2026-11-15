/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPolynomial.Symmetric.Complete.Elementary
public import TauCeti.RingTheory.MvPolynomial.Symmetric.Stable.Generators
import Mathlib.Tactic.LinearCombination
import TauCeti.RingTheory.MvPolynomial.Symmetric.Complete.PowerSum
import TauCeti.RingTheory.PowerSeries.Derivative

/-!
# The involution `ω` and the free generation of the symmetric functions by the `h_r`

The generating functions `H(t) = ∑ hₙ tⁿ` and `E(t) = ∑ eₙ tⁿ` of the complete homogeneous and
elementary symmetric functions satisfy `H(t) E(-t) = 1`, that is
`∑_{i + j = m} (-1)ʲ hᵢ eⱼ = 0` for `m > 0`. This relation is symmetric in `e` and `h`.

Since the `e_r` are free polynomial generators of the ring `Λ_R` of symmetric functions, there is a
unique algebra endomorphism `ω` of `Λ_R` sending each `e_r` to `h_r`. Applying `ω` to the relation
above and comparing with the relation itself shows by induction that `ω` also sends each `h_r` to
`e_r`. Hence `ω` is an involution, and in particular an algebra automorphism of `Λ_R`. It follows
that the complete homogeneous symmetric functions `h₁, h₂, …` are free polynomial generators of
`Λ_R` as well.

On the power sums, `ω(pₙ) = (-1)ⁿ⁺¹ pₙ` for `n ≥ 1`. Newton's identities for the `hₙ` say that
`t H'(t) = H(t) P(t)` for the generating function `P(t) = ∑_{n ≥ 1} pₙ tⁿ` of the power sums.
Applying `ω` turns this into `t E'(t) = E(t) ω(P)(t)`, while differentiating `H(t) E(-t) = 1` gives
`t E'(t) = -E(t) P(-t)`. Since `E(t)` is invertible, `ω(P)(t) = -P(-t)`. No division is needed, so
this holds over every commutative ring.

## Main definitions

* `TauCeti.SymmetricFunction.hsymmAlgHom R`: the algebra homomorphism `R[X₀, X₁, …] → Λ_R` sending
  `X r` to `h_(r + 1)`.
* `TauCeti.SymmetricFunction.omega R`: the involution `ω` of `Λ_R`, an algebra automorphism
  exchanging `e_r` and `h_r`.
* `TauCeti.SymmetricFunction.hsymmAlgEquiv R`: the free generation of `Λ_R` by the `h_r`, as an
  algebra equivalence.

## Main results

* `TauCeti.SymmetricFunction.sum_antidiagonal_of_stableHsymm_mul_neg_one_pow_mul_of_stableEsymm`:
  the relation `∑_{i + j = m} hᵢ (-1)ʲ eⱼ = δ_{m0}` in `Λ_R`.
* `TauCeti.SymmetricFunction.omega_of_stableEsymm`,
  `TauCeti.SymmetricFunction.omega_of_stableHsymm`: `ω(e_r) = h_r` and `ω(h_r) = e_r`.
* `TauCeti.SymmetricFunction.omega_omega`, `TauCeti.SymmetricFunction.omega_symm`: `ω² = id`.
* `TauCeti.SymmetricFunction.omega_of_stablePsum`: `ω(pₙ) = (-1)ⁿ⁺¹ pₙ` for `n ≠ 0`.
* `TauCeti.SymmetricFunction.hsymmAlgHom_injective`,
  `TauCeti.SymmetricFunction.hsymmAlgHom_surjective`: the `h_r` are algebraically independent
  generators of `Λ_R`.
* `TauCeti.SymmetricFunction.esymmAlgEquiv_trans_omega`,
  `TauCeti.SymmetricFunction.hsymmAlgEquiv_trans_omega`: `ω` carries the free generation by the
  `e_r` to the free generation by the `h_r`, and back.
* `TauCeti.SymmetricFunction.algHom_ext_of_stableHsymm`: algebra homomorphisms out of `Λ_R` agree
  once they agree on the `h_r`.

## References

* [I. G. Macdonald, *Symmetric Functions and Hall Polynomials*][macdonald1995], Chapter I,
  Section 2: the relation `H(t) E(-t) = 1`, the involution `ω` and the free generation of `Λ` by
  the `h_r`, and the action of `ω` on the power sums.
-/

public section

namespace TauCeti

open MvPolynomial DirectSum Finset

namespace SymmetricFunction

section CommSemiring

variable (R : Type*) [CommSemiring R]

/-- The algebra homomorphism from polynomials in countably many variables to the symmetric functions
sending the variable `X r` to the complete homogeneous symmetric function `h_(r + 1)`. -/
noncomputable def hsymmAlgHom : MvPolynomial ℕ R →ₐ[R] SymmetricFunction R :=
  aeval fun r => DirectSum.of _ (r + 1) (stableHsymm R (r + 1))

/-- The variable `X r` is sent to the complete homogeneous symmetric function `h_(r + 1)`. -/
@[simp]
theorem hsymmAlgHom_X (r : ℕ) :
    hsymmAlgHom R (X r) = DirectSum.of _ (r + 1) (stableHsymm R (r + 1)) :=
  aeval_X _ _

/-- In `d` variables, `TauCeti.SymmetricFunction.hsymmAlgHom` substitutes the complete homogeneous
symmetric polynomials. -/
theorem specialization_hsymmAlgHom (d : ℕ) (p : MvPolynomial ℕ R) :
    specialization R d (hsymmAlgHom R p) = aeval (fun r => hsymm (Fin d) R (r + 1)) p := by
  have h : (specialization R d).comp (hsymmAlgHom R) = aeval fun r => hsymm (Fin d) R (r + 1) :=
    MvPolynomial.algHom_ext fun r => by simp
  exact DFunLike.congr_fun h p

end CommSemiring

section CommRing

variable (R : Type*) [CommRing R]

/-- **The `h`–`e` relation** `H(t) E(-t) = 1` in the symmetric functions:
`∑_{i + j = m} hᵢ (-1)ʲ eⱼ = δ_{m0}`. -/
theorem sum_antidiagonal_of_stableHsymm_mul_neg_one_pow_mul_of_stableEsymm (m : ℕ) :
    ∑ p ∈ antidiagonal m, DirectSum.of _ p.1 (stableHsymm R p.1) *
        ((-1 : SymmetricFunction R) ^ p.2 * DirectSum.of _ p.2 (stableEsymm R p.2)) =
      if m = 0 then 1 else 0 := by
  refine ext_specialization fun d => ?_
  rw [map_sum, apply_ite (specialization R d), map_one, map_zero,
    ← sum_antidiagonal_hsymm_mul_neg_one_pow_mul_esymm (σ := Fin d) R m]
  simp

/-- The `h`–`e` relation with the roles of `e` and `h` exchanged:
`∑_{i + j = m} eᵢ (-1)ʲ hⱼ = δ_{m0}`. -/
theorem sum_antidiagonal_of_stableEsymm_mul_neg_one_pow_mul_of_stableHsymm (m : ℕ) :
    ∑ p ∈ antidiagonal m, DirectSum.of _ p.1 (stableEsymm R p.1) *
        ((-1 : SymmetricFunction R) ^ p.2 * DirectSum.of _ p.2 (stableHsymm R p.2)) =
      if m = 0 then 1 else 0 := by
  obtain rfl | hm := eq_or_ne m 0
  · simp
  have h := sum_antidiagonal_of_stableHsymm_mul_neg_one_pow_mul_of_stableEsymm R m
  simp only [hm, ↓reduceIte] at h ⊢
  rw [← Nat.sum_antidiagonal_swap, ← mul_zero ((-1 : SymmetricFunction R) ^ m), ← h,
    mul_sum]
  refine sum_congr rfl fun p hp => ?_
  rw [mem_antidiagonal] at hp
  subst hp
  have h2 : (-1 : SymmetricFunction R) ^ p.2 * (-1) ^ p.2 = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]
    simp
  rw [Prod.fst_swap, Prod.snd_swap, pow_add]
  linear_combination (-(-1 : SymmetricFunction R) ^ p.1 * DirectSum.of _ p.1 (stableHsymm R p.1) *
    DirectSum.of _ p.2 (stableEsymm R p.2)) * h2

/-- The algebra endomorphism of the symmetric functions sending `e_r` to `h_r`, before it is known
to be an involution. -/
private noncomputable def omegaAlgHom : SymmetricFunction R →ₐ[R] SymmetricFunction R :=
  (hsymmAlgHom R).comp (esymmAlgEquiv R).symm.toAlgHom

private theorem omegaAlgHom_of_stableEsymm (n : ℕ) :
    omegaAlgHom R (DirectSum.of _ n (stableEsymm R n)) = DirectSum.of _ n (stableHsymm R n) := by
  cases n with
  | zero => simp
  | succ r => simp [omegaAlgHom]

private theorem omegaAlgHom_of_stableHsymm (n : ℕ) :
    omegaAlgHom R (DirectSum.of _ n (stableHsymm R n)) = DirectSum.of _ n (stableEsymm R n) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  obtain _ | k := n
  · simp
  -- Apply `ω` to `∑ hᵢ (-1)ʲ eⱼ = 0` and compare with `∑ eᵢ (-1)ʲ hⱼ = 0`: the two sums agree
  -- term by term for `i ≤ k`, by induction, so their last terms `ω(h_(k + 1))` and `e_(k + 1)`
  -- agree.
  have h1 := congrArg (omegaAlgHom R)
    (sum_antidiagonal_of_stableHsymm_mul_neg_one_pow_mul_of_stableEsymm R (k + 1))
  have h2 := sum_antidiagonal_of_stableEsymm_mul_neg_one_pow_mul_of_stableHsymm R (k + 1)
  simp only [Nat.add_one_ne_zero, ↓reduceIte, map_zero, map_add, map_sum, map_mul, map_pow,
    map_neg, map_one, omegaAlgHom_of_stableEsymm, Nat.sum_antidiagonal_succ', pow_zero,
    stableEsymm_zero, stableHsymm_zero, of_stableSymmetricOne, mul_one] at h1 h2
  rw [← h2] at h1
  refine add_right_cancel (h1.trans ?_)
  congr 1
  refine sum_congr rfl fun p hp => ?_
  rw [mem_antidiagonal] at hp
  rw [ih p.1 (by omega)]

private theorem omegaAlgHom_comp_omegaAlgHom :
    (omegaAlgHom R).comp (omegaAlgHom R) = AlgHom.id R (SymmetricFunction R) :=
  algHom_ext fun r => by simp [omegaAlgHom_of_stableEsymm, omegaAlgHom_of_stableHsymm]

/-- **The involution `ω` of the symmetric functions**: the algebra automorphism of `Λ_R` sending
each elementary symmetric function `e_r` to the complete homogeneous symmetric function `h_r`
(`TauCeti.SymmetricFunction.omega_of_stableEsymm`). It is its own inverse
(`TauCeti.SymmetricFunction.omega_symm`), so it also sends `h_r` to `e_r`. -/
noncomputable def omega : SymmetricFunction R ≃ₐ[R] SymmetricFunction R :=
  AlgEquiv.ofAlgHom (omegaAlgHom R) (omegaAlgHom R) (omegaAlgHom_comp_omegaAlgHom R)
    (omegaAlgHom_comp_omegaAlgHom R)

/-- **`ω(e_r) = h_r`.** -/
@[simp]
theorem omega_of_stableEsymm (n : ℕ) :
    omega R (DirectSum.of _ n (stableEsymm R n)) = DirectSum.of _ n (stableHsymm R n) :=
  omegaAlgHom_of_stableEsymm R n

/-- **`ω(h_r) = e_r`.** -/
@[simp]
theorem omega_of_stableHsymm (n : ℕ) :
    omega R (DirectSum.of _ n (stableHsymm R n)) = DirectSum.of _ n (stableEsymm R n) :=
  omegaAlgHom_of_stableHsymm R n

/-- **`ω` is an involution.** -/
@[simp]
theorem omega_omega (x : SymmetricFunction R) : omega R (omega R x) = x :=
  DFunLike.congr_fun (omegaAlgHom_comp_omegaAlgHom R) x

/-- `ω` is its own inverse. -/
@[simp]
theorem omega_symm : (omega R).symm = omega R :=
  AlgEquiv.ext fun x => (AlgEquiv.symm_apply_eq _).mpr (omega_omega R x).symm

/-- `ω ∘ ω = id`, as algebra equivalences. -/
@[simp]
theorem omega_trans_omega : (omega R).trans (omega R) = AlgEquiv.refl :=
  AlgEquiv.ext (omega_omega R)

/-- `ω ∘ ω = id`, as algebra homomorphisms. -/
@[simp]
theorem omega_comp_omega :
    (omega R : SymmetricFunction R →ₐ[R] SymmetricFunction R).comp (omega R) =
      AlgHom.id R (SymmetricFunction R) :=
  AlgHom.ext (omega_omega R)

/-- `ω` turns a polynomial in the elementary symmetric functions into the same polynomial in the
complete homogeneous symmetric functions. -/
@[simp]
theorem omega_esymmAlgHom (p : MvPolynomial ℕ R) : omega R (esymmAlgHom R p) = hsymmAlgHom R p := by
  have h : (omega R).toAlgHom.comp (esymmAlgHom R) = hsymmAlgHom R :=
    MvPolynomial.algHom_ext fun r => by simp
  exact DFunLike.congr_fun h p

/-- `ω` turns a polynomial in the complete homogeneous symmetric functions into the same polynomial
in the elementary symmetric functions. -/
@[simp]
theorem omega_hsymmAlgHom (p : MvPolynomial ℕ R) : omega R (hsymmAlgHom R p) = esymmAlgHom R p := by
  rw [← omega_esymmAlgHom, omega_omega]

/-- **The complete homogeneous symmetric functions are algebraically independent.** -/
theorem hsymmAlgHom_injective : Function.Injective (hsymmAlgHom R) := by
  intro p q h
  rw [← omega_esymmAlgHom, ← omega_esymmAlgHom] at h
  exact esymmAlgHom_injective R ((omega R).injective h)

/-- **The complete homogeneous symmetric functions generate the symmetric functions.** -/
theorem hsymmAlgHom_surjective : Function.Surjective (hsymmAlgHom R) := by
  intro x
  obtain ⟨p, hp⟩ := esymmAlgHom_surjective R (omega R x)
  exact ⟨p, by rw [← omega_esymmAlgHom, hp, omega_omega]⟩

/-- **The free generation of the symmetric functions by the `h_r`**: the ring of symmetric
functions over a commutative ring `R` is the polynomial ring over `R` on the complete homogeneous
symmetric functions `h₁, h₂, …`, the variable `X r` representing `h_(r + 1)`. -/
noncomputable def hsymmAlgEquiv : MvPolynomial ℕ R ≃ₐ[R] SymmetricFunction R :=
  AlgEquiv.ofBijective (hsymmAlgHom R) ⟨hsymmAlgHom_injective R, hsymmAlgHom_surjective R⟩

/-- The free generation by the `h_r` is `TauCeti.SymmetricFunction.hsymmAlgHom`. -/
@[simp]
theorem hsymmAlgEquiv_apply (p : MvPolynomial ℕ R) : hsymmAlgEquiv R p = hsymmAlgHom R p :=
  (rfl)

/-- The complete homogeneous symmetric function `h_(r + 1)` corresponds to the variable `X r`. -/
@[simp]
theorem hsymmAlgEquiv_symm_of_stableHsymm (r : ℕ) :
    (hsymmAlgEquiv R).symm (DirectSum.of _ (r + 1) (stableHsymm R (r + 1))) = X r := by
  rw [AlgEquiv.symm_apply_eq, hsymmAlgEquiv_apply, hsymmAlgHom_X]

/-- Every symmetric function is the polynomial in the `h_r` that
`(TauCeti.SymmetricFunction.hsymmAlgEquiv R).symm` assigns to it. -/
@[simp]
theorem hsymmAlgHom_hsymmAlgEquiv_symm (x : SymmetricFunction R) :
    hsymmAlgHom R ((hsymmAlgEquiv R).symm x) = x :=
  (hsymmAlgEquiv R).apply_symm_apply x

/-- A polynomial in the `h_r` is recovered from the symmetric function it defines. -/
@[simp]
theorem hsymmAlgEquiv_symm_hsymmAlgHom (p : MvPolynomial ℕ R) :
    (hsymmAlgEquiv R).symm (hsymmAlgHom R p) = p :=
  (hsymmAlgEquiv R).symm_apply_apply p

/-- The free generation by the `h_r` is the free generation by the `e_r` followed by `ω`. -/
theorem esymmAlgEquiv_trans_omega : (esymmAlgEquiv R).trans (omega R) = hsymmAlgEquiv R :=
  AlgEquiv.ext fun p => by
    rw [AlgEquiv.trans_apply, esymmAlgEquiv_apply, hsymmAlgEquiv_apply, omega_esymmAlgHom]

/-- The free generation by the `e_r` is the free generation by the `h_r` followed by `ω`. -/
theorem hsymmAlgEquiv_trans_omega : (hsymmAlgEquiv R).trans (omega R) = esymmAlgEquiv R :=
  AlgEquiv.ext fun p => by
    rw [AlgEquiv.trans_apply, esymmAlgEquiv_apply, hsymmAlgEquiv_apply, omega_hsymmAlgHom]

variable {R} in
/-- **Algebra homomorphisms out of the symmetric functions are determined by their values on the
complete homogeneous symmetric functions** `h₁, h₂, …`. -/
theorem algHom_ext_of_stableHsymm {A : Type*} [Semiring A] [Algebra R A]
    {f g : SymmetricFunction R →ₐ[R] A}
    (h : ∀ n, f (DirectSum.of _ (n + 1) (stableHsymm R (n + 1))) =
      g (DirectSum.of _ (n + 1) (stableHsymm R (n + 1)))) : f = g := by
  have hfg : f.comp (hsymmAlgEquiv R).toAlgHom = g.comp (hsymmAlgEquiv R).toAlgHom :=
    MvPolynomial.algHom_ext fun r => by simpa using h r
  refine AlgHom.ext fun x => ?_
  obtain ⟨p, rfl⟩ := (hsymmAlgEquiv R).surjective x
  exact DFunLike.congr_fun hfg p

/-! ### `ω` on the power sums -/

open scoped PowerSeries

/-- The generating function `H(t) = ∑ hₙ tⁿ` of the complete homogeneous symmetric functions. -/
private noncomputable def hsymmSeries : (SymmetricFunction R)⟦X⟧ :=
  PowerSeries.mk fun n => DirectSum.of _ n (stableHsymm R n)

/-- The generating function `E(t) = ∑ eₙ tⁿ` of the elementary symmetric functions. -/
private noncomputable def esymmSeries : (SymmetricFunction R)⟦X⟧ :=
  PowerSeries.mk fun n => DirectSum.of _ n (stableEsymm R n)

/-- The generating function `P(t) = ∑_{n ≥ 1} pₙ tⁿ` of the power sum symmetric functions. -/
private noncomputable def psumSeries : (SymmetricFunction R)⟦X⟧ :=
  PowerSeries.mk fun n => if hn : n = 0 then 0 else DirectSum.of _ n (stablePsum R hn)

/-- `H(t) E(-t) = 1`. -/
private theorem hsymmSeries_mul_rescale_esymmSeries :
    hsymmSeries R * PowerSeries.rescale (-1) (esymmSeries R) = 1 := by
  ext m
  rw [PowerSeries.coeff_mul, PowerSeries.coeff_one,
    ← sum_antidiagonal_of_stableHsymm_mul_neg_one_pow_mul_of_stableEsymm R m]
  simp [hsymmSeries, esymmSeries, PowerSeries.coeff_rescale]

/-- `t H'(t) = H(t) P(t)`, read off from finitely many variables. -/
private theorem X_mul_derivative_hsymmSeries :
    PowerSeries.X * d⁄dX (hsymmSeries R) = hsymmSeries R * psumSeries R := by
  refine PowerSeries.ext fun n => ext_specialization (R := R) fun d => ?_
  let φ : SymmetricFunction R →+* MvPolynomial (Fin d) R := specialization R d
  have hH : PowerSeries.map φ (hsymmSeries R) = PowerSeries.mk fun n => hsymm (Fin d) R n := by
    ext k
    simp [φ, hsymmSeries]
  have hP : PowerSeries.map φ (psumSeries R) =
      PowerSeries.mk fun n => if n = 0 then 0 else psum (Fin d) R n := by
    ext k
    by_cases hk : k = 0 <;> simp [φ, psumSeries, hk]
  have h := congrArg (PowerSeries.coeff n) (X_mul_derivative_mk_hsymm (Fin d) R)
  rw [← hH, ← hP, ← PowerSeries.map_X φ, PowerSeries.derivative_map, ← map_mul, ← map_mul,
    PowerSeries.coeff_map, PowerSeries.coeff_map] at h
  exact h

/-- `ω` sends the power sum `p_n` to `(-1)^(n + 1) p_n`, in generating-function form. -/
private theorem map_omega_psumSeries :
    PowerSeries.map (omega R : SymmetricFunction R →+* SymmetricFunction R) (psumSeries R) =
      -PowerSeries.rescale (-1) (psumSeries R) := by
  set ω : SymmetricFunction R →+* SymmetricFunction R := ↑(omega R)
  set H := hsymmSeries R
  set E := esymmSeries R
  set P := psumSeries R
  set Θ : (SymmetricFunction R)⟦X⟧ → (SymmetricFunction R)⟦X⟧ := fun f => PowerSeries.X * d⁄dX f
  have hHE : H * PowerSeries.rescale (-1) E = 1 := hsymmSeries_mul_rescale_esymmSeries R
  have hΘH : Θ H = H * P := X_mul_derivative_hsymmSeries R
  -- `ω` turns `H` into `E`, so `t E'(t) = E(t) ω(P)(t)`.
  have hωH : PowerSeries.map ω H = E := by
    ext k
    simp [ω, H, E, hsymmSeries, esymmSeries]
  have hΘE : Θ E = E * PowerSeries.map ω P := by
    have h := congrArg (PowerSeries.map ω) hΘH
    rwa [map_mul, map_mul, PowerSeries.map_X, ← PowerSeries.derivative_map, hωH] at h
  -- Differentiating `H(t) E(-t) = 1` gives `t (E(-t))' = -P(t) E(-t)`.
  have hΘE' : Θ (PowerSeries.rescale (-1) E) = -(P * PowerSeries.rescale (-1) E) := by
    have h := congrArg Θ hHE
    simp only [Θ, Derivation.leibniz, Derivation.map_one_eq_zero, smul_eq_mul, mul_zero] at h
    simp only [Θ] at hΘH ⊢
    linear_combination PowerSeries.rescale (-1) E * h -
      (PowerSeries.X * d⁄dX (PowerSeries.rescale (-1) E) + P * PowerSeries.rescale (-1) E) * hHE -
      PowerSeries.rescale (-1) E ^ 2 * hΘH
  -- Rescaling back, `t E'(t) = -P(-t) E(t)`; cancel `E(t)`, whose inverse is `H(-t)`.
  have hΘE'' : Θ E = -(PowerSeries.rescale (-1) P * E) := by
    have h := congrArg (PowerSeries.rescale (-1)) hΘE'
    simp only [Θ, map_mul, map_neg, PowerSeries.rescale_X, PowerSeries.derivative_rescale,
      PowerSeries.rescale_rescale, neg_one_mul, neg_neg,
      PowerSeries.rescale_one, RingHom.id_apply, map_one] at h ⊢
    linear_combination h
  have hinv : PowerSeries.rescale (-1) H * E = 1 := by
    have h := congrArg (PowerSeries.rescale (-1)) hHE
    rwa [map_mul, PowerSeries.rescale_rescale, neg_one_mul, neg_neg, PowerSeries.rescale_one,
      RingHom.id_apply, map_one] at h
  linear_combination -PowerSeries.rescale (-1) H * (hΘE''.symm.trans hΘE) -
    (PowerSeries.map ω P + PowerSeries.rescale (-1) P) * hinv

/-- **`ω(p_n) = (-1)^(n + 1) p_n`**, for `n ≠ 0`. -/
@[simp]
theorem omega_of_stablePsum {n : ℕ} (hn : n ≠ 0) :
    omega R (DirectSum.of _ n (stablePsum R hn)) =
      (-1) ^ (n + 1) * DirectSum.of _ n (stablePsum R hn) := by
  have h := congrArg (PowerSeries.coeff n) (map_omega_psumSeries R)
  simp only [PowerSeries.coeff_map, map_neg, PowerSeries.coeff_rescale, psumSeries,
    PowerSeries.coeff_mk, hn, ↓reduceDIte] at h
  rw [RingHom.coe_coe] at h
  rw [h, pow_succ]
  ring

end CommRing

end SymmetricFunction

end TauCeti
