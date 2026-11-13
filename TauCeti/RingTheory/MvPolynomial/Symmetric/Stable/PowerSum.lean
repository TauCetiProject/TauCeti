/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPolynomial.Symmetric.PowerSum.Elementary
public import TauCeti.RingTheory.MvPolynomial.Symmetric.Stable.Generators
import TauCeti.Algebra.DirectSum.Internal
import TauCeti.RingTheory.GradedAlgebra.DirectSum
import TauCeti.RingTheory.MvPolynomial.WeightedHomogeneous

/-!
# The rational power-sum presentation of the symmetric functions

Newton's identities `(n + 1) e_(n + 1) = ∑_{i + j = n} (-1)ʲ eᵢ p_(j + 1)` hold in the ring `Λ_R`
of symmetric functions over every commutative ring, since they hold in every finite alphabet.
When `R` is a `ℚ`-algebra they can be solved for `e_(n + 1)`, so the power sums `p₁, p₂, …`
generate `Λ_R`; comparing with the free generation by the elementary symmetric functions shows that
they are algebraically independent as well. Over `ℤ` this fails: `p₁² - p₂ = 2 e₂`, and `e₂` is not
a polynomial in the power sums.

The inverse of the presentation is described by the polynomials
`TauCeti.SymmetricFunction.esymmPsumPoly R n`, written `E_n`, in the variables `X r`, which stand
for `p_(r + 1)`: they are determined by `E₀ = 1` and Newton's recursion, and specialise in every
finite alphabet to Newton's expression of `e_n` through the power sums.

## Main definitions

* `TauCeti.SymmetricFunction.psumAlgHom R`: the algebra homomorphism `R[X₀, X₁, …] → Λ_R` sending
  `X r` to `p_(r + 1)`.
* `TauCeti.SymmetricFunction.psumAlgEquiv R`: for a `ℚ`-algebra `R`, the power-sum presentation
  `R[X₀, X₁, …] ≃ₐ[R] Λ_R`.

## Main results

* `TauCeti.SymmetricFunction.mul_of_stableEsymm_eq_sum`: **Newton's identities** in `Λ_R`.
* `TauCeti.SymmetricFunction.psumAlgHom_esymmPsumPoly`: `E_n` evaluated at the power sums is `e_n`.
* `TauCeti.SymmetricFunction.psumAlgHom_injective`,
  `TauCeti.SymmetricFunction.psumAlgHom_surjective`: over a `ℚ`-algebra, the power sums are
  algebraically independent and generate `Λ_R`.
* `TauCeti.SymmetricFunction.psumAlgEquiv_symm_of_stableEsymm`,
  `TauCeti.SymmetricFunction.psumAlgEquiv_symm_of_stablePsum`: the inverse of the presentation
  sends `e_n` to `E_n` and `p_n` to `X (n - 1)`.
* `TauCeti.SymmetricFunction.algHom_ext_of_stablePsum`: over a `ℚ`-algebra, algebra homomorphisms
  out of `Λ_R` agree once they agree on the power sums.
* `TauCeti.SymmetricFunction.psumAlgHom_weightedHomogeneousComponent`,
  `TauCeti.SymmetricFunction.isWeightedHomogeneous_psumAlgEquiv_symm_of`: the presentation
  identifies the weighted grading `deg X_r = r + 1` with the grading of `Λ_R`.

## References

* [I. G. Macdonald, *Symmetric Functions and Hall Polynomials*][macdonald1995], Chapter I,
  Section 2: Newton's identities (2.11′), the power sums as free generators of `Λ_ℚ` (2.12), and
  the expression of `e_n` through the power sums (2.14′).
-/

public section

namespace TauCeti

open MvPolynomial Finset

namespace SymmetricFunction

section CommSemiring

variable (R : Type*) [CommSemiring R]

/-- The algebra homomorphism from polynomials in countably many variables to the symmetric functions
sending the variable `X r` to the power sum `p_(r + 1)`. There is no stable `p₀`, so the variables
are shifted by one. -/
noncomputable def psumAlgHom : MvPolynomial ℕ R →ₐ[R] SymmetricFunction R :=
  aeval fun r => DirectSum.of _ (r + 1) (stablePsum R r.succ_ne_zero)

/-- The variable `X r` is sent to the power sum `p_(r + 1)`. -/
@[simp]
theorem psumAlgHom_X (r : ℕ) :
    psumAlgHom R (X r) = DirectSum.of _ (r + 1) (stablePsum R r.succ_ne_zero) :=
  aeval_X _ _

/-- In `d` variables, `TauCeti.SymmetricFunction.psumAlgHom` substitutes the power sums
`p₁, p₂, …`. -/
theorem specialization_psumAlgHom (d : ℕ) (p : MvPolynomial ℕ R) :
    specialization R d (psumAlgHom R p) = aeval (fun r => psum (Fin d) R (r + 1)) p := by
  have h : (specialization R d).comp (psumAlgHom R) = aeval fun r => psum (Fin d) R (r + 1) :=
    MvPolynomial.algHom_ext fun r => by simp
  exact DFunLike.congr_fun h p

/-- **The power-sum homomorphism is graded**: it sends the component of weighted degree `n`, for
the weight `X r ↦ r + 1`, to the component of degree `n`. -/
theorem psumAlgHom_weightedHomogeneousComponent (n : ℕ) (p : MvPolynomial ℕ R) :
    psumAlgHom R (weightedHomogeneousComponent (· + 1) n p) =
      DirectSum.of _ n (psumAlgHom R p n) := by
  classical
  let := weightedDecomposition R (fun r : ℕ => r + 1)
  have h := DirectSum.map_decompose_shift (weightedHomogeneousSubmodule R (· + 1))
    (DirectSum.summand R fun n => stableSymmetricSubmodule R n) (psumAlgHom R).toAddMonoidHom id
    Function.injective_id
    (fun _ x hx => (mem_weightedHomogeneousSubmodule _ _ _ _).mp hx |>.aeval_mem
      fun r => DirectSum.of_mem_summand (r + 1) _) n p
  have hc : (DirectSum.decompose (weightedHomogeneousSubmodule R (· + 1)) p n : MvPolynomial ℕ R) =
      weightedHomogeneousComponent (· + 1) n p :=
    weightedDecomposition.decompose'_apply R _ p n
  rwa [hc, DirectSum.coe_decompose_summand] at h

end CommSemiring

section CommRing

variable (R : Type*) [CommRing R]

/-- **Newton's identities** in the symmetric functions:
`(n + 1) e_(n + 1) = ∑_{i + j = n} (-1)ʲ eᵢ p_(j + 1)`. -/
theorem mul_of_stableEsymm_eq_sum (n : ℕ) :
    (n + 1 : SymmetricFunction R) * DirectSum.of _ (n + 1) (stableEsymm R (n + 1)) =
      ∑ x ∈ antidiagonal n, (-1) ^ x.2 * DirectSum.of _ x.1 (stableEsymm R x.1) *
        DirectSum.of _ (x.2 + 1) (stablePsum R x.2.succ_ne_zero) := by
  refine ext_specialization fun d => ?_
  simp only [map_mul, map_add, map_natCast, map_one, specialization_of,
    coe_stableSymmetricProj_stableEsymm, map_sum, map_pow, map_neg,
    coe_stableSymmetricProj_stablePsum]
  exact mul_esymm_succ_eq_sum (Fin d) R n

end CommRing

section Rat

variable (R : Type*) [CommRing R] [Algebra ℚ R]

/-- **`E_n` evaluated at the power sums is the elementary symmetric function** `e_n`. -/
@[simp]
theorem psumAlgHom_esymmPsumPoly (n : ℕ) :
    psumAlgHom R (esymmPsumPoly R n) = DirectSum.of _ n (stableEsymm R n) :=
  ext_specialization fun d => by
    rw [specialization_psumAlgHom, aeval_psum_esymmPsumPoly, specialization_of,
      coe_stableSymmetricProj_stableEsymm]

/-- The algebra homomorphism `R[X₀, X₁, …] → R[X₀, X₁, …]` sending `X r` to `E_(r + 1)`, the
inverse of the power-sum presentation read in the elementary generators. -/
private noncomputable def esymmPsumAlgHom : MvPolynomial ℕ R →ₐ[R] MvPolynomial ℕ R :=
  aeval fun r => esymmPsumPoly R (r + 1)

private theorem psumAlgHom_comp_esymmPsumAlgHom :
    (psumAlgHom R).comp (esymmPsumAlgHom R) = SymmetricFunction.esymmAlgHom R :=
  MvPolynomial.algHom_ext fun r => by simp [esymmPsumAlgHom]

/-- Each variable `X r` is a polynomial in the `E_n`: Newton's recursion at `n = r` isolates the
term `(-1)ʳ X r`, and the other terms involve only `X j` for `j < r`. -/
private theorem esymmPsumAlgHom_surjective : Function.Surjective (esymmPsumAlgHom R) := by
  have hE : ∀ n, esymmPsumPoly R n ∈ (esymmPsumAlgHom R).range := by
    rintro (_ | n)
    · simp
    · exact ⟨X n, by simp [esymmPsumAlgHom]⟩
  have hX : ∀ r, X r ∈ (esymmPsumAlgHom R).range := by
    intro r
    induction r using Nat.strong_induction_on with
    | _ r ih =>
      have h := mul_esymmPsumPoly_succ R r
      rw [← add_sum_erase _ _ (by simp : ((0 : ℕ), r) ∈ antidiagonal r), esymmPsumPoly_zero,
        mul_one] at h
      have hrest : ∑ x ∈ (antidiagonal r).erase (0, r),
          (-1) ^ x.2 * esymmPsumPoly R x.1 * X x.2 ∈ (esymmPsumAlgHom R).range := by
        refine sum_mem fun x hx => mul_mem (mul_mem (pow_mem (neg_mem (one_mem _)) _) (hE _))
          (ih _ ?_)
        obtain ⟨hne, hx⟩ := mem_erase.mp hx
        rw [mem_antidiagonal] at hx
        refine lt_of_le_of_ne (by omega) fun h2 => hne ?_
        exact Prod.ext (by omega) h2
      have hmem : (-1 : MvPolynomial ℕ R) ^ r * X r ∈ (esymmPsumAlgHom R).range := by
        rw [eq_sub_of_add_eq h.symm]
        exact sub_mem (mul_mem (add_mem (natCast_mem _ r) (one_mem _)) (hE _)) hrest
      have := mul_mem (pow_mem (neg_mem (one_mem (esymmPsumAlgHom R).range)) r) hmem
      rwa [← mul_assoc, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_mul] at this
  refine (AlgHom.range_eq_top _).mp (eq_top_iff.mpr ?_)
  rw [← adjoin_range_X, Algebra.adjoin_le_iff]
  rintro _ ⟨r, rfl⟩
  exact hX r

/-- **The rational power-sum presentation of the symmetric functions**: over a `ℚ`-algebra `R`,
the ring of symmetric functions is the polynomial ring over `R` on the power sums `p₁, p₂, …`, the
variable `X r` representing `p_(r + 1)`. -/
noncomputable def psumAlgEquiv : MvPolynomial ℕ R ≃ₐ[R] SymmetricFunction R :=
  AlgEquiv.ofAlgHom (psumAlgHom R) ((esymmPsumAlgHom R).comp (esymmAlgEquiv R).symm.toAlgHom)
    (by
      refine algHom_ext fun n => ?_
      simp [esymmPsumAlgHom])
    (by
      refine AlgHom.ext fun y => ?_
      obtain ⟨p, rfl⟩ := esymmPsumAlgHom_surjective R y
      have hp : psumAlgHom R (esymmPsumAlgHom R p) = esymmAlgEquiv R p := by
        rw [esymmAlgEquiv_apply, ← psumAlgHom_comp_esymmPsumAlgHom R, AlgHom.comp_apply]
      rw [AlgHom.comp_apply, AlgHom.comp_apply, hp, AlgEquiv.coe_toAlgHom,
        AlgEquiv.symm_apply_apply, AlgHom.id_apply])

/-- The power-sum presentation is `TauCeti.SymmetricFunction.psumAlgHom`. -/
@[simp]
theorem psumAlgEquiv_apply (p : MvPolynomial ℕ R) : psumAlgEquiv R p = psumAlgHom R p :=
  (rfl)

/-- **The power sums are algebraically independent** over a `ℚ`-algebra. -/
theorem psumAlgHom_injective : Function.Injective (psumAlgHom R) :=
  (psumAlgEquiv R).injective

/-- **The power sums generate the symmetric functions** over a `ℚ`-algebra. -/
theorem psumAlgHom_surjective : Function.Surjective (psumAlgHom R) :=
  (psumAlgEquiv R).surjective

/-- Every symmetric function is the polynomial in the power sums that
`(TauCeti.SymmetricFunction.psumAlgEquiv R).symm` assigns to it. -/
@[simp]
theorem psumAlgHom_psumAlgEquiv_symm (x : SymmetricFunction R) :
    psumAlgHom R ((psumAlgEquiv R).symm x) = x :=
  (psumAlgEquiv R).apply_symm_apply x

/-- A polynomial in the power sums is recovered from the symmetric function it defines. -/
@[simp]
theorem psumAlgEquiv_symm_psumAlgHom (p : MvPolynomial ℕ R) :
    (psumAlgEquiv R).symm (psumAlgHom R p) = p :=
  (psumAlgEquiv R).symm_apply_apply p

/-- The power sum `p_n`, for `n ≠ 0`, corresponds to the variable `X (n - 1)`. -/
@[simp]
theorem psumAlgEquiv_symm_of_stablePsum {n : ℕ} (hn : n ≠ 0) :
    (psumAlgEquiv R).symm (DirectSum.of _ n (stablePsum R hn)) = X (n - 1) := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hn
  rw [AlgEquiv.symm_apply_eq, psumAlgEquiv_apply, Nat.add_sub_cancel, psumAlgHom_X]

/-- The elementary symmetric function `e_n` corresponds to Newton's polynomial `E_n`. -/
@[simp]
theorem psumAlgEquiv_symm_of_stableEsymm (n : ℕ) :
    (psumAlgEquiv R).symm (DirectSum.of _ n (stableEsymm R n)) = esymmPsumPoly R n := by
  rw [AlgEquiv.symm_apply_eq, psumAlgEquiv_apply, psumAlgHom_esymmPsumPoly]

/-- The inverse of the power-sum presentation sends a symmetric function of degree `n` to a
polynomial of weighted degree `n`, for the weight `X r ↦ r + 1`. -/
theorem isWeightedHomogeneous_psumAlgEquiv_symm_of {n : ℕ} (f : stableSymmetricSubmodule R n) :
    IsWeightedHomogeneous (· + 1) ((psumAlgEquiv R).symm (DirectSum.of _ n f)) n := by
  set p := (psumAlgEquiv R).symm (DirectSum.of _ n f)
  have hp : psumAlgHom R p = DirectSum.of _ n f := (psumAlgEquiv R).apply_symm_apply _
  have h : weightedHomogeneousComponent (· + 1) n p = p := by
    refine (psumAlgEquiv R).injective ?_
    rw [psumAlgEquiv_apply, psumAlgEquiv_apply, psumAlgHom_weightedHomogeneousComponent, hp,
      DirectSum.of_eq_same]
  rw [← h]
  exact weightedHomogeneousComponent_isWeightedHomogeneous n p

variable {R} in
/-- **Over a `ℚ`-algebra, algebra homomorphisms out of the symmetric functions are determined by
their values on the power sums** `p₁, p₂, …`. -/
theorem algHom_ext_of_stablePsum {A : Type*} [Semiring A] [Algebra R A]
    {f g : SymmetricFunction R →ₐ[R] A}
    (h : ∀ r, f (DirectSum.of _ (r + 1) (stablePsum R r.succ_ne_zero)) =
      g (DirectSum.of _ (r + 1) (stablePsum R r.succ_ne_zero))) : f = g := by
  have hfg : f.comp (psumAlgEquiv R).toAlgHom = g.comp (psumAlgEquiv R).toAlgHom :=
    MvPolynomial.algHom_ext fun r => by simpa using h r
  refine AlgHom.ext fun x => ?_
  obtain ⟨p, rfl⟩ := (psumAlgEquiv R).surjective x
  exact DFunLike.congr_fun hfg p

end Rat

end SymmetricFunction

end TauCeti
