/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem
public import TauCeti.RingTheory.MvPolynomial.Symmetric.PowerSum.Basic
public import TauCeti.RingTheory.MvPolynomial.Symmetric.Schur.Complete
public import TauCeti.RingTheory.MvPolynomial.Symmetric.Schur.Elementary
public import TauCeti.RingTheory.MvPolynomial.Symmetric.Stable.Algebra

/-!
# The elementary, complete and power-sum symmetric functions, and the fundamental theorem

The classical families of symmetric polynomials are stable under setting a variable to zero, so
they define symmetric functions: the elementary symmetric function `e_n`, the complete homogeneous
symmetric function `h_n`, and, for `n ≠ 0`, the power sum `p_n`. There is no stable zeroth power
sum: the zeroth power sum in `d` variables is the number `d`, which depends on the alphabet.

The main result is the **fundamental theorem of symmetric functions**: the elementary symmetric
functions `e₁, e₂, …` are algebraically independent generators of the ring `Λ_R` of symmetric
functions over a commutative ring. In finitely many variables this is Mathlib's
`MvPolynomial.esymmAlgEquiv`.

## Main definitions

* `TauCeti.stableEsymm R n`, `TauCeti.stableHsymm R n`: the symmetric functions `e_n` and `h_n`.
* `TauCeti.stablePsum R hn`: the power sum symmetric function `p_n`, for `hn : n ≠ 0`.
* `TauCeti.SymmetricFunction.esymmAlgHom R`: the algebra homomorphism `R[X₀, X₁, …] → Λ_R` sending
  `X r` to `e_(r + 1)`.
* `TauCeti.SymmetricFunction.esymmAlgEquiv R`: this homomorphism as an algebra equivalence.

## Main results

* `TauCeti.SymmetricFunction.algHom_ext`: algebra homomorphisms out of `Λ_R` are determined by
  their values on the elementary symmetric functions.

## References

* [I. G. Macdonald, *Symmetric Functions and Hall Polynomials*][macdonald1995], Chapter I,
  Section 2: (2.4) for the free generation of `Λ` by the `e_r`, and the definitions of `h_r`
  and `p_r`.
-/

public section

namespace TauCeti

open MvPolynomial DirectSum

section CommSemiring

variable (R : Type*) [CommSemiring R]

/-- **The elementary symmetric function** `e_n`, the Schur function of the one-column partition
`(1ⁿ)`. -/
noncomputable def stableEsymm (n : ℕ) : stableSymmetricSubmodule R n :=
  stableSchur R (Nat.Partition.ones n)

/-- The elementary symmetric function `e_n`, read in `d` variables, is the elementary symmetric
polynomial. -/
@[simp]
theorem coe_stableSymmetricProj_stableEsymm (n d : ℕ) :
    (stableSymmetricProj R n d (stableEsymm R n) : MvPolynomial (Fin d) R) = esymm (Fin d) R n := by
  rw [stableEsymm, coe_stableSymmetricProj_stableSchur, schurPoly_ones]

/-- `e_0` is the unit of the symmetric functions. -/
@[simp]
theorem stableEsymm_zero : stableEsymm R 0 = stableSymmetricOne R :=
  stableSymmetricSubmodule_ext fun d => Subtype.ext <| by simp

/-- **The complete homogeneous symmetric function** `h_n`. -/
noncomputable def stableHsymm (n : ℕ) : stableSymmetricSubmodule R n :=
  ⟨fun d => ⟨hsymm (Fin d) R n,
      mem_symmetricHomogeneousSubmodule.mpr ⟨hsymm_isSymmetric _ _ _, isHomogeneous_hsymm n⟩⟩,
    mem_stableSymmetricSubmodule.mpr fun d => aeval_snoc_zero_hsymm d n⟩

/-- The complete homogeneous symmetric function `h_n`, read in `d` variables, is the complete
homogeneous symmetric polynomial. -/
@[simp]
theorem coe_stableSymmetricProj_stableHsymm (n d : ℕ) :
    (stableSymmetricProj R n d (stableHsymm R n) : MvPolynomial (Fin d) R) = hsymm (Fin d) R n := by
  rw [stableHsymm, stableSymmetricProj_mk]

/-- `h_0` is the unit of the symmetric functions. -/
@[simp]
theorem stableHsymm_zero : stableHsymm R 0 = stableSymmetricOne R :=
  stableSymmetricSubmodule_ext fun d => Subtype.ext <| by simp

/-- **The power sum symmetric function** `p_n`, for `n ≠ 0`. There is no stable `p_0`: the zeroth
power sum in `d` variables is `d`. -/
noncomputable def stablePsum {n : ℕ} (hn : n ≠ 0) : stableSymmetricSubmodule R n :=
  ⟨fun d => ⟨psum (Fin d) R n,
      mem_symmetricHomogeneousSubmodule.mpr ⟨psum_isSymmetric _ _ _, isHomogeneous_psum R n⟩⟩,
    mem_stableSymmetricSubmodule.mpr fun d => aeval_snoc_zero_psum d hn⟩

/-- The power sum symmetric function `p_n`, read in `d` variables, is the power sum polynomial. -/
@[simp]
theorem coe_stableSymmetricProj_stablePsum {n : ℕ} (hn : n ≠ 0) (d : ℕ) :
    (stableSymmetricProj R n d (stablePsum R hn) : MvPolynomial (Fin d) R) = psum (Fin d) R n := by
  rw [stablePsum, stableSymmetricProj_mk]

namespace SymmetricFunction

/-- The algebra homomorphism from polynomials in countably many variables to the symmetric functions
sending the variable `X r` to the elementary symmetric function `e_(r + 1)`. -/
noncomputable def esymmAlgHom : MvPolynomial ℕ R →ₐ[R] SymmetricFunction R :=
  aeval fun r => DirectSum.of _ (r + 1) (stableEsymm R (r + 1))

/-- The variable `X r` is sent to the elementary symmetric function `e_(r + 1)`. -/
@[simp]
theorem esymmAlgHom_X (r : ℕ) :
    esymmAlgHom R (X r) = DirectSum.of _ (r + 1) (stableEsymm R (r + 1)) :=
  aeval_X _ _

/-- In `d` variables, `TauCeti.SymmetricFunction.esymmAlgHom` substitutes the elementary symmetric
polynomials. -/
theorem specialization_esymmAlgHom (d : ℕ) (p : MvPolynomial ℕ R) :
    specialization R d (esymmAlgHom R p) = aeval (fun r => esymm (Fin d) R (r + 1)) p := by
  have h : (specialization R d).comp (esymmAlgHom R) = aeval fun r => esymm (Fin d) R (r + 1) :=
    MvPolynomial.algHom_ext fun r => by simp
  exact DFunLike.congr_fun h p

/-- Each monomial in the elementary symmetric functions is homogeneous. -/
private theorem exists_esymmAlgHom_monomial_eq_of (s : ℕ →₀ ℕ) (a : R) :
    ∃ (k : ℕ) (y : stableSymmetricSubmodule R k),
      esymmAlgHom R (monomial s a) = DirectSum.of _ k y := by
  refine induction_on_monomial (motive := fun p => ∃ (k : ℕ) (y : stableSymmetricSubmodule R k),
    esymmAlgHom R p = DirectSum.of _ k y) (fun a => ?_) (fun p r hp => ?_) s a
  · exact ⟨0, _, (esymmAlgHom R).commutes a⟩
  · obtain ⟨k, y, hy⟩ := hp
    exact ⟨_, _, by rw [map_mul, hy, esymmAlgHom_X, DirectSum.of_mul_of]⟩

/-- The image of `TauCeti.SymmetricFunction.esymmAlgHom` contains the homogeneous components of its
elements. -/
private theorem of_esymmAlgHom_apply_mem_range (p : MvPolynomial ℕ R) (n : ℕ) :
    DirectSum.of _ n (esymmAlgHom R p n) ∈ (esymmAlgHom R).range := by
  induction p using MvPolynomial.induction_on' with
  | monomial s a =>
    obtain ⟨k, y, hy⟩ := exists_esymmAlgHom_monomial_eq_of R s a
    rw [hy]
    obtain rfl | hnk := eq_or_ne n k
    · rw [DirectSum.of_eq_same, ← hy]
      exact AlgHom.mem_range_self _ _
    · rw [DirectSum.of_eq_of_ne _ _ _ hnk, map_zero]
      exact zero_mem _
  | add p q hp hq =>
    rw [map_add, DirectSum.add_apply, map_add]
    exact add_mem hp hq

end SymmetricFunction

end CommSemiring

section CommRing

namespace SymmetricFunction

variable (R : Type*) [CommRing R]

/-- **The elementary symmetric functions are algebraically independent.** -/
theorem esymmAlgHom_injective : Function.Injective (esymmAlgHom R) := by
  refine (injective_iff_map_eq_zero _).mpr fun p hp => ?_
  obtain ⟨N, hN⟩ : ∃ N, ∀ r ∈ p.vars, r < N :=
    ⟨p.vars.sup id + 1, fun r hr => Nat.lt_succ_of_le (Finset.le_sup (f := id) hr)⟩
  obtain ⟨q, rfl⟩ := exists_rename_eq_of_vars_subset_range p (Fin.val : Fin N → ℕ)
    Fin.val_injective fun r hr => ⟨⟨r, hN r hr⟩, rfl⟩
  have hq := congrArg (specialization R N) hp
  rw [specialization_esymmAlgHom, aeval_rename, map_zero] at hq
  have : q = 0 := MvPolynomial.esymmAlgHom_injective R (σ := Fin N) (by simp)
    (Subtype.ext <| (esymmAlgHom_apply _).trans <| hq.trans <| by simp)
  rw [this, map_zero]

/-- A symmetric function of degree `n` is a polynomial in the elementary symmetric functions. -/
private theorem of_mem_range_esymmAlgHom {n : ℕ} (f : stableSymmetricSubmodule R n) :
    DirectSum.of _ n f ∈ (esymmAlgHom R).range := by
  have hf := mem_symmetricHomogeneousSubmodule.mp (stableSymmetricProj R n n f).2
  obtain ⟨q, hq⟩ :=
    MvPolynomial.esymmAlgHom_surjective R (σ := Fin n) (n := n) (by simp) ⟨_, hf.1⟩
  have hx :
      specialization R n (esymmAlgHom R (rename Fin.val q)) = stableSymmetricProj R n n f := by
    rw [specialization_esymmAlgHom, aeval_rename, ← congrArg Subtype.val hq]
    exact (esymmAlgHom_apply _).symm
  have hfx : esymmAlgHom R (rename Fin.val q) n = f := by
    refine stableSymmetricProj_injective le_rfl (Subtype.ext ?_)
    rw [← homogeneousComponent_specialization, hx, homogeneousComponent_of_mem hf.2,
      ite_eq_left rfl]
  rw [← hfx]
  exact of_esymmAlgHom_apply_mem_range R _ n

/-- **The elementary symmetric functions generate the symmetric functions.** -/
theorem esymmAlgHom_surjective : Function.Surjective (esymmAlgHom R) := by
  intro x
  induction x using DirectSum.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | of n f => exact of_mem_range_esymmAlgHom R f
  | add x y hx hy =>
    obtain ⟨p, rfl⟩ := hx
    obtain ⟨q, rfl⟩ := hy
    exact ⟨p + q, map_add _ _ _⟩

/-- **The fundamental theorem of symmetric functions**: the ring of symmetric functions over a
commutative ring `R` is the polynomial ring over `R` on the elementary symmetric functions
`e₁, e₂, …`, the variable `X r` representing `e_(r + 1)`. -/
noncomputable def esymmAlgEquiv : MvPolynomial ℕ R ≃ₐ[R] SymmetricFunction R :=
  AlgEquiv.ofBijective (esymmAlgHom R) ⟨esymmAlgHom_injective R, esymmAlgHom_surjective R⟩

/-- The fundamental equivalence is `TauCeti.SymmetricFunction.esymmAlgHom`. -/
@[simp]
theorem esymmAlgEquiv_apply (p : MvPolynomial ℕ R) : esymmAlgEquiv R p = esymmAlgHom R p :=
  (rfl)

/-- The elementary symmetric function `e_(r + 1)` corresponds to the variable `X r`. -/
@[simp]
theorem esymmAlgEquiv_symm_of_stableEsymm (r : ℕ) :
    (esymmAlgEquiv R).symm (DirectSum.of _ (r + 1) (stableEsymm R (r + 1))) = X r := by
  rw [AlgEquiv.symm_apply_eq, esymmAlgEquiv_apply, esymmAlgHom_X]

variable {R} in
/-- **Algebra homomorphisms out of the symmetric functions are determined by their values on the
elementary symmetric functions** `e₁, e₂, …`. -/
theorem algHom_ext {A : Type*} [Semiring A] [Algebra R A] {f g : SymmetricFunction R →ₐ[R] A}
    (h : ∀ n, f (DirectSum.of _ (n + 1) (stableEsymm R (n + 1))) =
      g (DirectSum.of _ (n + 1) (stableEsymm R (n + 1)))) : f = g := by
  have hfg : f.comp (esymmAlgEquiv R).toAlgHom = g.comp (esymmAlgEquiv R).toAlgHom :=
    MvPolynomial.algHom_ext fun r => by simpa using h r
  refine AlgHom.ext fun x => ?_
  obtain ⟨p, rfl⟩ := (esymmAlgEquiv R).surjective x
  exact DFunLike.congr_fun hfg p

end SymmetricFunction

end CommRing

end TauCeti
