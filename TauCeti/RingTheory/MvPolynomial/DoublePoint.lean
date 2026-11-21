/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import TauCeti.RingTheory.MvPolynomial.FirstJet
public import TauCeti.RingTheory.TrivSqZeroExt

/-!
# Double points in affine space

For a family of points `Pᵢ : σ → R`, `TauCeti.doubleIdeal P` is the square `(⋂ᵢ 𝔪_{Pᵢ})²` of the
ideal of polynomials vanishing at all of them, `𝔪_P = ker (eval P)`. The quotient
`R[X] ⧸ doubleIdeal P` is the coordinate ring of the affine scheme of the doubled points `2Pᵢ`.

For finitely many points over a commutative ring whose evaluation ideals `𝔪_{Pᵢ}` are pairwise
comaximal (for example, distinct points over a field), `doubleIdeal P` is the intersection
`⋂ᵢ 𝔪_{Pᵢ}²` of the squared point ideals, and the Chinese remainder theorem splits the quotient
into the local factors `R[X] ⧸ 𝔪_{Pᵢ}²`. For finitely many variables, each factor is the algebra of
first jets `TrivSqZeroExt R (σ → R)` (`TauCeti.ker_jetAlgebra`), so
`R[X] ⧸ doubleIdeal P ≃ₐ[R] ∏ᵢ TrivSqZeroExt R (σ → R)`, sending the class of `f` to its values
and gradients at the points. In particular values and first derivatives can be prescribed
independently by a single polynomial, and with `r` variables and `n` points over a ring satisfying
the strong rank condition the quotient has rank `n (r + 1)`, the length of `n` double points in
`r`-space. The product of square-zero algebras keeps the nilpotents: it is not the product of the
residue rings.

## Main definitions

* `TauCeti.doubleIdeal P`: the square of the ideal of the points `Pᵢ`.
* `TauCeti.doublePointQuotientEquiv`: for finitely many points with pairwise comaximal ideals over
  a commutative ring, the quotient by `doubleIdeal P` is the product of the first-jet algebras at
  the points.

## Main results

* `TauCeti.doubleIdeal_eq_iInf`: for finitely many points with pairwise comaximal ideals,
  `doubleIdeal P = ⋂ᵢ 𝔪_{Pᵢ}²`.
* `TauCeti.mem_doubleIdeal_iff`: for finitely many points with pairwise comaximal ideals, a
  polynomial lies in `doubleIdeal P` exactly when its value and first partial derivatives vanish at
  every point.
* `TauCeti.exists_forall_jetAlgebra_eq`: first jets at finitely many points with pairwise comaximal
  ideals can be prescribed independently.
* `TauCeti.finrank_quotient_doubleIdeal`: `n` double points in `r`-space with pairwise comaximal
  ideals have length `n (r + 1)`.

## References

* J.-M. Couveignes, *Enumerating number fields*, Ann. of Math. 192 (2020), 487–497, §3.
-/

public section

namespace TauCeti

open MvPolynomial

variable {σ ι : Type*}

/-- The ideal of the doubled points `2Pᵢ`: the square of the ideal of polynomials vanishing at
every point `Pᵢ`. Repetitions among the points are allowed. -/
noncomputable def doubleIdeal {R : Type*} [CommSemiring R] (P : ι → σ → R) :
    Ideal (MvPolynomial σ R) :=
  (⨅ i, RingHom.ker (eval (P i))) ^ 2

theorem doubleIdeal_def {R : Type*} [CommSemiring R] (P : ι → σ → R) :
    doubleIdeal P = (⨅ i, RingHom.ker (eval (P i))) ^ 2 :=
  (rfl)

/-- Reindexing the points does not change the ideal of the doubled points. -/
theorem doubleIdeal_comp {R ι' : Type*} [CommSemiring R] (P : ι → σ → R) (e : ι' ≃ ι) :
    doubleIdeal (P ∘ e) = doubleIdeal P := by
  simp only [doubleIdeal_def, Function.comp_apply]
  rw [e.iInf_comp (g := fun i ↦ RingHom.ker (eval (P i)))]

section CommRing

variable {R : Type*} [CommRing R] {P : ι → σ → R}

/-- For a finite family of points whose evaluation ideals are pairwise comaximal, the square of the
ideal of the points is the intersection of the squares of the ideals of the individual points. -/
theorem doubleIdeal_eq_iInf [Finite ι]
    (hP : Pairwise (Function.onFun IsCoprime fun i ↦ RingHom.ker (eval (P i)))) :
    doubleIdeal P = ⨅ i, RingHom.ker (eval (P i)) ^ 2 := by
  cases nonempty_fintype ι
  have hcop {f : ι → Ideal (MvPolynomial σ R)} (hf : Pairwise (Function.onFun IsCoprime f)) :
      ∏ i, f i = ⨅ i, f i := by
    simpa using Ideal.prod_eq_iInf_of_pairwise_isCoprime (s := Finset.univ) fun i _ j _ h ↦ hf h
  rw [doubleIdeal_def, ← hcop hP, ← hcop fun _ _ hij ↦ (hP hij).pow, Finset.prod_pow]

section JetAlgebra

variable [DecidableEq σ]

/-- For a finite family of points whose evaluation ideals are pairwise comaximal, the ideal of the
doubled points is the intersection of the kernels of the first jets at the points. -/
theorem doubleIdeal_eq_iInf_ker_jetAlgebra [Finite ι]
    (hP : Pairwise (Function.onFun IsCoprime fun i ↦ RingHom.ker (eval (P i)))) :
    doubleIdeal P = ⨅ i, RingHom.ker (jetAlgebra (P i)) := by
  simp only [doubleIdeal_eq_iInf hP, ker_jetAlgebra]

/-- **Chinese remainder for double points.** For finitely many points in finitely many variables
over a commutative ring whose evaluation ideals are pairwise comaximal, the coordinate ring of the
doubled points is isomorphic as an `R`-algebra to the product of the first-jet algebras at the
points: the class of `f` is sent to the values and gradients of `f` at the points
(`TauCeti.doublePointQuotientEquiv_mk`). -/
noncomputable def doublePointQuotientEquiv [Finite σ] [Finite ι]
    (hP : Pairwise (Function.onFun IsCoprime fun i ↦ RingHom.ker (eval (P i)))) :
    (MvPolynomial σ R ⧸ doubleIdeal P) ≃ₐ[R] (ι → TrivSqZeroExt R (σ → R)) :=
  let hpow : Pairwise (Function.onFun IsCoprime fun i ↦ RingHom.ker (eval (P i)) ^ 2) :=
    fun _ _ hij ↦ (hP hij).pow
  let crt : (MvPolynomial σ R ⧸ ⨅ i, RingHom.ker (eval (P i)) ^ 2) ≃ₐ[R]
      ((i : ι) → MvPolynomial σ R ⧸ RingHom.ker (eval (P i)) ^ 2) :=
    AlgEquiv.ofRingEquiv (f := Ideal.quotientInfRingEquivPiQuotient _ hpow) fun r ↦ by
      funext i
      exact Ideal.quotientInfRingEquivPiQuotient_mk_apply hpow (C r) i
  (Ideal.quotientEquivAlgOfEq R (doubleIdeal_eq_iInf hP)).trans <|
    crt.trans <| AlgEquiv.piCongrRight fun i ↦ jetAlgebraEquiv (P i)

/-- The class of `f` modulo the ideal of the doubled points corresponds to the first jets of `f`
at the points. -/
@[simp]
theorem doublePointQuotientEquiv_mk [Finite σ] [Finite ι]
    (hP : Pairwise (Function.onFun IsCoprime fun i ↦ RingHom.ker (eval (P i))))
    (f : MvPolynomial σ R) :
    doublePointQuotientEquiv hP (Ideal.Quotient.mk _ f) = fun i ↦ jetAlgebra (P i) f := by
  funext i
  unfold doublePointQuotientEquiv
  simp only [AlgEquiv.trans_apply, Ideal.quotientEquivAlgOfEq_mk, AlgEquiv.piCongrRight_apply,
    AlgEquiv.ofRingEquiv_apply]
  rw [Ideal.quotientInfRingEquivPiQuotient_mk_apply (fun _ _ hij ↦ (hP hij).pow) f i,
    jetAlgebraEquiv_mk]

/-- **Simultaneous first-jet interpolation.** At finitely many points in finitely many variables
over a commutative ring whose evaluation ideals are pairwise comaximal, any values and gradients are
the values and gradients of a single polynomial. -/
theorem exists_forall_jetAlgebra_eq [Finite σ] [Finite ι]
    (hP : Pairwise (Function.onFun IsCoprime fun i ↦ RingHom.ker (eval (P i))))
    (y : ι → TrivSqZeroExt R (σ → R)) : ∃ f : MvPolynomial σ R, ∀ i, jetAlgebra (P i) f = y i := by
  obtain ⟨q, hq⟩ := (doublePointQuotientEquiv hP).surjective y
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective q
  exact ⟨f, fun i ↦ by simpa using congrFun hq i⟩

end JetAlgebra

/-- For finitely many points with pairwise comaximal evaluation ideals, a polynomial lies in the
ideal of the doubled points exactly when its value and all its first partial derivatives vanish at
every point. -/
theorem mem_doubleIdeal_iff [Finite ι]
    (hP : Pairwise (Function.onFun IsCoprime fun i ↦ RingHom.ker (eval (P i))))
    {f : MvPolynomial σ R} :
    f ∈ doubleIdeal P ↔ ∀ i, eval (P i) f = 0 ∧ ∀ j, eval (P i) (pderiv j f) = 0 := by
  classical
  simp [doubleIdeal_eq_iInf_ker_jetAlgebra hP, RingHom.mem_ker, jetAlgebra_eq_zero_iff]

/-- **Length of distinct double points.** Over a commutative ring satisfying the strong rank
condition, `n` doubled points in affine `r`-space with pairwise comaximal evaluation ideals have
length `n (r + 1)`: the quotient by their ideal has rank `n (r + 1)`. -/
theorem finrank_quotient_doubleIdeal [StrongRankCondition R] [Fintype ι] [Fintype σ]
    (hP : Pairwise (Function.onFun IsCoprime fun i ↦ RingHom.ker (eval (P i)))) :
    Module.finrank R (MvPolynomial σ R ⧸ doubleIdeal P) =
      Fintype.card ι * (Fintype.card σ + 1) := by
  classical
  rw [(doublePointQuotientEquiv hP).toLinearEquiv.finrank_eq, Module.finrank_pi_fintype]
  simp [TrivSqZeroExt.finrank_eq_finrank_add_one]

end CommRing

end TauCeti
