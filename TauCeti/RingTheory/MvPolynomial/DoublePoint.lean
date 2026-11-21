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

For finitely many points `Pᵢ : σ → R`, `TauCeti.doubleIdeal P` is the square `(⋂ᵢ 𝔪_{Pᵢ})²` of the
ideal of polynomials vanishing at all of them, `𝔪_P = ker (eval P)`. The quotient
`R[X] ⧸ doubleIdeal P` is the coordinate ring of the affine scheme of the doubled points `2Pᵢ`.

Over a field and for distinct points, the ideals `𝔪_{Pᵢ}` are pairwise coprime, so `doubleIdeal P`
is the intersection `⋂ᵢ 𝔪_{Pᵢ}²` of the squared point ideals, and the Chinese remainder theorem
splits the quotient into the local factors `k[X] ⧸ 𝔪_{Pᵢ}²`. For finitely many variables, each
factor is the algebra of first jets `TrivSqZeroExt k (σ → k)` (`TauCeti.ker_jetAlgebra`), so
`k[X] ⧸ doubleIdeal P ≃ₐ[k] ∏ᵢ TrivSqZeroExt k (σ → k)`, sending the class of `f` to its values
and gradients at the points. In particular values and first derivatives at distinct points can be
prescribed independently by some polynomial, and with `r` variables and `n` points the quotient
has dimension `n (r + 1)`, the length of `n` distinct double points in `r`-space. The product of
square-zero algebras keeps the nilpotents: it is not the product of the residue fields.

## Main definitions

* `TauCeti.doubleIdeal P`: the square of the ideal of the points `Pᵢ`.
* `TauCeti.doublePointQuotientEquiv`: for distinct points over a field, the quotient by
  `doubleIdeal P` is the product of the first-jet algebras at the points.

## Main results

* `TauCeti.doubleIdeal_eq_iInf`: for distinct points over a field, `doubleIdeal P = ⋂ᵢ 𝔪_{Pᵢ}²`.
* `TauCeti.mem_doubleIdeal_iff`: a polynomial lies in `doubleIdeal P` exactly when its value and
  first partial derivatives vanish at every point.
* `TauCeti.exists_forall_jetAlgebra_eq`: first jets at distinct points can be prescribed
  independently.
* `TauCeti.finrank_quotient_doubleIdeal`: `n` distinct double points in `r`-space have length
  `n (r + 1)`.

## References

* J.-M. Couveignes, *Enumerating number fields*, Ann. of Math. 192 (2020), 487–497, §3.
-/

public section

namespace TauCeti

open MvPolynomial Function

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

/-- The double-point ideal of an empty family of points is the unit ideal. -/
@[simp]
theorem doubleIdeal_eq_top_of_isEmpty {R : Type*} [CommSemiring R] [IsEmpty ι] (P : ι → σ → R) :
    doubleIdeal P = ⊤ := by
  simp [doubleIdeal_def]

section CommRing

variable {R : Type*} [CommRing R] {P : ι → σ → R}

/-- For finitely many points over a commutative ring with pairwise unit coordinate differences,
the square of the ideal of the points is the intersection of the squares of the ideals of the
individual points. -/
theorem doubleIdeal_eq_iInf_of_pairwise_isUnit [Finite ι]
    (hP : Pairwise fun i j ↦ ∃ s, IsUnit (P i s - P j s)) :
    doubleIdeal P = ⨅ i, RingHom.ker (eval (P i)) ^ 2 := by
  cases nonempty_fintype ι
  have hcop {f : ι → Ideal (MvPolynomial σ R)} (hf : Pairwise (IsCoprime on f)) :
      ∏ i, f i = ⨅ i, f i := by
    simpa using Ideal.prod_eq_iInf_of_pairwise_isCoprime (s := Finset.univ) fun i _ j _ h ↦ hf h
  rw [doubleIdeal_def, ← hcop fun i j h ↦ isCoprime_ker_eval_of_exists_isUnit_sub (hP h),
    ← hcop fun i j h ↦ isCoprime_ker_eval_sq_of_exists_isUnit_sub (hP h), Finset.prod_pow]

section JetAlgebra

variable [DecidableEq σ]

/-- For finitely many points with pairwise unit coordinate differences, the ideal of the doubled
points is the intersection of the kernels of the first jets at the points. -/
theorem doubleIdeal_eq_iInf_ker_jetAlgebra_of_pairwise_isUnit [Finite ι]
    (hP : Pairwise fun i j ↦ ∃ s, IsUnit (P i s - P j s)) :
    doubleIdeal P = ⨅ i, RingHom.ker (jetAlgebra (P i)) := by
  simp only [doubleIdeal_eq_iInf_of_pairwise_isUnit hP, ker_jetAlgebra]

/-- **Simultaneous first-jet interpolation.** At finitely many points in finitely many variables
over a commutative ring with pairwise unit coordinate differences, any values and gradients are the
values and gradients of a single polynomial. -/
theorem exists_forall_jetAlgebra_eq_of_pairwise_isUnit [Finite ι] [Finite σ]
    (hP : Pairwise fun i j ↦ ∃ s, IsUnit (P i s - P j s)) (y : ι → TrivSqZeroExt R (σ → R)) :
    ∃ f : MvPolynomial σ R, ∀ i, jetAlgebra (P i) f = y i := by
  choose g hg using fun i ↦ jetAlgebra_surjective (P i) (y i)
  have hcop : Pairwise (IsCoprime on fun i ↦ RingHom.ker (jetAlgebra (P i))) := fun i j h ↦ by
    simpa only [ker_jetAlgebra] using isCoprime_ker_eval_sq_of_exists_isUnit_sub (hP h)
  obtain ⟨f, hf⟩ := Ideal.exists_forall_sub_mem_ideal hcop g
  refine ⟨f, fun i ↦ ?_⟩
  rw [← hg i, ← sub_eq_zero, ← map_sub]
  exact hf i

/-- For finitely many points in finitely many variables over a commutative ring with pairwise unit
coordinate differences, the coordinate ring of the doubled points is the product of the first-jet
algebras at the points. -/
noncomputable def doublePointQuotientEquivOfPairwiseIsUnit [Finite ι] [Finite σ]
    (hP : Pairwise fun i j ↦ ∃ s, IsUnit (P i s - P j s)) :
    (MvPolynomial σ R ⧸ doubleIdeal P) ≃ₐ[R] (ι → TrivSqZeroExt R (σ → R)) :=
  (Ideal.quotientEquivAlgOfEq R <| by
      rw [doubleIdeal_eq_iInf_ker_jetAlgebra_of_pairwise_isUnit hP]
      ext f
      simp [RingHom.mem_ker, funext_iff]).trans
    (Ideal.quotientKerAlgEquivOfSurjective
      (f := AlgHom.pi fun i ↦ jetAlgebra (P i)) <| show Surjective _ from fun y ↦ by
        obtain ⟨f, hf⟩ := exists_forall_jetAlgebra_eq_of_pairwise_isUnit hP y
        exact ⟨f, funext hf⟩)

/-- The class of `f` modulo the ideal of the doubled points corresponds to the first jets of `f`
at the points. -/
@[simp]
theorem doublePointQuotientEquivOfPairwiseIsUnit_mk [Finite ι] [Finite σ]
    (hP : Pairwise fun i j ↦ ∃ s, IsUnit (P i s - P j s)) (f : MvPolynomial σ R) :
    doublePointQuotientEquivOfPairwiseIsUnit hP (Ideal.Quotient.mk _ f) =
      fun i ↦ jetAlgebra (P i) f := by
  funext i
  simp [doublePointQuotientEquivOfPairwiseIsUnit]

/-- Reindexing the point family along an equivalence commutes with
`doublePointQuotientEquivOfPairwiseIsUnit`. -/
theorem doublePointQuotientEquivOfPairwiseIsUnit_comp_equiv {ι' : Type*}
    [Finite ι] [Finite ι'] [Finite σ]
    (hP : Pairwise fun i j ↦ ∃ s, IsUnit (P i s - P j s)) (e : ι' ≃ ι)
    (x : MvPolynomial σ R ⧸ doubleIdeal (P ∘ e)) (i' : ι') :
    doublePointQuotientEquivOfPairwiseIsUnit (hP.comp_of_injective e.injective) x i' =
      doublePointQuotientEquivOfPairwiseIsUnit hP
        (Ideal.quotientEquivAlgOfEq R (doubleIdeal_comp P e) x) (e i') := by
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [doublePointQuotientEquivOfPairwiseIsUnit_mk (P := P ∘ e), Ideal.quotientEquivAlgOfEq_mk,
    doublePointQuotientEquivOfPairwiseIsUnit_mk]
  rfl

end JetAlgebra

/-- For finitely many points over a commutative ring with pairwise unit coordinate differences, a
polynomial lies in `doubleIdeal P` iff its value and first partial derivatives vanish at every
point. -/
theorem mem_doubleIdeal_iff_of_pairwise_isUnit [Finite ι]
    (hP : Pairwise fun i j ↦ ∃ s, IsUnit (P i s - P j s)) {f : MvPolynomial σ R} :
    f ∈ doubleIdeal P ↔ ∀ i, eval (P i) f = 0 ∧ ∀ j, eval (P i) (pderiv j f) = 0 := by
  classical
  simp [doubleIdeal_eq_iInf_ker_jetAlgebra_of_pairwise_isUnit hP, RingHom.mem_ker,
    jetAlgebra_eq_zero_iff]

/-- **Length of distinct double points.** Over a commutative ring with the strong rank condition,
for finitely many points in finitely many variables with pairwise unit coordinate differences, the
quotient by `doubleIdeal P` has rank `card ι * (card σ + 1)`. -/
theorem finrank_quotient_doubleIdeal_of_pairwise_isUnit [StrongRankCondition R]
    [Fintype ι] [Fintype σ] (hP : Pairwise fun i j ↦ ∃ s, IsUnit (P i s - P j s)) :
    Module.finrank R (MvPolynomial σ R ⧸ doubleIdeal P) =
      Fintype.card ι * (Fintype.card σ + 1) := by
  classical
  rw [(doublePointQuotientEquivOfPairwiseIsUnit hP).toLinearEquiv.finrank_eq,
    Module.finrank_pi_fintype]
  simp [TrivSqZeroExt.finrank_eq_finrank_add_one]

end CommRing

section Field

variable {k : Type*} [Field k] {P : ι → σ → k}

/-- Distinct points over a field have a unit difference in some coordinate. -/
theorem pairwise_exists_isUnit_sub_of_injective (hP : Function.Injective P) :
    Pairwise fun i j ↦ ∃ s, IsUnit (P i s - P j s) := fun _ _ hij ↦ by
  obtain ⟨s, hs⟩ := Function.ne_iff.mp (hP.ne hij)
  exact ⟨s, (sub_ne_zero.mpr hs).isUnit⟩

/-- For finitely many distinct points over a field, the square of the ideal of the points is the
intersection of the squares of the ideals of the individual points. -/
theorem doubleIdeal_eq_iInf [Finite ι] (hP : Function.Injective P) :
    doubleIdeal P = ⨅ i, RingHom.ker (eval (P i)) ^ 2 :=
  doubleIdeal_eq_iInf_of_pairwise_isUnit (pairwise_exists_isUnit_sub_of_injective hP)

section JetAlgebra

variable [DecidableEq σ]

/-- For finitely many distinct points over a field, the ideal of the doubled points is the
intersection of the kernels of the first jets at the points. -/
theorem doubleIdeal_eq_iInf_ker_jetAlgebra [Finite ι] (hP : Function.Injective P) :
    doubleIdeal P = ⨅ i, RingHom.ker (jetAlgebra (P i)) :=
  doubleIdeal_eq_iInf_ker_jetAlgebra_of_pairwise_isUnit
    (pairwise_exists_isUnit_sub_of_injective hP)

variable [Finite σ]

/-- **Simultaneous first-jet interpolation.** At finitely many distinct points in finitely many
variables over a field, any values and gradients are the values and gradients of a single
polynomial. -/
theorem exists_forall_jetAlgebra_eq [Finite ι] (hP : Function.Injective P)
    (y : ι → TrivSqZeroExt k (σ → k)) : ∃ f : MvPolynomial σ k, ∀ i, jetAlgebra (P i) f = y i :=
  exists_forall_jetAlgebra_eq_of_pairwise_isUnit (pairwise_exists_isUnit_sub_of_injective hP) y

/-- For finitely many distinct points in finitely many variables over a field, the coordinate ring
of the doubled points is the product of the first-jet algebras at the points: the class of `f` is
sent to the values and gradients of `f` at the points (`TauCeti.doublePointQuotientEquiv_mk`). -/
noncomputable def doublePointQuotientEquiv [Finite ι] (hP : Function.Injective P) :
    (MvPolynomial σ k ⧸ doubleIdeal P) ≃ₐ[k] (ι → TrivSqZeroExt k (σ → k)) :=
  doublePointQuotientEquivOfPairwiseIsUnit (pairwise_exists_isUnit_sub_of_injective hP)

/-- The class of `f` modulo the ideal of the doubled points corresponds to the first jets of `f`
at the points. -/
@[simp]
theorem doublePointQuotientEquiv_mk [Finite ι] (hP : Function.Injective P)
    (f : MvPolynomial σ k) :
    doublePointQuotientEquiv hP (Ideal.Quotient.mk _ f) = fun i ↦ jetAlgebra (P i) f :=
  doublePointQuotientEquivOfPairwiseIsUnit_mk _ f

/-- Reindexing the point family along an equivalence commutes with `doublePointQuotientEquiv`. -/
theorem doublePointQuotientEquiv_comp_equiv {ι' : Type*} [Finite ι] [Finite ι']
    (hP : Function.Injective P) (e : ι' ≃ ι)
    (x : MvPolynomial σ k ⧸ doubleIdeal (P ∘ e)) (i' : ι') :
    doublePointQuotientEquiv (hP.comp e.injective) x i' =
      doublePointQuotientEquiv hP (Ideal.quotientEquivAlgOfEq k (doubleIdeal_comp P e) x) (e i') :=
  doublePointQuotientEquivOfPairwiseIsUnit_comp_equiv
    (pairwise_exists_isUnit_sub_of_injective hP) e x i'

end JetAlgebra

/-- For finitely many distinct points over a field, a polynomial lies in the ideal of the doubled
points exactly when its value and all its first partial derivatives vanish at every point. -/
theorem mem_doubleIdeal_iff [Finite ι] (hP : Function.Injective P)
    {f : MvPolynomial σ k} :
    f ∈ doubleIdeal P ↔ ∀ i, eval (P i) f = 0 ∧ ∀ j, eval (P i) (pderiv j f) = 0 :=
  mem_doubleIdeal_iff_of_pairwise_isUnit (pairwise_exists_isUnit_sub_of_injective hP)

/-- **Length of distinct double points.** Over a field, `n` distinct doubled points in affine
`r`-space have length `n (r + 1)`: the quotient by their ideal has dimension `n (r + 1)`. -/
theorem finrank_quotient_doubleIdeal [Fintype ι] [Fintype σ] (hP : Function.Injective P) :
    Module.finrank k (MvPolynomial σ k ⧸ doubleIdeal P) =
      Fintype.card ι * (Fintype.card σ + 1) :=
  finrank_quotient_doubleIdeal_of_pairwise_isUnit (pairwise_exists_isUnit_sub_of_injective hP)

end Field

end TauCeti
