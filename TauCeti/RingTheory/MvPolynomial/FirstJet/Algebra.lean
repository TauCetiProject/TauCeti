/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.InvariantBasisNumber
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.MvPolynomial.Ideal
public import TauCeti.RingTheory.MvPolynomial.OrderAt
import Mathlib.Data.Finsupp.Weight
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.RingTheory.Ideal.Operations
import TauCeti.RingTheory.MvPolynomial.Ideal
import TauCeti.RingTheory.TrivSqZeroExt

/-!
# First-jet algebras and finite double-point quotients

For a point `P : σ → R` over a commutative semiring `R`, the first-jet algebra evaluation
`MvPolynomial.jetAlgebra P : MvPolynomial σ R →ₐ[R] TrivSqZeroExt R (σ → R)` sends each variable
`X j` to `inl (P j) + inr (Pi.single j 1)`. Because products of infinitesimal elements vanish in
the trivial square-zero extension, the scalar component of `jetAlgebra P f` is the value `eval P f`
and the `j`-th infinitesimal coordinate is the partial derivative `eval P (pderiv j f)`, in every
characteristic.

Over a commutative ring `R`, translating variables by `MvPolynomial.taylor P` identifies the `k`-th
power of the evaluation ideal `RingHom.ker (eval P)` with the pullback of `idealOfVars σ R ^ k`,
which immediately shows that `RingHom.ker (jetAlgebra P) = RingHom.ker (eval P) ^ 2` with no
finiteness or field assumption. When `σ` is finite, `jetAlgebra P` is surjective and descends to an
`R`-algebra equivalence `MvPolynomial.jetAlgebraEquiv P`.

For a family of points `P : ι → σ → R`, the doubled-point ideal is
`MvPolynomial.doubleIdeal P = (⨅ i, RingHom.ker (eval (P i))) ^ 2`. Whenever the point ideals are
pairwise comaximal (in particular, over a field for an injective finite tuple `P`), Chinese
remainder decomposes `doubleIdeal P` as `⨅ i, RingHom.ker (eval (P i)) ^ 2` and identifies the
nonreduced quotient `MvPolynomial σ R ⧸ doubleIdeal P` as an `R`-algebra with the product of
first-jet algebras `ι → TrivSqZeroExt R (σ → R)` (`MvPolynomial.doublePointQuotientEquivOfPairwise`,
`MvPolynomial.doublePointQuotientEquiv`). Its rank over `R` is
`Fintype.card ι * (Fintype.card σ + 1)` (`MvPolynomial.finrank_quotient_doubleIdeal`).

## Main definitions

* `MvPolynomial.jetAlgebra`: the first-jet `R`-algebra homomorphism into `TrivSqZeroExt R (σ → R)`.
* `MvPolynomial.jetAlgebraEquiv`: the `R`-algebra equivalence
  `(MvPolynomial σ R ⧸ RingHom.ker (eval P) ^ 2) ≃ₐ[R] TrivSqZeroExt R (σ → R)`.
* `MvPolynomial.doubleIdeal`: the squared intersection ideal
  `(⨅ i, RingHom.ker (eval (P i))) ^ 2`.
* `MvPolynomial.doublePointQuotientEquivOfPairwise`, `MvPolynomial.doublePointQuotientEquiv`: the
  `R`-algebra equivalence `(MvPolynomial σ R ⧸ doubleIdeal P) ≃ₐ[R] ι → TrivSqZeroExt R (σ → R)`.

## Main results

* `MvPolynomial.fst_jetAlgebra`, `MvPolynomial.snd_jetAlgebra`, `MvPolynomial.jetAlgebra_eq`:
  explicit value and partial-derivative components of `jetAlgebra P f`.
* `MvPolynomial.ker_jetAlgebra`, `MvPolynomial.jetAlgebra_surjective`: the kernel of `jetAlgebra P`
  is `RingHom.ker (eval P) ^ 2`, and `jetAlgebra P` is surjective for finite `σ`.
* `MvPolynomial.isCoprime_ker_eval_of_isUnit_sub`, `MvPolynomial.isCoprime_ker_eval`: comaximality
  of point evaluation ideals.
* `MvPolynomial.doubleIdeal_eq_iInf_sq_of_pairwise`, `MvPolynomial.doubleIdeal_eq_iInf_sq`:
  the squared intersection of pairwise comaximal point ideals equals the intersection of their
  squares.
* `MvPolynomial.finrank_quotient_doubleIdeal_of_pairwise`,
  `MvPolynomial.finrank_quotient_doubleIdeal`: the `finrank` of the double-point quotient is
  `Fintype.card ι * (Fintype.card σ + 1)`.

## References

* J.-M. Couveignes, *Enumerating number fields*, Annals of Mathematics 192 (2020), 487–497, §3.
* M. C. Brambilla and G. Ottaviani, *On the Alexander–Hirschowitz Theorem*, J. Pure Appl. Algebra
  212 (2008), 1229–1251 (arXiv:math/0701409v2), §2, Proposition 2.1.
-/

public section

namespace MvPolynomial

section JetAlgebra

variable {σ R : Type*} [CommSemiring R]

/-- The first-jet `R`-algebra homomorphism at a point `P : σ → R`, sending `X j` to
`inl (P j) + inr (Pi.single j 1)` in the trivial square-zero extension `TrivSqZeroExt R (σ → R)`.
Its scalar component is `eval P f` and its infinitesimal component is the gradient
`fun j ↦ eval P (pderiv j f)`. -/
noncomputable def jetAlgebra (P : σ → R) :
    MvPolynomial σ R →ₐ[R] TrivSqZeroExt R (σ → R) := by
  classical
  exact aeval fun j ↦ TrivSqZeroExt.inl (P j) + TrivSqZeroExt.inr (Pi.single j 1)

theorem jetAlgebra_C (P : σ → R) (r : R) :
    jetAlgebra P (C r) = TrivSqZeroExt.inl r := by
  simp [TrivSqZeroExt.algebraMap_eq_inl]

@[simp]
theorem jetAlgebra_X [DecidableEq σ] (P : σ → R) (j : σ) :
    jetAlgebra P (X j) = TrivSqZeroExt.inl (P j) + TrivSqZeroExt.inr (Pi.single j 1) := by
  unfold jetAlgebra
  rw [aeval_X]
  congr 2
  ext k
  by_cases hk : k = j <;> simp [hk]

/-- The scalar component of `jetAlgebra P f` is the evaluation `eval P f`. -/
@[simp]
theorem fst_jetAlgebra (P : σ → R) (f : MvPolynomial σ R) :
    (jetAlgebra P f).fst = eval P f := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [TrivSqZeroExt.algebraMap_eq_inl]
  | add p q hp hq => simp [hp, hq]
  | mul_X p j hp =>
    rw [map_mul, TrivSqZeroExt.fst_mul, hp, map_mul, eval_X]
    simp [jetAlgebra]

/-- The `j`-th infinitesimal coordinate of `jetAlgebra P f` is the partial derivative
`eval P (pderiv j f)`. -/
@[simp]
theorem snd_jetAlgebra (P : σ → R) (f : MvPolynomial σ R) (j : σ) :
    (jetAlgebra P f).snd j = eval P (pderiv j f) := by
  classical
  induction f using MvPolynomial.induction_on with
  | C a => simp [TrivSqZeroExt.algebraMap_eq_inl]
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
    rw [map_mul, TrivSqZeroExt.snd_mul, Pi.add_apply, Pi.smul_apply, Pi.smul_apply,
      MulOpposite.smul_eq_mul_unop, fst_jetAlgebra, fst_jetAlgebra, jetAlgebra_X,
      TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add, hp, eval_X,
      smul_eq_mul, MulOpposite.unop_op]
    obtain rfl | hji := eq_or_ne j i
    · simp [mul_comm]
    · simp [pderiv_X_of_ne (Ne.symm hji), Pi.single_eq_of_ne hji, mul_comm]

/-- Explicit decomposition of `jetAlgebra P f` into its value and partial-derivative parts. -/
theorem jetAlgebra_eq (P : σ → R) (f : MvPolynomial σ R) :
    jetAlgebra P f =
      TrivSqZeroExt.inl (eval P f) + TrivSqZeroExt.inr fun j ↦ eval P (pderiv j f) := by
  ext <;> simp

/-- A polynomial lies in the kernel of `jetAlgebra P` if and only if its value and all first
partial derivatives vanish at `P`. -/
theorem mem_ker_jetAlgebra_iff (P : σ → R) (f : MvPolynomial σ R) :
    f ∈ RingHom.ker (jetAlgebra P) ↔ eval P f = 0 ∧ ∀ j, eval P (pderiv j f) = 0 := by
  rw [RingHom.mem_ker, TrivSqZeroExt.ext_iff]
  simp [_root_.funext_iff]

/-- The evaluation ideal `RingHom.ker (eval P)` is the pullback of the ideal of variables along
the Taylor shift `taylor P`. -/
theorem ker_eval_eq_comap_taylor (P : σ → R) :
    RingHom.ker (eval P) = (idealOfVars σ R).comap (taylor P).toRingHom := by
  ext p
  rw [RingHom.mem_ker, Ideal.mem_comap, ← ker_constantCoeff, RingHom.mem_ker,
    AlgHom.toRingHom_eq_coe, RingHom.coe_coe, constantCoeff_taylor]

end JetAlgebra

section JetAlgebraRing

variable {σ R : Type*} [CommRing R]

private theorem comap_taylor_eq_map_taylor_neg (P : σ → R) (I : Ideal (MvPolynomial σ R)) :
    I.comap (taylor P).toRingHom = I.map (taylor (-P)).toRingHom := by
  refine le_antisymm ?_ ?_
  · intro p hp
    rw [← taylor_neg_taylor P p]
    exact Ideal.mem_map_of_mem _ hp
  · rw [Ideal.map_le_iff_le_comap]
    intro p hp
    change taylor P (taylor (-P) p) ∈ I
    simpa [taylor_taylor] using hp

/-- Over a commutative ring, the `k`-th power of the evaluation ideal at `P` is the pullback of
the `k`-th power of the ideal of variables along the Taylor shift `taylor P`. -/
theorem pow_ker_eval_eq_comap_taylor (P : σ → R) (k : ℕ) :
    RingHom.ker (eval P) ^ k = (idealOfVars σ R ^ k).comap (taylor P).toRingHom := by
  rw [ker_eval_eq_comap_taylor, comap_taylor_eq_map_taylor_neg, ← Ideal.map_pow,
    ← comap_taylor_eq_map_taylor_neg]

/-- The kernel of `jetAlgebra P` is the square of the evaluation ideal `RingHom.ker (eval P)`.
This holds over any commutative ring and in arbitrarily many variables. -/
theorem ker_jetAlgebra (P : σ → R) :
    RingHom.ker (jetAlgebra P) = RingHom.ker (eval P) ^ 2 := by
  ext f
  rw [mem_ker_jetAlgebra_iff, pow_ker_eval_eq_comap_taylor, Ideal.mem_comap,
    AlgHom.toRingHom_eq_coe, RingHom.coe_coe, mem_pow_idealOfVars_iff']
  constructor
  · rintro ⟨h0, h1⟩ m hm
    obtain hdeg0 | hdeg1 : m.degree = 0 ∨ m.degree = 1 := by omega
    · rw [(Finsupp.degree_eq_zero_iff m).1 hdeg0, ← constantCoeff_eq, constantCoeff_taylor, h0]
    · obtain ⟨j, rfl⟩ := (Finsupp.sum_eq_one_iff m).1
        (by simpa [Finsupp.degree_apply, Finsupp.sum] using hdeg1)
      rw [coeff_single_one_taylor, h1 j]
  · intro h
    refine ⟨?_, fun j ↦ ?_⟩
    · rw [← constantCoeff_taylor, constantCoeff_eq]
      exact h 0 (by simp)
    · rw [← coeff_single_one_taylor]
      exact h (Finsupp.single j 1) (by simp)

/-- For finitely many variables over a commutative ring, the first-jet homomorphism `jetAlgebra P`
is surjective: constants and linear forms `X j - C (P j)` span the target. -/
theorem jetAlgebra_surjective [Finite σ] (P : σ → R) :
    Function.Surjective (jetAlgebra P) := by
  cases nonempty_fintype σ
  intro x
  refine ⟨C x.fst + ∑ j, C (x.snd j) * (X j - C (P j)), ?_⟩
  ext i
  · rw [fst_jetAlgebra]
    simp
  · rw [snd_jetAlgebra, map_add, map_sum, pderiv_C, zero_add]
    simp only [pderiv_mul, pderiv_C, zero_mul, zero_add, map_sub, sub_zero, map_sum, map_mul,
      eval_C]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      simp [pderiv_X_of_ne hji]
    · intro hi
      exact absurd (Finset.mem_univ i) hi

/-- For finitely many variables over a commutative ring, the quotient by `RingHom.ker (eval P) ^ 2`
is isomorphic as an `R`-algebra to the trivial square-zero extension `TrivSqZeroExt R (σ → R)`. -/
noncomputable def jetAlgebraEquiv [Finite σ] (P : σ → R) :
    (MvPolynomial σ R ⧸ RingHom.ker (eval P) ^ 2) ≃ₐ[R] TrivSqZeroExt R (σ → R) :=
  (Ideal.quotientEquivAlgOfEq R (ker_jetAlgebra P).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective (jetAlgebra_surjective P))

@[simp]
theorem jetAlgebraEquiv_mk [Finite σ] (P : σ → R) (f : MvPolynomial σ R) :
    jetAlgebraEquiv P (Ideal.Quotient.mk _ f) = jetAlgebra P f := by
  simp [jetAlgebraEquiv]

/-- If two points `P, Q : σ → R` differ by a unit in some coordinate, their evaluation ideals are
comaximal. -/
theorem isCoprime_ker_eval_of_isUnit_sub {P Q : σ → R} {j : σ} (h : IsUnit (P j - Q j)) :
    IsCoprime (RingHom.ker (eval P)) (RingHom.ker (eval Q)) := by
  obtain ⟨u, hu⟩ := h
  refine Ideal.isCoprime_iff_exists.2
    ⟨-C ((u⁻¹ : Rˣ) : R) * (X j - C (P j)), by simp,
      C ((u⁻¹ : Rˣ) : R) * (X j - C (Q j)), by simp, ?_⟩
  calc
    -C ((u⁻¹ : Rˣ) : R) * (X j - C (P j)) + C ((u⁻¹ : Rˣ) : R) * (X j - C (Q j))
      = C (((u⁻¹ : Rˣ) : R) * (P j - Q j)) := by
        rw [map_mul, map_sub]
        ring
    _ = 1 := by rw [← hu, Units.inv_mul, map_one]

/-- Over a field, the evaluation ideals of two distinct points are comaximal. -/
theorem isCoprime_ker_eval {k : Type*} [Field k] {P Q : σ → k} (hPQ : P ≠ Q) :
    IsCoprime (RingHom.ker (eval P)) (RingHom.ker (eval Q)) := by
  obtain ⟨j, hj⟩ := Function.ne_iff.1 hPQ
  exact isCoprime_ker_eval_of_isUnit_sub (IsUnit.mk0 _ (sub_ne_zero.2 hj))

end JetAlgebraRing

section DoubleIdeal

variable {σ ι κ R : Type*}

/-- The ideal of polynomials vanishing to order at least two on a family of points `P : ι → σ → R`,
defined as the square of the intersection of the point evaluation ideals. -/
noncomputable def doubleIdeal [CommSemiring R] (P : ι → σ → R) : Ideal (MvPolynomial σ R) :=
  (⨅ i, RingHom.ker (eval (P i))) ^ 2

theorem doubleIdeal_def [CommSemiring R] (P : ι → σ → R) :
    doubleIdeal P = (⨅ i, RingHom.ker (eval (P i))) ^ 2 := by
  rw [doubleIdeal]

/-- The squared intersection ideal is always contained in the intersection of the squared point
ideals. -/
theorem doubleIdeal_le_iInf_sq [CommSemiring R] (P : ι → σ → R) :
    doubleIdeal P ≤ ⨅ i, RingHom.ker (eval (P i)) ^ 2 :=
  le_iInf fun i ↦ Ideal.pow_right_mono (iInf_le _ i) 2

@[simp]
theorem doubleIdeal_isEmpty [CommSemiring R] [IsEmpty ι] (P : ι → σ → R) :
    doubleIdeal P = ⊤ := by
  simp [doubleIdeal]

@[simp]
theorem doubleIdeal_unique [CommSemiring R] [Unique ι] (P : ι → σ → R) :
    doubleIdeal P = RingHom.ker (eval (P default)) ^ 2 := by
  simp [doubleIdeal]

/-- Reindexing a point tuple along an equivalence leaves `doubleIdeal` unchanged. -/
theorem doubleIdeal_comp_equiv [CommSemiring R] (P : ι → σ → R) (e : κ ≃ ι) :
    doubleIdeal (P ∘ e) = doubleIdeal P := by
  rw [doubleIdeal, doubleIdeal]
  congr 1
  exact e.iInf_comp (g := fun i ↦ RingHom.ker (eval (P i)))

section CommRing

variable [CommRing R]

private theorem pairwise_isCoprime_sq {I : ι → Ideal (MvPolynomial σ R)}
    (hI : Pairwise (Function.onFun IsCoprime I)) :
    Pairwise (Function.onFun IsCoprime fun i ↦ I i ^ 2) :=
  fun _ _ hij ↦ (hI hij).pow

/-- For a finite family of points whose evaluation ideals are pairwise comaximal, `doubleIdeal P`
equals the intersection of the squared point ideals. -/
theorem doubleIdeal_eq_iInf_sq_of_pairwise [Finite ι] {P : ι → σ → R}
    (hP : Pairwise (Function.onFun IsCoprime fun i ↦ RingHom.ker (eval (P i)))) :
    doubleIdeal P = ⨅ i, RingHom.ker (eval (P i)) ^ 2 := by
  cases nonempty_fintype ι
  have h1 : ∏ i : ι, RingHom.ker (eval (P i)) = ⨅ i, RingHom.ker (eval (P i)) := by
    simpa using Ideal.prod_eq_iInf_of_pairwise_isCoprime (s := Finset.univ)
      (J := fun i ↦ RingHom.ker (eval (P i))) fun i _ j _ hij ↦ hP hij
  have h2 : ∏ i : ι, RingHom.ker (eval (P i)) ^ 2 = ⨅ i, RingHom.ker (eval (P i)) ^ 2 := by
    simpa using Ideal.prod_eq_iInf_of_pairwise_isCoprime (s := Finset.univ)
      (J := fun i ↦ RingHom.ker (eval (P i)) ^ 2) fun i _ j _ hij ↦ (hP hij).pow
  rw [doubleIdeal, ← h1, ← Finset.prod_pow, h2]

/-- A polynomial lies in `doubleIdeal P` (for pairwise comaximal point ideals) if and only if its
value and all first partial derivatives vanish at every point `P i`. -/
theorem mem_doubleIdeal_iff_of_pairwise [Finite ι] {P : ι → σ → R}
    (hP : Pairwise (Function.onFun IsCoprime fun i ↦ RingHom.ker (eval (P i))))
    {f : MvPolynomial σ R} :
    f ∈ doubleIdeal P ↔ ∀ i, eval (P i) f = 0 ∧ ∀ j, eval (P i) (pderiv j f) = 0 := by
  rw [doubleIdeal_eq_iInf_sq_of_pairwise hP, Ideal.mem_iInf]
  simp_rw [← ker_jetAlgebra, mem_ker_jetAlgebra_iff]

/-- **Chinese remainder for double points over a commutative ring.** When `σ` and `ι` are finite
and the point evaluation ideals are pairwise comaximal, the quotient
`MvPolynomial σ R ⧸ doubleIdeal P` is isomorphic as an `R`-algebra to the product of first-jet
algebras `ι → TrivSqZeroExt R (σ → R)`. -/
noncomputable def doublePointQuotientEquivOfPairwise [Finite σ] [Finite ι] {P : ι → σ → R}
    (hP : Pairwise (Function.onFun IsCoprime fun i ↦ RingHom.ker (eval (P i)))) :
    (MvPolynomial σ R ⧸ doubleIdeal P) ≃ₐ[R] (ι → TrivSqZeroExt R (σ → R)) :=
  let crt : (MvPolynomial σ R ⧸ ⨅ i, RingHom.ker (eval (P i)) ^ 2) ≃ₐ[R]
      ((i : ι) → MvPolynomial σ R ⧸ RingHom.ker (eval (P i)) ^ 2) :=
    AlgEquiv.ofRingEquiv
      (f := Ideal.quotientInfRingEquivPiQuotient _ (pairwise_isCoprime_sq hP))
      fun r ↦ by
        funext i
        exact Ideal.quotientInfRingEquivPiQuotient_mk_apply (pairwise_isCoprime_sq hP) (C r) i
  (Ideal.quotientEquivAlgOfEq R (doubleIdeal_eq_iInf_sq_of_pairwise hP)).trans <|
    crt.trans <| AlgEquiv.piCongrRight fun i ↦ jetAlgebraEquiv (P i)

@[simp]
theorem doublePointQuotientEquivOfPairwise_mk [Finite σ] [Finite ι] {P : ι → σ → R}
    (hP : Pairwise (Function.onFun IsCoprime fun i ↦ RingHom.ker (eval (P i))))
    (f : MvPolynomial σ R) (i : ι) :
    doublePointQuotientEquivOfPairwise hP (Ideal.Quotient.mk _ f) i = jetAlgebra (P i) f := by
  unfold doublePointQuotientEquivOfPairwise
  simp only [AlgEquiv.trans_apply, Ideal.quotientEquivAlgOfEq_mk, AlgEquiv.piCongrRight_apply,
    AlgEquiv.ofRingEquiv_apply]
  rw [Ideal.quotientInfRingEquivPiQuotient_mk_apply (pairwise_isCoprime_sq hP) f i,
    jetAlgebraEquiv_mk]

/-- Reindexing a point tuple along an equivalence commutes with
`doublePointQuotientEquivOfPairwise`. -/
theorem doublePointQuotientEquivOfPairwise_comp_equiv [Finite σ] [Finite ι] [Finite κ]
    {P : ι → σ → R}
    (hP : Pairwise (Function.onFun IsCoprime fun i ↦ RingHom.ker (eval (P i)))) (e : κ ≃ ι)
    (x : MvPolynomial σ R ⧸ doubleIdeal (P ∘ e)) (j : κ) :
    doublePointQuotientEquivOfPairwise (P := P ∘ e) (fun _ _ h ↦ hP (e.injective.ne h)) x j =
      doublePointQuotientEquivOfPairwise hP
        (Ideal.quotientEquivAlgOfEq R (doubleIdeal_comp_equiv P e) x) (e j) := by
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact (doublePointQuotientEquivOfPairwise_mk _ f j).trans (by simp)

/-- The `finrank` of the double-point quotient over a commutative ring with the strong rank
condition is `Fintype.card ι * (Fintype.card σ + 1)`. -/
theorem finrank_quotient_doubleIdeal_of_pairwise [StrongRankCondition R] [Fintype σ] [Fintype ι]
    {P : ι → σ → R}
    (hP : Pairwise (Function.onFun IsCoprime fun i ↦ RingHom.ker (eval (P i)))) :
    Module.finrank R (MvPolynomial σ R ⧸ doubleIdeal P) =
      Fintype.card ι * (Fintype.card σ + 1) := by
  rw [(doublePointQuotientEquivOfPairwise hP).toLinearEquiv.finrank_eq, Module.finrank_pi_fintype]
  simp [TrivSqZeroExt.finrank_eq, Module.finrank_self, add_comm]

end CommRing

section Field

variable {k : Type*} [Field k]

/-- Over a field, for a finite injective tuple of points `P`, `doubleIdeal P` equals the
intersection of the squared point ideals `RingHom.ker (eval (P i)) ^ 2`. -/
theorem doubleIdeal_eq_iInf_sq [Finite ι] {P : ι → σ → k} (hP : Function.Injective P) :
    doubleIdeal P = ⨅ i, RingHom.ker (eval (P i)) ^ 2 :=
  doubleIdeal_eq_iInf_sq_of_pairwise fun _ _ hij ↦ isCoprime_ker_eval (hP.ne hij)

/-- Over a field, for a finite injective tuple `P`, a polynomial lies in `doubleIdeal P` if and
only if its value and all first partial derivatives vanish at every `P i`. -/
theorem mem_doubleIdeal_iff [Finite ι] {P : ι → σ → k} (hP : Function.Injective P)
    {f : MvPolynomial σ k} :
    f ∈ doubleIdeal P ↔ ∀ i, eval (P i) f = 0 ∧ ∀ j, eval (P i) (pderiv j f) = 0 :=
  mem_doubleIdeal_iff_of_pairwise fun _ _ hij ↦ isCoprime_ker_eval (hP.ne hij)

/-- **Double-point quotient comparison.** Over a field `k`, for finitely many variables `σ` and a
finite injective tuple `P : ι → σ → k`, the nonreduced quotient `MvPolynomial σ k ⧸ doubleIdeal P`
is isomorphic as a `k`-algebra to the product of first-jet algebras
`ι → TrivSqZeroExt k (σ → k)`, sending the class of `f` to `fun i ↦ jetAlgebra (P i) f`. -/
noncomputable def doublePointQuotientEquiv [Finite σ] [Finite ι] {P : ι → σ → k}
    (hP : Function.Injective P) :
    (MvPolynomial σ k ⧸ doubleIdeal P) ≃ₐ[k] (ι → TrivSqZeroExt k (σ → k)) :=
  doublePointQuotientEquivOfPairwise fun _ _ hij ↦ isCoprime_ker_eval (hP.ne hij)

@[simp]
theorem doublePointQuotientEquiv_mk [Finite σ] [Finite ι] {P : ι → σ → k}
    (hP : Function.Injective P) (f : MvPolynomial σ k) (i : ι) :
    doublePointQuotientEquiv hP (Ideal.Quotient.mk _ f) i = jetAlgebra (P i) f :=
  doublePointQuotientEquivOfPairwise_mk _ f i

/-- Reindexing a tuple along an equivalence commutes with `doublePointQuotientEquiv`. -/
theorem doublePointQuotientEquiv_comp_equiv [Finite σ] [Finite ι] [Finite κ]
    {P : ι → σ → k} (hP : Function.Injective P) (e : κ ≃ ι)
    (x : MvPolynomial σ k ⧸ doubleIdeal (P ∘ e)) (j : κ) :
    doublePointQuotientEquiv (hP.comp e.injective) x j =
      doublePointQuotientEquiv hP
        (Ideal.quotientEquivAlgOfEq k (doubleIdeal_comp_equiv P e) x) (e j) :=
  doublePointQuotientEquivOfPairwise_comp_equiv _ e x j

/-- **Length of distinct double points.** Over a field `k`, the double-point quotient at
`Fintype.card ι` distinct points in `Fintype.card σ`-dimensional affine space has dimension
`Fintype.card ι * (Fintype.card σ + 1)`. -/
theorem finrank_quotient_doubleIdeal [Fintype σ] [Fintype ι] {P : ι → σ → k}
    (hP : Function.Injective P) :
    Module.finrank k (MvPolynomial σ k ⧸ doubleIdeal P) =
      Fintype.card ι * (Fintype.card σ + 1) :=
  finrank_quotient_doubleIdeal_of_pairwise fun _ _ hij ↦ isCoprime_ker_eval (hP.ne hij)

end Field

end DoubleIdeal

/-! ### Examples -/

/-- At the origin, `X 0` maps to `(0, e₀)` and `X 0 ^ 2` maps to `0` in the square-zero first-jet
algebra. -/
example {R : Type*} [CommSemiring R] :
    jetAlgebra (0 : Fin 2 → R) (X 0) = TrivSqZeroExt.inr (Pi.single 0 1) ∧
    jetAlgebra (0 : Fin 2 → R) (X 0 ^ 2) = 0 := by
  refine ⟨by simp, ?_⟩
  rw [map_pow, jetAlgebra_X]
  simp [sq, TrivSqZeroExt.inr_mul_inr]

/-- For the two distinct points `0` and `1` on the affine line over `ℚ`, the class of
`X 0 * (X 0 - 1)` in the double-point quotient is nonzero, while its square is zero: the quotient
retains its nonreduced structure. -/
example :
    let P : Fin 2 → Fin 1 → ℚ := ![fun _ ↦ 0, fun _ ↦ 1]
    let f : MvPolynomial (Fin 1) ℚ := X 0 * (X 0 - 1)
    Ideal.Quotient.mk (doubleIdeal P) f ≠ 0 ∧ Ideal.Quotient.mk (doubleIdeal P) f ^ 2 = 0 := by
  intro P f
  have hP : Function.Injective P := by
    intro i j hij
    have h0 := congrFun hij 0
    fin_cases i <;> fin_cases j <;> simp [P] at h0 ⊢
  refine ⟨?_, ?_⟩
  · intro h0
    have hmem : f ∈ doubleIdeal P := Ideal.Quotient.eq_zero_iff_mem.1 h0
    have hd := ((mem_doubleIdeal_iff hP).1 hmem 0).2 0
    simp [f, P] at hd
  · rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem, mem_doubleIdeal_iff hP]
    intro i
    fin_cases i <;> simp [f, P, sq]

/-- Over `ℤ`, the distinct points `0` and `2` on the affine line do not have comaximal evaluation
ideals: their sum is contained in the ideal `(X 0, 2)`, which is proper. -/
example :
    ¬ IsCoprime (RingHom.ker (eval (fun _ : Fin 1 ↦ (0 : ℤ))))
      (RingHom.ker (eval (fun _ : Fin 1 ↦ (2 : ℤ)))) := by
  intro h
  obtain ⟨a, ha, b, hb, hab⟩ := Ideal.isCoprime_iff_exists.1 h
  let φ : ℤ →+* ZMod 2 := Int.castRingHom (ZMod 2)
  have h02 : (φ ∘ fun _ : Fin 1 ↦ (0 : ℤ)) = φ ∘ fun _ : Fin 1 ↦ (2 : ℤ) := by
    funext _
    change (0 : ZMod 2) = ((2 : ℤ) : ZMod 2)
    decide
  have hmod : eval (φ ∘ fun _ : Fin 1 ↦ (0 : ℤ)) (map φ (a + b)) = 1 := by
    rw [hab, map_one, map_one]
  have ha0 : eval (φ ∘ fun _ : Fin 1 ↦ (0 : ℤ)) (map φ a) = 0 := by
    rw [eval_map, ← eval₂_comp, RingHom.mem_ker.1 ha, map_zero]
  have hb0 : eval (φ ∘ fun _ : Fin 1 ↦ (0 : ℤ)) (map φ b) = 0 := by
    rw [h02, eval_map, ← eval₂_comp, RingHom.mem_ker.1 hb, map_zero]
  rw [map_add, map_add, ha0, hb0, add_zero] at hmod
  exact zero_ne_one hmod

/-- The empty point tuple has zero-dimensional double-point quotient. -/
example {k : Type*} [Field k] (r : ℕ) (P : Fin 0 → Fin r → k) :
    Module.finrank k (MvPolynomial (Fin r) k ⧸ doubleIdeal P) = 0 := by
  simpa using finrank_quotient_doubleIdeal (P := P) (Function.injective_of_subsingleton P)

end MvPolynomial
