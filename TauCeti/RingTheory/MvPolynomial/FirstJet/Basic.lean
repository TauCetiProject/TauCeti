/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.InvariantBasisNumber
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.MvPolynomial.Ideal
public import TauCeti.RingTheory.MvPolynomial.OrderAt
import Mathlib.Algebra.Algebra.Pi
import Mathlib.Data.Finsupp.Weight
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Pi
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.Ideal.Operations
import TauCeti.Algebra.TrivSqZeroExt
import TauCeti.RingTheory.MvPolynomial.Ideal

/-!
# First-jet algebras and double-point ideals

Given a point `P : σ → R` over a commutative semiring `R`, the first-jet algebra homomorphism
`MvPolynomial.firstJet P : MvPolynomial σ R →ₐ[R] TrivSqZeroExt R (σ → R)` sends a polynomial `f`
to its value `eval P f` in the scalar part and its gradient `fun j ↦ eval P (pderiv j f)` in the
square-zero infinitesimal part. The Leibniz rule for partial derivatives turns this into an
`R`-algebra homomorphism; when `σ` has decidable equality, it is evaluation at the first-order
thickening `P + ε` (`MvPolynomial.firstJet_eq_aeval`).

Over a commutative ring `R`, translating to the origin via `MvPolynomial.taylor P` identifies the
kernel of `firstJet P` with `(RingHom.ker (eval P)) ^ 2` in every characteristic and for every
variable type `σ` (`MvPolynomial.ker_firstJet`). When `σ` is finite, `firstJet P` is already
surjective on polynomials of total degree at most `1`.

For a family of points `P : ι → σ → R`, the double-point ideal `MvPolynomial.doublePointIdeal P`
is `(⨅ i, RingHom.ker (eval (P i))) ^ 2`. When `ι` is finite and distinct points have a unit
coordinate difference (in particular, when `P` is injective over a field), the point ideals and
their squares are pairwise comaximal, so `doublePointIdeal P = ⨅ i, RingHom.ker (eval (P i)) ^ 2`,
the product jet map `MvPolynomial.piFirstJet P` is surjective with kernel `doublePointIdeal P`,
and the quotient `MvPolynomial σ R ⧸ doublePointIdeal P` is canonically isomorphic as an
`R`-algebra to `ι → TrivSqZeroExt R (σ → R)` (`MvPolynomial.doublePointQuotientEquiv`), of rank
`card ι * (card σ + 1)`.

## Main definitions

* `MvPolynomial.firstJet`: the first-jet `R`-algebra homomorphism
  `MvPolynomial σ R →ₐ[R] TrivSqZeroExt R (σ → R)` at a point `P : σ → R`.
* `MvPolynomial.doublePointIdeal`: the ideal `(⨅ i, RingHom.ker (eval (P i))) ^ 2` of the
  double-point subscheme supported at `P : ι → σ → R`.
* `MvPolynomial.piFirstJet`: the product first-jet `R`-algebra homomorphism
  `MvPolynomial σ R →ₐ[R] (ι → TrivSqZeroExt R (σ → R))`.
* `MvPolynomial.doublePointQuotientEquiv`: the `R`-algebra equivalence
  `(MvPolynomial σ R ⧸ doublePointIdeal P) ≃ₐ[R] (ι → TrivSqZeroExt R (σ → R))` for a finite
  family of points with pairwise unit coordinate differences.

## Main results

* `MvPolynomial.firstJet_eq_aeval`: `firstJet P` is algebra evaluation at `P + ε`.
* `MvPolynomial.exists_totalDegree_le_one_firstJet_eq`, `MvPolynomial.firstJet_surjective`:
  in finitely many variables over a commutative ring, `firstJet P` is surjective already on
  polynomials of total degree at most `1`.
* `MvPolynomial.ker_firstJet`: over any commutative ring and in every characteristic,
  `RingHom.ker (firstJet P) = RingHom.ker (eval P) ^ 2`.
* `MvPolynomial.isCoprime_ker_eval`: two points differing by a unit in some coordinate have
  comaximal evaluation ideals.
* `MvPolynomial.doublePointIdeal_eq_iInf_sq`: for finitely many points with pairwise unit
  coordinate differences, `doublePointIdeal P = ⨅ i, RingHom.ker (eval (P i)) ^ 2`.
* `MvPolynomial.ker_piFirstJet`, `MvPolynomial.piFirstJet_surjective`: kernel and surjectivity of
  `piFirstJet P`.
* `MvPolynomial.finrank_quotient_doublePointIdeal`: the quotient by `doublePointIdeal P` has rank
  `Fintype.card ι * (Fintype.card σ + 1)`.

## References

* M. C. Brambilla and G. Ottaviani, *On the Alexander–Hirschowitz theorem*, J. Pure Appl. Algebra
  212 (2008), 1229–1251, §§1–2.
* J.-M. Couveignes, *Enumerating number fields*, Ann. of Math. (2) 192 (2020), 487–497, §3,
  pp. 491–493.
-/

public section

namespace MvPolynomial

variable {σ ι ι' R k : Type*}

section CommSemiring

variable [CommSemiring R]

/-- The first-jet `R`-algebra homomorphism at a point `P : σ → R`, sending a polynomial `f` to its
value `eval P f` and gradient `fun j ↦ eval P (pderiv j f)` in the trivial square-zero extension
`TrivSqZeroExt R (σ → R)`. -/
noncomputable def firstJet (P : σ → R) :
    MvPolynomial σ R →ₐ[R] TrivSqZeroExt R (σ → R) where
  toFun f := TrivSqZeroExt.inl (eval P f) + TrivSqZeroExt.inr fun j ↦ eval P (pderiv j f)
  map_one' := by ext <;> simp
  map_mul' f g := by
    ext
    · simp
    · simp [TrivSqZeroExt.snd_mul, smul_eq_mul, Derivation.leibniz]
  map_zero' := by ext <;> simp
  map_add' f g := by ext <;> simp
  commutes' r := by ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]

@[simp]
theorem fst_firstJet (P : σ → R) (f : MvPolynomial σ R) :
    (firstJet P f).fst = eval P f := by
  simp [firstJet]

@[simp]
theorem snd_firstJet (P : σ → R) (f : MvPolynomial σ R) (j : σ) :
    (firstJet P f).snd j = eval P (pderiv j f) := by
  simp [firstJet]

theorem firstJet_C (P : σ → R) (r : R) :
    firstJet P (C r) = TrivSqZeroExt.inl r := by
  ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]

@[simp]
theorem firstJet_X [DecidableEq σ] (P : σ → R) (j : σ) :
    firstJet P (X j) = TrivSqZeroExt.inl (P j) + TrivSqZeroExt.inr (Pi.single j 1) := by
  ext
  · simp
  · simp [pderiv_X, Pi.single_apply, eq_comm]

/-- `firstJet P` is algebra evaluation at the first-order thickening `j ↦ P j + ε_j`. -/
theorem firstJet_eq_aeval [DecidableEq σ] (P : σ → R) :
    firstJet P = aeval fun j ↦ TrivSqZeroExt.inl (P j) + TrivSqZeroExt.inr (Pi.single j 1) :=
  MvPolynomial.algHom_ext fun j ↦ by simp

/-- Translating `f` to the origin by `taylor P` turns the first jet at `P` into the first jet at
`0`. -/
@[simp]
theorem firstJet_zero_taylor (P : σ → R) (f : MvPolynomial σ R) :
    firstJet 0 (taylor P f) = firstJet P f := by
  ext <;> simp [eval_zero]

/-- A polynomial lies in the kernel of `firstJet P` if and only if both it and all of its first
partial derivatives vanish at `P`. -/
theorem mem_ker_firstJet_iff (P : σ → R) (f : MvPolynomial σ R) :
    f ∈ RingHom.ker (firstJet P) ↔ eval P f = 0 ∧ ∀ j, eval P (pderiv j f) = 0 := by
  simp [RingHom.mem_ker, TrivSqZeroExt.ext_iff, funext_iff]

/-- The double-point ideal of a family of points `P : ι → σ → R`: the square of the ideal of
polynomials vanishing at every `P i`. -/
noncomputable def doublePointIdeal (P : ι → σ → R) : Ideal (MvPolynomial σ R) :=
  (⨅ i, RingHom.ker (eval (P i))) ^ 2

theorem doublePointIdeal_def (P : ι → σ → R) :
    doublePointIdeal P = (⨅ i, RingHom.ker (eval (P i))) ^ 2 := (rfl)

/-- Reindexing the point family along an equivalence leaves `doublePointIdeal` unchanged. -/
@[simp]
theorem doublePointIdeal_comp_equiv (P : ι → σ → R) (e : ι' ≃ ι) :
    doublePointIdeal (P ∘ e) = doublePointIdeal P := by
  simp only [doublePointIdeal_def, Function.comp_apply]
  congr 1
  exact e.iInf_congr fun _ ↦ rfl

/-- The double-point ideal of an empty family of points is the unit ideal. -/
@[simp]
theorem doublePointIdeal_eq_top_of_isEmpty [IsEmpty ι] (P : ι → σ → R) :
    doublePointIdeal P = ⊤ := by
  simp [doublePointIdeal_def]

/-- The product first-jet algebra homomorphism at a family of points `P : ι → σ → R`. -/
noncomputable def piFirstJet (P : ι → σ → R) :
    MvPolynomial σ R →ₐ[R] (ι → TrivSqZeroExt R (σ → R)) :=
  AlgHom.pi fun i ↦ firstJet (P i)

@[simp]
theorem piFirstJet_apply (P : ι → σ → R) (f : MvPolynomial σ R) (i : ι) :
    piFirstJet P f i = firstJet (P i) f := (rfl)

/-- Reindexing the point family along `g : ι' → ι` pulls back `piFirstJet` along `g`. -/
theorem piFirstJet_comp (P : ι → σ → R) (g : ι' → ι) (f : MvPolynomial σ R) (i' : ι') :
    piFirstJet (P ∘ g) f i' = piFirstJet P f (g i') := (rfl)

/-- A polynomial lies in the kernel of `piFirstJet P` if and only if both it and all of its first
partial derivatives vanish at every `P i`. -/
theorem mem_ker_piFirstJet_iff (P : ι → σ → R) (f : MvPolynomial σ R) :
    f ∈ RingHom.ker (piFirstJet P) ↔
      ∀ i, eval (P i) f = 0 ∧ ∀ j, eval (P i) (pderiv j f) = 0 := by
  simp [RingHom.mem_ker, _root_.funext_iff, TrivSqZeroExt.ext_iff]

end CommSemiring

section CommRing

variable [CommRing R]

/-- In finitely many variables over a commutative ring, every first-jet datum at `P` is realized by
a polynomial of total degree at most `1`. -/
theorem exists_totalDegree_le_one_firstJet_eq [Finite σ] (P : σ → R)
    (z : TrivSqZeroExt R (σ → R)) :
    ∃ f : MvPolynomial σ R, f.totalDegree ≤ 1 ∧ firstJet P f = z := by
  classical
  cases nonempty_fintype σ
  refine ⟨C z.fst + ∑ j, C (z.snd j) * (X j - C (P j)), ?_, ?_⟩
  · refine (totalDegree_add _ _).trans (max_le (by simp) ?_)
    refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun j _ ↦ ?_)
    refine (totalDegree_mul _ _).trans ?_
    rw [totalDegree_C, zero_add]
    exact (totalDegree_sub _ _).trans
      (max_le ((totalDegree_monomial_le (Finsupp.single j 1) (1 : R)).trans_eq (by simp))
        (by simp))
  · refine TrivSqZeroExt.ext ?_ (_root_.funext fun j ↦ ?_)
    · rw [fst_firstJet]
      simp
    · rw [snd_firstJet]
      simp [map_sum, Derivation.leibniz, pderiv_X, Pi.single_apply]

/-- In finitely many variables over a commutative ring, the local first-jet homomorphism is
surjective. -/
theorem firstJet_surjective [Finite σ] (P : σ → R) :
    Function.Surjective (firstJet P) :=
  fun z ↦ let ⟨f, _, hf⟩ := exists_totalDegree_le_one_firstJet_eq P z; ⟨f, hf⟩

/-- The evaluation ideal at `P` is the image of `idealOfVars σ R` under the inverse Taylor shift
`taylor (-P)`. -/
theorem ker_eval_eq_map_taylor_neg (P : σ → R) :
    RingHom.ker (eval P) = (idealOfVars σ R).map (taylor (-P)) := by
  have hsurj : Function.Surjective (taylor (-P) : MvPolynomial σ R →ₐ[R] MvPolynomial σ R) :=
    fun g ↦ ⟨taylor P g, taylor_neg_taylor P g⟩
  ext f
  rw [Ideal.mem_map_iff_of_surjective _ hsurj, RingHom.mem_ker, ← constantCoeff_taylor P,
    ← RingHom.mem_ker, ker_constantCoeff]
  exact ⟨fun hf ↦ ⟨taylor P f, hf, taylor_neg_taylor P f⟩,
    fun ⟨g, hg, hgf⟩ ↦ by rw [← hgf, taylor_taylor, add_neg_cancel, taylor_zero]; exact hg⟩

/-- A polynomial lies in `(RingHom.ker (eval P)) ^ k` if and only if its Taylor shift at `P` lies
in `(idealOfVars σ R) ^ k`. -/
theorem mem_pow_ker_eval_iff (P : σ → R) (k : ℕ) (f : MvPolynomial σ R) :
    f ∈ RingHom.ker (eval P) ^ k ↔ taylor P f ∈ idealOfVars σ R ^ k := by
  have hsurj : Function.Surjective (taylor (-P) : MvPolynomial σ R →ₐ[R] MvPolynomial σ R) :=
    fun g ↦ ⟨taylor P g, taylor_neg_taylor P g⟩
  rw [ker_eval_eq_map_taylor_neg, ← Ideal.map_pow, Ideal.mem_map_iff_of_surjective _ hsurj]
  exact ⟨fun ⟨g, hg, hgf⟩ ↦ by rw [← hgf, taylor_taylor, add_neg_cancel, taylor_zero]; exact hg,
    fun hf ↦ ⟨taylor P f, hf, taylor_neg_taylor P f⟩⟩

/-- **Kernel of the local first-jet algebra homomorphism.** Over any commutative ring and in every
characteristic, the kernel of `firstJet P` is `(RingHom.ker (eval P)) ^ 2`. -/
theorem ker_firstJet (P : σ → R) :
    RingHom.ker (firstJet P) = RingHom.ker (eval P) ^ 2 := by
  ext f
  rw [mem_ker_firstJet_iff, mem_pow_ker_eval_iff, mem_pow_idealOfVars_iff']
  constructor
  · rintro ⟨h0, h1⟩ e he
    interval_cases hd : e.degree
    · rw [Finsupp.degree_eq_zero_iff] at hd
      rw [hd, ← constantCoeff_eq, constantCoeff_taylor, h0]
    · have he1 : e ∈ Set.range (fun a : σ ↦ Finsupp.single a 1) := by
        rw [Finsupp.range_single_one]
        exact hd
      obtain ⟨j, rfl⟩ := he1
      rw [coeff_single_one_taylor, h1 j]
  · intro h
    refine ⟨?_, fun j ↦ ?_⟩
    · simpa [← constantCoeff_eq, constantCoeff_taylor] using h 0 (by simp)
    · simpa [coeff_single_one_taylor] using h (Finsupp.single j 1) (by simp)

/-- If two points `P, Q : σ → R` differ by a unit in some coordinate, their evaluation ideals are
comaximal. -/
theorem isCoprime_ker_eval {P Q : σ → R} (h : ∃ j, IsUnit (P j - Q j)) :
    IsCoprime (RingHom.ker (eval P)) (RingHom.ker (eval Q)) := by
  obtain ⟨j, u, hu⟩ := h
  rw [Ideal.isCoprime_iff_sup_eq, Ideal.eq_top_iff_one]
  have hP : C (↑u⁻¹ : R) * (X j - C (P j)) ∈ RingHom.ker (eval P) := by
    simp [RingHom.mem_ker]
  have hQ : C (↑u⁻¹ : R) * (X j - C (Q j)) ∈ RingHom.ker (eval Q) := by
    simp [RingHom.mem_ker]
  have h1 : (1 : MvPolynomial σ R) =
      C (↑u⁻¹ : R) * (X j - C (Q j)) - C (↑u⁻¹ : R) * (X j - C (P j)) := by
    rw [← mul_sub, sub_sub_sub_cancel_left, ← map_sub, ← hu, ← map_mul, Units.inv_mul, map_one]
  rw [h1]
  exact Submodule.sub_mem _ (Ideal.mem_sup_right hQ) (Ideal.mem_sup_left hP)

/-- For finitely many points with pairwise unit coordinate differences, the double-point ideal
equals the intersection of the squares of the individual evaluation ideals. -/
theorem doublePointIdeal_eq_iInf_sq [Finite ι] {P : ι → σ → R}
    (hP : Pairwise fun i j ↦ ∃ s, IsUnit (P i s - P j s)) :
    doublePointIdeal P = ⨅ i, RingHom.ker (eval (P i)) ^ 2 := by
  classical
  cases nonempty_fintype ι
  have hcop : Set.Pairwise ((Finset.univ : Finset ι) : Set ι) fun i j ↦
      IsCoprime (RingHom.ker (eval (P i))) (RingHom.ker (eval (P j))) :=
    fun _ _ _ _ hij ↦ isCoprime_ker_eval (hP hij)
  have hcop2 : Set.Pairwise ((Finset.univ : Finset ι) : Set ι) fun i j ↦
      IsCoprime (RingHom.ker (eval (P i)) ^ 2) (RingHom.ker (eval (P j)) ^ 2) :=
    fun _ _ _ _ hij ↦ (isCoprime_ker_eval (hP hij)).pow
  have h1 := Ideal.prod_eq_iInf_of_pairwise_isCoprime hcop
  have h2 := Ideal.prod_eq_iInf_of_pairwise_isCoprime hcop2
  simp only [Finset.mem_univ, iInf_pos] at h1 h2
  rw [doublePointIdeal_def, ← h1, ← Finset.prod_pow, h2]

/-- The kernel of `piFirstJet P` is `doublePointIdeal P` when `ι` is finite and distinct points
have a unit coordinate difference. -/
theorem ker_piFirstJet [Finite ι] {P : ι → σ → R}
    (hP : Pairwise fun i j ↦ ∃ s, IsUnit (P i s - P j s)) :
    RingHom.ker (piFirstJet P) = doublePointIdeal P := by
  rw [doublePointIdeal_eq_iInf_sq hP]
  ext f
  simp only [RingHom.mem_ker, Ideal.mem_iInf, ← ker_firstJet, _root_.funext_iff, piFirstJet_apply,
    Pi.zero_apply]

/-- A polynomial lies in `doublePointIdeal P` (for finitely many points with pairwise unit
coordinate differences) if and only if it and all of its first partial derivatives vanish at every
`P i`. -/
theorem mem_doublePointIdeal_iff [Finite ι] {P : ι → σ → R}
    (hP : Pairwise fun i j ↦ ∃ s, IsUnit (P i s - P j s)) (f : MvPolynomial σ R) :
    f ∈ doublePointIdeal P ↔ ∀ i, eval (P i) f = 0 ∧ ∀ j, eval (P i) (pderiv j f) = 0 := by
  rw [← ker_piFirstJet hP, mem_ker_piFirstJet_iff]

/-- For finitely many points in finitely many variables with pairwise unit coordinate differences,
the product first-jet map `piFirstJet P` is surjective. -/
theorem piFirstJet_surjective [Finite ι] [Finite σ] {P : ι → σ → R}
    (hP : Pairwise fun i j ↦ ∃ s, IsUnit (P i s - P j s)) :
    Function.Surjective (piFirstJet P) := by
  intro y
  choose g hg using fun i ↦ firstJet_surjective (P i) (y i)
  obtain ⟨f, hf⟩ := Ideal.exists_forall_sub_mem_ideal
    (I := fun i ↦ RingHom.ker (eval (P i)) ^ 2)
    (fun _ _ hij ↦ (isCoprime_ker_eval (hP hij)).pow) g
  refine ⟨f, _root_.funext fun i ↦ ?_⟩
  have hmem : f - g i ∈ RingHom.ker (firstJet (P i)) := by
    rw [ker_firstJet]
    exact hf i
  rw [RingHom.mem_ker, map_sub, sub_eq_zero] at hmem
  rw [piFirstJet_apply, hmem, hg i]

/-- **Double-point quotient comparison.** For finitely many points in finitely many variables with
pairwise unit coordinate differences, the quotient `MvPolynomial σ R ⧸ doublePointIdeal P` is
isomorphic as an `R`-algebra to the product `ι → TrivSqZeroExt R (σ → R)` of local first-jet
algebras, sending the class of `f` to `fun i ↦ firstJet (P i) f`. -/
noncomputable def doublePointQuotientEquiv [Finite ι] [Finite σ] {P : ι → σ → R}
    (hP : Pairwise fun i j ↦ ∃ s, IsUnit (P i s - P j s)) :
    (MvPolynomial σ R ⧸ doublePointIdeal P) ≃ₐ[R] (ι → TrivSqZeroExt R (σ → R)) :=
  (Ideal.quotientEquivAlgOfEq R (ker_piFirstJet hP).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective (piFirstJet_surjective hP))

@[simp]
theorem doublePointQuotientEquiv_mk [Finite ι] [Finite σ] {P : ι → σ → R}
    (hP : Pairwise fun i j ↦ ∃ s, IsUnit (P i s - P j s)) (f : MvPolynomial σ R) :
    doublePointQuotientEquiv hP (Ideal.Quotient.mk _ f) = fun i ↦ firstJet (P i) f := by
  ext i <;> simp [doublePointQuotientEquiv]

/-- Reindexing the point family along an equivalence commutes with `doublePointQuotientEquiv`. -/
theorem doublePointQuotientEquiv_comp_equiv [Finite ι] [Finite ι'] [Finite σ]
    {P : ι → σ → R} (hP : Pairwise fun i j ↦ ∃ s, IsUnit (P i s - P j s)) (e : ι' ≃ ι)
    (x : MvPolynomial σ R ⧸ doublePointIdeal (P ∘ e)) (i' : ι') :
    doublePointQuotientEquiv (hP.comp_of_injective e.injective) x i' =
      doublePointQuotientEquiv hP
        (Ideal.quotientEquivAlgOfEq R (doublePointIdeal_comp_equiv P e) x) (e i') := by
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [doublePointQuotientEquiv_mk (P := P ∘ e), Ideal.quotientEquivAlgOfEq_mk,
    doublePointQuotientEquiv_mk]
  rfl

/-- **Length of distinct double points.** Over a commutative ring with the strong rank condition,
the quotient by the double-point ideal of `card ι` points in `card σ` variables with pairwise unit
coordinate differences has rank `card ι * (card σ + 1)`. -/
theorem finrank_quotient_doublePointIdeal [StrongRankCondition R] [Fintype ι] [Fintype σ]
    {P : ι → σ → R} (hP : Pairwise fun i j ↦ ∃ s, IsUnit (P i s - P j s)) :
    Module.finrank R (MvPolynomial σ R ⧸ doublePointIdeal P) =
      Fintype.card ι * (Fintype.card σ + 1) := by
  let e : (MvPolynomial σ R ⧸ doublePointIdeal P) ≃ₗ[R] (ι × Option σ → R) :=
    (doublePointQuotientEquiv hP).toLinearEquiv ≪≫ₗ
      (LinearEquiv.piCongrRight fun _ ↦
        (TrivSqZeroExt.linearEquivProd R R (σ → R)).trans
          (LinearEquiv.piOptionEquivProd R (M := fun _ : Option σ ↦ R)).symm) ≪≫ₗ
      (LinearEquiv.curry R R ι (Option σ)).symm
  rw [e.finrank_eq, Module.finrank_pi, Fintype.card_prod, Fintype.card_option]

end CommRing

section Field

variable [Field k]

/-- Distinct points over a field have a unit difference in some coordinate. -/
theorem pairwise_exists_isUnit_sub_of_injective {P : ι → σ → k} (hP : Function.Injective P) :
    Pairwise fun i j ↦ ∃ s, IsUnit (P i s - P j s) := fun _ _ hij ↦ by
  obtain ⟨s, hs⟩ := Function.ne_iff.mp (hP.ne hij)
  exact ⟨s, (sub_ne_zero.mpr hs).isUnit⟩

/-- Over a field, distinct points have comaximal evaluation ideals. -/
theorem isCoprime_ker_eval_of_ne {P Q : σ → k} (h : P ≠ Q) :
    IsCoprime (RingHom.ker (eval P)) (RingHom.ker (eval Q)) := by
  obtain ⟨j, hj⟩ := Function.ne_iff.mp h
  exact isCoprime_ker_eval ⟨j, (sub_ne_zero.mpr hj).isUnit⟩

/-- Over a field, for finitely many distinct points, `doublePointIdeal P` equals the intersection
of the squares of the individual evaluation ideals. -/
theorem doublePointIdeal_eq_iInf_sq_of_injective [Finite ι] {P : ι → σ → k}
    (hP : Function.Injective P) :
    doublePointIdeal P = ⨅ i, RingHom.ker (eval (P i)) ^ 2 :=
  doublePointIdeal_eq_iInf_sq (pairwise_exists_isUnit_sub_of_injective hP)

/-- Over a field, the kernel of `piFirstJet P` at finitely many distinct points is
`doublePointIdeal P`. -/
theorem ker_piFirstJet_of_injective [Finite ι] {P : ι → σ → k} (hP : Function.Injective P) :
    RingHom.ker (piFirstJet P) = doublePointIdeal P :=
  ker_piFirstJet (pairwise_exists_isUnit_sub_of_injective hP)

/-- Over a field, a polynomial lies in `doublePointIdeal P` at finitely many distinct points if and
only if it and all of its first partial derivatives vanish at every `P i`. -/
theorem mem_doublePointIdeal_iff_of_injective [Finite ι] {P : ι → σ → k}
    (hP : Function.Injective P) (f : MvPolynomial σ k) :
    f ∈ doublePointIdeal P ↔ ∀ i, eval (P i) f = 0 ∧ ∀ j, eval (P i) (pderiv j f) = 0 :=
  mem_doublePointIdeal_iff (pairwise_exists_isUnit_sub_of_injective hP) f

/-- Over a field, `piFirstJet P` is surjective at finitely many distinct points in finitely many
variables. -/
theorem piFirstJet_surjective_of_injective [Finite ι] [Finite σ] {P : ι → σ → k}
    (hP : Function.Injective P) :
    Function.Surjective (piFirstJet P) :=
  piFirstJet_surjective (pairwise_exists_isUnit_sub_of_injective hP)

/-- Over a field, the quotient by the double-point ideal of `card ι` distinct points in `card σ`
variables has dimension `card ι * (card σ + 1)`. -/
theorem finrank_quotient_doublePointIdeal_of_injective [Fintype ι] [Fintype σ] {P : ι → σ → k}
    (hP : Function.Injective P) :
    Module.finrank k (MvPolynomial σ k ⧸ doublePointIdeal P) =
      Fintype.card ι * (Fintype.card σ + 1) :=
  finrank_quotient_doublePointIdeal (pairwise_exists_isUnit_sub_of_injective hP)

end Field

end MvPolynomial
