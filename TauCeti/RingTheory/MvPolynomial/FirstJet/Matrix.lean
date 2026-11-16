/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Rank
public import TauCeti.Data.Finsupp.Weight
public import TauCeti.RingTheory.MvPolynomial.FirstJet.Basic
public import TauCeti.RingTheory.MvPolynomial.RestrictTotalDegree
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Pi
import TauCeti.LinearAlgebra.HermiteInterpolation
import TauCeti.RingTheory.MvPolynomial.Finrank
import TauCeti.RingTheory.MvPolynomial.RestrictSupport

/-!
# Bounded first-jet evaluation, monomial matrices, and well-poisedness

Restricting the first-jet evaluation at a family of points `P : ι → σ → R` to the submodule
`MvPolynomial.restrictTotalDegree σ R d` of polynomials of total degree at most `d` yields the
`R`-linear map `MvPolynomial.firstJetMap P d : restrictTotalDegree σ R d →ₗ[R] (ι → Option σ → R)`,
with `none` recording the value `eval (P i) f` and `some j` recording the partial derivative
`eval (P i) (pderiv j f)`.

Projecting onto the `none` coordinates gives the value evaluation map `MvPolynomial.evalMap P d`,
and restricting the `some` coordinates to its kernel gives `MvPolynomial.firstJetDerivOnKer P d`.
Over a commutative ring, `firstJetMap P d` is surjective if and only if both `evalMap P d` and
`firstJetDerivOnKer P d` are surjective (`MvPolynomial.surjective_firstJetMap_iff`).

In the monomial basis `MvPolynomial.basisRestrictTotalDegree σ R d`, `firstJetMap P d` is
represented by the monomial first-jet matrix `MvPolynomial.firstJetMatrix P d` with rows indexed
by `ι × Option σ` and columns indexed by `{a : σ →₀ ℕ // a.degree ≤ d}`. Its rank equals
`Module.finrank R (LinearMap.range (firstJetMap P d))` and is bounded above by
`min ((card σ + d).choose d) (card ι * (card σ + 1))`. A configuration `P` is well-poised in
degree `d` (`MvPolynomial.WellPoised P d`) when `firstJetMap P d` is surjective; over a field,
this holds if and only if `firstJetMatrix P d` has full row rank `card ι * (card σ + 1)`.

In one variable (`[Unique σ]`), identifying `firstJetMap P d` with `Polynomial.hasseJet` of
uniform multiplicity `2` via `MvPolynomial.uniqueAlgEquiv` yields Hermite interpolation for
double points: over a commutative ring with unit node differences, `firstJetMap P d` is injective
when `d + 1 ≤ 2 * card ι` and surjective when `2 * card ι ≤ d + 1`; under `[StrongRankCondition R]`
(and in particular over any field for injective `P`), the matrix `firstJetMatrix P d` has exact
rank `min (d + 1) (2 * card ι)`.

## Main definitions

* `MvPolynomial.firstJetMap`: bounded first-jet evaluation on `restrictTotalDegree σ R d`.
* `MvPolynomial.evalMap`: value evaluation on `restrictTotalDegree σ R d`, the `none`-projection
  of `firstJetMap`.
* `MvPolynomial.firstJetDerivOnKer`: partial-derivative evaluation on `LinearMap.ker (evalMap P d)`.
* `MvPolynomial.firstJetMatrix`: the monomial matrix representing `firstJetMap P d`.
* `MvPolynomial.WellPoised`: surjectivity of `firstJetMap P d`.

## Main results

* `MvPolynomial.surjective_firstJetMap_iff`: over a commutative ring, `firstJetMap P d` is
  surjective iff `evalMap P d` and `firstJetDerivOnKer P d` are surjective.
* `MvPolynomial.firstJetMatrix_mulVec`, `MvPolynomial.toLin_firstJetMatrix`: `firstJetMatrix P d`
  represents `firstJetMap P d` in monomial coordinates.
* `MvPolynomial.rank_firstJetMatrix_eq_finrank_range`, `MvPolynomial.rank_firstJetMatrix_le`:
  matrix rank equals the rank of the range of `firstJetMap P d` and is bounded by the row and
  column counts.
* `MvPolynomial.WellPoised.rank_firstJetMatrix`, `MvPolynomial.WellPoised.card_mul_le_choose`,
  `MvPolynomial.wellPoised_iff_rank_eq`: well-poisedness forces full row rank and the dimension
  bound under `[StrongRankCondition R]`, and over a field is equivalent to full row rank.
* `MvPolynomial.wellPoised_of_subsingleton`, `MvPolynomial.not_wellPoised_zero`: one point is
  well-poised in every degree `d ≥ 1` over any commutative ring in finitely many variables, and
  no nonempty tuple in nonempty variables over a nontrivial semiring is well-poised in degree `0`.
* `MvPolynomial.firstJetMap_injective_of_unique`, `MvPolynomial.wellPoised_of_unique`,
  `MvPolynomial.rank_firstJetMatrix_unique`, `MvPolynomial.wellPoised_unique_iff`,
  `MvPolynomial.rank_firstJetMatrix_unique_of_injective`: univariate double-point Hermite
  interpolation and exact rank `min (d + 1) (2 * card ι)`.

## References

* M. C. Brambilla and G. Ottaviani, *On the Alexander–Hirschowitz theorem*, J. Pure Appl. Algebra
  212 (2008), 1229–1251, §§1–2, §7.1.
* J.-M. Couveignes, *Enumerating number fields*, Ann. of Math. (2) 192 (2020), 487–497, §3,
  pp. 491–493.
-/

public section

namespace MvPolynomial

variable {σ ι ι' R S k : Type*}

section FirstJetMap

variable [CommSemiring R]

/-- The bounded first-jet evaluation map at a family of points `P : ι → σ → R` on polynomials of
total degree at most `d`, sending `f` to `eval (P i) f` at `(i, none)` and
`eval (P i) (pderiv j f)` at `(i, some j)`. -/
noncomputable def firstJetMap (P : ι → σ → R) (d : ℕ) :
    restrictTotalDegree σ R d →ₗ[R] (ι → Option σ → R) where
  toFun f i z := match z with
    | none => eval (P i) f.1
    | some j => eval (P i) (pderiv j f.1)
  map_add' _ _ := by
    ext i z
    cases z <;> simp
  map_smul' _ _ := by
    ext i z
    cases z <;> simp

@[simp]
theorem firstJetMap_apply_none (P : ι → σ → R) (d : ℕ) (f : restrictTotalDegree σ R d) (i : ι) :
    firstJetMap P d f i none = eval (P i) f.1 := (rfl)

@[simp]
theorem firstJetMap_apply_some (P : ι → σ → R) (d : ℕ) (f : restrictTotalDegree σ R d) (i : ι)
    (j : σ) :
    firstJetMap P d f i (some j) = eval (P i) (pderiv j f.1) := (rfl)

/-- On a monomial `X ^ a`, the `none` coordinate of `firstJetMap P d` is `∏ s, P i s ^ a s`. -/
theorem firstJetMap_monomial_none (P : ι → σ → R) {d : ℕ} {a : σ →₀ ℕ} (ha : a.degree ≤ d)
    (i : ι) :
    firstJetMap P d ⟨monomial a 1, monomial_mem_restrictTotalDegree ha 1⟩ i none =
      a.prod fun s e ↦ P i s ^ e := by
  simp [eval_monomial]

/-- On a monomial `X ^ a`, the `some j` coordinate of `firstJetMap P d` is
`a j * ∏ s, P i s ^ (a - single j 1) s`. -/
theorem firstJetMap_monomial_some (P : ι → σ → R) {d : ℕ} {a : σ →₀ ℕ} (ha : a.degree ≤ d)
    (i : ι) (j : σ) :
    firstJetMap P d ⟨monomial a 1, monomial_mem_restrictTotalDegree ha 1⟩ i (some j) =
      (a j : R) * (a - Finsupp.single j 1).prod fun s e ↦ P i s ^ e := by
  simp [pderiv_monomial, eval_monomial]

/-- A bounded-degree polynomial lies in the kernel of `firstJetMap P d` iff it and all of its first
partial derivatives vanish at every `P i`. -/
theorem mem_ker_firstJetMap_iff (P : ι → σ → R) (d : ℕ) (f : restrictTotalDegree σ R d) :
    f ∈ LinearMap.ker (firstJetMap P d) ↔
      ∀ i, eval (P i) f.1 = 0 ∧ ∀ j, eval (P i) (pderiv j f.1) = 0 := by
  simp only [LinearMap.mem_ker, _root_.funext_iff, Pi.zero_apply, Option.forall,
    firstJetMap_apply_none, firstJetMap_apply_some]

/-- Raising the degree bound leaves `firstJetMap` unchanged along the submodule inclusion. -/
@[simp]
theorem firstJetMap_inclusion (P : ι → σ → R) {d e : ℕ} (h : d ≤ e)
    (f : restrictTotalDegree σ R d) :
    firstJetMap P e (Submodule.inclusion (restrictTotalDegree_mono σ R h) f) =
      firstJetMap P d f := (rfl)

/-- Reindexing the point family along `g : ι' → ι` pulls back `firstJetMap` along `g`. -/
@[simp]
theorem firstJetMap_comp (P : ι → σ → R) (g : ι' → ι) (d : ℕ) (f : restrictTotalDegree σ R d)
    (i' : ι') :
    firstJetMap (P ∘ g) d f i' = firstJetMap P d f (g i') := (rfl)

/-- Value evaluation of bounded-degree polynomials at `P : ι → σ → R`: the `none`-projection of
`firstJetMap P d`. -/
noncomputable def evalMap (P : ι → σ → R) (d : ℕ) :
    restrictTotalDegree σ R d →ₗ[R] (ι → R) where
  toFun f i := eval (P i) f.1
  map_add' _ _ := by ext i; simp
  map_smul' _ _ := by ext i; simp

@[simp]
theorem evalMap_apply (P : ι → σ → R) (d : ℕ) (f : restrictTotalDegree σ R d) (i : ι) :
    evalMap P d f i = eval (P i) f.1 := (rfl)

theorem evalMap_eq_firstJetMap_none (P : ι → σ → R) (d : ℕ) (f : restrictTotalDegree σ R d)
    (i : ι) :
    evalMap P d f i = firstJetMap P d f i none := (rfl)

theorem mem_ker_evalMap_iff (P : ι → σ → R) (d : ℕ) (f : restrictTotalDegree σ R d) :
    f ∈ LinearMap.ker (evalMap P d) ↔ ∀ i, eval (P i) f.1 = 0 := by
  simp [LinearMap.mem_ker, _root_.funext_iff]

@[simp]
theorem evalMap_inclusion (P : ι → σ → R) {d e : ℕ} (h : d ≤ e)
    (f : restrictTotalDegree σ R d) :
    evalMap P e (Submodule.inclusion (restrictTotalDegree_mono σ R h) f) = evalMap P d f := (rfl)

theorem evalMap_comp (P : ι → σ → R) (g : ι' → ι) (d : ℕ) (f : restrictTotalDegree σ R d)
    (i' : ι') :
    evalMap (P ∘ g) d f i' = evalMap P d f (g i') := (rfl)

/-- Reindexing the point family along an equivalence preserves `LinearMap.ker (evalMap P d)`. -/
@[simp]
theorem ker_evalMap_comp_equiv (P : ι → σ → R) (e : ι' ≃ ι) (d : ℕ) :
    LinearMap.ker (evalMap (P ∘ e) d) = LinearMap.ker (evalMap P d) := by
  ext f
  simp only [mem_ker_evalMap_iff, Function.comp_apply]
  exact ⟨fun h i ↦ by simpa using h (e.symm i), fun h i' ↦ h (e i')⟩

/-- Evaluation of first partial derivatives at `P : ι → σ → R` on polynomials of total degree at
most `d` vanishing at every `P i`. -/
noncomputable def firstJetDerivOnKer (P : ι → σ → R) (d : ℕ) :
    LinearMap.ker (evalMap P d) →ₗ[R] (ι → σ → R) where
  toFun f i j := eval (P i) (pderiv j f.1.1)
  map_add' _ _ := by ext i j; simp
  map_smul' _ _ := by ext i j; simp

@[simp]
theorem firstJetDerivOnKer_apply (P : ι → σ → R) (d : ℕ) (f : LinearMap.ker (evalMap P d))
    (i : ι) (j : σ) :
    firstJetDerivOnKer P d f i j = eval (P i) (pderiv j f.1.1) := (rfl)

theorem firstJetDerivOnKer_eq_firstJetMap_some (P : ι → σ → R) (d : ℕ)
    (f : LinearMap.ker (evalMap P d)) (i : ι) (j : σ) :
    firstJetDerivOnKer P d f i j = firstJetMap P d f.1 i (some j) := (rfl)

theorem mem_ker_firstJetDerivOnKer_iff (P : ι → σ → R) (d : ℕ)
    (f : LinearMap.ker (evalMap P d)) :
    f ∈ LinearMap.ker (firstJetDerivOnKer P d) ↔ ∀ i j, eval (P i) (pderiv j f.1.1) = 0 := by
  simp [LinearMap.mem_ker, _root_.funext_iff]

/-- Reindexing the point family along an equivalence permutes the target coordinates of
`firstJetDerivOnKer`. -/
theorem firstJetDerivOnKer_comp_equiv (P : ι → σ → R) (e : ι' ≃ ι) (d : ℕ)
    (f : LinearMap.ker (evalMap P d)) (i' : ι') :
    firstJetDerivOnKer (P ∘ e) d (LinearEquiv.ofEq _ _ (ker_evalMap_comp_equiv P e d).symm f) i' =
      firstJetDerivOnKer P d f (e i') := (rfl)

/-- A family of points `P : ι → σ → R` is well-poised in degree `d` when every value and
first-derivative datum at `P` is realized by a polynomial of total degree at most `d`. -/
def WellPoised (P : ι → σ → R) (d : ℕ) : Prop :=
  Function.Surjective (firstJetMap P d)

theorem wellPoised_def (P : ι → σ → R) (d : ℕ) :
    WellPoised P d ↔ Function.Surjective (firstJetMap P d) := Iff.rfl

/-- Well-poisedness is monotone in the degree bound. -/
theorem WellPoised.mono {P : ι → σ → R} {d e : ℕ} (hde : d ≤ e) (h : WellPoised P d) :
    WellPoised P e := fun y ↦
  let ⟨f, hf⟩ := h y
  ⟨Submodule.inclusion (restrictTotalDegree_mono σ R hde) f, hf⟩

/-- Reindexing the point family along an equivalence preserves well-poisedness. -/
theorem wellPoised_comp_equiv_iff (P : ι → σ → R) (e : ι' ≃ ι) (d : ℕ) :
    WellPoised (P ∘ e) d ↔ WellPoised P d := by
  constructor
  · intro h y
    obtain ⟨f, hf⟩ := h fun i' ↦ y (e i')
    refine ⟨f, _root_.funext fun i ↦ ?_⟩
    simpa [firstJetMap_comp] using congrFun hf (e.symm i)
  · intro h y
    obtain ⟨f, hf⟩ := h fun i ↦ y (e.symm i)
    refine ⟨f, _root_.funext fun i' ↦ ?_⟩
    simpa [firstJetMap_comp] using congrFun hf (e i')

/-- An empty family of points is well-poised in every degree. -/
theorem wellPoised_of_isEmpty [IsEmpty ι] (P : ι → σ → R) (d : ℕ) : WellPoised P d :=
  fun _ ↦ ⟨0, _root_.funext isEmptyElim⟩

/-- In degree `0`, every partial derivative vanishes, so a nonempty family of points in at least one
variable over a nontrivial commutative semiring is never well-poised. -/
theorem not_wellPoised_zero [Nontrivial R] [Nonempty ι] [Nonempty σ] (P : ι → σ → R) :
    ¬ WellPoised P 0 := by
  intro h
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  obtain ⟨j₀⟩ := ‹Nonempty σ›
  obtain ⟨f, hf⟩ := h fun _ z ↦ match z with
    | none => 0
    | some _ => 1
  have hdeg : f.1.totalDegree = 0 :=
    Nat.eq_zero_of_le_zero ((mem_restrictTotalDegree σ 0 f.1).1 f.2)
  have hpderiv : pderiv j₀ f.1 = 0 := by
    rw [totalDegree_eq_zero_iff_eq_C.mp hdeg, pderiv_C]
  have hval := congrFun (congrFun hf i₀) (some j₀)
  simp [hpderiv] at hval

end FirstJetMap

section FirstJetMapCommRing

variable [CommRing R]

/-- Over a commutative ring, for finitely many points with pairwise unit coordinate differences,
the kernel of `firstJetMap P d` consists of the polynomials of total degree at most `d` lying in
`doublePointIdeal P`. -/
theorem mem_ker_firstJetMap_iff_mem_doublePointIdeal [Finite ι] {P : ι → σ → R}
    (hP : Pairwise fun i j ↦ ∃ s, IsUnit (P i s - P j s)) (d : ℕ)
    (f : restrictTotalDegree σ R d) :
    f ∈ LinearMap.ker (firstJetMap P d) ↔ (f : MvPolynomial σ R) ∈ doublePointIdeal P := by
  rw [mem_ker_firstJetMap_iff, mem_doublePointIdeal_iff hP]

/-- **Surjectivity through the value kernel.** Over any commutative ring, `firstJetMap P d` is
surjective if and only if both `evalMap P d` and `firstJetDerivOnKer P d` are surjective. -/
theorem surjective_firstJetMap_iff (P : ι → σ → R) (d : ℕ) :
    Function.Surjective (firstJetMap P d) ↔
      Function.Surjective (evalMap P d) ∧ Function.Surjective (firstJetDerivOnKer P d) := by
  constructor
  · intro h
    refine ⟨fun v ↦ ?_, fun w ↦ ?_⟩
    · obtain ⟨f, hf⟩ := h fun i z ↦ match z with
        | none => v i
        | some _ => 0
      refine ⟨f, _root_.funext fun i ↦ ?_⟩
      simpa using congrFun (congrFun hf i) none
    · obtain ⟨f, hf⟩ := h fun i z ↦ match z with
        | none => 0
        | some j => w i j
      have hfker : f ∈ LinearMap.ker (evalMap P d) :=
        (mem_ker_evalMap_iff P d f).mpr fun i ↦ by simpa using congrFun (congrFun hf i) none
      refine ⟨⟨f, hfker⟩, _root_.funext fun i ↦ _root_.funext fun j ↦ ?_⟩
      simpa using congrFun (congrFun hf i) (some j)
  · rintro ⟨hval, hder⟩ y
    obtain ⟨f₁, hf₁⟩ := hval fun i ↦ y i none
    obtain ⟨⟨f₂, hf₂⟩, hgf₂⟩ := hder fun i j ↦ y i (some j) - eval (P i) (pderiv j f₁.1)
    refine ⟨f₁ + f₂, _root_.funext fun i ↦ _root_.funext fun z ↦ ?_⟩
    cases z with
    | none =>
      have h1 : eval (P i) f₁.1 = y i none := congrFun hf₁ i
      have h2 : eval (P i) f₂.1 = 0 := (mem_ker_evalMap_iff P d f₂).mp hf₂ i
      simp [h1, h2]
    | some j =>
      have h2 : eval (P i) (pderiv j f₂.1) = y i (some j) - eval (P i) (pderiv j f₁.1) :=
        congrFun (congrFun hgf₂ i) j
      simp [h2]

/-- Over a commutative ring, well-poisedness splits into surjectivity of values and surjectivity of
derivatives on the value kernel. -/
theorem wellPoised_iff_surjective_evalMap_and (P : ι → σ → R) (d : ℕ) :
    WellPoised P d ↔
      Function.Surjective (evalMap P d) ∧ Function.Surjective (firstJetDerivOnKer P d) :=
  surjective_firstJetMap_iff P d

/-- Over a commutative ring in finitely many variables, at most one point is well-poised in every
degree `d ≥ 1`. -/
theorem wellPoised_of_subsingleton [Finite σ] [Subsingleton ι] (P : ι → σ → R) {d : ℕ}
    (hd : 1 ≤ d) : WellPoised P d := by
  intro y
  rcases isEmpty_or_nonempty ι with hι | ⟨⟨i₀⟩⟩
  · exact ⟨0, _root_.funext isEmptyElim⟩
  · obtain ⟨f, hfdeg, hfj⟩ := exists_totalDegree_le_one_firstJet_eq (P i₀)
      (TrivSqZeroExt.inl (y i₀ none) + TrivSqZeroExt.inr fun j ↦ y i₀ (some j))
    refine ⟨⟨f, (mem_restrictTotalDegree σ d f).2 (hfdeg.trans hd)⟩,
      _root_.funext fun i ↦ _root_.funext fun z ↦ ?_⟩
    rw [Subsingleton.elim i i₀]
    cases z with
    | none =>
      simpa using congrArg TrivSqZeroExt.fst hfj
    | some j =>
      simpa using congrFun (congrArg TrivSqZeroExt.snd hfj) j

end FirstJetMapCommRing

section FirstJetMatrix

variable [CommSemiring R]

/-- The monomial matrix of first-jet evaluation at `P : ι → σ → R` in degree `d`, with rows indexed
by `ι × Option σ` and columns indexed by `{a : σ →₀ ℕ // a.degree ≤ d}`. -/
noncomputable def firstJetMatrix (P : ι → σ → R) (d : ℕ) :
    Matrix (ι × Option σ) {a : σ →₀ ℕ // a.degree ≤ d} R :=
  fun z a ↦ match z.2 with
    | none => eval (P z.1) (monomial a.1 1)
    | some j => eval (P z.1) (pderiv j (monomial a.1 1))

@[simp]
theorem firstJetMatrix_apply_none (P : ι → σ → R) (d : ℕ) (i : ι)
    (a : {a : σ →₀ ℕ // a.degree ≤ d}) :
    firstJetMatrix P d (i, none) a = eval (P i) (monomial a.1 1) := (rfl)

@[simp]
theorem firstJetMatrix_apply_some (P : ι → σ → R) (d : ℕ) (i : ι) (j : σ)
    (a : {a : σ →₀ ℕ // a.degree ≤ d}) :
    firstJetMatrix P d (i, some j) a = eval (P i) (pderiv j (monomial a.1 1)) := (rfl)

theorem firstJetMatrix_apply_none_eq_prod (P : ι → σ → R) (d : ℕ) (i : ι)
    (a : {a : σ →₀ ℕ // a.degree ≤ d}) :
    firstJetMatrix P d (i, none) a = a.1.prod fun s e ↦ P i s ^ e := by
  simp [eval_monomial]

theorem firstJetMatrix_apply_some_eq_mul_prod (P : ι → σ → R) (d : ℕ) (i : ι) (j : σ)
    (a : {a : σ →₀ ℕ // a.degree ≤ d}) :
    firstJetMatrix P d (i, some j) a =
      (a.1 j : R) * (a.1 - Finsupp.single j 1).prod fun s e ↦ P i s ^ e := by
  simp [pderiv_monomial, eval_monomial]

/-- Reindexing the point family along `g : ι' → ι` pulls back the rows of `firstJetMatrix`. -/
@[simp]
theorem firstJetMatrix_comp (P : ι → σ → R) (g : ι' → ι) (d : ℕ) (i' : ι') (z : Option σ)
    (a : {a : σ →₀ ℕ // a.degree ≤ d}) :
    firstJetMatrix (P ∘ g) d (i', z) a = firstJetMatrix P d (g i', z) a := (rfl)

/-- Mapping the entries of `firstJetMatrix P d` along a ring homomorphism `φ : R →+* S` produces
the first-jet matrix of the image configuration `fun i s ↦ φ (P i s)`. -/
@[simp]
theorem firstJetMatrix_map [CommSemiring S] (φ : R →+* S) (P : ι → σ → R) (d : ℕ) :
    (firstJetMatrix P d).map φ = firstJetMatrix (fun i s ↦ φ (P i s)) d := by
  ext ⟨i, z⟩ a
  cases z with
  | none =>
    simp [Matrix.map_apply, eval_monomial, Finsupp.prod, map_prod]
  | some j =>
    simp [Matrix.map_apply, pderiv_monomial, eval_monomial, Finsupp.prod, map_prod]

/-- Multiplying `firstJetMatrix P d` by the monomial coefficient vector of a bounded-degree
polynomial `f` computes `firstJetMap P d f`. -/
theorem firstJetMatrix_mulVec (P : ι → σ → R) (d : ℕ) [Fintype {a : σ →₀ ℕ // a.degree ≤ d}]
    (f : restrictTotalDegree σ R d) (i : ι) (z : Option σ) :
    (firstJetMatrix P d).mulVec (fun a ↦ (f : MvPolynomial σ R).coeff a.1) (i, z) =
      firstJetMap P d f i z := by
  have hrepr : f = ∑ a : {a : σ →₀ ℕ // a.degree ≤ d},
      (f : MvPolynomial σ R).coeff a.1 • basisRestrictTotalDegree σ R d a := by
    conv_lhs => rw [← (basisRestrictTotalDegree σ R d).sum_repr f]
    simp
  conv_rhs => rw [hrepr]
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec,
    dotProduct]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  cases z <;> simp [mul_comm]

/-- In the monomial basis `basisRestrictTotalDegree σ R d` and the standard row basis
`Pi.basisFun R (ι × Option σ)`, `firstJetMatrix P d` represents `firstJetMap P d` (up to
uncurrying the target). -/
theorem toLin_firstJetMatrix [Finite ι] [Finite σ] (P : ι → σ → R) (d : ℕ)
    [Fintype {a : σ →₀ ℕ // a.degree ≤ d}] [DecidableEq {a : σ →₀ ℕ // a.degree ≤ d}] :
    Matrix.toLin (basisRestrictTotalDegree σ R d) (Pi.basisFun R (ι × Option σ))
      (firstJetMatrix P d) =
      (LinearEquiv.curry R R ι (Option σ)).symm.toLinearMap.comp (firstJetMap P d) := by
  apply (LinearMap.toMatrix (basisRestrictTotalDegree σ R d)
    (Pi.basisFun R (ι × Option σ))).injective
  rw [LinearMap.toMatrix_toLin]
  ext ⟨i, z⟩ a
  rw [LinearMap.toMatrix_apply]
  cases z <;> simp

/-- The rank of `firstJetMatrix P d` equals the `R`-rank of the range of `firstJetMap P d`. -/
theorem rank_firstJetMatrix_eq_finrank_range [Finite ι] [Finite σ]
    (P : ι → σ → R) (d : ℕ) [Fintype {a : σ →₀ ℕ // a.degree ≤ d}] :
    (firstJetMatrix P d).rank = Module.finrank R (LinearMap.range (firstJetMap P d)) := by
  classical
  rw [Matrix.rank_eq_finrank_range_toLin (firstJetMatrix P d) (Pi.basisFun R (ι × Option σ))
      (basisRestrictTotalDegree σ R d),
    toLin_firstJetMatrix, LinearMap.range_comp]
  exact (LinearEquiv.curry R R ι (Option σ)).symm.finrank_map_eq _

/-- The rank of `firstJetMatrix P d` is bounded above by both the number of admissible monomials
`(card σ + d).choose d` and the number of jet conditions `card ι * (card σ + 1)`. -/
theorem rank_firstJetMatrix_le [StrongRankCondition R] [Fintype ι] [Fintype σ]
    (P : ι → σ → R) (d : ℕ) [Fintype {a : σ →₀ ℕ // a.degree ≤ d}] :
    (firstJetMatrix P d).rank ≤
      min ((Fintype.card σ + d).choose d) (Fintype.card ι * (Fintype.card σ + 1)) := by
  refine le_min ?_ ?_
  · exact (Matrix.rank_le_card_width _).trans_eq (Finsupp.card_degree_le d)
  · exact (Matrix.rank_le_card_height _).trans_eq (by rw [Fintype.card_prod, Fintype.card_option])

/-- Reindexing the point family along an equivalence preserves the rank of `firstJetMatrix`. -/
theorem rank_firstJetMatrix_comp_equiv [Finite ι] [Finite ι'] [Finite σ]
    (P : ι → σ → R) (e : ι' ≃ ι) (d : ℕ) [Fintype {a : σ →₀ ℕ // a.degree ≤ d}] :
    (firstJetMatrix (P ∘ e) d).rank = (firstJetMatrix P d).rank := by
  rw [rank_firstJetMatrix_eq_finrank_range, rank_firstJetMatrix_eq_finrank_range]
  let φ : (ι → Option σ → R) ≃ₗ[R] (ι' → Option σ → R) :=
    LinearEquiv.piCongrLeft' R (fun _ ↦ Option σ → R) e.symm
  have hcomp : firstJetMap (P ∘ e) d = φ.toLinearMap.comp (firstJetMap P d) := by
    ext f i' z
    simp [φ]
  rw [hcomp, LinearMap.range_comp]
  exact φ.finrank_map_eq _

/-- Over a commutative semiring with the strong rank condition, a well-poised configuration has
full row rank `card ι * (card σ + 1)`. -/
theorem WellPoised.rank_firstJetMatrix [StrongRankCondition R] [Fintype ι] [Fintype σ]
    {P : ι → σ → R} {d : ℕ} [Fintype {a : σ →₀ ℕ // a.degree ≤ d}] (h : WellPoised P d) :
    (firstJetMatrix P d).rank = Fintype.card ι * (Fintype.card σ + 1) := by
  rw [rank_firstJetMatrix_eq_finrank_range, LinearMap.range_eq_top.mpr h, finrank_top,
    (LinearEquiv.curry R R ι (Option σ)).symm.finrank_eq, Module.finrank_pi, Fintype.card_prod,
    Fintype.card_option]

/-- Over a commutative semiring with the strong rank condition, a well-poised configuration of
`card ι` points in `card σ` variables of degree `d` satisfies
`card ι * (card σ + 1) ≤ (card σ + d).choose d`. -/
theorem WellPoised.card_mul_le_choose [StrongRankCondition R] [Fintype ι] [Fintype σ]
    {P : ι → σ → R} {d : ℕ} (h : WellPoised P d) :
    Fintype.card ι * (Fintype.card σ + 1) ≤ (Fintype.card σ + d).choose d := by
  classical
  rw [← h.rank_firstJetMatrix]
  exact (rank_firstJetMatrix_le P d).trans (min_le_left _ _)

end FirstJetMatrix

section FieldRank

variable [Field k]

/-- **Full row rank criterion.** Over a field, `P` is well-poised in degree `d` if and only if
`firstJetMatrix P d` has full row rank `card ι * (card σ + 1)`. -/
theorem wellPoised_iff_rank_eq [Fintype ι] [Fintype σ] (P : ι → σ → k) (d : ℕ)
    [Fintype {a : σ →₀ ℕ // a.degree ≤ d}] :
    WellPoised P d ↔ (firstJetMatrix P d).rank = Fintype.card ι * (Fintype.card σ + 1) := by
  refine ⟨WellPoised.rank_firstJetMatrix, fun h ↦ ?_⟩
  rw [wellPoised_def, ← LinearMap.range_eq_top]
  refine Submodule.eq_top_of_finrank_eq ?_
  rw [← rank_firstJetMatrix_eq_finrank_range, h,
    (LinearEquiv.curry k k ι (Option σ)).symm.finrank_eq, Module.finrank_pi, Fintype.card_prod,
    Fintype.card_option]

end FieldRank

section Univariate

private theorem firstJetMap_unique_eq_hasseJet {σ ι R : Type*} [CommSemiring R] [Unique σ]
    (P : ι → σ → R) (d : ℕ) (f : restrictTotalDegree σ R d) (i : ι) (z : Option σ) :
    firstJetMap P d f i z =
      Polynomial.hasseJet (fun i ↦ P i default) (fun _ ↦ 2) (uniqueAlgEquiv R σ f.1) i
        (match z with | none => 0 | some _ => 1) := by
  have hX : uniqueAlgEquiv R σ (X default) = Polynomial.X := by
    simp [X, Polynomial.X]
  have hpderiv (g : MvPolynomial σ R) :
      uniqueAlgEquiv R σ (pderiv default g) = Polynomial.derivative (uniqueAlgEquiv R σ g) := by
    induction g using MvPolynomial.induction_on with
    | C r =>
      rw [pderiv_C, map_zero, ← algebraMap_eq, AlgEquiv.commutes, Polynomial.algebraMap_eq,
        Polynomial.derivative_C]
    | add p q hp hq =>
      rw [map_add, map_add, map_add, hp, hq, Polynomial.derivative_add]
    | mul_X p j hp =>
      rw [Unique.eq_default j, pderiv_mul, pderiv_X_self, mul_one, map_add, map_mul, map_mul,
        hX, hp, Polynomial.derivative_mul, Polynomial.derivative_X, mul_one, add_comm]
  cases z with
  | none =>
    simp only [firstJetMap_apply_none, Polynomial.hasseJet_apply, Fin.val_zero,
      Polynomial.hasseDeriv_zero']
    exact (eval₂_uniqueAlgEquiv (R := R) (σ := σ) (f := f.1) (φ := RingHom.id R) (a := P i)).symm
  | some j =>
    rw [Unique.eq_default j]
    simp only [firstJetMap_apply_some, Polynomial.hasseJet_apply, Fin.val_one,
      Polynomial.hasseDeriv_one', ← hpderiv]
    exact (eval₂_uniqueAlgEquiv (R := R) (σ := σ) (f := pderiv default f.1)
      (φ := RingHom.id R) (a := P i)).symm

/-- **Univariate Hermite injectivity** for double points over a commutative ring: when the node
differences are units and `d + 1 ≤ 2 * card ι`, `firstJetMap P d` is injective. -/
theorem firstJetMap_injective_of_unique [CommRing R] [Unique σ] [Fintype ι] {P : ι → σ → R}
    (hP : Pairwise fun i j ↦ IsUnit (P i default - P j default)) {d : ℕ}
    (hd : d + 1 ≤ 2 * Fintype.card ι) :
    Function.Injective (firstJetMap P d) := by
  intro f g hfg
  have hmem (p : MvPolynomial σ R) :
      p ∈ restrictTotalDegree σ R d ↔ uniqueAlgEquiv R σ p ∈ Polynomial.degreeLT R (d + 1) := by
    rw [uniqueAlgEquiv_mem_degreeLT_iff, restrictTotalDegree_eq_restrictSupport,
      mem_restrictSupport_iff, mem_restrictSupport_iff]
    simp [Finsupp.degree_eq_sum]
  have hsum : (∑ _ : ι, (2 : ℕ)) = 2 * Fintype.card ι := by
    simp [mul_comm]
  have hle : Polynomial.degreeLT R (d + 1) ≤ Polynomial.degreeLT R (∑ _ : ι, (2 : ℕ)) :=
    Polynomial.degreeLT_mono (hsum ▸ hd)
  let f' : Polynomial.degreeLT R (∑ _ : ι, (2 : ℕ)) :=
    ⟨uniqueAlgEquiv R σ f.1, hle ((hmem f.1).mp f.2)⟩
  let g' : Polynomial.degreeLT R (∑ _ : ι, (2 : ℕ)) :=
    ⟨uniqueAlgEquiv R σ g.1, hle ((hmem g.1).mp g.2)⟩
  have hjet : Polynomial.hermiteJet (fun i ↦ P i default) (fun _ ↦ 2) f' =
      Polynomial.hermiteJet (fun i ↦ P i default) (fun _ ↦ 2) g' := by
    ext i k
    fin_cases k
    · have h0 := congrFun (congrFun hfg i) none
      simpa [f', g', firstJetMap_unique_eq_hasseJet] using h0
    · have h1 := congrFun (congrFun hfg i) (some default)
      simpa [f', g', firstJetMap_unique_eq_hasseJet] using h1
  have heq := (Polynomial.hermiteJet_bijective_of_pairwise_isUnit_sub hP (fun _ ↦ 2)).injective hjet
  exact Subtype.ext ((uniqueAlgEquiv R σ).injective (congrArg Subtype.val heq))

/-- **Univariate Hermite surjectivity** for double points over a commutative ring: when the node
differences are units and `2 * card ι ≤ d + 1`, `P` is well-poised in degree `d`. -/
theorem wellPoised_of_unique [CommRing R] [Unique σ] [Fintype ι] {P : ι → σ → R}
    (hP : Pairwise fun i j ↦ IsUnit (P i default - P j default)) {d : ℕ}
    (hd : 2 * Fintype.card ι ≤ d + 1) :
    WellPoised P d := by
  intro y
  have hmem (p : MvPolynomial σ R) :
      p ∈ restrictTotalDegree σ R d ↔ uniqueAlgEquiv R σ p ∈ Polynomial.degreeLT R (d + 1) := by
    rw [uniqueAlgEquiv_mem_degreeLT_iff, restrictTotalDegree_eq_restrictSupport,
      mem_restrictSupport_iff, mem_restrictSupport_iff]
    simp [Finsupp.degree_eq_sum]
  have hsum : (∑ _ : ι, (2 : ℕ)) = 2 * Fintype.card ι := by
    simp [mul_comm]
  have hle : Polynomial.degreeLT R (∑ _ : ι, (2 : ℕ)) ≤ Polynomial.degreeLT R (d + 1) :=
    Polynomial.degreeLT_mono (hsum ▸ hd)
  let c : ∀ _ : ι, Fin 2 → R := fun i k ↦ match k with
    | ⟨0, _⟩ => y i none
    | ⟨1, _⟩ => y i (some default)
  obtain ⟨g, hg⟩ :=
    (Polynomial.hermiteJet_bijective_of_pairwise_isUnit_sub hP (fun _ ↦ 2)).surjective c
  let f : MvPolynomial σ R := (uniqueAlgEquiv R σ).symm g.1
  have hf_eq : uniqueAlgEquiv R σ f = g.1 := (uniqueAlgEquiv R σ).apply_symm_apply g.1
  have hfmem : f ∈ restrictTotalDegree σ R d := by
    rw [hmem, hf_eq]
    exact hle g.2
  refine ⟨⟨f, hfmem⟩, ?_⟩
  ext i z
  rw [firstJetMap_unique_eq_hasseJet, hf_eq]
  have hgi := congrFun hg i
  cases z with
  | none =>
    simpa [c] using congrFun hgi 0
  | some j =>
    rw [Unique.eq_default j]
    simpa [c] using congrFun hgi 1

/-- **Univariate Hermite interpolation rank.** Over any commutative ring with the strong rank
condition, for univariate points `P : ι → σ → R` (`[Unique σ]`) whose pairwise differences are
units, the monomial first-jet matrix in degree `d` has exact rank `min (d + 1) (2 * card ι)`. -/
theorem rank_firstJetMatrix_unique [CommRing R] [StrongRankCondition R] [Unique σ] [Fintype ι]
    {P : ι → σ → R} (hP : Pairwise fun i j ↦ IsUnit (P i default - P j default)) (d : ℕ)
    [Fintype {a : σ →₀ ℕ // a.degree ≤ d}] :
    (firstJetMatrix P d).rank = min (d + 1) (2 * Fintype.card ι) := by
  rcases le_total (d + 1) (2 * Fintype.card ι) with hle | hge
  · rw [min_eq_left hle, rank_firstJetMatrix_eq_finrank_range,
      LinearMap.finrank_range_of_inj (firstJetMap_injective_of_unique hP hle),
      TauCeti.finrank_restrictTotalDegree, Fintype.card_unique (α := σ), Nat.choose_one_right]
  · rw [min_eq_right hge, (wellPoised_of_unique hP hge).rank_firstJetMatrix,
      Fintype.card_unique (α := σ), mul_comm]

/-- Over any commutative ring with the strong rank condition, univariate double points
`P : ι → σ → R` (`[Unique σ]`) with pairwise unit differences are well-poised in degree `d` if and
only if `2 * card ι ≤ d + 1`. -/
theorem wellPoised_unique_iff [CommRing R] [StrongRankCondition R] [Unique σ] [Fintype ι]
    {P : ι → σ → R} (hP : Pairwise fun i j ↦ IsUnit (P i default - P j default)) (d : ℕ) :
    WellPoised P d ↔ 2 * Fintype.card ι ≤ d + 1 := by
  refine ⟨fun h ↦ ?_, wellPoised_of_unique hP⟩
  have hle := h.card_mul_le_choose
  rw [Fintype.card_unique (α := σ), Nat.add_comm 1 d, Nat.choose_succ_self_right] at hle
  omega

/-- Over any field, for distinct univariate points `P : ι → σ → k` (`[Unique σ]`), the monomial
first-jet matrix in degree `d` has exact rank `min (d + 1) (2 * card ι)`. -/
theorem rank_firstJetMatrix_unique_of_injective [Field k] [Unique σ] [Fintype ι]
    {P : ι → σ → k} (hP : Function.Injective P) (d : ℕ)
    [Fintype {a : σ →₀ ℕ // a.degree ≤ d}] :
    (firstJetMatrix P d).rank = min (d + 1) (2 * Fintype.card ι) :=
  rank_firstJetMatrix_unique
    ((pairwise_exists_isUnit_sub_of_injective hP).mono fun _ _ ⟨s, hs⟩ ↦
      Unique.eq_default s ▸ hs)
    d

/-- Over any field, distinct univariate double points `P : ι → σ → k` (`[Unique σ]`) are
well-poised in degree `d` if and only if `2 * card ι ≤ d + 1`. -/
theorem wellPoised_unique_iff_of_injective [Field k] [Unique σ] [Fintype ι] {P : ι → σ → k}
    (hP : Function.Injective P) (d : ℕ) :
    WellPoised P d ↔ 2 * Fintype.card ι ≤ d + 1 :=
  wellPoised_unique_iff
    ((pairwise_exists_isUnit_sub_of_injective hP).mono fun _ _ ⟨s, hs⟩ ↦
      Unique.eq_default s ▸ hs)
    d

end Univariate

end MvPolynomial
