/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import TauCeti.RingTheory.MvPolynomial.FirstJet.Algebra
public import TauCeti.RingTheory.MvPolynomial.HasseDeriv.JetEvaluation
public import TauCeti.RingTheory.MvPolynomial.RestrictTotalDegree
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.NormNum

/-!
# Bounded first-jet evaluation, matrix rank, and well-poised configurations

For a family of affine points `P : ι → σ → R` over a commutative semiring `R` and a total-degree
bound `d`, the bounded first-jet evaluation map
`MvPolynomial.firstJetMap P d : restrictTotalDegree σ R d →ₗ[R] ι → Option σ → R` sends a
polynomial `f` of total degree at most `d` to its values `eval (P i) f` at `none` and its partial
derivatives `eval (P i) (pderiv j f)` at `some j`. It is built directly from the Hasse jet map
`MvPolynomial.jetEval` on `{a : σ →₀ ℕ | a.degree ≤ d}` using `0` and `Finsupp.single j 1` as
multi-indices, so its monomial matrix `MvPolynomial.firstJetMatrix P d` inherits matrix
representation, vector multiplication, and base-change naturality from `MvPolynomial.jetMatrix`.

Projecting onto the `none` coordinates gives the value evaluation map
`MvPolynomial.firstJetValueMap P d`, and restricting the `some` coordinates to its kernel gives
`MvPolynomial.firstJetDerivativeOnKernel P d`. Over any commutative ring, `firstJetMap P d` is
surjective if and only if both `firstJetValueMap P d` and `firstJetDerivativeOnKernel P d` are
surjective (`MvPolynomial.surjective_firstJetMap_iff`). Over a field `k`, the rank of
`firstJetMatrix P d` equals the dimension of the range of `firstJetMap P d`, so well-poisedness
(`MvPolynomial.WellPoised P d`, defined as surjectivity of `firstJetMap P d`) is equivalent to full
row rank `Fintype.card ι * (Fintype.card σ + 1)`.

## Main definitions

* `MvPolynomial.firstJetMap`: bounded first-jet evaluation
  `restrictTotalDegree σ R d →ₗ[R] ι → Option σ → R`.
* `MvPolynomial.firstJetValueMap`: the value projection `restrictTotalDegree σ R d →ₗ[R] ι → R`.
* `MvPolynomial.firstJetDerivativeOnKernel`: first partial derivatives restricted to
  `LinearMap.ker (firstJetValueMap P d)`.
* `MvPolynomial.firstJetMatrix`: the monomial-basis matrix of `firstJetMap P d`.
* `MvPolynomial.WellPoised`: surjectivity of `firstJetMap P d`.

## Main results

* `MvPolynomial.mem_ker_firstJetMap_iff_mem_doubleIdeal`: for pairwise comaximal (in particular,
  distinct over a field) points, the kernel of `firstJetMap P d` is `doubleIdeal P` intersected
  with `restrictTotalDegree σ R d`.
* `MvPolynomial.wellPoised_iff_surjective_quotientMk`: well-poisedness is equivalent to
  surjectivity of the quotient map `restrictTotalDegree σ k d → MvPolynomial σ k ⧸ doubleIdeal P`.
* `MvPolynomial.surjective_firstJetMap_iff`: surjectivity of `firstJetMap P d` via the value map
  and derivatives on the value kernel.
* `MvPolynomial.toMatrix_firstJetMap`, `MvPolynomial.firstJetMap_eq_mulVec`,
  `MvPolynomial.firstJetMatrix_map`: matrix representation and naturality.
* `MvPolynomial.rank_firstJetMatrix_eq_finrank_range`,
  `MvPolynomial.surjective_firstJetMap_iff_rank_eq`, `MvPolynomial.wellPoised_iff_rank_eq`,
  `MvPolynomial.injective_firstJetMap_iff_rank_eq`: rank criteria for surjectivity,
  well-poisedness, and injectivity.
* `MvPolynomial.WellPoised.mono_degree`, `MvPolynomial.WellPoised.comp_injective`,
  `MvPolynomial.WellPoised.injective`, `MvPolynomial.WellPoised.card_mul_le`: structural
  properties of well-poised configurations.

## References

* J.-M. Couveignes, *Enumerating number fields*, Annals of Mathematics 192 (2020), 487–497, §3.
* M. C. Brambilla and G. Ottaviani, *On the Alexander–Hirschowitz Theorem*, J. Pure Appl. Algebra
  212 (2008), 1229–1251 (arXiv:math/0701409v2), §§1–2.
-/

public section

namespace MvPolynomial

open Matrix

section Basic

variable {σ ι κ R S : Type*} [CommSemiring R] [CommSemiring S]

private theorem hasseDeriv_single_one (j : σ) (f : MvPolynomial σ R) :
    hasseDeriv (Finsupp.single j 1) f = pderiv j f := by
  simpa using factorial_smul_hasseDeriv_single j 1 f

/-- Bounded first-jet evaluation: sends a polynomial `f` of total degree at most `d` to its values
`eval (P i) f` at `none` and its partial derivatives `eval (P i) (pderiv j f)` at `some j`. -/
noncomputable def firstJetMap (P : ι → σ → R) (d : ℕ) :
    restrictTotalDegree σ R d →ₗ[R] (ι → Option σ → R) :=
  (LinearEquiv.curry R R ι (Option σ)).toLinearMap ∘ₗ
    jetEval {a : σ →₀ ℕ | a.degree ≤ d} (fun z : ι × Option σ ↦ P z.1)
      (fun z ↦ z.2.elim 0 (Finsupp.single · 1)) ∘ₗ
    (LinearEquiv.ofEq _ _ (restrictTotalDegree_eq_restrictSupport σ R d)).toLinearMap

@[simp]
theorem firstJetMap_apply_none (P : ι → σ → R) (d : ℕ) (f : restrictTotalDegree σ R d) (i : ι) :
    firstJetMap P d f i none = eval (P i) (f : MvPolynomial σ R) := by
  simp [firstJetMap]

@[simp]
theorem firstJetMap_apply_some (P : ι → σ → R) (d : ℕ) (f : restrictTotalDegree σ R d)
    (i : ι) (j : σ) :
    firstJetMap P d f i (some j) = eval (P i) (pderiv j (f : MvPolynomial σ R)) := by
  simp [firstJetMap, hasseDeriv_single_one]

/-- The `none` coordinate of `firstJetMap P d f i` is the scalar component of `jetAlgebra`. -/
theorem firstJetMap_apply_none_eq_fst_jetAlgebra (P : ι → σ → R) (d : ℕ)
    (f : restrictTotalDegree σ R d) (i : ι) :
    firstJetMap P d f i none = (jetAlgebra (P i) (f : MvPolynomial σ R)).fst := by
  simp

/-- The `some j` coordinate of `firstJetMap P d f i` is the `j`-th infinitesimal component of
`jetAlgebra`. -/
theorem firstJetMap_apply_some_eq_snd_jetAlgebra (P : ι → σ → R) (d : ℕ)
    (f : restrictTotalDegree σ R d) (i : ι) (j : σ) :
    firstJetMap P d f i (some j) = (jetAlgebra (P i) (f : MvPolynomial σ R)).snd j := by
  simp

/-- A bounded polynomial lies in `LinearMap.ker (firstJetMap P d)` if and only if its value and
all first partial derivatives vanish at every point `P i`. -/
theorem mem_ker_firstJetMap {P : ι → σ → R} {d : ℕ} {f : restrictTotalDegree σ R d} :
    f ∈ LinearMap.ker (firstJetMap P d) ↔
      ∀ i, eval (P i) (f : MvPolynomial σ R) = 0 ∧
        ∀ j, eval (P i) (pderiv j (f : MvPolynomial σ R)) = 0 := by
  rw [LinearMap.mem_ker, _root_.funext_iff]
  simp only [Pi.zero_apply, _root_.funext_iff, Option.forall, firstJetMap_apply_none,
    firstJetMap_apply_some]

/-- Raising the degree bound does not change the first jet of a polynomial. -/
theorem firstJetMap_comp_inclusion (P : ι → σ → R) {d e : ℕ} (h : d ≤ e)
    (f : restrictTotalDegree σ R d) :
    firstJetMap P e (Submodule.inclusion (restrictTotalDegree_mono σ R h) f) =
      firstJetMap P d f := by
  ext i z
  cases z <;> simp

/-- Reindexing points along an equivalence reindexes the output of `firstJetMap`. -/
@[simp]
theorem firstJetMap_comp_equiv (P : ι → σ → R) (e : κ ≃ ι) (d : ℕ)
    (f : restrictTotalDegree σ R d) (j : κ) :
    firstJetMap (P ∘ e) d f j = firstJetMap P d f (e j) := by
  ext z
  cases z <;> simp

/-- Naturality of `firstJetMap` under a change of coefficients `φ : R →+* S`. -/
theorem firstJetMap_map (φ : R →+* S) (P : ι → σ → R) (d : ℕ) (f : restrictTotalDegree σ R d)
    (i : ι) (z : Option σ) :
    firstJetMap (fun i ↦ φ ∘ P i) d
        ⟨map φ (f : MvPolynomial σ R),
          (restrictTotalDegree_eq_restrictSupport σ S d).symm ▸
            map_mem_restrictSupport φ ((restrictTotalDegree_eq_restrictSupport σ R d) ▸ f.2)⟩
        i z =
      φ (firstJetMap P d f i z) := by
  have h := congrFun (jetEval_mapRestrictSupport {a : σ →₀ ℕ | a.degree ≤ d}
    (fun z : ι × Option σ ↦ P z.1) (fun z ↦ z.2.elim 0 (Finsupp.single · 1)) φ
    ((LinearEquiv.ofEq _ _ (restrictTotalDegree_eq_restrictSupport σ R d)) f)) (i, z)
  simpa [firstJetMap] using h

/-- The value projection of `firstJetMap P d`, sending a bounded polynomial `f` to
`fun i ↦ eval (P i) f`. -/
noncomputable def firstJetValueMap (P : ι → σ → R) (d : ℕ) :
    restrictTotalDegree σ R d →ₗ[R] (ι → R) :=
  (LinearMap.pi fun i ↦ LinearMap.proj (none : Option σ) ∘ₗ LinearMap.proj i) ∘ₗ firstJetMap P d

@[simp]
theorem firstJetValueMap_apply (P : ι → σ → R) (d : ℕ) (f : restrictTotalDegree σ R d) (i : ι) :
    firstJetValueMap P d f i = eval (P i) (f : MvPolynomial σ R) := by
  simp [firstJetValueMap]

/-- `firstJetValueMap P d` is the `none`-coordinate projection of `firstJetMap P d`. -/
theorem firstJetValueMap_eq_firstJetMap_none (P : ι → σ → R) (d : ℕ)
    (f : restrictTotalDegree σ R d) (i : ι) :
    firstJetValueMap P d f i = firstJetMap P d f i none := by
  simp

theorem mem_ker_firstJetValueMap {P : ι → σ → R} {d : ℕ} {f : restrictTotalDegree σ R d} :
    f ∈ LinearMap.ker (firstJetValueMap P d) ↔ ∀ i, eval (P i) (f : MvPolynomial σ R) = 0 := by
  rw [LinearMap.mem_ker, _root_.funext_iff]
  simp

/-- The partial-derivative evaluation map restricted to bounded polynomials vanishing at every
point `P i`. -/
noncomputable def firstJetDerivativeOnKernel (P : ι → σ → R) (d : ℕ) :
    LinearMap.ker (firstJetValueMap P d) →ₗ[R] (ι → σ → R) :=
  (LinearMap.pi fun i ↦ LinearMap.pi fun j ↦
      LinearMap.proj (some j : Option σ) ∘ₗ LinearMap.proj i) ∘ₗ
    firstJetMap P d ∘ₗ (LinearMap.ker (firstJetValueMap P d)).subtype

@[simp]
theorem firstJetDerivativeOnKernel_apply (P : ι → σ → R) (d : ℕ)
    (f : LinearMap.ker (firstJetValueMap P d)) (i : ι) (j : σ) :
    firstJetDerivativeOnKernel P d f i j = eval (P i) (pderiv j (f.1 : MvPolynomial σ R)) := by
  simp [firstJetDerivativeOnKernel]

theorem firstJetDerivativeOnKernel_eq_firstJetMap_some (P : ι → σ → R) (d : ℕ)
    (f : LinearMap.ker (firstJetValueMap P d)) (i : ι) (j : σ) :
    firstJetDerivativeOnKernel P d f i j = firstJetMap P d f.1 i (some j) := by
  simp

/-- The monomial-basis matrix of `firstJetMap P d`, with rows indexed by `ι × Option σ` and
columns indexed by bounded exponents `{a : σ →₀ ℕ // a.degree ≤ d}`. -/
noncomputable def firstJetMatrix (P : ι → σ → R) (d : ℕ) :
    Matrix (ι × Option σ) {a : σ →₀ ℕ // a.degree ≤ d} R :=
  jetMatrix {a : σ →₀ ℕ | a.degree ≤ d} (fun z : ι × Option σ ↦ P z.1)
    (fun z ↦ z.2.elim 0 (Finsupp.single · 1))

@[simp]
theorem firstJetMatrix_apply_none (P : ι → σ → R) (d : ℕ) (i : ι)
    (a : {a : σ →₀ ℕ // a.degree ≤ d}) :
    firstJetMatrix P d (i, none) a = eval (P i) (monomial a.1 1) := by
  simp [firstJetMatrix]

@[simp]
theorem firstJetMatrix_apply_some (P : ι → σ → R) (d : ℕ) (i : ι) (j : σ)
    (a : {a : σ →₀ ℕ // a.degree ≤ d}) :
    firstJetMatrix P d (i, some j) a = eval (P i) (pderiv j (monomial a.1 1)) := by
  simp [firstJetMatrix]

/-- Value-row entries of `firstJetMatrix`: `P i ^ a`. -/
theorem firstJetMatrix_apply_none_eq_prod (P : ι → σ → R) (d : ℕ) (i : ι)
    (a : {a : σ →₀ ℕ // a.degree ≤ d}) :
    firstJetMatrix P d (i, none) a = a.1.prod fun l e ↦ P i l ^ e := by
  simp [eval_monomial]

/-- Derivative-row entries of `firstJetMatrix`: `(a j) * P i ^ (a - eⱼ)`, which is `0` when
`a j = 0`. -/
theorem firstJetMatrix_apply_some_eq_mul_prod (P : ι → σ → R) (d : ℕ) (i : ι) (j : σ)
    (a : {a : σ →₀ ℕ // a.degree ≤ d}) :
    firstJetMatrix P d (i, some j) a =
      (a.1 j : R) * (a.1 - Finsupp.single j 1).prod fun l e ↦ P i l ^ e := by
  simpa [firstJetMatrix] using
    jetMatrix_apply {a : σ →₀ ℕ | a.degree ≤ d} (fun z : ι × Option σ ↦ P z.1)
      (fun z ↦ z.2.elim 0 (Finsupp.single · 1)) (i, some j) a

/-- `firstJetMatrix P d` is the matrix of `firstJetMap P d` (uncurried) in the monomial basis of
`restrictTotalDegree σ R d` and the standard basis of `ι × Option σ → R`. -/
theorem toMatrix_firstJetMap [Finite σ] [Finite ι] {d : ℕ}
    [Fintype {a : σ →₀ ℕ // a.degree ≤ d}] [DecidableEq {a : σ →₀ ℕ // a.degree ≤ d}]
    (P : ι → σ → R) :
    LinearMap.toMatrix (basisRestrictTotalDegree σ R d) (Pi.basisFun R (ι × Option σ))
      ((LinearEquiv.curry R R ι (Option σ)).symm.toLinearMap ∘ₗ firstJetMap P d) =
      firstJetMatrix P d := by
  ext ⟨i, z⟩ a
  cases z <;> simp [LinearMap.toMatrix_apply]

/-- Applying `firstJetMatrix P d` to the coefficient vector of a bounded polynomial `f` computes
`firstJetMap P d f`. -/
theorem firstJetMap_eq_mulVec {d : ℕ} [Fintype {a : σ →₀ ℕ // a.degree ≤ d}]
    (P : ι → σ → R) (f : restrictTotalDegree σ R d) (i : ι) (z : Option σ) :
    firstJetMap P d f i z =
      (firstJetMatrix P d *ᵥ fun a ↦ (f : MvPolynomial σ R).coeff a.1) (i, z) := by
  have h := congrFun
    (jetEval_eq_mulVec {a : σ →₀ ℕ | a.degree ≤ d} (fun z : ι × Option σ ↦ P z.1)
      (fun z ↦ z.2.elim 0 (Finsupp.single · 1))
      ((LinearEquiv.ofEq _ _ (restrictTotalDegree_eq_restrictSupport σ R d)) f)) (i, z)
  rw [firstJetMap, firstJetMatrix]
  exact h

/-- Naturality of `firstJetMatrix` under a ring homomorphism `φ : R →+* S`. -/
theorem firstJetMatrix_map (φ : R →+* S) (P : ι → σ → R) (d : ℕ) :
    firstJetMatrix (fun i ↦ φ ∘ P i) d = (firstJetMatrix P d).map φ :=
  jetMatrix_map _ _ _ φ

/-- Reindexing points along an equivalence permutes the rows of `firstJetMatrix`. -/
theorem firstJetMatrix_comp_equiv (P : ι → σ → R) (e : κ ≃ ι) (d : ℕ) :
    firstJetMatrix (P ∘ e) d = (firstJetMatrix P d).submatrix (Prod.map e id) id := by
  ext ⟨j, z⟩ a
  cases z <;> simp

/-- The rank of `firstJetMatrix P d` equals the `finrank` of the range of `firstJetMap P d`. -/
theorem rank_firstJetMatrix_eq_finrank_range {d : ℕ} [Fintype {a : σ →₀ ℕ // a.degree ≤ d}]
    (P : ι → σ → R) :
    (firstJetMatrix P d).rank = Module.finrank R (LinearMap.range (firstJetMap P d)) := by
  let eDom : restrictTotalDegree σ R d ≃ₗ[R] ({a : σ →₀ ℕ // a.degree ≤ d} → R) :=
    (basisRestrictTotalDegree σ R d).equivFun
  let eCod : (ι × Option σ → R) ≃ₗ[R] (ι → Option σ → R) := LinearEquiv.curry R R ι (Option σ)
  have hcomp : firstJetMap P d =
      eCod.toLinearMap ∘ₗ (firstJetMatrix P d).mulVecLin ∘ₗ eDom.toLinearMap := by
    ext f i z
    have hcoeff : (fun a ↦ (eDom f) a) = fun a ↦ (f : MvPolynomial σ R).coeff a.1 :=
      _root_.funext fun a ↦ basisRestrictTotalDegree_repr_apply d f a
    simpa [eDom, eCod, hcoeff] using firstJetMap_eq_mulVec P f i z
  have hrange : LinearMap.range (firstJetMap P d) =
      (LinearMap.range (firstJetMatrix P d).mulVecLin).map eCod.toLinearMap := by
    rw [hcomp, LinearMap.range_comp, LinearMap.range_comp_of_range_eq_top _ eDom.range]
  rw [Matrix.rank, hrange]
  exact (eCod.submoduleMap (LinearMap.range (firstJetMatrix P d).mulVecLin)).finrank_eq

/-- Reindexing points along an equivalence preserves the rank of `firstJetMatrix`. -/
theorem rank_firstJetMatrix_comp_equiv {d : ℕ} [Fintype {a : σ →₀ ℕ // a.degree ≤ d}]
    (P : ι → σ → R) (e : κ ≃ ι) :
    (firstJetMatrix (P ∘ e) d).rank = (firstJetMatrix P d).rank := by
  rw [rank_firstJetMatrix_eq_finrank_range, rank_firstJetMatrix_eq_finrank_range]
  let eCod : (ι → Option σ → R) ≃ₗ[R] (κ → Option σ → R) :=
    LinearEquiv.funCongrLeft R (Option σ → R) e
  have hcomp : firstJetMap (P ∘ e) d = eCod.toLinearMap ∘ₗ firstJetMap P d := by
    ext f j z
    simp [eCod]
  rw [hcomp, LinearMap.range_comp]
  exact (eCod.submoduleMap (LinearMap.range (firstJetMap P d))).finrank_eq.symm

end Basic

section CommRing

variable {σ ι R : Type*} [CommRing R]

/-- For a finite family of points with pairwise comaximal evaluation ideals, a bounded polynomial
lies in the kernel of `firstJetMap P d` if and only if it lies in `doubleIdeal P`. -/
theorem mem_ker_firstJetMap_iff_mem_doubleIdeal_of_pairwise [Finite ι] {P : ι → σ → R}
    (hP : Pairwise (Function.onFun IsCoprime fun i ↦ RingHom.ker (eval (P i)))) {d : ℕ}
    {f : restrictTotalDegree σ R d} :
    f ∈ LinearMap.ker (firstJetMap P d) ↔ (f : MvPolynomial σ R) ∈ doubleIdeal P := by
  rw [mem_ker_firstJetMap, mem_doubleIdeal_iff_of_pairwise hP]

/-- **Surjectivity through the value kernel.** Over any commutative ring, `firstJetMap P d` is
surjective if and only if the value map `firstJetValueMap P d` is surjective and the partial
derivative map `firstJetDerivativeOnKernel P d` on its kernel is surjective. -/
theorem surjective_firstJetMap_iff (P : ι → σ → R) (d : ℕ) :
    Function.Surjective (firstJetMap P d) ↔
      Function.Surjective (firstJetValueMap P d) ∧
        Function.Surjective (firstJetDerivativeOnKernel P d) := by
  constructor
  · intro h
    refine ⟨fun v ↦ ?_, fun w ↦ ?_⟩
    · obtain ⟨f, hf⟩ := h fun i z ↦ z.elim (v i) fun _ ↦ 0
      refine ⟨f, _root_.funext fun i ↦ ?_⟩
      simpa using congrFun (congrFun hf i) none
    · obtain ⟨f, hf⟩ := h fun i z ↦ z.elim 0 (w i)
      have hker : f ∈ LinearMap.ker (firstJetValueMap P d) := by
        rw [mem_ker_firstJetValueMap]
        intro i
        simpa using congrFun (congrFun hf i) none
      refine ⟨⟨f, hker⟩, _root_.funext fun i ↦ _root_.funext fun j ↦ ?_⟩
      simpa using congrFun (congrFun hf i) (some j)
  · rintro ⟨hv, hd⟩ y
    obtain ⟨f₀, hf₀⟩ := hv fun i ↦ y i none
    obtain ⟨⟨g, hg⟩, hgd⟩ := hd fun i j ↦ y i (some j) - firstJetMap P d f₀ i (some j)
    refine ⟨f₀ + g, _root_.funext fun i ↦ _root_.funext fun z ↦ ?_⟩
    cases z with
    | none =>
      have h0 : eval (P i) (f₀ : MvPolynomial σ R) = y i none := by
        simpa using congrFun hf₀ i
      have hg0 : eval (P i) (g : MvPolynomial σ R) = 0 := mem_ker_firstJetValueMap.1 hg i
      simp [h0, hg0]
    | some j =>
      have h1 : eval (P i) (pderiv j (g : MvPolynomial σ R)) =
          y i (some j) - firstJetMap P d f₀ i (some j) := by
        simpa using congrFun (congrFun hgd i) j
      simp [h1]

end CommRing

section WellPoised

variable {σ ι κ R : Type*} [CommSemiring R]

/-- A tuple of points `P : ι → σ → R` is well poised in degree `d` when every prescribed tuple of
values and first partial derivatives at the points `P i` is attained by a polynomial of total
degree at most `d`. -/
def WellPoised (P : ι → σ → R) (d : ℕ) : Prop :=
  Function.Surjective (firstJetMap P d)

theorem wellPoised_iff (P : ι → σ → R) (d : ℕ) :
    WellPoised P d ↔ Function.Surjective (firstJetMap P d) :=
  Iff.rfl

theorem wellPoised_iff_surjective_value_and_derivative {R : Type*} [CommRing R]
    (P : ι → σ → R) (d : ℕ) :
    WellPoised P d ↔
      Function.Surjective (firstJetValueMap P d) ∧
        Function.Surjective (firstJetDerivativeOnKernel P d) :=
  surjective_firstJetMap_iff P d

/-- For pairwise comaximal point ideals in finitely many variables, well-poisedness in degree `d`
is equivalent to surjectivity of the quotient map
`MvPolynomial σ R → MvPolynomial σ R ⧸ doubleIdeal P` restricted to `restrictTotalDegree σ R d`. -/
theorem wellPoised_iff_surjective_quotientMk_of_pairwise {R : Type*} [CommRing R]
    [Finite σ] [Finite ι] {P : ι → σ → R}
    (hP : Pairwise (Function.onFun IsCoprime fun i ↦ RingHom.ker (eval (P i)))) (d : ℕ) :
    WellPoised P d ↔
      Function.Surjective
        ((Ideal.Quotient.mkₐ R (doubleIdeal P)).toLinearMap ∘ₗ
          (restrictTotalDegree σ R d).subtype) := by
  let e : (ι → TrivSqZeroExt R (σ → R)) ≃ₗ[R] (ι → Option σ → R) :=
    { toFun := fun v i z ↦ z.elim (v i).fst (v i).snd
      invFun := fun y i ↦ TrivSqZeroExt.inl (y i none) + TrivSqZeroExt.inr fun j ↦ y i (some j)
      left_inv := fun v ↦ _root_.funext fun i ↦ by ext <;> simp
      right_inv := fun y ↦ _root_.funext fun i ↦ _root_.funext fun z ↦ by cases z <;> simp
      map_add' := fun _ _ ↦ _root_.funext fun _ ↦ _root_.funext fun z ↦ by cases z <;> rfl
      map_smul' := fun _ _ ↦ _root_.funext fun _ ↦ _root_.funext fun z ↦ by cases z <;> rfl }
  have hcomp : firstJetMap P d =
      e.toLinearMap ∘ₗ (doublePointQuotientEquivOfPairwise hP).toLinearMap ∘ₗ
        (Ideal.Quotient.mkₐ R (doubleIdeal P)).toLinearMap ∘ₗ
        (restrictTotalDegree σ R d).subtype := by
    ext f i z
    cases z <;> simp [e]
  rw [WellPoised, hcomp]
  refine ⟨fun hs y ↦ ?_,
    fun hs ↦ e.surjective.comp ((doublePointQuotientEquivOfPairwise hP).surjective.comp hs)⟩
  obtain ⟨f, hf⟩ := hs (e (doublePointQuotientEquivOfPairwise hP y))
  exact ⟨f, (doublePointQuotientEquivOfPairwise hP).injective (e.injective hf)⟩

/-- Raising the degree bound preserves well-poisedness. -/
theorem WellPoised.mono_degree {P : ι → σ → R} {d e : ℕ} (h : WellPoised P d) (hde : d ≤ e) :
    WellPoised P e := fun y ↦ by
  obtain ⟨f, hf⟩ := h y
  exact ⟨Submodule.inclusion (restrictTotalDegree_mono σ R hde) f, by
    rw [firstJetMap_comp_inclusion P hde, hf]⟩

/-- Passing to an injectively indexed subfamily preserves well-poisedness. -/
theorem WellPoised.comp_injective {P : ι → σ → R} {d : ℕ} (h : WellPoised P d)
    {g : κ → ι} (hg : Function.Injective g) :
    WellPoised (P ∘ g) d := fun y ↦ by
  classical
  obtain ⟨f, hf⟩ := h (Function.extend g y 0)
  refine ⟨f, _root_.funext fun k ↦ _root_.funext fun z ↦ ?_⟩
  have hkz := congrFun (congrFun hf (g k)) z
  rw [hg.extend_apply] at hkz
  cases z <;> simpa using hkz

/-- Reindexing a point tuple along an equivalence preserves well-poisedness. -/
theorem WellPoised.comp_equiv {P : ι → σ → R} {d : ℕ} (h : WellPoised P d) (e : κ ≃ ι) :
    WellPoised (P ∘ e) d :=
  h.comp_injective e.injective

theorem wellPoised_comp_equiv_iff (P : ι → σ → R) (e : κ ≃ ι) (d : ℕ) :
    WellPoised (P ∘ e) d ↔ WellPoised P d :=
  ⟨fun h ↦ by simpa [Function.comp_assoc] using h.comp_equiv e.symm, fun h ↦ h.comp_equiv e⟩

/-- Over a nontrivial commutative semiring, a well-poised tuple must consist of distinct points. -/
theorem WellPoised.injective [Nontrivial R] {P : ι → σ → R} {d : ℕ} (h : WellPoised P d) :
    Function.Injective P := by
  classical
  intro i j hij
  by_contra hne
  obtain ⟨f, hf⟩ := h (Function.update 0 i fun _ ↦ 1)
  have hi : eval (P i) (f : MvPolynomial σ R) = 1 := by
    simpa using congrFun (congrFun hf i) none
  have hj : eval (P j) (f : MvPolynomial σ R) = 0 := by
    simpa [Function.update_of_ne (Ne.symm hne)] using congrFun (congrFun hf j) none
  rw [hij, hj] at hi
  exact zero_ne_one hi

/-- The empty tuple is well poised in every degree. -/
theorem wellPoised_of_isEmpty [IsEmpty ι] (P : ι → σ → R) (d : ℕ) : WellPoised P d :=
  fun _ ↦ ⟨0, _root_.funext fun i ↦ isEmptyElim i⟩

/-- In degree zero, no nonempty tuple in at least one variable is well poised over a nontrivial
semiring, because all partial derivatives of constants vanish. -/
theorem not_wellPoised_zero [Nontrivial R] [Nonempty ι] [Nonempty σ] (P : ι → σ → R) :
    ¬ WellPoised P 0 := by
  intro h
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  obtain ⟨j₀⟩ := ‹Nonempty σ›
  obtain ⟨f, hf⟩ := h fun _ _ ↦ 1
  have hdeg : (f : MvPolynomial σ R).totalDegree = 0 :=
    Nat.eq_zero_of_le_zero ((mem_restrictTotalDegree σ 0 _).1 f.2)
  have hp0 : pderiv j₀ (f : MvPolynomial σ R) = 0 := by
    rw [totalDegree_eq_zero_iff_eq_C.1 hdeg, pderiv_C]
  have h1 := congrFun (congrFun hf i₀) (some j₀)
  simp [hp0] at h1

/-- Over a commutative ring, a tuple of at most one point in finitely many variables is well poised
in every degree `d ≥ 1`. -/
theorem wellPoised_of_subsingleton {R : Type*} [CommRing R] [Finite σ] [Subsingleton ι]
    (P : ι → σ → R) {d : ℕ} (hd : 1 ≤ d) : WellPoised P d := by
  rcases isEmpty_or_nonempty ι with _ | ⟨⟨i₀⟩⟩
  · exact wellPoised_of_isEmpty P d
  · cases nonempty_fintype σ
    intro y
    let p : MvPolynomial σ R :=
      C (y i₀ none) + ∑ j, C (y i₀ (some j)) * (X j - C (P i₀ j))
    have hp : p ∈ restrictTotalDegree σ R d := by
      rw [mem_restrictTotalDegree]
      refine (totalDegree_add _ _).trans (max_le (by simp) ?_)
      refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun j _ ↦ ?_)
      refine (totalDegree_mul _ _).trans ?_
      rw [totalDegree_C, zero_add]
      have hXj : (X j : MvPolynomial σ R).totalDegree ≤ 1 :=
        (totalDegree_monomial_le _ _).trans_eq (by simp)
      exact (totalDegree_sub _ _).trans (max_le (hXj.trans hd) (by simp))
    refine ⟨⟨p, hp⟩, _root_.funext fun i ↦ _root_.funext fun z ↦ ?_⟩
    rw [Subsingleton.elim i i₀]
    cases z with
    | none => simp [p]
    | some j =>
      rw [firstJetMap_apply_some]
      simp only [p, map_add, pderiv_C, zero_add, map_sum, pderiv_mul, zero_mul, map_sub, sub_zero,
        map_mul, eval_C]
      rw [Finset.sum_eq_single j]
      · simp
      · intro l _ hlj
        simp [pderiv_X_of_ne hlj]
      · intro hj
        exact absurd (Finset.mem_univ j) hj

end WellPoised

section Field

variable {σ ι k : Type*} [Field k]

/-- Over a field, for a finite injective tuple `P`, a bounded polynomial lies in the kernel of
`firstJetMap P d` if and only if it lies in `doubleIdeal P`. -/
theorem mem_ker_firstJetMap_iff_mem_doubleIdeal [Finite ι] {P : ι → σ → k}
    (hP : Function.Injective P) {d : ℕ} {f : restrictTotalDegree σ k d} :
    f ∈ LinearMap.ker (firstJetMap P d) ↔ (f : MvPolynomial σ k) ∈ doubleIdeal P :=
  mem_ker_firstJetMap_iff_mem_doubleIdeal_of_pairwise
    (fun _ _ hij ↦ isCoprime_ker_eval (hP.ne hij))

/-- Over a field, a finite injective tuple `P` is well poised in degree `d` if and only if the
quotient map `MvPolynomial σ k → MvPolynomial σ k ⧸ doubleIdeal P` is surjective on
`restrictTotalDegree σ k d`. -/
theorem wellPoised_iff_surjective_quotientMk [Finite σ] [Finite ι] {P : ι → σ → k}
    (hP : Function.Injective P) (d : ℕ) :
    WellPoised P d ↔
      Function.Surjective
        ((Ideal.Quotient.mkₐ k (doubleIdeal P)).toLinearMap ∘ₗ
          (restrictTotalDegree σ k d).subtype) :=
  wellPoised_iff_surjective_quotientMk_of_pairwise
    (fun _ _ hij ↦ isCoprime_ker_eval (hP.ne hij)) d

/-- The rank of `firstJetMatrix P d` is bounded above by the minimum of the source polynomial
dimension `(d + r choose r)` and the target jet dimension `n * (r + 1)`. -/
theorem rank_firstJetMatrix_le [Fintype σ] [Fintype ι] {d : ℕ}
    [Fintype {a : σ →₀ ℕ // a.degree ≤ d}] (P : ι → σ → k) :
    (firstJetMatrix P d).rank ≤
      min ((d + Fintype.card σ).choose (Fintype.card σ))
        (Fintype.card ι * (Fintype.card σ + 1)) := by
  have : Module.Finite k (restrictTotalDegree σ k d) :=
    Module.Finite.of_basis (basisRestrictTotalDegree σ k d)
  rw [rank_firstJetMatrix_eq_finrank_range]
  refine le_min ?_ ?_
  · have hrn := LinearMap.finrank_range_add_finrank_ker (firstJetMap P d)
    have hdom : Module.finrank k (restrictTotalDegree σ k d) =
        (d + Fintype.card σ).choose (Fintype.card σ) :=
      TauCeti.finrank_restrictTotalDegree σ k d
    omega
  · calc
      Module.finrank k (LinearMap.range (firstJetMap P d))
        ≤ Module.finrank k (ι → Option σ → k) := Submodule.finrank_le _
      _ = Fintype.card ι * (Fintype.card σ + 1) := by
        simp [Module.finrank_pi_fintype, Fintype.card_option]

/-- **Full row rank criterion.** Over a field, `firstJetMap P d` is surjective if and only if
`firstJetMatrix P d` has rank `Fintype.card ι * (Fintype.card σ + 1)`. -/
theorem surjective_firstJetMap_iff_rank_eq [Fintype σ] [Fintype ι] {d : ℕ}
    [Fintype {a : σ →₀ ℕ // a.degree ≤ d}] (P : ι → σ → k) :
    Function.Surjective (firstJetMap P d) ↔
      (firstJetMatrix P d).rank = Fintype.card ι * (Fintype.card σ + 1) := by
  rw [← LinearMap.range_eq_top, Submodule.eq_top_iff_finrank_eq,
    rank_firstJetMatrix_eq_finrank_range]
  simp [Module.finrank_pi_fintype, Fintype.card_option]

/-- Over a field, `P` is well poised in degree `d` if and only if `firstJetMatrix P d` has full
row rank `Fintype.card ι * (Fintype.card σ + 1)`. -/
theorem wellPoised_iff_rank_eq [Fintype σ] [Fintype ι] {d : ℕ}
    [Fintype {a : σ →₀ ℕ // a.degree ≤ d}] (P : ι → σ → k) :
    WellPoised P d ↔ (firstJetMatrix P d).rank = Fintype.card ι * (Fintype.card σ + 1) :=
  surjective_firstJetMap_iff_rank_eq P

/-- **Full column rank criterion.** Over a field, `firstJetMap P d` is injective if and only if
`firstJetMatrix P d` has rank `(d + Fintype.card σ).choose (Fintype.card σ)`. -/
theorem injective_firstJetMap_iff_rank_eq [Fintype σ] {d : ℕ}
    [Fintype {a : σ →₀ ℕ // a.degree ≤ d}] (P : ι → σ → k) :
    Function.Injective (firstJetMap P d) ↔
      (firstJetMatrix P d).rank = (d + Fintype.card σ).choose (Fintype.card σ) := by
  have : Module.Finite k (restrictTotalDegree σ k d) :=
    Module.Finite.of_basis (basisRestrictTotalDegree σ k d)
  rw [← LinearMap.ker_eq_bot, rank_firstJetMatrix_eq_finrank_range]
  have hrn := LinearMap.finrank_range_add_finrank_ker (firstJetMap P d)
  have hdom : Module.finrank k (restrictTotalDegree σ k d) =
      (d + Fintype.card σ).choose (Fintype.card σ) :=
    TauCeti.finrank_restrictTotalDegree σ k d
  constructor
  · intro hker
    rw [hker, finrank_bot, add_zero] at hrn
    exact hrn.trans hdom
  · intro hrank
    have hker0 : Module.finrank k (LinearMap.ker (firstJetMap P d)) = 0 := by omega
    exact Submodule.finrank_eq_zero.1 hker0

/-- **Necessary dimension bound for well-poisedness.** If `P` is well poised in degree `d`, then
`Fintype.card ι * (Fintype.card σ + 1) ≤ (d + Fintype.card σ).choose (Fintype.card σ)`. -/
theorem WellPoised.card_mul_le [Fintype σ] [Fintype ι] {P : ι → σ → k} {d : ℕ}
    (h : WellPoised P d) :
    Fintype.card ι * (Fintype.card σ + 1) ≤ (d + Fintype.card σ).choose (Fintype.card σ) := by
  classical
  have hle := rank_firstJetMatrix_le (d := d) P
  rw [(wellPoised_iff_rank_eq P).1 h] at hle
  exact (le_min_iff.1 hle).1

end Field

/-! ### Examples -/

/-- For `f = X 0 ^ 2` at `P = 3` in `𝔸¹`, the first jet is `(9, 6)`. -/
example :
    let P : Fin 1 → Fin 1 → ℚ := fun _ _ ↦ 3
    let f : restrictTotalDegree (Fin 1) ℚ 2 :=
      ⟨X 0 ^ 2, (mem_restrictTotalDegree (Fin 1) 2 _).2 <|
        (totalDegree_pow _ _).trans (by simp [totalDegree_X])⟩
    firstJetMap P 2 f 0 none = 9 ∧ firstJetMap P 2 f 0 (some 0) = 6 := by
  intro P f
  refine ⟨?_, ?_⟩
  · simp [P, f]
    norm_num
  · simp [P, f, sq]
    norm_num

/-- One point at the origin in `𝔸²` is well poised in degree `1` and has first-jet rank `3`. -/
example :
    let P : Fin 1 → Fin 2 → ℚ := fun _ _ ↦ 0
    WellPoised P 1 ∧ (firstJetMatrix P 1).rank = 3 := by
  intro P
  have hw : WellPoised P 1 := wellPoised_of_subsingleton P le_rfl
  exact ⟨hw, by simpa using (wellPoised_iff_rank_eq P).1 hw⟩

end MvPolynomial
