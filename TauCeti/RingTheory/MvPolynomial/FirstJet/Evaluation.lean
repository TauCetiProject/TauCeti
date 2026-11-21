/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.Rank
public import TauCeti.RingTheory.MvPolynomial.HasseDeriv.JetEvaluation
public import TauCeti.RingTheory.MvPolynomial.RestrictTotalDegree
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Tactic.NormNum
import TauCeti.LinearAlgebra.Dimension.Submodule

/-!
# Interpolation of values and first derivatives by bounded-degree polynomials

Let `P : ι → σ → R` be a family of points and `d` a degree bound. The first-jet map
`TauCeti.firstJetMap P d` sends a polynomial `f` of total degree at most `d` to the family of its
values `f (P i)` and first partial derivatives `∂ⱼ f (P i)` at the points, with the rows of a
point indexed by `Option σ`: `none` selects the value and `some j` the `j`-th partial derivative.
It is the jet evaluation map `MvPolynomial.jetEval` with the Hasse derivative orders `0` and `eⱼ`
at each point. The family `P` is *well poised* in degree `d`, `TauCeti.WellPoised P d`, when every
prescription of values and first derivatives at the points is attained, that is, when the first-jet
map is surjective. This is Hermite interpolation with double points in several variables.

Surjectivity splits into two steps: the values can be prescribed, by
`TauCeti.firstJetValueMap`, and the derivatives of the polynomials vanishing at the points can be
prescribed, by `TauCeti.firstJetDerivMap` on the kernel of the value map. In the monomial
coordinates of `MvPolynomial.basisRestrictTotalDegree` the first-jet map is represented by the
matrix `TauCeti.firstJetMatrix P d`, the jet matrix `MvPolynomial.jetMatrix` of these orders,
whose `(i, none)` row lists the values `P i ^ α` of the monomials and whose `(i, some j)` row lists
their derivatives `αⱼ P i ^ (α - eⱼ)`. Its rank equals
`finrank R (LinearMap.range (firstJetMap P d))` (`TauCeti.rank_firstJetMatrix_eq_finrank_range`).
Over a commutative semiring satisfying `StrongRankCondition`, the rank is bounded by
`min ((d + r) choose r) (n * (r + 1))` and well-poisedness requires
`n * (r + 1) ≤ (d + r) choose r`; over a nontrivial commutative semiring satisfying
`OrzechProperty`, injectivity of `firstJetMap P d` is characterized by full column rank; and over a
field, well-poisedness is full row rank `n * (r + 1)`.

## Main definitions

* `TauCeti.firstJetMap P d`: values and first partial derivatives at the points `P i` of the
  polynomials of total degree at most `d`.
* `TauCeti.firstJetValueMap P d`, `TauCeti.firstJetDerivMap P d`: its value rows, and its
  derivative rows on the polynomials vanishing at every point.
* `TauCeti.firstJetMatrix P d`: the monomial matrix of the first-jet map.
* `TauCeti.WellPoised P d`: the first-jet map is surjective.

## Main results

* `TauCeti.mem_ker_firstJetMap`: characterization of `LinearMap.ker (firstJetMap P d)`.
* `TauCeti.firstJetMap_map`, `TauCeti.firstJetMatrix_map`: base-change naturality for the
  first-jet map and matrix.
* `TauCeti.firstJetMap_surjective_iff`: the first-jet map is onto iff the value map is onto and
  the derivative map on its kernel is onto.
* `TauCeti.toMatrix_firstJetMap`, `TauCeti.firstJetMatrix_mulVec`,
  `TauCeti.firstJetMap_surjective_iff_mulVec_surjective`: `firstJetMatrix P d` is the matrix of
  the uncurried first-jet map in the monomial basis.
* `TauCeti.rank_firstJetMatrix_eq_finrank_range`, `TauCeti.rank_firstJetMatrix_comp_equiv`:
  matrix rank equals range `finrank` and is invariant under reindexing.
* `TauCeti.rank_firstJetMatrix_le`, `TauCeti.injective_firstJetMap_iff_rank_eq`,
  `TauCeti.WellPoised.card_mul_le`: rank bounds and full-column-rank criterion over
  `StrongRankCondition` and `OrzechProperty` semirings.
* `TauCeti.wellPoised_iff`, `TauCeti.wellPoised_iff_rank`: well-poisedness and, over a field,
  its full-row-rank characterization.
* `TauCeti.WellPoised.mono`, `TauCeti.WellPoised.comp_injective`,
  `TauCeti.wellPoised_comp_equiv`, `TauCeti.WellPoised.injective`,
  `TauCeti.wellPoised_of_isEmpty`, `TauCeti.wellPoised_of_subsingleton`,
  `TauCeti.not_wellPoised_zero`: structural properties and small-tuple characterizations of
  well-poisedness.

## References

* J.-M. Couveignes, *Enumerating number fields*, Ann. of Math. 192 (2020), no. 2, 487–497, §3.
* M. C. Brambilla and G. Ottaviani, *On the Alexander–Hirschowitz Theorem*, J. Pure Appl. Algebra
  212 (2008), 1229–1251 (arXiv:math/0701409v2), §§1–2.
-/

public section

namespace TauCeti

open Matrix MvPolynomial

open scoped Matrix

variable {ι κ σ R S : Type*}

section CommSemiring

variable [CommSemiring R] (P : ι → σ → R) (d : ℕ)

/-- The first-jet map of the points `P i` in degree `d`: a polynomial `f` of total degree at
most `d` is sent to the family whose `(i, none)` entry is the value `f (P i)` and whose
`(i, some j)` entry is the partial derivative `∂ⱼ f (P i)`. It is `MvPolynomial.jetEval` with the
Hasse derivative orders `0` and `eⱼ`, curried in the row index. -/
noncomputable def firstJetMap : restrictTotalDegree σ R d →ₗ[R] ι → Option σ → R :=
  (LinearEquiv.curry R R ι (Option σ)).toLinearMap ∘ₗ
    jetEval {s : σ →₀ ℕ | s.degree ≤ d} (fun z ↦ P z.1) (fun z ↦ z.2.elim 0 (Finsupp.single · 1)) ∘ₗ
      (LinearEquiv.ofEq _ _ (restrictTotalDegree_eq_restrictSupport σ R d)).toLinearMap

/-- Defining equation of `firstJetMap` in terms of `MvPolynomial.jetEval`. -/
theorem firstJetMap_def :
    firstJetMap P d =
      (LinearEquiv.curry R R ι (Option σ)).toLinearMap ∘ₗ
        jetEval {s : σ →₀ ℕ | s.degree ≤ d} (fun z ↦ P z.1)
          (fun z ↦ z.2.elim 0 (Finsupp.single · 1)) ∘ₗ
        (LinearEquiv.ofEq _ _ (restrictTotalDegree_eq_restrictSupport σ R d)).toLinearMap :=
  (rfl)

/-- The value row of the first jet at a point. -/
@[simp]
theorem firstJetMap_apply_none (f : restrictTotalDegree σ R d) (i : ι) :
    firstJetMap P d f i none = eval (P i) (f : MvPolynomial σ R) := by
  simp [firstJetMap]

/-- The `j`-th derivative row of the first jet at a point. -/
@[simp]
theorem firstJetMap_apply_some (f : restrictTotalDegree σ R d) (i : ι) (j : σ) :
    firstJetMap P d f i (some j) = eval (P i) (pderiv j (f : MvPolynomial σ R)) := by
  simpa [firstJetMap] using
    congrArg (eval (P i)) (factorial_smul_hasseDeriv_single j 1 (f : MvPolynomial σ R))

/-- A bounded polynomial lies in `LinearMap.ker (firstJetMap P d)` if and only if its value and
all first partial derivatives vanish at every point `P i`. -/
theorem mem_ker_firstJetMap {P : ι → σ → R} {d : ℕ} {f : restrictTotalDegree σ R d} :
    f ∈ LinearMap.ker (firstJetMap P d) ↔
      ∀ i, eval (P i) (f : MvPolynomial σ R) = 0 ∧
        ∀ j, eval (P i) (pderiv j (f : MvPolynomial σ R)) = 0 := by
  rw [LinearMap.mem_ker, _root_.funext_iff]
  simp only [Pi.zero_apply, _root_.funext_iff, Option.forall, firstJetMap_apply_none,
    firstJetMap_apply_some]

/-- Reindexing the points reindexes the first jets. -/
theorem firstJetMap_comp (e : κ → ι) :
    firstJetMap (P ∘ e) d = LinearMap.funLeft R (Option σ → R) e ∘ₗ firstJetMap P d := by
  ext f i z
  cases z <;> simp

/-- Raising the degree bound does not change the first jets. -/
@[simp]
theorem firstJetMap_comp_inclusion {d e : ℕ} (h : d ≤ e) :
    firstJetMap P e ∘ₗ Submodule.inclusion (restrictTotalDegree_mono σ R h) = firstJetMap P d := by
  ext f i z
  cases z <;> simp

/-- Naturality of `firstJetMap` under a change of coefficients `φ : R →+* S`. -/
theorem firstJetMap_map [CommSemiring S] (φ : R →+* S) (f : restrictTotalDegree σ R d)
    (i : ι) (z : Option σ) :
    firstJetMap (fun i ↦ φ ∘ P i) d
        ⟨map φ (f : MvPolynomial σ R),
          (restrictTotalDegree_eq_restrictSupport σ S d).symm ▸
            map_mem_restrictSupport φ ((restrictTotalDegree_eq_restrictSupport σ R d) ▸ f.property)⟩
        i z =
      φ (firstJetMap P d f i z) := by
  let e := LinearEquiv.ofEq _ _ (restrictTotalDegree_eq_restrictSupport σ R d)
  simpa [firstJetMap_def, e] using
    congrFun (jetEval_mapRestrictSupport {s : σ →₀ ℕ | s.degree ≤ d}
      (fun z : ι × Option σ ↦ P z.1) (fun z ↦ z.2.elim 0 (Finsupp.single · 1)) φ (e f)) (i, z)

/-- The value map of the points `P i` in degree `d`: a polynomial `f` of total degree at most `d`
is sent to its values `f (P i)`. These are the `none` rows of `TauCeti.firstJetMap P d`. -/
noncomputable def firstJetValueMap : restrictTotalDegree σ R d →ₗ[R] ι → R :=
  LinearMap.compLeft (LinearMap.proj none) ι ∘ₗ firstJetMap P d

/-- The value map consists of the `none` rows of the first-jet map. -/
theorem firstJetValueMap_apply_eq_firstJetMap (f : restrictTotalDegree σ R d) (i : ι) :
    firstJetValueMap P d f i = firstJetMap P d f i none := (rfl)

@[simp]
theorem firstJetValueMap_apply (f : restrictTotalDegree σ R d) (i : ι) :
    firstJetValueMap P d f i = eval (P i) (f : MvPolynomial σ R) := by
  rw [firstJetValueMap_apply_eq_firstJetMap, firstJetMap_apply_none]

/-- Reindexing the points reindexes the values. -/
theorem firstJetValueMap_comp (e : κ → ι) :
    firstJetValueMap (P ∘ e) d = LinearMap.funLeft R R e ∘ₗ firstJetValueMap P d := by
  ext f k
  simp

/-- A polynomial lies in the kernel of the value map iff it vanishes at every point. -/
theorem mem_ker_firstJetValueMap {f : restrictTotalDegree σ R d} :
    f ∈ LinearMap.ker (firstJetValueMap P d) ↔ ∀ i, eval (P i) (f : MvPolynomial σ R) = 0 := by
  simp [funext_iff]

/-- The derivative map of the points `P i` in degree `d`: a polynomial `f` of total degree at
most `d` vanishing at every point is sent to its first partial derivatives `∂ⱼ f (P i)`. These are
the `some` rows of `TauCeti.firstJetMap P d` on the kernel of `TauCeti.firstJetValueMap P d`. -/
noncomputable def firstJetDerivMap :
    LinearMap.ker (firstJetValueMap P d) →ₗ[R] ι → σ → R :=
  LinearMap.compLeft (LinearMap.funLeft R R some) ι ∘ₗ firstJetMap P d ∘ₗ
    (LinearMap.ker (firstJetValueMap P d)).subtype

/-- The derivative map consists of the `some` rows of the first-jet map on the kernel of the value
map. -/
theorem firstJetDerivMap_apply_eq_firstJetMap (f : LinearMap.ker (firstJetValueMap P d)) (i : ι)
    (j : σ) : firstJetDerivMap P d f i j = firstJetMap P d f i (some j) := (rfl)

@[simp]
theorem firstJetDerivMap_apply (f : LinearMap.ker (firstJetValueMap P d)) (i : ι) (j : σ) :
    firstJetDerivMap P d f i j =
      eval (P i) (pderiv j ((f : restrictTotalDegree σ R d) : MvPolynomial σ R)) := by
  rw [firstJetDerivMap_apply_eq_firstJetMap, firstJetMap_apply_some]

/-- A polynomial vanishing at the points `P i` vanishes at the points of a reindexed family. -/
theorem ker_firstJetValueMap_le_comp (e : κ → ι) :
    LinearMap.ker (firstJetValueMap P d) ≤ LinearMap.ker (firstJetValueMap (P ∘ e) d) := by
  rw [firstJetValueMap_comp]
  exact LinearMap.ker_le_ker_comp _ _

/-- Reindexing the points along a surjection, for instance a permutation, does not change the
polynomials vanishing at them. -/
theorem ker_firstJetValueMap_comp_of_surjective {e : κ → ι} (he : Function.Surjective e) :
    LinearMap.ker (firstJetValueMap (P ∘ e) d) = LinearMap.ker (firstJetValueMap P d) := by
  refine le_antisymm (fun f hf ↦ ?_) (ker_firstJetValueMap_le_comp P d e)
  rw [mem_ker_firstJetValueMap] at hf ⊢
  intro i
  obtain ⟨k, rfl⟩ := he i
  exact hf k

/-- Reindexing the points reindexes the derivatives of the polynomials vanishing at the points. For
a surjection `e`, the inclusion of kernels is the identification
`TauCeti.ker_firstJetValueMap_comp_of_surjective`. -/
theorem firstJetDerivMap_comp (e : κ → ι) :
    firstJetDerivMap (P ∘ e) d ∘ₗ Submodule.inclusion (ker_firstJetValueMap_le_comp P d e) =
      LinearMap.funLeft R (σ → R) e ∘ₗ firstJetDerivMap P d := by
  refine LinearMap.ext fun f ↦ ?_
  funext k j
  simp

/-- The monomial matrix of the first-jet map of the points `P i` in degree `d`. Its rows are
indexed by a point and an element of `Option σ`, its columns by the exponents `α` of degree at
most `d`; the `(i, none)` entry is `P i ^ α` and the `(i, some j)` entry is `αⱼ P i ^ (α - eⱼ)`,
see `TauCeti.firstJetMatrix_apply_none` and `TauCeti.firstJetMatrix_apply_some`. It is
`MvPolynomial.jetMatrix` with the Hasse derivative orders `0` and `eⱼ`. -/
noncomputable def firstJetMatrix : Matrix (ι × Option σ) {s : σ →₀ ℕ // s.degree ≤ d} R :=
  jetMatrix {s : σ →₀ ℕ | s.degree ≤ d} (fun z ↦ P z.1) (fun z ↦ z.2.elim 0 (Finsupp.single · 1))

/-- A value entry of the first-jet matrix is the value of the monomial at the point. -/
@[simp]
theorem firstJetMatrix_apply_none (i : ι) (s : {s : σ →₀ ℕ // s.degree ≤ d}) :
    firstJetMatrix P d (i, none) s = s.val.prod fun j e ↦ P i j ^ e := by
  simp [firstJetMatrix, eval_monomial]

/-- A derivative entry of the first-jet matrix is the exponent-weighted value of the monomial of
one lower degree in that variable; it vanishes when the exponent does. -/
@[simp]
theorem firstJetMatrix_apply_some (i : ι) (j : σ) (s : {s : σ →₀ ℕ // s.degree ≤ d}) :
    firstJetMatrix P d (i, some j) s =
      s.val j * (s.val - Finsupp.single j 1).prod fun k e ↦ P i k ^ e := by
  rw [firstJetMatrix, jetMatrix_apply]
  simp

/-- Naturality of `firstJetMatrix` under a change of coefficients `φ : R →+* S`. -/
theorem firstJetMatrix_map [CommSemiring S] (φ : R →+* S) :
    firstJetMatrix (fun i ↦ φ ∘ P i) d = (firstJetMatrix P d).map φ :=
  jetMatrix_map {s : σ →₀ ℕ | s.degree ≤ d} (fun z : ι × Option σ ↦ P z.1)
    (fun z ↦ z.2.elim 0 (Finsupp.single · 1)) φ

/-- The columns of the first-jet matrix are the first jets of the monomials. -/
theorem firstJetMap_basisRestrictTotalDegree (s : {s : σ →₀ ℕ // s.degree ≤ d}) (i : ι)
    (z : Option σ) :
    firstJetMap P d (basisRestrictTotalDegree σ R d s) i z = firstJetMatrix P d (i, z) s := by
  cases z <;> simp [firstJetMatrix]

/-- `firstJetMatrix P d` is the matrix of `firstJetMap P d` (uncurried) in the monomial basis of
`restrictTotalDegree σ R d` and the standard basis of `ι × Option σ → R`. -/
theorem toMatrix_firstJetMap [Finite (ι × Option σ)] {d : ℕ}
    [Fintype {a : σ →₀ ℕ // a.degree ≤ d}] [DecidableEq {a : σ →₀ ℕ // a.degree ≤ d}]
    (P : ι → σ → R) :
    LinearMap.toMatrix (basisRestrictTotalDegree σ R d) (Pi.basisFun R (ι × Option σ))
      ((LinearEquiv.curry R R ι (Option σ)).symm.toLinearMap ∘ₗ firstJetMap P d) =
      firstJetMatrix P d := by
  ext ⟨i, z⟩ a
  simp [LinearMap.toMatrix_apply, firstJetMap_basisRestrictTotalDegree]

/-- Reindexing points along an equivalence permutes the rows of `firstJetMatrix`. -/
theorem firstJetMatrix_comp_equiv (P : ι → σ → R) (e : κ ≃ ι) (d : ℕ) :
    firstJetMatrix (P ∘ e) d = (firstJetMatrix P d).submatrix (Prod.map e id) id := by
  ext ⟨j, z⟩ a
  cases z <;> simp

/-- The rank of `firstJetMatrix P d` equals the `finrank` of the range of `firstJetMap P d`. -/
theorem rank_firstJetMatrix_eq_finrank_range {d : ℕ} (P : ι → σ → R) :
    (firstJetMatrix P d).rank = Module.finrank R (LinearMap.range (firstJetMap P d)) := by
  let e : (ι × Option σ → R) ≃ₗ[R] (ι → Option σ → R) := LinearEquiv.curry R R ι (Option σ)
  have hcol :
      firstJetMap P d ∘ basisRestrictTotalDegree σ R d =
        e ∘ (firstJetMatrix P d).col := by
    funext s i z
    exact firstJetMap_basisRestrictTotalDegree P d s i z
  have hrange : LinearMap.range (firstJetMap P d) =
      Submodule.map e.toLinearMap (Submodule.span R (Set.range (firstJetMatrix P d).col)) := by
    rw [LinearMap.range_eq_map, ← (basisRestrictTotalDegree σ R d).span_eq,
      Submodule.map_span, ← Set.range_comp, hcol, Set.range_comp]
    exact (Submodule.map_span e.toLinearMap _).symm
  rw [hrange, ← Matrix.finrank_span_range_col]
  exact (Submodule.equivMapOfInjective e.toLinearMap e.injective _).finrank_eq

/-- Reindexing points along an equivalence preserves the rank of `firstJetMatrix`. -/
@[simp]
theorem rank_firstJetMatrix_comp_equiv {d : ℕ} (P : ι → σ → R) (e : κ ≃ ι) :
    (firstJetMatrix (P ∘ e) d).rank = (firstJetMatrix P d).rank := by
  rw [firstJetMatrix_comp_equiv]
  exact Matrix.rank_submatrix _ (e.prodCongr (Equiv.refl _)) (Equiv.refl _)

/-- In monomial coordinates the first-jet map is multiplication by the first-jet matrix. -/
theorem firstJetMatrix_mulVec [Fintype σ] [DecidableEq σ] (f : restrictTotalDegree σ R d) :
    firstJetMatrix P d *ᵥ (basisRestrictTotalDegree σ R d).equivFun f =
      Function.uncurry (firstJetMap P d f) := by
  -- `MvPolynomial.jetEval_eq_mulVec` needs the column instance on the set of exponents.
  let _ : Fintype {s : σ →₀ ℕ | s.degree ≤ d} := Finsupp.fintypeDegreeLe d
  simp only [firstJetMap, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    LinearEquiv.coe_curry, Function.uncurry_curry, jetEval_eq_mulVec]
  congr 1
  funext s
  simp

variable {P d} in
/-- The first-jet map is onto iff multiplication by the first-jet matrix is onto. -/
theorem firstJetMap_surjective_iff_mulVec_surjective [Fintype σ] [DecidableEq σ] :
    Function.Surjective (firstJetMap P d) ↔ (firstJetMatrix P d).mulVec.Surjective := by
  have h : (firstJetMatrix P d).mulVec ∘ (basisRestrictTotalDegree σ R d).equivFun =
      (Equiv.curry ι (Option σ) R).symm ∘ firstJetMap P d :=
    funext (firstJetMatrix_mulVec P d)
  rw [← Function.Surjective.of_comp_iff _ (basisRestrictTotalDegree σ R d).equivFun.surjective, h,
    EquivLike.comp_surjective]

/-- The points `P i` are *well poised* in degree `d` when every family of values and first
partial derivatives at the points is attained by a polynomial of total degree at most `d`. -/
def WellPoised : Prop :=
  Function.Surjective (firstJetMap P d)

variable {P d}

/-- Well-poisedness is surjectivity of the first-jet map. The definition of
`TauCeti.WellPoised` is not exposed, so importing modules introduce and eliminate it here. -/
theorem wellPoised_iff : WellPoised P d ↔ Function.Surjective (firstJetMap P d) :=
  Iff.rfl

/-- Points well poised in some degree are well poised in every higher degree. -/
theorem WellPoised.mono (hP : WellPoised P d) {e : ℕ} (h : d ≤ e) : WellPoised P e := by
  intro t
  obtain ⟨f, rfl⟩ := hP t
  exact ⟨Submodule.inclusion (restrictTotalDegree_mono σ R h) f,
    LinearMap.congr_fun (firstJetMap_comp_inclusion P h) f⟩

/-- A subfamily of well poised points is well poised. -/
theorem WellPoised.comp_injective (hP : WellPoised P d) {e : κ → ι}
    (he : Function.Injective e) : WellPoised (P ∘ e) d := by
  intro t
  obtain ⟨f, hf⟩ := hP (Function.extend e t 0)
  refine ⟨f, ?_⟩
  rw [firstJetMap_comp, LinearMap.comp_apply, hf]
  funext k
  rw [LinearMap.funLeft_apply]
  exact he.extend_apply t 0 k

/-- Well-poisedness does not depend on the indexing of the points. -/
theorem wellPoised_comp_equiv (e : κ ≃ ι) : WellPoised (P ∘ e) d ↔ WellPoised P d := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.comp_injective e.injective⟩
  simpa [Function.comp_assoc] using h.comp_injective e.symm.injective

/-- Over a nontrivial commutative semiring, a well-poised tuple must consist of distinct points. -/
theorem WellPoised.injective [Nontrivial R] (h : WellPoised P d) :
    Function.Injective P := by
  classical
  intro i j hij
  by_contra hne
  obtain ⟨f, hf⟩ := (wellPoised_iff.1 h) (Function.update 0 i fun _ ↦ 1)
  have hi : eval (P i) (f : MvPolynomial σ R) = 1 := by
    simpa using congrFun (congrFun hf i) none
  have hj : eval (P j) (f : MvPolynomial σ R) = 0 := by
    simpa [Function.update_of_ne (Ne.symm hne)] using congrFun (congrFun hf j) none
  rw [hij, hj] at hi
  exact zero_ne_one hi

/-- The empty tuple is well poised in every degree. -/
@[simp]
theorem wellPoised_of_isEmpty [IsEmpty ι] (P : ι → σ → R) (d : ℕ) : WellPoised P d :=
  wellPoised_iff.2 fun _ ↦ ⟨0, _root_.funext fun i ↦ isEmptyElim i⟩

variable (P) in
/-- No point is well poised in degree zero: the partial derivatives of a constant vanish. -/
theorem not_wellPoised_zero [Nontrivial R] [Nonempty ι] [Nonempty σ] : ¬WellPoised P 0 := by
  intro hP
  obtain ⟨i⟩ := ‹Nonempty ι›
  obtain ⟨j⟩ := ‹Nonempty σ›
  obtain ⟨f, hf⟩ := hP fun _ _ ↦ 1
  have hf' := congr_fun (congr_fun hf i) (some j)
  have hC := totalDegree_eq_zero_iff_eq_C.1
    (Nat.le_zero.1 ((mem_restrictTotalDegree σ 0 _).1 f.property))
  rw [firstJetMap_apply_some, hC, pderiv_C, map_zero] at hf'
  exact zero_ne_one hf'

/-- The rank of `firstJetMatrix P d` is bounded above by the minimum of the source polynomial
dimension `(d + r choose r)` and the target jet dimension `n * (r + 1)`. -/
theorem rank_firstJetMatrix_le [StrongRankCondition R] [Fintype σ] [Fintype ι] {d : ℕ}
    (P : ι → σ → R) :
    (firstJetMatrix P d).rank ≤
      min ((d + Fintype.card σ).choose (Fintype.card σ))
        (Fintype.card ι * (Fintype.card σ + 1)) := by
  classical
  have : Module.Finite R (restrictTotalDegree σ R d) :=
    Module.Finite.of_basis (basisRestrictTotalDegree σ R d)
  rw [rank_firstJetMatrix_eq_finrank_range]
  refine le_min
    ((LinearMap.finrank_range_le _).trans_eq (TauCeti.finrank_restrictTotalDegree σ R d)) ?_
  calc
    Module.finrank R (LinearMap.range (firstJetMap P d))
      ≤ Module.finrank R (ι → Option σ → R) := Submodule.finrank_le _
    _ = Fintype.card ι * (Fintype.card σ + 1) := by
      simp [Module.finrank_pi_fintype, Fintype.card_option]

/-- **Full column rank criterion.** Over a nontrivial commutative semiring satisfying
`OrzechProperty`, `firstJetMap P d` is injective if and only if `firstJetMatrix P d` has rank
`(d + Fintype.card σ).choose (Fintype.card σ)`. -/
theorem injective_firstJetMap_iff_rank_eq [Nontrivial R] [OrzechProperty R] [Fintype σ] {d : ℕ}
    (P : ι → σ → R) :
    Function.Injective (firstJetMap P d) ↔
      (firstJetMatrix P d).rank = (d + Fintype.card σ).choose (Fintype.card σ) := by
  classical
  let _ : Fintype {s : σ →₀ ℕ // s.degree ≤ d} := Finsupp.fintypeDegreeLe d
  have h : (firstJetMatrix P d).mulVec ∘ (basisRestrictTotalDegree σ R d).equivFun =
      (Equiv.curry ι (Option σ) R).symm ∘ firstJetMap P d :=
    funext (firstJetMatrix_mulVec P d)
  rw [← Function.Injective.of_comp_iff (Equiv.curry ι (Option σ) R).symm.injective, ← h,
    Function.Injective.of_comp_iff' _ (basisRestrictTotalDegree σ R d).equivFun.bijective,
    ← Matrix.rank_eq_card_iff_mulVec_injective,
    ← Module.finrank_eq_card_basis (basisRestrictTotalDegree σ R d),
    TauCeti.finrank_restrictTotalDegree]

/-- **Necessary dimension bound for well-poisedness.** Over a commutative semiring satisfying
`StrongRankCondition`, if `P` is well poised in degree `d`, then
`Fintype.card ι * (Fintype.card σ + 1) ≤ (d + Fintype.card σ).choose (Fintype.card σ)`. -/
theorem WellPoised.card_mul_le [StrongRankCondition R] [Fintype σ] [Fintype ι]
    (h : WellPoised P d) :
    Fintype.card ι * (Fintype.card σ + 1) ≤ (d + Fintype.card σ).choose (Fintype.card σ) := by
  classical
  have : Module.Finite R (restrictTotalDegree σ R d) :=
    Module.Finite.of_basis (basisRestrictTotalDegree σ R d)
  have hle := LinearMap.finrank_le_finrank_of_surjective (wellPoised_iff.1 h)
  rw [TauCeti.finrank_restrictTotalDegree] at hle
  simpa [Module.finrank_pi_fintype, Fintype.card_option] using hle

end CommSemiring

section CommRing

variable [CommRing R] {P : ι → σ → R} {d : ℕ}

/-- The first-jet map is onto iff the values can be prescribed and the derivatives of the
polynomials vanishing at the points can be prescribed. -/
theorem firstJetMap_surjective_iff :
    Function.Surjective (firstJetMap P d) ↔
      Function.Surjective (firstJetValueMap P d) ∧ Function.Surjective (firstJetDerivMap P d) := by
  refine ⟨fun h ↦ ⟨fun v ↦ ?_, fun w ↦ ?_⟩, fun ⟨hv, hw⟩ t ↦ ?_⟩
  · obtain ⟨f, hf⟩ := h fun i z ↦ z.elim (v i) 0
    exact ⟨f, funext fun i ↦ by simpa using congr_fun (congr_fun hf i) none⟩
  · obtain ⟨f, hf⟩ := h fun i z ↦ z.elim 0 (w i)
    have hf' (i : ι) (z : Option σ) := congr_fun (congr_fun hf i) z
    refine ⟨⟨f, (mem_ker_firstJetValueMap P d).2 fun i ↦ by simpa using hf' i none⟩, ?_⟩
    funext i j
    simpa using hf' i (some j)
  · obtain ⟨g, hg⟩ := hv fun i ↦ t i none
    obtain ⟨h, hh⟩ := hw fun i j ↦ t i (some j) - eval (P i) (pderiv j (g : MvPolynomial σ R))
    have hh0 := (mem_ker_firstJetValueMap P d).1 h.property
    refine ⟨g + h, funext fun i ↦ funext fun z ↦ ?_⟩
    cases z with
    | none => simpa [hh0 i] using congr_fun hg i
    | some j =>
      have hj := congr_fun (congr_fun hh i) j
      rw [firstJetDerivMap_apply] at hj
      simp [hj]

/-- A single point is well poised in every positive degree: the affine polynomial
`a + ∑ⱼ bⱼ (Xⱼ - xⱼ)` has value `a` and gradient `b` at `x`. -/
theorem wellPoised_of_subsingleton [Finite σ] [Subsingleton ι] (P : ι → σ → R) (hd : 1 ≤ d) :
    WellPoised P d := by
  classical
  have := Fintype.ofFinite σ
  refine WellPoised.mono (fun t ↦ ?_) hd
  rcases isEmpty_or_nonempty ι with hι | ⟨⟨i₀⟩⟩
  · exact ⟨0, funext hι.elim⟩
  have hX (j : σ) : (X j : MvPolynomial σ R) ∈ restrictTotalDegree σ R 1 := by
    rw [← one_mul (X j), ← C_1, C_mul_X_eq_monomial]
    exact monomial_mem_restrictTotalDegree (by simp) 1
  have hC (a : R) : (C a : MvPolynomial σ R) ∈ restrictTotalDegree σ R 1 :=
    (mem_restrictTotalDegree σ 1 _).2 (by simp)
  refine ⟨⟨C (t i₀ none) + ∑ j, t i₀ (some j) • (X j - C (P i₀ j)),
    add_mem (hC _) (Submodule.sum_mem _ fun j _ ↦
      Submodule.smul_mem _ _ (sub_mem (hX j) (hC _)))⟩, ?_⟩
  funext i z
  obtain rfl := Subsingleton.elim i i₀
  cases z <;> simp [Pi.single_apply]

end CommRing

section Field

variable {k : Type*} [Field k]

/-- Over a field, points are well poised iff their first-jet matrix has full row rank. -/
theorem wellPoised_iff_rank [Fintype ι] [Fintype σ] {P : ι → σ → k} {d : ℕ} :
    WellPoised P d ↔ (firstJetMatrix P d).rank = Fintype.card ι * (Fintype.card σ + 1) := by
  classical
  rw [WellPoised, firstJetMap_surjective_iff_mulVec_surjective,
    Matrix.mulVec_surjective_iff_rank_eq_card, Fintype.card_prod, Fintype.card_option]

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
  exact ⟨hw, by simpa using (wellPoised_iff_rank).1 hw⟩

end TauCeti
