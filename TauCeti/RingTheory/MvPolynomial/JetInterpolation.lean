/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Rank
public import TauCeti.RingTheory.MvPolynomial.DoublePoint
public import TauCeti.RingTheory.MvPolynomial.HasseDeriv.JetEvaluation
public import TauCeti.RingTheory.MvPolynomial.RestrictTotalDegree
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finrank
import TauCeti.Algebra.MvPolynomial.Equiv
import TauCeti.Data.Finsupp.Weight
import TauCeti.LinearAlgebra.HermiteInterpolation
import TauCeti.RingTheory.MvPolynomial.Finrank

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
coordinates of `MvPolynomial.basisRestrictTotalDegree` the first-jet map is multiplication by the
matrix `TauCeti.firstJetMatrix P d`, the jet matrix `MvPolynomial.jetMatrix` of these orders,
whose `(i, none)` row lists the values `P i ^ α` of the monomials and whose `(i, some j)` row lists
their derivatives `αⱼ P i ^ (α - eⱼ)`. Its rank equals
`Module.finrank R (LinearMap.range (firstJetMap P d))` and is bounded above by
`min ((card σ + d).choose d) (card ι * (card σ + 1))`. Over a field, the points are well poised
exactly when this matrix has full row rank `|ι| (|σ| + 1)`.

In one variable (`[Unique σ]`), identifying `firstJetMap P d` with `Polynomial.hasseJet` of
uniform multiplicity `2` via `MvPolynomial.uniqueAlgEquiv` yields Hermite interpolation for
double points: over a commutative ring with unit node differences, `firstJetMap P d` is injective
when `d + 1 ≤ 2 * card ι` and surjective when `2 * card ι ≤ d + 1`; under `[StrongRankCondition R]`
(and in particular over any field for injective `P`), `firstJetMatrix P d` has exact rank
`min (d + 1) (2 * card ι)`.

## Main definitions

* `TauCeti.firstJetMap P d`: values and first partial derivatives at the points `P i` of the
  polynomials of total degree at most `d`.
* `TauCeti.firstJetValueMap P d`, `TauCeti.firstJetDerivMap P d`: its value rows, and its
  derivative rows on the polynomials vanishing at every point.
* `TauCeti.firstJetMatrix P d`: the monomial matrix of the first-jet map.
* `TauCeti.WellPoised P d`: the first-jet map is surjective.

## Main results

* `TauCeti.firstJetMap_surjective_iff`: the first-jet map is onto iff the value map is onto and
  the derivative map on its kernel is onto.
* `TauCeti.mem_ker_firstJetMap_iff_mem_doubleIdeal`: for points with pairwise unit coordinate
  differences, the kernel of `firstJetMap P d` consists of the bounded-degree polynomials in
  `doubleIdeal P`.
* `TauCeti.firstJetMatrix_mulVec`, `TauCeti.toLin_firstJetMatrix`: the matrix represents the
  first-jet map in monomial coordinates.
* `TauCeti.firstJetMap_surjective_iff_mulVec_surjective`: the first-jet map is onto iff
  multiplication by its matrix is onto.
* `TauCeti.rank_firstJetMatrix_eq_finrank_range`, `TauCeti.rank_firstJetMatrix_le`: matrix rank
  equals the rank of the range of `firstJetMap P d` and is bounded by the row and column counts.
* `TauCeti.wellPoised_iff`: the points are well poised iff the first-jet map is surjective.
* `TauCeti.WellPoised.rank_firstJetMatrix`, `TauCeti.WellPoised.card_mul_le_choose`,
  `TauCeti.wellPoised_iff_rank`: well-poisedness forces full row rank and the dimension bound, and
  over a field is equivalent to full row rank `|ι| (|σ| + 1)`.
* `TauCeti.firstJetMap_comp`, `TauCeti.firstJetValueMap_comp`, `TauCeti.firstJetDerivMap_comp`,
  `TauCeti.rank_firstJetMatrix_comp_equiv`: reindexing the points.
* `TauCeti.WellPoised.mono`, `TauCeti.WellPoised.comp_injective`,
  `TauCeti.wellPoised_comp_equiv`: raising the degree and passing to a subfamily or a
  reindexing of the points preserve well-poisedness.
* `TauCeti.wellPoised_of_isEmpty`, `TauCeti.wellPoised_of_subsingleton`,
  `TauCeti.not_wellPoised_zero`: empty and singleton configurations are well poised in positive
  degree, and no nonempty point family is well poised in degree zero.
* `TauCeti.firstJetMap_injective_of_unique`, `TauCeti.wellPoised_of_unique`,
  `TauCeti.rank_firstJetMatrix_of_unique`, `TauCeti.wellPoised_iff_of_unique`,
  `TauCeti.rank_firstJetMatrix_of_unique_of_injective`,
  `TauCeti.wellPoised_iff_of_unique_of_injective`: univariate double-point Hermite interpolation
  and exact rank `min (d + 1) (2 * card ι)`.

## References

* J.-M. Couveignes, *Enumerating number fields*, Ann. of Math. 192 (2020), no. 2, 487–497, §3.
-/

public section

namespace TauCeti

open MvPolynomial

open scoped Matrix

variable {ι κ σ R : Type*}

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

/-- A bounded-degree polynomial lies in the kernel of `firstJetMap P d` iff it and all of its
first partial derivatives vanish at every `P i`. -/
theorem mem_ker_firstJetMap_iff (f : restrictTotalDegree σ R d) :
    f ∈ LinearMap.ker (firstJetMap P d) ↔
      ∀ i, eval (P i) (f : MvPolynomial σ R) = 0 ∧
        ∀ j, eval (P i) (pderiv j (f : MvPolynomial σ R)) = 0 := by
  simp only [LinearMap.mem_ker, funext_iff, Pi.zero_apply, Option.forall,
    firstJetMap_apply_none, firstJetMap_apply_some]

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

/-- The columns of the first-jet matrix are the first jets of the monomials. -/
theorem firstJetMap_basisRestrictTotalDegree (s : {s : σ →₀ ℕ // s.degree ≤ d}) (i : ι)
    (z : Option σ) :
    firstJetMap P d (basisRestrictTotalDegree σ R d s) i z = firstJetMatrix P d (i, z) s := by
  cases z <;> simp [firstJetMatrix]

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

/-- Mapping the entries of `firstJetMatrix P d` along a ring homomorphism `φ : R →+* S` produces
the first-jet matrix of the image configuration `fun i s ↦ φ (P i s)`. -/
@[simp]
theorem firstJetMatrix_map {S : Type*} [CommSemiring S] (φ : R →+* S) :
    (firstJetMatrix P d).map φ = firstJetMatrix (fun i s ↦ φ (P i s)) d := by
  ext ⟨i, z⟩ a
  cases z <;> simp [Matrix.map_apply, Finsupp.prod, map_prod]

/-- In the monomial basis `basisRestrictTotalDegree σ R d` and the standard row basis
`Pi.basisFun R (ι × Option σ)`, `firstJetMatrix P d` represents `firstJetMap P d` (up to
uncurrying the target). -/
theorem toLin_firstJetMatrix [Finite ι] [Finite σ]
    [Fintype {s : σ →₀ ℕ // s.degree ≤ d}] [DecidableEq {s : σ →₀ ℕ // s.degree ≤ d}] :
    Matrix.toLin (basisRestrictTotalDegree σ R d) (Pi.basisFun R (ι × Option σ))
      (firstJetMatrix P d) =
      (LinearEquiv.curry R R ι (Option σ)).symm.toLinearMap.comp (firstJetMap P d) := by
  apply (LinearMap.toMatrix (basisRestrictTotalDegree σ R d)
    (Pi.basisFun R (ι × Option σ))).injective
  rw [LinearMap.toMatrix_toLin]
  ext ⟨i, z⟩ s
  simp [LinearMap.toMatrix_apply, firstJetMap_basisRestrictTotalDegree]

/-- The rank of `firstJetMatrix P d` equals the `R`-rank of the range of `firstJetMap P d`. -/
theorem rank_firstJetMatrix_eq_finrank_range [Finite ι] [Finite σ] :
    (firstJetMatrix P d).rank = Module.finrank R (LinearMap.range (firstJetMap P d)) := by
  classical
  have _ : Fintype {s : σ →₀ ℕ // s.degree ≤ d} := Fintype.ofFinite _
  rw [Matrix.rank_eq_finrank_range_toLin (firstJetMatrix P d) (Pi.basisFun R (ι × Option σ))
      (basisRestrictTotalDegree σ R d),
    toLin_firstJetMatrix, LinearMap.range_comp]
  exact (LinearEquiv.curry R R ι (Option σ)).symm.finrank_map_eq _

/-- The rank of `firstJetMatrix P d` is bounded above by both the number of admissible monomials
`(card σ + d).choose d` and the number of jet conditions `card ι * (card σ + 1)`. -/
theorem rank_firstJetMatrix_le [StrongRankCondition R] [Fintype ι] [Fintype σ] :
    (firstJetMatrix P d).rank ≤
      min ((Fintype.card σ + d).choose d) (Fintype.card ι * (Fintype.card σ + 1)) := by
  classical
  have _ : Fintype {s : σ →₀ ℕ // s.degree ≤ d} := Finsupp.fintypeDegreeLe d
  refine le_min ?_ ?_
  · exact (Matrix.rank_le_card_width _).trans_eq (Finsupp.card_degree_le d)
  · exact (Matrix.rank_le_card_height _).trans_eq (by rw [Fintype.card_prod, Fintype.card_option])

/-- Reindexing the point family along an equivalence preserves the rank of `firstJetMatrix`. -/
theorem rank_firstJetMatrix_comp_equiv [Finite ι] [Finite κ] [Finite σ] (e : κ ≃ ι) :
    (firstJetMatrix (P ∘ e) d).rank = (firstJetMatrix P d).rank := by
  rw [rank_firstJetMatrix_eq_finrank_range, rank_firstJetMatrix_eq_finrank_range]
  let φ : (ι → Option σ → R) ≃ₗ[R] (κ → Option σ → R) :=
    LinearEquiv.piCongrLeft' R (fun _ ↦ Option σ → R) e.symm
  have hcomp : firstJetMap (P ∘ e) d = φ.toLinearMap.comp (firstJetMap P d) := by
    ext f k z
    cases z <;> simp [φ]
  rw [hcomp, LinearMap.range_comp]
  exact φ.finrank_map_eq _

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

/-- An empty family of points is well poised in every degree. -/
theorem wellPoised_of_isEmpty [IsEmpty ι] (P : ι → σ → R) (d : ℕ) : WellPoised P d :=
  fun _ ↦ ⟨0, funext isEmptyElim⟩

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

/-- Over a commutative semiring with the strong rank condition, a well-poised configuration has
full row rank `card ι * (card σ + 1)`. -/
theorem WellPoised.rank_firstJetMatrix [StrongRankCondition R] [Fintype ι] [Fintype σ]
    (h : WellPoised P d) :
    (firstJetMatrix P d).rank = Fintype.card ι * (Fintype.card σ + 1) := by
  rw [rank_firstJetMatrix_eq_finrank_range, LinearMap.range_eq_top.mpr h, finrank_top,
    (LinearEquiv.curry R R ι (Option σ)).symm.finrank_eq, Module.finrank_pi, Fintype.card_prod,
    Fintype.card_option]

/-- Over a commutative semiring with the rank condition, a well-poised configuration of `card ι`
points in `card σ` variables of degree `d` satisfies
`card ι * (card σ + 1) ≤ (card σ + d).choose d`. -/
theorem WellPoised.card_mul_le_choose [RankCondition R] [Fintype ι] [Fintype σ]
    (h : WellPoised P d) :
    Fintype.card ι * (Fintype.card σ + 1) ≤ (Fintype.card σ + d).choose d := by
  classical
  let _ : Fintype {s : σ →₀ ℕ // s.degree ≤ d} := Finsupp.fintypeDegreeLe d
  have hsurj : Function.Surjective (firstJetMatrix P d).mulVecLin := by
    rw [Matrix.coe_mulVecLin]
    exact (firstJetMap_surjective_iff_mulVec_surjective (P := P) (d := d)).mp h
  have hle := card_le_of_surjective R (firstJetMatrix P d).mulVecLin hsurj
  simpa only [Fintype.card_prod, Fintype.card_option, Finsupp.card_degree_le] using hle

end CommSemiring

section CommRing

variable [CommRing R] {P : ι → σ → R} {d : ℕ}

/-- Over a commutative ring, for finitely many points with pairwise unit coordinate differences,
the kernel of `firstJetMap P d` consists of the polynomials of total degree at most `d` lying in
`doubleIdeal P`. -/
theorem mem_ker_firstJetMap_iff_mem_doubleIdeal [Finite ι]
    (hP : Pairwise fun i j ↦ ∃ s, IsUnit (P i s - P j s)) (f : restrictTotalDegree σ R d) :
    f ∈ LinearMap.ker (firstJetMap P d) ↔ (f : MvPolynomial σ R) ∈ doubleIdeal P := by
  rw [mem_ker_firstJetMap_iff, mem_doubleIdeal_iff_of_pairwise_isUnit hP]

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

/-- Over a field, points are well poised iff their first-jet matrix has full row rank. -/
theorem wellPoised_iff_rank {k : Type*} [Field k] [Fintype ι] [Fintype σ] {P : ι → σ → k} :
    WellPoised P d ↔ (firstJetMatrix P d).rank = Fintype.card ι * (Fintype.card σ + 1) := by
  classical
  rw [WellPoised, firstJetMap_surjective_iff_mulVec_surjective,
    Matrix.mulVec_surjective_iff_rank_eq_card, Fintype.card_prod, Fintype.card_option]

end CommRing

section Univariate

private def optionUniqueEquivFinTwo (σ : Type*) [Unique σ] : Option σ ≃ Fin 2 where
  toFun z := z.elim 0 fun _ ↦ 1
  invFun k := if k = 0 then none else some default
  left_inv z := by cases z with | none => rfl | some j => simp [Unique.eq_default j]
  right_inv k := by fin_cases k <;> rfl

private theorem firstJetMap_unique_eq_hasseJet {σ ι R : Type*} [CommSemiring R] [Unique σ]
    (P : ι → σ → R) (d : ℕ) (f : restrictTotalDegree σ R d) (i : ι) (k : Fin 2) :
    firstJetMap P d f i ((optionUniqueEquivFinTwo σ).symm k) =
      Polynomial.hasseJet (fun i ↦ P i default) (fun _ ↦ 2) (uniqueAlgEquiv R σ f.val) i k := by
  fin_cases k
  · change firstJetMap P d f i none = _
    simp only [firstJetMap_apply_none, Polynomial.hasseJet_apply, Polynomial.hasseDeriv_zero']
    rw [← MvPolynomial.eval₂_id, ← Polynomial.eval₂_id, eval₂_uniqueAlgEquiv]
  · change firstJetMap P d f i (some default) = _
    simp only [firstJetMap_apply_some, Polynomial.hasseJet_apply, Polynomial.hasseDeriv_one',
      ← uniqueAlgEquiv_pderiv (default : σ)]
    rw [← MvPolynomial.eval₂_id, ← Polynomial.eval₂_id, eval₂_uniqueAlgEquiv]

/-- **Univariate Hermite injectivity** for double points over a commutative ring: when the node
differences are units and `d + 1 ≤ 2 * card ι`, `firstJetMap P d` is injective. -/
theorem firstJetMap_injective_of_unique [CommRing R] [Unique σ] [Fintype ι] {P : ι → σ → R}
    (hP : Pairwise fun i j ↦ IsUnit (P i default - P j default)) {d : ℕ}
    (hd : d + 1 ≤ 2 * Fintype.card ι) :
    Function.Injective (firstJetMap P d) := by
  intro f g hfg
  have hle : d + 1 ≤ ∑ _ : ι, 2 := by simpa [mul_comm] using hd
  have hjet : Polynomial.hermiteJet (fun i ↦ P i default) (fun _ ↦ 2)
        (Submodule.inclusion (Polynomial.degreeLT_mono hle)
          (restrictTotalDegreeEquivDegreeLT σ R d f)) =
      Polynomial.hermiteJet (fun i ↦ P i default) (fun _ ↦ 2)
        (Submodule.inclusion (Polynomial.degreeLT_mono hle)
          (restrictTotalDegreeEquivDegreeLT σ R d g)) := by
    ext i k
    simp only [Polynomial.hermiteJet_apply, Submodule.coe_inclusion,
      coe_restrictTotalDegreeEquivDegreeLT_apply, ← firstJetMap_unique_eq_hasseJet]
    exact congrFun (congrFun hfg i) ((optionUniqueEquivFinTwo σ).symm k)
  have heq :=
    (Polynomial.hermiteJet_bijective_of_pairwise_isUnit_sub hP (fun _ ↦ 2)).injective hjet
  exact (restrictTotalDegreeEquivDegreeLT σ R d).injective
    (Submodule.inclusion_injective _ heq)

/-- **Univariate Hermite surjectivity** for double points over a commutative ring: when the node
differences are units and `2 * card ι ≤ d + 1`, `P` is well poised in degree `d`. -/
theorem wellPoised_of_unique [CommRing R] [Unique σ] [Fintype ι] {P : ι → σ → R}
    (hP : Pairwise fun i j ↦ IsUnit (P i default - P j default)) {d : ℕ}
    (hd : 2 * Fintype.card ι ≤ d + 1) :
    WellPoised P d := by
  intro y
  have hle : ∑ _ : ι, 2 ≤ d + 1 := by simpa [mul_comm] using hd
  obtain ⟨g, hg⟩ :=
    (Polynomial.hermiteJet_bijective_of_pairwise_isUnit_sub hP (fun _ ↦ 2)).surjective
      fun i k ↦ y i ((optionUniqueEquivFinTwo σ).symm k)
  refine ⟨(restrictTotalDegreeEquivDegreeLT σ R d).symm
    (Submodule.inclusion (Polynomial.degreeLT_mono hle) g), ?_⟩
  ext i z
  rw [← (optionUniqueEquivFinTwo σ).symm_apply_apply z, firstJetMap_unique_eq_hasseJet,
    coe_restrictTotalDegreeEquivDegreeLT_symm_apply, Submodule.coe_inclusion,
    AlgEquiv.apply_symm_apply,
    ← Polynomial.hermiteJet_apply (a := fun i ↦ P i default) (m := fun _ ↦ 2) g]
  exact congrFun (congrFun hg i) (optionUniqueEquivFinTwo σ z)

/-- **Univariate Hermite interpolation rank.** Over any commutative ring with the strong rank
condition, for univariate points `P : ι → σ → R` (`[Unique σ]`) whose pairwise differences are
units, the monomial first-jet matrix in degree `d` has exact rank `min (d + 1) (2 * card ι)`. -/
theorem rank_firstJetMatrix_of_unique [CommRing R] [StrongRankCondition R] [Unique σ] [Fintype ι]
    {P : ι → σ → R} (hP : Pairwise fun i j ↦ IsUnit (P i default - P j default)) (d : ℕ) :
    (firstJetMatrix P d).rank = min (d + 1) (2 * Fintype.card ι) := by
  rcases le_total (d + 1) (2 * Fintype.card ι) with hle | hge
  · rw [min_eq_left hle, rank_firstJetMatrix_eq_finrank_range,
      LinearMap.finrank_range_of_inj (firstJetMap_injective_of_unique hP hle),
      finrank_restrictTotalDegree, Fintype.card_unique (α := σ), Nat.choose_one_right]
  · rw [min_eq_right hge, (wellPoised_of_unique hP hge).rank_firstJetMatrix,
      Fintype.card_unique (α := σ), mul_comm]

/-- Over any nontrivial commutative ring, univariate double points `P : ι → σ → R` (`[Unique σ]`)
with pairwise unit differences are well poised in degree `d` if and only if `2 * card ι ≤ d + 1`. -/
theorem wellPoised_iff_of_unique [CommRing R] [Nontrivial R] [Unique σ] [Fintype ι]
    {P : ι → σ → R} (hP : Pairwise fun i j ↦ IsUnit (P i default - P j default)) (d : ℕ) :
    WellPoised P d ↔ 2 * Fintype.card ι ≤ d + 1 := by
  refine ⟨fun h ↦ ?_, wellPoised_of_unique hP⟩
  have hle := h.card_mul_le_choose
  rw [Fintype.card_unique (α := σ), Nat.add_comm 1 d, Nat.choose_succ_self_right] at hle
  omega

/-- Over any field, for distinct univariate points `P : ι → σ → k` (`[Unique σ]`), the monomial
first-jet matrix in degree `d` has exact rank `min (d + 1) (2 * card ι)`. -/
theorem rank_firstJetMatrix_of_unique_of_injective {k : Type*} [Field k] [Unique σ] [Fintype ι]
    {P : ι → σ → k} (hP : Function.Injective P) (d : ℕ) :
    (firstJetMatrix P d).rank = min (d + 1) (2 * Fintype.card ι) :=
  rank_firstJetMatrix_of_unique
    ((pairwise_exists_isUnit_sub_of_injective hP).mono fun _ _ ⟨s, hs⟩ ↦
      Unique.eq_default s ▸ hs)
    d

/-- Over any field, distinct univariate double points `P : ι → σ → k` (`[Unique σ]`) are
well poised in degree `d` if and only if `2 * card ι ≤ d + 1`. -/
theorem wellPoised_iff_of_unique_of_injective {k : Type*} [Field k] [Unique σ] [Fintype ι]
    {P : ι → σ → k} (hP : Function.Injective P) (d : ℕ) :
    WellPoised P d ↔ 2 * Fintype.card ι ≤ d + 1 :=
  wellPoised_iff_of_unique
    ((pairwise_exists_isUnit_sub_of_injective hP).mono fun _ _ ⟨s, hs⟩ ↦
      Unique.eq_default s ▸ hs)
    d

end Univariate

end TauCeti
