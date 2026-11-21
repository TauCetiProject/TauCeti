/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Rank
public import TauCeti.RingTheory.MvPolynomial.HasseDeriv.JetEvaluation
public import TauCeti.RingTheory.MvPolynomial.RestrictTotalDegree

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
their derivatives `αⱼ P i ^ (α - eⱼ)`. Over a field, the points are well poised exactly when this
matrix has full row rank `|ι| (|σ| + 1)`.

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
* `TauCeti.firstJetMatrix_mulVec`: the matrix times the coefficient vector of `f` is the first
  jet of `f`.
* `TauCeti.firstJetMap_surjective_iff_mulVec_surjective`: the first-jet map is onto iff
  multiplication by its matrix is onto.
* `TauCeti.wellPoised_iff`: the points are well poised iff the first-jet map is surjective.
* `TauCeti.wellPoised_iff_rank`: over a field, the points are well poised iff the first-jet
  matrix has rank `|ι| (|σ| + 1)`.
* `TauCeti.firstJetMap_comp`, `TauCeti.firstJetValueMap_comp`, `TauCeti.firstJetDerivMap_comp`:
  reindexing the points reindexes the first jets, the values and the derivatives.
* `TauCeti.WellPoised.mono`, `TauCeti.WellPoised.comp_injective`,
  `TauCeti.wellPoised_comp_equiv`: raising the degree and passing to a subfamily or a
  reindexing of the points preserve well-poisedness.
* `TauCeti.wellPoised_of_subsingleton`, `TauCeti.not_wellPoised_zero`: one point is well poised
  in every positive degree, and no point is well poised in degree zero.

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

/-- Over a field, points are well poised iff their first-jet matrix has full row rank. -/
theorem wellPoised_iff_rank {k : Type*} [Field k] [Fintype ι] [Fintype σ] {P : ι → σ → k} :
    WellPoised P d ↔ (firstJetMatrix P d).rank = Fintype.card ι * (Fintype.card σ + 1) := by
  classical
  rw [WellPoised, firstJetMap_surjective_iff_mulVec_surjective,
    Matrix.mulVec_surjective_iff_rank_eq_card, Fintype.card_prod, Fintype.card_option]

end CommRing

end TauCeti
