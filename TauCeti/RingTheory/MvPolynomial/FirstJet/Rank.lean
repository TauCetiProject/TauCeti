/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPolynomial.FirstJet.Evaluation
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.RingTheory.Finiteness.Prod
import TauCeti.Algebra.MvPolynomial.Equiv
import TauCeti.Algebra.MvPolynomial.PDeriv
import TauCeti.Algebra.MvPolynomial.Rename
import TauCeti.LinearAlgebra.Dimension.Submodule
import TauCeti.LinearAlgebra.HermiteInterpolation
import TauCeti.LinearAlgebra.Pi.Prod

/-!
# Exact first-jet ranks: univariate Hermite and coordinate-hyperplane configurations

This file establishes exact rank formulas for `TauCeti.firstJetMatrix` in two geometric settings,
over an arbitrary field `k` in every characteristic (with the coordinate-hyperplane upper bound
holding over any commutative semiring satisfying `StrongRankCondition`):

1. **Univariate Hermite interpolation.** In one variable (`[Unique σ]`), identifying
   `restrictTotalDegree σ k d` with `Polynomial.degreeLT k (d + 1)` via
   `MvPolynomial.uniqueAlgEquiv` connects `firstJetMap P d` (and `firstJetValueMap P d`) directly
   to `Polynomial.hasseJet` restricted to `Polynomial.degreeLT k (d + 1)`, with multiplicity `2` for
   first jets and `1` for values. Consequently, every injective finite tuple `P` on the affine line
   has first-jet rank `min (d + 1) (2 * Fintype.card ι)` (`TauCeti.rank_firstJetMatrix_univariate`)
   and is well poised in degree `d` if and only if `2 * Fintype.card ι ≤ d + 1`
   (`TauCeti.wellPoised_iff_univariate`).

2. **Coordinate-hyperplane specialization.** When every point `P i` lies on a coordinate
   hyperplane `x_{j₀} = 0`, slicing along `x_{j₀} = 0` via `MvPolynomial.hyperplaneSliceMap`
   factors `firstJetMap P (d + 1)` through
   `restrictTotalDegree σ' R (d + 1) × restrictTotalDegree σ' R d`, yielding the binomial upper
   bound `(d + 1 + (r - 1) choose (r - 1)) + (d + (r - 1) choose (r - 1))`
   over any commutative semiring satisfying `StrongRankCondition`
   (`TauCeti.rank_firstJetMatrix_le_of_coord_eq_zero`), and over a field splitting the rank into the
   sum of the degree-`(d + 1)` first-jet rank and the degree-`d` value rank on the hyperplane
   (`TauCeti.rank_firstJetMatrix_of_coord_eq_zero`). In two variables (`Fintype.card σ = 2`),
   combining the two results gives the exact rank
   `min (d + 2) (2 * Fintype.card ι) + min (d + 1) (Fintype.card ι)`
   (`TauCeti.rank_firstJetMatrix_of_coord_eq_zero_of_card_eq_two`). In particular, two
   distinct points on a line in `𝔸²` have degree-`2` rank `5 < 6`, and seven distinct collinear
   rational points have degree-`5` rank `11 < 21`, demonstrating that the dimension inequality
   alone does not imply well-poisedness.

## Main results

* `TauCeti.finrank_range_firstJetValueMap_univariate`: univariate value evaluation rank
  `min (d + 1) (Fintype.card ι)`.
* `TauCeti.finrank_range_firstJetMap_univariate`,
  `TauCeti.rank_firstJetMatrix_univariate`, `TauCeti.wellPoised_iff_univariate`: exact
  univariate Hermite rank `min (d + 1) (2 * Fintype.card ι)` and well-poisedness criterion.
* `TauCeti.rank_firstJetMatrix_of_coord_eq_zero`,
  `TauCeti.rank_firstJetMatrix_le_of_coord_eq_zero`: coordinate-hyperplane rank splitting and
  binomial upper bound.
* `TauCeti.rank_firstJetMatrix_of_coord_eq_zero_of_card_eq_two`: exact first-jet rank of
  distinct points on a coordinate line in two variables.

## References

* J.-M. Couveignes, *Enumerating number fields*, Annals of Mathematics 192 (2020), 487–497, §3.
* M. C. Brambilla and G. Ottaviani, *On the Alexander–Hirschowitz Theorem*, J. Pure Appl. Algebra
  212 (2008), 1229–1251 (arXiv:math/0701409v2), §1 and §7.1.
-/

public section

namespace TauCeti

open MvPolynomial

section Univariate

private theorem eval_eq_eval_uniqueAlgEquiv {σ R : Type*} [CommSemiring R] [Unique σ]
    (a : σ → R) (p : MvPolynomial σ R) :
    eval a p = (uniqueAlgEquiv R σ p).eval (a default) :=
  (eval₂_uniqueAlgEquiv (R := R) (φ := RingHom.id R) (a := a) (f := p)).symm

private theorem eval_pderiv_eq_hasseDeriv_one_uniqueAlgEquiv {σ R : Type*} [CommSemiring R]
    [Unique σ] (a : σ → R) (s : σ) (p : MvPolynomial σ R) :
    eval a (pderiv s p) = (Polynomial.hasseDeriv 1 (uniqueAlgEquiv R σ p)).eval (a default) := by
  rw [Unique.eq_default s, eval_eq_eval_uniqueAlgEquiv, uniqueAlgEquiv_pderiv,
    Polynomial.hasseDeriv_one]

private noncomputable def univariateValueCodomainEquiv (R ι : Type*) [CommSemiring R] :
    ((i : ι) → Fin 1 → R) ≃ₗ[R] (ι → R) :=
  LinearEquiv.piCongrRight fun _ ↦ LinearEquiv.funUnique (Fin 1) R R

@[simp]
private theorem univariateValueCodomainEquiv_apply {R ι : Type*} [CommSemiring R]
    (y : (i : ι) → Fin 1 → R) (i : ι) :
    univariateValueCodomainEquiv R ι y i = y i 0 :=
  rfl

private noncomputable def univariateJetCodomainEquiv (R ι σ : Type*) [CommSemiring R] [Unique σ] :
    ((i : ι) → Fin 2 → R) ≃ₗ[R] (ι → Option σ → R) :=
  LinearEquiv.piCongrRight fun _ ↦
    LinearEquiv.funCongrLeft R R
      ((finSuccEquiv 1).trans (Equiv.optionCongr (Equiv.ofUnique (Fin 1) σ))).symm

@[simp]
private theorem univariateJetCodomainEquiv_apply_none {R ι σ : Type*} [CommSemiring R] [Unique σ]
    (y : (i : ι) → Fin 2 → R) (i : ι) :
    univariateJetCodomainEquiv R ι σ y i none = y i 0 := by
  simp [univariateJetCodomainEquiv, LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply,
    ← Equiv.optionCongr_symm]

@[simp]
private theorem univariateJetCodomainEquiv_apply_some {R ι σ : Type*} [CommSemiring R] [Unique σ]
    (y : (i : ι) → Fin 2 → R) (i : ι) (s : σ) :
    univariateJetCodomainEquiv R ι σ y i (some s) = y i 1 := by
  simp [univariateJetCodomainEquiv, LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply,
    ← Equiv.optionCongr_symm, Unique.eq_default ((Equiv.ofUnique (Fin 1) σ).symm s)]

private theorem firstJetValueMap_eq_hasseJet {σ ι R : Type*} [CommSemiring R] [Unique σ]
    (P : ι → σ → R) (d : ℕ) :
    firstJetValueMap P d =
      (univariateValueCodomainEquiv R ι).toLinearMap ∘ₗ
        (Polynomial.hasseJet (fun i ↦ P i default) (fun _ ↦ 1)).comp
          (Polynomial.degreeLT R (d + 1)).subtype ∘ₗ
        (restrictTotalDegreeEquivDegreeLT σ R d).toLinearMap := by
  ext f i
  simp [eval_eq_eval_uniqueAlgEquiv]

private theorem firstJetMap_eq_hasseJet {σ ι R : Type*} [CommSemiring R] [Unique σ]
    (P : ι → σ → R) (d : ℕ) :
    firstJetMap P d =
      (univariateJetCodomainEquiv R ι σ).toLinearMap ∘ₗ
        (Polynomial.hasseJet (fun i ↦ P i default) (fun _ ↦ 2)).comp
          (Polynomial.degreeLT R (d + 1)).subtype ∘ₗ
        (restrictTotalDegreeEquivDegreeLT σ R d).toLinearMap := by
  ext f i z
  cases z with
  | none => simp [eval_eq_eval_uniqueAlgEquiv]
  | some s => simp [eval_pderiv_eq_hasseDeriv_one_uniqueAlgEquiv]

variable {σ ι k : Type*} [Field k]

/-- In one variable, the range of the value map `firstJetValueMap P d` at `n` distinct points over
any field has dimension `min (d + 1) n`. -/
theorem finrank_range_firstJetValueMap_univariate [Unique σ] [Fintype ι]
    {P : ι → σ → k} (hP : Function.Injective P) (d : ℕ) :
    Module.finrank k (LinearMap.range (firstJetValueMap P d)) = min (d + 1) (Fintype.card ι) := by
  have ha : Function.Injective fun i ↦ P i default := fun i j hij ↦
    hP (_root_.funext fun s ↦ by rw [Unique.eq_default s]; exact hij)
  rw [firstJetValueMap_eq_hasseJet,
    LinearMap.finrank_range_comp_comp _ _ _ (univariateValueCodomainEquiv k ι).injective
      (restrictTotalDegreeEquivDegreeLT σ k d).surjective]
  simpa using Polynomial.finrank_range_hermiteJet_degreeLT (fun _ ↦ 1) ha.injOn (d + 1)

/-- In one variable, the range of `firstJetMap P d` at `n` distinct points over any field has
dimension `min (d + 1) (2 * n)`. -/
theorem finrank_range_firstJetMap_univariate [Unique σ] [Fintype ι]
    {P : ι → σ → k} (hP : Function.Injective P) (d : ℕ) :
    Module.finrank k (LinearMap.range (firstJetMap P d)) =
      min (d + 1) (2 * Fintype.card ι) := by
  have ha : Function.Injective fun i ↦ P i default := fun i j hij ↦
    hP (_root_.funext fun s ↦ by rw [Unique.eq_default s]; exact hij)
  rw [firstJetMap_eq_hasseJet,
    LinearMap.finrank_range_comp_comp _ _ _ (univariateJetCodomainEquiv k ι σ).injective
      (restrictTotalDegreeEquivDegreeLT σ k d).surjective]
  simpa [mul_comm] using
    Polynomial.finrank_range_hermiteJet_degreeLT (fun _ ↦ 2) ha.injOn (d + 1)

/-- **Univariate Hermite interpolation rank.** Over any field `k` in any characteristic, for any
injective finite tuple `P` on the affine line, `firstJetMatrix P d` has rank
`min (d + 1) (2 * Fintype.card ι)`. -/
theorem rank_firstJetMatrix_univariate [Unique σ] [Fintype ι] {d : ℕ}
    {P : ι → σ → k} (hP : Function.Injective P) :
    (firstJetMatrix P d).rank = min (d + 1) (2 * Fintype.card ι) := by
  rw [rank_firstJetMatrix_eq_finrank_range, finrank_range_firstJetMap_univariate hP]

/-- Over any field, an injective finite tuple on the affine line is well poised in degree `d` if
and only if `2 * Fintype.card ι ≤ d + 1`. -/
theorem wellPoised_iff_univariate [Unique σ] [Fintype ι]
    {P : ι → σ → k} (hP : Function.Injective P) (d : ℕ) :
    WellPoised P d ↔ 2 * Fintype.card ι ≤ d + 1 := by
  classical
  rw [wellPoised_iff_rank, rank_firstJetMatrix_univariate hP, Fintype.card_unique (α := σ),
    one_add_one_eq_two, mul_comm (Fintype.card ι) 2, min_eq_right_iff]

end Univariate

section CoordinateHyperplane

private noncomputable def hyperplaneJetCodomainEquiv {σ ι R : Type*} [CommSemiring R]
    [DecidableEq σ] (j₀ : σ) :
    (ι → Option σ → R) ≃ₗ[R] (ι → Option {j : σ // j ≠ j₀} → R) × (ι → R) :=
  let eOpt : Option (Option {j : σ // j ≠ j₀}) ≃ Option σ :=
    (Equiv.swap none (some none)).trans (Equiv.optionCongr (Equiv.optionSubtypeNe j₀))
  let eOne : (Option σ → R) ≃ₗ[R] (Option {j : σ // j ≠ j₀} → R) × R :=
    (LinearEquiv.funCongrLeft R R eOpt).trans
      ((LinearEquiv.piOptionEquivProd R).trans (LinearEquiv.prodComm R _ _))
  (LinearEquiv.piCongrRight fun _ ↦ eOne).trans
    (TauCeti.LinearEquiv.arrowProdEquivProdArrow R _ _)

@[simp]
private theorem hyperplaneJetCodomainEquiv_fst_none {σ ι R : Type*} [CommSemiring R]
    [DecidableEq σ] (j₀ : σ) (y : ι → Option σ → R) (i : ι) :
    (hyperplaneJetCodomainEquiv j₀ y).1 i none = y i none := by
  simp [hyperplaneJetCodomainEquiv, LinearEquiv.funCongrLeft_apply, LinearEquiv.piOptionEquivProd,
    Equiv.piOptionEquivProd]

@[simp]
private theorem hyperplaneJetCodomainEquiv_fst_some {σ ι R : Type*} [CommSemiring R]
    [DecidableEq σ] (j₀ : σ) (y : ι → Option σ → R) (i : ι) (l : {j : σ // j ≠ j₀}) :
    (hyperplaneJetCodomainEquiv j₀ y).1 i (some l) = y i (some l.val) := by
  simp [hyperplaneJetCodomainEquiv, LinearEquiv.funCongrLeft_apply, LinearEquiv.piOptionEquivProd,
    Equiv.piOptionEquivProd, Equiv.swap_apply_of_ne_of_ne]

@[simp]
private theorem hyperplaneJetCodomainEquiv_snd {σ ι R : Type*} [CommSemiring R] [DecidableEq σ]
    (j₀ : σ) (y : ι → Option σ → R) (i : ι) :
    (hyperplaneJetCodomainEquiv j₀ y).2 i = y i (some j₀) := by
  simp [hyperplaneJetCodomainEquiv, LinearEquiv.funCongrLeft_apply, LinearEquiv.piOptionEquivProd,
    Equiv.piOptionEquivProd]

private theorem hyperplaneJetCodomainEquiv_comp_firstJetMap {σ ι R : Type*} [CommSemiring R]
    [DecidableEq σ] {d : ℕ} {P : ι → σ → R} (j₀ : σ) (hP : ∀ i, P i j₀ = 0) :
    (hyperplaneJetCodomainEquiv (R := R) (ι := ι) j₀).toLinearMap ∘ₗ firstJetMap P (d + 1) =
      (firstJetMap (fun i (l : {j : σ // j ≠ j₀}) ↦ P i l.val) (d + 1)).prodMap
          (firstJetValueMap (fun i (l : {j : σ // j ≠ j₀}) ↦ P i l.val) d) ∘ₗ
        hyperplaneSliceMap j₀ d := by
  have hzero (i : ι) : ∀ a ∉ Set.range (Subtype.val : {j : σ // j ≠ j₀} → σ), P i a = 0 := by
    rintro a ha
    have haj : a = j₀ := by
      by_contra h
      exact ha ⟨⟨a, h⟩, rfl⟩
    rw [haj, hP i]
  ext f i z
  · cases z with
    | none =>
      simpa [Function.comp_def] using (eval_killCompl Subtype.val_injective (hzero i) f.val).symm
    | some l =>
      simpa [Function.comp_def, pderiv_killCompl] using
        (eval_killCompl Subtype.val_injective (hzero i) (pderiv l.val f.val)).symm
  · simpa [Function.comp_def] using
      (eval_killCompl Subtype.val_injective (hzero i) (pderiv j₀ f.val)).symm

private theorem firstJetMap_eq_hyperplaneSliceMap {σ ι R : Type*} [CommSemiring R] [DecidableEq σ]
    {d : ℕ} {P : ι → σ → R} (j₀ : σ) (hP : ∀ i, P i j₀ = 0) :
    firstJetMap P (d + 1) =
      (hyperplaneJetCodomainEquiv (R := R) (ι := ι) j₀).symm.toLinearMap ∘ₗ
        ((firstJetMap (fun i (l : {j : σ // j ≠ j₀}) ↦ P i l.val) (d + 1)).prodMap
          (firstJetValueMap (fun i (l : {j : σ // j ≠ j₀}) ↦ P i l.val) d)) ∘ₗ
        hyperplaneSliceMap j₀ d := by
  rw [← hyperplaneJetCodomainEquiv_comp_firstJetMap j₀ hP, ← LinearMap.comp_assoc]
  ext f i z
  simp

/-- **Coordinate-hyperplane rank upper bound.** Over any commutative semiring satisfying
`StrongRankCondition`, points lying on a coordinate hyperplane `x_{j₀} = 0` have degree-`(d + 1)`
first-jet rank at most `(d + 1 + (r - 1) choose (r - 1)) + (d + (r - 1) choose (r - 1))`. -/
theorem rank_firstJetMatrix_le_of_coord_eq_zero {σ ι R : Type*} [CommSemiring R]
    [StrongRankCondition R] [Fintype σ] {d : ℕ} {P : ι → σ → R} (j₀ : σ)
    (hP : ∀ i, P i j₀ = 0) :
    (firstJetMatrix P (d + 1)).rank ≤
      (d + 1 + (Fintype.card σ - 1)).choose (Fintype.card σ - 1) +
        (d + (Fintype.card σ - 1)).choose (Fintype.card σ - 1) := by
  classical
  let σ' := {j : σ // j ≠ j₀}
  let P' : ι → σ' → R := fun i l ↦ P i l.val
  let L :
      restrictTotalDegree σ' R (d + 1) × restrictTotalDegree σ' R d →ₗ[R] ι → Option σ → R :=
    (hyperplaneJetCodomainEquiv (R := R) (ι := ι) j₀).symm.toLinearMap ∘ₗ
      ((firstJetMap P' (d + 1)).prodMap (firstJetValueMap P' d))
  have hrange : LinearMap.range (firstJetMap P (d + 1)) = LinearMap.range L := by
    rw [firstJetMap_eq_hyperplaneSliceMap j₀ hP, ← LinearMap.comp_assoc,
      LinearMap.range_comp_of_range_eq_top _
        (LinearMap.range_eq_top.2 (hyperplaneSliceMap_surjective j₀ d))]
  have hcard : Fintype.card σ' = Fintype.card σ - 1 := by
    simp [σ', Fintype.card_subtype_compl]
  have : Module.Finite R (restrictTotalDegree σ' R (d + 1)) :=
    Module.Finite.of_basis (basisRestrictTotalDegree σ' R (d + 1))
  have : Module.Finite R (restrictTotalDegree σ' R d) :=
    Module.Finite.of_basis (basisRestrictTotalDegree σ' R d)
  have : Module.Free R (restrictTotalDegree σ' R (d + 1)) :=
    Module.Free.of_basis (basisRestrictTotalDegree σ' R (d + 1))
  have : Module.Free R (restrictTotalDegree σ' R d) :=
    Module.Free.of_basis (basisRestrictTotalDegree σ' R d)
  rw [rank_firstJetMatrix_eq_finrank_range, hrange]
  refine (LinearMap.finrank_range_le L).trans_eq ?_
  rw [Module.finrank_prod, TauCeti.finrank_restrictTotalDegree, TauCeti.finrank_restrictTotalDegree,
    hcard]

variable {σ ι k : Type*} [Field k]

/-- **Coordinate-hyperplane rank splitting.** When every point `P i` lies on the coordinate
hyperplane `x_{j₀} = 0`, slicing along `x_{j₀} = 0` splits the first-jet range into the product
of the degree-`(d + 1)` first-jet range and the degree-`d` value range on the hyperplane
`x_{j₀} = 0`. -/
theorem rank_firstJetMatrix_of_coord_eq_zero [Finite σ] {d : ℕ}
    {P : ι → σ → k} (j₀ : σ) (hP : ∀ i, P i j₀ = 0) :
    (firstJetMatrix P (d + 1)).rank =
      Module.finrank k
          (LinearMap.range (firstJetMap (fun i (l : {j : σ // j ≠ j₀}) ↦ P i l.val) (d + 1))) +
        Module.finrank k
          (LinearMap.range (firstJetValueMap (fun i (l : {j : σ // j ≠ j₀}) ↦ P i l.val) d)) := by
  have := Fintype.ofFinite σ
  classical
  let σ' := {j : σ // j ≠ j₀}
  have : Module.Finite k (restrictTotalDegree σ' k (d + 1)) :=
    Module.Finite.of_basis (basisRestrictTotalDegree σ' k (d + 1))
  have : Module.Finite k (restrictTotalDegree σ' k d) :=
    Module.Finite.of_basis (basisRestrictTotalDegree σ' k d)
  rw [rank_firstJetMatrix_eq_finrank_range, firstJetMap_eq_hyperplaneSliceMap j₀ hP,
    LinearMap.finrank_range_comp_comp _ _ _ (hyperplaneJetCodomainEquiv j₀).symm.injective
      (hyperplaneSliceMap_surjective j₀ d),
    LinearMap.range_prodMap, (Submodule.prodEquiv _ _).finrank_eq, Module.finrank_prod]

/-- **Exact rank of distinct points on a coordinate line in two variables.** For any injective
finite family `P : ι → σ → k` in two variables (`Fintype.card σ = 2`) lying on a coordinate line
`x_{j₀} = 0`, the degree-`(d + 1)` first-jet rank is
`min (d + 2) (2 * Fintype.card ι) + min (d + 1) (Fintype.card ι)`. -/
theorem rank_firstJetMatrix_of_coord_eq_zero_of_card_eq_two [Fintype σ] [Fintype ι]
    {d : ℕ} (hσ : Fintype.card σ = 2) {P : ι → σ → k}
    (hP : Function.Injective P) (j₀ : σ) (hcoord : ∀ i, P i j₀ = 0) :
    (firstJetMatrix P (d + 1)).rank =
      min (d + 2) (2 * Fintype.card ι) + min (d + 1) (Fintype.card ι) := by
  classical
  have hcard : Fintype.card {j : σ // j ≠ j₀} = 1 := by
    simp [Fintype.card_subtype_compl, hσ]
  obtain ⟨x, hx⟩ := Fintype.card_eq_one_iff.1 hcard
  let _ : Unique {j : σ // j ≠ j₀} := ⟨⟨x⟩, hx⟩
  have hP' : Function.Injective (fun i (l : {j : σ // j ≠ j₀}) ↦ P i l.val) := by
    intro i₁ i₂ h
    apply hP
    ext j
    by_cases hj : j = j₀
    · subst hj
      rw [hcoord, hcoord]
    · exact congrFun h ⟨j, hj⟩
  rw [rank_firstJetMatrix_of_coord_eq_zero j₀ hcoord,
    finrank_range_firstJetMap_univariate hP', finrank_range_firstJetValueMap_univariate hP']

end CoordinateHyperplane

/-! ### Examples -/

/-- Two distinct points `(0, 0)` and `(1, 0)` in `𝔸²` have degree-`2` first-jet rank `5` rather
than `6` (the defective quadric case), and are therefore not well poised in degree `2`. -/
example :
    let P : Fin 2 → Fin 2 → ℚ := fun i ↦ ![(i : ℚ), 0]
    (firstJetMatrix P 2).rank = 5 ∧ ¬ WellPoised P 2 := by
  intro P
  have hP : Function.Injective P := fun i j hij ↦
    Fin.ext (by simpa [P] using congrFun hij 0)
  have hr : (firstJetMatrix P 2).rank = 5 := by
    simpa [P] using
      rank_firstJetMatrix_of_coord_eq_zero_of_card_eq_two (d := 1) (Fintype.card_fin 2) hP 1
        fun _ ↦ rfl
  refine ⟨hr, fun hw ↦ ?_⟩
  have h6 : (firstJetMatrix P 2).rank = 6 := by
    simpa using (wellPoised_iff_rank).1 hw
  omega

/-- Seven distinct collinear points `(i, 0) ∈ ℚ²` (`0 ≤ i ≤ 6`) have degree-`5` first-jet rank
`11` rather than `21 = (5 + 2 choose 2)`, showing that the dimension count alone does not force
well-poisedness. -/
example :
    let P : Fin 7 → Fin 2 → ℚ := fun i ↦ ![(i : ℚ), 0]
    (firstJetMatrix P 5).rank = 11 ∧ ¬ WellPoised P 5 := by
  intro P
  have hP : Function.Injective P := fun i j hij ↦
    Fin.ext (by simpa [P] using congrFun hij 0)
  have hr : (firstJetMatrix P 5).rank = 11 := by
    simpa [P] using
      rank_firstJetMatrix_of_coord_eq_zero_of_card_eq_two (d := 4) (Fintype.card_fin 2) hP 1
        fun _ ↦ rfl
  refine ⟨hr, fun hw ↦ ?_⟩
  have h21 : (firstJetMatrix P 5).rank = 21 := by
    simpa using (wellPoised_iff_rank).1 hw
  omega

end TauCeti
