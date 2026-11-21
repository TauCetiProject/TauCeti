/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPolynomial.FirstJet.Evaluation
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import TauCeti.Algebra.MvPolynomial.PDeriv
import TauCeti.Algebra.MvPolynomial.Rename
import TauCeti.LinearAlgebra.Dimension.Submodule
import TauCeti.LinearAlgebra.HermiteInterpolation

/-!
# Exact first-jet ranks: univariate Hermite and coordinate-hyperplane configurations

This file establishes exact rank formulas for `TauCeti.firstJetMatrix` in two geometric settings,
over an arbitrary field `k` in every characteristic:

1. **Univariate Hermite interpolation.** In one variable (`[Unique σ]`), identifying
   `restrictTotalDegree σ k d` with `Polynomial.degreeLT k (d + 1)` via
   `MvPolynomial.uniqueAlgEquiv` connects `firstJetMap P d` (and `firstJetValueMap P d`) directly
   to the univariate Hermite jet map `Polynomial.hermiteJet`. Consequently, every injective finite
   tuple `P` on the affine line has first-jet rank `min (d + 1) (2 * Fintype.card ι)`
   (`TauCeti.rank_firstJetMatrix_univariate`) and is well poised in degree `d` if and only if
   `2 * Fintype.card ι ≤ d + 1` (`TauCeti.wellPoised_iff_univariate`).

2. **Coordinate-hyperplane specialization.** When every point `P i` lies on a coordinate
   hyperplane `x_{j₀} = 0`, writing a polynomial of total degree at most `d + 1` as
   `f₀ + X j₀ * f₁ + X j₀ ^ 2 * g` (via `MvPolynomial.killCompl`) splits the range of
   `firstJetMap P (d + 1)` into the product of the degree-`(d + 1)` first-jet range and the
   degree-`d` value range on the hyperplane (`TauCeti.rank_firstJetMatrix_of_coord_eq_zero`),
   yielding the binomial upper bound
   `(d + 1 + (r - 1) choose (r - 1)) + (d + (r - 1) choose (r - 1))`
   (`TauCeti.rank_firstJetMatrix_le_of_coord_eq_zero`). In two variables
   (`Fintype.card σ = 2`), combining the two results gives the exact rank
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

variable {σ ι k : Type*} [Field k]

/-- In one variable, the range of the value map `firstJetValueMap P d` at `n` distinct points over
any field has dimension `min (d + 1) n`. -/
theorem finrank_range_firstJetValueMap_univariate [Unique σ] [Fintype ι]
    {P : ι → σ → k} (hP : Function.Injective P) (d : ℕ) :
    Module.finrank k (LinearMap.range (firstJetValueMap P d)) = min (d + 1) (Fintype.card ι) := by
  let a : ι → k := fun i ↦ P i default
  have ha : Function.Injective a := fun i j hij ↦
    hP (_root_.funext fun s ↦ by rw [Unique.eq_default s]; exact hij)
  let eDom := restrictTotalDegreeEquivDegreeLT σ k d
  let eCod : ((i : ι) → Fin 1 → k) ≃ₗ[k] (ι → k) :=
    LinearEquiv.piCongrRight fun _ ↦ LinearEquiv.funUnique (Fin 1) k k
  let L := (Polynomial.hasseJet a (fun _ ↦ 1)).comp (Polynomial.degreeLT k (d + 1)).subtype
  have hcomp : firstJetValueMap P d = eCod.toLinearMap ∘ₗ L ∘ₗ eDom.toLinearMap := by
    ext f i
    simpa [eDom, eCod, L, a] using
      (eval₂_uniqueAlgEquiv (R := k) (φ := RingHom.id k) (a := P i) (f := f.val)).symm
  rw [hcomp, LinearMap.finrank_range_comp_comp eCod.toLinearMap L eDom.toLinearMap
    eCod.injective eDom.surjective]
  simpa [L] using Polynomial.finrank_range_hermiteJet_degreeLT ha (fun _ ↦ 1) (d + 1)

/-- In one variable, the range of `firstJetMap P d` at `n` distinct points over any field has
dimension `min (d + 1) (2 * n)`. -/
theorem finrank_range_firstJetMap_univariate [Unique σ] [Fintype ι]
    {P : ι → σ → k} (hP : Function.Injective P) (d : ℕ) :
    Module.finrank k (LinearMap.range (firstJetMap P d)) =
      min (d + 1) (2 * Fintype.card ι) := by
  let a : ι → k := fun i ↦ P i default
  have ha : Function.Injective a := fun i j hij ↦
    hP (_root_.funext fun s ↦ by rw [Unique.eq_default s]; exact hij)
  let eDom := restrictTotalDegreeEquivDegreeLT σ k d
  let eCod : ((i : ι) → Fin 2 → k) ≃ₗ[k] (ι → Option σ → k) :=
    LinearEquiv.piCongrRight fun _ ↦
      LinearEquiv.funCongrLeft k k
        ((finSuccEquiv 1).trans (Equiv.optionCongr (Equiv.ofUnique (Fin 1) σ))).symm
  let L := (Polynomial.hasseJet a (fun _ ↦ 2)).comp (Polynomial.degreeLT k (d + 1)).subtype
  have hcomp : firstJetMap P d = eCod.toLinearMap ∘ₗ L ∘ₗ eDom.toLinearMap := by
    ext f i z
    cases z with
    | none =>
      simpa [eDom, eCod, L, a, LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply,
        ← Equiv.optionCongr_symm] using
        (eval₂_uniqueAlgEquiv (R := k) (φ := RingHom.id k) (a := P i) (f := f.val)).symm
    | some s =>
      rw [Unique.eq_default s]
      have hderiv :
          (eCod (L (eDom f))) i (some default) =
            (Polynomial.hasseDeriv 1 (uniqueAlgEquiv k σ f.val)).eval (P i default) := by
        simp [eCod, L, eDom, a, LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply,
          ← Equiv.optionCongr_symm, Unique.eq_default ((Equiv.ofUnique (Fin 1) σ).symm default)]
      rw [firstJetMap_apply_some, LinearMap.comp_apply, LinearMap.comp_apply,
        LinearEquiv.coe_toLinearMap, LinearEquiv.coe_toLinearMap, hderiv,
        Polynomial.hasseDeriv_one, ← uniqueAlgEquiv_pderiv]
      exact (eval₂_uniqueAlgEquiv (R := k) (φ := RingHom.id k) (a := P i)
        (f := pderiv default f.val)).symm
  rw [hcomp, LinearMap.finrank_range_comp_comp eCod.toLinearMap L eDom.toLinearMap
    eCod.injective eDom.surjective]
  simpa [L, mul_comm] using Polynomial.finrank_range_hermiteJet_degreeLT ha (fun _ ↦ 2) (d + 1)

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

variable {σ ι k : Type*} [Field k]

private noncomputable def hyperplaneSliceMap (j₀ : σ) (d : ℕ) :
    restrictTotalDegree σ k (d + 1) →ₗ[k]
      restrictTotalDegree {j : σ // j ≠ j₀} k (d + 1) ×
        restrictTotalDegree {j : σ // j ≠ j₀} k d where
  toFun f :=
    (⟨killCompl Subtype.val_injective f.val,
      killCompl_mem_restrictTotalDegree Subtype.val_injective f.property⟩,
     ⟨killCompl Subtype.val_injective (pderiv j₀ f.val),
      killCompl_mem_restrictTotalDegree Subtype.val_injective <|
        (mem_restrictTotalDegree σ d _).2 <|
          (totalDegree_pderiv_le j₀ f.val).trans <|
            Nat.sub_le_of_le_add ((mem_restrictTotalDegree σ (d + 1) _).1 f.property)⟩)
  map_add' _ _ := by ext <;> simp
  map_smul' _ _ := by ext <;> simp

@[simp]
private theorem hyperplaneSliceMap_fst_coe (j₀ : σ) (d : ℕ)
    (f : restrictTotalDegree σ k (d + 1)) :
    ((hyperplaneSliceMap j₀ d f).1 : MvPolynomial {j : σ // j ≠ j₀} k) =
      killCompl Subtype.val_injective f.val :=
  rfl

@[simp]
private theorem hyperplaneSliceMap_snd_coe (j₀ : σ) (d : ℕ)
    (f : restrictTotalDegree σ k (d + 1)) :
    ((hyperplaneSliceMap j₀ d f).2 : MvPolynomial {j : σ // j ≠ j₀} k) =
      killCompl Subtype.val_injective (pderiv j₀ f.val) :=
  rfl

private theorem hyperplaneSliceMap_surjective (j₀ : σ) (d : ℕ) :
    Function.Surjective (hyperplaneSliceMap (k := k) j₀ d) := by
  rintro ⟨g₀, g₁⟩
  let p : MvPolynomial σ k := rename Subtype.val g₀.val + X j₀ * rename Subtype.val g₁.val
  have hp : p ∈ restrictTotalDegree σ k (d + 1) := by
    rw [mem_restrictTotalDegree]
    refine (totalDegree_add _ _).trans (max_le ?_ ?_)
    · exact (totalDegree_rename_le Subtype.val g₀.val).trans
        ((mem_restrictTotalDegree {j : σ // j ≠ j₀} (d + 1) _).1 g₀.property)
    · refine (totalDegree_mul _ _).trans ?_
      have hX : (X j₀ : MvPolynomial σ k).totalDegree ≤ 1 :=
        (totalDegree_monomial_le _ _).trans_eq (by simp)
      have hg1 : (rename Subtype.val g₁.val).totalDegree ≤ d :=
        (totalDegree_rename_le Subtype.val g₁.val).trans
          ((mem_restrictTotalDegree {j : σ // j ≠ j₀} d _).1 g₁.property)
      omega
  refine ⟨⟨p, hp⟩, Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)⟩
  · simp [p, killCompl_X_of_notMem_range]
  · simp [p, pderiv_rename_of_notMem_range]

private noncomputable def hyperplaneJetCodomainEquiv [DecidableEq σ] (j₀ : σ) :
    (ι → Option σ → k) ≃ₗ[k] (ι → Option {j : σ // j ≠ j₀} → k) × (ι → k) :=
  let eOpt : Option (Option {j : σ // j ≠ j₀}) ≃ Option σ :=
    (Equiv.swap none (some none)).trans (Equiv.optionCongr (Equiv.optionSubtypeNe j₀))
  let eOne : (Option σ → k) ≃ₗ[k] (Option {j : σ // j ≠ j₀} → k) × k :=
    (LinearEquiv.funCongrLeft k k eOpt).trans
      ((LinearEquiv.piOptionEquivProd k).trans (LinearEquiv.prodComm k _ _))
  (LinearEquiv.piCongrRight fun _ ↦ eOne).trans
    { Equiv.arrowProdEquivProdArrow ι _ _ with
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }

@[simp]
private theorem hyperplaneJetCodomainEquiv_fst_none [DecidableEq σ] (j₀ : σ)
    (y : ι → Option σ → k) (i : ι) :
    (hyperplaneJetCodomainEquiv j₀ y).1 i none = y i none := by
  simp [hyperplaneJetCodomainEquiv, LinearEquiv.funCongrLeft_apply, LinearEquiv.piOptionEquivProd,
    Equiv.piOptionEquivProd]

@[simp]
private theorem hyperplaneJetCodomainEquiv_fst_some [DecidableEq σ] (j₀ : σ)
    (y : ι → Option σ → k) (i : ι) (l : {j : σ // j ≠ j₀}) :
    (hyperplaneJetCodomainEquiv j₀ y).1 i (some l) = y i (some l.val) := by
  simp [hyperplaneJetCodomainEquiv, LinearEquiv.funCongrLeft_apply, LinearEquiv.piOptionEquivProd,
    Equiv.piOptionEquivProd, Equiv.swap_apply_of_ne_of_ne]

@[simp]
private theorem hyperplaneJetCodomainEquiv_snd [DecidableEq σ] (j₀ : σ)
    (y : ι → Option σ → k) (i : ι) :
    (hyperplaneJetCodomainEquiv j₀ y).2 i = y i (some j₀) := by
  simp [hyperplaneJetCodomainEquiv, LinearEquiv.funCongrLeft_apply, LinearEquiv.piOptionEquivProd,
    Equiv.piOptionEquivProd]

private theorem hyperplaneJetCodomainEquiv_comp_firstJetMap [DecidableEq σ] {d : ℕ}
    {P : ι → σ → k} (j₀ : σ) (hP : ∀ i, P i j₀ = 0) :
    (hyperplaneJetCodomainEquiv (k := k) (ι := ι) j₀).toLinearMap ∘ₗ firstJetMap P (d + 1) =
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

/-- **Coordinate-hyperplane rank splitting.** When every point `P i` lies on the coordinate
hyperplane `x_{j₀} = 0`, writing a degree-`(d + 1)` polynomial as `f₀ + X j₀ * f₁ + X j₀ ^ 2 * g`
splits the first-jet range into the product of the degree-`(d + 1)` first-jet range and the
degree-`d` value range on the hyperplane `x_{j₀} = 0`. -/
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
  let P' : ι → σ' → k := fun i l ↦ P i l.val
  have hcomp : firstJetMap P (d + 1) =
      (hyperplaneJetCodomainEquiv (k := k) (ι := ι) j₀).symm.toLinearMap ∘ₗ
        ((firstJetMap P' (d + 1)).prodMap (firstJetValueMap P' d)) ∘ₗ
        hyperplaneSliceMap j₀ d := by
    rw [← hyperplaneJetCodomainEquiv_comp_firstJetMap j₀ hP, ← LinearMap.comp_assoc]
    ext f i z
    simp
  have : Module.Finite k (restrictTotalDegree σ' k (d + 1)) :=
    Module.Finite.of_basis (basisRestrictTotalDegree σ' k (d + 1))
  have : Module.Finite k (restrictTotalDegree σ' k d) :=
    Module.Finite.of_basis (basisRestrictTotalDegree σ' k d)
  rw [rank_firstJetMatrix_eq_finrank_range, hcomp,
    LinearMap.finrank_range_comp_comp _ _ _ (hyperplaneJetCodomainEquiv j₀).symm.injective
      (hyperplaneSliceMap_surjective j₀ d),
    LinearMap.range_prodMap, (Submodule.prodEquiv _ _).finrank_eq, Module.finrank_prod]

/-- **Coordinate-hyperplane rank upper bound.** Points lying on a coordinate hyperplane `x_{j₀} = 0`
have degree-`(d + 1)` first-jet rank at most
`(d + 1 + (r - 1) choose (r - 1)) + (d + (r - 1) choose (r - 1))`. -/
theorem rank_firstJetMatrix_le_of_coord_eq_zero [Fintype σ] {d : ℕ}
    {P : ι → σ → k} (j₀ : σ) (hP : ∀ i, P i j₀ = 0) :
    (firstJetMatrix P (d + 1)).rank ≤
      (d + 1 + (Fintype.card σ - 1)).choose (Fintype.card σ - 1) +
        (d + (Fintype.card σ - 1)).choose (Fintype.card σ - 1) := by
  classical
  let σ' := {j : σ // j ≠ j₀}
  have hcard : Fintype.card σ' = Fintype.card σ - 1 := by
    simp [σ', Fintype.card_subtype_compl]
  have : Module.Finite k (restrictTotalDegree σ' k (d + 1)) :=
    Module.Finite.of_basis (basisRestrictTotalDegree σ' k (d + 1))
  have : Module.Finite k (restrictTotalDegree σ' k d) :=
    Module.Finite.of_basis (basisRestrictTotalDegree σ' k d)
  rw [rank_firstJetMatrix_of_coord_eq_zero j₀ hP]
  exact add_le_add
    ((LinearMap.finrank_range_le _).trans_eq <| by
      simpa [hcard] using TauCeti.finrank_restrictTotalDegree σ' k (d + 1))
    ((LinearMap.finrank_range_le _).trans_eq <| by
      simpa [hcard] using TauCeti.finrank_restrictTotalDegree σ' k d)

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
