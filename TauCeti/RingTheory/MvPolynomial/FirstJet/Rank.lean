/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPolynomial.FirstJet.Evaluation
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import TauCeti.Algebra.MvPolynomial.PDeriv
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

private theorem finrank_range_hermiteJet_degreeLT [Fintype ι] {a : ι → k}
    (ha : Function.Injective a) (m N : ℕ) :
    Module.finrank k (LinearMap.range
        ((LinearMap.pi fun i ↦ taylorJet (a i) m) ∘ₗ (Polynomial.degreeLT k N).subtype)) =
      min N (m * Fintype.card ι) := by
  let L : Polynomial.degreeLT k N →ₗ[k] (i : ι) → Fin m → k :=
    (LinearMap.pi fun i ↦ taylorJet (a i) m) ∘ₗ (Polynomial.degreeLT k N).subtype
  have hsum : ∑ _ : ι, m = m * Fintype.card ι := by
    rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_comm]
  rcases le_total N (m * Fintype.card ι) with hle | hge
  · have hNM : N ≤ ∑ _ : ι, m := hsum ▸ hle
    have hcomp : L = Polynomial.hermiteJet a (fun _ ↦ m) ∘ₗ
        Submodule.inclusion (Polynomial.degreeLT_mono hNM) := by
      ext f i r
      simp [L]
    have hinj : Function.Injective L := by
      rw [hcomp]
      exact (Polynomial.hermiteJet_injective ha (fun _ ↦ m)).comp
        (Submodule.inclusion_injective _)
    rw [min_eq_left hle, (LinearEquiv.ofInjective L hinj).finrank_eq.symm]
    simp [(Polynomial.degreeLTEquiv k N).finrank_eq]
  · have hMN : ∑ _ : ι, m ≤ N := hsum ▸ hge
    have hcomp : L ∘ₗ Submodule.inclusion (Polynomial.degreeLT_mono hMN) =
        Polynomial.hermiteJet a (fun _ ↦ m) := by
      ext f i r
      simp [L]
    have hsurj : Function.Surjective L := fun y ↦ by
      obtain ⟨f, hf⟩ := (Polynomial.hermiteJet_bijective ha (fun _ ↦ m)).surjective y
      refine ⟨Submodule.inclusion (Polynomial.degreeLT_mono hMN) f, ?_⟩
      simpa using (LinearMap.congr_fun hcomp f).trans hf
    rw [min_eq_right hge, LinearMap.range_eq_top.2 hsurj, finrank_top]
    simp [Module.finrank_pi_fintype, mul_comm]

private theorem uniqueAlgEquiv_pderiv [Unique σ] (f : MvPolynomial σ k) :
    uniqueAlgEquiv k σ (pderiv default f) = Polynomial.derivative (uniqueAlgEquiv k σ f) := by
  induction f using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => rw [map_add, map_add, map_add, map_add, hp, hq]
  | mul_X p j hp =>
    rw [Unique.eq_default j, pderiv_mul, pderiv_X_self, mul_one, map_add, map_mul, map_mul,
      Polynomial.derivative_mul, hp]
    simp [mul_comm, add_comm]

private noncomputable def restrictTotalDegreeEquivDegreeLT [Unique σ] (d : ℕ) :
    restrictTotalDegree σ k d ≃ₗ[k] Polynomial.degreeLT k (d + 1) :=
  (LinearEquiv.ofEq _ _ (by
    rw [restrictTotalDegree_eq_restrictSupport]
    congr 1
    ext μ
    simp [Finsupp.degree_eq_sum])).trans <|
    ((uniqueAlgEquiv k σ).toLinearEquiv.submoduleMap _).trans
      (LinearEquiv.ofEq _ _ (map_restrictSupport_uniqueAlgEquiv (d + 1)))

/-- In one variable, the range of the value map `firstJetValueMap P d` at `n` distinct points over
any field has dimension `min (d + 1) n`. -/
theorem finrank_range_firstJetValueMap_univariate [Unique σ] [Fintype ι]
    {P : ι → σ → k} (hP : Function.Injective P) (d : ℕ) :
    Module.finrank k (LinearMap.range (firstJetValueMap P d)) = min (d + 1) (Fintype.card ι) := by
  let a : ι → k := fun i ↦ P i default
  have ha : Function.Injective a := fun i j hij ↦
    hP (_root_.funext fun s ↦ by rw [Unique.eq_default s]; exact hij)
  let eDom := restrictTotalDegreeEquivDegreeLT (σ := σ) (k := k) d
  let eCod : ((i : ι) → Fin 1 → k) ≃ₗ[k] (ι → k) :=
    LinearEquiv.piCongrRight fun _ ↦ LinearEquiv.funUnique (Fin 1) k k
  let L := (LinearMap.pi fun i ↦ taylorJet (a i) 1) ∘ₗ
    (Polynomial.degreeLT k (d + 1)).subtype
  have hcomp : firstJetValueMap P d = eCod.toLinearMap ∘ₗ L ∘ₗ eDom.toLinearMap := by
    ext f i
    simpa [eDom, eCod, L, a, restrictTotalDegreeEquivDegreeLT] using
      (eval₂_uniqueAlgEquiv (R := k) (φ := RingHom.id k) (a := P i) (f := f.val)).symm
  rw [hcomp, LinearMap.range_comp, LinearMap.range_comp_of_range_eq_top _ eDom.range]
  simpa using (eCod.submoduleMap (LinearMap.range L)).finrank_eq.symm.trans
    (finrank_range_hermiteJet_degreeLT ha 1 (d + 1))

/-- In one variable, the range of `firstJetMap P d` at `n` distinct points over any field has
dimension `min (d + 1) (2 * n)`. -/
theorem finrank_range_firstJetMap_univariate [Unique σ] [Fintype ι]
    {P : ι → σ → k} (hP : Function.Injective P) (d : ℕ) :
    Module.finrank k (LinearMap.range (firstJetMap P d)) =
      min (d + 1) (2 * Fintype.card ι) := by
  let a : ι → k := fun i ↦ P i default
  have ha : Function.Injective a := fun i j hij ↦
    hP (_root_.funext fun s ↦ by rw [Unique.eq_default s]; exact hij)
  let eDom := restrictTotalDegreeEquivDegreeLT (σ := σ) (k := k) d
  let eCod : ((i : ι) → Fin 2 → k) ≃ₗ[k] (ι → Option σ → k) :=
    { toFun := fun v i z ↦ z.elim (v i 0) fun _ ↦ v i 1
      invFun := fun v i r ↦ if r = 0 then v i none else v i (some default)
      left_inv := fun v ↦ _root_.funext fun i ↦ _root_.funext fun r ↦ by fin_cases r <;> rfl
      right_inv := fun v ↦ _root_.funext fun i ↦ _root_.funext fun z ↦ by
        cases z with
        | none => rfl
        | some s => rw [Unique.eq_default s]; rfl
      map_add' := fun _ _ ↦ _root_.funext fun _ ↦ _root_.funext fun z ↦ by cases z <;> rfl
      map_smul' := fun _ _ ↦ _root_.funext fun _ ↦ _root_.funext fun z ↦ by cases z <;> rfl }
  let L := (LinearMap.pi fun i ↦ taylorJet (a i) 2) ∘ₗ
    (Polynomial.degreeLT k (d + 1)).subtype
  have hcomp : firstJetMap P d = eCod.toLinearMap ∘ₗ L ∘ₗ eDom.toLinearMap := by
    ext f i z
    cases z with
    | none =>
      simpa [eDom, eCod, L, a, restrictTotalDegreeEquivDegreeLT] using
        (eval₂_uniqueAlgEquiv (R := k) (φ := RingHom.id k) (a := P i) (f := f.val)).symm
    | some s =>
      rw [Unique.eq_default s]
      have hderiv :
          (eCod (L (eDom f))) i (some default) =
            (Polynomial.hasseDeriv 1 (uniqueAlgEquiv k σ f.val)).eval (P i default) := by
        simp [eCod, L, eDom, a, restrictTotalDegreeEquivDegreeLT]
      rw [firstJetMap_apply_some, LinearMap.comp_apply, LinearMap.comp_apply,
        LinearEquiv.coe_toLinearMap, LinearEquiv.coe_toLinearMap, hderiv,
        Polynomial.hasseDeriv_one, ← uniqueAlgEquiv_pderiv]
      exact (eval₂_uniqueAlgEquiv (R := k) (φ := RingHom.id k) (a := P i)
        (f := pderiv default f.val)).symm
  rw [hcomp, LinearMap.range_comp, LinearMap.range_comp_of_range_eq_top _ eDom.range]
  exact (eCod.submoduleMap (LinearMap.range L)).finrank_eq.symm.trans
    (finrank_range_hermiteJet_degreeLT ha 2 (d + 1))

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
    show 1 + 1 = 2 from rfl, mul_comm (Fintype.card ι) 2, min_eq_right_iff]

end Univariate

section CoordinateHyperplane

variable {σ ι k : Type*} [Field k]

private theorem killCompl_X_self (j₀ : σ) :
    killCompl (R := k) (Subtype.val_injective (p := fun j : σ ↦ j ≠ j₀)) (X j₀) = 0 := by
  classical
  rw [killCompl, aeval_X, dite_eq_right]
  simp

private theorem killCompl_X_of_ne (j₀ : σ) {j : σ} (hj : j ≠ j₀) :
    killCompl (R := k) (Subtype.val_injective (p := fun j : σ ↦ j ≠ j₀)) (X j) = X ⟨j, hj⟩ := by
  simpa using
    killCompl_rename_app (R := k) (Subtype.val_injective (p := fun j : σ ↦ j ≠ j₀)) (X ⟨j, hj⟩)

private theorem killCompl_mem_restrictTotalDegree {τ : Type*} {g : τ → σ}
    (hg : Function.Injective g) {m : ℕ} {f : MvPolynomial σ k}
    (hf : f ∈ restrictTotalDegree σ k m) :
    killCompl hg f ∈ restrictTotalDegree τ k m := by
  classical
  refine aeval_mem_restrictTotalDegree (fun j ↦ ?_) hf
  split_ifs
  · exact (totalDegree_monomial_le _ _).trans_eq (by simp)
  · simp

private theorem eval_killCompl (j₀ : σ) {x : σ → k} (hx : x j₀ = 0)
    (f : MvPolynomial σ k) :
    eval (fun l : {j : σ // j ≠ j₀} ↦ x l.val)
        (killCompl (Subtype.val_injective (p := fun j : σ ↦ j ≠ j₀)) f) =
      eval x f := by
  induction f using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p j hp =>
    rw [map_mul, map_mul, map_mul, hp]
    by_cases hj : j = j₀
    · subst hj
      rw [killCompl_X_self]
      simp [hx]
    · rw [killCompl_X_of_ne j₀ hj]
      simp

private theorem pderiv_killCompl (j₀ : σ) (l : {j : σ // j ≠ j₀})
    (f : MvPolynomial σ k) :
    pderiv l (killCompl (Subtype.val_injective (p := fun j : σ ↦ j ≠ j₀)) f) =
      killCompl (Subtype.val_injective (p := fun j : σ ↦ j ≠ j₀)) (pderiv l.val f) := by
  induction f using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p j hp =>
    rw [map_mul, pderiv_mul, pderiv_mul, map_add, map_mul, map_mul, hp]
    by_cases hj : j = j₀
    · subst hj
      rw [killCompl_X_self, pderiv_X_of_ne l.property.symm]
      simp
    · rw [killCompl_X_of_ne j₀ hj]
      by_cases hlj : j = l.val
      · have hlj' : (⟨j, hj⟩ : {j : σ // j ≠ j₀}) = l := Subtype.ext hlj
        rw [hlj', hlj]
        simp
      · have hlj' : (⟨j, hj⟩ : {j : σ // j ≠ j₀}) ≠ l := fun h ↦ hlj (congrArg Subtype.val h)
        simp [pderiv_X_of_ne hlj, pderiv_X_of_ne hlj']

private theorem pderiv_rename_of_ne (j₀ : σ) (g : MvPolynomial {j : σ // j ≠ j₀} k) :
    pderiv j₀ (rename Subtype.val g) = 0 := by
  induction g using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p l hp => simp [hp, pderiv_X_of_ne l.property]

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
  let slice : MvPolynomial σ k →ₐ[k] MvPolynomial σ' k :=
    killCompl (Subtype.val_injective (p := fun j : σ ↦ j ≠ j₀))
  let Φ : restrictTotalDegree σ k (d + 1) →ₗ[k]
      restrictTotalDegree σ' k (d + 1) × restrictTotalDegree σ' k d :=
    { toFun := fun f ↦
        (⟨slice f.val, killCompl_mem_restrictTotalDegree Subtype.val_injective f.property⟩,
         ⟨slice (pderiv j₀ f.val),
           killCompl_mem_restrictTotalDegree Subtype.val_injective <|
             (mem_restrictTotalDegree σ d _).2 <|
               (totalDegree_pderiv_le j₀ f.val).trans <|
                 Nat.sub_le_of_le_add ((mem_restrictTotalDegree σ (d + 1) _).1 f.property)⟩)
      map_add' := fun _ _ ↦ by ext <;> simp
      map_smul' := fun _ _ ↦ by ext <;> simp }
  have hΦ_surj : Function.Surjective Φ := by
    rintro ⟨g₀, g₁⟩
    let p : MvPolynomial σ k := rename Subtype.val g₀.val + X j₀ * rename Subtype.val g₁.val
    have hp : p ∈ restrictTotalDegree σ k (d + 1) := by
      rw [mem_restrictTotalDegree]
      refine (totalDegree_add _ _).trans (max_le ?_ ?_)
      · exact (totalDegree_rename_le Subtype.val g₀.val).trans
          ((mem_restrictTotalDegree σ' (d + 1) _).1 g₀.property)
      · refine (totalDegree_mul _ _).trans ?_
        have hX : (X j₀ : MvPolynomial σ k).totalDegree ≤ 1 :=
          (totalDegree_monomial_le _ _).trans_eq (by simp)
        have hg1 : (rename Subtype.val g₁.val).totalDegree ≤ d :=
          (totalDegree_rename_le Subtype.val g₁.val).trans
            ((mem_restrictTotalDegree σ' d _).1 g₁.property)
        omega
    refine ⟨⟨p, hp⟩, Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)⟩
    · simp only [Φ, slice, LinearMap.coe_mk, AddHom.coe_mk, p, map_add, map_mul,
        killCompl_rename_app]
      rw [killCompl_X_self, zero_mul, add_zero]
    · simp only [Φ, slice, LinearMap.coe_mk, AddHom.coe_mk, p, map_add, pderiv_rename_of_ne,
        zero_add, pderiv_mul, pderiv_X_self, one_mul, mul_zero, add_zero, killCompl_rename_app]
  let eCod : (ι → Option σ → k) ≃ₗ[k] (ι → Option σ' → k) × (ι → k) :=
    { toFun := fun y ↦ (fun i z ↦ z.elim (y i none) (fun l ↦ y i (some l.val)),
        fun i ↦ y i (some j₀))
      invFun := fun p i z ↦ match z with
        | none => p.fst i none
        | some j => if h : j = j₀ then p.snd i else p.fst i (some ⟨j, h⟩)
      left_inv := fun y ↦ _root_.funext fun i ↦ _root_.funext fun z ↦ by
        cases z with
        | none => rfl
        | some j => by_cases hj : j = j₀ <;> simp [hj]
      right_inv := fun ⟨y₀, y₁⟩ ↦ Prod.ext
        (_root_.funext fun i ↦ _root_.funext fun z ↦ by
          cases z with
          | none => rfl
          | some l => simp [l.property])
        (_root_.funext fun i ↦ by simp)
      map_add' := fun _ _ ↦
        Prod.ext (_root_.funext fun _ ↦ _root_.funext fun z ↦ by cases z <;> rfl) rfl
      map_smul' := fun _ _ ↦
        Prod.ext (_root_.funext fun _ ↦ _root_.funext fun z ↦ by cases z <;> rfl) rfl }
  have hcomp : eCod.toLinearMap ∘ₗ firstJetMap P (d + 1) =
      (firstJetMap P' (d + 1)).prodMap (firstJetValueMap P' d) ∘ₗ Φ := by
    ext f i z
    · cases z with
      | none =>
        simpa [eCod, Φ, slice, P'] using (eval_killCompl j₀ (hP i) f.val).symm
      | some l =>
        have hlhs : (eCod (firstJetMap P (d + 1) f)).fst i (some l) =
            eval (P i) (pderiv l.val f.val) := by
          simp [eCod]
        have hrhs :
            ((firstJetMap P' (d + 1)).prodMap (firstJetValueMap P' d) (Φ f)).fst i (some l) =
              eval (P' i) (pderiv l (slice f.val)) := by
          simp [Φ]
        rw [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, LinearMap.comp_apply, hlhs, hrhs,
          pderiv_killCompl, eval_killCompl j₀ (hP i)]
    · simpa [eCod, Φ, slice, P'] using (eval_killCompl j₀ (hP i) (pderiv j₀ f.val)).symm
  have hrange : LinearMap.range (eCod.toLinearMap ∘ₗ firstJetMap P (d + 1)) =
      (LinearMap.range (firstJetMap P' (d + 1))).prod
        (LinearMap.range (firstJetValueMap P' d)) := by
    rw [hcomp, LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.2 hΦ_surj)]
    ext ⟨u, v⟩
    simp [Submodule.mem_prod]
  have : Module.Finite k (restrictTotalDegree σ' k (d + 1)) :=
    Module.Finite.of_basis (basisRestrictTotalDegree σ' k (d + 1))
  have : Module.Finite k (restrictTotalDegree σ' k d) :=
    Module.Finite.of_basis (basisRestrictTotalDegree σ' k d)
  rw [rank_firstJetMatrix_eq_finrank_range,
    (eCod.submoduleMap (LinearMap.range (firstJetMap P (d + 1)))).finrank_eq,
    ← LinearMap.range_comp, hrange, (Submodule.prodEquiv _ _).finrank_eq, Module.finrank_prod]

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
  have h1 : Module.finrank k
      (LinearMap.range (firstJetMap (fun i (l : σ') ↦ P i l.val) (d + 1))) ≤
      (d + 1 + (Fintype.card σ - 1)).choose (Fintype.card σ - 1) := by
    have hrn := LinearMap.finrank_range_add_finrank_ker
      (firstJetMap (fun i (l : σ') ↦ P i l.val) (d + 1))
    have hdom := TauCeti.finrank_restrictTotalDegree σ' k (d + 1)
    rw [hcard] at hdom
    omega
  have h2 : Module.finrank k
      (LinearMap.range (firstJetValueMap (fun i (l : σ') ↦ P i l.val) d)) ≤
      (d + (Fintype.card σ - 1)).choose (Fintype.card σ - 1) := by
    have hrn := LinearMap.finrank_range_add_finrank_ker
      (firstJetValueMap (fun i (l : σ') ↦ P i l.val) d)
    have hdom := TauCeti.finrank_restrictTotalDegree σ' k d
    rw [hcard] at hdom
    omega
  exact add_le_add h1 h2

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
