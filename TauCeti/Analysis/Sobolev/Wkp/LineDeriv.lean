/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Wkp.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Directional derivatives of higher-order Sobolev functions

A function `u ∈ Lᵖ(Ω)` lies in `W^{k+1,p}(Ω)` exactly when, in every direction `v`, it has a weak
derivative `∂_v u` lying in `W^{k,p}(Ω)`; it suffices to check the directions of one orthonormal
basis. This is the description of the Sobolev scale by first derivatives,
`W^{k+1,p}(Ω) = {u ∈ Lᵖ(Ω) : ∂ᵢu ∈ W^{k,p}(Ω) for every i}`, and it is what lets a statement about
`W^{k,p}` be proved by induction on `k` one derivative at a time.

`TauCeti.Wkp` records the derivatives of `u` from the bottom up: the gradient first, and then the
weak Fréchet derivative of the previous field. The fields of `∂_v u` are therefore those of `u`
with `v` substituted in the innermost slot, the one belonging to the gradient. At the first level
this substitution is `A ↦ A† v`, since the gradient is identified with a vector through the inner
product. Conversely, the fields of `u` are reassembled from those of the `∂ᵢu` by inserting
`⟪eᵢ, ·⟫` in the innermost slot. Neither direction uses the symmetry of weak second derivatives.

No boundedness or boundary regularity of `Ω` is assumed.

## Main declarations

* `TauCeti.Wkp.exists_hasWeakLineDerivOn_value`: every directional weak derivative of an element
  of `W^{k+1,p}(Ω)` lies in `W^{k,p}(Ω)`.
* `TauCeti.Wkp.exists_value_eq_of_forall_hasWeakLineDerivOn`: if the weak derivatives of
  `u ∈ Lᵖ(Ω)` along an orthonormal basis lie in `W^{k,p}(Ω)`, then `u ∈ W^{k+1,p}(Ω)`.
* `TauCeti.Wkp.exists_value_eq_iff_forall_exists_hasWeakLineDerivOn`: the two combined.
* `TauCeti.W1p.exists_lowerOrder_eq_of_forall_hasWeakLineDerivOn`: the second-order case in the
  form a difference-quotient argument supplies, with `Lᵖ` weak derivatives of the components
  `⟪∇u, eⱼ⟫` of the weak gradient.

## References

* L. C. Evans, *Partial Differential Equations*, §5.2.2.
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory TopologicalSpace
open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-! ### Substituting and inserting a direction in the innermost slot -/

/-- Substitute `v` in the innermost slot of an iterated gradient. At order one this is
`A ↦ A† v`, the vector `w` with `⟪w, h⟫ = ⟪v, A h⟫`; at higher orders it acts on the value of
the outer slots. -/
private def contractL (v : E) : (j : ℕ) → IteratedGradient E (j + 1) →L[ℝ] IteratedGradient E j
  | 0 => LinearMap.toContinuousLinearMap
      { toFun := fun A : E →L[ℝ] E => ContinuousLinearMap.adjoint A v
        map_add' := fun A B => by simp
        map_smul' := fun c A => by simp }
  | j + 1 => ContinuousLinearMap.compL ℝ E _ _ (contractL v j)

/-- Insert the functional `⟪w, ·⟫` with value `e` in the innermost slot of an iterated gradient:
at order zero `w ↦ (h ↦ ⟪w, h⟫ e)`, and at higher orders the same on the value of the outer
slots. -/
private def insertL (e : E) : (j : ℕ) → IteratedGradient E j →L[ℝ] IteratedGradient E (j + 1)
  | 0 => LinearMap.toContinuousLinearMap
      { toFun := fun w : E => (innerSL ℝ w).smulRight e
        map_add' := fun w w' => by ext; simp [add_smul]
        map_smul' := fun c w => by ext; simp [smul_smul] }
  | j + 1 => ContinuousLinearMap.compL ℝ E _ _ (insertL e j)

private theorem inner_contractL_zero (v : E) (A : E →L[ℝ] E) (h : E) :
    ⟪contractL v 0 A, h⟫_ℝ = ⟪v, A h⟫_ℝ :=
  ContinuousLinearMap.adjoint_inner_left A h v

private theorem insertL_zero_apply (e w h : E) : insertL e 0 w h = ⟪w, h⟫_ℝ • e :=
  (rfl)

private theorem contractL_succ_apply (v : E) (j : ℕ) (A : IteratedGradient E (j + 2)) :
    contractL v (j + 1) A = (contractL v j).comp A :=
  (rfl)

private theorem insertL_succ_apply (e : E) (j : ℕ) (A : IteratedGradient E (j + 1)) :
    insertL e (j + 1) A = (insertL e j).comp A :=
  (rfl)

variable [MeasurableSpace E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {Omega : Opens E} {p : ENNReal} [Fact (1 ≤ p)]

/-! ### From `W^{k+1,p}` to the directional derivatives -/

/-- The first-order case of `TauCeti.Wkp.exists_wkp_lineDeriv`: a directional derivative of an
element of `W^{2,p}(Ω)` lies in `W^{1,p}(Ω)`, with gradient obtained by substituting the
direction in the innermost slot of the Hessian field. -/
private theorem Wkp.exists_wkp_lineDeriv_zero (v : E) (w : Wkp mu Omega p 2) :
    ∃ d : Wkp mu Omega p 1, HasWeakLineDerivOn mu Omega (Wkp.value 2 w) (Wkp.value 1 d) v ∧
      Wkp.iteratedGradient 0 d = (contractL v 0).compLp (Wkp.iteratedGradient 1 w) := by
  set w₁ := Wkp.lowerOrder 1 w
  have hH := Wkp.hasWeakFDerivOn_iteratedGradient 0 w
  -- the candidate value `⟪v, ∇u⟫` and its weak gradient `(D²u)† v`
  have hd : HasWeakFDerivOn mu Omega ((innerSL ℝ v).compLp (Wkp.iteratedGradient 0 w₁))
      (fun x => innerSL ℝ ((contractL v 0).compLp (Wkp.iteratedGradient 1 w) x)) := by
    refine ((hH.clm_comp (innerSL ℝ v)).congr_ae ?_).congr_ae_deriv ?_
    · filter_upwards [(innerSL ℝ v).coeFn_compLp (Wkp.iteratedGradient 0 w₁)] with x hx
      rw [hx]
    · filter_upwards [(contractL v 0).coeFn_compLp (Wkp.iteratedGradient 1 w)] with x hx
      ext h
      rw [hx, innerSL_apply_apply, inner_contractL_zero, ContinuousLinearMap.comp_apply,
        innerSL_apply_apply]
  refine ⟨W1p.mk _ _ hd, ?_, (Wkp.iteratedGradient_zero _).trans (W1p.gradient_mk _ _ hd)⟩
  rw [Wkp.value_one (W1p.mk _ _ hd), W1p.value_mk, Wkp.value_succ]
  have hu := (Wkp.hasWeakFDerivOn_value w₁).hasWeakLineDerivOn v
  refine hu.congr_ae_deriv ?_
  filter_upwards [(innerSL ℝ v).coeFn_compLp (Wkp.iteratedGradient 0 w₁)] with x hx
  rw [hx, innerSL_apply_apply, innerSL_apply_apply, real_inner_comm]

/-- A directional derivative of an element of `W^{k+2,p}(Ω)` lies in `W^{k+1,p}(Ω)`, and its
highest derivative is obtained by substituting the direction in the innermost slot of the
highest derivative of the original function. -/
private theorem Wkp.exists_wkp_lineDeriv (v : E) :
    ∀ (k : ℕ) (w : Wkp mu Omega p (k + 2)), ∃ d : Wkp mu Omega p (k + 1),
      HasWeakLineDerivOn mu Omega (Wkp.value (k + 2) w) (Wkp.value (k + 1) d) v ∧
        Wkp.iteratedGradient k d = (contractL v k).compLp (Wkp.iteratedGradient (k + 1) w)
  | 0, w => Wkp.exists_wkp_lineDeriv_zero v w
  | k + 1, w => by
      obtain ⟨d, hd, hdk⟩ := Wkp.exists_wkp_lineDeriv v k (Wkp.lowerOrder (k + 2) w)
      have hD : HasWeakFDerivOn mu Omega (Wkp.iteratedGradient k d)
          ((contractL v (k + 1)).compLp (Wkp.iteratedGradient (k + 2) w)) := by
        rw [hdk]
        refine (((Wkp.hasWeakFDerivOn_iteratedGradient (k + 1) w).clm_comp
          (contractL v k)).congr_ae ?_).congr_ae_deriv ?_
        · exact Filter.EventuallyEq.symm ((contractL v k).coeFn_compLp _)
        · filter_upwards [(contractL v (k + 1)).coeFn_compLp (Wkp.iteratedGradient (k + 2) w)]
            with x hx
          rw [hx, contractL_succ_apply]
      refine ⟨Wkp.mk k d _ hD, ?_, Wkp.iteratedGradient_mk k d _ hD⟩
      rw [Wkp.value_mk, Wkp.value_succ (k + 2) w]
      exact hd

/-- **Directional derivatives of Sobolev functions are Sobolev.** In every direction `v`, an
element of `W^{k+1,p}(Ω)` has a weak derivative which is the value of an element of
`W^{k,p}(Ω)`. -/
theorem Wkp.exists_hasWeakLineDerivOn_value :
    ∀ (k : ℕ) (w : Wkp mu Omega p (k + 1)) (v : E), ∃ d : Wkp mu Omega p k,
      HasWeakLineDerivOn mu Omega (Wkp.value (k + 1) w) (Wkp.value k d) v
  | 0, w, v => by
      refine ⟨(innerSL ℝ v).compLp (Wkp.iteratedGradient 0 w), ?_⟩
      rw [Wkp.value_zero]
      refine ((Wkp.hasWeakFDerivOn_value w).hasWeakLineDerivOn v).congr_ae_deriv ?_
      filter_upwards [(innerSL ℝ v).coeFn_compLp (Wkp.iteratedGradient 0 w)] with x hx
      rw [hx, innerSL_apply_apply, innerSL_apply_apply, real_inner_comm]
  | k + 1, w, v => (Wkp.exists_wkp_lineDeriv v k w).imp fun _ h => h.1

/-! ### From the directional derivatives to `W^{k+1,p}` -/

section Assembly

variable {ι : Type*} [Fintype ι]

/-- The first-order case of `TauCeti.Wkp.exists_value_eq_of_forall_hasWeakLineDerivOn`: weak
derivatives in `Lᵖ(Ω)` along an orthonormal basis assemble into a weak gradient. -/
private theorem W1p.exists_value_eq_gradient_eq (b : OrthonormalBasis ι ℝ E)
    (u : Lp ℝ p (mu.restrict Omega)) (d : ι → Lp ℝ p (mu.restrict Omega))
    (hd : ∀ i, HasWeakLineDerivOn mu Omega u (d i) (b i)) :
    ∃ w : W1p mu Omega p, W1p.value w = u ∧
      W1p.gradient w = ∑ i, (ContinuousLinearMap.toSpanSingleton ℝ (b i)).compLp (d i) := by
  classical
  set g := ∑ i, (ContinuousLinearMap.toSpanSingleton ℝ (b i)).compLp (d i)
  have hg : ∀ k, (fun x => innerSL ℝ (g x) (b k)) =ᵐ[mu.restrict Omega] d k := by
    intro k
    filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ
      fun i => (ContinuousLinearMap.toSpanSingleton ℝ (b i)).compLp (d i),
      ae_all_iff.mpr fun i => (ContinuousLinearMap.toSpanSingleton ℝ (b i)).coeFn_compLp (d i)]
      with x hsum hcomp
    rw [hsum, innerSL_apply_apply, sum_inner]
    simp [hcomp, inner_smul_left, OrthonormalBasis.inner_eq_ite]
  have hu : LocallyIntegrableOn (u : E → ℝ) Omega mu :=
    locallyIntegrableOn_of_locallyIntegrable_restrict ((Lp.memLp u).locallyIntegrable Fact.out)
  have hw : HasWeakFDerivOn mu Omega u (fun x => innerSL ℝ (g x)) :=
    b.toBasis.hasWeakFDerivOn_of_forall hu fun k => by
      simpa only [OrthonormalBasis.coe_toBasis] using (hd k).congr_ae_deriv (hg k).symm
  exact ⟨W1p.mk u g hw, W1p.value_mk u g hw, W1p.gradient_mk u g hw⟩

/-- The second-order case of `TauCeti.Wkp.exists_wkp_succ_of_forall`. -/
private theorem Wkp.exists_wkp_two_of_forall (b : OrthonormalBasis ι ℝ E)
    (u : Lp ℝ p (mu.restrict Omega)) (d : ι → Wkp mu Omega p 1)
    (hd : ∀ i, HasWeakLineDerivOn mu Omega u (Wkp.value 1 (d i)) (b i)) :
    ∃ w : Wkp mu Omega p 2, Wkp.value 2 w = u ∧ Wkp.iteratedGradient 1 w =
      ∑ i, (insertL (b i) 0).compLp (Wkp.iteratedGradient 0 (d i)) := by
  obtain ⟨w₁, hw₁, hg₁⟩ := W1p.exists_value_eq_gradient_eq b u _ hd
  set D := ∑ i, (insertL (b i) 0).compLp (Wkp.iteratedGradient 0 (d i))
  -- `∇u = ∑ᵢ (∂ᵢu) eᵢ`, and each summand has weak derivative `h ↦ ⟪∇∂ᵢu, h⟫ eᵢ`
  have hD : HasWeakFDerivOn mu Omega (Wkp.iteratedGradient 0 w₁) D := by
    have hsum := HasWeakFDerivOn.sum Finset.univ fun i _ =>
      (Wkp.hasWeakFDerivOn_value (d i)).clm_comp (ContinuousLinearMap.toSpanSingleton ℝ (b i))
    rw [Wkp.iteratedGradient_zero w₁, hg₁]
    refine (hsum.congr_ae ?_).congr_ae_deriv ?_
    · filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ
        fun i => (ContinuousLinearMap.toSpanSingleton ℝ (b i)).compLp (Wkp.value 1 (d i)),
        ae_all_iff.mpr fun i =>
          (ContinuousLinearMap.toSpanSingleton ℝ (b i)).coeFn_compLp (Wkp.value 1 (d i))]
        with x hsum hcomp
      simp only [hsum, hcomp]
    · filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ
        fun i => (insertL (b i) 0).compLp (Wkp.iteratedGradient 0 (d i)),
        ae_all_iff.mpr fun i => (insertL (b i) 0).coeFn_compLp (Wkp.iteratedGradient 0 (d i))]
        with x hsum hcomp
      refine (Finset.sum_congr rfl fun i _ => ?_).trans hsum.symm
      ext h
      rw [hcomp i, insertL_zero_apply]
      simp
  refine ⟨Wkp.mk 0 w₁ D hD, ?_, Wkp.iteratedGradient_mk 0 w₁ D hD⟩
  rw [Wkp.value_mk 0 w₁ D hD, Wkp.value_one w₁, hw₁]

/-- Elements of `W^{k+1,p}(Ω)` that are weak derivatives of `u` along an orthonormal basis assemble
into an element of `W^{k+2,p}(Ω)` with value `u`, whose highest derivative is obtained by
inserting the basis functionals in the innermost slot. -/
private theorem Wkp.exists_wkp_succ_of_forall (b : OrthonormalBasis ι ℝ E)
    (u : Lp ℝ p (mu.restrict Omega)) :
    ∀ (k : ℕ) (d : ι → Wkp mu Omega p (k + 1)),
      (∀ i, HasWeakLineDerivOn mu Omega u (Wkp.value (k + 1) (d i)) (b i)) →
      ∃ w : Wkp mu Omega p (k + 2), Wkp.value (k + 2) w = u ∧ Wkp.iteratedGradient (k + 1) w =
        ∑ i, (insertL (b i) k).compLp (Wkp.iteratedGradient k (d i))
  | 0, d, hd => Wkp.exists_wkp_two_of_forall b u d hd
  | k + 1, d, hd => by
      obtain ⟨w, hw, hwk⟩ := Wkp.exists_wkp_succ_of_forall b u k
        (fun i => Wkp.lowerOrder (k + 1) (d i)) fun i => by
          simpa only [← Wkp.value_succ] using hd i
      set D := ∑ i, (insertL (b i) (k + 1)).compLp (Wkp.iteratedGradient (k + 1) (d i))
      have hD : HasWeakFDerivOn mu Omega (Wkp.iteratedGradient (k + 1) w) D := by
        have hsum := HasWeakFDerivOn.sum Finset.univ fun i _ =>
          (Wkp.hasWeakFDerivOn_iteratedGradient k (d i)).clm_comp (insertL (b i) k)
        rw [hwk]
        refine (hsum.congr_ae ?_).congr_ae_deriv ?_
        · filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ fun i => (insertL (b i) k).compLp
            (Wkp.iteratedGradient k (Wkp.lowerOrder (k + 1) (d i))),
            ae_all_iff.mpr fun i => (insertL (b i) k).coeFn_compLp
              (Wkp.iteratedGradient k (Wkp.lowerOrder (k + 1) (d i)))]
            with x hsum hcomp
          simp only [hsum, hcomp]
        · filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ fun i =>
            (insertL (b i) (k + 1)).compLp (Wkp.iteratedGradient (k + 1) (d i)),
            ae_all_iff.mpr fun i => (insertL (b i) (k + 1)).coeFn_compLp
              (Wkp.iteratedGradient (k + 1) (d i))]
            with x hsum hcomp
          rw [hsum]
          exact Finset.sum_congr rfl fun i _ => by rw [hcomp i, insertL_succ_apply]
      refine ⟨Wkp.mk (k + 1) w D hD, ?_, Wkp.iteratedGradient_mk (k + 1) w D hD⟩
      rw [Wkp.value_mk, hw]

/-- **Sobolev functions from their directional derivatives.** If, along every vector of an
orthonormal basis, `u ∈ Lᵖ(Ω)` has a weak derivative which is the value of an element of
`W^{k,p}(Ω)`, then `u` is the value of an element of `W^{k+1,p}(Ω)`. -/
theorem Wkp.exists_value_eq_of_forall_hasWeakLineDerivOn (b : OrthonormalBasis ι ℝ E)
    (u : Lp ℝ p (mu.restrict Omega)) :
    ∀ k : ℕ, (∀ i, ∃ d : Wkp mu Omega p k,
      HasWeakLineDerivOn mu Omega u (Wkp.value k d) (b i)) →
      ∃ w : Wkp mu Omega p (k + 1), Wkp.value (k + 1) w = u
  | 0, h => by
      choose d hd using h
      obtain ⟨w, hw, -⟩ := W1p.exists_value_eq_gradient_eq b u d fun i => by
        simpa only [Wkp.value_zero] using hd i
      exact ⟨w, (Wkp.value_one w).trans hw⟩
  | k + 1, h => by
      choose d hd using h
      obtain ⟨w, hw, -⟩ := Wkp.exists_wkp_succ_of_forall b u k d hd
      exact ⟨w, hw⟩

end Assembly

/-- **The Sobolev scale by first derivatives.** A function `u ∈ Lᵖ(Ω)` is the value of an element
of `W^{k+1,p}(Ω)` exactly when, in every direction, it has a weak derivative which is the value of
an element of `W^{k,p}(Ω)`. -/
theorem Wkp.exists_value_eq_iff_forall_exists_hasWeakLineDerivOn (k : ℕ)
    (u : Lp ℝ p (mu.restrict Omega)) :
    (∃ w : Wkp mu Omega p (k + 1), Wkp.value (k + 1) w = u) ↔
      ∀ v : E, ∃ d : Wkp mu Omega p k, HasWeakLineDerivOn mu Omega u (Wkp.value k d) v := by
  refine ⟨fun ⟨w, hw⟩ v => hw ▸ Wkp.exists_hasWeakLineDerivOn_value k w v, fun h => ?_⟩
  exact Wkp.exists_value_eq_of_forall_hasWeakLineDerivOn (stdOrthonormalBasis ℝ E) u k
    fun i => h _

/-! ### Second order from the components of the gradient -/

/-- **Second-order weak differentiability from directional derivatives.** Fix an orthonormal
basis `e` of `E`. If, for every pair of indices `i, j`, the scalar component `⟪∇u, eⱼ⟫` of the
weak gradient of `u ∈ W^{1,p}(Ω)` has a weak derivative in `Lᵖ(Ω)` in the direction `eᵢ`, then
`u` is the first-order part of an element of `W^{2,p}(Ω)`.

This is how a difference-quotient argument, which produces exactly these componentwise
derivatives, certifies membership in the second-order Sobolev space. -/
theorem W1p.exists_lowerOrder_eq_of_forall_hasWeakLineDerivOn {ι : Type*} [Fintype ι]
    (u : W1p mu Omega p) (b : OrthonormalBasis ι ℝ E)
    (h : ∀ i j : ι, ∃ g : Lp ℝ p (mu.restrict Omega),
      HasWeakLineDerivOn mu Omega (fun x => ⟪W1p.gradient u x, b j⟫_ℝ) g (b i)) :
    ∃ U : Wkp mu Omega p 2, Wkp.lowerOrder 1 U = u := by
  have hgrad : ∀ j, (fun x => ⟪W1p.gradient u x, b j⟫_ℝ) =ᵐ[mu.restrict Omega]
      (innerSL ℝ (b j)).compLp (W1p.gradient u) := fun j => by
    filter_upwards [(innerSL ℝ (b j)).coeFn_compLp (W1p.gradient u)] with x hx
    rw [hx, innerSL_apply_apply, real_inner_comm]
  -- each component `∂ⱼu = ⟪∇u, eⱼ⟫` lies in `W^{1,p}(Ω)`, so `u ∈ W^{2,p}(Ω)`
  have hcomp : ∀ j, ∃ d : Wkp mu Omega p 1,
      HasWeakLineDerivOn mu Omega (W1p.value u) (Wkp.value 1 d) (b j) := fun j => by
    obtain ⟨d, hd⟩ := Wkp.exists_value_eq_of_forall_hasWeakLineDerivOn b
      ((innerSL ℝ (b j)).compLp (W1p.gradient u)) 0 fun i =>
        (h i j).imp fun _ hg => by simpa only [Wkp.value_zero] using hg.congr_ae (hgrad j)
    refine ⟨d, ?_⟩
    rw [hd]
    exact ((W1p.hasWeakFDerivOn u).hasWeakLineDerivOn (b j)).congr_ae_deriv (hgrad j)
  obtain ⟨U, hU⟩ := Wkp.exists_value_eq_of_forall_hasWeakLineDerivOn b (W1p.value u) 1 hcomp
  exact ⟨U, W1p.ext_value (((Wkp.value_one _).symm.trans (Wkp.value_succ 1 U).symm).trans hU)⟩

end TauCeti
