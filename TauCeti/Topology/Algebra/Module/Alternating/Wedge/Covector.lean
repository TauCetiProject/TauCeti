/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
public import Mathlib.Analysis.Normed.Operator.Mul
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import TauCeti.Topology.Algebra.Module.Alternating.Wedge.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import TauCeti.LinearAlgebra.Alternating.TopDegree

/-!
# Top-degree wedges with a covector

Let `a` be a real covector on a space `E` of dimension `l + 1`, let `N` be its kernel, and let
`a(r) = 1`. For a real `l`-form `ψ`, inserting `r` into `a ∧ ψ` and restricting to `N` gives

`ι_r (a ∧ ψ) = a(r) ψ = ψ` on `N`,

because `a` vanishes on `N`. A top-degree form is determined by this restriction
(`AlternatingMap.curryLeft_compLinearMap_subtype_eq_zero_iff`), so `a ∧ ψ` vanishes exactly when
`ψ` vanishes on `N`
(`ContinuousAlternatingMap.pairedWedge_eq_zero_iff_compContinuousLinearMap_subtypeL_eq_zero`).
The direction `ψ = 0` on `N` implies `a ∧ ψ = 0` holds in every dimension
(`ContinuousAlternatingMap.pairedWedge_eq_zero_of_compContinuousLinearMap_subtypeL_eq_zero`): on
linearly independent vectors the wedge is computed on their span, of dimension `l + 1`. Consequently
`a ∧ ψ` depends only on the restriction of `ψ` to `N`
(`ContinuousAlternatingMap.pairedWedge_congr_right_of_compContinuousLinearMap_subtypeL_eq`).

This is the step from the contact volume form `α ∧ (dα)ⁿ` to the top power of `dα` on the
hyperplane `ker α`.

## References

* H. Geiges, *An Introduction to Contact Topology*, Cambridge University Press, 2008, Section 1.1.
-/

public section

open Module

namespace ContinuousAlternatingMap

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  {l : ℕ}

/-- **A wedge with a covector vanishes exactly on its kernel.** On a real vector space of
dimension `l + 1`, let `N` be the kernel of a covector `a` and let `a(r) = 1`. An `l`-form `ψ`
satisfies `a ∧ ψ = 0` exactly when `ψ` vanishes on `N`. -/
theorem pairedWedge_eq_zero_iff_compContinuousLinearMap_subtypeL_eq_zero
    (hn : finrank ℝ E = l + 1) (a : E [⋀^Fin 1]→L[ℝ] ℝ) (ψ : E [⋀^Fin l]→L[ℝ] ℝ)
    {N : Submodule ℝ E} (hN : ∀ u, u ∈ N ↔ a ![u] = 0) {r : E} (hr : a ![r] = 1) :
    pairedWedge (ContinuousLinearMap.mul ℝ ℝ) (ContinuousLinearMap.mul ℝ ℝ).continuous₂ a ψ = 0 ↔
      ψ.compContinuousLinearMap N.subtypeL = 0 := by
  -- The covector `a` as a linear functional `f`, whose kernel is `N`.
  set f : Dual ℝ E := ((ofSubsingleton ℝ E ℝ (0 : Fin 1)).symm a).toLinearMap
  have hf (u : E) : f u = a ![u] := by
    simp [f, Matrix.vec_single_eq_const]
  obtain rfl : N = LinearMap.ker f := by
    ext u
    rw [hN, LinearMap.mem_ker, hf]
  -- The interior product of `a ∧ ψ` with `r`, restricted to `N`, is `a(r) ψ = ψ` on `N`.
  have hι : (((pairedWedge (ContinuousLinearMap.mul ℝ ℝ) (ContinuousLinearMap.mul ℝ ℝ).continuous₂
      a ψ).toAlternatingMap.domDomCongr (finCongr (Nat.add_comm 1 l))).curryLeft r
      ).compLinearMap (LinearMap.ker f).subtype =
        (ψ.compContinuousLinearMap (LinearMap.ker f).subtypeL).toAlternatingMap := by
    ext w
    have hw (i : Fin l) : a ![(w i : E)] = 0 := (hN _).1 (w i).property
    have hcast : (Matrix.vecCons r fun i ↦ (w i : E)) ∘ ⇑(finCongr (Nat.add_comm 1 l)) =
        Matrix.vecCons r (fun i ↦ (w i : E)) ∘ Fin.cast (Nat.add_comm 1 l) := by
      ext
      simp
    simp only [AlternatingMap.compLinearMap_apply, AlternatingMap.curryLeft_apply_apply,
      AlternatingMap.domDomCongr_apply, coe_toAlternatingMap, Submodule.coe_subtype,
      compContinuousLinearMap_apply, Submodule.coe_subtypeL]
    rw [hcast, pairedWedge_apply_vecCons_of_forall _ _ _ _ r _ hw, hr,
      ContinuousLinearMap.mul_apply', one_mul, Function.comp_def]
  -- A top-degree form vanishes exactly when this restricted interior product does.
  rw [← toAlternatingMap_injective.eq_iff, toAlternatingMap_zero,
    ← AlternatingMap.domDomCongr_eq_zero_iff (finCongr (Nat.add_comm 1 l)),
    ← AlternatingMap.curryLeft_compLinearMap_subtype_eq_zero_iff hn _ ((hf r).trans hr), hι,
    ← toAlternatingMap_zero, toAlternatingMap_injective.eq_iff]

/-- **A wedge with a covector kills the forms vanishing on its kernel.** Let `N` be the kernel of a
real covector `a`. If an `l`-form `ψ` vanishes on `N`, then `a ∧ ψ = 0`. Unlike
`ContinuousAlternatingMap.pairedWedge_eq_zero_iff_compContinuousLinearMap_subtypeL_eq_zero`, this
direction holds in every dimension: on linearly independent vectors `v` the wedge is computed on
their span, which has dimension `l + 1`. -/
theorem pairedWedge_eq_zero_of_compContinuousLinearMap_subtypeL_eq_zero
    (a : E [⋀^Fin 1]→L[ℝ] ℝ) {ψ : E [⋀^Fin l]→L[ℝ] ℝ} {N : Submodule ℝ E}
    (hN : ∀ u, u ∈ N ↔ a ![u] = 0) (h : ψ.compContinuousLinearMap N.subtypeL = 0) :
    pairedWedge (ContinuousLinearMap.mul ℝ ℝ) (ContinuousLinearMap.mul ℝ ℝ).continuous₂ a ψ =
      0 := by
  ext v
  rw [coe_zero, Pi.zero_apply]
  by_cases hli : LinearIndependent ℝ v
  swap
  · exact AlternatingMap.map_linearDependent (pairedWedge _ _ a ψ).toAlternatingMap v hli
  by_cases hv : ∀ i, a ![v i] = 0
  · exact pairedWedge_apply_eq_zero_of_forall _ _ a ψ v hv
  obtain ⟨j, hj⟩ := not_forall.1 hv
  -- Restrict to the span `W` of the vectors `v i`, of dimension `l + 1`, where `a` is nonzero.
  set W := Submodule.span ℝ (Set.range v)
  have hW : finrank ℝ W = l + 1 := by
    rw [finrank_span_eq_card hli, Fintype.card_fin, Nat.add_comm]
  let w : Fin (1 + l) → W := fun i ↦ ⟨v i, Submodule.subset_span (Set.mem_range_self i)⟩
  -- The vector `a(v j)⁻¹ v j` of `W`, computed through the linear functional of `a`.
  have hf := ofSubsingleton_symm_apply_apply ℝ E ℝ (0 : Fin 1) a
  have hr : a.compContinuousLinearMap W.subtypeL ![(a ![v j])⁻¹ • w j] = 1 := by
    simp only [Matrix.vec_single_eq_const, ← hf] at hj
    simp only [compContinuousLinearMap_apply, Function.comp_def, Matrix.vec_single_eq_const,
      Submodule.coe_subtypeL, Submodule.coe_subtype, SetLike.val_smul, ← hf, map_smul,
      smul_eq_mul]
    exact inv_mul_cancel₀ hj
  have key := (pairedWedge_eq_zero_iff_compContinuousLinearMap_subtypeL_eq_zero hW
    (a.compContinuousLinearMap W.subtypeL) (ψ.compContinuousLinearMap W.subtypeL)
    (N := N.comap W.subtype) (fun u ↦ by simp [hN, Function.comp_def, Matrix.vec_single_eq_const])
    hr).2 (by
    ext u
    simpa [Function.comp_def] using
      congrArg (fun φ : N [⋀^Fin l]→L[ℝ] ℝ ↦ φ fun i ↦ ⟨u i, (u i).property⟩) h)
  have hw := congrArg (fun φ : W [⋀^Fin (1 + l)]→L[ℝ] ℝ ↦ φ w) key
  rw [← pairedWedge_compContinuousLinearMap, compContinuousLinearMap_apply] at hw
  exact hw

/-- **A wedge with a covector only sees its kernel.** Let `N` be the kernel of a real covector `a`.
Two `l`-forms `ψ` and `ψ'` which agree on `N` have the same wedge with `a`: `a ∧ ψ = a ∧ ψ'`. -/
theorem pairedWedge_congr_right_of_compContinuousLinearMap_subtypeL_eq
    (a : E [⋀^Fin 1]→L[ℝ] ℝ) {ψ ψ' : E [⋀^Fin l]→L[ℝ] ℝ}
    {N : Submodule ℝ E} (hN : ∀ u, u ∈ N ↔ a ![u] = 0)
    (h : ψ.compContinuousLinearMap N.subtypeL = ψ'.compContinuousLinearMap N.subtypeL) :
    pairedWedge (ContinuousLinearMap.mul ℝ ℝ) (ContinuousLinearMap.mul ℝ ℝ).continuous₂ a ψ =
      pairedWedge (ContinuousLinearMap.mul ℝ ℝ) (ContinuousLinearMap.mul ℝ ℝ).continuous₂ a ψ' := by
  -- The difference `ψ' - ψ` vanishes on `N`, hence so does its wedge with `a`.
  have hdiff := pairedWedge_eq_zero_of_compContinuousLinearMap_subtypeL_eq_zero a (ψ := ψ' - ψ) hN
    (by
      ext w
      simpa only [compContinuousLinearMap_apply, sub_apply, coe_zero, Pi.zero_apply,
        sub_eq_zero] using (congrArg (fun φ : N [⋀^Fin l]→L[ℝ] ℝ ↦ φ w) h).symm)
  rw [← add_sub_cancel ψ ψ', pairedWedge_add_right, hdiff, add_zero]

end ContinuousAlternatingMap
