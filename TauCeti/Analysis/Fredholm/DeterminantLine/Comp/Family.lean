/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fredholm.DeterminantLine.Comp.Chart
public import TauCeti.LinearAlgebra.TensorProduct.Separation
import TauCeti.LinearAlgebra.Ray

/-!
# The composition law of Fredholm determinant lines along families

The composition law `det (g ∘ f) ≃ det f ⊗ det g` of determinant lines
(`LinearMap.detLineCompEquiv`) is read in the composite of kernel charts of `f` and `g` as the
product of the readings, up to a sign which, after the normalization
`(-1) ^ (dim coker f * r + t * dim coker g)`, depends only on the charts
(`ContinuousLinearMap.detLineChartEquiv_neg_one_pow_smul_comp`). Here `r` and `t` are the ranks of
the maps `ker (g ∘ f) → ker g` and `coker f → coker (g ∘ f)` of the kernel–cokernel sequence of
`g ∘ f`. This file deduces that, over `ℝ`, the normalized composition law carries continuous
orientations of the determinant lines of two composable continuous families of Fredholm operators
to a continuous orientation of the determinant lines of their composite
(`TauCeti.IsDetLineCoherentOn.clm_comp`). The composite chart moves with the operators; near each
parameter it is a positive multiple of the chart with the data frozen
(`ContinuousLinearMap.eventually_detLineChartEquiv_eq_smul`). Consequently orientation transport
along a composite of paths of Fredholm operators is the composite of the transports
(`TauCeti.detLineOrientationTransport_clm_comp`).

## Main results

* `TauCeti.IsDetLineCoherentOn.clm_comp`: normalized composites of coherent families are coherent.
* `TauCeti.detLineOrientationTransport_clm_comp`: orientation transport commutes with the
  composition law.

## References

* A. Zinger, *The determinant line bundle for Fredholm operators: construction, properties, and
  classification*, Math. Scand. 118 (2016), 203–268, arXiv:1304.6368 (the continuity of the
  composition isomorphisms of determinant lines).
-/

public section

open Module TensorProduct

namespace TauCeti

open Filter Set Topology ContinuousLinearMap

section Coherent

/-! ### Coherence of the composition law along families -/

variable {E F P X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] [NormedAddCommGroup P]
  [NormedSpace ℝ P] [CompleteSpace P] [TopologicalSpace X] {f : X → E →L[ℝ] F}
  {g : X → F →L[ℝ] P} {s : Set X} {x₀ : X}

omit [CompleteSpace E] [CompleteSpace F] in
/-- The composite kernel coordinate depends continuously on the first operator: it is a constant
plus `(x, l) ↦ (0, q₂ (f x, 0))`. -/
private theorem continuousWithinAt_compKerCoord {Λ₁ Λ₂ G₁ G₂ : Type*} [NormedAddCommGroup Λ₁]
    [NormedSpace ℝ Λ₁] [NormedAddCommGroup Λ₂] [NormedSpace ℝ Λ₂] [NormedAddCommGroup G₁]
    [NormedSpace ℝ G₁] [NormedAddCommGroup G₂] [NormedSpace ℝ G₂] {D₁ : Λ₁ →L[ℝ] F}
    {q₁ : E × Λ₁ →L[ℝ] G₁} {q₂ : F × Λ₂ →L[ℝ] G₂} (hf : ContinuousWithinAt f s x₀) :
    ContinuousWithinAt (fun x ↦ compKerCoord (f x) D₁ q₁ q₂) s x₀ := by
  have heq : (fun x ↦ compKerCoord (f x) D₁ q₁ q₂) = fun x ↦ compKerCoord 0 D₁ q₁ q₂ +
      (inr ℝ G₁ G₂ ∘L q₂ ∘L inl ℝ F Λ₂ ∘L f x) ∘L fst ℝ E (Λ₁ × Λ₂) := by
    funext x
    refine ContinuousLinearMap.ext fun ⟨y, l⟩ ↦ Prod.ext ?_ ?_
    · simp
    · simp only [compKerCoord_apply, add_apply, comp_apply, inl_apply, inr_apply, Prod.snd_add,
        zero_apply, zero_add]
      rw [← map_add, Prod.mk_add_mk, add_comm, add_zero]
      rfl
  rw [heq]
  exact continuousWithinAt_const.add ((continuousWithinAt_const.clm_comp
    (continuousWithinAt_const.clm_comp (continuousWithinAt_const.clm_comp hf))).clm_comp
      continuousWithinAt_const)

variable {v : ∀ x, (f x : E →ₗ[ℝ] F).detLine} {w : ∀ x, (g x : F →ₗ[ℝ] P).detLine}
  {u : ∀ x, ((g x).comp (f x) : E →ₗ[ℝ] P).detLine}

omit [CompleteSpace F] in
/-- The step of `TauCeti.IsDetLineCoherentOn.clm_comp` at one parameter: if kernel charts of `f` and
`g` valid at `x₀` read `v x` and `w x`, for `x ∈ s` near `x₀`, as nonnegative multiples of their
readings at `x₀`, then the normalized composite family is coherent within `s` at `x₀`. The composite
chart moves with `g x` and `f x`; near `x₀` it is a positive multiple of the chart frozen at `x₀`
(`ContinuousLinearMap.eventually_detLineChartEquiv_eq_smul`). -/
private theorem isDetLineCoherentWithinAt_clm_comp {Λ₁ G₁ Λ₂ G₂ : Type*} [NormedAddCommGroup Λ₁]
    [NormedSpace ℝ Λ₁] [FiniteDimensional ℝ Λ₁] [NormedAddCommGroup G₁] [NormedSpace ℝ G₁]
    [FiniteDimensional ℝ G₁] [NormedAddCommGroup Λ₂] [NormedSpace ℝ Λ₂] [FiniteDimensional ℝ Λ₂]
    [NormedAddCommGroup G₂] [NormedSpace ℝ G₂] [FiniteDimensional ℝ G₂] {D₁ : Λ₁ →L[ℝ] F}
    {q₁ : E × Λ₁ →L[ℝ] G₁} {D₂ : Λ₂ →L[ℝ] P} {q₂ : F × Λ₂ →L[ℝ] G₂} (hx₀ : x₀ ∈ s)
    (hf : ContinuousOn f s) (hg : ContinuousOn g s)
    (hFf : ∀ x ∈ s, IsFredholm (f x)) (hFg : ∀ x ∈ s, IsFredholm (g x))
    (hv : ∀ x ∈ s, v x ≠ 0) (hw : ∀ x ∈ s, w x ≠ 0)
    (hu : ∀ x ∈ s, ∀ [FiniteDimensional ℝ (f x).ker] [FiniteDimensional ℝ (F ⧸ (f x).range)]
      [FiniteDimensional ℝ (g x).ker] [FiniteDimensional ℝ (P ⧸ (g x).range)],
      u x = (-1 : ℝ) ^ (finrank ℝ (F ⧸ (f x).range) *
          finrank ℝ (LinearMap.range ((f x : E →ₗ[ℝ] F).kerCompToKer (g x : F →ₗ[ℝ] P))) +
        finrank ℝ (LinearMap.range ((f x : E →ₗ[ℝ] F).cokerToCokerComp (g x : F →ₗ[ℝ] P))) *
          finrank ℝ (P ⧸ (g x).range)) •
        ((f x : E →ₗ[ℝ] F).detLineCompEquiv (g x : F →ₗ[ℝ] P)).symm (v x ⊗ₜ w x))
    (h₀₁ : (((f x₀).coprod D₁).prod q₁).IsInvertible)
    (h₀₂ : (((g x₀).coprod D₂).prod q₂).IsInvertible)
    (hev₁ : ∀ᶠ x in 𝓝[s] x₀, ∃ h : (((f x).coprod D₁).prod q₁).IsInvertible,
      SameRay ℝ (detLineChartEquiv (f x) D₁ q₁ h (v x)) (detLineChartEquiv (f x₀) D₁ q₁ h₀₁ (v x₀)))
    (hev₂ : ∀ᶠ x in 𝓝[s] x₀, ∃ h : (((g x).coprod D₂).prod q₂).IsInvertible,
      SameRay ℝ (detLineChartEquiv (g x) D₂ q₂ h (w x))
        (detLineChartEquiv (g x₀) D₂ q₂ h₀₂ (w x₀))) :
    IsDetLineCoherentWithinAt (fun x ↦ (g x).comp (f x)) u s x₀ := by
  -- In the composite of the two kernel charts, `u x` is read as a constant sign times the product
  -- of the readings of `v x` and `w x`.
  have hread (x : X) (hx : x ∈ s) (h₁ : (((f x).coprod D₁).prod q₁).IsInvertible)
      (h₂ : (((g x).coprod D₂).prod q₂).IsInvertible) :
      detLineChartEquiv ((g x).comp (f x)) (((g x).comp D₁).coprod D₂) (compKerCoord (f x) D₁ q₁ q₂)
          (h₁.prod_coprod_compKerCoord h₂) (u x) =
        (-1 : ℝ) ^ (finrank ℝ Λ₁ * (finrank ℝ G₂ + finrank ℝ Λ₂)) •
          detLineTensorDualProdEquiv ℝ G₁ Λ₁ G₂ Λ₂
            (detLineChartEquiv (f x) D₁ q₁ h₁ (v x) ⊗ₜ
              detLineChartEquiv (g x) D₂ q₂ h₂ (w x)) := by
    have := (hFf x hx).finite_ker
    have := (hFf x hx).finite_coker
    have := (hFg x hx).finite_ker
    have := (hFg x hx).finite_coker
    exact (congrArg _ (hu x hx)).trans (detLineChartEquiv_neg_one_pow_smul_comp h₁ h₂ (v x) (w x))
  have hne₁ := (LinearEquiv.map_ne_zero_iff (detLineChartEquiv (f x₀) D₁ q₁ h₀₁)).2 (hv x₀ hx₀)
  have hne₂ := (LinearEquiv.map_ne_zero_iff (detLineChartEquiv (g x₀) D₂ q₂ h₀₂)).2 (hw x₀ hx₀)
  -- The composite chart moves with `f x` and `g x`; compare it with the chart frozen at `x₀`.
  have hT : ContinuousWithinAt (fun x ↦ (g x).comp (f x)) s x₀ := (hg x₀ hx₀).clm_comp (hf x₀ hx₀)
  have hmov := eventually_detLineChartEquiv_eq_smul (T := fun x ↦ (g x).comp (f x))
    (D₂ := fun x ↦ ((g x).comp D₁).coprod D₂) (q := fun x ↦ compKerCoord (f x) D₁ q₁ q₂) hT
    (((hg x₀ hx₀).clm_comp continuousWithinAt_const).continuousLinearMapCoprod
      continuousWithinAt_const) (continuousWithinAt_compKerCoord (hf x₀ hx₀))
    (h₀₁.prod_coprod_compKerCoord h₀₂)
  refine isDetLineCoherentWithinAt_of_eventually_sameRay (T := fun x ↦ (g x).comp (f x)) (v := u)
    hT ((hFg x₀ hx₀).comp (hFf x₀ hx₀)) ?_ (Λ := Λ₁ × Λ₂) (G := G₁ × G₂)
    (D₂ := ((g x₀).comp D₁).coprod D₂) (q := compKerCoord (f x₀) D₁ q₁ q₂)
    (h₀₁.prod_coprod_compKerCoord h₀₂) ?_
  · intro h0
    have hr := hread x₀ hx₀ h₀₁ h₀₂
    rw [h0, LinearEquiv.map_zero] at hr
    exact smul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero))
      ((LinearEquiv.map_ne_zero_iff _).2 (tmul_ne_zero hne₁ hne₂)) hr.symm
  · filter_upwards [hev₁, hev₂, hmov, self_mem_nhdsWithin] with x ⟨h₁, hx₁⟩ ⟨h₂, hx₂⟩
      ⟨_, h', c, hc, hcy⟩ hxs
    refine ⟨h', ?_⟩
    have hfrozen : detLineChartEquiv ((g x).comp (f x)) (((g x₀).comp D₁).coprod D₂)
        (compKerCoord (f x₀) D₁ q₁ q₂) h' (u x) = c⁻¹ •
          detLineChartEquiv ((g x).comp (f x)) (((g x).comp D₁).coprod D₂)
            (compKerCoord (f x) D₁ q₁ q₂) (h₁.prod_coprod_compKerCoord h₂) (u x) := by
      rw [hcy, smul_smul, inv_mul_cancel₀ hc.ne', one_smul]
    rw [hfrozen, hread x hxs h₁ h₂, hread x₀ hx₀ h₀₁ h₀₂]
    exact ((hx₁.tmul hx₂).map ((-1 : ℝ) ^ (finrank ℝ Λ₁ * (finrank ℝ G₂ + finrank ℝ Λ₂)) •
      (detLineTensorDualProdEquiv ℝ G₁ Λ₁ G₂ Λ₂).toLinearMap)).pos_smul_left (inv_pos.2 hc)

omit [CompleteSpace F] in
/-- **The composition of coherent families is coherent.** Let `v` and `w` be coherent families of
elements of the determinant lines of continuous families `f` and `g` of Fredholm operators on `s`,
composable as `g x ∘ f x`. Then the family `u` of their composites under the composition law,
normalized by the sign `(-1) ^ (dim coker f x * r x + t x * dim coker g x)`,

`u x = (-1) ^ (dim coker f x * r x + t x * dim coker g x) •
  (detLineCompEquiv (f x) (g x)).symm (v x ⊗ w x)`,

is coherent for the family `g x ∘ f x` on `s`. Here `r x` and `t x` are the ranks of the maps
`ker (g x ∘ f x) → ker (g x)` and `coker (f x) → coker (g x ∘ f x)` of the kernel–cokernel sequence
of the composite; the sign is needed because these dimensions jump along the family. The composite
of two kernel charts is a kernel chart
(`ContinuousLinearMap.IsInvertible.prod_coprod_compKerCoord`), which reads `u x` as the product of
the readings of `v x` and `w x` times a sign depending only on the charts
(`ContinuousLinearMap.detLineChartEquiv_neg_one_pow_smul_comp`). So the composition law carries
continuous orientations of `f` and `g` to a continuous orientation of `g ∘ f`. -/
theorem IsDetLineCoherentOn.clm_comp (hf : ContinuousOn f s) (hg : ContinuousOn g s)
    (hFf : ∀ x ∈ s, IsFredholm (f x)) (hFg : ∀ x ∈ s, IsFredholm (g x))
    (hv : IsDetLineCoherentOn f v s) (hw : IsDetLineCoherentOn g w s)
    (hu : ∀ x ∈ s, ∀ [FiniteDimensional ℝ (f x).ker] [FiniteDimensional ℝ (F ⧸ (f x).range)]
      [FiniteDimensional ℝ (g x).ker] [FiniteDimensional ℝ (P ⧸ (g x).range)],
      u x = (-1 : ℝ) ^ (finrank ℝ (F ⧸ (f x).range) *
          finrank ℝ (LinearMap.range ((f x : E →ₗ[ℝ] F).kerCompToKer (g x : F →ₗ[ℝ] P))) +
        finrank ℝ (LinearMap.range ((f x : E →ₗ[ℝ] F).cokerToCokerComp (g x : F →ₗ[ℝ] P))) *
          finrank ℝ (P ⧸ (g x).range)) •
        ((f x : E →ₗ[ℝ] F).detLineCompEquiv (g x : F →ₗ[ℝ] P)).symm (v x ⊗ₜ w x)) :
    IsDetLineCoherentOn (fun x ↦ (g x).comp (f x)) u s := by
  refine isDetLineCoherentOn_iff.2 fun x₀ hx₀ ↦ ?_
  obtain ⟨-, S₁, _, G₁, _, q₁, h₀₁, hev₁⟩ :=
    isDetLineCoherentWithinAt_iff.1 (isDetLineCoherentOn_iff.1 hv x₀ hx₀)
  obtain ⟨-, S₂, _, G₂, _, q₂, h₀₂, hev₂⟩ :=
    isDetLineCoherentWithinAt_iff.1 (isDetLineCoherentOn_iff.1 hw x₀ hx₀)
  exact isDetLineCoherentWithinAt_clm_comp hx₀ hf hg hFf hFg (fun _ hx ↦ hv.ne_zero hx)
    (fun _ hx ↦ hw.ne_zero hx) hu h₀₁ h₀₂ hev₁ hev₂

section Transport

variable {f : ℝ → E →L[ℝ] F} {g : ℝ → F →L[ℝ] P} {a b : ℝ}

/-- **Orientation transport commutes with the composition law.** Along paths `f` and `g` of
operators which are continuous and Fredholm between `a` and `b`, let the orientations of `v₀` and
`w₀` be transported to those of `v₁` and `w₁`. Then along the composite path `g ∘ f` the
orientation of the composite of `v₀` and `w₀` under the composition law is transported to that of
the composite of `v₁` and `w₁`, each normalized by the sign
`(-1) ^ (dim coker f t * r t + t' t * dim coker g t)` of `TauCeti.IsDetLineCoherentOn.clm_comp` at
its endpoint, where `r t` and `t' t` are the ranks of `ker (g t ∘ f t) → ker (g t)` and
`coker (f t) → coker (g t ∘ f t)`. -/
theorem detLineOrientationTransport_clm_comp (hf : ContinuousOn f (uIcc a b))
    (hg : ContinuousOn g (uIcc a b)) (hFf : ∀ t ∈ uIcc a b, IsFredholm (f t))
    (hFg : ∀ t ∈ uIcc a b, IsFredholm (g t)) [FiniteDimensional ℝ (f a).ker]
    [FiniteDimensional ℝ (F ⧸ (f a).range)] [FiniteDimensional ℝ (g a).ker]
    [FiniteDimensional ℝ (P ⧸ (g a).range)] [FiniteDimensional ℝ (f b).ker]
    [FiniteDimensional ℝ (F ⧸ (f b).range)] [FiniteDimensional ℝ (g b).ker]
    [FiniteDimensional ℝ (P ⧸ (g b).range)] {v₀ : (f a : E →ₗ[ℝ] F).detLine}
    {w₀ : (g a : F →ₗ[ℝ] P).detLine} {v₁ : (f b : E →ₗ[ℝ] F).detLine}
    {w₁ : (g b : F →ₗ[ℝ] P).detLine} (hv₀ : v₀ ≠ 0) (hw₀ : w₀ ≠ 0) (hv₁ : v₁ ≠ 0) (hw₁ : w₁ ≠ 0)
    (htr : detLineOrientationTransport a b hf hFf (rayOfNeZero ℝ v₀ hv₀) = rayOfNeZero ℝ v₁ hv₁)
    (htr' : detLineOrientationTransport a b hg hFg (rayOfNeZero ℝ w₀ hw₀) =
      rayOfNeZero ℝ w₁ hw₁) :
    detLineOrientationTransport (T := fun t ↦ (g t).comp (f t)) a b (hg.clm_comp hf)
        (fun t ht ↦ (hFg t ht).comp (hFf t ht))
        (rayOfNeZero ℝ ((-1 : ℝ) ^ (finrank ℝ (F ⧸ (f a).range) *
            finrank ℝ (LinearMap.range ((f a : E →ₗ[ℝ] F).kerCompToKer (g a : F →ₗ[ℝ] P))) +
          finrank ℝ (LinearMap.range ((f a : E →ₗ[ℝ] F).cokerToCokerComp (g a : F →ₗ[ℝ] P))) *
            finrank ℝ (P ⧸ (g a).range)) •
          ((f a : E →ₗ[ℝ] F).detLineCompEquiv (g a : F →ₗ[ℝ] P)).symm (v₀ ⊗ₜ w₀) :
            ((g a).comp (f a) : E →ₗ[ℝ] P).detLine)
          (smul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero))
            ((LinearEquiv.map_ne_zero_iff _).2 (TauCeti.tmul_ne_zero hv₀ hw₀)))) =
      rayOfNeZero ℝ ((-1 : ℝ) ^ (finrank ℝ (F ⧸ (f b).range) *
            finrank ℝ (LinearMap.range ((f b : E →ₗ[ℝ] F).kerCompToKer (g b : F →ₗ[ℝ] P))) +
          finrank ℝ (LinearMap.range ((f b : E →ₗ[ℝ] F).cokerToCokerComp (g b : F →ₗ[ℝ] P))) *
            finrank ℝ (P ⧸ (g b).range)) •
          ((f b : E →ₗ[ℝ] F).detLineCompEquiv (g b : F →ₗ[ℝ] P)).symm (v₁ ⊗ₜ w₁) :
            ((g b).comp (f b) : E →ₗ[ℝ] P).detLine)
        (smul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero))
          ((LinearEquiv.map_ne_zero_iff _).2 (TauCeti.tmul_ne_zero hv₁ hw₁))) := by
  classical
  -- Coherent families through `v₀` and `w₀` end on the rays of `v₁` and `w₁`.
  obtain ⟨V, rfl, hV⟩ := exists_isDetLineCoherentOn_Icc hf hFf left_mem_uIcc hv₀
  obtain ⟨W, rfl, hW⟩ := exists_isDetLineCoherentOn_Icc hg hFg left_mem_uIcc hw₀
  have hb := (ray_eq_iff _ _).1 ((detLineOrientationTransport_rayOfNeZero hf hFf hV).symm.trans htr)
  have hb' := (ray_eq_iff _ _).1
    ((detLineOrientationTransport_rayOfNeZero hg hFg hW).symm.trans htr')
  -- Their normalized composites form a coherent family for `g ∘ f`.
  let U (t : ℝ) : ((g t).comp (f t) : E →ₗ[ℝ] P).detLine :=
    if ht : t ∈ uIcc a b then
      have := (hFf t ht).finite_ker
      have := (hFf t ht).finite_coker
      have := (hFg t ht).finite_ker
      have := (hFg t ht).finite_coker
      (-1 : ℝ) ^ (finrank ℝ (F ⧸ (f t).range) *
          finrank ℝ (LinearMap.range ((f t : E →ₗ[ℝ] F).kerCompToKer (g t : F →ₗ[ℝ] P))) +
        finrank ℝ (LinearMap.range ((f t : E →ₗ[ℝ] F).cokerToCokerComp (g t : F →ₗ[ℝ] P))) *
          finrank ℝ (P ⧸ (g t).range)) •
        ((f t : E →ₗ[ℝ] F).detLineCompEquiv (g t : F →ₗ[ℝ] P)).symm (V t ⊗ₜ W t)
    else 0
  have hU : IsDetLineCoherentOn (fun t ↦ (g t).comp (f t)) U (uIcc a b) :=
    IsDetLineCoherentOn.clm_comp hf hg hFf hFg hV hW fun t ht _ _ _ _ ↦ dite_eq_left ht
  have hUa : U a = _ := dite_eq_left left_mem_uIcc
  have hUb : U b = _ := dite_eq_left right_mem_uIcc
  refine (congrArg (detLineOrientationTransport a b _ _) ?_).trans
    ((detLineOrientationTransport_rayOfNeZero (hg.clm_comp hf)
      (fun t ht ↦ (hFg t ht).comp (hFf t ht)) hU).trans ?_)
  · refine (ray_eq_iff _ _).2 ?_
    rw [hUa]
    exact SameRay.rfl
  · refine (ray_eq_iff _ _).2 ?_
    rw [hUb]
    exact (hb.tmul hb').map
      ((-1 : ℝ) ^ (finrank ℝ (F ⧸ (f b).range) *
          finrank ℝ (LinearMap.range ((f b : E →ₗ[ℝ] F).kerCompToKer (g b : F →ₗ[ℝ] P))) +
        finrank ℝ (LinearMap.range ((f b : E →ₗ[ℝ] F).cokerToCokerComp (g b : F →ₗ[ℝ] P))) *
          finrank ℝ (P ⧸ (g b).range)) •
        ((f b : E →ₗ[ℝ] F).detLineCompEquiv (g b : F →ₗ[ℝ] P)).symm.toLinearMap)

end Transport

end Coherent

end TauCeti
