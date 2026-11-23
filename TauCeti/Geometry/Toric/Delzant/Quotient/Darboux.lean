/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Toric.Delzant.Quotient.Symplectic
public import TauCeti.Geometry.Toric.Delzant.Quotient.Vertex

import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Analysis.Calculus.FDeriv.WithLp
import Mathlib.Analysis.SpecialFunctions.Sqrt
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Injective
import TauCeti.Geometry.Manifold.LocalDiffeomorph.MFDeriv
import TauCeti.Geometry.Manifold.LocalDiffeomorph.OpenSubset
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# Darboux charts of the Delzant quotient at its vertices

Let `i : N →+ V` be an integral lattice, `(u, c)` the facet presentation of a Delzant polytope `Δ`
and `M_Δ = Z / N_Δ` its Delzant quotient (`TauCeti.Toric.DelzantQuotient i u c`), a smooth manifold
(`TauCeti.Toric.IsDelzant.isManifold_delzantQuotient`) with the reduced symplectic form `ω_Δ`
(`TauCeti.Toric.IsDelzant.delzantQuotientSymplecticForm`). At a smooth vertex `v` of the
presentation, with set `A` of active facets, the vertex chart
(`TauCeti.Toric.DelzantQuotient.vertexChart`) is an equivariant homeomorphism from an open subset of
`M_Δ` onto an open subset `W` of `ℂ^A`, in which the moment map is the translated weight model
`v + Σ_k ½ |w_k|² ε_k` and the residual torus acts by the standard rotations. This file shows that
it is a **Darboux chart**: a smooth partial diffeomorphism pulling the standard symplectic form
`Σ_k dq_k ∧ dp_k` of `ℂ^A` back to `ω_Δ`.

* **The lift.** On `W` the inverse chart is `w ↦ [vertexLift w]`, where `vertexLift w ∈ Z` has
  coordinates `w_k` in `A` and the nonnegative real coordinates `√(2(⟨y, u_j⟩ - c_j))` outside `A`,
  for `y = v + Σ_k ½ |w_k|² ε_k`. On `W` these radicands are positive, so the lift is smooth
  (`TauCeti.Toric.DelzantQuotient.contDiffAt_vertexLift`). Its coordinates outside `A` are real,
  so their momenta vanish identically and they contribute nothing to `Σ_j dq_j ∧ dp_j`: the lift is
  symplectic from `ℂ^A` to `ℂ^ι`
  (`TauCeti.Toric.DelzantQuotient.stdSymplecticForm_fderiv_vertexLift`).
* **The inverse chart.** Composing the lift, as a smooth map into the level `Z`, with the smooth
  projection `Z → M_Δ` shows that the inverse chart is smooth on `W`
  (`TauCeti.Toric.IsDelzant.contMDiffOn_vertexChart_symm`). Since the projection pulls `ω_Δ` back
  to the restriction of the standard form of `ℂ^ι` to `Z`, the inverse chart pulls `ω_Δ` back to
  the standard form of `ℂ^A`
  (`TauCeti.Toric.IsDelzant.eval₂_delzantQuotientSymplecticForm_mfderiv_vertexChart_symm`).
* **The chart.** Hence the differential of the inverse chart is injective. As `ℂ^A` and `M_Δ` both
  have dimension `2 dim V`, the inverse function theorem makes the inverse chart a local
  diffeomorphism on `W`, and being injective there, its inverse, the vertex chart, is smooth
  (`TauCeti.Toric.IsDelzant.contMDiffOn_vertexChart`). The chart is therefore a partial
  diffeomorphism (`TauCeti.Toric.IsDelzant.vertexDarbouxChart`) pulling the standard form back to
  `ω_Δ` (`TauCeti.Toric.IsDelzant.eval₂_delzantQuotientSymplecticForm_eq_vertexDarbouxChart`).

Every point of `M_Δ` lies in the source of the chart at some vertex
(`TauCeti.Toric.IsDelzant.exists_mem_vertexChart_source`, in
`TauCeti.Geometry.Toric.Delzant.Quotient.Vertex`). So the Delzant quotient is covered by
equivariant Darboux charts in which the moment map is the translated weight model: these are the
local vertex models of a symplectic toric manifold.

## Main definitions

* `TauCeti.Toric.IsDelzant.vertexDarbouxChart`: the vertex chart as a smooth partial
  diffeomorphism.

## Main results

* `TauCeti.Toric.DelzantQuotient.contDiffAt_vertexLift`,
  `TauCeti.Toric.DelzantQuotient.stdSymplecticForm_fderiv_vertexLift`: the lift of the inverse
  chart into `ℂ^ι` is smooth and symplectic on the target.
* `TauCeti.Toric.IsDelzant.contMDiffOn_vertexChart_symm`,
  `TauCeti.Toric.IsDelzant.contMDiffOn_vertexChart`: the vertex chart and its inverse are smooth.
* `TauCeti.Toric.IsDelzant.eval₂_delzantQuotientSymplecticForm_mfderiv_vertexChart_symm`,
  `TauCeti.Toric.IsDelzant.eval₂_delzantQuotientSymplecticForm_eq_vertexDarbouxChart`: the vertex
  chart identifies `ω_Δ` with the standard symplectic form of `ℂ^A`.

## References

* T. Delzant, *Hamiltoniens périodiques et images convexes de l'application moment*,
  Bull. Soc. Math. France 116 (1988), 315–339.
* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Section 29.
* V. Guillemin, *Moment Maps and Combinatorial Invariants of Hamiltonian `T^n`-spaces*,
  Birkhäuser, 1994, Chapter 1.
-/

public section

noncomputable section

open Module Set Real
open scoped Manifold ContDiff

namespace TauCeti.Toric

variable {ι N V : Type*} [Fintype ι] [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {u : ι → N} {c : ι → ℝ} [FiniteDimensional ℝ V] {v : StrongDual ℝ V}

namespace DelzantQuotient

variable (hv : IsSmoothVertex i u c v) (hi : IsIntegralLattice i)
  (hvP : v ∈ facetPolyhedron i u c) [Fintype (activeSet (facetPairing i u) c v)]

/-! ### The lift of the inverse chart -/

/-- **The lift of the inverse vertex chart is smooth.** On the target of the vertex chart the
coordinates of `vertexLift w` outside the active facets are square roots of positive smooth
functions of `w`, and its other coordinates are coordinates of `w`. -/
theorem contDiffAt_vertexLift {n : WithTop ℕ∞}
    {w : EuclideanSpace ℝ (activeSet (facetPairing i u) c v) ×
      EuclideanSpace ℝ (activeSet (facetPairing i u) c v)}
    (hw : w ∈ (vertexChart hv hi hvP).target) :
    ContDiffAt ℝ n (vertexLift hv hi) w := by
  have hw' := (mem_vertexChart_target_iff hv hi hvP).1 hw
  refine ContDiffAt.prodMk (contDiffAt_piLp' 2 fun j ↦ ?_) (contDiffAt_piLp' 2 fun j ↦ ?_)
  · by_cases hj : j ∈ activeSet (facetPairing i u) c v
    · simp only [vertexLift_fst_of_mem hv hi _ hj]
      fun_prop
    · simp only [vertexLift_fst_of_notMem hv hi _ hj]
      refine ContDiffAt.sqrt (by fun_prop) ?_
      linarith [hw' j hj]
  · by_cases hj : j ∈ activeSet (facetPairing i u) c v
    · simp only [vertexLift_snd_of_mem hv hi _ hj]
      fun_prop
    · simp only [vertexLift_snd_of_notMem hv hi _ hj]
      exact contDiffAt_const

/-- The derivative of a coordinate of the lift of the inverse vertex chart, read off from an
explicit formula for that coordinate. -/
private theorem fderiv_vertexLift_apply_eq
    {w : EuclideanSpace ℝ (activeSet (facetPairing i u) c v) ×
      EuclideanSpace ℝ (activeSet (facetPairing i u) c v)}
    (hw : w ∈ (vertexChart hv hi hvP).target)
    (L : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι →L[ℝ] ℝ)
    {f : EuclideanSpace ℝ (activeSet (facetPairing i u) c v) ×
      EuclideanSpace ℝ (activeSet (facetPairing i u) c v) → ℝ}
    {f' : (EuclideanSpace ℝ (activeSet (facetPairing i u) c v) ×
      EuclideanSpace ℝ (activeSet (facetPairing i u) c v)) →L[ℝ] ℝ}
    (hf : L ∘ vertexLift hv hi = f) (hf' : HasFDerivAt f f' w)
    (a : EuclideanSpace ℝ (activeSet (facetPairing i u) c v) ×
      EuclideanSpace ℝ (activeSet (facetPairing i u) c v)) :
    L (fderiv ℝ (vertexLift hv hi) w a) = f' a := by
  have hd : DifferentiableAt ℝ (vertexLift hv hi) w :=
    (contDiffAt_vertexLift hv hi hvP hw (n := 1)).differentiableAt one_ne_zero
  have h := L.hasFDerivAt.comp w hd.hasFDerivAt
  rw [hf] at h
  exact congrArg (· a) (h.unique hf')

/-- The coordinates in the active facets of the derivative of the lift are those of the tangent
vector, and its momentum coordinates outside the active facets vanish. -/
private theorem fderiv_vertexLift_apply
    {w : EuclideanSpace ℝ (activeSet (facetPairing i u) c v) ×
      EuclideanSpace ℝ (activeSet (facetPairing i u) c v)}
    (hw : w ∈ (vertexChart hv hi hvP).target)
    (a : EuclideanSpace ℝ (activeSet (facetPairing i u) c v) ×
      EuclideanSpace ℝ (activeSet (facetPairing i u) c v)) :
    (∀ j (hj : j ∈ activeSet (facetPairing i u) c v),
      (fderiv ℝ (vertexLift hv hi) w a).1 j = a.1 ⟨j, hj⟩ ∧
        (fderiv ℝ (vertexLift hv hi) w a).2 j = a.2 ⟨j, hj⟩) ∧
      ∀ j ∉ activeSet (facetPairing i u) c v, (fderiv ℝ (vertexLift hv hi) w a).2 j = 0 := by
  refine ⟨fun j hj ↦ ⟨?_, ?_⟩, fun j hj ↦ ?_⟩
  · exact fderiv_vertexLift_apply_eq hv hi hvP hw
      ((PiLp.proj 2 (fun _ ↦ ℝ) j).comp (ContinuousLinearMap.fst ℝ _ _))
      (funext fun w ↦ vertexLift_fst_of_mem hv hi w hj)
      (f' := (PiLp.proj 2 (fun _ ↦ ℝ) (⟨j, hj⟩ : activeSet (facetPairing i u) c v)).comp
        (ContinuousLinearMap.fst ℝ _ _))
      ((PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 w.1 _).comp w (hasFDerivAt_fst (p := w))) a
  · exact fderiv_vertexLift_apply_eq hv hi hvP hw
      ((PiLp.proj 2 (fun _ ↦ ℝ) j).comp (ContinuousLinearMap.snd ℝ _ _))
      (funext fun w ↦ vertexLift_snd_of_mem hv hi w hj)
      (f' := (PiLp.proj 2 (fun _ ↦ ℝ) (⟨j, hj⟩ : activeSet (facetPairing i u) c v)).comp
        (ContinuousLinearMap.snd ℝ _ _))
      ((PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 w.2 _).comp w (hasFDerivAt_snd (p := w))) a
  · exact fderiv_vertexLift_apply_eq hv hi hvP hw
      ((PiLp.proj 2 (fun _ ↦ ℝ) j).comp (ContinuousLinearMap.snd ℝ _ _))
      (funext fun w ↦ vertexLift_snd_of_notMem hv hi w hj) (hasFDerivAt_const 0 w) a

/-- **The lift of the inverse vertex chart is symplectic.** Its differential on the target of the
vertex chart pulls the standard symplectic form of `ℂ^ι` back to that of `ℂ^A`: the coordinates
outside the active facets of the lift are real, so they contribute nothing. -/
theorem stdSymplecticForm_fderiv_vertexLift
    {w : EuclideanSpace ℝ (activeSet (facetPairing i u) c v) ×
      EuclideanSpace ℝ (activeSet (facetPairing i u) c v)}
    (hw : w ∈ (vertexChart hv hi hvP).target)
    (a b : EuclideanSpace ℝ (activeSet (facetPairing i u) c v) ×
      EuclideanSpace ℝ (activeSet (facetPairing i u) c v)) :
    stdSymplecticForm (fderiv ℝ (vertexLift hv hi) w a) (fderiv ℝ (vertexLift hv hi) w b) =
      stdSymplecticForm a b := by
  classical
  obtain ⟨ha, ha'⟩ := fderiv_vertexLift_apply hv hi hvP hw a
  obtain ⟨hb, hb'⟩ := fderiv_vertexLift_apply hv hi hvP hw b
  simp only [stdSymplecticForm_apply, PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  -- Coordinates outside the active facets contribute nothing.
  have hsplit (f : ι → ℝ) (hf : ∀ j ∉ activeSet (facetPairing i u) c v, f j = 0) :
      ∑ j, f j = ∑ j : activeSet (facetPairing i u) c v, f j := by
    rw [← Fintype.sum_subtype_add_sum_subtype (· ∈ activeSet (facetPairing i u) c v) f,
      Finset.sum_eq_zero fun (j : {j // j ∉ activeSet (facetPairing i u) c v}) _ ↦ hf j j.property,
      add_zero]
    -- The two sums over the active facets differ only in their `Fintype` instances.
    convert rfl
  rw [hsplit _ fun j hj ↦ by rw [hb' j hj, zero_mul],
    hsplit _ fun j hj ↦ by rw [ha' j hj, mul_zero]]
  refine congrArg₂ (· - ·) (Finset.sum_congr rfl fun j _ ↦ ?_) (Finset.sum_congr rfl fun j _ ↦ ?_)
  · rw [(ha j j.property).1, (hb j j.property).2]
  · rw [(ha j j.property).2, (hb j j.property).1]

/-- The target of the vertex chart, as an open subset of `ℂ^A`. -/
private def vertexChartTargetOpens : TopologicalSpace.Opens
    (EuclideanSpace ℝ (activeSet (facetPairing i u) c v) ×
      EuclideanSpace ℝ (activeSet (facetPairing i u) c v)) :=
  ⟨_, (vertexChart hv hi hvP).open_target⟩

/-- The lift of the inverse vertex chart is smooth on the open target of the chart. -/
private theorem contMDiff_vertexLift_subtypeVal :
    ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (activeSet (facetPairing i u) c v) ×
        EuclideanSpace ℝ (activeSet (facetPairing i u) c v))
      𝓘(ℝ, EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) ∞
      (fun w : vertexChartTargetOpens hv hi hvP ↦ vertexLift hv hi w) :=
  fun w ↦ contMDiffAt_subtype_iff.2 (contDiffAt_vertexLift hv hi hvP w.property).contMDiffAt

/-- On the target of the vertex chart, the lift lies in the level `Z`. -/
private theorem vertexLift_mem_delzantLevel_of_mem_target (w : vertexChartTargetOpens hv hi hvP) :
    vertexLift hv hi w ∈ delzantLevel i u c :=
  vertexLift_mem_delzantLevel hv hi fun j hj ↦
    ((mem_vertexChart_target_iff hv hi hvP).1 w.property j hj).le

/-- The inverse vertex chart on its target, as a map on the open subset of `ℂ^A`: the class of the
point `vertexLift w` of the level. -/
private theorem vertexChart_symm_comp_subtypeVal_eq :
    (vertexChart hv hi hvP).symm ∘ (Subtype.val : vertexChartTargetOpens hv hi hvP → _) =
      DelzantQuotient.mk ∘ fun w : vertexChartTargetOpens hv hi hvP ↦
        (⟨vertexLift hv hi w, vertexLift_mem_delzantLevel_of_mem_target hv hi hvP w⟩ :
          delzantLevel i u c) :=
  funext fun w ↦ vertexChart_symm_apply hv hi hvP w.property

end DelzantQuotient

/-! ### The vertex charts are Darboux charts -/

namespace IsDelzant

open DelzantQuotient

variable (hΔ : IsDelzant i u c) (hi : IsIntegralLattice i) (hv : IsSmoothVertex i u c v)
  (hvP : v ∈ facetPolyhedron i u c) [Fintype (activeSet (facetPairing i u) c v)]

/-- **The inverse vertex chart is smooth.** On its target it is the class of the smooth lift
`vertexLift w` into the level `Z`, followed by the smooth projection `Z → M_Δ`. -/
theorem contMDiffOn_vertexChart_symm :
    letI := hΔ.delzantQuotientChartedSpace hi
    ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (activeSet (facetPairing i u) c v) ×
        EuclideanSpace ℝ (activeSet (facetPairing i u) c v))
      𝓘(ℝ, ProperSMul.QuotientModelSpace (kernelTorusLieAlgebra i u)
        (Fin (Fintype.card ι + finrank ℝ V) → ℝ)) ∞
      (vertexChart hv hi hvP).symm (vertexChart hv hi hvP).target := by
  let _ := hΔ.delzantLevelChartedSpace hi
  let _ := hΔ.delzantQuotientChartedSpace hi
  intro w hw
  have hΦ := (hΔ.isSubmersion_delzantQuotientMk hi).contMDiff.comp
    (hΔ.contMDiff_codRestrict_delzantLevel hi (contMDiff_vertexLift_subtypeVal hv hi hvP)
      (vertexLift_mem_delzantLevel_of_mem_target hv hi hvP))
  rw [← vertexChart_symm_comp_subtypeVal_eq] at hΦ
  exact (contMDiffAt_subtype_iff (x := ⟨w, hw⟩)).1 (hΦ _) |>.contMDiffWithinAt

/-- **The inverse vertex chart pulls the symplectic form of the Delzant quotient back to the
standard symplectic form of `ℂ^A`.** The projection `Z → M_Δ` pulls the symplectic form `ω_Δ` back
to the restriction of the standard form of `ℂ^ι`, and on the target the inverse chart lifts
through the level by `vertexLift`, which is symplectic
(`TauCeti.Toric.DelzantQuotient.stdSymplecticForm_fderiv_vertexLift`). -/
theorem eval₂_delzantQuotientSymplecticForm_mfderiv_vertexChart_symm
    {w : EuclideanSpace ℝ (activeSet (facetPairing i u) c v) ×
      EuclideanSpace ℝ (activeSet (facetPairing i u) c v)}
    (hw : w ∈ (vertexChart hv hi hvP).target)
    (a b : EuclideanSpace ℝ (activeSet (facetPairing i u) c v) ×
      EuclideanSpace ℝ (activeSet (facetPairing i u) c v)) :
    letI := hΔ.delzantQuotientChartedSpace hi
    haveI := hΔ.isManifold_delzantQuotient hi
    (hΔ.delzantQuotientSymplecticForm hi).eval₂ ((vertexChart hv hi hvP).symm w)
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (activeSet (facetPairing i u) c v) ×
          EuclideanSpace ℝ (activeSet (facetPairing i u) c v))
          𝓘(ℝ, ProperSMul.QuotientModelSpace (kernelTorusLieAlgebra i u)
            (Fin (Fintype.card ι + finrank ℝ V) → ℝ)) (vertexChart hv hi hvP).symm w a)
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (activeSet (facetPairing i u) c v) ×
          EuclideanSpace ℝ (activeSet (facetPairing i u) c v))
          𝓘(ℝ, ProperSMul.QuotientModelSpace (kernelTorusLieAlgebra i u)
            (Fin (Fintype.card ι + finrank ℝ V) → ℝ)) (vertexChart hv hi hvP).symm w b) =
      stdSymplecticForm a b := by
  let _ := hΔ.delzantLevelChartedSpace hi
  let _ := hΔ.delzantQuotientChartedSpace hi
  have := hΔ.isManifold_delzantLevel hi ∞
  have := hΔ.isManifold_delzantQuotient hi
  have hℓ := contMDiff_vertexLift_subtypeVal hv hi hvP
  have hmk := (hΔ.isSubmersion_delzantQuotientMk hi).contMDiff
  have hL := hΔ.contMDiff_codRestrict_delzantLevel hi hℓ
    (vertexLift_mem_delzantLevel_of_mem_target hv hi hvP)
  -- On `W`, the pullback of `ω_Δ` along the class of the lift is the pullback of the standard form
  -- of `ℂ^ι` along the lift.
  have hpull : SmoothForm.mpullback _ (hmk.comp hL) (hΔ.delzantQuotientSymplecticForm hi) =
      SmoothForm.mpullback _ hℓ stdSymplecticForm.constSmooth := by
    rw [← SmoothForm.mpullback_mpullback _ _ hL hmk,
      hΔ.mpullback_delzantQuotientMk_delzantQuotientSymplecticForm hi]
    -- The inclusion of the level after the codomain restriction of the lift is the lift.
    rw [SmoothForm.mpullback_mpullback_of_comp_eq hL (hΔ.contMDiff_coe_delzantLevel hi) hℓ
      contMDiff_id (funext fun _ ↦ rfl), SmoothForm.mpullback_id, LinearMap.id_apply]
  -- Both sides are read through the differential of the inclusion of `W`, which is surjective.
  set x : vertexChartTargetOpens hv hi hvP := ⟨w, hw⟩
  obtain ⟨a₀, rfl⟩ := (bijective_mfderiv_subtype_val (I := 𝓘(ℝ,
    EuclideanSpace ℝ (activeSet (facetPairing i u) c v) ×
      EuclideanSpace ℝ (activeSet (facetPairing i u) c v))) x).2 a
  obtain ⟨b₀, rfl⟩ := (bijective_mfderiv_subtype_val (I := 𝓘(ℝ,
    EuclideanSpace ℝ (activeSet (facetPairing i u) c v) ×
      EuclideanSpace ℝ (activeSet (facetPairing i u) c v))) x).2 b
  have hval := (contMDiff_subtypeVal (n := 1) (I := 𝓘(ℝ,
    EuclideanSpace ℝ (activeSet (facetPairing i u) c v) ×
      EuclideanSpace ℝ (activeSet (facetPairing i u) c v)))
    (U := vertexChartTargetOpens hv hi hvP) x).mdifferentiableAt one_ne_zero
  have hsymm := ((hΔ.contMDiffOn_vertexChart_symm hi hv hvP).contMDiffAt
    ((vertexChart hv hi hvP).open_target.mem_nhds hw)).mdifferentiableAt (by simp)
  have hlift := (contDiffAt_vertexLift hv hi hvP hw (n := 1)).contMDiffAt.mdifferentiableAt
    one_ne_zero
  have h₁ := SmoothForm.eval₂_mpullback _ (hmk.comp hL) (hΔ.delzantQuotientSymplecticForm hi) x
    a₀ b₀
  rw [hpull, SmoothForm.eval₂_mpullback, SymplecticForm.fromTangentSpace_constSmooth_apply,
    NormedSpace.fromTangentSpace_apply, NormedSpace.fromTangentSpace_apply,
    ← vertexChart_symm_comp_subtypeVal_eq] at h₁
  -- Expose the lift as a composite with the inclusion of `W`, to apply the chain rule.
  change stdSymplecticForm (mfderiv _ _ (vertexLift hv hi ∘ Subtype.val) x a₀)
    (mfderiv _ _ (vertexLift hv hi ∘ Subtype.val) x b₀) = _ at h₁
  rw [mfderiv_comp_apply x hlift hval, mfderiv_comp_apply x hlift hval,
    mfderiv_comp_apply x hsymm hval, mfderiv_comp_apply x hsymm hval] at h₁
  -- The left sides agree up to evaluating `κ.symm ∘ Subtype.val` at `x = ⟨w, hw⟩`.
  convert h₁.symm using 1
  · rfl
  rw [mfderiv_eq_fderiv]
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply]
  exact (stdSymplecticForm_fderiv_vertexLift hv hi hvP hw _ _).symm

omit [Fintype (activeSet (facetPairing i u) c v)] in
include hΔ hi hv in
/-- The source and target model spaces of a vertex chart have the same dimension `2 dim V`: the
active normals at a smooth vertex form a basis of the lattice, of rank `dim V`. -/
private theorem finrank_prod_euclideanSpace_activeSet :
    finrank ℝ (EuclideanSpace ℝ (activeSet (facetPairing i u) c v) ×
        EuclideanSpace ℝ (activeSet (facetPairing i u) c v)) =
      finrank ℝ (ProperSMul.QuotientModelSpace (kernelTorusLieAlgebra i u)
        (Fin (Fintype.card ι + finrank ℝ V) → ℝ)) := by
  have := Fintype.ofFinite (activeSet (facetPairing i u) c v)
  rw [hΔ.finrank_delzantQuotientModelSpace hi, Module.finrank_prod, finrank_euclideanSpace,
    ← two_mul, ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq, hv.ncard_activeSet,
    hi.finrank_eq]

/-- The differential of the inverse vertex chart is injective on the target: it pulls the
symplectic form of the Delzant quotient back to the nondegenerate standard form. -/
private theorem injective_mfderiv_vertexChart_symm
    {w : EuclideanSpace ℝ (activeSet (facetPairing i u) c v) ×
      EuclideanSpace ℝ (activeSet (facetPairing i u) c v)}
    (hw : w ∈ (vertexChart hv hi hvP).target) :
    letI := hΔ.delzantQuotientChartedSpace hi
    Function.Injective (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (activeSet (facetPairing i u) c v) ×
        EuclideanSpace ℝ (activeSet (facetPairing i u) c v))
      𝓘(ℝ, ProperSMul.QuotientModelSpace (kernelTorusLieAlgebra i u)
        (Fin (Fintype.card ι + finrank ℝ V) → ℝ)) (vertexChart hv hi hvP).symm w) := by
  let _ := hΔ.delzantQuotientChartedSpace hi
  have := hΔ.isManifold_delzantQuotient hi
  refine (injective_iff_map_eq_zero _).2 fun a ha ↦ stdSymplecticForm.nondegenerate.1 a fun b ↦ ?_
  have h := hΔ.eval₂_delzantQuotientSymplecticForm_mfderiv_vertexChart_symm hi hv hvP hw a b
  rw [ha, SmoothBundleForm.eval₂_zero_left] at h
  exact h.symm

/-- The inverse vertex chart is a local diffeomorphism at every point of its target, by the
inverse function theorem. -/
private theorem isLocalDiffeomorphOn_vertexChart_symm :
    letI := hΔ.delzantQuotientChartedSpace hi
    IsLocalDiffeomorphOn 𝓘(ℝ, EuclideanSpace ℝ (activeSet (facetPairing i u) c v) ×
        EuclideanSpace ℝ (activeSet (facetPairing i u) c v))
      𝓘(ℝ, ProperSMul.QuotientModelSpace (kernelTorusLieAlgebra i u)
        (Fin (Fintype.card ι + finrank ℝ V) → ℝ)) ∞
      (vertexChart hv hi hvP).symm (vertexChart hv hi hvP).target := by
  let _ := hΔ.delzantQuotientChartedSpace hi
  have := hΔ.isManifold_delzantQuotient hi
  exact fun w ↦ isLocalDiffeomorphAt_of_injective_mfderiv
    (hΔ.contMDiffOn_vertexChart_symm hi hv hvP) (vertexChart hv hi hvP).open_target w.property
    BoundarylessManifold.isInteriorPoint (by simp)
    (hΔ.injective_mfderiv_vertexChart_symm hi hv hvP w.property)
    (finrank_prod_euclideanSpace_activeSet hΔ hi hv)

/-- **The vertex chart is smooth.** The inverse chart is an injective local diffeomorphism on the
target, so its inverse, the vertex chart, is smooth on the source. -/
theorem contMDiffOn_vertexChart :
    letI := hΔ.delzantQuotientChartedSpace hi
    ContMDiffOn 𝓘(ℝ, ProperSMul.QuotientModelSpace (kernelTorusLieAlgebra i u)
        (Fin (Fintype.card ι + finrank ℝ V) → ℝ))
      𝓘(ℝ, EuclideanSpace ℝ (activeSet (facetPairing i u) c v) ×
        EuclideanSpace ℝ (activeSet (facetPairing i u) c v)) ∞
      (vertexChart hv hi hvP) (vertexChart hv hi hvP).source := by
  let _ := hΔ.delzantQuotientChartedSpace hi
  have h := (hΔ.isLocalDiffeomorphOn_vertexChart_symm hi hv hvP).contMDiffOn_invFunOn
    (vertexChart hv hi hvP).open_target (vertexChart hv hi hvP).symm.injOn
  rw [(vertexChart hv hi hvP).symm_image_target_eq_source] at h
  refine h.congr fun q hq ↦ ?_
  -- On the source, the chart is the inverse of `κ.symm` on the target.
  have := (vertexChart hv hi hvP).symm.injOn.leftInvOn_invFunOn
    ((vertexChart hv hi hvP).map_source hq)
  rwa [(vertexChart hv hi hvP).left_inv hq, eq_comm] at this

/-- **The vertex chart as a Darboux chart.** The equivariant chart of the Delzant quotient at a
smooth vertex `v` (`TauCeti.Toric.DelzantQuotient.vertexChart`) is a smooth partial
diffeomorphism onto an open subset of `ℂ^A`, `A` the set of facets active at `v`, and it pulls the
standard symplectic form of `ℂ^A` back to the symplectic form of the Delzant quotient
(`TauCeti.Toric.IsDelzant.eval₂_delzantQuotientSymplecticForm_eq_vertexDarbouxChart`). -/
def vertexDarbouxChart :
    letI := hΔ.delzantQuotientChartedSpace hi
    PartialDiffeomorph 𝓘(ℝ, ProperSMul.QuotientModelSpace (kernelTorusLieAlgebra i u)
        (Fin (Fintype.card ι + finrank ℝ V) → ℝ))
      𝓘(ℝ, EuclideanSpace ℝ (activeSet (facetPairing i u) c v) ×
        EuclideanSpace ℝ (activeSet (facetPairing i u) c v))
      (DelzantQuotient i u c)
      (EuclideanSpace ℝ (activeSet (facetPairing i u) c v) ×
        EuclideanSpace ℝ (activeSet (facetPairing i u) c v)) ∞ :=
  letI := hΔ.delzantQuotientChartedSpace hi
  { toPartialEquiv := (vertexChart hv hi hvP).toPartialEquiv
    open_source := (vertexChart hv hi hvP).open_source
    open_target := (vertexChart hv hi hvP).open_target
    contMDiffOn_toFun := hΔ.contMDiffOn_vertexChart hi hv hvP
    contMDiffOn_invFun := hΔ.contMDiffOn_vertexChart_symm hi hv hvP }

@[simp]
theorem toOpenPartialHomeomorph_vertexDarbouxChart :
    letI := hΔ.delzantQuotientChartedSpace hi
    (hΔ.vertexDarbouxChart hi hv hvP).toOpenPartialHomeomorph = vertexChart hv hi hvP :=
  (rfl)

@[simp]
theorem coe_vertexDarbouxChart :
    letI := hΔ.delzantQuotientChartedSpace hi
    ⇑(hΔ.vertexDarbouxChart hi hv hvP) = vertexChart hv hi hvP :=
  (rfl)

@[simp]
theorem coe_symm_vertexDarbouxChart :
    letI := hΔ.delzantQuotientChartedSpace hi
    ⇑(hΔ.vertexDarbouxChart hi hv hvP).toPartialEquiv.symm = (vertexChart hv hi hvP).symm :=
  (rfl)

@[simp]
theorem vertexDarbouxChart_source :
    letI := hΔ.delzantQuotientChartedSpace hi
    (hΔ.vertexDarbouxChart hi hv hvP).source = (vertexChart hv hi hvP).source :=
  (rfl)

@[simp]
theorem vertexDarbouxChart_target :
    letI := hΔ.delzantQuotientChartedSpace hi
    (hΔ.vertexDarbouxChart hi hv hvP).target = (vertexChart hv hi hvP).target :=
  (rfl)

/-- **The vertex charts are Darboux charts.** On the source of the chart at a smooth vertex, the
symplectic form of the Delzant quotient is the pullback of the standard symplectic form
`Σ_k dq_k ∧ dp_k` of `ℂ^A` along the chart. -/
theorem eval₂_delzantQuotientSymplecticForm_eq_vertexDarbouxChart {q : DelzantQuotient i u c}
    (hq : q ∈ (vertexChart hv hi hvP).source)
    (a b : letI := hΔ.delzantQuotientChartedSpace hi
      TangentSpace 𝓘(ℝ, ProperSMul.QuotientModelSpace (kernelTorusLieAlgebra i u)
        (Fin (Fintype.card ι + finrank ℝ V) → ℝ)) q) :
    letI := hΔ.delzantQuotientChartedSpace hi
    haveI := hΔ.isManifold_delzantQuotient hi
    (hΔ.delzantQuotientSymplecticForm hi).eval₂ q a b =
      stdSymplecticForm
        (mvfderiv 𝓘(ℝ, ProperSMul.QuotientModelSpace (kernelTorusLieAlgebra i u)
          (Fin (Fintype.card ι + finrank ℝ V) → ℝ)) (hΔ.vertexDarbouxChart hi hv hvP) q a)
        (mvfderiv 𝓘(ℝ, ProperSMul.QuotientModelSpace (kernelTorusLieAlgebra i u)
          (Fin (Fintype.card ι + finrank ℝ V) → ℝ)) (hΔ.vertexDarbouxChart hi hv hvP) q b) := by
  let _ := hΔ.delzantQuotientChartedSpace hi
  have := hΔ.isManifold_delzantQuotient hi
  -- The differential of the inverse chart at `κ q` inverts that of the chart at `q`.
  have hinv (a : TangentSpace 𝓘(ℝ, ProperSMul.QuotientModelSpace (kernelTorusLieAlgebra i u)
      (Fin (Fintype.card ι + finrank ℝ V) → ℝ)) q) :
      mfderiv 𝓘(ℝ, EuclideanSpace ℝ (activeSet (facetPairing i u) c v) ×
        EuclideanSpace ℝ (activeSet (facetPairing i u) c v))
        𝓘(ℝ, ProperSMul.QuotientModelSpace (kernelTorusLieAlgebra i u)
          (Fin (Fintype.card ι + finrank ℝ V) → ℝ))
        (vertexChart hv hi hvP).symm (vertexChart hv hi hvP q)
        (mfderiv 𝓘(ℝ, ProperSMul.QuotientModelSpace (kernelTorusLieAlgebra i u)
          (Fin (Fintype.card ι + finrank ℝ V) → ℝ))
          𝓘(ℝ, EuclideanSpace ℝ (activeSet (facetPairing i u) c v) ×
            EuclideanSpace ℝ (activeSet (facetPairing i u) c v)) (vertexChart hv hi hvP) q a) = a :=
    (hΔ.vertexDarbouxChart hi hv hvP).mfderiv_symm_apply_mfderiv_apply (by simp) hq a
  have h := hΔ.eval₂_delzantQuotientSymplecticForm_mfderiv_vertexChart_symm hi hv hvP
    ((vertexChart hv hi hvP).map_source hq)
    (mfderiv 𝓘(ℝ, ProperSMul.QuotientModelSpace (kernelTorusLieAlgebra i u)
      (Fin (Fintype.card ι + finrank ℝ V) → ℝ))
      𝓘(ℝ, EuclideanSpace ℝ (activeSet (facetPairing i u) c v) ×
        EuclideanSpace ℝ (activeSet (facetPairing i u) c v)) (vertexChart hv hi hvP) q a)
    (mfderiv 𝓘(ℝ, ProperSMul.QuotientModelSpace (kernelTorusLieAlgebra i u)
      (Fin (Fintype.card ι + finrank ℝ V) → ℝ))
      𝓘(ℝ, EuclideanSpace ℝ (activeSet (facetPairing i u) c v) ×
        EuclideanSpace ℝ (activeSet (facetPairing i u) c v)) (vertexChart hv hi hvP) q b)
  rw [hinv, hinv, (vertexChart hv hi hvP).left_inv hq] at h
  rw [mvfderiv_apply_eq_mfderiv_apply, mvfderiv_apply_eq_mfderiv_apply, coe_vertexDarbouxChart]
  exact h

end IsDelzant

end TauCeti.Toric
