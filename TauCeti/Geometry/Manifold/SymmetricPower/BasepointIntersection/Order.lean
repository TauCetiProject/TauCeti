/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Analytic.AffineHyperplane
public import TauCeti.Geometry.Manifold.SymmetricPower.Manifold

/-!
# The intersection order of a curve with the basepoint divisor

For a complex curve `α` and a point `z` of `α`, the basepoint divisor `V_z ⊆ Sym α n` consists of
the unordered tuples containing `z`. In every elementary-symmetric chart that it meets, `V_z` is
an affine hyperplane `ℓ = b` with `ℓ ≠ 0`
(`TauCeti.exists_continuousLinearMap_ne_zero_mem_iff_symChartAt`). The *intersection order* of a
curve `f : ℂ → Sym α n` with `V_z` at a parameter `w`
(`TauCeti.basepointIntersectionOrder`) is the order of vanishing at `w` of `ℓ ∘ C ∘ f - b`, for
the chosen chart `C` at `f w`. It is `0` whenever `f w ∉ V_z`, and exactly then if `C ∘ f` is
analytic at `w`. For `f` continuous at `w`, it is `⊤` exactly when `f` stays in `V_z` near `w`.

For a curve that is holomorphic near `w`, the intersection order is independent of the
coordinates used to compute it: it is the order of vanishing of `H ∘ C ∘ f` for any chosen chart
`C` around `f w` and any analytic local equation `H` of `V_z` in `C` with nonzero differential
(`TauCeti.basepointIntersectionOrder_eq_analyticOrderAt`), in particular for any affine equation
of `V_z` in `C` (`TauCeti.basepointIntersectionOrder_eq_analyticOrderAt_sub`). The order can
therefore be read off in whichever chart is convenient. The input is that two local equations of a
hyperplane meet an analytic curve to the same order
(`AnalyticAt.analyticOrderAt_comp_eq_analyticOrderAt_sub`), applied after the analytic change of
elementary-symmetric coordinates (`TauCeti.analyticAt_symChartAt_symm_trans`).

For a holomorphic disk `u` in `Sym^g(Σ)` and a basepoint `z` of a Heegaard diagram, the
multiplicity `n_z(u)` of Ozsváth--Szabó, *Holomorphic disks and topological invariants for closed
three-manifolds*, Section 2, is the sum of these local orders over the finitely many intersections
of `u` with `V_z` (`TauCeti.finite_basepointDivisor_intersections_of_isPreconnected`), each of
which is positive. That sum is `TauCeti.basepointIntersectionNumber`; identifying it with the
topological intersection number of the homotopy class of `u` with `V_z` is not formalized.

## Main declarations

* `TauCeti.basepointIntersectionOrder`: the intersection order of a curve with `V_z` at `w`.
* `TauCeti.basepointIntersectionOrder_eq_analyticOrderAt`: it may be computed with any analytic
  local equation of `V_z`, with nonzero differential, in any chosen elementary-symmetric chart.
* `TauCeti.basepointIntersectionOrder_eq_analyticOrderAt_sub`: the special case of an affine
  equation of `V_z` in such a chart.
* `TauCeti.basepointIntersectionOrder_eq_zero_iff` and
  `TauCeti.basepointIntersectionOrder_eq_top_iff`: for a curve analytic in the chosen chart at
  `f w`, the order vanishes exactly off `V_z`; for a curve continuous at `w`, it is infinite
  exactly when the curve lies in `V_z` near `w`.
* `TauCeti.basepointIntersectionOrder_comp`: the order is unchanged by a holomorphic
  reparametrization with nonzero derivative.
-/

public section

open Filter
open scoped Manifold Topology

namespace TauCeti

variable {α : Type*} [TopologicalSpace α] [T2Space α] [ChartedSpace ℂ α] {n : ℕ}
  {z : α} {f : ℂ → Sym α n} {w : ℂ}

open Classical in
/-- The **intersection order** of a curve `f : ℂ → Sym α n` with the basepoint divisor `V_z` at a
parameter `w`: the order of vanishing at `w` of `t ↦ ℓ (C (f t)) - b`, where `C` is the chosen
elementary-symmetric chart at `f w` and `ℓ = b`, with `ℓ ≠ 0`, is an affine equation of `V_z` in
`C`. It is `0` when `f w ∉ V_z`. For a curve holomorphic near `w` it does not depend on the chart
or on the local equation (`TauCeti.basepointIntersectionOrder_eq_analyticOrderAt`). -/
noncomputable def basepointIntersectionOrder (z : α) (f : ℂ → Sym α n) (w : ℂ) : ℕ∞ :=
  if h : ∃ (ℓ : (Fin n → ℂ) →L[ℂ] ℂ) (b : ℂ), ℓ ≠ 0 ∧
      ∀ s ∈ (symChartAt (K := ℂ) (f w)).source,
        s ∈ Sym.basepointDivisor z ↔ ℓ (symChartAt (K := ℂ) (f w) s) = b then
    analyticOrderAt (fun t => h.choose (symChartAt (K := ℂ) (f w) (f t)) - h.choose_spec.choose) w
  else 0

/-- At a point of the basepoint divisor, the intersection order is the order of an affine equation
of the divisor in the chosen chart at that point. -/
private theorem exists_basepointIntersectionOrder_eq (hz : f w ∈ Sym.basepointDivisor z) :
    ∃ (ℓ : (Fin n → ℂ) →L[ℂ] ℂ) (b : ℂ), ℓ ≠ 0 ∧
      (∀ s ∈ (symChartAt (K := ℂ) (f w)).source,
        s ∈ Sym.basepointDivisor z ↔ ℓ (symChartAt (K := ℂ) (f w) s) = b) ∧
      basepointIntersectionOrder z f w =
        analyticOrderAt (fun t => ℓ (symChartAt (K := ℂ) (f w) (f t)) - b) w := by
  have h := exists_continuousLinearMap_ne_zero_mem_iff_symChartAt (K := ℂ) z (f w)
    ⟨f w, mem_symChartAt_source _, hz⟩
  exact ⟨h.choose, h.choose_spec.choose, h.choose_spec.choose_spec.1,
    h.choose_spec.choose_spec.2, by rw [basepointIntersectionOrder, dite_eq_left h]⟩

/-- The intersection order of a curve with the basepoint divisor vanishes at a parameter where the
curve is off the divisor. -/
@[simp]
theorem basepointIntersectionOrder_eq_zero_of_notMem (hz : f w ∉ Sym.basepointDivisor z) :
    basepointIntersectionOrder z f w = 0 := by
  rw [basepointIntersectionOrder]
  split_ifs with h
  · exact analyticOrderAt_eq_zero.2 <| Or.inr fun h0 =>
      hz ((h.choose_spec.choose_spec.2 _ (mem_symChartAt_source _)).2 (sub_eq_zero.1 h0))
  · rfl

/-- **Positivity of the intersection order.** For a curve whose coordinates in the chosen chart
at `f w` are analytic at `w`, the intersection order with the basepoint divisor vanishes exactly
when `f w` is off the divisor. -/
theorem basepointIntersectionOrder_eq_zero_iff
    (ha : AnalyticAt ℂ (fun t => symChartAt (K := ℂ) (f w) (f t)) w) :
    basepointIntersectionOrder z f w = 0 ↔ f w ∉ Sym.basepointDivisor z := by
  refine ⟨fun h hz => ?_, basepointIntersectionOrder_eq_zero_of_notMem⟩
  obtain ⟨ℓ, b, -, hℓ, hord⟩ := exists_basepointIntersectionOrder_eq hz
  have hg : AnalyticAt ℂ (fun t => ℓ (symChartAt (K := ℂ) (f w) (f t)) - b) w :=
    ((ℓ.analyticAt _).comp ha).sub analyticAt_const
  rw [hord, hg.analyticOrderAt_eq_zero] at h
  exact h (sub_eq_zero.2 ((hℓ _ (mem_symChartAt_source _)).1 hz))

/-- The intersection order of a curve continuous at `w` with the basepoint divisor is infinite
exactly when the curve lies in the divisor near `w`. -/
theorem basepointIntersectionOrder_eq_top_iff (hf : ContinuousAt f w) :
    basepointIntersectionOrder z f w = ⊤ ↔ ∀ᶠ t in 𝓝 w, f t ∈ Sym.basepointDivisor z := by
  by_cases hz : f w ∈ Sym.basepointDivisor z
  · obtain ⟨ℓ, b, -, hℓ, hord⟩ := exists_basepointIntersectionOrder_eq hz
    rw [hord, analyticOrderAt_eq_top]
    refine eventually_congr ?_
    filter_upwards [hf.preimage_mem_nhds
      ((symChartAt (K := ℂ) (f w)).open_source.mem_nhds (mem_symChartAt_source _))] with t ht
    rw [hℓ _ ht, sub_eq_zero]
  · rw [basepointIntersectionOrder_eq_zero_of_notMem hz]
    exact iff_of_false ENat.top_ne_zero.symm fun h => hz h.self_of_nhds

/-- **The intersection order is invariant under holomorphic reparametrization.** If `g` is
analytic at `w` with nonzero derivative there, then `f ∘ g` meets the basepoint divisor at `w` to
the same order as `f` does at `g w`. -/
theorem basepointIntersectionOrder_comp {g : ℂ → ℂ} (hg : AnalyticAt ℂ g w)
    (hg' : deriv g w ≠ 0) :
    basepointIntersectionOrder z (f ∘ g) w = basepointIntersectionOrder z f (g w) := by
  simp only [basepointIntersectionOrder, Function.comp_apply]
  split_ifs with h
  · exact analyticOrderAt_comp_of_deriv_ne_zero (f := fun t =>
      h.choose (symChartAt (K := ℂ) (f (g w)) (f t)) - h.choose_spec.choose) hg hg'
  · rfl

variable [IsManifold 𝓘(ℂ) 1 α]

/-- A function with nonzero differential keeps a nonzero differential after an
elementary-symmetric change of coordinates. -/
private theorem fderiv_comp_symChartAt_symm_trans_ne_zero {s s' x : Sym α n}
    (hs : x ∈ (symChartAt (K := ℂ) s).source) (hs' : x ∈ (symChartAt (K := ℂ) s').source)
    {H : (Fin n → ℂ) → ℂ} (hH : DifferentiableAt ℂ H (symChartAt (K := ℂ) s' x))
    (hH' : fderiv ℂ H (symChartAt (K := ℂ) s' x) ≠ 0) :
    fderiv ℂ (fun c => H (symChartAt (K := ℂ) s' ((symChartAt (K := ℂ) s).symm c)))
      (symChartAt (K := ℂ) s x) ≠ 0 := by
  set C := symChartAt (K := ℂ) s
  set C' := symChartAt (K := ℂ) s'
  have hT := (analyticAt_symChartAt_symm_trans hs hs').differentiableAt
  have hS := (analyticAt_symChartAt_symm_trans hs' hs).differentiableAt
  have hSx : C (C'.symm (C' x)) = C x := by rw [C'.left_inv hs']
  have hTx : C' (C.symm (C x)) = C' x := by rw [C.left_inv hs]
  -- the transition `T = C' ∘ C.symm` has the right inverse `S = C ∘ C'.symm` near `C' x`, so its
  -- differential at `C x` is surjective
  have hTS : (fun c => C' (C.symm (C (C'.symm c)))) =ᶠ[𝓝 (C' x)] id := by
    filter_upwards [C'.open_target.mem_nhds (C'.map_source hs'),
      (C'.tendsto_symm hs').eventually (C.open_source.mem_nhds hs)] with c hc hc'
    rw [id, C.left_inv hc', C'.right_inv hc]
  have hid : (fderiv ℂ (fun c => C' (C.symm c)) (C x)).comp
      (fderiv ℂ (fun c => C (C'.symm c)) (C' x)) = ContinuousLinearMap.id ℂ _ := by
    rw [← hSx, ← fderiv_fun_comp (C' x) (by rwa [hSx]) hS, hTS.fderiv_eq, fderiv_id]
  intro h0
  apply hH'
  rw [fderiv_fun_comp (C x) (by rwa [hTx]) hT, hTx] at h0
  rw [← ContinuousLinearMap.comp_id (fderiv ℂ H (C' x)), ← hid, ← ContinuousLinearMap.comp_assoc,
    h0, ContinuousLinearMap.zero_comp]

/-- **The intersection order is independent of the chart and of the local equation.** Let `f` be
continuous at `w` with `f w` in the basepoint divisor, and let `s` be a tuple whose chosen
elementary-symmetric chart `C` contains `f w` in its source, in which the coordinates of `f` are
analytic at `w`. If `H` is analytic at `C (f w)` with nonzero differential there, and `H ∘ C`
vanishes on the divisor near `f w`, then the intersection order of `f` with the divisor at `w` is
the order of vanishing of `H ∘ C ∘ f` at `w`. -/
theorem basepointIntersectionOrder_eq_analyticOrderAt {s : Sym α n} (hf : ContinuousAt f w)
    (hs : f w ∈ (symChartAt (K := ℂ) s).source)
    (ha : AnalyticAt ℂ (fun t => symChartAt (K := ℂ) s (f t)) w)
    (hz : f w ∈ Sym.basepointDivisor z) {H : (Fin n → ℂ) → ℂ}
    (hH : AnalyticAt ℂ H (symChartAt (K := ℂ) s (f w)))
    (hH' : fderiv ℂ H (symChartAt (K := ℂ) s (f w)) ≠ 0)
    (hHz : ∀ᶠ x in 𝓝 (f w), x ∈ Sym.basepointDivisor z → H (symChartAt (K := ℂ) s x) = 0) :
    basepointIntersectionOrder z f w =
      analyticOrderAt (fun t => H (symChartAt (K := ℂ) s (f t))) w := by
  obtain ⟨ℓ, b, -, hℓ, hord⟩ := exists_basepointIntersectionOrder_eq hz
  set C₀ := symChartAt (K := ℂ) (f w)
  set C := symChartAt (K := ℂ) s
  have h₀ : f w ∈ C₀.source := mem_symChartAt_source _
  -- the equation `H` read in the chart `C₀`: analytic, with nonzero differential, and vanishing
  -- on the hyperplane `ℓ = b` near `C₀ (f w)`
  have hG : AnalyticAt ℂ (fun c => H (C (C₀.symm c))) (C₀ (f w)) :=
    hH.comp_of_eq (analyticAt_symChartAt_symm_trans h₀ hs) (by rw [C₀.left_inv h₀])
  have hG' : fderiv ℂ (fun c => H (C (C₀.symm c))) (C₀ (f w)) ≠ 0 :=
    fderiv_comp_symChartAt_symm_trans_ne_zero h₀ hs hH.differentiableAt hH'
  have hzero : ∀ᶠ c in 𝓝 (C₀ (f w)), ℓ c = b → H (C (C₀.symm c)) = 0 := by
    filter_upwards [C₀.open_target.mem_nhds (C₀.map_source h₀),
      (C₀.tendsto_symm h₀).eventually hHz] with c hc hcz hcb
    exact hcz ((hℓ _ (C₀.map_target hc)).2 (by rwa [C₀.right_inv hc]))
  rw [hord, ← hG.analyticOrderAt_comp_eq_analyticOrderAt_sub hG'
    (analyticAt_symChartAt_comp_of_analyticAt hf hs h₀ ha) ((hℓ _ h₀).1 hz) hzero]
  refine analyticOrderAt_congr ?_
  filter_upwards [hf.preimage_mem_nhds (C₀.open_source.mem_nhds h₀)] with t ht
  rw [C₀.left_inv ht]

/-- **The intersection order may be computed from any affine equation of the divisor.** If `f` is
continuous at `w` and its coordinates in the chosen chart `C` at a tuple `s` are analytic at `w`,
with `f w` in the source of `C`, then for any affine equation `ℓ = b`, `ℓ ≠ 0`, of the basepoint
divisor in `C`, the intersection order of `f` with the divisor at `w` is the order of vanishing of
`t ↦ ℓ (C (f t)) - b` at `w`. -/
theorem basepointIntersectionOrder_eq_analyticOrderAt_sub {s : Sym α n} (hf : ContinuousAt f w)
    (hs : f w ∈ (symChartAt (K := ℂ) s).source)
    (ha : AnalyticAt ℂ (fun t => symChartAt (K := ℂ) s (f t)) w)
    {ℓ : (Fin n → ℂ) →L[ℂ] ℂ} {b : ℂ} (hℓ : ℓ ≠ 0)
    (hℓz : ∀ x ∈ (symChartAt (K := ℂ) s).source,
      x ∈ Sym.basepointDivisor z ↔ ℓ (symChartAt (K := ℂ) s x) = b) :
    basepointIntersectionOrder z f w =
      analyticOrderAt (fun t => ℓ (symChartAt (K := ℂ) s (f t)) - b) w := by
  by_cases hz : f w ∈ Sym.basepointDivisor z
  · refine basepointIntersectionOrder_eq_analyticOrderAt hf hs ha hz (H := fun c => ℓ c - b)
      ((ℓ.analyticAt _).sub analyticAt_const)
      (by rwa [fderiv_sub_const, ContinuousLinearMap.fderiv]) ?_
    filter_upwards [(symChartAt (K := ℂ) s).open_source.mem_nhds hs] with x hx hxz
    exact sub_eq_zero.2 ((hℓz x hx).1 hxz)
  · rw [basepointIntersectionOrder_eq_zero_of_notMem hz, eq_comm, analyticOrderAt_eq_zero]
    exact Or.inr fun h => hz ((hℓz _ hs).2 (sub_eq_zero.1 h))

end TauCeti

end
