/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.SymmetricPower.BasepointIntersection.Connected
public import TauCeti.Geometry.Manifold.SymmetricPower.BasepointIntersection.Order
import Mathlib.Data.ENat.BigOperators
import TauCeti.Topology.Sym.Cons

/-!
# The intersection number of a curve with the basepoint divisor

For a complex curve `α`, a point `z` of `α`, a curve `f : ℂ → Sym α n` and a parameter domain
`U ⊆ ℂ`, the *basepoint intersection number* `TauCeti.basepointIntersectionNumber z f U` is the
sum, over the parameters `w ∈ U`, of the local intersection orders
`TauCeti.basepointIntersectionOrder z f w` of `f` with the basepoint divisor
`V_z = Sym.basepointDivisor z`. Only parameters with `f w ∈ V_z` contribute.

For a holomorphic disk `u` in `Sym^g(Σ)` and a basepoint `z` of a Heegaard diagram, this is the
analytic count behind the multiplicity `n_z(u)` of Ozsváth--Szabó: the number of intersections of
`u` with `V_z`, each counted with its positive local order. This file proves the properties of the
count that do not involve the homotopy class of `u`:

* **Finiteness.** Let `U` be a bounded connected open set and `f` continuous on its closure, with
  analytic chart coordinates at its intersections with `V_z` in `U`, and sending the frontier of
  `U` off `V_z`, as the boundary condition on `T_α ∪ T_β` does for a basepoint off the attaching
  curves. Then `f` meets `V_z` at only finitely many parameters of `U`, and the intersection
  number is finite.
* **Positivity.** When the intersections are finite and `f` has analytic chart coordinates at
  each of them, every intersection contributes at least one, so the number of intersection points
  is at most the intersection number, which vanishes exactly when `f` misses `V_z` on `U`.
* **Reparametrization.** The intersection number is unchanged by an injective holomorphic change
  of parameter with nonzero derivative, in particular by a translation of the parameter domain.

Identifying this count with the topological intersection number of the homotopy class of `u` with
`V_z` is not formalized here.

## Main declarations

* `TauCeti.basepointIntersectionNumber`: the sum of the local intersection orders over `U`.
* `TauCeti.basepointIntersectionNumber_eq_sum`: with finitely many intersections, it is the finite
  sum of the orders at the intersections.
* `TauCeti.basepointIntersectionNumber_ne_top_of_frontier`: finiteness for a curve on a bounded
  connected domain whose frontier is mapped off `V_z`, from the finiteness of its intersections
  there (`TauCeti.finite_basepointDivisor_intersections_of_frontier`).
* `TauCeti.encard_le_basepointIntersectionNumber` and
  `TauCeti.basepointIntersectionNumber_eq_zero_iff`: positivity.
* `TauCeti.basepointIntersectionNumber_comp`: invariance under holomorphic reparametrization.

## References

* P. Ozsváth and Z. Szabó, *Holomorphic disks and topological invariants for closed
  three-manifolds*, Ann. of Math. **159** (2004),
  [arXiv:math/0101206](https://arxiv.org/abs/math/0101206), Sections 2 and 3 (the multiplicity
  `n_z` and its positivity for holomorphic disks).
-/

public section

open Filter Set
open scoped Topology

namespace TauCeti

variable {α : Type*} [TopologicalSpace α] [T2Space α] [ChartedSpace ℂ α] {n : ℕ}
  {z : α} {f : ℂ → Sym α n} {U W : Set ℂ} {w : ℂ}

/-- The **basepoint intersection number** of a curve `f : ℂ → Sym α n` on a parameter set `U`:
the sum over `w ∈ U` of the intersection orders of `f` with the basepoint divisor `V_z` at `w`.
Only intersections contribute. It is meaningful when `f` meets `V_z` at finitely many parameters
of `U` (`TauCeti.basepointIntersectionNumber_eq_sum`); with infinitely many, the `finsum`
convention makes it `0`. For a holomorphic disk with boundary off `V_z` it is the count of
Ozsváth--Szabó's multiplicity `n_z`. -/
noncomputable def basepointIntersectionNumber (z : α) (f : ℂ → Sym α n) (U : Set ℂ) : ℕ∞ :=
  ∑ᶠ w ∈ U, basepointIntersectionOrder z f w

/-- The basepoint intersection number is the `finsum` of the intersection orders over `U`. -/
theorem basepointIntersectionNumber_def (z : α) (f : ℂ → Sym α n) (U : Set ℂ) :
    basepointIntersectionNumber z f U = ∑ᶠ w ∈ U, basepointIntersectionOrder z f w := by
  rfl

/-- The basepoint intersection number on the empty parameter set is zero. -/
@[simp]
theorem basepointIntersectionNumber_empty (z : α) (f : ℂ → Sym α n) :
    basepointIntersectionNumber z f ∅ = 0 := by
  rw [basepointIntersectionNumber_def, finsum_mem_empty]

/-- The basepoint intersection number on a single parameter is the intersection order there. -/
@[simp]
theorem basepointIntersectionNumber_singleton (z : α) (f : ℂ → Sym α n) (w : ℂ) :
    basepointIntersectionNumber z f {w} = basepointIntersectionOrder z f w := by
  rw [basepointIntersectionNumber_def, finsum_mem_singleton]

/-- The intersection order with the basepoint divisor is supported on the intersections. -/
theorem support_basepointIntersectionOrder_subset :
    Function.support (basepointIntersectionOrder z f) ⊆ f ⁻¹' Sym.basepointDivisor z :=
  fun _ hw => by_contra fun h => hw (basepointIntersectionOrder_eq_zero_of_notMem h)

/-- With finitely many intersections in `U`, the basepoint intersection number is the finite sum
of the intersection orders at the intersections. -/
theorem basepointIntersectionNumber_eq_sum
    (hfin : (U ∩ f ⁻¹' Sym.basepointDivisor z).Finite) :
    basepointIntersectionNumber z f U =
      ∑ w ∈ hfin.toFinset, basepointIntersectionOrder z f w := by
  refine finsum_mem_eq_sum_of_subset _ ?_ ?_ <;> rw [hfin.coe_toFinset]
  · exact inter_subset_inter_right U support_basepointIntersectionOrder_subset
  · exact inter_subset_left

/-- A curve missing the basepoint divisor on `U` has intersection number zero on `U`. -/
theorem basepointIntersectionNumber_eq_zero_of_forall_notMem
    (h : ∀ w ∈ U, f w ∉ Sym.basepointDivisor z) : basepointIntersectionNumber z f U = 0 :=
  finsum_mem_eq_zero_of_forall_eq_zero fun w hw =>
    basepointIntersectionOrder_eq_zero_of_notMem (h w hw)

/-- With finitely many intersections in `U`, each intersection order at a parameter of `U` is at
most the basepoint intersection number. -/
theorem basepointIntersectionOrder_le_basepointIntersectionNumber
    (hfin : (U ∩ f ⁻¹' Sym.basepointDivisor z).Finite) (hw : w ∈ U) :
    basepointIntersectionOrder z f w ≤ basepointIntersectionNumber z f U := by
  by_cases hwD : f w ∈ Sym.basepointDivisor z
  · rw [basepointIntersectionNumber_eq_sum hfin]
    exact Finset.single_le_sum (fun _ _ => zero_le) (hfin.mem_toFinset.2 ⟨hw, hwD⟩)
  · simp [basepointIntersectionOrder_eq_zero_of_notMem hwD]

/-- **Positivity of the intersection number.** If a curve meets the basepoint divisor at finitely
many parameters of `U`, with analytic chart coordinates at each of them, then the number of these
parameters is at most the basepoint intersection number on `U`: each intersection counts at least
once. -/
theorem encard_le_basepointIntersectionNumber
    (hfin : (U ∩ f ⁻¹' Sym.basepointDivisor z).Finite)
    (ha : ∀ w ∈ U, f w ∈ Sym.basepointDivisor z →
      AnalyticAt ℂ (fun t => symChartAt (K := ℂ) (f w) (f t)) w) :
    (U ∩ f ⁻¹' Sym.basepointDivisor z).encard ≤ basepointIntersectionNumber z f U := by
  rw [basepointIntersectionNumber_eq_sum hfin, hfin.encard_eq_coe_toFinset_card,
    Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
  refine Finset.sum_le_sum fun w hw => ?_
  obtain ⟨hwU, hwD⟩ := hfin.mem_toFinset.1 hw
  exact Order.one_le_iff_ne_zero.2 fun h0 =>
    (basepointIntersectionOrder_eq_zero_iff (ha w hwU hwD)).1 h0 hwD

/-- **Positivity of the intersection number.** If a curve meets the basepoint divisor at finitely
many parameters of `U`, with analytic chart coordinates at each of them, then its basepoint
intersection number on `U` vanishes exactly when it misses the divisor on `U`. -/
theorem basepointIntersectionNumber_eq_zero_iff
    (hfin : (U ∩ f ⁻¹' Sym.basepointDivisor z).Finite)
    (ha : ∀ w ∈ U, f w ∈ Sym.basepointDivisor z →
      AnalyticAt ℂ (fun t => symChartAt (K := ℂ) (f w) (f t)) w) :
    basepointIntersectionNumber z f U = 0 ↔ ∀ w ∈ U, f w ∉ Sym.basepointDivisor z := by
  refine ⟨fun h w hw hwD => ?_, basepointIntersectionNumber_eq_zero_of_forall_notMem⟩
  have hle := encard_le_basepointIntersectionNumber hfin ha
  rw [h, nonpos_iff_eq_zero, encard_eq_zero] at hle
  exact hle.subset ⟨hw, hwD⟩

/-- With finitely many intersections in `U`, each of finite order, the basepoint intersection
number on `U` is finite. -/
theorem basepointIntersectionNumber_ne_top
    (hfin : (U ∩ f ⁻¹' Sym.basepointDivisor z).Finite)
    (htop : ∀ w ∈ U, basepointIntersectionOrder z f w ≠ ⊤) :
    basepointIntersectionNumber z f U ≠ ⊤ := by
  rw [basepointIntersectionNumber_eq_sum hfin]
  exact ENat.sum_ne_top.2 fun w hw => htop w (hfin.mem_toFinset.1 hw).1

/-- The basepoint intersection number is additive over disjoint parameter sets, each meeting the
divisor at finitely many parameters. -/
theorem basepointIntersectionNumber_union (hUW : Disjoint U W)
    (hU : (U ∩ f ⁻¹' Sym.basepointDivisor z).Finite)
    (hW : (W ∩ f ⁻¹' Sym.basepointDivisor z).Finite) :
    basepointIntersectionNumber z f (U ∪ W) =
      basepointIntersectionNumber z f U + basepointIntersectionNumber z f W :=
  finsum_mem_union' hUW
    (hU.subset (inter_subset_inter_right U support_basepointIntersectionOrder_subset))
    (hW.subset (inter_subset_inter_right W support_basepointIntersectionOrder_subset))

/-- **Invariance under holomorphic reparametrization.** If `g` is injective on `W`, analytic with
nonzero derivative at every parameter of `W`, then `f ∘ g` has the same basepoint intersection
number on `W` as `f` has on `g '' W`. -/
theorem basepointIntersectionNumber_comp {g : ℂ → ℂ} (hinj : InjOn g W)
    (hg : ∀ w ∈ W, AnalyticAt ℂ g w) (hg' : ∀ w ∈ W, deriv g w ≠ 0) :
    basepointIntersectionNumber z (f ∘ g) W = basepointIntersectionNumber z f (g '' W) := by
  rw [basepointIntersectionNumber, basepointIntersectionNumber, finsum_mem_image hinj]
  exact finsum_mem_congr rfl fun w hw => basepointIntersectionOrder_comp (hg w hw) (hg' w hw)

/-- Translating the parameter does not change the basepoint intersection number. -/
theorem basepointIntersectionNumber_comp_add_const (c : ℂ) :
    basepointIntersectionNumber z (fun t => f (t + c)) ((· + c) ⁻¹' U) =
      basepointIntersectionNumber z f U := by
  have h := basepointIntersectionNumber_comp (z := z) (f := f) (W := (· + c) ⁻¹' U)
    (add_left_injective c).injOn (fun _ _ => analyticAt_id.add analyticAt_const)
    (fun w _ => by simp)
  rw [image_preimage_eq U (add_right_surjective c)] at h
  exact h

/-- **Finiteness of the intersection number on a bounded domain.** Let `U ⊆ ℂ` be a bounded
connected open set and `f` continuous on its closure, with analytic chart coordinates at each
parameter of `U` sent into the basepoint divisor. If `f` sends the frontier of `U` off the
divisor, then its basepoint intersection number on `U` is finite. -/
theorem basepointIntersectionNumber_ne_top_of_frontier (hUo : IsOpen U)
    (hU : IsPreconnected U) (hUc : IsCompact (closure U)) (hf : ContinuousOn f (closure U))
    (ha : ∀ w ∈ U, f w ∈ Sym.basepointDivisor z →
      AnalyticAt ℂ (fun t => symChartAt (K := ℂ) (f w) (f t)) w)
    (hfr : ∀ w ∈ frontier U, f w ∉ Sym.basepointDivisor z) :
    basepointIntersectionNumber z f U ≠ ⊤ :=
  basepointIntersectionNumber_ne_top
    (finite_basepointDivisor_intersections_of_frontier z hUo hU hUc hf ha hfr) fun w hw =>
      basepointIntersectionOrder_ne_top_of_isPreconnected hU
        (fun _ hw => hf.continuousAt (mem_of_superset (hUo.mem_nhds hw) subset_closure)) ha
        (exists_mem_notMem_basepointDivisor_of_frontier ⟨w, hw⟩ hUc hf hfr) hw

end TauCeti
