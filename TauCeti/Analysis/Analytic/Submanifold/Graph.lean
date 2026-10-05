/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Analytic.Submanifold.Basic
import TauCeti.Data.Fin.Basic
import Mathlib.Topology.Algebra.Module.Equiv.Pi
import Mathlib.Topology.OpenPartialHomeomorph.Constructions
import Mathlib.Topology.Order.OrderClosed

/-!
# Cylinders and graphs of analytic submanifolds

In cylinder coordinates `Fin.cons t x`, adjoining a free scalar coordinate increases the
dimension of an analytic submanifold by one. The graph of a scalar function analytic on the
submanifold has the same dimension as its base. These constructions provide analytic charts
for sections and open sectors between analytic root functions.

The graph construction only requires analyticity on the submanifold: it uses a local extension
in a base chart, rather than requiring the given ambient function to be analytic.

## References

* S. G. Krantz and H. R. Parks, *A Primer of Real Analytic Functions*, second edition,
  Birkhäuser, 2002, Chapter 2.
-/

public section

open Set Filter Topology

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {n d : ℕ}
  {S : Set (Fin n → 𝕜)}

/-- Adjoining a free scalar coordinate to an analytic submanifold increases its dimension by
one. The new coordinate is coordinate zero, as in `Fin.cons`. -/
theorem IsAnalyticSubmanifold.cylinder (hS : IsAnalyticSubmanifold d S) :
    IsAnalyticSubmanifold (d + 1) {v : Fin (n + 1) → 𝕜 | Fin.tail v ∈ S} := by
  let c := (Fin.consEquivL 𝕜 (fun _ : Fin (n + 1) ↦ 𝕜)).toHomeomorph
  refine ⟨?_, Nat.add_le_add_right hS.le 1, ?_⟩
  · obtain ⟨x, hx⟩ := hS.nonempty
    exact ⟨Fin.cons 0 x, by simpa using hx⟩
  · intro v hv
    obtain ⟨e, hve, he⟩ := hS.exists_isAnalyticChart (Fin.tail v) hv
    let q := c.symm.toOpenPartialHomeomorph.trans
      (((OpenPartialHomeomorph.refl 𝕜).prod e).trans c.toOpenPartialHomeomorph)
    refine ⟨q, ?_, ?_⟩
    · simpa [q, c, OpenPartialHomeomorph.trans_source,
        OpenPartialHomeomorph.prod_source] using hve
    refine ⟨?_, ?_, ?_⟩
    · intro w hw
      have hw' : Fin.tail w ∈ e.source := by
        simpa [q, c, OpenPartialHomeomorph.trans_source,
          OpenPartialHomeomorph.prod_source] using hw
      exact ((Fin.consEquivL 𝕜 (fun _ : Fin (n + 1) ↦ 𝕜)).analyticAt _).comp
        (((ContinuousLinearMap.proj 0).analyticAt w).prod
          ((he.analyticOnNhd _ hw').comp
            (analyticAt_snd.comp ((Fin.consEquivL 𝕜 (fun _ : Fin (n + 1) ↦ 𝕜)).symm.analyticAt w))))
    · intro w hw
      have hw' : Fin.tail w ∈ e.target := by
        simpa [q, c, OpenPartialHomeomorph.trans_target,
          OpenPartialHomeomorph.prod_target] using hw
      exact ((Fin.consEquivL 𝕜 (fun _ : Fin (n + 1) ↦ 𝕜)).analyticAt _).comp
        (((ContinuousLinearMap.proj 0).analyticAt w).prod
          ((he.analyticOnNhd_symm _ hw').comp
            (analyticAt_snd.comp ((Fin.consEquivL 𝕜 (fun _ : Fin (n + 1) ↦ 𝕜)).symm.analyticAt w))))
    · intro w hw
      have hw' : Fin.tail w ∈ e.source := by
        simpa [q, c, OpenPartialHomeomorph.trans_source,
          OpenPartialHomeomorph.prod_source] using hw
      -- Unfold the local product chart to express its straightening property in coordinates.
      change (∀ i : Fin (n + 1), d + 1 ≤ i.val →
        (Fin.cons (w 0) (e (Fin.tail w)) : Fin (n + 1) → 𝕜) i = 0) ↔ Fin.tail w ∈ S
      rw [he.mem_iff hw']
      constructor
      · intro h j hj
        exact h j.succ (by simpa using hj)
      · intro h i hi
        obtain ⟨j, rfl⟩ := Fin.eq_succ_of_ne_zero (i := i) (by intro hz; simp [hz] at hi)
        exact h j (by simpa using hi)

-- The triangular change of coordinates used to straighten a graph over a base chart.
private theorem exists_graph_straightening
    (e : OpenPartialHomeomorph (Fin n → 𝕜) (Fin n → 𝕜)) (he : IsAnalyticChart d S e)
    (g : (Fin n → 𝕜) → 𝕜) (hg : AnalyticOnNhd 𝕜 g e.source) :
    ∃ q : OpenPartialHomeomorph (Fin (n + 1) → 𝕜) (Fin (n + 1) → 𝕜),
      q.source = Fin.tail ⁻¹' e.source ∧
      (∀ w, q w = Fin.cons (w 0 - g (Fin.tail w)) (e (Fin.tail w))) ∧
      AnalyticOnNhd 𝕜 q q.source ∧ AnalyticOnNhd 𝕜 q.symm q.target := by
  let c := Fin.consEquivL 𝕜 (fun _ : Fin (n + 1) ↦ 𝕜)
  have ht (w : Fin (n + 1) → 𝕜) : AnalyticAt 𝕜 Fin.tail w :=
    analyticAt_snd.comp (c.symm.analyticAt w)
  have htail : Continuous (Fin.tail : (Fin (n + 1) → 𝕜) → Fin n → 𝕜) :=
    continuous_id.finTail
  have hzero : Continuous (fun w : Fin (n + 1) → 𝕜 ↦ w 0) := continuous_apply 0
  let q : OpenPartialHomeomorph (Fin (n + 1) → 𝕜) (Fin (n + 1) → 𝕜) :=
    { toFun := fun w ↦ Fin.cons (w 0 - g (Fin.tail w)) (e (Fin.tail w))
      invFun := fun w ↦ Fin.cons (w 0 + g (e.symm (Fin.tail w))) (e.symm (Fin.tail w))
      source := Fin.tail ⁻¹' e.source
      target := Fin.tail ⁻¹' e.target
      map_source' := fun w hw ↦ by simpa using e.map_source hw
      map_target' := fun w hw ↦ by simpa using e.map_target hw
      left_inv' := fun w hw ↦ by simp [e.left_inv hw]
      right_inv' := fun w hw ↦ by simp [e.right_inv hw]
      open_source := e.open_source.preimage htail
      open_target := e.open_target.preimage htail
      continuousOn_toFun := by
        exact (hzero.continuousOn.sub
          (hg.continuousOn.comp htail.continuousOn fun _ hw ↦ hw)).finCons
          (e.continuousOn.comp htail.continuousOn fun _ hw ↦ hw)
      continuousOn_invFun := by
        exact (hzero.continuousOn.add
          (hg.continuousOn.comp
            (e.continuousOn_symm.comp htail.continuousOn fun _ hw ↦ hw)
            fun _ hw ↦ e.map_target hw)).finCons
          (e.continuousOn_symm.comp htail.continuousOn fun _ hw ↦ hw) }
  have hq : AnalyticOnNhd 𝕜 q q.source := by
    intro w hw
    exact (c.analyticAt _).comp
      ((((ContinuousLinearMap.proj 0).analyticAt w).sub ((hg _ hw).comp (ht w))).prod
        ((he.analyticOnNhd _ hw).comp (ht w)))
  have hq' : AnalyticOnNhd 𝕜 q.symm q.target := by
    intro w hw
    have ht' := (he.analyticOnNhd_symm _ hw).comp (ht w)
    exact (c.analyticAt _).comp
      ((((ContinuousLinearMap.proj 0).analyticAt w).add
        ((hg _ (e.map_target hw)).comp_of_eq ht' rfl)).prod ht')
  exact ⟨q, rfl, fun _ ↦ rfl, hq, hq'⟩

/-- The graph of a scalar function analytic on a submanifold is an analytic submanifold of the
same dimension. Only the values of the function on the base matter. -/
theorem IsAnalyticSubmanifold.graph (hS : IsAnalyticSubmanifold d S)
    {f : (Fin n → 𝕜) → 𝕜} (hf : AnalyticOnSubmanifold d f S) :
    IsAnalyticSubmanifold d {v : Fin (n + 1) → 𝕜 | Fin.tail v ∈ S ∧ v 0 = f (Fin.tail v)} := by
  refine ⟨?_, hS.le.trans (Nat.le_succ n), ?_⟩
  · obtain ⟨x, hx⟩ := hS.nonempty
    exact ⟨Fin.cons (f x) x, by simpa using hx⟩
  intro v hv
  have hd : d ≤ n := hS.le
  -- Extend the intrinsic analytic function in a base chart and restrict that chart.
  obtain ⟨U, hU, hxU, g, hg, hfg⟩ := hf.exists_analyticOnNhd_eqOn hS.le hv.1
  obtain ⟨e₀, hx₀, he₀⟩ := hS.exists_isAnalyticChart (Fin.tail v) hv.1
  let e := e₀.restrOpen U hU
  have he := he₀.restrOpen hU
  have hxe : Fin.tail v ∈ e.source := ⟨hx₀, hxU⟩
  have hg' : AnalyticOnNhd 𝕜 g e.source := hg.mono inter_subset_right
  obtain ⟨q, hsource, hformula, hq, hq'⟩ := exists_graph_straightening e he g hg'
  -- Move the constrained scalar coordinate after the `d` free base coordinates.
  let p := (ContinuousLinearEquiv.piCongrLeft 𝕜 (fun _ : Fin (n + 1) ↦ 𝕜)
    (Equiv.swap 0 (⟨d, by omega⟩ : Fin (n + 1)))).symm
  let r := q.trans p.toHomeomorph.toOpenPartialHomeomorph
  refine ⟨r, ?_, ?_, ?_, ?_⟩
  · simpa [r, OpenPartialHomeomorph.trans_source, hsource] using hxe
  · intro w hw
    exact (p.analyticAt _).comp (hq _ hw.1)
  · intro w hw
    exact (hq' _ hw.2).comp (p.symm.analyticAt w)
  · intro w hw
    have hw' : Fin.tail w ∈ e.source := by
      have hwq : w ∈ q.source := hw.1
      simpa only [hsource, mem_preimage] using hwq
    -- The permutation's inverse acts by precomposition; unfold it to read the coordinates.
    change (∀ i : Fin (n + 1), d ≤ i.val →
      q w (Equiv.swap 0 ⟨d, by omega⟩ i) = 0) ↔ _
    rw [hformula, forall_cons_swap_eq_zero_iff hS.le, sub_eq_zero, ← he.mem_iff hw']
    have hfg' (hx : Fin.tail w ∈ S) : f (Fin.tail w) = g (Fin.tail w) :=
      hfg ⟨hx, hw'.2⟩
    constructor
    · rintro ⟨h, hx⟩
      exact ⟨hx, h.trans (hfg' hx).symm⟩
    · rintro ⟨hx, h⟩
      exact ⟨h.trans (hfg' hx), hx⟩

/-- The nonempty sector below a continuous real function is an analytic submanifold of dimension
one more than its base. -/
theorem IsAnalyticSubmanifold.below {S : Set (Fin n → ℝ)} (hS : IsAnalyticSubmanifold d S)
    {f : (Fin n → ℝ) → ℝ} (hf : ContinuousOn f S) :
    IsAnalyticSubmanifold (d + 1)
      {v : Fin (n + 1) → ℝ | Fin.tail v ∈ S ∧ v 0 < f (Fin.tail v)} := by
  have hne : {v : Fin (n + 1) → ℝ | Fin.tail v ∈ S ∧ v 0 < f (Fin.tail v)}.Nonempty := by
    obtain ⟨x, hx⟩ := hS.nonempty
    exact ⟨Fin.cons (f x - 1) x, by simp [hx]⟩
  refine hS.cylinder.of_isOpen_preimage_val (fun _ hv ↦ hv.1) ?_ hne
  have hf' : Continuous (fun v : {v : Fin (n + 1) → ℝ | Fin.tail v ∈ S} ↦
      f (Fin.tail v.val)) :=
    hf.comp_continuous continuous_subtype_val.finTail (fun v ↦ v.property)
  have ht : Continuous (fun v : {v : Fin (n + 1) → ℝ | Fin.tail v ∈ S} ↦ v.val 0) :=
    (continuous_apply 0).comp continuous_subtype_val
  convert isOpen_lt ht hf' using 1
  ext v
  have hv : Fin.tail v.val ∈ S := v.property
  simp [hv]

/-- The nonempty sector above a continuous real function is an analytic submanifold of dimension
one more than its base. -/
theorem IsAnalyticSubmanifold.above {S : Set (Fin n → ℝ)} (hS : IsAnalyticSubmanifold d S)
    {f : (Fin n → ℝ) → ℝ} (hf : ContinuousOn f S) :
    IsAnalyticSubmanifold (d + 1)
      {v : Fin (n + 1) → ℝ | Fin.tail v ∈ S ∧ f (Fin.tail v) < v 0} := by
  have hne : {v : Fin (n + 1) → ℝ | Fin.tail v ∈ S ∧ f (Fin.tail v) < v 0}.Nonempty := by
    obtain ⟨x, hx⟩ := hS.nonempty
    exact ⟨Fin.cons (f x + 1) x, by simp [hx]⟩
  refine hS.cylinder.of_isOpen_preimage_val (fun _ hv ↦ hv.1) ?_ hne
  have hf' : Continuous (fun v : {v : Fin (n + 1) → ℝ | Fin.tail v ∈ S} ↦
      f (Fin.tail v.val)) :=
    hf.comp_continuous continuous_subtype_val.finTail (fun v ↦ v.property)
  have ht : Continuous (fun v : {v : Fin (n + 1) → ℝ | Fin.tail v ∈ S} ↦ v.val 0) :=
    (continuous_apply 0).comp continuous_subtype_val
  convert isOpen_lt hf' ht using 1
  ext v
  have hv : Fin.tail v.val ∈ S := v.property
  simp [hv]

/-- The nonempty open sector between two continuous real functions is an analytic submanifold
of dimension one more than its base. -/
theorem IsAnalyticSubmanifold.between {S : Set (Fin n → ℝ)} (hS : IsAnalyticSubmanifold d S)
    {f g : (Fin n → ℝ) → ℝ} (hf : ContinuousOn f S) (hg : ContinuousOn g S)
    (hne : {v : Fin (n + 1) → ℝ |
      Fin.tail v ∈ S ∧ f (Fin.tail v) < v 0 ∧ v 0 < g (Fin.tail v)}.Nonempty) :
    IsAnalyticSubmanifold (d + 1)
      {v : Fin (n + 1) → ℝ | Fin.tail v ∈ S ∧ f (Fin.tail v) < v 0 ∧ v 0 < g (Fin.tail v)} := by
  refine hS.cylinder.of_isOpen_preimage_val (fun _ hv ↦ hv.1) ?_ hne
  have hf' : Continuous (fun v : {v : Fin (n + 1) → ℝ | Fin.tail v ∈ S} ↦
      f (Fin.tail v.val)) :=
    hf.comp_continuous continuous_subtype_val.finTail (fun v ↦ v.property)
  have hg' : Continuous (fun v : {v : Fin (n + 1) → ℝ | Fin.tail v ∈ S} ↦
      g (Fin.tail v.val)) :=
    hg.comp_continuous continuous_subtype_val.finTail (fun v ↦ v.property)
  have ht : Continuous (fun v : {v : Fin (n + 1) → ℝ | Fin.tail v ∈ S} ↦ v.val 0) :=
    (continuous_apply 0).comp continuous_subtype_val
  convert (isOpen_lt hf' ht).inter (isOpen_lt ht hg') using 1
  ext v
  have hv : Fin.tail v.val ∈ S := v.property
  simp [hv]

end TauCeti
