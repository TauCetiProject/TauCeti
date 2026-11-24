/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.MetricSpace.CyclicDistanceCut
public import TauCeti.Topology.MetricSpace.DiscreteEnergy.Insertion
import TauCeti.Data.Fin.Basic
import TauCeti.Data.Fin.Tuple.Basic
import TauCeti.Topology.Constructions.Pi

/-!
# Discrete energy of closed metric chains

A closed broken path with `n + 1` breaks in a metric space `X` is recorded by its vertices
`(q₀, …, qₙ)`, read cyclically, together with the time steps `(τ₀, …, τₙ)` of its edges. As in
Abouzaid's distance cut `TauCeti.cyclicDistanceCut`, the edge `i` joins `q (i - 1)` to `q i`, with
`i - 1` computed in `Fin (n + 1)`, so the edge `0` is the closing edge from `qₙ` back to `q₀`. Its
**cyclic discrete energy** (`TauCeti.cyclicDiscreteEnergy`) is

`E(q) = ½ ∑ᵢ dist(q (i - 1), q i)² / τᵢ`.

It is defined on all tuples, before any geodesic interpolation is chosen. When consecutive vertices
are joined by minimizing geodesic segments, each run at constant speed during its step, it is the
energy `½ ∫ |γ'|²` of the resulting closed broken geodesic. This file develops it as the
closed-loop analogue of the fixed-endpoint discrete energy `TauCeti.discreteEnergy`.

* **Cutting open at the base vertex.** The cyclic energy of `q` is the fixed-endpoint energy of the
  chain `(q₀, q₁, …, qₙ, q₀)` at any times whose steps are the cyclic steps, the closing step last
  (`TauCeti.cyclicDiscreteEnergy_eq_discreteEnergy_snoc`). It does not depend on which vertex is
  called the base vertex (`TauCeti.cyclicDiscreteEnergy_rotate`).
* **Estimates.** For positive steps, Cauchy–Schwarz bounds the total edge length by
  `√(2 T E)`, with `T = ∑ τᵢ` the period, so every vertex lies within `√(2 T E)` of `q₀`; each
  edge satisfies `dist(q (i - 1), q i)² ≤ 2 E τᵢ`. So a closed chain of energy at most `c` lies in
  the distance cut with cut-offs `δᵢ` as soon as `2 c τᵢ ≤ δᵢ²`
  (`TauCeti.mem_cyclicDistanceCut_of_cyclicDiscreteEnergy_le`): a fine time mesh forces the
  vertices of an energy sublevel into the domain where short geodesics join consecutive vertices.
* **Energy carriers.** The strict energy sublevels
  (`TauCeti.cyclicDiscreteEnergyStrictSublevel`) are open in `Xⁿ⁺¹`, contain the constant loops for
  a positive cut-off, and their closed sublevels are compact when `X` is compact, or, in a proper
  space, once the base vertex is confined to a closed ball.
* **Subdivision.** Repeating the base vertex, the embedding `ιⁿ` of the distance cuts
  (`TauCeti.cyclicDistanceCutRepeatFirst`), preserves the energy for any step of the new edge of
  length zero (`TauCeti.cyclicDiscreteEnergy_cons_self`), and so maps energy carriers into each
  other by an embedding (`TauCeti.cyclicDiscreteEnergyRepeatFirst`), closed when `X` is Hausdorff
  (`TauCeti.isClosedEmbedding_cyclicDiscreteEnergyRepeatFirst`). Forgetting vertices, with the
  steps of the coarse edges the sums of the fine steps they span, does not increase the energy
  (`TauCeti.cyclicDiscreteEnergy_cyclicDiscreteEnergyForget_le`), the induced maps of carriers
  compose (`TauCeti.cyclicDiscreteEnergyForgetMap_trans`). Conversely, sampling constant-speed
  minimizing segments along the edges inserts vertices without changing the energy
  (`TauCeti.cyclicDiscreteEnergy_cyclicDiscreteEnergyInsert`), so in a geodesic space every
  coarse closed chain is the image of a fine one of the same energy
  (`TauCeti.exists_cyclicDiscreteEnergyForget_eq_and_cyclicDiscreteEnergy_eq`), and a continuous
  choice of segments gives a continuous insertion map of carriers with forgetting as a left
  inverse (`TauCeti.cyclicDiscreteEnergyForgetMap_comp_cyclicDiscreteEnergyInsertMap`).

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton, 1963, §16.
* M. Abouzaid, *Symplectic cohomology and Viterbo's theorem*, in *Free loop spaces in geometry
  and topology*, IRMA Lect. Math. Theor. Phys. 24 (2015), §11.2.
-/

public section

open scoped BigOperators
open Set

namespace TauCeti

variable {X : Type*} [PseudoMetricSpace X] {m n : ℕ}

/-! ### The cyclic discrete energy -/

/-- **The cyclic discrete energy** of a closed chain `(q₀, …, qₙ)` with time steps
`(τ₀, …, τₙ)`: half the sum over the edges `(q (i - 1), q i)`, read cyclically, of the squared
edge length divided by the step `τ i`. The edge `0` is the closing edge from `qₙ` to `q₀`. -/
noncomputable def cyclicDiscreteEnergy (τ : Fin (n + 1) → ℝ) (q : Fin (n + 1) → X) : ℝ :=
  (1 / 2) * ∑ i, dist (q i) (q (i - 1)) ^ 2 / τ i

/-- The defining finite-sum formula for the cyclic discrete energy. -/
theorem cyclicDiscreteEnergy_def (τ : Fin (n + 1) → ℝ) (q : Fin (n + 1) → X) :
    cyclicDiscreteEnergy τ q = (1 / 2) * ∑ i, dist (q i) (q (i - 1)) ^ 2 / τ i := (rfl)

/-- The cyclic discrete energy is continuous in the vertices, for any steps. -/
@[fun_prop]
theorem continuous_cyclicDiscreteEnergy (τ : Fin (n + 1) → ℝ) :
    Continuous (cyclicDiscreteEnergy (X := X) τ) := by
  unfold cyclicDiscreteEnergy
  fun_prop

/-- A constant loop has cyclic energy zero. -/
@[simp]
theorem cyclicDiscreteEnergy_const (τ : Fin (n + 1) → ℝ) (x : X) :
    cyclicDiscreteEnergy τ (fun _ ↦ x) = 0 := by
  simp [cyclicDiscreteEnergy]

/-- Each summand of the cyclic discrete energy is nonnegative for nonnegative steps. -/
theorem cyclicDiscreteEnergy_summand_nonneg {τ : Fin (n + 1) → ℝ} (hτ : 0 ≤ τ)
    (q : Fin (n + 1) → X) (i : Fin (n + 1)) : 0 ≤ dist (q i) (q (i - 1)) ^ 2 / τ i :=
  div_nonneg (sq_nonneg _) (hτ i)

/-- The cyclic discrete energy is nonnegative for nonnegative steps. -/
theorem cyclicDiscreteEnergy_nonneg {τ : Fin (n + 1) → ℝ} (hτ : 0 ≤ τ) (q : Fin (n + 1) → X) :
    0 ≤ cyclicDiscreteEnergy τ q :=
  mul_nonneg (by norm_num) (Finset.sum_nonneg fun i _ ↦ cyclicDiscreteEnergy_summand_nonneg hτ q i)

/-- **The cyclic energy does not depend on the base vertex.** Rotating the vertices and the
steps together, so that the vertex `k` becomes the base vertex, does not change the energy. -/
theorem cyclicDiscreteEnergy_rotate (τ : Fin (n + 1) → ℝ) (q : Fin (n + 1) → X)
    (k : Fin (n + 1)) :
    cyclicDiscreteEnergy (fun i ↦ τ (i + k)) (fun i ↦ q (i + k)) = cyclicDiscreteEnergy τ q := by
  simp only [cyclicDiscreteEnergy_def, sub_add_eq_add_sub]
  congr 1
  exact Equiv.sum_comp (Equiv.addRight k) fun i ↦ dist (q i) (q (i - 1)) ^ 2 / τ i

/-- **Cutting a closed chain open at its base vertex.** The cyclic energy of `(q₀, …, qₙ)` is the
fixed-endpoint discrete energy of the chain `(q₀, q₁, …, qₙ, q₀)` at any times `t` whose steps are
the cyclic steps: the step from the vertex `k` to the vertex `k + 1` of the chain is `τ (k + 1)`,
so the last step, back to `q₀`, is the step `τ 0` of the closing edge. -/
theorem cyclicDiscreteEnergy_eq_discreteEnergy_snoc {τ : Fin (n + 1) → ℝ}
    {t : Fin (n + 2) → ℝ} (ht : ∀ k : Fin (n + 1), t k.succ - t k.castSucc = τ (k + 1))
    (q : Fin (n + 1) → X) :
    cyclicDiscreteEnergy τ q = discreteEnergy t (Fin.snoc q (q 0)) := by
  rw [cyclicDiscreteEnergy_def, discreteEnergy_def, ← Equiv.sum_comp (Equiv.addRight 1)]
  congr 1
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [Equiv.coe_addRight, add_sub_cancel_right, Fin.snoc_castSucc, Fin.snoc_self_zero_succ, ht,
    dist_comm]

/-! ### Estimates -/

section Estimates

variable {τ : Fin (n + 1) → ℝ}

/-- The distance from the base vertex to any vertex of a closed chain is at most its total edge
length. -/
theorem dist_le_sum_dist_sub_one (q : Fin (n + 1) → X) (j : Fin (n + 1)) :
    dist (q 0) (q j) ≤ ∑ i, dist (q i) (q (i - 1)) := by
  refine (dist_le_sum_adjacent_dist q j).trans ?_
  rw [Fin.sum_univ_succ, add_comm]
  refine le_add_of_le_of_nonneg (Finset.sum_le_sum fun i _ ↦ ?_) dist_nonneg
  rw [Fin.succ_sub_one_eq_castSucc, dist_comm]

/-- **The discrete Cauchy–Schwarz inequality for closed chains**, in squared form: the square
of the total edge length is at most twice the period `∑ τᵢ` times the cyclic energy. -/
theorem sq_sum_dist_le_cyclicDiscreteEnergy (hτ : ∀ i, 0 < τ i) (q : Fin (n + 1) → X) :
    (∑ i, dist (q i) (q (i - 1))) ^ 2 ≤ 2 * (∑ i, τ i) * cyclicDiscreteEnergy τ q := by
  have hT : 0 < ∑ i, τ i := Finset.sum_pos (fun i _ ↦ hτ i) Finset.univ_nonempty
  have h := (div_le_iff₀ hT).mp (Finset.sq_sum_div_le_sum_sq_div Finset.univ
    (fun i ↦ dist (q i) (q (i - 1))) fun i _ ↦ hτ i)
  calc _ ≤ _ := h
    _ = _ := by rw [cyclicDiscreteEnergy_def]; ring

/-- The total edge length of a closed chain is at most `√(2 T E)`, with `T = ∑ τᵢ` the period. -/
theorem sum_dist_le_sqrt_cyclicDiscreteEnergy (hτ : ∀ i, 0 < τ i) (q : Fin (n + 1) → X) :
    ∑ i, dist (q i) (q (i - 1)) ≤ √(2 * (∑ i, τ i) * cyclicDiscreteEnergy τ q) :=
  Real.le_sqrt_of_sq_le (sq_sum_dist_le_cyclicDiscreteEnergy hτ q)

/-- Every vertex of a closed chain lies within `√(2 T E)` of the base vertex, with `T = ∑ τᵢ` the
period. -/
theorem dist_le_sqrt_cyclicDiscreteEnergy (hτ : ∀ i, 0 < τ i) (q : Fin (n + 1) → X)
    (j : Fin (n + 1)) :
    dist (q 0) (q j) ≤ √(2 * (∑ i, τ i) * cyclicDiscreteEnergy τ q) :=
  (dist_le_sum_dist_sub_one q j).trans (sum_dist_le_sqrt_cyclicDiscreteEnergy hτ q)

/-- For positive steps in a metric space, a closed chain has cyclic energy zero exactly when it
is a constant loop. -/
@[simp]
theorem cyclicDiscreteEnergy_eq_zero_iff {X : Type*} [MetricSpace X] (hτ : ∀ i, 0 < τ i)
    (q : Fin (n + 1) → X) : cyclicDiscreteEnergy τ q = 0 ↔ ∀ j, q j = q 0 := by
  refine ⟨fun hq j ↦ ?_, fun hq ↦ ?_⟩
  · have h := dist_le_sqrt_cyclicDiscreteEnergy hτ q j
    rw [hq, mul_zero, Real.sqrt_zero] at h
    exact (dist_le_zero.mp h).symm
  · rw [show q = fun _ ↦ q 0 from funext hq, cyclicDiscreteEnergy_const]

/-- Each squared edge length is at most twice the energy times the step of the edge. -/
theorem dist_sq_le_cyclicDiscreteEnergy_mul_step (hτ : 0 ≤ τ) {i : Fin (n + 1)}
    (hi : 0 < τ i) (q : Fin (n + 1) → X) :
    dist (q i) (q (i - 1)) ^ 2 ≤ 2 * cyclicDiscreteEnergy τ q * τ i := by
  have h := (div_le_iff₀ hi).mp (Finset.single_le_sum
    (f := fun j ↦ dist (q j) (q (j - 1)) ^ 2 / τ j)
    (fun j _ ↦ cyclicDiscreteEnergy_summand_nonneg hτ q j) (Finset.mem_univ i))
  calc _ ≤ _ := h
    _ = _ := by rw [cyclicDiscreteEnergy_def]; ring

/-- **Energy sublevels lie in distance cuts.** A closed chain of energy at most `c` lies in
Abouzaid's distance cut with nonnegative cut-offs `δ` as soon as `2 c τᵢ ≤ δᵢ²` for every edge. -/
theorem mem_cyclicDistanceCut_of_cyclicDiscreteEnergy_le (hτ : ∀ i, 0 < τ i)
    {δ : Fin (n + 1) → ℝ} (hδ : 0 ≤ δ) {c : ℝ} (hcδ : ∀ i, 2 * c * τ i ≤ δ i ^ 2)
    {q : Fin (n + 1) → X} (hq : cyclicDiscreteEnergy τ q ≤ c) : q ∈ cyclicDistanceCut δ := by
  refine mem_cyclicDistanceCut.mpr fun i ↦ ?_
  have h := dist_sq_le_cyclicDiscreteEnergy_mul_step (fun j ↦ (hτ j).le) (hτ i) q
  have hsq : dist (q i) (q (i - 1)) ^ 2 ≤ δ i ^ 2 :=
    h.trans ((mul_le_mul_of_nonneg_right (by linarith) (hτ i).le).trans (hcδ i))
  exact (pow_le_pow_iff_left₀ dist_nonneg (hδ i) two_ne_zero).mp hsq

end Estimates

/-! ### Energy carriers -/

/-- **The energy carrier of closed chains**: the cyclic tuples whose cyclic discrete energy with
steps `τ` is strictly less than `c`. -/
def cyclicDiscreteEnergyStrictSublevel (τ : Fin (n + 1) → ℝ) (c : ℝ) : Set (Fin (n + 1) → X) :=
  {q | cyclicDiscreteEnergy τ q < c}

@[simp]
theorem mem_cyclicDiscreteEnergyStrictSublevel {τ : Fin (n + 1) → ℝ} {c : ℝ}
    {q : Fin (n + 1) → X} :
    q ∈ cyclicDiscreteEnergyStrictSublevel τ c ↔ cyclicDiscreteEnergy τ q < c :=
  Iff.rfl

/-- The energy carriers are open in the full product of vertex spaces. -/
theorem isOpen_cyclicDiscreteEnergyStrictSublevel (τ : Fin (n + 1) → ℝ) (c : ℝ) :
    IsOpen (cyclicDiscreteEnergyStrictSublevel (X := X) τ c) :=
  isOpen_lt (continuous_cyclicDiscreteEnergy τ) continuous_const

/-- Raising the cut-off enlarges the energy carrier. -/
theorem cyclicDiscreteEnergyStrictSublevel_mono (τ : Fin (n + 1) → ℝ) {a c : ℝ} (hac : a ≤ c) :
    cyclicDiscreteEnergyStrictSublevel (X := X) τ a ⊆ cyclicDiscreteEnergyStrictSublevel τ c :=
  fun _ hq ↦ hq.trans_le hac

/-- The constant loops lie in every energy carrier with a positive cut-off. -/
theorem const_mem_cyclicDiscreteEnergyStrictSublevel (τ : Fin (n + 1) → ℝ) {c : ℝ} (hc : 0 < c)
    (x : X) : (fun _ ↦ x) ∈ cyclicDiscreteEnergyStrictSublevel τ c := by
  simpa using hc

/-- **Energy carriers lie in distance cuts.** For positive steps and nonnegative cut-offs with
`2 c τᵢ ≤ δᵢ²`, the energy carrier with cut-off `c` lies in the distance cut with cut-offs `δ`. -/
theorem cyclicDiscreteEnergyStrictSublevel_subset_cyclicDistanceCut {τ : Fin (n + 1) → ℝ}
    (hτ : ∀ i, 0 < τ i) {δ : Fin (n + 1) → ℝ} (hδ : 0 ≤ δ) {c : ℝ}
    (hcδ : ∀ i, 2 * c * τ i ≤ δ i ^ 2) :
    cyclicDiscreteEnergyStrictSublevel (X := X) τ c ⊆ cyclicDistanceCut δ :=
  fun _ hq ↦ mem_cyclicDistanceCut_of_cyclicDiscreteEnergy_le hτ hδ hcδ hq.le

/-- The closed energy sublevels are closed. -/
theorem isClosed_setOf_cyclicDiscreteEnergy_le (τ : Fin (n + 1) → ℝ) (a : ℝ) :
    IsClosed {q : Fin (n + 1) → X | cyclicDiscreteEnergy τ q ≤ a} :=
  isClosed_le (continuous_cyclicDiscreteEnergy τ) continuous_const

/-- In a proper space, the closed chains of energy at most `a` whose base vertex lies in a closed
ball form a compact set: every vertex lies within `√(2 T a)` of the base vertex. -/
theorem isCompact_setOf_cyclicDiscreteEnergy_le_and_dist_le [ProperSpace X]
    {τ : Fin (n + 1) → ℝ} (hτ : ∀ i, 0 < τ i) (a : ℝ) (x : X) (r : ℝ) :
    IsCompact {q : Fin (n + 1) → X | cyclicDiscreteEnergy τ q ≤ a ∧ dist (q 0) x ≤ r} := by
  refine (isCompact_univ_pi fun _ : Fin (n + 1) ↦
    isCompact_closedBall x (r + √(2 * (∑ i, τ i) * a))).of_isClosed_subset
      ((isClosed_setOf_cyclicDiscreteEnergy_le τ a).inter
        (isClosed_le ((continuous_apply 0).dist continuous_const) continuous_const)) ?_
  intro q ⟨hq, hx⟩ j _
  have hT : 0 ≤ ∑ i, τ i := Finset.sum_nonneg fun i _ ↦ (hτ i).le
  have hj : dist (q 0) (q j) ≤ √(2 * (∑ i, τ i) * a) :=
    (dist_le_sqrt_cyclicDiscreteEnergy hτ q j).trans (by gcongr)
  rw [Metric.mem_closedBall]
  calc dist (q j) x ≤ dist (q j) (q 0) + dist (q 0) x := dist_triangle _ _ _
    _ ≤ r + √(2 * (∑ i, τ i) * a) := by rw [dist_comm]; linarith

/-- In a compact space the closed energy sublevels are compact. -/
theorem isCompact_setOf_cyclicDiscreteEnergy_le [CompactSpace X] (τ : Fin (n + 1) → ℝ) (a : ℝ) :
    IsCompact {q : Fin (n + 1) → X | cyclicDiscreteEnergy τ q ≤ a} :=
  (isClosed_setOf_cyclicDiscreteEnergy_le τ a).isCompact

/-- In a compact space, for `a < c`, the closed energy sublevel `{E ≤ a}` is compact as a subset
of the energy carrier with cut-off `c`. -/
theorem isCompact_cyclicDiscreteEnergyStrictSublevel_le [CompactSpace X]
    (τ : Fin (n + 1) → ℝ) {a c : ℝ} (hac : a < c) :
    IsCompact {q : cyclicDiscreteEnergyStrictSublevel (X := X) τ c |
      cyclicDiscreteEnergy τ (q : Fin (n + 1) → X) ≤ a} :=
  Topology.IsInducing.subtypeVal.isCompact_preimage'
    (isCompact_setOf_cyclicDiscreteEnergy_le τ a) fun q hq ↦ ⟨⟨q, hq.trans_lt hac⟩, rfl⟩

/-! ### Repeating the base vertex -/

/-- **Repeating the base vertex preserves the cyclic energy.** The tuple `(q₀, q₀, q₁, …, qₙ)`
has the closing edge of `q` at the vertex `0`, with the same step `τ 0`, a new edge of length zero
at the vertex `1`, with an arbitrary step `s`, and the edge of `q` at the vertex `i` at the vertex
`i + 1`, with the same step. -/
theorem cyclicDiscreteEnergy_cons_self (τ : Fin (n + 1) → ℝ) (s : ℝ) (q : Fin (n + 1) → X) :
    cyclicDiscreteEnergy (Fin.cons (τ 0) (Fin.cons s (Fin.tail τ)) : Fin (n + 2) → ℝ)
      (Fin.cons (q 0) q) = cyclicDiscreteEnergy τ q := by
  simp only [cyclicDiscreteEnergy_def, Fin.sum_univ_succ]
  -- The closing edge `(q₀, qₙ)` keeps the step `τ 0`.
  rw [dist_cons_self_zero_sub_one, Fin.cons_zero]
  -- The new edge `(q₀, q₀)` has length zero.
  rw [Fin.succ_zero_eq_one, dist_cons_self_one_sub_one]
  -- The edge `(qₖ, qₖ₊₁)` keeps the step `τ (k + 1)`.
  simp only [dist_cons_self_succ_succ_sub_one]
  simp only [Fin.cons_succ, Fin.tail]
  ring

/-- **The embedding `ιⁿ` of energy carriers**, `(q₀, …, qₙ) ↦ (q₀, q₀, q₁, …, qₙ)`, repeating the
base vertex. The new edge of length zero gets the step `s`, and every other edge keeps its step.
On underlying tuples it is the embedding `TauCeti.cyclicDistanceCutRepeatFirst` of distance
cuts. -/
def cyclicDiscreteEnergyRepeatFirst (τ : Fin (n + 1) → ℝ) (s c : ℝ) :
    C(cyclicDiscreteEnergyStrictSublevel (X := X) τ c,
      cyclicDiscreteEnergyStrictSublevel (X := X)
        (Fin.cons (τ 0) (Fin.cons s (Fin.tail τ)) : Fin (n + 2) → ℝ) c) where
  toFun q := ⟨Fin.cons (q.val 0) q.val, mem_cyclicDiscreteEnergyStrictSublevel.mpr <| by
    rw [cyclicDiscreteEnergy_cons_self]
    exact q.property⟩
  continuous_toFun :=
    (isEmbedding_cons_apply_zero.continuous.comp continuous_subtypeVal).subtype_mk _

@[simp]
theorem coe_cyclicDiscreteEnergyRepeatFirst_apply (τ : Fin (n + 1) → ℝ) (s c : ℝ)
    (q : cyclicDiscreteEnergyStrictSublevel (X := X) τ c) :
    (cyclicDiscreteEnergyRepeatFirst τ s c q : Fin (n + 2) → X) = Fin.cons (q.val 0) q.val :=
  (rfl)

/-- Repeating the base vertex is an embedding of energy carriers: forgetting the first vertex is a
continuous left inverse on tuples. -/
theorem isEmbedding_cyclicDiscreteEnergyRepeatFirst (τ : Fin (n + 1) → ℝ) (s c : ℝ) :
    Topology.IsEmbedding (cyclicDiscreteEnergyRepeatFirst (X := X) τ s c) := by
  have hmaps : MapsTo (fun q : Fin (n + 1) → X ↦ (Fin.cons (q 0) q : Fin (n + 2) → X))
      (cyclicDiscreteEnergyStrictSublevel τ c)
      (cyclicDiscreteEnergyStrictSublevel (Fin.cons (τ 0) (Fin.cons s (Fin.tail τ))) c) :=
    fun q hq ↦ (cyclicDiscreteEnergyRepeatFirst τ s c ⟨q, hq⟩).property
  -- the carrier map is the restriction of the tuple map to the carriers
  have hfun : ⇑(cyclicDiscreteEnergyRepeatFirst (X := X) τ s c) = hmaps.restrict := by
    ext q : 2
    rw [coe_cyclicDiscreteEnergyRepeatFirst_apply, MapsTo.val_restrict_apply]
  rw [hfun]
  exact isEmbedding_cons_apply_zero.restrict hmaps

/-- The range of the map repeating the base vertex: the closed chains of the target carrier whose
first two vertices agree. Their tails automatically lie in the source carrier, since repeating the
base vertex preserves the energy. -/
theorem range_cyclicDiscreteEnergyRepeatFirst (τ : Fin (n + 1) → ℝ) (s c : ℝ) :
    range (cyclicDiscreteEnergyRepeatFirst (X := X) τ s c) = Subtype.val ⁻¹' {p | p 1 = p 0} := by
  ext ⟨p, hp⟩
  constructor
  · rintro ⟨q, hq⟩
    rw [← hq]
    simp [Fin.cons_one]
  · intro h01
    have hp' : p = Fin.cons (Fin.tail p 0) (Fin.tail p) := by
      rw [show Fin.tail p 0 = p 0 by simpa [Fin.tail] using h01, Fin.cons_self_tail]
    refine ⟨⟨Fin.tail p, ?_⟩, Subtype.ext ?_⟩
    · rw [mem_cyclicDiscreteEnergyStrictSublevel, ← cyclicDiscreteEnergy_cons_self τ s, ← hp']
      exact hp
    · rw [coe_cyclicDiscreteEnergyRepeatFirst_apply, ← hp']

/-- In a Hausdorff space, repeating the base vertex is a closed embedding of energy carriers. -/
theorem isClosedEmbedding_cyclicDiscreteEnergyRepeatFirst [T2Space X] (τ : Fin (n + 1) → ℝ)
    (s c : ℝ) : Topology.IsClosedEmbedding (cyclicDiscreteEnergyRepeatFirst (X := X) τ s c) := by
  refine ⟨isEmbedding_cyclicDiscreteEnergyRepeatFirst τ s c, ?_⟩
  rw [range_cyclicDiscreteEnergyRepeatFirst]
  exact (isClosed_eq (continuous_apply 1) (continuous_apply 0)).preimage continuous_subtypeVal

/-! ### Forgetting and inserting vertices -/

section Forget

variable {t : Fin (n + 2) → ℝ} {τ : Fin (n + 1) → ℝ} {τ' : Fin (m + 1) → ℝ}

/-- **Forgetting vertices of a closed chain.** For an order embedding `r` of the vertex slots
`0, …, m + 1` of the coarse chain cut open at its base vertex into those `0, …, n + 1` of the fine
one, the coarse closed chain keeps the fine vertices in the selected slots. Retaining the first and
last slots, imposed by the theorems that use this map, makes the base vertex retained. -/
def cyclicDiscreteEnergyForget (r : Fin (m + 2) ↪o Fin (n + 2)) (q : Fin (n + 1) → X) :
    Fin (m + 1) → X :=
  fun j ↦ (Fin.snoc q (q 0) : Fin (n + 2) → X) (r j.castSucc)

omit [PseudoMetricSpace X] in
@[simp]
theorem cyclicDiscreteEnergyForget_apply (r : Fin (m + 2) ↪o Fin (n + 2)) (q : Fin (n + 1) → X)
    (j : Fin (m + 1)) :
    cyclicDiscreteEnergyForget r q j = (Fin.snoc q (q 0) : Fin (n + 2) → X) (r j.castSucc) :=
  (rfl)

omit [PseudoMetricSpace X] in
/-- Retaining every vertex is the identity. -/
@[simp]
theorem cyclicDiscreteEnergyForget_refl (q : Fin (n + 1) → X) :
    cyclicDiscreteEnergyForget (RelEmbedding.refl (· ≤ · : Fin (n + 2) → Fin (n + 2) → Prop)) q =
      q := by
  funext j
  simp

/-- Forgetting vertices is continuous. -/
@[fun_prop]
theorem continuous_cyclicDiscreteEnergyForget (r : Fin (m + 2) ↪o Fin (n + 2)) :
    Continuous (cyclicDiscreteEnergyForget (X := X) r) := by
  refine continuous_pi fun j ↦ ?_
  simp only [cyclicDiscreteEnergyForget]
  exact (continuous_apply _).comp
    (Continuous.finSnoc (A := fun _ : Fin (n + 2) ↦ X) continuous_id (continuous_apply 0))

omit [PseudoMetricSpace X] in
/-- Cutting open the coarse chain at its base vertex gives the fine chain, cut open at its base
vertex, read at the selected slots. -/
theorem snoc_cyclicDiscreteEnergyForget {r : Fin (m + 2) ↪o Fin (n + 2)} (h0 : r 0 = 0)
    (hlast : r (Fin.last (m + 1)) = Fin.last (n + 1)) (q : Fin (n + 1) → X) :
    (Fin.snoc (cyclicDiscreteEnergyForget r q) (cyclicDiscreteEnergyForget r q 0) :
      Fin (m + 2) → X) = (Fin.snoc q (q 0) : Fin (n + 2) → X) ∘ r := by
  funext j
  induction j using Fin.lastCases with
  | last =>
    rw [Fin.snoc_last, cyclicDiscreteEnergyForget_apply, Function.comp_apply, hlast,
      Fin.snoc_last, Fin.castSucc_zero, h0, Fin.snoc_apply_zero]
  | cast j => rw [Fin.snoc_castSucc, cyclicDiscreteEnergyForget_apply, Function.comp_apply]

omit [PseudoMetricSpace X] in
/-- Successive vertex-forgetting agrees with selecting the composite subsequence. -/
@[simp]
theorem cyclicDiscreteEnergyForget_trans {l : ℕ} (r : Fin (m + 2) ↪o Fin (n + 2))
    (s : Fin (l + 2) ↪o Fin (m + 2)) (q : Fin (n + 1) → X) :
    cyclicDiscreteEnergyForget s (cyclicDiscreteEnergyForget r q) =
      cyclicDiscreteEnergyForget (s.trans r) q := by
  funext j
  -- An increasing selection never sends a non-final slot to the final slot.
  obtain ⟨k, hk⟩ := (s j.castSucc).eq_castSucc_of_ne_last
    ((s.strictMono j.castSucc_lt_last).trans_le (Fin.le_last _)).ne
  rw [cyclicDiscreteEnergyForget_apply, ← hk, Fin.snoc_castSucc, cyclicDiscreteEnergyForget_apply,
    cyclicDiscreteEnergyForget_apply, RelEmbedding.trans_apply, ← hk]

/-- **Forgetting vertices does not increase the cyclic energy.** Let the fine steps `τ` be those
of the times `t`, and the coarse steps `τ'` those of the selected times `t ∘ r`, the steps of the
cut-open chains in both cases. Then the coarse closed chain retaining the selected vertices has at
most the energy of the fine closed chain. -/
theorem cyclicDiscreteEnergy_cyclicDiscreteEnergyForget_le (ht : StrictMono t)
    (hτ : ∀ k : Fin (n + 1), t k.succ - t k.castSucc = τ (k + 1))
    {r : Fin (m + 2) ↪o Fin (n + 2)} (h0 : r 0 = 0)
    (hlast : r (Fin.last (m + 1)) = Fin.last (n + 1))
    (hτ' : ∀ k : Fin (m + 1), t (r k.succ) - t (r k.castSucc) = τ' (k + 1))
    (q : Fin (n + 1) → X) :
    cyclicDiscreteEnergy τ' (cyclicDiscreteEnergyForget r q) ≤ cyclicDiscreteEnergy τ q := by
  rw [cyclicDiscreteEnergy_eq_discreteEnergy_snoc (t := t ∘ r) hτ',
    cyclicDiscreteEnergy_eq_discreteEnergy_snoc hτ, snoc_cyclicDiscreteEnergyForget h0 hlast]
  exact discreteEnergy_comp_le ht _ r

/-- **Forgetting vertices maps energy carriers into each other**, for the steps of the times `t`
and of the selected times `t ∘ r`, as in
`TauCeti.cyclicDiscreteEnergy_cyclicDiscreteEnergyForget_le`. -/
def cyclicDiscreteEnergyForgetMap (ht : StrictMono t)
    (hτ : ∀ k : Fin (n + 1), t k.succ - t k.castSucc = τ (k + 1))
    {r : Fin (m + 2) ↪o Fin (n + 2)} (h0 : r 0 = 0)
    (hlast : r (Fin.last (m + 1)) = Fin.last (n + 1))
    (hτ' : ∀ k : Fin (m + 1), t (r k.succ) - t (r k.castSucc) = τ' (k + 1)) (c : ℝ) :
    C(cyclicDiscreteEnergyStrictSublevel (X := X) τ c,
      cyclicDiscreteEnergyStrictSublevel (X := X) τ' c) where
  toFun q := ⟨cyclicDiscreteEnergyForget r q.val,
    (cyclicDiscreteEnergy_cyclicDiscreteEnergyForget_le ht hτ h0 hlast hτ' q.val).trans_lt
      q.property⟩
  continuous_toFun :=
    ((continuous_cyclicDiscreteEnergyForget r).comp continuous_subtypeVal).subtype_mk _

@[simp]
theorem coe_cyclicDiscreteEnergyForgetMap_apply (ht : StrictMono t)
    (hτ : ∀ k : Fin (n + 1), t k.succ - t k.castSucc = τ (k + 1))
    {r : Fin (m + 2) ↪o Fin (n + 2)} (h0 : r 0 = 0)
    (hlast : r (Fin.last (m + 1)) = Fin.last (n + 1))
    (hτ' : ∀ k : Fin (m + 1), t (r k.succ) - t (r k.castSucc) = τ' (k + 1)) (c : ℝ)
    (q : cyclicDiscreteEnergyStrictSublevel (X := X) τ c) :
    (cyclicDiscreteEnergyForgetMap ht hτ h0 hlast hτ' c q : Fin (m + 1) → X) =
      cyclicDiscreteEnergyForget r q.val :=
  (rfl)

/-- The identity selection induces the identity on the energy carrier. -/
@[simp]
theorem cyclicDiscreteEnergyForgetMap_refl (ht : StrictMono t)
    (hτ : ∀ k : Fin (n + 1), t k.succ - t k.castSucc = τ (k + 1)) (c : ℝ) :
    cyclicDiscreteEnergyForgetMap ht hτ (r := RelEmbedding.refl (· ≤ ·)) rfl rfl hτ c =
      ContinuousMap.id (cyclicDiscreteEnergyStrictSublevel (X := X) τ c) := by
  ext q : 2
  exact cyclicDiscreteEnergyForget_refl q.val

/-- The continuous maps between energy carriers commute with further vertex-forgetting. -/
@[simp]
theorem cyclicDiscreteEnergyForgetMap_trans {l : ℕ} {τ'' : Fin (l + 1) → ℝ} (ht : StrictMono t)
    (hτ : ∀ k : Fin (n + 1), t k.succ - t k.castSucc = τ (k + 1))
    {r : Fin (m + 2) ↪o Fin (n + 2)} (hr0 : r 0 = 0)
    (hrlast : r (Fin.last (m + 1)) = Fin.last (n + 1))
    (hτ' : ∀ k : Fin (m + 1), t (r k.succ) - t (r k.castSucc) = τ' (k + 1))
    {s : Fin (l + 2) ↪o Fin (m + 2)} (hs0 : s 0 = 0)
    (hslast : s (Fin.last (l + 1)) = Fin.last (m + 1))
    (hτ'' : ∀ k : Fin (l + 1), t (r (s k.succ)) - t (r (s k.castSucc)) = τ'' (k + 1)) (c : ℝ) :
    (cyclicDiscreteEnergyForgetMap (ht.comp r.strictMono) hτ' hs0 hslast hτ'' c).comp
        (cyclicDiscreteEnergyForgetMap (X := X) ht hτ hr0 hrlast hτ' c) =
      cyclicDiscreteEnergyForgetMap ht hτ (r := s.trans r)
        (by rw [RelEmbedding.trans_apply, hs0, hr0])
        (by rw [RelEmbedding.trans_apply, hslast, hrlast]) hτ'' c := by
  ext q : 2
  exact cyclicDiscreteEnergyForget_trans r s q.val

omit [PseudoMetricSpace X] in
/-- **Inserting vertices into a closed chain.** For a selection `r` retaining the first and last
slots, sample the curves `γ i` along the coarse edges at the fine times `t`, as in
`TauCeti.discreteEnergyInsert`, and drop the last slot of the sampled tuple. When the times are
strictly increasing and the last curve ends where the first one starts, that slot repeats the base
vertex (`TauCeti.snoc_cyclicDiscreteEnergyInsert`). -/
noncomputable def cyclicDiscreteEnergyInsert (t : Fin (n + 2) → ℝ)
    (r : Fin (m + 2) ↪o Fin (n + 2)) (h0 : r 0 = 0)
    (hlast : r (Fin.last (m + 1)) = Fin.last (n + 1)) (γ : Fin (m + 1) → ℝ → X) :
    Fin (n + 1) → X :=
  fun j ↦ discreteEnergyInsert t r h0 hlast γ j.castSucc

omit [PseudoMetricSpace X] in
@[simp]
theorem cyclicDiscreteEnergyInsert_apply (t : Fin (n + 2) → ℝ)
    (r : Fin (m + 2) ↪o Fin (n + 2)) (h0 : r 0 = 0)
    (hlast : r (Fin.last (m + 1)) = Fin.last (n + 1)) (γ : Fin (m + 1) → ℝ → X)
    (j : Fin (n + 1)) :
    cyclicDiscreteEnergyInsert t r h0 hlast γ j = discreteEnergyInsert t r h0 hlast γ j.castSucc :=
  (rfl)

omit [PseudoMetricSpace X] in
/-- Closed-chain insertion varies continuously with a parameter whenever each chosen segment does,
at each fixed time in `[0, 1]`. -/
@[fun_prop]
theorem continuous_cyclicDiscreteEnergyInsert {A : Type*} [TopologicalSpace A]
    [TopologicalSpace X] (ht : Monotone t) (r : Fin (m + 2) ↪o Fin (n + 2)) (h0 : r 0 = 0)
    (hlast : r (Fin.last (m + 1)) = Fin.last (n + 1)) (γ : A → Fin (m + 1) → ℝ → X)
    (hγ : ∀ i u, u ∈ Icc (0 : ℝ) 1 → Continuous (fun a ↦ γ a i u)) :
    Continuous (fun a ↦ cyclicDiscreteEnergyInsert t r h0 hlast (γ a)) :=
  continuous_pi fun j ↦ (continuous_apply j.castSucc).comp
    (continuous_discreteEnergyInsert ht r h0 hlast γ hγ)

omit [PseudoMetricSpace X] in
/-- Closed-chain insertion depends only on the curves restricted to their parameter interval
`[0, 1]`. -/
theorem cyclicDiscreteEnergyInsert_congr (ht : Monotone t) (r : Fin (m + 2) ↪o Fin (n + 2))
    (h0 : r 0 = 0) (hlast : r (Fin.last (m + 1)) = Fin.last (n + 1))
    {γ₁ γ₂ : Fin (m + 1) → ℝ → X} (hγ : ∀ i, EqOn (γ₁ i) (γ₂ i) (Icc 0 1)) :
    cyclicDiscreteEnergyInsert t r h0 hlast γ₁ = cyclicDiscreteEnergyInsert t r h0 hlast γ₂ :=
  funext fun j ↦ congrFun (discreteEnergyInsert_congr ht r h0 hlast hγ) j.castSucc

omit [PseudoMetricSpace X] in
/-- For the identity selection, insertion of glued curves reads each curve at its start. -/
@[simp]
theorem cyclicDiscreteEnergyInsert_refl (ht : StrictMono t) (γ : Fin (n + 1) → ℝ → X)
    (hγ : ∀ k : Fin n, γ k.castSucc 1 = γ k.succ 0) :
    cyclicDiscreteEnergyInsert t (RelEmbedding.refl (· ≤ ·)) rfl rfl γ = fun j ↦ γ j 0 := by
  funext j
  exact (discreteEnergyInsert_apply ht _ _ _ γ hγ j j.castSucc
    ⟨le_rfl, j.castSucc_le_succ⟩).trans (by simp)

omit [PseudoMetricSpace X] in
/-- When the times are strictly increasing and the last curve ends where the first one starts,
cutting open the inserted closed chain at its base vertex recovers the whole sampled chain. -/
theorem snoc_cyclicDiscreteEnergyInsert (ht : StrictMono t)
    (r : Fin (m + 2) ↪o Fin (n + 2)) (h0 : r 0 = 0)
    (hlast : r (Fin.last (m + 1)) = Fin.last (n + 1)) {γ : Fin (m + 1) → ℝ → X}
    (hγ : γ (Fin.last m) 1 = γ 0 0) :
    (Fin.snoc (cyclicDiscreteEnergyInsert t r h0 hlast γ)
      (cyclicDiscreteEnergyInsert t r h0 hlast γ 0) : Fin (n + 2) → X) =
        discreteEnergyInsert t r h0 hlast γ := by
  funext j
  induction j using Fin.lastCases with
  | last =>
    rw [Fin.snoc_last, cyclicDiscreteEnergyInsert_apply, Fin.castSucc_zero,
      discreteEnergyInsert_zero, discreteEnergyInsert_last ht, hγ]
  | cast j => rw [Fin.snoc_castSucc, cyclicDiscreteEnergyInsert_apply]

omit [PseudoMetricSpace X] in
/-- Inserting samples of curves joining consecutive vertices, read cyclically, retains every vertex
of the coarse closed chain: forgetting the inserted vertices recovers it. -/
theorem cyclicDiscreteEnergyForget_cyclicDiscreteEnergyInsert (ht : StrictMono t)
    (r : Fin (m + 2) ↪o Fin (n + 2)) (h0 : r 0 = 0)
    (hlast : r (Fin.last (m + 1)) = Fin.last (n + 1)) (p : Fin (m + 1) → X)
    (γ : Fin (m + 1) → ℝ → X) (hsource : ∀ i, γ i 0 = p i)
    (htarget : ∀ i : Fin m, γ i.castSucc 1 = p i.succ) :
    cyclicDiscreteEnergyForget r (cyclicDiscreteEnergyInsert t r h0 hlast γ) = p := by
  funext j
  -- An increasing selection retaining the last slot never sends a non-final slot there.
  obtain ⟨k, hk⟩ := (r j.castSucc).eq_castSucc_of_ne_last
    ((r.strictMono j.castSucc_lt_last).trans_eq hlast).ne
  rw [cyclicDiscreteEnergyForget_apply, ← hk, Fin.snoc_castSucc, cyclicDiscreteEnergyInsert_apply,
    hk, discreteEnergyInsert_comp_apply ht r h0 hlast (Fin.snoc p (γ (Fin.last m) 1)) γ
      (fun i ↦ by rw [hsource, Fin.snoc_castSucc]) (fun i ↦ ?_), Fin.snoc_castSucc]
  induction i using Fin.lastCases with
  | last => rw [Fin.succ_last, Fin.snoc_last]
  | cast i => rw [Fin.succ_castSucc, Fin.snoc_castSucc, htarget]

/-- **Geodesic insertion preserves the cyclic energy.** Sampling constant-speed minimizing segments
along the edges of a closed chain, the closing edge included, at the fine times `t`, gives a fine
closed chain of the same energy, for the steps of `t` and of the selected times `t ∘ r`. -/
theorem cyclicDiscreteEnergy_cyclicDiscreteEnergyInsert (ht : StrictMono t)
    (hτ : ∀ k : Fin (n + 1), t k.succ - t k.castSucc = τ (k + 1))
    {r : Fin (m + 2) ↪o Fin (n + 2)} (h0 : r 0 = 0)
    (hlast : r (Fin.last (m + 1)) = Fin.last (n + 1))
    (hτ' : ∀ k : Fin (m + 1), t (r k.succ) - t (r k.castSucc) = τ' (k + 1))
    (p : Fin (m + 1) → X) (γ : Fin (m + 1) → ℝ → X)
    (hγ : ∀ i, IsGeodesicSegment (γ i) (p i) (p (i + 1))) :
    cyclicDiscreteEnergy τ (cyclicDiscreteEnergyInsert t r h0 hlast γ) =
      cyclicDiscreteEnergy τ' p := by
  rw [cyclicDiscreteEnergy_eq_discreteEnergy_snoc hτ,
    snoc_cyclicDiscreteEnergyInsert ht r h0 hlast
      (by rw [(hγ _).target, (hγ 0).source, Fin.last_add_one]),
    discreteEnergy_discreteEnergyInsert ht r h0 hlast (Fin.snoc p (p 0)) γ
      (fun i ↦ by simpa only [Fin.snoc_castSucc, Fin.snoc_self_zero_succ] using hγ i),
    cyclicDiscreteEnergy_eq_discreteEnergy_snoc (t := t ∘ r) hτ']

/-- **Geodesic insertion for closed chains.** In a geodesic space, for times `t` and a selection
`r` retaining the first and last slots, every coarse closed chain is obtained by forgetting
vertices of a fine closed chain with the same energy, for the steps of `t ∘ r` and of `t`: insert,
along each coarse edge, the points of a constant-speed minimizing segment at the intermediate
times. No continuous choice of segments is asserted. -/
theorem exists_cyclicDiscreteEnergyForget_eq_and_cyclicDiscreteEnergy_eq [IsGeodesicSpace X]
    (ht : StrictMono t) (hτ : ∀ k : Fin (n + 1), t k.succ - t k.castSucc = τ (k + 1))
    {r : Fin (m + 2) ↪o Fin (n + 2)} (h0 : r 0 = 0)
    (hlast : r (Fin.last (m + 1)) = Fin.last (n + 1))
    (hτ' : ∀ k : Fin (m + 1), t (r k.succ) - t (r k.castSucc) = τ' (k + 1))
    (p : Fin (m + 1) → X) :
    ∃ q : Fin (n + 1) → X, cyclicDiscreteEnergyForget r q = p ∧
      cyclicDiscreteEnergy τ q = cyclicDiscreteEnergy τ' p := by
  choose γ hγ using fun i : Fin (m + 1) ↦
    IsGeodesicSpace.exists_isGeodesicSegment (p i) (p (i + 1))
  exact ⟨cyclicDiscreteEnergyInsert t r h0 hlast γ,
    cyclicDiscreteEnergyForget_cyclicDiscreteEnergyInsert ht r h0 hlast p γ
      (fun i ↦ (hγ i).source) (fun i ↦ by rw [(hγ _).target, Fin.coeSucc_eq_succ]),
    cyclicDiscreteEnergy_cyclicDiscreteEnergyInsert ht hτ h0 hlast hτ' p γ hγ⟩

section InsertMap

variable (ht : StrictMono t) (hτ : ∀ k : Fin (n + 1), t k.succ - t k.castSucc = τ (k + 1))
  {r : Fin (m + 2) ↪o Fin (n + 2)} (h0 : r 0 = 0)
  (hlast : r (Fin.last (m + 1)) = Fin.last (n + 1))
  (hτ' : ∀ k : Fin (m + 1), t (r k.succ) - t (r k.castSucc) = τ' (k + 1)) (c : ℝ)
  (γ : cyclicDiscreteEnergyStrictSublevel (X := X) τ' c → Fin (m + 1) → ℝ → X)
  (hγ : ∀ p i, IsGeodesicSegment (γ p i) (p.val i) (p.val (i + 1)))
  (hcont : ∀ i u, u ∈ Icc (0 : ℝ) 1 → Continuous (fun p ↦ γ p i u))

/-- **Geodesic insertion maps energy carriers into each other.** Choose constant-speed minimizing
segments `γ p i` along the edges of each closed chain `p` in the strict sublevel below `c` for the
steps `τ'` of the selected times `t ∘ r`, such that for each edge `i` and each parameter `u` in
`[0, 1]` the point `γ p i u` depends continuously on `p`. Insertion is then a continuous map into
the strict sublevel below the same `c` for the steps `τ` of `t`. The choice is needed only on the
coarse sublevel. -/
noncomputable def cyclicDiscreteEnergyInsertMap :
    C(cyclicDiscreteEnergyStrictSublevel (X := X) τ' c,
      cyclicDiscreteEnergyStrictSublevel (X := X) τ c) where
  toFun p := ⟨cyclicDiscreteEnergyInsert t r h0 hlast (γ p),
    (cyclicDiscreteEnergy_cyclicDiscreteEnergyInsert ht hτ h0 hlast hτ' p.val (γ p)
      (hγ p)).trans_lt p.property⟩
  continuous_toFun :=
    (continuous_cyclicDiscreteEnergyInsert ht.monotone r h0 hlast γ hcont).subtype_mk _

@[simp]
theorem coe_cyclicDiscreteEnergyInsertMap_apply
    (p : cyclicDiscreteEnergyStrictSublevel (X := X) τ' c) :
    (cyclicDiscreteEnergyInsertMap ht hτ h0 hlast hτ' c γ hγ hcont p : Fin (n + 1) → X) =
      cyclicDiscreteEnergyInsert t r h0 hlast (γ p) :=
  (rfl)

/-- Insertion of closed chains depends only on the chosen segments on `[0, 1]`. -/
theorem cyclicDiscreteEnergyInsertMap_congr
    (γ₂ : cyclicDiscreteEnergyStrictSublevel (X := X) τ' c → Fin (m + 1) → ℝ → X)
    (hγ₂ : ∀ p i, IsGeodesicSegment (γ₂ p i) (p.val i) (p.val (i + 1)))
    (hcont₂ : ∀ i u, u ∈ Icc (0 : ℝ) 1 → Continuous (fun p ↦ γ₂ p i u))
    (heq : ∀ p i, EqOn (γ p i) (γ₂ p i) (Icc 0 1)) :
    cyclicDiscreteEnergyInsertMap ht hτ h0 hlast hτ' c γ hγ hcont =
      cyclicDiscreteEnergyInsertMap ht hτ h0 hlast hτ' c γ₂ hγ₂ hcont₂ := by
  ext p : 2
  exact cyclicDiscreteEnergyInsert_congr ht.monotone r h0 hlast (heq p)

/-- Forgetting the newly inserted vertices recovers the original point of the coarse carrier. -/
@[simp]
theorem cyclicDiscreteEnergyForgetMap_cyclicDiscreteEnergyInsertMap
    (p : cyclicDiscreteEnergyStrictSublevel (X := X) τ' c) :
    cyclicDiscreteEnergyForgetMap ht hτ h0 hlast hτ' c
      (cyclicDiscreteEnergyInsertMap ht hτ h0 hlast hτ' c γ hγ hcont p) = p :=
  Subtype.ext <| cyclicDiscreteEnergyForget_cyclicDiscreteEnergyInsert ht r h0 hlast p.val (γ p)
    (fun i ↦ (hγ p i).source) (fun i ↦ by rw [(hγ p _).target, Fin.coeSucc_eq_succ])

/-- Forgetting the newly inserted vertices is a left inverse to continuous geodesic insertion of
closed chains. -/
@[simp]
theorem cyclicDiscreteEnergyForgetMap_comp_cyclicDiscreteEnergyInsertMap :
    (cyclicDiscreteEnergyForgetMap ht hτ h0 hlast hτ' c).comp
        (cyclicDiscreteEnergyInsertMap ht hτ h0 hlast hτ' c γ hγ hcont) =
      ContinuousMap.id (cyclicDiscreteEnergyStrictSublevel (X := X) τ' c) := by
  ext p : 1
  exact cyclicDiscreteEnergyForgetMap_cyclicDiscreteEnergyInsertMap ht hτ h0 hlast hτ' c γ hγ
    hcont p

end InsertMap

/-- Insertion for the identity selection is the identity on the energy carrier. -/
@[simp]
theorem cyclicDiscreteEnergyInsertMap_refl (ht : StrictMono t)
    (hτ : ∀ k : Fin (n + 1), t k.succ - t k.castSucc = τ (k + 1)) (c : ℝ)
    (γ : cyclicDiscreteEnergyStrictSublevel (X := X) τ c → Fin (n + 1) → ℝ → X)
    (hγ : ∀ p i, IsGeodesicSegment (γ p i) (p.val i) (p.val (i + 1)))
    (hcont : ∀ i u, u ∈ Icc (0 : ℝ) 1 → Continuous (fun p ↦ γ p i u)) :
    cyclicDiscreteEnergyInsertMap ht hτ (r := RelEmbedding.refl (· ≤ ·)) rfl rfl hτ c γ hγ hcont =
      ContinuousMap.id (cyclicDiscreteEnergyStrictSublevel (X := X) τ c) := by
  ext p : 1
  have h := cyclicDiscreteEnergyForgetMap_cyclicDiscreteEnergyInsertMap ht hτ
    (r := RelEmbedding.refl (· ≤ ·)) rfl rfl hτ c γ hγ hcont p
  rwa [cyclicDiscreteEnergyForgetMap_refl] at h

end Forget

end TauCeti
