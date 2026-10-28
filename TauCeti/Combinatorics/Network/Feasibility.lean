/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Group.PosPart
public import TauCeti.Combinatorics.Network.AuxiliaryTerminals
public import TauCeti.Combinatorics.Network.ShortestAugmentation
public import TauCeti.Combinatorics.Network.Shift

/-!
# Feasibility of prescribed excess and Hoffman's circulation theorem

Let `Q` be an arrow family on a finite vertex type `V`, with lower and upper bounds `lo ≤ hi` on
its arrows in a linearly ordered additive group, and let `b : V → K` prescribe the excess at every
vertex. Either bound may be negative. An assignment between the bounds with excess `b`, an element
of `TauCeti.ExcessFlow lo hi b`, exists exactly when `∑ v, b v = 0` and, for every vertex set `S`,
the prescribed excess on `S` plus the lower bound on the arrows leaving `S` is at most the upper
bound on the arrows entering `S`. Both conditions are necessary, because the total excess on `S`
is the value entering `S` minus the value leaving it. For `b = 0` this is **Hoffman's circulation
theorem**: a circulation between the bounds exists exactly when, for every vertex set `S`, the
lower bound on the arrows entering `S` is at most the upper bound on the arrows leaving `S`.

The criterion is reduced to max-flow/min-cut on the network with auxiliary terminals of
`TauCeti.AuxTerminalHom`, with every vertex attached to both fresh terminals. Write
`b' = b - excessAt lo` for the excess still prescribed after subtracting the lower bounds. Each
original arrow gets capacity `hi - lo`, the arrow from the fresh source to `v` gets the supply
`(b' v)⁻`, and the arrow from `v` to the fresh sink gets the demand `(b' v)⁺`
(`TauCeti.excessFlowCapacity`). Every flow between the fresh terminals has value at most the total
demand. When `∑ v, b v = 0`, the flows of exactly this value are those saturating every auxiliary
arrow, and they correspond to the assignments with excess `b` (`TauCeti.ExcessFlow.auxFlowEquiv`).
The cut condition makes every cut between the fresh terminals at least as large as the total
demand, so a maximum flow, and hence an assignment with excess `b`, exists. Maximum flows can be
chosen with values in any additive subgroup containing the capacities, so an assignment with
excess `b` can be chosen with values in any additive subgroup containing `lo`, `hi` and `b`.

## Main definitions

* `TauCeti.excessFlowCapacity lo hi b`: the capacities of the auxiliary network.
* `TauCeti.ExcessFlow.toAuxFlow` and `TauCeti.Flow.toExcessFlow`: the flow of the auxiliary
  network corresponding to an assignment with excess `b`, and the assignment with excess `b`
  corresponding to a flow of the auxiliary network of value the total demand.
* `TauCeti.ExcessFlow.auxFlowEquiv`: the correspondence between them, which preserves values in
  additive subgroups in both directions (`TauCeti.ExcessFlow.toAuxFlow_mem` and
  `TauCeti.Flow.toExcessFlow_mem`).

## Main results

* `TauCeti.ExcessFlow.sum_eq_zero` and `TauCeti.ExcessFlow.sum_add_arrowSum_le`: the necessary
  conditions.
* `TauCeti.Flow.val_le_sum_posPart`: every flow of the auxiliary network has value at most the
  total demand.
* `TauCeti.Flow.val_eq_sum_posPart_iff`: it attains the total demand exactly when it saturates
  every auxiliary arrow.
* `TauCeti.exists_excessFlow_mem`: existence of an assignment with excess `b` and values in an
  additive subgroup containing the bounds and `b`, under the necessary conditions.
* `TauCeti.nonempty_excessFlow_iff`: the feasibility criterion for prescribed excess.
* `TauCeti.nonempty_excessFlow_zero_iff`: Hoffman's circulation theorem.
* `TauCeti.nonempty_excessFlow_or_sum_ne_zero_or_exists_lt` and
  `TauCeti.nonempty_excessFlow_zero_or_exists_lt`: an assignment with excess `b`, or a certificate
  that none exists.

## References

* A. J. Hoffman, *Some recent applications of the theory of linear inequalities to extremal
  combinatorial analysis*, Proc. Sympos. Appl. Math. 10, American Mathematical Society, 1960.
* A. Schrijver, *Combinatorial Optimization: Polyhedra and Efficiency*, Springer, 2003,
  Chapter 11.
-/

public section

namespace TauCeti

open Finset Sum

universe u v w

variable {V : Type u} {Q : V → V → Type v} {K : Type w}
variable [Fintype V] [∀ x y, Fintype (Q x y)] [AddCommGroup K]

/-! ### The auxiliary network -/

section Lattice

variable [Lattice K] {lo hi : Assignment Q K} {b : V → K}

variable (lo hi b) in
/-- The capacities deciding whether some assignment between `lo` and `hi` has excess `b`, on the
arrow family with auxiliary terminals attached to every vertex. Writing `b' = b - excessAt lo`,
each original arrow `e` has capacity `hi e - lo e`, the arrow from the fresh source to `v` has
capacity `(b' v)⁻` and the arrow from `v` to the fresh sink has capacity `(b' v)⁺`. -/
def excessFlowCapacity : Assignment (AuxTerminalHom Q univ univ) K :=
  auxTerminalCapacity (hi - lo) (fun v ↦ (b v - excessAt lo v)⁻) fun v ↦ (b v - excessAt lo v)⁺

@[simp]
theorem excessFlowCapacity_original {x y : V} (e : Q x y) :
    excessFlowCapacity lo hi b (AuxTerminalHom.original e) = hi e - lo e :=
  auxTerminalCapacity_original _ _ _ e

@[simp]
theorem excessFlowCapacity_source (v : V) :
    excessFlowCapacity lo hi b (AuxTerminalHom.source (mem_univ v)) = (b v - excessAt lo v)⁻ :=
  auxTerminalCapacity_source _ _ _ (mem_univ v)

@[simp]
theorem excessFlowCapacity_sink (v : V) :
    excessFlowCapacity lo hi b (AuxTerminalHom.sink (mem_univ v)) = (b v - excessAt lo v)⁺ :=
  auxTerminalCapacity_sink _ _ _ (mem_univ v)

variable [IsOrderedAddMonoid K]

/-- The capacities of the auxiliary network are nonnegative when `lo ≤ hi`. -/
theorem excessFlowCapacity_nonneg (hlohi : lo ≤ hi) : 0 ≤ excessFlowCapacity lo hi b :=
  auxTerminalCapacity_nonneg (fun _ _ e ↦ sub_nonneg.2 (hlohi _ _ e))
    (fun _ _ ↦ negPart_nonneg _) fun _ _ ↦ posPart_nonneg _

/-- The total demand equals the total supply when the prescribed excess sums to zero. -/
private theorem sum_negPart_eq_sum_posPart (hb : ∑ v, b v = 0) :
    ∑ v, (b v - excessAt lo v)⁻ = ∑ v, (b v - excessAt lo v)⁺ := by
  refine (sub_eq_zero.1 ?_).symm
  rw [← sum_sub_distrib]
  simp_rw [posPart_sub_negPart]
  rw [sum_sub_distrib, hb, sum_excessAt, sub_zero]

variable [DecidableEq V]

namespace ExcessFlow

/-- The flow of the auxiliary network corresponding to an assignment `f` with excess `b`: it
carries `f e - lo e` on each original arrow `e` and saturates every auxiliary arrow. -/
def toAuxFlow (f : ExcessFlow lo hi b) :
    Flow (excessFlowCapacity lo hi b) (inr false) (inr true) where
  toFun := auxTerminalCapacity (f.val - lo) (fun v ↦ (b v - excessAt lo v)⁻)
    fun v ↦ (b v - excessAt lo v)⁺
  mem_Icc := ⟨auxTerminalCapacity_nonneg (fun _ _ e ↦ sub_nonneg.2 (f.mem_Icc.1 _ _ e))
      (fun _ _ ↦ negPart_nonneg _) fun _ _ ↦ posPart_nonneg _,
    AuxTerminalHom.forall_iff.2 ⟨fun _ _ e ↦ by
      simpa using sub_le_sub_right (f.mem_Icc.2 _ _ e) (lo e), fun _ _ ↦ by simp,
      fun _ _ ↦ by simp⟩⟩
  conserve
    | inl v, _, _ => by
      simp only [AuxTerminalHom.excessAt_inl, auxTerminalRestrict_auxTerminalCapacity,
        AuxTerminalHom.sum_source (mem_univ v), AuxTerminalHom.sum_sink (mem_univ v),
        auxTerminalCapacity_source, auxTerminalCapacity_sink, excessAt_sub, f.excessAt_eq]
      rw [add_sub_assoc, negPart_sub_posPart, add_neg_cancel]
    | inr false, hσ, _ => (hσ rfl).elim
    | inr true, _, hτ => (hτ rfl).elim
  excessAt_sink_nonneg := by
    rw [AuxTerminalHom.excessAt_inr_true]
    exact sum_nonneg fun v _ ↦ by
      simp [AuxTerminalHom.sum_sink (mem_univ v)]

@[simp]
theorem toAuxFlow_toFun (f : ExcessFlow lo hi b) :
    f.toAuxFlow.toFun = auxTerminalCapacity (f.val - lo) (fun v ↦ (b v - excessAt lo v)⁻)
      fun v ↦ (b v - excessAt lo v)⁺ :=
  (rfl)

/-- The flow of the auxiliary network corresponding to an assignment with excess `b` has value the
total demand. -/
@[simp]
theorem val_toAuxFlow (f : ExcessFlow lo hi b) :
    f.toAuxFlow.val = ∑ v, (b v - excessAt lo v)⁺ := by
  rw [BoundedFlow.val_def, AuxTerminalHom.excessAt_inr_true, toAuxFlow_toFun]
  exact sum_congr rfl fun v _ ↦ by simp [AuxTerminalHom.sum_sink (mem_univ v)]

end ExcessFlow

namespace Flow

variable (g : Flow (excessFlowCapacity lo hi b) (inr false) (inr true))

omit [IsOrderedAddMonoid K] in
/-- The value of a flow of the auxiliary network is its total value on the arrows to the fresh
sink. -/
private theorem val_eq_sum_sink :
    g.val = ∑ v, g.toFun (AuxTerminalHom.sink (A := univ) (mem_univ v)) := by
  rw [BoundedFlow.val_def, AuxTerminalHom.excessAt_inr_true]
  exact sum_congr rfl fun v _ ↦ AuxTerminalHom.sum_sink (mem_univ v) _

omit [IsOrderedAddMonoid K] in
/-- The value of a flow of the auxiliary network is its total value on the arrows from the fresh
source. -/
private theorem val_eq_sum_source :
    g.val = ∑ v, g.toFun (AuxTerminalHom.source (B := univ) (mem_univ v)) := by
  rw [← neg_neg g.val, ← BoundedFlow.excessAt_source, AuxTerminalHom.excessAt_inr_false, neg_neg]
  exact sum_congr rfl fun v _ ↦ AuxTerminalHom.sum_source (mem_univ v) _

/-- Every flow of the auxiliary network has value at most the total demand. -/
theorem val_le_sum_posPart : g.val ≤ ∑ v, (b v - excessAt lo v)⁺ := by
  rw [val_eq_sum_sink]
  exact sum_le_sum fun v _ ↦ by
    simpa using g.le_upper (AuxTerminalHom.sink (A := univ) (mem_univ v))

/-- When the prescribed excess sums to zero, a flow of the auxiliary network has value the total
demand exactly when it saturates every arrow from the fresh source and every arrow to the fresh
sink. -/
theorem val_eq_sum_posPart_iff (hb : ∑ v, b v = 0) :
    g.val = ∑ v, (b v - excessAt lo v)⁺ ↔
      (∀ v, g.toFun (AuxTerminalHom.source (mem_univ v)) = (b v - excessAt lo v)⁻) ∧
        ∀ v, g.toFun (AuxTerminalHom.sink (mem_univ v)) = (b v - excessAt lo v)⁺ := by
  have hsource := sum_eq_sum_iff_of_le (s := univ) fun v _ ↦
    g.le_upper (AuxTerminalHom.source (B := univ) (mem_univ v))
  have hsink := sum_eq_sum_iff_of_le (s := univ) fun v _ ↦
    g.le_upper (AuxTerminalHom.sink (A := univ) (mem_univ v))
  simp only [excessFlowCapacity_source, excessFlowCapacity_sink, mem_univ, forall_const]
    at hsource hsink
  rw [← hsource, ← hsink, ← val_eq_sum_source, ← val_eq_sum_sink, sum_negPart_eq_sum_posPart hb,
    and_self]

/-- The assignment with excess `b` corresponding to a flow of the auxiliary network of value the
total demand, when the prescribed excess sums to zero: `lo` plus the restriction of the flow to the
original arrows. -/
def toExcessFlow (hb : ∑ v, b v = 0) (hg : g.val = ∑ v, (b v - excessAt lo v)⁺) :
    ExcessFlow lo hi b :=
  ⟨lo + auxTerminalRestrict g.toFun,
    ⟨fun _ _ e ↦ by simpa using g.nonneg (AuxTerminalHom.original e), fun _ _ e ↦ by
      simpa [le_sub_iff_add_le'] using g.le_upper (AuxTerminalHom.original e)⟩, by
    obtain ⟨hsource, hsink⟩ := (g.val_eq_sum_posPart_iff hb).1 hg
    funext v
    have h := g.conserve (inl v) inl_ne_inr inl_ne_inr
    rw [AuxTerminalHom.excessAt_inl, AuxTerminalHom.sum_source (mem_univ v),
      AuxTerminalHom.sum_sink (mem_univ v), hsource, hsink, add_sub_assoc, negPart_sub_posPart,
      add_neg_eq_zero] at h
    rw [excessAt_add, h, add_sub_cancel]⟩

@[simp]
theorem toExcessFlow_val (hb : ∑ v, b v = 0) (hg : g.val = ∑ v, (b v - excessAt lo v)⁺) :
    (g.toExcessFlow hb hg).val = lo + auxTerminalRestrict g.toFun :=
  (rfl)

/-- The assignment with excess `b` corresponding to a flow of the auxiliary network takes values in
every additive subgroup containing the flow and the lower bounds. -/
theorem toExcessFlow_mem (H : AddSubgroup K) (hlo : ∀ ⦃x y⦄ (e : Q x y), lo e ∈ H)
    (hb : ∑ v, b v = 0) (hg : g.val = ∑ v, (b v - excessAt lo v)⁺)
    (hgH : ∀ ⦃x y⦄ (e : AuxTerminalHom Q univ univ x y), g.toFun e ∈ H) :
    ∀ ⦃x y⦄ (e : Q x y), (g.toExcessFlow hb hg).val e ∈ H :=
  fun _ _ e ↦ by simpa using H.add_mem (hlo e) (hgH (AuxTerminalHom.original e))

end Flow

namespace ExcessFlow

/-- **Reduction to max-flow.** When the prescribed excess sums to zero, the assignments between
`lo` and `hi` with excess `b` correspond to the flows of the auxiliary network of value the total
demand, by `ExcessFlow.toAuxFlow` and `Flow.toExcessFlow`. -/
def auxFlowEquiv (hb : ∑ v, b v = 0) :
    ExcessFlow lo hi b ≃ {g : Flow (excessFlowCapacity lo hi b) (inr false) (inr true) //
      g.val = ∑ v, (b v - excessAt lo v)⁺} where
  toFun f := ⟨f.toAuxFlow, f.val_toAuxFlow⟩
  invFun g := g.1.toExcessFlow hb g.2
  left_inv f := Subtype.ext (by
    funext x y e
    simp)
  right_inv g := by
    obtain ⟨hsource, hsink⟩ := (g.1.val_eq_sum_posPart_iff hb).1 g.2
    refine Subtype.ext (Flow.ext (funext₃ (AuxTerminalHom.forall_iff.2
      ⟨fun _ _ e ↦ by simp, fun v _ ↦ by simp [hsource], fun v _ ↦ by simp [hsink]⟩)))

@[simp]
theorem auxFlowEquiv_apply_coe (hb : ∑ v, b v = 0) (f : ExcessFlow lo hi b) :
    (auxFlowEquiv hb f : Flow (excessFlowCapacity lo hi b) (inr false) (inr true)) =
      f.toAuxFlow :=
  (rfl)

@[simp]
theorem auxFlowEquiv_symm_apply (hb : ∑ v, b v = 0)
    (g : {g : Flow (excessFlowCapacity lo hi b) (inr false) (inr true) //
      g.val = ∑ v, (b v - excessAt lo v)⁺}) :
    (auxFlowEquiv hb).symm g = g.1.toExcessFlow hb g.2 :=
  (rfl)

end ExcessFlow

end Lattice

/-! ### Feasibility -/

section LinearOrder

variable [LinearOrder K] [IsOrderedAddMonoid K] {lo hi : Assignment Q K} {b : V → K}

/-- The supply and the demand at every vertex lie in every additive subgroup containing the lower
bounds and the prescribed excess. -/
private theorem negPart_mem_and_posPart_mem (H : AddSubgroup K)
    (hlo : ∀ ⦃x y⦄ (e : Q x y), lo e ∈ H) (hb : ∀ v, b v ∈ H) (v : V) :
    (b v - excessAt lo v)⁻ ∈ H ∧ (b v - excessAt lo v)⁺ ∈ H := by
  have hb' : b v - excessAt lo v ∈ H := H.sub_mem (hb v) (excessAt_mem hlo v)
  rw [negPart_eq_ite, posPart_eq_ite]
  constructor <;> split_ifs
  exacts [H.neg_mem hb', H.zero_mem, hb', H.zero_mem]

/-- The capacities of the auxiliary network lie in every additive subgroup containing the bounds
and the prescribed excess. -/
theorem excessFlowCapacity_mem (H : AddSubgroup K) (hlo : ∀ ⦃x y⦄ (e : Q x y), lo e ∈ H)
    (hhi : ∀ ⦃x y⦄ (e : Q x y), hi e ∈ H) (hb : ∀ v, b v ∈ H) :
    ∀ ⦃x y⦄ (e : AuxTerminalHom Q univ univ x y), excessFlowCapacity lo hi b e ∈ H :=
  AuxTerminalHom.forall_iff.2 ⟨fun _ _ e ↦ by simpa using H.sub_mem (hhi e) (hlo e),
    fun v _ ↦ by simpa using (negPart_mem_and_posPart_mem H hlo hb v).1,
    fun v _ ↦ by simpa using (negPart_mem_and_posPart_mem H hlo hb v).2⟩

variable [DecidableEq V]

/-- The flow of the auxiliary network corresponding to an assignment with excess `b` takes values in
every additive subgroup containing the assignment and the lower bounds. -/
theorem ExcessFlow.toAuxFlow_mem (H : AddSubgroup K) (hlo : ∀ ⦃x y⦄ (e : Q x y), lo e ∈ H)
    (f : ExcessFlow lo hi b) (hf : ∀ ⦃x y⦄ (e : Q x y), f.val e ∈ H) :
    ∀ ⦃x y⦄ (e : AuxTerminalHom Q univ univ x y), f.toAuxFlow.toFun e ∈ H := by
  have hb (v : V) : b v ∈ H := f.excessAt_eq v ▸ excessAt_mem hf v
  exact AuxTerminalHom.forall_iff.2
    ⟨fun _ _ e ↦ by simpa using H.sub_mem (hf e) (hlo e),
      fun v _ ↦ by simpa using (negPart_mem_and_posPart_mem H hlo hb v).1,
      fun v _ ↦ by simpa using (negPart_mem_and_posPart_mem H hlo hb v).2⟩

/-- Under the cut condition, every cut between the fresh terminals of the auxiliary network has
capacity at least the total demand. -/
theorem sum_posPart_le_arrowSum_excessFlowCapacity
    (hS : ∀ S : Finset V, ∑ v ∈ S, b v + arrowSum lo S Sᶜ ≤ arrowSum hi Sᶜ S)
    {S : Finset (V ⊕ Bool)} (hσ : inr false ∈ S) (hτ : inr true ∉ S) :
    ∑ v, (b v - excessAt lo v)⁺ ≤ arrowSum (excessFlowCapacity lo hi b) S Sᶜ := by
  set T := S.toLeft
  have hcut := hS Tᶜ
  rw [compl_compl] at hcut
  have hexcess := sum_excessAt_eq_arrowSum_sub lo Tᶜ
  rw [compl_compl] at hexcess
  have hpos : ∑ v ∈ Tᶜ, (b v - excessAt lo v)⁺ =
      ∑ v ∈ Tᶜ, (b v - excessAt lo v)⁻ + (∑ v ∈ Tᶜ, b v - ∑ v ∈ Tᶜ, excessAt lo v) := by
    rw [← sum_sub_distrib, ← sum_add_distrib]
    exact sum_congr rfl fun v _ ↦ sub_eq_iff_eq_add'.1 (posPart_sub_negPart _)
  rw [excessFlowCapacity, arrowSum_auxTerminalCapacity _ _ _ hσ hτ, ← compl_eq_univ_sdiff,
    univ_inter, ← sum_add_sum_compl T, hpos, hexcess, arrowSum_sub, ← sub_nonneg]
  convert sub_nonneg.2 hcut using 1
  abel

/-- **Feasibility with values in a subgroup.** If `lo ≤ hi`, the prescribed excess `b` sums to
zero, and for every vertex set `S` the prescribed excess on `S` plus the lower bound on the arrows
leaving `S` is at most the upper bound on the arrows entering `S`, then some assignment between
`lo` and `hi` has excess `b`. It can be chosen with values in any additive subgroup `H` containing
the bounds and `b`. -/
theorem exists_excessFlow_mem (hlohi : lo ≤ hi) (hb : ∑ v, b v = 0)
    (hS : ∀ S : Finset V, ∑ v ∈ S, b v + arrowSum lo S Sᶜ ≤ arrowSum hi Sᶜ S)
    (H : AddSubgroup K) (hlo : ∀ ⦃x y⦄ (e : Q x y), lo e ∈ H)
    (hhi : ∀ ⦃x y⦄ (e : Q x y), hi e ∈ H) (hbH : ∀ v, b v ∈ H) :
    ∃ f : ExcessFlow lo hi b, ∀ ⦃x y⦄ (e : Q x y), f.val e ∈ H := by
  obtain ⟨g, hg, hgH⟩ := Flow.exists_isMaximum_mem (s := inr false) (t := inr true)
    (excessFlowCapacity_nonneg hlohi) H (excessFlowCapacity_mem H hlo hhi hbH)
  obtain ⟨S, hσ, hτ, hgS⟩ := hg.exists_val_eq_arrowSum (by simp)
  have hval := le_antisymm g.val_le_sum_posPart
    (hgS ▸ sum_posPart_le_arrowSum_excessFlowCapacity hS hσ hτ)
  exact ⟨g.toExcessFlow hb hval, g.toExcessFlow_mem H hlo hb hval hgH⟩

/-- **Feasibility of prescribed excess.** For `lo ≤ hi`, some assignment between `lo` and `hi`
has excess `b` exactly when `b` sums to zero and, for every vertex set `S`, the prescribed excess
on `S` plus the lower bound on the arrows leaving `S` is at most the upper bound on the arrows
entering `S`. -/
theorem nonempty_excessFlow_iff (hlohi : lo ≤ hi) :
    Nonempty (ExcessFlow lo hi b) ↔
      ∑ v, b v = 0 ∧ ∀ S : Finset V, ∑ v ∈ S, b v + arrowSum lo S Sᶜ ≤ arrowSum hi Sᶜ S := by
  refine ⟨fun ⟨f⟩ ↦ ⟨f.sum_eq_zero, f.sum_add_arrowSum_le⟩, fun ⟨hb, hS⟩ ↦ ?_⟩
  obtain ⟨f, -⟩ := exists_excessFlow_mem hlohi hb hS ⊤ (fun _ _ _ ↦ AddSubgroup.mem_top _)
    (fun _ _ _ ↦ AddSubgroup.mem_top _) fun _ ↦ AddSubgroup.mem_top _
  exact ⟨f⟩

/-- **Hoffman's circulation theorem.** For `lo ≤ hi`, some circulation lies between `lo` and `hi`
exactly when, for every vertex set `S`, the lower bound on the arrows entering `S` is at most the
upper bound on the arrows leaving `S`. -/
theorem nonempty_excessFlow_zero_iff (hlohi : lo ≤ hi) :
    Nonempty (ExcessFlow lo hi 0) ↔ ∀ S : Finset V, arrowSum lo Sᶜ S ≤ arrowSum hi S Sᶜ := by
  rw [nonempty_excessFlow_iff hlohi]
  simp only [Pi.zero_apply, sum_const_zero, zero_add, true_and]
  exact ⟨fun h S ↦ by simpa using h Sᶜ, fun h S ↦ by simpa using h Sᶜ⟩

/-- **Infeasibility certificates.** For `lo ≤ hi`, either some assignment between `lo` and `hi`
has excess `b`, or `b` does not sum to zero, or some vertex set `S` has prescribed excess plus the
lower bound on the arrows leaving `S` strictly larger than the upper bound on the arrows entering
`S`. -/
theorem nonempty_excessFlow_or_sum_ne_zero_or_exists_lt (hlohi : lo ≤ hi) :
    Nonempty (ExcessFlow lo hi b) ∨ ∑ v, b v ≠ 0 ∨
      ∃ S : Finset V, arrowSum hi Sᶜ S < ∑ v ∈ S, b v + arrowSum lo S Sᶜ := by
  rw [or_iff_not_imp_right, nonempty_excessFlow_iff hlohi]
  push Not
  exact id

/-- **Hoffman cuts.** For `lo ≤ hi`, either some circulation lies between `lo` and `hi`, or some
vertex set `S` has lower bound on the arrows entering `S` strictly larger than the upper bound on
the arrows leaving `S`. -/
theorem nonempty_excessFlow_zero_or_exists_lt (hlohi : lo ≤ hi) :
    Nonempty (ExcessFlow lo hi 0) ∨ ∃ S : Finset V, arrowSum hi S Sᶜ < arrowSum lo Sᶜ S := by
  rw [or_iff_not_imp_right, nonempty_excessFlow_zero_iff hlohi]
  push Not
  exact id

end LinearOrder

/-!
## Examples

On the vertices `false` and `true`, with one arrow for each ordered pair, give both loops the
bounds `[-2, -2]`, the arrow `false → true` the bounds `[-1, 2]`, which cross zero, and the arrow
`true → false` the negative bounds `[-3, -1]`. Hoffman's theorem certifies from the cut conditions
that some circulation lies between these bounds; the value `-1` on both arrows between distinct
vertices is one. No assignment between the bounds has excess `1` at `false` and `-1` at `true`:
the prescribed excess `1` on `{false}` plus the lower bound `-1` on the arrow leaving it exceeds
the upper bound `-1` on the arrow entering it.
-/

private def exLo : Assignment (fun _ _ : Bool ↦ Unit) ℤ := fun x y _ ↦
  if x = y then -2 else if x = false then -1 else -3

private def exHi : Assignment (fun _ _ : Bool ↦ Unit) ℤ := fun x y _ ↦
  if x = y then -2 else if x = false then 2 else -1

private theorem exLo_le_exHi : exLo ≤ exHi := by
  rintro (_ | _) (_ | _) _ <;> simp [exLo, exHi]

example : Nonempty (ExcessFlow exLo exHi 0) := by
  refine (nonempty_excessFlow_zero_iff exLo_le_exHi).2 fun S ↦ ?_
  by_cases h₀ : false ∈ S <;> by_cases h₁ : true ∈ S <;>
    simp [arrowSum_eq_sum_ite, exLo, exHi, h₀, h₁]

example : IsEmpty (ExcessFlow exLo exHi fun v ↦ if v = false then 1 else -1) :=
  ⟨fun f ↦ absurd (f.sum_add_arrowSum_le {false}) (by simp [arrowSum_eq_sum_ite, exLo, exHi])⟩

end TauCeti
