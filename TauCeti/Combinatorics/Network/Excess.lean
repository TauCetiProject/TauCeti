/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Action.Pointwise.Set.Basic
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Algebra.Group.Submonoid.BigOperators
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Tactic.Abel
public import TauCeti.Combinatorics.Network.Basic

/-!
# Arrow assignments and their excess

A directed network on a vertex type `V` is described by an explicit arrow family
`Q : V → V → Type*`, where `Q v w` is the type of arrows from `v` to `w`; parallel arrows,
antiparallel arrows and loops are all allowed. An *arrow assignment* with values in a type `K`
attaches a value of `K` to every arrow, with no sign or capacity constraint. Flows, pseudoflows,
bounded assignments and residual updates are all arrow assignments subject to further conditions,
and they share the additive calculus developed here. Arrow sums only need `K` to be an additive
commutative monoid, while excess needs an additive commutative group.

The *excess* of an assignment `f` at a vertex `v` is the total value on arrows entering `v` minus
the total value on arrows leaving `v`. With this sign convention a demand vertex has positive
excess and a supply vertex negative excess, and the value of an ordinary `s`–`t` flow is its excess
at the sink `t`. A loop at `v` enters and leaves `v`, so it contributes nothing to the excess.

## Main definitions

* `TauCeti.Assignment Q K`: arrow assignments of the arrow family `Q` with values in `K`.
* `TauCeti.arrowSum Q f S T`: the total value of `f` on the arrows from `S` to `T`.
* `TauCeti.excessAt Q f v`: the excess of `f` at `v`.
* `TauCeti.excessHom Q`: excess as an additive homomorphism `Assignment Q K →+ (V → K)`.
* `TauCeti.Assignment.single e q`: the assignment with value `q` on the arrow `e` and zero
  elsewhere.
* `TauCeti.IsCirculation f`: `f` has zero excess at every vertex.

## Main results

* `TauCeti.sum_excessAt_eq_arrowSum_sub`: the total excess on a vertex set `S` is the value
  entering `S` minus the value leaving `S`.
* `TauCeti.sum_excessAt`: the total excess over all vertices vanishes.
* `TauCeti.excessAt_single`: a single arrow from `x` to `y` carrying `q` has excess `q` at `y` and
  `-q` at `x`.
* `TauCeti.excessAt_source_eq_neg_sink`: an assignment conserved away from `s` and `t` has opposite
  excesses at `s` and `t`, and `TauCeti.excessAt_sink_eq_arrowSum_sub` computes the excess at `t`
  as the net value across any vertex set containing `s` but not `t`.
* `TauCeti.isCirculation_iff_mem_ker`: circulations form the kernel of `excessHom`, and
  `TauCeti.setOf_excessAt_eq_eq_vadd_ker` identifies every nonempty prescribed-excess fibre with a
  translate of that kernel.
* `TauCeti.map_excessAt` and `TauCeti.excessAt_comp_equiv`: excess commutes with additive maps of
  coefficients and with transport along an identification of arrow families.
* `TauCeti.IsCirculation.map` and `TauCeti.Assignment.map_mem_Icc`: additive changes of
  coefficients preserve circulations, and monotone ones preserve feasibility.

## Implementation notes

The arrow family is an explicit argument rather than a `Quiver` instance, so that several arrow
families can coexist on one vertex type, and so that instance search finds `Fintype (Q v w)`
directly. An assignment binds its endpoints strict-implicitly, as `∀ ⦃v w⦄, Q v w → K`: it is
applied to an arrow as `f e`, while `f` on its own is not specialised to unknown endpoints.
-/

public section

namespace TauCeti

open Finset Pointwise

universe u u' v v' w

variable {V : Type u} (Q : V → V → Type v) (K : Type w)

variable {Q K}

/-! ### Single-arrow assignments -/

section Single

variable [Zero K]

open Classical in
/-- The assignment with value `q` on the arrow `e` and zero on every other arrow. -/
noncomputable def Assignment.single {x y : V} (e : Q x y) (q : K) : Assignment Q K :=
  fun a b e' ↦ if (⟨a, b, e'⟩ : Σ a b, Q a b) = ⟨x, y, e⟩ then q else 0

open Classical in
theorem Assignment.single_apply {x y a b : V} (e : Q x y) (q : K) (e' : Q a b) :
    Assignment.single e q e' = if (⟨a, b, e'⟩ : Σ a b, Q a b) = ⟨x, y, e⟩ then q else 0 :=
  (rfl)

@[simp]
theorem Assignment.single_apply_self {x y : V} (e : Q x y) (q : K) :
    Assignment.single e q e = q := by
  simp [Assignment.single]

theorem Assignment.single_apply_of_ne {x y a b : V} (e : Q x y) (q : K) {e' : Q a b}
    (h : (⟨a, b, e'⟩ : Σ a b, Q a b) ≠ ⟨x, y, e⟩) : Assignment.single e q e' = 0 := by
  simp [Assignment.single, h]

end Single

section AddCommMonoid

variable [AddCommMonoid K] [∀ v w, Fintype (Q v w)]

/-- The total value of the assignment `f` on the arrows from a vertex of `S` to a vertex of `T`.
Every arrow is counted once, so parallel arrows add; when `S` and `T` meet, loops at their common
vertices are counted. -/
def arrowSum (f : Assignment Q K) (S T : Finset V) : K :=
  ∑ v ∈ S, ∑ w ∈ T, ∑ e : Q v w, f e

theorem arrowSum_def (f : Assignment Q K) (S T : Finset V) :
    arrowSum f S T = ∑ v ∈ S, ∑ w ∈ T, ∑ e : Q v w, f e :=
  (rfl)

/-- An arrow sum as a sum over every arrow, with an indicator for its endpoints belonging to the
specified sets. -/
theorem arrowSum_eq_sum_ite [Fintype V] [DecidableEq V] (f : Assignment Q K)
    (S T : Finset V) :
    arrowSum f S T = ∑ v, ∑ w, ∑ e : Q v w, if v ∈ S ∧ w ∈ T then f e else 0 := by
  simp [arrowSum_def, ite_and]

/-- The arrow sums of an assignment with values in an additive submonoid lie in the submonoid. -/
theorem arrowSum_mem {M : Type*} [SetLike M K] [AddSubmonoidClass M K] {H : M}
    {f : Assignment Q K} (hf : ∀ ⦃v w⦄ (e : Q v w), f e ∈ H) (S T : Finset V) :
    arrowSum f S T ∈ H :=
  sum_mem fun _ _ ↦ sum_mem fun _ _ ↦ sum_mem fun e _ ↦ hf e

@[simp]
theorem arrowSum_zero (S T : Finset V) : arrowSum (0 : Assignment Q K) S T = 0 := by
  simp [arrowSum_def]

@[simp]
theorem arrowSum_add (f g : Assignment Q K) (S T : Finset V) :
    arrowSum (f + g) S T = arrowSum f S T + arrowSum g S T := by
  simp [arrowSum_def, sum_add_distrib]

@[simp]
theorem arrowSum_empty_left (f : Assignment Q K) (T : Finset V) : arrowSum f ∅ T = 0 := by
  simp [arrowSum_def]

@[simp]
theorem arrowSum_empty_right (f : Assignment Q K) (S : Finset V) : arrowSum f S ∅ = 0 := by
  simp [arrowSum_def]

theorem arrowSum_union_left [DecidableEq V] (f : Assignment Q K) {S S' : Finset V}
    (h : Disjoint S S') (T : Finset V) :
    arrowSum f (S ∪ S') T = arrowSum f S T + arrowSum f S' T := by
  simp only [arrowSum_def, sum_union h]

theorem arrowSum_union_right [DecidableEq V] (f : Assignment Q K) (S : Finset V) {T T' : Finset V}
    (h : Disjoint T T') :
    arrowSum f S (T ∪ T') = arrowSum f S T + arrowSum f S T' := by
  simp only [arrowSum_def, sum_union h, sum_add_distrib]

/-- Mapping the values of an assignment along an additive monoid homomorphism commutes with
summing them over the arrows between two vertex sets. -/
theorem map_arrowSum {L F : Type*} [AddCommMonoid L] [FunLike F K L] [AddMonoidHomClass F K L]
    (φ : F) (f : Assignment Q K) (S T : Finset V) :
    φ (arrowSum f S T) = arrowSum (f.map φ) S T := by
  simp [arrowSum_def, map_sum]

/-- Summing over the arrows between two vertex sets is monotone in the assignment. -/
@[gcongr]
theorem arrowSum_mono [Preorder K] [AddLeftMono K] {f g : Assignment Q K} (h : f ≤ g)
    (S T : Finset V) : arrowSum f S T ≤ arrowSum g S T :=
  sum_le_sum fun v _ ↦ sum_le_sum fun w _ ↦ sum_le_sum fun e _ ↦ h v w e

/-- A nonnegative assignment has zero total value on the arrows from `S` to `T` exactly when it
vanishes on each of these arrows. -/
theorem arrowSum_eq_zero_iff_of_nonneg [PartialOrder K] [IsOrderedAddMonoid K] {f : Assignment Q K}
    (hf : 0 ≤ f) {S T : Finset V} :
    arrowSum f S T = 0 ↔ ∀ v ∈ S, ∀ w ∈ T, ∀ e : Q v w, f e = 0 := by
  have h₃ (v w : V) : 0 ≤ ∑ e : Q v w, f e := sum_nonneg fun e _ ↦ hf v w e
  have h₂ (v : V) : 0 ≤ ∑ w ∈ T, ∑ e : Q v w, f e := sum_nonneg fun w _ ↦ h₃ v w
  simp only [arrowSum_def, sum_eq_zero_iff_of_nonneg fun v _ ↦ h₂ v,
    sum_eq_zero_iff_of_nonneg fun w _ ↦ h₃ _ w, sum_eq_zero_iff_of_nonneg fun e _ ↦ hf _ _ e,
    mem_univ, true_implies]

section Nonneg

variable [PartialOrder K] [IsOrderedAddMonoid K] {f : Assignment Q K}

/-- A nonnegative assignment has nonnegative total value on the arrows from `S` to `T`. -/
theorem arrowSum_nonneg (hf : 0 ≤ f) (S T : Finset V) : 0 ≤ arrowSum f S T :=
  sum_nonneg fun _ _ ↦ sum_nonneg fun _ _ ↦ sum_nonneg fun e _ ↦ hf _ _ e

/-- For a nonnegative assignment, the arrow sum is monotone in the set of source vertices. -/
theorem arrowSum_mono_left (hf : 0 ≤ f) {S S' : Finset V} (h : S ⊆ S') (T : Finset V) :
    arrowSum f S T ≤ arrowSum f S' T :=
  sum_le_sum_of_subset_of_nonneg h fun v _ _ ↦ sum_nonneg fun w _ ↦ sum_nonneg fun e _ ↦ hf v w e

/-- For a nonnegative assignment, the arrow sum is monotone in the set of target vertices. -/
theorem arrowSum_mono_right (hf : 0 ≤ f) (S : Finset V) {T T' : Finset V} (h : T ⊆ T') :
    arrowSum f S T ≤ arrowSum f S T' :=
  sum_le_sum fun v _ ↦ sum_le_sum_of_subset_of_nonneg h fun w _ _ ↦ sum_nonneg fun e _ ↦ hf v w e

/-- For a nonnegative assignment, the arrow sum is subadditive in the set of source vertices. -/
theorem arrowSum_union_left_le [DecidableEq V] (hf : 0 ≤ f) (S S' T : Finset V) :
    arrowSum f (S ∪ S') T ≤ arrowSum f S T + arrowSum f S' T := by
  rw [← union_sdiff_self_eq_union, arrowSum_union_left f disjoint_sdiff]
  grw [arrowSum_mono_left hf sdiff_subset]

/-- For a nonnegative assignment, the arrow sum is subadditive in the set of target vertices. -/
theorem arrowSum_union_right_le [DecidableEq V] (hf : 0 ≤ f) (S T T' : Finset V) :
    arrowSum f S (T ∪ T') ≤ arrowSum f S T + arrowSum f S T' := by
  rw [← union_sdiff_self_eq_union, arrowSum_union_right f S disjoint_sdiff]
  grw [arrowSum_mono_right hf S sdiff_subset]

/-- Adding the vertices of `X` to a vertex set `S` increases the nonnegative value leaving it by
at most the total value leaving `X`. -/
theorem arrowSum_union_compl_le [Fintype V] [DecidableEq V] (hf : 0 ≤ f) (S X : Finset V) :
    arrowSum f (S ∪ X) (S ∪ X)ᶜ ≤ arrowSum f S Sᶜ + arrowSum f X univ := by
  grw [arrowSum_union_left_le hf, arrowSum_mono_right hf S (compl_subset_compl.mpr
    subset_union_left), arrowSum_mono_right hf X (subset_univ _)]

/-- Removing the vertices of `Y` from a vertex set `S` increases the nonnegative value leaving it
by at most the total value entering `Y`. -/
theorem arrowSum_sdiff_compl_le [Fintype V] [DecidableEq V] (hf : 0 ≤ f) (S Y : Finset V) :
    arrowSum f (S \ Y) (S \ Y)ᶜ ≤ arrowSum f S Sᶜ + arrowSum f univ Y := by
  have h : (S \ Y)ᶜ = Sᶜ ∪ Y := by
    ext v
    simp [imp_iff_not_or]
  rw [h]
  grw [arrowSum_union_right_le hf, arrowSum_mono_left hf sdiff_subset,
    arrowSum_mono_left hf (subset_univ (S \ Y))]

/-- The value of a nonnegative assignment on a single arrow from `S` to `T` is at most its total
value on the arrows from `S` to `T`. -/
theorem apply_le_arrowSum (hf : 0 ≤ f) {S T : Finset V} {v w : V} (hv : v ∈ S) (hw : w ∈ T)
    (e : Q v w) : f e ≤ arrowSum f S T :=
  calc f e ≤ ∑ e : Q v w, f e := single_le_sum (fun e _ ↦ hf _ _ e) (mem_univ e)
    _ ≤ ∑ w ∈ T, ∑ e : Q v w, f e :=
      single_le_sum (f := fun w ↦ ∑ e : Q v w, f e) (fun _ _ ↦ sum_nonneg fun e _ ↦ hf _ _ e) hw
    _ ≤ arrowSum f S T :=
      single_le_sum (f := fun v ↦ ∑ w ∈ T, ∑ e : Q v w, f e)
        (fun _ _ ↦ sum_nonneg fun _ _ ↦ sum_nonneg fun e _ ↦ hf _ _ e) hv

end Nonneg

/-- The total value entering `v` for a single arrow from `x` to `y` is `q` when `v = y` and
zero otherwise. -/
theorem sum_sum_single_in [Fintype V] [DecidableEq V] {x y : V} (e : Q x y) (q : K) (v : V) :
    ∑ w, ∑ e' : Q w v, Assignment.single e q e' = if v = y then q else 0 := by
  split_ifs with hv
  · subst hv
    rw [Fintype.sum_eq_single x fun w hw ↦ sum_eq_zero fun e' _ ↦
        Assignment.single_apply_of_ne e q fun h ↦ hw (congrArg Sigma.fst h),
      Fintype.sum_eq_single e fun e' he' ↦ Assignment.single_apply_of_ne e q (by simpa using he'),
      Assignment.single_apply_self]
  · exact sum_eq_zero fun w _ ↦ sum_eq_zero fun e' _ ↦
      Assignment.single_apply_of_ne e q fun h ↦ hv (congrArg (fun a ↦ a.2.1) h)

/-- The total value leaving `v` for a single arrow from `x` to `y` is `q` when `v = x` and
zero otherwise. -/
theorem sum_sum_single_out [Fintype V] [DecidableEq V] {x y : V} (e : Q x y) (q : K) (v : V) :
    ∑ w, ∑ e' : Q v w, Assignment.single e q e' = if v = x then q else 0 := by
  split_ifs with hv
  · subst hv
    rw [Fintype.sum_eq_single y fun w hw ↦ sum_eq_zero fun e' _ ↦
        Assignment.single_apply_of_ne e q fun h ↦ hw (congrArg (fun a ↦ a.2.1) h),
      Fintype.sum_eq_single e fun e' he' ↦ Assignment.single_apply_of_ne e q (by simpa using he'),
      Assignment.single_apply_self]
  · exact sum_eq_zero fun w _ ↦ sum_eq_zero fun e' _ ↦
      Assignment.single_apply_of_ne e q fun h ↦ hv (congrArg Sigma.fst h)

end AddCommMonoid

section SubtractionCommMonoid

variable [SubtractionCommMonoid K] [∀ v w, Fintype (Q v w)]

@[simp]
theorem arrowSum_neg (f : Assignment Q K) (S T : Finset V) :
    arrowSum (-f) S T = -arrowSum f S T := by
  simp [arrowSum_def]

@[simp]
theorem arrowSum_sub (f g : Assignment Q K) (S T : Finset V) :
    arrowSum (f - g) S T = arrowSum f S T - arrowSum g S T := by
  simp [arrowSum_def, sum_sub_distrib]

end SubtractionCommMonoid

section AddCommGroup

variable [AddCommGroup K] [∀ v w, Fintype (Q v w)] [Fintype V]

/-- The *excess* of the assignment `f` at the vertex `v`: the total value on arrows entering `v`
minus the total value on arrows leaving `v`. Loops at `v` cancel. -/
def excessAt (f : Assignment Q K) (v : V) : K :=
  ∑ w, ∑ e : Q w v, f e - ∑ w, ∑ e : Q v w, f e

theorem excessAt_def (f : Assignment Q K) (v : V) :
    excessAt f v = ∑ w, ∑ e : Q w v, f e - ∑ w, ∑ e : Q v w, f e :=
  (rfl)

/-- The excess of an assignment with values in an additive subgroup lies in the subgroup. -/
theorem excessAt_mem {M : Type*} [SetLike M K] [AddSubgroupClass M K] {H : M}
    {f : Assignment Q K} (hf : ∀ ⦃v w⦄ (e : Q v w), f e ∈ H) (v : V) : excessAt f v ∈ H :=
  sub_mem (sum_mem fun _ _ ↦ sum_mem fun e _ ↦ hf e) (sum_mem fun _ _ ↦ sum_mem fun e _ ↦ hf e)

/-- The excess at `v` is the value entering `{v}` minus the value leaving `{v}`. -/
theorem excessAt_eq_arrowSum_sub (f : Assignment Q K) (v : V) :
    excessAt f v = arrowSum f univ {v} - arrowSum f {v} univ := by
  simp [excessAt_def, arrowSum_def]

@[simp]
theorem excessAt_zero (v : V) : excessAt (0 : Assignment Q K) v = 0 := by
  simp [excessAt_def]

@[simp]
theorem excessAt_add (f g : Assignment Q K) (v : V) :
    excessAt (f + g) v = excessAt f v + excessAt g v := by
  simp only [excessAt_def, Pi.add_apply, sum_add_distrib]
  abel

variable (Q K) in
/-- Excess as an additive homomorphism from arrow assignments to vertex functions. -/
def excessHom : Assignment Q K →+ (V → K) where
  toFun f := excessAt f
  map_zero' := funext excessAt_zero
  map_add' f g := funext (excessAt_add f g)

@[simp]
theorem excessHom_apply (f : Assignment Q K) (v : V) : excessHom Q K f v = excessAt f v :=
  (rfl)

@[simp]
theorem excessAt_neg (f : Assignment Q K) (v : V) : excessAt (-f) v = -excessAt f v :=
  congrFun (map_neg (excessHom Q K) f) v

@[simp]
theorem excessAt_sub (f g : Assignment Q K) (v : V) :
    excessAt (f - g) v = excessAt f v - excessAt g v :=
  congrFun (map_sub (excessHom Q K) f g) v

/-- A nonnegative assignment that vanishes on every arrow entering `v` has nonpositive excess at
`v`. -/
theorem excessAt_nonpos_of_nonneg_of_forall_in_eq_zero [PartialOrder K] [IsOrderedAddMonoid K]
    {f : Assignment Q K} (hf : 0 ≤ f) {v : V} (h : ∀ w (e : Q w v), f e = 0) :
    excessAt f v ≤ 0 := by
  simp only [excessAt_def, h, sum_const_zero, zero_sub, neg_nonpos]
  exact sum_nonneg fun w _ ↦ sum_nonneg fun e _ ↦ hf _ _ e

/-- A nonnegative assignment that vanishes on every arrow leaving `v` has nonnegative excess at
`v`. -/
theorem excessAt_nonneg_of_nonneg_of_forall_out_eq_zero [PartialOrder K] [IsOrderedAddMonoid K]
    {f : Assignment Q K} (hf : 0 ≤ f) {v : V} (h : ∀ w (e : Q v w), f e = 0) :
    0 ≤ excessAt f v := by
  simp only [excessAt_def, h, sum_const_zero, sub_zero]
  exact sum_nonneg fun w _ ↦ sum_nonneg fun e _ ↦ hf _ _ e

/-- An assignment between zero and `cap` has excess at `v` at most the total capacity of the arrows
entering `v`. -/
theorem excessAt_le_of_mem_Icc [PartialOrder K] [IsOrderedAddMonoid K] {f cap : Assignment Q K}
    (hf : f ∈ Set.Icc 0 cap) (v : V) : excessAt f v ≤ ∑ w, ∑ e : Q w v, cap e :=
  calc excessAt f v ≤ ∑ w, ∑ e : Q w v, f e :=
        sub_le_self _ (sum_nonneg fun _ _ ↦ sum_nonneg fun e _ ↦ hf.1 _ _ e)
    _ ≤ ∑ w, ∑ e : Q w v, cap e := sum_le_sum fun _ _ ↦ sum_le_sum fun e _ ↦ hf.2 _ _ e

/-- An assignment between zero and `cap` has minus its excess at `v` at most the total capacity of
the arrows leaving `v`. -/
theorem neg_excessAt_le_of_mem_Icc [PartialOrder K] [IsOrderedAddMonoid K]
    {f cap : Assignment Q K} (hf : f ∈ Set.Icc 0 cap) (v : V) :
    -excessAt f v ≤ ∑ w, ∑ e : Q v w, cap e :=
  calc -excessAt f v ≤ ∑ w, ∑ e : Q v w, f e := by
        rw [excessAt_def, neg_sub]
        exact sub_le_self _ (sum_nonneg fun _ _ ↦ sum_nonneg fun e _ ↦ hf.1 _ _ e)
    _ ≤ ∑ w, ∑ e : Q v w, cap e := sum_le_sum fun _ _ ↦ sum_le_sum fun e _ ↦ hf.2 _ _ e

/-- **Excess on a vertex set.** The total excess of `f` on `S` is the value on arrows entering `S`
from its complement minus the value on arrows leaving `S` for its complement; arrows with both ends
in `S` cancel. -/
theorem sum_excessAt_eq_arrowSum_sub [DecidableEq V] (f : Assignment Q K) (S : Finset V) :
    ∑ v ∈ S, excessAt f v = arrowSum f Sᶜ S - arrowSum f S Sᶜ := by
  have hin : ∀ v, ∑ w, ∑ e : Q w v, f e =
      ∑ w ∈ S, ∑ e : Q w v, f e + ∑ w ∈ Sᶜ, ∑ e : Q w v, f e :=
    fun v ↦ (sum_add_sum_compl S _).symm
  have hout : ∀ v, ∑ w, ∑ e : Q v w, f e =
      ∑ w ∈ S, ∑ e : Q v w, f e + ∑ w ∈ Sᶜ, ∑ e : Q v w, f e :=
    fun v ↦ (sum_add_sum_compl S _).symm
  simp only [excessAt_def, hin, hout, arrowSum_def, sum_sub_distrib, sum_add_distrib]
  rw [sum_comm (s := S) (t := S), sum_comm (s := S) (t := Sᶜ)]
  abel

/-- The total excess of an assignment over all vertices is zero: every arrow enters exactly one
vertex and leaves exactly one vertex. -/
@[simp]
theorem sum_excessAt (f : Assignment Q K) : ∑ v, excessAt f v = 0 := by
  simp only [excessAt_def, sum_sub_distrib]
  rw [sum_comm, sub_self]

/-- If an assignment is conserved at every vertex other than `s` and `t`, then its excesses at `s`
and `t` are opposite. In particular a flow loses at its source exactly what it delivers to its
sink. -/
theorem excessAt_source_eq_neg_sink (f : Assignment Q K) {s t : V}
    (hconserve : ∀ v, v ≠ s → v ≠ t → excessAt f v = 0) :
    excessAt f s = -excessAt f t := by
  obtain rfl | hst := eq_or_ne s t
  · -- when `s = t`, the excess at `s` is the total excess, which vanishes
    have hs : excessAt f s = 0 := by
      rw [← sum_excessAt f, Fintype.sum_eq_single s fun v hv ↦ hconserve v hv hv]
    rw [hs, neg_zero]
  · rw [eq_neg_iff_add_eq_zero, ← sum_excessAt f,
      Fintype.sum_eq_add s t hst fun v hv ↦ hconserve v hv.1 hv.2]

/-- **Value across a cut.** If an assignment is conserved at every vertex other than `s` and `t`,
then for every vertex set `S` containing `s` but not `t`, the excess at `t` is the value on arrows
leaving `S` minus the value on arrows entering `S`. -/
theorem excessAt_sink_eq_arrowSum_sub [DecidableEq V] (f : Assignment Q K) {s t : V}
    (hconserve : ∀ v, v ≠ s → v ≠ t → excessAt f v = 0) {S : Finset V} (hs : s ∈ S)
    (ht : t ∉ S) : excessAt f t = arrowSum f S Sᶜ - arrowSum f Sᶜ S := by
  have hsum : ∑ v ∈ S, excessAt f v = excessAt f s :=
    sum_eq_single_of_mem s hs fun v hv hvs ↦ hconserve v hvs (ne_of_mem_of_not_mem hv ht)
  rw [← neg_sub, ← sum_excessAt_eq_arrowSum_sub, hsum, excessAt_source_eq_neg_sink f hconserve,
    neg_neg]

/-- Mapping the values of an assignment along an additive group homomorphism commutes with
taking excess. -/
theorem map_excessAt {L F : Type*} [AddCommGroup L] [FunLike F K L] [AddMonoidHomClass F K L]
    (φ : F) (f : Assignment Q K) (v : V) :
    φ (excessAt f v) = excessAt (f.map φ) v := by
  simp [excessAt_def, map_sum]

/-- Excess is invariant under transport along an identification `σ` of the vertices and
identifications `τ` of the corresponding arrow types: pulling an assignment back along `τ` and
taking excess at `v` agrees with taking excess at `σ v`. -/
theorem excessAt_comp_equiv {W : Type u'} [Fintype W] {R : W → W → Type v'}
    [∀ a b, Fintype (R a b)] (σ : V ≃ W) (τ : ∀ v w, Q v w ≃ R (σ v) (σ w))
    (g : Assignment R K) (v : V) :
    excessAt (fun ⦃a b⦄ (e : Q a b) ↦ g (τ a b e)) v = excessAt g (σ v) := by
  simp only [excessAt_def, Equiv.sum_comp (τ _ _) (fun e ↦ g e)]
  rw [Equiv.sum_comp σ (fun w ↦ ∑ e : R w (σ v), g e),
    Equiv.sum_comp σ (fun w ↦ ∑ e : R (σ v) w, g e)]

/-- **Excess of a single arrow.** The assignment with value `q` on an arrow from `x` to `y` and
zero elsewhere has excess `q` at `y` and `-q` at `x`; for a loop the two cancel. -/
@[simp]
theorem excessAt_single [DecidableEq V] {x y : V} (e : Q x y) (q : K) (v : V) :
    excessAt (Assignment.single e q) v = (if v = y then q else 0) - (if v = x then q else 0) := by
  rw [excessAt_def, sum_sum_single_in, sum_sum_single_out]

/-! ### Circulations and prescribed excess -/

/-- A (signed) *circulation* is an arrow assignment conserved at every vertex: its excess vanishes
everywhere. No sign or capacity constraint is imposed. -/
def IsCirculation (f : Assignment Q K) : Prop :=
  ∀ v, excessAt f v = 0

theorem isCirculation_iff (f : Assignment Q K) : IsCirculation f ↔ ∀ v, excessAt f v = 0 :=
  Iff.rfl

/-- Circulations are exactly the kernel of the excess homomorphism. -/
theorem isCirculation_iff_mem_ker (f : Assignment Q K) :
    IsCirculation f ↔ f ∈ (excessHom Q K).ker := by
  rw [isCirculation_iff, AddMonoidHom.mem_ker, funext_iff]
  rfl

@[simp]
theorem isCirculation_zero : IsCirculation (0 : Assignment Q K) :=
  fun _ ↦ excessAt_zero _

theorem IsCirculation.add {f g : Assignment Q K} (hf : IsCirculation f)
    (hg : IsCirculation g) : IsCirculation (f + g) :=
  fun v ↦ by rw [excessAt_add, hf v, hg v, add_zero]

theorem IsCirculation.neg {f : Assignment Q K} (hf : IsCirculation f) :
    IsCirculation (-f) :=
  fun v ↦ by rw [excessAt_neg, hf v, neg_zero]

theorem IsCirculation.sub {f g : Assignment Q K} (hf : IsCirculation f)
    (hg : IsCirculation g) : IsCirculation (f - g) :=
  fun v ↦ by rw [excessAt_sub, hf v, hg v, sub_zero]

/-- A circulation carries the same total value into any vertex set `S` as out of it. -/
theorem IsCirculation.arrowSum_compl_eq [DecidableEq V] {f : Assignment Q K}
    (hf : IsCirculation f) (S : Finset V) : arrowSum f Sᶜ S = arrowSum f S Sᶜ := by
  rw [← sub_eq_zero, ← sum_excessAt_eq_arrowSum_sub, sum_eq_zero fun v _ ↦ hf v]

/-- Given one assignment `f₀` with excess `b`, an assignment has excess `b` exactly when it differs
from `f₀` by a circulation. -/
theorem excessAt_eq_iff_isCirculation_sub {f₀ : Assignment Q K} {b : V → K}
    (hf₀ : ∀ v, excessAt f₀ v = b v) (f : Assignment Q K) :
    (∀ v, excessAt f v = b v) ↔ IsCirculation (f - f₀) := by
  simp only [isCirculation_iff, excessAt_sub, hf₀, sub_eq_zero]

/-- Every nonempty prescribed-excess fibre is a translate of the circulations: if `f₀` has excess
`b`, the assignments with excess `b` are exactly `f₀ + c` for `c` in the kernel of `excessHom`. -/
theorem setOf_excessAt_eq_eq_vadd_ker {f₀ : Assignment Q K} {b : V → K}
    (hf₀ : ∀ v, excessAt f₀ v = b v) :
    {f : Assignment Q K | ∀ v, excessAt f v = b v} =
      f₀ +ᵥ ((excessHom Q K).ker : Set (Assignment Q K)) := by
  ext f
  refine (excessAt_eq_iff_isCirculation_sub hf₀ f).trans ?_
  rw [isCirculation_iff_mem_ker]
  constructor
  · exact fun h ↦ ⟨f - f₀, h, add_sub_cancel f₀ f⟩
  · rintro ⟨c, hc, rfl⟩
    simpa using hc

end AddCommGroup

/-! ### Change of coefficients -/

namespace Assignment

/-- Subtracting a subgroup-valued reference preserves membership on each arrow. -/
theorem sub_apply_mem_iff [AddGroup K] {M : Type*} [SetLike M K]
    [AddSubgroupClass M K] {H : M} {f h : Assignment Q K} {x y : V} (e : Q x y)
    (hh : h e ∈ H) : (f - h) e ∈ H ↔ f e ∈ H := by
  simpa only [Pi.sub_apply, sub_eq_add_neg] using
    add_mem_cancel_right (y := f e) (neg_mem hh)

section Algebra

variable {L F : Type*} [FunLike F K L]

@[simp]
theorem map_zero [Zero K] [Zero L] [ZeroHomClass F K L] (φ : F) :
    (0 : Assignment Q K).map φ = 0 := by
  funext _ _ e
  exact (map_apply _ _ e).trans (_root_.map_zero φ)

@[simp]
theorem map_add [Add K] [Add L] [AddHomClass F K L] (φ : F) (f g : Assignment Q K) :
    (f + g).map φ = f.map φ + g.map φ := by
  funext _ _ e
  simp

@[simp]
theorem map_neg [AddGroup K] [AddGroup L] [AddMonoidHomClass F K L] (φ : F)
    (f : Assignment Q K) : (-f).map φ = -f.map φ := by
  funext _ _ e
  simp

@[simp]
theorem map_sub [AddGroup K] [AddGroup L] [AddMonoidHomClass F K L] (φ : F)
    (f g : Assignment Q K) : (f - g).map φ = f.map φ - g.map φ := by
  funext _ _ e
  simp

end Algebra

section Order

variable {L : Type*} [Preorder K] [Preorder L] {φ : K → L}

theorem map_mono (hφ : Monotone φ) {f g : Assignment Q K} (h : f ≤ g) : f.map φ ≤ g.map φ := by
  intro x y e
  simpa only [map_apply] using hφ (h x y e)

/-- A monotone coefficient map preserves feasibility, with the bounds mapped as well. -/
theorem map_mem_Icc (hφ : Monotone φ) {lo hi f : Assignment Q K} (hf : f ∈ Set.Icc lo hi) :
    f.map φ ∈ Set.Icc (lo.map φ) (hi.map φ) :=
  ⟨map_mono hφ hf.1, map_mono hφ hf.2⟩

end Order

end Assignment

/-- A circulation stays a circulation after an additive change of coefficients. -/
theorem IsCirculation.map [Fintype V] [∀ v w, Fintype (Q v w)] [AddCommGroup K] {L F : Type*}
    [AddCommGroup L] [FunLike F K L] [AddMonoidHomClass F K L] {f : Assignment Q K}
    (hf : IsCirculation f) (φ : F) : IsCirculation (f.map φ) :=
  (isCirculation_iff _).2 fun v ↦ by
    rw [← map_excessAt, (isCirculation_iff f).1 hf v, _root_.map_zero]

namespace Network

/-- Excess of an assignment on a network's arrow family. The network's bounds play no role. -/
abbrev excessAt {C : Type*} [LE C] (N : Network C V) [Fintype V]
    [∀ x y, Fintype (N.Hom x y)] {K : Type w} [AddCommGroup K]
    (f : N.Assignment K) (x : V) : K :=
  TauCeti.excessAt f x

/-- The additive excess map on a network's arrow family. -/
abbrev excessHom {C : Type*} [LE C] (N : Network C V) [Fintype V]
    [∀ x y, Fintype (N.Hom x y)] {K : Type w} [AddCommGroup K] :
    N.Assignment K →+ (V → K) :=
  TauCeti.excessHom N.Hom K

end Network

end TauCeti
