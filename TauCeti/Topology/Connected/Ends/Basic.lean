/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.Topology.Compactness.SigmaCompact
public import Mathlib.Topology.Instances.Real.Lemmas
public import TauCeti.Topology.ConnectedComponents
import TauCeti.Topology.Compactness.Compact
import TauCeti.Topology.FilledHull

/-!
# Ends of a topological space

An *end* of a space `X` is a way of going to infinity in `X`. It is recorded by a decreasing
sequence `U₀ ⊇ U₁ ⊇ ⋯` in which each `Uᵢ` is a connected component of the complement of a compact
set and which is eventually disjoint from every compact set; two such sequences describe the same
end when each set of either sequence contains some set of the other. For instance `ℝ` has two
ends and a compact space has none.

Along a monotone sequence `K₀ ⊆ K₁ ⊆ ⋯` of compact sets that is cofinal among all compact sets, for
instance a `CompactExhaustion`, the ends are the inverse limit of the sets `π₀(X \ Kₙ)` of
complementary components, which is the classical description of ends.

In a preconnected, locally connected, locally compact Hausdorff space, every compact set lies in
the interior of a compact set whose complement has finitely many components, none of them with
compact closure (`TauCeti.exists_isCompact_finite_connectedComponents_compl`, in
`TauCeti/Topology/FilledHull.lean`). If the space is moreover σ-compact, each complementary
component with noncompact closure contains an end. A space is *connected at infinity* when, far
enough out, any two points are joined by a path avoiding a prescribed compact set. For
preconnected, locally path-connected, σ-compact, locally compact Hausdorff spaces, this says
exactly that there is at most one end, and exactly one when the space is noncompact. These
hypotheses hold for instance for connected second-countable manifolds and for connected locally
finite CW complexes.

Ends are the basic invariant at infinity of a noncompact space. They appear together with simple
connectivity at infinity (`TauCeti.SimplyConnectedAtInfinity`) in the proper homotopy theory of
noncompact complexes and manifolds.

## Main definitions

* `TauCeti.EndSequence X`: decreasing sequences of components of complements of compact sets
  which are eventually disjoint from every compact set.
* `TauCeti.EndSequence.component`: for a compact `L`, the component of `X \ L` that eventually
  contains such a sequence.
* `TauCeti.EndComponents X`: the ends of `X`, sequences up to mutual cofinal containment.
* `TauCeti.componentComplFunctor`: the inverse system `n ↦ π₀(X \ Kₙ)` of complementary
  components along a monotone sequence of sets.
* `TauCeti.ConnectedAtInfinity`: outside a large compact set, any two points are joined by a path
  avoiding a given compact set.

## Main results

* `TauCeti.EndSequence.equiv_iff_forall_exists_subset`: containment of each set of one sequence
  in a set of the other already implies the converse.
* `TauCeti.EndSequence.equiv_iff_forall_component_eq`: two sequences define the same end exactly
  when they eventually lie in the same component of `X \ L` for every compact `L`.
* `TauCeti.endComponentsEquivSections`: along a cofinal monotone sequence of compact sets, the
  ends are the inverse limit of the complementary components;
  `CompactExhaustion.endComponentsEquivSections` specializes this to a compact exhaustion.
* `TauCeti.isEmpty_endComponents`: a compact space has no ends.
* `TauCeti.exists_endSequence_subset_connectedComponentIn`: in a σ-compact, locally compact
  Hausdorff, locally connected space with no compact component, every complementary component of a
  compact set with noncompact closure contains an end sequence; in particular such a nonempty space
  has an end (`TauCeti.nonempty_endComponents`).
* `TauCeti.ConnectedAtInfinity.subsingleton_endComponents`: a space connected at infinity has at
  most one end. Conversely, `TauCeti.connectedAtInfinity_iff_subsingleton_endComponents` and
  `TauCeti.connectedAtInfinity_iff_natCard_endComponents_eq_one`: a preconnected, locally
  path-connected, σ-compact, locally compact Hausdorff space is connected at infinity exactly when
  it has at most one end, and, if it is noncompact, exactly when it has one end.
* `TauCeti.natCard_endComponents_real`: the real line has exactly two ends, at `+∞` and `-∞`.

## References

* H. Freudenthal, *Über die Enden topologischer Räume und Gruppen*, Math. Z. 33 (1931), 692–713.
* F. T. Farrell, L. R. Taylor, J. B. Wagoner, *The Whitehead theorem in the proper category*,
  Compositio Math. 27 (1973), 1–23, §1.
-/

public section

open CategoryTheory Filter Set

universe u

namespace TauCeti

variable {X : Type u} [TopologicalSpace X]

variable (X) in
/-- A sequence running out to an end of `X`: a decreasing sequence `U₀ ⊇ U₁ ⊇ ⋯` in which each
`Uₙ` is a connected component of the complement of some compact set, and which is eventually
disjoint from every compact set. -/
structure EndSequence where
  /-- The `n`-th set of the sequence. -/
  toFun : ℕ → Set X
  /-- Each set of the sequence is a connected component of the complement of a compact set. -/
  exists_eq_connectedComponentIn' :
    ∀ n, ∃ K : Set X, IsCompact K ∧ ∃ x ∉ K, toFun n = connectedComponentIn Kᶜ x
  /-- The sequence is decreasing. -/
  antitone' : Antitone toFun
  /-- The sequence is eventually disjoint from every compact set. -/
  eventually_disjoint' : ∀ K : Set X, IsCompact K → ∀ᶠ n in atTop, Disjoint (toFun n) K

namespace EndSequence

instance : FunLike (EndSequence X) ℕ (Set X) where
  coe := toFun
  coe_injective | ⟨_, _, _, _⟩, ⟨_, _, _, _⟩, rfl => rfl

variable (U V : EndSequence X)

@[ext]
theorem ext {U V : EndSequence X} (h : ∀ n, U n = V n) : U = V :=
  DFunLike.ext _ _ h

@[simp]
theorem toFun_eq_coe : U.toFun = U :=
  rfl

/-- Each set of an end sequence is a connected component of the complement of a compact set. -/
theorem exists_eq_connectedComponentIn (n : ℕ) :
    ∃ K : Set X, IsCompact K ∧ ∃ x ∉ K, U n = connectedComponentIn Kᶜ x :=
  U.exists_eq_connectedComponentIn' n

/-- An end sequence is decreasing. -/
theorem antitone : Antitone U :=
  U.antitone'

/-- An end sequence is eventually disjoint from every compact set. -/
theorem eventually_disjoint {K : Set X} (hK : IsCompact K) : ∀ᶠ n in atTop, Disjoint (U n) K :=
  U.eventually_disjoint' K hK

/-- Each set of an end sequence is nonempty. -/
theorem nonempty (n : ℕ) : (U n).Nonempty := by
  obtain ⟨K, -, x, hx, hU⟩ := U.exists_eq_connectedComponentIn n
  exact hU ▸ connectedComponentIn_nonempty_iff.2 hx

/-- Each set of an end sequence is preconnected. -/
theorem isPreconnected (n : ℕ) : IsPreconnected (U n) := by
  obtain ⟨K, -, x, -, hU⟩ := U.exists_eq_connectedComponentIn n
  exact hU ▸ isPreconnected_connectedComponentIn

/-- For a compact set `L`, the sequence eventually lies in a single component of `X \ L`. -/
theorem exists_eventually_subset_connectedComponentIn {L : Set X} (hL : IsCompact L) :
    ∃ x ∈ Lᶜ, ∀ᶠ n in atTop, U n ⊆ connectedComponentIn Lᶜ x := by
  obtain ⟨N, hN⟩ := (U.eventually_disjoint hL).exists_forall_of_atTop
  obtain ⟨x, hx⟩ := U.nonempty N
  have hsub : U N ⊆ connectedComponentIn Lᶜ x :=
    (U.isPreconnected N).subset_connectedComponentIn hx (hN N le_rfl).subset_compl_right
  exact ⟨x, (hN N le_rfl).subset_compl_right hx,
    eventually_atTop.2 ⟨N, fun n hn => (U.antitone hn).trans hsub⟩⟩

/-- For a compact set `L`, the component of `X \ L` that eventually contains the sequence. -/
noncomputable def component {L : Set X} (hL : IsCompact L) : ConnectedComponents ↥Lᶜ :=
  .mk ⟨(U.exists_eventually_subset_connectedComponentIn hL).choose,
    (U.exists_eventually_subset_connectedComponentIn hL).choose_spec.1⟩

/-- The sequence eventually lies in the component `U.component hL` of `X \ L`, and that
component is determined by this property. -/
theorem component_eq_mk_iff {L : Set X} (hL : IsCompact L) {x : X} (hx : x ∈ Lᶜ) :
    U.component hL = .mk ⟨x, hx⟩ ↔ ∀ᶠ n in atTop, U n ⊆ connectedComponentIn Lᶜ x := by
  have hspec := (U.exists_eventually_subset_connectedComponentIn hL).choose_spec
  set y := (U.exists_eventually_subset_connectedComponentIn hL).choose
  rw [component, ConnectedComponents.coe_eq_coe_iff_connectedComponentIn_eq]
  refine ⟨fun h => h ▸ hspec.2, fun h => ?_⟩
  obtain ⟨n, hn⟩ := (hspec.2.and h).exists
  obtain ⟨z, hz⟩ := U.nonempty n
  rw [connectedComponentIn_eq (hn.1 hz), connectedComponentIn_eq (hn.2 hz)]

/-- If `Uₙ` misses the compact set `L`, its component in `X \ L` is the component of the
sequence. -/
theorem component_eq_mk_of_mem {L : Set X} (hL : IsCompact L) {n : ℕ} (hn : Disjoint (U n) L)
    {x : X} (hxU : x ∈ U n) : U.component hL = .mk ⟨x, hn.subset_compl_right hxU⟩ :=
  (U.component_eq_mk_iff hL _).2 <| eventually_atTop.2 ⟨n, fun _ hm =>
    (U.antitone hm).trans <|
      (U.isPreconnected n).subset_connectedComponentIn hxU hn.subset_compl_right⟩

/-- For compact sets `L ⊆ L'`, the component of `X \ L'` containing the sequence maps to the
component of `X \ L` containing it. -/
theorem connectedComponentsMap_component {L L' : Set X} (hL : IsCompact L) (hL' : IsCompact L')
    (h : L ⊆ L') :
    (continuous_inclusion (compl_subset_compl.2 h)).connectedComponentsMap (U.component hL') =
      U.component hL := by
  obtain ⟨⟨x, hx⟩, hxU⟩ := ConnectedComponents.surjective_coe (U.component hL')
  rw [← hxU, Continuous.connectedComponentsMap_mk]
  refine ((U.component_eq_mk_iff hL _).2 ?_).symm
  exact ((U.component_eq_mk_iff hL' hx).1 hxU.symm).mono fun n hn =>
    hn.trans (connectedComponentIn_mono x (compl_subset_compl.2 h))

/-- Two end sequences define the same end when each set of either sequence contains a set of the
other. -/
instance setoid : Setoid (EndSequence X) where
  r U V := (∀ i, ∃ j, V j ⊆ U i) ∧ ∀ j, ∃ i, U i ⊆ V j
  iseqv :=
    { refl _ := ⟨fun i => ⟨i, le_rfl⟩, fun j => ⟨j, le_rfl⟩⟩
      symm h := ⟨h.2, h.1⟩
      trans h h' :=
        ⟨fun i => let ⟨j, hj⟩ := h.1 i; let ⟨k, hk⟩ := h'.1 j; ⟨k, hk.trans hj⟩,
          fun k => let ⟨j, hj⟩ := h'.2 k; let ⟨i, hi⟩ := h.2 j; ⟨i, hi.trans hj⟩⟩ }

/-- Unfolding the equivalence of end sequences: each set of either sequence contains a set of the
other. -/
theorem equiv_def : U ≈ V ↔ (∀ i, ∃ j, V j ⊆ U i) ∧ ∀ j, ∃ i, U i ⊆ V j :=
  Iff.rfl

/-- If each set of `U` contains a set of `V`, then `U` and `V` eventually lie in the same component
of `X \ L` for every compact `L`. -/
theorem component_eq_of_forall_exists_subset {U V : EndSequence X} (h : ∀ i, ∃ j, V j ⊆ U i)
    {L : Set X} (hL : IsCompact L) : U.component hL = V.component hL := by
  obtain ⟨⟨x, hx⟩, hxU⟩ := ConnectedComponents.surjective_coe (U.component hL)
  obtain ⟨n, hn⟩ := ((U.component_eq_mk_iff hL hx).1 hxU.symm).exists_forall_of_atTop
  obtain ⟨j, hj⟩ := h n
  rw [← hxU, eq_comm, V.component_eq_mk_iff]
  exact eventually_atTop.2 ⟨j, fun m hm => (V.antitone hm).trans (hj.trans (hn n le_rfl))⟩

/-- If `U` and `V` eventually lie in the same component of `X \ L` for every compact `L`, then
each set of `U` contains a set of `V`: the set `Uᵢ` is the component of the complement of its
compact set `K` in which `U` eventually lies. -/
private theorem exists_subset_of_forall_component_eq {U V : EndSequence X}
    (h : ∀ (L : Set X) (hL : IsCompact L), U.component hL = V.component hL) (i : ℕ) :
    ∃ j, V j ⊆ U i := by
  obtain ⟨K, hK, x, hx, hU⟩ := U.exists_eq_connectedComponentIn i
  have hUK : U.component hK = .mk ⟨x, hx⟩ :=
    (U.component_eq_mk_iff hK hx).2 <| eventually_atTop.2 ⟨i, fun _ hm => hU ▸ U.antitone hm⟩
  obtain ⟨j, hj⟩ :=
    ((V.component_eq_mk_iff hK hx).1 ((h K hK).symm.trans hUK)).exists_forall_of_atTop
  exact ⟨j, hU ▸ hj j le_rfl⟩

/-- Two end sequences define the same end exactly when, for every compact `L`, they eventually
lie in the same component of `X \ L`. -/
theorem equiv_iff_forall_component_eq :
    U ≈ V ↔ ∀ (L : Set X) (hL : IsCompact L), U.component hL = V.component hL :=
  ⟨fun h _ hL => component_eq_of_forall_exists_subset h.1 hL, fun h =>
    ⟨exists_subset_of_forall_component_eq h,
      exists_subset_of_forall_component_eq fun L hL => (h L hL).symm⟩⟩

/-- Containment of each set of one end sequence in a set of the other already makes the two
sequences define the same end. -/
theorem equiv_iff_forall_exists_subset : U ≈ V ↔ ∀ i, ∃ j, V j ⊆ U i :=
  ⟨fun h => h.1, fun h => (U.equiv_iff_forall_component_eq V).2 fun _ hL =>
    component_eq_of_forall_exists_subset h hL⟩

end EndSequence

variable (X) in
/-- The **ends** of a topological space `X`: decreasing sequences of components of complements of
compact sets, eventually disjoint from every compact set, up to mutual cofinal containment. -/
def EndComponents : Type u :=
  Quotient (EndSequence.setoid (X := X))

namespace EndComponents

/-- The end defined by an end sequence. -/
def mk (U : EndSequence X) : EndComponents X :=
  Quotient.mk _ U

/-- Every end is defined by an end sequence. -/
theorem mk_surjective : Function.Surjective (mk : EndSequence X → EndComponents X) :=
  Quotient.mk_surjective

/-- Two end sequences define the same end exactly when they are equivalent. -/
theorem mk_eq_mk_iff {U V : EndSequence X} : mk U = mk V ↔ U ≈ V :=
  Quotient.eq

/-- For a compact `L`, the component of `X \ L` in which the sequences of an end eventually lie. -/
noncomputable def component (e : EndComponents X) {L : Set X} (hL : IsCompact L) :
    ConnectedComponents ↥Lᶜ :=
  Quotient.lift (fun U : EndSequence X => U.component hL)
    (fun U V h => (U.equiv_iff_forall_component_eq V).1 h L hL) e

@[simp]
theorem component_mk (U : EndSequence X) {L : Set X} (hL : IsCompact L) :
    (mk U).component hL = U.component hL := by
  rfl

/-- An end is determined by its components in the complements of all compact sets. -/
theorem ext_component {e e' : EndComponents X}
    (h : ∀ (L : Set X) (hL : IsCompact L), e.component hL = e'.component hL) : e = e' := by
  obtain ⟨U, rfl⟩ := mk_surjective e
  obtain ⟨V, rfl⟩ := mk_surjective e'
  exact mk_eq_mk_iff.2 ((U.equiv_iff_forall_component_eq V).2 h)

/-- For compact sets `L ⊆ L'`, the component of an end in `X \ L'` maps to its component in
`X \ L`. -/
theorem connectedComponentsMap_component (e : EndComponents X) {L L' : Set X} (hL : IsCompact L)
    (hL' : IsCompact L') (h : L ⊆ L') :
    (continuous_inclusion (compl_subset_compl.2 h)).connectedComponentsMap (e.component hL') =
      e.component hL := by
  obtain ⟨U, rfl⟩ := mk_surjective e
  exact U.connectedComponentsMap_component hL hL' h

end EndComponents

/-- A compact space has no ends: an end sequence would eventually miss the whole space. -/
instance isEmpty_endComponents [CompactSpace X] : IsEmpty (EndComponents X) := by
  refine ⟨fun e => ?_⟩
  obtain ⟨U, -⟩ := EndComponents.mk_surjective e
  obtain ⟨n, hn⟩ := (U.eventually_disjoint isCompact_univ).exists
  exact (U.nonempty n).ne_empty (disjoint_univ.1 hn)

/-- The inverse system `n ↦ π₀(X \ Kₙ)` of components of the complements of a monotone sequence of
sets, with transition maps induced by the inclusions `X \ Kₙ ⊆ X \ Kₘ` for `m ≤ n`. -/
@[expose] noncomputable def componentComplFunctor (K : ℕ → Set X) (hK : Monotone K) :
    ℕᵒᵖ ⥤ Type u where
  obj n := ConnectedComponents ↥(K n.unop)ᶜ
  map f :=
    ↾(continuous_inclusion (compl_subset_compl.2 (hK (leOfHom f.unop)))).connectedComponentsMap
  map_id n := by
    ext c
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
    simp
  map_comp f g := by
    ext c
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
    simp

@[simp]
theorem componentComplFunctor_map_mk (K : ℕ → Set X) (hK : Monotone K) {m n : ℕᵒᵖ} (f : m ⟶ n)
    (x : ↥(K m.unop)ᶜ) :
    (componentComplFunctor K hK).map f (ConnectedComponents.mk x) =
      ConnectedComponents.mk (inclusion (compl_subset_compl.2 (hK (leOfHom f.unop))) x) :=
  rfl

variable {K : ℕ → Set X}

/-- An end defines a compatible family of components of the complements `X \ Kₙ`. -/
noncomputable def EndComponents.toSections (hK : Monotone K) (hKc : ∀ n, IsCompact (K n))
    (e : EndComponents X) : (componentComplFunctor K hK).sections :=
  ⟨fun n => e.component (hKc n.unop), fun {m n} f =>
    e.connectedComponentsMap_component (hKc n.unop) (hKc m.unop) (hK (leOfHom f.unop))⟩

@[simp]
theorem EndComponents.toSections_apply (hK : Monotone K) (hKc : ∀ n, IsCompact (K n))
    (e : EndComponents X) (n : ℕᵒᵖ) :
    (e.toSections hK hKc).val n = e.component (hKc n.unop) := by
  rfl

/-- A point of `X \ Kₙ` representing the `n`-th component of a compatible family. -/
private noncomputable def sectionsRep (hK : Monotone K)
    (s : (componentComplFunctor K hK).sections) (n : ℕ) : ↥(K n)ᶜ :=
  (ConnectedComponents.surjective_coe (s.val (.op n))).choose

private theorem mk_sectionsRep (hK : Monotone K) (s : (componentComplFunctor K hK).sections)
    (n : ℕ) : ConnectedComponents.mk (sectionsRep hK s n) = s.val (.op n) :=
  (ConnectedComponents.surjective_coe (s.val (.op n))).choose_spec

/-- For `m ≤ n`, the representative of the `n`-th component of a compatible family lies in the
`m`-th component. -/
private theorem connectedComponentIn_sectionsRep_eq (hK : Monotone K)
    (s : (componentComplFunctor K hK).sections) {m n : ℕ} (hmn : m ≤ n) :
    connectedComponentIn (K m)ᶜ (sectionsRep hK s n) =
      connectedComponentIn (K m)ᶜ (sectionsRep hK s m) := by
  have h := s.prop (homOfLE hmn).op
  rw [← mk_sectionsRep hK s n, ← mk_sectionsRep hK s m, componentComplFunctor_map_mk] at h
  exact (ConnectedComponents.coe_eq_coe_iff_connectedComponentIn_eq _ _).1 h

/-- The end sequence of the components of the complements `X \ Kₙ` picked out by a compatible
family. -/
noncomputable def EndSequence.ofSections (hK : Monotone K) (hKc : ∀ n, IsCompact (K n))
    (hcof : ∀ L : Set X, IsCompact L → ∃ n, L ⊆ K n) (s : (componentComplFunctor K hK).sections) :
    EndSequence X where
  toFun n := connectedComponentIn (K n)ᶜ (sectionsRep hK s n)
  exists_eq_connectedComponentIn' n := ⟨K n, hKc n, _, (sectionsRep hK s n).2, rfl⟩
  antitone' {m n} hmn := by
    dsimp only
    rw [← connectedComponentIn_sectionsRep_eq hK s hmn]
    exact connectedComponentIn_mono _ (compl_subset_compl.2 (hK hmn))
  eventually_disjoint' L hL := by
    obtain ⟨m, hm⟩ := hcof L hL
    exact eventually_atTop.2 ⟨m, fun n hn => disjoint_left.2 fun y hy hyL =>
      connectedComponentIn_subset _ _ hy (hK hn (hm hyL))⟩

/-- The `n`-th set of the end sequence of a compatible family is the `n`-th component of the
family, as a subset of `X \ Kₙ`. -/
theorem EndSequence.ofSections_apply (hK : Monotone K) (hKc : ∀ n, IsCompact (K n))
    (hcof : ∀ L : Set X, IsCompact L → ∃ n, L ⊆ K n) (s : (componentComplFunctor K hK).sections)
    {n : ℕ} {x : ↥(K n)ᶜ} (hx : ConnectedComponents.mk x = s.val (.op n)) :
    EndSequence.ofSections hK hKc hcof s n = connectedComponentIn (K n)ᶜ x := by
  rw [← mk_sectionsRep hK s n] at hx
  exact ((ConnectedComponents.coe_eq_coe_iff_connectedComponentIn_eq x.2
    (sectionsRep hK s n).2).1 hx).symm

/-- The end sequence of a compatible family lies, in the complement of `Kₙ`, in the `n`-th
component of the family. -/
theorem EndSequence.component_ofSections (hK : Monotone K) (hKc : ∀ n, IsCompact (K n))
    (hcof : ∀ L : Set X, IsCompact L → ∃ n, L ⊆ K n) (s : (componentComplFunctor K hK).sections)
    (n : ℕ) : (EndSequence.ofSections hK hKc hcof s).component (hKc n) = s.val (.op n) := by
  rw [← mk_sectionsRep hK s n]
  exact (EndSequence.ofSections hK hKc hcof s).component_eq_mk_of_mem (hKc n) (n := n)
    (disjoint_compl_left.mono_left (connectedComponentIn_subset _ _))
    (mem_connectedComponentIn (sectionsRep hK s n).2)

/-- Along a monotone sequence of compact sets `Kₙ` that is cofinal among all compact sets, the ends
of `X` are the inverse limit of the sets `π₀(X \ Kₙ)` of complementary components. The end of a
compatible family is the sequence of its components. -/
noncomputable def endComponentsEquivSections (hK : Monotone K) (hKc : ∀ n, IsCompact (K n))
    (hcof : ∀ L : Set X, IsCompact L → ∃ n, L ⊆ K n) :
    EndComponents X ≃ (componentComplFunctor K hK).sections where
  toFun e := e.toSections hK hKc
  invFun s := .mk (.ofSections hK hKc hcof s)
  left_inv e := by
    refine EndComponents.ext_component fun L hL => ?_
    obtain ⟨n, hn⟩ := hcof L hL
    rw [← e.connectedComponentsMap_component hL (hKc n) hn,
      ← (EndComponents.mk _).connectedComponentsMap_component hL (hKc n) hn,
      EndComponents.component_mk, EndSequence.component_ofSections,
      EndComponents.toSections_apply]
  right_inv s := Subtype.ext <| funext fun n =>
    EndSequence.component_ofSections hK hKc hcof s n.unop

@[simp]
theorem endComponentsEquivSections_apply (hK : Monotone K) (hKc : ∀ n, IsCompact (K n))
    (hcof : ∀ L : Set X, IsCompact L → ∃ n, L ⊆ K n) (e : EndComponents X) (n : ℕᵒᵖ) :
    (endComponentsEquivSections hK hKc hcof e).val n = e.component (hKc n.unop) := by
  rfl

@[simp]
theorem endComponentsEquivSections_symm_apply (hK : Monotone K) (hKc : ∀ n, IsCompact (K n))
    (hcof : ∀ L : Set X, IsCompact L → ∃ n, L ⊆ K n) (s : (componentComplFunctor K hK).sections) :
    (endComponentsEquivSections hK hKc hcof).symm s = .mk (.ofSections hK hKc hcof s) := by
  rfl

/-- The end of a compatible family lies, in the complement of `Kₙ`, in the `n`-th component of the
family. -/
theorem component_endComponentsEquivSections_symm (hK : Monotone K) (hKc : ∀ n, IsCompact (K n))
    (hcof : ∀ L : Set X, IsCompact L → ∃ n, L ⊆ K n) (s : (componentComplFunctor K hK).sections)
    (n : ℕ) : ((endComponentsEquivSections hK hKc hcof).symm s).component (hKc n) = s.val (.op n) :=
  EndSequence.component_ofSections hK hKc hcof s n

end TauCeti

namespace CompactExhaustion

variable {X : Type u} [TopologicalSpace X]

/-- The ends of a space with a compact exhaustion `K` are the inverse limit of the sets
`π₀(X \ Kₙ)` of complementary components. -/
noncomputable def endComponentsEquivSections (K : CompactExhaustion X) :
    TauCeti.EndComponents X ≃ (TauCeti.componentComplFunctor K fun _ _ h => K.subset h).sections :=
  TauCeti.endComponentsEquivSections _ K.isCompact fun _ hL => K.exists_superset_of_isCompact hL

@[simp]
theorem endComponentsEquivSections_apply (K : CompactExhaustion X) (e : TauCeti.EndComponents X)
    (n : ℕᵒᵖ) : (K.endComponentsEquivSections e).val n = e.component (K.isCompact n.unop) := by
  rfl

@[simp]
theorem endComponentsEquivSections_symm_apply (K : CompactExhaustion X)
    (s : (TauCeti.componentComplFunctor K fun _ _ h => K.subset h).sections) :
    K.endComponentsEquivSections.symm s =
      .mk (.ofSections _ K.isCompact (fun _ hL => K.exists_superset_of_isCompact hL) s) := by
  rfl

end CompactExhaustion

namespace TauCeti

section AtInfinity

variable {X : Type u} [TopologicalSpace X]

/-! ### Existence of ends -/

section Existence

variable [T2Space X] [WeaklyLocallyCompactSpace X] [SigmaCompactSpace X] [LocallyConnectedSpace X]

/-- **Every unbounded complementary component contains an end.** In a σ-compact, locally compact
Hausdorff, locally connected space with no compact connected component, let `L` be compact and let
the component of `x` in `X \ L` have noncompact closure. Then some end sequence starts inside that
component. -/
theorem exists_endSequence_subset_connectedComponentIn
    (hX : ∀ x : X, ¬IsCompact (connectedComponent x)) {L : Set X} (hL : IsCompact L) {x : X}
    (hx : ¬IsCompact (closure (connectedComponentIn Lᶜ x))) :
    ∃ U : EndSequence X, U 0 ⊆ connectedComponentIn Lᶜ x := by
  -- Along a compact exhaustion `Kₙ`, choose nested components of the complements of `L ∪ Kₙ`
  -- with noncompact closure.
  set K := CompactExhaustion.choice X
  have hM (n : ℕ) : IsCompact (L ∪ K n) := hL.union (K.isCompact n)
  have hMmono {m n : ℕ} (h : m ≤ n) : L ∪ K m ⊆ L ∪ K n := union_subset_union_right L (K.subset h)
  -- Points whose component in the complement of `L ∪ Kₙ` has noncompact closure.
  obtain ⟨y₀, hy₀, hP₀⟩ := exists_mem_not_isCompact_closure_connectedComponentIn_compl hX hx (hM 0)
  obtain ⟨z, rfl, hz⟩ := exists_seq_not_isCompact_closure_connectedComponentIn_compl hX hM hP₀
  have hzM (n : ℕ) : z n ∉ L ∪ K n :=
    notMem_of_not_isCompact_closure_connectedComponentIn_compl (hz n).1
  refine ⟨{ toFun n := connectedComponentIn (L ∪ K n)ᶜ (z n)
            exists_eq_connectedComponentIn' n := ⟨L ∪ K n, hM n, z n, hzM n, rfl⟩
            antitone' := antitone_nat_of_succ_le fun n ↦ ?_
            eventually_disjoint' C hC := ?_ }, ?_⟩
  · -- The next component lies in the component of the previous point.
    refine (connectedComponentIn_mono _ (compl_subset_compl.2 (hMmono n.le_succ))).trans ?_
    exact (connectedComponentIn_eq (hz n).2).symm.subset
  · obtain ⟨m, hm⟩ := K.exists_superset_of_isCompact hC
    exact eventually_atTop.2 ⟨m, fun n hn ↦ subset_compl_iff_disjoint_right.1 <|
      (connectedComponentIn_subset _ _).trans <| compl_subset_compl.2 <|
        hm.trans ((K.subset hn).trans subset_union_right)⟩
  · refine (connectedComponentIn_mono _ (compl_subset_compl.2 subset_union_left)).trans ?_
    exact (connectedComponentIn_eq hy₀).symm.subset

/-- A nonempty σ-compact, locally compact Hausdorff, locally connected space with no compact
connected component has an end. -/
theorem nonempty_endComponents [Nonempty X] (hX : ∀ x : X, ¬IsCompact (connectedComponent x)) :
    Nonempty (EndComponents X) := by
  obtain ⟨x⟩ := ‹Nonempty X›
  obtain ⟨U, -⟩ := exists_endSequence_subset_connectedComponentIn hX isCompact_empty (x := x) <| by
    rw [compl_empty, connectedComponentIn_univ, isClosed_connectedComponent.closure_eq]
    exact hX x
  exact ⟨.mk U⟩

end Existence

/-! ### Connectedness at infinity -/

variable (X) in
/-- A space is **connected at infinity** if for every compact set `K` there is a compact set
`L ⊇ K` such that any two points outside `L` are joined by a path in `X \ K`. -/
def ConnectedAtInfinity : Prop :=
  ∀ K : Set X, IsCompact K → ∃ L : Set X, IsCompact L ∧ K ⊆ L ∧ ∀ x ∉ L, ∀ y ∉ L, JoinedIn Kᶜ x y

/-- Unfolding `TauCeti.ConnectedAtInfinity`. -/
theorem connectedAtInfinity_iff : ConnectedAtInfinity X ↔
    ∀ K : Set X, IsCompact K → ∃ L : Set X, IsCompact L ∧ K ⊆ L ∧
      ∀ x ∉ L, ∀ y ∉ L, JoinedIn Kᶜ x y :=
  Iff.rfl

namespace ConnectedAtInfinity

/-- A compact space is connected at infinity: take `L` to be the whole space. -/
theorem of_compactSpace [CompactSpace X] : ConnectedAtInfinity X :=
  fun _ _ ↦ ⟨univ, isCompact_univ, subset_univ _, fun x hx ↦ absurd (mem_univ x) hx⟩

/-- A space connected at infinity has at most one end. -/
theorem subsingleton_endComponents (h : ConnectedAtInfinity X) :
    Subsingleton (EndComponents X) := by
  refine ⟨fun e e' ↦ ?_⟩
  obtain ⟨U, rfl⟩ := EndComponents.mk_surjective e
  obtain ⟨V, rfl⟩ := EndComponents.mk_surjective e'
  refine EndComponents.mk_eq_mk_iff.2 ((U.equiv_iff_forall_exists_subset V).2 fun i ↦ ?_)
  -- Far out, the sets of `U` and `V` are joined by paths avoiding the compact set `K` of `Uᵢ`, so
  -- they lie in the same component of its complement, which is `Uᵢ`.
  obtain ⟨K, hK, y, -, hU⟩ := U.exists_eq_connectedComponentIn i
  obtain ⟨L, hL, hKL, hjoin⟩ := h K hK
  obtain ⟨n, hin, hUn, hVn⟩ := ((eventually_ge_atTop i).and
    ((U.eventually_disjoint hL).and (V.eventually_disjoint hL))).exists
  obtain ⟨a, ha⟩ := U.nonempty n
  obtain ⟨b, hb⟩ := V.nonempty n
  -- The path from `a` to `b` avoids `K`, so `b` lies in the component of `a` in `X \ K`.
  obtain ⟨γ, hγ⟩ := hjoin a (disjoint_left.1 hUn ha) b (disjoint_left.1 hVn hb)
  have hab : b ∈ connectedComponentIn Kᶜ a :=
    (isPreconnected_range γ.continuous).subset_connectedComponentIn ⟨0, γ.source⟩
      (range_subset_iff.2 hγ) ⟨1, γ.target⟩
  have hVK : V n ⊆ Kᶜ := (hVn.mono_right hKL).subset_compl_right
  refine ⟨n, ((V.isPreconnected n).subset_connectedComponentIn hb hVK).trans ?_⟩
  rw [← connectedComponentIn_eq hab, hU, ← connectedComponentIn_eq (hU ▸ U.antitone hin ha)]

end ConnectedAtInfinity

section OneEnd

variable [T2Space X] [WeaklyLocallyCompactSpace X] [SigmaCompactSpace X]
  [LocallyPathConnectedSpace X] [PreconnectedSpace X]

/-- A preconnected, locally path-connected, σ-compact, locally compact Hausdorff space with at most
one end is connected at infinity. -/
theorem connectedAtInfinity_of_subsingleton_endComponents [Subsingleton (EndComponents X)] :
    ConnectedAtInfinity X := by
  -- Take a compact neighbourhood `L` of `K` whose complementary components all have noncompact
  -- closure. Each of them contains an end, so there is only one, and it is path-connected.
  refine fun K hK ↦ ?_
  obtain ⟨L, hL, hKL, -, hLc⟩ := exists_isCompact_finite_connectedComponents_compl hK
  refine ⟨L, hL, hKL.trans interior_subset, fun x hx y hy ↦ ?_⟩
  have : NoncompactSpace X :=
    ⟨fun h ↦ hLc x hx (h.of_isClosed_subset isClosed_closure (subset_univ _))⟩
  have hX := not_isCompact_connectedComponent (X := X)
  obtain ⟨U, hU⟩ := exists_endSequence_subset_connectedComponentIn hX hL (hLc x hx)
  obtain ⟨V, hV⟩ := exists_endSequence_subset_connectedComponentIn hX hL (hLc y hy)
  -- The two ends agree, so the components of `x` and `y` in `X \ L` share a point.
  obtain ⟨j, hj⟩ := ((U.equiv_iff_forall_exists_subset V).1
    (EndComponents.mk_eq_mk_iff.1 (Subsingleton.elim (EndComponents.mk U) (.mk V)))) 0
  obtain ⟨w, hw⟩ := V.nonempty j
  have hxy : y ∈ connectedComponentIn Lᶜ x := by
    rw [connectedComponentIn_eq (hU (hj hw)),
      ← connectedComponentIn_eq (hV (V.antitone j.zero_le hw))]
    exact mem_connectedComponentIn hy
  -- That component is open and connected, hence path-connected.
  exact (hL.isClosed.isOpen_compl.joinedIn_of_mem_connectedComponentIn hxy).mono
    ((connectedComponentIn_subset _ _).trans (compl_subset_compl.2 (hKL.trans interior_subset)))

/-- **Connectedness at infinity is having at most one end**, for preconnected, locally
path-connected, σ-compact, locally compact Hausdorff spaces. -/
theorem connectedAtInfinity_iff_subsingleton_endComponents :
    ConnectedAtInfinity X ↔ Subsingleton (EndComponents X) :=
  ⟨ConnectedAtInfinity.subsingleton_endComponents, fun _ ↦
    connectedAtInfinity_of_subsingleton_endComponents⟩

/-- **A noncompact space is connected at infinity exactly when it has one end**, for preconnected,
locally path-connected, σ-compact, locally compact Hausdorff spaces. -/
theorem connectedAtInfinity_iff_natCard_endComponents_eq_one [NoncompactSpace X] :
    ConnectedAtInfinity X ↔ Nat.card (EndComponents X) = 1 := by
  have := (Filter.cocompact X).nonempty_of_neBot
  have : Nonempty (EndComponents X) := nonempty_endComponents not_isCompact_connectedComponent
  rw [Nat.card_eq_one_iff_unique, connectedAtInfinity_iff_subsingleton_endComponents]
  exact (and_iff_left this).symm

end OneEnd

end AtInfinity

/-! ### The two ends of the real line -/

namespace EndSequence

/-- The end of `ℝ` at `+∞`: the half-lines `(n, ∞)`. -/
noncomputable def realAtTop : EndSequence ℝ where
  toFun n := Ioi n
  exists_eq_connectedComponentIn' n := ⟨Icc (-n) n, isCompact_Icc, n + 1,
    fun h => by linarith [h.2],
    (connectedComponentIn_compl_Icc_eq_Ioi (neg_le_self n.cast_nonneg) (lt_add_one _)).symm⟩
  antitone' _ _ h := Ioi_subset_Ioi (Nat.cast_le.2 h)
  eventually_disjoint' K hK := by
    obtain ⟨b, hb⟩ := hK.bddAbove
    filter_upwards [eventually_ge_atTop ⌈b⌉₊] with n hn
    refine disjoint_left.2 fun x (hx : (n : ℝ) < x) hxK => not_lt.2 (hb hxK) ?_
    linarith [(Nat.le_ceil b).trans (Nat.cast_le.2 hn)]

/-- The end of `ℝ` at `-∞`: the half-lines `(-∞, -n)`. -/
noncomputable def realAtBot : EndSequence ℝ where
  toFun n := Iio (-n)
  exists_eq_connectedComponentIn' n := ⟨Icc (-n) n, isCompact_Icc, -(n + 1),
    fun h => by linarith [h.1],
    (connectedComponentIn_compl_Icc_eq_Iio (neg_le_self n.cast_nonneg) (by linarith)).symm⟩
  antitone' _ _ h := Iio_subset_Iio (neg_le_neg (Nat.cast_le.2 h))
  eventually_disjoint' K hK := by
    obtain ⟨b, hb⟩ := hK.bddBelow
    filter_upwards [eventually_ge_atTop ⌈-b⌉₊] with n hn
    refine disjoint_left.2 fun x (hx : x < -(n : ℝ)) hxK => not_lt.2 (hb hxK) ?_
    linarith [(Nat.le_ceil (-b)).trans (Nat.cast_le.2 hn)]

@[simp]
theorem realAtTop_apply (n : ℕ) : realAtTop n = Ioi (n : ℝ) := by
  rfl

@[simp]
theorem realAtBot_apply (n : ℕ) : realAtBot n = Iio (-n : ℝ) := by
  rfl

/-- An end sequence of `ℝ` defines the end at `+∞` or the end at `-∞`, according to the side of
`0` on which it eventually lies. -/
theorem equiv_realAtTop_or_equiv_realAtBot (U : EndSequence ℝ) :
    U ≈ realAtTop ∨ U ≈ realAtBot := by
  obtain ⟨N, hN⟩ := (U.eventually_disjoint (isCompact_singleton (x := (0 : ℝ)))).exists
  have hne : ∀ q ∈ U N, id q ≠ 0 := fun q hq h => disjoint_left.1 hN hq h
  -- far enough out, the sequence also misses `[-i, i]`
  have hfar (i : ℕ) : ∃ j ≥ N, Disjoint (U j) (Icc (-i) i) := by
    obtain ⟨j, hj⟩ := ((eventually_ge_atTop N).and
      (U.eventually_disjoint isCompact_Icc)).exists_forall_of_atTop
    exact ⟨j, (hj j le_rfl).1, (hj j le_rfl).2⟩
  -- the preconnected set `U N` misses `0`, so it lies on one side of `0`
  rcases (U.isPreconnected N).mapsTo_Ioi_or_Iio continuousOn_id hne with h | h
  · refine .inl (Setoid.symm ((realAtTop.equiv_iff_forall_exists_subset U).2 fun i => ?_))
    obtain ⟨j, hjN, hj⟩ := hfar i
    refine ⟨j, fun x hx => ?_⟩
    have hx0 : 0 < x := h (U.antitone hjN hx)
    simp only [realAtTop_apply, mem_Ioi]
    by_contra h
    exact disjoint_left.1 hj hx ⟨by linarith [(Nat.cast_nonneg i : (0 : ℝ) ≤ i)], not_lt.1 h⟩
  · refine .inr (Setoid.symm ((realAtBot.equiv_iff_forall_exists_subset U).2 fun i => ?_))
    obtain ⟨j, hjN, hj⟩ := hfar i
    refine ⟨j, fun x hx => ?_⟩
    have hx0 : x < 0 := h (U.antitone hjN hx)
    simp only [realAtBot_apply, mem_Iio]
    by_contra h
    exact disjoint_left.1 hj hx ⟨not_lt.1 h, by linarith [(Nat.cast_nonneg i : (0 : ℝ) ≤ i)]⟩

/-- The ends of `ℝ` at `+∞` and at `-∞` are different. -/
theorem not_realAtTop_equiv_realAtBot : ¬ realAtTop ≈ realAtBot := fun h => by
  obtain ⟨j, hj⟩ := h.1 0
  have := hj (show (-(j : ℝ) - 1) ∈ realAtBot j by simp)
  simp only [realAtTop_apply, Nat.cast_zero, mem_Ioi] at this
  linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]

end EndSequence

/-- The real line has exactly two ends, at `+∞` and at `-∞`. -/
theorem natCard_endComponents_real : Nat.card (EndComponents ℝ) = 2 := by
  refine Nat.card_eq_two_iff.2 ⟨.mk .realAtTop, .mk .realAtBot,
    fun h => EndSequence.not_realAtTop_equiv_realAtBot (EndComponents.mk_eq_mk_iff.1 h), ?_⟩
  refine eq_univ_of_forall fun e => ?_
  obtain ⟨U, rfl⟩ := EndComponents.mk_surjective e
  rcases U.equiv_realAtTop_or_equiv_realAtBot with h | h
  · exact .inl (EndComponents.mk_eq_mk_iff.2 h)
  · exact .inr (EndComponents.mk_eq_mk_iff.2 h)

end TauCeti
