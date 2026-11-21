/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GraphOfGroups.Presentation
public import TauCeti.GroupTheory.GraphOfGroups.SpanningTree
public import TauCeti.GroupTheory.PushoutI.TrivialBase
public import Mathlib.GroupTheory.PushoutI
public import Mathlib.GroupTheory.HNNExtension
import TauCeti.GroupTheory.PushoutI.Map

/-!
# One-edge graphs of groups: amalgamated products and HNN extensions

A graph of groups with a single geometric edge is either a segment or a loop, and its
fundamental group is Mathlib's amalgamated product or HNN extension respectively.

* For the segment `GraphOfGroups.segment f g hf hg` with vertex groups `A`, `B`, edge group `C`
  and monomorphisms `f : C →* A`, `g : C →* B`, the group `π₁(𝔸, T)` relative to any nonempty
  set `T` of darts (for instance the maximal tree, which is the whole segment) is the amalgamated
  product `A ∗_C B`, Mathlib's `Monoid.PushoutI` indexed by the two vertices. The isomorphism is
  the identity on `A` and on `B` and kills both darts. When the edge group `C` is trivial this
  is the free product `A ∗ B`, Mathlib's `Monoid.Coprod A B`. For a `Bool`-indexed family of
  monomorphisms `φ b : C →* G b`, the amalgamated product of the vertex groups of the segment of
  `φ false` and `φ true` is the amalgamated product `Monoid.PushoutI φ` of the family. For the
  canonical spanning tree `T` of the segment, which contains every dart, `π₁Equiv` sends the class
  in `π₁(𝔸, v₀)` of the based loop `q y q⁻¹`, for any edge path `q` from `v₀` to a vertex `b`, to
  the image of `y ∈ A_b` in `π₁(𝔸, T)`.
* For the loop `GraphOfGroups.loop f g hf hg` with vertex group `G`, edge group `C` and
  monomorphisms `f g : C →* G`, the group `π₁(𝔸, ∅)` relative to the empty maximal tree is the
  HNN extension `HNNExtension G (range f) (range g) φ` with `φ (f c) = g c`. The isomorphism is
  the identity on `G` and sends the dart `((), true)`, whose boundary maps are `α = f` and
  `ω = g`, to `t⁻¹`: Mathlib's relation `t f(c) t⁻¹ = g(c)` is the relation
  `e g(c) e⁻¹ = f(c)` of the dart `e = ((), true)`, read for `e = t⁻¹`.

These comparisons transport the normal form theorems of `Monoid.PushoutI` and `HNNExtension` to
one-edge graphs of groups; in particular the vertex groups of a one-edge graph of groups embed in
its fundamental group.

## Main definitions

* `TauCeti.GraphOfGroups.segmentMaps`: the monomorphisms of the segment as the vertex-indexed
  family amalgamated by `Monoid.PushoutI`.
* `TauCeti.GraphOfGroups.π₁Tree.equivPushoutI`: `π₁(segment, T) ≃* A ∗_C B` for nonempty `T`.
* `TauCeti.GraphOfGroups.π₁Tree.equivCoprod`: `π₁(segment, T) ≃* A ∗ B` for nonempty `T` and
  trivial edge group.
* `TauCeti.GraphOfGroups.segmentPushoutIEquiv`: the amalgam of the vertex groups of the segment
  of a `Bool`-indexed family `φ` is `Monoid.PushoutI φ`.
* `TauCeti.GraphOfGroups.loopEquiv`: the isomorphism `range f ≃* range g`, `f c ↦ g c`, along
  which the HNN extension of the loop is taken.
* `TauCeti.GraphOfGroups.π₁Tree.equivHNNExtension`: `π₁(loop, ∅) ≃* HNNExtension G (range f)
  (range g) (loopEquiv f g hf hg)`.

## Main results

* `TauCeti.GraphOfGroups.π₁Equiv_segment_vertexHom_mapPath`: for the canonical spanning tree `T`
  of the segment, `π₁Equiv` sends the based loop class of `q y q⁻¹` to the vertex-group image of
  `y` in `π₁(segment, T)`, for every edge path `q`.
* `TauCeti.GraphOfGroups.π₁Tree.of_injective_segment` and
  `TauCeti.GraphOfGroups.π₁Tree.of_injective_loop`: the vertex groups of a one-edge graph of
  groups embed in its fundamental group.

## References

* J.-P. Serre, *Trees*, Chapter I, §1.1 and §5.1.
* V. Guirardel, G. Levitt, *JSJ decompositions of groups*, Astérisque 395 (2017), §1.1.
-/

public section

universe w x

namespace TauCeti

namespace GraphOfGroups

/-! ### The segment: amalgamated products -/

section segment

variable {A B : Type w} {C : Type x} [Group A] [Group B] [Group C] (f : C →* A) (g : C →* B)
  (hf : Function.Injective f) (hg : Function.Injective g)

/-- The monomorphisms `f : C →* A` and `g : C →* B` of the segment, as the family of maps into its
vertex groups, indexed by its two vertices, that `Monoid.PushoutI` amalgamates. -/
def segmentMaps : ∀ b : SerreGraph.segment.V, C →* (segment f g hf hg).vertexGroup b
  | false => f
  | true => g

@[simp] theorem segmentMaps_false : segmentMaps f g hf hg false = f := (rfl)

@[simp] theorem segmentMaps_true : segmentMaps f g hf hg true = g := (rfl)

theorem segmentMaps_injective (b : SerreGraph.segment.V) :
    Function.Injective (segmentMaps f g hf hg b) := by
  cases b
  · exact hf
  · exact hg

/-- The boundary map `α_e` of a dart `e` of the segment is the edge map into the vertex group at
the source of `e`. -/
theorem segment_α_eq_segmentMaps (e : SerreGraph.segment.E) :
    (segment f g hf hg).α e = segmentMaps f g hf hg (SerreGraph.segment.src e) := by
  cases e
  · exact segment_α_false f g hf hg
  · exact segment_α_true f g hf hg

/-- The boundary map of the dart leaving the vertex `b` of the segment is the edge map into the
vertex group at `b`. -/
@[simp] theorem αArrow_segmentArrow (b : SerreGraph.segment.V) :
    (segment f g hf hg).αArrow (SerreGraph.segmentArrow b) = segmentMaps f g hf hg b := by
  -- `segmentArrow b` is the arrow `⟨b, rfl, rfl⟩` of the dart `b`, the argument of `αArrow_mk`.
  have h : SerreGraph.segmentArrow b = ⟨b, rfl, rfl⟩ := Subtype.ext (SerreGraph.segmentArrow_val b)
  rw [h]
  exact ((segment f g hf hg).αArrow_mk b).trans (segment_α_eq_segmentMaps f g hf hg b)

namespace π₁Tree

variable {f g hf hg} {T : Set SerreGraph.segment.E}

/-- The defining relation `e ω_e(c) = α_e(c) e` of the dart `false` of the segment, which runs
from the vertex `false` to the vertex `true`. -/
private theorem edge_false_mul_of_true (c : C) :
    edge T false * of (𝔸 := segment f g hf hg) T true (g c) =
      of (𝔸 := segment f g hf hg) T false (f c) * edge T false := by
  have h := edge_mul_of_ω (𝔸 := segment f g hf hg) (T := T) false c
  rwa [segment_ω_false, segment_α_false] at h

/-- In `π₁(segment, T)` with `T` nonempty, both darts are trivial: one of them lies in `T`, and
the other is its inverse. -/
@[simp] theorem edge_segment_eq_one (hT : T.Nonempty) (e : SerreGraph.segment.E) :
    (edge T e : π₁Tree (segment f g hf hg) T) = 1 := by
  obtain ⟨e', he'⟩ := hT
  obtain rfl | rfl : e = e' ∨ e = SerreGraph.segment.rev e' := by
    cases e <;> cases e' <;> first | exact .inl rfl | exact .inr rfl
  · exact edge_eq_one he'
  · rw [edge_rev, edge_eq_one he', inv_one]

/-- In `π₁(segment, T)` with `T` nonempty, the two images of the edge group agree: the dart
`false` is trivial, so its relation `e g(c) e⁻¹ = f(c)` becomes `g(c) = f(c)`. -/
@[simp] theorem of_true_eq_of_false (hT : T.Nonempty) (c : C) :
    of (𝔸 := segment f g hf hg) T true (g c) = of (𝔸 := segment f g hf hg) T false (f c) := by
  have h := edge_false_mul_of_true (f := f) (hf := hf) (hg := hg) (T := T) c
  rwa [edge_segment_eq_one hT false, one_mul, mul_one] at h

variable (f g hf hg) in
/-- The fundamental group of the segment, relative to a nonempty set `T` of darts, is the
amalgamated product `A ∗_C B` of its vertex groups over the edge group, Mathlib's
`Monoid.PushoutI` of `segmentMaps f g hf hg`. The vertex groups map by the identity and both
darts map to `1`. The hypothesis on `T` is needed: relative to `T = ∅` the dart is an extra
generator of `π₁(segment, ∅)`. -/
noncomputable def equivPushoutI (hT : T.Nonempty) :
    π₁Tree (segment f g hf hg) T ≃* Monoid.PushoutI (segmentMaps f g hf hg) :=
  MonoidHom.toMulEquiv
    (lift (fun b => Monoid.PushoutI.of b) (fun _ => 1) (fun _ _ => rfl) (fun _ => by simp)
      (fun e c => by
        simp only [one_mul, inv_one, mul_one]
        -- `segment.tgt e` and `segment.src e` reduce to `!e` and `e`; rewriting them inside the
        -- dependent index of `Monoid.PushoutI.of` is not possible, so the cases close by `exact`.
        cases e
        · simp only [segment_ω_false, segment_α_false]
          exact (Monoid.PushoutI.of_apply_eq_base (segmentMaps f g hf hg) true c).trans
            (Monoid.PushoutI.of_apply_eq_base (segmentMaps f g hf hg) false c).symm
        · simp only [segment_ω_true, segment_α_true]
          exact (Monoid.PushoutI.of_apply_eq_base (segmentMaps f g hf hg) false c).trans
            (Monoid.PushoutI.of_apply_eq_base (segmentMaps f g hf hg) true c).symm))
    -- The literal `false : Bool` is not syntactically a vertex of the segment, so the group
    -- structure at it is supplied by naming the middle group `A` of the composite.
    (Monoid.PushoutI.lift (fun b => of T b)
      (MonoidHom.comp (N := A) (of (𝔸 := segment f g hf hg) T false) f) fun b => by
      cases b
      · rfl
      · exact MonoidHom.ext (of_true_eq_of_false hT))
    (hom_ext (fun b => by ext; simp) fun e => by simp [hT])
    (by
      have : Nonempty SerreGraph.segment.V := ⟨false⟩
      exact Monoid.PushoutI.hom_ext_nonempty fun b => by ext; simp)

@[simp] theorem equivPushoutI_of (hT : T.Nonempty) (b : SerreGraph.segment.V)
    (a : (segment f g hf hg).vertexGroup b) :
    equivPushoutI f g hf hg hT (of T b a) = Monoid.PushoutI.of b a :=
  lift_of ..

theorem equivPushoutI_edge (hT : T.Nonempty) (e : SerreGraph.segment.E) :
    equivPushoutI f g hf hg hT (edge T e) = 1 :=
  lift_edge ..

@[simp] theorem equivPushoutI_symm_of (hT : T.Nonempty) (b : SerreGraph.segment.V)
    (a : (segment f g hf hg).vertexGroup b) :
    (equivPushoutI f g hf hg hT).symm (Monoid.PushoutI.of b a) = of T b a :=
  (MulEquiv.symm_apply_eq _).2 (equivPushoutI_of hT b a).symm

/-- The vertex groups of the segment embed in its fundamental group relative to a nonempty set
of darts: this is the normal form theorem for amalgamated products. -/
theorem of_injective_segment (hT : T.Nonempty) (b : SerreGraph.segment.V) :
    Function.Injective (of (𝔸 := segment f g hf hg) T b) := by
  intro a a' h
  refine Monoid.PushoutI.of_injective (segmentMaps_injective f g hf hg) b ?_
  rw [← equivPushoutI_of hT, ← equivPushoutI_of hT, h]

/-! #### Trivial edge group: free products -/

section Coprod

variable [Subsingleton C]

variable (f g hf hg) in
/-- The amalgamated product of the vertex groups of the segment over a trivial edge group is
their free product. This is `Monoid.PushoutI.equivCoprod` for the family of vertex groups of the
segment: its index type is only definitionally `Bool`, so the monoid structures of the family
over `Bool` are not found by unification and are supplied here. -/
private noncomputable def pushoutIEquivCoprod :
    Monoid.PushoutI (segmentMaps f g hf hg) ≃* Monoid.Coprod A B :=
  @Monoid.PushoutI.equivCoprod _ _ (fun _ : SerreGraph.segment.V => inferInstance) _
    (segmentMaps f g hf hg) _

private theorem pushoutIEquivCoprod_of_false (a : A) :
    pushoutIEquivCoprod f g hf hg (Monoid.PushoutI.of (φ := segmentMaps f g hf hg) false a) =
      Monoid.Coprod.inl a :=
  @Monoid.PushoutI.equivCoprod_of_false _ _ (fun _ : SerreGraph.segment.V => inferInstance) _
    (segmentMaps f g hf hg) _ a

private theorem pushoutIEquivCoprod_of_true (b : B) :
    pushoutIEquivCoprod f g hf hg (Monoid.PushoutI.of (φ := segmentMaps f g hf hg) true b) =
      Monoid.Coprod.inr b :=
  @Monoid.PushoutI.equivCoprod_of_true _ _ (fun _ : SerreGraph.segment.V => inferInstance) _
    (segmentMaps f g hf hg) _ b

variable (f g hf hg) in
/-- The fundamental group of the segment with trivial edge group, relative to a nonempty set `T`
of darts, is the free product `A ∗ B` of its vertex groups, Mathlib's `Monoid.Coprod`. The vertex
group `A` maps by `Monoid.Coprod.inl`, the vertex group `B` by `Monoid.Coprod.inr`, and both
darts map to `1`. -/
noncomputable def equivCoprod (hT : T.Nonempty) :
    π₁Tree (segment f g hf hg) T ≃* Monoid.Coprod A B :=
  (equivPushoutI f g hf hg hT).trans (pushoutIEquivCoprod f g hf hg)

@[simp] theorem equivCoprod_of_false (hT : T.Nonempty) (a : A) :
    equivCoprod f g hf hg hT (of T false a) = Monoid.Coprod.inl a :=
  (congrArg (pushoutIEquivCoprod f g hf hg) (equivPushoutI_of hT false a)).trans
    (pushoutIEquivCoprod_of_false a)

@[simp] theorem equivCoprod_of_true (hT : T.Nonempty) (b : B) :
    equivCoprod f g hf hg hT (of T true b) = Monoid.Coprod.inr b :=
  (congrArg (pushoutIEquivCoprod f g hf hg) (equivPushoutI_of hT true b)).trans
    (pushoutIEquivCoprod_of_true b)

theorem equivCoprod_edge (hT : T.Nonempty) (e : SerreGraph.segment.E) :
    equivCoprod f g hf hg hT (edge T e) = 1 := by
  rw [edge_segment_eq_one hT, map_one]

@[simp] theorem equivCoprod_symm_inl (hT : T.Nonempty) (a : A) :
    (equivCoprod f g hf hg hT).symm (Monoid.Coprod.inl a) = of T false a :=
  (MulEquiv.symm_apply_eq _).2 (equivCoprod_of_false hT a).symm

@[simp] theorem equivCoprod_symm_inr (hT : T.Nonempty) (b : B) :
    (equivCoprod f g hf hg hT).symm (Monoid.Coprod.inr b) = of T true b :=
  (MulEquiv.symm_apply_eq _).2 (equivCoprod_of_true hT b).symm

end Coprod

end π₁Tree

variable {f g hf hg} in
/-- Every dart of the segment lies in its spanning tree `T`, so for any edge path `q` from `v₀` to
`b`, `π₁Equiv` sends the class in `π₁(𝔸, v₀)` of the based loop `q y q⁻¹` to the image of
`y ∈ A_b` in `π₁(𝔸, T)`. -/
@[simp]
theorem π₁Equiv_segment_vertexHom_mapPath {v₀ b : SerreGraph.segment.V}
    (q : SerreGraph.segment.Path v₀ b) (y : (segment f g hf hg).vertexGroup b) :
    π₁Equiv _ v₀ SerreGraph.segment_isTree.spanningTree
        (π₁.vertexHom ((dartPrefunctor _).mapPath q) y) =
      π₁Tree.of SerreGraph.segment_isTree.spanningTree.darts b y := by
  have hq : q.weight (fun {a b : SerreGraph.segment.V} (_ : a ⟶ b) =>
      (1 : π₁Tree (segment f g hf hg) SerreGraph.segment_isTree.spanningTree.darts)) = 1 :=
    SerreGraph.Path.weight_eq_one _ q (f := fun _ => 1) fun _ _ => rfl
  simp [π₁Equiv_apply, hq]

end segment

/-! ### The segment of a `Bool`-indexed family -/

section bool

variable {C : Type x} {G : Bool → Type w} [Group C] [∀ b, Group (G b)] (φ : ∀ b, C →* G b)
  (hφ : ∀ b, Function.Injective (φ b))

-- The vertices of the segment are the elements of `Bool` only up to unfolding: the indices
-- `id b` below keep the types `Bool` and `SerreGraph.segment.V` apart syntactically, so that
-- instance search finds the group structures of `G (id b)`. For the whole family over
-- `SerreGraph.segment.V`, which `Monoid.PushoutI.map` needs, instance search fails, and a local
-- instance supplies these structures.

/-- The vertex groups of the segment of `φ false` and `φ true` are the groups `G b`. -/
private def segmentVertexEquiv : ∀ b : SerreGraph.segment.V,
    (segment (φ false) (φ true) (hφ false) (hφ true)).vertexGroup b ≃* G (id b)
  | false => MulEquiv.refl (G false)
  | true => MulEquiv.refl (G true)

/-- For a `Bool`-indexed family of monomorphisms `φ b : C →* G b`, the amalgamated product of the
vertex groups of the segment of `φ false` and `φ true` is the amalgamated product
`G false ∗_C G true` of the family, `Monoid.PushoutI φ`. Both are amalgams of the same groups;
they differ only in their index types, the vertices of the segment and `Bool`. -/
noncomputable def segmentPushoutIEquiv :
    Monoid.PushoutI (segmentMaps (φ false) (φ true) (hφ false) (hφ true)) ≃* Monoid.PushoutI φ :=
  letI (b : SerreGraph.segment.V) : Group (G (id b)) := ‹∀ b : Bool, Group (G b)› b
  MonoidHom.toMulEquiv
    (Monoid.PushoutI.map (ι := SerreGraph.segment.V) (G' := fun b => G (id b))
      (φ := segmentMaps (φ false) (φ true) (hφ false) (hφ true)) (φ' := φ)
      (fun b => (segmentVertexEquiv φ hφ b).toMonoidHom) (.id C) fun b => by cases b <;> rfl)
    (Monoid.PushoutI.map (ι := SerreGraph.segment.V) (G := fun b => G (id b))
      (φ := φ) (φ' := segmentMaps (φ false) (φ true) (hφ false) (hφ true))
      (fun b => (segmentVertexEquiv φ hφ b).symm.toMonoidHom) (.id C) fun b => by cases b <;> rfl)
    (Monoid.PushoutI.map_comp_map_eq_id _ _ _ _ (fun b _ => by cases b <;> rfl) fun _ => rfl)
    (Monoid.PushoutI.map_comp_map_eq_id _ _ _ _ (fun b _ => by cases b <;> rfl) fun _ => rfl)

private theorem segmentPushoutIEquiv_of (b : SerreGraph.segment.V)
    (y : (segment (φ false) (φ true) (hφ false) (hφ true)).vertexGroup b) :
    segmentPushoutIEquiv φ hφ (Monoid.PushoutI.of b y) =
      Monoid.PushoutI.of (φ := φ) (id b) (segmentVertexEquiv φ hφ b y) :=
  letI (b : SerreGraph.segment.V) : Group (G (id b)) := ‹∀ b : Bool, Group (G b)› b
  Monoid.PushoutI.map_of ..

@[simp] theorem segmentPushoutIEquiv_of_false (y : G false) :
    segmentPushoutIEquiv φ hφ
        (Monoid.PushoutI.of (φ := segmentMaps (φ false) (φ true) (hφ false) (hφ true)) false y) =
      Monoid.PushoutI.of false y :=
  segmentPushoutIEquiv_of φ hφ false y

@[simp] theorem segmentPushoutIEquiv_of_true (y : G true) :
    segmentPushoutIEquiv φ hφ
        (Monoid.PushoutI.of (φ := segmentMaps (φ false) (φ true) (hφ false) (hφ true)) true y) =
      Monoid.PushoutI.of true y :=
  segmentPushoutIEquiv_of φ hφ true y

@[simp] theorem segmentPushoutIEquiv_symm_of_false (y : G false) :
    (segmentPushoutIEquiv φ hφ).symm (Monoid.PushoutI.of false y) =
      Monoid.PushoutI.of (φ := segmentMaps (φ false) (φ true) (hφ false) (hφ true)) false y :=
  (MulEquiv.symm_apply_eq _).2 (segmentPushoutIEquiv_of_false φ hφ y).symm

@[simp] theorem segmentPushoutIEquiv_symm_of_true (y : G true) :
    (segmentPushoutIEquiv φ hφ).symm (Monoid.PushoutI.of true y) =
      Monoid.PushoutI.of (φ := segmentMaps (φ false) (φ true) (hφ false) (hφ true)) true y :=
  (MulEquiv.symm_apply_eq _).2 (segmentPushoutIEquiv_of_true φ hφ y).symm

@[simp] theorem segmentPushoutIEquiv_base (c : C) :
    segmentPushoutIEquiv φ hφ (Monoid.PushoutI.base _ c) = Monoid.PushoutI.base φ c :=
  letI (b : SerreGraph.segment.V) : Group (G (id b)) := ‹∀ b : Bool, Group (G b)› b
  Monoid.PushoutI.map_base ..

@[simp] theorem segmentPushoutIEquiv_symm_base (c : C) :
    (segmentPushoutIEquiv φ hφ).symm (Monoid.PushoutI.base φ c) = Monoid.PushoutI.base _ c :=
  (MulEquiv.symm_apply_eq _).2 (segmentPushoutIEquiv_base φ hφ c).symm

end bool

/-! ### The loop: HNN extensions -/

section loop

variable {G : Type w} {C : Type x} [Group G] [Group C] (f g : C →* G)
  (hf : Function.Injective f) (hg : Function.Injective g)

/-- The isomorphism `range f ≃* range g`, `f c ↦ g c`, between the two images of the edge group
of the loop, along which the HNN extension of the loop is taken. -/
noncomputable def loopEquiv : f.range ≃* g.range :=
  (MonoidHom.ofInjective hf).symm.trans (MonoidHom.ofInjective hg)

@[simp] theorem loopEquiv_ofInjective (c : C) :
    loopEquiv f g hf hg (MonoidHom.ofInjective hf c) = MonoidHom.ofInjective hg c := by
  simp [loopEquiv]

@[simp] theorem loopEquiv_symm_ofInjective (c : C) :
    (loopEquiv f g hf hg).symm (MonoidHom.ofInjective hg c) = MonoidHom.ofInjective hf c := by
  simp [loopEquiv]

namespace π₁Tree

/-! The vertex `()` and the darts `((), b)` of `SerreGraph.rose Unit` are terms of `Unit` and
`Unit × Bool`, which are only definitionally the vertex and dart types of the loop. Generic
lemmas about `π₁Tree` therefore do not rewrite at them, and are instantiated explicitly below. -/

/-- The defining relation `e ω_e(c) = α_e(c) e` of the dart `((), false)` of the loop, with
`α = g` and `ω = f`. -/
private theorem edge_false_mul_of (c : C) :
    edge ∅ ((), false) * of (𝔸 := loop f g hf hg) ∅ () (f c) =
      of (𝔸 := loop f g hf hg) ∅ () (g c) * edge ∅ ((), false) := by
  have h := edge_mul_of_ω (𝔸 := loop f g hf hg) (T := ∅) ((), false) c
  rwa [loop_ω_false, loop_α_false] at h

/-- The map `π₁(loop, ∅) →* HNNExtension G (range f) (range g) φ`, the identity on `G`, sending
the dart `((), true)` to `t⁻¹` and its reverse `((), false)` to `t`. -/
private noncomputable def toHNN :
    π₁Tree (loop f g hf hg) ∅ →* HNNExtension G f.range g.range (loopEquiv f g hf hg) :=
  lift (fun _ => HNNExtension.of) (fun e => cond e.2 HNNExtension.t⁻¹ HNNExtension.t)
    (fun _ h => h.elim)
    (fun e => by
      obtain ⟨⟨⟩, _ | _⟩ := e
      · simp
      · simp)
    -- The edge group of every dart of the loop is `C` by definition.
    (fun e (c : C) => by
      obtain ⟨⟨⟩, _ | _⟩ := e
      · simp only [loop_ω_false, loop_α_false]
        have h := HNNExtension.equiv_eq_conj (φ := loopEquiv f g hf hg) (MonoidHom.ofInjective hf c)
        rw [loopEquiv_ofInjective] at h
        exact h.symm
      · simp only [loop_ω_true, loop_α_true]
        have h := HNNExtension.equiv_symm_eq_conj (φ := loopEquiv f g hf hg)
          (MonoidHom.ofInjective hg c)
        rw [loopEquiv_symm_ofInjective] at h
        exact h.symm)

private theorem toHNN_of (a : G) : toHNN f g hf hg (of ∅ () a) = HNNExtension.of a :=
  lift_of (𝔸 := loop f g hf hg) (T := ∅) _ _ _ _ _ () a

private theorem toHNN_edge_true : toHNN f g hf hg (edge ∅ ((), true)) = HNNExtension.t⁻¹ :=
  lift_edge (𝔸 := loop f g hf hg) (T := ∅) _ _ _ _ _ ((), true)

private theorem toHNN_edge_false : toHNN f g hf hg (edge ∅ ((), false)) = HNNExtension.t :=
  lift_edge (𝔸 := loop f g hf hg) (T := ∅) _ _ _ _ _ ((), false)

/-- The inverse map `HNNExtension G (range f) (range g) φ →* π₁(loop, ∅)`, the identity on `G`,
sending `t` to the dart `((), false)`. -/
private noncomputable def ofHNN :
    HNNExtension G f.range g.range (loopEquiv f g hf hg) →* π₁Tree (loop f g hf hg) ∅ :=
  HNNExtension.lift (of (𝔸 := loop f g hf hg) ∅ ()) (edge ∅ ((), false)) fun a => by
    obtain ⟨c, rfl⟩ := (MonoidHom.ofInjective hf).surjective a
    rw [loopEquiv_ofInjective]
    exact edge_false_mul_of f g hf hg c

private theorem ofHNN_of (a : G) : ofHNN f g hf hg (HNNExtension.of a) = of ∅ () a :=
  HNNExtension.lift_of ..

private theorem ofHNN_t : ofHNN f g hf hg HNNExtension.t = edge ∅ ((), false) :=
  HNNExtension.lift_t ..

/-- The fundamental group of the loop relative to its maximal tree `∅` is the HNN extension of
the vertex group `G` along `loopEquiv f g hf hg : range f ≃* range g`. The vertex group maps by
the identity and the dart `((), true)`, with `α = f` and `ω = g`, maps to `t⁻¹`, so that
Mathlib's relation `t f(c) t⁻¹ = g(c)` is the relation `e g(c) e⁻¹ = f(c)` of this dart. -/
noncomputable def equivHNNExtension :
    π₁Tree (loop f g hf hg) ∅ ≃* HNNExtension G f.range g.range (loopEquiv f g hf hg) :=
  MonoidHom.toMulEquiv (toHNN f g hf hg) (ofHNN f g hf hg)
    (hom_ext (fun _ => MonoidHom.ext fun a =>
        (congrArg (ofHNN f g hf hg) (toHNN_of f g hf hg a)).trans (ofHNN_of f g hf hg a))
      fun e => by
        obtain ⟨⟨⟩, _ | _⟩ := e
        · exact (congrArg (ofHNN f g hf hg) (toHNN_edge_false f g hf hg)).trans
            (ofHNN_t f g hf hg)
        · refine (congrArg (ofHNN f g hf hg) (toHNN_edge_true f g hf hg)).trans ?_
          rw [map_inv, ofHNN_t]
          exact (edge_rev (𝔸 := loop f g hf hg) (T := ∅) ((), false)).symm)
    (HNNExtension.hom_ext
      (MonoidHom.ext fun a =>
        (congrArg (toHNN f g hf hg) (ofHNN_of f g hf hg a)).trans (toHNN_of f g hf hg a))
      ((congrArg (toHNN f g hf hg) (ofHNN_t f g hf hg)).trans (toHNN_edge_false f g hf hg)))

@[simp] theorem equivHNNExtension_of (a : G) :
    equivHNNExtension f g hf hg (of ∅ () a) = HNNExtension.of a :=
  toHNN_of f g hf hg a

@[simp] theorem equivHNNExtension_edge_true :
    equivHNNExtension f g hf hg (edge ∅ ((), true)) = HNNExtension.t⁻¹ :=
  toHNN_edge_true f g hf hg

@[simp] theorem equivHNNExtension_edge_false :
    equivHNNExtension f g hf hg (edge ∅ ((), false)) = HNNExtension.t :=
  toHNN_edge_false f g hf hg

@[simp] theorem equivHNNExtension_symm_of (a : G) :
    (equivHNNExtension f g hf hg).symm (HNNExtension.of a) = of ∅ () a :=
  ofHNN_of f g hf hg a

@[simp] theorem equivHNNExtension_symm_t :
    (equivHNNExtension f g hf hg).symm HNNExtension.t = edge ∅ ((), false) :=
  ofHNN_t f g hf hg

/-- The vertex group of the loop embeds in its fundamental group relative to the maximal tree
`∅`: this is the normal form theorem for HNN extensions. -/
theorem of_injective_loop : Function.Injective (of (𝔸 := loop f g hf hg) ∅ ()) :=
  fun a a' h => HNNExtension.of_injective (φ := loopEquiv f g hf hg) <|
    (equivHNNExtension_of f g hf hg a).symm.trans
      ((congrArg _ h).trans (equivHNNExtension_of f g hf hg a'))

end π₁Tree

end loop

end GraphOfGroups

end TauCeti
