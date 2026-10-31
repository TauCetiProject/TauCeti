/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GraphOfGroups.Presentation
public import Mathlib.GroupTheory.PushoutI
public import Mathlib.GroupTheory.HNNExtension

/-!
# One-edge graphs of groups: amalgamated products and HNN extensions

A graph of groups with a single geometric edge is either a segment or a loop, and its
fundamental group is Mathlib's amalgamated product or HNN extension respectively.

* For the segment `GraphOfGroups.segment f g hf hg` with vertex groups `A`, `B`, edge group `C`
  and monomorphisms `f : C →* A`, `g : C →* B`, the group `π₁(𝔸, T)` relative to any nonempty
  set `T` of darts (for instance the maximal tree, which is the whole segment) is the amalgamated
  product `A ∗_C B`, Mathlib's `Monoid.PushoutI` indexed by the two vertices. The isomorphism is
  the identity on `A` and on `B` and kills both darts.
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
* `TauCeti.GraphOfGroups.loopEquiv`: the isomorphism `range f ≃* range g`, `f c ↦ g c`, along
  which the HNN extension of the loop is taken.
* `TauCeti.GraphOfGroups.π₁Tree.equivHNNExtension`: `π₁(loop, ∅) ≃* HNNExtension G (range f)
  (range g) (loopEquiv f g hf hg)`.

## Main results

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
private theorem edge_segment_eq_one (hT : T.Nonempty) (e : SerreGraph.segment.E) :
    (edge T e : π₁Tree (segment f g hf hg) T) = 1 := by
  obtain ⟨e', he'⟩ := hT
  obtain rfl | rfl : e = e' ∨ e = SerreGraph.segment.rev e' := by
    cases e <;> cases e' <;> first | exact .inl rfl | exact .inr rfl
  · exact edge_eq_one he'
  · rw [edge_rev, edge_eq_one he', inv_one]

/-- In `π₁(segment, T)` with `T` nonempty, the two images of the edge group agree: the dart
`false` is trivial, so its relation `e g(c) e⁻¹ = f(c)` becomes `g(c) = f(c)`. -/
private theorem of_true_eq_of_false (hT : T.Nonempty) (c : C) :
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
    (hom_ext (fun b => by ext; simp) fun e => by simp [edge_segment_eq_one hT])
    (by
      have : Nonempty SerreGraph.segment.V := ⟨false⟩
      exact Monoid.PushoutI.hom_ext_nonempty fun b => by ext; simp)

@[simp] theorem equivPushoutI_of (hT : T.Nonempty) (b : SerreGraph.segment.V)
    (a : (segment f g hf hg).vertexGroup b) :
    equivPushoutI f g hf hg hT (of T b a) = Monoid.PushoutI.of b a :=
  lift_of ..

@[simp] theorem equivPushoutI_edge (hT : T.Nonempty) (e : SerreGraph.segment.E) :
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
  have hφ : ∀ b, Function.Injective (segmentMaps f g hf hg b) := fun b => by
    cases b
    · exact hf
    · exact hg
  intro a a' h
  refine Monoid.PushoutI.of_injective hφ b ?_
  rw [← equivPushoutI_of hT, ← equivPushoutI_of hT, h]

end π₁Tree

end segment

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
