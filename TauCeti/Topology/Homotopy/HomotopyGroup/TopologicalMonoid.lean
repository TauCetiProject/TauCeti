/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.ContinuousMap.Algebra
public import TauCeti.Topology.Homotopy.HomotopyGroup.Product

import TauCeti.Topology.Homotopy.HomotopyGroup.Homotopy

/-!
# Pointwise products and inner conjugation on homotopy groups of topological monoids and groups

Let `M` be a space with a continuous multiplication and a two-sided unit `1`, for instance a
topological group or a Moore loop space. Two based maps `f : X → M` and `g : Y → M`, sending the
base points to `1`, have the pointwise product `(p, q) ↦ f p * g q : X × Y → M`. This file shows
that in positive dimensions it acts on homotopy groups by

`(f * g)_* (a × b) = f_* a * g_* b`,

where `a × b` is the class of `X × Y` with coordinates `a` and `b` (`HomotopyGroup.prod`). Since
`1` is a strict unit, `(f * g)_* (a × 1) = f_* a` and `(f * g)_* (1 × b) = g_* b` already on
generalized loops, and the general formula follows because `(f * g)_*` is a homomorphism.

Consequently the pointwise product induces a bijection on a homotopy group as soon as one factor
induces a bijection there and the other factor has a trivial source group
(`HomotopyGroup.bijective_map_mul_of_bijective_of_subsingleton`). This is how a product of a map
realizing the low homotopy groups with a map realizing the high ones is recognized as a weak
homotopy equivalence, as for the splitting of the loop space of a complex projective space.
More generally, it induces a bijection when `g_*` is injective with image the kernel of a
homomorphism `φ` out of the homotopy group of `M` and `φ ∘ f_*` is bijective
(`HomotopyGroup.bijective_map_mul_of_bijective_comp`): `f_*` then splits the extension of the
image of `φ` by the image of `g_*`, as for the loop space of a quaternionic projective space.

For loops, `f = g = id`, the formula is the first half of the Eckmann--Hilton argument, the
fundamental-group case of which is `FundamentalGroup.cast_map_prod_mul`.

In a topological group `G`, any path from `1` to `w` sweeps out a homotopy relative to `{1}` from
the identity map to the inner automorphism `MulAut.conj w`, since `γ(t) * 1 * γ(t)⁻¹ = 1` at every
instant (`ContinuousMap.homotopicRel_conj_of_joined`, `ContinuousMap.homotopicRel_conj`). Inner
conjugation by an element in the identity path component—and in particular by every element when `G`
is path-connected—therefore acts as the identity on `π_N(G, 1)` in every dimension `N`
(`HomotopyGroup.map_conj_eq_id_of_joined`, `HomotopyGroup.map_conj_eq_id`).

## Main results

* `HomotopyGroup.map_mul_prod`: `(f * g)_* (a × b) = f_* a * g_* b`.
* `HomotopyGroup.bijective_map_mul_of_bijective_of_subsingleton`,
  `HomotopyGroup.bijective_map_mul_of_subsingleton_of_bijective`: the pointwise product is
  bijective on a homotopy group if one factor is and the source group of the other is trivial.
* `HomotopyGroup.bijective_map_mul_of_bijective_comp`: the pointwise product is bijective on a
  homotopy group if `g_*` is injective with image the kernel of a homomorphism `φ`, and
  `φ ∘ f_*` is bijective.
* `ContinuousMap.homotopicRel_conj_of_joined`, `ContinuousMap.homotopicRel_conj`: inner conjugation
  by an element joined by a path to `1` is homotopic relative to `{1}` to the identity map.
* `HomotopyGroup.map_conj_eq_id_of_joined`, `HomotopyGroup.map_conj_eq_id`,
  `HomotopyGroup.mapHom_conj_eq_id`: inner conjugation acts trivially on `π_N(G, 1)`.
-/

public section

open scoped Topology.Homotopy

namespace HomotopyGroup

variable {N X Y M : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace M]
  [MulOneClass M] [ContinuousMul M] {x : X} {y : Y}

/-- The pointwise product `(p, q) ↦ f p * g q` of two maps sending the base points to `1` sends
the base point of `X × Y` to `1`. -/
theorem mul_comp_fst_comp_snd_apply_eq_one {f : C(X, M)} {g : C(Y, M)} (hf : f x = 1)
    (hg : g y = 1) :
    (f.comp ContinuousMap.fst * g.comp ContinuousMap.snd : C(X × Y, M)) (x, y) = 1 := by
  simp [hf, hg]

section Group

variable [DecidableEq N] [Nonempty N]

/-- Multiplying pointwise by a map sending the base point to the unit does not change the class of
a generalized loop: `(f * g)_* (a × 1) = f_* a`. -/
theorem map_mul_prod_one_right (f : C(X, M)) (g : C(Y, M)) (hf : f x = 1) (hg : g y = 1)
    (a : HomotopyGroup N X x) :
    map (f.comp ContinuousMap.fst * g.comp ContinuousMap.snd : C(X × Y, M))
        (mul_comp_fst_comp_snd_apply_eq_one hf hg) (prod a 1) = map f hf a := by
  induction a using Quotient.inductionOn with
  | h p =>
  rw [← mk_const_eq_one, prod_mk, map_mk, map_mk]
  exact congrArg _ (GenLoop.ext _ _ fun t ↦ by simp [GenLoop.map_apply, hg])

/-- Multiplying pointwise a map sending the base point to the unit does not change the class of a
generalized loop: `(f * g)_* (1 × b) = g_* b`. -/
theorem map_mul_prod_one_left (f : C(X, M)) (g : C(Y, M)) (hf : f x = 1) (hg : g y = 1)
    (b : HomotopyGroup N Y y) :
    map (f.comp ContinuousMap.fst * g.comp ContinuousMap.snd : C(X × Y, M))
        (mul_comp_fst_comp_snd_apply_eq_one hf hg) (prod 1 b) = map g hg b := by
  induction b using Quotient.inductionOn with
  | h q =>
  rw [← mk_const_eq_one, prod_mk, map_mk, map_mk]
  exact congrArg _ (GenLoop.ext _ _ fun t ↦ by simp [GenLoop.map_apply, hf])

/-- **The pointwise product of maps into a topological monoid acts on homotopy groups by the
product of the induced maps.** For based maps `f : X → M` and `g : Y → M` sending the base points
to the unit, the map `(p, q) ↦ f p * g q` sends the class with coordinates `a` and `b` to
`f_* a * g_* b`. -/
@[simp]
theorem map_mul_prod (f : C(X, M)) (g : C(Y, M)) (hf : f x = 1) (hg : g y = 1)
    (a : HomotopyGroup N X x) (b : HomotopyGroup N Y y) :
    map (f.comp ContinuousMap.fst * g.comp ContinuousMap.snd : C(X × Y, M))
        (mul_comp_fst_comp_snd_apply_eq_one hf hg) (prod a b) = map f hf a * map g hg b := by
  rw [← map_mul_prod_one_right f g hf hg, ← map_mul_prod_one_left f g hf hg, ← map_mul,
    ← prod_mul, mul_one, one_mul]

end Group

/-- The pointwise product `(p, q) ↦ f p * g q` induces a bijection on a homotopy group of positive
dimension if `g_*` is injective there, its image is the kernel of a homomorphism `φ` out of the
homotopy group of `M`, and `φ ∘ f_*` is bijective. -/
theorem bijective_map_mul_of_bijective_comp [DecidableEq N] [Nonempty N] {G : Type*} [Group G]
    {f : C(X, M)} {g : C(Y, M)} (hf : f x = 1) (hg : g y = 1) (φ : HomotopyGroup N M 1 →* G)
    (hφf : Function.Bijective (φ ∘ map (N := N) f hf))
    (hgi : Function.Injective (map (N := N) g hg))
    (hφg : ∀ c, φ c = 1 ↔ c ∈ Set.range (map (N := N) g hg)) :
    Function.Bijective (map (N := N) (f.comp ContinuousMap.fst * g.comp ContinuousMap.snd :
      C(X × Y, M)) (mul_comp_fst_comp_snd_apply_eq_one hf hg)) := by
  -- Read on coordinates, the induced map is `(a, b) ↦ f_* a * g_* b`.
  have h : map (N := N) (f.comp ContinuousMap.fst * g.comp ContinuousMap.snd : C(X × Y, M))
      (mul_comp_fst_comp_snd_apply_eq_one hf hg) =
        (fun p ↦ map f hf p.1 * map g hg p.2) ∘ prodEquiv x y := by
    funext c
    obtain ⟨⟨a, b⟩, rfl⟩ := (prodEquiv x y).symm.surjective c
    rw [prodEquiv_symm_apply, map_mul_prod f g hf hg]
    simp
  rw [h]
  refine Function.Bijective.comp ⟨fun ⟨a, b⟩ ⟨a', b'⟩ hab ↦ ?_, fun c ↦ ?_⟩
    (prodEquiv x y).bijective
  · -- `φ` kills the `g_*` factor, so the `f_*` factors agree, and then so do the others.
    have hφ (b : HomotopyGroup N Y y) : φ (map g hg b) = 1 := (hφg _).2 ⟨b, rfl⟩
    have ha : a = a' := hφf.1 (by simpa [hφ] using congrArg φ hab)
    subst ha
    exact Prod.ext rfl (hgi (mul_left_cancel hab))
  · -- Correct `c` by the `f_*` class with the same image under `φ`; the rest lies in the image
    -- of `g_*`.
    obtain ⟨a, ha⟩ := hφf.2 (φ c)
    rw [Function.comp_apply] at ha
    obtain ⟨b, hb⟩ := (hφg ((map f hf a)⁻¹ * c)).1 <| by
      rw [_root_.map_mul, _root_.map_inv, ha, inv_mul_cancel]
    exact ⟨(a, b), by simp [hb]⟩

/-- The pointwise product `(p, q) ↦ f p * g q` induces a bijection on a homotopy group of positive
dimension if `f` does and the corresponding homotopy group of `Y` is trivial. -/
theorem bijective_map_mul_of_bijective_of_subsingleton [Nonempty N] {f : C(X, M)} {g : C(Y, M)}
    (hf : f x = 1) (hg : g y = 1) (hfb : Function.Bijective (map (N := N) f hf))
    [Subsingleton (HomotopyGroup N Y y)] :
    Function.Bijective (map (N := N) (f.comp ContinuousMap.fst * g.comp ContinuousMap.snd :
      C(X × Y, M)) (mul_comp_fst_comp_snd_apply_eq_one hf hg)) := by
  classical
  -- Take `φ = id`: the image of `g_*` is trivial.
  refine bijective_map_mul_of_bijective_comp hf hg (MonoidHom.id _) hfb
    (Function.injective_of_subsingleton _) fun c ↦ ⟨fun hc ↦ ⟨1, ?_⟩, fun ⟨b, hb⟩ ↦ ?_⟩
  · rw [map_one, ← MonoidHom.id_apply _ c, hc]
  · rw [MonoidHom.id_apply, ← hb, Subsingleton.elim b 1, map_one]

/-- The pointwise product `(p, q) ↦ f p * g q` induces a bijection on a homotopy group of positive
dimension if `g` does and the corresponding homotopy group of `X` is trivial. -/
theorem bijective_map_mul_of_subsingleton_of_bijective [Nonempty N] {f : C(X, M)} {g : C(Y, M)}
    (hf : f x = 1) (hg : g y = 1) [Subsingleton (HomotopyGroup N X x)]
    (hgb : Function.Bijective (map (N := N) g hg)) :
    Function.Bijective (map (N := N) (f.comp ContinuousMap.fst * g.comp ContinuousMap.snd :
      C(X × Y, M)) (mul_comp_fst_comp_snd_apply_eq_one hf hg)) := by
  classical
  -- Take `φ` to the trivial group: the image of `g_*` is everything.
  exact bijective_map_mul_of_bijective_comp hf hg (1 : HomotopyGroup N M 1 →* Unit)
    (Function.bijective_of_subsingleton' _) hgb.1
    fun c ↦ iff_of_true (Subsingleton.elim _ _) (hgb.2 c)

end HomotopyGroup

namespace ContinuousMap

variable {G : Type*} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]

/-- **Inner conjugation by an element in the identity path component is pointed-homotopic to the
identity.** Given `Joined 1 w` in a topological group `G`, conjugating along a path from `1` to `w`
defines a homotopy relative to `{(1 : G)}` from `ContinuousMap.id G` to `MulAut.conj w`. -/
theorem homotopicRel_conj_of_joined {w : G} (hw : Joined (1 : G) w) :
    (ContinuousMap.id G).HomotopicRel
      ⟨MulAut.conj w, IsTopologicalGroup.continuous_conj w⟩ {(1 : G)} := by
  let γ : Path (1 : G) w := hw.somePath
  refine ⟨⟨⟨⟨fun tx : unitInterval × G ↦ γ tx.1 * tx.2 * (γ tx.1)⁻¹, by fun_prop⟩, ?_, ?_⟩, ?_⟩⟩
  · intro x
    simp [γ]
  · intro x
    simp only [γ, Path.target]
    rfl
  · intro t x hx
    rw [Set.mem_singleton_iff.mp hx]
    simp

/-- In a path-connected topological group, every inner automorphism is homotopic relative to
`{(1 : G)}` to the identity map. -/
theorem homotopicRel_conj [PathConnectedSpace G] (w : G) :
    (ContinuousMap.id G).HomotopicRel
      ⟨MulAut.conj w, IsTopologicalGroup.continuous_conj w⟩ {(1 : G)} :=
  homotopicRel_conj_of_joined (PathConnectedSpace.joined 1 w)

end ContinuousMap

namespace HomotopyGroup

variable {N G : Type*} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]

/-- **Inner conjugation by an element joined by a path to `1` acts trivially on every homotopy
group at `1`.** -/
theorem map_conj_eq_id_of_joined {w : G} (hw : Joined (1 : G) w)
    (h : (⟨MulAut.conj w, IsTopologicalGroup.continuous_conj w⟩ : C(G, G)) 1 = 1 :=
      (MulAut.conj w).map_one)
    (a : HomotopyGroup N G 1) :
    map ⟨MulAut.conj w, IsTopologicalGroup.continuous_conj w⟩ h a = a := by
  have heq := map_eq_of_homotopicRel (N := N) (x := (1 : G)) (y := (1 : G)) rfl
    (Set.mem_singleton (1 : G)) (ContinuousMap.homotopicRel_conj_of_joined hw)
  exact (map_congr rfl h _ a).trans ((congrFun heq a).symm.trans (map_id_apply a))

/-- **In a path-connected topological group, inner conjugation acts as the identity on every
homotopy group at `1`.** -/
@[simp]
theorem map_conj_eq_id [PathConnectedSpace G] (w : G)
    (h : (⟨MulAut.conj w, IsTopologicalGroup.continuous_conj w⟩ : C(G, G)) 1 = 1 :=
      (MulAut.conj w).map_one)
    (a : HomotopyGroup N G 1) :
    map ⟨MulAut.conj w, IsTopologicalGroup.continuous_conj w⟩ h a = a :=
  map_conj_eq_id_of_joined (PathConnectedSpace.joined 1 w) h a

/-- In a path-connected topological group, inner conjugation induces the identity homomorphism on
positive-dimensional homotopy groups at `1`. -/
@[simp]
theorem mapHom_conj_eq_id [DecidableEq N] [Nonempty N] [PathConnectedSpace G] (w : G)
    (h : (⟨MulAut.conj w, IsTopologicalGroup.continuous_conj w⟩ : C(G, G)) 1 = 1 :=
      (MulAut.conj w).map_one) :
    mapHom (N := N) ⟨MulAut.conj w, IsTopologicalGroup.continuous_conj w⟩ h =
      MonoidHom.id (HomotopyGroup N G 1) :=
  MonoidHom.ext (map_conj_eq_id w h)

end HomotopyGroup
