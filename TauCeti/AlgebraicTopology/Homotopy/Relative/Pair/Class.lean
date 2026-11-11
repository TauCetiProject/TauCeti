/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Homotopy.Relative.Pair.Homotopy

/-!
# The relative homotopy class of a map of pairs

Let `B` be a simply connected subspace of a space `Y` and `b ∈ B`. Every map of pairs
`g : (I × Iⁿ, ∂(I × Iⁿ)) → (Y, B)` is homotopic through maps of pairs to relative cubes at `b`,
all of which have the same class in `π_{n+1}(Y, B, b)`
(`TauCeti.RelHomotopyGroup.existsUnique_homotopicWith`). This file names that class,
`TauCeti.RelHomotopyGroup.pairClass b g`, and shows that it is compatible with the group structure
of `π_{n+1}(Y, B, b)` for maps of pairs that are not relative cubes:

* concatenating two maps of pairs `f` and `g` along a direction `j` of `Iⁿ`, when the face
  `t j = 1` of `f` agrees with the face `t j = 0` of `g` (`TauCeti.cubeTransAt`), multiplies their
  classes, in the order of `TauCeti.RelHomotopyGroup.mul_spec`
  (`TauCeti.RelHomotopyGroup.pairClass_cubeTransAt`);
* reversing a map of pairs along a direction of `Iⁿ` (`TauCeti.cubeSymmAt`) inverts its class
  (`TauCeti.RelHomotopyGroup.pairClass_cubeSymmAt`);
* a map with values in `B` has the trivial class
  (`TauCeti.RelHomotopyGroup.pairClass_eq_default_of_range_subset`).

These are the rules by which the singular cubes of `Y` with boundary in `B`, which span the
relative singular chains of `(Y, B)` after compression below the connectivity of the pair, map to
`π_{n+1}(Y, B, b)`. Unlike relative cubes, such cubes are not constant on any part of their
boundary, and the faces along which two of them are concatenated lie in `B` without being
constant.

## Proof of additivity

Let `f` and `g` share the face `W` along which they are concatenated. The deformation of a map of
pairs into a relative cube (`TauCeti.exists_homotopyWith_relGenLoop_of_openBox`) is driven by a
contraction of the open box `{1} × Iⁿ ∪ I × ∂Iⁿ`, which contains `W`. Contracting the open box
onto the point of its top face lying on `W`, along straight lines once the box has been pushed up
to the top face, keeps `W` inside itself. With the mirror-image contraction for `g`, the two
deformations agree on `W` at all times, so they glue to a homotopy through maps of pairs from the
concatenation of `f` and `g` to the concatenation of two relative cubes at a common point. Its
class is the product of their classes (`TauCeti.RelHomotopyGroup.mul_spec`), and transport to `b`
is a homomorphism (`TauCeti.RelHomotopyGroup.transport_mul`).

## Main definitions and results

* `TauCeti.RelHomotopyGroup.pairClass`: the class of a map of pairs into a simply connected
  subspace, characterised by `TauCeti.RelHomotopyGroup.pairClass_eq_mk_iff`.
* `TauCeti.RelHomotopyGroup.pairClass_cubeTransAt`, `TauCeti.RelHomotopyGroup.pairClass_cubeSymmAt`:
  compatibility with the group structure.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 4.1, the group structure on relative homotopy groups and the action of `π₁(A, x₀)`.
-/

public section

noncomputable section

universe u v

open Set Topology
open scoped unitInterval

namespace TauCeti

variable {N : Type v}

/-! ### The class of a map of pairs -/

namespace RelHomotopyGroup

variable {Y : TopCat.{u}} {B : Set Y} [SimplyConnectedSpace B]

section Class

variable [Finite N]

/-- **The relative homotopy class of a map of pairs.** If `B ⊆ Y` is simply connected and
`b ∈ B`, a map of pairs `g : (I × I^N, ∂(I × I^N)) → (Y, B)` is homotopic through maps of pairs to
relative cubes at `b`, all of which have the same class in `π_{n+1}(Y, B, b)`
(`TauCeti.RelHomotopyGroup.existsUnique_homotopicWith`). This is that class. -/
def pairClass (b : B) (g : C(I × (I^N), Y)) (hg : MapsTo g (Cube.prodBoundary N) B) :
    RelHomotopyGroup N ⟨TopPair.ofSubset B, b⟩ :=
  (existsUnique_homotopicWith b g hg).exists.choose

variable {b : B} {g g' : C(I × (I^N), Y)} {hg : MapsTo g (Cube.prodBoundary N) B}

/-- The class of a map of pairs is the class of a relative cube to which it is homotopic through
maps of pairs. -/
private theorem exists_pairClass_eq_mk : ∃ p : RelGenLoop N ⟨TopPair.ofSubset B, b⟩,
    pairClass b g hg = mk p ∧ g.HomotopicWith p.1 fun f ↦ MapsTo f (Cube.prodBoundary N) B :=
  let ⟨p, hp, h⟩ := (existsUnique_homotopicWith b g hg).exists.choose_spec
  ⟨p, hp.symm, h⟩

/-- **The characterisation of the class of a map of pairs**: it is the class of a relative cube
`p` exactly when the map is homotopic to `p` through maps of pairs. -/
theorem pairClass_eq_mk_iff {p : RelGenLoop N ⟨TopPair.ofSubset B, b⟩} :
    pairClass b g hg = mk p ↔ g.HomotopicWith p.1 fun f ↦ MapsTo f (Cube.prodBoundary N) B := by
  obtain ⟨q, hq, hgq⟩ := exists_pairClass_eq_mk (b := b) (g := g) (hg := hg)
  refine ⟨fun h ↦ hgq.trans ?_, fun h ↦ ?_⟩
  · have hqp := (mk_eq_mk.1 (hq.symm.trans h)).homotopicWith
    rwa [TopPair.range_ofSubset_map] at hqp
  · exact (existsUnique_homotopicWith b g hg).unique ⟨q, hq.symm, hgq⟩ ⟨p, rfl, h⟩

/-- The class of a relative cube, as a map of pairs, is its class. -/
@[simp]
theorem pairClass_coe (p : RelGenLoop N ⟨TopPair.ofSubset B, b⟩)
    (hp : MapsTo p.1 (Cube.prodBoundary N) B) : pairClass b p.1 hp = mk p :=
  pairClass_eq_mk_iff.2 (.refl _ hp)

/-- Maps of pairs homotopic through maps of pairs have the same class. -/
theorem pairClass_eq_of_homotopicWith (hg' : MapsTo g' (Cube.prodBoundary N) B)
    (h : g.HomotopicWith g' fun f ↦ MapsTo f (Cube.prodBoundary N) B) :
    pairClass b g hg = pairClass b g' hg' := by
  obtain ⟨q, hq, hgq⟩ := exists_pairClass_eq_mk (b := b) (g := g') (hg := hg')
  exact (pairClass_eq_mk_iff.2 (h.trans hgq)).trans hq.symm

end Class

section Transport

variable [Fintype N] {g : C(I × (I^N), Y)} {hg : MapsTo g (Cube.prodBoundary N) B}

/-- Changing the base point of the class of a map of pairs along a path in `B` gives its class at
the new base point. -/
theorem transport_pairClass {b b' : B} (γ : Path b b') :
    transport (X := ⟨TopPair.ofSubset B, b⟩) γ (pairClass b g hg) = pairClass b' g hg := by
  obtain ⟨p, hp, hgp⟩ := exists_pairClass_eq_mk (b := b) (g := g) (hg := hg)
  have hpq := (RelGenLoop.collarHomotopyAlong γ p).homotopicWith
  rw [TopPair.range_ofSubset_map] at hpq
  rw [hp]
  exact (transport_mk (X := ⟨TopPair.ofSubset B, b⟩) γ p).trans
    (pairClass_eq_mk_iff.2 (hgp.trans hpq)).symm

/-- The class at `b` of a map of pairs homotopic, through maps of pairs, to a relative cube `p`
at another point `y` of `B` is the transport of the class of `p` along any path from `y` to
`b`. -/
theorem pairClass_eq_transport_mk {b y : B} (p : RelGenLoop N ⟨TopPair.ofSubset B, y⟩)
    (h : g.HomotopicWith p.1 fun f ↦ MapsTo f (Cube.prodBoundary N) B) (γ : Path y b) :
    pairClass b g hg = transport (X := ⟨TopPair.ofSubset B, y⟩) γ (mk p) := by
  rw [← transport_pairClass γ, pairClass_eq_mk_iff.2 h]

end Transport

section Laws

variable [Finite N] {b : B} {g : C(I × (I^N), Y)} {hg : MapsTo g (Cube.prodBoundary N) B}

/-- **A map of pairs with values in `B` has the trivial class.** -/
theorem pairClass_eq_default_of_range_subset {b : B} (h : range g ⊆ B) :
    pairClass b g hg = default := by
  have := Fintype.ofFinite N
  -- Contracting the cube deforms `g` into a constant map, through maps with values in `B`.
  obtain ⟨y, hy⟩ : ∃ y : B, (y : Y) = g (1, fun _ ↦ 0) := ⟨⟨_, h ⟨_, rfl⟩⟩, rfl⟩
  have hc : g.HomotopicWith (RelGenLoop.const : RelGenLoop N ⟨TopPair.ofSubset B, y⟩).1
      fun f ↦ MapsTo f (Cube.prodBoundary N) B :=
    ⟨{ toFun := fun q ↦ g (openBoxContractionTo (fun _ ↦ 0) q.1 q.2)
       continuous_toFun := g.continuous.comp (continuous_openBoxContractionTo _)
       map_zero_left := fun w ↦ by simp [openBoxContractionTo_zero]
       map_one_left := fun w ↦ by
         simp only [openBoxContractionTo_one]
         exact hy.symm.trans (RelGenLoop.const_apply (X := ⟨TopPair.ofSubset B, y⟩) w).symm
       prop' := fun _ _ _ ↦ h ⟨_, rfl⟩ }⟩
  rw [pairClass_eq_transport_mk _ hc (PathConnectedSpace.somePath y b), ← default_eq]
  exact transport_default (X := ⟨TopPair.ofSubset B, y⟩) _

variable [DecidableEq N] [Nonempty N]

/-- **The class of a concatenation of maps of pairs.** Let `f` and `g` be maps of pairs
`(I × I^N, ∂(I × I^N)) → (Y, B)` into a simply connected subspace `B`, such that the face `t j = 1`
of `f` agrees with the face `t j = 0` of `g`. The class of their concatenation along `j` is the
product of their classes, in the order of `TauCeti.RelHomotopyGroup.mul_spec`. -/
theorem pairClass_cubeTransAt (j : N) {f g : C(I × (I^N), Y)}
    (hf : MapsTo f (Cube.prodBoundary N) B) (hg : MapsTo g (Cube.prodBoundary N) B)
    (h : ∀ s t, f (s, Function.update t j 1) = g (s, Function.update t j 0))
    (hfg : MapsTo (cubeTransAt j f g h) (Cube.prodBoundary N) B) :
    pairClass b (cubeTransAt j f g h) hfg = pairClass b g hg * pairClass b f hf := by
  have := Fintype.ofFinite N
  -- Deform `f` and `g` into relative cubes by contracting their open boxes onto the points of
  -- their top faces on the common face.
  have hJ (c : I^N) := exists_homotopyWith_relGenLoop_of_openBox (Y := Y) (B := B)
    (openBoxContractionTo c)
    (continuous_openBoxContractionTo c) (openBoxContractionTo_zero c)
    (fun hz t ↦ openBoxContractionTo_mem_prodBoundary c hz t)
    (fun _ ↦ openBoxContractionTo_one c _)
  obtain ⟨y, hy, p, F, hF⟩ := hJ (Function.update cubeCenter j 1) f hf
  obtain ⟨y', hy', q, G, hG⟩ := hJ (Function.update cubeCenter j 0) g hg
  obtain rfl : y = y' := Subtype.ext (hy.trans ((h 1 cubeCenter).trans hy'.symm))
  -- The two deformations agree on the common face at all times.
  have hFG (t s : I) (z : I^N) : F.toContinuousMap (t, (s, Function.update z j 1)) =
      G.toContinuousMap (t, (s, Function.update z j 0)) := by
    have hb (e : I) (he : e = 0 ∨ e = 1) : Function.update z j e ∈ Cube.boundary N :=
      ⟨j, by rwa [Function.update_self]⟩
    rw [hF t (.inr (hb 1 (.inr rfl))), hG t (.inr (hb 0 (.inl rfl))),
      openBoxContractionTo_update, openBoxContractionTo_update]
    exact h _ _
  -- Glue them into a homotopy through maps of pairs from the concatenation of `f` and `g` to the
  -- concatenation of the two relative cubes.
  have hpq : (cubeTransAt j f g h).HomotopicWith (RelGenLoop.transAt j p q).1
      fun f ↦ MapsTo f (Cube.prodBoundary N) B :=
    (congrArg (fun k ↦ (cubeTransAt j f g h).HomotopicWith k
      fun f ↦ MapsTo f (Cube.prodBoundary N) B) (RelGenLoop.coe_transAt j p q)).mpr
        (homotopicWith_cubeTransAt F G hFG)
  let γ := PathConnectedSpace.somePath y b
  rw [pairClass_eq_transport_mk _ hpq γ, ← mul_spec]
  exact (transport_mul (X := ⟨TopPair.ofSubset B, y⟩) γ _ _).trans (congrArg₂ (· * ·)
    (pairClass_eq_transport_mk _ ⟨G⟩ γ).symm (pairClass_eq_transport_mk _ ⟨F⟩ γ).symm)

/-- **The class of a reversed map of pairs.** Reversing a map of pairs
`(I × I^N, ∂(I × I^N)) → (Y, B)` into a simply connected subspace `B` along a direction `j` inverts
its class. -/
theorem pairClass_cubeSymmAt (j : N) {g : C(I × (I^N), Y)}
    (hg : MapsTo g (Cube.prodBoundary N) B)
    (hg' : MapsTo (cubeSymmAt j g) (Cube.prodBoundary N) B) :
    pairClass b (cubeSymmAt j g) hg' = (pairClass b g hg)⁻¹ := by
  have := Fintype.ofFinite N
  obtain ⟨y, -, p, ⟨G⟩⟩ := exists_homotopicWith_relGenLoop g hg
  -- Reversing a homotopy from `g` to `p` gives a homotopy from the reversal of `g` to that of `p`.
  let H := G.toContinuousMap.comp ((ContinuousMap.id I).prodMap (cubeSymmAt j (.id _)))
  have hH (t : I) (w : I × I^N) :
      H (t, w) = G.toContinuousMap (t, (w.1, fun i ↦ if i = j then σ (w.2 j) else w.2 i)) :=
    congrArg (fun x ↦ G.toContinuousMap (t, x)) (cubeSymmAt_apply j (.id _) w)
  have hp : (cubeSymmAt j g).HomotopicWith (RelGenLoop.symmAt j p).1
      fun f ↦ MapsTo f (Cube.prodBoundary N) B :=
    ⟨{ toContinuousMap := H
       map_zero_left := fun w ↦
         (hH 0 w).trans ((G.map_zero_left _).trans (cubeSymmAt_apply j g w).symm)
       map_one_left := fun w ↦ (hH 1 w).trans ((G.map_one_left _).trans <| by
         rw [RelGenLoop.coe_symmAt]
         exact (cubeSymmAt_apply j _ w).symm)
       prop' := fun t ↦ (mapsTo_cubeSymmAt (j := j) (G.prop t)).congr fun w _ ↦
         (cubeSymmAt_apply j _ w).trans (hH t w).symm }⟩
  let γ := PathConnectedSpace.somePath y b
  rw [pairClass_eq_transport_mk _ hp γ, ← inv_spec, pairClass_eq_transport_mk _ ⟨G⟩ γ]
  exact (mulEquivOfPath_apply (X := ⟨TopPair.ofSubset B, y⟩) γ _).symm.trans
    ((map_inv _ _).trans
      (congrArg (·⁻¹) (mulEquivOfPath_apply (X := ⟨TopPair.ofSubset B, y⟩) γ _)))

end Laws

end RelHomotopyGroup

end TauCeti
