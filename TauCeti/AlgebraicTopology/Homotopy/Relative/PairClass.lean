/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Homotopy.Relative.PairHomotopy

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

* `TauCeti.cubeTransAt`, `TauCeti.cubeSymmAt`: concatenation and reversal of maps out of a cube
  along a direction of `Iⁿ`, extending `TauCeti.RelGenLoop.transAt` and
  `TauCeti.RelGenLoop.symmAt`.
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

/-! ### Concatenation and reversal of maps out of a cube -/

section Concatenation

variable {Z Y : Type*} [TopologicalSpace Z] [TopologicalSpace Y] [DecidableEq N]

/-- Concatenation of two maps `f g : Z × I^N → Y` along a direction `j : N` of the cube `I^N`,
when the face `t j = 1` of `f` agrees with the face `t j = 0` of `g`: the map runs `f` on the half
`t j ≤ 1 / 2` and `g` on the other half, both reparametrised. For relative cubes this is
`TauCeti.RelGenLoop.transAt` (`TauCeti.RelGenLoop.coe_transAt`). -/
def cubeTransAt (j : N) (f g : C(Z × (I^N), Y))
    (h : ∀ s t, f (s, Function.update t j 1) = g (s, Function.update t j 0)) :
    C(Z × (I^N), Y) where
  toFun w := if (w.2 j : ℝ) ≤ 1 / 2
    then f (w.1, Function.update w.2 j (projIcc 0 1 zero_le_one (2 * w.2 j)))
    else g (w.1, Function.update w.2 j (projIcc 0 1 zero_le_one (2 * w.2 j - 1)))
  continuous_toFun := by
    refine Continuous.if_le (by fun_prop) (by fun_prop) (by fun_prop) continuous_const
      fun w hw ↦ ?_
    rw [hw]
    convert h w.1 w.2 using 4 <;> ext <;> norm_num

theorem cubeTransAt_apply (j : N) (f g : C(Z × (I^N), Y))
    (h : ∀ s t, f (s, Function.update t j 1) = g (s, Function.update t j 0)) (w : Z × I^N) :
    cubeTransAt j f g h w = if (w.2 j : ℝ) ≤ 1 / 2
      then f (w.1, Function.update w.2 j (projIcc 0 1 zero_le_one (2 * w.2 j)))
      else g (w.1, Function.update w.2 j (projIcc 0 1 zero_le_one (2 * w.2 j - 1))) :=
  (rfl)

/-- Reversal of a map `f : Z × I^N → Y` along a direction `j : N` of the cube `I^N`, by
`t j ↦ 1 - t j`. For relative cubes this is `TauCeti.RelGenLoop.symmAt`
(`TauCeti.RelGenLoop.coe_symmAt`). -/
def cubeSymmAt (j : N) (f : C(Z × (I^N), Y)) : C(Z × (I^N), Y) :=
  f.comp ⟨fun w ↦ (w.1, fun i ↦ if i = j then σ (w.2 j) else w.2 i),
    continuous_fst.prodMk (continuous_pi fun i ↦ by split_ifs <;> fun_prop)⟩

@[simp]
theorem cubeSymmAt_apply (j : N) (f : C(Z × (I^N), Y)) (w : Z × I^N) :
    cubeSymmAt j f w = f (w.1, fun i ↦ if i = j then σ (w.2 j) else w.2 i) :=
  (rfl)

/-- Each half of the concatenation along `j` sends the boundary of `I × I^N` into the boundary of
`I × I^N`. -/
private theorem update_mem_prodBoundary {j : N} {w : I × I^N} (hw : w ∈ Cube.prodBoundary N)
    {a : I} (ha : w.2 j = 0 ∨ w.2 j = 1 → a = w.2 j) :
    (w.1, Function.update w.2 j a) ∈ Cube.prodBoundary N := by
  rcases Cube.mem_prodBoundary_iff.1 hw with hs | ⟨i, hi⟩
  · exact Cube.mem_prodBoundary_iff.2 (.inl hs)
  refine Cube.mem_prodBoundary_iff.2 (.inr ⟨i, ?_⟩)
  dsimp only
  by_cases hij : i = j
  · subst hij
    rwa [Function.update_self, ha hi]
  · rwa [Function.update_of_ne hij]

theorem mapsTo_cubeTransAt {B : Set Y} {j : N} {f g : C(I × (I^N), Y)}
    (hf : MapsTo f (Cube.prodBoundary N) B) (hg : MapsTo g (Cube.prodBoundary N) B)
    (h : ∀ s t, f (s, Function.update t j 1) = g (s, Function.update t j 0)) :
    MapsTo (cubeTransAt j f g h) (Cube.prodBoundary N) B := by
  intro w hw
  rw [cubeTransAt_apply]
  split_ifs with hj
  · refine hf (update_mem_prodBoundary hw fun h0 ↦ ?_)
    rcases h0 with h0 | h0 <;> rw [h0] at hj ⊢
    · simp
    · norm_num at hj
  · refine hg (update_mem_prodBoundary hw fun h0 ↦ ?_)
    rcases h0 with h0 | h0 <;> rw [h0] at hj ⊢
    · norm_num at hj
    · ext; norm_num

theorem mapsTo_cubeSymmAt {B : Set Y} {j : N} {f : C(I × (I^N), Y)}
    (hf : MapsTo f (Cube.prodBoundary N) B) :
    MapsTo (cubeSymmAt j f) (Cube.prodBoundary N) B := by
  intro w hw
  refine hf (Cube.mem_prodBoundary_iff.2 ?_)
  rcases Cube.mem_prodBoundary_iff.1 hw with hs | ⟨i, hi⟩
  · exact .inl hs
  refine .inr ⟨i, ?_⟩
  by_cases hij : i = j
  · subst hij
    rcases hi with hi | hi <;> simp [hi]
  · simpa [hij] using hi

/-- Concatenating along `j` two homotopies through maps of pairs that agree on the common face at
all times gives a homotopy through maps of pairs between the concatenations. -/
theorem homotopicWith_cubeTransAt {B : Set Y} {j : N} {f g f' g' : C(I × (I^N), Y)}
    {h : ∀ s t, f (s, Function.update t j 1) = g (s, Function.update t j 0)}
    {h' : ∀ s t, f' (s, Function.update t j 1) = g' (s, Function.update t j 0)}
    (F : f.HomotopyWith f' fun k ↦ MapsTo k (Cube.prodBoundary N) B)
    (G : g.HomotopyWith g' fun k ↦ MapsTo k (Cube.prodBoundary N) B)
    (hFG : ∀ t s z, F (t, (s, Function.update z j 1)) = G (t, (s, Function.update z j 0))) :
    (cubeTransAt j f g h).HomotopicWith (cubeTransAt j f' g' h')
      fun k ↦ MapsTo k (Cube.prodBoundary N) B := by
  -- Concatenate the homotopies, read on `(I × I) × I^N`, and move the time coordinate back out.
  let e : C((I × I) × I^N, I × (I × I^N)) := Homeomorph.prodAssoc I I (I^N)
  let H := (cubeTransAt j (F.toContinuousMap.comp e) (G.toContinuousMap.comp e)
    fun s t ↦ hFG s.1 s.2 t).comp
      ((Homeomorph.prodAssoc I I (I^N)).symm : C(I × (I × I^N), (I × I) × I^N))
  have hH (t : I) (w : I × I^N) : H (t, w) = if (w.2 j : ℝ) ≤ 1 / 2
      then F (t, (w.1, Function.update w.2 j (projIcc 0 1 zero_le_one (2 * w.2 j))))
      else G (t, (w.1, Function.update w.2 j (projIcc 0 1 zero_le_one (2 * w.2 j - 1)))) :=
    (rfl)
  refine ⟨{ toFun := H
            continuous_toFun := H.continuous
            map_zero_left := fun w ↦ ?_
            map_one_left := fun w ↦ ?_
            prop' := fun t ↦ ?_ }⟩
  · simp only [hH, cubeTransAt_apply, ContinuousMap.HomotopyWith.apply_zero]
  · simp only [hH, cubeTransAt_apply, ContinuousMap.HomotopyWith.apply_one]
  · refine (mapsTo_cubeTransAt (F.prop t) (G.prop t) fun s z ↦ hFG t s z).congr fun w _ ↦ ?_
    simp only [ContinuousMap.coe_mk, hH]
    -- The stage `F.curry t` of `F` is `x ↦ F (t, x)` by definition (`Homotopy.curry_apply`).
    exact cubeTransAt_apply j _ _ _ w

end Concatenation

namespace RelGenLoop

variable {X : BasedTopPair.{u}} [DecidableEq N]

/-- A relative cube sends the faces `t j = 0` and `t j = 1` to the basepoint. -/
theorem apply_update (p : RelGenLoop N X) (s : I) (t : I^N) (j : N) {a : I}
    (ha : a = 0 ∨ a = 1) : p (s, Function.update t j a) = X.pair.map X.basepoint :=
  apply_of_mem_boundary p s ⟨j, by rwa [Function.update_self]⟩

/-- The concatenation of two relative cubes is their concatenation as maps out of the cube. -/
theorem coe_transAt (j : N) (p q : RelGenLoop N X) :
    (transAt j p q : C(I × (I^N), X.pair.fst)) = cubeTransAt j p q fun s t ↦
      (apply_update p s t j (.inr rfl)).trans (apply_update q s t j (.inl rfl)).symm :=
  ContinuousMap.ext fun w ↦ transAt_apply j p q w.1 w.2

/-- The reversal of a relative cube is its reversal as a map out of the cube. -/
theorem coe_symmAt (j : N) (p : RelGenLoop N X) :
    (symmAt j p : C(I × (I^N), X.pair.fst)) = cubeSymmAt j p :=
  ContinuousMap.ext fun w ↦ symmAt_apply j p w.1 w.2

end RelGenLoop

/-! ### Contracting the open box onto a point of its top face -/

section Contraction

/-- The contraction of the open box `{1} × I^N ∪ I × ∂I^N` of `I × I^N` onto the point `(1, c)` of
its top face: up to time `1 / 2` it pushes every point up to the top face, and after that it moves
the top face along straight lines onto `c`. Unlike `TauCeti.openBoxContraction`, which aims at the
centre of the top face, it keeps each face `t j = c j` of the cube through `(1, c)` inside
itself, which is what lets the deformations of two maps sharing such a face be glued. -/
private def openBoxContractionTo (c : I^N) (t : I) (w : I × I^N) : I × I^N :=
  (projIcc 0 1 zero_le_one ((w.1 : ℝ) + 2 * t),
    fun i ↦ projIcc 0 1 zero_le_one ((w.2 i : ℝ) + max 0 (2 * (t : ℝ) - 1) * (c i - w.2 i)))

private theorem continuous_openBoxContractionTo (c : I^N) :
    Continuous fun q : I × (I × I^N) ↦ openBoxContractionTo c q.1 q.2 :=
  (continuous_projIcc.comp (by fun_prop)).prodMk
    (continuous_pi fun _ ↦ continuous_projIcc.comp (by fun_prop))

private theorem openBoxContractionTo_zero (c : I^N) (w : I × I^N) :
    openBoxContractionTo c 0 w = w := by
  ext1
  · simp [openBoxContractionTo]
  · funext i
    simp [openBoxContractionTo]

private theorem openBoxContractionTo_one (c : I^N) (w : I × I^N) :
    openBoxContractionTo c 1 w = (1, c) := by
  ext1
  · exact projIcc_eq_one.2 (by simp; linarith [w.1.2.1])
  · funext i
    simp only [openBoxContractionTo, Set.Icc.coe_one]
    rw [show (w.2 i : ℝ) + max 0 (2 * 1 - 1) * (c i - w.2 i) = c i by norm_num, projIcc_val]

private theorem openBoxContractionTo_mem_prodBoundary (c : I^N) {w : I × I^N}
    (hw : w.1 = 1 ∨ w.2 ∈ Cube.boundary N) (t : I) :
    openBoxContractionTo c t w ∈ Cube.prodBoundary N := by
  refine Cube.mk_mem_prodBoundary ?_
  by_cases ht : (t : ℝ) ≤ 1 / 2
  · rcases hw with hw | hw
    · exact .inl (projIcc_eq_one.2 (by simp [hw]; linarith [t.2.1]))
    · refine .inr ?_
      have : max (0 : ℝ) (2 * t - 1) = 0 := max_eq_left (by linarith)
      simpa [openBoxContractionTo, this] using hw
  · exact .inl (projIcc_eq_one.2 (by linarith [w.1.2.1]))

/-- The contraction onto `(1, c)` keeps the face `t j = c j` inside itself, acting there as the
contraction onto any point with the same coordinates outside `j`. -/
private theorem openBoxContractionTo_update [DecidableEq N] (c : I^N) (j : N) (e : I) (t : I)
    (s : I) (z : I^N) :
    openBoxContractionTo (Function.update c j e) t (s, Function.update z j e) =
      ((openBoxContractionTo c t (s, z)).1,
        Function.update (openBoxContractionTo c t (s, z)).2 j e) := by
  ext1
  · rfl
  · funext i
    by_cases hij : i = j
    · subst hij
      simp [openBoxContractionTo]
    · simp [openBoxContractionTo, Function.update_of_ne hij]

end Contraction

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
  have hp : (cubeSymmAt j g).HomotopicWith (RelGenLoop.symmAt j p).1
      fun f ↦ MapsTo f (Cube.prodBoundary N) B :=
    ⟨{ toContinuousMap :=
         G.toContinuousMap.comp ((ContinuousMap.id I).prodMap (cubeSymmAt j (.id _)))
       map_zero_left := fun w ↦ G.map_zero_left _
       map_one_left := fun w ↦ by
         rw [RelGenLoop.coe_symmAt]
         exact G.map_one_left _
       prop' := fun t ↦ mapsTo_cubeSymmAt (j := j) (G.prop t) }⟩
  let γ := PathConnectedSpace.somePath y b
  rw [pairClass_eq_transport_mk _ hp γ, ← inv_spec, pairClass_eq_transport_mk _ ⟨G⟩ γ]
  exact (mulEquivOfPath_apply (X := ⟨TopPair.ofSubset B, y⟩) γ _).symm.trans
    ((map_inv _ _).trans
      (congrArg (·⁻¹) (mulEquivOfPath_apply (X := ⟨TopPair.ofSubset B, y⟩) γ _)))

end Laws

end RelHomotopyGroup

end TauCeti
