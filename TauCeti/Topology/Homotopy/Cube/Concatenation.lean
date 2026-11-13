/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Homotopy.Cube.Basic

/-!
# Concatenation and reversal of maps out of a cube

Mathlib concatenates and reverses generalized loops `I^N → X` along a direction `j : N` of the
cube (`GenLoop.transAt`, `GenLoop.symmAt`), using that they are constant on the boundary. This file
does the same for arbitrary continuous maps `Z × I^N → Y`, with an extra parameter space `Z`:

* `TauCeti.cubeTransAt j f g h` runs `f` on the half `t j ≤ 1 / 2` and `g` on the other half, when
  the face `t j = 1` of `f` agrees with the face `t j = 0` of `g` (the hypothesis `h`);
* `TauCeti.cubeSymmAt j f` reverses `f` by `t j ↦ 1 - t j`.

Both operations preserve maps of pairs `(I × I^N, ∂(I × I^N)) → (Y, B)`
(`TauCeti.mapsTo_cubeTransAt`, `TauCeti.mapsTo_cubeSymmAt`), and concatenating two homotopies
through maps of pairs that agree on the common face gives a homotopy through maps of pairs
between the concatenations (`TauCeti.homotopicWith_cubeTransAt`). For relative cubes they are
`TauCeti.RelGenLoop.transAt` and `TauCeti.RelGenLoop.symmAt`, which is how the group laws of
relative homotopy groups extend to maps of pairs that are not relative cubes.

## Main definitions and results

* `TauCeti.cubeTransAt`, `TauCeti.cubeSymmAt`: concatenation and reversal along a direction of the
  cube, with their faces `TauCeti.cubeTransAt_update_zero`, `TauCeti.cubeTransAt_update_one`,
  `TauCeti.cubeSymmAt_update_zero`, `TauCeti.cubeSymmAt_update_one`, and the involution
  `TauCeti.cubeSymmAt_cubeSymmAt`.
* `TauCeti.mapsTo_cubeTransAt`, `TauCeti.mapsTo_cubeSymmAt`: both preserve maps of pairs.
* `TauCeti.homotopicWith_cubeTransAt`: concatenation of homotopies through maps of pairs.
-/

public section

noncomputable section

open Set Topology
open scoped unitInterval

namespace TauCeti

variable {N : Type*} {Z Y : Type*} [TopologicalSpace Z] [TopologicalSpace Y] [DecidableEq N]

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

/-- The face `t j = 0` of the concatenation along `j` is the face `t j = 0` of the first map. -/
@[simp]
theorem cubeTransAt_update_zero (j : N) (f g : C(Z × (I^N), Y))
    (h : ∀ s t, f (s, Function.update t j 1) = g (s, Function.update t j 0)) (s : Z) (t : I^N) :
    cubeTransAt j f g h (s, Function.update t j 0) = f (s, Function.update t j 0) := by
  simp [cubeTransAt_apply]

/-- The face `t j = 1` of the concatenation along `j` is the face `t j = 1` of the second map. -/
@[simp]
theorem cubeTransAt_update_one (j : N) (f g : C(Z × (I^N), Y))
    (h : ∀ s t, f (s, Function.update t j 1) = g (s, Function.update t j 0)) (s : Z) (t : I^N) :
    cubeTransAt j f g h (s, Function.update t j 1) = g (s, Function.update t j 1) := by
  norm_num [cubeTransAt_apply]

/-- Reversal of a map `f : Z × I^N → Y` along a direction `j : N` of the cube `I^N`, by
`t j ↦ 1 - t j`. For relative cubes this is `TauCeti.RelGenLoop.symmAt`
(`TauCeti.RelGenLoop.coe_symmAt`). -/
def cubeSymmAt (j : N) (f : C(Z × (I^N), Y)) : C(Z × (I^N), Y) :=
  f.comp ⟨fun w ↦ (w.1, fun i ↦ if i = j then σ (w.2 j) else w.2 i),
    continuous_fst.prodMk (continuous_pi fun i ↦ by split_ifs <;> fun_prop)⟩

theorem cubeSymmAt_apply (j : N) (f : C(Z × (I^N), Y)) (w : Z × I^N) :
    cubeSymmAt j f w = f (w.1, fun i ↦ if i = j then σ (w.2 j) else w.2 i) :=
  (rfl)

/-- Reversal along `j` exchanges the faces `t j = 0` and `t j = 1`. -/
@[simp]
theorem cubeSymmAt_update_zero (j : N) (f : C(Z × (I^N), Y)) (s : Z) (t : I^N) :
    cubeSymmAt j f (s, Function.update t j 0) = f (s, Function.update t j 1) := by
  rw [cubeSymmAt_apply]
  congr 2
  funext i
  by_cases hij : i = j
  · subst hij
    simp
  · simp [hij]

/-- Reversal along `j` exchanges the faces `t j = 1` and `t j = 0`. -/
@[simp]
theorem cubeSymmAt_update_one (j : N) (f : C(Z × (I^N), Y)) (s : Z) (t : I^N) :
    cubeSymmAt j f (s, Function.update t j 1) = f (s, Function.update t j 0) := by
  rw [cubeSymmAt_apply]
  congr 2
  funext i
  by_cases hij : i = j
  · subst hij
    simp
  · simp [hij]

/-- Reversal along a direction is an involution. -/
@[simp]
theorem cubeSymmAt_cubeSymmAt (j : N) (f : C(Z × (I^N), Y)) :
    cubeSymmAt j (cubeSymmAt j f) = f := by
  ext w
  rw [cubeSymmAt_apply, cubeSymmAt_apply]
  congr 2
  funext i
  by_cases hij : i = j
  · subst hij
    simp
  · simp [hij]

theorem mapsTo_cubeTransAt {B : Set Y} {j : N} {f g : C(I × (I^N), Y)}
    (hf : MapsTo f (Cube.prodBoundary N) B) (hg : MapsTo g (Cube.prodBoundary N) B)
    (h : ∀ s t, f (s, Function.update t j 1) = g (s, Function.update t j 0)) :
    MapsTo (cubeTransAt j f g h) (Cube.prodBoundary N) B := by
  intro w hw
  rw [cubeTransAt_apply]
  split_ifs with hj
  · refine hf (Cube.update_mem_prodBoundary hw fun h0 ↦ ?_)
    rcases h0 with h0 | h0 <;> rw [h0] at hj ⊢
    · simp
    · norm_num at hj
  · refine hg (Cube.update_mem_prodBoundary hw fun h0 ↦ ?_)
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

end TauCeti
