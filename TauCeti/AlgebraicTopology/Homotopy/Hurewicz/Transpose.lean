/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Homotopy.Hurewicz.Sphere
public import TauCeti.Topology.Homotopy.GenLoop.Loop

/-!
# Hurewicz classes of transposed squares

A generalized loop `p : I² → X` at `x` can be read with its two cube directions exchanged, as the
generalized loop `(s, t) ↦ p (t, s)`; this is `GenLoop.congr x (Equiv.swap 0 1) p`. Two
constructions of the same square class differ in this way: a double loop `β` in the loop space
`Ω X x` gives the square `(s, t) ↦ β s t` (`GenLoop.fromDoubleLoop`), whereas the torus swept out
by the loop of free loops `s ↦ β s` is the square `(s, t) ↦ β t s` (`GenLoop.freeLoopTorus`).

Transposition is natural in based maps, and every generalized loop is the image of the tautological
loop `TauCeti.sphereGenLoop 2` of the sphere `S²`, whose Hurewicz class generates `H₂(S²; ℤ) ≅ ℤ`
(`TauCeti.isIso_hurewicz_sphereGenLoop`). So transposing multiplies Hurewicz classes by one
integer `k`, the same for every generalized loop in every space; since transposing twice is the
identity, `k² = 1` and `k` is a unit
(`GenLoop.exists_forall_hurewicz_congr_swap_eq_units_smul`). The sign is that of the
transposition of the square, which reverses its orientation; its value is not computed here, a
universal unit is what comparisons of Hurewicz classes read in the two orders need.

## Main results

* `GenLoop.exists_forall_hurewicz_congr_swap_eq_units_smul`: transposing a generalized loop of
  dimension two multiplies its integral Hurewicz class by a universal sign.
-/

public section

open CategoryTheory
open scoped Topology.Homotopy

namespace GenLoop

open TauCeti

variable {X : Type} [TopologicalSpace X] {x : X}

/-- Transposing a square commutes with pushing it forward along a based map. -/
theorem congr_swap_map {Y : Type} [TopologicalSpace Y] {y : Y} (f : C(X, Y)) (hf : f x = y)
    (p : Ω^ (Fin 2) X x) :
    _root_.GenLoop.congr y (Equiv.swap 0 1) (GenLoop.map f hf p) =
      GenLoop.map f hf (_root_.GenLoop.congr x (Equiv.swap 0 1) p) :=
  GenLoop.ext _ _ fun _ ↦ by simp only [congr_apply, GenLoop.map_apply]

/-- Transposing a square twice gives the square back. -/
@[simp]
theorem congr_swap_congr_swap (p : Ω^ (Fin 2) X x) :
    _root_.GenLoop.congr x (Equiv.swap 0 1) (_root_.GenLoop.congr x (Equiv.swap 0 1) p) = p :=
  GenLoop.ext _ _ fun _ ↦ by simp only [congr_apply, Equiv.swap_apply_self]

/-- **Transposing a square multiplies its Hurewicz class by a universal sign.** There is one unit
`σ` of `ℤ` such that for every generalized loop `p : I² → X` at `x`, in every space `X`, the
integral Hurewicz class of the transposed square `(s, t) ↦ p (t, s)` is `σ` times that of `p`. -/
theorem exists_forall_hurewicz_congr_swap_eq_units_smul :
    ∃ σ : ℤˣ, ∀ (X : Type) [TopologicalSpace X] (x : X) (p : Ω^ (Fin 2) X x),
      (hurewicz (ModuleCat.of ℤ ℤ) (_root_.GenLoop.congr x (Equiv.swap 0 1) p)).hom 1 =
        (σ : ℤ) • (hurewicz (ModuleCat.of ℤ ℤ) p).hom 1 := by
  obtain ⟨k, hk⟩ := exists_zsmul_hurewicz_sphereGenLoop 1 ((hurewicz (ModuleCat.of ℤ ℤ)
    (_root_.GenLoop.congr _ (Equiv.swap 0 1) (sphereGenLoop 2))).hom 1)
  -- Every square is the image of the tautological loop of `S²`, and both sides are natural.
  have key (X : Type) [TopologicalSpace X] (x : X) (p : Ω^ (Fin 2) X x) :
      (hurewicz (ModuleCat.of ℤ ℤ) (_root_.GenLoop.congr x (Equiv.swap 0 1) p)).hom 1 =
        k • (hurewicz (ModuleCat.of ℤ ℤ) p).hom 1 := by
    conv_lhs => rw [← map_toSphere_sphereGenLoop p, congr_swap_map, hurewicz_map,
      ModuleCat.hom_comp, LinearMap.comp_apply, ← hk, map_zsmul]
    conv_rhs => rw [hurewicz_eq_hurewicz_sphereGenLoop_comp, ModuleCat.hom_comp,
      LinearMap.comp_apply]
  -- Transposing twice is the identity, and the Hurewicz class of the tautological loop has
  -- infinite order, so `k * k = 1`.
  have hkk : k * k = 1 := by
    have h := key _ _ (_root_.GenLoop.congr _ (Equiv.swap 0 1) (sphereGenLoop 2))
    rw [congr_swap_congr_swap, ← hk, smul_smul] at h
    have hinj := (ConcreteCategory.bijective_of_isIso
      (hurewicz (ModuleCat.of ℤ ℤ) (sphereGenLoop 2))).1
    have h' : (hurewicz (ModuleCat.of ℤ ℤ) (sphereGenLoop 2)).hom (k * k) =
        (hurewicz (ModuleCat.of ℤ ℤ) (sphereGenLoop 2)).hom 1 := by
      rw [← mul_one (k * k), ← smul_eq_mul, map_zsmul, ← h]
    exact hinj h'
  exact ⟨⟨k, k, hkk, hkk⟩, key⟩

end GenLoop
