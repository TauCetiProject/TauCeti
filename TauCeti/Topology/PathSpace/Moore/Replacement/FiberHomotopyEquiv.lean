/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Homotopy.FiberHomotopyEquiv.Basic
public import TauCeti.Topology.PathSpace.Moore.Replacement.Basic

/-!
# Fibre homotopy equivalences and the fibres of Moore-path replacements

A map `h : E → E'` over `B` induces the map `(e, γ) ↦ (h e, γ)` of the fibres `F'` of the
Moore-path replacements over each point `b` (`TauCeti.MooreReplacement.Fiber.map`). This file
shows that this construction respects homotopies through maps over `B`: such a homotopy `H`
induces the homotopy `(s, (e, γ)) ↦ (H (s, e), γ)` of the maps of fibres
(`TauCeti.MooreReplacement.Fiber.mapHomotopy`). Consequently a fibre homotopy equivalence from
`p` to `q` induces a homotopy equivalence `F'_p ≃ₕ F'_q` of the fibres of the replacements over
every point (`TauCeti.FiberHomotopyEquiv.mooreReplacementFiberHomotopyEquiv`), whose forward map
commutes strictly with the right actions of the Moore loops at `b`.

So the fibre `F'`, with its strict action, is an invariant of `p` up to fibre homotopy
equivalence. For instance, a Hurewicz fibration is fibre homotopy equivalent to its own Moore-path
replacement (`TauCeti.MooreReplacement.fiberHomotopyEquiv`).

## Main definitions

* `TauCeti.MooreReplacement.Fiber.mapHomotopy`: the homotopy of maps of fibres induced by a
  homotopy through maps over `B`.
* `TauCeti.FiberHomotopyEquiv.mooreReplacementFiberHomotopyEquiv`: the homotopy equivalence of the
  fibres of the Moore-path replacements induced by a fibre homotopy equivalence.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, §7.1.
-/

public noncomputable section

open ContinuousMap unitInterval

namespace TauCeti

namespace MooreReplacement.Fiber

variable {E E' B : Type*} [TopologicalSpace E] [TopologicalSpace E'] [TopologicalSpace B]
  {p : C(E, B)} {q : C(E', B)} {b : B}

private theorem source_path_eq_apply_homotopyWith {h₀ h₁ : C(E, E')}
    (H : HomotopyWith h₀ h₁ fun h ↦ q.comp h = p) (y : I × Fiber p b) :
    y.2.val.path.source = q (H (y.1, y.2.val.point)) :=
  (source_path _).trans congr($(H.prop' y.1) y.2.val.point).symm

/-- A homotopy `H` through maps `E → E'` over `B` induces a homotopy of the maps of the fibres of
the Moore-path replacements over `b`: `(s, (e, γ)) ↦ (H (s, e), γ)`. -/
def mapHomotopy {h₀ h₁ : C(E, E')} (H : HomotopyWith h₀ h₁ fun h ↦ q.comp h = p)
    (hh₀ : q.comp h₀ = p) (hh₁ : q.comp h₁ = p) :
    Homotopy (map (b := b) h₀ hh₀) (map h₁ hh₁) where
  toFun y := ⟨MooreReplacement.mk (H (y.1, y.2.val.point)) y.2.val.path
      (source_path_eq_apply_homotopyWith H y),
    (congrArg MoorePath.target (path_mk _ _ _)).trans (target_path_val y.2)⟩
  continuous_toFun := (continuous_mk (H.continuous.comp (continuous_fst.prodMk
    (continuous_point.comp (continuous_val.comp continuous_snd))))
    (continuous_path.comp (continuous_val.comp continuous_snd)) _).subtype_mk _
  map_zero_left x := Subtype.ext <| by
    rw [← val_eq_subtypeVal (map h₀ hh₀ x)]
    exact MooreReplacement.ext (by simp) (by simp)
  map_one_left x := Subtype.ext <| by
    rw [← val_eq_subtypeVal (map h₁ hh₁ x)]
    exact MooreReplacement.ext (by simp) (by simp)

@[simp]
theorem point_mapHomotopy {h₀ h₁ : C(E, E')} (H : HomotopyWith h₀ h₁ fun h ↦ q.comp h = p)
    (hh₀ : q.comp h₀ = p) (hh₁ : q.comp h₁ = p) (y : I × Fiber p b) :
    (mapHomotopy H hh₀ hh₁ y).val.point = H (y.1, y.2.val.point) := by
  rw [val_eq_subtypeVal]
  exact point_mk _ _ _

@[simp]
theorem path_mapHomotopy {h₀ h₁ : C(E, E')} (H : HomotopyWith h₀ h₁ fun h ↦ q.comp h = p)
    (hh₀ : q.comp h₀ = p) (hh₁ : q.comp h₁ = p) (y : I × Fiber p b) :
    (mapHomotopy H hh₀ hh₁ y).val.path = y.2.val.path := by
  rw [val_eq_subtypeVal]
  exact path_mk _ _ _

end MooreReplacement.Fiber

namespace FiberHomotopyEquiv

open MooreReplacement

variable {E E' B : Type*} [TopologicalSpace E] [TopologicalSpace E'] [TopologicalSpace B]
  {p : C(E, B)} {q : C(E', B)}

/-- A fibre homotopy equivalence from `p` to `q` induces a **homotopy equivalence of the fibres of
the Moore-path replacements** over each point `b`, `(e, γ) ↦ (Φ e, γ)`, with homotopy inverse
`(e', γ) ↦ (Φ⁻¹ e', γ)`. -/
def mooreReplacementFiberHomotopyEquiv (Φ : FiberHomotopyEquiv p q) (b : B) :
    HomotopyEquiv (Fiber p b) (Fiber q b) where
  toFun := Fiber.map Φ.toFun Φ.comp_toFun
  invFun := Fiber.map Φ.invFun Φ.comp_invFun
  left_inv := by
    rw [← Fiber.map_comp, ← Fiber.map_id]
    exact Φ.left_inv.map fun H ↦ Fiber.mapHomotopy H _ _
  right_inv := by
    rw [← Fiber.map_comp, ← Fiber.map_id]
    exact Φ.right_inv.map fun H ↦ Fiber.mapHomotopy H _ _

theorem mooreReplacementFiberHomotopyEquiv_toFun (Φ : FiberHomotopyEquiv p q) (b : B) :
    (Φ.mooreReplacementFiberHomotopyEquiv b).toFun = Fiber.map Φ.toFun Φ.comp_toFun :=
  (rfl)

@[simp]
theorem coe_mooreReplacementFiberHomotopyEquiv (Φ : FiberHomotopyEquiv p q) (b : B) :
    ⇑(Φ.mooreReplacementFiberHomotopyEquiv b) = Fiber.map Φ.toFun Φ.comp_toFun :=
  (rfl)

@[simp]
theorem coe_mooreReplacementFiberHomotopyEquiv_symm (Φ : FiberHomotopyEquiv p q) (b : B) :
    ⇑(Φ.mooreReplacementFiberHomotopyEquiv b).symm = Fiber.map Φ.invFun Φ.comp_invFun :=
  (rfl)

end FiberHomotopyEquiv

end TauCeti
