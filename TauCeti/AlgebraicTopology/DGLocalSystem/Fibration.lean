/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.DGLocalSystem.Basic
public import TauCeti.AlgebraicTopology.Singular.Cubical.MonoidAlgebra.Action
public import TauCeti.Topology.PathSpace.Moore.Replacement.Basic

/-!
# The DG local system of a fibration

For a continuous map `p : E → B` and a point `b ∈ B`, the fibre `F'` over `b` of the Moore-path
replacement of `p` carries a strict continuous right action of the Moore loops `Ω_b B`,
`(e, γ) · ω = (e, γ · ω)`.  By `TauCeti.AlgebraicTopology.Singular.Cubical.MonoidAlgebra.Action`,
its normalized cubical chains `C_*(F')` form a right DG module over `C_*(Ω_b B)`: this is the
**DG local system of `p`** at `b` (BDHO §7.1).  It involves no choice of lifting function, and it
is natural in maps over `B`.

When `p` comes with a transitive lifting function `Φ`, the Moore loops act strictly on the fibre
`F = p⁻¹(b)` itself, `f · ω = Φ (f, ω)(end)`, which gives a second DG local system `C_*(F)_Φ`, and
transport `F' → F`, `(e, γ) ↦ Φ (e, γ)(end)`, is strictly equivariant, so it induces a **strict**
morphism of DG local systems `C_*(F') → C_*(F)_Φ`.

## Main definitions

* `TauCeti.fibrationLocalSystem R p b`: the DG local system `C_*(F')` on `(B, b)`.
* `TauCeti.fibrationLocalSystemMap R h hh`: its naturality along a map `h` over `B`.
* `TauCeti.liftingLocalSystem R hΦ b`: the DG local system `C_*(F)_Φ` of a transitive lifting
  function.
* `TauCeti.transportLocalSystemHom R hΦ b`: the strict morphism `C_*(F') → C_*(F)_Φ` induced by
  transport.

## Main results

* `TauCeti.fibrationLocalSystemMap_id`, `TauCeti.fibrationLocalSystemMap_comp`: functoriality.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, §7.1.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §1.4.
-/

public section

noncomputable section

open CategoryTheory MulOpposite

namespace TauCeti

universe u

section LocalSystem

variable {E E' E'' B : Type u} [TopologicalSpace E] [TopologicalSpace E'] [TopologicalSpace E'']
  [TopologicalSpace B] (R : Type*) [CommRing R]

/-- The **DG local system of a map** `p : E → B` at `b`: the normalized cubical chains of the fibre
`F'` of the Moore-path replacement, a right DG module over `C_*(Ω_b B; R)` through the strict
action of the Moore loops. -/
abbrev fibrationLocalSystem (p : C(E, B)) (b : B) : DGLocalSystem B b R :=
  cubicalChainModuleDG (MooreReplacement.Fiber p b) (MooreLoopSpace B b) R

/-- The morphism of DG local systems induced by a map `h : E → E'` over `B`. -/
def fibrationLocalSystemMap {p : C(E, B)} {p' : C(E', B)} {b : B} (h : C(E, E'))
    (hh : p'.comp h = p) : fibrationLocalSystem R p b ⟶ fibrationLocalSystem R p' b :=
  cubicalChainModuleMap R (MooreReplacement.Fiber.map h hh) fun ω x ↦
    MooreReplacement.Fiber.map_act h hh x ω

/-- The induced morphism is the push-forward of chains along the map of fibres. -/
theorem fibrationLocalSystemMap_apply {p : C(E, B)} {p' : C(E', B)} {b : B} (h : C(E, E'))
    (hh : p'.comp h = p) (x : fibrationLocalSystem R p b) :
    fibrationLocalSystemMap R h hh x =
      cubicalChainModuleLinearMap (G := MooreLoopSpace B b) R (MooreReplacement.Fiber.map h hh) x :=
  cubicalChainModuleMap_apply _ _ x

/-- The identity induces the identity. -/
@[simp]
theorem fibrationLocalSystemMap_id (p : C(E, B)) (b : B) :
    fibrationLocalSystemMap R (b := b) (ContinuousMap.id E) (ContinuousMap.comp_id p) =
      𝟙 (fibrationLocalSystem R p b) := by
  ext x
  rw [DGRightModuleCat.id_apply]
  rw [fibrationLocalSystemMap_apply, MooreReplacement.Fiber.map_id, cubicalChainModuleLinearMap_id,
    LinearMap.id_apply]

/-- A composite of maps over `B` induces the composite of the induced morphisms. -/
theorem fibrationLocalSystemMap_comp {p : C(E, B)} {p' : C(E', B)} {p'' : C(E'', B)} {b : B}
    (h : C(E, E')) (h' : C(E', E'')) (hh : p'.comp h = p) (hh' : p''.comp h' = p') :
    fibrationLocalSystemMap R (b := b) (h'.comp h) (by rw [← ContinuousMap.comp_assoc, hh', hh]) =
      fibrationLocalSystemMap R h hh ≫ fibrationLocalSystemMap R h' hh' := by
  ext x
  rw [DGRightModuleCat.comp_apply]
  rw [fibrationLocalSystemMap_apply, fibrationLocalSystemMap_apply, fibrationLocalSystemMap_apply,
    MooreReplacement.Fiber.map_comp h h' hh hh', cubicalChainModuleLinearMap_comp,
    LinearMap.comp_apply]

variable {R}

/-- The **DG local system `C_*(F)_Φ` of a transitive lifting function** `Φ` for `p` at `b`: the
normalized cubical chains of the fibre `F = p⁻¹(b)`, with the strict action of the Moore loops
`f · ω = Φ (f, ω)(end)`. -/
abbrev liftingLocalSystem {p : C(E, B)} {Φ : MooreLiftingFunction p} (hΦ : Φ.IsTransitive) (b : B) :
    DGLocalSystem B b R :=
  letI := hΦ.mulAction b
  letI := hΦ.continuousSMul b
  cubicalChainModuleDG {e // p e = b} (MooreLoopSpace B b) R

/-- **Transport as a strict morphism of DG local systems**: transport `F' → F`,
`(e, γ) ↦ Φ (e, γ)(end)`, along a transitive lifting function is strictly equivariant, so it
induces a morphism `C_*(F') → C_*(F)_Φ` of right DG modules over `C_*(Ω_b B)`. -/
def transportLocalSystemHom {p : C(E, B)} {Φ : MooreLiftingFunction p} (hΦ : Φ.IsTransitive)
    (b : B) : fibrationLocalSystem R p b ⟶ liftingLocalSystem hΦ b :=
  letI := hΦ.mulAction b
  letI := hΦ.continuousSMul b
  cubicalChainModuleMap R (Φ.transport b) fun ω x ↦ hΦ.transport_act b x ω

/-- The morphism induced by transport is the push-forward of chains along transport. -/
theorem transportLocalSystemHom_apply {p : C(E, B)} {Φ : MooreLiftingFunction p}
    (hΦ : Φ.IsTransitive) (b : B) (x : fibrationLocalSystem R p b) :
    transportLocalSystemHom hΦ b x =
      cubicalChainModuleLinearMap (G := MooreLoopSpace B b) R (Φ.transport b) x :=
  letI := hΦ.mulAction b
  letI := hΦ.continuousSMul b
  cubicalChainModuleMap_apply (Φ.transport b) (fun ω x ↦ hΦ.transport_act b x ω) x

end LocalSystem

end TauCeti

end
