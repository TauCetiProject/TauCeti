/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.ConstMulAction
public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.Topology.FiberBundle.Trivialization

/-!
# Trivializations of orbit projections from equivariant maps

Let a topological group `G` act continuously on `X`, and let `π : X → X ⧸ G` be the projection
to the orbit space, with its quotient topology. Over an open set `W` of orbits, a continuous map
`u : π⁻¹ W → G` with `u (g • x) = g * u x` trivializes `π` as a principal `G`-bundle: the map
`x ↦ (π x, u x)` is a homeomorphism `π⁻¹ W ≃ W × G`. Its inverse sends `(π x, g)` to
`(g * (u x)⁻¹) • x`; the point `(u x)⁻¹ • x` depends only on the orbit of `x`, so it defines a
continuous local section of `π` over `W`, by the universal property of the quotient topology.

This is the standard passage from an equivariant map to a local product structure for free
actions; see for instance Husemoller, *Fibre Bundles*, Chapter 4. It turns the construction of
equivariant maps into the construction of principal-bundle charts, using Mathlib's
`Trivialization`.

## Main definitions and results

* `TauCeti.orbitTrivialization`: the trivialization of the orbit projection over `W` determined
  by a continuous equivariant map `u : π⁻¹ W → G`.
* `TauCeti.orbitTrivialization_apply` and `TauCeti.orbitTrivialization_symm_apply_mk`: the chart
  and its inverse.
* `TauCeti.orbitTrivialization_apply_smul`: the chart intertwines the action on `X` with left
  multiplication on the fibre `G`.
-/

public section

open Bundle MulAction Set Topology

namespace TauCeti

variable {G X : Type*} [Group G] [MulAction G X] {W : Set (Quotient (orbitRel G X))} {u : X → G}

/-- The point `(u x)⁻¹ • x` only depends on the orbit of `x` when `u` is equivariant on a
saturated set containing `x`. -/
private theorem inv_smul_eq_of_smul_eq_mul
    (hu_smul : ∀ g : G, ∀ x ∈ Quotient.mk (orbitRel G X) ⁻¹' W, u (g • x) = g * u x)
    {x y : X} (hx : Quotient.mk (orbitRel G X) x ∈ W)
    (hxy : Quotient.mk (orbitRel G X) y = Quotient.mk (orbitRel G X) x) :
    (u y)⁻¹ • y = (u x)⁻¹ • x := by
  obtain ⟨g, rfl⟩ : ∃ g : G, g • x = y := Quotient.exact hxy
  rw [hu_smul g x hx, mul_inv_rev, mul_smul, inv_smul_smul]

variable [TopologicalSpace G] [ContinuousInv G] [TopologicalSpace X] [ContinuousSMul G X]

/-- The trivialization of the orbit projection `X → X ⧸ G` over an open set `W` of orbits,
determined by a continuous map `u : X → G` that is equivariant on the preimage of `W`. It sends
`x` to `(π x, u x)`, and its inverse sends `(π x, g)` to `(g * (u x)⁻¹) • x`. -/
noncomputable def orbitTrivialization (W : Set (Quotient (orbitRel G X))) (hW : IsOpen W)
    (u : X → G) (hu : ContinuousOn u (Quotient.mk (orbitRel G X) ⁻¹' W))
    (hu_smul : ∀ g : G, ∀ x ∈ Quotient.mk (orbitRel G X) ⁻¹' W, u (g • x) = g * u x) :
    Trivialization G (Quotient.mk (orbitRel G X)) where
  toFun x := (Quotient.mk _ x, u x)
  invFun p := p.2 • (u p.1.out)⁻¹ • p.1.out
  source := Quotient.mk (orbitRel G X) ⁻¹' W
  target := W ×ˢ univ
  map_source' _ hx := ⟨hx, mem_univ _⟩
  map_target' p hp := by simpa using hp.1
  left_inv' x hx := by
    simp only [inv_smul_eq_of_smul_eq_mul hu_smul hx (Quotient.out_eq _), smul_inv_smul]
  right_inv' p hp := by
    have hout : p.1.out ∈ Quotient.mk (orbitRel G X) ⁻¹' W := by simpa using hp.1
    have hsec : (u p.1.out)⁻¹ • p.1.out ∈ Quotient.mk (orbitRel G X) ⁻¹' W := by
      simpa using hp.1
    simp [hu_smul _ _ hsec, hu_smul _ _ hout]
  open_source := hW.preimage continuous_quot_mk
  open_target := hW.prod isOpen_univ
  continuousOn_toFun := continuous_quot_mk.continuousOn.prodMk hu
  continuousOn_invFun := by
    have hsec : ContinuousOn (fun y : Quotient (orbitRel G X) ↦ (u y.out)⁻¹ • y.out) W := by
      rw [isQuotientMap_quotient_mk'.continuousOn_isOpen_iff hW]
      refine ((hu.inv).smul continuousOn_id).congr fun x hx ↦ ?_
      exact inv_smul_eq_of_smul_eq_mul hu_smul hx (Quotient.out_eq _)
    exact continuousOn_snd.smul (hsec.comp continuousOn_fst fun _ hp ↦ hp.1)
  baseSet := W
  open_baseSet := hW
  source_eq := rfl
  target_eq := rfl
  proj_toFun _ _ := rfl

variable {hW : IsOpen W} {hu : ContinuousOn u (Quotient.mk (orbitRel G X) ⁻¹' W)}
  {hu_smul : ∀ g : G, ∀ x ∈ Quotient.mk (orbitRel G X) ⁻¹' W, u (g • x) = g * u x}

/-- `orbitTrivialization` sends `x` to its orbit together with `u x`. -/
@[simp]
theorem orbitTrivialization_apply (x : X) :
    orbitTrivialization W hW u hu hu_smul x = (Quotient.mk (orbitRel G X) x, u x) :=
  (rfl)

/-- The base of `orbitTrivialization` is the given open set of orbits. -/
@[simp]
theorem orbitTrivialization_baseSet : (orbitTrivialization W hW u hu hu_smul).baseSet = W :=
  (rfl)

/-- The inverse of `orbitTrivialization` sends `(π x, g)` to `(g * (u x)⁻¹) • x`. -/
@[simp]
theorem orbitTrivialization_symm_apply_mk {x : X} (hx : Quotient.mk (orbitRel G X) x ∈ W)
    (g : G) :
    (orbitTrivialization W hW u hu hu_smul).toOpenPartialHomeomorph.symm
      (Quotient.mk _ x, g) = (g * (u x)⁻¹) • x := by
  have hsrc : (g * (u x)⁻¹) • x ∈ (orbitTrivialization W hW u hu hu_smul).source := by
    simpa [Trivialization.mem_source] using hx
  have happly : orbitTrivialization W hW u hu hu_smul ((g * (u x)⁻¹) • x) =
      (Quotient.mk _ x, g) := by
    simp [hu_smul _ _ hx]
  rw [← happly]
  exact (orbitTrivialization W hW u hu hu_smul).toOpenPartialHomeomorph.left_inv hsrc

/-- `orbitTrivialization` intertwines the action of `G` on `X` with left multiplication on the
fibre `G`. -/
theorem orbitTrivialization_apply_smul (g : G) {x : X} (hx : Quotient.mk (orbitRel G X) x ∈ W) :
    orbitTrivialization W hW u hu hu_smul (g • x) =
      ((orbitTrivialization W hW u hu hu_smul x).1,
        g * (orbitTrivialization W hW u hu hu_smul x).2) := by
  simp only [orbitTrivialization_apply, hu_smul g x hx, orbitRel.Quotient.quotient_smul_eq]

end TauCeti
