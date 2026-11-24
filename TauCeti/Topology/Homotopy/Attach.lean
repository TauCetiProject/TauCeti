/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.UnitInterval
public import TauCeti.Topology.ContinuousMap.Glue.ClosedEmbeddings
public import TauCeti.Topology.Homotopy.OfApplyZero

/-!
# Deformations of an attached space

Let `Z` be obtained from a closed subset `X` by attaching a space `A` along a subset `S`: a closed
embedding `φ : A → Z` sends a point into `X` only if it lies in `S`, and `X` together with the
image of `φ` is all of `Z`. A deformation `H` of `A` which fixes `S` pointwise extends to a
deformation of `Z` which fixes `X` pointwise, by the identity on `X` and by `φ ∘ H` on the image of
`φ` (`Topology.IsClosedEmbedding.attachDeformation`). It is the gluing of the two along the closed
pieces `X` and the image of `φ` (`ContinuousMap.glueClosedEmbeddings`).

This is a topological input of the comparison of the relative homology of the attachment `(Z, X)`
with that of `(A, S)`, when `S` has an open neighbourhood `O` which a deformation of `A` fixing `S`
pushes into `S`: the thickening `X ∪ φ(O)` is then an open neighbourhood of `X`
(`Topology.IsClosedEmbedding.isOpen_union_image`) which the extended deformation pushes into `X`.
So the identity of `Z` is homotopic, keeping `X` and `X ∪ φ(O)` inside themselves, to a map pushing
`X ∪ φ(O)` into `X` (`Topology.IsClosedEmbedding.exists_homotopy_id_attach`).

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 2.1, the proof of
  Proposition 2.22 (good pairs).
-/

public section

noncomputable section

open Set Topology
open scoped unitInterval

namespace Topology.IsClosedEmbedding

variable {A Z : Type*} [TopologicalSpace A] [TopologicalSpace Z] {S O : Set A} {X : Set Z}
  {φ : C(A, Z)}
  (hφ : IsClosedEmbedding φ) (hX : IsClosed X) (hφX : ∀ a, φ a ∈ X → a ∈ S)
  (hcover : X ∪ range φ = univ) (H : C(I × A, A)) (hHS : ∀ t, ∀ a ∈ S, H (t, a) = a)

/-- **Extending a deformation over an attachment.** Let `Z` be obtained from the closed subset `X`
by attaching `A` along `S` through the closed embedding `φ`, and let `H : I × A → A` fix `S`
pointwise. The map `I × Z → Z` which is the projection on `I × X` and `φ ∘ H` on `I × A`. -/
def attachDeformation : C(I × Z, Z) :=
  ContinuousMap.glueClosedEmbeddings (i := Prod.map id ((↑) : X → Z)) (j := Prod.map id φ)
    ⟨fun p ↦ p.2, by fun_prop⟩ (φ.comp H)
    (IsClosedEmbedding.id.prodMap hX.isClosedEmbedding_subtypeVal)
    (IsClosedEmbedding.id.prodMap hφ)
    (eq_univ_of_forall fun p ↦ by
      obtain hz | ⟨a, ha⟩ := (hcover.symm ▸ mem_univ p.2 : p.2 ∈ X ∪ range φ)
      · exact Or.inl ⟨(p.1, ⟨p.2, hz⟩), rfl⟩
      · exact Or.inr ⟨(p.1, a), Prod.ext rfl ha⟩)
    (by
      rintro ⟨t, x⟩ ⟨s, a⟩ h
      obtain ⟨rfl, hx⟩ : t = s ∧ (x : Z) = φ a := Prod.ext_iff.1 h
      rw [ContinuousMap.coe_mk, ContinuousMap.comp_apply, hHS t a (hφX a (hx ▸ x.property))]
      exact hx)

/-- The extended deformation is `φ ∘ H` on the image of `φ`. -/
@[simp]
theorem attachDeformation_apply (t : I) (a : A) :
    attachDeformation hφ hX hφX hcover H hHS (t, φ a) = φ (H (t, a)) :=
  ContinuousMap.glueClosedEmbeddings_apply_right _ _ _ _ _ _ (t, a)

/-- The extended deformation fixes `X` pointwise. -/
theorem attachDeformation_apply_of_mem (t : I) {z : Z} (hz : z ∈ X) :
    attachDeformation hφ hX hφX hcover H hHS (t, z) = z :=
  ContinuousMap.glueClosedEmbeddings_apply_left _ _ _ _ _ _ (t, (⟨z, hz⟩ : X))

/-- If `H` starts at the identity, so does the extended deformation. -/
theorem attachDeformation_zero (hH₀ : ∀ a, H (0, a) = a) (z : Z) :
    attachDeformation hφ hX hφX hcover H hHS (0, z) = z := by
  obtain hz | ⟨a, rfl⟩ := (hcover.symm ▸ mem_univ z : z ∈ X ∪ range φ)
  · exact attachDeformation_apply_of_mem hφ hX hφX hcover H hHS 0 hz
  · rw [attachDeformation_apply, hH₀]

/-- If `H` keeps `O` in `O`, the extended deformation keeps the thickening `X ∪ φ(O)` in itself. -/
theorem attachDeformation_mem_union_image (hHO : ∀ t, ∀ a ∈ O, H (t, a) ∈ O) (t : I) {z : Z}
    (hz : z ∈ X ∪ φ '' O) : attachDeformation hφ hX hφX hcover H hHS (t, z) ∈ X ∪ φ '' O := by
  obtain hz | ⟨a, ha, rfl⟩ := hz
  · rw [attachDeformation_apply_of_mem hφ hX hφX hcover H hHS t hz]
    exact Or.inl hz
  · rw [attachDeformation_apply]
    exact Or.inr ⟨_, hHO t a ha, rfl⟩

/-- If `H` pushes `O` into `S` at time one, and `φ` sends `S` into `X`, the extended deformation
pushes the thickening `X ∪ φ(O)` into `X` at time one. -/
theorem attachDeformation_one_mem (hφS : ∀ a ∈ S, φ a ∈ X) (hH₁ : ∀ a ∈ O, H (1, a) ∈ S) {z : Z}
    (hz : z ∈ X ∪ φ '' O) : attachDeformation hφ hX hφX hcover H hHS (1, z) ∈ X := by
  obtain hz | ⟨a, ha, rfl⟩ := hz
  · rwa [attachDeformation_apply_of_mem hφ hX hφX hcover H hHS 1 hz]
  · rw [attachDeformation_apply]
    exact hφS _ (hH₁ a ha)

include hφ hX hφX hcover hHS in
/-- **The deformation of an attachment.** In the setting of
`Topology.IsClosedEmbedding.attachDeformation`, let `H` start at the identity, keep `O` inside `O`
and push `O` into `S` at time one, and let `φ` send `S` into `X`. Then the identity of `Z` is
homotopic, keeping `X` and the thickening `X ∪ φ(O)` inside themselves, to a map pushing `X ∪ φ(O)`
into `X`: the extension of `H` to `Z`. -/
theorem exists_homotopy_id_attach (hφS : ∀ a ∈ S, φ a ∈ X) (hH₀ : ∀ a, H (0, a) = a)
    (hHO : ∀ t, ∀ a ∈ O, H (t, a) ∈ O) (hH₁ : ∀ a ∈ O, H (1, a) ∈ S) :
    ∃ (ρ : C(Z, Z)) (G : (ContinuousMap.id Z).Homotopy ρ),
      (∀ (τ : I) (z : Z), z ∈ X → G (τ, z) ∈ X) ∧
        (∀ (τ : I) (z : Z), z ∈ X ∪ φ '' O → G (τ, z) ∈ X ∪ φ '' O) ∧ MapsTo ρ (X ∪ φ '' O) X :=
  ContinuousMap.exists_homotopy_id_of_deformation (attachDeformation hφ hX hφX hcover H hHS)
    (attachDeformation_zero hφ hX hφX hcover H hHS hH₀)
    (fun t _ hz ↦ (attachDeformation_apply_of_mem hφ hX hφX hcover H hHS t hz).symm ▸ hz)
    (fun t _ hz ↦ attachDeformation_mem_union_image hφ hX hφX hcover H hHS hHO t hz)
    (fun _ hz ↦ attachDeformation_one_mem hφ hX hφX hcover H hHS hφS hH₁ hz)

end Topology.IsClosedEmbedding
