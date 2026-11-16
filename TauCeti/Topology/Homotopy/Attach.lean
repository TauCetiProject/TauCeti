/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Homotopy.Basic
public import TauCeti.Topology.ContinuousMap.GlueClosedEmbeddings

/-!
# Deformations of an attached space

Let `Z` be obtained from a closed subset `X` by attaching a space `A` along a subset `S`: a closed
embedding `φ : A → Z` sends a point into `X` only if it lies in `S`, and `X` together with the
image of `φ` is all of `Z`. A deformation `H` of `A` which fixes `S` pointwise extends to a
deformation of `Z` which fixes `X` pointwise, by the identity on `X` and by `φ ∘ H` on the image of
`φ` (`TauCeti.attachHomotopy`). It is the gluing of the two along the closed pieces `X` and the
image of `φ` (`ContinuousMap.glueClosedEmbeddings`).

This is a topological input of the comparison of the relative homology of the attachment `(Z, X)`
with that of `(A, S)`, when `S` has an open neighbourhood `O` which a deformation of `A` fixing `S`
pushes into `S`: the thickening `X ∪ φ(O)` is then an open neighbourhood of `X`
(`Topology.IsClosedEmbedding.isOpen_union_image`) which the extended deformation pushes into `X`.
Both deformations start at the identity, so they are homotopies from the identity to their
time-one maps (`ContinuousMap.Homotopy.ofApplyZero`).

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 2.1, the proof of
  Proposition 2.22 (good pairs).
-/

public section

noncomputable section

open Set Topology
open scoped unitInterval

namespace ContinuousMap.Homotopy

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {f : C(X, Y)}

/-- A map `H : I × X → Y` which is `f` at time zero, as a homotopy from `f` to its time-one map
`H.curry 1`. -/
-- Exposed so that the homotopy applies definitionally as `H`: hypotheses on `H` then discharge
-- the hypotheses on the homotopy, for instance in `TopPair.isIso_singularHomologyMap_of_attach`.
@[expose]
def ofApplyZero (H : C(I × X, Y)) (hH : ∀ x, H (0, x) = f x) : f.Homotopy (H.curry 1) where
  toContinuousMap := H
  map_zero_left := hH
  map_one_left x := (H.curry_apply 1 x).symm

@[simp]
theorem ofApplyZero_apply (H : C(I × X, Y)) (hH : ∀ x, H (0, x) = f x) (p : I × X) :
    ofApplyZero H hH p = H p :=
  (rfl)

end ContinuousMap.Homotopy

namespace TauCeti

variable {A Z : Type*} [TopologicalSpace A] [TopologicalSpace Z] {S O : Set A} {X : Set Z}
  {φ : C(A, Z)}
  (hφ : IsClosedEmbedding φ) (hX : IsClosed X) (hφX : ∀ a, φ a ∈ X → a ∈ S)
  (hcover : X ∪ range φ = univ) (H : C(I × A, A)) (hHS : ∀ t, ∀ a ∈ S, H (t, a) = a)

/-- **Extending a deformation over an attachment.** Let `Z` be obtained from the closed subset `X`
by attaching `A` along `S` through the closed embedding `φ`, and let `H : I × A → A` fix `S`
pointwise. The map `I × Z → Z` which is the projection on `I × X` and `φ ∘ H` on `I × A`. -/
def attachHomotopy : C(I × Z, Z) :=
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
      rw [ContinuousMap.coe_mk, ContinuousMap.comp_apply, hHS t a (hφX a (hx ▸ x.2))]
      exact hx)

/-- The extended deformation is `φ ∘ H` on the image of `φ`. -/
@[simp]
theorem attachHomotopy_apply (t : I) (a : A) :
    attachHomotopy hφ hX hφX hcover H hHS (t, φ a) = φ (H (t, a)) :=
  ContinuousMap.glueClosedEmbeddings_apply_right _ _ _ _ _ _ (t, a)

/-- The extended deformation fixes `X` pointwise. -/
theorem attachHomotopy_apply_of_mem (t : I) {z : Z} (hz : z ∈ X) :
    attachHomotopy hφ hX hφX hcover H hHS (t, z) = z :=
  ContinuousMap.glueClosedEmbeddings_apply_left _ _ _ _ _ _ (t, (⟨z, hz⟩ : X))

/-- If `H` starts at the identity, so does the extended deformation. -/
theorem attachHomotopy_zero (hH₀ : ∀ a, H (0, a) = a) (z : Z) :
    attachHomotopy hφ hX hφX hcover H hHS (0, z) = z := by
  obtain hz | ⟨a, rfl⟩ := (hcover.symm ▸ mem_univ z : z ∈ X ∪ range φ)
  · exact attachHomotopy_apply_of_mem hφ hX hφX hcover H hHS 0 hz
  · rw [attachHomotopy_apply, hH₀]

/-- If `H` keeps `O` in `O`, the extended deformation keeps the thickening `X ∪ φ(O)` in itself. -/
theorem attachHomotopy_mem_union_image (hHO : ∀ t, ∀ a ∈ O, H (t, a) ∈ O) (t : I) {z : Z}
    (hz : z ∈ X ∪ φ '' O) : attachHomotopy hφ hX hφX hcover H hHS (t, z) ∈ X ∪ φ '' O := by
  obtain hz | ⟨a, ha, rfl⟩ := hz
  · rw [attachHomotopy_apply_of_mem hφ hX hφX hcover H hHS t hz]
    exact Or.inl hz
  · rw [attachHomotopy_apply]
    exact Or.inr ⟨_, hHO t a ha, rfl⟩

/-- If `H` pushes `O` into `S` at time one, and `φ` sends `S` into `X`, the extended deformation
pushes the thickening `X ∪ φ(O)` into `X` at time one. -/
theorem attachHomotopy_one_mem (hφS : ∀ a ∈ S, φ a ∈ X) (hH₁ : ∀ a ∈ O, H (1, a) ∈ S) {z : Z}
    (hz : z ∈ X ∪ φ '' O) : attachHomotopy hφ hX hφX hcover H hHS (1, z) ∈ X := by
  obtain hz | ⟨a, ha, rfl⟩ := hz
  · rwa [attachHomotopy_apply_of_mem hφ hX hφX hcover H hHS 1 hz]
  · rw [attachHomotopy_apply]
    exact hφS _ (hH₁ a ha)

end TauCeti
