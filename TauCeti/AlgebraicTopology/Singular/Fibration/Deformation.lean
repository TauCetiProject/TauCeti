/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Homotopy.Relative.Deformation
public import TauCeti.AlgebraicTopology.Singular.Fibration.Skeleton

/-!
# Homology of a Serre fibration over a base that deforms into a subspace

Let `p : E → B` be a Serre fibration and `A ⊆ B`. If `B` deforms into `A` in the weak sense, by a
homotopy that starts at the identity, ends inside `A`, and keeps `A` inside `A` at all times, then
all relative homotopy sets of `(B, A)` are trivial
(`TauCeti.RelHomotopyGroup.subsingleton_ofSubset_of_deformation`), so are those of
`(E, p⁻¹(A))`, and therefore `H_*(E, p⁻¹(A); R) = 0`
(`TauCeti.TopCat.isZero_singularHomology_preimage_of_deformation`).

Straight-line deformations of a convex base into a star-convex part, and the radial deformation
of a punctured ball onto its boundary sphere, are of this kind.

## Main results

* `TauCeti.TopCat.isZero_singularHomology_preimage_of_deformation`: if the base deforms into `A`,
  the pair `(E, p⁻¹(A))` is acyclic.
-/

public section

open CategoryTheory Limits
open scoped unitInterval

universe u

namespace TauCeti

namespace TopCat

variable {E B : _root_.TopCat.{u}} {p : E ⟶ B}

/-- **A Serre fibration over a base that deforms into `A` is acyclic modulo the part over `A`.**
Let `p : E ⟶ B` be a Serre fibration and `A ⊆ B`, and let `H : I × B → B` be a homotopy that starts
at the identity, ends inside `A`, and keeps `A` inside `A` at all times. Then
`Hₘ(E, p⁻¹(A); R) = 0` for every `m`. -/
theorem isZero_singularHomology_preimage_of_deformation (hp : serreFibrations p) {A : Set B}
    (H : C(I × B, B)) (h₀ : ∀ b, H (0, b) = b) (h₁ : ∀ b, H (1, b) ∈ A)
    (hA : ∀ t, ∀ b ∈ A, H (t, b) ∈ A) (R : Type u) [Ring R] (m : ℕ) :
    IsZero ((TopPair.ofSubset (p ⁻¹' A)).singularHomology (ModuleCat.of R R) m) :=
  isZero_singularHomology_preimage_of_relHomotopyGroup hp
    (fun b ↦ ⟨H (1, b), h₁ b,
      ⟨{ toFun := fun t ↦ H (t, b)
         continuous_toFun := by fun_prop
         source' := h₀ b
         target' := rfl }⟩⟩)
    (fun _ _ a ↦ RelHomotopyGroup.subsingleton_ofSubset_of_deformation H h₀ h₁ hA a) R
    (Nat.lt_succ_self m)

end TopCat

end TauCeti
