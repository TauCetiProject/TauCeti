/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.ProjectiveRepresentation.RepresentationGroup.Basic
public import TauCeti.RepresentationTheory.ProjectiveRepresentation.PGL.Lifting

/-!
# Finite stem extensions lifting all matrix projective representations

Every finite group over an algebraically closed field has a single finite central stem
extension over which all finite-dimensional matrix projective representations lift.
The extension is chosen before the matrix size and the projective representation, and the
lift has the same matrix size. Its projectivization is the pullback of the original action.

The finite stem extension is supplied by
`TauCeti.exists_finite_stem_factorSet_bijective_characterTransgression`; its universal
lifting property follows from character transgression. The construction works in arbitrary
characteristic. No identification of its kernel with integral second homology is asserted.

## References

* G. Karpilovsky, *Projective Representations of Finite Groups* (1985), Chapters 2–3.
-/

public section

namespace TauCeti

open scoped MatrixGroups

universe u

attribute [local instance] trivialMulDistribMulAction

variable (k G : Type) [Field k] [IsAlgClosed k] [Group G] [Finite G]

/-- A finite group admits a finite central stem extension lifting every matrix projective
representation over an algebraically closed field. The same extension works for all finite
index types, including the empty one, and is independent of the projective representation.
The equality asserts that the lift projectivizes to the original action pulled back along
the surjective projection. -/
theorem exists_finite_stem_extension_lifting_pgl :
    ∃ (E : Type) (_ : Group E) (_ : Finite E) (p : E →* G),
      Function.Surjective p ∧ p.ker ≤ Subgroup.center E ∧ p.ker ≤ commutator E ∧
      ∀ (ι : Type u) [Fintype ι] [DecidableEq ι] (q : G →* PGL(ι, k)),
        ∃ r : E →* GL ι k, Matrix.ProjGenLinGroup.mk.comp r = q.comp p := by
  obtain ⟨M, hM, hfin, γ, hcentral, hstem, hγ⟩ :=
    exists_finite_stem_factorSet_bijective_characterTransgression k G
  exact ⟨γ.Extension, inferInstance, inferInstance, FactorSet.rightHom γ,
    FactorSet.rightHom_surjective γ, hcentral, hstem,
    fun _ _ _ q ↦ q.exists_lift_pgl_of_characterTransgression_surjective γ hγ.surjective⟩

end TauCeti
