/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Fuchsian.Compactification.Manifold
public import TauCeti.Analysis.Complex.Fuchsian.DirichletDomain.Cofinite
import TauCeti.Geometry.Manifold.Complex.Analytic

/-!
# Cusp-free compactification and cocompact Fuchsian groups

The coarse quotient of a discrete subgroup of `PSL(2, ℝ)` is compact exactly when the group is
cofinite and has no cusp orbits. Compactness forces the dense coarse quotient to be closed in
its Hausdorff compactification, so no cusp can be adjoined. Conversely, the compactification
of a cofinite group is compact, and without cusps its coarse-quotient inclusion is surjective.

When the cusp set is empty, this inclusion is a biholomorphism, with the ordinary inclusion
as its forward map. Thus topological invariants and complex-analytic constructions on a compact
coarse quotient can be transported to the compactified surface without changing its atlas.
In particular, cell decompositions obtained from compact fundamental polygons describe that
same compactified surface.

The construction uses the open embedding and transported interior charts from
`Subgroup.CompactifiedQuotient`, and the compactness theorem for cofinite groups. Cofiniteness
of a cocompact group follows from its compact Dirichlet fundamental domain and local finiteness
of hyperbolic area.

## References

* Svetlana Katok, *Fuchsian Groups*, §§4.2–4.3.
* Fred Diamond and Jerry Shurman, *A First Course in Modular Forms*, §§2.4–2.5.
-/

public noncomputable section

open Function MeasureTheory MulAction Set Topology TauCeti UpperHalfPlane
open scoped ContDiff Manifold MatrixGroups

namespace Subgroup.CompactifiedQuotient

variable {Γ : Subgroup PSL(2, ℝ)} [DiscreteTopology Γ] [IsEmpty Γ.CuspOrbit]

/-- Without cusps, the coarse-quotient inclusion is a biholomorphism onto the compactification.
This does not require cofiniteness or compactness. -/
def ofQuotientBiholomorph : orbitRel.Quotient Γ ℍ ≃ₘ⟮𝓘(ℂ), 𝓘(ℂ)⟯ Γ.CompactifiedQuotient :=
  let e := Equiv.ofBijective (ofQuotient (Γ := Γ))
    ⟨ofQuotient_injective, ofQuotient_surjective_iff.mpr inferInstance⟩
  { toEquiv := e
    contMDiff_toFun := mdifferentiable_ofQuotient.contMDiff
    contMDiff_invFun := by
      apply MDifferentiable.contMDiff
      intro x
      obtain ⟨q, rfl⟩ := ofQuotient_surjective_iff.mpr inferInstance x
      apply mdifferentiableAt_comp_ofQuotient_iff.mp
      have hcomp : e.symm ∘ ofQuotient = id := funext e.left_inv
      rw [hcomp]
      exact mdifferentiableAt_id }

/-- The cusp-free comparison has the original inclusion as its forward function. -/
@[simp]
theorem coe_ofQuotientBiholomorph :
    ⇑(ofQuotientBiholomorph (Γ := Γ)) = ofQuotient := (rfl)

/-- The inverse comparison recovers an interior orbit unchanged. -/
@[simp]
theorem ofQuotientBiholomorph_symm_ofQuotient (q : orbitRel.Quotient Γ ℍ) :
    (ofQuotientBiholomorph (Γ := Γ)).symm (ofQuotient q) = q :=
  (ofQuotientBiholomorph (Γ := Γ)).left_inv q

end Subgroup.CompactifiedQuotient

namespace Subgroup

variable {Γ : Subgroup PSL(2, ℝ)} [DiscreteTopology Γ]

/-- A discrete subgroup has compact coarse quotient exactly when it is cofinite and cusp-free. -/
theorem compactSpace_quotient_iff_isCofinite_and_isEmpty_cuspOrbit :
    CompactSpace (orbitRel.Quotient Γ ℍ) ↔ Γ.IsCofinite ∧ IsEmpty Γ.CuspOrbit := by
  refine ⟨fun h ↦ ?_, fun ⟨hΓ, hC⟩ ↦ ?_⟩
  · let := h
    exact ⟨isCofinite_of_compactSpace, CompactifiedQuotient.isEmpty_cuspOrbit_of_compactSpace⟩
  · let := hC
    let := hΓ.compactSpace_compactifiedQuotient
    exact (CompactifiedQuotient.ofQuotientBiholomorph (Γ := Γ)).toHomeomorph.symm.compactSpace

end Subgroup
