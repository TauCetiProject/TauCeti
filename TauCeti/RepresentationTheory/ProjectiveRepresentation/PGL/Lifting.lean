/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.ProjectiveRepresentation.PGL.Basic
public import TauCeti.RepresentationTheory.ProjectiveRepresentation.Linearization

/-!
# Lifting matrix projective representations over a prescribed extension

Surjective character transgression of a factor-set extension guarantees that every
homomorphism to a finite matrix projective linear group lifts to a homomorphism to the
general linear group of the same size. The resulting square commutes exactly after
projectivization: no choice of scalar representatives appears in the conclusion.

This combines `MonoidHom.exists_isProjectiveRep_toPGL_eq` with
`TauCeti.IsProjectiveRep.exists_linearization_of_characterTransgression_surjective`.
The kernel action need not be trivial; equivariant kernel characters suffice.

## References

* G. Karpilovsky, *Projective Representations of Finite Groups* (1985), Chapters 1 and 3.
-/

public section

namespace MonoidHom

open TauCeti
open scoped MatrixGroups

attribute [local instance] trivialMulDistribMulAction

variable {k G M : Type} {ι : Type*} [CommRing k] [Group G] [CommGroup M]
  [MulDistribMulAction G M] [Fintype ι] [DecidableEq ι]

/-- Surjective character transgression makes every matrix projective representation lift
over the prescribed extension, with exactly the original projectivization. This includes
the empty matrix size and requires neither a field nor a finite group. -/
theorem exists_lift_pgl_of_characterTransgression_surjective (q : G →* PGL(ι, k))
    (γ : FactorSet G M)
    (hγ : Function.Surjective (γ.characterTransgression (A := kˣ))) :
    ∃ r : γ.Extension →* GL ι k,
      Matrix.ProjGenLinGroup.mk.comp r = q.comp (FactorSet.rightHom γ) := by
  let b := Pi.basisFun k ι
  obtain ⟨ρ, α, hρ, hq⟩ := q.exists_isProjectiveRep_toPGL_eq b
  obtain ⟨χ, c, π, -, hπ⟩ :=
    hρ.exists_linearization_of_characterTransgression_surjective γ hγ
  refine ⟨b.toGL.toMonoidHom.comp π, ?_⟩
  ext x
  simp only [comp_apply, MulEquiv.coe_toMonoidHom, hπ,
    ← LinearEquiv.mul_eq_trans, map_mul, Module.Basis.toGL_smulOfUnit,
    Matrix.ProjGenLinGroup.mk_scalar, one_mul]
  simpa only [IsProjectiveRep.toPGL_apply, FactorSet.rightHom_apply] using
    congrArg (fun f : G →* PGL(ι, k) ↦ f x.right) hq

end MonoidHom
