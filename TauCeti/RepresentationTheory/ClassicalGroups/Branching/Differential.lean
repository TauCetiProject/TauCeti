/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.BlockSucc
public import TauCeti.Algebra.Lie.UniversalEnveloping.Functoriality
public import TauCeti.RepresentationTheory.ClassicalGroups.Branching.Rationality
public import TauCeti.RepresentationTheory.ClassicalGroups.Differential

/-!
# Differentiating a rational representation restricted along the block inclusion

Restricting a rational representation `ρ` of `GL (n + 1) ℂ` along the block inclusion
`TauCeti.glBlockSucc : GL n ℂ → GL (n + 1) ℂ`, `g ↦ diag(g, 1)`, gives a rational representation
of `GL n ℂ` (`TauCeti.IsRationalRep.comp_glBlockSucc`). Its differential is the restriction of
the differential of `ρ` along the corner embedding `𝔤𝔩ₙ → 𝔤𝔩ₙ₊₁`, `X ↦ diag(X, 0)`: the comodule of
the restriction is the corestriction of the comodule of `ρ` along the coordinate morphism of the
block inclusion, `TauCeti.GeneralLinear.blockSuccCoordinateMap`, whose tangent map is the corner
embedding.

This is the compatibility of differentiation with the chain `GL 1 ⊂ GL 2 ⊂ ⋯` that lets the
Lie-algebraic Gelfand–Tsetlin generators, which live in the enveloping algebras of the corners
`𝔤𝔩₁ ⊂ 𝔤𝔩₂ ⊂ ⋯`, act compatibly on the branching of a rational representation.

## Main results

* `TauCeti.IsRationalRep.differential_comp_glBlockSucc`: the differential of the restriction is
  the differential of `ρ` composed with the corner embedding.
* `TauCeti.IsRationalRep.lift_differential_comp_glBlockSucc`: the same statement for the actions
  of the universal enveloping algebras.
-/

public section

attribute [local instance 100] LieRing.ofAssociativeRing

namespace TauCeti

namespace IsRationalRep

open GeneralLinear

variable {n : ℕ} {W : Type*} [AddCommGroup W] [Module ℂ W]
  {ρ : Representation ℂ (GL (Fin (n + 1)) ℂ) W}

/-- The comodule of the restriction of `ρ` along the block inclusion is the corestriction of the
comodule of `ρ` along the coordinate morphism of the block inclusion. -/
private theorem comodule_comp_glBlockSucc (hρ : IsRationalRep ρ) :
    hρ.comp_glBlockSucc.comodule =
      letI := hρ.comodule
      Comodule.Corestrict (blockSuccCoordinateMap ℂ n).toCoalgHom := by
  let _ := hρ.comodule
  refine (hρ.comp_glBlockSucc.eq_comodule _ fun g ↦ ?_).symm
  rw [Comodule.basePointsRepresentation_corestrict,
    mapDomain_blockSuccCoordinateMap_generalLinearToPoint, basePointsRepresentation_comodule,
    MonoidHom.comp_apply]

/-- **The differential of a restriction along the block inclusion** is the differential of the
original representation composed with the corner embedding `X ↦ diag(X, 0)` of `𝔤𝔩ₙ` in
`𝔤𝔩ₙ₊₁`. -/
@[simp]
theorem differential_comp_glBlockSucc (hρ : IsRationalRep ρ) (X : Matrix (Fin n) (Fin n) ℂ) :
    hρ.comp_glBlockSucc.differential X = hρ.differential (glEmbedding ℂ Fin.castSuccEmb X) := by
  have hX : (tangentLieEquivMatrix (R := ℂ) (B := ℂ) (n + 1)).symm
      (glEmbedding ℂ Fin.castSuccEmb X) =
        derivationComp (blockSuccCoordinateMap ℂ n)
          ((tangentLieEquivMatrix (R := ℂ) (B := ℂ) n).symm X) := by
    rw [LieEquiv.symm_apply_eq, tangentLieEquivMatrix_apply,
      tangentMatrix_derivationComp_blockSuccCoordinateMap, ← tangentLieEquivMatrix_apply,
      LieEquiv.apply_symm_apply]
  refine LinearMap.ext fun w ↦ ?_
  rw [differential_apply, differential_apply, hX, comodule_comp_glBlockSucc hρ]
  let _ := hρ.comodule
  exact Comodule.differential_corestrict W _ _ w

/-- **The enveloping-algebra form of `TauCeti.IsRationalRep.differential_comp_glBlockSucc`**:
`U(𝔤𝔩ₙ)` acts on the restriction of `ρ` along the block inclusion through the map of enveloping
algebras induced by the corner embedding. -/
theorem lift_differential_comp_glBlockSucc (hρ : IsRationalRep ρ)
    (u : UniversalEnvelopingAlgebra ℂ (Matrix (Fin n) (Fin n) ℂ)) :
    UniversalEnvelopingAlgebra.lift ℂ hρ.comp_glBlockSucc.differential u =
      UniversalEnvelopingAlgebra.lift ℂ hρ.differential
        (UniversalEnvelopingAlgebra.map ℂ (glEmbedding ℂ Fin.castSuccEmb) u) := by
  rw [← AlgHom.comp_apply]
  congr 1
  refine UniversalEnvelopingAlgebra.hom_ext ℂ (LieHom.ext fun X ↦ ?_)
  simp only [LieHom.comp_apply, AlgHom.coe_toLieHom, AlgHom.comp_apply,
    UniversalEnvelopingAlgebra.lift_ι_apply, UniversalEnvelopingAlgebra.map_ι]
  exact hρ.differential_comp_glBlockSucc X

end IsRationalRep

end TauCeti
