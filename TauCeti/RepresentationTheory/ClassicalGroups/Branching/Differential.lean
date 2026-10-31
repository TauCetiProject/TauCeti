/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.GeneralLinear.Embedding
public import TauCeti.RepresentationTheory.ClassicalGroups.Branching.Rationality
public import TauCeti.RepresentationTheory.ClassicalGroups.Differential
import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.BlockSucc

/-!
# Differentiating a restriction along the block inclusion

Restricting a rational representation `ρ` of `GL (n + 1) ℂ` along the block inclusion
`TauCeti.glBlockSucc : GL n ℂ →* GL (n + 1) ℂ` gives a rational representation of `GL n ℂ`
(`TauCeti.IsRationalRep.comp_glBlockSucc`). This file shows that its differential is the
differential of `ρ` restricted along the corner embedding `𝔤𝔩ₙ → 𝔤𝔩ₙ₊₁`, which places a matrix
in the upper-left block and pads it with zeros (`TauCeti.glEmbedding` along `Fin.castSuccEmb`):

`d(ρ ∘ glBlockSucc) = dρ ∘ glEmbedding`.

So the Lie algebra `𝔤𝔩ₙ` acts on the restriction through the upper-left corner of `𝔤𝔩ₙ₊₁`. Together
with `TauCeti.IsRationalRep.isIntertwiningMap_iff_forall_map_differential`, this says that an
intertwiner of `GL n ℂ`-representations into the restriction of `ρ` intertwines the actions of that
corner.

## The argument

The comodule of the restriction is the comodule of `ρ` corestricted along the comorphism
`TauCeti.GeneralLinear.blockSuccCoordinateMap : O(GLₙ₊₁) → O(GLₙ)` of the block inclusion: both
integrate the restricted representation, and a comodule over `O(GLₙ)` is determined by its
complex points (`TauCeti.IsRationalRep.eq_comodule`). Differentiating a corestricted comodule
precomposes with the tangent map of the comorphism (`TauCeti.Comodule.differential_corestrict`),
and that tangent map is the corner embedding
(`TauCeti.GeneralLinear.tangentMatrix_derivationComp_blockSuccCoordinateMap`).

## Main results

* `TauCeti.IsRationalRep.differential_comp_glBlockSucc`: the differential of the restriction is
  the differential of `ρ` along the corner embedding.
-/

public section

attribute [local instance 100] LieRing.ofAssociativeRing

namespace TauCeti

namespace IsRationalRep

open GeneralLinear

variable {n : ℕ} {W : Type*} [AddCommGroup W] [Module ℂ W]
  {ρ : Representation ℂ (GL (Fin (n + 1)) ℂ) W}

/-- The comodule of the restriction of a rational representation along the block inclusion is the
corestriction of its comodule along the comorphism of the block inclusion. -/
private theorem comodule_comp_glBlockSucc (hρ : IsRationalRep ρ) :
    hρ.comp_glBlockSucc.comodule =
      letI := hρ.comodule
      Comodule.Corestrict (blockSuccCoordinateMap ℂ n).toCoalgHom := by
  let _ := hρ.comodule
  refine (hρ.comp_glBlockSucc.eq_comodule _ fun g ↦ ?_).symm
  rw [Comodule.basePointsRepresentation_corestrict,
    mapDomain_blockSuccCoordinateMap_generalLinearToPoint, basePointsRepresentation_comodule,
    MonoidHom.comp_apply]

/-- **The differential of a restriction along the block inclusion**: restricting a rational
representation `ρ` of `GL (n + 1) ℂ` to `GL n ℂ` and differentiating gives the differential of
`ρ` on the upper-left corner `𝔤𝔩ₙ ⊆ 𝔤𝔩ₙ₊₁`. -/
theorem differential_comp_glBlockSucc (hρ : IsRationalRep ρ) :
    hρ.comp_glBlockSucc.differential =
      hρ.differential.comp (glEmbedding ℂ Fin.castSuccEmb) := by
  ext X : 1
  let _ := hρ.comodule
  have hX : (tangentLieEquivMatrix (R := ℂ) (B := ℂ) (n + 1)).symm
      (glEmbedding ℂ Fin.castSuccEmb X) =
        derivationComp (B := ℂ) (blockSuccCoordinateMap ℂ n)
          ((tangentLieEquivMatrix (R := ℂ) (B := ℂ) n).symm X) := by
    rw [LieEquiv.symm_apply_eq, tangentLieEquivMatrix_apply,
      tangentMatrix_derivationComp_blockSuccCoordinateMap, ← tangentLieEquivMatrix_apply,
      LieEquiv.apply_symm_apply]
  rw [LieHom.comp_apply, differential_apply hρ.comp_glBlockSucc, differential_apply hρ, hX,
    comodule_comp_glBlockSucc hρ]
  exact LinearMap.ext fun w ↦ Comodule.differential_corestrict W _ _ w

end IsRationalRep

end TauCeti
