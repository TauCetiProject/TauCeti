/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.BlockSucc
public import TauCeti.RepresentationTheory.ClassicalGroups.Branching.Rationality
public import TauCeti.RepresentationTheory.ClassicalGroups.Differential

/-!
# The differential of a rational representation restricted to `GL n`

A rational representation `ρ` of `GL (n + 1) ℂ` differentiates to a representation
`dρ = TauCeti.IsRationalRep.differential` of the matrix Lie algebra `𝔤𝔩ₙ₊₁(ℂ)`. Its restriction
`ρ ∘ glBlockSucc` along the block inclusion `GL n ℂ ↪ GL (n + 1) ℂ` is again rational
(`TauCeti.IsRationalRep.comp_glBlockSucc`), so it has a differential of its own, a representation
of `𝔤𝔩ₙ(ℂ)`. This file proves that the two are compatible: the differential of the restriction is
the restriction of the differential along the corner embedding `𝔤𝔩ₙ ↪ 𝔤𝔩ₙ₊₁`,
`X ↦ diag(X, 0)`, which is `TauCeti.glEmbedding ℂ Fin.castSuccEmb`.

The block inclusion is induced by the coordinate morphism
`TauCeti.GeneralLinear.blockSuccCoordinateMap`, so the comodule of the restriction is the
corestriction of the comodule of `ρ` along it, both comodules integrating the same group action
(`TauCeti.IsRationalRep.eq_comodule`). Differentiation commutes with corestriction
(`TauCeti.Comodule.differential_corestrict`), and the differential of the coordinate morphism is
the corner embedding
(`TauCeti.GeneralLinear.tangentMatrix_derivationComp_blockSuccCoordinateMap`).

This is what transports Lie-algebra statements along the chain `GL 1 ⊂ GL 2 ⊂ ⋯ ⊂ GL n`: an
intertwiner of `GL n ℂ`-representations into the restriction of `ρ` intertwines the differentials
(`TauCeti.IsRationalRep.isIntertwiningMap_iff_forall_map_differential`), hence the action of
`𝔤𝔩ₙ` on the source with that of the upper-left corner of `𝔤𝔩ₙ₊₁` through `dρ`.

## Main results

* `TauCeti.IsRationalRep.comodule_comp_glBlockSucc`: the comodule of the restriction of `ρ` to
  `GL n ℂ` is the corestriction of the comodule of `ρ` along the block inclusion.
* `TauCeti.IsRationalRep.differential_comp_glBlockSucc`: the differential of the restriction of
  `ρ` to `GL n ℂ` is the differential of `ρ` composed with the corner embedding.
-/

public section

attribute [local instance 100] LieRing.ofAssociativeRing

namespace TauCeti

namespace IsRationalRep

open GeneralLinear

variable {n : ℕ} {W : Type*} [AddCommGroup W] [Module ℂ W]
  {ρ : Representation ℂ (GL (Fin (n + 1)) ℂ) W}

/-- **The comodule of a restriction to `GL n` is the corestricted comodule.** The comodule of the
restriction of a rational representation of `GL (n + 1) ℂ` to `GL n ℂ` is the corestriction of its
comodule along the coordinate morphism of the block inclusion. -/
theorem comodule_comp_glBlockSucc (hρ : IsRationalRep ρ)
    (hρ' : IsRationalRep (ρ.comp (glBlockSucc ℂ n))) :
    hρ'.comodule = (letI := hρ.comodule
      Comodule.Corestrict (blockSuccCoordinateMap ℂ n).toCoalgHom) := by
  let _ := hρ.comodule
  refine (hρ'.eq_comodule _ fun g ↦ ?_).symm
  rw [Comodule.basePointsRepresentation_corestrict,
    hρ.basePointsRepresentation_comodule_eq_pointsMulEquiv,
    pointsMulEquiv_mapDomain_blockSuccCoordinateMap, pointsMulEquiv_apply,
    pointToGeneralLinear_generalLinearToPoint, MonoidHom.coe_comp, Function.comp_apply]

/-- **The differential of a restriction to `GL n` is the restricted differential.** For a
rational representation `ρ` of `GL (n + 1) ℂ`, the differential of its restriction along the
block inclusion `g ↦ diag(g, 1)` is the differential of `ρ` composed with the corner embedding
`X ↦ diag(X, 0)` of `𝔤𝔩ₙ(ℂ)` in `𝔤𝔩ₙ₊₁(ℂ)`. -/
theorem differential_comp_glBlockSucc (hρ : IsRationalRep ρ)
    (hρ' : IsRationalRep (ρ.comp (glBlockSucc ℂ n))) :
    hρ'.differential = hρ.differential.comp (glEmbedding ℂ Fin.castSuccEmb) := by
  have hX (X : Matrix (Fin n) (Fin n) ℂ) :
      derivationComp (B := ℂ) (blockSuccCoordinateMap ℂ n)
          ((tangentLieEquivMatrix (R := ℂ) (B := ℂ) n).symm X) =
        (tangentLieEquivMatrix (R := ℂ) (B := ℂ) (n + 1)).symm
          (glEmbedding ℂ Fin.castSuccEmb X) := by
    rw [LieEquiv.eq_symm_apply, tangentLieEquivMatrix_apply,
      tangentMatrix_derivationComp_blockSuccCoordinateMap, ← tangentLieEquivMatrix_apply,
      LieEquiv.apply_symm_apply]
  refine LieHom.ext fun X ↦ LinearMap.ext fun w ↦ ?_
  let _ := hρ.comodule
  rw [LieHom.comp_apply, differential_apply, differential_apply, comodule_comp_glBlockSucc hρ,
    Comodule.differential_corestrict, hX]

end IsRationalRep

end TauCeti
