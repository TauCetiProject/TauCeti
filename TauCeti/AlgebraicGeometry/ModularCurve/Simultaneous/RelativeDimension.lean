/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import TauCeti.AlgebraicGeometry.ModularCurve.ModuliProblem
import TauCeti.AlgebraicGeometry.ModularCurve.Simultaneous.Projections
import TauCeti.AlgebraicGeometry.Morphisms.Smooth.SourceDescent

/-!
# Transfer of smooth relative dimension along rigidifiers

Let `𝒫` and `𝒬` be representable, relatively representable, étale moduli problems over `Ell/B`,
with `𝒬` surjective over `Ell/B`. The simultaneous moduli scheme `𝕄(𝒬, 𝒫)` maps étale and
surjectively to the scheme representing `𝒫`, and étale to the scheme representing `𝒬`
(`ModuliProblem.RelRepData.mem_base_of_forget_snd`). When the scheme representing `𝒫` is smooth
over `B` and the scheme representing `𝒬` is smooth of relative dimension `n` over `B`, source
descent of smooth relative dimension along étale surjections
(`AlgebraicGeometry.SmoothOfRelativeDimension.of_comp_of_etale_of_surjective`) transfers smooth
relative dimension `n` to the scheme representing `𝒫`
(`ModuliProblem.RelRepData.smoothOfRelativeDimension_of_representableBy`).

## Main results

* `ModuliProblem.RelRepData.smoothOfRelativeDimension_of_representableBy`:
  smooth relative dimension transfers from an étale surjective rigidifier to any smooth
  representable étale moduli problem.
* `ModuliProblem.RelRepData.smoothOfRelativeDimension_iff_of_representableBy`:
  two representable, relatively representable, étale and surjective moduli problems whose bases are
  smooth over `B` have bases of the same smooth relative dimension over `B`.

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, Annals of Mathematics Studies
  108, Princeton University Press, 1985, 4.7 and 4.12.
-/

public section

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace TauCeti.AlgebraicGeometry.ModuliProblem.RelRepData

variable {B : Scheme.{u}} {n : ℕ}

/-- **Transfer of smooth relative dimension along a rigidifier.** Let `𝒫` and `𝒬` be moduli
problems over `Ell/B` represented by `U` and `V`, both relatively representable and étale over
`Ell/B`, with `𝒬` also surjective over `Ell/B`. If the base of `U` is smooth over `B` and the base
of `V` is smooth of relative dimension `n` over `B`, then the base of `U` is smooth of relative
dimension `n` over `B`. -/
theorem smoothOfRelativeDimension_of_representableBy {P Q : ModuliProblem B} {U V : EllObj B}
    (RP : P.RepresentableBy U) (RQ : Q.RepresentableBy V)
    (DP : P.RelRepData) (DQ : Q.RelRepData)
    (heP : DP.HasProperty @Etale) (heQ : DQ.HasProperty @Etale)
    (hsQ : DQ.HasProperty @Surjective)
    [Smooth U.structureMap] [SmoothOfRelativeDimension n V.structureMap] :
    SmoothOfRelativeDimension n U.structureMap := by
  let S := DQ.tensorRepresentableBy RP
  let a₁ := U.baseChangeFunctorHom (DQ.rep U)
  let a₂ := RQ.homEquiv.symm (S.homEquiv (𝟙 _)).1
  have : Etale a₁.base := by
    rw [EllObj.baseChangeFunctorHom_base]
    exact DQ.hasProperty_iff.mp heQ U
  have : Surjective a₁.base := by
    rw [EllObj.baseChangeFunctorHom_base]
    exact DQ.hasProperty_iff.mp hsQ U
  have ha₂ : RQ.homEquiv a₂ = (S.homEquiv (𝟙 _)).1 := RQ.homEquiv.apply_symm_apply _
  have : MorphismProperty.RespectsIso @Etale.{u} :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have : Etale a₂.base := DP.mem_base_of_forget_snd RQ S a₂ ha₂ (DP.hasProperty_iff.mp heP V)
  have hW : SmoothOfRelativeDimension (0 + n) (a₂.base ≫ V.structureMap) := inferInstance
  have : SmoothOfRelativeDimension n (a₁.base ≫ U.structureMap) := by
    rw [a₁.base_structureMap, ← a₂.base_structureMap]
    simpa only [Nat.zero_add] using hW
  exact SmoothOfRelativeDimension.of_comp_of_etale_of_surjective a₁.base U.structureMap

/-- Two representable, relatively representable, étale and surjective moduli problems over `Ell/B`
whose bases are smooth over `B` have bases of the same smooth relative dimension over `B`. -/
theorem smoothOfRelativeDimension_iff_of_representableBy {P Q : ModuliProblem B} {U V : EllObj B}
    (RP : P.RepresentableBy U) (RQ : Q.RepresentableBy V)
    (DP : P.RelRepData) (DQ : Q.RelRepData)
    (heP : DP.HasProperty @Etale) (hsP : DP.HasProperty @Surjective)
    (heQ : DQ.HasProperty @Etale) (hsQ : DQ.HasProperty @Surjective)
    [Smooth U.structureMap] [Smooth V.structureMap] :
    SmoothOfRelativeDimension n U.structureMap ↔ SmoothOfRelativeDimension n V.structureMap :=
  ⟨fun _ ↦ smoothOfRelativeDimension_of_representableBy RQ RP DQ DP heQ heP hsP,
    fun _ ↦ smoothOfRelativeDimension_of_representableBy RP RQ DP DQ heP heQ hsQ⟩

end TauCeti.AlgebraicGeometry.ModuliProblem.RelRepData
