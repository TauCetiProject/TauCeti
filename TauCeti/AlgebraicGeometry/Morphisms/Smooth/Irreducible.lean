/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import TauCeti.AlgebraicGeometry.Morphisms.Smooth.Regular
import TauCeti.AlgebraicGeometry.IrreducibleOfConnectedDomainStalk

/-!
# Connected smooth schemes over a regular base are irreducible

A connected scheme that is smooth over a locally Noetherian scheme with regular local rings is
irreducible. In particular a connected scheme smooth over a field is irreducible, and so is the
base change to `AlgebraicClosure K` of a smooth `K`-scheme whenever that base change is connected.

## Main results

* `TauCeti.AlgebraicGeometry.Smooth.irreducibleSpace_of_connectedSpace`: a connected scheme smooth
  over a locally Noetherian scheme with regular local rings is irreducible.
* `TauCeti.AlgebraicGeometry.Smooth.irreducibleSpace_baseChange_algebraicClosure_of_connectedSpace`:
  for a smooth morphism `X ⟶ Spec K`, the base change of `X` to `AlgebraicClosure K` is
  irreducible if it is connected.

## Provenance

The statements generalise two from AINTLIB (`github.com/CBirkbeck/AINTLIB`, Apache-2.0) at commit
`c3415f32a313e19ace43e05479aeaa0d56ca287a`:
`ModularCurves.irreducibleSpace_of_connectedSpace_of_smooth_curve` in
`projects/ModularCurves/ModularCurves/ForMathlib/SmoothSchemeIrreducible.lean`, for schemes smooth
of relative dimension one over an algebraically closed field, and
`ModularCurves.yRho_geometricallyIrreducible_of_connected'` in
`projects/ModularCurves/ModularCurves/ModularCurve/IrreducibilityScoping.lean`, for the base change
to `AlgebraicClosure ℚ` of a `ℚ`-scheme representing the `ρ`-level moduli problem, a hypothesis
that includes smoothness of relative dimension one. The source proves the first from irreducible
open neighbourhoods in standard smooth charts; the proof here uses the regularity of the local
rings.
-/

public section

open CategoryTheory Limits AlgebraicGeometry

namespace TauCeti

namespace AlgebraicGeometry

universe u

/-- A connected scheme smooth over a locally Noetherian scheme with regular local rings is
irreducible. In particular, a connected scheme smooth over a field is irreducible. -/
theorem Smooth.irreducibleSpace_of_connectedSpace {X S : Scheme.{u}} (f : X ⟶ S) [Smooth f]
    [IsLocallyNoetherian S] [∀ s : S, IsRegularLocalRing (S.presheaf.stalk s)] [ConnectedSpace X] :
    IrreducibleSpace X :=
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have := isRegularLocalRing_stalk_of_smooth f
  irreducibleSpace_of_connected_of_isDomain_stalk X fun _ ↦ inferInstance

/-- If `f : X ⟶ Spec K` is smooth and the base change of `X` to `AlgebraicClosure K` is connected,
then that base change is irreducible. -/
theorem Smooth.irreducibleSpace_baseChange_algebraicClosure_of_connectedSpace {K : Type u} [Field K]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of K)) [Smooth f] (hconn : ConnectedSpace
      ↥(pullback f (Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K)))))) :
    IrreducibleSpace
      ↥(pullback f (Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K))))) :=
  irreducibleSpace_of_connectedSpace (pullback.snd f _)

end AlgebraicGeometry

end TauCeti
