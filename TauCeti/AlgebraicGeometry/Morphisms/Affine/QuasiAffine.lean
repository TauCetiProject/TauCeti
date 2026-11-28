/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
public import Mathlib.AlgebraicGeometry.QuasiAffine
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
# Universally closed morphisms from quasi-affine schemes

A universally closed morphism from a quasi-affine scheme is affine. Its graph in the product of
the target and the spectrum of the source's global sections is a closed immersion. In particular,
a proper morphism from a quasi-affine scheme is finite.

The characterization of quasi-affineness via global sections is
[Stacks Project, Tag 01P9](https://stacks.math.columbia.edu/tag/01P9).
-/

public section

open CategoryTheory Limits

namespace AlgebraicGeometry.IsAffineHom

universe u

/-- A universally closed morphism from a quasi-affine scheme is affine. -/
theorem of_universallyClosed_of_isQuasiAffine {X Y : Scheme.{u}} (f : X ⟶ Y)
    [UniversallyClosed f] [X.IsQuasiAffine] : IsAffineHom f := by
  let affinization := Spec Γ(X, ⊤)
  let graph : X ⟶ Y ⨯ affinization := prod.lift f X.toSpecΓ
  have : IsAffineHom (prod.fst : Y ⨯ affinization ⟶ Y) :=
    isAffineHom_isStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasBinaryProduct' Y affinization).flip (by
        dsimp [affinization]
        infer_instance)
  have : UniversallyClosed (graph ≫ prod.fst) := by
    simpa [graph] using (inferInstance : UniversallyClosed f)
  have : UniversallyClosed graph := UniversallyClosed.of_comp_of_isSeparated graph prod.fst
  have : IsImmersion (graph ≫ prod.snd) := by
    simpa [graph] using (inferInstance : IsImmersion X.toSpecΓ)
  have : IsImmersion graph := IsImmersion.of_comp graph prod.snd
  have : IsClosedImmersion graph := .of_isPreimmersion graph graph.isClosedMap.isClosed_range
  simpa [graph] using (inferInstance : IsAffineHom (graph ≫ prod.fst))

end AlgebraicGeometry.IsAffineHom
