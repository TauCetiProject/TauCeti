/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import TauCeti.AlgebraicGeometry.Morphisms.Smooth.FormallySmooth
import TauCeti.AlgebraicGeometry.Morphisms.Etale.UniversalHomeomorphism

/-!
# Étale and formally étale morphisms of schemes

We compare Mathlib's étale morphisms of schemes with Tau Ceti's formally étale morphisms, defined
by unique infinitesimal lifting along affine first-order thickenings.

## Main results

* `TauCeti.AlgebraicGeometry.FormallyEtale.of_etale`: an étale morphism, for instance an open
  immersion, is formally étale: every commutative square against a first-order thickening with
  affine target has a unique lift. The lifts come from
  `IsUniversalHomeomorphism.hasLiftingProperty_of_etale`, since first-order thickenings are
  universal homeomorphisms.
* `TauCeti.AlgebraicGeometry.etale_iff_formallyEtale`: a morphism locally of finite presentation
  is étale if and only if it is formally étale.

## References

* [Stacks Project, Lemma 37.8.10](https://stacks.math.columbia.edu/tag/02HM), étale morphisms
  and formally étale morphisms locally of finite presentation.
-/

public section

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace TauCeti.AlgebraicGeometry

variable {X S : Scheme.{u}}

/-- An étale morphism is formally étale: every commutative square of an étale morphism against a
first-order thickening with affine target has a unique lift. -/
instance (priority := 100) FormallyEtale.of_etale (f : X ⟶ S) [Etale f] : FormallyEtale f :=
  -- First-order thickenings are universal homeomorphisms, so lifts exist by
  -- `IsUniversalHomeomorphism.hasLiftingProperty_of_etale`; étale morphisms are formally
  -- unramified, so lifts are unique.
  (formallyEtale_iff f).2
    ⟨⟨fun i _ a h w ↦ let sq : CommSq a i f h := ⟨w⟩; ⟨sq.lift, sq.fac_left, sq.fac_right⟩⟩,
      inferInstance⟩

/-- A formally étale morphism locally of finite presentation is étale. -/
theorem etale_of_formallyEtale (f : X ⟶ S) [FormallyEtale f]
    [LocallyOfFinitePresentation f] : Etale f :=
  have := smooth_of_formallySmooth f
  Etale.of_formallyUnramified_of_flat f

/-- A morphism locally of finite presentation is étale if and only if it is formally étale. -/
@[stacks 02HM]
theorem etale_iff_formallyEtale (f : X ⟶ S) [LocallyOfFinitePresentation f] :
    Etale f ↔ FormallyEtale f :=
  ⟨fun _ ↦ inferInstance, fun _ ↦ etale_of_formallyEtale f⟩

end TauCeti.AlgebraicGeometry
