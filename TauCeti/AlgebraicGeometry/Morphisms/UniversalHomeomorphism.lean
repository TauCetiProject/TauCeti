/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective

/-!
# Consequences of being a universal homeomorphism

A morphism of schemes `f : X ⟶ Y` is a *universal homeomorphism* when every base change of `f` is
a homeomorphism of underlying spaces. It is written here in Mathlib's form
`(topologically @IsHomeomorph).universally f`. This file records that such a morphism is
surjective, universally injective (radicial) and universally closed.

## Main results

* `AlgebraicGeometry.Surjective.of_universally_isHomeomorph`,
  `AlgebraicGeometry.UniversallyInjective.of_universally_isHomeomorph` and
  `AlgebraicGeometry.UniversallyClosed.of_universally_isHomeomorph`: a universal homeomorphism is
  surjective, universally injective and universally closed.
-/

public section

open CategoryTheory MorphismProperty

universe u

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}} {f : X ⟶ Y}

/-- A universal homeomorphism is surjective. -/
theorem Surjective.of_universally_isHomeomorph (hf : (topologically @IsHomeomorph).universally f) :
    Surjective f :=
  ⟨(universally_le _ _ hf).surjective⟩

/-- A universal homeomorphism is universally injective. -/
theorem UniversallyInjective.of_universally_isHomeomorph
    (hf : (topologically @IsHomeomorph).universally f) : UniversallyInjective f :=
  ⟨universally_mono (fun _ _ _ ↦ IsHomeomorph.injective) _ hf⟩

/-- A universal homeomorphism is universally closed. -/
theorem UniversallyClosed.of_universally_isHomeomorph
    (hf : (topologically @IsHomeomorph).universally f) : UniversallyClosed f :=
  ⟨universally_mono (fun _ _ _ ↦ IsHomeomorph.isClosedMap) _ hf⟩

end AlgebraicGeometry
