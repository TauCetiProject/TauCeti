/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.RingTheory.LocalProperties.IntegrallyClosed

/-!
# Integrally closed sections of integral schemes

On an integral scheme, the ring of sections over a nonempty affine open `V` is integrally closed
as soon as the local rings at the points of `V` are: its localizations at maximal ideals are local
rings of the scheme at points of `V`.

## Main results

* `AlgebraicGeometry.IsAffineOpen.isIntegrallyClosed`: on an integral scheme with integrally
  closed local rings, the sections over a nonempty affine open are integrally closed.
-/

public section

namespace AlgebraicGeometry

universe u

variable {T : Scheme.{u}}

/-- On an integral scheme, the ring of sections over a nonempty affine open `V` is integrally
closed if the local rings at the points of `V` are: its localizations at maximal ideals are local
rings of the scheme at points of `V`. -/
theorem IsAffineOpen.isIntegrallyClosed [IsIntegral T] {V : T.Opens} (hV : IsAffineOpen V)
    [Nonempty V] (hT : ∀ x ∈ V, IsIntegrallyClosed (T.presheaf.stalk x)) :
    IsIntegrallyClosed Γ(T, V) := by
  refine IsIntegrallyClosed.of_localization_maximal fun P _ _ ↦ ?_
  let y : PrimeSpectrum Γ(T, V) := ⟨P, inferInstance⟩
  have hy : hV.fromSpec y ∈ V := hV.range_fromSpec.subset (Set.mem_range_self y)
  let := TopCat.Presheaf.algebra_section_stalk T.presheaf ⟨hV.fromSpec y, hy⟩
  have : IsLocalization P.primeCompl (T.presheaf.stalk (hV.fromSpec y)) :=
    hV.isLocalization_stalk' y hy
  exact (hT (hV.fromSpec y) hy).of_equiv (IsLocalization.algEquiv P.primeCompl
    (T.presheaf.stalk (hV.fromSpec y)) (Localization.AtPrime P)).toRingEquiv

end AlgebraicGeometry
