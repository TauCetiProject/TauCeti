/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.RingTheory.LocalProperties.IntegrallyClosed

/-!
# Integrally closed sections of affine opens

If the ring of sections over an affine open `V` is a domain, it is integrally closed as
soon as the local rings at the points of `V` are: its localizations at maximal ideals are local
rings of the scheme at points of `V`.

## Main results

* `AlgebraicGeometry.IsAffineOpen.isIntegrallyClosed`: a domain of sections over an affine
  open is integrally closed when its local rings are.
* `TauCeti.AlgebraicGeometry.isDomain_and_isIntegrallyClosed_stalk_iff_of_isOpenImmersion`: open
  immersions preserve the domain and integral-closure conditions on stalks.
-/

public section

open CategoryTheory AlgebraicGeometry

universe u

namespace TauCeti.AlgebraicGeometry

/-- An open immersion identifies the local rings at corresponding points, preserving the
conjunction of domain and integral-closure properties. -/
theorem isDomain_and_isIntegrallyClosed_stalk_iff_of_isOpenImmersion {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsOpenImmersion f] (x : X) :
    IsDomain (Y.presheaf.stalk (f x)) ∧ IsIntegrallyClosed (Y.presheaf.stalk (f x)) ↔
      IsDomain (X.presheaf.stalk x) ∧ IsIntegrallyClosed (X.presheaf.stalk x) :=
  let e := (asIso (f.stalkMap x)).commRingCatIsoToRingEquiv
  by
    constructor
    · intro h
      obtain ⟨_, _⟩ := h
      exact ⟨e.symm.toMulEquiv.isDomain _, .of_equiv e⟩
    · intro h
      obtain ⟨_, _⟩ := h
      exact ⟨e.toMulEquiv.isDomain _, .of_equiv e.symm⟩

end TauCeti.AlgebraicGeometry

namespace AlgebraicGeometry

variable {T : Scheme.{u}}

/-- The domain of sections over an affine open `V` is integrally closed if the local rings
at the points of `V` are: its localizations at maximal ideals are local rings of the scheme at
points of `V`. -/
theorem IsAffineOpen.isIntegrallyClosed {V : T.Opens} [IsDomain Γ(T, V)] (hV : IsAffineOpen V)
    (hT : ∀ x ∈ V, IsIntegrallyClosed (T.presheaf.stalk x)) :
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
