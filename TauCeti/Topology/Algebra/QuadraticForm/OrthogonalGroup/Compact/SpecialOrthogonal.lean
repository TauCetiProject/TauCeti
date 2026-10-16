/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.QuadraticForm.OrthogonalGroup.Compact.Basic
public import TauCeti.Topology.Algebra.QuadraticForm.OrthogonalGroup.SpecialOrthogonal
import TauCeti.LinearAlgebra.QuadraticForm.Representation

/-!
# Compactness of special orthogonal groups over local fields

The special orthogonal group of an anisotropic quadratic form on a finite-dimensional space
over a locally compact nontrivially normed field is compact, with the canonical topology on
linear automorphisms. If the radical is trivial, the converse holds as well. Thus, for a form
with trivial radical, compactness of `SO(Q)` over `ℚ_p` is equivalent to anisotropy, and for a
nondegenerate real form it is equivalent to definiteness.
The real formulation is in `OrthogonalGroup.Real`.

The trivial-radical hypothesis in the converse is necessary: the zero form on a one-dimensional
space has trivial special orthogonal group, but is isotropic. Neither the sufficient condition
nor the criterion requires an assumption on the characteristic of the field. Both include
dimension zero.

The compactness implication uses the closed inclusion of `SO(Q)` into `O(Q)`. The converse
uses the unbounded split torus in the special orthogonal group of an isotropic space with
trivial radical. This noncompactness result needs neither local compactness nor a condition on `2`.

## Main results

* `TauCeti.QuadraticMap.not_isCompact_specialOrthogonalGroup`: the special orthogonal group of
  an isotropic form with trivial radical is not compact.
* `TauCeti.QuadraticMap.isCompact_specialOrthogonalGroup`: anisotropy implies compactness.
* `TauCeti.QuadraticMap.isCompact_specialOrthogonalGroup_iff`: for a form with trivial radical,
  compactness is equivalent to anisotropy.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms* (1963), §43.
-/

public section

namespace TauCeti.QuadraticMap

section Noncompact

variable {K V : Type*} [NontriviallyNormedField K] [AddCommGroup V] [Module K V]
  (Q : QuadraticForm K V)

/-- The special orthogonal group of an isotropic quadratic form with trivial radical on a
finite-dimensional space over a nontrivially normed field is not compact. -/
theorem not_isCompact_specialOrthogonalGroup [FiniteDimensional K V] (hQ : Q.radical = ⊥)
    (hiso : ¬Q.Anisotropic) :
    ¬IsCompact (specialOrthogonalGroup Q : Set (V ≃ₗ[K] V)) := by
  obtain ⟨u, v, -, hu, hv, huv⟩ :=
    _root_.QuadraticMap.exists_isotropic_pair_of_radical_eq_bot hQ hiso
  exact not_isCompact_of_hyperbolicPairTorus_sq_mem Q hu hv huv fun t =>
    hyperbolicPairTorus_mem_specialOrthogonalGroup hu hv huv (t ^ 2)

end Noncompact

section Compact

variable {K V : Type*} [NontriviallyNormedField K] [WeaklyLocallyCompactSpace K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V] (Q : QuadraticForm K V)

/-- The special orthogonal group of an anisotropic quadratic form on a finite-dimensional space
over a locally compact nontrivially normed field is compact. No nondegeneracy or characteristic
hypothesis is required. -/
theorem isCompact_specialOrthogonalGroup (hQ : Q.Anisotropic) :
    IsCompact (specialOrthogonalGroup Q : Set (V ≃ₗ[K] V)) :=
  (isCompact_orthogonalGroup Q hQ).of_isClosed_subset (isClosed_specialOrthogonalGroup Q)
    (specialOrthogonalGroup_le_orthogonalGroup Q)

/-- The special orthogonal group of a quadratic form with trivial radical on a
finite-dimensional space over a locally compact nontrivially normed field is compact exactly
when the form is anisotropic. -/
theorem isCompact_specialOrthogonalGroup_iff (hQ : Q.radical = ⊥) :
    IsCompact (specialOrthogonalGroup Q : Set (V ≃ₗ[K] V)) ↔ Q.Anisotropic :=
  ⟨fun h ↦ by_contra fun hiso ↦ not_isCompact_specialOrthogonalGroup Q hQ hiso h,
    isCompact_specialOrthogonalGroup Q⟩

end Compact

end TauCeti.QuadraticMap
