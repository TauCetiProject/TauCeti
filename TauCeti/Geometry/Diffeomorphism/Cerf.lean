/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Diffeomorphism.Smale
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Topology.Homotopy.Path
import TauCeti.Geometry.Diffeomorphism.Sphere.Isotopy

/-!
# Cerf's theorem: the path components of `Diff(S³)`

Cerf proved that every orientation-preserving diffeomorphism of the three-sphere is isotopic to
the identity, that is, `π₀ Diff⁺(S³) = 0`. This file states that theorem against the weak Whitney
topology on `Diff(S³)`, as `TauCeti.CerfTheorem`, and records what follows about the path
components of `Diff(S³)` from the dimension-independent results of
`TauCeti.Geometry.Diffeomorphism.Sphere.Isotopy`.

The statement avoids orientations of diffeomorphisms by comparing with the orthogonal group:
`TauCeti.CerfTheorem` says that every smooth diffeomorphism of `S³` is joined, in `Diff(S³)`, to
the restriction of an orthogonal transformation of `ℝ⁴`, so the map `π₀ O(4) → π₀ Diff(S³)`
induced by the reference inclusion `TauCeti.orthogonalToDiffSphere` is surjective. That map is
injective in every dimension (`TauCeti.joined_orthogonalToDiffSphere_iff`): two orthogonal
transformations of `ℝⁿ⁺¹` are isotopic as diffeomorphisms of `Sⁿ` exactly when they have the same
determinant. So `Diff(Sⁿ)` is never path-connected (`TauCeti.not_pathConnectedSpace_diff_sphere`),
and Cerf's theorem is equivalent to `Diff(S³)` having exactly two path components
(`TauCeti.cerfTheorem_iff_natCard_zerothHomotopy_eq_two`).

The orientation-free form is equivalent to Cerf's: a diffeomorphism isotopic to an orthogonal
transformation of determinant `-1` reverses orientation, so under `TauCeti.CerfTheorem` an
orientation-preserving diffeomorphism is isotopic to an element of `SO(4)`, hence to the identity;
and conversely an orientation-reversing diffeomorphism composed with a reflection preserves
orientation. Orientation-preservation of diffeomorphisms is not used here.

Cerf's theorem follows from the Smale conjecture `Diff(S³) ≃ O(4)` (Hatcher), since a homotopy
equivalence is surjective on path components (`TauCeti.SmaleConjecture.cerfTheorem`). It is not
proved here. Cerf's corollary `Γ₄ = 0`, that every diffeomorphism of `S³` extends over the
four-ball, is not stated here either.

## Main definitions

* `TauCeti.CerfTheorem`: every smooth diffeomorphism of `S³` is isotopic to an orthogonal one.

## Main results

* `TauCeti.SmaleConjecture.cerfTheorem`: the Smale conjecture implies Cerf's theorem.
* `TauCeti.cerfTheorem_iff_natCard_zerothHomotopy_eq_two`: Cerf's theorem holds exactly when
  `Diff(S³)` has two path components.

## References

* J. Cerf, *Sur les difféomorphismes de la sphère de dimension trois (Γ₄ = 0)*, Lecture Notes in
  Mathematics 53, Springer (1968), Théorème 1.
* A. Hatcher, *A proof of the Smale conjecture, `Diff(S³) ≃ O(4)`*, Ann. of Math. 117 (1983),
  553–607.
-/

public section

open Metric
open scoped Manifold ContDiff TauCeti.DiffeomorphWeakWhitney

namespace TauCeti

/-! ### Cerf's theorem -/

/-- **Cerf's theorem**, `π₀ Diff⁺(S³) = 0`, in orientation-free form: every smooth
diffeomorphism of the three-sphere is joined, in the weak Whitney topology, to the restriction of
an orthogonal transformation of `ℝ⁴`. Together with
`TauCeti.joined_orthogonalToDiffSphere_iff` this says that `Diff(S³)` has two path components,
the isotopy classes of the identity and of a reflection
(`TauCeti.cerfTheorem_iff_natCard_zerothHomotopy_eq_two`). It is stated, not proved. -/
def CerfTheorem : Prop :=
  ∀ f : Diff (𝓡 3) (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) ∞,
    ∃ A : Matrix.orthogonalGroup (Fin 4) ℝ, Joined (orthogonalToDiffSphere 3 ∞ A) f

/-- **The Smale conjecture implies Cerf's theorem.** A homotopy equivalence is surjective on path
components: if `g` is a homotopy inverse of the inclusion `O(4) → Diff(S³)`, then every `f` is
joined to the image of `g f` by the homotopy from the composite to the identity. -/
theorem SmaleConjecture.cerfTheorem (h : SmaleConjecture) : CerfTheorem := by
  obtain ⟨g, -, ⟨H⟩⟩ := smaleConjecture_iff_exists_homotopyInverse.1 h
  exact fun f ↦ ⟨g f, ⟨(H.evalAt f).cast (by simp) rfl⟩⟩

/-- **Cerf's theorem as a count of path components.** Cerf's theorem holds exactly when the
diffeomorphism group of `S³` has two path components. -/
theorem cerfTheorem_iff_natCard_zerothHomotopy_eq_two :
    CerfTheorem ↔
      Nat.card (ZerothHomotopy (Diff (𝓡 3) (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) ∞)) = 2 :=
  forall_exists_joined_orthogonalToDiffSphere_iff_natCard_zerothHomotopy_eq_two

end TauCeti
