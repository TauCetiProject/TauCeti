/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- `TauCeti.Algebra.CentralSimple.Subfield` is imported publicly: `TauCeti.Algebra.deg` and
-- `TauCeti.Algebra.IsSplittingField` occur in the statements below, and
-- `TauCeti.Algebra.isSplittingField_of_finrank_eq_deg` is the theorem the summit of this file
-- feeds. It re-exports `TauCeti.Algebra.CentralSimple.Splitting` and, through it, the degree API,
-- as well as `Subalgebra` and `IsField.of_isDomain_of_finite`, which turns a commutative subalgebra
-- into a subfield.
public import TauCeti.Algebra.CentralSimple.Subfield
-- Non-public: the stronger separable existence results are used only in proofs, and the
-- real quaternions and their centrality appear only in the worked examples.
import Mathlib.Basic.Real.Basic
import TauCeti.Algebra.Central.Quaternion
import TauCeti.Algebra.CentralSimple.MaximalSubfield.Separable

/-!
# Maximal subfields of a central division algebra

Let `K` be a field and `D` a finite-dimensional central division algebra over `K`.
`TauCeti/Algebra/CentralSimple/Subfield.lean` proves that a subfield of `D` has degree at most
`TauCeti.Algebra.deg K D`, and that a subfield attaining that bound splits `D`; what it leaves
open, in as many words, is whether the bound is attained at all. This file settles that: **`D` has
a subfield of degree exactly `deg K D`**, so the splitting field produced there is never vacuous
and every central division algebra is split by a finite extension of its centre sitting inside it.

The existence results are consequences of the stronger separable results in
`TauCeti/Algebra/CentralSimple/MaximalSubfield/Separable.lean`, obtained by dropping the
separability conclusion. That file constructs a separable commutative subalgebra of maximal
dimension, proves that it is its own centralizer, and uses the centralizer dimension formula
to determine its degree.

## Main results

* `TauCeti.Algebra.exists_subalgebra_isField_finrank_eq_deg`: **a central division algebra has a
  subfield of degree `deg K D`.**
* `TauCeti.Algebra.exists_isSplittingField_finrank_eq_deg`: **a central division algebra is split
  by a subfield of degree `deg K D`.**

## Implementation notes

The existence statements are stated for a **division** algebra. The passage from there to an
arbitrary central simple algebra `A ≃ₐ[K] Mₙ(D)`, and with it the index `ind A`, needs the
uniqueness of the division algebra in a Wedderburn presentation and is not done here.

## References

This is the maximal-subfield existence half of the fourth bullet of Layer 6 ("Splitting fields,
maximal subfields, and the index": "a **maximal subfield** `L` of a central division algebra `D`
(with `finrank K L = deg D`) splits `D`") of the
[semisimple algebras roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SemisimpleAlgebras/README.md).
See P. Gille, T. Szamuely, *Central Simple Algebras and Galois Cohomology*, Section 2.2, and
R. S. Pierce, *Associative Algebras*, GTM 88, Chapter 13.
-/

public section

namespace TauCeti

open Module

universe u

/-! ### A maximal subfield of a central division algebra -/

namespace Algebra

variable (K : Type*) [Field K] (D : Type u) [DivisionRing D] [Algebra K D] [Algebra.IsCentral K D]
  [FiniteDimensional K D]

/-- **A central division algebra has a subfield of degree `deg K D`.**

The subfield is delivered as a `Subalgebra K D` carrying `IsField`;
`TauCeti.Algebra.exists_isSplittingField_finrank_eq_deg` is the same subfield packaged as a field
in its own right, together with its embedding in `D`.

Together with `TauCeti.Algebra.finrank_le_deg`, which bounds the degree of *every* subfield by
`deg K D`, this says `L` is a maximal subfield in the literal sense as well. -/
theorem exists_subalgebra_isField_finrank_eq_deg :
    ∃ L : Subalgebra K D, IsField ↥L ∧ finrank K ↥L = deg K D := by
  obtain ⟨L, hfield, _, hdeg⟩ := exists_subalgebra_isField_isSeparable_finrank_eq_deg K D
  exact ⟨L, hfield, hdeg⟩

/-- **A central division algebra is split by a subfield of degree `deg K D`.**

This is the maximal-subfield route to a splitting field: unlike the passage to an algebraic
closure (`TauCeti.Algebra.isSplittingField_of_isSepClosed`), it produces a splitting field that is
a *finite* extension of `K`, and one realized inside `D` by the accompanying homomorphism. -/
theorem exists_isSplittingField_finrank_eq_deg :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra K L) (_ : L →ₐ[K] D),
      FiniteDimensional K L ∧ finrank K L = deg K D ∧ IsSplittingField K D L := by
  obtain ⟨L, hfield, halg, f, hfinite, _, hdeg, hsplit⟩ :=
    exists_isSplittingField_isSeparable_finrank_eq_deg K D
  exact ⟨L, hfield, halg, f, hfinite, hdeg, hsplit⟩

end Algebra

/-! ### Worked example: a maximal subfield of the real quaternions -/

section Examples

-- `_root_.` is needed because `TauCeti.Quaternion` is also a namespace, so a bare
-- `open scoped Quaternion` would open that one and leave the `ℍ[·]` notation out of scope.
open scoped _root_.Quaternion

/-- **The real quaternions have a subfield of degree `2`.** The general theorem produces one
without exhibiting a copy of `ℂ` by hand. Which subfield it is takes the classification of the
finite extensions of `ℝ`, not proved here, to say: every degree-`2` extension of `ℝ` is
`ℝ`-isomorphic to `ℂ`. The example in `TauCeti/Algebra/CentralSimple/Subfield.lean` exhibits a
copy of `ℂ` inside `ℍ[ℝ]` by hand instead. -/
example : ∃ L : Subalgebra ℝ ℍ[ℝ], IsField ↥L ∧ Module.finrank ℝ ↥L = 2 := by
  have hdeg : Algebra.deg ℝ ℍ[ℝ] = 2 :=
    Algebra.deg_eq_of_finrank_eq_sq (by rw [Quaternion.finrank_eq_four]; norm_num)
  exact hdeg ▸ Algebra.exists_subalgebra_isField_finrank_eq_deg ℝ ℍ[ℝ]

/-- **A subalgebra of `ℍ[ℝ]` of degree `2` is not the base field**, so when `deg K D > 1` the
subfield produced above genuinely enlarges the centre; the existence theorem is not answered by
`K` itself. -/
example (L : Subalgebra ℝ ℍ[ℝ]) (h : Module.finrank ℝ ↥L = 2) : L ≠ ⊥ := by
  rintro rfl
  rw [Subalgebra.finrank_bot] at h
  omega

end Examples

end TauCeti
