/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Fuchsian.Covolume
public import TauCeti.NumberTheory.Modular

/-!
# The level-one modular group as a cofinite Fuchsian group

The effective group acting on the upper half-plane at level one is the image of
`PSL(2, ℤ)` in `PSL(2, ℝ)`, not `SL(2, ℤ)`: the latter still contains the central matrix
`-I`, which acts trivially. This file proves that the projective image is a discrete cofinite
subgroup of `PSL(2, ℝ)`.

The standard open modular fundamental domain is transported from the `PSL(2, ℤ)` action to
its image in `PSL(2, ℝ)`. Its finite hyperbolic area then proves cofiniteness. This supplies the
effective level-one input for quotient and compactification constructions.

## Main results

* `TauCeti.ModularGroup.isFundamentalDomain_fdo_psl2zToPSL2RRange`: the standard open modular
  domain is a fundamental domain for the projective image in `PSL(2, ℝ)`.
* `TauCeti.ModularGroup.isCofinite_psl2zToPSL2RRange`: that image is a cofinite Fuchsian group.

## References

* Fred Diamond and Jerry Shurman, *A First Course in Modular Forms*, Graduate Texts in
  Mathematics 228, Springer, 2005, §§2.3–2.4.
* Jean-Pierre Serre, *A Course in Arithmetic*, Graduate Texts in Mathematics 7, Springer,
  1973, Chapter VII.
-/

public section

noncomputable section

open MeasureTheory UpperHalfPlane

open scoped MatrixGroups

namespace TauCeti.ModularGroup

/-- The standard open modular domain is a fundamental domain for the image of `PSL(2, ℤ)` in
`PSL(2, ℝ)`. It presents the effective level-one quotient and supplies the finite-area domain
used to prove that the projective image is cofinite. -/
theorem isFundamentalDomain_fdo_psl2zToPSL2RRange :
    IsFundamentalDomain psl2zToPSL2R.range (_root_.ModularGroup.fdo : Set ℍ) volume := by
  simpa only [Set.preimage_id] using
    _root_.ModularGroup.isFundamentalDomain_fdo.preimage_of_equiv
      (Measure.QuasiMeasurePreserving.id volume)
      (MonoidHom.ofInjective psl2zToPSL2R_injective).bijective
      fun g τ ↦ by
        simp only [id_eq, MonoidHom.ofInjective_apply, Subgroup.smul_def,
          UpperHalfPlane.psl2zToPSL2R_smul]

/-- The image of `PSL(2, ℤ)` in `PSL(2, ℝ)` is a cofinite Fuchsian group. -/
theorem isCofinite_psl2zToPSL2RRange : psl2zToPSL2R.range.IsCofinite := by
  apply isFundamentalDomain_fdo_psl2zToPSL2RRange.isCofinite_of_volume_ne_top
  exact ne_of_lt <| by
    rw [← measure_congr _root_.ModularGroup.fd_ae_eq_fdo]
    exact _root_.ModularGroup.volume_fd_lt_top

end TauCeti.ModularGroup
