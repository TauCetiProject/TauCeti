/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.FiniteAdeleRing
public import TauCeti.NumberTheory.NumberField.CanonicalEmbedding.MixedImage
public import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.TorsionClass

/-!
# The lattice `Eⁿ ∩ x Ôⁿ` of an adelic matrix

Let `E` be a number field, `𝔸_f` its finite adeles, `Ô` the integral ones and `n` a finite type.
For `x ∈ GL_n(𝔸_f)` the `𝓞 E`-module `Eⁿ ∩ x Ôⁿ`
(`Matrix.GeneralLinearGroup.frameLattice`) is finitely generated and spans `Eⁿ`, so its
image in `(E ⊗ ℝ)ⁿ`, the coordinatewise mixed embedding `Submodule.mixedImage`, is discrete and a
full lattice. Finite generation comes from a common denominator: if `d ≠ 0` in `𝓞 E` makes
`d · x` integral, the module lies in `d⁻¹ 𝓞_Eⁿ`, whose mixed image is discrete because `𝓞 E` is
discrete in `E ⊗ ℝ`. The matrix `x` itself does not act on `(E ⊗ ℝ)ⁿ`.

## Main results

* `Matrix.GeneralLinearGroup.isZLattice_mixedImage_frameLattice`: the image of `Eⁿ ∩ x Ôⁿ` in
  `(E ⊗ ℝ)ⁿ` is a full lattice.

## References

* the folder `grh` of https://github.com/lsernau/grh-lean at commit
  72fead102f663d5c7a407964a13dc0cf9d977207, file `Lib/Shimura/Uniformisation/AdelicFrames`.
-/

public section
noncomputable section

open scoped NumberField NumberField.AdeleRing

namespace Matrix.GeneralLinearGroup

variable {E : Type*} [Field E] [NumberField E] {n : Type*} [Fintype n] [DecidableEq n]

open scoped Classical in
/-- **The image of `Eⁿ ∩ x Ôⁿ` in `(E ⊗ ℝ)ⁿ` is a full lattice** for every `x ∈ GL_n(𝔸_f)`: it is
discrete because the module is finitely generated, and spans because the module spans `Eⁿ`. -/
theorem isZLattice_mixedImage_frameLattice (x : GL n 𝔸ᶠ[E]) :
    IsZLattice ℝ x.frameLattice.mixedImage :=
  Submodule.isZLattice_mixedImage x.span_frameLattice_eq_top

end Matrix.GeneralLinearGroup
