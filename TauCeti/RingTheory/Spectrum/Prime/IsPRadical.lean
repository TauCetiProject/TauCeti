/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IsPerfectClosure
public import Mathlib.RingTheory.Spectrum.Prime.Homeomorph

/-!
# Prime spectra of `p`-radical ring maps

A ring map `i : K →+* L` is `p`-radical (Mathlib's `IsPRadical i p`) if some `p ^ n`-th power of
every element of `L` lies in the image of `K` and the kernel of `i` consists of `p`-nilpotent
elements. When `p ≠ 0`, `Spec L → Spec K` is a homeomorphism of prime spectra.

## Main results

* `IsPRadical.isHomeomorph_comap`: a `p`-radical ring map induces a homeomorphism of prime spectra.

## References

* B. Bhatt and P. Scholze, *Projectivity of the Witt vector affine Grassmannian*, Invent. Math.
  209 (2017), Section 3.
* The Stacks Project, [Tag 0BR8](https://stacks.math.columbia.edu/tag/0BR8), for the
  homeomorphism of spectra.
-/

public section

namespace IsPRadical

variable {K L : Type*} [CommRing K] [CommRing L] (i : K →+* L) (p : ℕ) [IsPRadical i p]

/-- **A `p`-radical ring map induces a homeomorphism of prime spectra.** -/
theorem isHomeomorph_comap [NeZero p] : IsHomeomorph (PrimeSpectrum.comap i) :=
  PrimeSpectrum.isHomeomorph_comap i
    (fun x ↦ let ⟨n, y, hy⟩ := IsPRadical.pow_mem i p x
      ⟨p ^ n, pow_pos (Nat.pos_of_neZero p) n, y, hy⟩)
    ((IsPRadical.ker_le i p).trans pNilradical_le_nilradical)

end IsPRadical
