/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.GeometryOfNumbers.LatticePointCount
public import TauCeti.NumberTheory.NumberField.Global.Counting.CongruenceLattice
public import TauCeti.NumberTheory.NumberField.Global.Counting.RayFundamentalDomain.Lipschitz

/-!
# Counting congruence-lattice points in the ray fundamental domain

Let `𝔪` be a modulus of a number field `K` and `I` an invertible fractional ideal.  This file
counts the points of a coset of `congruenceLattice 𝔪 I` inside the dilates of the norm-≤-one
section of `rayFundamentalDomain 𝔪`, with a power-saving error and — the point — with an implied
constant that does not depend on the coset.

Nothing here is new geometry.  The lattice-point count with a power-saving error takes a bounded
region whose frontier is Lipschitz parametrizable in codimension one, and the norm-≤-one section
of the ray fundamental domain has been shown to be exactly that; the congruence lattice has been
shown to be a full `ℤ`-lattice in the mixed space.  This file is the instantiation, and it exists
because the three inputs live in three different developments and the fit between them is the
step that a count of ideals in a fixed ray class actually consumes.

The count is stated for an arbitrary translate `ξ` rather than for the lattice itself because a
fixed ray class corresponds to one coset of the congruence lattice, so every class needs its own
instance of the estimate.  What the statement provides is a single `A` valid for *every* translate
at once, which is the form the class-by-class count consumes directly.

## Main results

* `TauCeti.GlobalNumberFields.exists_abs_ncard_smul_rayFundamentalDomain_inter_vadd_sub_le`: the
  points of any coset of `congruenceLattice 𝔪 I` in the dilate `c •` of the norm-≤-one section
  number `vol / covolume * c ^ [K:ℚ]` up to `O(c ^ ([K:ℚ] - 1))`, uniformly in the coset.

## References

* S. Lang, *Algebraic Number Theory*, Chapter VI, §2.
-/

public section

open Bornology MeasureTheory Module NumberField NumberField.mixedEmbedding
open scoped Pointwise nonZeroDivisors

namespace TauCeti.GlobalNumberFields

variable {K : Type*} [Field K] [NumberField K]

open scoped Classical in
/-- **The congruence-lattice count in the ray fundamental domain, uniformly in the coset.**  For
any coset `ξ +ᵥ congruenceLattice 𝔪 I`, the number of its points in the dilate
`c • (rayFundamentalDomain 𝔪 ∩ {norm ≤ 1})` is the volume ratio times `c ^ [K:ℚ]`, with an error
`O(c ^ ([K:ℚ] - 1))` whose implied constant is independent of both `c` and the coset.

The exponent is written `finrank ℝ (mixedSpace K)`, which is `[K:ℚ]` by
`NumberField.mixedEmbedding.finrank`; a consumer counting ideals by their absolute norm rewrites
along that equality. -/
theorem exists_abs_ncard_smul_rayFundamentalDomain_inter_vadd_sub_le (𝔪 : Modulus K)
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ∃ A ≥ (0 : ℝ), ∀ (ξ : mixedSpace K) (c : ℝ), 1 ≤ c →
      |(((c • (rayFundamentalDomain 𝔪 ∩ {x : mixedSpace K | mixedEmbedding.norm x ≤ 1})) ∩
            (ξ +ᵥ (congruenceLattice 𝔪 I : Set (mixedSpace K)))).ncard : ℝ) -
          volume.real (rayFundamentalDomain 𝔪 ∩ {x : mixedSpace K | mixedEmbedding.norm x ≤ 1}) /
            ZLattice.covolume (congruenceLattice 𝔪 I) volume *
              c ^ finrank ℝ (mixedSpace K)| ≤ A * c ^ (finrank ℝ (mixedSpace K) - 1) :=
  -- `.2.2` is the Lipschitz-frontier conjunct; the boundedness hypothesis is a separate lemma
  TauCeti.exists_abs_ncard_smul_inter_vadd_sub_le
    (isBounded_rayFundamentalDomain_inter_normLeOne 𝔪)
    (isLipschitzParametrizable_frontier_rayFundamentalDomain 𝔪).2.2

end TauCeti.GlobalNumberFields
