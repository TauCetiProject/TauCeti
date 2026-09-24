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
  number `vol / covolume * c ^ [K:ℚ]` up to `O(c ^ ([K:ℚ] - 1))`, uniformly in the coset;
* `TauCeti.GlobalNumberFields.exists_abs_ncard_rayFundamentalDomain_inter_norm_le_inter_vadd_sub_le`
  — the same count graded by the norm: the main term is linear in `t` and the error is
  `O(t ^ (1 - 1 / [K:ℚ]))`.

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

open scoped Classical in
/-- **The congruence-lattice count graded by the norm, uniformly in the coset.**  For any coset
`ξ +ᵥ congruenceLattice 𝔪 I`, the number of its points in the ray fundamental domain of norm at
most `t` is `vol / covolume * t`, with an error `O(t ^ (1 - 1 / [K:ℚ]))` whose implied constant is
independent of both `t` and the coset.

This is the previous estimate regraded from dilations to norms: the main term is linear in `t`,
and the boundary exponent `[K:ℚ] - 1` becomes the power saving `1 / [K:ℚ]`.  Unlike
`ZLattice.covolume.tendsto_card_le_div'`, which gives a limit, it provides an explicit error
term, uniform in the coset. -/
theorem exists_abs_ncard_rayFundamentalDomain_inter_norm_le_inter_vadd_sub_le (𝔪 : Modulus K)
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : ∃ A ≥ (0 : ℝ), ∀ (ξ : mixedSpace K) (t : ℝ), 1 ≤ t →
      |(((rayFundamentalDomain 𝔪 ∩ {x : mixedSpace K | mixedEmbedding.norm x ≤ t}) ∩
            (ξ +ᵥ (congruenceLattice 𝔪 I : Set (mixedSpace K)))).ncard : ℝ) -
          volume.real (rayFundamentalDomain 𝔪 ∩ {x : mixedSpace K | mixedEmbedding.norm x ≤ 1}) /
            ZLattice.covolume (congruenceLattice 𝔪 I) volume * t| ≤
        A * t ^ (1 - ((finrank ℚ K : ℝ))⁻¹) := by
  obtain ⟨A, hA0, hA⟩ := exists_abs_ncard_smul_rayFundamentalDomain_inter_vadd_sub_le 𝔪 I
  simp only [mixedEmbedding.finrank] at hA
  refine ⟨A, hA0, fun ξ t ht ↦ ?_⟩
  have ht0 : (0 : ℝ) < t := lt_of_lt_of_le one_pos ht
  have hn : 0 < finrank ℚ K := finrank_pos
  have hc1 : 1 ≤ t ^ ((finrank ℚ K : ℝ))⁻¹ := Real.one_le_rpow ht (by positivity)
  have hc0 : (0 : ℝ) < t ^ ((finrank ℚ K : ℝ))⁻¹ := lt_of_lt_of_le one_pos hc1
  have hcn : (t ^ ((finrank ℚ K : ℝ))⁻¹) ^ finrank ℚ K = t :=
    Real.rpow_inv_natCast_pow ht0.le hn.ne'
  have herr : (t ^ ((finrank ℚ K : ℝ))⁻¹) ^ (finrank ℚ K - 1) =
      t ^ (1 - ((finrank ℚ K : ℝ))⁻¹) := by
    -- the two semantic steps: a natural power of an `rpow` is an `rpow`, and `rpow` exponents
    -- multiply; what remains is arithmetic in the exponent
    rw [← Real.rpow_natCast (t ^ ((finrank ℚ K : ℝ))⁻¹) (finrank ℚ K - 1), ← Real.rpow_mul ht0.le]
    congr 1
    have hn0 : (finrank ℚ K : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
    push_cast [Nat.cast_sub hn]
    field_simp
  -- dilating by `c` scales the norm by `c ^ [K:ℚ]`, so `c = t ^ (1 / [K:ℚ])` is the factor that
  -- presents the norm-≤-`t` section as a dilate of the norm-≤-one section
  have key := hA ξ (t ^ ((finrank ℚ K : ℝ))⁻¹) hc1
  rwa [smul_rayFundamentalDomain_inter_normLeOne 𝔪 hc0, hcn, herr] at key

end TauCeti.GlobalNumberFields
