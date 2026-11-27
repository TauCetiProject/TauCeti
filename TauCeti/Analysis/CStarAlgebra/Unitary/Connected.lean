/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Unitary.Connected
public import Mathlib.Topology.Algebra.Star.Unitary
import TauCeti.Analysis.RCLike.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.RealImaginaryPart
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Topology.Separation.Connected

/-!
# Unitary paths from spectral cuts

A unitary with nonnegative real part, and any self-adjoint unitary, is joined to the identity
(`Unitary.joined_one_of_nonneg_realPart`, `Unitary.joined_one_of_isSelfAdjoint`). These
continuous-functional-calculus paths supply the two factors of the reflection argument for
Hilbert-space unitaries. They do not assert connectedness of the unitary group of a general
C⋆-algebra. Their proofs are adapted from
[AtiyahSinger/Analysis/FredholmPaths.lean][fredholm-paths] in Lean-Atiyah-Singer, and supply the
source formalization's supplementary reflection argument for the invertible path connectedness
used in *Spin Geometry*, III §7, Lemma 7.7, p. 203.

Separately, multiplying a unitary by a unimodular scalar other than `-1` stays in its path
component (`Unitary.joined_smul`). Hence a unitary whose spectrum misses a point `z` of the unit
circle is joined to the identity (`Unitary.joined_one_of_notMem_spectrum`): rotating, `-1` is not
in the spectrum of `-z⋆ u`, so `‖-z⋆ u - 1‖ < 2` and Mathlib's exponential path
`Unitary.joined` joins `-z⋆ u` to `1`, while scalar rotations join `u` to `-z⋆ u`. In particular
every unitary with finite spectrum is joined to the identity
(`Unitary.joined_one_of_finite_spectrum`). This scalar-rotation argument is the
path-connectedness step behind the vanishing of `K₁` for finite-dimensional C⋆-algebras
(Blackadar, §8.1).

## References

* H. B. Lawson, Jr., and M.-L. Michelsohn, *Spin Geometry*, Princeton Mathematical Series 38,
  Princeton University Press, 1989, Chapter III, §7, Lemma 7.7, p. 203,
  [DOI](https://doi.org/10.1515/9781400883912).
* B. Blackadar, *K-Theory for Operator Algebras*, 2nd ed., Cambridge University Press (1998),
  §8.1.

[fredholm-paths]: https://github.com/alpha-squared-labs/Lean-Atiyah-Singer/blob/09fc7bab3f9ff606901bde4b5a5580470da63a70/AtiyahSinger/Analysis/FredholmPaths.lean
-/

public section

open Complex
open scoped ComplexOrder ComplexStarModule

/-- A unitary with nonnegative real part lies in the path component of the identity. -/
theorem Unitary.joined_one_of_nonneg_realPart
    {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (u : unitary A) (hu : 0 ≤ (ℜ (u : A) : A)) :
    Joined (1 : unitary A) u := by
  -- Positivity of the real part excludes the branch cut at -1.
  have hgap : -(1 : ℂ) ∉ spectrum ℂ (u : A) := by
    intro h
    have hmem : (-1 : ℝ) ∈ spectrum ℝ (ℜ (u : A) : A) := by
      rw [spectrum_realPart' (u : A) (by infer_instance)]
      exact ⟨-1, h, by simp⟩
    have hnonneg := spectrum_nonneg_of_nonneg hu hmem
    norm_num at hnonneg
  exact Unitary.joined 1 u ((Unitary.norm_sub_one_lt_two_iff u.property).mpr hgap)

/-- A self-adjoint unitary lies in the path component of the identity over the complex field. -/
theorem Unitary.joined_one_of_isSelfAdjoint
    {A : Type*} [CStarAlgebra A]
    (u : unitary A) (hu : IsSelfAdjoint (u : A)) : Joined (1 : unitary A) u := by
  let : PartialOrder A := CStarAlgebra.spectralOrder _
  let : StarOrderedRing A := CStarAlgebra.spectralOrderedRing _
  -- Multiplication by i moves the spectrum {1,-1} away from the logarithm's cut.
  let w : unitary A := ⟨Complex.I • (1 : A), by
    constructor <;> simp [star_smul, smul_smul]⟩
  have hw : Joined (1 : unitary A) w := by
    apply Unitary.joined_one_of_nonneg_realPart
    dsimp only [w, Subtype.coe_mk]
    rw [realPart_apply_coe]
    simp [star_smul]
  have hwu : Joined (1 : unitary A) (w * u) := by
    apply Unitary.joined_one_of_nonneg_realPart
    simp only [Submonoid.coe_mul]
    dsimp only [w, Subtype.coe_mk]
    rw [realPart_apply_coe]
    simp [star_smul, hu.star_eq]
  simpa using hw.inv.mul hwu


section Spectrum

variable {A : Type*} [CStarAlgebra A]

/-- Multiplying a unitary by a unimodular scalar `w ≠ -1` stays in its path component. -/
theorem Unitary.joined_smul (v : unitary A) {w : ℂ} (hw : w ∈ unitary ℂ) (hw₁ : w ≠ -1) :
    Joined v ⟨w • (v : A), Unitary.smul_mem_of_mem hw v.prop⟩ := by
  refine Unitary.joined _ _ ?_
  have h : ‖w - 1‖ < 2 := by
    rw [Unitary.norm_sub_one_lt_two_iff hw]
    have : spectrum ℂ w = {w} := by simpa using spectrum.scalar_eq (A := ℂ) w
    rw [this, Set.mem_singleton_iff]
    exact hw₁.symm
  have hv : ‖(v : A)‖ ≤ 1 := by
    rcases subsingleton_or_nontrivial A with _ | _
    · simp [Subsingleton.elim (v : A) 0]
    · exact (CStarRing.norm_coe_unitary v).le
  calc ‖w • (v : A) - v‖ = ‖(w - 1) • (v : A)‖ := by rw [sub_smul, one_smul]
    _ ≤ ‖w - 1‖ * ‖(v : A)‖ := norm_smul_le _ _
    _ ≤ ‖w - 1‖ * 1 := by gcongr
    _ < 2 := by rwa [mul_one]

/-- **Unitaries whose spectrum misses a point of the circle are joined to `1`.** If `z` is a
unitary scalar and `z ∉ σ(u)`, then `u` lies in the path component of the identity. -/
theorem Unitary.joined_one_of_notMem_spectrum (u : unitary A) {z : ℂ} (hz : z ∈ unitary ℂ)
    (hzu : z ∉ spectrum ℂ (u : A)) : Joined 1 u := by
  set c : ℂ := -star z
  have hc : c ∈ unitary ℂ := TauCeti.RCLike.mem_unitary_iff_norm_eq_one.2 (by
    rw [norm_neg, norm_star, TauCeti.RCLike.mem_unitary_iff_norm_eq_one.1 hz])
  have hcz : star c * c = 1 := Unitary.star_mul_self_of_mem hc
  set v : unitary A := ⟨c • (u : A), Unitary.smul_mem_of_mem hc u.prop⟩
  -- `-1 ∉ σ(c u) = c σ(u)`, since `-1 = c w` forces `w = z`.
  have hv : Joined 1 v := by
    refine Unitary.joined _ _ ?_
    rw [OneMemClass.coe_one, Unitary.norm_sub_one_lt_two_iff v.prop]
    have hc₀ : c ≠ 0 := by rintro h; simp [h] at hcz
    rw [show (v : A) = (Units.mk0 c hc₀ : ℂˣ) • (u : A) by rw [Units.smul_mk0],
      spectrum.unit_smul_eq_smul]
    rintro ⟨w, hw, hcw⟩
    refine hzu ?_
    have hzz : star z * z = 1 := Unitary.star_mul_self_of_mem hz
    have : w = z := by
      simp only [Units.val_mk0, smul_eq_mul, c] at hcw
      linear_combination (-w) * hzz - z * hcw
    exact this ▸ hw
  -- `u = c⋆ v`, reached from `v` by one or two scalar rotations.
  have hu : (u : A) = star c • (v : A) := by
    simp only [v, smul_smul, hcz, one_smul]
  refine hv.trans ?_
  by_cases hc₁ : star c = -1
  · have hI : Complex.I ∈ unitary ℂ := TauCeti.RCLike.mem_unitary_iff_norm_eq_one.2 (by simp)
    refine (Unitary.joined_smul v hI (by simp [Complex.ext_iff])).trans ?_
    convert Unitary.joined_smul _ hI (by simp [Complex.ext_iff]) using 1
    ext
    simp only [hu, hc₁, smul_smul, Complex.I_mul_I]
  · convert Unitary.joined_smul v (Unitary.star_mem hc) hc₁ using 1
    exact Subtype.ext hu

/-- A unitary with finite spectrum is joined to `1` by a path of unitaries. -/
theorem Unitary.joined_one_of_finite_spectrum (u : unitary A)
    (h : (spectrum ℂ (u : A)).Finite) : Joined 1 u := by
  have hinf : (Metric.sphere (0 : ℂ) 1).Infinite :=
    IsPreconnected.infinite_of_nontrivial (isConnected_sphere (E := ℂ)
      (by rw [Complex.rank_real_complex]; norm_num) 0 zero_le_one).isPreconnected
      ⟨1, by simp, -1, by simp, by norm_num⟩
  obtain ⟨z, hz, hzu⟩ := hinf.exists_notMem_finite h
  exact Unitary.joined_one_of_notMem_spectrum u
    (TauCeti.RCLike.mem_unitary_iff_norm_eq_one.2 (by simpa using hz)) hzu

end Spectrum
