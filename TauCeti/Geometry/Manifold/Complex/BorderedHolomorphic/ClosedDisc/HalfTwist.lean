/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import TauCeti.Geometry.Manifold.Complex.BorderedHolomorphic.ClosedDisc
public import TauCeti.Geometry.Manifold.Complex.BorderedHolomorphic.DoubledBundle.MaslovIndex
public import TauCeti.Topology.VectorBundle.FiniteRank.LocalFrames

/-!
# The half-twisted bundle pairs over the closed disc

For an integer `k`, the bundle pair `(ℂ, e^{ikθ/2} ℝ)` over the closed unit disc `𝕔𝔻` is the
trivial line bundle `ℂ` with the real line `F_z = z^{k/2} ℝ` over each point `z` of the unit
circle. The line `z^{k/2} ℝ` is well defined although `z^{k/2}` is not: the two square roots of
`z^k` span the same real line. Going once around the circle, `F` turns by `k` half turns, so for odd
`k` it has no continuous nonvanishing section. These pairs are the normalization of the boundary
Maslov index, `μ(ℂ, e^{ikθ/2} ℝ) = k` (McDuff–Salamon, Theorem C.3.5).

The pair is presented by the local frames `halfTwistFrames k` of the trivial line bundle: at an
interior point the frame `1` on the open disc, and at a point `ζ` of the circle the frame
`z ↦ ζ^{k/2} (z / ζ)^{k/2}` (principal branches) on the half-disc `re (z / ζ) > 0`. The two frames
at a point `z` of the circle are square roots of `z^k`, so they differ by a sign
(`sq_exp_halfTwistExponent`), and the core `halfTwistCore k` of the trivial bundle read in these
frames is real along the circle (`isRealAlong_halfTwistCore`). Its isomorphism
`halfTwistIso k` with the trivial line core is multiplication by `z^{k/2}` over a point `z` of the
circle (`fiberMap_halfTwistIso_hom_of_norm_eq_one`), so it carries the real line of the core onto
`z^{k/2} ℝ`.

For `k = 0` this isomorphism is the identity over the circle, so the pair is isomorphic to the
trivial pair `(ℂ, ℝ)` and has Maslov index `0` (`maslovIndex_halfTwistCore_zero`).

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Theorem C.3.5 (normalization of the boundary Maslov index).
-/

public section

noncomputable section

open Set CategoryTheory TauCeti TauCeti.FiniteRankBundleCore
open scoped Manifold Complex.UnitDisc

namespace Complex.UnitClosedDisc

local notation "A" => (borderedInterior 𝕔𝔻 : Set 𝕔𝔻)ᶜ

/-- The domain of the half-twisted frame at `i`: the open disc for an interior point, and the
half-disc `re (z / i) > 0` for a point of the circle. -/
def halfTwistDomain (i : 𝕔𝔻) : Set 𝕔𝔻 :=
  if ‖(i : ℂ)‖ < 1 then {z | ‖(z : ℂ)‖ < 1} else {z | 0 < ((z : ℂ) / i).re}

/-- The logarithm of the half-twisted frame at `i`: `0` for an interior point, and
`(k / 2) (log i + log (z / i))` for a point of the circle. -/
def halfTwistExponent (k : ℤ) (i z : 𝕔𝔻) : ℂ :=
  if ‖(i : ℂ)‖ < 1 then 0 else (k / 2 : ℂ) * (log i + log ((z : ℂ) / i))

private theorem ne_zero_of_not_norm_lt_one {i : 𝕔𝔻} (hi : ¬‖(i : ℂ)‖ < 1) : (i : ℂ) ≠ 0 := by
  rintro h
  exact hi (by simp [h])

/-- The domains of the half-twisted frames are open. -/
theorem isOpen_halfTwistDomain (i : 𝕔𝔻) : IsOpen (halfTwistDomain i) := by
  rw [halfTwistDomain]
  split_ifs
  · exact isOpen_lt (continuous_norm.comp continuous_coe) continuous_const
  · exact isOpen_lt continuous_const (continuous_re.comp (continuous_coe.div_const _))

/-- Each half-twisted frame is defined at its centre. -/
theorem mem_halfTwistDomain_self (i : 𝕔𝔻) : i ∈ halfTwistDomain i := by
  rw [halfTwistDomain]
  split_ifs with hi
  · exact hi
  · simp [div_self (ne_zero_of_not_norm_lt_one hi)]

/-- The logarithm of each half-twisted frame is continuous on its domain: on the half-disc
`re (z / i) > 0` the quotient `z / i` stays in the slit plane of the principal logarithm. -/
theorem continuousOn_halfTwistExponent (k : ℤ) (i : 𝕔𝔻) :
    ContinuousOn (halfTwistExponent k i) (halfTwistDomain i) := by
  unfold halfTwistExponent halfTwistDomain
  split_ifs
  · exact continuousOn_const
  · have h : ContinuousOn (fun z : 𝕔𝔻 ↦ log ((z : ℂ) / i)) {z | 0 < ((z : ℂ) / i).re} :=
      fun z hz ↦ (continuousAt_clog (Or.inl hz)).comp_continuousWithinAt
        (f := fun w : 𝕔𝔻 ↦ (w : ℂ) / i) (continuous_coe.div_const _).continuousWithinAt
    exact continuousOn_const.mul (continuousOn_const.add h)

/-- Away from `0`, the square of a frame centred on the circle is `z ^ k`. -/
theorem sq_exp_halfTwistExponent (k : ℤ) {i z : 𝕔𝔻} (hi : ¬‖(i : ℂ)‖ < 1) (hz : (z : ℂ) ≠ 0) :
    exp (halfTwistExponent k i z) ^ 2 = (z : ℂ) ^ k := by
  have hi0 := ne_zero_of_not_norm_lt_one hi
  simp only [halfTwistExponent, hi, ↓reduceIte]
  rw [← exp_natCast_mul, Nat.cast_ofNat,
    show (2 : ℂ) * ((k / 2 : ℂ) * (log i + log ((z : ℂ) / i))) = k * (log i + log ((z : ℂ) / i))
      by ring, exp_intCast_mul, exp_add, exp_log hi0, exp_log (div_ne_zero hz hi0),
    mul_div_cancel₀ _ hi0]

/-- At the centre of a frame centred on the circle, the frame is the principal power
`i ^ (k / 2)`. -/
theorem exp_halfTwistExponent_self (k : ℤ) {i : 𝕔𝔻} (hi : ¬‖(i : ℂ)‖ < 1) :
    exp (halfTwistExponent k i i) = (i : ℂ) ^ ((k : ℂ) / 2) := by
  simp only [halfTwistExponent, hi, ↓reduceIte]
  rw [div_self (ne_zero_of_not_norm_lt_one hi), log_one, add_zero,
    cpow_def_of_ne_zero (ne_zero_of_not_norm_lt_one hi), mul_comm]

/-- The half-twisted frames: multiplication by `exp (halfTwistExponent k i z)`, which is `1` at an
interior centre `i` and `i^{k/2} (z / i)^{k/2}` at a centre `i` on the circle. -/
def halfTwistFrames (k : ℤ) : LocalFrames ℂ 𝕔𝔻 1 where
  domain := halfTwistDomain
  isOpen_domain := isOpen_halfTwistDomain
  mem_domain_self := mem_halfTwistDomain_self
  frame i z := ContinuousLinearEquiv.smulLeft (Units.mk0 _ (exp_ne_zero (halfTwistExponent k i z)))
  continuousOn_frame i := by
    have h : (fun z ↦ ((ContinuousLinearEquiv.smulLeft
        (Units.mk0 _ (exp_ne_zero (halfTwistExponent k i z))) : (Fin 1 → ℂ) ≃L[ℂ] (Fin 1 → ℂ)) :
          (Fin 1 → ℂ) →L[ℂ] (Fin 1 → ℂ))) =
        fun z ↦ exp (halfTwistExponent k i z) • ContinuousLinearMap.id ℂ (Fin 1 → ℂ) := by
      ext z v : 2
      simp [Units.smul_def]
    rw [h]
    exact (continuous_exp.comp_continuousOn (continuousOn_halfTwistExponent k i)).smul
      continuousOn_const

/-- The half-twisted frame at `i` over `z` is multiplication by `exp (halfTwistExponent k i z)`. -/
theorem halfTwistFrames_frame_apply (k : ℤ) (i z : 𝕔𝔻) (v : Fin 1 → ℂ) :
    (halfTwistFrames k).frame i z v = exp (halfTwistExponent k i z) • v := by
  simp [halfTwistFrames, Units.smul_def]

/-- The inverse of the half-twisted frame at `i` over `z` is multiplication by
`exp (halfTwistExponent k i z)⁻¹`. -/
theorem halfTwistFrames_frame_symm_apply (k : ℤ) (i z : 𝕔𝔻) (v : Fin 1 → ℂ) :
    ((halfTwistFrames k).frame i z).symm v = (exp (halfTwistExponent k i z))⁻¹ • v := by
  rw [ContinuousLinearEquiv.symm_apply_eq, halfTwistFrames_frame_apply, smul_inv_smul₀
    (exp_ne_zero _)]

/-- **The half-twisted bundle pair** `(ℂ, e^{ikθ/2} ℝ)` over the closed unit disc: the trivial line
bundle read in the frames `halfTwistFrames k`. -/
-- Expose the rank so that the fibres reduce to `Fin 1 → ℂ`.
@[expose]
def halfTwistCore (k : ℤ) : FiniteRankBundleCore ℂ 𝕔𝔻 :=
  (halfTwistFrames k).core

/-- The half-twisted core is a line bundle. -/
@[simp] theorem rank_halfTwistCore (k : ℤ) : (halfTwistCore k).rank = 1 := (rfl)

/-- The half-twisted core is real along the circle: over a point `z` of the circle, any two
half-twisted frames are square roots of `z ^ k`, so they differ by a sign. -/
theorem isRealAlong_halfTwistCore (k : ℤ) : (halfTwistCore k).IsRealAlong A := by
  refine (halfTwistFrames k).isRealAlong_core_iff.2 fun i j a ha hi hj v ↦ ?_
  have ha1 : ‖(a : ℂ)‖ = 1 := notMem_borderedInterior_iff.1 ha
  -- A point of the circle lies only in the domains of frames centred on the circle.
  have hc {l : 𝕔𝔻} (hl : a ∈ halfTwistDomain l) : ¬‖(l : ℂ)‖ < 1 := fun h ↦ by
    simp only [halfTwistDomain, h, ↓reduceIte, mem_ofPred_eq] at hl
    exact (ne_of_lt hl) ha1
  set c := (exp (halfTwistExponent k j a))⁻¹ * exp (halfTwistExponent k i a)
  have hsq : c * c = 1 := by
    have ha0 : (a : ℂ) ≠ 0 := fun h ↦ by simp [h] at ha1
    rw [show c * c = (exp (halfTwistExponent k j a) ^ 2)⁻¹ * exp (halfTwistExponent k i a) ^ 2 by
      ring, sq_exp_halfTwistExponent k (hc hi) ha0, sq_exp_halfTwistExponent k (hc hj) ha0,
      inv_mul_cancel₀ (zpow_ne_zero _ ha0)]
  have hstar : star c = c := by
    rcases mul_self_eq_one_iff.1 hsq with h | h <;> simp [h]
  simp only [halfTwistFrames_frame_apply, halfTwistFrames_frame_symm_apply, smul_smul]
  rw [star_smul, hstar]

/-- The half-twisted core is the trivial line core, by multiplication with the frame at each
point. -/
def halfTwistIso (k : ℤ) : halfTwistCore k ≅ trivial ℂ 𝕔𝔻 1 :=
  (halfTwistFrames k).isoTrivial

/-- Over a point `z` of the circle, the isomorphism of the half-twisted core with the trivial line
core is multiplication by `z ^ (k / 2)`. So it carries the real line of the core onto
`z^{k/2} ℝ`. -/
theorem fiberMap_halfTwistIso_hom_of_norm_eq_one (k : ℤ) {z : 𝕔𝔻} (hz : ‖(z : ℂ)‖ = 1) :
    (halfTwistIso k).hom.fiberMap z =
      (z : ℂ) ^ ((k : ℂ) / 2) • ContinuousLinearMap.id ℂ (Fin 1 → ℂ) := by
  ext v : 1
  -- The isomorphism is multiplication by the frame at `z` (`LocalFrames.isoTrivial`), and the
  -- frame at `z` over `z` is the principal power `z ^ (k / 2)`.
  rw [halfTwistIso, LocalFrames.isoTrivial_hom]
  refine (DFunLike.congr_fun ((halfTwistFrames k).fiberMap_toTrivial z) v).trans
    ((halfTwistFrames_frame_apply k z z v).trans ?_)
  rw [exp_halfTwistExponent_self k (hz.symm ▸ lt_irrefl 1)]
  -- Both sides are `z ^ (k / 2) • v`.
  rfl

/-- **The trivial half-twist has Maslov index zero**: for `k = 0` the half-twisted pair is
isomorphic to the trivial pair `(ℂ, ℝ)`, by the identity over the circle. -/
theorem maslovIndex_halfTwistCore_zero :
    (halfTwistCore 0).maslovIndex (isRealAlong_halfTwistCore 0) = 0 := by
  rw [maslovIndex_eq_of_iso _ (isRealAlong_trivial 1 A) (halfTwistIso 0) fun a ha v ↦ by
    rw [fiberMap_halfTwistIso_hom_of_norm_eq_one 0 (notMem_borderedInterior_iff.1 ha)]
    simp only [Int.cast_zero, zero_div, cpow_zero, one_smul]
    -- Both sides are `star v`.
    rfl]
  exact maslovIndex_trivial 1

end Complex.UnitClosedDisc
