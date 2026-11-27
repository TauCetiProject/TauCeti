/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import TauCeti.Topology.Algebra.Module.Equiv.SMul
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

/-- The domain of a frame centred at an interior point is the open disc. -/
theorem mem_halfTwistDomain_of_norm_lt_one {i z : 𝕔𝔻} (hi : ‖(i : ℂ)‖ < 1) :
    z ∈ halfTwistDomain i ↔ ‖(z : ℂ)‖ < 1 := by
  simp only [halfTwistDomain, hi, ↓reduceIte, mem_ofPred_eq]

/-- The domain of a frame centred at a point of the circle is the half-disc `re (z / i) > 0`. -/
theorem mem_halfTwistDomain_of_norm_eq_one {i z : 𝕔𝔻} (hi : ‖(i : ℂ)‖ = 1) :
    z ∈ halfTwistDomain i ↔ 0 < ((z : ℂ) / i).re := by
  simp only [halfTwistDomain, hi.not_lt, ↓reduceIte, mem_ofPred_eq]

/-- A frame centred at an interior point is `1`. -/
@[simp] theorem halfTwistExponent_of_norm_lt_one (k : ℤ) {i : 𝕔𝔻} (hi : ‖(i : ℂ)‖ < 1) (z : 𝕔𝔻) :
    halfTwistExponent k i z = 0 := by
  simp only [halfTwistExponent, hi, ↓reduceIte]

/-- A frame centred at a point `i` of the circle is `exp ((k / 2) (log i + log (z / i)))`. -/
theorem halfTwistExponent_of_norm_eq_one (k : ℤ) {i : 𝕔𝔻} (hi : ‖(i : ℂ)‖ = 1) (z : 𝕔𝔻) :
    halfTwistExponent k i z = (k / 2 : ℂ) * (log i + log ((z : ℂ) / i)) := by
  simp only [halfTwistExponent, hi.not_lt, ↓reduceIte]

/-- The domains of the half-twisted frames are open. -/
theorem isOpen_halfTwistDomain (i : 𝕔𝔻) : IsOpen (halfTwistDomain i) := by
  rw [halfTwistDomain]
  split_ifs
  · exact isOpen_lt (continuous_norm.comp continuous_coe) continuous_const
  · exact isOpen_lt continuous_const (continuous_re.comp (continuous_coe.div_const _))

/-- Each half-twisted frame is defined at its centre. -/
theorem mem_halfTwistDomain_self (i : 𝕔𝔻) : i ∈ halfTwistDomain i := by
  rcases (norm_le_one i).lt_or_eq with hi | hi
  · exact (mem_halfTwistDomain_of_norm_lt_one hi).2 hi
  · simp [mem_halfTwistDomain_of_norm_eq_one hi,
      div_self (ne_zero_of_norm_ne_zero (hi ▸ one_ne_zero))]

/-- The logarithm of each half-twisted frame is continuous on its domain: on the half-disc
`re (z / i) > 0` the quotient `z / i` stays in the slit plane of the principal logarithm. -/
theorem continuousOn_halfTwistExponent (k : ℤ) (i : 𝕔𝔻) :
    ContinuousOn (halfTwistExponent k i) (halfTwistDomain i) := by
  rcases (norm_le_one i).lt_or_eq with hi | hi
  · exact continuousOn_const.congr fun z _ ↦ halfTwistExponent_of_norm_lt_one k hi z
  · have h : ContinuousOn (fun z : 𝕔𝔻 ↦ log ((z : ℂ) / i)) (halfTwistDomain i) :=
      fun z hz ↦ (continuousAt_clog (Or.inl ((mem_halfTwistDomain_of_norm_eq_one hi).1 hz)))
        |>.comp_continuousWithinAt (f := fun w : 𝕔𝔻 ↦ (w : ℂ) / i)
          (continuous_coe.div_const _).continuousWithinAt
    exact (continuousOn_const.mul (continuousOn_const.add h)).congr fun z _ ↦
      halfTwistExponent_of_norm_eq_one k hi z

/-- Away from `0`, the square of a frame centred on the circle is `z ^ k`. -/
theorem sq_exp_halfTwistExponent (k : ℤ) {i z : 𝕔𝔻} (hi : ‖(i : ℂ)‖ = 1) (hz : (z : ℂ) ≠ 0) :
    exp (halfTwistExponent k i z) ^ 2 = (z : ℂ) ^ k := by
  have hi0 := ne_zero_of_norm_ne_zero (hi ▸ one_ne_zero)
  -- The two logarithms add up to a logarithm of `z`.
  have hlog : exp (log i + log ((z : ℂ) / i)) = z := by
    rw [exp_add, exp_log hi0, exp_log (div_ne_zero hz hi0), mul_div_cancel₀ _ hi0]
  have h2 : (2 : ℂ) * halfTwistExponent k i z = k * (log i + log ((z : ℂ) / i)) := by
    rw [halfTwistExponent_of_norm_eq_one k hi]
    ring
  rw [← exp_natCast_mul, Nat.cast_ofNat, h2, exp_intCast_mul, hlog]

/-- At the centre of a frame centred on the circle, the frame is the principal power
`i ^ (k / 2)`. -/
theorem exp_halfTwistExponent_self (k : ℤ) {i : 𝕔𝔻} (hi : ‖(i : ℂ)‖ = 1) :
    exp (halfTwistExponent k i i) = (i : ℂ) ^ ((k : ℂ) / 2) := by
  have hi0 : (i : ℂ) ≠ 0 := ne_zero_of_norm_ne_zero (hi ▸ one_ne_zero)
  rw [halfTwistExponent_of_norm_eq_one k hi, div_self hi0, log_one, add_zero,
    cpow_def_of_ne_zero hi0, mul_comm]

/-- The half-twisted frames: multiplication by `exp (halfTwistExponent k i z)`, which is `1` at an
interior centre `i` and `i^{k/2} (z / i)^{k/2}` at a centre `i` on the circle. -/
def halfTwistFrames (k : ℤ) : LocalFrames ℂ 𝕔𝔻 1 where
  domain := halfTwistDomain
  isOpen_domain := isOpen_halfTwistDomain
  mem_domain_self := mem_halfTwistDomain_self
  frame i z := ContinuousLinearEquiv.smulLeft (Units.mk0 _ (exp_ne_zero (halfTwistExponent k i z)))
  continuous_frame i := by
    have h : (fun z : halfTwistDomain i ↦ ((ContinuousLinearEquiv.smulLeft
        (Units.mk0 _ (exp_ne_zero (halfTwistExponent k i z))) : (Fin 1 → ℂ) ≃L[ℂ] (Fin 1 → ℂ)) :
          (Fin 1 → ℂ) →L[ℂ] (Fin 1 → ℂ))) =
        fun z : halfTwistDomain i ↦
          exp (halfTwistExponent k i z) • ContinuousLinearMap.id ℂ (Fin 1 → ℂ) :=
      funext fun _ ↦ (ContinuousLinearEquiv.coe_smulLeft _).trans (Units.smul_def _ _)
    rw [h]
    exact (continuous_exp.comp ((continuousOn_iff_continuous_domRestrict.1
      (continuousOn_halfTwistExponent k i)))).smul continuous_const

/-- The domains of the half-twisted frames. -/
@[simp] theorem halfTwistFrames_domain (k : ℤ) : (halfTwistFrames k).domain = halfTwistDomain :=
  (rfl)

/-- The half-twisted frame at `i` over `z` is multiplication by `exp (halfTwistExponent k i z)`. -/
theorem coe_halfTwistFrames_frame (k : ℤ) (i : 𝕔𝔻) (z : (halfTwistFrames k).domain i) :
    ((halfTwistFrames k).frame i z : (Fin 1 → ℂ) →L[ℂ] (Fin 1 → ℂ)) =
      exp (halfTwistExponent k i z) • ContinuousLinearMap.id ℂ (Fin 1 → ℂ) := by
  rw [← Units.val_mk0 (exp_ne_zero (halfTwistExponent k i z)), ← Units.smul_def]
  exact ContinuousLinearEquiv.coe_smulLeft _

/-- The inverse of the half-twisted frame at `i` over `z` is multiplication by
`exp (halfTwistExponent k i z)⁻¹`. -/
theorem coe_halfTwistFrames_frame_symm (k : ℤ) (i : 𝕔𝔻) (z : (halfTwistFrames k).domain i) :
    (((halfTwistFrames k).frame i z).symm : (Fin 1 → ℂ) →L[ℂ] (Fin 1 → ℂ)) =
      (exp (halfTwistExponent k i z))⁻¹ • ContinuousLinearMap.id ℂ (Fin 1 → ℂ) := by
  rw [← Units.val_mk0 (exp_ne_zero (halfTwistExponent k i z)), ← Units.val_inv_eq_inv_val,
    ← Units.smul_def]
  exact ContinuousLinearEquiv.coe_smulLeft_symm _

/-- The half-twisted frame at `i` over `z` applied to a vector. -/
@[simp] theorem halfTwistFrames_frame_apply (k : ℤ) (i : 𝕔𝔻) (z : (halfTwistFrames k).domain i)
    (v : Fin 1 → ℂ) : (halfTwistFrames k).frame i z v = exp (halfTwistExponent k i z) • v := by
  rw [← ContinuousLinearEquiv.coe_coe, coe_halfTwistFrames_frame, _root_.smul_apply,
    ContinuousLinearMap.id_apply]

/-- The inverse of the half-twisted frame at `i` over `z` applied to a vector. -/
@[simp] theorem halfTwistFrames_frame_symm_apply (k : ℤ) (i : 𝕔𝔻)
    (z : (halfTwistFrames k).domain i) (v : Fin 1 → ℂ) :
    ((halfTwistFrames k).frame i z).symm v = (exp (halfTwistExponent k i z))⁻¹ • v := by
  rw [← ContinuousLinearEquiv.coe_coe, coe_halfTwistFrames_frame_symm, _root_.smul_apply,
    ContinuousLinearMap.id_apply]

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
  have hc {l : 𝕔𝔻} (hl : a ∈ halfTwistDomain l) : ‖(l : ℂ)‖ = 1 :=
    (norm_le_one l).eq_of_not_lt fun h ↦
      (ne_of_lt ((mem_halfTwistDomain_of_norm_lt_one h).1 hl)) ha1
  set c := (exp (halfTwistExponent k j a))⁻¹ * exp (halfTwistExponent k i a)
  have hsq : c * c = 1 := by
    have ha0 : (a : ℂ) ≠ 0 := ne_zero_of_norm_ne_zero (ha1 ▸ one_ne_zero)
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

/-- The isomorphism of the half-twisted core with the trivial line core is multiplication by the
frame `exp (halfTwistExponent k z z)` over `z`. -/
theorem fiberMap_halfTwistIso_hom (k : ℤ) (z : 𝕔𝔻) :
    (halfTwistIso k).hom.fiberMap z =
      exp (halfTwistExponent k z z) • ContinuousLinearMap.id ℂ (Fin 1 → ℂ) := by
  rw [halfTwistIso, LocalFrames.isoTrivial_hom]
  exact ((halfTwistFrames k).fiberMap_toTrivial z).trans (coe_halfTwistFrames_frame k z _)

/-- The inverse isomorphism is multiplication by the inverse frame over `z`. -/
theorem fiberMap_halfTwistIso_inv (k : ℤ) (z : 𝕔𝔻) :
    (halfTwistIso k).inv.fiberMap z =
      (exp (halfTwistExponent k z z))⁻¹ • ContinuousLinearMap.id ℂ (Fin 1 → ℂ) := by
  rw [halfTwistIso, LocalFrames.isoTrivial_inv]
  exact ((halfTwistFrames k).fiberMap_ofTrivial z).trans (coe_halfTwistFrames_frame_symm k z _)

/-- Over an interior point the isomorphism of the half-twisted core with the trivial line core is
the identity. -/
theorem fiberMap_halfTwistIso_hom_of_norm_lt_one (k : ℤ) {z : 𝕔𝔻} (hz : ‖(z : ℂ)‖ < 1) :
    (halfTwistIso k).hom.fiberMap z = ContinuousLinearMap.id ℂ (Fin 1 → ℂ) := by
  rw [fiberMap_halfTwistIso_hom, halfTwistExponent_of_norm_lt_one k hz, exp_zero, one_smul]

/-- Over a point `z` of the circle, the isomorphism of the half-twisted core with the trivial line
core is multiplication by `z ^ (k / 2)`. So it carries the real line of the core onto
`z^{k/2} ℝ`. -/
theorem fiberMap_halfTwistIso_hom_of_norm_eq_one (k : ℤ) {z : 𝕔𝔻} (hz : ‖(z : ℂ)‖ = 1) :
    (halfTwistIso k).hom.fiberMap z =
      (z : ℂ) ^ ((k : ℂ) / 2) • ContinuousLinearMap.id ℂ (Fin 1 → ℂ) := by
  rw [fiberMap_halfTwistIso_hom, exp_halfTwistExponent_self k hz]

/-- **The trivial half-twist has Maslov index zero**: for `k = 0` the half-twisted pair is
isomorphic to the trivial pair `(ℂ, ℝ)`, by the identity over the circle. -/
theorem maslovIndex_halfTwistCore_zero :
    (halfTwistCore 0).maslovIndex (isRealAlong_halfTwistCore 0) = 0 := by
  rw [maslovIndex_eq_of_iso _ (isRealAlong_trivial 1 A) (halfTwistIso 0) fun a ha v ↦ by
    rw [fiberMap_halfTwistIso_hom_of_norm_eq_one 0 (notMem_borderedInterior_iff.1 ha)]
    simp only [Int.cast_zero, zero_div, cpow_zero, one_smul]
    have h (w : Fin 1 → ℂ) : ContinuousLinearMap.id ℂ (Fin 1 → ℂ) (star w) =
        star (ContinuousLinearMap.id ℂ (Fin 1 → ℂ) w) := by
      rw [ContinuousLinearMap.id_apply, ContinuousLinearMap.id_apply]
    -- The fibres of the half-twisted core are `Fin 1 → ℂ` (`rank_halfTwistCore`).
    exact h v]
  exact maslovIndex_trivial 1

end Complex.UnitClosedDisc
