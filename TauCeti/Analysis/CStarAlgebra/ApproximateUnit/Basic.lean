/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.ApproximateUnit
import Mathlib.Algebra.Order.Interval.Set.Group
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Mathlib.Analysis.Real.Sqrt
import TauCeti.Analysis.Normed.Ring.ApproximateUnit
import TauCeti.Analysis.Normed.Ring.Lipschitz
import TauCeti.Topology.MetricSpace.UniformConvergence

/-!
# Increasing approximate units: images and uniform convergence

A star-algebra homomorphism between C⋆-algebras is positive and contractive, so it maps the
positive part of the closed unit ball into itself. Hence the image of an increasing approximate
unit under a surjective homomorphism is an increasing approximate unit of the target,
`Filter.IsIncreasingApproximateUnit.map`. This transfers approximate-unit limits, such as the
norm of a positive functional, from a C⋆-algebra to its quotients.

Since an increasing approximate unit eventually lies in the closed unit ball, two-sided
compressions `e * a * e` converge to `a` (`Filter.IsIncreasingApproximateUnit.tendsto_mul_self`),
the convergence `e * a → a` is uniform for `a` in a compact set
(`Filter.IsIncreasingApproximateUnit.tendstoUniformlyOn_mul_right`), and so is the convergence
`a * e → a` (`Filter.IsIncreasingApproximateUnit.tendstoUniformlyOn_mul_left`). This controls
`e * α_r(b) → α_r(b)` uniformly along a compact set of group elements `r` for a continuous action
`α`, as needed for approximate units of twisted convolution algebras.

`TauCeti.CStarAlgebra.norm_mul_star_sub_star_sq_le` is the estimate for a positive contraction `e`
that drives the approximate-unit argument showing that closed two-sided ideals are self-adjoint and
that `x * e → x` along an increasing approximate unit of a closed `⋆`-subalgebra `B` containing
`star x * x` (`Filter.IsIncreasingApproximateUnit.tendsto_mul_star_of_star_mul_self_mem` and
`Filter.IsIncreasingApproximateUnit.tendsto_mul_of_star_mul_self_mem`):
`‖e * star a - star a‖ ^ 2 ≤ ‖star a * a - e * (star a * a)‖`. Its companions
`TauCeti.CStarAlgebra.norm_sub_mul_sq_le`, `‖a - a * e‖ ^ 2 ≤ ‖star a * a + z‖ + ‖z - z * e‖`, and
`TauCeti.CStarAlgebra.norm_sub_mul_le_of_star_mul_self_le`, `‖x - x * e‖ ≤ ‖y - y * e‖` whenever
`star x * x ≤ star y * y`, drive the quotient C⋆-identity and order-heredity arguments.

`TauCeti.CStarAlgebra.norm_sub_mul_sq_le_of_star_mul_self_le` compares an element `y` with a
dominating `b ≥ star y * y`: `‖y - y * e‖ ^ 2 ≤ 2 * ‖b - b * e‖` for a self-adjoint contraction
`e`. Hence a right approximate unit for `b` is one for `y`,
`TauCeti.CStarAlgebra.tendsto_mul_of_star_mul_self_le`. Every closed star subalgebra carries an
approximate unit of positive contractions, seen as a filter on the ambient algebra,
`NonUnitalStarSubalgebra.exists_approximateUnit`.
-/

public section

open Filter Topology
open scoped CStarAlgebra ComplexOrder

namespace Filter.IsIncreasingApproximateUnit

section Uniform

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A]

/-- Along an increasing approximate unit, two-sided compression `e * a * e` tends to `a`. -/
theorem tendsto_mul_self {l : Filter A} (hl : l.IsIncreasingApproximateUnit) (a : A) :
    Tendsto (fun e => e * a * e) l (𝓝 a) :=
  TauCeti.tendsto_mul_mul_of_isBoundedUnder ⟨1, eventually_map.mpr hl.eventually_norm⟩
    (hl.tendsto_mul_right a) (hl.tendsto_mul_left a)

/-- Along an increasing approximate unit, `e * a → a` uniformly for `a` in a compact set. -/
theorem tendstoUniformlyOn_mul_right {l : Filter A} (hl : l.IsIncreasingApproximateUnit)
    {K : Set A} (hK : IsCompact K) : TendstoUniformlyOn (fun e a => e * a) id l K :=
  TauCeti.tendstoUniformlyOn_of_lipschitzWith
    (hl.eventually_norm.mono fun e h => (TauCeti.lipschitzWith_mul_left e).weaken
      (by rwa [← NNReal.coe_le_coe, coe_nnNorm, NNReal.coe_one]))
    hK fun a _ => hl.tendsto_mul_right a

/-- Along an increasing approximate unit, `a * e → a` uniformly for `a` in a compact set. -/
theorem tendstoUniformlyOn_mul_left {l : Filter A} (hl : l.IsIncreasingApproximateUnit)
    {K : Set A} (hK : IsCompact K) : TendstoUniformlyOn (fun e a => a * e) id l K :=
  TauCeti.tendstoUniformlyOn_of_lipschitzWith
    (hl.eventually_norm.mono fun e h => (TauCeti.lipschitzWith_mul_right e).weaken
      (by rwa [← NNReal.coe_le_coe, coe_nnNorm, NNReal.coe_one]))
    hK fun a _ => hl.tendsto_mul_left a

end Uniform

section Map

variable {A B F : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [FunLike F A B] [NonUnitalAlgHomClass F ℂ A B] [StarHomClass F A B]

/-- The image of an increasing approximate unit under a surjective star-algebra homomorphism of
C⋆-algebras is an increasing approximate unit. -/
theorem map {l : Filter A} (hl : l.IsIncreasingApproximateUnit) (f : F)
    (hf : Function.Surjective f) : (l.map f).IsIncreasingApproximateUnit where
  toIsApproximateUnit := hl.toIsApproximateUnit.map f (map_continuous f) hf
  eventually_nonneg := eventually_map.mpr <| hl.eventually_nonneg.mono fun _ hx => map_nonneg f hx
  eventually_norm := eventually_map.mpr <| hl.eventually_norm.mono fun a ha =>
    (NonUnitalStarAlgHom.norm_apply_le f a).trans ha

end Map

end Filter.IsIncreasingApproximateUnit

namespace TauCeti.CStarAlgebra

open Unitization

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- For a positive contraction `e` in a nonunital C⋆-algebra and any `a`, the C⋆-identity in the
unitization gives `‖e * star a - star a‖ ^ 2 ≤ ‖star a * a - e * (star a * a)‖`. -/
theorem norm_mul_star_sub_star_sq_le {e : A} (he₀ : 0 ≤ e) (he₁ : ‖e‖ ≤ 1) (a : A) :
    ‖e * star a - star a‖ ^ 2 ≤ ‖star a * a - e * (star a * a)‖ := by
  have he_icc : (e : A⁺¹) ∈ Set.Icc (0 : A⁺¹) 1 :=
    CStarAlgebra.inr_mem_Icc_iff_norm_le.mpr ⟨he₀, he₁⟩
  have h1_icc : 1 - (e : A⁺¹) ∈ Set.Icc (0 : A⁺¹) 1 :=
    Set.sub_mem_Icc_zero_iff_right.mpr he_icc
  obtain ⟨h1_nonneg, h1_norm⟩ := CStarAlgebra.mem_Icc_iff_norm_le_one.mp h1_icc
  have h1_star : star (1 - (e : A⁺¹)) = 1 - (e : A⁺¹) :=
    (IsSelfAdjoint.of_nonneg h1_nonneg).star_eq
  let b : A⁺¹ := (1 - (e : A⁺¹)) * star (a : A⁺¹)
  have hb_norm : ‖e * star a - star a‖ = ‖b‖ := by
    rw [norm_sub_rev, ← Unitization.norm_inr (𝕜 := ℂ), Unitization.inr_sub,
      Unitization.inr_mul, Unitization.inr_star]
    congr 1
    dsimp only [b]
    rw [sub_mul, one_mul]
  have hb_mul : b * star b = ((star a * a - e * (star a * a) : A) : A⁺¹) * (1 - (e : A⁺¹)) := by
    simp only [b, star_mul, star_star, h1_star, Unitization.inr_sub, Unitization.inr_mul,
      Unitization.inr_star]
    noncomm_ring
  calc
    ‖e * star a - star a‖ ^ 2 = ‖b‖ ^ 2 := by rw [hb_norm]
    _ = ‖b * star b‖ := by rw [sq, ← CStarRing.norm_self_mul_star]
    _ = ‖((star a * a - e * (star a * a) : A) : A⁺¹) * (1 - (e : A⁺¹))‖ := by rw [hb_mul]
    _ ≤ ‖((star a * a - e * (star a * a) : A) : A⁺¹)‖ * ‖1 - (e : A⁺¹)‖ := norm_mul_le _ _
    _ ≤ ‖star a * a - e * (star a * a)‖ * 1 := by
      rw [Unitization.norm_inr]
      exact mul_le_mul_of_nonneg_left h1_norm (norm_nonneg _)
    _ = ‖star a * a - e * (star a * a)‖ := mul_one _

/-- For a positive contraction `e` in a nonunital C⋆-algebra and any `a` and `z`, the C⋆-identity in
the unitization applied to `a * (1 - e)` gives `‖a - a * e‖ ^ 2 ≤ ‖star a * a + z‖ + ‖z - z * e‖`.
With `z` in a closed two-sided ideal `I` and `e` running through an approximate unit of `I`, the
last term tends to `0`; this bounds `‖mk I a‖ ^ 2` by `‖star a * a + z‖` in the quotient `A ⧸ I`.
-/
theorem norm_sub_mul_sq_le {e : A} (he₀ : 0 ≤ e) (he₁ : ‖e‖ ≤ 1) (a z : A) :
    ‖a - a * e‖ ^ 2 ≤ ‖star a * a + z‖ + ‖z - z * e‖ := by
  have h1_icc : 1 - (e : A⁺¹) ∈ Set.Icc (0 : A⁺¹) 1 :=
    Set.sub_mem_Icc_zero_iff_right.mpr (CStarAlgebra.inr_mem_Icc_iff_norm_le.mpr ⟨he₀, he₁⟩)
  obtain ⟨h1_nonneg, h1_norm⟩ := CStarAlgebra.mem_Icc_iff_norm_le_one.mp h1_icc
  have h1_star : star (1 - (e : A⁺¹)) = 1 - (e : A⁺¹) :=
    (IsSelfAdjoint.of_nonneg h1_nonneg).star_eq
  have hb : ((a - a * e : A) : A⁺¹) = (a : A⁺¹) * (1 - (e : A⁺¹)) := by
    rw [Unitization.inr_sub, Unitization.inr_mul, mul_sub, mul_one]
  have hb_mul : star ((a : A⁺¹) * (1 - (e : A⁺¹))) * ((a : A⁺¹) * (1 - (e : A⁺¹))) =
      (1 - (e : A⁺¹)) * ((star a * a + z : A) : A⁺¹) * (1 - (e : A⁺¹)) -
        (1 - (e : A⁺¹)) * ((z - z * e : A) : A⁺¹) := by
    simp only [star_mul, h1_star, Unitization.inr_add, Unitization.inr_sub, Unitization.inr_mul,
      Unitization.inr_star]
    noncomm_ring
  rw [← Unitization.norm_inr (𝕜 := ℂ), hb, sq, ← CStarRing.norm_star_mul_self, hb_mul,
    ← Unitization.norm_inr (𝕜 := ℂ) (star a * a + z), ← Unitization.norm_inr (𝕜 := ℂ) (z - z * e)]
  refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
  · simpa only [one_mul, mul_one] using
      norm_mul_le_of_le (norm_mul_le_of_le h1_norm le_rfl) h1_norm
  · simpa only [one_mul] using norm_mul_le_of_le h1_norm le_rfl

/-- If `star x * x ≤ star y * y` in a nonunital C⋆-algebra, then `‖x - x * e‖ ≤ ‖y - y * e‖` for
every `e : A` (no positivity or norm bound on `e` is needed). -/
theorem norm_sub_mul_le_of_star_mul_self_le {x y : A} (hxy : star x * x ≤ star y * y) (e : A) :
    ‖x - x * e‖ ≤ ‖y - y * e‖ := by
  have hsq (z : A) :
      ‖z - z * e‖ ^ 2 = ‖star (1 - (e : A⁺¹)) * ((star z * z : A) : A⁺¹) * (1 - (e : A⁺¹))‖ := by
    have hz : ((z - z * e : A) : A⁺¹) = (z : A⁺¹) * (1 - (e : A⁺¹)) := by
      rw [Unitization.inr_sub, Unitization.inr_mul, mul_sub, mul_one]
    rw [← Unitization.norm_inr (𝕜 := ℂ), hz, sq, ← CStarRing.norm_star_mul_self]
    simp only [star_mul, Unitization.inr_mul, Unitization.inr_star, mul_assoc]
  have hle : ‖x - x * e‖ ^ 2 ≤ ‖y - y * e‖ ^ 2 := by
    rw [hsq x, hsq y]
    refine CStarAlgebra.norm_le_norm_of_le_of_nonneg
      (star_left_conjugate_le_conjugate ((Unitization.inr_le_inr_iff ℂ).mpr hxy) (1 - (e : A⁺¹))) ?_
    exact star_left_conjugate_nonneg ((Unitization.inr_nonneg_iff ℂ).mpr (star_mul_self_nonneg x)) _
  exact (sq_le_sq.mp hle).trans_eq (abs_of_nonneg (norm_nonneg _)) |>.trans'
    (le_abs_self _)

/-- If `e` is a self-adjoint contraction and `star y * y ≤ b`, then
`‖y - y * e‖ ^ 2 ≤ 2 * ‖b - b * e‖`: the defect of `e` as a right unit for `y` is controlled by
its defect for `b`. -/
theorem norm_sub_mul_sq_le_of_star_mul_self_le {e y b : A} (he : IsSelfAdjoint e)
    (he₁ : ‖e‖ ≤ 1) (hyb : star y * y ≤ b) : ‖y - y * e‖ ^ 2 ≤ 2 * ‖b - b * e‖ := by
  -- `c p` is the compression `(1 - e) p (1 - e)`, written without a unit.
  set c : A → A := fun p ↦ (p - p * e) - e * (p - p * e) with hc
  have hc_star (z : A) : star (z - z * e) * (z - z * e) = c (star z * z) := by
    simp only [hc, star_sub, star_mul, he.star_eq]
    noncomm_ring
  have hc_nonneg {p : A} (hp : 0 ≤ p) : 0 ≤ c p := by
    obtain ⟨z, rfl⟩ := _root_.CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hp
    rw [← hc_star]
    exact star_mul_self_nonneg _
  have hle : c (star y * y) ≤ c b := by
    rw [← sub_nonneg]
    convert hc_nonneg (sub_nonneg.mpr hyb) using 1
    simp only [hc]
    noncomm_ring
  calc ‖y - y * e‖ ^ 2 = ‖c (star y * y)‖ := by
        rw [← hc_star, CStarRing.norm_star_mul_self, sq]
    _ ≤ ‖c b‖ :=
        _root_.CStarAlgebra.norm_le_norm_of_le_of_nonneg hle (hc_nonneg (star_mul_self_nonneg y))
    _ ≤ ‖b - b * e‖ + ‖e‖ * ‖b - b * e‖ :=
        (norm_sub_le _ _).trans (by gcongr; exact norm_mul_le _ _)
    _ ≤ 2 * ‖b - b * e‖ := by nlinarith [norm_nonneg (b - b * e)]

/-- Along a filter of self-adjoint contractions, a right approximate unit for `b` is a right
approximate unit for every `y` with `star y * y ≤ b`. -/
theorem tendsto_mul_of_star_mul_self_le {l : Filter A} {y b : A}
    (he : ∀ᶠ e in l, IsSelfAdjoint e) (he₁ : ∀ᶠ e in l, ‖e‖ ≤ 1) (hyb : star y * y ≤ b)
    (hb : Tendsto (b * ·) l (𝓝 b)) : Tendsto (y * ·) l (𝓝 y) := by
  rw [tendsto_iff_norm_sub_tendsto_zero] at hb ⊢
  have hs : Tendsto (fun e ↦ √(2 * ‖b * e - b‖)) l (𝓝 0) := by
    simpa only [Function.comp_def, mul_zero, Real.sqrt_zero] using
      (Real.continuous_sqrt.tendsto 0).comp ((hb.const_mul 2).trans (by rw [mul_zero]))
  refine squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _) ?_ hs
  filter_upwards [he, he₁] with e he he₁
  rw [norm_sub_rev, norm_sub_rev (b * e)]
  exact Real.le_sqrt_of_sq_le (norm_sub_mul_sq_le_of_star_mul_self_le he he₁ hyb)

end TauCeti.CStarAlgebra

namespace Filter.IsIncreasingApproximateUnit

section Subalgebra

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  {B : NonUnitalStarSubalgebra ℂ A} [IsClosed (B : Set A)]

/-- Along an increasing approximate unit `l` of a closed `⋆`-subalgebra `B`, right convergence
`x * (e : A) → x` implies left convergence `(e : A) * star x → star x` via `star` continuity. -/
theorem tendsto_coe_mul_star_of_tendsto_mul_coe {l : Filter B} (hl : l.IsIncreasingApproximateUnit)
    {x : A} (h : Tendsto (fun e : B => x * (e : A)) l (𝓝 x)) :
    Tendsto (fun e : B => (e : A) * star x) l (𝓝 (star x)) := by
  refine ((continuous_star.tendsto x).comp h).congr' ?_
  filter_upwards [hl.eventually_nonneg] with e he
  simp only [Function.comp_def, star_mul,
    (IsSelfAdjoint.of_nonneg (Subtype.coe_le_coe.mpr he)).star_eq]

/-- If `star x * x` belongs to a closed `⋆`-subalgebra `B`, then `(e : A) * star x → star x` along
any increasing approximate unit `l` of `B`. -/
theorem tendsto_mul_star_of_star_mul_self_mem {l : Filter B} (hl : l.IsIncreasingApproximateUnit)
    {x : A} (hx : star x * x ∈ B) :
    Tendsto (fun e : B => (e : A) * star x) l (𝓝 (star x)) := by
  let k : B := ⟨star x * x, hx⟩
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hsq : ∀ᶠ e : B in l, ‖(e : A) * star x - star x‖ ^ 2 ≤ ‖e * k - k‖ := by
    filter_upwards [hl.eventually_nonneg, hl.eventually_norm] with e he₀ he₁
    have h := TauCeti.CStarAlgebra.norm_mul_star_sub_star_sq_le (A := A)
      (Subtype.coe_le_coe.mpr he₀) he₁ x
    rwa [norm_sub_rev (star x * x)] at h
  have hk_lim : Tendsto (fun e : B => Real.sqrt ‖e * k - k‖) l (𝓝 0) := by
    simpa only [Real.sqrt_zero, Function.comp_def] using
      (Real.continuous_sqrt.tendsto 0).comp
        (tendsto_iff_norm_sub_tendsto_zero.mp (hl.tendsto_mul_right k))
  refine squeeze_zero_norm' ?_ hk_lim
  filter_upwards [hsq] with e he
  rw [Real.norm_of_nonneg (norm_nonneg _)]
  exact Real.le_sqrt_of_sq_le he

/-- If `star x * x` belongs to a closed `⋆`-subalgebra `B`, then `x * (e : A) → x` along any
increasing approximate unit `l` of `B`. -/
theorem tendsto_mul_of_star_mul_self_mem {l : Filter B} (hl : l.IsIncreasingApproximateUnit)
    {x : A} (hx : star x * x ∈ B) :
    Tendsto (fun e : B => x * (e : A)) l (𝓝 x) := by
  have hstar := (continuous_star.tendsto (star x)).comp
    (hl.tendsto_mul_star_of_star_mul_self_mem hx)
  rw [star_star] at hstar
  refine hstar.congr' ?_
  filter_upwards [hl.eventually_nonneg] with e he
  simp only [Function.comp_def, star_mul, star_star,
    (IsSelfAdjoint.of_nonneg (Subtype.coe_le_coe.mpr he)).star_eq]

/-- If `x * star x` belongs to a closed `⋆`-subalgebra `B`, then `(e : A) * x → x` along any
increasing approximate unit `l` of `B`. -/
theorem tendsto_mul_of_mul_star_self_mem {l : Filter B} (hl : l.IsIncreasingApproximateUnit)
    {x : A} (hx : x * star x ∈ B) :
    Tendsto (fun e : B => (e : A) * x) l (𝓝 x) := by
  simpa only [star_star] using
    hl.tendsto_mul_star_of_star_mul_self_mem (x := star x) (by simpa only [star_star] using hx)

end Subalgebra

end Filter.IsIncreasingApproximateUnit

namespace NonUnitalStarSubalgebra

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- A closed star subalgebra `B` of a C⋆-algebra has an approximate unit of positive (hence
self-adjoint) contractions: a proper filter on `A` that eventually lies in `B`, along which
`b * e → b` and `e * b → b` for every `b ∈ B`. -/
theorem exists_approximateUnit {B : NonUnitalStarSubalgebra ℂ A} (hB : IsClosed (B : Set A)) :
    ∃ l : Filter A, l.NeBot ∧ (∀ᶠ e in l, e ∈ B) ∧ (∀ᶠ e in l, 0 ≤ e) ∧
      (∀ᶠ e in l, IsSelfAdjoint e) ∧ (∀ᶠ e in l, ‖e‖ ≤ 1) ∧
      ∀ b ∈ B, Tendsto (b * ·) l (𝓝 b) ∧ Tendsto (· * b) l (𝓝 b) := by
  let _ : NonUnitalCStarAlgebra B := nonUnitalCStarAlgebra B (h_closed := hB)
  have _ : StarOrderedRing B := Subtype.starOrderedRing B (hs := hB)
  have hl := CStarAlgebra.increasingApproximateUnit B
  have := hl.neBot
  have hpos : ∀ᶠ e in (CStarAlgebra.approximateUnit B).map ((↑) : B → A), 0 ≤ e :=
    eventually_map.mpr <| hl.eventually_nonneg.mono fun e he ↦
      (ZeroMemClass.coe_zero B).symm.trans_le (Subtype.coe_le_coe.mpr he)
  refine ⟨_, inferInstance, eventually_map.mpr <| .of_forall fun e ↦ e.property, hpos,
    hpos.mono fun _ ↦ IsSelfAdjoint.of_nonneg,
    eventually_map.mpr <| hl.eventually_norm.mono fun e he ↦
      (AddSubgroupClass.coe_norm (s := B) e).symm.trans_le he, fun b hb ↦ ⟨?_, ?_⟩⟩
  · simpa only [tendsto_map'_iff, Function.comp_def, NonUnitalStarSubalgebra.coe_mul] using
      (continuous_subtypeVal.tendsto _).comp (hl.tendsto_mul_left ⟨b, hb⟩)
  · simpa only [tendsto_map'_iff, Function.comp_def, NonUnitalStarSubalgebra.coe_mul] using
      (continuous_subtypeVal.tendsto _).comp (hl.tendsto_mul_right ⟨b, hb⟩)

end NonUnitalStarSubalgebra
