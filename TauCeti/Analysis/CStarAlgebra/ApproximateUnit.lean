/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.ApproximateUnit
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
public import TauCeti.Topology.ApproximateUnit
import Mathlib.Algebra.Order.Interval.Set.Group

/-!
# Increasing approximate units: images, uniform convergence, and order-dominated limits

A star-algebra homomorphism between C⋆-algebras is positive and contractive, so it maps the
positive part of the closed unit ball into itself. Hence the image of an increasing approximate
unit under a surjective homomorphism is an increasing approximate unit of the target,
`Filter.IsIncreasingApproximateUnit.map`. This transfers approximate-unit limits, such as the
norm of a positive functional, from a C⋆-algebra to its quotients.

Since an increasing approximate unit eventually lies in the closed unit ball, the convergence
`e * a → a` is uniform for `a` in a compact set,
`Filter.IsIncreasingApproximateUnit.tendstoUniformlyOn_mul_right`, and so is the convergence
`a * e → a`, `Filter.IsIncreasingApproximateUnit.tendstoUniformlyOn_mul_left`, while the two-sided
product `e * a * e` converges pointwise to `a`,
`Filter.IsIncreasingApproximateUnit.tendsto_mul_mul` (deduced from the general contractive
sandwich limit `TauCeti.tendsto_mul_mul_of_tendsto`). Uniform convergence controls
`e * α_r(b) → α_r(b)` along a compact set of group elements `r` for a continuous action `α`, as
needed for approximate units of twisted convolution algebras.

`TauCeti.CStarAlgebra.norm_sub_mul_sq_le_of_star_mul_self_le` bounds `‖x - x * e‖ ^ 2` by
`‖b - e * b‖` whenever `0 ≤ e`, `‖e‖ ≤ 1`, and `star x * x ≤ b`, yielding both
`TauCeti.CStarAlgebra.norm_mul_star_sub_star_sq_le` and
`TauCeti.CStarAlgebra.norm_sqrt_sub_mul_sq_le`. For any closed star subalgebra `s` and any
increasing approximate unit `l` of `s`, this drives
`Filter.IsIncreasingApproximateUnit.tendsto_mul_left_of_star_mul_self_le`,
`Filter.IsIncreasingApproximateUnit.tendsto_mul_left_of_star_mul_self_mem`,
`Filter.IsIncreasingApproximateUnit.tendsto_sqrt_mul_of_nonneg_of_le`, and
`Filter.IsIncreasingApproximateUnit.tendsto_mul_mul_of_nonneg_of_le`. Meanwhile
`TauCeti.CStarAlgebra.norm_sub_mul_sq_le`, `‖a - a * e‖ ^ 2 ≤ ‖star a * a + z‖ + ‖z - z * e‖`,
drives the proof of the C⋆-identity on the quotient by a closed two-sided ideal.
-/

public section

open Filter Topology
open scoped CStarAlgebra

namespace TauCeti

/-- In a nonunital seminormed ring, if `u i` and `v i` are eventually contractions along a filter
`l` such that `f i → b`, `u i * b → b`, and `b * v i → b`, then `u i * f i * v i → b`. -/
theorem tendsto_mul_mul_of_tendsto {ι A : Type*} [NonUnitalSeminormedRing A] {l : Filter ι}
    {u f v : ι → A} {b : A} (hu₁ : ∀ᶠ i in l, ‖u i‖ ≤ 1) (hv₁ : ∀ᶠ i in l, ‖v i‖ ≤ 1)
    (hf : Tendsto f l (𝓝 b)) (hu : Tendsto (fun i ↦ u i * b) l (𝓝 b))
    (hv : Tendsto (fun i ↦ b * v i) l (𝓝 b)) :
    Tendsto (fun i ↦ u i * f i * v i) l (𝓝 b) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hzero : Tendsto (fun i ↦ ‖f i - b‖ + (‖u i * b - b‖ + ‖b * v i - b‖)) l (𝓝 0) := by
    simpa only [add_zero] using (tendsto_iff_norm_sub_tendsto_zero.mp hf).add
      ((tendsto_iff_norm_sub_tendsto_zero.mp hu).add (tendsto_iff_norm_sub_tendsto_zero.mp hv))
  refine squeeze_zero_norm' ?_ hzero
  filter_upwards [hu₁, hv₁] with i hui hvi
  have hsub : u i * f i * v i - b =
      u i * (f i - b) * v i + ((u i * b - b) * v i + (b * v i - b)) := by noncomm_ring
  rw [Real.norm_of_nonneg (norm_nonneg _), hsub]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · exact ((norm_mul_le _ _).trans (mul_le_of_le_one_right (norm_nonneg _) hvi)).trans
      ((norm_mul_le _ _).trans (mul_le_of_le_one_left (norm_nonneg _) hui))
  · exact (norm_add_le _ _).trans (add_le_add
      ((norm_mul_le _ _).trans (mul_le_of_le_one_right (norm_nonneg _) hvi)) le_rfl)

end TauCeti

namespace TauCeti.CStarAlgebra

open Unitization

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- For a positive contraction `e` in a nonunital C⋆-algebra and `star x * x ≤ b`, the C⋆-identity
and order monotonicity of the norm in `A⁺¹` give `‖x - x * e‖ ^ 2 ≤ ‖b - e * b‖`. -/
theorem norm_sub_mul_sq_le_of_star_mul_self_le {e x b : A} (he₀ : 0 ≤ e) (he₁ : ‖e‖ ≤ 1)
    (hxb : star x * x ≤ b) :
    ‖x - x * e‖ ^ 2 ≤ ‖b - e * b‖ := by
  let u : A⁺¹ := 1 - (e : A⁺¹)
  have hu_icc : u ∈ Set.Icc (0 : A⁺¹) 1 :=
    Set.sub_mem_Icc_zero_iff_right.mpr (CStarAlgebra.inr_mem_Icc_iff_norm_le.mpr ⟨he₀, he₁⟩)
  obtain ⟨hu_nonneg, hu_norm⟩ := CStarAlgebra.mem_Icc_iff_norm_le_one.mp hu_icc
  have hu_star : star u = u := (IsSelfAdjoint.of_nonneg hu_nonneg).star_eq
  have hdiff : ((x - x * e : A) : A⁺¹) = (x : A⁺¹) * u := by
    simp only [u, Unitization.inr_sub, Unitization.inr_mul, mul_sub, mul_one]
  have hstar_mul : star ((x : A⁺¹) * u) * ((x : A⁺¹) * u) = u * ((star x * x : A) : A⁺¹) * u := by
    rw [star_mul, hu_star, ← Unitization.inr_star, mul_assoc, ← mul_assoc ((star x : A) : A⁺¹),
      ← Unitization.inr_mul, mul_assoc]
  have hle : u * ((star x * x : A) : A⁺¹) * u ≤ u * (b : A⁺¹) * u := by
    simpa only [hu_star] using
      star_left_conjugate_le_conjugate (Unitization.inr_le_inr_iff.mpr hxb) u
  have hux_nonneg : 0 ≤ u * ((star x * x : A) : A⁺¹) * u := by
    simpa only [hu_star] using
      star_left_conjugate_nonneg (Unitization.inr_nonneg_iff.mpr (star_mul_self_nonneg x)) u
  have hub_eq : u * (b : A⁺¹) * u = ((b - e * b : A) : A⁺¹) * u := by
    simp only [u, Unitization.inr_sub, Unitization.inr_mul]
    noncomm_ring
  calc
    ‖x - x * e‖ ^ 2 = ‖((x - x * e : A) : A⁺¹)‖ ^ 2 := by rw [Unitization.norm_inr]
    _ = ‖u * ((star x * x : A) : A⁺¹) * u‖ := by
      rw [hdiff, sq, ← CStarRing.norm_star_mul_self, hstar_mul]
    _ ≤ ‖u * (b : A⁺¹) * u‖ := CStarAlgebra.norm_le_norm_of_le_of_nonneg hle hux_nonneg
    _ = ‖((b - e * b : A) : A⁺¹) * u‖ := by rw [hub_eq]
    _ ≤ ‖b - e * b‖ * 1 := by
      refine (norm_mul_le _ _).trans ?_
      rw [Unitization.norm_inr]
      exact mul_le_mul_of_nonneg_left hu_norm (norm_nonneg _)
    _ = ‖b - e * b‖ := mul_one _

/-- For a positive contraction `e` in a nonunital C⋆-algebra and any `a`, the C⋆-identity in the
unitization gives `‖e * star a - star a‖ ^ 2 ≤ ‖star a * a - e * (star a * a)‖`. -/
theorem norm_mul_star_sub_star_sq_le {e : A} (he₀ : 0 ≤ e) (he₁ : ‖e‖ ≤ 1) (a : A) :
    ‖e * star a - star a‖ ^ 2 ≤ ‖star a * a - e * (star a * a)‖ := by
  have hnorm : ‖e * star a - star a‖ = ‖a - a * e‖ := by
    rw [norm_sub_rev, ← norm_star (a - a * e), star_sub, star_mul,
      (IsSelfAdjoint.of_nonneg he₀).star_eq]
  rw [hnorm]
  exact norm_sub_mul_sq_le_of_star_mul_self_le he₀ he₁ le_rfl

/-- For a positive contraction `e` in `A` and `0 ≤ a ≤ b`, the C⋆-identity and order monotonicity of
the norm in `A⁺¹` give `‖CFC.sqrt a - CFC.sqrt a * e‖ ^ 2 ≤ ‖b - e * b‖`. -/
theorem norm_sqrt_sub_mul_sq_le {e a b : A} (he₀ : 0 ≤ e) (he₁ : ‖e‖ ≤ 1)
    (ha : 0 ≤ a) (hab : a ≤ b) :
    ‖CFC.sqrt a - CFC.sqrt a * e‖ ^ 2 ≤ ‖b - e * b‖ := by
  refine norm_sub_mul_sq_le_of_star_mul_self_le he₀ he₁ ?_
  rwa [(CFC.sqrt_nonneg a).isSelfAdjoint.star_eq, CFC.sqrt_mul_sqrt_self a ha]

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

end TauCeti.CStarAlgebra

namespace Filter.IsIncreasingApproximateUnit

section Uniform

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A]

/-- Along an increasing approximate unit, `e * a → a` uniformly for `a` in a compact set. -/
theorem tendstoUniformlyOn_mul_right {l : Filter A} (hl : l.IsIncreasingApproximateUnit)
    {K : Set A} (hK : IsCompact K) : TendstoUniformlyOn (fun e a => e * a) id l K := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  -- Cover `K` by finitely many balls of radius `ε / 3`, and use the eventual bound `‖e‖ ≤ 1`.
  obtain ⟨t, -, ht, hKt⟩ := hK.finite_cover_balls (e := ε / 3) (by positivity)
  have hconv : ∀ᶠ e in l, ∀ c ∈ t, dist c (e * c) < ε / 3 := (eventually_all_finite ht).2
    fun c _ => (Metric.tendsto_nhds.1 (hl.tendsto_mul_right c) (ε / 3) (by positivity)).mono
      fun _ h => by rwa [dist_comm]
  filter_upwards [hl.eventually_norm, hconv] with e he hc a ha
  obtain ⟨c, hct, hac⟩ := Set.mem_iUnion₂.1 (hKt ha)
  have hmul : dist (e * c) (e * a) ≤ dist c a := by
    rw [dist_eq_norm, dist_eq_norm, ← mul_sub]
    exact (norm_mul_le _ _).trans (mul_le_of_le_one_left (norm_nonneg _) he)
  calc dist (id a) (e * a) ≤ dist a c + dist c (e * c) + dist (e * c) (e * a) :=
        dist_triangle4 _ _ _ _
    _ < ε / 3 + ε / 3 + ε / 3 := by
        gcongr
        · exact Metric.mem_ball.1 hac
        · exact hc c hct
        · exact hmul.trans_lt (by rw [dist_comm]; exact Metric.mem_ball.1 hac)
    _ = ε := by ring

/-- Along an increasing approximate unit, `a * e → a` uniformly for `a` in a compact set. -/
theorem tendstoUniformlyOn_mul_left {l : Filter A} (hl : l.IsIncreasingApproximateUnit)
    {K : Set A} (hK : IsCompact K) : TendstoUniformlyOn (fun e a => a * e) id l K := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  -- Cover `K` by finitely many balls of radius `ε / 3`, and use the eventual bound `‖e‖ ≤ 1`.
  obtain ⟨t, -, ht, hKt⟩ := hK.finite_cover_balls (e := ε / 3) (by positivity)
  have hconv : ∀ᶠ e in l, ∀ c ∈ t, dist c (c * e) < ε / 3 := (eventually_all_finite ht).2
    fun c _ => (Metric.tendsto_nhds.1 (hl.tendsto_mul_left c) (ε / 3) (by positivity)).mono
      fun _ h => by rwa [dist_comm]
  filter_upwards [hl.eventually_norm, hconv] with e he hc a ha
  obtain ⟨c, hct, hac⟩ := Set.mem_iUnion₂.1 (hKt ha)
  have hmul : dist (c * e) (a * e) ≤ dist c a := by
    rw [dist_eq_norm, dist_eq_norm, ← sub_mul]
    exact (norm_mul_le _ _).trans (mul_le_of_le_one_right (norm_nonneg _) he)
  calc dist (id a) (a * e) ≤ dist a c + dist c (c * e) + dist (c * e) (a * e) :=
        dist_triangle4 _ _ _ _
    _ < ε / 3 + ε / 3 + ε / 3 := by
        gcongr
        · exact Metric.mem_ball.1 hac
        · exact hc c hct
        · exact hmul.trans_lt (by rw [dist_comm]; exact Metric.mem_ball.1 hac)
    _ = ε := by ring

/-- Along an increasing approximate unit, the two-sided product `e * a * e` converges to `a`. -/
theorem tendsto_mul_mul {l : Filter A} (hl : l.IsIncreasingApproximateUnit) (a : A) :
    Tendsto (fun e => e * a * e) l (𝓝 a) :=
  TauCeti.tendsto_mul_mul_of_tendsto hl.eventually_norm hl.eventually_norm tendsto_const_nhds
    (hl.tendsto_mul_right a) (hl.tendsto_mul_left a)

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

section SubalgebraOrderLimits

variable {S A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [SetLike S A] [NonUnitalSubringClass S A] [SMulMemClass S ℂ A] [StarMemClass S A]
  {s : S} [IsClosed (s : Set A)] {l : Filter s}

/-- If `star x * x ≤ b` with `b` in a closed star subalgebra `s`, then `x * (e : A) → x` along any
increasing approximate unit `l` of `s`. -/
theorem tendsto_mul_left_of_star_mul_self_le (hl : l.IsIncreasingApproximateUnit) {x b : A}
    (hxb : star x * x ≤ b) (hb : b ∈ s) :
    Tendsto (fun e : s ↦ x * (e : A)) l (𝓝 x) := by
  let bS : s := ⟨b, hb⟩
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hsq : ∀ᶠ e : s in l, ‖x * (e : A) - x‖ ^ 2 ≤ ‖bS - e * bS‖ := by
    filter_upwards [hl.eventually_nonneg, hl.eventually_norm] with e he₀ he₁
    rw [← Subtype.coe_le_coe, ZeroMemClass.coe_zero] at he₀
    rw [AddSubgroupClass.coe_norm] at he₁
    rw [norm_sub_rev, AddSubgroupClass.coe_norm, AddSubgroupClass.coe_sub, MulMemClass.coe_mul]
    exact TauCeti.CStarAlgebra.norm_sub_mul_sq_le_of_star_mul_self_le he₀ he₁ hxb
  have hb_lim : Tendsto (fun e : s ↦ ‖bS - e * bS‖) l (𝓝 0) := by
    simpa only [norm_sub_rev] using tendsto_iff_norm_sub_tendsto_zero.mp (hl.tendsto_mul_right bS)
  have hsqrt : Tendsto (fun e : s ↦ Real.sqrt ‖bS - e * bS‖) l (𝓝 0) := by
    simpa only [Real.sqrt_zero, Function.comp_def] using
      (Real.continuous_sqrt.tendsto 0).comp hb_lim
  refine squeeze_zero_norm' ?_ hsqrt
  filter_upwards [hsq] with e he
  rw [Real.norm_of_nonneg (norm_nonneg _)]
  exact Real.le_sqrt_of_sq_le he

/-- If `star x * x` belongs to a closed star subalgebra `s`, then `x * (e : A) → x` along any
increasing approximate unit `l` of `s`. -/
theorem tendsto_mul_left_of_star_mul_self_mem (hl : l.IsIncreasingApproximateUnit) {x : A}
    (hx : star x * x ∈ s) :
    Tendsto (fun e : s ↦ x * (e : A)) l (𝓝 x) :=
  hl.tendsto_mul_left_of_star_mul_self_le le_rfl hx

/-- If `0 ≤ a ≤ b` and `b` lies in a closed star subalgebra `s`, then
`CFC.sqrt a * (e : A) → CFC.sqrt a` along any increasing approximate unit `l` of `s`. -/
theorem tendsto_sqrt_mul_of_nonneg_of_le (hl : l.IsIncreasingApproximateUnit) {a b : A}
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ∈ s) :
    Tendsto (fun e : s ↦ CFC.sqrt a * (e : A)) l (𝓝 (CFC.sqrt a)) := by
  refine hl.tendsto_mul_left_of_star_mul_self_le ?_ hb
  rwa [(CFC.sqrt_nonneg a).isSelfAdjoint.star_eq, CFC.sqrt_mul_sqrt_self a ha]

/-- If `0 ≤ a ≤ b` and `b` lies in a closed star subalgebra `s`, then `(e : A) * a * (e : A) → a`
along any increasing approximate unit `l` of `s`. -/
theorem tendsto_mul_mul_of_nonneg_of_le (hl : l.IsIncreasingApproximateUnit) {a b : A}
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ∈ s) :
    Tendsto (fun e : s ↦ (e : A) * a * (e : A)) l (𝓝 a) := by
  have hright : Tendsto (fun e : s ↦ CFC.sqrt a * (e : A)) l (𝓝 (CFC.sqrt a)) :=
    hl.tendsto_sqrt_mul_of_nonneg_of_le ha hab hb
  have hs_star : star (CFC.sqrt a) = CFC.sqrt a := (CFC.sqrt_nonneg a).isSelfAdjoint.star_eq
  have hleft : Tendsto (fun e : s ↦ (e : A) * CFC.sqrt a) l (𝓝 (CFC.sqrt a)) := by
    have hstar : Tendsto (fun e : s ↦ star (CFC.sqrt a * (e : A))) l (𝓝 (star (CFC.sqrt a))) :=
      (continuous_star.tendsto _).comp hright
    rw [hs_star] at hstar
    refine hstar.congr' ?_
    filter_upwards [hl.eventually_star_eq] with e he_star
    have he_coe : star (e : A) = (e : A) := by
      simpa only [StarMemClass.coe_star] using congrArg ((↑) : s → A) he_star
    rw [star_mul, hs_star, he_coe]
  have hmul : Tendsto (fun e : s ↦ ((e : A) * CFC.sqrt a) * (CFC.sqrt a * (e : A))) l
      (𝓝 (CFC.sqrt a * CFC.sqrt a)) :=
    hleft.mul hright
  rw [CFC.sqrt_mul_sqrt_self a ha] at hmul
  refine hmul.congr fun e ↦ ?_
  simp only [mul_assoc, ← mul_assoc (CFC.sqrt a), CFC.sqrt_mul_sqrt_self a ha]

end SubalgebraOrderLimits

end Filter.IsIncreasingApproximateUnit
