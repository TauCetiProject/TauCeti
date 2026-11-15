/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Hull
public import Mathlib.Analysis.CStarAlgebra.ApproximateUnit
public import TauCeti.Topology.ApproximateUnit
import Mathlib.Algebra.Order.Interval.Set.Group
import Mathlib.Analysis.Convex.Cone.InnerDual
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Mathlib.Analysis.Normed.Module.Convex

/-!
# Increasing approximate units: subnets, convexification, transport and estimates

A star-algebra homomorphism between C⋆-algebras is positive and contractive, so it maps the
positive part of the closed unit ball into itself. Hence the image of an increasing approximate
unit under a surjective homomorphism is an increasing approximate unit of the target,
`Filter.IsIncreasingApproximateUnit.map`, and star-algebra equivalences preserve increasing
approximate units in both directions, `Filter.IsIncreasingApproximateUnit.map_equiv_iff`. Passing
to a proper subfilter (`Filter.IsIncreasingApproximateUnit.mono`) or replacing every member of the
filter by its real convex hull (`Filter.IsIncreasingApproximateUnit.lift'_convexHull`) also
preserves `Filter.IsIncreasingApproximateUnit`.

Along any approximate unit of a C⋆-algebra, two-sided compression `e * a * e` converges in norm to
`a`, `Filter.IsApproximateUnit.tendsto_mul_mul`. Since an increasing approximate unit eventually
lies in the closed unit ball, the convergence `e * a → a` is uniform for `a` in a compact set,
`Filter.IsIncreasingApproximateUnit.tendstoUniformlyOn_mul_right`, and so is `a * e → a`,
`Filter.IsIncreasingApproximateUnit.tendstoUniformlyOn_mul_left`.

`TauCeti.CStarAlgebra.norm_mul_star_sub_star_sq_le` is the estimate for a positive contraction `e`
that drives the approximate-unit argument showing that closed two-sided ideals are self-adjoint:
`‖e * star a - star a‖ ^ 2 ≤ ‖star a * a - e * (star a * a)‖`. Its companion
`TauCeti.CStarAlgebra.norm_sub_mul_sq_le`, `‖a - a * e‖ ^ 2 ≤ ‖star a * a + z‖ + ‖z - z * e‖`,
drives the proof of the C⋆-identity on the quotient by a closed two-sided ideal and shows that an
increasing approximate unit of `B` mapped into `A` by `f` right-approximates every `a` with
`star a * a ∈ Set.range f`,
`Filter.IsIncreasingApproximateUnit.tendsto_mul_left_of_star_mul_self_mem_range`.
-/

public section

open Filter Topology
open scoped CStarAlgebra

namespace Filter.IsApproximateUnit

/-- Along any approximate unit of a C⋆-algebra, two-sided compression `e * a * e` converges in
norm to `a`. Neither positivity nor norm boundedness of the filter is needed, because `A` is
spanned by nonnegative elements `b = √b * √b` on which `e * (√b * √b) * e = (e * √b) * (√b * e)`.
-/
theorem tendsto_mul_mul {A : Type*} [NonUnitalCStarAlgebra A] {l : Filter A}
    (hl : l.IsApproximateUnit) (a : A) :
    Tendsto (fun e => e * a * e) l (𝓝 a) := by
  let _ := CStarAlgebra.spectralOrder A
  have _ := CStarAlgebra.spectralOrderedRing A
  have ha : a ∈ Submodule.span ℂ {x : A | 0 ≤ x} := by simp [CStarAlgebra.span_nonneg]
  induction ha using Submodule.span_induction with
  | mem b hb =>
    let s : A := cfcₙ Real.sqrt b
    have hs : s * s = b := by
      dsimp only [s]
      rw [← cfcₙ_mul ..]
      refine (cfcₙ_congr fun r hr => ?_).trans (cfcₙ_id' ℝ b)
      grind [Real.mul_self_sqrt]
    rw [← hs]
    exact ((hl.tendsto_mul_right s).mul (hl.tendsto_mul_left s)).congr fun e => by
      simp only [mul_assoc]
  | zero => simpa using tendsto_const_nhds
  | add x y _ _ hx hy =>
    refine (hx.add hy).congr fun e => ?_
    rw [mul_add, add_mul]
  | smul c x _ hx =>
    refine (hx.const_smul c).congr fun e => ?_
    rw [mul_smul_comm, smul_mul_assoc]

end Filter.IsApproximateUnit

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

/-- Any proper subfilter (subnet) of an increasing approximate unit is an increasing approximate
unit. -/
theorem mono {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] {l l' : Filter A}
    (hl : l.IsIncreasingApproximateUnit) (hle : l' ≤ l) [l'.NeBot] :
    l'.IsIncreasingApproximateUnit where
  tendsto_mul_left a := (hl.tendsto_mul_left a).mono_left hle
  tendsto_mul_right a := (hl.tendsto_mul_right a).mono_left hle
  eventually_nonneg := hl.eventually_nonneg.filter_mono hle
  eventually_norm := hl.eventually_norm.filter_mono hle

/-- Convexification of an increasing approximate unit: replacing every member of `l` by its real
convex hull yields a coarser increasing approximate unit. -/
theorem lift'_convexHull {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] {l : Filter A} (hl : l.IsIncreasingApproximateUnit) :
    (l.lift' (convexHull ℝ)).IsIncreasingApproximateUnit where
  tendsto_mul_left a := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    let L : A →ₗ[ℝ] A :=
      { toFun := (a * ·)
        map_add' := mul_add a
        map_smul' := fun r x => mul_smul_comm r a x }
    have hball : Convex ℝ {e : A | dist (a * e) a < ε} := (convex_ball a ε).linear_preimage L
    exact eventually_of_mem (mem_lift' (Metric.tendsto_nhds.mp (hl.tendsto_mul_left a) ε hε))
      fun x hx => convexHull_min subset_rfl hball hx
  tendsto_mul_right a := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    let R : A →ₗ[ℝ] A :=
      { toFun := (· * a)
        map_add' := fun x y => add_mul x y a
        map_smul' := fun r x => smul_mul_assoc r x a }
    have hball : Convex ℝ {e : A | dist (e * a) a < ε} := (convex_ball a ε).linear_preimage R
    exact eventually_of_mem (mem_lift' (Metric.tendsto_nhds.mp (hl.tendsto_mul_right a) ε hε))
      fun x hx => convexHull_min subset_rfl hball hx
  eventually_nonneg := by
    have hIci : Convex ℝ (Set.Ici (0 : A)) := fun _ hx _ hy _ _ ha hb _ =>
      add_nonneg (smul_nonneg ha hx) (smul_nonneg hb hy)
    exact eventually_of_mem (mem_lift' hl.eventually_nonneg)
      fun x hx => convexHull_min subset_rfl hIci hx
  eventually_norm := by
    refine eventually_of_mem (mem_lift' hl.closedBall_mem) fun x hx => ?_
    have hmem := convexHull_min subset_rfl (convex_closedBall (0 : A) 1) hx
    simpa [Metric.mem_closedBall, dist_zero_right] using hmem
  neBot := by
    have := hl.neBot
    exact (lift'_neBot_iff fun _ _ hst => convexHull_mono hst).mpr
      fun _ hs => (nonempty_of_mem hs).convexHull

/-- Transporting a filter along a star-algebra equivalence preserves increasing approximate units
in both directions. -/
@[simp]
theorem map_equiv_iff {A B : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
    (e : A ≃⋆ₐ[ℂ] B) {l : Filter A} :
    (l.map e).IsIncreasingApproximateUnit ↔ l.IsIncreasingApproximateUnit := by
  refine ⟨fun h => ?_, fun h => h.map e e.surjective⟩
  have hsymm := h.map e.symm e.symm.surjective
  rwa [Filter.map_map, show (e.symm : B → A) ∘ e = id from funext e.symm_apply_apply,
    Filter.map_id] at hsymm

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

end TauCeti.CStarAlgebra

namespace Filter.IsIncreasingApproximateUnit

variable {A B F : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [FunLike F B A] [NonUnitalAlgHomClass F ℂ B A] [StarHomClass F B A]

/-- Along an increasing approximate unit `l` of `B` mapped into `A` by a star-algebra homomorphism
`f`, right multiplication `a * f e` converges to `a` whenever `star a * a` lies in the range of `f`.
In particular, if `B` is a closed C⋆-subalgebra of `A` and `star a * a ∈ B`, then `a * e → a` along
any increasing approximate unit of `B`. -/
theorem tendsto_mul_left_of_star_mul_self_mem_range {l : Filter B}
    (hl : l.IsIncreasingApproximateUnit) (f : F) {a : A} (ha : star a * a ∈ Set.range f) :
    Tendsto (fun e => a * f e) l (𝓝 a) := by
  obtain ⟨b, hb⟩ := ha
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hsq : ∀ᶠ e in l, ‖a * f e - a‖ ^ 2 ≤ ‖b * e - b‖ := by
    filter_upwards [hl.eventually_nonneg, hl.eventually_norm] with e he₀ he₁
    have hfe₀ : 0 ≤ f e := map_nonneg f he₀
    have hfe₁ : ‖f e‖ ≤ 1 := (NonUnitalStarAlgHom.norm_apply_le f e).trans he₁
    have h := TauCeti.CStarAlgebra.norm_sub_mul_sq_le hfe₀ hfe₁ a (-f b)
    have hz : -f b - -f b * f e = f (b * e - b) := by
      rw [neg_mul, sub_neg_eq_add, add_comm, ← sub_eq_add_neg, ← map_mul, ← map_sub]
    rw [← hb, add_neg_cancel, norm_zero, zero_add, hz, norm_sub_rev a (a * f e)] at h
    exact h.trans (NonUnitalStarAlgHom.norm_apply_le f (b * e - b))
  have hb_lim : Tendsto (fun e => Real.sqrt ‖b * e - b‖) l (𝓝 0) := by
    simpa only [Real.sqrt_zero, Function.comp_def] using
      (Real.continuous_sqrt.tendsto 0).comp
        (tendsto_iff_norm_sub_tendsto_zero.mp (hl.tendsto_mul_left b))
  refine squeeze_zero_norm' ?_ hb_lim
  filter_upwards [hsq] with e he
  rw [Real.norm_of_nonneg (norm_nonneg _)]
  exact Real.le_sqrt_of_sq_le he

/-- Along an increasing approximate unit `l` of `B` mapped into `A` by a star-algebra homomorphism
`f`, left multiplication `f e * a` converges to `a` whenever `a * star a` lies in the range of `f`.
-/
theorem tendsto_mul_right_of_mul_star_self_mem_range {l : Filter B}
    (hl : l.IsIncreasingApproximateUnit) (f : F) {a : A} (ha : a * star a ∈ Set.range f) :
    Tendsto (fun e => f e * a) l (𝓝 a) := by
  have ha' : star (star a) * star a ∈ Set.range f := by rwa [star_star]
  have hlim := (continuous_star.tendsto (star a)).comp
    (hl.tendsto_mul_left_of_star_mul_self_mem_range f ha')
  rw [star_star] at hlim
  refine hlim.congr' ?_
  filter_upwards [hl.eventually_star_eq] with e he
  simp [star_mul, ← map_star, he]

end Filter.IsIncreasingApproximateUnit
