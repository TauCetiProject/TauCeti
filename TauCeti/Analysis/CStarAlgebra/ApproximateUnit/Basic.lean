/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.ApproximateUnit
public import TauCeti.Analysis.Normed.Ring.ApproximateUnit
public import TauCeti.Topology.ApproximateUnit
import Mathlib.Algebra.Order.Interval.Set.Group
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Mathlib.Analysis.Normed.Group.BallSphere
import Mathlib.Order.Filter.Lift

/-!
# Increasing approximate units: subfilters, convexification, transport, and uniform convergence

This file develops general operations on increasing approximate units
(`Filter.IsIncreasingApproximateUnit`) and the canonical approximate unit
(`CStarAlgebra.approximateUnit`) of a possibly nonunital C⋆-algebra:

* **Subfilters and subnets:** any proper subfilter of an increasing approximate unit is again an
  increasing approximate unit (`Filter.IsIncreasingApproximateUnit.mono`). In particular,
  intersecting `CStarAlgebra.isBasis_nonneg_sections A` with the *open* unit ball rather than the
  closed unit ball gives a proper subfilter `CStarAlgebra.strictApproximateUnit A` along which
  `‖e‖ < 1` holds eventually (`CStarAlgebra.increasingStrictApproximateUnit`).
* **Convexification:** replacing every filter set by its real convex hull preserves increasing
  approximate units (`Filter.IsIncreasingApproximateUnit.lift'_convexHull`), while the canonical
  filters `CStarAlgebra.approximateUnit A` and `CStarAlgebra.strictApproximateUnit A` already have
  bases of convex sets and are fixed by `lift' (convexHull ℝ)`
  (`CStarAlgebra.lift'_convexHull_approximateUnit`,
  `CStarAlgebra.lift'_convexHull_strictApproximateUnit`).
* **Uniform convergence on compact sets:** since an increasing approximate unit eventually lies in
  the closed unit ball, `e * a → a` and `a * e → a` uniformly for `a` in any compact set
  (`Filter.IsIncreasingApproximateUnit.tendstoUniformlyOn_mul_right`,
  `Filter.IsIncreasingApproximateUnit.tendstoUniformlyOn_mul_left`).
* **Transport along homomorphisms:** a star-algebra homomorphism between C⋆-algebras is positive
  and contractive, so pushing forward an increasing approximate unit along any star homomorphism
  with dense range (in particular, any surjective one) yields an increasing approximate unit of the
  target (`Filter.IsIncreasingApproximateUnit.map_of_denseRange`,
  `Filter.IsIncreasingApproximateUnit.map`), and star-algebra equivalences preserve increasing
  approximate units (`Filter.IsIncreasingApproximateUnit.map_equiv_iff`).
* **Norm estimates for ideals and quotients:** `TauCeti.CStarAlgebra.norm_mul_star_sub_star_sq_le`
  and `TauCeti.CStarAlgebra.norm_sub_mul_sq_le` bound `‖e * star a - star a‖ ^ 2` and
  `‖a - a * e‖ ^ 2` for a positive contraction `e` via the unitization `A⁺¹`.

## References

* Bruce Blackadar, *Operator Algebras: Theory of C*-Algebras and von Neumann Algebras*,
  II.4.1–II.4.2.
* Gert K. Pedersen, *C*-Algebras and their Automorphism Groups*, Section 1.4.
-/

public section

open Filter Set Topology
open scoped CStarAlgebra

/-- Every filter `l` is finer than `l.lift' (convexHull 𝕜)`, since each set is contained in its
`𝕜`-convex hull. -/
theorem Filter.le_lift'_convexHull (𝕜 : Type*) {E : Type*} [Semiring 𝕜] [PartialOrder 𝕜]
    [AddCommMonoid E] [Module 𝕜 E] (l : Filter E) : l ≤ l.lift' (convexHull 𝕜) :=
  le_lift'.2 fun _ h => mem_of_superset h (subset_convexHull 𝕜 _)

namespace Filter.IsIncreasingApproximateUnit

section Subfilter

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A]

/-- Any proper subfilter (in particular, any subnet) of an increasing approximate unit is an
increasing approximate unit. -/
theorem mono {l l' : Filter A} (hl : l.IsIncreasingApproximateUnit) (hle : l' ≤ l) [l'.NeBot] :
    l'.IsIncreasingApproximateUnit where
  toIsApproximateUnit := hl.toIsApproximateUnit.of_le hle
  eventually_nonneg := hl.eventually_nonneg.filter_mono hle
  eventually_norm := hl.eventually_norm.filter_mono hle

end Subfilter

section Convex

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- **Convexification of an increasing approximate unit.** Replacing each set of an increasing
approximate unit `l` by its real convex hull produces a coarser filter `l.lift' (convexHull ℝ)` with
a basis of convex sets that is still an increasing approximate unit. -/
theorem lift'_convexHull {l : Filter A} (hl : l.IsIncreasingApproximateUnit) :
    (l.lift' (convexHull ℝ)).IsIncreasingApproximateUnit := by
  have : (l.lift' (convexHull ℝ)).NeBot := hl.neBot.mono (l.le_lift'_convexHull ℝ)
  have hmem_of_convex {s : Set A} (hs : Convex ℝ s) (hsl : s ∈ l) :
      s ∈ l.lift' (convexHull ℝ) :=
    hs.convexHull_eq ▸ mem_lift' hsl
  refine
    { tendsto_mul_left := fun a => Metric.tendsto_nhds.2 fun ε hε => hmem_of_convex ?_ ?_
      tendsto_mul_right := fun a => Metric.tendsto_nhds.2 fun ε hε => hmem_of_convex ?_ ?_
      eventually_nonneg := hmem_of_convex ?_ hl.eventually_nonneg
      eventually_norm := mem_of_superset
        (hmem_of_convex (convex_closedBall (0 : A) 1) hl.closedBall_mem)
        fun x hx => by simpa using hx }
  · intro x hx y hy u v hu hv huv
    simp only [mem_ofPred_eq, dist_eq_norm] at hx hy ⊢
    have hlin : a * (u • x + v • y) - a = u • (a * x - a) + v • (a * y - a) := calc
      a * (u • x + v • y) - a = (u • (a * x) + v • (a * y)) - (u • a + v • a) := by
        rw [mul_add, mul_smul_comm, mul_smul_comm, ← add_smul, huv, one_smul]
      _ = u • (a * x - a) + v • (a * y - a) := by
        simp only [smul_sub]
        abel
    rw [hlin]
    calc
      ‖u • (a * x - a) + v • (a * y - a)‖ ≤ u * ‖a * x - a‖ + v * ‖a * y - a‖ :=
        (norm_add_le _ _).trans <| by
          simp only [norm_smul, Real.norm_of_nonneg hu, Real.norm_of_nonneg hv, le_rfl]
      _ < u * ε + v * ε := by
        rcases hu.eq_or_lt with rfl | hu'
        · simp [by simpa using huv, hy]
        · exact add_lt_add_of_lt_of_le (mul_lt_mul_of_pos_left hx hu')
            (mul_le_mul_of_nonneg_left hy.le hv)
      _ = ε := by rw [← add_mul, huv, one_mul]
  · exact Metric.tendsto_nhds.1 (hl.tendsto_mul_left a) ε hε
  · intro x hx y hy u v hu hv huv
    simp only [mem_ofPred_eq, dist_eq_norm] at hx hy ⊢
    have hlin : (u • x + v • y) * a - a = u • (x * a - a) + v • (y * a - a) := calc
      (u • x + v • y) * a - a = (u • (x * a) + v • (y * a)) - (u • a + v • a) := by
        rw [add_mul, smul_mul_assoc, smul_mul_assoc, ← add_smul, huv, one_smul]
      _ = u • (x * a - a) + v • (y * a - a) := by
        simp only [smul_sub]
        abel
    rw [hlin]
    calc
      ‖u • (x * a - a) + v • (y * a - a)‖ ≤ u * ‖x * a - a‖ + v * ‖y * a - a‖ :=
        (norm_add_le _ _).trans <| by
          simp only [norm_smul, Real.norm_of_nonneg hu, Real.norm_of_nonneg hv, le_rfl]
      _ < u * ε + v * ε := by
        rcases hu.eq_or_lt with rfl | hu'
        · simp [by simpa using huv, hy]
        · exact add_lt_add_of_lt_of_le (mul_lt_mul_of_pos_left hx hu')
            (mul_le_mul_of_nonneg_left hy.le hv)
      _ = ε := by rw [← add_mul, huv, one_mul]
  · exact Metric.tendsto_nhds.1 (hl.tendsto_mul_right a) ε hε
  · intro x hx y hy u v hu hv _
    exact add_nonneg (smul_nonneg hu hx) (smul_nonneg hv hy)

end Convex

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

/-- The image of an increasing approximate unit under a star-algebra homomorphism of C⋆-algebras
with dense range is an increasing approximate unit. -/
theorem map_of_denseRange {l : Filter A} (hl : l.IsIncreasingApproximateUnit) (f : F)
    (hd : DenseRange f) : (l.map f).IsIncreasingApproximateUnit where
  toIsApproximateUnit := hl.toIsApproximateUnit.map_of_denseRange f (map_continuous f) hd
    (hl.eventually_norm.mono fun a ha => (NonUnitalStarAlgHom.norm_apply_le f a).trans ha)
  eventually_nonneg := eventually_map.mpr <| hl.eventually_nonneg.mono fun _ hx => map_nonneg f hx
  eventually_norm := eventually_map.mpr <| hl.eventually_norm.mono fun a ha =>
    (NonUnitalStarAlgHom.norm_apply_le f a).trans ha

/-- The image of an increasing approximate unit under a surjective star-algebra homomorphism of
C⋆-algebras is an increasing approximate unit. -/
theorem map {l : Filter A} (hl : l.IsIncreasingApproximateUnit) (f : F)
    (hf : Function.Surjective f) : (l.map f).IsIncreasingApproximateUnit :=
  hl.map_of_denseRange f hf.denseRange

/-- Star-algebra equivalences of C⋆-algebras preserve increasing approximate units. -/
@[simp]
theorem map_equiv_iff {l : Filter A} (e : A ≃⋆ₐ[ℂ] B) :
    (l.map e).IsIncreasingApproximateUnit ↔ l.IsIncreasingApproximateUnit := by
  refine ⟨fun h => ?_, fun h => h.map e e.surjective⟩
  have hinv := h.map e.symm e.symm.surjective
  rwa [Filter.map_map, show (⇑e.symm ∘ ⇑e) = id from funext e.symm_apply_apply,
    Filter.map_id] at hinv

end Map

end Filter.IsIncreasingApproximateUnit

namespace CStarAlgebra

section ConvexSections

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- Every upper section `{x : A | a ≤ x} ∩ Metric.closedBall 0 1` in the canonical approximate-unit
basis is real-convex. -/
theorem convex_Ici_inter_closedBall (a : A) :
    Convex ℝ ({x : A | a ≤ x} ∩ Metric.closedBall 0 1) := by
  refine Convex.inter ?_ (convex_closedBall 0 1)
  intro x hx y hy u v hu hv huv
  calc
    a = u • a + v • a := by rw [← add_smul, huv, one_smul]
    _ ≤ u • x + v • y := add_le_add (smul_le_smul_of_nonneg_left hx hu)
        (smul_le_smul_of_nonneg_left hy hv)

/-- Every strict upper section `{x : A | a ≤ x} ∩ Metric.ball 0 1` is real-convex. -/
theorem convex_Ici_inter_ball (a : A) :
    Convex ℝ ({x : A | a ≤ x} ∩ Metric.ball 0 1) := by
  refine Convex.inter ?_ (convex_ball 0 1)
  intro x hx y hy u v hu hv huv
  calc
    a = u • a + v • a := by rw [← add_smul, huv, one_smul]
    _ ≤ u • x + v • y := add_le_add (smul_le_smul_of_nonneg_left hx hu)
        (smul_le_smul_of_nonneg_left hy hv)

variable (A)

/-- The **strict canonical approximate unit** of a C⋆-algebra `A`: the filter generated by the
convex strict-ball upper sections `{x : A | a ≤ x} ∩ Metric.ball 0 1` for `0 ≤ a` with `‖a‖ < 1`.
It refines `CStarAlgebra.approximateUnit A` while ensuring `‖e‖ < 1` eventually. -/
def strictApproximateUnit : Filter A :=
  (isBasis_nonneg_sections A).filter ⊓ 𝓟 (Metric.ball 0 1)

/-- `CStarAlgebra.strictApproximateUnit A` has a basis of convex sets
`{x : A | a ≤ x} ∩ Metric.ball 0 1` indexed by `0 ≤ a` with `‖a‖ < 1`. -/
theorem hasBasis_strictApproximateUnit :
    (strictApproximateUnit A).HasBasis (fun x : A ↦ 0 ≤ x ∧ ‖x‖ < 1)
      ({x | · ≤ x} ∩ Metric.ball 0 1) :=
  (isBasis_nonneg_sections A).hasBasis.inf_principal (Metric.ball 0 1)

/-- `CStarAlgebra.strictApproximateUnit A` refines `CStarAlgebra.approximateUnit A`. -/
theorem strictApproximateUnit_le_approximateUnit :
    strictApproximateUnit A ≤ approximateUnit A :=
  inf_le_inf_left _ (principal_mono.2 Metric.ball_subset_closedBall)

/-- Along `CStarAlgebra.strictApproximateUnit A`, elements have norm strictly less than `1`. -/
theorem eventually_norm_lt_one_strictApproximateUnit :
    ∀ᶠ x in strictApproximateUnit A, ‖x‖ < 1 :=
  .filter_mono inf_le_right <| by simp

/-- The strict canonical approximate unit of a C⋆-algebra is a proper filter. -/
instance instNeBotStrictApproximateUnit : (strictApproximateUnit A).NeBot :=
  (hasBasis_strictApproximateUnit A).neBot_iff.mpr fun {x} hx =>
    ⟨x, le_rfl, by simpa using hx.2⟩

/-- `CStarAlgebra.strictApproximateUnit A` is an increasing approximate unit. -/
theorem increasingStrictApproximateUnit :
    (strictApproximateUnit A).IsIncreasingApproximateUnit :=
  (increasingApproximateUnit A).mono (strictApproximateUnit_le_approximateUnit A)

/-- Because its canonical basis sets are already convex, `CStarAlgebra.approximateUnit A` is fixed
by `lift' (convexHull ℝ)`. -/
@[simp]
theorem lift'_convexHull_approximateUnit :
    (approximateUnit A).lift' (convexHull ℝ) = approximateUnit A := by
  refine le_antisymm ?_ ((approximateUnit A).le_lift'_convexHull ℝ)
  rw [(hasBasis_approximateUnit A).ge_iff]
  intro a ha
  exact (convex_Ici_inter_closedBall a).convexHull_eq ▸
    mem_lift' ((hasBasis_approximateUnit A).mem_of_mem ha)

/-- Because its canonical basis sets are already convex, `CStarAlgebra.strictApproximateUnit A` is
fixed by `lift' (convexHull ℝ)`. -/
@[simp]
theorem lift'_convexHull_strictApproximateUnit :
    (strictApproximateUnit A).lift' (convexHull ℝ) = strictApproximateUnit A := by
  refine le_antisymm ?_ ((strictApproximateUnit A).le_lift'_convexHull ℝ)
  rw [(hasBasis_strictApproximateUnit A).ge_iff]
  intro a ha
  exact (convex_Ici_inter_ball a).convexHull_eq ▸
    mem_lift' ((hasBasis_strictApproximateUnit A).mem_of_mem ha)

end ConvexSections

end CStarAlgebra

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
