/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Distribution.IntegralManifold.Leaf
public import TauCeti.Geometry.Manifold.Foliation.Leaf

import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
import Mathlib.Topology.Connected.Clopen
import TauCeti.Geometry.Manifold.Distribution.IntegralManifold.Existence
import TauCeti.Geometry.Manifold.Foliation.Horizontal
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# Leaves of a foliation as maximal integral manifolds

For a foliation `F` of rank `k` of a finite-dimensional real manifold `M` with boundaryless model,
two notions of leaf are available: the curve-theoretic leaf `F.leaf x : Set M`, consisting of all
points joined to `x` by a finite chain of `C¹` curves tangent to `F`, and the global Frobenius leaf
of the involutive tangent distribution `F.distribution`, a connected injectively parametrized
`k`-dimensional integral manifold with its own intrinsic manifold topology.

This file proves that these two descriptions agree: for every `m : ℕ∞` with `1 ≤ m` at most the
regularity of `F` (and more generally whenever `F.distribution` is `C^m` of constant rank on a
`C^r` ambient manifold with `m + 1 ≤ r`), the ambient image of the `C^m` Frobenius leaf through `x`
is equal to `F.leaf x`. In particular, for a `C^m` foliation `F : Foliation I m M k` (`m : ℕ∞`),
`F.leafIntegralManifold x` equips `F.leaf x` with a canonical connected, injectively parametrized
`C^m` `IntegralManifold` structure that inherits Hausdorffness and second countability as typeclass
instances from `M`, admits unique `C^n` (`n ≤ m`) factorization for horizontal maps (`1 ≤ n`)
without `SecondCountableTopology M` and for arbitrary maps when `M` is second countable, and is
unique up to `C^m` diffeomorphism over `M` among maximal preconnected injective `C^m` integral
manifolds of `F.distribution`.

## Main definitions

* `TauCeti.Foliation.leafIntegralManifold`: the leaf of a `C^m` foliation (`m : ℕ∞`) on a
  finite-dimensional real `C^(m + 1)` manifold `M` with boundaryless model through `x`, packaged as
  a `k`-dimensional `C^m` `IntegralManifold` in the same universe as `M`.

## Main results

* `TauCeti.Foliation.range_leaf_distribution`: for any foliation `F : Foliation I n M k` and any
  valid leaf regularity `m : ℕ∞` (`1 ≤ m`) and ambient regularity `r` (`m + 1 ≤ r`), the ambient
  image of the `C^m` Frobenius leaf of `F.distribution` through `x` equals `F.leaf x`.
* `TauCeti.Foliation.leafIntegralManifold_def` and
  `TauCeti.Foliation.range_leafIntegralManifold`: unfolding `F.leafIntegralManifold x` to
  `IsInvolutiveDistribution.leaf` and identifying its ambient image with `F.leaf x`.
* `TauCeti.Foliation.mem_range_leafIntegralManifold_iff` and
  `TauCeti.Foliation.mem_range_leafIntegralManifold_self`: membership in the image of
  `F.leafIntegralManifold x`.
* `TauCeti.Foliation.connectedSpace_leafIntegralManifold`,
  `TauCeti.Foliation.map_leafIntegralManifold_injective`,
  `TauCeti.Foliation.t2Space_leafIntegralManifold`,
  `TauCeti.Foliation.secondCountableTopology_leafIntegralManifold`, and
  `TauCeti.Foliation.range_subset_leafIntegralManifold`: topological instances, injectivity, and
  maximality properties of `F.leafIntegralManifold x`.
* `TauCeti.Foliation.existsUnique_contMDiff_factor_leafIntegralManifold_of_isHorizontalMap` and
  `TauCeti.Foliation.existsUnique_contMDiff_factor_leafIntegralManifold`: unique `C^n` (`n ≤ m`)
  factorization of maps with image in `F.leaf x` through `(F.leafIntegralManifold x).carrier` for
  horizontal maps (`1 ≤ n`) without `SecondCountableTopology M`, and for all maps when `M` is
  second countable.
* `TauCeti.Foliation.range_eq_leaf_of_maximal` and
  `TauCeti.Foliation.exists_diffeomorph_leafIntegralManifold_of_maximal`: any maximal preconnected
  `C^m` integral manifold of `F.distribution` through `x` has ambient image `F.leaf x`, and when
  injectively parametrized is `C^m` diffeomorphic to `F.leafIntegralManifold x` over `M`.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, second edition (2013), Theorem 19.21 and
  Lemmas 19.22–19.23, pp. 502–505 (maximal integral manifolds and leaves of foliations).
* A. Candel, L. Conlon, *Foliations I*, AMS GSM 23 (2000), Chapter 1.
-/

public section

noncomputable section

open Set Function Filter Topology TopologicalSpace Manifold
open TauCeti.Manifold
open scoped Manifold ContDiff Topology

universe u

namespace TauCeti.Foliation

section CurveConstancy

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type u} [TopologicalSpace M] [ChartedSpace H M]

/-- Along a `C¹` curve tangent to `D` on `[0, 1]`, any coordinate map sending `D` into a
subspace `W` of `E` changes by an element of `W` across subintervals remaining in its domain. -/
private theorem curve_sub_mem_of_flatChart
    {D : ∀ x : M, Submodule ℝ (TangentSpace I x)} {γ : ℝ → M}
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Icc 0 1))
    (htan : ∀ t ∈ Icc (0 : ℝ) 1, curveVelocityWithin I γ (Icc 0 1) t ∈ D (γ t))
    {W : Submodule ℝ E} {Φ : M → E} {U : Set M} (hU : IsOpen U)
    (hΦ : MDifferentiableOn I 𝓘(ℝ, E) Φ U)
    (hΦflat : ∀ z ∈ U, (D z).map (mfderiv I 𝓘(ℝ, E) Φ z).toLinearMap ≤ W)
    {a b : ℝ} (hab : a ≤ b) (hsub : Icc a b ⊆ Icc 0 1) (hγU : ∀ u ∈ Icc a b, γ u ∈ U) :
    Φ (γ b) - Φ (γ a) ∈ W := by
  rcases eq_or_lt_of_le hab with rfl | hlt
  · simpa only [sub_self] using W.zero_mem
  have : IsClosed (W : Set E) := W.isClosed_of_finiteDimensional
  let q : E →L[ℝ] E ⧸ W := W.mkQL
  have hderiv (u : ℝ) (hu : u ∈ Icc a b) : HasDerivWithinAt (q ∘ Φ ∘ γ) 0 (Icc a b) u := by
    have hu01 : u ∈ Icc (0 : ℝ) 1 := hsub hu
    have hγu := (hasMFDerivWithinAt_curveVelocityWithin
      (hγ.mdifferentiableOn one_ne_zero u hu01)).mono hsub
    have hΦu := (hΦ (γ u) (hγU u hu)).mdifferentiableAt (hU.mem_nhds (hγU u hu))
    have hmem : mvfderiv I Φ (γ u) (curveVelocityWithin I γ (Icc 0 1) u) ∈ W := by
      rw [mvfderiv_apply_eq_mfderiv_apply]
      exact hΦflat (γ u) (hγU u hu) (Submodule.mem_map_of_mem (htan u hu01))
    have hq0 : q (mvfderiv I Φ (γ u) (curveVelocityWithin I γ (Icc 0 1) u)) = 0 :=
      (Submodule.Quotient.mk_eq_zero W).mpr hmem
    exact hq0 ▸ q.hasFDerivAt.comp_hasDerivWithinAt u (hasDerivWithinAt_comp_curve hΦu hγu)
  have hconst := constant_of_derivWithin_zero
    (fun u hu ↦ (hderiv u hu).differentiableWithinAt)
    (fun u hu ↦ (hderiv u (Ico_subset_Icc_self hu)).derivWithin
      (uniqueDiffOn_Icc hlt u (Ico_subset_Icc_self hu)))
    b (right_mem_Icc.mpr hab)
  apply (Submodule.Quotient.mk_eq_zero W).mp
  rw [← Submodule.mkQ_apply, ← Submodule.mkQL_apply, map_sub, sub_eq_zero]
  exact hconst

omit [FiniteDimensional ℝ E] in
/-- Restricting a Euclidean integral plaque to an open Euclidean ball inside its domain yields a
preconnected `C^m` integral plaque whose image is cut out inside the original plaque by an ambient
open set. -/
private theorem exists_preconnected_ball_plaque {m : ℕ∞} (hm0 : (m : ℕ∞ω) ≠ 0) {k : ℕ}
    {D : ∀ x : M, Submodule ℝ (TangentSpace I x)}
    {V : Opens (EuclideanSpace ℝ (Fin k))} (v : V) {f : V → M}
    (hemb : IsEmbedding f) (hf : IsIntegralManifold (𝓡 k) m D f) :
    ∃ (B : Opens V) (_ : PreconnectedSpace B) (U_amb : Set M),
      IsOpen U_amb ∧ f ⁻¹' U_amb = B ∧ v ∈ (B : Set V) ∧
        IsIntegralManifold (𝓡 k) m D (f ∘ (Subtype.val : B → V)) := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp V.isOpen v.1 v.2
  let B : Opens V := ⟨Subtype.val ⁻¹' Metric.ball v.1 ε,
    Metric.isOpen_ball.preimage continuous_subtype_val⟩
  let j : Metric.ball v.1 ε → B := fun z ↦ ⟨⟨z.1, hball z.2⟩, z.2⟩
  have hjcont : Continuous j :=
    Continuous.subtype_mk (Continuous.subtype_mk continuous_subtype_val _) _
  have hjsurj : Surjective j := fun ⟨⟨u, _⟩, hub⟩ ↦ ⟨⟨u, hub⟩, rfl⟩
  let _ : PreconnectedSpace (Metric.ball v.1 ε) :=
    Subtype.preconnectedSpace (convex_ball v.1 ε).isPreconnected
  have hBpre : PreconnectedSpace B := ⟨hjsurj.range_eq ▸ isPreconnected_range hjcont⟩
  have hvB : v ∈ (B : Set V) := Metric.mem_ball_self hε
  have : Nonempty B := ⟨⟨v, hvB⟩⟩
  obtain ⟨U_amb, hUopen, hfU⟩ := hemb.isInducing.isOpen_iff.mp B.isOpen
  exact ⟨B, hBpre, U_amb, hUopen, hfU, hvB, hf.comp_subtypeVal hm0⟩

/-- Near any parameter `t₀ ∈ [0, 1]`, a `C¹` curve tangent to an involutive `C^m` distribution
remains inside the image of a single preconnected `C^m` Euclidean integral plaque. -/
private theorem eventually_mem_preconnected_plaque [I.Boundaryless]
    {m : ℕ∞} (hm : 1 ≤ m) {r : ℕ∞ω} (hmr : (m : ℕ∞ω) + 1 ≤ r)
    [IsManifold I 1 M] [IsManifold I r M] {k : ℕ}
    {D : ∀ x : M, Submodule ℝ (TangentSpace I x)}
    (hinv : IsInvolutiveDistribution I D) (hD : IsContMDiffDistribution I m k D)
    {γ : ℝ → M} (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Icc 0 1))
    (htan : ∀ t ∈ Icc (0 : ℝ) 1, curveVelocityWithin I γ (Icc 0 1) t ∈ D (γ t))
    {t₀ : ℝ} (ht₀ : t₀ ∈ Icc (0 : ℝ) 1) :
    ∃ (V : Opens (EuclideanSpace ℝ (Fin k))) (B : Opens V) (_ : PreconnectedSpace B)
      (g : B → M), IsIntegralManifold (𝓡 k) m D g ∧ γ t₀ ∈ range g ∧
        ∀ᶠ t in 𝓝[Icc 0 1] t₀, γ t ∈ range g := by
  have hm0 : (m : ℕ∞ω) ≠ 0 := ne_of_gt (zero_lt_one.trans_le (by exact_mod_cast hm))
  obtain ⟨W, Φ, V, v, f, _, hxΦ, hΦflat, hfv, _, hemb, hslice, hf⟩ :=
    hinv.exists_isIntegralManifold_euclidean hm hmr hD (γ t₀)
  obtain ⟨B, hBpre, U_amb, hUopen, hfU, hvB, hg⟩ :=
    exists_preconnected_ball_plaque hm0 v hemb hf
  have hvU : γ t₀ ∈ U_amb := by
    rw [← hfv, ← mem_preimage, hfU]
    exact hvB
  obtain ⟨δ, hδpos, hδ⟩ := Metric.mem_nhdsWithin_iff.mp <|
    (hγ.continuousOn t₀ ht₀).preimage_mem_nhdsWithin
      ((hUopen.inter Φ.open_source).mem_nhds ⟨hvU, hxΦ⟩)
  refine ⟨V, B, hBpre, f ∘ Subtype.val, hg, ⟨⟨v, hvB⟩, hfv⟩, ?_⟩
  filter_upwards [Metric.mem_nhdsWithin_iff.mpr ⟨δ, hδpos, Subset.rfl⟩] with t ht
  have ht₀_mem : t₀ ∈ Metric.ball t₀ δ ∩ Icc 0 1 := ⟨Metric.mem_ball_self hδpos, ht₀⟩
  have hIcc : Icc (min t t₀) (max t t₀) ⊆ Metric.ball t₀ δ ∩ Icc 0 1 :=
    ((convex_ball t₀ δ).inter (convex_Icc 0 1)).ordConnected.out
      (min_rec' (· ∈ _) ht ht₀_mem) (max_rec' (· ∈ _) ht ht₀_mem)
  have hba : Φ (γ (max t t₀)) - Φ (γ (min t t₀)) ∈ W :=
    curve_sub_mem_of_flatChart hγ htan Φ.open_source (Φ.contMDiffOn.mdifferentiableOn hm0)
      (fun z hz ↦ (hΦflat z hz).le) min_le_max (hIcc.trans inter_subset_right)
      fun u hu ↦ (hδ (hIcc hu)).2
  have htW : Φ (γ t) - Φ (γ t₀) ∈ W := by
    rcases le_total t t₀ with hle | hle
    · simpa only [min_eq_left hle, max_eq_right hle, neg_sub] using W.neg_mem hba
    · simpa only [min_eq_right hle, max_eq_left hle] using hba
  obtain ⟨u, hu⟩ : γ t ∈ range f :=
    (isSliceChart_iff.mp hslice (γ t) (hδ ht).2).mpr
      ⟨⟨Φ (γ t) - Φ (γ t₀), htW⟩, by simp [PartialDiffeomorph.toFun'_toOpenPartialHomeomorph]⟩
  have huB : u ∈ (B : Set V) := by
    rw [← hfU, mem_preimage, hu]
    exact (hδ ht).1
  exact ⟨⟨u, huB⟩, hu⟩

end CurveConstancy

section GeneralRegularity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  {n : ℕ∞ω} {k : ℕ} [IsManifold I (n + 1) M]

/-- For any foliation `F : Foliation I n M k` on a finite-dimensional real manifold `M` with
boundaryless model, and any leaf regularity `m : ℕ∞` (`1 ≤ m`) and ambient regularity `r`
(`m + 1 ≤ r`) for which `F.distribution` is `C^m` of constant rank, the ambient image of the `C^m`
Frobenius leaf of `F.distribution` through `x` equals the tangent-curve leaf `F.leaf x`. -/
theorem range_leaf_distribution (F : Foliation I n M k) {m : ℕ∞} (hm : 1 ≤ m)
    {r : ℕ∞ω} [IsManifold I r M] (hmr : (m : ℕ∞ω) + 1 ≤ r) {k' : ℕ}
    (hD : letI : IsManifold I 1 M := IsManifold.of_le (n := n + 1) le_add_self
      IsContMDiffDistribution I m k' F.distribution)
    (x : M) :
    letI : IsManifold I 1 M := IsManifold.of_le (n := n + 1) le_add_self
    range (F.isInvolutiveDistribution.leaf hm hmr hD x).map = F.leaf x := by
  let _ : IsManifold I 1 M := IsManifold.of_le (n := n + 1) le_add_self
  have hm1 : (1 : ℕ∞ω) ≤ m := WithTop.coe_le_coe.mpr hm
  refine Subset.antisymm ?_ ?_
  · obtain ⟨z₀, hz₀⟩ := F.isInvolutiveDistribution.mem_range_leaf_self hm hmr hD x
    let N := F.isInvolutiveDistribution.leaf hm hmr hD x
    let _ : IsManifold (𝓡 k') 1 N.carrier := .of_le hm1
    exact (F.range_subset_leaf_of_isHorizontalMap
      (isHorizontalMap_iff_range_mfderiv_le.mpr fun z ↦ (N.range_mfderiv z).le)
      (N.contMDiff_map.of_le hm1) z₀).trans_eq (congrArg F.leaf hz₀)
  · have hr : Equivalence fun y z : M ↦
        z ∈ range (F.isInvolutiveDistribution.leaf hm hmr hD y).map :=
      ⟨fun y ↦ F.isInvolutiveDistribution.mem_range_leaf_self hm hmr hD y,
       fun hyz ↦ (F.isInvolutiveDistribution.mem_range_leaf_comm hm hmr hD).mp hyz,
       fun hyz hzw ↦ F.isInvolutiveDistribution.range_leaf_eq_of_mem hm hmr hD hyz ▸ hzw⟩
    intro z hz
    refine F.sameLeaf_le hr (fun y z hyz ↦ ?_) x z (F.mem_leaf.mp hz)
    obtain ⟨γ, hγ, htan, rfl, rfl⟩ := F.joinedByTangentCurve_iff.mp hyz
    refine (convex_Icc (0 : ℝ) 1).isPreconnected.induction₂
      (fun t₁ t₂ ↦ γ t₂ ∈ range (F.isInvolutiveDistribution.leaf hm hmr hD (γ t₁)).map)
      (fun t₀ ht₀ ↦ ?_) (fun _ _ _ _ _ _ ↦ hr.trans) (fun _ _ _ _ ↦ hr.symm)
      (left_mem_Icc.mpr zero_le_one) (right_mem_Icc.mpr zero_le_one)
    obtain ⟨V, B, hBpre, g, hg, ht₀g, hfg⟩ :=
      eventually_mem_preconnected_plaque hm hmr F.isInvolutiveDistribution hD hγ htan ht₀
    have hsub : range g ⊆ range (F.isInvolutiveDistribution.leaf hm hmr hD (γ t₀)).map :=
      F.isInvolutiveDistribution.range_subset_leaf_of_isIntegralManifold hm hmr hD hm1 hg
        ⟨γ t₀, ht₀g, F.isInvolutiveDistribution.mem_range_leaf_self hm hmr hD (γ t₀)⟩
    exact hfg.mono fun _ ht ↦ hsub ht

end GeneralRegularity

section PackagedLeaf

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  {m : ℕ∞} {k : ℕ} [IsManifold I ((m : ℕ∞ω) + 1) M]

/-- The leaf of a `C^m` foliation `F` (`m : ℕ∞`) on a finite-dimensional real `C^(m + 1)` manifold
`M` with boundaryless model through `x`, packaged as a connected, injectively parametrized
`k`-dimensional `C^m` `IntegralManifold` in the same universe as `M`. -/
def leafIntegralManifold (F : Foliation I m M k) (x : M) :
    IntegralManifold.{u, u} (I := I) m F.distribution k :=
  let _ : IsManifold I 1 M := IsManifold.of_le (n := (m : ℕ∞ω) + 1) le_add_self
  F.isInvolutiveDistribution.leaf (WithTop.coe_le_coe.mp F.one_le) le_rfl
    F.isContMDiffDistribution x

/-- `F.leafIntegralManifold x` is the canonical global `C^m` Frobenius leaf of `F.distribution`
through `x`. -/
theorem leafIntegralManifold_def (F : Foliation I m M k) (x : M) :
    letI : IsManifold I 1 M := IsManifold.of_le (n := (m : ℕ∞ω) + 1) le_add_self
    F.leafIntegralManifold x =
      F.isInvolutiveDistribution.leaf (WithTop.coe_le_coe.mp F.one_le) le_rfl
        F.isContMDiffDistribution x :=
  (rfl)

/-- The ambient image of `F.leafIntegralManifold x` is the curve-defined leaf `F.leaf x`. -/
@[simp]
theorem range_leafIntegralManifold (F : Foliation I m M k) (x : M) :
    range (F.leafIntegralManifold x).map = F.leaf x :=
  F.range_leaf_distribution (WithTop.coe_le_coe.mp F.one_le) le_rfl F.isContMDiffDistribution x

/-- A point belongs to the ambient image of `F.leafIntegralManifold x` if and only if it lies on
the same leaf of `F` as `x`. -/
theorem mem_range_leafIntegralManifold_iff (F : Foliation I m M k) {x y : M} :
    y ∈ range (F.leafIntegralManifold x).map ↔ F.SameLeaf x y := by
  rw [F.range_leafIntegralManifold x, mem_leaf]

/-- Every point lies in the ambient image of `F.leafIntegralManifold` through it. -/
theorem mem_range_leafIntegralManifold_self (F : Foliation I m M k) (x : M) :
    x ∈ range (F.leafIntegralManifold x).map :=
  (F.mem_range_leafIntegralManifold_iff).mpr (SameLeaf.refl F x)

/-- The intrinsic carrier of `F.leafIntegralManifold x` is connected. -/
instance connectedSpace_leafIntegralManifold (F : Foliation I m M k) (x : M) :
    ConnectedSpace (F.leafIntegralManifold x).carrier := by
  let _ : IsManifold I 1 M := IsManifold.of_le (n := (m : ℕ∞ω) + 1) le_add_self
  exact F.isInvolutiveDistribution.connectedSpace_leaf (WithTop.coe_le_coe.mp F.one_le) le_rfl
    F.isContMDiffDistribution x

/-- The ambient parametrization of `F.leafIntegralManifold x` is injective. -/
theorem map_leafIntegralManifold_injective (F : Foliation I m M k) (x : M) :
    Injective (F.leafIntegralManifold x).map := by
  let _ : IsManifold I 1 M := IsManifold.of_le (n := (m : ℕ∞ω) + 1) le_add_self
  exact F.isInvolutiveDistribution.map_leaf_injective (WithTop.coe_le_coe.mp F.one_le) le_rfl
    F.isContMDiffDistribution x

/-- When the ambient manifold is Hausdorff, the intrinsic carrier of `F.leafIntegralManifold x` is
Hausdorff. -/
instance t2Space_leafIntegralManifold [T2Space M] (F : Foliation I m M k) (x : M) :
    T2Space (F.leafIntegralManifold x).carrier := by
  let _ : IsManifold I 1 M := IsManifold.of_le (n := (m : ℕ∞ω) + 1) le_add_self
  exact F.isInvolutiveDistribution.t2Space_leaf (WithTop.coe_le_coe.mp F.one_le) le_rfl
    F.isContMDiffDistribution x

/-- When the ambient manifold is second countable, the intrinsic carrier of
`F.leafIntegralManifold x` is second countable. -/
instance secondCountableTopology_leafIntegralManifold [SecondCountableTopology M]
    (F : Foliation I m M k) (x : M) :
    SecondCountableTopology (F.leafIntegralManifold x).carrier := by
  let _ : IsManifold I 1 M := IsManifold.of_le (n := (m : ℕ∞ω) + 1) le_add_self
  exact F.isInvolutiveDistribution.secondCountableTopology_leaf (WithTop.coe_le_coe.mp F.one_le)
    le_rfl F.isContMDiffDistribution x

/-- Every preconnected packaged integral manifold of `F.distribution` of regularity at least `C¹`
whose image meets `F.leafIntegralManifold x` has its entire image contained in it. -/
theorem range_subset_leafIntegralManifold (F : Foliation I m M k) {x : M}
    {m' : ℕ∞ω} (hm' : 1 ≤ m') (N' : IntegralManifold (I := I) m' F.distribution k)
    [PreconnectedSpace N'.carrier]
    (hmeet : (range N'.map ∩ range (F.leafIntegralManifold x).map).Nonempty) :
    range N'.map ⊆ range (F.leafIntegralManifold x).map := by
  let _ : IsManifold I 1 M := IsManifold.of_le (n := (m : ℕ∞ω) + 1) le_add_self
  exact F.isInvolutiveDistribution.range_subset_leaf (WithTop.coe_le_coe.mp F.one_le) le_rfl
    F.isContMDiffDistribution hm' N' hmeet

/-- For a `C^m` foliation `F` (`m : ℕ∞`) on a finite-dimensional real `C^(m + 1)` manifold `M` with
boundaryless model, every horizontal `C^n` map (`1 ≤ n`, `n ≤ m`) from a `C¹` manifold into
`F.leaf x` factors uniquely as a `C^n` map through `(F.leafIntegralManifold x).carrier`, without
assuming second countability of `M`. -/
theorem existsUnique_contMDiff_factor_leafIntegralManifold_of_isHorizontalMap
    (F : Foliation I m M k) {x : M}
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {A : Type*} [TopologicalSpace A] {K : ModelWithCorners ℝ V A}
    {P : Type*} [TopologicalSpace P] [ChartedSpace A P] [IsManifold K 1 P]
    {n : ℕ∞ω} (hn : 1 ≤ n) (hnm : n ≤ m)
    {g : P → M} (hg_hor : IsHorizontalMap K F.distribution g) (hg : ContMDiff K I n g)
    (hr : range g ⊆ F.leaf x) :
    ∃! h : P → (F.leafIntegralManifold x).carrier,
      ContMDiff K (𝓡 k) n h ∧ (F.leafIntegralManifold x).map ∘ h = g := by
  let _ : IsManifold I 1 M := IsManifold.of_le (n := (m : ℕ∞ω) + 1) le_add_self
  rw [← F.range_leafIntegralManifold x] at hr
  exact F.isInvolutiveDistribution.existsUnique_contMDiff_factor_leaf_of_isHorizontalMap
    (WithTop.coe_le_coe.mp F.one_le) le_rfl F.isContMDiffDistribution hn hnm hg_hor hg hr

/-- Over a second-countable finite-dimensional real `C^(m + 1)` manifold `M` with boundaryless
model, every `C^n` map (`n ≤ m`) into `F.leaf x` for a `C^m` foliation `F` (`m : ℕ∞`) factors
uniquely as a `C^n` map through `(F.leafIntegralManifold x).carrier`. -/
theorem existsUnique_contMDiff_factor_leafIntegralManifold [SecondCountableTopology M]
    (F : Foliation I m M k) {x : M}
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {A : Type*} [TopologicalSpace A] {K : ModelWithCorners ℝ V A}
    {P : Type*} [TopologicalSpace P] [ChartedSpace A P]
    {n : ℕ∞ω} (hnm : n ≤ m)
    {g : P → M} (hg : ContMDiff K I n g) (hr : range g ⊆ F.leaf x) :
    ∃! h : P → (F.leafIntegralManifold x).carrier,
      ContMDiff K (𝓡 k) n h ∧ (F.leafIntegralManifold x).map ∘ h = g := by
  let _ : IsManifold I 1 M := IsManifold.of_le (n := (m : ℕ∞ω) + 1) le_add_self
  rw [← F.range_leafIntegralManifold x] at hr
  exact F.isInvolutiveDistribution.existsUnique_contMDiff_factor_leaf
    (WithTop.coe_le_coe.mp F.one_le) le_rfl F.isContMDiffDistribution hnm hg hr

/-- Whenever `y ∈ F.leaf x`, the intrinsic leaf carriers `(F.leafIntegralManifold y).carrier` and
`(F.leafIntegralManifold x).carrier` are `C^m` diffeomorphic over `M`. -/
theorem exists_diffeomorph_leafIntegralManifold_of_mem_leaf (F : Foliation I m M k) {x y : M}
    (hy : y ∈ F.leaf x) :
    ∃ e : Diffeomorph (𝓡 k) (𝓡 k)
        (F.leafIntegralManifold y).carrier (F.leafIntegralManifold x).carrier m,
      ∀ z, (F.leafIntegralManifold x).map (e z) = (F.leafIntegralManifold y).map z := by
  let _ : IsManifold I 1 M := IsManifold.of_le (n := (m : ℕ∞ω) + 1) le_add_self
  rw [← F.range_leafIntegralManifold x] at hy
  exact F.isInvolutiveDistribution.exists_diffeomorph_leaf_of_mem (WithTop.coe_le_coe.mp F.one_le)
    le_rfl F.isContMDiffDistribution hy

/-- For a `C^m` foliation `F` (`m : ℕ∞`) on a finite-dimensional real `C^(m + 1)` manifold `M` with
boundaryless model, any preconnected `C^m` integral manifold of `F.distribution` through `x` that
contains the image of every connected `C^m` integral manifold meeting it has ambient image
`F.leaf x`. -/
theorem range_eq_leaf_of_maximal (F : Foliation I m M k) {x : M}
    (L : IntegralManifold (I := I) m F.distribution k) [PreconnectedSpace L.carrier]
    (hx : x ∈ range L.map)
    (hmax : ∀ N' : IntegralManifold.{u, u} (I := I) m F.distribution k, ConnectedSpace N'.carrier →
      (range N'.map ∩ range L.map).Nonempty → range N'.map ⊆ range L.map) :
    range L.map = F.leaf x := by
  let _ : IsManifold I 1 M := IsManifold.of_le (n := (m : ℕ∞ω) + 1) le_add_self
  exact (F.isInvolutiveDistribution.range_eq_range_leaf_of_maximal
    (WithTop.coe_le_coe.mp F.one_le) le_rfl F.isContMDiffDistribution L hx hmax).trans
    (F.range_leafIntegralManifold x)

/-- For a `C^m` foliation `F` (`m : ℕ∞`) on a finite-dimensional real `C^(m + 1)` manifold `M` with
boundaryless model, any preconnected injectively parametrized `C^m` integral manifold of
`F.distribution` through `x` that contains the image of every connected `C^m` integral manifold
meeting it is `C^m` diffeomorphic over `M` to `F.leafIntegralManifold x`. -/
theorem exists_diffeomorph_leafIntegralManifold_of_maximal (F : Foliation I m M k) {x : M}
    (L : IntegralManifold (I := I) m F.distribution k) [PreconnectedSpace L.carrier]
    (hinj : Injective L.map) (hx : x ∈ range L.map)
    (hmax : ∀ N' : IntegralManifold.{u, u} (I := I) m F.distribution k, ConnectedSpace N'.carrier →
      (range N'.map ∩ range L.map).Nonempty → range N'.map ⊆ range L.map) :
    ∃ e : Diffeomorph (𝓡 k) (𝓡 k) L.carrier (F.leafIntegralManifold x).carrier m,
      ∀ z, (F.leafIntegralManifold x).map (e z) = L.map z := by
  let _ : IsManifold I 1 M := IsManifold.of_le (n := (m : ℕ∞ω) + 1) le_add_self
  exact F.isInvolutiveDistribution.exists_diffeomorph_leaf_of_maximal
    (WithTop.coe_le_coe.mp F.one_le) le_rfl F.isContMDiffDistribution L hinj hx hmax

end PackagedLeaf

end TauCeti.Foliation
