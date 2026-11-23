/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Distribution.IntegralManifold.Leaf
public import TauCeti.Geometry.Manifold.Foliation.Leaf

import Mathlib.Geometry.Manifold.Instances.Icc
import TauCeti.Geometry.Manifold.Foliation.Horizontal

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
unique up to `C^m` diffeomorphism over `M` among inclusion-maximal preconnected injective `C^m`
integral manifolds of `F.distribution`.

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
  `TauCeti.Foliation.exists_diffeomorph_leafIntegralManifold_of_maximal`: any inclusion-maximal
  preconnected `C^m` integral manifold of `F.distribution` through `x` has ambient image `F.leaf x`,
  and when injectively parametrized is `C^m` diffeomorphic to `F.leafIntegralManifold x` over `M`.

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
    have : Fact ((0 : ℝ) < 1) := ⟨zero_lt_one⟩
    let _ : PreconnectedSpace (Icc (0 : ℝ) 1) := Subtype.preconnectedSpace isPreconnected_Icc
    let g : Icc (0 : ℝ) 1 → M := γ ∘ Subtype.val
    have hg_diff : MDifferentiable (𝓡∂ 1) I g :=
      (hγ.comp_contMDiff (contMDiff_subtypeVal_Icc (x := 0) (y := 1) (n := 1))
        Subtype.prop).mdifferentiable one_ne_zero
    have hg_hor : IsHorizontalMap (𝓡∂ 1) F.distribution g := by
      refine isHorizontalMap_iff.mpr fun u v ↦ ?_
      have hsub := ((contMDiff_subtypeVal_Icc (x := 0) (y := 1) (n := 1) u).mdifferentiableAt
        one_ne_zero).hasMFDerivAt
      have hγu := hasMFDerivWithinAt_curveVelocityWithin
        (hγ.mdifferentiableOn one_ne_zero u.val u.property)
      have hcomp := hasMFDerivWithinAt_univ.mp <|
        hγu.comp u hsub.hasMFDerivWithinAt fun z _ ↦ z.property
      exact DFunLike.congr_fun hcomp.mfderiv v ▸ Submodule.smul_mem _ _ (htan u.val u.property)
    have hsub : range g ⊆ range (F.isInvolutiveDistribution.leaf hm hmr hD (γ 0)).map :=
      F.isInvolutiveDistribution.range_subset_leaf_of_isHorizontalMap hm hmr hD hg_hor hg_diff
        ⟨γ 0, ⟨⟨0, left_mem_Icc.mpr zero_le_one⟩, rfl⟩,
          F.isInvolutiveDistribution.mem_range_leaf_self hm hmr hD (γ 0)⟩
    exact hsub ⟨⟨1, right_mem_Icc.mpr zero_le_one⟩, rfl⟩

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
boundaryless model, any preconnected `C^m` integral manifold of `F.distribution` through `x` whose
ambient image is inclusion-maximal among connected injectively parametrized `C^m` integral manifolds
has ambient image `F.leaf x`. -/
theorem range_eq_leaf_of_maximal (F : Foliation I m M k) {x : M}
    (L : IntegralManifold (I := I) m F.distribution k) [PreconnectedSpace L.carrier]
    (hx : x ∈ range L.map)
    (hmax : ∀ N' : IntegralManifold.{u, u} (I := I) m F.distribution k, ConnectedSpace N'.carrier →
      Injective N'.map → range L.map ⊆ range N'.map → range N'.map ⊆ range L.map) :
    range L.map = F.leaf x := by
  let _ : IsManifold I 1 M := IsManifold.of_le (n := (m : ℕ∞ω) + 1) le_add_self
  exact (F.isInvolutiveDistribution.range_eq_range_leaf_of_maximal
    (WithTop.coe_le_coe.mp F.one_le) le_rfl F.isContMDiffDistribution L hx hmax).trans
    (F.range_leafIntegralManifold x)

/-- For a `C^m` foliation `F` (`m : ℕ∞`) on a finite-dimensional real `C^(m + 1)` manifold `M` with
boundaryless model, any preconnected injectively parametrized `C^m` integral manifold of
`F.distribution` through `x` whose ambient image is inclusion-maximal among connected injectively
parametrized `C^m` integral manifolds is `C^m` diffeomorphic over `M` to `F.leafIntegralManifold x`.
-/
theorem exists_diffeomorph_leafIntegralManifold_of_maximal (F : Foliation I m M k) {x : M}
    (L : IntegralManifold (I := I) m F.distribution k) [PreconnectedSpace L.carrier]
    (hinj : Injective L.map) (hx : x ∈ range L.map)
    (hmax : ∀ N' : IntegralManifold.{u, u} (I := I) m F.distribution k, ConnectedSpace N'.carrier →
      Injective N'.map → range L.map ⊆ range N'.map → range N'.map ⊆ range L.map) :
    ∃ e : Diffeomorph (𝓡 k) (𝓡 k) L.carrier (F.leafIntegralManifold x).carrier m,
      ∀ z, (F.leafIntegralManifold x).map (e z) = L.map z := by
  let _ : IsManifold I 1 M := IsManifold.of_le (n := (m : ℕ∞ω) + 1) le_add_self
  exact F.isInvolutiveDistribution.exists_diffeomorph_leaf_of_maximal
    (WithTop.coe_le_coe.mp F.one_le) le_rfl F.isContMDiffDistribution L hinj hx hmax

end PackagedLeaf

end TauCeti.Foliation
