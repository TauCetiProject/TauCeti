/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Compactness.Lindelof
public import TauCeti.Analysis.Complex.RiemannSurface.SomewhereInjective
public import TauCeti.Geometry.Symplectic.JHolomorphic.BranchDegree
import TauCeti.Geometry.Manifold.ChartedSpace
import TauCeti.Geometry.Manifold.Immersion.Family
import TauCeti.Geometry.Manifold.MFDeriv.LocalInjectivity
import TauCeti.Topology.Perfect
import TauCeti.Topology.Separation.Hausdorff

/-!
# Closed pseudoholomorphic curves of branch degree one are somewhere injective

Let `S` be a compact connected Hausdorff Riemann surface, `N` a Hausdorff manifold with a smooth
almost complex structure `J`, and `u : S → N` a nonconstant pseudoholomorphic map of class `C²`.
Off the finite preimage `B = u⁻¹(u(Crit u))` of its critical values, the classes of the
coincident-branch relation `Γ₀` all have the same number `d ≥ 1` of points
(`TauCeti.exists_pos_forall_ncard_setOf_germFactorsThrough_eq`); here `z` and `ζ` are related when
the branch of `u` at `z` factors holomorphically through the branch of `u` at `ζ`
(`TauCeti.RiemannSurface.GermFactorsThrough u z u ζ`). This `d` is the degree of the branched cover
through which `u` factors over its simple curve (McDuff–Salamon, Proposition 2.5.1). This file
shows that `d = 1` exactly when `u` has an injective point, a point `z` with `du(z)` injective and
`u⁻¹(u z) = {z}` (`TauCeti.IsInjectivePoint`), and that the injective points of such a curve are
all points except a countable set of noninjective points, which accumulates at no point where `u`
is immersed.

* **Branch degree one everywhere.** If no point of a dense set, such as the complement of `B`, is
  related to another point, then no point of `S` at all is related to another point
  (`TauCeti.RiemannSurface.GermFactorsThrough.eq_of_dense`). A factorization `u = u ∘ φ` near `z`
  with `φ z = ζ ≠ z` relates every point `w` near `z` to `φ w ≠ w`, and some of these `w` lie in
  the dense set.
* **Injective points accumulate.** If no two distinct points are related, the points near an
  immersed point `z₀` other than `z₀` are injective points
  (`TauCeti.eventually_isInjectivePoint_of_forall_germFactorsThrough_imp_eq`). Otherwise there are
  points `z → z₀`, `z ≠ z₀`, with partners `ζ z ≠ z` of the same value, and by compactness the
  partners cluster at some `ζ₀`. If `ζ₀ = z₀` this contradicts the injectivity of `u` near the
  immersed point `z₀`. If `ζ₀ ≠ z₀`, the image under `u` of every neighbourhood of `z₀` meets `u`
  at points `ζ z ≠ ζ₀` accumulating at `ζ₀`, so the branch of `u` at `ζ₀` factors through the one
  at `z₀` (`TauCeti.germFactorsThrough_of_frequently_mem_image`, McDuff–Salamon, Lemma 2.4.3),
  relating the distinct points `ζ₀` and `z₀`.
* **The equivalence.** An injective point `x` lies off `B` and is related only to itself, so its
  class has one element and `d = 1`; conversely, if `d = 1` then the noncritical points, which
  exist, are limits of injective points. Hence `u` is somewhere injective exactly when no two
  distinct points of `S` are related
  (`TauCeti.isSomewhereInjective_iff_forall_germFactorsThrough_imp_eq`), exactly when every class
  off `B` has one element
  (`TauCeti.isSomewhereInjective_iff_forall_ncard_setOf_germFactorsThrough_eq_one`).
  For the Riemann sphere, `d = 1` makes `u` a simple sphere: it factors through no holomorphic map
  of the sphere of degree greater than one
  (`TauCeti.isSimpleSphere_of_forall_germFactorsThrough_imp_eq`).
* **The noninjective locus.** For such a curve the injective points are codiscrete within the
  immersed points (`TauCeti.setOf_isInjectivePoint_mem_codiscreteWithin`), so the noninjective
  points, at which `du` vanishes or another point has the same value, accumulate only at the
  finitely many critical points and form a countable set
  (`TauCeti.countable_setOf_not_isInjectivePoint`).

## Main results

* `TauCeti.RiemannSurface.GermFactorsThrough.eq_of_dense`: if no point of a dense set, such as the
  complement of `u⁻¹(u(Crit u))`, has a coincident branch at another point, then no point does.
* `TauCeti.IsSomewhereInjective.eq_of_germFactorsThrough`: on a somewhere injective closed curve,
  coincident branches occur only at the same point.
* `TauCeti.eventually_isInjectivePoint_of_forall_germFactorsThrough_imp_eq`,
  `TauCeti.setOf_isInjectivePoint_mem_codiscreteWithin`: near an immersed point, the other points
  of a curve of branch degree one are injective points.
* `TauCeti.isSomewhereInjective_iff_forall_germFactorsThrough_imp_eq`,
  `TauCeti.isSomewhereInjective_iff_forall_ncard_setOf_germFactorsThrough_eq_one`: a closed curve
  is somewhere injective exactly when its branch degree `d` is one.
* `TauCeti.isSimpleSphere_of_forall_germFactorsThrough_imp_eq`: a sphere of branch degree one is
  simple.
* `TauCeti.countable_setOf_not_isInjectivePoint`: a closed curve of branch degree one has countably
  many noninjective points.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., American
  Mathematical Society Colloquium Publications 52, 2012, Lemma 2.4.3 and Proposition 2.5.1.
* C. Wendl, *Lectures on holomorphic curves in symplectic and contact geometry*, arXiv:1011.1690,
  Proposition 4.3 and Definitions 4.4 and 4.5.
-/

public section

open Function Set Filter Topology
open scoped Manifold ContDiff TauCeti.ComplexManifold

namespace TauCeti

open SmoothAlmostComplexStructure RiemannSurface

variable {S : Type*} [TopologicalSpace S] [ChartedSpace ℂ S] [IsManifold 𝓘(ℂ) ∞ S]
  {E H N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N]
  {J : SmoothAlmostComplexStructure I N} {u : S → N}

omit [IsManifold 𝓘(ℂ) ∞ S] [TopologicalSpace N] in
/-- **Branch degree one on a dense set gives branch degree one everywhere.** Let `u : S → N` be a
map from a Hausdorff Riemann surface, and let `s` be a dense set of points of `S`, such as the
complement of the preimage `B = u⁻¹(u(Crit u))` of the critical values of `u`, at each of which
the branch of `u` factors holomorphically through the branch of `u` at no other point. Then the
branch of `u` at any point `z` factors holomorphically through the branch of `u` at no other
point. -/
theorem RiemannSurface.GermFactorsThrough.eq_of_dense [T2Space S] {s : Set S} (hs : Dense s)
    (hd : ∀ z ∈ s, ∀ ζ, GermFactorsThrough u z u ζ → ζ = z)
    {z ζ : S} (h : GermFactorsThrough u z u ζ) : ζ = z := by
  by_contra hne
  -- A factorization `u = u ∘ φ` near `z` with `φ z = ζ` relates each `w` near `z` to `φ w`.
  obtain ⟨φ, hφz, hφc, hφr⟩ := h.exists_eventually_germFactorsThrough
  -- Since `φ z = ζ ≠ z`, also `φ w ≠ w` for `w` near `z`.
  obtain ⟨U, V, hU, hV, hζU, hzV, hUV⟩ := t2_separation hne
  have hφU : ∀ᶠ w in 𝓝 z, φ w ∈ U := hφc.preimage_mem_nhds (hφz ▸ hU.mem_nhds hζU)
  -- Some such `w` lies in `s`, where it can only be related to itself.
  obtain ⟨w, hws, hwr, hwU, hwV⟩ := (mem_closure_iff_frequently.1 (hs.closure_eq ▸ mem_univ z)
    |>.and_eventually (hφr.and (hφU.and (hV.mem_nhds hzV)))).exists
  rw [hd w hws (φ w) hwr] at hwU
  exact disjoint_left.1 hUV hwU hwV

omit [IsManifold 𝓘(ℂ) ∞ S] [FiniteDimensional ℝ E] [I.Boundaryless] [TopologicalSpace N]
  [IsManifold I ∞ N] in
/-- A map from a Riemann surface with two points, whose branch at a point factors holomorphically
through its branch at no other point, is not constant: the branches of a constant map all factor
through each other by constant changes of coordinate. -/
private theorem exists_apply_ne_of_forall_germFactorsThrough_imp_eq [Nontrivial S]
    (hd : ∀ z ζ, GermFactorsThrough u z u ζ → ζ = z) : ∃ x₁ x₂, u x₁ ≠ u x₂ := by
  by_contra! h
  obtain ⟨a, b, hab⟩ := exists_pair_ne S
  exact hab (hd b a (germFactorsThrough_iff.2 ⟨fun _ ↦ a, rfl,
    .of_forall fun _ ↦ mdifferentiableAt_const, .of_forall fun y ↦ h y a⟩))

/-- On a closed curve whose coincident-branch classes off `B = u⁻¹(u(Crit u))` all have one
element, the branch of `u` at a point factors holomorphically through the branch of `u` at no
other point. -/
private theorem eq_of_germFactorsThrough_of_forall_ncard_eq_one [CompactSpace S]
    [PreconnectedSpace S] [T2Space S] (hu : ContMDiff 𝓘(ℝ, ℂ) I 1 u)
    (hJu : IsPseudoholomorphic (ofComplexManifold ℂ S) J u) (hne : ∃ x₁ x₂, u x₁ ≠ u x₂)
    (h1 : ∀ z ∉ criticalValuePreimage I u, {ζ | GermFactorsThrough u z u ζ}.ncard = 1)
    {z ζ : S} (hzζ : GermFactorsThrough u z u ζ) : ζ = z := by
  have : PerfectSpace S := ChartedSpace.perfectSpace (H := ℂ)
  refine GermFactorsThrough.eq_of_dense (s := (criticalValuePreimage I u)ᶜ) ?_
    (fun y hy ζ' hζ' ↦ ?_) hzζ
  · rw [compl_eq_univ_sdiff]
    exact dense_univ.sdiff_finite (finite_criticalValuePreimage hu hJu hne)
  · -- The class of `y` is a singleton containing `y`.
    obtain ⟨a, ha⟩ := ncard_eq_one.1 (h1 y hy)
    have hy' : y ∈ {ζ | GermFactorsThrough u y u ζ} := .refl u y
    have hζ'' : ζ' ∈ {ζ | GermFactorsThrough u y u ζ} := hζ'
    rw [ha, mem_singleton_iff] at hy' hζ''
    exact hζ''.trans hy'.symm

/-- **On a closed curve of branch degree one, the points near an immersed point are injective.**
Let `u : S → N` be a `C²` pseudoholomorphic map from a compact Riemann surface into a Hausdorff
almost complex manifold such that the branch of `u` at a point factors holomorphically through the
branch of `u` at no other point. If `u` is immersed at `z₀`, then every point near `z₀` other than
`z₀` is an injective point of `u`. -/
theorem eventually_isInjectivePoint_of_forall_germFactorsThrough_imp_eq [CompactSpace S]
    [T2Space N] (hu : ContMDiff 𝓘(ℝ, ℂ) I 2 u)
    (hJu : IsPseudoholomorphic (ofComplexManifold ℂ S) J u)
    (hd : ∀ z ζ, GermFactorsThrough u z u ζ → ζ = z) {z₀ : S}
    (hz₀ : mfderiv 𝓘(ℝ, ℂ) I u z₀ ≠ 0) :
    ∀ᶠ z in 𝓝[≠] z₀, IsInjectivePoint 𝓘(ℝ, ℂ) I u z := by
  have hinj₀ : Injective (mfderiv 𝓘(ℝ, ℂ) I u z₀) :=
    (hJu.isPseudoholomorphicAt z₀).injective_mfderiv_iff_ne_zero.2 hz₀
  -- `u` is injective on a neighbourhood `t` of `z₀`, and immersed near `z₀`.
  obtain ⟨t, ht, htinj⟩ := (hu z₀).exists_mem_nhds_injOn two_ne_zero hinj₀
  have hD := (hu z₀).eventually_injective_mfderiv_of_injective one_le_two hinj₀
  -- An immersed point that is not an injective point shares its value with another point.
  have hpartner : ∀ z, Injective (mfderiv 𝓘(ℝ, ℂ) I u z) →
      ¬IsInjectivePoint 𝓘(ℝ, ℂ) I u z → ∃ ζ, ζ ≠ z ∧ u ζ = u z := by
    intro z hz hnz
    by_contra! h
    exact hnz ⟨hz, fun ζ hζ ↦ by_contra fun hne ↦ h ζ hne hζ⟩
  choose! ζ hζne hζu using hpartner
  by_contra hfreq
  -- The filter `F` of the noninjective points near `z₀`, other than `z₀`.
  set F := 𝓝[≠] z₀ ⊓ 𝓟 {z | ¬IsInjectivePoint 𝓘(ℝ, ℂ) I u z}
  have hF : F.NeBot := frequently_iff_neBot.1 (not_eventually.1 hfreq)
  have hFz₀ : F ≤ 𝓝 z₀ := inf_le_left.trans nhdsWithin_le_nhds
  have hFt : ∀ᶠ z in F, z ∈ t ∧ z ≠ z₀ ∧ ζ z ≠ z ∧ u (ζ z) = u z := by
    have hne : ∀ᶠ z in F, z ≠ z₀ := mem_inf_of_left self_mem_nhdsWithin
    have hni : ∀ᶠ z in F, ¬IsInjectivePoint 𝓘(ℝ, ℂ) I u z :=
      mem_inf_of_right (mem_principal_self _)
    filter_upwards [hFz₀ ht, hFz₀ hD, hne, hni] with z hzt hzD hzne hzni
    exact ⟨hzt, hzne, hζne z hzD hzni, hζu z hzD hzni⟩
  -- The partners `ζ z` cluster at some point `ζ₀`.
  obtain ⟨ζ₀, hζ₀⟩ := exists_clusterPt_of_compactSpace (map ζ F)
  have hfr : ∀ s ∈ 𝓝 ζ₀, ∃ᶠ z in F, ζ z ∈ s ∧ z ∈ t ∧ z ≠ z₀ ∧ ζ z ≠ z ∧ u (ζ z) = u z :=
    fun s hs ↦ (frequently_map.1 (hζ₀.frequently hs)).and_eventually hFt
  by_cases hζz₀ : ζ₀ = z₀
  · -- Partners near `z₀` contradict the injectivity of `u` on `t`.
    obtain ⟨z, hζt, hzt, -, hζz, hu'⟩ := (hfr t (hζz₀ ▸ ht)).exists
    exact hζz (htinj hζt hzt hu')
  · -- The values `u z` near `u z₀` are taken at points `ζ z ≠ ζ₀` accumulating at `ζ₀`, so the
    -- branch of `u` at `ζ₀` factors through the branch of `u` at `z₀`.
    have hval : u z₀ = u ζ₀ := eq_of_frequently_mem_image hu.continuous.continuousAt
      hu.continuous.continuousAt fun s hs ↦ ((hfr s hs).mono
        fun z h ↦ ⟨ζ z, h.1, h.2.2.2.2⟩).filter_mono hFz₀
    have hacc : ∀ s ∈ 𝓝 z₀, ∃ᶠ b in 𝓝[≠] ζ₀, u b ∈ u '' s := by
      intro s hs
      rw [frequently_nhdsWithin_iff, frequently_iff]
      intro W hW
      obtain ⟨z, ⟨hζW, hzt, hzne, -, hu'⟩, hzs⟩ := ((hfr W hW).and_eventually (hFz₀ hs)).exists
      refine ⟨ζ z, hζW, ⟨z, hzs, hu'.symm⟩, fun hζ ↦ hzne (htinj hzt (mem_of_mem_nhds ht) ?_)⟩
      rw [← hu', hval, ← mem_singleton_iff.1 hζ]
    exact hζz₀ (hd ζ₀ z₀ (germFactorsThrough_of_frequently_mem_image hu hJu
      (hu.of_le one_le_two) hJu hz₀ hacc)).symm

/-- **The noninjective points of a closed curve of branch degree one accumulate only at critical
points.** Let `u : S → N` be a `C²` pseudoholomorphic map from a compact Riemann surface into a
Hausdorff almost complex manifold such that the branch of `u` at a point factors holomorphically
through the branch of `u` at no other point. Then the injective points of `u` are codiscrete within
the points where `u` is immersed. -/
theorem setOf_isInjectivePoint_mem_codiscreteWithin [CompactSpace S] [T2Space N]
    (hu : ContMDiff 𝓘(ℝ, ℂ) I 2 u) (hJu : IsPseudoholomorphic (ofComplexManifold ℂ S) J u)
    (hd : ∀ z ζ, GermFactorsThrough u z u ζ → ζ = z) :
    {z | IsInjectivePoint 𝓘(ℝ, ℂ) I u z} ∈
      codiscreteWithin {z | mfderiv 𝓘(ℝ, ℂ) I u z ≠ 0} :=
  mem_codiscreteWithin_iff_forall_mem_nhdsNE.2 fun _ hz ↦ mem_of_superset
    (eventually_isInjectivePoint_of_forall_germFactorsThrough_imp_eq hu hJu hd hz)
    subset_union_left

/-- **A closed curve of branch degree one is somewhere injective.** Let `u : S → N` be a `C²`
pseudoholomorphic map from a compact connected Riemann surface into a Hausdorff almost complex
manifold such that the branch of `u` at a point factors holomorphically through the branch of `u`
at no other point. Then `u` has an injective point. -/
theorem isSomewhereInjective_of_forall_germFactorsThrough_imp_eq [CompactSpace S]
    [ConnectedSpace S] [T2Space N] (hu : ContMDiff 𝓘(ℝ, ℂ) I 2 u)
    (hJu : IsPseudoholomorphic (ofComplexManifold ℂ S) J u)
    (hd : ∀ z ζ, GermFactorsThrough u z u ζ → ζ = z) : IsSomewhereInjective 𝓘(ℝ, ℂ) I u := by
  have : PerfectSpace S := ChartedSpace.perfectSpace (H := ℂ)
  have : Nontrivial S := PerfectSpace.nontrivial S
  obtain ⟨x₁⟩ := (ConnectedSpace.toNonempty : Nonempty S)
  -- The critical points of the nonconstant map `u` are isolated, so `u` is immersed somewhere.
  obtain ⟨z₀, hz₀⟩ := Filter.nonempty_of_mem (mem_codiscrete_iff_forall_mem_nhdsNE.1
    (setOf_mfderiv_ne_zero_mem_codiscrete_of_isPseudoholomorphic (hu.of_le one_le_two) hJu
      (exists_apply_ne_of_forall_germFactorsThrough_imp_eq hd)) x₁)
  obtain ⟨z, hz⟩ :=
    (eventually_isInjectivePoint_of_forall_germFactorsThrough_imp_eq hu hJu hd hz₀).exists
  exact hz.isSomewhereInjective

/-- **On a somewhere injective closed curve, coincident branches occur only at the same point.**
Let `u : S → N` be a `C²` pseudoholomorphic map from a compact connected Hausdorff Riemann surface
into a Hausdorff almost complex manifold with an injective point. Then the branch of `u` at a point
`z` factors holomorphically through the branch of `u` at no point other than `z`. -/
theorem IsSomewhereInjective.eq_of_germFactorsThrough [CompactSpace S] [ConnectedSpace S]
    [T2Space S] [T2Space N] (hu : ContMDiff 𝓘(ℝ, ℂ) I 2 u)
    (hJu : IsPseudoholomorphic (ofComplexManifold ℂ S) J u) (h : IsSomewhereInjective 𝓘(ℝ, ℂ) I u)
    {z ζ : S} (hzζ : GermFactorsThrough u z u ζ) : ζ = z := by
  have : PerfectSpace S := ChartedSpace.perfectSpace (H := ℂ)
  obtain ⟨x, hx⟩ := isSomewhereInjective_iff.1 h
  -- `u` is not constant: the points near `x` other than `x` have other values.
  obtain ⟨w, hw⟩ := (eventually_mem_nhdsWithin (a := x) (s := {x}ᶜ)).exists
  have hne : ∃ x₁ x₂, u x₁ ≠ u x₂ := ⟨w, x, hx.apply_ne hw⟩
  -- The class of the injective point `x` is `{x}`, so all classes off `B` have one point.
  have hxB : x ∉ criticalValuePreimage I u := fun hB ↦ by
    obtain ⟨y, hy0, hyx⟩ := mem_criticalValuePreimage.1 hB
    exact (hJu.isPseudoholomorphicAt x).injective_mfderiv_iff_ne_zero.1 hx.injective_mfderiv
      (hx.eq_of_apply_eq hyx ▸ hy0)
  have hx1 : {ζ | GermFactorsThrough u x u ζ} = {x} :=
    Subset.antisymm (fun ζ hζ ↦ hx.eq_of_apply_eq (GermFactorsThrough.apply_eq hζ).symm)
      (singleton_subset_iff.2 (.refl u x))
  obtain ⟨d, -, hd⟩ := exists_pos_forall_ncard_setOf_germFactorsThrough_eq hu hJu hne
  have hd1 : d = 1 := by rw [← hd x hxB, hx1, ncard_singleton]
  exact eq_of_germFactorsThrough_of_forall_ncard_eq_one (hu.of_le one_le_two) hJu hne
    (fun y hy ↦ (hd y hy).trans hd1) hzζ

/-- **A closed curve is somewhere injective exactly when it has branch degree one.** A `C²`
pseudoholomorphic map `u : S → N` from a compact connected Hausdorff Riemann surface into a
Hausdorff almost complex manifold has an injective point if and only if the branch of `u` at a
point factors holomorphically through the branch of `u` at no other point. -/
theorem isSomewhereInjective_iff_forall_germFactorsThrough_imp_eq [CompactSpace S]
    [ConnectedSpace S] [T2Space S] [T2Space N] (hu : ContMDiff 𝓘(ℝ, ℂ) I 2 u)
    (hJu : IsPseudoholomorphic (ofComplexManifold ℂ S) J u) :
    IsSomewhereInjective 𝓘(ℝ, ℂ) I u ↔ ∀ z ζ, GermFactorsThrough u z u ζ → ζ = z :=
  ⟨fun h _ _ ↦ h.eq_of_germFactorsThrough hu hJu,
    isSomewhereInjective_of_forall_germFactorsThrough_imp_eq hu hJu⟩

/-- **A closed curve is somewhere injective exactly when its branch degree `d` is one.** A
nonconstant `C²` pseudoholomorphic map `u : S → N` from a compact connected Hausdorff Riemann
surface into a Hausdorff almost complex manifold has an injective point if and only if, for every
point `z` outside the preimage `B = u⁻¹(u(Crit u))` of its critical values, `z` is the only point
through whose branch the branch of `u` at `z` factors holomorphically. -/
theorem isSomewhereInjective_iff_forall_ncard_setOf_germFactorsThrough_eq_one [CompactSpace S]
    [ConnectedSpace S] [T2Space S] [T2Space N] (hu : ContMDiff 𝓘(ℝ, ℂ) I 2 u)
    (hJu : IsPseudoholomorphic (ofComplexManifold ℂ S) J u) (hne : ∃ x₁ x₂, u x₁ ≠ u x₂) :
    IsSomewhereInjective 𝓘(ℝ, ℂ) I u ↔
      ∀ z ∉ criticalValuePreimage I u, {ζ | GermFactorsThrough u z u ζ}.ncard = 1 := by
  rw [isSomewhereInjective_iff_forall_germFactorsThrough_imp_eq hu hJu]
  refine ⟨fun h z _ ↦ ?_, fun h z ζ hzζ ↦ ?_⟩
  · rw [← ncard_singleton z]
    exact congrArg ncard (Subset.antisymm (fun ζ hζ ↦ h z ζ hζ)
      (singleton_subset_iff.2 (.refl u z)))
  · exact eq_of_germFactorsThrough_of_forall_ncard_eq_one (hu.of_le one_le_two) hJu hne h hzζ

/-- **A closed curve of branch degree one has countably many noninjective points.** Let
`u : S → N` be a `C²` pseudoholomorphic map from a compact connected Riemann surface into a
Hausdorff almost complex manifold such that the branch of `u` at a point factors holomorphically
through the branch of `u` at no other point. Then the points at which `du` vanishes or which share
their value with another point form a countable set. -/
theorem countable_setOf_not_isInjectivePoint [CompactSpace S] [ConnectedSpace S] [T2Space N]
    (hu : ContMDiff 𝓘(ℝ, ℂ) I 2 u) (hJu : IsPseudoholomorphic (ofComplexManifold ℂ S) J u)
    (hd : ∀ z ζ, GermFactorsThrough u z u ζ → ζ = z) :
    {z | ¬IsInjectivePoint 𝓘(ℝ, ℂ) I u z}.Countable := by
  have : PerfectSpace S := ChartedSpace.perfectSpace (H := ℂ)
  have : Nontrivial S := PerfectSpace.nontrivial S
  have : SecondCountableTopology S := ChartedSpace.secondCountable_of_sigmaCompact ℂ S
  -- Off the finitely many critical points, the noninjective points form a discrete set.
  have hdisc : IsDiscrete ({z | ¬IsInjectivePoint 𝓘(ℝ, ℂ) I u z} ∩
      {z | mfderiv 𝓘(ℝ, ℂ) I u z ≠ 0}) :=
    isDiscrete_of_codiscreteWithin (by
      simpa only [compl_ofPred, not_not] using
        setOf_isInjectivePoint_mem_codiscreteWithin hu hJu hd)
  refine (((HereditarilyLindelofSpace.isLindelof _).countable_of_isDiscrete hdisc).union
    (finite_setOf_mfderiv_eq_zero_of_isPseudoholomorphic (hu.of_le one_le_two) hJu
      (exists_apply_ne_of_forall_germFactorsThrough_imp_eq hd)).countable).mono fun z hz ↦ ?_
  by_cases h0 : mfderiv 𝓘(ℝ, ℂ) I u z = 0
  · exact Or.inr h0
  · exact Or.inl ⟨hz, h0⟩

/-- **A sphere of branch degree one is simple.** A `C²` pseudoholomorphic map `u` of the Riemann
sphere into a Hausdorff almost complex manifold, such that the branch of `u` at a point
factors holomorphically through the branch of `u` at no other point, factors through no holomorphic
map of the sphere to itself of degree greater than one. -/
theorem isSimpleSphere_of_forall_germFactorsThrough_imp_eq [T2Space N] {u : OnePoint ℂ → N}
    (hu : ContMDiff 𝓘(ℝ, ℂ) I 2 u)
    (hJu : IsPseudoholomorphic (ofComplexManifold ℂ (OnePoint ℂ)) J u)
    (hd : ∀ z ζ, GermFactorsThrough u z u ζ → ζ = z) : IsSimpleSphere u :=
  (isSomewhereInjective_of_forall_germFactorsThrough_imp_eq hu hJu hd).isSimpleSphere
    (hu.of_le one_le_two)

end TauCeti
