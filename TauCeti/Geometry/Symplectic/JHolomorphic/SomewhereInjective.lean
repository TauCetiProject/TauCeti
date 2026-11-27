/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Compactness.Lindelof
public import TauCeti.Analysis.Complex.RiemannSurface.Descent
public import TauCeti.Analysis.Complex.RiemannSurface.SomewhereInjective
public import TauCeti.Geometry.Symplectic.JHolomorphic.BranchDegree
import TauCeti.Analysis.Complex.RiemannSurface.Branch.Values
import TauCeti.Analysis.Complex.RiemannSurface.Ramification
import TauCeti.Geometry.Manifold.ChartedSpace
import TauCeti.Geometry.Manifold.Immersion.Family
import TauCeti.Geometry.Manifold.MFDeriv.Basic
import TauCeti.Geometry.Manifold.MFDeriv.LocalInjectivity
import TauCeti.Topology.Perfect
import TauCeti.Topology.Separation.Hausdorff

/-!
# Somewhere injective closed pseudoholomorphic curves

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
is immersed. It then shows that the factorization of a closed curve through a somewhere injective
one is unique (McDuff–Salamon, Proposition 2.5.1).

* **Branch degree one everywhere.** If no point of a dense set, such as the complement of `B`, is
  related to another point, then no point of `S` at all is related to another point
  (`TauCeti.RiemannSurface.GermFactorsThrough.eq_of_dense`). A factorization `u = u ∘ φ` near `z`
  with `φ z = ζ ≠ z` relates every point `w` near `z` to `φ w ≠ w`, and some of these `w` lie in
  the dense set.
* **Injective points accumulate.** If no point other than an immersed point `z₀` is related to
  `z₀`, the points near `z₀` other than `z₀` are injective points
  (`TauCeti.eventually_isInjectivePoint_of_forall_germFactorsThrough_imp_eq`). Otherwise there are
  points `z → z₀`, `z ≠ z₀`, with partners `ζ z ≠ z` of the same value, and by compactness the
  partners cluster at some `ζ₀`. If `ζ₀ = z₀` this contradicts the injectivity of `u` near the
  immersed point `z₀`. If `ζ₀ ≠ z₀`, the image under `u` of every neighbourhood of `z₀` meets `u`
  at points `ζ z ≠ ζ₀` accumulating at `ζ₀`, so the branch of `u` at `ζ₀` factors through the one
  at `z₀` (`TauCeti.germFactorsThrough_of_frequently_mem_image`, McDuff–Salamon, Lemma 2.4.3),
  relating the distinct points `ζ₀` and `z₀`.
* **The equivalence.** An injective point `x` lies off `B`
  (`TauCeti.IsInjectivePoint.notMem_criticalValuePreimage`) and is related only to itself, so its
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
* **Uniqueness of the underlying simple curve.** Let `u = v₁ ∘ π₁ = v₂ ∘ π₂` with finite
  holomorphic maps `πᵢ : S → Sᵢ` onto compact connected Riemann surfaces and somewhere injective
  `C²` pseudoholomorphic curves `vᵢ : Sᵢ → N`. At two points `z`, `z'` of `S` where `πᵢ` is
  unramified, the branch of `u` at `z'` factors holomorphically through its branch at `z` exactly
  when `πᵢ z' = πᵢ z` (`TauCeti.IsSomewhereInjective.germFactorsThrough_comp_iff`), by pushing
  changes of coordinate down through local inverses of `πᵢ`
  (`TauCeti.RiemannSurface.germFactorsThrough_comp_iff`). Off a finite subset of `S` the fibres of
  `π₁` and of `π₂` are therefore both described by the germs of `u`, so they coincide; by the open
  mapping theorem they coincide everywhere
  (`TauCeti.RiemannSurface.FiniteHolomorphicMap.apply_eq_of_apply_eq_of_finite`), and two finite
  holomorphic maps with the same fibres differ by a unique biholomorphism
  (`TauCeti.RiemannSurface.FiniteHolomorphicMap.existsUnique_biholomorph_comp_eq`).

## Main results

* `TauCeti.IsSomewhereInjective.germFactorsThrough_iff`: on a somewhere injective closed curve,
  coincident branches occur only at the same point.
* `TauCeti.IsSomewhereInjective.germFactorsThrough_comp_iff`: the coincident branches of
  `v ∘ π` at unramified points lie over the same point of the somewhere injective curve `v`.
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
* `TauCeti.existsUnique_biholomorph_of_isSomewhereInjective`: uniqueness of the factorization of
  a closed pseudoholomorphic curve through a somewhere injective one.

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

omit [IsManifold 𝓘(ℂ) ∞ S] [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ N] in
/-- An injective point `x` of a map `u : S → N` from a Riemann surface lies outside the preimage
`B = u⁻¹(u(Crit u))` of its critical values: `x` is the only point of its fibre, and `u` is
immersed at `x`. -/
theorem IsInjectivePoint.notMem_criticalValuePreimage {x : S}
    (hx : IsInjectivePoint 𝓘(ℝ, ℂ) I u x) : x ∉ criticalValuePreimage I u := fun hB ↦ by
  obtain ⟨y, hy0, hyx⟩ := mem_criticalValuePreimage.1 hB
  exact mfderiv_ne_zero_of_injective hx.injective_mfderiv (hx.eq_of_apply_eq hyx ▸ hy0)

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
  · -- The class of `y` is a singleton containing `y`, so it is `{y}`.
    obtain ⟨a, ha⟩ := ncard_eq_one.1 (h1 y hy)
    have hya : y = a := mem_singleton_iff.1 (ha ▸ GermFactorsThrough.refl u y)
    exact setOf_germFactorsThrough_eq_singleton_iff.1 (hya ▸ ha) ζ' hζ'

/-- **On a closed curve of branch degree one, the points near an immersed point are injective.**
Let `u : S → N` be a `C²` pseudoholomorphic map from a compact Riemann surface into a Hausdorff
almost complex manifold, immersed at `z₀`, such that the branch of `u` at no point other than `z₀`
factors holomorphically through the branch of `u` at `z₀`. Then every point near `z₀` other than
`z₀` is an injective point of `u`. -/
theorem eventually_isInjectivePoint_of_forall_germFactorsThrough_imp_eq [CompactSpace S]
    [T2Space N] (hu : ContMDiff 𝓘(ℝ, ℂ) I 2 u)
    (hJu : IsPseudoholomorphic (ofComplexManifold ℂ S) J u) {z₀ : S}
    (hd : ∀ ζ, GermFactorsThrough u ζ u z₀ → ζ = z₀)
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
    exact hζz₀ (hd ζ₀ (germFactorsThrough_of_frequently_mem_image hu hJu
      (hu.of_le one_le_two) hJu hz₀ hacc))

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
    (eventually_isInjectivePoint_of_forall_germFactorsThrough_imp_eq hu hJu
      (fun ζ h ↦ (hd ζ _ h).symm) hz)
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
    (eventually_isInjectivePoint_of_forall_germFactorsThrough_imp_eq hu hJu
      (fun ζ h ↦ (hd ζ z₀ h).symm) hz₀).exists
  exact hz.isSomewhereInjective

/-- **A somewhere injective curve has no coincident branches.** Let `u : S → N` be a `C²`
pseudoholomorphic map from a compact connected Hausdorff Riemann surface into a Hausdorff almost
complex manifold with an injective point. Then the branch of `u` at `w'` factors holomorphically
through the branch of `u` at `w` only for `w = w'`. -/
theorem IsSomewhereInjective.germFactorsThrough_iff [CompactSpace S] [ConnectedSpace S]
    [T2Space S] [T2Space N] (hu : ContMDiff 𝓘(ℝ, ℂ) I 2 u)
    (hJu : IsPseudoholomorphic (ofComplexManifold ℂ S) J u) (h : IsSomewhereInjective 𝓘(ℝ, ℂ) I u)
    {w w' : S} : GermFactorsThrough u w' u w ↔ w' = w := by
  refine ⟨fun hww' ↦ ?_, fun h ↦ h ▸ .refl u w'⟩
  obtain ⟨x, hx⟩ := isSomewhereInjective_iff.1 h
  have hne : ∃ x₁ x₂, u x₁ ≠ u x₂ := h.exists_apply_ne
  -- The class of the injective point `x` is `{x}`, so all classes off `B` have one point.
  have hx1 : {ζ | GermFactorsThrough u x u ζ} = {x} :=
    setOf_germFactorsThrough_eq_singleton_iff.2 fun _ hζ ↦ hx.eq_of_apply_eq hζ.apply_eq.symm
  obtain ⟨d, -, hd⟩ := exists_pos_forall_ncard_setOf_germFactorsThrough_eq hu hJu hne
  have hd1 : d = 1 := by rw [← hd x hx.notMem_criticalValuePreimage, hx1, ncard_singleton]
  exact (eq_of_germFactorsThrough_of_forall_ncard_eq_one (hu.of_le one_le_two) hJu hne
    (fun y hy ↦ (hd y hy).trans hd1) hww').symm

/-- **A closed curve is somewhere injective exactly when it has branch degree one.** A `C²`
pseudoholomorphic map `u : S → N` from a compact connected Hausdorff Riemann surface into a
Hausdorff almost complex manifold has an injective point if and only if the branch of `u` at a
point factors holomorphically through the branch of `u` at no other point. -/
theorem isSomewhereInjective_iff_forall_germFactorsThrough_imp_eq [CompactSpace S]
    [ConnectedSpace S] [T2Space S] [T2Space N] (hu : ContMDiff 𝓘(ℝ, ℂ) I 2 u)
    (hJu : IsPseudoholomorphic (ofComplexManifold ℂ S) J u) :
    IsSomewhereInjective 𝓘(ℝ, ℂ) I u ↔ ∀ z ζ, GermFactorsThrough u z u ζ → ζ = z :=
  ⟨fun h _ _ hzζ ↦ ((h.germFactorsThrough_iff hu hJu).1 hzζ).symm,
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
  · rw [setOf_germFactorsThrough_eq_singleton_iff.2 (h z), ncard_singleton]
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

/-- **Coincident branches of a multiple cover lie over one point.** Let `u` be a `C²`
pseudoholomorphic, somewhere injective curve on a compact connected Hausdorff Riemann surface and
`π` a map to it, holomorphic near `z` and `z'` and unramified there. Then the branch of `u ∘ π` at
`z'` factors holomorphically through its branch at `z` exactly when `π z' = π z`. -/
theorem IsSomewhereInjective.germFactorsThrough_comp_iff [CompactSpace S] [ConnectedSpace S]
    [T2Space S] [T2Space N] (hu : ContMDiff 𝓘(ℝ, ℂ) I 2 u)
    (hJu : IsPseudoholomorphic (ofComplexManifold ℂ S) J u)
    (hi : IsSomewhereInjective 𝓘(ℝ, ℂ) I u) {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) 1 X] {π : X → S} {z z' : X}
    (hπz : ∀ᶠ x in 𝓝 z, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) π x)
    (hπz' : ∀ᶠ x in 𝓝 z', MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) π x)
    (hz : localMultiplicity π z = 1) (hz' : localMultiplicity π z' = 1) :
    GermFactorsThrough (u ∘ π) z' (u ∘ π) z ↔ π z' = π z :=
  (RiemannSurface.germFactorsThrough_comp_iff hπz hπz' hz hz').trans
    (hi.germFactorsThrough_iff hu hJu)

omit [IsManifold 𝓘(ℂ) ∞ S] in
/-- **Uniqueness of the simple curve underlying a closed pseudoholomorphic curve.** Let `S` be a
compact Riemann surface, `π₁ : S → S₁` and `π₂ : S → S₂` finite holomorphic maps onto compact
connected Riemann surfaces, and `v₁ : S₁ → N`, `v₂ : S₂ → N` somewhere injective `C²`
pseudoholomorphic curves with `v₁ ∘ π₁ = v₂ ∘ π₂`. Then there is exactly one biholomorphism
`a : S₁ → S₂` with `a ∘ π₁ = π₂` and `v₂ ∘ a = v₁`. -/
theorem existsUnique_biholomorph_of_isSomewhereInjective [CompactSpace S] [T2Space N]
    {S₁ S₂ : Type*} [TopologicalSpace S₁]
    [ChartedSpace ℂ S₁] [IsManifold 𝓘(ℂ) ∞ S₁] [ConnectedSpace S₁] [T2Space S₁]
    [TopologicalSpace S₂] [ChartedSpace ℂ S₂] [IsManifold 𝓘(ℂ) ∞ S₂] [ConnectedSpace S₂]
    [T2Space S₂] [IsManifold 𝓘(ℂ) 1 S] (π₁ : FiniteHolomorphicMap S S₁)
    (π₂ : FiniteHolomorphicMap S S₂) {v₁ : S₁ → N} {v₂ : S₂ → N} (hv₁ : ContMDiff 𝓘(ℝ, ℂ) I 2 v₁)
    (hv₂ : ContMDiff 𝓘(ℝ, ℂ) I 2 v₂) (hJv₁ : IsPseudoholomorphic (ofComplexManifold ℂ S₁) J v₁)
    (hJv₂ : IsPseudoholomorphic (ofComplexManifold ℂ S₂) J v₂)
    (hi₁ : IsSomewhereInjective 𝓘(ℝ, ℂ) I v₁) (hi₂ : IsSomewhereInjective 𝓘(ℝ, ℂ) I v₂)
    (h : v₁ ∘ π₁ = v₂ ∘ π₂) :
    ∃! a : S₁ ≃ₘ⟮𝓘(ℂ), 𝓘(ℂ)⟯ S₂, a ∘ π₁ = π₂ ∧ v₂ ∘ a = v₁ := by
  have := π₁.compactSpace_codomain
  have := π₂.compactSpace_codomain
  -- Off a finite set `F`, both covers are unramified.
  set F := π₁ ⁻¹' π₁.branchValues ∪ π₂ ⁻¹' π₂.branchValues
  have hF : F.Finite :=
    (π₁.finite_branchValues.preimage' fun y _ ↦ π₁.finite_fiber y).union
      (π₂.finite_branchValues.preimage' fun y _ ↦ π₂.finite_fiber y)
  have hlm₁ : ∀ z ∉ F, localMultiplicity π₁ z = 1 := fun z hz ↦
    (π₁.notMem_branchValues_iff _).1 (fun h ↦ hz (.inl h)) z rfl
  have hlm₂ : ∀ z ∉ F, localMultiplicity π₂ z = 1 := fun z hz ↦
    (π₂.notMem_branchValues_iff _).1 (fun h ↦ hz (.inr h)) z rfl
  -- There, the fibres of both covers are the classes of coincident branches of `v₁ ∘ π₁`.
  have hfib : ∀ z ∉ F, ∀ z' ∉ F, π₁ z = π₁ z' ↔ π₂ z = π₂ z' := fun z hz z' hz' ↦ by
    rw [eq_comm (a := π₁ z), eq_comm (a := π₂ z),
      ← hi₁.germFactorsThrough_comp_iff hv₁ hJv₁ (.of_forall fun x ↦ π₁.holomorphic x)
        (.of_forall fun x ↦ π₁.holomorphic x) (hlm₁ z hz) (hlm₁ z' hz'), h,
      hi₂.germFactorsThrough_comp_iff hv₂ hJv₂ (.of_forall fun x ↦ π₂.holomorphic x)
        (.of_forall fun x ↦ π₂.holomorphic x) (hlm₂ z hz) (hlm₂ z' hz')]
  -- By the open mapping theorem the fibres coincide everywhere.
  have hfib' : ∀ z z', π₁ z = π₁ z' ↔ π₂ z = π₂ z' := fun z z' ↦
    ⟨π₁.apply_eq_of_apply_eq_of_finite π₂.holomorphic.continuous hF
      (fun x hx x' hx' ↦ (hfib x hx x' hx').1),
     π₂.apply_eq_of_apply_eq_of_finite π₁.holomorphic.continuous hF
      (fun x hx x' hx' ↦ (hfib x hx x' hx').2)⟩
  obtain ⟨a, ha, huniq⟩ := π₁.existsUnique_biholomorph_comp_eq π₂ hfib'
  refine ⟨a, ⟨ha, funext fun y ↦ ?_⟩, fun a' ha' ↦ huniq a' ha'.1⟩
  obtain ⟨x, rfl⟩ := π₁.surjective y
  rw [comp_apply, ← comp_apply (f := a), ha]
  exact (congrFun h x).symm


end TauCeti
