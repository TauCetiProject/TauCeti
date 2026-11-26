/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.JHolomorphic.RiemannSurface
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import TauCeti.Geometry.Manifold.Connected
import TauCeti.Geometry.Manifold.MFDeriv.LocalInjectivity

/-!
# The number of coincident branches of a closed pseudoholomorphic curve

Let `S` be a compact connected Hausdorff Riemann surface, `N` a Hausdorff manifold with a smooth
almost complex structure `J`, and `u : S → N` a nonconstant pseudoholomorphic map of class `C²`.
Its critical values have the finite preimage `B = u⁻¹(u(Crit u))`
(`TauCeti.finite_preimage_image_setOf_mfderiv_eq_zero_of_isPseudoholomorphic`). On `S \ B` the
relation `Γ₀`, under which `z` and `ζ` are related when the branches of `u` at `z` and at `ζ` differ
by a holomorphic change of source coordinate (`TauCeti.RiemannSurface.GermFactorsThrough u z u ζ`),
is a closed equivalence relation (`TauCeti.equivalence_germFactorsThrough`,
`TauCeti.isClosed_setOf_germFactorsThrough`). This file shows that its classes all have the same
finite number `d ≥ 1` of elements (`TauCeti.exists_pos_forall_ncard_setOf_germFactorsThrough_eq`).
This `d` is the degree of the branched cover `S → S/Γ` through which `u` factors in the
construction of the simple curve underlying `u` (McDuff–Salamon, Proposition 2.5.1), and `u` is a
multiple cover exactly when `d > 1`.

The count is locally constant because `Γ₀` is locally trivial over every point `z₀` whose fibre
`u⁻¹(u z₀)` consists of immersed points and whose class is finite
(`TauCeti.exists_eventually_setOf_germFactorsThrough_eq_image`). Let `C` be the class of `z₀`. For
each `ζ ∈ C` the branch of `u` at `z₀` factors as `u = u ∘ ψ_ζ` near `z₀`, with `ψ_ζ z₀ = ζ`. Then
for `z` near `z₀` the class of `z` is exactly `{ψ_ζ z | ζ ∈ C}`, and these points are distinct:

* **the points `ψ_ζ z` are related to `z`**, through the same factorization `u = u ∘ ψ_ζ`, and lie
  in pairwise disjoint neighbourhoods `V_ζ` of the points `ζ`;
* **no other point is related to `z`**. Near each `ζ ∈ C` the map `u` is immersed, hence injective
  on `V_ζ` (`ContMDiffAt.exists_mem_nhds_injOn`,
  `TauCeti.IsPseudoholomorphicAt.injective_mfderiv_iff_ne_zero`), so `ψ_ζ z` is the only point of
  `V_ζ` with the value `u z`. Outside the `V_ζ` the compact set `K = S \ ⋃ V_ζ` contains no
  point related to `z₀`: such a point would lie in `C`. Since the relation is closed at immersed
  points (`TauCeti.germFactorsThrough_of_mem_closure`), and points with another value stay
  unrelated, the tube lemma keeps `K` free of points related to `z` for all `z` near `z₀`
  (`TauCeti.eventually_forall_not_germFactorsThrough_of_isCompact`).

Since `S \ B` is connected (`TauCeti.isConnected_compl_of_finite_of_one_lt_rank`), the locally
constant count is constant there.

## Main results

* `TauCeti.eventually_forall_not_germFactorsThrough_of_isCompact`: points of a compact set that
  are not related to `z₀` are not related to any point near `z₀`.
* `TauCeti.exists_eventually_setOf_germFactorsThrough_eq_image`: the coincident-branch relation is
  locally trivial over a point whose fibre is immersed and whose class is finite.
* `TauCeti.eventually_ncard_setOf_germFactorsThrough_eq`: the number of coincident branches is
  locally constant there.
* `TauCeti.exists_pos_forall_ncard_setOf_germFactorsThrough_eq`: off the preimage of the critical
  values, every class of the coincident-branch relation has the same number `d ≥ 1` of elements.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Proposition 2.5.1 and its proof.
* C. Wendl, *Lectures on holomorphic curves in symplectic and contact geometry*, arXiv:1011.1690,
  Proposition 4.3.
-/

public section

open Set Filter Topology
open scoped Manifold ContDiff TauCeti.ComplexManifold

namespace TauCeti

open SmoothAlmostComplexStructure RiemannSurface

variable {S : Type*} [TopologicalSpace S] [ChartedSpace ℂ S] [IsManifold 𝓘(ℂ) ∞ S]
  {E H N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N]
  {J : SmoothAlmostComplexStructure I N} {u : S → N}

/-- **Unrelated points stay unrelated, uniformly on compact sets.** Let `u₀ : S → N` of class `C²`
and `u₁ : S' → N` of class `C¹` be pseudoholomorphic maps from Riemann surfaces into a Hausdorff
almost complex manifold, `z₀` a point of `S'` and `K ⊆ S` a compact set such that the branch of
`u₁` at `z₀` factors holomorphically through the branch of `u₀` at no point of `K`. If `u₀` is
immersed at the points of `K` where it takes the value `u₁ z₀`, then for every `z` near `z₀` the
branch of `u₁` at `z` factors through the branch of `u₀` at no point of `K`. -/
theorem eventually_forall_not_germFactorsThrough_of_isCompact [T2Space N]
    {S' : Type*} [TopologicalSpace S'] [ChartedSpace ℂ S'] [IsManifold 𝓘(ℂ) ∞ S']
    {u₀ : S → N} {u₁ : S' → N} (hu₀ : ContMDiff 𝓘(ℝ, ℂ) I 2 u₀)
    (hJu₀ : IsPseudoholomorphic (ofComplexManifold ℂ S) J u₀) (hu₁ : ContMDiff 𝓘(ℝ, ℂ) I 1 u₁)
    (hJu₁ : IsPseudoholomorphic (ofComplexManifold ℂ S') J u₁)
    {z₀ : S'} {K : Set S} (hK : IsCompact K) (hK₀ : ∀ y ∈ K, ¬GermFactorsThrough u₁ z₀ u₀ y)
    (himm : ∀ y ∈ K, u₀ y = u₁ z₀ → mfderiv 𝓘(ℝ, ℂ) I u₀ y ≠ 0) :
    ∀ᶠ z in 𝓝 z₀, ∀ y ∈ K, ¬GermFactorsThrough u₁ z u₀ y := by
  refine hK.eventually_forall_of_forall_eventually fun y hy ↦ ?_
  by_cases hyu : u₀ y = u₁ z₀
  · -- The point `y` is immersed, so `(y, z₀)` is not a limit of related pairs, by closedness of
    -- the relation at immersed points.
    have hcl : (y, z₀) ∉ closure {p : S × S' | GermFactorsThrough u₁ p.2 u₀ p.1} := fun h ↦
      hK₀ y hy (germFactorsThrough_of_mem_closure hu₀ hJu₀ hu₁ hJu₁ h (himm y hy hyu))
    rw [mem_closure_iff_frequently, not_frequently] at hcl
    exact (continuous_swap.tendsto (z₀, y)).eventually hcl
  · -- Related points have the same value, and nearby pairs keep different values.
    filter_upwards [(isOpen_ne_fun (hu₁.continuous.comp continuous_fst)
      (hu₀.continuous.comp continuous_snd)).mem_nhds (Ne.symm hyu)] with p hp hrel
    exact hp hrel.apply_eq

/-- **The coincident-branch relation is locally trivial.** Let `u : S → N` be a `C²`
pseudoholomorphic map from a compact Hausdorff Riemann surface into a Hausdorff almost complex
manifold, and let `z₀` be a point whose fibre `u⁻¹(u z₀)` consists of immersed points. Let `C` be
the set of points `ζ` such that the branch of `u` at `z₀` factors holomorphically through the
branch of `u` at `ζ`, and suppose that `C` is finite. Then there are maps `ψ ζ`, continuous at
`z₀` with `ψ ζ z₀ = ζ` for `ζ ∈ C`, such that for every `z` near `z₀` the points through whose
branch the branch of `u` at `z` factors are exactly the points `ψ ζ z`, `ζ ∈ C`, and these are
distinct. -/
theorem exists_eventually_setOf_germFactorsThrough_eq_image [CompactSpace S] [T2Space S]
    [T2Space N] (hu : ContMDiff 𝓘(ℝ, ℂ) I 2 u)
    (hJu : IsPseudoholomorphic (ofComplexManifold ℂ S) J u) {z₀ : S}
    (hfin : {ζ | GermFactorsThrough u z₀ u ζ}.Finite)
    (himm : ∀ ζ, u ζ = u z₀ → mfderiv 𝓘(ℝ, ℂ) I u ζ ≠ 0) :
    ∃ ψ : S → S → S,
      (∀ ζ ∈ {ζ | GermFactorsThrough u z₀ u ζ}, ψ ζ z₀ = ζ ∧ ContinuousAt (ψ ζ) z₀) ∧
      ∀ᶠ z in 𝓝 z₀, {ζ | GermFactorsThrough u z u ζ} =
          (fun ζ ↦ ψ ζ z) '' {ζ | GermFactorsThrough u z₀ u ζ} ∧
        InjOn (fun ζ ↦ ψ ζ z) {ζ | GermFactorsThrough u z₀ u ζ} := by
  set C := {ζ | GermFactorsThrough u z₀ u ζ}
  have hCfib : C ⊆ u ⁻¹' {u z₀} := fun ζ hζ ↦ (GermFactorsThrough.apply_eq hζ).symm
  -- The factorizations `u = u ∘ ψ ζ` near `z₀`, with `ψ ζ z₀ = ζ`, relate `z` to `ψ ζ z`.
  choose! ψ hψz₀ hψc hψr using fun ζ (hζ : ζ ∈ C) ↦
    GermFactorsThrough.exists_eventually_germFactorsThrough hζ
  -- Pairwise disjoint open neighbourhoods `V ζ` of the points of `C`, on which `u` is injective.
  choose! t ht htinj using fun ζ (hζ : ζ ∈ u ⁻¹' {u z₀}) ↦ (hu ζ).exists_mem_nhds_injOn
    two_ne_zero ((hJu.isPseudoholomorphicAt ζ).injective_mfderiv_iff_ne_zero.2 (himm ζ hζ))
  obtain ⟨U, hU, hUd⟩ := hfin.t2_separation
  set V : S → Set S := fun ζ ↦ U ζ ∩ interior (t ζ)
  have hVo : ∀ ζ, IsOpen (V ζ) := fun ζ ↦ (hU ζ).2.inter isOpen_interior
  have hVmem : ∀ ζ ∈ C, ζ ∈ V ζ := fun ζ hζ ↦
    ⟨(hU ζ).1, mem_interior_iff_mem_nhds.2 (ht ζ (hCfib hζ))⟩
  have hVinj : ∀ ζ ∈ C, InjOn u (V ζ) := fun ζ hζ ↦
    (htinj ζ (hCfib hζ)).mono fun _ h ↦ interior_subset h.2
  have hVd : C.PairwiseDisjoint V := hUd.mono fun _ ↦ inter_subset_left
  -- Near `z₀`, each `ψ ζ z` lies in `V ζ` and is related to `z`.
  have hlow : ∀ᶠ z in 𝓝 z₀, ∀ ζ ∈ C, ψ ζ z ∈ V ζ ∧ GermFactorsThrough u z u (ψ ζ z) :=
    (eventually_all_finite hfin).2 fun ζ hζ ↦ Eventually.and ((hψc ζ hζ).preimage_mem_nhds
      ((hVo ζ).mem_nhds (by rw [hψz₀ ζ hζ]; exact hVmem ζ hζ))) (hψr ζ hζ)
  -- Near `z₀`, no point outside the `V ζ` is related to `z`.
  have hup := eventually_forall_not_germFactorsThrough_of_isCompact hu hJu (hu.of_le one_le_two)
    hJu (isOpen_biUnion fun ζ _ ↦ hVo ζ).isClosed_compl.isCompact
    (fun y hy hyC ↦ hy (mem_biUnion (s := C) hyC (hVmem y hyC))) fun y _ ↦ himm y
  refine ⟨ψ, fun ζ hζ ↦ ⟨hψz₀ ζ hζ, hψc ζ hζ⟩, ?_⟩
  filter_upwards [hlow, hup] with z hlowz hupz
  refine ⟨Subset.antisymm (fun ζ' hζ' ↦ ?_) ?_, fun ζ₁ h₁ ζ₂ h₂ h ↦ ?_⟩
  · -- A point related to `z` lies in some `V ζ`, where `u` takes the value `u z` only at `ψ ζ z`.
    have hζ'V : ζ' ∈ ⋃ ζ ∈ C, V ζ := by
      by_contra h
      exact hupz ζ' h hζ'
    obtain ⟨ζ, hζ, hζ'ζ⟩ := mem_iUnion₂.1 hζ'V
    refine ⟨ζ, hζ, hVinj ζ hζ (hlowz ζ hζ).1 hζ'ζ ?_⟩
    exact (GermFactorsThrough.apply_eq (hlowz ζ hζ).2).symm.trans
      (GermFactorsThrough.apply_eq hζ')
  · rintro _ ⟨ζ, hζ, rfl⟩
    exact (hlowz ζ hζ).2
  · -- The points `ψ ζ z` lie in the pairwise disjoint sets `V ζ`.
    by_contra hne
    have h' : ψ ζ₁ z = ψ ζ₂ z := h
    exact Set.disjoint_left.1 (hVd h₁ h₂ hne) (hlowz ζ₁ h₁).1 (h' ▸ (hlowz ζ₂ h₂).1)

/-- **The number of coincident branches is locally constant.** Let `u : S → N` be a `C²`
pseudoholomorphic map from a compact Hausdorff Riemann surface into a Hausdorff almost complex
manifold, and let `z₀` be a point whose fibre `u⁻¹(u z₀)` consists of immersed points and which
is related to finitely many points. Then for `z` near `z₀` there are as many points through whose
branch the branch of `u` at `z` factors holomorphically as there are for `z₀`. -/
theorem eventually_ncard_setOf_germFactorsThrough_eq [CompactSpace S] [T2Space S] [T2Space N]
    (hu : ContMDiff 𝓘(ℝ, ℂ) I 2 u) (hJu : IsPseudoholomorphic (ofComplexManifold ℂ S) J u)
    {z₀ : S} (hfin : {ζ | GermFactorsThrough u z₀ u ζ}.Finite)
    (himm : ∀ ζ, u ζ = u z₀ → mfderiv 𝓘(ℝ, ℂ) I u ζ ≠ 0) :
    ∀ᶠ z in 𝓝 z₀, {ζ | GermFactorsThrough u z u ζ}.ncard =
      {ζ | GermFactorsThrough u z₀ u ζ}.ncard := by
  obtain ⟨ψ, -, h⟩ := exists_eventually_setOf_germFactorsThrough_eq_image hu hJu hfin himm
  filter_upwards [h] with z ⟨hz, hinj⟩
  rw [hz, hinj.ncard_image]

/-- **Coincident branches have constant multiplicity off the critical values.** Let `u : S → N` be
a nonconstant `C²` pseudoholomorphic map from a compact connected Hausdorff Riemann surface into a
Hausdorff almost complex manifold, and `B = u⁻¹(u(Crit u))` the preimage of its critical values.
There is a `d ≥ 1` such that for every `z ∉ B` there are exactly `d` points `ζ` such that the
branch of `u` at `z` factors holomorphically through the branch of `u` at `ζ`. -/
theorem exists_pos_forall_ncard_setOf_germFactorsThrough_eq [CompactSpace S] [ConnectedSpace S]
    [T2Space S] [T2Space N] (hu : ContMDiff 𝓘(ℝ, ℂ) I 2 u)
    (hJu : IsPseudoholomorphic (ofComplexManifold ℂ S) J u) (hne : ∃ x₁ x₂, u x₁ ≠ u x₂) :
    ∃ d : ℕ, 0 < d ∧ ∀ z ∉ u ⁻¹' (u '' {x | mfderiv 𝓘(ℝ, ℂ) I u x = 0}),
      {ζ | GermFactorsThrough u z u ζ}.ncard = d := by
  set B := u ⁻¹' (u '' {x | mfderiv 𝓘(ℝ, ℂ) I u x = 0})
  have hu₁ : ContMDiff 𝓘(ℝ, ℂ) I 1 u := hu.of_le one_le_two
  -- The classes are finite, the fibres off `B` are immersed, and `S \ B` is connected.
  have hfin : ∀ z, {ζ | GermFactorsThrough u z u ζ}.Finite := fun z ↦
    (finite_preimage_singleton_of_isPseudoholomorphic hu₁ hJu hne (u z)).subset
      fun ζ hζ ↦ (GermFactorsThrough.apply_eq hζ).symm
  have himm : ∀ z ∉ B, ∀ ζ, u ζ = u z → mfderiv 𝓘(ℝ, ℂ) I u ζ ≠ 0 :=
    fun z hz ζ hζ h0 ↦ hz ⟨ζ, h0, hζ⟩
  have hBc : IsConnected Bᶜ := isConnected_compl_of_finite_of_one_lt_rank (E := ℂ)
    (by rw [Complex.rank_real_complex]; exact Nat.one_lt_ofNat)
    (finite_preimage_image_setOf_mfderiv_eq_zero_of_isPseudoholomorphic hu₁ hJu hne)
  -- The count is locally constant on `S \ B`, hence constant there.
  have hcont : ContinuousOn (fun z ↦ {ζ | GermFactorsThrough u z u ζ}.ncard) Bᶜ :=
    fun z hz ↦ (continuousAt_const.congr (EventuallyEq.symm
      (eventually_ncard_setOf_germFactorsThrough_eq hu hJu (hfin z) (himm z hz))))
        |>.continuousWithinAt
  obtain ⟨z₁, hz₁⟩ := hBc.nonempty
  refine ⟨{ζ | GermFactorsThrough u z₁ u ζ}.ncard, ?_, fun z hz ↦
    hBc.isPreconnected.constant (Y := ℕ) hcont hz hz₁⟩
  -- The class of `z₁` is finite and contains `z₁`.
  exact (ncard_pos (hfin z₁)).2 ⟨z₁, .refl u z₁⟩

end TauCeti
