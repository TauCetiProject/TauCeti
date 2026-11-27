/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Covering.Basic
public import Mathlib.Topology.Maps.Proper.Basic
public import TauCeti.Geometry.Symplectic.JHolomorphic.RiemannSurface
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import TauCeti.Topology.Covering.Proper
import TauCeti.Geometry.Manifold.Connected
import TauCeti.Geometry.Manifold.MFDeriv.LocalInjectivity

/-!
# The coincident branches of a closed pseudoholomorphic curve

Let `S` be a compact connected Hausdorff Riemann surface, `N` a Hausdorff manifold with a smooth
almost complex structure `J`, and `u : S → N` a nonconstant pseudoholomorphic map of class `C²`.
Its critical values have the finite preimage `B = u⁻¹(u(Crit u))`
(`TauCeti.criticalValuePreimage`, `TauCeti.finite_criticalValuePreimage`). On `S \ B` the
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

The relation is moreover a covering of `S \ B`. As a subset `Γ₀` of `(S \ B) × (S \ B)`
(`TauCeti.coincidentBranches`), its first projection `(z, ζ) ↦ z` is a proper covering map with
finite fibres (`TauCeti.isCoveringMap_fst_coincidentBranches`) for every `C²` pseudoholomorphic map
from a compact Hausdorff Riemann surface, connected or not; when `S` is connected and `u`
nonconstant, its fibres all have `d` points. This is the covering from which the quotient
`S / Γ` of McDuff–Salamon's construction is built.

* **Properness.** `Γ₀` is closed in `(S \ B) × S`, by closedness of the relation at immersed points
  (`TauCeti.germFactorsThrough_of_mem_closure`), and the projection `(S \ B) × S → S \ B` is
  proper because `S` is compact.
* **Local homeomorphism.** At a pair `(z₀, ζ₀)` of `Γ₀`, a holomorphic factorization `u = u ∘ φ`
  near `z₀` with `φ z₀ = ζ₀` gives the local inverse `z ↦ (z, φ z)`, and `u` is injective near the
  immersed point `ζ₀`, so `(z, φ z)` is the only pair over `z` near `(z₀, ζ₀)`.

A proper local homeomorphism with Hausdorff domain is a covering map
(`IsLocalHomeomorph.isCoveringMap_of_isProperMap`), and a proper covering map has finite fibres
(`IsCoveringMap.isProperMap_iff_finite_fiber`).

## Main definitions

* `TauCeti.coincidentBranches`: the coincident-branch relation `Γ₀ ⊆ (S \ B) × (S \ B)`.

## Main results

* `TauCeti.eventually_forall_not_germFactorsThrough_of_isCompact`: points of a compact set that
  are not related to `z₀` are not related to any point near `z₀`.
* `TauCeti.exists_eventually_setOf_germFactorsThrough_eq_image`: the coincident-branch relation is
  locally trivial over a point whose fibre is immersed and whose class is finite.
* `TauCeti.eventually_ncard_setOf_germFactorsThrough_eq`: the number of coincident branches is
  locally constant there.
* `TauCeti.exists_pos_forall_ncard_setOf_germFactorsThrough_eq`: off the preimage of the critical
  values, every class of the coincident-branch relation has the same number `d ≥ 1` of elements.
* `TauCeti.equivalence_coincidentBranches`, `TauCeti.isClosed_coincidentBranches`: `Γ₀` is a
  closed equivalence relation on `S \ B`.
* `TauCeti.isProperMap_fst_coincidentBranches`, `TauCeti.isLocalHomeomorph_fst_coincidentBranches`:
  the first projection of `Γ₀` is proper and a local homeomorphism.
* `TauCeti.isCoveringMap_fst_coincidentBranches`, `TauCeti.finite_preimage_fst_coincidentBranches`:
  the first projection of `Γ₀` is a covering map with finite fibres.
* `TauCeti.exists_pos_forall_ncard_preimage_fst_coincidentBranches`: when `S` is connected and `u`
  nonconstant, all its fibres have the same number `d ≥ 1` of points.

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

/-! ### The number of coincident branches -/

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
    ∃ d : ℕ, 0 < d ∧ ∀ z ∉ criticalValuePreimage I u,
      {ζ | GermFactorsThrough u z u ζ}.ncard = d := by
  set B := criticalValuePreimage I u
  have hu₁ : ContMDiff 𝓘(ℝ, ℂ) I 1 u := hu.of_le one_le_two
  -- The classes are finite, the fibres off `B` are immersed, and `S \ B` is connected.
  have hfin : ∀ z, {ζ | GermFactorsThrough u z u ζ}.Finite := fun z ↦
    (finite_preimage_singleton_of_isPseudoholomorphic hu₁ hJu hne (u z)).subset
      fun ζ hζ ↦ (GermFactorsThrough.apply_eq hζ).symm
  have himm : ∀ z ∉ B, ∀ ζ, u ζ = u z → mfderiv 𝓘(ℝ, ℂ) I u ζ ≠ 0 :=
    fun z hz ζ hζ h0 ↦ hz (mem_criticalValuePreimage.2 ⟨ζ, h0, hζ⟩)
  have hBc : IsConnected Bᶜ := isConnected_compl_of_finite_of_one_lt_rank (E := ℂ)
    (by rw [Complex.rank_real_complex]; exact Nat.one_lt_ofNat)
    (finite_criticalValuePreimage hu₁ hJu hne)
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


/-! ### The coincident-branch relation as a covering -/

variable (I) in
/-- **The coincident-branch relation** `Γ₀` of a map `u : S → N` from a Riemann surface, on the
complement `S \ B` of the preimage `B = u⁻¹(u(Crit u))` of its critical values: the pairs
`(z, ζ)` such that the branch of `u` at `z` factors holomorphically through the branch of `u` at
`ζ`. For a pseudoholomorphic `u` of class `C²` it is a closed equivalence relation
(`TauCeti.equivalence_coincidentBranches`, `TauCeti.isClosed_coincidentBranches`). -/
def coincidentBranches (u : S → N) :
    Set (↥(criticalValuePreimage I u)ᶜ × ↥(criticalValuePreimage I u)ᶜ) :=
  {p | GermFactorsThrough u (p.1 : S) u (p.2 : S)}

omit [IsManifold 𝓘(ℂ) ∞ S] [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ N] in
@[simp]
theorem mem_coincidentBranches
    {p : ↥(criticalValuePreimage I u)ᶜ × ↥(criticalValuePreimage I u)ᶜ} :
    p ∈ coincidentBranches I u ↔ GermFactorsThrough u (p.1 : S) u (p.2 : S) :=
  Iff.rfl

/-- **The coincident-branch relation is an equivalence relation** on the complement of the
preimage of the critical values of a `C²` pseudoholomorphic map from a Riemann surface. -/
theorem equivalence_coincidentBranches (hu : ContMDiff 𝓘(ℝ, ℂ) I 2 u)
    (hJu : IsPseudoholomorphic (ofComplexManifold ℂ S) J u) :
    Equivalence fun z ζ : ↥(criticalValuePreimage I u)ᶜ ↦ (z, ζ) ∈ coincidentBranches I u :=
  ⟨fun z ↦ .refl u z,
    fun {z _} h ↦ h.symm (hu.of_le one_le_two) hJu hu hJu
      (mfderiv_ne_zero_of_notMem_criticalValuePreimage z.prop),
    fun h₁ h₂ ↦ h₁.trans h₂⟩

/-- The pairs `(z, ζ)` with `z ∉ u⁻¹(u(Crit u))` such that the branch of `u` at `z` factors
holomorphically through the branch of `u` at `ζ` form a closed subset of `(S \ B) × S`. -/
private theorem isClosed_setOf_germFactorsThrough_compl_criticalValuePreimage [T2Space N]
    (hu : ContMDiff 𝓘(ℝ, ℂ) I 2 u) (hJu : IsPseudoholomorphic (ofComplexManifold ℂ S) J u) :
    IsClosed {p : ↥(criticalValuePreimage I u)ᶜ × S | GermFactorsThrough u (p.1 : S) u p.2} := by
  refine isClosed_of_closure_subset fun p hp ↦ ?_
  -- Related points have the same value, so `p.2` lies in the fibre of `p.1`, which is immersed.
  have hcl : IsClosed {q : ↥(criticalValuePreimage I u)ᶜ × S | u q.1 = u q.2} :=
    isClosed_eq (hu.continuous.comp (continuous_subtypeVal.comp continuous_fst))
      (hu.continuous.comp continuous_snd)
  have hval : u p.1 = u p.2 :=
    closure_minimal (s := {q : ↥(criticalValuePreimage I u)ᶜ × S | GermFactorsThrough u q.1 u q.2})
      (fun q hq ↦ GermFactorsThrough.apply_eq hq) hcl hp
  refine germFactorsThrough_of_mem_closure hu hJu (hu.of_le one_le_two) hJu ?_
    (mfderiv_ne_zero_of_notMem_criticalValuePreimage
      ((mem_criticalValuePreimage_iff_of_apply_eq hval).not.1 p.1.prop))
  exact map_mem_closure (f := fun q : ↥(criticalValuePreimage I u)ᶜ × S ↦ (q.2, (q.1 : S)))
    (continuous_snd.prodMk (continuous_subtypeVal.comp continuous_fst)) hp fun _ hq ↦ hq

/-- **The coincident-branch relation is closed** in `(S \ B) × (S \ B)`, for a `C²`
pseudoholomorphic map into a Hausdorff almost complex manifold. -/
theorem isClosed_coincidentBranches [T2Space N] (hu : ContMDiff 𝓘(ℝ, ℂ) I 2 u)
    (hJu : IsPseudoholomorphic (ofComplexManifold ℂ S) J u) :
    IsClosed (coincidentBranches I u) :=
  (isClosed_setOf_germFactorsThrough_compl_criticalValuePreimage hu hJu).preimage
    (continuous_fst.prodMk (continuous_subtypeVal.comp continuous_snd))

/-- **The first projection of the coincident-branch relation is proper.** For a `C²`
pseudoholomorphic map `u` from a compact Riemann surface into a Hausdorff almost complex manifold,
the projection `(z, ζ) ↦ z` from the coincident-branch relation `Γ₀` onto `S \ B` is a proper map.
-/
theorem isProperMap_fst_coincidentBranches [CompactSpace S] [T2Space N]
    (hu : ContMDiff 𝓘(ℝ, ℂ) I 2 u) (hJu : IsPseudoholomorphic (ofComplexManifold ℂ S) J u) :
    IsProperMap fun p : coincidentBranches I u ↦ p.val.1 := by
  -- `Γ₀` is a closed subset of `(S \ B) × S`, over which the first projection is proper.
  set ι : coincidentBranches I u → ↥(criticalValuePreimage I u)ᶜ × S := fun p ↦ (p.val.1, p.val.2)
  have hrange : range ι = {q | GermFactorsThrough u (q.1 : S) u q.2} := by
    refine Subset.antisymm (range_subset_iff.2 fun p ↦ p.prop) fun q hq ↦ ?_
    exact ⟨⟨(q.1, ⟨q.2, hq.notMem_criticalValuePreimage q.1.prop⟩), hq⟩, rfl⟩
  have hι : IsClosedEmbedding ι :=
    ⟨(IsEmbedding.id.prodMap IsEmbedding.subtypeVal).comp IsEmbedding.subtypeVal,
      hrange ▸ isClosed_setOf_germFactorsThrough_compl_criticalValuePreimage hu hJu⟩
  exact (isProperMap_fst_of_compactSpace (X := ↥(criticalValuePreimage I u)ᶜ) (Y := S)).comp
    hι.isProperMap

omit [FiniteDimensional ℝ E] [I.Boundaryless] in
/-- A coincidence `(z₀, ζ₀)` of branches of a `C¹` pseudoholomorphic map, immersed at `ζ₀`, has a
local section: a map `φ` and open neighbourhoods `W` of `z₀` and `V` of `ζ₀` such that `u` is
injective on `V`, and on `W` the map `φ` is continuous, takes values in `V` and relates each point
`y` to `φ y`. -/
private theorem exists_isOpen_forall_germFactorsThrough (hu : ContMDiff 𝓘(ℝ, ℂ) I 1 u)
    (hJu : IsPseudoholomorphic (ofComplexManifold ℂ S) J u) {z₀ ζ₀ : S}
    (hp : GermFactorsThrough u z₀ u ζ₀) (hζ₀ : mfderiv 𝓘(ℝ, ℂ) I u ζ₀ ≠ 0) :
    ∃ (φ : S → S) (W V : Set S), IsOpen W ∧ z₀ ∈ W ∧ IsOpen V ∧ ζ₀ ∈ V ∧ InjOn u V ∧
      ∀ y ∈ W, ContinuousAt φ y ∧ φ y ∈ V ∧ GermFactorsThrough u y u (φ y) := by
  -- `u` is injective near the immersed point `ζ₀`.
  obtain ⟨t, ht, htinj⟩ := (hu ζ₀).exists_mem_nhds_injOn one_ne_zero
    ((hJu.isPseudoholomorphicAt ζ₀).injective_mfderiv_iff_ne_zero.2 hζ₀)
  -- A factorization `u = u ∘ φ` near `z₀` relates each nearby point `y` to `φ y`.
  obtain ⟨φ, hφz₀, hφd, hφu⟩ := germFactorsThrough_iff.1 hp
  have hφt : ∀ᶠ y in 𝓝 z₀, φ y ∈ interior t :=
    hφd.self_of_nhds.continuousAt.preimage_mem_nhds (hφz₀ ▸ interior_mem_nhds.2 ht)
  have hev : ∀ᶠ y in 𝓝 z₀,
      ContinuousAt φ y ∧ φ y ∈ interior t ∧ GermFactorsThrough u y u (φ y) := by
    filter_upwards [hφd.eventually_nhds, hφu.eventually_nhds, hφt] with y hyd hyu hyt
    exact ⟨hyd.self_of_nhds.continuousAt, hyt, germFactorsThrough_iff.2 ⟨φ, rfl, hyd, hyu⟩⟩
  obtain ⟨W, hWsub, hWo, hz₀W⟩ := eventually_nhds_iff.1 hev
  exact ⟨φ, W, interior t, hWo, hz₀W, isOpen_interior, mem_interior_iff_mem_nhds.2 ht,
    htinj.mono interior_subset, hWsub⟩

omit [FiniteDimensional ℝ E] [I.Boundaryless] in
/-- **The first projection of the coincident-branch relation is a local homeomorphism.** For a
`C¹` pseudoholomorphic map `u` from a Riemann surface into an almost complex manifold, the
projection `(z, ζ) ↦ z` from the coincident-branch relation `Γ₀` onto `S \ B` is a local
homeomorphism. -/
theorem isLocalHomeomorph_fst_coincidentBranches (hu : ContMDiff 𝓘(ℝ, ℂ) I 1 u)
    (hJu : IsPseudoholomorphic (ofComplexManifold ℂ S) J u) :
    IsLocalHomeomorph fun p : coincidentBranches I u ↦ p.val.1 := by
  classical
  rintro ⟨⟨z₀, ζ₀⟩, hp⟩
  obtain ⟨φ, W, V, hWo, hz₀W, hVo, hζ₀V, hVinj, hWsub⟩ :=
    exists_isOpen_forall_germFactorsThrough hu hJu hp
      (mfderiv_ne_zero_of_notMem_criticalValuePreimage ζ₀.prop)
  -- The local inverse `z ↦ (z, φ z)` over `W`.
  let sec : ↥(criticalValuePreimage I u)ᶜ → coincidentBranches I u := fun z ↦
    if hz : (z : S) ∈ W then
      ⟨(z, ⟨φ z, (hWsub z hz).2.2.notMem_criticalValuePreimage z.prop⟩), (hWsub z hz).2.2⟩
    else ⟨(z₀, ζ₀), hp⟩
  have hsec {z : ↥(criticalValuePreimage I u)ᶜ} (hz : (z : S) ∈ W) :
      ((sec z).val.1 : S) = z ∧ ((sec z).val.2 : S) = φ z := by
    simp only [sec, hz, ↓reduceDIte, and_self]
  have hsecc {z : ↥(criticalValuePreimage I u)ᶜ} (hz : (z : S) ∈ W) : ContinuousAt sec z := by
    have hW : ∀ᶠ z' : ↥(criticalValuePreimage I u)ᶜ in 𝓝 z, (z' : S) ∈ W :=
      continuous_subtypeVal.continuousAt.preimage_mem_nhds (hWo.mem_nhds hz)
    refine IsInducing.subtypeVal.continuousAt_iff.2 (ContinuousAt.prodMk ?_ ?_)
    · refine continuousAt_id.congr ?_
      filter_upwards [hW] with z' hz'
      exact Subtype.ext (hsec hz').1.symm
    · refine IsInducing.subtypeVal.continuousAt_iff.2
        (((hWsub z hz).1.comp continuous_subtypeVal.continuousAt).congr ?_)
      filter_upwards [hW] with z' hz'
      exact (hsec hz').2.symm
  refine ⟨{
    toFun := fun p ↦ p.val.1
    invFun := sec
    source := {q | ((q.val.1 : S) ∈ W) ∧ (q.val.2 : S) ∈ V}
    target := {z | (z : S) ∈ W}
    map_source' := fun q hq ↦ hq.1
    map_target' := fun z hz ↦ ⟨(hsec hz).1 ▸ hz, (hsec hz).2 ▸ (hWsub z hz).2.1⟩
    left_inv' := fun q hq ↦ by
      -- `φ q₁` and `q₂` are points of `V` with the same value, so they agree.
      have hW := hWsub _ hq.1
      refine Subtype.ext (Prod.ext (Subtype.ext (hsec hq.1).1) (Subtype.ext ?_))
      rw [(hsec hq.1).2]
      exact hVinj hW.2.1 hq.2
        (hW.2.2.apply_eq.symm.trans (GermFactorsThrough.apply_eq q.prop))
    right_inv' := fun z hz ↦ Subtype.ext (hsec hz).1
    open_source := (hWo.preimage (continuous_subtypeVal.comp
      (continuous_fst.comp continuous_subtypeVal))).inter (hVo.preimage
        (continuous_subtypeVal.comp (continuous_snd.comp continuous_subtypeVal)))
    open_target := hWo.preimage continuous_subtypeVal
    continuousOn_toFun := (continuous_fst.comp continuous_subtypeVal).continuousOn
    continuousOn_invFun := fun z hz ↦ (hsecc hz).continuousWithinAt }, ?_, rfl⟩
  exact ⟨hz₀W, hζ₀V⟩

/-- **The coincident-branch relation is a finite covering.** For a `C²` pseudoholomorphic map `u`
from a compact Hausdorff Riemann surface into a Hausdorff almost complex manifold, the projection
`(z, ζ) ↦ z` from the coincident-branch relation `Γ₀` onto the complement `S \ B` of the preimage
of the critical values is a covering map. It is proper
(`TauCeti.isProperMap_fst_coincidentBranches`) with finite fibres
(`TauCeti.finite_preimage_fst_coincidentBranches`), and when `S` is connected and `u` nonconstant
all its fibres have the same number `d ≥ 1` of points
(`TauCeti.exists_pos_forall_ncard_preimage_fst_coincidentBranches`). -/
theorem isCoveringMap_fst_coincidentBranches [CompactSpace S] [T2Space S] [T2Space N]
    (hu : ContMDiff 𝓘(ℝ, ℂ) I 2 u) (hJu : IsPseudoholomorphic (ofComplexManifold ℂ S) J u) :
    IsCoveringMap fun p : coincidentBranches I u ↦ p.val.1 :=
  (isLocalHomeomorph_fst_coincidentBranches (hu.of_le one_le_two) hJu).isCoveringMap_of_isProperMap
    (isProperMap_fst_coincidentBranches hu hJu)

/-- **The coincident-branch relation has finite fibres.** For a `C²` pseudoholomorphic map from a
compact Hausdorff Riemann surface into a Hausdorff almost complex manifold, every fibre of the
first projection of the coincident-branch relation `Γ₀` onto `S \ B` is finite. -/
theorem finite_preimage_fst_coincidentBranches [CompactSpace S] [T2Space S] [T2Space N]
    (hu : ContMDiff 𝓘(ℝ, ℂ) I 2 u) (hJu : IsPseudoholomorphic (ofComplexManifold ℂ S) J u)
    (z : ↥(criticalValuePreimage I u)ᶜ) :
    ((fun p : coincidentBranches I u ↦ p.val.1) ⁻¹' {z}).Finite :=
  finite_coe_iff.1 <| (isCoveringMap_fst_coincidentBranches hu hJu).isProperMap_iff_finite_fiber.1
    (isProperMap_fst_coincidentBranches hu hJu) z

omit [IsManifold 𝓘(ℂ) ∞ S] [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ N] in
/-- The fibre over `z` of the first projection of the coincident-branch relation has as many
points as there are points `ζ` such that the branch of `u` at `z` factors holomorphically through
the branch of `u` at `ζ`. -/
theorem ncard_preimage_fst_coincidentBranches (z : ↥(criticalValuePreimage I u)ᶜ) :
    ((fun p : coincidentBranches I u ↦ p.val.1) ⁻¹' {z}).ncard =
      {ζ | GermFactorsThrough u z u ζ}.ncard := by
  -- The second projection identifies the fibre with the class of `z`.
  have himage : (fun p : coincidentBranches I u ↦ (p.val.2 : S)) ''
      ((fun p : coincidentBranches I u ↦ p.val.1) ⁻¹' {z}) = {ζ | GermFactorsThrough u z u ζ} := by
    refine Subset.antisymm ?_ fun ζ hζ ↦ ?_
    · rintro _ ⟨p, hp, rfl⟩
      rw [mem_preimage, mem_singleton_iff] at hp
      exact hp ▸ p.prop
    · exact ⟨⟨(z, ⟨ζ, hζ.notMem_criticalValuePreimage z.prop⟩), hζ⟩, rfl, rfl⟩
  rw [← himage, InjOn.ncard_image]
  intro p hp q hq h
  rw [mem_preimage, mem_singleton_iff] at hp hq
  exact Subtype.ext (Prod.ext (hp.trans hq.symm) (Subtype.ext h))

/-- **The coincident-branch covering has constant degree.** For a nonconstant `C²`
pseudoholomorphic map from a compact connected Hausdorff Riemann surface into a Hausdorff almost
complex manifold, all the fibres of the first projection of the coincident-branch relation `Γ₀`
onto `S \ B` have the same number `d ≥ 1` of points. -/
theorem exists_pos_forall_ncard_preimage_fst_coincidentBranches [CompactSpace S]
    [ConnectedSpace S] [T2Space S] [T2Space N] (hu : ContMDiff 𝓘(ℝ, ℂ) I 2 u)
    (hJu : IsPseudoholomorphic (ofComplexManifold ℂ S) J u) (hne : ∃ x₁ x₂, u x₁ ≠ u x₂) :
    ∃ d : ℕ, 0 < d ∧ ∀ z : ↥(criticalValuePreimage I u)ᶜ,
      ((fun p : coincidentBranches I u ↦ p.val.1) ⁻¹' {z}).ncard = d := by
  obtain ⟨d, hd, h⟩ := exists_pos_forall_ncard_setOf_germFactorsThrough_eq hu hJu hne
  exact ⟨d, hd, fun z ↦ (ncard_preimage_fst_coincidentBranches z).trans (h z z.prop)⟩

end TauCeti
