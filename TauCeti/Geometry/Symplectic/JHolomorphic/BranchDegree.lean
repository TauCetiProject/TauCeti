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
import TauCeti.Geometry.Manifold.ChartedSpace
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

The quotient `S / Γ` of McDuff–Salamon's construction is taken by the closure `Γ` of `Γ₀` in
`S × S` (`TauCeti.coincidentBranchClosure`), which also relates the points of the finite set `B`.
When `S` is compact, connected and Hausdorff and `u` is nonconstant, `Γ` is an equivalence relation
on `S` (`TauCeti.equivalence_coincidentBranchClosure`) with finite classes, `B` is a union of
classes, and off `B` the relation `Γ` is `Γ₀`. Reflexivity holds since `B` is finite, so every
point is a limit of points of `S \ B`. Transitivity at a point `b ∈ B` rests on the fact that `Γ`
propagates to nearby points: if `a` is related to `b`, then every point near `b` outside `B` has a
coincident branch near `a`
(`TauCeti.eventually_exists_germFactorsThrough_of_mem_coincidentBranchClosure`).
Indeed, choose a closed neighbourhood `T` of `a` meeting the fibre `u⁻¹(u b)` only at `a`, and a
connected punctured neighbourhood `P` of `b` avoiding `B` whose fibres stay in `interior T ∪ Tᶜ`.
The points of `P` with a coincident branch in `interior T` form an open subset of `P`, by
continuation of factorizations, and a closed one, since points unrelated to the compact set `T`
stay unrelated to it. This subset is not empty, as `(a, b)` is a limit of pairs of `Γ₀`, so it is
all of `P`.

## Main definitions

* `TauCeti.coincidentBranches`: the coincident-branch relation `Γ₀ ⊆ (S \ B) × (S \ B)`.
* `TauCeti.coincidentBranchClosure`: its closure `Γ` in `S × S`.

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
* `TauCeti.mem_coincidentBranchClosure_iff_of_notMem`: off `B` the closure `Γ` is `Γ₀`.
* `TauCeti.mem_criticalValuePreimage_iff_of_mem_coincidentBranchClosure`: `B` is invariant under
  `Γ`.
* `TauCeti.eventually_exists_germFactorsThrough_of_mem_coincidentBranchClosure`: `Γ` propagates to
  the points near `b` outside `B`.
* `TauCeti.equivalence_coincidentBranchClosure`: `Γ` is an equivalence relation on `S`.
* `TauCeti.finite_setOf_mem_coincidentBranchClosure`: the classes of `Γ` are finite.

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

/-! ### The closure of the coincident-branch relation -/

variable (I) in
/-- **The closure `Γ` of the coincident-branch relation** of a map `u : S → N` from a Riemann
surface: the closure in `S × S` of the pairs `(z, ζ)` with `z` outside the preimage
`B = u⁻¹(u(Crit u))` of the critical values such that the branch of `u` at `z` factors
holomorphically through the branch of `u` at `ζ`. These pairs are the coincident-branch relation
`Γ₀` (`TauCeti.coincidentBranches`) seen in `S × S`
(`TauCeti.coincidentBranchClosure_eq_closure_image`). For a nonconstant `C²` pseudoholomorphic
map from a compact connected Hausdorff Riemann surface, `Γ` is an equivalence relation on `S`
(`TauCeti.equivalence_coincidentBranchClosure`) with finite classes, which agrees with `Γ₀` off
`B`. -/
def coincidentBranchClosure (u : S → N) : Set (S × S) :=
  closure {p | p.1 ∉ criticalValuePreimage I u ∧ GermFactorsThrough u p.1 u p.2}

omit [IsManifold 𝓘(ℂ) ∞ S] [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ N] in
/-- Unfold `TauCeti.coincidentBranchClosure`. -/
theorem coincidentBranchClosure_def :
    coincidentBranchClosure I u =
      closure {p | p.1 ∉ criticalValuePreimage I u ∧ GermFactorsThrough u p.1 u p.2} :=
  (rfl)

omit [IsManifold 𝓘(ℂ) ∞ S] [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ N] in
/-- The closure `Γ` of the coincident-branch relation is the closure in `S × S` of the
coincident-branch relation `Γ₀ ⊆ (S \ B) × (S \ B)`. -/
theorem coincidentBranchClosure_eq_closure_image :
    coincidentBranchClosure I u = closure ((fun p : ↥(criticalValuePreimage I u)ᶜ ×
      ↥(criticalValuePreimage I u)ᶜ ↦ ((p.1 : S), (p.2 : S))) '' coincidentBranches I u) := by
  refine congrArg closure (Subset.antisymm (fun p hp ↦ ?_) ?_)
  · exact ⟨(⟨p.1, hp.1⟩, ⟨p.2, hp.2.notMem_criticalValuePreimage hp.1⟩), hp.2, rfl⟩
  · rintro _ ⟨q, hq, rfl⟩
    exact ⟨q.1.prop, hq⟩

omit [IsManifold 𝓘(ℂ) ∞ S] [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ N] in
/-- The closure `Γ` of the coincident-branch relation is closed. -/
theorem isClosed_coincidentBranchClosure : IsClosed (coincidentBranchClosure I u) :=
  isClosed_closure

omit [IsManifold 𝓘(ℂ) ∞ S] [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ N] in
/-- Coincident branches at a point outside `B = u⁻¹(u(Crit u))` are related by the closure `Γ`
of the coincident-branch relation. -/
theorem mem_coincidentBranchClosure_of_germFactorsThrough {z ζ : S}
    (hz : z ∉ criticalValuePreimage I u) (h : GermFactorsThrough u z u ζ) :
    (z, ζ) ∈ coincidentBranchClosure I u :=
  subset_closure ⟨hz, h⟩

omit [IsManifold 𝓘(ℂ) ∞ S] [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ N] in
/-- Points related by the closure `Γ` of the coincident-branch relation of a continuous map into a
Hausdorff space have the same image. -/
theorem apply_eq_of_mem_coincidentBranchClosure [T2Space N] (hu : Continuous u) {p : S × S}
    (hp : p ∈ coincidentBranchClosure I u) : u p.1 = u p.2 :=
  closure_minimal (s := {q : S × S | q.1 ∉ criticalValuePreimage I u ∧
    GermFactorsThrough u q.1 u q.2})
    (t := {q : S × S | u q.1 = u q.2}) (fun _ hq ↦ GermFactorsThrough.apply_eq hq.2)
    (isClosed_eq (hu.comp continuous_fst) (hu.comp continuous_snd)) hp

omit [IsManifold 𝓘(ℂ) ∞ S] [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ N] in
/-- **The preimage of the critical values is invariant under `Γ`.** A point related by the
closure `Γ` of the coincident-branch relation to a point of `B = u⁻¹(u(Crit u))` lies in `B`. -/
theorem mem_criticalValuePreimage_iff_of_mem_coincidentBranchClosure [T2Space N]
    (hu : Continuous u) {p : S × S} (hp : p ∈ coincidentBranchClosure I u) :
    p.1 ∈ criticalValuePreimage I u ↔ p.2 ∈ criticalValuePreimage I u :=
  mem_criticalValuePreimage_iff_of_apply_eq (apply_eq_of_mem_coincidentBranchClosure hu hp)

/-- **Off the critical values, `Γ` is the coincident-branch relation.** For a `C²`
pseudoholomorphic map into a Hausdorff almost complex manifold and a point `z` outside
`B = u⁻¹(u(Crit u))`, the pair `(z, ζ)` lies in the closure `Γ` of the coincident-branch relation
exactly when the branch of `u` at `z` factors holomorphically through the branch of `u` at `ζ`. -/
theorem mem_coincidentBranchClosure_iff_of_notMem [T2Space N] (hu : ContMDiff 𝓘(ℝ, ℂ) I 2 u)
    (hJu : IsPseudoholomorphic (ofComplexManifold ℂ S) J u) {z ζ : S}
    (hz : z ∉ criticalValuePreimage I u) :
    (z, ζ) ∈ coincidentBranchClosure I u ↔ GermFactorsThrough u z u ζ := by
  refine ⟨fun h ↦ ?_, mem_coincidentBranchClosure_of_germFactorsThrough hz⟩
  -- `ζ` has the value of `z`, so it is immersed, and the relation is closed at immersed points.
  have hζ : ζ ∉ criticalValuePreimage I u :=
    (mem_criticalValuePreimage_iff_of_mem_coincidentBranchClosure hu.continuous h).not.1 hz
  exact germFactorsThrough_of_mem_closure hu hJu (hu.of_le one_le_two) hJu
    (map_mem_closure (f := Prod.swap) continuous_swap h fun _ hq ↦ hq.2)
    (mfderiv_ne_zero_of_notMem_criticalValuePreimage hζ)

/-- **`Γ` is reflexive.** For a nonconstant `C¹` pseudoholomorphic map from a compact connected
Riemann surface, every point `z` is related to itself by the closure `Γ` of the coincident-branch
relation, being a limit of points outside the finite set `B = u⁻¹(u(Crit u))`. -/
theorem mem_coincidentBranchClosure_self [CompactSpace S] [PreconnectedSpace S]
    (hu : ContMDiff 𝓘(ℝ, ℂ) I 1 u) (hJu : IsPseudoholomorphic (ofComplexManifold ℂ S) J u)
    (hne : ∃ x₁ x₂, u x₁ ≠ u x₂) (z : S) : (z, z) ∈ coincidentBranchClosure I u := by
  have := ChartedSpace.t1Space ℂ S
  have : PerfectSpace S := ChartedSpace.perfectSpace (H := ℂ)
  -- Every neighbourhood of `z` is infinite, so it meets the complement of the finite set `B`.
  have hz : z ∈ closure (criticalValuePreimage I u)ᶜ := mem_closure_iff_nhds.2 fun W hW ↦
    ((infinite_of_mem_nhds z hW).sdiff (finite_criticalValuePreimage hu hJu hne)).nonempty
  exact map_mem_closure (f := fun y ↦ (y, y)) (continuous_id.prodMk continuous_id) hz
    fun y hy ↦ ⟨hy, .refl u y⟩

/-- **`Γ` is symmetric.** For a `C²` pseudoholomorphic map, the closure `Γ` of the
coincident-branch relation is invariant under `(z, ζ) ↦ (ζ, z)`. -/
theorem swap_mem_coincidentBranchClosure (hu : ContMDiff 𝓘(ℝ, ℂ) I 2 u)
    (hJu : IsPseudoholomorphic (ofComplexManifold ℂ S) J u) {p : S × S}
    (hp : p ∈ coincidentBranchClosure I u) : p.swap ∈ coincidentBranchClosure I u :=
  map_mem_closure (f := Prod.swap) continuous_swap hp fun _ hq ↦
    ⟨hq.2.notMem_criticalValuePreimage hq.1, hq.2.symm (hu.of_le one_le_two) hJu hu hJu
      (mfderiv_ne_zero_of_notMem_criticalValuePreimage hq.1)⟩

/-- For a nonconstant pseudoholomorphic map from a compact connected Riemann surface, every point
`a` has arbitrarily small closed neighbourhoods `T` such that, for any point `b`, every point with
the value `u z` lies in `interior T` or outside `T` for all `z` near `b`. -/
private theorem exists_isClosed_mem_nhds_eventually_preimage_subset [CompactSpace S]
    [PreconnectedSpace S] [T2Space S] [T2Space N] (hu : ContMDiff 𝓘(ℝ, ℂ) I 1 u)
    (hJu : IsPseudoholomorphic (ofComplexManifold ℂ S) J u) (hne : ∃ x₁ x₂, u x₁ ≠ u x₂)
    {a b : S} {W : Set S} (hW : W ∈ 𝓝 a) :
    ∃ T ∈ 𝓝 a, IsClosed T ∧ T ⊆ W ∧ ∀ᶠ z in 𝓝 b, u ⁻¹' {u z} ⊆ interior T ∪ Tᶜ := by
  have := ChartedSpace.t1Space ℂ S
  -- A closed neighbourhood `T ⊆ W` of `a` meeting the finite fibre `u⁻¹(u b)` only at `a`.
  have hF := finite_preimage_singleton_of_isPseudoholomorphic hu hJu hne (u b)
  obtain ⟨T, hT, hTc, hTsub⟩ := exists_mem_nhds_isClosed_subset (inter_mem hW
    ((hF.sdiff (t := {a})).isClosed.compl_mem_nhds fun h ↦ h.2 rfl))
  have hFT : u ⁻¹' {u b} ⊆ interior T ∪ Tᶜ := fun y hy ↦ by
    rcases eq_or_ne y a with rfl | hya
    · exact Or.inl (mem_interior_iff_mem_nhds.2 hT)
    · exact Or.inr fun hyT ↦ (hTsub hyT).2 ⟨hy, hya⟩
  -- Near `u b` the fibres of `u` stay in `interior T ∪ Tᶜ`, since `u` is a closed map.
  have hK : IsClosed (u '' (interior T ∪ Tᶜ)ᶜ) := hu.continuous.isClosedMap _
    (isOpen_interior.union hTc.isOpen_compl).isClosed_compl
  refine ⟨T, hT, hTc, fun y hy ↦ (hTsub hy).1, ?_⟩
  filter_upwards [hu.continuous.continuousAt.preimage_mem_nhds
    (hK.isOpen_compl.mem_nhds fun ⟨y, hy, hyb⟩ ↦ hy (hFT hyb))] with z hz y hy
  by_contra h
  exact hz ⟨y, h, hy⟩

/-- Let `T` be a closed subset of a compact Riemann surface and `z` a point outside
`B = u⁻¹(u(Crit u))` whose fibre lies in `interior T ∪ Tᶜ`. If the branch of `u` at `z` factors
through its branch at no point of `interior T`, the same holds at every point near `z`. -/
private theorem eventually_not_exists_germFactorsThrough_of_preimage_subset [CompactSpace S]
    [T2Space N] (hu : ContMDiff 𝓘(ℝ, ℂ) I 2 u)
    (hJu : IsPseudoholomorphic (ofComplexManifold ℂ S) J u) {T : Set S} (hTc : IsClosed T) {z : S}
    (hzB : z ∉ criticalValuePreimage I u) (hzT : u ⁻¹' {u z} ⊆ interior T ∪ Tᶜ)
    (hz : ¬∃ ζ ∈ interior T, GermFactorsThrough u z u ζ) :
    ∀ᶠ y in 𝓝 z, ¬∃ ζ ∈ interior T, GermFactorsThrough u y u ζ := by
  -- The branch at `z` factors through no branch at a point of `T`: such a point has the value of
  -- `z`, so it lies in `interior T`.
  have hzT' : ∀ y ∈ T, ¬GermFactorsThrough u z u y := fun y hyT hzy ↦
    hz ⟨y, (hzT hzy.apply_eq.symm).resolve_right (not_not.2 hyT), hzy⟩
  filter_upwards [eventually_forall_not_germFactorsThrough_of_isCompact hu hJu (hu.of_le one_le_two)
    hJu hTc.isCompact hzT' fun y _ hy ↦ mfderiv_ne_zero_of_notMem_criticalValuePreimage
      ((mem_criticalValuePreimage_iff_of_apply_eq hy).not.2 hzB)] with y hy ⟨ζ, hζ, hyζ⟩
  exact hy ζ (interior_subset hζ) hyζ

/-- **The relation `Γ` propagates to nearby points.** Let `u` be a nonconstant `C²`
pseudoholomorphic map from a compact connected Hausdorff Riemann surface into a Hausdorff almost
complex manifold, and let `a` and `b` be related by the closure `Γ` of the coincident-branch
relation. For every neighbourhood `W` of `a`, the branch of `u` at every point `z` near `b` outside
`B = u⁻¹(u(Crit u))` factors holomorphically through its branch at some point of `W`. -/
theorem eventually_exists_germFactorsThrough_of_mem_coincidentBranchClosure [CompactSpace S]
    [PreconnectedSpace S] [T2Space S] [T2Space N] (hu : ContMDiff 𝓘(ℝ, ℂ) I 2 u)
    (hJu : IsPseudoholomorphic (ofComplexManifold ℂ S) J u) (hne : ∃ x₁ x₂, u x₁ ≠ u x₂)
    {a b : S} (hab : (a, b) ∈ coincidentBranchClosure I u) {W : Set S} (hW : W ∈ 𝓝 a) :
    ∀ᶠ z in 𝓝 b, z ∉ criticalValuePreimage I u → ∃ ζ ∈ W, GermFactorsThrough u z u ζ := by
  have := ChartedSpace.t1Space ℂ S
  set B := criticalValuePreimage I u
  have hu₁ : ContMDiff 𝓘(ℝ, ℂ) I 1 u := hu.of_le one_le_two
  have hval : u a = u b := apply_eq_of_mem_coincidentBranchClosure hu.continuous hab
  by_cases hb : b ∉ B
  · -- Off `B`, a factorization of the branch at `b` through the branch at `a` continues nearby.
    have ha : a ∉ B := (mem_criticalValuePreimage_iff_of_apply_eq hval).not.2 hb
    have hba : GermFactorsThrough u b u a :=
      ((mem_coincidentBranchClosure_iff_of_notMem hu hJu ha).1 hab).symm hu₁ hJu hu hJu
        (mfderiv_ne_zero_of_notMem_criticalValuePreimage ha)
    filter_upwards [hba.eventually_exists_germFactorsThrough hW] with z hz _ using hz
  rw [not_not] at hb
  -- A closed neighbourhood `T ⊆ W` of `a`, and a connected punctured neighbourhood `V \ {b}` of
  -- `b` avoiding `B` whose fibres lie in `interior T ∪ Tᶜ`.
  obtain ⟨T, hT, hTc, hTW, hTfib⟩ :=
    exists_isClosed_mem_nhds_eventually_preimage_subset (b := b) hu₁ hJu hne hW
  obtain ⟨V, hV, hVU, hVc⟩ := exists_mem_nhds_subset_isConnected_sdiff_singleton (E := ℂ)
    (by rw [Complex.rank_real_complex]; exact Nat.one_lt_ofNat) b (inter_mem hTfib
      (((finite_criticalValuePreimage hu₁ hJu hne).sdiff (t := {b})).isClosed.compl_mem_nhds
        fun h ↦ h.2 rfl))
  have hP : ∀ z ∈ V, z ∉ B → z ∈ V \ {b} := fun z hzV hzB ↦ ⟨hzV, fun h ↦ hzB (h ▸ hb)⟩
  -- The points with a coincident branch in `interior T` form an open set `R`, by continuation of
  -- factorizations, whose complement is open near the points of `V \ {b}`, since points unrelated
  -- to the compact set `T` stay unrelated to it.
  set R := {z | ∃ ζ ∈ interior T, GermFactorsThrough u z u ζ}
  have hRo : ∀ z ∈ R, R ∈ 𝓝 z := fun _ ⟨_, hζ, hzζ⟩ ↦
    hzζ.eventually_exists_germFactorsThrough (isOpen_interior.mem_nhds hζ)
  have hRc : ∀ z ∈ V \ {b}, z ∉ R → Rᶜ ∈ 𝓝 z := fun z hz hzR ↦
    eventually_not_exists_germFactorsThrough_of_preimage_subset hu hJu hTc
      (fun h ↦ (hVU hz.1).2 ⟨h, hz.2⟩) (hVU hz.1).1 hzR
  -- `R` meets `V \ {b}`, as `a` and `b` are limits of related points, so it contains `V \ {b}`.
  obtain ⟨⟨α, β⟩, ⟨hα, hβ⟩, hαB, hαβ⟩ := mem_closure_iff_nhds.1 hab _ (prod_mem_nhds
    (isOpen_interior.mem_nhds (mem_interior_iff_mem_nhds.2 hT)) (interior_mem_nhds.2 hV))
  have hβR : β ∈ R := ⟨α, hα, hαβ.symm hu₁ hJu hu hJu
    (mfderiv_ne_zero_of_notMem_criticalValuePreimage hαB)⟩
  have hPR : V \ {b} ⊆ interior R :=
    hVc.isPreconnected.subset_left_of_subset_union isOpen_interior isOpen_interior
      (disjoint_compl_right.mono interior_subset interior_subset)
      (fun z hz ↦ (em (z ∈ R)).imp (fun h ↦ mem_interior_iff_mem_nhds.2 (hRo z h))
        fun h ↦ mem_interior_iff_mem_nhds.2 (hRc z hz h))
      ⟨β, hP β (interior_subset hβ) (hαβ.notMem_criticalValuePreimage hαB),
        mem_interior_iff_mem_nhds.2 (hRo β hβR)⟩
  filter_upwards [hV] with z hzV hzB
  obtain ⟨ζ, hζ, hzζ⟩ := interior_subset (hPR (hP z hzV hzB))
  exact ⟨ζ, hTW (interior_subset hζ), hzζ⟩

/-- **`Γ` is transitive.** For a nonconstant `C²` pseudoholomorphic map `u` from a compact connected
Hausdorff Riemann surface into a Hausdorff almost complex manifold, the closure `Γ` of the
coincident-branch relation is transitive. -/
theorem mem_coincidentBranchClosure_trans [CompactSpace S] [PreconnectedSpace S] [T2Space S]
    [T2Space N]
    (hu : ContMDiff 𝓘(ℝ, ℂ) I 2 u) (hJu : IsPseudoholomorphic (ofComplexManifold ℂ S) J u)
    (hne : ∃ x₁ x₂, u x₁ ≠ u x₂) {a b c : S} (hab : (a, b) ∈ coincidentBranchClosure I u)
    (hbc : (b, c) ∈ coincidentBranchClosure I u) : (a, c) ∈ coincidentBranchClosure I u := by
  refine mem_closure_iff_nhds.2 fun t ht ↦ ?_
  obtain ⟨Wa, hWa, Wc, hWc, hWt⟩ := mem_nhds_prod_iff.1 ht
  -- A point `β` near `b` related to a point `γ` near `c` is related to a point `α` near `a`.
  obtain ⟨⟨β, γ⟩, ⟨hβ, hγ⟩, hβB, hβγ⟩ := mem_closure_iff_nhds.1 hbc _ (prod_mem_nhds
    (eventually_exists_germFactorsThrough_of_mem_coincidentBranchClosure hu hJu hne hab hWa) hWc)
  obtain ⟨α, hα, hβα⟩ := hβ hβB
  exact ⟨(α, γ), hWt ⟨hα, hγ⟩, hβα.notMem_criticalValuePreimage hβB,
    (hβα.symm (hu.of_le one_le_two) hJu hu hJu
      (mfderiv_ne_zero_of_notMem_criticalValuePreimage hβB)).trans hβγ⟩

/-- **The closure of the coincident-branch relation is an equivalence relation.** For a
nonconstant `C²` pseudoholomorphic map `u` from a compact connected Hausdorff Riemann surface into
a Hausdorff almost complex manifold, the closure `Γ` in `S × S` of the coincident-branch relation
is an equivalence relation on `S`. Its classes are finite
(`TauCeti.finite_setOf_mem_coincidentBranchClosure`), the preimage `B = u⁻¹(u(Crit u))` of the
critical values is a union of classes
(`TauCeti.mem_criticalValuePreimage_iff_of_mem_coincidentBranchClosure`), and off `B` it is the
coincident-branch relation (`TauCeti.mem_coincidentBranchClosure_iff_of_notMem`). -/
theorem equivalence_coincidentBranchClosure [CompactSpace S] [PreconnectedSpace S] [T2Space S]
    [T2Space N] (hu : ContMDiff 𝓘(ℝ, ℂ) I 2 u)
    (hJu : IsPseudoholomorphic (ofComplexManifold ℂ S) J u) (hne : ∃ x₁ x₂, u x₁ ≠ u x₂) :
    Equivalence fun z ζ : S ↦ (z, ζ) ∈ coincidentBranchClosure I u :=
  ⟨mem_coincidentBranchClosure_self (hu.of_le one_le_two) hJu hne,
    fun h ↦ swap_mem_coincidentBranchClosure hu hJu h,
    mem_coincidentBranchClosure_trans hu hJu hne⟩

/-- **The classes of `Γ` are finite.** For a nonconstant `C¹` pseudoholomorphic map from a compact
connected Riemann surface into a Hausdorff almost complex manifold, each point is related to
finitely many points by the closure `Γ` of the coincident-branch relation, since related points
have the same image. -/
theorem finite_setOf_mem_coincidentBranchClosure [CompactSpace S] [PreconnectedSpace S]
    [T2Space N] (hu : ContMDiff 𝓘(ℝ, ℂ) I 1 u)
    (hJu : IsPseudoholomorphic (ofComplexManifold ℂ S) J u) (hne : ∃ x₁ x₂, u x₁ ≠ u x₂) (z : S) :
    {ζ | (z, ζ) ∈ coincidentBranchClosure I u}.Finite :=
  (finite_preimage_singleton_of_isPseudoholomorphic hu hJu hne (u z)).subset fun _ hζ ↦
    (apply_eq_of_mem_coincidentBranchClosure hu.continuous hζ).symm

end TauCeti
