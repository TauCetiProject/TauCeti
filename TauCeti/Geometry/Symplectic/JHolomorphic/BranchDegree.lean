/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Covering.Basic
public import Mathlib.Topology.Maps.Proper.Basic
public import TauCeti.Geometry.Symplectic.JHolomorphic.RiemannSurface
import Mathlib.Data.Set.Card.Arithmetic
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

A similar argument counts partners. The number of partners near `z` of a point `w ∉ B` near `z` is
eventually a constant `e_z`, the local multiplicity (`TauCeti.coincidentBranchMultiplicity`). It is
positive, and equal to `1` off `B`. Over each class of `Γ` the multiplicities add up to `d`
(`TauCeti.finsum_mem_coincidentBranchMultiplicity_eq`): the partners of a point `w ∉ B` near `z` lie
near the points of the class of `z`, and near each such point `ζ` they number `e_ζ`, since `w` has
the partners of a point near `ζ`. In McDuff–Salamon's construction of the quotient `S / Γ`, these
are the local degrees of the branched cover `S → S / Γ` of degree `d`, which this file does not
construct.

## Main definitions

* `TauCeti.coincidentBranches`: the coincident-branch relation `Γ₀ ⊆ (S \ B) × (S \ B)`.
* `TauCeti.coincidentBranchClosure`: its closure `Γ` in `S × S`.
* `TauCeti.coincidentBranchMultiplicity`: the local multiplicities `e_z`.

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
* `TauCeti.exists_mem_nhds_forall_eventually_ncard_eq_coincidentBranchMultiplicity`: `e_z` is the
  number of partners near `z` of the points off `B` near `z`.
* `TauCeti.coincidentBranchMultiplicity_pos`,
  `TauCeti.coincidentBranchMultiplicity_eq_one_of_notMem`: the local multiplicities are positive,
  and equal to `1` off `B`.
* `TauCeti.finsum_mem_coincidentBranchMultiplicity_eq`: over each class of `Γ` they add up to `d`.

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

/-- For a nonconstant `C¹` pseudoholomorphic map from a compact connected Riemann surface, the
branch of `u` at `w` factors holomorphically through the branches of `u` at finitely many points:
they lie in the fibre of `u w`. -/
private theorem finite_setOf_germFactorsThrough [CompactSpace S] [PreconnectedSpace S]
    (hu : ContMDiff 𝓘(ℝ, ℂ) I 1 u) (hJu : IsPseudoholomorphic (ofComplexManifold ℂ S) J u)
    (hne : ∃ x₁ x₂, u x₁ ≠ u x₂) (w : S) : {y | GermFactorsThrough u w u y}.Finite :=
  (finite_preimage_singleton_of_isPseudoholomorphic hu hJu hne (u w)).subset fun _ hy ↦
    (GermFactorsThrough.apply_eq hy).symm

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
  have hfin : ∀ z, {ζ | GermFactorsThrough u z u ζ}.Finite :=
    finite_setOf_germFactorsThrough hu₁ hJu hne
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
    fun {z _} h ↦ h.symm_of_notMem_criticalValuePreimage hu hJu z.prop,
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
map from a compact connected Hausdorff Riemann surface into a Hausdorff almost complex manifold,
`Γ` is an equivalence relation on `S` (`TauCeti.equivalence_coincidentBranchClosure`) with finite
classes, which agrees with `Γ₀` off `B`. -/
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
    ⟨hq.2.notMem_criticalValuePreimage hq.1, hq.2.symm_of_notMem_criticalValuePreimage hu hJu hq.1⟩

/-- For a nonconstant pseudoholomorphic map `u` from a compact connected Riemann surface and
points `a`, `b`, every neighbourhood of `a` contains a closed neighbourhood `T` of `a` such that
`u⁻¹(u z) ⊆ interior T ∪ Tᶜ` for all `z` near `b`. -/
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
  -- Near `u b` the fibres of `u` stay in the open set `interior T ∪ Tᶜ`, since `u` is a closed map.
  exact ⟨T, hT, hTc, fun y hy ↦ (hTsub hy).1, (hu.continuous.tendsto b).eventually
    (hu.continuous.isClosedMap.eventually_nhds_fiber (p := (· ∈ interior T ∪ Tᶜ)) (u b)
      fun y hy ↦ (isOpen_interior.union hTc.isOpen_compl).mem_nhds (hFT hy))⟩

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
      ((mem_coincidentBranchClosure_iff_of_notMem hu hJu ha).1 hab)
        |>.symm_of_notMem_criticalValuePreimage hu hJu ha
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
  have hβR : β ∈ R := ⟨α, hα, hαβ.symm_of_notMem_criticalValuePreimage hu hJu hαB⟩
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
    (hβα.symm_of_notMem_criticalValuePreimage hu hJu hβB).trans hβγ⟩

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

/-- For a nonconstant `C¹` pseudoholomorphic map from a compact connected Riemann surface, the
points near `z` other than `z` lie outside the finite set `u⁻¹(u(Crit u))`. -/
private theorem compl_criticalValuePreimage_mem_nhdsNE [CompactSpace S] [PreconnectedSpace S]
    (hu : ContMDiff 𝓘(ℝ, ℂ) I 1 u) (hJu : IsPseudoholomorphic (ofComplexManifold ℂ S) J u)
    (hne : ∃ x₁ x₂, u x₁ ≠ u x₂) (z : S) : (criticalValuePreimage I u)ᶜ ∈ 𝓝[≠] z := by
  have := ChartedSpace.t1Space ℂ S
  simpa [← compl_eq_univ_sdiff] using nhdsNE_of_nhdsNE_sdiff_finite (x := z) univ_mem
    (finite_criticalValuePreimage hu hJu hne).to_subtype

/-- For a nonconstant `C¹` pseudoholomorphic map from a compact connected Riemann surface, a
property holding near `z` holds at some point outside `u⁻¹(u(Crit u))`. -/
private theorem exists_notMem_criticalValuePreimage_of_eventually [CompactSpace S]
    [PreconnectedSpace S] (hu : ContMDiff 𝓘(ℝ, ℂ) I 1 u)
    (hJu : IsPseudoholomorphic (ofComplexManifold ℂ S) J u) (hne : ∃ x₁ x₂, u x₁ ≠ u x₂) {z : S}
    {P : S → Prop} (h : ∀ᶠ w in 𝓝 z, P w) : ∃ w ∉ criticalValuePreimage I u, P w := by
  have : PerfectSpace S := ChartedSpace.perfectSpace (H := ℂ)
  obtain ⟨w, hw, hwB⟩ := ((h.filter_mono nhdsWithin_le_nhds).and
    (compl_criticalValuePreimage_mem_nhdsNE hu hJu hne z)).exists
  exact ⟨w, hwB, hw⟩

/-- For a nonconstant `C¹` pseudoholomorphic map from a compact connected Hausdorff Riemann
surface, every neighbourhood of `ξ` contains an open neighbourhood `W'` of `ξ` whose closure meets
the fibre `u⁻¹(u ξ)` only at `ξ`, since that fibre is finite. -/
private theorem exists_isOpen_forall_mem_closure_apply_eq_imp_eq [CompactSpace S]
    [PreconnectedSpace S] [T2Space S] (hu : ContMDiff 𝓘(ℝ, ℂ) I 1 u)
    (hJu : IsPseudoholomorphic (ofComplexManifold ℂ S) J u) (hne : ∃ x₁ x₂, u x₁ ≠ u x₂)
    {ξ : S} {W : Set S} (hW : W ∈ 𝓝 ξ) :
    ∃ W' ⊆ W, IsOpen W' ∧ ξ ∈ W' ∧ ∀ y ∈ closure W', u y = u ξ → y = ξ := by
  have hF : (u ⁻¹' {u ξ} \ {ξ}).Finite :=
    (finite_preimage_singleton_of_isPseudoholomorphic hu hJu hne (u ξ)).sdiff
  obtain ⟨C, hC, hCc, hCW⟩ := exists_mem_nhds_isClosed_subset
    (inter_mem hW (hF.isClosed.isOpen_compl.mem_nhds fun h ↦ h.2 rfl))
  refine ⟨interior C, interior_subset.trans (hCW.trans inter_subset_left), isOpen_interior,
    mem_interior_iff_mem_nhds.2 hC, fun y hy hyu ↦ by_contra fun h ↦ ?_⟩
  exact (hCW (closure_minimal interior_subset hCc hy)).2 ⟨hyu, h⟩

/-- For a nonconstant `C¹` pseudoholomorphic map from a compact connected Riemann surface, every
neighbourhood of `ζ` contains an open neighbourhood `D` of `ζ` such that `D \ u⁻¹(u(Crit u))` is
preconnected: a connected open neighbourhood, from which a finite set is removed. -/
private theorem exists_isOpen_isPreconnected_sdiff_criticalValuePreimage [CompactSpace S]
    [PreconnectedSpace S] (hu : ContMDiff 𝓘(ℝ, ℂ) I 1 u)
    (hJu : IsPseudoholomorphic (ofComplexManifold ℂ S) J u) (hne : ∃ x₁ x₂, u x₁ ≠ u x₂)
    {ζ : S} {O : Set S} (hO : O ∈ 𝓝 ζ) :
    ∃ D ⊆ O, IsOpen D ∧ ζ ∈ D ∧ IsPreconnected (D \ criticalValuePreimage I u) := by
  have := ChartedSpace.locallyConnectedSpace ℂ S
  have := ChartedSpace.t1Space ℂ S
  have hB := finite_criticalValuePreimage hu hJu hne
  obtain ⟨D, ⟨hDo, hζD, hDc⟩, hDO⟩ := (LocallyConnectedSpace.open_connected_basis ζ).mem_iff.1 hO
  exact ⟨D, hDO, hDo, hζD, isPreconnected_sdiff_of_isOpen_of_isDiscrete_of_one_lt_rank (E := ℂ)
    (by rw [Complex.rank_real_complex]; exact Nat.one_lt_ofNat) hDo hDc.isPreconnected
    hB.isClosed hB.isDiscrete⟩

/-- For a nonconstant `C¹` pseudoholomorphic map from a compact connected Hausdorff Riemann
surface and points `ζ`, `ξ` with the same value, every neighbourhood of `ξ` contains an open
neighbourhood `W'` of `ξ` whose closure meets the fibre `u⁻¹(u ξ)` only at `ξ`, and `ζ` has an open
neighbourhood `D` with `D \ u⁻¹(u(Crit u))` preconnected on which `u` takes no value that it takes
on the frontier of `W'`. -/
private theorem exists_isOpen_isPreconnected_sdiff_forall_notMem_image_frontier [CompactSpace S]
    [PreconnectedSpace S] [T2Space S] [T2Space N] (hu : ContMDiff 𝓘(ℝ, ℂ) I 1 u)
    (hJu : IsPseudoholomorphic (ofComplexManifold ℂ S) J u) (hne : ∃ x₁ x₂, u x₁ ≠ u x₂)
    {ζ ξ : S} (hζξ : u ζ = u ξ) {W : Set S} (hW : W ∈ 𝓝 ξ) :
    ∃ W' ⊆ W, IsOpen W' ∧ ξ ∈ W' ∧ (∀ y ∈ closure W', u y = u ξ → y = ξ) ∧
      ∃ D, IsOpen D ∧ ζ ∈ D ∧ IsPreconnected (D \ criticalValuePreimage I u) ∧
        ∀ w ∈ D, u w ∉ u '' frontier W' := by
  obtain ⟨W', hW'W, hW'o, hξW', hW'F⟩ :=
    exists_isOpen_forall_mem_closure_apply_eq_imp_eq hu hJu hne hW
  have huK : u ζ ∉ u '' frontier W' := fun ⟨y, hy, hyu⟩ ↦
    hy.2 (by rw [hW'o.interior_eq]; exact hW'F y hy.1 (hyu.trans hζξ) ▸ hξW')
  obtain ⟨D, hDO, hDo, hζD, hs⟩ := exists_isOpen_isPreconnected_sdiff_criticalValuePreimage hu hJu
    hne (hu.continuous.continuousAt.preimage_mem_nhds
      ((isClosed_frontier.isCompact.image hu.continuous).isClosed.isOpen_compl.mem_nhds huK))
  exact ⟨W', hW'W, hW'o, hξW', hW'F, D, hDo, hζD, hs, fun _ hw ↦ hDO hw⟩

/-- **Properties of the partners propagate along `Γ`.** Let `u` be a nonconstant `C²`
pseudoholomorphic map from a compact connected Hausdorff Riemann surface into a Hausdorff almost
complex manifold, and `(z, ζ)` a pair of `Γ`. If the set of partners of every point
`w' ∉ u⁻¹(u(Crit u))` near `ζ` has a property `P`, so has the set of partners of every point
`w ∉ u⁻¹(u(Crit u))` near `z`: such a `w` has a partner `w'` near `ζ`, and related points off
`u⁻¹(u(Crit u))` have the same partners. -/
private theorem eventually_of_mem_coincidentBranchClosure [CompactSpace S] [PreconnectedSpace S]
    [T2Space S] [T2Space N] (hu : ContMDiff 𝓘(ℝ, ℂ) I 2 u)
    (hJu : IsPseudoholomorphic (ofComplexManifold ℂ S) J u) (hne : ∃ x₁ x₂, u x₁ ≠ u x₂)
    {z ζ : S} (h : (z, ζ) ∈ coincidentBranchClosure I u) {P : Set S → Prop}
    (hP : ∀ᶠ w' in 𝓝 ζ, w' ∉ criticalValuePreimage I u → P {y | GermFactorsThrough u w' u y}) :
    ∀ᶠ w in 𝓝 z, w ∉ criticalValuePreimage I u → P {y | GermFactorsThrough u w u y} := by
  filter_upwards [eventually_exists_germFactorsThrough_of_mem_coincidentBranchClosure hu hJu hne
    (swap_mem_coincidentBranchClosure hu hJu h) hP] with w hw hwB
  obtain ⟨w', hw'P, hww'⟩ := hw hwB
  have hw'w : GermFactorsThrough u w' u w := hww'.symm_of_notMem_criticalValuePreimage hu hJu hwB
  have hpart : {y | GermFactorsThrough u w u y} = {y | GermFactorsThrough u w' u y} :=
    ext fun y ↦ ⟨hw'w.trans, hww'.trans⟩
  exact hpart ▸ hw'P (hww'.notMem_criticalValuePreimage hwB)

/-! ### Local multiplicities -/

/-- The number of points of an open set `V` through whose branch the branch of `u` at `w` factors
holomorphically is locally constant at a point `w ∉ u⁻¹(u(Crit u))` none of whose partners lies on
the frontier of `V`: by the local triviality of `Γ₀`, the partners of nearby points stay inside or
outside `V` with the partners of `w`. -/
private theorem eventually_ncard_inter_setOf_germFactorsThrough_eq [CompactSpace S]
    [PreconnectedSpace S] [T2Space S] [T2Space N] (hu : ContMDiff 𝓘(ℝ, ℂ) I 2 u)
    (hJu : IsPseudoholomorphic (ofComplexManifold ℂ S) J u) (hne : ∃ x₁ x₂, u x₁ ≠ u x₂)
    {w : S} (hw : w ∉ criticalValuePreimage I u) {V : Set S} (hV : IsOpen V)
    (hfr : ∀ y ∈ frontier V, ¬GermFactorsThrough u w u y) :
    ∀ᶠ w' in 𝓝 w, (V ∩ {y | GermFactorsThrough u w' u y}).ncard =
      (V ∩ {y | GermFactorsThrough u w u y}).ncard := by
  set C := {ζ | GermFactorsThrough u w u ζ}
  obtain ⟨ψ, hψ, hev⟩ := exists_eventually_setOf_germFactorsThrough_eq_image hu hJu
    (finite_setOf_germFactorsThrough (hu.of_le one_le_two) hJu hne w)
    fun ζ hζ h0 ↦ hw (mem_criticalValuePreimage.2 ⟨ζ, h0, hζ⟩)
  -- For `w'` near `w`, each partner `ψ ζ w'` lies in `V` exactly when `ζ` does.
  have hV' : ∀ᶠ w' in 𝓝 w, ∀ ζ ∈ C, (ψ ζ w' ∈ V ↔ ζ ∈ V) := by
    refine (eventually_all_finite (finite_setOf_germFactorsThrough (hu.of_le one_le_two) hJu hne
      w)).2 fun ζ hζ ↦ ?_
    obtain ⟨hψζ, hψc⟩ := hψ ζ hζ
    by_cases hζV : ζ ∈ V
    · filter_upwards [hψc.preimage_mem_nhds (hV.mem_nhds (by rwa [hψζ]))] with w' hw'
        using iff_of_true hw' hζV
    · have hζc : ζ ∉ closure V := fun h ↦ hfr ζ ⟨h, by rwa [hV.interior_eq]⟩ hζ
      filter_upwards [hψc.preimage_mem_nhds (isClosed_closure.isOpen_compl.mem_nhds
        (by rwa [hψζ]))] with w' hw' using iff_of_false (fun h ↦ hw' (subset_closure h)) hζV
  filter_upwards [hev, hV'] with w' ⟨hw'eq, hinj⟩ hw'V
  have himage : V ∩ {y | GermFactorsThrough u w' u y} = (fun ζ ↦ ψ ζ w') '' (C ∩ V) := by
    rw [hw'eq]
    ext y
    constructor
    · rintro ⟨hyV, ζ, hζ, rfl⟩
      exact ⟨ζ, ⟨hζ, (hw'V ζ hζ).1 hyV⟩, rfl⟩
    · rintro ⟨ζ, ⟨hζ, hζV⟩, rfl⟩
      exact ⟨(hw'V ζ hζ).2 hζV, ζ, hζ, rfl⟩
  rw [himage, (hinj.mono inter_subset_left).ncard_image, inter_comm]

/-- A neighbourhood `V` of `z` and a number `n` such that for every smaller neighbourhood `V'` of
`z`, every point `w ∉ u⁻¹(u(Crit u))` near `z` has exactly `n` partners in `V'`. -/
private theorem exists_mem_nhds_forall_eventually_ncard_eq [CompactSpace S] [PreconnectedSpace S]
    [T2Space S] [T2Space N] (hu : ContMDiff 𝓘(ℝ, ℂ) I 2 u)
    (hJu : IsPseudoholomorphic (ofComplexManifold ℂ S) J u) (hne : ∃ x₁ x₂, u x₁ ≠ u x₂) (z : S) :
    ∃ V ∈ 𝓝 z, ∃ n : ℕ, ∀ V' ∈ 𝓝 z, V' ⊆ V → ∀ᶠ w in 𝓝 z, w ∉ criticalValuePreimage I u →
      (V' ∩ {y | GermFactorsThrough u w u y}).ncard = n := by
  set B := criticalValuePreimage I u
  have hu₁ : ContMDiff 𝓘(ℝ, ℂ) I 1 u := hu.of_le one_le_two
  -- An open neighbourhood `W'` of `z` whose closure meets the fibre `u⁻¹(u z)` only at `z`, and a
  -- neighbourhood `D` of `z` with `D \ B` preconnected on which `u` avoids `u '' frontier W'`.
  obtain ⟨W', -, hW'o, hzW', hW'F, D, hDo, hzD, hs, hDK⟩ :=
    exists_isOpen_isPreconnected_sdiff_forall_notMem_image_frontier hu₁ hJu hne rfl univ_mem
  -- No point of `D` has a partner on the frontier of `W'`, so the number of partners in `W'` is
  -- locally constant on `D \ B`, hence constant.
  have hcont : ContinuousOn (fun w ↦ (W' ∩ {y | GermFactorsThrough u w u y}).ncard) (D \ B) :=
    fun w ⟨hwD, hwB⟩ ↦ (continuousAt_const.congr (EventuallyEq.symm
      (eventually_ncard_inter_setOf_germFactorsThrough_eq hu hJu hne hwB hW'o
        fun y hy hwy ↦ hDK w hwD ⟨y, hy, hwy.apply_eq.symm⟩))).continuousWithinAt
  obtain ⟨w₀, hw₀B, hw₀D⟩ :=
    exists_notMem_criticalValuePreimage_of_eventually hu₁ hJu hne (hDo.mem_nhds hzD)
  refine ⟨W', hW'o.mem_nhds hzW', (W' ∩ {y | GermFactorsThrough u w₀ u y}).ncard,
    fun V' hV' hV'W' ↦ ?_⟩
  -- For `w` near `z`, the partners of `w` in `W'` lie in `V'`, since `u` takes the value `u z` at
  -- no point of `closure W'` outside the interior of `V'`.
  have hK' : IsCompact (closure W' \ interior V') :=
    (isClosed_closure.sdiff isOpen_interior).isCompact
  have huK' : u z ∉ u '' (closure W' \ interior V') := fun ⟨y, ⟨hy, hyV'⟩, hyu⟩ ↦
    hyV' (hW'F y hy hyu ▸ mem_interior_iff_mem_nhds.2 hV')
  filter_upwards [hDo.mem_nhds hzD, hu.continuous.continuousAt.preimage_mem_nhds
    ((hK'.image hu.continuous).isClosed.isOpen_compl.mem_nhds huK')] with w hwD hwK' hwB
  have heq : V' ∩ {y | GermFactorsThrough u w u y} = W' ∩ {y | GermFactorsThrough u w u y} := by
    refine Subset.antisymm (inter_subset_inter_left _ hV'W') fun y ⟨hyW', hy⟩ ↦ ⟨?_, hy⟩
    by_contra hyV'
    exact hwK' ⟨y, ⟨subset_closure hyW', fun h ↦ hyV' (interior_subset h)⟩, hy.apply_eq.symm⟩
  rw [heq]
  exact hs.constant hcont ⟨hwD, hwB⟩ ⟨hw₀D, hw₀B⟩

variable (I) in
/-- **The local multiplicity `e_z` of the coincident-branch relation** of a map `u : S → N` at a
point `z`: the number of points near `z` through whose branch the branch of `u` at a point
`w ∉ u⁻¹(u(Crit u))` near `z` factors holomorphically. For a nonconstant `C²` pseudoholomorphic map
from a compact connected Hausdorff Riemann surface into a Hausdorff almost complex manifold, this
number is the same for all small neighbourhoods of `z` and all such `w` near `z`
(`TauCeti.exists_mem_nhds_forall_eventually_ncard_eq_coincidentBranchMultiplicity`). It is
positive (`TauCeti.coincidentBranchMultiplicity_pos`), it is `1` off `u⁻¹(u(Crit u))`
(`TauCeti.coincidentBranchMultiplicity_eq_one_of_notMem`), and over each class of the closure `Γ`
of the coincident-branch relation it sums to the number `d` of coincident branches
(`TauCeti.finsum_mem_coincidentBranchMultiplicity_eq`). In McDuff–Salamon's construction of the
quotient `S / Γ`, it is the local degree at `z` of the branched cover `S → S / Γ`. -/
noncomputable def coincidentBranchMultiplicity (u : S → N) (z : S) : ℕ :=
  sInf {n | ∃ V ∈ 𝓝 z, ∀ᶠ w in 𝓝 z, w ∉ criticalValuePreimage I u →
    (V ∩ {y | GermFactorsThrough u w u y}).ncard ≤ n}

/-- **The local multiplicity counts the partners nearby.** For a nonconstant `C²`
pseudoholomorphic map `u` from a compact connected Hausdorff Riemann surface into a Hausdorff
almost complex manifold, every point `z` has a neighbourhood `V` such that for every neighbourhood
`V' ⊆ V` of `z`, every point `w ∉ u⁻¹(u(Crit u))` near `z` has exactly `e_z` points in `V'` through
whose branch the branch of `u` at `w` factors holomorphically. -/
theorem exists_mem_nhds_forall_eventually_ncard_eq_coincidentBranchMultiplicity [CompactSpace S]
    [PreconnectedSpace S] [T2Space S] [T2Space N] (hu : ContMDiff 𝓘(ℝ, ℂ) I 2 u)
    (hJu : IsPseudoholomorphic (ofComplexManifold ℂ S) J u) (hne : ∃ x₁ x₂, u x₁ ≠ u x₂) (z : S) :
    ∃ V ∈ 𝓝 z, ∀ V' ∈ 𝓝 z, V' ⊆ V → ∀ᶠ w in 𝓝 z, w ∉ criticalValuePreimage I u →
      (V' ∩ {y | GermFactorsThrough u w u y}).ncard = coincidentBranchMultiplicity I u z := by
  obtain ⟨V, hV, n, h⟩ := exists_mem_nhds_forall_eventually_ncard_eq hu hJu hne z
  have hmem : n ∈ {n | ∃ V ∈ 𝓝 z, ∀ᶠ w in 𝓝 z, w ∉ criticalValuePreimage I u →
      (V ∩ {y | GermFactorsThrough u w u y}).ncard ≤ n} :=
    ⟨V, hV, (h V hV subset_rfl).mono fun _ hw hwB ↦ (hw hwB).le⟩
  -- Every bound `m` on the counts in some neighbourhood `V''` bounds the count `n` in `V'' ∩ V`.
  have hn : coincidentBranchMultiplicity I u z = n := by
    refine le_antisymm (Nat.sInf_le hmem) (le_csInf ⟨n, hmem⟩ fun m ⟨V'', hV'', hm⟩ ↦ ?_)
    obtain ⟨w, hwB, hw₁, hw₂⟩ := exists_notMem_criticalValuePreimage_of_eventually
      (hu.of_le one_le_two) hJu hne ((h _ (inter_mem hV'' hV) inter_subset_right).and hm)
    calc n = (V'' ∩ V ∩ {y | GermFactorsThrough u w u y}).ncard := (hw₁ hwB).symm
      _ ≤ (V'' ∩ {y | GermFactorsThrough u w u y}).ncard :=
        ncard_le_ncard (inter_subset_inter_left _ inter_subset_left)
          ((finite_setOf_germFactorsThrough (hu.of_le one_le_two) hJu hne w).inter_of_right _)
      _ ≤ m := hw₂ hwB
  exact hn ▸ ⟨V, hV, h⟩

/-- **The local multiplicities are positive**, for a nonconstant `C²` pseudoholomorphic map from a
compact connected Hausdorff Riemann surface into a Hausdorff almost complex manifold: each point
`w ∉ u⁻¹(u(Crit u))` near `z` is its own partner. -/
theorem coincidentBranchMultiplicity_pos [CompactSpace S] [PreconnectedSpace S] [T2Space S]
    [T2Space N] (hu : ContMDiff 𝓘(ℝ, ℂ) I 2 u)
    (hJu : IsPseudoholomorphic (ofComplexManifold ℂ S) J u) (hne : ∃ x₁ x₂, u x₁ ≠ u x₂) (z : S) :
    0 < coincidentBranchMultiplicity I u z := by
  obtain ⟨V, hV, h⟩ :=
    exists_mem_nhds_forall_eventually_ncard_eq_coincidentBranchMultiplicity hu hJu hne z
  obtain ⟨w, hwB, hw, hwV⟩ := exists_notMem_criticalValuePreimage_of_eventually
    (hu.of_le one_le_two) hJu hne ((h V hV subset_rfl).and hV)
  rw [← hw hwB]
  exact (ncard_pos ((finite_setOf_germFactorsThrough (hu.of_le one_le_two) hJu hne
    w).inter_of_right _)).2 ⟨w, hwV, .refl u w⟩

/-- **The local multiplicity is `1` off the preimage of the critical values**, for a nonconstant
`C²` pseudoholomorphic map from a compact connected Hausdorff Riemann surface into a Hausdorff
almost complex manifold: near an immersed point `u` is injective, so a point near `z` is its only
partner near `z`. -/
theorem coincidentBranchMultiplicity_eq_one_of_notMem [CompactSpace S] [PreconnectedSpace S]
    [T2Space S] [T2Space N] (hu : ContMDiff 𝓘(ℝ, ℂ) I 2 u)
    (hJu : IsPseudoholomorphic (ofComplexManifold ℂ S) J u) (hne : ∃ x₁ x₂, u x₁ ≠ u x₂) {z : S}
    (hz : z ∉ criticalValuePreimage I u) : coincidentBranchMultiplicity I u z = 1 := by
  obtain ⟨V, hV, h⟩ :=
    exists_mem_nhds_forall_eventually_ncard_eq_coincidentBranchMultiplicity hu hJu hne z
  obtain ⟨t, ht, htinj⟩ := (hu z).exists_mem_nhds_injOn two_ne_zero
    ((hJu.isPseudoholomorphicAt z).injective_mfderiv_iff_ne_zero.2
      (mfderiv_ne_zero_of_notMem_criticalValuePreimage hz))
  rw [← (h (V ∩ t) (inter_mem hV ht) inter_subset_left).self_of_nhds hz, ncard_eq_one]
  refine ⟨z, Subset.antisymm (fun y ⟨⟨_, hyt⟩, hy⟩ ↦ ?_)
    (singleton_subset_iff.2 ⟨⟨mem_of_mem_nhds hV, mem_of_mem_nhds ht⟩, .refl u z⟩)⟩
  exact htinj hyt (mem_of_mem_nhds ht) hy.apply_eq.symm

/-- **The local multiplicities over a class of `Γ` add up to the number of coincident branches.**
Let `u` be a nonconstant `C²` pseudoholomorphic map from a compact connected Hausdorff Riemann
surface into a Hausdorff almost complex manifold, such that the branch of `u` at every point
`w ∉ u⁻¹(u(Crit u))` factors holomorphically through the branches of `u` at exactly `d` points (as
`TauCeti.exists_pos_forall_ncard_setOf_germFactorsThrough_eq` provides). Then for every point `z`,
the local multiplicities `e_ζ` of the points `ζ` related to `z` by the closure `Γ` of the
coincident-branch relation add up to `d`. -/
theorem finsum_mem_coincidentBranchMultiplicity_eq [CompactSpace S] [PreconnectedSpace S]
    [T2Space S] [T2Space N] (hu : ContMDiff 𝓘(ℝ, ℂ) I 2 u)
    (hJu : IsPseudoholomorphic (ofComplexManifold ℂ S) J u) (hne : ∃ x₁ x₂, u x₁ ≠ u x₂) {d : ℕ}
    (hd : ∀ w ∉ criticalValuePreimage I u, {ζ | GermFactorsThrough u w u ζ}.ncard = d) (z : S) :
    ∑ᶠ ζ ∈ {ζ | (z, ζ) ∈ coincidentBranchClosure I u}, coincidentBranchMultiplicity I u ζ = d := by
  set B := criticalValuePreimage I u
  set C := {ζ | (z, ζ) ∈ coincidentBranchClosure I u}
  have hu₁ : ContMDiff 𝓘(ℝ, ℂ) I 1 u := hu.of_le one_le_two
  have hC : C.Finite := finite_setOf_mem_coincidentBranchClosure hu₁ hJu hne z
  -- Pairwise disjoint open neighbourhoods `V' ζ` of the points `ζ ∈ C`, small enough to count the
  -- partners of the points near `ζ` by `e_ζ`.
  choose! V hV hVe using fun ζ (_ : ζ ∈ C) ↦
    exists_mem_nhds_forall_eventually_ncard_eq_coincidentBranchMultiplicity hu hJu hne ζ
  obtain ⟨U, hU, hUd⟩ := hC.t2_separation
  set V' : S → Set S := fun ζ ↦ U ζ ∩ interior (V ζ)
  have hV'o : ∀ ζ, IsOpen (V' ζ) := fun ζ ↦ (hU ζ).2.inter isOpen_interior
  have hV'mem : ∀ ζ ∈ C, ζ ∈ V' ζ := fun ζ hζ ↦
    ⟨(hU ζ).1, mem_interior_iff_mem_nhds.2 (hV ζ hζ)⟩
  -- A point `w ∉ B` near `z` has the partners of some point near each `ζ ∈ C`, so it has `e_ζ`
  -- partners in `V' ζ`.
  have hcount : ∀ ζ ∈ C, ∀ᶠ w in 𝓝 z, w ∉ B →
      (V' ζ ∩ {y | GermFactorsThrough u w u y}).ncard = coincidentBranchMultiplicity I u ζ :=
    fun ζ hζ ↦ eventually_of_mem_coincidentBranchClosure hu hJu hne hζ (P := fun T ↦
      (V' ζ ∩ T).ncard = coincidentBranchMultiplicity I u ζ) (hVe ζ hζ (V' ζ)
        ((hV'o ζ).mem_nhds (hV'mem ζ hζ)) (inter_subset_right.trans interior_subset))
  -- A point `w` near `z` has no partner outside the sets `V' ζ`, since `Γ` is closed and relates
  -- `z` to no point of the compact set outside them.
  have hK : IsCompact (⋃ ζ ∈ C, V' ζ)ᶜ := (isOpen_biUnion fun ζ _ ↦ hV'o ζ).isClosed_compl.isCompact
  have hout : ∀ᶠ w in 𝓝 z, ∀ y ∈ (⋃ ζ ∈ C, V' ζ)ᶜ, (w, y) ∉ coincidentBranchClosure I u :=
    hK.eventually_forall_of_forall_eventually fun y hy ↦
      isClosed_coincidentBranchClosure.isOpen_compl.mem_nhds fun hzy ↦
        hy (mem_biUnion hzy (hV'mem y hzy))
  obtain ⟨w, hwB, hwc, hwo⟩ := exists_notMem_criticalValuePreimage_of_eventually hu₁ hJu hne
    (((eventually_all_finite hC).2 hcount).and hout)
  -- The partners of `w` are the disjoint union of its partners in the sets `V' ζ`.
  have hunion : {y | GermFactorsThrough u w u y} =
      ⋃ ζ ∈ C, (V' ζ ∩ {y | GermFactorsThrough u w u y}) := by
    refine Subset.antisymm (fun y hy ↦ ?_) (iUnion₂_subset fun _ _ ↦ inter_subset_right)
    by_contra hny
    refine hwo y (fun hyV ↦ hny ?_) (mem_coincidentBranchClosure_of_germFactorsThrough hwB hy)
    obtain ⟨ζ, hζ, hyζ⟩ := mem_iUnion₂.1 hyV
    exact mem_iUnion₂.2 ⟨ζ, hζ, hyζ, hy⟩
  rw [← hd w hwB, hunion, Set.Finite.ncard_biUnion hC (fun _ _ ↦
    (finite_setOf_germFactorsThrough hu₁ hJu hne w).inter_of_right _)
    (hUd.mono fun _ ↦ inter_subset_left.trans inter_subset_left)]
  exact finsum_mem_congr rfl fun ζ hζ ↦ (hwc ζ hζ hwB).symm

end TauCeti
