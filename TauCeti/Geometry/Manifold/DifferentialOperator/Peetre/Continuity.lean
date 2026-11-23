/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialOperator.Peetre.Section
public import TauCeti.Geometry.Manifold.VectorBundle.Section.CompletelyMetrizable
public import TauCeti.Geometry.Manifold.VectorBundle.Section.WithSeminorms
import Mathlib.Analysis.LocallyConvex.Barrelled
import TauCeti.Geometry.Manifold.ContMDiffMap.Chart.Seminorm
import TauCeti.Geometry.Manifold.VectorBundle.Section.VanishingIdeal
import TauCeti.Topology.Algebra.Module.FiniteDimension

/-!
# Local operators between section spaces are continuous

Let `V` and `W` be smooth real vector bundles over a finite-dimensional Hausdorff boundaryless
Lindelöf manifold `M`, with `V` of finite rank, and give the smooth sections `Γ(V)` and `Γ(W)`
the topology of compact convergence of all derivatives of their frame coefficients
(`ContMDiffSection.frameTopology`). This file proves that every linear map `P : Γ(V) → Γ(W)`
which is *local*, that is `(P s) x = 0` whenever `s` vanishes near `x`, is continuous
(`LinearMap.continuous_of_apply_eq_zero_of_eventuallyEq`). No continuity of `P` is assumed. In
particular every differential operator between sections, in Grothendieck's sense of iterated
commutators with multiplication operators, is continuous
(`TauCeti.continuous_of_mem_differentialOperators_section`).

This is the continuity half of Peetre's theorem: by
`LinearMap.exists_apply_eq_zero_of_mem_smoothVanishingIdeal_pow_smul_top`, a local operator has
locally finite order, and the argument below turns finite order into continuity without writing
the operator in coordinates.

## The argument

* **Finite order gives pointwise continuity.** If a linear map `Λ : Γ(V) → G` kills the
  submodule `I_x ^ (r + 1) Γ(V)`, then `Λ` only depends on the chart derivatives of order at most
  `r` at `x` of the frame coefficients of a section
  (`TauCeti.mem_smoothVanishingIdeal_pow_succ_smul_top_of_iteratedFDeriv_eq_zero`). These
  derivatives form a continuous linear map into a finite-dimensional space, so `Λ` is continuous
  (`LinearMap.continuous_of_apply_eq_zero_of_mem_smoothVanishingIdeal_pow_smul_top`).
* **Every coordinate derivative of `P s` is such a functional.** For a frame of `W`, a chart and
  an order `m`, the `m`-th chart derivative of the frame coefficients of `P s` is again a local
  operator, continuous on the chart domain, so Peetre's theorem applies to it. Hence its value at
  each coordinate point depends continuously on `s`.
* **Uniformity by Banach–Steinhaus.** The frame topology on `Γ(V)` is completely metrizable
  (`ContMDiffSection.baireSpace_frameTopology`), hence barrelled. The seminorms of the frame
  topology of `Γ(W)` are suprema over compact coordinate sets of the norms of the pointwise
  functionals above, and a pointwise bounded supremum of continuous seminorms on a barrelled
  space is continuous (`Seminorm.continuous_iSup`).

## References

* J. Peetre, *Réctification à l'article « Une caractérisation abstraite des opérateurs
  différentiels »*, Math. Scand. 8 (1960), 116–120.
* I. Kolář, P. W. Michor, J. Slovák, *Natural Operations in Differential Geometry*, Springer,
  1993, Theorem 19.1 and §19.
* M. Hirsch, *Differential Topology*, GTM 33, Chapter 2, §1, for the compact derivative
  topology.
-/

public section

open Bundle Set Filter Module TopologicalSpace
open scoped ContDiff Manifold Topology

noncomputable section

namespace LinearMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]
  {ι : Type*} (e : ι → Trivialization F (π F V)) [∀ i, MemTrivializationAtlas (e i)]
  (U : ι → Opens M) (hU : ∀ i, (U i : Set M) ⊆ (e i).baseSet)
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- **Functionals of finite order are continuous.** A linear map `Λ : Γ(V) → G` which vanishes on
`I_x ^ (r + 1) Γ(V)`, for some `r` and an interior point `x`, is continuous for the frame topology
of any frame system whose domains contain `x`. Such a `Λ` only sees the `r`-jet of a section at
`x`; Peetre's theorem (`LinearMap.exists_apply_eq_zero_of_mem_smoothVanishingIdeal_pow_smul_top`)
provides the order `r` for the values at `x` of a local operator. -/
theorem continuous_of_apply_eq_zero_of_mem_smoothVanishingIdeal_pow_smul_top
    (Λ : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] G) {x : M} (hx : ∃ i, x ∈ U i) (hxI : I.IsInteriorPoint x)
    {r : ℕ}
    (hI : ∀ s ∈ TauCeti.smoothVanishingIdeal I x ^ (r + 1) •
      (⊤ : Submodule C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯), Λ s = 0) :
    let _ := ContMDiffSection.frameTopology (I := I) (n := ∞) e U hU
    Continuous Λ := by
  let _ := ContMDiffSection.frameTopology (I := I) (n := ∞) e U hU
  obtain ⟨i, hi⟩ := hx
  let x' : U i := ⟨x, hi⟩
  have hk (k : Fin (r + 1)) : ((k : ℕ) : ℕ∞ω) ≤ ∞ := by exact_mod_cast le_top
  let z₀ : (extChartAt I x').target := ⟨extChartAt I x' x', mem_extChartAt_target x'⟩
  -- The `r`-jet at `x` of the frame coefficients, a continuous map to a finite-dimensional space.
  let J : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Π k : Fin (r + 1), E [×k]→L[ℝ] F :=
    LinearMap.pi fun k ↦ (e i).frameJetAt (hU i) x' k (hk k) z₀
  have hJk (s : Cₛ^∞⟮I; F, V⟯) (k : Fin (r + 1)) : J s k =
      ContMDiffMap.chartIteratedFDeriv ((e i).frameCoordinates (hU i) s) x' k (hk k) z₀ := by
    simp only [J, LinearMap.pi_apply, Trivialization.frameJetAt_apply]
  have hJ : Continuous J := continuous_pi fun k ↦ by
    simp only [J, LinearMap.pi_apply]
    exact ContMDiffSection.continuous_frameJetAt e U hU i x' k (hk k) z₀
  -- `Λ` vanishes on the kernel of `J`.
  have hker : LinearMap.ker J ≤ LinearMap.ker Λ := fun s hs ↦ by
    rw [LinearMap.mem_ker] at hs ⊢
    have hjet (k : ℕ) (hkr : k ≤ r) : iteratedFDeriv ℝ k
        ((fun y ↦ (e i ⟨y, s y⟩).2) ∘ (extChartAt I x).symm) (extChartAt I x x) = 0 := by
      have h : ContMDiffMap.chartIteratedFDeriv ((e i).frameCoordinates (hU i) s) x' k
          (hk ⟨k, Nat.lt_succ_of_le hkr⟩) z₀ = 0 :=
        (hJk s ⟨k, Nat.lt_succ_of_le hkr⟩).symm.trans (congrFun hs ⟨k, Nat.lt_succ_of_le hkr⟩)
      rwa [(e i).chartIteratedFDeriv_frameCoordinates_self (hU i) s x' k _ hxI] at h
    exact hI s (TauCeti.mem_smoothVanishingIdeal_pow_succ_smul_top_of_iteratedFDeriv_eq_zero
      (e i) (hU i hi) hxI hjet)
  -- Hence `Λ` factors through the finite-dimensional range of `J`.
  exact continuous_of_ker_le_ker hJ hker

section Target

variable {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F']
  {W : M → Type*} [TopologicalSpace (TotalSpace F' W)]
  [∀ x, AddCommGroup (W x)] [∀ x, Module ℝ (W x)] [∀ x, TopologicalSpace (W x)]
  [FiberBundle F' W] [VectorBundle ℝ F' W] [ContMDiffVectorBundle ∞ F' W I]

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [T2Space M] in
/-- The coordinates in the chart at `x'` of an open subset `O`, as a function on `M` that is
continuous on the points of `O` in the chart source. -/
private theorem exists_continuousOn_extChartAt {O : Opens M} (x' : O)
    (z : (extChartAt I x').target) :
    ∃ pt : M → (extChartAt I x').target,
      ContinuousOn pt (Subtype.val '' (extChartAt I x').source) ∧
        ∀ (a : O) (ha : a ∈ (extChartAt I x').source),
          pt a = ⟨extChartAt I x' a, (extChartAt I x').map_source ha⟩ := by
  classical
  let pt : M → (extChartAt I x').target := fun p ↦
    if h : ∃ hp : p ∈ O, (⟨p, hp⟩ : O) ∈ (extChartAt I x').source then
      ⟨extChartAt I x' ⟨p, h.1⟩, (extChartAt I x').map_source h.2⟩ else z
  have hpt (a : O) (ha : a ∈ (extChartAt I x').source) :
      pt a = ⟨extChartAt I x' a, (extChartAt I x').map_source ha⟩ :=
    dite_eq_left ⟨a.property, ha⟩
  refine ⟨pt, ?_, hpt⟩
  rw [continuousOn_iff_continuous_domRestrict]
  have hmem (p : Subtype.val '' (extChartAt I x').source) :
      ∃ hp : (p : M) ∈ O, (⟨p, hp⟩ : O) ∈ (extChartAt I x').source := by
    obtain ⟨a, ha, hap⟩ := p.property
    exact ⟨hap ▸ a.property, by simpa [← hap] using ha⟩
  let ψ : Subtype.val '' (extChartAt I x').source → O := fun p ↦ ⟨p, (hmem p).1⟩
  have hψ : Continuous ψ := continuous_subtypeVal.subtype_mk _
  have hrestr : (Subtype.val '' (extChartAt I x').source).domRestrict pt = fun p ↦
      ⟨extChartAt I x' (ψ p), (extChartAt I x').map_source (hmem p).2⟩ :=
    funext fun p ↦ hpt (ψ p) (hmem p).2
  rw [hrestr]
  exact ((continuousOn_extChartAt x').comp_continuous hψ fun p ↦ (hmem p).2).subtype_mk _

omit [FiniteDimensional ℝ E] [T2Space M] [FiniteDimensional ℝ F]
  [ContMDiffVectorBundle ∞ F V I] in
/-- The chart derivatives of the frame coefficients of `P s`, for a local operator `P`, vanish at
the coordinates of a point near which `s` vanishes. -/
private theorem chartIteratedFDeriv_frameCoordinates_eq_zero
    (P : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F', W⟯)
    (hloc : ∀ (s : Cₛ^∞⟮I; F, V⟯) (x : M), (∀ᶠ y in 𝓝 x, s y = 0) → P s x = 0)
    (e' : Trivialization F' (π F' W)) [MemTrivializationAtlas e'] {O : Opens M}
    (hO : (O : Set M) ⊆ e'.baseSet) (x' : O) (m : ℕ) (hm : (m : ℕ∞ω) ≤ ∞) {a : O}
    (ha : a ∈ (extChartAt I x').source) {s : Cₛ^∞⟮I; F, V⟯} (hs : ∀ᶠ y in 𝓝 (a : M), s y = 0) :
    ContMDiffMap.chartIteratedFDeriv (e'.frameCoordinates hO (P s)) x' m hm
      ⟨extChartAt I x' a, (extChartAt I x').map_source ha⟩ = 0 := by
  apply ContMDiffMap.chartIteratedFDeriv_eq_zero_of_eventuallyEq_zero
  rw [Subtype.coe_mk, (extChartAt I x').left_inv ha]
  have hPs : ∀ᶠ y in 𝓝 (a : M), P s y = 0 := hs.eventually_nhds.mono fun y hy ↦ hloc s y hy
  filter_upwards [(continuous_subtypeVal.tendsto a).eventually hPs] with y hy
  have h := (e'.frameCoordinates_eq_iff hO (P s) 0 y).2 hy
  rwa [map_zero] at h

/-- For a local operator `P`, each chart derivative of the frame coefficients of `P s` at a
coordinate point depends continuously on `s`: it is a local operator in `s`, continuous on the
chart domain, so Peetre's theorem gives it finite order. -/
private theorem continuous_chartIteratedFDeriv_frameCoordinates_apply
    [BoundarylessManifold I M] (P : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F', W⟯)
    (hloc : ∀ (s : Cₛ^∞⟮I; F, V⟯) (x : M), (∀ᶠ y in 𝓝 x, s y = 0) → P s x = 0)
    (hcover : ∀ x, ∃ i, x ∈ U i) (e' : Trivialization F' (π F' W)) [MemTrivializationAtlas e']
    {O : Opens M} (hO : (O : Set M) ⊆ e'.baseSet) (x' : O) (m : ℕ) (hm : (m : ℕ∞ω) ≤ ∞)
    (z : (extChartAt I x').target) :
    let _ := ContMDiffSection.frameTopology (I := I) (n := ∞) e U hU
    Continuous fun s ↦
      ContMDiffMap.chartIteratedFDeriv (e'.frameCoordinates hO (P s)) x' m hm z := by
  let _ := ContMDiffSection.frameTopology (I := I) (n := ∞) e U hU
  let G := E [×m]→L[ℝ] F'
  let Φ : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] C((extChartAt I x').target, G) :=
    ContMDiffMap.chartIteratedFDerivLinearMap x' m hm ∘ₗ e'.frameCoordinates hO ∘ₗ P
  have hΦ (s : Cₛ^∞⟮I; F, V⟯) :
      Φ s = ContMDiffMap.chartIteratedFDeriv (e'.frameCoordinates hO (P s)) x' m hm :=
    ContMDiffMap.chartIteratedFDerivLinearMap_apply (I := I) x' m hm _
  -- The points `S` of `M` represented in the chart at `x'`, and their coordinates `pt`.
  set S : Set M := Subtype.val '' (extChartAt I x').source
  have hSO : IsOpen S := O.isOpen.isOpenMap_subtypeVal _ (isOpen_extChartAt_source x')
  obtain ⟨pt, hptS, hpt⟩ := exists_continuousOn_extChartAt (I := I) x' z
  -- The chart derivative of `P s` as a function on `M`: it is local and continuous on `S`.
  let P' : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Π _ : M, G :=
    LinearMap.pi fun p ↦ (ContinuousMap.evalCLM ℝ (pt p)).toLinearMap ∘ₗ Φ
  have hP' (s : Cₛ^∞⟮I; F, V⟯) (p : M) : P' s p = Φ s (pt p) := rfl
  have hlocP' (s : Cₛ^∞⟮I; F, V⟯) (p : M) (hp : p ∈ S) (hs : ∀ᶠ y in 𝓝 p, s y = 0) :
      P' s p = 0 := by
    obtain ⟨a, ha, rfl⟩ := hp
    rw [hP', hpt a ha, hΦ]
    exact chartIteratedFDeriv_frameCoordinates_eq_zero P hloc e' hO x' m hm ha hs
  -- Peetre's theorem at the point represented by `z`, applied to `P'` as an operator into the
  -- sections of the trivial bundle with fibre `G`.
  let q : O := (extChartAt I x').symm z
  have hqs : q ∈ (extChartAt I x').source := (extChartAt I x').map_target z.property
  have hptq : pt q = z := by
    rw [hpt q hqs]
    exact Subtype.ext ((extChartAt I x').right_inv z.property)
  obtain ⟨r, hr⟩ := LinearMap.exists_apply_eq_zero_of_mem_smoothVanishingIdeal_pow_smul_top
    (W := Bundle.Trivial M G) P' hSO hlocP'
    (fun s ↦ (Bundle.Trivial.homeomorphProd M G).symm.continuous.comp_continuousOn
      (continuousOn_id.prodMk ((Φ s).continuous.comp_continuousOn hptS))) isCompact_singleton
    (singleton_subset_iff.2 ⟨q, hqs, rfl⟩)
  let Λ : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] E [×m]→L[ℝ] F' := e'.frameJetAt hO x' m hm z ∘ₗ P
  have hΛ' (s : Cₛ^∞⟮I; F, V⟯) :
      Λ s = ContMDiffMap.chartIteratedFDeriv (e'.frameCoordinates hO (P s)) x' m hm z := by
    simp only [Λ, LinearMap.comp_apply, Trivialization.frameJetAt_apply]
  have hΛ (s : Cₛ^∞⟮I; F, V⟯) : Λ s = P' s q := by
    rw [hP', hptq, hΛ', hΦ]
  have hfun : (fun s ↦ ContMDiffMap.chartIteratedFDeriv (e'.frameCoordinates hO (P s)) x' m hm z) =
      ⇑Λ := funext fun s ↦ (hΛ' s).symm
  rw [hfun]
  exact continuous_of_apply_eq_zero_of_mem_smoothVanishingIdeal_pow_smul_top e U hU Λ
    (hcover q) BoundarylessManifold.isInteriorPoint (r := r) fun s hs ↦
      (hΛ s).trans (hr q rfl s hs)

/-- **Local operators between sections are continuous.** Let `V` and `W` be smooth real vector
bundles over a finite-dimensional Hausdorff boundaryless Lindelöf manifold, `V` of finite rank. A
linear map `P : Γ(V) → Γ(W)` between smooth sections which is local, that is `(P s) x = 0`
whenever `s` vanishes near `x`, is continuous for the compact derivative topologies of any
covering frame system of `V` and any frame system of `W`. No continuity of `P` is assumed. -/
theorem continuous_of_apply_eq_zero_of_eventuallyEq [I.Boundaryless] [LindelofSpace M]
    (P : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F', W⟯)
    (hloc : ∀ (s : Cₛ^∞⟮I; F, V⟯) (x : M), (∀ᶠ y in 𝓝 x, s y = 0) → P s x = 0)
    (hcover : ∀ x, ∃ i, x ∈ U i) {κ : Type*} (e' : κ → Trivialization F' (π F' W))
    [∀ j, MemTrivializationAtlas (e' j)] (U' : κ → Opens M)
    (hU' : ∀ j, (U' j : Set M) ⊆ (e' j).baseSet) :
    let _ := ContMDiffSection.frameTopology (I := I) (n := ∞) e U hU
    let _ := ContMDiffSection.frameTopology (I := I) (n := ∞) e' U' hU'
    Continuous P := by
  let _ := ContMDiffSection.frameTopology (I := I) (n := ∞) e U hU
  let _ := ContMDiffSection.frameTopology (I := I) (n := ∞) e' U' hU'
  -- The sections of `V` form a Baire, hence barrelled, space.
  have := ContMDiffSection.isTopologicalAddGroup_frameTopology (I := I) (n := ∞) e U hU
  have := ContMDiffSection.continuousSMul_frameTopology (I := I) (n := ∞) e U hU
  have := ContMDiffSection.baireSpace_frameTopology (I := I) (n := ∞) e U hU hcover
  refine (ContMDiffSection.withSeminorms_frameSeminormFamily (I := I) (n := ∞) e' U'
    hU').continuous_of_continuous_comp P ?_
  rintro ⟨j, x', ⟨m, hm⟩, K⟩
  have : CompactSpace K := isCompact_iff_compactSpace.mp K.isCompact
  -- The seminorm is the supremum over `K` of the norms of pointwise continuous functionals.
  let p (z : K) : Seminorm ℝ Cₛ^∞⟮I; F, V⟯ :=
    (normSeminorm ℝ (E [×m]→L[ℝ] F')).comp ((e' j).frameJetAt (hU' j) x' m hm z ∘ₗ P)
  have hp (z : K) (s : Cₛ^∞⟮I; F, V⟯) : p z s =
      ‖ContMDiffMap.chartIteratedFDeriv ((e' j).frameCoordinates (hU' j) (P s)) x' m hm z‖ := by
    simp only [p, Seminorm.comp_apply, coe_normSeminorm, LinearMap.comp_apply,
      Trivialization.frameJetAt_apply]
  have hpc (z : K) : Continuous (p z) := by
    simp_rw [funext (hp z)]
    exact (continuous_chartIteratedFDeriv_frameCoordinates_apply e U hU P hloc hcover (e' j)
      (hU' j) x' m hm z).norm
  have hbdd : BddAbove (Set.range p) := by
    refine Seminorm.bddAbove_range_iff.2 fun s ↦
      ⟨‖(ContMDiffMap.chartIteratedFDeriv ((e' j).frameCoordinates (hU' j) (P s)) x' m
        hm).restrict K‖, ?_⟩
    rintro _ ⟨z, rfl⟩
    dsimp only
    rw [hp z s]
    exact ((ContMDiffMap.chartIteratedFDeriv ((e' j).frameCoordinates (hU' j) (P s)) x' m
      hm).restrict (K : Set (extChartAt I x').target)).norm_coe_le_norm z
  have heq : ⇑((ContMDiffSection.frameSeminormFamily (I := I) (n := ∞) e' U' hU'
      ⟨j, x', ⟨m, hm⟩, K⟩).comp P) = ⨆ z, ⇑(p z) := by
    funext s
    rw [Seminorm.comp_apply, ContMDiffSection.frameSeminormFamily_apply,
      Trivialization.chartDerivativeSeminorm_apply, ContinuousMap.norm_eq_iSup_norm, iSup_apply]
    exact iSup_congr fun z ↦ (hp z s).symm
  rw [heq]
  exact Seminorm.continuous_iSup p hpc hbdd

end Target

end LinearMap

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [LindelofSpace M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]
  {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F']
  {W : M → Type*} [TopologicalSpace (TotalSpace F' W)]
  [∀ x, AddCommGroup (W x)] [∀ x, Module ℝ (W x)] [∀ x, TopologicalSpace (W x)]
  [FiberBundle F' W] [VectorBundle ℝ F' W] [ContMDiffVectorBundle ∞ F' W I]

/-- **Differential operators between sections are continuous.** A differential operator
`P : Γ(V) → Γ(W)` of any order in Grothendieck's sense, between smooth sections of real vector
bundles over a finite-dimensional Hausdorff boundaryless Lindelöf manifold, `V` of finite rank,
is continuous for the compact derivative topologies of any covering frame system of `V` and any
frame system of `W`. -/
theorem continuous_of_mem_differentialOperators_section
    {P : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F', W⟯} {r : ℕ}
    (hP : P ∈ differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ r)
    {ι : Type*} (e : ι → Trivialization F (π F V)) [∀ i, MemTrivializationAtlas (e i)]
    (U : ι → Opens M) (hU : ∀ i, (U i : Set M) ⊆ (e i).baseSet) (hcover : ∀ x, ∃ i, x ∈ U i)
    {κ : Type*} (e' : κ → Trivialization F' (π F' W)) [∀ j, MemTrivializationAtlas (e' j)]
    (U' : κ → Opens M) (hU' : ∀ j, (U' j : Set M) ⊆ (e' j).baseSet) :
    let _ := ContMDiffSection.frameTopology (I := I) (n := ∞) e U hU
    let _ := ContMDiffSection.frameTopology (I := I) (n := ∞) e' U' hU'
    Continuous P :=
  P.continuous_of_apply_eq_zero_of_eventuallyEq e U hU
    (fun _ _ hs ↦ differentialOperators_section_apply_eq_zero_of_eventuallyEq hP hs) hcover e' U'
    hU'

end TauCeti

end
