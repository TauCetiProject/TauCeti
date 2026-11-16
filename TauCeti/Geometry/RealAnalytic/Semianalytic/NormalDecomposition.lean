/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Analytic.Submanifold.Basic
public import TauCeti.Geometry.RealAlgebraic.SignInvariant
public import TauCeti.Geometry.RealAnalytic.Semianalytic.Basic
public import TauCeti.Topology.ClusterSet
import TauCeti.Analysis.Analytic.Complexification.Weierstrass
import TauCeti.Analysis.Analytic.Submanifold.Dimension
import TauCeti.Analysis.Analytic.Submanifold.Transport
import TauCeti.Analysis.Analytic.Uniqueness
import TauCeti.Analysis.Polynomial.Monic.RootBound
import TauCeti.Geometry.RealAlgebraic.Stack.Closure
import TauCeti.Geometry.RealAlgebraic.Stack.Sectors
import TauCeti.Geometry.RealAnalytic.Projection
import TauCeti.Geometry.RealAnalytic.Semianalytic.Stack

/-!
# Local normal decompositions for real analytic and semianalytic germs

Around any point `x₀ ∈ ℝ ^ n` and inside any prescribed neighbourhood of `x₀`, a finite family of
real analytic germs admits an open neighbourhood `U` of `x₀` partitioned into finitely many
connected, globally semianalytic real-analytic submanifolds (`TauCeti.IsNormalDecomposition`) on
each of which every germ has constant sign (`TauCeti.exists_isNormalDecomposition_signInvariant`).
Equivalently, any finite family of semianalytic set germs at `x₀` admits a local normal
decomposition compatible with each set (`TauCeti.exists_isNormalDecomposition_subset_or_disjoint`).

In addition to connectedness, semianalyticity, and the analytic-submanifold structure of each
stratum, `TauCeti.IsNormalDecomposition` records three topological regularity properties inside `U`:

* **Preconnected approach regions** (`TauCeti.IsPreconnectedApproachAt`) at every point of `U`,
  expressing local connectedness of each stratum along its closure in `U`.
* **Frontier condition:** whenever a stratum `S` meets `closure T`, one has `S ⊆ closure T`, so
  `U ∩ closure T` is a union of strata.
* **Strict dimension drop:** whenever `S ⊆ closure T` with `S ≠ T`, `dim S < dim T`, so
  `U ∩ (closure T \ T)` is a finite union of strata of strictly smaller dimension.

For any set `A` compatible with a normal decomposition `(U, 𝒞)`, `A ∩ U` is a finite union of
strata, has finitely many connected components, and each of its connected components is a union of
strata and therefore semianalytic.

The proof proceeds by induction on the ambient dimension `n`. After discarding germs that vanish
near `x₀`, a simultaneous linear change of coordinates places the remaining germs in Weierstrass
general position in the first coordinate
(`TauCeti.exists_continuousLinearEquiv_forall_analyticOrderAt_ne_top`). Real Weierstrass
preparation replaces each germ up to a nonvanishing unit by a monic polynomial in the vertical
coordinate with analytic base coefficients vanishing at the base centre. Fujiwara's bound traps all
real roots inside a vertical interval `(t₀ - δ, t₀ + δ)`, two constant boundary factors
`X - (t₀ ± δ)` cap the cylinder, Collins' analytic projection supplies finitely many base germs to
pass to the induction hypothesis, and the preconnected-approach invariant extends root functions
continuously to frontier strata in `U_base` to establish both parts of the frontier condition.

## Main declarations

* `TauCeti.IsNormalDecomposition`: finite partition of an open set `U ⊆ ℝ ^ n` into connected
  semianalytic real-analytic submanifolds with preconnected approach regions along `U`, the
  frontier condition, and strict dimension drop on distinct incident strata.
* `TauCeti.IsNormalDecomposition.inter_closure_eq_biUnion`,
  `TauCeti.IsNormalDecomposition.inter_closure_diff_eq_biUnion`: inside `U`, closures and relative
  frontiers of strata are unions of strata.
* `TauCeti.IsNormalDecomposition.isSemianalytic_connectedComponentIn`,
  `TauCeti.IsNormalDecomposition.finite_image_connectedComponentIn`: semianalyticity and finiteness
  of the connected components of `A ∩ U` for any compatible set `A`.
* `TauCeti.IsNormalDecomposition.image_continuousLinearEquiv`: invariance under continuous linear
  equivalences of `ℝ ^ n`.
* `TauCeti.exists_isNormalDecomposition_signInvariant`: local normal-decomposition theorem for a
  finite family of real analytic germs.
* `TauCeti.exists_isNormalDecomposition_subset_or_disjoint`,
  `TauCeti.SemianalyticAt.exists_isNormalDecomposition`,
  `TauCeti.semianalyticAt_iff_exists_isNormalDecomposition`: local normal-decomposition theorem and
  characterization for semianalytic set germs.

## References

* S. Łojasiewicz, *Ensembles semi-analytiques*, IHÉS lecture notes (1965), §18–23.
* S. Łojasiewicz, *Triangulation of semi-analytic sets*, Annali della Scuola Normale Superiore di
  Pisa (3) 18 (1964), 449–474, §1–2.
* E. Bierstone and P. D. Milman, *Semianalytic and subanalytic sets*, Publications Mathématiques de
  l'IHÉS 67 (1988), 5–42, §2.
-/

public section

open Filter Function Polynomial Set Topology

namespace TauCeti

/-! ### Normal decompositions and their structural consequences -/

/-- A *normal decomposition* on an open subset `U ⊆ ℝ ^ n` is a finite pairwise disjoint partition
`𝒞` of `U` into connected semianalytic real-analytic submanifolds that have preconnected approach
regions at every point of `U` and satisfy the frontier and dimension-drop conditions: whenever
`S, T ∈ 𝒞` satisfy `(S ∩ closure T).Nonempty`, `S ⊆ closure T`, and whenever `S ⊆ closure T` with
`S ≠ T`, `dim S < dim T`. -/
structure IsNormalDecomposition {n : ℕ} (U : Set (Fin n → ℝ))
    (𝒞 : Set (Set (Fin n → ℝ))) : Prop where
  /-- The ambient domain of the decomposition is open. -/
  isOpen_domain : IsOpen U
  /-- The decomposition has finitely many strata. -/
  finite : 𝒞.Finite
  /-- Distinct strata are disjoint. -/
  pairwiseDisjoint : 𝒞.PairwiseDisjoint id
  /-- The strata cover `U`. -/
  sUnion_eq : ⋃₀ 𝒞 = U
  /-- Every stratum is connected, and in particular nonempty. -/
  isConnected : ∀ S ∈ 𝒞, IsConnected S
  /-- Every stratum is globally semianalytic in `ℝ ^ n`, including at its frontier points. -/
  isSemianalytic : ∀ S ∈ 𝒞, IsSemianalytic S
  /-- Every stratum is a real-analytic submanifold of some dimension `d ≤ n`. -/
  exists_isAnalyticSubmanifold : ∀ S ∈ 𝒞, ∃ d, IsAnalyticSubmanifold d S
  /-- Every stratum has preconnected approach regions at every point of `U`. -/
  isPreconnectedApproachAt : ∀ S ∈ 𝒞, ∀ x ∈ U, IsPreconnectedApproachAt S x
  /-- Frontier containment: if a stratum meets the closure of another stratum, it lies inside that
  closure. -/
  subset_closure_of_inter_closure_nonempty :
    ∀ S ∈ 𝒞, ∀ T ∈ 𝒞, (S ∩ closure T).Nonempty → S ⊆ closure T
  /-- Dimension drop: if a stratum `S` lies in the closure of a distinct stratum `T`, then
  `dim S < dim T`. -/
  dim_lt_of_ne_of_subset_closure :
    ∀ S ∈ 𝒞, ∀ T ∈ 𝒞, S ≠ T → S ⊆ closure T →
      ∀ dS dT, IsAnalyticSubmanifold dS S → IsAnalyticSubmanifold dT T → dS < dT

namespace IsNormalDecomposition

variable {n dS dT : ℕ} {U S T A : Set (Fin n → ℝ)} {𝒞 : Set (Set (Fin n → ℝ))}
  (h𝒞 : IsNormalDecomposition U 𝒞)
include h𝒞

/-- Every stratum of a normal decomposition of `U` is contained in `U`. -/
theorem subset_of_mem (hS : S ∈ 𝒞) : S ⊆ U :=
  h𝒞.sUnion_eq ▸ subset_sUnion_of_mem hS

/-- Every stratum of a normal decomposition is nonempty. -/
theorem nonempty_of_mem (hS : S ∈ 𝒞) : S.Nonempty :=
  (h𝒞.isConnected S hS).nonempty

/-- Every stratum of a normal decomposition is preconnected. -/
theorem isPreconnected_of_mem (hS : S ∈ 𝒞) : IsPreconnected S :=
  (h𝒞.isConnected S hS).isPreconnected

/-- Every stratum of a normal decomposition is locally closed in `ℝ ^ n`. -/
theorem isLocallyClosed_of_mem (hS : S ∈ 𝒞) : IsLocallyClosed S := by
  obtain ⟨d, hd⟩ := h𝒞.exists_isAnalyticSubmanifold S hS
  exact hd.isLocallyClosed

/-- Every point of `U` belongs to some stratum of `𝒞`. -/
theorem exists_mem {x : Fin n → ℝ} (hx : x ∈ U) : ∃ S ∈ 𝒞, x ∈ S :=
  mem_sUnion.1 (h𝒞.sUnion_eq.symm ▸ hx)

/-- A point of `U` belongs to at most one stratum of `𝒞`. -/
theorem eq_of_mem_of_mem (hS : S ∈ 𝒞) (hT : T ∈ 𝒞) {x : Fin n → ℝ} (hxS : x ∈ S) (hxT : x ∈ T) :
    S = T := by
  by_contra hne
  exact disjoint_left.1 (h𝒞.pairwiseDisjoint hS hT hne) hxS hxT

/-- For any two strata `S, T ∈ 𝒞`, `S` is either contained in `closure T` or disjoint from it. -/
theorem subset_closure_or_disjoint_closure (hS : S ∈ 𝒞) (hT : T ∈ 𝒞) :
    S ⊆ closure T ∨ Disjoint S (closure T) := by
  by_cases h : Disjoint S (closure T)
  · exact Or.inr h
  · exact Or.inl (h𝒞.subset_closure_of_inter_closure_nonempty S hS T hT
      (not_disjoint_iff_nonempty_inter.1 h))

/-- Incident distinct strata satisfy strict dimension drop. -/
theorem dim_lt_of_ne_of_inter_closure_nonempty (hS : S ∈ 𝒞) (hT : T ∈ 𝒞) (hne : S ≠ T)
    (hinter : (S ∩ closure T).Nonempty) (hdS : IsAnalyticSubmanifold dS S)
    (hdT : IsAnalyticSubmanifold dT T) : dS < dT :=
  h𝒞.dim_lt_of_ne_of_subset_closure S hS T hT hne
    (h𝒞.subset_closure_of_inter_closure_nonempty S hS T hT hinter) dS dT hdS hdT

/-- Inside `U`, the closure of a stratum `T ∈ 𝒞` is the union of the strata contained in
`closure T`. -/
theorem inter_closure_eq_biUnion (hT : T ∈ 𝒞) :
    U ∩ closure T = ⋃ S ∈ {S ∈ 𝒞 | S ⊆ closure T}, S := by
  ext x
  simp only [mem_inter_iff, mem_iUnion, mem_ofPred_eq, exists_prop]
  refine ⟨fun ⟨hxU, hxcl⟩ ↦ ?_, fun ⟨S, ⟨hS, hScl⟩, hxS⟩ ↦ ⟨h𝒞.subset_of_mem hS hxS, hScl hxS⟩⟩
  obtain ⟨S, hS, hxS⟩ := h𝒞.exists_mem hxU
  exact ⟨S, ⟨hS, h𝒞.subset_closure_of_inter_closure_nonempty S hS T hT ⟨x, hxS, hxcl⟩⟩, hxS⟩

/-- Inside `U`, the relative frontier `closure T \ T` of a stratum `T ∈ 𝒞` is the union of the
strata `S ≠ T` contained in `closure T`, each of which has strictly smaller dimension than `T`. -/
theorem inter_closure_diff_eq_biUnion (hT : T ∈ 𝒞) :
    U ∩ (closure T \ T) = ⋃ S ∈ {S ∈ 𝒞 | S ≠ T ∧ S ⊆ closure T}, S := by
  ext x
  simp only [mem_inter_iff, Set.mem_sdiff, mem_iUnion, mem_ofPred_eq, exists_prop]
  constructor
  · rintro ⟨hxU, hxcl, hxT⟩
    obtain ⟨S, hS, hxS⟩ := h𝒞.exists_mem hxU
    refine ⟨S, ⟨hS, fun hST ↦ hxT (hST ▸ hxS), ?_⟩, hxS⟩
    exact h𝒞.subset_closure_of_inter_closure_nonempty S hS T hT ⟨x, hxS, hxcl⟩
  · rintro ⟨S, ⟨hS, hne, hScl⟩, hxS⟩
    exact ⟨h𝒞.subset_of_mem hS hxS, hScl hxS,
      disjoint_left.1 (h𝒞.pairwiseDisjoint hS hT hne) hxS⟩

/-- If every stratum of `𝒞` lies inside or outside `A`, then `A ∩ U` is the union of the strata
contained in `A`. -/
theorem inter_eq_biUnion (hA : ∀ S ∈ 𝒞, S ⊆ A ∨ Disjoint S A) :
    A ∩ U = ⋃ S ∈ {S ∈ 𝒞 | S ⊆ A}, S := by
  ext x
  simp only [mem_inter_iff, mem_iUnion, mem_ofPred_eq, exists_prop]
  refine ⟨fun ⟨hxA, hxU⟩ ↦ ?_, fun ⟨S, ⟨hS, hSA⟩, hxS⟩ ↦ ⟨hSA hxS, h𝒞.subset_of_mem hS hxS⟩⟩
  obtain ⟨S, hS, hxS⟩ := h𝒞.exists_mem hxU
  exact ⟨S, ⟨hS, (hA S hS).resolve_right fun hd ↦ disjoint_left.1 hd hxS hxA⟩, hxS⟩

/-- If `A` is compatible with `𝒞`, then `A ∩ U` is globally semianalytic. -/
theorem isSemianalytic_inter (hA : ∀ S ∈ 𝒞, S ⊆ A ∨ Disjoint S A) :
    IsSemianalytic (A ∩ U) := by
  rw [h𝒞.inter_eq_biUnion hA]
  exact .biUnion (h𝒞.finite.subset (sep_subset _ _)) fun S hS ↦ h𝒞.isSemianalytic S hS.1

/-- If `A` is compatible with `𝒞`, then every connected component of `A ∩ U` is the union of the
strata of `𝒞` contained in that connected component. -/
theorem connectedComponentIn_inter_eq_biUnion (hA : ∀ S ∈ 𝒞, S ⊆ A ∨ Disjoint S A)
    (x : Fin n → ℝ) :
    connectedComponentIn (A ∩ U) x =
      ⋃ S ∈ {S ∈ 𝒞 | S ⊆ connectedComponentIn (A ∩ U) x}, S := by
  refine subset_antisymm (fun y hy ↦ ?_) (iUnion₂_subset fun S hS ↦ hS.2)
  have hyAU : y ∈ A ∩ U := connectedComponentIn_subset (A ∩ U) x hy
  obtain ⟨S, hS, hyS⟩ := h𝒞.exists_mem hyAU.2
  have hSA : S ⊆ A := (hA S hS).resolve_right fun hd ↦ disjoint_left.1 hd hyS hyAU.1
  have hS_comp : S ⊆ connectedComponentIn (A ∩ U) x := by
    rw [connectedComponentIn_eq hy]
    exact (h𝒞.isPreconnected_of_mem hS).subset_connectedComponentIn hyS
      (subset_inter hSA (h𝒞.subset_of_mem hS))
  exact mem_iUnion₂.2 ⟨S, ⟨hS, hS_comp⟩, hyS⟩

/-- If `A` is compatible with `𝒞`, then every connected component of `A ∩ U` is globally
semianalytic. -/
theorem isSemianalytic_connectedComponentIn (hA : ∀ S ∈ 𝒞, S ⊆ A ∨ Disjoint S A)
    (x : Fin n → ℝ) :
    IsSemianalytic (connectedComponentIn (A ∩ U) x) := by
  rw [h𝒞.connectedComponentIn_inter_eq_biUnion hA x]
  exact .biUnion (h𝒞.finite.subset (sep_subset _ _)) fun S hS ↦ h𝒞.isSemianalytic S hS.1

/-- If `A` is compatible with `𝒞`, then `A ∩ U` has finitely many connected components. -/
theorem finite_image_connectedComponentIn (hA : ∀ S ∈ 𝒞, S ⊆ A ∨ Disjoint S A) :
    (connectedComponentIn (A ∩ U) '' (A ∩ U)).Finite := by
  refine (h𝒞.finite.powerset.image sUnion).subset ?_
  rintro _ ⟨x, -, rfl⟩
  refine ⟨{S ∈ 𝒞 | S ⊆ connectedComponentIn (A ∩ U) x}, sep_subset _ _, ?_⟩
  rw [sUnion_eq_biUnion, ← h𝒞.connectedComponentIn_inter_eq_biUnion hA x]

/-- Transporting a normal decomposition along a continuous linear equivalence preserves all
properties of a normal decomposition. -/
theorem image_continuousLinearEquiv {m : ℕ} (L : (Fin n → ℝ) ≃L[ℝ] (Fin m → ℝ)) :
    IsNormalDecomposition (L '' U) ((image L) '' 𝒞) where
  isOpen_domain := L.toHomeomorph.isOpenMap U h𝒞.isOpen_domain
  finite := h𝒞.finite.image (image L)
  pairwiseDisjoint := by
    rintro _ ⟨S, hS, rfl⟩ _ ⟨T, hT, rfl⟩ hne
    rw [onFun, id, id, disjoint_image_iff L.injective]
    exact h𝒞.pairwiseDisjoint hS hT fun h ↦ hne (congrArg (image L) h)
  sUnion_eq := by rw [← image_sUnion, h𝒞.sUnion_eq]
  isConnected := by
    rintro _ ⟨S, hS, rfl⟩
    exact (h𝒞.isConnected S hS).image L L.continuous.continuousOn
  isSemianalytic := by
    rintro _ ⟨S, hS, rfl⟩
    exact (Equiv.isSemianalytic_image_iff L.toEquiv (fun x _ ↦ L.analyticAt x)
      (fun y _ ↦ L.symm.analyticAt y)).2 (h𝒞.isSemianalytic S hS)
  exists_isAnalyticSubmanifold := by
    rintro _ ⟨S, hS, rfl⟩
    obtain ⟨d, hd⟩ := h𝒞.exists_isAnalyticSubmanifold S hS
    exact ⟨d, hd.image_continuousLinearEquiv L⟩
  isPreconnectedApproachAt := by
    rintro _ ⟨S, hS, rfl⟩ _ ⟨x, hx, rfl⟩
    exact (h𝒞.isPreconnectedApproachAt S hS x hx).image L.continuous.continuousAt
      L.continuous.continuousOn L.symm.continuous.continuousAt (L.symm_apply_apply x)
      fun z _ ↦ L.symm_apply_apply z
  subset_closure_of_inter_closure_nonempty := by
    rintro _ ⟨S, hS, rfl⟩ _ ⟨T, hT, rfl⟩ hne
    have hcl : closure (L '' T) = L '' closure T := (L.toHomeomorph.image_closure T).symm
    rw [hcl] at hne ⊢
    rw [← image_inter L.injective, image_nonempty] at hne
    exact image_mono (h𝒞.subset_closure_of_inter_closure_nonempty S hS T hT hne)
  dim_lt_of_ne_of_subset_closure := by
    rintro _ ⟨S, hS, rfl⟩ _ ⟨T, hT, rfl⟩ hne hsub dS dT hdS hdT
    have hcl : closure (L '' T) = L '' closure T := (L.toHomeomorph.image_closure T).symm
    rw [hcl, image_subset_image_iff L.injective] at hsub
    rw [isAnalyticSubmanifold_image_continuousLinearEquiv_iff] at hdS hdT
    exact h𝒞.dim_lt_of_ne_of_subset_closure S hS T hT (fun h ↦ hne (congrArg (image L) h)) hsub
      dS dT hdS hdT

end IsNormalDecomposition

/-- In ambient dimension zero, `{univ}` is a normal decomposition of `univ`. -/
theorem isNormalDecomposition_singleton_univ :
    IsNormalDecomposition (univ : Set (Fin 0 → ℝ)) {univ} where
  isOpen_domain := isOpen_univ
  finite := finite_singleton univ
  pairwiseDisjoint := pairwiseDisjoint_singleton univ id
  sUnion_eq := sUnion_singleton univ
  isConnected _ hS := by rw [mem_singleton_iff.1 hS]; exact isConnected_univ
  isSemianalytic _ hS := by rw [mem_singleton_iff.1 hS]; exact isSemianalytic_univ
  exists_isAnalyticSubmanifold _ hS := by
    rw [mem_singleton_iff.1 hS]
    exact ⟨0, isOpen_univ.isAnalyticSubmanifold univ_nonempty⟩
  isPreconnectedApproachAt _ hS x _ := by
    rw [mem_singleton_iff.1 hS, isPreconnectedApproachAt_def]
    intro s hs
    have hs_univ : s = univ := eq_univ_of_forall fun y ↦ by
      simpa only [Subsingleton.elim y x] using mem_of_mem_nhds hs
    exact ⟨univ, univ_mem, hs_univ ▸ subset_rfl, by simpa using isPreconnected_univ⟩
  subset_closure_of_inter_closure_nonempty _ hS _ hT _ := by
    rw [mem_singleton_iff.1 hS, mem_singleton_iff.1 hT, closure_univ]
  dim_lt_of_ne_of_subset_closure _ hS _ hT hne :=
    False.elim (hne ((mem_singleton_iff.1 hS).trans (mem_singleton_iff.1 hT).symm))

/-! ### Cylindrical lifting over a bounded polynomial box -/

/-- Wrapper around `isPreconnectedApproachAt_image_cylinder_sectorSet_castSucc_succ` indexed by an
arbitrary sector `j : Fin (count + 1)` that is neither `0` nor `Fin.last count`. -/
private lemma isPreconnectedApproachAt_image_cylinder_sectorSet_of_ne {n count : ℕ}
    {T B : Set (Fin n → ℝ)} {θ : Fin count → T → ℝ} (hmono : ∀ x, StrictMono fun i ↦ θ i x)
    {j : Fin (count + 1)} (hj0 : j ≠ 0) (hjl : j ≠ Fin.last count)
    {θ_ext : Fin count → (Fin n → ℝ) → ℝ} (hTB : T ⊆ B) (hθc : ∀ i, ContinuousOn (θ_ext i) B)
    (hθeq : ∀ i (x : T), θ_ext i x.1 = θ i x) (hconn : ∀ x ∈ B, IsPreconnectedApproachAt T x)
    {y : Fin (n + 1) → ℝ} (hy : Fin.tail y ∈ B ∨ Fin.tail y ∉ closure T) :
    IsPreconnectedApproachAt (cylinder T '' sectorSet θ j) y := by
  cases count with
  | zero => exact absurd (Fin.eq_zero j) hj0
  | succ k =>
    cases j using Fin.cases with
    | zero => exact absurd rfl hj0
    | succ j' =>
      cases j' using Fin.lastCases with
      | last => exact absurd (Fin.succ_last k) hjl
      | cast m =>
        exact isPreconnectedApproachAt_image_cylinder_sectorSet_castSucc_succ hmono hTB
          (hθc m.castSucc) (hθc m.succ) (hθeq m.castSucc) (hθeq m.succ) hconn hy

/-- Over the same base `T`, if a cell `F ∈ stackCells T θ` meets the closure of a bounded sector
`E = cylinder T '' sectorSet θ j` (`j ≠ 0, last`), then `F ⊆ closure E` and either `F = E` or `F`
is a section (hence of strictly smaller dimension). -/
private lemma subset_closure_and_section_or_eq_of_same_base_sectorSet {n count : ℕ}
    {T : Set (Fin n → ℝ)} {θ : Fin count → T → ℝ} (hcont : ∀ i, Continuous (θ i))
    (hmono : ∀ x, StrictMono fun i ↦ θ i x) {j : Fin (count + 1)} (hj0 : j ≠ 0)
    (hjl : j ≠ Fin.last count) {F : Set (Fin (n + 1) → ℝ)} (hF : F ∈ stackCells T θ)
    (hne_inter : (F ∩ closure (cylinder T '' sectorSet θ j)).Nonempty) :
    F ⊆ closure (cylinder T '' sectorSet θ j) ∧
      ((∃ r, F = cylinder T '' sectionSet θ r) ∨ F = cylinder T '' sectorSet θ j) := by
  cases count with
  | zero => exact absurd (Fin.eq_zero j) hj0
  | succ k =>
    cases j using Fin.cases with
    | zero => exact absurd rfl hj0
    | succ j' =>
      cases j' using Fin.lastCases with
      | last => exact absurd (Fin.succ_last k) hjl
      | cast m =>
        let θ_ext : Fin (k + 1) → (Fin n → ℝ) → ℝ := fun i ↦ extend Subtype.val (θ i) 0
        have hθ_eq (i : Fin (k + 1)) (x : T) : θ_ext i x.1 = θ i x :=
          Subtype.val_injective.extend_apply (θ i) 0 x
        have hθ_cont (i : Fin (k + 1)) : ContinuousOn (θ_ext i) T := by
          rw [continuousOn_iff_continuous_domRestrict]
          exact (hcont i).congr fun x ↦ (hθ_eq i x).symm
        have hdic := subset_closure_or_disjoint_of_mem_stackCells_sectorSet_castSucc_succ hmono
          hmono subset_rfl subset_closure subset_rfl (hθ_cont m.castSucc) (hθ_cont m.succ)
          (hθ_eq m.castSucc) (hθ_eq m.succ) (hθ_eq m.castSucc) (hθ_eq m.succ) hF
        obtain ⟨hsub, hshape⟩ := hdic.resolve_right (not_disjoint_iff_nonempty_inter.2 hne_inter)
        refine ⟨hsub, ?_⟩
        rcases hshape with ⟨r, rfl⟩ | ⟨r, hr_gt, hr_le, rfl⟩
        · exact Or.inl ⟨r, rfl⟩
        · refine Or.inr (congrArg (cylinder T '' sectorSet θ ·) (Fin.ext ?_))
          have h₁ : m.val < r.val := hr_gt
          have h₂ : r.val ≤ m.val + 1 := hr_le
          change r.val = m.val + 1
          omega

/-- Over distinct strata `S ≠ T` (`S ⊆ B ⊆ closure T`), if `F ∈ stackCells S φ` meets the closure
of a bounded sector `E = cylinder T '' sectorSet θ j` (`j ≠ 0, last`), then `F ⊆ closure E`. -/
private lemma subset_closure_of_mem_stackCells_sectorSet_of_ne {n count l : ℕ}
    {T B S : Set (Fin n → ℝ)} {θ : Fin count → T → ℝ} (hmono : ∀ x, StrictMono fun i ↦ θ i x)
    {φ : Fin l → S → ℝ} (hφmono : ∀ x, StrictMono fun i ↦ φ i x)
    {j : Fin (count + 1)} (hj0 : j ≠ 0) (hjl : j ≠ Fin.last count)
    {θ_ext : Fin count → (Fin n → ℝ) → ℝ} {σ : Fin count → Fin l}
    (hTB : T ⊆ B) (hBT : B ⊆ closure T) (hSB : S ⊆ B)
    (hθc : ∀ i, ContinuousOn (θ_ext i) B) (hθeq : ∀ i (x : T), θ_ext i x.1 = θ i x)
    (hφeq : ∀ i (x : S), θ_ext i x.1 = φ (σ i) x)
    {F : Set (Fin (n + 1) → ℝ)} (hF : F ∈ stackCells S φ)
    (hne_inter : (F ∩ closure (cylinder T '' sectorSet θ j)).Nonempty) :
    F ⊆ closure (cylinder T '' sectorSet θ j) := by
  cases count with
  | zero => exact absurd (Fin.eq_zero j) hj0
  | succ k =>
    cases j using Fin.cases with
    | zero => exact absurd rfl hj0
    | succ j' =>
      cases j' using Fin.lastCases with
      | last => exact absurd (Fin.succ_last k) hjl
      | cast m =>
        have hdic := subset_closure_or_disjoint_of_mem_stackCells_sectorSet_castSucc_succ hmono
          hφmono hTB hBT hSB (hθc m.castSucc) (hθc m.succ) (hθeq m.castSucc) (hθeq m.succ)
          (hφeq m.castSucc) (hφeq m.succ) hF
        exact (hdic.resolve_right (not_disjoint_iff_nonempty_inter.2 hne_inter)).1

/-- Root bounds and box dichotomy for a delineation `D_S` over `S ⊆ U_base` whose roots all lie in
`[t₀ - δ, t₀ + δ]` and include the two boundary heights `t₀ - δ` and `t₀ + δ`:
every root function is bounded, `2 ≤ D_S.count` with lowest root `t₀ - δ` and highest root `t₀ + δ`,
and each ambient cell `E ∈ stackCells S D_S.root` either lies inside the open box
`U' = {y | Fin.tail y ∈ U_base ∧ y 0 ∈ Ioo (t₀ - δ) (t₀ + δ)}` (with any sector index `j` satisfying
`j ≠ 0` and `j ≠ Fin.last D_S.count`) or is disjoint from `U'`. -/
private lemma box_properties_of_delineation {n : ℕ} {κ : Type*} {P : κ → (Fin n → ℝ) → ℝ[X]}
    {U_base S : Set (Fin n → ℝ)} {t₀ δ : ℝ} (hδ : 0 < δ) (hSU : S ⊆ U_base) (hSne : S.Nonempty)
    (D_S : Delineation fun k (x : S) ↦ P k x)
    (hlo_root : ∀ x : S, ∃ k, P k x.1 ≠ 0 ∧ (P k x.1).IsRoot (t₀ - δ))
    (hhi_root : ∀ x : S, ∃ k, P k x.1 ≠ 0 ∧ (P k x.1).IsRoot (t₀ + δ))
    (hroot_Icc : ∀ (x : S) k t, P k x.1 ≠ 0 → (P k x.1).IsRoot t → t ∈ Icc (t₀ - δ) (t₀ + δ)) :
    (∀ i, Bornology.IsBounded (range (D_S.root i))) ∧
      ∀ E ∈ stackCells S D_S.root,
        (E ⊆ {y : Fin (n + 1) → ℝ | Fin.tail y ∈ U_base ∧ y 0 ∈ Ioo (t₀ - δ) (t₀ + δ)} ∧
          ∀ j, E = cylinder S '' sectorSet D_S.root j → j ≠ 0 ∧ j ≠ Fin.last D_S.count) ∨
        Disjoint E {y : Fin (n + 1) → ℝ | Fin.tail y ∈ U_base ∧ y 0 ∈ Ioo (t₀ - δ) (t₀ + δ)} := by
  have hmem_Icc (i : Fin D_S.count) (x : S) : D_S.root i x ∈ Icc (t₀ - δ) (t₀ + δ) := by
    obtain ⟨k, hk0, hkr⟩ := (Set.ext_iff.1 (D_S.range_root x) (D_S.root i x)).1 ⟨i, rfl⟩
    exact hroot_Icc x k _ hk0 hkr
  have hbdd (i : Fin D_S.count) : Bornology.IsBounded (range (D_S.root i)) :=
    isCompact_Icc.isBounded.subset (range_subset_iff.2 (hmem_Icc i))
  obtain ⟨x₀, hx₀⟩ := hSne
  obtain ⟨k_lo₀, hk_lo₀, hr_lo₀⟩ := hlo_root ⟨x₀, hx₀⟩
  obtain ⟨i_lo₀, hi_lo₀⟩ := D_S.exists_root_eq k_lo₀ ⟨x₀, hx₀⟩ hk_lo₀ (t₀ - δ) hr_lo₀
  obtain ⟨k_hi₀, hk_hi₀, hr_hi₀⟩ := hhi_root ⟨x₀, hx₀⟩
  obtain ⟨i_hi₀, hi_hi₀⟩ := D_S.exists_root_eq k_hi₀ ⟨x₀, hx₀⟩ hk_hi₀ (t₀ + δ) hr_hi₀
  have hne_lh : i_lo₀ ≠ i_hi₀ := fun h ↦ by
    have : t₀ - δ = t₀ + δ := hi_lo₀.symm.trans ((congrArg (D_S.root · ⟨x₀, hx₀⟩) h).trans hi_hi₀)
    linarith
  have hcount : 2 ≤ D_S.count := by
    have h1 := i_lo₀.isLt
    have h2 := i_hi₀.isLt
    have h3 : i_lo₀.val ≠ i_hi₀.val := fun h ↦ hne_lh (Fin.ext h)
    omega
  let i₀ : Fin D_S.count := ⟨0, by omega⟩
  let i_max : Fin D_S.count := ⟨D_S.count - 1, by omega⟩
  have hi₀_val : i₀.val = 0 := rfl
  have hi_max_val : i_max.val = D_S.count - 1 := rfl
  have hroot_zero (x : S) : D_S.root i₀ x = t₀ - δ := by
    obtain ⟨k, hk, hr⟩ := hlo_root x
    obtain ⟨i, hi⟩ := D_S.exists_root_eq k x hk (t₀ - δ) hr
    have hle1 : t₀ - δ ≤ D_S.root i₀ x := (hmem_Icc i₀ x).1
    have hle2 : D_S.root i₀ x ≤ D_S.root i x :=
      (D_S.strictMono_root x).monotone (Fin.le_def.2 (by rw [hi₀_val]; exact Nat.zero_le _))
    linarith
  have hroot_max (x : S) : D_S.root i_max x = t₀ + δ := by
    obtain ⟨k, hk, hr⟩ := hhi_root x
    obtain ⟨i, hi⟩ := D_S.exists_root_eq k x hk (t₀ + δ) hr
    have hle1 : D_S.root i_max x ≤ t₀ + δ := (hmem_Icc i_max x).2
    have hle2 : D_S.root i x ≤ D_S.root i_max x :=
      (D_S.strictMono_root x).monotone (Fin.le_def.2 (by rw [hi_max_val]; have := i.isLt; omega))
    linarith
  refine ⟨hbdd, fun E hE ↦ ?_⟩
  set U' := {y : Fin (n + 1) → ℝ | Fin.tail y ∈ U_base ∧ y 0 ∈ Ioo (t₀ - δ) (t₀ + δ)}
  rcases mem_stackCells.1 hE with ⟨i, rfl⟩ | ⟨j, rfl⟩
  · by_cases hi : 0 < i.val ∧ i.val < D_S.count - 1
    · refine Or.inl ⟨fun y hy ↦ ?_, fun j hj ↦ ?_⟩
      · obtain ⟨hyS, hysec⟩ := mem_image_cylinder.1 hy
        simp only [mem_sectionSet] at hysec
        refine ⟨hSU hyS, ?_, ?_⟩
        · rw [← hysec, ← hroot_zero ⟨Fin.tail y, hyS⟩]
          exact D_S.strictMono_root ⟨Fin.tail y, hyS⟩ (Fin.lt_def.2 hi.1)
        · rw [← hysec, ← hroot_max ⟨Fin.tail y, hyS⟩]
          exact D_S.strictMono_root ⟨Fin.tail y, hyS⟩ (Fin.lt_def.2 hi.2)
      · exact False.elim (Set.Nonempty.not_disjoint
          ⟨cylinder S (⟨x₀, hx₀⟩, D_S.root i ⟨x₀, hx₀⟩),
            mem_image_of_mem _ (by simp [mem_sectionSet]),
            hj ▸ mem_image_of_mem _ (by simp [mem_sectionSet])⟩
          ((disjoint_image_iff cylinder_injective).2 (disjoint_sectionSet_sectorSet D_S.root i j)))
    · refine Or.inr (disjoint_left.2 fun y hy hyU' ↦ ?_)
      obtain ⟨hyS, hysec⟩ := mem_image_cylinder.1 hy
      simp only [mem_sectionSet] at hysec
      have hi_bound := i.isLt
      have hor : i = i₀ ∨ i = i_max := by
        rcases eq_or_ne i.val 0 with h0 | h0
        · exact Or.inl (Fin.ext h0)
        · exact Or.inr (Fin.ext (by rw [hi_max_val]; omega))
      rcases hor with rfl | rfl
      · linarith [hyU'.2.1, hysec, hroot_zero ⟨Fin.tail y, hyS⟩]
      · linarith [hyU'.2.2, hysec, hroot_max ⟨Fin.tail y, hyS⟩]
  · by_cases hj : j ≠ 0 ∧ j ≠ Fin.last D_S.count
    · refine Or.inl ⟨fun y hy ↦ ?_, fun j' hj' ↦ ?_⟩
      · obtain ⟨hyS, hysec⟩ := mem_image_cylinder.1 hy
        rw [mem_sectorSet] at hysec
        have hj_pos : 0 < j.val := Nat.pos_of_ne_zero fun h ↦ hj.1 (Fin.ext h)
        have hj_lt : j.val < D_S.count :=
          lt_of_le_of_ne (Nat.le_of_lt_succ j.isLt) fun h ↦ hj.2 (Fin.ext h)
        refine ⟨hSU hyS, ?_, ?_⟩
        · rw [← hroot_zero ⟨Fin.tail y, hyS⟩]
          exact hysec.1 i₀ (Fin.lt_def.2 hj_pos)
        · rw [← hroot_max ⟨Fin.tail y, hyS⟩]
          exact hysec.2 i_max (Fin.le_def.2 (by change j.val ≤ D_S.count - 1; omega))
      · have : j = j' := by
          by_contra hne
          have : Nonempty S := ⟨⟨x₀, hx₀⟩⟩
          obtain ⟨z, hz⟩ := sectorSet_nonempty D_S.strictMono_root j
          exact disjoint_left.1
            ((disjoint_image_iff cylinder_injective).2
              (pairwise_disjoint_sectorSet D_S.root hne))
            (mem_image_of_mem _ hz) (hj' ▸ mem_image_of_mem _ hz)
        exact this ▸ hj
    · refine Or.inr (disjoint_left.2 fun y hy hyU' ↦ ?_)
      obtain ⟨hyS, hysec⟩ := mem_image_cylinder.1 hy
      rw [mem_sectorSet] at hysec
      rcases eq_or_ne j 0 with rfl | hj0
      · have hlt := hysec.2 i₀ (Fin.le_def.2 (Nat.le_refl 0))
        linarith [hyU'.2.1, hroot_zero ⟨Fin.tail y, hyS⟩]
      · have hjl : j = Fin.last D_S.count := not_not.1 fun h ↦ hj ⟨hj0, h⟩
        subst hjl
        have hgt := hysec.1 i_max (Fin.lt_def.2 (by change D_S.count - 1 < D_S.count; omega))
        linarith [hyU'.2.2, hroot_max ⟨Fin.tail y, hyS⟩]

/-- **Cylindrical lifting of a normal decomposition.** Given a normal decomposition `(U_base, 𝒟)`
whose closures lie inside an open set `B₁`, and a finite family `P_ext` of monic real polynomials
of constant degrees `d_ext` with analytic coefficients on `B₁` whose real roots lie in
`[t₀ - δ, t₀ + δ]` and include both `t₀ - δ` and `t₀ + δ`, choosing a delineation `D S` of `P_ext`
over each `S ∈ 𝒟` produces a normal decomposition `𝒞'` of the open cylinder
`U' = U_base × (t₀ - δ, t₀ + δ)` on every stratum of which each `P_ext k` is sign-invariant. -/
private lemma lift_isNormalDecomposition_of_box {n : ℕ} {κ : Type*} [Finite κ]
    {B₁ U_base : Set (Fin n → ℝ)} {𝒟 : Set (Set (Fin n → ℝ))}
    (h𝒟 : IsNormalDecomposition U_base 𝒟) (hcl_B₁ : ∀ S ∈ 𝒟, closure S ⊆ B₁)
    {P_ext : κ → (Fin n → ℝ) → ℝ[X]} {d_ext : κ → ℕ} {t₀ δ : ℝ} (hδ : 0 < δ)
    (hmonic : ∀ k x, (P_ext k x).Monic) (hdeg : ∀ k x, (P_ext k x).natDegree = d_ext k)
    (hcoeff : ∀ k j, AnalyticOnNhd ℝ (fun x ↦ (P_ext k x).coeff j) B₁)
    (hP_eval : ∀ k, ContinuousOn (fun z : (Fin n → ℝ) × ℝ ↦ (P_ext k z.1).eval z.2) (B₁ ×ˢ univ))
    (hlo_root : ∀ x ∈ B₁, ∃ k, (P_ext k x).IsRoot (t₀ - δ))
    (hhi_root : ∀ x ∈ B₁, ∃ k, (P_ext k x).IsRoot (t₀ + δ))
    (hroot_Icc : ∀ x ∈ B₁, ∀ k t, (P_ext k x).IsRoot t → t ∈ Icc (t₀ - δ) (t₀ + δ))
    (D : ∀ S : 𝒟, Delineation fun k (x : S.1) ↦ P_ext k x) :
    let U' := {y : Fin (n + 1) → ℝ | Fin.tail y ∈ U_base ∧ y 0 ∈ Ioo (t₀ - δ) (t₀ + δ)}
    let 𝒞' := ⋃ S : 𝒟, {E ∈ stackCells S.1 (D S).root | E ⊆ U'}
    IsNormalDecomposition U' 𝒞' ∧
      ∀ k, ∀ E ∈ 𝒞', SignInvariant (fun y ↦ (P_ext k (Fin.tail y)).eval (y 0)) E := by
  intro U' 𝒞'
  have : Finite 𝒟 := h𝒟.finite.to_subtype
  have hS_B₁ (S : 𝒟) : S.1 ⊆ B₁ := subset_closure.trans (hcl_B₁ S.1 S.2)
  have hbox (S : 𝒟) := box_properties_of_delineation hδ (h𝒟.subset_of_mem S.2)
    (h𝒟.nonempty_of_mem S.2) (D S)
    (fun x ↦ let ⟨k, hk⟩ := hlo_root x.1 (hS_B₁ S x.2); ⟨k, (hmonic k x.1).ne_zero, hk⟩)
    (fun x ↦ let ⟨k, hk⟩ := hhi_root x.1 (hS_B₁ S x.2); ⟨k, (hmonic k x.1).ne_zero, hk⟩)
    (fun x k t _ ht ↦ hroot_Icc x.1 (hS_B₁ S x.2) k t ht)
  -- Continuous extensions of the bounded root functions of `D T` across `U_base ∩ closure T.1`.
  have hroot_ext (T : 𝒟) :
      ∃ θ_ext : Fin (D T).count → (Fin n → ℝ) → ℝ,
        (∀ i, ContinuousOn (θ_ext i) (U_base ∩ closure T.1)) ∧
        (∀ i (x : T.1), θ_ext i x.1 = (D T).root i x) ∧
        (∀ x ∈ U_base ∩ closure T.1, Monotone fun i ↦ θ_ext i x) ∧
        ∀ i, ∃ k, (∀ x : T.1, P_ext k x.1 ≠ 0) ∧
          ∀ x ∈ U_base ∩ closure T.1, (P_ext k x).IsRoot (θ_ext i x) :=
    (D T).exists_continuousOn_root_extension
      (fun x hx ↦ ⟨h𝒟.subset_of_mem T.2 hx, subset_closure hx⟩) inter_subset_right (hbox T).1
      (fun k ↦ (hP_eval k).mono (prod_mono_left (hcl_B₁ T.1 T.2)))
      (fun k _ x _ ↦ (hmonic k x).ne_zero)
      (fun x hx ↦ h𝒟.isPreconnectedApproachAt T.1 T.2 x hx.1)
  have hsubmanifold_sec (S : 𝒟) {dS : ℕ} (hdS : IsAnalyticSubmanifold dS S.1)
      (r : Fin (D S).count) :
      IsAnalyticSubmanifold dS (cylinder S.1 '' sectionSet (D S).root r) :=
    (D S).isAnalyticSubmanifold_sectionSet hdS
      (fun k j ↦ ((hcoeff k j).mono (hS_B₁ S)).analyticOnSubmanifold hdS) r
  -- Establish frontier containment and dimension drop simultaneously for pairs in `𝒞'`.
  have hfrontier {F E : Set (Fin (n + 1) → ℝ)} (hF : F ∈ 𝒞') (hE : E ∈ 𝒞')
      (hne_inter : (F ∩ closure E).Nonempty) :
      F ⊆ closure E ∧
        (F ≠ E → ∀ dF dE, IsAnalyticSubmanifold dF F → IsAnalyticSubmanifold dE E → dF < dE) := by
    obtain ⟨S, hF_cell, hF_sub⟩ := mem_iUnion.1 hF
    obtain ⟨T, hE_cell, hE_sub⟩ := mem_iUnion.1 hE
    obtain ⟨y₀, hy₀F, hy₀cl⟩ := id hne_inter
    have hFS : F ⊆ Fin.tail ⁻¹' S.1 := by
      rw [← sUnion_stackCells fun x ↦ ((D S).strictMono_root x).monotone]
      exact subset_sUnion_of_mem hF_cell
    have hET : E ⊆ Fin.tail ⁻¹' closure T.1 := fun z hz ↦ by
      have : z ∈ Fin.tail ⁻¹' T.1 := by
        rw [← sUnion_stackCells fun x ↦ ((D T).strictMono_root x).monotone]
        exact subset_sUnion_of_mem hE_cell hz
      exact subset_closure this
    have hy₀_clT : Fin.tail y₀ ∈ closure T.1 :=
      closure_minimal hET (isClosed_closure.preimage (by fun_prop)) hy₀cl
    have hS_clT : S.1 ⊆ closure T.1 :=
      h𝒟.subset_closure_of_inter_closure_nonempty S.1 S.2 T.1 T.2 ⟨Fin.tail y₀, hFS hy₀F, hy₀_clT⟩
    have hSB : S.1 ⊆ U_base ∩ closure T.1 := subset_inter (h𝒟.subset_of_mem S.2) hS_clT
    obtain ⟨dS, hdS⟩ := h𝒟.exists_isAnalyticSubmanifold S.1 S.2
    obtain ⟨dT, hdT⟩ := h𝒟.exists_isAnalyticSubmanifold T.1 T.2
    obtain ⟨θ_ext, hθc, hθeq, hθmono, hθroot⟩ := hroot_ext T
    obtain ⟨σ, -, hφeq⟩ := (D S).exists_monotone_root_eq_of_subset (h𝒟.isConnected S.1 S.2) hSB
      hθc hθmono fun i ↦
        let ⟨k, _, hk⟩ := hθroot i
        ⟨k, fun x _ ↦ (hmonic k x).ne_zero, fun x hx ↦ hk x (hSB hx)⟩
    have hTB : T.1 ⊆ U_base ∩ closure T.1 :=
      subset_inter (h𝒟.subset_of_mem T.2) subset_closure
    rcases mem_stackCells.1 hE_cell with ⟨i, rfl⟩ | ⟨j, rfl⟩
    · -- `E` is a section over `T.1`.
      have hdic := subset_closure_or_disjoint_of_mem_stackCells_sectionSet (D S).strictMono_root
        hTB inter_subset_right hSB (hθc i) (hθeq i) (hφeq i) hF_cell
      obtain ⟨rfl, hsub⟩ := hdic.resolve_right (not_disjoint_iff_nonempty_inter.2 hne_inter)
      refine ⟨hsub, fun hFE dF dE hdF hdE ↦ ?_⟩
      have hdF_eq : dF = dS := hdF.dim_eq (hsubmanifold_sec S hdS (σ i))
      have hdE_eq : dE = dT := hdE.dim_eq (hsubmanifold_sec T hdT i)
      have hST : S.1 ≠ T.1 := by
        intro hST_val
        have hST : S = T := Subtype.ext hST_val
        subst hST
        obtain ⟨x_S, hx_S⟩ := h𝒟.nonempty_of_mem S.2
        have hσi : σ i = i := ((D S).strictMono_root ⟨x_S, hx_S⟩).injective <| by
          rw [← hφeq i ⟨x_S, hx_S⟩, hθeq i ⟨x_S, hx_S⟩]
        exact hFE (congrArg (cylinder S.1 '' sectionSet (D S).root ·) hσi)
      have := h𝒟.dim_lt_of_ne_of_subset_closure S.1 S.2 T.1 T.2 hST hS_clT dS dT hdS hdT
      omega
    · -- `E` is a bounded sector over `T.1`.
      have hj_ne : j ≠ 0 ∧ j ≠ Fin.last (D T).count :=
        ((hbox T).2 _ hE_cell).resolve_right
          (not_disjoint_iff_nonempty_inter.2
            ((isConnected_of_mem_stackCells (h𝒟.isConnected T.1 T.2) (D T).continuous_root
              (D T).strictMono_root hE_cell).nonempty.mono (subset_inter subset_rfl hE_sub)))
          |>.2 j rfl
      by_cases hST : S = T
      · subst hST
        obtain ⟨hsub, hshape⟩ := subset_closure_and_section_or_eq_of_same_base_sectorSet
          (D S).continuous_root (D S).strictMono_root hj_ne.1 hj_ne.2 hF_cell hne_inter
        refine ⟨hsub, fun hFE dF dE hdF hdE ↦ ?_⟩
        rcases hshape with ⟨r, rfl⟩ | hEq
        · have hdF_eq : dF = dS := hdF.dim_eq (hsubmanifold_sec S hdS r)
          have hdE_eq : dE = dS + 1 := hdE.dim_eq
            (isAnalyticSubmanifold_image_cylinder_sectorSet hdS (D S).continuous_root
              (D S).strictMono_root j)
          omega
        · exact False.elim (hFE hEq)
      · have hST_val : S.1 ≠ T.1 := fun h ↦ hST (Subtype.ext h)
        have hsub := subset_closure_of_mem_stackCells_sectorSet_of_ne (D T).strictMono_root
          (D S).strictMono_root hj_ne.1 hj_ne.2 hTB inter_subset_right hSB hθc hθeq hφeq hF_cell
          hne_inter
        refine ⟨hsub, fun _ dF dE hdF hdE ↦ ?_⟩
        have hdE_eq : dE = dT + 1 := hdE.dim_eq
          (isAnalyticSubmanifold_image_cylinder_sectorSet hdT (D T).continuous_root
            (D T).strictMono_root j)
        obtain ⟨eF, heF_or, heF⟩ := (D S).exists_isAnalyticSubmanifold_of_mem_stackCells hdS
          (fun k l ↦ ((hcoeff k l).mono (hS_B₁ S)).analyticOnSubmanifold hdS) hF_cell
        have hdF_eq : dF = eF := hdF.dim_eq heF
        have hd_lt := h𝒟.dim_lt_of_ne_of_subset_closure S.1 S.2 T.1 T.2 hST_val hS_clT dS dT hdS hdT
        rcases heF_or with rfl | rfl <;> omega
  refine ⟨{
    isOpen_domain := (h𝒟.isOpen_domain.preimage (by fun_prop)).inter
      (isOpen_Ioo.preimage (continuous_apply 0))
    finite := finite_iUnion fun S ↦ (finite_stackCells S.1 (D S).root).subset (sep_subset _ _)
    pairwiseDisjoint := by
      rintro E₁ hE₁ E₂ hE₂ hne
      obtain ⟨S₁, hc₁, -⟩ := mem_iUnion.1 hE₁
      obtain ⟨S₂, hc₂, -⟩ := mem_iUnion.1 hE₂
      by_cases hS : S₁ = S₂
      · subst hS
        exact pairwiseDisjoint_stackCells (fun x ↦ ((D S₁).strictMono_root x).injective)
          hc₁ hc₂ hne
      · have hd_base := h𝒟.pairwiseDisjoint S₁.2 S₂.2 fun h ↦ hS (Subtype.ext h)
        refine disjoint_left.2 fun y hy₁ hy₂ ↦ ?_
        have hy₁' : Fin.tail y ∈ S₁.1 := by
          have : y ∈ ⋃₀ stackCells S₁.1 (D S₁).root := subset_sUnion_of_mem hc₁ hy₁
          rwa [sUnion_stackCells fun x ↦ ((D S₁).strictMono_root x).monotone] at this
        have hy₂' : Fin.tail y ∈ S₂.1 := by
          have : y ∈ ⋃₀ stackCells S₂.1 (D S₂).root := subset_sUnion_of_mem hc₂ hy₂
          rwa [sUnion_stackCells fun x ↦ ((D S₂).strictMono_root x).monotone] at this
        exact disjoint_left.1 hd_base hy₁' hy₂'
    sUnion_eq := by
      refine subset_antisymm (sUnion_subset fun E hE ↦ ?_) (fun y hy ↦ ?_)
      · obtain ⟨S, -, hsub⟩ := mem_iUnion.1 hE
        exact hsub
      · obtain ⟨S, hS, hyS⟩ := h𝒟.exists_mem hy.1
        have hy_cyl : y ∈ ⋃₀ stackCells S (D ⟨S, hS⟩).root := by
          rw [sUnion_stackCells fun x ↦ ((D ⟨S, hS⟩).strictMono_root x).monotone]
          exact hyS
        obtain ⟨E, hE_cell, hyE⟩ := mem_sUnion.1 hy_cyl
        have hE_sub : E ⊆ U' := (((hbox ⟨S, hS⟩).2 E hE_cell).resolve_right
          (not_disjoint_iff_nonempty_inter.2 ⟨y, hyE, hy⟩)).1
        exact mem_sUnion.2 ⟨E, mem_iUnion.2 ⟨⟨S, hS⟩, hE_cell, hE_sub⟩, hyE⟩
    isConnected := by
      rintro E hE
      obtain ⟨S, hE_cell, -⟩ := mem_iUnion.1 hE
      exact isConnected_of_mem_stackCells (h𝒟.isConnected S.1 S.2) (D S).continuous_root
        (D S).strictMono_root hE_cell
    isSemianalytic := by
      rintro E hE
      obtain ⟨S, hE_cell, -⟩ := mem_iUnion.1 hE
      refine (D S).isSemianalytic_of_mem_stackCells (h𝒟.isSemianalytic S.1 S.2) (fun x hx ↦ ?_)
        hE_cell
      exact ⟨d_ext, fun k j _ ↦ hcoeff k j x (hcl_B₁ S.1 S.2 hx),
        fun k ↦ Eventually.of_forall fun z ↦ (hdeg k z).le⟩
    exists_isAnalyticSubmanifold := by
      rintro E hE
      obtain ⟨S, hE_cell, -⟩ := mem_iUnion.1 hE
      obtain ⟨dS, hdS⟩ := h𝒟.exists_isAnalyticSubmanifold S.1 S.2
      obtain ⟨dE, -, hdE⟩ := (D S).exists_isAnalyticSubmanifold_of_mem_stackCells hdS
        (fun k j ↦ ((hcoeff k j).mono (hS_B₁ S)).analyticOnSubmanifold hdS) hE_cell
      exact ⟨dE, hdE⟩
    isPreconnectedApproachAt := by
      rintro E hE y hy
      obtain ⟨T, hE_cell, hE_sub⟩ := mem_iUnion.1 hE
      obtain ⟨θ_ext, hθc, hθeq, -, -⟩ := hroot_ext T
      have hy_or : Fin.tail y ∈ U_base ∩ closure T.1 ∨ Fin.tail y ∉ closure T.1 := by
        by_cases h : Fin.tail y ∈ closure T.1
        · exact Or.inl ⟨hy.1, h⟩
        · exact Or.inr h
      have hTB : T.1 ⊆ U_base ∩ closure T.1 :=
        subset_inter (h𝒟.subset_of_mem T.2) subset_closure
      have hconn_B : ∀ x ∈ U_base ∩ closure T.1, IsPreconnectedApproachAt T.1 x :=
        fun x hx ↦ h𝒟.isPreconnectedApproachAt T.1 T.2 x hx.1
      rcases mem_stackCells.1 hE_cell with ⟨i, rfl⟩ | ⟨j, rfl⟩
      · exact isPreconnectedApproachAt_image_cylinder_sectionSet hTB (hθc i) (hθeq i) hconn_B hy_or
      · have hj_ne : j ≠ 0 ∧ j ≠ Fin.last (D T).count :=
          ((hbox T).2 _ hE_cell).resolve_right
            (not_disjoint_iff_nonempty_inter.2
              ((isConnected_of_mem_stackCells (h𝒟.isConnected T.1 T.2) (D T).continuous_root
                 (D T).strictMono_root hE_cell).nonempty.mono (subset_inter subset_rfl hE_sub)))
            |>.2 j rfl
        exact isPreconnectedApproachAt_image_cylinder_sectorSet_of_ne (D T).strictMono_root hj_ne.1
          hj_ne.2 hTB hθc hθeq hconn_B hy_or
    subset_closure_of_inter_closure_nonempty := fun F hF E hE hne ↦ (hfrontier hF hE hne).1
    dim_lt_of_ne_of_subset_closure := fun F hF E hE hFE hsub dF dE hdF hdE ↦ by
      obtain ⟨S, hF_cell, -⟩ := mem_iUnion.1 hF
      have hne : (F ∩ closure E).Nonempty :=
        (isConnected_of_mem_stackCells (h𝒟.isConnected S.1 S.2) (D S).continuous_root
          (D S).strictMono_root hF_cell).nonempty.mono (subset_inter subset_rfl hsub)
      exact (hfrontier hF hE hne).2 hFE dF dE hdF hdE
  }, fun k E hE ↦ ?_⟩
  obtain ⟨S, hE_cell, -⟩ := mem_iUnion.1 hE
  have hcomp : ((fun y ↦ (P_ext k (Fin.tail y)).eval (y 0)) ∘ cylinder S.1) =
      fun z : S.1 × ℝ ↦ (P_ext k z.1.1).eval z.2 := by
    ext z
    simp
  rcases mem_stackCells.1 hE_cell with ⟨i, rfl⟩ | ⟨j, rfl⟩ <;>
    rw [signInvariant_image, hcomp]
  · exact (D S).signInvariant_sectionSet k i
  · exact (D S).signInvariant_sectorSet k j

/-! ### Main local normal-decomposition theorems -/

private lemma exists_isNormalDecomposition_signInvariant_fin {n m : ℕ}
    {f : Fin m → (Fin n → ℝ) → ℝ} {x₀ : Fin n → ℝ} (hf : ∀ i, AnalyticAt ℝ (f i) x₀)
    {V : Set (Fin n → ℝ)} (hV : V ∈ 𝓝 x₀) :
    ∃ U ⊆ V, x₀ ∈ U ∧ ∃ 𝒞 : Set (Set (Fin n → ℝ)),
      IsNormalDecomposition U 𝒞 ∧ ∀ i, ∀ S ∈ 𝒞, SignInvariant (f i) S := by
  induction n generalizing m with
  | zero =>
    have hV_univ : V = univ := eq_univ_of_forall fun y ↦ by
      simpa only [Subsingleton.elim y x₀] using mem_of_mem_nhds hV
    refine ⟨univ, hV_univ ▸ subset_rfl, mem_univ x₀, {univ}, isNormalDecomposition_singleton_univ,
      fun i S _ ↦ Set.Subsingleton.signInvariant subsingleton_of_subsingleton⟩
  | succ n ih =>
    classical
    -- Separate identically vanishing germs at `x₀` from nonvanishing germs.
    let ι₀ := {i : Fin m // f i =ᶠ[𝓝 x₀] 0}
    let ι' := {i : Fin m // ¬f i =ᶠ[𝓝 x₀] 0}
    have hzero_ev : ∀ᶠ y in 𝓝 x₀, ∀ i : ι₀, f i.1 y = 0 := eventually_all.2 fun i ↦ i.2
    obtain ⟨V₀, hV₀_sub, hV₀_open, hx₀V₀⟩ := eventually_nhds_iff.1 (inter_mem hV hzero_ev)
    -- Identify `(Fin n → ℝ) × ℝ` with `Fin (n + 1) → ℝ` via `(b, t) ↦ Fin.cons t b`.
    let e_prod : ((Fin n → ℝ) × ℝ) ≃L[ℝ] Fin (n + 1) → ℝ :=
      (ContinuousLinearEquiv.prodComm ℝ (Fin n → ℝ) ℝ).trans (Fin.consEquivL ℝ fun _ ↦ ℝ)
    have he_prod_apply (p : (Fin n → ℝ) × ℝ) : e_prod p = Fin.cons p.2 p.1 := rfl
    let p₀ : (Fin n → ℝ) × ℝ := e_prod.symm x₀
    have hg₀_an (i : ι') : AnalyticAt ℝ (fun p ↦ f i.1 (e_prod p)) p₀ :=
      (hf i.1).comp_of_eq (e_prod.analyticAt p₀) (e_prod.apply_symm_apply x₀)
    have hg₀_ne (i : ι') : ¬(fun p ↦ f i.1 (e_prod p)) =ᶠ[𝓝 p₀] 0 := fun h ↦ i.2 <| by
      have hpre := e_prod.symm.continuous.continuousAt (x := x₀) |>.eventually h
      exact hpre.mono fun y hy ↦ by
        simpa only [Function.comp_apply, Pi.zero_apply, e_prod.apply_symm_apply] using hy
    -- Simultaneous linear change of coordinates into Weierstrass general position.
    obtain ⟨L₀, q₀, hL₀q₀, hord⟩ :=
      exists_continuousLinearEquiv_forall_analyticOrderAt_ne_top hg₀_an hg₀_ne
    set b₀ : Fin n → ℝ := q₀.1
    set t₀ : ℝ := q₀.2
    have hq₀ : (b₀, t₀) = q₀ := Prod.mk.eta
    let L : (Fin (n + 1) → ℝ) ≃L[ℝ] Fin (n + 1) → ℝ :=
      e_prod.symm.trans (L₀.trans e_prod)
    let y₀ : Fin (n + 1) → ℝ := e_prod q₀
    have hLy₀ : L y₀ = x₀ := by
      simp only [L, y₀, p₀, ContinuousLinearEquiv.trans_apply,
        ContinuousLinearEquiv.symm_apply_apply, hL₀q₀]
      exact e_prod.apply_symm_apply x₀
    let g : ι' → (Fin n → ℝ) × ℝ → ℝ := fun i p ↦ f i.1 (L (e_prod p))
    have hg_eq (i : ι') (p : (Fin n → ℝ) × ℝ) : g i p = f i.1 (e_prod (L₀ p)) := by
      simp [g, L]
    have hg_comp (i : ι') : g i = (fun p ↦ f i.1 (e_prod p)) ∘ L₀ := funext (hg_eq i)
    have hg_an (i : ι') : AnalyticAt ℝ (g i) (b₀, t₀) := by
      rw [hg_comp i, hq₀]
      exact (hg₀_an i).comp_of_eq (L₀.analyticAt q₀) hL₀q₀
    have hg_ord (i : ι') : analyticOrderAt (fun t ↦ g i (b₀, t)) t₀ ≠ ⊤ := by
      simpa only [hg_eq] using hord i
    choose d hd using fun i ↦ ENat.ne_top_iff_exists.1 (hg_ord i)
    choose c u hc hc0 hu hu0 hfac using
      fun i ↦ (hg_an i).exists_weierstrassPreparation_real (hd i).symm
    -- Shrink to a product box `W_b × (t₀ - δ, t₀ + δ)` inside `L ⁻¹' V₀` where each unit `u i` has
    -- constant nonzero sign and each Weierstrass factorization holds.
    have hu_sign (i : ι') :
        ∀ᶠ p in 𝓝 (b₀, t₀), SignType.sign (u i p) = SignType.sign (u i (b₀, t₀)) :=
      ((continuousAt_sign_of_ne_zero (hu0 i)).comp (hu i).continuousAt)
        ((isOpen_discrete _).mem_nhds (mem_singleton _))
    have hbox_ev : ∀ᶠ p in 𝓝 (b₀, t₀),
        L (e_prod p) ∈ V₀ ∧
        (∀ i : ι', g i p =
          (TauCeti.Polynomial.monicOfCoeff (fun l ↦ c i l p.1)).eval (p.2 - t₀) * u i p) ∧
        ∀ i : ι', SignType.sign (u i p) = SignType.sign (u i (b₀, t₀)) := by
      have hV₀_ev : ∀ᶠ p in 𝓝 (b₀, t₀), L (e_prod p) ∈ V₀ :=
        (L.continuous.comp e_prod.continuous).continuousAt.eventually
          (hV₀_open.mem_nhds (by simpa only [Function.comp_apply, y₀] using hLy₀.symm ▸ hx₀V₀))
      exact hV₀_ev.and ((eventually_all.2 hfac).and (eventually_all.2 hu_sign))
    obtain ⟨W_b, hW_b, W_t, hW_t, hW_prod⟩ := mem_nhds_prod_iff.1 hbox_ev
    obtain ⟨δ, hδ, hδ_sub⟩ := Metric.mem_nhds_iff.1 hW_t
    -- Choose `r₁ > 0` so all `c i l` are analytic on `B₁ = ball b₀ r₁` with Fujiwara's bound.
    have hc_small : ∀ᶠ x in 𝓝 b₀, ∀ i : ι', ∀ l : Fin (d i),
        AnalyticAt ℝ (c i l) x ∧ ‖c i l x‖ ≤ (min 1 (δ / 4)) ^ (d i - l.val) := by
      refine eventually_all.2 fun i ↦ eventually_all.2 fun l ↦ (hc i l).eventually_analyticAt.and ?_
      have hpos : (0 : ℝ) < (min 1 (δ / 4)) ^ (d i - l.val) := by
        have : (0 : ℝ) < min 1 (δ / 4) := lt_min zero_lt_one (by positivity)
        positivity
      have hlim : Tendsto (fun x ↦ ‖c i l x‖) (𝓝 b₀) (𝓝 0) := by
        simpa only [hc0 i l, norm_zero] using (hc i l).continuousAt.tendsto.norm
      exact (hlim.eventually (isOpen_Iio.mem_nhds (mem_Iio.2 hpos))).mono fun _ hx ↦ hx.le
    have hW_b_ev : ∀ᶠ x in 𝓝 b₀, x ∈ W_b := hW_b
    obtain ⟨r₁, hr₁, hr₁_ball⟩ := Metric.eventually_nhds_iff.1 (hW_b_ev.and hc_small)
    set B₁ := Metric.ball b₀ r₁
    have hc_B₁ (i : ι') (l : Fin (d i)) : AnalyticOnNhd ℝ (c i l) B₁ :=
      fun x hx ↦ ((hr₁_ball hx).2 i l).1
    -- Define the extended monic polynomial family `P_ext : (ι' ⊕ Bool) → (Fin n → ℝ) → ℝ[X]`.
    let P_ext : (ι' ⊕ Bool) → (Fin n → ℝ) → ℝ[X]
      | .inl i, x => (TauCeti.Polynomial.monicOfCoeff (fun l ↦ c i l x)).comp (X - C t₀)
      | .inr false, _ => X - C (t₀ - δ)
      | .inr true, _ => X - C (t₀ + δ)
    let d_ext : ι' ⊕ Bool → ℕ
      | .inl i => d i
      | .inr _ => 1
    have hmonic_eq (i : ι') (x : Fin n → ℝ) :
        TauCeti.Polynomial.monicOfCoeff (fun l ↦ c i l x) =
          X ^ d i + ∑ l : Fin (d i), C (c i l x) * X ^ (l : ℕ) := by
      conv_lhs => rw [(TauCeti.Polynomial.monicOfCoeff fun l ↦ c i l x).as_sum_range_C_mul_X_pow]
      rw [TauCeti.Polynomial.natDegree_monicOfCoeff, Finset.sum_range_succ,
        TauCeti.Polynomial.coeff_monicOfCoeff_self, map_one, one_mul, add_comm,
        ← Fin.sum_univ_eq_sum_range]
      simp only [TauCeti.Polynomial.coeff_monicOfCoeff]
    have hP_inl_eq (i : ι') (x : Fin n → ℝ) :
        P_ext (.inl i) x =
          (X - C t₀) ^ d i + ∑ l : Fin (d i), C (c i l x) * (X - C t₀) ^ (l : ℕ) := by
      simp only [P_ext, hmonic_eq, add_comp, X_pow_comp, sum_comp, mul_comp, C_comp]
    have hP_monic (k : ι' ⊕ Bool) (x : Fin n → ℝ) : (P_ext k x).Monic := by
      rcases k with i | (_ | _)
      · exact (TauCeti.Polynomial.monic_monicOfCoeff _).comp_X_sub_C t₀
      · exact monic_X_sub_C _
      · exact monic_X_sub_C _
    have hP_deg (k : ι' ⊕ Bool) (x : Fin n → ℝ) : (P_ext k x).natDegree = d_ext k := by
      rcases k with i | (_ | _)
      · rw [natDegree_comp, TauCeti.Polynomial.natDegree_monicOfCoeff, natDegree_X_sub_C, mul_one]
      · exact natDegree_X_sub_C _
      · exact natDegree_X_sub_C _
    have hP_coeff (k : ι' ⊕ Bool) (j : ℕ) :
        AnalyticOnNhd ℝ (fun x ↦ (P_ext k x).coeff j) B₁ := by
      rcases k with i | (_ | _)
      · have heq : (fun x ↦ (P_ext (.inl i) x).coeff j) =
            fun x ↦ ((X - C t₀ : ℝ[X]) ^ d i).coeff j +
              ∑ l : Fin (d i), c i l x * ((X - C t₀ : ℝ[X]) ^ (l : ℕ)).coeff j := by
          ext x
          simp only [hP_inl_eq, coeff_add, finsetSum_coeff, coeff_C_mul]
        rw [heq]
        exact AnalyticOnNhd.fun_add analyticOnNhd_const
          (Finset.analyticOnNhd_fun_sum _ fun l _ ↦
            AnalyticOnNhd.mul (hc_B₁ i l) analyticOnNhd_const)
      · exact analyticOnNhd_const
      · exact analyticOnNhd_const
    have hP_eval (k : ι' ⊕ Bool) :
        ContinuousOn (fun z : (Fin n → ℝ) × ℝ ↦ (P_ext k z.1).eval z.2) (B₁ ×ˢ univ) := by
      have han : AnalyticOnNhd ℝ
          (fun z : (Fin n → ℝ) × ℝ ↦
            ∑ j ∈ Finset.range (d_ext k + 1), (P_ext k z.1).coeff j * z.2 ^ j)
          (B₁ ×ˢ univ) :=
        Finset.analyticOnNhd_fun_sum _ fun j _ ↦
          AnalyticOnNhd.mul
            (AnalyticOnNhd.fun_comp (hP_coeff k j) (analyticOnNhd_fst (t := B₁ ×ˢ univ))
              fun _ hz ↦ hz.1)
            (AnalyticOnNhd.fun_pow analyticOnNhd_snd j)
      exact han.continuousOn.congr fun z _ ↦ by rw [eval_eq_sum_range, hP_deg k z.1]
    have hP_roots_Icc (x : Fin n → ℝ) (hx : x ∈ B₁) (k : ι' ⊕ Bool) (t : ℝ)
        (ht : (P_ext k x).IsRoot t) : t ∈ Icc (t₀ - δ) (t₀ + δ) := by
      rcases k with i | (_ | _)
      · have hroot_sub : (TauCeti.Polynomial.monicOfCoeff (fun l ↦ c i l x)).IsRoot (t - t₀) := by
          simpa only [P_ext, IsRoot.def, eval_comp, eval_sub, eval_X, eval_C] using ht
        have hnorm : ‖t - t₀‖ ≤ 2 * min 1 (δ / 4) :=
          hroot_sub.norm_le_two_mul (TauCeti.Polynomial.monic_monicOfCoeff _) fun m hm ↦ by
            rw [TauCeti.Polynomial.natDegree_monicOfCoeff] at hm ⊢
            simpa only [TauCeti.Polynomial.coeff_monicOfCoeff _ ⟨m, hm⟩] using
              ((hr₁_ball hx).2 i ⟨m, hm⟩).2
        have habs : |t - t₀| ≤ δ / 2 := by
          rw [Real.norm_eq_abs] at hnorm
          have : min 1 (δ / 4) ≤ δ / 4 := min_le_right _ _
          linarith
        rw [abs_le] at habs
        exact ⟨by linarith, by linarith⟩
      · have : t = t₀ - δ := sub_eq_zero.1 (by simpa [P_ext, IsRoot.def] using ht)
        exact ⟨by linarith, by linarith⟩
      · have : t = t₀ + δ := sub_eq_zero.1 (by simpa [P_ext, IsRoot.def] using ht)
        exact ⟨by linarith, by linarith⟩
    -- Apply Collins' analytic projection and the induction hypothesis on `ball b₀ (r₁ / 2)`.
    obtain ⟨g_proj, hg_proj, hdelin⟩ := exists_analyticOnNhd_projection_delineation
      (fun k j _ ↦ hP_coeff k j) (fun k x _ ↦ (hP_deg k x).le)
    let e_proj : Fin g_proj.card ≃ g_proj := g_proj.equivFin.symm
    obtain ⟨U_base, hU_base_sub, hb₀U, 𝒟, h𝒟, hsign_base⟩ := ih
      (f := fun j : Fin g_proj.card ↦ (e_proj j).1)
      (fun j ↦ hg_proj (e_proj j).1 (e_proj j).2 b₀ (Metric.mem_ball_self hr₁))
      (Metric.ball_mem_nhds b₀ (half_pos hr₁))
    have hcl_B₁ (S : Set (Fin n → ℝ)) (hS : S ∈ 𝒟) : closure S ⊆ B₁ :=
      (closure_mono ((h𝒟.subset_of_mem hS).trans hU_base_sub)).trans
        (Metric.closure_ball_subset_closedBall.trans
          (Metric.closedBall_subset_ball (half_lt_self hr₁)))
    let D (S : 𝒟) : Delineation fun k (x : S.1) ↦ P_ext k x :=
      (hdelin S.1 (subset_closure.trans (hcl_B₁ S.1 S.2)) (h𝒟.isPreconnected_of_mem S.2)
        fun a ha x hx y hy ↦ by
          have h := signInvariant_def.1 (hsign_base (g_proj.equivFin ⟨a, ha⟩) S.1 S.2) x hx y hy
          simp only [e_proj, Equiv.symm_apply_apply] at h
          rw [← sign_eq_zero_iff, h, sign_eq_zero_iff]).some
    obtain ⟨h𝒞', hsign_P⟩ := lift_isNormalDecomposition_of_box h𝒟 hcl_B₁ hδ hP_monic hP_deg
      hP_coeff hP_eval
      (fun x _ ↦ ⟨.inr false, by simp [P_ext]⟩)
      (fun x _ ↦ ⟨.inr true, by simp [P_ext]⟩)
      hP_roots_Icc D
    set U' := {y : Fin (n + 1) → ℝ | Fin.tail y ∈ U_base ∧ y 0 ∈ Ioo (t₀ - δ) (t₀ + δ)}
    set 𝒞' := ⋃ S : 𝒟, {E ∈ stackCells S.1 (D S).root | E ⊆ U'}
    have hy₀U' : y₀ ∈ U' := by
      refine ⟨?_, ?_⟩
      · simpa only [y₀, he_prod_apply, Fin.tail_cons] using hb₀U
      · simpa only [y₀, he_prod_apply, Fin.cons_zero] using ⟨by linarith, by linarith⟩
    have hU'_box (y : Fin (n + 1) → ℝ) (hy : y ∈ U') : (Fin.tail y, y 0) ∈ W_b ×ˢ W_t := by
      refine ⟨(hr₁_ball (Metric.ball_subset_ball (half_le_self hr₁.le) (hU_base_sub hy.1))).1,
        hδ_sub ?_⟩
      rw [Real.ball_eq_Ioo]
      exact hy.2
    have hU'_V₀ (y : Fin (n + 1) → ℝ) (hy : y ∈ U') : L y ∈ V₀ := by
      simpa only [he_prod_apply, Fin.cons_self_tail] using (hW_prod (hU'_box y hy)).1
    -- Transport `(U', 𝒞')` back along `L` to `x₀`.
    refine ⟨L '' U', ?_, ⟨y₀, hy₀U', hLy₀⟩, (image L) '' 𝒞', h𝒞'.image_continuousLinearEquiv L,
      ?_⟩
    · rintro _ ⟨y, hy, rfl⟩
      exact (hV₀_sub (L y) (hU'_V₀ y hy)).1
    · rintro i _ ⟨E, hE, rfl⟩
      rw [signInvariant_image]
      by_cases hi0 : f i =ᶠ[𝓝 x₀] 0
      · refine (signInvariant_const (0 : ℝ)).congr fun y hy ↦ ?_
        exact ((hV₀_sub (L y) (hU'_V₀ y (h𝒞'.subset_of_mem hE hy))).2 ⟨i, hi0⟩).symm
      · let i' : ι' := ⟨i, hi0⟩
        have hu_inv : SignInvariant (fun y : Fin (n + 1) → ℝ ↦ u i' (Fin.tail y, y 0)) E := by
          rw [signInvariant_iff_exists]
          refine ⟨SignType.sign (u i' (b₀, t₀)), fun y hy ↦ ?_⟩
          exact (hW_prod (hU'_box y (h𝒞'.subset_of_mem hE hy))).2.2 i'
        refine ((hsign_P (.inl i') E hE).mul hu_inv).congr fun y hy ↦ ?_
        have hbox_y := (hW_prod (hU'_box y (h𝒞'.subset_of_mem hE hy))).2.1 i'
        simpa only [g, he_prod_apply, Fin.cons_self_tail, P_ext, eval_comp, eval_sub, eval_X,
          eval_C, Function.comp_apply] using hbox_y.symm

/-- **Local normal-decomposition theorem for real analytic germs.** Given a finite family `f` of
functions real analytic at `x₀ ∈ ℝ ^ n` and a neighbourhood `V ∈ 𝓝 x₀`, there exist an open
neighbourhood `U ⊆ V` of `x₀` and a normal decomposition `𝒞` of `U` on each stratum of which every
`f i` is sign-invariant. -/
theorem exists_isNormalDecomposition_signInvariant {n : ℕ} {ι : Type*} [Finite ι]
    {f : ι → (Fin n → ℝ) → ℝ} {x₀ : Fin n → ℝ} (hf : ∀ i, AnalyticAt ℝ (f i) x₀)
    {V : Set (Fin n → ℝ)} (hV : V ∈ 𝓝 x₀) :
    ∃ U ⊆ V, x₀ ∈ U ∧ ∃ 𝒞 : Set (Set (Fin n → ℝ)),
      IsNormalDecomposition U 𝒞 ∧ ∀ i, ∀ S ∈ 𝒞, SignInvariant (f i) S := by
  obtain ⟨m, ⟨e⟩⟩ := Finite.exists_equiv_fin ι
  obtain ⟨U, hUV, hx₀U, 𝒞, h𝒞, hsign⟩ := exists_isNormalDecomposition_signInvariant_fin
    (f := fun j ↦ f (e.symm j)) (fun j ↦ hf (e.symm j)) hV
  exact ⟨U, hUV, hx₀U, 𝒞, h𝒞, fun i S hS ↦ by
    simpa only [e.symm_apply_apply] using hsign (e i) S hS⟩

/-- **Local normal-decomposition theorem for semianalytic set germs.** Given a finite family `s` of
subsets of `ℝ ^ n` semianalytic at `x₀` and a neighbourhood `V ∈ 𝓝 x₀`, there exist an open
neighbourhood `U ⊆ V` of `x₀` and a normal decomposition `𝒞` of `U` compatible with every `s k`
(every stratum of `𝒞` is either contained in `s k` or disjoint from `s k`). -/
theorem exists_isNormalDecomposition_subset_or_disjoint {n : ℕ} {κ : Type*} [Finite κ]
    {s : κ → Set (Fin n → ℝ)} {x₀ : Fin n → ℝ} (hs : ∀ k, SemianalyticAt (s k) x₀)
    {V : Set (Fin n → ℝ)} (hV : V ∈ 𝓝 x₀) :
    ∃ U ⊆ V, x₀ ∈ U ∧ ∃ 𝒞 : Set (Set (Fin n → ℝ)),
      IsNormalDecomposition U 𝒞 ∧ ∀ k, ∀ S ∈ 𝒞, S ⊆ s k ∨ Disjoint S (s k) := by
  classical
  cases nonempty_fintype κ
  choose W hW t ht hst using fun k ↦ semianalyticAt_def.1 (hs k)
  choose m f hf Φ ht_eq using fun k ↦ (ht k).exists_eq_setOf_sign
  let V' := V ∩ ⋂ k : κ, W k
  have hV' : V' ∈ 𝓝 x₀ := inter_mem hV (iInter_mem.2 hW)
  obtain ⟨U, hUV', hx₀U, 𝒞, h𝒞, hsign⟩ := exists_isNormalDecomposition_signInvariant
    (f := fun (p : Σ k : κ, Fin (m k)) ↦ f p.1 p.2)
    (fun p ↦ hf p.1 p.2 x₀ (mem_of_mem_nhds (hW p.1))) hV'
  refine ⟨U, hUV'.trans inter_subset_left, hx₀U, 𝒞, h𝒞, fun k S hS ↦ ?_⟩
  have hSW : S ⊆ W k := (h𝒞.subset_of_mem hS).trans
    (hUV'.trans (inter_subset_right.trans (iInter_subset W k)))
  have hmem_iff (x : Fin n → ℝ) (hx : x ∈ S) : x ∈ s k ↔ x ∈ t k := by
    have h := Set.ext_iff.1 (hst k) x
    simpa only [mem_inter_iff, hSW hx, and_true] using h
  have hdic := subset_or_disjoint_setOf_sign (fun j ↦ hsign ⟨k, j⟩ S hS) (Φ k)
  rw [← ht_eq k] at hdic
  rcases hdic with hsub | hdisj
  · exact Or.inl fun x hx ↦ (hmem_iff x hx).2 (hsub hx)
  · exact Or.inr (disjoint_left.2 fun x hx hxs ↦ disjoint_left.1 hdisj hx ((hmem_iff x hx).1 hxs))

/-- Single-set form of `exists_isNormalDecomposition_subset_or_disjoint`: a set semianalytic at
`x₀` admits a compatible local normal decomposition inside any neighbourhood `V ∈ 𝓝 x₀`. -/
theorem SemianalyticAt.exists_isNormalDecomposition {n : ℕ} {s V : Set (Fin n → ℝ)}
    {x₀ : Fin n → ℝ} (hs : SemianalyticAt s x₀) (hV : V ∈ 𝓝 x₀) :
    ∃ U ⊆ V, x₀ ∈ U ∧ ∃ 𝒞 : Set (Set (Fin n → ℝ)),
      IsNormalDecomposition U 𝒞 ∧ ∀ S ∈ 𝒞, S ⊆ s ∨ Disjoint S s := by
  obtain ⟨U, hUV, hx₀U, 𝒞, h𝒞, hcompat⟩ :=
    exists_isNormalDecomposition_subset_or_disjoint (fun _ : Unit ↦ hs) hV
  exact ⟨U, hUV, hx₀U, 𝒞, h𝒞, hcompat ()⟩

/-- A subset `s ⊆ ℝ ^ n` is semianalytic at `x₀` if and only if `x₀` admits a local normal
decomposition `(U, 𝒞)` compatible with `s`. -/
theorem semianalyticAt_iff_exists_isNormalDecomposition {n : ℕ} {s : Set (Fin n → ℝ)}
    {x₀ : Fin n → ℝ} :
    SemianalyticAt s x₀ ↔
      ∃ U, x₀ ∈ U ∧ ∃ 𝒞 : Set (Set (Fin n → ℝ)),
        IsNormalDecomposition U 𝒞 ∧ ∀ S ∈ 𝒞, S ⊆ s ∨ Disjoint S s := by
  refine ⟨fun hs ↦ ?_, fun ⟨U, hx₀U, 𝒞, h𝒞, hcompat⟩ ↦ ?_⟩
  · obtain ⟨U, -, hx₀U, 𝒞, h𝒞, hcompat⟩ := hs.exists_isNormalDecomposition univ_mem
    exact ⟨U, hx₀U, 𝒞, h𝒞, hcompat⟩
  · refine ((h𝒞.isSemianalytic_inter hcompat).semianalyticAt x₀).congr ?_
    filter_upwards [h𝒞.isOpen_domain.mem_nhds hx₀U] with y hy
    simp [hy]

end TauCeti
