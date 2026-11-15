/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Setoid.Partition
public import TauCeti.Analysis.Analytic.Submanifold.Basic
public import TauCeti.Geometry.RealAnalytic.Semianalytic.Basic
public import TauCeti.Topology.ClusterSet

import Mathlib.Analysis.Convex.Basic
import TauCeti.Analysis.Analytic.Submanifold.Dimension
import TauCeti.Analysis.Analytic.Submanifold.Transport
import TauCeti.Analysis.Convex.ClusterSet

/-!
# Normal decompositions into semianalytic submanifolds

A *normal decomposition* of a subset `U ⊆ ℝⁿ` (`TauCeti.IsNormalDecomposition U 𝒞`) is a finite
partition `𝒞` of `U` into connected, semianalytic real analytic submanifolds, each having
preconnected approach regions at every ambient point (`TauCeti.IsPreconnectedApproachAt`),
satisfying Łojasiewicz's frontier condition:

* **Incidence:** if `S, T ∈ 𝒞` and `(S ∩ closure T).Nonempty`, then `S ⊆ closure T`.
* **Dimension drop:** if `S, T ∈ 𝒞`, `S ⊆ closure T`, and `S ≠ T`, then `dim S < dim T`.

Every piece is locally closed (`TauCeti.IsNormalDecomposition.isLocallyClosed`) because it is an
analytic submanifold. Inside `U`, the closure and strict frontier of each piece are unions of
pieces (`TauCeti.IsNormalDecomposition.inter_closure_eq_sUnion`,
`TauCeti.IsNormalDecomposition.inter_closure_sdiff_eq_sUnion`). When `U` is open and a set `s` is
compatible with `𝒞` (`∀ S ∈ 𝒞, S ⊆ s ∨ Disjoint S s`), both `U ∩ closure s` and
`U ∩ (closure s \ s)` are likewise unions of pieces of `𝒞`, with every piece of
`U ∩ (closure s \ s)` having strictly smaller dimension than some piece contained in `s`.

Normal decompositions are invariant under continuous linear equivalences of the ambient coordinate
space (`TauCeti.IsNormalDecomposition.image_continuousLinearEquiv`,
`TauCeti.IsNormalDecomposition.preimage_continuousLinearEquiv`), allowing local existence proofs to
place a finite analytic family in general position before applying Weierstrass preparation.

## Main declarations

* `TauCeti.IsNormalDecomposition`: finite connected semianalytic submanifold partition with
  preconnected approach regions and the two-part frontier condition.
* `TauCeti.IsNormalDecomposition.inter_closure_eq_sUnion`,
  `TauCeti.IsNormalDecomposition.inter_closure_sdiff_eq_sUnion`: closure and strict frontier of a
  piece inside `U` are unions of pieces.
* `TauCeti.IsNormalDecomposition.inter_closure_eq_sUnion_of_isOpen`,
  `TauCeti.IsNormalDecomposition.inter_closure_sdiff_eq_sUnion_of_isOpen`: closure and
  `closure s \ s` inside an open `U` for any set `s` compatible with `𝒞`.
* `TauCeti.isNormalDecomposition_empty`, `TauCeti.isNormalDecomposition_singleton_univ`: base
  decompositions of `∅` and `ℝ⁰`.
* `TauCeti.IsNormalDecomposition.image_continuousLinearEquiv`,
  `TauCeti.IsNormalDecomposition.preimage_continuousLinearEquiv`: invariance under continuous linear
  equivalences.

## References

* S. Łojasiewicz, *Ensembles semi-analytiques*, IHÉS lecture notes, 1965, §16–18.
* S. Łojasiewicz, *Triangulation of semi-analytic sets*, Annali della Scuola Normale Superiore di
  Pisa (3) 18 (1964), 449–474, §1.
* E. Bierstone and P. D. Milman, *Semianalytic and subanalytic sets*, Publications Mathématiques de
  l'IHÉS 67 (1988), 5–42, §2.
-/

public section

open Filter Function Set Topology

namespace TauCeti

/-- A *normal decomposition* of `U ⊆ ℝⁿ` is a finite partition `𝒞` of `U` into connected,
semianalytic real analytic submanifolds with preconnected approach regions at every ambient point,
satisfying both parts of the frontier condition: if a piece `S` meets `closure T` then
`S ⊆ closure T`, and if moreover `S ≠ T` then `dim S < dim T`. -/
structure IsNormalDecomposition {n : ℕ} (U : Set (Fin n → ℝ))
    (𝒞 : Set (Set (Fin n → ℝ))) : Prop where
  /-- The decomposition has finitely many pieces. -/
  finite : 𝒞.Finite
  /-- The pieces cover `U`. -/
  sUnion_eq : ⋃₀ 𝒞 = U
  /-- Distinct pieces are disjoint. -/
  pairwiseDisjoint : 𝒞.PairwiseDisjoint id
  /-- Every piece is connected, hence nonempty. -/
  isConnected : ∀ {S}, S ∈ 𝒞 → IsConnected S
  /-- Every piece is semianalytic in the ambient space `ℝⁿ`. -/
  isSemianalytic : ∀ {S}, S ∈ 𝒞 → IsSemianalytic S
  /-- Every piece is a real analytic submanifold of some dimension. -/
  exists_isAnalyticSubmanifold : ∀ {S}, S ∈ 𝒞 → ∃ d, IsAnalyticSubmanifold d S
  /-- Every piece has preconnected approach regions at every point of `ℝⁿ`, including its frontier
  points. -/
  isPreconnectedApproachAt : ∀ {S}, S ∈ 𝒞 → ∀ x, IsPreconnectedApproachAt S x
  /-- **Frontier condition (containment).** A piece meeting the closure of another piece is
  contained in that closure. -/
  subset_closure_of_nonempty_inter :
    ∀ {S}, S ∈ 𝒞 → ∀ {T}, T ∈ 𝒞 → (S ∩ closure T).Nonempty → S ⊆ closure T
  /-- **Frontier condition (dimension drop).** A piece strictly contained in the closure of another
  piece has strictly smaller submanifold dimension. -/
  dim_lt_of_subset_closure :
    ∀ {S}, S ∈ 𝒞 → ∀ {T}, T ∈ 𝒞 → S ⊆ closure T → S ≠ T →
      ∀ {dS dT}, IsAnalyticSubmanifold dS S → IsAnalyticSubmanifold dT T → dS < dT

namespace IsNormalDecomposition

variable {n n' : ℕ} {U : Set (Fin n → ℝ)} {𝒞 : Set (Set (Fin n → ℝ))}
  {S T : Set (Fin n → ℝ)} {dS dT : ℕ}

/-- Every piece of a normal decomposition of `U` is contained in `U`. -/
theorem subset_of_mem (h : IsNormalDecomposition U 𝒞) (hS : S ∈ 𝒞) : S ⊆ U :=
  h.sUnion_eq ▸ subset_sUnion_of_mem hS

/-- Every point of `U` belongs to some piece of the decomposition. -/
theorem exists_mem_of_mem (h : IsNormalDecomposition U 𝒞) {x : Fin n → ℝ} (hx : x ∈ U) :
    ∃ S ∈ 𝒞, x ∈ S :=
  mem_sUnion.1 (h.sUnion_eq.symm ▸ hx)

/-- Every piece of a normal decomposition is nonempty. -/
theorem nonempty_of_mem (h : IsNormalDecomposition U 𝒞) (hS : S ∈ 𝒞) : S.Nonempty :=
  (h.isConnected hS).nonempty

/-- The empty set is never a piece of a normal decomposition. -/
theorem empty_notMem (h : IsNormalDecomposition U 𝒞) : ∅ ∉ 𝒞 :=
  fun h0 ↦ not_nonempty_empty (h.nonempty_of_mem h0)

/-- Every piece of a normal decomposition is preconnected. -/
theorem isPreconnected (h : IsNormalDecomposition U 𝒞) (hS : S ∈ 𝒞) : IsPreconnected S :=
  (h.isConnected hS).isPreconnected

/-- Every piece of a normal decomposition is locally closed in `ℝⁿ`. -/
theorem isLocallyClosed (h : IsNormalDecomposition U 𝒞) (hS : S ∈ 𝒞) : IsLocallyClosed S :=
  let ⟨_, hd⟩ := h.exists_isAnalyticSubmanifold hS
  hd.isLocallyClosed

/-- Two pieces of a normal decomposition containing a common point are equal. -/
theorem eq_of_mem_of_mem (h : IsNormalDecomposition U 𝒞) (hS : S ∈ 𝒞) (hT : T ∈ 𝒞)
    {x : Fin n → ℝ} (hxS : x ∈ S) (hxT : x ∈ T) : S = T :=
  h.pairwiseDisjoint.elim hS hT (not_disjoint_iff.2 ⟨x, hxS, hxT⟩)

/-- Two pieces of a normal decomposition with nonempty intersection are equal. -/
theorem eq_of_nonempty_inter (h : IsNormalDecomposition U 𝒞) (hS : S ∈ 𝒞) (hT : T ∈ 𝒞)
    (hne : (S ∩ T).Nonempty) : S = T :=
  let ⟨_, hxS, hxT⟩ := hne
  h.eq_of_mem_of_mem hS hT hxS hxT

/-- Pulling back the pieces of a normal decomposition of `U` to the subtype `U` gives a partition
of `U`. -/
theorem isPartition_preimage (h : IsNormalDecomposition U 𝒞) :
    Setoid.IsPartition ((fun S ↦ (Subtype.val : U → Fin n → ℝ) ⁻¹' S) '' 𝒞) := by
  refine PairwiseDisjoint.isPartition_of_exists_of_ne_empty ?_ (fun x ↦ ?_) ?_
  · rintro _ ⟨S, hS, rfl⟩ _ ⟨T, hT, rfl⟩ hne
    exact (h.pairwiseDisjoint hS hT (fun hST ↦ hne (hST ▸ rfl))).preimage _
  · obtain ⟨S, hS, hxS⟩ := h.exists_mem_of_mem x.2
    exact ⟨_, mem_image_of_mem _ hS, hxS⟩
  · rintro ⟨S, hS, h0⟩
    obtain ⟨x, hxS⟩ := h.nonempty_of_mem hS
    exact notMem_empty (⟨x, h.subset_of_mem hS hxS⟩ : U) (h0 ▸ hxS)

/-- A distinct piece meeting the closure of another piece has strictly smaller dimension. -/
theorem dim_lt_of_nonempty_inter_closure (h : IsNormalDecomposition U 𝒞) (hS : S ∈ 𝒞) (hT : T ∈ 𝒞)
    (hne : (S ∩ closure T).Nonempty) (hne_set : S ≠ T)
    (hdS : IsAnalyticSubmanifold dS S) (hdT : IsAnalyticSubmanifold dT T) : dS < dT :=
  h.dim_lt_of_subset_closure hS hT (h.subset_closure_of_nonempty_inter hS hT hne) hne_set hdS hdT

/-- Mutual closure containment between pieces forces equality: strict frontier incidence is
asymmetric. -/
theorem eq_of_subset_closure_of_subset_closure (h : IsNormalDecomposition U 𝒞)
    (hS : S ∈ 𝒞) (hT : T ∈ 𝒞) (hST : S ⊆ closure T) (hTS : T ⊆ closure S) : S = T := by
  by_contra hne
  obtain ⟨dS, hdS⟩ := h.exists_isAnalyticSubmanifold hS
  obtain ⟨dT, hdT⟩ := h.exists_isAnalyticSubmanifold hT
  exact lt_asymm (h.dim_lt_of_subset_closure hS hT hST hne hdS hdT)
    (h.dim_lt_of_subset_closure hT hS hTS (Ne.symm hne) hdT hdS)

/-- Inside `U`, the closure of a piece `T` is the union of the pieces contained in `closure T`. -/
theorem inter_closure_eq_sUnion (h : IsNormalDecomposition U 𝒞) (hT : T ∈ 𝒞) :
    U ∩ closure T = ⋃₀ {S ∈ 𝒞 | S ⊆ closure T} := by
  refine Subset.antisymm (fun x ⟨hxU, hxcl⟩ ↦ ?_) (sUnion_subset fun S ⟨hS, hST⟩ ↦
    subset_inter (h.subset_of_mem hS) hST)
  obtain ⟨S, hS, hxS⟩ := h.exists_mem_of_mem hxU
  exact mem_sUnion.2 ⟨S, ⟨hS, h.subset_closure_of_nonempty_inter hS hT ⟨x, hxS, hxcl⟩⟩, hxS⟩

/-- Inside `U`, `closure T \ T` is the union of the pieces strictly contained in `closure T`, each
of which has dimension strictly smaller than `dim T`. -/
theorem inter_closure_sdiff_eq_sUnion (h : IsNormalDecomposition U 𝒞) (hT : T ∈ 𝒞) :
    U ∩ (closure T \ T) = ⋃₀ {S ∈ 𝒞 | S ⊆ closure T ∧ S ≠ T} := by
  refine Subset.antisymm (fun x ⟨hxU, hxcl, hxT⟩ ↦ ?_) (sUnion_subset fun S ⟨hS, hST, hne⟩ ↦ ?_)
  · obtain ⟨S, hS, hxS⟩ := h.exists_mem_of_mem hxU
    refine mem_sUnion.2 ⟨S, ⟨hS, h.subset_closure_of_nonempty_inter hS hT ⟨x, hxS, hxcl⟩,
      ?_⟩, hxS⟩
    rintro rfl
    exact hxT hxS
  · refine fun x hxS ↦ ⟨h.subset_of_mem hS hxS, hST hxS, fun hxT ↦ hne ?_⟩
    exact h.eq_of_mem_of_mem hS hT hxS hxT

/-- If a set `s` is compatible with a normal decomposition `𝒞` of `U` (each piece lies in `s` or
misses `s`), then `s ∩ U` is the union of the pieces contained in `s`. -/
theorem inter_eq_sUnion_sep (h : IsNormalDecomposition U 𝒞) {s : Set (Fin n → ℝ)}
    (hs : ∀ S ∈ 𝒞, S ⊆ s ∨ Disjoint S s) :
    s ∩ U = ⋃₀ {S ∈ 𝒞 | S ⊆ s} := by
  refine Subset.antisymm (fun x ⟨hxs, hxU⟩ ↦ ?_) (sUnion_subset fun S ⟨hS, hSs⟩ ↦
    subset_inter hSs (h.subset_of_mem hS))
  obtain ⟨S, hS, hxS⟩ := h.exists_mem_of_mem hxU
  refine mem_sUnion.2 ⟨S, ⟨hS, (hs S hS).resolve_right ?_⟩, hxS⟩
  exact not_disjoint_iff.2 ⟨x, hxS, hxs⟩

/-- If `U` is open and `s` is compatible with `𝒞`, then `U ∩ closure s` is the union of the pieces
of `𝒞` contained in the closure of some piece of `𝒞` lying in `s`. -/
theorem inter_closure_eq_sUnion_of_isOpen (h : IsNormalDecomposition U 𝒞) (hU : IsOpen U)
    {s : Set (Fin n → ℝ)} (hs : ∀ S ∈ 𝒞, S ⊆ s ∨ Disjoint S s) :
    U ∩ closure s = ⋃₀ {S ∈ 𝒞 | ∃ T ∈ 𝒞, T ⊆ s ∧ S ⊆ closure T} := by
  have hcl_open : U ∩ closure s = U ∩ closure (s ∩ U) := by
    refine Subset.antisymm (fun x ⟨hxU, hxcl⟩ ↦ ⟨hxU, ?_⟩)
      (inter_subset_inter_right U (closure_mono inter_subset_left))
    rw [inter_comm s U]
    exact hU.inter_closure ⟨hxU, hxcl⟩
  rw [hcl_open, h.inter_eq_sUnion_sep hs,
    (h.finite.subset (sep_subset _ _)).closure_sUnion, inter_iUnion₂]
  ext x
  simp only [mem_iUnion, exists_prop, mem_sUnion, mem_sep_iff]
  constructor
  · rintro ⟨T, ⟨hT, hTs⟩, hx⟩
    obtain ⟨S, ⟨hS, hST⟩, hxS⟩ := mem_sUnion.1 ((h.inter_closure_eq_sUnion hT) ▸ hx)
    exact ⟨S, ⟨hS, T, hT, hTs, hST⟩, hxS⟩
  · rintro ⟨S, ⟨hS, T, hT, hTs, hST⟩, hxS⟩
    exact ⟨T, ⟨hT, hTs⟩, h.subset_of_mem hS hxS, hST hxS⟩

/-- If `U` is open and `s` is compatible with `𝒞`, then `U ∩ (closure s \ s)` is the union of the
pieces of `𝒞` disjoint from `s` that lie in the closure of some piece of `𝒞` contained in `s`.
Every such piece is distinct from its witness `T ⊆ s`, hence has strictly smaller dimension. -/
theorem inter_closure_sdiff_eq_sUnion_of_isOpen (h : IsNormalDecomposition U 𝒞) (hU : IsOpen U)
    {s : Set (Fin n → ℝ)} (hs : ∀ S ∈ 𝒞, S ⊆ s ∨ Disjoint S s) :
    U ∩ (closure s \ s) =
      ⋃₀ {S ∈ 𝒞 | Disjoint S s ∧ ∃ T ∈ 𝒞, T ⊆ s ∧ S ⊆ closure T} := by
  have heq : U ∩ (closure s \ s) = (U ∩ closure s) \ s := by
    ext x
    simp only [mem_inter_iff, Set.mem_sdiff]
    tauto
  rw [heq, h.inter_closure_eq_sUnion_of_isOpen hU hs]
  ext x
  simp only [Set.mem_sdiff, mem_sUnion, mem_sep_iff]
  constructor
  · rintro ⟨⟨S, ⟨hS, T, hT, hTs, hST⟩, hxS⟩, hxs⟩
    have hdisj : Disjoint S s := (hs S hS).resolve_left fun hSs ↦ hxs (hSs hxS)
    exact ⟨S, ⟨hS, hdisj, T, hT, hTs, hST⟩, hxS⟩
  · rintro ⟨S, ⟨hS, hdisj, T, hT, hTs, hST⟩, hxS⟩
    exact ⟨⟨S, ⟨hS, T, hT, hTs, hST⟩, hxS⟩, disjoint_left.1 hdisj hxS⟩

end IsNormalDecomposition

/-! ### Base decompositions -/

/-- The empty collection is a normal decomposition of the empty set in any ambient dimension. -/
theorem isNormalDecomposition_empty {n : ℕ} :
    IsNormalDecomposition (∅ : Set (Fin n → ℝ)) ∅ where
  finite := finite_empty
  sUnion_eq := sUnion_empty
  pairwiseDisjoint := pairwiseDisjoint_empty
  isConnected h := False.elim h
  isSemianalytic h := False.elim h
  exists_isAnalyticSubmanifold h := False.elim h
  isPreconnectedApproachAt h := False.elim h
  subset_closure_of_nonempty_inter h := False.elim h
  dim_lt_of_subset_closure h := False.elim h

/-- A normal decomposition of the empty set must be the empty collection. -/
@[simp]
theorem isNormalDecomposition_empty_iff {n : ℕ} {𝒞 : Set (Set (Fin n → ℝ))} :
    IsNormalDecomposition ∅ 𝒞 ↔ 𝒞 = ∅ := by
  refine ⟨fun h ↦ eq_empty_iff_forall_notMem.2 fun S hS ↦ ?_,
    fun h ↦ h ▸ isNormalDecomposition_empty⟩
  obtain ⟨x, hx⟩ := h.nonempty_of_mem hS
  exact notMem_empty x (h.subset_of_mem hS hx)

/-- In dimension zero, `{univ}` is a normal decomposition of `univ : Set (Fin 0 → ℝ)`. -/
theorem isNormalDecomposition_singleton_univ :
    IsNormalDecomposition (univ : Set (Fin 0 → ℝ)) {univ} where
  finite := finite_singleton univ
  sUnion_eq := sUnion_singleton univ
  pairwiseDisjoint := pairwiseDisjoint_singleton univ id
  isConnected := by
    rintro _ rfl
    exact isConnected_univ
  isSemianalytic := by
    rintro _ rfl
    exact isSemianalytic_univ
  exists_isAnalyticSubmanifold := by
    rintro _ rfl
    exact ⟨0, isOpen_univ.isAnalyticSubmanifold univ_nonempty⟩
  isPreconnectedApproachAt := by
    rintro _ rfl x
    exact convex_univ.isPreconnectedApproachAt x
  subset_closure_of_nonempty_inter := by
    rintro _ rfl _ rfl _
    exact subset_closure
  dim_lt_of_subset_closure := by
    rintro _ rfl _ rfl _ hne
    exact False.elim (hne rfl)

/-! ### Transport along continuous linear equivalences -/

namespace IsNormalDecomposition

variable {n n' : ℕ} {U : Set (Fin n → ℝ)} {𝒞 : Set (Set (Fin n → ℝ))}

/-- Mapping every piece of a normal decomposition by a continuous linear equivalence gives a normal
decomposition of the image. -/
theorem image_continuousLinearEquiv (h : IsNormalDecomposition U 𝒞)
    (e : (Fin n → ℝ) ≃L[ℝ] Fin n' → ℝ) :
    IsNormalDecomposition (e '' U) (image e '' 𝒞) := by
  have hcl (A : Set (Fin n → ℝ)) : closure (e '' A) = e '' closure A :=
    (e.toHomeomorph.image_closure A).symm
  refine
    { finite := h.finite.image _
      sUnion_eq := by
        ext y
        simp only [sUnion_image, mem_iUnion, mem_image, ← h.sUnion_eq, mem_sUnion]
        exact ⟨fun ⟨S, hS, x, hxS, hxy⟩ ↦ ⟨x, ⟨S, hS, hxS⟩, hxy⟩,
          fun ⟨x, ⟨S, hS, hxS⟩, hxy⟩ ↦ ⟨S, hS, x, hxS, hxy⟩⟩
      pairwiseDisjoint := ?_
      isConnected := ?_
      isSemianalytic := ?_
      exists_isAnalyticSubmanifold := ?_
      isPreconnectedApproachAt := ?_
      subset_closure_of_nonempty_inter := ?_
      dim_lt_of_subset_closure := ?_ }
  · rintro _ ⟨S, hS, rfl⟩ _ ⟨T, hT, rfl⟩ hne
    exact disjoint_image_of_injective e.injective
      (h.pairwiseDisjoint hS hT fun hST ↦ hne (hST ▸ rfl))
  · rintro _ ⟨S, hS, rfl⟩
    exact (h.isConnected hS).image e e.continuous.continuousOn
  · rintro _ ⟨S, hS, rfl⟩
    exact (e.toEquiv.isSemianalytic_image_iff (fun x _ ↦ e.analyticAt x)
      (fun y _ ↦ e.symm.analyticAt y)).2 (h.isSemianalytic hS)
  · rintro _ ⟨S, hS, rfl⟩
    obtain ⟨d, hd⟩ := h.exists_isAnalyticSubmanifold hS
    exact ⟨d, hd.image_continuousLinearEquiv e⟩
  · rintro _ ⟨S, hS, rfl⟩ y
    have happ := (h.isPreconnectedApproachAt hS (e.symm y)).image
      e.continuous.continuousAt e.continuous.continuousOn
      e.symm.continuous.continuousAt (e.symm_apply_apply _) (fun x _ ↦ e.symm_apply_apply x)
    rwa [e.apply_symm_apply] at happ
  · rintro _ ⟨S, hS, rfl⟩ _ ⟨T, hT, rfl⟩ ⟨_, ⟨x, hxS, rfl⟩, hycl⟩
    rw [hcl] at hycl ⊢
    obtain ⟨x', hx'cl, hxx'⟩ := hycl
    exact image_mono (h.subset_closure_of_nonempty_inter hS hT ⟨x', e.injective hxx' ▸ hxS, hx'cl⟩)
  · rintro _ ⟨S, hS, rfl⟩ _ ⟨T, hT, rfl⟩ hsub hne _ _ hdS hdT
    rw [hcl, image_subset_image_iff e.injective] at hsub
    rw [isAnalyticSubmanifold_image_continuousLinearEquiv_iff] at hdS hdT
    exact h.dim_lt_of_subset_closure hS hT hsub (fun hST ↦ hne (hST ▸ rfl)) hdS hdT

/-- Pulling back every piece of a normal decomposition along a continuous linear equivalence gives a
normal decomposition of the preimage. -/
theorem preimage_continuousLinearEquiv {U : Set (Fin n' → ℝ)} {𝒞 : Set (Set (Fin n' → ℝ))}
    (h : IsNormalDecomposition U 𝒞) (e : (Fin n → ℝ) ≃L[ℝ] Fin n' → ℝ) :
    IsNormalDecomposition (e ⁻¹' U) (preimage e '' 𝒞) := by
  have hpre (A : Set (Fin n' → ℝ)) : e ⁻¹' A = e.symm '' A :=
    (e.symm.image_eq_preimage_symm A).symm
  rw [hpre U, show preimage (e : (Fin n → ℝ) → Fin n' → ℝ) = image e.symm from funext hpre]
  exact h.image_continuousLinearEquiv e.symm

end IsNormalDecomposition

end TauCeti
