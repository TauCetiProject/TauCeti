/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Dimension.Covering
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.ShrinkingLemma
public import Mathlib.Topology.UrysohnsLemma

/-!
# Covering dimension from extension of maps into spheres

This file proves the half of the sphere-extension characterization of covering dimension that
bounds the dimension: if `X` is a compact space and every continuous map from a closed subset of
`X` to the unit sphere `Sᵈ` of a real normed space of dimension `d + 1` extends to `X`, then `X`
has covering dimension at most `d`. The obstruction to extending such maps is how lower bounds on
the stable range of rings of continuous functions turn into upper bounds on the covering dimension
(Vaserstein).

The route goes through Hemmingsen's characterization, which is proved here in both directions for
compact spaces: `X` has covering dimension at most `d` exactly when every open cover of `X` by
`d + 2` sets has an open shrinking with empty intersection. Shrinking a finite cover once for each
of its `(d + 2)`-element sets of indices produces a refinement of order at most `d + 1`.

To obtain such shrinkings from the extension property, take a closed shrinking `F` of a cover
`U₀, …, U_{d+1}` and Urysohn functions separating `Fᵢ` from the complement of `Uᵢ` for `i ≤ d`.
They define a map into `ℝᵈ⁺¹`, nonvanishing on the closed set where one of them is `0` or `1`.
Normalized and extended to a map `g : X → Sᵈ`, its coordinates `gᵢ` are negative on `Fᵢ` and
positive off `Uᵢ`, and they have no common zero. The sets `{gᵢ < 0}` for `i ≤ d`, together with
the part of `U_{d+1}` where some `gᵢ` is positive, form the required shrinking. The extension
property also makes `X` normal, which the closed shrinking and the Urysohn functions use.

## Main results

* `TauCeti.HasCoveringDimensionLE.exists_shrinking_iInter_eq_empty` and
  `TauCeti.hasCoveringDimensionLE_iff_forall_exists_shrinking_iInter_eq_empty`: Hemmingsen's
  characterization of covering dimension at most `d` by open covers with `d + 2` members.
* `TauCeti.hasCoveringDimensionLE_of_forall_exists_extension_sphere`: if every map from a closed
  subset to the unit sphere of a real normed space of dimension `d + 1` extends, then the
  covering dimension is at most `d`.

## References

* R. Engelking, *Dimension Theory*, North-Holland, 1978, §3.2 (Hemmingsen's characterization by
  covers with `n + 2` members, the theorem on partitions, and Theorem 3.2.10 on extension of
  maps into `Sⁿ`).
* E. Hemmingsen, *Some theorems in dimension theory for normal Hausdorff spaces*, Duke Math. J.
  13 (1946), 495–504.
* L. N. Vaserstein, *Stable rank of rings and dimensionality of topological spaces*, Funct. Anal.
  Appl. 5 (1971), 102–110.
-/

public section

open Set Topology Module Metric

namespace TauCeti

variable {X : Type*} [TopologicalSpace X]

/-! ### Hemmingsen's characterization -/

/-- In a space of covering dimension at most `d`, every open cover by `d + 2` sets has an open
shrinking with empty intersection. -/
theorem HasCoveringDimensionLE.exists_shrinking_iInter_eq_empty {d : ℕ}
    (h : HasCoveringDimensionLE X d) {U : Fin (d + 2) → Set X} (hUo : ∀ i, IsOpen (U i))
    (hU : ⋃ i, U i = univ) :
    ∃ V : Fin (d + 2) → Set X, (∀ i, IsOpen (V i)) ∧ (∀ i, V i ⊆ U i) ∧ ⋃ i, V i = univ ∧
      ⋂ i, V i = ∅ := by
  -- A shrinking of order at most `d + 1` has no point in all `d + 2` of its members.
  obtain ⟨V, hVo, hVU, hVc, hVm⟩ := h.exists_shrinking hUo hU
  refine ⟨V, hVo, hVU, hVc, eq_empty_of_forall_notMem fun x hx ↦ ?_⟩
  have hall : {i | x ∈ V i} = univ := eq_univ_of_forall (mem_iInter.1 hx)
  have := hVm x
  rw [hall, encard_univ, ENat.card_eq_coe_fintype_card, Fintype.card_fin, Nat.cast_le] at this
  omega

/-- The hypothesis of Hemmingsen's characterization: every open cover of `X` by `d + 2` sets has
an open shrinking with empty intersection. -/
private abbrev ShrinkingCondition (X : Type*) [TopologicalSpace X] (d : ℕ) : Prop :=
  ∀ U : Fin (d + 2) → Set X, (∀ i, IsOpen (U i)) → ⋃ i, U i = univ →
    ∃ V : Fin (d + 2) → Set X, (∀ i, IsOpen (V i)) ∧ (∀ i, V i ⊆ U i) ∧ ⋃ i, V i = univ ∧
      ⋂ i, V i = ∅

/-- One shrinking step: under Hemmingsen's condition, an open cover indexed by any type has an
open shrinking whose members indexed by a given set `S` of `d + 2` indices have empty
intersection. -/
private theorem exists_shrinking_biInter_eq_empty {d : ℕ} (h : ShrinkingCondition X d)
    {ι : Type*} {U : ι → Set X} (hUo : ∀ i, IsOpen (U i)) (hU : ⋃ i, U i = univ)
    {S : Finset ι} (hS : S.card = d + 2) :
    ∃ V : ι → Set X, (∀ i, IsOpen (V i)) ∧ (∀ i, V i ⊆ U i) ∧ ⋃ i, V i = univ ∧
      ⋂ i ∈ S, V i = ∅ := by
  classical
  -- Enlarge each `U i`, `i ∈ S`, by the union `W` of the members outside `S`, shrink the
  -- resulting cover by `d + 2` sets, and intersect back with `U i`.
  let e : Fin (d + 2) ≃ S := (S.equivFin.trans (finCongr hS)).symm
  let W := ⋃ (j) (_ : j ∉ S), U j
  have hWo : IsOpen W := isOpen_iUnion fun j ↦ isOpen_iUnion fun _ ↦ hUo j
  obtain ⟨V', hV'o, hV'O, hV'c, hV'e⟩ := h (fun k ↦ U (e k) ∪ W)
    (fun k ↦ (hUo _).union hWo) (eq_univ_of_forall fun x ↦ by
      obtain ⟨j, hj⟩ := mem_iUnion.1 (hU ▸ mem_univ x)
      by_cases hjS : j ∈ S
      · exact mem_iUnion.2 ⟨e.symm ⟨j, hjS⟩, Or.inl (by simpa using hj)⟩
      · exact mem_iUnion.2 ⟨0, Or.inr (mem_iUnion₂.2 ⟨j, hjS, hj⟩)⟩)
  refine ⟨fun j ↦ if hj : j ∈ S then U j ∩ V' (e.symm ⟨j, hj⟩) else U j, fun j ↦ ?_,
    fun j ↦ ?_, eq_univ_of_forall fun x ↦ ?_, eq_empty_of_forall_notMem fun x hx ↦ ?_⟩
  · dsimp only
    split_ifs
    exacts [(hUo j).inter (hV'o _), hUo j]
  · dsimp only
    split_ifs
    exacts [inter_subset_left, subset_rfl]
  · by_cases hxW : x ∈ W
    · obtain ⟨j, hjS, hxj⟩ := mem_iUnion₂.1 hxW
      exact mem_iUnion.2 ⟨j, by simpa [hjS] using hxj⟩
    · obtain ⟨k, hk⟩ := mem_iUnion.1 (hV'c ▸ mem_univ x)
      have hxU : x ∈ U (e k) := ((hV'O k hk).resolve_right hxW)
      exact mem_iUnion.2 ⟨e k, by simpa [(e k).property] using ⟨hxU, hk⟩⟩
  · refine (eq_empty_iff_forall_notMem.1 hV'e) x (mem_iInter.2 fun k ↦ ?_)
    have := mem_iInter₂.1 hx (e k) (e k).property
    simp only [(e k).property, ↓reduceDIte, Subtype.coe_eta, Equiv.symm_apply_apply] at this
    exact this.2

/-- Under Hemmingsen's condition, a finite open cover has an open shrinking in which every
`d + 2` members have empty intersection. -/
private theorem exists_shrinking_forall_biInter_eq_empty {d : ℕ} (h : ShrinkingCondition X d)
    {ι : Type*} [Finite ι] {U : ι → Set X} (hUo : ∀ i, IsOpen (U i)) (hU : ⋃ i, U i = univ) :
    ∃ V : ι → Set X, (∀ i, IsOpen (V i)) ∧ (∀ i, V i ⊆ U i) ∧ ⋃ i, V i = univ ∧
      ∀ S : Finset ι, S.card = d + 2 → ⋂ i ∈ S, V i = ∅ := by
  classical
  have := Fintype.ofFinite ι
  -- Treat the finitely many sets of `d + 2` indices one at a time; shrinking further keeps the
  -- intersections already made empty.
  suffices ∀ 𝒮 : Finset (Finset ι), ∃ V : ι → Set X, (∀ i, IsOpen (V i)) ∧ (∀ i, V i ⊆ U i) ∧
      ⋃ i, V i = univ ∧ ∀ S ∈ 𝒮, S.card = d + 2 → ⋂ i ∈ S, V i = ∅ by
    obtain ⟨V, hVo, hVU, hVc, hVe⟩ := this Finset.univ
    exact ⟨V, hVo, hVU, hVc, fun S hS ↦ hVe S (Finset.mem_univ S) hS⟩
  intro 𝒮
  induction 𝒮 using Finset.induction_on with
  | empty => exact ⟨U, hUo, fun _ ↦ subset_rfl, hU, by simp⟩
  | insert S 𝒮 _ ih =>
    obtain ⟨V, hVo, hVU, hVc, hVe⟩ := ih
    by_cases hS : S.card = d + 2
    · obtain ⟨V', hV'o, hV'V, hV'c, hV'e⟩ := exists_shrinking_biInter_eq_empty h hVo hVc hS
      refine ⟨V', hV'o, fun i ↦ (hV'V i).trans (hVU i), hV'c, fun T hT hTc ↦ ?_⟩
      rcases Finset.mem_insert.1 hT with rfl | hT
      · exact hV'e
      · exact eq_empty_of_subset (biInter_mono subset_rfl fun i _ ↦ hV'V i) (hVe T hT hTc)
    · refine ⟨V, hVo, hVU, hVc, fun T hT hTc ↦ ?_⟩
      rcases Finset.mem_insert.1 hT with rfl | hT
      · exact absurd hTc hS
      · exact hVe T hT hTc

/-- **Hemmingsen's characterization**, the converse direction: a compact space in which every open
cover by `d + 2` sets has an open shrinking with empty intersection has covering dimension at most
`d`. -/
theorem hasCoveringDimensionLE_of_forall_exists_shrinking_iInter_eq_empty [CompactSpace X]
    {d : ℕ} (h : ∀ U : Fin (d + 2) → Set X, (∀ i, IsOpen (U i)) → ⋃ i, U i = univ →
      ∃ V : Fin (d + 2) → Set X, (∀ i, IsOpen (V i)) ∧ (∀ i, V i ⊆ U i) ∧ ⋃ i, V i = univ ∧
        ⋂ i, V i = ∅) :
    HasCoveringDimensionLE X d := by
  classical
  rw [hasCoveringDimensionLE_iff]
  intro 𝒰 h𝒰o h𝒰c
  -- Pass to a finite subcover and shrink it so that no point lies in `d + 2` of its members.
  obtain ⟨t, ht𝒰, htf, htc⟩ := isCompact_univ.elim_finite_subcover_image (c := id) h𝒰o
    (by simpa [← sUnion_eq_biUnion] using h𝒰c.ge)
  have := htf.to_subtype
  have := Fintype.ofFinite t
  obtain ⟨V, hVo, hVU, hVc, hVe⟩ := exists_shrinking_forall_biInter_eq_empty (U := Subtype.val)
    h (fun i : t ↦ h𝒰o _ (ht𝒰 i.property))
    (eq_univ_of_forall fun x ↦ by simpa using htc (mem_univ x))
  refine ⟨range V, forall_mem_range.2 hVo, by rwa [sUnion_range],
    forall_mem_range.2 fun i ↦ ⟨i, ht𝒰 i.property, hVU i⟩, fun x ↦ ?_⟩
  -- The members containing `x` are the images of the indices `i` with `x ∈ V i`.
  have hsub : {W | W ∈ range V ∧ x ∈ W} ⊆ V '' (Finset.univ.filter (x ∈ V ·) : Finset t) := by
    rintro _ ⟨⟨i, rfl⟩, hx⟩
    exact ⟨i, by simpa using hx, rfl⟩
  refine (encard_le_encard hsub).trans ((encard_image_le _ _).trans ?_)
  rw [encard_coe_eq_coe_finsetCard, Nat.cast_le]
  by_contra! hlt
  obtain ⟨S, hSs, hSc⟩ := Finset.exists_subset_card_eq (Nat.succ_le_of_lt hlt)
  refine (eq_empty_iff_forall_notMem.1 (hVe S hSc)) x (mem_iInter₂.2 fun i hi ↦ ?_)
  simpa using hSs hi

/-- **Hemmingsen's characterization**: a compact space has covering dimension at most `d` exactly
when every open cover by `d + 2` sets has an open shrinking with empty intersection. -/
theorem hasCoveringDimensionLE_iff_forall_exists_shrinking_iInter_eq_empty [CompactSpace X]
    {d : ℕ} :
    HasCoveringDimensionLE X d ↔ ∀ U : Fin (d + 2) → Set X, (∀ i, IsOpen (U i)) →
      ⋃ i, U i = univ → ∃ V : Fin (d + 2) → Set X, (∀ i, IsOpen (V i)) ∧ (∀ i, V i ⊆ U i) ∧
        ⋃ i, V i = univ ∧ ⋂ i, V i = ∅ :=
  ⟨fun h _ hUo hU ↦ h.exists_shrinking_iInter_eq_empty hUo hU,
    hasCoveringDimensionLE_of_forall_exists_shrinking_iInter_eq_empty⟩

/-! ### Extension of maps into spheres -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A space in which every map from a closed subset to the unit sphere of a nonzero real normed
space `E` extends is normal: an extension of a map sending two disjoint closed sets to two distinct
points pulls back disjoint neighbourhoods of these points to neighbourhoods of the two sets. -/
private theorem normalSpace_of_forall_exists_extension_sphere [Nontrivial E]
    (h : ∀ A : Set X, IsClosed A → ∀ f : C(A, sphere (0 : E) 1),
      ∃ F : C(X, sphere (0 : E) 1), F.restrict A = f) :
    NormalSpace X := by
  classical
  refine ⟨fun s t hs ht hst ↦ ?_⟩
  obtain ⟨v, hv⟩ := exists_norm_eq E zero_le_one
  let p : sphere (0 : E) 1 := ⟨v, by simpa using hv⟩
  let q : sphere (0 : E) 1 := ⟨-v, by simpa using hv⟩
  have hpq : p ≠ q := fun hpq ↦ by
    have hvv : v = -v := congrArg Subtype.val hpq
    have h2 : (2 : ℝ) • v = 0 := by
      rw [two_smul]
      nth_rw 2 [hvv]
      exact add_neg_cancel v
    rcases smul_eq_zero.1 h2 with h2 | h2
    · norm_num at h2
    · simp [h2] at hv
  -- The points of `s` form a clopen subset of `s ∪ t`, so the map sending them to `p` and the
  -- points of `t` to `q` is continuous.
  have hsc : IsClosed {x : ↥(s ∪ t) | (x : X) ∈ s} := hs.preimage continuous_subtypeVal
  have hso : IsOpen {x : ↥(s ∪ t) | (x : X) ∈ s} := by
    have : {x : ↥(s ∪ t) | (x : X) ∈ s}ᶜ = {x : ↥(s ∪ t) | (x : X) ∈ t} := by
      ext x
      exact ⟨fun hx ↦ x.property.resolve_left hx, fun hx hxs ↦ hst.notMem_of_mem_left hxs hx⟩
    rw [← isClosed_compl_iff, this]
    exact ht.preimage continuous_subtypeVal
  let f : C(↥(s ∪ t), sphere (0 : E) 1) :=
    ⟨fun x ↦ if (x : X) ∈ s then p else q, continuous_if
      (fun x hx ↦ by rw [IsClopen.frontier_eq ⟨hsc, hso⟩] at hx; exact hx.elim)
      continuousOn_const continuousOn_const⟩
  obtain ⟨F, hF⟩ := h _ (hs.union ht) f
  have hFs (x : X) (hx : x ∈ s ∪ t) : F x = if x ∈ s then p else q := congr($hF ⟨x, hx⟩)
  obtain ⟨u, w, hu, hw, hpu, hqw, huw⟩ := t2_separation hpq
  refine ⟨F ⁻¹' u, F ⁻¹' w, hu.preimage F.continuous, hw.preimage F.continuous,
    fun x hx ↦ ?_, fun x hx ↦ ?_, huw.preimage F⟩
  · simpa [mem_preimage, hFs x (Or.inl hx), hx] using hpu
  · simpa [mem_preimage, hFs x (Or.inr hx), hst.notMem_of_mem_right hx] using hqw

/-- The theorem on partitions, in functional form: if every map from a closed subset of a normal
space `X` to the unit sphere of a real normed space `E` of dimension `d + 1` extends to `X`, then
for `d + 1` pairs of disjoint closed sets `(A i, B i)` there are continuous functions `g i`,
negative on `A i` and positive on `B i`, without common zero. The zero set of `g i` is a partition
between `A i` and `B i`, and these partitions have empty intersection. -/
private theorem exists_neg_pos_forall_exists_ne_zero_of_forall_exists_extension_sphere
    [NormalSpace X] {d : ℕ} (hE : finrank ℝ E = d + 1)
    (h : ∀ A : Set X, IsClosed A → ∀ f : C(A, sphere (0 : E) 1),
      ∃ F : C(X, sphere (0 : E) 1), F.restrict A = f)
    {A B : Fin (d + 1) → Set X} (hA : ∀ i, IsClosed (A i)) (hB : ∀ i, IsClosed (B i))
    (hAB : ∀ i, Disjoint (A i) (B i)) :
    ∃ g : Fin (d + 1) → C(X, ℝ), (∀ i, ∀ x ∈ A i, g i x < 0) ∧ (∀ i, ∀ x ∈ B i, 0 < g i x) ∧
      ∀ x, ∃ i, g i x ≠ 0 := by
  have : FiniteDimensional ℝ E := Module.finite_of_finrank_eq_succ hE
  let L : E ≃L[ℝ] (Fin (d + 1) → ℝ) := (Module.finBasisOfFinrankEq ℝ E hE).equivFunL
  -- Urysohn functions `φ i`, equal to `0` on `A i` and to `1` on `B i`, define a map `a` with
  -- coordinates `φ i - 1 / 2`, which does not vanish on the closed set `K = ⋃ i, A i ∪ B i`.
  choose φ hφ0 hφ1 _ using fun i ↦ exists_continuous_zero_one_of_isClosed (hA i) (hB i) (hAB i)
  let K : Set X := ⋃ i, A i ∪ B i
  have hK : IsClosed K := isClosed_iUnion_of_finite fun i ↦ (hA i).union (hB i)
  let a : C(X, E) := ⟨fun x ↦ L.symm fun i ↦ φ i x - 1 / 2, by fun_prop⟩
  have hLa (x : X) (i : Fin (d + 1)) : L (a x) i = φ i x - 1 / 2 := by simp [a]
  have ha (x : X) (hx : x ∈ K) : a x ≠ 0 := by
    obtain ⟨i, hi⟩ := mem_iUnion.1 hx
    intro h0
    have := hLa x i
    rw [h0, map_zero, Pi.zero_apply] at this
    rcases hi with hi | hi
    · rw [hφ0 i hi] at this; norm_num at this
    · rw [hφ1 i hi] at this; norm_num at this
  -- Normalize `a` on `K` into the sphere and extend; `g i` is the `i`-th coordinate of the
  -- extension, which on `K` is a positive multiple of `φ i - 1 / 2`.
  let f : C(K, sphere (0 : E) 1) :=
    ⟨fun x ↦ ⟨‖a x‖⁻¹ • a x, by simp [norm_smul, ha x x.property]⟩, by
      refine Continuous.subtype_mk (Continuous.smul ?_ (by fun_prop)) _
      exact (continuous_norm.comp (by fun_prop)).inv₀ fun x ↦ norm_ne_zero_iff.2 (ha x x.property)⟩
  obtain ⟨G, hG⟩ := h K hK f
  have hgK (x : X) (hx : x ∈ K) (i : Fin (d + 1)) :
      L (G x) i = ‖a x‖⁻¹ * (φ i x - 1 / 2) := by
    have : (G x : E) = ‖a x‖⁻¹ • a x := by
      rw [← ContinuousMap.restrict_apply G K ⟨x, hx⟩, hG]; rfl
    simp [this, hLa]
  have hapos (x : X) (hx : x ∈ K) : 0 < ‖a x‖⁻¹ := inv_pos.2 (norm_pos_iff.2 (ha x hx))
  refine ⟨fun i ↦ ⟨fun x ↦ L (G x) i, by fun_prop⟩, fun i x hx ↦ ?_, fun i x hx ↦ ?_, fun x ↦ ?_⟩
  · have hxK : x ∈ K := mem_iUnion.2 ⟨i, Or.inl hx⟩
    rw [ContinuousMap.coe_mk, hgK x hxK, hφ0 i hx, Pi.zero_apply]
    exact mul_neg_of_pos_of_neg (hapos x hxK) (by norm_num)
  · have hxK : x ∈ K := mem_iUnion.2 ⟨i, Or.inr hx⟩
    rw [ContinuousMap.coe_mk, hgK x hxK, hφ1 i hx, Pi.one_apply]
    exact mul_pos (hapos x hxK) (by norm_num)
  · -- `G x` lies on the sphere, so it is nonzero.
    by_contra! h0
    have : (G x : E) = 0 := L.injective (by ext i; simpa using h0 i)
    simpa [this] using (G x).property

/-- If every map from a closed subset of a normal space `X` to the unit sphere of a real normed
space `E` of dimension `d + 1` extends to `X`, then every open cover of `X` by `d + 2` sets has an
open shrinking with empty intersection. -/
private theorem exists_shrinking_iInter_eq_empty_of_forall_exists_extension_sphere
    [NormalSpace X] {d : ℕ} (hE : finrank ℝ E = d + 1)
    (h : ∀ A : Set X, IsClosed A → ∀ f : C(A, sphere (0 : E) 1),
      ∃ F : C(X, sphere (0 : E) 1), F.restrict A = f)
    {U : Fin (d + 2) → Set X} (hUo : ∀ i, IsOpen (U i)) (hU : ⋃ i, U i = univ) :
    ∃ V : Fin (d + 2) → Set X, (∀ i, IsOpen (V i)) ∧ (∀ i, V i ⊆ U i) ∧ ⋃ i, V i = univ ∧
      ⋂ i, V i = ∅ := by
  -- A closed shrinking `F` of `U`, and functions `g i` for the first `d + 1` indices, negative
  -- on `F i`, positive off `U i`, and without common zero.
  obtain ⟨F, hFX, hFc, hFU⟩ := exists_iUnion_eq_closed_subset hUo (fun _ ↦ toFinite _) hU
  replace hFX (x : X) : ∃ i, x ∈ F i := mem_iUnion.1 (hFX ▸ mem_univ x)
  obtain ⟨g, hgneg, hgpos, hgne⟩ :=
    exists_neg_pos_forall_exists_ne_zero_of_forall_exists_extension_sphere hE h
      (fun i ↦ hFc i.castSucc) (fun i ↦ (hUo i.castSucc).isClosed_compl)
      (fun i ↦ disjoint_compl_right_iff_subset.2 (hFU i.castSucc))
  -- The shrinking: `{g i < 0}` for the first `d + 1` indices, and the part of the last member
  -- where some `g i` is positive.
  refine ⟨Fin.lastCases (U (Fin.last _) ∩ ⋃ i, {x | 0 < g i x}) fun i ↦ {x | g i x < 0},
    fun i ↦ ?_, fun i ↦ ?_, eq_univ_of_forall fun x ↦ ?_, eq_empty_of_forall_notMem fun x hx ↦ ?_⟩
  · induction i using Fin.lastCases with
    | last =>
      simpa using (hUo _).inter (isOpen_iUnion fun i ↦ isOpen_lt continuous_const (g i).continuous)
    | cast i => simpa using isOpen_lt (g i).continuous continuous_const
  · induction i using Fin.lastCases with
    | last => simp
    | cast i =>
      intro x hx
      by_contra hxU
      exact (hgpos i x hxU).not_gt (by simpa using hx)
  · rw [mem_iUnion, Fin.exists_fin_succ']
    simp only [Fin.lastCases_castSucc, Fin.lastCases_last, mem_ofPred_eq, mem_inter_iff,
      mem_iUnion]
    by_contra! hx
    obtain ⟨i, hi⟩ := hFX x
    obtain ⟨j, hj⟩ := hgne x
    induction i using Fin.lastCases with
    | last => exact hj (le_antisymm (hx.2 (hFU _ hi) j) (hx.1 j))
    | cast i => exact (hgneg i x hi).not_ge (hx.1 i)
  · rw [mem_iInter, Fin.forall_fin_succ'] at hx
    simp only [Fin.lastCases_castSucc, Fin.lastCases_last, mem_ofPred_eq, mem_inter_iff,
      mem_iUnion] at hx
    obtain ⟨hneg, -, i, hi⟩ := hx
    exact (hneg i).not_gt hi

/-- **Covering dimension from extension of maps into spheres.** If `X` is a compact space and every
continuous map from a closed subset of `X` to the unit sphere of a real normed space of dimension
`d + 1`, a sphere `Sᵈ`, extends to `X`, then `X` has covering dimension at most `d`. Such an `X`
is automatically normal.

This is the sufficiency half of the characterization of covering dimension by extension of maps
into `Sᵈ` (Engelking, Theorem 3.2.10). -/
theorem hasCoveringDimensionLE_of_forall_exists_extension_sphere [CompactSpace X] {d : ℕ}
    (hE : finrank ℝ E = d + 1)
    (h : ∀ A : Set X, IsClosed A → ∀ f : C(A, sphere (0 : E) 1),
      ∃ F : C(X, sphere (0 : E) 1), F.restrict A = f) :
    HasCoveringDimensionLE X d :=
  have : Nontrivial E := Module.nontrivial_of_finrank_eq_succ hE
  have : NormalSpace X := normalSpace_of_forall_exists_extension_sphere h
  hasCoveringDimensionLE_of_forall_exists_shrinking_iInter_eq_empty fun _ hUo hU ↦
    exists_shrinking_iInter_eq_empty_of_forall_exists_extension_sphere hE h hUo hU

end TauCeti
