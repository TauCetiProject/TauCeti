/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Order.RegionBetween
import TauCeti.Topology.Order.IntermediateValue

/-!
# Graphs and consecutive bands over a connected base

Let `f : ι → X → ℝ` be a family of functions, continuous on a set `s ⊆ X`, any two of which
either agree on `s` or take different values at every point of `s`. Over a preconnected base the
members of the family are then strictly ordered: two members which do not agree on `s` satisfy
`f i < f j` on all of `s` or `f j < f i` on all of `s`.

Two members are *consecutive over `s`* (`TauCeti.IsConsecutiveOn`) when `f i < f j` on `s` and no
member of the family lies strictly between them at a point of `s`. The open bands
`regionBetween (f i) (f j) s` between consecutive members form `TauCeti.consecutiveBands f s`, and
together with the graphs of the members over `s` they are the strata of the family over `s`,
`TauCeti.bandStrata f s`. These strata

* cover the cylinder `s ×ˢ univ` when `s` is preconnected and, over each point of `s`, the values
  of the family are unbounded above and below with only finitely many distinct values in each
  compact interval (`TauCeti.sUnion_bandStrata`);
* are pairwise disjoint (`TauCeti.pairwiseDisjoint_bandStrata`);
* form a locally finite family when the graphs do and `s` meets arbitrarily small neighbourhoods
  of every point in a preconnected set (`TauCeti.locallyFinite_bandStrata`). This holds, for
  instance, for a convex subset of a real normed space.

On a face `s₀ ⊆ closure s` of the base carrying its own family of sections `g`, two consecutive
members of `f` which extend continuously to `s₀` restrict to equal or consecutive members of `g`
(`TauCeti.IsConsecutiveOn.eqOn_or_isConsecutiveOn`), so that the closure of a band over `s` meets
the cylinder over `s₀` in a union of strata of `g`
(`TauCeti.IsConsecutiveOn.exists_closure_regionBetween_inter_eq_sUnion`). This requires every graph
of `g` to lie in the closure of the union of the graphs of `f`.

In Łojasiewicz's triangulation of semianalytic sets, the base is an open simplex of a
triangulation compatible with the projections of the pairwise intersections of a locally finite
family of graphs; the members of that family whose projection contains the simplex restrict to a
family of sections as above, and these strata are the cells of the decomposition of the cylinder
over that simplex.

## Main declarations

* `TauCeti.IsConsecutiveOn f s i j`: `f i` and `f j` are consecutive over `s`.
* `TauCeti.consecutiveBands f s`: the open bands between consecutive members of `f` over `s`.
* `TauCeti.bandStrata f s`: the graphs over `s` and the consecutive bands.
* `TauCeti.exists_isConsecutiveOn_mem_regionBetween`: a point of the cylinder which lies on no
  graph lies in the band between two consecutive members.
* `TauCeti.sUnion_bandStrata`, `TauCeti.pairwiseDisjoint_bandStrata`,
  `TauCeti.locallyFinite_bandStrata`: the strata form a locally finite partition of the cylinder.
* `TauCeti.IsConsecutiveOn.eqOn_or_isConsecutiveOn`: consecutive members restrict to equal or
  consecutive members on a face.
* `TauCeti.IsConsecutiveOn.exists_closure_regionBetween_inter_eq_sUnion`: the closure of a band
  meets the cylinder over a face in a union of strata.

## References

* S. Łojasiewicz, *Triangulation of semi-analytic sets*, Ann. Scuola Norm. Sup. Pisa (3) **18**
  (1964), 449–474, §4, steps II and III.
-/

public section

open Set Filter Topology

namespace TauCeti

variable {X ι : Type*} {f : ι → X → ℝ} {s : Set X} {i j i' j' : ι}

/-- Two members `f i` and `f j` of a family of real functions are *consecutive over `s`*:
`f i < f j` on `s`, and no member of the family lies strictly between them at a point of `s`. -/
structure IsConsecutiveOn (f : ι → X → ℝ) (s : Set X) (i j : ι) : Prop where
  /-- The lower member lies strictly below the upper one on `s`. -/
  lt : ∀ x ∈ s, f i x < f j x
  /-- No member of the family lies strictly between the two at a point of `s`. -/
  notMem_Ioo : ∀ k, ∀ x ∈ s, f k x ∉ Ioo (f i x) (f j x)

/-- The open bands over `s` between consecutive members of the family `f`. -/
def consecutiveBands (f : ι → X → ℝ) (s : Set X) : Set (Set (X × ℝ)) :=
  {B | ∃ i j, IsConsecutiveOn f s i j ∧ regionBetween (f i) (f j) s = B}

/-- The strata of the family `f` over `s`: the graphs of its members over `s` and the open bands
between consecutive members. -/
def bandStrata (f : ι → X → ℝ) (s : Set X) : Set (Set (X × ℝ)) :=
  range (fun i ↦ s.graphOn (f i)) ∪ consecutiveBands f s

@[simp]
theorem mem_consecutiveBands {B : Set (X × ℝ)} :
    B ∈ consecutiveBands f s ↔ ∃ i j, IsConsecutiveOn f s i j ∧ regionBetween (f i) (f j) s = B :=
  Iff.rfl

@[simp]
theorem mem_bandStrata {B : Set (X × ℝ)} :
    B ∈ bandStrata f s ↔ (∃ i, s.graphOn (f i) = B) ∨ B ∈ consecutiveBands f s :=
  Iff.rfl

/-- The graph of each member of the family over `s` is a stratum. -/
theorem graphOn_mem_bandStrata (f : ι → X → ℝ) (s : Set X) (i : ι) :
    s.graphOn (f i) ∈ bandStrata f s :=
  .inl ⟨i, rfl⟩

/-- Every band between consecutive members is a stratum. -/
theorem consecutiveBands_subset_bandStrata (f : ι → X → ℝ) (s : Set X) :
    consecutiveBands f s ⊆ bandStrata f s :=
  subset_union_right

/-- The open band between two consecutive members is a consecutive band. -/
theorem IsConsecutiveOn.regionBetween_mem_consecutiveBands (h : IsConsecutiveOn f s i j) :
    regionBetween (f i) (f j) s ∈ consecutiveBands f s :=
  ⟨i, j, h, rfl⟩

namespace IsConsecutiveOn

/-- The lower member of a consecutive pair determines the upper one on `s`. -/
theorem eqOn_upper (h : IsConsecutiveOn f s i j) (h' : IsConsecutiveOn f s i j') :
    EqOn (f j) (f j') s := fun x hx ↦
  le_antisymm (not_lt.1 fun hlt ↦ h.notMem_Ioo j' x hx ⟨h'.lt x hx, hlt⟩)
    (not_lt.1 fun hlt ↦ h'.notMem_Ioo j x hx ⟨h.lt x hx, hlt⟩)

/-- The upper member of a consecutive pair determines the lower one on `s`. -/
theorem eqOn_lower (h : IsConsecutiveOn f s i j) (h' : IsConsecutiveOn f s i' j) :
    EqOn (f i) (f i') s := fun x hx ↦
  le_antisymm (not_lt.1 fun hlt ↦ h'.notMem_Ioo i x hx ⟨hlt, h.lt x hx⟩)
    (not_lt.1 fun hlt ↦ h.notMem_Ioo i' x hx ⟨hlt, h'.lt x hx⟩)

/-- No graph of a member of the family meets the band between two consecutive members. -/
theorem disjoint_graphOn (h : IsConsecutiveOn f s i j) (k : ι) :
    Disjoint (s.graphOn (f k)) (regionBetween (f i) (f j) s) :=
  Set.disjoint_left.2 fun p hk hp ↦ h.notMem_Ioo k p.1 hp.1 ((mem_graphOn.1 hk).2 ▸ hp.2)

/-- Suppose that any two members of the family which agree at a point of `s` agree on all of `s`.
If the bands between two consecutive pairs meet, then the pairs have the same lower and the same
upper members on `s`. -/
theorem eqOn_of_mem_regionBetween (hsep : ∀ i j, EqOn (f i) (f j) s ∨ ∀ x ∈ s, f i x ≠ f j x)
    (h : IsConsecutiveOn f s i j) (h' : IsConsecutiveOn f s i' j') {p : X × ℝ}
    (hp : p ∈ regionBetween (f i) (f j) s) (hp' : p ∈ regionBetween (f i') (f j') s) :
    EqOn (f i) (f i') s ∧ EqOn (f j) (f j') s := by
  obtain ⟨hx, hi, hj⟩ := hp
  obtain ⟨-, hi', hj'⟩ := hp'
  have hlo : f i p.1 = f i' p.1 :=
    le_antisymm (not_lt.1 fun hlt ↦ h'.notMem_Ioo i _ hx ⟨hlt, hi.trans hj'⟩)
      (not_lt.1 fun hlt ↦ h.notMem_Ioo i' _ hx ⟨hlt, hi'.trans hj⟩)
  have hhi : f j p.1 = f j' p.1 :=
    le_antisymm (not_lt.1 fun hlt ↦ h.notMem_Ioo j' _ hx ⟨hi.trans hj', hlt⟩)
      (not_lt.1 fun hlt ↦ h'.notMem_Ioo j _ hx ⟨hi'.trans hj, hlt⟩)
  exact ⟨(hsep i i').resolve_right fun hne ↦ hne _ hx hlo,
    (hsep j j').resolve_right fun hne ↦ hne _ hx hhi⟩

end IsConsecutiveOn

/-- The strata of a family whose members agree on `s` as soon as they agree at one point of `s`
are pairwise disjoint. -/
theorem pairwiseDisjoint_bandStrata
    (hsep : ∀ i j, EqOn (f i) (f j) s ∨ ∀ x ∈ s, f i x ≠ f j x) :
    (bandStrata f s).PairwiseDisjoint id := by
  rintro B (⟨i, rfl⟩ | ⟨i, j, h, rfl⟩) B' (⟨i', rfl⟩ | ⟨i', j', h', rfl⟩) hne
  · rcases hsep i i' with he | hne'
    · exact absurd (graphOn_inj.2 he) hne
    · exact Set.disjoint_left.2 fun p hp hp' ↦ hne' p.1 (mem_graphOn.1 hp).1
        ((mem_graphOn.1 hp).2.trans (mem_graphOn.1 hp').2.symm)
  · exact h'.disjoint_graphOn i
  · exact (h.disjoint_graphOn i').symm
  · refine Set.disjoint_left.2 fun p hp hp' ↦ hne ?_
    obtain ⟨hlo, hhi⟩ := h.eqOn_of_mem_regionBetween hsep h' hp hp'
    exact regionBetween_congr hlo hhi

section Cover

variable [TopologicalSpace X]

/-- Over a preconnected base, a point `(x, t)` of the cylinder `s ×ˢ univ` which lies on no
graph of the family lies in the open band between two consecutive members, provided that some
values of the family at `x` lie below `t` and some lie above `t`, and that only finitely many
distinct values lie in each compact interval. -/
theorem exists_isConsecutiveOn_mem_regionBetween (hs : IsPreconnected s)
    (hf : ∀ i, ContinuousOn (f i) s)
    (hsep : ∀ i j, EqOn (f i) (f j) s ∨ ∀ x ∈ s, f i x ≠ f j x) {x : X} {t : ℝ} (hx : x ∈ s)
    (hfin : ∀ a b, (range (fun i ↦ f i x) ∩ Icc a b).Finite) (hlo : ∃ i, f i x < t)
    (hhi : ∃ j, t < f j x) (ht : ∀ i, f i x ≠ t) :
    ∃ i j, IsConsecutiveOn f s i j ∧ (x, t) ∈ regionBetween (f i) (f j) s := by
  obtain ⟨i₀, hi₀⟩ := hlo
  obtain ⟨j₀, hj₀⟩ := hhi
  -- the highest value below `t` and the lowest value above `t`
  obtain ⟨_, ⟨⟨i, rfl⟩, hi₁, hi₂⟩, himax⟩ := exists_max_image
    (range (fun k ↦ f k x) ∩ Icc (f i₀ x) t) id (hfin _ _) ⟨_, ⟨i₀, rfl⟩, le_rfl, hi₀.le⟩
  obtain ⟨_, ⟨⟨j, rfl⟩, hj₁, hj₂⟩, hjmin⟩ := exists_min_image
    (range (fun k ↦ f k x) ∩ Icc t (f j₀ x)) id (hfin _ _) ⟨_, ⟨j₀, rfl⟩, hj₀.le, le_rfl⟩
  have hit : f i x < t := hi₂.lt_of_ne (ht i)
  have htj : t < f j x := hj₁.lt_of_ne (ht j).symm
  have hlt : ∀ {i j y}, y ∈ s → f i y < f j y → ∀ z ∈ s, f i z < f j z :=
    fun hy hlt ↦ hs.forall_lt_of_lt (hf _) (hf _) (hsep _ _) hy hlt
  refine ⟨i, j, ⟨hlt hx (hit.trans htj), fun k y hy hk ↦ ?_⟩, hx, hit, htj⟩
  have h₁ := hlt hy hk.1 x hx
  have h₂ := hlt hy hk.2 x hx
  rcases lt_trichotomy (f k x) t with hkt | hkt | hkt
  · exact (himax _ ⟨⟨k, rfl⟩, hi₁.trans h₁.le, hkt.le⟩).not_gt h₁
  · exact ht k hkt
  · exact (hjmin _ ⟨⟨k, rfl⟩, hkt.le, h₂.le.trans hj₂⟩).not_gt h₂

/-- The strata of a family over a preconnected base cover the cylinder over the base, provided
that at every point of the base the values of the family are unbounded above and below, with only
finitely many distinct values in each compact interval. The finiteness condition follows from
`LocallyFinite.finite_range_apply_inter` (in `TauCeti.Topology.LocallyFinite.Projection`) when the
graphs form a locally finite family. -/
theorem sUnion_bandStrata (hs : IsPreconnected s) (hf : ∀ i, ContinuousOn (f i) s)
    (hsep : ∀ i j, EqOn (f i) (f j) s ∨ ∀ x ∈ s, f i x ≠ f j x)
    (hfin : ∀ x ∈ s, ∀ a b, (range (fun i ↦ f i x) ∩ Icc a b).Finite)
    (hunb : ∀ x ∈ s, ∀ t, (∃ i, f i x < t) ∧ ∃ j, t < f j x) :
    ⋃₀ bandStrata f s = s ×ˢ (univ : Set ℝ) := by
  refine Subset.antisymm (sUnion_subset ?_) ?_
  · rintro B (⟨i, rfl⟩ | ⟨i, j, -, rfl⟩)
    · exact fun p hp ↦ ⟨(mem_graphOn.1 hp).1, trivial⟩
    · exact regionBetween_subset _ _ _
  · rintro ⟨x, t⟩ ⟨hx, -⟩
    by_cases ht : ∃ i, f i x = t
    · obtain ⟨i, hi⟩ := ht
      exact ⟨_, graphOn_mem_bandStrata f s i, mem_graphOn.2 ⟨hx, hi⟩⟩
    · obtain ⟨i, j, h, hp⟩ := exists_isConsecutiveOn_mem_regionBetween hs hf hsep hx (hfin x hx)
        (hunb x hx t).1 (hunb x hx t).2 (not_exists.1 ht)
      exact ⟨_, consecutiveBands_subset_bandStrata f s h.regionBetween_mem_consecutiveBands, hp⟩

end Cover

section LocallyFinite

variable [TopologicalSpace X]

/-- Given a neighbourhood `V` of a point meeting `s` in a preconnected set, and an interval
`Ioo a b`, at most one band between consecutive members meets the box `V ×ˢ Ioo a b` without
either of its boundary graphs meeting the box. -/
private theorem subsingleton_consecutiveBands_inter {V : Set X} (hV : IsPreconnected (V ∩ s))
    (hf : ∀ i, ContinuousOn (f i) s)
    (hsep : ∀ i j, EqOn (f i) (f j) s ∨ ∀ x ∈ s, f i x ≠ f j x) {a b : ℝ} (hab : a < b) :
    {B | ∃ i j, IsConsecutiveOn f s i j ∧ regionBetween (f i) (f j) s = B ∧
      (B ∩ V ×ˢ Ioo a b).Nonempty ∧ (s.graphOn (f i) ∩ V ×ˢ Ioo a b) = ∅ ∧
        (s.graphOn (f j) ∩ V ×ˢ Ioo a b) = ∅}.Subsingleton := by
  -- a member whose graph misses the box lies entirely below or entirely above it over `V ∩ s`
  have hside : ∀ k, s.graphOn (f k) ∩ V ×ˢ Ioo a b = ∅ →
      (∀ y ∈ V ∩ s, f k y ≤ a) ∨ ∀ y ∈ V ∩ s, b ≤ f k y := fun k hk ↦
    hV.forall_le_or_forall_ge ((hf k).mono inter_subset_right) hab fun y hy hy' ↦
      (eq_empty_iff_forall_notMem.1 hk) (y, f k y) ⟨⟨y, hy.2, rfl⟩, hy.1, hy'⟩
  -- such a band contains the whole vertical segment over `V ∩ s` through the box
  have hmem : ∀ i j, IsConsecutiveOn f s i j →
      (regionBetween (f i) (f j) s ∩ V ×ˢ Ioo a b).Nonempty →
      s.graphOn (f i) ∩ V ×ˢ Ioo a b = ∅ → s.graphOn (f j) ∩ V ×ˢ Ioo a b = ∅ →
      ∀ y ∈ V ∩ s, ∀ t ∈ Ioo a b, (y, t) ∈ regionBetween (f i) (f j) s := by
    rintro i j - ⟨q, ⟨hqs, hqi, hqj⟩, hqV, hqa, hqb⟩ hi hj y hy t ⟨hat, htb⟩
    have hq : q.1 ∈ V ∩ s := ⟨hqV, hqs⟩
    have hi' := (hside i hi).resolve_right fun h ↦ (h _ hq).not_gt (hqi.trans hqb)
    have hj' := (hside j hj).resolve_left fun h ↦ (h _ hq).not_gt (hqa.trans hqj)
    exact ⟨hy.2, (hi' y hy).trans_lt hat, htb.trans_le (hj' y hy)⟩
  rintro _ ⟨i, j, h, rfl, ⟨q, hq, hqW⟩, hi, hj⟩ _ ⟨i', j', h', rfl, hne', hi', hj'⟩
  have hy : q.1 ∈ V ∩ s := ⟨hqW.1, hq.1⟩
  obtain ⟨hlo, hhi⟩ := h.eqOn_of_mem_regionBetween hsep h'
    (hmem i j h ⟨q, hq, hqW⟩ hi hj q.1 hy _ hqW.2)
    (hmem i' j' h' hne' hi' hj' q.1 hy _ hqW.2)
  exact regionBetween_congr hlo hhi

/-- The strata of a family form a locally finite family as soon as the graphs do, provided that
every point has arbitrarily small neighbourhoods meeting `s` in a preconnected set. -/
theorem locallyFinite_bandStrata
    (hs : ∀ x, ∀ U ∈ 𝓝 x, ∃ V ∈ 𝓝 x, V ⊆ U ∧ IsPreconnected (V ∩ s))
    (hf : ∀ i, ContinuousOn (f i) s)
    (hsep : ∀ i j, EqOn (f i) (f j) s ∨ ∀ x ∈ s, f i x ≠ f j x)
    (hlf : LocallyFinite fun i ↦ s.graphOn (f i)) :
    LocallyFinite ((↑) : bandStrata f s → Set (X × ℝ)) := by
  rintro ⟨x, t⟩
  obtain ⟨U, hU, hUfin⟩ := hlf (x, t)
  obtain ⟨u, hu, v, hv, huv⟩ := mem_nhds_prod_iff.1 hU
  obtain ⟨a, b, hab, hv'⟩ := mem_nhds_iff_exists_Ioo_subset.1 hv
  obtain ⟨V, hV, hVu, hVs⟩ := hs x u hu
  set W := V ×ˢ Ioo a b
  have hWU : W ⊆ U := (prod_mono hVu hv').trans huv
  set L := {i | (s.graphOn (f i) ∩ W).Nonempty}
  have hL : L.Finite := hUfin.subset fun i ⟨q, hq, hqW⟩ ↦ ⟨q, hq, hWU hqW⟩
  -- the bands whose lower, respectively upper, boundary graph meets the box
  have hlow : ∀ i, {B | ∃ j, IsConsecutiveOn f s i j ∧ regionBetween (f i) (f j) s = B}.Finite :=
    fun i ↦ Subsingleton.finite <| by
      rintro _ ⟨j, h, rfl⟩ _ ⟨j', h', rfl⟩
      exact regionBetween_congr (eqOn_refl _ _) (h.eqOn_upper h')
  have hupp : ∀ j, {B | ∃ i, IsConsecutiveOn f s i j ∧ regionBetween (f i) (f j) s = B}.Finite :=
    fun j ↦ Subsingleton.finite <| by
      rintro _ ⟨i, h, rfl⟩ _ ⟨i', h', rfl⟩
      exact regionBetween_congr (h.eqOn_lower h') (eqOn_refl _ _)
  have hT := (((hL.image fun i ↦ s.graphOn (f i)).union (hL.biUnion fun i _ ↦ hlow i)).union
    (hL.biUnion fun j _ ↦ hupp j)).union
    (subsingleton_consecutiveBands_inter hVs hf hsep (hab.1.trans hab.2)).finite
  refine ⟨W, prod_mem_nhds hV (Ioo_mem_nhds hab.1 hab.2),
    (hT.preimage Subtype.val_injective.injOn).subset ?_⟩
  rintro ⟨B, (⟨i, rfl⟩ | ⟨i, j, h, rfl⟩)⟩ hB
  · exact .inl (.inl (.inl ⟨i, hB, rfl⟩))
  · by_cases hi : i ∈ L
    · exact .inl (.inl (.inr (mem_biUnion hi ⟨j, h, rfl⟩)))
    by_cases hj : j ∈ L
    · exact .inl (.inr (mem_biUnion hj ⟨i, h, rfl⟩))
    exact .inr ⟨i, j, h, rfl, hB, not_nonempty_iff_eq_empty.1 hi,
      not_nonempty_iff_eq_empty.1 hj⟩

end LocallyFinite

section Face

/-! ### Restriction to a face

Let `s₀ ⊆ closure s` be a face of the base, carrying its own family of sections `g`, such that
every graph of `g` over `s₀` lies in the closure of the union of the graphs of `f` over `s`.
Two consecutive members of `f` over `s` which extend continuously to `s₀` and restrict on `s₀` to
members of `g` restrict to equal or consecutive members of `g`, so the closure of the band between
them meets the cylinder over `s₀` in strata of `g`. -/

variable [TopologicalSpace X] {κ : Type*} {g : κ → X → ℝ} {s₀ : Set X} {k₁ k₂ : κ}

/-- **Consecutive sections restrict to equal or consecutive sections on a face.** Let
`s₀ ⊆ closure s` and let every graph of the family `g` over `s₀` lie in the closure of the union
of the graphs of `f` over `s`. If `f i` and `f j` are consecutive over `s`, continuous on
`s ∪ s₀`, and agree on `s₀` with `g k₁` and `g k₂`, then `g k₁` and `g k₂` agree on `s₀` or are
consecutive over `s₀`. -/
theorem IsConsecutiveOn.eqOn_or_isConsecutiveOn (h : IsConsecutiveOn f s i j)
    (hs₀ : s₀ ⊆ closure s) (hfi : ContinuousOn (f i) (s ∪ s₀))
    (hfj : ContinuousOn (f j) (s ∪ s₀))
    (hsep₀ : ∀ k k', EqOn (g k) (g k') s₀ ∨ ∀ x ∈ s₀, g k x ≠ g k' x)
    (hg : ∀ k, s₀.graphOn (g k) ⊆ closure (⋃ i, s.graphOn (f i)))
    (hi : EqOn (f i) (g k₁) s₀) (hj : EqOn (f j) (g k₂) s₀) :
    EqOn (g k₁) (g k₂) s₀ ∨ IsConsecutiveOn g s₀ k₁ k₂ := by
  have hci : ∀ y ∈ s₀, ContinuousWithinAt (f i) s y :=
    fun y hy ↦ (hfi y (.inr hy)).mono subset_union_left
  have hcj : ∀ y ∈ s₀, ContinuousWithinAt (f j) s y :=
    fun y hy ↦ (hfj y (.inr hy)).mono subset_union_left
  refine (hsep₀ k₁ k₂).imp id fun hne ↦ ⟨fun y hy ↦ ?_, fun k y hy hk ↦ ?_⟩
  · exact (hi hy ▸ hj hy ▸ ContinuousWithinAt.closure_le (hs₀ hy) (hci y hy) (hcj y hy)
      fun x hx ↦ (h.lt x hx).le).lt_of_ne (hne y hy)
  rw [← hi hy, ← hj hy] at hk
  -- near `y`, the members `f i` and `f j` stay below and above a box around `(y, g k y)`
  obtain ⟨a, hia, hak⟩ := exists_between hk.1
  obtain ⟨b, hkb, hbj⟩ := exists_between hk.2
  obtain ⟨U, hU, hyU, hUs⟩ := mem_nhdsWithin.1
    (((hci y hy).eventually (gt_mem_nhds hia)).and ((hcj y hy).eventually (lt_mem_nhds hbj)))
  -- so a point of a graph of `f` in that box lies strictly between `f i` and `f j`
  obtain ⟨p, ⟨hpU, hpa, hpb⟩, hp⟩ := mem_closure_iff.1 (hg k ⟨y, hy, rfl⟩) _
    (hU.prod isOpen_Ioo) ⟨hyU, hak, hkb⟩
  obtain ⟨i', hp⟩ := mem_iUnion.1 hp
  obtain ⟨hps, hpi'⟩ := mem_graphOn.1 hp
  obtain ⟨h₁, h₂⟩ := hUs ⟨hpU, hps⟩
  exact h.notMem_Ioo i' p.1 hps ⟨h₁.trans (hpi' ▸ hpa), (hpi' ▸ hpb).trans h₂⟩

/-- **The closure of a band meets the cylinder over a face in strata.** Under the hypotheses of
`TauCeti.IsConsecutiveOn.eqOn_or_isConsecutiveOn`, with `f i` and `f j` continuous on all of
`closure s`, the closure of the band between the consecutive members `f i` and `f j` over `s`
meets `s₀ ×ˢ univ` in a union of strata of `g` over `s₀`. -/
theorem IsConsecutiveOn.exists_closure_regionBetween_inter_eq_sUnion
    (h : IsConsecutiveOn f s i j) (hs₀ : s₀ ⊆ closure s)
    (hfi : ContinuousOn (f i) (closure s)) (hfj : ContinuousOn (f j) (closure s))
    (hsep₀ : ∀ k k', EqOn (g k) (g k') s₀ ∨ ∀ x ∈ s₀, g k x ≠ g k' x)
    (hg : ∀ k, s₀.graphOn (g k) ⊆ closure (⋃ i, s.graphOn (f i)))
    (hi : EqOn (f i) (g k₁) s₀) (hj : EqOn (f j) (g k₂) s₀) :
    ∃ T ⊆ bandStrata g s₀,
      closure (regionBetween (f i) (f j) s) ∩ s₀ ×ˢ (univ : Set ℝ) = ⋃₀ T := by
  have hcl : closure (regionBetween (f i) (f j) s) ∩ s₀ ×ˢ (univ : Set ℝ) =
      closedRegionBetween (g k₁) (g k₂) s₀ := by
    rw [closure_regionBetween hfi hfj h.lt, ← closedRegionBetween_congr hi hj]
    ext p
    simp only [mem_inter_iff, mem_closedRegionBetween, mem_prod, mem_univ, and_true]
    exact ⟨fun ⟨⟨_, hp⟩, hp₀⟩ ↦ ⟨hp₀, hp⟩, fun ⟨hp₀, hp⟩ ↦ ⟨⟨hs₀ hp₀, hp⟩, hp₀⟩⟩
  rw [hcl]
  have hss : s ∪ s₀ ⊆ closure s := union_subset subset_closure hs₀
  rcases h.eqOn_or_isConsecutiveOn hs₀ (hfi.mono hss) (hfj.mono hss) hsep₀ hg hi hj with he | hc
  · refine ⟨{s₀.graphOn (g k₁)}, singleton_subset_iff.2 (graphOn_mem_bandStrata g s₀ k₁), ?_⟩
    rw [sUnion_singleton, ← closedRegionBetween_congr (eqOn_refl _ _) he,
      closedRegionBetween_self]
  · refine ⟨{s₀.graphOn (g k₁), regionBetween (g k₁) (g k₂) s₀, s₀.graphOn (g k₂)}, ?_, ?_⟩
    · rintro B (rfl | rfl | rfl)
      exacts [graphOn_mem_bandStrata g s₀ k₁,
        consecutiveBands_subset_bandStrata g s₀ hc.regionBetween_mem_consecutiveBands,
        graphOn_mem_bandStrata g s₀ k₂]
    · rw [closedRegionBetween_eq_union fun x hx ↦ (hc.lt x hx).le, sUnion_insert, sUnion_insert,
        sUnion_singleton, union_assoc]

end Face

end TauCeti
