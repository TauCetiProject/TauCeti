/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.InvarianceOfDomain
public import TauCeti.Geometry.RealAlgebraic.CAD.Existence
import TauCeti.Topology.LocallyClosed

/-!
# Dimension of semialgebraic sets

The dimension `TauCeti.semialgebraicDim s` of a subset `s` of `ℝ ^ n` is the supremum of the `d`
such that `s` contains a nonempty subset homeomorphic to an open subset of `ℝ ^ d`; the empty set
has dimension `⊥`. By invariance of domain this is at most `n`
(`TauCeti.semialgebraicDim_le`), and a nonempty set which is itself homeomorphic to an open
subset of `ℝ ^ d` has dimension exactly `d` (`TauCeti.semialgebraicDim_eq_of_isOpenEmbedding`).

The definition is intrinsic, and the point is that for semialgebraic sets it is computed by any
cylindrical algebraic decomposition. Every cell of a CAD is locally closed
(`TauCeti.IsCAD.isLocallyClosed`) and homeomorphic to an open subset of some `ℝ ^ d`
(`TauCeti.IsCAD.exists_injective_isOpenEmbedding_comp`): a section over a base cell is
homeomorphic to the base, and a sector over it is an open subset of the cylinder over the base.
The dimension of a finite union of locally closed sets is the largest of their dimensions
(`TauCeti.semialgebraicDim_iUnion_of_isLocallyClosed`), because a nonempty space covered by
finitely many locally closed sets has one of them with nonempty interior. Hence the dimension of
a union of cells of a CAD is the largest dimension of those cells
(`TauCeti.IsCAD.semialgebraicDim_eq_iSup`). In particular the maximal dimension of the cells of a
CAD contained in a semialgebraic set does not depend on the decomposition. The dimension of the
union of a locally closed set with any set is the larger of their dimensions
(`IsLocallyClosed.semialgebraicDim_union`), and a semialgebraic set is a finite union of locally
closed CAD cells, so the dimension of the union of a semialgebraic set and any set is the larger of
their dimensions (`TauCeti.IsSemialgebraic.semialgebraicDim_union`).

## Main declarations

* `TauCeti.semialgebraicDim`: the dimension of a subset of `ℝ ^ n`.
* `TauCeti.semialgebraicDim_le`, `TauCeti.semialgebraicDim_eq_bot_iff`,
  `TauCeti.semialgebraicDim_mono`: the dimension of a nonempty set lies between `0` and `n`, and
  is monotone.
* `TauCeti.semialgebraicDim_le_of_isEmbedding`, `TauCeti.semialgebraicDim_image_of_isEmbedding`:
  dimension is monotone along embeddings, and invariant under embeddings of the ambient space.
* `TauCeti.semialgebraicDim_eq_of_isOpenEmbedding`, `IsOpen.semialgebraicDim_eq`: a nonempty open
  subset of `ℝ ^ d` has dimension `d`.
* `TauCeti.semialgebraicDim_iUnion_of_isLocallyClosed`: dimension of finite unions of locally
  closed sets.
* `TauCeti.IsCAD.exists_semialgebraicDim_eq`: each cell of a CAD has a natural dimension `d` and
  is homeomorphic to an open subset of `ℝ ^ d`.
* `TauCeti.IsCAD.semialgebraicDim_eq_iSup`: the dimension of a union of cells of a CAD is the
  largest dimension of these cells.
* `IsLocallyClosed.semialgebraicDim_union`: the dimension of the union of a locally
  closed set and any set.
* `TauCeti.IsSemialgebraic.semialgebraicDim_union`: the dimension of the union of a semialgebraic
  set and any set.
* `TauCeti.exists_isOpenEmbedding_semialgebraicDim_eq`: a nonempty set contains a locally closed
  Euclidean cell of the same dimension.

## References

* J. Bochnak, M. Coste, M.-F. Roy, *Real Algebraic Geometry*, Ergebnisse der Mathematik und ihrer
  Grenzgebiete 36, Springer, 1998, Section 2.8.
-/

public section

open Module Set Topology

namespace TauCeti

variable {n : ℕ}

/-- The **dimension** of a subset `s` of `ℝ ^ n`: the supremum of the natural numbers `d` such
that `s` contains a nonempty subset homeomorphic to an open subset of `ℝ ^ d`. The empty set has
dimension `⊥`, and every other set has a natural number dimension at most `n`
(`TauCeti.semialgebraicDim_le`). For a semialgebraic set this is the largest dimension of the
cells of any cylindrical algebraic decomposition adapted to it
(`TauCeti.IsCAD.semialgebraicDim_eq_iSup`). -/
noncomputable def semialgebraicDim (s : Set (Fin n → ℝ)) : WithBot ℕ∞ :=
  ⨆ (t : Set (Fin n → ℝ)) (_ : t ⊆ s) (_ : t.Nonempty) (d : ℕ)
    (_ : ∃ f : t → (Fin d → ℝ), IsOpenEmbedding f), (d : WithBot ℕ∞)

variable {s t : Set (Fin n → ℝ)}

/-- An upper bound for the dimension is a bound on the dimensions `d` of the nonempty subsets
homeomorphic to open subsets of `ℝ ^ d`. -/
theorem semialgebraicDim_le_iff {k : WithBot ℕ∞} :
    semialgebraicDim s ≤ k ↔ ∀ t ⊆ s, t.Nonempty → ∀ (d : ℕ) (f : t → (Fin d → ℝ)),
      IsOpenEmbedding f → (d : WithBot ℕ∞) ≤ k := by
  simp only [semialgebraicDim, iSup_le_iff]
  exact forall₂_congr fun _ _ ↦ forall_congr' fun _ ↦ forall_congr' fun _ ↦
    ⟨fun h f hf ↦ h ⟨f, hf⟩, fun h ⟨f, hf⟩ ↦ h f hf⟩

/-- If a nonempty space `X` embeds into `s` and has an open embedding into `ℝ ^ d`, then `s` has
dimension at least `d`. -/
theorem le_semialgebraicDim {X : Type*} [TopologicalSpace X] [Nonempty X]
    {g : X → Fin n → ℝ} (hg : IsEmbedding g) (hgs : range g ⊆ s) {d : ℕ}
    {f : X → Fin d → ℝ} (hf : IsOpenEmbedding f) : (d : WithBot ℕ∞) ≤ semialgebraicDim s :=
  le_iSup₂_of_le (range g) hgs <| le_iSup_of_le (range_nonempty g) <| le_iSup₂_of_le d
    ⟨f ∘ hg.toHomeomorph.symm, hf.comp hg.toHomeomorph.symm.isOpenEmbedding⟩ le_rfl

/-- Dimension is monotone. -/
theorem semialgebraicDim_mono (h : s ⊆ t) : semialgebraicDim s ≤ semialgebraicDim t :=
  semialgebraicDim_le_iff.2 fun u hu hne d f hf ↦
    have := hne.to_subtype
    le_semialgebraicDim .subtypeVal (by simpa using hu.trans h) hf

/-- Dimension is monotone along embeddings: a set which embeds into `s` has dimension at most that
of `s`. -/
theorem semialgebraicDim_le_of_isEmbedding {m : ℕ} {t : Set (Fin m → ℝ)} {g : t → Fin n → ℝ}
    (hg : IsEmbedding g) (hgs : range g ⊆ s) : semialgebraicDim t ≤ semialgebraicDim s :=
  semialgebraicDim_le_iff.2 fun _ hu hne _ _ hf ↦
    have := hne.to_subtype
    le_semialgebraicDim (hg.comp (IsEmbedding.inclusion hu))
      ((range_comp_subset_range _ _).trans hgs) hf

/-- Dimension is invariant under embeddings of the ambient space. -/
@[simp]
theorem semialgebraicDim_image_of_isEmbedding {m : ℕ} {f : (Fin n → ℝ) → Fin m → ℝ}
    (hf : IsEmbedding f) (s : Set (Fin n → ℝ)) :
    semialgebraicDim (f '' s) = semialgebraicDim s := by
  refine le_antisymm ?_ <| semialgebraicDim_le_of_isEmbedding (hf.comp .subtypeVal) <| by
    rintro _ ⟨x, rfl⟩
    exact mem_image_of_mem f x.2
  -- `f '' s` embeds back into `s` through the inverse of `f` on its range.
  let e := hf.toHomeomorph
  refine semialgebraicDim_le_of_isEmbedding
    (g := fun y : f '' s ↦ e.symm ⟨y, image_subset_range f s y.2⟩)
    (e.symm.isEmbedding.comp (IsEmbedding.inclusion (image_subset_range f s))) ?_
  rintro _ ⟨⟨_, x, hx, rfl⟩, rfl⟩
  simpa [e] using hx

/-- **Invariance of dimension.** A subset of `ℝ ^ n` has dimension at most `n`. -/
theorem semialgebraicDim_le (s : Set (Fin n → ℝ)) : semialgebraicDim s ≤ n :=
  semialgebraicDim_le_iff.2 fun t _ hne d f hf ↦ by
    have := hne.to_subtype
    have h := hf.finrank_le_of_isEmbedding (E := Fin n → ℝ) .subtypeVal
    simp only [finrank_fin_fun] at h
    exact_mod_cast h

/-- The dimension of a set is `⊥` exactly when the set is empty. -/
@[simp]
theorem semialgebraicDim_eq_bot_iff : semialgebraicDim s = ⊥ ↔ s = ∅ := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · -- A point of `s` is homeomorphic to `ℝ ^ 0`.
    by_contra hs
    obtain ⟨x, hx⟩ := nonempty_iff_ne_empty.2 hs
    have h0 := le_semialgebraicDim (X := ({x} : Set (Fin n → ℝ))) .subtypeVal
      (by simpa using hx) (Homeomorph.homeomorphOfUnique _ (Fin 0 → ℝ)).isOpenEmbedding
    simp [h] at h0
  · subst h
    exact le_bot_iff.1 <| semialgebraicDim_le_iff.2 fun t ht hne ↦
      absurd (subset_empty_iff.1 ht) hne.ne_empty

/-- The empty set has dimension `⊥`. -/
@[simp]
theorem semialgebraicDim_empty : semialgebraicDim (∅ : Set (Fin n → ℝ)) = ⊥ :=
  semialgebraicDim_eq_bot_iff.2 rfl

/-- A nonempty set which is homeomorphic to an open subset of `ℝ ^ d` has dimension `d`. -/
theorem semialgebraicDim_eq_of_isOpenEmbedding (hs : s.Nonempty) {d : ℕ}
    {f : s → Fin d → ℝ} (hf : IsOpenEmbedding f) : semialgebraicDim s = d := by
  have := hs.to_subtype
  refine le_antisymm (semialgebraicDim_le_iff.2 fun t ht hne e g hg ↦ ?_)
    (le_semialgebraicDim .subtypeVal (by simp) hf)
  -- The subset `t` embeds into `ℝ ^ d` through `s`.
  have := hne.to_subtype
  have h := hg.finrank_le_of_isEmbedding (E := Fin d → ℝ)
    (hf.isEmbedding.comp (IsEmbedding.inclusion ht))
  simp only [finrank_fin_fun] at h
  exact_mod_cast h

/-- A nonempty open subset of `ℝ ^ n` has dimension `n`. -/
theorem _root_.IsOpen.semialgebraicDim_eq (hs : IsOpen s) (hne : s.Nonempty) :
    semialgebraicDim s = n :=
  semialgebraicDim_eq_of_isOpenEmbedding hne hs.isOpenEmbedding_subtypeVal

/-- The whole space `ℝ ^ n` has dimension `n`. -/
@[simp]
theorem semialgebraicDim_univ : semialgebraicDim (univ : Set (Fin n → ℝ)) = n :=
  isOpen_univ.semialgebraicDim_eq univ_nonempty

/-- If `m ⊆ ℝ ^ n` has an open embedding into `ℝ ^ d`, then every nonempty open subset of `m`
that lies in `u` shows that `u` has dimension at least `d`. -/
private theorem le_semialgebraicDim_of_isOpen {u m : Set (Fin n → ℝ)} {d : ℕ} {f : m → Fin d → ℝ}
    (hf : IsOpenEmbedding f) {V : Set m} (hV : IsOpen V) (hne : V.Nonempty)
    (hVu : Subtype.val '' V ⊆ u) : (d : WithBot ℕ∞) ≤ semialgebraicDim u := by
  have := hne.to_subtype
  refine le_semialgebraicDim (X := V) (IsEmbedding.subtypeVal.comp IsEmbedding.subtypeVal) ?_
    (hf.comp hV.isOpenEmbedding_subtypeVal)
  rintro _ ⟨y, rfl⟩
  exact hVu ⟨y, y.2, rfl⟩

/-- **Dimension of finite unions.** The dimension of a finite union of locally closed subsets of
`ℝ ^ n` is the largest of their dimensions. -/
theorem semialgebraicDim_iUnion_of_isLocallyClosed {ι : Type*} [Finite ι]
    {u : ι → Set (Fin n → ℝ)} (hu : ∀ i, IsLocallyClosed (u i)) :
    semialgebraicDim (⋃ i, u i) = ⨆ i, semialgebraicDim (u i) := by
  refine le_antisymm (semialgebraicDim_le_iff.2 fun t ht hne d f hf ↦ ?_)
    (iSup_le fun i ↦ semialgebraicDim_mono (subset_iUnion u i))
  -- The traces of the `u i` on `t` are locally closed and cover `t`, so one of them has an
  -- interior point `x` in `t`. Near `x`, the set `t` lies in that `u i`.
  have := hne.to_subtype
  obtain ⟨i, x, hx⟩ := nonempty_interior_of_iUnion_of_isLocallyClosed
    (fun i ↦ (hu i).preimage continuous_subtype_val)
    (eq_univ_of_forall fun x ↦ by simpa using ht x.2)
  exact le_iSup_of_le i <| le_semialgebraicDim_of_isOpen hf isOpen_interior ⟨x, hx⟩
    (image_subset_iff.2 interior_subset)

/-- **Dimension of finite unions.** The dimension of the union of a finite family of locally
closed subsets of `ℝ ^ n` is the largest of their dimensions. -/
theorem semialgebraicDim_sUnion_of_isLocallyClosed {𝒮 : Set (Set (Fin n → ℝ))} (h𝒮 : 𝒮.Finite)
    (hl : ∀ u ∈ 𝒮, IsLocallyClosed u) :
    semialgebraicDim (⋃₀ 𝒮) = ⨆ u ∈ 𝒮, semialgebraicDim u := by
  have := h𝒮.to_subtype
  rw [sUnion_eq_iUnion, semialgebraicDim_iUnion_of_isLocallyClosed
    (u := fun u : 𝒮 ↦ (u : Set (Fin n → ℝ))) fun u ↦ hl u.1 u.2, iSup_subtype']

/-! ### Cells of cylindrical algebraic decompositions -/

namespace IsCAD

variable {𝒞 : Set (Set (Fin n → ℝ))} {E : Set (Fin n → ℝ)}

/-- Every cell `E` of a cylindrical algebraic decomposition has a natural number dimension `d`,
and is homeomorphic to an open subset of `ℝ ^ d`. -/
theorem exists_semialgebraicDim_eq (h : IsCAD n 𝒞) (hE : E ∈ 𝒞) :
    ∃ d : ℕ, semialgebraicDim E = d ∧ ∃ f : E → Fin d → ℝ, IsOpenEmbedding f := by
  obtain ⟨d, _, _, hf⟩ := h.exists_injective_isOpenEmbedding_comp hE
  exact ⟨d, semialgebraicDim_eq_of_isOpenEmbedding (h.isConnected hE).nonempty hf, _, hf⟩

/-- **Dimension from cells.** If a set `s` contains or misses each cell of a cylindrical algebraic
decomposition, its dimension is the largest dimension of the cells it contains. In particular this
maximum does not depend on the decomposition. -/
theorem semialgebraicDim_eq_iSup (h : IsCAD n 𝒞) {s : Set (Fin n → ℝ)}
    (hs : ∀ E ∈ 𝒞, E ⊆ s ∨ Disjoint E s) :
    semialgebraicDim s = ⨆ E ∈ {E ∈ 𝒞 | E ⊆ s}, semialgebraicDim E := by
  conv_lhs => rw [← h.sUnion_sep_subset hs]
  exact semialgebraicDim_sUnion_of_isLocallyClosed (h.finite.subset (sep_subset _ _))
    fun E hE ↦ h.isLocallyClosed hE.1

end IsCAD

/-- A semialgebraic subset of `ℝ ^ n` is the union of finitely many locally closed sets, each
homeomorphic to an open subset of some `ℝ ^ d`: the cells of an adapted cylindrical algebraic
decomposition that it contains. -/
theorem IsSemialgebraic.exists_finite_sUnion_eq (hs : IsSemialgebraic s) :
    ∃ 𝒮 : Set (Set (Fin n → ℝ)), 𝒮.Finite ∧ ⋃₀ 𝒮 = s ∧ ∀ u ∈ 𝒮, IsLocallyClosed u ∧
      ∃ d, ∃ f : u → Fin d → ℝ, IsOpenEmbedding f := by
  obtain ⟨𝒞, h𝒞, hsub⟩ := hs.exists_isCAD_subset_or_disjoint
  exact ⟨{E ∈ 𝒞 | E ⊆ s}, h𝒞.finite.subset (sep_subset _ _), h𝒞.sUnion_sep_subset hsub,
    fun E hE ↦ ⟨h𝒞.isLocallyClosed hE.1,
      let ⟨d, _, _, hf⟩ := h𝒞.exists_injective_isOpenEmbedding_comp hE.1; ⟨d, _, hf⟩⟩⟩

/-- **Dimension of unions with a locally closed set.** The dimension of the union of a locally
closed set and any other set is the larger of their dimensions. -/
theorem _root_.IsLocallyClosed.semialgebraicDim_union (hs : IsLocallyClosed s)
    (t : Set (Fin n → ℝ)) :
    semialgebraicDim (s ∪ t) = max (semialgebraicDim s) (semialgebraicDim t) := by
  refine le_antisymm (semialgebraicDim_le_iff.2 fun m hm hne d f hf ↦ ?_)
    (max_le (semialgebraicDim_mono subset_union_left) (semialgebraicDim_mono subset_union_right))
  have := hne.to_subtype
  by_cases hint : (interior ((Subtype.val : m → Fin n → ℝ) ⁻¹' s)).Nonempty
  · -- `s` has an interior point in `m`, and near it `m` lies in `s`.
    obtain ⟨x, hx⟩ := hint
    exact le_max_of_le_left <| le_semialgebraicDim_of_isOpen hf isOpen_interior ⟨x, hx⟩
      (image_subset_iff.2 interior_subset)
  · -- Otherwise `s` is nowhere dense in `m`, so an open part of `m` lies in `t`.
    have hK : IsNowhereDense ((Subtype.val : m → Fin n → ℝ) ⁻¹' s) :=
      (hs.preimage continuous_subtype_val).isNowhereDense_iff.2 (not_nonempty_iff_eq_empty.1 hint)
    let Y : Set m := (closure ((Subtype.val : m → Fin n → ℝ) ⁻¹' s))ᶜ
    have hY : Y.Nonempty := by
      by_contra h
      rw [not_nonempty_iff_eq_empty, compl_empty_iff] at h
      rw [IsNowhereDense, h, interior_univ] at hK
      exact univ_nonempty.ne_empty hK
    exact le_max_of_le_right <| le_semialgebraicDim_of_isOpen hf isClosed_closure.isOpen_compl hY
      (by
        rintro _ ⟨y, hy, rfl⟩
        exact (hm y.2).resolve_left fun h ↦ hy (subset_closure h))

/-- **Dimension of unions.** The dimension of the union of a semialgebraic set and any other set is
the larger of their dimensions. -/
theorem IsSemialgebraic.semialgebraicDim_union (hs : IsSemialgebraic s) (t : Set (Fin n → ℝ)) :
    semialgebraicDim (s ∪ t) = max (semialgebraicDim s) (semialgebraicDim t) := by
  obtain ⟨𝒮, h𝒮, rfl, hl⟩ := hs.exists_finite_sUnion_eq
  clear hs
  induction 𝒮, h𝒮 using Set.Finite.induction_on with
  | empty => simp
  | @insert u 𝒮 _ _ ih =>
    have hu : IsLocallyClosed u := (hl u (mem_insert _ _)).1
    have ih := ih fun v hv ↦ hl v (mem_insert_of_mem _ hv)
    rw [sUnion_insert, union_assoc, hu.semialgebraicDim_union (⋃₀ 𝒮 ∪ t),
      hu.semialgebraicDim_union (⋃₀ 𝒮), ih, max_assoc]

/-- A nonempty set contains a locally closed subset of the same dimension which is homeomorphic to
an open subset of a Euclidean space. -/
theorem exists_isOpenEmbedding_semialgebraicDim_eq (hne : s.Nonempty) :
    ∃ u ⊆ s, IsLocallyClosed u ∧ u.Nonempty ∧ ∃ d : ℕ,
      semialgebraicDim s = d ∧ ∃ f : u → Fin d → ℝ, IsOpenEmbedding f := by
  -- The dimensions `d` of the Euclidean pieces of `s` are bounded by `n`, so one is largest.
  let D : Set ℕ := {d | ∃ u ⊆ s, u.Nonempty ∧ ∃ f : u → Fin d → ℝ, IsOpenEmbedding f}
  have hD : D.Nonempty := by
    obtain ⟨x, hx⟩ := hne
    exact ⟨0, {x}, by simpa using hx, singleton_nonempty x, _,
      (Homeomorph.homeomorphOfUnique _ (Fin 0 → ℝ)).isOpenEmbedding⟩
  have hbdd : BddAbove D := ⟨n, fun d ⟨u, hu, hune, f, hf⟩ ↦ by
    have := hune.to_subtype
    have h := le_semialgebraicDim (X := u) (n := n) (s := s) .subtypeVal (by simpa using hu) hf
    exact_mod_cast h.trans (semialgebraicDim_le s)⟩
  obtain ⟨u, hu, hune, f, hf⟩ := Nat.sSup_mem hD hbdd
  have hdim : semialgebraicDim s = sSup D := by
    have := hune.to_subtype
    refine le_antisymm (semialgebraicDim_le_iff.2 fun t ht hne' d g hg ↦ ?_)
      (le_semialgebraicDim .subtypeVal (by simpa using hu) hf)
    exact_mod_cast le_csSup hbdd ⟨t, ht, hne', g, hg⟩
  refine ⟨u, hu, ?_, hune, sSup D, hdim, f, hf⟩
  -- `u` is locally compact, being open in a Euclidean space, hence locally closed.
  have := hf.locallyCompactSpace
  exact isLocallyClosed_of_locallyCompactSpace

end TauCeti
