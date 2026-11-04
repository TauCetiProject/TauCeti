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
CAD contained in a semialgebraic set does not depend on the decomposition. Consequently the
dimension of a union of two semialgebraic sets is the larger of their dimensions
(`TauCeti.IsSemialgebraic.semialgebraicDim_union`).

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
* `TauCeti.IsSemialgebraic.semialgebraicDim_union`: the dimension of a union of two semialgebraic
  sets.
* `TauCeti.IsSemialgebraic.exists_isOpenEmbedding_semialgebraicDim_eq`: a nonempty semialgebraic
  set contains a locally closed Euclidean cell of the same dimension.

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
  have : Nonempty (interior ((Subtype.val : t → Fin n → ℝ) ⁻¹' u i)) := ⟨⟨x, hx⟩⟩
  refine le_iSup_of_le i <| le_semialgebraicDim
    (X := interior ((Subtype.val : t → Fin n → ℝ) ⁻¹' u i))
    (IsEmbedding.subtypeVal.comp IsEmbedding.subtypeVal) ?_
    (hf.comp isOpen_interior.isOpenEmbedding_subtypeVal)
  rintro _ ⟨y, rfl⟩
  exact interior_subset (s := (Subtype.val : t → Fin n → ℝ) ⁻¹' u i) y.2

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

/-- **Dimension of unions.** The dimension of the union of two semialgebraic sets is the larger of
their dimensions. -/
theorem IsSemialgebraic.semialgebraicDim_union (hs : IsSemialgebraic s)
    (ht : IsSemialgebraic t) :
    semialgebraicDim (s ∪ t) = max (semialgebraicDim s) (semialgebraicDim t) := by
  obtain ⟨𝒮, h𝒮, rfl, hl⟩ := hs.exists_finite_sUnion_eq
  obtain ⟨𝒯, h𝒯, rfl, hl'⟩ := ht.exists_finite_sUnion_eq
  rw [← sUnion_union, semialgebraicDim_sUnion_of_isLocallyClosed (h𝒮.union h𝒯)
      fun u hu ↦ hu.elim (fun hu ↦ (hl u hu).1) fun hu ↦ (hl' u hu).1,
    semialgebraicDim_sUnion_of_isLocallyClosed h𝒮 fun u hu ↦ (hl u hu).1,
    semialgebraicDim_sUnion_of_isLocallyClosed h𝒯 fun u hu ↦ (hl' u hu).1, iSup_union]

/-- A nonempty semialgebraic set contains a locally closed subset of the same dimension
which is homeomorphic to an open subset of a Euclidean space. -/
theorem IsSemialgebraic.exists_isOpenEmbedding_semialgebraicDim_eq
    (hs : IsSemialgebraic s) (hne : s.Nonempty) :
    ∃ u ⊆ s, IsLocallyClosed u ∧ u.Nonempty ∧ ∃ d : ℕ,
      semialgebraicDim s = d ∧ ∃ f : u → Fin d → ℝ, IsOpenEmbedding f := by
  obtain ⟨𝒮, h𝒮, hcover, hl⟩ := hs.exists_finite_sUnion_eq
  have h𝒮ne : 𝒮.Nonempty := by
    obtain ⟨x, hx⟩ := hne
    rw [← hcover, mem_sUnion] at hx
    obtain ⟨u, hu, _⟩ := hx
    exact ⟨u, hu⟩
  have := h𝒮.to_subtype
  have := h𝒮ne.to_subtype
  obtain ⟨u, hu⟩ := Finite.ciSup_mem (fun u : 𝒮 ↦ semialgebraicDim u.val)
  have hdim : semialgebraicDim s = semialgebraicDim u.val := by
    rw [← hcover, semialgebraicDim_sUnion_of_isLocallyClosed h𝒮 (fun u hu ↦ (hl u hu).1)]
    simpa only [iSup_subtype'] using hu.symm
  have hune : u.val.Nonempty := by
    apply nonempty_iff_ne_empty.mpr
    intro he
    have : s = ∅ := semialgebraicDim_eq_bot_iff.mp (by simpa [he] using hdim)
    exact hne.ne_empty this
  obtain ⟨d, f, hf⟩ := (hl u.val u.property).2
  exact ⟨u.val, by rw [← hcover]; exact subset_sUnion_of_mem u.property,
    (hl u.val u.property).1, hune, d,
    hdim.trans (semialgebraicDim_eq_of_isOpenEmbedding hune hf), f, hf⟩

end TauCeti
