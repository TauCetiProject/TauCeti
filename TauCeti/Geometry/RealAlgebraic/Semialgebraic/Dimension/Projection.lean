/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.RealAlgebraic.Semialgebraic.Dimension.Basic
public import TauCeti.Geometry.RealAlgebraic.Semialgebraic.Image

/-!
# Dimension of semialgebraic sets under coordinate projections

A change of coordinates `x ↦ x ∘ ι`, for any `ι : Fin m → Fin n` and in particular for a
coordinate projection, does not increase the dimension of a semialgebraic subset of `ℝ ^ n`
(`TauCeti.IsSemialgebraic.semialgebraicDim_image_comp_le`). For the projection `Fin.tail`
forgetting coordinate `0` this is read off a cylindrical algebraic decomposition adapted to the
set: each of its cells contains the graph of a continuous function over the projected cell, so the
projected cell embeds into the cell. When `ι` is surjective, `x ↦ x ∘ ι` is an embedding of the
ambient space and preserves dimension; otherwise it is a coordinate permutation, followed by
forgetting coordinate `0`, followed by a change of coordinates with one coordinate fewer. Without
semialgebraicity the bound fails: the graph of the indicator function of the rationals contains
no arc, so it has dimension `0`, but it projects onto `ℝ`.

Conversely, every cell of such a decomposition is mapped homeomorphically onto an open subset of
`ℝ ^ d` by a projection onto `d` of its coordinates. Together these give a characterization of
dimension by coordinate projections (`TauCeti.IsSemialgebraic.natCast_le_semialgebraicDim_iff`):
a semialgebraic set has dimension at least `d` exactly when some projection onto `d` distinct
coordinates maps it onto a set with nonempty interior.

## Main declarations

* `TauCeti.semialgebraicDim_image_comp_of_surjective`: changes of coordinates `x ↦ x ∘ ι` with
  `ι` surjective, such as coordinate permutations, preserve dimension.
* `TauCeti.IsSemialgebraic.semialgebraicDim_image_tail_le`,
  `TauCeti.IsSemialgebraic.semialgebraicDim_image_comp_le`: coordinate projections do not
  increase the dimension of semialgebraic sets.
* `TauCeti.IsSemialgebraic.natCast_le_semialgebraicDim_iff`: dimension by coordinate
  projections with nonempty interior.

## References

* J. Bochnak, M. Coste, M.-F. Roy, *Real Algebraic Geometry*, Ergebnisse der Mathematik und ihrer
  Grenzgebiete 36, Springer, 1998, Section 2.8.
-/

public section

open Function Set Topology

namespace TauCeti

variable {m n : ℕ}

/-- A change of coordinates `x ↦ x ∘ ι` with `ι` surjective, such as a coordinate permutation,
does not change the dimension: it embeds `ℝ ^ n` into `ℝ ^ m`. -/
@[simp]
theorem semialgebraicDim_image_comp_of_surjective {ι : Fin m → Fin n} (hι : Surjective ι)
    (s : Set (Fin n → ℝ)) : semialgebraicDim ((fun x ↦ x ∘ ι) '' s) = semialgebraicDim s :=
  semialgebraicDim_image_of_isEmbedding (hι.isEmbedding_comp ι) s

/-- **Projection does not increase dimension.** Forgetting coordinate `0` does not increase the
dimension of a semialgebraic set. -/
theorem IsSemialgebraic.semialgebraicDim_image_tail_le {s : Set (Fin (n + 1) → ℝ)}
    (hs : IsSemialgebraic s) : semialgebraicDim (Fin.tail '' s) ≤ semialgebraicDim s := by
  obtain ⟨𝒞, h𝒞, hsub⟩ := hs.exists_isCAD_subset_or_disjoint
  -- The projection of `s` is the union of the projections of the cells of `𝒞` contained in `s`,
  -- which are locally closed cells of the projected decomposition.
  conv_lhs => rw [← h𝒞.sUnion_sep_subset hsub, image_sUnion]
  rw [semialgebraicDim_sUnion_of_isLocallyClosed ((h𝒞.finite.subset (sep_subset _ _)).image _)
    (by rintro _ ⟨E, hE, rfl⟩; exact h𝒞.image_tail.isLocallyClosed (mem_image_of_mem _ hE.1))]
  refine iSup₂_le ?_
  rintro _ ⟨E, hE, rfl⟩
  -- The cell `E` contains the graph of a continuous function on `Fin.tail '' E`, and this graph
  -- is homeomorphic to `Fin.tail '' E`.
  obtain ⟨g, hg, hgE⟩ := h𝒞.exists_continuous_cons_mem hE.1
  have htail : (Fin.tail ∘ fun x : Fin.tail '' E ↦ (Fin.cons (g x) x.1 : Fin (n + 1) → ℝ)) =
      Subtype.val := by
    funext x
    simp
  refine (semialgebraicDim_le_of_isEmbedding
    (IsEmbedding.of_comp (by fun_prop) (continuous_pi fun i : Fin n ↦ continuous_apply i.succ)
      (htail ▸ IsEmbedding.subtypeVal)) ?_).trans (semialgebraicDim_mono hE.2)
  rintro _ ⟨x, rfl⟩
  exact hgE x

/-- **Coordinate projections do not increase dimension.** For every `ι : Fin m → Fin n`, the image
of a semialgebraic set under `x ↦ x ∘ ι` has at most its dimension. -/
theorem IsSemialgebraic.semialgebraicDim_image_comp_le {s : Set (Fin n → ℝ)}
    (hs : IsSemialgebraic s) (ι : Fin m → Fin n) :
    semialgebraicDim ((fun x ↦ x ∘ ι) '' s) ≤ semialgebraicDim s := by
  induction n generalizing m with
  | zero => exact (semialgebraicDim_image_comp_of_surjective (·.elim0) s).le
  | succ n ih =>
    by_cases hsurj : Surjective ι
    · exact (semialgebraicDim_image_comp_of_surjective hsurj s).le
    -- Otherwise swap coordinate `0` with a coordinate `j` that `ι` misses, and forget it.
    obtain ⟨j, hj⟩ := not_forall.1 hsurj
    let σ := Equiv.swap (0 : Fin (n + 1)) j
    have hne (i : Fin m) : σ (ι i) ≠ 0 := fun h ↦
      hj ⟨i, by simpa [σ, Equiv.swap_apply_eq_iff] using h⟩
    let ι' : Fin m → Fin n := fun i ↦ (σ (ι i)).pred (hne i)
    have hσ : IsSemialgebraic ((fun x ↦ x ∘ σ) '' s) := hs.image_comp σ
    have heq : (fun x ↦ x ∘ ι) '' s = (fun x ↦ x ∘ ι') '' (Fin.tail '' ((fun x ↦ x ∘ σ) '' s)) := by
      simp only [image_image]
      refine image_congr fun x _ ↦ funext fun i ↦ ?_
      simp [ι', Fin.tail, σ]
    rw [heq]
    calc _ ≤ semialgebraicDim (Fin.tail '' ((fun x ↦ x ∘ σ) '' s)) :=
          ih (HasSemialgebraicProjections.isSemialgebraic_image_tail hσ) ι'
      _ ≤ semialgebraicDim ((fun x ↦ x ∘ σ) '' s) := hσ.semialgebraicDim_image_tail_le
      _ = semialgebraicDim s := semialgebraicDim_image_comp_of_surjective σ.surjective s

/-- **Dimension by coordinate projections.** A semialgebraic subset of `ℝ ^ n` has dimension at
least `d` exactly when its projection `x ↦ x ∘ ι` onto some `d` distinct coordinates has nonempty
interior in `ℝ ^ d`. -/
theorem IsSemialgebraic.natCast_le_semialgebraicDim_iff {s : Set (Fin n → ℝ)}
    (hs : IsSemialgebraic s) {d : ℕ} :
    (d : WithBot ℕ∞) ≤ semialgebraicDim s ↔
      ∃ ι : Fin d → Fin n, Injective ι ∧ (interior ((fun x ↦ x ∘ ι) '' s)).Nonempty := by
  refine ⟨fun h ↦ ?_, fun ⟨ι, _, hint⟩ ↦ ?_⟩
  · -- A cell of maximal dimension among those of an adapted decomposition contained in `s` is
    -- mapped onto an open subset of `ℝ ^ d'` by a coordinate projection, where `d ≤ d'`.
    obtain ⟨𝒞, h𝒞, hsub⟩ := hs.exists_isCAD_subset_or_disjoint
    have hne : {E ∈ 𝒞 | E ⊆ s}.Nonempty := by
      refine nonempty_iff_ne_empty.2 fun h0 ↦ ?_
      rw [← h𝒞.sUnion_sep_subset hsub, h0, sUnion_empty, semialgebraicDim_empty] at h
      exact (WithBot.bot_lt_coe _).not_ge h
    obtain ⟨E, hE, hmax⟩ :=
      exists_max_image _ semialgebraicDim (h𝒞.finite.subset (sep_subset _ _)) hne
    obtain ⟨d', ι, hι, hf⟩ := h𝒞.exists_injective_isOpenEmbedding_comp hE.1
    obtain ⟨x, hx⟩ := (h𝒞.isConnected hE.1).nonempty
    have hdd' : d ≤ d' := by
      rw [h𝒞.semialgebraicDim_eq_iSup hsub] at h
      exact_mod_cast semialgebraicDim_eq_of_isOpenEmbedding ⟨x, hx⟩ hf ▸ h.trans (iSup₂_le hmax)
    -- Keeping the first `d` of these `d'` coordinates is an open map.
    let p := LinearMap.funLeft ℝ ℝ (Fin.castLE hdd')
    have hp : IsOpenMap p := p.isOpenMap_of_finiteDimensional <|
      LinearMap.funLeft_surjective_of_injective _ _ _ (Fin.castLE_injective hdd')
    refine ⟨ι ∘ Fin.castLE hdd', hι.comp (Fin.castLE_injective hdd'), p (x ∘ ι),
      interior_mono ?_ ((hp _ hf.isOpen_range).interior_eq.symm ▸
        mem_image_of_mem p (mem_range_self (⟨x, hx⟩ : E)))⟩
    rintro _ ⟨_, ⟨y, rfl⟩, rfl⟩
    exact ⟨y.1, hE.2 y.2, rfl⟩
  · -- The projection contains a nonempty open subset of `ℝ ^ d`.
    calc (d : WithBot ℕ∞) = semialgebraicDim (interior ((fun x ↦ x ∘ ι) '' s)) :=
          (isOpen_interior.semialgebraicDim_eq hint).symm
      _ ≤ semialgebraicDim ((fun x ↦ x ∘ ι) '' s) := semialgebraicDim_mono interior_subset
      _ ≤ semialgebraicDim s := hs.semialgebraicDim_image_comp_le ι

end TauCeti
