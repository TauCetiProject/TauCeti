/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.ZLattice.Covolume
public import TauCeti.Analysis.InnerProductSpace.Projection.Basis
import TauCeti.Algebra.Module.ZLattice.AdaptedBasis
import TauCeti.Algebra.Module.ZLattice.Basic
import TauCeti.Analysis.InnerProductSpace.Gram.Projection

/-!
# Projecting a lattice along a rational subspace

Let `Δ` be a discrete full lattice in a finite-dimensional real inner product space `E` and `W`
a real subspace. The intersection `Δ ∩ W` is recorded as the lattice `ZLattice.comap ℝ Δ W.subtype`
in `W`, and `W` is rational for `Δ` when `Δ ∩ W` spans `W`. In that case `Δ` has a basis whose
first `dim W` vectors form a basis of `Δ ∩ W` (`ZLattice.exists_basis_sum_finrank`), and the
first block of such a basis spans `W` over `ℝ` (`ZLattice.span_range_ofZLatticeBasis_inl`), both
in `TauCeti.Algebra.Module.ZLattice.AdaptedBasis`.

Let `π : E → Wᗮ` be the orthogonal projection. For a basis of `Δ` whose first block spans `W`, the
projections of the second block are a real basis of `Wᗮ` whose `ℤ`-span is the image `π(Δ)`
(`ZLattice.span_orthogonalProjectionInr_ofZLatticeBasis`).
So if `W` is rational for `Δ`, the projection `π(Δ)` is a full lattice in `Wᗮ`, and its covolume is
the covolume of `Δ` divided by the covolume of `Δ ∩ W`, all covolumes being taken for the intrinsic
volumes of `E`, `W` and `Wᗮ` (`ZLattice.covolume_map_orthogonalProjectionOnto`). No unimodularity
or self-duality of `Δ` is assumed.

## Main results

* `ZLattice.span_orthogonalProjectionInr_ofZLatticeBasis`: the projections to `Wᗮ` of the second
  block of a basis of `Δ` whose first block spans `W` span `π(Δ)` over `ℤ`.
* `ZLattice.discreteTopology_map_orthogonalProjectionOnto`,
  `ZLattice.isZLattice_map_orthogonalProjectionOnto`: if `Δ ∩ W` spans `W`, then `π(Δ)` is a
  discrete full lattice in `Wᗮ`.
* `ZLattice.covolume_map_orthogonalProjectionOnto`: if `Δ ∩ W` spans `W`, then
  `covolume π(Δ) = covolume Δ / covolume (Δ ∩ W)`.

## References

* T. Horesh and Y. Karasik, *Equidistribution of primitive lattices in ℝⁿ*, Q. J. Math. 74
  (2023), 1253–1294, Proposition B.4, p. 1290.
-/

public section

open MeasureTheory Module Submodule

namespace ZLattice

section InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {Δ : Submodule ℤ E} [DiscreteTopology Δ] [IsZLattice ℝ Δ] {W : Submodule ℝ E}

/-- **The projected basis spans the projected lattice.** Let `b` be a basis of a full lattice `Δ`
indexed by `ι ⊕ κ` whose first block spans `W`. The `ℤ`-span of the projections to `Wᗮ` of the
second block is the image of `Δ` under the orthogonal projection to `Wᗮ`. -/
theorem span_orthogonalProjectionInr_ofZLatticeBasis {ι κ : Type*} (b : Basis (ι ⊕ κ) ℤ Δ)
    (hW : span ℝ (Set.range (b.ofZLatticeBasis ℝ Δ ∘ Sum.inl)) = W) :
    span ℤ (Set.range ((b.ofZLatticeBasis ℝ Δ).orthogonalProjectionInr hW)) =
      Δ.map ((Wᗮ.orthogonalProjectionOnto : E →ₗ[ℝ] Wᗮ).restrictScalars ℤ) := by
  conv_rhs => rw [← b.ofZLatticeBasis_span ℝ Δ]
  rw [Submodule.map_span, ← Set.range_comp]
  refine le_antisymm (span_mono ?_) (span_le.2 ?_)
  · rintro _ ⟨j, rfl⟩
    exact ⟨.inr j, by simp⟩
  · rintro _ ⟨i | j, rfl⟩
    · have hi : (b (.inl i) : E) ∈ W := by
        rw [← hW, ← b.ofZLatticeBasis_apply ℝ Δ]
        exact subset_span ⟨i, rfl⟩
      simp [orthogonalProjectionOnto_orthogonal_apply_eq_zero hi]
    · exact subset_span ⟨j, by simp⟩

/-- The projection of a full lattice to the orthogonal complement of a rational subspace is the
`ℤ`-span of a real basis of the complement. -/
private theorem exists_basis_span_eq_map_orthogonalProjectionOnto
    (hL : span ℝ (ZLattice.comap ℝ Δ W.subtype : Set W) = ⊤) :
    ∃ (s : ℕ) (q : Basis (Fin s) ℝ Wᗮ),
      span ℤ (Set.range q) =
        Δ.map ((Wᗮ.orthogonalProjectionOnto : E →ₗ[ℝ] Wᗮ).restrictScalars ℤ) := by
  obtain ⟨s, b, c, -, hbc⟩ := exists_basis_sum_finrank Δ hL
  have hW := span_range_ofZLatticeBasis_inl hL b c hbc
  exact ⟨s, _, span_orthogonalProjectionInr_ofZLatticeBasis b hW⟩

/-- If `Δ ∩ W` spans `W`, the projection of `Δ` to `Wᗮ` is discrete. -/
theorem discreteTopology_map_orthogonalProjectionOnto
    (hL : span ℝ (ZLattice.comap ℝ Δ W.subtype : Set W) = ⊤) :
    DiscreteTopology (Δ.map ((Wᗮ.orthogonalProjectionOnto : E →ₗ[ℝ] Wᗮ).restrictScalars ℤ)) := by
  obtain ⟨s, q, hq⟩ := exists_basis_span_eq_map_orthogonalProjectionOnto hL
  rw [← hq]
  infer_instance

/-- If `Δ ∩ W` spans `W`, the projection of `Δ` to `Wᗮ` spans `Wᗮ`. Its discreteness, required to
state this, is `ZLattice.discreteTopology_map_orthogonalProjectionOnto`. -/
theorem isZLattice_map_orthogonalProjectionOnto
    (hL : span ℝ (ZLattice.comap ℝ Δ W.subtype : Set W) = ⊤)
    [DiscreteTopology (Δ.map ((Wᗮ.orthogonalProjectionOnto : E →ₗ[ℝ] Wᗮ).restrictScalars ℤ))] :
    IsZLattice ℝ (Δ.map ((Wᗮ.orthogonalProjectionOnto : E →ₗ[ℝ] Wᗮ).restrictScalars ℤ)) := by
  obtain ⟨s, q, hq⟩ := exists_basis_span_eq_map_orthogonalProjectionOnto hL
  exact ⟨hq ▸ ZSpan.span_top q⟩

variable [MeasurableSpace E] [BorelSpace E]

/-- **The covolume of a projected lattice.** If the intersection of a full lattice `Δ` with a real
subspace `W` spans `W`, the projection of `Δ` to `Wᗮ` has covolume `covolume Δ / covolume (Δ ∩ W)`,
each covolume being taken for the volume of the inner product of `E`, `W` or `Wᗮ`. -/
theorem covolume_map_orthogonalProjectionOnto
    (hL : span ℝ (ZLattice.comap ℝ Δ W.subtype : Set W) = ⊤) :
    covolume (Δ.map ((Wᗮ.orthogonalProjectionOnto : E →ₗ[ℝ] Wᗮ).restrictScalars ℤ)) =
      covolume Δ / covolume (ZLattice.comap ℝ Δ W.subtype) := by
  have : IsZLattice ℝ (ZLattice.comap ℝ Δ W.subtype) := ⟨hL⟩
  obtain ⟨s, b, c, -, hbc⟩ := exists_basis_sum_finrank Δ hL
  have hW := span_range_ofZLatticeBasis_inl hL b c hbc
  set q := (b.ofZLatticeBasis ℝ Δ).orthogonalProjectionInr hW
  have hq := span_orthogonalProjectionInr_ofZLatticeBasis b hW
  -- The squared covolumes are Gram determinants, and the Gram determinant of `b` splits.
  have hgram : (Matrix.gram ℝ fun x ↦ (b x : E)).det =
      (Matrix.gram ℝ fun i ↦ ((c i : W) : E)).det *
        (Matrix.gram ℝ fun j ↦ ((q j : Wᗮ) : E)).det := by
    have hsplit : (fun x ↦ (b x : E)) =
        Sum.elim (fun i ↦ (b (.inl i) : E)) (fun j ↦ (b (.inr j) : E)) := by
      ext (i | j) <;> simp
    rw [hsplit, Matrix.det_gram_sumElim_eq_mul_det_gram_starProjection _ _
      (by simpa [Function.comp_def] using hW)]
    simp [q, hbc, coe_orthogonalProjectionOnto_apply]
  have hsq : covolume Δ ^ 2 = (covolume (ZLattice.comap ℝ Δ W.subtype) *
      covolume (Δ.map ((Wᗮ.orthogonalProjectionOnto : E →ₗ[ℝ] Wᗮ).restrictScalars ℤ))) ^ 2 := by
    rw [mul_pow, covolume_sq_eq_det_gram Δ b, covolume_sq_eq_det_gram _ c, ← hq,
      covolume_span_sq_eq_det_gram q, hgram, ← W.subtypeₗᵢ.gram_comp, ← Wᗮ.subtypeₗᵢ.gram_comp]
    simp [Function.comp_def]
  have hP := covolume_pos (span ℤ (Set.range q)) volume
  rw [hq] at hP
  have hL' := covolume_pos (ZLattice.comap ℝ Δ W.subtype) volume
  rw [eq_div_iff hL'.ne', mul_comm]
  exact (pow_left_inj₀ (covolume_pos Δ volume).le (mul_pos hL' hP).le two_ne_zero).1 hsq |>.symm

end InnerProductSpace

end ZLattice
