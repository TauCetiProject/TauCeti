/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.PL.Orthant.Basic
public import TauCeti.Topology.PL.Product

/-!
# Flattening a solid orthant to a half-space

Subtracting the last coordinate gives tangential coordinates. The least of all original
coordinates gives the normal coordinate. Together these define an ambient PL homeomorphism
carrying the nonnegative orthant onto a closed half-space, with its frontier carried onto
the boundary hyperplane. The inverse adds the normal coordinate to the boundary lift.

This gives boundary charts for polyhedral balls: near a vertex a simplex is an orthant,
and flattening the solid orthant provides coordinates in a manifold with boundary.
The construction includes the one-dimensional orthant, with no tangential coordinates.

The inverse reuses `orthantLift` and its finite affine decomposition.
Reference: C. P. Rourke and B. J. Sanderson, *Introduction to Piecewise-Linear Topology*,
Springer (1972), Chapters 1–2 (polyhedral local models).
-/

public section

noncomputable section

open Set Topology

namespace TauCeti

variable {ι : Type*} [Fintype ι]

/-- An ambient PL homeomorphism flattening the nonnegative orthant to a half-space.
Its tangential coordinate is `orthantProjection`; its normal coordinate is the minimum
of all orthant coordinates. -/
def orthantFlattening : ((ι → ℝ) × ℝ) ≃ₜ ((ι → ℝ) × ℝ) := by
  have hc := continuousOn_univ.mp
    (isPiecewiseAffineOn_orthantLift (ι := ι)).continuousOn
  refine {
    toFun := fun p => (orthantProjection p, p.2 - (orthantLift (orthantProjection p)).2)
    invFun := fun q => ((orthantLift q.1).1 + fun _ => q.2, (orthantLift q.1).2 + q.2)
    left_inv := ?_
    right_inv := ?_
    continuous_toFun := orthantProjection.continuous.prodMk
      (continuous_snd.sub ((hc.comp orthantProjection.continuous).snd))
    continuous_invFun := ((hc.comp continuous_fst).fst.add
      (continuous_pi fun _ => continuous_snd)).prodMk
      ((hc.comp continuous_fst).snd.add continuous_snd) }
  · intro p
    apply Prod.ext
    · funext i
      have h := congrFun (orthantProjection_orthantLift (orthantProjection p)) i
      simp only [orthantProjection_apply, Pi.add_apply] at h ⊢
      linarith
    · simp
  · intro q
    have hp : orthantProjection
        ((orthantLift q.1).1 + fun _ => q.2, (orthantLift q.1).2 + q.2) = q.1 := by
      ext i
      have h := congrFun (orthantProjection_orthantLift q.1) i
      simp only [orthantProjection_apply, Pi.add_apply] at h ⊢
      linarith
    simp [hp]

/-- The flattening subtracts the boundary lift's last coordinate from the height. -/
@[simp] theorem orthantFlattening_apply (p : (ι → ℝ) × ℝ) :
    orthantFlattening p =
      (orthantProjection p, p.2 - (orthantLift (orthantProjection p)).2) := (rfl)

/-- The inverse adds the height to every coordinate of the orthant boundary lift. -/
@[simp] theorem orthantFlattening_symm_apply (q : (ι → ℝ) × ℝ) :
    orthantFlattening.symm q =
      ((orthantLift q.1).1 + fun _ => q.2, (orthantLift q.1).2 + q.2) := (rfl)

/-- Flattening is piecewise affine on the whole ambient space. -/
theorem isPiecewiseAffineOn_orthantFlattening :
    IsPiecewiseAffineOn (orthantFlattening (ι := ι)) univ := by
  let A : (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ)) →L[ℝ] ((ι → ℝ) × ℝ) :=
    (orthantProjection.comp (ContinuousLinearMap.fst ℝ _ _)).prod
      ((ContinuousLinearMap.snd ℝ _ _).comp (ContinuousLinearMap.fst ℝ _ _) -
        (ContinuousLinearMap.snd ℝ _ _).comp (ContinuousLinearMap.snd ℝ _ _))
  have hl := (isPiecewiseAffineOn_orthantLift (ι := ι)).comp
    (isPiecewiseAffineOn_continuousAffineMap orthantProjection.toContinuousAffineMap univ)
    (mapsTo_univ _ _)
  exact ((isPiecewiseAffineOn_continuousAffineMap A.toContinuousAffineMap univ).comp
    ((isPiecewiseAffineOn_continuousAffineMap (ContinuousAffineMap.id ℝ _) univ).prodMk hl)
    (mapsTo_univ _ _)).congr (fun _ _ => rfl)

/-- The inverse flattening is piecewise affine on the whole ambient space. -/
theorem isPiecewiseAffineOn_orthantFlattening_symm :
    IsPiecewiseAffineOn (orthantFlattening (ι := ι)).symm univ := by
  let A : (((ι → ℝ) × ℝ) × ℝ) →L[ℝ] ((ι → ℝ) × ℝ) :=
    (((ContinuousLinearMap.fst ℝ (ι → ℝ) ℝ).comp
      (ContinuousLinearMap.fst ℝ ((ι → ℝ) × ℝ) ℝ)) +
      ContinuousLinearMap.pi (fun _ : ι =>
        ContinuousLinearMap.snd ℝ ((ι → ℝ) × ℝ) ℝ)).prod
      ((ContinuousLinearMap.snd ℝ _ _).comp (ContinuousLinearMap.fst ℝ _ _) +
        ContinuousLinearMap.snd ℝ _ _)
  have hl := (isPiecewiseAffineOn_orthantLift (ι := ι)).comp
    (isPiecewiseAffineOn_continuousAffineMap
      (ContinuousLinearMap.fst ℝ (ι → ℝ) ℝ).toContinuousAffineMap univ)
    (mapsTo_univ _ _)
  exact ((isPiecewiseAffineOn_continuousAffineMap A.toContinuousAffineMap univ).comp
    (hl.prodMk (isPiecewiseAffineOn_continuousAffineMap
      (ContinuousLinearMap.snd ℝ (ι → ℝ) ℝ).toContinuousAffineMap univ))
    (mapsTo_univ _ _)).congr (fun q _ => by
      rw [orthantFlattening_symm_apply]
      ext i <;> simp [A])

/-- The normal coordinate is the minimum of the original coordinates, including the last one. -/
theorem orthantFlattening_snd_eq_inf (p : (ι → ℝ) × ℝ) :
    (orthantFlattening p).2 =
      Finset.univ.inf' Finset.univ_nonempty (Option.elim' p.2 p.1) := by
  obtain ⟨hx, ht, hz⟩ := (mem_frontier_nonnegOrthant_iff _).mp
    (orthantLift_mem_frontier (orthantProjection p))
  have he (i : ι) := congrFun (orthantProjection_orthantLift (orthantProjection p)) i
  simp only [orthantProjection_apply] at he
  apply le_antisymm
  · apply Finset.le_inf'
    intro i _
    cases i with
    | none => simp only [orthantFlattening_apply, Option.elim'_none]; linarith
    | some i => simp only [orthantFlattening_apply, Option.elim'_some]; linarith [hx i, he i]
  · rcases hz with hz | ⟨i, hi⟩
    · simpa only [orthantFlattening_apply, hz, sub_zero, Option.elim'_none] using
        Finset.inf'_le (Option.elim' p.2 p.1) (Finset.mem_univ none)
    · have hb := Finset.inf'_le (Option.elim' p.2 p.1) (Finset.mem_univ (some i))
      simp only [Option.elim'_some, orthantFlattening_apply] at hb ⊢
      linarith [he i]

/-- The orthant condition becomes nonnegativity of the normal coordinate. -/
theorem mem_nonnegOrthant_iff_orthantFlattening (p : (ι → ℝ) × ℝ) :
    p ∈ Ici (0 : (ι → ℝ) × ℝ) ↔ 0 ≤ (orthantFlattening p).2 := by
  rw [orthantFlattening_snd_eq_inf, Finset.le_inf'_iff]
  simp only [mem_Ici, Prod.le_def, Pi.le_def, Finset.mem_univ, forall_const]
  constructor
  · rintro ⟨hx, ht⟩ (_ | i)
    · exact ht
    · exact hx i
  · intro h
    exact ⟨fun i => h (some i), h none⟩

/-- The ambient flattening takes the nonnegative orthant onto the closed half-space. -/
theorem orthantFlattening_image_nonnegOrthant :
    orthantFlattening '' Ici (0 : (ι → ℝ) × ℝ) = {q | 0 ≤ q.2} := by
  rw [Homeomorph.image_eq_preimage_symm]
  ext q
  simp only [mem_preimage, mem_ofPred_eq, mem_nonnegOrthant_iff_orthantFlattening,
    Homeomorph.apply_symm_apply]

/-- The orthant frontier is exactly where the flattened normal coordinate vanishes. -/
theorem mem_frontier_nonnegOrthant_iff_orthantFlattening (p : (ι → ℝ) × ℝ) :
    p ∈ frontier (Ici (0 : (ι → ℝ) × ℝ)) ↔ (orthantFlattening p).2 = 0 := by
  rw [mem_frontier_nonnegOrthant_iff]
  have hmin := orthantFlattening_snd_eq_inf p
  constructor
  · rintro ⟨hx, ht, hz⟩
    apply le_antisymm
    · rw [hmin]
      rcases hz with hz | ⟨i, hi⟩
      · simpa only [hz, Option.elim'_none] using
        Finset.inf'_le (Option.elim' p.2 p.1) (Finset.mem_univ none)
      · simpa only [Option.elim'_some, hi] using
          Finset.inf'_le (Option.elim' p.2 p.1) (Finset.mem_univ (some i))
    · exact (mem_nonnegOrthant_iff_orthantFlattening p).mp ⟨hx, ht⟩
  · intro hp
    obtain ⟨hx, ht⟩ := (mem_nonnegOrthant_iff_orthantFlattening p).mpr hp.ge
    refine ⟨hx, ht, ?_⟩
    obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty
      (Option.elim' p.2 p.1)
    rw [← hmin, hp] at hi
    cases i with
    | none => exact Or.inl hi.symm
    | some i => exact Or.inr ⟨i, hi.symm⟩

/-- The solid nonnegative orthant is PL homeomorphic to a closed half-space.
Both maps are restrictions of the ambient piecewise-affine flattening and its inverse. -/
def orthantHalfSpaceHomeomorph :
    Ici (0 : (ι → ℝ) × ℝ) ≃ₜ {q : (ι → ℝ) × ℝ | 0 ≤ q.2} :=
  orthantFlattening.subtype mem_nonnegOrthant_iff_orthantFlattening

/-- The half-space homeomorphism uses the ambient flattening formula. -/
@[simp] theorem coe_orthantHalfSpaceHomeomorph_apply
    (p : Ici (0 : (ι → ℝ) × ℝ)) :
    (orthantHalfSpaceHomeomorph p : (ι → ℝ) × ℝ) = orthantFlattening p := (rfl)

/-- Its inverse uses the ambient inverse flattening formula. -/
@[simp] theorem coe_orthantHalfSpaceHomeomorph_symm_apply
    (q : {q : (ι → ℝ) × ℝ | 0 ≤ q.2}) :
    (orthantHalfSpaceHomeomorph.symm q : (ι → ℝ) × ℝ) =
      orthantFlattening.symm q := (rfl)

end TauCeti
