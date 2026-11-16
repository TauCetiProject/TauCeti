/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Variational.Spectrum
public import TauCeti.Analysis.Variational.QuadraticEnergy

/-!
# Identification of real quadratic energy minimizers with Lax--Milgram solutions

On a real Hilbert space `V`, a coercive continuous bilinear form `B : V →L[ℝ] V →L[ℝ] ℝ` (`hB :
IsCoercive B`) has a unique Lax--Milgram solution `hB.solutionOfFunctional ℓ` to `∀ v, B u v = ℓ v`
for every continuous linear functional `ℓ : StrongDual ℝ V`, specialized to represented forcings
`⟪F, ·⟫_ℝ` by `hB.solutionOfInner F` and to pulled-back `H`-forcings `v ↦ ⟪h, J v⟫_ℝ` by
`hB.formSolutionMap J h`.

When `B` is symmetric (`∀ u v, B u v = B v u`), these Lax--Milgram solutions are precisely the
unique global minimizers of `TauCeti.quadraticEnergy B ℓ` over `V` (Hunter, Theorem 4.20). Even
without symmetry of `B`, evaluating `TauCeti.quadraticEnergy B ℓ` at `hB.solutionOfFunctional ℓ`
simplifies to `-ℓ (hB.solutionOfFunctional ℓ)` (the global minimum value when `B` is symmetric).

## Main declarations

* `IsCoercive.isMinOn_quadraticEnergy_iff_eq_solutionOfFunctional` and
  `IsCoercive.isMinOn_quadraticEnergy_solutionOfFunctional`: equivalence between global minimality
  of `TauCeti.quadraticEnergy B ℓ` and `u = hB.solutionOfFunctional ℓ` for symmetric coercive `B`.
* `IsCoercive.isMinOn_quadraticEnergy_iff_eq_continuousLinearEquivOfBilin_symm`: identification via
  Mathlib's `IsCoercive.continuousLinearEquivOfBilin` and `InnerProductSpace.toDual ℝ V`.
* `IsCoercive.isMinOn_quadraticEnergy_toDual_iff_eq_solutionOfInner` and
  `IsCoercive.isMinOn_quadraticEnergy_toDual_solutionOfInner`: identification for represented
  forcing `InnerProductSpace.toDual ℝ V F`.
* `IsCoercive.isMinOn_quadraticEnergy_toSesqForm_iff_eq_formSolutionMap` and
  `IsCoercive.isMinOn_quadraticEnergy_toSesqForm_formSolutionMap`: identification for `H`-forcing
  `ContinuousLinearMap.toSesqForm J h`.
* `IsCoercive.quadraticEnergy_solutionOfFunctional`,
  `IsCoercive.quadraticEnergy_toDual_solutionOfInner`,
  `IsCoercive.quadraticEnergy_formSolutionMap`, and
  `IsCoercive.quadraticEnergy_innerSL_comp_formSolutionMap`: values of `TauCeti.quadraticEnergy` at
  Lax--Milgram solutions.

## References

* J. K. Hunter, *Notes on Partial Differential Equations*, Chapter 4, Theorem 4.20.
-/

public section

noncomputable section

open scoped InnerProductSpace

namespace IsCoercive

variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [SeminormedAddCommGroup H] [InnerProductSpace ℝ H]
  {B : V →L[ℝ] V →L[ℝ] ℝ}

/-- **Characterization of global minimizers via `IsCoercive.solutionOfFunctional`**: for a symmetric
coercive real bilinear form `B`, `u` minimizes `TauCeti.quadraticEnergy B ℓ` on `Set.univ` if and
only if `u = hB.solutionOfFunctional ℓ` (Hunter, Theorem 4.20). -/
theorem isMinOn_quadraticEnergy_iff_eq_solutionOfFunctional (hB : IsCoercive B)
    (hsymm : ∀ u v, B u v = B v u) (ℓ : StrongDual ℝ V) {u : V} :
    IsMinOn (TauCeti.quadraticEnergy B ℓ) Set.univ u ↔ u = hB.solutionOfFunctional ℓ := by
  have hstar : ∀ x y, B x y = star (B y x) := fun x y ↦ by simpa using hsymm x y
  have hpos : ∀ w, 0 ≤ RCLike.re (B w w) := fun w ↦ by simpa using hB.apply_self_nonneg w
  rw [TauCeti.isMinOn_quadraticEnergy_univ_iff hstar hpos]
  exact ⟨fun hu ↦ hB.eq_solutionOfFunctional hu,
    fun h ↦ h ▸ hB.apply_solutionOfFunctional_eq ℓ⟩

/-- For a symmetric coercive real bilinear form `B` on a Hilbert space, the Lax--Milgram functional
solution `hB.solutionOfFunctional ℓ` minimizes `TauCeti.quadraticEnergy B ℓ` over `V`
(Hunter, Theorem 4.20). -/
theorem isMinOn_quadraticEnergy_solutionOfFunctional (hB : IsCoercive B)
    (hsymm : ∀ u v, B u v = B v u) (ℓ : StrongDual ℝ V) :
    IsMinOn (TauCeti.quadraticEnergy B ℓ) Set.univ (hB.solutionOfFunctional ℓ) :=
  (hB.isMinOn_quadraticEnergy_iff_eq_solutionOfFunctional hsymm ℓ).mpr rfl

/-- **Characterization of global minimizers via Mathlib's
`IsCoercive.continuousLinearEquivOfBilin`**: for a symmetric coercive real bilinear form `B`, `u`
minimizes `TauCeti.quadraticEnergy B ℓ` on `Set.univ` if and only if `u` equals the inverse
Lax--Milgram operator applied to the Fréchet--Riesz representative of `ℓ`. -/
theorem isMinOn_quadraticEnergy_iff_eq_continuousLinearEquivOfBilin_symm (hB : IsCoercive B)
    (hsymm : ∀ u v, B u v = B v u) (ℓ : StrongDual ℝ V) {u : V} :
    IsMinOn (TauCeti.quadraticEnergy B ℓ) Set.univ u ↔
      u = hB.continuousLinearEquivOfBilin.symm ((InnerProductSpace.toDual ℝ V).symm ℓ) := by
  rw [hB.isMinOn_quadraticEnergy_iff_eq_solutionOfFunctional hsymm ℓ,
    solutionOfFunctional_apply, solutionOfInner_def]

/-- **Characterization of global minimizers for represented forcing `⟪F, ·⟫_ℝ`** via
`IsCoercive.solutionOfInner` when `B` is a symmetric coercive real bilinear form. -/
theorem isMinOn_quadraticEnergy_toDual_iff_eq_solutionOfInner (hB : IsCoercive B)
    (hsymm : ∀ u v, B u v = B v u) (F : V) {u : V} :
    IsMinOn (TauCeti.quadraticEnergy B (InnerProductSpace.toDual ℝ V F)) Set.univ u ↔
      u = hB.solutionOfInner F := by
  rw [hB.isMinOn_quadraticEnergy_iff_eq_solutionOfFunctional hsymm, solutionOfFunctional_toDual]

/-- For a symmetric coercive real bilinear form `B`, `hB.solutionOfInner F` minimizes
`TauCeti.quadraticEnergy B (InnerProductSpace.toDual ℝ V F)` on `Set.univ`. -/
theorem isMinOn_quadraticEnergy_toDual_solutionOfInner (hB : IsCoercive B)
    (hsymm : ∀ u v, B u v = B v u) (F : V) :
    IsMinOn (TauCeti.quadraticEnergy B (InnerProductSpace.toDual ℝ V F)) Set.univ
      (hB.solutionOfInner F) :=
  (hB.isMinOn_quadraticEnergy_toDual_iff_eq_solutionOfInner hsymm F).mpr rfl

/-- **Characterization of global minimizers for forcing `v ↦ ⟪h, J v⟫_ℝ`** via
`IsCoercive.formSolutionMap`: for a symmetric coercive real bilinear form `B`, `u` minimizes
`TauCeti.quadraticEnergy B (ContinuousLinearMap.toSesqForm J h)` on `Set.univ` if and only if
`u = hB.formSolutionMap J h`. -/
theorem isMinOn_quadraticEnergy_toSesqForm_iff_eq_formSolutionMap (hB : IsCoercive B)
    (hsymm : ∀ u v, B u v = B v u) (J : V →L[ℝ] H) (h : H) {u : V} :
    IsMinOn (TauCeti.quadraticEnergy B (ContinuousLinearMap.toSesqForm J h)) Set.univ u ↔
      u = hB.formSolutionMap J h := by
  rw [hB.isMinOn_quadraticEnergy_iff_eq_solutionOfFunctional hsymm, formSolutionMap_apply]

/-- For a symmetric coercive real bilinear form `B` and forcing `v ↦ ⟪h, J v⟫_ℝ`
(`ContinuousLinearMap.toSesqForm J h`), `hB.formSolutionMap J h` minimizes
`TauCeti.quadraticEnergy B (ContinuousLinearMap.toSesqForm J h)` on `Set.univ`. -/
theorem isMinOn_quadraticEnergy_toSesqForm_formSolutionMap (hB : IsCoercive B)
    (hsymm : ∀ u v, B u v = B v u) (J : V →L[ℝ] H) (h : H) :
    IsMinOn (TauCeti.quadraticEnergy B (ContinuousLinearMap.toSesqForm J h)) Set.univ
      (hB.formSolutionMap J h) :=
  (hB.isMinOn_quadraticEnergy_toSesqForm_iff_eq_formSolutionMap hsymm J h).mpr rfl

/-- Value of `TauCeti.quadraticEnergy B ℓ` at the Lax--Milgram solution
`hB.solutionOfFunctional ℓ` (its global minimum value when `B` is symmetric). -/
@[simp]
theorem quadraticEnergy_solutionOfFunctional (hB : IsCoercive B) (ℓ : StrongDual ℝ V) :
    TauCeti.quadraticEnergy B ℓ (hB.solutionOfFunctional ℓ) = -ℓ (hB.solutionOfFunctional ℓ) := by
  rw [TauCeti.quadraticEnergy_real_apply, hB.apply_solutionOfFunctional_eq]
  ring

/-- Value of `TauCeti.quadraticEnergy B (InnerProductSpace.toDual ℝ V F)` at `hB.solutionOfInner F`
(its global minimum value when `B` is symmetric). -/
@[simp]
theorem quadraticEnergy_toDual_solutionOfInner (hB : IsCoercive B) (F : V) :
    TauCeti.quadraticEnergy B (InnerProductSpace.toDual ℝ V F) (hB.solutionOfInner F) =
      -⟪F, hB.solutionOfInner F⟫_ℝ := by
  rw [← solutionOfFunctional_toDual, quadraticEnergy_solutionOfFunctional,
    solutionOfFunctional_toDual, InnerProductSpace.toDual_apply_apply]

/-- Value of `TauCeti.quadraticEnergy B ((innerSL ℝ h).comp J)` at `hB.formSolutionMap J h`
(its global minimum value when `B` is symmetric). -/
@[simp]
theorem quadraticEnergy_innerSL_comp_formSolutionMap (hB : IsCoercive B) (J : V →L[ℝ] H) (h : H) :
    TauCeti.quadraticEnergy B ((innerSL ℝ h).comp J) (hB.formSolutionMap J h) =
      -⟪h, J (hB.formSolutionMap J h)⟫_ℝ := by
  rw [TauCeti.quadraticEnergy_real_apply, hB.apply_formSolutionMap]
  simp only [ContinuousLinearMap.comp_apply, innerSL_apply_apply]
  ring

/-- Value of `TauCeti.quadraticEnergy B (ContinuousLinearMap.toSesqForm J h)` at
`hB.formSolutionMap J h` (its global minimum value when `B` is symmetric). -/
theorem quadraticEnergy_formSolutionMap (hB : IsCoercive B) (J : V →L[ℝ] H) (h : H) :
    TauCeti.quadraticEnergy B (ContinuousLinearMap.toSesqForm J h) (hB.formSolutionMap J h) =
      -⟪h, J (hB.formSolutionMap J h)⟫_ℝ := by
  simp

end IsCoercive

end
