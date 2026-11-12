/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fredholm.LevelSet.GlobalParametric
public import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Incidence equations and transverse parameters

For a family `F : E × P → V` and a map `j : W → V`, the incidence equation is
`F (x, p) - j y = 0`. A regular incidence parameter is one for which the derivative in
the source variables `(x, y)` is surjective at every incidence point. Its linearization
is the difference of the derivatives of the slice and of `j`; in particular, the
derivative of `j` must not be omitted.

These equations express transversality to a map, without requiring its image to be
closed or embedded. If the sum of the source dimensions is smaller than the target
dimension, regularity implies disjointness of the two images.

The construction uses `TauCeti.IsRegularParameter` for the parametrized zero equation.
For the classical transversality criterion, see Lee, *Introduction to Smooth Manifolds*,
second edition, Chapter 6.
-/

public section

open Function Set
open scoped ContDiff

namespace TauCeti

variable {E W V P : Type*}

section Equation

variable [AddGroup V]

/-- The equation whose zeros are the incidences of a parametrized map with `j`.
The source variables precede the parameter. -/
def incidenceEquation (F : E × P → V) (j : W → V) : (E × W) × P → V :=
  fun z ↦ F (z.1.1, z.2) - j z.1.2

/-- Evaluate the incidence equation in source and parameter coordinates. -/
@[simp]
theorem incidenceEquation_apply (F : E × P → V) (j : W → V) (x : E) (y : W) (p : P) :
    incidenceEquation F j ((x, y), p) = F (x, p) - j y :=
  (rfl)

/-- A zero of the incidence equation is an equality of the two maps. -/
theorem incidenceEquation_eq_zero (F : E × P → V) (j : W → V) (x : E) (y : W) (p : P) :
    incidenceEquation F j ((x, y), p) = 0 ↔ F (x, p) = j y := by
  simp only [incidenceEquation_apply, sub_eq_zero]

end Equation

section Derivative

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup W] [NormedSpace 𝕜 W]
  [NormedAddCommGroup V] [NormedSpace 𝕜 V]
  [NormedAddCommGroup P] [NormedSpace 𝕜 P]

/-- The incidence equation has the differentiability order of the family and the map. -/
theorem _root_.ContDiff.incidenceEquation {n : ℕ∞ω} {F : E × P → V} {j : W → V}
    (hF : ContDiff 𝕜 n F) (hj : ContDiff 𝕜 n j) :
    ContDiff 𝕜 n (incidenceEquation F j) := by
  exact (hF.comp (contDiff_fst.fst.prodMk contDiff_snd)).sub
    (hj.comp contDiff_fst.snd)

/-- The full derivative of the incidence equation, including the parameter direction. -/
theorem fderiv_incidenceEquation_apply
    {F : E × P → V} {j : W → V} {x : E} {y : W} {p : P}
    (hF : DifferentiableAt 𝕜 F (x, p)) (hj : DifferentiableAt 𝕜 j y)
    (u : E) (v : W) (q : P) :
    fderiv 𝕜 (incidenceEquation F j) ((x, y), p) ((u, v), q) =
      fderiv 𝕜 F (x, p) (u, q) - fderiv 𝕜 j y v := by
  have hfst : HasFDerivAt (Prod.fst : (E × W) × P → E × W)
      (ContinuousLinearMap.fst 𝕜 (E × W) P) ((x, y), p) := hasFDerivAt_fst
  have hsnd : HasFDerivAt (Prod.snd : (E × W) × P → P)
      (ContinuousLinearMap.snd 𝕜 (E × W) P) ((x, y), p) := hasFDerivAt_snd
  have hd := ((hF.hasFDerivAt.comp ((x, y), p) (hfst.fst.prodMk hsnd)).sub
    (hj.hasFDerivAt.comp ((x, y), p) hfst.snd)).fderiv
  exact congrArg (fun L : ((E × W) × P) →L[𝕜] V ↦ L ((u, v), q)) hd

/-- The source derivative is `(u, v) ↦ D_x F (x, p) u - D j y v`. -/
theorem fderiv_incidenceEquation_comp_inl
    {F : E × P → V} {j : W → V} {x : E} {y : W} {p : P}
    (hF : DifferentiableAt 𝕜 F (x, p)) (hj : DifferentiableAt 𝕜 j y) :
    (fderiv 𝕜 (incidenceEquation F j) ((x, y), p)).comp
        (ContinuousLinearMap.inl 𝕜 (E × W) P) =
      ((fderiv 𝕜 F (x, p)).comp (ContinuousLinearMap.inl 𝕜 E P)).coprod
        (-fderiv 𝕜 j y) := by
  apply ContinuousLinearMap.ext
  rintro ⟨u, v⟩
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply,
    fderiv_incidenceEquation_apply hF hj, ContinuousLinearMap.coprod_apply,
    neg_apply, sub_eq_add_neg]

end Derivative

section Regular

variable [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- A parameter is regular for incidence when the slice is transverse to `j` at
every incidence point. This uses the derivative only in the source variables. -/
def IsRegularIncidenceParameter (F : E × P → V) (j : W → V) (p : P) : Prop :=
  IsRegularParameter (incidenceEquation F j) 0 p

/-- Regular incidence parameters are precisely the regular parameters of the zero equation. -/
theorem isRegularIncidenceParameter_iff (F : E × P → V) (j : W → V) (p : P) :
    IsRegularIncidenceParameter F j p ↔ IsRegularParameter (incidenceEquation F j) 0 p :=
  (Iff.rfl)

/-- For differentiable maps, regular incidence is the usual surjectivity criterion
for the difference of their source derivatives. Differentiability is needed only at
incidence points. -/
theorem isRegularIncidenceParameter_iff_surjective
    {F : E × P → V} {j : W → V} {p : P}
    (hF : ∀ x y, F (x, p) = j y → DifferentiableAt ℝ F (x, p))
    (hj : ∀ x y, F (x, p) = j y → DifferentiableAt ℝ j y) :
    IsRegularIncidenceParameter F j p ↔ ∀ x y, F (x, p) = j y →
      Surjective (((fderiv ℝ F (x, p)).comp (ContinuousLinearMap.inl ℝ E P)).coprod
        (-fderiv ℝ j y)) := by
  rw [isRegularIncidenceParameter_iff, isRegularParameter_iff]
  simp only [Prod.forall, incidenceEquation_eq_zero]
  congr! 3 with x y hxy
  rw [fderiv_incidenceEquation_comp_inl (hF x y hxy) (hj x y hxy)]

/-- A slice which misses the image of `j` is a regular incidence slice. -/
theorem isRegularIncidenceParameter_of_disjoint_range
    {F : E × P → V} {j : W → V} {p : P}
    (h : Disjoint (range fun x ↦ F (x, p)) (range j)) :
    IsRegularIncidenceParameter F j p := by
  rw [isRegularIncidenceParameter_iff, isRegularParameter_iff]
  rintro ⟨x, y⟩ hxy
  have heq := (incidenceEquation_eq_zero F j x y p).1 hxy
  exact (Set.disjoint_left.1 h ⟨x, rfl⟩ ⟨y, heq.symm⟩).elim

/-- In dimensions too small for a surjective source derivative, a regular slice has
no incidence points. No differentiability hypotheses are needed for this implication. -/
theorem IsRegularIncidenceParameter.disjoint_range [FiniteDimensional ℝ E]
    [FiniteDimensional ℝ W] {F : E × P → V} {j : W → V} {p : P}
    (h : IsRegularIncidenceParameter F j p)
    (hdim : Module.finrank ℝ E + Module.finrank ℝ W < Module.finrank ℝ V) :
    Disjoint (range fun x ↦ F (x, p)) (range j) := by
  rw [Set.disjoint_left]
  rintro _ ⟨x, rfl⟩ ⟨y, hy⟩
  have hs := (isRegularParameter_iff.1
    ((isRegularIncidenceParameter_iff F j p).1 h)) (x, y)
      ((incidenceEquation_eq_zero F j x y p).2 hy.symm)
  have hd := LinearMap.finrank_le_finrank_of_surjective hs
  rw [Module.finrank_prod] at hd
  exact (not_le_of_gt hdim) hd

/-- Below the target dimension, regular incidence is equivalent to avoidance. -/
theorem isRegularIncidenceParameter_iff_disjoint_range [FiniteDimensional ℝ E]
    [FiniteDimensional ℝ W] {F : E × P → V} {j : W → V} {p : P}
    (hdim : Module.finrank ℝ E + Module.finrank ℝ W < Module.finrank ℝ V) :
    IsRegularIncidenceParameter F j p ↔ Disjoint (range fun x ↦ F (x, p)) (range j) :=
  ⟨fun h ↦ h.disjoint_range hdim, isRegularIncidenceParameter_of_disjoint_range⟩

/-- Surjectivity of the derivative of `j` alone suffices for transverse incidence.
This includes the identity map, even for a singular source slice. -/
theorem isRegularIncidenceParameter_of_surjective_fderiv
    {F : E × P → V} {j : W → V} {p : P}
    (hF : ∀ x y, F (x, p) = j y → DifferentiableAt ℝ F (x, p))
    (hj : ∀ x y, F (x, p) = j y → DifferentiableAt ℝ j y)
    (hs : ∀ x y, F (x, p) = j y → Surjective (fderiv ℝ j y)) :
    IsRegularIncidenceParameter F j p := by
  rw [isRegularIncidenceParameter_iff_surjective hF hj]
  intro x y hxy v
  obtain ⟨w, hw⟩ := hs x y hxy (-v)
  exact ⟨(0, w), by simp [hw, ← Prod.zero_eq_mk]⟩

/-- Every differentiable family is transverse to the identity map at every parameter. -/
theorem isRegularIncidenceParameter_id {F : E × P → V} {p : P}
    (hF : ∀ x, DifferentiableAt ℝ F (x, p)) :
    IsRegularIncidenceParameter F (id : V → V) p := by
  apply isRegularIncidenceParameter_of_surjective_fderiv
    (fun x _ _ ↦ hF x) (fun _ y _ ↦ differentiableAt_id)
  intro x y hxy
  simpa using (Function.surjective_id : Surjective (id : V → V))

end Regular

end TauCeti
