/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fredholm.LevelSet.GlobalParametric
public import Mathlib.LinearAlgebra.Dimension.Finrank
import TauCeti.Analysis.Calculus.FDeriv.Basic

/-!
# Incidence equations and transverse parameters

For a family `F : E × P → V` and a map `j : W → V`, the incidence equation is
`F (x, p) - j y = 0`. Regularity restricts the joint Fréchet derivative of the
incidence equation at `((x, y), p)` to the source directions `E × W`, requiring
surjectivity at every incidence point. When `F` and `j` are differentiable there, this
agrees with slice transversality: the linearization is the difference of the source
derivative of `F` and the derivative of `j`.

These equations express transversality to a map, without requiring its image to be
closed or embedded. If the sources `E` and `W` are finite-dimensional and the sum of their
`Module.finrank`s is smaller than the target `Module.finrank`, regularity implies
disjointness of the two images. This inequality applies only to finite-dimensional targets.

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

/-- The incidence equation as a function of source and parameter coordinates. -/
theorem incidenceEquation_def (F : E × P → V) (j : W → V) :
    incidenceEquation F j = fun z ↦ F (z.1.1, z.2) - j z.1.2 :=
  (rfl)

/-- Evaluate the incidence equation at an arbitrary source and parameter point. -/
@[simp, grind =]
theorem incidenceEquation_apply (F : E × P → V) (j : W → V) (z : (E × W) × P) :
    incidenceEquation F j z = F (z.1.1, z.2) - j z.1.2 :=
  (rfl)

/-- A zero of the incidence equation is an equality of the two maps. -/
@[grind =]
theorem incidenceEquation_eq_zero {F : E × P → V} {j : W → V} {z : (E × W) × P} :
    incidenceEquation F j z = 0 ↔ F (z.1.1, z.2) = j z.1.2 := by
  simp only [incidenceEquation_apply, sub_eq_zero]

end Equation

section Derivative

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup W] [NormedSpace 𝕜 W]
  [NormedAddCommGroup V] [NormedSpace 𝕜 V]
  [NormedAddCommGroup P] [NormedSpace 𝕜 P]

/-- The incidence equation has the pointwise differentiability order of its two maps. -/
@[fun_prop]
theorem _root_.ContDiffAt.incidenceEquation {n : ℕ∞ω} {F : E × P → V} {j : W → V}
    {x : E} {y : W} {p : P}
    (hF : ContDiffAt 𝕜 n F (x, p)) (hj : ContDiffAt 𝕜 n j y) :
    ContDiffAt 𝕜 n (incidenceEquation F j) ((x, y), p) := by
  exact (hF.comp ((x, y), p) (contDiffAt_fst.fst.prodMk contDiffAt_snd)).sub
    (hj.comp ((x, y), p) contDiffAt_fst.snd)

/-- The incidence equation has the differentiability order of the family and the map. -/
@[fun_prop]
theorem _root_.ContDiff.incidenceEquation {n : ℕ∞ω} {F : E × P → V} {j : W → V}
    (hF : ContDiff 𝕜 n F) (hj : ContDiff 𝕜 n j) :
    ContDiff 𝕜 n (incidenceEquation F j) := by
  rw [contDiff_iff_contDiffAt]
  rintro ⟨⟨x, y⟩, p⟩
  exact (hF.contDiffAt (x := (x, p))).incidenceEquation hj.contDiffAt

/-- Derivatives of the two maps give the full derivative of the incidence equation. -/
@[fun_prop]
theorem _root_.HasFDerivAt.incidenceEquation
    {F : E × P → V} {j : W → V} {F' : E × P →L[𝕜] V} {j' : W →L[𝕜] V}
    {x : E} {y : W} {p : P} (hF : HasFDerivAt F F' (x, p)) (hj : HasFDerivAt j j' y) :
    HasFDerivAt (incidenceEquation F j)
      (((F'.comp (.inl 𝕜 E P)).coprod (-j')).coprod (F'.comp (.inr 𝕜 E P)))
      ((x, y), p) := by
  rw [incidenceEquation_def]
  have hfst : HasFDerivAt (Prod.fst : (E × W) × P → E × W)
      (ContinuousLinearMap.fst 𝕜 (E × W) P) ((x, y), p) := hasFDerivAt_fst
  refine ((hF.comp ((x, y), p) (hfst.fst.prodMk hasFDerivAt_snd)).sub
    (hj.comp ((x, y), p) hfst.snd)).congr_fderiv ?_
  ext <;> simp [← Prod.zero_eq_mk]

/-- Strict derivatives of the maps give the strict derivative of the incidence equation. -/
@[fun_prop]
theorem _root_.HasStrictFDerivAt.incidenceEquation
    {F : E × P → V} {j : W → V} {F' : E × P →L[𝕜] V} {j' : W →L[𝕜] V}
    {x : E} {y : W} {p : P}
    (hF : HasStrictFDerivAt F F' (x, p)) (hj : HasStrictFDerivAt j j' y) :
    HasStrictFDerivAt (incidenceEquation F j)
      (((F'.comp (.inl 𝕜 E P)).coprod (-j')).coprod (F'.comp (.inr 𝕜 E P)))
      ((x, y), p) := by
  rw [incidenceEquation_def]
  have hfst : HasStrictFDerivAt (Prod.fst : (E × W) × P → E × W)
      (ContinuousLinearMap.fst 𝕜 (E × W) P) ((x, y), p) := hasStrictFDerivAt_fst
  refine ((hF.comp ((x, y), p) (hfst.fst.prodMk hasStrictFDerivAt_snd)).sub
    (hj.comp ((x, y), p) hfst.snd)).congr_fderiv ?_
  ext <;> simp [← Prod.zero_eq_mk]

/-- The incidence equation is differentiable wherever its two maps are differentiable. -/
@[fun_prop]
theorem _root_.DifferentiableAt.incidenceEquation
    {F : E × P → V} {j : W → V} {x : E} {y : W} {p : P}
    (hF : DifferentiableAt 𝕜 F (x, p)) (hj : DifferentiableAt 𝕜 j y) :
    DifferentiableAt 𝕜 (incidenceEquation F j) ((x, y), p) :=
  (hF.hasFDerivAt.incidenceEquation hj.hasFDerivAt).differentiableAt

/-- The incidence equation is differentiable when its two maps are differentiable. -/
@[fun_prop]
theorem _root_.Differentiable.incidenceEquation {F : E × P → V} {j : W → V}
    (hF : Differentiable 𝕜 F) (hj : Differentiable 𝕜 j) :
    Differentiable 𝕜 (incidenceEquation F j) :=
  fun _ ↦ (hF _).incidenceEquation (hj _)

/-- The incidence equation is differentiable at a point exactly when the family and the map
are differentiable at the corresponding points. -/
@[simp]
theorem differentiableAt_incidenceEquation_iff {F : E × P → V} {j : W → V}
    {z : (E × W) × P} :
    DifferentiableAt 𝕜 (incidenceEquation F j) z ↔
      DifferentiableAt 𝕜 F (z.1.1, z.2) ∧ DifferentiableAt 𝕜 j z.1.2 := by
  obtain ⟨⟨x, y⟩, p⟩ := z
  refine ⟨fun h ↦ ⟨?_, ?_⟩, fun h ↦ h.1.incidenceEquation h.2⟩
  · have hF : F = fun q ↦ incidenceEquation F j ((q.1, y), q.2) + j y := by
      funext q
      simp
    rw [hF]
    exact (h.comp (f := fun q : E × P ↦ ((q.1, y), q.2)) (x, p) (by fun_prop)).add_const _
  · have hj : j = fun w ↦ F (x, p) - incidenceEquation F j ((x, w), p) := by
      funext w
      simp
    rw [hj]
    exact (h.comp (f := fun w : W ↦ ((x, w), p)) y (by fun_prop)).const_sub _

/-- The incidence equation is differentiable exactly when its two maps are differentiable. -/
@[simp]
theorem differentiable_incidenceEquation_iff {F : E × P → V} {j : W → V} :
    Differentiable 𝕜 (incidenceEquation F j) ↔ Differentiable 𝕜 F ∧ Differentiable 𝕜 j :=
  ⟨fun h ↦ ⟨fun z ↦ (differentiableAt_incidenceEquation_iff.1 (h ((z.1, 0), z.2))).1,
    fun y ↦ (differentiableAt_incidenceEquation_iff.1 (h ((0, y), 0))).2⟩,
    fun h ↦ h.1.incidenceEquation h.2⟩

/-- The incidence equation has differentiability order `n` at a point exactly when the family
and the map have that order at the corresponding points. -/
@[simp]
theorem contDiffAt_incidenceEquation_iff {n : ℕ∞ω} {F : E × P → V} {j : W → V}
    {z : (E × W) × P} :
    ContDiffAt 𝕜 n (incidenceEquation F j) z ↔
      ContDiffAt 𝕜 n F (z.1.1, z.2) ∧ ContDiffAt 𝕜 n j z.1.2 := by
  obtain ⟨⟨x, y⟩, p⟩ := z
  refine ⟨fun h ↦ ⟨?_, ?_⟩, fun h ↦ h.1.incidenceEquation h.2⟩
  · have hF : F = fun q ↦ incidenceEquation F j ((q.1, y), q.2) + j y := by
      funext q
      simp
    rw [hF]
    exact (h.comp (f := fun q : E × P ↦ ((q.1, y), q.2)) (x, p) (by fun_prop)).add
      contDiffAt_const
  · have hj : j = fun w ↦ F (x, p) - incidenceEquation F j ((x, w), p) := by
      funext w
      simp
    rw [hj]
    exact contDiffAt_const.sub (h.comp (f := fun w : W ↦ ((x, w), p)) y (by fun_prop))

/-- The incidence equation has differentiability order `n` exactly when its two maps do. -/
@[simp]
theorem contDiff_incidenceEquation_iff {n : ℕ∞ω} {F : E × P → V} {j : W → V} :
    ContDiff 𝕜 n (incidenceEquation F j) ↔ ContDiff 𝕜 n F ∧ ContDiff 𝕜 n j := by
  simp only [contDiff_iff_contDiffAt]
  exact ⟨fun h ↦ ⟨fun z ↦ (contDiffAt_incidenceEquation_iff.1 (h ((z.1, 0), z.2))).1,
    fun y ↦ (contDiffAt_incidenceEquation_iff.1 (h ((0, y), 0))).2⟩,
    fun h ↦ fun z ↦ (h.1 _).incidenceEquation (h.2 _)⟩

/-- The full derivative of the incidence equation, including the parameter direction. -/
theorem fderiv_incidenceEquation_apply
    {F : E × P → V} {j : W → V} {x : E} {y : W} {p : P}
    (hF : DifferentiableAt 𝕜 F (x, p)) (hj : DifferentiableAt 𝕜 j y)
    (u : E) (v : W) (q : P) :
    fderiv 𝕜 (incidenceEquation F j) ((x, y), p) ((u, v), q) =
      fderiv 𝕜 F (x, p) (u, q) - fderiv 𝕜 j y v := by
  rw [(hF.hasFDerivAt.incidenceEquation hj.hasFDerivAt).fderiv]
  simp only [ContinuousLinearMap.coprod_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.inl_apply, neg_apply, ContinuousLinearMap.inr_apply, sub_eq_add_neg]
  rw [add_right_comm, ← map_add]
  simp

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

/-- The parameter derivative of the incidence equation is that of the family. -/
theorem fderiv_incidenceEquation_comp_inr
    {F : E × P → V} {j : W → V} {x : E} {y : W} {p : P}
    (hF : DifferentiableAt 𝕜 F (x, p)) (hj : DifferentiableAt 𝕜 j y) :
    (fderiv 𝕜 (incidenceEquation F j) ((x, y), p)).comp
        (ContinuousLinearMap.inr 𝕜 (E × W) P) =
      (fderiv 𝕜 F (x, p)).comp (ContinuousLinearMap.inr 𝕜 E P) := by
  ext q
  simp [fderiv_incidenceEquation_apply hF hj]

end Derivative

section Regular

variable [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- Incidence regularity requires the joint Fréchet derivative of the incidence equation,
restricted to the source directions `E × W`, to be surjective at every incidence point.
It agrees with slice transversality when `F` and `j` are differentiable there. -/
def IsRegularIncidenceParameter (F : E × P → V) (j : W → V) (p : P) : Prop :=
  IsRegularParameter (incidenceEquation F j) 0 p

/-- Regular incidence parameters are precisely the regular parameters of the zero equation. -/
theorem isRegularIncidenceParameter_iff {F : E × P → V} {j : W → V} {p : P} :
    IsRegularIncidenceParameter F j p ↔ IsRegularParameter (incidenceEquation F j) 0 p :=
  (Iff.rfl)

/-- At an incidence point of a regular slice, the family and the map are differentiable. -/
theorem IsRegularIncidenceParameter.differentiableAt
    {F : E × P → V} {j : W → V} {p : P} {x : E} {y : W}
    (h : IsRegularIncidenceParameter F j p) (hxy : F (x, p) = j y) :
    DifferentiableAt ℝ F (x, p) ∧ DifferentiableAt ℝ j y := by
  have hs := (isRegularParameter_iff.1 (isRegularIncidenceParameter_iff.1 h)) (x, y)
    (incidenceEquation_eq_zero.2 hxy)
  rw [ContinuousLinearMap.coe_comp] at hs
  exact differentiableAt_incidenceEquation_iff.1 (differentiableAt_of_fderiv_surjective hs.of_comp)

/-- At an incidence point, regularity gives surjectivity of the source linearization. -/
theorem IsRegularIncidenceParameter.surjective
    {F : E × P → V} {j : W → V} {p : P} {x : E} {y : W}
    (h : IsRegularIncidenceParameter F j p) (hxy : F (x, p) = j y) :
    Surjective (((fderiv ℝ F (x, p)).comp (.inl ℝ E P)).coprod (-fderiv ℝ j y)) := by
  obtain ⟨hF, hj⟩ := h.differentiableAt hxy
  rw [← fderiv_incidenceEquation_comp_inl hF hj]
  exact (isRegularParameter_iff.1 (isRegularIncidenceParameter_iff.1 h)) (x, y)
    (incidenceEquation_eq_zero.2 hxy)

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
  have heq := incidenceEquation_eq_zero.1 hxy
  exact (Set.disjoint_left.1 h ⟨x, rfl⟩ ⟨y, heq.symm⟩).elim

/-- When the sources `E` and `W` are finite-dimensional and the sum of their
`Module.finrank`s is below the target `Module.finrank`, a regular slice has no incidence
points. This inequality applies only to finite-dimensional targets. No differentiability
hypotheses are needed for this implication. -/
theorem IsRegularIncidenceParameter.disjoint_range [FiniteDimensional ℝ E]
    [FiniteDimensional ℝ W] {F : E × P → V} {j : W → V} {p : P}
    (h : IsRegularIncidenceParameter F j p)
    (hdim : Module.finrank ℝ E + Module.finrank ℝ W < Module.finrank ℝ V) :
    Disjoint (range fun x ↦ F (x, p)) (range j) := by
  rw [Set.disjoint_left]
  rintro _ ⟨x, rfl⟩ ⟨y, hy⟩
  have hs := (isRegularParameter_iff.1
    (isRegularIncidenceParameter_iff.1 h)) (x, y)
      (incidenceEquation_eq_zero.2 hy.symm)
  have hd := LinearMap.finrank_le_finrank_of_surjective hs
  rw [Module.finrank_prod] at hd
  exact (not_le_of_gt hdim) hd

/-- When the sources `E` and `W` are finite-dimensional and the sum of their
`Module.finrank`s is below the target `Module.finrank`, regular incidence is equivalent to
avoidance. The inequality requires a finite-dimensional target. -/
theorem isRegularIncidenceParameter_iff_disjoint_range [FiniteDimensional ℝ E]
    [FiniteDimensional ℝ W] {F : E × P → V} {j : W → V} {p : P}
    (hdim : Module.finrank ℝ E + Module.finrank ℝ W < Module.finrank ℝ V) :
    IsRegularIncidenceParameter F j p ↔ Disjoint (range fun x ↦ F (x, p)) (range j) :=
  ⟨fun h ↦ h.disjoint_range hdim, isRegularIncidenceParameter_of_disjoint_range⟩

/-- When `F` is differentiable at every incidence point, surjectivity of the derivative of `j`
there suffices for transverse incidence, without any rank condition on the source derivative
of `F`. This includes the identity map, even for a singular source slice. -/
theorem isRegularIncidenceParameter_of_surjective_fderiv
    {F : E × P → V} {j : W → V} {p : P}
    (hF : ∀ x y, F (x, p) = j y → DifferentiableAt ℝ F (x, p))
    (hs : ∀ x y, F (x, p) = j y → Surjective (fderiv ℝ j y)) :
    IsRegularIncidenceParameter F j p := by
  rw [isRegularIncidenceParameter_iff_surjective hF
    fun _ y hxy ↦ differentiableAt_of_fderiv_surjective (hs _ y hxy)]
  intro x y hxy v
  obtain ⟨w, hw⟩ := hs x y hxy (-v)
  exact ⟨(0, w), by simp [hw, ← Prod.zero_eq_mk]⟩

/-- Every differentiable family is transverse to the identity map at every parameter. -/
theorem isRegularIncidenceParameter_id {F : E × P → V} {p : P}
    (hF : ∀ x, DifferentiableAt ℝ F (x, p)) :
    IsRegularIncidenceParameter F (id : V → V) p := by
  apply isRegularIncidenceParameter_of_surjective_fderiv
    (fun x _ _ ↦ hF x)
  intro _ y _
  simpa using (Function.surjective_id : Surjective (id : V → V))

/-- Incidence with a constant map is the level equation at that constant. -/
@[simp]
theorem isRegularIncidenceParameter_const {F : E × P → V} {c : V} {p : P} :
    IsRegularIncidenceParameter F (fun _ : W ↦ c) p ↔ IsRegularParameter F c p := by
  refine ⟨fun h ↦ isRegularParameter_iff.2 fun x hx v ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨⟨u, _⟩, hu⟩ := h.surjective (y := 0) hx v
    exact ⟨u, by simpa using hu⟩
  · have hF (x : E) (_ : W) (hx : F (x, p) = c) : DifferentiableAt ℝ F (x, p) := by
      have hs := isRegularParameter_iff.1 h x hx
      rw [ContinuousLinearMap.coe_comp] at hs
      exact differentiableAt_of_fderiv_surjective hs.of_comp
    refine (isRegularIncidenceParameter_iff_surjective hF
      fun _ _ _ ↦ differentiableAt_const c).2 fun x _ hx v ↦ ?_
    obtain ⟨u, hu⟩ := isRegularParameter_iff.1 h x hx v
    exact ⟨(u, 0), by simpa using hu⟩

/-- Incidence with the zero map is the zero level equation. -/
@[simp]
theorem isRegularIncidenceParameter_zero {F : E × P → V} {p : P} :
    IsRegularIncidenceParameter F (0 : W → V) p ↔ IsRegularParameter F 0 p :=
  isRegularIncidenceParameter_const

end Regular

end TauCeti
