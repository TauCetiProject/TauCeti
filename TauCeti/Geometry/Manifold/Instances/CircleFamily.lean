/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Algebra.Structures
public import TauCeti.Geometry.Manifold.Instances.AddCircle
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Prod
public import TauCeti.Topology.Covering.Homeomorph
public import TauCeti.Topology.Covering.Prod

/-!
# The smooth family of circles of positive period

`TauCeti.CircleFamily` is the dependent total space of the circles `AddCircle p`, for `p > 0`.
Its normalization sends `(p, x)` to `(p, D_(p,1) x)`, where `D` is the usual rescaling of
additive circles. We transport the topology and smooth structure from the product of the
positive real axis and the unit-period circle through this explicit equivalence.

The fixed-period circles embed smoothly with their existing smooth structures, and each has a
smooth retraction from the total family. These maps identify each original circle with the
subspace fiber of the period projection. The real representative map sends `(p, t)` to
`(p, [t]_p)`; in normalized coordinates its angle is `[t/p]_1`.

The representative map is a covering and a local diffeomorphism, jointly in period and time.
The total space is Hausdorff and second countable. No behavior at period zero is asserted.
The construction uses the rescaling `AddCircle.diffeomorphAddCircle` and the transport API
`Homeomorph.pullbackDiffeomorph`.
-/

public section

noncomputable section

open Set Topology
open scoped Manifold ContDiff

namespace TauCeti

/-- The positive real axis with its native open-submanifold structure. -/
abbrev PositivePeriod := ↥(⟨Ioi (0 : ℝ), isOpen_Ioi⟩ : TopologicalSpace.Opens ℝ)

instance (p : PositivePeriod) : Fact (0 < (p : ℝ)) := ⟨p.property⟩

/-- The total family of additive circles, retaining the original circle in each positive fiber. -/
@[ext]
structure CircleFamily where
  /-- The positive period. -/
  period : PositivePeriod
  /-- A point of the additive circle with this period. -/
  point : AddCircle (period : ℝ)

namespace CircleFamily

/-- Normalize the period-dependent circle to the unit-period circle. -/
def normalizationEquiv : CircleFamily ≃ PositivePeriod × AddCircle (1 : ℝ) where
  toFun z := (z.period, AddCircle.diffeomorphAddCircle (z.period : ℝ) 1 ⊤ z.point)
  invFun z := ⟨z.1, (AddCircle.diffeomorphAddCircle (z.1 : ℝ) 1 ⊤).symm z.2⟩
  left_inv z := by
    rcases z with ⟨p, x⟩
    exact congrArg (CircleFamily.mk p)
      ((AddCircle.diffeomorphAddCircle (p : ℝ) 1 ⊤).symm_apply_apply x)
  right_inv z := Prod.ext rfl ((AddCircle.diffeomorphAddCircle (z.1 : ℝ) 1 ⊤).apply_symm_apply _)

instance : TopologicalSpace CircleFamily :=
  TopologicalSpace.induced normalizationEquiv inferInstance

/-- The total topology is the one for which normalization is a homeomorphism. -/
def normalizationHomeomorph : CircleFamily ≃ₜ PositivePeriod × AddCircle (1 : ℝ) :=
  normalizationEquiv.toHomeomorphOfIsInducing ⟨rfl⟩

instance : T2Space CircleFamily := normalizationHomeomorph.symm.t2Space

instance : SecondCountableTopology CircleFamily :=
  normalizationHomeomorph.secondCountableTopology

instance : ChartedSpace (ModelProd ℝ ℝ) CircleFamily :=
  normalizationHomeomorph.pullbackChartedSpace

instance {n : ℕ∞ω} : IsManifold (𝓘(ℝ).prod 𝓘(ℝ)) n CircleFamily :=
  normalizationHomeomorph.pullback_isManifold _ n

/-- The smooth normalization of the entire dependent family. -/
def normalization (n : ℕ∞ω) :
    CircleFamily ≃ₘ^n⟮𝓘(ℝ).prod 𝓘(ℝ), 𝓘(ℝ).prod 𝓘(ℝ)⟯
      PositivePeriod × AddCircle (1 : ℝ) :=
  { normalizationEquiv with
    contMDiff_toFun := by
      have h := (normalizationHomeomorph.pullbackDiffeomorph (𝓘(ℝ).prod 𝓘(ℝ)) n).contMDiff
      rw [Homeomorph.coe_pullbackDiffeomorph] at h
      simpa only [normalizationHomeomorph, Equiv.toHomeomorphOfIsInducing_apply] using h
    contMDiff_invFun := by
      have h := (normalizationHomeomorph.pullbackDiffeomorph (𝓘(ℝ).prod 𝓘(ℝ)) n).symm.contMDiff
      rw [Homeomorph.coe_pullbackDiffeomorph_symm] at h
      simpa only [normalizationHomeomorph, Equiv.toHomeomorphOfIsInducing_symm_apply] using h }

/-- Normalization retains the positive period. -/
@[simp]
theorem normalization_fst (n : ℕ∞ω) (z : CircleFamily) :
    (normalization n z).1 = z.period := by
  unfold normalization normalizationEquiv
  rfl

/-- Normalization rescales the circle point to period one. -/
@[simp]
theorem normalization_snd (n : ℕ∞ω) (z : CircleFamily) :
    (normalization n z).2 = AddCircle.diffeomorphAddCircle (z.period : ℝ) 1 ⊤ z.point := by
  unfold normalization normalizationEquiv
  rfl

/-- The inverse normalization rescales the unit-period circle back to the specified period. -/
@[simp]
theorem normalization_symm_apply (n : ℕ∞ω) (z : PositivePeriod × AddCircle (1 : ℝ)) :
    (normalization n).symm z =
      ⟨z.1, (AddCircle.diffeomorphAddCircle (z.1 : ℝ) 1 ⊤).symm z.2⟩ := by
  unfold normalization normalizationEquiv
  rfl

/-- The period projection is analytic. -/
theorem contMDiff_period (n : ℕ∞ω) :
    ContMDiff (𝓘(ℝ).prod 𝓘(ℝ)) 𝓘(ℝ) n period := by
  simpa only [Function.comp_def, normalization_fst] using
    contMDiff_fst.comp (normalization n).contMDiff

/-- In normalized coordinates, a fixed-period inclusion rescales only the circle. -/
@[simp]
theorem normalization_mk (n : ℕ∞ω) (p : PositivePeriod) (x : AddCircle (p : ℝ)) :
    normalization n (mk p x) =
      (p, AddCircle.diffeomorphAddCircle (p : ℝ) 1 ⊤ x) := by
  unfold normalization normalizationEquiv
  rfl

/-- Retract the whole family onto a fixed circle by keeping the normalized angle. -/
def retraction (p : PositivePeriod) (z : CircleFamily) : AddCircle (p : ℝ) :=
  (AddCircle.diffeomorphAddCircle (p : ℝ) 1 ⊤).symm (normalization ⊤ z).2

/-- The retraction is a left inverse of the fixed-period inclusion. -/
@[simp]
theorem retraction_mk (p : PositivePeriod) (x : AddCircle (p : ℝ)) :
    retraction p (mk p x) = x := by
  simpa only [retraction, normalization_snd] using
    (AddCircle.diffeomorphAddCircle (p : ℝ) 1 ⊤).symm_apply_apply x

/-- On the period fiber, inclusion is a right inverse of retraction. -/
theorem mk_retraction {p : PositivePeriod} {z : CircleFamily} (h : z.period = p) :
    mk p (retraction p z) = z := by
  subst p
  rcases z with ⟨p, x⟩
  exact congrArg (mk p) (retraction_mk p x)

/-- The original fixed-period atlas makes its inclusion into the total family analytic. -/
theorem contMDiff_mk (p : PositivePeriod) (n : ℕ∞ω) :
    ContMDiff 𝓘(ℝ) (𝓘(ℝ).prod 𝓘(ℝ)) n (mk p) := by
  have h := (normalization n).symm.contMDiff.comp
    ((contMDiff_const (c := p)).prodMk ((AddCircle.diffeomorphAddCircle (p : ℝ) 1 ⊤).contMDiff.of_le
      le_top))
  convert h using 1
  funext x
  simp only [Function.comp_apply, normalization_symm_apply, Diffeomorph.symm_apply_apply]

/-- Keeping the normalized angle gives an analytic retraction to every fixed-period circle. -/
theorem contMDiff_retraction (p : PositivePeriod) (n : ℕ∞ω) :
    ContMDiff (𝓘(ℝ).prod 𝓘(ℝ)) 𝓘(ℝ) n (retraction p) :=
  ((AddCircle.diffeomorphAddCircle (p : ℝ) 1 ⊤).symm.contMDiff.of_le le_top).comp
    (contMDiff_snd.comp ((normalization ⊤).contMDiff.of_le le_top))

/-- Each original circle is homeomorphic to the subspace fiber of the period projection. -/
def fiberHomeomorph (p : PositivePeriod) :
    AddCircle (p : ℝ) ≃ₜ {z : CircleFamily // z.period = p} where
  toFun x := ⟨mk p x, rfl⟩
  invFun z := retraction p z.1
  left_inv := retraction_mk p
  right_inv z := Subtype.ext (mk_retraction z.2)
  continuous_toFun := ((contMDiff_mk p 0).continuous).subtype_mk _
  continuous_invFun := (contMDiff_retraction p 0).continuous.comp continuous_subtype_val

/-- The fiber homeomorphism is the original fixed-period inclusion. -/
@[simp]
theorem coe_fiberHomeomorph (p : PositivePeriod) (x : AddCircle (p : ℝ)) :
    (fiberHomeomorph p x).1 = mk p x := (rfl)

/-- The inverse fiber homeomorphism is the smooth retraction restricted to the fiber. -/
@[simp]
theorem fiberHomeomorph_symm_apply (p : PositivePeriod) (z : {z : CircleFamily // z.period = p}) :
    (fiberHomeomorph p).symm z = retraction p z.1 := (rfl)

/-- The real representative map of the positive-period total family. -/
def representative (z : PositivePeriod × ℝ) : CircleFamily := mk z.1 (z.2 : AddCircle _)

/-- The representative map preserves the period. -/
@[simp]
theorem period_representative (z : PositivePeriod × ℝ) : (representative z).period = z.1 := (rfl)

/-- The representative's normalized angle is the class of `t/p` in the unit circle. -/
@[simp]
theorem normalization_representative (n : ℕ∞ω) (z : PositivePeriod × ℝ) :
    normalization n (representative z) = (z.1, ((z.2 / (z.1 : ℝ) : ℝ) : AddCircle (1 : ℝ))) := by
  rw [representative, normalization_mk, AddCircle.diffeomorphAddCircle_apply_mk]
  simp [div_eq_mul_inv]

/-- Every point in the dependent family has a real representative with its own period. -/
theorem representative_surjective : Function.Surjective representative := by
  intro z
  obtain ⟨t, ht⟩ := QuotientAddGroup.mk_surjective z.point
  exact ⟨(z.period, t), by simp [representative, ht]⟩

/-- Normalize real representatives by dividing their time coordinate by their positive period. -/
def realNormalization (n : ℕ∞ω) :
    (PositivePeriod × ℝ) ≃ₘ^n⟮𝓘(ℝ).prod 𝓘(ℝ), 𝓘(ℝ).prod 𝓘(ℝ)⟯
      PositivePeriod × ℝ where
  toFun z := (z.1, z.2 / (z.1 : ℝ))
  invFun z := (z.1, z.2 * (z.1 : ℝ))
  left_inv z := by simp [z.1.property.ne']
  right_inv z := by simp [z.1.property.ne']
  contMDiff_toFun := contMDiff_fst.prodMk (contMDiff_snd.div₀
    (contMDiff_subtype_val.comp contMDiff_fst) fun z ↦ z.1.property.ne')
  contMDiff_invFun := contMDiff_fst.prodMk
    (contMDiff_snd.mul (contMDiff_subtype_val.comp contMDiff_fst))

/-- Real normalization divides the time coordinate by the period. -/
@[simp]
theorem realNormalization_apply (n : ℕ∞ω) (z : PositivePeriod × ℝ) :
    realNormalization n z = (z.1, z.2 / (z.1 : ℝ)) := (rfl)

/-- Inverse real normalization multiplies the normalized time by the period. -/
@[simp]
theorem realNormalization_symm_apply (n : ℕ∞ω) (z : PositivePeriod × ℝ) :
    (realNormalization n).symm z = (z.1, z.2 * (z.1 : ℝ)) := (rfl)

/-- The representative map is a product covering in normalized coordinates. -/
private theorem representative_eq (n : ℕ∞ω) :
    representative = (normalization n).symm ∘
      Prod.map id ((↑) : ℝ → AddCircle (1 : ℝ)) ∘ realNormalization n := by
  funext z
  apply (normalization n).injective
  simp only [Diffeomorph.coe_toEquiv, Function.comp_apply, Diffeomorph.apply_symm_apply,
    realNormalization_apply, Prod.map_apply, id_eq, normalization_representative]

/-- The real representative map is a local diffeomorphism. -/
theorem isLocalDiffeomorph_representative (n : ℕ∞ω) :
    IsLocalDiffeomorph (𝓘(ℝ).prod 𝓘(ℝ)) (𝓘(ℝ).prod 𝓘(ℝ)) n representative := by
  rw [representative_eq n]
  intro z
  have h := (Diffeomorph.refl 𝓘(ℝ) PositivePeriod n).isLocalDiffeomorph.prodMap
    (AddCircle.isLocalDiffeomorph_coe 1 n)
  exact ((realNormalization n).isLocalDiffeomorph z).comp _ _
    ((h _).comp _ _ ((normalization n).symm.isLocalDiffeomorph _))

/-- The real representative map is analytic jointly in the positive period and time. -/
theorem contMDiff_representative (n : ℕ∞ω) :
    ContMDiff (𝓘(ℝ).prod 𝓘(ℝ)) (𝓘(ℝ).prod 𝓘(ℝ)) n representative :=
  (isLocalDiffeomorph_representative n).contMDiff

/-- The real representative map is a covering of the dependent total family. -/
theorem isCoveringMap_representative : IsCoveringMap representative := by
  rw [representative_eq 0]
  exact ((IsCoveringMap.id.prodMap (AddCircle.isCoveringMap_coe 1)).comp_homeomorph
    (realNormalization 0).toHomeomorph).homeomorph_comp (normalization 0).symm.toHomeomorph

end CircleFamily

end TauCeti
