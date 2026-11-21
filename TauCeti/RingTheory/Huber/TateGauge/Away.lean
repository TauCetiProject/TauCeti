/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.LocalizationTopology.Away
public import TauCeti.RingTheory.Huber.TateGauge.Normed

/-!
# Tate gauges on the away localisation `A₀[1/π]`

Let `A₀` be a commutative ring, `π ∈ A₀` a nonzerodivisor such that `A₀` is `π`-adically
separated, and `A` a localisation of `A₀` away from `π`. Endowing `A` with the `π`-adic topology
`TauCeti.Huber.awayTopology π A`, any radius `α ∈ (0, 1)` produces a norm datum
`TauCeti.Huber.awayTateNormDatum` with ring of definition `(algebraMap A₀ A).range` and
pseudo-uniformiser `π`, and hence a compatible ultrametric `NormedCommRing` structure
`TauCeti.Huber.awayNormedCommRing` on `A` whose underlying ring, uniform space, and topology
agree definitionally with those already on `A`.

When `A₀` is additionally `π`-adically precomplete, `awayNormedCommRing` is complete; when `A` is
nontrivial, it is a normalised normed Tate ring in which `π` is a multiplicative pseudo-uniformiser
of norm `α`. None of these structures are registered as global instances.

## Main definitions

* `TauCeti.Huber.awayTateNormDatum`: the `TateNormDatum A` attached to `(algebraMap A₀ A).range`,
  `π`, and `α ∈ (0, 1)` for any topology with basis `πⁿ A₀`.
* `TauCeti.Huber.awayNormedCommRing`: the ultrametric `NormedCommRing A` induced by the
  `π`-adic Tate gauge of radius `α ∈ (0, 1)`.

## Main results

* `TauCeti.Huber.completeSpace_awayNormedCommRing`,
  `TauCeti.Huber.isUltrametricDist_awayNormedCommRing`,
  `TauCeti.Huber.normOneClass_awayNormedCommRing`,
  `TauCeti.Huber.isTate_awayNormedCommRing`: Banach–Tate properties of `awayNormedCommRing`.
* `TauCeti.Huber.norm_le_one_iff_awayNormedCommRing`: the closed unit ball is the image of `A₀`.
* `TauCeti.Huber.norm_pseudoUniformizer_zpow_mul_awayNormedCommRing`,
  `TauCeti.Huber.norm_pseudoUniformizer_mul_awayNormedCommRing`,
  `TauCeti.Huber.norm_pseudoUniformizer_awayNormedCommRing`: scaling and norm of `π`.
-/

public noncomputable section

open Filter Topology
open scoped nonZeroDivisors

namespace TauCeti.Huber

section AwayDatum

variable {A₀ : Type*} [CommRing A₀] {π : A₀} {A : Type*} [CommRing A] [Algebra A₀ A]
  [IsLocalization.Away π A] [TopologicalSpace A]
  (hb : (𝓝 (0 : A)).HasBasis (fun _ : ℕ ↦ True) fun n ↦ (awayNhd π A n : Set A))

section Datum

variable [SeparatelyContinuousAdd A]

/-- The `TateNormDatum` on `A₀[1/π]` given by the ring of definition `(algebraMap A₀ A).range`,
the pseudo-uniformiser `π`, and a chosen radius `α ∈ (0, 1)`. -/
def awayTateNormDatum {α : ℝ} (hα₀ : 0 < α) (hα₁ : α < 1) : TateNormDatum A where
  ringOfDefinition := (algebraMap A₀ A).range
  isOpen_ringOfDefinition := isOpen_range_algebraMap_of_hasBasis hb
  isBounded_ringOfDefinition := isBounded_range_algebraMap_of_hasBasis hb
  pseudoUniformizer := (IsLocalization.Away.algebraMap_isUnit π).unit
  isTopologicallyNilpotent_pseudoUniformizer :=
    (isPseudoUniformizer_algebraMap_of_hasBasis hb).isTopologicallyNilpotent
  pseudoUniformizer_mem := ⟨π, rfl⟩
  radius := α
  radius_pos := hα₀
  radius_lt_one := hα₁

@[simp] theorem awayTateNormDatum_ringOfDefinition {α : ℝ} (hα₀ : 0 < α) (hα₁ : α < 1) :
    (awayTateNormDatum hb hα₀ hα₁).ringOfDefinition = (algebraMap A₀ A).range := (rfl)

@[simp] theorem awayTateNormDatum_pseudoUniformizer {α : ℝ} (hα₀ : 0 < α) (hα₁ : α < 1) :
    (awayTateNormDatum hb hα₀ hα₁).pseudoUniformizer =
      (IsLocalization.Away.algebraMap_isUnit π).unit := (rfl)

theorem coe_awayTateNormDatum_pseudoUniformizer {α : ℝ} (hα₀ : 0 < α) (hα₁ : α < 1) :
    ((awayTateNormDatum hb hα₀ hα₁).pseudoUniformizer : A) = algebraMap A₀ A π := (rfl)

@[simp] theorem awayTateNormDatum_radius {α : ℝ} (hα₀ : 0 < α) (hα₁ : α < 1) :
    (awayTateNormDatum hb hα₀ hα₁).radius = α := (rfl)

end Datum

variable [IsTopologicalRing A]

/-- The closed unit ball of the `π`-adic Tate gauge on `A₀[1/π]` is the image of `A₀`. -/
theorem tateNorm_le_one_iff_awayTateNormDatum {α : ℝ} (hα₀ : 0 < α) (hα₁ : α < 1) {x : A} :
    tateNorm (awayTateNormDatum hb hα₀ hα₁) x ≤ 1 ↔ x ∈ (algebraMap A₀ A).range := by
  simpa using tateNorm_le_zpow_iff (awayTateNormDatum hb hα₀ hα₁) (x := x) (n := 0)

/-- When `A₀` is `π`-adically separated, `π` is a nonzerodivisor, and `A` is nontrivial, the
element `π` has norm `α` in the `π`-adic Tate gauge of radius `α`. -/
theorem tateNorm_pseudoUniformizer_awayTateNormDatum (hπ : π ∈ A₀⁰)
    [IsHausdorff (Ideal.span {π}) A₀] [Nontrivial A] {α : ℝ} (hα₀ : 0 < α) (hα₁ : α < 1) :
    tateNorm (awayTateNormDatum hb hα₀ hα₁) (algebraMap A₀ A π) = α := by
  have : T2Space A := t2Space_of_hasBasis hb hπ
  simpa [coe_awayTateNormDatum_pseudoUniformizer] using
    tateNorm_pseudoUniformizer_mul (awayTateNormDatum hb hα₀ hα₁) 1

end AwayDatum

section AwayNormedCommRing

variable {A₀ : Type*} [CommRing A₀] (π : A₀) (A : Type*) [CommRing A] [Algebra A₀ A]
  [IsLocalization.Away π A] (hπ : π ∈ A₀⁰) [IsHausdorff (Ideal.span {π}) A₀]

/-- The ultrametric `NormedCommRing` structure on `A₀[1/π]` induced by the `π`-adic Tate gauge of
radius `α ∈ (0, 1)`.

Its underlying `CommRing`, `UniformSpace`, and `TopologicalSpace` structures are definitionally
`‹CommRing A›`, `awayUniformSpace π A`, and `awayTopology π A`, independent of `α`. It is not
registered as a global instance. -/
abbrev awayNormedCommRing {α : ℝ} (hα₀ : 0 < α) (hα₁ : α < 1) : NormedCommRing A :=
  letI : UniformSpace A := awayUniformSpace π A
  haveI : IsTopologicalRing A := isTopologicalRing_awayTopology (π := π)
  haveI : IsUniformAddGroup A := isUniformAddGroup_awayUniformSpace (π := π) (A := A)
  haveI : T2Space A :=
    t2Space_of_hasBasis (hasBasis_nhds_zero_awayTopology (π := π) (A := A)) hπ
  tateNormedCommRing
    (awayTateNormDatum (hasBasis_nhds_zero_awayTopology (π := π) (A := A)) hα₀ hα₁)

variable {α : ℝ} (hα₀ : 0 < α) (hα₁ : α < 1)

theorem commRing_awayNormedCommRing :
    (awayNormedCommRing π A hπ hα₀ hα₁).toCommRing = (inferInstance : CommRing A) := (rfl)

theorem uniformSpace_awayNormedCommRing :
    (awayNormedCommRing π A hπ hα₀ hα₁).toUniformSpace = awayUniformSpace π A := (rfl)

theorem topologicalSpace_awayNormedCommRing :
    (awayNormedCommRing π A hπ hα₀ hα₁).toUniformSpace.toTopologicalSpace =
      awayTopology π A := (rfl)

theorem hasBasis_nhds_zero_awayNormedCommRing :
    letI := awayNormedCommRing π A hπ hα₀ hα₁
    (𝓝 (0 : A)).HasBasis (fun _ : ℕ ↦ True) fun n ↦ (awayNhd π A n : Set A) :=
  hasBasis_nhds_zero_awayTopology (π := π) (A := A)

theorem norm_awayNormedCommRing (x : A) :
    letI := awayNormedCommRing π A hπ hα₀ hα₁
    ‖x‖ = tateNorm
      (awayTateNormDatum (hasBasis_nhds_zero_awayNormedCommRing π A hπ hα₀ hα₁) hα₀ hα₁) x := by
  let := awayNormedCommRing π A hπ hα₀ hα₁
  exact norm_tateNormedCommRing
    (awayTateNormDatum (hasBasis_nhds_zero_awayNormedCommRing π A hπ hα₀ hα₁) hα₀ hα₁) x

/-- `A₀[1/π]` is complete for the `π`-adic Tate gauge of any radius `α ∈ (0, 1)` when `A₀` is
`π`-adically precomplete. -/
theorem completeSpace_awayNormedCommRing [IsPrecomplete (Ideal.span {π}) A₀] :
    letI := awayNormedCommRing π A hπ hα₀ hα₁
    CompleteSpace A := by
  let := awayNormedCommRing π A hπ hα₀ hα₁
  exact completeSpace_of_hasBasis (hasBasis_nhds_zero_awayNormedCommRing π A hπ hα₀ hα₁) hπ

/-- The `π`-adic Tate gauge on `A₀[1/π]` is ultrametric. -/
theorem isUltrametricDist_awayNormedCommRing :
    letI := awayNormedCommRing π A hπ hα₀ hα₁
    IsUltrametricDist A := by
  let := awayNormedCommRing π A hπ hα₀ hα₁
  exact isUltrametricDist_tateNormedCommRing
    (awayTateNormDatum (hasBasis_nhds_zero_awayNormedCommRing π A hπ hα₀ hα₁) hα₀ hα₁)

/-- `‖1‖ = 1` for the `π`-adic Tate gauge on a nontrivial localisation `A₀[1/π]`. -/
theorem normOneClass_awayNormedCommRing [Nontrivial A] :
    letI := awayNormedCommRing π A hπ hα₀ hα₁
    NormOneClass A := by
  let := awayNormedCommRing π A hπ hα₀ hα₁
  exact normOneClass_tateNormedCommRing
    (awayTateNormDatum (hasBasis_nhds_zero_awayNormedCommRing π A hπ hα₀ hα₁) hα₀ hα₁)

/-- A nontrivial localisation `A₀[1/π]` with the `π`-adic Tate gauge is a normed Tate ring. -/
theorem isTate_awayNormedCommRing [Nontrivial A] :
    letI := awayNormedCommRing π A hπ hα₀ hα₁
    NormedRing.IsTate A := by
  let := awayNormedCommRing π A hπ hα₀ hα₁
  exact isTate_tateNormedCommRing
    (awayTateNormDatum (hasBasis_nhds_zero_awayNormedCommRing π A hπ hα₀ hα₁) hα₀ hα₁)

theorem norm_le_one_iff_awayNormedCommRing {x : A} :
    letI := awayNormedCommRing π A hπ hα₀ hα₁
    ‖x‖ ≤ 1 ↔ x ∈ (algebraMap A₀ A).range := by
  let := awayNormedCommRing π A hπ hα₀ hα₁
  rw [norm_awayNormedCommRing]
  exact tateNorm_le_one_iff_awayTateNormDatum
    (hasBasis_nhds_zero_awayNormedCommRing π A hπ hα₀ hα₁) hα₀ hα₁

theorem norm_pseudoUniformizer_zpow_mul_awayNormedCommRing (k : ℤ) (x : A) :
    letI := awayNormedCommRing π A hπ hα₀ hα₁
    ‖(((IsLocalization.Away.algebraMap_isUnit π).unit ^ k : Aˣ) : A) * x‖ = α ^ k * ‖x‖ := by
  let := awayNormedCommRing π A hπ hα₀ hα₁
  rw [norm_awayNormedCommRing, norm_awayNormedCommRing]
  simpa only [awayTateNormDatum_pseudoUniformizer, awayTateNormDatum_radius] using
    tateNorm_zpow_mul
      (awayTateNormDatum (hasBasis_nhds_zero_awayNormedCommRing π A hπ hα₀ hα₁) hα₀ hα₁) k x

theorem norm_pseudoUniformizer_mul_awayNormedCommRing (x : A) :
    letI := awayNormedCommRing π A hπ hα₀ hα₁
    ‖algebraMap A₀ A π * x‖ = α * ‖x‖ := by
  let := awayNormedCommRing π A hπ hα₀ hα₁
  rw [norm_awayNormedCommRing, norm_awayNormedCommRing]
  simpa only [coe_awayTateNormDatum_pseudoUniformizer, awayTateNormDatum_radius] using
    tateNorm_pseudoUniformizer_mul
      (awayTateNormDatum (hasBasis_nhds_zero_awayNormedCommRing π A hπ hα₀ hα₁) hα₀ hα₁) x

theorem norm_pseudoUniformizer_awayNormedCommRing [Nontrivial A] :
    letI := awayNormedCommRing π A hπ hα₀ hα₁
    ‖algebraMap A₀ A π‖ = α := by
  let := awayNormedCommRing π A hπ hα₀ hα₁
  rw [norm_awayNormedCommRing]
  exact tateNorm_pseudoUniformizer_awayTateNormDatum
    (hasBasis_nhds_zero_awayNormedCommRing π A hπ hα₀ hα₁) hπ hα₀ hα₁

end AwayNormedCommRing

end TauCeti.Huber
