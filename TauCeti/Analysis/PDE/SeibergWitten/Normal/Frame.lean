/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import TauCeti.Analysis.InnerProductSpace.AlternatingForm
public import TauCeti.Analysis.PDE.SeibergWitten.Canonical.Line
public import TauCeti.LinearAlgebra.CliffordAlgebra.HalfSpinor
import TauCeti.Analysis.InnerProductSpace.OrthogonalFamily

/-!
# Eight-component normal frame intertwiners for the Seiberg–Witten model

Around a complex curve in an oriented four-manifold with compatible almost complex structure `J`, a
positively oriented `J`-unitary tangent-normal frame `e` (`J e₀ = e₁`, `J e₂ = e₃`) and a unit
canonical spinor `u₀ ∈ W⁺` compare the four-dimensional gauge-fixed linearized Seiberg–Witten
operator between `Ω¹(V) × W⁺` and `ℝ × Λ⁺ V × W⁻` with the planar vortex operators `(L_x, L_x*)`
on pairs `(y, η) ∈ ℝ⁴ × ℝ⁴`.

Using the self-dual orthonormal basis `(ω_u, ρ₁, ρ₂)` of `Λ⁺ V` from
`TauCeti.Analysis.InnerProductSpace.HodgeStar.Kahler.Basic` and the half-spinor frames `(u₀, -β₀)`
of `W⁺` (where `β₀ = pairedSpinor e u₀`) and `(c(e₂) u₀, c(e₀) u₀)` of `W⁻` from
`TauCeti.Analysis.PDE.SeibergWitten.Canonical.Line`,
this file constructs the eight-real-component domain and target linear equivalences
`normalDomainEquiv` and `normalTargetEquiv` together with `normalFrameForm`, `normalFrameSpinor`,
`normalFrameSelfDual`, `normalFrameNegSpinor`, and their weighted component norm identities.

## Main definitions

* `SeibergWitten.normalFrameForm`: the one-form `-η₀ e₀* + η₁ e₁* + y₀ e₂* + y₁ e₃*`.
* `SeibergWitten.normalFrameSpinor`: the spinor `2(y₂ + i y₃) u₀ - 2(η₂ + i η₃) β₀`.
* `SeibergWitten.normalFrameSelfDual`: the self-dual two-vector `L₁ ω_u + A₀ ρ₁ + A₁ ρ₂`.
* `SeibergWitten.normalFrameNegSpinor`: the negative half-spinor
  `2(L₂ + i L₃) c(e₂) u₀ - 2(A₂ + i A₃) c(e₀) u₀`.
* `SeibergWitten.normalDomainEquiv`: the eight-component domain intertwiner
  `(ℝ⁴ × ℝ⁴) ≃L[ℝ] Ω¹(V) × W⁺`.
* `SeibergWitten.normalTargetEquiv`: the eight-component target intertwiner
  `(ℝ⁴ × ℝ⁴) ≃L[ℝ] ℝ × Λ⁺ V × W⁻`.

## Main results

* `SeibergWitten.normalFrameForm_eq_of_apply`: reconstruction of a `1`-form from its
  values on the orthonormal frame `e`.
* `SeibergWitten.alternatingFormInner_normalFrameForm_add_norm_sq_normalFrameSpinor_div_four`:
  weighted domain norm identity `‖b‖² + ‖ζ‖² / 4 = ‖y‖² + ‖η‖²`.
* `SeibergWitten.sq_add_norm_sq_add_norm_sq_div_four_normalTargetEquiv`: weighted target
  norm identity `f² + ‖τ‖² + ‖ν‖² / 4 = ‖L‖² + ‖A‖²`.

## References

* C. H. Taubes, *Gr ⇒ SW: From pseudo-holomorphic curves to Seiberg–Witten solutions*,
  J. Differential Geom. 51 (1999), 203–334, §2–3.
-/

public section

noncomputable section

open CliffordAlgebra Complex Module exteriorPower
open scoped RealInnerProductSpace InnerProductSpace

namespace TauCeti.SeibergWitten

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [Fact (finrank ℝ V = 4)]
  {Q : QuadraticForm ℝ V} {o : Orientation ℝ V (Fin 4)}
  {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
  {ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ W}
  {e : OrthonormalBasis (Fin 4) ℝ V} {J : AlmostComplexStructure V}

attribute [local instance] finiteDimensional_of_finrank_four

/-! ### Eight-real-component weighted-isometric domain and target intertwiners -/

section Intertwiners

omit [Fact (finrank ℝ V = 4)] in
/-- The one-form `-η₀ e₀* + η₁ e₁* + y₀ e₂* + y₁ e₃*` for normal `y` and tangential `η`. -/
def normalFrameForm (e : OrthonormalBasis (Fin 4) ℝ V)
    (y η : EuclideanSpace ℝ (Fin 4)) : V [⋀^Fin 1]→L[ℝ] ℝ :=
  ContinuousAlternatingMap.ofSubsingletonLIE (0 : Fin 1)
    ((-η 0) • innerSL ℝ (e 0) + η 1 • innerSL ℝ (e 1) +
      y 0 • innerSL ℝ (e 2) + y 1 • innerSL ℝ (e 3))

omit [Fact (finrank ℝ V = 4)] in
/-- Definitional unfolding of `normalFrameForm`. -/
theorem normalFrameForm_def (e : OrthonormalBasis (Fin 4) ℝ V)
    (y η : EuclideanSpace ℝ (Fin 4)) :
    normalFrameForm e y η = ContinuousAlternatingMap.ofSubsingletonLIE (0 : Fin 1)
      ((-η 0) • innerSL ℝ (e 0) + η 1 • innerSL ℝ (e 1) +
        y 0 • innerSL ℝ (e 2) + y 1 • innerSL ℝ (e 3)) :=
  (rfl)

omit [Fact (finrank ℝ V = 4)] in
/-- Pointwise evaluation of `normalFrameForm` on a vector `v`. -/
@[simp]
theorem normalFrameForm_apply (e : OrthonormalBasis (Fin 4) ℝ V)
    (y η : EuclideanSpace ℝ (Fin 4)) (v : V) :
    normalFrameForm e y η (fun _ ↦ v) =
      -η 0 * ⟪e 0, v⟫ + η 1 * ⟪e 1, v⟫ + y 0 * ⟪e 2, v⟫ + y 1 * ⟪e 3, v⟫ := by
  simp [normalFrameForm]

omit [Fact (finrank ℝ V = 4)] in
/-- `normalFrameForm` is additive in `(y, η)`. -/
theorem normalFrameForm_add (e : OrthonormalBasis (Fin 4) ℝ V)
    (y₁ y₂ η₁ η₂ : EuclideanSpace ℝ (Fin 4)) :
    normalFrameForm e (y₁ + y₂) (η₁ + η₂) = normalFrameForm e y₁ η₁ + normalFrameForm e y₂ η₂ := by
  simp only [normalFrameForm, ← map_add, PiLp.add_apply]; congr 1; module

omit [Fact (finrank ℝ V = 4)] in
/-- `normalFrameForm` is `ℝ`-homogeneous in `(y, η)`. -/
theorem normalFrameForm_smul (e : OrthonormalBasis (Fin 4) ℝ V) (r : ℝ)
    (y η : EuclideanSpace ℝ (Fin 4)) :
    normalFrameForm e (r • y) (r • η) = r • normalFrameForm e y η := by
  ext v; simp [normalFrameForm]; ring

omit [Fact (finrank ℝ V = 4)] in
/-- `normalFrameForm e` maps `(0, 0)` to `0`. -/
@[simp]
theorem normalFrameForm_zero (e : OrthonormalBasis (Fin 4) ℝ V) :
    normalFrameForm e 0 0 = 0 := by
  ext v; simp [normalFrameForm]

omit [Fact (finrank ℝ V = 4)] in
/-- Any continuous real `1`-form `ω` is reconstructed by `normalFrameForm e` from its frame
evaluations on `e 0, e 1, e 2, e 3`. -/
theorem normalFrameForm_eq_of_apply {e : OrthonormalBasis (Fin 4) ℝ V}
    {y η : EuclideanSpace ℝ (Fin 4)} {ω : V [⋀^Fin 1]→L[ℝ] ℝ}
    (h0 : -η 0 = ω (fun _ ↦ e 0)) (h1 : η 1 = ω (fun _ ↦ e 1))
    (h2 : y 0 = ω (fun _ ↦ e 2)) (h3 : y 1 = ω (fun _ ↦ e 3)) :
    normalFrameForm e y η = ω := by
  apply (ContinuousAlternatingMap.ofSubsingletonLIE (0 : Fin 1)).symm.injective
  ext w
  set L := (ContinuousAlternatingMap.ofSubsingletonLIE (0 : Fin 1)).symm ω
  have hL (v : V) : ω (fun _ ↦ v) = L v := by
    simp [L, ContinuousAlternatingMap.ofSubsingletonLIE_symm_apply]
  conv_rhs => rw [← e.sum_repr' w]
  simp only [normalFrameForm, LinearIsometryEquiv.symm_apply_apply, add_apply, smul_apply,
    innerSL_apply_apply, Fin.sum_univ_four, smul_eq_mul, h0, h1, h2, h3, hL]
  simp only [map_add, map_smul, smul_eq_mul]
  ring

omit [FiniteDimensional ℂ W] in variable (o ρ) in
/-- The positive half-spinor `2(y₂ + i y₃) u₀ - 2(η₂ + i η₃) β₀` in `(u₀, β₀)`. -/
def normalFrameSpinor (e : OrthonormalBasis (Fin 4) ℝ V) (u₀ : positiveHalfSpinors o ρ)
    (y η : EuclideanSpace ℝ (Fin 4)) : positiveHalfSpinors o ρ :=
  ((2 : ℂ) * ((y 2 : ℂ) + (y 3 : ℂ) * I)) • u₀ -
    ((2 : ℂ) * ((η 2 : ℂ) + (η 3 : ℂ) * I)) • pairedSpinor e u₀

omit [FiniteDimensional ℂ W] in
/-- Definitional unfolding of `normalFrameSpinor`. -/
theorem normalFrameSpinor_def (e : OrthonormalBasis (Fin 4) ℝ V) (u₀ : positiveHalfSpinors o ρ)
    (y η : EuclideanSpace ℝ (Fin 4)) :
    normalFrameSpinor o ρ e u₀ y η =
      ((2 : ℂ) * ((y 2 : ℂ) + (y 3 : ℂ) * I)) • u₀ -
        ((2 : ℂ) * ((η 2 : ℂ) + (η 3 : ℂ) * I)) • pairedSpinor e u₀ :=
  (rfl)

omit [FiniteDimensional ℂ W] in variable (o ρ) in
/-- `normalFrameSpinor` is additive in `(y, η)`. -/
theorem normalFrameSpinor_add (e : OrthonormalBasis (Fin 4) ℝ V) (u₀ : positiveHalfSpinors o ρ)
    (y₁ y₂ η₁ η₂ : EuclideanSpace ℝ (Fin 4)) :
    normalFrameSpinor o ρ e u₀ (y₁ + y₂) (η₁ + η₂) =
      normalFrameSpinor o ρ e u₀ y₁ η₁ + normalFrameSpinor o ρ e u₀ y₂ η₂ := by
  simp only [normalFrameSpinor, PiLp.add_apply, ofReal_add]; module

omit [FiniteDimensional ℂ W] in variable (o ρ) in
/-- `normalFrameSpinor` is `ℝ`-homogeneous in `(y, η)`. -/
theorem normalFrameSpinor_smul (e : OrthonormalBasis (Fin 4) ℝ V) (u₀ : positiveHalfSpinors o ρ)
    (r : ℝ) (y η : EuclideanSpace ℝ (Fin 4)) :
    normalFrameSpinor o ρ e u₀ (r • y) (r • η) = r • normalFrameSpinor o ρ e u₀ y η := by
  simp only [normalFrameSpinor, PiLp.smul_apply, smul_eq_mul, ofReal_mul]
  rw [← Complex.coe_smul]; module

omit [FiniteDimensional ℂ W] in variable (o ρ) in
/-- `normalFrameSpinor` maps `(0, 0)` to `0`. -/
@[simp]
theorem normalFrameSpinor_zero (e : OrthonormalBasis (Fin 4) ℝ V) (u₀ : positiveHalfSpinors o ρ) :
    normalFrameSpinor o ρ e u₀ 0 0 = 0 := by
  simp [normalFrameSpinor]

omit [FiniteDimensional ℂ W] in variable (o) in
/-- The self-dual two-vector `L₁ ω_u + A₀ ρ₁ + A₁ ρ₂` in the frame `(ω_u, ρ₁, ρ₂)` of
`Λ⁺ V`. -/
def normalFrameSelfDual (hkl : 2 + 2 = finrank ℝ V) (he : e.toBasis.orientation = o)
    (h₀ : J (e 0) = e 1) (h₂₃ : J (e 2) = e 3) (L A : EuclideanSpace ℝ (Fin 4)) :
    Module.End.eigenspace (o.hodgeStar hkl : Module.End ℝ (⋀[ℝ]^2 V)) 1 :=
  L 1 • J.kahlerSelfDual o hkl (AlmostComplexStructure.hodgeStar_kahlerForm h₀ h₂₃ hkl he) +
    A 0 • AlmostComplexStructure.antiInvariantSelfDual₁ o e hkl he +
    A 1 • AlmostComplexStructure.antiInvariantSelfDual₂ o e hkl he

omit [FiniteDimensional ℂ W] in variable (o) in
/-- Definitional unfolding of `normalFrameSelfDual`. -/
theorem normalFrameSelfDual_def (hkl : 2 + 2 = finrank ℝ V) (he : e.toBasis.orientation = o)
    (h₀ : J (e 0) = e 1) (h₂₃ : J (e 2) = e 3) (L A : EuclideanSpace ℝ (Fin 4)) :
    normalFrameSelfDual o hkl he h₀ h₂₃ L A =
      L 1 • J.kahlerSelfDual o hkl (AlmostComplexStructure.hodgeStar_kahlerForm h₀ h₂₃ hkl he) +
        A 0 • AlmostComplexStructure.antiInvariantSelfDual₁ o e hkl he +
        A 1 • AlmostComplexStructure.antiInvariantSelfDual₂ o e hkl he :=
  (rfl)

omit [FiniteDimensional ℂ W] in variable (o) in
/-- `normalFrameSelfDual` is additive in `(L, A)`. -/
theorem normalFrameSelfDual_add (hkl : 2 + 2 = finrank ℝ V) (he : e.toBasis.orientation = o)
    (h₀ : J (e 0) = e 1) (h₂₃ : J (e 2) = e 3)
    (L₁ L₂ A₁ A₂ : EuclideanSpace ℝ (Fin 4)) :
    normalFrameSelfDual o hkl he h₀ h₂₃ (L₁ + L₂) (A₁ + A₂) =
      normalFrameSelfDual o hkl he h₀ h₂₃ L₁ A₁ +
        normalFrameSelfDual o hkl he h₀ h₂₃ L₂ A₂ := by
  simp only [normalFrameSelfDual, PiLp.add_apply]; module

omit [FiniteDimensional ℂ W] in variable (o) in
/-- `normalFrameSelfDual` is `ℝ`-homogeneous in `(L, A)`. -/
theorem normalFrameSelfDual_smul (hkl : 2 + 2 = finrank ℝ V) (he : e.toBasis.orientation = o)
    (h₀ : J (e 0) = e 1) (h₂₃ : J (e 2) = e 3) (r : ℝ)
    (L A : EuclideanSpace ℝ (Fin 4)) :
    normalFrameSelfDual o hkl he h₀ h₂₃ (r • L) (r • A) =
      r • normalFrameSelfDual o hkl he h₀ h₂₃ L A := by
  simp only [normalFrameSelfDual, PiLp.smul_apply, smul_eq_mul]; module

omit [FiniteDimensional ℂ W] in variable (o) in
/-- `normalFrameSelfDual` maps `(0, 0)` to `0`. -/
@[simp]
theorem normalFrameSelfDual_zero (hkl : 2 + 2 = finrank ℝ V) (he : e.toBasis.orientation = o)
    (h₀ : J (e 0) = e 1) (h₂₃ : J (e 2) = e 3) :
    normalFrameSelfDual o hkl he h₀ h₂₃ 0 0 = 0 := by
  simp [normalFrameSelfDual]

variable (o ρ) in
private abbrev positiveHalfSpinorsEquiv :
    positiveHalfSpinors o ρ ≃ₗ[ℂ] Module.End.eigenspace (ρ (chirality Q o)) 1 :=
  LinearEquiv.ofEq _ _ (positiveHalfSpinors_eq_eigenspace o ρ)

omit [FiniteDimensional ℂ W] in variable (o ρ) in
/-- The negative half-spinor `2(L₂ + i L₃) c(e₂) u₀ - 2(A₂ + i A₃) c(e₀) u₀` in the frame
`(c(e₂) u₀, c(e₀) u₀)` of `W⁻`. -/
def normalFrameNegSpinor (e : OrthonormalBasis (Fin 4) ℝ V) (u₀ : positiveHalfSpinors o ρ)
    (L A : EuclideanSpace ℝ (Fin 4)) : Module.End.eigenspace (ρ (chirality Q o)) (-1) :=
  ((2 : ℂ) * ((L 2 : ℂ) + (L 3 : ℂ) * I)) •
      halfSpinCliffordMul o ρ 1 (e 2) (positiveHalfSpinorsEquiv o ρ u₀) -
    ((2 : ℂ) * ((A 2 : ℂ) + (A 3 : ℂ) * I)) •
      halfSpinCliffordMul o ρ 1 (e 0) (positiveHalfSpinorsEquiv o ρ u₀)

omit [FiniteDimensional ℂ W] in
/-- Definitional unfolding of `normalFrameNegSpinor`. -/
theorem normalFrameNegSpinor_def (e : OrthonormalBasis (Fin 4) ℝ V) (u₀ : positiveHalfSpinors o ρ)
    (L A : EuclideanSpace ℝ (Fin 4)) :
    let ePos := LinearEquiv.ofEq _ _ (positiveHalfSpinors_eq_eigenspace o ρ)
    normalFrameNegSpinor o ρ e u₀ L A =
      ((2 : ℂ) * ((L 2 : ℂ) + (L 3 : ℂ) * I)) • halfSpinCliffordMul o ρ 1 (e 2) (ePos u₀) -
        ((2 : ℂ) * ((A 2 : ℂ) + (A 3 : ℂ) * I)) • halfSpinCliffordMul o ρ 1 (e 0) (ePos u₀) :=
  (rfl)

omit [FiniteDimensional ℂ W] in variable (o ρ) in
/-- `normalFrameNegSpinor` is additive in `(L, A)`. -/
theorem normalFrameNegSpinor_add (e : OrthonormalBasis (Fin 4) ℝ V) (u₀ : positiveHalfSpinors o ρ)
    (L₁ L₂ A₁ A₂ : EuclideanSpace ℝ (Fin 4)) :
    normalFrameNegSpinor o ρ e u₀ (L₁ + L₂) (A₁ + A₂) =
      normalFrameNegSpinor o ρ e u₀ L₁ A₁ + normalFrameNegSpinor o ρ e u₀ L₂ A₂ := by
  simp only [normalFrameNegSpinor, PiLp.add_apply, ofReal_add]; module

omit [FiniteDimensional ℂ W] in variable (o ρ) in
/-- `normalFrameNegSpinor` is `ℝ`-homogeneous in `(L, A)`. -/
theorem normalFrameNegSpinor_smul (e : OrthonormalBasis (Fin 4) ℝ V) (u₀ : positiveHalfSpinors o ρ)
    (r : ℝ) (L A : EuclideanSpace ℝ (Fin 4)) :
    normalFrameNegSpinor o ρ e u₀ (r • L) (r • A) = r • normalFrameNegSpinor o ρ e u₀ L A := by
  simp only [normalFrameNegSpinor, PiLp.smul_apply, smul_eq_mul, ofReal_mul]
  rw [← Complex.coe_smul]; module

omit [FiniteDimensional ℂ W] in variable (o ρ) in
/-- `normalFrameNegSpinor` maps `(0, 0)` to `0`. -/
@[simp]
theorem normalFrameNegSpinor_zero (e : OrthonormalBasis (Fin 4) ℝ V)
    (u₀ : positiveHalfSpinors o ρ) :
    normalFrameNegSpinor o ρ e u₀ 0 0 = 0 := by
  simp [normalFrameNegSpinor]

private theorem inner_sub_smul_re_im_of_orthonormal {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] {a b : H} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hab : ⟪a, b⟫_ℂ = 0)
    (x₂ x₃ y₂ y₃ : ℝ) :
    let s : H := ((2 : ℂ) * (x₂ + x₃ * I)) • a - ((2 : ℂ) * (y₂ + y₃ * I)) • b
    (⟪a, s⟫_ℂ).re / 2 = x₂ ∧ (⟪a, s⟫_ℂ).im / 2 = x₃ ∧
      -(⟪b, s⟫_ℂ).re / 2 = y₂ ∧ -(⟪b, s⟫_ℂ).im / 2 = y₃ := by
  intro s
  have h₁ := inner_smul_add_smul_of_inner_eq_zero_left ha hab
    ((2 : ℂ) * (x₂ + x₃ * I)) (-((2 : ℂ) * (y₂ + y₃ * I)))
  have h₂ := inner_smul_add_smul_of_inner_eq_zero_right hb hab
    ((2 : ℂ) * (x₂ + x₃ * I)) (-((2 : ℂ) * (y₂ + y₃ * I)))
  rw [neg_smul, ← sub_eq_add_neg] at h₁ h₂
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (congrArg (fun z : ℂ ↦ z.re / 2) h₁).trans (by simp)
  · exact (congrArg (fun z : ℂ ↦ z.im / 2) h₁).trans (by simp)
  · exact (congrArg (fun z : ℂ ↦ -z.re / 2) h₂).trans (by simp)
  · exact (congrArg (fun z : ℂ ↦ -z.im / 2) h₂).trans (by simp)

private theorem two_mul_re_im_smul_sub_eq {H : Type*} [AddCommGroup H] [Module ℂ H]
    (a b : H) (z₁ z₂ : ℂ) :
    ((2 : ℂ) * (((z₁.re / 2 : ℝ) : ℂ) + ((z₁.im / 2 : ℝ) : ℂ) * I)) • a -
        ((2 : ℂ) * (((-z₂.re / 2 : ℝ) : ℂ) + ((-z₂.im / 2 : ℝ) : ℂ) * I)) • b =
      z₁ • a + z₂ • b := by
  rw [sub_eq_add_neg, ← neg_smul]
  congr 1 <;> congr 1 <;> (apply Complex.ext <;> simp <;> ring)

section Equivs

variable (o ρ) (hQ : ∀ v, Q v = -‖v‖ ^ 2) (hkl : 2 + 2 = finrank ℝ V)
  (he : e.toBasis.orientation = o) (h₀ : J (e 0) = e 1) (h₂₃ : J (e 2) = e 3)
  (h₂ : finrank ℂ (positiveHalfSpinors o ρ) = 2)
  (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v))
  {u₀ : positiveHalfSpinors o ρ} (hu₀ : cliffordProjection o ρ J.kahlerForm u₀ = u₀)
  (hu₀₁ : ‖u₀‖ = 1)
include hQ hkl he h₀ h₂₃ h₂ hρ hu₀ hu₀₁

omit hkl he h₂ in
private theorem normalDomainEquiv_left_inv
    (p : EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4)) :
    let q := (normalFrameForm e p.fst p.snd, normalFrameSpinor o ρ e u₀ p.fst p.snd)
    (!₂[q.fst (fun _ ↦ e 2), q.fst (fun _ ↦ e 3),
        (⟪u₀, q.snd⟫_ℂ).re / 2, (⟪u₀, q.snd⟫_ℂ).im / 2],
     !₂[-q.fst (fun _ ↦ e 0), q.fst (fun _ ↦ e 1),
        -(⟪pairedSpinor e u₀, q.snd⟫_ℂ).re / 2,
        -(⟪pairedSpinor e u₀, q.snd⟫_ℂ).im / 2]) = p := by
  have horth :=
    inner_pairedSpinor_eq_zero_of_cliffordProjection_apply_eq_self hQ h₀ h₂₃ hρ hu₀
  have hβ₀₁ : ‖pairedSpinor e u₀‖ = 1 := norm_pairedSpinor_eq_one hQ hρ hu₀₁
  obtain ⟨hure, huim, hvre, hvim⟩ :=
    inner_sub_smul_re_im_of_orthonormal hu₀₁ hβ₀₁ horth
      (p.fst 2) (p.fst 3) (p.snd 2) (p.snd 3)
  have he_ite := orthonormal_iff_ite.1 e.orthonormal
  exact Prod.ext
    (by ext i; fin_cases i <;>
      first | exact hure | exact huim | simp [normalFrameForm_apply, he_ite])
    (by ext i; fin_cases i <;>
      first | exact hvre | exact hvim | simp [normalFrameForm_apply, he_ite])

private theorem normalDomainEquiv_right_inv
    (q : (V [⋀^Fin 1]→L[ℝ] ℝ) × positiveHalfSpinors o ρ) :
    let y : EuclideanSpace ℝ (Fin 4) :=
      !₂[q.fst (fun _ ↦ e 2), q.fst (fun _ ↦ e 3),
        (⟪u₀, q.snd⟫_ℂ).re / 2, (⟪u₀, q.snd⟫_ℂ).im / 2]
    let η : EuclideanSpace ℝ (Fin 4) :=
      !₂[-q.fst (fun _ ↦ e 0), q.fst (fun _ ↦ e 1),
         -(⟪pairedSpinor e u₀, q.snd⟫_ℂ).re / 2,
         -(⟪pairedSpinor e u₀, q.snd⟫_ℂ).im / 2]
    (normalFrameForm e y η, normalFrameSpinor o ρ e u₀ y η) = q :=
  Prod.ext
    (normalFrameForm_eq_of_apply (by simp) (by simp) (by simp) (by simp))
    (by
      conv_rhs =>
        rw [eq_inner_smul_add_inner_pairedSpinor_smul hQ hkl he h₀ h₂₃ h₂ hρ
          hu₀ hu₀₁ q.snd]
      simpa [normalFrameSpinor] using
        two_mul_re_im_smul_sub_eq u₀ (pairedSpinor e u₀) ⟪u₀, q.snd⟫_ℂ ⟪pairedSpinor e u₀, q.snd⟫_ℂ)

/-- **The eight-component domain frame intertwiner** `(y, η) ≃ (b, ζ) ∈ Ω¹(V) × W⁺`. -/
def normalDomainEquiv :
    (EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4)) ≃L[ℝ]
      (V [⋀^Fin 1]→L[ℝ] ℝ) × positiveHalfSpinors o ρ :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun p := (normalFrameForm e p.fst p.snd, normalFrameSpinor o ρ e u₀ p.fst p.snd)
      map_add' p q := Prod.ext (normalFrameForm_add e p.fst q.fst p.snd q.snd)
        (normalFrameSpinor_add o ρ e u₀ p.fst q.fst p.snd q.snd)
      map_smul' r p := Prod.ext (normalFrameForm_smul e r p.fst p.snd)
        (normalFrameSpinor_smul o ρ e u₀ r p.fst p.snd)
      invFun q :=
        (!₂[q.fst (fun _ ↦ e 2), q.fst (fun _ ↦ e 3),
            (⟪u₀, q.snd⟫_ℂ).re / 2, (⟪u₀, q.snd⟫_ℂ).im / 2],
         !₂[-q.fst (fun _ ↦ e 0), q.fst (fun _ ↦ e 1),
            -(⟪pairedSpinor e u₀, q.snd⟫_ℂ).re / 2,
            -(⟪pairedSpinor e u₀, q.snd⟫_ℂ).im / 2])
      left_inv := normalDomainEquiv_left_inv o ρ hQ h₀ h₂₃ hρ hu₀ hu₀₁
      right_inv := normalDomainEquiv_right_inv o ρ hQ hkl he h₀ h₂₃ h₂ hρ hu₀ hu₀₁ }

/-- Pointwise formula for `normalDomainEquiv`. -/
@[simp]
theorem normalDomainEquiv_apply (p : EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4)) :
    normalDomainEquiv o ρ hQ hkl he h₀ h₂₃ h₂ hρ hu₀ hu₀₁ p =
      (normalFrameForm e p.fst p.snd, normalFrameSpinor o ρ e u₀ p.fst p.snd) :=
  (rfl)

/-- Pointwise formula for the inverse of `normalDomainEquiv`. -/
@[simp]
theorem normalDomainEquiv_symm_apply (q : (V [⋀^Fin 1]→L[ℝ] ℝ) × positiveHalfSpinors o ρ) :
    (normalDomainEquiv o ρ hQ hkl he h₀ h₂₃ h₂ hρ hu₀ hu₀₁).symm q =
      (!₂[q.fst (fun _ ↦ e 2), q.fst (fun _ ↦ e 3),
          (⟪u₀, q.snd⟫_ℂ).re / 2, (⟪u₀, q.snd⟫_ℂ).im / 2],
       !₂[-q.fst (fun _ ↦ e 0), q.fst (fun _ ↦ e 1),
          -(⟪pairedSpinor e u₀, q.snd⟫_ℂ).re / 2,
          -(⟪pairedSpinor e u₀, q.snd⟫_ℂ).im / 2]) :=
  (rfl)

omit hkl he h₂ in
/-- Weighted component norm identity for `(normalFrameForm e y η, normalFrameSpinor o ρ e u₀ y η)`:
`‖b‖² + ‖ζ‖² / 4 = ‖y‖² + ‖η‖²`. -/
theorem alternatingFormInner_normalFrameForm_add_norm_sq_normalFrameSpinor_div_four
    (y η : EuclideanSpace ℝ (Fin 4)) :
    alternatingFormInner V 1 (normalFrameForm e y η) (normalFrameForm e y η) +
        ‖normalFrameSpinor o ρ e u₀ y η‖ ^ 2 / 4 = ‖y‖ ^ 2 + ‖η‖ ^ 2 := by
  have horth :=
    inner_pairedSpinor_eq_zero_of_cliffordProjection_apply_eq_self hQ h₀ h₂₃ hρ hu₀
  have hβ₀₁ : ‖pairedSpinor e u₀‖ = 1 := norm_pairedSpinor_eq_one hQ hρ hu₀₁
  have hform : alternatingFormInner V 1 (normalFrameForm e y η) (normalFrameForm e y η) =
      η 0 ^ 2 + η 1 ^ 2 + y 0 ^ 2 + y 1 ^ 2 := by
    set u : V := (-η 0) • e 0 + η 1 • e 1 + y 0 • e 2 + y 1 • e 3
    have hnf : normalFrameForm e y η = alternatingFormEquiv V 1 (ιMulti ℝ 1 ![u]) := by
      ext v
      have hv : v = ![v 0] := funext fun i ↦ by fin_cases i; rfl
      rw [hv, alternatingFormEquiv_ιMulti_apply, Matrix.det_fin_one]
      simp [normalFrameForm, u, inner_add_left, real_inner_smul_left]
    rw [hnf, alternatingFormInner_alternatingFormEquiv, ← alternatingFormEquiv_apply,
      alternatingFormEquiv_ιMulti_apply, Matrix.det_fin_one]
    simp only [Matrix.of_apply, Matrix.cons_val_zero, u, inner_add_left, inner_add_right,
      real_inner_smul_left, real_inner_smul_right, orthonormal_iff_ite.1 e.orthonormal]
    norm_num; ring
  rw [hform, normalFrameSpinor, sub_eq_add_neg, ← neg_smul,
    norm_smul_add_smul_sq_of_inner_eq_zero hu₀₁ hβ₀₁ horth,
    ← normSq_eq_norm_sq, ← normSq_eq_norm_sq, EuclideanSpace.real_norm_sq_eq y,
    EuclideanSpace.real_norm_sq_eq η, Fin.sum_univ_four, Fin.sum_univ_four]
  simp [normSq_apply]; ring

omit hQ hkl h₂ hρ hu₀ hu₀₁ in
private def normalTargetInv (u₀ : positiveHalfSpinors o ρ)
    (q : ℝ × Module.End.eigenspace (o.hodgeStar hkl : Module.End ℝ (⋀[ℝ]^2 V)) 1 ×
      Module.End.eigenspace (ρ (chirality Q o)) (-1)) :
    EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4) :=
  (!₂[q.fst,
      ⟪J.kahlerSelfDual o hkl (AlmostComplexStructure.hodgeStar_kahlerForm h₀ h₂₃ hkl he),
        q.snd.fst⟫,
      (⟪halfSpinCliffordMul o ρ 1 (e 2) (positiveHalfSpinorsEquiv o ρ u₀), q.snd.snd⟫_ℂ).re / 2,
      (⟪halfSpinCliffordMul o ρ 1 (e 2) (positiveHalfSpinorsEquiv o ρ u₀), q.snd.snd⟫_ℂ).im / 2],
   !₂[⟪AlmostComplexStructure.antiInvariantSelfDual₁ o e hkl he, q.snd.fst⟫,
      ⟪AlmostComplexStructure.antiInvariantSelfDual₂ o e hkl he, q.snd.fst⟫,
      -(⟪halfSpinCliffordMul o ρ 1 (e 0) (positiveHalfSpinorsEquiv o ρ u₀), q.snd.snd⟫_ℂ).re / 2,
      -(⟪halfSpinCliffordMul o ρ 1 (e 0) (positiveHalfSpinorsEquiv o ρ u₀),
        q.snd.snd⟫_ℂ).im / 2])

omit h₂ in
private theorem normalTargetEquiv_left_inv
    (p : EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4)) :
    normalTargetInv o ρ hkl he h₀ h₂₃ u₀
        (p.fst 0, normalFrameSelfDual o hkl he h₀ h₂₃ p.fst p.snd,
          normalFrameNegSpinor o ρ e u₀ p.fst p.snd) = p := by
  let b := J.selfDualOrthonormalBasis o e hkl he h₀ h₂₃
  let τ := normalFrameSelfDual o hkl he h₀ h₂₃ p.fst p.snd
  have hb (i : Fin 3) : ⟪b i, τ⟫ = ![p.fst.ofLp 1, p.snd.ofLp 0, p.snd.ofLp 1] i := by
    simpa [b, τ, normalFrameSelfDual, Fin.sum_univ_three] using
      b.orthonormal.inner_right_fintype ![p.fst.ofLp 1, p.snd.ofLp 0, p.snd.ofLp 1] i
  have hsd0 : ⟪J.kahlerSelfDual o hkl
        (AlmostComplexStructure.hodgeStar_kahlerForm h₀ h₂₃ hkl he), τ⟫ =
      p.fst.ofLp 1 := by
    simpa [b] using hb 0
  have hsd1 : ⟪AlmostComplexStructure.antiInvariantSelfDual₁ o e hkl he, τ⟫ =
      p.snd.ofLp 0 := by
    simpa [b] using hb 1
  have hsd2 : ⟪AlmostComplexStructure.antiInvariantSelfDual₂ o e hkl he, τ⟫ =
      p.snd.ofLp 1 := by
    simpa [b] using hb 2
  have hn (i : Fin 4) :
      ‖halfSpinCliffordMul o ρ 1 (e i) (positiveHalfSpinorsEquiv o ρ u₀)‖ = 1 :=
    norm_halfSpinCliffordMul_ofEq_eq_one hQ hρ (e.orthonormal.1 i) hu₀₁
  have hw₂₀ := inner_halfSpinCliffordMul_two_zero hQ h₀ h₂₃ hρ hu₀
  obtain ⟨h2re, h2im, h0re, h0im⟩ :=
    inner_sub_smul_re_im_of_orthonormal (hn 2) (hn 0) hw₂₀
      (p.fst 2) (p.fst 3) (p.snd 2) (p.snd 3)
  simp only [normalTargetInv]
  refine Prod.ext ?_ ?_
  · ext i; fin_cases i
    · simp
    · exact hsd0
    · simpa [normalFrameNegSpinor] using h2re
    · simpa [normalFrameNegSpinor] using h2im
  · ext i; fin_cases i
    · exact hsd1
    · exact hsd2
    · simpa [normalFrameNegSpinor] using h0re
    · simpa [normalFrameNegSpinor] using h0im

private theorem normalTargetEquiv_right_inv
    (q : ℝ × Module.End.eigenspace (o.hodgeStar hkl : Module.End ℝ (⋀[ℝ]^2 V)) 1 ×
      Module.End.eigenspace (ρ (chirality Q o)) (-1)) :
    let p := normalTargetInv o ρ hkl he h₀ h₂₃ u₀ q
    (p.fst 0, normalFrameSelfDual o hkl he h₀ h₂₃ p.fst p.snd,
      normalFrameNegSpinor o ρ e u₀ p.fst p.snd) = q :=
  Prod.ext (by simp [normalTargetInv]) <| Prod.ext
    (by
      simpa [normalTargetInv, normalFrameSelfDual] using
        (AlmostComplexStructure.eq_inner_kahlerSelfDual_add_antiInvariantSelfDual
          (e := e) (he := he) (h₀ := h₀) (h₂ := h₂₃)
          (AlmostComplexStructure.hodgeStar_kahlerForm h₀ h₂₃ hkl he) q.snd.fst).symm)
    (by
      conv_rhs =>
        rw [eq_inner_halfSpinCliffordMul hQ hkl he h₀ h₂₃ h₂ hρ hu₀ hu₀₁ q.snd.snd]
      simpa [normalTargetInv, normalFrameNegSpinor] using
        two_mul_re_im_smul_sub_eq
          (halfSpinCliffordMul o ρ 1 (e 2) (positiveHalfSpinorsEquiv o ρ u₀))
          (halfSpinCliffordMul o ρ 1 (e 0) (positiveHalfSpinorsEquiv o ρ u₀)) _ _)

/-- **The eight-component target frame intertwiner** `(L, A) ≃ (f, τ, ν) ∈ ℝ × Λ⁺ V × W⁻`. -/
def normalTargetEquiv :
    (EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4)) ≃L[ℝ]
      ℝ × Module.End.eigenspace (o.hodgeStar hkl : Module.End ℝ (⋀[ℝ]^2 V)) 1 ×
        Module.End.eigenspace (ρ (chirality Q o)) (-1) :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun p :=
        (p.fst 0, normalFrameSelfDual o hkl he h₀ h₂₃ p.fst p.snd,
          normalFrameNegSpinor o ρ e u₀ p.fst p.snd)
      map_add' p q := Prod.ext (by simp) (Prod.ext
        (normalFrameSelfDual_add o hkl he h₀ h₂₃ p.fst q.fst p.snd q.snd)
        (normalFrameNegSpinor_add o ρ e u₀ p.fst q.fst p.snd q.snd))
      map_smul' r p := Prod.ext (by simp) (Prod.ext
        (normalFrameSelfDual_smul o hkl he h₀ h₂₃ r p.fst p.snd)
        (normalFrameNegSpinor_smul o ρ e u₀ r p.fst p.snd))
      invFun := normalTargetInv o ρ hkl he h₀ h₂₃ u₀
      left_inv := normalTargetEquiv_left_inv o ρ hQ hkl he h₀ h₂₃ hρ hu₀ hu₀₁
      right_inv := normalTargetEquiv_right_inv o ρ hQ hkl he h₀ h₂₃ h₂ hρ hu₀ hu₀₁ }

/-- Pointwise formula for `normalTargetEquiv`. -/
@[simp]
theorem normalTargetEquiv_apply (p : EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4)) :
    normalTargetEquiv o ρ hQ hkl he h₀ h₂₃ h₂ hρ hu₀ hu₀₁ p =
      (p.fst 0, normalFrameSelfDual o hkl he h₀ h₂₃ p.fst p.snd,
        normalFrameNegSpinor o ρ e u₀ p.fst p.snd) :=
  (rfl)

/-- Pointwise formula for the inverse of `normalTargetEquiv`. -/
@[simp]
theorem normalTargetEquiv_symm_apply
    (q : ℝ × Module.End.eigenspace (o.hodgeStar hkl : Module.End ℝ (⋀[ℝ]^2 V)) 1 ×
      Module.End.eigenspace (ρ (chirality Q o)) (-1)) :
    let ePos := LinearEquiv.ofEq _ _ (positiveHalfSpinors_eq_eigenspace o ρ)
    (normalTargetEquiv o ρ hQ hkl he h₀ h₂₃ h₂ hρ hu₀ hu₀₁).symm q =
      (!₂[q.fst,
          ⟪J.kahlerSelfDual o hkl (AlmostComplexStructure.hodgeStar_kahlerForm h₀ h₂₃ hkl he),
            q.snd.fst⟫,
          (⟪halfSpinCliffordMul o ρ 1 (e 2) (ePos u₀), q.snd.snd⟫_ℂ).re / 2,
          (⟪halfSpinCliffordMul o ρ 1 (e 2) (ePos u₀), q.snd.snd⟫_ℂ).im / 2],
       !₂[⟪AlmostComplexStructure.antiInvariantSelfDual₁ o e hkl he, q.snd.fst⟫,
          ⟪AlmostComplexStructure.antiInvariantSelfDual₂ o e hkl he, q.snd.fst⟫,
          -(⟪halfSpinCliffordMul o ρ 1 (e 0) (ePos u₀), q.snd.snd⟫_ℂ).re / 2,
          -(⟪halfSpinCliffordMul o ρ 1 (e 0) (ePos u₀), q.snd.snd⟫_ℂ).im / 2]) :=
  (rfl)

/-- Weighted component norm identity for `normalTargetEquiv`:
`f² + ‖τ‖² + ‖ν‖² / 4 = ‖L‖² + ‖A‖²`. -/
theorem sq_add_norm_sq_add_norm_sq_div_four_normalTargetEquiv
    (L A : EuclideanSpace ℝ (Fin 4)) :
    let q := normalTargetEquiv o ρ hQ hkl he h₀ h₂₃ h₂ hρ hu₀ hu₀₁ (L, A)
    q.fst ^ 2 + ‖q.snd.fst‖ ^ 2 + ‖q.snd.snd‖ ^ 2 / 4 = ‖L‖ ^ 2 + ‖A‖ ^ 2 := by
  intro q
  have hq0 : q.fst = L 0 := by simp only [q, normalTargetEquiv_apply]
  have hq1 : ‖q.snd.fst‖ ^ 2 = L 1 ^ 2 + A 0 ^ 2 + A 1 ^ 2 := by
    let b := J.selfDualOrthonormalBasis o e hkl he h₀ h₂₃
    have hsum : ∑ i : Fin 3, (![L 1, A 0, A 1] i) • b i = q.snd.fst := by
      simp [q, b, normalFrameSelfDual, Fin.sum_univ_three]
    rw [← real_inner_self_eq_norm_sq, ← hsum,
      b.orthonormal.inner_sum ![L 1, A 0, A 1] ![L 1, A 0, A 1] Finset.univ, Fin.sum_univ_three]
    simp [sq]
  have hn (i : Fin 4) :
      ‖halfSpinCliffordMul o ρ 1 (e i) (positiveHalfSpinorsEquiv o ρ u₀)‖ = 1 :=
    norm_halfSpinCliffordMul_ofEq_eq_one hQ hρ (e.orthonormal.1 i) hu₀₁
  have hq2 : q.snd.snd =
      ((2 : ℂ) * (L 2 + L 3 * I)) •
          halfSpinCliffordMul o ρ 1 (e 2) (positiveHalfSpinorsEquiv o ρ u₀) +
        ((-2 : ℂ) * (A 2 + A 3 * I)) •
          halfSpinCliffordMul o ρ 1 (e 0) (positiveHalfSpinorsEquiv o ρ u₀) := by
    simp only [q, normalTargetEquiv_apply, normalFrameNegSpinor]; module
  rw [hq0, hq1, hq2, norm_smul_add_smul_sq_of_inner_eq_zero (hn 2) (hn 0)
      (inner_halfSpinCliffordMul_two_zero hQ h₀ h₂₃ hρ hu₀),
    ← normSq_eq_norm_sq, ← normSq_eq_norm_sq, EuclideanSpace.real_norm_sq_eq L,
    EuclideanSpace.real_norm_sq_eq A, Fin.sum_univ_four, Fin.sum_univ_four]
  simp [normSq_apply]; ring

end Equivs
end Intertwiners
end TauCeti.SeibergWitten
