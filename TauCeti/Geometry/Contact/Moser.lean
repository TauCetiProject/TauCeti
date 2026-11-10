/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Contact.Flat
public import TauCeti.Geometry.Manifold.DifferentialForm.LieDeriv
import TauCeti.Geometry.Manifold.DifferentialForm.Wedge.Leibniz
import TauCeti.Geometry.Manifold.VectorBundle.Hom
import TauCeti.Geometry.Manifold.VectorBundle.Scalar
import TauCeti.Geometry.Manifold.VectorBundle.Translate

/-!
# The horizontal contact-Moser equation

For a contact form `α` and a one-form `β`, the horizontal contact-Moser equation is
`α(Y) = 0`, `(ι_Y dα + β)|ker α = 0`. Its unique solution is
`Y = (α♭)⁻¹ (β(R_α) α - β)`, where `α♭` is the contact flat map.
We construct this vector field, prove its smoothness, and characterize its value using only
these equations. It vanishes precisely where `β` annihilates the contact hyperplane. For families
`α m`, `β m` depending smoothly on a parameter `m`, evaluated along a smooth map `b`, the vectors
`Y_m(b m)` depend smoothly on `m`
(`TauCeti.SmoothForm.contMDiffAt_sectionAlong_contactMoserVectorField`).

For a family `α_t`, take `β = ∂t α_t`. Replacing a local defining form by `f_t α_t`
replaces this pair by `(f_t α_t, f_t β + (∂t f_t) α_t)`. The solution is unchanged,
even for negative multipliers. This independence allows the local solutions to agree across
noncooriented contact charts. The resulting infinitesimal identity is
`L_Y α + β = β(R_α) α`. This file proves the equation and the change-of-form law,
not existence of its time-dependent flow or an isotopy theorem.

The construction uses the inverse contact flat map from
`TauCeti.Geometry.Contact.Flat`, as in the construction of contact Hamiltonian vector fields.

## References

* H. Geiges, *An Introduction to Contact Topology*, Cambridge University Press, 2008,
  Theorem 2.2.2 (Gray stability).
-/

public section

noncomputable section

open Bundle
open scoped ContDiff Manifold Topology

namespace TauCeti.SmoothForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {α β γ : SmoothForm I M ℝ 1}

/-- The horizontal contact-Moser vector field for a one-form `α` and a variation `β`.
For a contact form in finite dimensions this is the unique vector in `ker α` satisfying
`(ι_Y dα + β)|ker α = 0`. The inverse is `ContinuousLinearMap.inverse`, so the definition
is zero wherever the contact flat map is not invertible. -/
def contactMoserVectorField (α β : SmoothForm I M ℝ 1) (x : M) : TangentSpace I x :=
  (α.contactFlat x).inverse
    (β.1 x ![α.reebVectorField x] • degreeOneEquiv α x - degreeOneEquiv β x)

/-- The formula for the horizontal contact-Moser vector field. -/
theorem contactMoserVectorField_def (α β : SmoothForm I M ℝ 1) (x : M) :
    α.contactMoserVectorField β x = (α.contactFlat x).inverse
      (β.1 x ![α.reebVectorField x] • degreeOneEquiv α x - degreeOneEquiv β x) :=
  (rfl)

/-- The zero variation gives the zero contact-Moser vector field. -/
@[simp]
theorem contactMoserVectorField_zero (α : SmoothForm I M ℝ 1) :
    α.contactMoserVectorField 0 = 0 := by
  funext x
  simp [contactMoserVectorField_def]

/-- **Contact-Moser vector fields of smooth families.** Let `α m` and `β m` be one-forms on `M`,
depending on a parameter `m ∈ N`, such that `α m` is a contact form for `m` near `m₀`, and let
`b : N → M`. If the values
`(α m)_(b m)`, `(β m)_(b m)` and the exterior derivatives `(dα m)_(b m)` depend `C^n` on `m`, as
sections along `b`, then so do the contact-Moser vectors of `(α m, β m)` at `b m`, as a map to the
tangent bundle. -/
theorem contMDiffAt_sectionAlong_contactMoserVectorField [FiniteDimensional ℝ E]
    {EN HN N : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN] [TopologicalSpace HN]
    {J : ModelWithCorners ℝ EN HN} [TopologicalSpace N] [ChartedSpace HN N] {n : WithTop ℕ∞}
    {b : N → M} {α β : N → SmoothForm I M ℝ 1} {m₀ : N}
    (hc : ∀ᶠ m in 𝓝 m₀, (α m).IsContactForm)
    (hα : ContMDiffAt J (I.prod 𝓘(ℝ, E [⋀^Fin 1]→L[ℝ] ℝ)) n
      (fun m ↦ TotalSpace.mk' (E [⋀^Fin 1]→L[ℝ] ℝ)
        (E := fun x : M ↦ TangentSpace I x [⋀^Fin 1]→L[ℝ] Trivial M ℝ x) (b m) ((α m).1 (b m))) m₀)
    (hdα : ContMDiffAt J (I.prod 𝓘(ℝ, E [⋀^Fin 2]→L[ℝ] ℝ)) n
      (fun m ↦ TotalSpace.mk' (E [⋀^Fin 2]→L[ℝ] ℝ)
        (E := fun x : M ↦ TangentSpace I x [⋀^Fin 2]→L[ℝ] Trivial M ℝ x) (b m)
        (mextDeriv (α m).1 (b m))) m₀)
    (hβ : ContMDiffAt J (I.prod 𝓘(ℝ, E [⋀^Fin 1]→L[ℝ] ℝ)) n
      (fun m ↦ TotalSpace.mk' (E [⋀^Fin 1]→L[ℝ] ℝ)
        (E := fun x : M ↦ TangentSpace I x [⋀^Fin 1]→L[ℝ] Trivial M ℝ x) (b m)
        ((β m).1 (b m))) m₀) :
    ContMDiffAt J I.tangent n
      (fun m ↦ (⟨b m, (α m).contactMoserVectorField (β m) (b m)⟩ : TangentBundle I M)) m₀ := by
  have hR := contMDiffAt_sectionAlong_reebVectorField hc hα hdα
  have hβ₁ := (contMDiffAt_sectionAlong_degreeOneEquiv_iff (b := b) (α := β)).2 hβ
  -- The coefficient `β(R_α)`, read in the trivial line bundle.
  have hβR : ContMDiffAt J 𝓘(ℝ) n
      (fun m ↦ (β m).1 (b m) ![(α m).reebVectorField (b m)]) m₀ := by
    have h := (contMDiffAt_totalSpace.1
      (ContMDiffAt.clm_bundle_apply (E₂ := Trivial M ℝ) hβ₁ hR)).2
    simpa [Trivial.eq_trivialization, degreeOneEquiv_apply_apply_vec] using h
  have h := (ContMDiffAt.clm_bundle_inverse (x := m₀) (ϕ := fun m ↦ (α m).contactFlat (b m))
    (contMDiffAt_sectionAlong_contactFlat hα hdα)
    (hc.self_of_nhds.isInvertible_contactFlat (b m₀))).clm_bundle_apply
      ((hβR.smul_totalSpace (contMDiffAt_sectionAlong_degreeOneEquiv_iff.2 hα)).sub_sectionAlong
        hβ₁)
  simpa only [contactMoserVectorField_def] using h

namespace IsContactForm

variable [FiniteDimensional ℝ E] (hα : α.IsContactForm)
include hα

/-- The contact flat map sends the contact-Moser vector to `β(R_α) α - β`. -/
@[simp]
theorem contactFlat_contactMoserVectorField (β : SmoothForm I M ℝ 1) (x : M) :
    α.contactFlat x (α.contactMoserVectorField β x) =
      β.1 x ![α.reebVectorField x] • degreeOneEquiv α x - degreeOneEquiv β x :=
  (hα.isInvertible_contactFlat x).self_apply_inverse _

/-- The contact-Moser vector field is horizontal. -/
@[simp]
theorem apply_contactMoserVectorField (β : SmoothForm I M ℝ 1) (x : M) :
    α.1 x ![α.contactMoserVectorField β x] = 0 := by
  have h := DFunLike.congr_fun (hα.contactFlat_contactMoserVectorField β x)
    (α.reebVectorField x)
  simpa [contactFlat_apply, hα.mextDeriv_reebVectorField_right,
    hα.apply_reebVectorField] using h

/-- The full contraction identity for the contact-Moser vector field. -/
theorem mextDeriv_contactMoserVectorField_left (β : SmoothForm I M ℝ 1) (x : M)
    (v : TangentSpace I x) :
    mextDeriv α.1 x ![α.contactMoserVectorField β x, v] =
      β.1 x ![α.reebVectorField x] * α.1 x ![v] - β.1 x ![v] := by
  have h := DFunLike.congr_fun (hα.contactFlat_contactMoserVectorField β x) v
  simpa [contactFlat_apply, hα.apply_contactMoserVectorField] using h

/-- **Existence and uniqueness for the horizontal contact-Moser equation.** It suffices to
prescribe the contraction on the contact hyperplane. -/
theorem eq_contactMoserVectorField_iff {x : M} {v : TangentSpace I x} :
    v = α.contactMoserVectorField β x ↔ α.1 x ![v] = 0 ∧
      ∀ w ∈ α.kerDistribution x, mextDeriv α.1 x ![v, w] + β.1 x ![w] = 0 := by
  constructor
  · rintro rfl
    refine ⟨hα.apply_contactMoserVectorField β x, fun w hw ↦ ?_⟩
    rw [hα.mextDeriv_contactMoserVectorField_left, mem_kerDistribution.1 hw]
    ring
  · rintro ⟨hv, hd⟩
    apply sub_eq_zero.1
    refine (isContactForm_iff.1 hα x).2 (v - α.contactMoserVectorField β x)
      (by simp [hv, hα.apply_contactMoserVectorField]) fun w hw ↦ ?_
    have h := hd w (mem_kerDistribution.2 hw)
    rw [ContinuousAlternatingMap.map_vecCons_sub, hα.mextDeriv_contactMoserVectorField_left,
      hw]
    linarith

/-- The contact-Moser vector depends only on the restriction of the variation to `ker α`. -/
theorem contactMoserVectorField_eq_iff {x : M} :
    α.contactMoserVectorField β x = α.contactMoserVectorField γ x ↔
      ∀ w ∈ α.kerDistribution x, β.1 x ![w] = γ.1 x ![w] := by
  rw [hα.eq_contactMoserVectorField_iff]
  simp only [hα.apply_contactMoserVectorField, hα.mextDeriv_contactMoserVectorField_left,
    true_and]
  constructor <;> intro h w hw
  · have := h w hw
    rw [mem_kerDistribution.1 hw] at this
    linarith
  · rw [mem_kerDistribution.1 hw, h w hw]
    ring

/-- In particular, the field vanishes wherever the variation annihilates the contact plane.
This is the pointwise stationary-locus criterion for a relative contact deformation. -/
theorem contactMoserVectorField_eq_zero_iff {x : M} :
    α.contactMoserVectorField β x = 0 ↔
      ∀ w ∈ α.kerDistribution x, β.1 x ![w] = 0 := by
  simpa using (hα.contactMoserVectorField_eq_iff (β := β) (γ := 0) (x := x))

/-- The horizontal contact-Moser vector field of a smooth variation is smooth. -/
theorem contMDiff_contactMoserVectorField (β : SmoothForm I M ℝ 1) :
    ContMDiff I I.tangent ∞ (T% (α.contactMoserVectorField β)) := fun x ↦
  contMDiffAt_sectionAlong_contactMoserVectorField (b := id) (α := fun _ ↦ α)
    (β := fun _ ↦ β) (.of_forall fun _ ↦ hα) (α.contMDiff x) (contMDiff_mextDeriv α x)
    (β.contMDiff x)

/-- The infinitesimal rescaling identity for the contact-Moser field:
`L_Y α + β = β(R_α) α`, evaluated on a tangent vector. -/
theorem mlieDerivForm_contactMoserVectorField_add (β : SmoothForm I M ℝ 1) (x : M)
    (v : TangentSpace I x) :
    mlieDerivForm (α.contactMoserVectorField β) α.1 x ![v] + β.1 x ![v] =
      β.1 x ![α.reebVectorField x] * α.1 x ![v] := by
  have hYd := (hα.contMDiff_contactMoserVectorField β).mdifferentiable (by simp)
  rw [mlieDerivForm_apply_eq_mextDeriv_add (f := fun _ ↦ (0 : ℝ))
    (hα.apply_contactMoserVectorField β) (α.mdifferentiableAt x) (hYd x),
    mvfderiv_const, zero_apply, add_zero,
    hα.mextDeriv_contactMoserVectorField_left, sub_add_cancel]

/-- **Change of local defining form.** Replacing `(α, β)` by `(f α, f β + g α)` leaves the
horizontal contact-Moser vector unchanged. For a time-dependent multiplier, `g = ∂t f`.
There is no positivity hypothesis on the nowhere-zero multiplier `f`. -/
theorem contactMoserVectorField_of_eq_smul {α' β' : SmoothForm I M ℝ 1} {f g : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ) 1 f) (hf₀ : ∀ x, f x ≠ 0)
    (hα' : ∀ x, α'.1 x = f x • α.1 x)
    (hβ' : ∀ x, β'.1 x = f x • β.1 x + g x • α.1 x) :
    α'.contactMoserVectorField β' = α.contactMoserVectorField β := by
  have hc : α'.IsContactForm := (isContactForm_iff_of_eq_smul hf hf₀ hα').2 hα
  funext x
  symm
  apply hc.eq_contactMoserVectorField_iff.2
  have hY := hα.apply_contactMoserVectorField β x
  refine ⟨by simp [hα', hY], fun w hw ↦ ?_⟩
  have hwα : α.1 x ![w] = 0 := by
    rw [kerDistribution_of_eq_smul hf₀ hα'] at hw
    exact mem_kerDistribution.1 hw
  have hd := (hα.eq_contactMoserVectorField_iff (β := β) (x := x)).1 rfl
  have hα'' : α'.1 = fun y ↦ f y • α.1 y := funext hα'
  rw [hα'', mextDeriv_fun_smul_apply ((hf x).mdifferentiableAt one_ne_zero)
    (α.mdifferentiableAt x), hY, hwα]
  simp only [hβ', ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.smul_apply,
    smul_eq_mul, hwα, mul_zero, sub_zero, zero_add, add_zero]
  rw [← mul_add, hd.2 w (mem_kerDistribution.2 hwα), mul_zero]

end IsContactForm

end TauCeti.SmoothForm
