/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.JHolomorphic.Normal.Linearization
public import TauCeti.Geometry.Symplectic.AlmostComplex.Quotient
public import TauCeti.Geometry.Symplectic.JHolomorphic.Symbol

/-!
# The complex normal quotient and its Cauchy–Riemann symbol

The derivative of a pseudoholomorphic map has invariant image. Thus its actual normal
quotient inherits an almost complex structure. The normal linearization takes values in
complex-antilinear maps into the normal quotient, and its Leibniz rule is the real Cauchy–Riemann
symbol for this
quotient structure. In a holomorphic coordinate on a curve, the symbol is bijective at every
nonzero real covector by `bijective_cauchyRiemannSymbolAntilinear`.

No complement, metric or integrability assumption on the ambient structure is used. The
statements apply even without immersivity; for an immersion the quotient is the normal fiber.
These local statements do not construct a global normal bundle or its Fredholm realization.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Section 3.1.
-/

public section

noncomputable section

namespace TauCeti

variable {U V : Type*}
  [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The almost complex structure on the actual normal quotient of a pseudoholomorphic map. -/
def normalComplexStructure (j : AlmostComplexStructure U) (J : V → AlmostComplexStructure V)
    (u : U → V) (x : U) (hu : IsJHolomorphicAt (fun _ ↦ j) J u x) :
    AlmostComplexStructure (V ⧸ (fderiv ℝ u x).toLinearMap.range) :=
  (J (u x)).quotient (fderiv ℝ u x).toLinearMap.range (by
    rintro _ ⟨v, rfl⟩
    exact ⟨j v, hu.fderiv_apply_commute⟩)

/-- The normal complex structure is induced by the ambient structure on the derivative quotient. -/
theorem normalComplexStructure_def (j : AlmostComplexStructure U)
    (J : V → AlmostComplexStructure V) (u : U → V) (x : U)
    (hu : IsJHolomorphicAt (fun _ ↦ j) J u x) :
    normalComplexStructure j J u x hu =
      (J (u x)).quotient (fderiv ℝ u x).toLinearMap.range (by
        rintro _ ⟨v, rfl⟩
        exact ⟨j v, hu.fderiv_apply_commute⟩) := (rfl)

/-- Applying the normal complex structure is applying `J` to any ambient lift. -/
@[simp]
theorem normalComplexStructure_mk (j : AlmostComplexStructure U)
    (J : V → AlmostComplexStructure V) (u : U → V) (x : U)
    (hu : IsJHolomorphicAt (fun _ ↦ j) J u x) (v : V) :
    normalComplexStructure j J u x hu (Submodule.Quotient.mk v) =
      Submodule.Quotient.mk (J (u x) v) := by
  simp only [normalComplexStructure, AlmostComplexStructure.quotient_mk]

/-- The projection to the normal quotient is complex-linear. -/
@[simp]
theorem isComplexLinearMap_normalComplexStructure_mkQ (j : AlmostComplexStructure U)
    (J : V → AlmostComplexStructure V) (u : U → V) (x : U)
    (hu : IsJHolomorphicAt (fun _ ↦ j) J u x) :
    IsComplexLinearMap (J (u x)) (normalComplexStructure j J u x hu)
      (fderiv ℝ u x).toLinearMap.range.mkQ := by
  rw [normalComplexStructure_def]
  exact (J (u x)).isComplexLinearMap_mkQ _ _

/-- The normal linearization is complex-antilinear on the source tangent space, with values
in the normal quotient. This is distinct from complex linearity in the normal section, which
need not hold when `J` is not integrable. -/
theorem isComplexAntilinear_normalCauchyRiemannLinearization
    [FiniteDimensional ℝ U] [FiniteDimensional ℝ V]
    (j : AlmostComplexStructure U) (J : V → AlmostComplexStructure V)
    (u ξ : U → V) (x : U) (hu : IsJHolomorphicAt (fun _ ↦ j) J u x) :
    IsComplexAntilinear j.toLinearMap (normalComplexStructure j J u x hu).toLinearMap
      (normalCauchyRiemannLinearization j.toLinearMap.toContinuousLinearMap
        (fun y ↦ (J y).toLinearMap.toContinuousLinearMap) u ξ x) := by
  have h := isComplexAntilinear_cauchyRiemannLinearization j J u ξ x hu
  apply isComplexAntilinear_of_apply
  intro v
  simpa only [normalCauchyRiemannLinearization_apply, Submodule.mkQ_apply,
    normalComplexStructure_mk, Submodule.Quotient.mk_neg, ContinuousLinearMap.coe_coe] using
      congrArg (fderiv ℝ u x).toLinearMap.range.mkQ (h.apply v)

/-- The Leibniz remainder of the actual normal linearization is the intrinsic real
Cauchy–Riemann symbol on the normal quotient. Together with
`bijective_cauchyRiemannSymbolAntilinear`, this identifies its elliptic symbol over a source
curve. -/
theorem normalCauchyRiemannLinearization_fun_smul_eq_smul_add_cauchyRiemannSymbol
    [FiniteDimensional ℝ U] [FiniteDimensional ℝ V]
    (j : AlmostComplexStructure U) (J : V → AlmostComplexStructure V)
    (u ξ : U → V) (f : U → ℝ) (x : U)
    (hu : IsJHolomorphicAt (fun _ ↦ j) J u x)
    (hf : DifferentiableAt ℝ f x) (hξ : DifferentiableAt ℝ ξ x) :
    normalCauchyRiemannLinearization j.toLinearMap.toContinuousLinearMap
        (fun y ↦ (J y).toLinearMap.toContinuousLinearMap) u (fun y ↦ f y • ξ y) x =
      f x • normalCauchyRiemannLinearization j.toLinearMap.toContinuousLinearMap
        (fun y ↦ (J y).toLinearMap.toContinuousLinearMap) u ξ x +
      cauchyRiemannSymbol j (normalComplexStructure j J u x hu) (fderiv ℝ f x).toLinearMap
        ((fderiv ℝ u x).toLinearMap.range.mkQ (ξ x)) := by
  ext v
  rw [normalCauchyRiemannLinearization_fun_smul _ _ _ _ _ _ _ hf hξ]
  simp only [LinearMap.add_apply, LinearMap.smul_apply, cauchyRiemannSymbol_apply,
    Submodule.mkQ_apply, normalComplexStructure_mk, Submodule.Quotient.mk_sub,
    Submodule.Quotient.mk_smul, LinearMap.coe_toContinuousLinearMap',
    ContinuousLinearMap.coe_coe]

end TauCeti
