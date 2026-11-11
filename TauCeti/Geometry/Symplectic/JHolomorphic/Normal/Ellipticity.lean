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
complex-antilinear covectors, and its Leibniz rule is the real Cauchy–Riemann symbol for this
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

/-- Applying the normal complex structure is applying `J` to any ambient lift. -/
@[simp]
theorem normalComplexStructure_mk (j : AlmostComplexStructure U)
    (J : V → AlmostComplexStructure V) (u : U → V) (x : U)
    (hu : IsJHolomorphicAt (fun _ ↦ j) J u x) (v : V) :
    normalComplexStructure j J u x hu (Submodule.Quotient.mk v) =
      Submodule.Quotient.mk (J (u x) v) := by
  simp only [normalComplexStructure, AlmostComplexStructure.quotient_mk]

/-- The normal linearization is a complex-antilinear covector on the source. This is not
complex linearity in the normal section: that stronger property need not hold. -/
theorem isComplexAntilinear_normalCauchyRiemannLinearization
    [FiniteDimensional ℝ U] [FiniteDimensional ℝ V]
    (j : AlmostComplexStructure U) (J : V → AlmostComplexStructure V)
    (u ξ : U → V) (x : U) (hu : IsJHolomorphicAt (fun _ ↦ j) J u x)
    (hJ : DifferentiableAt ℝ (fun y ↦ (J y).toLinearMap.toContinuousLinearMap) (u x)) :
    IsComplexAntilinear j.toLinearMap (normalComplexStructure j J u x hu).toLinearMap
      (normalCauchyRiemannLinearization j.toLinearMap.toContinuousLinearMap
        (fun y ↦ (J y).toLinearMap.toContinuousLinearMap) u ξ x) := by
  have h := isComplexAntilinear_cauchyRiemannLinearization j J u ξ x hu hJ
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
    (u ξ : U → V) (f : U → ℝ) (x v : U)
    (hu : IsJHolomorphicAt (fun _ ↦ j) J u x)
    (hf : DifferentiableAt ℝ f x) (hξ : DifferentiableAt ℝ ξ x) :
    normalCauchyRiemannLinearization j.toLinearMap.toContinuousLinearMap
        (fun y ↦ (J y).toLinearMap.toContinuousLinearMap) u (fun y ↦ f y • ξ y) x v =
      f x • normalCauchyRiemannLinearization j.toLinearMap.toContinuousLinearMap
        (fun y ↦ (J y).toLinearMap.toContinuousLinearMap) u ξ x v +
      cauchyRiemannSymbol j (normalComplexStructure j J u x hu) (fderiv ℝ f x).toLinearMap
        ((fderiv ℝ u x).toLinearMap.range.mkQ (ξ x)) v := by
  rw [normalCauchyRiemannLinearization_fun_smul _ _ _ _ _ _ _ hf hξ]
  simp only [cauchyRiemannSymbol_apply, Submodule.mkQ_apply, normalComplexStructure_mk,
    Submodule.Quotient.mk_sub, Submodule.Quotient.mk_smul,
    LinearMap.coe_toContinuousLinearMap', ContinuousLinearMap.coe_coe]

end TauCeti
