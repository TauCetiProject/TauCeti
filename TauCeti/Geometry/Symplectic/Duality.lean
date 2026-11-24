/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.AlmostComplex
public import TauCeti.Topology.Algebra.Module.BilinearForm
public import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps

/-!
# Contraction with a symplectic form

On a finite-dimensional real normed space, contraction with a symplectic form is an
invertible continuous linear map to the continuous dual. This identifies covectors with
vectors and allows the contraction equation in Moser's deformation argument to be solved
using the continuous-linear-map inverse. The symplectic pairing of two continuous maps is
continuous, and that of two differentiable curves satisfies the product rule. The pairing is
bounded by the operator norm of the form, and the continuous bilinear map minus its transpose is
twice the form.

## Main declarations

* `TauCeti.SymplecticForm.flatEquiv`: the isomorphism `ω♭ : v ↦ ω(v, ·)` of `V` with its
  continuous dual.
* `TauCeti.SymplecticForm.leftAdjointL`: the `ω`-transpose `L ↦ Lᵀ` of endomorphisms,
  `ω (Lᵀ v) w = ω v (L w)`, Mathlib's `LinearMap.BilinForm.leftAdjointOfNondegenerate` for `ω`
  as a continuous linear map in `L`.
* `TauCeti.SymplecticForm.Invariant.leftAdjointL_eq_neg`: a complex structure preserving `ω` has
  `ω`-transpose `-J`.

See McDuff--Salamon, *Introduction to Symplectic Topology*, Section 3.2.
-/

public section

namespace TauCeti.SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- Contraction with a finite-dimensional symplectic form is an isomorphism to the
continuous dual. -/
@[simp]
theorem isInvertible_toContinuousBilinearMap (ω : SymplecticForm V) :
    ω.toBilinForm.toContinuousBilinearMap.IsInvertible :=
  TauCeti.isInvertible_toContinuousBilinearMap_iff_separatingLeft.mpr
    ω.nondegenerate.1

section Continuity

variable {X : Type*} [TopologicalSpace X] {p q : X → V} {s : Set X}

/-- The symplectic pairing of two maps continuous on a set is continuous on that set. -/
theorem continuousOn_apply_comp (ω : SymplecticForm V) (hp : ContinuousOn p s)
    (hq : ContinuousOn q s) : ContinuousOn (fun z ↦ ω (p z) (q z)) s := by
  simpa only [Function.comp_apply, LinearMap.toContinuousBilinearMap_apply] using
    ContinuousOn.clm_apply (ω.toBilinForm.toContinuousBilinearMap.continuous.comp_continuousOn hp)
      hq

/-- The symplectic pairing of two continuous maps is continuous. -/
theorem continuous_apply_comp (ω : SymplecticForm V) (hp : Continuous p) (hq : Continuous q) :
    Continuous fun z ↦ ω (p z) (q z) :=
  continuousOn_univ.mp <| ω.continuousOn_apply_comp hp.continuousOn hq.continuousOn

end Continuity

/-- A symplectic form on a finite-dimensional space is bounded by the operator norm of its
continuous bilinear map: `|ω(v, w)| ≤ ‖ω‖ ‖v‖ ‖w‖`. -/
theorem abs_apply_le_opNorm_mul_norm_mul_norm (ω : SymplecticForm V) (v w : V) :
    |ω v w| ≤ ‖ω.toBilinForm.toContinuousBilinearMap‖ * ‖v‖ * ‖w‖ := by
  simpa only [LinearMap.toContinuousBilinearMap_apply, Real.norm_eq_abs] using
    ω.toBilinForm.toContinuousBilinearMap.le_opNorm₂ v w

/-- The continuous bilinear map of a symplectic form minus its transpose is twice the form:
`ω(x, y) - ω(y, x) = 2 ω(x, y)`. This is the integrand of the Green formulas for symplectic
area. -/
theorem toContinuousBilinearMap_sub_swap (ω : SymplecticForm V) (x y : V) :
    ω.toBilinForm.toContinuousBilinearMap x y - ω.toBilinForm.toContinuousBilinearMap y x =
      2 * ω x y := by
  rw [LinearMap.toContinuousBilinearMap_apply, LinearMap.toContinuousBilinearMap_apply,
    ← ω.isAlt.neg_eq x y]
  ring

/-- The product rule for the symplectic pairing of two curves. -/
theorem hasDerivAt_apply_comp (ω : SymplecticForm V) {p q : ℝ → V} {p' q' : V} {t : ℝ}
    (hp : HasDerivAt p p' t) (hq : HasDerivAt q q' t) :
    HasDerivAt (fun t ↦ ω (p t) (q t)) (ω p' (q t) + ω (p t) q') t := by
  simpa only [LinearMap.toContinuousBilinearMap_apply, add_comm] using
    ω.toBilinForm.toContinuousBilinearMap.hasDerivAt_of_bilinear (fun _ ↦ hp) (fun _ ↦ hq)

/-! ### Covectors as vectors through `ω` -/

/-- The isomorphism `ω♭ : v ↦ ω(v, ·)` of a finite-dimensional symplectic vector space with its
continuous dual. -/
noncomputable def flatEquiv (ω : SymplecticForm V) : V ≃L[ℝ] (V →L[ℝ] ℝ) :=
  ((ω.toBilinForm.toDual ω.nondegenerate).trans
    LinearMap.toContinuousLinearMap).toContinuousLinearEquiv

@[simp]
theorem flatEquiv_apply (ω : SymplecticForm V) (v w : V) : ω.flatEquiv v w = ω v w := by
  simp [flatEquiv, LinearMap.BilinForm.toDual_def]

@[simp]
theorem apply_flatEquiv_symm_apply (ω : SymplecticForm V) (φ : V →L[ℝ] ℝ) (w : V) :
    ω (ω.flatEquiv.symm φ) w = φ w := by
  rw [← flatEquiv_apply, ContinuousLinearEquiv.apply_symm_apply]

/-- As a continuous linear map, `ω♭` is the contraction map
`ω.toBilinForm.toContinuousBilinearMap`. -/
theorem coe_flatEquiv (ω : SymplecticForm V) :
    (ω.flatEquiv : V →L[ℝ] (V →L[ℝ] ℝ)) = ω.toBilinForm.toContinuousBilinearMap := by
  ext v w
  simp

/-- As a continuous linear map, `ω♭⁻¹` is the inverse
`ω.toBilinForm.toContinuousBilinearMap.inverse` used to define Hamiltonian vector fields. -/
theorem coe_flatEquiv_symm (ω : SymplecticForm V) :
    (ω.flatEquiv.symm : (V →L[ℝ] ℝ) →L[ℝ] V) =
      ω.toBilinForm.toContinuousBilinearMap.inverse := by
  rw [← coe_flatEquiv, ContinuousLinearMap.inverse_equiv]

omit [FiniteDimensional ℝ V] in
/-- Two endomorphisms that pair in the same way under `ω` are equal. -/
theorem continuousLinearMap_ext_of_apply_eq (ω : SymplecticForm V) {L L' : V →L[ℝ] V}
    (h : ∀ v w, ω (L v) w = ω (L' v) w) : L = L' :=
  ContinuousLinearMap.coe_injective
    (ω.toBilinForm.compLeft_injective ω.nondegenerate (LinearMap.BilinForm.ext h))

/-! ### The `ω`-transpose -/

private theorem apply_leftAdjointOfNondegenerate_apply (ω : SymplecticForm V) (L : V →L[ℝ] V)
    (v w : V) :
    ω (ω.toBilinForm.leftAdjointOfNondegenerate ω.nondegenerate (L : V →ₗ[ℝ] V) v) w =
      ω v (L w) :=
  ω.toBilinForm.isAdjointPairLeftAdjointOfNondegenerate ω.nondegenerate _ v w

/-- The `ω`-transpose `L ↦ Lᵀ` of endomorphisms, Mathlib's
`LinearMap.BilinForm.leftAdjointOfNondegenerate` for `ω`, as a continuous linear map in `L`. It is
characterized by `ω (Lᵀ v) w = ω v (L w)` (`apply_leftAdjointL_apply`). -/
noncomputable def leftAdjointL (ω : SymplecticForm V) : (V →L[ℝ] V) →L[ℝ] (V →L[ℝ] V) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun L ↦ LinearMap.toContinuousLinearMap
        (ω.toBilinForm.leftAdjointOfNondegenerate ω.nondegenerate (L : V →ₗ[ℝ] V))
      map_add' := fun L L' ↦ ω.continuousLinearMap_ext_of_apply_eq fun v w ↦ by
        simp only [LinearMap.coe_toContinuousLinearMap', add_apply, map_add, LinearMap.add_apply,
          apply_leftAdjointOfNondegenerate_apply]
      map_smul' := fun c L ↦ ω.continuousLinearMap_ext_of_apply_eq fun v w ↦ by
        simp only [LinearMap.coe_toContinuousLinearMap', smul_apply, map_smul, LinearMap.smul_apply,
          RingHom.id_apply, apply_leftAdjointOfNondegenerate_apply] }

/-- The `ω`-transpose of `L` is Mathlib's `LinearMap.BilinForm.leftAdjointOfNondegenerate` of `L`
for `ω`, as a continuous linear map. This holds by definition of `leftAdjointL`. -/
theorem leftAdjointL_apply (ω : SymplecticForm V) (L : V →L[ℝ] V) :
    ω.leftAdjointL L = LinearMap.toContinuousLinearMap
      (ω.toBilinForm.leftAdjointOfNondegenerate ω.nondegenerate (L : V →ₗ[ℝ] V)) := by
  rw [leftAdjointL, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk]

@[simp]
theorem apply_leftAdjointL_apply (ω : SymplecticForm V) (L : V →L[ℝ] V) (v w : V) :
    ω (ω.leftAdjointL L v) w = ω v (L w) := by
  rw [leftAdjointL_apply, LinearMap.coe_toContinuousLinearMap',
    apply_leftAdjointOfNondegenerate_apply]

/-- For a complex structure `J` preserving `ω`, the `ω`-transpose of `J` is `-J`. -/
theorem Invariant.leftAdjointL_eq_neg {ω : SymplecticForm V} {J : AlmostComplexStructure V}
    (hJ : ω.Invariant J) :
    ω.leftAdjointL J.toLinearMap.toContinuousLinearMap = -J.toLinearMap.toContinuousLinearMap :=
  ω.continuousLinearMap_ext_of_apply_eq fun v w ↦ by simp [hJ.apply_apply_eq_neg]

end TauCeti.SymplecticForm
