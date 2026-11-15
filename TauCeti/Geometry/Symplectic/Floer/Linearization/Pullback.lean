/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Linearization
public import TauCeti.Geometry.Symplectic.Floer.Pullback
public import TauCeti.Geometry.Symplectic.JHolomorphic.Line
import TauCeti.Geometry.Symplectic.Cayley.Tangent

/-!
# The linearized Floer operator under holomorphic changes of domain coordinates

The coordinate Floer operator `F(u) = ∂s u - X_Ks(u) + J(z, u)(∂t u - X_Kt(u))`
(`TauCeti.SymplecticForm.floerOperator`) and its linearization `D_u`
(`TauCeti.SymplecticForm.floerLinearization`) are written in one coordinate `z = (s, t)` of the
domain. On a punctured Riemann surface such as the pair of pants they are written in a global
coordinate on the compact part and in cylinder coordinates on each end, which are related by a
holomorphic change of coordinates `φ` (for the pair of pants, the end charts
`TauCeti.Floer.endChart`). This file records how the two operators transform under `φ`.

Let `dφ_w` be complex linear, so that `dφ_w ∂s = (a, b)` and `dφ_w ∂t = (-b, a)`, and pull the
data back: `J'(w, y) = J(φ w, y)`, `K' = φ^*K` (`TauCeti.Floer.perturbationPullback`) and
`u' = u ∘ φ`. Write `J = J(φ w, u(φ w))`.

* `TauCeti.SymplecticForm.floerOperator_perturbationPullback`: the Floer operator transforms by
  the complex number `a - b J`: `F'(u')(w) = a F(u)(φ w) - b J F(u)(φ w)`. Since `a - b J` is
  invertible when `dφ_w ≠ 0`, the two equations have the same solutions
  (`TauCeti.SymplecticForm.floerOperator_perturbationPullback_eq_zero_iff`).
* `TauCeti.SymplecticForm.floerLinearization_perturbationPullback`: the linearization along the
  pulled back section `ξ' = ξ ∘ φ` transforms in the same way, up to a term proportional to
  `F(u)`: `D'_{u'} ξ'(w) = a D_u ξ(φ w) - b (J D_u ξ(φ w) + (dJ ξ) F(u)(φ w))`, where `dJ ξ` is
  the derivative of `J(φ w, ·)` at `u(φ w)` in the direction `ξ(φ w)`.
  The computation uses `J² = -1` and its derivative `(dJ ξ) J + J (dJ ξ) = 0`
  (`TauCeti.AlmostComplexStructure.mem_tangentSpace_of_hasFDerivAt`).
* `TauCeti.SymplecticForm.floerLinearization_perturbationPullback_of_floerOperator_eq_zero`: along
  a solution, `D'_{u'} ξ'(w) = (a - b J) D_u ξ(φ w)`. This is the transformation law of the value
  on `∂s` of a `J`-antilinear one-form `η`, since `η(dφ_w ∂s) = a η(∂s) + b η(∂t)` and
  `η(∂t) = -J η(∂s)`. So the two charts compute the same `(0, 1)`-form `D_u ξ`.

Since `|a - b J|` is comparable to `|dφ_w|`, with constants depending only on a bound `M` for `J`,
and `det dφ_w = a² + b²`, the `L²` norm of `D_u ξ` is invariant up to the factor `1 + M²` under
the change of variables: over a set `s` on which `φ` is injective, along a solution,

`∫_s ‖D'_{u'} ξ'‖² ≤ (1 + M²) ∫_{φ '' s} ‖D_u ξ‖²`, and
`∫_{φ '' s} ‖D_u ξ‖² ≤ (1 + M²) ∫_s ‖D'_{u'} ξ'‖²`

(`TauCeti.SymplecticForm.setIntegral_norm_floerLinearization_perturbationPullback_sq_le`,
`TauCeti.SymplecticForm.setIntegral_image_norm_floerLinearization_sq_le`). This is the conformal
invariance of the `L²` norm of `(0, 1)`-forms on a surface. It lets estimates for `D_u` proved in
cylinder coordinates on the ends of a punctured domain, such as
`TauCeti.SymplecticForm.exists_mem_forall_setIntegral_le_mul_setIntegral_floerLinearization`,
be read in a global coordinate, and conversely. The norm of the section `ξ` itself is not
conformally invariant, and is not treated here.

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., Sections 3.1
  and 8.1, on the linearized operator, its independence of coordinates and Hamiltonian
  perturbations as one-forms on the domain.
-/

public section

open ContinuousLinearMap Filter Function MeasureTheory Set
open scoped Topology

namespace TauCeti

/-- A complex-linear endomorphism of the standard complex line `ℝ × ℝ`, multiplication by
`a + b i` with `(a, b)` the image of `1`, has determinant `a² + b²`. -/
theorem IsComplexLinearMap.det_eq {F : ℝ × ℝ →ₗ[ℝ] ℝ × ℝ}
    (hF : IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (AlmostComplexStructure.product ℝ) F) :
    LinearMap.det F = (F stdComplexLineReal).1 ^ 2 + (F stdComplexLineReal).2 ^ 2 := by
  rw [LinearMap.det_finTwoProd, ← stdComplexLineReal_eq, ← stdComplexLineImag_eq,
    hF.apply_stdComplexLineImag, AlmostComplexStructure.product_apply]
  ring

namespace SymplecticForm

open Floer

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
variable {φ : ℝ × ℝ → ℝ × ℝ} {J : ℝ × ℝ → V → AlmostComplexStructure V}
  {Ks Kt : ℝ × ℝ → V → ℝ} {u ξ : ℝ × ℝ → V} {w : ℝ × ℝ}

/-- The Hamiltonian vector field of a component of the pullback `φ^*K` near a point `x` is the
corresponding combination of the Hamiltonian vector fields of `K_s` and `K_t` at `φ w`, so its
derivative at `x` is the same combination of their derivatives. -/
theorem fderiv_hamiltonianVectorField_perturbationPullback (ω : SymplecticForm V) {x : V}
    (hKs : ContDiffAt ℝ 2 (uncurry Ks) (φ w, x)) (hKt : ContDiffAt ℝ 2 (uncurry Kt) (φ w, x))
    (v : ℝ × ℝ) :
    fderiv ℝ (ω.hamiltonianVectorField (perturbationPullback φ Ks Kt v w)) x =
      (fderiv ℝ φ w v).1 • fderiv ℝ (ω.hamiltonianVectorField (Ks (φ w))) x +
        (fderiv ℝ φ w v).2 • fderiv ℝ (ω.hamiltonianVectorField (Kt (φ w))) x := by
  have hc : ContDiffAt ℝ 2 (fun y : V ↦ (φ w, y)) x := contDiffAt_const.prodMk contDiffAt_id
  -- Near `x` the slices of `K_s` and `K_t` at `φ w` are differentiable.
  have hslice {K : ℝ × ℝ → V → ℝ} (hK : ContDiffAt ℝ 2 (uncurry K) (φ w, x)) :
      ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ (K (φ w)) y := by
    filter_upwards [hc.continuousAt.eventually (hK.eventually (by simp))] with y hy
    exact (hy.comp y (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by norm_num)
  -- At `x` the Hamiltonian vector fields of the slices are differentiable.
  have hX {K : ℝ × ℝ → V → ℝ} (hK : ContDiffAt ℝ 2 (uncurry K) (φ w, x)) :
      DifferentiableAt ℝ (ω.hamiltonianVectorField (K (φ w))) x :=
    ((ω.contDiffAt_hamiltonianVectorField_uncurry (n := 1) hK).comp x
      (hc.of_le (by norm_num))).differentiableAt one_ne_zero
  have heq : ω.hamiltonianVectorField (perturbationPullback φ Ks Kt v w) =ᶠ[𝓝 x]
      fun y ↦ (fderiv ℝ φ w v).1 • ω.hamiltonianVectorField (Ks (φ w)) y +
        (fderiv ℝ φ w v).2 • ω.hamiltonianVectorField (Kt (φ w)) y := by
    filter_upwards [hslice hKs, hslice hKt] with y hs ht
    have h : perturbationPullback φ Ks Kt v w = fun y ↦
        (fderiv ℝ φ w v).1 * Ks (φ w) y + (fderiv ℝ φ w v).2 * Kt (φ w) y :=
      funext (perturbationPullback_apply φ Ks Kt v w)
    rw [h]
    exact ω.hamiltonianVectorField_const_mul_add_const_mul hs ht _ _
  rw [heq.fderiv_eq]
  exact (((hX hKs).hasFDerivAt.const_smul _).add ((hX hKt).hasFDerivAt.const_smul _)).fderiv

/-- **Naturality of the Floer operator.** Under a change of domain coordinates `φ` with complex
linear derivative `dφ_w`, `dφ_w ∂s = (a, b)`, the Floer operator of `u ∘ φ` for the pulled back
data `J(φ ·)`, `φ^*K` is `(a - b J) F(u)(φ w)`, with `J = J(φ w, u(φ w))`. -/
theorem floerOperator_perturbationPullback (ω : SymplecticForm V)
    (hφ : DifferentiableAt ℝ φ w)
    (hφJ : IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (AlmostComplexStructure.product ℝ) (fderiv ℝ φ w : ℝ × ℝ →ₗ[ℝ] ℝ × ℝ))
    (hu : DifferentiableAt ℝ u (φ w)) (hKs : DifferentiableAt ℝ (Ks (φ w)) (u (φ w)))
    (hKt : DifferentiableAt ℝ (Kt (φ w)) (u (φ w))) :
    ω.floerOperator (fun w' y ↦ (J (φ w') y).toLinearMap.toContinuousLinearMap)
        (perturbationPullback φ Ks Kt stdComplexLineReal)
        (perturbationPullback φ Ks Kt stdComplexLineImag) (u ∘ φ) w =
      (fderiv ℝ φ w stdComplexLineReal).1 •
          ω.floerOperator (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) Ks Kt u (φ w) -
        (fderiv ℝ φ w stdComplexLineReal).2 • J (φ w) (u (φ w))
          (ω.floerOperator (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap)
            Ks Kt u (φ w)) := by
  set a := (fderiv ℝ φ w stdComplexLineReal).1
  set b := (fderiv ℝ φ w stdComplexLineReal).2
  have hP (v : ℝ × ℝ) : ω.perturbedFDeriv Ks Kt u (φ w) v =
      v.1 • ω.perturbedFDeriv Ks Kt u (φ w) stdComplexLineReal +
        v.2 • ω.perturbedFDeriv Ks Kt u (φ w) stdComplexLineImag := by
    simpa using (ω.perturbedFDeriv Ks Kt u (φ w) : ℝ × ℝ →ₗ[ℝ] V).apply_stdComplexLine v
  have h₂ := hφJ.apply_stdComplexLineImag
  simp only [ContinuousLinearMap.coe_coe] at h₂
  have h₁ : fderiv ℝ φ w stdComplexLineReal = (a, b) := rfl
  rw [floerOperator_eq_perturbedFDeriv, floerOperator_eq_perturbedFDeriv,
    ω.perturbedFDeriv_perturbationPullback hφ hu hKs hKt, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply, h₂, h₁, hP (a, b), AlmostComplexStructure.product_apply,
    hP (-b, a)]
  simp only [Function.comp_apply, LinearMap.coe_toContinuousLinearMap', map_add, map_smul,
    AlmostComplexStructure.apply_apply]
  module

/-- Under a change of domain coordinates `φ` with complex linear derivative `dφ_w ≠ 0`, `u ∘ φ`
solves the Floer equation for the pulled back data at `w` exactly when `u` solves it at `φ w`. -/
theorem floerOperator_perturbationPullback_eq_zero_iff (ω : SymplecticForm V)
    (hφ : DifferentiableAt ℝ φ w)
    (hφJ : IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (AlmostComplexStructure.product ℝ) (fderiv ℝ φ w : ℝ × ℝ →ₗ[ℝ] ℝ × ℝ))
    (hφ₀ : fderiv ℝ φ w ≠ 0) (hu : DifferentiableAt ℝ u (φ w))
    (hKs : DifferentiableAt ℝ (Ks (φ w)) (u (φ w)))
    (hKt : DifferentiableAt ℝ (Kt (φ w)) (u (φ w))) :
    ω.floerOperator (fun w' y ↦ (J (φ w') y).toLinearMap.toContinuousLinearMap)
        (perturbationPullback φ Ks Kt stdComplexLineReal)
        (perturbationPullback φ Ks Kt stdComplexLineImag) (u ∘ φ) w = 0 ↔
      ω.floerOperator (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) Ks Kt u (φ w) = 0 := by
  rw [ω.floerOperator_perturbationPullback hφ hφJ hu hKs hKt]
  set a := (fderiv ℝ φ w stdComplexLineReal).1
  set b := (fderiv ℝ φ w stdComplexLineReal).2
  set F := ω.floerOperator (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) Ks Kt u (φ w)
  refine ⟨fun h ↦ ?_, fun h ↦ by simp [h]⟩
  -- A complex-linear map of the plane vanishes when its value at `1` does.
  have hab : a ^ 2 + b ^ 2 ≠ 0 := by
    intro h₀
    have h0 : ((fderiv ℝ φ w : ℝ × ℝ →L[ℝ] ℝ × ℝ) : ℝ × ℝ →ₗ[ℝ] ℝ × ℝ) = 0 := by
      rw [hφJ.eq_zero_iff_apply_stdComplexLineReal, ContinuousLinearMap.coe_coe]
      exact Prod.ext (pow_eq_zero_iff two_ne_zero |>.1 (by nlinarith : a ^ 2 = 0))
        (pow_eq_zero_iff two_ne_zero |>.1 (by nlinarith : b ^ 2 = 0))
    exact hφ₀ (ContinuousLinearMap.coe_injective
      (h0.trans ContinuousLinearMap.toLinearMap_zero.symm))
  -- `(a + b J)(a - b J) = a² + b²`.
  have hF : (a ^ 2 + b ^ 2) • F = a • (a • F - b • J (φ w) (u (φ w)) F) +
      b • J (φ w) (u (φ w)) (a • F - b • J (φ w) (u (φ w)) F) := by
    simp only [AlmostComplexStructure.apply_sub, AlmostComplexStructure.apply_smul,
      AlmostComplexStructure.apply_apply]
    module
  rw [h, AlmostComplexStructure.apply_zero, smul_zero, smul_zero, add_zero] at hF
  exact (smul_eq_zero.1 hF).resolve_left hab

/-- **Naturality of the linearized Floer operator.** Under a change of domain coordinates `φ`
with complex linear derivative `dφ_w`, `dφ_w ∂s = (a, b)`, the linearization along `u ∘ φ` for the
pulled back data `J(φ ·)`, `φ^*K`, applied to `ξ ∘ φ`, is
`a D_u ξ(φ w) - b (J D_u ξ(φ w) + (dJ ξ) F(u)(φ w))`, with `J = J(φ w, u(φ w))` and `dJ ξ` the
derivative of `J(φ w, ·)` at `u(φ w)` in the direction `ξ(φ w)`. -/
theorem floerLinearization_perturbationPullback (ω : SymplecticForm V)
    (hφ : DifferentiableAt ℝ φ w)
    (hφJ : IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (AlmostComplexStructure.product ℝ) (fderiv ℝ φ w : ℝ × ℝ →ₗ[ℝ] ℝ × ℝ))
    (hu : DifferentiableAt ℝ u (φ w)) (hξ : DifferentiableAt ℝ ξ (φ w))
    (hKs : ContDiffAt ℝ 2 (uncurry Ks) (φ w, u (φ w)))
    (hKt : ContDiffAt ℝ 2 (uncurry Kt) (φ w, u (φ w)))
    (hJ : DifferentiableAt ℝ (fun y ↦ (J (φ w) y).toLinearMap.toContinuousLinearMap)
      (u (φ w))) :
    ω.floerLinearization (fun w' y ↦ (J (φ w') y).toLinearMap.toContinuousLinearMap)
        (perturbationPullback φ Ks Kt stdComplexLineReal)
        (perturbationPullback φ Ks Kt stdComplexLineImag) (u ∘ φ) (ξ ∘ φ) w =
      (fderiv ℝ φ w stdComplexLineReal).1 •
          ω.floerLinearization (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap)
            Ks Kt u ξ (φ w) -
        (fderiv ℝ φ w stdComplexLineReal).2 • (J (φ w) (u (φ w))
          (ω.floerLinearization (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap)
            Ks Kt u ξ (φ w)) +
          fderiv ℝ (fun y ↦ (J (φ w) y).toLinearMap.toContinuousLinearMap) (u (φ w)) (ξ (φ w))
            (ω.floerOperator (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap)
              Ks Kt u (φ w))) := by
  set a := (fderiv ℝ φ w stdComplexLineReal).1
  set b := (fderiv ℝ φ w stdComplexLineReal).2
  have hc : ContDiffAt ℝ 2 (fun y : V ↦ (φ w, y)) (u (φ w)) :=
    contDiffAt_const.prodMk contDiffAt_id
  -- The derivative of `J(φ w, ·)` anticommutes with `J`.
  have hY := AlmostComplexStructure.mem_tangentSpace_of_hasFDerivAt hJ.hasFDerivAt (ξ (φ w))
  rw [AlmostComplexStructure.mem_tangentSpace_iff_apply] at hY
  simp only [ContinuousLinearMap.coe_coe] at hY
  -- The derivatives of `ξ ∘ φ` and `u ∘ φ`, in the columns `(a, b)` and `(-b, a)` of `dφ_w`.
  have hd (L : ℝ × ℝ →L[ℝ] V) (v : ℝ × ℝ) :
      L v = v.1 • L stdComplexLineReal + v.2 • L stdComplexLineImag := by
    simpa using (L : ℝ × ℝ →ₗ[ℝ] V).apply_stdComplexLine v
  have h₂ := hφJ.apply_stdComplexLineImag
  simp only [ContinuousLinearMap.coe_coe] at h₂
  have h₁ : fderiv ℝ φ w stdComplexLineReal = (a, b) := rfl
  have hKs₁ : DifferentiableAt ℝ (Ks (φ w)) (u (φ w)) :=
    (hKs.comp _ hc).differentiableAt (by norm_num)
  have hKt₁ : DifferentiableAt ℝ (Kt (φ w)) (u (φ w)) :=
    (hKt.comp _ hc).differentiableAt (by norm_num)
  have hXt := ω.hamiltonianVectorField_perturbationPullback hKs₁ hKt₁ stdComplexLineImag
  rw [floerLinearization_def, floerLinearization_def, floerOperator_def]
  simp only [Function.comp_apply, fderiv_comp w hξ hφ, fderiv_comp w hu hφ,
    ContinuousLinearMap.comp_apply, hXt,
    ω.fderiv_hamiltonianVectorField_perturbationPullback hKs hKt, h₂, h₁,
    AlmostComplexStructure.product_apply, _root_.add_apply, _root_.smul_apply]
  rw [hd (fderiv ℝ ξ (φ w)) (a, b), hd (fderiv ℝ ξ (φ w)) (-b, a),
    hd (fderiv ℝ u (φ w)) (-b, a)]
  simp only [LinearMap.coe_toContinuousLinearMap', map_add, map_sub, map_smul,
    AlmostComplexStructure.apply_apply, hY]
  module

/-- **Naturality of the linearized Floer operator along a solution.** If `u` solves the Floer
equation at `φ w`, the linearization along `u ∘ φ` for the pulled back data, applied to `ξ ∘ φ`,
is `(a - b J) D_u ξ(φ w)`, with `dφ_w ∂s = (a, b)` and `J = J(φ w, u(φ w))`. -/
theorem floerLinearization_perturbationPullback_of_floerOperator_eq_zero (ω : SymplecticForm V)
    (hφ : DifferentiableAt ℝ φ w)
    (hφJ : IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (AlmostComplexStructure.product ℝ) (fderiv ℝ φ w : ℝ × ℝ →ₗ[ℝ] ℝ × ℝ))
    (hu : DifferentiableAt ℝ u (φ w)) (hξ : DifferentiableAt ℝ ξ (φ w))
    (hKs : ContDiffAt ℝ 2 (uncurry Ks) (φ w, u (φ w)))
    (hKt : ContDiffAt ℝ 2 (uncurry Kt) (φ w, u (φ w)))
    (hJ : DifferentiableAt ℝ (fun y ↦ (J (φ w) y).toLinearMap.toContinuousLinearMap)
      (u (φ w)))
    (hF : ω.floerOperator (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap)
      Ks Kt u (φ w) = 0) :
    ω.floerLinearization (fun w' y ↦ (J (φ w') y).toLinearMap.toContinuousLinearMap)
        (perturbationPullback φ Ks Kt stdComplexLineReal)
        (perturbationPullback φ Ks Kt stdComplexLineImag) (u ∘ φ) (ξ ∘ φ) w =
      (fderiv ℝ φ w stdComplexLineReal).1 •
          ω.floerLinearization (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap)
            Ks Kt u ξ (φ w) -
        (fderiv ℝ φ w stdComplexLineReal).2 • J (φ w) (u (φ w))
          (ω.floerLinearization (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap)
            Ks Kt u ξ (φ w)) := by
  rw [ω.floerLinearization_perturbationPullback hφ hφJ hu hξ hKs hKt hJ, hF, map_zero, add_zero]

/-- **The linearized operator is conformally bounded under a change of coordinates.** Along a
solution, the norm of the linearization in the coordinates `w` is at most `(1 + M²) det dφ_w`
times that in the coordinates `φ w`, squared, where `M` bounds the norm of `J(φ w, u(φ w))`. -/
theorem norm_floerLinearization_perturbationPullback_sq_le (ω : SymplecticForm V) {M : ℝ}
    (hφ : DifferentiableAt ℝ φ w)
    (hφJ : IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (AlmostComplexStructure.product ℝ) (fderiv ℝ φ w : ℝ × ℝ →ₗ[ℝ] ℝ × ℝ))
    (hu : DifferentiableAt ℝ u (φ w)) (hξ : DifferentiableAt ℝ ξ (φ w))
    (hKs : ContDiffAt ℝ 2 (uncurry Ks) (φ w, u (φ w)))
    (hKt : ContDiffAt ℝ 2 (uncurry Kt) (φ w, u (φ w)))
    (hJ : DifferentiableAt ℝ (fun y ↦ (J (φ w) y).toLinearMap.toContinuousLinearMap)
      (u (φ w)))
    (hF : ω.floerOperator (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap)
      Ks Kt u (φ w) = 0)
    (hM : ‖(J (φ w) (u (φ w))).toLinearMap.toContinuousLinearMap‖ ≤ M) :
    ‖ω.floerLinearization (fun w' y ↦ (J (φ w') y).toLinearMap.toContinuousLinearMap)
        (perturbationPullback φ Ks Kt stdComplexLineReal)
        (perturbationPullback φ Ks Kt stdComplexLineImag) (u ∘ φ) (ξ ∘ φ) w‖ ^ 2 ≤
      (1 + M ^ 2) * (fderiv ℝ φ w).det *
        ‖ω.floerLinearization (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap)
          Ks Kt u ξ (φ w)‖ ^ 2 := by
  rw [ω.floerLinearization_perturbationPullback_of_floerOperator_eq_zero hφ hφJ hu hξ hKs hKt hJ
    hF, ContinuousLinearMap.det, hφJ.det_eq, ContinuousLinearMap.coe_coe]
  set a := (fderiv ℝ φ w stdComplexLineReal).1
  set b := (fderiv ℝ φ w stdComplexLineReal).2
  set D := ω.floerLinearization (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap)
    Ks Kt u ξ (φ w)
  have hJD : ‖J (φ w) (u (φ w)) D‖ ≤ M * ‖D‖ :=
    ((J (φ w) (u (φ w))).toLinearMap.toContinuousLinearMap.le_opNorm D).trans
      (mul_le_mul_of_nonneg_right hM (norm_nonneg D))
  have h₁ : ‖a • D - b • J (φ w) (u (φ w)) D‖ ≤ (|a| + |b| * M) * ‖D‖ := by
    calc ‖a • D - b • J (φ w) (u (φ w)) D‖
        ≤ ‖a • D‖ + ‖b • J (φ w) (u (φ w)) D‖ := norm_sub_le _ _
      _ = |a| * ‖D‖ + |b| * ‖J (φ w) (u (φ w)) D‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
      _ ≤ |a| * ‖D‖ + |b| * (M * ‖D‖) := by gcongr
      _ = (|a| + |b| * M) * ‖D‖ := by ring
  have h₂ : (|a| + |b| * M) ^ 2 ≤ (1 + M ^ 2) * (a ^ 2 + b ^ 2) := by
    nlinarith [sq_nonneg (|a| * M - |b|), sq_abs a, sq_abs b]
  calc ‖a • D - b • J (φ w) (u (φ w)) D‖ ^ 2 ≤ ((|a| + |b| * M) * ‖D‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h₁ 2
    _ = (|a| + |b| * M) ^ 2 * ‖D‖ ^ 2 := by ring
    _ ≤ (1 + M ^ 2) * (a ^ 2 + b ^ 2) * ‖D‖ ^ 2 := by gcongr

/-- **The linearized operator is conformally bounded below under a change of coordinates.** Along
a solution, `det dφ_w` times the norm of the linearization in the coordinates `φ w`, squared, is at
most `1 + M²` times that in the coordinates `w`, where `M` bounds the norm of `J(φ w, u(φ w))`. -/
theorem det_mul_norm_floerLinearization_sq_le (ω : SymplecticForm V) {M : ℝ}
    (hφ : DifferentiableAt ℝ φ w)
    (hφJ : IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (AlmostComplexStructure.product ℝ) (fderiv ℝ φ w : ℝ × ℝ →ₗ[ℝ] ℝ × ℝ))
    (hu : DifferentiableAt ℝ u (φ w)) (hξ : DifferentiableAt ℝ ξ (φ w))
    (hKs : ContDiffAt ℝ 2 (uncurry Ks) (φ w, u (φ w)))
    (hKt : ContDiffAt ℝ 2 (uncurry Kt) (φ w, u (φ w)))
    (hJ : DifferentiableAt ℝ (fun y ↦ (J (φ w) y).toLinearMap.toContinuousLinearMap)
      (u (φ w)))
    (hF : ω.floerOperator (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap)
      Ks Kt u (φ w) = 0)
    (hM : ‖(J (φ w) (u (φ w))).toLinearMap.toContinuousLinearMap‖ ≤ M) :
    (fderiv ℝ φ w).det *
        ‖ω.floerLinearization (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap)
          Ks Kt u ξ (φ w)‖ ^ 2 ≤
      (1 + M ^ 2) *
        ‖ω.floerLinearization (fun w' y ↦ (J (φ w') y).toLinearMap.toContinuousLinearMap)
          (perturbationPullback φ Ks Kt stdComplexLineReal)
          (perturbationPullback φ Ks Kt stdComplexLineImag) (u ∘ φ) (ξ ∘ φ) w‖ ^ 2 := by
  rw [ω.floerLinearization_perturbationPullback_of_floerOperator_eq_zero hφ hφJ hu hξ hKs hKt hJ
    hF, ContinuousLinearMap.det, hφJ.det_eq, ContinuousLinearMap.coe_coe]
  set a := (fderiv ℝ φ w stdComplexLineReal).1
  set b := (fderiv ℝ φ w stdComplexLineReal).2
  set D := ω.floerLinearization (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap)
    Ks Kt u ξ (φ w)
  set D' := a • D - b • J (φ w) (u (φ w)) D
  have hJD : ‖J (φ w) (u (φ w)) D'‖ ≤ M * ‖D'‖ :=
    ((J (φ w) (u (φ w))).toLinearMap.toContinuousLinearMap.le_opNorm D').trans
      (mul_le_mul_of_nonneg_right hM (norm_nonneg D'))
  -- `(a + b J)(a - b J) = a² + b²`.
  have hD : (a ^ 2 + b ^ 2) • D = a • D' + b • J (φ w) (u (φ w)) D' := by
    simp only [D', AlmostComplexStructure.apply_sub, AlmostComplexStructure.apply_smul,
      AlmostComplexStructure.apply_apply]
    module
  have h₁ : (a ^ 2 + b ^ 2) * ‖D‖ ≤ (|a| + |b| * M) * ‖D'‖ := by
    calc (a ^ 2 + b ^ 2) * ‖D‖ = ‖a • D' + b • J (φ w) (u (φ w)) D'‖ := by
          rw [← hD, norm_smul, Real.norm_of_nonneg (by positivity)]
      _ ≤ ‖a • D'‖ + ‖b • J (φ w) (u (φ w)) D'‖ := norm_add_le _ _
      _ = |a| * ‖D'‖ + |b| * ‖J (φ w) (u (φ w)) D'‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
      _ ≤ |a| * ‖D'‖ + |b| * (M * ‖D'‖) := by gcongr
      _ = (|a| + |b| * M) * ‖D'‖ := by ring
  have h₂ : (|a| + |b| * M) ^ 2 ≤ (1 + M ^ 2) * (a ^ 2 + b ^ 2) := by
    nlinarith [sq_nonneg (|a| * M - |b|), sq_abs a, sq_abs b]
  rcases (by positivity : 0 ≤ a ^ 2 + b ^ 2).eq_or_lt with h₀ | hpos
  · rw [← h₀, zero_mul]
    positivity
  refine le_of_mul_le_mul_left ?_ hpos
  calc (a ^ 2 + b ^ 2) * ((a ^ 2 + b ^ 2) * ‖D‖ ^ 2) = ((a ^ 2 + b ^ 2) * ‖D‖) ^ 2 := by ring
    _ ≤ ((|a| + |b| * M) * ‖D'‖) ^ 2 := pow_le_pow_left₀ (by positivity) h₁ 2
    _ = (|a| + |b| * M) ^ 2 * ‖D'‖ ^ 2 := by ring
    _ ≤ (1 + M ^ 2) * (a ^ 2 + b ^ 2) * ‖D'‖ ^ 2 := by gcongr
    _ = (a ^ 2 + b ^ 2) * ((1 + M ^ 2) * ‖D'‖ ^ 2) := by ring

section Integral

variable {s : Set (ℝ × ℝ)} {M : ℝ}

/-- **Conformal invariance of the `L²` norm of the linearized operator, upper bound.** Let `φ` be
injective on a measurable set `s`, with complex linear derivative, and let `u` solve the Floer
equation on `φ '' s`, with `J` bounded by `M` there. Then the `L²` norm over `s` of the
linearization along `u ∘ φ` for the pulled back data, applied to `ξ ∘ φ`, is at most `1 + M²`
times the `L²` norm of `D_u ξ` over `φ '' s`, squared. -/
theorem setIntegral_norm_floerLinearization_perturbationPullback_sq_le (ω : SymplecticForm V)
    (hs : MeasurableSet s) (hinj : InjOn φ s) (hφ : ∀ w ∈ s, DifferentiableAt ℝ φ w)
    (hφJ : ∀ w ∈ s, IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (AlmostComplexStructure.product ℝ) (fderiv ℝ φ w : ℝ × ℝ →ₗ[ℝ] ℝ × ℝ))
    (hu : ∀ w ∈ s, DifferentiableAt ℝ u (φ w)) (hξ : ∀ w ∈ s, DifferentiableAt ℝ ξ (φ w))
    (hKs : ∀ w ∈ s, ContDiffAt ℝ 2 (uncurry Ks) (φ w, u (φ w)))
    (hKt : ∀ w ∈ s, ContDiffAt ℝ 2 (uncurry Kt) (φ w, u (φ w)))
    (hJ : ∀ w ∈ s, DifferentiableAt ℝ
      (fun y ↦ (J (φ w) y).toLinearMap.toContinuousLinearMap) (u (φ w)))
    (hF : ∀ w ∈ s, ω.floerOperator (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap)
      Ks Kt u (φ w) = 0)
    (hM : ∀ w ∈ s, ‖(J (φ w) (u (φ w))).toLinearMap.toContinuousLinearMap‖ ≤ M)
    (hint : IntegrableOn (fun z ↦ ‖ω.floerLinearization
      (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) Ks Kt u ξ z‖ ^ 2) (φ '' s)) :
    ∫ w in s, ‖ω.floerLinearization (fun w' y ↦ (J (φ w') y).toLinearMap.toContinuousLinearMap)
        (perturbationPullback φ Ks Kt stdComplexLineReal)
        (perturbationPullback φ Ks Kt stdComplexLineImag) (u ∘ φ) (ξ ∘ φ) w‖ ^ 2 ≤
      (1 + M ^ 2) * ∫ z in φ '' s, ‖ω.floerLinearization
        (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) Ks Kt u ξ z‖ ^ 2 := by
  -- Lebesgue measure on `ℝ × ℝ` is the product measure, an additive Haar measure.
  have := Measure.prod.instIsAddHaarMeasure (volume : Measure ℝ) (volume : Measure ℝ)
  have hφ' (w : ℝ × ℝ) (hw : w ∈ s) : HasFDerivWithinAt φ (fderiv ℝ φ w) s w :=
    (hφ w hw).hasFDerivAt.hasFDerivWithinAt
  rw [integral_image_eq_integral_abs_det_fderiv_smul volume hs hφ' hinj, ← integral_const_mul]
  refine integral_mono_of_nonneg (Eventually.of_forall fun _ ↦ by positivity)
    ((((integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume hs hφ' hinj _).1
      hint).const_mul (1 + M ^ 2))) ((ae_restrict_iff' hs).2 (Eventually.of_forall fun w hw ↦ ?_))
  dsimp only
  rw [smul_eq_mul, abs_of_nonneg (by rw [ContinuousLinearMap.det, (hφJ w hw).det_eq]; positivity),
    ← mul_assoc]
  exact ω.norm_floerLinearization_perturbationPullback_sq_le (hφ w hw) (hφJ w hw) (hu w hw)
    (hξ w hw) (hKs w hw) (hKt w hw) (hJ w hw) (hF w hw) (hM w hw)

/-- **Conformal invariance of the `L²` norm of the linearized operator, lower bound.** Let `φ` be
injective on a measurable set `s`, with complex linear derivative, and let `u` solve the Floer
equation on `φ '' s`, with `J` bounded by `M` there. Then the `L²` norm of `D_u ξ` over `φ '' s`
is at most `1 + M²` times the `L²` norm over `s` of the linearization along `u ∘ φ` for the pulled
back data, applied to `ξ ∘ φ`, squared. -/
theorem setIntegral_image_norm_floerLinearization_sq_le (ω : SymplecticForm V)
    (hs : MeasurableSet s) (hinj : InjOn φ s) (hφ : ∀ w ∈ s, DifferentiableAt ℝ φ w)
    (hφJ : ∀ w ∈ s, IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (AlmostComplexStructure.product ℝ) (fderiv ℝ φ w : ℝ × ℝ →ₗ[ℝ] ℝ × ℝ))
    (hu : ∀ w ∈ s, DifferentiableAt ℝ u (φ w)) (hξ : ∀ w ∈ s, DifferentiableAt ℝ ξ (φ w))
    (hKs : ∀ w ∈ s, ContDiffAt ℝ 2 (uncurry Ks) (φ w, u (φ w)))
    (hKt : ∀ w ∈ s, ContDiffAt ℝ 2 (uncurry Kt) (φ w, u (φ w)))
    (hJ : ∀ w ∈ s, DifferentiableAt ℝ
      (fun y ↦ (J (φ w) y).toLinearMap.toContinuousLinearMap) (u (φ w)))
    (hF : ∀ w ∈ s, ω.floerOperator (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap)
      Ks Kt u (φ w) = 0)
    (hM : ∀ w ∈ s, ‖(J (φ w) (u (φ w))).toLinearMap.toContinuousLinearMap‖ ≤ M)
    (hint : IntegrableOn (fun w ↦ ‖ω.floerLinearization
      (fun w' y ↦ (J (φ w') y).toLinearMap.toContinuousLinearMap)
      (perturbationPullback φ Ks Kt stdComplexLineReal)
      (perturbationPullback φ Ks Kt stdComplexLineImag) (u ∘ φ) (ξ ∘ φ) w‖ ^ 2) s) :
    ∫ z in φ '' s, ‖ω.floerLinearization
        (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) Ks Kt u ξ z‖ ^ 2 ≤
      (1 + M ^ 2) * ∫ w in s, ‖ω.floerLinearization
        (fun w' y ↦ (J (φ w') y).toLinearMap.toContinuousLinearMap)
        (perturbationPullback φ Ks Kt stdComplexLineReal)
        (perturbationPullback φ Ks Kt stdComplexLineImag) (u ∘ φ) (ξ ∘ φ) w‖ ^ 2 := by
  -- Lebesgue measure on `ℝ × ℝ` is the product measure, an additive Haar measure.
  have := Measure.prod.instIsAddHaarMeasure (volume : Measure ℝ) (volume : Measure ℝ)
  have hφ' (w : ℝ × ℝ) (hw : w ∈ s) : HasFDerivWithinAt φ (fderiv ℝ φ w) s w :=
    (hφ w hw).hasFDerivAt.hasFDerivWithinAt
  rw [integral_image_eq_integral_abs_det_fderiv_smul volume hs hφ' hinj, ← integral_const_mul]
  refine integral_mono_of_nonneg (Eventually.of_forall fun _ ↦ by positivity)
    (hint.const_mul (1 + M ^ 2)) ((ae_restrict_iff' hs).2 (Eventually.of_forall fun w hw ↦ ?_))
  dsimp only
  rw [smul_eq_mul, abs_of_nonneg (by rw [ContinuousLinearMap.det, (hφJ w hw).det_eq]; positivity)]
  exact ω.det_mul_norm_floerLinearization_sq_le (hφ w hw) (hφJ w hw) (hu w hw) (hξ w hw)
    (hKs w hw) (hKt w hw) (hJ w hw) (hF w hw) (hM w hw)

end Integral

end SymplecticForm

end TauCeti
