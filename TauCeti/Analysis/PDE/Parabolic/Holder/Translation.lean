/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Parabolic.Holder.Solvability
public import TauCeti.Analysis.Holder.Translation

/-!
# Spatial translations of parabolic problems

For `v : E`, the spatial translation `u ↦ u(· + v, ·)` is a linear isometric equivalence of the
order-two parabolic Hölder space `C_b^{2+α,1+α/2}(E × [a, b])`
(`TauCeti.ParabolicC2HolderSpace.translateLIE`). Its derivative fields are the translated fields
of `u`, and its spatial traces are the translated traces.

Translating `u` and the coefficients of the parabolic operator
`P u = ∂ₜu - A·D_x²u - B·D_xu - C·u` translates `P u`. Consequently the solution operator of the
Cauchy problem `P u = f`, `u(·, 0) = g` on `ℝⁿ × [0, T]` is covariant: the solution with
translated coefficients and translated data `(f(· + v, ·), g(· + v))` is the translate of the
solution (`TauCeti.ParabolicC2HolderSpace.euclideanInitialDataCLE_symm_translate`). When the
coefficients are invariant under the translation, the solution operator commutes with it
(`TauCeti.ParabolicC2HolderSpace.euclideanInitialDataCLE_symm_translate_of_invariant`).

## Main declarations

All declarations are in the `TauCeti.ParabolicC2HolderSpace` namespace.

* `translateLIE`: the spatial translation `u ↦ u(· + v, ·)`, with its fields and its spatial
  traces.
* `parabolicOperatorL_translateLIE` and `euclideanParabolicOperatorL_translateLIE`: translating
  the coefficients and the solution translates the forcing.
* `ellipticity_compIsometryEquivLIE`: translated coefficients stay uniformly elliptic.
* `euclideanInitialDataCLE_symm_translate`: translation covariance of the solution operator.
* `euclideanInitialDataCLE_symm_translate_of_invariant`: the solution operator commutes with
  translations that leave the coefficients invariant.

## References

* A. Lunardi, *Linear and nonlinear diffusion problems*, Cortona lecture notes, 2004, Chapter 4.
-/

public section
noncomputable section

namespace TauCeti.ParabolicC2HolderSpace

open Set ParabolicSpaceTime
open scoped NNReal BoundedContinuousFunction

variable {α : ℝ≥0} {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A local shortcut for the norm on Hessians. Without it, instance search for the operator norm
on `(E →L[ℝ] E →L[ℝ] F) →L[ℝ] F`, the coefficient space of the second-order term, fails, for the
reason explained in `TauCeti.Analysis.PDE.Parabolic.Holder.Operator`. -/
local instance instNormedAddCommGroupTranslationHessian :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] F) := inferInstance
/-- A local shortcut for scalar operations on Hessians, needed for the same reason. -/
local instance instNormedSpaceTranslationHessian :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] F) := inferInstance

/-! ### The translation isometry -/

section Translation

variable {a b : ℝ} {hab : a < b}

/-- The spatial translation `u ↦ u(· + v, ·)` of an order-two parabolic Hölder map. -/
private def translate (v : E) (u : ParabolicC2HolderSpace α E F hab) :
    ParabolicC2HolderSpace α E F hab :=
  mk ((valueL u).compContinuous
      ⟨_, (slabSpaceIsometryEquiv (a := a) (b := b) (IsometryEquiv.addRight v)).continuous⟩)
    ((spatialFDerivL u).compContinuous
      ⟨_, (slabSpaceIsometryEquiv (a := a) (b := b) (IsometryEquiv.addRight v)).continuous⟩)
    (HolderSpace.compIsometryEquivLIE α _ (slabSpaceIsometryEquiv (IsometryEquiv.addRight v))
      (spatialSecondFDerivL u))
    (HolderSpace.compIsometryEquivLIE α _ (slabSpaceIsometryEquiv (IsometryEquiv.addRight v))
      (timeDerivL u))
    (fun t x ↦ by
      simpa using (hasFDerivAt_comp_add_right v).2 (u.hasSpatialFDerivAt t (x + v)))
    (fun t x ↦ by
      simpa using (hasFDerivAt_comp_add_right v).2 (u.hasSpatialSecondFDerivAt t (x + v)))
    (fun x t ↦ by
      simpa [timeExtension_def] using u.hasTimeDerivWithinAt (x + v) t)

private theorem translate_apply (v : E) (u : ParabolicC2HolderSpace α E F hab)
    (p : slab (E := E) a b) : translate v u p = u (slabSpaceMap (IsometryEquiv.addRight v) p) := by
  simp [translate]

private theorem norm_translate_le (v : E) (u : ParabolicC2HolderSpace α E F hab) :
    ‖translate v u‖ ≤ ‖u‖ := by
  rw [norm_eq, norm_eq u, translate, valueL_mk, spatialFDerivL_mk, spatialSecondFDerivL_mk,
    timeDerivL_mk, LinearIsometryEquiv.norm_map, LinearIsometryEquiv.norm_map]
  gcongr
  · exact BoundedContinuousFunction.norm_compContinuous_le _ _
  · exact BoundedContinuousFunction.norm_compContinuous_le _ _

variable (α F hab) in
/-- The spatial translation `u ↦ u(· + v, ·)` of order-two parabolic Hölder maps on
`E × [a, b]`, as a linear isometric equivalence. Its inverse is the translation by `-v`. -/
def translateLIE (v : E) :
    ParabolicC2HolderSpace α E F hab ≃ₗᵢ[ℝ] ParabolicC2HolderSpace α E F hab :=
  LinearIsometryEquiv.ofBounds
    { toFun := translate v
      invFun := translate (-v)
      map_add' u w := by ext p; simp only [translate_apply, add_apply]
      map_smul' c u := by ext p; simp only [translate_apply, smul_apply, RingHom.id_apply]
      left_inv u := by
        ext p
        obtain ⟨x, t, rfl⟩ : ∃ x t, slabMk x t = p := ⟨_, _, slabMk_space_slabTime p⟩
        simp [translate_apply]
      right_inv u := by
        ext p
        obtain ⟨x, t, rfl⟩ : ∃ x t, slabMk x t = p := ⟨_, _, slabMk_space_slabTime p⟩
        simp [translate_apply] }
    (norm_translate_le v) (norm_translate_le (-v))

private theorem translateLIE_eq_translate (v : E) (u : ParabolicC2HolderSpace α E F hab) :
    translateLIE α F hab v u = translate v u :=
  (rfl)

@[simp]
theorem translateLIE_apply (v : E) (u : ParabolicC2HolderSpace α E F hab)
    (p : slab (E := E) a b) :
    translateLIE α F hab v u p = u (slabSpaceMap (IsometryEquiv.addRight v) p) := by
  rw [translateLIE_eq_translate, translate_apply]

/-- The spatial gradient of a translate is the translated gradient. -/
@[simp]
theorem spatialFDerivL_translateLIE (v : E) (u : ParabolicC2HolderSpace α E F hab)
    (p : slab (E := E) a b) :
    spatialFDerivL (translateLIE α F hab v u) p =
      spatialFDerivL u (slabSpaceMap (IsometryEquiv.addRight v) p) := by
  rw [translateLIE_eq_translate, translate, spatialFDerivL_mk]
  simp

/-- The spatial Hessian of a translate is the translated Hessian. -/
@[simp]
theorem spatialSecondFDerivL_translateLIE (v : E) (u : ParabolicC2HolderSpace α E F hab)
    (p : slab (E := E) a b) :
    spatialSecondFDerivL (translateLIE α F hab v u) p =
      spatialSecondFDerivL u (slabSpaceMap (IsometryEquiv.addRight v) p) := by
  rw [translateLIE_eq_translate, translate, spatialSecondFDerivL_mk]
  simp

/-- The time derivative of a translate is the translated time derivative. -/
@[simp]
theorem timeDerivL_translateLIE (v : E) (u : ParabolicC2HolderSpace α E F hab)
    (p : slab (E := E) a b) :
    timeDerivL (translateLIE α F hab v u) p =
      timeDerivL u (slabSpaceMap (IsometryEquiv.addRight v) p) := by
  rw [translateLIE_eq_translate, translate, timeDerivL_mk]
  simp

@[simp]
theorem translateLIE_symm (v : E) :
    (translateLIE α F hab v).symm = translateLIE α F hab (-v) := by
  ext u p
  rfl

@[simp]
theorem translateLIE_zero (u : ParabolicC2HolderSpace α E F hab) :
    translateLIE α F hab (0 : E) u = u := by
  ext p
  obtain ⟨x, t, rfl⟩ : ∃ x t, slabMk x t = p := ⟨_, _, slabMk_space_slabTime p⟩
  simp

/-- The spatial trace of a translate at time `t` is the translate of the spatial trace. -/
@[simp]
theorem spatialTrace_translateLIE (v : E) (u : ParabolicC2HolderSpace α E F hab) (t : Icc a b) :
    (translateLIE α F hab v u).spatialTrace t =
      CkHolderSpace.translateLIE 2 α F v (u.spatialTrace t) := by
  ext x
  simp

/-! ### Translation covariance of the parabolic operator -/

/-- Translating the coefficient fields `A`, `B`, `C` and the map `u` translates
`P u = ∂ₜu - A·D_x²u - B·D_xu - C·u`. -/
@[simp]
theorem parabolicOperatorL_translateLIE (hα : α ≤ 1) (v : E)
    (A : HolderSpace α (slab (E := E) a b) ((E →L[ℝ] E →L[ℝ] F) →L[ℝ] F))
    (B : HolderSpace α (slab (E := E) a b) ((E →L[ℝ] F) →L[ℝ] F))
    (C : HolderSpace α (slab (E := E) a b) (F →L[ℝ] F))
    (u : ParabolicC2HolderSpace α E F hab) :
    parabolicOperatorL hα
        (HolderSpace.compIsometryEquivLIE α _ (slabSpaceIsometryEquiv (IsometryEquiv.addRight v)) A)
        (HolderSpace.compIsometryEquivLIE α _ (slabSpaceIsometryEquiv (IsometryEquiv.addRight v)) B)
        (HolderSpace.compIsometryEquivLIE α _ (slabSpaceIsometryEquiv (IsometryEquiv.addRight v)) C)
        (translateLIE α F hab v u) =
      HolderSpace.compIsometryEquivLIE α F (slabSpaceIsometryEquiv (IsometryEquiv.addRight v))
        (parabolicOperatorL hα A B C u) := by
  ext p
  simp

end Translation

section Euclidean

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Translating the scalar coefficients `aⁱʲ`, `bⁱ`, `c` and the map `u` translates
`P u = ∂ₜu - aⁱʲ ∂ᵢ∂ⱼu - bⁱ ∂ᵢu - c u`. -/
@[simp]
theorem euclideanParabolicOperatorL_translateLIE {t₀ t₁ : ℝ} {ht : t₀ < t₁} (hα : α ≤ 1)
    (v : EuclideanSpace ℝ ι)
    (a : ι → ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) t₀ t₁) ℝ)
    (b : ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) t₀ t₁) ℝ)
    (c : HolderSpace α (slab (E := EuclideanSpace ℝ ι) t₀ t₁) ℝ)
    (u : ParabolicC2HolderSpace α (EuclideanSpace ℝ ι) ℝ ht) :
    euclideanParabolicOperatorL hα
        (fun i j ↦ HolderSpace.compIsometryEquivLIE α ℝ
          (slabSpaceIsometryEquiv (IsometryEquiv.addRight v)) (a i j))
        (fun i ↦ HolderSpace.compIsometryEquivLIE α ℝ
          (slabSpaceIsometryEquiv (IsometryEquiv.addRight v)) (b i))
        (HolderSpace.compIsometryEquivLIE α ℝ
          (slabSpaceIsometryEquiv (IsometryEquiv.addRight v)) c) (translateLIE α ℝ ht v u) =
      HolderSpace.compIsometryEquivLIE α ℝ (slabSpaceIsometryEquiv (IsometryEquiv.addRight v))
        (euclideanParabolicOperatorL hα a b c u) := by
  ext p
  simp

/-! ### Translation covariance of the solution operator -/

/-- Precomposing the coefficients `aⁱʲ` with an isometric equivalence `g` of the slab preserves
uniform ellipticity, with the same constant. -/
theorem ellipticity_compIsometryEquivLIE {t₀ t₁ : ℝ}
    (g : slab (E := EuclideanSpace ℝ ι) t₀ t₁ ≃ᵢ slab (E := EuclideanSpace ℝ ι) t₀ t₁)
    {a : ι → ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) t₀ t₁) ℝ}
    (ha : ∃ lam : ℝ, 0 < lam ∧ ∀ p (ξ : EuclideanSpace ℝ ι),
      lam * ‖ξ‖ ^ 2 ≤ (Matrix.of fun i j ↦ a i j p).toQuadraticForm' ξ) :
    ∃ lam : ℝ, 0 < lam ∧ ∀ p (ξ : EuclideanSpace ℝ ι),
      lam * ‖ξ‖ ^ 2 ≤
        (Matrix.of fun i j ↦ HolderSpace.compIsometryEquivLIE α ℝ g (a i j) p).toQuadraticForm' ξ :=
  ha.imp fun _ h ↦ ⟨h.1, fun p ξ ↦ by simpa using h.2 (g p) ξ⟩

variable {T : ℝ≥0} {hα₀ : 0 < α} {hα₁ : α < 1} {hT : (0 : ℝ) < T}

/-- **Translation covariance of the Cauchy problem.** The solution of the Cauchy problem
`P u = f(· + v, ·)`, `u(·, 0) = g(· + v)` for the operator with translated coefficients
`aⁱʲ(· + v, ·)`, `bⁱ(· + v, ·)`, `c(· + v, ·)` is the translate `u(· + v, ·)` of the solution of
`P u = f`, `u(·, 0) = g` for the original coefficients. -/
theorem euclideanInitialDataCLE_symm_translate (v : EuclideanSpace ℝ ι)
    {a : ι → ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ}
    {b : ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ}
    {c : HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ}
    (ha : ∃ lam : ℝ, 0 < lam ∧ ∀ p (ξ : EuclideanSpace ℝ ι),
      lam * ‖ξ‖ ^ 2 ≤ (Matrix.of fun i j ↦ a i j p).toQuadraticForm' ξ)
    (f : HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ)
    (g : CkHolderSpace 2 α (EuclideanSpace ℝ ι) ℝ) :
    (euclideanInitialDataCLE hα₀ hα₁ hT
        (fun i j ↦ HolderSpace.compIsometryEquivLIE α ℝ
          (slabSpaceIsometryEquiv (IsometryEquiv.addRight v)) (a i j))
        (fun i ↦ HolderSpace.compIsometryEquivLIE α ℝ
          (slabSpaceIsometryEquiv (IsometryEquiv.addRight v)) (b i))
        (HolderSpace.compIsometryEquivLIE α ℝ
          (slabSpaceIsometryEquiv (IsometryEquiv.addRight v)) c)
        (ellipticity_compIsometryEquivLIE _ ha)).symm
        (HolderSpace.compIsometryEquivLIE α ℝ (slabSpaceIsometryEquiv (IsometryEquiv.addRight v)) f,
          CkHolderSpace.translateLIE 2 α ℝ v g) =
      translateLIE α ℝ hT v ((euclideanInitialDataCLE hα₀ hα₁ hT a b c ha).symm (f, g)) := by
  rw [ContinuousLinearEquiv.symm_apply_eq, euclideanInitialDataCLE_apply,
    euclideanParabolicOperatorL_translateLIE, spatialTrace_translateLIE,
    euclideanParabolicOperatorL_euclideanInitialDataCLE_symm_apply,
    spatialTrace_euclideanInitialDataCLE_symm_apply]

/-- **The solution operator commutes with translations leaving the coefficients invariant.** If
`aⁱʲ(· + v, ·) = aⁱʲ`, `bⁱ(· + v, ·) = bⁱ` and `c(· + v, ·) = c`, then the solution of the Cauchy
problem `P u = f(· + v, ·)`, `u(·, 0) = g(· + v)` is the translate `u(· + v, ·)` of the solution
of `P u = f`, `u(·, 0) = g`. -/
theorem euclideanInitialDataCLE_symm_translate_of_invariant (v : EuclideanSpace ℝ ι)
    {a : ι → ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ}
    {b : ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ}
    {c : HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ}
    (ha : ∃ lam : ℝ, 0 < lam ∧ ∀ p (ξ : EuclideanSpace ℝ ι),
      lam * ‖ξ‖ ^ 2 ≤ (Matrix.of fun i j ↦ a i j p).toQuadraticForm' ξ)
    (ha_inv : ∀ i j, HolderSpace.compIsometryEquivLIE α ℝ
      (slabSpaceIsometryEquiv (IsometryEquiv.addRight v)) (a i j) = a i j)
    (hb_inv : ∀ i, HolderSpace.compIsometryEquivLIE α ℝ
      (slabSpaceIsometryEquiv (IsometryEquiv.addRight v)) (b i) = b i)
    (hc_inv : HolderSpace.compIsometryEquivLIE α ℝ
      (slabSpaceIsometryEquiv (IsometryEquiv.addRight v)) c = c)
    (f : HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ)
    (g : CkHolderSpace 2 α (EuclideanSpace ℝ ι) ℝ) :
    (euclideanInitialDataCLE hα₀ hα₁ hT a b c ha).symm
        (HolderSpace.compIsometryEquivLIE α ℝ (slabSpaceIsometryEquiv (IsometryEquiv.addRight v)) f,
          CkHolderSpace.translateLIE 2 α ℝ v g) =
      translateLIE α ℝ hT v ((euclideanInitialDataCLE hα₀ hα₁ hT a b c ha).symm (f, g)) := by
  have h := euclideanInitialDataCLE_symm_translate (hα₀ := hα₀) (hα₁ := hα₁) (hT := hT) (b := b)
    (c := c) v ha f g
  simpa only [ha_inv, hb_inv, hc_inv] using h

end Euclidean

end TauCeti.ParabolicC2HolderSpace
