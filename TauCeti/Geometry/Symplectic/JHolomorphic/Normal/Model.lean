/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Calculus
public import TauCeti.Analysis.Calculus.DifferentialForm.Basic
public import TauCeti.Analysis.Calculus.DifferentialForm.Regularity
public import TauCeti.Analysis.Complex.Wirtinger.Basic
public import TauCeti.Geometry.Symplectic.Complex.Line
public import TauCeti.Geometry.Symplectic.JHolomorphic.Varying
public import TauCeti.Geometry.Symplectic.Liouville.Linear
public import TauCeti.Geometry.Symplectic.Prod.Skew
import Mathlib.Topology.Algebra.Module.FiniteDimensionBilinear
import TauCeti.Geometry.Symplectic.JHolomorphic.Prod.Skew
import TauCeti.Geometry.Symplectic.CompatibleMetric

/-!
# The linear normal model of a pseudoholomorphic curve and its taming form

Let `C` be an embedded pseudoholomorphic curve in an almost complex four-manifold, with complex
normal line `N_C` and real normal Cauchy–Riemann operator `D_C`. Over a holomorphic chart `z` of
the base and in a unitary frame of `N_C` with fibre coordinate `w`, the operator reads

`D_C s = ∂bar s + ν s + μ conj s`

for complex functions `ν` and `μ` on the base. These are the values on `1` of the `(0,1)`-form
coefficients of `D_C` in `TauCeti.Analysis.Complex.Wirtinger.RootBranch`. Dilating the normal
directions of the ambient almost complex structure about `C` produces, in the limit, an almost
complex structure `J_N` on the total space of `N_C` whose holomorphic sections are the solutions
of `D_C s = 0`. This file constructs `J_N` and a closed form taming it in these coordinates, on
`ℂ × ℂ` with base coordinate `z` and fibre coordinate `w`. The convergence of the rescaled
ambient structures to `J_N` is not treated here.

## The structure `J_N`

At `p = (z, w)`, put `c = ν(z) w + μ(z) conj w`. Then (`TauCeti.normalModelStructure`)

`J_N(p)(ξ, η) = (I ξ, I η + 2 I c conj ξ)`,

the skew product (`TauCeti.AlmostComplexStructure.skewProd`) of multiplication by `I` on the base
and on the fibre along the real-linear map `ξ ↦ -c conj ξ`. Then:

* the projection to the base is `J_N`-holomorphic, and the fibres `{z₀} × ℂ` are
  `J_N`-holomorphic discs with the standard structure
  (`TauCeti.isJHolomorphic_fst_normalModelStructure`,
  `TauCeti.isJHolomorphic_prodMk_right_normalModelStructure`); a map into a single fibre is
  `J_N`-holomorphic exactly when it is holomorphic into `ℂ`
  (`TauCeti.isJHolomorphicAt_prodMk_right_normalModelStructure_iff`);
* the graph of a section `s` is `J_N`-holomorphic exactly when `s` is differentiable and
  `∂bar s + ν s + μ conj s = 0` (`TauCeti.isJHolomorphicAt_graph_normalModelStructure_iff`,
  `TauCeti.isJHolomorphic_graph_normalModelStructure_iff`), where
  `∂bar s = TauCeti.conjWirtingerDeriv s z 1`;
* since `c` is linear over `ℝ` in `w`, the fibrewise dilations `(z, w) ↦ (z, a w)`, `a ∈ ℝ`, are
  `J_N`-holomorphic (`TauCeti.isJHolomorphic_prodMap_id_smul_normalModelStructure`).

## The taming form

For a real connection one-form `A` on the base and a constant `K`, the one-form
(`TauCeti.normalModelPrimitive`)

`λ(z, w)(ξ, η) = (K ω(z, ξ) + ω(w, η) + |w|² A(z) ξ) / 2`,

with `ω(u, v) = Im (conj u * v)` the standard area form, is `K λ₀ + (ρ² / 2) (dθ + A)` in polar
coordinates `w = ρ e^{iθ}`, where `dλ₀ = ω` on the base. Its exterior derivative
`Ω = dλ = K π^*ω + d((ρ² / 2) (dθ + A))` (`TauCeti.normalModelForm`) is closed
(`TauCeti.extDeriv_normalModelForm_apply`, `TauCeti.extDeriv_normalModelForm`) and is given by
(`TauCeti.normalModelForm_apply`)

`Ω(X, Y) = K ω(ξ, ξ') + ω(η, η') + ⟪w, η⟫ A(z) ξ' - ⟪w, η'⟫ A(z) ξ + (|w|² / 2) dA(z)(ξ, ξ')`

for `X = (ξ, η)` and `Y = (ξ', η')`. It restricts to the area form on every fibre
(`TauCeti.normalModelForm_apply_vertical`). The perturbation terms of `J_N` and of `Ω` relative to
the split model are of size `|w|`, while the base term grows with `K`, so `Ω` tames `J_N` on
bounded disc bundles once `K` is large: if `|w| ≤ R`, `|ν(z)| + |μ(z)| ≤ m`, `‖A(z)‖ ≤ a`,
`‖dA(z)‖ ≤ b` and `K ≥ R² (3 (m + a)² + b) + δ`, then

`δ |ξ|² + |η|² / 2 ≤ Ω(X, J_N X)`

(`TauCeti.le_normalModelForm_apply_normalModelStructure`). Over a compact set of the base a single
`K` therefore makes `Ω` tame `J_N` on the whole disc bundle of radius `R`
(`TauCeti.exists_forall_normalModelForm_apply_normalModelStructure_pos`). Pairing currents with
`Ω` is what bounds the mass of positive closed currents, in particular of `J_N`-holomorphic
curves, in the normal bundle.

## References

* C. H. Taubes, *SW ⇒ Gr: from the Seiberg–Witten equations to pseudo-holomorphic curves*,
  J. Amer. Math. Soc. 9 (1996), 845–918.
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Sections 2.2 and 8.1 (taming forms and skew products of almost complex structures).
-/

public section

namespace TauCeti

open Complex ComplexConjugate
open scoped InnerProductSpace

/-- The real-linear map `ξ ↦ -(c conj ξ)`, the shear of the normal model. -/
private def normalModelShear (c : ℂ) : ℂ →ₗ[ℝ] ℂ :=
  (-c) • Complex.conjAe.toLinearMap

/-- The almost complex structure `J_N` on the total space `ℂ × ℂ` of a trivialized complex line
over a planar base, determined by the real Cauchy–Riemann operator
`D s = ∂bar s + ν s + μ conj s`. At `p = (z, w)` it is the skew product of the two standard
structures along `ξ ↦ -(c conj ξ)`, `c = ν z w + μ z conj w`. -/
noncomputable def normalModelStructure (ν μ : ℂ → ℂ) (p : ℂ × ℂ) :
    AlmostComplexStructure (ℂ × ℂ) :=
  (AlmostComplexStructure.ofComplexModule ℂ).skewProd (AlmostComplexStructure.ofComplexModule ℂ)
    (normalModelShear (ν p.1 * p.2 + μ p.1 * conj p.2))

@[simp]
theorem normalModelStructure_apply (ν μ : ℂ → ℂ) (p ξ : ℂ × ℂ) :
    normalModelStructure ν μ p ξ =
      (I * ξ.1, I * ξ.2 + 2 * I * (ν p.1 * p.2 + μ p.1 * conj p.2) * conj ξ.1) := by
  simp only [normalModelStructure, AlmostComplexStructure.skewProd_apply,
    AlmostComplexStructure.ofComplexModule_apply, smul_eq_mul, normalModelShear,
    LinearMap.smul_apply, AlgEquiv.toLinearMap_apply, Complex.conjAe_coe, map_mul, conj_I,
    Prod.mk.injEq, true_and]
  ring

variable {ν μ : ℂ → ℂ}

/-- **The projection to the base is holomorphic**: `J_N` lies over the standard structure of the
base. -/
theorem isJHolomorphic_fst_normalModelStructure :
    IsJHolomorphic (normalModelStructure ν μ) (fun _ ↦ AlmostComplexStructure.ofComplexModule ℂ)
      Prod.fst :=
  AlmostComplexStructure.isJHolomorphic_fst_skewProd (J₁ := fun _ ↦ _)

/-- **Vertical maps.** A map `y ↦ (z₀, g y)` into the fibre over `z₀` is `J_N`-holomorphic at `y`
exactly when `g` is holomorphic at `y` into `ℂ` with its standard structure. -/
theorem isJHolomorphicAt_prodMk_right_normalModelStructure_iff {U : Type*}
    [NormedAddCommGroup U] [NormedSpace ℝ U] {J : U → AlmostComplexStructure U} {g : U → ℂ}
    {z₀ : ℂ} {y : U} :
    IsJHolomorphicAt J (normalModelStructure ν μ) (fun y ↦ (z₀, g y)) y ↔
      IsJHolomorphicAt J (fun _ ↦ AlmostComplexStructure.ofComplexModule ℂ) g y :=
  AlmostComplexStructure.isJHolomorphicAt_prodMk_right_skewProd_iff (J₁ := fun _ ↦ _)

/-- **The normal fibres are holomorphic discs**: `J_N` restricts to multiplication by `I` on the
vertical tangent spaces, so every fibre `{z₀} × ℂ` is a `J_N`-holomorphic curve. -/
theorem isJHolomorphic_prodMk_right_normalModelStructure (z₀ : ℂ) :
    IsJHolomorphic (fun _ ↦ AlmostComplexStructure.ofComplexModule ℂ) (normalModelStructure ν μ)
      (fun w ↦ (z₀, w)) :=
  (isJHolomorphic_iff _ _ _).2 fun w ↦
    isJHolomorphicAt_prodMk_right_normalModelStructure_iff.2 (isJHolomorphicAt_id _ w)

/-- **Invariance under normal dilations.** For every real `a`, the fibrewise dilation
`(z, w) ↦ (z, a w)` is `J_N`-holomorphic, because `J_N` depends linearly on the normal
coordinate. This scale invariance is the one expected of a limit of normal rescalings. -/
theorem isJHolomorphic_prodMap_id_smul_normalModelStructure (a : ℝ) :
    IsJHolomorphic (normalModelStructure ν μ) (normalModelStructure ν μ)
      (Prod.map id (a • ·)) := by
  refine (isJHolomorphic_iff _ _ _).2 fun p ↦ ?_
  refine isJHolomorphicAt_of_hasFDerivAt (f' := (ContinuousLinearMap.fst ℝ ℂ ℂ).prod
      (a • ContinuousLinearMap.snd ℝ ℂ ℂ)) ?_ ?_
  · exact hasFDerivAt_fst.prodMk ((hasFDerivAt_snd (p := p)).const_smul a)
  · rw [isComplexLinearMap_iff_apply]
    intro ξ
    simp only [normalModelStructure_apply, Prod.map_fst, Prod.map_snd, id_eq,
      ContinuousLinearMap.coe_coe, ContinuousLinearMap.prod_apply, ContinuousLinearMap.coe_fst',
      smul_apply, ContinuousLinearMap.coe_snd', Complex.real_smul, map_mul,
      conj_ofReal, Prod.mk.injEq, true_and]
    ring

/-- **Holomorphic sections are the kernel of the normal operator.** A section `s` has
`J_N`-holomorphic graph at `z` exactly when it is differentiable at `z` and solves the real
Cauchy–Riemann equation `∂bar s + ν s + μ conj s = 0` there. -/
theorem isJHolomorphicAt_graph_normalModelStructure_iff {s : ℂ → ℂ} {z : ℂ} :
    IsJHolomorphicAt (fun _ ↦ AlmostComplexStructure.ofComplexModule ℂ) (normalModelStructure ν μ)
        (fun z ↦ (z, s z)) z ↔
      DifferentiableAt ℝ s z ∧ conjWirtingerDeriv s z 1 + ν z * s z + μ z * conj (s z) = 0 := by
  -- complex linearity of the graph derivative reduces to one complex identity in `ξ`
  have key : ∀ ξ : ℂ, (fderiv ℝ s z (I * ξ) =
      I * fderiv ℝ s z ξ + 2 * I * (ν z * s z + μ z * conj (s z)) * conj ξ) ↔
      2 * I * conj ξ * (conjWirtingerDeriv s z 1 + ν z * s z + μ z * conj (s z)) = 0 := by
    intro ξ
    rw [fderiv_apply_eq_smul_wirtingerDeriv_add_smul_conjWirtingerDeriv,
      fderiv_apply_eq_smul_wirtingerDeriv_add_smul_conjWirtingerDeriv]
    simp only [smul_eq_mul, map_mul, conj_I]
    constructor <;> intro h <;> linear_combination (-1 : ℂ) * h
  have hlin : IsComplexLinearMap (AlmostComplexStructure.ofComplexModule ℂ)
        (AlmostComplexStructure.ofComplexModule ℂ)
        ((fderiv ℝ s z : ℂ →ₗ[ℝ] ℂ) - normalModelShear (ν z * s z + μ z * conj (s z))) ↔
      ∀ ξ : ℂ, fderiv ℝ s z (I * ξ) =
        I * fderiv ℝ s z ξ + 2 * I * (ν z * s z + μ z * conj (s z)) * conj ξ := by
    rw [isComplexLinearMap_iff_apply]
    refine forall_congr' fun ξ ↦ ?_
    simp only [normalModelShear, AlmostComplexStructure.ofComplexModule_apply,
      LinearMap.sub_apply, LinearMap.smul_apply, ContinuousLinearMap.coe_coe,
      AlgEquiv.toLinearMap_apply, Complex.conjAe_coe, smul_eq_mul, map_mul, conj_I]
    constructor <;> intro h <;> linear_combination h
  refine (AlmostComplexStructure.isJHolomorphicAt_graph_skewProd_iff (J₁ := fun _ ↦ _)).trans
    (and_congr_right fun _ ↦ hlin.trans ⟨fun h ↦ ?_, fun h ξ ↦ (key ξ).2 ?_⟩)
  · simpa using (key 1).1 (h 1)
  · rw [h, mul_zero]

/-- **`J_N`-holomorphic sections are the solutions of the normal operator.** The graph of `s` is
`J_N`-holomorphic exactly when `s` is differentiable and solves `∂bar s + ν s + μ conj s = 0`
everywhere. -/
theorem isJHolomorphic_graph_normalModelStructure_iff {s : ℂ → ℂ} :
    IsJHolomorphic (fun _ ↦ AlmostComplexStructure.ofComplexModule ℂ) (normalModelStructure ν μ)
        (fun z ↦ (z, s z)) ↔
      Differentiable ℝ s ∧ ∀ z, conjWirtingerDeriv s z 1 + ν z * s z + μ z * conj (s z) = 0 := by
  simp only [isJHolomorphic_iff, isJHolomorphicAt_graph_normalModelStructure_iff]
  exact forall_and

/-! ### The taming form -/

/-- The constant-coefficient bilinear form `K ω(z, ξ) + ω(w, η)` on `ℂ × ℂ`, with `ω` the standard
area form. Its radial primitive is the constant-coefficient part of the primitive of the taming
form. -/
private noncomputable def normalModelBilin (K : ℝ) : (ℂ × ℂ) →L[ℝ] (ℂ × ℂ) →L[ℝ] ℝ :=
  K • stdComplexSymplecticForm.toBilinForm.toContinuousBilinearMap.bilinearComp
      (ContinuousLinearMap.fst ℝ ℂ ℂ) (ContinuousLinearMap.fst ℝ ℂ ℂ) +
    stdComplexSymplecticForm.toBilinForm.toContinuousBilinearMap.bilinearComp
      (ContinuousLinearMap.snd ℝ ℂ ℂ) (ContinuousLinearMap.snd ℝ ℂ ℂ)

private theorem normalModelBilin_apply (K : ℝ) (p u : ℂ × ℂ) :
    normalModelBilin K p u =
      K * stdComplexSymplecticForm p.1 u.1 + stdComplexSymplecticForm p.2 u.2 := by
  simp [normalModelBilin]

/-- The connection part `(|w|² / 2) A(z) ξ` of the primitive of the taming form. -/
private noncomputable def normalModelConnection (A : ℂ → ℂ [⋀^Fin 1]→L[ℝ] ℝ) (p : ℂ × ℂ) :
    (ℂ × ℂ) [⋀^Fin 1]→L[ℝ] ℝ :=
  (‖p.2‖ ^ 2 / 2) •
    ContinuousAlternatingMap.compContinuousLinearMapCLM (ContinuousLinearMap.fst ℝ ℂ ℂ) (A p.1)

/-- The primitive `λ` of the taming form of the normal model, for a parameter `K` and a real
connection one-form `A` on the base:

`λ(z, w)(ξ, η) = (K ω(z, ξ) + ω(w, η) + |w|² A(z) ξ) / 2`,

with `ω` the standard area form of `ℂ`. In polar coordinates `w = ρ e^{iθ}` on the fibre,
`ω(w, dw) = ρ² dθ`, so this is `K λ₀ + (ρ² / 2) (dθ + A)` with `dλ₀` the base area form. -/
noncomputable def normalModelPrimitive (K : ℝ) (A : ℂ → ℂ [⋀^Fin 1]→L[ℝ] ℝ) :
    ℂ × ℂ → (ℂ × ℂ) [⋀^Fin 1]→L[ℝ] ℝ :=
  ContinuousLinearMap.liouvilleFormCLM (normalModelBilin K) + normalModelConnection A

@[simp]
theorem normalModelPrimitive_apply (K : ℝ) (A : ℂ → ℂ [⋀^Fin 1]→L[ℝ] ℝ) (p : ℂ × ℂ)
    (v : Fin 1 → ℂ × ℂ) :
    normalModelPrimitive K A p v =
      (K * stdComplexSymplecticForm p.1 (v 0).1 + stdComplexSymplecticForm p.2 (v 0).2) / 2 +
        ‖p.2‖ ^ 2 / 2 * A p.1 (fun _ ↦ (v 0).1) := by
  have hv : (fun i ↦ (v i).1) = fun _ ↦ (v 0).1 := funext fun i ↦ by rw [Subsingleton.elim i 0]
  simp [normalModelPrimitive, normalModelConnection, normalModelBilin_apply, Function.comp_def, hv]
  ring

/-- The taming form `Ω = dλ` of the normal model (`normalModelPrimitive`). It is
`K π^*ω + d((ρ² / 2) (dθ + A))`: the base area form scaled by `K`, plus the area form of the
fibres twisted by the connection `A`. -/
noncomputable def normalModelForm (K : ℝ) (A : ℂ → ℂ [⋀^Fin 1]→L[ℝ] ℝ) (p : ℂ × ℂ) :
    (ℂ × ℂ) [⋀^Fin 2]→L[ℝ] ℝ :=
  extDeriv (normalModelPrimitive K A) p

/-- The taming form is the exterior derivative of its primitive. -/
theorem normalModelForm_def (K : ℝ) (A : ℂ → ℂ [⋀^Fin 1]→L[ℝ] ℝ) :
    normalModelForm K A = extDeriv (normalModelPrimitive K A) :=
  (rfl)

variable {K : ℝ} {A : ℂ → ℂ [⋀^Fin 1]→L[ℝ] ℝ}

private theorem differentiableAt_normalModelConnection {p : ℂ × ℂ}
    (hA : DifferentiableAt ℝ A p.1) : DifferentiableAt ℝ (normalModelConnection A) p := by
  have h₁ : DifferentiableAt ℝ (fun q : ℂ × ℂ ↦ ‖q.2‖ ^ 2 / 2) p := by
    have := DifferentiableAt.norm_sq ℝ (differentiableAt_snd (𝕜 := ℝ) (p := p))
    fun_prop
  exact h₁.smul ((ContinuousLinearMap.differentiableAt _).comp p (hA.comp p differentiableAt_fst))

theorem differentiableAt_normalModelPrimitive {p : ℂ × ℂ} (hA : DifferentiableAt ℝ A p.1) :
    DifferentiableAt ℝ (normalModelPrimitive K A) p :=
  (ContinuousLinearMap.differentiableAt _).add (differentiableAt_normalModelConnection hA)

theorem contDiffAt_normalModelPrimitive {n : WithTop ℕ∞} {p : ℂ × ℂ}
    (hA : ContDiffAt ℝ n A p.1) : ContDiffAt ℝ n (normalModelPrimitive K A) p := by
  have h₁ : ContDiffAt ℝ n (fun q : ℂ × ℂ ↦ ‖q.2‖ ^ 2 / 2) p := by
    have := ContDiffAt.norm_sq ℝ (contDiffAt_snd (𝕜 := ℝ) (E := ℂ) (F := ℂ) (n := n) (p := p))
    fun_prop
  exact (ContinuousLinearMap.contDiff _).contDiffAt.add
    (h₁.smul ((ContinuousLinearMap.contDiff _).contDiffAt.comp p (hA.comp p contDiffAt_fst)))

theorem contDiff_normalModelPrimitive {n : WithTop ℕ∞} (hA : ContDiff ℝ n A) :
    ContDiff ℝ n (normalModelPrimitive K A) :=
  contDiff_iff_contDiffAt.2 fun _ ↦ contDiffAt_normalModelPrimitive hA.contDiffAt

/-- The derivative of the coefficient `(|w|² / 2) A(z) ξ` of the connection part of the primitive
in the direction `v`. -/
private theorem fderiv_normalModelConnection_apply {p : ℂ × ℂ} (hA : DifferentiableAt ℝ A p.1)
    (u v : ℂ × ℂ) :
    fderiv ℝ (fun y ↦ normalModelConnection A y (fun _ ↦ u)) p v =
      ⟪p.2, v.2⟫_ℝ * A p.1 (fun _ ↦ u.1) + ‖p.2‖ ^ 2 / 2 * fderiv ℝ A p.1 v.1 (fun _ ↦ u.1) := by
  have hfun : (fun y ↦ normalModelConnection A y (fun _ ↦ u)) =
      fun y ↦ ‖y.2‖ ^ 2 * (2 : ℝ)⁻¹ * A y.1 (fun _ ↦ u.1) := by
    funext y
    simp [normalModelConnection, Function.comp_def, div_eq_mul_inv]
  have h₂ := (HasFDerivAt.norm_sq (hasFDerivAt_snd (𝕜 := ℝ) (p := p))).mul_const (2 : ℝ)⁻¹
  have h₃ : HasFDerivAt (fun y : ℂ × ℂ ↦ A y.1 (fun _ ↦ u.1))
      (((fderiv ℝ A p.1).comp (ContinuousLinearMap.fst ℝ ℂ ℂ)).flipAlternating
        (fun _ ↦ u.1)) p :=
    (hA.hasFDerivAt.comp p hasFDerivAt_fst).continuousAlternatingMap_apply_const _
  rw [hfun, (h₂.fun_mul h₃).fderiv]
  simp
  ring

/-- **The taming form in coordinates.** At `p = (z, w)`, for `A` differentiable at `z`,

`Ω(X, Y) = K ω(ξ, ξ') + ω(η, η') + ⟪w, η⟫ A(z) ξ' - ⟪w, η'⟫ A(z) ξ + (|w|² / 2) dA(z)(ξ, ξ')`

for `X = (ξ, η)` and `Y = (ξ', η')`. On the vertical tangent spaces it is the fibre area form,
and along the zero section it is `K π^*ω` plus the fibre area form. -/
theorem normalModelForm_apply {p : ℂ × ℂ} (hA : DifferentiableAt ℝ A p.1) (X Y : ℂ × ℂ) :
    normalModelForm K A p ![X, Y] =
      K * stdComplexSymplecticForm X.1 Y.1 + stdComplexSymplecticForm X.2 Y.2 +
        ⟪p.2, X.2⟫_ℝ * A p.1 (fun _ ↦ Y.1) - ⟪p.2, Y.2⟫_ℝ * A p.1 (fun _ ↦ X.1) +
        ‖p.2‖ ^ 2 / 2 * extDeriv A p.1 ![X.1, Y.1] := by
  have hskew (v w : ℂ × ℂ) : normalModelBilin K v w = -normalModelBilin K w v := by
    simp only [normalModelBilin_apply, stdComplexSymplecticForm_apply]
    ring
  rw [normalModelForm_def, normalModelPrimitive,
    extDeriv_add (ContinuousLinearMap.differentiableAt _)
      (differentiableAt_normalModelConnection hA),
    ContinuousAlternatingMap.add_apply,
    ContinuousLinearMap.extDeriv_liouvilleFormCLM_apply_of_skew _ two_ne_zero hskew,
    extDeriv_apply_pair_of_differentiableAt (differentiableAt_normalModelConnection hA),
    fderiv_normalModelConnection_apply hA, fderiv_normalModelConnection_apply hA,
    extDeriv_apply_pair, normalModelBilin_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

/-- **The taming form is closed** at every point over which the connection is `C²`: there it is
exact, `Ω = dλ`. -/
theorem extDeriv_normalModelForm_apply {p : ℂ × ℂ} (hA : ContDiffAt ℝ 2 A p.1) :
    extDeriv (normalModelForm K A) p = 0 :=
  extDeriv_extDeriv_apply (contDiffAt_normalModelPrimitive hA) (by simp)

/-- **The taming form is closed**: it is exact, `Ω = dλ`, for a `C²` connection. -/
theorem extDeriv_normalModelForm (hA : ContDiff ℝ 2 A) :
    extDeriv (normalModelForm K A) = 0 :=
  funext fun _ ↦ extDeriv_normalModelForm_apply hA.contDiffAt

/-- On the vertical tangent spaces the taming form is the area form of the fibre. -/
theorem normalModelForm_apply_vertical {p : ℂ × ℂ} (hA : DifferentiableAt ℝ A p.1) (η η' : ℂ) :
    normalModelForm K A p ![(0, η), (0, η')] = stdComplexSymplecticForm η η' := by
  have h₁ : A p.1 (fun _ ↦ (0 : ℂ)) = 0 := (A p.1).map_coord_zero 0 rfl
  have h₂ : extDeriv A p.1 ![(0 : ℂ), 0] = 0 :=
    (extDeriv A p.1).map_eq_zero_of_eq _ (i := 0) (j := 1) rfl (by decide)
  rw [normalModelForm_apply hA]
  simp [h₁, h₂]

/-- **Quantitative taming on a disc bundle.** At `p = (z, w)` with `|w| ≤ R`, suppose
`|ν(z)| + |μ(z)| ≤ m`, `‖A(z)‖ ≤ a` and `‖dA(z)‖ ≤ b`. If
`K ≥ R² (3 (m + a)² + b) + δ`, then for every tangent vector `X = (ξ, η)`

`δ |ξ|² + |η|² / 2 ≤ Ω(X, J_N X)`.

The constants depend only on bounds for the coefficients of the normal operator, the connection
and its curvature, so a single `K` serves a whole disc bundle over a region where these bounds
hold. -/
theorem le_normalModelForm_apply_normalModelStructure {p : ℂ × ℂ}
    (hA : DifferentiableAt ℝ A p.1) {m a b R δ : ℝ} (hm : ‖ν p.1‖ + ‖μ p.1‖ ≤ m)
    (ha : ‖A p.1‖ ≤ a) (hb : ‖extDeriv A p.1‖ ≤ b) (hR : ‖p.2‖ ≤ R)
    (hK : R ^ 2 * (3 * (m + a) ^ 2 + b) + δ ≤ K) (X : ℂ × ℂ) :
    δ * ‖X.1‖ ^ 2 + ‖X.2‖ ^ 2 / 2 ≤ normalModelForm K A p ![X, normalModelStructure ν μ p X] := by
  set c := ν p.1 * p.2 + μ p.1 * conj p.2
  set x := ‖X.1‖
  set y := ‖X.2‖
  set r := ‖p.2‖
  have hx : 0 ≤ x := norm_nonneg _
  have hy : 0 ≤ y := norm_nonneg _
  have hr : 0 ≤ r := norm_nonneg _
  have hm₀ : 0 ≤ m := (add_nonneg (norm_nonneg _) (norm_nonneg _)).trans hm
  have ha₀ : 0 ≤ a := (norm_nonneg _).trans ha
  have hb₀ : 0 ≤ b := (norm_nonneg _).trans hb
  have hc : ‖c‖ ≤ m * r := by
    calc ‖c‖ ≤ ‖ν p.1‖ * r + ‖μ p.1‖ * r := by
          refine (norm_add_le _ _).trans ?_
          simp [r]
      _ = (‖ν p.1‖ + ‖μ p.1‖) * r := by ring
      _ ≤ m * r := mul_le_mul_of_nonneg_right hm hr
  set C := ‖c‖
  have hC : 0 ≤ C := norm_nonneg _
  -- the five terms of `Ω(X, J_N X)` and their bounds
  have hJ : normalModelStructure ν μ p X = (I * X.1, I * X.2 + 2 * I * c * conj X.1) :=
    normalModelStructure_apply ν μ p X
  have h₀ : stdComplexSymplecticForm X.1 (I * X.1) = x ^ 2 := by
    simpa [AlmostComplexStructure.ofComplexModule_apply, Complex.normSq_eq_norm_sq] using
      stdComplexSymplecticForm_apply_ofComplexModule X.1
  have h₁ : stdComplexSymplecticForm X.2 (I * X.2 + 2 * I * c * conj X.1) =
      y ^ 2 + stdComplexSymplecticForm X.2 (2 * I * c * conj X.1) := by
    simp [stdComplexSymplecticForm_apply, y, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    ring
  have hn₁ : ‖2 * I * c * conj X.1‖ = 2 * C * x := by simp [C, x]
  have b₁ : |stdComplexSymplecticForm X.2 (2 * I * c * conj X.1)| ≤ y * (2 * C * x) :=
    hn₁ ▸ SymplecticForm.abs_apply_le_norm_mul_norm (J := AlmostComplexStructure.ofComplexModule ℂ)
      (fun v w ↦ by
        simp [stdComplexSymplecticForm_apply, AlmostComplexStructure.ofComplexModule_apply,
          Complex.inner]
        ring) _ _
  have hA₁ (ζ : ℂ) : |A p.1 (fun _ ↦ ζ)| ≤ a * ‖ζ‖ := by
    have h : |A p.1 (fun _ ↦ ζ)| ≤ ‖A p.1‖ * ‖ζ‖ := by
      simpa using (A p.1).le_opNorm (fun _ ↦ ζ)
    exact h.trans (mul_le_mul_of_nonneg_right ha (norm_nonneg ζ))
  have b₂ : |⟪p.2, X.2⟫_ℝ * A p.1 (fun _ ↦ I * X.1)| ≤ r * y * (a * x) := by
    rw [abs_mul]
    refine mul_le_mul (abs_real_inner_le_norm _ _) ?_ (abs_nonneg _) (by positivity)
    simpa [x] using hA₁ (I * X.1)
  have hn₃ : ‖I * X.2 + 2 * I * c * conj X.1‖ ≤ y + 2 * C * x :=
    (norm_add_le _ _).trans (by rw [hn₁]; simp [y])
  have b₃ : |⟪p.2, I * X.2 + 2 * I * c * conj X.1⟫_ℝ * A p.1 (fun _ ↦ X.1)| ≤
      r * (y + 2 * C * x) * (a * x) := by
    rw [abs_mul]
    refine mul_le_mul ((abs_real_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_left hn₃ hr)) ?_ (abs_nonneg _) (by positivity)
    exact hA₁ X.1
  have b₄ : |extDeriv A p.1 ![X.1, I * X.1]| ≤ b * x ^ 2 := by
    have h : |extDeriv A p.1 ![X.1, I * X.1]| ≤ ‖extDeriv A p.1‖ * (‖X.1‖ * ‖I * X.1‖) := by
      simpa [Fin.prod_univ_two] using (extDeriv A p.1).le_opNorm ![X.1, I * X.1]
    refine h.trans ?_
    simpa [x, sq] using mul_le_mul_of_nonneg_right hb (mul_nonneg hx hx)
  rw [normalModelForm_apply hA, hJ, h₀, h₁]
  -- the algebraic estimate, with the products of norms treated as atoms
  have hCr : C ≤ m * R := hc.trans (mul_le_mul_of_nonneg_left hR hm₀)
  have k₁ : C * y * x ≤ m * R * y * x :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCr hy) hx
  have k₂ : r * y * x ≤ R * y * x :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hR hy) hx
  have k₃ : r * C * x ^ 2 ≤ R * (m * R) * x ^ 2 :=
    mul_le_mul_of_nonneg_right (mul_le_mul hR hCr hC (hr.trans hR)) (sq_nonneg x)
  have k₄ : r ^ 2 * (b * x ^ 2) ≤ R ^ 2 * (b * x ^ 2) :=
    mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hr hR 2) (by positivity)
  have k₅ : 0 ≤ (y - 2 * R * (m + a) * x) ^ 2 := sq_nonneg _
  have k₆ : (2 * R ^ 2 * (m + a) ^ 2 + 2 * R ^ 2 * a * m + R ^ 2 * b + δ) * x ^ 2 ≤
      K * x ^ 2 := by
    refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg x)
    have : 2 * a * m ≤ (m + a) ^ 2 := by nlinarith [sq_nonneg (m - a)]
    nlinarith [sq_nonneg R, mul_nonneg (sq_nonneg R) hb₀]
  have k₇ : 0 ≤ R ^ 2 * (b * x ^ 2) := by positivity
  have k₈ : 0 ≤ a * (R * y * x - r * y * x) := mul_nonneg ha₀ (by linarith)
  have k₉ : 0 ≤ a * (R * (m * R) * x ^ 2 - r * C * x ^ 2) := mul_nonneg ha₀ (by linarith)
  have e₁ := (abs_le.1 b₁).1
  have e₂ := (abs_le.1 b₂).1
  have e₃ := (abs_le.1 b₃).2
  have e₄ : -(r ^ 2 / 2 * (b * x ^ 2)) ≤ r ^ 2 / 2 * extDeriv A p.1 ![X.1, I * X.1] := by
    have := mul_le_mul_of_nonneg_left (abs_le.1 b₄).1 (by positivity : (0 : ℝ) ≤ r ^ 2 / 2)
    linarith
  linarith

/-- **The taming form tames `J_N` on every bounded disc bundle.** Over a compact set `S` of the
base on which `ν` and `μ` are continuous, for a connection `A` that is `C¹` at every point of
`S`, and every radius `R`, there
is `K₀` such that for all `K ≥ K₀` the form `Ω_K` tames `J_N` at every point `(z, w)` with
`z ∈ S` and `|w| ≤ R`. -/
theorem exists_forall_normalModelForm_apply_normalModelStructure_pos {S : Set ℂ} (hS : IsCompact S)
    (hν : ContinuousOn ν S) (hμ : ContinuousOn μ S) (hA : ∀ z ∈ S, ContDiffAt ℝ 1 A z) (R : ℝ) :
    ∃ K₀, ∀ K ≥ K₀, ∀ p : ℂ × ℂ, p.1 ∈ S → ‖p.2‖ ≤ R → ∀ X : ℂ × ℂ, X ≠ 0 →
      0 < normalModelForm K A p ![X, normalModelStructure ν μ p X] := by
  obtain ⟨m, hm⟩ := hS.exists_bound_of_continuousOn
    (f := fun z ↦ ‖ν z‖ + ‖μ z‖) (hν.norm.add hμ.norm)
  obtain ⟨a, ha⟩ := hS.exists_bound_of_continuousOn
    fun z hz ↦ (hA z hz).continuousAt.continuousWithinAt
  obtain ⟨b, hb⟩ := hS.exists_bound_of_continuousOn
    fun z hz ↦ (contDiffAt_extDeriv (r := 0) (hA z hz) (by simp)).continuousAt.continuousWithinAt
  refine ⟨R ^ 2 * (3 * (m + a) ^ 2 + b) + 1, fun K hK p hp hpR X hX ↦ ?_⟩
  have hA' : DifferentiableAt ℝ A p.1 := (hA p.1 hp).differentiableAt one_ne_zero
  have hle := le_normalModelForm_apply_normalModelStructure (ν := ν) (μ := μ) hA'
    ((le_abs_self _).trans (hm p.1 hp)) (ha p.1 hp) (hb p.1 hp) hpR hK X
  refine lt_of_lt_of_le ?_ hle
  rcases X with ⟨ξ, η⟩
  by_cases hξ : ξ = 0
  · have hη : 0 < ‖η‖ := norm_pos_iff.2 (by rintro rfl; exact hX (by simp [hξ]))
    positivity
  · positivity

end TauCeti
