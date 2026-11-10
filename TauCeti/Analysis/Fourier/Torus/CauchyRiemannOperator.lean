/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Algebra.SmoothFunctions
public import TauCeti.Analysis.Fourier.Torus.ConjWirtinger
public import TauCeti.Geometry.Manifold.VectorBundle.CauchyRiemann.Connection
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Trivial
public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.AddCircle
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Composition
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.Topology.Instances.AddCircle.UnitAddTorus

/-!
# The Cauchy-Riemann operator on the trivial line bundle over the square torus

The square torus `ℂ / (ℤ + iℤ)` is the product `ℝ / ℤ × ℝ / ℤ` of two circles, with its standard
almost complex structure `TauCeti.SmoothAlmostComplexStructure.addCircleProd 1 1`, which sends the
direction `∂_s` of the first circle to the direction `∂_t` of the second. Complex valued functions
on it are the sections of the trivial line bundle, and their `∂bar`, the `(0,1)`-part
`(dσ)^{0,1}` of the canonical connection of the trivial bundle, is a complex linear real
Cauchy-Riemann operator.

At each point a `(0,1)`-form `η` with values in `ℂ` is determined by its value on `∂_s`: it is
`η (∂_s) dzbar`, where `dzbar (a ∂_s + b ∂_t) = a - i b`. Under this identification, `∂bar` is the
Cauchy-Riemann operator `UnitAddTorus.conjWirtingerDeriv = (∂_s + i ∂_t) / 2` on functions on
`UnitAddTorus (Fin 2)`, whose kernel and cokernel are computed by Fourier series. Hence, on smooth
sections of the trivial line bundle:

* the kernel of `∂bar` consists of the constant sections, of real dimension `2`;
* a smooth `(0,1)`-form `g dzbar` is `∂bar` of a smooth section exactly when `g` has mean zero, so
  the cokernel is spanned by the classes of the antiholomorphic forms `c dzbar`, of real
  dimension `2`;
* the index of `∂bar` is `0 = 1 · χ(T²) + 2 · 0`.

## Main definitions

* `TauCeti.UnitAddTorus.cauchyRiemannOperator`: the operator `σ ↦ (dσ)^{0,1}` on complex valued
  functions on `AddCircle 1 × AddCircle 1`.
* `TauCeti.UnitAddTorus.dzbar`: the `(0,1)`-form `dzbar` of the square torus.
* `TauCeti.UnitAddTorus.contMDiffMapEquiv`: smooth functions on `AddCircle 1 × AddCircle 1` are the
  smooth functions on `UnitAddTorus (Fin 2)`.
* `TauCeti.UnitAddTorus.cauchyRiemannOperatorₗ`: `∂bar` on smooth sections, with its values read
  through `η ↦ η (∂_s)`, as a real linear map.

## Main results

* `TauCeti.UnitAddTorus.isRealCauchyRiemannOperator_cauchyRiemannOperator` and
  `TauCeti.UnitAddTorus.isComplexLinearOperator_cauchyRiemannOperator`: `∂bar` is a complex linear
  real Cauchy-Riemann operator on the trivial line bundle.
* `TauCeti.UnitAddTorus.isZeroOneForm_iff_eq_smul_dzbar`: a `(0,1)`-form is `η (∂_s) dzbar`.
* `TauCeti.UnitAddTorus.cauchyRiemannOperator_eq_smul_dzbar`: `∂bar σ` is the conjugate Wirtinger
  derivative of `σ` on `UnitAddTorus (Fin 2)` times `dzbar`.
* `TauCeti.UnitAddTorus.cauchyRiemannOperator_eq_zero_iff`: a smooth section is in the kernel of
  `∂bar` if and only if it is constant.
* `TauCeti.UnitAddTorus.exists_cauchyRiemannOperator_eq_smul_dzbar_iff`: a smooth form `g dzbar` is
  `∂bar` of a smooth section if and only if `g` has mean zero.
* `TauCeti.UnitAddTorus.finrank_ker_cauchyRiemannOperatorₗ`,
  `TauCeti.UnitAddTorus.finrank_cokernel_cauchyRiemannOperatorₗ` and
  `TauCeti.UnitAddTorus.finrank_ker_sub_finrank_cokernel_cauchyRiemannOperatorₗ`: kernel and
  cokernel have real dimension `2`, and the index is `0`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  American Mathematical Society Colloquium Publications 52, 2012, Appendix C.1 (real
  Cauchy-Riemann operators and the Riemann-Roch theorem on a closed Riemann surface).
-/

public section

noncomputable section

open Bundle Complex ComplexConjugate
open scoped ContDiff Manifold

namespace TauCeti.UnitAddTorus

open SmoothAlmostComplexStructure

/-! ### The operator and its Cauchy-Riemann property -/

/-- The Cauchy-Riemann operator `∂bar σ = (dσ)^{0,1}` on complex valued functions on the square
torus `AddCircle 1 × AddCircle 1`, the sections of its trivial line bundle: the `(0,1)`-part, for
the standard almost complex structure, of the canonical connection of the trivial bundle. It sends
`v` to `½ (dσ (v) + i dσ (j v))` (`TauCeti.UnitAddTorus.cauchyRiemannOperator_apply`). -/
def cauchyRiemannOperator (σ : UnitAddCircle × UnitAddCircle → ℂ)
    (x : UnitAddCircle × UnitAddCircle) : TangentSpace (𝓘(ℝ).prod 𝓘(ℝ)) x →L[ℝ] ℂ :=
  (addCircleProd 1 1).zeroOnePart (V := Bundle.Trivial _ ℂ)
    (CovariantDerivative.trivial (I := 𝓘(ℝ).prod 𝓘(ℝ)) ℂ σ x)

theorem cauchyRiemannOperator_apply (σ : UnitAddCircle × UnitAddCircle → ℂ)
    (x : UnitAddCircle × UnitAddCircle) (v : TangentSpace (𝓘(ℝ).prod 𝓘(ℝ)) x) :
    cauchyRiemannOperator σ x v =
      (2⁻¹ : ℝ) • (mvfderiv (𝓘(ℝ).prod 𝓘(ℝ)) σ x v +
        I • mvfderiv (𝓘(ℝ).prod 𝓘(ℝ)) σ x ((-v.2, v.1) : ℝ × ℝ)) := by
  rw [cauchyRiemannOperator, zeroOnePart_apply, addCircleProd_apply,
    CovariantDerivative.trivial_apply]

/-- `∂bar` is a real Cauchy-Riemann operator on the trivial line bundle of the square torus. -/
theorem isRealCauchyRiemannOperator_cauchyRiemannOperator :
    IsRealCauchyRiemannOperator ℂ (addCircleProd 1 1)
      (V := Bundle.Trivial (UnitAddCircle × UnitAddCircle) ℂ) cauchyRiemannOperator :=
  (CovariantDerivative.trivial (I := 𝓘(ℝ).prod 𝓘(ℝ)) (M := UnitAddCircle × UnitAddCircle)
    ℂ).isCovariantDerivativeOnUniv.isRealCauchyRiemannOperator_zeroOnePart _

/-- `∂bar` is a complex linear real Cauchy-Riemann operator on the trivial line bundle of the
square torus. -/
theorem isComplexLinearOperator_cauchyRiemannOperator :
    IsComplexLinearOperator ℂ (V := Bundle.Trivial (UnitAddCircle × UnitAddCircle) ℂ)
      cauchyRiemannOperator := by
  refine (CovariantDerivative.trivial (I := 𝓘(ℝ).prod 𝓘(ℝ))
    (M := UnitAddCircle × UnitAddCircle) ℂ).isCovariantDerivativeOnUniv
    |>.isComplexLinearOperator_zeroOnePart _ fun σ x hσ ↦ ?_
  simp only [mdifferentiableAt_section, Trivial.fiberBundle_trivializationAt',
    Trivial.trivialization_apply] at hσ
  simp only [CovariantDerivative.trivial_apply]
  exact mvfderiv_const_smul hσ I

/-! ### `(0,1)`-forms on the square torus -/

/-- The real linear form `(a, b) ↦ a - i b` on `ℝ × ℝ`. -/
private def dzbarAux : ℝ × ℝ →L[ℝ] ℂ :=
  conjCLE.toContinuousLinearMap ∘L equivRealProdCLM.symm.toContinuousLinearMap

private theorem dzbarAux_apply (v : ℝ × ℝ) : dzbarAux v = v.1 - v.2 * I := by
  change conj (equivRealProdCLM.symm v) = _
  rw [equivRealProdCLM_symm_apply, map_add, map_mul, conj_ofReal, conj_ofReal, conj_I, mul_neg,
    sub_eq_add_neg]

/-- A real linear form `η` on `ℝ × ℝ` with `η (-b, a) = -i η (a, b)` is `η (1, 0)` times
`(a, b) ↦ a - i b`. -/
private theorem forall_neg_snd_fst_iff (η : ℝ × ℝ →L[ℝ] ℂ) :
    (∀ v : ℝ × ℝ, η (-v.2, v.1) = -(I • η v)) ↔ η = η (1, 0) • dzbarAux := by
  constructor
  · intro h
    -- `η (∂_t) = η (j ∂_s) = -i η (∂_s)`, and `η` is determined by its values on `∂_s` and `∂_t`.
    have ht : η (0, 1) = -(I * η (1, 0)) := by simpa using h (1, 0)
    refine ContinuousLinearMap.ext fun v ↦ ?_
    have hv : v = v.1 • ((1, 0) : ℝ × ℝ) + v.2 • ((0, 1) : ℝ × ℝ) := by ext <;> simp
    rw [smul_apply, dzbarAux_apply, hv, map_add, map_smul, map_smul, ht]
    simp only [real_smul, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul,
      mul_one, mul_zero, add_zero, zero_add]
    ring_nf
  · intro h v
    rw [h, smul_apply, smul_apply, dzbarAux_apply,
      dzbarAux_apply, smul_eq_mul, smul_eq_mul, smul_eq_mul]
    ring_nf
    rw [I_sq]
    push_cast
    ring

/-- The `(0,1)`-form `dzbar` of the square torus at `x`: `a ∂_s + b ∂_t ↦ a - i b`, the conjugate
of the complex coordinate `z = s + i t`. -/
def dzbar (x : UnitAddCircle × UnitAddCircle) : TangentSpace (𝓘(ℝ).prod 𝓘(ℝ)) x →L[ℝ] ℂ :=
  dzbarAux

theorem dzbar_apply (x : UnitAddCircle × UnitAddCircle) (v : ℝ × ℝ) :
    dzbar x v = v.1 - v.2 * I :=
  dzbarAux_apply v

/-- **The `(0,1)`-forms of the square torus.** A `ℂ`-valued real linear form `η` at `x` is a
`(0,1)`-form exactly when it is `η (∂_s) dzbar`. So `η ↦ η (∂_s)` identifies the `(0,1)`-forms at
`x` with `ℂ`, with inverse `c ↦ c dzbar` (`TauCeti.UnitAddTorus.isZeroOneForm_smul_dzbar`,
`TauCeti.UnitAddTorus.smul_dzbar_apply_fst`). -/
theorem isZeroOneForm_iff_eq_smul_dzbar {x : UnitAddCircle × UnitAddCircle}
    (η : TangentSpace (𝓘(ℝ).prod 𝓘(ℝ)) x →L[ℝ] ℂ) :
    (addCircleProd 1 1).IsZeroOneForm (V := Bundle.Trivial _ ℂ) η ↔
      η = η ((1, 0) : ℝ × ℝ) • dzbar x := by
  rw [isZeroOneForm_iff]
  simp only [addCircleProd_apply]
  exact forall_neg_snd_fst_iff η

/-- The value of `c dzbar` on `∂_s` is `c`. -/
theorem smul_dzbar_apply_fst (x : UnitAddCircle × UnitAddCircle) (c : ℂ) :
    (c • dzbar x) ((1, 0) : ℝ × ℝ) = c := by
  change c * dzbarAux (1, 0) = c
  simp [dzbarAux_apply]

/-- Every multiple `c dzbar` is a `(0,1)`-form. -/
theorem isZeroOneForm_smul_dzbar (x : UnitAddCircle × UnitAddCircle) (c : ℂ) :
    (addCircleProd 1 1).IsZeroOneForm (V := Bundle.Trivial _ ℂ) (c • dzbar x) := by
  rw [isZeroOneForm_iff_eq_smul_dzbar, smul_dzbar_apply_fst]

/-! ### The operator in the coordinates of `UnitAddTorus (Fin 2)` -/

/-- The identification `UnitAddTorus (Fin 2) ≃ AddCircle 1 × AddCircle 1`, `y ↦ (y 0, y 1)`. -/
abbrev prodEquiv : UnitAddTorus (Fin 2) ≃ UnitAddCircle × UnitAddCircle :=
  piFinTwoEquiv fun _ ↦ UnitAddCircle

/-- The quotient map `ℝ × ℝ → AddCircle 1 × AddCircle 1`. -/
private abbrev quotientMap : ℝ × ℝ → UnitAddCircle × UnitAddCircle :=
  Prod.map ((↑) : ℝ → UnitAddCircle) ((↑) : ℝ → UnitAddCircle)

/-- The coordinates `ℝ × ℝ` of the plane covering the torus are those of `Fin 2 → ℝ`. -/
private abbrev coordEquiv : (Fin 2 → ℝ) ≃L[ℝ] ℝ × ℝ :=
  ContinuousLinearEquiv.piFinTwo ℝ fun _ ↦ ℝ

/-- The lift to `Fin 2 → ℝ` of `σ ∘ prodEquiv` is the lift `σ ∘ quotientMap` to `ℝ × ℝ`, read
through `coordEquiv`. -/
private theorem lift_eq (σ : UnitAddCircle × UnitAddCircle → ℂ) :
    (fun y : Fin 2 → ℝ ↦ (σ ∘ prodEquiv) fun i ↦ (y i : UnitAddCircle)) =
      (σ ∘ quotientMap) ∘ coordEquiv :=
  rfl

/-- Smooth functions on `AddCircle 1 × AddCircle 1` are the smooth functions on
`UnitAddTorus (Fin 2)`. -/
theorem contMDiff_iff_comp_prodEquiv_mem_smoothFunctions {σ : UnitAddCircle × UnitAddCircle → ℂ} :
    ContMDiff (𝓘(ℝ).prod 𝓘(ℝ)) 𝓘(ℝ, ℂ) ∞ σ ↔ σ ∘ prodEquiv ∈ smoothFunctions (Fin 2) := by
  rw [mem_smoothFunctions, lift_eq, coordEquiv.contDiff_comp_iff, ← contMDiff_iff_contDiff,
    (AddCircle.isLocalDiffeomorph_prodMap_coe 1 1 ∞).contMDiff_comp_iff
      (AddCircle.prodMap_coe_surjective 1 1) le_rfl]

/-- At the image of `z`, the differential of `σ` is the derivative of its lift `σ ∘ quotientMap`. -/
private theorem mvfderiv_apply_eq_fderiv {σ : UnitAddCircle × UnitAddCircle → ℂ} {z : ℝ × ℝ}
    (hσ : MDifferentiableAt (𝓘(ℝ).prod 𝓘(ℝ)) 𝓘(ℝ, ℂ) σ (quotientMap z)) (v : ℝ × ℝ) :
    mvfderiv (𝓘(ℝ).prod 𝓘(ℝ)) σ (quotientMap z) v = fderiv ℝ (σ ∘ quotientMap) z v := by
  have hπ := (AddCircle.hasMFDerivAt_prodMap_coe 1 1 z)
  have h := mvfderiv_comp_apply z hσ hπ.mdifferentiableAt v
  rw [hπ.mfderiv, mvfderiv_eq_fderiv] at h
  exact h.symm

/-- **`∂bar` on the torus is the conjugate Wirtinger derivative.** For a smooth `σ`, `∂bar σ` at `x`
is `UnitAddTorus.conjWirtingerDeriv (σ ∘ prodEquiv)` at `x` times `dzbar`: under the identification
`η ↦ η (∂_s)` of `(0,1)`-forms with `ℂ`, the bundle operator is the operator `(∂_s + i ∂_t) / 2` on
functions on `UnitAddTorus (Fin 2)`. -/
theorem cauchyRiemannOperator_eq_smul_dzbar {σ : UnitAddCircle × UnitAddCircle → ℂ}
    (hσ : ContMDiff (𝓘(ℝ).prod 𝓘(ℝ)) 𝓘(ℝ, ℂ) ∞ σ) (x : UnitAddCircle × UnitAddCircle) :
    cauchyRiemannOperator σ x =
      _root_.UnitAddTorus.conjWirtingerDeriv (σ ∘ prodEquiv) (prodEquiv.symm x) • dzbar x := by
  obtain ⟨⟨a, b⟩, rfl⟩ := AddCircle.prodMap_coe_surjective 1 1 x
  have hσx := hσ.mdifferentiableAt (x := quotientMap (a, b)) (by simp)
  refine ((isZeroOneForm_iff_eq_smul_dzbar _).1
    (isZeroOneForm_zeroOnePart (V := Bundle.Trivial _ ℂ) (j := addCircleProd 1 1)
      (CovariantDerivative.trivial (I := 𝓘(ℝ).prod 𝓘(ℝ)) ℂ σ (quotientMap (a, b))))).trans
    (congrArg (· • dzbar _) ?_)
  -- The point `([a], [b])` is the image of `a + i b`, and the lift of `σ ∘ prodEquiv` to `ℂ` is the
  -- lift `σ ∘ quotientMap` to `ℝ × ℝ`, read through `ℂ ≃ ℝ × ℝ`.
  have hx : prodEquiv.symm (quotientMap (a, b)) =
      fun i ↦ ((![(⟨a, b⟩ : ℂ).re, (⟨a, b⟩ : ℂ).im] i : ℝ) : UnitAddCircle) := by
    funext i
    fin_cases i <;> rfl
  have hg : (fun w : ℂ ↦ (σ ∘ prodEquiv) fun i ↦ ((![w.re, w.im] i : ℝ) : UnitAddCircle)) =
      (σ ∘ quotientMap) ∘ equivRealProdCLM :=
    rfl
  change cauchyRiemannOperator σ (quotientMap (a, b)) ((1, 0) : ℝ × ℝ) = _
  rw [cauchyRiemannOperator_apply σ _ ((1, 0) : ℝ × ℝ), mvfderiv_apply_eq_fderiv hσx,
    mvfderiv_apply_eq_fderiv hσx, hx, _root_.UnitAddTorus.conjWirtingerDeriv_coe
      (contMDiff_iff_comp_prodEquiv_mem_smoothFunctions.1 hσ), hg, conjWirtingerDeriv_apply,
    equivRealProdCLM.comp_right_fderiv]
  simp [Complex.real_smul, mul_add]

/-! ### Kernel and range on smooth sections -/

/-- A form `c dzbar` determines `c`. -/
theorem smul_dzbar_injective (x : UnitAddCircle × UnitAddCircle) :
    Function.Injective fun c : ℂ ↦ c • dzbar x := fun c c' h ↦ by
  rw [← smul_dzbar_apply_fst x c, ← smul_dzbar_apply_fst x c']
  exact congrArg (fun η : TangentSpace (𝓘(ℝ).prod 𝓘(ℝ)) x →L[ℝ] ℂ ↦ η ((1, 0) : ℝ × ℝ)) h

/-- **The kernel of `∂bar`.** A smooth section of the trivial line bundle of the square torus is in
the kernel of `∂bar` if and only if it is constant. -/
theorem cauchyRiemannOperator_eq_zero_iff {σ : UnitAddCircle × UnitAddCircle → ℂ}
    (hσ : ContMDiff (𝓘(ℝ).prod 𝓘(ℝ)) 𝓘(ℝ, ℂ) ∞ σ) :
    cauchyRiemannOperator σ = 0 ↔ ∃ c : ℂ, σ = fun _ ↦ c := by
  have hf := contMDiff_iff_comp_prodEquiv_mem_smoothFunctions.1 hσ
  have h : cauchyRiemannOperator σ = 0 ↔
      _root_.UnitAddTorus.conjWirtingerDeriv (σ ∘ prodEquiv) = 0 := by
    constructor
    · intro h
      funext y
      have hy := congrFun h (prodEquiv y)
      rw [cauchyRiemannOperator_eq_smul_dzbar hσ, Equiv.symm_apply_apply, Pi.zero_apply,
        ← zero_smul ℂ (dzbar _)] at hy
      exact smul_dzbar_injective _ hy
    · intro h
      funext x
      rw [cauchyRiemannOperator_eq_smul_dzbar hσ, h, Pi.zero_apply, Pi.zero_apply]
      exact zero_smul ℂ (dzbar x)
  rw [h, _root_.UnitAddTorus.conjWirtingerDeriv_eq_zero_iff hf]
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c, funext fun x ↦ ?_⟩
    simpa using congrFun hc (prodEquiv.symm x)
  · rintro ⟨c, rfl⟩
    exact ⟨c, rfl⟩

/-- **The range of `∂bar`.** A smooth `(0,1)`-form `g dzbar` on the square torus is `∂bar σ` for a
smooth section `σ` if and only if `g` has mean zero. So the cokernel of `∂bar` is spanned by the
classes of the antiholomorphic forms `c dzbar`, of which only `0` is in the range. -/
theorem exists_cauchyRiemannOperator_eq_smul_dzbar_iff {g : UnitAddCircle × UnitAddCircle → ℂ}
    (hg : ContMDiff (𝓘(ℝ).prod 𝓘(ℝ)) 𝓘(ℝ, ℂ) ∞ g) :
    (∃ σ, ContMDiff (𝓘(ℝ).prod 𝓘(ℝ)) 𝓘(ℝ, ℂ) ∞ σ ∧
        ∀ x, cauchyRiemannOperator σ x = g x • dzbar x) ↔
      _root_.UnitAddTorus.mFourierCoeff (g ∘ prodEquiv) 0 = 0 := by
  rw [← _root_.UnitAddTorus.exists_conjWirtingerDeriv_eq_iff
    (contMDiff_iff_comp_prodEquiv_mem_smoothFunctions.1 hg)]
  constructor
  · rintro ⟨σ, hσ, h⟩
    refine ⟨σ ∘ prodEquiv, contMDiff_iff_comp_prodEquiv_mem_smoothFunctions.1 hσ,
      funext fun y ↦ smul_dzbar_injective (prodEquiv y) ?_⟩
    have hy := h (prodEquiv y)
    rwa [cauchyRiemannOperator_eq_smul_dzbar hσ, Equiv.symm_apply_apply] at hy
  · rintro ⟨f, hf, hfg⟩
    have hσ : ContMDiff (𝓘(ℝ).prod 𝓘(ℝ)) 𝓘(ℝ, ℂ) ∞ (f ∘ prodEquiv.symm) := by
      rwa [contMDiff_iff_comp_prodEquiv_mem_smoothFunctions, Function.comp_assoc,
        Equiv.symm_comp_self, Function.comp_id]
    refine ⟨f ∘ prodEquiv.symm, hσ, fun x ↦ ?_⟩
    rw [cauchyRiemannOperator_eq_smul_dzbar hσ, Function.comp_assoc, Equiv.symm_comp_self,
      Function.comp_id, hfg, Function.comp_apply, Equiv.apply_symm_apply]

/-! ### Dimensions and the index -/

/-- Smooth functions on `AddCircle 1 × AddCircle 1` are the smooth functions on
`UnitAddTorus (Fin 2)`, through `prodEquiv`. -/
def contMDiffMapEquiv :
    C^∞⟮𝓘(ℝ).prod 𝓘(ℝ), UnitAddCircle × UnitAddCircle; 𝓘(ℝ, ℂ), ℂ⟯ ≃ₗ[ℝ]
      smoothFunctions (Fin 2) where
  toFun σ := ⟨σ ∘ prodEquiv, contMDiff_iff_comp_prodEquiv_mem_smoothFunctions.1 σ.contMDiff⟩
  invFun f := ⟨f ∘ prodEquiv.symm, contMDiff_iff_comp_prodEquiv_mem_smoothFunctions.2 (by
    rw [Function.comp_assoc, Equiv.symm_comp_self, Function.comp_id]
    exact f.2)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv σ := by
    ext x
    simp
  right_inv f := Subtype.ext <| by
    change (f : UnitAddTorus (Fin 2) → ℂ) ∘ prodEquiv.symm ∘ prodEquiv = f
    rw [Equiv.symm_comp_self, Function.comp_id]

@[simp]
theorem coe_contMDiffMapEquiv_apply
    (σ : C^∞⟮𝓘(ℝ).prod 𝓘(ℝ), UnitAddCircle × UnitAddCircle; 𝓘(ℝ, ℂ), ℂ⟯) :
    (contMDiffMapEquiv σ : UnitAddTorus (Fin 2) → ℂ) = σ ∘ prodEquiv :=
  (rfl)

/-- `∂bar` on smooth sections of the trivial line bundle of the square torus, with its values
read through the identification `η ↦ η (∂_s)` of `(0,1)`-forms with `ℂ`
(`TauCeti.UnitAddTorus.cauchyRiemannOperator_eq_cauchyRiemannOperatorₗ_smul_dzbar`), as a real
linear map. -/
def cauchyRiemannOperatorₗ :
    C^∞⟮𝓘(ℝ).prod 𝓘(ℝ), UnitAddCircle × UnitAddCircle; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℝ]
      C^∞⟮𝓘(ℝ).prod 𝓘(ℝ), UnitAddCircle × UnitAddCircle; 𝓘(ℝ, ℂ), ℂ⟯ :=
  contMDiffMapEquiv.symm.toLinearMap ∘ₗ conjWirtingerDerivₗ.restrictScalars ℝ ∘ₗ
    contMDiffMapEquiv.toLinearMap

/-- `cauchyRiemannOperatorₗ σ` is the conjugate Wirtinger derivative of `σ ∘ prodEquiv`. -/
theorem cauchyRiemannOperatorₗ_apply
    (σ : C^∞⟮𝓘(ℝ).prod 𝓘(ℝ), UnitAddCircle × UnitAddCircle; 𝓘(ℝ, ℂ), ℂ⟯)
    (x : UnitAddCircle × UnitAddCircle) :
    cauchyRiemannOperatorₗ σ x =
      _root_.UnitAddTorus.conjWirtingerDeriv (σ ∘ prodEquiv) (prodEquiv.symm x) := by
  change (conjWirtingerDerivₗ (contMDiffMapEquiv σ) : UnitAddTorus (Fin 2) → ℂ)
    (prodEquiv.symm x) = _
  rw [coe_conjWirtingerDerivₗ_apply, coe_contMDiffMapEquiv_apply]

/-- `∂bar σ` is `cauchyRiemannOperatorₗ σ` times `dzbar`. -/
theorem cauchyRiemannOperator_eq_cauchyRiemannOperatorₗ_smul_dzbar
    (σ : C^∞⟮𝓘(ℝ).prod 𝓘(ℝ), UnitAddCircle × UnitAddCircle; 𝓘(ℝ, ℂ), ℂ⟯)
    (x : UnitAddCircle × UnitAddCircle) :
    cauchyRiemannOperator σ x = cauchyRiemannOperatorₗ σ x • dzbar x := by
  rw [cauchyRiemannOperator_eq_smul_dzbar σ.contMDiff, cauchyRiemannOperatorₗ_apply]

private theorem map_ker_cauchyRiemannOperatorₗ :
    (LinearMap.ker cauchyRiemannOperatorₗ).map contMDiffMapEquiv.toLinearMap =
      (LinearMap.ker conjWirtingerDerivₗ).restrictScalars ℝ := by
  ext f
  simp [Submodule.map_equiv_eq_comap_symm, cauchyRiemannOperatorₗ]

private theorem map_range_cauchyRiemannOperatorₗ :
    (LinearMap.range cauchyRiemannOperatorₗ).map contMDiffMapEquiv.toLinearMap =
      (LinearMap.range conjWirtingerDerivₗ).restrictScalars ℝ := by
  ext f
  simp only [Submodule.map_equiv_eq_comap_symm, Submodule.mem_comap, LinearMap.mem_range,
    Submodule.restrictScalars_mem, cauchyRiemannOperatorₗ, LinearMap.coe_comp,
    Function.comp_apply, LinearEquiv.coe_coe, LinearMap.coe_restrictScalars]
  constructor
  · rintro ⟨σ, hσ⟩
    exact ⟨contMDiffMapEquiv σ, contMDiffMapEquiv.symm.injective hσ⟩
  · rintro ⟨g, rfl⟩
    exact ⟨contMDiffMapEquiv.symm g, by simp⟩

/-- The kernel of `∂bar` on smooth sections of the trivial line bundle of the square torus, the
constants, has real dimension `2`. -/
theorem finrank_ker_cauchyRiemannOperatorₗ :
    Module.finrank ℝ (LinearMap.ker cauchyRiemannOperatorₗ) = 2 := by
  rw [(contMDiffMapEquiv.ofSubmodules _ _ map_ker_cauchyRiemannOperatorₗ).finrank_eq]
  exact finrank_real_ker_conjWirtingerDerivₗ

/-- The cokernel of `∂bar` on smooth sections of the trivial line bundle of the square torus has
real dimension `2`. -/
theorem finrank_cokernel_cauchyRiemannOperatorₗ :
    Module.finrank ℝ (C^∞⟮𝓘(ℝ).prod 𝓘(ℝ), UnitAddCircle × UnitAddCircle; 𝓘(ℝ, ℂ), ℂ⟯ ⧸
      LinearMap.range cauchyRiemannOperatorₗ) = 2 := by
  rw [(Submodule.Quotient.equiv _ _ contMDiffMapEquiv map_range_cauchyRiemannOperatorₗ).finrank_eq,
    (Submodule.Quotient.restrictScalarsEquiv ℝ _).finrank_eq]
  exact finrank_real_cokernel_conjWirtingerDerivₗ

/-- **The index of `∂bar` on the torus.** On smooth sections of the trivial line bundle of the
square torus, `∂bar` has index `dim ker ∂bar - dim coker ∂bar = 0`, which is
`n χ(T²) + 2 c₁ = 1 · 0 + 2 · 0`. -/
theorem finrank_ker_sub_finrank_cokernel_cauchyRiemannOperatorₗ :
    (Module.finrank ℝ (LinearMap.ker cauchyRiemannOperatorₗ) : ℤ) -
      Module.finrank ℝ (C^∞⟮𝓘(ℝ).prod 𝓘(ℝ), UnitAddCircle × UnitAddCircle; 𝓘(ℝ, ℂ), ℂ⟯ ⧸
        LinearMap.range cauchyRiemannOperatorₗ) = 0 := by
  rw [finrank_ker_cauchyRiemannOperatorₗ, finrank_cokernel_cauchyRiemannOperatorₗ, sub_self]

end TauCeti.UnitAddTorus
