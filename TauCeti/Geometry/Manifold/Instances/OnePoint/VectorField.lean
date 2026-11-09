/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Eval.SMul
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Geometry.Manifold.VectorBundle.MDifferentiable
public import Mathlib.Geometry.Manifold.VectorBundle.Tangent
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.RingTheory.Polynomial.Basic
public import TauCeti.Geometry.Manifold.Instances.OnePoint.Basic

/-!
# Holomorphic vector fields on the Riemann sphere

A vector field on the Riemann sphere `OnePoint ℂ` is a section `X` of its holomorphic tangent
bundle; it is holomorphic when `x ↦ (x, X x)` is a holomorphic map into the tangent bundle. In
Mathlib the tangent space `TangentSpace 𝓘(ℂ, ℂ) x` is `ℂ`, a tangent vector at `x` being read in
the preferred chart at `x`, so a vector field is a function `X : OnePoint ℂ → ℂ`. This
file shows that the holomorphic vector fields are exactly the fields `(a + b z + c z²) ∂_z`: in
the affine chart `X` reads as a polynomial of degree at most `2`, and its value at `∞`, read in the
inverted chart `w = z⁻¹`, is `-c` (`OnePoint.mdifferentiable_tangent_iff`). They form a complex
vector space isomorphic to the polynomials of degree less than `3`
(`OnePoint.holomorphicVectorFieldsEquiv`), of complex dimension `3` and real dimension `6`.

The proof reads `X` in the two charts. In the affine chart it is an entire function `f`. In the
inverted chart the derivative of the transition `z ↦ z⁻¹` is `-z⁻²`, so `X` reads there as
`h w = -w² f(w⁻¹)` for `w ≠ 0`, and `h` is holomorphic at `0`. Hence `f(z) = -z² h(z⁻¹)` is
`O(|z|²)` at infinity, and by Liouville's theorem for functions of polynomial growth `f` is a
polynomial of degree at most `2`. Conversely `-w² (a + b w⁻¹ + c w⁻²) = -(a w² + b w + c)` is
entire.

This is the kernel Check of the Riemann–Roch index formula for `∂bar` on `TS²`: the real index
`n χ + 2 c₁ = 1 · 2 + 2 · 2 = 6` is the real dimension of the holomorphic vector fields, the Lie
algebra of `PSL₂(ℂ)`, while the formula with `c₁` in place of `2 c₁` would give `4`
(`OnePoint.finrank_real_holomorphicVectorFields_eq_index` and
`OnePoint.finrank_real_holomorphicVectorFields_ne`).

## Main declarations

* `OnePoint.polynomialVectorField`: the vector field `p(z) ∂_z` of a polynomial `p`, with value
  `-p.coeff 2` at `∞`.
* `OnePoint.mdifferentiable_tangent_iff`: a vector field is holomorphic exactly when it is
  `p(z) ∂_z` for a polynomial `p` of degree less than `3`.
* `OnePoint.holomorphicVectorFields` and `OnePoint.holomorphicVectorFieldsEquiv`: the space of
  holomorphic vector fields and its isomorphism with `Polynomial.degreeLT ℂ 3`.
* `OnePoint.finrank_holomorphicVectorFields` and `OnePoint.finrank_real_holomorphicVectorFields`:
  complex dimension `3` and real dimension `6`.

## References

* Dusa McDuff and Dietmar Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  AMS Colloquium Publications 52, 2012, Appendix C.1.
* Otto Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81,
  Springer, 1981, §1.5 (c).
-/

public section

open Bornology Bundle Filter Function Polynomial Set Topology

open scoped Manifold

noncomputable section

namespace OnePoint

/-! ### The tangent bundle read in the two charts -/

/-- In the preferred trivialization of the tangent bundle of the Riemann sphere at a finite point,
a tangent vector at a finite point reads as itself: both charts are the affine chart. -/
theorem trivializationAt_coe_apply_coe (z₀ z v : ℂ) :
    (trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ)) (z₀ : OnePoint ℂ) ⟨(z : OnePoint ℂ), v⟩).2 = v := by
  have h : (affineChart : OpenPartialHomeomorph (OnePoint ℂ) ℂ) ∘ affineChart.symm = id :=
    funext fun _ ↦ by simp
  simp [TangentBundle.trivializationAt_apply, h]

/-- In the preferred trivialization of the tangent bundle of the Riemann sphere at `∞`, a tangent
vector at `∞` reads as itself. -/
theorem trivializationAt_infty_apply_infty (v : ℂ) :
    (trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ)) (∞ : OnePoint ℂ) ⟨∞, v⟩).2 = v := by
  have h : (invChart : OpenPartialHomeomorph (OnePoint ℂ) ℂ) ∘ invChart.symm = id :=
    funext fun _ ↦ invChart.right_inv (by simp)
  simp [TangentBundle.trivializationAt_apply, h]

/-- In the preferred trivialization of the tangent bundle of the Riemann sphere at `∞`, a tangent
vector `v` at a nonzero finite point `z` reads as `-z⁻² v`: the derivative of the chart transition
`z ↦ z⁻¹`. -/
theorem trivializationAt_infty_apply_coe {z : ℂ} (hz : z ≠ 0) (v : ℂ) :
    (trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ)) (∞ : OnePoint ℂ) ⟨(z : OnePoint ℂ), v⟩).2 =
      -(z ^ 2)⁻¹ * v := by
  have h : (invChart : OpenPartialHomeomorph (OnePoint ℂ) ℂ) ∘ affineChart.symm = fun w ↦ w⁻¹ :=
    funext fun _ ↦ by simp
  simp [TangentBundle.trivializationAt_apply, h, (hasDerivAt_inv hz).hasFDerivAt.fderiv, mul_comm]

/-- A function on the Riemann sphere is differentiable at a point exactly when it is
differentiable at the corresponding point after composing with the inverse of a chart of the
atlas whose source contains the point. -/
theorem mdifferentiableAt_iff_differentiableAt_comp_symm {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℂ F] {e : OpenPartialHomeomorph (OnePoint ℂ) ℂ} (he : e ∈ atlas ℂ (OnePoint ℂ))
    {x : OnePoint ℂ} (hx : x ∈ e.source) {g : OnePoint ℂ → F} :
    MDifferentiableAt 𝓘(ℂ, ℂ) 𝓘(ℂ, F) g x ↔ DifferentiableAt ℂ (g ∘ e.symm) (e x) := by
  rw [← mdifferentiableAt_iff_differentiableAt]
  refine ⟨fun hg ↦ ?_, fun hg ↦ ?_⟩
  · refine MDifferentiableAt.comp (I' := 𝓘(ℂ, ℂ)) _ ?_
      (mdifferentiableAt_atlas_symm he (e.map_source hx))
    rwa [e.left_inv hx]
  · refine (hg.comp x (mdifferentiableAt_atlas he hx)).congr_of_eventuallyEq ?_
    filter_upwards [e.eventually_left_inverse hx] with y hy
    simp [hy]

/-- A vector field on the Riemann sphere is holomorphic at a finite point `z₀` exactly when its
coefficient in the affine chart is complex differentiable at `z₀`. -/
theorem mdifferentiableAt_tangent_coe_iff (X : OnePoint ℂ → ℂ) (z₀ : ℂ) :
    MDifferentiableAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ).tangent
        (fun x ↦ (⟨x, X x⟩ : TangentBundle 𝓘(ℂ, ℂ) (OnePoint ℂ))) (z₀ : OnePoint ℂ) ↔
      DifferentiableAt ℂ (fun z : ℂ ↦ X z) z₀ := by
  refine (mdifferentiableAt_section (IB := 𝓘(ℂ, ℂ)) (F := ℂ) (E := TangentSpace 𝓘(ℂ, ℂ)) X).trans ?_
  rw [mdifferentiableAt_iff_differentiableAt_comp_symm (e := affineChart) (Or.inl rfl)
      (by simp)]
  refine Iff.of_eq (congrArg₂ _ (funext fun z ↦ ?_) (by simp))
  rw [Function.comp_apply, affineChart_symm_apply]
  exact trivializationAt_coe_apply_coe z₀ z (X z)

/-- The coefficient of a vector field on the Riemann sphere in the inverted chart: at `w ≠ 0` it
is `-w² X(w⁻¹)`, where `z ↦ X z` is the coefficient in the affine chart
(`OnePoint.invChartCoeff_of_ne_zero`), and at `w = 0` it is the value at `∞`
(`OnePoint.invChartCoeff_zero`). -/
def invChartCoeff (X : OnePoint ℂ → ℂ) (w : ℂ) : ℂ :=
  (trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ)) (∞ : OnePoint ℂ)
    ⟨invChart.symm w, X (invChart.symm w)⟩).2

theorem invChartCoeff_zero (X : OnePoint ℂ → ℂ) : invChartCoeff X 0 = X ∞ := by
  rw [invChartCoeff, invChart_symm_zero]
  exact trivializationAt_infty_apply_infty _

theorem invChartCoeff_of_ne_zero (X : OnePoint ℂ → ℂ) {w : ℂ} (hw : w ≠ 0) :
    invChartCoeff X w = -w ^ 2 * X (w⁻¹ : ℂ) := by
  rw [invChartCoeff, invChart_symm_of_ne_zero hw, trivializationAt_infty_apply_coe (inv_ne_zero hw),
    inv_pow, inv_inv]

/-- A vector field on the Riemann sphere is holomorphic at `∞` exactly when its coefficient in the
inverted chart is complex differentiable at `0`. -/
theorem mdifferentiableAt_tangent_infty_iff (X : OnePoint ℂ → ℂ) :
    MDifferentiableAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ).tangent
        (fun x ↦ (⟨x, X x⟩ : TangentBundle 𝓘(ℂ, ℂ) (OnePoint ℂ))) (∞ : OnePoint ℂ) ↔
      DifferentiableAt ℂ (invChartCoeff X) 0 := by
  refine (mdifferentiableAt_section (IB := 𝓘(ℂ, ℂ)) (F := ℂ) (E := TangentSpace 𝓘(ℂ, ℂ)) X).trans ?_
  rw [mdifferentiableAt_iff_differentiableAt_comp_symm (e := invChart) (Or.inr rfl)
      (by simp), invChart_infty]
  rfl

/-! ### Polynomial vector fields -/

/-- The vector field `p(z) ∂_z` on the Riemann sphere attached to a polynomial `p`: its coefficient
in the affine chart is `p`, and its value at `∞`, read in the inverted chart, is `-p.coeff 2`. For
`p = a + b z + c z²` it is the holomorphic vector field `(a + b z + c z²) ∂_z`, which reads as
`-(a w² + b w + c) ∂_w` in the inverted chart `w = z⁻¹`. -/
def polynomialVectorField : ℂ[X] →ₗ[ℂ] OnePoint ℂ → ℂ where
  toFun p x := x.elim (-p.coeff 2) p.eval
  map_add' p q := by
    funext x
    induction x using OnePoint.rec with
    | infty => simp [add_comm]
    | coe z => simp
  map_smul' c p := by
    funext x
    induction x using OnePoint.rec with
    | infty => simp
    | coe z => simp [Polynomial.eval_smul, smul_eq_mul]

@[simp]
theorem polynomialVectorField_coe (p : ℂ[X]) (z : ℂ) :
    polynomialVectorField p z = p.eval z :=
  (rfl)

@[simp]
theorem polynomialVectorField_infty (p : ℂ[X]) :
    polynomialVectorField p ∞ = -p.coeff 2 :=
  (rfl)

theorem polynomialVectorField_injective : Injective polynomialVectorField := fun p q h ↦
  Polynomial.funext fun z ↦ by simpa using congrFun h z

/-- A polynomial of degree less than `3` is `a + b z + c z²`. -/
private theorem eval_eq_of_mem_degreeLT {p : ℂ[X]} (hp : p ∈ degreeLT ℂ 3) (z : ℂ) :
    p.eval z = p.coeff 0 + p.coeff 1 * z + p.coeff 2 * z ^ 2 := by
  rcases eq_or_ne p 0 with rfl | hp0
  · simp
  have hn : p.natDegree < 3 := (natDegree_lt_iff_degree_lt hp0).2 (mem_degreeLT.1 hp)
  rw [eval_eq_sum_range' hn]
  simp [Finset.sum_range_succ]

/-- The inverted-chart coefficient of `p(z) ∂_z` for `p = a + b z + c z²` is
`-(a w² + b w + c)`. -/
private theorem invChartCoeff_polynomialVectorField {p : ℂ[X]} (hp : p ∈ degreeLT ℂ 3) (w : ℂ) :
    invChartCoeff (polynomialVectorField p) w =
      -(p.coeff 0 * w ^ 2 + p.coeff 1 * w + p.coeff 2) := by
  rcases eq_or_ne w 0 with rfl | hw
  · simp [invChartCoeff_zero]
  rw [invChartCoeff_of_ne_zero _ hw, polynomialVectorField_coe, eval_eq_of_mem_degreeLT hp]
  field_simp

/-! ### Holomorphic vector fields -/

/-- **Holomorphic vector fields on the Riemann sphere.** A vector field `X` on `OnePoint ℂ` is
holomorphic exactly when it is `p(z) ∂_z` for a polynomial `p = a + b z + c z²` of degree less than
`3`; at `∞` it then takes the value `-c` in the inverted chart. -/
theorem mdifferentiable_tangent_iff (X : OnePoint ℂ → ℂ) :
    MDifferentiable 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ).tangent
        (fun x ↦ (⟨x, X x⟩ : TangentBundle 𝓘(ℂ, ℂ) (OnePoint ℂ))) ↔
      ∃ p ∈ degreeLT ℂ 3, polynomialVectorField p = X := by
  have hsplit : MDifferentiable 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ).tangent
        (fun x ↦ (⟨x, X x⟩ : TangentBundle 𝓘(ℂ, ℂ) (OnePoint ℂ))) ↔
      Differentiable ℂ (fun z : ℂ ↦ X z) ∧ DifferentiableAt ℂ (invChartCoeff X) 0 := by
    refine ⟨fun h ↦ ⟨fun z ↦ (mdifferentiableAt_tangent_coe_iff X z).1 (h z),
      (mdifferentiableAt_tangent_infty_iff X).1 (h ∞)⟩, fun ⟨hf, hh⟩ x ↦ ?_⟩
    induction x using OnePoint.rec with
    | infty => exact (mdifferentiableAt_tangent_infty_iff X).2 hh
    | coe z => exact (mdifferentiableAt_tangent_coe_iff X z).2 (hf z)
  rw [hsplit]
  constructor
  · rintro ⟨hf, hh⟩
    -- In the affine chart `X z = -z² h(z⁻¹)`, which is `O(|z|²)` since `h` is continuous at `0`.
    have hbound : (fun z ↦ invChartCoeff X z⁻¹) =O[cobounded ℂ] (fun _ ↦ (1 : ℂ)) :=
      (hh.continuousAt.tendsto.comp tendsto_inv₀_cobounded).isBigO_one ℂ
    have hgrowth : (fun z : ℂ ↦ X z) =O[cobounded ℂ] (· ^ 2) := by
      refine ((Asymptotics.isBigO_refl (fun z : ℂ ↦ z ^ 2) _).neg_left.mul hbound).congr' ?_ ?_
      · filter_upwards [eventually_ne_cobounded (0 : ℂ)] with z hz
        rw [invChartCoeff_of_ne_zero _ (inv_ne_zero hz), inv_inv]
        field_simp
      · filter_upwards with z using mul_one _
    obtain ⟨p, hpn, hp⟩ := hf.exists_eq_polynomial_eval_of_isBigO_pow hgrowth
    have hp' (z : ℂ) : X z = p.eval z := congrFun hp z
    have hpmem : p ∈ degreeLT ℂ 3 := mem_degreeLT.2 <| degree_le_natDegree.trans_lt
      (by exact_mod_cast (show p.natDegree < 3 by omega) : (p.natDegree : WithBot ℕ) < 3)
    refine ⟨p, hpmem, funext fun x ↦ ?_⟩
    induction x using OnePoint.rec with
    | coe z => exact (hp' z).symm
    | infty =>
      -- The value at `∞` is the limit of `h w = -(a w² + b w + c)` as `w → 0`.
      have hq : Continuous fun w : ℂ ↦ -(p.coeff 0 * w ^ 2 + p.coeff 1 * w + p.coeff 2) := by
        fun_prop
      have heq : invChartCoeff X =ᶠ[𝓝[≠] 0]
          fun w ↦ -(p.coeff 0 * w ^ 2 + p.coeff 1 * w + p.coeff 2) := by
        filter_upwards [self_mem_nhdsWithin] with w (hw : w ≠ 0)
        rw [invChartCoeff_of_ne_zero _ hw, hp', eval_eq_of_mem_degreeLT hpmem]
        field_simp
      have h0 := tendsto_nhds_unique
        (hh.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
        (((hq.tendsto 0).mono_left nhdsWithin_le_nhds).congr' heq.symm)
      rw [polynomialVectorField_infty, ← invChartCoeff_zero X, h0]
      simp
  · rintro ⟨p, hp, rfl⟩
    refine ⟨fun z ↦ by simpa using p.differentiable z, ?_⟩
    rw [funext (invChartCoeff_polynomialVectorField hp)]
    fun_prop

/-- The complex vector space of **holomorphic vector fields** on the Riemann sphere: the vector
fields `X` for which `x ↦ (x, X x)` is a holomorphic map into the tangent bundle. -/
def holomorphicVectorFields : Submodule ℂ (OnePoint ℂ → ℂ) where
  carrier := {X | MDifferentiable 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ).tangent
    (fun x ↦ (⟨x, X x⟩ : TangentBundle 𝓘(ℂ, ℂ) (OnePoint ℂ)))}
  add_mem' hX hY := mdifferentiable_add_section hX hY
  zero_mem' := mdifferentiable_zeroSection ℂ (TangentSpace 𝓘(ℂ, ℂ))
  smul_mem' _ _ hX := mdifferentiable_smul_const_section hX

theorem mem_holomorphicVectorFields {X : OnePoint ℂ → ℂ} :
    X ∈ holomorphicVectorFields ↔ MDifferentiable 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ).tangent
      (fun x ↦ (⟨x, X x⟩ : TangentBundle 𝓘(ℂ, ℂ) (OnePoint ℂ))) :=
  (Iff.rfl)

/-- The holomorphic vector fields are the images of the polynomials of degree less than `3`. -/
theorem holomorphicVectorFields_eq_map :
    holomorphicVectorFields = (degreeLT ℂ 3).map polynomialVectorField := by
  ext X
  rw [mem_holomorphicVectorFields, mdifferentiable_tangent_iff, Submodule.mem_map]

/-- The holomorphic vector fields on the Riemann sphere are the fields `(a + b z + c z²) ∂_z`: the
space they form is isomorphic to the space of polynomials of degree less than `3`. -/
def holomorphicVectorFieldsEquiv : holomorphicVectorFields ≃ₗ[ℂ] degreeLT ℂ 3 :=
  (LinearEquiv.ofEq _ _ holomorphicVectorFields_eq_map).trans
    (Submodule.equivMapOfInjective _ polynomialVectorField_injective _).symm

/-- The holomorphic vector fields on the Riemann sphere form a complex vector space of
dimension `3`. -/
theorem finrank_holomorphicVectorFields : Module.finrank ℂ holomorphicVectorFields = 3 := by
  rw [holomorphicVectorFieldsEquiv.finrank_eq, (degreeLTEquiv ℂ 3).finrank_eq,
    Module.finrank_fin_fun]

/-- The holomorphic vector fields on the Riemann sphere form a real vector space of dimension `6`,
the real dimension of `PSL₂(ℂ)`. -/
theorem finrank_real_holomorphicVectorFields : Module.finrank ℝ holomorphicVectorFields = 6 := by
  rw [finrank_real_of_complex, finrank_holomorphicVectorFields]

/-- **Index Check on `TS²`.** The real dimension of the holomorphic vector fields on the Riemann
sphere, which is the kernel of `∂bar` on `TS²` (whose cokernel vanishes), is the Riemann–Roch index
`n χ + 2 c₁` with `n = 1`, `χ(S²) = 2` and `c₁(TS²)[S²] = 2`. -/
theorem finrank_real_holomorphicVectorFields_eq_index :
    Module.finrank ℝ holomorphicVectorFields = 1 * 2 + 2 * 2 :=
  finrank_real_holomorphicVectorFields

/-- **Index Check on `TS²`, wrong formula.** The variant `n χ + c₁` of the index formula, with
`c₁` in place of `2 c₁`, would predict real dimension `4`, which is wrong. -/
theorem finrank_real_holomorphicVectorFields_ne :
    Module.finrank ℝ holomorphicVectorFields ≠ 1 * 2 + 2 := by
  rw [finrank_real_holomorphicVectorFields]
  decide

end OnePoint
