/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import TauCeti.Geometry.Contact.Basic
public import TauCeti.Geometry.Manifold.ContMDiff.Log
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Smooth
public import TauCeti.Geometry.Manifold.MFDeriv.Prod
public import TauCeti.Geometry.Manifold.VectorBundle.Tangent.Basic
public import TauCeti.Geometry.Manifold.VectorField.ModelChart
public import TauCeti.Geometry.Manifold.VectorField.Prod
public import TauCeti.Geometry.Symplectic.Liouville.VectorField
public import TauCeti.Geometry.Symplectic.Manifold.TwoForm
import TauCeti.Geometry.Manifold.DifferentialForm.Closed
import TauCeti.Geometry.Manifold.DifferentialForm.Naturality
import TauCeti.Geometry.Manifold.DifferentialForm.Wedge.Leibniz
import TauCeti.LinearAlgebra.BilinearForm.Basic

/-!
# The symplectization of a contact form

Let `α` be a one-form on a manifold `M`. Its **symplectization** is the product `ℝ × M`, with real
coordinate `t`, carrying the one-form

`θ = eᵗ α` (`TauCeti.SmoothForm.symplectization α`),

where `α` is pulled back along the projection to `M`. Its exterior derivative is
`dθ = eᵗ (dt ∧ α + dα)`: on tangent vectors `(s, v)` and `(t', w)` at `(t, x)` it takes the value
`eᵗ (s α(w) - t' α(v) + dα(v, w))` (`TauCeti.SmoothForm.mextDeriv_symplectization_apply`).
The two-form `dθ` is symplectic exactly when `α` is a contact form
(`TauCeti.SmoothForm.isSymplectic_mextDerivₗ_symplectization_iff`). Closedness is automatic, and
nondegeneracy is, at each point, the linear algebra of
`Module.Dual.isContact_iff_nondegenerate_symplectizationForm`.

With the conventions `ω = -dλ` for exact symplectic manifolds and `ι_Z ω = -λ` for their Liouville
fields, the symplectization of a contact form is the exact symplectic manifold
`(ℝ × M, ω = dθ)` with primitive `λ = -θ`. Its Liouville field is the unit vector field `∂_t` along
the real factor: `ι_(∂_t) dθ = θ`
(`TauCeti.SmoothForm.interior_mextDeriv_symplectization`), so `∂_t` is a Liouville vector field of
`dθ` (`TauCeti.SmoothForm.isLiouvilleVectorField_symplectization`).

If a smooth map `F : M → M'` pulls a one-form `α'` back to `f α` for a smooth positive function
`f`, then its lift `(t, x) ↦ (t - log f(x), F(x))` pulls `eᵗ α'` back to `eᵗ α`
(`TauCeti.SmoothForm.mpullback_symplectizationLift_symplectization`). For a
coorientation-preserving contactomorphism this is its lift to the symplectizations; it preserves
the primitive `θ` and not only `dθ`. Taking `F` to be the identity, the map
`(t, x) ↦ (t - log f(x), x)` pulls the symplectization form of `f α` back to that of `α`.

If instead `f` is negative, the lift for `-f` pulls the symplectization form of `-α'` back to that
of `α` (`TauCeti.SmoothForm.mpullback_symplectizationLift_neg_symplectization`). For a nowhere
vanishing `α`, the strict lift has no free constant: a map `(t, x) ↦ (φ(t, x), F(x))` covering `F`
pulls `eᵗ α'` back to `eᵗ α` only when `f > 0` and `φ(t, x) = t - log f(x)`
(`TauCeti.SmoothForm.eq_symplectizationLift_of_mpullback_symplectization_eq`).

This file treats the symplectization of a chosen contact form, that is, of a trivialized
cooriented contact structure. In terms of the annihilator line `(ker α)⁰ ⊂ T*M`, the point
`(t, x)` corresponds to the covector `eᵗ α_x` of its positive half.

## Main definitions

* `TauCeti.SmoothForm.symplectization α`: the one-form `eᵗ α` on `ℝ × M`.
* `TauCeti.symplectizationLift`: the map `(t, x) ↦ (t - log f(x), F(x))`.

## Main results

* `TauCeti.SmoothForm.mextDeriv_symplectization_apply`: `d(eᵗ α) = eᵗ (dt ∧ α + dα)`.
* `TauCeti.SmoothForm.isSymplectic_mextDerivₗ_symplectization_iff`: `d(eᵗ α)` is symplectic exactly
  when `α` is a contact form.
* `TauCeti.SmoothForm.interior_mextDeriv_symplectization`,
  `TauCeti.SmoothForm.isLiouvilleVectorField_symplectization`: `∂_t` is the Liouville field.
* `TauCeti.SmoothForm.mpullback_symplectizationLift_symplectization`: lifts of conformal maps of
  one-forms preserve the symplectization form.
* `TauCeti.SmoothForm.eq_symplectizationLift_of_mpullback_symplectization_eq`: uniqueness of the
  strict lift.

## References

* H. Geiges, *An Introduction to Contact Topology*, Cambridge University Press, 2008,
  Section 1.1 and Appendix B (symplectization).
* D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford, 2017,
  Section 3.5 (the symplectization of a contact manifold).
-/

public section

noncomputable section

open Manifold
open scoped Manifold ContDiff

namespace TauCeti

namespace SmoothForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- The **symplectization form** `eᵗ α` on `ℝ × M` of a one-form `α` on `M`, where `t` is the real
coordinate and `α` is pulled back along the projection to `M`. When `α` is a contact form, its
exterior derivative is a symplectic form
(`TauCeti.SmoothForm.isSymplectic_mextDerivₗ_symplectization_iff`). -/
def symplectization (α : SmoothForm I M ℝ 1) : SmoothForm (𝓘(ℝ).prod I) (ℝ × M) ℝ 1 :=
  ⟨fun p ↦ Real.exp p.1 • (mpullback Prod.snd contMDiff_snd α).1 p,
    ((mpullback Prod.snd contMDiff_snd α).isSmoothForm.fun_smul
      (Real.contDiff_exp.contMDiff.comp contMDiff_fst)).mem_smoothBundleForms⟩

/-- The symplectization form is `eᵗ` times the pullback of the form along the projection. -/
theorem coe_symplectization (α : SmoothForm I M ℝ 1) :
    α.symplectization.1 = fun p ↦ Real.exp p.1 • (mpullback Prod.snd contMDiff_snd α).1 p :=
  (rfl)

/-- The symplectization form sends a tangent vector `(s, v)` at `(t, x)` to `eᵗ α_x(v)`. -/
@[simp]
theorem symplectization_apply (α : SmoothForm I M ℝ 1) (p : ℝ × M)
    (v : TangentSpace (𝓘(ℝ).prod I) p) :
    α.symplectization.1 p ![v] =
      Real.exp p.1 * α.1 p.2 ![(Manifold.tangentSpaceProdEquiv p v).2] := by
  simp only [coe_symplectization, ContinuousAlternatingMap.smul_apply, smul_eq_mul,
    mpullback_snd_apply, Matrix.vec_single_eq_const]

variable (I) in
/-- The exterior derivative of the symplectization form `eᵗ α` is `eᵗ (dt ∧ α + dα)`: it takes the
value `eᵗ (s α_x(w) - s' α_x(v) + dα_x(v, w))` on tangent vectors `(s, v)` and `(s', w)` at
`(t, x)`. -/
theorem mextDeriv_symplectization_apply (α : SmoothForm I M ℝ 1) (p : ℝ × M)
    (v w : TangentSpace (𝓘(ℝ).prod I) p) :
    mextDeriv α.symplectization.1 p ![v, w] =
      Real.exp p.1 *
        (NormedSpace.fromTangentSpace p.1 (Manifold.tangentSpaceProdEquiv p v).1 *
            α.1 p.2 ![(Manifold.tangentSpaceProdEquiv p w).2] -
          NormedSpace.fromTangentSpace p.1 (Manifold.tangentSpaceProdEquiv p w).1 *
            α.1 p.2 ![(Manifold.tangentSpaceProdEquiv p v).2] +
          mextDeriv α.1 p.2 ![(Manifold.tangentSpaceProdEquiv p v).2,
            (Manifold.tangentSpaceProdEquiv p w).2]) := by
  set β : SmoothForm (𝓘(ℝ).prod I) (ℝ × M) ℝ 1 := mpullback Prod.snd contMDiff_snd α
  -- The pulled-back form evaluates on the second components.
  have hβ (u : TangentSpace (𝓘(ℝ).prod I) p) :
      β.1 p ![u] = α.1 p.2 ![(Manifold.tangentSpaceProdEquiv p u).2] := by
    simp only [β, mpullback_snd_apply, Matrix.vec_single_eq_const]
  -- Its exterior derivative is `dα` on the second components, by naturality.
  have hdβ : mextDeriv β.1 p ![v, w] =
      mextDeriv α.1 p.2 ![(Manifold.tangentSpaceProdEquiv p v).2,
        (Manifold.tangentSpaceProdEquiv p w).2] := by
    have := eval₂_mpullback_snd (mextDerivₗ I 1 α) p v w
    rwa [← mextDerivₗ_mpullback, SmoothBundleForm.eval₂_apply, SmoothBundleForm.eval₂_apply,
      mextDerivₗ_apply, mextDerivₗ_apply] at this
  -- The derivative of `eᵗ` in the direction of `(s, v)` is `eᵗ s`.
  have hexp (u : TangentSpace (𝓘(ℝ).prod I) p) :
      mvfderiv (𝓘(ℝ).prod I) (fun q : ℝ × M ↦ Real.exp q.1) p u =
        Real.exp p.1 * NormedSpace.fromTangentSpace p.1 (Manifold.tangentSpaceProdEquiv p u).1 := by
    rw [Manifold.tangentSpaceProdEquiv_apply, mul_comm, ← smul_eq_mul]
    exact (Real.hasDerivAt_exp p.1).mvfderiv_comp_fst_apply u
  rw [coe_symplectization,
    mextDeriv_fun_smul_apply (f := fun q ↦ Real.exp q.1)
      (((Real.contDiff_exp (n := 1)).contMDiff.comp contMDiff_fst p).mdifferentiableAt
        one_ne_zero)
      (β.mdifferentiableAt p),
    hexp, hexp, hβ, hβ, hdβ]
  ring

/-- The exterior derivative of the symplectization form, evaluated as a smooth two-form on two
tangent vectors. -/
theorem eval₂_mextDerivₗ_symplectization (α : SmoothForm I M ℝ 1) (p : ℝ × M)
    (v w : TangentSpace (𝓘(ℝ).prod I) p) :
    (mextDerivₗ (𝓘(ℝ).prod I) 1 α.symplectization).eval₂ p v w =
      Real.exp p.1 *
        (NormedSpace.fromTangentSpace p.1 (Manifold.tangentSpaceProdEquiv p v).1 *
            α.1 p.2 ![(Manifold.tangentSpaceProdEquiv p w).2] -
          NormedSpace.fromTangentSpace p.1 (Manifold.tangentSpaceProdEquiv p w).1 *
            α.1 p.2 ![(Manifold.tangentSpaceProdEquiv p v).2] +
          (mextDerivₗ I 1 α).eval₂ p.2 (Manifold.tangentSpaceProdEquiv p v).2
            (Manifold.tangentSpaceProdEquiv p w).2) := by
  rw [SmoothBundleForm.eval₂_apply, mextDerivₗ_apply, mextDeriv_symplectization_apply,
    SmoothBundleForm.eval₂_apply, mextDerivₗ_apply]

/-- At a point `(t, x)` of `ℝ × M`, the exterior derivative of the symplectization form is `eᵗ`
times the symplectization form `Module.Dual.symplectizationForm` of the covector `α_x` and the
bilinear form `dα_x`, read through the splitting `T_(t, x)(ℝ × M) = ℝ × T_x M`. -/
private theorem bilinFormAt_mextDerivₗ_symplectization (α : SmoothForm I M ℝ 1) (p : ℝ × M) :
    (mextDerivₗ (𝓘(ℝ).prod I) 1 α.symplectization).bilinFormAt p =
      LinearMap.BilinForm.congr
        (((NormedSpace.fromTangentSpace (𝕜 := ℝ) p.1).symm.prodCongr
          (ContinuousLinearEquiv.refl ℝ (TangentSpace I p.2))).trans
          (Manifold.tangentSpaceProdEquiv p).symm).toLinearEquiv
        (Real.exp p.1 •
          Module.Dual.symplectizationForm (degreeOneEquiv α p.2 : TangentSpace I p.2 →ₗ[ℝ] ℝ)
            ((mextDerivₗ I 1 α).bilinFormAt p.2)) := by
  refine LinearMap.ext₂ fun v w ↦ ?_
  rw [bilinFormAt_apply, eval₂_mextDerivₗ_symplectization, LinearMap.BilinForm.congr_apply,
    LinearMap.smul_apply, LinearMap.smul_apply, Module.Dual.symplectizationForm_apply,
    degreeOneEquiv_coe_apply, degreeOneEquiv_coe_apply, bilinFormAt_apply, smul_eq_mul]
  -- The inverse of the splitting sends `u` to its two components `(s, v)`.
  simp only [ContinuousLinearEquiv.coe_symm_toLinearEquiv, ContinuousLinearEquiv.symm_trans_apply,
    ContinuousLinearEquiv.symm_symm, ContinuousLinearEquiv.prodCongr_symm,
    ContinuousLinearEquiv.prodCongr_apply, ContinuousLinearEquiv.refl_symm,
    ContinuousLinearEquiv.coe_refl', id_eq]

/-- **The symplectization is symplectic.** The exterior derivative `d(eᵗ α)` of the
symplectization form is nondegenerate exactly when `α` is a contact form. -/
theorem isNondegenerate_mextDerivₗ_symplectization_iff {α : SmoothForm I M ℝ 1} :
    SmoothTwoForm.IsNondegenerate (mextDerivₗ (𝓘(ℝ).prod I) 1 α.symplectization) ↔
      α.IsContactForm := by
  have key (p : ℝ × M) :
      (∀ v, (∀ w, SmoothBundleForm.eval₂
        (mextDerivₗ (𝓘(ℝ).prod I) 1 α.symplectization) p v w = 0) → v = 0) ↔
        Module.Dual.IsContact (degreeOneEquiv α p.2 : TangentSpace I p.2 →ₗ[ℝ] ℝ)
          ((mextDerivₗ I 1 α).bilinFormAt p.2) := by
    trans ((mextDerivₗ (𝓘(ℝ).prod I) 1 α.symplectization).bilinFormAt p).Nondegenerate
    · rw [LinearMap.BilinForm.Nondegenerate,
        (isAlt_bilinFormAt _ p).isRefl.nondegenerate_iff_separatingLeft]
      simp only [LinearMap.SeparatingLeft, bilinFormAt_apply]
    rw [bilinFormAt_mextDerivₗ_symplectization, LinearMap.BilinForm.nondegenerate_congr_iff,
      TauCeti.BilinForm.nondegenerate_smul_iff (IsRegular.of_ne_zero (Real.exp_pos p.1).ne'),
      Module.Dual.isContact_iff_nondegenerate_symplectizationForm]
  rw [SmoothTwoForm.isNondegenerate_iff_separatingLeft, isContactForm_def]
  exact ⟨fun h x ↦ (key ((0 : ℝ), x)).1 (h ((0 : ℝ), x)), fun h p ↦ (key p).2 (h p.2)⟩

/-- **The symplectization is symplectic.** The exterior derivative `d(eᵗ α)` of the
symplectization form is a symplectic form on `ℝ × M` exactly when `α` is a contact form. -/
theorem isSymplectic_mextDerivₗ_symplectization_iff {α : SmoothForm I M ℝ 1} :
    SmoothTwoForm.IsSymplectic (mextDerivₗ (𝓘(ℝ).prod I) 1 α.symplectization) ↔
      α.IsContactForm :=
  ⟨fun h ↦ isNondegenerate_mextDerivₗ_symplectization_iff.1 h.isNondegenerate,
    fun h ↦ ⟨isClosed_mextDerivₗ _, isNondegenerate_mextDerivₗ_symplectization_iff.2 h⟩⟩

/-- The exterior derivative of the symplectization form of a contact form is symplectic. -/
theorem IsContactForm.isSymplectic_mextDerivₗ_symplectization {α : SmoothForm I M ℝ 1}
    (hα : α.IsContactForm) :
    SmoothTwoForm.IsSymplectic (mextDerivₗ (𝓘(ℝ).prod I) 1 α.symplectization) :=
  isSymplectic_mextDerivₗ_symplectization_iff.2 hα

/-! ### The Liouville field -/

/-- **The Liouville field of the symplectization.** The unit vector field `∂_t` along the real
factor of `ℝ × M` satisfies `ι_(∂_t) d(eᵗ α) = eᵗ α`. -/
theorem interior_mextDeriv_symplectization (α : SmoothForm I M ℝ 1) :
    (mextDeriv α.symplectization.1).interior
        (Manifold.prodVectorField (constVectorField (1 : ℝ)) (0 : (x : M) → TangentSpace I x)) =
      α.symplectization.1 := by
  funext p
  refine ContinuousAlternatingMap.ext fun v ↦ ?_
  have hv : v = ![v 0] := funext fun i ↦ by fin_cases i; rfl
  set Z := Manifold.prodVectorField (constVectorField (1 : ℝ)) (0 : (x : M) → TangentSpace I x)
  have hcons : (Matrix.vecCons (Z p) ![v 0] : Fin 2 → TangentSpace (𝓘(ℝ).prod I) p) =
      ![Z p, v 0] :=
    (rfl)
  rw [RoughForm.interior_apply, hv, hcons, mextDeriv_symplectization_apply,
    symplectization_apply]
  have h₀ : α.1 p.2 ![(0 : TangentSpace I p.2)] = 0 := (α.1 p.2).map_coord_zero 0 rfl
  have h₀' : mextDeriv α.1 p.2 ![(0 : TangentSpace I p.2),
      (Manifold.tangentSpaceProdEquiv p (v 0)).2] = 0 :=
    (mextDeriv α.1 p.2).map_coord_zero 0 rfl
  simp only [Z, Manifold.tangentSpaceProdEquiv_prodVectorField, Pi.zero_apply, h₀, h₀', mul_zero,
    sub_zero, add_zero]
  rw [constVectorField_apply, ContinuousLinearEquiv.apply_symm_apply, one_mul]

/-- **The Liouville field of the symplectization.** The unit vector field `∂_t` along the real
factor of `ℝ × M` is a Liouville vector field of `d(eᵗ α)`. -/
theorem isLiouvilleVectorField_symplectization (α : SmoothForm I M ℝ 1) :
    IsLiouvilleVectorField (mextDeriv α.symplectization.1)
      (Manifold.prodVectorField (constVectorField (1 : ℝ)) (0 : (x : M) → TangentSpace I x)) := by
  have hω := fun p ↦ by
    simpa only [mextDerivₗ_apply] using
      (mextDerivₗ (𝓘(ℝ).prod I) 1 α.symplectization).mdifferentiableAt p
  have hZ : ContMDiff (𝓘(ℝ).prod I) (𝓘(ℝ).prod I).tangent ∞
      (T% (Manifold.prodVectorField (constVectorField (1 : ℝ)) (0 : (x : M) → TangentSpace I x))) :=
    Manifold.contMDiff_prodVectorField (contMDiff_constVectorField 1)
      (Bundle.contMDiff_zeroSection ℝ (TangentSpace I))
  rw [isLiouvilleVectorField_iff_mextDeriv_interior_eq hω (hZ.mdifferentiable (by simp))
    (SmoothForm.mextDeriv_mextDeriv _), interior_mextDeriv_symplectization]

/-! ### Lifts of conformal maps -/

end SmoothForm

variable {E H M E' H' M' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {I' : ModelWithCorners ℝ E' H'} [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' ∞ M']

/-- The lift `(t, x) ↦ (t - log f(x), F(x))` of a map `F : M → M'` to `ℝ × M → ℝ × M'`, for a
function `f` on `M`. When `F` pulls a one-form `α'` back to `f α` with `f` positive, it pulls the
symplectization form of `α'` back to that of `α`
(`TauCeti.SmoothForm.mpullback_symplectizationLift_symplectization`). -/
def symplectizationLift (F : M → M') (f : M → ℝ) (p : ℝ × M) : ℝ × M' :=
  (p.1 - Real.log (f p.2), F p.2)

omit [TopologicalSpace M] [TopologicalSpace M'] in
@[simp]
theorem symplectizationLift_apply (F : M → M') (f : M → ℝ) (p : ℝ × M) :
    symplectizationLift F f p = (p.1 - Real.log (f p.2), F p.2) :=
  (rfl)

omit [IsManifold I ∞ M] [IsManifold I' ∞ M'] in
/-- The lift of a smooth map along a smooth nowhere vanishing function is smooth. -/
theorem contMDiff_symplectizationLift {F : M → M'} (hF : ContMDiff I I' ∞ F) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ) ∞ f) (hf₀ : ∀ x, f x ≠ 0) :
    ContMDiff (𝓘(ℝ).prod I) (𝓘(ℝ).prod I') ∞ (symplectizationLift F f) :=
  (contMDiff_fst.sub ((hf.log hf₀).comp contMDiff_snd)).prodMk (hF.comp contMDiff_snd)

namespace SmoothForm

/-- Pulling back a symplectization form along a map covering `F` depends on its real component
only through its exponential. No derivative of that component occurs. -/
theorem mpullback_symplectization_apply_of_snd_eq {F : M → M'}
    (hF : ContMDiff I I' ∞ F) {f : M → ℝ} {α : SmoothForm I M ℝ 1}
    {α' : SmoothForm I' M' ℝ 1}
    (hα : ∀ x, (mpullback F hF α').1 x = f x • α.1 x)
    {Ψ : ℝ × M → ℝ × M'} (hΨ : ContMDiff (𝓘(ℝ).prod I) (𝓘(ℝ).prod I') ∞ Ψ)
    (hcover : ∀ p, (Ψ p).2 = F p.2) (p : ℝ × M)
    (v : TangentSpace (𝓘(ℝ).prod I) p) :
    (mpullback Ψ hΨ α'.symplectization).1 p ![v] =
      Real.exp (Ψ p).1 * f p.2 * α.1 p.2 ![(Manifold.tangentSpaceProdEquiv p v).2] := by
  have hcomp : TauCeti.mpullback (𝓘(ℝ).prod I) (𝓘(ℝ).prod I') Ψ
      (mpullback Prod.snd contMDiff_snd α').1 =
        TauCeti.mpullback (𝓘(ℝ).prod I) I Prod.snd (mpullback F hF α').1 := by
    rw [coe_mpullback, coe_mpullback,
      ← TauCeti.mpullback_comp (hΨ.mdifferentiable (by simp)) mdifferentiable_snd,
      ← TauCeti.mpullback_comp mdifferentiable_snd (hF.mdifferentiable (by simp))]
    exact congrArg (fun G ↦ TauCeti.mpullback (𝓘(ℝ).prod I) I' G α'.1) (funext hcover)
  have h := congrArg (fun φ ↦ φ p ![v]) hcomp
  rw [← coe_mpullback Prod.snd contMDiff_snd, mpullback_snd_apply, hα p.2] at h
  simp only [ContinuousAlternatingMap.smul_apply, smul_eq_mul,
    Matrix.vec_single_eq_const] at h
  simp only [coe_mpullback, TauCeti.mpullback_apply, coe_symplectization,
    ContinuousAlternatingMap.smul_apply, smul_eq_mul] at h ⊢
  simp only [Matrix.vec_single_eq_const] at h ⊢
  rw [h]
  ring

/-- **Lifts of conformal maps preserve the symplectization form.** If a smooth map `F : M → M'`
pulls a one-form `α'` back to `f α`, for a smooth positive function `f`, then its lift
`(t, x) ↦ (t - log f(x), F(x))` pulls the symplectization form `eᵗ α'` back to `eᵗ α`. For a
contactomorphism `F` preserving coorientations, this is its exact symplectic lift to the
symplectizations. -/
theorem mpullback_symplectizationLift_symplectization {F : M → M'} (hF : ContMDiff I I' ∞ F)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f) (hf₀ : ∀ x, 0 < f x) {α : SmoothForm I M ℝ 1}
    {α' : SmoothForm I' M' ℝ 1} (hα : ∀ x, (mpullback F hF α').1 x = f x • α.1 x) :
    mpullback (symplectizationLift F f)
        (contMDiff_symplectizationLift hF hf fun x ↦ (hf₀ x).ne') α'.symplectization =
      α.symplectization := by
  apply Subtype.ext
  funext p
  refine ContinuousAlternatingMap.ext fun v ↦ ?_
  have hv : v = ![v 0] := by ext i; fin_cases i; rfl
  rw [hv, mpullback_symplectization_apply_of_snd_eq hF hα _ (fun _ ↦ rfl),
    symplectization_apply, symplectizationLift_apply, Real.exp_sub, Real.exp_log (hf₀ p.2)]
  field_simp [(hf₀ p.2).ne']

/-- **Lifts of coorientation-reversing maps.** If a smooth map `F : M → M'` pulls a one-form `α'`
back to `f α`, for a smooth negative function `f`, then the lift
`(t, x) ↦ (t - log(-f(x)), F(x))` pulls the symplectization form `eᵗ (-α')` of the oppositely
cooriented form back to `eᵗ α`. In terms of annihilator lines, it interchanges their two halves. -/
theorem mpullback_symplectizationLift_neg_symplectization {F : M → M'}
    (hF : ContMDiff I I' ∞ F) {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f) (hf₀ : ∀ x, f x < 0)
    {α : SmoothForm I M ℝ 1} {α' : SmoothForm I' M' ℝ 1}
    (hα : ∀ x, (mpullback F hF α').1 x = f x • α.1 x) :
    mpullback (symplectizationLift F (-f))
        (contMDiff_symplectizationLift hF hf.neg fun x ↦ neg_ne_zero.2 (hf₀ x).ne)
        (-α').symplectization =
      α.symplectization :=
  mpullback_symplectizationLift_symplectization hF hf.neg (fun x ↦ neg_pos.2 (hf₀ x))
    fun x ↦ mpullback_neg_apply_eq_neg_smul (hα x)

/-- **Uniqueness of the strict lift.** Let a smooth map `F : M → M'` pull a one-form `α'` back to
`f α`, where `α` vanishes nowhere. If a smooth map of the form `(t, x) ↦ (φ(t, x), F(x))` pulls the
symplectization form `eᵗ α'` back to `eᵗ α`, then `f` is positive and the map is the lift
`(t, x) ↦ (t - log f(x), F(x))`. In particular a strict lift of a contactomorphism to the
symplectizations has no free additive constant. -/
theorem eq_symplectizationLift_of_mpullback_symplectization_eq {F : M → M'}
    (hF : ContMDiff I I' ∞ F) {f : M → ℝ} {α : SmoothForm I M ℝ 1} {α' : SmoothForm I' M' ℝ 1}
    (hα : ∀ x, (mpullback F hF α').1 x = f x • α.1 x) (hα₀ : ∀ x, α.1 x ≠ 0)
    {φ : ℝ × M → ℝ} (hφ : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) ∞ φ)
    (h : mpullback (fun p ↦ (φ p, F p.2)) (hφ.prodMk (hF.comp contMDiff_snd))
        α'.symplectization = α.symplectization) :
    (∀ x, 0 < f x) ∧ (fun p ↦ (φ p, F p.2)) = symplectizationLift F f := by
  -- Evaluating both forms at `p` on a vector `(0, v)` with `α(v) ≠ 0` gives `e^φ f = eᵗ`.
  have key (p : ℝ × M) : Real.exp (φ p) * f p.2 = Real.exp p.1 := by
    obtain ⟨v, hv⟩ := RoughForm.exists_apply_ne_zero (hα₀ p.2)
    set u := (Manifold.tangentSpaceProdEquiv (I := 𝓘(ℝ)) (J := I) p).symm (0, v)
    have hΦ := ((hφ.prodMk (hF.comp contMDiff_snd)) p).mdifferentiableAt (by simp)
    have hu : (Manifold.tangentSpaceProdEquiv p u).2 = v := by
      rw [ContinuousLinearEquiv.apply_symm_apply]
    have hsnd : (Manifold.tangentSpaceProdEquiv (φ p, F p.2)
        (mfderiv (𝓘(ℝ).prod I) (𝓘(ℝ).prod I') (fun p ↦ (φ p, F p.2)) p u)).2 =
          mfderiv I I' F p.2 v := by
      rw [Manifold.tangentSpaceProdEquiv_apply]
      refine (hΦ.mfderiv_snd_apply u).symm.trans ?_
      -- The second coordinate of the map is `F ∘ Prod.snd`.
      rw [show (fun y ↦ (φ y, (F ∘ Prod.snd) y).2) = F ∘ Prod.snd from rfl,
        mfderiv_comp_apply p ((hF p.2).mdifferentiableAt (by simp)) mdifferentiableAt_snd,
        mfderiv_snd_apply, ← hu, Manifold.tangentSpaceProdEquiv_apply]
    have hp := congrArg (fun θ : SmoothForm (𝓘(ℝ).prod I) (ℝ × M) ℝ 1 ↦ θ.1 p ![u]) h
    have hF' := congrArg (fun A ↦ A ![v]) (hα p.2)
    simp only [mpullback_apply, Matrix.cons_val_fin_one, ← Matrix.vec_single_eq_const,
      symplectization_apply, hsnd, hu, ContinuousAlternatingMap.smul_apply, smul_eq_mul] at hp hF'
    rw [hF', ← mul_assoc] at hp
    exact mul_right_cancel₀ hv hp
  have hf (x : M) : 0 < f x :=
    pos_of_mul_pos_right ((key ((0 : ℝ), x)).symm ▸ Real.exp_pos 0) (Real.exp_pos _).le
  refine ⟨hf, funext fun p ↦ Prod.ext ?_ (by simp)⟩
  rw [symplectizationLift_apply, eq_sub_iff_add_eq, ← Real.log_exp (φ p),
    ← Real.log_mul (Real.exp_pos _).ne' (hf p.2).ne', key, Real.log_exp]

end SmoothForm

end TauCeti
