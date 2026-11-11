/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.AsymptoticOperator
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import TauCeti.MeasureTheory.Integral.Rectangle

/-!
# The formal adjoint of the stationary cylinder operator

Let `(V, ω)` be a finite-dimensional symplectic vector space, `J_t` a continuous family of
`ω`-invariant complex structures with associated forms `g_t = ω(·, J_t ·)`, and `S_t` a continuous
family of infinitesimally symplectic maps, the linearized Hamiltonian vector field along an orbit.
The linearized Floer operator at the stationary cylinder over the orbit is
`D ξ = ∂s ξ + J_t (∂t ξ - S_t ξ) = ∂s ξ + A ξ`
(`TauCeti.Floer.stationaryCylinderOperator`), where `A` is the asymptotic operator, symmetric for
the `L²` pairing `∫₀¹ g_t` on loops. Its formal adjoint for the pairing `∫∫ g_t` is therefore

`D† η = -∂s η + J_t (∂t η - S_t η) = -∂s η + A η`

(`TauCeti.Floer.stationaryCylinderAdjoint`). This file proves the corresponding Green formula and
uses it to show that `D` has no classical cokernel on decaying maps.

* **Green's formula.** For `C¹` maps `ξ` and `η` and a rectangle `[a₁, b₁] × [a₂, b₂]`,
  `∫∫ g(D ξ, η) = ∫∫ g(ξ, D† η)` plus the boundary terms `∫ g_t(ξ, η)` over the two vertical sides
  and `∫ ω(ξ, η)` over the two horizontal sides
  (`Floer.setIntegral_associatedBilinForm_stationaryCylinderOperator_eq_add`). Pointwise,
  `g(D ξ, η) - g(ξ, D† η)` is `∂s g_t(ξ, η) + ∂t ω(ξ, η)`: the complex structure cancels from the
  `t`-derivative terms, and the zeroth-order terms cancel because `S_t` is infinitesimally
  symplectic. For maps of period one in `t` the horizontal terms cancel, so on a finite cylinder
  `[a, b] × [0, 1]` with `ξ` vanishing on the two boundary slices the identity is
  `∫∫ g(D ξ, η) = ∫∫ g(ξ, D† η)`
  (`Floer.setIntegral_associatedBilinForm_stationaryCylinderOperator_eq_of_periodic`), and for a
  compactly supported `ξ` it holds over the whole plane
  (`Floer.integral_associatedBilinForm_stationaryCylinderOperator_eq_of_hasCompactSupport`).
* **Weak solutions of the adjoint equation.** For `ω`-invariant `J_t`, a `C¹` map `η` such that
  `∫∫ g(D ξ, η) = 0` for every smooth `ξ` compactly supported in an open set `U` solves
  `D† η = 0` on `U` (`Floer.eqOn_stationaryCylinderAdjoint_eq_zero_of_forall_integral_eq_zero`).
  This is the fundamental lemma of the calculus of variations
  (`IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero`) applied to the Green formula.
* **Reflection.** `D† η (s, t) = D (η ∘ ρ) (-s, t)` for the reflection `ρ (s, t) = (-s, t)`
  (`Floer.stationaryCylinderAdjoint_eq_stationaryCylinderOperator_comp`). So decaying solutions of
  `D† η = 0` are reflections of decaying solutions of `D ξ = 0`, and these vanish by
  `Floer.eq_zero_of_stationaryCylinderOperator_eq_zero`: a `C²` map of period one in `t` with
  `D† η = 0` which tends to zero with `∂t η` as `|s| → ∞` is zero
  (`Floer.eq_zero_of_stationaryCylinderAdjoint_eq_zero`).
* **No classical cokernel.** Consequently a `C²` map `η` of period one in `t`, decaying with
  `∂t η`, which is `L²`-orthogonal to `D ξ` for every smooth compactly supported `ξ`, is zero
  (`Floer.eq_zero_of_forall_integral_associatedBilinForm_stationaryCylinderOperator_eq_zero`).
  As for the injectivity of `D`, no nondegeneracy of the orbit is needed.

The injectivity of `D` on decaying maps, the `L²` estimate of
`TauCeti.Geometry.Symplectic.Floer.AsymptoticOperator.Estimate` at a nondegenerate orbit and the
vanishing of the classical cokernel proved here are the ingredients of the invertibility of
`∂s + A` on the cylinder. That invertibility itself, which needs the regularity of weak cokernel
elements in `L²` and the Sobolev realization of `D`, is not treated here.

## References

* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 2.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., AMS
  Colloquium Publications 52, 2012, Section 3.1, on the formal adjoint of a real Cauchy–Riemann
  operator.
-/

public section

open Function Filter Set MeasureTheory Topology

namespace TauCeti

namespace Floer

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {J : ℝ → AlmostComplexStructure V} {S : ℝ → V →L[ℝ] V} {ξ η : ℝ × ℝ → V} {z : ℝ × ℝ}

/-- The formal adjoint `D† η = -∂s η + J_t (∂t η - S_t η)` of the stationary cylinder operator
`D = ∂s + J_t (∂t - S_t)` for the `L²` pairing `∫∫ ω(·, J_t ·)`, with `s` the first and `t` the
second coordinate. On each slice `s = const` it is `-∂s + A` for the asymptotic operator `A`. -/
noncomputable def stationaryCylinderAdjoint (J : ℝ → AlmostComplexStructure V)
    (S : ℝ → V →L[ℝ] V) (η : ℝ × ℝ → V) (z : ℝ × ℝ) : V :=
  -fderiv ℝ η z stdComplexLineReal + J z.2 (fderiv ℝ η z stdComplexLineImag - S z.2 (η z))

/-- The defining formula of the formal adjoint of the stationary cylinder operator. -/
theorem stationaryCylinderAdjoint_def (J : ℝ → AlmostComplexStructure V) (S : ℝ → V →L[ℝ] V)
    (η : ℝ × ℝ → V) (z : ℝ × ℝ) :
    stationaryCylinderAdjoint J S η z =
      -fderiv ℝ η z stdComplexLineReal + J z.2 (fderiv ℝ η z stdComplexLineImag - S z.2 (η z)) :=
  (rfl)

/-- The formal adjoint vanishes on the zero map. -/
@[simp]
theorem stationaryCylinderAdjoint_zero : stationaryCylinderAdjoint J S 0 = 0 := by
  funext z
  simp [stationaryCylinderAdjoint_def]

/-- The formal adjoint commutes with real scaling. -/
@[simp]
theorem stationaryCylinderAdjoint_smul (c : ℝ) :
    stationaryCylinderAdjoint J S (c • η) = c • stationaryCylinderAdjoint J S η := by
  funext z
  simp only [stationaryCylinderAdjoint_def, fderiv_const_smul_field, Pi.smul_apply,
    smul_apply, map_sub, map_smul, smul_sub, smul_add, smul_neg]

/-- The formal adjoint is additive on maps differentiable at the point. -/
theorem stationaryCylinderAdjoint_add (hξ : DifferentiableAt ℝ ξ z)
    (hη : DifferentiableAt ℝ η z) :
    stationaryCylinderAdjoint J S (ξ + η) z =
      stationaryCylinderAdjoint J S ξ z + stationaryCylinderAdjoint J S η z := by
  simp only [stationaryCylinderAdjoint_def, fderiv_add hξ hη, Pi.add_apply,
    add_apply, map_add, map_sub, neg_add]
  abel

/-- On a map differentiable at `z`, the formal adjoint is `-∂s` plus the asymptotic operator
applied to the loop `t ↦ η(s, t)`. -/
theorem stationaryCylinderAdjoint_eq_neg_add_asymptoticOperator (hη : DifferentiableAt ℝ η z) :
    stationaryCylinderAdjoint J S η z =
      -fderiv ℝ η z stdComplexLineReal + asymptoticOperator J S (fun t ↦ η (z.1, t)) z.2 := by
  have h := stationaryCylinderOperator_eq_add_asymptoticOperator (J := J) (S := S) hη
  rw [stationaryCylinderOperator_def] at h
  rw [stationaryCylinderAdjoint_def, add_left_cancel h]

/-- **The formal adjoint is the reflected operator.** For the reflection `ρ (s, t) = (-s, t)`,
`D† η (s, t) = D (η ∘ ρ) (-s, t)`. -/
theorem stationaryCylinderAdjoint_eq_stationaryCylinderOperator_comp (η : ℝ × ℝ → V)
    (z : ℝ × ℝ) :
    stationaryCylinderAdjoint J S η z =
      stationaryCylinderOperator J S (fun w ↦ η (-w.1, w.2)) (-z.1, z.2) := by
  set ρ : (ℝ × ℝ) ≃L[ℝ] ℝ × ℝ :=
    (ContinuousLinearEquiv.neg ℝ).prodCongr (ContinuousLinearEquiv.refl ℝ ℝ)
  have hρ : (fun w : ℝ × ℝ ↦ η (-w.1, w.2)) = η ∘ ρ := rfl
  have hd : fderiv ℝ (η ∘ ρ) (-z.1, z.2) = (fderiv ℝ η z).comp (ρ : (ℝ × ℝ) →L[ℝ] ℝ × ℝ) := by
    rw [ρ.comp_right_fderiv]
    simp [ρ]
  rw [stationaryCylinderAdjoint_def, stationaryCylinderOperator_def, hρ, hd]
  simp [ρ, stdComplexLineReal_eq, stdComplexLineImag_eq, ← map_neg]

section Green

variable [FiniteDimensional ℝ V] {ω : SymplecticForm V}

omit [FiniteDimensional ℝ V] in
/-- The pointwise Green identity: for `ω`-invariant `J` and infinitesimally symplectic `T`,
`g(xs + J (xt - T x), y) = g(x, -ys + J (yt - T y)) + (ω(xs, J y) + ω(x, J ys)) + (ω(xt, y) +
ω(x, yt))` for `g = ω(·, J ·)`. The last two brackets are the derivatives of `g(ξ, η)` in `s` and
of `ω(ξ, η)` in `t` when `x, xs, xt` and `y, ys, yt` are the values and partial derivatives of
`ξ` and `η`. -/
private theorem associatedBilinForm_add_apply_eq {J : AlmostComplexStructure V} {T : V →L[ℝ] V}
    (hJ : ω.Invariant J) (hT : ∀ v w, ω (T v) w + ω v (T w) = 0) (x xs xt y ys yt : V) :
    ω.associatedBilinForm J (xs + J (xt - T x)) y =
      ω.associatedBilinForm J x (-ys + J (yt - T y)) + (ω xs (J y) + ω x (J ys)) +
        (ω xt y + ω x yt) := by
  have h₁ := (ω.invariant_iff J).mp hJ (xt - T x) y
  have h₂ := hT x y
  simp only [SymplecticForm.associatedBilinForm_apply, AlmostComplexStructure.apply_apply,
    map_add, map_sub, map_neg, LinearMap.add_apply, LinearMap.sub_apply] at h₁ h₂ ⊢
  linarith

omit [FiniteDimensional ℝ V] in
/-- For `C¹` maps `η`, the formal adjoint `D† η` is continuous. -/
theorem continuous_stationaryCylinderAdjoint (hJc : Continuous fun p : ℝ × V ↦ J p.1 p.2)
    (hSc : Continuous S) (hη : ContDiff ℝ 1 η) :
    Continuous (stationaryCylinderAdjoint J S η) := by
  have hdη : Continuous (fderiv ℝ η) := hη.continuous_fderiv one_ne_zero
  rw [funext (stationaryCylinderAdjoint_def J S η)]
  exact (hdη.clm_apply continuous_const).neg.add (hJc.comp (continuous_snd.prodMk
    ((hdη.clm_apply continuous_const).sub ((hSc.comp continuous_snd).clm_apply hη.continuous))))

/-- **Green's formula for the stationary cylinder operator.** Let each `J_t` leave `ω` invariant
and depend continuously on `t`, and let each `S_t` be infinitesimally symplectic. For `C¹` maps
`ξ` and `η` and a rectangle `[a₁, b₁] × [a₂, b₂]`, with `g_t = ω(·, J_t ·)`,

`∫∫ g(D ξ, η) = ∫∫ g(ξ, D† η) + ∫ (g_t(ξ, η)(b₁, t) - g_t(ξ, η)(a₁, t)) dt
  + ∫ (ω(ξ, η)(s, b₂) - ω(ξ, η)(s, a₂)) ds`. -/
theorem setIntegral_associatedBilinForm_stationaryCylinderOperator_eq_add
    (hJ : ∀ t, ω.Invariant (J t)) (hJc : Continuous fun p : ℝ × V ↦ J p.1 p.2)
    (hS : ∀ t v w, ω (S t v) w + ω v (S t w) = 0) (hSc : Continuous S) (hξ : ContDiff ℝ 1 ξ)
    (hη : ContDiff ℝ 1 η) {a₁ b₁ a₂ b₂ : ℝ} (h₁ : a₁ ≤ b₁) (h₂ : a₂ ≤ b₂) :
    ∫ z in Icc a₁ b₁ ×ˢ Icc a₂ b₂,
        ω.associatedBilinForm (J z.2) (stationaryCylinderOperator J S ξ z) (η z) =
      (∫ z in Icc a₁ b₁ ×ˢ Icc a₂ b₂,
          ω.associatedBilinForm (J z.2) (ξ z) (stationaryCylinderAdjoint J S η z)) +
        (∫ t in Icc a₂ b₂, (ω.associatedBilinForm (J t) (ξ (b₁, t)) (η (b₁, t)) -
          ω.associatedBilinForm (J t) (ξ (a₁, t)) (η (a₁, t)))) +
        ∫ s in Icc a₁ b₁, (ω (ξ (s, b₂)) (η (s, b₂)) - ω (ξ (s, a₂)) (η (s, a₂))) := by
  have hξd : Differentiable ℝ ξ := hξ.differentiable one_ne_zero
  have hηd : Differentiable ℝ η := hη.differentiable one_ne_zero
  have hdξ : Continuous (fderiv ℝ ξ) := hξ.continuous_fderiv one_ne_zero
  have hdη : Continuous (fderiv ℝ η) := hη.continuous_fderiv one_ne_zero
  have hJf {f : ℝ × ℝ → V} (hf : Continuous f) : Continuous fun z : ℝ × ℝ ↦ J z.2 (f z) :=
    hJc.comp (continuous_snd.prodMk hf)
  have hfst {f : ℝ × ℝ → V} (hf : Differentiable ℝ f) (s t : ℝ) :
      HasDerivAt (fun s ↦ f (s, t)) (fderiv ℝ f (s, t) (1, 0)) s :=
    (hf (s, t)).hasFDerivAt.comp_hasDerivAt s (hasDerivAt_prodMk_left s t)
  have hsnd {f : ℝ × ℝ → V} (hf : Differentiable ℝ f) (s t : ℝ) :
      HasDerivAt (fun t ↦ f (s, t)) (fderiv ℝ f (s, t) (0, 1)) t :=
    (hf (s, t)).hasFDerivAt.comp_hasDerivAt t (hasDerivAt_prodMk_right s t)
  -- The partial derivatives of `ξ` and `η`.
  set ξs : ℝ × ℝ → V := fun z ↦ fderiv ℝ ξ z (1, 0)
  set ξt : ℝ × ℝ → V := fun z ↦ fderiv ℝ ξ z (0, 1)
  set ηs : ℝ × ℝ → V := fun z ↦ fderiv ℝ η z (1, 0)
  set ηt : ℝ × ℝ → V := fun z ↦ fderiv ℝ η z (0, 1)
  have hξs : Continuous ξs := hdξ.clm_apply continuous_const
  have hξt : Continuous ξt := hdξ.clm_apply continuous_const
  have hηs : Continuous ηs := hdη.clm_apply continuous_const
  have hηt : Continuous ηt := hdη.clm_apply continuous_const
  -- `g(D ξ, η) - g(ξ, D† η) = ∂s φ₁ + ∂t φ₂` with `Φ₁ = g(ξ, η)` and `Φ₂ = ω(ξ, η)`.
  set φ₁ : ℝ × ℝ → ℝ := fun z ↦ ω (ξs z) (J z.2 (η z)) + ω (ξ z) (J z.2 (ηs z))
  set φ₂ : ℝ × ℝ → ℝ := fun z ↦ ω (ξt z) (η z) + ω (ξ z) (ηt z)
  set A : ℝ × ℝ → ℝ := fun z ↦
    ω.associatedBilinForm (J z.2) (ξ z) (stationaryCylinderAdjoint J S η z)
  have hφ₁ : Continuous φ₁ :=
    (ω.continuous_apply_comp hξs (hJf hη.continuous)).add
      (ω.continuous_apply_comp hξ.continuous (hJf hηs))
  have hφ₂ : Continuous φ₂ :=
    (ω.continuous_apply_comp hξt hη.continuous).add (ω.continuous_apply_comp hξ.continuous hηt)
  have hA : Continuous A := ω.continuous_apply_comp hξ.continuous
    (hJf (continuous_stationaryCylinderAdjoint hJc hSc hη))
  have hpt : ∀ z : ℝ × ℝ,
      ω.associatedBilinForm (J z.2) (stationaryCylinderOperator J S ξ z) (η z) =
        A z + φ₁ z + φ₂ z := fun z ↦ by
    simp only [A, stationaryCylinderOperator_def, stationaryCylinderAdjoint_def,
      stdComplexLineReal_eq, stdComplexLineImag_eq]
    exact associatedBilinForm_add_apply_eq (hJ z.2) (hS z.2) _ _ _ _ _ _
  have hR : IsCompact (Icc a₁ b₁ ×ˢ Icc a₂ b₂) := isCompact_Icc.prod isCompact_Icc
  have hJs (t : ℝ) (s : ℝ) : HasDerivAt (fun s ↦ J t (η (s, t))) (J t (ηs (s, t))) s :=
    (LinearMap.toContinuousLinearMap (J t).toLinearMap).hasFDerivAt.comp_hasDerivAt s
      (hfst hηd s t)
  have hI₁ : ∫ z in Icc a₁ b₁ ×ˢ Icc a₂ b₂, φ₁ z = ∫ t in Icc a₂ b₂,
      (ω.associatedBilinForm (J t) (ξ (b₁, t)) (η (b₁, t)) -
        ω.associatedBilinForm (J t) (ξ (a₁, t)) (η (a₁, t))) :=
    setIntegral_rect_eq_setIntegral_sub_of_hasDerivAt_fst (Φ := fun z ↦ ω (ξ z) (J z.2 (η z)))
      hφ₁ (fun s t ↦ ω.hasDerivAt_apply_comp (hfst hξd s t) (hJs t s)) h₁
  have hI₂ : ∫ z in Icc a₁ b₁ ×ˢ Icc a₂ b₂, φ₂ z =
      ∫ s in Icc a₁ b₁, (ω (ξ (s, b₂)) (η (s, b₂)) - ω (ξ (s, a₂)) (η (s, a₂))) :=
    setIntegral_rect_eq_setIntegral_sub_of_hasDerivAt_snd (Φ := fun z ↦ ω (ξ z) (η z)) hφ₂
      (fun s t ↦ ω.hasDerivAt_apply_comp (hsnd hξd s t) (hsnd hηd s t)) h₂
  rw [integral_congr_ae (Eventually.of_forall hpt),
    integral_add (f := fun z ↦ A z + φ₁ z) ((hA.add hφ₁).continuousOn.integrableOn_compact hR)
      (hφ₂.continuousOn.integrableOn_compact hR),
    integral_add (hA.continuousOn.integrableOn_compact hR)
      (hφ₁.continuousOn.integrableOn_compact hR), hI₁, hI₂]

/-- **Green's formula on a finite cylinder.** Under the hypotheses of
`Floer.setIntegral_associatedBilinForm_stationaryCylinderOperator_eq_add`, let `ξ` and `η` have
period one in `t`, and let `ξ` vanish on the slices `s = a` and `s = b`. Then
`∫∫ g(D ξ, η) = ∫∫ g(ξ, D† η)` over `[a, b] × [0, 1]`. -/
theorem setIntegral_associatedBilinForm_stationaryCylinderOperator_eq_of_periodic
    (hJ : ∀ t, ω.Invariant (J t)) (hJc : Continuous fun p : ℝ × V ↦ J p.1 p.2)
    (hS : ∀ t v w, ω (S t v) w + ω v (S t w) = 0) (hSc : Continuous S) (hξ : ContDiff ℝ 1 ξ)
    (hη : ContDiff ℝ 1 η) (hξp : ∀ s t, ξ (s, t + 1) = ξ (s, t))
    (hηp : ∀ s t, η (s, t + 1) = η (s, t)) {a b : ℝ} (hab : a ≤ b) (ha : ∀ t, ξ (a, t) = 0)
    (hb : ∀ t, ξ (b, t) = 0) :
    ∫ z in Icc a b ×ˢ Icc 0 1,
        ω.associatedBilinForm (J z.2) (stationaryCylinderOperator J S ξ z) (η z) =
      ∫ z in Icc a b ×ˢ Icc 0 1,
        ω.associatedBilinForm (J z.2) (ξ z) (stationaryCylinderAdjoint J S η z) := by
  have hξ1 (s : ℝ) : ξ (s, 1) = ξ (s, 0) := by simpa using hξp s 0
  have hη1 (s : ℝ) : η (s, 1) = η (s, 0) := by simpa using hηp s 0
  rw [setIntegral_associatedBilinForm_stationaryCylinderOperator_eq_add hJ hJc hS hSc hξ hη hab
    zero_le_one]
  simp [ha, hb, hξ1, hη1]

/-- **Green's formula for compactly supported maps.** Under the hypotheses of
`Floer.setIntegral_associatedBilinForm_stationaryCylinderOperator_eq_add`, if `ξ` has compact
support then `∫∫ g(D ξ, η) = ∫∫ g(ξ, D† η)` over the whole plane. -/
theorem integral_associatedBilinForm_stationaryCylinderOperator_eq_of_hasCompactSupport
    (hJ : ∀ t, ω.Invariant (J t)) (hJc : Continuous fun p : ℝ × V ↦ J p.1 p.2)
    (hS : ∀ t v w, ω (S t v) w + ω v (S t w) = 0) (hSc : Continuous S) (hξ : ContDiff ℝ 1 ξ)
    (hη : ContDiff ℝ 1 η) (hξc : HasCompactSupport ξ) :
    ∫ z, ω.associatedBilinForm (J z.2) (stationaryCylinderOperator J S ξ z) (η z) =
      ∫ z, ω.associatedBilinForm (J z.2) (ξ z) (stationaryCylinderAdjoint J S η z) := by
  obtain ⟨r, hr, hsub⟩ := hξc.isCompact.isBounded.subset_closedBall_lt 0 0
  -- Off the closed ball of radius `r`, both `ξ` and its derivative vanish.
  have hout {z : ℝ × ℝ} (hz : r < ‖z‖) : ξ z = 0 ∧ fderiv ℝ ξ z = 0 := by
    have hz' : z ∉ tsupport ξ := fun h ↦ by
      have := hsub h
      rw [Metric.mem_closedBall, dist_zero_right] at this
      linarith
    exact ⟨image_eq_zero_of_notMem_tsupport hz',
      notMem_support.mp fun h ↦ hz' (support_fderiv_subset ℝ h)⟩
  have hQ {z : ℝ × ℝ} (hz : z ∉ Icc (-(r + 1)) (r + 1) ×ˢ Icc (-(r + 1)) (r + 1)) : r < ‖z‖ := by
    simp only [mem_prod, mem_Icc, not_and_or, not_le] at hz
    have h₁ := norm_fst_le z
    have h₂ := norm_snd_le z
    rw [Real.norm_eq_abs] at h₁ h₂
    rcases hz with (h | h) | (h | h)
    · linarith [neg_abs_le z.1]
    · linarith [le_abs_self z.1]
    · linarith [neg_abs_le z.2]
    · linarith [le_abs_self z.2]
  have hside {z : ℝ × ℝ} (hz : |z.1| = r + 1 ∨ |z.2| = r + 1) : ξ z = 0 := by
    refine (hout ?_).1
    rcases hz with h | h
    · linarith [norm_fst_le z, Real.norm_eq_abs z.1]
    · linarith [norm_snd_le z, Real.norm_eq_abs z.2]
  have hpos : |r + 1| = r + 1 := abs_of_pos (by linarith)
  have hneg : |-(r + 1)| = r + 1 := by rw [abs_neg, hpos]
  have hD {z : ℝ × ℝ} (hz : r < ‖z‖) : stationaryCylinderOperator J S ξ z = 0 := by
    rw [stationaryCylinderOperator_def, (hout hz).1, (hout hz).2]
    simp
  have hL := setIntegral_eq_integral_of_forall_compl_eq_zero (μ := volume)
    (s := Icc (-(r + 1)) (r + 1) ×ˢ Icc (-(r + 1)) (r + 1))
    (f := fun z ↦ ω.associatedBilinForm (J z.2) (stationaryCylinderOperator J S ξ z) (η z))
    fun z hz ↦ by rw [hD (hQ hz), map_zero, LinearMap.zero_apply]
  have hR := setIntegral_eq_integral_of_forall_compl_eq_zero (μ := volume)
    (s := Icc (-(r + 1)) (r + 1) ×ˢ Icc (-(r + 1)) (r + 1))
    (f := fun z ↦ ω.associatedBilinForm (J z.2) (ξ z) (stationaryCylinderAdjoint J S η z))
    fun z hz ↦ by rw [(hout (hQ hz)).1, map_zero, LinearMap.zero_apply]
  rw [← hL, ← hR, setIntegral_associatedBilinForm_stationaryCylinderOperator_eq_add hJ hJc hS hSc
    hξ hη (by linarith) (by linarith)]
  have h₁ (t : ℝ) : ξ (r + 1, t) = 0 := hside (z := (r + 1, t)) (Or.inl hpos)
  have h₂ (t : ℝ) : ξ (-(r + 1), t) = 0 := hside (z := (-(r + 1), t)) (Or.inl hneg)
  have h₃ (s : ℝ) : ξ (s, r + 1) = 0 := hside (z := (s, r + 1)) (Or.inr hpos)
  have h₄ (s : ℝ) : ξ (s, -(r + 1)) = 0 := hside (z := (s, -(r + 1))) (Or.inr hneg)
  simp only [h₁, h₂, h₃, h₄]
  simp

/-- **Weak solutions of the adjoint equation are strong solutions.** Let each `J_t` leave `ω`
invariant and depend continuously on `t`, and let each `S_t` be infinitesimally symplectic.
If a `C¹` map `η` is `L²`-orthogonal to `D ξ` for every smooth map `ξ` compactly supported in an
open set `U`, for the pairing `∫∫ g(·, ·)` with `g_t = ω(·, J_t ·)`, then `D† η = 0` on `U`. The
pairing need not be positive: only its nondegeneracy is used. -/
theorem eqOn_stationaryCylinderAdjoint_eq_zero_of_forall_integral_eq_zero
    (hJ : ∀ t, ω.Invariant (J t)) (hJc : Continuous fun p : ℝ × V ↦ J p.1 p.2)
    (hS : ∀ t v w, ω (S t v) w + ω v (S t w) = 0) (hSc : Continuous S) (hη : ContDiff ℝ 1 η)
    {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    (h : ∀ ξ : ℝ × ℝ → V, ContDiff ℝ (⊤ : ℕ∞) ξ → HasCompactSupport ξ → tsupport ξ ⊆ U →
      ∫ z, ω.associatedBilinForm (J z.2) (stationaryCylinderOperator J S ξ z) (η z) = 0) :
    EqOn (stationaryCylinderAdjoint J S η) 0 U := by
  set f := stationaryCylinderAdjoint J S η
  have hf : Continuous f := continuous_stationaryCylinderAdjoint hJc hSc hη
  -- Testing against `ξ = φ • v` shows that each component `g(v, D† η)` vanishes on `U`.
  have hv (v : V) : EqOn (fun z : ℝ × ℝ ↦ ω.associatedBilinForm (J z.2) v (f z)) 0 U := by
    have hF : Continuous fun z : ℝ × ℝ ↦ ω.associatedBilinForm (J z.2) v (f z) :=
      ω.continuous_apply_comp continuous_const (hJc.comp (continuous_snd.prodMk hf))
    have hae := hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero (μ := volume)
      (hF.locallyIntegrable.locallyIntegrableOn U) fun φ hφ hφc hφU ↦ by
        have hξ : ContDiff ℝ (⊤ : ℕ∞) fun z ↦ φ z • v := hφ.smul contDiff_const
        have hξc : HasCompactSupport fun z ↦ φ z • v := hφc.smul_right (f' := fun _ ↦ v)
        have h₀ := h _ hξ hξc ((tsupport_smul_subset_left φ fun _ ↦ v).trans hφU)
        rw [integral_associatedBilinForm_stationaryCylinderOperator_eq_of_hasCompactSupport
          hJ hJc hS hSc (hξ.of_le (by simp)) hη hξc] at h₀
        simpa [smul_eq_mul] using h₀
    exact Measure.eqOn_open_of_ae_eq ((ae_restrict_iff' hU.measurableSet).2 hae) hU
      hF.continuousOn continuousOn_const
  -- The associated form `g_t` is nondegenerate, so `D† η = 0` on `U`.
  exact fun z hz ↦ (ω.associatedBilinForm_nondegenerate (J z.2)).2 (f z) fun v ↦ hv v hz

/-- **Decaying solutions of the adjoint equation vanish.** Let each `J_t` be `ω`-compatible and
depend continuously on `t`, and let each `S_t` be infinitesimally symplectic. A `C²` solution `η`
of `D† η = -∂s η + J_t (∂t η - S_t η) = 0` of period one in `t`, which tends to zero together with
`∂t η` as `|s| → ∞`, uniformly in `t`, is identically zero. -/
theorem eq_zero_of_stationaryCylinderAdjoint_eq_zero (hJ : ∀ t, ω.Compatible (J t))
    (hJc : Continuous fun p : ℝ × V ↦ J p.1 p.2)
    (hS : ∀ t v w, ω (S t v) w + ω v (S t w) = 0) (hSc : Continuous S) (hη : ContDiff ℝ 2 η)
    (hper : ∀ s t, η (s, t + 1) = η (s, t)) (hD : ∀ z, stationaryCylinderAdjoint J S η z = 0)
    (hdecay : Tendsto (fun z ↦ (η z, fderiv ℝ η z stdComplexLineImag))
      (comap Prod.fst (cocompact ℝ)) (𝓝 0)) :
    η = 0 := by
  -- The reflection `ρ (s, t) = (-s, t)` turns `D†` into `D`.
  set ρ : (ℝ × ℝ) ≃L[ℝ] ℝ × ℝ :=
    (ContinuousLinearEquiv.neg ℝ).prodCongr (ContinuousLinearEquiv.refl ℝ ℝ)
  have hρ (z : ℝ × ℝ) : ρ z = (-z.1, z.2) := rfl
  have hfd (z : ℝ × ℝ) :
      fderiv ℝ (η ∘ ρ) z stdComplexLineImag = fderiv ℝ η (ρ z) stdComplexLineImag := by
    rw [ρ.comp_right_fderiv]
    simp [hρ, stdComplexLineImag_eq]
  have hρF : Tendsto ρ (comap Prod.fst (cocompact ℝ)) (comap Prod.fst (cocompact ℝ)) := by
    -- `Prod.fst ∘ ρ` is `Neg.neg ∘ Prod.fst` by definition of `ρ`.
    exact tendsto_comap_iff.2
      ((Homeomorph.neg ℝ).isClosedEmbedding.tendsto_cocompact.comp tendsto_comap)
  have h₀ : η ∘ ρ = 0 := by
    refine eq_zero_of_stationaryCylinderOperator_eq_zero hJ hJc hS hSc (hη.comp ρ.contDiff)
      (fun s t ↦ hper (-s) t) (fun z ↦ ?_) ?_
    · simpa [stationaryCylinderAdjoint_eq_stationaryCylinderOperator_comp, hρ, Function.comp_def]
        using hD (ρ z)
    · simp_rw [hfd]
      exact hdecay.comp hρF
  funext z
  simpa [hρ] using congrFun h₀ (ρ z)

/-- **The stationary cylinder operator has no classical cokernel.** Let each `J_t` be
`ω`-compatible and depend continuously on `t`, and let each `S_t` be infinitesimally symplectic. A
`C²` map `η` of period one in `t`, which tends to zero together with `∂t η` as `|s| → ∞`,
uniformly in `t`, and which is `L²`-orthogonal to `D ξ` for every smooth compactly supported `ξ`
for the pairing `∫∫ ω(·, J_t ·)`, is identically zero. No nondegeneracy of the orbit is needed. -/
theorem eq_zero_of_forall_integral_associatedBilinForm_stationaryCylinderOperator_eq_zero
    (hJ : ∀ t, ω.Compatible (J t)) (hJc : Continuous fun p : ℝ × V ↦ J p.1 p.2)
    (hS : ∀ t v w, ω (S t v) w + ω v (S t w) = 0) (hSc : Continuous S) (hη : ContDiff ℝ 2 η)
    (hper : ∀ s t, η (s, t + 1) = η (s, t))
    (hdecay : Tendsto (fun z ↦ (η z, fderiv ℝ η z stdComplexLineImag))
      (comap Prod.fst (cocompact ℝ)) (𝓝 0))
    (h : ∀ ξ : ℝ × ℝ → V, ContDiff ℝ (⊤ : ℕ∞) ξ → HasCompactSupport ξ →
      ∫ z, ω.associatedBilinForm (J z.2) (stationaryCylinderOperator J S ξ z) (η z) = 0) :
    η = 0 :=
  eq_zero_of_stationaryCylinderAdjoint_eq_zero hJ hJc hS hSc hη hper
    (fun z ↦ eqOn_stationaryCylinderAdjoint_eq_zero_of_forall_integral_eq_zero
      (fun t ↦ (hJ t).invariant) hJc hS hSc (hη.of_le (by norm_num)) isOpen_univ
      (fun ξ hξ hξc _ ↦ h ξ hξ hξc) (mem_univ z))
    hdecay

end Green

end Floer

end TauCeti
