/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Degree.Global
public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.ChangeOfVariables
public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Regularity
public import TauCeti.Geometry.Manifold.MFDeriv.Constancy
public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Orientation
public import TauCeti.Geometry.Symplectic.Manifold.Energy
public import TauCeti.Geometry.Symplectic.Manifold.JHolomorphic

/-!
# The energy of a map from a surface

Let `(C, j)` be a surface with an almost complex structure, `X` a manifold with a smooth two-form
`form` and an almost complex structure `J`, and `u : C → X`. The energy of `u` is half the
integral of `|du|²`, measured with the metric `g(v, w) = form(v, J w)` on `X` and a conformal
metric on `C`; it does not depend on the conformal metric. This file defines it without choosing
one. The **energy form** of `u` (`TauCeti.SmoothTwoForm.energyForm`) is the top form

`ε_u(v, w) = ½ (form(du (j v), J du w) - form(du (j w), J du v))`

on `C` (`TauCeti.SmoothTwoForm.energyForm_apply`). On a frame `(e, j e)` it is
`½ (form(du e, J du e) + form(du (j e), J du (j e)))`
(`TauCeti.SmoothTwoForm.energyForm_apply_frame`), half the energy density
`TauCeti.SmoothTwoForm.stdComplexLineEnergyDensity` of `du` read in the frame. Since `C` is
two-dimensional, the energy form depends only on the quadratic form `v ↦ form(v, J v)`, so it is
the same for the symmetrization of `form(·, J ·)`, the metric associated with a taming form. On a
surface oriented so that the frames `(e, j e)` are positive, the **energy** of `u`
(`TauCeti.SmoothTwoForm.energy`) is the integral of its energy form.

* **The energy identity.** Where `u` is pseudoholomorphic, its energy form is `u^* form`
  (`TauCeti.SmoothTwoForm.energyForm_eq_mpullback_of_isPseudoholomorphicAt`), so the energy of a
  pseudoholomorphic map is its symplectic area `∫_C u^* form`
  (`TauCeti.SmoothTwoForm.energy_eq_integralTopForm_mpullback`). No relation between `form` and
  `J` is needed.
* **Positivity.** Under tameness the energy is nonnegative
  (`TauCeti.SmoothTwoForm.Tames.energy_nonneg`). For a `C¹` map from a compact surface it vanishes
  exactly when `du = 0` (`TauCeti.SmoothTwoForm.Tames.energy_eq_zero_iff`), and then `u` is
  constant on a connected surface (`TauCeti.SmoothTwoForm.Tames.apply_eq_of_energy_eq_zero`).
* **The Wirtinger inequality.** For a compatible pair, the symplectic area of a `C¹` map from a
  compact surface is at most its energy
  (`TauCeti.SmoothTwoForm.Compatible.integralTopForm_mpullback_le_energy`), with equality exactly
  for pseudoholomorphic maps
  (`TauCeti.SmoothTwoForm.Compatible.energy_eq_integralTopForm_mpullback_iff`).
* **Changes of domain.** The energy form is natural under pseudoholomorphic maps of surfaces
  (`TauCeti.SmoothTwoForm.energyForm_comp_apply`). Hence the energy is invariant under
  pseudoholomorphic diffeomorphisms (`TauCeti.SmoothTwoForm.energy_comp_diffeomorph`), and
  precomposing a smooth pseudoholomorphic map with a proper pseudoholomorphic map multiplies its
  energy by the degree (`TauCeti.SmoothTwoForm.energy_comp_eq_degree_mul`).

The energy form of a `C¹` map is continuous (`TauCeti.SmoothTwoForm.isSmoothForm_energyForm`), so
it is integrable on a compact surface; the integral statements about compact surfaces rest on
this. The comparison of `∫_C u^* form` with the pairing of `[form]` with the homology class of `u`
is a de Rham comparison not made here.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications 52, 2012, Section 2.2 (the energy of a map from a Riemann surface, and
  the energy identity of Lemma 2.2.1).
-/

public section

noncomputable section

open Bundle Module
open scoped ContDiff Manifold

namespace TauCeti

namespace SmoothTwoForm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {X : Type*} [TopologicalSpace X] [ChartedSpace H X]
  [IsManifold I ∞ X]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] {H' : Type*}
  [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} {C : Type*} [TopologicalSpace C]
  [ChartedSpace H' C] [IsManifold I' ∞ C]

/-- The **energy form** of a map `u` from a surface `(C, j)` into `X`: the top form
`ε_u(v, w) = ½ (form(du (j v), J du w) - form(du (j w), J du v))`
(`TauCeti.SmoothTwoForm.energyForm_apply`). It is the polarization
`½ ((A + K)^* form - A^* form - K^* form)` of the pullbacks of `form` along `A = du ∘ j` and
`K = J ∘ du`. On a frame `(e, j e)` of a tangent plane it is half the energy density of `du`
(`TauCeti.SmoothTwoForm.energyForm_apply_frame`). -/
def energyForm (form : SmoothTwoForm I X) (J : SmoothAlmostComplexStructure I X)
    (j : SmoothAlmostComplexStructure I' C) (u : C → X) : RoughForm I' C ℝ 2 := fun c ↦
  (2⁻¹ : ℝ) • ((form.1 (u c)).compContinuousLinearMap
      ((mfderiv I' I u c).comp (j.toEndomorphism c) + (J.toEndomorphism (u c)).comp
        (mfderiv I' I u c)) -
    (form.1 (u c)).compContinuousLinearMap ((mfderiv I' I u c).comp (j.toEndomorphism c)) -
    (form.1 (u c)).compContinuousLinearMap ((J.toEndomorphism (u c)).comp (mfderiv I' I u c)))

variable {form : SmoothTwoForm I X} {J : SmoothAlmostComplexStructure I X}
  {j : SmoothAlmostComplexStructure I' C} {u : C → X}

/-- The energy form evaluates on `(v, w)` to
`½ (form(du (j v), J du w) - form(du (j w), J du v))`. -/
@[simp]
theorem energyForm_apply (c : C) (v w : TangentSpace I' c) :
    form.energyForm J j u c ![v, w] = 2⁻¹ *
      (SmoothBundleForm.eval₂ form (u c) (mfderiv I' I u c (j c v))
          (J (u c) (mfderiv I' I u c w)) -
        SmoothBundleForm.eval₂ form (u c) (mfderiv I' I u c (j c w))
          (J (u c) (mfderiv I' I u c v))) := by
  simp only [energyForm, ContinuousAlternatingMap.smul_apply, ContinuousAlternatingMap.sub_apply,
    ContinuousAlternatingMap.compContinuousLinearMap_apply, smul_eq_mul]
  congr 1
  have key (a b : TangentSpace I (u c)) :
      form.1 (u c) ![a, b] = form.bilinFormAt (u c) a b := by
    rw [SmoothForm.bilinFormAt_apply, SmoothBundleForm.eval₂_apply]
  have hcomp (L : TangentSpace I' c →L[ℝ] TangentSpace I (u c)) :
      ⇑L ∘ ![v, w] = ![L v, L w] := by
    ext i
    fin_cases i <;> rfl
  simp only [hcomp, key, add_apply, ContinuousLinearMap.comp_apply, map_add, LinearMap.add_apply]
  rw [← SmoothForm.bilinFormAt_apply, ← SmoothForm.bilinFormAt_apply]
  -- Expanding `(A + K)^* form - A^* form - K^* form` leaves `form(A v, K w) + form(K v, A w)`.
  have halt := LinearMap.IsAlt.neg (SmoothForm.isAlt_bilinFormAt form (u c))
    (mfderiv I' I u c (j.toEndomorphism c w)) (J.toEndomorphism (u c) (mfderiv I' I u c v))
  linarith

/-- On a frame `(e, j e)`, the energy form is
`½ (form(du e, J du e) + form(du (j e), J du (j e)))`, half the sum of the squared lengths of
`du e` and `du (j e)` for the metric `form(·, J ·)`. -/
theorem energyForm_apply_frame (c : C) (e : TangentSpace I' c) :
    form.energyForm J j u c ![e, j c e] = 2⁻¹ *
      (SmoothBundleForm.eval₂ form (u c) (mfderiv I' I u c e) (J (u c) (mfderiv I' I u c e)) +
        SmoothBundleForm.eval₂ form (u c) (mfderiv I' I u c (j c e))
          (J (u c) (mfderiv I' I u c (j c e)))) := by
  rw [energyForm_apply, j.apply_apply]
  simp only [map_neg, ← SmoothForm.bilinFormAt_apply, LinearMap.neg_apply]
  ring

/-- The value of the energy form on a frame `(e, j e)` is half the energy density of the map
`(s, t) ↦ du (s • e + t • j e)` from the standard complex line. -/
theorem energyForm_apply_frame_eq_stdComplexLineEnergyDensity (c : C) (e : TangentSpace I' c) :
    form.energyForm J j u c ![e, j c e] = 2⁻¹ * form.stdComplexLineEnergyDensity J (u c)
      ((mfderiv I' I u c).toLinearMap ∘ₗ
        (LinearMap.toSpanSingleton ℝ _ e).coprod (LinearMap.toSpanSingleton ℝ _ (j c e))) := by
  rw [energyForm_apply_frame, stdComplexLineEnergyDensity_def]
  simp [stdComplexLineReal, stdComplexLineImag]

/-- **The energy form of a pseudoholomorphic map is the pulled-back form.** At a point `c` of a
surface where `u` is pseudoholomorphic, the energy form of `u` is `u^* form`. Both are top forms on
the tangent plane at `c`, and they agree on a frame `(e, j e)`, where both equal
`form (du e, J du e)`. No relation between `form` and `J` is needed. -/
theorem energyForm_eq_mpullback_of_isPseudoholomorphicAt {c : C}
    (hc : finrank ℝ (TangentSpace I' c) = 2) (hu : IsPseudoholomorphicAt j J u c) :
    form.energyForm J j u c = mpullback I' I u form.1 c := by
  have : FiniteDimensional ℝ (TangentSpace I' c) := Module.finite_of_finrank_eq_succ hc
  obtain ⟨e, he⟩ := (finrank_pos_iff_exists_ne_zero (R := ℝ) (M := TangentSpace I' c)).1
    (by omega)
  -- The frame `(e, j e)` of the tangent plane at `c`.
  set b₀ := basisOfLinearIndependentOfCardEqFinrank
    ((j.almostComplexStructureAt c).linearIndependent_pair he) (by simp [hc])
  have hb₀ : ⇑b₀ = ![e, j c e] := by
    rw [coe_basisOfLinearIndependentOfCardEqFinrank,
      SmoothAlmostComplexStructure.almostComplexStructureAt_apply]
  rw [← sub_eq_zero]
  set η := form.energyForm J j u c - mpullback I' I u form.1 c
  have hη : η b₀ = 0 := by
    have halt := LinearMap.IsAlt.neg (SmoothForm.isAlt_bilinFormAt form (u c))
      (J (u c) (mfderiv I' I u c e)) (mfderiv I' I u c e)
    rw [hb₀, ContinuousAlternatingMap.sub_apply, energyForm_apply_frame, mpullback_apply_pair,
      hu.mfderiv_apply_commute, J.apply_apply, ← SmoothBundleForm.eval₂_apply]
    simp only [← SmoothForm.bilinFormAt_apply, map_neg] at halt ⊢
    linarith
  -- A top form on the plane is its value on the frame `b₀` times `det_{b₀}`.
  apply ContinuousAlternatingMap.toAlternatingMap_injective
  rw [η.toAlternatingMap.eq_smul_basis_det b₀]
  simp [hη]

/-- Under tameness, the energy form is nonnegative on every frame `(e, j e)`. -/
theorem Tames.energyForm_apply_frame_nonneg (htame : form.Tames J) (c : C)
    (e : TangentSpace I' c) : 0 ≤ form.energyForm J j u c ![e, j c e] := by
  rw [energyForm_apply_frame_eq_stdComplexLineEnergyDensity]
  exact mul_nonneg (by norm_num) (htame.stdComplexLineEnergyDensity_nonneg _ _)

/-- Under tameness, the energy form is positive on a frame `(e, j e)` with `du e ≠ 0`. -/
theorem Tames.energyForm_apply_frame_pos (htame : form.Tames J) {c : C}
    {e : TangentSpace I' c} (he : mfderiv I' I u c e ≠ 0) :
    0 < form.energyForm J j u c ![e, j c e] := by
  rw [energyForm_apply_frame_eq_stdComplexLineEnergyDensity]
  refine mul_pos (by norm_num) (htame.stdComplexLineEnergyDensity_pos _ fun h ↦ he ?_)
  simpa [stdComplexLineReal] using LinearMap.congr_fun h stdComplexLineReal

/-- **The pointwise Wirtinger inequality for a map from a surface.** For a compatible pair, the
pulled-back form `u^* form` is at most the energy form on every frame `(e, j e)`. -/
theorem Compatible.mpullback_apply_frame_le_energyForm_apply_frame (hcompat : form.Compatible J)
    (c : C) (e : TangentSpace I' c) :
    mpullback I' I u form.1 c ![e, j c e] ≤ form.energyForm J j u c ![e, j c e] := by
  have h := hcompat.two_mul_twoForm_le_stdComplexLineEnergyDensity (u c)
    ((mfderiv I' I u c).toLinearMap ∘ₗ
      (LinearMap.toSpanSingleton ℝ _ e).coprod (LinearMap.toSpanSingleton ℝ _ (j c e)))
  simp only [LinearMap.coe_comp, Function.comp_apply, stdComplexLineReal, stdComplexLineImag,
    LinearMap.coprod_apply, LinearMap.toSpanSingleton_apply, one_smul, zero_smul, add_zero,
    zero_add, ContinuousLinearMap.coe_coe] at h
  rw [energyForm_apply_frame_eq_stdComplexLineEnergyDensity, mpullback_apply_pair,
    ← SmoothBundleForm.eval₂_apply]
  linarith

/-- **The equality case of the pointwise Wirtinger inequality.** For a compatible pair, the energy
form and `u^* form` agree on a frame `(e, j e)` exactly when `du (j e) = J du e`. -/
theorem Compatible.energyForm_apply_frame_eq_mpullback_apply_frame_iff
    (hcompat : form.Compatible J) (c : C) (e : TangentSpace I' c) :
    form.energyForm J j u c ![e, j c e] = mpullback I' I u form.1 c ![e, j c e] ↔
      mfderiv I' I u c (j c e) = J (u c) (mfderiv I' I u c e) := by
  have h := hcompat.invariant.stdComplexLineEnergyDensity_sub_two_mul_twoForm (u c)
    ((mfderiv I' I u c).toLinearMap ∘ₗ
      (LinearMap.toSpanSingleton ℝ _ e).coprod (LinearMap.toSpanSingleton ℝ _ (j c e)))
  simp only [LinearMap.coe_comp, Function.comp_apply, stdComplexLineReal, stdComplexLineImag,
    LinearMap.coprod_apply, LinearMap.toSpanSingleton_apply, one_smul, zero_smul, add_zero,
    zero_add, ContinuousLinearMap.coe_coe] at h
  rw [energyForm_apply_frame_eq_stdComplexLineEnergyDensity, mpullback_apply_pair,
    ← SmoothBundleForm.eval₂_apply]
  set w := mfderiv I' I u c e + J (u c) (mfderiv I' I u c (j c e))
  -- The Cauchy–Riemann defect `w = du e + J du (j e)` vanishes exactly when `du (j e) = J du e`.
  have hw : w = 0 ↔ mfderiv I' I u c (j c e) = J (u c) (mfderiv I' I u c e) := by
    constructor
    · intro hw0
      have h1 := congrArg (J.toEndomorphism (u c)) hw0
      have h2 := J.apply_apply (u c) (mfderiv I' I u c (j c e))
      simp only [w, map_add, map_zero] at h1
      beta_reduce at h1 h2 ⊢
      rw [h2, ← sub_eq_add_neg, sub_eq_zero] at h1
      exact h1.symm
    · intro hcr
      simp [w, hcr, J.apply_apply]
  rw [← hw]
  constructor
  · intro heq
    by_contra hw0
    have := tames_iff.1 hcompat.tames (u c) w hw0
    linarith
  · intro hw0
    rw [hw0, map_zero, SmoothBundleForm.eval₂_self] at h
    linarith

/-- **Continuity of the energy form.** The energy form of a `C¹` map is continuous. -/
theorem isSmoothForm_energyForm [FiniteDimensional ℝ E'] (hu : ContMDiff I' I 1 u) :
    IsSmoothForm I' 0 (form.energyForm J j u) := by
  rw [isSmoothForm_iff_forall_contMDiffAt_trivializationAt_apply]
  intro x v
  -- The frame fields `y ↦ e.symmL y a` of the tangent trivialization `e` at `x`, and their
  -- images under `j`.
  have hV (a : E') : ContMDiffAt I' I'.tangent 0
      (fun y ↦ (⟨y, (trivializationAt E' (TangentSpace I') x).symmL ℝ y a⟩ :
        TangentBundle I' C)) x :=
    ((trivializationAt E' (TangentSpace I') x).contMDiffAt_symmL (n := 0)
      (mem_baseSet_trivializationAt E' (TangentSpace I') x)).clm_bundle_apply
      (by rw [Bundle.contMDiffAt_section_iff]; exact contMDiffAt_const)
  have hjV (a : E') : ContMDiffAt I' I'.tangent 0
      (fun y ↦ (⟨y, j y ((trivializationAt E' (TangentSpace I') x).symmL ℝ y a)⟩ :
        TangentBundle I' C)) x :=
    ((j.toEndomorphism.contMDiff x).of_le (by simp)).clm_bundle_apply (hV a)
  -- The images of tangent fields under `du`, and the images of those under `J`.
  have hdu {W : ∀ y, TangentSpace I' y}
      (hW : ContMDiffAt I' I'.tangent 0 (fun y ↦ (⟨y, W y⟩ : TangentBundle I' C)) x) :
      ContMDiffAt I' I.tangent 0
        (fun y ↦ (⟨u y, mfderiv I' I u y (W y)⟩ : TangentBundle I X)) x :=
    (contMDiff_zero_iff.2 (hu.continuous_tangentMap le_rfl)).contMDiffAt.comp x hW
  have hJdu {W : ∀ y, TangentSpace I' y}
      (hW : ContMDiffAt I' I'.tangent 0 (fun y ↦ (⟨y, W y⟩ : TangentBundle I' C)) x) :
      ContMDiffAt I' I.tangent 0
        (fun y ↦ (⟨u y, J (u y) (mfderiv I' I u y (W y))⟩ : TangentBundle I X)) x :=
    (((J.toEndomorphism.contMDiff (u x)).of_le (by simp)).comp x
      ((contMDiff_proj (TangentSpace I)).contMDiffAt.comp x (hdu hW))).clm_bundle_apply (hdu hW)
  have hfr (y : C) : ⇑((trivializationAt E' (TangentSpace I') x).symmL ℝ y) ∘ v =
      ![(trivializationAt E' (TangentSpace I') x).symmL ℝ y (v 0),
        (trivializationAt E' (TangentSpace I') x).symmL ℝ y (v 1)] := by
    ext i
    fin_cases i <;> rfl
  -- The scalar values of `form` along `u` on two such fields.
  have heval {P Q : ∀ y, TangentSpace I (u y)}
      (hP : ContMDiffAt I' I.tangent 0 (fun y ↦ (⟨u y, P y⟩ : TangentBundle I X)) x)
      (hQ : ContMDiffAt I' I.tangent 0 (fun y ↦ (⟨u y, Q y⟩ : TangentBundle I X)) x) :
      ContMDiffAt I' 𝓘(ℝ) 0 (fun y ↦ SmoothBundleForm.eval₂ form (u y) (P y) (Q y)) x :=
    (contMDiff_zero_iff.2
      (continuous_snd.comp (Trivial.homeomorphProd X ℝ).continuous)).contMDiffAt.comp x
        (SmoothBundleForm.contMDiffAt_eval₂ form hP hQ)
  simp only [hfr, energyForm_apply]
  refine (((heval (hdu (hjV (v 0))) (hJdu (hV (v 1)))).sub
    (heval (hdu (hjV (v 1))) (hJdu (hV (v 0))))).const_smul
      (2⁻¹ : ℝ)).congr_of_eventuallyEq (Filter.Eventually.of_forall fun y ↦ ?_)
  simp only [Pi.smul_apply, smul_eq_mul]

/-! ### The energy of a map from an oriented surface -/

variable [FiniteDimensional ℝ E'] {o : Manifold.Orientation I' C (Fin 2)}

/-- The **energy** of a map `u` from an oriented surface `(C, j)` into `X`: the integral of its
energy form `TauCeti.SmoothTwoForm.energyForm` against the orientation `o`. For a compact
surface oriented so that the frames `(e, j e)` are positive and a `C¹` map, this is half the
integral of `|du|²`. As for every top-form integral, it is `0` when the energy form is not
integrable. -/
def energy (form : SmoothTwoForm I X) (J : SmoothAlmostComplexStructure I X)
    (j : SmoothAlmostComplexStructure I' C) (o : Manifold.Orientation I' C (Fin 2)) (u : C → X) :
    ℝ :=
  integralTopForm o (form.energyForm J j u)

/-- Unfolding the energy into the integral of the energy form. -/
theorem energy_def : form.energy J j o u = integralTopForm o (form.energyForm J j u) :=
  (rfl)

/-- **The energy identity.** The energy of a pseudoholomorphic map from an oriented surface is its
symplectic area `∫_C u^* form`. No relation between `form` and `J` is needed. -/
theorem energy_eq_integralTopForm_mpullback (hhol : ∀ c, IsPseudoholomorphicAt j J u c) :
    form.energy J j o u = integralTopForm o (mpullback I' I u form.1) := by
  rw [energy, show form.energyForm J j u = mpullback I' I u form.1 from funext fun c ↦
    energyForm_eq_mpullback_of_isPseudoholomorphicAt (by simpa using o.finrank_tangentSpace_eq c)
      (hhol c)]

/-- **Nonnegativity of energy.** Under tameness, the energy of every map from a surface oriented
so that the frames `(e, j e)` are positive is nonnegative. -/
theorem Tames.energy_nonneg (htame : form.Tames J)
    (ho : ∀ c (b : Basis (Fin 2) ℝ (TangentSpace I' c)), b 1 = j c (b 0) →
      b.orientation = o.orientationAt c) :
    0 ≤ form.energy J j o u :=
  integralTopForm_nonneg o fun c b hb ↦
    j.apply_basis_nonneg_of_forall_nonneg (ho c) (htame.energyForm_apply_frame_nonneg c) b hb

section Compact

variable [CompactSpace C]

/-- The energy minus the symplectic area of a `C¹` map is the integral of the difference of the
two forms. -/
private theorem energy_sub_integralTopForm_mpullback (hu : ContMDiff I' I 1 u) :
    form.energy J j o u - integralTopForm o (mpullback I' I u form.1) =
      integralTopForm o (form.energyForm J j u + -mpullback I' I u form.1) := by
  have hpb : IsSmoothForm I' 0 (mpullback I' I u form.1) :=
    ((SmoothForm.isSmoothForm form).of_le (by simp)).mpullback (by simpa using hu)
  rw [energy, integralTopForm_add_of_compactSpace o (isSmoothForm_energyForm hu) hpb.neg,
    ← neg_one_smul ℝ (mpullback I' I u form.1), integralTopForm_smul]
  ring

/-- **The Wirtinger inequality for maps from a closed surface.** For a compatible pair, the
symplectic area `∫_C u^* form` of a `C¹` map from a compact surface, oriented so that the frames
`(e, j e)` are positive, is at most its energy. -/
theorem Compatible.integralTopForm_mpullback_le_energy (hcompat : form.Compatible J)
    (ho : ∀ c (b : Basis (Fin 2) ℝ (TangentSpace I' c)), b 1 = j c (b 0) →
      b.orientation = o.orientationAt c)
    (hu : ContMDiff I' I 1 u) :
    integralTopForm o (mpullback I' I u form.1) ≤ form.energy J j o u := by
  rw [← sub_nonneg, energy_sub_integralTopForm_mpullback hu]
  refine integralTopForm_nonneg o fun c b hb ↦ j.apply_basis_nonneg_of_forall_nonneg (ho c)
    (fun e ↦ ?_) b hb
  rw [Pi.add_apply, Pi.neg_apply, ContinuousAlternatingMap.add_apply,
    ContinuousAlternatingMap.neg_apply, ← sub_eq_add_neg, sub_nonneg]
  exact hcompat.mpullback_apply_frame_le_energyForm_apply_frame c e

/-- **The equality case of the Wirtinger inequality.** For a compatible pair, a `C¹` map from a
compact surface, oriented so that the frames `(e, j e)` are positive, has energy equal to its
symplectic area exactly when it is pseudoholomorphic. -/
theorem Compatible.energy_eq_integralTopForm_mpullback_iff (hcompat : form.Compatible J)
    (ho : ∀ c (b : Basis (Fin 2) ℝ (TangentSpace I' c)), b 1 = j c (b 0) →
      b.orientation = o.orientationAt c)
    (hu : ContMDiff I' I 1 u) :
    form.energy J j o u = integralTopForm o (mpullback I' I u form.1) ↔
      ∀ c, IsPseudoholomorphicAt j J u c := by
  refine ⟨fun h c ↦ isPseudoholomorphicAt_iff_mfderiv.2
    ⟨(hu c).mdifferentiableAt one_ne_zero, fun e ↦ ?_⟩, energy_eq_integralTopForm_mpullback⟩
  by_contra hne
  -- Away from the Cauchy–Riemann equation the energy form exceeds `u^* form` on some frame, so
  -- the energy exceeds the area.
  have hnn (c : C) (e : TangentSpace I' c) :
      0 ≤ (form.energyForm J j u + -mpullback I' I u form.1) c ![e, j c e] := by
    rw [Pi.add_apply, Pi.neg_apply, ContinuousAlternatingMap.add_apply,
      ContinuousAlternatingMap.neg_apply, ← sub_eq_add_neg, sub_nonneg]
    exact hcompat.mpullback_apply_frame_le_energyForm_apply_frame c e
  have hpos : 0 < (form.energyForm J j u + -mpullback I' I u form.1) c ![e, j c e] := by
    refine (hnn c e).lt_of_ne fun h0 ↦
      hne ((hcompat.energyForm_apply_frame_eq_mpullback_apply_frame_iff c e).1 ?_)
    rw [Pi.add_apply, Pi.neg_apply, ContinuousAlternatingMap.add_apply,
      ContinuousAlternatingMap.neg_apply, ← sub_eq_add_neg] at h0
    linarith
  have hpb : IsSmoothForm I' 0 (mpullback I' I u form.1) :=
    ((SmoothForm.isSmoothForm form).of_le (by simp)).mpullback (by simpa using hu)
  have := j.integralTopForm_pos_of_forall_nonneg ho ((isSmoothForm_energyForm hu).add hpb.neg)
    (isClosed_tsupport _).isCompact hnn hpos
  rw [← energy_sub_integralTopForm_mpullback hu, h, sub_self] at this
  exact this.false

/-- **Zero energy.** Under tameness, a `C¹` map from a compact surface, oriented so that the frames
`(e, j e)` are positive, has zero energy exactly when its differential vanishes everywhere. -/
theorem Tames.energy_eq_zero_iff (htame : form.Tames J)
    (ho : ∀ c (b : Basis (Fin 2) ℝ (TangentSpace I' c)), b 1 = j c (b 0) →
      b.orientation = o.orientationAt c)
    (hu : ContMDiff I' I 1 u) :
    form.energy J j o u = 0 ↔ ∀ c, mfderiv I' I u c = 0 := by
  refine ⟨fun h c ↦ ?_, fun h ↦ ?_⟩
  · by_contra hne
    obtain ⟨e, he⟩ := DFunLike.ne_iff.1 hne
    have := j.integralTopForm_pos_of_forall_nonneg ho (isSmoothForm_energyForm hu)
      (isClosed_tsupport _).isCompact (htame.energyForm_apply_frame_nonneg (u := u))
      (htame.energyForm_apply_frame_pos he)
    rw [← energy_def, h] at this
    exact this.false
  · rw [energy, show form.energyForm J j u = 0 from funext fun c ↦ ?_, integralTopForm_zero]
    ext v
    rw [show v = ![v 0, v 1] from (FinVec.etaExpand_eq v).symm, energyForm_apply, h c]
    simp

/-- **Zero energy forces constancy.** Under tameness, a `C¹` map of zero energy from a compact
connected surface, oriented so that the frames `(e, j e)` are positive, is constant. -/
theorem Tames.apply_eq_of_energy_eq_zero [PreconnectedSpace C] (htame : form.Tames J)
    (ho : ∀ c (b : Basis (Fin 2) ℝ (TangentSpace I' c)), b 1 = j c (b 0) →
      b.orientation = o.orientationAt c)
    (hu : ContMDiff I' I 1 u) (h : form.energy J j o u = 0) (c c' : C) : u c = u c' :=
  (hu.mdifferentiable one_ne_zero).apply_eq_of_mfderiv_eq_zero
    ((htame.energy_eq_zero_iff ho hu).1 h) c c'

end Compact

/-! ### Changes of domain -/

section Reparametrization

variable {H'' : Type*} [TopologicalSpace H''] {I'' : ModelWithCorners ℝ E' H''} {C' : Type*}
  [TopologicalSpace C'] [ChartedSpace H'' C'] [IsManifold I'' ∞ C']
  {j' : SmoothAlmostComplexStructure I'' C'} {o' : Manifold.Orientation I'' C' (Fin 2)}

omit [FiniteDimensional ℝ E'] in
/-- **Naturality of the energy form.** If `φ` is pseudoholomorphic at `c'` and `u` is
differentiable at `φ c'`, the energy form of `u ∘ φ` at `c'` is the pullback by `φ` of the
energy form of `u`. -/
theorem energyForm_comp_apply {φ : C' → C} {c' : C'} (hφ : IsPseudoholomorphicAt j' j φ c')
    (hu : MDifferentiableAt I' I u (φ c')) :
    form.energyForm J j' (u ∘ φ) c' = mpullback I'' I' φ (form.energyForm J j u) c' := by
  ext v
  rw [show v = ![v 0, v 1] from (FinVec.etaExpand_eq v).symm, energyForm_apply,
    mpullback_apply_pair, energyForm_apply, mfderiv_comp c' hu hφ.mdifferentiableAt]
  simp only [ContinuousLinearMap.comp_apply, hφ.mfderiv_apply_commute, Function.comp_apply]

/-- **Conformal invariance of energy.** Let `Φ` be a pseudoholomorphic `C^n` diffeomorphism,
`n ≠ 0`, between surfaces oriented so that their frames `(e, j e)` are positive. Then for every
differentiable map `u`, the energy of `u ∘ Φ` is the energy of `u`. -/
theorem energy_comp_diffeomorph
    (ho' : ∀ c (b : Basis (Fin 2) ℝ (TangentSpace I'' c)), b 1 = j' c (b 0) →
      b.orientation = o'.orientationAt c)
    (ho : ∀ c (b : Basis (Fin 2) ℝ (TangentSpace I' c)), b 1 = j c (b 0) →
      b.orientation = o.orientationAt c)
    {n : WithTop ℕ∞} (Φ : C' ≃ₘ^n⟮I'', I'⟯ C) (hn : n ≠ 0)
    (hΦ : ∀ c', IsPseudoholomorphicAt j' j Φ c') (hu : MDifferentiable I' I u) :
    form.energy J j' o' (u ∘ Φ) = form.energy J j o u := by
  -- The derivative of `Φ` is an isomorphism of nonzero planes, so it is nonzero.
  have mfderiv_ne_zero (c' : C') : mfderiv I'' I' Φ c' ≠ 0 := by
    obtain ⟨v, hv⟩ := (finrank_pos_iff_exists_ne_zero (R := ℝ) (M := TangentSpace I'' c')).1
      (by simp [o'.finrank_tangentSpace_eq c'])
    have hev := (Φ.mfderivToContinuousLinearEquiv hn c').map_ne_zero_iff.2 hv
    have key : Φ.mfderivToContinuousLinearEquiv hn c' v = mfderiv I'' I' Φ c' v := by
      rw [← Diffeomorph.mfderivToContinuousLinearEquiv_coe Φ hn]
      rfl
    exact fun h ↦ hev (key.trans (by rw [h]; rfl))
  rw [energy, show form.energyForm J j' (u ∘ Φ) =
      mpullback I'' I' Φ (form.energyForm J j u) from
    funext fun c' ↦ energyForm_comp_apply (hΦ c') (hu _)]
  exact Φ.toHomeomorph.isOpenEmbedding.integralTopForm_mpullback_of_isOrientationPreservingAt
    (fun c' ↦ (hΦ c').isOrientationPreservingAt (ho' c') (ho (Φ c')) (mfderiv_ne_zero c'))
    (by simp)

/-- **Degree scaling of energy.** Let `u` be a smooth pseudoholomorphic map from a compact
connected boundaryless surface `C`, and `φ : C' → C` a proper smooth pseudoholomorphic map from a
boundaryless surface. Then the energy of `u ∘ φ` is the degree of `φ` times the energy of
`u`. -/
theorem energy_comp_eq_degree_mul [BoundarylessManifold I'' C'] [T2Space C']
    [BoundarylessManifold I' C] [T2Space C] [CompactSpace C] [ConnectedSpace C] {φ : C' → C}
    (hφ : ContMDiff I'' I' ∞ φ) (hφp : IsProperMap φ)
    (hφhol : ∀ c', IsPseudoholomorphicAt j' j φ c')
    (hu : ContMDiff I' I ∞ u) (hhol : ∀ c, IsPseudoholomorphicAt j J u c) :
    form.energy J j' o' (u ∘ φ) = degree o' o φ * form.energy J j o u := by
  rw [energy_eq_integralTopForm_mpullback fun c' ↦ (hhol (φ c')).comp (hφhol c'),
    energy_eq_integralTopForm_mpullback hhol,
    mpullback_comp (hφ.mdifferentiable (by simp)) (hu.mdifferentiable (by simp))]
  exact integralTopForm_mpullback_eq_degree_mul o' o hφ hφp
    ((SmoothForm.isSmoothForm form).mpullback (by simpa using hu)) (isClosed_tsupport _).isCompact

end Reparametrization

end SmoothTwoForm

end TauCeti
