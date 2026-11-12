/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Distribution.TestFunction
public import Mathlib.Analysis.InnerProductSpace.Laplacian
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import TauCeti.Analysis.Distribution.TestFunction.LineDeriv
import TauCeti.Analysis.Distribution.TestFunction.LinearEquiv
import TauCeti.Analysis.InnerProductSpace.Harmonic.Weyl
import TauCeti.Analysis.InnerProductSpace.Laplacian.Basic
import TauCeti.Analysis.Sobolev.WeakDeriv.Basic
import TauCeti.MeasureTheory.Function.LocallyIntegrable
import TauCeti.MeasureTheory.Measure.Lebesgue.Complex

/-!
# Reflecting the weak Laplace equation across the real axis

Let `R` be a continuous real-linear map of a real normed space `V` (in the application,
`R = conj` on `ℂⁿ`), and let `ξ f g : ℂ → V` be given on the upper half of a conjugation-invariant
open set `Ω`. The reflection of `ξ` twisted by `R` is `ξ` above the real axis and
`z ↦ R (ξ (conj z))` below it (`TauCeti.twistedReflection`). Reflect `ξ` and `f` this way, and `g`
with `-R`, because `g` pairs with the derivative `∂ₜ` in the odd variable `t = im z`.

The main theorem identifies when the reflected triple satisfies the weak divergence-form Laplace
equation `Δξ = ∂ₛ f + ∂ₜ g` on all of `Ω`, in the test-function form

`∀ φ : 𝓓(Ω, ℝ), ∫ Δφ • ξ = -∫ (∂ₛφ • f + ∂ₜφ • g)`.

Splitting a test function into its even and odd parts in `t`, the lower half-plane is moved onto
the upper one by the measure preserving map `conj`, under which `Δφ` and `∂ₛφ` keep their parity
and `∂ₜφ` changes it. The doubled identity therefore holds if and only if

* the identity for `ξ + Rξ`, `f + Rf`, `g + Rg` holds on the upper half-plane against every test
  function even in `t`, and
* the identity for `ξ - Rξ`, `f - Rf`, `g - Rg` holds there against every test function odd in
  `t`.

When `R` is an involution these are the identities for the components `(1 ± R) / 2` of the data.
This is the order-zero reflection step of McDuff–Salamon, Lemma B.4.6, at the level of the weak
Laplace equation; it needs no hypothesis on `R`.

## Main definitions

* `TauCeti.twistedReflection`: the reflection of a function across the real axis twisted by `R`.

## Main results

* `TauCeti.locallyIntegrableOn_twistedReflection`: the reflection of a function locally integrable
  up to the real axis is locally integrable on the doubled domain.
* `TauCeti.forall_integral_laplacian_smul_twistedReflection_eq_iff`: the reflected triple solves
  the weak Laplace equation on `Ω` if and only if the even and odd half-plane identities hold.
* `TauCeti.integral_laplacian_smul_twistedReflection_eq`: the direction used for regularity up to
  the boundary.

## Checks

* `TauCeti.integral_laplacian_smul_twistedReflection_conjCLE_id_eq_zero`: reflecting the solution
  `z` of the real boundary problem with `R = conj` gives `z` again, which solves the doubled
  equation.
* `TauCeti.exists_integral_laplacian_smul_twistedReflection_id_ne_zero`: the even reflection
  `s + i |t|` (that is, `R = id`) does not.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.4.
-/

public section

noncomputable section

open Complex MeasureTheory Set TopologicalSpace Filter InnerProductSpace LineDeriv
open scoped ComplexConjugate Distributions Laplacian Topology

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The reflection of `ξ : ℂ → V` across the real axis twisted by `R`: it is `ξ z` for
`0 < im z`, `R (ξ (conj z))` for `im z < 0`, and `0` on the real axis, a null set. -/
def twistedReflection (R : V →L[ℝ] V) (ξ : ℂ → V) (z : ℂ) : V :=
  {w : ℂ | 0 < w.im}.indicator ξ z + R ({w : ℂ | 0 < w.im}.indicator ξ (conj z))

variable {R : V →L[ℝ] V} {ξ f g : ℂ → V} {z : ℂ}

/-- Above the real axis the twisted reflection of `ξ` is `ξ`. -/
@[simp]
theorem twistedReflection_of_pos (hz : 0 < z.im) : twistedReflection R ξ z = ξ z := by
  have hz' : conj z ∉ {w : ℂ | 0 < w.im} := by simpa using hz.le
  have hz'' : z ∈ {w : ℂ | 0 < w.im} := mem_ofPred.2 hz
  rw [twistedReflection, indicator_of_mem hz'', indicator_of_notMem hz', map_zero, add_zero]

/-- Below the real axis the twisted reflection of `ξ` is `R` applied to `ξ` at the mirror
point. -/
@[simp]
theorem twistedReflection_of_neg (hz : z.im < 0) :
    twistedReflection R ξ z = R (ξ (conj z)) := by
  have hz' : z ∉ {w : ℂ | 0 < w.im} := not_lt.2 hz.le
  have hz'' : conj z ∈ {w : ℂ | 0 < w.im} := by simpa using hz
  rw [twistedReflection, indicator_of_notMem hz', indicator_of_mem hz'', zero_add]

/-- On the real axis the twisted reflection of `ξ` is `0`. -/
@[simp]
theorem twistedReflection_of_im_eq_zero (hz : z.im = 0) : twistedReflection R ξ z = 0 := by
  have hz' : z ∉ {w : ℂ | 0 < w.im} := by simp [hz]
  have hz'' : conj z ∉ {w : ℂ | 0 < w.im} := by simp [hz]
  rw [twistedReflection, indicator_of_notMem hz', indicator_of_notMem hz'', map_zero, add_zero]

/-! ### Local integrability -/

/-- The open upper half-plane `{z | 0 < im z}`. -/
private abbrev upper : Set ℂ := {z : ℂ | 0 < z.im}

private theorem measurableSet_upper : MeasurableSet upper :=
  measurableSet_lt measurable_const Complex.measurable_im

/-- **Local integrability of the twisted reflection.** If `ξ` is locally integrable on `s` up to
the real axis, its twisted reflection is locally integrable on the conjugation-invariant set
`s`. -/
theorem locallyIntegrableOn_twistedReflection {s : Set ℂ} (hs : ∀ z ∈ s, conj z ∈ s)
    (R : V →L[ℝ] V) (hξ : LocallyIntegrableOn ξ (s ∩ {z | 0 ≤ z.im})) :
    LocallyIntegrableOn (twistedReflection R ξ) s := by
  have h := locallyIntegrableOn_indicator_setOf_pos_im hξ
  have hc : LocallyIntegrableOn (fun z ↦ upper.indicator ξ (conj z)) s := by
    simpa only [conjCLE_apply] using h.comp_continuousLinearEquiv_of_mapsTo conjCLE
      (fun z hz ↦ by simpa only [conjCLE_apply] using hs z hz)
  exact h.add (R.locallyIntegrableOn_comp hc)

/-! ### The doubled weak Laplace equation -/

variable {Ω : Opens ℂ}

/-- The integrand `Δφ • a + (∂ₛφ • b + ∂ₜφ • c)` of the weak divergence-form Laplace equation
`Δa = ∂ₛ b + ∂ₜ c` against the test function `φ`. -/
private def lapIntegrand (φ : ℂ → ℝ) (a b c : ℂ → V) (z : ℂ) : V :=
  Δ φ z • a z + (fderiv ℝ φ z 1 • b z + fderiv ℝ φ z I • c z)

private theorem integrable_rhs (φ : 𝓓(Ω, ℝ)) {b c : ℂ → V} (hb : LocallyIntegrableOn b Ω)
    (hc : LocallyIntegrableOn c Ω) :
    Integrable fun z ↦ fderiv ℝ (φ : ℂ → ℝ) z 1 • b z + fderiv ℝ (φ : ℂ → ℝ) z I • c z := by
  have hd (z v : ℂ) := (φ.contDiff.differentiable (by simp) z).lineDeriv_eq_fderiv (v := v)
  have h1 := integrable_lineDeriv_smul_of_locallyIntegrableOn hb φ 1
  have h2 := integrable_lineDeriv_smul_of_locallyIntegrableOn hc φ I
  simp only [hd] at h1 h2
  exact h1.add h2

private theorem integrable_lapIntegrand (φ : 𝓓(Ω, ℝ)) {a b c : ℂ → V}
    (ha : LocallyIntegrableOn a Ω) (hb : LocallyIntegrableOn b Ω)
    (hc : LocallyIntegrableOn c Ω) : Integrable (lapIntegrand (φ : ℂ → ℝ) a b c) :=
  (φ.integrable_laplacian_smul ha).add (integrable_rhs φ hb hc)

/-- The weak identity `∫ Δφ • a = -∫ (∂ₛφ • b + ∂ₜφ • c)` says that the integrand `lapIntegrand`
has integral zero. -/
private theorem integral_eq_neg_iff (φ : 𝓓(Ω, ℝ)) {a b c : ℂ → V}
    (ha : LocallyIntegrableOn a Ω) (hb : LocallyIntegrableOn b Ω)
    (hc : LocallyIntegrableOn c Ω) :
    (∫ z, Δ (φ : ℂ → ℝ) z • a z =
      -∫ z, (fderiv ℝ (φ : ℂ → ℝ) z 1 • b z + fderiv ℝ (φ : ℂ → ℝ) z I • c z)) ↔
      ∫ z, lapIntegrand (φ : ℂ → ℝ) a b c z = 0 := by
  unfold lapIntegrand
  rw [integral_add (φ.integrable_laplacian_smul ha) (integrable_rhs φ hb hc),
    eq_neg_iff_add_eq_zero]

/-- The weak identity on the upper half-plane is the whole-plane identity for the data cut off to
the upper half-plane. -/
private theorem setIntegral_eq_neg_iff (φ : 𝓓(Ω, ℝ)) (a b c : ℂ → V) :
    (∫ z in upper, Δ (φ : ℂ → ℝ) z • a z =
      -∫ z in upper, (fderiv ℝ (φ : ℂ → ℝ) z 1 • b z + fderiv ℝ (φ : ℂ → ℝ) z I • c z)) ↔
    ∫ z, Δ (φ : ℂ → ℝ) z • upper.indicator a z =
      -∫ z, (fderiv ℝ (φ : ℂ → ℝ) z 1 • upper.indicator b z +
        fderiv ℝ (φ : ℂ → ℝ) z I • upper.indicator c z) := by
  rw [← integral_indicator measurableSet_upper, ← integral_indicator measurableSet_upper,
    indicator_smul, indicator_add, indicator_smul, indicator_smul]

/-- The integral of `lapIntegrand` is additive in the test function. -/
private theorem integral_lapIntegrand_add (φ ψ : 𝓓(Ω, ℝ)) {a b c : ℂ → V}
    (ha : LocallyIntegrableOn a Ω) (hb : LocallyIntegrableOn b Ω)
    (hc : LocallyIntegrableOn c Ω) :
    ∫ z, lapIntegrand ((φ + ψ : 𝓓(Ω, ℝ)) : ℂ → ℝ) a b c z =
      (∫ z, lapIntegrand (φ : ℂ → ℝ) a b c z) + ∫ z, lapIntegrand (ψ : ℂ → ℝ) a b c z := by
  refine (integral_congr_ae (Eventually.of_forall fun z ↦ ?_)).trans
    (integral_add (integrable_lapIntegrand φ ha hb hc) (integrable_lapIntegrand ψ ha hb hc))
  have hΔ : Δ ((φ + ψ : 𝓓(Ω, ℝ)) : ℂ → ℝ) z = Δ (φ : ℂ → ℝ) z + Δ (ψ : ℂ → ℝ) z := by
    rw [← TestFunction.laplacianCLM_apply, map_add, FunLike.coe_add, Pi.add_apply,
      TestFunction.laplacianCLM_apply, TestFunction.laplacianCLM_apply]
  have hd : fderiv ℝ ((φ + ψ : 𝓓(Ω, ℝ)) : ℂ → ℝ) z =
      fderiv ℝ (φ : ℂ → ℝ) z + fderiv ℝ (ψ : ℂ → ℝ) z := by
    rw [FunLike.coe_add]
    exact fderiv_add (φ.contDiff.differentiable (by simp) z)
      (ψ.contDiff.differentiable (by simp) z)
  simp only [lapIntegrand]
  rw [hΔ, hd]
  simp only [FunLike.coe_add, Pi.add_apply, add_smul]
  abel

/-- The integral of `lapIntegrand` is additive in the data. -/
private theorem integral_lapIntegrand_add_data (φ : 𝓓(Ω, ℝ)) {a b c a' b' c' : ℂ → V}
    (ha : LocallyIntegrableOn a Ω) (hb : LocallyIntegrableOn b Ω)
    (hc : LocallyIntegrableOn c Ω) (ha' : LocallyIntegrableOn a' Ω)
    (hb' : LocallyIntegrableOn b' Ω) (hc' : LocallyIntegrableOn c' Ω) :
    ∫ z, lapIntegrand (φ : ℂ → ℝ) (a + a') (b + b') (c + c') z =
      (∫ z, lapIntegrand (φ : ℂ → ℝ) a b c z) + ∫ z, lapIntegrand (φ : ℂ → ℝ) a' b' c' z := by
  refine (integral_congr_ae (Eventually.of_forall fun z ↦ ?_)).trans
    (integral_add (integrable_lapIntegrand φ ha hb hc) (integrable_lapIntegrand φ ha' hb' hc'))
  simp only [lapIntegrand, Pi.add_apply, smul_add]
  abel

private theorem mapsTo_conjLIE (hΩ : ∀ z ∈ Ω, conj z ∈ Ω) :
    MapsTo conjLIE.toContinuousLinearEquiv Ω Ω := fun z hz ↦ by
  simpa only [LinearIsometryEquiv.coe_toContinuousLinearEquiv, conjLIE_apply, SetLike.mem_coe]
    using hΩ z hz

/-- The test function `z ↦ φ (conj z)` on a conjugation-invariant open set. -/
private def conjTest (hΩ : ∀ z ∈ Ω, conj z ∈ Ω) (φ : 𝓓(Ω, ℝ)) : 𝓓(Ω, ℝ) :=
  conjLIE.toContinuousLinearEquiv.transportTestFunction (mapsTo_conjLIE hΩ) φ

private theorem conjTest_apply (hΩ : ∀ z ∈ Ω, conj z ∈ Ω) (φ : 𝓓(Ω, ℝ)) (z : ℂ) :
    conjTest hΩ φ z = φ (conj z) := by
  simp only [conjTest, ContinuousLinearEquiv.transportTestFunction_apply,
    LinearIsometryEquiv.coe_symm_toContinuousLinearEquiv, conjLIE_symm, conjLIE_apply]

private theorem coe_conjTest (hΩ : ∀ z ∈ Ω, conj z ∈ Ω) (φ : 𝓓(Ω, ℝ)) :
    (conjTest hΩ φ : ℂ → ℝ) = (φ : ℂ → ℝ) ∘ conjLIE := by
  ext z
  simp [conjTest_apply]

private theorem laplacian_conjTest (hΩ : ∀ z ∈ Ω, conj z ∈ Ω) (φ : 𝓓(Ω, ℝ)) (z : ℂ) :
    Δ (conjTest hΩ φ : ℂ → ℝ) z = Δ (φ : ℂ → ℝ) (conj z) := by
  rw [coe_conjTest, laplacian_comp_linearIsometryEquiv_right, Function.comp_apply, conjLIE_apply]

private theorem fderiv_conjTest (hΩ : ∀ z ∈ Ω, conj z ∈ Ω) (φ : 𝓓(Ω, ℝ)) (z v : ℂ) :
    fderiv ℝ (conjTest hΩ φ : ℂ → ℝ) z v = fderiv ℝ (φ : ℂ → ℝ) (conj z) (conj v) := by
  simp only [conjTest, ContinuousLinearEquiv.fderiv_transportTestFunction,
    ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_symm_toContinuousLinearEquiv, conjLIE_symm, conjLIE_apply]

/-- **The reflection formula.** The weak Laplace integrand of the reflected data against `φ`
integrates to the half-plane integrand of the data against `φ`, plus that of `R` applied to the
data against `φ ∘ conj`. -/
private theorem integral_lapIntegrand_twistedReflection (hΩ : ∀ z ∈ Ω, conj z ∈ Ω)
    (R : V →L[ℝ] V) (φ : 𝓓(Ω, ℝ))
    (hξ : LocallyIntegrableOn ξ ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}))
    (hf : LocallyIntegrableOn f ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}))
    (hg : LocallyIntegrableOn g ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im})) :
    ∫ z, lapIntegrand (φ : ℂ → ℝ) (twistedReflection R ξ) (twistedReflection R f)
        (twistedReflection (-R) g) z =
      (∫ z, lapIntegrand (φ : ℂ → ℝ) (upper.indicator ξ) (upper.indicator f)
          (upper.indicator g) z) +
        ∫ z, lapIntegrand (conjTest hΩ φ : ℂ → ℝ) (fun w ↦ R (upper.indicator ξ w))
          (fun w ↦ R (upper.indicator f w)) (fun w ↦ R (upper.indicator g w)) z := by
  have hξ' := locallyIntegrableOn_indicator_setOf_pos_im hξ
  have hf' := locallyIntegrableOn_indicator_setOf_pos_im hf
  have hg' := locallyIntegrableOn_indicator_setOf_pos_im hg
  set J := lapIntegrand (conjTest hΩ φ : ℂ → ℝ) (fun w ↦ R (upper.indicator ξ w))
    (fun w ↦ R (upper.indicator f w)) (fun w ↦ R (upper.indicator g w))
  have hJ : Integrable J :=
    integrable_lapIntegrand _ (R.locallyIntegrableOn_comp hξ')
      (R.locallyIntegrableOn_comp hf') (R.locallyIntegrableOn_comp hg')
  have hpt (z : ℂ) : lapIntegrand (φ : ℂ → ℝ) (twistedReflection R ξ) (twistedReflection R f)
      (twistedReflection (-R) g) z =
      lapIntegrand (φ : ℂ → ℝ) (upper.indicator ξ) (upper.indicator f)
        (upper.indicator g) z + J (conjLIE z) := by
    have h1 : conj (1 : ℂ) = 1 := by simp
    have hI : conj I = -I := by simp
    simp only [J, lapIntegrand, laplacian_conjTest, fderiv_conjTest, conjLIE_apply,
      RCLike.conj_conj, h1, hI, map_neg, twistedReflection, neg_apply,
      smul_add, smul_neg, neg_smul]
    abel
  have hJc : Integrable fun z ↦ J (conjLIE z) := (integrable_comp conjLIE J).2 hJ
  rw [integral_congr_ae (Eventually.of_forall hpt),
    integral_add (integrable_lapIntegrand φ hξ' hf' hg') hJc, integral_comp conjLIE J]

/-- **Reflecting the weak divergence-form Laplace equation across the real axis.** Let `Ω` be
a conjugation-invariant open set, `R` a continuous linear map of `V`, and `ξ`, `f`, `g` locally
integrable on `Ω` up to the real axis. Reflect `ξ` and `f` by `R` and `g` by `-R`
(`twistedReflection`). The reflected triple solves `Δξ = ∂ₛ f + ∂ₜ g` weakly on `Ω` if and only
if, on the upper half-plane, `ξ + Rξ`, `f + Rf`, `g + Rg` satisfy the weak identity against every
test function even in `t = im z`, and `ξ - Rξ`, `f - Rf`, `g - Rg` satisfy it against every test
function odd in `t`. For an involution `R` these are the identities for the components
`(1 ± R) / 2` of the data. -/
theorem forall_integral_laplacian_smul_twistedReflection_eq_iff (hΩ : ∀ z ∈ Ω, conj z ∈ Ω)
    (R : V →L[ℝ] V) (hξ : LocallyIntegrableOn ξ ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}))
    (hf : LocallyIntegrableOn f ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}))
    (hg : LocallyIntegrableOn g ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im})) :
    (∀ φ : 𝓓(Ω, ℝ), ∫ z, Δ (φ : ℂ → ℝ) z • twistedReflection R ξ z =
      -∫ z, (fderiv ℝ (φ : ℂ → ℝ) z 1 • twistedReflection R f z +
        fderiv ℝ (φ : ℂ → ℝ) z I • twistedReflection (-R) g z)) ↔
    (∀ φ : 𝓓(Ω, ℝ), (∀ z, φ (conj z) = φ z) →
      ∫ z in {z : ℂ | 0 < z.im}, Δ (φ : ℂ → ℝ) z • (ξ z + R (ξ z)) =
        -∫ z in {z : ℂ | 0 < z.im}, (fderiv ℝ (φ : ℂ → ℝ) z 1 • (f z + R (f z)) +
          fderiv ℝ (φ : ℂ → ℝ) z I • (g z + R (g z)))) ∧
    (∀ φ : 𝓓(Ω, ℝ), (∀ z, φ (conj z) = -φ z) →
      ∫ z in {z : ℂ | 0 < z.im}, Δ (φ : ℂ → ℝ) z • (ξ z - R (ξ z)) =
        -∫ z in {z : ℂ | 0 < z.im}, (fderiv ℝ (φ : ℂ → ℝ) z 1 • (f z - R (f z)) +
          fderiv ℝ (φ : ℂ → ℝ) z I • (g z - R (g z)))) := by
  have hξ' := locallyIntegrableOn_indicator_setOf_pos_im hξ
  have hf' := locallyIntegrableOn_indicator_setOf_pos_im hf
  have hg' := locallyIntegrableOn_indicator_setOf_pos_im hg
  have hRξ : LocallyIntegrableOn (fun z ↦ R (upper.indicator ξ z)) Ω :=
    R.locallyIntegrableOn_comp hξ'
  have hRf : LocallyIntegrableOn (fun z ↦ R (upper.indicator f z)) Ω :=
    R.locallyIntegrableOn_comp hf'
  have hRg : LocallyIntegrableOn (fun z ↦ R (upper.indicator g z)) Ω :=
    R.locallyIntegrableOn_comp hg'
  have hξr := locallyIntegrableOn_twistedReflection hΩ R hξ
  have hfr := locallyIntegrableOn_twistedReflection hΩ R hf
  have hgr := locallyIntegrableOn_twistedReflection hΩ (-R) hg
  -- The indicator of `ξ ± Rξ` is `ξ⁺ ± Rξ⁺`, where `ξ⁺` is `ξ` cut off to the upper half-plane.
  have hind (s : ℝ) (u : ℂ → V) : upper.indicator (fun z ↦ u z + s • R (u z)) =
      upper.indicator u + s • fun z ↦ R (upper.indicator u z) := by
    rw [indicator_add, indicator_const_smul, ← Function.comp_def R u,
      indicator_comp_of_zero (map_zero R)]
    ext z
    simp only [Pi.add_apply, Pi.smul_apply, Function.comp_apply]
  have hplus (u : ℂ → V) : upper.indicator (fun z ↦ u z + R (u z)) =
      upper.indicator u + fun z ↦ R (upper.indicator u z) := by
    simpa using hind 1 u
  have hminus (u : ℂ → V) : upper.indicator (fun z ↦ u z - R (u z)) =
      upper.indicator u + -fun z ↦ R (upper.indicator u z) := by
    simpa [sub_eq_add_neg] using hind (-1) u
  -- The half-plane identities, as vanishing of the integral of `lapIntegrand`.
  have heven (φ : 𝓓(Ω, ℝ)) :
      (∫ z in upper, Δ (φ : ℂ → ℝ) z • (ξ z + R (ξ z)) =
        -∫ z in upper, (fderiv ℝ (φ : ℂ → ℝ) z 1 • (f z + R (f z)) +
          fderiv ℝ (φ : ℂ → ℝ) z I • (g z + R (g z)))) ↔
      (∫ z, lapIntegrand (φ : ℂ → ℝ) (upper.indicator ξ) (upper.indicator f)
          (upper.indicator g) z) +
        ∫ z, lapIntegrand (φ : ℂ → ℝ) (fun w ↦ R (upper.indicator ξ w))
          (fun w ↦ R (upper.indicator f w)) (fun w ↦ R (upper.indicator g w)) z = 0 := by
    rw [setIntegral_eq_neg_iff, hplus, hplus, hplus,
      integral_eq_neg_iff φ (hξ'.add hRξ) (hf'.add hRf) (hg'.add hRg),
      integral_lapIntegrand_add_data φ hξ' hf' hg' hRξ hRf hRg]
  have hodd (φ : 𝓓(Ω, ℝ)) :
      (∫ z in upper, Δ (φ : ℂ → ℝ) z • (ξ z - R (ξ z)) =
        -∫ z in upper, (fderiv ℝ (φ : ℂ → ℝ) z 1 • (f z - R (f z)) +
          fderiv ℝ (φ : ℂ → ℝ) z I • (g z - R (g z)))) ↔
      (∫ z, lapIntegrand (φ : ℂ → ℝ) (upper.indicator ξ) (upper.indicator f)
          (upper.indicator g) z) +
        ∫ z, lapIntegrand (-φ : 𝓓(Ω, ℝ)) (fun w ↦ R (upper.indicator ξ w))
          (fun w ↦ R (upper.indicator f w)) (fun w ↦ R (upper.indicator g w)) z = 0 := by
    rw [setIntegral_eq_neg_iff, hminus, hminus, hminus,
      integral_eq_neg_iff φ (hξ'.add hRξ.neg) (hf'.add hRf.neg) (hg'.add hRg.neg),
      integral_lapIntegrand_add_data φ hξ' hf' hg' hRξ.neg hRf.neg hRg.neg]
    have hneg : ∫ z, lapIntegrand ((-φ : 𝓓(Ω, ℝ)) : ℂ → ℝ) (fun w ↦ R (upper.indicator ξ w))
        (fun w ↦ R (upper.indicator f w)) (fun w ↦ R (upper.indicator g w)) z =
        ∫ z, lapIntegrand (φ : ℂ → ℝ) (-fun w ↦ R (upper.indicator ξ w))
          (-fun w ↦ R (upper.indicator f w)) (-fun w ↦ R (upper.indicator g w)) z := by
      congr 1
      ext z
      simp [lapIntegrand, laplacian_neg, fderiv_neg]
    rw [hneg]
  -- The reflection formula for even and odd test functions.
  have hconj_even {φ : 𝓓(Ω, ℝ)} (hφ : ∀ z, φ (conj z) = φ z) : conjTest hΩ φ = φ := by
    ext z; rw [conjTest_apply, hφ]
  have hconj_odd {φ : 𝓓(Ω, ℝ)} (hφ : ∀ z, φ (conj z) = -φ z) : conjTest hΩ φ = -φ := by
    ext z; rw [conjTest_apply, hφ]; simp
  have hrefl (φ : 𝓓(Ω, ℝ)) := integral_lapIntegrand_twistedReflection hΩ R φ hξ hf hg
  constructor
  · intro h
    refine ⟨fun φ hφ ↦ ?_, fun φ hφ ↦ ?_⟩
    · have h' := hrefl φ
      rw [hconj_even hφ] at h'
      rw [heven, ← h', ← integral_eq_neg_iff φ hξr hfr hgr]
      exact h φ
    · have h' := hrefl φ
      rw [hconj_odd hφ] at h'
      rw [hodd, ← h', ← integral_eq_neg_iff φ hξr hfr hgr]
      exact h φ
  · rintro ⟨he, ho⟩ φ
    rw [integral_eq_neg_iff φ hξr hfr hgr]
    -- Split `φ + φ` into the even test function `φ + φ ∘ conj` and the odd one `φ - φ ∘ conj`.
    set ψ := conjTest hΩ φ
    have hE : ∀ z, (φ + ψ) (conj z) = (φ + ψ) z := by
      intro z; simp [ψ, conjTest_apply, add_comm]
    have hO : ∀ z, (φ - ψ) (conj z) = -(φ - ψ) z := by
      intro z; simp [ψ, conjTest_apply]
    have hE' : ∫ z, lapIntegrand ((φ + ψ : 𝓓(Ω, ℝ)) : ℂ → ℝ) (twistedReflection R ξ)
        (twistedReflection R f) (twistedReflection (-R) g) z = 0 := by
      rw [hrefl, hconj_even hE]
      exact (heven (φ + ψ)).1 (he _ hE)
    have hO' : ∫ z, lapIntegrand ((φ - ψ : 𝓓(Ω, ℝ)) : ℂ → ℝ) (twistedReflection R ξ)
        (twistedReflection R f) (twistedReflection (-R) g) z = 0 := by
      rw [hrefl, hconj_odd hO]
      exact (hodd (φ - ψ)).1 (ho _ hO)
    have hsum : (φ + ψ) + (φ - ψ) = φ + φ := by abel
    have h2 := integral_lapIntegrand_add (φ + ψ) (φ - ψ) hξr hfr hgr
    rw [hE', hO', hsum, integral_lapIntegrand_add φ φ hξr hfr hgr, add_zero] at h2
    have key (x : V) (hx : x + x = 0) : x = 0 := by
      rw [← two_smul ℝ x] at hx
      exact (smul_eq_zero.1 hx).resolve_left two_ne_zero
    exact key _ h2

/-- **The doubled weak Laplace equation.** If, on the upper half-plane, `ξ + Rξ`, `f + Rf`,
`g + Rg` satisfy the weak divergence-form Laplace identity against every test function on `Ω`
even in `t = im z`, and `ξ - Rξ`, `f - Rf`, `g - Rg` satisfy it against every test function odd in
`t`, then the reflections of `ξ` and `f` by `R` and of `g` by `-R` solve `Δξ = ∂ₛ f + ∂ₜ g`
weakly on all of the conjugation-invariant open set `Ω`. -/
theorem integral_laplacian_smul_twistedReflection_eq (hΩ : ∀ z ∈ Ω, conj z ∈ Ω)
    (R : V →L[ℝ] V) (hξ : LocallyIntegrableOn ξ ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}))
    (hf : LocallyIntegrableOn f ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}))
    (hg : LocallyIntegrableOn g ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}))
    (heven : ∀ φ : 𝓓(Ω, ℝ), (∀ z, φ (conj z) = φ z) →
      ∫ z in {z : ℂ | 0 < z.im}, Δ (φ : ℂ → ℝ) z • (ξ z + R (ξ z)) =
        -∫ z in {z : ℂ | 0 < z.im}, (fderiv ℝ (φ : ℂ → ℝ) z 1 • (f z + R (f z)) +
          fderiv ℝ (φ : ℂ → ℝ) z I • (g z + R (g z))))
    (hodd : ∀ φ : 𝓓(Ω, ℝ), (∀ z, φ (conj z) = -φ z) →
      ∫ z in {z : ℂ | 0 < z.im}, Δ (φ : ℂ → ℝ) z • (ξ z - R (ξ z)) =
        -∫ z in {z : ℂ | 0 < z.im}, (fderiv ℝ (φ : ℂ → ℝ) z 1 • (f z - R (f z)) +
          fderiv ℝ (φ : ℂ → ℝ) z I • (g z - R (g z))))
    (φ : 𝓓(Ω, ℝ)) :
    ∫ z, Δ (φ : ℂ → ℝ) z • twistedReflection R ξ z =
      -∫ z, (fderiv ℝ (φ : ℂ → ℝ) z 1 • twistedReflection R f z +
        fderiv ℝ (φ : ℂ → ℝ) z I • twistedReflection (-R) g z) :=
  (forall_integral_laplacian_smul_twistedReflection_eq_iff hΩ R hξ hf hg).2 ⟨heven, hodd⟩ φ

/-! ### Checks: the reflection of `z` -/

/-- Off the real axis, the reflection of `z` twisted by `conj` is `z`. -/
theorem twistedReflection_conjCLE_id (hz : z.im ≠ 0) :
    twistedReflection (conjCLE : ℂ →L[ℝ] ℂ) id z = z := by
  rcases hz.lt_or_gt with hz | hz
  · simp [hz]
  · simp [hz]

/-- Off the real axis, the reflection of `z = s + i t` twisted by the identity is the even
reflection `s + i |t|`. -/
theorem twistedReflection_id_id (hz : z.im ≠ 0) :
    twistedReflection (ContinuousLinearMap.id ℝ ℂ) id z = z.re + |z.im| * I := by
  rcases hz.lt_or_gt with hz | hz
  · rw [twistedReflection_of_neg hz, abs_of_neg hz]
    apply Complex.ext <;> simp
  · rw [twistedReflection_of_pos hz, abs_of_pos hz]
    exact (re_add_im z).symm

/-- **Check: the reflection by `conj` of the real-boundary solution `z` solves the doubled
equation.** With `f = g = 0`, the reflection of `z` by `R = conj` is `z` off the real axis, and
`z` is harmonic, so `∫ Δφ • ξ = 0` for every test function `φ` on `Ω`. -/
theorem integral_laplacian_smul_twistedReflection_conjCLE_id_eq_zero (φ : 𝓓(Ω, ℝ)) :
    ∫ z, Δ (φ : ℂ → ℝ) z • twistedReflection (conjCLE : ℂ →L[ℝ] ℂ) id z = 0 := by
  have hae : (fun z ↦ Δ (φ : ℂ → ℝ) z • twistedReflection (conjCLE : ℂ →L[ℝ] ℂ) id z) =ᵐ[volume]
      fun z ↦ Δ (φ : ℂ → ℝ) z • id z := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 (Complex.volume_setOf_im_eq 0)] with z hz
    rw [twistedReflection_conjCLE_id hz, id]
  rw [integral_congr_ae hae]
  have hh : HarmonicOnNhd (id : ℂ → ℂ) Ω := fun x _ ↦ (contDiffAt_id (𝕜 := ℂ)).harmonicAt
  exact (hh.weaklyHarmonicOn (μ := volume)).integral_laplacian_smul_eq_zero φ

/-- **Check: the even reflection `s + i |t|` does not solve the doubled equation.** With
`f = g = 0` and `R = id`, the reflection of `z` is `s + i |t|` off the real axis, which is not
weakly harmonic on `ℂ`: a weakly harmonic function agrees almost everywhere with a harmonic one,
and the continuous function `s + i |t|` would then be smooth, while `|t|` is not differentiable at
`0`. -/
theorem exists_integral_laplacian_smul_twistedReflection_id_ne_zero :
    ∃ φ : 𝓓((⊤ : Opens ℂ), ℝ),
      ∫ z, Δ (φ : ℂ → ℝ) z • twistedReflection (ContinuousLinearMap.id ℝ ℂ) id z ≠ 0 := by
  by_contra! h
  set w : ℂ → ℂ := fun z ↦ z.re + |z.im| * I with hw
  have hwc : Continuous w := by fun_prop
  have hloc : LocallyIntegrableOn (twistedReflection (ContinuousLinearMap.id ℝ ℂ) id)
      (⊤ : Opens ℂ) :=
    locallyIntegrableOn_twistedReflection (by simp) _
      (continuous_id.locallyIntegrable.locallyIntegrableOn _)
  have hharm : WeaklyHarmonicOn volume (⊤ : Opens ℂ)
      (twistedReflection (ContinuousLinearMap.id ℝ ℂ) id) :=
    weaklyHarmonicOn_iff.2 ⟨hloc, h⟩
  have hwae : twistedReflection (ContinuousLinearMap.id ℝ ℂ) id
      =ᵐ[volume.restrict ((⊤ : Opens ℂ) : Set ℂ)] w := by
    rw [Opens.coe_top, Measure.restrict_univ]
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 (Complex.volume_setOf_im_eq 0)] with z hz
    exact twistedReflection_id_id hz
  have hwh : HarmonicOnNhd w (⊤ : Opens ℂ) :=
    (harmonicOnNhd_iff_weaklyHarmonicOn (μ := volume) hwc.continuousOn).2 (hharm.congr_ae hwae)
  have hwd : DifferentiableAt ℝ w 0 := (hwh 0 (by simp)).1.differentiableAt (by norm_num)
  have habs : DifferentiableAt ℝ (fun t : ℝ ↦ (w (t * I)).im) 0 := by
    have hlin : DifferentiableAt ℝ (fun t : ℝ ↦ ofRealCLM t * I) 0 :=
      (ofRealCLM.differentiable.mul_const I) 0
    have hw' : DifferentiableAt ℝ w (ofRealCLM 0 * I) := by simpa using hwd
    simpa only [Function.comp_def, imCLM_apply, ofRealCLM_apply] using
      imCLM.differentiableAt.comp (0 : ℝ) (hw'.comp (0 : ℝ) hlin)
  have hfun : (fun t : ℝ ↦ (w (t * I)).im) = abs := by
    ext t
    simp [hw]
  rw [hfun] at habs
  exact not_differentiableAt_abs_zero habs

end TauCeti
