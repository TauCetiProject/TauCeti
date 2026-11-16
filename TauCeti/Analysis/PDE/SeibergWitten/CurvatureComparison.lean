/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.SeibergWitten.CutoffCurrent
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import TauCeti.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import TauCeti.Analysis.Calculus.DifferentialForm.Basic
import TauCeti.Analysis.Calculus.DifferentialForm.Integral
import TauCeti.Analysis.Calculus.DifferentialForm.Regularity
import TauCeti.Analysis.Calculus.DifferentialForm.Wedge
import TauCeti.LinearAlgebra.Basis.Fin
import TauCeti.MeasureTheory.Integral.Bochner.CauchySchwarz

/-!
# The cutoff current and the curvature current against test forms

Let `(a, α)` be an abelian Higgs pair with `a = i b`, on a finite-dimensional real normed space
`E` of dimension `2 + n` carrying an almost complex structure `J`. Its cutoff current
`Θ = i F_a + d(χ(|α|²) τ)` (`TauCeti.SeibergWitten.cutoffCurrent`) differs from the curvature
current `i F_a = -db` by the exact form `d(χ(|α|²) τ)`. In Taubes's passage from Seiberg–Witten
solutions to pseudoholomorphic curves, `Θ / 2π` is the current that converges to the limiting
curve, and this file shows that `Θ` and `i F_a` have the same pairings with test forms up to an
error controlled by two integrals: that of `|1 - |α|²|` and that of `|∂bar_a α|`.

For a compactly supported test form `ζ` of degree `n`, integration by parts gives

`∫ (Θ - i F_a) ∧ ζ = ∫ χ(|α|²) τ ∧ dζ`

(`TauCeti.SeibergWitten.integral_cutoffCurrent_add_extDeriv_wedge_eq`). By the
modulus-potential decomposition `χ(|α|²) τ = d^c_J H(|α|²) + E`
(`TauCeti.SeibergWitten.cutoffPhaseForm_eq_twistedDifferential_add`), a second integration by
parts moves the derivative in `d^c_J H(|α|²)` onto `dζ`
(`TauCeti.AlmostComplexStructure.integral_twistedDifferential_wedge_eq`). The pointwise bounds
`|H(s)| ≤ |s - 1| / c` and `|E| ≤ (2 / √c) |∂bar_a α|`, for a cutoff `χ` vanishing below `c`,
then give

`|∫ (Θ - i F_a) ∧ ζ| ≤ C (A₂ / c ∫_K |1 - |α|²| + A₁ / √c ∫_K |∂bar_a α|)`

(`TauCeti.SeibergWitten.exists_abs_integral_cutoffCurrent_add_extDeriv_wedge_le`). Here `K` is a
compact set containing the support of `ζ`, `A₁` bounds `|dζ|` and `A₂` bounds the derivative of
`dζ`, so `A₁` and `A₂` are controlled by the `C²` norm of `ζ`. The constant `C` depends only on
`J` and on the basis used to integrate top-degree forms. For a family of fields with
`∫_K |1 - |α|²| = O(h²)` and `∫_K |∂bar_a α| = O(h)`, the right side is `O(h)` for each fixed
test form, so `Θ / 2π` and `i F_a / 2π` have the same weak limits as `h → 0`. For
large-parameter Seiberg–Witten solutions, with `h = (2r)^(-1/2)`, these are the scales of the
coarse estimates on `1 - |α|²` and `∂bar_a α`.

**Normal dilations.** Near a pseudoholomorphic curve, Taubes's analysis dilates the normal
directions by a factor `a → 0` with `h / a → 0`. In a flat chart `ℂ_base × ℂ_normal` whose complex
structure preserves the two factors this is the linear map `L(z, w) = (z, a w)`, which commutes
with `J` and has `|det L| = a²`, and `‖L‖ ≤ 1` for `a ≤ 1` in the product norm.
The comparison holds for the pullbacks `L^* Θ` and `L^* i F_a` along any invertible linear map `L`
commuting with `J`: the currents and `∂bar_a α` of the pulled-back pair `(L^* b, α ∘ L)` are the
pullbacks of those of `(b, α)` (`TauCeti.SeibergWitten.cutoffCurrent_comp`,
`TauCeti.SeibergWitten.covariantDBar_comp`), and changing variables along `L` gives

`|∫ L^* (Θ - i F_a) ∧ ζ| ≤ C (A₂ / c |det L|⁻¹ ∫_{L K} |1 - |α|²| +`
`  A₁ / √c ‖L‖ |det L|⁻¹ ∫_{L K} |∂bar_a α|)`

(`exists_abs_integral_cutoffCurrent_add_extDeriv_compContinuousLinearMap_wedge_le`), with the
same constant `C`. The integrals are over the image `L K`, a tube of volume
`|det L| Vol K`; by the Cauchy–Schwarz inequality on it, the bounds `∫_{L K} |1 - |α|²| ≤ D₁` and
`∫_{L K} |∂bar_a α|² ≤ D₂` give the bound
`C (A₂ / c D₁ / |det L| + A₁ / √c ‖L‖ √(D₂ Vol K / |det L|))`
(`exists_abs_integral_cutoffCurrent_add_extDeriv_compContinuousLinearMap_wedge_le_sqrt`).
For the normal dilation and `D₁, D₂ = O(h²)` this is `O((h / a)² + h / a)`, with the `C²` norm of
`ζ` entering through `A₂` and its `C¹` norm through `A₁`. Hence along a family with
`h² / |det L| → 0`, in particular `h / a → 0`, the pairings of `L^* Θ` and of `L^* i F_a` with each
fixed test form differ by a quantity tending to zero
(`tendsto_integral_cutoffCurrent_add_extDeriv_compContinuousLinearMap_wedge`):
the dilated cutoff current and the dilated curvature current of the original connection have the
same weak limits.

The statements are for linear changes of coordinates, as in a flat chart. Near a curve in a
curved four-manifold the dilation is taken along a foliation by pseudoholomorphic normal discs,
which is not linear, and the comparison there is not treated here.

## References

* C. H. Taubes, *SW ⇒ Gr: from the Seiberg–Witten equations to pseudo-holomorphic curves*,
  J. Amer. Math. Soc. 9 (1996), 845–918.
* C. H. Taubes, *Seiberg–Witten invariants and pseudo-holomorphic subvarieties for self-dual,
  harmonic 2-forms*, Geom. Topol. 3 (1999), 167–210.
-/

public section

noncomputable section

open ContinuousAlternatingMap Complex Filter MeasureTheory Set
open scoped Topology

namespace TauCeti.SeibergWitten

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {n : ℕ}
  {α : E → ℂ} {b : E → E [⋀^Fin 1]→L[ℝ] ℝ} {χ : ℝ → ℝ} {ζ : E → E [⋀^Fin n]→L[ℝ] ℝ}

omit [FiniteDimensional ℝ E] in
/-- **The cutoff current against a test form.** For a compactly supported C1 test form `ζ` of
degree `n` on a space of dimension `2 + n`, the pairing of `Θ - i F_a = Θ + db` with `ζ` is the
pairing of the cutoff phase form `χ(|α|²) τ` with `dζ`. Top-degree coefficients are taken on a
basis `e` and integrated against its Haar measure. -/
theorem integral_cutoffCurrent_add_extDeriv_wedge_eq (e : Module.Basis (Fin (2 + n)) ℝ E)
    (hα : ContDiff ℝ 2 α) (hb : ContDiff ℝ 1 b) (hχ : ContDiff ℝ 1 χ) (hχ₀ : χ =ᶠ[𝓝 0] 0)
    (hζ : ContDiff ℝ 1 ζ) (hc : HasCompactSupport ζ) :
    ∫ x, wedge (cutoffCurrent χ b α x + extDeriv b x) (ζ x) e ∂e.addHaar =
      ∫ x, wedge (cutoffPhaseForm χ b α x) (extDeriv ζ x) (e ∘ Fin.cast (by omega)) ∂e.addHaar := by
  have h := e.integral_extDeriv_wedge_eq_integral_wedge_extDeriv (by omega)
    (contDiff_cutoffPhaseForm hα hb hχ hχ₀) hζ hc
  -- The index cast `1 + 1 + n = 2 + n` is the identity.
  have e₁ : ⇑e ∘ Fin.cast (show 1 + 1 + n = 2 + n by omega) = ⇑e := rfl
  rw [e₁, pow_one, neg_neg, one_mul] at h
  simpa only [cutoffCurrent_apply, sub_add_cancel] using h

variable (J : AlmostComplexStructure E)

/-- **Comparison of the cutoff current with the curvature current.** There is a constant `C`,
depending only on `J` and the basis `e`, with the following property. Let `χ` vanish below
`c > 0` with `|χ| ≤ 1`, and let `ζ` be a `C²` test form of degree `n` supported in a compact set
`K`, with `|dζ| ≤ A₁` and `|D(dζ)| ≤ A₂`. Then

`|∫ (Θ - i F_a) ∧ ζ| ≤ C (A₂ / c ∫_K |1 - |α|²| + A₁ / √c ∫_K |∂bar_a α|)`,

where `Θ - i F_a = Θ + db`. Top-degree coefficients are taken on `e` and integrated against its
Haar measure. -/
theorem exists_abs_integral_cutoffCurrent_add_extDeriv_wedge_le
    (e : Module.Basis (Fin (2 + n)) ℝ E) :
    ∃ C, 0 ≤ C ∧ ∀ ⦃χ : ℝ → ℝ⦄ ⦃b : E → E [⋀^Fin 1]→L[ℝ] ℝ⦄ ⦃α : E → ℂ⦄
      ⦃ζ : E → E [⋀^Fin n]→L[ℝ] ℝ⦄ ⦃K : Set E⦄ ⦃c A₁ A₂ : ℝ⦄, 0 < c →
      (∀ t < c, χ t = 0) → (∀ t, |χ t| ≤ 1) → ContDiff ℝ 1 χ → ContDiff ℝ 2 α →
      ContDiff ℝ 1 b → ContDiff ℝ 2 ζ → IsCompact K → tsupport ζ ⊆ K →
      (∀ x, ‖extDeriv ζ x‖ ≤ A₁) → (∀ x, ‖fderiv ℝ (extDeriv ζ) x‖ ≤ A₂) →
      |∫ x, wedge (cutoffCurrent χ b α x + extDeriv b x) (ζ x) e ∂e.addHaar| ≤
        C * (A₂ / c * ∫ x in K, |normSq (α x) - 1| ∂e.addHaar +
          A₁ / √c * ∫ x in K, ‖covariantDBar J b α x‖ ∂e.addHaar) := by
  let e₁ := e.reindex (finCongr (by omega : 2 + n = 1 + (n + 1)))
  obtain ⟨C₁, hC₁, hIA⟩ := J.exists_abs_integral_twistedDifferential_wedge_le e₁
  obtain ⟨C₂, _, hIB⟩ := e₁.exists_abs_integral_wedge_le
  refine ⟨max C₁ (2 * C₂), by positivity, ?_⟩
  intro χ b α ζ K c A₁ A₂ hc hχc hχ₁ hχ hα hb hζ hK hζK hA₁ hA₂
  have hχ₀ : χ =ᶠ[𝓝 0] 0 := (eventually_lt_nhds hc).mono hχc
  have hcζ : HasCompactSupport ζ := hK.of_isClosed_subset (isClosed_tsupport ζ) hζK
  set η := extDeriv ζ
  have hη : ContDiff ℝ 1 η := contDiff_extDeriv hζ (by norm_num)
  have hcη : HasCompactSupport η := hcζ.extDeriv
  -- Outside `K` the form `dζ` vanishes.
  have hηK : tsupport η ⊆ K := tsupport_extDeriv_subset.trans hζK
  have hη0 (x) (hx : x ∉ K) : η x = 0 := image_eq_zero_of_notMem_tsupport fun h ↦ hx (hηK h)
  have hA₁0 : 0 ≤ A₁ := (norm_nonneg _).trans (hA₁ 0)
  have hA₂0 : 0 ≤ A₂ := (ContinuousLinearMap.opNorm_nonneg _).trans (hA₂ 0)
  -- The modulus potential `H(|α|²)` and the decomposition `χ(|α|²) τ = d^c_J H(|α|²) + E`.
  set H := modulusPotential χ
  have hH (t : ℝ) : HasDerivAt H (χ t / t) t := hasDerivAt_modulusPotential hχ.continuous hχ₀ t
  have hs : ContDiff ℝ 1 fun y ↦ normSq (α y) := by
    simp_rw [normSq_eq_norm_sq]
    exact (contDiff_norm_sq ℝ).comp (hα.of_le one_le_two)
  have hg : ContDiff ℝ 1 fun y ↦ H (normSq (α y)) :=
    (contDiff_modulusPotential hχ.continuous hχ₀).comp hs
  have hdec (x : E) : cutoffPhaseForm χ b α x =
      J.twistedDifferential (fun y ↦ H (normSq (α y))) x + cutoffDBarForm J χ b α x :=
    cutoffPhaseForm_eq_twistedDifferential_add J (hH _) (hχc 0 hc)
      (hα.differentiable two_ne_zero x)
  -- Reduce to the pairing of the cutoff phase form with `dζ`, evaluated on `e₁`.
  have he₁ : ⇑e ∘ Fin.cast (show 1 + (n + 1) = 2 + n by omega) = ⇑e₁ :=
    (e.reindex_finCongr_comp_cast _ rfl).symm
  have hμ : e₁.addHaar = e.addHaar := Module.Basis.addHaar_reindex _ _
  rw [integral_cutoffCurrent_add_extDeriv_wedge_eq e hα hb hχ hχ₀ (hζ.of_le one_le_two) hcζ, he₁,
    ← hμ]
  set g := fun y ↦ H (normSq (α y))
  set A := fun x ↦ wedge (J.twistedDifferential g x) (η x) e₁
  set B := fun x ↦ wedge (cutoffDBarForm J χ b α x) (η x) e₁
  have hcw (φ : E → E [⋀^Fin 1]→L[ℝ] ℝ) : HasCompactSupport fun x ↦ wedge (φ x) (η x) e₁ :=
    hcη.wedge_left.comp_left (g := fun ω : E [⋀^Fin (1 + (n + 1))]→L[ℝ] ℝ ↦ ω e₁) rfl
  have hA : Integrable A e₁.addHaar :=
    (((J.contDiff_twistedDifferential (n := 0) hg (by simp)).wedge
      (hη.of_le zero_le_one)).continuous.eval_const _).integrable_of_hasCompactSupport
      (hcw _)
  have hT : Integrable (fun x ↦ wedge (cutoffPhaseForm χ b α x) (η x) e₁) e₁.addHaar :=
    (((contDiff_cutoffPhaseForm (n := 0) (by simpa using hα.of_le one_le_two)
      (hb.of_le zero_le_one) (hχ.of_le zero_le_one) hχ₀).wedge
      (hη.of_le zero_le_one)).continuous.eval_const _).integrable_of_hasCompactSupport
      (hcw _)
  have hsplit (x : E) : wedge (cutoffPhaseForm χ b α x) (η x) e₁ = A x + B x := by
    simp only [A, B, hdec, wedge_add_left, ContinuousAlternatingMap.add_apply]
  have hB : Integrable B e₁.addHaar :=
    (hT.sub hA).congr (Eventually.of_forall fun x ↦ by
      rw [Pi.sub_apply, hsplit, add_sub_cancel_left])
  rw [integral_congr_ae (Eventually.of_forall hsplit), integral_add hA hB]
  -- The `d^c_J H(|α|²)` term, by `|H(s)| ≤ |s - 1| / c`.
  have hA' : |∫ x, A x ∂e₁.addHaar| ≤
      C₁ * (A₂ / c * ∫ x in K, |normSq (α x) - 1| ∂e₁.addHaar) :=
    calc |∫ x, A x ∂e₁.addHaar|
        ≤ C₁ * (A₂ * ∫ x in K, |normSq (α x) - 1| / c ∂e₁.addHaar) :=
          hIA hg hη hK hηK
            (((hs.continuous.sub continuous_const).abs.div_const c).continuousOn
              |>.integrableOn_compact hK)
            (fun x _ ↦ abs_modulusPotential_le hc (fun t _ ht ↦ hχc t ht) hχ₁ (normSq_nonneg _))
            hA₂
      _ = _ := by
          rw [integral_div]
          ring
  -- The correction term `E = 2 χ(|α|²) Re (α⁻¹ ∂bar_a α) ∘ J`, by `|E| ≤ (2 / √c) |∂bar_a α|`.
  have hB' : |∫ x, B x ∂e₁.addHaar| ≤
      2 * C₂ * (A₁ / √c * ∫ x in K, ‖covariantDBar J b α x‖ ∂e₁.addHaar) :=
    calc |∫ x, B x ∂e₁.addHaar|
        ≤ C₂ * (A₁ * ∫ x in K, 2 / √c * ‖covariantDBar J b α x‖ ∂e₁.addHaar) :=
          hIB hK.measurableSet hη0
            ((continuous_const.mul (continuous_covariantDBar J (hα.of_le one_le_two)
              hb.continuous).norm).continuousOn.integrableOn_compact hK)
            (fun x _ ↦ norm_cutoffDBarForm_le J hc (fun t _ ht ↦ hχc t ht) hχ₁ b α x) hA₁
      _ = _ := by
          rw [integral_const_mul]
          ring
  calc |∫ x, A x ∂e₁.addHaar + ∫ x, B x ∂e₁.addHaar|
      ≤ |∫ x, A x ∂e₁.addHaar| + |∫ x, B x ∂e₁.addHaar| := abs_add_le _ _
    _ ≤ C₁ * (A₂ / c * ∫ x in K, |normSq (α x) - 1| ∂e₁.addHaar) +
        2 * C₂ * (A₁ / √c * ∫ x in K, ‖covariantDBar J b α x‖ ∂e₁.addHaar) := add_le_add hA' hB'
    _ ≤ _ := by
        rw [mul_add]
        gcongr
        exacts [le_max_left _ _, le_max_right _ _]

/-! ### Linear changes of coordinates and normal dilations -/

/-- **Comparison of the currents after a linear change of coordinates.** Let `C` be the constant of
`TauCeti.SeibergWitten.exists_abs_integral_cutoffCurrent_add_extDeriv_wedge_le` for `J` and `e`, and
let `L` be an invertible linear map commuting with `J`. For `χ`, `ζ`, `K`, `c`, `A₁`, `A₂` as there,
the pullback `L^* (Θ - i F_a)` of the difference of the two currents of `(b, α)` satisfies

`|∫ L^* (Θ - i F_a) ∧ ζ| ≤ C (A₂ / c |det L|⁻¹ ∫_{L K} |1 - |α|²| +`
`  A₁ / √c ‖L‖ |det L|⁻¹ ∫_{L K} |∂bar_a α|)`.

The integrals on the right are over the image `L K` of the support of the test form, in the
original coordinates. -/
theorem exists_abs_integral_cutoffCurrent_add_extDeriv_compContinuousLinearMap_wedge_le
    (e : Module.Basis (Fin (2 + n)) ℝ E) :
    ∃ C, 0 ≤ C ∧ ∀ ⦃χ : ℝ → ℝ⦄ ⦃b : E → E [⋀^Fin 1]→L[ℝ] ℝ⦄ ⦃α : E → ℂ⦄
      ⦃ζ : E → E [⋀^Fin n]→L[ℝ] ℝ⦄ ⦃K : Set E⦄ ⦃c A₁ A₂ : ℝ⦄ ⦃L : E →L[ℝ] E⦄, 0 < c →
      (∀ t < c, χ t = 0) → (∀ t, |χ t| ≤ 1) → ContDiff ℝ 1 χ → ContDiff ℝ 2 α →
      ContDiff ℝ 1 b → ContDiff ℝ 2 ζ → IsCompact K → tsupport ζ ⊆ K →
      (∀ x, ‖extDeriv ζ x‖ ≤ A₁) → (∀ x, ‖fderiv ℝ (extDeriv ζ) x‖ ≤ A₂) → L.det ≠ 0 →
      (∀ v, L (J v) = J (L v)) →
      |∫ x, wedge ((cutoffCurrent χ b α (L x) + extDeriv b (L x)).compContinuousLinearMap L)
          (ζ x) e ∂e.addHaar| ≤
        C * (A₂ / c * |L.det|⁻¹ * ∫ y in L '' K, |normSq (α y) - 1| ∂e.addHaar +
          A₁ / √c * ‖L‖ * |L.det|⁻¹ * ∫ y in L '' K, ‖covariantDBar J b α y‖ ∂e.addHaar) := by
  obtain ⟨C, hC, hcmp⟩ := exists_abs_integral_cutoffCurrent_add_extDeriv_wedge_le J e
  refine ⟨C, hC, ?_⟩
  intro χ b α ζ K c A₁ A₂ L hc hχc hχ₁ hχ hα hb hζ hK hζK hA₁ hA₂ hL hLJ
  have hχ₀ : χ =ᶠ[𝓝 0] 0 := (eventually_lt_nhds hc).mono hχc
  -- The pulled-back pair `(L^* b, α ∘ L)`.
  set b' : E → E [⋀^Fin 1]→L[ℝ] ℝ := fun z ↦ (b (L z)).compContinuousLinearMap L
  have hα' : ContDiff ℝ 2 (α ∘ L) := hα.comp L.contDiff
  have hb' : ContDiff ℝ 1 b' := by
    have h := contDiffOn_pullback_continuousLinearMap (t := univ) hb.contDiffOn L
    rwa [preimage_univ, contDiffOn_univ] at h
  have hfd : (fun z ↦ (b (L z)).compContinuousLinearMap (fderiv ℝ L z)) = b' := by
    simp [b']
  -- The pulled-back currents are the currents of the pulled-back pair.
  have hpt (x : E) : (cutoffCurrent χ b α (L x) + extDeriv b (L x)).compContinuousLinearMap L =
      cutoffCurrent χ b' (α ∘ L) x + extDeriv b' x := by
    have h := cutoffCurrent_comp (y := x) hα.contDiffAt hb.contDiffAt hχ hχ₀ L.contDiff.contDiffAt
    rw [hfd, L.fderiv] at h
    rw [h, L.extDeriv_pullback ((hb.differentiable one_ne_zero) (L x))]
    ext v
    simp
  simp_rw [hpt]
  refine (hcmp hc hχc hχ₁ hχ hα' hb' hζ hK hζK hA₁ hA₂).trans ?_
  -- Change variables along `L` in the two integrals.
  have hinj : Function.Injective L :=
    ((Module.End.isUnit_iff _).1 ((LinearMap.isUnit_iff_isUnit_det _).2 hL.isUnit)).1
  have hcv (g : E → ℝ) :
      ∫ x in K, g (L x) ∂e.addHaar = |L.det|⁻¹ * ∫ y in L '' K, g y ∂e.addHaar := by
    rw [integral_image_eq_integral_abs_det_fderiv_smul e.addHaar hK.measurableSet
      (fun x _ ↦ L.hasFDerivAt.hasFDerivWithinAt) hinj.injOn]
    simp_rw [smul_eq_mul]
    rw [integral_const_mul, inv_mul_cancel_left₀ (abs_ne_zero.2 hL)]
  have hdbar : ∫ x in K, ‖covariantDBar J b' (α ∘ L) x‖ ∂e.addHaar ≤
      ‖L‖ * (|L.det|⁻¹ * ∫ y in L '' K, ‖covariantDBar J b α y‖ ∂e.addHaar) := by
    rw [← hcv, ← integral_const_mul]
    refine setIntegral_mono_on
      ((continuous_covariantDBar J (hα'.of_le one_le_two) hb'.continuous).norm.continuousOn
        |>.integrableOn_compact hK)
      ((continuous_const.mul ((continuous_covariantDBar J (hα.of_le one_le_two)
        hb.continuous).comp L.continuous).norm).continuousOn.integrableOn_compact hK)
      hK.measurableSet fun x _ ↦ ?_
    have h := covariantDBar_comp J J (b := b) ((hα.differentiable two_ne_zero) (L x))
      L.differentiableAt (by simpa using hLJ)
    rw [hfd, L.fderiv] at h
    rw [h, mul_comm]
    exact ContinuousLinearMap.opNorm_comp_le _ _
  have hX : ∫ x in K, |normSq ((α ∘ L) x) - 1| ∂e.addHaar =
      |L.det|⁻¹ * ∫ y in L '' K, |normSq (α y) - 1| ∂e.addHaar :=
    hcv fun y ↦ |normSq (α y) - 1|
  rw [hX]
  have hAc : 0 ≤ A₁ / √c := div_nonneg ((norm_nonneg _).trans (hA₁ 0)) (Real.sqrt_nonneg _)
  refine (mul_le_mul_of_nonneg_left
    (add_le_add le_rfl (mul_le_mul_of_nonneg_left hdbar hAc)) hC).trans_eq ?_
  ring

/-- **Comparison of the currents after a linear change of coordinates, in terms of `L¹` and `L²`
bounds.** With `C` as in
`exists_abs_integral_cutoffCurrent_add_extDeriv_compContinuousLinearMap_wedge_le`, if on the
image `L K` of the support of the test form `∫_{L K} |1 - |α|²| ≤ D₁` and
`∫_{L K} |∂bar_a α|² ≤ D₂`, then

`|∫ L^* (Θ - i F_a) ∧ ζ| ≤ C (A₂ / c D₁ / |det L| + A₁ / √c ‖L‖ √(D₂ Vol K / |det L|))`.

For the dilation `(z, w) ↦ (z, a w)` of the normal factor of `ℂ_base × ℂ_normal` one has
`|det L| = a²` and `‖L‖ ≤ 1` for `a ≤ 1` in the product norm, and Taubes's bounds
`D₁, D₂ = O(h²)` on the tube make the right side `O((h / a)²) + O(h / a)`. -/
theorem exists_abs_integral_cutoffCurrent_add_extDeriv_compContinuousLinearMap_wedge_le_sqrt
    (e : Module.Basis (Fin (2 + n)) ℝ E) :
    ∃ C, 0 ≤ C ∧ ∀ ⦃χ : ℝ → ℝ⦄ ⦃b : E → E [⋀^Fin 1]→L[ℝ] ℝ⦄ ⦃α : E → ℂ⦄
      ⦃ζ : E → E [⋀^Fin n]→L[ℝ] ℝ⦄ ⦃K : Set E⦄ ⦃c A₁ A₂ D₁ D₂ : ℝ⦄ ⦃L : E →L[ℝ] E⦄, 0 < c →
      (∀ t < c, χ t = 0) → (∀ t, |χ t| ≤ 1) → ContDiff ℝ 1 χ → ContDiff ℝ 2 α →
      ContDiff ℝ 1 b → ContDiff ℝ 2 ζ → IsCompact K → tsupport ζ ⊆ K →
      (∀ x, ‖extDeriv ζ x‖ ≤ A₁) → (∀ x, ‖fderiv ℝ (extDeriv ζ) x‖ ≤ A₂) → L.det ≠ 0 →
      (∀ v, L (J v) = J (L v)) →
      ∫ y in L '' K, |normSq (α y) - 1| ∂e.addHaar ≤ D₁ →
      ∫ y in L '' K, ‖covariantDBar J b α y‖ ^ 2 ∂e.addHaar ≤ D₂ →
      |∫ x, wedge ((cutoffCurrent χ b α (L x) + extDeriv b (L x)).compContinuousLinearMap L)
          (ζ x) e ∂e.addHaar| ≤
        C * (A₂ / c * (D₁ / |L.det|) +
          A₁ / √c * ‖L‖ * √(D₂ * e.addHaar.real K / |L.det|)) := by
  obtain ⟨C, hC, hcmp⟩ :=
    exists_abs_integral_cutoffCurrent_add_extDeriv_compContinuousLinearMap_wedge_le J e
  refine ⟨C, hC, ?_⟩
  intro χ b α ζ K c A₁ A₂ D₁ D₂ L hc hχc hχ₁ hχ hα hb hζ hK hζK hA₁ hA₂ hL hLJ hD₁ hD₂
  refine (hcmp hc hχc hχ₁ hχ hα hb hζ hK hζK hA₁ hA₂ hL hLJ).trans ?_
  set μ := e.addHaar
  set S := L '' K
  have hd : 0 < |L.det| := abs_pos.2 hL
  have hS : IsCompact S := hK.image L.continuous
  -- The Cauchy–Schwarz inequality on `S`, whose volume is `|det L| Vol K`.
  have hf : Continuous fun y ↦ ‖covariantDBar J b α y‖ :=
    (continuous_covariantDBar J (hα.of_le one_le_two) hb.continuous).norm
  have : IsFiniteMeasure (μ.restrict S) := isFiniteMeasure_restrict.2 hS.measure_lt_top.ne
  obtain ⟨B, hB⟩ := hS.exists_bound_of_continuousOn hf.continuousOn
  have hm : MemLp (fun y ↦ ‖covariantDBar J b α y‖) 2 (μ.restrict S) :=
    MemLp.of_bound hf.aestronglyMeasurable B (ae_restrict_of_forall_mem hS.measurableSet hB)
  have hCS := sq_integral_mul_le_integral_sq_mul_integral_sq hm (memLp_const (1 : ℝ))
  simp only [mul_one, one_pow, integral_const, smul_eq_mul, measureReal_restrict_apply_univ]
    at hCS
  have hvol : μ.real S = |L.det| * μ.real K := by
    simp [S, measureReal_def, Measure.addHaar_image_continuousLinearMap, ENNReal.toReal_mul,
      abs_nonneg]
  have hY : ∫ y in S, ‖covariantDBar J b α y‖ ∂μ ≤ √(D₂ * (|L.det| * μ.real K)) := by
    refine (le_abs_self _).trans (Real.abs_le_sqrt (hCS.trans ?_))
    rw [← hvol]
    exact mul_le_mul_of_nonneg_right hD₂ measureReal_nonneg
  have hA₁0 : 0 ≤ A₁ := (norm_nonneg _).trans (hA₁ 0)
  have hA₂0 : 0 ≤ A₂ := (ContinuousLinearMap.opNorm_nonneg _).trans (hA₂ 0)
  -- `|det L|⁻¹ √(D₂ |det L| Vol K) = √(D₂ Vol K / |det L|)`.
  have hsq : |L.det|⁻¹ * √(D₂ * (|L.det| * μ.real K)) = √(D₂ * μ.real K / |L.det|) := by
    rw [show D₂ * (|L.det| * μ.real K) = (D₂ * μ.real K / |L.det|) * |L.det| ^ 2 by
      field_simp, Real.sqrt_mul' _ (sq_nonneg _), Real.sqrt_sq hd.le]
    field_simp
  calc C * (A₂ / c * |L.det|⁻¹ * ∫ y in S, |normSq (α y) - 1| ∂μ +
        A₁ / √c * ‖L‖ * |L.det|⁻¹ * ∫ y in S, ‖covariantDBar J b α y‖ ∂μ)
      ≤ C * (A₂ / c * |L.det|⁻¹ * D₁ +
        A₁ / √c * ‖L‖ * |L.det|⁻¹ * √(D₂ * (|L.det| * μ.real K))) := by gcongr
    _ = _ := by
        rw [mul_assoc (A₁ / √c * ‖L‖), hsq, div_eq_inv_mul D₁, ← mul_assoc]

/-- **The dilated cutoff and curvature currents have the same weak limits.** Let `ζ` be a
compactly supported `C²` test form and `χ` a `C¹` cutoff with `|χ| ≤ 1` vanishing below `c > 0`.
Let `(bᵢ, αᵢ)` be pairs and `Lᵢ` invertible linear maps commuting with `J`, with `‖Lᵢ‖ ≤ B`.
Suppose that on the images `Lᵢ (supp ζ)` the bounds `∫ |1 - |αᵢ|²| ≤ M hᵢ²` and
`∫ |∂bar_a αᵢ|² ≤ M hᵢ²` hold and that `hᵢ² / |det Lᵢ| → 0`. Then
`∫ Lᵢ^* (Θᵢ - i F_{aᵢ}) ∧ ζ → 0`: the pairings of the pullbacks of the cutoff currents and of the
curvature currents with `ζ` differ by a quantity tending to zero. For the dilations
`(z, w) ↦ (z, aᵢ w)` of the normal factor of `ℂ_base × ℂ_normal`, `|det Lᵢ| = aᵢ²` and the
condition is `hᵢ / aᵢ → 0`. -/
theorem tendsto_integral_cutoffCurrent_add_extDeriv_compContinuousLinearMap_wedge
    {ι : Type*} {l : Filter ι} (e : Module.Basis (Fin (2 + n)) ℝ E) {χ : ℝ → ℝ} {c B M : ℝ}
    {ζ : E → E [⋀^Fin n]→L[ℝ] ℝ} {b : ι → E → E [⋀^Fin 1]→L[ℝ] ℝ} {α : ι → E → ℂ}
    {L : ι → E →L[ℝ] E} {h : ι → ℝ} (hc : 0 < c) (hχc : ∀ t < c, χ t = 0)
    (hχ₁ : ∀ t, |χ t| ≤ 1) (hχ : ContDiff ℝ 1 χ) (hζ : ContDiff ℝ 2 ζ) (hcζ : HasCompactSupport ζ)
    (hα : ∀ i, ContDiff ℝ 2 (α i)) (hb : ∀ i, ContDiff ℝ 1 (b i)) (hL : ∀ i, (L i).det ≠ 0)
    (hLJ : ∀ i v, L i (J v) = J (L i v)) (hLB : ∀ i, ‖L i‖ ≤ B)
    (hD₁ : ∀ i, ∫ y in L i '' tsupport ζ, |normSq (α i y) - 1| ∂e.addHaar ≤ M * h i ^ 2)
    (hD₂ : ∀ i, ∫ y in L i '' tsupport ζ, ‖covariantDBar J (b i) (α i) y‖ ^ 2 ∂e.addHaar ≤
      M * h i ^ 2)
    (hh : Tendsto (fun i ↦ h i ^ 2 / |(L i).det|) l (𝓝 0)) :
    Tendsto (fun i ↦ ∫ x, wedge ((cutoffCurrent χ (b i) (α i) (L i x) +
      extDeriv (b i) (L i x)).compContinuousLinearMap (L i)) (ζ x) e ∂e.addHaar) l (𝓝 0) := by
  obtain ⟨C, hC, hcmp⟩ :=
    exists_abs_integral_cutoffCurrent_add_extDeriv_compContinuousLinearMap_wedge_le_sqrt J e
  -- Bounds on `dζ` and its derivative, from compact support.
  have hη : ContDiff ℝ 1 (extDeriv ζ) := contDiff_extDeriv hζ (by norm_num)
  obtain ⟨A₁, hA₁⟩ := (hη.continuous).bounded_above_of_compact_support hcζ.extDeriv
  obtain ⟨A₂, hA₂⟩ := (hη.continuous_fderiv one_ne_zero).bounded_above_of_compact_support
    (hcζ.extDeriv.fderiv (𝕜 := ℝ))
  have hA₁0 : 0 ≤ A₁ := (norm_nonneg _).trans (hA₁ 0)
  set V := e.addHaar.real (tsupport ζ)
  -- The bound of each term tends to zero with `tᵢ = hᵢ² / |det Lᵢ|`.
  have hg : Tendsto (fun i ↦ C * (A₂ / c * (M * (h i ^ 2 / |(L i).det|)) +
      A₁ / √c * B * √(M * V * (h i ^ 2 / |(L i).det|)))) l (𝓝 0) := by
    have h1 := (hh.const_mul M).const_mul (A₂ / c)
    have h2 := (((hh.const_mul (M * V)).sqrt).const_mul (A₁ / √c * B))
    simpa using (h1.add h2).const_mul C
  refine squeeze_zero_norm (fun i ↦ ?_) hg
  rw [Real.norm_eq_abs]
  calc _ ≤ C * (A₂ / c * (M * h i ^ 2 / |(L i).det|) +
        A₁ / √c * ‖L i‖ * √(M * h i ^ 2 * V / |(L i).det|)) :=
        hcmp hc hχc hχ₁ hχ (hα i) (hb i) hζ hcζ.isCompact subset_rfl hA₁ hA₂ (hL i) (hLJ i)
          (hD₁ i) (hD₂ i)
    _ ≤ _ := by
        rw [mul_div_assoc M, show M * h i ^ 2 * V / |(L i).det| =
          M * V * (h i ^ 2 / |(L i).det|) by ring]
        gcongr
        exact hLB i

end TauCeti.SeibergWitten
