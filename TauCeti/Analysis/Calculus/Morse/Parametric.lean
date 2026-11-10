/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Morse.NormalForm
import TauCeti.Analysis.Calculus.InverseFunctionTheorem

/-!
# The parametric Morse lemma in a trivial bundle

A smooth family of functions `f (b, v)` with a critical zero section and a strongly nondegenerate
vertical Hessian admits local coordinates preserving the base parameter. The coordinate change
fixes the zero section and transforms the function into its vertical Hessian quadratic form. Both
the coordinate change and its local inverse are jointly smooth in base and fiber.

The construction follows the operator-square-root proof of the Morse--Palais lemma, as formalized
in `TauCeti.Analysis.Calculus.Morse.NormalForm`. Write `H b` for the vertical Hessian of `f` at
`(b, 0)` and `B (b, v)` for the averaged vertical Hessian
`TauCeti.hessianAverage (fun v ↦ f (b, v)) 0 v`. The **canonical parametric Morse operator**
`R (b, v) = TauCeti.parametricMorseOperator f (b, v)` is the square root near the identity of
`(H b)⁻¹ ∘ B (b, v)`, and the **canonical parametric Morse map**
`TauCeti.parametricMorseMap f` is `(b, v) ↦ (b, R (b, v) v)`. Near a point of the zero section with
invertible vertical Hessian, `R` satisfies
`H b (R w) (R w') = B (b, v) w w'`, so Taylor's formula turns `f (b, v)` into
`f (b, 0) + ½ H b (R v, R v)` along a critical zero section. The map is `C^n` there for a
`C^{n+2}` family and has derivative the identity on the zero section; the inverse function theorem
then makes it a chart (`TauCeti.exists_parametric_morse_chart`).
The Hessian convention is the second derivative itself, so the quadratic formula has a factor
`1 / 2`.

Since it involves no choices, the construction is natural. It depends only on the germ of `f`
along the zero section (`Filter.EventuallyEq.parametricMorseMap`). If `f'` is the same family in
other coordinates, `f' (σ b, T b v) = f (b, v)` near the zero section for a change of parameter `σ`
and a family `T` of linear isomorphisms of the fibres, continuous at the base point, then
the canonical maps correspond: `Φ' (σ b, T b v) = (σ b, T b (Φ (b, v)).2)`
(`TauCeti.eventually_parametricMorseMap_transition`). These are the compatibilities with bundle
transitions under which the local coordinate changes over the trivializations of a vector bundle,
such as the normal bundle of a Morse–Bott critical submanifold, agree near the zero section.

## Main declarations

* `TauCeti.parametricMorseOperator`, `TauCeti.parametricMorseMap`: the canonical operator and
  coordinate change.
* `TauCeti.eventually_contDiffAt_parametricMorseMap`, `TauCeti.hasFDerivAt_parametricMorseMap`:
  their regularity and their derivative on the zero section.
* `TauCeti.eventually_fderiv_fderiv_apply_parametricMorseOperator`: the canonical congruence of
  the averaged vertical Hessian with the vertical Hessian.
* `TauCeti.eventually_eq_add_fderiv_fderiv_parametricMorseMap`: the canonical parametric Morse
  normal form.
* `TauCeti.eventually_parametricMorseOperator_transition`,
  `TauCeti.eventually_parametricMorseMap_transition`: compatibility with changes of
  trivialization.
* `TauCeti.exists_parametric_morse_normal_form`, `TauCeti.exists_parametric_morse_chart`: the
  parametric Morse lemma on a product neighbourhood, and as a local chart.

## References

* R. S. Palais, *The Morse lemma for Banach spaces*, Bull. Amer. Math. Soc. **75** (1969),
  968--971.
* R. S. Palais, *Morse theory on Hilbert manifolds*, Topology **2** (1963), 299--340, Section 2.
* R. Bott, *Nondegenerate critical manifolds*, Annals of Mathematics **60** (1954), 248--261, for
  the normal form along a critical submanifold.
-/

public section

noncomputable section

open Filter Set Topology
open scoped ContDiff

namespace TauCeti

variable {P E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {f : P × E → ℝ} {a : P} {n : ℕ∞}

/-! ### The canonical coordinate change -/

/-- The comparison operator `H⁻¹ ∘ B` whose square root is the canonical parametric Morse
operator. -/
private def morseComparison (f : P × E → ℝ) (z : P × E) : E →L[ℝ] E :=
  (fderiv ℝ (fderiv ℝ fun v ↦ f (z.1, v)) 0).inverse.comp
    (hessianAverage (fun v ↦ f (z.1, v)) 0 z.2)

private theorem morseComparison_zero {b : P}
    (hH : (fderiv ℝ (fderiv ℝ fun v ↦ f (b, v)) 0).IsInvertible) :
    morseComparison f (b, 0) = 1 := by
  rw [morseComparison, hessianAverage_zero, hH.inverse_comp_self, ContinuousLinearMap.one_def]

variable [CompleteSpace E]

/-- The **canonical parametric Morse operator** of a family `f (b, v)` at `z = (b, v)`. Write
`H` for the vertical Hessian of `f` at `(b, 0)` and `B` for the averaged vertical Hessian
`TauCeti.hessianAverage (fun v ↦ f (b, v)) 0 v`, so that `B = H` when `v = 0`. The operator is the
square root near the identity (`TauCeti.sqrtNearOne`) of the comparison operator `H⁻¹ ∘ B`.
Near a point of the zero section with invertible vertical Hessian it conjugates `B` to `H`
(`TauCeti.eventually_fderiv_fderiv_apply_parametricMorseOperator`). -/
def parametricMorseOperator (f : P × E → ℝ) (z : P × E) : E →L[ℝ] E :=
  sqrtNearOne (E →L[ℝ] E)
    ((fderiv ℝ (fderiv ℝ fun v ↦ f (z.1, v)) 0).inverse.comp
      (hessianAverage (fun v ↦ f (z.1, v)) 0 z.2))

/-- The **canonical parametric Morse map** `(b, v) ↦ (b, R (b, v) v)`, where `R` is
`TauCeti.parametricMorseOperator f`. It preserves the parameter and fixes the zero section, and
near a point of a critical zero section with invertible vertical Hessian it carries `f` to its
vertical Hessian quadratic form
(`TauCeti.eventually_eq_add_fderiv_fderiv_parametricMorseMap`). Being given by a formula rather
than by a choice, it is compatible with changes of trivialization
(`TauCeti.eventually_parametricMorseMap_transition`). -/
def parametricMorseMap (f : P × E → ℝ) (z : P × E) : P × E :=
  (z.1, parametricMorseOperator f z z.2)

@[simp]
theorem parametricMorseMap_fst (f : P × E → ℝ) (z : P × E) : (parametricMorseMap f z).1 = z.1 :=
  (rfl)

@[simp]
theorem parametricMorseMap_snd (f : P × E → ℝ) (z : P × E) :
    (parametricMorseMap f z).2 = parametricMorseOperator f z z.2 :=
  (rfl)

/-- The canonical parametric Morse map fixes the zero section. -/
@[simp]
theorem parametricMorseMap_zero (f : P × E → ℝ) (b : P) :
    parametricMorseMap f (b, 0) = (b, 0) := by
  simp [parametricMorseMap]

private theorem parametricMorseOperator_eq (f : P × E → ℝ) (z : P × E) :
    parametricMorseOperator f z = sqrtNearOne (E →L[ℝ] E) (morseComparison f z) :=
  rfl

private theorem parametricMorseOperator_eq_comp (f : P × E → ℝ) :
    parametricMorseOperator f = sqrtNearOne (E →L[ℝ] E) ∘ morseComparison f :=
  rfl

/-- On the zero section, at a point with invertible vertical Hessian, the canonical parametric
Morse operator is the identity. -/
theorem parametricMorseOperator_zero {b : P}
    (hH : (fderiv ℝ (fderiv ℝ fun v ↦ f (b, v)) 0).IsInvertible) :
    parametricMorseOperator f (b, 0) = 1 := by
  rw [parametricMorseOperator_eq, morseComparison_zero hH, sqrtNearOne_one]

variable [NormedAddCommGroup P] [NormedSpace ℝ P]

omit [CompleteSpace E] in
/-- The vertical Hessian of a jointly `C^{n+2}` family is `C^n` in the parameter. -/
private theorem contDiff_fderiv_fderiv_slice (hf : ContDiff ℝ (n + 2) f) :
    ContDiff ℝ n fun b : P ↦ fderiv ℝ (fderiv ℝ fun v ↦ f (b, v)) 0 := by
  have h := (contDiff_hessianAverage_param hf (0 : E)).comp
    (contDiff_id.prodMk contDiff_const : ContDiff ℝ n fun b : P ↦ (b, (0 : E)))
  simpa only [Function.comp_def, id, hessianAverage_zero] using h

private theorem contDiffAt_morseComparison (hf : ContDiff ℝ (n + 2) f) {z : P × E}
    (hz : (fderiv ℝ (fderiv ℝ fun v ↦ f (z.1, v)) 0).IsInvertible) :
    ContDiffAt ℝ n (morseComparison f) z := by
  have hH : ContDiffAt ℝ n (fun z : P × E ↦ fderiv ℝ (fderiv ℝ fun v ↦ f (z.1, v)) 0) z :=
    ((contDiff_fderiv_fderiv_slice hf).comp contDiff_fst).contDiffAt
  have hinv : ContDiffAt ℝ n
      (fun z : P × E ↦ (fderiv ℝ (fderiv ℝ fun v ↦ f (z.1, v)) 0).inverse) z :=
    ContDiffAt.comp (g := ContinuousLinearMap.inverse) z hz.contDiffAt_map_inverse hH
  exact hinv.clm_comp (contDiff_hessianAverage_param hf 0).contDiffAt

/-- Near a point of the zero section with invertible vertical Hessian, so are the vertical
Hessians at the parameters of all nearby points. -/
private theorem eventually_isInvertible_fderiv_fderiv_slice (hf : ContDiff ℝ 2 f)
    (hH : (fderiv ℝ (fderiv ℝ fun v ↦ f (a, v)) 0).IsInvertible) :
    ∀ᶠ z in 𝓝 (a, (0 : E)), (fderiv ℝ (fderiv ℝ fun v ↦ f (z.1, v)) 0).IsInvertible :=
  (continuous_fst.tendsto (a, (0 : E))).eventually <|
    (contDiff_fderiv_fderiv_slice (n := 0) (by simpa using hf)).continuous.continuousAt.eventually
      hH.eventually_nhds

private theorem tendsto_morseComparison (hf : ContDiff ℝ 2 f)
    (hH : (fderiv ℝ (fderiv ℝ fun v ↦ f (a, v)) 0).IsInvertible) :
    Tendsto (morseComparison f) (𝓝 (a, 0)) (𝓝 1) := by
  simpa only [morseComparison_zero hH] using
    (contDiffAt_morseComparison (n := 0) (z := (a, 0)) (by simpa using hf) hH).continuousAt.tendsto

/-- Near a point of the zero section with invertible vertical Hessian, the canonical parametric
Morse operator squares to the comparison operator. -/
private theorem eventually_parametricMorseOperator_mul_self (hf : ContDiff ℝ 2 f)
    (hH : (fderiv ℝ (fderiv ℝ fun v ↦ f (a, v)) 0).IsInvertible) :
    ∀ᶠ z in 𝓝 (a, (0 : E)),
      parametricMorseOperator f z * parametricMorseOperator f z = morseComparison f z := by
  filter_upwards [(tendsto_morseComparison hf hH).eventually eventually_mul_self_sqrtNearOne]
    with z hz
  rw [parametricMorseOperator_eq]
  exact hz

/-- **Regularity of the canonical parametric Morse operator.** For a jointly `C^{n+2}` family,
the canonical parametric Morse operator is `C^n` near every point of the zero section with
invertible vertical Hessian. -/
theorem eventually_contDiffAt_parametricMorseOperator (hf : ContDiff ℝ (n + 2) f)
    (hH : (fderiv ℝ (fderiv ℝ fun v ↦ f (a, v)) 0).IsInvertible) :
    ∀ᶠ z in 𝓝 (a, (0 : E)), ContDiffAt ℝ n (parametricMorseOperator f) z := by
  filter_upwards [eventually_isInvertible_fderiv_fderiv_slice (hf.of_le le_add_self) hH,
    (tendsto_morseComparison (hf.of_le le_add_self) hH).eventually
      analyticAt_sqrtNearOne.eventually_analyticAt] with z hz hza
  rw [parametricMorseOperator_eq_comp]
  exact hza.contDiffAt.comp z (contDiffAt_morseComparison hf hz)

private theorem continuousAt_parametricMorseOperator (hf : ContDiff ℝ 2 f)
    (hH : (fderiv ℝ (fderiv ℝ fun v ↦ f (a, v)) 0).IsInvertible) :
    ContinuousAt (parametricMorseOperator f) (a, 0) :=
  (eventually_contDiffAt_parametricMorseOperator (n := 0) (by simpa using hf) hH).self_of_nhds
    |>.continuousAt

private theorem tendsto_parametricMorseOperator (hf : ContDiff ℝ 2 f)
    (hH : (fderiv ℝ (fderiv ℝ fun v ↦ f (a, v)) 0).IsInvertible) :
    Tendsto (parametricMorseOperator f) (𝓝 (a, 0)) (𝓝 1) := by
  simpa only [parametricMorseOperator_zero hH] using
    (continuousAt_parametricMorseOperator hf hH).tendsto

/-- **Regularity of the canonical parametric Morse map.** For a jointly `C^{n+2}` family, the
canonical parametric Morse map is `C^n` near every point of the zero section with invertible
vertical Hessian. -/
theorem eventually_contDiffAt_parametricMorseMap (hf : ContDiff ℝ (n + 2) f)
    (hH : (fderiv ℝ (fderiv ℝ fun v ↦ f (a, v)) 0).IsInvertible) :
    ∀ᶠ z in 𝓝 (a, (0 : E)), ContDiffAt ℝ n (parametricMorseMap f) z := by
  filter_upwards [eventually_contDiffAt_parametricMorseOperator hf hH] with z hz
  exact contDiffAt_fst.prodMk (hz.clm_apply contDiffAt_snd)

/-- **The canonical congruence.** Near a point of the zero section with invertible vertical
Hessian, the canonical parametric Morse operator `R` of a `C²` family conjugates the averaged
vertical Hessian `B` to the vertical Hessian `H` on the zero section:
`H (R w) (R w') = B w w'`. -/
theorem eventually_fderiv_fderiv_apply_parametricMorseOperator (hf : ContDiff ℝ 2 f)
    (hH : (fderiv ℝ (fderiv ℝ fun v ↦ f (a, v)) 0).IsInvertible) :
    ∀ᶠ z in 𝓝 (a, (0 : E)), ∀ w w',
      fderiv ℝ (fderiv ℝ fun v ↦ f (z.1, v)) 0 (parametricMorseOperator f z w)
          (parametricMorseOperator f z w') =
        hessianAverage (fun v ↦ f (z.1, v)) 0 z.2 w w' := by
  have hslice (b : P) : ContDiff ℝ 2 fun v ↦ f (b, v) := hf.comp (contDiff_const.prodMk contDiff_id)
  -- Write `Hz` for the vertical Hessian at the parameter of `z`, `Bz` for the averaged vertical
  -- Hessian, `R` for the operator and `C = Hz⁻¹ ∘ Bz`, so that `R * R = C` near `(a, 0)`.
  let Hz : P × E → E →L[ℝ] E →L[ℝ] ℝ := fun z ↦ fderiv ℝ (fderiv ℝ fun v ↦ f (z.1, v)) 0
  have hHsymm (z : P × E) (w w' : E) : Hz z w w' = Hz z w' w := by
    simpa only [Hz, hessianAverage_zero] using hessianAverage_symm (hslice z.1) 0 0 w w'
  -- The adjoint of `R` for `Hz` tends to the identity, so it is the square root of the adjoint
  -- of `C`, which is `C` itself: `R` is self-adjoint for `Hz`.
  have hHc : ContinuousAt Hz (a, 0) :=
    ((contDiff_fderiv_fderiv_slice (n := 0) (by simpa using hf)).comp contDiff_fst).continuous
      |>.continuousAt
  have hadj : Tendsto (fun z ↦ (Hz z).bilinAdjoint (sqrtNearOne (E →L[ℝ] E) (morseComparison f z)))
      (𝓝 (a, 0)) (𝓝 1) := by
    have hc : ContinuousAt (fun z ↦ (Hz z).bilinAdjoint (parametricMorseOperator f z)) (a, 0) := by
      simp only [ContinuousLinearMap.bilinAdjoint]
      exact (ContinuousAt.comp (g := ContinuousLinearMap.inverse) (f := Hz) (x := (a, 0))
          (hH.contDiffAt_map_inverse (n := 0)).continuousAt hHc).clm_comp
        ((ContinuousLinearMap.flipₗᵢ ℝ E E ℝ).continuous.continuousAt.comp
          (hHc.clm_comp (continuousAt_parametricMorseOperator hf hH)))
    have h1 : (Hz (a, 0)).bilinAdjoint (parametricMorseOperator f (a, 0)) = 1 := by
      rw [parametricMorseOperator_zero hH, ContinuousLinearMap.bilinAdjoint_one hH (hHsymm (a, 0))]
    have h := hc.tendsto
    rw [h1] at h
    simpa only [parametricMorseOperator_eq] using h
  filter_upwards [eventually_isInvertible_fderiv_fderiv_slice hf hH,
    eventually_parametricMorseOperator_mul_self hf hH,
    eventually_sqrtNearOne_map (tendsto_morseComparison hf hH) hadj
      ((eventually_isInvertible_fderiv_fderiv_slice hf hH).mono fun z hz x ↦
        ContinuousLinearMap.bilinAdjoint_mul hz (hHsymm z) x x)] with z hz hR hRadj w w'
  set R := parametricMorseOperator f z
  have hC (w w' : E) : Hz z (morseComparison f z w) w' = hessianAverage (fun v ↦ f (z.1, v)) 0 z.2
      w w' := by
    simp [morseComparison, Hz, hz.self_apply_inverse]
  -- `C` is self-adjoint for `Hz`, because `Bz` is symmetric.
  have hCadj : (Hz z).bilinAdjoint (morseComparison f z) = morseComparison f z :=
    ContinuousLinearMap.ext fun w ↦ hz.injective <| ContinuousLinearMap.ext fun w' ↦ by
      rw [ContinuousLinearMap.bilinAdjoint_apply_apply hz, hC, hC,
        hessianAverage_symm (hslice z.1)]
  have hRsa : (Hz z).bilinAdjoint R = R := by
    rw [hCadj, ← parametricMorseOperator_eq] at hRadj
    exact hRadj.symm
  calc Hz z (R w) (R w') = Hz z ((Hz z).bilinAdjoint R w) (R w') := by rw [hRsa]
    _ = Hz z (morseComparison f z w') w := by
      rw [ContinuousLinearMap.bilinAdjoint_apply_apply hz, ← mul_apply_eq_comp, hR]
    _ = hessianAverage (fun v ↦ f (z.1, v)) 0 z.2 w w' := by
      rw [hC, hessianAverage_symm (hslice z.1)]

/-- **The canonical parametric Morse normal form.** Near a point `(a, 0)` of a critical zero
section of a `C²` family `f` with invertible vertical Hessian, the canonical parametric Morse map
`Φ` carries `f` to the vertical Hessian quadratic form on the zero section:
`f z = f (z.1, 0) + ½ D²(f (z.1, ·))(0) ((Φ z).2, (Φ z).2)`. -/
theorem eventually_eq_add_fderiv_fderiv_parametricMorseMap (hf : ContDiff ℝ 2 f)
    (hcrit : ∀ᶠ b in 𝓝 a, fderiv ℝ (fun v ↦ f (b, v)) 0 = 0)
    (hH : (fderiv ℝ (fderiv ℝ fun v ↦ f (a, v)) 0).IsInvertible) :
    ∀ᶠ z in 𝓝 (a, (0 : E)), f z = f (z.1, 0) + (2 : ℝ)⁻¹ *
      fderiv ℝ (fderiv ℝ fun v ↦ f (z.1, v)) 0 (parametricMorseMap f z).2
        (parametricMorseMap f z).2 := by
  filter_upwards [eventually_fderiv_fderiv_apply_parametricMorseOperator hf hH,
    (continuous_fst.tendsto (a, (0 : E))).eventually hcrit] with z hz hzcrit
  have hslice : ContDiff ℝ 2 fun v ↦ f (z.1, v) := hf.comp (contDiff_const.prodMk contDiff_id)
  have ht := map_add_eq_add_hessianAverage hslice 0 z.2
  simpa only [zero_add, hzcrit, zero_apply, add_zero, smul_eq_mul, ← hz,
    parametricMorseMap_snd, Prod.mk.eta] using ht

/-- **The derivative of the canonical parametric Morse map.** At a point of the zero section with
invertible vertical Hessian, the canonical parametric Morse map of a jointly `C^{n+2}` family,
`n ≠ 0`, has derivative the identity. -/
theorem hasFDerivAt_parametricMorseMap (hf : ContDiff ℝ (n + 2) f)
    (hH : (fderiv ℝ (fderiv ℝ fun v ↦ f (a, v)) 0).IsInvertible) (hn : n ≠ 0) :
    HasFDerivAt (parametricMorseMap f) (ContinuousLinearMap.id ℝ (P × E)) (a, 0) := by
  have hRa := (eventually_contDiffAt_parametricMorseOperator hf hH).self_of_nhds
  have hd : HasFDerivAt (fun z : P × E ↦ parametricMorseOperator f z z.2)
      ((parametricMorseOperator f (a, 0)).comp (ContinuousLinearMap.snd ℝ P E) +
        (fderiv ℝ (parametricMorseOperator f) (a, 0)).flip 0) (a, 0) :=
    (hRa.differentiableAt (by simpa using hn)).hasFDerivAt.clm_apply hasFDerivAt_snd
  refine (hasFDerivAt_fst.prodMk hd).congr_fderiv ?_
  ext z <;> simp [parametricMorseOperator_zero hH]

/-! ### Compatibility with changes of trivialization -/

section Transition

variable {P' E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [CompleteSpace E']
  {f' : P' × E' → ℝ} {σ : P → P'} {T : P → E ≃L[ℝ] E'}

omit [CompleteSpace E] [NormedSpace ℝ P] [CompleteSpace E'] in
/-- The comparison operators of two families related by a fibrewise linear change of
coordinates `T` over a parameter change `σ`, near the zero section, are conjugate by `T`. -/
private theorem eventually_morseComparison_transition
    (hcomp : ∀ᶠ z in 𝓝 (a, (0 : E)), f' (σ z.1, T z.1 z.2) = f z) :
    ∀ᶠ z in 𝓝 (a, (0 : E)), morseComparison f' (σ z.1, T z.1 z.2) =
      (T z.1).conjContinuousAlgEquiv (morseComparison f z) := by
  obtain ⟨U, V, hU, haU, hV, h0V, hUV⟩ := mem_nhds_prod_iff'.mp hcomp
  obtain ⟨r, hr, hrV⟩ := Metric.isOpen_iff.mp hV 0 h0V
  filter_upwards [prod_mem_nhds (hU.mem_nhds haU) (Metric.ball_mem_nhds (0 : E) hr)] with z hz
  obtain ⟨b, v⟩ := z
  obtain ⟨hb, hv⟩ := hz
  -- The two fibre restrictions agree after `T b` on a ball containing the segment from `0` to
  -- `v`. Write `L` for precomposition of linear forms with `(T b)⁻¹`.
  have hg (y : E) (hy : y ∈ Metric.ball (0 : E) r) :
      (fun u ↦ f' (σ b, u)) ∘ T b =ᶠ[𝓝 y] fun u ↦ f (b, u) :=
    Filter.eventuallyEq_of_mem (Metric.isOpen_ball.mem_nhds hy) fun u hu ↦
      hUV (Set.mk_mem_prod hb (hrV hu))
  have hseg (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : (0 : E) + t • v ∈ Metric.ball (0 : E) r := by
    rw [zero_add, mem_ball_zero_iff, norm_smul, Real.norm_of_nonneg ht.1]
    exact (mul_le_of_le_one_left (norm_nonneg v) ht.2).trans_lt (mem_ball_zero_iff.mp hv)
  let L : (E →L[ℝ] ℝ) ≃L[ℝ] (E' →L[ℝ] ℝ) := (T b).arrowCongr (ContinuousLinearEquiv.refl ℝ ℝ)
  have hB (x : E) (hx : ∀ t ∈ Icc (0 : ℝ) 1, (0 : E) + t • x ∈ Metric.ball (0 : E) r) :
      hessianAverage (fun u ↦ f' (σ b, u)) 0 (T b x) =
        (L : (E →L[ℝ] ℝ) →L[ℝ] (E' →L[ℝ] ℝ)) ∘L hessianAverage (fun u ↦ f (b, u)) 0 x ∘L
          ((T b).symm : E' →L[ℝ] E) := by
    ext w w'
    have h := hessianAverage_comp_continuousLinearEquiv (fun u ↦ f' (σ b, u)) (T b) 0 x
      ((T b).symm w) ((T b).symm w')
    rw [hessianAverage_congr_of_eventuallyEq fun t ht ↦ hg _ (hx t ht)] at h
    simpa [L] using h.symm
  have hH := hB 0 fun t _ ↦ by simpa using Metric.mem_ball_self (x := (0 : E)) hr
  simp only [map_zero, hessianAverage_zero] at hH
  simp only [morseComparison]
  rw [hB v hseg, hH, ContinuousLinearMap.inverse_equiv_comp,
    ContinuousLinearMap.inverse_comp_equiv]
  ext u
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.symm_apply_apply, ContinuousLinearEquiv.symm_symm,
    ContinuousLinearEquiv.conjContinuousAlgEquiv_apply_apply]

omit [NormedSpace ℝ P] in
/-- **The canonical parametric Morse operator only depends on the germ of the family along the
zero section.** -/
theorem _root_.Filter.EventuallyEq.parametricMorseOperator {f₁ f₂ : P × E → ℝ}
    (h : f₁ =ᶠ[𝓝 (a, 0)] f₂) :
    parametricMorseOperator f₁ =ᶠ[𝓝 (a, 0)] parametricMorseOperator f₂ := by
  filter_upwards [eventually_morseComparison_transition (σ := id)
    (T := fun _ ↦ ContinuousLinearEquiv.refl ℝ E) h.symm] with z hz
  simp only [id, ContinuousLinearEquiv.refl_apply, Prod.mk.eta,
    ContinuousLinearEquiv.conjContinuousAlgEquiv_refl, ContinuousAlgEquiv.refl_apply] at hz
  rw [parametricMorseOperator_eq, parametricMorseOperator_eq, hz]

omit [NormedSpace ℝ P] in
/-- **The canonical parametric Morse map only depends on the germ of the family along the zero
section.** -/
theorem _root_.Filter.EventuallyEq.parametricMorseMap {f₁ f₂ : P × E → ℝ}
    (h : f₁ =ᶠ[𝓝 (a, 0)] f₂) :
    parametricMorseMap f₁ =ᶠ[𝓝 (a, 0)] parametricMorseMap f₂ := by
  filter_upwards [h.parametricMorseOperator] with z hz
  rw [TauCeti.parametricMorseMap, TauCeti.parametricMorseMap, hz]

/-- **The canonical parametric Morse operator under a change of trivialization.** Let a `C²`
family `f` have invertible vertical Hessian at `(a, 0)`, and let `f'` be the same family in other
coordinates near the zero section: `f' (σ b, T b v) = f (b, v)` for `(b, v)` near `(a, 0)`, where
`σ` is any change of parameter and `T` is a family of linear isomorphisms of the fibres,
continuous at `a`. Then near `(a, 0)` the canonical operators of `f'`
and `f` are conjugate by `T`. -/
theorem eventually_parametricMorseOperator_transition (hf : ContDiff ℝ 2 f)
    (hT : ContinuousAt (fun b ↦ (T b : E →L[ℝ] E')) a)
    (hcomp : ∀ᶠ z in 𝓝 (a, (0 : E)), f' (σ z.1, T z.1 z.2) = f z)
    (hH : (fderiv ℝ (fderiv ℝ fun v ↦ f (a, v)) 0).IsInvertible) :
    ∀ᶠ z in 𝓝 (a, (0 : E)), parametricMorseOperator f' (σ z.1, T z.1 z.2) =
      (T z.1).conjContinuousAlgEquiv (parametricMorseOperator f z) := by
  -- The conjugate of the operator of `f` tends to the identity, so it is the square root of the
  -- conjugate of the comparison operator of `f`, which is the comparison operator of `f'`.
  have hconj : Tendsto (fun z : P × E ↦ (T z.1).conjContinuousAlgEquiv
      (sqrtNearOne (E →L[ℝ] E) (morseComparison f z))) (𝓝 (a, 0)) (𝓝 1) := by
    have hT₁ : ContinuousAt (fun z : P × E ↦ (T z.1 : E →L[ℝ] E')) (a, 0) :=
      hT.comp_of_eq continuousAt_fst rfl
    -- Inversion of operators is continuous at the isomorphism `T a`, since `E` is complete.
    have hTsymm : ContinuousAt (fun b ↦ ((T b).symm : E' →L[ℝ] E)) a := by
      simpa only [Function.comp_def, ContinuousLinearMap.inverse_equiv] using
        ContinuousAt.comp (g := ContinuousLinearMap.inverse) (f := fun b ↦ (T b : E →L[ℝ] E'))
          (x := a) (contDiffAt_map_inverse (n := 0) (T a)).continuousAt hT
    have hT₂ : ContinuousAt (fun z : P × E ↦ ((T z.1).symm : E' →L[ℝ] E)) (a, 0) :=
      hTsymm.comp_of_eq continuousAt_fst rfl
    have hc : ContinuousAt (fun z : P × E ↦ (T z.1 : E →L[ℝ] E') ∘L
        parametricMorseOperator f z ∘L ((T z.1).symm : E' →L[ℝ] E)) (a, 0) :=
      hT₁.clm_comp ((continuousAt_parametricMorseOperator hf hH).clm_comp hT₂)
    have h1 : (T a : E →L[ℝ] E') ∘L parametricMorseOperator f (a, 0) ∘L
        ((T a).symm : E' →L[ℝ] E) = 1 := by
      ext u
      simp [parametricMorseOperator_zero hH]
    have h := hc.tendsto
    rw [h1] at h
    simpa only [ContinuousLinearEquiv.conjContinuousAlgEquiv_apply,
      parametricMorseOperator_eq] using h
  have hmap := eventually_sqrtNearOne_map (A := E →L[ℝ] E) (B := E' →L[ℝ] E')
    (φ := fun z : P × E ↦ ((T z.1).conjContinuousAlgEquiv : (E →L[ℝ] E) → E' →L[ℝ] E'))
    (tendsto_morseComparison hf hH) hconj
    (Eventually.of_forall fun z x ↦ map_mul (T z.1).conjContinuousAlgEquiv x x)
  filter_upwards [eventually_morseComparison_transition hcomp, hmap] with z hz hconjR
  rw [parametricMorseOperator_eq f', hz, hconjR, parametricMorseOperator_eq]

/-- **The canonical parametric Morse map under a change of trivialization.** In the setting of
`TauCeti.eventually_parametricMorseOperator_transition`, near `(a, 0)` the canonical parametric
Morse maps of `f'` and `f` correspond under the change of coordinates
`τ (b, v) = (σ b, T b v)`: `Φ' (τ z) = τ (Φ z)`. -/
theorem eventually_parametricMorseMap_transition (hf : ContDiff ℝ 2 f)
    (hT : ContinuousAt (fun b ↦ (T b : E →L[ℝ] E')) a)
    (hcomp : ∀ᶠ z in 𝓝 (a, (0 : E)), f' (σ z.1, T z.1 z.2) = f z)
    (hH : (fderiv ℝ (fderiv ℝ fun v ↦ f (a, v)) 0).IsInvertible) :
    ∀ᶠ z in 𝓝 (a, (0 : E)), parametricMorseMap f' (σ z.1, T z.1 z.2) =
      (σ z.1, T z.1 (parametricMorseMap f z).2) := by
  filter_upwards [eventually_parametricMorseOperator_transition hf hT hcomp hH] with z hz
  simp [parametricMorseMap, hz]

end Transition

/-! ### Local normal forms -/

/-- **Parametric Morse normal form.** A jointly `C^{n+2}` family with a critical zero section
near `a` and invertible vertical Hessian at `(a, 0)` has a jointly `C^n` fiber coordinate change
on a product neighborhood. It fixes the zero section, preserves the parameter, and has identity
derivative at `(a, 0)`. The reference quadratic form is the vertical Hessian at each `(b, 0)`.
The base space need not be complete for this forward coordinate construction. The canonical
parametric Morse map `TauCeti.parametricMorseMap f` is such a coordinate change; see
`TauCeti.eventually_contDiffAt_parametricMorseMap`, `TauCeti.hasFDerivAt_parametricMorseMap` and
`TauCeti.eventually_eq_add_fderiv_fderiv_parametricMorseMap`. -/
theorem exists_parametric_morse_normal_form (hf : ContDiff ℝ (n + 2) f)
    (hcrit : ∀ᶠ b in 𝓝 a, fderiv ℝ (fun v ↦ f (b, v)) 0 = 0)
    (hH : (fderiv ℝ (fderiv ℝ (fun v ↦ f (a, v))) 0).IsInvertible) (hn : n ≠ 0) :
    ∃ (Φ : P × E → P × E) (U : Set P) (V : Set E),
      IsOpen U ∧ IsOpen V ∧ a ∈ U ∧ (0 : E) ∈ V ∧
      (∀ z, (Φ z).1 = z.1) ∧ (∀ b, Φ (b, 0) = (b, 0)) ∧
      ContDiffOn ℝ n Φ (U ×ˢ V) ∧
      HasFDerivAt Φ (ContinuousLinearMap.id ℝ (P × E)) (a, 0) ∧
      ∀ z ∈ U ×ˢ V,
        f z = f (z.1, 0) + (2 : ℝ)⁻¹ *
          fderiv ℝ (fderiv ℝ (fun v ↦ f (z.1, v))) 0 (Φ z).2 (Φ z).2 := by
  obtain ⟨U, V, hU, haU, hV, h0V, hUV⟩ := mem_nhds_prod_iff'.mp
    ((eventually_contDiffAt_parametricMorseMap hf hH).and
      (eventually_eq_add_fderiv_fderiv_parametricMorseMap (hf.of_le le_add_self) hcrit hH))
  exact ⟨parametricMorseMap f, U, V, hU, hV, haU, h0V, parametricMorseMap_fst f,
    parametricMorseMap_zero f, fun z hz ↦ (hUV hz).1.contDiffWithinAt,
    hasFDerivAt_parametricMorseMap hf hH hn, fun z hz ↦ (hUV hz).2⟩

/-- **The parametric Morse lemma, as a local chart.** The chart has a product source containing
`(a, 0)`, preserves the base parameter in both directions, and fixes the zero section. Its
quadratic equation uses the vertical Hessian on that same zero section. The base and the fiber
are Banach spaces, so the ordinary inverse function theorem applies to their product. -/
theorem exists_parametric_morse_chart [CompleteSpace P] (hf : ContDiff ℝ (n + 2) f)
    (hcrit : ∀ᶠ b in 𝓝 a, fderiv ℝ (fun v ↦ f (b, v)) 0 = 0)
    (hH : (fderiv ℝ (fderiv ℝ (fun v ↦ f (a, v))) 0).IsInvertible) (hn : n ≠ 0) :
    ∃ (ψ : OpenPartialHomeomorph (P × E) (P × E)) (U : Set P) (V : Set E),
      IsOpen U ∧ IsOpen V ∧ a ∈ U ∧ (0 : E) ∈ V ∧ ψ.source = U ×ˢ V ∧
      (∀ z, (ψ z).1 = z.1) ∧ (∀ b, ψ (b, 0) = (b, 0)) ∧
      (∀ z ∈ ψ.target, (ψ.symm z).1 = z.1) ∧
      ContDiffOn ℝ n ψ ψ.source ∧ ContDiffOn ℝ n ψ.symm ψ.target ∧
      ∀ z ∈ ψ.source,
        f z = f (z.1, 0) + (2 : ℝ)⁻¹ *
          fderiv ℝ (fderiv ℝ (fun v ↦ f (z.1, v))) 0 (ψ z).2 (ψ z).2 := by
  obtain ⟨Φ, U, V, hU, hV, haU, h0V, hΦfst, hΦ0, hΦ, hΦd, hΦeq⟩ :=
    exists_parametric_morse_normal_form hf hcrit hH hn
  have haUV : (a, (0 : E)) ∈ U ×ˢ V := ⟨haU, h0V⟩
  have hUV : IsOpen (U ×ˢ V) := hU.prod hV
  have hn' : 1 ≤ (n : ℕ∞ω) :=
    ENat.one_le_iff_ne_zero_withTop.2 (by simpa using hn)
  obtain ⟨Θ, hΘ, haΘ, hΘsub, hΘsymm⟩ :=
    ContDiffOn.exists_openPartialHomeomorph hΦ hUV haUV hn'
      (e := ContinuousLinearEquiv.refl ℝ (P × E)) hΦd.fderiv.symm
  -- Choose a product source to retain a common fiber neighborhood.
  obtain ⟨W, Z, hW, haW, hZ, h0Z, hWZ⟩ :=
    mem_nhds_prod_iff'.mp (Θ.open_source.mem_nhds haΘ)
  let ψ := Θ.restrOpen (W ×ˢ Z) (hW.prod hZ)
  have hsource : ψ.source = W ×ˢ Z := by
    rw [OpenPartialHomeomorph.restrOpen_source]
    apply inter_eq_right.mpr
    exact hWZ
  have hψ : (ψ : P × E → P × E) = Φ := by
    simpa only [ψ, OpenPartialHomeomorph.coe_restrOpen] using hΘ
  refine ⟨ψ, W, Z, hW, hZ, haW, h0Z, hsource, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [hψ] using hΦfst
  · simpa only [hψ] using hΦ0
  · intro z hz
    have hi := congrArg Prod.fst (ψ.right_inv hz)
    rwa [hψ, hΦfst] at hi
  · rw [hψ]
    exact hΦ.mono (fun z hz ↦ hΘsub (hWZ (hsource ▸ hz)))
  · exact hΘsymm.mono inter_subset_left
  · intro z hz
    simpa only [hψ] using hΦeq z (hΘsub (hWZ (hsource ▸ hz)))

end TauCeti
