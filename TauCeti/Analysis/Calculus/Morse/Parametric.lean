/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Morse.NormalForm
import TauCeti.Analysis.Calculus.IteratedFDeriv.CompContinuousLinearEquiv
import TauCeti.Analysis.Calculus.InverseFunctionTheorem
import TauCeti.Analysis.Normed.Operator.BoundedLinearMaps

/-!
# The parametric Morse lemma in a trivial bundle

A smooth family of functions with a critical zero section and a strongly nondegenerate vertical
Hessian admits local coordinates preserving the base parameter. The coordinate change fixes the
zero section and transforms the function into its vertical Hessian quadratic form. Both the
coordinate change and its local inverse are jointly smooth in base and fiber.

The construction follows the operator-square-root proof of the Morse--Palais lemma, as formalized
in `TauCeti.Analysis.Calculus.Morse.NormalForm`: apply its canonical congruence to the integral
average of the vertical Hessian, then invert the map `(b, v) ↦ (b, R (b, v) v)`.
The Hessian convention is the second derivative itself, so the quadratic formula has a factor
`1 / 2`.

The fibre coordinate is canonical: `TauCeti.parametricMorseCoord f (b, v) = R (b, v) v`, where
`R (b, v)` is the canonical congruence `TauCeti.morseCongruence` of the averaged vertical Hessian
with the vertical Hessian at `(b, 0)`. Because no choice enters, it is natural for fibrewise linear
changes of coordinates: if `g (b, v) = f (b, e b v)` for linear equivalences `e b` depending
continuously on `b`, then near the zero section
`parametricMorseCoord g (b, v) = (e b)⁻¹ (parametricMorseCoord f (b, e b v))`
(`TauCeti.eventually_parametricMorseCoord_comp`). It also depends only on the germ of `f` along
the zero section (`Filter.EventuallyEq.parametricMorseCoord`) and reads `f` only along fibres, so
if `f' (σ b, T b v) = f (b, v)` near the zero section, for any change of parameter `σ` and fibre
isomorphisms `T b` depending continuously on `b`, then
`parametricMorseCoord f' (σ b, T b v) = T b (parametricMorseCoord f (b, v))` near the zero section
(`TauCeti.eventually_parametricMorseCoord_transition`). Read in two trivializations of a vector
bundle, the canonical coordinates of a function therefore agree near the zero section. This is the
compatibility with bundle transitions needed to patch the local normal forms of a Morse–Bott
function along its critical submanifold; the patching itself is not done here.

## Main declarations

* `TauCeti.parametricMorseCoord`: the canonical fibre coordinate.
* `TauCeti.parametricMorseCoord_congr_of_eqOn`: it only depends on the family near the segment
  in the fibre.
* `TauCeti.eventually_eq_add_parametricMorseCoord`: the family is its vertical Hessian quadratic
  form in this coordinate.
* `TauCeti.eventually_contDiffAt_parametricMorseCoord` and
  `TauCeti.hasFDerivAt_parametricMorseCoord`: it is `C^n` for a `C^{n+2}` family, with
  derivative the fibre projection on the zero section.
* `TauCeti.eventually_parametricMorseCoord_comp`: naturality for fibrewise linear changes of
  coordinates.
* `Filter.EventuallyEq.parametricMorseCoord`: the coordinate only depends on the germ of the
  family along the zero section.
* `TauCeti.eventually_parametricMorseCoord_transition`: compatibility with changes of
  trivialization, allowing a change of parameter and only a local relation between the families.
* `TauCeti.exists_parametric_morse_normal_form` and `TauCeti.exists_parametric_morse_chart`: the
  resulting coordinate change and local chart on a product neighbourhood, given by the canonical
  coordinate.

## References

* R. S. Palais, *The Morse lemma for Banach spaces*, Bull. Amer. Math. Soc. **75** (1969),
  968--971.
* R. S. Palais, *Morse theory on Hilbert manifolds*, Topology **2** (1963), 299--340, Section 2.
-/

public section

noncomputable section

open Filter Set Topology
open scoped ContDiff

namespace TauCeti

variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {f : P × E → ℝ} {a : P} {n : ℕ∞}

/-- The **canonical parametric Morse coordinate** of a family `f (b, v)`: the fibre vector
`R (b, v) v`, where `R (b, v)` is the canonical congruence `TauCeti.morseCongruence` comparing
the averaged vertical Hessian along the segment from `(b, 0)` to `(b, v)` with the vertical
Hessian at `(b, 0)`. For a `C^2` family whose zero section is critical near `a` and whose
vertical Hessian `H b` at `(b, 0)` is invertible at `b = a`, near `(a, 0)` it satisfies
`f (b, v) = f (b, 0) + 2⁻¹ * H b (parametricMorseCoord f (b, v)) (parametricMorseCoord f (b, v))`
(`TauCeti.eventually_eq_add_parametricMorseCoord`). Under the same regularity and invertibility
hypotheses, the coordinate is unchanged by fibrewise linear changes of coordinates
(`TauCeti.eventually_parametricMorseCoord_comp`). -/
def parametricMorseCoord (f : P × E → ℝ) (z : P × E) : E :=
  morseCongruence (fderiv ℝ (fderiv ℝ fun v ↦ f (z.1, v)) 0)
    (hessianAverage (fun v ↦ f (z.1, v)) 0 z.2) z.2

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
/-- The canonical parametric Morse coordinate applies the canonical congruence of the averaged
vertical Hessian with the vertical Hessian at `(b, 0)` to the fibre vector. -/
theorem parametricMorseCoord_def (f : P × E → ℝ) (z : P × E) :
    parametricMorseCoord f z = morseCongruence (fderiv ℝ (fderiv ℝ fun v ↦ f (z.1, v)) 0)
      (hessianAverage (fun v ↦ f (z.1, v)) 0 z.2) z.2 := by
  rw [parametricMorseCoord]

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
/-- The canonical parametric Morse coordinate vanishes on the zero section. -/
@[simp]
theorem parametricMorseCoord_mk_zero (f : P × E → ℝ) (b : P) :
    parametricMorseCoord f (b, 0) = 0 := by
  simp [parametricMorseCoord_def]

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
/-- The **canonical parametric Morse coordinate only depends on the family near the segment** in
the fibre from `0` to `z.2`: families whose slices over `z.1` agree on an open set star-convex
about `0` and containing `z.2` have the same coordinate at `z`. -/
theorem parametricMorseCoord_congr_of_eqOn {f g : P × E → ℝ} {z : P × E} {V : Set E}
    (hV : IsOpen V) (hV₀ : StarConvex ℝ 0 V)
    (hfg : EqOn (fun v ↦ f (z.1, v)) (fun v ↦ g (z.1, v)) V) (hz : z.2 ∈ V) :
    parametricMorseCoord f z = parametricMorseCoord g z := by
  have hD : ∀ y ∈ V, fderiv ℝ (fderiv ℝ fun v ↦ f (z.1, v)) y =
      fderiv ℝ (fderiv ℝ fun v ↦ g (z.1, v)) y := fun y hy ↦
    (hfg.eventuallyEq_of_mem (hV.mem_nhds hy)).fderiv.fderiv_eq
  have hseg : ∀ t ∈ uIcc (0 : ℝ) 1, (0 : E) + t • z.2 ∈ V := by
    intro t ht
    rw [uIcc_of_le zero_le_one] at ht
    simpa using hV₀.smul_mem hz ht.1 ht.2
  have hA : hessianAverage (fun v ↦ f (z.1, v)) 0 z.2 =
      hessianAverage (fun v ↦ g (z.1, v)) 0 z.2 := by
    rw [hessianAverage_eq_integral_Icc, hessianAverage_eq_integral_Icc]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun t ht ↦ ?_
    rw [hD _ (hseg t (by rwa [uIcc_of_le zero_le_one]))]
  rw [parametricMorseCoord_def, parametricMorseCoord_def, hA,
    hD 0 (by simpa using hseg 0 (by simp))]

omit [CompleteSpace E] in
/-- The pair of forms compared by the canonical coordinate: the vertical Hessian at `(b, 0)` and
the averaged vertical Hessian at `(b, v)`. It is jointly `C^n` for a `C^{n+2}` family, and it is
the pair `(H a, H a)` at `(a, 0)`. -/
private theorem contDiff_verticalHessianPair (hf : ContDiff ℝ (n + 2) f) :
    ContDiff ℝ n fun z : P × E ↦ (fderiv ℝ (fderiv ℝ fun v ↦ f (z.1, v)) 0,
      hessianAverage (fun v ↦ f (z.1, v)) 0 z.2) := by
  have hA := contDiff_hessianAverage_param hf (0 : E)
  have hH : ContDiff ℝ n fun z : P × E ↦ fderiv ℝ (fderiv ℝ fun v ↦ f (z.1, v)) 0 := by
    simpa only [Function.comp_def, hessianAverage_zero] using
      hA.comp (contDiff_fst.prodMk contDiff_const : ContDiff ℝ n fun z : P × E ↦ (z.1, (0 : E)))
  exact hH.prodMk hA

omit [CompleteSpace E] in
private theorem tendsto_verticalHessianPair (hf : ContDiff ℝ 2 f) :
    Tendsto (fun z : P × E ↦ (fderiv ℝ (fderiv ℝ fun v ↦ f (z.1, v)) 0,
      hessianAverage (fun v ↦ f (z.1, v)) 0 z.2)) (𝓝 (a, 0))
      (𝓝 (fderiv ℝ (fderiv ℝ fun v ↦ f (a, v)) 0, fderiv ℝ (fderiv ℝ fun v ↦ f (a, v)) 0)) := by
  have h := (contDiff_verticalHessianPair (n := 0) (by simpa using hf)).continuous.tendsto
    (a, (0 : E))
  simpa only [hessianAverage_zero] using h

/-- Near a point of the zero section with invertible vertical Hessian, the canonical parametric
Morse coordinate of a `C^{n+2}` family is `C^n`. -/
theorem eventually_contDiffAt_parametricMorseCoord (hf : ContDiff ℝ (n + 2) f)
    (hH : (fderiv ℝ (fderiv ℝ fun v ↦ f (a, v)) 0).IsInvertible) :
    ∀ᶠ z in 𝓝 (a, 0), ContDiffAt ℝ n (parametricMorseCoord f) z := by
  have hf₂ : ContDiff ℝ 2 f := hf.of_le le_add_self
  filter_upwards [(tendsto_verticalHessianPair hf₂).eventually
    (eventually_contDiffAt_morseCongruence hH (n := n))] with z hz
  exact (ContDiffAt.comp (g := fun p : (E →L[ℝ] E →L[ℝ] ℝ) × (E →L[ℝ] E →L[ℝ] ℝ) ↦
    morseCongruence p.1 p.2) z hz (contDiff_verticalHessianPair hf).contDiffAt).clm_apply
    contDiffAt_snd

/-- At a point of the zero section with invertible vertical Hessian, the derivative of the
canonical parametric Morse coordinate of a `C^2` family is the projection to the fibre. -/
theorem hasFDerivAt_parametricMorseCoord (hf : ContDiff ℝ 2 f)
    (hH : (fderiv ℝ (fderiv ℝ fun v ↦ f (a, v)) 0).IsInvertible) :
    HasFDerivAt (parametricMorseCoord f) (ContinuousLinearMap.snd ℝ P E) (a, 0) := by
  let R : P × E → E →L[ℝ] E := fun z ↦ morseCongruence
    (fderiv ℝ (fderiv ℝ fun v ↦ f (z.1, v)) 0) (hessianAverage (fun v ↦ f (z.1, v)) 0 z.2)
  -- Only continuity of `R` is needed: the coordinate differs from the fibre projection by
  -- `(R z - 1) z.2`, a vanishing operator applied to a vector of size `O (z - (a, 0))`.
  have hR₁ : Tendsto R (𝓝 (a, 0)) (𝓝 1) :=
    (tendsto_morseCongruence hH).comp (tendsto_verticalHessianPair hf)
  have hR : Tendsto (fun z ↦ R z - 1) (𝓝 (a, 0)) (𝓝 0) := by
    simpa only [sub_self] using hR₁.sub_const 1
  have hsnd : (fun z : P × E ↦ (z - (a, 0)).2) =O[𝓝 (a, 0)] fun z ↦ z - (a, 0) :=
    Asymptotics.isBigO_of_le _ fun z ↦ norm_snd_le (z - (a, 0))
  have ho := ((Asymptotics.isLittleO_one_iff ℝ).2 hR).norm_left.mul_isBigO
    hsnd.norm_left.norm_right
  simp only [one_mul] at ho
  refine HasFDerivAt.of_isLittleO <| (Asymptotics.isBigO_of_le _ fun z ↦ ?_).trans_isLittleO
    ho.of_norm_right
  rw [parametricMorseCoord_def, parametricMorseCoord_mk_zero]
  refine (le_of_eq ?_).trans (((R z - 1).le_opNorm _).trans (Real.le_norm_self _))
  simp [R]

/-- **The parametric Morse normal form in the canonical coordinate.** Near a point `(a, 0)` of a
critical zero section with invertible vertical Hessian, a `C^2` family `f` is its vertical
Hessian quadratic form at `(b, 0)` evaluated on the canonical parametric Morse coordinate. -/
theorem eventually_eq_add_parametricMorseCoord (hf : ContDiff ℝ 2 f)
    (hcrit : ∀ᶠ b in 𝓝 a, fderiv ℝ (fun v ↦ f (b, v)) 0 = 0)
    (hH : (fderiv ℝ (fderiv ℝ fun v ↦ f (a, v)) 0).IsInvertible) :
    ∀ᶠ z in 𝓝 (a, (0 : E)), f z = f (z.1, 0) + (2 : ℝ)⁻¹ *
      fderiv ℝ (fderiv ℝ fun v ↦ f (z.1, v)) 0 (parametricMorseCoord f z)
        (parametricMorseCoord f z) := by
  have hslice (b : P) : ContDiff ℝ 2 (fun v ↦ f (b, v)) :=
    hf.comp (contDiff_const.prodMk contDiff_id)
  filter_upwards [(tendsto_verticalHessianPair hf).eventually
    (eventually_morseCongruence_apply hH), continuousAt_fst.eventually hcrit] with z hz hzcrit
  have hsymm (b : P) (w w' : E) :
      fderiv ℝ (fderiv ℝ fun v ↦ f (b, v)) 0 w w' =
        fderiv ℝ (fderiv ℝ fun v ↦ f (b, v)) 0 w' w := by
    simpa only [hessianAverage_zero] using hessianAverage_symm (hslice b) 0 0 w w'
  have hc := hz (hsymm z.1) (hessianAverage_symm (hslice z.1) 0 z.2) z.2 z.2
  have ht := map_add_eq_add_hessianAverage (hslice z.1) 0 z.2
  simp only [zero_add, hzcrit, zero_apply, add_zero, smul_eq_mul,
    Prod.mk.eta] at ht
  rw [ht, parametricMorseCoord_def, hc]

section Naturality

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [CompleteSpace E']

/-- **The canonical parametric Morse coordinate is natural for fibrewise linear changes of
coordinates.** Let `e b : E' ≃L[ℝ] E` be linear equivalences depending continuously on `b` at
`a`, and let `g (b, v) = f (b, e b v)`. Near `(a, 0)` the canonical
coordinate of `g` is that of `f` read through `e b`:
`parametricMorseCoord g (b, v) = (e b)⁻¹ (parametricMorseCoord f (b, e b v))`.

Applied to the coordinate changes of a vector bundle, this says that the canonical coordinates of
a function read in two trivializations agree near the zero section, so that they define a single
fibre-preserving coordinate change there. -/
theorem eventually_parametricMorseCoord_comp (hf : ContDiff ℝ 2 f)
    (hH : (fderiv ℝ (fderiv ℝ fun v ↦ f (a, v)) 0).IsInvertible) {e : P → E' ≃L[ℝ] E}
    (he : ContinuousAt (fun b ↦ (e b : E' →L[ℝ] E)) a) :
    ∀ᶠ z in 𝓝 (a, (0 : E')), parametricMorseCoord (fun z ↦ f (z.1, e z.1 z.2)) z =
      (e z.1).symm (parametricMorseCoord f (z.1, e z.1 z.2)) := by
  have hslice (b : P) : ContDiff ℝ 2 (fun v ↦ f (b, v)) :=
    hf.comp (contDiff_const.prodMk contDiff_id)
  -- The forms of the pulled-back family are the pullbacks of the forms of `f`.
  have hHg (b : P) : fderiv ℝ (fderiv ℝ fun v ↦ f (b, e b v)) 0 =
      (fderiv ℝ (fderiv ℝ fun v ↦ f (b, v)) 0).bilinearComp (e b : E' →L[ℝ] E)
        (e b : E' →L[ℝ] E) := by
    ext w w'
    simpa [Function.comp_def] using
      (e b).fderiv_fderiv_comp_right_apply_apply (fun v ↦ f (b, v)) 0 w w'
  have hAg (z : P × E') : hessianAverage (fun v ↦ f (z.1, e z.1 v)) 0 z.2 =
      (hessianAverage (fun v ↦ f (z.1, v)) 0 (e z.1 z.2)).bilinearComp
        (e z.1 : E' →L[ℝ] E) (e z.1 : E' →L[ℝ] E) := by
    ext w w'
    simpa [Function.comp_def] using
      hessianAverage_comp_continuousLinearEquiv_apply (hslice z.1) (e z.1) 0 z.2 w w'
  -- The change of coordinates `ψ (b, v) = (b, e b v)` fixes `(a, 0)`.
  set ψ : P × E' → P × E := fun z ↦ (z.1, e z.1 z.2)
  have hψ : Tendsto ψ (𝓝 (a, 0)) (𝓝 (a, 0)) := he.tendsto_prodMk_clm_apply
  have hpair := (tendsto_verticalHessianPair hf).comp hψ
  -- Pulling back along `e b` conjugates the canonical congruence of `f` by `e b`.
  filter_upwards [eventually_morseCongruence_bilinearComp
    (B₁ := fun z : P × E' ↦ fderiv ℝ (fderiv ℝ fun v ↦ f (z.1, v)) 0)
    (B := fun z : P × E' ↦ hessianAverage (fun v ↦ f (z.1, v)) 0 (e z.1 z.2))
    (e := fun z : P × E' ↦ e z.1) hH hpair (he.tendsto.comp continuousAt_fst.tendsto)]
    with z hz
  rw [parametricMorseCoord_def, parametricMorseCoord_def, hHg, hAg, hz]
  simp

end Naturality

section Transition

omit [NormedSpace ℝ P] in
/-- **The canonical parametric Morse coordinate only depends on the germ of the family along the
zero section.** If two families agree near `(a, 0)`, so do their canonical coordinates. -/
theorem _root_.Filter.EventuallyEq.parametricMorseCoord {f₁ f₂ : P × E → ℝ}
    (h : f₁ =ᶠ[𝓝 (a, 0)] f₂) :
    parametricMorseCoord f₁ =ᶠ[𝓝 (a, 0)] parametricMorseCoord f₂ := by
  obtain ⟨U, V, hU, haU, hV, h0V, hUV⟩ := mem_nhds_prod_iff'.mp h
  obtain ⟨r, hr, hrV⟩ := Metric.isOpen_iff.mp hV 0 h0V
  filter_upwards [prod_mem_nhds (hU.mem_nhds haU) (Metric.ball_mem_nhds (0 : E) hr)] with z hz
  obtain ⟨b, v⟩ := z
  obtain ⟨hb, hv⟩ := hz
  -- The two fibre restrictions agree on a ball containing the segment from `0` to `v`.
  have hg (y : E) (hy : y ∈ Metric.ball (0 : E) r) :
      (fun u ↦ f₁ (b, u)) =ᶠ[𝓝 y] fun u ↦ f₂ (b, u) :=
    Filter.eventuallyEq_of_mem (Metric.isOpen_ball.mem_nhds hy) fun u hu ↦
      hUV (Set.mk_mem_prod hb (hrV hu))
  have hseg (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : (0 : E) + t • v ∈ Metric.ball (0 : E) r :=
    (convex_ball (0 : E) r).add_smul_mem (Metric.mem_ball_self hr) (by rwa [zero_add]) ht
  rw [parametricMorseCoord_def, parametricMorseCoord_def,
    hessianAverage_congr_of_eventuallyEq fun t ht ↦ hg _ (hseg t ht),
    (hg 0 (Metric.mem_ball_self hr)).fderiv.fderiv_eq]

variable {P' E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [CompleteSpace E']
  {f' : P' × E' → ℝ} {σ : P → P'} {T : P → E ≃L[ℝ] E'}

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
/-- **The canonical parametric Morse coordinate only reads the family along fibres.** Changing
the parameter of a family by any map `σ` changes its canonical coordinate in the same way. -/
theorem parametricMorseCoord_comp_prodMap (f : P' × E → ℝ) (σ : P → P') (b : P) (v : E) :
    parametricMorseCoord (fun z ↦ f (σ z.1, z.2)) (b, v) = parametricMorseCoord f (σ b, v) := by
  simp only [parametricMorseCoord_def]

/-- **The canonical parametric Morse coordinate under a change of trivialization.** Let a `C^2`
family `f` have invertible vertical Hessian at `(a, 0)`, and let `f'` be the same family in other
coordinates near the zero section: `f' (σ b, T b v) = f (b, v)` for `(b, v)` near `(a, 0)`, where
`σ` is any change of parameter and `T b : E ≃L[ℝ] E'` are linear isomorphisms of the fibres
depending continuously on `b` at `a`. No regularity of `f'` or `σ` is assumed. Then near `(a, 0)`
the canonical coordinates correspond:
`parametricMorseCoord f' (σ b, T b v) = T b (parametricMorseCoord f (b, v))`. -/
theorem eventually_parametricMorseCoord_transition (hf : ContDiff ℝ 2 f)
    (hH : (fderiv ℝ (fderiv ℝ fun v ↦ f (a, v)) 0).IsInvertible)
    (hT : ContinuousAt (fun b ↦ (T b : E →L[ℝ] E')) a)
    (hcomp : ∀ᶠ z in 𝓝 (a, (0 : E)), f' (σ z.1, T z.1 z.2) = f z) :
    ∀ᶠ z in 𝓝 (a, (0 : E)), parametricMorseCoord f' (σ z.1, T z.1 z.2) =
      T z.1 (parametricMorseCoord f z) := by
  -- Inversion of operators is continuous at the isomorphism `T a`, since `E` is complete.
  have hTsymm : ContinuousAt (fun b ↦ ((T b).symm : E' →L[ℝ] E)) a := by
    simpa only [Function.comp_def, ContinuousLinearMap.inverse_equiv] using
      ContinuousAt.comp (g := ContinuousLinearMap.inverse) (f := fun b ↦ (T b : E →L[ℝ] E'))
        (x := a) (contDiffAt_map_inverse (n := 0) (T a)).continuousAt hT
  -- The fibrewise changes of coordinates `(b, v) ↦ (b, T b v)` and its inverse fix `(a, 0)`.
  have hψ : Tendsto (fun z : P × E ↦ (z.1, T z.1 z.2)) (𝓝 (a, 0)) (𝓝 (a, 0)) :=
    hT.tendsto_prodMk_clm_apply
  have hψsymm : Tendsto (fun z : P × E' ↦ (z.1, (T z.1).symm z.2)) (𝓝 (a, 0)) (𝓝 (a, 0)) :=
    hTsymm.tendsto_prodMk_clm_apply
  -- Read in the parameter of `f`, the family `f'` is near `(a, 0)` the pullback of `f` along
  -- `(T b)⁻¹`, whose canonical coordinate is natural.
  have hloc : (fun z : P × E' ↦ f' (σ z.1, z.2)) =ᶠ[𝓝 (a, 0)]
      fun z ↦ f (z.1, (T z.1).symm z.2) := by
    filter_upwards [hψsymm.eventually hcomp] with z hz
    simpa using hz
  filter_upwards [hψ.eventually hloc.parametricMorseCoord,
    hψ.eventually (eventually_parametricMorseCoord_comp hf hH (e := fun b ↦ (T b).symm) hTsymm)]
    with z hloc' hnat
  rw [parametricMorseCoord_comp_prodMap] at hloc'
  rw [hloc', hnat]
  simp

end Transition

/-- **Parametric Morse normal form.** A jointly `C^{n+2}` family with a critical zero section
near `a` and invertible vertical Hessian at `(a, 0)` has a jointly `C^n` fiber coordinate change
`(b, v) ↦ (b, parametricMorseCoord f (b, v))` on a product neighborhood. It preserves the
parameter, fixes the zero section (`TauCeti.parametricMorseCoord_mk_zero`), and has identity
derivative at `(a, 0)`. The reference quadratic form is the vertical Hessian at each `(b, 0)`.
The base space need not be complete for this forward coordinate construction. -/
theorem exists_parametric_morse_normal_form (hf : ContDiff ℝ (n + 2) f)
    (hcrit : ∀ᶠ b in 𝓝 a, fderiv ℝ (fun v ↦ f (b, v)) 0 = 0)
    (hH : (fderiv ℝ (fderiv ℝ (fun v ↦ f (a, v))) 0).IsInvertible) :
    ∃ (U : Set P) (V : Set E),
      IsOpen U ∧ IsOpen V ∧ a ∈ U ∧ (0 : E) ∈ V ∧
      ContDiffOn ℝ n (fun z : P × E ↦ (z.1, parametricMorseCoord f z)) (U ×ˢ V) ∧
      HasFDerivAt (fun z : P × E ↦ (z.1, parametricMorseCoord f z))
        (ContinuousLinearMap.id ℝ (P × E)) (a, 0) ∧
      ∀ z ∈ U ×ˢ V,
        f z = f (z.1, 0) + (2 : ℝ)⁻¹ * fderiv ℝ (fderiv ℝ (fun v ↦ f (z.1, v))) 0
          (parametricMorseCoord f z) (parametricMorseCoord f z) := by
  obtain ⟨U, V, hU, haU, hV, h0V, hUV⟩ := mem_nhds_prod_iff'.mp
    (Filter.inter_mem (eventually_contDiffAt_parametricMorseCoord hf hH)
      (eventually_eq_add_parametricMorseCoord (hf.of_le le_add_self) hcrit hH))
  refine ⟨U, V, hU, hV, haU, h0V,
    fun z hz ↦ (contDiffAt_fst.prodMk (hUV hz).1).contDiffWithinAt, ?_, fun z hz ↦ (hUV hz).2⟩
  simpa only [ContinuousLinearMap.fst_prod_snd] using
    hasFDerivAt_fst.prodMk (hasFDerivAt_parametricMorseCoord (hf.of_le le_add_self) hH)

/-- **The parametric Morse lemma, as a local chart.** The chart has a product source containing
`(a, 0)` and is given by the canonical coordinate
`(b, v) ↦ (b, parametricMorseCoord f (b, v))`, so it preserves the base parameter and fixes the
zero section; its inverse preserves the base parameter too. Its quadratic equation uses the
vertical Hessian on that same zero section. The base and the fiber are Banach spaces, so the
ordinary inverse function theorem applies to their product. -/
theorem exists_parametric_morse_chart [CompleteSpace P] (hf : ContDiff ℝ (n + 2) f)
    (hcrit : ∀ᶠ b in 𝓝 a, fderiv ℝ (fun v ↦ f (b, v)) 0 = 0)
    (hH : (fderiv ℝ (fderiv ℝ (fun v ↦ f (a, v))) 0).IsInvertible) (hn : n ≠ 0) :
    ∃ (ψ : OpenPartialHomeomorph (P × E) (P × E)) (U : Set P) (V : Set E),
      IsOpen U ∧ IsOpen V ∧ a ∈ U ∧ (0 : E) ∈ V ∧ ψ.source = U ×ˢ V ∧
      (∀ z, ψ z = (z.1, parametricMorseCoord f z)) ∧
      (∀ z ∈ ψ.target, (ψ.symm z).1 = z.1) ∧
      ContDiffOn ℝ n ψ ψ.source ∧ ContDiffOn ℝ n ψ.symm ψ.target ∧
      ∀ z ∈ ψ.source,
        f z = f (z.1, 0) + (2 : ℝ)⁻¹ *
          fderiv ℝ (fderiv ℝ (fun v ↦ f (z.1, v))) 0 (ψ z).2 (ψ z).2 := by
  obtain ⟨U, V, hU, hV, haU, h0V, hΦ, hΦd, hΦeq⟩ :=
    exists_parametric_morse_normal_form hf hcrit hH
  set Φ : P × E → P × E := fun z ↦ (z.1, parametricMorseCoord f z)
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
  refine ⟨ψ, W, Z, hW, hZ, haW, h0Z, hsource, fun z ↦ by rw [hψ], ?_, ?_, ?_, ?_⟩
  · intro z hz
    -- the first coordinate of `ψ (ψ.symm z) = z` is that of `ψ.symm z`
    have hi := congrArg Prod.fst (ψ.right_inv hz)
    rwa [hψ] at hi
  · rw [hψ]
    exact hΦ.mono (fun z hz ↦ hΘsub (hWZ (hsource ▸ hz)))
  · exact hΘsymm.mono inter_subset_left
  · intro z hz
    rw [hψ]
    exact hΦeq z (hΘsub (hWZ (hsource ▸ hz)))

end TauCeti
