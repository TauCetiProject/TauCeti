/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.EnergyForm.Sobolev
public import TauCeti.Analysis.Sobolev.W1p.DifferenceQuotient
import TauCeti.MeasureTheory.Function.Lp.Norm

/-!
# Difference quotients in either argument of the Sobolev energy form

For essentially bounded coefficients, the energy form is bilinear on the whole-space Sobolev
space. A difference quotient in either argument is therefore the inverse step times the
energy difference between a translate and the original argument. These identities isolate the
linearity step in discrete integration by parts.

Translation moves between the two arguments with the opposite shift and translated coefficients.
For Lipschitz coefficient fields, the resulting commutator has a bound independent of the
difference-quotient step. These energy-form identities are used in weak-solution regularity,
but require neither ellipticity nor a weak equation.

## References

* L. C. Evans, *Partial Differential Equations*, §6.3.1, Theorem 1, for the
  difference-quotient argument with variable coefficients.
* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Theorem 8.8 and Lemma 7.23, for the difference-quotient coefficient estimates.
-/

public section

noncomputable section

open MeasureTheory Set TopologicalSpace
open scoped ENNReal NNReal InnerProductSpace

namespace TauCeti.PDE

variable {ι : Type*} [Fintype ι] {mu : Measure (EuclideanSpace ℝ ι)} [mu.IsAddHaarMeasure]
  {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {K : ℝ≥0}
  {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {c : EuclideanSpace ℝ ι → ℝ}
  {Omega : Opens (EuclideanSpace ℝ ι)}

/-- Expanding a difference quotient in the first argument of the energy form. -/
theorem energyFormH1_differenceQuotient_left
    (hcoeff : MemLp (fun x => energyIntegrand (a x) (b x) (c x)) ⊤
      (mu.restrict Omega))
    (w : EuclideanSpace ℝ ι) (t : ℝ) {hw : MapsTo (· + t • w) Omega Omega}
    (u v : W1p mu Omega 2) :
    energyFormH1 a b c
        (W1p.differenceQuotient le_rfl w t hw u) v
      = t⁻¹ * (energyFormH1 a b c (W1p.translate hw u) v
        - energyFormH1 a b c u v) := by
  rw [W1p.differenceQuotient_def, W1p.restrictL_self,
    ← energyFormH1L_apply (b := b) (c := c) hcoeff]
  simp only [map_smul, map_sub, smul_apply, sub_apply, energyFormH1L_apply, smul_eq_mul]

/-- Expanding a difference quotient in the second argument of the energy form. -/
theorem energyFormH1_differenceQuotient_right
    (hcoeff : MemLp (fun x => energyIntegrand (a x) (b x) (c x)) ⊤
      (mu.restrict Omega))
    (w : EuclideanSpace ℝ ι) (t : ℝ) {hw : MapsTo (· + t • w) Omega Omega}
    (u v : W1p mu Omega 2) :
    energyFormH1 a b c u
        (W1p.differenceQuotient le_rfl w t hw v)
      = t⁻¹ * (energyFormH1 a b c u (W1p.translate hw v)
        - energyFormH1 a b c u v) := by
  rw [W1p.differenceQuotient_def, W1p.restrictL_self,
    ← energyFormH1L_apply (b := b) (c := c) hcoeff]
  simp only [map_smul, map_sub, energyFormH1L_apply, smul_eq_mul]

/-- **Translation moves across the energy form.** For opposite vectors `h` and `k`, translating
the first argument of the energy form of `a` by `h` is the same as translating the second
argument and the coefficient field by `k`:

`∫ ⟨a(x) ∇u(x + h), ∇v(x)⟩ dx = ∫ ⟨a(x + k) ∇u(x), ∇v(x + k)⟩ dx`.

This is the integrated form of the substitution `x ↦ x + k`, and needs no hypothesis on `a`. For
a constant coefficient matrix the translated coefficient field is the original one. -/
theorem energyFormH1_translate (a : EuclideanSpace ℝ ι → Matrix ι ι ℝ)
    {h k : EuclideanSpace ℝ ι} (hk : h + k = 0)
    (hOmega : (Omega : Set _) = (· + h) ⁻¹' Omega)
    {hh : MapsTo (· + h) Omega Omega} {hkOmega : MapsTo (· + k) Omega Omega}
    (u v : W1p mu Omega 2) :
    energyFormH1 a 0 0 (W1p.translate hh u) v
      = energyFormH1 (fun x => a (x + k)) 0 0 u
        (W1p.translate hkOmega v) := by
  rw [energyFormH1_zero_zero_eq_setIntegral, energyFormH1_zero_zero_eq_setIntegral]
  have hres : MeasurePreserving (· + h) (mu.restrict Omega) (mu.restrict Omega) :=
    by simpa only [← hOmega] using
      (measurePreserving_add_right mu h).restrict_preimage Omega.isOpen.measurableSet
  have hcancel : ∀ x : EuclideanSpace ℝ ι, x + h + k = x := fun x => by
    rw [add_assoc, hk, add_zero]
  have htr : ∀ (s : EuclideanSpace ℝ ι) (hs : MapsTo (· + s) Omega Omega)
      (z : W1p mu Omega 2),
      (W1p.gradient (W1p.translate hs z) :
        EuclideanSpace ℝ ι → EuclideanSpace ℝ ι)
        =ᵐ[mu.restrict Omega] fun x => W1p.gradient z (x + s) :=
    fun s hs z => W1p.gradient_translate_ae hs z
  calc ∫ x, matrixBilinearForm (a x) (W1p.gradient v x)
        (W1p.gradient (W1p.translate hh u) x) ∂mu.restrict Omega
      = ∫ x, matrixBilinearForm (a (x + h + k)) (W1p.gradient v (x + h + k))
          (W1p.gradient u (x + h)) ∂mu.restrict Omega := by
        refine integral_congr_ae ?_
        filter_upwards [htr h hh u] with x hx
        rw [hx, hcancel]
    _ = ∫ x, matrixBilinearForm (a (x + k)) (W1p.gradient v (x + k))
          (W1p.gradient u x) ∂mu.restrict Omega :=
        hres.integral_comp (Homeomorph.addRight h).measurableEmbedding
          (fun y => matrixBilinearForm (a (y + k)) (W1p.gradient v (y + k)) (W1p.gradient u y)
    _ = ∫ x, matrixBilinearForm (a (x + k))
          (W1p.gradient (W1p.translate hkOmega v) x)
          (W1p.gradient u x) ∂mu.restrict Omega := by
        refine integral_congr_ae ?_
        filter_upwards [htr k hkOmega v] with x hx
        rw [hx]

/-- **Translating a Lipschitz coefficient field moves the energy form by little.** If
`x ↦ a(x)` has essentially bounded energy densities and is `K`-Lipschitz in the operator norm
of its bilinear forms, then
translating it by `s` changes the energy form by at most `K ‖s‖ ‖∇y‖_{L²} ‖∇z‖_{L²}`. -/
theorem norm_energyFormH1_comp_add_sub_le
    (hcoeff : MemLp (fun x => energyIntegrand (a x) 0 0) ⊤
      (mu.restrict Omega))
    (hK : LipschitzOnWith K (fun x => matrixBilinearForm (a x)) Omega)
    (s : EuclideanSpace ℝ ι) (hOmega : (Omega : Set _) = (· + s) ⁻¹' Omega)
    (y z : W1p mu Omega 2) :
    ‖energyFormH1 (fun x => a (x + s)) 0 0 y z - energyFormH1 a 0 0 y z‖
      ≤ K * ‖s‖ * ‖W1p.gradient y‖ * ‖W1p.gradient z‖ := by
  -- The difference is the energy form of the difference of the coefficient fields.
  have hdiff : energyFormH1 (fun x => a (x + s)) 0 0 y z - energyFormH1 a 0 0 y z
      = ∫ x, (matrixBilinearForm (a (x + s)) - matrixBilinearForm (a x))
          (W1p.gradient z x) (W1p.gradient y x) ∂mu.restrict Omega := by
    simp only [energyFormH1_def, Pi.zero_apply]
    rw [← integral_sub
      (integrable_energyIntegrand_jetField
        (memLp_energyIntegrand_comp_add_right hcoeff s hOmega) y z)
      (integrable_energyIntegrand_jetField hcoeff y z)]
    simp
  -- The Lipschitz bound on the coefficient field, pointwise.
  have hpt : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)),
      ‖(matrixBilinearForm (a (x + s)) - matrixBilinearForm (a x))
      (W1p.gradient z x) (W1p.gradient y x)‖
        ≤ K * ‖s‖ * (‖W1p.gradient z x‖ * ‖W1p.gradient y x‖) := fun x hx => by
    have hxs : x + s ∈ Omega := by
      change x ∈ (· + s) ⁻¹' Omega
      rwa [← hOmega]
    calc _ ≤ ‖matrixBilinearForm (a (x + s)) - matrixBilinearForm (a x)‖
            * ‖W1p.gradient z x‖ * ‖W1p.gradient y x‖ := ContinuousLinearMap.le_opNorm₂ _ _ _
      _ ≤ K * ‖s‖ * ‖W1p.gradient z x‖ * ‖W1p.gradient y x‖ := by
          gcongr
          exact (hK.norm_sub_le hxs hx).trans_eq (by rw [add_sub_cancel_left])
      _ = _ := by ring
  -- Cauchy--Schwarz for the two gradients.
  have hmem : ∀ q : W1p mu Omega 2, MemLp (W1p.gradient q : EuclideanSpace ℝ ι →
      EuclideanSpace ℝ ι) (ENNReal.ofReal (2 : ℝ)) (mu.restrict Omega) := fun q => by
    simpa using Lp.memLp (W1p.gradient q)
  have hsq : ∀ q : W1p mu Omega 2,
      √(∫ x, ‖W1p.gradient q x‖ ^ 2 ∂mu.restrict Omega) = ‖W1p.gradient q‖ :=
    fun q => by
      have := W1p.integral_norm_gradient_sq_eq_norm_gradient_sq q
      rw [this, Real.sqrt_sq (norm_nonneg _)]
  have hCS := integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two (hmem z) (hmem y)
  simp only [Real.rpow_two, ← Real.sqrt_eq_rpow, hsq] at hCS
  have hint : Integrable (fun x => ‖W1p.gradient z x‖ * ‖W1p.gradient y x‖)
      (mu.restrict Omega) := by
    have hmem' : ∀ q : W1p mu Omega 2,
        MemLp (fun x => ‖W1p.gradient q x‖) 2 (mu.restrict Omega) := fun q => by
      simpa using (Lp.memLp (W1p.gradient q)).norm
    exact (hmem' z).integrable_mul (hmem' y)
  rw [hdiff]
  calc _ ≤ ∫ x, K * ‖s‖ * (‖W1p.gradient z x‖ * ‖W1p.gradient y x‖) ∂mu.restrict Omega :=
        norm_integral_le_of_norm_le (hint.const_mul _)
          ((ae_mem_restrict (mu := mu) (Omega := Omega)).mono fun x hx => hpt x hx)
    _ = K * ‖s‖ * ∫ x, ‖W1p.gradient z x‖ * ‖W1p.gradient y x‖ ∂mu.restrict Omega :=
        integral_const_mul _ _
    _ ≤ K * ‖s‖ * (‖W1p.gradient z‖ * ‖W1p.gradient y‖) := by gcongr
    _ = K * ‖s‖ * ‖W1p.gradient y‖ * ‖W1p.gradient z‖ := by ring

/-- **Discrete integration by parts for the energy form.** Testing the difference quotient of
`u` against `v` with the translated coefficients `aₜ = a(· + t w)` is, up to sign, testing `u`
against the difference quotient of `v` with the opposite step, plus a commutator term:

`aₜ(Dᵗ u, v) = -a(u, D⁻ᵗ v) - t⁻¹ (aₜ(u, v) - a(u, v))`.

This is the integrated form of the discrete product rule `Dᵗ(a ∇u) = aₜ Dᵗ∇u + (Dᵗ a) ∇u`. For
constant coefficients the commutator vanishes and the identity reads `a(Dᵗ u, v) = -a(u, D⁻ᵗ v)`.
The hypothesis on the coefficients makes the energy form bilinear and continuous on `H¹(ℝⁿ)`. -/
theorem energyFormH1_differenceQuotient_eq_neg_sub
    (hcoeff : MemLp (fun x => energyIntegrand (a x) 0 0) ⊤
      (mu.restrict ((⊤ : Opens (EuclideanSpace ℝ ι)) : Set (EuclideanSpace ℝ ι))))
    (w : EuclideanSpace ℝ ι) (t : ℝ) (u v : W1p mu ⊤ 2) :
    energyFormH1 (fun x => a (x + t • w)) 0 0
        (W1p.differenceQuotient le_rfl w t (Set.mapsTo_univ (· + t • w) _) u) v
      = -energyFormH1 a 0 0 u
          (W1p.differenceQuotient le_rfl w (-t) (Set.mapsTo_univ (· + (-t) • w) _) v)
        - t⁻¹ * (energyFormH1 (fun x => a (x + t • w)) 0 0 u v - energyFormH1 a 0 0 u v) := by
  have hcoeff' := memLp_energyIntegrand_comp_add_right hcoeff (t • w) (by ext x; simp)
  have hk : t • w + (-t) • w = 0 := by rw [← add_smul]; simp
  have htranslate := energyFormH1_translate (fun x => a (x + t • w)) hk
    (by ext x; simp) (hh := Set.mapsTo_univ _ _) (hkOmega := Set.mapsTo_univ _ _) u v
  have hcancel : (-t) • w + t • w = 0 := by rw [← add_smul]; simp
  simp only [add_assoc, hcancel, add_zero] at htranslate
  rw [energyFormH1_differenceQuotient_left (b := 0) (c := 0) hcoeff',
    energyFormH1_differenceQuotient_right (b := 0) (c := 0) hcoeff, htranslate, inv_neg]
  ring

/-- **The commutator of the energy form with a translation.** If the bilinear forms of the
coefficient field are `K`-Lipschitz in operator norm, then translating the coefficients by `t w`
changes the energy form by at most `K |t| ‖w‖ ‖∇u‖_{L²} ‖∇v‖_{L²}`:

`|t⁻¹ (aₜ(u, v) - a(u, v))| ≤ K ‖w‖ ‖∇v‖_{L²} ‖∇u‖_{L²}`, where `aₜ = a(· + t w)`.

This bounds the commutator term of `TauCeti.PDE.energyFormH1_differenceQuotient_eq_neg_sub`
uniformly in `t`. The hypothesis on the coefficients makes both energy densities integrable. -/
theorem norm_inv_mul_energyFormH1_comp_add_sub_le
    (hcoeff : MemLp (fun x => energyIntegrand (a x) 0 0) ⊤
      (mu.restrict ((⊤ : Opens (EuclideanSpace ℝ ι)) : Set (EuclideanSpace ℝ ι))))
    (hLip : LipschitzWith K fun x => matrixBilinearForm (a x)) (w : EuclideanSpace ℝ ι) (t : ℝ)
    (u v : W1p mu ⊤ 2) :
    ‖t⁻¹ * (energyFormH1 (fun x => a (x + t • w)) 0 0 u v - energyFormH1 a 0 0 u v)‖
      ≤ K * ‖w‖ * (‖W1p.gradient v‖ * ‖W1p.gradient u‖) := by
  rcases eq_or_ne t 0 with rfl | ht
  · simp only [inv_zero, zero_mul, norm_zero]
    positivity
  rw [norm_mul, norm_inv, Real.norm_eq_abs]
  calc |t|⁻¹ * ‖energyFormH1 (fun x => a (x + t • w)) 0 0 u v - energyFormH1 a 0 0 u v‖
      ≤ |t|⁻¹ * (K * ‖t • w‖ * ‖W1p.gradient u‖ * ‖W1p.gradient v‖) := by
        gcongr
        exact norm_energyFormH1_comp_add_sub_le hcoeff hLip.lipschitzOnWith
          (t • w) (by ext x; simp) u v
    _ = K * ‖w‖ * (‖W1p.gradient v‖ * ‖W1p.gradient u‖) := by
        rw [norm_smul, Real.norm_eq_abs]
        field_simp [abs_ne_zero.mpr ht]

end TauCeti.PDE
