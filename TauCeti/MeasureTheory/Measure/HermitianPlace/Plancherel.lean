/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.HermitianPlace.Basic
import TauCeti.MeasureTheory.Integral.Pi
import TauCeti.MeasureTheory.Integral.SchurTest

/-!
# Plancherel's inequality at a place

Let `A` be a place (`TauCeti.HermitianPlace`), `ι` a finite type, and `v*w = ∑ i, star vᵢ * wᵢ` the
standard hermitian pairing of `A^ι`, written `star v ⬝ᵥ w`. For a unit `η` and an integrable
`f : A^ι → ℂ`, **Plancherel's inequality**

`∫ |∫ ψ(η · v*w) f(w) dw|² dv ≤ (c_A / mod η) ^ |ι| · ∫ |f|²`

holds (`TauCeti.HermitianPlace.lintegral_enorm_integral_sq_le`), where `c_A` is the Plancherel
constant of the place. No Fourier inversion is part of the axioms of a place: the inequality is
derived from the damping kernel `G` alone.

The proof damps the integrand. For an integrable weight `W ≥ 0`, expanding the square and
integrating in `v` first writes `∫ W(v) |F(v)|² dv` as `∫∫ f(w) conj f(w') K_W(w - w') dw dw'` with
`K_W(z) = ∫ W(v) ψ(η · v*z) dv`, and Schur's test bounds this by `‖K_W‖₁ · ∫ |f|²`
(`TauCeti.HermitianPlace.lintegral_ofReal_mul_enorm_integral_sq_le`). For the weight
`W(v) = ∏ᵢ G(u vᵢ)`, with `G` the damping kernel of the place and `u` a unit, the change of
variables `v ↦ u v` shows `‖K_W‖₁ ≤ (c_A / mod η) ^ |ι|` for every `u`. As `u` tends to `0`
through units, `W` tends to `1` pointwise, and Fatou's lemma removes the damping.

More generally, for a matrix `J`, measures `ρ`, `ρ'` and sets `S`, `S'`, the kernel `ψ(ξ · v*Jy)`
*multiplies square norms by at most `C`* from `(S, ρ)` to `(S', ρ')`
(`TauCeti.HermitianPlace.FourierSqNormLe`) if
`∫_{S'} |∫ ψ(ξ · v*Jy) φ(y) dρ(y)|² dρ'(v) ≤ C ∫ |φ|² dρ` for measurable `ρ`-integrable `φ`
vanishing off `S`. Plancherel's inequality is the case of the identity matrix and Haar measure
(`TauCeti.HermitianPlace.fourierSqNormLe_one`).

## Main definitions

* `TauCeti.HermitianPlace.FourierSqNormLe`: bounds for the kernel `ψ(ξ · v*Jy)` on `L²`.

## Main results

* `TauCeti.HermitianPlace.continuous_integral_ψ_mul`: the transform of an integrable function is
  continuous.
* `TauCeti.HermitianPlace.lintegral_ofReal_mul_enorm_integral_sq_le`: the damped inequality.
* `TauCeti.HermitianPlace.lintegral_enorm_integral_sq_le`: Plancherel's inequality.
* `TauCeti.HermitianPlace.fourierSqNormLe_one`: Plancherel's inequality as a kernel bound.

## References

* W. Rudin, *Fourier Analysis on Groups*, Interscience (1962), §1.6: Plancherel's theorem on
  locally compact abelian groups.

The damping argument is that of the Lean project grh-lean (https://github.com/lsernau/grh-lean,
Apache 2.0, Copyright 2026 Anthropic, PBC), declaration `New.Floors.Place.plancherel_inequality`
in `src/Lib/DiscreteSeries/Bruhat/FloorMeasures.lean`; the kernel bounds follow
`New.Floors.Place.FourierSqNormLe` in `src/Lib/DiscreteSeries/Bruhat/FourierKernels.lean`.
-/

public section

open MeasureTheory Matrix Filter Topology ComplexConjugate
open scoped ENNReal

namespace TauCeti.HermitianPlace

variable {A : Type*} [CommRing A] [StarRing A] [TopologicalSpace A] [MeasureSpace A]
  (P : HermitianPlace A) {ι : Type*} [Fintype ι]

/-- The kernel of a real weight is conjugated by `z ↦ -z`. -/
private theorem integral_mul_ψ_neg (η : A) (W : (ι → A) → ℝ) (z : ι → A) :
    ∫ v, (W v : ℂ) * P.ψ (η * (star v ⬝ᵥ -z)) =
      conj (∫ v, (W v : ℂ) * P.ψ (η * (star v ⬝ᵥ z))) := by
  rw [← integral_conj]
  refine integral_congr_ae (Eventually.of_forall fun v ↦ ?_)
  simp only [dotProduct_neg, mul_neg, AddChar.map_neg_eq_inv, Circle.coe_inv_eq_conj, map_mul,
    Complex.conj_ofReal]

/-- The kernel `ψ(ξ · v*Jy)` **multiplies square norms by at most `C`** from `(S, ρ)` to
`(S', ρ')` if `∫_{S'} |∫ ψ(ξ · v*Jy) φ(y) dρ(y)|² dρ'(v) ≤ C · ∫ |φ|² dρ` for every measurable
`ρ`-integrable `φ` vanishing off `S`. -/
def FourierSqNormLe (J : Matrix ι ι A) (ξ : A) (ρ ρ' : Measure (ι → A)) (S S' : Set (ι → A))
    (C : ℝ≥0∞) : Prop :=
  ∀ φ : (ι → A) → ℂ, Measurable φ → Integrable φ ρ → (∀ y ∉ S, φ y = 0) →
    ∫⁻ v in S', ‖∫ y, (P.ψ (ξ * (star v ⬝ᵥ J *ᵥ y)) : ℂ) * φ y ∂ρ‖ₑ ^ 2 ∂ρ' ≤
      C * ∫⁻ y, ‖φ y‖ₑ ^ 2 ∂ρ

/-- A kernel bound persists for smaller sets and a larger constant. -/
theorem FourierSqNormLe.mono {J : Matrix ι ι A} {ξ : A} {ρ ρ' : Measure (ι → A)}
    {S S' T T' : Set (ι → A)} {C C' : ℝ≥0∞} (h : P.FourierSqNormLe J ξ ρ ρ' S S' C)
    (hT : T ⊆ S) (hT' : T' ⊆ S') (hC : C ≤ C') : P.FourierSqNormLe J ξ ρ ρ' T T' C' :=
  fun φ hφm hφ hφT ↦ (lintegral_mono_set hT').trans <|
    (h φ hφm hφ fun y hy ↦ hφT y fun hyT ↦ hy (hT hyT)).trans (by gcongr)

variable [IsTopologicalRing A] [ContinuousStar A] [SecondCountableTopology A] [BorelSpace A]

/-- The transform `v ↦ ∫ ψ(η · v*w) f(w) dw` of an integrable function `f` on `A^ι` is
continuous. -/
theorem continuous_integral_ψ_mul (η : A) {f : (ι → A) → ℂ} (hf : Integrable f) :
    Continuous fun v : ι → A ↦ ∫ w, (P.ψ (η * (star v ⬝ᵥ w)) : ℂ) * f w := by
  have he := P.continuous_ψ_mul_dotProduct (ι := ι) η
  refine continuous_of_dominated (bound := fun w ↦ ‖f w‖) (fun v ↦ ?_) (fun v ↦ ?_) hf.norm ?_
  · exact (he.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable.mul
      hf.aestronglyMeasurable
  · exact Eventually.of_forall fun w ↦ by simp
  · exact Eventually.of_forall fun w ↦
      (he.comp (continuous_id.prodMk continuous_const)).mul continuous_const

/-- The kernel `z ↦ ∫ W(v) ψ(η · v*z) dv` of an integrable weight is continuous. -/
private theorem continuous_integral_mul_ψ (η : A) {W : (ι → A) → ℝ} (hW : Integrable W) :
    Continuous fun z : ι → A ↦ ∫ v, (W v : ℂ) * P.ψ (η * (star v ⬝ᵥ z)) := by
  have he := P.continuous_ψ_mul_dotProduct (ι := ι) η
  refine continuous_of_dominated (bound := fun v ↦ ‖W v‖) (fun z ↦ ?_) (fun z ↦ ?_) hW.norm ?_
  · exact (Complex.continuous_ofReal.comp_aestronglyMeasurable hW.aestronglyMeasurable).mul
      (he.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable
  · exact Eventually.of_forall fun v ↦ by simp
  · exact Eventually.of_forall fun v ↦
      continuous_const.mul (he.comp (continuous_const.prodMk continuous_id))

variable [LocallyCompactSpace A] [(volume : Measure A).IsAddHaarMeasure]

/-- Expanding the square and integrating in `v` first: `∫ W(v) |F(v)|² dv` is
`∫∫ f(w) conj f(w') K_W(w - w') dw dw'`. -/
private theorem integral_mul_mul_conj_eq (η : A) {W : (ι → A) → ℝ} (hW : Integrable W)
    {f : (ι → A) → ℂ} (hf : Integrable f) :
    ∫ v, (W v : ℂ) * ((∫ w, (P.ψ (η * (star v ⬝ᵥ w)) : ℂ) * f w) *
        conj (∫ w, (P.ψ (η * (star v ⬝ᵥ w)) : ℂ) * f w)) =
      ∫ p : (ι → A) × (ι → A),
        f p.1 * conj (f p.2) * ∫ v, (W v : ℂ) * P.ψ (η * (star v ⬝ᵥ (p.1 - p.2))) := by
  set e : (ι → A) → (ι → A) → ℂ := fun v w ↦ P.ψ (η * (star v ⬝ᵥ w))
  have he : Continuous (Function.uncurry e) := P.continuous_ψ_mul_dotProduct η
  have hFF (v : ι → A) : (∫ w, e v w * f w) * conj (∫ w, e v w * f w) =
      ∫ p : (ι → A) × (ι → A), e v p.1 * f p.1 * conj (e v p.2 * f p.2) := by
    rw [Measure.volume_eq_prod,
      integral_prod_mul (fun w ↦ e v w * f w) (fun w ↦ conj (e v w * f w)), integral_conj]
  have he' (g : (ι → A) × ((ι → A) × (ι → A)) → (ι → A) × (ι → A)) (hg : Continuous g) :
      AEStronglyMeasurable (fun q ↦ e (g q).1 (g q).2) (volume.prod volume) :=
    (he.comp hg).aestronglyMeasurable
  have hint : Integrable (Function.uncurry fun v (p : (ι → A) × (ι → A)) ↦
      (W v : ℂ) * (e v p.1 * f p.1 * conj (e v p.2 * f p.2))) (volume.prod volume) := by
    refine (hW.norm.mul_prod (hf.norm.mul_prod hf.norm)).mono' ?_ (Eventually.of_forall fun q ↦ ?_)
    · exact (Complex.continuous_ofReal.comp_aestronglyMeasurable
        hW.aestronglyMeasurable).comp_fst.mul
        (((he' (fun q ↦ (q.1, q.2.1)) (by fun_prop)).mul
          hf.aestronglyMeasurable.comp_fst.comp_snd).mul
        (Complex.continuous_conj.comp_aestronglyMeasurable
          ((he' (fun q ↦ (q.1, q.2.2)) (by fun_prop)).mul
            hf.aestronglyMeasurable.comp_snd.comp_snd)))
    · obtain ⟨v, w, w'⟩ := q
      refine le_of_eq ?_
      simp only [Function.uncurry_apply_pair, norm_mul, RCLike.norm_conj, Complex.norm_real, e,
        Circle.norm_coe]
      ring
  calc ∫ v, (W v : ℂ) * ((∫ w, e v w * f w) * conj (∫ w, e v w * f w))
      = ∫ v, ∫ p : (ι → A) × (ι → A),
          (W v : ℂ) * (e v p.1 * f p.1 * conj (e v p.2 * f p.2)) := by
        simp_rw [hFF, integral_const_mul]
    _ = ∫ p : (ι → A) × (ι → A), ∫ v,
          (W v : ℂ) * (e v p.1 * f p.1 * conj (e v p.2 * f p.2)) :=
        integral_integral_swap hint
    _ = _ := by
        refine integral_congr_ae (Eventually.of_forall fun p ↦ ?_)
        simp only [← integral_const_mul]
        refine integral_congr_ae (Eventually.of_forall fun v ↦ ?_)
        beta_reduce
        rw [← P.ψ_mul_dotProduct_mul_conj, map_mul]
        ring

/-- **Damped Plancherel inequality.** For an integrable weight `W ≥ 0` on `A^ι` and an
integrable `f`, `∫ W(v) |∫ ψ(η · v*w) f(w) dw|² dv ≤ ‖K_W‖₁ ∫ |f|²`, where
`K_W(z) = ∫ W(v) ψ(η · v*z) dv`. -/
theorem lintegral_ofReal_mul_enorm_integral_sq_le (η : A) {W : (ι → A) → ℝ}
    (hW0 : ∀ v, 0 ≤ W v) (hW : Integrable W) {f : (ι → A) → ℂ} (hf : Integrable f) :
    ∫⁻ v, ENNReal.ofReal (W v) * ‖∫ w, (P.ψ (η * (star v ⬝ᵥ w)) : ℂ) * f w‖ₑ ^ 2 ≤
      (∫⁻ z, ‖∫ v, (W v : ℂ) * P.ψ (η * (star v ⬝ᵥ z))‖ₑ) * ∫⁻ w, ‖f w‖ₑ ^ 2 := by
  set F : (ι → A) → ℂ := fun v ↦ ∫ w, (P.ψ (η * (star v ⬝ᵥ w)) : ℂ) * f w
  set K : (ι → A) → ℂ := fun z ↦ ∫ v, (W v : ℂ) * P.ψ (η * (star v ⬝ᵥ z))
  have hF_le (v : ι → A) : ‖F v‖ ≤ ∫ w, ‖f w‖ :=
    (norm_integral_le_integral_norm _).trans_eq (by simp)
  -- The left side is the norm of the complex integral `∫ W F conj F`.
  have hint : Integrable fun v ↦ W v * ‖F v‖ ^ 2 := by
    refine (hW.mul_const ((∫ w, ‖f w‖) ^ 2)).mono' (hW.aestronglyMeasurable.mul
      ((P.continuous_integral_ψ_mul η hf).norm.pow 2).aestronglyMeasurable)
      (Eventually.of_forall fun v ↦ ?_)
    rw [Real.norm_of_nonneg (mul_nonneg (hW0 v) (by positivity))]
    gcongr
    exacts [hW0 v, hF_le v]
  have hreal : ∫ v, (W v : ℂ) * (F v * conj (F v)) = ((∫ v, W v * ‖F v‖ ^ 2 : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    exact integral_congr_ae (Eventually.of_forall fun v ↦ by simp [RCLike.mul_conj])
  have h1 : ∫⁻ v, ENNReal.ofReal (W v) * ‖F v‖ₑ ^ 2 = ‖∫ v, (W v : ℂ) * (F v * conj (F v))‖ₑ := by
    rw [hreal, ← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg (integral_nonneg fun v ↦ by
      have := hW0 v; positivity), ofReal_integral_eq_lintegral_ofReal hint
      (Eventually.of_forall fun v ↦ by have := hW0 v; positivity)]
    refine lintegral_congr fun v ↦ ?_
    rw [ENNReal.ofReal_mul (hW0 v), ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
  -- Fubini, then Schur's test for the symmetric kernel `‖K (x - y)‖`.
  have hK : Continuous K := P.continuous_integral_mul_ψ η hW
  have hfm : AEMeasurable (fun x ↦ ‖f x‖ₑ) := hf.aestronglyMeasurable.eNorm
  calc ∫⁻ v, ENNReal.ofReal (W v) * ‖F v‖ₑ ^ 2
      = ‖∫ p : (ι → A) × (ι → A), f p.1 * conj (f p.2) * K (p.1 - p.2)‖ₑ := by
        rw [h1, P.integral_mul_mul_conj_eq η hW hf]
    _ ≤ ∫⁻ p : (ι → A) × (ι → A), ‖f p.1‖ₑ * (‖K (p.1 - p.2)‖ₑ * ‖f p.2‖ₑ) := by
        refine (eNorm_integral_le_lintegral_eNorm _).trans (le_of_eq (lintegral_congr fun p ↦ ?_))
        rw [eNorm_mul, eNorm_mul, RCLike.eNorm_conj]
        ring
    _ = ∫⁻ x, ∫⁻ y, ‖f x‖ₑ * (‖K (x - y)‖ₑ * ‖f y‖ₑ) := by
        rw [Measure.volume_eq_prod, lintegral_prod _ ?_]
        have hk : AEMeasurable (fun p : (ι → A) × (ι → A) ↦ ‖K (p.1 - p.2)‖ₑ)
            (volume.prod volume) := (hK.comp continuous_sub).eNorm.measurable.aemeasurable
        exact hfm.comp_fst.mul (hk.mul hfm.comp_snd)
    _ ≤ (∫⁻ z, ‖K z‖ₑ) * ∫⁻ w, ‖f w‖ₑ ^ 2 :=
        lintegral_lintegral_mul_sub_mul_le hK.eNorm.measurable
          (fun z ↦ by rw [show K (-z) = conj (K z) from P.integral_mul_ψ_neg η W z,
            RCLike.eNorm_conj]) hfm

/-- The transform `z ↦ ∫ ∏ᵢ G(vᵢ) ψ(v*z) dv` of a product of damping kernels has `L¹` norm at most
`c ^ |ι|` when the transform of `G` has `L¹` norm at most `c`. -/
private theorem lintegral_enorm_integral_prod_mul_ψ_le {G : A → ℝ} (hGc : Continuous G)
    (hGi : Integrable G) {c : ℝ≥0∞} (hG : ∫⁻ w, ‖∫ v, (G v : ℂ) * P.ψ (star v * w)‖ₑ ≤ c) :
    ∫⁻ z : ι → A, ‖∫ v, ((∏ i, G (v i) : ℝ) : ℂ) * P.ψ (star v ⬝ᵥ z)‖ₑ ≤ c ^ Fintype.card ι := by
  set Ghat : A → ℂ := fun w ↦ ∫ v, (G v : ℂ) * P.ψ (star v * w)
  have hψ (v : A) : Continuous fun w : A ↦ (P.ψ (star v * w) : ℂ) :=
    continuous_subtypeVal.comp (P.continuous_ψ.comp (continuous_const.mul continuous_id))
  have hGhat : Continuous Ghat := by
    refine continuous_of_dominated (bound := fun v ↦ ‖G v‖) (fun w ↦ ?_) (fun w ↦ ?_) hGi.norm
      (Eventually.of_forall fun v ↦ continuous_const.mul (hψ v))
    · exact (Complex.continuous_ofReal.comp hGc).mul (continuous_subtypeVal.comp
        (P.continuous_ψ.comp (continuous_star.mul continuous_const))) |>.aestronglyMeasurable
    · exact Eventually.of_forall fun v ↦ by simp
  have hprod (z : ι → A) :
      ∫ v, ((∏ i, G (v i) : ℝ) : ℂ) * P.ψ (star v ⬝ᵥ z) = ∏ i, Ghat (z i) := by
    have hsum (g : ι → A) : P.ψ (∑ i, g i) = ∏ i, P.ψ (g i) := by
      simpa only [AddChar.toMonoidHom_apply, ← ofAdd_sum, toAdd_ofAdd] using
        map_prod P.ψ.toMonoidHom (fun i ↦ Multiplicative.ofAdd (g i)) Finset.univ
    rw [← integral_fintype_prod_volume_eq_prod]
    refine integral_congr_ae (Eventually.of_forall fun v ↦ ?_)
    have hcoe (g : ι → Circle) : ((∏ i, g i : Circle) : ℂ) = ∏ i, (g i : ℂ) :=
      map_prod Circle.coeHom g _
    simp [dotProduct, hsum, hcoe, Finset.prod_mul_distrib]
  calc ∫⁻ z : ι → A, ‖∫ v, ((∏ i, G (v i) : ℝ) : ℂ) * P.ψ (star v ⬝ᵥ z)‖ₑ
      = ∫⁻ z : ι → A, ∏ i, ‖Ghat (z i)‖ₑ := by
        refine lintegral_congr fun z ↦ ?_
        simp only [hprod, eNorm_eq_nnNorm, nnNorm_prod, ENNReal.ofNNReal_finsetProd]
    _ = ∏ _i : ι, ∫⁻ w, ‖Ghat w‖ₑ :=
        TauCeti.lintegral_fintype_prod_eq_prod (fun _ ↦ volume) fun _ ↦ hGhat.eNorm.measurable
    _ ≤ c ^ Fintype.card ι := by
        rw [Finset.prod_const, Finset.card_univ]
        exact pow_le_pow_left' hG _

omit [ContinuousStar A] in
/-- Damping by `v ↦ u • v` for a unit `u` leaves the `L¹` norm of the transform unchanged, and a
unit frequency `η` divides it by `mod η ^ |ι|`. -/
private theorem lintegral_enorm_integral_comp_smul_mul_ψ (η u : Aˣ) (D : (ι → A) → ℂ) :
    ∫⁻ z, ‖∫ v, D ((u : A) • v) * P.ψ (η * (star v ⬝ᵥ z))‖ₑ =
      (P.modulus η)⁻¹ ^ Fintype.card ι * ∫⁻ z, ‖∫ v, D v * P.ψ (star v ⬝ᵥ z)‖ₑ := by
  set a : Aˣ := η * star u⁻¹
  have hpt (z : ι → A) : ∫ v, D ((u : A) • v) * P.ψ (η * (star v ⬝ᵥ z)) =
      ((P.modulus u)⁻¹ ^ Fintype.card ι).toReal • ∫ v, D v * P.ψ (star v ⬝ᵥ ((a : A) • z)) := by
    rw [← P.integral_comp_smul u]
    refine integral_congr_ae (Eventually.of_forall fun v ↦ ?_)
    have : star ((u : A) • v) ⬝ᵥ ((a : A) • z) = η * (star v ⬝ᵥ z) := by
      simp only [a, star_smul, smul_dotProduct, dotProduct_smul, Units.val_mul, Units.coe_star,
        smul_eq_mul]
      rw [← mul_assoc, mul_assoc (η : A), ← star_mul, Units.mul_inv, star_one, mul_one]
    beta_reduce
    rw [this]
  have hmu0 := P.modulus_units_ne_zero u
  have hmut := P.modulus_units_ne_top u
  have ha : (P.modulus a)⁻¹ = (P.modulus η)⁻¹ * P.modulus u := by
    simp only [a, Units.val_mul, Units.coe_star, map_mul, P.modulus_star, P.modulus_units_inv]
    rw [ENNReal.mul_inv (Or.inr (ENNReal.inv_ne_top.2 hmu0)) (Or.inl (P.modulus_units_ne_top η)),
      inv_inv]
  have hr : ‖((P.modulus u)⁻¹ ^ Fintype.card ι).toReal‖ₑ = (P.modulus u)⁻¹ ^ Fintype.card ι := by
    rw [Real.eNorm_eq_ofReal ENNReal.toReal_nonneg, ENNReal.ofReal_toReal
      (ENNReal.pow_ne_top (ENNReal.inv_ne_top.2 hmu0))]
  simp_rw [hpt, eNorm_smul, hr]
  rw [lintegral_const_mul' _ _ (ENNReal.pow_ne_top (ENNReal.inv_ne_top.2 hmu0)),
    P.lintegral_comp_smul a (fun z ↦ ‖∫ v, D v * P.ψ (star v ⬝ᵥ z)‖ₑ), ha]
  calc (P.modulus u)⁻¹ ^ Fintype.card ι * (((P.modulus η)⁻¹ * P.modulus u) ^ Fintype.card ι *
        ∫⁻ z, ‖∫ v, D v * P.ψ (star v ⬝ᵥ z)‖ₑ)
      = ((P.modulus u)⁻¹ * P.modulus u) ^ Fintype.card ι * ((P.modulus η)⁻¹ ^ Fintype.card ι *
          ∫⁻ z, ‖∫ v, D v * P.ψ (star v ⬝ᵥ z)‖ₑ) := by ring
    _ = _ := by rw [ENNReal.inv_mul_cancel hmu0 hmut, one_pow, one_mul]

/-- **Plancherel's inequality** at a place: for a unit `η` and an integrable function `f` on
`A^ι`, `∫ |∫ ψ(η · v*w) f(w) dw|² dv ≤ (c_A / mod η) ^ |ι| · ∫ |f|²`, where
`v*w = ∑ᵢ star vᵢ * wᵢ` and
`c_A` is the Plancherel constant of the place. -/
theorem lintegral_enorm_integral_sq_le (η : Aˣ) {f : (ι → A) → ℂ} (hf : Integrable f) :
    ∫⁻ v, ‖∫ w, (P.ψ (η * (star v ⬝ᵥ w)) : ℂ) * f w‖ₑ ^ 2 ≤
      (P.plancherelConst / P.modulus η) ^ Fintype.card ι * ∫⁻ w, ‖f w‖ₑ ^ 2 := by
  obtain ⟨G, hGc, hGi, hG0, hG1, hG⟩ := P.exists_damping_kernel
  obtain ⟨u, hu⟩ := P.exists_seq_units_tendsto_zero
  set F : (ι → A) → ℂ := fun v ↦ ∫ w, (P.ψ (η * (star v ⬝ᵥ w)) : ℂ) * f w
  set D : (ι → A) → ℝ := fun v ↦ ∏ i, G (v i)
  have hD : Integrable D := Integrable.fintype_prod fun _ ↦ hGi
  have hDc : Continuous D := continuous_finsetProd _ fun i _ ↦ hGc.comp (continuous_apply i)
  -- The damped weights `v ↦ D (u n • v)`.
  have hW (n : ℕ) : Integrable fun v ↦ D ((u n : A) • v) := by
    have he : MeasurableEmbedding ((u n : A) • · : (ι → A) → ι → A) :=
      (Homeomorph.smul (u n)).measurableEmbedding
    refine (he.integrable_map_iff (g := D)).mp ?_
    rw [P.map_smul_volume]
    exact hD.smul_measure (ENNReal.pow_ne_top (ENNReal.inv_ne_top.2 (P.modulus_units_ne_zero _)))
  have hbound (n : ℕ) : ∫⁻ v, ENNReal.ofReal (D ((u n : A) • v)) * ‖F v‖ₑ ^ 2 ≤
      (P.plancherelConst / P.modulus η) ^ Fintype.card ι * ∫⁻ w, ‖f w‖ₑ ^ 2 := by
    refine (P.lintegral_ofReal_mul_enorm_integral_sq_le η
      (fun v ↦ Finset.prod_nonneg fun i _ ↦ hG0 _) (hW n) hf).trans (mul_le_mul_left ?_ _)
    have := P.lintegral_enorm_integral_comp_smul_mul_ψ η (u n) (fun v ↦ (D v : ℂ))
    simp only [D] at this ⊢
    rw [this, div_eq_mul_inv, mul_pow, mul_comm]
    exact mul_le_mul_left (P.lintegral_enorm_integral_prod_mul_ψ_le hGc hGi hG) _
  -- As `u n → 0`, the weights tend to `D 0 = 1`, and Fatou's lemma removes them.
  have hlim (v : ι → A) : Tendsto (fun n ↦ ENNReal.ofReal (D ((u n : A) • v)) * ‖F v‖ₑ ^ 2)
      atTop (𝓝 (‖F v‖ₑ ^ 2)) := by
    have h0 : Tendsto (fun n ↦ D ((u n : A) • v)) atTop (𝓝 1) := by
      have := (hDc.tendsto 0).comp ((hu.smul_const v).trans (by rw [zero_smul]))
      simpa [D, hG1, Function.comp_def] using this
    simpa using ENNReal.Tendsto.mul_const (ENNReal.tendsto_ofReal h0) (Or.inl (by simp))
  have hmeas (n : ℕ) : AEMeasurable fun v ↦ ENNReal.ofReal (D ((u n : A) • v)) * ‖F v‖ₑ ^ 2 :=
    ((ENNReal.measurable_ofReal.comp (hDc.comp (continuous_const_smul _)).measurable).mul
      ((P.continuous_integral_ψ_mul η hf).eNorm.measurable.pow_const 2)).aemeasurable
  calc ∫⁻ v, ‖F v‖ₑ ^ 2
      = ∫⁻ v, liminf (fun n ↦ ENNReal.ofReal (D ((u n : A) • v)) * ‖F v‖ₑ ^ 2) atTop :=
        lintegral_congr fun v ↦ (hlim v).liminf_eq.symm
    _ ≤ liminf (fun n ↦ ∫⁻ v, ENNReal.ofReal (D ((u n : A) • v)) * ‖F v‖ₑ ^ 2) atTop :=
        lintegral_liminf_le' hmeas
    _ ≤ _ := liminf_le_of_frequently_le' (Frequently.of_forall hbound)

/-- Plancherel's inequality as a kernel bound: for a unit `η`, the kernel `ψ(η · v*y)` multiplies
square norms on Haar measure of `A^ι` by at most `(c_A / mod η) ^ |ι|`. -/
theorem fourierSqNormLe_one [DecidableEq ι] (η : Aˣ) :
    P.FourierSqNormLe (1 : Matrix ι ι A) η volume volume Set.univ Set.univ
      ((P.plancherelConst / P.modulus η) ^ Fintype.card ι) :=
  fun _ _ hφ _ ↦ by simpa using P.lintegral_enorm_integral_sq_le η hφ

end TauCeti.HermitianPlace
