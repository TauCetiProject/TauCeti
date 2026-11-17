/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Analytic.OfScalars
public import TauCeti.Analysis.Normed.Algebra.HolomorphicFunctionalCalculus.Basic
import Mathlib.Analysis.Complex.RemovableSingularity

/-!
# Spectral mapping, elementary agreement, commutation, and naturality

For an element `a` of a complex Banach algebra `A`, this file establishes the fundamental
algebraic, spectral, and analytic properties of `holomorphicCalculus a` and
`holomorphicCalculusOn a U ha`:

* **Algebraic consequences of sending the coordinate germ to `a`:** any unital complex-algebra
  homomorphism `Φ : holomorphicGerms (spectrum ℂ a) →ₐ[ℂ] A` sending the coordinate germ to `a`
  sends `z ↦ (w - z)⁻¹` to `resolvent a w` (and `z ↦ (z - w)⁻¹` to `-resolvent a w`) and satisfies
  the **spectral mapping theorem** `spectrum ℂ (Φ g) = spectrum ℂ g` (complementing the general
  germ-algebra formulas `holomorphicGerms.algHom_ofFun_polynomial` and
  `holomorphicGerms.algHom_ofFun_div`).
* **Spectral mapping theorem:** `spectrum ℂ (holomorphicCalculus a g)` is the set of point values
  of `g` on `spectrum ℂ a`, and `spectrum ℂ (holomorphicCalculusOn a U ha f) = extend f ''
  spectrum ℂ a`. Neither nontriviality of `A` nor `‖1‖ = 1` is assumed.
* **Commutation:** every element commuting with `a` commutes with `holomorphicCalculusOn a U ha f`
  and `holomorphicCalculus a g`, so all values of the calculus lie in the bicommutant of `a`.
* **Convergent power series:** if `f` has formal power series `p` on an open ball `B(z₀, r)`
  containing `spectrum ℂ a`, then `fun n ↦ p.coeff n • (a - algebraMap ℂ A z₀) ^ n` is
  norm-summable in `A` with sum `holomorphicCalculus a (ofFun f _)`.
* **Naturality and scalar evaluation:** continuous unital complex-algebra homomorphisms intertwine
  `holomorphicCalculusOn` and `holomorphicCalculus`, and in `ℂ` itself `holomorphicCalculus z` is
  point evaluation at `z`.

## References

* H. G. Dales, *Banach Algebras and Automatic Continuity*, §2.4.
* J. B. Conway, *A Course in Functional Analysis*, second edition, VII.4.
-/

public noncomputable section

open Complex Filter Metric Set TopologicalSpace Topology
open scoped NNReal ENNReal Real

namespace TauCeti

open Contour HolomorphicFunctions

/-! ### Algebraic consequences of sending the coordinate germ to `a` -/

section Algebraic

variable {A : Type*} [Ring A] [Algebra ℂ A] {a : A}
  {Φ : holomorphicGerms (spectrum ℂ a) →ₐ[ℂ] A}

/-- `z ↦ (w - z)⁻¹` is analytic near `spectrum ℂ a` if and only if `w ∈ resolventSet ℂ a`. -/
theorem analyticOnNhd_sub_inv_left_iff {a : A} {w : ℂ} :
    AnalyticOnNhd ℂ (fun z => (w - z)⁻¹) (spectrum ℂ a) ↔ w ∈ resolventSet ℂ a := by
  refine ⟨fun hf => spectrum.notMem_iff.mp fun hw => ?_, fun hw _ hz => ?_⟩
  · have hc : ContinuousAt (fun z : ℂ => (w - z)⁻¹) (w - 0) := by
      simpa using (hf w hw).continuousAt
    have h0 : ContinuousAt (fun z : ℂ => w - z) 0 :=
      (continuous_const.sub continuous_id).continuousAt
    have hinv : ContinuousAt (Inv.inv : ℂ → ℂ) 0 :=
      (hc.comp h0).congr (Eventually.of_forall fun z => by simp)
    exact NormedField.continuousAt_inv.mp hinv rfl
  · exact (analyticAt_const.sub analyticAt_id).inv
      (sub_ne_zero.mpr fun h => by dsimp at h; exact spectrum.notMem_iff.mpr hw (h ▸ hz))

/-- `z ↦ (z - w)⁻¹` is analytic near `spectrum ℂ a` if and only if `w ∈ resolventSet ℂ a`. -/
theorem analyticOnNhd_sub_inv_right_iff {a : A} {w : ℂ} :
    AnalyticOnNhd ℂ (fun z => (z - w)⁻¹) (spectrum ℂ a) ↔ w ∈ resolventSet ℂ a := by
  have hneg : (fun z : ℂ => (z - w)⁻¹) = -(fun z : ℂ => (w - z)⁻¹) := by
    ext z
    rw [Pi.neg_apply, ← neg_sub w z, inv_neg]
  rw [hneg, ← analyticOnNhd_sub_inv_left_iff]
  exact ⟨fun h => by simpa using h.neg, fun h => h.neg⟩

/-- For `w` in the resolvent set of `a`, `z ↦ (w - z)⁻¹` is analytic near `spectrum ℂ a`. -/
theorem analyticOnNhd_sub_inv_left {a : A} {w : ℂ} (hw : w ∈ resolventSet ℂ a) :
    AnalyticOnNhd ℂ (fun z => (w - z)⁻¹) (spectrum ℂ a) :=
  analyticOnNhd_sub_inv_left_iff.mpr hw

/-- For `w` in the resolvent set of `a`, `z ↦ (z - w)⁻¹` is analytic near `spectrum ℂ a`. -/
theorem analyticOnNhd_sub_inv_right {a : A} {w : ℂ} (hw : w ∈ resolventSet ℂ a) :
    AnalyticOnNhd ℂ (fun z => (z - w)⁻¹) (spectrum ℂ a) :=
  analyticOnNhd_sub_inv_right_iff.mpr hw

/-- Any unital complex-algebra homomorphism on `holomorphicGerms (spectrum ℂ a)` sending the
coordinate germ to `a` sends `z ↦ (w - z)⁻¹` (when analytic near `spectrum ℂ a`) to
`resolvent a w`. -/
theorem algHom_ofFun_sub_inv_left (hΦ : Φ (holomorphicGerms.ofFun id analyticOnNhd_id) = a)
    (w : ℂ) (hf : AnalyticOnNhd ℂ (fun z => (w - z)⁻¹) (spectrum ℂ a)) :
    Φ (holomorphicGerms.ofFun (fun z => (w - z)⁻¹) hf) = resolvent a w := by
  have hw : w ∈ resolventSet ℂ a := analyticOnNhd_sub_inv_left_iff.mp hf
  have hne : ∀ z ∈ spectrum ℂ a, w - z ≠ 0 :=
    fun z hz => sub_ne_zero.mpr fun h => spectrum.notMem_iff.mpr hw (h ▸ hz)
  have h1 : AnalyticOnNhd ℂ (1 : ℂ → ℂ) (spectrum ℂ a) := analyticOnNhd_const
  have hden : AnalyticOnNhd ℂ (fun z => w - z) (spectrum ℂ a) :=
    analyticOnNhd_const.sub analyticOnNhd_id
  have hdiv :
      holomorphicGerms.ofFun (fun z => (w - z)⁻¹) hf =
        holomorphicGerms.ofFun (fun z => (1 : ℂ → ℂ) z / (w - z)) (h1.div hden hne) := by
    rw [holomorphicGerms.ofFun_eq_iff]
    exact Eventually.of_forall fun z => (one_div _).symm
  have hΦden : Φ (holomorphicGerms.ofFun (fun z => w - z) hden) = algebraMap ℂ A w - a := by
    have hden_eq :
        holomorphicGerms.ofFun (fun z => w - z) hden =
          algebraMap ℂ (holomorphicGerms (spectrum ℂ a)) w -
            holomorphicGerms.ofFun id analyticOnNhd_id := by
      rw [← holomorphicGerms.ofFun_const, ← holomorphicGerms.ofFun_sub,
        holomorphicGerms.ofFun_eq_iff]
      exact Eventually.of_forall fun _ => rfl
    rw [hden_eq, map_sub, AlgHom.commutes, hΦ]
  rw [hdiv, holomorphicGerms.algHom_ofFun_div Φ h1 hden hne, hΦden]
  simp [resolvent]

/-- Any unital complex-algebra homomorphism on `holomorphicGerms (spectrum ℂ a)` sending the
coordinate germ to `a` sends `z ↦ (z - w)⁻¹` (when analytic near `spectrum ℂ a`) to
`-resolvent a w`. -/
theorem algHom_ofFun_sub_inv_right (hΦ : Φ (holomorphicGerms.ofFun id analyticOnNhd_id) = a)
    (w : ℂ) (hf : AnalyticOnNhd ℂ (fun z => (z - w)⁻¹) (spectrum ℂ a)) :
    Φ (holomorphicGerms.ofFun (fun z => (z - w)⁻¹) hf) = -resolvent a w := by
  have hw : w ∈ resolventSet ℂ a := analyticOnNhd_sub_inv_right_iff.mp hf
  have hneg :
      holomorphicGerms.ofFun (fun z => (z - w)⁻¹) hf =
        -holomorphicGerms.ofFun (fun z => (w - z)⁻¹) (analyticOnNhd_sub_inv_left hw) := by
    rw [← holomorphicGerms.ofFun_neg, holomorphicGerms.ofFun_eq_iff]
    exact Eventually.of_forall fun z => by dsimp; rw [← neg_sub w z, inv_neg]
  rw [hneg, map_neg, algHom_ofFun_sub_inv_left hΦ w _]

/-- On an open neighbourhood `V` of `spectrum ℂ a` on which `z ↦ (w - z)⁻¹` is holomorphic, any
unital homomorphism sending the coordinate germ to `a` sends it to `resolvent a w`. -/
theorem algHom_toGerm_sub_inv_left (hΦ : Φ (holomorphicGerms.ofFun id analyticOnNhd_id) = a)
    {V : Opens ℂ} (ha : spectrum ℂ a ⊆ V) (w : ℂ)
    (hf : DifferentiableOn ℂ (fun z => (w - z)⁻¹) V) :
    Φ (toGerm ha (of V (fun z => (w - z)⁻¹) hf)) = resolvent a w := by
  rw [toGerm_of]
  exact algHom_ofFun_sub_inv_left hΦ w _

/-- On an open neighbourhood `V` of `spectrum ℂ a` on which `z ↦ (z - w)⁻¹` is holomorphic, any
unital homomorphism sending the coordinate germ to `a` sends it to `-resolvent a w`. -/
theorem algHom_toGerm_sub_inv_right (hΦ : Φ (holomorphicGerms.ofFun id analyticOnNhd_id) = a)
    {V : Opens ℂ} (ha : spectrum ℂ a ⊆ V) (w : ℂ)
    (hf : DifferentiableOn ℂ (fun z => (z - w)⁻¹) V) :
    Φ (toGerm ha (of V (fun z => (z - w)⁻¹) hf)) = -resolvent a w := by
  rw [toGerm_of]
  exact algHom_ofFun_sub_inv_right hΦ w _

/-- **Algebraic spectral mapping theorem.** For any unital complex-algebra homomorphism
`Φ : holomorphicGerms (spectrum ℂ a) →ₐ[ℂ] A` sending the coordinate germ to `a`, every germ
`g : holomorphicGerms (spectrum ℂ a)` satisfies `spectrum ℂ (Φ g) = spectrum ℂ g`. -/
theorem spectrum_algHom_eq (hΦ : Φ (holomorphicGerms.ofFun id analyticOnNhd_id) = a)
    (g : holomorphicGerms (spectrum ℂ a)) :
    spectrum ℂ (Φ g) = spectrum ℂ g := by
  refine Subset.antisymm (AlgHom.spectrum_apply_subset Φ g) fun c hc => ?_
  rw [holomorphicGerms.spectrum_eq] at hc
  obtain ⟨w, hw, hwc⟩ := hc
  obtain ⟨U, f, hU, haU, hfU, hfg⟩ := mem_holomorphicGerms_iff_exists_open.mp g.property
  have hg_eq : g = holomorphicGerms.ofFun f ((hfU.analyticOnNhd hU).mono haU) :=
    Subtype.ext (by rw [holomorphicGerms.coe_ofFun, hfg])
  have hfw : f w = c := by
    rw [← hwc, hg_eq, holomorphicGerms.eval_ofFun]
  have hdU : DifferentiableOn ℂ (dslope f w) U :=
    (Complex.differentiableOn_dslope (hU.mem_nhds (haU hw))).mpr hfU
  let q : holomorphicGerms (spectrum ℂ a) :=
    holomorphicGerms.ofFun (dslope f w) ((hdU.analyticOnNhd hU).mono haU)
  let zid : holomorphicGerms (spectrum ℂ a) := holomorphicGerms.ofFun id analyticOnNhd_id
  have hfac_left : algebraMap ℂ _ c - g = (algebraMap ℂ _ w - zid) * q := by
    rw [hg_eq, ← holomorphicGerms.ofFun_const, ← holomorphicGerms.ofFun_const,
      ← holomorphicGerms.ofFun_sub, ← holomorphicGerms.ofFun_sub, ← holomorphicGerms.ofFun_mul,
      holomorphicGerms.ofFun_eq_iff]
    refine Eventually.of_forall fun z => ?_
    have hds := sub_smul_dslope f w z
    simp only [smul_eq_mul, hfw] at hds
    dsimp
    linear_combination hds
  have hΦ_left := congrArg Φ hfac_left
  rw [map_sub, AlgHom.commutes, map_mul, map_sub, AlgHom.commutes, hΦ] at hΦ_left
  have hcomm : Commute (algebraMap ℂ A w - a) (Φ q) := by
    simpa only [map_sub, AlgHom.commutes, zid, hΦ] using
      (Commute.all (algebraMap ℂ (holomorphicGerms (spectrum ℂ a)) w - zid) q).map Φ
  rw [spectrum.mem_iff]
  exact fun hu => spectrum.mem_iff.mp hw ((hcomm.isUnit_mul_iff.mp (hΦ_left ▸ hu)).1)

end Algebraic

end TauCeti

/-! ### Commutation and bicommutant -/

section Commute

open TauCeti TauCeti.Contour TauCeti.HolomorphicFunctions

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

/-- Every element commuting with `a` commutes with `holomorphicCalculusOn a U ha f`. -/
theorem Commute.holomorphicCalculusOn_right {a b : A} (hb : Commute b a) (U : Opens ℂ)
    (ha : spectrum ℂ a ⊆ U) (f : holomorphicFunctions U) :
    Commute b (holomorphicCalculusOn a U ha f) := by
  obtain ⟨Γ, hΓ, hn, hw⟩ := (spectrum.isCompact a).exists_cycle_windingNumber_eq_one U.isOpen ha
  rw [holomorphicCalculusOn_eq_integral a U ha f Γ hΓ hn hw]
  exact (hb.integral_smul_resolvent_right
    ((differentiableOn_extend f).continuousOn.mono fun _ hz => (Cycle.isIn_iff.mp hΓ hz).1)
    (Cycle.isIn_iff.mpr fun _ hz => spectrum.notMem_iff.mp (Cycle.isIn_iff.mp hΓ hz).2)).smul_right
    (2 * π * I)⁻¹

/-- Every element commuting with `a` commutes with `holomorphicCalculus a g`; in particular, every
value of the holomorphic functional calculus lies in the bicommutant of `a`. -/
theorem Commute.holomorphicCalculus_right {a b : A} (hb : Commute b a)
    (g : holomorphicGerms (spectrum ℂ a)) :
    Commute b (holomorphicCalculus a g) := by
  obtain ⟨U, ha, f, rfl⟩ := holomorphicGerms.exists_toGerm_eq g
  rw [holomorphicCalculus_toGerm]
  exact hb.holomorphicCalculusOn_right U ha f

end Commute

namespace TauCeti

open Contour HolomorphicFunctions

section BanachAlgebra

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

/-! ### Resolvent and rational function agreement -/

/-- The holomorphic germ calculus sends `z ↦ (w - z)⁻¹` (when analytic near `spectrum ℂ a`) to
`resolvent a w`. -/
@[simp]
theorem holomorphicCalculus_sub_inv_left (a : A) (w : ℂ)
    (hf : AnalyticOnNhd ℂ (fun z => (w - z)⁻¹) (spectrum ℂ a)) :
    holomorphicCalculus a (holomorphicGerms.ofFun (fun z => (w - z)⁻¹) hf) =
      resolvent a w :=
  algHom_ofFun_sub_inv_left (holomorphicCalculus_id a) w hf

/-- The holomorphic germ calculus sends `z ↦ (z - w)⁻¹` (when analytic near `spectrum ℂ a`) to
`-resolvent a w`. -/
@[simp]
theorem holomorphicCalculus_sub_inv_right (a : A) (w : ℂ)
    (hf : AnalyticOnNhd ℂ (fun z => (z - w)⁻¹) (spectrum ℂ a)) :
    holomorphicCalculus a (holomorphicGerms.ofFun (fun z => (z - w)⁻¹) hf) =
      -resolvent a w :=
  algHom_ofFun_sub_inv_right (holomorphicCalculus_id a) w hf

/-- On an open neighbourhood `U` of `spectrum ℂ a` on which `z ↦ (w - z)⁻¹` is holomorphic,
`holomorphicCalculusOn` sends it to `resolvent a w`. -/
@[simp]
theorem holomorphicCalculusOn_sub_inv_left (a : A) (U : Opens ℂ) (ha : spectrum ℂ a ⊆ U)
    (w : ℂ) (hf : DifferentiableOn ℂ (fun z => (w - z)⁻¹) U) :
    holomorphicCalculusOn a U ha (of U (fun z => (w - z)⁻¹) hf) = resolvent a w := by
  rw [← holomorphicCalculus_toGerm]
  exact algHom_toGerm_sub_inv_left (holomorphicCalculus_id a) ha w hf

/-- On an open neighbourhood `U` of `spectrum ℂ a` on which `z ↦ (z - w)⁻¹` is holomorphic,
`holomorphicCalculusOn` sends it to `-resolvent a w`. -/
@[simp]
theorem holomorphicCalculusOn_sub_inv_right (a : A) (U : Opens ℂ) (ha : spectrum ℂ a ⊆ U)
    (w : ℂ) (hf : DifferentiableOn ℂ (fun z => (z - w)⁻¹) U) :
    holomorphicCalculusOn a U ha (of U (fun z => (z - w)⁻¹) hf) = -resolvent a w := by
  rw [← holomorphicCalculus_toGerm]
  exact algHom_toGerm_sub_inv_right (holomorphicCalculus_id a) ha w hf

/-- If a holomorphic representative `g` does not vanish on `spectrum ℂ a`, its image under
`holomorphicCalculus a` is a unit in `A`. -/
theorem isUnit_holomorphicCalculus_ofFun (a : A) {g : ℂ → ℂ}
    (hg : AnalyticOnNhd ℂ g (spectrum ℂ a)) (hg0 : ∀ z ∈ spectrum ℂ a, g z ≠ 0) :
    IsUnit (holomorphicCalculus a (holomorphicGerms.ofFun g hg)) :=
  ((holomorphicGerms.isUnit_iff _).mpr fun z hz => by simpa using hg0 z hz).map
    (holomorphicCalculus a)

/-- The holomorphic germ calculus sends a quotient `f / g` with `g` nonvanishing on `spectrum ℂ a`
to `f(a) * Ring.inverse (g(a))`. -/
theorem holomorphicCalculus_ofFun_div (a : A) {f g : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (spectrum ℂ a)) (hg : AnalyticOnNhd ℂ g (spectrum ℂ a))
    (hg0 : ∀ z ∈ spectrum ℂ a, g z ≠ 0) :
    holomorphicCalculus a (holomorphicGerms.ofFun (fun z => f z / g z) (hf.div hg hg0)) =
      holomorphicCalculus a (holomorphicGerms.ofFun f hf) *
        Ring.inverse (holomorphicCalculus a (holomorphicGerms.ofFun g hg)) :=
  holomorphicGerms.algHom_ofFun_div (holomorphicCalculus a) hf hg hg0

/-- **Rational function agreement.** For complex polynomials `p` and `q` with `q` nonvanishing on
`spectrum ℂ a`, the holomorphic germ calculus evaluates `z ↦ p(z) / q(z)` to
`Polynomial.aeval a p * Ring.inverse (Polynomial.aeval a q)`. -/
theorem holomorphicCalculus_div_polynomial (a : A) (p : Polynomial ℂ) {q : Polynomial ℂ}
    (hq : ∀ z ∈ spectrum ℂ a, q.eval z ≠ 0) :
    holomorphicCalculus a
      (holomorphicGerms.ofFun (fun z => p.eval z / q.eval z)
        (((AnalyticOnNhd.eval_polynomial p).mono (subset_univ _)).div
          ((AnalyticOnNhd.eval_polynomial q).mono (subset_univ _)) hq)) =
      Polynomial.aeval a p * Ring.inverse (Polynomial.aeval a q) := by
  rw [holomorphicCalculus_ofFun_div a ((AnalyticOnNhd.eval_polynomial p).mono (subset_univ _))
      ((AnalyticOnNhd.eval_polynomial q).mono (subset_univ _)) hq,
    holomorphicCalculus_polynomial, holomorphicCalculus_polynomial]

/-! ### Spectral mapping theorem -/

/-- The holomorphic functional calculus preserves spectra: the spectrum in `A` of
`holomorphicCalculus a g` coincides with the spectrum of the germ `g`. -/
theorem spectrum_holomorphicCalculus_eq_spectrum (a : A)
    (g : holomorphicGerms (spectrum ℂ a)) :
    spectrum ℂ (holomorphicCalculus a g) = spectrum ℂ g :=
  spectrum_algHom_eq (holomorphicCalculus_id a) g

/-- **Spectral mapping theorem** for holomorphic germs: `σ(g(a))` is the set of point values of `g`
on `σ(a)`. -/
@[simp]
theorem spectrum_holomorphicCalculus (a : A) (g : holomorphicGerms (spectrum ℂ a)) :
    spectrum ℂ (holomorphicCalculus a g) =
      {c | ∃ (z : ℂ) (hz : z ∈ spectrum ℂ a), holomorphicGerms.eval z hz g = c} :=
  (spectrum_holomorphicCalculus_eq_spectrum a g).trans (holomorphicGerms.spectrum_eq g)

/-- **Spectral mapping theorem** for represented germs: `σ(f(a)) = f '' σ(a)`. -/
@[simp high] -- Fire before `spectrum_holomorphicCalculus` expands into a set-builder.
theorem spectrum_holomorphicCalculus_ofFun (a : A) (f : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f (spectrum ℂ a)) :
    spectrum ℂ (holomorphicCalculus a (holomorphicGerms.ofFun f hf)) = f '' spectrum ℂ a :=
  (spectrum_holomorphicCalculus_eq_spectrum a _).trans (holomorphicGerms.spectrum_ofFun f hf)

/-- **Spectral mapping theorem** on an open neighbourhood `U` of `σ(a)`. -/
@[simp]
theorem spectrum_holomorphicCalculusOn (a : A) (U : Opens ℂ) (ha : spectrum ℂ a ⊆ U)
    (f : holomorphicFunctions U) :
    spectrum ℂ (holomorphicCalculusOn a U ha f) = extend f '' spectrum ℂ a := by
  conv_lhs => rw [← of_extend f]
  rw [← holomorphicCalculus_toGerm, toGerm_of, spectrum_holomorphicCalculus_ofFun]

/-- **Spectral mapping theorem** for an explicit `DifferentiableOn` representative on `U`. -/
@[simp high] -- Fire before `spectrum_holomorphicCalculusOn` leaves `extend (of U f hf)`.
theorem spectrum_holomorphicCalculusOn_of (a : A) (U : Opens ℂ) (ha : spectrum ℂ a ⊆ U)
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f U) :
    spectrum ℂ (holomorphicCalculusOn a U ha (of U f hf)) = f '' spectrum ℂ a := by
  rw [← holomorphicCalculus_toGerm, toGerm_of, spectrum_holomorphicCalculus_ofFun]

/-! ### Convergent power series -/

/-- If `f` has formal power series `p` on an open ball `Metric.eball z₀ r` containing
`spectrum ℂ a`, then `fun n ↦ p.coeff n • (a - algebraMap ℂ A z₀) ^ n` is absolutely norm-summable
in `A`. -/
theorem _root_.HasFPowerSeriesOnBall.summable_norm_coeff_smul_sub_pow
    {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ} {z₀ : ℂ} {r : ℝ≥0∞}
    (hf : HasFPowerSeriesOnBall f p z₀ r) {a : A} (ha : spectrum ℂ a ⊆ Metric.eball z₀ r) :
    Summable fun n => ‖p.coeff n • (a - algebraMap ℂ A z₀) ^ n‖ := by
  nontriviality A
  set x := a - algebraMap ℂ A z₀
  have hspec_lt : spectralRadius ℂ x < r := by
    obtain ⟨w, hw, hws⟩ := spectrum.exists_nnNorm_eq_spectralRadius x
    rw [← spectrum.sub_singleton_eq] at hw
    obtain ⟨z, hz, w', hw', rfl⟩ := Set.mem_sub.mp hw
    have hnndist : nndist z z₀ = ‖z - z₀‖₊ :=
      NNReal.eq (by rw [coe_nndist, coe_nnNorm, dist_eq_norm])
    rw [Set.mem_singleton_iff.mp hw', ← hnndist, ← edist_nndist] at hws
    exact hws ▸ Metric.mem_eball.mp (ha hz)
  obtain ⟨ρ, hρ₁, hρ₂⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hspec_lt
  have hgρ : gelfandRadius x < ρ := by
    rw [spectrum.spectralRadius_eq_gelfandRadius] at hρ₁
    exact (ENNReal.ofReal_lt_coe_iff (gelfandRadius_nonneg x)).mp hρ₁
  obtain ⟨C, _, hC⟩ := norm_pow_le_mul_pow_of_gelfandRadius_lt x hgρ
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_)
    ((p.summable_norm_mul_pow (hρ₂.trans_le hf.r_le)).mul_left C)
  calc ‖p.coeff n • x ^ n‖
      = ‖p n‖ * ‖x ^ n‖ := by rw [norm_smul, p.norm_apply_eq_norm_coef]
    _ ≤ ‖p n‖ * (C * (ρ : ℝ) ^ n) := mul_le_mul_of_nonneg_left (hC n) (norm_nonneg _)
    _ = C * (‖p n‖ * (ρ : ℝ) ^ n) := by ring

/-- **Power series agreement** on the open ball of convergence: if `f` has formal power series `p`
on `Metric.eball z₀ r` and `spectrum ℂ a ⊆ Metric.eball z₀ r`, then
`∑ n, p.coeff n • (a - algebraMap ℂ A z₀) ^ n` converges in norm to `holomorphicCalculusOn`
of `f`. -/
theorem _root_.HasFPowerSeriesOnBall.hasSum_holomorphicCalculusOn
    {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ} {z₀ : ℂ} {r : ℝ≥0∞}
    (hf : HasFPowerSeriesOnBall f p z₀ r) {a : A} (ha : spectrum ℂ a ⊆ Metric.eball z₀ r) :
    HasSum (fun n => p.coeff n • (a - algebraMap ℂ A z₀) ^ n)
      (holomorphicCalculusOn a ⟨Metric.eball z₀ r, Metric.isOpen_eball⟩ ha
        (of ⟨Metric.eball z₀ r, Metric.isOpen_eball⟩ f hf.differentiableOn)) := by
  let U : Opens ℂ := ⟨Metric.eball z₀ r, Metric.isOpen_eball⟩
  let q : Polynomial ℂ := Polynomial.X - Polynomial.C z₀
  let w : holomorphicFunctions U := of U (fun z => q.eval z) q.differentiable.differentiableOn
  let F : ℕ → holomorphicFunctions U := fun n => ∑ k ∈ Finset.range n, p.coeff k • w ^ k
  have hF_apply (n : ℕ) (z : U) : extend (F n) z = p.partialSum n ((z : ℂ) - z₀) := by
    rw [extend_apply]
    have hsum : (F n).val z = ∑ k ∈ Finset.range n, (p.coeff k • w ^ k).val z :=
      map_sum ((ContinuousMap.evalAlgHom ℂ ℂ z).comp (holomorphicFunctions U).val) _ _
    rw [hsum, FormalMultilinearSeries.partialSum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [p.apply_eq_pow_smul_coeff]
    simp [w, q, smul_eq_mul, mul_comm]
  have hF_tendsto : Tendsto F atTop (𝓝 (of U f hf.differentiableOn)) := by
    rw [tendsto_iff_tendstoLocallyUniformlyOn]
    refine (hf.tendstoLocallyUniformlyOn'.congr_right fun z hz => ?_).congr fun n z hz => ?_
    · rw [extend_apply (of U f hf.differentiableOn) ⟨z, hz⟩, of_apply]
    · exact (hF_apply n ⟨z, hz⟩).symm
  have hw_calc : holomorphicCalculusOn a U ha w = a - algebraMap ℂ A z₀ := by
    rw [holomorphicCalculusOn_polynomial a U ha q]
    simp [q]
  have hcalc_F (n : ℕ) :
      holomorphicCalculusOn a U ha (F n) =
        ∑ k ∈ Finset.range n, p.coeff k • (a - algebraMap ℂ A z₀) ^ k := by
    simp only [F, map_sum, map_smul, map_pow, hw_calc]
  have htendsto_nat :
      Tendsto (fun n => ∑ k ∈ Finset.range n, p.coeff k • (a - algebraMap ℂ A z₀) ^ k) atTop
        (𝓝 (holomorphicCalculusOn a U ha (of U f hf.differentiableOn))) := by
    simpa only [Function.comp_def, hcalc_F] using
      ((continuous_holomorphicCalculusOn a U ha).tendsto _).comp hF_tendsto
  exact (hasSum_iff_tendsto_nat_of_summable_norm
    (hf.summable_norm_coeff_smul_sub_pow ha)).mpr htendsto_nat

/-- **Power series agreement** for the holomorphic germ calculus. -/
theorem _root_.HasFPowerSeriesOnBall.hasSum_holomorphicCalculus
    {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ} {z₀ : ℂ} {r : ℝ≥0∞}
    (hf : HasFPowerSeriesOnBall f p z₀ r) {a : A} (ha : spectrum ℂ a ⊆ Metric.eball z₀ r) :
    HasSum (fun n => p.coeff n • (a - algebraMap ℂ A z₀) ^ n)
      (holomorphicCalculus a
        (holomorphicGerms.ofFun f
          ((hf.differentiableOn.analyticOnNhd Metric.isOpen_eball).mono ha))) := by
  simpa only [← toGerm_of (U := ⟨Metric.eball z₀ r, Metric.isOpen_eball⟩) ha f hf.differentiableOn,
    holomorphicCalculus_toGerm] using hf.hasSum_holomorphicCalculusOn ha

/-- `tsum` form of `HasFPowerSeriesOnBall.hasSum_holomorphicCalculus`. -/
theorem _root_.HasFPowerSeriesOnBall.holomorphicCalculus_eq_tsum
    {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ} {z₀ : ℂ} {r : ℝ≥0∞}
    (hf : HasFPowerSeriesOnBall f p z₀ r) {a : A} (ha : spectrum ℂ a ⊆ Metric.eball z₀ r) :
    holomorphicCalculus a
      (holomorphicGerms.ofFun f
        ((hf.differentiableOn.analyticOnNhd Metric.isOpen_eball).mono ha)) =
      ∑' n, p.coeff n • (a - algebraMap ℂ A z₀) ^ n :=
  (hf.hasSum_holomorphicCalculus ha).tsum_eq.symm

/-- For a scalar power series `∑' n, c n * (z - z₀) ^ n` whose open disk of convergence contains
`spectrum ℂ a`, the holomorphic germ calculus agrees with `FormalMultilinearSeries.ofScalarsSum`. -/
theorem holomorphicCalculus_ofScalarsSum (c : ℕ → ℂ) (z₀ : ℂ) {a : A}
    (ha : spectrum ℂ a ⊆ Metric.eball z₀ (FormalMultilinearSeries.ofScalars ℂ c).radius) :
    holomorphicCalculus a
      (holomorphicGerms.ofFun (fun z => FormalMultilinearSeries.ofScalarsSum c (z - z₀))
        ((analyticOnNhd_ofScalarsSum_sub c z₀).mono ha)) =
      FormalMultilinearSeries.ofScalarsSum c (a - algebraMap ℂ A z₀) := by
  nontriviality A
  obtain ⟨w, hw, _⟩ := spectrum.exists_nnNorm_eq_spectralRadius a
  have hr : 0 < (FormalMultilinearSeries.ofScalars ℂ c).radius :=
    bot_le.trans_lt (Metric.mem_eball.mp (ha hw))
  rw [(hasFPowerSeriesOnBall_ofScalarsSum_sub c z₀ hr).holomorphicCalculus_eq_tsum ha,
    FormalMultilinearSeries.ofScalars_sum_eq]
  exact tsum_congr fun n => by rw [FormalMultilinearSeries.coeff_ofScalars]

/-! ### Scalar evaluation in `ℂ` -/

/-- In the complex field `ℂ` itself, `holomorphicCalculusOn z` evaluates a holomorphic function at
`z`. -/
@[simp]
theorem holomorphicCalculusOn_complex (z : ℂ) (U : Opens ℂ) (hz : spectrum ℂ z ⊆ U)
    (f : holomorphicFunctions U) :
    holomorphicCalculusOn z U hz f =
      f.val ⟨z, hz (spectrum.mem_iff.mpr (by simp))⟩ := by
  obtain ⟨Γ, hΓ, hn, hw⟩ := (spectrum.isCompact z).exists_cycle_windingNumber_eq_one U.isOpen hz
  have hz_mem : z ∈ spectrum ℂ z := spectrum.mem_iff.mpr (by simp)
  have hzΓ : z ∉ Cycle.trace Γ := fun h => (Cycle.isIn_iff.mp hΓ h).2 hz_mem
  have hΓU : Γ.IsIn U := Cycle.isIn_iff.mpr fun _ h => (Cycle.isIn_iff.mp hΓ h).1
  have hint :
      Cycle.integral (fun w => extend f w • resolvent z w) Γ =
        Cycle.integral (fun w => extend f w / (w - z)) Γ := by
    refine Cycle.integral_congr fun w _ => ?_
    simp [resolvent, Ring.inverse_eq_inv', div_eq_mul_inv]
  have hcif :
      Cycle.integral (fun w => extend f w / (w - z)) Γ = 2 * π * I * extend f z := by
    simpa [hw z hz_mem] using
      Cycle.cauchyIntegralFormula_nullHomologous U.isOpen (differentiableOn_extend f) hΓU hn hzΓ
  rw [holomorphicCalculusOn_eq_integral z U hz f Γ hΓ hn hw, hint, hcif,
    extend_apply f ⟨z, hz hz_mem⟩, smul_eq_mul]
  field_simp [two_pi_I_ne_zero]

/-- In the complex field `ℂ` itself, `holomorphicCalculus z` is point evaluation of germs at `z`. -/
@[simp]
theorem holomorphicCalculus_complex (z : ℂ) (g : holomorphicGerms (spectrum ℂ z)) :
    holomorphicCalculus z g =
      holomorphicGerms.eval z (spectrum.mem_iff.mpr (by simp)) g := by
  obtain ⟨U, hz, f, rfl⟩ := holomorphicGerms.exists_toGerm_eq g
  rw [holomorphicCalculus_toGerm, holomorphicCalculusOn_complex, eval_toGerm]

end BanachAlgebra

/-! ### Naturality under continuous unital algebra homomorphisms -/

section Naturality

variable {A B F : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]
  [NormedRing B] [NormedAlgebra ℂ B] [CompleteSpace B]
  [FunLike F A B] [AlgHomClass F ℂ A B]

/-- **Naturality of `holomorphicCalculusOn`.** Every continuous unital complex-algebra homomorphism
`φ : A → B` satisfies `φ (holomorphicCalculusOn a U ha f) = holomorphicCalculusOn (φ a) U _ f`. -/
theorem map_holomorphicCalculusOn (φ : F) (hφ : Continuous φ) (a : A) (U : Opens ℂ)
    (ha : spectrum ℂ a ⊆ U) (f : holomorphicFunctions U) :
    φ (holomorphicCalculusOn a U ha f) =
      holomorphicCalculusOn (φ a) U ((AlgHom.spectrum_apply_subset φ a).trans ha) f := by
  let φL : A →L[ℂ] B := { (AlgHom.ofClass φ).toLinearMap with cont := hφ }
  have hφL (x : A) : φL x = φ x := rfl
  obtain ⟨Γ, hΓ, hn, hw⟩ := (spectrum.isCompact a).exists_cycle_windingNumber_eq_one U.isOpen ha
  have hsub : spectrum ℂ (φ a) ⊆ spectrum ℂ a := AlgHom.spectrum_apply_subset φ a
  have hΓ' : Γ.IsIn (U \ spectrum ℂ (φ a)) :=
    Cycle.isIn_iff.mpr fun z hz =>
      ⟨(Cycle.isIn_iff.mp hΓ hz).1, fun h => (Cycle.isIn_iff.mp hΓ hz).2 (hsub h)⟩
  have hw' : ∀ z ∈ spectrum ℂ (φ a), Cycle.windingNumber z Γ = 1 := fun z hz => hw z (hsub hz)
  have hR : Γ.IsIn (resolventSet ℂ a) :=
    Cycle.isIn_iff.mpr fun _ hz => spectrum.notMem_iff.mp (Cycle.isIn_iff.mp hΓ hz).2
  have hcont : ContinuousOn (fun z => extend f z • resolvent a z) (Cycle.trace Γ) :=
    ((differentiableOn_extend f).continuousOn.mono
      fun _ hz => (Cycle.isIn_iff.mp hΓ hz).1).smul (Cycle.continuousOn_resolvent hR)
  have hint := Cycle.integral_comp_comm (f := fun z => extend f z • resolvent a z)
    (fun _ => Cycle.intervalIntegrable_of_mem_support hcont) φL
  rw [← hφL, holomorphicCalculusOn_eq_integral a U ha f Γ hΓ hn hw, map_smul, ← hint,
    holomorphicCalculusOn_eq_integral (φ a) U (hsub.trans ha) f Γ hΓ' hn hw']
  congr 1
  refine Cycle.integral_congr fun z hz => ?_
  rw [map_smul, hφL, AlgHom.map_resolvent φ (Cycle.isIn_iff.mp hR hz)]

/-- `simp` form of `map_holomorphicCalculusOn` for bundled continuous algebra homomorphisms
(`ContinuousMapClass`). -/
@[simp]
theorem map_holomorphicCalculusOn_continuousMapClass [ContinuousMapClass F A B] (φ : F) (a : A)
    (U : Opens ℂ) (ha : spectrum ℂ a ⊆ U) (f : holomorphicFunctions U) :
    φ (holomorphicCalculusOn a U ha f) =
      holomorphicCalculusOn (φ a) U ((AlgHom.spectrum_apply_subset φ a).trans ha) f :=
  map_holomorphicCalculusOn φ (map_continuous φ) a U ha f

/-- **Naturality of `holomorphicCalculus`.** Every continuous unital complex-algebra homomorphism
`φ : A → B` intertwines `holomorphicCalculus a` with `holomorphicCalculus (φ a)` along restriction
from `spectrum ℂ a` to `spectrum ℂ (φ a)`. -/
theorem map_holomorphicCalculus (φ : F) (hφ : Continuous φ) (a : A)
    (g : holomorphicGerms (spectrum ℂ a)) :
    φ (holomorphicCalculus a g) =
      holomorphicCalculus (φ a)
        (holomorphicGerms.restrict (AlgHom.spectrum_apply_subset φ a) g) := by
  obtain ⟨U, ha, f, rfl⟩ := holomorphicGerms.exists_toGerm_eq g
  rw [holomorphicCalculus_toGerm, restrict_toGerm, holomorphicCalculus_toGerm,
    map_holomorphicCalculusOn φ hφ a U ha f]

/-- `simp` form of `map_holomorphicCalculus` for bundled continuous algebra homomorphisms
(`ContinuousMapClass`). -/
@[simp]
theorem map_holomorphicCalculus_continuousMapClass [ContinuousMapClass F A B] (φ : F) (a : A)
    (g : holomorphicGerms (spectrum ℂ a)) :
    φ (holomorphicCalculus a g) =
      holomorphicCalculus (φ a)
        (holomorphicGerms.restrict (AlgHom.spectrum_apply_subset φ a) g) :=
  map_holomorphicCalculus φ (map_continuous φ) a g

end Naturality

end TauCeti
