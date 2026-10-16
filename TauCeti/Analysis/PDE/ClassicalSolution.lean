/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.DirichletProblem
public import Mathlib.Analysis.InnerProductSpace.Laplacian
import TauCeti.Analysis.Calculus.Gradient
import TauCeti.Analysis.InnerProductSpace.Laplacian.Basic
import TauCeti.Analysis.Sobolev.W1p.VanishingBoundary
import TauCeti.Analysis.Sobolev.WeakDeriv.Laplacian
import TauCeti.MeasureTheory.Function.LocallyIntegrable

/-!
# Classical solutions of the Dirichlet problem are weak solutions

Let `Ω` be a bounded open subset of `ℝⁿ` and let `w` be of class `C²` on `Ω`, continuous on
`closure Ω` and zero on `frontier Ω`, with `Δw ∈ L²(Ω)`. Then `w` is the weak solution of the
Dirichlet problem for its own Laplacian: it lies in `H¹₀(Ω)` and `∫_Ω ∇v · ∇w = -∫_Ω Δw v` for
every `v ∈ H¹₀(Ω)`. So the weak solution of `-Δu = f` in `Ω`, `u = 0` on `∂Ω`, given by
Lax--Milgram agrees with every classical solution. No regularity of `∂Ω` is assumed, and of `w`
up to the boundary only continuity.

The content is the energy bound. Nothing is assumed about `∇w` near `∂Ω`, so `w ∈ H¹(Ω)` has to
be proved. For `ε > 0` the truncation `(w - ε)⁺` has compact support in `Ω`, because `w` is
continuous up to the boundary and vanishes there, and Green's identity gives

`∫_{w > ε} ‖∇w‖² = -∫_Ω Δw (w - ε)⁺ ≤ sup_Ω |w| ∫_Ω |Δw|`.

The same bound for `-w`, the limit `ε → 0`, and the vanishing of `∇w` almost everywhere on
`{w = 0}` give `∫_Ω ‖∇w‖² < ∞`. Then `w ∈ H¹₀(Ω)` by
`TauCeti.W1p.mem_w1p0Submodule_of_continuousOn_closure`. The boundary condition is used in the
energy bound and not only in the conclusion: Hadamard's example is a harmonic function on the
disc, continuous up to the boundary, with infinite Dirichlet energy.

## Main declarations

* `TauCeti.PDE.energyFormH1_one_zero_zero_eq_setIntegral_neg_laplacian_mul`: Green's first
  identity `∫_Ω ∇v · ∇u = -∫_Ω Δw v` for `v ∈ H¹₀(Ω)` and `u ∈ H¹(Ω)` represented by a `C²`
  function `w` with `Δw ∈ L²(Ω)`.
* `TauCeti.PDE.exists_isWeakSolutionDirichlet_laplacian_of_contDiffOn`: a `C²` function
  continuous up to the boundary and vanishing there is a weak solution in `H¹₀(Ω)` of the
  Dirichlet problem for its own Laplacian.
* `TauCeti.PDE.exists_value_ae_eq_and_energyFormH1_eq_of_laplacian_eq`: a classical Dirichlet
  eigenfunction of `-Δ`, `-Δw = κ w` in `Ω` with `w = 0` on `∂Ω`, is a weak one.
* `TauCeti.PDE.IsWeakSolutionDirichlet.value_ae_eq_of_contDiffOn`: on a domain inside a ball, the
  weak solution of `-Δu = f`, `u = 0` on `∂Ω`, equals any such classical solution.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Section 6.1.2 (classical solutions
  satisfy the weak formulation).
* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Section 7.4 (truncations of Sobolev functions) and Theorem 8.3.
-/

public section

noncomputable section

namespace TauCeti

namespace PDE

open InnerProductSpace Laplacian MeasureTheory Metric Set Filter TopologicalSpace
open scoped Distributions Gradient InnerProductSpace ENNReal Topology

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {mu : Measure (EuclideanSpace ℝ ι)}
  [mu.IsAddHaarMeasure] {Omega : Opens (EuclideanSpace ℝ ι)} {w : EuclideanSpace ℝ ι → ℝ}

/-- **Green's first identity against `H¹₀(Ω)`.** Let `u ∈ H¹(Ω)` agree almost everywhere on `Ω`
with a function `w` of class `C²` on `Ω` whose Laplacian lies in `L²(Ω)`. Then
`∫_Ω ∇v · ∇u = -∫_Ω Δw v` for every `v ∈ H¹₀(Ω)`: `u` solves `-Δu = -Δw` weakly. No boundary
condition is imposed on `u`. -/
theorem energyFormH1_one_zero_zero_eq_setIntegral_neg_laplacian_mul {u : W1p mu Omega 2}
    (hw : ContDiffOn ℝ 2 w Omega) (hu : W1p.value u =ᵐ[mu.restrict Omega] w)
    (hΔ : MemLp (Δ w) 2 (mu.restrict Omega)) (v : W1p0 mu Omega 2) :
    energyFormH1 (fun _ => 1) 0 0 u (v : W1p mu Omega 2) =
      ∫ x in Omega, -Δ w x * W1p.value (v : W1p mu Omega 2) x ∂mu := by
  have hO : MeasurableSet (Omega : Set (EuclideanSpace ℝ ι)) := Omega.isOpen.measurableSet
  have h1 := uniformlyEllipticOn_const_one_one (n := ι) (Omega : Set (EuclideanSpace ℝ ι))
  have hcoeff := memLp_energyIntegrand_of_bounds (mu := mu) (b := 0) (c := 0) (beta := 0)
    (gamma := 0) h1.upper_nonneg aestronglyMeasurable_const aestronglyMeasurable_const
    aestronglyMeasurable_const (fun _x hx eta xi => h1.upper_bound hx eta xi) (fun _ _ => by simp)
    (fun _ _ => by simp)
  have hf := hΔ.neg.coeFn_toLp
  refine ((forall_energyFormH1_eq_setIntegral_iff_forall_testFunction hcoeff
    (hΔ.neg.toLp _) u).2 (fun φ => ?_) v).trans (integral_congr_ae ?_)
  · -- Against a test function: `∫ ⟪∇φ, ∇u⟫ = -∫ Δφ u = -∫ Δφ w = -∫ φ Δw`.
    have hgrad : energyFormH1 (fun _ => 1) 0 0 u (W1p.ofTestFunctionₗ mu Omega 2 φ) =
        ∫ x, ⟪∇ (φ : EuclideanSpace ℝ ι → ℝ) x, W1p.gradient u x⟫_ℝ ∂mu := by
      rw [energyFormH1_zero_zero_eq_setIntegral]
      refine (integral_congr_ae ?_).trans
        (setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_)
      · filter_upwards [gradientTestFunctionLp_apply_ae (mu := mu) 2 φ] with x hx
        rw [W1p.gradient_ofTestFunctionₗ, hx, matrixBilinearForm_one_apply]
        exact ((EuclideanSpace.inner_eq_star_dotProduct _ _).trans (dotProduct_comm _ _)).symm
      · have hφ : fderiv ℝ (φ : EuclideanSpace ℝ ι → ℝ) x = 0 :=
          fderiv_of_notMem_tsupport ℝ fun hx' => hx (φ.tsupport_subset hx')
        simp [gradient, hφ]
    have hval : ∫ x, Δ (φ : EuclideanSpace ℝ ι → ℝ) x • W1p.value u x ∂mu =
        ∫ x, Δ (φ : EuclideanSpace ℝ ι → ℝ) x • w x ∂mu := by
      refine integral_congr_ae ?_
      filter_upwards [(ae_restrict_iff' hO).1 hu] with x hx
      by_cases hxΩ : x ∈ (Omega : Set (EuclideanSpace ℝ ι))
      · rw [hx hxΩ]
      · rw [image_eq_zero_of_notMem_tsupport fun h' =>
          hxΩ (φ.tsupport_subset (tsupport_laplacian_subset _ h'))]
        simp
    rw [hgrad, ← neg_neg (∫ x, ⟪_, _⟫_ℝ ∂mu),
      ← (W1p.hasWeakFDerivOn u).integral_laplacian_smul_eq_neg_integral_inner φ, hval,
      hw.integral_laplacian_smul_eq_integral_smul_laplacian φ, ← integral_neg,
      ← setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_]
    · refine integral_congr_ae ?_
      filter_upwards [ae_restrict_of_ae_restrict_of_subset subset_rfl hf] with x hx
      rw [hx, Pi.neg_apply, smul_eq_mul]
      ring
    · simp [φ.zero_on_compl hx]
  · filter_upwards [hf] with x hx
    rw [hx, Pi.neg_apply]

omit [DecidableEq ι] in
/-- **The energy of a classical solution above a positive level.** Let `w` be of class `C²` on a
bounded open set `Ω`, continuous on its closure, zero on its frontier, with `|w| ≤ S` on `Ω` and
`Δw` integrable on `Ω`. Then for `ε > 0`, testing `-Δw` against the truncation `(w - ε)⁺`, which
has compact support in `Ω`, gives `∫_{w > ε} ‖∇w‖² ≤ S ∫_Ω |Δw|`. -/
private theorem setLIntegral_enorm_gradient_sq_le
    (hb : Bornology.IsBounded (Omega : Set (EuclideanSpace ℝ ι))) (hw : ContDiffOn ℝ 2 w Omega)
    (hwc : ContinuousOn w (closure (Omega : Set (EuclideanSpace ℝ ι))))
    (hw0 : ∀ x ∈ frontier (Omega : Set (EuclideanSpace ℝ ι)), w x = 0)
    (hΔ : IntegrableOn (Δ w) Omega mu) {S : ℝ}
    (hS : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), |w x| ≤ S) (hS0 : 0 ≤ S) {ε : ℝ}
    (hε : 0 < ε) :
    ∫⁻ x in (Omega : Set (EuclideanSpace ℝ ι)) ∩ w ⁻¹' Ioi ε, ‖∇ w x‖ₑ ^ 2 ∂mu ≤
      ENNReal.ofReal (S * ∫ x in Omega, |Δ w x| ∂mu) := by
  classical
  have hO := Omega.isOpen
  have h2 : (2 : ℝ≥0∞) ≠ ∞ := ENNReal.ofNat_ne_top
  -- A neighbourhood `V` of the superlevel set, compactly contained in `Ω`.
  obtain ⟨K, hK, hUK, hKO⟩ := exists_isCompact_inter_preimage_Ici_subset_subset hO hb hwc hw0 hε
  obtain ⟨V', hV'o, hKV, hVO', hL⟩ := exists_open_between_and_isCompact_closure hK hO hKO
  set V : Opens (EuclideanSpace ℝ ι) := ⟨V', hV'o⟩
  have hVL : (V : Set (EuclideanSpace ℝ ι)) ⊆ closure V' := subset_closure
  have hVO : (V : Set (EuclideanSpace ℝ ι)) ⊆ Omega := hVL.trans hVO'
  have hV : MeasurableSet (V : Set (EuclideanSpace ℝ ι)) := V.isOpen.measurableSet
  obtain ⟨U, hUv, hUg⟩ := W1p.exists_value_gradient_ae_eq_of_contDiffOn_of_isCompact (mu := mu)
    (p := 2) hO (hw.of_le one_le_two) hL hVL hVO'
  -- The truncation `(w - ε)⁺` vanishes off `K`, so it has zero boundary values on `V`.
  have hP : W1p.posPartAbove h2 hε.le U ∈ w1p0Submodule mu V 2 := by
    refine W1p.mem_w1p0Submodule_of_isCompact h2 hK hKV ?_
    filter_upwards [W1p.value_posPartAbove_ae h2 hε.le U, hUv, ae_restrict_mem hV]
      with x hx hxw hxV hxK
    rw [hx, hxw, max_eq_right (sub_nonpos.2 (not_le.1 fun h => hxK (hUK ⟨hVO hxV, h⟩)).le)]
  have hgreen := energyFormH1_one_zero_zero_eq_setIntegral_neg_laplacian_mul (hw.mono hVO) hUv
    (((hw.continuousOn_laplacian hO).mono hVO').memLp_restrict_of_subset_isCompact hL hV hVL 2)
    ⟨_, hP⟩
  rw [energyFormH1_one_zero_zero_apply] at hgreen
  -- The energy side is `∫_A ‖∇w‖²` over the open set `A = Ω ∩ {w > ε}`, which lies in `V`.
  set A := (Omega : Set (EuclideanSpace ℝ ι)) ∩ w ⁻¹' Ioi ε
  have hA : MeasurableSet A := (hw.continuousOn.isOpen_inter_preimage hO isOpen_Ioi).measurableSet
  have hAV : A ⊆ V := fun x hx => hKV (hUK ⟨hx.1, le_of_lt hx.2⟩)
  have hleft : ∫ x in V, W1p.gradient (W1p.posPartAbove h2 hε.le U) x ⬝ᵥ
      W1p.gradient U x ∂mu = ∫ x in A, ‖∇ w x‖ ^ 2 ∂mu := by
    rw [← inter_eq_left.2 hAV, ← Measure.restrict_restrict hA, ← integral_indicator hA]
    refine integral_congr_ae ?_
    filter_upwards [W1p.gradient_posPartAbove_ae h2 hε.le U, hUv, hUg,
      ae_restrict_mem hV] with x hPx hUx hgx hxV
    rw [hPx]
    by_cases hx : ε < w x
    · rw [indicator_of_mem (by simpa [hUx] using hx),
        indicator_of_mem (s := A) (f := fun x => ‖∇ w x‖ ^ 2) ⟨hVO hxV, hx⟩, hgx,
        ← real_inner_self_eq_norm_sq, EuclideanSpace.inner_eq_star_dotProduct, star_trivial]
    · rw [indicator_of_notMem (by simpa [hUx] using hx),
        indicator_of_notMem (s := A) (f := fun x => ‖∇ w x‖ ^ 2) fun h => hx h.2,
        WithLp.ofLp_zero, zero_dotProduct]
  -- The forcing side is at most `S ∫_Ω |Δw|`, because `0 ≤ (w - ε)⁺ ≤ |w| ≤ S` on `Ω`.
  have hbound : ∀ᵐ x ∂mu.restrict V,
      ‖-Δ w x * W1p.value (W1p.posPartAbove h2 hε.le U) x‖ ≤ S * |Δ w x| := by
    filter_upwards [W1p.value_posPartAbove_ae h2 hε.le U, hUv, ae_restrict_mem hV]
      with x hPx hUx hxV
    rw [Real.norm_eq_abs, abs_mul, abs_neg, hPx, hUx, abs_of_nonneg (le_max_right (w x - ε) 0),
      mul_comm]
    exact mul_le_mul_of_nonneg_right
      (max_le (by linarith [le_abs_self (w x), hS x (hVO hxV)]) hS0) (abs_nonneg _)
  have hΔV : IntegrableOn (fun x => S * |Δ w x|) V mu := ((hΔ.mono_set hVO).abs).const_mul S
  have hright : ∫ x in V, -Δ w x * W1p.value (W1p.posPartAbove h2 hε.le U) x ∂mu ≤
      S * ∫ x in Omega, |Δ w x| ∂mu := by
    calc _ ≤ ∫ x in V, S * |Δ w x| ∂mu :=
          integral_mono_ae (hΔV.mono' ((hΔ.mono_set hVO).aestronglyMeasurable.neg.mul
            (Lp.aestronglyMeasurable _)) hbound) hΔV
            (hbound.mono fun x hx => (le_abs_self _).trans hx)
      _ = S * ∫ x in V, |Δ w x| ∂mu := integral_const_mul S _
      _ ≤ S * ∫ x in Omega, |Δ w x| ∂mu :=
          mul_le_mul_of_nonneg_left (setIntegral_mono_set hΔ.abs
            (ae_of_all _ fun _ => abs_nonneg _) hVO.eventuallyLE) hS0
  -- Back to the Lebesgue integral of `‖∇w‖ₑ²`.
  have hintA : IntegrableOn (fun x => ‖∇ w x‖ ^ 2) A mu := by
    refine ((W1p.integrable_norm_gradient_sq U).mono_measure
      (Measure.restrict_mono hAV le_rfl)).congr ?_
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hAV hUg] with x hx
    rw [hx]
  calc ∫⁻ x in A, ‖∇ w x‖ₑ ^ 2 ∂mu = ENNReal.ofReal (∫ x in A, ‖∇ w x‖ ^ 2 ∂mu) := by
        rw [ofReal_integral_eq_lintegral_ofReal hintA (ae_of_all _ fun _ => by positivity)]
        refine lintegral_congr fun x => ?_
        rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
    _ ≤ ENNReal.ofReal (S * ∫ x in Omega, |Δ w x| ∂mu) :=
        ENNReal.ofReal_le_ofReal (hleft ▸ hgreen ▸ hright)

omit [DecidableEq ι] in
/-- **The Dirichlet energy of a classical solution is finite.** Under the hypotheses of
`setLIntegral_enorm_gradient_sq_le`, `∫_Ω ‖∇w‖² ≤ 2 S ∫_Ω |Δw|`: the bound above each level `ε > 0`
of `w` and of `-w`, in the limit `ε → 0`, controls the energy on `{w ≠ 0}`, and `∇w = 0` almost
everywhere on `{w = 0}`. -/
private theorem setLIntegral_enorm_gradient_sq_le_add
    (hb : Bornology.IsBounded (Omega : Set (EuclideanSpace ℝ ι))) (hw : ContDiffOn ℝ 2 w Omega)
    (hwc : ContinuousOn w (closure (Omega : Set (EuclideanSpace ℝ ι))))
    (hw0 : ∀ x ∈ frontier (Omega : Set (EuclideanSpace ℝ ι)), w x = 0)
    (hΔ1 : IntegrableOn (Δ w) Omega mu) {S : ℝ}
    (hS : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), |w x| ≤ S) (hS0 : 0 ≤ S) :
    ∫⁻ x in Omega, ‖∇ w x‖ₑ ^ 2 ∂mu ≤
      ENNReal.ofReal (S * ∫ x in Omega, |Δ w x| ∂mu) +
        ENNReal.ofReal (S * ∫ x in Omega, |Δ w x| ∂mu) := by
  have hO := Omega.isOpen
  set C := ENNReal.ofReal (S * ∫ x in Omega, |Δ w x| ∂mu)
  -- The energy above each level `ε > 0` of `|w|`, from the truncations of `w` and of `-w`.
  have hlevel (ε : ℝ) (hε : 0 < ε) :
      ∫⁻ x in (Omega : Set (EuclideanSpace ℝ ι)) ∩ {x | ε < |w x|}, ‖∇ w x‖ₑ ^ 2 ∂mu ≤ C + C := by
    have hsplit : (Omega : Set (EuclideanSpace ℝ ι)) ∩ {x | ε < |w x|} =
        ((Omega : Set (EuclideanSpace ℝ ι)) ∩ w ⁻¹' Ioi ε) ∪
          ((Omega : Set (EuclideanSpace ℝ ι)) ∩ (-w) ⁻¹' Ioi ε) := by
      ext x
      simp only [mem_inter_iff, mem_ofPred_eq, mem_union, mem_preimage, mem_Ioi, Pi.neg_apply,
        lt_abs]
      tauto
    have hneg := setLIntegral_enorm_gradient_sq_le (w := -w) hb hw.neg hwc.neg
      (fun x hx => by simp [hw0 x hx]) (by rw [laplacian_neg]; exact hΔ1.neg)
      (fun x hx => by simpa using hS x hx) hS0 hε
    have hgneg (x : EuclideanSpace ℝ ι) : ‖∇ (-w) x‖ₑ = ‖∇ w x‖ₑ := by
      rw [← ofReal_norm, ← ofReal_norm, norm_gradient_eq_norm_fderiv,
        norm_gradient_eq_norm_fderiv, fderiv_neg, norm_neg]
    simp only [hgneg, laplacian_neg, Pi.neg_apply, abs_neg] at hneg
    rw [hsplit]
    exact (lintegral_union_le _ _ _).trans (add_le_add
      (setLIntegral_enorm_gradient_sq_le hb hw hwc hw0 hΔ1 hS hS0 hε) hneg)
  -- Letting `ε → 0`, the energy on the set where `w ≠ 0`.
  have hnz : ∫⁻ x in (Omega : Set (EuclideanSpace ℝ ι)) ∩ {x | w x ≠ 0}, ‖∇ w x‖ₑ ^ 2 ∂mu ≤
      C + C := by
    have hU : (Omega : Set (EuclideanSpace ℝ ι)) ∩ {x | w x ≠ 0} =
        ⋃ n : ℕ, (Omega : Set (EuclideanSpace ℝ ι)) ∩ {x | 1 / ((n : ℝ) + 1) < |w x|} := by
      ext x
      simp only [mem_inter_iff, mem_ofPred_eq, mem_iUnion]
      refine ⟨fun ⟨hx, hx0⟩ => ?_, fun ⟨n, hx, hn⟩ => ⟨hx, abs_pos.1 (lt_trans (by positivity) hn)⟩⟩
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (abs_pos.2 hx0)
      exact ⟨n, hx, hn⟩
    rw [hU, setLIntegral_iUnion_of_directed]
    · exact iSup_le fun n => hlevel _ Nat.one_div_pos_of_nat
    · refine Monotone.directed_le fun n m hnm x hx => ⟨hx.1, ?_⟩
      simp only [mem_ofPred_eq] at hx ⊢
      exact lt_of_le_of_lt (Nat.one_div_le_one_div hnm) hx.2
  -- The gradient vanishes almost everywhere on the zero set.
  have hA : MeasurableSet ((Omega : Set (EuclideanSpace ℝ ι)) ∩ {x | w x ≠ 0}) :=
    (hw.continuousOn.isOpen_inter_preimage hO isOpen_compl_singleton).measurableSet
  calc ∫⁻ x in Omega, ‖∇ w x‖ₑ ^ 2 ∂mu
      = ∫⁻ x in Omega, ((Omega : Set (EuclideanSpace ℝ ι)) ∩ {x | w x ≠ 0}).indicator
          (fun x => ‖∇ w x‖ₑ ^ 2) x ∂mu := by
        refine lintegral_congr_ae ?_
        filter_upwards [gradient_ae_eq_zero_on_level_set_of_contDiffOn (hw.of_le one_le_two) 0,
          ae_restrict_mem hO.measurableSet] with x hx hxO
        by_cases h : w x = 0
        · rw [indicator_of_notMem (s := (Omega : Set (EuclideanSpace ℝ ι)) ∩ {x | w x ≠ 0})
            fun h' => h'.2 h, hx h]
          simp
        · rw [indicator_of_mem (s := (Omega : Set (EuclideanSpace ℝ ι)) ∩ {x | w x ≠ 0})
            ⟨hxO, h⟩]
    _ = ∫⁻ x in (Omega : Set (EuclideanSpace ℝ ι)) ∩ {x | w x ≠ 0}, ‖∇ w x‖ₑ ^ 2 ∂mu := by
        rw [lintegral_indicator hA, Measure.restrict_restrict hA,
          inter_eq_left.2 inter_subset_left]
    _ ≤ C + C := hnz

/-- **A classical solution of the Dirichlet problem is the weak solution.** Let `Ω` be a bounded
open set and let `w` be of class `C²` on `Ω`, continuous on `closure Ω` and zero on
`frontier Ω`, with `Δw ∈ L²(Ω)`. Then `w` has finite Dirichlet energy and represents an element
`u ∈ H¹₀(Ω)` that solves `-Δu = -Δw` weakly, in `Ω` with `u = 0` on `∂Ω`. No regularity of `∂Ω`
is assumed, and of `w` up to the boundary only continuity. -/
theorem exists_isWeakSolutionDirichlet_laplacian_of_contDiffOn
    (hb : Bornology.IsBounded (Omega : Set (EuclideanSpace ℝ ι))) (hw : ContDiffOn ℝ 2 w Omega)
    (hwc : ContinuousOn w (closure (Omega : Set (EuclideanSpace ℝ ι))))
    (hw0 : ∀ x ∈ frontier (Omega : Set (EuclideanSpace ℝ ι)), w x = 0)
    (hΔ : MemLp (Δ w) 2 (mu.restrict Omega)) :
    ∃ u : W1p0 mu Omega 2, W1p.value (u : W1p mu Omega 2) =ᵐ[mu.restrict Omega] w ∧
      IsWeakSolutionDirichlet (fun _ => 1) 0 0 (hΔ.neg.toLp _) u := by
  have hO := Omega.isOpen
  have hOm := hO.measurableSet
  have : IsFiniteMeasure (mu.restrict Omega) := isFiniteMeasure_restrict.2 hb.measure_lt_top.ne
  have hΔ1 : IntegrableOn (Δ w) Omega mu := hΔ.integrable one_le_two
  obtain ⟨S₀, hS₀⟩ := hb.isCompact_closure.exists_bound_of_continuousOn hwc
  have hS : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), |w x| ≤ max S₀ 0 := fun x hx =>
    (hS₀ x (subset_closure hx)).trans (le_max_left _ _)
  have hgm : AEStronglyMeasurable (∇ w) (mu.restrict Omega) :=
    (measurable_gradient w).aestronglyMeasurable
  -- `∇w` and `w` are square integrable on `Ω`.
  have hg : MemLp (∇ w) 2 (mu.restrict Omega) := by
    refine (memLp_two_iff_integrable_sq_norm hgm).2 ⟨hgm.norm.pow 2, ?_⟩
    refine lt_of_le_of_lt (le_of_eq (lintegral_congr fun x => ?_))
      ((setLIntegral_enorm_gradient_sq_le_add hb hw hwc hw0 hΔ1 hS (le_max_right S₀ 0)).trans_lt
        (ENNReal.add_lt_top.2 ⟨ENNReal.ofReal_lt_top, ENNReal.ofReal_lt_top⟩))
    rw [enorm_pow, enorm_norm]
  have hv : MemLp w 2 (mu.restrict Omega) :=
    MemLp.of_bound (hw.continuousOn.aestronglyMeasurable hOm) (max S₀ 0)
      ((ae_restrict_iff' hOm).2 (ae_of_all _ fun x hx => by rw [Real.norm_eq_abs]; exact hS x hx))
  -- So `w` is a Sobolev function, with zero boundary values, solving the equation weakly.
  obtain ⟨U, hUv, -⟩ := W1p.exists_value_gradient_ae_eq_of_contDiffOn (hw.of_le one_le_two) hv hg
  refine ⟨⟨U, W1p.mem_w1p0Submodule_of_continuousOn_closure ENNReal.ofNat_ne_top hb hwc hw0 hUv⟩,
    hUv, (isWeakSolutionDirichlet_iff _ _).2 fun v => ?_⟩
  rw [energyFormH1_one_zero_zero_eq_setIntegral_neg_laplacian_mul hw hUv hΔ v]
  refine integral_congr_ae ?_
  filter_upwards [hΔ.neg.coeFn_toLp] with x hx
  rw [hx, Pi.neg_apply]

/-- **A classical Dirichlet eigenfunction of `-Δ` is a weak one.** Let `Ω` be a bounded open set
and let `w` be of class `C²` on `Ω`, continuous on `closure Ω` and zero on `frontier Ω`, with
`-Δw = κ w` on `Ω`. Then `w` represents some `u ∈ H¹₀(Ω)` with `∫_Ω ∇v · ∇u = κ ∫_Ω u v` for
every `v ∈ H¹₀(Ω)`. No regularity of `∂Ω` is assumed. -/
theorem exists_value_ae_eq_and_energyFormH1_eq_of_laplacian_eq
    (hb : Bornology.IsBounded (Omega : Set (EuclideanSpace ℝ ι))) (hw : ContDiffOn ℝ 2 w Omega)
    (hwc : ContinuousOn w (closure (Omega : Set (EuclideanSpace ℝ ι))))
    (hw0 : ∀ x ∈ frontier (Omega : Set (EuclideanSpace ℝ ι)), w x = 0) {kappa : ℝ}
    (hΔ : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), Δ w x = -kappa * w x) :
    ∃ u : W1p0 mu Omega 2, W1p.value (u : W1p mu Omega 2) =ᵐ[mu.restrict Omega] w ∧
      ∀ v : W1p0 mu Omega 2,
        energyFormH1 (fun _ => 1) 0 0 (u : W1p mu Omega 2) (v : W1p mu Omega 2) =
          kappa * ⟪W1p.value (u : W1p mu Omega 2), W1p.value (v : W1p mu Omega 2)⟫_ℝ := by
  have hOm := Omega.isOpen.measurableSet
  have : IsFiniteMeasure (mu.restrict Omega) := isFiniteMeasure_restrict.2 hb.measure_lt_top.ne
  have hΔae : Δ w =ᵐ[mu.restrict Omega] fun x => -kappa * w x :=
    (ae_restrict_iff' hOm).2 (ae_of_all _ hΔ)
  -- `w` is bounded on `Ω`, so `Δw = -κ w` is square integrable there.
  obtain ⟨S, hS⟩ := hb.isCompact_closure.exists_bound_of_continuousOn hwc
  have hΔ2 : MemLp (Δ w) 2 (mu.restrict Omega) := by
    refine (MemLp.of_bound (((hw.continuousOn.aestronglyMeasurable hOm).const_mul (-kappa)))
      (|kappa| * S) ((ae_restrict_iff' hOm).2 (ae_of_all _ fun x hx => ?_))).ae_eq hΔae.symm
    rw [norm_mul, norm_neg, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hS x (subset_closure hx)) (abs_nonneg _)
  obtain ⟨u, hu, hsol⟩ := exists_isWeakSolutionDirichlet_laplacian_of_contDiffOn hb hw hwc hw0 hΔ2
  refine ⟨u, hu, fun v => ?_⟩
  rw [(isWeakSolutionDirichlet_iff _ _).1 hsol v, W1p.inner_value_eq_setIntegral,
    ← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [hΔ2.neg.coeFn_toLp, hu, hΔae] with x h1 h2 h3
  rw [h1, Pi.neg_apply, h3, h2]
  ring

/-- **The weak solution of the Dirichlet problem is the classical one.** Let `Ω ⊆ ℝ^{n+1}` be an
open set contained in a ball, and let `w` be of class `C²` on `Ω`, continuous on `closure Ω` and
zero on `frontier Ω`. If `u ∈ H¹₀(Ω)` is the weak solution of `-Δu = f` in `Ω`, `u = 0` on `∂Ω`,
for some `f ∈ L²(Ω)` with `f = -Δw` almost everywhere on `Ω`, then `u = w` almost everywhere on
`Ω`. -/
theorem IsWeakSolutionDirichlet.value_ae_eq_of_contDiffOn {n : ℕ}
    {Omega : Opens (EuclideanSpace ℝ (Fin (n + 1)))} {w : EuclideanSpace ℝ (Fin (n + 1)) → ℝ}
    {z : EuclideanSpace ℝ (Fin (n + 1))} {R : ℝ}
    (hball : (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))) ⊆ ball z R)
    (hw : ContDiffOn ℝ 2 w Omega)
    (hwc : ContinuousOn w (closure (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))))
    (hw0 : ∀ x ∈ frontier (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))), w x = 0)
    {f : Lp ℝ 2 (volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))))}
    (hf : f =ᵐ[volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))] -Δ w)
    {u : W1p0 volume Omega 2} (hu : IsWeakSolutionDirichlet (fun _ => 1) 0 0 f u) :
    W1p.value (u : W1p volume Omega 2)
      =ᵐ[volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))] w := by
  have hΔ : MemLp (Δ w) 2 (volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))) := by
    simpa using ((Lp.memLp f).ae_eq hf).neg
  obtain ⟨v, hvw, hv⟩ := exists_isWeakSolutionDirichlet_laplacian_of_contDiffOn
    (isBounded_ball.subset hball) hw hwc hw0 hΔ
  have hfv : hΔ.neg.toLp _ = f := by
    refine Lp.ext ?_
    filter_upwards [hΔ.neg.coeFn_toLp, hf] with x h1 h2
    rw [h1, h2]
  rw [hfv] at hv
  have huv : u = v := (existsUnique_isWeakSolutionDirichlet_laplacian_of_subset_ball
    (le_max_right R 0) (hball.trans (ball_subset_ball (le_max_left R 0))) f).unique hu hv
  rw [huv]
  exact hvw

end PDE

end TauCeti
