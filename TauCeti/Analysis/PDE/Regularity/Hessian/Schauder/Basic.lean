/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.Hessian.Holder
import TauCeti.Analysis.Calculus.Gradient
import TauCeti.Analysis.Calculus.IteratedFDeriv.Lp
import TauCeti.Analysis.PDE.ClassicalSolution
import TauCeti.Analysis.PDE.Ellipticity.ConstantCoefficient
import TauCeti.Analysis.InnerProductSpace.Laplacian.Basic
import TauCeti.MeasureTheory.Function.LocallyIntegrable
import TauCeti.MeasureTheory.Measure.Haar.NormedSpace
import TauCeti.Topology.MetricSpace.Holder
import TauCeti.Topology.MetricSpace.Thickening

/-!
# Interior Schauder estimates for classical solutions

Let `0 < α < 1`, and let `A` be a constant `(n + 1) × (n + 1)` matrix with
`λ ‖ξ‖² ≤ ξᵀ A ξ ≤ Λ ‖ξ‖²` and `0 < λ`. This file proves the interior `C^{2,α}` estimate for
classical solutions of `∑ᵢⱼ Aᵢⱼ ∂ᵢ∂ⱼu = f`: if `u` is `C²` on an open set containing the closed
`R`-thickening of a bounded set `S ⊆ ℝ^{n+1}`, and `f` is `α`-Hölder with constant `K` on the open
`R`-thickening `S_R`, then `D²u` is `α`-Hölder on `S`, with constant

`C (Λ / λ)^(1 + (n + 1) / 4 + α / 2) (K / λ + R^{-(n+1)/2-α} ‖D²u‖_{L²(S_R)})`,

where `C` depends only on `n` and `α`. The matrix enters only through `λ` and `Λ`, uniformly over
all matrices with these ellipticity constants. This is the estimate for the frozen operator in the
perturbation argument for equations with Hölder continuous coefficients, where the coefficients
are frozen at a point of each small ball. The lower-order term is the `L²` norm of `D²u` on the
thickening, as in Campanato's approach, rather than the supremum of `u`.

## The argument

For the Laplacian, `u` lies in `H¹(W)` for an open `W ⊇ closure S_R` with compact closure in the
domain, and Green's identity
(`TauCeti.PDE.energyFormH1_one_zero_zero_eq_setIntegral_neg_laplacian_mul`) makes it a weak
solution of `-Δu = -Δu` against `H¹₀(W)`. The interior Hölder estimate for weak solutions
(`TauCeti.PDE.exists_hasWeakLineDerivOn_and_holderOnWith_preciseRepresentative_gradient`) then
bounds the precise representative of the weak gradient of each weak derivative `∂ᵢu`. For a `C²`
function the weak derivative is the classical one and the precise representative of a continuous
function is the function itself, so `∇∂ᵢu` is `α`-Hölder on `S`. Summing over the coordinate
directions (`TauCeti.norm_iteratedFDeriv_two_sub_le_sum`) gives the estimate for `D²u`.

For a general `A`, there is a linear automorphism `e` with `‖e‖ ≤ √Λ`, `‖e⁻¹‖ ≤ 1 / √λ` and
`Δ (u ∘ e) = (∑ᵢⱼ Aᵢⱼ ∂ᵢ∂ⱼu) ∘ e` (`TauCeti.PDE.exists_continuousLinearEquiv_laplacian_comp_eq`).
The estimate for the Laplacian applies to `v = u ∘ e` on the `(R / √Λ)`-thickening of `e⁻¹ S`,
where `Δv` is `α`-Hölder with constant `K Λ^(α/2)`. Changing variables,
`‖D²v‖_{L²} ≤ Λ |det e|^(-1/2) ‖D²u‖_{L²(S_R)}`, and `|det e⁻¹| ≤ ‖e⁻¹‖^(n+1)`
(`ContinuousLinearMap.abs_det_le_opNorm_pow`). Finally `D²u = D²v ∘ e⁻¹` precomposed with `e⁻¹` in
both slots, which costs the factor `‖e⁻¹‖^(2+α) ≤ λ^(-1-α/2)`
(`ContinuousLinearEquiv.holderOnWith_iteratedFDeriv_of_comp_right`).

## Main declarations

* `TauCeti.PDE.exists_holderOnWith_iteratedFDeriv_two_of_laplacian`: the interior Schauder
  estimate for `C²` solutions of Poisson's equation.
* `TauCeti.PDE.exists_mem_nhds_holderOnWith_iteratedFDeriv_two_of_laplacian`: a `C²` function
  with locally `α`-Hölder Laplacian has locally `α`-Hölder second derivatives.
* `TauCeti.PDE.exists_holderOnWith_iteratedFDeriv_two_of_sum_smul_fderiv_fderiv`: the interior
  Schauder estimate for `C²` solutions of `∑ᵢⱼ Aᵢⱼ ∂ᵢ∂ⱼu = f`, with explicit dependence on `λ`
  and `Λ`.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Theorem 4.6 and Lemma 6.1 (reduction of a constant-coefficient operator to the Laplacian by a
  linear change of variables).
* M. Giaquinta, L. Martinazzi, *An Introduction to the Regularity Theory for Elliptic Systems,
  Harmonic Maps and Minimal Graphs*, 2nd ed., Chapter 5.
-/

public section

noncomputable section

open InnerProductSpace Laplacian MeasureTheory Metric Set TopologicalSpace TauCeti.MeasureTheory
open scoped Gradient InnerProductSpace NNReal ENNReal Topology

namespace TauCeti

namespace PDE

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin (n + 1))

/-- The weak derivative of a `C²` function along `e`, with values in `H¹(V)`, has the classical
gradient of `∂ₑu` as its weak gradient, and the precise representative of that weak gradient is
the classical gradient at every point of `V`. -/
private theorem eqOn_preciseRepresentative_gradient {U : Set E} {V : Opens E} {u g : E → ℝ}
    {e : E} (hU : IsOpen U) (hu : ContDiffOn ℝ 2 u U) (hVU : (V : Set E) ⊆ U)
    (hg : g =ᵐ[volume.restrict V] u) {d : W1p volume V 2}
    (hd : HasWeakLineDerivOn volume V g (W1p.value d) e) :
    W1p.gradient d =ᵐ[volume.restrict V] ∇ (fun y => fderiv ℝ u y e) ∧
      EqOn (preciseRepresentative volume (W1p.gradient d : E → E))
        (∇ fun y => fderiv ℝ u y e) V := by
  have hu1 : ContDiffOn ℝ 1 (fun y => fderiv ℝ u y e) U :=
    (hu.fderiv_of_isOpen hU (by norm_num)).clm_apply contDiffOn_const
  -- The weak derivative of `u` along `e` is the classical one.
  have hdw : W1p.value d =ᵐ[volume.restrict V] fun y => fderiv ℝ u y e := by
    have hcl := hasWeakFDerivOn_gradient_of_contDiffOn (μ := volume) (Ω := V)
      ((hu.of_le one_le_two).mono hVU)
    refine ((hd.congr_ae hg).ae_eq (hasWeakFDerivOn_iff.1 hcl e)).trans (ae_of_all _ fun y => ?_)
    simp [inner_gradient_left]
  -- Hence the weak gradient of `d` is the classical gradient of `∂ₑu`.
  have hgrad : W1p.gradient d =ᵐ[volume.restrict V] ∇ (fun y => fderiv ℝ u y e) :=
    (((W1p.hasWeakFDerivOn d).congr_ae hdw).ae_eq
      (hasWeakFDerivOn_gradient_of_contDiffOn (hu1.mono hVU))).mono fun x hx =>
        innerSL_inj.mp hx
  refine ⟨hgrad, eqOn_preciseRepresentative_of_continuousOn V.isOpen ?_ hgrad ?_⟩
  · exact W1p.locallyIntegrableOn_gradient d
  · exact ((InnerProductSpace.toDual ℝ E).symm.continuous.comp_continuousOn
      (hu1.continuousOn_fderiv_of_isOpen hU le_rfl)).mono hVU

/-- If the weak gradient of `d` agrees a.e. on `V` with `∇ (∂ₑu)` for a unit vector `e`, and
`fderiv u` is differentiable on a set `U ⊇ V`, then `‖∇d‖_{L²} ≤ ‖D²u‖_{L²(V)}`. -/
private theorem norm_gradient_le_toReal_eLpNorm_iteratedFDeriv_two {U : Set E} {V : Opens E}
    {u : E → ℝ} {e : E} {d : W1p volume V 2} (he : ‖e‖ = 1)
    (hVU : (V : Set E) ⊆ U) (hdiff : ∀ x ∈ U, DifferentiableAt ℝ (fderiv ℝ u) x)
    (hgrad : W1p.gradient d =ᵐ[volume.restrict V] ∇ (fun y => fderiv ℝ u y e))
    (hfin : eLpNorm (iteratedFDeriv ℝ 2 u) 2 (volume.restrict (V : Set E)) ≠ ∞) :
    ‖W1p.gradient d‖ ≤ (eLpNorm (iteratedFDeriv ℝ 2 u) 2 (volume.restrict (V : Set E))).toReal := by
  rw [Lp.norm_def, eLpNorm_congr_ae hgrad]
  refine ENNReal.toReal_mono hfin
    (eLpNorm_mono_ae (measurable_gradient _).aestronglyMeasurable ?_)
  filter_upwards [self_mem_ae_restrict V.isOpen.measurableSet] with z hz
  simpa [he] using norm_gradient_fderiv_apply_le (hdiff z (hVU hz)) e

/-- **Interior Schauder estimate for Poisson's equation, classical form.** Let `0 < α < 1`. There
is a constant `C`, depending only on `n` and `α`, such that the following holds. Let `u` be of
class `C²` on an open set `U ⊆ ℝ^{n+1}`, let `S` be bounded, `R > 0`, and suppose that the closed
`R`-thickening of `S` lies in `U` and that `Δu` is `α`-Hölder with constant `K` on the open
`R`-thickening `S_R`. Then the second derivative `D²u` is `α`-Hölder on `S`, with constant

`C (K + R^{-(n+1)/2-α} ‖D²u‖_{L²(S_R)})`. -/
theorem exists_holderOnWith_iteratedFDeriv_two_of_laplacian {α : ℝ≥0} (hα : 0 < α)
    (hα1 : α < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {U S : Set E} {u : E → ℝ} {K : ℝ≥0} {R : ℝ},
      IsOpen U → ContDiffOn ℝ 2 u U → Bornology.IsBounded S → 0 < R → cthickening R S ⊆ U →
      HolderOnWith K α (Δ u) (thickening R S) →
      HolderOnWith (C * (K + R ^ (-(((n : ℝ) + 1) / 2 + α)) *
        (eLpNorm (iteratedFDeriv ℝ 2 u) 2 (volume.restrict (thickening R S))).toReal)).toNNReal
        α (iteratedFDeriv ℝ 2 u) S := by
  obtain ⟨C₀, hC₀, h⟩ :=
    exists_hasWeakLineDerivOn_and_holderOnWith_preciseRepresentative_gradient hα hα1 (n := n)
  refine ⟨(n + 1) * C₀, by positivity, fun {U S u K R} hU hu hS hR hSU hK => ?_⟩
  have hTU : closure (thickening R S) ⊆ U :=
    (closure_thickening_subset_cthickening R S).trans hSU
  have hTc : IsCompact (closure (thickening R S)) := hS.thickening.isCompact_closure
  obtain ⟨V, hVT⟩ : ∃ V : Opens E, (V : Set E) = thickening R S := ⟨⟨_, isOpen_thickening⟩, rfl⟩
  -- An open `W` between `closure V` and `U` with compact closure, on which `u ∈ H¹(W)`.
  obtain ⟨W, hW, hTW, hWU, hWc⟩ := exists_open_between_and_isCompact_closure hTc hU hTU
  lift W to Opens E using hW with Omega
  obtain ⟨v, hv, -⟩ := W1p.exists_value_gradient_ae_eq_of_contDiffOn_of_isCompact (mu := volume)
    (Omega := Omega) (p := 2) hU (hu.of_le one_le_two) hWc subset_closure hWU
  have hΔ : MemLp (Δ u) 2 (volume.restrict Omega) :=
    ((hu.continuousOn_laplacian hU).mono hWU).memLp_restrict_of_subset_isCompact hWc
      Omega.isOpen.measurableSet subset_closure 2
  have hweak : ∀ w : W1p0 volume Omega 2,
      energyFormH1 (fun _ => 1) 0 0 v (w : W1p volume Omega 2) =
        ∫ x in Omega, -Δ u x * W1p.value (w : W1p volume Omega 2) x :=
    energyFormH1_one_zero_zero_eq_setIntegral_neg_laplacian_mul
      (hu.mono (subset_closure.trans hWU)) hv hΔ
  have hK' : HolderOnWith K α (fun x => -Δ u x) (thickening R S) := fun x hx y hy => by
    simpa only [edist_neg_neg] using hK x hx y hy
  have hVU : (V : Set E) ⊆ U := hVT ▸ subset_closure.trans hTU
  have hvV : W1p.value v =ᵐ[volume.restrict V] u :=
    ae_restrict_of_ae_restrict_of_subset (hVT ▸ subset_closure.trans hTW) hv
  -- The `L²` norm of `D²u` on `S_R` is finite.
  have hfin := TauCeti.eLpNorm_iteratedFDeriv_two_thickening_ne_top volume hU hu hS hSU
  have hdiff : ∀ x ∈ U, DifferentiableAt ℝ (fderiv ℝ u) x := fun x hx =>
    ((hu.contDiffAt (hU.mem_nhds hx)).fderiv_right (m := 1) (by norm_num)).differentiableAt
      one_ne_zero
  have hSV : S ⊆ V := hVT ▸ self_subset_thickening hR S
  set b := EuclideanSpace.basisFun (Fin (n + 1)) ℝ
  -- Each `∇∂ᵢu` is `α`-Hölder on `S`, by the weak estimate.
  have hdir : ∀ i, ∀ x ∈ S, ∀ y ∈ S,
      dist (∇ (fun z => fderiv ℝ u z (b i)) x)
        (∇ (fun z => fderiv ℝ u z (b i)) y) ≤
        C₀ * (K + R ^ (-(((n : ℝ) + 1) / 2 + α)) *
          (eLpNorm (iteratedFDeriv ℝ 2 u) 2 (volume.restrict (thickening R S))).toReal) *
          dist x y ^ (α : ℝ) := by
    intro i x hx y hy
    obtain ⟨d, hd, hhol⟩ := h (V := V) hΔ.neg hweak (hVT ▸ hTc) (hVT ▸ hTW) hK' hR
      hVT.symm.subset (b i)
    obtain ⟨hgrad, heq⟩ := eqOn_preciseRepresentative_gradient hU hu hVU hvV hd
    have hnorm : ‖W1p.gradient d‖ ≤
        (eLpNorm (iteratedFDeriv ℝ 2 u) 2 (volume.restrict (thickening R S))).toReal := by
      simpa only [hVT] using norm_gradient_le_toReal_eLpNorm_iteratedFDeriv_two (by simp) hVU
        hdiff hgrad (hVT ▸ hfin)
    have h1 := hhol.dist_le hx hy
    rw [heq (hSV hx), heq (hSV hy), Real.coe_toNNReal _ (by positivity)] at h1
    refine h1.trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
    gcongr
    simp
  rw [mul_assoc]
  have hHol := b.holderOnWith_iteratedFDeriv_two_of_dist_gradient_le (α := α) (by positivity)
    (fun x hx => hdiff x (hVU (hSV hx))) hdir
  rwa [Fintype.card_fin, Nat.cast_add, Nat.cast_one] at hHol

/-- **Local `C^{2,α}` regularity for Poisson's equation.** Let `0 < α < 1`, and let `u` be of class
`C²` on an open set `U ⊆ ℝ^{n+1}` whose Laplacian is locally `α`-Hölder on `U`. Then `D²u` is
locally `α`-Hölder on `U`: every point of `U` has a neighbourhood on which `D²u` is `α`-Hölder. -/
theorem exists_mem_nhds_holderOnWith_iteratedFDeriv_two_of_laplacian {α : ℝ≥0} (hα : 0 < α)
    (hα1 : α < 1) {U : Set E} {u : E → ℝ} (hU : IsOpen U) (hu : ContDiffOn ℝ 2 u U)
    (hΔ : ∀ x ∈ U, ∃ T ∈ 𝓝 x, ∃ K : ℝ≥0, HolderOnWith K α (Δ u) T) {x : E} (hx : x ∈ U) :
    ∃ T ∈ 𝓝 x, ∃ K : ℝ≥0, HolderOnWith K α (iteratedFDeriv ℝ 2 u) T := by
  obtain ⟨C, -, hC⟩ := exists_holderOnWith_iteratedFDeriv_two_of_laplacian (n := n) hα hα1
  obtain ⟨T, hT, K, hK⟩ := hΔ x hx
  obtain ⟨r, hr, hrUT⟩ := nhds_basis_closedBall.mem_iff.1 (Filter.inter_mem (hU.mem_nhds hx) hT)
  have hr2 : 0 < r / 2 := half_pos hr
  -- Apply the interior estimate to `S = B(x, r / 2)`, whose `r / 2`-thickenings lie in
  -- `closedBall x r ⊆ U ∩ T`.
  refine ⟨ball x (r / 2), ball_mem_nhds x hr2, _, hC hU hu isBounded_ball hr2 ?_ (hK.mono ?_)⟩
  · rw [cthickening_ball hr2.le hr2, add_halves]
    exact hrUT.trans inter_subset_left
  · refine (thickening_ball x _ _).trans ?_
    rw [add_halves]
    exact ball_subset_closedBall.trans (hrUT.trans inter_subset_right)

/-- The bookkeeping of the powers of `λ`, `Λ` and `R` in the transfer of the interior Schauder
estimate from the Laplacian to an operator with ellipticity constants `λ ≤ Λ`. -/
private theorem schauder_constant_le {lam Lam R K M C : ℝ} {α : ℝ≥0} (hlam : 0 < lam)
    (hlamLam : lam ≤ Lam) (hR : 0 < R) (hK : 0 ≤ K) (hC : 0 ≤ C) :
    C * (K * Lam ^ ((α : ℝ) / 2) + (R / √Lam) ^ (-(((n : ℝ) + 1) / 2 + α)) *
        (Lam * lam ^ (-(((n : ℝ) + 1) / 4)) * M)) * lam⁻¹ * lam ^ (-((α : ℝ) / 2)) ≤
      C * (Lam / lam) ^ (1 + ((n : ℝ) + 1) / 4 + α / 2) *
        (K / lam + R ^ (-(((n : ℝ) + 1) / 2 + α)) * M) := by
  have hLam : 0 < Lam := hlam.trans_le hlamLam
  set β : ℝ := ((n : ℝ) + 1) / 2 + α
  set γ : ℝ := 1 + ((n : ℝ) + 1) / 4 + α / 2
  have hγ : (Lam / lam) ^ γ = Lam ^ (β / 2) * Lam *
      (lam ^ (-(((n : ℝ) + 1) / 4)) * lam ^ (-((α : ℝ) / 2)) * lam⁻¹) := by
    rw [Real.div_rpow hLam.le hlam.le, div_eq_mul_inv, ← Real.rpow_neg hlam.le,
      ← Real.rpow_add_one hLam.ne', ← Real.rpow_neg_one, ← Real.rpow_add hlam,
      ← Real.rpow_add hlam]
    congr 2 <;> ring
  have hRβ : (R / √Lam) ^ (-β) = R ^ (-β) * Lam ^ (β / 2) := by
    rw [Real.div_rpow hR.le (Real.sqrt_nonneg _), Real.sqrt_eq_rpow, ← Real.rpow_mul hLam.le,
      div_eq_mul_inv, ← Real.rpow_neg hLam.le]
    ring_nf
  -- The `K` term carries the factor `(Λ / λ)^(α / 2) ≤ (Λ / λ)^γ`.
  have hT1 : K * Lam ^ ((α : ℝ) / 2) * (lam⁻¹ * lam ^ (-((α : ℝ) / 2))) ≤
      (Lam / lam) ^ γ * (K / lam) := by
    have h1 : K * Lam ^ ((α : ℝ) / 2) * (lam⁻¹ * lam ^ (-((α : ℝ) / 2))) =
        (Lam / lam) ^ ((α : ℝ) / 2) * (K / lam) := by
      rw [Real.div_rpow hLam.le hlam.le, Real.rpow_neg hlam.le]
      field_simp
    rw [h1]
    gcongr
    · exact (one_le_div hlam).2 hlamLam
    · exact le_add_of_nonneg_left (by positivity)
  -- The `M` term carries exactly the factor `(Λ / λ)^γ`.
  have hT2 : (R / √Lam) ^ (-β) * (Lam * lam ^ (-(((n : ℝ) + 1) / 4)) * M) *
      (lam⁻¹ * lam ^ (-((α : ℝ) / 2))) = (Lam / lam) ^ γ * (R ^ (-β) * M) := by
    rw [hγ, hRβ]
    ring
  calc C * (K * Lam ^ ((α : ℝ) / 2) + (R / √Lam) ^ (-β) *
          (Lam * lam ^ (-(((n : ℝ) + 1) / 4)) * M)) * lam⁻¹ * lam ^ (-((α : ℝ) / 2))
      = C * (K * Lam ^ ((α : ℝ) / 2) * (lam⁻¹ * lam ^ (-((α : ℝ) / 2))) +
          (R / √Lam) ^ (-β) * (Lam * lam ^ (-(((n : ℝ) + 1) / 4)) * M) *
            (lam⁻¹ * lam ^ (-((α : ℝ) / 2)))) := by ring
    _ ≤ C * ((Lam / lam) ^ γ * (K / lam) + (Lam / lam) ^ γ * (R ^ (-β) * M)) := by
        rw [hT2]
        gcongr
    _ = C * (Lam / lam) ^ γ * (K / lam + R ^ (-β) * M) := by ring

/-- If `Δ (u ∘ e) = (∑ᵢⱼ Aᵢⱼ ∂ᵢ∂ⱼu) ∘ e` and `‖e ξ‖ ≤ √Λ ‖ξ‖`, then `∑ᵢⱼ Aᵢⱼ ∂ᵢ∂ⱼu` being
`α`-Hölder with constant `K` on the `R`-thickening of `S` makes `Δ (u ∘ e)` `α`-Hölder with
constant `K Λ^(α/2)` on the `R / √Λ`-thickening of `e ⁻¹' S`. -/
private theorem holderOnWith_laplacian_comp {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    {e : E ≃L[ℝ] E} {Lam R : ℝ} {α : ℝ≥0} {U S : Set E} {u : E → ℝ} {K : ℝ≥0} (hLam : 0 < Lam)
    (hlip : LipschitzWith (√Lam).toNNReal e)
    (hΔ : ∀ (u : E → ℝ) (y : E), ContDiffAt ℝ 2 u (e y) → Δ (u ∘ e) y = ∑ i, ∑ j, A i j •
      fderiv ℝ (fderiv ℝ u) (e y) (EuclideanSpace.single i 1) (EuclideanSpace.single j 1))
    (hU : IsOpen U) (hu : ContDiffOn ℝ 2 u U)
    (hthick : thickening (R / √Lam) (e ⁻¹' S) ⊆ e ⁻¹' thickening R S)
    (hcthick : cthickening (R / √Lam) (e ⁻¹' S) ⊆ e ⁻¹' U)
    (hK : HolderOnWith K α (fun x => ∑ i, ∑ j, A i j • fderiv ℝ (fderiv ℝ u) x
      (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) (thickening R S)) :
    HolderOnWith (K * (Lam ^ ((α : ℝ) / 2)).toNNReal) α (Δ (u ∘ e))
      (thickening (R / √Lam) (e ⁻¹' S)) := by
  refine HolderOnWith.of_dist_le fun y hy y' hy' => ?_
  have hyU : ∀ {z}, z ∈ thickening (R / √Lam) (e ⁻¹' S) → e z ∈ U := fun hz =>
    hcthick (thickening_subset_cthickening _ _ hz)
  rw [hΔ u y (hu.contDiffAt (hU.mem_nhds (hyU hy))),
    hΔ u y' (hu.contDiffAt (hU.mem_nhds (hyU hy')))]
  have hc : K * (√Lam).toNNReal ^ (α : ℝ) = K * (Lam ^ ((α : ℝ) / 2)).toNNReal := by
    congr 1
    refine NNReal.eq ?_
    rw [NNReal.coe_rpow, Real.coe_toNNReal _ (Real.sqrt_nonneg _),
      Real.coe_toNNReal _ (by positivity), Real.sqrt_eq_rpow, ← Real.rpow_mul hLam.le]
    ring_nf
  have hcomp := hK.comp (hlip.holderWith.holderOnWith (thickening (R / √Lam) (e ⁻¹' S))) hthick
  rw [mul_one, hc] at hcomp
  exact hcomp.dist_le hy hy'

/-- **Interior Schauder estimate for constant-coefficient operators, classical form.** Let
`0 < α < 1`. There is a constant `C`, depending only on `n` and `α`, such that the following
holds. Let `A` be a matrix with `λ ‖ξ‖² ≤ ξᵀ A ξ ≤ Λ ‖ξ‖²` and `0 < λ`, let `u` be of class `C²`
on an open set `U ⊆ ℝ^{n+1}`, let `S` be bounded, `R > 0`, and suppose that the closed
`R`-thickening of `S` lies in `U` and that `∑ᵢⱼ Aᵢⱼ ∂ᵢ∂ⱼu` is `α`-Hölder with constant `K` on the
open `R`-thickening `S_R`. Then `D²u` is `α`-Hölder on `S`, with constant

`C (Λ / λ)^(1 + (n + 1) / 4 + α / 2) (K / λ + R^{-(n+1)/2-α} ‖D²u‖_{L²(S_R)})`. -/
theorem exists_holderOnWith_iteratedFDeriv_two_of_sum_smul_fderiv_fderiv {α : ℝ≥0}
    (hα : 0 < α) (hα1 : α < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {lam Lam : ℝ}, 0 < lam →
      (∀ ξ : E, lam * ‖ξ‖ ^ 2 ≤ A.toQuadraticForm' ξ) →
      (∀ ξ : E, A.toQuadraticForm' ξ ≤ Lam * ‖ξ‖ ^ 2) →
      ∀ {U S : Set E} {u : E → ℝ} {K : ℝ≥0} {R : ℝ},
      IsOpen U → ContDiffOn ℝ 2 u U → Bornology.IsBounded S → 0 < R → cthickening R S ⊆ U →
      HolderOnWith K α (fun x => ∑ i, ∑ j, A i j • fderiv ℝ (fderiv ℝ u) x
        (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) (thickening R S) →
      HolderOnWith (C * (Lam / lam) ^ (1 + ((n : ℝ) + 1) / 4 + α / 2) * (K / lam +
        R ^ (-(((n : ℝ) + 1) / 2 + α)) *
          (eLpNorm (iteratedFDeriv ℝ 2 u) 2 (volume.restrict (thickening R S))).toReal)).toNNReal
        α (iteratedFDeriv ℝ 2 u) S := by
  obtain ⟨C, hC, h⟩ := exists_holderOnWith_iteratedFDeriv_two_of_laplacian hα hα1 (n := n)
  refine ⟨C, hC, fun {A lam Lam} hlam hA hA' {U S u K R} hU hu hS hR hSU hK => ?_⟩
  -- Straighten `A` to the identity by a linear change of variables `e`, apply the estimate for
  -- the Laplacian to `v = u ∘ e`, compare the `L²` norms of `D²v` and `D²u`, and transfer the
  -- Hölder bound for `D²v` back to `D²u`.
  obtain ⟨e, he, he', hΔ⟩ := exists_continuousLinearEquiv_laplacian_comp_eq (F := ℝ) hlam hA hA'
  have hlamLam : lam ≤ Lam := by
    simpa using (hA (EuclideanSpace.single 0 1)).trans (hA' _)
  have hLam : 0 < Lam := hlam.trans_le hlamLam
  -- The transformed problem for `v = u ∘ e`, on the thickening of `e⁻¹ S` of radius `R / √Λ`.
  set v := u ∘ e
  set R' := R / √Lam
  have hR' : 0 < R' := by positivity
  have hlip : LipschitzWith (√Lam).toNNReal e := LipschitzWith.of_dist_le_mul fun y y' => by
    rw [Real.coe_toNNReal _ (Real.sqrt_nonneg _), dist_eq_norm, dist_eq_norm, ← map_sub]
    exact he' _
  have hthick : thickening R' (e ⁻¹' S) ⊆ e ⁻¹' thickening R S := by
    simpa only [Real.coe_toNNReal _ (Real.sqrt_nonneg _)] using
      hlip.thickening_preimage_subset_preimage_thickening S (R := R)
  have hcthick : cthickening R' (e ⁻¹' S) ⊆ e ⁻¹' U := by
    refine (?_ : cthickening R' (e ⁻¹' S) ⊆ e ⁻¹' cthickening R S).trans (preimage_mono hSU)
    simpa only [Real.coe_toNNReal _ (Real.sqrt_nonneg _)] using
      hlip.cthickening_preimage_subset_preimage_cthickening S
  have hS' : Bornology.IsBounded (e ⁻¹' S) := by
    rw [← e.image_symm_eq_preimage]
    exact (e.symm : E →L[ℝ] E).lipschitzWith.isBounded_image hS
  have hvhol := h (hU.preimage e.continuous)
    (hu.comp (e : E →L[ℝ] E).contDiff.contDiffOn (mapsTo_preimage _ _)) hS' hR' hcthick
    (holderOnWith_laplacian_comp hLam hlip hΔ hU hu hthick hcthick hK)
  -- The `L²` norm of `D²v` on the new thickening is controlled by that of `D²u`.
  have hesn : ‖(e.symm : E →L[ℝ] E)‖ ≤ (√lam)⁻¹ :=
    ContinuousLinearMap.opNorm_le_bound _ (by positivity) he
  have hMv : (eLpNorm (iteratedFDeriv ℝ 2 v) 2
        (volume.restrict (thickening R' (e ⁻¹' S)))).toReal ≤
      Lam * lam ^ (-(((n : ℝ) + 1) / 4)) *
        (eLpNorm (iteratedFDeriv ℝ 2 u) 2 (volume.restrict (thickening R S))).toReal := by
    have h2 := TauCeti.toReal_eLpNorm_iteratedFDeriv_two_comp_le (volume : Measure E) hlam hLam
      he' hesn hU hu hS hSU
    rwa [finrank_euclideanSpace_fin, Nat.cast_add, Nat.cast_one] at h2
  -- Transfer the Hölder bound for `D²v` on `e⁻¹ S` back to `D²u` on `S`, at the cost of
  -- `‖e⁻¹‖^{2 + α} ≤ λ^{-1-α/2}`.
  refine (e.holderOnWith_iteratedFDeriv_of_comp_right hvhol).mono_const ?_
  rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ (by positivity)]
  push_cast
  rw [Real.coe_toNNReal _ (by positivity), Real.coe_toNNReal _ (by positivity)]
  have hes2 : ‖(e.symm : E →L[ℝ] E)‖ ^ 2 ≤ lam⁻¹ :=
    (pow_le_pow_left₀ (norm_nonneg _) hesn 2).trans_eq (by rw [inv_pow, Real.sq_sqrt hlam.le])
  have hesα : ‖(e.symm : E →L[ℝ] E)‖ ^ (α : ℝ) ≤ lam ^ (-((α : ℝ) / 2)) :=
    (Real.rpow_le_rpow (norm_nonneg _) hesn α.coe_nonneg).trans_eq (by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hlam.le, ← Real.rpow_mul hlam.le]
      ring_nf)
  calc C * (K * Lam ^ ((α : ℝ) / 2) + R' ^ (-(((n : ℝ) + 1) / 2 + α)) *
          (eLpNorm (iteratedFDeriv ℝ 2 v) 2 (volume.restrict (thickening R' (e ⁻¹' S)))).toReal) *
        ‖(e.symm : E →L[ℝ] E)‖ ^ 2 * ‖(e.symm : E →L[ℝ] E)‖ ^ (α : ℝ)
      ≤ C * (K * Lam ^ ((α : ℝ) / 2) + R' ^ (-(((n : ℝ) + 1) / 2 + α)) *
          (Lam * lam ^ (-(((n : ℝ) + 1) / 4)) *
            (eLpNorm (iteratedFDeriv ℝ 2 u) 2 (volume.restrict (thickening R S))).toReal)) *
        lam⁻¹ * lam ^ (-((α : ℝ) / 2)) := by gcongr
    _ ≤ _ := schauder_constant_le hlam hlamLam hR K.coe_nonneg hC

end PDE

end TauCeti
