/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.SeibergWitten.DiscCharge.Basic
public import TauCeti.Analysis.Calculus.DifferentialForm.SliceMoment
import TauCeti.Topology.Discrete

/-!
# The transverse flux of the cutoff current in a tube

Let `(a, α)` be an abelian Higgs pair on a product `E × ℂ`, with `a = i b`, thought of as a
tubular neighbourhood of a pseudoholomorphic curve with base coordinate `z ∈ E` and complex
normal coordinate `w ∈ ℂ`, and let `Θ = i F_a + d(χ(|α|²) τ)` be its cutoff current
(`TauCeti.SeibergWitten.cutoffCurrent`), for a cutoff `χ` vanishing near `0` and equal to `1` on
`(c, ∞)`. In Taubes's passage from Seiberg–Witten solutions to pseudoholomorphic curves, the zeros
of `α` concentrate along the curve, so outside a tube `{‖w‖ ≤ R}` the section `α` lies in the
vacuum region `|α|² > c`. This file shows that `Θ` then has **constant integer transverse flux**:
it is a two-form supported in the tube whose normal slices `μ_z = Θ(z, w)(∂_x, ∂_y) dx dy`
(`TauCeti.sliceMoment`) all have the same total flux `∫ dμ_z = 2π n`, where `n ∈ ℤ` is the
winding number of `α` around any normal circle `{z} × {‖w‖ = ρ}` outside the tube.

* Outside the tube the cutoff current vanishes
  (`TauCeti.SeibergWitten.cutoffCurrent_eq_zero_of_notMem_closedBall`), since there `χ = 1`
  near `|α|²`.
* Over every base point `z` the flux `∫ dμ_z` is the charge of the normal disc
  `w ↦ (z, w)` of any radius `ρ ≥ 0` with `ρ > R`, which is `2π` times the winding number of
  `w ↦ α(z, w)` around its boundary circle
  (`TauCeti.SeibergWitten.exists_int_sliceMoment_cutoffCurrent_eq`, by
  `TauCeti.SeibergWitten.exists_int_integral_cutoffCurrent_comp_closedBall`).
* The flux is continuous in `z` and takes values in `2π ℤ`, so it is the same integer over the
  whole base (`TauCeti.SeibergWitten.exists_int_forall_sliceMoment_cutoffCurrent_eq`). No
  closedness of `Θ` is used for this, only the continuity of a `C²` section and a `C¹`
  connection form.
* With the closedness of `Θ`, the pairing of the cutoff current with a form `k π^*β + dη` on a
  two-dimensional base, for a compactly supported continuous base form `β` and a compactly
  supported `C¹` one-form `η`, is topological,
  `∫ Θ ∧ (k π^*β + dη) = 2π n k ∫ β`
  (`exists_int_integral_cutoffCurrent_wedge_smul_compContinuousLinearMap_fst_add_extDeriv`).
  This is a model, on the flat product chart `E × ℂ` and with `n` the winding number above, of the
  pairing of the cutoff current with a taming form; it does not by itself transport to a curved
  tube or identify `n` with the degree of the curve.
* The normal dilation `Φ_a (z, W) = (z, a W)` carries the cutoff current of `(b, α)` to that of
  the dilated pair `(Φ_a^* b, α ∘ Φ_a)`, whose slice moments are those of `Θ` with the weight
  rescaled by `a⁻¹` (`TauCeti.SeibergWitten.sliceMoment_cutoffCurrent_comp_prodMap_smul`). So the
  dilated current has the same flux, and its moments `M_k` are `a⁻ᵏ` times those of `Θ`.

## References

* C. H. Taubes, *SW ⇒ Gr: from the Seiberg–Witten equations to pseudo-holomorphic curves*,
  J. Amer. Math. Soc. 9 (1996), 845–918.
* C. H. Taubes, *Gr ⇒ SW: From pseudo-holomorphic curves to Seiberg–Witten solutions*,
  J. Differential Geom. 51 (1999), 203–334.
-/

public section

noncomputable section

open ContinuousAlternatingMap Complex Filter Set MeasureTheory
open scoped Topology Real

namespace TauCeti.SeibergWitten

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {χ : ℝ → ℝ}
  {b : E × ℂ → (E × ℂ) [⋀^Fin 1]→L[ℝ] ℝ} {α : E × ℂ → ℂ} {c R : ℝ}

/-- **The cutoff current vanishes outside the tube.** If `χ = 1` on `(c, ∞)` with `c ≥ 0`, and
`|α(z, w)|² > c` whenever `‖w‖ > R`, then the cutoff current vanishes at every point `(z, w)` with
`w` outside the closed disc of radius `R`. -/
theorem cutoffCurrent_eq_zero_of_notMem_closedBall (hc : 0 ≤ c) (hα : ContDiff ℝ 2 α)
    (hχc : EqOn χ 1 (Ioi c)) (hR : ∀ z w, R < ‖w‖ → c < normSq (α (z, w))) (z : E) {w : ℂ}
    (hw : w ∉ Metric.closedBall 0 R) : cutoffCurrent χ b α (z, w) = 0 := by
  by_contra h
  have hle := tsupport_cutoffCurrent_subset (b := b) hc hα hχc (subset_tsupport _ h)
  rw [Metric.mem_closedBall, dist_zero_right, not_le] at hw
  exact (hR z w hw).not_ge hle

/-- **The flux through a normal fibre is the winding number at its boundary.** Let `α` be a `C²`
section and `b` a `C¹` connection form, let the cutoff `χ` be `C¹`, vanish near `0` and equal `1`
on `(c, ∞)`, and let `|α(z, w)|² > c` whenever `‖w‖ > R`. Then for every radius `ρ ≥ 0` with
`ρ > R` the flux `∫ dμ_z` of the cutoff current through the normal fibre over `z` is `2π n`, where
the integer `n` is the winding number of `α(z, ·)` around the circle of radius `ρ`. -/
theorem exists_int_sliceMoment_cutoffCurrent_eq (hα : ContDiff ℝ 2 α) (hb : ContDiff ℝ 1 b)
    (hχ : ContDiff ℝ 1 χ) (hχ₀ : χ =ᶠ[𝓝 0] 0) (hχc : EqOn χ 1 (Ioi c))
    (hR : ∀ z w, R < ‖w‖ → c < normSq (α (z, w))) {ρ : ℝ} (hρ₀ : 0 ≤ ρ) (hρ : R < ρ) (z : E) :
    ∃ n : ℤ, Contour.windingNumber (fun θ ↦ α (z, circleMap 0 ρ θ)) (-π) π 0 = n ∧
      sliceMoment (cutoffCurrent χ b α) (fun _ ↦ (1 : ℝ)) z = 2 * π * n := by
  have hc := nonneg_of_cutoff_eventuallyEq_zero_of_eqOn_one hχ₀ hχc
  have hσ : ContDiff ℝ 2 fun w : ℂ ↦ (z, w) := contDiff_prodMk_right z
  have hbd (θ : ℝ) : χ (normSq (α (z, circleMap 0 ρ θ))) = 1 :=
    hχc (hR z _ (by rwa [norm_circleMap_zero, abs_of_nonneg hρ₀]))
  obtain ⟨n, hn, hI⟩ := exists_int_integral_cutoffCurrent_comp_closedBall hρ₀ hα hb hχ hχ₀ hσ hbd
  refine ⟨n, hn, ?_⟩
  -- The pullback by the normal disc `w ↦ (z, w)` evaluates the cutoff current on `(0, 1), (0, i)`.
  have hframe :
      ⇑(ContinuousLinearMap.inr ℝ E ℂ) ∘ ![(1 : ℂ), I] = ![((0 : E), (1 : ℂ)), (0, I)] := by
    ext i : 1
    fin_cases i <;> simp
  simp only [(hasFDerivAt_prodMk_right z _).fderiv, compContinuousLinearMap_apply, hframe] at hI
  rw [sliceMoment_def, ← hI, ← setIntegral_eq_integral_of_forall_compl_eq_zero
    (s := Metric.closedBall 0 ρ) fun w hw ↦ ?_]
  · simp
  · rw [cutoffCurrent_eq_zero_of_notMem_closedBall hc hα hχc hR z
      (fun h ↦ hw (Metric.closedBall_subset_closedBall hρ.le h))]
    simp

/-- **Constant integer transverse flux.** Let `α` be a `C²` section and `b` a `C¹` connection
form, let the cutoff `χ` be `C¹`, vanish near `0` and equal `1` on `(c, ∞)`, and let
`|α(z, w)|² > c` whenever `‖w‖ > R`. Then there is one integer `n` such that the flux `∫ dμ_z` of
the cutoff current through the normal fibre over every base point `z` is `2π n`, and `n` is the
winding number of `α(z, ·)` around every circle of radius `ρ ≥ 0` with `ρ > R`. -/
theorem exists_int_forall_sliceMoment_cutoffCurrent_eq (hα : ContDiff ℝ 2 α)
    (hb : ContDiff ℝ 1 b) (hχ : ContDiff ℝ 1 χ) (hχ₀ : χ =ᶠ[𝓝 0] 0) (hχc : EqOn χ 1 (Ioi c))
    (hR : ∀ z w, R < ‖w‖ → c < normSq (α (z, w))) :
    ∃ n : ℤ, (∀ z, sliceMoment (cutoffCurrent χ b α) (fun _ ↦ (1 : ℝ)) z = 2 * π * n) ∧
      ∀ z ρ, 0 ≤ ρ → R < ρ →
        Contour.windingNumber (fun θ ↦ α (z, circleMap 0 ρ θ)) (-π) π 0 = n := by
  have hc := nonneg_of_cutoff_eventuallyEq_zero_of_eqOn_one hχ₀ hχc
  set f := sliceMoment (cutoffCurrent χ b α) (fun _ ↦ (1 : ℝ))
  have hR₁ : R < max R 0 + 1 := by linarith [le_max_left R 0]
  have hρ₁ : 0 ≤ max R 0 + 1 := by linarith [le_max_right R 0]
  have hint (z : E) : ∃ n : ℤ, f z = 2 * π * n :=
    (exists_int_sliceMoment_cutoffCurrent_eq hα hb hχ hχ₀ hχc hR hρ₁ hR₁ z).imp
      fun _ h ↦ h.2
  -- The flux is continuous in the base point, since the cutoff current is continuous and vanishes
  -- outside the tube.
  have hf : Continuous f :=
    (contDiff_sliceMoment (n := 0) (isCompact_closedBall 0 R)
      (contDiff_cutoffCurrent (n := 1) hα hb hχ hχ₀ (by norm_num)) contDiff_const
      fun z _ hw ↦ cutoffCurrent_eq_zero_of_notMem_closedBall hc hα hχc hR z hw).continuous
  -- A continuous function with values in `2π ℤ` is locally constant, hence constant.
  have hloc : IsLocallyConstant f := by
    refine (IsLocallyConstant.iff_eventually_eq f).2 fun z ↦ ?_
    obtain ⟨n₀, hn₀⟩ := (hf.tendsto z).exists_eventually_eq_mul_intCast Real.two_pi_pos
      (Eventually.of_forall hint)
    exact hn₀.mono fun y hy ↦ hy.trans (mem_of_mem_nhds hn₀).symm
  obtain ⟨n, hn⟩ := hint 0
  have hconst (z : E) : f z = 2 * π * n := (hloc.apply_eq_of_preconnectedSpace z 0).trans hn
  refine ⟨n, hconst, fun z ρ hρ₀ hρ ↦ ?_⟩
  obtain ⟨m, hm, hfm⟩ := exists_int_sliceMoment_cutoffCurrent_eq hα hb hχ hχ₀ hχc hR hρ₀ hρ z
  rw [hm, Int.cast_inj, ← @Int.cast_inj ℝ]
  have := hfm.symm.trans (hconst z)
  exact mul_left_cancel₀ Real.two_pi_pos.ne' this

open ContinuousLinearMap in
/-- **The pairing of the cutoff current with a taming form is topological.** Let the base `E`
be two-dimensional with basis `e`. Let `α` be a `C³` section and `b` a `C²` connection form, let
the cutoff `χ` be `C²`, vanish near `0` and equal `1` on `(c, ∞)`, and let `|α(z, w)|² > c`
whenever `‖w‖ > R`; then the cutoff current is closed.
Let `n` be the winding number of `α` around the normal circles outside the tube. For a compactly
supported continuous base two-form `β` and a compactly supported `C¹` one-form `η` on `E × ℂ`,

`∫ Θ ∧ (k π^*β + dη) = 2π n k ∫ β`.

Top-degree coefficients are taken on the product frame `(e₀, 0), (e₁, 0), (0, 1), (0, i)` and
integrated against its Haar measure. -/
theorem exists_int_integral_cutoffCurrent_wedge_smul_compContinuousLinearMap_fst_add_extDeriv
    [MeasurableSpace E] [BorelSpace E] (e : Module.Basis (Fin 2) ℝ E) (hα : ContDiff ℝ 3 α)
    (hb : ContDiff ℝ 2 b) (hχ : ContDiff ℝ 2 χ) (hχ₀ : χ =ᶠ[𝓝 0] 0)
    (hχc : EqOn χ 1 (Ioi c)) (hR : ∀ z w, R < ‖w‖ → c < normSq (α (z, w)))
    {β : E → E [⋀^Fin 2]→L[ℝ] ℝ} (hβ : Continuous β) (hβc : HasCompactSupport β)
    {η : E × ℂ → (E × ℂ) [⋀^Fin 1]→L[ℝ] ℝ} (hη : ContDiff ℝ 1 η) (hηc : HasCompactSupport η)
    (k : ℝ) :
    ∃ n : ℤ, (∀ z ρ, 0 ≤ ρ → R < ρ →
        Contour.windingNumber (fun θ ↦ α (z, circleMap 0 ρ θ)) (-π) π 0 = n) ∧
      ∫ x, (cutoffCurrent χ b α x).wedge (k • (β x.1).compContinuousLinearMap (fst ℝ E ℂ) +
          extDeriv η x) ((e.prod Complex.basisOneI).reindex finSumFinEquiv)
          ∂((e.prod Complex.basisOneI).reindex finSumFinEquiv).addHaar =
        2 * π * n * k * ∫ z, β z e ∂e.addHaar := by
  have hc := nonneg_of_cutoff_eventuallyEq_zero_of_eqOn_one hχ₀ hχc
  obtain ⟨n, hflux, hwind⟩ := exists_int_forall_sliceMoment_cutoffCurrent_eq
    (hα.of_le (by norm_num)) (hb.of_le (by norm_num)) (hχ.of_le (by norm_num)) hχ₀ hχc hR
  refine ⟨n, hwind, ?_⟩
  have hT : ContDiff ℝ 1 (cutoffCurrent χ b α) :=
    contDiff_cutoffCurrent (n := 2) hα hb hχ hχ₀ (by norm_num)
  rw [integral_wedge_smul_compContinuousLinearMap_fst_add_extDeriv e (isCompact_closedBall 0 R) hT
    (fun z _ hw ↦
      cutoffCurrent_eq_zero_of_notMem_closedBall hc (hα.of_le (by norm_num)) hχc hR z hw)
    (fun x ↦ congr_fun (extDeriv_cutoffCurrent hα hb hχ hχ₀) x) hβ hβc hη hηc k 0, hflux 0]
  ring

/-- **The cutoff current under the normal dilation.** Let `Φ_a (z, W) = (z, a W)` be the normal
dilation, `a ≠ 0`. The cutoff current of the dilated pair `(Φ_a^* b, α ∘ Φ_a)` is the pullback
`Φ_a^* Θ` of the cutoff current `Θ` of `(b, α)` (`cutoffCurrent_comp`), so its slice moments are
those of `Θ` with the weight rescaled by `a⁻¹`: `∫ g dμ_z(Φ_a^* Θ) = ∫ g(a⁻¹ w) dμ_z(Θ)`. In
particular the dilated current has the same flux as `Θ`. -/
theorem sliceMoment_cutoffCurrent_comp_prodMap_smul {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (hα : ContDiff ℝ 2 α) (hb : ContDiff ℝ 1 b) (hχ : ContDiff ℝ 1 χ)
    (hχ₀ : χ =ᶠ[𝓝 0] 0) (g : ℂ → F) {a : ℝ} (ha : a ≠ 0) (z : E) :
    sliceMoment (cutoffCurrent χ
        (fun x ↦ (b (x.1, a • x.2)).compContinuousLinearMap
          ((ContinuousLinearMap.id ℝ E).prodMap (a • ContinuousLinearMap.id ℝ ℂ)))
        fun x ↦ α (x.1, a • x.2)) g z =
      sliceMoment (cutoffCurrent χ b α) (fun w ↦ g (a⁻¹ • w)) z := by
  set L := (ContinuousLinearMap.id ℝ E).prodMap (a • ContinuousLinearMap.id ℝ ℂ)
  have hL (x : E × ℂ) : L x = (x.1, a • x.2) := by simp [L, Prod.map]
  have hcomp (x : E × ℂ) : cutoffCurrent χ (fun x ↦ (b (L x)).compContinuousLinearMap L)
      (α ∘ L) x = (cutoffCurrent χ b α (L x)).compContinuousLinearMap L := by
    simpa only [L.fderiv] using cutoffCurrent_comp (f := L) hα.contDiffAt hb.contDiffAt hχ hχ₀
      L.contDiff.contDiffAt
  simp only [hL] at hcomp
  rw [← sliceMoment_compContinuousLinearMap_prodMap_smul _ g ha]
  exact congrArg (fun T ↦ sliceMoment T g z) (funext hcomp)

end TauCeti.SeibergWitten
