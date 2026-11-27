/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.JHolomorphic.WeakDerivative
public import TauCeti.Geometry.Manifold.Instances.OnePoint.Tangent.Basic
public import TauCeti.Geometry.Symplectic.JHolomorphic.RealChart
import TauCeti.Analysis.Complex.CauchyRiemann.Weak.Bootstrap
import TauCeti.Geometry.Symplectic.Floer.RemovableSingularity.Smooth
import TauCeti.Geometry.Symplectic.JHolomorphic.Regularity

/-!
# Removal of singularities for finite-energy pseudoholomorphic curves

Let `J` be an almost complex structure on a finite-dimensional real inner product space `V`,
of class `C^ℓ`, `2 ≤ ℓ ≤ ∞`, as a map into `V →L[ℝ] V` near a compact set `K`, and tamed by a
symplectic form along the curves considered. A `C³` solution `u` of the Cauchy–Riemann equation
`∂ₜu = J(u) ∂ₛu` on a punctured disc `B(z₀, R) \ {z₀}`, with image in `K` and finite energy
`∫ ‖∂ₛu‖²`, has a limit `q` at the puncture, and the map filled with `q` at `z₀` is of class `C^ℓ`
on the whole disc and solves the Cauchy–Riemann equation there, the puncture included
(`TauCeti.SymplecticForm.exists_contDiffOn_update_of_finite_energy`). This is the removal of
singularities theorem of McDuff–Salamon, Theorem 4.1.2, for a structure of finite regularity;
the filling is smooth when `J` is.

The equation `∂ₜu = J(u) ∂ₛu` is the Floer equation
`∂ₜu - X(z, u) i = J(z, u) (∂ₛu - X(z, u) 1)` with `X = 0` and the structure `(z, x) ↦ J x`, so
the result is the corresponding case of removal of finite-energy punctures of Floer solutions
(`TauCeti.Floer.exists_contDiffOn_update_of_finite_energy`): the filling is a continuous weak
solution with weak derivative in `Lᵖ` for some `p > 2` near the puncture, interior elliptic
bootstrapping makes it `C^ℓ` on the whole disc, and the equation at `z₀` follows by continuity.

The same holds at the end of a plane. For a finite-energy solution on the exterior `‖z‖ > R` of a
disc, the inverted map `w ↦ u w⁻¹`, filled at `0` with the limit of `u` at infinity, is of class
`C^ℓ` on the disc `B(0, R⁻¹)` and solves the Cauchy–Riemann equation there
(`TauCeti.SymplecticForm.exists_contDiffOn_update_comp_inv_of_finite_energy`). Consequently a
finite-energy pseudoholomorphic plane extends to a `C^ℓ` map on the Riemann sphere `OnePoint ℂ`,
regarded as a real surface through its two holomorphic charts
(`TauCeti.SymplecticForm.exists_contMDiff_onePoint_elim_of_finite_energy`): read in the inverted
chart at `∞` the extension is the filled inverted map. Thus the bubbles of Gromov compactness,
finite-energy planes, extend to `C^ℓ` maps of the sphere; that the extension also solves the
Cauchy–Riemann equation in the chart at `∞` is the statement of
`TauCeti.SymplecticForm.exists_contDiffOn_update_comp_inv_of_finite_energy`.

## Main results

In the namespace `TauCeti.SymplecticForm`:

* `exists_contDiffOn_update_of_finite_energy`: a finite-energy puncture is removable, and the
  filling is a `C^ℓ` solution of the Cauchy–Riemann equation on the whole disc.
* `exists_contDiffOn_update_comp_inv_of_finite_energy`: the same at the end of a plane, in the
  inverted coordinate.
* `exists_tendsto_cocompact_and_contDiffOn_update_comp_inv`: the same for a `C¹` map on the
  exterior of a disc in the real coordinates `ℝ × ℝ`, holomorphic for a constant structure `J₀`
  whose metric `ω(·, J₀ ·)` is the inner product, with integrable area density; the map is
  smooth there by elliptic regularity (`TauCeti.contDiffOn_of_isComplexLinearMap_fderiv`), and the
  filling in the chart at infinity is smooth.
* `exists_contMDiff_onePoint_elim_of_finite_energy`: a finite-energy plane extends to a `C^ℓ` map
  of the Riemann sphere.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed.,
  Theorem 4.1.2 and Section 4.5 (removal of singularities) and Appendix B.4 (elliptic
  bootstrapping).
-/

public section

open Complex Filter MeasureTheory Metric Set Topology TopologicalSpace
open scoped Manifold OnePoint TauCeti.ComplexManifold

namespace TauCeti.SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] {ω : SymplecticForm V} {J₀ : AlmostComplexStructure V}
  {u : ℂ → V} {J : V → V →L[ℝ] V} {z₀ : ℂ} {R c : ℝ} {W K : Set V} {ℓ : ℕ∞}

open Classical in
/-- **Removal of singularities** (McDuff–Salamon, Theorem 4.1.2). Let `J` be `C^ℓ`, `2 ≤ ℓ ≤ ∞`,
near a compact set `K` on which `J² = -1`, and let `u` be a `C³` solution of `∂ₜu = J(u) ∂ₛu` on
the punctured disc `B(z₀, R) \ {z₀}`, with image in `K`, tamed by `ω` with a uniform constant, and
of finite energy. The fixed structure `J₀` identifies the given inner product with a symplectic
metric. Then `u` has a limit `q ∈ K` at `z₀`, and the filling `Function.update u z₀ q` is of class
`C^ℓ` on `B(z₀, R)`, with image in `K`, and solves the Cauchy–Riemann equation at every point of
`B(z₀, R)`, the puncture included. -/
theorem exists_contDiffOn_update_of_finite_energy (hℓ : 2 ≤ ℓ)
    (hg : ∀ v w, ω v (J₀ w) = inner ℝ v w) (hc : 0 < c) (hR : 0 < R)
    (hW : IsOpen W) (hJ : ContDiffOn ℝ ℓ J W) (hK : IsCompact K) (hKW : K ⊆ W)
    (hJsq : ∀ x ∈ K, ∀ v, J x (J x v) = -v)
    (hu : ContDiffOn ℝ 3 u (ball z₀ R \ {z₀}))
    (hCR : ∀ z ∈ ball z₀ R \ {z₀}, fderiv ℝ u z I = J (u z) (fderiv ℝ u z 1))
    (huK : MapsTo u (ball z₀ R \ {z₀}) K)
    (htame : ∀ z ∈ ball z₀ R \ {z₀}, ∀ v, c * ‖v‖ ^ 2 ≤ ω v (J (u z) v))
    (henergy : IntegrableOn (fun z ↦ ‖fderiv ℝ u z 1‖ ^ 2) (ball z₀ R)) :
    ∃ q ∈ K, Tendsto u (𝓝[≠] z₀) (𝓝 q) ∧ MapsTo (Function.update u z₀ q) (ball z₀ R) K ∧
      ContDiffOn ℝ ℓ (Function.update u z₀ q) (ball z₀ R) ∧
      ∀ z ∈ ball z₀ R, fderiv ℝ (Function.update u z₀ q) z I =
        J (Function.update u z₀ q z) (fderiv ℝ (Function.update u z₀ q) z 1) := by
  -- This is the case `X = 0` of the Floer equation, for the structure `(z, x) ↦ J x`.
  obtain ⟨q, hq, hlim, hmaps, hv, hF⟩ :=
    Floer.exists_contDiffOn_update_of_finite_energy (J := fun x ↦ J x.2) (X := 0)
      (W := univ ×ˢ W) hℓ hg hc hR (isOpen_univ.prod hW)
      (hJ.comp contDiff_snd.contDiffOn fun _ hx ↦ (mem_prod.1 hx).2) contDiffOn_const hK
      (prod_mono (subset_univ _) hKW) (fun x hx ↦ hJsq x.2 hx.2) hu
      (fun z hz ↦ by simpa using hCR z hz) huK htame henergy
  exact ⟨q, hq, hlim, hmaps, hv, fun z hz ↦ by simpa using hF z hz⟩

open Classical in
/-- **Removal of the singularity at the end of a plane.** Let `J` be `C^ℓ`, `2 ≤ ℓ ≤ ∞`, near a
compact set `K` on which `J² = -1`, and let `u` be a `C³` solution of `∂ₜu = J(u) ∂ₛu` on the
exterior `‖z‖ > R` of a disc, with image in `K`, tamed by `ω` with a uniform constant, and of finite
energy. The fixed structure `J₀` identifies the given inner product with a symplectic metric.
Then `u` has a limit `q ∈ K` at infinity, and the inverted map `w ↦ u w⁻¹`, filled with `q` at
`0`, is of class `C^ℓ` on `B(0, R⁻¹)`, with image in `K`, and solves the Cauchy–Riemann equation at
every point of `B(0, R⁻¹)`, `0` included. For `R ≤ 0` the disc is empty. -/
theorem exists_contDiffOn_update_comp_inv_of_finite_energy (hℓ : 2 ≤ ℓ)
    (hg : ∀ v w, ω v (J₀ w) = inner ℝ v w) (hc : 0 < c)
    (hW : IsOpen W) (hJ : ContDiffOn ℝ ℓ J W) (hK : IsCompact K) (hKW : K ⊆ W)
    (hJsq : ∀ x ∈ K, ∀ v, J x (J x v) = -v)
    (hu : ContDiffOn ℝ 3 u (closedBall 0 R)ᶜ)
    (hCR : ∀ z ∈ (closedBall (0 : ℂ) R)ᶜ, fderiv ℝ u z I = J (u z) (fderiv ℝ u z 1))
    (huK : MapsTo u (closedBall 0 R)ᶜ K)
    (htame : ∀ z ∈ (closedBall (0 : ℂ) R)ᶜ, ∀ v, c * ‖v‖ ^ 2 ≤ ω v (J (u z) v))
    (henergy : IntegrableOn (fun z ↦ ‖fderiv ℝ u z 1‖ ^ 2) (closedBall 0 R)ᶜ) :
    ∃ q ∈ K, Tendsto u (cocompact ℂ) (𝓝 q) ∧
      MapsTo (Function.update (fun w ↦ u w⁻¹) 0 q) (ball 0 R⁻¹) K ∧
      ContDiffOn ℝ ℓ (Function.update (fun w ↦ u w⁻¹) 0 q) (ball 0 R⁻¹) ∧
      ∀ w ∈ ball (0 : ℂ) R⁻¹, fderiv ℝ (Function.update (fun w ↦ u w⁻¹) 0 q) w I =
        J (Function.update (fun w ↦ u w⁻¹) 0 q w)
          (fderiv ℝ (Function.update (fun w ↦ u w⁻¹) 0 q) w 1) := by
  -- For `R ≤ 0` the disc `B(0, R⁻¹)` is empty, and the limit comes from the case `R = 1`.
  wlog hR : 0 < R generalizing R
  · have hS : (closedBall (0 : ℂ) 1)ᶜ ⊆ (closedBall (0 : ℂ) R)ᶜ :=
      compl_subset_compl.2 (closedBall_subset_closedBall (by linarith [not_lt.1 hR]))
    obtain ⟨q, hq, hlim, -⟩ := this (hu.mono hS) (fun z hz ↦ hCR z (hS hz)) (huK.mono_left hS)
      (fun z hz ↦ htame z (hS hz)) (henergy.mono_set hS) one_pos
    have hB : ball (0 : ℂ) R⁻¹ = ∅ := ball_eq_empty.2 (inv_nonpos.2 (not_lt.1 hR))
    exact ⟨q, hq, hlim, hB ▸ mapsTo_empty _ _, hB ▸ contDiffOn_empty, by simp [hB]⟩
  -- The inverted map is a finite-energy solution on the punctured disc of radius `R⁻¹`.
  obtain ⟨hv, hCRv, hvK, hvtame, hvenergy⟩ :=
    contDiffOn_comp_inv_and_integrableOn_of_finite_energy (hJ.continuousOn.mono hKW) hK hJsq hu
      hCR huK htame henergy
  obtain ⟨q, hq, hlim, hmaps, hf, hCRf⟩ :=
    ω.exists_contDiffOn_update_of_finite_energy hℓ hg hc (inv_pos.2 hR) hW hJ hK hKW
      hJsq hv hCRv hvK hvtame hvenergy
  refine ⟨q, hq, ?_, hmaps, hf, hCRf⟩
  rw [← Metric.cobounded_eq_cocompact]
  simpa [Function.comp_def] using hlim.comp tendsto_inv₀_cobounded'

open Function in
open TauCeti.Complex (realChart) in
/-- **Removal of the singularity at infinity in the chart at infinity.** Let the inner product of
`V` be the metric `⟪v, w⟫ = ω(v, J₀ w)` of `J₀`, and let `u` be `C¹` and `J₀`-holomorphic on the
exterior `‖z‖ > T` of a disc, in complex coordinates, with integrable area density
`ω(∂ₛu, ∂ₜu)` and values in a compact set `K` there. Then `u` has a limit `q ∈ K` at infinity,
and its expression `y ↦ u(y⁻¹)` in the chart at infinity, filled with `q` at `0`, is smooth on the
disc `‖y‖ < T⁻¹` with values in `K`. By
`TauCeti.isComplexLinearMap_fderiv_of_eq_comp_inv` the filled map is `J₀`-holomorphic on that
disc, its centre included. -/
theorem exists_tendsto_cocompact_and_contDiffOn_update_comp_inv {u : ℝ × ℝ → V} {T : ℝ}
    (ω : SymplecticForm V)
    (hg : ∀ v w, ω v (J₀ w) = inner ℝ v w) {K : Set V} (hK : IsCompact K)
    (hu : ContDiffOn ℝ 1 u (equivRealProdCLM.symm ⁻¹' (closedBall 0 T)ᶜ))
    (hhol : ∀ z ∈ equivRealProdCLM.symm ⁻¹' (closedBall 0 T)ᶜ, IsComplexLinearMap
      (AlmostComplexStructure.product ℝ) J₀ (fderiv ℝ u z : ℝ × ℝ →ₗ[ℝ] V))
    (hint : IntegrableOn (fun z ↦ ω (fderiv ℝ u z stdComplexLineReal)
      (fderiv ℝ u z stdComplexLineImag)) (equivRealProdCLM.symm ⁻¹' (closedBall 0 T)ᶜ))
    (huK : MapsTo u (equivRealProdCLM.symm ⁻¹' (closedBall 0 T)ᶜ) K) :
    ∃ q ∈ K, Tendsto u (cocompact (ℝ × ℝ)) (𝓝 q) ∧
      MapsTo (update (fun y ↦ u (realChart (fun ζ ↦ ζ⁻¹) y)) 0 q)
        (equivRealProdCLM.symm ⁻¹' ball 0 T⁻¹) K ∧
      ContDiffOn ℝ (⊤ : ℕ∞) (update (fun y ↦ u (realChart (fun ζ ↦ ζ⁻¹) y)) 0 q)
        (equivRealProdCLM.symm ⁻¹' ball 0 T⁻¹) := by
  set S : Set (ℝ × ℝ) := equivRealProdCLM.symm ⁻¹' (closedBall 0 T)ᶜ
  have hmem (z : ℂ) (hz : z ∈ (closedBall (0 : ℂ) T)ᶜ) : equivRealProdCLM z ∈ S := by
    rwa [mem_preimage, ContinuousLinearEquiv.symm_apply_apply]
  -- On the exterior `u` is holomorphic for the constant structure `J₀`, hence smooth.
  have hus : ContDiffOn ℝ (⊤ : ℕ∞) u S :=
    contDiffOn_of_isComplexLinearMap_fderiv (J := fun _ ↦ J₀)
      (isClosed_closedBall.isOpen_compl.preimage equivRealProdCLM.symm.continuous) isOpen_univ
      contDiffOn_const hu (mapsTo_univ _ _) hhol
  -- In the complex coordinate, the area density is `‖∂ₛu‖²`.
  have hsq (z : ℂ) (hz : z ∈ (closedBall (0 : ℂ) T)ᶜ) :
      ‖fderiv ℝ (u ∘ equivRealProdCLM) z 1‖ ^ 2 =
        ω (fderiv ℝ u (equivRealProdCLM z) stdComplexLineReal)
          (fderiv ℝ u (equivRealProdCLM z) stdComplexLineImag) := by
    have h := (hhol _ (hmem z hz)).apply_stdComplexLineImag
    simp only [ContinuousLinearMap.coe_coe] at h
    rw [fderiv_comp_equivRealProdCLM_one, h, hg, real_inner_self_eq_norm_sq]
  have hpre : measurableEquivRealProd ⁻¹' S = (closedBall (0 : ℂ) T)ᶜ := by
    ext z
    simp [S, Complex.equivRealProdCLM_symm_apply]
  have henergy : IntegrableOn (fun z ↦ ‖fderiv ℝ (u ∘ equivRealProdCLM) z 1‖ ^ 2)
      (closedBall (0 : ℂ) T)ᶜ := by
    have h := (Complex.volume_preserving_equiv_real_prod.integrableOn_comp_preimage
      measurableEquivRealProd.measurableEmbedding).2 hint
    rw [hpre] at h
    refine h.congr_fun (fun z hz ↦ ?_) isClosed_closedBall.isOpen_compl.measurableSet
    rw [hsq z hz, comp_apply, Complex.measurableEquivRealProd_apply,
      Complex.equivRealProdCLM_apply]
  obtain ⟨q, hq, hlim, hmaps, hf, -⟩ := ω.exists_contDiffOn_update_comp_inv_of_finite_energy
    (J := fun _ ↦ J₀.toLinearMap.toContinuousLinearMap) (c := 1) (W := univ) le_top hg one_pos
    isOpen_univ contDiffOn_const hK (subset_univ _) (fun x _ v ↦ by simp)
    ((hus.comp equivRealProdCLM.contDiff.contDiffOn hmem).of_le (WithTop.coe_le_coe.2 le_top))
    (fun z hz ↦ by
      simpa [fderiv_comp_equivRealProdCLM_one, fderiv_comp_equivRealProdCLM_I] using
        (hhol _ (hmem z hz)).apply_stdComplexLineImag)
    (huK.comp hmem) (fun z _ v ↦ by simp [hg]) henergy
  -- The filled map in the chart at infinity is the complex filled map read in real coordinates.
  have hw (y : ℝ × ℝ) : update (fun y ↦ u (realChart (fun ζ ↦ ζ⁻¹) y)) 0 q y =
      update (fun ζ ↦ (u ∘ equivRealProdCLM) ζ⁻¹) 0 q (equivRealProdCLM.symm y) := by
    rcases eq_or_ne y 0 with rfl | hy
    · simp
    · rw [update_of_ne hy, update_of_ne (by simpa using hy), TauCeti.Complex.realChart_apply,
        comp_apply]
  refine ⟨q, hq, ?_, fun y hy ↦ hw y ▸ hmaps hy, (hf.comp
    equivRealProdCLM.symm.contDiff.contDiffOn (mapsTo_preimage _ _)).congr fun y _ ↦ hw y⟩
  simpa [comp_def] using
    hlim.comp equivRealProdCLM.symm.toHomeomorph.isClosedEmbedding.tendsto_cocompact

/-- **A finite-energy plane extends to a sphere.** Let `J` be `C^ℓ`, `2 ≤ ℓ ≤ ∞`, near a compact set
`K` on which `J² = -1`, and let `u` be a `C³` solution of `∂ₜu = J(u) ∂ₛu` on the whole plane, with
image in `K`, tamed by `ω` with a uniform constant, and of finite energy. The fixed structure `J₀`
identifies the given inner product with a symplectic metric. Then `u` has a limit `q ∈ K` at
infinity, and sending the point at infinity to `q` extends `u` to a `C^ℓ` map on the
Riemann sphere `OnePoint ℂ`, regarded as a real surface. -/
theorem exists_contMDiff_onePoint_elim_of_finite_energy (hℓ : 2 ≤ ℓ)
    (hg : ∀ v w, ω v (J₀ w) = inner ℝ v w) (hc : 0 < c)
    (hW : IsOpen W) (hJ : ContDiffOn ℝ ℓ J W) (hK : IsCompact K) (hKW : K ⊆ W)
    (hJsq : ∀ x ∈ K, ∀ v, J x (J x v) = -v) (hu : ContDiff ℝ 3 u)
    (hCR : ∀ z, fderiv ℝ u z I = J (u z) (fderiv ℝ u z 1)) (huK : ∀ z, u z ∈ K)
    (htame : ∀ z v, c * ‖v‖ ^ 2 ≤ ω v (J (u z) v))
    (henergy : Integrable (fun z ↦ ‖fderiv ℝ u z 1‖ ^ 2)) :
    ∃ q ∈ K, ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, V) ℓ (fun x : OnePoint ℂ ↦ x.elim q u) := by
  obtain ⟨q, hq, -, -, hv, -⟩ := ω.exists_contDiffOn_update_comp_inv_of_finite_energy (R := 1) hℓ
    hg hc hW hJ hK hKW hJsq hu.contDiffOn (fun z _ ↦ hCR z) (fun z _ ↦ huK z)
    (fun z _ ↦ htame z) henergy.integrableOn
  -- On the plane `u` is a classical solution, hence `C^ℓ`.
  have hu' : ContDiff ℝ ℓ u := contDiffOn_univ.1 <|
    contDiffOn_of_fderiv_apply_I_eq isOpen_univ hW hJ (hu.contDiffOn.of_le (by norm_num))
      (fun z _ ↦ hKW (huK z)) (fun z _ ↦ hJsq _ (huK z)) fun z _ ↦ hCR z
  refine ⟨q, hq, fun x ↦ ?_⟩
  induction x using OnePoint.rec with
  | infty =>
    -- Near `∞` the extension is the filled inverted map read in the inverted chart.
    have hchart : ⇑(extChartAt 𝓘(ℝ, ℂ) (∞ : OnePoint ℂ)) = OnePoint.invChart := by
      simp [OnePoint.chartAt_infty]
    have heq : (fun x : OnePoint ℂ ↦ x.elim q u) =ᶠ[𝓝 ∞]
        Function.update (fun w ↦ u w⁻¹) 0 q ∘ OnePoint.invChart := by
      filter_upwards [OnePoint.invChart.open_source.mem_nhds
        (by simp [OnePoint.invChart_source])] with x hx
      induction x using OnePoint.rec with
      | infty => simp [OnePoint.invChart_infty]
      | coe z =>
        have hz : z ≠ 0 := fun h ↦ by simp [OnePoint.invChart_source, h] at hx
        simp [OnePoint.invChart_coe, hz]
    refine ContMDiffAt.congr_of_eventuallyEq ?_ heq
    refine ContMDiffAt.comp_of_eq (hv.contDiffAt (ball_mem_nhds 0 (by norm_num))).contMDiffAt
      ?_ OnePoint.invChart_infty
    simpa [hchart] using contMDiffAt_extChartAt (I := 𝓘(ℝ, ℂ)) (n := ℓ) (x := (∞ : OnePoint ℂ))
  | coe z =>
    -- Near a finite point the extension is `u` read in the affine chart.
    have hchart : ⇑(extChartAt 𝓘(ℝ, ℂ) (z : OnePoint ℂ)) = OnePoint.affineChart := by
      simp [OnePoint.chartAt_coe]
    have heq : (fun x : OnePoint ℂ ↦ x.elim q u) =ᶠ[𝓝 (z : OnePoint ℂ)]
        u ∘ OnePoint.affineChart := by
      filter_upwards [isOpen_compl_singleton.mem_nhds (OnePoint.coe_ne_infty z)] with x hx
      induction x using OnePoint.rec with
      | infty => exact absurd rfl hx
      | coe w => simp [OnePoint.affineChart_coe]
    refine ContMDiffAt.congr_of_eventuallyEq ?_ heq
    refine ContMDiffAt.comp_of_eq hu'.contDiffAt.contMDiffAt ?_ (OnePoint.affineChart_coe z)
    simpa [hchart] using contMDiffAt_extChartAt (I := 𝓘(ℝ, ℂ)) (n := ℓ) (x := (z : OnePoint ℂ))

end TauCeti.SymplecticForm
