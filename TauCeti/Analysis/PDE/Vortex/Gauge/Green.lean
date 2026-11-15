/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.Gauge.Laplacian
public import TauCeti.Analysis.Sobolev.BesselPotential.Real

/-!
# The gauge Laplacian as an isomorphism of Sobolev spaces

At a plane vortex field `x = (b₁, b₂, p, q)` the gauge Laplacian `d₀* d₀ = -Δ + (p² + q²)` is a
Schrödinger operator (`TauCeti.Vortex.integral_mul_gaugeAdjoint_gaugeDirection`). When `x` is a
continuous field of the affine space `A_m^k`, `k ≥ 2`, and `j ≤ k`, the equation `d₀* d₀ u = g`
has, for every `g ∈ H^j(ℂ)`, a weak solution `u ∈ H^(j+2)(ℂ)`, unique among weak solutions in
`L²(ℂ)`
(`TauCeti.Vortex.exists_mem_realSobolevFunctions_integral_mul_gaugeAdjoint_gaugeDirection_eq`,
`TauCeti.Vortex.ae_eq_of_integral_mul_gaugeAdjoint_gaugeDirection_eq`). This file packages these
statements about functions as bounded operators between the completed Sobolev spaces.

The spaces are the real Banach spaces `H^s_ℝ(ℂ) = BesselPotentialSpace.realSubmodule ℂ s`, the
closed real subspaces of Mathlib's Bessel-potential spaces `H^s(ℂ)` formed by the real `H^s`
functions, read off by `BesselPotentialSpace.reValue`. Gauge parameters are real functions, and
these are the domain and target of the linearized Coulomb gauge condition.

* `TauCeti.Vortex.gaugeGreen : H^j_ℝ(ℂ) →L[ℝ] H^(j+2)_ℝ(ℂ)`, the **Green operator**: the real part
  of `gaugeGreen g` is a weak solution of `d₀* d₀ u = g` (`TauCeti.Vortex.gaugeGreen_spec`), and
  `gaugeGreen g` is the only element of `H^(j+2)_ℝ(ℂ)` with this property
  (`TauCeti.Vortex.eq_gaugeGreen_iff`).
* Conversely, every real `w ∈ H^(j+2)(ℂ)` has `d₀* d₀ w ∈ H^j(ℂ)` weakly
  (`exists_mem_realSobolevFunctions_integral_mul_gaugeAdjoint_gaugeDirection_eq_of_mem_add_two`),
  so the Green operator is bijective (`TauCeti.Vortex.gaugeGreen_injective`,
  `TauCeti.Vortex.gaugeGreen_surjective`).
* `TauCeti.Vortex.gaugeLaplacianEquiv : H^(j+2)_ℝ(ℂ) ≃L[ℝ] H^j_ℝ(ℂ)`: the gauge Laplacian, the
  inverse of the Green operator (`TauCeti.Vortex.coe_gaugeLaplacianEquiv_symm`,
  `TauCeti.Vortex.gaugeLaplacianEquiv_gaugeGreen`, `TauCeti.Vortex.gaugeGreen_gaugeLaplacianEquiv`),
  characterized by its weak equation (`TauCeti.Vortex.gaugeLaplacianEquiv_apply_eq_iff`).

Linearity of the Green operator follows from uniqueness of weak solutions. Boundedness follows from
the closed graph theorem: if `gₙ → g` in `H^j` and `gaugeGreen gₙ → v` in `H^(j+2)`, then both
converge in `L²`, testing against a fixed compactly supported function passes to the limit
(`BesselPotentialSpace.continuous_integral_reValue_mul`), so `v` is a weak solution for `g`, and
uniqueness gives `v = gaugeGreen g`. The open mapping theorem then makes the gauge Laplacian
bounded. No explicit bounds on the operator norms are computed.

For `j = k - 1` and `k ≥ 3` this is the regularity at which the gauge Laplacian enters the slice
theorem for the action of the Sobolev framed gauge group `G_(k+1)`
(`TauCeti.Vortex.sobolevGaugeGroup`) on `A_m^k`: since `e^(itf) · x₀` has derivative `d₀ f` at
`t = 0`, the Coulomb gauge condition `d₀* (u · x₀ - x₀) = 0` has linearization `d₀* d₀` at the
identity. That linearization and the slice theorem itself are not formalized here.

## References

* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
-/

public section

noncomputable section

namespace TauCeti.Vortex

open MeasureTheory TemperedDistribution Filter BesselPotentialSpace
open scoped Laplacian ContDiff BesselPotentialSpace Topology

variable {f : ContDiffBump (0 : ℝ)} {m k j : ℕ} {x : ℂ → EuclideanSpace ℝ (Fin 4)}

/-- The image `-Δφ + (p² + q²) φ` of a compactly supported `C²` function under the gauge
Laplacian of a continuous field is square integrable. -/
private theorem memLp_neg_laplacian_add_sq_add_sq_mul (hcont : Continuous x) {φ : ℂ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ) :
    MemLp (fun z ↦ -Δ φ z + (x z 2 ^ 2 + x z 3 ^ 2) * φ z) 2 (volume : Measure ℂ) := by
  have h2 : Continuous fun z ↦ x z 2 := by fun_prop
  have h3 : Continuous fun z ↦ x z 3 := by fun_prop
  refine Continuous.memLp_of_hasCompactSupport ?_ ?_
  · exact hφ.continuous_laplacian.neg.add ((h2.pow 2).add (h3.pow 2) |>.mul hφ.continuous)
  · exact hc.laplacian.neg.add (hc.mul_left)

/-- Weak solutions of the gauge Laplacian are preserved by sums, up to null sets. -/
private theorem weak_add (hcont : Continuous x) {u u₁ u₂ g g₁ g₂ : ℂ → ℝ}
    (hu₁ : MemLp u₁ 2 volume) (hu₂ : MemLp u₂ 2 volume) (hg₁ : MemLp g₁ 2 volume)
    (hg₂ : MemLp g₂ 2 volume) (hu : u =ᵐ[volume] u₁ + u₂) (hg : g =ᵐ[volume] g₁ + g₂)
    (h₁ : ∀ φ : ℂ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      ∫ z, u₁ z * gaugeAdjoint x (gaugeDirection x φ) z = ∫ z, g₁ z * φ z)
    (h₂ : ∀ φ : ℂ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      ∫ z, u₂ z * gaugeAdjoint x (gaugeDirection x φ) z = ∫ z, g₂ z * φ z)
    (φ : ℂ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    ∫ z, u z * gaugeAdjoint x (gaugeDirection x φ) z = ∫ z, g z * φ z := by
  have hφ2 : ContDiff ℝ 2 φ := hφ.of_le (by simp)
  have hψ := memLp_neg_laplacian_add_sq_add_sq_mul hcont hφ2 hc
  have hφL : MemLp φ 2 volume := hφ.continuous.memLp_of_hasCompactSupport hc
  have e₁ := h₁ φ hφ hc
  have e₂ := h₂ φ hφ hc
  rw [integral_mul_gaugeAdjoint_gaugeDirection hφ2] at e₁ e₂ ⊢
  set ψ : ℂ → ℝ := fun z ↦ -Δ φ z + (x z 2 ^ 2 + x z 3 ^ 2) * φ z
  calc ∫ z, u z * ψ z = ∫ z, u₁ z * ψ z + u₂ z * ψ z :=
        integral_congr_ae (hu.mono fun z hz ↦ by simp only [hz, Pi.add_apply]; ring)
    _ = (∫ z, u₁ z * ψ z) + ∫ z, u₂ z * ψ z :=
        integral_add (hu₁.integrable_mul hψ) (hu₂.integrable_mul hψ)
    _ = (∫ z, g₁ z * φ z) + ∫ z, g₂ z * φ z := congrArg₂ (· + ·) e₁ e₂
    _ = ∫ z, g₁ z * φ z + g₂ z * φ z :=
        (integral_add (hg₁.integrable_mul hφL) (hg₂.integrable_mul hφL)).symm
    _ = ∫ z, g z * φ z :=
        integral_congr_ae (hg.mono fun z hz ↦ by simp only [hz, Pi.add_apply]; ring)

/-- Weak solutions of the gauge Laplacian are preserved by scalar multiples, up to null sets. -/
private theorem weak_smul {u u₁ g g₁ : ℂ → ℝ} (c : ℝ) (hu : u =ᵐ[volume] c • u₁)
    (hg : g =ᵐ[volume] c • g₁)
    (h₁ : ∀ φ : ℂ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      ∫ z, u₁ z * gaugeAdjoint x (gaugeDirection x φ) z = ∫ z, g₁ z * φ z)
    (φ : ℂ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    ∫ z, u z * gaugeAdjoint x (gaugeDirection x φ) z = ∫ z, g z * φ z := by
  calc ∫ z, u z * gaugeAdjoint x (gaugeDirection x φ) z
      = ∫ z, c * (u₁ z * gaugeAdjoint x (gaugeDirection x φ) z) :=
        integral_congr_ae (hu.mono fun z hz ↦ by simp only [hz, Pi.smul_apply, smul_eq_mul]; ring)
    _ = ∫ z, c * (g₁ z * φ z) := by rw [integral_const_mul, integral_const_mul, h₁ φ hφ hc]
    _ = ∫ z, g z * φ z :=
        integral_congr_ae (hg.mono fun z hz ↦ by simp only [hz, Pi.smul_apply, smul_eq_mul]; ring)

variable (f m) in
/-- The solution of `d₀* d₀ u = g` for `g ∈ H^j_ℝ(ℂ)`, before linearity is established. -/
private def greenFun (hk : 1 < k) (hjk : j ≤ k) (hx : x ∈ framedFieldSpace f m k)
    (hcont : Continuous x) (g : realSubmodule ℂ (j : ℝ)) :
    realSubmodule ℂ ((j : ℝ) + 2) :=
  ofRealSobolev (exists_mem_realSobolevFunctions_integral_mul_gaugeAdjoint_gaugeDirection_eq hk
    hjk hx hcont (reValue_mem_realSobolevFunctions (by positivity) g.2)).choose_spec.1

/-- The real part of `greenFun g` is a weak solution of `d₀* d₀ u = g`, for `C²` test functions. -/
private theorem greenFun_spec (hk : 1 < k) (hjk : j ≤ k) (hx : x ∈ framedFieldSpace f m k)
    (hcont : Continuous x) (g : realSubmodule ℂ (j : ℝ))
    (φ : ℂ → ℝ) (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ) :
    ∫ z, reValue (greenFun f m hk hjk hx hcont g : H^{(j : ℝ) + 2}(ℂ)) z *
        gaugeAdjoint x (gaugeDirection x φ) z = ∫ z, reValue (g : H^{(j : ℝ)}(ℂ)) z * φ z := by
  set h := exists_mem_realSobolevFunctions_integral_mul_gaugeAdjoint_gaugeDirection_eq hk hjk hx
    hcont (reValue_mem_realSobolevFunctions (by positivity) g.2)
  rw [← h.choose_spec.2 φ hφ hc]
  exact integral_congr_ae ((reValue_ofRealSobolev (by positivity) h.choose_spec.1).mono
    fun z hz ↦ by simp only [greenFun, hz])

/-- An element of `H^(j+2)_ℝ(ℂ)` whose real part is a weak solution of `d₀* d₀ u = g` is
`greenFun g`. -/
private theorem eq_greenFun (hk : 1 < k) (hjk : j ≤ k) (hx : x ∈ framedFieldSpace f m k)
    (hcont : Continuous x) (g : realSubmodule ℂ (j : ℝ))
    (v : realSubmodule ℂ ((j : ℝ) + 2))
    (hv : ∀ φ : ℂ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      ∫ z, reValue (v : H^{(j : ℝ) + 2}(ℂ)) z * gaugeAdjoint x (gaugeDirection x φ) z =
        ∫ z, reValue (g : H^{(j : ℝ)}(ℂ)) z * φ z) :
    v = greenFun f m hk hjk hx hcont g :=
  Subtype.ext <| eq_of_reValue_ae_eq (by positivity) v.2 (greenFun f m hk hjk hx hcont g).2 <|
    ae_eq_of_integral_mul_gaugeAdjoint_gaugeDirection_eq (by exact_mod_cast hk) hx hcont
      (memLp_reValue _) (memLp_reValue _) hv
      fun φ hφ hc ↦ greenFun_spec hk hjk hx hcont g φ (hφ.of_le (by simp)) hc

variable (f m) in
/-- The solution map of the gauge Laplacian as a linear map, by uniqueness of weak solutions. -/
private def greenLinear (hk : 1 < k) (hjk : j ≤ k) (hx : x ∈ framedFieldSpace f m k)
    (hcont : Continuous x) :
    realSubmodule ℂ (j : ℝ) →ₗ[ℝ]
      realSubmodule ℂ ((j : ℝ) + 2) where
  toFun := greenFun f m hk hjk hx hcont
  map_add' g₁ g₂ := by
    refine (eq_greenFun hk hjk hx hcont _ _ ?_).symm
    exact weak_add hcont (memLp_reValue _) (memLp_reValue _) (memLp_reValue _)
      (memLp_reValue _) (reValue_add _ _) (reValue_add _ _)
      (fun φ hφ hc ↦ greenFun_spec hk hjk hx hcont g₁ φ (hφ.of_le (by simp)) hc)
      (fun φ hφ hc ↦ greenFun_spec hk hjk hx hcont g₂ φ (hφ.of_le (by simp)) hc)
  map_smul' c g := by
    refine (eq_greenFun hk hjk hx hcont _ _ ?_).symm
    exact weak_smul c (reValue_smul _ _) (reValue_smul _ _)
      (fun φ hφ hc ↦ greenFun_spec hk hjk hx hcont g φ (hφ.of_le (by simp)) hc)

variable (f m) in
/-- **The Green operator of the gauge Laplacian.** Let `x` be a continuous field of the affine
space `A_m^k`, `k ≥ 2`, and `j ≤ k`. For `g ∈ H^j_ℝ(ℂ)` the element `gaugeGreen g ∈ H^(j+2)_ℝ(ℂ)` is
the unique one whose real part `u` solves `d₀* d₀ u = g` weakly (`TauCeti.Vortex.gaugeGreen_spec`,
`TauCeti.Vortex.eq_gaugeGreen_iff`). It is a bounded real-linear operator. -/
def gaugeGreen (hk : 1 < k) (hjk : j ≤ k) (hx : x ∈ framedFieldSpace f m k)
    (hcont : Continuous x) :
    realSubmodule ℂ (j : ℝ) →L[ℝ]
      realSubmodule ℂ ((j : ℝ) + 2) :=
  ContinuousLinearMap.ofSeqClosedGraph (g := greenLinear f m hk hjk hx hcont) fun g g₀ v hg hv ↦ by
    refine eq_greenFun hk hjk hx hcont g₀ v fun φ hφ hc ↦ ?_
    have hφ2 : ContDiff ℝ 2 φ := hφ.of_le (by simp)
    have hψ := memLp_neg_laplacian_add_sq_add_sq_mul hcont hφ2 hc
    have hφL : MemLp φ 2 volume := hφ.continuous.memLp_of_hasCompactSupport hc
    -- Test the weak equations of the `gaugeGreen (g n)` and pass to the limit in `L²`.
    have hl := (((continuous_integral_reValue_mul hψ).comp continuous_subtype_val).tendsto v).comp
      hv
    have hr := (((continuous_integral_reValue_mul hφL).comp continuous_subtype_val).tendsto
      g₀).comp hg
    have heq (n : ℕ) : ((fun u : H^{(j : ℝ) + 2}(ℂ) ↦ ∫ z, reValue u z *
        (-Δ φ z + (x z 2 ^ 2 + x z 3 ^ 2) * φ z)) ∘ Subtype.val ∘ greenLinear f m hk hjk hx hcont ∘
        g) n = ((fun u : H^{(j : ℝ)}(ℂ) ↦ ∫ z, reValue u z * φ z) ∘ Subtype.val ∘ g) n := by
      simp only [Function.comp_apply]
      rw [← integral_mul_gaugeAdjoint_gaugeDirection hφ2]
      exact greenFun_spec hk hjk hx hcont (g n) φ hφ2 hc
    rw [integral_mul_gaugeAdjoint_gaugeDirection hφ2]
    exact tendsto_nhds_unique (hl.congr heq) hr

/-- The real part of `gaugeGreen g` is a weak solution of `d₀* d₀ u = g`:
`∫ u · d₀* d₀ φ = ∫ g φ` for every compactly supported `C²` function `φ`. -/
theorem gaugeGreen_spec (hk : 1 < k) (hjk : j ≤ k) (hx : x ∈ framedFieldSpace f m k)
    (hcont : Continuous x) (g : realSubmodule ℂ (j : ℝ))
    (φ : ℂ → ℝ) (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ) :
    ∫ z, reValue (gaugeGreen f m hk hjk hx hcont g : H^{(j : ℝ) + 2}(ℂ)) z *
        gaugeAdjoint x (gaugeDirection x φ) z = ∫ z, reValue (g : H^{(j : ℝ)}(ℂ)) z * φ z :=
  greenFun_spec hk hjk hx hcont g φ hφ hc

/-- **Uniqueness.** An element `v ∈ H^(j+2)_ℝ(ℂ)` is `gaugeGreen g` exactly when its real part is
a weak solution of `d₀* d₀ u = g`, tested against smooth compactly supported functions. -/
theorem eq_gaugeGreen_iff (hk : 1 < k) (hjk : j ≤ k) (hx : x ∈ framedFieldSpace f m k)
    (hcont : Continuous x) {g : realSubmodule ℂ (j : ℝ)}
    {v : realSubmodule ℂ ((j : ℝ) + 2)} :
    v = gaugeGreen f m hk hjk hx hcont g ↔
      ∀ φ : ℂ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
        ∫ z, reValue (v : H^{(j : ℝ) + 2}(ℂ)) z * gaugeAdjoint x (gaugeDirection x φ) z =
          ∫ z, reValue (g : H^{(j : ℝ)}(ℂ)) z * φ z := by
  refine ⟨?_, eq_greenFun hk hjk hx hcont g v⟩
  rintro rfl φ hφ hc
  exact gaugeGreen_spec hk hjk hx hcont g φ (hφ.of_le (by simp)) hc

/-- The Green operator of the gauge Laplacian is injective: `g` is recovered from the weak
equation. -/
theorem gaugeGreen_injective (hk : 1 < k) (hjk : j ≤ k) (hx : x ∈ framedFieldSpace f m k)
    (hcont : Continuous x) : Function.Injective (gaugeGreen f m hk hjk hx hcont) := by
  intro g₁ g₂ h
  refine Subtype.ext (eq_of_reValue_ae_eq (by positivity) g₁.2 g₂.2 ?_)
  refine ae_eq_of_integral_contDiff_smul_eq ((memLp_reValue _).locallyIntegrable one_le_two)
    ((memLp_reValue _).locallyIntegrable one_le_two) fun φ hφ hc ↦ ?_
  have e₁ := gaugeGreen_spec hk hjk hx hcont g₁ φ (hφ.of_le (by simp)) hc
  have e₂ := gaugeGreen_spec hk hjk hx hcont g₂ φ (hφ.of_le (by simp)) hc
  rw [h] at e₁
  simp only [smul_eq_mul, mul_comm (φ _)]
  rw [← e₁, e₂]

/-! ### Surjectivity: the gauge Laplacian on `H^(j+2)` -/

/-- The Green operator of the gauge Laplacian is surjective: every `v ∈ H^(j+2)_ℝ(ℂ)` is
`gaugeGreen g` for `g = d₀* d₀ v`. -/
theorem gaugeGreen_surjective (hk : 1 < k) (hjk : j ≤ k) (hx : x ∈ framedFieldSpace f m k)
    (hcont : Continuous x) : Function.Surjective (gaugeGreen f m hk hjk hx hcont) := by
  intro v
  obtain ⟨g, hg, hweak⟩ :=
    exists_mem_realSobolevFunctions_integral_mul_gaugeAdjoint_gaugeDirection_eq_of_mem_add_two hk
      hjk hx (reValue_mem_realSobolevFunctions (by positivity) v.2)
  refine ⟨ofRealSobolev hg, ((eq_gaugeGreen_iff hk hjk hx hcont).2 fun φ hφ hc ↦ ?_).symm⟩
  rw [hweak φ hφ hc]
  exact integral_congr_ae ((reValue_ofRealSobolev (by positivity) hg).mono fun z hz ↦ by
    simp only [hz])

variable (f m) in
/-- **The gauge Laplacian as an isomorphism of Sobolev spaces.** Let `x` be a continuous field of
`A_m^k`, `k ≥ 2`, and `j ≤ k`. The gauge Laplacian `d₀* d₀ = -Δ + (p² + q²)` is a bounded linear
isomorphism `H^(j+2)_ℝ(ℂ) ≃L[ℝ] H^j_ℝ(ℂ)`, characterized by its weak equation
(`TauCeti.Vortex.gaugeLaplacianEquiv_spec`); its inverse is the Green operator
`TauCeti.Vortex.gaugeGreen` (`TauCeti.Vortex.coe_gaugeLaplacianEquiv_symm`). -/
def gaugeLaplacianEquiv (hk : 1 < k) (hjk : j ≤ k) (hx : x ∈ framedFieldSpace f m k)
    (hcont : Continuous x) :
    realSubmodule ℂ ((j : ℝ) + 2) ≃L[ℝ] realSubmodule ℂ (j : ℝ) :=
  (ContinuousLinearEquiv.ofBijective (gaugeGreen f m hk hjk hx hcont)
    (LinearMap.ker_eq_bot.2 (gaugeGreen_injective hk hjk hx hcont))
    (LinearMap.range_eq_top.2 (gaugeGreen_surjective hk hjk hx hcont))).symm

/-- The inverse of the gauge Laplacian is its Green operator. -/
@[simp]
theorem coe_gaugeLaplacianEquiv_symm (hk : 1 < k) (hjk : j ≤ k)
    (hx : x ∈ framedFieldSpace f m k) (hcont : Continuous x) :
    ⇑(gaugeLaplacianEquiv f m hk hjk hx hcont).symm = gaugeGreen f m hk hjk hx hcont := by
  simp [gaugeLaplacianEquiv]

/-- The real part of `v ∈ H^(j+2)_ℝ(ℂ)` is a weak solution of `d₀* d₀ v = g` for
`g = gaugeLaplacianEquiv v`. -/
theorem gaugeLaplacianEquiv_spec (hk : 1 < k) (hjk : j ≤ k) (hx : x ∈ framedFieldSpace f m k)
    (hcont : Continuous x) (v : realSubmodule ℂ ((j : ℝ) + 2)) (φ : ℂ → ℝ) (hφ : ContDiff ℝ 2 φ)
    (hc : HasCompactSupport φ) :
    ∫ z, reValue (v : H^{(j : ℝ) + 2}(ℂ)) z * gaugeAdjoint x (gaugeDirection x φ) z =
      ∫ z, reValue (gaugeLaplacianEquiv f m hk hjk hx hcont v : H^{(j : ℝ)}(ℂ)) z * φ z := by
  conv_lhs => rw [← (gaugeLaplacianEquiv f m hk hjk hx hcont).symm_apply_apply v,
    coe_gaugeLaplacianEquiv_symm]
  exact gaugeGreen_spec hk hjk hx hcont _ φ hφ hc

/-- The gauge Laplacian of `gaugeGreen g` is `g`. -/
@[simp]
theorem gaugeLaplacianEquiv_gaugeGreen (hk : 1 < k) (hjk : j ≤ k)
    (hx : x ∈ framedFieldSpace f m k) (hcont : Continuous x) (g : realSubmodule ℂ (j : ℝ)) :
    gaugeLaplacianEquiv f m hk hjk hx hcont (gaugeGreen f m hk hjk hx hcont g) = g := by
  rw [← coe_gaugeLaplacianEquiv_symm, ContinuousLinearEquiv.apply_symm_apply]

/-- The Green operator inverts the gauge Laplacian. -/
@[simp]
theorem gaugeGreen_gaugeLaplacianEquiv (hk : 1 < k) (hjk : j ≤ k)
    (hx : x ∈ framedFieldSpace f m k) (hcont : Continuous x) (v : realSubmodule ℂ ((j : ℝ) + 2)) :
    gaugeGreen f m hk hjk hx hcont (gaugeLaplacianEquiv f m hk hjk hx hcont v) = v := by
  rw [← coe_gaugeLaplacianEquiv_symm, ContinuousLinearEquiv.symm_apply_apply]

/-- `gaugeLaplacianEquiv v = g` exactly when the real part of `v` is a weak solution of
`d₀* d₀ u = g`, tested against smooth compactly supported functions. -/
theorem gaugeLaplacianEquiv_apply_eq_iff (hk : 1 < k) (hjk : j ≤ k)
    (hx : x ∈ framedFieldSpace f m k) (hcont : Continuous x) {v : realSubmodule ℂ ((j : ℝ) + 2)}
    {g : realSubmodule ℂ (j : ℝ)} :
    gaugeLaplacianEquiv f m hk hjk hx hcont v = g ↔
      ∀ φ : ℂ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
        ∫ z, reValue (v : H^{(j : ℝ) + 2}(ℂ)) z * gaugeAdjoint x (gaugeDirection x φ) z =
          ∫ z, reValue (g : H^{(j : ℝ)}(ℂ)) z * φ z := by
  rw [← eq_gaugeGreen_iff hk hjk hx hcont, ← coe_gaugeLaplacianEquiv_symm,
    ContinuousLinearEquiv.eq_symm_apply]

end TauCeti.Vortex
