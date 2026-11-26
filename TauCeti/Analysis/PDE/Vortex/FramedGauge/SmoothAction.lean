/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.FramedGauge.LieGroup
public import TauCeti.Analysis.PDE.Vortex.FramedGauge.Quotient
public import TauCeti.Analysis.PDE.Vortex.FramedGauge.RealChart

/-!
# The smooth action of the Sobolev gauge group on the framed vortex fields

For an integer `k > 1`, the Sobolev framed gauge group `G_(k+1)` of plane vortices
(`TauCeti.Vortex.SobolevTopologicalGaugeGroup`) is a Lie group modelled on the real `H^(k+1)`
phases, through the exponential charts `F ↦ u exp (i F)`
(`TauCeti.Vortex.SobolevTopologicalGaugeGroup.instLieGroup`). It acts on the continuous fields
of the affine space `A_m^k = x_m + H^k(ℂ; iT*ℂ ⊕ ℂ)` of framed degree-`m` vortex fields
(`TauCeti.Vortex.SobolevFieldSpace`) by `(a, α) ↦ (a - u⁻¹ du, u α)`, and a field `x` is recorded
by the coordinates `subRef x ∈ H^k(ℂ)⁴` of `x - x_m`. This file shows that the action is smooth,
and computes its differential.

**Smoothness.** The coordinates of `u · x - x_m` are `smulCoord` of `R = Re u - 1`, `J = Im u` and
`y = subRef x` (`TauCeti.Vortex.SobolevFieldSpace.subRef_smul`). This expression is built from
derivatives, inclusions, multiplications in the algebra `H^k(ℂ)` and multiplications by the
reference coordinates, all continuous linear or bilinear, so it is a smooth function of
`(R, J, y)` (`TauCeti.Vortex.SobolevFieldSpace.contDiff_smulCoord`). Since `R` and `J` are smooth
functions of `u ∈ G_(k+1)`, the action is smooth in the affine coordinates of `A_m^k`
(`TauCeti.Vortex.SobolevFieldSpace.contMDiff_smulCoord_reSubOne_imPart`); in particular every
orbit map `u ↦ u · x` is smooth (`TauCeti.Vortex.SobolevFieldSpace.contMDiff_subRef_smul`). In
exponential coordinates `u = exp (i F)`, the action is jointly smooth in the real phase `F` and
the coordinates `y` (`TauCeti.Vortex.SobolevFieldSpace.contDiff_smulCoord_expGauge`). In the real
coordinates `realSubRef` of the fields, the action is jointly smooth in the gauge and the field
(`TauCeti.Vortex.SobolevFieldSpace.contMDiff_realSubRef_smul_ofRealSubRef`), in particular in
exponential coordinates
(`TauCeti.Vortex.SobolevFieldSpace.contDiff_realSubRef_expGauge_smul_ofRealSubRef`). On a
continuous field, `exp (i F)` acts as the classical phase gauge of the continuous representative
of `F` (`TauCeti.Vortex.SobolevFieldSpace.coe_expGauge_smul`).

**The differential.** In the exponential chart at the identity, `R = cos F - 1` has derivative `0`
and `J = sin F` has derivative `G ↦ G` at `F = 0`. Differentiating `smulCoord` there gives the
infinitesimal gauge action in the coordinates of `A_m^k`: for `x = x_m + y` with coordinates
`x = (b₁, b₂, p, q)`, a phase `G` is sent to

`d₀ G = (-∂₁ G, -∂₂ G, -q G, p G)`

(`TauCeti.Vortex.SobolevFieldSpace.gaugeDirectionCoord`,
`TauCeti.Vortex.SobolevFieldSpace.hasFDerivAt_smulCoord_expGauge_zero`). Jointly in `(F, y)`, the
derivative of `(F, y) ↦ exp (i F) · (x_m + y) - x_m` at `(0, y)` is `(G, η) ↦ d₀ G + η`
(`TauCeti.Vortex.SobolevFieldSpace.hasFDerivAt_smulCoord_expGauge_prod_zero`). By the group law, the
derivative of `F ↦ exp (i F) · x` at any `F₀` is the infinitesimal action at `exp (i F₀) · x`
(`TauCeti.Vortex.SobolevFieldSpace.hasFDerivAt_subRef_expGauge_smul`). For a real phase `G`, the
coordinates of `d₀ G` are the `L²` functions of the classical infinitesimal gauge action
`TauCeti.Vortex.gaugeDirection x g` of the continuous representative `g` of `G`
(`TauCeti.Vortex.SobolevFieldSpace.coeFn_inclusionLp_gaugeDirectionCoord_ae_eq`).

At a base field `x₀`, the differential of the Coulomb gauge-fixing map `u ↦ d₀*_(x₀) (u · x₀ - x₀)`
at the identity is therefore the gauge Laplacian `d₀*_(x₀) d₀ = -Δ + |α₀|² / 4`, an isomorphism
from `H^(k+1)` to `H^(k-1)` (`TauCeti.Vortex.sobolevGaugeLaplacianEquiv`). This is the input of the
implicit function theorem that puts the fields near `x₀` into the Coulomb slice through `x₀` and
makes the slices charts of `A_m^k / G_(k+1)`; that slice theorem is not proved here.

## Main results

* `TauCeti.Vortex.SobolevFieldSpace.contDiff_smulCoord`: the coordinates of the transformed field
  are a (complex-)smooth function of `(Re u - 1, Im u, subRef x)`.
* `TauCeti.Vortex.SobolevFieldSpace.contMDiff_smulCoord_reSubOne_imPart`,
  `TauCeti.Vortex.SobolevFieldSpace.contMDiff_subRef_smul`: the action of `G_(k+1)` on `A_m^k` is
  smooth in the affine coordinates of `A_m^k`, and so are its orbit maps.
* `TauCeti.Vortex.SobolevFieldSpace.contDiff_smulCoord_expGauge`: the action is smooth in
  exponential coordinates, jointly in the phase and the field.
* `TauCeti.Vortex.SobolevFieldSpace.contMDiff_realSubRef_smul_ofRealSubRef`,
  `TauCeti.Vortex.SobolevFieldSpace.contDiff_realSubRef_smul_ofRealSubRef`,
  `TauCeti.Vortex.SobolevFieldSpace.contDiff_realSubRef_expGauge_smul_ofRealSubRef`: the action is
  smooth in the real coordinates of the fields, jointly with the gauge or its exponential phase,
  and for a fixed gauge.
* `TauCeti.Vortex.SobolevFieldSpace.coe_expGauge_smul`: `exp (i F)` acts as the phase gauge of the
  continuous representative of `F`.
* `TauCeti.Vortex.SobolevFieldSpace.gaugeDirectionCoord`: the infinitesimal gauge action `d₀` in
  these coordinates, a bounded complex-linear map `H^(k+1)(ℂ) → H^k(ℂ)⁴`.
* `TauCeti.Vortex.SobolevFieldSpace.hasFDerivAt_smulCoord_expGauge_zero`,
  `TauCeti.Vortex.SobolevFieldSpace.hasFDerivAt_subRef_expGauge_smul`: the differential of the
  action in the exponential chart is `d₀`.
* `TauCeti.Vortex.SobolevFieldSpace.hasFDerivAt_smulCoord_expGauge_prod_zero`: jointly in the phase
  and the field coordinates, the differential at `(0, y)` is `(G, η) ↦ d₀ G + η`.
* `TauCeti.Vortex.SobolevFieldSpace.coeFn_inclusionLp_gaugeDirectionCoord_ae_eq`: `d₀` computes the
  classical infinitesimal gauge action of the continuous representative of a real phase.
* `TauCeti.Vortex.SobolevFieldSpace.exists_pos_forall_abs_norm_sectionValue_sub_le`: fields close
  in the real coordinates to a gauge transform of `y` have sections close in norm to that of `y`,
  uniformly in the gauge.

## References

* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
* C. H. Taubes, *Gr ⇒ SW: From pseudo-holomorphic curves to Seiberg–Witten solutions*,
  J. Differential Geom. 51 (1999), 203–334.
-/

public section

noncomputable section

namespace TauCeti.Vortex

open Complex Filter MeasureTheory Module TemperedDistribution BesselPotentialSpace Topology
open scoped SchwartzMap BesselPotentialSpace Manifold ContDiff

namespace SobolevFieldSpace

open SobolevTopologicalGaugeGroup

variable {f : ContDiffBump (0 : ℝ)} {m k : ℕ} [Fact (1 < k)] {hs : 1 < (k : ℝ) + 1}

/-- **The coordinates of the transformed field are smooth** in `R = Re u - 1`, `J = Im u` and the
coordinates `y` of `x - x_m`, even complex-smooth: `smulCoord` is built from continuous
complex-linear maps and the continuous bilinear product of `H^k(ℂ)`. -/
theorem contDiff_smulCoord :
    ContDiff ℂ ∞ fun p : H^{(k : ℝ) + 1}(ℂ) × H^{(k : ℝ) + 1}(ℂ) × (Fin 4 → H^{(k : ℝ)}(ℂ)) ↦
      smulCoord f m p.1 p.2.1 p.2.2 := by
  have hk := finrank_lt (k := k)
  refine contDiff_pi.2 fun j ↦ ?_
  fin_cases j
  · simp only [Fin.zero_eta, smulCoord_zero hk]; fun_prop
  · simp only [Fin.mk_one, smulCoord_one hk]; fun_prop
  · simp only [Fin.reduceFinMk, smulCoord_two hk]; fun_prop
  · simp only [Fin.reduceFinMk, smulCoord_three hk]; fun_prop

variable (f m hs) in
/-- **The action of `G_(k+1)` on `A_m^k` is smooth** in the affine coordinates of `A_m^k`: the map
`(u, y) ↦ smulCoord (Re u - 1) (Im u) y`, which sends `u` and the coordinates `y = subRef x` of a
field to the coordinates of `u · x` (`subRef_smul`), is smooth on `G_(k+1) × H^k(ℂ)⁴`. -/
theorem contMDiff_smulCoord_reSubOne_imPart :
    ContMDiff (𝓘(ℝ, realSubmodule ℂ (zero_le_one.trans hs.le)).prod 𝓘(ℝ, Fin 4 → H^{(k : ℝ)}(ℂ)))
      𝓘(ℝ, Fin 4 → H^{(k : ℝ)}(ℂ)) ∞
      fun p : SobolevTopologicalGaugeGroup hs × (Fin 4 → H^{(k : ℝ)}(ℂ)) ↦
        smulCoord f m (reSubOne p.1) (imPart p.1) p.2 :=
  (contDiff_smulCoord.restrict_scalars ℝ).contMDiff.comp
    ((contMDiff_reSubOne.comp contMDiff_fst).prodMk_space
      ((contMDiff_imPart.comp contMDiff_fst).prodMk_space contMDiff_snd))

/-- **The orbit maps of the gauge action are smooth**: for a continuous field `x` of `A_m^k`, the
coordinates of `u · x - x_m` depend smoothly on `u ∈ G_(k+1)`. -/
theorem contMDiff_subRef_smul (x : SobolevFieldSpace f m k) :
    ContMDiff 𝓘(ℝ, realSubmodule ℂ (zero_le_one.trans hs.le)) 𝓘(ℝ, Fin 4 → H^{(k : ℝ)}(ℂ)) ∞
      fun u : SobolevTopologicalGaugeGroup hs ↦ subRef (u • x) := by
  simp_rw [subRef_smul]
  exact (contMDiff_smulCoord_reSubOne_imPart f m hs).comp (contMDiff_id.prodMk contMDiff_const)

/-- **The action in exponential coordinates is smooth**: the coordinates of `exp (i F) · x - x_m`
depend smoothly on the real phase `F ∈ H^(k+1)` and on the coordinates `y` of `x - x_m`. -/
theorem contDiff_smulCoord_expGauge :
    ContDiff ℝ ∞ fun p : realSubmodule ℂ (zero_le_one.trans hs.le) × (Fin 4 → H^{(k : ℝ)}(ℂ)) ↦
      smulCoord f m (reSubOne (expGauge hs p.1)) (imPart (expGauge hs p.1)) p.2 := by
  have hR := contMDiff_iff_contDiff.1 (contMDiff_reSubOne.comp (contMDiff_expGauge (hs := hs) ∞))
  have hJ := contMDiff_iff_contDiff.1 (contMDiff_imPart.comp (contMDiff_expGauge (hs := hs) ∞))
  exact (contDiff_smulCoord.restrict_scalars ℝ).comp
    ((hR.comp contDiff_fst).prodMk ((hJ.comp contDiff_fst).prodMk contDiff_snd))

variable (f m hs) in
/-- **The action of `G_(k+1)` on `A_m^k` is smooth in real coordinates**: the real coordinates of
`u · x` depend smoothly on the gauge `u ∈ G_(k+1)` and on the real coordinates `v` of the field
`x = x_m + v` (`ofRealSubRef`). -/
theorem contMDiff_realSubRef_smul_ofRealSubRef :
    ContMDiff (𝓘(ℝ, realSubmodule ℂ (zero_le_one.trans hs.le)).prod
        𝓘(ℝ, Fin 4 → realSubmodule ℂ (k.cast_nonneg : (0 : ℝ) ≤ k)))
      𝓘(ℝ, Fin 4 → realSubmodule ℂ (k.cast_nonneg : (0 : ℝ) ≤ k)) ∞
      fun p : SobolevTopologicalGaugeGroup hs ×
          (Fin 4 → realSubmodule ℂ (k.cast_nonneg : (0 : ℝ) ≤ k)) ↦
        realSubRef k.cast_nonneg
          (p.1 • ofRealSubRef (f := f) (m := m) (Nat.one_lt_cast.2 Fact.out) p.2) := by
  -- The real coordinates are the real parts of the complex coordinates `subRef`, which are given
  -- by `smulCoord` (`subRef_smul`).
  have hfun : (fun p : SobolevTopologicalGaugeGroup hs ×
        (Fin 4 → realSubmodule ℂ (k.cast_nonneg : (0 : ℝ) ≤ k)) ↦
      realSubRef k.cast_nonneg
        (p.1 • ofRealSubRef (f := f) (m := m) (Nat.one_lt_cast.2 Fact.out) p.2)) =
      fun p ↦ realPartPi ℂ k.cast_nonneg
        (smulCoord f m (reSubOne p.1) (imPart p.1) (coordInclusion ℂ k.cast_nonneg p.2)) := by
    funext p j
    rw [realPartPi_apply, ← subRef_ofRealSubRef (Nat.one_lt_cast.2 Fact.out), ← subRef_smul,
      ← coe_realSubRef k.cast_nonneg, realPartCLM_coe]
  rw [hfun]
  exact (realPartPi ℂ _).contDiff.contMDiff.comp
    ((contMDiff_smulCoord_reSubOne_imPart f m hs).comp
      (contMDiff_fst.prodMk ((coordInclusion ℂ _).contDiff.contMDiff.comp contMDiff_snd)))

/-- **A gauge acts smoothly in the real coordinates**: for `u ∈ G_(k+1)`, the real coordinates of
`u · x` are a smooth function of the real coordinates of `x`. -/
theorem contDiff_realSubRef_smul_ofRealSubRef (u : SobolevTopologicalGaugeGroup hs) :
    ContDiff ℝ ∞ fun v : Fin 4 → realSubmodule ℂ (Nat.cast_nonneg k : (0 : ℝ) ≤ k) ↦
      (u • ofRealSubRef (f := f) (m := m) (by exact_mod_cast (Fact.out : 1 < k)) v).realSubRef
        (Nat.cast_nonneg k) :=
  contMDiff_iff_contDiff.1 ((contMDiff_realSubRef_smul_ofRealSubRef f m hs).comp
    (contMDiff_const.prodMk contMDiff_id))

/-- **The action in exponential and real coordinates is smooth**: the real coordinates of
`exp (i F) · x` depend smoothly on the real phase `F ∈ H^(k+1)` and on the real coordinates `u` of
the field `x = x_m + u` (`ofRealSubRef`). -/
theorem contDiff_realSubRef_expGauge_smul_ofRealSubRef :
    ContDiff ℝ ∞ fun p : realSubmodule ℂ (zero_le_one.trans hs.le) ×
        (Fin 4 → realSubmodule ℂ (k.cast_nonneg : (0 : ℝ) ≤ k)) ↦
      realSubRef k.cast_nonneg
        (expGauge hs p.1 • ofRealSubRef (f := f) (m := m) (Nat.one_lt_cast.2 Fact.out) p.2) :=
  contMDiff_iff_contDiff.1 ((contMDiff_realSubRef_smul_ofRealSubRef f m hs).comp
    (((contMDiff_expGauge (hs := hs) ∞).comp contDiff_fst.contMDiff).prodMk
      contDiff_snd.contMDiff))

/-- **A phase acts through its continuous representative.** The gauge `exp (i F)` of `G_(k+1)`
acts on a continuous field `y` of `A_m^k` as the phase gauge `phaseGauge y φ` of the continuous
representative `φ` of `F`. -/
theorem coe_expGauge_smul (F : realSubmodule ℂ (zero_le_one.trans hs.le))
    (y : SobolevFieldSpace f m k) : ⇑(expGauge hs F • y) = phaseGauge y (continuousRep F) := by
  have hk : (1 : ℝ) < k := Nat.one_lt_cast.2 Fact.out
  have hφ : ContDiff ℝ 1 (continuousRep F) :=
    contDiff_continuousRep (finrank_real_complex_add_two_mul_lt_two_mul (by push_cast; linarith)) F
  rw [coe_smul, toSubgroup_expGauge]
  exact gaugeTransform_exp (hφ.differentiable one_ne_zero) y

variable (f m) in
/-- **The infinitesimal gauge action in the coordinates of `A_m^k`.** At the field `x_m + y`, with
coordinates `y ∈ H^k(ℂ)⁴` of `x - x_m` and `x = (b₁, b₂, p, q)`, the phase `G ∈ H^(k+1)(ℂ)` is sent
to the coordinates of `d₀ G = (-∂₁ G, -∂₂ G, -q G, p G)` (`gaugeDirectionCoord_apply`), the
derivative of the action in the exponential chart (`hasFDerivAt_smulCoord_expGauge_zero`). It is
defined on complexified phases; for a real phase and a field `x` it computes the classical
`gaugeDirection x` (`coeFn_inclusionLp_gaugeDirectionCoord_ae_eq`). -/
def gaugeDirectionCoord (y : Fin 4 → H^{(k : ℝ)}(ℂ)) :
    H^{(k : ℝ) + 1}(ℂ) →L[ℂ] Fin 4 → H^{(k : ℝ)}(ℂ) :=
  let ι : H^{(k : ℝ) + 1}(ℂ) →L[ℂ] H^{(k : ℝ)}(ℂ) := inclusion (lt_add_one _).le
  let M := mulCLM (finrank_lt (k := k))
  let D (v : ℂ) : H^{(k : ℝ) + 1}(ℂ) →L[ℂ] H^{(k : ℝ)}(ℂ) :=
    lineDerivCLM ENNReal.one_lt_two ENNReal.ofNat_ne_top v
  ContinuousLinearMap.pi ![-D 1, -D I, -((M.flip (y 3) + referenceMulCLM f m k 3) ∘L ι),
    (M.flip (y 2) + referenceMulCLM f m k 2) ∘L ι]

/-- The coordinates of `d₀ G`: `-∂₁ G`, `-∂₂ G`, `-(G y₃ + q_m G)` and `G y₂ + p_m G`; `hk` is any
proof that `H^k(ℂ)` is an algebra. -/
theorem gaugeDirectionCoord_apply (hk : (finrank ℝ ℂ : ℝ) < 2 * (k : ℝ))
    (y : Fin 4 → H^{(k : ℝ)}(ℂ)) (G : H^{(k : ℝ) + 1}(ℂ)) :
    gaugeDirectionCoord f m y G =
      ![-lineDerivCLM ENNReal.one_lt_two ENNReal.ofNat_ne_top 1 G,
        -lineDerivCLM ENNReal.one_lt_two ENNReal.ofNat_ne_top I G,
        -(mulCLM hk (inclusion (lt_add_one (k : ℝ)).le G) (y 3) +
          referenceMulCLM f m k 3 (inclusion (lt_add_one (k : ℝ)).le G)),
        mulCLM hk (inclusion (lt_add_one (k : ℝ)).le G) (y 2) +
          referenceMulCLM f m k 2 (inclusion (lt_add_one (k : ℝ)).le G)] := by
  funext j
  fin_cases j <;> rfl

omit [Fact (1 < k)] in
/-- The connection coordinates `y_a - (∂_v J + R ∂_v J - J ∂_v R)` of `smulCoord`, along
`F ↦ (R F, J F)`, at a point where `R` and `J` vanish and `R` has derivative zero: the products
have derivative zero there, so the derivative is `-∂_v` composed with that of `J`. -/
private theorem hasFDerivAt_connectionCoord {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hk : (finrank ℝ ℂ : ℝ) < 2 * (k : ℝ)) {R J : E → H^{(k : ℝ) + 1}(ℂ)}
    {J' : E →L[ℝ] H^{(k : ℝ) + 1}(ℂ)} {e : E}
    (hR : HasFDerivAt R (0 : E →L[ℝ] H^{(k : ℝ) + 1}(ℂ)) e) (hJ : HasFDerivAt J J' e)
    (hR₀ : R e = 0) (hJ₀ : J e = 0) (y : Fin 4 → H^{(k : ℝ)}(ℂ)) (a : Fin 4) (v : ℂ) :
    HasFDerivAt (fun F ↦ y a - (lineDerivCLM ENNReal.one_lt_two ENNReal.ofNat_ne_top v (J F) +
        mulCLM hk (inclusion (lt_add_one (k : ℝ)).le (R F))
          (lineDerivCLM ENNReal.one_lt_two ENNReal.ofNat_ne_top v (J F)) -
        mulCLM hk (inclusion (lt_add_one (k : ℝ)).le (J F))
          (lineDerivCLM ENNReal.one_lt_two ENNReal.ofNat_ne_top v (R F))))
      (-((lineDerivCLM ENNReal.one_lt_two ENNReal.ofNat_ne_top v).restrictScalars ℝ ∘L J')) e := by
  set ι : H^{(k : ℝ) + 1}(ℂ) →L[ℂ] H^{(k : ℝ)}(ℂ) := inclusion (lt_add_one _).le
  set D : H^{(k : ℝ) + 1}(ℂ) →L[ℂ] H^{(k : ℝ)}(ℂ) :=
    lineDerivCLM ENNReal.one_lt_two ENNReal.ofNat_ne_top v
  set B := (mulCLM hk).bilinearRestrictScalars ℝ
  have hDJ : HasFDerivAt (fun F ↦ D (J F)) (D.restrictScalars ℝ ∘L J') e :=
    (D.restrictScalars ℝ).hasFDerivAt.comp e hJ
  refine ((hasFDerivAt_const (y a) e).sub ((hDJ.add (B.hasFDerivAt_of_bilinear
    ((ι.restrictScalars ℝ).hasFDerivAt.comp e hR) hDJ)).sub (B.hasFDerivAt_of_bilinear
    ((ι.restrictScalars ℝ).hasFDerivAt.comp e hJ)
    ((D.restrictScalars ℝ).hasFDerivAt.comp e hR)))).congr_fderiv ?_
  ext G : 1
  simp [hR₀, hJ₀]

/-- The derivative of `F ↦ smulCoord (R F) (J F) y` at a point where `R` and `J` vanish and `R` has
derivative zero is `d₀` composed with the derivative of `J`: the terms of `smulCoord` that are
bilinear in `(R, J)` do not contribute. -/
private theorem hasFDerivAt_smulCoord_comp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {R J : E → H^{(k : ℝ) + 1}(ℂ)} {J' : E →L[ℝ] H^{(k : ℝ) + 1}(ℂ)} {e : E}
    (hR : HasFDerivAt R (0 : E →L[ℝ] H^{(k : ℝ) + 1}(ℂ)) e) (hJ : HasFDerivAt J J' e)
    (hR₀ : R e = 0) (hJ₀ : J e = 0) (y : Fin 4 → H^{(k : ℝ)}(ℂ)) :
    HasFDerivAt (fun F ↦ smulCoord f m (R F) (J F) y)
      ((gaugeDirectionCoord f m y).restrictScalars ℝ ∘L J') e := by
  have hk := finrank_lt (k := k)
  set ι : H^{(k : ℝ) + 1}(ℂ) →L[ℂ] H^{(k : ℝ)}(ℂ) := inclusion (lt_add_one _).le
  set B := (mulCLM hk).bilinearRestrictScalars ℝ
  have hιR : HasFDerivAt (fun F ↦ ι (R F)) (ι.restrictScalars ℝ ∘L 0) e :=
    (ι.restrictScalars ℝ).hasFDerivAt.comp e hR
  have hιJ : HasFDerivAt (fun F ↦ ι (J F)) (ι.restrictScalars ℝ ∘L J') e :=
    (ι.restrictScalars ℝ).hasFDerivAt.comp e hJ
  have href (a : Fin 4) {T : E → H^{(k : ℝ)}(ℂ)} {T' : E →L[ℝ] H^{(k : ℝ)}(ℂ)}
      (hT : HasFDerivAt T T' e) :
      HasFDerivAt (fun F ↦ referenceMulCLM f m k a (T F))
        ((referenceMulCLM f m k a).restrictScalars ℝ ∘L T') e :=
    ((referenceMulCLM f m k a).restrictScalars ℝ).hasFDerivAt.comp e hT
  rw [hasFDerivAt_pi']
  intro j
  fin_cases j
  · simp only [Fin.zero_eta, smulCoord_zero hk]
    refine (hasFDerivAt_connectionCoord hk hR hJ hR₀ hJ₀ y 0 1).congr_fderiv ?_
    ext G : 1
    simp [gaugeDirectionCoord_apply hk]
  · simp only [Fin.mk_one, smulCoord_one hk]
    refine (hasFDerivAt_connectionCoord hk hR hJ hR₀ hJ₀ y 1 I).congr_fderiv ?_
    ext G : 1
    simp [gaugeDirectionCoord_apply hk]
  · have := (((((hasFDerivAt_const (y 2) e).add
      (B.hasFDerivAt_of_bilinear hιR (hasFDerivAt_const (y 2) e))).sub
      (B.hasFDerivAt_of_bilinear hιJ (hasFDerivAt_const (y 3) e))).add (href 2 hιR)).sub
      (href 3 hιJ))
    simp only [Fin.reduceFinMk, smulCoord_two hk]
    refine this.congr_fderiv ?_
    ext G : 1
    simp [B, hR₀, hJ₀, gaugeDirectionCoord_apply hk, ι]
    abel
  · have := (((((hasFDerivAt_const (y 3) e).add
      (B.hasFDerivAt_of_bilinear hιJ (hasFDerivAt_const (y 2) e))).add
      (B.hasFDerivAt_of_bilinear hιR (hasFDerivAt_const (y 3) e))).add (href 2 hιJ)).add
      (href 3 hιR))
    simp only [Fin.reduceFinMk, smulCoord_three hk]
    refine this.congr_fderiv ?_
    ext G : 1
    simp [B, hR₀, hJ₀, gaugeDirectionCoord_apply hk, ι]

/-- **The differential of the gauge action at the identity is `d₀`.** In the exponential chart
`F ↦ exp (i F)` at the identity of `G_(k+1)`, the coordinates of the transformed field have
derivative `G ↦ gaugeDirectionCoord y G` at `F = 0`, for any coordinates `y`. -/
theorem hasFDerivAt_smulCoord_expGauge_zero (y : Fin 4 → H^{(k : ℝ)}(ℂ)) :
    HasFDerivAt (fun F : realSubmodule ℂ (zero_le_one.trans hs.le) ↦
        smulCoord f m (reSubOne (expGauge hs F)) (imPart (expGauge hs F)) y)
      ((gaugeDirectionCoord f m y).restrictScalars ℝ ∘L
        (realSubmodule ℂ (zero_le_one.trans hs.le)).subtypeL) 0 :=
  hasFDerivAt_smulCoord_comp hasFDerivAt_reSubOne_expGauge_zero hasFDerivAt_imPart_expGauge_zero
    (by rw [AddChar.map_zero_eq_one, reSubOne_one]) (by rw [AddChar.map_zero_eq_one, imPart_one]) y

/-- **The joint differential of the gauge action at the identity.** In exponential coordinates, the
map `(F, y) ↦ smulCoord (Re (exp (i F)) - 1) (Im (exp (i F))) y`, which sends a real phase `F` and
the coordinates `y` of `x - x_m` to those of `exp (i F) · x - x_m`, has derivative
`(G, η) ↦ d₀ G + η` at `(0, y)`, where `d₀ = gaugeDirectionCoord f m y` is the infinitesimal gauge
action at `x`. -/
theorem hasFDerivAt_smulCoord_expGauge_prod_zero (y : Fin 4 → H^{(k : ℝ)}(ℂ)) :
    HasFDerivAt (fun p : realSubmodule ℂ (zero_le_one.trans hs.le) × (Fin 4 → H^{(k : ℝ)}(ℂ)) ↦
        smulCoord f m (reSubOne (expGauge hs p.1)) (imPart (expGauge hs p.1)) p.2)
      ((gaugeDirectionCoord f m y).restrictScalars ℝ ∘L
          (realSubmodule ℂ (zero_le_one.trans hs.le)).subtypeL ∘L .fst ℝ _ _ + .snd ℝ _ _)
      (0, y) := by
  have hk := finrank_lt (k := k)
  have hR := (hasFDerivAt_reSubOne_expGauge_zero (hs := hs)).comp (f := Prod.fst)
    ((0 : realSubmodule ℂ (zero_le_one.trans hs.le)), y) (hasFDerivAt_fst (𝕜 := ℝ))
  have hJ := (hasFDerivAt_imPart_expGauge_zero (hs := hs)).comp (f := Prod.fst)
    ((0 : realSubmodule ℂ (zero_le_one.trans hs.le)), y) (hasFDerivAt_fst (𝕜 := ℝ))
  have hy (j : Fin 4) := (hasFDerivAt_apply (𝕜 := ℝ) j y).comp (f := Prod.snd)
    ((0 : realSubmodule ℂ (zero_le_one.trans hs.le)), y) hasFDerivAt_snd
  have hD (v : ℂ) := ((lineDerivCLM (E := ℂ) (s := (k : ℝ)) ENNReal.one_lt_two
    ENNReal.ofNat_ne_top v).restrictScalars ℝ).hasFDerivAt.comp _ hJ
  have hDR (v : ℂ) := ((lineDerivCLM (E := ℂ) (s := (k : ℝ)) ENNReal.one_lt_two
    ENNReal.ofNat_ne_top v).restrictScalars ℝ).hasFDerivAt.comp _ hR
  have hιR := ((inclusion (E := ℂ) (lt_add_one (k : ℝ)).le).restrictScalars ℝ).hasFDerivAt.comp _ hR
  have hιJ := ((inclusion (E := ℂ) (lt_add_one (k : ℝ)).le).restrictScalars ℝ).hasFDerivAt.comp _ hJ
  have hrefR (a : Fin 4) := ((referenceMulCLM f m k a).restrictScalars ℝ).hasFDerivAt.comp _ hιR
  have hrefJ (a : Fin 4) := ((referenceMulCLM f m k a).restrictScalars ℝ).hasFDerivAt.comp _ hιJ
  -- The product of `H^k(ℂ)`, as a real bilinear map.
  set M := (mulCLM hk).bilinearRestrictScalars ℝ with hM
  rw [hasFDerivAt_pi']
  intro j
  -- Assemble the derivative of each coordinate from the pieces above.
  fin_cases j <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, smulCoord_zero hk,
      smulCoord_one hk, smulCoord_two hk, smulCoord_three hk] <;>
    [refine ((hy 0).sub (((hD 1).add (M.hasFDerivAt_of_bilinear hιR (hD 1))).sub
      (M.hasFDerivAt_of_bilinear hιJ (hDR 1)))).congr_fderiv ?_;
    refine ((hy 1).sub (((hD I).add (M.hasFDerivAt_of_bilinear hιR (hD I))).sub
      (M.hasFDerivAt_of_bilinear hιJ (hDR I)))).congr_fderiv ?_;
    refine (((((hy 2).add (M.hasFDerivAt_of_bilinear hιR (hy 2))).sub
      (M.hasFDerivAt_of_bilinear hιJ (hy 3))).add (hrefR 2)).sub (hrefJ 3)).congr_fderiv ?_;
    refine (((((hy 3).add (M.hasFDerivAt_of_bilinear hιJ (hy 2))).add
      (M.hasFDerivAt_of_bilinear hιR (hy 3))).add (hrefJ 2)).add (hrefR 3)).congr_fderiv ?_]
  -- It remains to identify each assembled derivative with the claimed one.
  all_goals
    refine ContinuousLinearMap.ext fun p ↦ ?_
    simp only [Fin.isValue, hM, ContinuousLinearMap.coe_restrictScalars', Function.comp_apply,
      AddChar.map_zero_eq_one, reSubOne_one, imPart_one, map_zero, zero_apply, add_zero, zero_add,
      sub_zero, sub_apply, add_apply, neg_add_rev, ContinuousLinearMap.zero_comp,
      ContinuousLinearMap.comp_zero, ContinuousLinearMap.comp_add, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', ContinuousLinearMap.proj_apply,
      ContinuousLinearMap.precompL_apply, ContinuousLinearMap.bilinearRestrictScalars_apply_apply,
      Submodule.coe_subtypeL, Submodule.subtype_apply, gaugeDirectionCoord_apply hk,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    abel

/-- **The differential of an orbit map.** For a continuous field `x` of `A_m^k`, the derivative of
`F ↦ exp (i F) · x` at `F₀`, in the coordinates of `A_m^k`, is the infinitesimal gauge action at
the field `exp (i F₀) · x`. -/
theorem hasFDerivAt_subRef_expGauge_smul (x : SobolevFieldSpace f m k)
    (F₀ : realSubmodule ℂ (zero_le_one.trans hs.le)) :
    HasFDerivAt (fun F ↦ subRef (expGauge hs F • x))
      ((gaugeDirectionCoord f m (subRef (expGauge hs F₀ • x))).restrictScalars ℝ ∘L
        (realSubmodule ℂ (zero_le_one.trans hs.le)).subtypeL) F₀ := by
  have h := hasFDerivAt_smulCoord_expGauge_zero (f := f) (m := m) (hs := hs)
    (subRef (expGauge hs F₀ • x))
  rw [← sub_self F₀] at h
  refine (h.comp (f := fun F ↦ F - F₀) F₀ (hasFDerivAt_sub_const F₀)).congr_of_eventuallyEq
    (Eventually.of_forall fun F ↦ ?_) |>.congr_fderiv ?_
  · rw [Function.comp_apply, ← subRef_smul, smul_smul, ← AddChar.map_add_eq_mul, sub_add_cancel]
  · ext G : 1
    simp

/-- **`d₀` computes the classical infinitesimal gauge action.** For a continuous field `x` of
`A_m^k` and a real phase `G ∈ H^(k+1)(ℂ)`, the `L²` function of the coordinate `j` of
`gaugeDirectionCoord (subRef x) G` is the coordinate `j` of `gaugeDirection x g`, where `g` is the
continuous representative of `G`, a `C¹` function. -/
theorem coeFn_inclusionLp_gaugeDirectionCoord_ae_eq (x : SobolevFieldSpace f m k)
    {h : (0 : ℝ) ≤ k + 1} (G : realSubmodule ℂ h) (j : Fin 4) :
    ⇑(inclusionLp k.cast_nonneg (gaugeDirectionCoord f m (subRef x) G j)) =ᵐ[volume]
      fun z ↦ ((gaugeDirection x (continuousRep G) z j : ℝ) : ℂ) := by
  have hk := finrank_lt (k := k)
  have hs' : (finrank ℝ ℂ : ℝ) < 2 * ((k : ℝ) + 1) := by
    have : (0 : ℝ) ≤ 2 := by norm_num
    linarith
  have hG := coeFn_inclusionLp_ae_eq_continuousRep hs' G
  have hG' : ⇑(inclusionLp k.cast_nonneg
      (inclusion (lt_add_one (k : ℝ)).le (G : H^{(k : ℝ) + 1}(ℂ)))) =ᵐ[volume]
      fun z ↦ (continuousRep G z : ℂ) := by
    rw [inclusionLp_inclusion]
    exact hG
  have hC1 : ContDiff ℝ 1 (continuousRep G) := by
    refine contDiff_continuousRep ?_ G
    push_cast
    linarith
  have hd (v : ℂ) := coeFn_inclusionLp_lineDerivCLM_ae_eq ENNReal.one_lt_two
    ENNReal.ofNat_ne_top k.cast_nonneg hC1 hG v
  have hy (a : Fin 4) := coeFn_toLp_inclusion_subRef k.cast_nonneg x a
  have hM (a b : H^{(k : ℝ)}(ℂ)) := coeFn_toLp_inclusion_mulCLM hk k.cast_nonneg a b
  simp only [toLp_inclusion] at hy hM
  have href (a : Fin 4) := coeFn_inclusionLp_referenceMulCLM_ae_eq (f := f) (m := m) a
    (inclusion (lt_add_one (k : ℝ)).le (G : H^{(k : ℝ) + 1}(ℂ)))
  rw [gaugeDirectionCoord_apply hk]
  fin_cases j
  · simp only [Fin.zero_eta, Matrix.cons_val_zero, map_neg]
    filter_upwards [Lp.coeFn_neg (inclusionLp k.cast_nonneg
      (lineDerivCLM ENNReal.one_lt_two ENNReal.ofNat_ne_top 1 (G : H^{(k : ℝ) + 1}(ℂ)))), hd 1]
      with z h₁ h₂
    rw [h₁, Pi.neg_apply, h₂, gaugeDirection_apply_zero, Complex.ofReal_neg]
  · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero, map_neg]
    filter_upwards [Lp.coeFn_neg (inclusionLp k.cast_nonneg
      (lineDerivCLM ENNReal.one_lt_two ENNReal.ofNat_ne_top I (G : H^{(k : ℝ) + 1}(ℂ)))), hd I]
      with z h₁ h₂
    rw [h₁, Pi.neg_apply, h₂, gaugeDirection_apply_one, Complex.ofReal_neg]
  · simp only [Fin.reduceFinMk, Matrix.cons_val, map_neg]
    filter_upwards [Lp.coeFn_neg (inclusionLp k.cast_nonneg
      (mulCLM hk (inclusion (lt_add_one (k : ℝ)).le (G : H^{(k : ℝ) + 1}(ℂ))) (subRef x 3) +
        referenceMulCLM f m k 3 (inclusion (lt_add_one (k : ℝ)).le (G : H^{(k : ℝ) + 1}(ℂ))))),
      coeFn_inclusionLp_add_ae_eq k.cast_nonneg (hM _ (subRef x 3)) (href 3), hG', hy 3]
      with z h₁ h₂ h₃ h₄
    rw [h₁, Pi.neg_apply, h₂, h₃, h₄, gaugeDirection_apply_two]
    push_cast
    ring
  · simp only [Fin.reduceFinMk, Matrix.cons_val]
    filter_upwards [coeFn_inclusionLp_add_ae_eq k.cast_nonneg (hM _ (subRef x 2)) (href 2), hG',
      hy 2] with z h₁ h₂ h₃
    rw [h₁, h₂, h₃, gaugeDirection_apply_three]
    push_cast
    ring

/-- **The norm of the section is uniformly continuous along gauge orbits.** For `k ≥ 2` and every
`δ > 0` there is `ε > 0` such that, for all continuous fields `x` and `y` of `A_m^k` and every
gauge `g ∈ G_(k+1)`, if the real coordinates of `x` are within `ε` of those of `g · y`, then the
norms of the sections of `x` and `y` differ by at most `δ` everywhere. -/
theorem exists_pos_forall_abs_norm_sectionValue_sub_le {δ : ℝ} (hδ : 0 < δ) :
    ∃ ε > 0, ∀ (x y : SobolevFieldSpace f m k) (g : SobolevTopologicalGaugeGroup hs),
      ‖x.realSubRef (Nat.cast_nonneg k) - (g • y).realSubRef (Nat.cast_nonneg k)‖ < ε →
        ∀ z, |‖sectionValue x z‖ - ‖sectionValue y z‖| ≤ δ := by
  obtain ⟨C, hC⟩ := exists_forall_norm_sectionValue_sub_le_mul (f := f) (m := m)
    (h := Nat.cast_nonneg k) (by exact_mod_cast (Fact.out : 1 < k))
  refine ⟨δ / (|C| + 1), by positivity, fun x y g hxy z ↦ ?_⟩
  rw [← norm_sectionValue_smul g y z]
  refine (abs_norm_sub_norm_le _ _).trans ((hC x (g • y) z).trans ?_)
  calc C * ‖x.realSubRef _ - (g • y).realSubRef _‖
      ≤ (|C| + 1) * ‖x.realSubRef _ - (g • y).realSubRef _‖ := by
        gcongr; linarith [le_abs_self C]
    _ ≤ (|C| + 1) * (δ / (|C| + 1)) := mul_le_mul_of_nonneg_left hxy.le (by positivity)
    _ = δ := by field_simp

end SobolevFieldSpace

end TauCeti.Vortex
