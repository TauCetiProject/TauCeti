/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Cylinder.Periodization
public import TauCeti.Analysis.Sobolev.Cylinder.W1p
public import TauCeti.Analysis.Sobolev.WeakDeriv.Basic
import Mathlib.MeasureTheory.SpecificCodomains.Pi
import TauCeti.Analysis.Calculus.FDeriv.Periodization

/-!
# Weak derivatives of the elements of `W^{1,p}` of the cylinder

The Sobolev space `W^{1,p}(ℝ × S¹, V)` of the cylinder (`TauCeti.CylinderSobolev.W1p`) is the
closure of the jets `(ξ, ∂s ξ, ∂t ξ)` of test sections in `Lᵖ(ℝ × [0, 1], V × V × V)`. An element
is therefore an `Lᵖ` jet `(ξ, ξ_s, ξ_t)` on the strip, and for `2 < p < ∞` its value has a
continuous representative of period one in `t`, its image under the Sobolev embedding
(`TauCeti.CylinderSobolev.continuousValue`). This file shows that the two other components of the
jet are the weak derivatives of that representative on the whole plane, in the sense of
`TauCeti.HasWeakFDerivOn`, the notion used by interior elliptic regularity.

* **The weak derivative identity on the strip.** For a scalar test section `ψ` and a test section
  `ξ`, the integrals over the strip of `ψ ∂ₑξ + (∂ₑψ) ξ` in the two coordinate directions `e`
  vanish (`TauCeti.StripSobolev.integral_smul_fderiv_add_fderiv_smul_eq_zero`): in the direction
  `s` because `ξ` vanishes for `|s|` large, in the direction `t` by periodicity. Since `ψ` lies in
  every `Lᵖ`, the identity `∫ ψ ξ_e + ∫ (∂ₑψ) ξ = 0` passes from the jets of test sections to
  their closure `W^{1,p}` (`TauCeti.StripSobolev.integral_smul_add_eq_zero_of_mem_jetClosure`).
* **Weak derivatives on the plane.** Let `2 < p < ∞`, let `x = (ξ, ξ_s, ξ_t) ∈ W^{1,p}`, and let
  `g_s` and `g_t` be strongly measurable functions of period one in `t` agreeing with `ξ_s` and
  `ξ_t` on the strip, as given by
  `TauCeti.CylinderSobolev.exists_stronglyMeasurable_periodic_ae_eq`.
  The integral over the plane of a compactly supported function times a function of period one in
  `t` unfolds onto the strip, where it becomes an integral against the periodization of the
  compactly supported function, a scalar test section. Hence `g_s` and `g_t` are the weak partial
  derivatives of the continuous representative of `ξ` on `ℝ × ℝ`
  (`TauCeti.CylinderSobolev.hasWeakLineDerivOn_continuousValue_fst`,
  `TauCeti.CylinderSobolev.hasWeakLineDerivOn_continuousValue_snd`), and
  `z ↦ ds ⊗ g_s z + dt ⊗ g_t z` is its weak derivative
  (`TauCeti.CylinderSobolev.hasWeakFDerivOn_continuousValue`). In particular the continuous
  representative has a weak derivative on the plane which is locally `Lᵖ` and of period one in `t`
  (`TauCeti.CylinderSobolev.exists_hasWeakFDerivOn_continuousValue`).

The nonlinear Floer section of a map of the cylinder is formed on increments in `W^{1,p}`, `p > 2`;
this file is the passage from such increments to the weak solutions of Cauchy–Riemann equations on
open subsets of the plane, to which interior elliptic bootstrapping applies.

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., Appendix B.1,
  on weak derivatives and Sobolev spaces on surfaces.
-/

public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace TauCeti.CylinderSobolev

open StripSobolev (jet jet_apply stripMeasure integral_smul_fderiv_add_fderiv_smul_eq_zero
  integral_smul_add_eq_zero_of_mem_jetClosure)

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- **The weak derivative identity on the strip.** For `x = (ξ, ξ_s, ξ_t)` in `W1p V p`, a scalar
test section `ψ` and a coordinate direction `e`, with `P` the component of the jet recording the
derivative in the direction `e`, `∫ ψ P(x) + ∫ (∂ₑψ) ξ = 0` over the strip: on test sections this
is integration by parts, the boundary terms in `t` cancelling by periodicity. -/
private lemma integral_smul_add_eq_zero_of_mem_W1p [CompleteSpace V] {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {x : Lp (V × V × V) p stripMeasure} (hx : x ∈ W1p V p) {ψ : ℝ × ℝ → ℝ}
    (hψ : ψ ∈ testSection ℝ) {e : ℝ × ℝ} (he : e = (1, 0) ∨ e = (0, 1))
    {P : V × V × V →L[ℝ] V} (hP : ∀ (ξ : ℝ × ℝ → V) z, P (jet ξ z) = fderiv ℝ ξ z e) :
    ∫ z, ψ z • P (x z) ∂stripMeasure + ∫ z, fderiv ℝ ψ z e • (x z).1 ∂stripMeasure = 0 := by
  obtain ⟨hψ2, hψper, -⟩ := mem_testSection_iff.1 hψ
  refine integral_smul_add_eq_zero_of_mem_jetClosure
    (by simpa only [jet_apply] using (memLp_jet hψ _).fst)
    ((memLp_jet hψ _).fderiv_apply_of_jet e) hP (fun ξ hξ ↦ ?_) hx
  obtain ⟨hξ2, hξper, R, hR⟩ := mem_testSection_iff.1 hξ
  exact integral_smul_fderiv_add_fderiv_smul_eq_zero (hψ2.of_le one_le_two) (hξ2.of_le one_le_two)
    hR (fun s ↦ by simpa using congrArg₂ (· • ·) (hψper s 0) (hξper s 0)) he

/-! ### Weak derivatives on the plane -/

section Plane

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- On the plane, the derivative component `P x` of `x ∈ W^{1,p}`, extended with period one in
`t`, is the weak derivative in the coordinate direction `e` of the continuous representative. -/
private lemma hasWeakLineDerivOn_continuousValue [CompleteSpace V] (hp : 2 < p) (hpt : p ≠ ∞)
    (x : W1p V p) {e : ℝ × ℝ} (he : e = (1, 0) ∨ e = (0, 1)) {P : V × V × V →L[ℝ] V}
    (hP : ∀ (ξ : ℝ × ℝ → V) z, P (jet ξ z) = fderiv ℝ ξ z e) {g : ℝ × ℝ → V}
    (hg : StronglyMeasurable g) (hgper : ∀ s t, g (s, t + 1) = g (s, t))
    (hgx : g =ᵐ[stripMeasure] fun z ↦ P ((x : Lp (V × V × V) p stripMeasure) z)) :
    HasWeakLineDerivOn volume ⊤ (continuousValue p x) g e := by
  have hp1 : 1 ≤ p := Fact.out
  lift p to ℝ≥0 using hpt
  have hgloc : MemLpLoc p univ g := memLpLoc_univ_of_periodic hg hgper (by exact_mod_cast hp1)
    ((P.comp_memLp' (Lp.memLp _)).ae_eq hgx.symm)
  have hgli : LocallyIntegrable g :=
    locallyIntegrableOn_univ.1 (hgloc.locallyIntegrableOn hp1 isOpen_univ.isLocallyClosed)
  have hu := (continuousValue p x).continuous
  refine hasWeakLineDerivOn_iff_testFunction.2 ⟨inferInstance,
    hu.locallyIntegrable.locallyIntegrableOn _, hgli.locallyIntegrableOn _, fun φ ↦ ?_⟩
  have hφ := φ.contDiff (n := ⊤)
  have hφc : HasCompactSupport (φ : ℝ × ℝ → ℝ) := φ.hasCompactSupport
  have hφ1 : ContDiff ℝ 1 (φ : ℝ × ℝ → ℝ) := hφ.of_le (by simp)
  have hφe : Continuous fun z ↦ fderiv ℝ (φ : ℝ × ℝ → ℝ) z e :=
    (hφ1.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hl : ∀ z, lineDeriv ℝ (φ : ℝ × ℝ → ℝ) z e = fderiv ℝ φ z e := fun z ↦
    ((hφ1.differentiable one_ne_zero) z).lineDeriv_eq_fderiv
  -- The periodization `ψ` of `φ` is a scalar test section of the cylinder.
  set ψ : ℝ × ℝ → ℝ := fun z ↦ ∑' n : ℤ, (φ : ℝ × ℝ → ℝ) (z.1, z.2 + n)
  have hψ : ψ ∈ testSection ℝ := tsum_add_intCast_mem_testSection (hφ.of_le (by simp)) hφc
  have hψe (z : ℝ × ℝ) :
      ∑' n : ℤ, fderiv ℝ (φ : ℝ × ℝ → ℝ) (z.1, z.2 + n) e = fderiv ℝ ψ z e :=
    (fderiv_tsum_add_intCast_apply (hφ1.differentiable one_ne_zero) hφc z e).symm
  -- On the strip, the continuous representative is the value of `x`.
  have hval : (continuousValue p x : ℝ × ℝ → V) =ᵐ[stripMeasure]
      fun z ↦ ((x : Lp (V × V × V) p stripMeasure) z).1 :=
    (valueL_ae_eq_continuousValue hp ENNReal.coe_ne_top x).symm.trans (coeFn_valueL x)
  simp_rw [hl]
  rw [integral_smul_eq_integral_tsum_smul hφe (hφc.fderiv_apply (𝕜 := ℝ) e)
      hu.locallyIntegrable (continuousValue_add_one hp ENNReal.coe_ne_top x),
    integral_smul_eq_integral_tsum_smul φ.continuous hφc hgli hgper]
  simp_rw [hψe]
  have e₁ : ∫ z, fderiv ℝ ψ z e • continuousValue p x z ∂stripMeasure =
      ∫ z, fderiv ℝ ψ z e • ((x : Lp (V × V × V) p stripMeasure) z).1 ∂stripMeasure :=
    integral_congr_ae (hval.mono fun z hz ↦ by simp only [hz])
  have e₂ : ∫ z, (∑' n : ℤ, (φ : ℝ × ℝ → ℝ) (z.1, z.2 + n)) • g z ∂stripMeasure =
      ∫ z, ψ z • P ((x : Lp (V × V × V) p stripMeasure) z) ∂stripMeasure :=
    integral_congr_ae (hgx.mono fun z hz ↦ by simp only [hz, ψ])
  rw [e₁, e₂]
  exact eq_neg_of_add_eq_zero_left
    ((add_comm _ _).trans (integral_smul_add_eq_zero_of_mem_W1p x.property hψ he hP))

variable [CompleteSpace V]

/-- **The weak `s`-derivative on the plane.** For `2 < p < ∞` and `x = (ξ, ξ_s, ξ_t) ∈ W^{1,p}`, a
strongly measurable function `g` of period one in `t` agreeing with `ξ_s` on the strip is the weak
derivative in the direction `s` of the continuous representative of `ξ`, on the whole plane. -/
theorem hasWeakLineDerivOn_continuousValue_fst (hp : 2 < p) (hpt : p ≠ ∞) (x : W1p V p)
    {g : ℝ × ℝ → V} (hg : StronglyMeasurable g) (hgper : ∀ s t, g (s, t + 1) = g (s, t))
    (hgx : g =ᵐ[stripMeasure] fun z ↦ ((x : Lp (V × V × V) p stripMeasure) z).2.1) :
    HasWeakLineDerivOn volume ⊤ (continuousValue p x) g (1, 0) :=
  hasWeakLineDerivOn_continuousValue hp hpt x (Or.inl rfl)
    (P := (ContinuousLinearMap.fst ℝ V V).comp (ContinuousLinearMap.snd ℝ V (V × V)))
    (fun _ _ ↦ by simp [jet_apply]) hg hgper hgx

/-- **The weak `t`-derivative on the plane.** For `2 < p < ∞` and `x = (ξ, ξ_s, ξ_t) ∈ W^{1,p}`, a
strongly measurable function `g` of period one in `t` agreeing with `ξ_t` on the strip is the weak
derivative in the direction `t` of the continuous representative of `ξ`, on the whole plane. -/
theorem hasWeakLineDerivOn_continuousValue_snd (hp : 2 < p) (hpt : p ≠ ∞) (x : W1p V p)
    {g : ℝ × ℝ → V} (hg : StronglyMeasurable g) (hgper : ∀ s t, g (s, t + 1) = g (s, t))
    (hgx : g =ᵐ[stripMeasure] fun z ↦ ((x : Lp (V × V × V) p stripMeasure) z).2.2) :
    HasWeakLineDerivOn volume ⊤ (continuousValue p x) g (0, 1) :=
  hasWeakLineDerivOn_continuousValue hp hpt x (Or.inr rfl)
    (P := (ContinuousLinearMap.snd ℝ V V).comp (ContinuousLinearMap.snd ℝ V (V × V)))
    (fun _ _ ↦ by simp [jet_apply]) hg hgper hgx

/-- **The weak derivative on the plane.** For `2 < p < ∞` and `x = (ξ, ξ_s, ξ_t) ∈ W^{1,p}`, let
`g_s` and `g_t` be strongly measurable functions of period one in `t` agreeing with `ξ_s` and
`ξ_t` on the strip. Then `z ↦ ds ⊗ g_s z + dt ⊗ g_t z` is the weak derivative of the continuous
representative of `ξ` on the whole plane. For a choice of `g_s` and `g_t` for which this weak
derivative is also locally `Lᵖ`, see
`TauCeti.CylinderSobolev.exists_hasWeakFDerivOn_continuousValue`. -/
theorem hasWeakFDerivOn_continuousValue (hp : 2 < p) (hpt : p ≠ ∞) (x : W1p V p)
    {gs gt : ℝ × ℝ → V} (hgs : StronglyMeasurable gs) (hgt : StronglyMeasurable gt)
    (hgsper : ∀ s t, gs (s, t + 1) = gs (s, t)) (hgtper : ∀ s t, gt (s, t + 1) = gt (s, t))
    (hgsx : gs =ᵐ[stripMeasure] fun z ↦ ((x : Lp (V × V × V) p stripMeasure) z).2.1)
    (hgtx : gt =ᵐ[stripMeasure] fun z ↦ ((x : Lp (V × V × V) p stripMeasure) z).2.2) :
    HasWeakFDerivOn volume ⊤ (continuousValue p x) (fun z ↦
      (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight (gs z) +
        (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (gt z)) := by
  refine (Module.Basis.finTwoProd ℝ).hasWeakFDerivOn_of_forall
    ((continuousValue p x).continuous.locallyIntegrable.locallyIntegrableOn _) fun i ↦ ?_
  fin_cases i
  · simpa using hasWeakLineDerivOn_continuousValue_fst hp hpt x hgs hgsper hgsx
  · simpa using hasWeakLineDerivOn_continuousValue_snd hp hpt x hgt hgtper hgtx

/-- **`W^{1,p}` of the cylinder is weakly differentiable on the plane.** For `2 < p < ∞`, the
continuous representative of the value of `x = (ξ, ξ_s, ξ_t) ∈ W^{1,p}(ℝ × S¹, V)` has a weak
derivative `D` on the whole plane which is locally `Lᵖ`, of period one in `t`, and whose partial
derivatives `D z (1, 0)` and `D z (0, 1)` agree with `ξ_s` and `ξ_t` almost everywhere on the
strip. -/
theorem exists_hasWeakFDerivOn_continuousValue (hp : 2 < p) (hpt : p ≠ ∞) (x : W1p V p) :
    ∃ D : ℝ × ℝ → ℝ × ℝ →L[ℝ] V, HasWeakFDerivOn volume ⊤ (continuousValue p x) D ∧
      MemLpLoc p univ D ∧ (∀ s t, D (s, t + 1) = D (s, t)) ∧
      ∀ᵐ z ∂stripMeasure, D z (1, 0) = ((x : Lp (V × V × V) p stripMeasure) z).2.1 ∧
        D z (0, 1) = ((x : Lp (V × V × V) p stripMeasure) z).2.2 := by
  have hp1 : 1 ≤ p := Fact.out
  lift p to ℝ≥0 using hpt
  set y : Lp (V × V × V) p stripMeasure := x.val
  obtain ⟨gs, hgs, hgsper, hgsx⟩ := exists_stronglyMeasurable_periodic_ae_eq
    ((ContinuousLinearMap.fst ℝ V V).comp (ContinuousLinearMap.snd ℝ V (V × V)) |>.compLp y)
  obtain ⟨gt, hgt, hgtper, hgtx⟩ := exists_stronglyMeasurable_periodic_ae_eq
    ((ContinuousLinearMap.snd ℝ V V).comp (ContinuousLinearMap.snd ℝ V (V × V)) |>.compLp y)
  have hgsx' : gs =ᵐ[stripMeasure] fun z ↦ (y z).2.1 :=
    hgsx.trans (ContinuousLinearMap.coeFn_compLp _ y)
  have hgtx' : gt =ᵐ[stripMeasure] fun z ↦ (y z).2.2 :=
    hgtx.trans (ContinuousLinearMap.coeFn_compLp _ y)
  have hloc {g : ℝ × ℝ → V} (hg : StronglyMeasurable g) (hgper : ∀ s t, g (s, t + 1) = g (s, t))
      (f : Lp V p stripMeasure) (hgf : g =ᵐ[stripMeasure] f) : MemLpLoc p univ g :=
    memLpLoc_univ_of_periodic hg hgper (by exact_mod_cast hp1) ((Lp.memLp f).ae_eq hgf.symm)
  refine ⟨_, hasWeakFDerivOn_continuousValue hp ENNReal.coe_ne_top x hgs hgt hgsper hgtper hgsx'
    hgtx', ?_, fun s t ↦ by simp [hgsper, hgtper], ?_⟩
  · refine ((hloc hgs hgsper _ hgsx).clm_comp (ContinuousLinearMap.smulRightL ℝ ℝ ℝ (ℝ × ℝ) V
      (ContinuousLinearMap.fst ℝ ℝ ℝ))).add ((hloc hgt hgtper _ hgtx).clm_comp
      (ContinuousLinearMap.smulRightL ℝ ℝ ℝ (ℝ × ℝ) V (ContinuousLinearMap.snd ℝ ℝ ℝ))) |>.congr ?_
    intro z _
    ext <;> simp
  · filter_upwards [hgsx', hgtx'] with z hs ht
    simp [hs, ht]

end Plane

end TauCeti.CylinderSobolev
