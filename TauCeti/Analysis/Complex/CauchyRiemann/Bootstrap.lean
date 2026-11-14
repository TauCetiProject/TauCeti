/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.CauchyRiemann.RoughCoefficients.Regularity
public import TauCeti.Analysis.Complex.CauchyRiemann.Weak.Comparison
import Mathlib.Analysis.Normed.Module.FiniteDimension
import TauCeti.Analysis.Sobolev.Local.ChainRule.Higher
import TauCeti.Analysis.Sobolev.Local.Morrey.Higher

/-!
# Interior elliptic bootstrapping for the nonlinear Cauchy–Riemann equation

Let `V` be a finite-dimensional real normed space and `Ω ⊆ ℂ` an open set. Given a
domain-dependent almost complex structure `J : ℂ → V → V →L[ℝ] V` and an inhomogeneous term
`η : ℂ → V → V`, consider a continuous `W^{1,p}_loc(Ω)` solution `u : ℂ → V` of

`∂_s u + J(z, u) ∂_t u = η(z, u)`

in the sense of `TauCeti.IsWeakCauchyRiemannOn p Ω J η u`.

For finite `p > 2`, if `J` and `η` are `C^ℓ` on an open neighbourhood of the graph of `u` over `Ω`
and `J(z, u z)² = -1` for every `z ∈ Ω`, then `u ∈ W^{ℓ+1,p}_loc(Ω)`, and consequently `u` is
`C^ℓ` on `Ω` (McDuff–Salamon, Theorem B.4.1 and Remark B.4.3). Because `u` is already continuous
on `Ω` as part of `IsWeakCauchyRiemannOn`, no modification on a null set is needed.

The proof freezes coefficients along the solution: if `u ∈ W^{m,p}_loc(Ω)` with `1 ≤ m ≤ ℓ`, the
higher-order local Sobolev chain rule (`TauCeti.MemWkpLoc.contDiffOn_comp_graph_succ`) places
`z ↦ J(z, u z)` and `z ↦ η(z, u z)` in `W^{m,p}_loc(Ω)`, and linear interior regularity for
Sobolev coefficients (`TauCeti.memWkpLoc_of_ae_linearCR`, with `S = 0`) upgrades `u` to
`W^{m+1,p}_loc(Ω)`.

For finite regularity `ℓ < ∞` the hypothesis `p ≠ ⊤` is sharp: in
`TauCeti.Analysis.Complex.CauchyRiemann.LogLog.Sobolev`, the graph of
`f(z) = z² log log (1 / ‖z‖)` (`TauCeti.isWeakCauchyRiemannOn_graph_logLogExample`) solves the
homogeneous equation for a `C¹` almost complex structure with `p = ∞`, yet fails to belong to
`W^{2,∞}_loc` on any neighbourhood of `0`
(`TauCeti.not_memWkpLoc_two_top_graph_logLogExample`). In the smooth case (`J, η` of class `C^∞`)
the endpoint `p = ∞` is allowed because a `W^{1,∞}_loc` solution is `W^{1,3}_loc` by local
monotonicity in the exponent.

## Main results

* `TauCeti.IsWeakCauchyRiemannOn.memWkpLoc_of_contDiffOn`: local-neighbourhood `C^ℓ` data give
  `MemWkpLoc p Ω (ℓ + 1) u` for `2 < p < ∞`.
* `TauCeti.IsWeakCauchyRiemannOn.contDiffOn_of_le`: under the same hypotheses, `ContDiffOn ℝ ℓ u Ω`.
* `TauCeti.IsWeakCauchyRiemannOn.contDiffOn`: local-neighbourhood `C^∞` data give
  `ContDiffOn ℝ ∞ u Ω` for every `2 < p ≤ ∞`.
* `TauCeti.memWkpLoc_of_isWeakCauchyRiemannOn`,
  `TauCeti.contDiffOn_of_isWeakCauchyRiemannOn`: the global-data planar forms.
* `TauCeti.IsPseudoholomorphicOn.contDiffOn`, `TauCeti.IsPseudoholomorphic.contDiff`: a `C¹`
  map from an open subset of `ℂ` (or all of `ℂ`) into a finite-dimensional real normed space
  carrying a smooth almost complex structure `J` that is `J`-holomorphic is `C^∞`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.4 (Theorem B.4.1 and Remark B.4.3).
-/

public noncomputable section

open Complex MeasureTheory Set TopologicalSpace
open scoped ContDiff ENNReal Manifold NNReal

namespace TauCeti

private theorem inv_add_inv_lt_one_of_two_lt {p : ℝ≥0} (hp : (2 : ℝ≥0∞) < p) :
    (p : ℝ≥0∞)⁻¹ + (p : ℝ≥0∞)⁻¹ < 1 := by
  have hpR : (2 : ℝ) < p := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < p := by linarith
  have hinv : (p : ℝ)⁻¹ < 2⁻¹ := (inv_lt_inv₀ hp0 two_pos).2 hpR
  have hsum : (p : ℝ)⁻¹ + (p : ℝ)⁻¹ < 1 := by linarith
  rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_inv_of_pos hp0,
    ← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_one]
  exact (ENNReal.ofReal_lt_ofReal_iff zero_lt_one).2 hsum

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-! ### Finite-regularity and smooth interior bootstrapping -/

/-- **Interior elliptic bootstrapping with local `C^ℓ` data.** Let `2 < p < ∞`, let `W ⊆ ℂ × V` be
an open neighbourhood of the graph of `u` over an open set `Ω ⊆ ℂ`, and suppose `J` and `η` are
`C^ℓ` on `W` with `J(z, u z)² = -1` for every `z ∈ Ω`. Every solution `u` of
`IsWeakCauchyRiemannOn p Ω J η u` belongs to `MemWkpLoc p Ω (ℓ + 1) u`. At `ℓ = 0` this is
`IsWeakCauchyRiemannOn.memWkpLoc_one`; for `ℓ ≥ 1` each bootstrap step gains one derivative
(McDuff–Salamon, Theorem B.4.1 and Remark B.4.3). -/
theorem IsWeakCauchyRiemannOn.memWkpLoc_of_contDiffOn [FiniteDimensional ℝ V] {p : ENNReal}
    (hp : 2 < p) (hp_top : p ≠ ⊤) {ℓ : ℕ} {Ω : Opens ℂ} {W : Set (ℂ × V)} (hW : IsOpen W)
    {J : ℂ → V → V →L[ℝ] V} {η : ℂ → V → V} {u : ℂ → V}
    (hJ : ContDiffOn ℝ ℓ (Function.uncurry J) W)
    (hJsq : ∀ z ∈ (Ω : Set ℂ), (J z (u z)).comp (J z (u z)) = -ContinuousLinearMap.id ℝ V)
    (hη : ContDiffOn ℝ ℓ (Function.uncurry η) W)
    (hu : IsWeakCauchyRiemannOn p Ω J η u) (huW : ∀ z ∈ (Ω : Set ℂ), (z, u z) ∈ W) :
    MemWkpLoc p Ω (ℓ + 1) u := by
  lift p to ℝ≥0 using hp_top
  have : CompleteSpace V := FiniteDimensional.completeSpace ℝ V
  have hpNN : 2 < p := by exact_mod_cast hp
  have hp1 : (1 : ℝ≥0∞) < p := (by norm_num : (1 : ℝ≥0∞) < 2).trans hp
  have hpp : (p : ℝ≥0∞)⁻¹ + (p : ℝ≥0∞)⁻¹ < 1 := inv_add_inv_lt_one_of_two_lt hp
  obtain ⟨huc, -, D, hD, -, hae⟩ := isWeakCauchyRiemannOn_iff_of_isOpen.1 hu
  have hu1 : MemWkpLoc p Ω 1 u := hu.memWkpLoc_one
  have hJsq_ae : ∀ᵐ z ∂volume.restrict Ω,
      (J z (u z)).comp (J z (u z)) = -ContinuousLinearMap.id ℝ V :=
    (ae_restrict_iff' Ω.isOpen.measurableSet).2 (.of_forall hJsq)
  have hae_lin : ∀ᵐ z ∂volume.restrict Ω,
      D z 1 + J z (u z) (D z I) + (0 : ℂ → V →L[ℝ] V) z (u z) = η z (u z) := by
    simpa using hae
  suffices ∀ d ≤ ℓ, MemWkpLoc p Ω (d + 1) u from this ℓ le_rfl
  intro d hd
  induction d with
  | zero => exact hu1
  | succ d' ih =>
    have hud : MemWkpLoc p Ω (d' + 1) u := ih (Nat.le_of_succ_le hd)
    have hJu : MemWkpLoc p Ω (d' + 1) (fun z => J z (u z)) :=
      hud.contDiffOn_comp_graph_succ hpNN huc hW
        (hJ.of_le (by exact_mod_cast hd)) huW
    have hηu : MemWkpLoc p Ω (d' + 1) (fun z => η z (u z)) :=
      hud.contDiffOn_comp_graph_succ hpNN huc hW
        (hη.of_le (by exact_mod_cast hd)) huW
    exact memWkpLoc_of_ae_linearCR hp ENNReal.coe_ne_top hpp ENNReal.coe_ne_top hp1 le_rfl
      (Nat.succ_pos d') le_rfl le_rfl hJu hJsq_ae memWkpLoc_zero_fun hu1 hD hae_lin hηu

/-- **Classical `C^ℓ` regularity from local `C^ℓ` data.** Under the hypotheses of
`IsWeakCauchyRiemannOn.memWkpLoc_of_contDiffOn`, `u` is `C^ℓ` on `Ω` (with no null-set modification,
since `u` is continuous on `Ω`). -/
theorem IsWeakCauchyRiemannOn.contDiffOn_of_le [FiniteDimensional ℝ V] {p : ENNReal}
    (hp : 2 < p) (hp_top : p ≠ ⊤) {ℓ : ℕ} {Ω : Opens ℂ} {W : Set (ℂ × V)} (hW : IsOpen W)
    {J : ℂ → V → V →L[ℝ] V} {η : ℂ → V → V} {u : ℂ → V}
    (hJ : ContDiffOn ℝ ℓ (Function.uncurry J) W)
    (hJsq : ∀ z ∈ (Ω : Set ℂ), (J z (u z)).comp (J z (u z)) = -ContinuousLinearMap.id ℝ V)
    (hη : ContDiffOn ℝ ℓ (Function.uncurry η) W)
    (hu : IsWeakCauchyRiemannOn p Ω J η u) (huW : ∀ z ∈ (Ω : Set ℂ), (z, u z) ∈ W) :
    ContDiffOn ℝ ℓ u Ω := by
  have husob := hu.memWkpLoc_of_contDiffOn hp hp_top hW hJ hJsq hη huW
  obtain ⟨g, hg, hug⟩ := husob.exists_contDiffOn_ae_eq hp
  exact hg.congr (Measure.eqOn_open_of_ae_eq hug Ω.isOpen hu.continuousOn hg.continuousOn)

/-- **Smooth interior bootstrapping with local `C^∞` data.** For every `2 < p ≤ ∞`, if `J` and `η`
are smooth on an open neighbourhood `W ⊆ ℂ × V` of the graph of `u` over `Ω` and `J(z, u z)² = -1`
for every `z ∈ Ω`, then `u` is smooth on `Ω`. Unlike the finite-regularity theorem, `p = ⊤` is
allowed because a `W^{1,∞}_loc` solution is `W^{1,3}_loc`. -/
theorem IsWeakCauchyRiemannOn.contDiffOn [FiniteDimensional ℝ V] {p : ENNReal} (hp : 2 < p)
    {Ω : Opens ℂ} {W : Set (ℂ × V)} (hW : IsOpen W)
    {J : ℂ → V → V →L[ℝ] V} {η : ℂ → V → V} {u : ℂ → V}
    (hJ : ContDiffOn ℝ ∞ (Function.uncurry J) W)
    (hJsq : ∀ z ∈ (Ω : Set ℂ), (J z (u z)).comp (J z (u z)) = -ContinuousLinearMap.id ℝ V)
    (hη : ContDiffOn ℝ ∞ (Function.uncurry η) W)
    (hu : IsWeakCauchyRiemannOn p Ω J η u) (huW : ∀ z ∈ (Ω : Set ℂ), (z, u z) ∈ W) :
    ContDiffOn ℝ ∞ u Ω := by
  let p₀ : ENNReal := min p 3
  have hp₀ : 2 < p₀ := lt_min hp (by norm_num)
  have hp₀_top : p₀ ≠ ⊤ := ne_top_of_le_ne_top (by norm_num) (min_le_right p 3)
  have hu₀ : IsWeakCauchyRiemannOn p₀ Ω J η u := hu.mono_exponent (min_le_left p 3)
  exact contDiffOn_infty.2 fun ℓ =>
    hu₀.contDiffOn_of_le hp₀ hp₀_top hW
      (hJ.of_le (WithTop.coe_le_coe.2 le_top)) hJsq
      (hη.of_le (WithTop.coe_le_coe.2 le_top)) huW

/-- **Interior elliptic bootstrapping** (McDuff–Salamon, Theorem B.4.1 and Remark B.4.3): for a
finite exponent `p > 2`, a `C^ℓ` domain-dependent almost complex structure `J` (`J² = -1`) and a
`C^ℓ` inhomogeneous term `η`, every weak solution `u` of `∂_s u + J(z, u) ∂_t u = η(z, u)` on `Ω`
belongs to `W^{ℓ+1,p}_loc(Ω)`. The endpoint `p = ⊤` fails at `ℓ = 1`
(`TauCeti.not_memWkpLoc_two_top_graph_logLogExample`). -/
theorem memWkpLoc_of_isWeakCauchyRiemannOn [FiniteDimensional ℝ V] {p : ENNReal} (hp : 2 < p)
    (hp_top : p ≠ ⊤) {ℓ : ℕ} {Ω : Opens ℂ} {J : ℂ → V → V →L[ℝ] V}
    (hJ : ContDiff ℝ ℓ (Function.uncurry J))
    (hJsq : ∀ z x, (J z x).comp (J z x) = -ContinuousLinearMap.id ℝ V) {η : ℂ → V → V}
    (hη : ContDiff ℝ ℓ (Function.uncurry η)) {u : ℂ → V}
    (hu : IsWeakCauchyRiemannOn p Ω J η u) :
    MemWkpLoc p Ω (ℓ + 1) u :=
  hu.memWkpLoc_of_contDiffOn hp hp_top isOpen_univ hJ.contDiffOn (fun z _ => hJsq z (u z))
    hη.contDiffOn (fun _ _ => trivial)

/-- **Smooth interior bootstrapping**: for any `2 < p ≤ ∞`, a weak solution `u` of
`∂_s u + J(z, u) ∂_t u = η(z, u)` on `Ω` for smooth data `J` (`J² = -1`) and `η` is smooth on
`Ω`. Since `u` is continuous on `Ω`, no modification on a null set is needed. -/
theorem contDiffOn_of_isWeakCauchyRiemannOn [FiniteDimensional ℝ V] {p : ENNReal} (hp : 2 < p)
    {Ω : Opens ℂ} {J : ℂ → V → V →L[ℝ] V} (hJ : ContDiff ℝ ∞ (Function.uncurry J))
    (hJsq : ∀ z x, (J z x).comp (J z x) = -ContinuousLinearMap.id ℝ V) {η : ℂ → V → V}
    (hη : ContDiff ℝ ∞ (Function.uncurry η)) {u : ℂ → V}
    (hu : IsWeakCauchyRiemannOn p Ω J η u) :
    ContDiffOn ℝ ∞ u Ω :=
  hu.contDiffOn hp isOpen_univ hJ.contDiffOn (fun z _ => hJsq z (u z)) hη.contDiffOn
    (fun _ _ => trivial)

/-! ### Smoothness of `C¹` pseudoholomorphic curves -/

/-- **Smoothness of `C¹` pseudoholomorphic maps on planar domains.** If `J` is a smooth almost
complex structure on a finite-dimensional real normed space `V` and `u : ℂ → V` is `C¹` on an open
set `Ω ⊆ ℂ` and pseudoholomorphic on `Ω`, then `u` is `C^∞` on `Ω`. -/
theorem IsPseudoholomorphicOn.contDiffOn [FiniteDimensional ℝ V] {Ω : Opens ℂ}
    {J : SmoothAlmostComplexStructure 𝓘(ℝ, V) V} {u : ℂ → V}
    (h : IsPseudoholomorphicOn (AlmostComplexStructure.ofComplexModule ℂ).constSmooth J u Ω)
    (hu : ContDiffOn ℝ 1 u Ω) :
    ContDiffOn ℝ ∞ u Ω := by
  let J₀ : ℂ → V → V →L[ℝ] V := fun _ x => J.toEndomorphism x
  have hw : IsWeakCauchyRiemannOn 3 Ω J₀ (fun _ _ => 0) u :=
    (isWeakCauchyRiemannOn_iff_isPseudoholomorphicOn J hu).2 h
  have hJ_smooth : ContDiff ℝ ∞ (Function.uncurry J₀) :=
    J.contDiff_toEndomorphism.comp (contDiff_snd (E := ℂ) (F := V))
  have hJsq (z : ℂ) (x : V) : (J₀ z x).comp (J₀ z x) = -ContinuousLinearMap.id ℝ V := by
    ext v
    exact J.apply_apply x v
  exact contDiffOn_of_isWeakCauchyRiemannOn (by norm_num) hJ_smooth hJsq contDiff_const hw

/-- **Smoothness of global `C¹` pseudoholomorphic maps from `ℂ`.** If `J` is a smooth almost complex
structure on a finite-dimensional real normed space `V` and `u : ℂ → V` is `C¹` and
pseudoholomorphic, then `u` is `C^∞`. -/
theorem IsPseudoholomorphic.contDiff [FiniteDimensional ℝ V]
    {J : SmoothAlmostComplexStructure 𝓘(ℝ, V) V} {u : ℂ → V}
    (h : IsPseudoholomorphic (AlmostComplexStructure.ofComplexModule ℂ).constSmooth J u)
    (hu : ContDiff ℝ 1 u) :
    ContDiff ℝ ∞ u := by
  rw [← contDiffOn_univ]
  exact IsPseudoholomorphicOn.contDiffOn (Ω := ⊤) (h.isPseudoholomorphicOn _) hu.contDiffOn

end TauCeti
