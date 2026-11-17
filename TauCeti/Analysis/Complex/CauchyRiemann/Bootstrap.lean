/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import TauCeti.Analysis.Complex.CauchyRiemann.RoughCoefficients.Regularity
public import TauCeti.Analysis.Complex.CauchyRiemann.Weak
public import TauCeti.Geometry.Symplectic.Complex.Module.Basic
public import TauCeti.Geometry.Symplectic.JHolomorphic.Varying
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
`C^n` on `Ω` for any `n : ℕ∞` whenever `J` and `η` are `C^n` and `2 < p ≤ ∞` (McDuff–Salamon,
Theorem B.4.1 and Remark B.4.3). Because `u` is already continuous on `Ω` as part of
`IsWeakCauchyRiemannOn`, no modification on a null set is needed.

The proof freezes coefficients along the solution: if `u ∈ W^{m,p}_loc(Ω)` with `1 ≤ m ≤ ℓ`, the
higher-order local Sobolev chain rule (`TauCeti.MemWkpLoc.contDiffOn_comp_graph_succ`) places
`z ↦ J(z, u z)` and `z ↦ η(z, u z)` in `W^{m,p}_loc(Ω)`, and linear interior regularity for
Sobolev coefficients (`TauCeti.memWkpLoc_of_ae_cauchyRiemann`, with `S = 0`) upgrades `u` to
`W^{m+1,p}_loc(Ω)`.

For Sobolev membership `u ∈ W^{ℓ+1,p}_loc` at finite `ℓ`, the hypothesis `p ≠ ⊤` is sharp: in
`TauCeti.Analysis.Complex.CauchyRiemann.LogLog.Sobolev`, the graph of
`f(z) = z² log log (1 / ‖z‖)` (`TauCeti.isWeakCauchyRiemannOn_graph_logLogExample`) solves the
homogeneous equation for a `C¹` almost complex structure with `p = ∞`, yet fails to belong to
`W^{2,∞}_loc` on any neighbourhood of `0`
(`TauCeti.not_memWkpLoc_two_top_graph_logLogExample`). For `C^n` regularity (`n : ℕ∞`), the
endpoint `p = ∞` is allowed because a `W^{1,∞}_loc` solution is `W^{1,3}_loc` by local
monotonicity in the exponent, and `W^{ℓ+1,3}_loc ⊂ C^ℓ`.

Applying local `C^n` bootstrapping to `J`-holomorphic maps into a finite-dimensional real normed
space yields `C^n` regularity under local `C^n` regularity of `J`. The manifold-level smoothness
corollaries for `TauCeti.IsPseudoholomorphicOn` and `TauCeti.IsPseudoholomorphic` live in
`TauCeti.Geometry.Symplectic.Manifold.JHolomorphic.Regularity`.

## Main results

* `TauCeti.IsWeakCauchyRiemannOn.memWkpLoc_of_contDiffOn`: local-neighbourhood `C^ℓ` data give
  `MemWkpLoc p Ω (ℓ + 1) u` for `2 < p < ∞`.
* `TauCeti.IsWeakCauchyRiemannOn.contDiffOn`: local-neighbourhood `C^n` data (`n : ℕ∞`) give
  `ContDiffOn ℝ n u Ω` for every `2 < p ≤ ∞`.
* `TauCeti.memWkpLoc_of_isWeakCauchyRiemannOn`,
  `TauCeti.contDiffOn_of_isWeakCauchyRiemannOn`: the global-data planar forms.
* `TauCeti.IsJHolomorphicOn.contDiffOn`, `TauCeti.IsJHolomorphic.contDiff`: a `C¹` map from an open
  subset `s ⊆ ℂ` (or all of `ℂ`) into a finite-dimensional real normed space that is
  `J`-holomorphic for a locally (or globally) `C^n` almost complex structure `J` is `C^n`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.4 (Theorem B.4.1 and Remark B.4.3).
-/

public noncomputable section

open Complex MeasureTheory Set TopologicalSpace
open scoped ContDiff ENNReal NNReal

namespace TauCeti

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
  have hp1 : (1 : ℝ≥0∞) < p := (by exact_mod_cast one_lt_two : (1 : ℝ≥0∞) < 2).trans hp
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
    exact memWkpLoc_of_ae_cauchyRiemann hp hp1.le hp1 ENNReal.coe_ne_top le_rfl
      (Nat.succ_pos d') le_rfl le_rfl hJu hJsq_ae memWkpLoc_zero_fun hu1 hD hae_lin hηu

/-- **`C^n` interior bootstrapping with local `C^n` data.** For every `2 < p ≤ ∞` and `n : ℕ∞`, if
`J` and `η` are `C^n` on an open neighbourhood `W ⊆ ℂ × V` of the graph of `u` over `Ω` and
`J(z, u z)² = -1` for every `z ∈ Ω`, then `u` is `C^n` on `Ω` (with no null-set modification, since
`u` is continuous on `Ω`). Unlike Sobolev membership at `p = ⊤`, `p = ⊤` is allowed here because a
`W^{1,∞}_loc` solution is `W^{1,3}_loc`. -/
theorem IsWeakCauchyRiemannOn.contDiffOn [FiniteDimensional ℝ V] {p : ENNReal} (hp : 2 < p)
    {n : ℕ∞} {Ω : Opens ℂ} {W : Set (ℂ × V)} (hW : IsOpen W)
    {J : ℂ → V → V →L[ℝ] V} {η : ℂ → V → V} {u : ℂ → V}
    (hJ : ContDiffOn ℝ n (Function.uncurry J) W)
    (hJsq : ∀ z ∈ (Ω : Set ℂ), (J z (u z)).comp (J z (u z)) = -ContinuousLinearMap.id ℝ V)
    (hη : ContDiffOn ℝ n (Function.uncurry η) W)
    (hu : IsWeakCauchyRiemannOn p Ω J η u) (huW : ∀ z ∈ (Ω : Set ℂ), (z, u z) ∈ W) :
    ContDiffOn ℝ n u Ω := by
  let p₀ : ENNReal := min p 3
  have hp₀ : 2 < p₀ := lt_min hp (by exact_mod_cast (by norm_num : 2 < 3))
  have hp₀_top : p₀ ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofNat_ne_top (min_le_right p 3)
  have hu₀ : IsWeakCauchyRiemannOn p₀ Ω J η u := hu.mono_exponent (min_le_left p 3)
  refine contDiffOn_iff_forall_nat_le.2 fun ℓ hℓ => ?_
  have husob := hu₀.memWkpLoc_of_contDiffOn hp₀ hp₀_top hW (hJ.of_le (mod_cast hℓ)) hJsq
    (hη.of_le (mod_cast hℓ)) huW
  obtain ⟨g, hg, hug⟩ := husob.exists_contDiffOn_ae_eq hp₀
  exact hg.congr (Measure.eqOn_open_of_ae_eq hug Ω.isOpen hu.continuousOn hg.continuousOn)

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

/-- **`C^n` interior bootstrapping**: for any `2 < p ≤ ∞` and `n : ℕ∞`, a weak solution `u` of
`∂_s u + J(z, u) ∂_t u = η(z, u)` on `Ω` for `C^n` data `J` (`J² = -1`) and `η` is `C^n` on `Ω`.
Since `u` is continuous on `Ω`, no modification on a null set is needed. -/
theorem contDiffOn_of_isWeakCauchyRiemannOn [FiniteDimensional ℝ V] {p : ENNReal} (hp : 2 < p)
    {n : ℕ∞} {Ω : Opens ℂ} {J : ℂ → V → V →L[ℝ] V} (hJ : ContDiff ℝ n (Function.uncurry J))
    (hJsq : ∀ z x, (J z x).comp (J z x) = -ContinuousLinearMap.id ℝ V) {η : ℂ → V → V}
    (hη : ContDiff ℝ n (Function.uncurry η)) {u : ℂ → V}
    (hu : IsWeakCauchyRiemannOn p Ω J η u) :
    ContDiffOn ℝ n u Ω :=
  hu.contDiffOn hp isOpen_univ hJ.contDiffOn (fun z _ => hJsq z (u z)) hη.contDiffOn
    (fun _ _ => trivial)

/-! ### Local `C^n` regularity of `C¹` `J`-holomorphic maps on normed spaces -/

/-- **Local `C^n` regularity of `C¹` `J`-holomorphic maps on planar open sets.** Let `V` be a
finite-dimensional real normed space, let `W ⊆ V` be an open set on which
`x ↦ LinearMap.toContinuousLinearMap (J x).toLinearMap` is `C^n`, and let `u : ℂ → V` be a `C¹` map
on an open set `s ⊆ ℂ` mapping `s` into `W` and satisfying
`IsJHolomorphicOn (fun _ => AlmostComplexStructure.ofComplexModule ℂ) J u s`. Then `u` is `C^n` on
`s` (McDuff–Salamon, Theorem B.4.1 and Remark B.4.3). -/
theorem IsJHolomorphicOn.contDiffOn [FiniteDimensional ℝ V] {n : ℕ∞} {s : Set ℂ} {W : Set V}
    {J : V → AlmostComplexStructure V} {u : ℂ → V}
    (h : IsJHolomorphicOn (fun _ => AlmostComplexStructure.ofComplexModule ℂ) J u s)
    (hs : IsOpen s) (hW : IsOpen W)
    (hJ : ContDiffOn ℝ n (fun x => LinearMap.toContinuousLinearMap (J x).toLinearMap) W)
    (hu : ContDiffOn ℝ 1 u s) (huW : MapsTo u s W) :
    ContDiffOn ℝ n u s := by
  have : CompleteSpace V := FiniteDimensional.completeSpace ℝ V
  let Ω : Opens ℂ := ⟨s, hs⟩
  let J₀ : ℂ → V → V →L[ℝ] V := fun _ x => LinearMap.toContinuousLinearMap (J x).toLinearMap
  have hw : IsWeakCauchyRiemannOn 3 Ω J₀ (fun _ _ => 0) u := by
    refine isWeakCauchyRiemannOn_of_contDiffOn (Ω := Ω) hu fun z hz => ?_
    have hz_hol := (h.isJHolomorphicWithinAt hz).isJHolomorphicAt_of_mem_nhds (hs.mem_nhds hz)
    have hcomm : fderiv ℝ u z I = (J (u z)).toLinearMap (fderiv ℝ u z 1) := by
      have h1 := LinearMap.congr_fun hz_hol.fderiv_isComplexLinear 1
      simpa only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe,
        AlmostComplexStructure.ofComplexModule_apply, smul_eq_mul, mul_one] using h1
    have hsq :
        (J (u z)).toLinearMap ((J (u z)).toLinearMap (fderiv ℝ u z 1)) = -fderiv ℝ u z 1 := by
      simpa only [LinearMap.comp_apply, LinearMap.neg_apply, LinearMap.id_apply] using
        LinearMap.congr_fun (J (u z)).square_neg (fderiv ℝ u z 1)
    simp only [J₀, LinearMap.coe_toContinuousLinearMap', hcomm, hsq, add_neg_cancel]
  have hJ_cd : ContDiffOn ℝ n (Function.uncurry J₀) (univ ×ˢ W) :=
    hJ.comp contDiffOn_snd fun _ hp => hp.2
  have hJsq : ∀ z ∈ (Ω : Set ℂ), (J₀ z (u z)).comp (J₀ z (u z)) = -ContinuousLinearMap.id ℝ V :=
    fun z _ => ContinuousLinearMap.ext fun v => (J (u z)).apply_apply v
  exact hw.contDiffOn (by exact_mod_cast (by norm_num : 2 < 3)) (isOpen_univ.prod hW) hJ_cd hJsq
    contDiffOn_const fun z hz => ⟨trivial, huW hz⟩

/-- **Global `C^n` regularity of `C¹` `J`-holomorphic maps from `ℂ`.** If `V` is a
finite-dimensional real normed space, `x ↦ LinearMap.toContinuousLinearMap (J x).toLinearMap` is
`C^n`, and `u : ℂ → V` is `C¹` and `J`-holomorphic, then `u` is `C^n`. -/
theorem IsJHolomorphic.contDiff [FiniteDimensional ℝ V] {n : ℕ∞}
    {J : V → AlmostComplexStructure V} {u : ℂ → V}
    (h : IsJHolomorphic (fun _ => AlmostComplexStructure.ofComplexModule ℂ) J u)
    (hJ : ContDiff ℝ n (fun x => LinearMap.toContinuousLinearMap (J x).toLinearMap))
    (hu : ContDiff ℝ 1 u) :
    ContDiff ℝ n u :=
  contDiffOn_univ.1 <| (h.isJHolomorphicOn univ).contDiffOn isOpen_univ isOpen_univ
    hJ.contDiffOn hu.contDiffOn (mapsTo_univ u univ)

end TauCeti
