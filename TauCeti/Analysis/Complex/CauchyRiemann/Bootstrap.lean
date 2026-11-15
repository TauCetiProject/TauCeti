/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import TauCeti.Analysis.Complex.CauchyRiemann.RoughCoefficients.Regularity
public import TauCeti.Analysis.Complex.CauchyRiemann.Weak
public import TauCeti.Geometry.Manifold.Complex.Isothermal
public import TauCeti.Geometry.Symplectic.Complex.Module.Basic
import TauCeti.Analysis.Sobolev.Local.ChainRule.Higher
import TauCeti.Analysis.Sobolev.Local.Morrey.Higher
import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Chart

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
space yields `C^n` regularity under local `C^n` regularity of `J`, and working in target charts and
isothermal domain charts upgrades any `C¹` pseudoholomorphic curve from an almost complex surface
with isothermal charts into a finite-dimensional smooth almost complex manifold without boundary to
a `C^n` (in particular smooth) map.

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
* `TauCeti.IsPseudoholomorphicOn.contMDiffOn`, `TauCeti.IsPseudoholomorphic.contMDiff`: a `C¹`
  pseudoholomorphic map from an open subset (or all) of an almost complex surface with isothermal
  charts into a finite-dimensional smooth almost complex manifold without boundary is `C^n` for
  every `n : ℕ∞`.
* `TauCeti.IsPseudoholomorphicOn.contDiffOn`, `TauCeti.IsPseudoholomorphic.contDiff`: the planar
  specializations for maps `ℂ → V`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.4 (Theorem B.4.1 and Remark B.4.3).
-/

public noncomputable section

open Complex MeasureTheory Set TopologicalSpace
open scoped ContDiff ENNReal Manifold NNReal

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
    have hcomm : fderiv ℝ u z I = J (u z) (fderiv ℝ u z 1) := by
      have h1 := hz_hol.fderiv_apply_commute (v := (1 : ℂ))
      simpa [AlmostComplexStructure.ofComplexModule_apply] using h1
    change fderiv ℝ u z 1 + J (u z) (fderiv ℝ u z I) = 0
    rw [hcomm, (J (u z)).apply_apply, add_neg_cancel]
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

/-! ### Smoothness of `C¹` pseudoholomorphic curves between almost complex manifolds -/

private theorem contMDiffOn_of_isPseudoholomorphicOn_ofComplexManifold
    {E' H' M' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
    [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} [I'.Boundaryless]
    [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' ∞ M']
    {J : SmoothAlmostComplexStructure I' M'}
    {s : Set ℂ} {u : ℂ → M'}
    (h : IsPseudoholomorphicOn (SmoothAlmostComplexStructure.ofComplexManifold ℂ ℂ) J u s)
    (hs : IsOpen s) (hu : ContMDiffOn 𝓘(ℝ, ℂ) I' 1 u s) :
    ContMDiffOn 𝓘(ℝ, ℂ) I' ∞ u s := by
  classical
  intro z₀ hz₀
  refine ContMDiffAt.contMDiffWithinAt ?_
  let φ := extChartAt I' (u z₀)
  let U : Set ℂ := s ∩ u ⁻¹' φ.source
  let W : Set E' := φ.target
  let v : ℂ → E' := φ ∘ u
  have hφ_src : IsOpen φ.source := isOpen_extChartAt_source (I := I') (u z₀)
  have hW : IsOpen W := isOpen_extChartAt_target (I := I') (u z₀)
  have hU : IsOpen U := hu.continuousOn.isOpen_inter_preimage hs hφ_src
  have hz₀U : z₀ ∈ U := ⟨hz₀, mem_extChartAt_source (u z₀)⟩
  have hvW : MapsTo v U W := fun z hz => φ.map_source hz.2
  have hφ_c1 : ContMDiffOn I' 𝓘(ℝ, E') 1 φ φ.source := by
    rw [extChartAt_source]
    exact (contMDiffOn_extChartAt (I := I') (x := u z₀)).of_le (WithTop.coe_le_coe.2 le_top)
  have hv_c1 : ContDiffOn ℝ 1 v U :=
    contMDiffOn_iff_contDiffOn.1 (hφ_c1.comp (hu.mono inter_subset_left) inter_subset_right)
  let J₀ : AlmostComplexStructure E' :=
    ⟨(J.inChart (u z₀) (φ (u z₀))).toLinearMap,
      LinearMap.ext fun w => J.inChart_inChart (u z₀) (mem_extChartAt_target (u z₀)) w⟩
  let J_chart : E' → AlmostComplexStructure E' := fun y =>
    if hy : y ∈ W then
      ⟨(J.inChart (u z₀) y).toLinearMap,
        LinearMap.ext fun w => J.inChart_inChart (u z₀) hy w⟩
    else J₀
  have hJ_chart_eq : EqOn (fun y => LinearMap.toContinuousLinearMap (J_chart y).toLinearMap)
      (J.inChart (u z₀)) W := fun y hy => by
    ext w
    simp [J_chart, hy]
  have hJ_chart_smooth :
      ContDiffOn ℝ ∞ (fun y => LinearMap.toContinuousLinearMap (J_chart y).toLinearMap) W :=
    (J.contDiffOn_inChart (u z₀)).congr hJ_chart_eq
  have hv_hol :
      IsJHolomorphicOn (fun _ => AlmostComplexStructure.ofComplexModule ℂ) J_chart v U := by
    refine (isJHolomorphicOn_iff _ _ _ _).2 fun z hz => ?_
    have hv_diff : DifferentiableAt ℝ v z :=
      (hv_c1.differentiableOn one_ne_zero).differentiableAt (hU.mem_nhds hz)
    have hu_at : IsPseudoholomorphicAt (SmoothAlmostComplexStructure.ofComplexManifold ℂ ℂ) J u z :=
      (h.isPseudoholomorphicWithinAt hz.1).isPseudoholomorphicAt_of_mem_nhds (hs.mem_nhds hz.1)
    refine (isJHolomorphicAt_of_hasFDerivAt hv_diff.hasFDerivAt ?_).isJHolomorphicWithinAt
    refine (isComplexLinearMap_iff_apply _ _ _).2 fun w => ?_
    have hchart := J.fderiv_extChartAt_comp_apply_eq_inChart (u z₀) hu_at.continuousAt hz.2
      (hu_at.mfderiv_apply_commute w)
    have hI : AlmostComplexStructure.ofComplexModule ℂ w =
        SmoothAlmostComplexStructure.ofComplexManifold ℂ ℂ z w := by
      rw [AlmostComplexStructure.ofComplexModule_apply,
        SmoothAlmostComplexStructure.ofComplexManifold_apply]
    have hJy : J_chart (v z) (fderiv ℝ v z w) = J.inChart (u z₀) (v z) (fderiv ℝ v z w) := by
      simp [J_chart, hvW hz]
    change fderiv ℝ v z (AlmostComplexStructure.ofComplexModule ℂ w) =
      J_chart (v z) (fderiv ℝ v z w)
    rw [hI, hJy]
    exact hchart
  have hv_smooth : ContDiffOn ℝ ∞ v U := hv_hol.contDiffOn hU hW hJ_chart_smooth hv_c1 hvW
  have hv_at : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E') ∞ v z₀ :=
    contMDiffAt_iff_contDiffAt.2 (hv_smooth.contDiffAt (hU.mem_nhds hz₀U))
  have hφ_symm : ContMDiffAt 𝓘(ℝ, E') I' ∞ φ.symm (v z₀) :=
    (contMDiffOn_extChartAt_symm (I := I') (u z₀)).contMDiffAt (hW.mem_nhds (hvW hz₀U))
  have h_eq : u =ᶠ[nhds z₀] φ.symm ∘ v := by
    filter_upwards [hU.mem_nhds hz₀U] with z hz
    exact (φ.left_inv hz.2).symm
  exact (hφ_symm.comp z₀ hv_at).congr_of_eventuallyEq h_eq

private theorem contMDiffAt_of_isIsothermalChart
    {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℝ, ℂ) ∞ M]
    {j : SmoothAlmostComplexStructure 𝓘(ℝ, ℂ) M} {e : OpenPartialHomeomorph M ℂ}
    (he : IsIsothermalChart j e) {x₀ : M} (hx₀ : x₀ ∈ e.source) :
    ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ e x₀ := by
  have he_symm_hol :
      IsPseudoholomorphicOn (SmoothAlmostComplexStructure.ofComplexManifold ℂ ℂ) j e.symm
        e.target :=
    isPseudoholomorphicOn_iff.2 fun z hz =>
      (he.isPseudoholomorphicAt_symm hz).isPseudoholomorphicWithinAt
  have he_symm_c1 : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) 1 e.symm e.target :=
    contMDiffOn_symm_of_mem_maximalAtlas he.mem_maximalAtlas
  have he_symm_smooth : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ e.symm e.target :=
    contMDiffOn_of_isPseudoholomorphicOn_ofComplexManifold he_symm_hol e.open_target he_symm_c1
  let ψ : OpenPartialHomeomorph M ℂ := chartAt ℂ x₀
  let f : OpenPartialHomeomorph ℂ ℂ := e.symm ≫ₕ ψ
  let z₀ : ℂ := e x₀
  let w₀ : ℂ := ψ x₀
  have hz₀ : z₀ ∈ e.target := e.map_source hx₀
  have hx₀ψ : x₀ ∈ ψ.source := mem_chart_source ℂ x₀
  have hw₀ψ : w₀ ∈ ψ.target := ψ.map_source hx₀ψ
  have hz₀f : z₀ ∈ f.source := ⟨hz₀, by simpa [z₀, e.left_inv hx₀] using hx₀ψ⟩
  have hw₀f : w₀ ∈ f.target := ⟨hw₀ψ, by simpa [w₀, ψ.left_inv hx₀ψ] using hx₀⟩
  have hfsymm_w₀ : f.symm w₀ = z₀ := by simp [f, w₀, z₀, ψ.left_inv hx₀ψ]
  have hf_z₀ : f z₀ = w₀ := by simp [f, w₀, z₀, e.left_inv hx₀]
  have hψ_at : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ ψ x₀ :=
    (contMDiffOn_chart (I := 𝓘(ℝ, ℂ)) (x := x₀)).contMDiffAt (ψ.open_source.mem_nhds hx₀ψ)
  have hf_smooth : ContDiffAt ℝ ∞ f z₀ := by
    have he_symm_at : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ e.symm z₀ :=
      he_symm_smooth.contMDiffAt (e.open_target.mem_nhds hz₀)
    have hψ_at' : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ ψ (e.symm z₀) := by
      simpa [z₀, e.left_inv hx₀] using hψ_at
    exact contMDiffAt_iff_contDiffAt.1 (hψ_at'.comp z₀ he_symm_at)
  have hf_diff : DifferentiableAt ℝ f z₀ := hf_smooth.differentiableAt (by simp)
  have hf_symm_diff : DifferentiableAt ℝ f.symm w₀ := by
    have he_diff : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) e (ψ.symm w₀) := by
      simpa [w₀, ψ.left_inv hx₀ψ] using
        mdifferentiableAt_of_mem_maximalAtlas he.mem_maximalAtlas hx₀
    have hψ_symm_diff : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ψ.symm w₀ :=
      (contMDiffOn_chart_symm (I := 𝓘(ℝ, ℂ)) (n := ∞) (x := x₀)).contMDiffAt
        (ψ.open_target.mem_nhds hw₀ψ) |>.mdifferentiableAt (by simp)
    exact mdifferentiableAt_iff_differentiableAt.1 (he_diff.comp w₀ hψ_symm_diff)
  have hleft_inv : (fderiv ℝ f.symm w₀).comp (fderiv ℝ f z₀) = ContinuousLinearMap.id ℝ ℂ := by
    have hfd_symm : HasFDerivAt f.symm (fderiv ℝ f.symm w₀) (f z₀) := by
      rw [hf_z₀]
      exact hf_symm_diff.hasFDerivAt
    have hcomp : HasFDerivAt (f.symm ∘ f) ((fderiv ℝ f.symm w₀).comp (fderiv ℝ f z₀)) z₀ :=
      hfd_symm.comp z₀ hf_diff.hasFDerivAt
    have heq : id =ᶠ[nhds z₀] f.symm ∘ f := by
      filter_upwards [f.open_source.mem_nhds hz₀f] with z hz
      exact (f.left_inv hz).symm
    exact (hcomp.congr_of_eventuallyEq heq).unique (hasFDerivAt_id z₀)
  have hright_inv : (fderiv ℝ f z₀).comp (fderiv ℝ f.symm w₀) = ContinuousLinearMap.id ℝ ℂ := by
    have hfd : HasFDerivAt f (fderiv ℝ f z₀) (f.symm w₀) := by
      rw [hfsymm_w₀]
      exact hf_diff.hasFDerivAt
    have hcomp : HasFDerivAt (f ∘ f.symm) ((fderiv ℝ f z₀).comp (fderiv ℝ f.symm w₀)) w₀ :=
      hfd.comp w₀ hf_symm_diff.hasFDerivAt
    have heq : id =ᶠ[nhds w₀] f ∘ f.symm := by
      filter_upwards [f.open_target.mem_nhds hw₀f] with w hw
      exact (f.right_inv hw).symm
    exact (hcomp.congr_of_eventuallyEq heq).unique (hasFDerivAt_id w₀)
  let f₀' : ℂ ≃L[ℝ] ℂ :=
    ContinuousLinearEquiv.equivOfInverse (fderiv ℝ f z₀) (fderiv ℝ f.symm w₀)
      (fun v => DFunLike.congr_fun hleft_inv v) (fun v => DFunLike.congr_fun hright_inv v)
  have hf_symm_smooth : ContDiffAt ℝ ∞ f.symm w₀ :=
    f.contDiffAt_symm (f₀' := f₀') hw₀f (hfsymm_w₀ ▸ hf_diff.hasFDerivAt) (hfsymm_w₀ ▸ hf_smooth)
  have he_eq : e =ᶠ[nhds x₀] f.symm ∘ ψ := by
    filter_upwards [ψ.open_source.mem_nhds hx₀ψ] with x hx
    simp [f, ψ.left_inv hx]
  exact ((contMDiffAt_iff_contDiffAt.2 hf_symm_smooth).comp x₀ hψ_at).congr_of_eventuallyEq he_eq

/-- **Smoothness of `C¹` pseudoholomorphic curves between almost complex manifolds.** Let `M` be a
smooth real surface carrying a smooth almost complex structure `j` with isothermal charts, and let
`M'` be a finite-dimensional smooth manifold without boundary carrying a smooth almost complex
structure `J`. If `u : M → M'` is `C¹` and `(j, J)`-holomorphic on an open set `s ⊆ M`, then `u`
is `C^n` on `s` for every `n : ℕ∞` (McDuff–Salamon, Theorem B.4.1). -/
theorem IsPseudoholomorphicOn.contMDiffOn
    {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℝ, ℂ) ∞ M]
    {j : SmoothAlmostComplexStructure 𝓘(ℝ, ℂ) M} [j.HasIsothermalCharts]
    {E' H' M' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
    [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} [I'.Boundaryless]
    [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' ∞ M']
    {J : SmoothAlmostComplexStructure I' M'}
    {s : Set M} {n : ℕ∞} {u : M → M'}
    (h : IsPseudoholomorphicOn j J u s) (hs : IsOpen s) (hu : ContMDiffOn 𝓘(ℝ, ℂ) I' 1 u s) :
    ContMDiffOn 𝓘(ℝ, ℂ) I' n u s := by
  suffices ContMDiffOn 𝓘(ℝ, ℂ) I' ∞ u s from this.of_le (WithTop.coe_le_coe.2 le_top)
  intro x₀ hx₀s
  refine ContMDiffAt.contMDiffWithinAt ?_
  obtain ⟨e, he, hx₀⟩ :=
    SmoothAlmostComplexStructure.HasIsothermalCharts.exists_isIsothermalChart (j := j) x₀
  let T : Set ℂ := e.target ∩ e.symm ⁻¹' s
  have hT : IsOpen T := e.isOpen_inter_preimage_symm hs
  have h_comp_c1 : ContMDiffOn 𝓘(ℝ, ℂ) I' 1 (u ∘ e.symm) T :=
    hu.comp ((contMDiffOn_symm_of_mem_maximalAtlas he.mem_maximalAtlas).mono inter_subset_left)
      inter_subset_right
  have h_comp_hol :
      IsPseudoholomorphicOn (SmoothAlmostComplexStructure.ofComplexManifold ℂ ℂ) J
        (u ∘ e.symm) T :=
    isPseudoholomorphicOn_iff.2 fun z hz =>
      (((h.isPseudoholomorphicWithinAt hz.2).isPseudoholomorphicAt_of_mem_nhds
        (hs.mem_nhds hz.2)).comp
          (he.isPseudoholomorphicAt_symm hz.1)).isPseudoholomorphicWithinAt
  have h_comp_smooth : ContMDiffOn 𝓘(ℝ, ℂ) I' ∞ (u ∘ e.symm) T :=
    contMDiffOn_of_isPseudoholomorphicOn_ofComplexManifold h_comp_hol hT h_comp_c1
  have hz₀T : e x₀ ∈ T := ⟨e.map_source hx₀, by simpa [e.left_inv hx₀] using hx₀s⟩
  have h_comp_at : ContMDiffAt 𝓘(ℝ, ℂ) I' ∞ (u ∘ e.symm) (e x₀) :=
    h_comp_smooth.contMDiffAt (hT.mem_nhds hz₀T)
  have he_at : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ e x₀ := contMDiffAt_of_isIsothermalChart he hx₀
  have hu_eq : u =ᶠ[nhds x₀] (u ∘ e.symm) ∘ e := by
    filter_upwards [e.open_source.mem_nhds hx₀] with x hx
    simp [e.left_inv hx]
  exact (h_comp_at.comp x₀ he_at).congr_of_eventuallyEq hu_eq

/-- **Smoothness of global `C¹` pseudoholomorphic curves between almost complex manifolds.** If `M`
is a smooth real surface with a smooth almost complex structure `j` admitting isothermal charts,
`M'` is a finite-dimensional smooth manifold without boundary with a smooth almost complex
structure `J`, and `u : M → M'` is `C¹` and `(j, J)`-holomorphic, then `u` is `C^n` for every
`n : ℕ∞`. -/
theorem IsPseudoholomorphic.contMDiff
    {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℝ, ℂ) ∞ M]
    {j : SmoothAlmostComplexStructure 𝓘(ℝ, ℂ) M} [j.HasIsothermalCharts]
    {E' H' M' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
    [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} [I'.Boundaryless]
    [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' ∞ M']
    {J : SmoothAlmostComplexStructure I' M'}
    {n : ℕ∞} {u : M → M'}
    (h : IsPseudoholomorphic j J u) (hu : ContMDiff 𝓘(ℝ, ℂ) I' 1 u) :
    ContMDiff 𝓘(ℝ, ℂ) I' n u :=
  contMDiffOn_univ.1 <| (h.isPseudoholomorphicOn univ).contMDiffOn isOpen_univ hu.contMDiffOn

/-- **Smoothness of `C¹` pseudoholomorphic maps on planar open sets.** If `j` is a smooth almost
complex structure on `ℂ` with isothermal charts (for instance `ofComplexManifold ℂ ℂ`), `J` is a
smooth almost complex structure on a finite-dimensional real normed space `V`, and `u : ℂ → V` is
`C¹` and `(j, J)`-holomorphic on an open set `s ⊆ ℂ`, then `u` is `C^n` on `s` for every
`n : ℕ∞`. -/
theorem IsPseudoholomorphicOn.contDiffOn [FiniteDimensional ℝ V]
    {j : SmoothAlmostComplexStructure 𝓘(ℝ, ℂ) ℂ} [j.HasIsothermalCharts]
    {J : SmoothAlmostComplexStructure 𝓘(ℝ, V) V} {s : Set ℂ} {n : ℕ∞} {u : ℂ → V}
    (h : IsPseudoholomorphicOn j J u s) (hs : IsOpen s) (hu : ContDiffOn ℝ 1 u s) :
    ContDiffOn ℝ n u s :=
  contMDiffOn_iff_contDiffOn.1 (h.contMDiffOn hs (contMDiffOn_iff_contDiffOn.2 hu))

/-- **Smoothness of global `C¹` pseudoholomorphic maps from `ℂ`.** If `j` is a smooth almost
complex structure on `ℂ` with isothermal charts, `J` is a smooth almost complex structure on a
finite-dimensional real normed space `V`, and `u : ℂ → V` is `C¹` and `(j, J)`-holomorphic, then
`u` is `C^n` for every `n : ℕ∞`. -/
theorem IsPseudoholomorphic.contDiff [FiniteDimensional ℝ V]
    {j : SmoothAlmostComplexStructure 𝓘(ℝ, ℂ) ℂ} [j.HasIsothermalCharts]
    {J : SmoothAlmostComplexStructure 𝓘(ℝ, V) V} {n : ℕ∞} {u : ℂ → V}
    (h : IsPseudoholomorphic j J u) (hu : ContDiff ℝ 1 u) :
    ContDiff ℝ n u :=
  contMDiff_iff_contDiff.1 (h.contMDiff (contMDiff_iff_contDiff.2 hu))

end TauCeti
