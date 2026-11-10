/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Capacity.Monotonicity
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import TauCeti.Dynamics.Flow.Periodic.Limit
import TauCeti.Geometry.Manifold.Flow.Complete
import TauCeti.Geometry.Manifold.IntegralCurve.Basic
import TauCeti.Geometry.Manifold.IntegralCurve.GlobalFlow
import TauCeti.Geometry.Manifold.IntegralCurve.Monotone
import TauCeti.Geometry.Manifold.LocallyContractible
import TauCeti.Geometry.Manifold.RegularValue.Factorization
import TauCeti.Geometry.Symplectic.Hamiltonian.Characteristic

/-!
# Contractible almost existence from a finite capacity

Let `σ` be a nondegenerate two-form on a finite-dimensional boundaryless Hausdorff manifold `M`,
`W ⊆ M` the set in which contractibility is tested, and `F : M → ℝ` a smooth function whose
sublevel sets `{F ≤ s}` are compact for `s < b`, with `{F < b} ⊆ W`, and which attains every value
in `(a, b)`. This file completes the Hofer–Zehnder–Struwe argument: under these hypotheses,
finiteness of the relative `π₁`-sensitive Hofer–Zehnder capacity `c°_HZ({F < b}, Z)` in `W`, for
`Z ⊆ {F ≤ a}`, gives a closed characteristic, contractible in `W`, on almost every regular level
of `F` in `(a, b)`
(`TauCeti.SmoothTwoForm.IsNondegenerate.ae_hasContractibleClosedCharacteristic`). Hence every
level in `(a, b)` has the contractible almost existence property in `W`
(`TauCeti.SmoothTwoForm.IsNondegenerate.hasContractibleAlmostExistence`). Since the relative
capacity in `W` of a subset of `W` is bounded by the absolute capacity `c°_HZ(W)`, finiteness of
`c°_HZ(W)` gives the contractible almost existence property in `W` on every nonempty regular level
of `F` whose sublevel sets just above it are compact and lie in `W`
(`IsNondegenerate.hasContractibleAlmostExistence_of_contractibleHZCapacity_ne_top`). This is
Proposition 6.3 of Barraud–Damian–Humilière–Oancea for a domain `W`, for instance a Liouville
domain inside its completion; `W = M` gives the statement for the manifold itself.

The monotonicity argument
(`IsNondegenerate.ae_forall_exists_hasContractibleClosedCharacteristicOfPeriodLE`) provides, for
almost every `s ∈ (a, b)`, a bound `K` and closed characteristics, contractible in `W`, of period at
most `K` on levels arbitrarily close to `s`. The remaining step is a compactness argument
(`IsNondegenerate.hasContractibleClosedCharacteristicOfPeriodLE_of_frequently`): if levels
arbitrarily close to a regular level `s` carry such orbits, and the sublevel set `{F ≤ b}` is
compact for some `b > s`, with `{F < b} ⊆ W`, then the level `s` itself carries one. The
Hamiltonian vector field `X_F`, cut off outside `{F < b}`, generates a global flow which preserves
the levels of `F`, and the closed characteristics on the nearby levels are periodic orbits of this
flow. By compactness, their base points and periods converge along an ultrafilter, and the general
facts about limits of periodic orbits of a flow (`TauCeti.Dynamics.Flow.Periodic.Limit`), applied
to the flow restricted to the invariant open set `{F < b}` and to its inclusion into `W`, show that
the limit is a periodic orbit on the level `s` with loop contractible in `W`. Its period is positive
because `X_F` does not vanish on a regular level, while periodic orbits whose periods tend to `0`
accumulate only at rest points.

## Main results

* `IsNondegenerate.hasContractibleClosedCharacteristicOfPeriodLE_of_frequently`: closed
  characteristics of bounded period on levels accumulating at a regular level `s` give one
  on the level `s`.
* `TauCeti.SmoothTwoForm.IsNondegenerate.ae_hasContractibleClosedCharacteristic`: if the
  sublevel sets `{F ≤ s}`, `s < b`, are compact and `F` attains every value in `(a, b)`, finite
  relative capacity gives closed characteristics on almost every regular level in `(a, b)`.
* `TauCeti.SmoothTwoForm.IsNondegenerate.hasContractibleAlmostExistence`: under the same
  hypotheses, finite relative capacity gives the contractible almost existence property on every
  level in `(a, b)`.
* `IsNondegenerate.hasContractibleAlmostExistence_of_contractibleHZCapacity_ne_top`: finiteness of
  `c°_HZ(W)` implies the contractible almost existence property in `W` of every nonempty regular
  level with compact sublevel sets inside `W` just above it, Proposition 6.3.

## References

* H. Hofer, E. Zehnder, *Symplectic Invariants and Hamiltonian Dynamics*, Birkhäuser, 1994,
  Section 4.2.
* M. Struwe, *Existence of periodic solutions of Hamiltonian systems on almost every energy
  surface*, Bol. Soc. Brasil. Mat. 20 (1990), 49–58.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, Proposition 6.3.
-/

public section

noncomputable section

open Filter Function MeasureTheory Set Topology
open scoped ContDiff ENNReal Manifold

namespace TauCeti

namespace SmoothTwoForm

namespace IsNondegenerate

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [BoundarylessManifold I M] {σ : SmoothTwoForm I M}
  {W Z : Set M} {F : M → ℝ}

/-- **The Hamiltonian vector field cut off outside a compact sublevel set.** For `m < b` with
`{F ≤ b}` compact, the field `ψ(F) X_F`, with `ψ` a smooth step from `1` on `(-∞, m]` to `0` on
`[b, ∞)`, is a complete `C¹` vector field equal to `X_F` on `{F ≤ m}` and a multiple of `X_F` at
every point. -/
private theorem exists_isCompleteVectorField_eq_hamiltonianVectorField (hσ : σ.IsNondegenerate)
    (hF : ContMDiff I 𝓘(ℝ) 2 F) {m b : ℝ} (hmb : m < b) (hcpt : IsCompact {x | F x ≤ b}) :
    ∃ v : (x : M) → TangentSpace I x,
      ContMDiff I I.tangent 1 (fun x ↦ (⟨x, v x⟩ : TangentBundle I M)) ∧
        IsCompleteVectorField v ∧ (∀ x, F x ≤ m → v x = σ.hamiltonianVectorField F x) ∧
          ∀ x, ∃ a : ℝ, v x = a • σ.hamiltonianVectorField F x := by
  have : CompleteSpace E := FiniteDimensional.complete ℝ E
  set ψ : M → ℝ := fun x ↦ Real.smoothTransition ((b - F x) / (b - m))
  have hψ : ContMDiff I 𝓘(ℝ) 1 ψ :=
    (Real.smoothTransition.contDiff.comp ((contDiff_const.sub contDiff_id).div_const _)
      |>.comp_contMDiff hF).of_le (by norm_num)
  have hX : ContMDiff I I.tangent 1 (T% (σ.hamiltonianVectorField F)) :=
    hσ.contMDiff_hamiltonianVectorField (n := 1) (by simp) (by norm_num [hF])
  have hv := hψ.smul_section hX
  refine ⟨ψ • σ.hamiltonianVectorField F, hv,
    isCompleteVectorField_of_isCompact_of_eq_zero_off hv hcpt fun x hx ↦ ?_, fun x hx ↦ ?_,
    fun x ↦ ⟨ψ x, rfl⟩⟩
  · have hx : b < F x := not_le.1 hx
    simp only [Pi.smul_apply', ψ, Real.smoothTransition.zero_of_nonpos
      (div_nonpos_of_nonpos_of_nonneg (show b - F x ≤ 0 by linarith) (show 0 ≤ b - m by linarith)),
      zero_smul]
  · simp only [Pi.smul_apply', ψ, Real.smoothTransition.one_of_one_le
      ((one_le_div (show 0 < b - m by linarith)).2 (show b - m ≤ b - F x by linarith)), one_smul]

/-- **A regular level carries no rest points of the cut-off flow.** If `v` agrees with the
Hamiltonian vector field `X_F` on `{F ≤ m}`, `s ≤ m` is a regular value of `F`, and `x₀` lies on
the level `s`, then the orbit of `x₀` under the flow of `v` is not constant. -/
private theorem not_forall_globalFlow_eq_self (hσ : σ.IsNondegenerate) {s m : ℝ}
    (hs : IsRegularValue I 𝓘(ℝ) F s) {v : (x : M) → TangentSpace I x}
    (hv : ContMDiff I I.tangent 1 (fun x ↦ (⟨x, v x⟩ : TangentBundle I M)))
    (hcomplete : IsCompleteVectorField v) (hsm : s ≤ m)
    (hvX : ∀ x, F x ≤ m → v x = σ.hamiltonianVectorField F x) {x₀ : M} (hx₀ : F x₀ = s) :
    ¬ ∀ t, globalFlow v hv hcomplete t x₀ = x₀ := fun hfix ↦ by
  refine hσ.hamiltonianVectorField_ne_zero (hs.isRegularPoint hx₀) ?_
  -- The orbit of `x₀` is a constant integral curve of `v`, so `v x₀ = 0`.
  have h₀ := isMIntegralCurve_globalFlow hv hcomplete x₀
  rw [show (fun t ↦ globalFlow v hv hcomplete t x₀) = fun _ ↦ x₀ from funext hfix] at h₀
  rw [← hvX x₀ (hx₀.trans_le hsm)]
  exact isMIntegralCurve_const_iff.1 h₀

/-- **The levels of `F` are invariant.** `F` is constant along the flow of a complete field that is
at every point a multiple of the Hamiltonian vector field `X_F`. -/
private theorem apply_globalFlow_eq (hσ : σ.IsNondegenerate) (hF : MDifferentiable I 𝓘(ℝ) F)
    {v : (x : M) → TangentSpace I x}
    (hv : ContMDiff I I.tangent 1 (fun x ↦ (⟨x, v x⟩ : TangentBundle I M)))
    (hcomplete : IsCompleteVectorField v)
    (hvX : ∀ x, ∃ a : ℝ, v x = a • σ.hamiltonianVectorField F x) (t : ℝ) (x : M) :
    F (globalFlow v hv hcomplete t x) = F x := by
  have h := ((isMIntegralCurve_globalFlow hv hcomplete x).isMIntegralCurveOn univ)
    |>.apply_eq_of_mvfderiv_apply_eq_zero isOpen_univ isPreconnected_univ (fun u _ ↦ hF _)
      (fun u _ ↦ by
        obtain ⟨a, ha⟩ := hvX (globalFlow v hv hcomplete u x)
        rw [ha, map_smul,
          (hσ.isHamiltonianVectorField_hamiltonianVectorField F).mvfderiv_apply_self, smul_zero])
      (mem_univ 0) (mem_univ t)
  rwa [(globalFlow v hv hcomplete).map_zero_apply] at h

/-- **A closed characteristic on a limiting level.** Let `F` be `C²`, `s` a regular value of `F`
and `{F ≤ b}` compact for some `b > s`, with `{F < b} ⊆ W`. If levels of `F` arbitrarily close to
`s` carry closed characteristics, contractible in `W`, of period at most `K`, then so does the
level `s`. -/
theorem hasContractibleClosedCharacteristicOfPeriodLE_of_frequently (hσ : σ.IsNondegenerate)
    (hF : ContMDiff I 𝓘(ℝ) 2 F) {s b K : ℝ} (hsb : s < b) (hcpt : IsCompact {x | F x ≤ b})
    (hW : {x | F x < b} ⊆ W) (hs : IsRegularValue I 𝓘(ℝ) F s)
    (h : ∃ᶠ c in 𝓝 s, σ.HasContractibleClosedCharacteristicOfPeriodLE W F c K) :
    σ.HasContractibleClosedCharacteristicOfPeriodLE W F s K := by
  -- A complete field `v` agreeing with `X_F` below the level `m`, and its flow `ϕ`, which
  -- preserves the levels of `F`.
  set m := (s + b) / 2 with hm
  have hsm : s < m := by linarith
  have hmb : m < b := by linarith
  obtain ⟨v, hv, hcomplete, hvX, hvF⟩ :=
    exists_isCompleteVectorField_eq_hamiltonianVectorField hσ hF hmb hcpt
  set ϕ := globalFlow v hv hcomplete
  have hϕF (t : ℝ) (x : M) : F (ϕ t x) = F x :=
    apply_globalFlow_eq hσ (hF.mdifferentiable (by norm_num)) hv hcomplete hvF t x
  -- The levels below `m` carrying closed characteristics, as a filter at `s`, refined to an
  -- ultrafilter.
  set P := fun c ↦ σ.HasContractibleClosedCharacteristicOfPeriodLE W F c K ∧ c < m
  set l : Filter {c // P c} := comap Subtype.val (𝓝 s)
  have : l.NeBot :=
    comap_neBot_iff_frequently.2 (by simpa using h.and_eventually (eventually_lt_nhds hsm))
  set u := Ultrafilter.of l
  have hul : (u : Filter {c // P c}) ≤ l := Ultrafilter.of_le l
  have hc : Tendsto (fun c : {c // P c} ↦ (c : ℝ)) u (𝓝 s) := tendsto_comap.mono_left hul
  choose T γ hT hTK hγ hper hne hlev g hg hgγ using
    fun c : {c // P c} ↦ hasContractibleClosedCharacteristicOfPeriodLE_iff.1 c.2.1
  -- The orbits are orbits of `ϕ`, which return to their base points.
  have hϕγ (c : {c // P c}) (t : ℝ) : ϕ t (γ c 0) = γ c t :=
    globalFlow_eq_of_isMIntegralCurve hv hcomplete
      (fun t ↦ hvX (γ c t) ((hlev c t).trans_le c.2.2.le) ▸ hγ c t) t
  have hret (c : {c // P c}) : ϕ (T c) (γ c 0) = γ c 0 :=
    (hϕγ c (T c)).trans (by simpa using hper c 0)
  have hxU (c : {c // P c}) : F (γ c 0) < b := (hlev c 0).trans_lt (c.2.2.trans hmb)
  -- By compactness, the periods and base points converge along `u`.
  obtain ⟨⟨T₀, x₀⟩, -, hlim⟩ := (isCompact_Icc.prod hcpt).ultrafilter_le_nhds
    (u.map fun c ↦ (T c, γ c 0)) (le_principal_iff.2 (Ultrafilter.mem_map.2
      (univ_mem' fun c ↦ ⟨⟨(hT c).le, hTK c⟩, (hxU c).le⟩)))
  have hTlim : Tendsto T u (𝓝 T₀) := (continuous_fst.tendsto _).comp hlim
  have hxlim : Tendsto (fun c ↦ γ c 0) u (𝓝 x₀) := (continuous_snd.tendsto _).comp hlim
  -- The limit orbit lies on the level `s`, where `v = X_F` does not vanish.
  have hFx₀ : F x₀ = s :=
    tendsto_nhds_unique ((hF.continuous.tendsto _).comp hxlim) (hc.congr fun c ↦ (hlev c 0).symm)
  have hrest : ¬ ∀ t, ϕ t x₀ = x₀ :=
    not_forall_globalFlow_eq_self hσ hs hv hcomplete hsm.le hvX hFx₀
  -- The limit period is positive, since fast periodic orbits accumulate at rest points.
  have hT₀ : 0 < T₀ := by
    refine (ge_of_tendsto hTlim (Eventually.of_forall fun c ↦ (hT c).le)).lt_of_ne fun h₀ ↦
      hrest (ϕ.apply_eq_self_of_tendsto_zero hxlim (h₀ ▸ hTlim) (.of_forall hT) (.of_forall hret))
  have hfix₀ : ϕ T₀ x₀ = x₀ := ϕ.apply_eq_self_of_tendsto hxlim hTlim (.of_forall hret)
  -- Contractibility in `W` passes to the limit.
  have : StronglyLocallyContractibleSpace H := I.stronglyLocallyContractibleSpace
  have : StronglyLocallyContractibleSpace M := ChartedSpace.stronglyLocallyContractibleSpace H M
  -- The flow preserves the open sublevel set `{F < b}`, but need not preserve `W`.
  have hinv : IsInvariant ϕ {x | F x < b} := fun t y hy ↦ by
    simpa only [mem_ofPred_eq, hϕF] using hy
  obtain ⟨g₀, hg₀, hg₀x⟩ := ϕ.exists_nullhomotopic_of_tendsto_of_isInvariant
    (isOpen_lt hF.continuous continuous_const) hinv hW (.of_forall hxU) (hFx₀.trans_lt hsb) hxlim
    hTlim hT₀ hfix₀ (.of_forall hret)
    (.of_forall fun c ↦ ⟨g c, hg c, fun t ↦ (hgγ c t).trans (hϕγ c t).symm⟩)
  refine hasContractibleClosedCharacteristicOfPeriodLE_iff.2 ⟨T₀, fun t ↦ ϕ t x₀, hT₀,
    le_of_tendsto hTlim (.of_forall hTK), fun t ↦ ?_, fun t ↦ ?_, ?_,
    fun t ↦ (hϕF t x₀).trans hFx₀, g₀, hg₀, hg₀x⟩
  · rw [← hvX _ (((hϕF t x₀).trans hFx₀).trans_le hsm.le)]
    exact isMIntegralCurve_globalFlow hv hcomplete x₀ t
  · simp only [ϕ.map_add, hfix₀]
  · by_contra! hcon
    exact hrest fun t ↦ (hcon t).trans (ϕ.map_zero_apply x₀)

/-- **Contractible closed characteristics on almost every level** (Hofer–Zehnder, Struwe). Let
`F` be smooth, with compact sublevel sets `{F ≤ s}` for `s < b` and `{F < b} ⊆ W`, let every value
in `(a, b)` be attained by `F`, and let `Z ⊆ {F ≤ a}`. If the relative capacity `c°_HZ({F < b}, Z)`
in `W` is finite, then almost every regular level of `F` in `(a, b)` carries a closed characteristic
contractible in `W`. -/
theorem ae_hasContractibleClosedCharacteristic (hσ : σ.IsNondegenerate)
    (hF : ContMDiff I 𝓘(ℝ) ∞ F) {a b : ℝ} (hcpt : ∀ s < b, IsCompact {x | F x ≤ s})
    (hW : {x | F x < b} ⊆ W) (hrange : Ioo a b ⊆ range F) (hZ : Z ⊆ {x | F x ≤ a})
    (hcap : σ.relContractibleHZCapacity W {x | F x < b} Z ≠ (∞ : ℝ≥0∞)) :
    ∀ᵐ s, s ∈ Ioo a b → IsRegularValue I 𝓘(ℝ) F s →
      σ.HasContractibleClosedCharacteristic W F s := by
  filter_upwards [hσ.ae_forall_exists_hasContractibleClosedCharacteristicOfPeriodLE hF hcpt
    (by simp [ModelWithCorners.interior_eq_univ]) hrange hZ hcap] with s hs hsab hreg
  obtain ⟨K, hK⟩ := hs hsab
  refine (hσ.hasContractibleClosedCharacteristicOfPeriodLE_of_frequently (hF.of_le (by simp))
    (K := K)
    (b := (s + b) / 2) (by linarith [hsab.2]) (hcpt _ (by linarith [hsab.2]))
    (fun x hx ↦ hW (by rw [mem_ofPred_eq] at hx ⊢; linarith [hsab.2])) hreg
    (frequently_iff.2 fun hU ↦ ?_)).hasContractibleClosedCharacteristic
  obtain ⟨δ, hδ, hδU⟩ := Metric.mem_nhds_iff.1 hU
  obtain ⟨c, hc, hcK⟩ := hK (δ / 2) (half_pos hδ)
  refine ⟨c, hδU ?_, hcK⟩
  rw [Metric.mem_ball, Real.dist_eq, abs_lt]
  constructor <;> linarith [hc.1, hc.2]

/-- **Contractible almost existence from a finite relative capacity.** Under the hypotheses of
`ae_hasContractibleClosedCharacteristic`, every level of `F` in `(a, b)` has the contractible
almost existence property in `W`. This is the relative form of the Hofer–Zehnder–Struwe theorem. -/
theorem hasContractibleAlmostExistence (hσ : σ.IsNondegenerate) (hF : ContMDiff I 𝓘(ℝ) ∞ F)
    {a b : ℝ} (hcpt : ∀ s < b, IsCompact {x | F x ≤ s}) (hW : {x | F x < b} ⊆ W)
    (hrange : Ioo a b ⊆ range F) (hZ : Z ⊆ {x | F x ≤ a})
    (hcap : σ.relContractibleHZCapacity W {x | F x < b} Z ≠ (∞ : ℝ≥0∞))
    {c : ℝ} (hc : c ∈ Ioo a b) : σ.HasContractibleAlmostExistence W F c := by
  refine hasContractibleAlmostExistence_iff.2
    ⟨min (c - a) (b - c), lt_min (by linarith [hc.1]) (by linarith [hc.2]), ?_⟩
  filter_upwards [hσ.ae_hasContractibleClosedCharacteristic hF hcpt hW hrange hZ hcap]
    with s hs hsc
  refine hs ⟨?_, ?_⟩
  · linarith [hsc.1, min_le_left (c - a) (b - c)]
  · linarith [hsc.2, min_le_right (c - a) (b - c)]

/-- **Finite capacity implies contractible almost existence** (Barraud–Damian–Humilière–Oancea,
Proposition 6.3, after Hofer–Zehnder and Struwe). Let the model `I` be boundaryless and `σ`
nondegenerate, let `W ⊆ M` have finite `π₁`-sensitive Hofer–Zehnder capacity `c°_HZ(W)`, and let
`F` be smooth. Every nonempty regular level `F⁻¹(c)` such that, for some `b > c`, `{F ≤ b}` is
compact and `{F < b}` lies in `W`, has the contractible almost existence property in `W`. For
`W = M` this is almost existence in the whole manifold. -/
theorem hasContractibleAlmostExistence_of_contractibleHZCapacity_ne_top [I.Boundaryless]
    (hσ : σ.IsNondegenerate) (hF : ContMDiff I 𝓘(ℝ) ∞ F)
    (hcap : σ.contractibleHZCapacity W ≠ (∞ : ℝ≥0∞)) {b c : ℝ} (hcb : c < b)
    (hcpt : IsCompact {x | F x ≤ b}) (hW : {x | F x < b} ⊆ W)
    (hreg : IsRegularValue I 𝓘(ℝ) F c) (hne : ∃ x, F x = c) :
    σ.HasContractibleAlmostExistence W F c := by
  -- `F` is open at a point of the regular level, so its range contains a neighbourhood of `c`.
  obtain ⟨x, hx⟩ := hne
  have hrange : range F ∈ 𝓝 c := by
    rw [← hx, ← (hreg.isRegularPoint hx).map_nhds_eq (hF x) (by simp)]
    exact mem_of_superset (image_mem_map univ_mem) (image_subset_range F univ)
  obtain ⟨ε, hε, hεr⟩ := Metric.mem_nhds_iff.1 hrange
  set ε' := min ε (b - c)
  have hε' : 0 < ε' := lt_min hε (sub_pos.2 hcb)
  have hε'ε : ε' ≤ ε := min_le_left _ _
  have hε'b : ε' ≤ b - c := min_le_right _ _
  have hball : Ioo (c - ε') (c + ε') ⊆ range F := fun r hr ↦ hεr (by
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [hr.1, hr.2])
  -- Apply the relative theorem on `(c - ε' / 2, c + ε')` with `Z = {F < c - ε' / 2}`.
  obtain ⟨y, hy⟩ := hball (show c - 3 * ε' / 4 ∈ Ioo (c - ε') (c + ε') from
    ⟨by linarith, by linarith⟩)
  have hWc : {x | F x < c + ε'} ⊆ W := fun z hz ↦ hW (by rw [mem_ofPred_eq] at hz ⊢; linarith)
  refine hσ.hasContractibleAlmostExistence hF
    (a := c - ε' / 2) (b := c + ε') (Z := {y | F y < c - ε' / 2})
    (fun s hs ↦ hcpt.of_isClosed_subset (isClosed_le hF.continuous continuous_const)
      fun z hz ↦ by rw [mem_ofPred_eq] at hz ⊢; linarith) hWc
    ((Ioo_subset_Ioo_left (by linarith)).trans hball)
    (fun _ hz ↦ by rw [mem_ofPred_eq] at hz ⊢; exact hz.le)
    (ne_top_of_le_ne_top hcap (relContractibleHZCapacity_le_contractibleHZCapacity hWc
      ⟨y, mem_interior_iff_mem_nhds.2 <| (isOpen_lt hF.continuous continuous_const).mem_nhds
        (by rw [mem_ofPred_eq]; linarith)⟩))
    ⟨by linarith, by linarith⟩

end IsNondegenerate

end SmoothTwoForm

end TauCeti
