/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Topology.Connected.Basic
public import Mathlib.Topology.Instances.AddCircle.Defs
public import TauCeti.GroupTheory.GroupAction.SubMulAction
public import TauCeti.Geometry.Manifold.Instances.NonzeroVectors
public import TauCeti.Geometry.Manifold.Instances.Quotient
public import TauCeti.Topology.Compactness.LocallyCompact
import Mathlib.Analysis.Normed.Module.Ball.RadialEquiv
import Mathlib.Topology.Instances.ZMultiples
import TauCeti.Analysis.Normed.Field.ZPowers

/-!
# Hopf manifolds

For a unit `c` of a nontrivially normed field `𝕜` and a normed space `E` over `𝕜`, the
**Hopf manifold** `TauCeti.HopfManifold E c` is the orbit space of the nonzero vectors of `E` under
the group `⟨c⟩ = Subgroup.zpowers c` of dilations `v ↦ cᵏ v`, `k ∈ ℤ`. The group acts through
Mathlib's action of `𝕜ˣ` on nonzero vectors, by analytic maps
(`TauCeti.instContMDiffConstSMulSubgroupNonZero`) and freely (`Units.isCancelSMul_nonZero`).

When `‖c‖ ≠ 1` the action is properly discontinuous
(`TauCeti.HopfManifold.instProperlyDiscontinuousSMul`): `log ‖cᵏ v‖ - log ‖v‖ = k log ‖c‖`, so
only finitely many dilations move a compact set of nonzero vectors to meet another one. Hence, for
nontrivial locally compact `E`, `TauCeti.instIsManifoldQuotient` makes the Hopf manifold a
Hausdorff analytic manifold modelled on `E`, with the orbit projection `TauCeti.HopfManifold.mk`
an analytic local diffeomorphism. If `E` is proper, for instance finite-dimensional over `ℝ` or
`ℂ`, the Hopf manifold is compact: every orbit meets the closed annulus `1 ≤ ‖v‖ ≤ ‖c‖` when
`1 < ‖c‖` (`Units.exists_zpow_smul_mem_annulus`).

The hypothesis `‖c‖ ≠ 1` cannot be dropped. If `‖c‖ = 1` the dilations preserve the norm, which
then descends to an unbounded continuous function on the quotient, so the quotient is not compact;
if moreover `c` has infinite order, such as `c = exp i` in `ℂ`, the action is not properly
discontinuous. The hypothesis is supplied to instance search as `Fact (‖(c : 𝕜)‖ ≠ 1)`.

For a real dilation factor `r > 1`, polar coordinates `[v] ↦ (log ‖v‖ mod log r, v / ‖v‖)`
identify the Hopf manifold of a proper real or complex normed space `E` with the product of the
circle `ℝ / (log r) ℤ` and the unit sphere of `E`
(`TauCeti.HopfManifold.homeomorphAddCircleProdSphere`). Over `𝕜 = ℂ` the Hopf manifold of a
nontrivial `E` is connected. So with `E = ℂⁿ` and `‖c‖ ≠ 1` it is a compact connected complex
manifold of dimension `n`, and for a real factor `c = r > 1` it is homeomorphic to `S¹ × S²ⁿ⁻¹`.
For other `c` this homeomorphism is not proved here.

The **primary Hopf surface** `TauCeti.HopfSurface` is the case `E = ℂ²`, `c = 2`. It is the
standard example of a compact complex surface that is not Kähler: its first Betti number `1` is
odd, and its Hodge numbers `h^(1,0) = 0` and `h^(0,1) = 1` differ. This file constructs the surface
and its topology; those cohomological invariants are not computed here.

## Main definitions

* `TauCeti.HopfManifold E c`: the orbit space of the nonzero vectors of `E` under `⟨c⟩`.
* `TauCeti.HopfManifold.mk`: the orbit projection.
* `TauCeti.HopfManifold.homeomorphAddCircleProdSphere`: for a real dilation factor `r > 1`, the
  homeomorphism with the product of a circle and the unit sphere.
* `TauCeti.HopfSurface`: the primary Hopf surface `(ℂ² ∖ {0}) / (z ↦ 2z)`.

## Main results

* `TauCeti.HopfManifold.instProperlyDiscontinuousSMul`: for `‖c‖ ≠ 1` the dilations act properly
  discontinuously on the nonzero vectors.
* `TauCeti.HopfManifold.mk_eq_mk_iff`: two nonzero vectors have the same image exactly when they
  differ by a power of `c`.
* `TauCeti.HopfManifold.isLocalDiffeomorph_mk`, `TauCeti.HopfManifold.mdifferentiable_mk`: the
  orbit projection is an analytic local diffeomorphism; over `ℂ` it is a local biholomorphism.
* `TauCeti.HopfManifold.instCompactSpace`: for proper `E` the Hopf manifold is compact.
* `TauCeti.HopfManifold.instConnectedSpace`: over `ℂ` it is connected.
* `TauCeti.HopfSurface.homeomorphAddCircleProdSphere`: the primary Hopf surface is homeomorphic
  to `S¹ × S³`.

## References

* H. Hopf, *Zur Topologie der komplexen Mannigfaltigkeiten*, Studies and Essays presented to
  R. Courant, Interscience, 1948, 167–185.
* D. Huybrechts, *Complex Geometry: An Introduction*, Springer, 2005, Example 2.1.4 (the Hopf
  manifold `(ℂⁿ ∖ {0}) / ℤ` as a compact complex manifold diffeomorphic to `S¹ × S²ⁿ⁻¹`).
* J.-P. Demailly, *Complex Analytic and Differential Geometry*, Chapter VI, (4.7) (the Hopf
  surface is not Kähler).
-/

public noncomputable section

open Set Filter Topology Metric
open scoped Manifold ContDiff

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E]

variable (E) in
/-- The **Hopf manifold** of `E` and a unit `c` of `𝕜`: the orbit space of the nonzero vectors
of `E` under the group `⟨c⟩ = Subgroup.zpowers c` of dilations `v ↦ cᵏ v`. For `‖c‖ ≠ 1` and
nontrivial locally compact `E` it is an analytic manifold modelled on `E`; for `E = ℂⁿ` it is a
compact complex manifold. -/
abbrev HopfManifold (c : 𝕜ˣ) : Type _ :=
  MulAction.orbitRel.Quotient (Subgroup.zpowers c) {v : E // v ≠ 0}

namespace HopfManifold

variable {c : 𝕜ˣ}

/-- For `‖c‖ ≠ 1` the powers of `c` act properly discontinuously on the nonzero vectors: only
finitely many of them move a compact set of nonzero vectors to meet another compact set. -/
instance instProperlyDiscontinuousSMul [Fact (‖(c : 𝕜)‖ ≠ 1)] :
    ProperlyDiscontinuousSMul (Subgroup.zpowers c) {v : E // v ≠ 0} where
  finite_disjoint_inter_image {K L} hK hL := by
    obtain ⟨d, hd, hdc⟩ := exists_one_lt_norm_zpowers_eq (Fact.out : ‖(c : 𝕜)‖ ≠ 1)
    -- The logarithmic ratio of norms is continuous, so it is bounded on `L × K`.
    let ψ : {v : E // v ≠ 0} × {v : E // v ≠ 0} → ℝ :=
      fun p ↦ Real.log ‖(p.1 : E)‖ - Real.log ‖(p.2 : E)‖
    have hψ : Continuous ψ := by
      refine .sub (.log (by fun_prop) fun p ↦ norm_ne_zero_iff.mpr p.1.property)
        (.log (by fun_prop) fun p ↦ norm_ne_zero_iff.mpr p.2.property)
    obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp ((hL.prod hK).image hψ).isBounded
    have hlog : 0 < Real.log ‖(d : 𝕜)‖ := Real.log_pos hd
    let φ : ℤ → Subgroup.zpowers c := fun k ↦ ⟨d ^ k, hdc ▸ zpow_mem (Subgroup.mem_zpowers d) k⟩
    -- Only finitely many integers `k` have `|k log ‖d‖| ≤ C`.
    have hfin : {k : ℤ | (k : ℝ) ∈ closedBall 0 (C / Real.log ‖(d : 𝕜)‖)}.Finite :=
      tendsto_cofinite_cocompact_iff.mp Int.tendsto_coe_cofinite _ (isCompact_closedBall _ _)
    refine (hfin.image φ).subset fun g hg ↦ ?_
    obtain ⟨_, ⟨v, hv, rfl⟩, hgv⟩ := hg
    obtain ⟨k, hk⟩ :=
      Subgroup.mem_zpowers_iff.mp (hdc.symm ▸ g.property : (g : 𝕜ˣ) ∈ Subgroup.zpowers d)
    refine ⟨k, ?_, Subtype.ext hk⟩
    have hnorm : ‖((g • v : {v : E // v ≠ 0}) : E)‖ = ‖(d : 𝕜)‖ ^ k * ‖(v : E)‖ := by
      rw [Subgroup.smul_def, ← hk, Units.norm_coe_zpow_smul]
    have hψv : ψ (g • v, v) = k * Real.log ‖(d : 𝕜)‖ := by
      simp only [ψ, hnorm]
      rw [Real.log_mul (zpow_ne_zero _ (by positivity)) (norm_ne_zero_iff.mpr v.property),
        Real.log_zpow]
      ring
    have hCk := hC _ ⟨(g • v, v), ⟨hgv, hv⟩, rfl⟩
    rw [hψv, Real.norm_eq_abs, abs_mul, abs_of_pos hlog, ← le_div_iff₀ hlog] at hCk
    simpa using hCk

variable (E c) in
/-- The orbit projection from the nonzero vectors of `E` onto the Hopf manifold. -/
abbrev mk : {v : E // v ≠ 0} → HopfManifold E c := Quotient.mk _

/-- Every point of the Hopf manifold is the image of a nonzero vector. -/
theorem mk_surjective : Function.Surjective (mk E c) := Quotient.mk_surjective

/-- Two nonzero vectors have the same image in the Hopf manifold exactly when they differ by a
power of `c`. -/
theorem mk_eq_mk_iff {v w : {v : E // v ≠ 0}} : mk E c v = mk E c w ↔ ∃ k : ℤ, c ^ k • w = v := by
  rw [mk, Quotient.eq, MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨⟨g, hg⟩, rfl⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    exact ⟨k, rfl⟩
  · rintro ⟨k, rfl⟩
    exact ⟨⟨c ^ k, zpow_mem (Subgroup.mem_zpowers c) k⟩, rfl⟩

/-- Dilating a nonzero vector by a power of `c` does not change its image in the Hopf
manifold. -/
@[simp]
theorem mk_zpow_smul (k : ℤ) (v : {v : E // v ≠ 0}) : mk E c (c ^ k • v) = mk E c v :=
  mk_eq_mk_iff.mpr ⟨k, rfl⟩

/-- Dilating a nonzero vector by `c` does not change its image in the Hopf manifold. -/
@[simp]
theorem mk_smul (v : {v : E // v ≠ 0}) : mk E c (c • v) = mk E c v := by
  simpa using mk_zpow_smul (c := c) 1 v

/-- The orbit projection is continuous. -/
@[fun_prop]
theorem continuous_mk : Continuous (mk E c) := continuous_quot_mk

variable [Nontrivial E] [LocallyCompactSpace E] [Fact (‖(c : 𝕜)‖ ≠ 1)]

/-- The orbit projection onto the Hopf manifold is an analytic local diffeomorphism. -/
theorem isLocalDiffeomorph_mk {n : ℕ∞ω} : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) n (mk E c) :=
  isLocalDiffeomorph_quotientMk

/-- The orbit projection onto the Hopf manifold is differentiable; over `ℂ` it is holomorphic. -/
theorem mdifferentiable_mk : MDifferentiable 𝓘(𝕜, E) 𝓘(𝕜, E) (mk E c) :=
  (isLocalDiffeomorph_mk (n := 1)).contMDiff.mdifferentiable one_ne_zero

omit [Nontrivial E] [LocallyCompactSpace E] [Fact (‖(c : 𝕜)‖ ≠ 1)] in
/-- The Hopf manifold of a second-countable space is second countable. -/
instance instSecondCountableTopology [SecondCountableTopology E] :
    SecondCountableTopology (HopfManifold E c) :=
  ContinuousConstSMul.secondCountableTopology

omit [Nontrivial E] [LocallyCompactSpace E] in
/-- For proper `E`, for instance finite-dimensional `E` over `ℝ` or `ℂ`, the Hopf manifold is
compact: it is the image of a closed annulus. -/
instance instCompactSpace [ProperSpace E] : CompactSpace (HopfManifold E c) := by
  obtain ⟨d, hd, hdc⟩ := exists_one_lt_norm_zpowers_eq (Fact.out : ‖(c : 𝕜)‖ ≠ 1)
  let A : Set {v : E // v ≠ 0} := {v | 1 ≤ ‖(v : E)‖ ∧ ‖(v : E)‖ ≤ ‖(d : 𝕜)‖}
  have hA : IsCompact A := by
    have himage : Subtype.val '' A = {v : E | 1 ≤ ‖v‖} ∩ closedBall 0 ‖(d : 𝕜)‖ := by
      ext v
      simp only [A, mem_image, mem_inter_iff, mem_closedBall, dist_zero_right]
      refine ⟨?_, fun hv ↦ ⟨⟨v, norm_pos_iff.mp (one_pos.trans_le hv.1)⟩, hv, rfl⟩⟩
      rintro ⟨w, hw, rfl⟩
      exact hw
    rw [Subtype.isCompact_iff, himage]
    exact (isCompact_closedBall 0 _).inter_left (isClosed_le continuous_const continuous_norm)
  have hA' : mk E c '' A = univ := eq_univ_of_forall fun x ↦ by
    obtain ⟨v, rfl⟩ := mk_surjective x
    obtain ⟨k, hk₁, hk₂⟩ := Units.exists_zpow_smul_mem_annulus hd v
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (hdc ▸ zpow_mem (Subgroup.mem_zpowers d) k)
    exact ⟨d ^ k • v, ⟨hk₁, hk₂⟩, mk_eq_mk_iff.mpr ⟨j, by rw [hj]⟩⟩
  exact ⟨hA' ▸ hA.image continuous_mk⟩

omit [Nontrivial E] [LocallyCompactSpace E] [Fact (‖(c : 𝕜)‖ ≠ 1)] in
/-- The Hopf manifold of a space whose nonzero vectors are connected, for instance a nontrivial
complex normed space, is connected. -/
instance instConnectedSpace [ConnectedSpace {v : E // v ≠ 0}] :
    ConnectedSpace (HopfManifold E c) :=
  inferInstanceAs (ConnectedSpace (Quotient _))

end HopfManifold

namespace HopfManifold

section Polar

/-! ### Polar coordinates for a real dilation factor

For a real dilation factor `r > 1`, a nonzero vector `v` is determined by its direction
`v / ‖v‖` and the logarithm of its norm, and the dilation by `r` only translates `log ‖v‖` by
`log r`. So the Hopf manifold is the product of the circle `ℝ / (log r) ℤ` and the unit sphere.
Here `𝕜` is a normed `ℝ`-algebra, such as `ℝ` or `ℂ`, and `c` is the image of `r` in `𝕜`. -/

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedAlgebra ℝ 𝕜] {E : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] {c : 𝕜ˣ}
  {r : ℝ}

/-- The polar coordinates `(log ‖v‖ mod log r, v / ‖v‖)` of a nonzero vector, read off from
Mathlib's polar homeomorphism `homeomorphUnitSphereProd`. -/
private def polar (r : ℝ) (v : {v : E // v ≠ 0}) : AddCircle (Real.log r) × sphere (0 : E) 1 :=
  let p := homeomorphUnitSphereProd E ⟨v, v.property⟩
  ((Real.log p.2 : AddCircle (Real.log r)), p.1)

private theorem polar_fst (v : {v : E // v ≠ 0}) :
    (polar r v).1 = (Real.log ‖(v : E)‖ : AddCircle (Real.log r)) := by
  simp [polar]

private theorem coe_polar_snd (v : {v : E // v ≠ 0}) :
    ((polar r v).2 : E) = ‖(v : E)‖⁻¹ • (v : E) := by
  simp [polar]

private theorem continuous_polar : Continuous (polar (E := E) r) := by
  have h := (homeomorphUnitSphereProd E).continuous.comp
    (continuous_subtypeVal.subtype_mk fun v : {v : E // v ≠ 0} ↦ v.property)
  exact .prodMk ((AddCircle.continuous_mk' _).comp ((continuous_subtypeVal.comp h.snd).log
    fun v ↦ (homeomorphUnitSphereProd E ⟨v, v.property⟩).2.property.out.ne')) h.fst

private theorem polar_zpow_smul (hr : 0 < r) (hc : (c : 𝕜) = algebraMap ℝ 𝕜 r) (k : ℤ)
    (v : {v : E // v ≠ 0}) : polar r (c ^ k • v) = polar r v := by
  have hv : ‖(v : E)‖ ≠ 0 := norm_ne_zero_iff.mpr v.property
  have hrk : 0 < r ^ k := zpow_pos hr k
  have hnorm : ‖((c ^ k • v : {v : E // v ≠ 0}) : E)‖ = r ^ k * ‖(v : E)‖ := by
    rw [Units.coe_zpow_smul_of_eq_algebraMap hc, norm_smul, Real.norm_of_nonneg hrk.le]
  refine Prod.ext ?_ (Subtype.ext ?_)
  · simp only [polar_fst, hnorm]
    rw [Real.log_mul hrk.ne' hv, Real.log_zpow, AddCircle.coe_add, add_eq_right,
      AddCircle.coe_eq_zero_iff]
    exact ⟨k, zsmul_eq_mul _ _⟩
  · simp only [coe_polar_snd, Units.coe_zpow_smul_of_eq_algebraMap hc, smul_smul, norm_smul,
      Real.norm_of_nonneg hrk.le]
    congr 1
    field_simp

/-- Nonzero vectors with the same polar coordinates differ by a power of the dilation. -/
private theorem exists_zpow_smul_eq_of_polar_eq (hr : 1 < r) (hc : (c : 𝕜) = algebraMap ℝ 𝕜 r)
    {v w : {v : E // v ≠ 0}} (h : polar r v = polar r w) : ∃ k : ℤ, c ^ k • w = v := by
  have hv : 0 < ‖(v : E)‖ := norm_pos_iff.mpr v.property
  have hw : 0 < ‖(w : E)‖ := norm_pos_iff.mpr w.property
  obtain ⟨h₁, h₂⟩ := Prod.ext_iff.mp h
  obtain ⟨k, hk⟩ := (AddCircle.coe_eq_zero_iff (p := Real.log r)
    (x := Real.log ‖(v : E)‖ - Real.log ‖(w : E)‖)).mp
      (by rw [AddCircle.coe_sub, sub_eq_zero, ← polar_fst, ← polar_fst]; exact h₁)
  have hrk : 0 < r ^ k := zpow_pos (one_pos.trans hr) k
  -- The norms differ by the factor `r ^ k`.
  have hnorm : ‖(v : E)‖ = r ^ k * ‖(w : E)‖ := by
    refine Real.log_injOn_pos hv (mul_pos hrk hw) ?_
    rw [Real.log_mul hrk.ne' hw.ne', Real.log_zpow, ← zsmul_eq_mul, hk, sub_add_cancel]
  -- The directions agree, so the vectors differ by the same factor.
  have hdir : ‖(v : E)‖⁻¹ • (v : E) = ‖(w : E)‖⁻¹ • (w : E) := by
    rw [← coe_polar_snd (r := r), ← coe_polar_snd (r := r), h₂]
  refine ⟨k, Subtype.ext ?_⟩
  rw [Units.coe_zpow_smul_of_eq_algebraMap hc, ← smul_inv_smul₀ hv.ne' (v : E), hdir, smul_smul,
    hnorm, mul_inv_cancel_right₀ hw.ne']

private theorem surjective_polar : Function.Surjective (polar (E := E) r) := by
  rintro ⟨θ, u⟩
  obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective θ
  obtain ⟨v, hv⟩ := (homeomorphUnitSphereProd E).surjective (u, ⟨Real.exp t, Real.exp_pos t⟩)
  refine ⟨⟨v, v.property⟩, ?_⟩
  simp only [polar]
  rw [hv, Real.log_exp]

variable [ProperSpace E]

/-- For a real dilation factor `r > 1`, the Hopf manifold of a proper space `E`, such as a
finite-dimensional real or complex space, is homeomorphic to the product of the circle
`ℝ / (log r) ℤ` and the unit sphere of `E`, by `[v] ↦ (log ‖v‖ mod log r, v / ‖v‖)`. For
`E = ℂⁿ` this is `S¹ × S²ⁿ⁻¹`. -/
def homeomorphAddCircleProdSphere (hr : 1 < r) (hc : (c : 𝕜) = algebraMap ℝ 𝕜 r) :
    HopfManifold E c ≃ₜ AddCircle (Real.log r) × sphere (0 : E) 1 :=
  haveI : Fact (‖(c : 𝕜)‖ ≠ 1) :=
    ⟨by rw [hc, norm_algebraMap', Real.norm_of_nonneg (one_pos.trans hr).le]; exact hr.ne'⟩
  let f : HopfManifold E c → AddCircle (Real.log r) × sphere (0 : E) 1 :=
    Quotient.lift (polar r) fun v w h ↦ by
      obtain ⟨k, hk⟩ := mk_eq_mk_iff.mp (Quotient.sound h : mk E c v = mk E c w)
      rw [← hk, polar_zpow_smul (one_pos.trans hr) hc]
  have hf : Function.Bijective f := by
    refine ⟨fun x y hxy ↦ ?_, fun p ↦ ?_⟩
    · obtain ⟨v, rfl⟩ := mk_surjective x
      obtain ⟨w, rfl⟩ := mk_surjective y
      exact mk_eq_mk_iff.mpr (exists_zpow_smul_eq_of_polar_eq hr hc hxy)
    · obtain ⟨v, hv⟩ := surjective_polar p
      exact ⟨mk E c v, hv⟩
  Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective f hf)
    (continuous_quot_lift _ continuous_polar)

/-- The homeomorphism sends `[v]` to the polar coordinates of `v`. This holds by definition:
`Continuous.homeoOfEquivCompactToT2` and `Equiv.ofBijective` apply the underlying function, and
`Quotient.lift` computes on a class. -/
private theorem homeomorphAddCircleProdSphere_mk (hr : 1 < r)
    (hc : (c : 𝕜) = algebraMap ℝ 𝕜 r) (v : {v : E // v ≠ 0}) :
    homeomorphAddCircleProdSphere hr hc (mk E c v) = polar r v :=
  rfl

/-- The circle coordinate of the image of `[v]` is `log ‖v‖`. -/
@[simp]
theorem homeomorphAddCircleProdSphere_mk_fst (hr : 1 < r) (hc : (c : 𝕜) = algebraMap ℝ 𝕜 r)
    (v : {v : E // v ≠ 0}) :
    (homeomorphAddCircleProdSphere hr hc (mk E c v)).1 = (Real.log ‖(v : E)‖ : AddCircle _) := by
  rw [homeomorphAddCircleProdSphere_mk, polar_fst]

/-- The sphere coordinate of the image of `[v]` is `v / ‖v‖`. -/
@[simp]
theorem coe_homeomorphAddCircleProdSphere_mk_snd (hr : 1 < r) (hc : (c : 𝕜) = algebraMap ℝ 𝕜 r)
    (v : {v : E // v ≠ 0}) :
    ((homeomorphAddCircleProdSphere hr hc (mk E c v)).2 : E) = ‖(v : E)‖⁻¹ • (v : E) := by
  rw [homeomorphAddCircleProdSphere_mk, coe_polar_snd]

/-- The inverse polar map sends `(t mod log r, u)` to the class of `exp t • u`. -/
@[simp]
theorem homeomorphAddCircleProdSphere_symm_apply (hr : 1 < r)
    (hc : (c : 𝕜) = algebraMap ℝ 𝕜 r) (t : ℝ) (u : sphere (0 : E) 1) :
    (homeomorphAddCircleProdSphere hr hc).symm ((t : AddCircle (Real.log r)), u) =
      mk E c ⟨Real.exp t • (u : E),
        smul_ne_zero (Real.exp_ne_zero t) (ne_zero_of_mem_unit_sphere u)⟩ := by
  have hu : ‖(u : E)‖ = 1 := mem_sphere_zero_iff_norm.mp u.property
  have hnorm : ‖Real.exp t • (u : E)‖ = Real.exp t := by
    rw [norm_smul, hu, mul_one, Real.norm_of_nonneg (Real.exp_nonneg t)]
  rw [Homeomorph.symm_apply_eq]
  refine Prod.ext ?_ (Subtype.ext ?_)
  · rw [homeomorphAddCircleProdSphere_mk_fst, hnorm, Real.log_exp]
  · rw [coe_homeomorphAddCircleProdSphere_mk_snd, hnorm, smul_smul,
      inv_mul_cancel₀ (Real.exp_ne_zero t), one_smul]

end Polar

end HopfManifold

/-- The **primary Hopf surface** `(ℂ² ∖ {0}) / (z ↦ 2z)`, the Hopf manifold of
`EuclideanSpace ℂ (Fin 2)` and the dilation by `2`. It is a compact connected complex surface,
homeomorphic to `S¹ × S³` (`TauCeti.HopfSurface.homeomorphAddCircleProdSphere`). -/
abbrev HopfSurface : Type :=
  HopfManifold (EuclideanSpace ℂ (Fin 2)) (Units.mk0 (2 : ℂ) two_ne_zero)

/-- The dilation factor `2` of the primary Hopf surface does not have norm one. -/
instance HopfSurface.instFactNormNeOne : Fact (‖((Units.mk0 (2 : ℂ) two_ne_zero : ℂˣ) : ℂ)‖ ≠ 1) :=
  ⟨by norm_num⟩

/-- The primary Hopf surface is homeomorphic to `S¹ × S³`, the product of the circle
`ℝ / (log 2) ℤ` and the unit sphere of `ℂ²`, by `[z] ↦ (log ‖z‖ mod log 2, z / ‖z‖)`. -/
def HopfSurface.homeomorphAddCircleProdSphere :
    HopfSurface ≃ₜ AddCircle (Real.log 2) × sphere (0 : EuclideanSpace ℂ (Fin 2)) 1 :=
  HopfManifold.homeomorphAddCircleProdSphere one_lt_two (by simp [map_ofNat])

/-- The circle coordinate of the image of `[z]` in `S¹ × S³` is `log ‖z‖`. -/
@[simp]
theorem HopfSurface.homeomorphAddCircleProdSphere_mk_fst
    (v : {v : EuclideanSpace ℂ (Fin 2) // v ≠ 0}) :
    (HopfSurface.homeomorphAddCircleProdSphere (HopfManifold.mk _ _ v)).1 =
      (Real.log ‖(v : EuclideanSpace ℂ (Fin 2))‖ : AddCircle (Real.log 2)) :=
  HopfManifold.homeomorphAddCircleProdSphere_mk_fst _ _ v

/-- The sphere coordinate of the image of `[z]` in `S¹ × S³` is `z / ‖z‖`. -/
@[simp]
theorem HopfSurface.coe_homeomorphAddCircleProdSphere_mk_snd
    (v : {v : EuclideanSpace ℂ (Fin 2) // v ≠ 0}) :
    ((HopfSurface.homeomorphAddCircleProdSphere (HopfManifold.mk _ _ v)).2 :
        EuclideanSpace ℂ (Fin 2)) =
      ‖(v : EuclideanSpace ℂ (Fin 2))‖⁻¹ • (v : EuclideanSpace ℂ (Fin 2)) :=
  HopfManifold.coe_homeomorphAddCircleProdSphere_mk_snd _ _ v

/-- The inverse map sends `(t mod log 2, u)` in `S¹ × S³` to the class of `exp t • u`. -/
@[simp]
theorem HopfSurface.homeomorphAddCircleProdSphere_symm_apply (t : ℝ)
    (u : sphere (0 : EuclideanSpace ℂ (Fin 2)) 1) :
    HopfSurface.homeomorphAddCircleProdSphere.symm ((t : AddCircle (Real.log 2)), u) =
      HopfManifold.mk _ _ ⟨Real.exp t • (u : EuclideanSpace ℂ (Fin 2)),
        smul_ne_zero (Real.exp_ne_zero t) (ne_zero_of_mem_unit_sphere u)⟩ :=
  HopfManifold.homeomorphAddCircleProdSphere_symm_apply _ _ t u

end TauCeti
