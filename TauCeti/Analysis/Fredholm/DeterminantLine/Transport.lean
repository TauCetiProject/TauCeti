/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Ray
public import Mathlib.Order.Interval.Set.UnorderedInterval
public import TauCeti.Analysis.Fredholm.DeterminantLine.Chart
import Mathlib.Topology.Order.IntermediateValue
import TauCeti.Analysis.Fredholm.Stabilization
import TauCeti.LinearAlgebra.Ray

/-!
# Transport of orientations of Fredholm determinant lines

Let `T : X → E →L[ℝ] F` be a continuous family of operators between real Banach spaces. At a
Fredholm member the determinant line `det (ker T x) ⊗ (det (F ⧸ range T x))^*` is a real line,
but kernel and cokernel jump with `x`, so the lines of the family are compared through the kernel
charts of `ContinuousLinearMap.detLineChartEquiv`: a stabilizer `D₂` and a kernel coordinate `q`
with `((T x).coprod D₂).prod q` invertible identify the determinant line of `T x` with one fixed
line, for all `x` near a given parameter. Transitions between kernel charts are continuous and
nowhere zero (`ContinuousLinearMap.exists_continuous_detLineChartEquiv_symm_eq_smul`).

A family `v x` of elements of the determinant lines is **coherent** at `x₀` within `s`
(`TauCeti.IsDetLineCoherentWithinAt`) if `v x₀ ≠ 0` and some kernel chart valid at `x₀` reads `v x`,
for `x ∈ s` near `x₀`, as a nonnegative (possibly zero) multiple of its reading of `v x₀`. A
family is **coherent on `s`** (`TauCeti.IsDetLineCoherentOn`) if it is coherent within `s` at every
point of `s`. It is then nonzero at every point of `s`, so the nearby multiples are positive: a
family coherent on `s` is a continuous section of the determinant line bundle over `s` up to
rescaling by positive functions, that is, a continuous orientation of the determinant lines over
`s`. The transition between two kernel charts valid at `x₀` is, at `x` near `x₀`, a scalar multiple
of the same transition at `x₀`, with a coefficient which depends continuously on `x` and equals `1`
at `x₀`, hence is positive nearby (`ContinuousLinearMap.eventually_detLineChartEquiv_symm_eq_smul`).
So the condition holds for every kernel chart valid at `x₀` as soon as it holds for one
(`TauCeti.IsDetLineCoherentWithinAt.eventually_sameRay`).

* **Uniqueness.** Two coherent families on a preconnected set that lie on the same ray at one point
  lie on the same ray everywhere (`TauCeti.IsDetLineCoherentOn.sameRay`). The set where they agree
  up to positive scaling is open and closed, because both are read in one kernel chart near each
  point.
* **Existence along intervals.** If `T : ℝ → E →L[ℝ] F` is continuous and Fredholm on `[p, q]`,
  every nonzero element of the determinant line at any `x₀ ∈ [p, q]` extends to a coherent family
  on `[p, q]` (`TauCeti.exists_isDetLineCoherentOn_Icc`). The set of `t` for which a coherent family
  exists on `[p, t]` is open and closed in `[p, q]`: a family on `[p, u]` is continued past `u` by
  holding its reading constant in a kernel chart valid near `u`.

Together these give the **transport of orientations** along a path of Fredholm operators which is
continuous on the interval `[[a, b]]` of transport (`TauCeti.detLineOrientationTransport`): the
orientation of the determinant line of `T a` given by `v₀ ≠ 0` is carried to the orientation of
`T b` given by `v b`, for the coherent family `v` on `[[a, b]]` with `v a = v₀`. It is
characterized by `TauCeti.detLineOrientationTransport_rayOfNeZero` and satisfies the identity
(`TauCeti.detLineOrientationTransport_self`), reversal
(`TauCeti.detLineOrientationTransport_symm`) and concatenation
(`TauCeti.detLineOrientationTransport_trans`) laws, and is the identity along a constant path
(`TauCeti.detLineOrientationTransport_const`). Since the negative of a coherent family is coherent
(`TauCeti.IsDetLineCoherentOn.neg`), the opposite orientation is transported to the opposite
orientation (`TauCeti.detLineOrientationTransport_neg`). Only orientations are transported: a line
bundle carries no canonical linear isomorphism between distant fibres, and none is constructed
here.

This is how the determinant lines of linearized operators are oriented: an orientation fixed at a
reference operator, for instance the complex orientation of a complex-linear operator
(`TauCeti.IsComplexPositiveTMulDual`), is transported along a path of Fredholm operators to the
operator of interest.

## Main definitions

* `TauCeti.IsDetLineCoherentWithinAt T v s x₀`: the family `v` of elements of the determinant
  lines is coherent at `x₀` within `s`, nonzero at `x₀` and read in a kernel chart, nearby, as
  nonnegative multiples of its reading at `x₀`.
* `TauCeti.IsDetLineCoherentOn T v s`: `v` is coherent at every point of `s`; it is a continuous
  orientation of the determinant lines over `s`.
* `TauCeti.detLineOrientationTransport`: the transport of orientations of determinant lines along
  a continuous path of Fredholm operators.

## Main results

* `TauCeti.IsDetLineCoherentWithinAt.eventually_sameRay`: coherence holds in every kernel chart.
* `TauCeti.IsDetLineCoherentOn.sameRay`: uniqueness on preconnected sets.
* `TauCeti.exists_isDetLineCoherentOn_Icc`: existence along a compact interval.
* `TauCeti.detLineOrientationTransport_rayOfNeZero`: orientation transport follows coherent
  families.
* `TauCeti.detLineOrientationTransport_self`, `TauCeti.detLineOrientationTransport_symm`,
  `TauCeti.detLineOrientationTransport_trans`, `TauCeti.detLineOrientationTransport_neg`,
  `TauCeti.detLineOrientationTransport_const`: the laws of orientation transport.

## References

* D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  AMS Colloquium Publications 52, 2012, Section A.2 (determinant line bundles).
* A. Zinger, *The determinant line bundle for Fredholm operators: construction, properties, and
  classification*, Math. Scand. 118 (2016), 203–268, arXiv:1304.6368.
-/

public section

open Filter Set Topology ContinuousLinearMap TensorProduct Module

namespace TauCeti

variable {E F X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace X]

section Coherent

/-- A family `v x` of elements of the determinant lines of the operators `T x` is **coherent at
`x₀` within `s`** if `v x₀ ≠ 0` and some kernel chart valid at `x₀`, with stabilizer a
finite-dimensional subspace `S` of the target and kernel coordinate `q`, reads `v x`, for `x ∈ s`
near `x₀`, as a nonnegative (possibly zero) multiple of its reading of `v x₀`. By
`TauCeti.IsDetLineCoherentWithinAt.eventually_sameRay`, every kernel chart valid at `x₀` reads it
in this way when the family `T` is continuous within `s` at `x₀`. A family coherent at every point
of `s` is a continuous orientation over `s` (`TauCeti.IsDetLineCoherentOn`). -/
def IsDetLineCoherentWithinAt (T : X → E →L[ℝ] F) (v : ∀ x, (T x : E →ₗ[ℝ] F).detLine)
    (s : Set X) (x₀ : X) : Prop :=
  v x₀ ≠ 0 ∧ ∃ (S : Submodule ℝ F) (_ : FiniteDimensional ℝ S) (G : Submodule ℝ (E × S))
    (_ : FiniteDimensional ℝ G) (q : E × S →L[ℝ] G)
    (h₀ : (((T x₀).coprod S.subtypeL).prod q).IsInvertible),
    ∀ᶠ x in 𝓝[s] x₀, ∃ h : (((T x).coprod S.subtypeL).prod q).IsInvertible,
      SameRay ℝ (detLineChartEquiv (T x) S.subtypeL q h (v x))
        (detLineChartEquiv (T x₀) S.subtypeL q h₀ (v x₀))

/-- A family of elements of the determinant lines is **coherent on `s`** if it is coherent within
`s` at every point of `s`. It is then nonzero at every point of `s`, so its nearby readings in a
kernel chart are positive multiples of each other: it is a continuous orientation of the
determinant lines over `s`. -/
def IsDetLineCoherentOn (T : X → E →L[ℝ] F) (v : ∀ x, (T x : E →ₗ[ℝ] F).detLine)
    (s : Set X) : Prop :=
  ∀ x ∈ s, IsDetLineCoherentWithinAt T v s x

variable {T : X → E →L[ℝ] F} {v w : ∀ x, (T x : E →ₗ[ℝ] F).detLine} {s t : Set X} {x₀ : X}

theorem isDetLineCoherentWithinAt_iff : IsDetLineCoherentWithinAt T v s x₀ ↔
    v x₀ ≠ 0 ∧ ∃ (S : Submodule ℝ F) (_ : FiniteDimensional ℝ S) (G : Submodule ℝ (E × S))
      (_ : FiniteDimensional ℝ G) (q : E × S →L[ℝ] G)
      (h₀ : (((T x₀).coprod S.subtypeL).prod q).IsInvertible),
      ∀ᶠ x in 𝓝[s] x₀, ∃ h : (((T x).coprod S.subtypeL).prod q).IsInvertible,
        SameRay ℝ (detLineChartEquiv (T x) S.subtypeL q h (v x))
          (detLineChartEquiv (T x₀) S.subtypeL q h₀ (v x₀)) :=
  Iff.rfl

theorem isDetLineCoherentOn_iff :
    IsDetLineCoherentOn T v s ↔ ∀ x ∈ s, IsDetLineCoherentWithinAt T v s x :=
  Iff.rfl

theorem IsDetLineCoherentWithinAt.ne_zero (hv : IsDetLineCoherentWithinAt T v s x₀) :
    v x₀ ≠ 0 :=
  hv.1

theorem IsDetLineCoherentOn.ne_zero (hv : IsDetLineCoherentOn T v s) {x : X} (hx : x ∈ s) :
    v x ≠ 0 :=
  (hv x hx).ne_zero

/-- Coherence within `s` at `x₀` implies coherence within any set which is a neighbourhood of `x₀`
within `t` and contained in `s` near `x₀`. -/
theorem IsDetLineCoherentWithinAt.mono_of_mem_nhdsWithin (hv : IsDetLineCoherentWithinAt T v s x₀)
    (hst : s ∈ 𝓝[t] x₀) : IsDetLineCoherentWithinAt T v t x₀ := by
  obtain ⟨hv0, S, hS, G, hG, q, h₀, hev⟩ := hv
  exact ⟨hv0, S, hS, G, hG, q, h₀, nhdsWithin_le_of_mem hst hev⟩

theorem IsDetLineCoherentWithinAt.mono (hv : IsDetLineCoherentWithinAt T v s x₀) (hts : t ⊆ s) :
    IsDetLineCoherentWithinAt T v t x₀ :=
  hv.mono_of_mem_nhdsWithin (mem_of_superset self_mem_nhdsWithin hts)

theorem IsDetLineCoherentOn.mono (hv : IsDetLineCoherentOn T v s) (hts : t ⊆ s) :
    IsDetLineCoherentOn T v t :=
  fun x hx ↦ (hv x (hts hx)).mono hts

/-- Coherence only depends on the family near `x₀`. -/
theorem IsDetLineCoherentWithinAt.congr (hv : IsDetLineCoherentWithinAt T v s x₀)
    (hvw : ∀ᶠ x in 𝓝[s] x₀, v x = w x) (hx₀ : v x₀ = w x₀) :
    IsDetLineCoherentWithinAt T w s x₀ := by
  obtain ⟨hv0, S, hS, G, hG, q, h₀, hev⟩ := hv
  refine ⟨hx₀ ▸ hv0, S, hS, G, hG, q, h₀, ?_⟩
  filter_upwards [hev, hvw] with x ⟨h, hx⟩ hvwx
  exact ⟨h, by rwa [← hvwx, ← hx₀]⟩

/-- Coherence is preserved by multiplication by a nonzero scalar. -/
theorem IsDetLineCoherentWithinAt.smul (hv : IsDetLineCoherentWithinAt T v s x₀) {r : ℝ}
    (hr : r ≠ 0) : IsDetLineCoherentWithinAt T (fun x ↦ r • v x) s x₀ := by
  obtain ⟨hv0, S, hS, G, hG, q, h₀, hev⟩ := hv
  refine ⟨smul_ne_zero hr hv0, S, hS, G, hG, q, h₀, ?_⟩
  filter_upwards [hev] with x ⟨h, hx⟩
  exact ⟨h, by simpa only [map_smul] using hx.smul r⟩

theorem IsDetLineCoherentOn.smul (hv : IsDetLineCoherentOn T v s) {r : ℝ} (hr : r ≠ 0) :
    IsDetLineCoherentOn T (fun x ↦ r • v x) s :=
  fun x hx ↦ (hv x hx).smul hr

/-- Coherence is preserved by negation, which reverses the orientation at every point. -/
theorem IsDetLineCoherentWithinAt.neg (hv : IsDetLineCoherentWithinAt T v s x₀) :
    IsDetLineCoherentWithinAt T (fun x ↦ -v x) s x₀ :=
  (hv.smul (neg_ne_zero.2 one_ne_zero)).congr (Eventually.of_forall fun x ↦ neg_one_smul ℝ (v x))
    (neg_one_smul ℝ (v x₀))

theorem IsDetLineCoherentOn.neg (hv : IsDetLineCoherentOn T v s) :
    IsDetLineCoherentOn T (fun x ↦ -v x) s :=
  fun x hx ↦ (hv x hx).neg

/-- Coherence pulls back along maps of the parameter space: if `v` is coherent within `s` at
`f y₀` and `f` maps `𝓝[t] y₀` into `𝓝[s] (f y₀)`, then `y ↦ v (f y)` is coherent within `t` at
`y₀` for the family `T ∘ f`. -/
theorem IsDetLineCoherentWithinAt.comp {Y : Type*} [TopologicalSpace Y] {f : Y → X} {t : Set Y}
    {y₀ : Y} (hv : IsDetLineCoherentWithinAt T v s (f y₀))
    (hf : Tendsto f (𝓝[t] y₀) (𝓝[s] (f y₀))) :
    IsDetLineCoherentWithinAt (T ∘ f) (fun y ↦ v (f y)) t y₀ := by
  obtain ⟨hv0, S, hS, G, hG, q, h₀, hev⟩ := hv
  exact ⟨hv0, S, hS, G, hG, q, h₀, hf.eventually hev⟩

variable [CompleteSpace E]

/-- **Coherence holds in every kernel chart.** If `v` is coherent within `s` at `x₀` for a
family continuous within `s` at `x₀`, then every kernel chart valid at `x₀` reads `v x`, for `x ∈ s`
near `x₀`, as a nonnegative multiple of its reading of `v x₀`. -/
theorem IsDetLineCoherentWithinAt.eventually_sameRay (hT : ContinuousWithinAt T s x₀)
    (hv : IsDetLineCoherentWithinAt T v s x₀) {Λ G : Type*} [NormedAddCommGroup Λ]
    [NormedSpace ℝ Λ] [FiniteDimensional ℝ Λ] [NormedAddCommGroup G] [NormedSpace ℝ G]
    [FiniteDimensional ℝ G] {D₂ : Λ →L[ℝ] F} {q : E × Λ →L[ℝ] G}
    (h₀ : (((T x₀).coprod D₂).prod q).IsInvertible) :
    ∀ᶠ x in 𝓝[s] x₀, ∃ h : (((T x).coprod D₂).prod q).IsInvertible,
      SameRay ℝ (detLineChartEquiv (T x) D₂ q h (v x))
        (detLineChartEquiv (T x₀) D₂ q h₀ (v x₀)) := by
  obtain ⟨-, S, hS, G₁, hG₁, q₁, h₁, hev⟩ := hv
  filter_upwards [hev, hT.tendsto.eventually (eventually_detLineChartEquiv_symm_eq_smul h₀ h₁)]
    with x hx hcx
  obtain ⟨h₁x, hsr⟩ := hx
  obtain ⟨h, h', c, hc, hcu⟩ := hcx
  refine ⟨h, ?_⟩
  -- Map the readings in the first chart to the second chart by the transition at `x₀`; at `x` the
  -- transition is `c` times that one.
  have := (hsr.map ((detLineChartEquiv (T x₀) S.subtypeL q₁ h₁).symm.trans
    (detLineChartEquiv (T x₀) D₂ q h₀)).toLinearMap).pos_smul_left hc
  simpa only [LinearEquiv.coe_coe, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply, ← hcu]
    using this

/-- **Uniqueness of coherent families.** Two coherent families on a preconnected set which lie on
the same ray at one point lie on the same ray at every point. -/
theorem IsDetLineCoherentOn.sameRay (hT : ContinuousOn T s) (hs : IsPreconnected s)
    (hv : IsDetLineCoherentOn T v s) (hw : IsDetLineCoherentOn T w s) {x y : X} (hx : x ∈ s)
    (hy : y ∈ s) (hxy : SameRay ℝ (v x) (w x)) : SameRay ℝ (v y) (w y) := by
  refine (hs.induction₂' (fun x y ↦ SameRay ℝ (v x) (w x) ↔ SameRay ℝ (v y) (w y))
    (fun z hz ↦ ?_) (fun _ _ _ _ _ _ h₁ h₂ ↦ h₁.trans h₂) hx hy).1 hxy
  obtain ⟨hvz, S, hS, G, hG, q, h₀, hev⟩ := hv z hz
  have hwz := (hw z hz).eventually_sameRay (hT z hz) h₀
  filter_upwards [hev, hwz, self_mem_nhdsWithin] with y hvy hwy hys
  obtain ⟨h, hvy⟩ := hvy
  obtain ⟨h', hwy⟩ := hwy
  -- In the chart at `z`, the nonzero readings of `v` and `w` at `y` lie on the rays of their
  -- nonzero readings at `z`, so they lie on one ray exactly when those do.
  have hvy0 := (LinearEquiv.map_ne_zero_iff (detLineChartEquiv (T y) S.subtypeL q h)).2
    (hv.ne_zero hys)
  have hwy0 := (LinearEquiv.map_ne_zero_iff (detLineChartEquiv (T y) S.subtypeL q h')).2
    (hw.ne_zero hys)
  have hvz0 := (LinearEquiv.map_ne_zero_iff (detLineChartEquiv (T z) S.subtypeL q h₀)).2 hvz
  have hwz0 := (LinearEquiv.map_ne_zero_iff (detLineChartEquiv (T z) S.subtypeL q h₀)).2
    (hw.ne_zero hz)
  have key : SameRay ℝ (v y) (w y) ↔ SameRay ℝ (v z) (w z) :=
    (SameRay.sameRay_map_iff (detLineChartEquiv (T y) S.subtypeL q h)).symm.trans
      ((Iff.intro (fun hyw ↦ (hvy.symm.trans_of_ne_zero hyw hvy0).trans_of_ne_zero hwy hwy0)
        fun hzw ↦ (hvy.trans_of_ne_zero hzw hvz0).trans_of_ne_zero hwy.symm hwz0).trans
        (SameRay.sameRay_map_iff (detLineChartEquiv (T z) S.subtypeL q h₀)))
  exact ⟨key.symm, key⟩

variable [CompleteSpace F]

/-- A family which is a fixed nonzero element of the determinant line of a fixed Fredholm operator
is coherent. -/
theorem isDetLineCoherentOn_const {T₀ : E →L[ℝ] F} (hT₀ : IsFredholm T₀)
    {v₀ : (T₀ : E →ₗ[ℝ] F).detLine} (hv₀ : v₀ ≠ 0) (s : Set X) :
    IsDetLineCoherentOn (fun _ ↦ T₀) (fun _ ↦ v₀) s := by
  intro x _
  obtain ⟨S, hS, G, hG, q, U, -, hxU, hinv⟩ := hT₀.exists_isOpen_kernelChart
  exact ⟨hv₀, S, hS, G, hG, q, hinv _ hxU, Eventually.of_forall fun _ ↦ ⟨hinv _ hxU, SameRay.rfl⟩⟩

/-- A family which is nonzero at a parameter with Fredholm operator is coherent on the singleton
of that parameter. -/
private theorem isDetLineCoherentOn_singleton (hF : IsFredholm (T x₀)) (hv : v x₀ ≠ 0) :
    IsDetLineCoherentOn T v {x₀} := by
  rintro x rfl
  obtain ⟨S, hS, G, hG, q, U, -, hxU, hinv⟩ := hF.exists_isOpen_kernelChart
  refine ⟨hv, S, hS, G, hG, q, hinv _ hxU, ?_⟩
  rw [nhdsWithin_singleton]
  exact Filter.eventually_pure.2 ⟨hinv _ hxU, SameRay.rfl⟩

section Interval

variable {T : ℝ → E →L[ℝ] F} {v : ∀ x, (T x : E →ₗ[ℝ] F).detLine}

omit [CompleteSpace F] in
/-- **Continuation of a coherent family.** A coherent family on `[a, u]` continues to a coherent
family on `[a, t]` through a kernel chart valid on `[u, t]`: beyond `u` the continued family is
read in the chart as the constant reading of the family at `u`. -/
private theorem exists_isDetLineCoherentOn_Icc_of_le {a u t : ℝ}
    (hT : ContinuousOn T (Icc a t)) (hau : a ≤ u) (hut : u ≤ t)
    (hv : IsDetLineCoherentOn T v (Icc a u))
    {S : Submodule ℝ F} [FiniteDimensional ℝ S] {G : Submodule ℝ (E × S)}
    [FiniteDimensional ℝ G] {q : E × S →L[ℝ] G}
    (hq : ∀ x ∈ Icc u t, (((T x).coprod S.subtypeL).prod q).IsInvertible) :
    ∃ w : ∀ x, (T x : E →ₗ[ℝ] F).detLine, IsDetLineCoherentOn T w (Icc a t) := by
  classical
  have hu : u ∈ Icc a u := ⟨hau, le_rfl⟩
  have hqu := hq u ⟨le_rfl, hut⟩
  set w₀ := detLineChartEquiv (T u) S.subtypeL q hqu (v u)
  have hw₀ : w₀ ≠ 0 := (LinearEquiv.map_ne_zero_iff _).2 (hv u hu).ne_zero
  let w : ∀ x, (T x : E →ₗ[ℝ] F).detLine := fun x ↦
    if x ≤ u then v x else
      if h : (((T x).coprod S.subtypeL).prod q).IsInvertible then
        (detLineChartEquiv (T x) S.subtypeL q h).symm w₀ else 0
  have hwu : w u = v u := ite_eq_left le_rfl
  -- Beyond `u` the chart reads `w` as the constant `w₀`.
  have hwr (x : ℝ) (hx : x ∈ Ioc u t) : ∃ h : (((T x).coprod S.subtypeL).prod q).IsInvertible,
      detLineChartEquiv (T x) S.subtypeL q h (w x) = w₀ := by
    have h := hq x ⟨hx.1.le, hx.2⟩
    refine ⟨h, ?_⟩
    simp only [w, ite_eq_right (not_le.2 hx.1), dite_eq_left h, LinearEquiv.apply_symm_apply]
  refine ⟨w, fun x hx ↦ ?_⟩
  rcases lt_trichotomy x u with hxu | rfl | hux
  · -- Below `u`, `w` is `v` near `x`.
    have hmem : Icc a u ∈ 𝓝[Icc a t] x :=
      mem_of_superset (inter_mem_nhdsWithin _ (Iio_mem_nhds hxu)) fun y hy ↦ ⟨hy.1.1, hy.2.le⟩
    refine ((hv x ⟨hx.1, hxu.le⟩).mono_of_mem_nhdsWithin hmem).congr ?_ (ite_eq_left hxu.le).symm
    filter_upwards [nhdsWithin_le_nhds (Iic_mem_nhds hxu)] with y hy using (ite_eq_left hy).symm
  · -- At `u`, the chart reads `v` on the left and the constant `w₀` on the right.
    have hsplit : 𝓝[Icc a t] x ≤ 𝓝[Icc a x] x ⊔ 𝓝[Ioc x t] x := by
      rw [← nhdsWithin_union]
      exact nhdsWithin_mono _ fun y hy ↦
        (le_or_gt y x).imp (fun h ↦ ⟨hy.1, h⟩) fun h ↦ ⟨h, hy.2⟩
    refine ⟨by rw [hwu]; exact (hv x hu).ne_zero, S, inferInstance, G, inferInstance, q, hqu,
      hsplit (eventually_sup.2 ⟨?_, ?_⟩)⟩
    · filter_upwards [(hv x hu).eventually_sameRay
          ((hT x ⟨hau, hut⟩).mono (Icc_subset_Icc_right hut)) hqu, self_mem_nhdsWithin]
        with y ⟨h, hy⟩ hy'
      have hwy : w y = v y := ite_eq_left hy'.2
      refine ⟨h, ?_⟩
      rwa [hwu, hwy]
    · filter_upwards [self_mem_nhdsWithin] with y hy
      obtain ⟨h, hyw⟩ := hwr y hy
      refine ⟨h, ?_⟩
      rw [hyw, hwu]
  · -- Beyond `u`, the chart reads `w` as the constant `w₀`.
    obtain ⟨hx', hxw⟩ := hwr x ⟨hux, hx.2⟩
    refine ⟨fun h0 ↦ hw₀ (by rw [← hxw, h0, LinearEquiv.map_zero]), S, inferInstance, G,
      inferInstance, q, hx', ?_⟩
    have hev : ∀ᶠ y in 𝓝[Icc a t] x, y ∈ Ioc u t :=
      mem_of_superset (inter_mem_nhdsWithin _ (Ioi_mem_nhds hux)) fun y hy ↦ ⟨hy.2, hy.1.2⟩
    refine hev.mono fun y hy ↦ ?_
    have hy' := hwr y hy
    exact ⟨hy'.1, (congrArg₂ (SameRay ℝ) hy'.2 hxw).mpr SameRay.rfl⟩

/-- **Existence of coherent families along an interval.** For a family `T` of operators which are
continuous and Fredholm on `[p, q]`, every nonzero element of the determinant line at a point `x₀`
of `[p, q]` is the value at `x₀` of a coherent family on `[p, q]`. -/
theorem exists_isDetLineCoherentOn_Icc {p q : ℝ} (hT : ContinuousOn T (Icc p q))
    (hF : ∀ t ∈ Icc p q, IsFredholm (T t)) {x₀ : ℝ} (hx₀ : x₀ ∈ Icc p q)
    {v₀ : (T x₀ : E →ₗ[ℝ] F).detLine} (hv₀ : v₀ ≠ 0) :
    ∃ v : ∀ t, (T t : E →ₗ[ℝ] F).detLine, v x₀ = v₀ ∧ IsDetLineCoherentOn T v (Icc p q) := by
  have hpq : p ≤ q := hx₀.1.trans hx₀.2
  -- `P t`: a coherent family exists on `[p, t]`. It holds at `p` and is locally constant in `t`.
  let P : ℝ → Prop := fun t ↦
    ∃ v : ∀ t, (T t : E →ₗ[ℝ] F).detLine, IsDetLineCoherentOn T v (Icc p t)
  have hP (x : ℝ) (hx : x ∈ Icc p q) : ∀ᶠ y in 𝓝[Icc p q] x, (P x ↔ P y) ∧ (P y ↔ P x) := by
    obtain ⟨S, hS, G, hG, q', U, hU, hxU, hinv⟩ := (hF x hx).exists_isOpen_kernelChart
    obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhdsWithin_iff.1 ((hT x hx).preimage_mem_nhdsWithin
      (hU.mem_nhds hxU))
    -- Between two points of `[p, q]` where one kernel chart is valid, `P` does not change.
    have step (m M : ℝ) (hm : m ∈ Icc p q) (hM : M ≤ q) (hmM : m ≤ M) (hU' : Icc m M ⊆ T ⁻¹' U) :
        P m ↔ P M :=
      ⟨fun ⟨v, hv⟩ ↦ exists_isDetLineCoherentOn_Icc_of_le (hT.mono (Icc_subset_Icc_right hM))
        hm.1 hmM hv fun z hz ↦ hinv _ (hU' hz),
        fun ⟨v, hv⟩ ↦ ⟨v, hv.mono (Icc_subset_Icc_right hmM)⟩⟩
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Metric.ball_mem_nhds x hδ)]
      with y hy hyx
    have hxy : uIcc x y ⊆ T ⁻¹' U :=
      (subset_inter ((Real.ball_eq_Ioo x δ ▸ ordConnected_Ioo :).uIcc_subset
        (Metric.mem_ball_self hδ) hyx) (ordConnected_Icc.uIcc_subset hx hy)).trans hball
    rcases le_total x y with h | h
    · have := step x y hx hy.2 h (by rwa [uIcc_of_le h] at hxy)
      exact ⟨this, this.symm⟩
    · have := step y x hy hx.2 h (by rwa [uIcc_of_ge h] at hxy)
      exact ⟨this.symm, this⟩
  -- A coherent family on the singleton `[p, p]`.
  have hFp := hF p (left_mem_Icc.2 hpq)
  have : Nontrivial (T p : E →ₗ[ℝ] F).detLine :=
    Module.nontrivial_of_finrank_eq_succ hFp.finrank_detLine
  obtain ⟨u₀, hu₀⟩ := exists_ne (0 : (T p : E →ₗ[ℝ] F).detLine)
  have hPp : P p := ⟨Function.update (fun _ ↦ 0) p u₀, by
    rw [Icc_self]
    exact isDetLineCoherentOn_singleton hFp (by rwa [Function.update_self])⟩
  obtain ⟨w, hw⟩ := (isPreconnected_Icc.induction₂' (fun x y ↦ P x ↔ P y) hP
    (fun _ _ _ _ _ _ h₁ h₂ ↦ h₁.trans h₂) (left_mem_Icc.2 hpq) (right_mem_Icc.2 hpq)).1 hPp
  -- Rescale to the prescribed value at `x₀`.
  obtain ⟨r, hr⟩ := (finrank_eq_one_iff_of_ne_zero' (w x₀) (hw.ne_zero hx₀)).1
    (hF x₀ hx₀).finrank_detLine v₀
  have hr0 : r ≠ 0 := by
    rintro rfl
    exact hv₀ (by rw [← hr, zero_smul])
  exact ⟨fun t ↦ r • w t, hr, hw.smul hr0⟩

end Interval

end Coherent

section Transport

variable [CompleteSpace E] [CompleteSpace F] {T : ℝ → E →L[ℝ] F} {a b c : ℝ}

/-- **Transport of orientations** of determinant lines along a path `T` of operators which are
continuous and Fredholm between `a` and `b`. The orientation of the determinant line of `T a` given
by `v₀ ≠ 0` is carried to the orientation of the determinant line of `T b` given by `v b`, for any
coherent family `v` on `[[a, b]]` with `v a = v₀` (`TauCeti.exists_isDetLineCoherentOn_Icc`);
by uniqueness (`TauCeti.IsDetLineCoherentOn.sameRay`) the result does not depend on the choice
of `v` or of `v₀` in its ray. -/
noncomputable def detLineOrientationTransport (a b : ℝ) (hT : ContinuousOn T (uIcc a b))
    (hF : ∀ t ∈ uIcc a b, IsFredholm (T t)) :
    Module.Ray ℝ (T a : E →ₗ[ℝ] F).detLine → Module.Ray ℝ (T b : E →ₗ[ℝ] F).detLine :=
  Quotient.lift (s := RayVector.Setoid ℝ _)
    (fun u ↦ rayOfNeZero ℝ ((exists_isDetLineCoherentOn_Icc hT hF left_mem_uIcc u.2).choose b)
      ((exists_isDetLineCoherentOn_Icc hT hF left_mem_uIcc u.2).choose_spec.2.ne_zero
        right_mem_uIcc))
    fun u u' (h : SameRay ℝ (u : (T a : E →ₗ[ℝ] F).detLine) u') ↦ by
      have hu := (exists_isDetLineCoherentOn_Icc hT hF left_mem_uIcc u.2).choose_spec
      have hu' := (exists_isDetLineCoherentOn_Icc hT hF left_mem_uIcc u'.2).choose_spec
      exact (ray_eq_iff _ _).2 (hu.2.sameRay hT isPreconnected_uIcc hu'.2 left_mem_uIcc
        right_mem_uIcc (by rwa [hu.1, hu'.1]))

/-- **Characterization of orientation transport**: along a coherent family `v` on `[[a, b]]`,
the orientation of `v a` is transported to the orientation of `v b`. -/
theorem detLineOrientationTransport_rayOfNeZero (hT : ContinuousOn T (uIcc a b))
    (hF : ∀ t ∈ uIcc a b, IsFredholm (T t)) {v : ∀ t, (T t : E →ₗ[ℝ] F).detLine}
    (hv : IsDetLineCoherentOn T v (uIcc a b)) :
    detLineOrientationTransport a b hT hF (rayOfNeZero ℝ (v a) (hv.ne_zero left_mem_uIcc)) =
      rayOfNeZero ℝ (v b) (hv.ne_zero right_mem_uIcc) := by
  have hex := (exists_isDetLineCoherentOn_Icc hT hF left_mem_uIcc
    (hv.ne_zero left_mem_uIcc)).choose_spec
  exact (ray_eq_iff _ _).2 (hex.2.sameRay hT isPreconnected_uIcc hv left_mem_uIcc right_mem_uIcc
    (by rw [hex.1]))

/-- Orientation transport from a point to itself is the identity. -/
@[simp]
theorem detLineOrientationTransport_self (a : ℝ) (hT : ContinuousOn T (uIcc a a))
    (hF : ∀ t ∈ uIcc a a, IsFredholm (T t)) : detLineOrientationTransport a a hT hF = id := by
  funext o
  induction o using Module.Ray.ind with | h v₀ hv₀ => ?_
  obtain ⟨v, rfl, hv⟩ := exists_isDetLineCoherentOn_Icc hT hF left_mem_uIcc hv₀
  exact detLineOrientationTransport_rayOfNeZero hT hF hv

/-- **Reversal law**: transporting an orientation from `a` to `b` and back gives the original
orientation. -/
@[simp]
theorem detLineOrientationTransport_symm (hT : ContinuousOn T (uIcc a b))
    (hT' : ContinuousOn T (uIcc b a)) (hF : ∀ t ∈ uIcc a b, IsFredholm (T t))
    (hF' : ∀ t ∈ uIcc b a, IsFredholm (T t)) (o : Module.Ray ℝ (T a : E →ₗ[ℝ] F).detLine) :
    detLineOrientationTransport b a hT' hF' (detLineOrientationTransport a b hT hF o) = o := by
  induction o using Module.Ray.ind with | h v₀ hv₀ => ?_
  obtain ⟨v, rfl, hv⟩ := exists_isDetLineCoherentOn_Icc hT hF left_mem_uIcc hv₀
  rw [detLineOrientationTransport_rayOfNeZero hT hF hv]
  exact detLineOrientationTransport_rayOfNeZero hT' hF' (uIcc_comm a b ▸ hv)

/-- **Concatenation law**: transporting an orientation from `a` to `b` and then from `b` to `c`
is transporting it from `a` to `c`. -/
theorem detLineOrientationTransport_trans (hTab : ContinuousOn T (uIcc a b))
    (hTbc : ContinuousOn T (uIcc b c)) (hTac : ContinuousOn T (uIcc a c))
    (hab : ∀ t ∈ uIcc a b, IsFredholm (T t)) (hbc : ∀ t ∈ uIcc b c, IsFredholm (T t))
    (hac : ∀ t ∈ uIcc a c, IsFredholm (T t)) (o : Module.Ray ℝ (T a : E →ₗ[ℝ] F).detLine) :
    detLineOrientationTransport b c hTbc hbc (detLineOrientationTransport a b hTab hab o) =
      detLineOrientationTransport a c hTac hac o := by
  induction o using Module.Ray.ind with | h v₀ hv₀ => ?_
  -- A coherent family on the interval spanned by `a`, `b` and `c`.
  set I := Icc (min (min a b) c) (max (max a b) c)
  have hmem {x : ℝ} (hx : x = a ∨ x = b ∨ x = c) : x ∈ I := by
    rcases hx with rfl | rfl | rfl <;> constructor <;> simp
  have hsub {x y : ℝ} (hx : x = a ∨ x = b ∨ x = c) (hy : y = a ∨ y = b ∨ y = c) : uIcc x y ⊆ I :=
    uIcc_subset_Icc (hmem hx) (hmem hy)
  -- `I` is covered by `[[a, b]]` and `[[b, c]]`, which share `b`.
  have hcover : I ⊆ uIcc a b ∪ uIcc b c := by
    rintro t ⟨h₁, h₂⟩
    simp only [mem_union, mem_uIcc, min_le_iff, le_max_iff] at h₁ h₂ ⊢
    grind
  have hT : ContinuousOn T I := (hTab.union_of_isClosed hTbc isClosed_Icc isClosed_Icc).mono hcover
  have hF (t : ℝ) (ht : t ∈ I) : IsFredholm (T t) := (hcover ht).elim (hab t) (hbc t)
  obtain ⟨v, rfl, hv⟩ := exists_isDetLineCoherentOn_Icc hT hF (hmem (.inl rfl)) hv₀
  rw [detLineOrientationTransport_rayOfNeZero hTab hab
      (hv.mono (hsub (.inl rfl) (.inr (.inl rfl)))),
    detLineOrientationTransport_rayOfNeZero hTbc hbc
      (hv.mono (hsub (.inr (.inl rfl)) (.inr (.inr rfl)))),
    detLineOrientationTransport_rayOfNeZero hTac hac
      (hv.mono (hsub (.inl rfl) (.inr (.inr rfl))))]

/-- Orientation transport carries the opposite orientation to the opposite orientation. -/
@[simp]
theorem detLineOrientationTransport_neg (hT : ContinuousOn T (uIcc a b))
    (hF : ∀ t ∈ uIcc a b, IsFredholm (T t)) (o : Module.Ray ℝ (T a : E →ₗ[ℝ] F).detLine) :
    detLineOrientationTransport a b hT hF (-o) = -detLineOrientationTransport a b hT hF o := by
  induction o using Module.Ray.ind with | h v₀ hv₀ => ?_
  obtain ⟨v, rfl, hv⟩ := exists_isDetLineCoherentOn_Icc hT hF left_mem_uIcc hv₀
  rw [detLineOrientationTransport_rayOfNeZero hT hF hv]
  -- Negation of rays is negation of representatives (`neg_rayOfNeZero`, which holds by `rfl`).
  exact detLineOrientationTransport_rayOfNeZero hT hF hv.neg

/-- Along a constant path, orientation transport is the identity. -/
@[simp]
theorem detLineOrientationTransport_const {T₀ : E →L[ℝ] F} (hT₀ : IsFredholm T₀) (a b : ℝ) :
    detLineOrientationTransport (T := fun _ ↦ T₀) a b continuousOn_const (fun _ _ ↦ hT₀) =
      id := by
  funext o
  induction o using Module.Ray.ind with | h v₀ hv₀ => ?_
  exact detLineOrientationTransport_rayOfNeZero continuousOn_const _
    (isDetLineCoherentOn_const hT₀ hv₀ _)

end Transport

end TauCeti
