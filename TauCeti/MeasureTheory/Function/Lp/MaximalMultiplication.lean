/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.LinearPMap
public import TauCeti.LinearAlgebra.LinearPMap.SmulSub
public import TauCeti.MeasureTheory.Function.Lp.Multiplication
public import TauCeti.Topology.Algebra.Module.LinearPMap.Resolvent.Basic
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import TauCeti.LinearAlgebra.LinearPMap.Basic
import TauCeti.MeasureTheory.Function.Lp.DominatedConvergence
import TauCeti.Topology.Algebra.Module.LinearPMap.GraphCore

/-!
# Maximal unbounded multiplication operators on `Lᵖ`

Given a scalar function `f : α → 𝕜` on a measure space `(α, μ)` and a normed `𝕜`-space `E`,
pointwise scalar multiplication `u ↦ (x ↦ f x • u x)` defines a partial linear operator
`MeasureTheory.Lp.maximalMultiplication p μ f` on `Lp E p μ` whose domain consists of all classes
`u ∈ Lp E p μ` for which `x ↦ f x • u x` belongs to `MemLp · p μ` (including almost-everywhere
strong measurability of the product).

Because `MemLp` already bundles measurability and `Lᵖ` integrability of the product, the
definition itself carries no measurability hypothesis on `f`: altering `f` on a `μ`-null set
produces the identical `LinearPMap` (`MeasureTheory.Lp.maximalMultiplication_congr_ae`), and a pair
`(u, v)` lies on its graph if and only if `v =ᵐ[μ] fun x ↦ f x • u x`
(`MeasureTheory.Lp.mem_graph_maximalMultiplication_iff`).

## Main definitions

* `MeasureTheory.Lp.maximalMultiplication p μ f`: the maximal partial linear operator of
  multiplication by `f : α → 𝕜` on `Lp E p μ`.
* `MeasureTheory.Lp.boundedSupportSubmodule p μ f`: the submodule of vectors `u : Lp E p μ`
  vanishing almost everywhere outside a set on which `f` is bounded.

## Main results

* `MeasureTheory.Lp.mem_graph_maximalMultiplication_iff`: `(u, v)` belongs to the graph of
  `maximalMultiplication p μ f` if and only if `v =ᵐ[μ] fun x ↦ f x • u x`.
* `MeasureTheory.Lp.maximalMultiplication_eq_maximalMultiplication_iff`: on a sigma-finite space
  with nontrivial fiber `E`, two almost-everywhere strongly measurable multipliers induce the same
  maximal operator if and only if they agree almost everywhere.
* `MeasureTheory.Lp.isClosed_maximalMultiplication`: `maximalMultiplication p μ f` is closed for
  every `1 ≤ p ≤ ∞`, every measure `μ`, and every symbol `f`.
* `MeasureTheory.Lp.dense_maximalMultiplication_domain` and
  `MeasureTheory.Lp.hasCore_boundedSupportSubmodule`: when `f` is almost-everywhere strongly
  measurable and `p ≠ ∞`, the vectors of `f`-bounded support form a dense operator core for
  `maximalMultiplication p μ f`, so its maximal domain is dense in `Lp E p μ`.
* `MeasureTheory.Lp.adjoint_maximalMultiplication`: on `Lp E 2 μ` for a complete inner-product
  space `E` over `𝕜` (`[RCLike 𝕜]`) and any measure `μ`, the Hilbert adjoint of
  `maximalMultiplication 2 μ f` for an almost-everywhere strongly measurable `f` is
  `maximalMultiplication 2 μ (star f)`.
* `MeasureTheory.Lp.isSelfAdjoint_maximalMultiplication` and
  `MeasureTheory.Lp.isSelfAdjoint_maximalMultiplication_iff`: almost-everywhere self-conjugate
  symbols give self-adjoint operators on any measure space, and on a sigma-finite measure space
  with nontrivial fiber this condition is also necessary.
* `MeasureTheory.Lp.existsUnique_maximalMultiplication`: existence and uniqueness of the closed,
  densely defined maximal `L²` realization of an almost-everywhere strongly measurable multiplier.
* `MeasureTheory.Lp.mem_resolventSet_maximalMultiplication_iff` and
  `MeasureTheory.Lp.spectrum_maximalMultiplication`: on a sigma-finite space with nontrivial
  fiber and `1 ≤ p ≤ ∞`, the spectrum of `maximalMultiplication p μ f` is the measure-theoretic
  essential range `{z : 𝕜 | ∀ ε > 0, μ {x | ‖f x - z‖ < ε} ≠ 0}`, with explicit resolvent given
  by multiplication by `(z - f)⁻¹`.

## References

* G. Teschl, *Mathematical Methods in Quantum Mechanics*, Section 3.1 and Theorem 3.18.
* M. Reed and B. Simon, *Methods of Modern Mathematical Physics I: Functional Analysis*,
  Section VIII.3, Example 1.
-/

public section

noncomputable section

open Filter Topology
open scoped ENNReal InnerProductSpace

namespace MeasureTheory.Lp

section Basic

variable {α 𝕜 E : Type*} [MeasurableSpace α] [NormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] {p : ℝ≥0∞} {μ : Measure α}

/-- The maximal partial linear operator of pointwise scalar multiplication by `f : α → 𝕜` on
`Lp E p μ`, defined on the submodule `{u : Lp E p μ | MemLp (fun x ↦ f x • u x) p μ}`. -/
def maximalMultiplication (p : ℝ≥0∞) (μ : Measure α) (f : α → 𝕜) :
    Lp E p μ →ₗ.[𝕜] Lp E p μ where
  domain :=
    { carrier := {u : Lp E p μ | MemLp (fun x ↦ f x • u x) p μ}
      zero_mem' := by
        refine MemLp.zero.ae_eq ?_
        filter_upwards [Lp.coeFn_zero E p μ] with x hx
        rw [hx, Pi.zero_apply, smul_zero]
      add_mem' {u v} hu hv := by
        refine (hu.add hv).ae_eq ?_
        filter_upwards [Lp.coeFn_add u v] with x hx
        rw [Pi.add_apply, hx, Pi.add_apply, smul_add]
      smul_mem' c {u} hu := by
        refine (hu.const_smul c).ae_eq ?_
        filter_upwards [Lp.coeFn_smul c u] with x hx
        rw [Pi.smul_apply, hx, Pi.smul_apply, smul_comm (f x) c] }
  toFun :=
    { toFun u := u.2.toLp (fun x ↦ f x • (u : Lp E p μ) x)
      map_add' u v := by
        refine Lp.ext ?_
        filter_upwards [(u + v).2.coeFn_toLp, Lp.coeFn_add (u.2.toLp _) (v.2.toLp _),
          u.2.coeFn_toLp, v.2.coeFn_toLp, Lp.coeFn_add (u : Lp E p μ) v]
          with x huv hadd hu hv hcoe
        rw [huv, hadd, Pi.add_apply, hu, hv, AddMemClass.coe_add, hcoe, Pi.add_apply, smul_add]
      map_smul' c u := by
        refine Lp.ext ?_
        filter_upwards [(c • u).2.coeFn_toLp, Lp.coeFn_smul c (u.2.toLp _),
          u.2.coeFn_toLp, Lp.coeFn_smul c (u : Lp E p μ)] with x hcu hsmul hu hcoe
        rw [RingHom.id_apply, hcu, hsmul, Pi.smul_apply, hu, SetLike.val_smul, hcoe,
          Pi.smul_apply, smul_comm (f x) c] }

/-- A class `u : Lp E p μ` lies in the domain of `maximalMultiplication p μ f` precisely when
`x ↦ f x • u x` belongs to `MemLp · p μ`. -/
@[simp]
theorem mem_domain_maximalMultiplication {f : α → 𝕜} {u : Lp E p μ} :
    u ∈ (maximalMultiplication p μ f).domain ↔ MemLp (fun x ↦ f x • u x) p μ :=
  (Iff.rfl)

/-- Applying `maximalMultiplication p μ f` to `u` with membership proof `hu` produces the `Lᵖ`
class of `x ↦ f x • u x`. -/
theorem maximalMultiplication_apply {f : α → 𝕜} {u : Lp E p μ}
    (hu : MemLp (fun x ↦ f x • u x) p μ) :
    maximalMultiplication p μ f ⟨u, mem_domain_maximalMultiplication.2 hu⟩ =
      hu.toLp (fun x ↦ f x • u x) :=
  (rfl)

/-- `maximalMultiplication p μ f` acts by pointwise scalar multiplication almost everywhere on its
domain. -/
theorem coeFn_maximalMultiplication {f : α → 𝕜}
    (u : (maximalMultiplication (E := E) p μ f).domain) :
    maximalMultiplication p μ f u =ᵐ[μ] fun x ↦ f x • (u : Lp E p μ) x :=
  u.2.coeFn_toLp

/-- The value of `maximalMultiplication p μ f` at `u` equals `v` if and only if
`x ↦ f x • u x` agrees with `v` almost everywhere. -/
theorem maximalMultiplication_apply_eq_iff {f : α → 𝕜}
    {u : (maximalMultiplication (E := E) p μ f).domain} {v : Lp E p μ} :
    maximalMultiplication p μ f u = v ↔ (fun x ↦ f x • (u : Lp E p μ) x) =ᵐ[μ] v :=
  ⟨fun h ↦ h ▸ (coeFn_maximalMultiplication u).symm,
    fun h ↦ Lp.ext ((coeFn_maximalMultiplication u).trans h)⟩

/-- A pair `w = (u, v)` belongs to the graph of `maximalMultiplication p μ f` if and only if
`v` agrees almost everywhere with `x ↦ f x • u x`. -/
theorem mem_graph_maximalMultiplication_iff {f : α → 𝕜} {w : Lp E p μ × Lp E p μ} :
    w ∈ (maximalMultiplication (E := E) p μ f).graph ↔
      w.2 =ᵐ[μ] fun x ↦ f x • w.1 x := by
  rcases w with ⟨u₀, v₀⟩
  rw [(maximalMultiplication (E := E) p μ f).mem_graph_iff]
  constructor
  · rintro ⟨u, rfl, rfl⟩
    exact coeFn_maximalMultiplication u
  · intro hw
    have hu : MemLp (fun x ↦ f x • u₀ x) p μ := (Lp.memLp v₀).ae_eq hw
    exact ⟨⟨u₀, mem_domain_maximalMultiplication.2 hu⟩, rfl,
      maximalMultiplication_apply_eq_iff.2 hw.symm⟩

/-- Any partial linear operator on `Lp E p μ` with domain `{u | MemLp (fun x ↦ f x • u x) p μ}`
that acts almost everywhere as `x ↦ f x • u x` is equal to `maximalMultiplication p μ f`. -/
theorem eq_maximalMultiplication_of_domain_of_ae {f : α → 𝕜}
    {T : Lp E p μ →ₗ.[𝕜] Lp E p μ}
    (hdom : ∀ u : Lp E p μ, u ∈ T.domain ↔ MemLp (fun x ↦ f x • u x) p μ)
    (hae : ∀ u : T.domain, T u =ᵐ[μ] fun x ↦ f x • (u : Lp E p μ) x) :
    T = maximalMultiplication p μ f := by
  refine LinearPMap.ext (SetLike.ext fun u ↦ (hdom u).trans mem_domain_maximalMultiplication.symm)
    fun u hu₁ hu₂ ↦ ?_
  exact (maximalMultiplication_apply_eq_iff (u := ⟨u, hu₂⟩)).2 (hae ⟨u, hu₁⟩).symm |>.symm

/-- Modifying the symbol on a `μ`-null set leaves `maximalMultiplication p μ f` unchanged. -/
theorem maximalMultiplication_congr_ae {f g : α → 𝕜} (hfg : f =ᵐ[μ] g) :
    maximalMultiplication (E := E) p μ f = maximalMultiplication (E := E) p μ g := by
  refine LinearPMap.eq_of_eq_graph (SetLike.ext fun w ↦ ?_)
  rw [mem_graph_maximalMultiplication_iff, mem_graph_maximalMultiplication_iff]
  have hsmul : (fun x ↦ f x • w.1 x) =ᵐ[μ] fun x ↦ g x • w.1 x :=
    hfg.mono fun x hx ↦ by dsimp only; rw [hx]
  exact ⟨fun h ↦ h.trans hsmul, fun h ↦ h.trans hsmul.symm⟩

/-- The zero multiplier induces the everywhere-defined zero partial linear operator. -/
@[simp]
theorem maximalMultiplication_zero :
    maximalMultiplication (E := E) p μ (0 : α → 𝕜) = 0 := by
  refine LinearPMap.eq_of_eq_graph (SetLike.ext fun ⟨u₀, v₀⟩ ↦ ?_)
  rw [mem_graph_maximalMultiplication_iff, (0 : Lp E p μ →ₗ.[𝕜] Lp E p μ).mem_graph_iff]
  constructor
  · intro hw
    refine ⟨⟨u₀, Submodule.mem_top⟩, rfl, ?_⟩
    rw [LinearPMap.zero_apply]
    refine (Lp.ext ?_).symm
    refine hw.trans ?_
    filter_upwards [Lp.coeFn_zero E p μ] with x h0
    rw [Pi.zero_apply, zero_smul, h0, Pi.zero_apply]
  · rintro ⟨u, rfl, rfl⟩
    filter_upwards [Lp.coeFn_zero E p μ] with x h0
    rw [LinearPMap.zero_apply, h0, Pi.zero_apply, Pi.zero_apply, zero_smul]

/-- A constant multiplier `c` induces the everywhere-defined scalar multiple `c • id`. -/
theorem maximalMultiplication_const (c : 𝕜) :
    maximalMultiplication (E := E) p μ (fun _ ↦ c) =
      (c • LinearMap.id : Lp E p μ →ₗ[𝕜] Lp E p μ).toPMap ⊤ := by
  refine LinearPMap.eq_of_eq_graph (SetLike.ext fun ⟨u₀, v₀⟩ ↦ ?_)
  rw [mem_graph_maximalMultiplication_iff,
    ((c • LinearMap.id : Lp E p μ →ₗ[𝕜] Lp E p μ).toPMap ⊤).mem_graph_iff]
  constructor
  · intro hw
    refine ⟨⟨u₀, Submodule.mem_top⟩, rfl, (Lp.ext ?_).symm⟩
    exact hw.trans (Lp.coeFn_smul c u₀).symm
  · rintro ⟨u, rfl, rfl⟩
    exact Lp.coeFn_smul c (u : Lp E p μ)

/-- The unit multiplier `1` induces the everywhere-defined identity operator. -/
@[simp]
theorem maximalMultiplication_one :
    maximalMultiplication (E := E) p μ (1 : α → 𝕜) =
      (LinearMap.id : Lp E p μ →ₗ[𝕜] Lp E p μ).toPMap ⊤ := by
  simpa only [Pi.one_def, one_smul] using
    maximalMultiplication_const (E := E) (p := p) (μ := μ) (1 : 𝕜)

/-- Negating the multiplier negates the maximal multiplication operator. -/
@[simp]
theorem maximalMultiplication_neg (f : α → 𝕜) :
    maximalMultiplication (E := E) p μ (-f) = -maximalMultiplication (E := E) p μ f := by
  refine LinearPMap.ext ?_ fun u hu₁ hu₂ ↦ ?_
  · ext u
    simp only [LinearPMap.neg_domain, mem_domain_maximalMultiplication, Pi.neg_apply, neg_smul]
    exact ⟨fun h ↦ h.neg.ae_eq (Eventually.of_forall fun x ↦ neg_neg _), fun h ↦ h.neg⟩
  · refine Lp.ext ?_
    have hu₂' : u ∈ (maximalMultiplication (E := E) p μ f).domain := hu₂
    filter_upwards [coeFn_maximalMultiplication ⟨u, hu₁⟩,
      Lp.coeFn_neg (maximalMultiplication p μ f ⟨u, hu₂'⟩),
      coeFn_maximalMultiplication ⟨u, hu₂'⟩] with x h₁ hneg h₂
    rw [LinearPMap.neg_apply, h₁, Pi.neg_apply, neg_smul, hneg, Pi.neg_apply, h₂]

/-- Scaling the multiplier by a nonzero scalar `c` scales the maximal multiplication operator by
`c`. For `c = 0` the left-hand side has full domain `⊤` while `0 • T` retains `T.domain`. -/
theorem maximalMultiplication_smul {c : 𝕜} (hc : c ≠ 0) (f : α → 𝕜) :
    maximalMultiplication (E := E) p μ (c • f) = c • maximalMultiplication (E := E) p μ f := by
  refine LinearPMap.ext ?_ fun u hu₁ hu₂ ↦ ?_
  · ext u
    simp only [LinearPMap.smul_domain, mem_domain_maximalMultiplication, Pi.smul_apply,
      smul_eq_mul, mul_smul]
    refine ⟨fun h ↦ (h.const_smul c⁻¹).ae_eq (Eventually.of_forall fun x ↦ ?_),
      fun h ↦ h.const_smul c⟩
    rw [Pi.smul_apply, inv_smul_smul₀ hc]
  · refine Lp.ext ?_
    have hu₂' : u ∈ (maximalMultiplication (E := E) p μ f).domain := hu₂
    filter_upwards [coeFn_maximalMultiplication ⟨u, hu₁⟩,
      Lp.coeFn_smul c (maximalMultiplication p μ f ⟨u, hu₂'⟩),
      coeFn_maximalMultiplication ⟨u, hu₂'⟩] with x h₁ hsmul h₂
    rw [LinearPMap.smul_apply, h₁, Pi.smul_apply, smul_eq_mul, mul_smul, hsmul, Pi.smul_apply, h₂]

/-- Subtracting a constant scalar `c` from the multiplier shifts the maximal multiplication
operator by `LinearPMap.subScalar · c`. -/
theorem maximalMultiplication_sub_const (f : α → 𝕜) (c : 𝕜) :
    maximalMultiplication (E := E) p μ (fun x ↦ f x - c) =
      (maximalMultiplication (E := E) p μ f).subScalar c := by
  refine LinearPMap.ext ?_ fun u hu₁ hu₂ ↦ ?_
  · ext u
    simp only [LinearPMap.subScalar_domain, mem_domain_maximalMultiplication, sub_smul]
    refine ⟨fun h ↦ (h.add ((Lp.memLp u).const_smul c)).ae_eq (Eventually.of_forall fun x ↦ ?_),
      fun h ↦ h.sub ((Lp.memLp u).const_smul c)⟩
    simp only [Pi.add_apply, Pi.smul_apply, sub_add_cancel]
  · refine Lp.ext ?_
    have hu₂' : u ∈ (maximalMultiplication (E := E) p μ f).domain := by
      rwa [LinearPMap.subScalar_domain] at hu₂
    filter_upwards [coeFn_maximalMultiplication ⟨u, hu₁⟩,
      Lp.coeFn_sub (maximalMultiplication p μ f ⟨u, hu₂'⟩) (c • u),
      coeFn_maximalMultiplication ⟨u, hu₂'⟩, Lp.coeFn_smul c u] with x h₁ hsub h₂ hsmul
    rw [LinearPMap.subScalar_apply, h₁, hsub, Pi.sub_apply, h₂, hsmul, Pi.smul_apply, sub_smul]

/-- The operator sum of two maximal multiplication operators is a restriction of the maximal
multiplication operator of the pointwise sum. -/
theorem add_maximalMultiplication_le (f g : α → 𝕜) :
    maximalMultiplication (E := E) p μ f + maximalMultiplication (E := E) p μ g ≤
      maximalMultiplication (E := E) p μ (f + g) := by
  refine LinearPMap.le_of_le_graph fun ⟨u₀, v₀⟩ hw ↦ ?_
  obtain ⟨u, rfl, rfl⟩ :=
    (maximalMultiplication p μ f + maximalMultiplication p μ g).mem_graph_iff.1 hw
  rw [mem_graph_maximalMultiplication_iff]
  have huf : (u : Lp E p μ) ∈ (maximalMultiplication (E := E) p μ f).domain := u.2.1
  have hug : (u : Lp E p μ) ∈ (maximalMultiplication (E := E) p μ g).domain := u.2.2
  filter_upwards [Lp.coeFn_add (maximalMultiplication p μ f ⟨(u : Lp E p μ), huf⟩)
      (maximalMultiplication p μ g ⟨(u : Lp E p μ), hug⟩),
    coeFn_maximalMultiplication ⟨(u : Lp E p μ), huf⟩,
    coeFn_maximalMultiplication ⟨(u : Lp E p μ), hug⟩]
    with x hadd hf hg
  rw [LinearPMap.add_apply, hadd, Pi.add_apply, hf, hg, Pi.add_apply, add_smul]

/-- For `u` in the domain of `maximalMultiplication p μ g`, its image lies in the domain of
`maximalMultiplication p μ f` if and only if `u` lies in the domain of
`maximalMultiplication p μ (f * g)`. -/
theorem maximalMultiplication_mem_domain_iff {f g : α → 𝕜}
    (u : (maximalMultiplication (E := E) p μ g).domain) :
    maximalMultiplication p μ g u ∈ (maximalMultiplication (E := E) p μ f).domain ↔
      (u : Lp E p μ) ∈ (maximalMultiplication (E := E) p μ (f * g)).domain := by
  rw [mem_domain_maximalMultiplication, mem_domain_maximalMultiplication]
  have hae : (fun x ↦ f x • (maximalMultiplication p μ g u) x) =ᵐ[μ]
      fun x ↦ (f * g) x • (u : Lp E p μ) x := by
    filter_upwards [coeFn_maximalMultiplication u] with x hx
    rw [hx, Pi.mul_apply, mul_smul]
  exact ⟨fun h ↦ h.ae_eq hae, fun h ↦ h.ae_eq hae.symm⟩

/-- Applying `maximalMultiplication p μ f` after `maximalMultiplication p μ g` agrees with
`maximalMultiplication p μ (f * g)` whenever `u` belongs to the domain of `g` and its image
belongs to the domain of `f`. -/
theorem maximalMultiplication_apply_maximalMultiplication {f g : α → 𝕜}
    (u : (maximalMultiplication (E := E) p μ g).domain)
    (hu : maximalMultiplication p μ g u ∈ (maximalMultiplication (E := E) p μ f).domain) :
    maximalMultiplication p μ f ⟨maximalMultiplication p μ g u, hu⟩ =
      maximalMultiplication p μ (f * g)
        ⟨u, (maximalMultiplication_mem_domain_iff u).1 hu⟩ := by
  rw [maximalMultiplication_apply_eq_iff]
  filter_upwards [coeFn_maximalMultiplication u,
    coeFn_maximalMultiplication ⟨(u : Lp E p μ), (maximalMultiplication_mem_domain_iff u).1 hu⟩]
    with x hxg hxfg
  rw [hxg, hxfg, Pi.mul_apply, mul_smul]

/-- A vector `u : Lp E p μ` lies in the kernel of `maximalMultiplication p μ f` if and only if
at almost every point either `f x = 0` or `u x = 0`. -/
theorem mem_ker_maximalMultiplication_iff {f : α → 𝕜} {u : Lp E p μ} :
    u ∈ (maximalMultiplication (E := E) p μ f).ker ↔ ∀ᵐ x ∂μ, f x = 0 ∨ u x = 0 := by
  rw [LinearPMap.mem_ker_iff]
  constructor
  · rintro ⟨v, rfl, hv0⟩
    filter_upwards [coeFn_maximalMultiplication v, hv0 ▸ Lp.coeFn_zero E p μ] with x hx h0
    exact smul_eq_zero.1 (hx.symm.trans h0)
  · intro h
    have hzero : (fun x ↦ f x • u x) =ᵐ[μ] (0 : α → E) :=
      h.mono fun x hx ↦ smul_eq_zero.2 hx
    have hu : MemLp (fun x ↦ f x • u x) p μ := MemLp.zero.ae_eq hzero.symm
    refine ⟨⟨u, mem_domain_maximalMultiplication.2 hu⟩, rfl, Lp.ext ?_⟩
    exact (coeFn_maximalMultiplication ⟨u, mem_domain_maximalMultiplication.2 hu⟩).trans
      (hzero.trans (Lp.coeFn_zero E p μ).symm)

/-- When `f` is essentially bounded (`MemLp f ∞ μ`), `maximalMultiplication p μ f` is defined on
all of `Lp E p μ`. -/
theorem domain_maximalMultiplication_eq_top {f : α → 𝕜} (hf : MemLp f ∞ μ) :
    (maximalMultiplication (E := E) p μ f).domain = ⊤ :=
  Submodule.eq_top_iff'.2 fun u ↦ mem_domain_maximalMultiplication.2 (hf.smul (Lp.memLp u))

/-- For an essentially bounded complex symbol `a : Lp ℂ ∞ μ`, `maximalMultiplication 2 μ a` agrees
with `MeasureTheory.Lp.multiplicationOperator a` viewed as an everywhere-defined `LinearPMap`. -/
@[simp]
theorem maximalMultiplication_coeFn_eq_multiplicationOperator
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] (a : Lp ℂ ∞ μ) :
    maximalMultiplication (E := F) 2 μ a =
      (multiplicationOperator (E := F) a : Lp F 2 μ →ₗ[ℂ] Lp F 2 μ).toPMap ⊤ := by
  refine eq_maximalMultiplication_of_domain_of_ae (fun u ↦ ?_) (fun u ↦ ?_) |>.symm
  · simp only [LinearMap.toPMap_domain, Submodule.mem_top, true_iff]
    exact (Lp.memLp a).smul (Lp.memLp u)
  · exact multiplicationOperator_ae a (u : Lp F 2 μ)

end Basic

/-! ### Closedness -/

section Closed

variable {α 𝕜 E : Type*} [MeasurableSpace α] [NormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] {p : ℝ≥0∞} [Fact (1 ≤ p)] {μ : Measure α}

/-- `maximalMultiplication p μ f` is a closed partial linear operator for every `1 ≤ p ≤ ∞`, every
measure `μ`, and every symbol `f : α → 𝕜`. -/
theorem isClosed_maximalMultiplication (f : α → 𝕜) :
    (maximalMultiplication (E := E) p μ f).IsClosed := by
  refine IsSeqClosed.isClosed fun w w_lim hw hlim ↦ ?_
  have hfst : Tendsto (fun n ↦ (w n).1) atTop (𝓝 w_lim.1) :=
    (continuous_fst.tendsto w_lim).comp hlim
  have hsnd : Tendsto (fun n ↦ (w n).2) atTop (𝓝 w_lim.2) :=
    (continuous_snd.tendsto w_lim).comp hlim
  obtain ⟨φ, hφ, hu_ae⟩ := (tendstoInMeasure_of_tendsto_Lp hfst).exists_seq_tendsto_ae
  obtain ⟨ψ, hψ, hv_ae⟩ :=
    (tendstoInMeasure_of_tendsto_Lp (hsnd.comp hφ.tendsto_atTop)).exists_seq_tendsto_ae
  have hgraph : ∀ᵐ x ∂μ, ∀ k, (w (φ (ψ k))).2 x = f x • (w (φ (ψ k))).1 x :=
    ae_all_iff.2 fun k ↦ mem_graph_maximalMultiplication_iff.1 (hw (φ (ψ k)))
  rw [SetLike.mem_coe, mem_graph_maximalMultiplication_iff]
  filter_upwards [hu_ae, hv_ae, hgraph] with x hux hvx hgx
  have hrhs : Tendsto (fun k ↦ (w (φ (ψ k))).2 x) atTop (𝓝 (f x • w_lim.1 x)) :=
    ((hux.comp hψ.tendsto_atTop).const_smul (f x)).congr'
      (Eventually.of_forall fun k ↦ (hgx k).symm)
  exact tendsto_nhds_unique hvx hrhs

end Closed

/-! ### Bounded-support vectors, domain density, core property, and symbol faithfulness -/

section CutoffAndFaithful

variable {α 𝕜 E : Type*} [MeasurableSpace α] [NormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] {p : ℝ≥0∞} {μ : Measure α}

/-- The submodule of vectors `u : Lp E p μ` vanishing almost everywhere where `‖f‖` exceeds some
finite bound `C`. -/
def boundedSupportSubmodule (p : ℝ≥0∞) (μ : Measure α) (f : α → 𝕜) :
    Submodule 𝕜 (Lp E p μ) where
  carrier := {u : Lp E p μ | ∃ C : ℝ, ∀ᵐ x ∂μ, u x ≠ 0 → ‖f x‖ ≤ C}
  zero_mem' := ⟨0, (Lp.coeFn_zero E p μ).mono fun _ hx hne ↦ False.elim (hne hx)⟩
  add_mem' {u v} := by
    rintro ⟨C₁, h₁⟩ ⟨C₂, h₂⟩
    refine ⟨max C₁ C₂, ?_⟩
    filter_upwards [Lp.coeFn_add u v, h₁, h₂] with x hadd hu hv hne
    rw [hadd, Pi.add_apply] at hne
    by_cases hux : u x = 0
    · rw [hux, zero_add] at hne
      exact (hv hne).trans (le_max_right _ _)
    · exact (hu hux).trans (le_max_left _ _)
  smul_mem' c {u} := by
    rintro ⟨C, hu⟩
    refine ⟨C, ?_⟩
    filter_upwards [Lp.coeFn_smul c u, hu] with x hsmul hx hne
    rw [hsmul, Pi.smul_apply] at hne
    exact hx (right_ne_zero_of_smul hne)

/-- Membership in `boundedSupportSubmodule p μ f` means that `‖f‖` is bounded almost everywhere on
the support of `u`. -/
theorem mem_boundedSupportSubmodule_iff {f : α → 𝕜} {u : Lp E p μ} :
    u ∈ boundedSupportSubmodule p μ f ↔ ∃ C : ℝ, ∀ᵐ x ∂μ, u x ≠ 0 → ‖f x‖ ≤ C :=
  (Iff.rfl)

/-- For an almost-everywhere strongly measurable symbol `f`, every vector in
`boundedSupportSubmodule p μ f` lies in the domain of `maximalMultiplication p μ f`. -/
theorem boundedSupportSubmodule_le_domain {f : α → 𝕜} (hf : AEStronglyMeasurable f μ) :
    boundedSupportSubmodule (E := E) p μ f ≤
      (maximalMultiplication (E := E) p μ f).domain := by
  intro u hu
  obtain ⟨C, hC⟩ := mem_boundedSupportSubmodule_iff.1 hu
  rw [mem_domain_maximalMultiplication]
  refine (Lp.memLp u).of_le_mul (c := max C 0)
    (hf.smul (Lp.aestronglyMeasurable u)) ?_
  filter_upwards [hC] with x hx
  by_cases hux : u x = 0
  · simp [hux]
  · rw [norm_smul]
    exact mul_le_mul_of_nonneg_right ((hx hux).trans (le_max_left _ _)) (norm_nonneg _)

/-- Sublevel set `{x | ‖hf.mk f x‖ ≤ n}` used to truncate vectors along `f`. -/
private def cutoffSet {f : α → 𝕜} (hf : AEStronglyMeasurable f μ) (n : ℕ) : Set α :=
  {x | ‖hf.mk f x‖ ≤ n}

private theorem mem_cutoffSet_iff {f : α → 𝕜} {hf : AEStronglyMeasurable f μ} {n : ℕ} {x : α} :
    x ∈ cutoffSet hf n ↔ ‖hf.mk f x‖ ≤ n :=
  Iff.rfl

private theorem measurableSet_cutoffSet {f : α → 𝕜} (hf : AEStronglyMeasurable f μ) (n : ℕ) :
    MeasurableSet (cutoffSet hf n) :=
  measurableSet_le hf.stronglyMeasurable_mk.norm.measurable measurable_const

omit [NormedSpace 𝕜 E] in
/-- Truncation of `u : Lp E p μ` to the sublevel set `{x | ‖hf.mk f x‖ ≤ n}`. -/
private def cutoffLp {f : α → 𝕜} (hf : AEStronglyMeasurable f μ) (n : ℕ)
    (u : Lp E p μ) : Lp E p μ :=
  ((Lp.memLp u).indicator (measurableSet_cutoffSet hf n).nullMeasurableSet).toLp
    ((cutoffSet hf n).indicator u)

omit [NormedSpace 𝕜 E] in
private theorem coeFn_cutoffLp {f : α → 𝕜} (hf : AEStronglyMeasurable f μ) (n : ℕ)
    (u : Lp E p μ) :
    cutoffLp hf n u =ᵐ[μ] (cutoffSet hf n).indicator u :=
  MemLp.coeFn_toLp _

private theorem cutoffLp_mem_boundedSupportSubmodule {f : α → 𝕜}
    (hf : AEStronglyMeasurable f μ) (n : ℕ) (u : Lp E p μ) :
    cutoffLp hf n u ∈ boundedSupportSubmodule p μ f := by
  refine mem_boundedSupportSubmodule_iff.2 ⟨n, ?_⟩
  filter_upwards [coeFn_cutoffLp hf n u, hf.ae_eq_mk] with x hcut hmk hne
  rw [hcut] at hne
  rw [hmk]
  exact mem_cutoffSet_iff.1 (Set.mem_of_indicator_ne_zero hne)

private theorem indicatorConstLp_mem_domain_of_subset_cutoffSet {f : α → 𝕜}
    (hf : AEStronglyMeasurable f μ) {n : ℕ} {s : Set α} (hs : MeasurableSet s)
    (hμs : μ s ≠ ∞) (hsub : s ⊆ cutoffSet hf n) (v : E) :
    indicatorConstLp p hs hμs v ∈ (maximalMultiplication (E := E) p μ f).domain := by
  refine boundedSupportSubmodule_le_domain hf (mem_boundedSupportSubmodule_iff.2 ⟨n, ?_⟩)
  filter_upwards [indicatorConstLp_coeFn (p := p) (hs := hs) (hμs := hμs) (c := v),
    hf.ae_eq_mk] with x hu hmk hne
  rw [hu] at hne
  rw [hmk]
  exact mem_cutoffSet_iff.1 (hsub (Set.mem_of_indicator_ne_zero hne))

/-- On a sigma-finite measure space with nontrivial fiber `E`, two almost-everywhere strongly
measurable symbols induce the same maximal multiplication operator if and only if they agree
almost everywhere. -/
theorem maximalMultiplication_eq_maximalMultiplication_iff [SigmaFinite μ] [Nontrivial E]
    {f g : α → 𝕜} (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) :
    maximalMultiplication (E := E) p μ f = maximalMultiplication (E := E) p μ g ↔ f =ᵐ[μ] g := by
  refine ⟨fun h ↦ ?_, maximalMultiplication_congr_ae⟩
  obtain ⟨v, hv⟩ := exists_ne (0 : E)
  have hlocal (m n : ℕ) :
      ∀ᵐ x ∂μ, x ∈ spanningSets μ m ∩ cutoffSet hf n ∩ cutoffSet hg n → f x = g x := by
    set s := spanningSets μ m ∩ cutoffSet hf n ∩ cutoffSet hg n
    have hs : MeasurableSet s :=
      ((measurableSet_spanningSets μ m).inter (measurableSet_cutoffSet hf n)).inter
        (measurableSet_cutoffSet hg n)
    have hμs : μ s ≠ ∞ :=
      ((measure_mono (Set.inter_subset_left.trans Set.inter_subset_left)).trans_lt
        (measure_spanningSets_lt_top μ m)).ne
    set u : Lp E p μ := indicatorConstLp p hs hμs v
    have huf := indicatorConstLp_mem_domain_of_subset_cutoffSet (p := p) hf hs hμs
      (fun _ hx ↦ hx.1.2) v
    have hug := indicatorConstLp_mem_domain_of_subset_cutoffSet (p := p) hg hs hμs
      (fun _ hx ↦ hx.2) v
    have heq_ae : maximalMultiplication p μ f ⟨u, huf⟩ =ᵐ[μ]
        maximalMultiplication p μ g ⟨u, hug⟩ := by
      rw [LinearPMap.congr_fun h huf hug]
    filter_upwards [coeFn_maximalMultiplication ⟨u, huf⟩, coeFn_maximalMultiplication ⟨u, hug⟩,
      heq_ae, indicatorConstLp_coeFn (p := p) (hs := hs) (hμs := hμs) (c := v)]
      with x hfx hgx hfgx hux hxs
    have hv_eq : f x • v = g x • v := by
      rw [← Set.indicator_of_mem hxs (fun _ ↦ v), ← hux, ← hfx, ← hgx]
      exact hfgx
    exact smul_left_injective 𝕜 hv hv_eq
  filter_upwards [ae_all_iff.2 fun m ↦ ae_all_iff.2 fun n ↦ hlocal m n] with x hall
  obtain ⟨m, hm⟩ := Set.mem_iUnion.1 (iUnion_spanningSets μ ▸ Set.mem_univ x)
  let n : ℕ := max ⌈‖hf.mk f x‖⌉₊ ⌈‖hg.mk g x‖⌉₊
  have hnf : x ∈ cutoffSet hf n :=
    mem_cutoffSet_iff.2 ((Nat.le_ceil _).trans (Nat.cast_le.2 (le_max_left _ _)))
  have hng : x ∈ cutoffSet hg n :=
    mem_cutoffSet_iff.2 ((Nat.le_ceil _).trans (Nat.cast_le.2 (le_max_right _ _)))
  exact hall m n ⟨⟨hm, hnf⟩, hng⟩

/-- On a sigma-finite measure space with nontrivial fiber `E`, the kernel of
`maximalMultiplication p μ f` for an almost-everywhere strongly measurable symbol `f` is trivial
if and only if `{x | f x = 0}` has measure zero. -/
theorem ker_maximalMultiplication_eq_bot_iff [SigmaFinite μ] [Nontrivial E]
    {f : α → 𝕜} (hf : AEStronglyMeasurable f μ) :
    (maximalMultiplication (E := E) p μ f).ker = ⊥ ↔ μ {x | f x = 0} = 0 := by
  rw [Submodule.eq_bot_iff, measure_eq_zero_iff_ae_notMem]
  constructor
  · intro hker
    obtain ⟨v, hv⟩ := exists_ne (0 : E)
    have hlocal (m : ℕ) : ∀ᵐ x ∂μ, x ∈ spanningSets μ m → f x ≠ 0 := by
      set s := spanningSets μ m ∩ {x | ‖hf.mk f x‖ = 0}
      have hs : MeasurableSet s :=
        (measurableSet_spanningSets μ m).inter
          (hf.stronglyMeasurable_mk.norm.measurable (measurableSet_singleton 0))
      have hμs : μ s ≠ ∞ :=
        ((measure_mono Set.inter_subset_left).trans_lt (measure_spanningSets_lt_top μ m)).ne
      set u : Lp E p μ := indicatorConstLp p hs hμs v
      have hu_ker : u ∈ (maximalMultiplication (E := E) p μ f).ker := by
        rw [mem_ker_maximalMultiplication_iff]
        filter_upwards [indicatorConstLp_coeFn (p := p) (hs := hs) (hμs := hμs) (c := v),
          hf.ae_eq_mk] with x hux hmk
        by_cases hxs : x ∈ s
        · exact Or.inl (hmk.trans (norm_eq_zero.1 hxs.2))
        · exact Or.inr (hux.trans (Set.indicator_of_notMem hxs _))
      have hu0 : u = 0 := hker u hu_ker
      filter_upwards [hu0 ▸ Lp.coeFn_zero E p μ,
        indicatorConstLp_coeFn (p := p) (hs := hs) (hμs := hμs) (c := v), hf.ae_eq_mk]
        with x h0 hux hmk hxm hfx0
      have hxs : x ∈ s := ⟨hxm, norm_eq_zero.2 (hmk.symm.trans hfx0)⟩
      exact hv ((Set.indicator_of_mem hxs (fun _ ↦ v)).symm.trans (hux.symm.trans h0))
    filter_upwards [ae_all_iff.2 hlocal] with x hx hfx
    obtain ⟨m, hm⟩ := Set.mem_iUnion.1 (iUnion_spanningSets μ ▸ Set.mem_univ x)
    exact hx m hm hfx
  · intro hne u hu
    refine Lp.ext ?_
    filter_upwards [mem_ker_maximalMultiplication_iff.1 hu, hne, Lp.coeFn_zero E p μ]
      with x hfx hne0 h0
    rcases hfx with hfx0 | hux0
    · exact False.elim (hne0 hfx0)
    · exact hux0.trans h0.symm

/-- On a sigma-finite measure space with nontrivial fiber `E`, `z` is not an eigenvalue of
`maximalMultiplication p μ f` (`ker (smulSub z ·) = ⊥`) if and only if `{x | f x = z}` is
`μ`-null. -/
theorem ker_smulSub_maximalMultiplication_eq_bot_iff [SigmaFinite μ] [Nontrivial E]
    {f : α → 𝕜} (hf : AEStronglyMeasurable f μ) (z : 𝕜) :
    LinearMap.ker ((maximalMultiplication (E := E) p μ f).smulSub z) = ⊥ ↔
      μ {x | f x = z} = 0 := by
  let g : α → 𝕜 := f - fun _ ↦ z
  have hset : {x | f x = z} = {x | g x = 0} := by
    ext x
    exact sub_eq_zero.symm
  have hshift : maximalMultiplication (E := E) p μ g =
      (maximalMultiplication (E := E) p μ f).subScalar z :=
    maximalMultiplication_sub_const f z
  rw [hset, ← ker_maximalMultiplication_eq_bot_iff (E := E) (p := p)
      (hf.sub aestronglyMeasurable_const), hshift, Submodule.eq_bot_iff, Submodule.eq_bot_iff]
  let T := maximalMultiplication (E := E) p μ f
  constructor
  · intro h u hu
    obtain ⟨w, rfl, hw0⟩ := LinearPMap.mem_ker_iff.1 hu
    rw [T.subScalar_apply, sub_eq_zero] at hw0
    let w' : T.domain := ⟨w, (T.subScalar_domain z) ▸ w.2⟩
    have hw' : w' ∈ LinearMap.ker (T.smulSub z) := by
      rw [LinearMap.mem_ker, T.smulSub_apply]
      exact sub_eq_zero.2 hw0.symm
    exact congrArg Subtype.val (h w' hw')
  · intro h u hu
    apply Subtype.ext
    refine h (u : Lp E p μ) (LinearPMap.mem_ker_iff.2 ?_)
    have hu_dom : (u : Lp E p μ) ∈ (T.subScalar z).domain := by
      rw [LinearPMap.subScalar_domain]
      exact u.2
    refine ⟨⟨u, hu_dom⟩, rfl, ?_⟩
    have hu0 : T.smulSub z u = 0 := hu
    rw [LinearPMap.smulSub_apply_eq_neg_subScalar, neg_eq_zero] at hu0
    exact hu0

private theorem maximalMultiplication_cutoffLp {f : α → 𝕜} (hf : AEStronglyMeasurable f μ)
    (n : ℕ) (u : (maximalMultiplication (E := E) p μ f).domain) :
    maximalMultiplication p μ f
        ⟨cutoffLp hf n (u : Lp E p μ), boundedSupportSubmodule_le_domain hf
          (cutoffLp_mem_boundedSupportSubmodule hf n (u : Lp E p μ))⟩ =
      cutoffLp hf n (maximalMultiplication p μ f u) := by
  refine maximalMultiplication_apply_eq_iff.2 ?_
  filter_upwards [coeFn_cutoffLp hf n (u : Lp E p μ),
    coeFn_cutoffLp hf n (maximalMultiplication p μ f u),
    coeFn_maximalMultiplication u] with x hcu hctu htu
  rw [hcu, hctu]
  by_cases hx : x ∈ cutoffSet hf n
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, htu]
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, smul_zero]

section NormedCutoff

variable [Fact (1 ≤ p)]

omit [NormedSpace 𝕜 E] in
private theorem tendsto_cutoffLp {f : α → 𝕜} (hf : AEStronglyMeasurable f μ)
    (hp : p ≠ ∞) (u : Lp E p μ) :
    Tendsto (fun n ↦ cutoffLp hf n u) atTop (𝓝 u) := by
  rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm']
  refine (TauCeti.tendsto_eLpNorm_sub_of_ae_tendsto (m := μ) (C := 1) hp
    (f := fun n ↦ (cutoffSet hf n).indicator u) (g := u)
    (Eventually.of_forall fun n ↦
      (Lp.aestronglyMeasurable u).indicator (measurableSet_cutoffSet hf n))
    (Lp.memLp u) ?_ ?_).congr fun n ↦
      eLpNorm_congr_ae ((coeFn_cutoffLp hf n u).sub Filter.EventuallyEq.rfl).symm
  · refine Eventually.of_forall fun n ↦ Eventually.of_forall fun x ↦ ?_
    by_cases hx : x ∈ cutoffSet hf n <;> simp [hx]
  · refine Eventually.of_forall fun x ↦ tendsto_atTop_of_eventually_const (i₀ := ⌈‖hf.mk f x‖⌉₊)
      fun n hn ↦ Set.indicator_of_mem
        (mem_cutoffSet_iff.2 ((Nat.le_ceil _).trans (Nat.cast_le.2 hn))) _

/-- When `f` is almost-everywhere strongly measurable and `p ≠ ∞`, `boundedSupportSubmodule p μ f`
is dense in `Lp E p μ`. -/
theorem dense_boundedSupportSubmodule {f : α → 𝕜} (hf : AEStronglyMeasurable f μ)
    (hp : p ≠ ∞) :
    Dense (boundedSupportSubmodule (E := E) p μ f : Set (Lp E p μ)) := by
  rw [dense_iff_closure_eq, Set.eq_univ_iff_forall]
  intro u
  exact mem_closure_of_tendsto (tendsto_cutoffLp hf hp u)
    (Eventually.of_forall fun n ↦ cutoffLp_mem_boundedSupportSubmodule hf n u)

/-- When `f` is almost-everywhere strongly measurable and `p ≠ ∞`, the domain of
`maximalMultiplication p μ f` is dense in `Lp E p μ`. -/
theorem dense_maximalMultiplication_domain {f : α → 𝕜} (hf : AEStronglyMeasurable f μ)
    (hp : p ≠ ∞) :
    Dense ((maximalMultiplication (E := E) p μ f).domain : Set (Lp E p μ)) :=
  (dense_boundedSupportSubmodule hf hp).mono (boundedSupportSubmodule_le_domain hf)

/-- When `f` is almost-everywhere strongly measurable and `p ≠ ∞`, the submodule of vectors of
`f`-bounded support is an operator core (`LinearPMap.HasCore`) for
`maximalMultiplication p μ f`. -/
theorem hasCore_boundedSupportSubmodule {f : α → 𝕜} (hf : AEStronglyMeasurable f μ)
    (hp : p ≠ ∞) :
    (maximalMultiplication (E := E) p μ f).HasCore (boundedSupportSubmodule p μ f) := by
  have hT_closed : (maximalMultiplication (E := E) p μ f).IsClosed :=
    isClosed_maximalMultiplication f
  refine (hT_closed.hasCore_iff_graph_subset_closure (boundedSupportSubmodule_le_domain hf)).2 ?_
  intro ⟨u₀, v₀⟩ hw
  obtain ⟨u, rfl, rfl⟩ := (maximalMultiplication (E := E) p μ f).mem_graph_iff.1 hw
  have hmem (n : ℕ) :
      (cutoffLp hf n (u : Lp E p μ), cutoffLp hf n (maximalMultiplication p μ f u)) ∈
        (((maximalMultiplication (E := E) p μ f).domRestrict
          (boundedSupportSubmodule p μ f)).graph : Set (Lp E p μ × Lp E p μ)) := by
    have hS_mem : cutoffLp hf n (u : Lp E p μ) ∈ boundedSupportSubmodule (E := E) p μ f :=
      cutoffLp_mem_boundedSupportSubmodule hf n (u : Lp E p μ)
    have hdom : cutoffLp hf n (u : Lp E p μ) ∈
        ((maximalMultiplication (E := E) p μ f).domRestrict
          (boundedSupportSubmodule p μ f)).domain := by
      rw [LinearPMap.domRestrict_domain, Submodule.mem_inf]
      exact ⟨hS_mem, boundedSupportSubmodule_le_domain hf hS_mem⟩
    refine ((maximalMultiplication (E := E) p μ f).domRestrict
      (boundedSupportSubmodule p μ f)).mem_graph_iff.2 ⟨⟨_, hdom⟩, rfl, ?_⟩
    exact ((maximalMultiplication (E := E) p μ f).domRestrict_apply (x := ⟨_, hdom⟩)
      (y := ⟨_, boundedSupportSubmodule_le_domain hf hS_mem⟩) rfl).trans
      (maximalMultiplication_cutoffLp hf n u)
  exact mem_closure_of_tendsto
    ((tendsto_cutoffLp hf hp (u : Lp E p μ)).prodMk_nhds
      (tendsto_cutoffLp hf hp (maximalMultiplication p μ f u)))
    (Eventually.of_forall hmem)

end NormedCutoff

end CutoffAndFaithful

/-! ### Star-symbol domain invariance, Hilbert-space adjoint, and self-adjointness -/

section StarDomain

variable {α 𝕜 E : Type*} [MeasurableSpace α] [NormedField 𝕜] [StarAddMonoid 𝕜]
  [NormedStarGroup 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] {p : ℝ≥0∞} {μ : Measure α}

private def starPairMap (q : {r : E × E // ∃ c : 𝕜, r.2 = c • r.1}) : E :=
  letI := Classical.propDecidable
  if q.1.1 = 0 then 0 else star q.2.choose • q.1.1

omit [NormedStarGroup 𝕜] in
private theorem starPairMap_apply {x : E} {c : 𝕜}
    (h : (x, c • x) ∈ {r : E × E | ∃ c : 𝕜, r.2 = c • r.1}) :
    starPairMap (𝕜 := 𝕜) ⟨(x, c • x), h⟩ = star c • x := by
  dsimp [starPairMap]
  split_ifs with hx
  · simp [hx]
  · rw [smul_left_injective 𝕜 hx h.choose_spec.symm]

private theorem continuous_starPairMap :
    Continuous (starPairMap (𝕜 := 𝕜) (E := E)) := by
  rw [Metric.continuous_iff]
  rintro ⟨⟨x₀, y₀⟩, hp₀⟩ ε hε
  obtain ⟨c₀, rfl⟩ : ∃ c₀ : 𝕜, y₀ = c₀ • x₀ := hp₀
  have hC : 0 < 1 + 2 * ‖c₀‖ := by positivity
  refine ⟨ε / (1 + 2 * ‖c₀‖), div_pos hε hC, ?_⟩
  rintro ⟨⟨x, y⟩, hp⟩ hdist
  obtain ⟨c, rfl⟩ : ∃ c : 𝕜, y = c • x := hp
  rw [starPairMap_apply, starPairMap_apply, _root_.dist_eq_norm]
  have hd : max ‖x - x₀‖ ‖c • x - c₀ • x₀‖ < ε / (1 + 2 * ‖c₀‖) := by
    simpa [Subtype.dist_eq, Prod.dist_eq, _root_.dist_eq_norm] using hdist
  have hx : ‖x - x₀‖ ≤ max ‖x - x₀‖ ‖c • x - c₀ • x₀‖ := le_max_left _ _
  have hy : ‖c • x - c₀ • x₀‖ ≤ max ‖x - x₀‖ ‖c • x - c₀ • x₀‖ := le_max_right _ _
  have hdiff : (c - c₀) • x = (c • x - c₀ • x₀) - c₀ • (x - x₀) := by
    rw [sub_smul, smul_sub, sub_sub_sub_cancel_right]
  have hbound : ‖star c • x - star c₀ • x₀‖ ≤
      (1 + 2 * ‖c₀‖) * max ‖x - x₀‖ ‖c • x - c₀ • x₀‖ := by
    calc ‖star c • x - star c₀ • x₀‖
        = ‖(star c - star c₀) • x + star c₀ • (x - x₀)‖ := by
          rw [sub_smul, smul_sub, sub_add_sub_cancel]
      _ ≤ ‖(star c - star c₀) • x‖ + ‖star c₀ • (x - x₀)‖ := norm_add_le _ _
      _ = ‖star (c - c₀)‖ * ‖x‖ + ‖star c₀‖ * ‖x - x₀‖ := by
          rw [← star_sub, norm_smul, norm_smul]
      _ = ‖(c - c₀) • x‖ + ‖c₀‖ * ‖x - x₀‖ := by
          rw [norm_star, norm_star, ← norm_smul]
      _ ≤ (‖c • x - c₀ • x₀‖ + ‖c₀ • (x - x₀)‖) + ‖c₀‖ * ‖x - x₀‖ := by
          gcongr; rw [hdiff]; exact norm_sub_le _ _
      _ = ‖c • x - c₀ • x₀‖ + 2 * ‖c₀‖ * ‖x - x₀‖ := by
          rw [norm_smul]; ring
      _ ≤ 1 * max ‖x - x₀‖ ‖c • x - c₀ • x₀‖ +
          2 * ‖c₀‖ * max ‖x - x₀‖ ‖c • x - c₀ • x₀‖ := by
          gcongr; linarith
      _ = (1 + 2 * ‖c₀‖) * max ‖x - x₀‖ ‖c • x - c₀ • x₀‖ := by ring
  exact hbound.trans_lt ((lt_div_iff₀' hC).1 hd)

private theorem memLp_star_smul_of_memLp {f : α → 𝕜} {u : α → E}
    (hu : AEStronglyMeasurable u μ) (hfu : MemLp (fun t ↦ f t • u t) p μ) :
    MemLp (fun t ↦ star (f t) • u t) p μ := by
  let g : α → {r : E × E // ∃ c : 𝕜, r.2 = c • r.1} :=
    fun t ↦ ⟨(u t, f t • u t), f t, rfl⟩
  have hg : AEStronglyMeasurable g μ :=
    Topology.IsEmbedding.subtypeVal.aestronglyMeasurable_comp_iff.1
      (hu.prodMk hfu.aestronglyMeasurable)
  have haesm : AEStronglyMeasurable (fun t ↦ star (f t) • u t) μ :=
    (continuous_starPairMap.comp_aestronglyMeasurable hg).congr
      (Eventually.of_forall fun _ ↦ starPairMap_apply _)
  refine hfu.of_le_mul (c := 1) haesm (Eventually.of_forall fun t ↦ ?_)
  rw [one_mul, norm_smul, norm_smul, norm_star]

/-- Over a normed field `𝕜` with a norm-preserving additive star involution,
`maximalMultiplication p μ (star f)` has the same domain as `maximalMultiplication p μ f` for
every symbol `f : α → 𝕜` and every normed `𝕜`-space `E`. -/
@[simp]
theorem domain_maximalMultiplication_star (f : α → 𝕜) :
    (maximalMultiplication (E := E) p μ (star f)).domain =
      (maximalMultiplication (E := E) p μ f).domain := by
  ext u
  simp only [mem_domain_maximalMultiplication, Pi.star_apply]
  exact ⟨fun h ↦ star_star f ▸
      memLp_star_smul_of_memLp (f := star f) (Lp.aestronglyMeasurable u) h,
    memLp_star_smul_of_memLp (Lp.aestronglyMeasurable u)⟩

end StarDomain

section Hilbert

variable {α 𝕜 E : Type*} [MeasurableSpace α] [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] {μ : Measure α}

/-- `maximalMultiplication 2 μ (star f)` is a formal adjoint of `maximalMultiplication 2 μ f` on
`Lp E 2 μ`, with no measurability, completeness, or sigma-finiteness assumptions. -/
theorem isFormalAdjoint_maximalMultiplication (f : α → 𝕜) :
    (maximalMultiplication (E := E) 2 μ f).IsFormalAdjoint
      (maximalMultiplication (E := E) 2 μ (star f)) := by
  intro x y
  rw [L2.inner_def, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_maximalMultiplication x, coeFn_maximalMultiplication y] with t hx hy
  rw [hx, hy, inner_smul_left, inner_smul_right, Pi.star_apply, RCLike.star_def]

private theorem indicator_ae_of_forall_inner_eq {f : α → 𝕜} (hf : AEStronglyMeasurable f μ)
    {v w : Lp E 2 μ}
    (hadj : ∀ x : (maximalMultiplication (E := E) 2 μ f).domain,
      ⟪w, (x : Lp E 2 μ)⟫_𝕜 = ⟪v, maximalMultiplication 2 μ f x⟫_𝕜)
    (n : ℕ) :
    (cutoffSet hf n).indicator w =ᵐ[μ]
      (cutoffSet hf n).indicator (fun t ↦ star (f t) • v t) := by
  have hz : MemLp ((cutoffSet hf n).indicator (fun t ↦ star (f t) • v t)) 2 μ := by
    refine (Lp.memLp v).of_le_mul (c := n)
      ((hf.star.smul (Lp.aestronglyMeasurable v)).indicator (measurableSet_cutoffSet hf n)) ?_
    filter_upwards [hf.ae_eq_mk] with t hmk
    by_cases ht : t ∈ cutoffSet hf n
    · rw [Set.indicator_of_mem ht, norm_smul, norm_star, hmk]
      exact mul_le_mul_of_nonneg_right (mem_cutoffSet_iff.1 ht) (norm_nonneg _)
    · rw [Set.indicator_of_notMem ht, _root_.norm_zero]
      positivity
  have hinner : cutoffLp hf n w = hz.toLp _ := by
    refine ext_inner_right 𝕜 fun u ↦ ?_
    have hu_dom : cutoffLp hf n u ∈ (maximalMultiplication (E := E) 2 μ f).domain :=
      boundedSupportSubmodule_le_domain hf (cutoffLp_mem_boundedSupportSubmodule hf n u)
    have h1 : ⟪cutoffLp hf n w, u⟫_𝕜 = ⟪w, cutoffLp hf n u⟫_𝕜 := by
      rw [L2.inner_def, L2.inner_def]
      refine integral_congr_ae ?_
      filter_upwards [coeFn_cutoffLp hf n w, coeFn_cutoffLp hf n u] with t hw' hu'
      rw [hw', hu']
      by_cases ht : t ∈ cutoffSet hf n <;> simp [ht]
    have h2 : ⟪v, maximalMultiplication 2 μ f ⟨cutoffLp hf n u, hu_dom⟩⟫_𝕜 = ⟪hz.toLp _, u⟫_𝕜 := by
      rw [L2.inner_def, L2.inner_def]
      refine integral_congr_ae ?_
      filter_upwards [coeFn_maximalMultiplication ⟨cutoffLp hf n u, hu_dom⟩,
        coeFn_cutoffLp hf n u, hz.coeFn_toLp] with t hTu hu' hz'
      rw [hTu, hu', hz']
      by_cases ht : t ∈ cutoffSet hf n
      · simp [ht, inner_smul_left, inner_smul_right, RCLike.star_def]
      · simp [ht]
    exact h1.trans ((hadj ⟨cutoffLp hf n u, hu_dom⟩).trans h2)
  exact (coeFn_cutoffLp hf n w).symm.trans (hinner ▸ hz.coeFn_toLp)

section Complete

variable [CompleteSpace E]

/-- On `Lp E 2 μ` for any measure `μ`, the Hilbert adjoint of `maximalMultiplication 2 μ f` for an
almost-everywhere strongly measurable symbol `f` is `maximalMultiplication 2 μ (star f)`. -/
@[simp]
theorem adjoint_maximalMultiplication {f : α → 𝕜} (hf : AEStronglyMeasurable f μ) :
    (maximalMultiplication (E := E) 2 μ f).adjoint =
      maximalMultiplication (E := E) 2 μ (star f) := by
  set T := maximalMultiplication (E := E) 2 μ f
  set S := maximalMultiplication (E := E) 2 μ (star f)
  have hdense : Dense (T.domain : Set (Lp E 2 μ)) :=
    dense_maximalMultiplication_domain hf ENNReal.ofNat_ne_top
  have hle : S ≤ T.adjoint :=
    (isFormalAdjoint_maximalMultiplication (E := E) (μ := μ) f).le_adjoint hdense
  refine (LinearPMap.eq_of_le_of_domain_eq hle (le_antisymm hle.1 fun v hv ↦ ?_)).symm
  set w : Lp E 2 μ := T.adjoint ⟨v, hv⟩
  have hadj : ∀ x : T.domain, ⟪w, (x : Lp E 2 μ)⟫_𝕜 = ⟪v, T x⟫_𝕜 :=
    T.adjoint_isFormalAdjoint hdense ⟨v, hv⟩
  have hglobal : w =ᵐ[μ] fun t ↦ star (f t) • v t := by
    filter_upwards [ae_all_iff.2 (indicator_ae_of_forall_inner_eq hf hadj)] with t ht
    have hmem : t ∈ cutoffSet hf ⌈‖hf.mk f t‖⌉₊ := mem_cutoffSet_iff.2 (Nat.le_ceil _)
    simpa [Set.indicator_of_mem hmem] using ht ⌈‖hf.mk f t‖⌉₊
  exact mem_domain_maximalMultiplication.2 ((Lp.memLp w).ae_eq hglobal)

/-- The Hilbert adjoint of `maximalMultiplication 2 μ f` has the same domain as
`maximalMultiplication 2 μ f` when `f` is almost-everywhere strongly measurable. -/
theorem adjoint_maximalMultiplication_domain {f : α → 𝕜} (hf : AEStronglyMeasurable f μ) :
    (maximalMultiplication (E := E) 2 μ f).adjoint.domain =
      (maximalMultiplication (E := E) 2 μ f).domain := by
  rw [adjoint_maximalMultiplication hf, domain_maximalMultiplication_star f]

/-- `maximalMultiplication 2 μ f` is metrically normal on its domain: its adjoint has the same
domain and the same norm at every vector of that domain. -/
theorem norm_adjoint_maximalMultiplication_apply {f : α → 𝕜} (hf : AEStronglyMeasurable f μ)
    (u : (maximalMultiplication (E := E) 2 μ f).domain) :
    ‖(maximalMultiplication (E := E) 2 μ f).adjoint
        ⟨(u : Lp E 2 μ), by rw [adjoint_maximalMultiplication_domain hf]; exact u.2⟩‖ =
      ‖maximalMultiplication (E := E) 2 μ f u‖ := by
  have hu_star : (u : Lp E 2 μ) ∈ (maximalMultiplication (E := E) 2 μ (star f)).domain := by
    rw [domain_maximalMultiplication_star f]
    exact u.2
  have heq : (maximalMultiplication (E := E) 2 μ f).adjoint
      ⟨(u : Lp E 2 μ), by rw [adjoint_maximalMultiplication_domain hf]; exact u.2⟩ =
      maximalMultiplication (E := E) 2 μ (star f) ⟨(u : Lp E 2 μ), hu_star⟩ :=
    LinearPMap.congr_fun (adjoint_maximalMultiplication hf) _ _
  rw [heq]
  have hnorm : ∀ᵐ t ∂μ,
      ‖(maximalMultiplication (E := E) 2 μ (star f) ⟨(u : Lp E 2 μ), hu_star⟩) t‖ =
        ‖(maximalMultiplication (E := E) 2 μ f u) t‖ := by
    filter_upwards [coeFn_maximalMultiplication ⟨(u : Lp E 2 μ), hu_star⟩,
      coeFn_maximalMultiplication u] with t h₁ h₂
    rw [h₁, h₂, Pi.star_apply, norm_smul, norm_smul, norm_star]
  exact le_antisymm (Lp.norm_le_norm_of_ae_le (hnorm.mono fun _ h ↦ h.le))
    (Lp.norm_le_norm_of_ae_le (hnorm.mono fun _ h ↦ h.ge))

/-- An almost-everywhere strongly measurable symbol satisfying `star (f t) = f t` almost everywhere
induces a self-adjoint maximal multiplication operator on `Lp E 2 μ`, for any measure `μ`. -/
theorem isSelfAdjoint_maximalMultiplication {f : α → 𝕜} (hf : AEStronglyMeasurable f μ)
    (hreal : ∀ᵐ t ∂μ, star (f t) = f t) :
    IsSelfAdjoint (maximalMultiplication (E := E) 2 μ f) := by
  rw [LinearPMap.isSelfAdjoint_def, adjoint_maximalMultiplication hf]
  exact maximalMultiplication_congr_ae hreal

/-- On a sigma-finite measure space with nontrivial fiber `E`, `maximalMultiplication 2 μ f` is
self-adjoint if and only if `star (f t) = f t` almost everywhere. -/
theorem isSelfAdjoint_maximalMultiplication_iff [SigmaFinite μ] [Nontrivial E]
    {f : α → 𝕜} (hf : AEStronglyMeasurable f μ) :
    IsSelfAdjoint (maximalMultiplication (E := E) 2 μ f) ↔ ∀ᵐ t ∂μ, star (f t) = f t := by
  rw [LinearPMap.isSelfAdjoint_def, adjoint_maximalMultiplication hf,
    maximalMultiplication_eq_maximalMultiplication_iff hf.star hf]
  rfl

/-- **Existence and uniqueness of the maximal `L²` multiplier.** Every almost-everywhere strongly
measurable scalar symbol `f : α → 𝕜` on any measure space `(α, μ)` has a unique maximal partial
linear realization on `Lp E 2 μ`; it is densely defined and closed, and is self-adjoint whenever
`f` is self-conjugate almost everywhere. -/
theorem existsUnique_maximalMultiplication {f : α → 𝕜} (hf : AEStronglyMeasurable f μ) :
    ∃! T : Lp E 2 μ →ₗ.[𝕜] Lp E 2 μ,
      (∀ x : Lp E 2 μ, x ∈ T.domain ↔ MemLp (fun t ↦ f t • x t) 2 μ) ∧
      (∀ x : T.domain, ∀ᵐ t ∂μ, (T x) t = f t • (x : Lp E 2 μ) t) ∧
      Dense (T.domain : Set (Lp E 2 μ)) ∧ T.IsClosed ∧
      ((∀ᵐ t ∂μ, star (f t) = f t) → IsSelfAdjoint T) := by
  refine ⟨maximalMultiplication (E := E) 2 μ f,
    ⟨fun _ ↦ mem_domain_maximalMultiplication,
      coeFn_maximalMultiplication,
      dense_maximalMultiplication_domain hf ENNReal.ofNat_ne_top,
      isClosed_maximalMultiplication f,
      isSelfAdjoint_maximalMultiplication hf⟩,
    fun T ⟨hdom, hae, _, _, _⟩ ↦ eq_maximalMultiplication_of_domain_of_ae hdom hae⟩

end Complete

end Hilbert

/-! ### Resolvent and essential-range spectrum -/

section Resolvent

variable {α 𝕜 E : Type*} [MeasurableSpace α] [NormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] {p : ℝ≥0∞} [Fact (1 ≤ p)] {μ : Measure α}

/-- Bounded `Lᵖ` scalar multiplication by an `L∞` class, used to exhibit the reciprocal resolvent
without requiring `NontriviallyNormedField 𝕜`. -/
private def linftySmulCLM (a : Lp 𝕜 ∞ μ) : Lp E p μ →L[𝕜] Lp E p μ where
  toFun u := a • u
  map_add' u v := Lp.add_smul a u v
  map_smul' c u := (Lp.smul_comm c a u).symm
  cont := by
    refine LipschitzWith.continuous (K := ‖a‖₊) (lipschitzWith_iff_dist_le_mul.2 fun u v ↦ ?_)
    have hsub : (a • u : Lp E p μ) - a • v = a • (u - v) := by
      rw [sub_eq_add_neg, sub_eq_add_neg, ← Lp.smul_neg, Lp.add_smul]
    rw [_root_.dist_eq_norm, _root_.dist_eq_norm, hsub, coe_nnNorm]
    exact Lp.norm_smul_le a (u - v)

private theorem coeFn_linftySmulCLM (a : Lp 𝕜 ∞ μ) (u : Lp E p μ) :
    linftySmulCLM (p := p) a u =ᵐ[μ] fun x ↦ a x • u x :=
  coeFn_lpSMul a u

omit [NormedAddCommGroup E] [NormedSpace 𝕜 E] [Fact (1 ≤ p)] in
private theorem memLp_inv_sub_of_ae_le {f : α → 𝕜} (hf : AEStronglyMeasurable f μ)
    {z : 𝕜} {ε : ℝ} (hε : 0 < ε) (hbound : ∀ᵐ x ∂μ, ε ≤ ‖f x - z‖) :
    MemLp (fun x ↦ (z - f x)⁻¹) ∞ μ := by
  refine memLp_top_of_bound (aestronglyMeasurable_const.sub hf).inv₀ ε⁻¹ ?_
  filter_upwards [hbound] with x hx
  rw [norm_inv, norm_sub_rev]
  exact inv_anti₀ hε hx

private theorem isResolventAt_linftySmulCLM {f : α → 𝕜} (hf : AEStronglyMeasurable f μ)
    {z : 𝕜} {ε : ℝ} (hε : 0 < ε) (hbound : ∀ᵐ x ∂μ, ε ≤ ‖f x - z‖) :
    LinearPMap.IsResolventAt (maximalMultiplication (E := E) p μ f) z
      (linftySmulCLM (E := E) (p := p) ((memLp_inv_sub_of_ae_le hf hε hbound).toLp _)) := by
  set hg := memLp_inv_sub_of_ae_le hf hε hbound
  set R := linftySmulCLM (E := E) (p := p) (hg.toLp _)
  refine LinearPMap.isResolventAt_iff_forall_mem_graph.2 ⟨fun y ↦ ?_, fun ⟨u₀, v₀⟩ hq ↦ ?_⟩
  · rw [mem_graph_maximalMultiplication_iff]
    filter_upwards [coeFn_linftySmulCLM (E := E) (p := p) (hg.toLp _) y, hg.coeFn_toLp,
      Lp.coeFn_sub (z • R y) y, Lp.coeFn_smul z (R y), hbound]
      with x hRy hgx hsub hsmul hx
    have hne : z - f x ≠ 0 := norm_pos_iff.1 (hε.trans_le (norm_sub_rev (f x) z ▸ hx))
    rw [hsub, Pi.sub_apply, hsmul, Pi.smul_apply, hRy, hgx]
    calc z • ((z - f x)⁻¹ • y x) - y x
        = (z * (z - f x)⁻¹ - (z - f x) * (z - f x)⁻¹) • y x := by
          rw [mul_inv_cancel₀ hne, sub_smul, one_smul, mul_smul]
      _ = f x • ((z - f x)⁻¹ • y x) := by
          rw [← sub_mul, sub_sub_cancel, mul_smul]
  · refine Lp.ext ?_
    filter_upwards [coeFn_linftySmulCLM (E := E) (p := p) (hg.toLp _) (z • u₀ - v₀),
      hg.coeFn_toLp, Lp.coeFn_sub (z • u₀) v₀, Lp.coeFn_smul z u₀,
      mem_graph_maximalMultiplication_iff.1 hq, hbound]
      with x hRw hgx hsub hsmul hqx hx
    have hne : z - f x ≠ 0 := norm_pos_iff.1 (hε.trans_le (norm_sub_rev (f x) z ▸ hx))
    rw [hRw, hgx, hsub, Pi.sub_apply, hsmul, Pi.smul_apply, hqx]
    calc (z - f x)⁻¹ • (z • u₀ x - f x • u₀ x)
        = ((z - f x)⁻¹ * (z - f x)) • u₀ x := by rw [← sub_smul, smul_smul]
      _ = u₀ x := by rw [inv_mul_cancel₀ hne, one_smul]

/-- When `f - z` is bounded away from zero almost everywhere by `ε > 0`, `z` belongs to the
resolvent set of `maximalMultiplication p μ f`. -/
theorem mem_resolventSet_maximalMultiplication_of_ae_le_norm_sub {f : α → 𝕜}
    (hf : AEStronglyMeasurable f μ) {z : 𝕜} {ε : ℝ} (hε : 0 < ε)
    (hbound : ∀ᵐ x ∂μ, ε ≤ ‖f x - z‖) :
    z ∈ (maximalMultiplication (E := E) p μ f).resolventSet :=
  (isResolventAt_linftySmulCLM hf hε hbound).mem_resolventSet

/-- When `f - z` is bounded away from zero almost everywhere by `ε > 0`, the resolvent of
`maximalMultiplication p μ f` at `z` acts almost everywhere as pointwise multiplication by
`(z - f)⁻¹`. -/
theorem resolvent_maximalMultiplication_ae {f : α → 𝕜} (hf : AEStronglyMeasurable f μ)
    {z : 𝕜} {ε : ℝ} (hε : 0 < ε) (hbound : ∀ᵐ x ∂μ, ε ≤ ‖f x - z‖) (y : Lp E p μ) :
    (maximalMultiplication (E := E) p μ f).resolvent z y =ᵐ[μ]
      fun x ↦ (z - f x)⁻¹ • y x := by
  rw [LinearPMap.resolvent_eq_of_isResolventAt (isResolventAt_linftySmulCLM hf hε hbound)]
  filter_upwards [coeFn_linftySmulCLM (E := E) (p := p)
      ((memLp_inv_sub_of_ae_le hf hε hbound).toLp _) y,
    (memLp_inv_sub_of_ae_le hf hε hbound).coeFn_toLp] with x hRy hgx
  rw [hRy, hgx]

omit [Fact (1 ≤ p)] in
private theorem norm_smul_sub_indicatorConstLp_le {f : α → 𝕜} (hf : AEStronglyMeasurable f μ)
    {z : 𝕜} {ε : ℝ} {t : Set α} (ht : MeasurableSet t) (hμt : μ t ≠ ∞)
    (hts : ∀ x ∈ t, ‖hf.mk f x - z‖ < ε) (v : E)
    (hu_dom : indicatorConstLp p ht hμt v ∈ (maximalMultiplication (E := E) p μ f).domain) :
    ‖z • indicatorConstLp p ht hμt v -
        maximalMultiplication p μ f ⟨indicatorConstLp p ht hμt v, hu_dom⟩‖ ≤
      ε * ‖indicatorConstLp p ht hμt v‖ := by
  set u : Lp E p μ := indicatorConstLp p ht hμt v
  refine Lp.norm_le_mul_norm_of_ae_le_mul ?_
  filter_upwards [Lp.coeFn_sub (z • u) (maximalMultiplication p μ f ⟨u, hu_dom⟩),
    Lp.coeFn_smul z u, coeFn_maximalMultiplication ⟨u, hu_dom⟩,
    indicatorConstLp_coeFn (p := p) (hs := ht) (hμs := hμt) (c := v),
    hf.ae_eq_mk] with x hsub hsmul hMf hux hmk
  rw [hsub, Pi.sub_apply, hsmul, Pi.smul_apply, hMf, ← sub_smul, norm_smul, norm_sub_rev]
  by_cases hxt : x ∈ t
  · exact mul_le_mul_of_nonneg_right (hmk ▸ (hts x hxt).le) (norm_nonneg _)
  · rw [hux, Set.indicator_of_notMem hxt]
    simp

end Resolvent

section NontrivialFieldResolvent

variable {α 𝕜 E : Type*} [MeasurableSpace α] [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] {p : ℝ≥0∞} [Fact (1 ≤ p)] {μ : Measure α}

/-- When `f - z` is bounded away from zero almost everywhere by `ε > 0` over a nontrivially normed
field, the operator norm of the resolvent at `z` is at most `ε⁻¹`. -/
theorem norm_resolvent_maximalMultiplication_le {f : α → 𝕜} (hf : AEStronglyMeasurable f μ)
    {z : 𝕜} {ε : ℝ} (hε : 0 < ε) (hbound : ∀ᵐ x ∂μ, ε ≤ ‖f x - z‖) :
    ‖(maximalMultiplication (E := E) p μ f).resolvent z‖ ≤ ε⁻¹ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.2 hε.le) fun y ↦
    Lp.norm_le_mul_norm_of_ae_le_mul ?_
  filter_upwards [resolvent_maximalMultiplication_ae hf hε hbound y, hbound] with x hRy hx
  rw [hRy, norm_smul, norm_inv, norm_sub_rev]
  exact mul_le_mul_of_nonneg_right (inv_anti₀ hε hx) (norm_nonneg _)

private theorem exists_measure_lt_norm_sub_eq_zero_of_nontrivial [SigmaFinite μ] [Nontrivial E]
    {f : α → 𝕜} (hf : AEStronglyMeasurable f μ) {z : 𝕜} {R : Lp E p μ →L[𝕜] Lp E p μ}
    (hR : ∀ u : (maximalMultiplication (E := E) p μ f).domain,
      R (z • (u : Lp E p μ) - maximalMultiplication p μ f u) = u) :
    ∃ ε > 0, μ {x | ‖f x - z‖ < ε} = 0 := by
  have hR_pos : 0 < ‖R‖ + 1 := add_pos_of_nonneg_of_pos (norm_nonneg R) zero_lt_one
  set ε : ℝ := (‖R‖ + 1)⁻¹
  refine ⟨ε, inv_pos.2 hR_pos, ?_⟩
  by_contra hμ
  set s : Set α := {x | ‖hf.mk f x - z‖ < ε}
  have hs : MeasurableSet s :=
    measurableSet_lt
      (hf.stronglyMeasurable_mk.sub stronglyMeasurable_const).norm.measurable measurable_const
  have hs_ae : s =ᵐ[μ] {x | ‖f x - z‖ < ε} :=
    eventuallyEqSet_iff.2 (hf.ae_eq_mk.symm.mono fun x hx ↦ by dsimp [s]; rw [hx])
  obtain ⟨t, ht, hts, hμt_pos, hμt_top⟩ :=
    Measure.exists_subset_measure_lt_top hs (pos_iff_ne_zero.2 (measure_congr hs_ae ▸ hμ))
  obtain ⟨v, hv⟩ := exists_ne (0 : E)
  set u : Lp E p μ := indicatorConstLp p ht hμt_top.ne v
  have hu_pos : 0 < ‖u‖ := norm_pos_iff.2 fun hu0 ↦
    hμt_pos.ne' (measure_eq_zero_iff_ae_notMem.2 <| by
      filter_upwards [hu0 ▸ Lp.coeFn_zero E p μ,
        indicatorConstLp_coeFn (p := p) (hs := ht) (hμs := hμt_top.ne) (c := v)]
        with x h0 hux hxt
      exact hv ((Set.indicator_of_mem hxt (fun _ ↦ v)).symm.trans (hux.symm.trans h0)))
  have hu_dom : u ∈ (maximalMultiplication (E := E) p μ f).domain := by
    refine indicatorConstLp_mem_domain_of_subset_cutoffSet (n := ⌈ε + ‖z‖⌉₊) hf ht hμt_top.ne
      (fun x hxt ↦ mem_cutoffSet_iff.2 ?_) v
    have htri : ‖hf.mk f x‖ ≤ ‖hf.mk f x - z‖ + ‖z‖ := by
      simpa only [sub_add_cancel] using norm_add_le (hf.mk f x - z) z
    exact (htri.trans (add_le_add (hts hxt).le le_rfl)).trans (Nat.le_ceil _)
  have hshift := norm_smul_sub_indicatorConstLp_le hf ht hμt_top.ne (fun _ hx ↦ hts hx) v hu_dom
  have hround : 1 * ‖u‖ ≤ (‖R‖ * ε) * ‖u‖ := by
    calc 1 * ‖u‖ = ‖R (z • u - maximalMultiplication p μ f ⟨u, hu_dom⟩)‖ := by
          rw [one_mul, hR ⟨u, hu_dom⟩]
      _ ≤ ‖R‖ * ‖z • u - maximalMultiplication p μ f ⟨u, hu_dom⟩‖ := R.le_opNorm _
      _ ≤ ‖R‖ * (ε * ‖u‖) := mul_le_mul_of_nonneg_left hshift (norm_nonneg R)
      _ = (‖R‖ * ε) * ‖u‖ := (mul_assoc _ _ _).symm
  exact not_lt_of_ge (le_of_mul_le_mul_right hround hu_pos)
    ((mul_inv_lt_iff₀ hR_pos).2 (by linarith))

end NontrivialFieldResolvent

section Spectrum

variable {α 𝕜 E : Type*} [MeasurableSpace α] [NormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] {p : ℝ≥0∞} [Fact (1 ≤ p)] {μ : Measure α}

/-- On a sigma-finite measure space with nontrivial fiber `E`, `z` belongs to the resolvent set of
`maximalMultiplication p μ f` for an almost-everywhere strongly measurable symbol `f` if and only
if `{x | ‖f x - z‖ < ε}` is `μ`-null for some `ε > 0`. -/
theorem mem_resolventSet_maximalMultiplication_iff [SigmaFinite μ] [Nontrivial E]
    {f : α → 𝕜} (hf : AEStronglyMeasurable f μ) (z : 𝕜) :
    z ∈ (maximalMultiplication (E := E) p μ f).resolventSet ↔
      ∃ ε > 0, μ {x | ‖f x - z‖ < ε} = 0 := by
  refine ⟨fun hz ↦ ?_, fun ⟨ε, hε, hμ⟩ ↦ ?_⟩
  · by_cases htriv : ∀ a : 𝕜, a ≠ 0 → ‖a‖ = 1
    · refine ⟨1 / 2, by positivity, ?_⟩
      have hset : {x | ‖f x - z‖ < 1 / 2} = {x | f x = z} := by
        ext x
        simp only [Set.mem_ofPred_eq]
        refine ⟨fun hlt ↦ sub_eq_zero.1 ?_, fun heq ↦ by simp [heq]⟩
        by_contra hne
        linarith [htriv _ hne]
      rw [hset, ← ker_smulSub_maximalMultiplication_eq_bot_iff (E := E) (p := p) hf z,
        LinearMap.ker_eq_bot]
      intro u v huv
      exact (LinearPMap.smul_sub_bijective hz).injective
        (((maximalMultiplication p μ f).smulSub_apply z u).symm.trans
          (huv.trans ((maximalMultiplication p μ f).smulSub_apply z v)))
    · push Not at htriv
      obtain ⟨a, ha0, ha1⟩ := htriv
      have hnt : ∃ c : 𝕜, 1 < ‖c‖ := by
        rcases lt_or_gt_of_ne ha1 with hlt | hgt
        · exact ⟨a⁻¹, by rw [norm_inv]; exact (one_lt_inv₀ (norm_pos_iff.2 ha0)).2 hlt⟩
        · exact ⟨a, hgt⟩
      let inst : NontriviallyNormedField 𝕜 := { toNormedField := ‹_›, non_trivial := hnt }
      exact exists_measure_lt_norm_sub_eq_zero_of_nontrivial (𝕜 := 𝕜) hf
        (LinearPMap.isResolventAt_resolvent hz).apply_smul_sub
  · refine mem_resolventSet_maximalMultiplication_of_ae_le_norm_sub hf hε ?_
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hμ] with x hx
    exact not_lt.1 hx

/-- **Essential-range spectrum of a maximal multiplication operator.** On a sigma-finite measure
space with nontrivial fiber `E`, for every `1 ≤ p ≤ ∞` and almost-everywhere strongly measurable
symbol `f : α → 𝕜`, the spectrum of `maximalMultiplication p μ f` is the measure-theoretic
essential range `{z : 𝕜 | ∀ ε > 0, μ {x | ‖f x - z‖ < ε} ≠ 0}`. -/
theorem spectrum_maximalMultiplication [SigmaFinite μ] [Nontrivial E]
    {f : α → 𝕜} (hf : AEStronglyMeasurable f μ) :
    (maximalMultiplication (E := E) p μ f).spectrum =
      {z : 𝕜 | ∀ ε > 0, μ {x | ‖f x - z‖ < ε} ≠ 0} := by
  ext z
  simp only [LinearPMap.mem_spectrum_iff, mem_resolventSet_maximalMultiplication_iff (E := E) hf,
    Set.mem_ofPred_eq, not_exists, not_and]

end Spectrum

end MeasureTheory.Lp
