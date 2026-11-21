/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.LinearPMap
public import TauCeti.LinearAlgebra.LinearPMap.SmulSub
public import TauCeti.MeasureTheory.Function.Lp.Multiplication.Basic
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import TauCeti.LinearAlgebra.LinearPMap.Basic
import TauCeti.MeasureTheory.Function.Lp.DominatedConvergence
import TauCeti.MeasureTheory.Function.Lp.Indicator
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

For the resolvent and essential-range spectrum of `MeasureTheory.Lp.maximalMultiplication`, see
`TauCeti.MeasureTheory.Function.Lp.MaximalMultiplication.Spectrum`.

## Main definitions

* `MeasureTheory.Lp.maximalMultiplication p μ f`: the maximal partial linear operator of
  multiplication by `f : α → 𝕜` on `Lp E p μ`.
* `MeasureTheory.Lp.boundedOnSupportSubmodule p μ f`: the submodule of vectors `u : Lp E p μ` on
  whose support `f` is almost everywhere bounded (vanishing almost everywhere outside a set on which
  `f` is bounded).

## Main results

* `MeasureTheory.Lp.mem_graph_maximalMultiplication_iff`: `(u, v)` belongs to the graph of
  `maximalMultiplication p μ f` if and only if `v =ᵐ[μ] fun x ↦ f x • u x`.
* `MeasureTheory.Lp.maximalMultiplication_eq_maximalMultiplication_iff`: on a sigma-finite space
  with nontrivial fiber `E`, two almost-everywhere strongly measurable multipliers induce the same
  maximal operator if and only if they agree almost everywhere.
* `MeasureTheory.Lp.isClosed_maximalMultiplication`: `maximalMultiplication p μ f` is closed for
  every `1 ≤ p ≤ ∞`, every measure `μ`, and every symbol `f`.
* `MeasureTheory.Lp.dense_domain_maximalMultiplication` and
  `MeasureTheory.Lp.hasCore_maximalMultiplication_boundedOnSupportSubmodule`: when `f` is
  almost-everywhere strongly measurable and `p ≠ ∞`, `boundedOnSupportSubmodule p μ f` is a dense
  operator core for `maximalMultiplication p μ f`, so its maximal domain is dense in `Lp E p μ`.
* `MeasureTheory.Lp.adjoint_maximalMultiplication`: on `Lp E 2 μ` for a complete inner-product
  space `E` over `𝕜` (`[RCLike 𝕜]`) and any measure `μ`, the Hilbert adjoint of
  `maximalMultiplication 2 μ f` for an almost-everywhere strongly measurable `f` is
  `maximalMultiplication 2 μ (star f)`.
* `MeasureTheory.Lp.isSelfAdjoint_maximalMultiplication` and
  `MeasureTheory.Lp.isSelfAdjoint_maximalMultiplication_iff`: an almost-everywhere strongly
  measurable symbol that is self-conjugate almost everywhere gives a self-adjoint operator on any
  measure space, and on a sigma-finite measure space with nontrivial fiber this condition is also
  necessary for an almost-everywhere strongly measurable symbol.
* `MeasureTheory.Lp.existsUnique_maximal_multiplier`: existence and uniqueness of the closed,
  densely defined maximal `L²` realization of an almost-everywhere strongly measurable multiplier.

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
    { toFun u := u.property.toLp (fun x ↦ f x • (u : Lp E p μ) x)
      map_add' u v := by
        refine Lp.ext ?_
        filter_upwards [(u + v).property.coeFn_toLp, Lp.coeFn_add (u.property.toLp _)
            (v.property.toLp _),
          u.property.coeFn_toLp, v.property.coeFn_toLp, Lp.coeFn_add (u : Lp E p μ) v]
          with x huv hadd hu hv hcoe
        rw [huv, hadd, Pi.add_apply, hu, hv, AddMemClass.coe_add, hcoe, Pi.add_apply, smul_add]
      map_smul' c u := by
        refine Lp.ext ?_
        filter_upwards [(c • u).property.coeFn_toLp, Lp.coeFn_smul c (u.property.toLp _),
          u.property.coeFn_toLp, Lp.coeFn_smul c (u : Lp E p μ)] with x hcu hsmul hu hcoe
        rw [RingHom.id_apply, hcu, hsmul, Pi.smul_apply, hu, SetLike.val_smul, hcoe,
          Pi.smul_apply, smul_comm (f x) c] }

/-- A class `u : Lp E p μ` lies in the domain of `maximalMultiplication p μ f` precisely when
`x ↦ f x • u x` belongs to `MemLp · p μ`.

Not a `simp` lemma: on the right-hand side, `simp` tries `MeasureTheory.MemLp.of_discrete`,
whose `DiscreteMeasurableSpace` search times out in large environments. -/
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
  u.property.coeFn_toLp

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

/-- A constant multiplier `c` induces the everywhere-defined scalar multiple `c • id`. -/
theorem maximalMultiplication_const (c : 𝕜) :
    maximalMultiplication (E := E) p μ (fun _ ↦ c) =
      (c • LinearMap.id : Lp E p μ →ₗ[𝕜] Lp E p μ).toPMap ⊤ := by
  refine (eq_maximalMultiplication_of_domain_of_ae (fun u ↦ ?_) (fun u ↦ ?_)).symm
  · simp only [LinearMap.toPMap_domain, Submodule.mem_top, true_iff]
    exact (Lp.memLp u).const_smul c
  · exact Lp.coeFn_smul c (u : Lp E p μ)

/-- The zero multiplier induces the everywhere-defined zero partial linear operator. -/
@[simp]
theorem maximalMultiplication_zero :
    maximalMultiplication (E := E) p μ (0 : α → 𝕜) = 0 := by
  refine (maximalMultiplication_const (E := E) (p := p) (μ := μ) (0 : 𝕜)).trans ?_
  exact LinearPMap.ext rfl fun _ _ _ ↦ by simp

/-- The unit multiplier `1` induces the everywhere-defined identity operator. -/
@[simp]
theorem maximalMultiplication_one :
    maximalMultiplication (E := E) p μ (1 : α → 𝕜) =
      (LinearMap.id : Lp E p μ →ₗ[𝕜] Lp E p μ).toPMap ⊤ := by
  simpa only [Pi.one_def, one_smul] using
    maximalMultiplication_const (E := E) (p := p) (μ := μ) (1 : 𝕜)

/-- Scaling the multiplier by a nonzero scalar `c` scales the maximal multiplication operator by
`c`. For `c = 0` the left-hand side has full domain `⊤` while `0 • T` retains `T.domain`. -/
theorem maximalMultiplication_smul {c : 𝕜} (hc : c ≠ 0) (f : α → 𝕜) :
    maximalMultiplication (E := E) p μ (c • f) = c • maximalMultiplication (E := E) p μ f := by
  refine (eq_maximalMultiplication_of_domain_of_ae (fun u ↦ ?_) (fun u ↦ ?_)).symm
  · simp only [LinearPMap.smul_domain, mem_domain_maximalMultiplication, Pi.smul_apply,
      smul_eq_mul, mul_smul]
    refine ⟨fun h ↦ h.const_smul c,
      fun h ↦ (h.const_smul c⁻¹).ae_eq (Eventually.of_forall fun x ↦ ?_)⟩
    rw [Pi.smul_apply, inv_smul_smul₀ hc]
  · rw [LinearPMap.smul_apply]
    filter_upwards [Lp.coeFn_smul c (maximalMultiplication (E := E) p μ f u),
      coeFn_maximalMultiplication u] with x hsmul hf
    rw [hsmul, Pi.smul_apply, hf, Pi.smul_apply, smul_eq_mul, mul_smul]

/-- Negating the multiplier negates the maximal multiplication operator. -/
@[simp]
theorem maximalMultiplication_neg (f : α → 𝕜) :
    maximalMultiplication (E := E) p μ (-f) = -maximalMultiplication (E := E) p μ f := by
  simpa only [neg_one_smul, LinearPMap.neg_smul, one_smul] using
    maximalMultiplication_smul (E := E) (p := p) (μ := μ) (neg_ne_zero.2 one_ne_zero) f

/-- Subtracting a constant scalar `c` from the multiplier shifts the maximal multiplication
operator by `LinearPMap.subScalar · c`. -/
theorem maximalMultiplication_sub_const (f : α → 𝕜) (c : 𝕜) :
    maximalMultiplication (E := E) p μ (fun x ↦ f x - c) =
      (maximalMultiplication (E := E) p μ f).subScalar c := by
  refine (eq_maximalMultiplication_of_domain_of_ae (fun u ↦ ?_) (fun u ↦ ?_)).symm
  · simp only [LinearPMap.subScalar_domain, mem_domain_maximalMultiplication, sub_smul]
    refine ⟨fun h ↦ h.sub ((Lp.memLp u).const_smul c),
      fun h ↦ (h.add ((Lp.memLp u).const_smul c)).ae_eq (Eventually.of_forall fun x ↦ ?_)⟩
    simp only [Pi.add_apply, Pi.smul_apply, sub_add_cancel]
  · rw [LinearPMap.subScalar_apply]
    let u' : (maximalMultiplication (E := E) p μ f).domain :=
      ⟨u, (LinearPMap.subScalar_domain (maximalMultiplication (E := E) p μ f) c) ▸ u.property⟩
    filter_upwards [Lp.coeFn_sub (maximalMultiplication (E := E) p μ f u') (c • (u : Lp E p μ)),
      coeFn_maximalMultiplication u', Lp.coeFn_smul c (u : Lp E p μ)] with x hsub hf hsmul
    rw [hsub, Pi.sub_apply, hf, hsmul, Pi.smul_apply, sub_smul]

/-- The operator sum of two maximal multiplication operators is a restriction of the maximal
multiplication operator of the pointwise sum. -/
theorem le_maximalMultiplication_add (f g : α → 𝕜) :
    maximalMultiplication (E := E) p μ f + maximalMultiplication (E := E) p μ g ≤
      maximalMultiplication (E := E) p μ (f + g) := by
  refine LinearPMap.le_of_le_graph fun ⟨u₀, v₀⟩ hw ↦ ?_
  obtain ⟨u, rfl, rfl⟩ :=
    (maximalMultiplication p μ f + maximalMultiplication p μ g).mem_graph_iff.1 hw
  have hu : (u : Lp E p μ) ∈ (maximalMultiplication (E := E) p μ f).domain ⊓
      (maximalMultiplication (E := E) p μ g).domain := by
    simpa only [LinearPMap.add_domain] using u.property
  obtain ⟨huf, hug⟩ := Submodule.mem_inf.1 hu
  rw [mem_graph_maximalMultiplication_iff, LinearPMap.add_apply]
  filter_upwards [Lp.coeFn_add (maximalMultiplication (E := E) p μ f ⟨(u : Lp E p μ), huf⟩)
      (maximalMultiplication (E := E) p μ g ⟨(u : Lp E p μ), hug⟩),
    coeFn_maximalMultiplication ⟨(u : Lp E p μ), huf⟩,
    coeFn_maximalMultiplication ⟨(u : Lp E p μ), hug⟩] with x hadd hf hg
  rw [hadd, Pi.add_apply, hf, hg, Pi.add_apply, add_smul]

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

/-- For an essentially bounded symbol `a : Lp 𝕜 ∞ μ`, `maximalMultiplication p μ a` (`1 ≤ p ≤ ∞`)
agrees with `MeasureTheory.Lp.multiplicationOperator a` viewed as an everywhere-defined
`LinearPMap`. -/
@[simp]
theorem maximalMultiplication_coeFn_eq_multiplicationOperator [Fact (1 ≤ p)] (a : Lp 𝕜 ∞ μ) :
    maximalMultiplication (E := E) p μ a =
      (multiplicationOperator (E := E) (p := p) a : Lp E p μ →ₗ[𝕜] Lp E p μ).toPMap ⊤ := by
  refine (eq_maximalMultiplication_of_domain_of_ae (fun u ↦ ?_) (fun u ↦ ?_)).symm
  · simp only [LinearMap.toPMap_domain, Submodule.mem_top, true_iff]
    exact (Lp.memLp a).smul (Lp.memLp u)
  · exact multiplicationOperator_ae a (u : Lp E p μ)

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

/-! ### Bounded-on-support vectors, domain density, core property, and symbol faithfulness -/

section CutoffAndFaithful

variable {α 𝕜 E : Type*} [MeasurableSpace α] [NormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] {p : ℝ≥0∞} {μ : Measure α}

/-- The submodule of vectors `u : Lp E p μ` on whose support `‖f‖` is almost everywhere bounded
by some finite constant `C`. -/
def boundedOnSupportSubmodule (p : ℝ≥0∞) (μ : Measure α) (f : α → 𝕜) :
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

/-- Membership in `boundedOnSupportSubmodule p μ f` means that `‖f‖` is bounded almost everywhere
on the support of `u`. -/
@[simp]
theorem mem_boundedOnSupportSubmodule_iff {f : α → 𝕜} {u : Lp E p μ} :
    u ∈ boundedOnSupportSubmodule p μ f ↔ ∃ C : ℝ, ∀ᵐ x ∂μ, u x ≠ 0 → ‖f x‖ ≤ C :=
  (Iff.rfl)

/-- For an almost-everywhere strongly measurable symbol `f`, every vector in
`boundedOnSupportSubmodule p μ f` lies in the domain of `maximalMultiplication p μ f`. -/
theorem boundedOnSupportSubmodule_le_domain_maximalMultiplication {f : α → 𝕜}
    (hf : AEStronglyMeasurable f μ) :
    boundedOnSupportSubmodule (E := E) p μ f ≤
      (maximalMultiplication (E := E) p μ f).domain := by
  intro u hu
  obtain ⟨C, hC⟩ := mem_boundedOnSupportSubmodule_iff.1 hu
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

private theorem cutoffLp_mem_boundedOnSupportSubmodule {f : α → 𝕜}
    (hf : AEStronglyMeasurable f μ) (n : ℕ) (u : Lp E p μ) :
    cutoffLp hf n u ∈ boundedOnSupportSubmodule p μ f := by
  refine mem_boundedOnSupportSubmodule_iff.2 ⟨n, ?_⟩
  filter_upwards [coeFn_cutoffLp hf n u, hf.ae_eq_mk] with x hcut hmk hne
  rw [hcut] at hne
  rw [hmk]
  exact mem_cutoffSet_iff.1 (Set.mem_of_indicator_ne_zero hne)

private theorem indicatorConstLp_mem_domain_of_subset_cutoffSet {f : α → 𝕜}
    (hf : AEStronglyMeasurable f μ) {n : ℕ} {s : Set α} (hs : MeasurableSet s)
    (hμs : μ s ≠ ∞) (hsub : s ⊆ cutoffSet hf n) (v : E) :
    indicatorConstLp p hs hμs v ∈ (maximalMultiplication (E := E) p μ f).domain := by
  refine boundedOnSupportSubmodule_le_domain_maximalMultiplication hf
    (mem_boundedOnSupportSubmodule_iff.2 ⟨n, ?_⟩)
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
      have hs_null : μ s = 0 :=
        (TauCeti.indicatorConstLp_eq_zero_iff.1 (hker u hu_ker)).resolve_right hv
      filter_upwards [measure_eq_zero_iff_ae_notMem.1 hs_null, hf.ae_eq_mk]
        with x hnots hmk hxm hfx0
      exact hnots ⟨hxm, norm_eq_zero.2 (hmk.symm.trans hfx0)⟩
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

/-- On a sigma-finite measure space with nontrivial fiber `E`, for an almost-everywhere strongly
measurable symbol `f`, `z` is not an eigenvalue of `maximalMultiplication p μ f`
(`ker (smulSub z ·) = ⊥`) if and only if `{x | f x = z}` is `μ`-null. -/
theorem ker_smulSub_maximalMultiplication_eq_bot_iff [SigmaFinite μ] [Nontrivial E]
    {f : α → 𝕜} (hf : AEStronglyMeasurable f μ) (z : 𝕜) :
    LinearMap.ker ((maximalMultiplication (E := E) p μ f).smulSub z) = ⊥ ↔
      μ {x | f x = z} = 0 := by
  have hset : {x | f x - z = 0} = {x | f x = z} := by
    ext x
    exact sub_eq_zero
  have hsub : AEStronglyMeasurable (fun x ↦ f x - z) μ := hf.sub aestronglyMeasurable_const
  rw [LinearPMap.ker_smulSub_eq_bot_iff, ← maximalMultiplication_sub_const,
    ker_maximalMultiplication_eq_bot_iff (E := E) (p := p) hsub, hset]

private theorem maximalMultiplication_cutoffLp {f : α → 𝕜} (hf : AEStronglyMeasurable f μ)
    (n : ℕ) (u : (maximalMultiplication (E := E) p μ f).domain) :
    maximalMultiplication p μ f
        ⟨cutoffLp hf n (u : Lp E p μ), boundedOnSupportSubmodule_le_domain_maximalMultiplication hf
          (cutoffLp_mem_boundedOnSupportSubmodule hf n (u : Lp E p μ))⟩ =
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

/-- When `f` is almost-everywhere strongly measurable and `p ≠ ∞`,
`boundedOnSupportSubmodule p μ f` is dense in `Lp E p μ`. -/
theorem dense_boundedOnSupportSubmodule {f : α → 𝕜} (hf : AEStronglyMeasurable f μ)
    (hp : p ≠ ∞) :
    Dense (boundedOnSupportSubmodule (E := E) p μ f : Set (Lp E p μ)) := by
  rw [dense_iff_closure_eq, Set.eq_univ_iff_forall]
  intro u
  exact mem_closure_of_tendsto (tendsto_cutoffLp hf hp u)
    (Eventually.of_forall fun n ↦ cutoffLp_mem_boundedOnSupportSubmodule hf n u)

/-- When `f` is almost-everywhere strongly measurable and `p ≠ ∞`, the domain of
`maximalMultiplication p μ f` is dense in `Lp E p μ`. -/
theorem dense_domain_maximalMultiplication {f : α → 𝕜} (hf : AEStronglyMeasurable f μ)
    (hp : p ≠ ∞) :
    Dense ((maximalMultiplication (E := E) p μ f).domain : Set (Lp E p μ)) :=
  (dense_boundedOnSupportSubmodule hf hp).mono
    (boundedOnSupportSubmodule_le_domain_maximalMultiplication hf)

/-- When `f` is almost-everywhere strongly measurable and `p ≠ ∞`,
`boundedOnSupportSubmodule p μ f` is an operator core (`LinearPMap.HasCore`) for
`maximalMultiplication p μ f`. -/
theorem hasCore_maximalMultiplication_boundedOnSupportSubmodule {f : α → 𝕜}
    (hf : AEStronglyMeasurable f μ) (hp : p ≠ ∞) :
    (maximalMultiplication (E := E) p μ f).HasCore (boundedOnSupportSubmodule p μ f) := by
  have hT_closed : (maximalMultiplication (E := E) p μ f).IsClosed :=
    isClosed_maximalMultiplication f
  refine (hT_closed.hasCore_iff_graph_subset_closure
    (boundedOnSupportSubmodule_le_domain_maximalMultiplication hf)).2 ?_
  intro ⟨u₀, v₀⟩ hw
  obtain ⟨u, rfl, rfl⟩ := (maximalMultiplication (E := E) p μ f).mem_graph_iff.1 hw
  have hmem (n : ℕ) :
      (cutoffLp hf n (u : Lp E p μ), cutoffLp hf n (maximalMultiplication p μ f u)) ∈
        (((maximalMultiplication (E := E) p μ f).domRestrict
          (boundedOnSupportSubmodule p μ f)).graph : Set (Lp E p μ × Lp E p μ)) := by
    have hS_mem : cutoffLp hf n (u : Lp E p μ) ∈ boundedOnSupportSubmodule (E := E) p μ f :=
      cutoffLp_mem_boundedOnSupportSubmodule hf n (u : Lp E p μ)
    have hdom : cutoffLp hf n (u : Lp E p μ) ∈
        ((maximalMultiplication (E := E) p μ f).domRestrict
          (boundedOnSupportSubmodule p μ f)).domain := by
      rw [LinearPMap.domRestrict_domain, Submodule.mem_inf]
      exact ⟨hS_mem, boundedOnSupportSubmodule_le_domain_maximalMultiplication hf hS_mem⟩
    refine ((maximalMultiplication (E := E) p μ f).domRestrict
      (boundedOnSupportSubmodule p μ f)).mem_graph_iff.2 ⟨⟨_, hdom⟩, rfl, ?_⟩
    exact ((maximalMultiplication (E := E) p μ f).domRestrict_apply (x := ⟨_, hdom⟩)
      (y := ⟨_, boundedOnSupportSubmodule_le_domain_maximalMultiplication hf hS_mem⟩) rfl).trans
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

/-- Over a normed field `𝕜` with a norm-preserving additive star involution,
`maximalMultiplication p μ (star f)` has the same domain as `maximalMultiplication p μ f` for
every symbol `f : α → 𝕜` and every normed `𝕜`-space `E`. -/
@[simp]
theorem domain_maximalMultiplication_star (f : α → 𝕜) :
    (maximalMultiplication (E := E) p μ (star f)).domain =
      (maximalMultiplication (E := E) p μ f).domain := by
  ext u
  simp only [mem_domain_maximalMultiplication, Pi.star_apply]
  exact memLp_star_smul_iff (Lp.aestronglyMeasurable u)

/-- Over a normed field `𝕜` with a norm-preserving additive star involution,
`maximalMultiplication p μ (star f)` and `maximalMultiplication p μ f` have the same norm at every
vector of their common domain. -/
theorem norm_maximalMultiplication_star_apply (f : α → 𝕜)
    (u : (maximalMultiplication (E := E) p μ f).domain) :
    ‖maximalMultiplication (E := E) p μ (star f)
        ⟨(u : Lp E p μ), by rw [domain_maximalMultiplication_star f]; exact u.property⟩‖ =
      ‖maximalMultiplication (E := E) p μ f u‖ := by
  let u' : (maximalMultiplication (E := E) p μ (star f)).domain :=
    ⟨(u : Lp E p μ), by rw [domain_maximalMultiplication_star f]; exact u.property⟩
  rw [Lp.norm_def, Lp.norm_def]
  refine congrArg ENNReal.toReal
    (eLpNorm_congr_norm_ae (Lp.aestronglyMeasurable _) (Lp.aestronglyMeasurable _) ?_)
  filter_upwards [coeFn_maximalMultiplication u', coeFn_maximalMultiplication u] with t h₁ h₂
  rw [h₁, h₂, Pi.star_apply, norm_smul, norm_smul, norm_star]

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
      boundedOnSupportSubmodule_le_domain_maximalMultiplication hf
        (cutoffLp_mem_boundedOnSupportSubmodule hf n u)
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
    dense_domain_maximalMultiplication hf ENNReal.ofNat_ne_top
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
theorem domain_adjoint_maximalMultiplication {f : α → 𝕜} (hf : AEStronglyMeasurable f μ) :
    (maximalMultiplication (E := E) 2 μ f).adjoint.domain =
      (maximalMultiplication (E := E) 2 μ f).domain := by
  rw [adjoint_maximalMultiplication hf, domain_maximalMultiplication_star f]

/-- For an almost-everywhere strongly measurable symbol `f`, the Hilbert adjoint of
`maximalMultiplication 2 μ f` has the same norm as `maximalMultiplication 2 μ f` at every vector of
their common domain (`domain_adjoint_maximalMultiplication`). -/
theorem norm_adjoint_maximalMultiplication_apply {f : α → 𝕜} (hf : AEStronglyMeasurable f μ)
    (u : (maximalMultiplication (E := E) 2 μ f).domain) :
    ‖(maximalMultiplication (E := E) 2 μ f).adjoint
        ⟨(u : Lp E 2 μ), by rw [domain_adjoint_maximalMultiplication hf]; exact u.property⟩‖ =
      ‖maximalMultiplication (E := E) 2 μ f u‖ := by
  rw [LinearPMap.congr_fun (adjoint_maximalMultiplication hf) _
    (by rw [domain_maximalMultiplication_star f]; exact u.property)]
  exact norm_maximalMultiplication_star_apply f u

/-- An almost-everywhere strongly measurable symbol satisfying `star (f t) = f t` almost everywhere
induces a self-adjoint maximal multiplication operator on `Lp E 2 μ`, for any measure `μ`. -/
theorem isSelfAdjoint_maximalMultiplication {f : α → 𝕜} (hf : AEStronglyMeasurable f μ)
    (hreal : ∀ᵐ t ∂μ, star (f t) = f t) :
    IsSelfAdjoint (maximalMultiplication (E := E) 2 μ f) := by
  rw [LinearPMap.isSelfAdjoint_def, adjoint_maximalMultiplication hf]
  exact maximalMultiplication_congr_ae hreal

/-- On a sigma-finite measure space with nontrivial fiber `E`, for an almost-everywhere strongly
measurable symbol `f`, `maximalMultiplication 2 μ f` is self-adjoint if and only if
`star (f t) = f t` almost everywhere. -/
theorem isSelfAdjoint_maximalMultiplication_iff [SigmaFinite μ] [Nontrivial E]
    {f : α → 𝕜} (hf : AEStronglyMeasurable f μ) :
    IsSelfAdjoint (maximalMultiplication (E := E) 2 μ f) ↔ ∀ᵐ t ∂μ, star (f t) = f t := by
  rw [LinearPMap.isSelfAdjoint_def, adjoint_maximalMultiplication hf,
    maximalMultiplication_eq_maximalMultiplication_iff hf.star hf]
  simp only [Filter.EventuallyEq, Pi.star_apply]

/-- **Existence and uniqueness of the maximal `L²` multiplier.** Every almost-everywhere strongly
measurable scalar symbol `f : α → 𝕜` on any measure space `(α, μ)` has a unique maximal partial
linear realization on `Lp E 2 μ`; it is densely defined and closed, and is self-adjoint whenever
`f` is self-conjugate almost everywhere. -/
theorem existsUnique_maximal_multiplier {f : α → 𝕜} (hf : AEStronglyMeasurable f μ) :
    ∃! T : Lp E 2 μ →ₗ.[𝕜] Lp E 2 μ,
      (∀ x : Lp E 2 μ, x ∈ T.domain ↔ MemLp (fun t ↦ f t • x t) 2 μ) ∧
      (∀ x : T.domain, ∀ᵐ t ∂μ, (T x) t = f t • (x : Lp E 2 μ) t) ∧
      Dense (T.domain : Set (Lp E 2 μ)) ∧ T.IsClosed ∧
      ((∀ᵐ t ∂μ, star (f t) = f t) → IsSelfAdjoint T) := by
  refine ⟨maximalMultiplication (E := E) 2 μ f,
    ⟨fun _ ↦ mem_domain_maximalMultiplication,
      coeFn_maximalMultiplication,
      dense_domain_maximalMultiplication hf ENNReal.ofNat_ne_top,
      isClosed_maximalMultiplication f,
      isSelfAdjoint_maximalMultiplication hf⟩,
    fun T ⟨hdom, hae, _, _, _⟩ ↦ eq_maximalMultiplication_of_domain_of_ae hdom hae⟩

end Complete

end Hilbert

end MeasureTheory.Lp
