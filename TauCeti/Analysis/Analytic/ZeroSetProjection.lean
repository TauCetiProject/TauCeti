/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Data.Set.Restrict
public import Mathlib.Topology.Maps.Basic
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import TauCeti.Analysis.Analytic.IteratedDeriv
import TauCeti.Analysis.Analytic.Order
import TauCeti.Analysis.Calculus.Deriv.ZeroSetProjection

/-!
# Analytic hypersurfaces with property (P)

Write points of a cylinder `E × ℝ` as `(u, t)`, with base point `u` and height `t`. Following
Łojasiewicz, a set `Z ⊆ E × ℝ` has *property (P)* when the projection of each of its relatively
open subsets to the base is open, that is, when `Z.domRestrict Prod.fst` is an open map.

The zero set of a real analytic function need not have this property: the zero set of
`(u, t) ↦ t ^ 2 + u ^ 2` is a single point. Łojasiewicz's lemma says that it acquires it after
multiplication by a suitable second analytic function. Let `f` be analytic at `x₀` and not
identically zero near `x₀` on the vertical line through `x₀`, so that it vanishes to some finite
order `q` at `x₀` along that line. Then for `g` the product of the vertical derivatives
`∂ₜᵏ f`, `1 ≤ k ≤ q`, the zero set of `f * g` has property (P) on every open set near `x₀`
(`AnalyticAt.exists_isOpenMap_domRestrict_fst_setOf_mul_eq_zero`). Indeed, near `x₀` the
derivative `∂ₜ^q f` does not vanish, and at each zero of `f * g` the last of the functions
`f, ∂ₜ f, …, ∂ₜ^(q-1) f` vanishing there has a nonvanishing vertical derivative, so these zeros
persist over nearby base points (`TauCeti.isOpenMap_domRestrict_fst_setOf_exists_eq_zero`). The
function `g` is again not identically zero on the vertical line through `x₀`.

In Łojasiewicz's triangulation of semianalytic sets, this lemma provides an analytic function
whose zero set contains that of `f` and projects openly. Its zero set is then used as the
lower-dimensional part of a normal decomposition adapted to a nonsingular vertical direction.

## Main results

* `AnalyticAt.exists_isOpenMap_domRestrict_fst_setOf_mul_eq_zero`: Łojasiewicz's lemma on
  hypersurfaces with property (P).

## References

* S. Łojasiewicz, *Triangulation of semi-analytic sets*, Annali della Scuola Normale Superiore di
  Pisa (3) 18 (1964), 449–474, §2, Lemma 7.
-/

public section

open Set Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

namespace AnalyticAt

/-- **Hypersurfaces with property (P)** (Łojasiewicz). Let `f : E × ℝ → ℝ` be analytic at `x₀`
and not identically zero near `x₀` on the vertical line through `x₀`. Then there are an open
neighbourhood `N` of `x₀` and a function `g` analytic on `N`, again not identically zero near `x₀`
on the vertical line through `x₀`, such that the zero set of `f * g` in each open subset `U` of `N`
has property (P): the projection to the base of each of its relatively open subsets is open. -/
theorem exists_isOpenMap_domRestrict_fst_setOf_mul_eq_zero {f : E × ℝ → ℝ} {x₀ : E × ℝ}
    (hf : AnalyticAt ℝ f x₀) (hf₀ : ¬∀ᶠ t in 𝓝 x₀.2, f (x₀.1, t) = 0) :
    ∃ (g : E × ℝ → ℝ) (N : Set (E × ℝ)), IsOpen N ∧ x₀ ∈ N ∧ AnalyticOnNhd ℝ g N ∧
      (¬∀ᶠ t in 𝓝 x₀.2, g (x₀.1, t) = 0) ∧
      ∀ U ⊆ N, IsOpen U → IsOpenMap ({x ∈ U | f x * g x = 0}.domRestrict Prod.fst) := by
  -- The vertical derivatives `D k = ∂ₜᵏ f`, analytic wherever `f` is.
  set D : ℕ → E × ℝ → ℝ := fun k x ↦ iteratedDeriv k (fun t ↦ f (x.1, t)) x.2 with hD
  set A := {x : E × ℝ | AnalyticAt ℝ f x}
  have hDA (k : ℕ) {x : E × ℝ} (hx : x ∈ A) : AnalyticAt ℝ (D k) x :=
    AnalyticAt.iteratedDeriv_snd hx k
  have hDcont (k : ℕ) : ContinuousOn (D k) A := fun x hx ↦
    (hDA k hx).continuousAt.continuousWithinAt
  -- Along the vertical line through `x₀`, `f` vanishes to a finite order `q`.
  set φ : ℝ → ℝ := fun t ↦ f (x₀.1, t)
  have hφ : AnalyticAt ℝ φ x₀.2 := hf.curry_right
  obtain ⟨q, hq⟩ := ENat.ne_top_iff_exists.1 (mt analyticOrderAt_eq_top.1 hf₀)
  have hDq : D q x₀ ≠ 0 :=
    ((analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero hφ).1 hq.symm).2
  -- `N` is the part of the analytic locus of `f` where `∂ₜ^q f` does not vanish.
  set N := A ∩ D q ⁻¹' {0}ᶜ
  have hN : IsOpen N := (hDcont q).isOpen_inter_preimage (isOpen_analyticAt ℝ f)
    isOpen_compl_singleton
  refine ⟨∏ k ∈ Finset.range q, D (k + 1), N, hN, ⟨hf, hDq⟩,
    Finset.analyticOnNhd_prod _ fun k _ x hx ↦ hDA (k + 1) hx.1, ?_, fun U hUN hU ↦ ?_⟩
  · -- On the vertical line through `x₀`, `g` is a product of derivatives of `φ` of finite order.
    rw [← analyticOrderAt_eq_top, ← ne_eq]
    have hg : (fun t ↦ (∏ k ∈ Finset.range q, D (k + 1)) (x₀.1, t)) =
        ∏ k ∈ Finset.range q, deriv^[k + 1] φ := by
      ext t
      simp [hD, φ, iteratedDeriv_eq_iterate]
    have hφk (k : ℕ) : AnalyticAt ℝ (deriv^[k] φ) x₀.2 := hφ.iterated_deriv k
    rw [hg, TauCeti.analyticOrderAt_prod fun k _ ↦ hφk (k + 1),
      Finset.sum_congr rfl fun k hk ↦ analyticOrderAt_iterated_deriv hq
        (Finset.mem_range.1 hk), ← Nat.cast_sum]
    exact ENat.natCast_ne_top _
  · -- The zeros of `f * g` in `U` are the points where some `∂ₜᵏ f` with `k < q` vanishes.
    have hset : {x ∈ U | f x * (∏ k ∈ Finset.range q, D (k + 1)) x = 0} =
        {x ∈ U | ∃ k < q, D k x = 0} := by
      ext x
      simp only [mem_ofPred_eq, and_congr_right_iff]
      intro hx
      have hfD : f x * (∏ k ∈ Finset.range q, D (k + 1)) x =
          ∏ k ∈ Finset.range (q + 1), D k x := by
        rw [Finset.prod_range_succ', Finset.prod_apply, mul_comm]
        simp [hD]
      rw [hfD, Finset.prod_eq_zero_iff]
      simp only [Finset.mem_range]
      refine ⟨fun ⟨k, hk, hk0⟩ ↦ ⟨k, ?_, hk0⟩, fun ⟨k, hk, hk0⟩ ↦ ⟨k, by omega, hk0⟩⟩
      exact (Nat.lt_succ_iff.1 hk).lt_of_ne fun h ↦ (hUN hx).2 (h ▸ hk0)
    rw [hset]
    refine TauCeti.isOpenMap_domRestrict_fst_setOf_exists_eq_zero hU
      (fun k _ ↦ (hDcont k).mono fun x hx ↦ (hUN hx).1) (fun k _ x hx ↦ ?_)
      fun x hx ↦ (hUN hx).2
    -- The vertical derivative of `∂ₜᵏ f` is `∂ₜ^(k+1) f`.
    have hdiff : DifferentiableAt ℝ (iteratedDeriv k fun t ↦ f (x.1, t)) x.2 :=
      (hDA k (hUN hx).1).curry_right.differentiableAt
    simpa [hD, iteratedDeriv_succ] using hdiff.hasDerivAt

end AnalyticAt
