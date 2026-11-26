/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Continuous
public import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Topology.TietzeExtension

/-!
# Uniform approximation by ridge functions

Finite linear combinations of continuous ridge functions approximate every continuous function on
any compact subset of a real inner product space. This lets uniform approximation on such sets
be reduced to approximation of the one-variable profiles of the ridge functions.

The exponential ridge functions form a multiplicatively closed family and separate points, so
Mathlib's Stone–Weierstrass theorem applies to their span. See Allan Pinkus,
*Approximation theory of the MLP model in neural networks*, Acta Numerica 8 (1999), pp. 154–155,
for the exponential argument and the finite-dimensional case of ridge density.
-/

public section

open scoped RealInnerProductSpace

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Continuous ridge functions on `E`, given by a continuous profile applied to the inner
product with a fixed direction. -/
def ridgeFunctions (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] : Set (E → ℝ) :=
  Set.range fun p : E × C(ℝ, ℝ) ↦ fun x ↦ p.2 ⟪p.1, x⟫

/-- A ridge function is specified by a direction and a continuous one-variable profile. -/
theorem mem_ridgeFunctions_iff {g : E → ℝ} :
    g ∈ ridgeFunctions E ↔ ∃ (a : E) (h : C(ℝ, ℝ)), (fun x ↦ h ⟪a, x⟫) = g := by
  simp only [ridgeFunctions, Set.mem_range, Prod.exists]

/-- On a compact subset of a real inner product space, every continuous restriction can be
uniformly approximated by finite linear combinations of continuous ridge functions. -/
theorem _root_.IsCompact.exists_mem_span_ridgeFunctions_dist_lt {K : Set E} (hK : IsCompact K)
    {f : E → ℝ} (hf : ContinuousOn f K) {ε : ℝ} (hε : 0 < ε) :
    ∃ g ∈ Submodule.span ℝ (ridgeFunctions E), ∀ x ∈ K, dist (f x) (g x) < ε := by
  let e : Multiplicative E →* C(E, ℝ) :=
    { toFun := fun a ↦ ⟨fun x ↦ Real.exp ⟪a.toAdd, x⟫, by fun_prop⟩
      map_one' := by ext x; simp
      map_mul' := fun a b ↦ by
        ext x
        simp [inner_add_left, Real.exp_add] }
  let A : Subalgebra ℝ C(E, ℝ) := Algebra.adjoin ℝ (MonoidHom.mrange e : Set C(E, ℝ))
  have hsep : A.SeparatesPoints := by
    intro x y hxy
    obtain ⟨a, ha⟩ : ∃ a : E, ⟪a, x⟫ ≠ ⟪a, y⟫ := by
      by_contra! h
      exact hxy (ext_inner_left ℝ h)
    refine ⟨_, ⟨e (.ofAdd a), Algebra.subset_adjoin ⟨.ofAdd a, rfl⟩, rfl⟩, ?_⟩
    exact Real.exp_injective.ne ha
  -- The exponential family is already closed under products, so its adjoin is its linear span.
  have hspan : A.toSubmodule ≤
      (Submodule.span ℝ (ridgeFunctions E)).comap (ContinuousMap.coeFnLinearMap ℝ) := by
    simp only [A, Algebra.adjoin_eq_span, Submonoid.closure_eq]
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨a, rfl⟩
    exact Submodule.subset_span (mem_ridgeFunctions_iff.mpr
      ⟨a.toAdd, ⟨Real.exp, Real.continuous_exp⟩, rfl⟩)
  let fK : C(K, ℝ) := ⟨K.domRestrict f, hf.domRestrict⟩
  obtain ⟨F, hF⟩ := fK.exists_restrict_eq hK.isClosed
  obtain ⟨g, hg, happ⟩ :=
    ContinuousMap.exists_mem_subalgebra_near_continuous_of_isCompact_of_separatesPoints
      hsep F hK hε
  refine ⟨g, hspan hg, fun x hx ↦ ?_⟩
  have hxF : F x = f x := DFunLike.congr_fun hF ⟨x, hx⟩
  rw [← hxF, dist_comm, Real.dist_eq, ← Real.norm_eq_abs]
  exact happ x hx

end TauCeti
