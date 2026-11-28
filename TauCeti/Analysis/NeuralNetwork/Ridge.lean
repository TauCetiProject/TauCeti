/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Continuous
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

/-- The set of ridge functions is the range of the map from directions and continuous profiles. -/
theorem ridgeFunctions_def :
    ridgeFunctions E = Set.range (fun p : E × C(ℝ, ℝ) ↦ fun x ↦ p.2 ⟪p.1, x⟫) := (rfl)

/-- A ridge function is specified by a direction and a continuous one-variable profile. -/
theorem mem_ridgeFunctions_iff {g : E → ℝ} :
    g ∈ ridgeFunctions E ↔ ∃ (a : E) (h : C(ℝ, ℝ)), (fun x ↦ h ⟪a, x⟫) = g := by
  simp only [ridgeFunctions_def, Set.mem_range, Prod.exists]

/-- Applying a continuous profile to the inner product with a fixed direction gives a ridge
function. -/
@[simp]
theorem mem_ridgeFunctions (a : E) (h : C(ℝ, ℝ)) :
    (fun x ↦ h ⟪a, x⟫) ∈ ridgeFunctions E :=
  mem_ridgeFunctions_iff.mpr ⟨a, h, rfl⟩

/-- Every ridge function is continuous. -/
@[grind →]
theorem continuous_of_mem_ridgeFunctions {g : E → ℝ} (hg : g ∈ ridgeFunctions E) :
    Continuous g := by
  obtain ⟨a, h, rfl⟩ := mem_ridgeFunctions_iff.mp hg
  fun_prop

/-- Every finite linear combination of ridge functions is continuous. -/
@[grind →]
theorem continuous_of_mem_span_ridgeFunctions {g : E → ℝ}
    (hg : g ∈ Submodule.span ℝ (ridgeFunctions E)) : Continuous g := by
  have hmem (f : E → ℝ) : f ∈ continuousSubmodule E ℝ ℝ ↔ Continuous f := Iff.rfl
  have hspan : Submodule.span ℝ (ridgeFunctions E) ≤ continuousSubmodule E ℝ ℝ :=
    Submodule.span_le.mpr fun f hf ↦ (hmem f).mpr (continuous_of_mem_ridgeFunctions hf)
  exact (hmem g).mp (hspan hg)

/-- On a compact subset of a real inner product space, every continuous restriction can be
uniformly approximated by finite linear combinations of continuous ridge functions. -/
theorem _root_.IsCompact.exists_mem_span_ridgeFunctions_dist_lt {K : Set E} (hK : IsCompact K)
    {f : E → ℝ} (hf : ContinuousOn f K) {ε : ℝ} (hε : 0 < ε) :
    ∃ g ∈ Submodule.span ℝ (ridgeFunctions E), ∀ x ∈ K, dist (f x) (g x) < ε := by
  let L : E →+ C(E, ℝ) :=
    { toFun := fun a ↦ ⟨fun x ↦ ⟪a, x⟫, by fun_prop⟩
      map_zero' := by ext x; simp
      map_add' := fun a b ↦ by
        ext x
        simp [inner_add_left] }
  let e : Multiplicative E →* C(E, ℝ) :=
    (Real.expMonoidHom.compLeftContinuous E (Real.continuous_exp.comp continuous_toAdd)).comp
      L.toMultiplicative
  have he (a : Multiplicative E) (x : E) : e a x = Real.exp ⟪a.toAdd, x⟫ := by
    dsimp only [e]
    erw [MonoidHom.comp_apply, MonoidHom.compLeftContinuous_apply, ContinuousMap.comp_apply,
      ContinuousMap.coe_mk, Real.expMonoidHom_apply, AddMonoidHom.coe_toMultiplicative]
    -- Evaluating a multiplicative tag on a continuous map tags its value pointwise.
    change Real.exp (Multiplicative.ofAdd (L a.toAdd x)).toAdd = _
    simp [L]
  let A : Subalgebra ℝ C(E, ℝ) := Algebra.adjoin ℝ (MonoidHom.mrange e : Set C(E, ℝ))
  have hsep : A.SeparatesPoints := by
    intro x y hxy
    obtain ⟨a, ha⟩ : ∃ a : E, ⟪a, x⟫ ≠ ⟪a, y⟫ := by
      by_contra! h
      exact hxy (ext_inner_left ℝ h)
    refine ⟨_, ⟨e (.ofAdd a), Algebra.subset_adjoin ⟨.ofAdd a, rfl⟩, rfl⟩, ?_⟩
    simpa only [he, toAdd_ofAdd] using Real.exp_injective.ne ha
  have hcoe (g : C(E, ℝ)) : ContinuousMap.coeFnLinearMap ℝ g = ⇑g := by
    funext x
    rw [ContinuousMap.coeFnLinearMap_apply]
    exact ContinuousMap.coeFnAddMonoidHom_apply g x
  -- The exponential family is already closed under products, so its adjoin is its linear span.
  have hspan : A.toSubmodule ≤
      (Submodule.span ℝ (ridgeFunctions E)).comap (ContinuousMap.coeFnLinearMap ℝ) := by
    simp only [A, Algebra.adjoin_eq_span, Submonoid.closure_eq]
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨a, rfl⟩
    refine Submodule.mem_comap.mpr ?_
    rw [hcoe]
    apply Submodule.subset_span
    refine mem_ridgeFunctions_iff.mpr ⟨a.toAdd, ⟨Real.exp, Real.continuous_exp⟩, ?_⟩
    funext x
    simp only [ContinuousMap.coe_mk, he]
  let fK : C(K, ℝ) := ⟨K.domRestrict f, hf.domRestrict⟩
  obtain ⟨F, hF⟩ := fK.exists_restrict_eq hK.isClosed
  obtain ⟨g, hg, happ⟩ :=
    ContinuousMap.exists_mem_subalgebra_near_continuous_of_isCompact_of_separatesPoints
      hsep F hK hε
  refine ⟨g, ?_, fun x hx ↦ ?_⟩
  · simpa only [hcoe] using Submodule.mem_comap.mp (hspan ((Subalgebra.mem_toSubmodule A).mpr hg))
  have hxF : F x = f x := by
    simpa only [ContinuousMap.restrict_apply, fK, ContinuousMap.coe_mk, Set.domRestrict_apply] using
      DFunLike.congr_fun hF ⟨x, hx⟩
  simpa only [← hxF, dist_eq_norm'] using happ x hx

end TauCeti
