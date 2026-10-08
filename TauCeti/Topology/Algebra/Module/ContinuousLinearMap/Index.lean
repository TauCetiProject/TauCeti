/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.LinearMap.Index
public import Mathlib.Topology.Algebra.Module.Equiv.Basic

/-!
# Index of continuous linear maps

The index of a continuous linear map is the integer `dim ker T − dim coker T`. Mathlib
already develops the purely algebraic `LinearMap.index`; this file transfers its elementary API to
continuous linear maps. The value is junk when the kernel or cokernel is infinite-dimensional,
following Mathlib's convention for `LinearMap.index`. The definition and its elementary formulas
need only algebraic module structures and topologies; continuity hypotheses are confined to the
operations that need them.

## Main declarations

* `ContinuousLinearMap.index`: the index of a continuous linear map.
* `ContinuousLinearMap.index_eq_finrank_sub`: the defining dimension formula.
* `ContinuousLinearMap.index_eq_of_finiteDimensional`: between finite-dimensional spaces,
  the index is the dimension of the domain minus the dimension of the codomain.
* `ContinuousLinearMap.index_zero`: the index of the zero map is the difference of the dimensions.
* `ContinuousLinearMap.index_id`, `ContinuousLinearEquiv.index_eq_zero`, and
  `index_eq_zero_of_bijective`: identities, continuous linear equivalences, and bijective maps have
  index zero.
* `ContinuousLinearMap.index_smul` and `index_neg`: nonzero rescaling and negation preserve
  the index.
* `ContinuousLinearMap.index_equiv_comp` and `index_comp_equiv`: composition with a
  continuous linear equivalence preserves the index.
* `ContinuousLinearMap.index_of_surjective` and `index_of_injective`: the index in the one-sided
  cases.
* `ContinuousLinearMap.finrank_ker_eq_iff_index_eq` and
  `bijective_of_surjective_of_index_eq_zero`: index zero detects bijectivity for a surjective map
  with finite-dimensional kernel.

The sign convention follows McDuff--Salamon, *J-holomorphic Curves and Symplectic Topology*,
Appendix A.1.
-/

public section

namespace ContinuousLinearMap

open Module

section Ring

variable {𝕜 : Type*} [Ring 𝕜]
variable {E F G : Type*}
variable [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
variable [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F]
variable [AddCommGroup G] [Module 𝕜 G] [TopologicalSpace G]

/-- The **index** of a continuous linear map, `dim ker T − dim coker T`, defined as the index of
the underlying linear map. -/
noncomputable def index (T : E →L[𝕜] F) : ℤ := (T : E →ₗ[𝕜] F).index

/-- The index as the algebraic index of the underlying linear map. -/
lemma index_def (T : E →L[𝕜] F) : ContinuousLinearMap.index T =
    (T : E →ₗ[𝕜] F).index := (rfl)

/-- The index is `dim ker T − dim coker T`. -/
lemma index_eq_finrank_sub (T : E →L[𝕜] F) :
    ContinuousLinearMap.index T = (finrank 𝕜 (LinearMap.ker (T : E →ₗ[𝕜] F)) : ℤ) -
      finrank 𝕜 (F ⧸ LinearMap.range (T : E →ₗ[𝕜] F)) := by
  rw [ContinuousLinearMap.index_def]
  exact LinearMap.index_eq_finrank_sub

/-- The index of the zero continuous linear map is the dimension of its domain minus the
dimension of its codomain. -/
@[simp]
lemma index_zero :
    (0 : E →L[𝕜] F).index = (finrank 𝕜 E : ℤ) - finrank 𝕜 F := by
  simpa only [index_def, toLinearMap_zero] using
    (LinearMap.index_zero (R := 𝕜) (M := E) (N := F))

/-- A surjective continuous linear map has index the dimension of its kernel. -/
lemma index_of_surjective [Nontrivial 𝕜] (T : E →L[𝕜] F) (hT : Function.Surjective T) :
    T.index = (finrank 𝕜 T.ker : ℤ) := by
  rw [index_eq_finrank_sub, LinearMap.range_eq_top.mpr hT]
  simp [Module.finrank_zero_of_subsingleton]

/-- For a surjective continuous linear map, having index `n` and having a kernel of dimension `n`
are the same statement. -/
lemma finrank_ker_eq_iff_index_eq [Nontrivial 𝕜] {n : ℕ} (T : E →L[𝕜] F)
    (hT : Function.Surjective T) :
    finrank 𝕜 T.ker = n ↔ T.index = n := by
  rw [T.index_of_surjective hT, Nat.cast_inj]

/-- An injective continuous linear map has index the negative of the dimension of its cokernel. -/
lemma index_of_injective [Nontrivial 𝕜] (T : E →L[𝕜] F) (hT : Function.Injective T) :
    T.index = -(finrank 𝕜 (F ⧸ T.range) : ℤ) := by
  rw [index_def, LinearMap.index_of_injective hT]

/-- A bijective continuous linear map has index zero. -/
lemma index_eq_zero_of_bijective (T : E →L[𝕜] F)
    (hT : Function.Bijective T) : ContinuousLinearMap.index T = 0 := by
  rw [ContinuousLinearMap.index_def]
  nontriviality 𝕜
  rw [LinearMap.index_of_injective hT.injective, LinearMap.range_eq_top.mpr hT.surjective]
  simp [Module.finrank_zero_of_subsingleton]

/-- The identity operator has index `0`. -/
@[simp] lemma index_id : ContinuousLinearMap.index
    (ContinuousLinearMap.id 𝕜 E) = 0 :=
  index_eq_zero_of_bijective _ Function.bijective_id

/-- A continuous linear equivalence has index `0`. -/
@[simp] lemma _root_.ContinuousLinearEquiv.index_eq_zero (e : E ≃L[𝕜] F) :
    ContinuousLinearMap.index (e : E →L[𝕜] F) = 0 :=
  index_eq_zero_of_bijective _ e.bijective

/-- The index is unchanged by negation. -/
@[simp] lemma index_neg [IsTopologicalAddGroup F] (T : E →L[𝕜] F) : ContinuousLinearMap.index (-T)
    = ContinuousLinearMap.index T := by
  have hneg : ((LinearEquiv.neg 𝕜 : F ≃ₗ[𝕜] F) : F →ₗ[𝕜] F).comp
      (T : E →ₗ[𝕜] F) = -(T : E →ₗ[𝕜] F) := by
    ext x
    simp
  simpa only [index_def, toLinearMap_neg, hneg] using
    (T : E →ₗ[𝕜] F).index_equiv_comp (LinearEquiv.neg 𝕜)

/-- Postcomposing with a continuous linear equivalence leaves the index unchanged. -/
@[simp] lemma index_equiv_comp (T : E →L[𝕜] F) (e : F ≃L[𝕜] G) :
    ContinuousLinearMap.index ((e : F →L[𝕜] G).comp T) = ContinuousLinearMap.index T := by
  rw [ContinuousLinearMap.index_def, ContinuousLinearMap.index_def,
    ContinuousLinearMap.toLinearMap_comp,
    ContinuousLinearEquiv.toLinearMap_toContinuousLinearMap]
  rw [LinearMap.index_equiv_comp]

/-- Precomposing with a continuous linear equivalence leaves the index unchanged. -/
@[simp] lemma index_comp_equiv (T : E →L[𝕜] F) (e : G ≃L[𝕜] E) :
    ContinuousLinearMap.index (T.comp (e : G →L[𝕜] E)) = ContinuousLinearMap.index T := by
  rw [ContinuousLinearMap.index_def, ContinuousLinearMap.index_def,
    ContinuousLinearMap.toLinearMap_comp,
    ContinuousLinearEquiv.toLinearMap_toContinuousLinearMap]
  rw [LinearMap.index_comp_equiv]

end Ring

section DivisionRing

variable {𝕜 : Type*} [DivisionRing 𝕜]
variable {E F : Type*}
variable [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
variable [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F]

/-- Between finite-dimensional spaces the index is `dim E − dim F`, for any operator. -/
lemma index_eq_of_finiteDimensional [FiniteDimensional 𝕜 E]
    [FiniteDimensional 𝕜 F]
    (T : E →L[𝕜] F) : ContinuousLinearMap.index T = (finrank 𝕜 E : ℤ) - finrank 𝕜 F := by
  rw [ContinuousLinearMap.index_def, LinearMap.index_eq_of_finiteDimensional]

/-- A surjective operator of index zero with finite-dimensional kernel is bijective. Only
finiteness of the kernel is used, not the full Fredholm property. This is the converse of
`ContinuousLinearMap.index_eq_zero_of_bijective` for a surjective operator. -/
lemma bijective_of_surjective_of_index_eq_zero (T : E →L[𝕜] F)
    (hfin : FiniteDimensional 𝕜 T.ker) (hT : Function.Surjective T)
    (hindex : T.index = 0) : Function.Bijective T := by
  have := hfin
  have hker : T.ker = ⊥ :=
    Submodule.finrank_eq_zero.1
      ((T.finrank_ker_eq_iff_index_eq hT).2 (by exact_mod_cast hindex))
  exact ⟨LinearMap.ker_eq_bot.1 hker, hT⟩

end DivisionRing

section Field

variable {𝕜 : Type*} [Field 𝕜]
variable {E F : Type*}
variable [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
variable [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F] [ContinuousConstSMul 𝕜 F]

/-- The index is unchanged by a nonzero scalar multiple. -/
lemma index_smul (T : E →L[𝕜] F) {c : 𝕜} (hc : c ≠ 0) :
    ContinuousLinearMap.index (c • T) = ContinuousLinearMap.index T := by
  rw [ContinuousLinearMap.index_def, ContinuousLinearMap.index_def,
    ContinuousLinearMap.toLinearMap_smul, LinearMap.index_smul _ hc]

end Field

end ContinuousLinearMap
