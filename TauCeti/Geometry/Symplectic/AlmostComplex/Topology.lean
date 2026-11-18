/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.AlmostComplex
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import TauCeti.Topology.Algebra.Module.BilinearForm

import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import TauCeti.Geometry.Symplectic.Duality

/-!
# The topology on linear complex structures

The complex structures of a finite-dimensional real normed space carry the topology induced by
the operator norm of their endomorphisms. Since all norms on a finite-dimensional space are
equivalent, it does not depend on the choice of the norm of `V`.

## Main declarations

* The instance `TopologicalSpace (TauCeti.AlmostComplexStructure V)`: the topology induced from
  the operator norm on `V →L[ℝ] V`.
* `TauCeti.AlmostComplexStructure.isEmbedding_toContinuousLinearMap`: sending a complex
  structure to its continuous endomorphism is a topological embedding.
* `TauCeti.AlmostComplexStructure.continuous_iff`: continuity of maps into the complex
  structures is continuity of their endomorphisms in the operator norm.
* `TauCeti.AlmostComplexStructure.toContinuousLinearMap_mul_self`: in the operator-norm algebra a
  complex structure squares to `-1`.
* `TauCeti.AlmostComplexStructure.toContinuousLinearMap_cayley`: in operator-norm coordinates the
  Cayley transform is the rational expression `-(1 + J₀ J₁)(1 - J₀ J₁)⁻¹`.
* `TauCeti.SymplecticForm.Tames.eventually_of_continuousAt`: tameness is an open condition along
  families that are continuous in the operator norm.
* `TauCeti.SymplecticForm.exists_pos_forall_mul_norm_sq_le_associatedBilinForm`: along a family
  of tame structures continuous on a compact set, the forms `ω(·, J ·)` are uniformly equivalent
  to the square of the norm.
* `TauCeti.SymplecticForm.continuousOn_associatedBilinForm_apply_self`: the forms `ω(·, J ·)` of
  a continuous family of structures, evaluated along a continuous map, vary continuously.
-/

public noncomputable section

open Filter Topology

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

namespace AlmostComplexStructure

/-- The topology on the complex structures of a finite-dimensional real normed space induced by
the operator norm of their endomorphisms. Since all norms on a finite-dimensional space are
equivalent, it does not depend on the choice of the norm of `V`. -/
instance : TopologicalSpace (AlmostComplexStructure V) :=
  .induced (fun J ↦ LinearMap.toContinuousLinearMap J.toLinearMap) inferInstance

/-- Sending a complex structure to its endomorphism is a topological embedding into the
continuous endomorphisms. -/
theorem isEmbedding_toContinuousLinearMap :
    IsEmbedding fun J : AlmostComplexStructure V ↦ LinearMap.toContinuousLinearMap J.toLinearMap :=
  ⟨⟨rfl⟩, LinearMap.toContinuousLinearMap.injective.comp toLinearMap_injective⟩

/-- A map into the complex structures is continuous exactly when its endomorphisms are
continuous in the operator norm. -/
theorem continuous_iff {X : Type*} [TopologicalSpace X] {f : X → AlmostComplexStructure V} :
    Continuous f ↔ Continuous fun x ↦ LinearMap.toContinuousLinearMap (f x).toLinearMap :=
  isEmbedding_toContinuousLinearMap.continuous_iff

/-- In the operator-norm algebra, an almost complex structure squares to `-1`. -/
@[simp]
theorem toContinuousLinearMap_mul_self (J : AlmostComplexStructure V) :
    LinearMap.toContinuousLinearMap J.toLinearMap * LinearMap.toContinuousLinearMap J.toLinearMap =
      -1 := by
  ext v
  simp

/-- In operator-norm coordinates, the Cayley transform is the rational expression
`-(1 + J₀ J₁)(1 - J₀ J₁)⁻¹` of the continuous endomorphisms `J₀` and `J₁`, with the junk
inverse `0` when `1 - J₀ J₁` is not invertible on either side. -/
theorem toContinuousLinearMap_cayley (J₀ J₁ : AlmostComplexStructure V) {A B : V →L[ℝ] V}
    (hA : A.toLinearMap = J₀.toLinearMap) (hB : B.toLinearMap = J₁.toLinearMap) :
    LinearMap.toContinuousLinearMap (J₀.cayley J₁) = cayleyFormula A B := by
  have hA' : LinearMap.toContinuousLinearMap J₀.toLinearMap = A :=
    ContinuousLinearMap.coe_injective (by rw [LinearMap.coe_toContinuousLinearMap, hA])
  have hB' : LinearMap.toContinuousLinearMap J₁.toLinearMap = B :=
    ContinuousLinearMap.coe_injective (by rw [LinearMap.coe_toContinuousLinearMap, hB])
  rw [← hA', ← hB', cayley_eq_cayleyFormula]
  exact map_cayleyFormula (Module.End.toContinuousLinearMap V) J₀.toLinearMap J₁.toLinearMap

end AlmostComplexStructure

namespace SymplecticForm

/-- Tameness is an open condition: if a family of complex structures is continuous at `x` in
the operator-norm topology and `ω`-tame there, it is `ω`-tame near `x`. -/
theorem Tames.eventually_of_continuousAt {X : Type*} [TopologicalSpace X] {ω : SymplecticForm V}
    {J : X → AlmostComplexStructure V} {x : X}
    (hJ : ContinuousAt (fun y => LinearMap.toContinuousLinearMap (J y).toLinearMap) x)
    (h : ω.Tames (J x)) : ∀ᶠ y in 𝓝 x, ω.Tames (J y) := by
  let ωc := ω.toBilinForm.toContinuousBilinearMap
  -- The forms `ω(·, A ·)` depend continuously on the operator `A`, and positivity is open.
  have hc : Continuous fun A : V →L[ℝ] V => (ContinuousLinearMap.compL ℝ V V ℝ).flip A ∘L ωc := by
    fun_prop
  have hA : ∀ᶠ A in 𝓝 (LinearMap.toContinuousLinearMap (J x).toLinearMap),
      ∀ v, v ≠ 0 → 0 < ((ContinuousLinearMap.compL ℝ V V ℝ).flip A ∘L ωc) v v :=
    hc.continuousAt.preimage_mem_nhds (isOpen_setOf_forall_bilinear_apply_self_pos.mem_nhds
      fun v hv => by simpa [ωc] using h v hv)
  filter_upwards [hJ.eventually hA] with y hy v hv
  simpa [ωc] using hy v hv

/-- **Uniform equivalence of tame metrics.** If a family of complex structures `J_x` is continuous
in the operator norm on a compact set `K` and `ω`-tame there, the forms `g_x = ω(·, J_x ·)` are
uniformly equivalent to the square of the norm over `K`: there are constants `a > 0` and `b ≥ 0`
with `a ‖v‖² ≤ g_x(v, v) ≤ b ‖v‖²` for every `x ∈ K` and every vector `v`. -/
theorem exists_pos_forall_mul_norm_sq_le_associatedBilinForm (ω : SymplecticForm V)
    {X : Type*} [TopologicalSpace X] {J : X → AlmostComplexStructure V} {K : Set X}
    (hK : IsCompact K)
    (hJ : ContinuousOn (fun x ↦ LinearMap.toContinuousLinearMap (J x).toLinearMap) K)
    (hJt : ∀ x ∈ K, ω.Tames (J x)) :
    ∃ a > 0, ∃ b ≥ 0, ∀ x ∈ K, ∀ v,
      a * ‖v‖ ^ 2 ≤ ω.associatedBilinForm (J x) v v ∧
        ω.associatedBilinForm (J x) v v ≤ b * ‖v‖ ^ 2 := by
  set e : X → V →L[ℝ] V := fun x ↦ LinearMap.toContinuousLinearMap (J x).toLinearMap
  set ωc := ω.toBilinForm.toContinuousBilinearMap
  obtain ⟨a, ha, hlow⟩ := (hK.image_of_continuousOn hJ).exists_pos_forall_mul_norm_sq_le_compRight
    ωc (by
      rintro _ ⟨x, hx, rfl⟩ v hv
      simpa [e, ωc] using hJt x hx v hv)
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hJ
  refine ⟨a, ha, ‖ωc‖ * max M 0, by positivity, fun x hx v ↦
    ⟨by simpa [e, ωc] using hlow _ ⟨x, hx, rfl⟩ v, ?_⟩⟩
  have h₁ : ω.associatedBilinForm (J x) v v = ωc v (e x v) := by simp [e, ωc]
  rw [h₁]
  calc ωc v (e x v) ≤ ‖ωc v (e x v)‖ := Real.le_norm_self _
    _ ≤ ‖ωc‖ * ‖v‖ * ‖e x v‖ := ωc.le_opNorm₂ _ _
    _ ≤ ‖ωc‖ * ‖v‖ * (max M 0 * ‖v‖) := by
        gcongr
        exact (e x).le_opNorm v |>.trans
          (mul_le_mul_of_nonneg_right ((hM x hx).trans (le_max_left _ _)) (norm_nonneg _))
    _ = ‖ωc‖ * max M 0 * ‖v‖ ^ 2 := by ring

/-- The map `x ↦ g_x(f x, f x)` for `g_x = ω(·, J(x) ·)` is continuous on a set when `J` and `f`
are. -/
theorem continuousOn_associatedBilinForm_apply_self {ω : SymplecticForm V} {X : Type*}
    [TopologicalSpace X] {J : X → AlmostComplexStructure V} {s : Set X}
    (hJc : ContinuousOn (fun x ↦ (J x).toLinearMap.toContinuousLinearMap) s) {f : X → V}
    (hf : ContinuousOn f s) :
    ContinuousOn (fun x ↦ ω.associatedBilinForm (J x) (f x) (f x)) s := by
  simpa using ω.continuousOn_apply_comp hf (hJc.clm_apply hf)

end SymplecticForm

end TauCeti
