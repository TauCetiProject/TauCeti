/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.AlmostComplex.StructureVariation
public import TauCeti.Geometry.Symplectic.Prod.Basic
public import TauCeti.Geometry.Symplectic.StandardCompatible
public import TauCeti.Geometry.Symplectic.TameMetric

import TauCeti.Analysis.Normed.Algebra.NilpotentExponential

/-!
# A path of tame structures on `ℝ⁴` that leaves the compatible ones

On `ℝ⁴ = ℝ² × ℝ²` with the split symplectic form `ω = ω₀ ⊕ ω₀`,
`ω₀((a, b), (a', b')) = a b' - b a'`, and the standard compatible structure `J₀ = j ⊕ j`,
`j (a, b) = (-b, a)`, consider the variation

`Y (v₁, v₂) = (C v₂, 0)`, `C = [[0, -2], [-2, 0]]`

(`TauCeti.SymplecticForm.TameNotCompatibleExample.shearDirection`). All declarations of this file
live in the namespace `TauCeti.SymplecticForm.TameNotCompatibleExample`, since they concern this
one fixed example. The variation `Y` anticommutes with `J₀`, so it is a tangent vector to the space
of complex structures at `J₀`
(`TauCeti.SymplecticForm.TameNotCompatibleExample.shearDirection_mem_tangentSpace`), but it is not
skew-adjoint for `ω`, so it is not tangent to the compatible structures
(`TauCeti.SymplecticForm.TameNotCompatibleExample.shearDirection_notMem_compatibleTangentSpace`).

Its tangent path `J_ε = exp(ε B) J₀ exp(-ε B)`, `B = ½ J₀ Y`
(`TauCeti.AlmostComplexStructure.tangentPath`), is the family
`TauCeti.SymplecticForm.TameNotCompatibleExample.shearComplexStructure`.
Here `B (v₁, v₂) = (diag(1, -1) v₂, 0)` squares to zero, so `exp(ε B)` is the shear
`[[I, ε diag(1, -1)], [0, I]]`, and the path is the straight line `J_ε = J₀ + ε Y`
(`TauCeti.SymplecticForm.TameNotCompatibleExample.shearComplexStructure_apply`), that is
`J_ε = [[j, ε C], [0, j]]`; at `ε = 0` it is `J₀`
(`TauCeti.SymplecticForm.TameNotCompatibleExample.shearComplexStructure_zero`). Along it

`ω(v, J_ε v) = |v|² + ε ω₀(v₁, C v₂) = |v|² + 2 ε (b d - a c)` for `v = ((a, b), (c, d))`

(`TauCeti.SymplecticForm.TameNotCompatibleExample.apply_shearComplexStructure_self`). Since
`|ω₀(v₁, C v₂)| ≤ |v|²`, this gives:

* `TauCeti.SymplecticForm.TameNotCompatibleExample.tames_shearComplexStructure_iff`: `ω` tames
  `J_ε` exactly when `|ε| < 1`. At `ε = 1` the vector `v = ((1, 0), (1, 0))` has
  `ω(v, J₁ v) = 0`, so the unscaled shear is not tame.
* `TauCeti.SymplecticForm.TameNotCompatibleExample.compatible_shearComplexStructure_iff`: `ω` is
  compatible with `J_ε` only for `ε = 0`, since `ω(J_ε e₃, J_ε e₄) = 1 - 4 ε²` while
  `ω(e₃, e₄) = 1`
  (`TauCeti.SymplecticForm.TameNotCompatibleExample.invariant_shearComplexStructure_iff`).
* `TauCeti.SymplecticForm.TameNotCompatibleExample.gradientOperator_ne_shearComplexStructure`: for
  `0 < |ε| < 1` the gradient operator of the tame pair `(ω, J_ε)` is not `J_ε`, so
  `J_ε (γ' - X_H)` is not the gradient of the action for the symmetrized metric of `(ω, J_ε)`.

So this particular path, through an anti-`J₀` direction that is not tangent to the compatible
structures, is tame exactly on the bounded interval `|ε| < 1`. By contrast, the tangent path of
a compatible structure in a compatible direction stays compatible for all times
(`TauCeti.SymplecticForm.Compatible.tangentPath`), while for a tame structure and an arbitrary
direction the general result `TauCeti.SymplecticForm.Tames.eventually_tangentPath` only gives
tameness for small times. On `ℝ⁴` the tame structures are therefore strictly more than the
compatible ones, while in dimension `2` they coincide
(`TauCeti.SymplecticForm.Tames.compatible_of_finrank_le_two`).

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications 52, 2012, Sections 2.1 and 2.5 (tame and compatible structures and the
  metric of a tame structure).
-/

public section

namespace TauCeti.SymplecticForm.TameNotCompatibleExample

open NormedSpace

/-- The variation `Y (v₁, v₂) = (C v₂, 0)` of the standard complex structure of `ℝ² × ℝ²`, with
`C = [[0, -2], [-2, 0]]`. It anticommutes with `J₀ = j ⊕ j`
(`TauCeti.SymplecticForm.TameNotCompatibleExample.shearDirection_mem_tangentSpace`), and is not
skew-adjoint for `ω₀ ⊕ ω₀`
(`TauCeti.SymplecticForm.TameNotCompatibleExample.shearDirection_notMem_compatibleTangentSpace`). -/
noncomputable def shearDirection : ((ℝ × ℝ) × (ℝ × ℝ)) →L[ℝ] ((ℝ × ℝ) × (ℝ × ℝ)) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v ↦ ((-2 * v.2.2, -2 * v.2.1), 0)
      map_add' := fun v w ↦ by ext <;> simp <;> ring
      map_smul' := fun c v ↦ by ext <;> simp <;> ring }

@[simp]
theorem shearDirection_apply (v : (ℝ × ℝ) × (ℝ × ℝ)) :
    shearDirection v = ((-2 * v.2.2, -2 * v.2.1), 0) :=
  (rfl)

/-- The variation `Y` anticommutes with the standard complex structure `J₀ = j ⊕ j`, so it is
tangent to the space of complex structures at `J₀`. -/
theorem shearDirection_mem_tangentSpace :
    (shearDirection : Module.End ℝ ((ℝ × ℝ) × (ℝ × ℝ))) ∈
      ((AlmostComplexStructure.product ℝ).prod
        (AlmostComplexStructure.product ℝ)).tangentSpace := by
  refine AlmostComplexStructure.mem_tangentSpace_iff_apply.2 fun v ↦ ?_
  ext <;> simp

/-- The variation `Y` is not skew-adjoint for `ω₀ ⊕ ω₀`, so it is not tangent to the compatible
structures at `J₀`. -/
theorem shearDirection_notMem_compatibleTangentSpace :
    (shearDirection : Module.End ℝ ((ℝ × ℝ) × (ℝ × ℝ))) ∉
      ((stdSymplecticForm (V := ℝ)).prod stdSymplecticForm).compatibleTangentSpace
        ((AlmostComplexStructure.product ℝ).prod (AlmostComplexStructure.product ℝ)) := by
  intro h
  have := (SymplecticForm.mem_compatibleTangentSpace.1 h).2 ((0, 0), (1, 0)) ((1, 0), (0, 0))
  norm_num at this

/-- The family `J_ε` of complex structures on `ℝ² × ℝ²`: the tangent path
`exp(ε B) J₀ exp(-ε B)`, `B = ½ J₀ Y`, of the standard structure `J₀ = j ⊕ j` in the direction
`Y = TauCeti.SymplecticForm.TameNotCompatibleExample.shearDirection`. It is the straight line
`J₀ + ε Y` (`TauCeti.SymplecticForm.TameNotCompatibleExample.shearComplexStructure_apply`). -/
noncomputable def shearComplexStructure (ε : ℝ) :
    AlmostComplexStructure ((ℝ × ℝ) × (ℝ × ℝ)) :=
  ((AlmostComplexStructure.product ℝ).prod (AlmostComplexStructure.product ℝ)).tangentPath
    shearDirection ε

/-- At `ε = 0` the shear path is the standard structure `J₀ = j ⊕ j`. -/
@[simp]
theorem shearComplexStructure_zero :
    shearComplexStructure 0 =
      (AlmostComplexStructure.product ℝ).prod (AlmostComplexStructure.product ℝ) :=
  AlmostComplexStructure.tangentPath_zero _ _

/-- **The shear path is a straight line**: `J_ε = J₀ + ε Y`, that is
`J_ε ((a, b), (c, d)) = ((-b - 2 ε d, a - 2 ε c), (-d, c))`. -/
@[simp]
theorem shearComplexStructure_apply (ε : ℝ) (v : (ℝ × ℝ) × (ℝ × ℝ)) :
    shearComplexStructure ε v =
      (AlmostComplexStructure.product ℝ).prod (AlmostComplexStructure.product ℝ) v +
        ε • shearDirection v := by
  set B : ((ℝ × ℝ) × (ℝ × ℝ)) →L[ℝ] ((ℝ × ℝ) × (ℝ × ℝ)) := (2⁻¹ : ℝ) •
    (LinearMap.toContinuousLinearMap
      ((AlmostComplexStructure.product ℝ).prod (AlmostComplexStructure.product ℝ)).toLinearMap *
        shearDirection) with hB
  have hsq (t : ℝ) : (t • B) ^ 2 = 0 := by
    ext <;> simp [sq, hB]
  have h := congrArg (· v) (AlmostComplexStructure.toContinuousLinearMap_tangentPath
    ((AlmostComplexStructure.product ℝ).prod (AlmostComplexStructure.product ℝ)) shearDirection ε)
  simp only [LinearMap.coe_toContinuousLinearMap'] at h
  rw [shearComplexStructure, h, ← hB, exp_eq_one_add_of_sq_eq_zero ℝ (hsq ε), ← neg_smul,
    exp_eq_one_add_of_sq_eq_zero ℝ (hsq (-ε))]
  ext <;> simp [hB] <;> ring

/-- The diagonal of `ω₀ ⊕ ω₀` along the shear path:
`ω(v, J_ε v) = |v|² + 2 ε (b d - a c)` for `v = ((a, b), (c, d))`. -/
theorem apply_shearComplexStructure_self (ε : ℝ) (v : (ℝ × ℝ) × (ℝ × ℝ)) :
    ((stdSymplecticForm (V := ℝ)).prod stdSymplecticForm) v (shearComplexStructure ε v) =
      v.1.1 ^ 2 + v.1.2 ^ 2 + v.2.1 ^ 2 + v.2.2 ^ 2 +
        2 * ε * (v.1.2 * v.2.2 - v.1.1 * v.2.1) := by
  simp
  ring

/-- **The shear path is tame exactly for `|ε| < 1`.** The cross term `2 ε (b d - a c)` of
`ω(v, J_ε v)` is bounded by `|ε| |v|²`, and at `|ε| ≥ 1` the vector `((1, 0), (±1, 0))` has
`ω(v, J_ε v) = 2 - 2 |ε| ≤ 0`. -/
theorem tames_shearComplexStructure_iff {ε : ℝ} :
    ((stdSymplecticForm (V := ℝ)).prod stdSymplecticForm).Tames (shearComplexStructure ε) ↔
      |ε| < 1 := by
  refine ⟨fun h ↦ ?_, fun hε v hv ↦ ?_⟩
  · by_contra! hε
    rcases le_abs'.1 hε with hε | hε
    · have := h ((1, 0), (-1, 0)) (by simp)
      rw [apply_shearComplexStructure_self] at this
      norm_num at this
      linarith
    · have := h ((1, 0), (1, 0)) (by simp)
      rw [apply_shearComplexStructure_self] at this
      norm_num at this
      linarith
  · rw [apply_shearComplexStructure_self]
    obtain ⟨⟨a, b⟩, ⟨c, d⟩⟩ := v
    -- `|v|² > 0` is the tameness of `J₀`, the member `ε = 0` of the path.
    have hS : 0 < a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 := by
      have h₀ := (SymplecticForm.prod_compatible stdSymplecticForm_compatible_product
        stdSymplecticForm_compatible_product).tames _ hv
      rw [← shearComplexStructure_zero, apply_shearComplexStructure_self] at h₀
      simpa using h₀
    obtain ⟨hε₁, hε₂⟩ := abs_lt.1 hε
    rcases le_total 0 ε with h0 | h0
    · nlinarith [mul_pos (sub_pos.2 hε₂) hS,
        mul_nonneg h0 (add_nonneg (sq_nonneg (b + d)) (sq_nonneg (a - c)))]
    · nlinarith [mul_pos (neg_lt_iff_pos_add.1 hε₁) hS,
        mul_nonneg (neg_nonneg.2 h0) (add_nonneg (sq_nonneg (b - d)) (sq_nonneg (a + c)))]

/-- **`ω₀ ⊕ ω₀` is invariant under `J_ε` only at `ε = 0`**: for the last two basis vectors
`ω(J_ε e₃, J_ε e₄) = 1 - 4 ε²`, while `ω(e₃, e₄) = 1`. -/
theorem invariant_shearComplexStructure_iff {ε : ℝ} :
    ((stdSymplecticForm (V := ℝ)).prod stdSymplecticForm).Invariant (shearComplexStructure ε) ↔
      ε = 0 := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · have := (SymplecticForm.invariant_iff _ _).1 h ((0, 0), (1, 0)) ((0, 0), (0, 1))
    simp at this
    nlinarith [sq_nonneg ε]
  · rintro rfl
    simpa using
      SymplecticForm.prod_invariant stdSymplecticForm_invariant_product
        stdSymplecticForm_invariant_product

/-- **`J_ε` is compatible with `ω₀ ⊕ ω₀` only at `ε = 0`**, where it is the standard structure. So
for `0 < |ε| < 1` the structure `J_ε` is tame but not compatible
(`TauCeti.SymplecticForm.TameNotCompatibleExample.tames_shearComplexStructure_iff`). -/
theorem compatible_shearComplexStructure_iff {ε : ℝ} :
    ((stdSymplecticForm (V := ℝ)).prod stdSymplecticForm).Compatible (shearComplexStructure ε) ↔
      ε = 0 := by
  refine ⟨fun h ↦ invariant_shearComplexStructure_iff.1 h.invariant, ?_⟩
  rintro rfl
  simpa using
    SymplecticForm.prod_compatible stdSymplecticForm_compatible_product
      stdSymplecticForm_compatible_product

/-- For `ε ≠ 0` with `ω₀ ⊕ ω₀` taming `J_ε` (that is, `0 < |ε| < 1`), the gradient operator of the
tame pair is not `J_ε`: the gradient of the action for the symmetrized metric of `(ω, J_ε)` is not
`J_ε (γ' - X_H)`. -/
theorem gradientOperator_ne_shearComplexStructure {ε : ℝ}
    (h : ((stdSymplecticForm (V := ℝ)).prod stdSymplecticForm).Tames (shearComplexStructure ε))
    (hε : ε ≠ 0) :
    h.gradientOperator ≠ (shearComplexStructure ε).toLinearMap :=
  fun h' ↦ hε (compatible_shearComplexStructure_iff.1 (h.gradientOperator_eq_iff.1 h'))

end TauCeti.SymplecticForm.TameNotCompatibleExample
