/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import TauCeti.Geometry.Symplectic.AlmostComplex

/-!
# The standard compatible triple on `V × V`

For a real inner product space `V`, the doubled space `V × V` carries a canonical compatible
triple `(ω, J, g)`: the standard symplectic form `ω₀`, the product almost complex structure
`J(x, y) = (-y, x)` from `TauCeti.AlmostComplexStructure.product`, and the componentwise inner
product `g` recovered as `ω₀(·, J ·)`. When `V = ℝ^n`, this specializes to the standard model
`ℝ^{2n} = ℝ^n ⊕ ℝ^n`; in general it serves as a non-vacuous witness that the pointwise
almost-complex/symplectic definitions of `AlmostComplex.lean` are inhabited and interact as
the standard conventions require.

## Main declarations

* `TauCeti.stdSymplecticForm`: the standard symplectic form
  `ω₀((x₁, y₁), (x₂, y₂)) = ⟪x₁, y₂⟫ - ⟪y₁, x₂⟫` on `V × V`.
* `TauCeti.stdSymplecticForm_invariant_product`: `ω₀` is invariant under the product almost
  complex structure `J`.
* `TauCeti.stdSymplecticForm_tames_product`: `ω₀` tames `J`, with `ω₀(v, J v) = ‖v.1‖² + ‖v.2‖²`.
* `TauCeti.stdSymplecticForm_compatible_product`: `ω₀` is compatible with `J`.
* `TauCeti.stdSymplecticForm_associatedBilinForm_product`: the metric `g = ω₀(·, J ·)` is the
  sum of the inner products pulled back from the two factors.

The conventions follow McDuff--Salamon, *J-holomorphic Curves and Symplectic Topology*,
Section 2.1, where `(ℝ^{2n}, ω₀, J₀)` is the standard compatible model.
-/

public section

namespace TauCeti

open scoped InnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The standard symplectic bilinear form on `V × V`, given by
`ω₀((x₁, y₁), (x₂, y₂)) = ⟪x₁, y₂⟫ - ⟪y₁, x₂⟫`. -/
private noncomputable def stdSymplecticBilin : LinearMap.BilinForm ℝ (V × V) :=
  (innerₗ V).compl₁₂ (LinearMap.fst ℝ V V) (LinearMap.snd ℝ V V) -
    (innerₗ V).compl₁₂ (LinearMap.snd ℝ V V) (LinearMap.fst ℝ V V)

@[simp]
private lemma stdSymplecticBilin_apply (u w : V × V) :
    stdSymplecticBilin u w = ⟪u.1, w.2⟫_ℝ - ⟪u.2, w.1⟫_ℝ := by
  simp [stdSymplecticBilin]

private lemma stdSymplecticBilin_isAlt : (stdSymplecticBilin (V := V)).IsAlt := by
  intro u
  simp [real_inner_comm]

private lemma stdSymplecticBilin_nondegenerate :
    (stdSymplecticBilin (V := V)).Nondegenerate := by
  refine (LinearMap.IsAlt.isRefl (B := stdSymplecticBilin (V := V))
    stdSymplecticBilin_isAlt).nondegenerate_iff_separatingLeft.mpr ?_
  intro u hu
  have h : ⟪u.1, u.1⟫_ℝ + ⟪u.2, u.2⟫_ℝ = 0 := by
    simpa using hu (-u.2, u.1)
  have hzero := (add_eq_zero_iff_of_nonneg real_inner_self_nonneg
    real_inner_self_nonneg).mp h
  exact Prod.ext (inner_self_eq_zero.mp hzero.1) (inner_self_eq_zero.mp hzero.2)

/-- The standard symplectic form `ω₀((x₁, y₁), (x₂, y₂)) = ⟪x₁, y₂⟫ - ⟪y₁, x₂⟫` on `V × V`. -/
noncomputable def stdSymplecticForm : SymplecticForm (V × V) where
  toBilinForm := stdSymplecticBilin
  isAlt := stdSymplecticBilin_isAlt
  nondegenerate := stdSymplecticBilin_nondegenerate

/-- The coordinate formula for evaluating the standard symplectic form on two vectors of `V × V`. -/
@[simp]
lemma stdSymplecticForm_apply (u w : V × V) :
    stdSymplecticForm u w = ⟪u.1, w.2⟫_ℝ - ⟪u.2, w.1⟫_ℝ := by
  simp [stdSymplecticForm]

/-- The standard symplectic form is invariant under the product almost complex structure. -/
lemma stdSymplecticForm_invariant_product :
    (stdSymplecticForm (V := V)).Invariant (AlmostComplexStructure.product V) := by
  rw [SymplecticForm.invariant_iff]
  intro v w
  simp [sub_eq_add_neg, add_comm]

/-- `ω₀(v, J v) = ‖v.1‖² + ‖v.2‖²` for the product almost complex structure `J`. -/
lemma stdSymplecticForm_apply_product_self (v : V × V) :
    stdSymplecticForm v (AlmostComplexStructure.product V v) = ⟪v.1, v.1⟫_ℝ + ⟪v.2, v.2⟫_ℝ := by
  simp

/-- The standard symplectic form tames the product almost complex structure. -/
lemma stdSymplecticForm_tames_product :
    (stdSymplecticForm (V := V)).Tames (AlmostComplexStructure.product V) := by
  intro v hv
  rw [stdSymplecticForm_apply_product_self]
  by_cases h1 : v.1 = 0
  · have h2 : v.2 ≠ 0 := fun h2 => hv (Prod.ext_iff.2 ⟨h1, h2⟩)
    have hpos : 0 < ⟪v.2, v.2⟫_ℝ := real_inner_self_pos.2 h2
    simpa [h1] using hpos
  · have hpos : 0 < ⟪v.1, v.1⟫_ℝ := real_inner_self_pos.2 h1
    exact add_pos_of_pos_of_nonneg hpos real_inner_self_nonneg

/-- The standard symplectic form is compatible with the product almost complex structure. -/
lemma stdSymplecticForm_compatible_product :
    (stdSymplecticForm (V := V)).Compatible (AlmostComplexStructure.product V) :=
  SymplecticForm.Compatible.of_tames stdSymplecticForm_invariant_product
    stdSymplecticForm_tames_product

/-- The metric `g = ω₀(·, J ·)` associated to the standard compatible triple is the
sum of the inner products pulled back along the two coordinate projections. In particular,
`g(u, w) = ⟪u.1, w.1⟫ + ⟪u.2, w.2⟫`. -/
lemma stdSymplecticForm_associatedBilinForm_product :
    (stdSymplecticForm (V := V)).associatedBilinForm (AlmostComplexStructure.product V) =
      (innerₗ V).compl₁₂ (LinearMap.fst ℝ V V) (LinearMap.fst ℝ V V) +
        (innerₗ V).compl₁₂ (LinearMap.snd ℝ V V) (LinearMap.snd ℝ V V) := by
  apply LinearMap.ext₂
  intro u w
  simp

end TauCeti
