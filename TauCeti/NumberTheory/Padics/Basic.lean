/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.MulAction
public import Mathlib.NumberTheory.Padics.PadicIntegers

/-!
# Basic instances for the `p`-adic numbers

This file provides a direct instance for the nontriviality of `ℚ_[p]`, already implied by
its field structure, and an instance expressing that `2` is invertible. These instances support
finite-dimensional constructions and algebraic trace and norm calculations over the `p`-adic field.

It also records that the scalar action of `ℤ_[p]` on `ℚ_[p]` multiplies norms,
`‖a • x‖ = ‖a‖ * ‖x‖`. In particular the action is contractive, so `ℚ_[p]` itself is a
coefficient ring for Mathlib's Mahler isometry `PadicInt.mahlerEquiv` and for the Amice transform
of measures on `ℤ_p`.

Finally, it records that the inclusion `PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p]` is the structure
map of the `ℤ_[p]`-algebra `ℚ_[p]`, and that it is a topological embedding of norm at most `1` whose
range contains the closed unit ball. These are the hypotheses under which `ℚ_[p]`-valued measures
of norm at most `1` come from `ℤ_[p]`-valued measures.
-/

public section

noncomputable section

namespace TauCeti

/-- A direct instance of the existing fact that the `p`-adic field has distinct zero and one. -/
-- Avoid backtracking through Henselian-ring instances during rank and freeness synthesis.
instance (p : ℕ) [Fact (Nat.Prime p)] : Nontrivial ℚ_[p] :=
  @DivisionRing.toNontrivial _ (instFieldPadic p).toDivisionRing

/-- Two is invertible in the `p`-adic field, including when `p = 2`. -/
instance instInvertibleTwoPadic (p : ℕ) [Fact (Nat.Prime p)] : Invertible (2 : ℚ_[p]) :=
  invertibleOfNonzero two_ne_zero

/-- The scalar action of `ℤ_[p]` on `ℚ_[p]` is multiplication by the inclusion, so it multiplies
norms. This also provides the contractive action `IsBoundedSMul ℤ_[p] ℚ_[p]`. -/
instance normSMulClass_padicInt_padic (p : ℕ) [Fact (Nat.Prime p)] :
    NormSMulClass ℤ_[p] ℚ_[p] :=
  ⟨fun a x ↦ by rw [Algebra.smul_def, norm_mul, PadicInt.algebraMap_apply, PadicInt.norm_coe]⟩

end TauCeti

namespace PadicInt

variable {p : ℕ} [Fact (Nat.Prime p)]

/-- The structure map of the `ℤ_[p]`-algebra `ℚ_[p]` is the inclusion `PadicInt.Coe.ringHom`. -/
theorem algebraMap_eq_coe_ringHom : algebraMap ℤ_[p] ℚ_[p] = Coe.ringHom :=
  RingHom.ext algebraMap_apply

/-- The inclusion `ℤ_[p] → ℚ_[p]` takes values in the closed unit ball. -/
theorem norm_coe_ringHom_le_one (a : ℤ_[p]) : ‖Coe.ringHom a‖ ≤ 1 := by
  simpa using a.norm_le_one

/-- The inclusion `ℤ_[p] → ℚ_[p]` is a topological embedding. -/
theorem isEmbedding_coe_ringHom : Topology.IsEmbedding (Coe.ringHom (p := p)) :=
  isometry_subtype_coe.isEmbedding

/-- Every element of the closed unit ball of `ℚ_[p]` lies in the image of `ℤ_[p]`. -/
theorem closedBall_subset_range_coe_ringHom :
    Metric.closedBall (0 : ℚ_[p]) 1 ⊆ Set.range (Coe.ringHom (p := p)) :=
  fun x hx ↦ ⟨⟨x, mem_closedBall_zero_iff.mp hx⟩, rfl⟩

end PadicInt
