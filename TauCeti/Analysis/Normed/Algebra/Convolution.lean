/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Module.Finite.Dual
public import TauCeti.Analysis.Normed.Module.TensorProduct.Ultra
public import TauCeti.Algebra.Coalgebra.Convolution.Scalar

/-!
# Sup norms on convolution algebras

The dual of a finite module over a ring mapping into the unit ball of an ultrametric
field carries the sup norm `LinearMap.supNorm`. Exterior products have exactly the
product norm. Convolution is submultiplicative, since it is an exterior product
precomposed with comultiplication; its unit has norm at most one.

For a bialgebra, transposing multiplication and tensoring with the counit give
homomorphisms between the convolution algebras of the bialgebra and its tensor square.
Transposition does not increase the sup norm, and the counit maps are the exterior products
with the convolution unit, whose norms are given by `WithConv.supNorm_mulTensor`.
These estimates are independent of any choice of generators or basis.
No norm instances are installed on linear maps or on `WithConv`.

## References

These norms on convolution algebras are the setting of the bound for the cokernel of the
Hodge–Tate map in L. Alpöge's formal Lean proof of the Riemann hypothesis for Dirichlet
L-functions (2026), https://github.com/leanprover-community/riemann-hypothesis. The estimates
here are elementary, and the formalization is independent of that source. The exterior
convolution product and its multiplicativity are supplied by `WithConv.mulTensor` and
`WithConv.mulTensor_convMul`.
-/

public section

open TensorProduct WithConv


namespace CoalgHom

variable {R C M N : Type*} [CommSemiring R] [NormedField C] [Algebra R C]
  [AddCommMonoid M] [Module R M] [Coalgebra R M] [Module.Finite R M]
  [AddCommMonoid N] [Module R N] [Coalgebra R N]

/-- Precomposition by a coalgebra homomorphism does not increase the sup norm. -/
theorem supNorm_convPrecompCoefficients_le (h : N →ₗc[R] M)
    (f : WithConv (M →ₗ[R] C)) (hR : ∀ r : R, ‖algebraMap R C r‖ ≤ 1) :
    (h.convPrecompCoefficients f).ofConv.supNorm ≤ f.ofConv.supNorm := by
  rw [convPrecompCoefficients_apply]
  exact f.ofConv.supNorm_comp_le h.toLinearMap hR

end CoalgHom

namespace WithConv

variable {R C M N : Type*} [CommSemiring R] [NormedField C] [Algebra R C]
  [AddCommMonoid M] [Module R M] [Module.Finite R M]
  [AddCommMonoid N] [Module R N] [Module.Finite R N]

/-- Exterior products of field-valued linear maps have exactly the product sup norm. -/
theorem supNorm_mulTensor (f : WithConv (M →ₗ[R] C)) (g : WithConv (N →ₗ[R] C))
    (hR : ∀ r : R, ‖algebraMap R C r‖ ≤ 1) :
    (mulTensor f g).ofConv.supNorm = f.ofConv.supNorm * g.ofConv.supNorm := by
  have := IsUltrametricDist.isUltrametricDist_of_forall_norm_algebraMap_le_one hR
  apply le_antisymm
  · apply ((mulTensor f g).ofConv.supNorm_le_iff hR).mpr
    apply LinearMap.norm_apply_le_of_tmul
    intro m n
    simp only [mulTensor_apply_tmul, norm_mul]
    exact mul_le_mul (f.ofConv.norm_apply_le_supNorm hR m)
      (g.ofConv.norm_apply_le_supNorm hR n) (norm_nonneg _) (f.ofConv.supNorm_nonneg)
  · obtain ⟨m, hm⟩ := f.ofConv.exists_norm_eq_supNorm hR
    obtain ⟨n, hn⟩ := g.ofConv.exists_norm_eq_supNorm hR
    simpa only [mulTensor_apply_tmul, norm_mul, hm, hn] using
      (mulTensor f g).ofConv.norm_apply_le_supNorm hR (m ⊗ₜ[R] n)

/-- Convolution is submultiplicative for the sup norm. -/
theorem supNorm_convMul_le [CoalgebraStruct R M] (f g : WithConv (M →ₗ[R] C))
    (hR : ∀ r : R, ‖algebraMap R C r‖ ≤ 1) :
    (f * g).ofConv.supNorm ≤ f.ofConv.supNorm * g.ofConv.supNorm := by
  have := IsUltrametricDist.isUltrametricDist_of_forall_norm_algebraMap_le_one hR
  apply ((f * g).ofConv.supNorm_le_iff hR).mpr
  intro m
  rw [(Coalgebra.Repr.arbitrary R m).convMul_apply]
  apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg
    (mul_nonneg (f.ofConv.supNorm_nonneg) (g.ofConv.supNorm_nonneg))
  intro i _
  rw [norm_mul]
  exact mul_le_mul (f.ofConv.norm_apply_le_supNorm hR _)
    (g.ofConv.norm_apply_le_supNorm hR _) (norm_nonneg _) (f.ofConv.supNorm_nonneg)

omit [Module.Finite R M] in
/-- The values of the counit-induced element lie in the closed unit ball, since they come
from the base ring. -/
theorem norm_convOne_apply_le [CoalgebraStruct R M]
    (hR : ∀ r : R, ‖algebraMap R C r‖ ≤ 1) (m : M) :
    ‖(1 : WithConv (M →ₗ[R] C)).ofConv m‖ ≤ 1 := by
  simpa only [LinearMap.convOne_apply] using hR (Coalgebra.counit m)

omit [Module.Finite R M] in
/-- The counit-induced element has sup norm at most one, since its values come from the
base ring. It is a convolution unit when the coalgebra laws hold. -/
theorem supNorm_convOne_le [CoalgebraStruct R M]
    (hR : ∀ r : R, ‖algebraMap R C r‖ ≤ 1) :
    (1 : WithConv (M →ₗ[R] C)).ofConv.supNorm ≤ 1 := by
  rw [LinearMap.supNorm_def]
  exact ciSup_le (norm_convOne_apply_le hR)

end WithConv

namespace WithConv

variable {R C A : Type*} [CommSemiring R] [NormedField C] [Algebra R C]
  [Semiring A] [_root_.Bialgebra R A] [Module.Finite R A]

/-- Transposing multiplication does not increase the sup norm. -/
theorem supNorm_convolutionDelta_le (f : WithConv (A →ₗ[R] C))
    (hR : ∀ r : R, ‖algebraMap R C r‖ ≤ 1) :
    (TauCeti.Bialgebra.convolutionDelta R C A f).ofConv.supNorm ≤ f.ofConv.supNorm := by
  rw [TauCeti.Bialgebra.convolutionDelta_def]
  exact (Bialgebra.mulCoalgHom R A).supNorm_convPrecompCoefficients_le f hR

omit [Module.Finite R A] in
/-- On the convolution algebra of a bialgebra the counit has sup norm exactly one. -/
theorem supNorm_convOne_eq_one (hR : ∀ r : R, ‖algebraMap R C r‖ ≤ 1) :
    (1 : WithConv (A →ₗ[R] C)).ofConv.supNorm = 1 := by
  apply le_antisymm (WithConv.supNorm_convOne_le hR)
  have hb : BddAbove (Set.range fun a ↦ ‖(1 : WithConv (A →ₗ[R] C)).ofConv a‖) :=
    ⟨1, Set.forall_mem_range.2 (norm_convOne_apply_le hR)⟩
  simpa only [LinearMap.convOne_apply, Bialgebra.counit_one, map_one, norm_one,
    LinearMap.supNorm_def] using
    (le_ciSup hb (1 : A))

end WithConv
