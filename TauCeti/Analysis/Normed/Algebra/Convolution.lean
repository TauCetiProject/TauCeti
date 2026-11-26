/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Module.FiniteDual
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
Their norm estimates are independent of any choice of generators or basis.
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


namespace WithConv

variable {R C M N : Type*} [CommSemiring R] [NormedField C] [Algebra R C]
  [AddCommMonoid M] [Module R M] [Module.Finite R M]
  [AddCommMonoid N] [Module R N] [Module.Finite R N]

/-- Exterior products of field-valued linear maps have exactly the product sup norm. -/
theorem supNorm_mulTensor (f : WithConv (M →ₗ[R] C)) (g : WithConv (N →ₗ[R] C))
    (hR : ∀ r : R, ‖algebraMap R C r‖ ≤ 1) :
    (mulTensor f g).ofConv.supNorm = f.ofConv.supNorm * g.ofConv.supNorm := by
  have : IsUltrametricDist C :=
    IsUltrametricDist.isUltrametricDist_of_forall_norm_natCast_le_one fun n ↦ by
      simpa using hR (n : R)
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
  have : IsUltrametricDist C :=
    IsUltrametricDist.isUltrametricDist_of_forall_norm_natCast_le_one fun n ↦ by
      simpa using hR (n : R)
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
/-- The convolution unit has sup norm at most one, since its values come from the base ring. -/
theorem supNorm_convOne_le [CoalgebraStruct R M]
    (hR : ∀ r : R, ‖algebraMap R C r‖ ≤ 1) :
    (1 : WithConv (M →ₗ[R] C)).ofConv.supNorm ≤ 1 := by
  rw [LinearMap.supNorm_def]
  exact ciSup_le fun m ↦ hR (Coalgebra.counit m)

/-- The product of the two counit embeddings has exactly the product sup norm. -/
theorem supNorm_tensorCounitRight_mul_tensorCounitLeft [Coalgebra R M] [Coalgebra R N]
    (f : WithConv (M →ₗ[R] C)) (g : WithConv (N →ₗ[R] C))
    (hR : ∀ r : R, ‖algebraMap R C r‖ ≤ 1) :
    (tensorCounitRight R C M N f * tensorCounitLeft R C M N g).ofConv.supNorm =
      f.ofConv.supNorm * g.ofConv.supNorm := by
  rw [tensorCounitRight_mul_tensorCounitLeft, supNorm_mulTensor f g hR]

end WithConv

namespace WithConv

variable {R C A : Type*} [CommSemiring R] [NormedField C] [Algebra R C]
  [Semiring A] [_root_.Bialgebra R A] [Module.Finite R A]

/-- Transposing multiplication does not increase the sup norm. -/
theorem supNorm_convolutionDelta_le (f : WithConv (A →ₗ[R] C))
    (hR : ∀ r : R, ‖algebraMap R C r‖ ≤ 1) :
    (TauCeti.Bialgebra.convolutionDelta R C A f).ofConv.supNorm ≤ f.ofConv.supNorm := by
  have : IsUltrametricDist C :=
    IsUltrametricDist.isUltrametricDist_of_forall_norm_natCast_le_one fun n ↦ by
      simpa using hR (n : R)
  apply (LinearMap.supNorm_le_iff _ hR).mpr
  apply LinearMap.norm_apply_le_of_tmul
  intro a b
  simpa only [TauCeti.Bialgebra.convolutionDelta_apply_tmul] using
    f.ofConv.norm_apply_le_supNorm hR (a * b)

omit [Module.Finite R A] in
/-- On the convolution algebra of a bialgebra the counit has sup norm exactly one. -/
theorem supNorm_convOne_eq_one (hR : ∀ r : R, ‖algebraMap R C r‖ ≤ 1) :
    (1 : WithConv (A →ₗ[R] C)).ofConv.supNorm = 1 := by
  apply le_antisymm (WithConv.supNorm_convOne_le hR)
  have hb : BddAbove (Set.range fun a ↦ ‖(1 : WithConv (A →ₗ[R] C)).ofConv a‖) := by
    refine ⟨1, ?_⟩
    rintro _ ⟨a, rfl⟩
    exact hR (Coalgebra.counit a)
  simpa only [LinearMap.convOne_apply, Bialgebra.counit_one, map_one, norm_one,
    LinearMap.supNorm_def] using
    (le_ciSup hb (1 : A))

end WithConv
