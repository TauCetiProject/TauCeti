/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.RingOpNorm.OpenMapping

import TauCeti.RingTheory.Huber.ClosedSubmodule

/-!
# Bounds on maps from finite Banach modules

Over a complete ultrametric Tate ring, every linear map from a finite complete normed module
with contractive scalar action to a seminormed module with contractive scalar action is bounded.
The target need not be complete or ultrametric. The ring need not be commutative or noetherian,
and the modules need not be free.

The key input is quantitative finite spanning: a finite generating family admits coefficient
lifts bounded linearly in the norm of the vector. The composite of an arbitrary linear map
with that presentation is continuous on the finite free module, hence bounded over Tate scalars.
Combining these bounds gives `LinearMap.exists_bound_of_module_finite`.

Applied in both directions, this proves bounded equivalence of any two Banach module norms
on a finite module, expressed without choosing new norms by
`LinearEquiv.exists_norm_bounds_of_module_finite`. In particular, no prior compatibility of
the two topologies is required. Zero modules and empty generating families are included.

In the other direction, let `R` be a complete commutative topological Tate ring and
let `S` be a Tate seminormed ring acting compatibly on `R` and on the modules, for instance
`S = R` for a Banach-Tate ring, or a complete commutative ultrametric normed algebra `R` over a
nontrivially normed field `S`. An injective `R`-linear map with closed range from a finite
seminormed module into a complete normed module, both with contractive `S`-actions and continuous
`R`-actions, is bounded below (`LinearMap.antilipschitz_of_injective_of_isClosed_range`): its
range is complete and carries the module topology, so the inverse on the range is continuous and
therefore bounded. If `R` is Hausdorff and the target is noetherian, every injective `R`-linear
map into it has closed range and finite source, so it is bounded below
(`LinearMap.antilipschitz_of_injective_of_isNoetherian`).

## References

* C. Johansson and J. Newton, *Extended eigenvarieties for overconvergent cohomology*,
  arXiv:1604.07739, §2.1.
* S. Bosch, U. Güntzer and R. Remmert, *Non-Archimedean Analysis*, §3.7.
-/

public section

namespace LinearMap

variable {R M N : Type*} [SeminormedRing R] [IsUltrametricDist R] [CompleteSpace R]
  [TauCeti.NormedRing.IsTate R]
  [NormedAddCommGroup M] [Module R M] [IsBoundedSMul R M] [CompleteSpace M]
  [Module.Finite R M]
  [SeminormedAddCommGroup N] [Module R N] [IsBoundedSMul R N]

/-- Every linear map from a finite Banach module over a complete ultrametric Tate ring is
bounded. The target is only seminormed and need not be complete or ultrametric. -/
theorem exists_bound_of_module_finite (f : M →ₗ[R] N) :
    ∃ C > 0, ∀ x, ‖f x‖ ≤ C * ‖x‖ := by
  obtain ⟨n, v, hv⟩ := Module.Finite.exists_fin (R := R) (M := M)
  let q := Fintype.linearCombination R v
  obtain ⟨A, hA, hlift⟩ := TauCeti.exists_linearCombination_eq_and_norm_le v hv
  obtain ⟨B, hB, hbound⟩ := TauCeti.NormedRing.IsTate.bound_of_continuous
    (f.comp q) (f.comp q).continuous_on_pi
  refine ⟨B * A, mul_pos hB hA, fun x ↦ ?_⟩
  obtain ⟨c, hc, hcnorm⟩ := hlift x
  have hqc : q c = x := (Fintype.linearCombination_apply R v c).trans hc
  calc
    ‖f x‖ = ‖(f.comp q) c‖ := by rw [LinearMap.comp_apply, hqc]
    _ ≤ B * ‖c‖ := hbound c
    _ ≤ B * (A * ‖x‖) := mul_le_mul_of_nonneg_left hcnorm hB.le
    _ = (B * A) * ‖x‖ := (mul_assoc _ _ _).symm

end LinearMap

namespace LinearEquiv

variable {R M N : Type*} [SeminormedRing R] [IsUltrametricDist R] [CompleteSpace R]
  [TauCeti.NormedRing.IsTate R]
  [NormedAddCommGroup M] [Module R M] [IsBoundedSMul R M] [CompleteSpace M]
  [Module.Finite R M]
  [NormedAddCommGroup N] [Module R N] [IsBoundedSMul R N] [CompleteSpace N]

/-- An algebraic equivalence between finite Banach modules is bounded in both directions.
Taking the identity between two normed copies of the same module proves that their norms
are bounded-equivalent, without assuming their topologies agree. -/
theorem exists_norm_bounds_of_module_finite (e : M ≃ₗ[R] N) :
    ∃ C > 0, ∀ x, ‖e x‖ ≤ C * ‖x‖ ∧ ‖x‖ ≤ C * ‖e x‖ := by
  have : Module.Finite R N := Module.Finite.of_surjective e.toLinearMap e.surjective
  obtain ⟨A, hA, hforward⟩ := e.toLinearMap.exists_bound_of_module_finite
  obtain ⟨B, _, hbackward⟩ := e.symm.toLinearMap.exists_bound_of_module_finite
  refine ⟨max A B, lt_max_of_lt_left hA, fun x ↦ ⟨?_, ?_⟩⟩
  · exact (hforward x).trans (mul_le_mul_of_nonneg_right (le_max_left A B) (norm_nonneg x))
  · have hx : ‖x‖ ≤ B * ‖e x‖ := by simpa using hbackward (e x)
    exact hx.trans (mul_le_mul_of_nonneg_right (le_max_right A B) (norm_nonneg (e x)))

end LinearEquiv

namespace LinearMap

variable (S : Type*) {R M N : Type*} [SeminormedRing S] [TauCeti.NormedRing.IsTate S]
  [CommRing R] [UniformSpace R] [IsUniformAddGroup R] [CompleteSpace R]
  [IsTopologicalRing R] [TauCeti.Huber.IsTateRing R] [SMul S R]
  [SeminormedAddCommGroup M] [Module S M] [IsBoundedSMul S M] [Module R M]
  [IsScalarTower S R M] [ContinuousSMul R M]
  [NormedAddCommGroup N] [Module S N] [IsBoundedSMul S N] [CompleteSpace N] [Module R N]
  [IsScalarTower S R N] [ContinuousSMul R N]

include S in
/-- **Injective linear maps with closed range are bounded below.** Let `R` be a complete
commutative topological Tate ring, and let `S` be a seminormed ring with a multiplicative
pseudo-uniformiser acting on `R`. Let `M` be a finite seminormed module and `N` a complete normed
module, both with contractive `S`-actions and with continuous `R`-actions compatible with `S`.
Every injective `R`-linear map `f : M → N` with closed range is antilipschitz, so
`‖x‖ ≤ C ‖f x‖` for some `C`. Unlike
`ContinuousLinearMap.antilipschitz_of_injective_of_isClosed_range_of_isTate`, `f` need not be
continuous and `M` need not be complete: finiteness of `M` replaces both. -/
theorem antilipschitz_of_injective_of_isClosed_range [Module.Finite R M] (f : M →ₗ[R] N)
    (hf : Function.Injective f) (hclosed : IsClosed (Set.range f)) :
    ∃ C, AntilipschitzWith C f := by
  -- The range of `f` is closed in `N`, hence complete, and it is finite over `R`.
  have : CompleteSpace (range f) := by
    rw [← LinearMap.coe_range] at hclosed
    exact hclosed.completeSpace_coe
  have := TauCeti.Huber.IsTateRing.isModuleTopology (A := R) (M := range f)
  have : IsBoundedSMul S (range f) := .of_norm_smul_le fun s x ↦ norm_smul_le s (x : N)
  -- So the inverse of `f` on its range is continuous, hence bounded.
  let g := (LinearEquiv.ofInjective f hf).symm.toLinearMap
  obtain ⟨C, hC0, hC⟩ := TauCeti.NormedRing.IsTate.bound_of_continuous (g.restrictScalars S)
    (IsModuleTopology.continuous_of_linearMap g)
  refine ⟨C.toNNReal, AddMonoidHomClass.antilipschitz_of_bound f fun x ↦ ?_⟩
  simpa [g, Real.coe_toNNReal _ hC0.le] using hC (LinearEquiv.ofInjective f hf x)

include S in
/-- **Injective linear maps into noetherian modules are bounded below.** Let `R` be a complete
Hausdorff commutative topological Tate ring, and let `S` be a seminormed ring with a
multiplicative pseudo-uniformiser acting on `R`. Let `M` be a seminormed module and `N` a complete
normed module, both with contractive `S`-actions and with continuous `R`-actions compatible with
`S`, and let `N` be noetherian over `R`. Every injective `R`-linear map `f : M → N` is
antilipschitz, so `‖x‖ ≤ C ‖f x‖` for some `C`. Taking `S = R` covers a Banach-Tate ring `R`;
taking `S` a nontrivially normed field covers complete commutative ultrametric normed algebras
over it. -/
theorem antilipschitz_of_injective_of_isNoetherian [T2Space R] [IsNoetherian R N]
    (f : M →ₗ[R] N) (hf : Function.Injective f) : ∃ C, AntilipschitzWith C f := by
  -- `M` is isomorphic to the range of `f`, which is finite and closed in the noetherian `N`.
  have : Module.Finite R M := Module.Finite.equiv (LinearEquiv.ofInjective f hf).symm
  exact antilipschitz_of_injective_of_isClosed_range S f hf <|
    f.coe_range ▸ TauCeti.Huber.isClosed_of_isNoetherian (range f)

end LinearMap
