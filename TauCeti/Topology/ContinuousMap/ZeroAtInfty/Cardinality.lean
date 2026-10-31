/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Module.Bases.Orthonormal

/-!
# Cardinality invariance of nonarchimedean model spaces

Over an ultrametric normed ring satisfying the strong rank condition,
a continuous linear map with dense range from `C₀(I, R)` to `C₀(J, R)` implies
`#J ≤ #I`. Consequently continuously linearly equivalent model spaces have
equally many coordinates. The indices may be empty, finite, or infinite and
may lie in different universes. Neither completeness nor a discrete value group
is required.

The coordinate vectors of the target can be approximated within distance one
by images of finite linear combinations of source coordinates. These images
remain orthonormal. Their preimages are therefore linearly independent in the
algebraic coordinate span, where Mathlib's dimension theorem applies.

## References

* J.-P. Serre, *Endomorphismes complètement continus des espaces de Banach p-adiques*,
  Publ. Math. IHÉS 12 (1962), 69–85, §1.
-/

public section

open Set Submodule
open scoped ZeroAtInfty Cardinal

universe u v w

variable {I : Type u} {J : Type v} {R : Type w}
  [TopologicalSpace I] [DiscreteTopology I] [TopologicalSpace J] [DiscreteTopology J]
  [NormedRing R] [IsUltrametricDist R] [StrongRankCondition R]

/-- A continuous linear map with dense range between ultrametric model spaces
cannot increase the cardinality of the coordinate index. -/
theorem ContinuousLinearMap.lift_mk_le_of_denseRange_zeroAtInfty
    (f : C₀(I, R) →L[R] C₀(J, R)) (hf : DenseRange f) :
    Cardinal.lift.{u} #J ≤ Cardinal.lift.{v} #I := by
  classical
  let P := span R (range fun i : I ↦ ZeroAtInftyContinuousMap.single i (1 : R))
  have hdP : DenseRange ((↑) : P → C₀(I, R)) := by
    exact (ZeroAtInftyContinuousMap.dense_span_single_one (R := R) (I := I)).denseRange_val
  have hd : DenseRange (fun x : P ↦ f x) := hf.comp hdP f.continuous
  have happrox (j : J) : ∃ x : P,
      ‖ZeroAtInftyContinuousMap.single j (1 : R) - f x‖ < 1 := by
    obtain ⟨y, ⟨x, rfl⟩, hy⟩ := Metric.mem_closure_iff.1
      (hd (ZeroAtInftyContinuousMap.single j 1)) 1 zero_lt_one
    exact ⟨x, by simpa only [dist_eq_norm] using hy⟩
  choose x hx using happrox
  have ho := (TauCeti.isOrthonormalBasis_single_one (R := R) (I := J)).isOrthonormalFamily
  have hli : LinearIndependent R (fun j ↦ f (x j)) :=
    (ho.of_norm_sub_lt_one hx).linearIndependent
  have hxi : LinearIndependent R x := hli.of_comp (f.toLinearMap.comp P.subtype)
  let b := Module.Basis.span
    (ZeroAtInftyContinuousMap.linearIndependent_single_one (I := I) (R := R))
  have h := linearIndependent_le_basis
    (b.reindex (Equiv.ulift : ULift.{v} I ≃ I).symm)
    (x ∘ (Equiv.ulift : ULift.{u} J ≃ J)) (hxi.comp _ Equiv.ulift.injective)
  simpa only [Cardinal.mk_uLift] using h

/-- Continuously linearly equivalent ultrametric model spaces have coordinate
indices of the same cardinality. -/
theorem ContinuousLinearEquiv.lift_mk_eq_zeroAtInfty
    (e : C₀(I, R) ≃L[R] C₀(J, R)) :
    Cardinal.lift.{v} #I = Cardinal.lift.{u} #J := by
  exact le_antisymm
    ((e.symm : C₀(J, R) →L[R] C₀(I, R)).lift_mk_le_of_denseRange_zeroAtInfty
      e.symm.surjective.denseRange)
    ((e : C₀(I, R) →L[R] C₀(J, R)).lift_mk_le_of_denseRange_zeroAtInfty
      e.surjective.denseRange)
