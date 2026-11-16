/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.ToLin
public import TauCeti.Topology.Algebra.Module.ModuleTopology

/-!
# Joint continuity of families of linear maps

For a finitely generated module with its module topology, a family of linear maps acts jointly
continuously exactly when evaluation at each fixed vector is continuous. It suffices to check
this on a finite generating family: the linear-combination map from a finite power of the
coefficient ring is an open quotient map, and its product with any parameter space remains so.
The target needs only continuous addition and scalar multiplication, not the module topology.

For finite free source and target, joint continuity is equivalently continuity of every matrix
entry in any pair of bases. These criteria apply in particular to actions on finite projective
modules over topological coefficient rings, without a norm or a locally compact parameter space.
-/

public section

namespace LinearMap

section Generators

variable {X R M N : Type*} [TopologicalSpace X] [Ring R] [TopologicalSpace R]
  [IsTopologicalRing R] [AddCommGroup M] [Module R M] [TopologicalSpace M]
  [IsModuleTopology R M] [AddCommMonoid N] [Module R N] [TopologicalSpace N]
  [ContinuousAdd N] [ContinuousSMul R N]

/-- Joint continuity of a family of linear maps can be checked on any finite generating family
of the source, equipped with its module topology. -/
theorem continuous_uncurry_iff_of_span_eq_top (f : X → M →ₗ[R] N)
    {ι : Type*} [Finite ι] (v : ι → M) (hv : Submodule.span R (Set.range v) = ⊤) :
    Continuous (fun p : X × M => f p.1 p.2) ↔ ∀ i, Continuous (fun x => f x (v i)) := by
  let := Fintype.ofFinite ι
  constructor
  · intro h i
    exact h.comp (continuous_id.prodMk continuous_const)
  · intro h
    let q := Fintype.linearCombination R v
    have hq : IsOpenQuotientMap q :=
      IsModuleTopology.isOpenQuotientMap_of_surjective
        (LinearMap.range_eq_top.mp (by rw [Fintype.range_linearCombination, hv]))
    refine ((IsOpenQuotientMap.id.prodMap hq).continuous_comp_iff).mp ?_
    have hsum : Continuous (fun p : X × (ι → R) => ∑ i, p.2 i • f p.1 (v i)) := by
      exact continuous_finsetSum _ fun i _ =>
        (continuous_apply i |>.comp continuous_snd).smul ((h i).comp continuous_fst)
    simpa [Function.comp_def, q, Fintype.linearCombination_apply, map_sum] using hsum

/-- On a finite module with its module topology, pointwise continuity of a linear family is
equivalent to joint continuity of evaluation. -/
theorem continuous_uncurry_iff [Module.Finite R M] (f : X → M →ₗ[R] N) :
    Continuous (fun p : X × M => f p.1 p.2) ↔ ∀ m, Continuous (fun x => f x m) := by
  constructor
  · intro h m
    exact h.comp (continuous_id.prodMk continuous_const)
  · intro h
    obtain ⟨n, v, hv⟩ := Module.Finite.exists_fin (R := R) (M := M)
    exact (continuous_uncurry_iff_of_span_eq_top f v hv).mpr (fun i => h (v i))

end Generators

section Matrix

variable {X R M N ι κ : Type*} [TopologicalSpace X] [CommRing R] [TopologicalSpace R]
  [IsTopologicalRing R] [AddCommGroup M] [Module R M] [TopologicalSpace M]
  [IsModuleTopology R M] [AddCommGroup N] [Module R N] [TopologicalSpace N]
  [IsModuleTopology R N] [Fintype ι] [Finite κ] [DecidableEq ι]

/-- In finite bases, a linear family acts jointly continuously exactly when all its matrix
entries are continuous. This includes empty bases. -/
theorem continuous_uncurry_iff_matrix (f : X → M →ₗ[R] N)
    (b : Module.Basis ι R M) (c : Module.Basis κ R N) :
    Continuous (fun p : X × M => f p.1 p.2) ↔
      ∀ i j, Continuous (fun x => LinearMap.toMatrix b c (f x) i j) := by
  have := IsModuleTopology.toContinuousAdd R N
  rw [continuous_uncurry_iff_of_span_eq_top f b b.span_eq]
  constructor
  · intro h i j
    simpa only [Function.comp_def, LinearMap.toMatrix_apply, Module.Basis.coord_apply] using
      (IsModuleTopology.continuous_of_linearMap (c.coord i)).comp (h j)
  · intro h j
    apply (TauCeti.ModuleTopology.equivFunHomeomorph c).comp_continuous_iff.mp
    exact continuous_pi fun i => by
      simpa [LinearMap.toMatrix_apply, Module.Basis.equivFun_apply] using h i j

end Matrix

end LinearMap
