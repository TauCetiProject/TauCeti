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

For a finitely generated module with its module topology over a ring with continuous addition
and multiplication, a family of linear maps acts jointly continuously exactly when evaluation at
each fixed vector is continuous. It suffices to check this on a finite generating family: the
linear-combination map from a finite power of the coefficient ring is an open quotient map, and
its product with any parameter space remains so. For these two criteria the target needs only
continuous addition and scalar multiplication, not the module topology.

Over a commutative topological semiring, for finite free source and target with their module
topologies, joint continuity is equivalent to continuity of every matrix entry in finite bases.
-/

public section

namespace TauCeti.ModuleTopology

/-- Test joint continuity on a finite family whose linear-combination map is an open quotient. -/
private theorem continuous_uncurry_iff_apply_of_isOpenQuotientMap
    {X R M N ι : Type*} [TopologicalSpace X] [Semiring R] [TopologicalSpace R]
    [AddCommMonoid M] [Module R M] [TopologicalSpace M]
    [AddCommMonoid N] [Module R N] [TopologicalSpace N] [ContinuousAdd N] [ContinuousSMul R N]
    [Fintype ι] (f : X → M →ₗ[R] N) (v : ι → M)
    (hq : IsOpenQuotientMap (Fintype.linearCombination R v)) :
    Continuous (fun p : X × M => f p.1 p.2) ↔ ∀ i, Continuous (fun x => f x (v i)) := by
  constructor
  · intro h i
    exact h.comp (continuous_id.prodMk continuous_const)
  · intro h
    refine ((IsOpenQuotientMap.id.prodMap hq).continuous_comp_iff).mp ?_
    have hsum : Continuous (fun p : X × (ι → R) => ∑ i, p.2 i • f p.1 (v i)) :=
      continuous_finsetSum _ fun i _ =>
        (continuous_apply i |>.comp continuous_snd).smul ((h i).comp continuous_fst)
    change Continuous (fun p : X × (ι → R) => f p.1 (Fintype.linearCombination R v p.2))
    simpa only [Fintype.linearCombination_apply, map_sum, map_smul] using hsum

section Generators

variable {X R M N : Type*} [TopologicalSpace X] [Ring R] [TopologicalSpace R]
  [IsTopologicalSemiring R] [AddCommGroup M] [Module R M] [TopologicalSpace M]
  [IsModuleTopology R M] [AddCommMonoid N] [Module R N] [TopologicalSpace N]
  [ContinuousAdd N] [ContinuousSMul R N]

/-- Joint continuity of a family of linear maps can be checked on any finite generating family
of the source, equipped with its module topology. -/
theorem continuous_uncurry_iff_apply_of_span_eq_top (f : X → M →ₗ[R] N)
    {ι : Type*} [Finite ι] (v : ι → M) (hv : Submodule.span R (Set.range v) = ⊤) :
    Continuous (fun p : X × M => f p.1 p.2) ↔ ∀ i, Continuous (fun x => f x (v i)) := by
  let := Fintype.ofFinite ι
  exact continuous_uncurry_iff_apply_of_isOpenQuotientMap f v
    (IsModuleTopology.isOpenQuotientMap_of_surjective
      (LinearMap.range_eq_top.mp (by rw [Fintype.range_linearCombination, hv])))

/-- On a finite module with its module topology, pointwise continuity of a linear family is
equivalent to joint continuity of evaluation. -/
theorem continuous_uncurry_iff_apply [Module.Finite R M] (f : X → M →ₗ[R] N) :
    Continuous (fun p : X × M => f p.1 p.2) ↔ ∀ m, Continuous (fun x => f x m) := by
  constructor
  · intro h m
    exact h.comp (continuous_id.prodMk continuous_const)
  · intro h
    obtain ⟨n, v, hv⟩ := Module.Finite.exists_fin (R := R) (M := M)
    exact (continuous_uncurry_iff_apply_of_span_eq_top f v hv).mpr (fun i => h (v i))

end Generators

section Matrix

variable {X R M N ι κ : Type*} [TopologicalSpace X] [CommSemiring R] [TopologicalSpace R]
  [IsTopologicalSemiring R] [AddCommMonoid M] [Module R M] [TopologicalSpace M]
  [IsModuleTopology R M] [AddCommMonoid N] [Module R N] [TopologicalSpace N]
  [IsModuleTopology R N] [Fintype ι] [Finite κ] [DecidableEq ι]

/-- For modules with their module topologies over a commutative topological semiring, a linear
family acts jointly continuously exactly when all its matrix entries in finite bases are
continuous. This includes empty bases. -/
theorem continuous_uncurry_iff_matrix (f : X → M →ₗ[R] N)
    (b : Module.Basis ι R M) (c : Module.Basis κ R N) :
    Continuous (fun p : X × M => f p.1 p.2) ↔
      ∀ i j, Continuous (fun x => LinearMap.toMatrix b c (f x) i j) := by
  have := IsModuleTopology.toContinuousAdd R N
  have hq : IsOpenQuotientMap (Fintype.linearCombination R (b : ι → M)) := by
    have he : (equivFunHomeomorph b).symm = ⇑(Fintype.linearCombination R (b : ι → M)) := by
      funext x
      rw [equivFunHomeomorph_symm_apply, Module.Basis.equivFun_symm_apply,
        Fintype.linearCombination_apply]
    rw [← he]
    exact (equivFunHomeomorph b).symm.isOpenQuotientMap
  rw [continuous_uncurry_iff_apply_of_isOpenQuotientMap f b hq]
  constructor
  · intro h i j
    simpa only [Function.comp_def, LinearMap.toMatrix_apply, Module.Basis.coord_apply] using
      (IsModuleTopology.continuous_of_linearMap (c.coord i)).comp (h j)
  · intro h j
    apply (TauCeti.ModuleTopology.equivFunHomeomorph c).comp_continuous_iff.mp
    exact continuous_pi fun i => by
      simpa [LinearMap.toMatrix_apply, Module.Basis.equivFun_apply] using h i j

end Matrix

end TauCeti.ModuleTopology
