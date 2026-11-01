/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.LaurentSeries.Lattice
public import TauCeti.RingTheory.HahnSeries.TensorProduct
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.Topology.Algebra.IsUniformGroup.Basic
public import Mathlib.Topology.UniformSpace.Pi
public import Mathlib.Topology.Algebra.Module.ModuleTopology
public import Mathlib.Topology.Algebra.Module.Equiv.Basic

/-!
# Finite-dimensional Laurent modules and their topology

A finite basis of `V` identifies `V((t))` with a finite product of copies of `K((t))`.
This identification is a homeomorphism for the lattice topology: membership in `U_a(V)`
is equivalent to membership of every scalar coordinate in `U_a(K)`. Thus the lattice topology
agrees with the module topology over the Laurent field, independently of the chosen basis,
and the resulting uniform additive group is complete.

The algebraic comparison uses `HahnModule.tensorProductToHahnModule` and Mathlib's
`Module.Basis.baseChange`, rather than a new scalar-extension construction.
-/

public section

noncomputable section

open HahnSeries HahnModule Filter Topology
open scoped LaurentSeries

namespace Module.Basis

variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V] [Finite ι]

/-- Use the coefficientwise action in the tensor product, as in the Hahn-module comparison.
The default Laurent algebra has a propositionally equal action. -/
private local instance instCoefficientAlgebra : Algebra K K⸨X⸩ := HahnSeries.instAlgebra

/-- Scalar coordinate series in a finite basis of the coefficient space. -/
def laurentSeriesEquiv (b : Basis ι K V) : HahnModule ℤ K V ≃ₗ[K⸨X⸩] (ι → K⸨X⸩) :=
  (LinearEquiv.ofBijective (tensorProductToHahnModule ℤ K V)
    (tensorProductToHahnModule_bijective_of_basis b)).symm ≪≫ₗ (b.baseChange K⸨X⸩).equivFun

/-- The coefficient of a scalar coordinate series is the corresponding coordinate of the
vector coefficient. -/
@[simp]
theorem coeff_laurentSeriesEquiv (b : Basis ι K V) (x : HahnModule ℤ K V) (i : ι) (n : ℤ) :
    (b.laurentSeriesEquiv x i).coeff n = b.repr (((of K).symm x).coeff n) i := by
  obtain ⟨z, rfl⟩ := (tensorProductToHahnModule_bijective_of_basis b).surjective x
  have hz : b.laurentSeriesEquiv (tensorProductToHahnModule ℤ K V z) =
      (b.baseChange K⸨X⸩).equivFun z :=
    congrArg (b.baseChange K⸨X⸩).equivFun (LinearEquiv.symm_apply_apply _ z)
  rw [hz]
  clear hz
  induction z using TensorProduct.inductionOn with
  | tmul f v => simp [Basis.equivFun_apply, mul_comm]
  | add z w hz hw => simp_all [Basis.equivFun_apply]

/-- In a finite coefficient basis, the lattice condition is a condition on every scalar
coordinate series, with the same lower bound. -/
theorem mem_lattice_iff_laurentSeriesEquiv (b : Basis ι K V) (x : HahnModule ℤ K V) (a : ℤ) :
    x ∈ TauCeti.HahnModule.lattice K V a ↔
      ∀ i, b.laurentSeriesEquiv x i ∈ TauCeti.LaurentSeries.lattice K K a := by
  simp only [TauCeti.HahnModule.mem_lattice_iff, TauCeti.LaurentSeries.mem_lattice_iff,
    coeff_laurentSeriesEquiv]
  constructor
  · intro h i n hn
    simp [h n hn]
  · intro h n hn
    exact b.repr.injective (Finsupp.ext fun i ↦ by simpa using h i n hn)

/-- Every scalar coordinate projection is continuous for the lattice topology. -/
theorem continuous_laurentSeriesEquiv_apply (b : Basis ι K V) (i : ι) :
    Continuous (fun x : HahnModule ℤ K V ↦ b.laurentSeriesEquiv x i) := by
  let f := (LinearMap.proj i).comp b.laurentSeriesEquiv.toLinearMap
  apply continuous_of_continuousAt_zero f.toAddMonoidHom
  rw [ContinuousAt, map_zero]
  apply (TauCeti.LaurentSeries.hasBasis_nhds_zero_lattice).tendsto_right_iff.mpr
  intro a _
  filter_upwards [TauCeti.HahnModule.lattice_mem_nhds_zero K V a] with x hx
  exact (b.mem_lattice_iff_laurentSeriesEquiv x a).mp hx i

/-- Scalar coordinate series identify the lattice topology with the finite product valuation
topology. This holds for every finite basis, so the comparison is independent of basis choice. -/
def laurentSeriesContinuousLinearEquiv (b : Basis ι K V) :
    HahnModule ℤ K V ≃L[K⸨X⸩] (ι → K⸨X⸩) where
  __ := b.laurentSeriesEquiv
  continuous_toFun := continuous_pi b.continuous_laurentSeriesEquiv_apply
  continuous_invFun := by
    apply continuous_of_continuousAt_zero b.laurentSeriesEquiv.symm.toAddMonoidHom
    rw [ContinuousAt, map_zero]
    apply (TauCeti.HahnModule.hasBasis_nhds_zero_lattice K V).tendsto_right_iff.mpr
    intro a _
    have h (i : ι) : ∀ᶠ y : ι → K⸨X⸩ in 𝓝 0,
        y i ∈ TauCeti.LaurentSeries.lattice K K a :=
      (continuous_apply i).continuousAt.preimage_mem_nhds
        ((TauCeti.LaurentSeries.hasBasis_nhds_zero_lattice).mem_of_mem trivial)
    filter_upwards [eventually_all.mpr h] with y hy
    exact (b.mem_lattice_iff_laurentSeriesEquiv _ a).mpr (by simpa using hy)

/-- The topological comparison has the scalar coordinate map as its underlying function. -/
theorem laurentSeriesContinuousLinearEquiv_apply (b : Basis ι K V) (x : HahnModule ℤ K V) :
    b.laurentSeriesContinuousLinearEquiv x = b.laurentSeriesEquiv x := (rfl)

/-- The scalar coordinate homeomorphism reads the coordinates of each vector coefficient. -/
@[simp]
theorem coeff_laurentSeriesContinuousLinearEquiv (b : Basis ι K V) (x : HahnModule ℤ K V)
    (i : ι) (n : ℤ) :
    (b.laurentSeriesContinuousLinearEquiv x i).coeff n =
      b.repr (((of K).symm x).coeff n) i :=
  b.coeff_laurentSeriesEquiv x i n

end Module.Basis

namespace TauCeti.HahnModule

variable (R V : Type*) [Ring R] [AddCommGroup V] [Module R V]

/-- The additive uniformity associated to the lattice topology. -/
instance instUniformSpace : UniformSpace (HahnModule ℤ R V) :=
  IsTopologicalAddGroup.rightUniformSpace _

/-- The lattice uniformity makes module-valued Laurent series a uniform additive group. -/
instance instIsUniformAddGroup : IsUniformAddGroup (HahnModule ℤ R V) :=
  isUniformAddGroup_of_addCommGroup

end TauCeti.HahnModule

namespace Module.Basis

variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V] [Finite ι]

/-- Module-valued Laurent series are complete whenever the coefficient space has a finite
basis. No topology on the coefficient field or coefficient space is used. -/
theorem completeSpace_laurentSeries (b : Basis ι K V) : CompleteSpace (HahnModule ℤ K V) := by
  let e := b.laurentSeriesContinuousLinearEquiv
  let u : HahnModule ℤ K V ≃ᵤ (ι → K⸨X⸩) :=
    { e.toEquiv with
      uniformContinuous_toFun :=
        uniformContinuous_addMonoidHom_of_continuous (f := e.toAddMonoidHom) e.continuous
      uniformContinuous_invFun :=
        uniformContinuous_addMonoidHom_of_continuous (f := e.symm.toAddMonoidHom)
          e.symm.continuous }
  exact u.completeSpace_iff.mpr inferInstance

end Module.Basis

namespace TauCeti.HahnModule

variable (K V : Type*) [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- For finite-dimensional coefficients, the lattice topology is the module topology over the
valued Laurent field. In particular this topology does not depend on a coefficient basis. -/
instance instIsModuleTopology : IsModuleTopology K⸨X⸩ (HahnModule ℤ K V) :=
  IsModuleTopology.iso (Module.Free.chooseBasis K V).laurentSeriesContinuousLinearEquiv.symm

/-- Finite-dimensional module-valued Laurent series are complete for the lattice uniformity. -/
instance instCompleteSpace : CompleteSpace (HahnModule ℤ K V) :=
  (Module.Free.chooseBasis K V).completeSpace_laurentSeries

end TauCeti.HahnModule
