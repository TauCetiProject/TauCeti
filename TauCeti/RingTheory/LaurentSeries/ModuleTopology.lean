/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.LaurentSeries.Lattice
public import TauCeti.RingTheory.HahnSeries.TensorProduct
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.Topology.Algebra.Module.ModuleTopology

/-!
# Finite-dimensional Laurent modules and their topology

A finite basis of `V` identifies `V((t))` with a finite product of copies of `K((t))`.
This identification is a homeomorphism for the lattice topology: membership in `U_a(V)`
is equivalent to membership of every scalar coordinate in `U_a(K)`. Thus the lattice topology
agrees with the module topology over the Laurent field, independently of the chosen basis,
and the resulting uniform additive group is complete.

The algebraic comparison uses `HahnModule.tensorProductEquiv` and Mathlib's
`Module.Basis.baseChange`. These results make `V((t))` a complete topological module over
`K((t))` for use in continuous residue duality.
-/

public section

noncomputable section

open HahnSeries HahnModule Filter Topology
open scoped LaurentSeries TensorProduct

namespace Module.Basis

-- Use the coefficientwise action in the tensor product, as in the Hahn-module comparison.
-- The default Laurent algebra has a propositionally equal action.
attribute [local instance 2000] HahnSeries.instAlgebra

section Algebra

variable {R V ι : Type*} [CommSemiring R] [AddCommMonoid V] [Module R V] [Finite ι]

/-- Scalar coordinate series in a finite basis of the coefficient space. -/
def laurentSeriesEquiv (b : Basis ι R V) : HahnModule ℤ R V ≃ₗ[R⸨X⸩] (ι → R⸨X⸩) := by
  haveI := Module.Free.of_basis b
  haveI := Module.Finite.of_basis b
  exact (tensorProductEquiv ℤ R V).symm ≪≫ₗ (b.baseChange R⸨X⸩).equivFun

/-- The coordinate comparison agrees with base change on scalar-extended vectors. -/
@[simp]
theorem laurentSeriesEquiv_tensorProductToHahnModule (b : Basis ι R V)
    (z : HahnSeries ℤ R ⊗[R] V) :
    b.laurentSeriesEquiv (tensorProductToHahnModule ℤ R V z) =
      (b.baseChange R⸨X⸩).equivFun z := by
  have := Module.Free.of_basis b
  have := Module.Finite.of_basis b
  simp [laurentSeriesEquiv, ← tensorProductEquiv_apply]

/-- The coefficient of a scalar coordinate series is the corresponding coordinate of the
vector coefficient. -/
@[simp]
theorem coeff_laurentSeriesEquiv (b : Basis ι R V) (x : HahnModule ℤ R V) (i : ι) (n : ℤ) :
    (b.laurentSeriesEquiv x i).coeff n = b.repr (((of R).symm x).coeff n) i := by
  have := Module.Free.of_basis b
  have := Module.Finite.of_basis b
  obtain ⟨z, rfl⟩ := (tensorProductEquiv ℤ R V).surjective x
  rw [tensorProductEquiv_apply, laurentSeriesEquiv_tensorProductToHahnModule]
  induction z using TensorProduct.inductionOn with
  | tmul f v => simp [Basis.equivFun_apply, mul_comm]
  | add z w hz hw => simp_all [Basis.equivFun_apply]

/-- The inverse comparison reconstructs each vector coefficient from its coordinates. -/
@[simp]
theorem repr_coeff_laurentSeriesEquiv_symm (b : Basis ι R V) (y : ι → R⸨X⸩)
    (i : ι) (n : ℤ) :
    b.repr (((of R).symm (b.laurentSeriesEquiv.symm y)).coeff n) i = (y i).coeff n := by
  rw [← coeff_laurentSeriesEquiv, LinearEquiv.apply_symm_apply]

/-- In a finite coefficient basis, the lattice condition is a condition on every scalar
coordinate series, with the same lower bound. -/
theorem mem_lattice_iff_laurentSeriesEquiv (b : Basis ι R V) (x : HahnModule ℤ R V) (a : ℤ) :
    x ∈ TauCeti.HahnModule.lattice R V a ↔
      ∀ i, b.laurentSeriesEquiv x i ∈ TauCeti.LaurentSeries.lattice R R a := by
  simp only [TauCeti.HahnModule.mem_lattice_iff, TauCeti.LaurentSeries.mem_lattice_iff,
    coeff_laurentSeriesEquiv]
  simp_rw [← b.forall_coord_eq_zero_iff, Basis.coord_apply]
  exact ⟨fun h i n hn ↦ h n hn i, fun h n hn i ↦ h i n hn⟩

end Algebra

variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V] [Finite ι]

/-- Scalar coordinate series identify the lattice topology with the finite product valuation
topology. Such an equivalence exists for every finite basis; the equivalence itself depends
on the basis. -/
def laurentSeriesContinuousLinearEquiv (b : Basis ι K V) :
    HahnModule ℤ K V ≃L[K⸨X⸩] (ι → K⸨X⸩) where
  __ := b.laurentSeriesEquiv
  continuous_toFun := by
    apply continuous_of_continuousAt_zero b.laurentSeriesEquiv
    rw [ContinuousAt, map_zero]
    apply tendsto_pi_nhds.mpr
    intro i
    apply (TauCeti.LaurentSeries.hasBasis_nhds_zero_lattice).tendsto_right_iff.mpr
    intro a _
    filter_upwards [TauCeti.HahnModule.lattice_mem_nhds_zero K V a] with x hx
    exact (b.mem_lattice_iff_laurentSeriesEquiv x a).mp hx i
  continuous_invFun := by
    apply continuous_of_continuousAt_zero b.laurentSeriesEquiv.symm
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

/-- The inverse topological comparison has the inverse coordinate map as its function. -/
theorem laurentSeriesContinuousLinearEquiv_symm_apply (b : Basis ι K V) (y : ι → K⸨X⸩) :
    b.laurentSeriesContinuousLinearEquiv.symm y = b.laurentSeriesEquiv.symm y := (rfl)

/-- The inverse coordinate homeomorphism reconstructs each vector coefficient. -/
@[simp]
theorem repr_coeff_laurentSeriesContinuousLinearEquiv_symm (b : Basis ι K V) (y : ι → K⸨X⸩)
    (i : ι) (n : ℤ) :
    b.repr (((of K).symm (b.laurentSeriesContinuousLinearEquiv.symm y)).coeff n) i =
      (y i).coeff n := by
  rw [laurentSeriesContinuousLinearEquiv_symm_apply, repr_coeff_laurentSeriesEquiv_symm]

end Module.Basis

namespace TauCeti.HahnModule

variable (K V : Type*) [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- For finite-dimensional coefficients, the lattice topology is the module topology over the
valued Laurent field. In particular this topology does not depend on a coefficient basis. -/
instance instIsModuleTopology : IsModuleTopology K⸨X⸩ (HahnModule ℤ K V) :=
  IsModuleTopology.iso (Module.Free.chooseBasis K V).laurentSeriesContinuousLinearEquiv.symm

end TauCeti.HahnModule
