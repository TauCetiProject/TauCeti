/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Node.Basic
public import TauCeti.Topology.PureDimension
public import Mathlib.RingTheory.AdjoinRoot
import TauCeti.RingTheory.KrullDimension.Quotient
import TauCeti.RingTheory.Ideal.GoingDown
import TauCeti.RingTheory.KrullDimension.Integral
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import TauCeti.RingTheory.Flat.NonZeroDivisors
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.KrullDimension.Field

/-!
# The nodal equation is free over the sum of its coordinates

Put `s = x + y` on the curve `xy = a`. The coordinate `x` is then a root of the monic quadratic
`T² - sT + a` over `R[s]`, and `y = s - x`. Conversely, adjoining a root `t` of this quadratic to
`R[s]` gives a solution `x = t`, `y = s - t` of the nodal equation. So the node algebra
`NodeAlgebra R a = R[x, y] ⧸ (xy - a)` is `R[s]` with a root of a monic quadratic adjoined: it is
free of rank two over the polynomial ring `R[s]`, with basis `1, x` (`AdjoinRoot.powerBasis'`).

This finite free presentation controls the local model of a node over any base ring `R`:

* it is a free, hence flat, `R`-module, and faithfully flat when `R` is nontrivial;
* it is integral over `R[s]`, which it contains, so it has the Krull dimension of `R[s]`;
* over a field it is pure of dimension one: since it is flat over `R[s]`, going down holds, so
  every minimal prime lies over the zero ideal of `R[s]`, and each irreducible component is
  integral over the line `Spec R[s]`, which it dominates.

Flatness over the base and pure one-dimensionality of the fibres are the fibrewise conditions,
beside finite presentation, in the characterization of families of curves with at worst nodal
singularities; the fibres of `NodeAlgebra R a` over `R` are node algebras over the residue
fields by `TauCeti.NodeAlgebra.baseChange`.

## Main definitions

* `TauCeti.NodeAlgebra.quadratic a`: the monic quadratic `T² - sT + a` over `R[s]`.
* `TauCeti.NodeAlgebra.adjoinRootEquiv a`: the node algebra is `R[s]` with a root of
  `quadratic a` adjoined, with `x` corresponding to the root and `x + y` to `s`.

## Main results

* `TauCeti.NodeAlgebra.instFree`: the node algebra is a free `R`-module.
* `TauCeti.NodeAlgebra.coord_mem_nonZeroDivisors`: if `a` is a nonzerodivisor of `R`, then, the
  node algebra being flat, both coordinates are nonzerodivisors.
* `TauCeti.NodeAlgebra.ringKrullDim_eq_ringKrullDim_polynomial`: its Krull dimension is that of
  `R[s]`.
* `TauCeti.NodeAlgebra.ringKrullDim_eq_ringKrullDim_add_one`: over a Noetherian ring `R` it has
  Krull dimension `dim R + 1`.
* `TauCeti.NodeAlgebra.isPureDimensional_primeSpectrum`: over a field its spectrum is pure of
  dimension one.

## References

* [Stacks Project, Example 55.14.1, Tag 0CDC](https://stacks.math.columbia.edu/tag/0CDC), the
  local model `xy = πⁿ` of a node over a discrete valuation ring.
-/

public section

noncomputable section

namespace TauCeti

namespace NodeAlgebra

open Polynomial

variable {R : Type*} [CommRing R] (a : R)

/-- The monic quadratic `T² - sT + a` over the polynomial ring `R[s]`. On the node `xy = a` it
has the root `x` when `s = x + y`. -/
def quadratic : R[X][X] :=
  X ^ 2 - C X * X + C (C a)

/-- The defining formula of `quadratic a`. -/
theorem quadratic_def : quadratic a = X ^ 2 - C X * X + C (C a) := (rfl)

/-- The quadratic `T² - sT + a` is monic. -/
theorem monic_quadratic : (quadratic a).Monic := by
  rw [quadratic_def]
  monicity!

/-- Over a nontrivial ring, `quadratic a` has degree two. -/
theorem natDegree_quadratic [Nontrivial R] : (quadratic a).natDegree = 2 := by
  rw [quadratic_def]
  compute_degree!

/-- The coordinate `x` is a root of `quadratic a` over `R[s]` with `s ↦ x + y`. -/
private theorem eval₂_quadratic_coord :
    (quadratic a).eval₂
      ((aeval (coord a 0 + coord a 1) : R[X] →ₐ[R] NodeAlgebra R a) : R[X] →+* NodeAlgebra R a)
      (coord a 0) = 0 := by
  simp only [quadratic_def, eval₂_add, eval₂_sub, eval₂_mul, eval₂_X_pow, eval₂_X, eval₂_C,
    RingHom.coe_coe, aeval_X, aeval_C, ← coord_zero_mul_coord_one]
  ring

/-- The root of `quadratic a` and its conjugate `s - root` satisfy the nodal equation. -/
private theorem root_mul_sub_root :
    AdjoinRoot.root (quadratic a) * (AdjoinRoot.of (quadratic a) X - AdjoinRoot.root _) =
      algebraMap R (AdjoinRoot (quadratic a)) a := by
  have h : AdjoinRoot.mk (quadratic a) (X ^ 2 - C X * X + C (C a)) = 0 := by
    rw [← quadratic_def]
    exact AdjoinRoot.mk_self
  simp only [map_add, map_sub, map_mul, map_pow, AdjoinRoot.mk_X, AdjoinRoot.mk_C] at h
  rw [AdjoinRoot.algebraMap_eq', RingHom.comp_apply, Polynomial.algebraMap_eq]
  linear_combination -h

/-- The node algebra is the polynomial ring `R[s]` with a root of the monic quadratic
`T² - sT + a` adjoined: the root corresponds to `x`, and `s` to `x + y`. -/
def adjoinRootEquiv : AdjoinRoot (quadratic a) ≃ₐ[R] NodeAlgebra R a :=
  AlgEquiv.ofAlgHom
    (AdjoinRoot.liftAlgHom (quadratic a) (aeval (coord a 0 + coord a 1)) (coord a 0)
      (eval₂_quadratic_coord a))
    (lift a (AdjoinRoot.root _) (AdjoinRoot.of _ X - AdjoinRoot.root _) (root_mul_sub_root a))
    (by ext <;> simp)
    (by ext <;> simp)

@[simp]
theorem adjoinRootEquiv_root :
    adjoinRootEquiv a (AdjoinRoot.root (quadratic a)) = coord a 0 := by
  simp [adjoinRootEquiv]

@[simp]
theorem adjoinRootEquiv_of (p : R[X]) :
    adjoinRootEquiv a (AdjoinRoot.of (quadratic a) p) = aeval (coord a 0 + coord a 1) p := by
  simp [adjoinRootEquiv]

@[simp]
theorem adjoinRootEquiv_symm_coord_zero :
    (adjoinRootEquiv a).symm (coord a 0) = AdjoinRoot.root (quadratic a) := by
  simp [adjoinRootEquiv]

@[simp]
theorem adjoinRootEquiv_symm_coord_one :
    (adjoinRootEquiv a).symm (coord a 1) =
      AdjoinRoot.of (quadratic a) X - AdjoinRoot.root (quadratic a) := by
  simp [adjoinRootEquiv]

/-- The node algebra is a free `R`-module, being free of rank two over the free `R`-module
`R[s]`. In particular it is flat, and faithfully flat. -/
instance instFree : Module.Free R (NodeAlgebra R a) :=
  have := (monic_quadratic a).free_adjoinRoot
  have : Module.Free R (AdjoinRoot (quadratic a)) := .trans (S := R[X])
  .of_equiv (adjoinRootEquiv a).toLinearEquiv

/-- Over a nontrivial ring, `R[s]` with a root of `quadratic a` adjoined is nontrivial. -/
private theorem nontrivial_adjoinRoot [Nontrivial R] : Nontrivial (AdjoinRoot (quadratic a)) :=
  (AdjoinRoot.nontrivial_iff_of_monic (monic_quadratic a)).2 <| by
    rw [← natDegree_pos_iff_degree_pos, natDegree_quadratic]
    exact two_pos

/-- Over a nontrivial ring the node algebra is nontrivial; being free, it is then a faithfully
flat `R`-algebra. -/
instance [Nontrivial R] : Nontrivial (NodeAlgebra R a) :=
  have := nontrivial_adjoinRoot a
  (adjoinRootEquiv a).injective.nontrivial

variable {a} in
/-- If `a` is a nonzerodivisor of `R`, then both coordinates are nonzerodivisors of the node
algebra of `xy = a`. -/
theorem coord_mem_nonZeroDivisors (ha : a ∈ nonZeroDivisors R) (i : Fin 2) :
    coord a i ∈ nonZeroDivisors (NodeAlgebra R a) := by
  -- If `xz = 0`, then `az = y · xz = 0`, and `a` is a nonzerodivisor of the flat algebra.
  have key : ∀ z, coord a i * z = 0 → z = 0 := fun z hz ↦
    (Module.Flat.algebraMap_mem_nonZeroDivisors ha).1 z
      (by rw [← coord_mul_coord_one_sub, mul_right_comm, hz, zero_mul])
  exact mem_nonZeroDivisors_iff_left.mpr key

/-- The node algebra has the Krull dimension of the polynomial ring `R[s]`, over which it is
integral and which it contains. -/
theorem ringKrullDim_eq_ringKrullDim_polynomial :
    ringKrullDim (NodeAlgebra R a) = ringKrullDim R[X] := by
  cases subsingleton_or_nontrivial R
  · have := Module.subsingleton R (NodeAlgebra R a)
    rw [ringKrullDim_eq_bot_of_subsingleton, ringKrullDim_eq_bot_of_subsingleton]
  have := (monic_quadratic a).free_adjoinRoot
  have := (monic_quadratic a).finite_adjoinRoot
  have := nontrivial_adjoinRoot a
  rw [← ringKrullDim_eq_of_ringEquiv (adjoinRootEquiv a).toRingEquiv]
  exact ringKrullDim_eq_of_isIntegral_of_faithfulSMul

/-- Over a Noetherian ring `R`, the node algebra has Krull dimension `dim R + 1`. -/
theorem ringKrullDim_eq_ringKrullDim_add_one [IsNoetherianRing R] :
    ringKrullDim (NodeAlgebra R a) = ringKrullDim R + 1 := by
  rw [ringKrullDim_eq_ringKrullDim_polynomial, Polynomial.ringKrullDim_of_isNoetherianRing]

section Field

variable {k : Type*} [Field k] (c : k)

/-- Over a field, the node algebra has Krull dimension one. -/
theorem ringKrullDim_eq_one : ringKrullDim (NodeAlgebra k c) = 1 := by
  rw [ringKrullDim_eq_ringKrullDim_add_one, ringKrullDim_eq_zero_of_field, zero_add]

/-- Over a field, every irreducible component of the node `xy = c` is a curve: the spectrum of
the node algebra is pure of dimension one. -/
theorem isPureDimensional_primeSpectrum :
    IsPureDimensional 1 (PrimeSpectrum (NodeAlgebra k c)) := by
  have := (monic_quadratic c).free_adjoinRoot
  have := (monic_quadratic c).finite_adjoinRoot
  refine IsPureDimensional.homeomorph ?_
    (PrimeSpectrum.homeomorphOfRingEquiv (adjoinRootEquiv c).toRingEquiv)
  rw [isPureDimensional_primeSpectrum_iff]
  intro P hP
  have : P.IsPrime := hP.1.1
  -- The minimal prime `P` lies over the unique minimal prime `⊥` of `k[s]`, by going down.
  have hunder : P.under k[X] = ⊥ := by
    have := Ideal.under_mem_minimalPrimes (R := k[X]) hP
    rwa [IsDomain.minimalPrimes_eq_singleton_bot] at this
  have : FaithfulSMul k[X] (AdjoinRoot (quadratic c) ⧸ P) := by
    rw [faithfulSMul_iff_algebraMap_injective, injective_iff_map_eq_zero]
    intro p hp
    rwa [IsScalarTower.algebraMap_apply k[X] (AdjoinRoot (quadratic c)),
      Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem, ← Ideal.mem_comap,
      ← Ideal.under_def, hunder] at hp
  rw [ringKrullDim_eq_of_isIntegral_of_faithfulSMul (R := k[X]),
    Polynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field, zero_add]
  rfl

end Field

end NodeAlgebra

end TauCeti
