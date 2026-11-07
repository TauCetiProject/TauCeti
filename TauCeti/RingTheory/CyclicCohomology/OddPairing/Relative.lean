/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.RelativeK1
public import TauCeti.RingTheory.CyclicCohomology.OddPairing.AlgebraicK1
public import TauCeti.RingTheory.CyclicCohomology.Relative.Matrix

/-!
# The odd pairing of a nonunital algebra

Let `A` be a possibly nonunital complex algebra and `A⁺ = Unitization ℂ A` its forced unitization.
The cyclic cohomology of `A` is the relative cyclic cohomology `HCⁿ(A; M)`, the cohomology of the
cyclic cochains on `A⁺` vanishing when all arguments are scalar, and its `K₁` is the relative
`K₁`, the kernel of `K₁(A⁺) → K₁(ℂ)`. This file defines Connes' odd pairing between them: a
relative class `x ∈ K₁(A⁺)` pairs with `c ∈ HC²ᵐ⁺¹(A; M)` through Connes' odd pairing of `K₁(A⁺)`
with the image of `c` in the cyclic cohomology `HC²ᵐ⁺¹(A⁺; M)` of the forced unitization.

For an invertible matrix `u` over `A⁺` with a relative class and a relative cyclic cocycle `φ`,
the pairing is Connes' formula
`(1 + i)⁻¹ 2⁻ⁿ Γ(n/2 + 1)⁻¹ (φ#Tr)(u⁻¹ - 1, u - 1, …, u⁻¹ - 1, u - 1)` with `n = 2m + 1`.

The matrix extension of a relative cyclic cochain vanishes when all its arguments are scalar
matrices, so the classes of scalar matrices pair trivially with relative cyclic cohomology. Since
`K₁(A⁺)` is the product of relative `K₁` and the classes of scalar matrices, the pairing of an
arbitrary class of `A⁺` with a relative cyclic class is the pairing of its relative part: no
information is lost by restricting to relative `K₁`. The pairing is natural for homomorphisms of
nonunital algebras.

## Main definitions

* `TauCeti.relativeAlgebraicK1.oddPairing`: Connes' odd pairing of relative `K₁` with relative
  cyclic cohomology.

## Main results

* `TauCeti.relativeAlgebraicK1.oddPairing_mk_mk`: Connes' formula for the pairing.
* `TauCeti.AlgebraicK1.oddPairing_map_algebraMap_toUnitization_eq_zero`: classes of scalar
  matrices pair trivially with relative cyclic cohomology.
* `TauCeti.relativeAlgebraicK1.oddPairing_projection`: the pairing of a class of `A⁺` with a
  relative cyclic class is the pairing of its relative part.
* `TauCeti.relativeAlgebraicK1.oddPairing_map`: naturality.

## References

* A. Connes, *Noncommutative Geometry*, Chapter III, §3, for the odd pairing, and Chapter III, §1,
  for the cyclic cohomology of nonunital algebras through their unitization.
* J.-L. Loday, *Cyclic Homology*, §1.4 and §8.3.
-/

public section

noncomputable section

namespace TauCeti

open cyclicCohomology

variable {A M : Type*} [NonUnitalRing A] [Module ℂ A] [IsScalarTower ℂ A A] [SMulCommClass ℂ A A]
  [AddCommGroup M] [Module ℂ M]

/-- **Scalar classes pair trivially**: the image in `K₁(A⁺)` of a class of `K₁(ℂ)` pairs to zero
with every relative cyclic cohomology class. -/
@[simp]
theorem AlgebraicK1.oddPairing_map_algebraMap_toUnitization_eq_zero (m : ℕ) (y : AlgebraicK1 ℂ)
    (c : relativeCyclicCohomology ℂ A M (2 * m + 1)) :
    (AlgebraicK1.oddPairing (Unitization ℂ A) M m
        (AlgebraicK1.map (algebraMap ℂ (Unitization ℂ A)) y)).toAdd
      (reducedCyclicCohomology.toCyclic ℂ (Unitization ℂ A) M (2 * m + 1) c) = 0 := by
  obtain ⟨n, u, rfl⟩ := AlgebraicK1.exists_mk y
  obtain ⟨φ, rfl⟩ := reducedCyclicCohomology.mk_surjective ℂ (Unitization ℂ A) M (2 * m + 1) c
  rw [AlgebraicK1.map_mk, AlgebraicK1.oddPairing_mk, toAdd_ofAdd, LinearMap.comp_apply,
    reducedCyclicCohomology.toCyclic_mk,
    oddPairing_matrixExtension_mk]
  simp only [Units.coe_map_inv, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass,
    RingHom.mapMatrix_apply]
  -- Both entries `u⁻¹ - 1` and `u - 1` of the pairing are scalar matrices.
  convert smul_zero _
  convert matrixCochainExtension_map_algebraMap_eq_zero (φ : relativeCyclicCochains ℂ A M _)
    fun k : Fin (2 * m + 2) ↦ if Even (k : ℕ) then (↑u⁻¹ - 1 : Matrix (Fin n) (Fin n) ℂ) else ↑u - 1
    using 2
  funext k
  split_ifs <;> simp [Matrix.map_sub, Matrix.map_one]

namespace relativeAlgebraicK1

variable (A M) in
/-- **Connes' odd pairing of relative `K₁` with relative cyclic cohomology** in degree `2m + 1`: a
relative class of `K₁(A⁺)` is sent to the functional `c ↦ ⟨x, c⟩` on `HC²ᵐ⁺¹(A; M)`, Connes' odd
pairing of `x` with the image of `c` in the cyclic cohomology of the forced unitization. It is a
homomorphism to the additive group of functionals, written multiplicatively. -/
def oddPairing (m : ℕ) :
    relativeAlgebraicK1 ℂ A →*
      Multiplicative (relativeCyclicCohomology ℂ A M (2 * m + 1) →ₗ[ℂ] M) :=
  MonoidHom.comp
    (AddMonoidHom.toMultiplicative (LinearMap.lcomp ℂ M
      (reducedCyclicCohomology.toCyclic ℂ (Unitization ℂ A) M (2 * m + 1)).hom).toAddMonoidHom)
    ((AlgebraicK1.oddPairing (Unitization ℂ A) M m).comp (relativeAlgebraicK1 ℂ A).subtype)

/-- The odd pairing of a relative class `x` with a relative cyclic class `c` is the odd pairing of
`x` with the image of `c` in the cyclic cohomology of the forced unitization. -/
theorem oddPairing_apply (m : ℕ) (x : relativeAlgebraicK1 ℂ A)
    (c : relativeCyclicCohomology ℂ A M (2 * m + 1)) :
    (oddPairing A M m x).toAdd c =
      (AlgebraicK1.oddPairing (Unitization ℂ A) M m x).toAdd
        (reducedCyclicCohomology.toCyclic ℂ (Unitization ℂ A) M (2 * m + 1) c) :=
  (rfl)

/-- **Connes' formula for the relative odd pairing**: an invertible matrix `u` over `A⁺` with a
relative class pairs with the class of a relative cyclic cocycle `φ` of degree `n = 2m + 1` as
`(1 + i)⁻¹ 2⁻ⁿ Γ(n/2 + 1)⁻¹ (φ#Tr)(u⁻¹ - 1, u - 1, …, u⁻¹ - 1, u - 1)`. -/
theorem oddPairing_mk_mk (m n : ℕ) (u : GL (Fin n) (Unitization ℂ A))
    (hu : AlgebraicK1.mk (Unitization ℂ A) n u ∈ relativeAlgebraicK1 ℂ A)
    (φ : reducedCyclicCocycles ℂ (Unitization ℂ A) M (2 * m + 1)) :
    (oddPairing A M m ⟨_, hu⟩).toAdd
        (reducedCyclicCohomology.mk ℂ (Unitization ℂ A) M (2 * m + 1) φ) =
      ((1 + Complex.I)⁻¹ * ((2 : ℂ) ^ (2 * m + 1))⁻¹ *
          ((Real.Gamma ((2 * m + 1 : ℝ) / 2 + 1) : ℂ))⁻¹) •
        matrixCochainExtension (Fin n) (2 * m + 1)
          ((φ : relativeCyclicCochains ℂ A M (2 * m + 1)) :
            MultilinearMap ℂ (fun _ : Fin (2 * m + 2) ↦ Unitization ℂ A) M)
          fun k ↦ if Even (k : ℕ) then ↑u⁻¹ - 1 else ↑u - 1 := by
  rw [oddPairing_apply, AlgebraicK1.oddPairing_mk, toAdd_ofAdd, LinearMap.comp_apply,
    reducedCyclicCohomology.toCyclic_mk,
    oddPairing_matrixExtension_mk]

/-- **The pairing of an arbitrary class of `A⁺` sees only its relative part**: a class `x` of `A⁺`
pairs with a relative cyclic class as its relative part `x · s(ε(x))⁻¹` does. -/
@[simp]
theorem oddPairing_projection (m : ℕ) (x : AlgebraicK1 (Unitization ℂ A))
    (c : relativeCyclicCohomology ℂ A M (2 * m + 1)) :
    (oddPairing A M m (projection ℂ A x)).toAdd c =
      (AlgebraicK1.oddPairing (Unitization ℂ A) M m x).toAdd
        (reducedCyclicCohomology.toCyclic ℂ (Unitization ℂ A) M (2 * m + 1) c) := by
  conv_rhs => rw [← coe_projection_mul_map_algebraMap x, ← AlgebraicK1.map_map]
  rw [map_mul, toAdd_mul, LinearMap.add_apply,
    AlgebraicK1.oddPairing_map_algebraMap_toUnitization_eq_zero, add_zero, oddPairing_apply]

/-- **Naturality of the relative odd pairing**: for a homomorphism of nonunital algebras
`f : A →ₙₐ[ℂ] B`, the image of a relative class `x` pairs with a relative cyclic class of `B` as
`x` pairs with the pullback of the class along `f`. -/
theorem oddPairing_map {B : Type _} [NonUnitalRing B] [Module ℂ B] [IsScalarTower ℂ B B]
    [SMulCommClass ℂ B B] (f : A →ₙₐ[ℂ] B) (m : ℕ) (x : relativeAlgebraicK1 ℂ A) :
    (oddPairing B M m (map f x)).toAdd =
      (oddPairing A M m x).toAdd ∘ₗ (relativeCyclicCohomology.map M f (2 * m + 1)).hom := by
  refine LinearMap.ext fun c ↦ ?_
  rw [oddPairing_apply, coe_map_apply, LinearMap.comp_apply, oddPairing_apply,
    relativeCyclicCohomology.toCyclic_map_unitization]
  exact LinearMap.congr_fun (AlgebraicK1.oddPairing_map (Unitization.map f) m (x : _)) _

end relativeAlgebraicK1

end TauCeti
