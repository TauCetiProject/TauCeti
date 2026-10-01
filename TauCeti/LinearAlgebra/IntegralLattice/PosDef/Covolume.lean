/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.ZLattice.Covolume
public import TauCeti.LinearAlgebra.IntegralLattice.Gram

/-!
# The covolume of an integral lattice realized in Euclidean space

A *realization* of an integral lattice `L` in a real inner product space `E` is a `ℤ`-linear map
`φ : L → E` carrying the integral form to the inner product,
`⟪φ x, φ y⟫ = β(x, y)`, whose image spans `E` over `ℝ`. When `L` is nondegenerate, this file
proves that the image `φ(L)` is a `ℤ`-lattice in `E` (discrete and of full rank) and that its
covolume, for the volume measure of the inner product, satisfies

`covolume(φ(L))² = det L`, equivalently `covolume(φ(L)) = √(disc L)`.

This reconciles the analytic covolume of Mathlib's `ZLattice` with the algebraic determinant of
the lattice. The form of a realized lattice is the pullback of an inner product, so only positive
semidefinite lattices have realizations, and nondegeneracy is the hypothesis that rules out a
collapsing `φ`: the zero form on `ℤ`, realized by the zero map into the zero space, has
determinant `0` but covolume `1`.

## Main results

* `TauCeti.IntegralLattice.gram_comp_eq_map_gramMatrix`: the Gram matrix of the image of a carrier
  basis is the integral Gram matrix of the lattice.
* `TauCeti.IntegralLattice.injective_of_inner_eq`: a realization of a nondegenerate lattice is
  injective.
* `TauCeti.IntegralLattice.linearIndependent_comp_basis`: it carries carrier bases to
  `ℝ`-linearly independent families.
* `TauCeti.IntegralLattice.discreteTopology_range`: the image of a full realization is discrete,
  hence a `ℤ`-lattice in `E`.
* `TauCeti.IntegralLattice.covolume_range_sq_eq_determinant`: `covolume(φ(L))² = det L`.
* `TauCeti.IntegralLattice.covolume_range_eq_sqrt_discriminant`: `covolume(φ(L)) = √(disc L)`.

## References

* J. W. S. Cassels, *An Introduction to the Geometry of Numbers*, Chapter I, §2.
* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, Chapter 1, §1.
-/

public section

open Module MeasureTheory
open scoped InnerProductSpace

namespace TauCeti.IntegralLattice

universe u

variable {V : Type u} [AddCommGroup V] [Module ℚ V] {L : IntegralLattice V}
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {φ : L →ₗ[ℤ] E}

section Gram

variable (hφ : ∀ x y : L, ⟪φ x, φ y⟫_ℝ = L.integralForm x y)
include hφ

/-- A map carrying the integral form to the inner product carries the integral Gram matrix of a
carrier basis to the real Gram matrix of its image. -/
theorem gram_comp_eq_map_gramMatrix {ι : Type*} (e : Basis ι ℤ L) :
    Matrix.gram ℝ (fun i ↦ φ (e i)) = (L.gramMatrix e).map ((↑) : ℤ → ℝ) := by
  ext i j
  simp [Matrix.gram_apply, hφ]

/-- A map carrying the integral form to the inner product carries every carrier basis to a family
whose Gram determinant is the determinant of the lattice. -/
theorem det_gram_comp_eq_determinant {ι : Type*} [Fintype ι] [DecidableEq ι] (e : Basis ι ℤ L) :
    (Matrix.gram ℝ (fun i ↦ φ (e i))).det = L.determinant := by
  rw [gram_comp_eq_map_gramMatrix hφ, ← Int.cast_det, ← gramDet_def, L.determinant_eq_gramDet e]

variable [L.IsNondegenerate]

/-- A map carrying the form of a nondegenerate lattice to the inner product is injective. -/
theorem injective_of_inner_eq : Function.Injective φ := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  refine ((nondegenerate_integralForm_iff L).mpr L.form_nondegenerate).1 x fun y ↦ ?_
  have h := hφ x y
  rw [hx, inner_zero_left] at h
  exact_mod_cast h.symm

/-- A map carrying the form of a nondegenerate lattice to the inner product carries every carrier
basis to an `ℝ`-linearly independent family. -/
theorem linearIndependent_comp_basis {ι : Type*} [Finite ι] (e : Basis ι ℤ L) :
    LinearIndependent ℝ (fun i ↦ φ (e i)) := by
  classical
  have := Fintype.ofFinite ι
  rw [← Matrix.det_gram_ne_zero_iff_linearIndependent, det_gram_comp_eq_determinant hφ]
  exact_mod_cast (determinant_ne_zero_iff L).mpr L.form_nondegenerate

variable (hspan : Submodule.span ℝ (Set.range φ) = ⊤)
include hspan

/-- The images of the chosen carrier basis under a full realization, as an `ℝ`-basis of `E`. -/
private noncomputable def realBasis : Basis (Free.ChooseBasisIndex ℤ L) ℝ E :=
  Basis.mk (linearIndependent_comp_basis hφ (Free.chooseBasis ℤ L)) <| by
    rw [← hspan, ← LinearMap.coe_range, LinearMap.range_eq_map,
      ← (Free.chooseBasis ℤ L).span_eq, Submodule.map_span, ← Set.range_comp,
      Submodule.span_span_of_tower]
    exact le_rfl

private theorem realBasis_apply (i : Free.ChooseBasisIndex ℤ L) :
    realBasis hφ hspan i = φ (Free.chooseBasis ℤ L i) :=
  Basis.mk_apply _ _ i

/-- The image of a full realization is the `ℤ`-span of the real basis it induces. -/
private theorem range_eq_span_realBasis :
    LinearMap.range φ = Submodule.span ℤ (Set.range (realBasis hφ hspan)) := by
  rw [LinearMap.range_eq_map, ← (Free.chooseBasis ℤ L).span_eq, Submodule.map_span,
    ← Set.range_comp]
  congr 2
  ext i
  exact (realBasis_apply hφ hspan i).symm

/-- The image of a full realization of a nondegenerate lattice is discrete. -/
theorem discreteTopology_range : DiscreteTopology (LinearMap.range φ) := by
  rw [range_eq_span_realBasis hφ hspan]
  infer_instance

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- **The covolume identity.** The square of the covolume of a nondegenerate integral lattice,
realized in a real inner product space, is its determinant. -/
theorem covolume_range_sq_eq_determinant :
    ZLattice.covolume (LinearMap.range φ) ^ 2 = L.determinant := by
  classical
  have := discreteTopology_range hφ hspan
  have : IsZLattice ℝ (LinearMap.range φ) := ⟨by rw [LinearMap.coe_range, hspan]⟩
  let e := Free.chooseBasis ℤ L
  rw [ZLattice.covolume_sq_eq_det_gram _ (e.map (LinearEquiv.ofInjective φ
    (injective_of_inner_eq hφ))), ← det_gram_comp_eq_determinant hφ e]
  simp

/-- The covolume of a nondegenerate integral lattice, realized in a real inner product space, is
the square root of its discriminant. -/
theorem covolume_range_eq_sqrt_discriminant :
    ZLattice.covolume (LinearMap.range φ) = √(L.discriminant : ℝ) := by
  have := discreteTopology_range hφ hspan
  have : IsZLattice ℝ (LinearMap.range φ) := ⟨by rw [LinearMap.coe_range, hspan]⟩
  rw [discriminant_def, Nat.cast_natAbs, Int.cast_abs,
    ← covolume_range_sq_eq_determinant hφ hspan, abs_sq,
    Real.sqrt_sq (ZLattice.covolume_pos _ _).le]

end Gram

end TauCeti.IntegralLattice
