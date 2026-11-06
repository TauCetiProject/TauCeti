/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Torus.Basic
public import TauCeti.LinearAlgebra.Basis.DiagonalTorus.Restriction

/-!
# Restriction of the character lattice in Kostant torus matrix coordinates

The restriction and range theorems `Module.Basis.weightTorus_torusPointMap`,
`Module.Basis.weightTorus_mem_range_iff` and `Module.Basis.range_weightTorus_eq_of_injective`
transport to `kostantTorusMatrix` through the chosen basis. They apply to arbitrary lattice maps
and weights, without assuming that the lattice is the full weight lattice of a Chevalley datum.
-/

public section

namespace TauCeti.UniversalEnvelopingAlgebra

variable {κ ν V : Type*} [Fintype κ] [Fintype ν] [AddCommGroup V]
  (M : AddSubgroup V) {n : ℕ} (b : Module.Basis (Fin n) ℤ M)
  {A : Type*} [CommRing A] [Algebra ℤ A]

/-- Equality of torus matrices is equality of the corresponding weighted basis automorphisms,
even when their character lattices differ. -/
theorem kostantTorusMatrix_eq_iff (wt : Fin n → κ → ℤ) (wt' : Fin n → ν → ℤ)
    (s : κ → Aˣ) (u : ν → Aˣ) :
    kostantTorusMatrix M b wt s = kostantTorusMatrix M b wt' u ↔
      basisWeightTorus (b.baseChange A) wt s = basisWeightTorus (b.baseChange A) wt' u := by
  rw [← basisMatrix_kostantTorusPoints, ← basisMatrix_kostantTorusPoints,
    (Units.map_injective (LinearMap.toMatrixAlgEquiv (b.baseChange A)).injective).eq_iff,
    ← kostantTorusPoints_toLinearEquiv, ← kostantTorusPoints_toLinearEquiv]
  constructor
  · exact congrArg LinearMap.GeneralLinearGroup.toLinearEquiv
  · intro h
    apply Units.ext
    ext x
    simpa only [LinearMap.GeneralLinearGroup.coe_toLinearEquiv] using
      congrArg (fun f => f x) h

/-- Pulling back weights along a lattice map restricts the torus parameter in matrix coordinates.
-/
-- Not a simp lemma: `kostantTorusMatrix_apply` already rewrites both sides to diagonal form.
theorem kostantTorusMatrix_torusPointMap [DecidableEq κ] (wt : Fin n → κ → ℤ)
    (φ : (κ → ℤ) →ₗ[ℤ] (ν → ℤ)) (s : ν → Aˣ) :
    kostantTorusMatrix M b wt (torusPointMap φ s) =
      kostantTorusMatrix M b (fun i => φ (wt i)) s := by
  simp only [kostantTorusMatrix_apply, torusCharacter_torusPointMap]

/-- For spanning coordinate weights, a torus matrix is reached by the ambient-lattice
parametrization precisely when its parameter extends along the lattice map. -/
theorem kostantTorusMatrix_mem_range_iff [DecidableEq κ] (wt : Fin n → κ → ℤ)
    (hwt : Submodule.span ℤ (Set.range wt) = ⊤)
    (φ : (κ → ℤ) →ₗ[ℤ] (ν → ℤ)) (s : κ → Aˣ) :
    kostantTorusMatrix M b wt s ∈
        (kostantTorusMatrix M b (fun i => φ (wt i)) (A := A)).range ↔
      s ∈ (torusPointMap (R := A) φ).range := by
  simpa only [MonoidHom.mem_range, kostantTorusMatrix_eq_iff] using
    (b.baseChange A).weightTorus_mem_range_iff wt hwt φ s

/-- With divisible units, restriction along an injective lattice map preserves the image of the
matrix torus. -/
theorem range_kostantTorusMatrix_eq_of_injective [RootableBy Aˣ ℕ]
    (wt : Fin n → κ → ℤ) {φ : (κ → ℤ) →ₗ[ℤ] (ν → ℤ)} (hφ : Function.Injective φ) :
    (kostantTorusMatrix M b (fun i => φ (wt i)) (A := A)).range =
      (kostantTorusMatrix M b wt (A := A)).range := by
  have h := (b.baseChange A).range_weightTorus_eq_of_injective wt hφ
  apply le_antisymm
  · rintro g ⟨s, rfl⟩
    obtain ⟨u, hu⟩ := (le_of_eq h) ⟨s, rfl⟩
    exact ⟨u, (kostantTorusMatrix_eq_iff M b _ _ _ _).2 hu⟩
  · rintro g ⟨s, rfl⟩
    obtain ⟨u, hu⟩ := (ge_of_eq h) ⟨s, rfl⟩
    exact ⟨u, (kostantTorusMatrix_eq_iff M b _ _ _ _).2 hu⟩

end TauCeti.UniversalEnvelopingAlgebra
