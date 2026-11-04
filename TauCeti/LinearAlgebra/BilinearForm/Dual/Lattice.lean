/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.DualLattice
public import TauCeti.Algebra.Module.Lattice

/-!
# Dual submodules of lattices

This file develops the duality theory for full lattices in vector spaces equipped with a
nondegenerate bilinear form over a fraction field.

## Main declarations

* `LinearMap.BilinForm.dualSubmoduleToDual_surjective`: surjectivity of
  `dualSubmoduleToDual` for a full lattice and nondegenerate bilinear form.
* `LinearMap.BilinForm.dualSubmoduleEquivDual`: the canonical linear equivalence
  `B.dualSubmodule N ≃ₗ[R] Module.Dual R N`.
* `LinearMap.BilinForm.dualSubmoduleEquivDual_apply`: evaluation of
  `dualSubmoduleEquivDual` is `B.dualSubmoduleToDual N`.
* `LinearMap.BilinForm.dualSubmodule_dualSubmodule_flip`: double duality for free
  full lattices using `B.flip`.
* `LinearMap.BilinForm.dualSubmodule_flip_dualSubmodule`: double duality for free
  full lattices with `B.flip` on the outside.
* `LinearMap.BilinForm.fg_of_le_dualSubmodule`: over a Noetherian ring, a submodule which spans
  the ambient finite-dimensional space and lies in its own dual is finitely generated.
-/

public section

open Module

namespace TauCeti

universe u

variable {R K V : Type*} [CommRing R] [IsDomain R]
variable [Field K] [Algebra R K] [IsFractionRing R K] [Module.IsTorsionFree R K]
variable [AddCommGroup V] [Module R V] [Module K V] [IsScalarTower R K V]

/-- For a nondegenerate bilinear form `B` over the fraction field and a full lattice `N`, Mathlib's
canonical pairing `B.dualSubmoduleToDual N` from the dual lattice to the dual of `N` is
surjective. No lattice basis is needed. -/
theorem _root_.LinearMap.BilinForm.dualSubmoduleToDual_surjective
    (B : LinearMap.BilinForm K V) (hB : B.Nondegenerate)
    (N : Submodule R V) [N.IsLattice K] :
    Function.Surjective (B.dualSubmoduleToDual N) := by
  -- A linear form on the lattice extends to the fraction field, where nondegeneracy represents it
  -- by an ambient vector; that vector lies in the dual lattice and maps to the form.
  have := Module.Finite.of_isLattice (A := K) N
  have := Submodule.IsLattice.isLocalizedModule_subtype K N Submodule.IsLattice.span_eq_top
  intro f
  let fK : Module.Dual K V :=
    IsLocalizedModule.mapExtendScalars (nonZeroDivisors R) N.subtype (Algebra.linearMap R K) K f
  have hfK (n : N) : fK n = algebraMap R K (f n) :=
    IsLocalizedModule.map_apply (nonZeroDivisors R) N.subtype (Algebra.linearMap R K) f n
  let x := (B.toDual hB).symm fK
  have hx : x ∈ B.dualSubmodule N := by
    intro y hy
    rw [LinearMap.BilinForm.apply_toDual_symm_apply]
    exact Submodule.mem_one.mpr ⟨f ⟨y, hy⟩, (hfK ⟨y, hy⟩).symm⟩
  refine ⟨⟨x, hx⟩, ?_⟩
  ext n
  apply FaithfulSMul.algebraMap_injective R K
  rw [LinearMap.BilinForm.dualSubmoduleToDual_apply_apply,
    LinearMap.BilinForm.dualSubmodulePairing_spec]
  exact (B.apply_toDual_symm_apply fK n).trans (hfK n)

/-- The dual submodule of a full lattice is canonically isomorphic to its `R`-linear dual
whenever the ambient bilinear form is nondegenerate. -/
noncomputable def _root_.LinearMap.BilinForm.dualSubmoduleEquivDual
    (B : LinearMap.BilinForm K V) (hB : B.Nondegenerate)
    (N : Submodule R V) [hN : N.IsLattice K] :
    B.dualSubmodule N ≃ₗ[R] Module.Dual R N :=
  LinearEquiv.ofBijective (B.dualSubmoduleToDual N)
    ⟨B.dualSubmoduleToDual_injective hB N hN.span_eq_top,
      LinearMap.BilinForm.dualSubmoduleToDual_surjective B hB N⟩

/-- The underlying linear map of `dualSubmoduleEquivDual` is `B.dualSubmoduleToDual N`. -/
@[simp]
theorem _root_.LinearMap.BilinForm.dualSubmoduleEquivDual_apply
    (B : LinearMap.BilinForm K V) (hB : B.Nondegenerate)
    (N : Submodule R V) [N.IsLattice K] (x : B.dualSubmodule N) :
    LinearMap.BilinForm.dualSubmoduleEquivDual B hB N x = B.dualSubmoduleToDual N x :=
  LinearEquiv.ofBijective_apply (B.dualSubmoduleToDual N) x

omit [IsDomain R] [Module.IsTorsionFree R K] in
/-- Dualizing by `B.flip` and then by `B` recovers the original free full lattice. -/
theorem _root_.LinearMap.BilinForm.dualSubmodule_dualSubmodule_flip
    (B : LinearMap.BilinForm K V) (hB : B.Nondegenerate)
    (N : Submodule R V) [N.IsLattice K] [Module.Free R N] :
    B.dualSubmodule (B.flip.dualSubmodule N) = N := by
  let b := Module.Free.chooseBasis R N
  let b_ext := b.extendOfIsLattice K
  calc
    B.dualSubmodule (B.flip.dualSubmodule N) =
        B.dualSubmodule (B.flip.dualSubmodule (Submodule.span R (Set.range b_ext))) :=
      congrArg (fun S => B.dualSubmodule (B.flip.dualSubmodule S))
        b.span_range_extendOfIsLattice.symm
    _ = Submodule.span R (Set.range b_ext) :=
      B.dualSubmodule_dualSubmodule_flip_of_basis hB b_ext
    _ = N := b.span_range_extendOfIsLattice

omit [IsDomain R] [Module.IsTorsionFree R K] in
/-- Dualizing by `B` and then by `B.flip` recovers the original free full lattice. -/
theorem _root_.LinearMap.BilinForm.dualSubmodule_flip_dualSubmodule
    (B : LinearMap.BilinForm K V) (hB : B.Nondegenerate)
    (N : Submodule R V) [N.IsLattice K] [Module.Free R N] :
    B.flip.dualSubmodule (B.dualSubmodule N) = N := by
  have h := LinearMap.BilinForm.dualSubmodule_dualSubmodule_flip B.flip hB.flip N
  have hflip : B.flip.flip = B := by ext; rfl
  rwa [hflip] at h

section FG

variable {A K M : Type*} [CommRing A] [Field K] [AddCommGroup M] [Algebra A K] [Module A M]
  [Module K M] [IsScalarTower A K M] [FiniteDimensional K M]

/-- Over a Noetherian ring `A`, a submodule `N` which spans a finite-dimensional `K`-vector space
`M` and lies in its own dual for a nondegenerate bilinear form `B` is finitely generated: it lies
in the `A`-span of the dual basis of a basis of `M` chosen inside `N`. -/
theorem _root_.LinearMap.BilinForm.fg_of_le_dualSubmodule [IsNoetherianRing A]
    {B : LinearMap.BilinForm K M}
    (hB : B.Nondegenerate) {N : Submodule A M} (hspan : Submodule.span K (N : Set M) = ⊤)
    (hN : N ≤ B.dualSubmodule N) : N.FG := by
  classical
  obtain ⟨s, hsN, hs, hli⟩ := exists_linearIndependent K (N : Set M)
  have : Finite s := hli.finite_of_isNoetherian
  let b : Module.Basis s K M := .mk hli (by rw [Subtype.range_coe_subtype, Set.ofPred_mem_eq,
    hs, hspan])
  -- `N` lies in the dual of the `A`-span of `b`, which is the `A`-span of the dual basis.
  have hle : N ≤ B.dualSubmodule (Submodule.span A (Set.range b)) := fun m hm z hz ↦
    hN hm z (Submodule.span_le.2 (by simpa [b] using hsN) hz)
  rw [LinearMap.BilinForm.dualSubmodule_span_of_basis B hB b] at hle
  exact (Submodule.fg_span (Set.finite_range _)).of_le hle

end FG

end TauCeti
