/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.DualLattice
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
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
* `LinearMap.BilinForm.dualSubmodule_anti`: dualizing reverses inclusions.
* `LinearMap.BilinForm.det_toMatrix_smul_mem_span`: Cramer's rule for dual lattices; if the Gram
  matrix of a basis `b` has entries in `R`, then its determinant times any element of the dual of
  `span R b` lies in `span R b`.
-/

public section

open Module Matrix

namespace TauCeti

universe u

section Cramer

variable {R K V : Type*} [CommRing R] [Field K] [Algebra R K]
variable [AddCommGroup V] [Module R V] [Module K V] [IsScalarTower R K V]

/-- Taking dual submodules with respect to a bilinear form reverses inclusions. -/
theorem _root_.LinearMap.BilinForm.dualSubmodule_anti (B : LinearMap.BilinForm K V) :
    Antitone (B.dualSubmodule (R := R)) :=
  fun _ _ h _ hx y hy => hx y (h hy)

/-- **Cramer's rule for dual lattices.** Let `b` be a basis of `V` over the field `K` such that
every Gram matrix entry `B (b i) (b j)` lies in `R`. Then the Gram determinant
`r = det (B (b i) (b j))` multiplies the dual of the `R`-span of `b` into that span: `r • x` lies in
the `R`-span of `b` whenever every `B x (b j)` lies in `R`. When `B` is nondegenerate, `r ≠ 0`
(`LinearMap.BilinForm.nondegenerate_iff_det_ne_zero`), so the dual lattice lies in
`r⁻¹ • span R (Set.range b)`.

The adjugate argument is adapted from Mathlib's `Algebra.discr_mul_isIntegral_mem_adjoin`, which
treats the trace form of a separable field extension and a power basis; here it is stated for an
arbitrary bilinear form and basis. -/
theorem _root_.LinearMap.BilinForm.det_toMatrix_smul_mem_span (B : LinearMap.BilinForm K V)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι K V)
    (hb : ∀ i j, B (b i) (b j) ∈ (1 : Submodule R K)) {x : V}
    (hx : x ∈ B.dualSubmodule (Submodule.span R (Set.range b))) :
    (LinearMap.BilinForm.toMatrix b B).det • x ∈ Submodule.span R (Set.range b) := by
  choose G hG using fun i j => Submodule.mem_one.1 (hb i j)
  choose t ht using fun j => Submodule.mem_one.1 (hx (b j) (Submodule.subset_span ⟨j, rfl⟩))
  have hGmap : LinearMap.BilinForm.toMatrix b B = (algebraMap R K).mapMatrix (Matrix.of G) := by
    ext i j
    simp [hG, LinearMap.BilinForm.toMatrix_apply]
  -- the coordinates `c` of `x` satisfy `c ᵥ* (Gram matrix) = t`
  have hc : b.equivFun x ᵥ* LinearMap.BilinForm.toMatrix b B = fun j => algebraMap R K (t j) := by
    ext j
    rw [ht]
    conv_rhs => rw [← b.sum_repr x]
    simp only [vecMul, dotProduct, LinearMap.BilinForm.toMatrix_apply, Basis.equivFun_apply,
      map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  -- multiplying by the adjugate gives `det • c = t ᵥ* adjugate G`, whose entries lie in `R`
  have hdet : (LinearMap.BilinForm.toMatrix b B).det • b.equivFun x =
      fun j => algebraMap R K ((t ᵥ* (Matrix.of G).adjugate) j) := by
    rw [← vecMul_one (b.equivFun x), ← vecMul_smul, ← mul_adjugate, ← vecMul_vecMul, hc, hGmap,
      ← RingHom.map_adjugate]
    ext j
    simp [vecMul, dotProduct]
  rw [← b.sum_equivFun x, Finset.smul_sum]
  refine sum_mem fun i _ => ?_
  rw [smul_smul, ← smul_eq_mul, ← Pi.smul_apply _ (b.equivFun x), hdet, algebraMap_smul]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

end Cramer

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

end TauCeti
