/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.GradedMulAction
public import TauCeti.Algebra.Module.GradedModule.Internal

/-!
# The degree-zero part of a module homomorphism

An arbitrary homomorphism between internally graded modules need not be homogeneous, nor a
finite sum of homogeneous homomorphisms. Its degree-zero part nevertheless exists: on a
homogeneous input of degree `p`, retain just the degree-`p` component of the output.

This operation preserves linearity over the graded algebra, not just over the coefficient
ring. Composition with a degree-zero map on either side commutes with taking the degree-zero
part. Consequently an ungraded lift of a graded map can be replaced by a graded lift. This is
the bridge from projective underlying modules to projective objects in the graded category.

## References

* C. Năstăsescu and F. Van Oystaeyen, *Methods of Graded Rings*, Section 2.3, for graded
  projective modules and the homogeneous-component argument.
-/

public section

namespace TauCeti

open scoped DirectSum

namespace InternalGrading

universe uk uA uM uN uP

variable {k : Type uk} [CommSemiring k] {A : Type uA} [Semiring A] [Algebra k A]
  {M : Type uM} [AddCommMonoid M] [Module A M] [Module k M] [IsScalarTower k A M]
  {N : Type uN} [AddCommMonoid N] [Module A N] [Module k N] [IsScalarTower k A N]
  (G : InternalGrading k M) (H : InternalGrading k N)

/-- Assemble the degree-preserving part of a map using the internal decomposition of its source.
This auxiliary map is linear over the coefficient ring. -/
private noncomputable def degreeZeroPartBase (f : M →ₗ[A] N) : M →ₗ[k] N :=
  DirectSum.toModule k ℤ N (fun p =>
    (H.piece p).subtype ∘ₗ DirectSum.component k ℤ (fun q => H.piece q) p ∘ₗ
      (DirectSum.decomposeLinearEquiv H.piece).toLinearMap ∘ₗ
        f.restrictScalars k ∘ₗ (G.piece p).subtype) ∘ₗ
    (DirectSum.decomposeLinearEquiv G.piece).toLinearMap

private theorem degreeZeroPartBase_apply_of_mem (f : M →ₗ[A] N) {p : ℤ} {x : M}
    (hx : x ∈ G.piece p) :
    degreeZeroPartBase G H f x = (DirectSum.decompose H.piece (f x) p : N) := by
  have hdec := DirectSum.decomposeLinearEquiv_apply_coe G.piece p ⟨x, hx⟩
  simp only [degreeZeroPartBase, LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [hdec, DirectSum.toModule_lof]
  rfl

variable (𝒜 : ℤ → Submodule k A)
  [SetLike.GradedSMul 𝒜 G.piece] [SetLike.GradedSMul 𝒜 H.piece]

private theorem degreeZeroPartBase_smul_of_mem (f : M →ₗ[A] N)
    {i p : ℤ} {a : A} {x : M} (ha : a ∈ 𝒜 i) (hx : x ∈ G.piece p) :
    degreeZeroPartBase G H f (a • x) = a • degreeZeroPartBase G H f x := by
  rw [degreeZeroPartBase_apply_of_mem G H f (SetLike.GradedSMul.smul_mem ha hx),
    degreeZeroPartBase_apply_of_mem G H f hx, map_smul]
  have hsmul : LinearMap.IsHomogeneous (a • (LinearMap.id : N →ₗ[k] N))
      H.piece H.piece i := by
    rw [LinearMap.isHomogeneous_def]
    intro q y hy
    simpa only [LinearMap.smul_apply, LinearMap.id_apply, vadd_eq_add, add_comm] using
      (SetLike.GradedSMul.smul_mem (B := H.piece) ha hy)
  have h := (hsmul.map_decompose p (f x)).symm
  rw [add_comm p i] at h
  exact h

variable [DirectSum.Decomposition 𝒜]

include 𝒜 in
private theorem degreeZeroPartBase_map_smul (f : M →ₗ[A] N) (a : A) (x : M) :
    degreeZeroPartBase G H f (a • x) = a • degreeZeroPartBase G H f x := by
  -- First extend in the module input, then in the algebra scalar. Both internal decompositions
  -- span their ambient modules, so checking homogeneous inputs suffices.
  have hscalar : ∀ i (a : A), a ∈ 𝒜 i → ∀ x : M,
      degreeZeroPartBase G H f (a • x) = a • degreeZeroPartBase G H f x := by
    intro i a ha
    have h := G.linearMap_ext (f := (degreeZeroPartBase G H f).comp
        (a • (LinearMap.id : M →ₗ[k] M)))
      (g := a • degreeZeroPartBase G H f)
      (fun p x hx => degreeZeroPartBase_smul_of_mem G H 𝒜 f ha hx)
    exact LinearMap.congr_fun h
  have h := (InternalGrading.ofDecomposition 𝒜).linearMap_ext
    (f := (degreeZeroPartBase G H f).comp (LinearMap.id.smulRight x))
    (g := LinearMap.id.smulRight (degreeZeroPartBase G H f x))
    (fun i a ha => hscalar i a (by simpa only [ofDecomposition_piece] using ha) x)
  exact LinearMap.congr_fun h a

/-- The degree-zero part of an `A`-linear map between graded `A`-modules. On a homogeneous
input of degree `p`, it retains the degree-`p` component of the output. No finite-generation
hypothesis is needed. -/
noncomputable def degreeZeroPart (f : M →ₗ[A] N) : M →ₗ[A] N where
  toFun := degreeZeroPartBase G H f
  map_add' := map_add _
  map_smul' := degreeZeroPartBase_map_smul G H 𝒜 f

/-- On a homogeneous input, the degree-zero part is the corresponding output component. -/
theorem degreeZeroPart_apply_of_mem (f : M →ₗ[A] N) {p : ℤ} {x : M}
    (hx : x ∈ G.piece p) :
    degreeZeroPart G H 𝒜 f x = (DirectSum.decompose H.piece (f x) p : N) :=
  degreeZeroPartBase_apply_of_mem G H f hx

/-- The degree-zero part is a homogeneous module map of degree zero. -/
theorem isHomogeneous_degreeZeroPart (f : M →ₗ[A] N) :
    LinearMap.IsHomogeneous (degreeZeroPart G H 𝒜 f) G.piece H.piece 0 := by
  rw [LinearMap.isHomogeneous_def]
  intro p x hx
  rw [add_zero, degreeZeroPart_apply_of_mem G H 𝒜 f hx]
  exact (DirectSum.decompose H.piece (f x) p).2

/-- Taking the degree-zero part fixes precisely the maps homogeneous of degree zero. -/
@[simp]
theorem degreeZeroPart_eq_self_iff (f : M →ₗ[A] N) :
    degreeZeroPart G H 𝒜 f = f ↔ LinearMap.IsHomogeneous f G.piece H.piece 0 := by
  constructor
  · intro hf
    rw [← hf]
    exact isHomogeneous_degreeZeroPart G H 𝒜 f
  · intro hf
    apply LinearMap.restrictScalars_injective k
    apply G.linearMap_ext
    intro p x hx
    exact (degreeZeroPart_apply_of_mem G H 𝒜 f hx).trans
      (DirectSum.decompose_of_mem_same H.piece (by simpa using hf.map_mem hx))

variable {P : Type uP} [AddCommMonoid P] [Module A P] [Module k P] [IsScalarTower k A P]
  (I : InternalGrading k P) [SetLike.GradedSMul 𝒜 I.piece]

/-- Postcomposition by a homogeneous map of degree zero commutes with taking the degree-zero
part. This allows an ungraded factorization of a graded map to be made graded. -/
theorem comp_degreeZeroPart (f : M →ₗ[A] N) {g : N →ₗ[A] P}
    (hg : LinearMap.IsHomogeneous g H.piece I.piece 0) :
    g.comp (degreeZeroPart G H 𝒜 f) = degreeZeroPart G I 𝒜 (g.comp f) := by
  apply LinearMap.restrictScalars_injective k
  apply G.linearMap_ext
  intro p x hx
  simp only [LinearMap.restrictScalars_apply, LinearMap.comp_apply]
  rw [degreeZeroPart_apply_of_mem G H 𝒜 f hx,
    degreeZeroPart_apply_of_mem G I 𝒜 (g.comp f) hx]
  have h := hg.map_decompose p (f x)
  rw [add_zero] at h
  exact h

/-- Precomposition by a homogeneous map of degree zero commutes with taking the degree-zero
part. -/
theorem degreeZeroPart_comp (f : N →ₗ[A] P) {g : M →ₗ[A] N}
    (hg : LinearMap.IsHomogeneous g G.piece H.piece 0) :
    degreeZeroPart G I 𝒜 (f.comp g) = (degreeZeroPart H I 𝒜 f).comp g := by
  apply LinearMap.restrictScalars_injective k
  apply G.linearMap_ext
  intro p x hx
  simp only [LinearMap.restrictScalars_apply, LinearMap.comp_apply]
  rw [degreeZeroPart_apply_of_mem G I 𝒜 (f.comp g) hx,
    degreeZeroPart_apply_of_mem H I 𝒜 f (by simpa using hg.map_mem hx)]
  rfl

end InternalGrading

end TauCeti
