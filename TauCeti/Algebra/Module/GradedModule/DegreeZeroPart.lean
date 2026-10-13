/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.GradedMulAction
public import TauCeti.Algebra.Module.GradedModule.Internal
import TauCeti.Algebra.DirectSum.Internal

/-!
# The degree-zero part of a module homomorphism

An arbitrary homomorphism between internally graded modules need not be homogeneous, nor a
finite sum of homogeneous homomorphisms. Its degree-zero part nevertheless exists: on a
homogeneous input of degree `p`, retain just the degree-`p` component of the output.

This operation preserves linearity over the graded scalar semiring. The coefficient semiring
used to form the homogeneous submodules need not be commutative, and the two scalar actions
need no scalar-tower compatibility. Composition with a degree-zero map on either side commutes
with taking the degree-zero part. Consequently an ungraded lift of a graded map can be replaced
by a graded lift. This is the bridge from projective underlying modules to projective objects
in the graded category.

## References

* C. Năstăsescu and F. Van Oystaeyen, *Methods of Graded Rings*, Section 2.3, for graded
  projective modules and the homogeneous-component argument.
-/

public section

namespace TauCeti

namespace InternalGrading

universe uk uA uM uN uP

variable {k : Type uk} [Semiring k] {A : Type uA} [Semiring A]
  {M : Type uM} [AddCommMonoid M] [Module A M] [Module k M]
  {N : Type uN} [AddCommMonoid N] [Module A N] [Module k N]
  (G : InternalGrading k M) (H : InternalGrading k N)

/-- Assemble the degree-preserving part of a map using the internal decomposition of its source.
This auxiliary map is additive; scalar compatibility will follow from the graded action. -/
private noncomputable def degreeZeroPartBase (f : M →ₗ[A] N) : M →+ N :=
  (DirectSum.toAddMonoid fun p =>
    (AddSubmonoidClass.subtype (H.piece p)).comp <|
      (DFinsupp.evalAddMonoidHom p).comp <|
        (DirectSum.decomposeAddEquiv H.piece).toAddMonoidHom.comp <|
          f.toAddMonoidHom.comp (AddSubmonoidClass.subtype (G.piece p))).comp
    (DirectSum.decomposeAddEquiv G.piece).toAddMonoidHom

private theorem degreeZeroPartBase_apply_of_mem (f : M →ₗ[A] N) {p : ℤ} {x : M}
    (hx : x ∈ G.piece p) :
    degreeZeroPartBase G H f x = (DirectSum.decompose H.piece (f x) p : N) := by
  simp [degreeZeroPartBase, DirectSum.decompose_of_mem G.piece hx, DFinsupp.evalAddMonoidHom]

variable {S : Type*} [SetLike S A] (𝒜 : ℤ → S)
  [SetLike.GradedSMul 𝒜 G.piece] [SetLike.GradedSMul 𝒜 H.piece]

private theorem degreeZeroPartBase_smul_of_mem (f : M →ₗ[A] N)
    {i p : ℤ} {a : A} {x : M} (ha : a ∈ 𝒜 i) (hx : x ∈ G.piece p) :
    degreeZeroPartBase G H f (a • x) = a • degreeZeroPartBase G H f x := by
  rw [degreeZeroPartBase_apply_of_mem G H f (SetLike.GradedSMul.smul_mem ha hx),
    degreeZeroPartBase_apply_of_mem G H f hx, map_smul]
  exact (DirectSum.map_decompose_shift H.piece H.piece (DistribSMul.toAddMonoidHom N a)
    (i + ·) (add_right_injective i) (fun _ _ hy => SetLike.GradedSMul.smul_mem ha hy)
    p (f x)).symm

variable [AddSubmonoidClass S A] [DirectSum.Decomposition 𝒜]

include 𝒜 in
private theorem degreeZeroPartBase_map_smul (f : M →ₗ[A] N) (a : A) (x : M) :
    degreeZeroPartBase G H f (a • x) = a • degreeZeroPartBase G H f x := by
  -- Both internal decompositions span their ambient additive monoids, so it suffices to
  -- check homogeneous scalars and homogeneous inputs.
  induction a using DirectSum.Decomposition.inductionOn 𝒜 with
  | zero => simp
  | homogeneous a =>
    induction x using DirectSum.Decomposition.inductionOn G.piece with
    | zero => simp
    | homogeneous x => exact degreeZeroPartBase_smul_of_mem G H 𝒜 f a.2 x.2
    | add x y hx hy => simp [smul_add, hx, hy]
  | add a b ha hb => simp [add_smul, ha, hb]

/-- The degree-zero part of an `A`-linear map between graded `A`-modules. On a homogeneous
input of degree `p`, it retains the degree-`p` component of the output. No finite-generation
hypothesis or scalar-tower compatibility is needed. The scalar grading may consist of any
additive subobjects of `A`. -/
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
@[simp]
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
    refine G.linearMap_ext fun p x hx ↦ ?_
    exact (degreeZeroPart_apply_of_mem G H 𝒜 f hx).trans
      (DirectSum.decompose_of_mem_same H.piece (by simpa using hf.map_mem hx))

variable {P : Type uP} [AddCommMonoid P] [Module A P] [Module k P]
  (I : InternalGrading k P) [SetLike.GradedSMul 𝒜 I.piece]

/-- Postcomposition by a homogeneous map of degree zero commutes with taking the degree-zero
part. This allows an ungraded factorization of a graded map to be made graded. -/
theorem comp_degreeZeroPart (f : M →ₗ[A] N) {g : N →ₗ[A] P}
    (hg : LinearMap.IsHomogeneous g H.piece I.piece 0) :
    g.comp (degreeZeroPart G H 𝒜 f) = degreeZeroPart G I 𝒜 (g.comp f) := by
  refine G.linearMap_ext fun p x hx ↦ ?_
  simp only [LinearMap.comp_apply]
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
  refine G.linearMap_ext fun p x hx ↦ ?_
  simp only [LinearMap.comp_apply]
  rw [degreeZeroPart_apply_of_mem G I 𝒜 (f.comp g) hx,
    degreeZeroPart_apply_of_mem H I 𝒜 f (by simpa using hg.map_mem hx)]
  rfl

end InternalGrading

end TauCeti
