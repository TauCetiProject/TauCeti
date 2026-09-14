/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Projection
public import TauCeti.Algebra.Homology.AInfinity.Algebra.Unit
public import TauCeti.RingTheory.GradedAlgebra.Trivial

/-!
# Augmented `A∞` algebras

An augmentation of a strictly unital `A∞` algebra is a strict morphism to the ground ring,
concentrated in degree zero.  Thus it preserves the strict unit and the binary operation, while it
annihilates every operation of arity other than two.  Its kernel is the reduced augmentation ideal:
all unary and higher operations land in this ideal, and the binary operation preserves it as soon
as one input lies in it.

The strict unit splits the augmentation.  Consequently the underlying module is canonically the
product of the ground ring and the reduced augmentation ideal.  This is the decomposition used by
the reduced bar construction, whose tensor words are formed from the second factor.

## Main definitions

* `TauCeti.AInfinityAlgebra.Augmentation`: a strict augmentation to the ground ring.
* `TauCeti.AInfinityAlgebra.Augmentation.augmentationIdeal`: its homogeneous kernel.
* `TauCeti.AInfinityAlgebra.Augmentation.splitLinearEquiv`: the scalar--reduced decomposition.

## References

* B. Keller, *Introduction to A-infinity algebras and modules*, Sections 3.1 and 3.6.
-/

public section

namespace TauCeti

universe uR uA

namespace AInfinityAlgebra

variable {R : Type uR} {A : Type uA} [CommRing R] [AddCommGroup A] [Module R A]

/-- An augmentation of a strictly unital `A∞` algebra over `R`.

The underlying degree-zero linear map is a strict `A∞` morphism to `R` with its ordinary
multiplication and zero operations in every other arity.  The chosen element `e` is required to be
a strict unit and to map to one. -/
structure Augmentation (𝒜 : AInfinityAlgebra R A) (e : A) where
  /-- The chosen element is a strict unit. -/
  toStrictUnit : 𝒜.StrictUnit e
  /-- The underlying linear map to the ground ring. -/
  toLinearMap : A →ₗ[R] R
  /-- The augmentation has degree zero, where the ground ring has its trivial grading. -/
  map_mem : LinearMap.IsHomogeneous toLinearMap 𝒜.grading.piece (trivialGrading R R) 0
  /-- The augmentation sends the strict unit to one. -/
  map_unit : toLinearMap e = 1
  /-- The augmentation preserves the binary operation. -/
  map_binary : ∀ x y, toLinearMap (𝒜.m 2 ![x, y]) = toLinearMap x * toLinearMap y
  /-- The augmentation annihilates operations of arity other than two. -/
  map_m_of_ne_two : ∀ (n : ℕ), n ≠ 2 → ∀ x, toLinearMap (𝒜.m n x) = 0

namespace Augmentation

variable {𝒜 : AInfinityAlgebra R A} {e : A}

instance : CoeFun (𝒜.Augmentation e) fun _ ↦ A → R :=
  ⟨fun ε ↦ ε.toLinearMap⟩

attribute [simp] Augmentation.map_unit Augmentation.map_binary Augmentation.map_m_of_ne_two

/-- Augmentations are determined by their underlying linear maps. -/
@[ext]
theorem ext {ε ε' : 𝒜.Augmentation e} (h : ε.toLinearMap = ε'.toLinearMap) : ε = ε' := by
  cases ε
  cases ε'
  cases h
  rfl

@[simp]
theorem map_zero (ε : 𝒜.Augmentation e) : ε 0 = 0 :=
  ε.toLinearMap.map_zero

@[simp]
theorem map_add (ε : 𝒜.Augmentation e) (x y : A) : ε (x + y) = ε x + ε y :=
  ε.toLinearMap.map_add x y

@[simp]
theorem map_sub (ε : 𝒜.Augmentation e) (x y : A) : ε (x - y) = ε x - ε y :=
  ε.toLinearMap.map_sub x y

/-- A homogeneous element of nonzero degree has zero augmentation. -/
theorem map_eq_zero_of_mem_piece (ε : 𝒜.Augmentation e) {p : ℤ} (hp : p ≠ 0) {x : A}
    (hx : x ∈ 𝒜.grading.piece p) : ε x = 0 := by
  have hεx := ε.map_mem.map_mem hx
  exact ((mem_trivialGrading_iff R R).mp hεx).resolve_left (by simpa using hp)

/-- An augmentation is surjective because it sends the strict unit to one. -/
theorem surjective (ε : 𝒜.Augmentation e) : Function.Surjective ε := by
  intro r
  refine ⟨r • e, ?_⟩
  simp

/-- The augmentation ideal, the kernel of the underlying linear map. -/
def augmentationIdeal (ε : 𝒜.Augmentation e) : Submodule R A :=
  LinearMap.ker ε.toLinearMap

/-- Membership in the augmentation ideal is equivalent to vanishing under the augmentation. -/
@[simp]
theorem mem_augmentationIdeal (ε : 𝒜.Augmentation e) {x : A} :
    x ∈ ε.augmentationIdeal ↔ ε x = 0 :=
  LinearMap.mem_ker

/-- Every homogeneous component of an element of the augmentation ideal remains in the ideal. -/
theorem decompose_mem_augmentationIdeal (ε : 𝒜.Augmentation e) {x : A}
    (hx : x ∈ ε.augmentationIdeal) (p : ℤ) :
    (DirectSum.decompose 𝒜.grading.piece x p : A) ∈ ε.augmentationIdeal := by
  rw [ε.mem_augmentationIdeal] at hx ⊢
  by_cases hp : p = 0
  · subst p
    have hε := 𝒜.grading.map_eq_map_decompose (N := R) ε.toLinearMap.toAddHom
      (fun j y hy hj ↦ ε.map_eq_zero_of_mem_piece hj hy) x
    exact hε.symm.trans hx
  · exact ε.map_eq_zero_of_mem_piece hp (DirectSum.decompose 𝒜.grading.piece x p).2

/-- Every operation outside arity two takes values in the augmentation ideal. -/
theorem m_mem_augmentationIdeal_of_ne_two (ε : 𝒜.Augmentation e) {n : ℕ} (hn : n ≠ 2)
    (x : Fin n → A) : 𝒜.m n x ∈ ε.augmentationIdeal := by
  rw [ε.mem_augmentationIdeal, ε.map_m_of_ne_two n hn]

/-- The binary operation takes values in the augmentation ideal if either input belongs to it. -/
theorem binary_mem_augmentationIdeal (ε : 𝒜.Augmentation e) {x y : A}
    (hxy : x ∈ ε.augmentationIdeal ∨ y ∈ ε.augmentationIdeal) :
    𝒜.m 2 ![x, y] ∈ ε.augmentationIdeal := by
  rw [ε.mem_augmentationIdeal, ε.map_binary]
  rcases hxy with hx | hy
  · rw [(ε.mem_augmentationIdeal).mp hx, zero_mul]
  · rw [(ε.mem_augmentationIdeal).mp hy, mul_zero]

/-- The scalar section determined by the strict unit. -/
def unitLinearMap (_ε : 𝒜.Augmentation e) : R →ₗ[R] A :=
  LinearMap.toSpanSingleton R A e

/-- The scalar section sends a scalar to that multiple of the strict unit. -/
@[simp]
theorem unitLinearMap_apply (ε : 𝒜.Augmentation e) (r : R) :
    ε.unitLinearMap r = r • e :=
  LinearMap.toSpanSingleton_apply R A e r

/-- The augmentation is a retraction of its scalar section. -/
@[simp]
theorem comp_unitLinearMap (ε : 𝒜.Augmentation e) :
    ε.toLinearMap.comp ε.unitLinearMap = LinearMap.id := by
  apply LinearMap.ext
  intro r
  simp

/-- Removing the scalar part of an element leaves an element of the augmentation ideal. -/
theorem sub_smul_unit_mem_augmentationIdeal (ε : 𝒜.Augmentation e) (x : A) :
    x - ε x • e ∈ ε.augmentationIdeal := by
  rw [ε.mem_augmentationIdeal, ε.map_sub, ε.toLinearMap.map_smul, ε.map_unit, smul_eq_mul,
    mul_one, sub_self]

/-- The projection onto the augmentation ideal, obtained by subtracting the scalar part. -/
def reducedPart (ε : 𝒜.Augmentation e) :
    A →ₗ[R] ε.augmentationIdeal :=
  LinearMap.codRestrict _
    (LinearMap.id - ε.unitLinearMap.comp ε.toLinearMap)
    ε.sub_smul_unit_mem_augmentationIdeal

/-- The reduced-part projection subtracts the scalar multiple of the strict unit. -/
@[simp]
theorem coe_reducedPart (ε : 𝒜.Augmentation e) (x : A) :
    (ε.reducedPart x : A) = x - ε x • e := by
  rfl

/-- The reduced-part projection fixes the augmentation ideal pointwise. -/
@[simp]
theorem reducedPart_coe (ε : 𝒜.Augmentation e) (x : ε.augmentationIdeal) :
    ε.reducedPart (x : A) = x := by
  apply Subtype.ext
  rw [ε.coe_reducedPart, (ε.mem_augmentationIdeal).mp x.property, zero_smul, sub_zero]

/-- The canonical splitting into scalar and reduced parts. -/
noncomputable def splitLinearEquiv (ε : 𝒜.Augmentation e) :
    A ≃ₗ[R] R × ε.augmentationIdeal :=
  LinearMap.equivProdOfSurjectiveOfIsCompl ε.toLinearMap ε.reducedPart
    (LinearMap.range_eq_top.2 ε.surjective) (LinearMap.range_eq_of_proj ε.reducedPart_coe)
    (LinearMap.isCompl_of_proj ε.reducedPart_coe)

/-- The splitting records the scalar and reduced parts of an element. -/
@[simp]
theorem splitLinearEquiv_apply (ε : 𝒜.Augmentation e) (x : A) :
    ε.splitLinearEquiv x = (ε x, ε.reducedPart x) := (rfl)

/-- The inverse splitting adds the scalar and reduced parts. -/
@[simp]
theorem splitLinearEquiv_symm_apply (ε : 𝒜.Augmentation e)
    (x : R × ε.augmentationIdeal) :
    ε.splitLinearEquiv.symm x = x.1 • e + x.2 := by
  have hx : ε (x.2 : A) = 0 := (ε.mem_augmentationIdeal).mp x.2.property
  rw [LinearEquiv.symm_apply_eq, ε.splitLinearEquiv_apply]
  refine Prod.ext ?_ (Subtype.ext ?_)
  · rw [ε.map_add, ε.toLinearMap.map_smul, ε.map_unit, smul_eq_mul, mul_one, hx, add_zero]
  · rw [ε.coe_reducedPart, ε.map_add, ε.toLinearMap.map_smul, ε.map_unit, smul_eq_mul, mul_one, hx,
      add_zero, add_sub_cancel_left]

end Augmentation

end AInfinityAlgebra

end TauCeti
