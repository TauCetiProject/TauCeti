/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.NormTwoShell.Basic
public import Mathlib.Algebra.Lie.BaseChange
public import Mathlib.Algebra.Lie.CartanSubalgebra
public import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# The Cartan subalgebra of the signed shell Lie algebra

After extending scalars, the Cartan vectors of the signed norm-two-shell Lie algebra span an
abelian subalgebra. Its adjoint action is diagonal in the scalar-extended integral basis: it
vanishes on the Cartan vectors and acts on a root vector by its integral Gram pairing.
When multiplication by two is injective in the coefficient ring, this subalgebra is
self-normalizing and hence is a Cartan subalgebra. In particular this constructs the Cartan
subalgebra over the rationals, without requiring a Killing-form computation.

## References

* V. G. Kac, *Infinite dimensional Lie algebras*, third edition, §7.8.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §§8 and 14.
-/

public section

open Module TensorProduct

namespace Matrix.ShellLieAlgebra

noncomputable section

variable {I : Type*} [Fintype I] [LinearOrder I] (B : Matrix I I ℤ)
variable (A : Type*) [CommRing A]
variable [Fact B.PosDef] [Fact (∀ i, Even (B i i))]

/-- A Cartan vector acts trivially on the Cartan coordinates after scalar extension. -/
@[simp]
theorem basis_baseChange_repr_one_tmul_cartan_lie_inl (h : I → ℤ)
    (x : A ⊗[ℤ] ShellLieAlgebra B) (i : I) :
    ((basis B).baseChange A).repr ⁅(1 : A) ⊗ₜ[ℤ] cartan B h, x⁆ (.inl i) = 0 := by
  let b := (basis B).baseChange A
  have heq : (b.coord (.inl i)).comp
      (LieAlgebra.ad A (A ⊗[ℤ] ShellLieAlgebra B) ((1 : A) ⊗ₜ[ℤ] cartan B h)) = 0 := by
    apply b.ext
    intro j
    cases j with
    | inl j => simp [b, Basis.baseChange_apply, LieAlgebra.ad_apply]
    | inr a =>
      simp [b, Basis.baseChange_apply, LieAlgebra.ad_apply, TensorProduct.tmul_smul]
  exact congrArg (fun f => f x) heq

/-- A Cartan vector scales a root coordinate by its Gram pairing with that root. -/
@[simp]
theorem basis_baseChange_repr_one_tmul_cartan_lie_inr (h : I → ℤ)
    (x : A ⊗[ℤ] ShellLieAlgebra B) (a : B.normTwoShell) :
    ((basis B).baseChange A).repr ⁅(1 : A) ⊗ₜ[ℤ] cartan B h, x⁆ (.inr a) =
      (h ⬝ᵥ B *ᵥ (a : I → ℤ) : ℤ) • ((basis B).baseChange A).repr x (.inr a) := by
  let b := (basis B).baseChange A
  have heq : (b.coord (.inr a)).comp
      (LieAlgebra.ad A (A ⊗[ℤ] ShellLieAlgebra B) ((1 : A) ⊗ₜ[ℤ] cartan B h)) =
      ((h ⬝ᵥ B *ᵥ (a : I → ℤ) : ℤ) : A) • b.coord (.inr a) := by
    apply b.ext
    intro j
    cases j with
    | inl j => simp [b, Basis.baseChange_apply, LieAlgebra.ad_apply]
    | inr c =>
      by_cases hac : a = c
      · subst c
        simp [b, Basis.baseChange_apply, LieAlgebra.ad_apply, TensorProduct.tmul_smul]
      · simp [b, Basis.baseChange_apply, LieAlgebra.ad_apply, TensorProduct.tmul_smul, hac]
  simpa only [LinearMap.comp_apply, LinearMap.smul_apply, LieAlgebra.ad_apply,
    Int.cast_smul_eq_zsmul, Basis.coord_apply, b] using congrArg (fun f => f x) heq

private theorem lie_eq_zero_of_mem_range_cartan_basis :
    ∀ x ∈ Set.range (fun i : I => ((basis B).baseChange A) (.inl i)),
      ∀ y ∈ Set.range (fun i : I => ((basis B).baseChange A) (.inl i)), ⁅x, y⁆ = 0 := by
  rintro - ⟨i, rfl⟩ - ⟨j, rfl⟩
  simp [Basis.baseChange_apply]

/-- The abelian subalgebra spanned by the scalar-extended integral Cartan vectors. -/
def cartanSubalgebra : LieSubalgebra A (A ⊗[ℤ] ShellLieAlgebra B) :=
  LieSubalgebra.lieSpan A _ (Set.range fun i : I => ((basis B).baseChange A) (.inl i))

instance : IsLieAbelian (cartanSubalgebra B A) := by
  rw [cartanSubalgebra, LieSubalgebra.isLieAbelian_lieSpan_iff]
  exact lie_eq_zero_of_mem_range_cartan_basis B A

/-- The underlying module of the Cartan subalgebra is the span of the Cartan basis vectors. -/
theorem toSubmodule_cartanSubalgebra :
    (cartanSubalgebra B A).toSubmodule =
      Submodule.span A (Set.range fun i : I => ((basis B).baseChange A) (.inl i)) := by
  exact LieSubalgebra.coe_lieSpan_eq_span_of_forall_lie_eq_zero
    (lie_eq_zero_of_mem_range_cartan_basis B A)

/-- A vector belongs to the Cartan subalgebra precisely when all its root coordinates vanish. -/
@[simp]
theorem mem_cartanSubalgebra_iff (x : A ⊗[ℤ] ShellLieAlgebra B) :
    x ∈ cartanSubalgebra B A ↔
      ∀ a : B.normTwoShell, ((basis B).baseChange A).repr x (.inr a) = 0 := by
  classical
  -- The defining span is the image of the left summand of the basis index type.
  have hs : Set.range (fun i : I => ((basis B).baseChange A) (.inl i)) =
      ((basis B).baseChange A) '' Set.range Sum.inl := by
    ext x
    simp
  rw [← LieSubalgebra.mem_toSubmodule, toSubmodule_cartanSubalgebra, hs, Basis.mem_span_image]
  constructor
  · intro hx a
    by_contra ha
    have := hx (Finsupp.mem_support_iff.mpr ha)
    simp at this
  · intro hx j hj
    cases j with
    | inl i => exact ⟨i, rfl⟩
    | inr a => exact False.elim ((Finsupp.mem_support_iff.mp hj) (hx a))

/-- Every scalar-extended Cartan vector belongs to the Cartan subalgebra. -/
theorem tmul_cartan_mem_cartanSubalgebra (r : A) (h : I → ℤ) :
    r ⊗ₜ[ℤ] cartan B h ∈ cartanSubalgebra B A := by
  simp [mem_cartanSubalgebra_iff, Basis.baseChange_repr_tmul]

/-- If multiplication by two is injective, the Cartan span is self-normalizing. -/
theorem cartanSubalgebra_normalizer_eq_self (h2 : IsRegular (2 : A)) :
    (cartanSubalgebra B A).normalizer = cartanSubalgebra B A := by
  refine le_antisymm ?_ (cartanSubalgebra B A).le_normalizer
  intro x hx
  rw [mem_cartanSubalgebra_iff]
  intro a
  have hmem := ((cartanSubalgebra B A).mem_normalizer_iff' x).mp hx
    ((1 : A) ⊗ₜ[ℤ] cartan B (a : I → ℤ))
    (tmul_cartan_mem_cartanSubalgebra B A 1 a)
  have hz := (mem_cartanSubalgebra_iff B A _).mp hmem a
  rw [basis_baseChange_repr_one_tmul_cartan_lie_inr, mem_normTwoShell.mp a.2] at hz
  simp only [zsmul_eq_mul, Int.cast_ofNat] at hz
  exact h2.left (by simpa only [mul_zero] using hz)

/-- The scalar-extended Cartan span is a Cartan subalgebra whenever two is regular. -/
instance [h2 : Fact (IsRegular (2 : A))] :
    (cartanSubalgebra B A).IsCartanSubalgebra where
  nilpotent := inferInstance
  self_normalizing := cartanSubalgebra_normalizer_eq_self B A h2.out

end

end Matrix.ShellLieAlgebra
