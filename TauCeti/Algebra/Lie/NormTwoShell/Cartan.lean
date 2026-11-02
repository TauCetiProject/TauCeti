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
theorem baseChangeBasis_repr_cartan_lie_inl (h : I → ℤ)
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
theorem baseChangeBasis_repr_cartan_lie_inr (h : I → ℤ)
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

private theorem lie_eq_zero_of_mem_cartanSpan {x y : A ⊗[ℤ] ShellLieAlgebra B}
    (hx : x ∈ Submodule.span A (Set.range fun i : I =>
      ((basis B).baseChange A) (.inl i)))
    (hy : y ∈ Submodule.span A (Set.range fun i : I =>
      ((basis B).baseChange A) (.inl i))) : ⁅x, y⁆ = 0 := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨j, rfl⟩ := hy
      simp [Basis.baseChange_apply]
    | zero => exact _root_.lie_zero (((basis B).baseChange A) (.inl i))
    | add y z _ _ hy hz =>
      rw [_root_.lie_add (((basis B).baseChange A) (.inl i)) y z, hy, hz, add_zero]
    | smul c y _ hy =>
      rw [_root_.lie_smul c (((basis B).baseChange A) (.inl i)) y, hy, smul_zero]
  | zero => exact _root_.zero_lie _
  | add x z _ _ hx hz => rw [_root_.add_lie, hx, hz, add_zero]
  | smul c x _ hx => rw [_root_.smul_lie, hx, smul_zero]

/-- The abelian subalgebra spanned by the scalar-extended integral Cartan vectors. -/
def cartanSubalgebra : LieSubalgebra A (A ⊗[ℤ] ShellLieAlgebra B) :=
  { Submodule.span A (Set.range fun i : I =>
      ((basis B).baseChange A) (.inl i)) with
    lie_mem' := by
      intro x y hx hy
      rw [lie_eq_zero_of_mem_cartanSpan B A hx hy]
      exact Submodule.zero_mem _ }

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
  -- Membership ignores the bracket-closure proof in the subalgebra constructor.
  change x ∈ Submodule.span A (Set.range fun i : I =>
    ((basis B).baseChange A) (.inl i)) ↔ _
  rw [hs, Basis.mem_span_image]
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

/-- Cartan elements commute after scalar extension. -/
theorem lie_eq_zero_of_mem_cartanSubalgebra {x y : A ⊗[ℤ] ShellLieAlgebra B}
    (hx : x ∈ cartanSubalgebra B A) (hy : y ∈ cartanSubalgebra B A) : ⁅x, y⁆ = 0 :=
  lie_eq_zero_of_mem_cartanSpan B A hx hy

instance : IsLieAbelian (cartanSubalgebra B A) where
  trivial x y := Subtype.ext (lie_eq_zero_of_mem_cartanSubalgebra B A x.2 y.2)

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
  rw [baseChangeBasis_repr_cartan_lie_inr, mem_normTwoShell.mp a.2] at hz
  rw [← Int.cast_smul_eq_zsmul A, Int.cast_ofNat, smul_eq_mul] at hz
  exact h2.left (by simpa only [mul_zero] using hz)

/-- The scalar-extended Cartan span is a Cartan subalgebra whenever two is regular. -/
instance [h2 : Fact (IsRegular (2 : A))] :
    (cartanSubalgebra B A).IsCartanSubalgebra where
  nilpotent := inferInstance
  self_normalizing := cartanSubalgebra_normalizer_eq_self B A h2.out

end

end Matrix.ShellLieAlgebra
