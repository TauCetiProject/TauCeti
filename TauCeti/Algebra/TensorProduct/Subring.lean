/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Flat.Domain
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Tensor squares of subrings

This file defines the canonical map from the integral tensor square of a subring of an algebra
to the tensor square of the ambient algebra, together with its range and basic membership lemmas.

## Main definitions and results

* `Subring.tensorSquareMap`: the canonical map from the integral tensor square.
* `Subring.tensorSquareMap_injective_of_flat`: the canonical map is injective when the subring is
  flat over `ℤ` and the base ring acts compatibly on the integral tensor square.
* `Subring.tensorSquareMap_injective`: over a rational algebra, the canonical map is
  injective.
* `Subring.tensorSquareRange`: the range of the canonical map.
* `Subring.tensorSquareEquivRange`: over a rational algebra, the canonical equivalence
  onto that range.
* `Subring.mem_tensorSquareRange_iff`: membership in the range in terms of a preimage.
* `Subring.tmul_mem_tensorSquareRange`: pure tensors of subring elements lie in the range.
-/

public section

open scoped TensorProduct

section

universe u v

variable (R : Type u) {A : Type v} [CommRing R] [Ring A] [Algebra R A]

/-- The canonical map from the integral tensor square of a subring to the tensor square of the
ambient algebra. On pure tensors, it applies the subring inclusion in both factors. -/
noncomputable def _root_.Subring.tensorSquareMap (S : Subring A) : S ⊗[ℤ] S →ₐ[ℤ] A ⊗[R] A :=
  Algebra.TensorProduct.lift
    ((Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] A).restrictScalars ℤ |>.comp
      S.subtype.toIntAlgHom)
    ((Algebra.TensorProduct.includeRight : A →ₐ[R] A ⊗[R] A).restrictScalars ℤ |>.comp
      S.subtype.toIntAlgHom)
    fun x y => by
      simp only [AlgHom.comp_apply, RingHom.toIntAlgHom_apply, Subring.coe_subtype]
      exact (Commute.one_right _).tmul (Commute.one_left _)

/-- The canonical tensor-square map sends a pure tensor to the pure tensor of the underlying
ambient elements. -/
@[simp]
theorem _root_.Subring.tensorSquareMap_tmul (S : Subring A) (x y : S) :
    Subring.tensorSquareMap R S (x ⊗ₜ[ℤ] y) = (x : A) ⊗ₜ[R] (y : A) := by
  simp [Subring.tensorSquareMap]

/-- If a subring `S` of an `R`-algebra `A` is flat over `ℤ`, and `R`-scalars can be moved across
`A ⊗[ℤ] A`, then the canonical map from the integral tensor square of `S` to `A ⊗[R] A` is
injective. The second condition holds when `R` is `ℤ` or `ℚ`, and for a localization of `ℤ` by
`IsLocalization.tensorProduct_compatibleSMul`. -/
-- Composing with the canonical map `A ⊗[R] A → A ⊗[ℤ] A` gives the tensor square of the
-- inclusion of `S`, which is injective because `S` is flat over the domain `ℤ`.
theorem _root_.Subring.tensorSquareMap_injective_of_flat {R : Type u} [CommRing R] [Algebra R A]
    [TensorProduct.CompatibleSMul ℤ R A A] (S : Subring A) [Module.Flat ℤ S] :
    Function.Injective (Subring.tensorSquareMap R S) := by
  let f : S →ₗ[ℤ] A := S.subtype.toIntAlgHom.toLinearMap
  have hcomp : TensorProduct.mapOfCompatibleSMul ℤ R ℤ A A ∘ₗ
      (Subring.tensorSquareMap R S).toLinearMap = TensorProduct.map f f :=
    TensorProduct.ext' fun x y => by simp [f]
  refine .of_comp (f := TensorProduct.mapOfCompatibleSMul ℤ R ℤ A A) ?_
  rw [← AlgHom.coe_toLinearMap, ← LinearMap.coe_comp, hcomp]
  exact TensorProduct.map_injective_of_flat_flat_of_isDomain f f
    S.subtype_injective S.subtype_injective

section Rational

variable {A : Type v} [Ring A] [Algebra ℚ A]

/-- The canonical map from the integer tensor square of a subring of a rational algebra to the
rational tensor square of the ambient algebra is injective. -/
-- The subring is torsion-free as an abelian group because it embeds in a rational vector space,
-- hence flat over `ℤ`.
theorem _root_.Subring.tensorSquareMap_injective (S : Subring A) :
    Function.Injective (Subring.tensorSquareMap ℚ S) := by
  have : HasUniqueDiv A := .of_module_rat A
  have : HasUniqueDiv S :=
    Function.Injective.hasUniqueDiv S.subtype.toAddMonoidHom S.subtype_injective
  exact S.tensorSquareMap_injective_of_flat

end Rational

/-- The range of the canonical map from the integral tensor square of a subring to the tensor
square of the ambient algebra. -/
noncomputable def _root_.Subring.tensorSquareRange (S : Subring A) : Subring (A ⊗[R] A) :=
  (Subring.tensorSquareMap R S).toRingHom.range

/-- Membership in the tensor-square range is equivalent to having an integral tensor preimage. -/
@[simp]
theorem _root_.Subring.mem_tensorSquareRange_iff (S : Subring A) (z : A ⊗[R] A) :
    z ∈ Subring.tensorSquareRange R S ↔ ∃ t : S ⊗[ℤ] S, Subring.tensorSquareMap R S t = z := by
  rfl

/-- A pure tensor whose two factors lie in a subring belongs to its tensor-square range. -/
theorem _root_.Subring.tmul_mem_tensorSquareRange (S : Subring A) {x y : A} (hx : x ∈ S)
    (hy : y ∈ S) :
    x ⊗ₜ[R] y ∈ Subring.tensorSquareRange R S := by
  rw [Subring.mem_tensorSquareRange_iff]
  exact ⟨(⟨x, hx⟩ : S) ⊗ₜ[ℤ] (⟨y, hy⟩ : S), Subring.tensorSquareMap_tmul R S _ _⟩

section RationalRange

variable {A : Type v} [Ring A] [Algebra ℚ A]

/-- The canonical equivalence from the integer tensor square of a subring of a rational algebra
onto its range in the rational tensor square. -/
noncomputable def _root_.Subring.tensorSquareEquivRange (S : Subring A) :
    S ⊗[ℤ] S ≃ₐ[ℤ] Subring.tensorSquareRange ℚ S :=
  AlgEquiv.ofInjective (Subring.tensorSquareMap ℚ S) (Subring.tensorSquareMap_injective S)

/-- The equivalence onto the tensor-square range acts by the canonical tensor-square map. -/
@[simp]
theorem _root_.Subring.coe_tensorSquareEquivRange_apply (S : Subring A) (t : S ⊗[ℤ] S) :
    (Subring.tensorSquareEquivRange S t : A ⊗[ℚ] A) = Subring.tensorSquareMap ℚ S t :=
  AlgEquiv.ofInjective_apply (Subring.tensorSquareMap ℚ S) (Subring.tensorSquareMap_injective S) t

end RationalRange

end
