/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.TensorProduct.Unit
public import TauCeti.RingTheory.Huber.Pair.Finite.Basic
import Mathlib.RingTheory.TensorProduct.Finite

/-!
# Plus rings of finite completed tensor products

For a finite algebra `B` over `A` whose base change `C ⊗[A] B` is naturally complete over `C`,
`TauCeti.Huber.Pair.finiteAlgebra.map_plus_baseChangeEquiv` shows that
`CompletedTensor.baseChangeEquiv` carries the integral-closure plus ring onto the completed tensor
plus ring.

Finiteness of the coprojection `(C, C⁺) → (C, C⁺) ⊗̂_A (B, B⁺)` as a morphism of Huber pairs
constrains the plus ring `B⁺` of the other factor. The completed tensor plus ring contains the
image of `B⁺`, and a finite morphism makes it integral over the image of `C⁺`. When the
coprojection is injective, every element of `A` landing in `B⁺` therefore lands in the integrally
closed `C⁺` (`Pair.completedTensor.algebraMap_mem_plus_of_isFinite_inl`).

Over the base itself, with `B = C = A` complete and Hausdorff, the coprojection
`(A, A⁺₁) → (A, A⁺₁) ⊗̂_A (A, A⁺₂)` is finite only if `A⁺₂ ≤ A⁺₁`
(`Pair.completedTensor.plus_le_of_isFinite_inl_self`), and when `A⁺₁ ≤ A⁺₂` the right unit
carries the completed tensor plus ring onto `A⁺₂` (`Pair.completedTensor.rightUnitor_plus_self`
in `TauCeti.RingTheory.Huber.TensorProduct.Unit`). So for `A⁺₁ ⊊ A⁺₂` the completed tensor
product is `(A, A⁺₂)` and the coprojection is the identity ring map `(A, A⁺₁) → (A, A⁺₂)`, which is
not finite. This is why finite étale base change of Huber pairs uses the integral-closure plus
ring on the finite étale factor (`Pair.completedTensor.isFiniteEtale_inl`).

## Main results

* `TauCeti.Huber.Pair.completedTensor.algebraMap_mem_plus_of_isFinite_inl`: if the coprojection
  from `(C, C⁺)` is finite and injective, then `a ∈ A` with image in `B⁺` has image in `C⁺`.
* `TauCeti.Huber.Pair.completedTensor.plus_le_of_isFinite_inl_self`: over the base, a finite
  coprojection forces `A⁺₂ ≤ A⁺₁`.
* `TauCeti.Huber.Pair.finiteAlgebra.map_plus_baseChangeEquiv`: `CompletedTensor.baseChangeEquiv`
  transports the integral-closure plus ring of `C ⊗[A] B` onto the completed tensor plus ring.

## References

* K. S. Kedlaya and R. Liu, *Relative p-adic Hodge theory: foundations*, Astérisque 371 (2015),
  §2.4, Remark 2.4.2 and (2.4.3.1).
-/

public section

open TensorProduct Algebra.TensorProduct

namespace TauCeti.Huber.Pair.completedTensor

section General

variable {A B C : Type*} [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]
  [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
  [IsTopologicalRing A] [IsTopologicalRing B] [IsTopologicalRing C]
  [IsHuberRing B] [IsHuberRing C]
  [IsAdicHom (algebraMap A B)] [IsAdicHom (algebraMap A C)]
  {T : Pair C} {U : Pair B}

/-- **A finite injective coprojection pulls the other factor's plus ring back into its own.** If
`(C, C⁺) → (C, C⁺) ⊗̂_A (B, B⁺)` is a finite morphism of Huber pairs with injective ring map, then
every `a : A` whose image lies in `B⁺` has image in `C⁺`: its image in the completed tensor plus
ring is integral over the image of `C⁺`, and `C⁺` is integrally closed in `C`. -/
theorem algebraMap_mem_plus_of_isFinite_inl (h : (inl A T U).IsFinite)
    (hinj : Function.Injective (CompletedTensor.inl A C B)) {a : A}
    (ha : algebraMap A B a ∈ U.plus) : algebraMap A C a ∈ T.plus := by
  refine h.mem_plus_of_injective (by rwa [toRingHom_inl]) ?_
  rw [toRingHom_inl, CompletedTensor.inl_algebraMap, ← CompletedTensor.inr_algebraMap]
  exact T.inr_mem_completedTensor_plus U ha

end General

section Self

variable {A : Type*} [CommRing A] [UniformSpace A] [IsUniformAddGroup A] [IsTopologicalRing A]
  [IsHuberRing A] [CompleteSpace A] [T2Space A] {S T : Pair A}

/-- **Over the base, a finite coprojection does not enlarge the plus ring.** For two Huber pairs
`(A, A⁺₁)` and `(A, A⁺₂)` on the same complete Hausdorff ring, if the coprojection
`(A, A⁺₁) → (A, A⁺₁) ⊗̂_A (A, A⁺₂)` is finite then `A⁺₂ ≤ A⁺₁`. -/
theorem plus_le_of_isFinite_inl_self (h : (inl A S T).IsFinite) : T.plus ≤ S.plus := fun _ ha ↦
  algebraMap_mem_plus_of_isFinite_inl h
    (Function.LeftInverse.injective (CompletedTensor.rightUnitor_inl A A)) ha

end Self

end TauCeti.Huber.Pair.completedTensor

namespace TauCeti.Huber.Pair.finiteAlgebra

attribute [local instance] CompletedTensor.leftAlgebra

/-- The natural module topology on the finite base change. -/
noncomputable local instance tensorModuleTopology (A C B : Type*) [CommRing A] [CommRing C]
    [CommRing B] [Algebra A C] [Algebra A B] [TopologicalSpace C] :
    TopologicalSpace (C ⊗[A] B) :=
  moduleTopology C (C ⊗[A] B)

local instance (A C B : Type*) [CommRing A] [CommRing C] [CommRing B] [Algebra A C] [Algebra A B]
    [Module.Finite A B] [TopologicalSpace C] [IsTopologicalRing C] :
    IsTopologicalRing (C ⊗[A] B) :=
  let := tensorModuleTopology A C B
  IsModuleTopology.isTopologicalRing C _

local instance (A C B : Type*) [CommRing A] [CommRing C] [CommRing B] [Algebra A C] [Algebra A B]
    [Module.Finite A B] [TopologicalSpace C] [IsTopologicalRing C] [IsHuberRing C] :
    IsHuberRing (C ⊗[A] B) :=
  let := tensorModuleTopology A C B
  IsHuberRing.of_isModuleTopology (A := C)

/-- The comparison transports the integral-closure plus ring of the finite base change
onto the completed tensor plus ring. No uniformity or sheafiness hypothesis is needed. -/
theorem map_plus_baseChangeEquiv {A C B : Type*} [CommRing A] [CommRing C] [CommRing B]
    [Algebra A C] [Algebra A B]
    [TopologicalSpace A] [IsTopologicalRing A] [IsHuberRing A]
    [TopologicalSpace C] [IsTopologicalRing C] [IsHuberRing C]
    [TopologicalSpace B] [IsTopologicalRing B] [IsHuberRing B]
    [IsModuleTopology A B] [Module.Finite A B]
    [IsAdicHom (algebraMap A C)] [IsAdicHom (algebraMap A B)]
    (h : IsNaturallyComplete C (C ⊗[A] B))
    (S : Pair A) (T : Pair C) (f : Pair.Hom S T) (hf : f.toRingHom = algebraMap A C) :
    let := tensorModuleTopology A C B
    (T.finiteAlgebra (C ⊗[A] B)).plus.map (CompletedTensor.baseChangeEquiv A C B h).toRingHom =
      (T.completedTensor A (S.finiteAlgebra B)).plus := by
  let := tensorModuleTopology A C B
  let : UniformSpace (C ⊗[A] B) := IsTopologicalAddGroup.rightUniformSpace _
  have : IsUniformAddGroup (C ⊗[A] B) := isUniformAddGroup_of_addCommGroup
  have : CompleteSpace (C ⊗[A] B) := (isNaturallyComplete_iff.mp h).1
  have : T2Space (C ⊗[A] B) := (isNaturallyComplete_iff.mp h).2
  let hleft := Pair.completedTensor.inl A T (S.finiteAlgebra B)
  let hforward := Pair.finiteAlgebra.lift hleft
    (by simp [hleft, CompletedTensor.algebraMap_leftAlgebra])
    (CompletedTensor.baseChangeEquiv A C B h).toAlgHom
  let hright := Pair.finiteAlgebra.lift
    ((Pair.finiteAlgebra.algebraHom T (C ⊗[A] B)).comp f)
    (by ext a; simp [hf, IsScalarTower.algebraMap_apply A C (C ⊗[A] B)])
    (includeRight : B →ₐ[A] C ⊗[A] B)
  let hback := Pair.completedTensor.lift (A := A)
    (Pair.finiteAlgebra.algebraHom T (C ⊗[A] B)) hright
    (by ext a; simp [hright])
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    simpa [hforward] using hforward.map_mem_plus x hx
  · intro x hx
    refine ⟨(CompletedTensor.baseChangeEquiv A C B h).symm x, ?_,
      (CompletedTensor.baseChangeEquiv A C B h).apply_symm_apply x⟩
    have hcont : Continuous (CompletedTensor.baseChangeEquiv A C B h).symm :=
      ((CompletedTensor.baseChangeEquiv A C B h).toEquiv.isHomeomorph_iff.mp
        (CompletedTensor.isHomeomorph_baseChangeEquiv A C B h)).2
    have hmap : hback.toRingHom = (CompletedTensor.baseChangeEquiv A C B h).symm.toRingHom := by
      apply CompletedTensor.hom_ext hback.continuous_toRingHom hcont
      · ext c
        simp [hback]
      · ext b
        simp [hback, hright]
    have hx' : (CompletedTensor.baseChangeEquiv A C B h).symm x = hback.toRingHom x :=
      (RingHom.congr_fun hmap x).symm
    rw [hx']
    exact hback.map_mem_plus x hx

end TauCeti.Huber.Pair.finiteAlgebra
