/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Preprojective.ADE.TypeA.Basis

/-!
# A global basis of the type-`A` preprojective algebra

The bounded valleys in all vertex corners together form a basis of the signless preprojective
algebra of `Aₙ`. The existing corner bases are assembled by projecting an arbitrary algebra
element into each source-target corner and using the orthogonality and completeness of the
vertex idempotents. In particular, the algebra is finite-dimensional over every field.

This global basis is the coordinate system needed to define and calculate the longest-valley
Frobenius functional in the proof of self-injectivity.

## References

* C. M. Ringel, *The preprojective algebra of a quiver*, for the finite-dimensionality and
  self-injectivity of preprojective algebras of finite Dynkin type.
* The corner valley bases used here are developed in
  `TauCeti.RepresentationTheory.Quiver.Preprojective.ADE.TypeA`.
-/

public section

namespace TauCeti

open _root_.Quiver PathAlgebra DoubledQuiver

variable (k : Type*) [Field k] {n : ℕ}

attribute [local instance] finiteNeighborSetFintype

local notation "AG" => diagramGraph (DynkinType.cartanMatrix (DynkinType.A n))
local notation "Q" => DoubledQuiver AG
local notation "Π" => signlessPreprojectiveAlgebra k Q
local notation "π" => signlessPreprojectiveMk k Q
local notation "e" => fun a : Fin (DynkinType.A n).rank =>
  π (vertexIdempotent k (vertex AG a))

/-- An index for the global valley basis of the signless type-`A` preprojective algebra:
source, target, and a bottom within the bounded interval for that corner. -/
abbrev PreprojectiveABasisIndex (n : ℕ) :=
  Σ a : Fin (DynkinType.A n).rank, Σ b : Fin (DynkinType.A n).rank,
    ↥(Finset.Icc (a.val + b.val + 1 - n) (min a.val b.val))

/-- The family of all bounded valleys in all corners of the signless type-`A` preprojective
algebra. -/
noncomputable def signlessPreprojectiveABasisFun : PreprojectiveABasisIndex n → Π
  | ⟨a, b, m⟩ => signlessPreprojectiveAValley k a b m

@[simp]
theorem signlessPreprojectiveABasisFun_apply
    (i : PreprojectiveABasisIndex n) :
    signlessPreprojectiveABasisFun k i =
      signlessPreprojectiveAValley k i.1 i.2.1 i.2.2 := by
  rfl

private theorem vertex_mul_mul_mem_corner (a b : Fin (DynkinType.A n).rank) (x : Π) :
    e b * x * e a ∈ cornerSubmodule k (e b) (e a) := by
  have hid (i : Fin (DynkinType.A n).rank) : IsIdempotentElem (e i) :=
    IsIdempotentElem.map (vertexIdempotent_mul_self (k := k) (vertex AG i)) π
  rw [mem_cornerSubmodule_iff k (hid b) (hid a)]
  calc
    e b * (e b * x * e a) * e a = (e b * e b) * x * (e a * e a) := by
      simp only [mul_assoc]
    _ = e b * x * e a := by rw [(hid b).eq, (hid a).eq]

private noncomputable def signlessPreprojectiveACornerProjection
    (a b : Fin (DynkinType.A n).rank) : Π →ₗ[k] cornerSubmodule k (e b) (e a) :=
  { toFun := fun x => ⟨e b * x * e a, vertex_mul_mul_mem_corner k a b x⟩
    map_add' := fun x y => by ext; simp only [mul_add, add_mul, Submodule.coe_add]
    map_smul' := fun c x => by
      ext
      simp only [RingHom.id_apply, Submodule.coe_smul, mul_smul_comm, smul_mul_assoc] }

@[simp]
private theorem coe_signlessPreprojectiveACornerProjection_apply
    (a b : Fin (DynkinType.A n).rank) (x : Π) :
    (signlessPreprojectiveACornerProjection k a b x : Π) = e b * x * e a := by
  rfl

private noncomputable def signlessPreprojectiveAGlobalCoord
    (i : PreprojectiveABasisIndex n) : Π →ₗ[k] k :=
  (signlessPreprojectiveACornerBasis k i.1 i.2.1).coord i.2.2 ∘ₗ
    signlessPreprojectiveACornerProjection k i.1 i.2.1

private theorem cornerProjection_valley
    (a b c d : Fin (DynkinType.A n).rank) (m : ℕ) :
    (signlessPreprojectiveACornerProjection k a b
        (signlessPreprojectiveAValley k c d m) : Π) =
      if a = c ∧ b = d then signlessPreprojectiveAValley k c d m else 0 := by
  classical
  simp only [coe_signlessPreprojectiveACornerProjection_apply]
  have hid (i : Fin (DynkinType.A n).rank) : IsIdempotentElem (e i) :=
    IsIdempotentElem.map (vertexIdempotent_mul_self (k := k) (vertex AG i)) π
  have hx := signlessPreprojectiveAValley_mem_cornerSubmodule k c d m
  by_cases hac : a = c
  · subst c
    by_cases hbd : b = d
    · subst d
      simp only [true_and, ite_true, mul_eq_self_of_mem_cornerSubmodule (hid b) hx,
        mul_eq_self_of_mem_cornerSubmodule_right (hid a) hx]
    · have horth : e b * e d = 0 := by
        rw [← map_mul, vertexIdempotent_mul_vertexIdempotent_of_ne
          (fun h => hbd (vertex_injective AG h)), map_zero]
      rw [ite_eq_right (not_and_of_not_right _ hbd)]
      calc
        e b * signlessPreprojectiveAValley k a d m * e a =
            e b * (e d * signlessPreprojectiveAValley k a d m) * e a :=
          congrArg (fun y => e b * y * e a)
            (mul_eq_self_of_mem_cornerSubmodule (hid d) hx).symm
        _ = (e b * e d) * signlessPreprojectiveAValley k a d m * e a := by
          simp only [mul_assoc]
        _ = 0 := by rw [horth, zero_mul, zero_mul]
  · have horth : e c * e a = 0 := by
      rw [← map_mul, vertexIdempotent_mul_vertexIdempotent_of_ne
        (fun h => hac (vertex_injective AG h).symm), map_zero]
    rw [ite_eq_right (not_and_of_not_left _ hac)]
    calc
      e b * signlessPreprojectiveAValley k c d m * e a =
          e b * (signlessPreprojectiveAValley k c d m * e c) * e a := by
        rw [mul_eq_self_of_mem_cornerSubmodule_right (hid c) hx]
      _ = e b * signlessPreprojectiveAValley k c d m * (e c * e a) := by
        simp only [mul_assoc]
      _ = 0 := by simp only [horth, mul_zero]

@[simp]
private theorem signlessPreprojectiveAGlobalCoord_valley
    (i j : PreprojectiveABasisIndex n) :
    signlessPreprojectiveAGlobalCoord k i
        (signlessPreprojectiveAValley k j.1 j.2.1 j.2.2) =
      if j = i then 1 else 0 := by
  classical
  rcases i with ⟨a, b, m⟩
  rcases j with ⟨c, d, l⟩
  simp only [signlessPreprojectiveAGlobalCoord, LinearMap.coe_comp, Function.comp_apply]
  by_cases h : a = c ∧ b = d
  · rcases h with ⟨rfl, rfl⟩
    have hp : signlessPreprojectiveACornerProjection k a b
        (signlessPreprojectiveAValley k a b l) =
        signlessPreprojectiveACornerBasis k a b l := by
      apply Subtype.ext
      rw [cornerProjection_valley]
      simp only [and_self, ite_true, coe_signlessPreprojectiveACornerBasis_apply]
    rw [hp, Module.Basis.coord_apply, Module.Basis.repr_self_apply]
    by_cases hl : l = m
    · subst l
      simp only [ite_true]
    · rw [ite_eq_right hl, ite_eq_right]
      intro hji
      apply hl
      apply Subtype.ext
      exact congrArg (fun x : PreprojectiveABasisIndex n => x.2.2.val) hji
  · have hp : signlessPreprojectiveACornerProjection k a b
        (signlessPreprojectiveAValley k c d l) = 0 := by
      apply Subtype.ext
      rw [cornerProjection_valley, ite_eq_right h]
      rfl
    rw [hp, map_zero]
    rw [ite_eq_right]
    intro hji
    apply h
    exact ⟨Fin.ext (congrArg (fun x : PreprojectiveABasisIndex n => x.1.val) hji).symm,
      Fin.ext (congrArg (fun x : PreprojectiveABasisIndex n => x.2.1.val) hji).symm⟩

/-- The global bounded-valley family is linearly independent. -/
theorem linearIndependent_signlessPreprojectiveABasisFun :
    LinearIndependent k (signlessPreprojectiveABasisFun k : PreprojectiveABasisIndex n → Π) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  have hcoord := congrArg (signlessPreprojectiveAGlobalCoord k i) hc
  rw [map_sum] at hcoord
  simp only [map_smul, signlessPreprojectiveABasisFun_apply,
    signlessPreprojectiveAGlobalCoord_valley, map_zero, smul_eq_mul] at hcoord
  simpa using hcoord

private theorem sum_vertexIdempotent_eq_one :
    ∑ a : Fin (DynkinType.A n).rank, e a = 1 := by
  classical
  calc
    ∑ a, e a = π (∑ a, vertexIdempotent k (vertex AG a)) := by rw [map_sum]
    _ = π (∑ v : Q, vertexIdempotent k v) := by
      congr 1
      simpa only [vertexEquiv_apply] using
        (vertexEquiv AG).sum_comp (fun v => vertexIdempotent k v)
    _ = π 1 := by rw [PathAlgebra.one_def]
    _ = 1 := map_one π

/-- The global bounded-valley family spans the signless type-`A` preprojective algebra. -/
theorem span_range_signlessPreprojectiveABasisFun_eq_top :
    Submodule.span k (Set.range
      (signlessPreprojectiveABasisFun k : PreprojectiveABasisIndex n → Π)) = ⊤ := by
  classical
  rw [eq_top_iff]
  intro x _
  have hcorner (a b : Fin (DynkinType.A n).rank) :
      e b * x * e a ∈ Submodule.span k (Set.range
        (signlessPreprojectiveABasisFun k : PreprojectiveABasisIndex n → Π)) := by
    let z : cornerSubmodule k (e b) (e a) :=
      signlessPreprojectiveACornerProjection k a b x
    rw [← coe_signlessPreprojectiveACornerProjection_apply]
    change (z : Π) ∈ Submodule.span k (Set.range
      (signlessPreprojectiveABasisFun k : PreprojectiveABasisIndex n → Π))
    rw [← (signlessPreprojectiveACornerBasis k a b).sum_repr z]
    simp only [Submodule.coe_sum, Submodule.coe_smul]
    exact Submodule.sum_mem _ fun m _ => Submodule.smul_mem _ _
      (Submodule.subset_span ⟨⟨a, b, m⟩, by
        simp only [signlessPreprojectiveABasisFun_apply,
          coe_signlessPreprojectiveACornerBasis_apply]⟩)
  have hxsum : x = ∑ a, ∑ b, e b * x * e a := by
    calc
      x = 1 * x * 1 := by rw [one_mul, mul_one]
      _ = (∑ b, e b) * x * (∑ a, e a) := by
        simp only [sum_vertexIdempotent_eq_one]
      _ = ∑ a, ∑ b, e b * x * e a := by
        simp only [Finset.sum_mul, Finset.mul_sum]
  rw [hxsum]
  exact Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun b _ => hcorner a b

/-- The basis of the signless type-`A` preprojective algebra consisting of all bounded valleys. -/
noncomputable def signlessPreprojectiveABasis :
    Module.Basis (PreprojectiveABasisIndex n) k Π :=
  Module.Basis.mk (linearIndependent_signlessPreprojectiveABasisFun k)
    (span_range_signlessPreprojectiveABasisFun_eq_top k).ge

@[simp]
theorem signlessPreprojectiveABasis_apply (i : PreprojectiveABasisIndex n) :
    signlessPreprojectiveABasis k i = signlessPreprojectiveABasisFun k i :=
  Module.Basis.mk_apply _ _ _

/-- The dimension of the signless type-`A` preprojective algebra is the number of bounded
valleys across all source-target corners. -/
theorem finrank_signlessPreprojectiveAlgebra_A :
    Module.finrank k Π = Fintype.card (PreprojectiveABasisIndex n) :=
  Module.finrank_eq_card_basis (signlessPreprojectiveABasis k)

end TauCeti
