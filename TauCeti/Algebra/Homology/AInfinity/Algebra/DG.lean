/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.AInfinity.Algebra.Hom.Strict
public import TauCeti.Algebra.Homology.DG.Algebra.Hom.Basic

/-!
# Differential graded algebras as `A∞` algebras

A nonunital differential graded algebra `(A, d)` is an `A∞` algebra with `m₁ = d`, `m₂` the
product, and `m n = 0` for `n ≥ 3`.  The arity-one and arity-two Stasheff identities are `d² = 0`
and the graded Leibniz rule, the arity-three identity is associativity, and every identity of arity
at least four vanishes term by term, because each of its terms contains an operation of arity at
least three.  No unit is needed for any of this, and a morphism of nonunital DG algebras is a
strict `A∞` morphism.  For a unital DG algebra the unit is moreover a strict unit, and a morphism
of DG algebras is a strictly unital strict `A∞` morphism.

The nonunital generality matters because cohomology algebras need not be unital: the cohomology
of an `A∞` algebra is only a graded nonunital algebra, and it becomes an `A∞` algebra, with zero
unary operation, through `TauCeti.isNonUnitalDGAlgebra_zero`.

Conversely, an `A∞` algebra structure on a graded nonunital algebra whose binary operation is the
product makes its unary operation a DG algebra differential.  If its higher operations vanish, it
is the `A∞` algebra of that DG algebra.  Thus nonunital DG algebras are exactly the `A∞` algebras
on graded nonunital algebras whose binary operation is the product and whose higher operations
vanish.

## Main definitions

* `TauCeti.IsNonUnitalDGAlgebra.toAInfinityAlgebra`: the `A∞` algebra of a nonunital DG algebra.
* `TauCeti.NonUnitalDGAlgHom.toAInfinityStrictHom`: a nonunital DG algebra morphism as a strict
  `A∞` morphism.
* `TauCeti.DGAlgHom.toAInfinityStrictUnitalHom`: a DG algebra morphism as a strictly unital
  strict `A∞` morphism.

## Main results

* `TauCeti.IsNonUnitalDGAlgebra.toAInfinityAlgebra_m_one_apply`,
  `toAInfinityAlgebra_m_two_apply`, and `toAInfinityAlgebra_m_of_three_le`: its operations are the
  differential, the product, and zero.
* `TauCeti.IsDGAlgebra.strictUnit_one`: the unit of a DG algebra is a strict unit.
* `TauCeti.AInfinityAlgebra.isNonUnitalDGAlgebra_differential` and
  `TauCeti.AInfinityAlgebra.isDGAlgebra_differential`: the unary operation of an `A∞` algebra
  whose binary operation is the product is a DG algebra differential.
* `TauCeti.AInfinityAlgebra.eq_toAInfinityAlgebra`: such an `A∞` algebra with vanishing higher
  operations is the `A∞` algebra of that DG algebra.

## References

* B. Keller, *Introduction to A-infinity algebras and modules*, Sections 3.1 and 3.4.
-/

public section

open _root_.MultilinearMap

namespace TauCeti

universe uR uA uB uC

section NonUnital

variable {R : Type uR} {A : Type uA} {B : Type uB} {C : Type uC} [CommRing R]
  [NonUnitalRing A] [Module R A] [IsScalarTower R A A] [SMulCommClass R A A]
  [NonUnitalRing B] [Module R B] [IsScalarTower R B B] [SMulCommClass R B B]
  [NonUnitalRing C] [Module R C] [IsScalarTower R C C] [SMulCommClass R C C]
  {𝒜 : ℤ → Submodule R A} {ℬ : ℤ → Submodule R B} {𝒞 : ℤ → Submodule R C}
  [SetLike.GradedMul 𝒜] [DirectSum.Decomposition 𝒜]
  [SetLike.GradedMul ℬ] [DirectSum.Decomposition ℬ]
  [SetLike.GradedMul 𝒞] [DirectSum.Decomposition 𝒞]
  {d : A →ₗ[R] A} {dA : A →ₗ[R] A} {dB : B →ₗ[R] B} {dC : C →ₗ[R] C}

namespace IsNonUnitalDGAlgebra

/-- The `A∞` operations of a differential `d` on an algebra: `m₁ = d`, `m₂` is the product, and all
other operations vanish. -/
private noncomputable def operation (d : A →ₗ[R] A) :
    ∀ n : ℕ, MultilinearMap R (fun _ : Fin n ↦ A) A
  | 0 => 0
  | 1 => MultilinearMap.ofSubsingleton R A A 0 d
  | 2 => (MultilinearMap.ofSubsingletonₗ R R A A (0 : Fin 1) ∘ₗ LinearMap.mul R A).uncurryLeft
  | _ + 3 => 0

private theorem operation_zero (d : A →ₗ[R] A) : operation d 0 = 0 := (rfl)

private theorem operation_one_apply (d : A →ₗ[R] A) (x : Fin 1 → A) :
    operation d 1 x = d (x 0) := (rfl)

private theorem operation_two_apply (d : A →ₗ[R] A) (x : Fin 2 → A) :
    operation d 2 x = x 0 * x 1 := by
  simp [operation, LinearMap.uncurryLeft_apply, Fin.tail]

private theorem operation_of_three_le (d : A →ₗ[R] A) {n : ℕ} (hn : 3 ≤ n) :
    operation d n = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn
  rfl

/-- The operation `operation d n` has degree `2 - n` when `d` raises degree by one. -/
private theorem isHomogeneous_operation (h : IsNonUnitalDGAlgebra 𝒜 d) (n : ℕ) :
    MultilinearMap.IsHomogeneous (operation d n) (fun _ ↦ 𝒜) 𝒜 (2 - n) := by
  rw [MultilinearMap.isHomogeneous_def]
  intro e x hx
  rcases n with _ | _ | _ | n
  · simp [operation_zero]
  · simpa [operation_one_apply] using h.map_mem (hx 0)
  · simpa [operation_two_apply] using SetLike.mul_mem_graded (hx 0) (hx 1)
  · simp [operation_of_three_le d (by omega : 3 ≤ n + 3)]

/-- The operations of a nonunital DG algebra satisfy every Stasheff identity on homogeneous
inputs. -/
private theorem stasheffSum_operation (h : IsNonUnitalDGAlgebra 𝒜 d) (n : ℕ) (e : ℕ → ℤ)
    (x : ℕ → A) (hx : ∀ i < n, x i ∈ 𝒜 (e i)) :
    AInfinity.stasheffSum (operation d) e x n = 0 := by
  match n, hx with
  | 0, _ => exact AInfinity.stasheffSum_zero _ _ _
  | 1, _ => simpa [AInfinity.stasheffSum_one, operation_one_apply] using h.sq_zero (x 0)
  | 2, hx =>
    rw [AInfinity.stasheffSum_two_eq_zero_iff]
    simpa [operation_one_apply, operation_two_apply, ← negOnePow_smul_eq_negOnePowCast_smul]
      using h.leibniz (hx 0 (by omega)) (x 1)
  | 3, _ =>
    rw [AInfinity.stasheffSum_three_eq_zero_iff_of_m_three_eq_zero _ _ _
      (operation_of_three_le d le_rfl)]
    simp [operation_two_apply, mul_assoc]
  | n + 4, _ =>
    -- Each term has an inner operation of arity `s` and an outer one of arity `n + 5 - s`, and
    -- one of them has arity at least three.
    rw [AInfinity.stasheffSum_def]
    refine Finset.sum_eq_zero fun p hp ↦ Finset.sum_eq_zero fun s hs ↦ ?_
    rw [Finset.mem_range] at hp
    rw [Finset.mem_Icc] at hs
    rw [AInfinity.stasheffTerm_def]
    rcases lt_or_ge s 3 with hs3 | hs3
    · rw [operation_of_three_le d (by omega : 3 ≤ p + 1 + (n + 4 - p - s)),
        evalNat_def, _root_.zero_apply, smul_zero]
    · have hinner : evalNat (operation d s) (fun j ↦ x (p + j)) = 0 := by
        rw [operation_of_three_le d hs3, evalNat_def, _root_.zero_apply]
      rw [hinner, evalNat_def, (operation d _).map_coord_zero
        (⟨p, by omega⟩ : Fin (p + 1 + (n + 4 - p - s))) (by simp), smul_zero]

/-- The `A∞` algebra of a nonunital DG algebra: `m₁ = d`, `m₂` is the product, and `m n = 0` for
`n ≥ 3`. -/
noncomputable def toAInfinityAlgebra (h : IsNonUnitalDGAlgebra 𝒜 d) : AInfinityAlgebra R A :=
  AInfinityAlgebra.ofStasheff (InternalGrading.ofDecomposition 𝒜) (operation d) (operation_zero d)
    (fun n _ ↦ by
      rw [InternalGrading.ofDecomposition_piece]
      exact isHomogeneous_operation h n)
    (AInfinity.suspensionTaylor _ _) (AInfinity.isSuspension_suspensionTaylor _ _)
    (fun n _ e x hx ↦ by
      rw [InternalGrading.ofDecomposition_piece] at hx
      exact stasheffSum_operation h n e x hx)

/-- The `A∞` algebra of a nonunital DG algebra carries the grading of the algebra. -/
@[simp]
theorem toAInfinityAlgebra_grading (h : IsNonUnitalDGAlgebra 𝒜 d) :
    h.toAInfinityAlgebra.grading = InternalGrading.ofDecomposition 𝒜 := by
  rw [toAInfinityAlgebra, AInfinityAlgebra.ofStasheff_grading]

/-- The unary operation of the `A∞` algebra of a nonunital DG algebra is the differential. -/
@[simp]
theorem toAInfinityAlgebra_m_one_apply (h : IsNonUnitalDGAlgebra 𝒜 d) (x : Fin 1 → A) :
    h.toAInfinityAlgebra.m 1 x = d (x 0) := by
  rw [toAInfinityAlgebra, AInfinityAlgebra.ofStasheff_m, operation_one_apply]

/-- The binary operation of the `A∞` algebra of a nonunital DG algebra is the product. -/
@[simp]
theorem toAInfinityAlgebra_m_two_apply (h : IsNonUnitalDGAlgebra 𝒜 d) (x : Fin 2 → A) :
    h.toAInfinityAlgebra.m 2 x = x 0 * x 1 := by
  rw [toAInfinityAlgebra, AInfinityAlgebra.ofStasheff_m, operation_two_apply]

/-- The operations of arity at least three of the `A∞` algebra of a nonunital DG algebra
vanish. -/
theorem toAInfinityAlgebra_m_of_three_le (h : IsNonUnitalDGAlgebra 𝒜 d) {n : ℕ} (hn : 3 ≤ n) :
    h.toAInfinityAlgebra.m n = 0 := by
  rw [toAInfinityAlgebra, AInfinityAlgebra.ofStasheff_m, operation_of_three_le d hn]

/-- The simp-normal form of `toAInfinityAlgebra_m_of_three_le`. -/
@[simp]
theorem toAInfinityAlgebra_m_add_three (h : IsNonUnitalDGAlgebra 𝒜 d) (n : ℕ) :
    h.toAInfinityAlgebra.m (n + 3) = 0 :=
  h.toAInfinityAlgebra_m_of_three_le (by omega)

/-- The differential of the `A∞` algebra of a nonunital DG algebra is the DG differential. -/
@[simp]
theorem toAInfinityAlgebra_differential (h : IsNonUnitalDGAlgebra 𝒜 d) :
    h.toAInfinityAlgebra.differential = d := by
  ext x
  simp

/-- The bilinear product of the `A∞` algebra of a nonunital DG algebra is the algebra
multiplication. -/
@[simp]
theorem toAInfinityAlgebra_mul (h : IsNonUnitalDGAlgebra 𝒜 d) :
    h.toAInfinityAlgebra.mul = LinearMap.mul R A := by
  ext x y
  simp

end IsNonUnitalDGAlgebra

namespace NonUnitalDGAlgHom

variable {hA : IsNonUnitalDGAlgebra 𝒜 dA} {hB : IsNonUnitalDGAlgebra ℬ dB}
  {hC : IsNonUnitalDGAlgebra 𝒞 dC}

/-- A morphism of nonunital DG algebras is a strict morphism of their `A∞` algebras. -/
noncomputable def toAInfinityStrictHom (f : NonUnitalDGAlgHom hA hB) :
    AInfinityStrictHom hA.toAInfinityAlgebra hB.toAInfinityAlgebra where
  toLinearMap := (f : A →ₗ[R] B)
  map_mem' ha := by simpa using GradedFunLike.map_mem f (by simpa using ha)
  map_m' n := by
    ext x
    rcases n with _ | _ | _ | n <;> simp

/-- The strict `A∞` morphism of a nonunital DG algebra morphism has the same underlying
function. -/
@[simp]
theorem coe_toAInfinityStrictHom (f : NonUnitalDGAlgHom hA hB) :
    ⇑f.toAInfinityStrictHom = f := (rfl)

/-- The identity nonunital DG algebra morphism gives the identity strict `A∞` morphism. -/
@[simp]
theorem toAInfinityStrictHom_id :
    (NonUnitalDGAlgHom.id hA).toAInfinityStrictHom = AInfinityStrictHom.id _ := by
  ext a
  simp

/-- Passing from nonunital DG algebra morphisms to strict `A∞` morphisms preserves
composition. -/
@[simp]
theorem toAInfinityStrictHom_comp (g : NonUnitalDGAlgHom hB hC) (f : NonUnitalDGAlgHom hA hB) :
    (g.comp f).toAInfinityStrictHom = g.toAInfinityStrictHom.comp f.toAInfinityStrictHom := by
  ext a
  simp

end NonUnitalDGAlgHom

namespace AInfinityAlgebra

/-- If the binary operation of an `A∞` algebra structure on a graded nonunital algebra is the
product, its unary operation is a nonunital DG algebra differential. -/
theorem isNonUnitalDGAlgebra_differential (𝒜' : AInfinityAlgebra R A)
    (hG : 𝒜'.grading = InternalGrading.ofDecomposition 𝒜) (hm₂ : ∀ a b, 𝒜'.m 2 ![a, b] = a * b) :
    IsNonUnitalDGAlgebra 𝒜 𝒜'.differential where
  map_mem {p a} ha := by
    have := (𝒜'.m_degree 1 one_pos).map_mem (fun _ ↦ p) ![a] fun _ ↦ by simpa [hG] using ha
    simpa [hG, add_comm] using this
  sq_zero a := by simpa using 𝒜'.stasheff_arity_one a
  leibniz {p a} ha b := by
    have := 𝒜'.stasheff_arity_two a b p (by simpa [hG] using ha)
    simpa [hm₂, ← negOnePow_smul_eq_negOnePowCast_smul] using this

/-- An `A∞` algebra structure on a graded nonunital algebra whose binary operation is the product
and whose higher operations vanish is the `A∞` algebra of the nonunital DG algebra given by its
unary operation. -/
theorem eq_toAInfinityAlgebra (𝒜' : AInfinityAlgebra R A)
    (hG : 𝒜'.grading = InternalGrading.ofDecomposition 𝒜) (hm₂ : ∀ a b, 𝒜'.m 2 ![a, b] = a * b)
    (hm : ∀ n, 3 ≤ n → 𝒜'.m n = 0) :
    𝒜' = (𝒜'.isNonUnitalDGAlgebra_differential hG hm₂).toAInfinityAlgebra := by
  refine AInfinityAlgebra.ext
    (hG.trans (IsNonUnitalDGAlgebra.toAInfinityAlgebra_grading _).symm) (funext fun n ↦ ?_)
  rcases n with _ | _ | _ | n
  · simp
  · ext x
    rw [IsNonUnitalDGAlgebra.toAInfinityAlgebra_m_one_apply, differential_apply]
    congr 1
    funext i
    fin_cases i
    rfl
  · ext x
    rw [IsNonUnitalDGAlgebra.toAInfinityAlgebra_m_two_apply, ← hm₂]
    congr 1
    funext i
    fin_cases i <;> rfl
  · rw [IsNonUnitalDGAlgebra.toAInfinityAlgebra_m_add_three]
    exact hm (n + 3) (by omega)

end AInfinityAlgebra

end NonUnital

section Unital

variable {R : Type uR} {A : Type uA} {B : Type uB} {C : Type uC}
  [CommRing R] [Ring A] [Ring B] [Ring C]
  [Algebra R A] [Algebra R B] [Algebra R C]
  {𝒜 : ℤ → Submodule R A} {ℬ : ℤ → Submodule R B} {𝒞 : ℤ → Submodule R C}
  [GradedAlgebra 𝒜] [GradedAlgebra ℬ] [GradedAlgebra 𝒞]
  {d : A →ₗ[R] A} {dA : A →ₗ[R] A} {dB : B →ₗ[R] B} {dC : C →ₗ[R] C}

namespace IsDGAlgebra

/-- The unit of a DG algebra is a strict unit of its `A∞` algebra. -/
theorem strictUnit_one (h : IsDGAlgebra 𝒜 d) :
    h.toIsNonUnitalDGAlgebra.toAInfinityAlgebra.StrictUnit 1 where
  degree_zero := by simpa using SetLike.one_mem_graded 𝒜
  binary_left x := by simp
  binary_right x := by simp
  higher n hn x := by
    rintro ⟨i, hi⟩
    rcases n with _ | _ | _ | n
    · exact i.elim0
    · rw [Fin.fin_one_eq_zero i] at hi
      rw [IsNonUnitalDGAlgebra.toAInfinityAlgebra_m_one_apply, hi, h.map_one_eq_zero]
    · exact absurd rfl hn
    · simp

end IsDGAlgebra

namespace DGAlgHom

variable {hA : IsDGAlgebra 𝒜 dA} {hB : IsDGAlgebra ℬ dB} {hC : IsDGAlgebra 𝒞 dC}

/-- A morphism of DG algebras is a strictly unital strict morphism of their `A∞` algebras. -/
noncomputable def toAInfinityStrictUnitalHom (f : DGAlgHom hA hB) :
    AInfinityStrictUnitalHom hA.strictUnit_one hB.strictUnit_one where
  toAInfinityStrictHom := f.toNonUnitalDGAlgHom.toAInfinityStrictHom
  map_unit' := by simp

/-- The strict `A∞` morphism underlying a DG algebra morphism is that of the nonunital DG algebra
morphism obtained by forgetting units. -/
@[simp]
theorem toAInfinityStrictHom_toAInfinityStrictUnitalHom (f : DGAlgHom hA hB) :
    f.toAInfinityStrictUnitalHom.toAInfinityStrictHom =
      f.toNonUnitalDGAlgHom.toAInfinityStrictHom := (rfl)

/-- The `A∞` morphism of a DG algebra morphism has the same underlying function. -/
@[simp]
theorem coe_toAInfinityStrictUnitalHom (f : DGAlgHom hA hB) :
    ⇑f.toAInfinityStrictUnitalHom = f :=
  f.toNonUnitalDGAlgHom.coe_toAInfinityStrictHom.trans f.coe_toNonUnitalDGAlgHom

/-- The identity DG algebra morphism gives the identity `A∞` morphism. -/
@[simp]
theorem toAInfinityStrictUnitalHom_id :
    (DGAlgHom.id hA).toAInfinityStrictUnitalHom = AInfinityStrictUnitalHom.id _ := by
  ext a
  simp

/-- Passing from DG algebra morphisms to `A∞` morphisms preserves composition. -/
@[simp]
theorem toAInfinityStrictUnitalHom_comp (g : DGAlgHom hB hC) (f : DGAlgHom hA hB) :
    (g.comp f).toAInfinityStrictUnitalHom =
      g.toAInfinityStrictUnitalHom.comp f.toAInfinityStrictUnitalHom := by
  ext a
  simp

end DGAlgHom

namespace AInfinityAlgebra

/-- If the binary operation of an `A∞` algebra structure on a graded algebra is the product, its
unary operation is a DG algebra differential. -/
theorem isDGAlgebra_differential (𝒜' : AInfinityAlgebra R A)
    (hG : 𝒜'.grading = InternalGrading.ofDecomposition 𝒜) (hm₂ : ∀ a b, 𝒜'.m 2 ![a, b] = a * b) :
    IsDGAlgebra 𝒜 𝒜'.differential :=
  have h := 𝒜'.isNonUnitalDGAlgebra_differential hG hm₂
  ⟨h.map_mem, h.sq_zero, h.leibniz⟩

end AInfinityAlgebra

end Unital

end TauCeti
