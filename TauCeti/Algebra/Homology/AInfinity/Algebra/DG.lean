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

A differential graded algebra `(A, d)` is an `A∞` algebra with `m₁ = d`, `m₂` the product, and
`m n = 0` for `n ≥ 3`.  The arity-one and arity-two Stasheff identities are `d² = 0` and the
graded Leibniz rule, the arity-three identity is associativity, and every identity of arity at
least four vanishes term by term, because each of its terms contains an operation of arity at
least three.  The unit of `A` is a strict unit, and a morphism of DG algebras is a strictly unital
strict `A∞` morphism.

Conversely, an `A∞` algebra structure on a graded algebra whose binary operation is the product
makes its unary operation a DG algebra differential.  If its higher operations vanish, it is the
`A∞` algebra of that DG algebra.  Thus DG algebras are exactly the `A∞` algebras on graded
algebras whose binary operation is the product and whose higher operations vanish.

## Main definitions

* `TauCeti.IsDGAlgebra.toAInfinityAlgebra`: the `A∞` algebra of a DG algebra.
* `TauCeti.DGAlgHom.toAInfinityStrictUnitalHom`: a DG algebra morphism as a strictly unital
  strict `A∞` morphism.

## Main results

* `TauCeti.IsDGAlgebra.toAInfinityAlgebra_m_one_apply`, `toAInfinityAlgebra_m_two_apply`, and
  `toAInfinityAlgebra_m_of_three_le`: its operations are the differential, the product, and zero.
* `TauCeti.IsDGAlgebra.strictUnit_one`: the unit of a DG algebra is a strict unit.
* `TauCeti.AInfinityAlgebra.isDGAlgebra_differential`: the unary operation of an `A∞` algebra
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

variable {R : Type uR} {A : Type uA} {B : Type uB} {C : Type uC}
  [CommRing R] [Ring A] [Ring B] [Ring C]
  [Algebra R A] [Algebra R B] [Algebra R C]
  {𝒜 : ℤ → Submodule R A} {ℬ : ℤ → Submodule R B} {𝒞 : ℤ → Submodule R C}
  [GradedAlgebra 𝒜] [GradedAlgebra ℬ] [GradedAlgebra 𝒞]
  {dA : A →ₗ[R] A} {dB : B →ₗ[R] B} {dC : C →ₗ[R] C}

namespace IsDGAlgebra

/-- The `A∞` operations of a differential `d` on an algebra: `m₁ = d`, `m₂` is the product, and all
other operations vanish. -/
private noncomputable def operation (d : A →ₗ[R] A) :
    ∀ n : ℕ, MultilinearMap R (fun _ : Fin n ↦ A) A
  | 0 => 0
  | 1 => MultilinearMap.ofSubsingleton R A A 0 d
  | 2 => MultilinearMap.mkPiAlgebraFin R 2 A
  | _ + 3 => 0

private theorem operation_zero (d : A →ₗ[R] A) : operation d 0 = 0 := (rfl)

private theorem operation_one_apply (d : A →ₗ[R] A) (x : Fin 1 → A) :
    operation d 1 x = d (x 0) := (rfl)

private theorem operation_two_apply (d : A →ₗ[R] A) (x : Fin 2 → A) :
    operation d 2 x = x 0 * x 1 := by
  simp [operation]

private theorem operation_of_three_le (d : A →ₗ[R] A) {n : ℕ} (hn : 3 ≤ n) :
    operation d n = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn
  rfl

/-- The operation `operation d n` has degree `2 - n` when `d` raises degree by one. -/
private theorem isHomogeneous_operation (h : IsDGAlgebra 𝒜 d) (n : ℕ) :
    MultilinearMap.IsHomogeneous (operation d n) (fun _ ↦ 𝒜) 𝒜 (2 - n) := by
  rw [MultilinearMap.isHomogeneous_def]
  intro e x hx
  rcases n with _ | _ | _ | n
  · simp [operation_zero]
  · simpa [operation_one_apply] using h.map_mem (hx 0)
  · simpa [operation_two_apply] using SetLike.mul_mem_graded (hx 0) (hx 1)
  · simp [operation_of_three_le d (by omega : 3 ≤ n + 3)]

/-- The operations of a DG algebra satisfy every Stasheff identity on homogeneous inputs. -/
private theorem stasheffSum_operation (h : IsDGAlgebra 𝒜 d) (n : ℕ) (e : ℕ → ℤ) (x : ℕ → A)
    (hx : ∀ i < n, x i ∈ 𝒜 (e i)) :
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

/-- The `A∞` algebra of a DG algebra: `m₁ = d`, `m₂` is the product, and `m n = 0` for `n ≥ 3`. -/
noncomputable def toAInfinityAlgebra (h : IsDGAlgebra 𝒜 d) : AInfinityAlgebra R A :=
  AInfinityAlgebra.ofStasheff (InternalGrading.ofDecomposition 𝒜) (operation d) (operation_zero d)
    (fun n _ ↦ by
      rw [InternalGrading.ofDecomposition_piece]
      exact isHomogeneous_operation h n)
    (AInfinity.suspensionTaylor _ _) (AInfinity.isSuspension_suspensionTaylor _ _)
    (fun n _ e x hx ↦ by
      rw [InternalGrading.ofDecomposition_piece] at hx
      exact stasheffSum_operation h n e x hx)

/-- The `A∞` algebra of a DG algebra carries the grading of the algebra. -/
@[simp]
theorem toAInfinityAlgebra_grading (h : IsDGAlgebra 𝒜 d) :
    h.toAInfinityAlgebra.grading = InternalGrading.ofDecomposition 𝒜 := by
  rw [toAInfinityAlgebra, AInfinityAlgebra.ofStasheff_grading]

/-- The unary operation of the `A∞` algebra of a DG algebra is the differential. -/
@[simp]
theorem toAInfinityAlgebra_m_one_apply (h : IsDGAlgebra 𝒜 d) (x : Fin 1 → A) :
    h.toAInfinityAlgebra.m 1 x = d (x 0) := by
  rw [toAInfinityAlgebra, AInfinityAlgebra.ofStasheff_m, operation_one_apply]

/-- The binary operation of the `A∞` algebra of a DG algebra is the product. -/
@[simp]
theorem toAInfinityAlgebra_m_two_apply (h : IsDGAlgebra 𝒜 d) (x : Fin 2 → A) :
    h.toAInfinityAlgebra.m 2 x = x 0 * x 1 := by
  rw [toAInfinityAlgebra, AInfinityAlgebra.ofStasheff_m, operation_two_apply]

/-- The operations of arity at least three of the `A∞` algebra of a DG algebra vanish. -/
theorem toAInfinityAlgebra_m_of_three_le (h : IsDGAlgebra 𝒜 d) {n : ℕ} (hn : 3 ≤ n) :
    h.toAInfinityAlgebra.m n = 0 := by
  rw [toAInfinityAlgebra, AInfinityAlgebra.ofStasheff_m, operation_of_three_le d hn]

/-- The simp-normal form of `toAInfinityAlgebra_m_of_three_le`. -/
@[simp]
theorem toAInfinityAlgebra_m_add_three (h : IsDGAlgebra 𝒜 d) (n : ℕ) :
    h.toAInfinityAlgebra.m (n + 3) = 0 :=
  h.toAInfinityAlgebra_m_of_three_le (by omega)

/-- The differential of the `A∞` algebra of a DG algebra is the DG differential. -/
@[simp]
theorem toAInfinityAlgebra_differential (h : IsDGAlgebra 𝒜 d) :
    h.toAInfinityAlgebra.differential = d := by
  ext x
  simp

/-- The bilinear product of the `A∞` algebra of a DG algebra is the algebra multiplication. -/
@[simp]
theorem toAInfinityAlgebra_mul (h : IsDGAlgebra 𝒜 d) :
    h.toAInfinityAlgebra.mul = LinearMap.mul R A := by
  ext x y
  simp

/-- The unit of a DG algebra is a strict unit of its `A∞` algebra. -/
theorem strictUnit_one (h : IsDGAlgebra 𝒜 d) : h.toAInfinityAlgebra.StrictUnit 1 where
  degree_zero := by simpa using SetLike.one_mem_graded 𝒜
  binary_left x := by simp
  binary_right x := by simp
  higher n hn x := by
    rintro ⟨i, hi⟩
    rcases n with _ | _ | _ | n
    · exact i.elim0
    · rw [Fin.fin_one_eq_zero i] at hi
      rw [toAInfinityAlgebra_m_one_apply, hi, h.map_one_eq_zero]
    · exact absurd rfl hn
    · simp

end IsDGAlgebra

namespace DGAlgHom

variable {hA : IsDGAlgebra 𝒜 dA} {hB : IsDGAlgebra ℬ dB} {hC : IsDGAlgebra 𝒞 dC}

/-- A morphism of DG algebras is a strictly unital strict morphism of their `A∞` algebras. -/
noncomputable def toAInfinityStrictUnitalHom (f : DGAlgHom hA hB) :
    AInfinityStrictUnitalHom hA.strictUnit_one hB.strictUnit_one where
  toLinearMap := (f : A →ₐ[R] B).toLinearMap
  map_mem' ha := by simpa using GradedFunLike.map_mem f (by simpa using ha)
  map_m' n := by
    ext x
    rcases n with _ | _ | _ | n <;> simp
  map_unit' := map_one f

/-- The `A∞` morphism of a DG algebra morphism has the same underlying function. -/
@[simp]
theorem coe_toAInfinityStrictUnitalHom (f : DGAlgHom hA hB) :
    ⇑f.toAInfinityStrictUnitalHom = f := (rfl)

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
    IsDGAlgebra 𝒜 𝒜'.differential where
  map_mem {p a} ha := by
    have := (𝒜'.m_degree 1 one_pos).map_mem (fun _ ↦ p) ![a] fun _ ↦ by simpa [hG] using ha
    simpa [hG, add_comm] using this
  sq_zero a := by simpa using 𝒜'.stasheff_arity_one a
  leibniz {p a} ha b := by
    have := 𝒜'.stasheff_arity_two a b p (by simpa [hG] using ha)
    simpa [hm₂, ← negOnePow_smul_eq_negOnePowCast_smul] using this

/-- An `A∞` algebra structure on a graded algebra whose binary operation is the product and whose
higher operations vanish is the `A∞` algebra of the DG algebra given by its unary operation. -/
theorem eq_toAInfinityAlgebra (𝒜' : AInfinityAlgebra R A)
    (hG : 𝒜'.grading = InternalGrading.ofDecomposition 𝒜) (hm₂ : ∀ a b, 𝒜'.m 2 ![a, b] = a * b)
    (hm : ∀ n, 3 ≤ n → 𝒜'.m n = 0) :
    𝒜' = (𝒜'.isDGAlgebra_differential hG hm₂).toAInfinityAlgebra := by
  refine AInfinityAlgebra.ext (hG.trans (IsDGAlgebra.toAInfinityAlgebra_grading _).symm)
    (funext fun n ↦ ?_)
  rcases n with _ | _ | _ | n
  · simp
  · ext x
    rw [IsDGAlgebra.toAInfinityAlgebra_m_one_apply, differential_apply]
    congr 1
    funext i
    fin_cases i
    rfl
  · ext x
    rw [IsDGAlgebra.toAInfinityAlgebra_m_two_apply, ← hm₂]
    congr 1
    funext i
    fin_cases i <;> rfl
  · rw [IsDGAlgebra.toAInfinityAlgebra_m_add_three]
    exact hm (n + 3) (by omega)

end AInfinityAlgebra

end TauCeti
