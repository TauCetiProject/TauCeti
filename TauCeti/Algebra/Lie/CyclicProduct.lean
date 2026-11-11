/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Pi
public import TauCeti.Algebra.Lie.Subalgebra.Fixed.Basic
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Fixed Lie algebras of cyclic products

Suppose an automorphism cyclically permutes a nonempty family of Lie algebra factors,
with specified Lie equivalences between successive factors. Its fixed Lie algebra is
isomorphic to the fixed Lie algebra of the return automorphism on the first factor.
The inverse transports a fixed vector along the successive equivalences. This reduces
fixed-algebra calculations for component cycles, including internal automorphism twists,
to a calculation on one component. No assumption on the order of the return automorphism
or the characteristic is needed.

The construction uses `LieHom.fixedSubalgebra` for both fixed carriers. See V. Kac,
*Infinite-Dimensional Lie Algebras*, §7.9, for the component-cycle reduction in folding.
-/

public section

namespace TauCeti
namespace LieCyclicProduct

variable {R : Type*} [CommRing R] {n : ℕ}
variable {L : Fin (n + 1) → Type*} [∀ i, LieRing (L i)] [∀ i, LieAlgebra R (L i)]

/-- Transport from the first factor to a specified factor along a chain of Lie equivalences. -/
def transport (e : ∀ i : Fin n, L i.castSucc ≃ₗ⁅R⁆ L i.succ)
    (i : Fin (n + 1)) : L 0 ≃ₗ⁅R⁆ L i :=
  Fin.induction (LieEquiv.refl : L 0 ≃ₗ⁅R⁆ L 0) (fun j t => t.trans (e j)) i

/-- Transport to the first factor is the identity. -/
@[simp]
theorem transport_zero (e : ∀ i : Fin n, L i.castSucc ≃ₗ⁅R⁆ L i.succ) :
    transport e 0 = LieEquiv.refl := by
  simp [transport]

/-- Transport to the next factor appends the next equivalence. -/
@[simp]
theorem transport_succ (e : ∀ i : Fin n, L i.castSucc ≃ₗ⁅R⁆ L i.succ) (i : Fin n) :
    transport e i.succ = (transport e i.castSucc).trans (e i) := by
  simp [transport]

/-- The return automorphism is transport along the chain followed by the closing equivalence. -/
def returnEquiv (e : ∀ i : Fin n, L i.castSucc ≃ₗ⁅R⁆ L i.succ)
    (c : L (Fin.last n) ≃ₗ⁅R⁆ L 0) : L 0 ≃ₗ⁅R⁆ L 0 :=
  (transport e (Fin.last n)).trans c

/-- The return automorphism applies the closing map after transport to the last factor. -/
@[simp]
theorem returnEquiv_apply (e : ∀ i : Fin n, L i.castSucc ≃ₗ⁅R⁆ L i.succ)
    (c : L (Fin.last n) ≃ₗ⁅R⁆ L 0) (x : L 0) :
    returnEquiv e c x = c (transport e (Fin.last n) x) := (rfl)

/-- The product automorphism sends each factor to its successor, closing the last to the first. -/
def shift (e : ∀ i : Fin n, L i.castSucc ≃ₗ⁅R⁆ L i.succ)
    (c : L (Fin.last n) ≃ₗ⁅R⁆ L 0) : (∀ i, L i) ≃ₗ⁅R⁆ (∀ i, L i) where
  toFun x := Fin.cons (c (x (Fin.last n))) (fun i => e i (x i.castSucc))
  invFun x := Fin.snoc (fun i => (e i).symm (x i.succ)) (c.symm (x 0))
  left_inv x := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
  right_inv x := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp
  map_add' x y := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp
  map_smul' t x := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp
  map_lie' {x y} := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp [LieEquiv.map_lie]

/-- The first coordinate of the shifted tuple comes from the last factor. -/
@[simp]
theorem shift_apply_zero (e : ∀ i : Fin n, L i.castSucc ≃ₗ⁅R⁆ L i.succ)
    (c : L (Fin.last n) ≃ₗ⁅R⁆ L 0) (x : ∀ i, L i) :
    shift e c x 0 = c (x (Fin.last n)) := (rfl)

/-- Every other shifted coordinate comes from its predecessor. -/
@[simp]
theorem shift_apply_succ (e : ∀ i : Fin n, L i.castSucc ≃ₗ⁅R⁆ L i.succ)
    (c : L (Fin.last n) ≃ₗ⁅R⁆ L 0) (x : ∀ i, L i) (i : Fin n) :
    shift e c x i.succ = e i (x i.castSucc) := (rfl)

/-- The last coordinate of the inverse shift uses the inverse closing equivalence. -/
@[simp]
theorem shift_symm_apply_last (e : ∀ i : Fin n, L i.castSucc ≃ₗ⁅R⁆ L i.succ)
    (c : L (Fin.last n) ≃ₗ⁅R⁆ L 0) (x : ∀ i, L i) :
    (shift e c).symm x (Fin.last n) = c.symm (x 0) := by
  have h := congrFun ((shift e c).apply_symm_apply x) 0
  simpa only [shift_apply_zero, LieEquiv.symm_apply_apply] using congrArg c.symm h

/-- Every other coordinate of the inverse shift uses the inverse successor equivalence. -/
@[simp]
theorem shift_symm_apply_castSucc (e : ∀ i : Fin n, L i.castSucc ≃ₗ⁅R⁆ L i.succ)
    (c : L (Fin.last n) ≃ₗ⁅R⁆ L 0) (x : ∀ i, L i) (i : Fin n) :
    (shift e c).symm x i.castSucc = (e i).symm (x i.succ) := by
  have h := congrFun ((shift e c).apply_symm_apply x) i.succ
  simpa only [shift_apply_succ, LieEquiv.symm_apply_apply] using congrArg (e i).symm h

/-- A fixed tuple is determined by its first coordinate and transport along the chain. -/
theorem apply_eq_transport (e : ∀ i : Fin n, L i.castSucc ≃ₗ⁅R⁆ L i.succ)
    (c : L (Fin.last n) ≃ₗ⁅R⁆ L 0)
    (x : (shift e c).toLieHom.fixedSubalgebra) (i : Fin (n + 1)) :
    x.val i = transport e i (x.val 0) := by
  have hx := LieHom.mem_fixedSubalgebra.mp x.property
  induction i using Fin.induction with
  | zero => simp
  | succ i ih =>
    have hi := congrFun hx i.succ
    simpa [ih, -LieHom.apply_coe_fixedSubalgebra] using hi.symm

/-- The first coordinate of a fixed tuple is fixed by the return automorphism. -/
theorem returnEquiv_apply_zero (e : ∀ i : Fin n, L i.castSucc ≃ₗ⁅R⁆ L i.succ)
    (c : L (Fin.last n) ≃ₗ⁅R⁆ L 0)
    (x : (shift e c).toLieHom.fixedSubalgebra) :
    returnEquiv e c (x.val 0) = x.val 0 := by
  rw [returnEquiv_apply, ← apply_eq_transport e c x]
  exact congrFun (LieHom.mem_fixedSubalgebra.mp x.property) 0

/-- Restriction to the first factor identifies the fixed product with the fixed return algebra.
Its inverse transports a return-fixed vector along the chain. -/
def fixedEquiv (e : ∀ i : Fin n, L i.castSucc ≃ₗ⁅R⁆ L i.succ)
    (c : L (Fin.last n) ≃ₗ⁅R⁆ L 0) :
    (shift e c).toLieHom.fixedSubalgebra ≃ₗ⁅R⁆
      (returnEquiv e c).toLieHom.fixedSubalgebra where
  toFun x := ⟨x.val 0, LieHom.mem_fixedSubalgebra.mpr (returnEquiv_apply_zero e c x)⟩
  invFun x := ⟨fun i => transport e i x.val, by
    apply LieHom.mem_fixedSubalgebra.mpr
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa [-LieHom.apply_coe_fixedSubalgebra] using LieHom.mem_fixedSubalgebra.mp x.property
    · simp⟩
  left_inv x := by
    apply Subtype.ext
    funext i
    exact (apply_eq_transport e c x i).symm
  right_inv x := by
    apply Subtype.ext
    simp
  map_add' x y := rfl
  map_smul' t x := rfl
  map_lie' := rfl

/-- Restriction to the first factor is the forward fixed-algebra equivalence. -/
@[simp]
theorem fixedEquiv_apply (e : ∀ i : Fin n, L i.castSucc ≃ₗ⁅R⁆ L i.succ)
    (c : L (Fin.last n) ≃ₗ⁅R⁆ L 0) (x : (shift e c).toLieHom.fixedSubalgebra) :
    (fixedEquiv e c x).val = x.val 0 := (rfl)

/-- The inverse fixed-algebra equivalence is transport to every factor. -/
@[simp]
theorem fixedEquiv_symm_apply (e : ∀ i : Fin n, L i.castSucc ≃ₗ⁅R⁆ L i.succ)
    (c : L (Fin.last n) ≃ₗ⁅R⁆ L 0)
    (x : (returnEquiv e c).toLieHom.fixedSubalgebra) (i : Fin (n + 1)) :
    ((fixedEquiv e c).symm x).val i = transport e i x.val := (rfl)

end LieCyclicProduct
end TauCeti
