/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.AInfinity.Algebra.Unit
public import TauCeti.Algebra.Homology.AInfinity.Module.Right.Free

/-!
# Strict units for right A-infinity modules

A strict unit of a right `A∞` module is a strict unit of its algebra which acts as the identity
through the binary module operation and annihilates every higher module operation containing it.
The module input occupies the first slot, so the vanishing condition concerns only the algebra
inputs. The unary differential remains unrestricted.

The regular right module of a strictly unital `A∞` algebra is strictly unital. This supplies the
unit law needed for representable modules and their Yoneda evaluation.

## References

* B. Keller, *Introduction to A-infinity algebras and modules*, Sections 3.1 and 4.1.
-/

public section

namespace TauCeti

universe uR uA uM

namespace AInfinityRightModule

variable {R : Type uR} {A : Type uA} {M : Type uM}
  [CommRing R] [AddCommGroup A] [Module R A] [AddCommGroup M] [Module R M]
  {AA : AInfinityAlgebra R A}

/-- A **strict unit** for a right `A∞` module. The algebra element `e` is a strict unit of `AA`,
acts as the identity by the binary module operation, and makes all module operations of arity at
least three vanish when it occurs among the algebra inputs. -/
structure StrictUnit (MM : AInfinityRightModule AA M) (e : A) : Prop where
  /-- The chosen element is a strict unit of the acting algebra. -/
  algebraUnit : AA.StrictUnit e
  /-- The binary module action of the unit is the identity. -/
  binary_right : ∀ x, MM.m 2 x ![e] = x
  /-- A higher module operation vanishes if one of its algebra inputs is the unit. -/
  higher : ∀ (n : ℕ), 1 < n → ∀ (x : M) (a : Fin n → A),
    (∃ i, a i = e) → MM.m (n + 1) x a = 0

attribute [simp] StrictUnit.binary_right

namespace StrictUnit

variable {MM : AInfinityRightModule AA M} {e : A}

/-- A higher module operation vanishes when a specified algebra input is the unit. -/
theorem m_eq_zero_of_eq_unit (h : MM.StrictUnit e) {n : ℕ} (hn : 1 < n)
    (x : M) (a : Fin n → A) {i : Fin n} (hi : a i = e) :
    MM.m (n + 1) x a = 0 :=
  h.higher n hn x a ⟨i, hi⟩

end StrictUnit

end AInfinityRightModule

namespace AInfinityAlgebra

variable {R : Type uR} {A : Type uA} [CommRing R] [AddCommGroup A] [Module R A]
  {AA : AInfinityAlgebra R A} {e : A}

/-- The regular right module of a strictly unital `A∞` algebra is strictly unital. -/
theorem StrictUnit.toRightModule (he : AA.StrictUnit e) :
    AA.toRightModule.StrictUnit e where
  algebraUnit := he
  binary_right x := by
    rw [AA.m_toRightModule]
    have h : (Fin.cons x ![e] : Fin 2 → A) = ![x, e] := by
      funext i
      fin_cases i <;> rfl
    simpa only [Nat.reduceAdd, h] using he.binary_right x
  higher n hn x a hi := by
    rw [AA.m_toRightModule]
    rcases hi with ⟨i, hi⟩
    exact he.higher (n + 1) (by omega) (Fin.cons x a) ⟨i.succ, by simpa using hi⟩

end AInfinityAlgebra

end TauCeti
