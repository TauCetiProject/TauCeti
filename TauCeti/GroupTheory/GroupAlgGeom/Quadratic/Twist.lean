/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GroupAlgGeom.Quadratic.Word
public import TauCeti.GroupTheory.GroupAlgGeom.Twist
import TauCeti.Data.List.ProdOfFn
import Mathlib.GroupTheory.Commutator.Basic

/-!
# Twists of the atoms of a quadratic word

A twist `twistHom B e` of the free `G`-group `G[X]` substitutes `B ^ l * v * B ^ r` for every
variable `v`, where `(l, r) = e v` (`TauCeti.GroupAlgGeom.twistHom`). This file computes its
values on the atoms `zⱼ⁻¹ cⱼ zⱼ`, `[xᵢ, yᵢ]` and `uₖ²` of a quadratic word, and shows that it fixes
an atom, and the word `S₀ = ∏ⱼ zⱼ⁻¹ cⱼ zⱼ ∏ᵢ [xᵢ, yᵢ]`, when its exponents vanish at their
variables. The basic automorphisms of [IFT], §7.1 and §7.5, are twists that move the variables
of two adjacent atoms; these lemmas show that they fix the other atoms.

## Main results

* `TauCeti.GroupAlgGeom.Quadratic.twistHom_coeffAtom`, `twistHom_commAtom`: a twist on the atoms
  `zⱼ⁻¹ cⱼ zⱼ` and `[xᵢ, yᵢ]`.
* `TauCeti.GroupAlgGeom.Quadratic.twistHom_coeffAtom_of_eq_zero`,
  `twistHom_commAtom_of_eq_zero`, `twistHom_sqAtom_of_eq_zero`, `twistHom_basicWord`: a twist
  whose exponents vanish at the variables of an atom, or of `S₀`, fixes it.

## References

* [IFT] O. Kharlampovich, A. Myasnikov, *Implicit function theorem over free groups*, J. Algebra
  290 (2005), §7.1 and §7.5.
-/

public section

open Monoid.Coprod
open scoped commutatorElement

namespace TauCeti.GroupAlgGeom.Quadratic

variable {G X : Type*} [Group G] {n m r : ℕ} {x y : Fin n → X} {z : Fin m → X} {u : Fin r → X}
  {B : GX G X} {e : X → ℤ × ℤ} (c : Fin m → G)

/-- A twist whose left exponent vanishes at `z_j` conjugates the atom `z_j⁻¹ c_j z_j`. -/
theorem twistHom_coeffAtom (j : Fin m) (hj : (e (z j)).1 = 0) :
    twistHom B e (coeffAtom z c j) = (B ^ (e (z j)).2)⁻¹ * coeffAtom z c j * B ^ (e (z j)).2 := by
  simp [coeffAtom_def, hj, mul_assoc]

/-- A twist on the atom `[x_i, y_i]`. -/
theorem twistHom_commAtom (i : Fin n) :
    twistHom B e (commAtom x y i) =
      ⁅(B ^ (e (x i)).1 * inr (.of (x i)) * B ^ (e (x i)).2)⁻¹,
        (B ^ (e (y i)).1 * inr (.of (y i)) * B ^ (e (y i)).2)⁻¹⁆ := by
  simp [commAtom_def, map_commutatorElement]

/-- A twist whose exponents vanish at `z_j` fixes the atom `z_j⁻¹ c_j z_j`. -/
theorem twistHom_coeffAtom_of_eq_zero (j : Fin m) (hj : e (z j) = 0) :
    twistHom B e (coeffAtom z c j) = coeffAtom z c j := by
  simp [twistHom_coeffAtom, hj]

/-- A twist whose exponents vanish at `x_i` and `y_i` fixes the atom `[x_i, y_i]`. -/
theorem twistHom_commAtom_of_eq_zero (i : Fin n) (hx : e (x i) = 0) (hy : e (y i) = 0) :
    twistHom B e (commAtom x y i) = commAtom x y i := by
  rw [twistHom_commAtom, hx, hy]
  simp [commAtom_def]

/-- A twist whose exponents vanish at `uₖ` fixes the square `uₖ²`. -/
theorem twistHom_sqAtom_of_eq_zero (k : Fin r) (hk : e (u k) = 0) :
    twistHom B e (sqAtom u k) = sqAtom u k := by
  simp [sqAtom_def, hk]

theorem twistHom_prod_coeffAtom (hz : ∀ j, e (z j) = 0) :
    twistHom B e (List.ofFn (coeffAtom z c)).prod = (List.ofFn (coeffAtom z c)).prod :=
  List.map_prod_ofFn_of_forall _ _ fun j => twistHom_coeffAtom_of_eq_zero c j (hz j)

theorem twistHom_prod_commAtom (hx : ∀ i, e (x i) = 0) (hy : ∀ i, e (y i) = 0) :
    twistHom B e (List.ofFn (commAtom x y)).prod = (List.ofFn (commAtom (G := G) x y)).prod :=
  List.map_prod_ofFn_of_forall _ _ fun i => twistHom_commAtom_of_eq_zero i (hx i) (hy i)

/-- A twist whose exponents vanish at the variables of `S₀` fixes `S₀`. -/
theorem twistHom_basicWord (hx : ∀ i, e (x i) = 0) (hy : ∀ i, e (y i) = 0)
    (hz : ∀ j, e (z j) = 0) : twistHom B e (basicWord x y z c) = basicWord x y z c := by
  rw [basicWord_def, map_mul, twistHom_prod_coeffAtom c hz, twistHom_prod_commAtom hx hy]

end TauCeti.GroupAlgGeom.Quadratic
