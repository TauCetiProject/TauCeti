/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.ZMod.Defs
public import Mathlib.GroupTheory.Abelianization.Defs
public import TauCeti.GroupTheory.SurfaceGroup.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Pi
import TauCeti.GroupTheory.Torsion

/-!
# Abelianizations of closed surface groups

The abelianization of the closed orientable surface group
`S⁺(g, 0) = ⟨a₁, b₁, …, a_g, b_g | [a₁, b₁] ⋯ [a_g, b_g]⟩` is free abelian of rank `2 g`, on the
classes of the generators: the relator is a product of commutators, so it imposes no relation in
the abelianization.

The abelianization of the closed nonorientable surface group
`S⁻(g + 1, 0) = ⟨c₁, …, c_{g+1} | c₁ ^ 2 ⋯ c_{g+1} ^ 2⟩` is `ℤ ^ g × ℤ / 2`. In the abelianization
the generators may be rechosen to be `c₁, …, c_g` and `d = c₁ + ⋯ + c_{g+1}`, subject only to
`2 d = 0`.

Since `ℤ ^ (2 h)` has no element of order two, no closed nonorientable surface group is isomorphic
to a closed orientable one. For instance the Klein bottle group `S⁻(2, 0)`, with abelianization
`ℤ × ℤ / 2`, is not isomorphic to the torus group `S⁺(1, 0)`, although both surfaces have Euler
characteristic zero.

## Main definitions

* `TauCeti.SurfaceGroup.Orientable.closedAbelianizationEquiv`:
  `Group.Abelianization S⁺(g, 0) ≃* ℤ ^ (Fin g ⊕ Fin g)`, sending the classes of `aᵢ` and `bᵢ`
  to the standard basis vectors at `Sum.inl i` and `Sum.inr i`.
* `TauCeti.SurfaceGroup.Nonorientable.closedAbelianizationEquiv`:
  `Group.Abelianization S⁻(g + 1, 0) ≃* ℤ ^ g × ℤ / 2`, sending the class of `cᵢ` to the standard
  basis vector `(eᵢ, 0)` for `i ≤ g` and the class of `c_{g+1}` to `(-(e₁ + ⋯ + e_g), 1)`.

## Main results

* `TauCeti.SurfaceGroup.isEmpty_nonorientable_succ_zero_mulEquiv_orientable_zero`: the closed
  nonorientable surface group `S⁻(g + 1, 0)` is not isomorphic to any closed orientable surface
  group `S⁺(h, 0)`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Cambridge University Press, 2002, Section 1.2, pp. 51–52 (Corollary 1.27 and the following
  paragraph: the abelianizations of the fundamental groups of the closed surfaces `M_g` and `N_g`).
-/

public section

namespace TauCeti

namespace SurfaceGroup

namespace Orientable

/-- **The abelianization of a closed orientable surface group is free abelian of rank `2 g`.**
The abelianization of `S⁺(g, 0)` is `ℤ ^ (Fin g ⊕ Fin g)`, written multiplicatively, with the
classes of `aᵢ` and `bᵢ` as the standard basis vectors at `Sum.inl i` and `Sum.inr i`. -/
def closedAbelianizationEquiv (g : ℕ) :
    Group.Abelianization (Orientable g 0) ≃* Multiplicative (Fin g ⊕ Fin g → ℤ) :=
  MonoidHom.toMulEquiv
    -- In a commutative group the commutators of the closed orientable surface word vanish.
    (Group.Abelianization.lift <| lift (fun i ↦ .ofAdd (Pi.single (.inl i) 1))
      (fun i ↦ .ofAdd (Pi.single (.inr i) 1)) Fin.elim0 (by simp [orientableWord_def]))
    (AddMonoidHom.toMultiplicativeLeft (Fintype.linearCombination ℤ <|
      Sum.elim (fun i ↦ .ofMul (.of (a g 0 i))) fun i ↦ .ofMul (.of (b g 0 i))).toAddMonoidHom)
    (by
      ext i
      exacts [by simp, by simp, i.elim0])
    (by
      ext v x
      cases v <;> simp)

@[simp]
theorem closedAbelianizationEquiv_of_a {g : ℕ} (i : Fin g) :
    closedAbelianizationEquiv g (.of (a g 0 i)) = .ofAdd (Pi.single (.inl i) 1) := by
  simp [closedAbelianizationEquiv]

@[simp]
theorem closedAbelianizationEquiv_of_b {g : ℕ} (i : Fin g) :
    closedAbelianizationEquiv g (.of (b g 0 i)) = .ofAdd (Pi.single (.inr i) 1) := by
  simp [closedAbelianizationEquiv]

@[simp]
theorem closedAbelianizationEquiv_symm_ofAdd_single_inl {g : ℕ} (i : Fin g) (n : ℤ) :
    (closedAbelianizationEquiv g).symm (.ofAdd (Pi.single (.inl i) n)) = .of (a g 0 i) ^ n := by
  simp [MulEquiv.symm_apply_eq, ← ofAdd_zsmul, ← Pi.single_mul_right]

@[simp]
theorem closedAbelianizationEquiv_symm_ofAdd_single_inr {g : ℕ} (i : Fin g) (n : ℤ) :
    (closedAbelianizationEquiv g).symm (.ofAdd (Pi.single (.inr i) n)) = .of (b g 0 i) ^ n := by
  simp [MulEquiv.symm_apply_eq, ← ofAdd_zsmul, ← Pi.single_mul_right]

end Orientable

namespace Nonorientable

/-- The class of `cᵢ` in `ℤ ^ g × ℤ / 2` under the abelianization of `S⁻(g + 1, 0)`: the standard
basis vector `(eᵢ, 0)` for `i ≤ g`, and `(-(e₁ + ⋯ + e_g), 1)` for `i = g + 1`. -/
private def crosscapClass (g : ℕ) : Fin (g + 1) → Multiplicative ((Fin g → ℤ) × ZMod 2) :=
  Fin.lastCases (.ofAdd (-1, 1)) fun i ↦ .ofAdd (Pi.single i 1, 0)

@[simp]
private theorem crosscapClass_castSucc (g : ℕ) (i : Fin g) :
    crosscapClass g i.castSucc = .ofAdd (Pi.single i 1, 0) :=
  Fin.lastCases_castSucc ..

@[simp]
private theorem crosscapClass_last (g : ℕ) : crosscapClass g (Fin.last g) = .ofAdd (-1, 1) :=
  Fin.lastCases_last ..

/-- Twice the element `(0, 1)` of `ℤ ^ g × ℤ / 2` is zero. -/
private theorem two_nsmul_zero_one (g : ℕ) : 2 • ((0, 1) : (Fin g → ℤ) × ZMod 2) = 0 :=
  Prod.ext (by simp) rfl

/-- The classes of all the crosscaps add up to the torsion element `(0, 1)`. -/
private theorem prod_crosscapClass (g : ℕ) : ∏ i, crosscapClass g i = .ofAdd (0, 1) := by
  simp only [Fin.prod_univ_castSucc, crosscapClass_castSucc, crosscapClass_last, ← ofAdd_sum,
    ← ofAdd_add]
  congr 1
  ext <;> simp [Prod.fst_sum, Prod.snd_sum, Finset.sum_apply, Pi.single_apply]

private theorem nonorientableWord_crosscapClass (g : ℕ) :
    nonorientableWord (crosscapClass g) Fin.elim0 = 1 := by
  rw [nonorientableWord_def, List.ofFn_zero, List.prod_nil, mul_one, List.prod_ofFn,
    Finset.prod_pow, prod_crosscapClass, ← ofAdd_nsmul, two_nsmul_zero_one, ofAdd_zero]

/-- In the abelianization of `S⁻(g, 0)` twice the sum of the classes of the crosscaps is zero. -/
private theorem two_nsmul_sum_of_c (g : ℕ) :
    2 • ∑ i, Additive.ofMul (Group.Abelianization.of (c g 0 i)) = 0 := by
  simpa [nonorientableWord_def, map_list_prod, List.map_ofFn, Function.comp_def, List.prod_ofFn,
    Finset.prod_pow, ← ofMul_pow, ← ofMul_prod] using
    congrArg (fun x ↦ Additive.ofMul (Group.Abelianization.of x))
      (nonorientableWord_c_peripheral g 0)

/-- The homomorphism from `ℤ / 2` to the abelianization of `S⁻(g, 0)` sending the generator to the
sum of the classes of the crosscaps, which has order dividing two. -/
private def torsionHom (g : ℕ) : ZMod 2 →+ Additive (Group.Abelianization (Nonorientable g 0)) :=
  ZMod.lift 2 ⟨zmultiplesHom _ (∑ i, .ofMul (.of (c g 0 i))), by
    rw [zmultiplesHom_apply, natCast_zsmul, two_nsmul_sum_of_c]⟩

private theorem torsionHom_intCast (g : ℕ) (k : ℤ) :
    torsionHom g k = k • ∑ i, .ofMul (.of (c g 0 i)) := by
  simp [torsionHom]

private theorem torsionHom_one (g : ℕ) : torsionHom g 1 = ∑ i, .ofMul (.of (c g 0 i)) := by
  simpa using torsionHom_intCast g 1

/-- **The abelianization of a closed nonorientable surface group is `ℤ ^ g × ℤ / 2`.** The
abelianization of `S⁻(g + 1, 0)` is `(Fin g → ℤ) × ZMod 2`, written multiplicatively. The class of
`cᵢ` for `i ≤ g` is the standard basis vector `(eᵢ, 0)`, and the class of the last generator
`c_{g+1}` is `(-(e₁ + ⋯ + e_g), 1)`; the torsion element `(0, 1)` is the class of
`c₁ ⋯ c_{g+1}`. -/
def closedAbelianizationEquiv (g : ℕ) :
    Group.Abelianization (Nonorientable (g + 1) 0) ≃* Multiplicative ((Fin g → ℤ) × ZMod 2) :=
  MonoidHom.toMulEquiv
    (Group.Abelianization.lift <|
      lift (crosscapClass g) Fin.elim0 (nonorientableWord_crosscapClass g))
    (AddMonoidHom.toMultiplicativeLeft <| AddMonoidHom.coprod
      (Fintype.linearCombination ℤ fun i ↦ .ofMul (.of (c (g + 1) 0 i.castSucc))).toAddMonoidHom
      (torsionHom (g + 1)))
    (by
      ext i
      · induction i using Fin.lastCases with
        | last => simp [torsionHom_one, Fintype.linearCombination_apply, Fin.sum_univ_castSucc]
        | cast i => simp
      · exact i.elim0)
    (by
      -- `ℤ ^ g × ℤ / 2` is generated by the vectors `(eᵢ, 0)` and `(0, 1)`.
      refine MonoidHom.toAdditiveRight.injective <| AddMonoidHom.toIntLinearMap_injective <|
        LinearMap.prod_ext (LinearMap.pi_ext fun i x ↦ ?_) (LinearMap.ext fun t ↦ ?_)
      · simp [← ofAdd_zsmul, ← Pi.single_mul_right]
      · obtain ⟨k, rfl⟩ := ZMod.intCast_surjective t
        simp [torsionHom_intCast, prod_crosscapClass, ← ofAdd_zsmul])

@[simp]
theorem closedAbelianizationEquiv_of_c_castSucc {g : ℕ} (i : Fin g) :
    closedAbelianizationEquiv g (.of (c (g + 1) 0 i.castSucc)) = .ofAdd (Pi.single i 1, 0) := by
  simp [closedAbelianizationEquiv]

@[simp]
theorem closedAbelianizationEquiv_of_c_last (g : ℕ) :
    closedAbelianizationEquiv g (.of (c (g + 1) 0 (Fin.last g))) = .ofAdd (-1, 1) := by
  simp [closedAbelianizationEquiv]

@[simp]
theorem closedAbelianizationEquiv_symm_ofAdd_single_zero {g : ℕ} (i : Fin g) (n : ℤ) :
    (closedAbelianizationEquiv g).symm (.ofAdd (Pi.single i n, 0)) =
      .of (c (g + 1) 0 i.castSucc) ^ n := by
  simp [MulEquiv.symm_apply_eq, ← ofAdd_zsmul, ← Pi.single_mul_right]

/-- The torsion element `(0, 1)` of `ℤ ^ g × ℤ / 2` is the class of the product of the
crosscaps. -/
@[simp]
theorem closedAbelianizationEquiv_symm_ofAdd_zero_one (g : ℕ) :
    (closedAbelianizationEquiv g).symm (.ofAdd (0, 1)) = ∏ i, .of (c (g + 1) 0 i) := by
  rw [MulEquiv.symm_apply_eq, map_prod]
  simpa [closedAbelianizationEquiv] using (prod_crosscapClass g).symm

end Nonorientable

/-- **Closed nonorientable and orientable surface groups are not isomorphic.** No closed
nonorientable surface group `S⁻(g + 1, 0)` is isomorphic to a closed orientable surface group
`S⁺(h, 0)`: the abelianization `ℤ ^ g × ℤ / 2` of the former has an element of order two, while the
abelianization `ℤ ^ (2 h)` of the latter has none. For `g = h = 1` the Klein bottle group `S⁻(2, 0)`
is not the torus group `S⁺(1, 0)`, although both surfaces have Euler characteristic zero. -/
theorem isEmpty_nonorientable_succ_zero_mulEquiv_orientable_zero (g h : ℕ) :
    IsEmpty (Nonorientable (g + 1) 0 ≃* Orientable h 0) :=
  ⟨fun e ↦ not_subsingleton (ZMod 2) <| subsingleton_of_mulEquiv isAddTorsion_of_finite <|
    ((Orientable.closedAbelianizationEquiv h).symm.trans e.symm.abelianizationCongr).trans
      (Nonorientable.closedAbelianizationEquiv g)⟩

end SurfaceGroup

end TauCeti
