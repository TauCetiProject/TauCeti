/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.Matrix.Nondegenerate
public import TauCeti.LinearAlgebra.Matrix.Cartan.Datum.Basic

/-!
# Constructions of Cartan data

This file builds Cartan data whose weight lattice is the dual `X = Hom(Y, ℤ)` of the coweight
lattice, paired with `Y` by evaluation:

* `TauCeti.CartanDatum.simplyConnected A d`: the simply connected datum of a nonsingular
  symmetrizable generalized Cartan matrix `A` with symmetrizer `d`, on `Y = ℤ^ι` with the standard
  basis vectors as coroots and the roots `αⱼ = Σᵢ aᵢⱼ eᵢ*`. Its Cartan matrix is `A`. The roots
  are independent because `A` is nonsingular; this covers every finite type, and the nonsingular
  indefinite types.
* `TauCeti.CartanDatum.rankOne α h`: the rank-one datum with a single root `α ∈ Hom(Y, ℤ)` and
  coroot `h ∈ Y` with `α h = 2`, on an arbitrary reflexive lattice `Y`. It records the simply
  connected and adjoint forms of `A₁`, and `GL₂` with its central direction.

The last section checks the conventions on small examples: the full lattice keeps central and
isogeny directions, the coreflection is `y ↦ y − ⟨α, y⟩ h` and not `y ↦ y + ⟨α, y⟩ h`, the
symmetrizer of `B₂` is `(1, 2)` and not `(1, 1)`, and the braid lengths of `A₁ × A₁`, `A₂`, `B₂`
and `G₂` are `2, 3, 4, 6`.

## References

* G. Lusztig, *Introduction to Quantum Groups*, Progress in Mathematics 110, Birkhäuser, 1993,
  §2.2 (root data, simply connected and adjoint).
-/

public section

open scoped Matrix

namespace TauCeti

namespace CartanDatum

open Module

/-! ### The simply connected datum of a nonsingular matrix -/

section SimplyConnected

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The **simply connected Cartan datum** of a nonsingular symmetrizable generalized Cartan matrix
`A` (diagonal `2`, nonpositive off-diagonal entries, `dᵢ aᵢⱼ = dⱼ aⱼᵢ` with `d` positive): the
coweight lattice is `ℤ^ι` with the standard basis vectors `eᵢ` as simple coroots, the weight lattice
is its dual, and the simple roots are `αⱼ = Σᵢ aᵢⱼ eᵢ*`, so that `⟨αⱼ, hᵢ⟩ = aᵢⱼ`. Nonsingularity
of `A` makes the roots linearly independent. -/
def simplyConnected (A : Matrix ι ι ℤ) (d : ι → ℕ) (hdiag : ∀ i, A i i = 2)
    (hoff : ∀ i j, i ≠ j → A i j ≤ 0) (hd : ∀ i, 0 < d i)
    (hsymm : ∀ i j, (d i : ℤ) * A i j = d j * A j i) (hdet : A.det ≠ 0) :
    CartanDatum ι (Dual ℤ (ι → ℤ)) (ι → ℤ) where
  pairing := .id
  root j := ∑ i, A i j • LinearMap.proj i
  coroot i := Pi.single i 1
  linearIndependent_root := by
    refine Fintype.linearIndependent_iff.mpr fun c hc ↦ ?_
    have hA : A *ᵥ c = 0 := funext fun i ↦ by
      have := LinearMap.congr_fun hc (Pi.single i 1)
      simpa [Matrix.mulVec, dotProduct, Pi.single_apply, mul_comm] using this
    exact congr_fun (Matrix.eq_zero_of_mulVec_eq_zero hdet hA)
  linearIndependent_coroot := Pi.linearIndependent_single_one ι ℤ
  pairing_root_coroot_self i := by simp [Pi.single_apply, hdiag]
  pairing_root_coroot_nonpos {i j} hij := by simpa [Pi.single_apply] using hoff i j hij
  symmetrizer := d
  symmetrizer_pos := hd
  symmetrizer_mul_pairing i j := by simpa [Pi.single_apply] using hsymm i j

variable (A : Matrix ι ι ℤ) (d : ι → ℕ) (hdiag : ∀ i, A i i = 2)
  (hoff : ∀ i j, i ≠ j → A i j ≤ 0) (hd : ∀ i, 0 < d i)
  (hsymm : ∀ i j, (d i : ℤ) * A i j = d j * A j i) (hdet : A.det ≠ 0)

-- `(rfl)`, not `rfl`: the body of `simplyConnected` is not exposed, and the parenthesised form
-- keeps these proofs out of the exported definitional-equality check.
@[simp]
lemma simplyConnected_pairing_apply (x : Dual ℤ (ι → ℤ)) (y : ι → ℤ) :
    (simplyConnected A d hdiag hoff hd hsymm hdet).pairing x y = x y := (rfl)

@[simp]
lemma simplyConnected_coroot (i : ι) :
    (simplyConnected A d hdiag hoff hd hsymm hdet).coroot i = Pi.single i 1 := (rfl)

@[simp]
lemma simplyConnected_root_apply (j : ι) (y : ι → ℤ) :
    (simplyConnected A d hdiag hoff hd hsymm hdet).root j y = ∑ i, A i j * y i := by
  simp [simplyConnected]

@[simp]
lemma simplyConnected_symmetrizer :
    (simplyConnected A d hdiag hoff hd hsymm hdet).symmetrizer = d := (rfl)

/-- The Cartan matrix of the simply connected datum of `A` is `A`. -/
@[simp]
lemma cartan_simplyConnected : (simplyConnected A d hdiag hoff hd hsymm hdet).cartan = A := by
  ext i j
  simp [cartan_apply, Pi.single_apply]

end SimplyConnected

/-! ### Rank one -/

section RankOne

variable {Y : Type*} [AddCommGroup Y] [IsReflexive ℤ Y]

/-- The **rank-one Cartan datum** on a reflexive lattice `Y` with the single coroot `h ∈ Y` and the
single root `α ∈ Hom(Y, ℤ)`, where `α h = 2`, and with symmetrizer `1`. The weight lattice is the
dual of `Y`, paired with `Y` by evaluation. -/
def rankOne (α : Dual ℤ Y) (h : Y) (hα : α h = 2) : CartanDatum Unit (Dual ℤ Y) Y where
  pairing := .id
  root _ := α
  coroot _ := h
  linearIndependent_root := linearIndependent_unique_iff.mpr fun h₀ ↦ by simp [h₀] at hα
  linearIndependent_coroot := linearIndependent_unique_iff.mpr fun h₀ ↦ by simp [h₀] at hα
  pairing_root_coroot_self _ := hα
  pairing_root_coroot_nonpos hij := (hij rfl).elim
  symmetrizer _ := 1
  symmetrizer_pos _ := one_pos
  symmetrizer_mul_pairing _ _ := rfl

variable (α : Dual ℤ Y) (h : Y) (hα : α h = 2)

-- `(rfl)`, not `rfl`: the body of `rankOne` is not exposed, and the parenthesised form keeps these
-- proofs out of the exported definitional-equality check.
@[simp]
lemma rankOne_pairing_apply (x : Dual ℤ Y) (y : Y) : (rankOne α h hα).pairing x y = x y := (rfl)

@[simp]
lemma rankOne_root (i : Unit) : (rankOne α h hα).root i = α := (rfl)

@[simp]
lemma rankOne_coroot (i : Unit) : (rankOne α h hα).coroot i = h := (rfl)

@[simp]
lemma rankOne_symmetrizer (i : Unit) : (rankOne α h hα).symmetrizer i = 1 := (rfl)

lemma coreflection_rankOne_apply (i : Unit) (y : Y) :
    (rankOne α h hα).coreflection i y = y - α y • h := by
  simp [coreflection_apply]

end RankOne

/-! ### Checks -/

section Checks

/-- The empty index type on the full lattice `Y = ℤ`: a Cartan datum with no roots whose coweight
lattice, the lattice of a one-dimensional torus, is nonzero. -/
example : CartanDatum Empty (Dual ℤ ℤ) ℤ where
  pairing := .id
  root := Empty.elim
  coroot := Empty.elim
  linearIndependent_root := linearIndependent_empty_type
  linearIndependent_coroot := linearIndependent_empty_type
  pairing_root_coroot_self i := i.elim
  pairing_root_coroot_nonpos {i} := i.elim
  symmetrizer := Empty.elim
  symmetrizer_pos i := i.elim
  symmetrizer_mul_pairing i := i.elim

/-- Simply connected `A₁` (`Y = ℤh`, `α = 2ω`) against adjoint `A₁` (`Y = ℤϖ`, `h = 2ϖ`,
`α = ϖ*`): in the adjoint datum the root takes the value `1` on `ϖ`, a value the simply connected
root never takes, and the coreflection sends `ϖ` to `−ϖ`. -/
example :
    (rankOne (LinearMap.id : Dual ℤ ℤ) 2 rfl).coreflection () 1 = -1 ∧
      (∃ y : ℤ, (rankOne (LinearMap.id : Dual ℤ ℤ) 2 rfl).pairing
        ((rankOne (LinearMap.id : Dual ℤ ℤ) 2 rfl).root ()) y = 1) ∧
      ¬ ∃ y : ℤ, (rankOne (2 • LinearMap.id : Dual ℤ ℤ) 1 rfl).pairing
        ((rankOne (2 • LinearMap.id : Dual ℤ ℤ) 1 rfl).root ()) y = 1 := by
  refine ⟨by simp [coreflection_rankOne_apply], ⟨1, by simp⟩, ?_⟩
  rintro ⟨y, hy⟩
  simp at hy
  omega

/-- `GL₂`: on `Y = ℤ²` with `h = e₁ − e₂` and `α = e₁* − e₂*`, the coreflection swaps `e₁` and
`e₂` and fixes the central direction `e₁ + e₂`. -/
example :
    let D := rankOne
      (LinearMap.proj (R := ℤ) (φ := fun _ : Fin 2 ↦ ℤ) 0 - LinearMap.proj 1 : Dual ℤ (Fin 2 → ℤ))
      (Pi.single 0 1 - Pi.single 1 1) (by simp)
    D.coreflection () (Pi.single 0 1) = Pi.single 1 1 ∧
      D.coreflection () (Pi.single 1 1) = Pi.single 0 1 ∧
      D.coreflection () (fun _ ↦ 1) = fun _ ↦ 1 := by
  refine ⟨?_, ?_, ?_⟩ <;>
  · ext k
    fin_cases k <;> simp [coreflection_rankOne_apply]

/-- `B₂` with `a₁₂ = −2`, `a₂₁ = −1`: the symmetrizer `(1, 2)` is accepted, its second toral
direction is `2h₂`, and its braid length is `4`; the symmetrizer `(1, 1)` fails the symmetrizing
identity at `(1, 2)`. -/
example :
    let D := simplyConnected !![2, -2; -1, 2] ![1, 2] (by simp [Fin.forall_fin_two])
      (by simp [Fin.forall_fin_two]) (by simp [Fin.forall_fin_two]) (by simp [Fin.forall_fin_two])
      (by simp [Matrix.det_fin_two_of])
    D.simpleTorus 1 = 2 • D.coroot 1 ∧ D.braidLength 0 1 = 4 ∧
      ¬ ∀ i j, ((![1, 1] : Fin 2 → ℕ) i : ℤ) * !![2, -2; -1, 2] i j =
        (![1, 1] : Fin 2 → ℕ) j * !![2, -2; -1, 2] j i := by
  refine ⟨by simp [simpleTorus_def], ?_, fun h ↦ by simpa using h 0 1⟩
  rw [braidLength_of_ne_of_le _ (by decide) (by simp)]
  simp

/-- The braid lengths of `A₁ × A₁`, `A₂` and `G₂` (with `a₁₂ = −3`, `a₂₁ = −1` and symmetrizer
`(1, 3)`) are `2`, `3` and `6`. -/
example :
    (simplyConnected !![2, 0; 0, 2] ![1, 1] (by simp [Fin.forall_fin_two])
      (by simp [Fin.forall_fin_two]) (by simp [Fin.forall_fin_two]) (by simp [Fin.forall_fin_two])
      (by simp [Matrix.det_fin_two_of])).braidLength 0 1 = 2 ∧
    (simplyConnected !![2, -1; -1, 2] ![1, 1] (by simp [Fin.forall_fin_two])
      (by simp [Fin.forall_fin_two]) (by simp [Fin.forall_fin_two]) (by simp [Fin.forall_fin_two])
      (by simp [Matrix.det_fin_two_of])).braidLength 0 1 = 3 ∧
    (simplyConnected !![2, -3; -1, 2] ![1, 3] (by simp [Fin.forall_fin_two])
      (by simp [Fin.forall_fin_two]) (by simp [Fin.forall_fin_two]) (by simp [Fin.forall_fin_two])
      (by simp [Matrix.det_fin_two_of])).braidLength 0 1 = 6 := by
  refine ⟨?_, ?_, ?_⟩ <;>
  · rw [braidLength_of_ne_of_le _ (by decide) (by simp)]
    simp

end Checks

end CartanDatum

end TauCeti
