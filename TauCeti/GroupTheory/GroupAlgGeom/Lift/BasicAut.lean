/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GroupAlgGeom.Twist
public import Mathlib.Algebra.Group.Commutator
import TauCeti.Data.List.ProdOfFn
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.Tactic.Group

/-!
# Basic automorphisms of an orientable quadratic word

Let `G` be a group and `X` a set of variables containing pairwise distinct variables `xᵢ`, `yᵢ`
(`i = 1, …, n`) and `zⱼ` (`j = 1, …, m`), and let `cⱼ ∈ G`. Following [IFT], §7.1, this file
defines `G`-automorphisms of the free `G`-group `G[X]` fixing the word
`S₀ = ∏ⱼ zⱼ⁻¹ cⱼ zⱼ ∏ᵢ [xᵢ, yᵢ]`, where `[x, y] = x⁻¹ y⁻¹ x y`. Composing a solution of a
quadratic equation with products of powers of these automorphisms produces the families of
solutions that are used to lift equations to the coordinate group of the quadratic equation.

Each basic automorphism multiplies or conjugates the variables of one or two atoms by a word `A`
that it fixes, and fixes the other variables. Writing `c^z = z⁻¹ c z`, they are
* `basicCoeff`: `zⱼ ↦ zⱼ A`, `zⱼ' ↦ zⱼ' A` with `A = cⱼ^{zⱼ} cⱼ'^{zⱼ'}`;
* `basicLink`: `zⱼ ↦ zⱼ A`, `xᵢ ↦ A⁻¹ xᵢ A`, `yᵢ ↦ A⁻¹ yᵢ` with `A = cⱼ^{zⱼ} xᵢ⁻¹`;
* `basicY`: `yᵢ ↦ xᵢ yᵢ`, and `basicX`: `xᵢ ↦ yᵢ xᵢ`;
* `basicComm`: `xᵢ ↦ A⁻¹ xᵢ`, `yᵢ ↦ A⁻¹ yᵢ A`, `xᵢ' ↦ A⁻¹ xᵢ' A`, `yᵢ' ↦ A⁻¹ yᵢ'` with
  `A = yᵢ xᵢ'⁻¹`, for `i ≠ i'` (for `i = i'` it conjugates `xᵢ` and `yᵢ` by `A`).

They are automorphisms for all indices. The word `S₀` is fixed by `basicY` and `basicX`, and by
the other three when the two atoms are adjacent in `S₀`: `j' = j + 1` for `basicCoeff`, the last
coefficient atom and the first commutator for `basicLink`, and `i' = i + 1` for `basicComm`;
these are the automorphisms of [IFT], §7.1.

All of them are twists (`TauCeti.GroupAlgGeom.twist`), so their powers are given by the same
formulas with `A ^ k` in place of `A`, for every integer `k` ([IFT], Lemma 41).

## Main definitions

* `TauCeti.GroupAlgGeom.Lift.coeffAtom`, `TauCeti.GroupAlgGeom.Lift.commAtom`: the atoms
  `zⱼ⁻¹ cⱼ zⱼ` and `[xᵢ, yᵢ]`.
* `TauCeti.GroupAlgGeom.Lift.basicWord`: the word `S₀`.
* `TauCeti.GroupAlgGeom.Lift.basicCoeff`, `basicLink`, `basicY`, `basicX`, `basicComm`: the basic
  automorphisms.

## Main results

* `TauCeti.GroupAlgGeom.Lift.basicCoeff_basicWord`, `basicLink_basicWord`, `basicY_basicWord`,
  `basicX_basicWord`, `basicComm_basicWord`: the basic automorphisms fix `S₀`.
* `TauCeti.GroupAlgGeom.Lift.basicCoeff_zpow_inr_of_left` and the lemmas after it: the powers of
  the basic automorphisms on the variables.

## References

* [IFT] O. Kharlampovich, A. Myasnikov, *Implicit function theorem over free groups*, J. Algebra
  290 (2005), §7.1 and Lemma 41.
* [LIFT] O. Kharlampovich, A. Myasnikov, *Algebraic geometry over free groups: lifting solutions
  into generic points*, Contemp. Math. 378 (2005), §4.
-/

public section

open Monoid.Coprod
open scoped commutatorElement

namespace TauCeti.GroupAlgGeom.Lift

variable {G X : Type*} [Group G] {n m : ℕ}

/-! ### The word `S₀` and its atoms -/

section Word

variable (x y : Fin n → X) (z : Fin m → X) (c : Fin m → G)

/-- The conjugate `z_j⁻¹ c_j z_j` of the coefficient `c_j` by the variable `z_j`. -/
def coeffAtom (j : Fin m) : GX G X :=
  (inr (.of (z j)))⁻¹ * inl (c j) * inr (.of (z j))

/-- The commutator `[x_i, y_i] = x_i⁻¹ y_i⁻¹ x_i y_i` of two variables. -/
def commAtom (i : Fin n) : GX G X :=
  ⁅(inr (.of (x i)) : GX G X)⁻¹, (inr (.of (y i)))⁻¹⁆

/-- The word `S₀ = ∏ⱼ zⱼ⁻¹ cⱼ zⱼ ∏ᵢ [xᵢ, yᵢ]` of [IFT], §7.1. -/
def basicWord : GX G X :=
  (List.ofFn (coeffAtom z c)).prod * (List.ofFn (commAtom (G := G) x y)).prod

theorem coeffAtom_def (j : Fin m) :
    coeffAtom z c j = (inr (.of (z j)))⁻¹ * inl (c j) * inr (.of (z j)) := (rfl)

theorem commAtom_def (i : Fin n) :
    commAtom (G := G) x y i = ⁅(inr (.of (x i)) : GX G X)⁻¹, (inr (.of (y i)))⁻¹⁆ := (rfl)

theorem basicWord_def :
    basicWord x y z c =
      (List.ofFn (coeffAtom z c)).prod * (List.ofFn (commAtom (G := G) x y)).prod := (rfl)

private theorem basicWord_eq_prod_append :
    basicWord x y z c = (List.ofFn (Fin.append (coeffAtom z c) (commAtom x y))).prod := by
  rw [List.ofFn_fin_append, List.prod_append, basicWord_def]

end Word

/-! ### Exponents of a block of variables -/

section BlockExp

variable {x y : Fin n → X} {z : Fin m → X} {ex ey : Fin n → ℤ × ℤ} {ez : Fin m → ℤ × ℤ}

/-- The exponents on `X` that are `ex i` at `x i`, `ey i` at `y i`, `ez j` at `z j` and zero at
the other variables. -/
private noncomputable def blockExp (x y : Fin n → X) (z : Fin m → X) (ex ey : Fin n → ℤ × ℤ)
    (ez : Fin m → ℤ × ℤ) : X → ℤ × ℤ :=
  Function.extend (Sum.elim (Sum.elim x y) z) (Sum.elim (Sum.elim ex ey) ez) 0

variable (inj : (Sum.elim (Sum.elim x y) z).Injective)
include inj

private theorem blockExp_x (i : Fin n) : blockExp x y z ex ey ez (x i) = ex i :=
  inj.extend_apply _ _ (.inl (.inl i))

private theorem blockExp_y (i : Fin n) : blockExp x y z ex ey ez (y i) = ey i :=
  inj.extend_apply _ _ (.inl (.inr i))

private theorem blockExp_z (j : Fin m) : blockExp x y z ex ey ez (z j) = ez j :=
  inj.extend_apply _ _ (.inr j)

private theorem blockExp_eq_zero {v : X} (hx : ∀ i, v = x i → ex i = 0)
    (hy : ∀ i, v = y i → ey i = 0) (hz : ∀ j, v = z j → ez j = 0) :
    blockExp x y z ex ey ez v = 0 := by
  by_cases hv : ∃ a, Sum.elim (Sum.elim x y) z a = v
  · obtain ⟨(i | i) | j, rfl⟩ := hv
    · exact (blockExp_x inj i).trans (hx i rfl)
    · exact (blockExp_y inj i).trans (hy i rfl)
    · exact (blockExp_z inj j).trans (hz j rfl)
  · exact Function.extend_apply' _ _ _ hv

variable {B : GX G X} (c : Fin m → G)

private theorem twistHom_coeffAtom (j : Fin m) (hj : (ez j).1 = 0) :
    twistHom B (blockExp x y z ex ey ez) (coeffAtom z c j) =
      (B ^ (ez j).2)⁻¹ * coeffAtom z c j * B ^ (ez j).2 := by
  simp [coeffAtom, blockExp_z inj, hj, mul_assoc]

private theorem twistHom_commAtom (i : Fin n) :
    twistHom B (blockExp x y z ex ey ez) (commAtom x y i) =
      ⁅(B ^ (ex i).1 * inr (.of (x i)) * B ^ (ex i).2)⁻¹,
        (B ^ (ey i).1 * inr (.of (y i)) * B ^ (ey i).2)⁻¹⁆ := by
  simp [commAtom, map_commutatorElement, blockExp_x inj, blockExp_y inj]

private theorem twistHom_coeffAtom_of_eq_zero (j : Fin m) (hj : ez j = 0) :
    twistHom B (blockExp x y z ex ey ez) (coeffAtom z c j) = coeffAtom z c j := by
  simp [twistHom_coeffAtom inj, hj]

private theorem twistHom_commAtom_of_eq_zero (i : Fin n) (hx : ex i = 0) (hy : ey i = 0) :
    twistHom B (blockExp x y z ex ey ez) (commAtom x y i) = commAtom x y i := by
  rw [twistHom_commAtom inj, hx, hy]
  simp [commAtom_def]

private theorem twistHom_prod_coeffAtom (hz : ∀ j, ez j = 0) :
    twistHom B (blockExp x y z ex ey ez) (List.ofFn (coeffAtom z c)).prod =
      (List.ofFn (coeffAtom z c)).prod :=
  List.map_prod_ofFn_of_forall _ _ fun j => twistHom_coeffAtom_of_eq_zero inj c j (hz j)

private theorem twistHom_prod_commAtom (hx : ∀ i, ex i = 0) (hy : ∀ i, ey i = 0) :
    twistHom B (blockExp x y z ex ey ez) (List.ofFn (commAtom x y)).prod =
      (List.ofFn (commAtom (G := G) x y)).prod :=
  List.map_prod_ofFn_of_forall _ _ fun i => twistHom_commAtom_of_eq_zero inj i (hx i) (hy i)

end BlockExp

/-! ### The basic automorphisms -/

section Families

variable {x y : Fin n → X} {z : Fin m → X} (inj : (Sum.elim (Sum.elim x y) z).Injective)
  (c : Fin m → G)
include inj

section Coeff

variable (j j' : Fin m)

private theorem twistHom_coeffTerm {B : GX G X}
    (hB : Commute B (coeffAtom z c j * coeffAtom z c j')) :
    twistHom B (blockExp x y z 0 0 fun k => if k = j ∨ k = j' then (0, 1) else 0)
      (coeffAtom z c j * coeffAtom z c j') = coeffAtom z c j * coeffAtom z c j' := by
  rw [map_mul, twistHom_coeffAtom inj c j (by simp), twistHom_coeffAtom inj c j' (by simp)]
  simp only [true_or, or_true, ite_true, zpow_one]
  calc _ = B⁻¹ * (coeffAtom z c j * coeffAtom z c j') * B := by group
    _ = _ := hB.inv_mul_cancel

/-- The basic automorphism `z_j ↦ z_j A`, `z_j' ↦ z_j' A` of `G[X]`, where
`A = z_j⁻¹ c_j z_j * z_j'⁻¹ c_j' z_j'`; the other variables are fixed. For `j' = j + 1` it is the
automorphism `γ_j` of [IFT], §7.1, with `j ≤ m - 1`. -/
noncomputable def basicCoeff : MulAut (GX G X) :=
  twist (coeffAtom z c j * coeffAtom z c j')
    (blockExp x y z 0 0 fun k => if k = j ∨ k = j' then (0, 1) else 0)
    (twistHom_coeffTerm inj c j j' (Commute.refl _))
    (twistHom_coeffTerm inj c j j' (Commute.refl _).inv_left)

@[simp]
theorem basicCoeff_inl (g : G) : basicCoeff inj c j j' (inl g) = inl g := by
  simp [basicCoeff]

theorem basicCoeff_zpow_inr_of_left (k : ℤ) :
    (basicCoeff inj c j j' ^ k) (inr (.of (z j))) =
      inr (.of (z j)) * (coeffAtom z c j * coeffAtom z c j') ^ k := by
  simp [basicCoeff, twist_zpow_apply, twistHom_inr_of, blockExp_z inj]

theorem basicCoeff_zpow_inr_of_right (k : ℤ) :
    (basicCoeff inj c j j' ^ k) (inr (.of (z j'))) =
      inr (.of (z j')) * (coeffAtom z c j * coeffAtom z c j') ^ k := by
  simp [basicCoeff, twist_zpow_apply, twistHom_inr_of, blockExp_z inj]

theorem basicCoeff_zpow_inr_of_of_ne {v : X} (hj : v ≠ z j) (hj' : v ≠ z j') (k : ℤ) :
    (basicCoeff inj c j j' ^ k) (inr (.of v)) = (inr (.of v) : GX G X) := by
  rw [basicCoeff, twist_zpow_apply, twistHom_inr_of,
    blockExp_eq_zero inj (by simp) (by simp) (by rintro l rfl; aesop)]
  simp

/-- The basic automorphism of two adjacent coefficient atoms fixes the word `S₀`. -/
theorem basicCoeff_basicWord (hj : (j : ℕ) + 1 = j') :
    basicCoeff inj c j j' (basicWord x y z c) = basicWord x y z c := by
  rw [basicCoeff, twist_apply, basicWord_def, map_mul]
  congr 1
  · exact List.map_prod_ofFn_of_adjacent _ _ hj
      (fun l hl hl' => twistHom_coeffAtom_of_eq_zero inj c l (by simp [hl, hl']))
      (twistHom_coeffTerm inj c j j' (.refl _))
  · exact twistHom_prod_commAtom inj (fun _ => rfl) fun _ => rfl

end Coeff

section Link

variable (j : Fin m) (i : Fin n)

private theorem twistHom_linkTerm {B : GX G X}
    (hB : Commute B (coeffAtom z c j * (inr (.of (x i)))⁻¹)) :
    twistHom B (blockExp x y z (Pi.single i (-1, 1)) (Pi.single i (-1, 0)) (Pi.single j (0, 1)))
      (coeffAtom z c j * (inr (.of (x i)))⁻¹) = coeffAtom z c j * (inr (.of (x i)))⁻¹ := by
  rw [map_mul, map_inv, twistHom_coeffAtom inj c j (by simp), twistHom_inr_of, blockExp_x inj]
  simp only [Pi.single_eq_same]
  calc _ = B⁻¹ * (coeffAtom z c j * (inr (.of (x i)))⁻¹) * B := by group
    _ = _ := hB.inv_mul_cancel

/-- The basic automorphism `z_j ↦ z_j A`, `x_i ↦ A⁻¹ x_i A`, `y_i ↦ A⁻¹ y_i` of `G[X]`, where
`A = z_j⁻¹ c_j z_j * x_i⁻¹`; the other variables are fixed. For the last coefficient atom and
the first commutator it is the automorphism `γ_m` of [IFT], §7.1. -/
noncomputable def basicLink : MulAut (GX G X) :=
  twist (coeffAtom z c j * (inr (.of (x i)))⁻¹)
    (blockExp x y z (Pi.single i (-1, 1)) (Pi.single i (-1, 0)) (Pi.single j (0, 1)))
    (twistHom_linkTerm inj c j i (Commute.refl _))
    (twistHom_linkTerm inj c j i (Commute.refl _).inv_left)

@[simp]
theorem basicLink_inl (g : G) : basicLink inj c j i (inl g) = inl g := by
  simp [basicLink]

theorem basicLink_zpow_inr_of_z (k : ℤ) :
    (basicLink inj c j i ^ k) (inr (.of (z j))) =
      inr (.of (z j)) * (coeffAtom z c j * (inr (.of (x i)))⁻¹) ^ k := by
  simp [basicLink, twist_zpow_apply, twistHom_inr_of, blockExp_z inj]

theorem basicLink_zpow_inr_of_x (k : ℤ) :
    (basicLink inj c j i ^ k) (inr (.of (x i))) =
      ((coeffAtom z c j * (inr (.of (x i)))⁻¹) ^ k)⁻¹ * inr (.of (x i)) *
        (coeffAtom z c j * (inr (.of (x i)))⁻¹) ^ k := by
  simp [basicLink, twist_zpow_apply, twistHom_inr_of, blockExp_x inj]

theorem basicLink_zpow_inr_of_y (k : ℤ) :
    (basicLink inj c j i ^ k) (inr (.of (y i))) =
      ((coeffAtom z c j * (inr (.of (x i)))⁻¹) ^ k)⁻¹ * inr (.of (y i)) := by
  simp [basicLink, twist_zpow_apply, twistHom_inr_of, blockExp_y inj]

theorem basicLink_zpow_inr_of_of_ne {v : X} (hz : v ≠ z j) (hx : v ≠ x i) (hy : v ≠ y i)
    (k : ℤ) : (basicLink inj c j i ^ k) (inr (.of v)) = (inr (.of v) : GX G X) := by
  rw [basicLink, twist_zpow_apply, twistHom_inr_of, blockExp_eq_zero inj
    (by rintro l rfl; exact Pi.single_eq_of_ne (fun h => hx (congrArg x h)) _)
    (by rintro l rfl; exact Pi.single_eq_of_ne (fun h => hy (congrArg y h)) _)
    (by rintro l rfl; exact Pi.single_eq_of_ne (fun h => hz (congrArg z h)) _)]
  simp

/-- The basic automorphism of the last coefficient atom and the first commutator fixes the word
`S₀`. -/
theorem basicLink_basicWord (hj : (j : ℕ) + 1 = m) (hi : (i : ℕ) = 0) :
    basicLink inj c j i (basicWord x y z c) = basicWord x y z c := by
  rw [basicLink, twist_apply, basicWord_eq_prod_append]
  refine List.map_prod_ofFn_of_adjacent _ _ (i := Fin.castAdd n j) (i' := Fin.natAdd m i)
    (by simp [hj, hi]) (fun l hl hl' => ?_) ?_
  · induction l using Fin.addCases with
    | left l =>
      have hlj : l ≠ j := fun h => hl (h ▸ rfl)
      simpa using twistHom_coeffAtom_of_eq_zero inj c l (Pi.single_eq_of_ne hlj _)
    | right l =>
      have hli : l ≠ i := fun h => hl' (h ▸ rfl)
      simpa using twistHom_commAtom_of_eq_zero inj l (Pi.single_eq_of_ne hli _)
        (Pi.single_eq_of_ne hli _)
  · rw [Fin.append_left, Fin.append_right, map_mul, twistHom_coeffAtom inj c j (by simp),
      twistHom_commAtom inj]
    simp only [Pi.single_eq_same, commAtom_def, commutatorElement_def]
    group

end Link

section Y

variable (i : Fin n)

/-- The basic automorphism `y_i ↦ x_i y_i` of `G[X]`; the other variables are fixed. These are
the automorphisms `γ_{m+4i-3}` and `γ_{m+4i-1}` of [IFT], §7.1. -/
noncomputable def basicY : MulAut (GX G X) :=
  twist (inr (.of (x i))) (blockExp x y z 0 (Pi.single i (1, 0)) 0)
    (by simp [blockExp_x inj]) (by simp [blockExp_x inj])

@[simp]
theorem basicY_inl (g : G) : basicY inj i (inl g) = inl g := by
  simp [basicY]

theorem basicY_zpow_inr_of (k : ℤ) :
    (basicY inj i ^ k) (inr (.of (y i))) =
      (inr (.of (x i)) : GX G X) ^ k * inr (.of (y i)) := by
  simp [basicY, twist_zpow_apply, twistHom_inr_of, blockExp_y inj]

theorem basicY_zpow_inr_of_of_ne {v : X} (hy : v ≠ y i) (k : ℤ) :
    (basicY inj i ^ k) (inr (.of v)) = (inr (.of v) : GX G X) := by
  rw [basicY, twist_zpow_apply, twistHom_inr_of, blockExp_eq_zero inj (by simp)
    (by rintro l rfl; exact Pi.single_eq_of_ne (fun h => hy (congrArg y h)) _) (by simp)]
  simp

/-- The basic automorphism `y_i ↦ x_i y_i` fixes the word `S₀`. -/
theorem basicY_basicWord : basicY inj i (basicWord x y z c) = basicWord x y z c := by
  rw [basicY, twist_apply, basicWord_def, map_mul]
  congr 1
  · exact twistHom_prod_coeffAtom inj c fun _ => rfl
  refine List.map_prod_ofFn_of_forall _ _ fun l => ?_
  rw [twistHom_commAtom inj, commAtom_def]
  obtain rfl | hl := eq_or_ne l i
  · simp only [Pi.zero_apply, Pi.single_eq_same, Prod.fst_zero, Prod.snd_zero,
      commutatorElement_def]
    group
  · simp [hl]

end Y

section X

variable (i : Fin n)

/-- The basic automorphism `x_i ↦ y_i x_i` of `G[X]`; the other variables are fixed. This is
the automorphism `γ_{m+4i-2}` of [IFT], §7.1. -/
noncomputable def basicX : MulAut (GX G X) :=
  twist (inr (.of (y i))) (blockExp x y z (Pi.single i (1, 0)) 0 0)
    (by simp [blockExp_y inj]) (by simp [blockExp_y inj])

@[simp]
theorem basicX_inl (g : G) : basicX inj i (inl g) = inl g := by
  simp [basicX]

theorem basicX_zpow_inr_of (k : ℤ) :
    (basicX inj i ^ k) (inr (.of (x i))) =
      (inr (.of (y i)) : GX G X) ^ k * inr (.of (x i)) := by
  simp [basicX, twist_zpow_apply, twistHom_inr_of, blockExp_x inj]

theorem basicX_zpow_inr_of_of_ne {v : X} (hx : v ≠ x i) (k : ℤ) :
    (basicX inj i ^ k) (inr (.of v)) = (inr (.of v) : GX G X) := by
  rw [basicX, twist_zpow_apply, twistHom_inr_of, blockExp_eq_zero inj
    (by rintro l rfl; exact Pi.single_eq_of_ne (fun h => hx (congrArg x h)) _) (by simp) (by simp)]
  simp

/-- The basic automorphism `x_i ↦ y_i x_i` fixes the word `S₀`. -/
theorem basicX_basicWord : basicX inj i (basicWord x y z c) = basicWord x y z c := by
  rw [basicX, twist_apply, basicWord_def, map_mul]
  congr 1
  · exact twistHom_prod_coeffAtom inj c fun _ => rfl
  refine List.map_prod_ofFn_of_forall _ _ fun l => ?_
  rw [twistHom_commAtom inj, commAtom_def]
  obtain rfl | hl := eq_or_ne l i
  · simp only [Pi.zero_apply, Pi.single_eq_same, Prod.fst_zero, Prod.snd_zero,
      commutatorElement_def]
    group
  · simp [hl]

end X

section Comm

variable (i i' : Fin n)

private theorem twistHom_commTerm {B : GX G X}
    (hB : Commute B (inr (.of (y i)) * (inr (.of (x i')))⁻¹)) :
    twistHom B (blockExp x y z (fun l => if l = i' then (-1, 1) else if l = i then (-1, 0) else 0)
        (fun l => if l = i then (-1, 1) else if l = i' then (-1, 0) else 0) 0)
      (inr (.of (y i)) * (inr (.of (x i')))⁻¹) = inr (.of (y i)) * (inr (.of (x i')))⁻¹ := by
  rw [map_mul, map_inv, twistHom_inr_of, twistHom_inr_of, blockExp_y inj, blockExp_x inj]
  simp only [ite_true]
  calc _ = B⁻¹ * (inr (.of (y i)) * (inr (.of (x i')))⁻¹) * B := by group
    _ = _ := hB.inv_mul_cancel

/-- The basic automorphism of `G[X]` given, for `i ≠ i'`, by `x_i ↦ A⁻¹ x_i`, `y_i ↦ A⁻¹ y_i A`,
`x_i' ↦ A⁻¹ x_i' A`, `y_i' ↦ A⁻¹ y_i'`, where `A = y_i x_i'⁻¹`; the other variables are fixed.
For `i = i'` it is `x_i ↦ A⁻¹ x_i A`, `y_i ↦ A⁻¹ y_i A`. For `i' = i + 1` it is the automorphism
`γ_{m+4i}` of [IFT], §7.1. -/
noncomputable def basicComm : MulAut (GX G X) :=
  twist (inr (.of (y i)) * (inr (.of (x i')))⁻¹)
    (blockExp x y z (fun l => if l = i' then (-1, 1) else if l = i then (-1, 0) else 0)
      (fun l => if l = i then (-1, 1) else if l = i' then (-1, 0) else 0) 0)
    (twistHom_commTerm inj i i' (Commute.refl _))
    (twistHom_commTerm inj i i' (Commute.refl _).inv_left)

@[simp]
theorem basicComm_inl (g : G) : basicComm inj i i' (inl g) = inl g := by
  simp [basicComm]

theorem basicComm_zpow_inr_of_x_left (h : i ≠ i') (k : ℤ) :
    (basicComm inj i i' ^ k) (inr (.of (x i))) =
      (((inr (.of (y i)) : GX G X) * (inr (.of (x i')))⁻¹) ^ k)⁻¹ * inr (.of (x i)) := by
  simp [basicComm, twist_zpow_apply, twistHom_inr_of, blockExp_x inj, h]

theorem basicComm_zpow_inr_of_y_left (k : ℤ) :
    (basicComm inj i i' ^ k) (inr (.of (y i))) =
      (((inr (.of (y i)) : GX G X) * (inr (.of (x i')))⁻¹) ^ k)⁻¹ * inr (.of (y i)) *
        (inr (.of (y i)) * (inr (.of (x i')))⁻¹) ^ k := by
  simp [basicComm, twist_zpow_apply, twistHom_inr_of, blockExp_y inj]

theorem basicComm_zpow_inr_of_x_right (k : ℤ) :
    (basicComm inj i i' ^ k) (inr (.of (x i'))) =
      (((inr (.of (y i)) : GX G X) * (inr (.of (x i')))⁻¹) ^ k)⁻¹ * inr (.of (x i')) *
        (inr (.of (y i)) * (inr (.of (x i')))⁻¹) ^ k := by
  simp [basicComm, twist_zpow_apply, twistHom_inr_of, blockExp_x inj]

theorem basicComm_zpow_inr_of_y_right (h : i ≠ i') (k : ℤ) :
    (basicComm inj i i' ^ k) (inr (.of (y i'))) =
      (((inr (.of (y i)) : GX G X) * (inr (.of (x i')))⁻¹) ^ k)⁻¹ * inr (.of (y i')) := by
  simp [basicComm, twist_zpow_apply, twistHom_inr_of, blockExp_y inj, h.symm]

theorem basicComm_zpow_inr_of_of_ne {v : X} (hx : v ≠ x i) (hy : v ≠ y i) (hx' : v ≠ x i')
    (hy' : v ≠ y i') (k : ℤ) :
    (basicComm inj i i' ^ k) (inr (.of v)) = (inr (.of v) : GX G X) := by
  rw [basicComm, twist_zpow_apply, twistHom_inr_of, blockExp_eq_zero inj
    (by rintro l rfl; simp [show l ≠ i' from fun h => hx' (congrArg x h),
      show l ≠ i from fun h => hx (congrArg x h)])
    (by rintro l rfl; simp [show l ≠ i from fun h => hy (congrArg y h),
      show l ≠ i' from fun h => hy' (congrArg y h)])
    (by simp)]
  simp

/-- The basic automorphism of two adjacent commutators fixes the word `S₀`. -/
theorem basicComm_basicWord (hi : (i : ℕ) + 1 = i') :
    basicComm inj i i' (basicWord x y z c) = basicWord x y z c := by
  have hne : i ≠ i' := fun h => by simp [h] at hi
  rw [basicComm, twist_apply, basicWord_def, map_mul]
  congr 1
  · exact twistHom_prod_coeffAtom inj c fun _ => rfl
  refine List.map_prod_ofFn_of_adjacent _ _ hi (fun l hl hl' =>
    twistHom_commAtom_of_eq_zero inj l (by simp [hl, hl']) (by simp [hl, hl'])) ?_
  rw [map_mul, twistHom_commAtom inj, twistHom_commAtom inj]
  simp only [↓reduceIte, hne, hne.symm, commAtom_def, commutatorElement_def]
  group

end Comm

end Families

end TauCeti.GroupAlgGeom.Lift
