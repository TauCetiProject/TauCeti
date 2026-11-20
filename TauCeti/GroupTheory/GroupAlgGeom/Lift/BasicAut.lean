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
import Mathlib.GroupTheory.GroupAction.FixedPoints
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

* `TauCeti.GroupAlgGeom.Lift.eval_coeffAtom`, `eval_commAtom`, `eval_basicWord`: the values of
  the atoms and of `S₀` at a point.
* `TauCeti.GroupAlgGeom.Lift.basicCoeff_basicWord`, `basicLink_basicWord`, `basicY_basicWord`,
  `basicX_basicWord`, `basicComm_basicWord`: the basic automorphisms fix `S₀`; so do their
  inverses and their natural and integer powers (`basicY_symm_basicWord`, `basicY_pow_basicWord`,
  `basicY_zpow_basicWord`, and the same for the other four).
* `TauCeti.GroupAlgGeom.Lift.basicCoeff_inl`, `basicCoeff_inr_of_left` and the lemmas after them:
  the basic automorphisms, their inverses and their natural and integer powers on the
  coefficients and on the variables.

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

variable {H : Type*} [Group H] (ι : G →* H) (u : X → H)

@[simp]
theorem eval_coeffAtom (j : Fin m) :
    eval ι u (coeffAtom z c j) = (u (z j))⁻¹ * ι (c j) * u (z j) := by
  simp [coeffAtom_def]

@[simp]
theorem eval_commAtom (i : Fin n) : eval ι u (commAtom x y i) = ⁅(u (x i))⁻¹, (u (y i))⁻¹⁆ := by
  simp [commAtom_def, map_commutatorElement]

/-- The value of the word `S₀` at a point `u`: `∏ⱼ u(zⱼ)⁻¹ ι(cⱼ) u(zⱼ) ∏ᵢ [u(xᵢ), u(yᵢ)]`. -/
@[simp]
theorem eval_basicWord :
    eval ι u (basicWord x y z c) =
      (List.ofFn fun j => (u (z j))⁻¹ * ι (c j) * u (z j)).prod *
        (List.ofFn fun i => ⁅(u (x i))⁻¹, (u (y i))⁻¹⁆).prod := by
  simp [basicWord_def, map_list_prod, List.map_ofFn, Function.comp_def]

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
automorphism `γ_{j+1}` of [IFT], §7.1 (the automorphisms of [IFT] are numbered from `1`, the
indices `j : Fin m` from `0`). -/
noncomputable def basicCoeff : MulAut (GX G X) :=
  twist (coeffAtom z c j * coeffAtom z c j')
    (blockExp x y z 0 0 fun k => if k = j ∨ k = j' then (0, 1) else 0)
    (twistHom_coeffTerm inj c j j' (Commute.refl _))
    (twistHom_coeffTerm inj c j j' (Commute.refl _).inv_left)

@[simp]
theorem basicCoeff_inl (g : G) : basicCoeff inj c j j' (inl g) = inl g := by
  simp [basicCoeff]

@[simp]
theorem basicCoeff_symm_inl (g : G) : (basicCoeff inj c j j').symm (inl g) = inl g := by
  simp [basicCoeff]

@[simp]
theorem basicCoeff_pow_inl (k : ℕ) (g : G) : (basicCoeff inj c j j' ^ k) (inl g) = inl g := by
  simp [basicCoeff]

@[simp]
theorem basicCoeff_zpow_inl (k : ℤ) (g : G) : (basicCoeff inj c j j' ^ k) (inl g) = inl g := by
  simp [basicCoeff]

@[simp]
theorem basicCoeff_inr_of_left :
    basicCoeff inj c j j' (inr (.of (z j))) =
      inr (.of (z j)) * (coeffAtom z c j * coeffAtom z c j') := by
  simp [basicCoeff, blockExp_z inj]

@[simp]
theorem basicCoeff_symm_inr_of_left :
    (basicCoeff inj c j j').symm (inr (.of (z j))) =
      inr (.of (z j)) * (coeffAtom z c j * coeffAtom z c j')⁻¹ := by
  simp [basicCoeff, blockExp_z inj]

@[simp]
theorem basicCoeff_pow_inr_of_left (k : ℕ) :
    (basicCoeff inj c j j' ^ k) (inr (.of (z j))) =
      inr (.of (z j)) * (coeffAtom z c j * coeffAtom z c j') ^ k := by
  simp [basicCoeff, blockExp_z inj]

@[simp]
theorem basicCoeff_zpow_inr_of_left (k : ℤ) :
    (basicCoeff inj c j j' ^ k) (inr (.of (z j))) =
      inr (.of (z j)) * (coeffAtom z c j * coeffAtom z c j') ^ k := by
  simp [basicCoeff, blockExp_z inj]

@[simp]
theorem basicCoeff_inr_of_right :
    basicCoeff inj c j j' (inr (.of (z j'))) =
      inr (.of (z j')) * (coeffAtom z c j * coeffAtom z c j') := by
  simp [basicCoeff, blockExp_z inj]

@[simp]
theorem basicCoeff_symm_inr_of_right :
    (basicCoeff inj c j j').symm (inr (.of (z j'))) =
      inr (.of (z j')) * (coeffAtom z c j * coeffAtom z c j')⁻¹ := by
  simp [basicCoeff, blockExp_z inj]

@[simp]
theorem basicCoeff_pow_inr_of_right (k : ℕ) :
    (basicCoeff inj c j j' ^ k) (inr (.of (z j'))) =
      inr (.of (z j')) * (coeffAtom z c j * coeffAtom z c j') ^ k := by
  simp [basicCoeff, blockExp_z inj]

@[simp]
theorem basicCoeff_zpow_inr_of_right (k : ℤ) :
    (basicCoeff inj c j j' ^ k) (inr (.of (z j'))) =
      inr (.of (z j')) * (coeffAtom z c j * coeffAtom z c j') ^ k := by
  simp [basicCoeff, blockExp_z inj]

theorem basicCoeff_zpow_inr_of_of_ne {v : X} (hj : v ≠ z j) (hj' : v ≠ z j') (k : ℤ) :
    (basicCoeff inj c j j' ^ k) (inr (.of v)) = (inr (.of v) : GX G X) := by
  rw [basicCoeff, twist_zpow_apply, twistHom_inr_of,
    blockExp_eq_zero inj (by simp) (by simp) (by rintro l rfl; aesop)]
  simp

theorem basicCoeff_inr_of_of_ne {v : X} (hj : v ≠ z j) (hj' : v ≠ z j') :
    basicCoeff inj c j j' (inr (.of v)) = (inr (.of v) : GX G X) := by
  simpa using basicCoeff_zpow_inr_of_of_ne inj c j j' hj hj' 1

theorem basicCoeff_symm_inr_of_of_ne {v : X} (hj : v ≠ z j) (hj' : v ≠ z j') :
    (basicCoeff inj c j j').symm (inr (.of v)) = (inr (.of v) : GX G X) := by
  simpa using basicCoeff_zpow_inr_of_of_ne inj c j j' hj hj' (-1)

theorem basicCoeff_pow_inr_of_of_ne {v : X} (hj : v ≠ z j) (hj' : v ≠ z j') (k : ℕ) :
    (basicCoeff inj c j j' ^ k) (inr (.of v)) = (inr (.of v) : GX G X) := by
  simpa using basicCoeff_zpow_inr_of_of_ne inj c j j' hj hj' k

/-- The basic automorphism of two adjacent coefficient atoms fixes the word `S₀`. -/
theorem basicCoeff_basicWord (hj : (j : ℕ) + 1 = j') :
    basicCoeff inj c j j' (basicWord x y z c) = basicWord x y z c := by
  rw [basicCoeff, twist_apply, basicWord_def, map_mul]
  congr 1
  · exact List.map_prod_ofFn_of_adjacent _ _ hj
      (fun l hl hl' => twistHom_coeffAtom_of_eq_zero inj c l (by simp [hl, hl']))
      (twistHom_coeffTerm inj c j j' (.refl _))
  · exact twistHom_prod_commAtom inj (fun _ => rfl) fun _ => rfl

theorem basicCoeff_zpow_basicWord (hj : (j : ℕ) + 1 = j') (k : ℤ) :
    (basicCoeff inj c j j' ^ k) (basicWord x y z c) = basicWord x y z c := by
  rw [← MulAut.smul_def]
  exact MulAction.mem_fixedBy_zpow
    ((MulAut.smul_def _ _).trans (basicCoeff_basicWord inj c j j' hj)) k

theorem basicCoeff_symm_basicWord (hj : (j : ℕ) + 1 = j') :
    (basicCoeff inj c j j').symm (basicWord x y z c) = basicWord x y z c := by
  simpa using basicCoeff_zpow_basicWord inj c j j' hj (-1)

theorem basicCoeff_pow_basicWord (hj : (j : ℕ) + 1 = j') (k : ℕ) :
    (basicCoeff inj c j j' ^ k) (basicWord x y z c) = basicWord x y z c := by
  simpa using basicCoeff_zpow_basicWord inj c j j' hj k

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

@[simp]
theorem basicLink_symm_inl (g : G) : (basicLink inj c j i).symm (inl g) = inl g := by
  simp [basicLink]

@[simp]
theorem basicLink_pow_inl (k : ℕ) (g : G) : (basicLink inj c j i ^ k) (inl g) = inl g := by
  simp [basicLink]

@[simp]
theorem basicLink_zpow_inl (k : ℤ) (g : G) : (basicLink inj c j i ^ k) (inl g) = inl g := by
  simp [basicLink]

@[simp]
theorem basicLink_inr_of_z :
    basicLink inj c j i (inr (.of (z j))) =
      inr (.of (z j)) * (coeffAtom z c j * (inr (.of (x i)))⁻¹) := by
  simp [basicLink, blockExp_z inj]

@[simp]
theorem basicLink_symm_inr_of_z :
    (basicLink inj c j i).symm (inr (.of (z j))) =
      inr (.of (z j)) * (coeffAtom z c j * (inr (.of (x i)))⁻¹)⁻¹ := by
  simp [basicLink, blockExp_z inj]

@[simp]
theorem basicLink_pow_inr_of_z (k : ℕ) :
    (basicLink inj c j i ^ k) (inr (.of (z j))) =
      inr (.of (z j)) * (coeffAtom z c j * (inr (.of (x i)))⁻¹) ^ k := by
  simp [basicLink, blockExp_z inj]

@[simp]
theorem basicLink_zpow_inr_of_z (k : ℤ) :
    (basicLink inj c j i ^ k) (inr (.of (z j))) =
      inr (.of (z j)) * (coeffAtom z c j * (inr (.of (x i)))⁻¹) ^ k := by
  simp [basicLink, blockExp_z inj]

@[simp]
theorem basicLink_inr_of_x :
    basicLink inj c j i (inr (.of (x i))) =
      (coeffAtom z c j * (inr (.of (x i)))⁻¹)⁻¹ * inr (.of (x i)) *
        (coeffAtom z c j * (inr (.of (x i)))⁻¹) := by
  simp [basicLink, blockExp_x inj]

@[simp]
theorem basicLink_symm_inr_of_x :
    (basicLink inj c j i).symm (inr (.of (x i))) =
      (coeffAtom z c j * (inr (.of (x i)))⁻¹) * inr (.of (x i)) *
        (coeffAtom z c j * (inr (.of (x i)))⁻¹)⁻¹ := by
  simp [basicLink, blockExp_x inj]

@[simp]
theorem basicLink_pow_inr_of_x (k : ℕ) :
    (basicLink inj c j i ^ k) (inr (.of (x i))) =
      ((coeffAtom z c j * (inr (.of (x i)))⁻¹) ^ k)⁻¹ * inr (.of (x i)) *
        (coeffAtom z c j * (inr (.of (x i)))⁻¹) ^ k := by
  simp [basicLink, blockExp_x inj]

@[simp]
theorem basicLink_zpow_inr_of_x (k : ℤ) :
    (basicLink inj c j i ^ k) (inr (.of (x i))) =
      ((coeffAtom z c j * (inr (.of (x i)))⁻¹) ^ k)⁻¹ * inr (.of (x i)) *
        (coeffAtom z c j * (inr (.of (x i)))⁻¹) ^ k := by
  simp [basicLink, blockExp_x inj]

@[simp]
theorem basicLink_inr_of_y :
    basicLink inj c j i (inr (.of (y i))) =
      (coeffAtom z c j * (inr (.of (x i)))⁻¹)⁻¹ * inr (.of (y i)) := by
  simp [basicLink, blockExp_y inj]

@[simp]
theorem basicLink_symm_inr_of_y :
    (basicLink inj c j i).symm (inr (.of (y i))) =
      (coeffAtom z c j * (inr (.of (x i)))⁻¹) * inr (.of (y i)) := by
  simp [basicLink, blockExp_y inj]

@[simp]
theorem basicLink_pow_inr_of_y (k : ℕ) :
    (basicLink inj c j i ^ k) (inr (.of (y i))) =
      ((coeffAtom z c j * (inr (.of (x i)))⁻¹) ^ k)⁻¹ * inr (.of (y i)) := by
  simp [basicLink, blockExp_y inj]

@[simp]
theorem basicLink_zpow_inr_of_y (k : ℤ) :
    (basicLink inj c j i ^ k) (inr (.of (y i))) =
      ((coeffAtom z c j * (inr (.of (x i)))⁻¹) ^ k)⁻¹ * inr (.of (y i)) := by
  simp [basicLink, blockExp_y inj]

theorem basicLink_zpow_inr_of_of_ne {v : X} (hz : v ≠ z j) (hx : v ≠ x i) (hy : v ≠ y i)
    (k : ℤ) : (basicLink inj c j i ^ k) (inr (.of v)) = (inr (.of v) : GX G X) := by
  rw [basicLink, twist_zpow_apply, twistHom_inr_of, blockExp_eq_zero inj
    (by rintro l rfl; exact Pi.single_eq_of_ne (fun h => hx (congrArg x h)) _)
    (by rintro l rfl; exact Pi.single_eq_of_ne (fun h => hy (congrArg y h)) _)
    (by rintro l rfl; exact Pi.single_eq_of_ne (fun h => hz (congrArg z h)) _)]
  simp

theorem basicLink_inr_of_of_ne {v : X} (hz : v ≠ z j) (hx : v ≠ x i) (hy : v ≠ y i) :
    basicLink inj c j i (inr (.of v)) = (inr (.of v) : GX G X) := by
  simpa using basicLink_zpow_inr_of_of_ne inj c j i hz hx hy 1

theorem basicLink_symm_inr_of_of_ne {v : X} (hz : v ≠ z j) (hx : v ≠ x i) (hy : v ≠ y i) :
    (basicLink inj c j i).symm (inr (.of v)) = (inr (.of v) : GX G X) := by
  simpa using basicLink_zpow_inr_of_of_ne inj c j i hz hx hy (-1)

theorem basicLink_pow_inr_of_of_ne {v : X} (hz : v ≠ z j) (hx : v ≠ x i) (hy : v ≠ y i)
    (k : ℕ) : (basicLink inj c j i ^ k) (inr (.of v)) = (inr (.of v) : GX G X) := by
  simpa using basicLink_zpow_inr_of_of_ne inj c j i hz hx hy k

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

theorem basicLink_zpow_basicWord (hj : (j : ℕ) + 1 = m) (hi : (i : ℕ) = 0) (k : ℤ) :
    (basicLink inj c j i ^ k) (basicWord x y z c) = basicWord x y z c := by
  rw [← MulAut.smul_def]
  exact MulAction.mem_fixedBy_zpow
    ((MulAut.smul_def _ _).trans (basicLink_basicWord inj c j i hj hi)) k

theorem basicLink_symm_basicWord (hj : (j : ℕ) + 1 = m) (hi : (i : ℕ) = 0) :
    (basicLink inj c j i).symm (basicWord x y z c) = basicWord x y z c := by
  simpa using basicLink_zpow_basicWord inj c j i hj hi (-1)

theorem basicLink_pow_basicWord (hj : (j : ℕ) + 1 = m) (hi : (i : ℕ) = 0) (k : ℕ) :
    (basicLink inj c j i ^ k) (basicWord x y z c) = basicWord x y z c := by
  simpa using basicLink_zpow_basicWord inj c j i hj hi k

end Link

section Y

variable (i : Fin n)

/-- The basic automorphism `y_i ↦ x_i y_i` of `G[X]`; the other variables are fixed. These are
the automorphisms `γ_{m+4i+1}` and `γ_{m+4i+3}` of [IFT], §7.1 (the automorphisms of [IFT] are
numbered from `1`, the indices `i : Fin n` from `0`). -/
noncomputable def basicY : MulAut (GX G X) :=
  twist (inr (.of (x i))) (blockExp x y z 0 (Pi.single i (1, 0)) 0)
    (by simp [blockExp_x inj]) (by simp [blockExp_x inj])

@[simp]
theorem basicY_inl (g : G) : basicY inj i (inl g) = inl g := by
  simp [basicY]

@[simp]
theorem basicY_symm_inl (g : G) : (basicY inj i).symm (inl g) = inl g := by
  simp [basicY]

@[simp]
theorem basicY_pow_inl (k : ℕ) (g : G) : (basicY inj i ^ k) (inl g) = inl g := by
  simp [basicY]

@[simp]
theorem basicY_zpow_inl (k : ℤ) (g : G) : (basicY inj i ^ k) (inl g) = inl g := by
  simp [basicY]

@[simp]
theorem basicY_inr_of :
    basicY inj i (inr (.of (y i))) = (inr (.of (x i)) : GX G X) * inr (.of (y i)) := by
  simp [basicY, blockExp_y inj]

@[simp]
theorem basicY_symm_inr_of :
    (basicY inj i).symm (inr (.of (y i))) = (inr (.of (x i)) : GX G X)⁻¹ * inr (.of (y i)) := by
  simp [basicY, blockExp_y inj]

@[simp]
theorem basicY_pow_inr_of (k : ℕ) :
    (basicY inj i ^ k) (inr (.of (y i))) = (inr (.of (x i)) : GX G X) ^ k * inr (.of (y i)) := by
  simp [basicY, blockExp_y inj]

@[simp]
theorem basicY_zpow_inr_of (k : ℤ) :
    (basicY inj i ^ k) (inr (.of (y i))) =
      (inr (.of (x i)) : GX G X) ^ k * inr (.of (y i)) := by
  simp [basicY, blockExp_y inj]

theorem basicY_zpow_inr_of_of_ne {v : X} (hy : v ≠ y i) (k : ℤ) :
    (basicY inj i ^ k) (inr (.of v)) = (inr (.of v) : GX G X) := by
  rw [basicY, twist_zpow_apply, twistHom_inr_of, blockExp_eq_zero inj (by simp)
    (by rintro l rfl; exact Pi.single_eq_of_ne (fun h => hy (congrArg y h)) _) (by simp)]
  simp

theorem basicY_inr_of_of_ne {v : X} (hy : v ≠ y i) :
    basicY inj i (inr (.of v)) = (inr (.of v) : GX G X) := by
  simpa using basicY_zpow_inr_of_of_ne inj i hy 1

theorem basicY_symm_inr_of_of_ne {v : X} (hy : v ≠ y i) :
    (basicY inj i).symm (inr (.of v)) = (inr (.of v) : GX G X) := by
  simpa using basicY_zpow_inr_of_of_ne inj i hy (-1)

theorem basicY_pow_inr_of_of_ne {v : X} (hy : v ≠ y i) (k : ℕ) :
    (basicY inj i ^ k) (inr (.of v)) = (inr (.of v) : GX G X) := by
  simpa using basicY_zpow_inr_of_of_ne inj i hy k

/-- The basic automorphism `y_i ↦ x_i y_i` fixes the word `S₀`. -/
@[simp]
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

@[simp]
theorem basicY_zpow_basicWord (k : ℤ) :
    (basicY inj i ^ k) (basicWord x y z c) = basicWord x y z c := by
  rw [← MulAut.smul_def]
  exact MulAction.mem_fixedBy_zpow ((MulAut.smul_def _ _).trans (basicY_basicWord inj c i)) k

@[simp]
theorem basicY_symm_basicWord : (basicY inj i).symm (basicWord x y z c) = basicWord x y z c := by
  simpa using basicY_zpow_basicWord inj c i (-1)

@[simp]
theorem basicY_pow_basicWord (k : ℕ) :
    (basicY inj i ^ k) (basicWord x y z c) = basicWord x y z c := by
  simpa using basicY_zpow_basicWord inj c i k

end Y

section X

variable (i : Fin n)

/-- The basic automorphism `x_i ↦ y_i x_i` of `G[X]`; the other variables are fixed. This is
the automorphism `γ_{m+4i+2}` of [IFT], §7.1 (the automorphisms of [IFT] are numbered from `1`,
the indices `i : Fin n` from `0`). -/
noncomputable def basicX : MulAut (GX G X) :=
  twist (inr (.of (y i))) (blockExp x y z (Pi.single i (1, 0)) 0 0)
    (by simp [blockExp_y inj]) (by simp [blockExp_y inj])

@[simp]
theorem basicX_inl (g : G) : basicX inj i (inl g) = inl g := by
  simp [basicX]

@[simp]
theorem basicX_symm_inl (g : G) : (basicX inj i).symm (inl g) = inl g := by
  simp [basicX]

@[simp]
theorem basicX_pow_inl (k : ℕ) (g : G) : (basicX inj i ^ k) (inl g) = inl g := by
  simp [basicX]

@[simp]
theorem basicX_zpow_inl (k : ℤ) (g : G) : (basicX inj i ^ k) (inl g) = inl g := by
  simp [basicX]

@[simp]
theorem basicX_inr_of :
    basicX inj i (inr (.of (x i))) = (inr (.of (y i)) : GX G X) * inr (.of (x i)) := by
  simp [basicX, blockExp_x inj]

@[simp]
theorem basicX_symm_inr_of :
    (basicX inj i).symm (inr (.of (x i))) = (inr (.of (y i)) : GX G X)⁻¹ * inr (.of (x i)) := by
  simp [basicX, blockExp_x inj]

@[simp]
theorem basicX_pow_inr_of (k : ℕ) :
    (basicX inj i ^ k) (inr (.of (x i))) = (inr (.of (y i)) : GX G X) ^ k * inr (.of (x i)) := by
  simp [basicX, blockExp_x inj]

@[simp]
theorem basicX_zpow_inr_of (k : ℤ) :
    (basicX inj i ^ k) (inr (.of (x i))) =
      (inr (.of (y i)) : GX G X) ^ k * inr (.of (x i)) := by
  simp [basicX, blockExp_x inj]

theorem basicX_zpow_inr_of_of_ne {v : X} (hx : v ≠ x i) (k : ℤ) :
    (basicX inj i ^ k) (inr (.of v)) = (inr (.of v) : GX G X) := by
  rw [basicX, twist_zpow_apply, twistHom_inr_of, blockExp_eq_zero inj
    (by rintro l rfl; exact Pi.single_eq_of_ne (fun h => hx (congrArg x h)) _) (by simp) (by simp)]
  simp

theorem basicX_inr_of_of_ne {v : X} (hx : v ≠ x i) :
    basicX inj i (inr (.of v)) = (inr (.of v) : GX G X) := by
  simpa using basicX_zpow_inr_of_of_ne inj i hx 1

theorem basicX_symm_inr_of_of_ne {v : X} (hx : v ≠ x i) :
    (basicX inj i).symm (inr (.of v)) = (inr (.of v) : GX G X) := by
  simpa using basicX_zpow_inr_of_of_ne inj i hx (-1)

theorem basicX_pow_inr_of_of_ne {v : X} (hx : v ≠ x i) (k : ℕ) :
    (basicX inj i ^ k) (inr (.of v)) = (inr (.of v) : GX G X) := by
  simpa using basicX_zpow_inr_of_of_ne inj i hx k

/-- The basic automorphism `x_i ↦ y_i x_i` fixes the word `S₀`. -/
@[simp]
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

@[simp]
theorem basicX_zpow_basicWord (k : ℤ) :
    (basicX inj i ^ k) (basicWord x y z c) = basicWord x y z c := by
  rw [← MulAut.smul_def]
  exact MulAction.mem_fixedBy_zpow ((MulAut.smul_def _ _).trans (basicX_basicWord inj c i)) k

@[simp]
theorem basicX_symm_basicWord : (basicX inj i).symm (basicWord x y z c) = basicWord x y z c := by
  simpa using basicX_zpow_basicWord inj c i (-1)

@[simp]
theorem basicX_pow_basicWord (k : ℕ) :
    (basicX inj i ^ k) (basicWord x y z c) = basicWord x y z c := by
  simpa using basicX_zpow_basicWord inj c i k

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
`γ_{m+4i+4}` of [IFT], §7.1 (the automorphisms of [IFT] are numbered from `1`, the indices
`i : Fin n` from `0`). -/
noncomputable def basicComm : MulAut (GX G X) :=
  twist (inr (.of (y i)) * (inr (.of (x i')))⁻¹)
    (blockExp x y z (fun l => if l = i' then (-1, 1) else if l = i then (-1, 0) else 0)
      (fun l => if l = i then (-1, 1) else if l = i' then (-1, 0) else 0) 0)
    (twistHom_commTerm inj i i' (Commute.refl _))
    (twistHom_commTerm inj i i' (Commute.refl _).inv_left)

@[simp]
theorem basicComm_inl (g : G) : basicComm inj i i' (inl g) = inl g := by
  simp [basicComm]

@[simp]
theorem basicComm_symm_inl (g : G) : (basicComm inj i i').symm (inl g) = inl g := by
  simp [basicComm]

@[simp]
theorem basicComm_pow_inl (k : ℕ) (g : G) : (basicComm inj i i' ^ k) (inl g) = inl g := by
  simp [basicComm]

@[simp]
theorem basicComm_zpow_inl (k : ℤ) (g : G) : (basicComm inj i i' ^ k) (inl g) = inl g := by
  simp [basicComm]

theorem basicComm_inr_of_x_left (h : i ≠ i') :
    basicComm inj i i' (inr (.of (x i))) =
      ((inr (.of (y i)) : GX G X) * (inr (.of (x i')))⁻¹)⁻¹ * inr (.of (x i)) := by
  simp [basicComm, blockExp_x inj, h]

theorem basicComm_symm_inr_of_x_left (h : i ≠ i') :
    (basicComm inj i i').symm (inr (.of (x i))) =
      ((inr (.of (y i)) : GX G X) * (inr (.of (x i')))⁻¹) * inr (.of (x i)) := by
  simp [basicComm, blockExp_x inj, h]

theorem basicComm_pow_inr_of_x_left (h : i ≠ i') (k : ℕ) :
    (basicComm inj i i' ^ k) (inr (.of (x i))) =
      (((inr (.of (y i)) : GX G X) * (inr (.of (x i')))⁻¹) ^ k)⁻¹ * inr (.of (x i)) := by
  simp [basicComm, blockExp_x inj, h]

theorem basicComm_zpow_inr_of_x_left (h : i ≠ i') (k : ℤ) :
    (basicComm inj i i' ^ k) (inr (.of (x i))) =
      (((inr (.of (y i)) : GX G X) * (inr (.of (x i')))⁻¹) ^ k)⁻¹ * inr (.of (x i)) := by
  simp [basicComm, blockExp_x inj, h]

@[simp]
theorem basicComm_inr_of_y_left :
    basicComm inj i i' (inr (.of (y i))) =
      ((inr (.of (y i)) : GX G X) * (inr (.of (x i')))⁻¹)⁻¹ * inr (.of (y i)) *
        (inr (.of (y i)) * (inr (.of (x i')))⁻¹) := by
  simp [basicComm, blockExp_y inj]

@[simp]
theorem basicComm_symm_inr_of_y_left :
    (basicComm inj i i').symm (inr (.of (y i))) =
      ((inr (.of (y i)) : GX G X) * (inr (.of (x i')))⁻¹) * inr (.of (y i)) *
        (inr (.of (y i)) * (inr (.of (x i')))⁻¹)⁻¹ := by
  simp [basicComm, blockExp_y inj]

@[simp]
theorem basicComm_pow_inr_of_y_left (k : ℕ) :
    (basicComm inj i i' ^ k) (inr (.of (y i))) =
      (((inr (.of (y i)) : GX G X) * (inr (.of (x i')))⁻¹) ^ k)⁻¹ * inr (.of (y i)) *
        (inr (.of (y i)) * (inr (.of (x i')))⁻¹) ^ k := by
  simp [basicComm, blockExp_y inj]

@[simp]
theorem basicComm_zpow_inr_of_y_left (k : ℤ) :
    (basicComm inj i i' ^ k) (inr (.of (y i))) =
      (((inr (.of (y i)) : GX G X) * (inr (.of (x i')))⁻¹) ^ k)⁻¹ * inr (.of (y i)) *
        (inr (.of (y i)) * (inr (.of (x i')))⁻¹) ^ k := by
  simp [basicComm, blockExp_y inj]

@[simp]
theorem basicComm_inr_of_x_right :
    basicComm inj i i' (inr (.of (x i'))) =
      ((inr (.of (y i)) : GX G X) * (inr (.of (x i')))⁻¹)⁻¹ * inr (.of (x i')) *
        (inr (.of (y i)) * (inr (.of (x i')))⁻¹) := by
  simp [basicComm, blockExp_x inj]

@[simp]
theorem basicComm_symm_inr_of_x_right :
    (basicComm inj i i').symm (inr (.of (x i'))) =
      ((inr (.of (y i)) : GX G X) * (inr (.of (x i')))⁻¹) * inr (.of (x i')) *
        (inr (.of (y i)) * (inr (.of (x i')))⁻¹)⁻¹ := by
  simp [basicComm, blockExp_x inj]

@[simp]
theorem basicComm_pow_inr_of_x_right (k : ℕ) :
    (basicComm inj i i' ^ k) (inr (.of (x i'))) =
      (((inr (.of (y i)) : GX G X) * (inr (.of (x i')))⁻¹) ^ k)⁻¹ * inr (.of (x i')) *
        (inr (.of (y i)) * (inr (.of (x i')))⁻¹) ^ k := by
  simp [basicComm, blockExp_x inj]

@[simp]
theorem basicComm_zpow_inr_of_x_right (k : ℤ) :
    (basicComm inj i i' ^ k) (inr (.of (x i'))) =
      (((inr (.of (y i)) : GX G X) * (inr (.of (x i')))⁻¹) ^ k)⁻¹ * inr (.of (x i')) *
        (inr (.of (y i)) * (inr (.of (x i')))⁻¹) ^ k := by
  simp [basicComm, blockExp_x inj]

theorem basicComm_inr_of_y_right (h : i ≠ i') :
    basicComm inj i i' (inr (.of (y i'))) =
      ((inr (.of (y i)) : GX G X) * (inr (.of (x i')))⁻¹)⁻¹ * inr (.of (y i')) := by
  simp [basicComm, blockExp_y inj, h.symm]

theorem basicComm_symm_inr_of_y_right (h : i ≠ i') :
    (basicComm inj i i').symm (inr (.of (y i'))) =
      ((inr (.of (y i)) : GX G X) * (inr (.of (x i')))⁻¹) * inr (.of (y i')) := by
  simp [basicComm, blockExp_y inj, h.symm]

theorem basicComm_pow_inr_of_y_right (h : i ≠ i') (k : ℕ) :
    (basicComm inj i i' ^ k) (inr (.of (y i'))) =
      (((inr (.of (y i)) : GX G X) * (inr (.of (x i')))⁻¹) ^ k)⁻¹ * inr (.of (y i')) := by
  simp [basicComm, blockExp_y inj, h.symm]

theorem basicComm_zpow_inr_of_y_right (h : i ≠ i') (k : ℤ) :
    (basicComm inj i i' ^ k) (inr (.of (y i'))) =
      (((inr (.of (y i)) : GX G X) * (inr (.of (x i')))⁻¹) ^ k)⁻¹ * inr (.of (y i')) := by
  simp [basicComm, blockExp_y inj, h.symm]

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

theorem basicComm_inr_of_of_ne {v : X} (hx : v ≠ x i) (hy : v ≠ y i) (hx' : v ≠ x i')
    (hy' : v ≠ y i') : basicComm inj i i' (inr (.of v)) = (inr (.of v) : GX G X) := by
  simpa using basicComm_zpow_inr_of_of_ne inj i i' hx hy hx' hy' 1

theorem basicComm_symm_inr_of_of_ne {v : X} (hx : v ≠ x i) (hy : v ≠ y i) (hx' : v ≠ x i')
    (hy' : v ≠ y i') : (basicComm inj i i').symm (inr (.of v)) = (inr (.of v) : GX G X) := by
  simpa using basicComm_zpow_inr_of_of_ne inj i i' hx hy hx' hy' (-1)

theorem basicComm_pow_inr_of_of_ne {v : X} (hx : v ≠ x i) (hy : v ≠ y i) (hx' : v ≠ x i')
    (hy' : v ≠ y i') (k : ℕ) :
    (basicComm inj i i' ^ k) (inr (.of v)) = (inr (.of v) : GX G X) := by
  simpa using basicComm_zpow_inr_of_of_ne inj i i' hx hy hx' hy' k

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

theorem basicComm_zpow_basicWord (hi : (i : ℕ) + 1 = i') (k : ℤ) :
    (basicComm inj i i' ^ k) (basicWord x y z c) = basicWord x y z c := by
  rw [← MulAut.smul_def]
  exact MulAction.mem_fixedBy_zpow
    ((MulAut.smul_def _ _).trans (basicComm_basicWord inj c i i' hi)) k

theorem basicComm_symm_basicWord (hi : (i : ℕ) + 1 = i') :
    (basicComm inj i i').symm (basicWord x y z c) = basicWord x y z c := by
  simpa using basicComm_zpow_basicWord inj c i i' hi (-1)

theorem basicComm_pow_basicWord (hi : (i : ℕ) + 1 = i') (k : ℕ) :
    (basicComm inj i i' ^ k) (basicWord x y z c) = basicWord x y z c := by
  simpa using basicComm_zpow_basicWord inj c i i' hi k

end Comm

end Families

end TauCeti.GroupAlgGeom.Lift
