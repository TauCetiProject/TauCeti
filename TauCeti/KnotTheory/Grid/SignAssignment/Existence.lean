/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.SignAssignment.Basic
import Mathlib.Algebra.CharP.Invertible
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import TauCeti.KnotTheory.Grid.Differential.Square.Recut.Geometry
import TauCeti.KnotTheory.Grid.Differential.Square.Uniqueness
import TauCeti.KnotTheory.Grid.Rectangle.Annulus.Basic
import TauCeti.LinearAlgebra.CliffordAlgebra.Pin.Action
import TauCeti.LinearAlgebra.CliffordAlgebra.Pin.Kernel
import TauCeti.LinearAlgebra.QuadraticForm.Diagonal.Basic
import TauCeti.LinearAlgebra.QuadraticForm.Radical

/-!
# Existence of sign assignments for grid rectangles

Every grid size `n` admits a `GridSignAssignment n`. Following Gallais's Clifford-algebraic
formulation of the Manolescu--Ozsváth--Szabó--Thurston existence theorem, we equip `ℚⁿ` with the
negative-definite quadratic form `Q(v) = -½ ∑ vᵢ²`, embed the symmetric group `Sₙ` into the
orthogonal group `O(Q)` by coordinate permutation, and lift each grid state's permutation
`x.toPerm ∈ Sₙ` to an element `σ(x)` of the double cover `Pin(Q) → O(Q)`.

For each transposition `(a b)` with `a ≠ b`, the root vector `e_a - e_b` has `Q(e_a - e_b) = -1`,
so its Clifford image `t(a, b) = ι(e_a - e_b)` lies in `Pin(Q)` and covers `(a b) ∈ O(Q)`. Because
the kernel of `Pin(Q) → O(Q)` is `{±1}` (reusing
`CliffordAlgebra.existsUnique_zsmul_of_pinToOrthogonal_eq` from
`TauCeti.LinearAlgebra.CliffordAlgebra.Pin.Kernel`), every rectangle `r` from `x` to `y` satisfies
`σ(x) · t(r.left, r.right) = S(r) · σ(y)` for a unique sign `S(r) ∈ ℤˣ`.

All three axioms of a sign assignment reduce to four elementary identities in `CliffordAlgebra Q`:
* `t(a, b)² = -1` (vertical annulus rule),
* `t(a, b) · t(b, a) = 1` (horizontal annulus rule),
* `t(a, b) · t(c, d) = -t(c, d) · t(a, b)` for disjoint `{a, b}` and `{c, d}` (disjoint-side square
  rule), and
* `t(a, b) · t(b, c) = t(b, c) · t(c, a)` for distinct `a, b, c` (one-common-side recut square
  rule).

The uniqueness of two-step empty rectangle decompositions of a given covered-square multiset
(`TauCeti.KnotTheory.Grid.Differential.Square.Uniqueness`) ensures that every pair of distinct
empty decompositions in the square rule is either a disjoint-side commutation or a recut.

## Main results

* `TauCeti.GridSignAssignment.nonempty`: every grid size `n : ℕ` admits a sign assignment.

## References

* E. Gallais, *Sign refinement for combinatorial link Floer homology*, Algebr. Geom. Topol. 8
  (2008), 1581--1592 (arXiv:0706.0089).
* C. Manolescu, P. Ozsváth, Z. Szabó, D. Thurston, *On combinatorial link Floer homology*,
  Geom. Topol. 11 (2007), Section 4 (arXiv:math/0610559).
* P. Ozsváth, A. Stipsicz, Z. Szabó, *Grid Homology for Knots and Links*, AMS Mathematical Surveys
  and Monographs 208, 2015, Chapter 15.2.
-/

public section

namespace TauCeti

namespace GridSignAssignment

/-! ### The negative-definite quadratic form and the `Pin⁻` double cover of `Sₙ` -/

/-- The negative-definite quadratic form `Q(v) = -½ ∑ vᵢ²` on `ℚⁿ`, scaled so that every root
vector `e_a - e_b` (`a ≠ b`) has norm `-1`. -/
private noncomputable def gridForm (n : ℕ) : QuadraticForm ℚ (Fin n → ℚ) :=
  QuadraticMap.weightedSumSquares ℚ (fun _ : Fin n => (-1 / 2 : ℚ))

private theorem gridForm_apply {n : ℕ} (v : Fin n → ℚ) :
    gridForm n v = ∑ i : Fin n, (-1 / 2 : ℚ) * (v i * v i) := by
  simp [gridForm, QuadraticMap.weightedSumSquares_apply]

private theorem polar_gridForm {n : ℕ} (v w : Fin n → ℚ) :
    QuadraticMap.polar (gridForm n) v w = -∑ i : Fin n, v i * w i := by
  simp only [QuadraticMap.polar, gridForm_apply, Pi.add_apply, ← Finset.sum_neg_distrib,
    ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun _ _ => by ring

private theorem gridForm_nondegenerate (n : ℕ) : (gridForm n).Nondegenerate :=
  _root_.QuadraticMap.nondegenerate_weightedSumSquares_iff.mpr fun _ =>
    isRegular_iff_ne_zero.mpr (by norm_num)

/-- Coordinate permutation embeds `Equiv.Perm (Fin n)` into the orthogonal group of `gridForm n`. -/
private noncomputable def permToOrthogonal (n : ℕ) :
    Equiv.Perm (Fin n) →* QuadraticMap.orthogonalGroup (gridForm n) where
  toFun σ :=
    ⟨LinearEquiv.funCongrLeft ℚ ℚ σ⁻¹,
      QuadraticMap.mem_orthogonalGroup_iff.mpr fun v => by
        simp only [gridForm_apply, LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply]
        exact Equiv.sum_comp σ⁻¹ (fun i => (-1 / 2 : ℚ) * (v i * v i))⟩
  map_one' := Subtype.ext <| by dsimp only; rw [inv_one]; rfl
  map_mul' _ _ := Subtype.ext <| by
    dsimp only; rw [mul_inv_rev, Equiv.Perm.mul_def, LinearEquiv.funCongrLeft_comp]; rfl

private theorem permToOrthogonal_apply {n : ℕ} (σ : Equiv.Perm (Fin n)) (v : Fin n → ℚ)
    (i : Fin n) : ((permToOrthogonal n σ : (Fin n → ℚ) ≃ₗ[ℚ] (Fin n → ℚ)) v) i = v (σ⁻¹ i) := rfl

/-- The root vector `e_a - e_b ∈ ℚⁿ`. -/
private def rootVec {n : ℕ} (a b : Fin n) : Fin n → ℚ := Pi.single a 1 - Pi.single b 1

private theorem rootVec_swap {n : ℕ} (a b : Fin n) : rootVec b a = -rootVec a b := by simp [rootVec]

private theorem rootVec_cycle {n : ℕ} (a b c : Fin n) :
    rootVec c a = -(rootVec a b + rootVec b c) := by
  ext i; simp only [rootVec, Pi.sub_apply, Pi.neg_apply, Pi.add_apply]; ring

private theorem gridForm_rootVec {n : ℕ} {a b : Fin n} (hab : a ≠ b) :
    gridForm n (rootVec a b) = -1 := by
  rw [gridForm_apply]
  have hterm : ∀ i : Fin n, (-1 / 2 : ℚ) * (rootVec a b i * rootVec a b i) =
      (if i = a then (-1 / 2 : ℚ) else 0) + (if i = b then (-1 / 2 : ℚ) else 0) := fun i => by
    simp only [rootVec, Pi.sub_apply, Pi.single_apply]
    by_cases ha : i = a <;> by_cases hb : i = b <;> simp_all [hab.symm]
  simp only [hterm, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  norm_num

private theorem polar_gridForm_rootVec {n : ℕ} (a b : Fin n) (v : Fin n → ℚ) :
    QuadraticMap.polar (gridForm n) (rootVec a b) v = v b - v a := by
  simp [polar_gridForm, rootVec, Pi.single_apply, ite_mul]; ring

/-- The Pin-group lift `ι(e_a - e_b)` of the transposition `Equiv.swap a b`. -/
private noncomputable def pinSwap {n : ℕ} (a b : Fin n) (hab : a ≠ b) : pinGroup (gridForm n) :=
  ⟨CliffordAlgebra.ι (gridForm n) (rootVec a b),
    CliffordAlgebra.ι_mem_pinGroup (gridForm_rootVec hab)⟩

private theorem pinToOrthogonal_pinSwap {n : ℕ} (a b : Fin n) (hab : a ≠ b) :
    CliffordAlgebra.pinToOrthogonal (gridForm n) (pinSwap a b hab) =
      permToOrthogonal n (Equiv.swap a b) := by
  apply Subtype.ext; ext v i
  rw [pinSwap, CliffordAlgebra.pinToOrthogonal_ι_apply (gridForm_rootVec hab),
    permToOrthogonal_apply, Equiv.swap_inv, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    polar_gridForm_rootVec]
  simp only [rootVec, Pi.sub_apply, Pi.single_apply, Equiv.swap_apply_def]
  by_cases ha : i = a <;> by_cases hb : i = b <;> simp_all [hab.symm]

private theorem exists_pinToOrthogonal_eq_permToOrthogonal {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    ∃ g : pinGroup (gridForm n),
      CliffordAlgebra.pinToOrthogonal (gridForm n) g = permToOrthogonal n σ := by
  induction σ using Equiv.Perm.swap_induction_on with
  | one => exact ⟨1, by simp⟩
  | swap_mul f a b hab ih =>
    obtain ⟨g, hg⟩ := ih
    exact ⟨pinSwap a b hab * g, by rw [map_mul, pinToOrthogonal_pinSwap, hg, ← map_mul]⟩

/-! ### Clifford algebra relations among root-vector generators -/

/-- The Clifford-algebra element `t(a, b) = ι(e_a - e_b)` associated to an ordered pair of
columns. -/
private noncomputable abbrev rootClifford {n : ℕ} (a b : Fin n) : CliffordAlgebra (gridForm n) :=
  CliffordAlgebra.ι (gridForm n) (rootVec a b)

private theorem rootClifford_mul_self {n : ℕ} {a b : Fin n} (hab : a ≠ b) :
    rootClifford a b * rootClifford a b = -1 := by
  rw [rootClifford, CliffordAlgebra.ι_sq_scalar, gridForm_rootVec hab, map_neg, map_one]

private theorem rootClifford_swap {n : ℕ} (a b : Fin n) : rootClifford b a = -rootClifford a b := by
  rw [rootClifford, rootVec_swap, map_neg]

private theorem rootClifford_mul_swap {n : ℕ} {a b : Fin n} (hab : a ≠ b) :
    rootClifford a b * rootClifford b a = 1 := by
  rw [rootClifford_swap a b, mul_neg, rootClifford_mul_self hab, neg_neg]

private theorem rootClifford_mul_comm_neg {n : ℕ} {a b c d : Fin n}
    (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) :
    rootClifford a b * rootClifford c d = -(rootClifford c d * rootClifford a b) := by
  have hsum := CliffordAlgebra.ι_mul_ι_add_swap (Q := gridForm n) (rootVec a b) (rootVec c d)
  rw [show QuadraticMap.polar (gridForm n) (rootVec a b) (rootVec c d) = 0 by
    rw [polar_gridForm_rootVec]; simp [rootVec, hac, had, hbc, hbd], map_zero] at hsum
  exact eq_neg_of_add_eq_zero_left hsum

private theorem rootClifford_mul_cycle {n : ℕ} {a b c : Fin n}
    (hab : a ≠ b) (hbc : b ≠ c) (hca : c ≠ a) :
    rootClifford a b * rootClifford b c = rootClifford b c * rootClifford c a := by
  have hsum := CliffordAlgebra.ι_mul_ι_add_swap (Q := gridForm n) (rootVec a b) (rootVec b c)
  rw [show QuadraticMap.polar (gridForm n) (rootVec a b) (rootVec b c) = 1 by
    rw [polar_gridForm_rootVec]; simp [rootVec, hab.symm, hbc, hca.symm], map_one] at hsum
  have hba : rootClifford b c * rootClifford a b = 1 - rootClifford a b * rootClifford b c :=
    eq_sub_of_add_eq' hsum
  rw [show rootClifford c a = -(rootClifford a b + rootClifford b c) by
    rw [rootClifford, rootVec_cycle, map_neg, map_add],
    mul_neg, mul_add, hba, rootClifford_mul_self hbc]
  abel

private theorem rootClifford_recut_eq_neg_of_hasSameSideOverlap {n : ℕ} {x z : GridState n}
    (D : GridRectangleDecomposition x z) (hone : D.HasOneCommonSide)
    (hD₁ : D.first.IsEmpty) (hD₂ : D.second.IsEmpty) (hsame : D.HasSameSideOverlap) :
    rootClifford (D.recut hone hD₁ hD₂).first.left (D.recut hone hD₁ hD₂).first.right *
        rootClifford (D.recut hone hD₁ hD₂).second.left (D.recut hone hD₁ hD₂).second.right =
      -(rootClifford D.first.left D.first.right * rootClifford D.second.left D.second.right) := by
  rcases (D.hasSameSideOverlap_iff.mp hsame).2 with hleft | hright
  · have hdata := D.isRecutOfLeftEqLeft_recut hleft hone hD₁ hD₂
    have hab := D.first.left_ne_right
    have hac : D.first.left ≠ D.second.right := hleft ▸ D.second.left_ne_right
    have hbc : D.first.right ≠ D.second.right := fun h =>
      D.sideColumns_ne_of_hasOneCommonSide hone
        (by simp [GridRectangleBetween.sideColumns, hleft, h])
    obtain ⟨hEr₁, hEr₂⟩ := hdata.recut_sides
    rw [hEr₁, hEr₂, ← hleft]
    rcases hdata.recut_branch with ⟨-, -, hEl₁, hEl₂⟩ | ⟨-, -, hEl₁, hEl₂⟩
    · simpa [hEl₁, hEl₂, rootClifford_swap D.first.right D.second.right,
        rootClifford_swap D.first.left D.first.right] using
        rootClifford_mul_cycle hbc.symm hab.symm hac
    · simpa only [hEl₁, hEl₂, rootClifford_swap D.first.left D.first.right, neg_mul] using
        (rootClifford_mul_cycle hab.symm hac hbc.symm).symm
  · have hdata := D.isRecutOfRightEqRight_recut hright hone hD₁ hD₂
    have hba := D.first.left_ne_right
    have hca : D.second.left ≠ D.first.right := hright ▸ D.second.left_ne_right
    have hcb : D.second.left ≠ D.first.left := fun h =>
      D.sideColumns_ne_of_hasOneCommonSide hone
        (by simp [GridRectangleBetween.sideColumns, hright, h])
    obtain ⟨hEl₁, hEl₂⟩ := hdata.recut_sides
    rw [hEl₁, hEl₂, ← hright]
    rcases hdata.recut_branch with ⟨-, -, hEr₁, hEr₂⟩ | ⟨-, -, hEr₁, hEr₂⟩
    · simpa only [hEr₁, hEr₂, rootClifford_swap D.second.left D.first.right, mul_neg] using
        rootClifford_mul_cycle hcb hba hca.symm
    · simpa [hEr₁, hEr₂, rootClifford_swap D.second.left D.first.right,
        rootClifford_swap D.first.left D.second.left] using
        (rootClifford_mul_cycle hca.symm hcb hba).trans (rootClifford_mul_cycle hcb hba hca.symm)

/-- Recutting a one-common-side empty decomposition negates the Clifford product of its two root
vectors. -/
private theorem rootClifford_recut_eq_neg {n : ℕ} {x z : GridState n}
    (D : GridRectangleDecomposition x z) (hone : D.HasOneCommonSide)
    (hD₁ : D.first.IsEmpty) (hD₂ : D.second.IsEmpty) :
    rootClifford (D.recut hone hD₁ hD₂).first.left (D.recut hone hD₁ hD₂).first.right *
        rootClifford (D.recut hone hD₁ hD₂).second.left (D.recut hone hD₁ hD₂).second.right =
      -(rootClifford D.first.left D.first.right * rootClifford D.second.left D.second.right) := by
  rcases D.hasSameSideOverlap_or_hasMixedSideOverlap hone with hsame | hmixed
  · exact rootClifford_recut_eq_neg_of_hasSameSideOverlap D hone hD₁ hD₂ hsame
  · have hrecut := D.isRecut_recut hone hD₁ hD₂
    have h := rootClifford_recut_eq_neg_of_hasSameSideOverlap (D.recut hone hD₁ hD₂)
      (D.hasOneCommonSide_recut hone hD₁ hD₂) hrecut.isEmpty_first hrecut.isEmpty_second
      ((D.hasSameSideOverlap_recut_iff hone hD₁ hD₂).mpr hmixed)
    rw [D.recut_recut hone hD₁ hD₂] at h
    rw [h, neg_neg]

/-- Any two distinct empty two-step decompositions covering the same multiset of squares have
opposite Clifford products of their root-vector generators. -/
private theorem rootClifford_mul_eq_neg_of_val_add_val_eq_of_ne {n : ℕ} {x z : GridState n}
    {D E : GridRectangleDecomposition x z}
    (hD₁ : D.first.IsEmpty) (hD₂ : D.second.IsEmpty)
    (hE₁ : E.first.IsEmpty) (hE₂ : E.second.IsEmpty) (hne : E ≠ D)
    (hdom : E.first.toGridRectangle.coveredSquares.val +
        E.second.toGridRectangle.coveredSquares.val =
      D.first.toGridRectangle.coveredSquares.val + D.second.toGridRectangle.coveredSquares.val) :
    rootClifford E.first.left E.first.right * rootClifford E.second.left E.second.right =
      -(rootClifford D.first.left D.first.right * rootClifford D.second.left D.second.right) := by
  rcases D.hasDisjointSides_or_hasOneCommonSide_of_ne
      (D.target_ne_source_of_val_add_val_eq_of_ne hne hdom) with hdisj | hone
  · obtain rfl := D.eq_commute_of_val_add_val_eq_of_ne hdisj hE₁ hE₂ hne hdom
    obtain ⟨hll, hlr, hrl, hrr⟩ := D.hasDisjointSides_iff.mp hdisj
    rw [D.commute_first_left hdisj, D.commute_first_right hdisj,
      D.commute_second_left hdisj, D.commute_second_right hdisj]
    exact rootClifford_mul_comm_neg hll.symm hrl.symm hlr.symm hrr.symm
  · obtain rfl := D.eq_recut_of_val_add_val_eq_of_ne hone hD₁ hD₂ hE₁ hne hdom
    exact rootClifford_recut_eq_neg D hone hD₁ hD₂

/-! ### Construction of a `GridSignAssignment n` -/

/-- Existence of a sign assignment for every positive grid size `n`, constructed from any lift of
`GridState n` along `Pin(gridForm n) → O(gridForm n)`. -/
private theorem nonempty_of_neZero (n : ℕ) [NeZero n] : Nonempty (GridSignAssignment n) := by
  have : Nonempty (Fin n) := ⟨⟨0, NeZero.pos n⟩⟩
  choose σ hσ using fun x : GridState n => exists_pinToOrthogonal_eq_permToOrthogonal x.toPerm
  have hrect : ∀ {x y : GridState n} (r : GridRectangleBetween x y),
      ∃! s : ℤˣ, (σ x : CliffordAlgebra (gridForm n)) * rootClifford r.left r.right =
        (s : ℤ) • (σ y : CliffordAlgebra (gridForm n)) := fun {x y} r => by
    have hproj : CliffordAlgebra.pinToOrthogonal (gridForm n)
          (σ x * pinSwap r.left r.right r.left_ne_right) =
        CliffordAlgebra.pinToOrthogonal (gridForm n) (σ y) := by
      rw [map_mul, hσ x, pinToOrthogonal_pinSwap, ← map_mul, hσ y,
        ← GridState.swapColumns_toPerm, ← congrArg GridState.toPerm r.target_eq_swapColumns]
    simpa only [Submonoid.coe_mul, pinSwap] using
      CliffordAlgebra.existsUnique_zsmul_of_pinToOrthogonal_eq (gridForm n)
        (gridForm_nondegenerate n) hproj
  let signFn : ∀ {x y : GridState n} (r : GridRectangleBetween x y), r.IsEmpty → ℤˣ :=
    fun r _ => (hrect r).choose
  have hsign_spec : ∀ {x y : GridState n} (r : GridRectangleBetween x y) (hr : r.IsEmpty),
      (σ x : CliffordAlgebra (gridForm n)) * rootClifford r.left r.right =
        (signFn r hr : ℤ) • (σ y : CliffordAlgebra (gridForm n)) :=
    fun r _ => (hrect r).choose_spec.1
  have htwo_step : ∀ {x y z : GridState n} (r₁ : GridRectangleBetween x y)
      (r₂ : GridRectangleBetween y z) (hr₁ : r₁.IsEmpty) (hr₂ : r₂.IsEmpty),
      (σ x : CliffordAlgebra (gridForm n)) *
          (rootClifford r₁.left r₁.right * rootClifford r₂.left r₂.right) =
        ((signFn r₁ hr₁ * signFn r₂ hr₂ : ℤˣ) : ℤ) •
          (σ z : CliffordAlgebra (gridForm n)) := fun r₁ r₂ hr₁ hr₂ => by
    rw [← mul_assoc, hsign_spec r₁ hr₁, smul_mul_assoc, hsign_spec r₂ hr₂, smul_smul, Units.val_mul]
  refine ⟨{
    sign := signFn
    sign_mul_sign_eq_neg := fun {x z} D E hD₁ hD₂ hE₁ hE₂ hne hdom => by
      refine CliffordAlgebra.zsmul_coe_pinGroup_injective (σ z) ?_
      dsimp only; rw [← htwo_step E.first E.second hE₁ hE₂,
        rootClifford_mul_eq_neg_of_val_add_val_eq_of_ne hD₁ hD₂ hE₁ hE₂ hne hdom, mul_neg,
        htwo_step D.first D.second hD₁ hD₂, Units.val_neg, neg_smul]
    sign_mul_sign_eq_neg_one_of_left_eq_left := fun {x _} r s hr hs hleft => by
      refine CliffordAlgebra.zsmul_coe_pinGroup_injective (σ x) ?_
      dsimp only; rw [← htwo_step r s hr hs, hleft, r.right_eq_right_of_left_eq_left s hleft,
        rootClifford_mul_self r.left_ne_right]; simp
    sign_mul_sign_eq_one_of_left_eq_right := fun {x _} r s hr hs hright => by
      refine CliffordAlgebra.zsmul_coe_pinGroup_injective (σ x) ?_
      dsimp only; rw [← htwo_step r s hr hs, hright, r.right_eq_left_of_left_eq_right s hright,
        rootClifford_mul_swap r.left_ne_right]; simp
  }⟩

/-- **Existence of grid sign assignments** (Manolescu--Ozsváth--Szabó--Thurston; Gallais).
Every grid size `n : ℕ` admits a sign assignment. -/
instance nonempty (n : ℕ) : Nonempty (GridSignAssignment n) := by
  cases n with
  | zero => exact ⟨⟨fun r _ => r.left.elim0, fun D _ _ _ _ _ _ _ => D.first.left.elim0,
      fun r _ _ _ _ => r.left.elim0, fun r _ _ _ _ => r.left.elim0⟩⟩
  | succ m => exact nonempty_of_neZero (m + 1)

end GridSignAssignment

end TauCeti
