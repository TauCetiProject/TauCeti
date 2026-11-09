/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.PadicIntegers
public import TauCeti.LinearAlgebra.BilinearForm.Characteristic
public import TauCeti.LinearAlgebra.BilinearForm.JordanSplitting.Basic
import TauCeti.LinearAlgebra.BilinearForm.Even.Henselian
import TauCeti.LinearAlgebra.BilinearForm.Isometry.Basic
import TauCeti.LinearAlgebra.BilinearForm.JordanSplitting.Replace
import TauCeti.LinearAlgebra.Matrix.BilinearForm
import TauCeti.NumberTheory.Padics.BilinearForm.BinaryDiagonal
import TauCeti.NumberTheory.Padics.BilinearForm.MixedSignWalking.Basic
import TauCeti.NumberTheory.Padics.BilinearForm.MixedSignWalking.EvenLower
import TauCeti.NumberTheory.Padics.BilinearForm.Oddity
import TauCeti.NumberTheory.Padics.DyadicUnits
import TauCeti.NumberTheory.Padics.PadicIntegers
import TauCeti.NumberTheory.Padics.SerreSigns
import TauCeti.RingTheory.Henselian.Basic

/-!
# Sign walking on dyadic Jordan splittings

Let `B` be a symmetric form on a finite free `ℤ_[2]`-module with a Jordan splitting `N` with
respect to `2`, so that `B` is `2 ^ i` times a unimodular form `C i` on `N i`. Write
`U = !![0, 1; 1, 0]` and `V = !![2, 1; 1, 2]`. The Jordan splitting is not determined by `B`, and
in the Conway–Sloane calculus of `2`-adic symbols the freedom is recorded by *sign walking*: the
signs `χ₈(det C i)` of two constituents in the same train can be changed together, the oddity of
each constituent of type I among them changing by `4`. This file proves that sign walking is
available on every Jordan splitting in the following three configurations, which are the steps of
a sign walk that do not pass between two adjacent constituents of type I:

* `N k` of type I and `N (k + 1)` of type II and nonzero
  (`LinearMap.BilinForm.IsJordanSplitting.exists_signWalk_succ_of_odd_of_even`), from
  `⟨a⟩ ⊥ 2 U ≅ ⟨5 a⟩ ⊥ 2 V` and `⟨a⟩ ⊥ 2 V ≅ ⟨5 a⟩ ⊥ 2 U`;
* `N k` of type II and nonzero and `N (k + 1)` of type I
  (`LinearMap.BilinForm.IsJordanSplitting.exists_signWalk_succ_of_even_of_odd`), from
  `U ⊥ ⟨2 a⟩ ≅ V ⊥ ⟨10 a⟩` and `V ⊥ ⟨2 a⟩ ≅ U ⊥ ⟨10 a⟩`;
* `N k` and `N (k + 2)` of type I
  (`LinearMap.BilinForm.IsJordanSplitting.exists_signWalk_add_two_of_odd_of_odd`), from
  `⟨a, 4 b⟩ ≅ ⟨5 a, 20 b⟩`.

In each case there is another Jordan splitting `N'` of `B`, agreeing with `N` away from the two
indices, in which the Gram determinants of the two constituents are multiplied by the nonsquare
unit `5` up to squares, and the oddities of the constituents of type I among them by `4` modulo
`8`. Since `5 ≡ 1` modulo `4` and its sign is `χ₈(5) = -1`, this is the sign walk. The isometries
above concern one or two vectors of each constituent: a vector `x` of `N k` with `B x x = 2 ^ k a`,
`a` a unit, for a constituent of type I, and a pair with Gram matrix `2 ^ k U` or `2 ^ k V` for a
nonzero constituent of type II. These blocks are exchanged by
`LinearMap.BilinForm.IsJordanSplitting.exists_isJordanSplitting_of_span_eq`, which keeps their
orthogonal complements in the two constituents.

Between two adjacent constituents of type I, both signs change together with the oddities in a
different way, `⟨1, 2⟩ ≅ ⟨3, 6⟩`, and this is covered by the classification of `⟨a, 2 b⟩`
(`TauCeti.equivalent_toBilin'_diagonal_two_pow_mul_iff`) rather than by the moves here.

The isometry invariants of a dyadic Jordan splitting, such as the determinant conditions of
`LinearMap.BilinForm.IsJordanSplitting.exists_sq_mul_det_toMatrix_eq_of_equivalent` and the
sign-oddity conditions of
`LinearMap.BilinForm.IsJordanSplitting.prod_χ₈_pow_mul_stdAddChar_sum_eq_of_equivalent`, do not
see these moves. Comparing two Jordan splittings with the same invariants, the moves are what
remove a difference in the sign of a constituent, by walking it to the next constituent of its
train.

## Main results

* `LinearMap.BilinForm.IsJordanSplitting.exists_signWalk_succ_of_odd_of_even`,
  `LinearMap.BilinForm.IsJordanSplitting.exists_signWalk_succ_of_even_of_odd`: sign walking between
  adjacent constituents of different types.
* `LinearMap.BilinForm.IsJordanSplitting.exists_signWalk_add_two_of_odd_of_odd`: sign walking
  between constituents of type I two scales apart.

## References

* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, Chapter 15, §7.5, for
  sign walking.
* D. Allcock, I. Gal and A. Mark, *The Conway–Sloane calculus for 2-adic lattices*, Lemma 4.2.
* O. T. O'Meara, *Introduction to Quadratic Forms*, §93.
-/

public section

open Module
open LinearMap (BilinForm)
open scoped Matrix

namespace LinearMap.BilinForm

variable {M : Type*} [AddCommGroup M] [Module ℤ_[2] M] {B : BilinForm ℤ_[2] M}
  {N : ℕ → Submodule ℤ_[2] M}

/-! ### Vectors of constituents of type I and type II -/

/-- A constituent `N k` of type I has a vector `x` with `B x x = 2 ^ k a` for a unit `a`. -/
private theorem IsJordanSplitting.exists_mem_apply_self_eq_two_pow_mul (h : B.IsJordanSplitting 2 N)
    {k : ℕ} (hodd : ¬∀ x ∈ N k, 2 * 2 ^ k ∣ B x x) :
    ∃ x ∈ N k, ∃ a : ℤ_[2], IsUnit a ∧ B x x = 2 ^ k * a := by
  push Not at hodd
  obtain ⟨x, hx, hndvd⟩ := hodd
  obtain ⟨a, ha⟩ := (h.isModular k).dvd ⟨x, hx⟩ ⟨x, hx⟩
  refine ⟨x, hx, a, by_contra fun hu ↦ hndvd ?_, by simpa using ha⟩
  obtain ⟨c, rfl⟩ := PadicInt.not_isUnit_iff_dvd.mp hu
  exact ⟨c, by simpa [mul_comm, mul_assoc, mul_left_comm] using ha⟩

/-- A nonzero constituent `N k` of type II has a pair `e, f` whose Gram matrix is `2 ^ k` times
`U = !![0, 1; 1, 0]` or `V = !![2, 1; 1, 2]`. -/
private theorem IsJordanSplitting.exists_mem_apply_eq_two_pow [Module.Free ℤ_[2] M]
    [Module.Finite ℤ_[2] M] (h : B.IsJordanSplitting 2 N) (hB : B.IsSymm) {k : ℕ}
    (heven : ∀ x ∈ N k, 2 * 2 ^ k ∣ B x x) (hne : N k ≠ ⊥) :
    ∃ e ∈ N k, ∃ f ∈ N k, B e f = 2 ^ k ∧
      (B e e = 0 ∧ B f f = 0 ∨ B e e = 2 ^ (k + 1) ∧ B f f = 2 ^ (k + 1)) := by
  have h2k : (2 : ℤ_[2]) ^ k ∈ nonZeroDivisors ℤ_[2] :=
    mem_nonZeroDivisors_of_ne_zero (pow_ne_zero k two_ne_zero)
  obtain ⟨C, hC, hCp⟩ := isModular_def.mp (h.isModular k)
  have hBC (y z : N k) : 2 ^ k * C y z = B y z := by
    simpa using LinearMap.congr_fun₂ hC y z
  have hCs : C.IsSymm := IsSymm.of_smul h2k (hC ▸ hB.restrict (N k))
  have hCeven (y : N k) : 2 ∣ C y y := by
    obtain ⟨c, hc⟩ := heven y y.2
    exact ⟨c, (mul_cancel_left_mem_nonZeroDivisors h2k).mp (by
      rw [hBC]; linear_combination hc)⟩
  -- A perfect pairing on a nonzero free module takes the value `1`.
  have := h.free k
  let b := Module.Free.chooseBasis ℤ_[2] (N k)
  have : Nontrivial (N k) := Submodule.nontrivial_iff_ne_bot.mpr hne
  obtain ⟨i⟩ : Nonempty (Module.Free.ChooseBasisIndex ℤ_[2] (N k)) := b.index_nonempty
  obtain ⟨y, hy⟩ := hCp.bijective_left.2 (b.coord i)
  obtain ⟨e, f, hef, hUV⟩ := hCs.exists_hyperbolic_or_exists_two_one_one_two
    (PadicInt.card_residueField 2) hCeven (x := y) (y := b i) (by simp [hy])
  refine ⟨e, e.2, f, f.2, by rw [← hBC, hef, mul_one], ?_⟩
  rcases hUV with ⟨he, hf⟩ | ⟨he, hf⟩
  · exact .inl ⟨by rw [← hBC, he, mul_zero], by rw [← hBC, hf, mul_zero]⟩
  · exact .inr ⟨by rw [← hBC, he, pow_succ], by rw [← hBC, hf, pow_succ]⟩

/-- The range of a triple is the union of the ranges of its first entry and of the other two. -/
private theorem range_three {α : Type*} (z : Fin 3 → α) :
    Set.range ![z 0] ∪ Set.range ![z 1, z 2] = Set.range z := by
  ext y
  simp only [Set.mem_union, Set.mem_range, Fin.exists_fin_succ, Fin.exists_fin_zero]
  simp [Fin.succ_zero_eq_one, Fin.succ_one_eq_two, eq_comm]

/-- Exchanging blocks of the constituents `N k` and `N l` whose Gram determinants change by `5`
up to squares changes the Gram determinants of `N k` and `N l` by `5` up to squares. -/
private theorem IsJordanSplitting.exists_signWalk_aux [Module.Free ℤ_[2] M] [Module.Finite ℤ_[2] M]
    (h : B.IsJordanSplitting 2 N) (hB : B.IsSymm) {k l : ℕ}
    (hkl : k ≠ l) {p q : ℕ} {v v' : Fin p → M} {w w' : Fin q → M}
    {A A' : Matrix (Fin p) (Fin p) ℤ_[2]} {D D' : Matrix (Fin q) (Fin q) ℤ_[2]}
    (hv : ∀ i, v i ∈ N k) (hw : ∀ i, w i ∈ N l)
    (hA : ∀ i j, B (v i) (v j) = 2 ^ k * A i j) (hA' : ∀ i j, B (v' i) (v' j) = 2 ^ k * A' i j)
    (hD : ∀ i j, B (w i) (w j) = 2 ^ l * D i j) (hD' : ∀ i j, B (w' i) (w' j) = 2 ^ l * D' i j)
    (hAu : IsUnit A.det) (hA'u : IsUnit A'.det) (hDu : IsUnit D.det) (hD'u : IsUnit D'.det)
    (hvw' : ∀ i j, B (v' i) (w' j) = 0)
    (hspan : Submodule.span ℤ_[2] (Set.range v' ∪ Set.range w') =
      Submodule.span ℤ_[2] (Set.range v ∪ Set.range w))
    (h5A : IsSquare (5 * A.det * A'.det)) (h5D : IsSquare (5 * D.det * D'.det)) :
    ∃ N' : ℕ → Submodule ℤ_[2] M, B.IsJordanSplitting 2 N' ∧
      (∀ i, i ≠ k → i ≠ l → N' i = N i) ∧
      (∀ (n : ℕ) (d : Basis (Fin n) ℤ_[2] (N k)) (d' : Basis (Fin n) ℤ_[2] (N' k)),
        IsSquare (5 * ((B.restrict (N k)).toMatrix d).det *
          ((B.restrict (N' k)).toMatrix d').det)) ∧
      (∀ (n : ℕ) (d : Basis (Fin n) ℤ_[2] (N l)) (d' : Basis (Fin n) ℤ_[2] (N' l)),
        IsSquare (5 * ((B.restrict (N l)).toMatrix d).det *
          ((B.restrict (N' l)).toMatrix d').det)) ∧
      (∃ (m : ℕ) (t : Fin m → M) (G : Matrix (Fin m) (Fin m) ℤ_[2]),
        (∀ i j, B (t i) (t j) = 2 ^ k * G i j) ∧ IsUnit G.det ∧ (∀ i j, B (v i) (t j) = 0) ∧
        (∀ i j, B (v' i) (t j) = 0) ∧ N k = Submodule.span ℤ_[2] (Set.range (Sum.elim v t)) ∧
        N' k = Submodule.span ℤ_[2] (Set.range (Sum.elim v' t))) ∧
      (∃ (m : ℕ) (s : Fin m → M) (H : Matrix (Fin m) (Fin m) ℤ_[2]),
        (∀ i j, B (s i) (s j) = 2 ^ l * H i j) ∧ IsUnit H.det ∧ (∀ i j, B (w i) (s j) = 0) ∧
        (∀ i j, B (w' i) (s j) = 0) ∧ N l = Submodule.span ℤ_[2] (Set.range (Sum.elim w s)) ∧
        N' l = Submodule.span ℤ_[2] (Set.range (Sum.elim w' s))) := by
  have h2 : (2 : ℤ_[2]) ∈ nonZeroDivisors ℤ_[2] := mem_nonZeroDivisors_of_ne_zero two_ne_zero
  obtain ⟨N', hN', hagree, ⟨m, t, G, hG, hGu, hvt, hv't, hNk, hN'k⟩,
    ⟨m', s, H, hH, hHu, hws, hw's, hNl, hN'l⟩⟩ :=
    h.exists_isJordanSplitting_of_span_eq hB h2 hkl hv hw hA hA' hD hD' hAu hA'u hDu hD'u hvw' hspan
  exact ⟨N', hN', hagree,
    fun n d d' ↦ isSquare_mul_det_mul_det_of_eq_span hB.isRefl (pow_mem h2 k) hA hA' hG hvt hv't
      hAu hA'u hGu h5A hNk hN'k d d',
    fun n d d' ↦ isSquare_mul_det_mul_det_of_eq_span hB.isRefl (pow_mem h2 l) hD hD' hH hws hw's
      hDu hD'u hHu h5D hNl hN'l d d',
    ⟨m, t, G, hG, hGu, hvt, hv't, hNk, hN'k⟩, ⟨m', s, H, hH, hHu, hws, hw's, hNl, hN'l⟩⟩

/-- `5 det U det V = -15` is a square in `ℤ_[2]`. -/
private theorem isSquare_five_mul_det_hyperbolic_mul_det_anisotropic :
    IsSquare (5 * (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℤ_[2]).det *
      (!![2, 1; 1, 2] : Matrix (Fin 2) (Fin 2) ℤ_[2]).det) := by
  have hu : IsUnit (-15 : ℤ_[2]) := by
    rw [PadicInt.isUnit_iff_toZModPow_three_mul_self, map_neg, map_ofNat]
    decide
  have := (PadicInt.isSquare_mul_iff_toZModPow_three_eq hu isUnit_one).mpr
    (by rw [map_neg, map_ofNat, map_one]; decide)
  rw [Matrix.det_fin_two_of, Matrix.det_fin_two_of]
  convert this using 1
  ring

/-- The hyperbolic plane `U` is unimodular. -/
private theorem isUnit_det_hyperbolic :
    IsUnit (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℤ_[2]).det := by
  simp [Matrix.det_fin_two_of]

/-- The anisotropic plane `V`, of determinant `3`, is unimodular. -/
private theorem isUnit_det_anisotropic :
    IsUnit (!![2, 1; 1, 2] : Matrix (Fin 2) (Fin 2) ℤ_[2]).det := by
  rw [Matrix.det_fin_two_of, PadicInt.isUnit_iff_toZModPow_three_mul_self]
  simp only [map_sub, map_mul, map_one, map_ofNat]
  decide

/-- The range of a pair is the union of the ranges of its two entries. -/
private theorem range_two {α : Type*} (z : Fin 2 → α) :
    Set.range ![z 0] ∪ Set.range ![z 1] = Set.range z := by
  ext y
  simp only [Set.mem_union, Set.mem_range, Fin.exists_fin_succ, Fin.exists_fin_zero]
  simp [Fin.succ_zero_eq_one, eq_comm]

/-- For a unit `a` of `ℤ_[2]`, a change of oddity by `5 a - a` is a change by `4` modulo `8`. -/
private theorem eight_dvd_sub_sub_four {a : ℤ_[2]} (ha : IsUnit a) {c : ℤ_[2]}
    (h : (8 : ℤ_[2]) ∣ c - (5 * a - a)) : (8 : ℤ_[2]) ∣ c - 4 := by
  have h4 : (8 : ℤ_[2]) ∣ 4 - 4 * a := by
    rw [PadicInt.eight_dvd_sub_iff_toZModPow_three_eq, map_mul, map_ofNat]
    have hA := PadicInt.isUnit_iff_toZModPow_three_mul_self.mp ha
    generalize PadicInt.toZModPow 3 a = A at hA ⊢
    revert A
    decide
  rw [show c - 4 = c - (5 * a - a) - (4 - 4 * a) by ring]
  exact dvd_sub h h4

/-- Exchanging a vector `x` of `N u` with `B x x = 2 ^ u a` and a pair `e, f` of `N p` with Gram
matrix `2 ^ p D` for vectors `z'` with Gram matrix `⟨2 ^ u 5 a⟩ ⊥ 2 ^ p D'`, spanning the same
submodule, is a sign walk between `N u` and `N p` when `5 det D det D'` is a square. -/
private theorem IsJordanSplitting.exists_signWalk_unary_binary [Module.Free ℤ_[2] M]
    [Module.Finite ℤ_[2] M] (h : B.IsJordanSplitting 2 N) (hB : B.IsSymm) {u p : ℕ}
    (hup : u ≠ p) {x e f : M} (hx : x ∈ N u) (he : e ∈ N p) (hf : f ∈ N p) {a : ℤ_[2]}
    (ha : IsUnit a) (hxx : B x x = 2 ^ u * a) {z' : Fin 3 → M}
    {D D' : Matrix (Fin 2) (Fin 2) ℤ_[2]}
    (hD : ∀ i j, B (![e, f] i) (![e, f] j) = 2 ^ p * D i j)
    (hD' : ∀ i j, B (![z' 1, z' 2] i) (![z' 1, z' 2] j) = 2 ^ p * D' i j) (hDu : IsUnit D.det)
    (hD'u : IsUnit D'.det) (h5D : IsSquare (5 * D.det * D'.det))
    (hz'0 : B (z' 0) (z' 0) = 2 ^ u * (5 * a)) (hz'1 : B (z' 0) (z' 1) = 0)
    (hz'2 : B (z' 0) (z' 2) = 0)
    (hspan : Submodule.span ℤ_[2] (Set.range z') = Submodule.span ℤ_[2] (Set.range ![x, e, f])) :
    ∃ N' : ℕ → Submodule ℤ_[2] M, B.IsJordanSplitting 2 N' ∧
      (∀ i, i ≠ u → i ≠ p → N' i = N i) ∧
      (∀ (n : ℕ) (d : Basis (Fin n) ℤ_[2] (N u)) (d' : Basis (Fin n) ℤ_[2] (N' u)),
        IsSquare (5 * ((B.restrict (N u)).toMatrix d).det *
          ((B.restrict (N' u)).toMatrix d').det)) ∧
      (∀ (n : ℕ) (d : Basis (Fin n) ℤ_[2] (N p)) (d' : Basis (Fin n) ℤ_[2] (N' p)),
        IsSquare (5 * ((B.restrict (N p)).toMatrix d).det *
          ((B.restrict (N' p)).toMatrix d').det)) ∧
      ∀ (C : BilinForm ℤ_[2] (N u)) (C' : BilinForm ℤ_[2] (N' u)) (w : N u) (w' : N' u),
        (2 : ℤ_[2]) ^ u • C = B.restrict (N u) → (2 : ℤ_[2]) ^ u • C' = B.restrict (N' u) →
        C.IsCharacteristic w → C'.IsCharacteristic w' → (8 : ℤ_[2]) ∣ C' w' w' - C w w - 4 := by
  have h5a : IsUnit (5 * a) := TauCeti.isUnit_five_padicInt.mul ha
  have hspan' : Submodule.span ℤ_[2] (Set.range ![z' 0] ∪ Set.range ![z' 1, z' 2]) =
      Submodule.span ℤ_[2] (Set.range ![x] ∪ Set.range ![e, f]) := by
    rw [range_three z', hspan, ← range_three ![x, e, f]]
    rfl
  have h5A : IsSquare (5 * (!![a] : Matrix (Fin 1) (Fin 1) ℤ_[2]).det * (!![5 * a]).det) :=
    ⟨5 * a, by rw [Matrix.det_fin_one_of, Matrix.det_fin_one_of]⟩
  obtain ⟨N', hN', hagree, hdu, hdp, ⟨m, t, G, hG, hGu, hvt, hv't, hNu, hN'u⟩, -⟩ :=
    h.exists_signWalk_aux hB hup (v := ![x]) (v' := ![z' 0]) (w := ![e, f])
      (w' := ![z' 1, z' 2]) (A := !![a]) (A' := !![5 * a]) (fun i ↦ by fin_cases i; exact hx)
      (fun i ↦ by fin_cases i <;> assumption)
      (fun i j ↦ by fin_cases i; fin_cases j; simpa using hxx)
      (fun i j ↦ by fin_cases i; fin_cases j; simpa using hz'0) hD hD'
      (by simpa using ha) (by simpa using h5a) hDu hD'u
      (fun i j ↦ by fin_cases i; fin_cases j <;> simp [hz'1, hz'2]) hspan' h5A h5D
  refine ⟨N', hN', hagree, hdu, hdp, fun C C' w w' hC hC' hw hw' ↦ ?_⟩
  exact eight_dvd_sub_sub_four ha (hB.eight_dvd_sub_sub_of_eq_span hxx hz'0 hG
    (fun j ↦ by simpa using hvt 0 j) (fun j ↦ by simpa using hv't 0 j) ha h5a hGu hNu hN'u hC hC'
    hw hw')

/-- **Sign walking from a constituent of type I to the constituent of type II above it.** Let `N`
be a Jordan splitting with respect to `2` of a symmetric form `B` on a finite free `ℤ_[2]`-module.
Suppose that `N k` is of type I, that is, some `B x x` with `x ∈ N k` is not divisible by
`2 * 2 ^ k`, and that `N (k + 1)` is nonzero and of type II. Then `B` has a Jordan splitting `N'`
agreeing with `N` away from `k` and `k + 1`, in which the Gram determinants of the constituents of
indices `k` and `k + 1` are multiplied by `5` up to squares, and the oddity of the unimodular
rescaling of the constituent of index `k` changes by `4` modulo `8`. In the language of
Conway–Sloane symbols, the signs of both constituents change. The underlying isometry is
`⟨a⟩ ⊥ 2 !![0, 1; 1, 0] ≅ ⟨5 a⟩ ⊥ 2 !![2, 1; 1, 2]`
(`TauCeti.equivalent_toBilin'_unary_two_hyperbolic`), or its reverse. -/
theorem IsJordanSplitting.exists_signWalk_succ_of_odd_of_even [Module.Free ℤ_[2] M]
    [Module.Finite ℤ_[2] M] (h : B.IsJordanSplitting 2 N) (hB : B.IsSymm) {k : ℕ}
    (hodd : ¬∀ x ∈ N k, 2 * 2 ^ k ∣ B x x) (heven : ∀ x ∈ N (k + 1), 2 * 2 ^ (k + 1) ∣ B x x)
    (hne : N (k + 1) ≠ ⊥) :
    ∃ N' : ℕ → Submodule ℤ_[2] M, B.IsJordanSplitting 2 N' ∧
      (∀ i, i ≠ k → i ≠ k + 1 → N' i = N i) ∧
      (∀ (n : ℕ) (d : Basis (Fin n) ℤ_[2] (N k)) (d' : Basis (Fin n) ℤ_[2] (N' k)),
        IsSquare (5 * ((B.restrict (N k)).toMatrix d).det *
          ((B.restrict (N' k)).toMatrix d').det)) ∧
      (∀ (n : ℕ) (d : Basis (Fin n) ℤ_[2] (N (k + 1))) (d' : Basis (Fin n) ℤ_[2] (N' (k + 1))),
        IsSquare (5 * ((B.restrict (N (k + 1))).toMatrix d).det *
          ((B.restrict (N' (k + 1))).toMatrix d').det)) ∧
      ∀ (C : BilinForm ℤ_[2] (N k)) (C' : BilinForm ℤ_[2] (N' k)) (w : N k) (w' : N' k),
        (2 : ℤ_[2]) ^ k • C = B.restrict (N k) → (2 : ℤ_[2]) ^ k • C' = B.restrict (N' k) →
        C.IsCharacteristic w → C'.IsCharacteristic w' → (8 : ℤ_[2]) ∣ C' w' w' - C w w - 4 := by
  obtain ⟨x, hx, a, ha, hxx⟩ := h.exists_mem_apply_self_eq_two_pow_mul hodd
  obtain ⟨e, he, f, hf, hef, hUV⟩ := h.exists_mem_apply_eq_two_pow hB heven hne
  have hxe : B x e = 0 := h.apply_eq_zero k (k + 1) (by omega) x hx e he
  have hxf : B x f = 0 := h.apply_eq_zero k (k + 1) (by omega) x hx f hf
  -- Walk `⟨a⟩ ⊥ 2 U` to `⟨5 a⟩ ⊥ 2 V`, or `⟨a⟩ ⊥ 2 V` to `⟨5 a⟩ ⊥ 2 U`.
  obtain ⟨z', D, D', hD, hD', hDu, hD'u, h5D, hz'0, hz'1, hz'2, hspan⟩ :
      ∃ (z' : Fin 3 → M) (D D' : Matrix (Fin 2) (Fin 2) ℤ_[2]),
        (∀ i j, B (![e, f] i) (![e, f] j) = 2 ^ (k + 1) * D i j) ∧
        (∀ i j, B (![z' 1, z' 2] i) (![z' 1, z' 2] j) = 2 ^ (k + 1) * D' i j) ∧
        IsUnit D.det ∧ IsUnit D'.det ∧ IsSquare (5 * D.det * D'.det) ∧
        B (z' 0) (z' 0) = 2 ^ k * (5 * a) ∧ B (z' 0) (z' 1) = 0 ∧ B (z' 0) (z' 2) = 0 ∧
        Submodule.span ℤ_[2] (Set.range z') = Submodule.span ℤ_[2] (Set.range ![x, e, f]) := by
    have h1 : (2 : ℤ_[2]) ^ (k + 1) = 2 ^ k * 2 := pow_succ 2 k
    have h2 : (2 : ℤ_[2]) ^ (k + 1 + 1) = 2 ^ k * 4 := by ring
    rcases hUV with ⟨hee, hff⟩ | ⟨hee, hff⟩
    · obtain ⟨z', hz', hspan⟩ := exists_span_range_eq_of_equivalent_toBilin' (B := B)
        (v := ![x, e, f])
        (fun i j ↦ by
          fin_cases i <;> fin_cases j <;>
            simp [hxx, hxe, hxf, hef, hee, hff, hB.eq e x, hB.eq f x, hB.eq f e, h1])
        (TauCeti.equivalent_toBilin'_unary_two_hyperbolic k ha)
      refine ⟨z', !![0, 1; 1, 0], !![2, 1; 1, 2], fun i j ↦ ?_, fun i j ↦ ?_,
        isUnit_det_hyperbolic, isUnit_det_anisotropic,
        isSquare_five_mul_det_hyperbolic_mul_det_anisotropic, by simpa using hz' 0 0,
        by simpa using hz' 0 1, by simpa using hz' 0 2, hspan⟩
      · fin_cases i <;> fin_cases j <;> simp [hef, hee, hff, hB.eq f e]
      · fin_cases i <;> fin_cases j <;> simp [hz', h1] <;> ring
    · obtain ⟨z', hz', hspan⟩ := exists_span_range_eq_of_equivalent_toBilin' (B := B)
        (v := ![x, e, f])
        (fun i j ↦ by
          fin_cases i <;> fin_cases j <;>
            simp [hxx, hxe, hxf, hef, hee, hff, hB.eq e x, hB.eq f x, hB.eq f e, h1, h2])
        (TauCeti.equivalent_toBilin'_unary_two_anisotropic k ha)
      refine ⟨z', !![2, 1; 1, 2], !![0, 1; 1, 0], fun i j ↦ ?_, fun i j ↦ ?_,
        isUnit_det_anisotropic, isUnit_det_hyperbolic,
        by simpa only [mul_right_comm] using isSquare_five_mul_det_hyperbolic_mul_det_anisotropic,
        by simpa using hz' 0 0, by simpa using hz' 0 1, by simpa using hz' 0 2, hspan⟩
      · fin_cases i <;> fin_cases j <;> simp [hef, hee, hff, hB.eq f e, h1] <;> ring
      · fin_cases i <;> fin_cases j <;> simp [hz', h1]
  exact h.exists_signWalk_unary_binary hB (by omega) hx he hf ha hxx hD hD' hDu hD'u h5D hz'0
    hz'1 hz'2 hspan

/-- **Sign walking from a constituent of type II to the constituent of type I above it.** Let `N`
be a Jordan splitting with respect to `2` of a symmetric form `B` on a finite free `ℤ_[2]`-module.
Suppose that `N k` is nonzero and of type II, that is, `2 * 2 ^ k` divides `B x x` for `x ∈ N k`,
and that `N (k + 1)` is of type I. Then `B` has a Jordan splitting `N'` agreeing with `N` away from
`k` and `k + 1`, in which the Gram determinants of the constituents of indices `k` and `k + 1` are
multiplied by `5` up to squares, and the oddity of the unimodular rescaling of the constituent of
index `k + 1` changes by `4` modulo `8`. The underlying isometry is
`!![0, 1; 1, 0] ⊥ ⟨2 a⟩ ≅ !![2, 1; 1, 2] ⊥ ⟨10 a⟩`
(`TauCeti.equivalent_toBilin'_two_unary_hyperbolic`), or its reverse. -/
theorem IsJordanSplitting.exists_signWalk_succ_of_even_of_odd [Module.Free ℤ_[2] M]
    [Module.Finite ℤ_[2] M] (h : B.IsJordanSplitting 2 N) (hB : B.IsSymm) {k : ℕ}
    (heven : ∀ x ∈ N k, 2 * 2 ^ k ∣ B x x) (hne : N k ≠ ⊥)
    (hodd : ¬∀ x ∈ N (k + 1), 2 * 2 ^ (k + 1) ∣ B x x) :
    ∃ N' : ℕ → Submodule ℤ_[2] M, B.IsJordanSplitting 2 N' ∧
      (∀ i, i ≠ k → i ≠ k + 1 → N' i = N i) ∧
      (∀ (n : ℕ) (d : Basis (Fin n) ℤ_[2] (N k)) (d' : Basis (Fin n) ℤ_[2] (N' k)),
        IsSquare (5 * ((B.restrict (N k)).toMatrix d).det *
          ((B.restrict (N' k)).toMatrix d').det)) ∧
      (∀ (n : ℕ) (d : Basis (Fin n) ℤ_[2] (N (k + 1))) (d' : Basis (Fin n) ℤ_[2] (N' (k + 1))),
        IsSquare (5 * ((B.restrict (N (k + 1))).toMatrix d).det *
          ((B.restrict (N' (k + 1))).toMatrix d').det)) ∧
      ∀ (C : BilinForm ℤ_[2] (N (k + 1))) (C' : BilinForm ℤ_[2] (N' (k + 1))) (w : N (k + 1))
        (w' : N' (k + 1)), (2 : ℤ_[2]) ^ (k + 1) • C = B.restrict (N (k + 1)) →
        (2 : ℤ_[2]) ^ (k + 1) • C' = B.restrict (N' (k + 1)) →
        C.IsCharacteristic w → C'.IsCharacteristic w' → (8 : ℤ_[2]) ∣ C' w' w' - C w w - 4 := by
  obtain ⟨x, hx, a, ha, hxx⟩ := h.exists_mem_apply_self_eq_two_pow_mul hodd
  obtain ⟨e, he, f, hf, hef, hUV⟩ := h.exists_mem_apply_eq_two_pow hB heven hne
  have hxe : B x e = 0 := h.apply_eq_zero (k + 1) k (by omega) x hx e he
  have hxf : B x f = 0 := h.apply_eq_zero (k + 1) k (by omega) x hx f hf
  have h1 : (2 : ℤ_[2]) ^ (k + 1) = 2 ^ k * 2 := pow_succ 2 k
  -- Walk `U ⊥ ⟨2 a⟩` to `V ⊥ ⟨10 a⟩`, or `V ⊥ ⟨2 a⟩` to `U ⊥ ⟨10 a⟩`.
  obtain ⟨z', D, D', hD, hD', hDu, hD'u, h5D, hz'0, hz'1, hz'2, hspan⟩ :
      ∃ (z' : Fin 3 → M) (D D' : Matrix (Fin 2) (Fin 2) ℤ_[2]),
        (∀ i j, B (![e, f] i) (![e, f] j) = 2 ^ k * D i j) ∧
        (∀ i j, B (![z' 1, z' 2] i) (![z' 1, z' 2] j) = 2 ^ k * D' i j) ∧
        IsUnit D.det ∧ IsUnit D'.det ∧ IsSquare (5 * D.det * D'.det) ∧
        B (z' 0) (z' 0) = 2 ^ (k + 1) * (5 * a) ∧ B (z' 0) (z' 1) = 0 ∧ B (z' 0) (z' 2) = 0 ∧
        Submodule.span ℤ_[2] (Set.range z') = Submodule.span ℤ_[2] (Set.range ![x, e, f]) := by
    rcases hUV with ⟨hee, hff⟩ | ⟨hee, hff⟩
    · obtain ⟨z', hz', hspan⟩ := exists_span_range_eq_of_equivalent_toBilin' (B := B)
        (v := ![x, e, f])
        (fun i j ↦ by
          fin_cases i <;> fin_cases j <;>
            simp [hxx, hxe, hxf, hef, hee, hff, hB.eq e x, hB.eq f x, hB.eq f e, h1]
          ring)
        (TauCeti.equivalent_toBilin'_two_unary_hyperbolic k ha)
      have hz'00 : B (z' 0) (z' 0) = 2 ^ k * (10 * a) := by simpa using hz' 0 0
      refine ⟨z', !![0, 1; 1, 0], !![2, 1; 1, 2], fun i j ↦ ?_, fun i j ↦ ?_,
        isUnit_det_hyperbolic, isUnit_det_anisotropic,
        isSquare_five_mul_det_hyperbolic_mul_det_anisotropic,
        by rw [h1]; linear_combination hz'00, by simpa using hz' 0 1, by simpa using hz' 0 2,
        hspan⟩
      · fin_cases i <;> fin_cases j <;> simp [hef, hee, hff, hB.eq f e]
      · fin_cases i <;> fin_cases j <;> simp [hz']
    · obtain ⟨z', hz', hspan⟩ := exists_span_range_eq_of_equivalent_toBilin' (B := B)
        (v := ![x, e, f])
        (fun i j ↦ by
          fin_cases i <;> fin_cases j <;>
            simp [hxx, hxe, hxf, hef, hee, hff, hB.eq e x, hB.eq f x, hB.eq f e, h1]
          ring)
        (TauCeti.equivalent_toBilin'_two_unary_anisotropic k ha)
      have hz'00 : B (z' 0) (z' 0) = 2 ^ k * (10 * a) := by simpa using hz' 0 0
      refine ⟨z', !![2, 1; 1, 2], !![0, 1; 1, 0], fun i j ↦ ?_, fun i j ↦ ?_,
        isUnit_det_anisotropic, isUnit_det_hyperbolic,
        by simpa only [mul_right_comm] using isSquare_five_mul_det_hyperbolic_mul_det_anisotropic,
        by rw [h1]; linear_combination hz'00, by simpa using hz' 0 1, by simpa using hz' 0 2,
        hspan⟩
      · fin_cases i <;> fin_cases j <;> simp [hef, hee, hff, hB.eq f e, h1]
      · fin_cases i <;> fin_cases j <;> simp [hz']
  obtain ⟨N', hN', hagree, hdu, hdp, hodd'⟩ := h.exists_signWalk_unary_binary hB (by omega) hx he
    hf ha hxx hD hD' hDu hD'u h5D hz'0 hz'1 hz'2 hspan
  exact ⟨N', hN', fun i hik hik' ↦ hagree i hik' hik, hdp, hdu, hodd'⟩

/-- **Sign walking between constituents of type I two scales apart.** Let `N` be a Jordan splitting
with respect to `2` of a symmetric form `B` on a finite free `ℤ_[2]`-module, with `N k` and
`N (k + 2)` of type I; the constituent `N (k + 1)` is arbitrary. Then `B` has a Jordan splitting
`N'` agreeing with `N` away from `k` and `k + 2`, in which the Gram determinants of the
constituents of indices `k` and `k + 2` are multiplied by `5` up to squares, and the oddities of
their unimodular rescalings change by `4` modulo `8`. The underlying isometry is
`⟨a, 4 b⟩ ≅ ⟨5 a, 20 b⟩` (`TauCeti.equivalent_toBilin'_diagonal_four_mul_five_mul`). -/
theorem IsJordanSplitting.exists_signWalk_add_two_of_odd_of_odd [Module.Free ℤ_[2] M]
    [Module.Finite ℤ_[2] M] (h : B.IsJordanSplitting 2 N) (hB : B.IsSymm) {k : ℕ}
    (hodd : ¬∀ x ∈ N k, 2 * 2 ^ k ∣ B x x)
    (hodd' : ¬∀ x ∈ N (k + 2), 2 * 2 ^ (k + 2) ∣ B x x) :
    ∃ N' : ℕ → Submodule ℤ_[2] M, B.IsJordanSplitting 2 N' ∧
      (∀ i, i ≠ k → i ≠ k + 2 → N' i = N i) ∧
      (∀ (n : ℕ) (d : Basis (Fin n) ℤ_[2] (N k)) (d' : Basis (Fin n) ℤ_[2] (N' k)),
        IsSquare (5 * ((B.restrict (N k)).toMatrix d).det *
          ((B.restrict (N' k)).toMatrix d').det)) ∧
      (∀ (n : ℕ) (d : Basis (Fin n) ℤ_[2] (N (k + 2))) (d' : Basis (Fin n) ℤ_[2] (N' (k + 2))),
        IsSquare (5 * ((B.restrict (N (k + 2))).toMatrix d).det *
          ((B.restrict (N' (k + 2))).toMatrix d').det)) ∧
      (∀ (C : BilinForm ℤ_[2] (N k)) (C' : BilinForm ℤ_[2] (N' k)) (w : N k) (w' : N' k),
        (2 : ℤ_[2]) ^ k • C = B.restrict (N k) → (2 : ℤ_[2]) ^ k • C' = B.restrict (N' k) →
        C.IsCharacteristic w → C'.IsCharacteristic w' → (8 : ℤ_[2]) ∣ C' w' w' - C w w - 4) ∧
      ∀ (C : BilinForm ℤ_[2] (N (k + 2))) (C' : BilinForm ℤ_[2] (N' (k + 2))) (w : N (k + 2))
        (w' : N' (k + 2)), (2 : ℤ_[2]) ^ (k + 2) • C = B.restrict (N (k + 2)) →
        (2 : ℤ_[2]) ^ (k + 2) • C' = B.restrict (N' (k + 2)) →
        C.IsCharacteristic w → C'.IsCharacteristic w' → (8 : ℤ_[2]) ∣ C' w' w' - C w w - 4 := by
  obtain ⟨x, hx, a, ha, hxx⟩ := h.exists_mem_apply_self_eq_two_pow_mul hodd
  obtain ⟨y, hy, b, hb, hyy⟩ := h.exists_mem_apply_self_eq_two_pow_mul hodd'
  have hxy : B x y = 0 := h.apply_eq_zero k (k + 2) (by omega) x hx y hy
  have h5a : IsUnit (5 * a) := TauCeti.isUnit_five_padicInt.mul ha
  have h5b : IsUnit (5 * b) := TauCeti.isUnit_five_padicInt.mul hb
  have h2 : (2 : ℤ_[2]) ^ (k + 2) = 2 ^ k * 4 := by ring
  -- Walk `⟨a⟩ ⊥ ⟨4 b⟩` to `⟨5 a⟩ ⊥ ⟨20 b⟩`, at the scale `2 ^ k`.
  have hwalk : (Matrix.toBilin' ((2 : ℤ_[2]) ^ k • Matrix.diagonal ![a, 4 * b])).Equivalent
      (Matrix.toBilin' ((2 : ℤ_[2]) ^ k • Matrix.diagonal ![5 * a, 4 * (5 * b)])) := by
    simp only [map_smul]
    exact (equivalent_smul_iff (mem_nonZeroDivisors_of_ne_zero (pow_ne_zero k two_ne_zero))).mpr
      (TauCeti.equivalent_toBilin'_diagonal_four_mul_five_mul ha hb)
  obtain ⟨z', hz', hspan⟩ := exists_span_range_eq_of_equivalent_toBilin' (B := B) (v := ![x, y])
    (fun i j ↦ by
      fin_cases i <;> fin_cases j <;> simp [hxx, hyy, hxy, hB.eq y x, h2]; ring) hwalk
  have hspan' : Submodule.span ℤ_[2] (Set.range ![z' 0] ∪ Set.range ![z' 1]) =
      Submodule.span ℤ_[2] (Set.range ![x] ∪ Set.range ![y]) := by
    rw [range_two z', hspan, ← range_two ![x, y]]
    rfl
  have hz'0 : B (z' 0) (z' 0) = 2 ^ k * (5 * a) := by simpa using hz' 0 0
  have hz'1 : B (z' 1) (z' 1) = 2 ^ (k + 2) * (5 * b) := by
    simpa [h2, mul_assoc] using hz' 1 1
  have h5 (c : ℤ_[2]) :
      IsSquare (5 * (!![c] : Matrix (Fin 1) (Fin 1) ℤ_[2]).det * (!![5 * c]).det) :=
    ⟨5 * c, by rw [Matrix.det_fin_one_of, Matrix.det_fin_one_of]⟩
  obtain ⟨N', hN', hagree, hdk, hdl, ⟨m, t, G, hG, hGu, hvt, hv't, hNk, hN'k⟩,
    ⟨m', s, H, hH, hHu, hws, hw's, hNl, hN'l⟩⟩ :=
    h.exists_signWalk_aux hB (k := k) (l := k + 2) (by omega) (v := ![x]) (v' := ![z' 0])
      (w := ![y]) (w' := ![z' 1]) (A := !![a]) (A' := !![5 * a]) (D := !![b]) (D' := !![5 * b])
      (fun i ↦ by fin_cases i; exact hx) (fun i ↦ by fin_cases i; exact hy)
      (fun i j ↦ by fin_cases i; fin_cases j; simpa using hxx)
      (fun i j ↦ by fin_cases i; fin_cases j; simpa using hz'0)
      (fun i j ↦ by fin_cases i; fin_cases j; simpa using hyy)
      (fun i j ↦ by fin_cases i; fin_cases j; simpa using hz'1)
      (by simpa using ha) (by simpa using h5a) (by simpa using hb) (by simpa using h5b)
      (fun i j ↦ by fin_cases i; fin_cases j; simpa using hz' 0 1) hspan' (h5 a) (h5 b)
  refine ⟨N', hN', hagree, hdk, hdl, fun C C' w w' hC hC' hw hw' ↦ ?_,
    fun C C' w w' hC hC' hw hw' ↦ ?_⟩
  · exact eight_dvd_sub_sub_four ha (hB.eight_dvd_sub_sub_of_eq_span hxx hz'0 hG
      (fun j ↦ by simpa using hvt 0 j) (fun j ↦ by simpa using hv't 0 j) ha h5a hGu hNk hN'k hC
      hC' hw hw')
  · exact eight_dvd_sub_sub_four hb (hB.eight_dvd_sub_sub_of_eq_span hyy hz'1 hH
      (fun j ↦ by simpa using hws 0 j) (fun j ↦ by simpa using hw's 0 j) hb h5b hHu hNl hN'l hC
      hC' hw hw')

end LinearMap.BilinForm
