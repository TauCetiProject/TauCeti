/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.CyclicCohomology.Matrix
public import TauCeti.RingTheory.HochschildCohomology.Complex
import Mathlib.LinearAlgebra.Multilinear.Curry
import Mathlib.Tactic.LinearCombination
import TauCeti.Data.Fin.Basic

/-!
# Matrix Morita invariance of Hochschild cohomology

Let `B` be a unital algebra and `(x, y)` a *frame* of `B`: finitely many pairs of elements with
`∑ c, x c * y c = 1`. Conjugation of cochains by the frame,

`(θψ)(a₀, …, aₙ) = ∑ ψ(y p₀ a₀ x p₁, y p₁ a₁ x p₂, …, y pₙ aₙ x p₀)`,

summed over the closed paths `p` of indices, is chain homotopic to the identity on the Hochschild
cochain complex. The homotopy `H = ∑ⱼ (-1)ʲ Hⱼ` evaluates a cochain on the tuples

`hⱼ(a₀, …, aₙ) = (a₀ x k₀, y k₀ a₁ x k₁, …, y kⱼ₋₁ aⱼ x kⱼ, y kⱼ, aⱼ₊₁, …, aₙ)`,

summed over `k₀, …, kⱼ`. These satisfy the presimplicial homotopy identities against the
Hochschild faces: a face merging two conjugated entries removes the index between them, because
`∑ c, x c * y c = 1`, and the other faces commute with the `hⱼ` up to a shift. The zeroth face
of `h₀` is the identity and the last face of `hₙ` is `θ`, so `bH + Hb = 1 - θ`.

For the matrix algebra `B = Matrix ι ι A` over a unital algebra `A` and the matrix units
`x c = E_cr`, `y c = E_rc` of a fixed column and row `r`, the conjugate `y p · a · x q` is the
entry `a p q` placed at `(r, r)`. So `θ` is the matrix extension `φ ↦ φ#Tr` of
`TauCeti.matrixCochainExtension` composed with restriction of cochains to the corner
`a ↦ a E_rr`. That restriction is a left inverse of matrix extension, and the homotopy makes it a
right inverse on cohomology: matrix extension induces a bijection
`HHⁿ(A, Hom_R(A, M)) → HHⁿ(Matrix ι ι A, Hom_R(Matrix ι ι A, M))` in every degree, for every
nonempty finite `ι`. This is the Hochschild input to Morita invariance of cyclic cohomology for
matrices, which follows along the SBI sequence.

Inside the proofs, tuples of algebra elements and of indices are handled as sequences indexed by
`ℕ`, so that the faces and the homotopy tuples are explicit case distinctions on natural numbers.

## Main definitions

* `TauCeti.frameCochainConjugation`: conjugation `θ` of cochains by a frame.
* `TauCeti.frameCochainHomotopy`: the homotopy `H` from the identity to `θ`.
* `TauCeti.hochschildCohomology.matrixExtension`: the map on Hochschild cohomology induced by
  matrix extension.

## Main results

* `TauCeti.hochschildCoboundary_frameCochainHomotopy_add_frameCochainHomotopy_hochschildCoboundary`
  and `TauCeti.frameCochainHomotopy_hochschildCoboundary_zero`: `bH + Hb = 1 - θ`, and `Hb = 1 - θ`
  in degree zero.
* `TauCeti.hochschildCoboundary_frameCochainConjugation`: frame conjugation is a cochain map.
* `TauCeti.frameCochainConjugation_single`: for matrix units, frame conjugation is matrix
  extension after corner restriction.
* `TauCeti.hochschildCohomology.bijective_matrixExtension`: matrix Morita invariance of
  Hochschild cohomology.

## References

* J.-L. Loday, *Cyclic Homology*, Grundlehren der mathematischen Wissenschaften 301, Springer
  (1998), §1.2 (Morita invariance of Hochschild homology for matrices).
* A. Connes, *Non-commutative differential geometry*, Publ. Math. IHÉS 62 (1985), Part II.
-/

public section

namespace TauCeti

section NatTuple

variable {B ι : Type*}

/-- The face multiplying the adjacent entries `l` and `l + 1` of a tuple indexed by `ℕ`. -/
private def natFace [Mul B] (l : ℕ) (g : ℕ → B) (t : ℕ) : B :=
  if t < l then g t else if t = l then g l * g (l + 1) else g (t + 1)

/-- The last face `(gₘ g₀, g₁, …, gₘ₋₁)` of a tuple `(g₀, …, gₘ)` indexed by `ℕ`. -/
private def natLastFace [Mul B] (m : ℕ) (g : ℕ → B) (t : ℕ) : B :=
  if t = 0 then g m * g 0 else g t

private theorem hochschildFace_castSucc_val [Mul B] {m : ℕ} (l : Fin (m + 1)) (g : ℕ → B) :
    hochschildFace l.castSucc (fun s : Fin (m + 2) ↦ g s) =
      fun t : Fin (m + 1) ↦ natFace l g t := by
  funext t
  simp only [hochschildFace_castSucc, Fin.contractNth, natFace, Fin.val_castSucc, Fin.val_succ]
  split_ifs with h₁ h₂ <;> first | rfl | rw [h₂]

private theorem hochschildFace_last_val [Mul B] {m : ℕ} (g : ℕ → B) :
    hochschildFace (Fin.last (m + 1)) (fun s : Fin (m + 2) ↦ g s) =
      fun t : Fin (m + 1) ↦ natLastFace (m + 1) g t := by
  rw [hochschildFace_last]
  funext t
  cases t using Fin.cases <;> simp [natLastFace]

private theorem insertNth_val {m : ℕ} (p : Fin (m + 1)) (v : B) (f : ℕ → B) (t : Fin (m + 1)) :
    p.insertNth (α := fun _ ↦ B) v (fun s : Fin m ↦ f s) t =
      if (t : ℕ) < p then f t else if (t : ℕ) = p then v else f (t - 1) := by
  cases t using Fin.succAboveCases p with
  | x => simp
  | p s =>
    rw [Fin.insertNth_apply_succAbove, Fin.val_succAbove]
    split_ifs with h₁ h₂ h₃ <;> simp_all <;> omega

/-- The left factors `1, y κ₀, y κ₁, …` of the homotopy tuples. -/
private def natLeft [One B] (y : ι → B) (κ : ℕ → ι) (t : ℕ) : B :=
  if t = 0 then 1 else y (κ (t - 1))

/-- The tuple `(g₀ x κ₀, y κ₀ g₁ x κ₁, …, y κⱼ₋₁ gⱼ x κⱼ, y κⱼ, gⱼ₊₁, gⱼ₊₂, …)` indexed by `ℕ`. -/
private def natHomotopy [Mul B] [One B] (x y : ι → B) (j : ℕ) (κ : ℕ → ι) (g : ℕ → B)
    (t : ℕ) : B :=
  if t ≤ j then natLeft y κ t * g t * x (κ t) else if t = j + 1 then y (κ j) else g (t - 1)

/-- The homotopy tuple only depends on the indices `κ₀, …, κⱼ`. -/
private theorem natHomotopy_congr [Mul B] [One B] (x y : ι → B) {j : ℕ} {κ κ' : ℕ → ι}
    (h : ∀ t ≤ j, κ t = κ' t) (g : ℕ → B) : natHomotopy x y j κ g = natHomotopy x y j κ' g := by
  funext t
  simp only [natHomotopy, natLeft]
  split_ifs with h₁ h₂ h₃
  · rw [h t h₁]
  · rw [h t h₁, h (t - 1) (by omega)]
  · rw [h j le_rfl]
  · rfl

/-- A tuple of indices `(k₀, …, kⱼ)` extended to `ℕ` by repeating its last entry. -/
private def clampIndex {j : ℕ} (k : Fin (j + 1) → ι) (t : ℕ) : ι :=
  k ⟨min t j, by omega⟩

private theorem clampIndex_val {j : ℕ} (k : Fin (j + 1) → ι) (t : Fin (j + 1)) :
    clampIndex k t = k t := by
  simp [clampIndex, Nat.min_eq_left (Nat.le_of_lt_succ t.2)]

private theorem clampIndex_self {j : ℕ} (k : Fin (j + 1) → ι) :
    clampIndex k j = k (Fin.last j) := by
  simp [clampIndex, Fin.last]

/-- Insert the index `c` at position `l` of a sequence of indices. -/
private def natInsert (l : ℕ) (c : ι) (κ : ℕ → ι) (t : ℕ) : ι :=
  if t < l then κ t else if t = l then c else κ (t - 1)

private theorem clampIndex_insertNth {j : ℕ} (l : Fin (j + 2)) (c : ι) (k : Fin (j + 1) → ι)
    {t : ℕ} (ht : t ≤ j + 1) :
    clampIndex (l.insertNth c k) t = natInsert l c (clampIndex k) t := by
  have hk : k = fun s : Fin (j + 1) ↦ clampIndex k s := funext fun s ↦ (clampIndex_val k s).symm
  have ht' : min t (j + 1) = t := Nat.min_eq_left ht
  rw [clampIndex]
  conv_lhs => rw [hk]
  rw [insertNth_val]
  simp only [ht', natInsert]

/-- The `l`-th Hochschild face of a tuple `(g₀, …, gₘ)` indexed by `ℕ`. -/
private def natFaceAt [Mul B] (m l : ℕ) (g : ℕ → B) : ℕ → B :=
  if l < m then natFace l g else natLastFace m g

private theorem natFaceAt_of_lt [Mul B] {m l : ℕ} (h : l < m) (g : ℕ → B) :
    natFaceAt m l g = natFace l g :=
  ite_eq_left h

private theorem natFaceAt_self [Mul B] (m : ℕ) (g : ℕ → B) : natFaceAt m m g = natLastFace m g :=
  ite_eq_right (lt_irrefl m)

private theorem hochschildFace_val [Mul B] {m : ℕ} (l : Fin (m + 2)) (g : ℕ → B) :
    hochschildFace l (fun s : Fin (m + 2) ↦ g s) =
      fun t : Fin (m + 1) ↦ natFaceAt (m + 1) l g t := by
  induction l using Fin.lastCases with
  | last =>
    rw [hochschildFace_last_val]
    simp [natFaceAt]
  | cast l =>
    rw [hochschildFace_castSucc_val]
    simp [natFaceAt, l.2]

variable [Monoid B] (x y : ι → B)

/-- A face merging two entries of a homotopy tuple below its inserted entry removes the index
between them. -/
private theorem natFace_natHomotopy_natInsert {l j : ℕ} (hlj : l ≤ j) (c : ι) (κ : ℕ → ι)
    (g : ℕ → B) :
    natFace l (natHomotopy x y (j + 1) (natInsert l c κ) g) = fun t ↦
      if t = l then natLeft y κ l * g l * x c * (y c * (g (l + 1) * x (κ l)))
      else natHomotopy x y j κ (natFace l g) t := by
  funext t
  rcases lt_trichotomy t l with h | rfl | h <;> rcases lt_trichotomy t (j + 1) with h' | h' | h' <;>
    first | omega | simp (disch := omega) only [natFace, natHomotopy, natLeft, natInsert,
      ite_eq_left, ite_eq_right, ite_true, Nat.add_sub_cancel, Nat.sub_add_cancel, mul_assoc, h']

/-- The face merging the last conjugated entry with the inserted entry removes its index. -/
private theorem natFace_natHomotopy_natInsert_self {l : ℕ} (hl : 1 ≤ l) (c : ι) (κ : ℕ → ι)
    (g : ℕ → B) :
    natFace l (natHomotopy x y l (natInsert l c κ) g) = fun t ↦
      if t = l then natLeft y κ l * g l * x c * (y c * 1)
      else natFace l (natHomotopy x y (l - 1) κ g) t := by
  funext t
  rcases lt_trichotomy t l with h | rfl | h <;>
    first | omega | simp (disch := omega) only [natFace, natHomotopy, natLeft, natInsert,
      ite_eq_left, ite_eq_right, ite_true, Nat.add_sub_cancel, Nat.sub_add_cancel, mul_assoc,
      mul_one]

/-- A face beyond the inserted entry of a homotopy tuple commutes with the homotopy. -/
private theorem natFace_natHomotopy {l j : ℕ} (hjl : j + 1 < l) (κ : ℕ → ι) (g : ℕ → B) :
    natFace l (natHomotopy x y j κ g) = natHomotopy x y j κ (natFace (l - 1) g) := by
  funext t
  rcases lt_trichotomy t (j + 1) with h | h | h <;> rcases lt_trichotomy t l with h' | h' | h' <;>
    first | omega | simp (disch := omega) only [natFace, natHomotopy, ite_eq_left, ite_eq_right,
      ite_true, Nat.add_sub_cancel, Nat.sub_add_cancel, h, h']

/-- The last face of a homotopy tuple not reaching the last entry commutes with the homotopy. -/
private theorem natLastFace_natHomotopy {m j : ℕ} (hjm : j < m) (κ : ℕ → ι) (g : ℕ → B) :
    natLastFace (m + 1) (natHomotopy x y j κ g) = natHomotopy x y j κ (natLastFace m g) := by
  funext t
  rcases Nat.eq_zero_or_pos t with h | h <;> rcases lt_trichotomy t (j + 1) with h' | h' | h' <;>
    first | omega | simp (disch := omega) only [natLastFace, natHomotopy, natLeft, ite_eq_left,
      ite_eq_right, ite_true, Nat.add_sub_cancel, mul_assoc, one_mul, h, h']

/-- The zeroth face of the zeroth homotopy tuple merges its first two entries. -/
private theorem natFace_zero_natHomotopy_zero (κ : ℕ → ι) (g : ℕ → B) :
    natFace 0 (natHomotopy x y 0 κ g) = fun t ↦
      if t = 0 then 1 * g 0 * x (κ 0) * (y (κ 0) * 1) else g t := by
  funext t
  rcases Nat.eq_zero_or_pos t with h | h <;>
    simp (disch := omega) only [natFace, natHomotopy, natLeft, ite_eq_left, ite_eq_right,
      ite_true, Nat.add_sub_cancel, mul_one, h]

end NatTuple

/-! ### Signs of presimplicial homotopies -/

section Signs

variable {M : Type*} [AddCommGroup M]

private theorem neg_one_pow_succ_smul_add (m : ℕ) (a : M) :
    (-1 : ℤ) ^ (m + 1) • a + (-1 : ℤ) ^ m • a = 0 := by
  rw [pow_succ, mul_neg_one, neg_smul, neg_add_cancel]

/-- Peel the last row and column off a double sum over two ranges. -/
private theorem sum_range_succ_sum_range_succ (F : ℕ → ℕ → M) (a b : ℕ) :
    ∑ j ∈ Finset.range (a + 1), ∑ l ∈ Finset.range (b + 1), F l j =
      ∑ j ∈ Finset.range a, ∑ l ∈ Finset.range b, F l j + ∑ j ∈ Finset.range a, F b j +
        ∑ l ∈ Finset.range (b + 1), F l a := by
  rw [Finset.sum_range_succ _ a]
  congr 1
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ ↦ Finset.sum_range_succ _ _

/-- The last column of the `D`-sum of a presimplicial homotopy cancels the last column of its
`E`-sum, up to one term. -/
private theorem sum_last_column (N : ℕ) (D E : ℕ → ℕ → M)
    (hc : ∀ j, j ≤ N → D (N + 2) j = E j (N + 1)) :
    ∑ j ∈ Finset.range (N + 1), (-1 : ℤ) ^ (N + 2 + j) • D (N + 2) j +
      ∑ j ∈ Finset.range N, (-1 : ℤ) ^ (N + 1 + j) • E j (N + 1) = E N (N + 1) := by
  have hs : ∑ j ∈ Finset.range N, ((-1 : ℤ) ^ (N + 2 + j) • D (N + 2) j +
      (-1 : ℤ) ^ (N + 1 + j) • E j (N + 1)) = 0 := by
    refine Finset.sum_eq_zero fun j hj ↦ ?_
    rw [hc j (by simp at hj; omega), show N + 2 + j = N + 1 + j + 1 by omega]
    exact neg_one_pow_succ_smul_add _ _
  rw [Finset.sum_range_succ, hc N le_rfl, add_right_comm, ← Finset.sum_add_distrib, hs,
    zero_add, Even.neg_one_pow ⟨N + 1, by omega⟩, one_smul]

/-- The last row of the `D`-sum of a presimplicial homotopy cancels the last row of its `E`-sum,
up to three terms. -/
private theorem sum_last_row (N : ℕ) (D E : ℕ → ℕ → M) (ha : ∀ l, l < N + 1 → D l (N + 1) = E N l)
    (hb : D (N + 1) (N + 1) = D (N + 1) N) :
    ∑ l ∈ Finset.range (N + 3), (-1 : ℤ) ^ (l + (N + 1)) • D l (N + 1) +
      ∑ l ∈ Finset.range (N + 2), (-1 : ℤ) ^ (l + N) • E N l =
        D (N + 1) N - D (N + 2) (N + 1) - E N (N + 1) := by
  have hs : ∑ l ∈ Finset.range (N + 1), (-1 : ℤ) ^ (l + (N + 1)) • D l (N + 1) +
      ∑ l ∈ Finset.range (N + 1), (-1 : ℤ) ^ (l + N) • E N l = 0 := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun l hl ↦ ?_
    rw [ha l (by simpa using hl), ← add_assoc]
    exact neg_one_pow_succ_smul_add _ _
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ (fun l ↦ _ • E N l), hb,
    Even.neg_one_pow ⟨N + 1, rfl⟩, Odd.neg_one_pow ⟨N + 1, by omega⟩,
    Odd.neg_one_pow ⟨N, by omega⟩, ← sub_eq_zero, ← hs]
  simp only [one_smul, neg_smul]
  abel

/-- The sign bookkeeping of a presimplicial homotopy: if `D l j` (the `l`-th face after the
`j`-th homotopy operator) and `E j l` (the `j`-th homotopy operator after the `l`-th face) satisfy
the presimplicial homotopy identities, then the alternating double sums of `D` and `E` add up to
`D 0 0 - D (N + 1) N`. -/
private theorem sum_presimplicial_homotopy (N : ℕ) (D E : ℕ → ℕ → M)
    (ha : ∀ l j, l < j → j ≤ N → D l j = E (j - 1) l)
    (hb : ∀ l, 1 ≤ l → l ≤ N → D l l = D l (l - 1))
    (hc : ∀ l j, j + 1 < l → l ≤ N + 1 → D l j = E j (l - 1)) :
    ∑ j ∈ Finset.range (N + 1), ∑ l ∈ Finset.range (N + 2), (-1 : ℤ) ^ (l + j) • D l j +
      ∑ j ∈ Finset.range N, ∑ l ∈ Finset.range (N + 1), (-1 : ℤ) ^ (l + j) • E j l =
      D 0 0 - D (N + 1) N := by
  induction N with
  | zero => simp [Finset.sum_range_succ, sub_eq_add_neg]
  | succ N ih =>
    have ih := ih (fun l j h hj ↦ ha l j h (by omega)) (fun l h hl ↦ hb l h (by omega))
      (fun l j h hl ↦ hc l j h (by omega))
    have h₁ := sum_last_column N D E fun j hj ↦ hc (N + 2) j (by omega) le_rfl
    have h₂ := sum_last_row N D E (fun l hl ↦ ha l (N + 1) hl le_rfl)
      (hb (N + 1) (by omega) le_rfl)
    rw [sum_range_succ_sum_range_succ _ (N + 1) (N + 2),
      sum_range_succ_sum_range_succ (fun l j ↦ (-1 : ℤ) ^ (l + j) • E j l) N (N + 1)]
    linear_combination (norm := abel) ih + h₁ + h₂

end Signs

/-! ### Frame conjugation and its homotopy to the identity -/

section Frame

variable {R B M ι : Type*} [CommSemiring R] [Semiring B] [Module R B] [IsScalarTower R B B]
  [SMulCommClass R B B] [Fintype ι] (x y : ι → B)

section AddCommMonoid

variable [AddCommMonoid M] [Module R M]

variable (R M) in
/-- Conjugation of cochains by the frame `(x, y)`:
`(θ ψ)(a₀, …, aₙ) = ∑ ψ(y p₀ a₀ x p₁, y p₁ a₁ x p₂, …, y pₙ aₙ x p₀)`, the sum over all closed
paths `p` of indices. When `∑ c, x c * y c = 1` it is homotopic to the identity
(`TauCeti.hochschildCoboundary_frameCochainHomotopy_add_frameCochainHomotopy_hochschildCoboundary`).
-/
noncomputable def frameCochainConjugation (n : ℕ) :
    MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ B) M →ₗ[R]
      MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ B) M where
  toFun ψ := ∑ p : Fin (n + 1) → ι,
    ψ.compLinearMap fun j ↦ LinearMap.mulLeftRight R (y (p j), x (p (finRotate (n + 1) j)))
  map_add' ψ φ := by
    ext a
    simp [MultilinearMap.compLinearMap_apply, Finset.sum_add_distrib]
  map_smul' c ψ := by
    ext a
    simp [MultilinearMap.compLinearMap_apply, Finset.smul_sum]

/-- The closed-path formula for frame conjugation. -/
@[simp]
theorem frameCochainConjugation_apply (n : ℕ)
    (ψ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ B) M) (a : Fin (n + 1) → B) :
    frameCochainConjugation R M x y n ψ a =
      ∑ p : Fin (n + 1) → ι, ψ (fun j ↦ y (p j) * a j * x (p (finRotate (n + 1) j))) := by
  simp [frameCochainConjugation, MultilinearMap.compLinearMap_apply]

/-- The left and right factors of the `s`-th entry of a homotopy tuple. -/
private def homotopyPair {j : ℕ} (k : Fin (j + 1) → ι) (s : ℕ) : B × B :=
  if s ≤ j then (natLeft y (clampIndex k) s, x (clampIndex k s)) else (1, 1)

variable (R) in
/-- The term `ψ ↦ ψ ∘ hⱼ` of the homotopy for the index tuple `k`, where
`hⱼ(a₀, …, aₙ) = (a₀ x k₀, y k₀ a₁ x k₁, …, y kⱼ₋₁ aⱼ x kⱼ, y kⱼ, aⱼ₊₁, …, aₙ)`. -/
private noncomputable def homotopyTerm {n : ℕ} (j : Fin (n + 1)) (k : Fin (j + 1) → ι)
    (ψ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 2) ↦ B) M) :
    MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ B) M :=
  (MultilinearMap.curryMid (M := fun _ : Fin (n + 2) ↦ B) j.succ ψ
    (y (k (Fin.last j)))).compLinearMap fun s ↦ LinearMap.mulLeftRight R (homotopyPair x y k s)

omit [Fintype ι] in
private theorem homotopyTerm_val {n : ℕ} (j : Fin (n + 1)) (k : Fin (j + 1) → ι)
    (ψ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 2) ↦ B) M) (g : ℕ → B) :
    homotopyTerm R x y j k ψ (fun s ↦ g s) =
      ψ (fun t ↦ natHomotopy x y j (clampIndex k) g t) := by
  simp only [homotopyTerm, MultilinearMap.compLinearMap_apply,
    MultilinearMap.curryMid_apply_apply]
  congr 1
  funext t
  rw [insertNth_val j.succ _ (fun s ↦ LinearMap.mulLeftRight R (homotopyPair x y k s) (g s))]
  simp only [natHomotopy, homotopyPair, Fin.val_succ]
  split_ifs <;> first | rfl | omega | simp [clampIndex_self]

omit [IsScalarTower R B B] [SMulCommClass R B B] in
/-- A sum over an index `c` of a cochain whose `l`-th argument contains `x c * y c` collapses to
a single evaluation when `∑ c, x c * y c = 1`. -/
private theorem sum_apply_collapse (hxy : ∑ c, x c * y c = 1) {m : ℕ}
    (ψ : MultilinearMap (RingHom.id R) (fun _ : Fin m ↦ B) M) (T : ℕ → B) {l : ℕ} (hl : l < m)
    (u v : B) (huv : T l = u * v) :
    ∑ c, ψ (fun t : Fin m ↦ if (t : ℕ) = l then u * x c * (y c * v) else T t) =
      ψ (fun t ↦ T t) := by
  have h (c : ι) : (fun t : Fin m ↦ if (t : ℕ) = l then u * x c * (y c * v) else T t) =
      Function.update (fun t : Fin m ↦ T t) ⟨l, hl⟩ (u * x c * (y c * v)) := by
    funext t
    rcases eq_or_ne t ⟨l, hl⟩ with rfl | ht
    · simp
    · simp [Function.update_of_ne ht, Fin.val_ne_of_ne ht]
  have hsum : ∑ c, u * x c * (y c * v) = T l := by
    simp only [← mul_assoc, ← Finset.sum_mul]
    simp only [mul_assoc u, ← Finset.mul_sum, hxy, mul_one, huv]
  simp only [h, ← MultilinearMap.map_update_sum, hsum]
  exact congrArg ψ (Function.update_eq_self_iff.2 rfl)

end AddCommMonoid

section AddCommGroup

variable [AddCommGroup M] [Module R M]

variable (R M) in
/-- The homotopy `H : Cⁿ⁺¹ → Cⁿ` from the identity to frame conjugation:
`(Hψ)(a₀, …, aₙ) = ∑ⱼ (-1)ʲ ∑ ψ(a₀ x k₀, y k₀ a₁ x k₁, …, y kⱼ₋₁ aⱼ x kⱼ, y kⱼ, aⱼ₊₁, …, aₙ)`,
the inner sum over the index tuples `k = (k₀, …, kⱼ)`. It is the transpose of the classical
homotopy for Morita invariance of Hochschild homology. -/
noncomputable def frameCochainHomotopy (n : ℕ) :
    MultilinearMap (RingHom.id R) (fun _ : Fin (n + 2) ↦ B) M →ₗ[R]
      MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ B) M where
  toFun ψ := ∑ j : Fin (n + 1), (-1 : ℤ) ^ (j : ℕ) •
    ∑ k : Fin (j + 1) → ι, homotopyTerm R x y j k ψ
  map_add' ψ φ := by
    ext a
    simp [homotopyTerm, MultilinearMap.compLinearMap_apply, MultilinearMap.curryMid_apply_apply,
      Finset.sum_add_distrib]
  map_smul' c ψ := by
    ext a
    simp [homotopyTerm, MultilinearMap.compLinearMap_apply, MultilinearMap.curryMid_apply_apply,
      Finset.smul_sum, smul_comm c]

private theorem frameCochainHomotopy_val (n : ℕ)
    (ψ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 2) ↦ B) M) (g : ℕ → B) :
    frameCochainHomotopy R M x y n ψ (fun s ↦ g s) =
      ∑ j ∈ Finset.range (n + 1), (-1 : ℤ) ^ j •
        ∑ k : Fin (j + 1) → ι, ψ (fun t ↦ natHomotopy x y j (clampIndex k) g t) := by
  simp only [frameCochainHomotopy, LinearMap.coe_mk, AddHom.coe_mk, sum_apply, smul_apply,
    homotopyTerm_val]
  exact Fin.sum_univ_eq_sum_range (fun j ↦ (-1 : ℤ) ^ j •
    ∑ k : Fin (j + 1) → ι, ψ (fun t ↦ natHomotopy x y j (clampIndex k) g t)) (n + 1)

omit [Fintype ι] in
private theorem hochschildCoboundary_val (n : ℕ)
    (ψ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ B) M) (g : ℕ → B) :
    hochschildCoboundary R B M n ψ (fun s ↦ g s) =
      ∑ l ∈ Finset.range (n + 2), (-1 : ℤ) ^ l • ψ (fun t ↦ natFaceAt (n + 1) l g t) := by
  rw [hochschildCoboundary_apply]
  simp only [hochschildFace_val]
  exact Fin.sum_univ_eq_sum_range
    (fun l ↦ (-1 : ℤ) ^ l • ψ (fun t : Fin (n + 1) ↦ natFaceAt (n + 1) l g t)) (n + 2)

/-- The sum over index tuples of `ψ` on the `l`-th face of the `j`-th homotopy tuple. -/
private noncomputable def faceHomotopySum {m : ℕ}
    (ψ : MultilinearMap (RingHom.id R) (fun _ : Fin (m + 1) ↦ B) M) (g : ℕ → B) (l j : ℕ) : M :=
  ∑ k : Fin (j + 1) → ι, ψ (fun t ↦ natFaceAt (m + 1) l (natHomotopy x y j (clampIndex k) g) t)

/-- The sum over index tuples of `ψ` on the `j`-th homotopy tuple of the `l`-th face. -/
private noncomputable def homotopyFaceSum {m : ℕ}
    (ψ : MultilinearMap (RingHom.id R) (fun _ : Fin (m + 1) ↦ B) M) (g : ℕ → B) (j l : ℕ) : M :=
  ∑ k : Fin (j + 1) → ι, ψ (fun t ↦ natHomotopy x y j (clampIndex k) (natFaceAt m l g) t)

private theorem frameCochainHomotopy_hochschildCoboundary_val (m : ℕ)
    (ψ : MultilinearMap (RingHom.id R) (fun _ : Fin (m + 1) ↦ B) M) (g : ℕ → B) :
    frameCochainHomotopy R M x y m (hochschildCoboundary R B M m ψ) (fun s ↦ g s) =
      ∑ j ∈ Finset.range (m + 1), ∑ l ∈ Finset.range (m + 2),
        (-1 : ℤ) ^ (l + j) • faceHomotopySum x y ψ g l j := by
  rw [frameCochainHomotopy_val]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  simp only [hochschildCoboundary_val, faceHomotopySum, Finset.smul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ ↦ Finset.sum_congr rfl fun k _ ↦ ?_
  rw [smul_smul, ← pow_add, add_comm]

private theorem hochschildCoboundary_frameCochainHomotopy_val (n : ℕ)
    (ψ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 2) ↦ B) M) (g : ℕ → B) :
    hochschildCoboundary R B M n (frameCochainHomotopy R M x y n ψ) (fun s ↦ g s) =
      ∑ j ∈ Finset.range (n + 1), ∑ l ∈ Finset.range (n + 2),
        (-1 : ℤ) ^ (l + j) • homotopyFaceSum x y ψ g j l := by
  rw [hochschildCoboundary_val]
  simp only [frameCochainHomotopy_val, homotopyFaceSum, Finset.smul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun l _ ↦
    Finset.sum_congr rfl fun k _ ↦ ?_
  rw [smul_smul, ← pow_add]

variable {x y}

omit [IsScalarTower R B B] [SMulCommClass R B B] in
/-- A face below the inserted entry of a homotopy tuple removes an index. -/
private theorem faceHomotopySum_of_lt (hxy : ∑ c, x c * y c = 1) {m : ℕ}
    (ψ : MultilinearMap (RingHom.id R) (fun _ : Fin (m + 1) ↦ B) M) (g : ℕ → B) {l j : ℕ}
    (hlj : l < j) (hjm : j ≤ m) :
    faceHomotopySum x y ψ g l j = homotopyFaceSum x y ψ g (j - 1) l := by
  obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  simp (disch := omega) only [faceHomotopySum, homotopyFaceSum, Nat.add_sub_cancel, natFaceAt_of_lt]
  rw [← (Fin.insertNthEquiv (fun _ ↦ ι) ⟨l, by omega⟩).sum_comp, Fintype.sum_prod_type,
    Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  simp only [Fin.insertNthEquiv_apply]
  have key (c : ι) : (fun t : Fin (m + 1) ↦ natFace l (natHomotopy x y (j + 1)
      (clampIndex (Fin.insertNth (⟨l, by omega⟩ : Fin (j + 2)) c k)) g) t) =
      fun t : Fin (m + 1) ↦ if (t : ℕ) = l then
        natLeft y (clampIndex k) l * g l * x c * (y c * (g (l + 1) * x (clampIndex k l)))
      else natHomotopy x y j (clampIndex k) (natFace l g) t := by
    rw [natHomotopy_congr x y (fun t ht ↦ clampIndex_insertNth _ c k ht) g,
      natFace_natHomotopy_natInsert x y (by omega)]
  simp only [key]
  refine sum_apply_collapse x y hxy ψ _ (by omega) _ _ ?_
  simp (disch := omega) only [natHomotopy, natFace, ite_eq_left, ite_eq_right, ite_true,
    mul_assoc]

omit [IsScalarTower R B B] [SMulCommClass R B B] in
/-- The face merging the last conjugated entry with the inserted entry of a homotopy tuple removes
the last index. -/
private theorem faceHomotopySum_self (hxy : ∑ c, x c * y c = 1) {m : ℕ}
    (ψ : MultilinearMap (RingHom.id R) (fun _ : Fin (m + 1) ↦ B) M) (g : ℕ → B) {l : ℕ}
    (hl : 1 ≤ l) (hlm : l ≤ m) :
    faceHomotopySum x y ψ g l l = faceHomotopySum x y ψ g l (l - 1) := by
  obtain ⟨l, rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by omega⟩
  simp (disch := omega) only [faceHomotopySum, Nat.add_sub_cancel, natFaceAt_of_lt]
  rw [← (Fin.insertNthEquiv (fun _ ↦ ι) (Fin.last (l + 1))).sum_comp, Fintype.sum_prod_type,
    Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  simp only [Fin.insertNthEquiv_apply]
  have key (c : ι) : (fun t : Fin (m + 1) ↦ natFace (l + 1) (natHomotopy x y (l + 1)
      (clampIndex (Fin.insertNth (Fin.last (l + 1)) c k)) g) t) =
      fun t : Fin (m + 1) ↦ if (t : ℕ) = l + 1 then
        natLeft y (clampIndex k) (l + 1) * g (l + 1) * x c * (y c * 1)
      else natFace (l + 1) (natHomotopy x y l (clampIndex k) g) t := by
    rw [natHomotopy_congr x y (fun t ht ↦ clampIndex_insertNth _ c k ht) g, Fin.val_last,
      natFace_natHomotopy_natInsert_self x y (by omega), Nat.add_sub_cancel]
  simp only [key]
  refine sum_apply_collapse x y hxy ψ _ (by omega) _ _ ?_
  simp (disch := omega) only [natHomotopy, natFace, natLeft, ite_eq_left, ite_eq_right,
    ite_true, Nat.add_sub_cancel, mul_one]

omit [IsScalarTower R B B] [SMulCommClass R B B] in
/-- A face beyond the inserted entry of a homotopy tuple commutes with the homotopy. -/
private theorem faceHomotopySum_of_add_one_lt {m : ℕ}
    (ψ : MultilinearMap (RingHom.id R) (fun _ : Fin (m + 1) ↦ B) M) (g : ℕ → B) {l j : ℕ}
    (hjl : j + 1 < l) (hlm : l ≤ m + 1) :
    faceHomotopySum x y ψ g l j = homotopyFaceSum x y ψ g j (l - 1) := by
  simp only [faceHomotopySum, homotopyFaceSum]
  rcases hlm.lt_or_eq with hlm | rfl
  · simp (disch := omega) only [natFaceAt_of_lt, natFace_natHomotopy x y hjl]
  · simp only [Nat.add_sub_cancel, natFaceAt_self, natLastFace_natHomotopy x y (by omega : j < m)]

omit [IsScalarTower R B B] [SMulCommClass R B B] in
/-- The zeroth face of the zeroth homotopy tuple gives back the original tuple. -/
private theorem faceHomotopySum_zero_zero (hxy : ∑ c, x c * y c = 1) {m : ℕ}
    (ψ : MultilinearMap (RingHom.id R) (fun _ : Fin (m + 1) ↦ B) M) (g : ℕ → B) :
    faceHomotopySum x y ψ g 0 0 = ψ (fun t ↦ g t) := by
  simp only [faceHomotopySum, natFaceAt_of_lt m.succ_pos]
  rw [← (Equiv.funUnique (Fin 1) ι).symm.sum_comp]
  have key (c : ι) : (fun t : Fin (m + 1) ↦ natFace 0 (natHomotopy x y 0
      (clampIndex ((Equiv.funUnique (Fin 1) ι).symm c)) g) t) =
      fun t : Fin (m + 1) ↦ if (t : ℕ) = 0 then 1 * g 0 * x c * (y c * 1)
      else g t := by
    have hκ : clampIndex ((Equiv.funUnique (Fin 1) ι).symm c) = fun _ ↦ c := by
      funext t
      simp [clampIndex]
    rw [hκ, natFace_zero_natHomotopy_zero]
  simp only [key]
  exact sum_apply_collapse x y hxy ψ _ m.succ_pos _ _ (by simp)

/-- The last face of the last homotopy tuple is frame conjugation. -/
private theorem faceHomotopySum_last {m : ℕ}
    (ψ : MultilinearMap (RingHom.id R) (fun _ : Fin (m + 1) ↦ B) M) (g : ℕ → B) :
    faceHomotopySum x y ψ g (m + 1) m = frameCochainConjugation R M x y m ψ (fun t ↦ g t) := by
  simp only [frameCochainConjugation_apply, faceHomotopySum, natFaceAt_self]
  conv_rhs => rw [← (Equiv.arrowCongr (finRotate (m + 1)) (Equiv.refl ι)).sum_comp]
  refine Finset.sum_congr rfl fun k _ ↦ congrArg ψ (funext fun t ↦ ?_)
  simp only [Equiv.arrowCongr_apply, Equiv.coe_refl, Function.comp_apply, id,
    Equiv.symm_apply_apply]
  cases t using Fin.cases with
  | zero =>
    rw [Fin.finRotate_symm_zero, ← clampIndex_self k, ← clampIndex_val k 0]
    simp [natLastFace, natHomotopy, natLeft, mul_assoc]
  | succ t =>
    rw [Fin.finRotate_symm_succ, ← clampIndex_val k t.succ, ← clampIndex_val k t.castSucc]
    simp [natLastFace, natHomotopy, natLeft]

/-- Every tuple is the restriction of a sequence indexed by `ℕ`. -/
private theorem exists_eq_val {m : ℕ} (a : Fin m → B) : ∃ g : ℕ → B, a = fun s : Fin m ↦ g s :=
  ⟨fun t ↦ if h : t < m then a ⟨t, h⟩ else 0, funext fun s : Fin m ↦ by simp [s.2]⟩

/-- In degree zero, `H(bψ) = ψ - θψ`: frame conjugation is homotopic to the identity. -/
theorem frameCochainHomotopy_hochschildCoboundary_zero (hxy : ∑ c, x c * y c = 1)
    (ψ : MultilinearMap (RingHom.id R) (fun _ : Fin 1 ↦ B) M) :
    frameCochainHomotopy R M x y 0 (hochschildCoboundary R B M 0 ψ) =
      ψ - frameCochainConjugation R M x y 0 ψ := by
  ext a
  obtain ⟨g, rfl⟩ := exists_eq_val a
  have h := sum_presimplicial_homotopy 0 (faceHomotopySum x y ψ g) (fun _ _ ↦ 0)
    (fun l j hlj hj ↦ by omega) (fun l hl hl' ↦ by omega)
    (fun l j hjl hl ↦ by omega)
  simp only [Finset.range_zero, Finset.sum_empty, add_zero] at h
  rw [frameCochainHomotopy_hochschildCoboundary_val, h, faceHomotopySum_zero_zero hxy,
    faceHomotopySum_last, sub_apply]

/-- The homotopy identity `bH + Hb = 1 - θ` in positive degree: frame conjugation by a frame with
`∑ c, x c * y c = 1` is homotopic to the identity on the Hochschild cochain complex. -/
theorem hochschildCoboundary_frameCochainHomotopy_add_frameCochainHomotopy_hochschildCoboundary
    (hxy : ∑ c, x c * y c = 1) (n : ℕ)
    (ψ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 2) ↦ B) M) :
    hochschildCoboundary R B M n (frameCochainHomotopy R M x y n ψ) +
        frameCochainHomotopy R M x y (n + 1) (hochschildCoboundary R B M (n + 1) ψ) =
      ψ - frameCochainConjugation R M x y (n + 1) ψ := by
  ext a
  obtain ⟨g, rfl⟩ := exists_eq_val a
  rw [add_apply, sub_apply,
    hochschildCoboundary_frameCochainHomotopy_val, frameCochainHomotopy_hochschildCoboundary_val,
    add_comm, sum_presimplicial_homotopy (n + 1) (faceHomotopySum x y ψ g)
      (homotopyFaceSum x y ψ g) (fun l j hlj hj ↦ faceHomotopySum_of_lt hxy ψ g hlj hj)
      (fun l hl hl' ↦ faceHomotopySum_self hxy ψ g hl hl')
      (fun l j hjl hl ↦ faceHomotopySum_of_add_one_lt ψ g hjl hl),
    faceHomotopySum_zero_zero hxy, faceHomotopySum_last]

/-- Frame conjugation by a frame with `∑ c, x c * y c = 1` commutes with the Hochschild
coboundary. -/
theorem hochschildCoboundary_frameCochainConjugation (hxy : ∑ c, x c * y c = 1) (n : ℕ)
    (ψ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ B) M) :
    hochschildCoboundary R B M n (frameCochainConjugation R M x y n ψ) =
      frameCochainConjugation R M x y (n + 1) (hochschildCoboundary R B M n ψ) := by
  have h₂ := hochschildCoboundary_frameCochainHomotopy_add_frameCochainHomotopy_hochschildCoboundary
    hxy n (hochschildCoboundary R B M n ψ)
  rw [hochschildCoboundary_hochschildCoboundary, map_zero, add_zero] at h₂
  rw [← sub_sub_cancel (hochschildCoboundary R B M n ψ) (frameCochainConjugation R M x y (n + 1) _),
    ← h₂]
  cases n with
  | zero =>
    rw [← sub_sub_cancel ψ (frameCochainConjugation R M x y 0 ψ),
      ← frameCochainHomotopy_hochschildCoboundary_zero hxy ψ, map_sub]
  | succ n =>
    rw [← sub_sub_cancel ψ (frameCochainConjugation R M x y (n + 1) ψ),
      ← hochschildCoboundary_frameCochainHomotopy_add_frameCochainHomotopy_hochschildCoboundary
        hxy n ψ, map_sub, map_add, hochschildCoboundary_hochschildCoboundary, zero_add]

end AddCommGroup

end Frame

/-! ### Matrix Morita invariance of Hochschild cohomology -/

section Matrix

variable {R A M ι : Type*} [Fintype ι]

section CommSemiring

variable [CommSemiring R] [Semiring A] [Module R A] [IsScalarTower R A A] [SMulCommClass R A A]
  [AddCommMonoid M] [Module R M]

/-- Conjugation by the matrix units of the `r`-th column and row is matrix extension of the
restriction to the `(r, r)` corner. -/
theorem frameCochainConjugation_single [DecidableEq ι] (r : ι) (n : ℕ)
    (ψ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ Matrix ι ι A) M) :
    frameCochainConjugation R M (fun c ↦ Matrix.single c r (1 : A))
        (fun c ↦ Matrix.single r c (1 : A)) n ψ =
      matrixCochainExtension ι n (ψ.compLinearMap fun _ ↦ Matrix.singleLinearMap R r r) := by
  ext a
  simp [frameCochainConjugation_apply, MultilinearMap.compLinearMap_apply]

end CommSemiring

variable [CommRing R] [Semiring A] [Module R A] [IsScalarTower R A A] [SMulCommClass R A A]
  [AddCommGroup M] [Module R M]

/-- The inclusion `a ↦ a E_rr` of `A` into the `(r, r)` corner of the matrix algebra, as a
homomorphism of nonunital algebras. -/
private def cornerHom [DecidableEq ι] (r : ι) : A →ₙₐ[R] Matrix ι ι A where
  toFun := Matrix.single r r
  map_smul' c a := (Matrix.smul_single c r r a).symm
  map_zero' := Matrix.single_zero r r
  map_add' := Matrix.single_add r r
  map_mul' a b := (Matrix.single_mul_single_same a r r r b).symm

/-- Restriction of a cochain on matrices to the `(r, r)` corner. -/
private def cornerRestriction [DecidableEq ι] (r : ι) {n : ℕ}
    (ψ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ Matrix ι ι A) M) :
    MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ A) M :=
  ψ.compLinearMap fun _ ↦ Matrix.singleLinearMap R r r

omit [IsScalarTower R A A] [SMulCommClass R A A] in
private theorem cornerRestriction_matrixCochainExtension [DecidableEq ι] (r : ι) (n : ℕ)
    (φ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ A) M) :
    cornerRestriction r (matrixCochainExtension ι n φ) = φ := by
  ext a
  simp [cornerRestriction, MultilinearMap.compLinearMap_apply]

private theorem hochschildCoboundary_cornerRestriction [DecidableEq ι] (r : ι) (n : ℕ)
    (ψ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ Matrix ι ι A) M) :
    hochschildCoboundary R A M n (cornerRestriction r ψ) =
      cornerRestriction r (hochschildCoboundary R (Matrix ι ι A) M n ψ) := by
  have h : ((cornerHom r : A →ₙₐ[R] Matrix ι ι A) : A →ₗ[R] Matrix ι ι A) =
      Matrix.singleLinearMap R r r :=
    LinearMap.ext fun _ ↦ rfl
  simpa only [cornerRestriction, h] using hochschildCoboundary_compLinearMap (cornerHom r) ψ

/-- Matrix extension composed with corner restriction is homotopic to the identity, in degree
zero. -/
private theorem matrixCochainExtension_cornerRestriction_zero [DecidableEq ι] (r : ι)
    (ψ : MultilinearMap (RingHom.id R) (fun _ : Fin 1 ↦ Matrix ι ι A) M) :
    ψ - matrixCochainExtension ι 0 (cornerRestriction r ψ) =
      frameCochainHomotopy R M (fun c ↦ Matrix.single c r (1 : A))
        (fun c ↦ Matrix.single r c (1 : A)) 0 (hochschildCoboundary R (Matrix ι ι A) M 0 ψ) := by
  rw [frameCochainHomotopy_hochschildCoboundary_zero (by simp [Matrix.sum_single_one]),
    frameCochainConjugation_single, cornerRestriction]

/-- Matrix extension composed with corner restriction is homotopic to the identity, in positive
degree. -/
private theorem matrixCochainExtension_cornerRestriction_succ [DecidableEq ι] (r : ι) (n : ℕ)
    (ψ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 2) ↦ Matrix ι ι A) M) :
    ψ - matrixCochainExtension ι (n + 1) (cornerRestriction r ψ) =
      hochschildCoboundary R (Matrix ι ι A) M n (frameCochainHomotopy R M
          (fun c ↦ Matrix.single c r (1 : A)) (fun c ↦ Matrix.single r c (1 : A)) n ψ) +
        frameCochainHomotopy R M (fun c ↦ Matrix.single c r (1 : A))
          (fun c ↦ Matrix.single r c (1 : A)) (n + 1)
          (hochschildCoboundary R (Matrix ι ι A) M (n + 1) ψ) := by
  rw [hochschildCoboundary_frameCochainHomotopy_add_frameCochainHomotopy_hochschildCoboundary
    (by simp [Matrix.sum_single_one]), frameCochainConjugation_single, cornerRestriction]

variable {n : ℕ}

/-- Matrix extension maps Hochschild cocycles to Hochschild cocycles. -/
theorem matrixCochainExtension_mem_hochschildCocycles
    {φ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ A) M}
    (hφ : φ ∈ hochschildCocycles R A M n) :
    matrixCochainExtension ι n φ ∈ hochschildCocycles R (Matrix ι ι A) M n := by
  rw [mem_hochschildCocycles_iff] at hφ ⊢
  rw [← matrixCochainExtension_hochschildCoboundary, hφ, map_zero]

/-- Matrix extension maps Hochschild coboundaries to Hochschild coboundaries. -/
theorem matrixCochainExtension_mem_hochschildCoboundaries
    {φ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ A) M}
    (hφ : φ ∈ hochschildCoboundaries R A M n) :
    matrixCochainExtension ι n φ ∈ hochschildCoboundaries R (Matrix ι ι A) M n := by
  cases n with
  | zero =>
    rw [hochschildCoboundaries_zero, Submodule.mem_bot] at hφ ⊢
    rw [hφ, map_zero]
  | succ n =>
    obtain ⟨χ, rfl⟩ := mem_hochschildCoboundaries_succ_iff.1 hφ
    exact mem_hochschildCoboundaries_succ_iff.2
      ⟨_, (matrixCochainExtension_hochschildCoboundary ι n χ).symm⟩

namespace hochschildCohomology

variable (M ι n) in
/-- The map `HHⁿ(A, Hom_R(A, M)) → HHⁿ(Matrix ι ι A, Hom_R(Matrix ι ι A, M))` on Hochschild
cohomology induced by matrix extension `φ ↦ φ#Tr` of cocycles. -/
noncomputable def matrixExtension :
    hochschildCohomology R A M n →ₗ[R] hochschildCohomology R (Matrix ι ι A) M n :=
  desc n (mk R (Matrix ι ι A) M n ∘ₗ (matrixCochainExtension ι n).restrict
      fun _ ↦ matrixCochainExtension_mem_hochschildCocycles)
    fun _ hφ ↦ (mk_eq_zero_iff _ _ _ n _).2 (matrixCochainExtension_mem_hochschildCoboundaries hφ)

/-- The induced map sends the class of a Hochschild cocycle to the class of its matrix
extension. -/
@[simp]
theorem matrixExtension_mk (φ : hochschildCocycles R A M n) :
    matrixExtension M ι n (mk R A M n φ) =
      mk R (Matrix ι ι A) M n ⟨matrixCochainExtension ι n φ,
        matrixCochainExtension_mem_hochschildCocycles φ.2⟩ :=
  desc_mk _ _ _ φ

/-- **Matrix Morita invariance of Hochschild cohomology.** For a nonempty finite index type `ι`,
matrix extension `φ ↦ φ#Tr` induces a bijection
`HHⁿ(A, Hom_R(A, M)) → HHⁿ(Matrix ι ι A, Hom_R(Matrix ι ι A, M))` in every degree. Its inverse is
restriction to a diagonal corner `a ↦ a E_rr`, and matrix extension after corner restriction is
homotopic to the identity on the Hochschild cochains of the matrix algebra. -/
theorem bijective_matrixExtension [Nonempty ι] :
    Function.Bijective (matrixExtension (R := R) (A := A) M ι n) := by
  classical
  obtain ⟨r⟩ := ‹Nonempty ι›
  have hρ {φ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ Matrix ι ι A) M}
      (hφ : φ ∈ hochschildCocycles R (Matrix ι ι A) M n) :
      cornerRestriction r φ ∈ hochschildCocycles R A M n := by
    rw [mem_hochschildCocycles_iff] at hφ ⊢
    rw [hochschildCoboundary_cornerRestriction, hφ, cornerRestriction,
      MultilinearMap.zero_compLinearMap]
  constructor
  · refine (injective_iff_map_eq_zero _).2 fun z hz ↦ ?_
    obtain ⟨φ, rfl⟩ := mk_surjective R A M n z
    rw [matrixExtension_mk, mk_eq_zero_iff] at hz
    rw [mk_eq_zero_iff, ← cornerRestriction_matrixCochainExtension r n φ.1]
    cases n with
    | zero =>
      rw [hochschildCoboundaries_zero, Submodule.mem_bot] at hz ⊢
      simp only at hz
      rw [hz, cornerRestriction, MultilinearMap.zero_compLinearMap]
    | succ n =>
      obtain ⟨χ, hχ⟩ := mem_hochschildCoboundaries_succ_iff.1 hz
      exact mem_hochschildCoboundaries_succ_iff.2
        ⟨cornerRestriction r χ, by rw [hochschildCoboundary_cornerRestriction, hχ]⟩
  · intro z
    obtain ⟨ψ, rfl⟩ := mk_surjective R (Matrix ι ι A) M n z
    refine ⟨mk R A M n ⟨cornerRestriction r ψ.1, hρ ψ.2⟩, ?_⟩
    rw [matrixExtension_mk, mk_eq_mk_iff]
    have hψ := mem_hochschildCocycles_iff.1 ψ.2
    cases n with
    | zero =>
      rw [hochschildCoboundaries_zero, Submodule.mem_bot, ← neg_eq_zero, neg_sub,
        matrixCochainExtension_cornerRestriction_zero, hψ, map_zero]
    | succ n =>
      rw [← neg_mem_iff, neg_sub, matrixCochainExtension_cornerRestriction_succ, hψ, map_zero,
        add_zero]
      exact mem_hochschildCoboundaries_succ_iff.2 ⟨_, rfl⟩

end hochschildCohomology

end Matrix

end TauCeti
