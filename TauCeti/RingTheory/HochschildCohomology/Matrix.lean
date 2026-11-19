/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.CyclicCohomology.Matrix
public import TauCeti.RingTheory.HochschildCohomology.Complex
import Mathlib.LinearAlgebra.Multilinear.Curry
import TauCeti.Algebra.BigOperators.AlternatingSum
import TauCeti.Data.Fin.Basic
import TauCeti.Data.Fin.Tuple.Basic
import TauCeti.Data.Matrix.Basis

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

private theorem clampIndex_insertNth {j : ℕ} (l : Fin (j + 2)) (c : ι) (k : Fin (j + 1) → ι)
    {t : ℕ} (ht : t ≤ j + 1) :
    clampIndex (l.insertNth c k) t = natInsert l c (clampIndex k) t := by
  have hk : k = fun s : Fin (j + 1) ↦ clampIndex k s := funext fun s ↦ (clampIndex_val k s).symm
  have ht' : min t (j + 1) = t := Nat.min_eq_left ht
  rw [clampIndex]
  conv_lhs => rw [hk]
  rw [Fin.insertNth_comp_val]
  simp only [ht']

variable [Monoid B] (x y : ι → B)

/-- A face merging two entries of a homotopy tuple below its inserted entry removes the index
between them. -/
private theorem natContract_natHomotopy_natInsert {l j : ℕ} (hlj : l ≤ j) (c : ι) (κ : ℕ → ι)
    (g : ℕ → B) :
    natContract l (natHomotopy x y (j + 1) (natInsert l c κ) g) = fun t ↦
      if t = l then natLeft y κ l * g l * x c * (y c * (g (l + 1) * x (κ l)))
      else natHomotopy x y j κ (natContract l g) t := by
  funext t
  rcases lt_trichotomy t l with h | rfl | h <;> rcases lt_trichotomy t (j + 1) with h' | h' | h' <;>
    first | omega | simp (disch := omega) only [natContract_apply, natHomotopy, natLeft,
      natInsert_apply, ite_eq_left, ite_eq_right, ite_true, Nat.add_sub_cancel, Nat.sub_add_cancel,
      mul_assoc, h']

/-- The face merging the last conjugated entry with the inserted entry removes its index. -/
private theorem natContract_natHomotopy_natInsert_self {l : ℕ} (hl : 1 ≤ l) (c : ι) (κ : ℕ → ι)
    (g : ℕ → B) :
    natContract l (natHomotopy x y l (natInsert l c κ) g) = fun t ↦
      if t = l then natLeft y κ l * g l * x c * (y c * 1)
      else natContract l (natHomotopy x y (l - 1) κ g) t := by
  funext t
  rcases lt_trichotomy t l with h | rfl | h <;>
    first | omega | simp (disch := omega) only [natContract_apply, natHomotopy, natLeft,
      natInsert_apply, ite_eq_left, ite_eq_right, ite_true, Nat.add_sub_cancel, Nat.sub_add_cancel,
      mul_assoc, mul_one]

/-- A face beyond the inserted entry of a homotopy tuple commutes with the homotopy. -/
private theorem natContract_natHomotopy {l j : ℕ} (hjl : j + 1 < l) (κ : ℕ → ι) (g : ℕ → B) :
    natContract l (natHomotopy x y j κ g) = natHomotopy x y j κ (natContract (l - 1) g) := by
  funext t
  rcases lt_trichotomy t (j + 1) with h | h | h <;> rcases lt_trichotomy t l with h' | h' | h' <;>
    first | omega | simp (disch := omega) only [natContract_apply, natHomotopy, ite_eq_left,
      ite_eq_right, ite_true, Nat.add_sub_cancel, Nat.sub_add_cancel, h, h']

/-- The last face of a homotopy tuple not reaching the last entry commutes with the homotopy. -/
private theorem natContract_zero_natRotate_natHomotopy {m j : ℕ} (hjm : j < m) (κ : ℕ → ι)
    (g : ℕ → B) :
    natContract 0 (natRotate (m + 1) (natHomotopy x y j κ g)) =
      natHomotopy x y j κ (natContract 0 (natRotate m g)) := by
  funext t
  rcases Nat.eq_zero_or_pos t with h | h <;> rcases lt_trichotomy t (j + 1) with h' | h' | h' <;>
    first | omega | simp (disch := omega) only [natContract_apply, natRotate_apply, natHomotopy,
      natLeft, ite_eq_left, ite_eq_right, ite_true, Nat.add_sub_cancel, mul_assoc, one_mul, h, h']

/-- The zeroth face of the zeroth homotopy tuple merges its first two entries. -/
private theorem natContract_zero_natHomotopy_zero (κ : ℕ → ι) (g : ℕ → B) :
    natContract 0 (natHomotopy x y 0 κ g) = fun t ↦
      if t = 0 then 1 * g 0 * x (κ 0) * (y (κ 0) * 1) else g t := by
  funext t
  rcases Nat.eq_zero_or_pos t with h | h <;>
    simp (disch := omega) only [natContract_apply, natHomotopy, natLeft, ite_eq_left, ite_eq_right,
      ite_true, Nat.add_sub_cancel, mul_one, h]

end NatTuple

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
      MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ B) M :=
  ∑ p : Fin (n + 1) → ι, MultilinearMap.compLinearMapₗ fun j ↦
    LinearMap.mulLeftRight R (y (p j), x (p (finRotate (n + 1) j)))

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
  rw [Fin.insertNth_comp_val j.succ _
    (fun s ↦ LinearMap.mulLeftRight R (homotopyPair x y k s) (g s))]
  simp only [natInsert_apply, natHomotopy, homotopyPair, Fin.val_succ]
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

/-- The formula for the homotopy: `(Hψ)(a₀, …, aₙ)` is the alternating sum over `j` of the sums
over the index tuples `k : Fin (j + 1) → ι` of `ψ` evaluated on
`(a₀ x k₀, y k₀ a₁ x k₁, …, y kⱼ₋₁ aⱼ x kⱼ, y kⱼ, aⱼ₊₁, …, aₙ)`, the entry `y kⱼ` inserted at
position `j + 1`. -/
theorem frameCochainHomotopy_apply (n : ℕ)
    (ψ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 2) ↦ B) M) (a : Fin (n + 1) → B) :
    frameCochainHomotopy R M x y n ψ a =
      ∑ j : Fin (n + 1), (-1 : ℤ) ^ (j : ℕ) • ∑ k : Fin (j + 1) → ι,
        ψ (j.succ.insertNth (y (k (Fin.last j))) fun s ↦
          if h : (s : ℕ) ≤ j then
            (if (s : ℕ) = 0 then 1 else y (k ⟨s - 1, by omega⟩)) * a s * x (k ⟨s, by omega⟩)
          else a s) := by
  simp only [frameCochainHomotopy, LinearMap.coe_mk, AddHom.coe_mk, sum_apply, smul_apply,
    homotopyTerm, MultilinearMap.compLinearMap_apply, MultilinearMap.curryMid_apply_apply]
  refine Finset.sum_congr rfl fun j _ ↦ congrArg _ <| Finset.sum_congr rfl fun k _ ↦
    congrArg ψ <| congrArg _ <| funext fun s ↦ ?_
  simp only [homotopyPair]
  split_ifs with h h₀
  · simp [LinearMap.mulLeftRight_apply, natLeft, clampIndex, h₀]
  · simp [LinearMap.mulLeftRight_apply, natLeft, clampIndex, h₀, Nat.min_eq_left h,
      Nat.min_eq_left (show (s : ℕ) - 1 ≤ j by omega)]
  · simp [LinearMap.mulLeftRight_apply]

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
      ∑ l ∈ Finset.range (n + 2), (-1 : ℤ) ^ l • ψ (fun t ↦ natHochschildFace (n + 1) l g t) := by
  rw [hochschildCoboundary_apply]
  simp only [hochschildFace_comp_val]
  exact Fin.sum_univ_eq_sum_range
    (fun l ↦ (-1 : ℤ) ^ l • ψ (fun t : Fin (n + 1) ↦ natHochschildFace (n + 1) l g t)) (n + 2)

/-- The sum over index tuples of `ψ` on the `l`-th face of the `j`-th homotopy tuple. -/
private noncomputable def faceHomotopySum {m : ℕ}
    (ψ : MultilinearMap (RingHom.id R) (fun _ : Fin (m + 1) ↦ B) M) (g : ℕ → B) (l j : ℕ) : M :=
  ∑ k : Fin (j + 1) → ι,
    ψ (fun t ↦ natHochschildFace (m + 1) l (natHomotopy x y j (clampIndex k) g) t)

/-- The sum over index tuples of `ψ` on the `j`-th homotopy tuple of the `l`-th face. -/
private noncomputable def homotopyFaceSum {m : ℕ}
    (ψ : MultilinearMap (RingHom.id R) (fun _ : Fin (m + 1) ↦ B) M) (g : ℕ → B) (j l : ℕ) : M :=
  ∑ k : Fin (j + 1) → ι, ψ (fun t ↦ natHomotopy x y j (clampIndex k) (natHochschildFace m l g) t)

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
/-- If the `l`-th face of a homotopy tuple whose indices carry `c` at position `p` puts
`u * x c * (y c * v)` in entry `l` and agrees with `F` elsewhere, where `F l = u * v`, then summing
over `c` collapses the face to `F`. -/
private theorem sum_natContract_natHomotopy_insertNth (hxy : ∑ c, x c * y c = 1) {m j : ℕ}
    (ψ : MultilinearMap (RingHom.id R) (fun _ : Fin (m + 1) ↦ B) M) (g : ℕ → B)
    (p : Fin (j + 2)) {l : ℕ} (hlm : l < m + 1) (F : (Fin (j + 1) → ι) → ℕ → B)
    (u v : (Fin (j + 1) → ι) → B)
    (hF : ∀ k c, natContract l (natHomotopy x y (j + 1) (clampIndex (p.insertNth c k)) g) =
      fun t ↦ if t = l then u k * x c * (y c * v k) else F k t)
    (huv : ∀ k, F k l = u k * v k) :
    ∑ k : Fin (j + 2) → ι, ψ (fun t ↦ natContract l (natHomotopy x y (j + 1) (clampIndex k) g) t) =
      ∑ k : Fin (j + 1) → ι, ψ (fun t ↦ F k t) := by
  rw [← (Fin.insertNthEquiv (fun _ ↦ ι) p).sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  simp only [Fin.insertNthEquiv_apply, hF]
  exact sum_apply_collapse x y hxy ψ _ hlm _ _ (huv k)

omit [IsScalarTower R B B] [SMulCommClass R B B] in
/-- A face below the inserted entry of a homotopy tuple removes an index. -/
private theorem faceHomotopySum_of_lt (hxy : ∑ c, x c * y c = 1) {m : ℕ}
    (ψ : MultilinearMap (RingHom.id R) (fun _ : Fin (m + 1) ↦ B) M) (g : ℕ → B) {l j : ℕ}
    (hlj : l < j) (hjm : j ≤ m) :
    faceHomotopySum x y ψ g l j = homotopyFaceSum x y ψ g (j - 1) l := by
  obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  simp (disch := omega) only [faceHomotopySum, homotopyFaceSum, Nat.add_sub_cancel,
    natHochschildFace_of_lt]
  refine sum_natContract_natHomotopy_insertNth hxy ψ g ⟨l, by omega⟩ (by omega)
    (fun k ↦ natHomotopy x y j (clampIndex k) (natContract l g))
    (fun k ↦ natLeft y (clampIndex k) l * g l) (fun k ↦ g (l + 1) * x (clampIndex k l))
    (fun k c ↦ ?_) fun k ↦ ?_
  · rw [natHomotopy_congr x y (fun t ht ↦ clampIndex_insertNth _ c k ht) g,
      natContract_natHomotopy_natInsert x y (by omega)]
  · simp (disch := omega) only [natHomotopy, natContract_apply, ite_eq_left, ite_eq_right, ite_true,
      mul_assoc]

omit [IsScalarTower R B B] [SMulCommClass R B B] in
/-- The face merging the last conjugated entry with the inserted entry of a homotopy tuple removes
the last index. -/
private theorem faceHomotopySum_self (hxy : ∑ c, x c * y c = 1) {m : ℕ}
    (ψ : MultilinearMap (RingHom.id R) (fun _ : Fin (m + 1) ↦ B) M) (g : ℕ → B) {l : ℕ}
    (hl : 1 ≤ l) (hlm : l ≤ m) :
    faceHomotopySum x y ψ g l l = faceHomotopySum x y ψ g l (l - 1) := by
  obtain ⟨l, rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by omega⟩
  simp (disch := omega) only [faceHomotopySum, Nat.add_sub_cancel, natHochschildFace_of_lt]
  refine sum_natContract_natHomotopy_insertNth hxy ψ g (Fin.last (l + 1)) (by omega)
    (fun k ↦ natContract (l + 1) (natHomotopy x y l (clampIndex k) g))
    (fun k ↦ natLeft y (clampIndex k) (l + 1) * g (l + 1)) (fun _ ↦ 1) (fun k c ↦ ?_) fun k ↦ ?_
  · rw [natHomotopy_congr x y (fun t ht ↦ clampIndex_insertNth _ c k ht) g, Fin.val_last,
      natContract_natHomotopy_natInsert_self x y (by omega), Nat.add_sub_cancel]
  · simp (disch := omega) only [natHomotopy, natContract_apply, natLeft, ite_eq_left, ite_eq_right,
      ite_true, Nat.add_sub_cancel, mul_one]

omit [IsScalarTower R B B] [SMulCommClass R B B] in
/-- A face beyond the inserted entry of a homotopy tuple commutes with the homotopy. -/
private theorem faceHomotopySum_of_add_one_lt {m : ℕ}
    (ψ : MultilinearMap (RingHom.id R) (fun _ : Fin (m + 1) ↦ B) M) (g : ℕ → B) {l j : ℕ}
    (hjl : j + 1 < l) (hlm : l ≤ m + 1) :
    faceHomotopySum x y ψ g l j = homotopyFaceSum x y ψ g j (l - 1) := by
  simp only [faceHomotopySum, homotopyFaceSum]
  rcases hlm.lt_or_eq with hlm | rfl
  · simp (disch := omega) only [natHochschildFace_of_lt, natContract_natHomotopy x y hjl]
  · simp only [Nat.add_sub_cancel, natHochschildFace_self,
      natContract_zero_natRotate_natHomotopy x y (by omega : j < m)]

omit [IsScalarTower R B B] [SMulCommClass R B B] in
/-- The zeroth face of the zeroth homotopy tuple gives back the original tuple. -/
private theorem faceHomotopySum_zero_zero (hxy : ∑ c, x c * y c = 1) {m : ℕ}
    (ψ : MultilinearMap (RingHom.id R) (fun _ : Fin (m + 1) ↦ B) M) (g : ℕ → B) :
    faceHomotopySum x y ψ g 0 0 = ψ (fun t ↦ g t) := by
  simp only [faceHomotopySum, natHochschildFace_of_lt m.succ_pos]
  rw [← (Equiv.funUnique (Fin 1) ι).symm.sum_comp]
  have key (c : ι) : (fun t : Fin (m + 1) ↦ natContract 0 (natHomotopy x y 0
      (clampIndex ((Equiv.funUnique (Fin 1) ι).symm c)) g) t) =
      fun t : Fin (m + 1) ↦ if (t : ℕ) = 0 then 1 * g 0 * x c * (y c * 1)
      else g t := by
    have hκ : clampIndex ((Equiv.funUnique (Fin 1) ι).symm c) = fun _ ↦ c := by
      funext t
      simp [clampIndex]
    rw [hκ, natContract_zero_natHomotopy_zero]
  simp only [key]
  exact sum_apply_collapse x y hxy ψ _ m.succ_pos _ _ (by simp)

/-- The last face of the last homotopy tuple is frame conjugation. -/
private theorem faceHomotopySum_last {m : ℕ}
    (ψ : MultilinearMap (RingHom.id R) (fun _ : Fin (m + 1) ↦ B) M) (g : ℕ → B) :
    faceHomotopySum x y ψ g (m + 1) m = frameCochainConjugation R M x y m ψ (fun t ↦ g t) := by
  simp only [frameCochainConjugation_apply, faceHomotopySum, natHochschildFace_self]
  conv_rhs => rw [← (Equiv.arrowCongr (finRotate (m + 1)) (Equiv.refl ι)).sum_comp]
  refine Finset.sum_congr rfl fun k _ ↦ congrArg ψ (funext fun t ↦ ?_)
  simp only [Equiv.arrowCongr_apply, Equiv.coe_refl, Function.comp_apply, id,
    Equiv.symm_apply_apply]
  cases t using Fin.cases with
  | zero =>
    rw [Fin.finRotate_symm_zero, ← clampIndex_self k, ← clampIndex_val k 0]
    simp [natRotate_apply, natHomotopy, natLeft, mul_assoc]
  | succ t =>
    rw [Fin.finRotate_symm_succ, ← clampIndex_val k t.succ, ← clampIndex_val k t.castSucc]
    simp [natHomotopy, natLeft]

/-- In degree zero, `H(bψ) = ψ - θψ`: frame conjugation is homotopic to the identity. -/
theorem frameCochainHomotopy_hochschildCoboundary_zero (hxy : ∑ c, x c * y c = 1)
    (ψ : MultilinearMap (RingHom.id R) (fun _ : Fin 1 ↦ B) M) :
    frameCochainHomotopy R M x y 0 (hochschildCoboundary R B M 0 ψ) =
      ψ - frameCochainConjugation R M x y 0 ψ := by
  ext a
  obtain ⟨g, hg⟩ := Fin.val_injective.surjective_comp_right' (fun _ : ℕ ↦ (0 : B)) a
  obtain rfl : a = fun s : Fin _ ↦ g s := hg.symm
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
  obtain ⟨g, hg⟩ := Fin.val_injective.surjective_comp_right' (fun _ : ℕ ↦ (0 : B)) a
  obtain rfl : a = fun s : Fin _ ↦ g s := hg.symm
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

section NonUnital

variable [Semiring R] [NonUnitalSemiring A] [Module R A] [IsScalarTower R A A]
  [SMulCommClass R A A] [AddCommGroup M] [Module R M] [SMulCommClass R R M] {n : ℕ}

/-- Matrix extension maps Hochschild cocycles to Hochschild cocycles. -/
theorem matrixCochainExtension_mem_hochschildCocycles
    {φ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ A) M}
    (hφ : φ ∈ hochschildCocycles R A M n) :
    matrixCochainExtension ι n φ ∈ hochschildCocycles R (Matrix ι ι A) M n :=
  apply_mem_hochschildCocycles (fun n ↦ matrixCochainExtension ι n)
    (fun n χ ↦ (matrixCochainExtension_hochschildCoboundary ι n χ).symm) hφ

/-- Matrix extension maps Hochschild coboundaries to Hochschild coboundaries. -/
theorem matrixCochainExtension_mem_hochschildCoboundaries
    {φ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ A) M}
    (hφ : φ ∈ hochschildCoboundaries R A M n) :
    matrixCochainExtension ι n φ ∈ hochschildCoboundaries R (Matrix ι ι A) M n :=
  apply_mem_hochschildCoboundaries (fun n ↦ matrixCochainExtension ι n)
    (fun n χ ↦ (matrixCochainExtension_hochschildCoboundary ι n χ).symm) hφ

end NonUnital

section CommRing

variable [CommRing R] [NonUnitalSemiring A] [Module R A] [IsScalarTower R A A]
  [SMulCommClass R A A] [AddCommGroup M] [Module R M] {n : ℕ}

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

end hochschildCohomology

end CommRing

variable [CommRing R] [Semiring A] [Module R A] [IsScalarTower R A A] [SMulCommClass R A A]
  [AddCommGroup M] [Module R M]

/-- Restriction of cochains on matrices to the `(r, r)` corner. -/
private noncomputable def cornerRestriction [DecidableEq ι] (r : ι) (n : ℕ) :
    MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ Matrix ι ι A) M →ₗ[R]
      MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ A) M :=
  MultilinearMap.compLinearMapₗ fun _ ↦ Matrix.singleLinearMap R r r

omit [IsScalarTower R A A] [SMulCommClass R A A] in
private theorem cornerRestriction_matrixCochainExtension [DecidableEq ι] (r : ι) (n : ℕ)
    (φ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ A) M) :
    cornerRestriction r n (matrixCochainExtension ι n φ) = φ := by
  ext a
  simp [cornerRestriction, MultilinearMap.compLinearMap_apply]

private theorem hochschildCoboundary_cornerRestriction [DecidableEq ι] (r : ι) (n : ℕ)
    (ψ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ Matrix ι ι A) M) :
    hochschildCoboundary R A M n (cornerRestriction r n ψ) =
      cornerRestriction r (n + 1) (hochschildCoboundary R (Matrix ι ι A) M n ψ) := by
  simpa only [cornerRestriction, MultilinearMap.compLinearMapₗ_apply,
    Matrix.toLinearMap_singleNonUnitalAlgHom] using
    hochschildCoboundary_compLinearMap (Matrix.singleNonUnitalAlgHom R r) ψ

/-- Matrix extension composed with corner restriction is homotopic to the identity, in degree
zero. -/
private theorem matrixCochainExtension_cornerRestriction_zero [DecidableEq ι] (r : ι)
    (ψ : MultilinearMap (RingHom.id R) (fun _ : Fin 1 ↦ Matrix ι ι A) M) :
    ψ - matrixCochainExtension ι 0 (cornerRestriction r 0 ψ) =
      frameCochainHomotopy R M (fun c ↦ Matrix.single c r (1 : A))
        (fun c ↦ Matrix.single r c (1 : A)) 0 (hochschildCoboundary R (Matrix ι ι A) M 0 ψ) := by
  rw [frameCochainHomotopy_hochschildCoboundary_zero (by simp [Matrix.sum_single_one]),
    frameCochainConjugation_single, cornerRestriction, MultilinearMap.compLinearMapₗ_apply]

/-- Matrix extension composed with corner restriction is homotopic to the identity, in positive
degree. -/
private theorem matrixCochainExtension_cornerRestriction_succ [DecidableEq ι] (r : ι) (n : ℕ)
    (ψ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 2) ↦ Matrix ι ι A) M) :
    ψ - matrixCochainExtension ι (n + 1) (cornerRestriction r (n + 1) ψ) =
      hochschildCoboundary R (Matrix ι ι A) M n (frameCochainHomotopy R M
          (fun c ↦ Matrix.single c r (1 : A)) (fun c ↦ Matrix.single r c (1 : A)) n ψ) +
        frameCochainHomotopy R M (fun c ↦ Matrix.single c r (1 : A))
          (fun c ↦ Matrix.single r c (1 : A)) (n + 1)
          (hochschildCoboundary R (Matrix ι ι A) M (n + 1) ψ) := by
  rw [hochschildCoboundary_frameCochainHomotopy_add_frameCochainHomotopy_hochschildCoboundary
    (by simp [Matrix.sum_single_one]), frameCochainConjugation_single, cornerRestriction,
    MultilinearMap.compLinearMapₗ_apply]

variable {n : ℕ}

namespace hochschildCohomology

/-- **Matrix Morita invariance of Hochschild cohomology.** For a nonempty finite index type `ι`,
matrix extension `φ ↦ φ#Tr` induces a bijection
`HHⁿ(A, Hom_R(A, M)) → HHⁿ(Matrix ι ι A, Hom_R(Matrix ι ι A, M))` in every degree. Its inverse is
restriction to a diagonal corner `a ↦ a E_rr`, and matrix extension after corner restriction is
homotopic to the identity on the Hochschild cochains of the matrix algebra. -/
theorem bijective_matrixExtension [Nonempty ι] :
    Function.Bijective (matrixExtension (R := R) (A := A) M ι n) := by
  classical
  obtain ⟨r⟩ := ‹Nonempty ι›
  constructor
  · refine (injective_iff_map_eq_zero _).2 fun z hz ↦ ?_
    obtain ⟨φ, rfl⟩ := mk_surjective R A M n z
    rw [matrixExtension_mk, mk_eq_zero_iff] at hz
    rw [mk_eq_zero_iff, ← cornerRestriction_matrixCochainExtension r n φ.1]
    exact apply_mem_hochschildCoboundaries (cornerRestriction r)
      (hochschildCoboundary_cornerRestriction r) hz
  · intro z
    obtain ⟨ψ, rfl⟩ := mk_surjective R (Matrix ι ι A) M n z
    refine ⟨mk R A M n ⟨cornerRestriction r n ψ.1, apply_mem_hochschildCocycles
      (cornerRestriction r) (hochschildCoboundary_cornerRestriction r) ψ.2⟩, ?_⟩
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
