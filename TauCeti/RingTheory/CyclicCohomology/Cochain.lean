/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Multilinear.Basic
public import Mathlib.Logic.Equiv.Fin.Rotate
import TauCeti.Algebra.BigOperators.AlternatingSum

/-!
# The Hochschild coboundary and cyclic cochains

For a possibly nonunital and nonassociative `R`-algebra `A` and an `R`-module `M`, an
`n`-cochain is an `R`-multilinear map `φ : Aⁿ⁺¹ → M`. This file constructs the Hochschild
coboundary
`b : Cⁿ → Cⁿ⁺¹`,
`(bφ)(a₀, …, aₙ₊₁) = ∑_{j ≤ n} (-1)ʲ φ(a₀, …, aⱼaⱼ₊₁, …, aₙ₊₁) + (-1)ⁿ⁺¹ φ(aₙ₊₁a₀, a₁, …, aₙ)`,
proves `b ∘ b = 0` when the multiplication is associative, and shows that `b` preserves the cyclic
cochains, those with
`φ(aₙ, a₀, …, aₙ₋₁) = (-1)ⁿ φ(a₀, …, aₙ)`. For unital `A` and `M = R` these are the data from
which the Hochschild cochain complex of `A` with coefficients in its dual `A*` and Connes' cyclic
subcomplex can be assembled; the complexes themselves and their cohomology are not constructed
here. The formulas make sense for nonunital `A`, so they also apply to unitizations and their
relative complexes.

The coboundary is the alternating sum of the cofaces `φ ↦ φ ∘ dᵢ`, where `dᵢ` are face maps
on tuples. For unital `A`, these faces and the rotation are part of the Hochschild cyclic module;
in the nonunital setting no degeneracies are provided. The two facts above are consequences of
identities between faces and the cyclic rotation
`t(a₀, …, aₙ₊₁) = (aₙ₊₁, a₀, …, aₙ)`: the simplicial identity
`dᵢ ∘ d_{j+1} = d_j ∘ dᵢ` for `i ≤ j`, and `d₀ ∘ t = d_{n+1}`, `d_{i+1} ∘ t = t ∘ dᵢ`.

## Main definitions

* `TauCeti.hochschildFace`: the faces `dᵢ` on tuples.
* `TauCeti.hochschildCoface`: the cofaces `φ ↦ φ ∘ dᵢ` on multilinear cochains.
* `TauCeti.hochschildCoboundary`: the Hochschild coboundary `b`.
* `TauCeti.cyclicCochains`: the submodule of cyclic cochains.
* `TauCeti.cyclicHochschildCoboundary`: the restriction of `b` to cyclic cochains.

## Main results

* `TauCeti.hochschildCoboundary_hochschildCoboundary`: `b (b φ) = 0`.
* `TauCeti.hochschildCoboundary_mem_cyclicCochains`: `b` maps cyclic cochains to cyclic cochains.
* `TauCeti.cyclicHochschildCoboundary_cyclicHochschildCoboundary`: the restriction of `b` to
  cyclic cochains also squares to zero.
* `TauCeti.hochschildCoboundary_zero_eq_zero_iff`: the degree-zero cocycles are the traces.

## References

* A. Connes, *Noncommutative Geometry*, Chapter III, §1.
* J.-L. Loday, *Cyclic Homology*, §§1.1, 2.1.
-/

public section

open Function

namespace TauCeti

/-! ### Faces on natural-number indexed sequences -/

section NatFace

variable {A : Type*}

private theorem exists_eq_comp_val {m : ℕ} (a : Fin (m + 1) → A) :
    ∃ b : ℕ → A, a = fun k : Fin (m + 1) ↦ b k :=
  ⟨fun k ↦ a ⟨min k m, by omega⟩, by funext k; simp [Nat.min_eq_left (Nat.le_of_lt_succ k.2)]⟩

/-- Cyclic rotation `(b₀, …, bₙ) ↦ (bₙ, b₀, …, bₙ₋₁)` of a sequence of length `n + 1`. -/
private def natRotate (n : ℕ) (b : ℕ → A) (k : ℕ) : A :=
  if k = 0 then b n else b (k - 1)

private theorem comp_finRotate_symm_comp_val {n : ℕ} (b : ℕ → A) :
    (fun k : Fin (n + 1) ↦ b k) ∘ (finRotate (n + 1)).symm =
      fun k : Fin (n + 1) ↦ natRotate n b k := by
  funext k
  rcases k with ⟨_ | k, hk⟩
  · simp [natRotate, Fin.coe_neg_one]
  · simp [natRotate, finRotate_symm_apply, Fin.val_sub_one_of_ne_zero]

section Mul

variable [Mul A]

/-- Contraction of the entries `i` and `i + 1` of a sequence. -/
private def natContract (i : ℕ) (b : ℕ → A) (k : ℕ) : A :=
  if k < i then b k else if k = i then b k * b (k + 1) else b (k + 1)

/-- The last Hochschild face of a sequence of length `n + 2`. -/
private def natWrap (n : ℕ) (b : ℕ → A) (k : ℕ) : A :=
  if k = 0 then b (n + 1) * b 0 else b k

private theorem contractNth_comp_val {n : ℕ} (j : Fin (n + 2)) (b : ℕ → A) :
    Fin.contractNth j (· * ·) (fun k : Fin (n + 2) ↦ b k) =
      fun k : Fin (n + 1) ↦ natContract j b k := by
  funext k
  simp only [Fin.contractNth, Fin.val_castSucc, Fin.val_succ, natContract]

end Mul

section Semigroup

variable [Semigroup A]

private theorem natContract_natContract {i j : ℕ} (hij : i ≤ j) (b : ℕ → A) (k : ℕ) :
    natContract i (natContract (j + 1) b) k = natContract j (natContract i b) k := by
  simp only [natContract]
  split_ifs <;> first | omega | simp_all [mul_assoc]

private theorem natContract_natContract_natRotate {n i : ℕ} (hi : i ≤ n) (b : ℕ → A) {k : ℕ}
    (hk : k ≤ n) :
    natContract i (natContract 0 (natRotate (n + 2) b)) k =
      natContract 0 (natRotate (n + 1) (natContract i b)) k := by
  simp only [natContract, natRotate]
  split_ifs <;> first | omega | simp_all [mul_assoc]

private theorem natContract_natRotate_natContract_natRotate {n : ℕ} (b : ℕ → A) {k : ℕ}
    (hk : k ≤ n) :
    natContract 0 (natRotate (n + 1) (natContract 0 (natRotate (n + 2) b))) k =
      natContract 0 (natRotate (n + 1) (natContract (n + 1) b)) k := by
  simp only [natContract, natRotate]
  split_ifs <;> first | omega | simp_all [mul_assoc]

end Semigroup

section Mul

variable [Mul A]

private theorem natContract_succ_natRotate {n i : ℕ} (hi : i < n) (b : ℕ → A) (k : ℕ) :
    natContract (i + 1) (natRotate (n + 1) b) k = natRotate n (natContract i b) k := by
  simp only [natContract, natRotate]
  split_ifs <;> first | omega | simp_all [Nat.sub_one_add_one]

private theorem natContract_natRotate_natRotate {n : ℕ} (b : ℕ → A) {k : ℕ} (hk : k ≤ n) :
    natContract 0 (natRotate (n + 1) (natRotate (n + 1) b)) k =
      natRotate n (natContract n b) k := by
  simp only [natContract, natRotate]
  split_ifs <;> first | omega | simp_all

end Mul

/-- The position of the contracted sequence at which the entry `k` of the original sequence
appears, for the contraction of the entries `j` and `j + 1`. -/
private def natContractPos (j k : ℕ) : ℕ := if k ≤ j then k else k - 1

private theorem natContractPos_lt {n j k : ℕ} (hj : j < n + 1) (hk : k < n + 2) :
    natContractPos j k < n + 1 := by
  simp only [natContractPos]
  split_ifs <;> omega

private theorem natContract_update_of_ne [Mul A] {j k m : ℕ}
    (hm : m ≠ natContractPos j k) (b : ℕ → A) (x : A) :
    natContract j (update b k x) m = natContract j b m := by
  simp only [natContract, natContractPos, update_apply] at hm ⊢
  split_ifs at hm ⊢ <;> first | omega | rfl

private theorem natContract_update_add [NonUnitalNonAssocSemiring A] (j k : ℕ) (b : ℕ → A)
    (x y : A) :
    natContract j (update b k (x + y)) (natContractPos j k) =
      natContract j (update b k x) (natContractPos j k) +
        natContract j (update b k y) (natContractPos j k) := by
  simp only [natContract, natContractPos, update_apply]
  split_ifs <;> first | omega | simp [add_mul, mul_add]

private theorem natContract_update_smul {R : Type*} [NonUnitalNonAssocSemiring A] [SMul R A]
    [IsScalarTower R A A] [SMulCommClass R A A] (j k : ℕ) (b : ℕ → A) (c : R) (x : A) :
    natContract j (update b k (c • x)) (natContractPos j k) =
      c • natContract j (update b k x) (natContractPos j k) := by
  simp only [natContract, natContractPos, update_apply]
  split_ifs <;> first | omega | simp [smul_mul_assoc, mul_smul_comm]

end NatFace

/-! ### Hochschild faces of tuples -/

section Face

variable {A : Type*} {n : ℕ}

section Mul

variable [Mul A]

/-- The `i`-th Hochschild face of a tuple `(a₀, …, aₙ₊₁)`. For `i ≤ n` it multiplies the adjacent
entries `aᵢ` and `aᵢ₊₁`; the last face is `(aₙ₊₁ a₀, a₁, …, aₙ)`, i.e. the zeroth face of the
cyclically rotated tuple `(aₙ₊₁, a₀, …, aₙ)`. -/
def hochschildFace (i : Fin (n + 2)) (a : Fin (n + 2) → A) : Fin (n + 1) → A :=
  Fin.lastCases (Fin.contractNth 0 (· * ·) (a ∘ (finRotate _).symm))
    (fun j ↦ Fin.contractNth j.castSucc (· * ·) a) i

/-- The `j`-th Hochschild face for `j ≤ n` multiplies the entries `j` and `j + 1`. -/
@[simp]
theorem hochschildFace_castSucc (j : Fin (n + 1)) (a : Fin (n + 2) → A) :
    hochschildFace j.castSucc a = Fin.contractNth j.castSucc (· * ·) a := by
  simp [hochschildFace]

/-- The last Hochschild face is the zeroth face of the cyclically rotated tuple. -/
theorem hochschildFace_last_eq_contractNth (a : Fin (n + 2) → A) :
    hochschildFace (Fin.last (n + 1)) a =
      Fin.contractNth 0 (· * ·) (a ∘ (finRotate (n + 2)).symm) := by
  simp [hochschildFace]

/-- The last Hochschild face is `(aₙ₊₁ a₀, a₁, …, aₙ)`. -/
@[simp]
theorem hochschildFace_last (a : Fin (n + 2) → A) :
    hochschildFace (Fin.last (n + 1)) a =
      Fin.cons (a (Fin.last (n + 1)) * a 0) fun k ↦ a k.castSucc.succ := by
  obtain ⟨b, rfl⟩ := exists_eq_comp_val a
  rw [hochschildFace_last_eq_contractNth, comp_finRotate_symm_comp_val, contractNth_comp_val]
  funext k
  cases k using Fin.cases <;> simp [natContract, natRotate]

private theorem hochschildFace_castSucc_comp_val (j : Fin (n + 1)) (b : ℕ → A) :
    hochschildFace j.castSucc (fun k : Fin (n + 2) ↦ b k) =
      fun k : Fin (n + 1) ↦ natContract j b k := by
  rw [hochschildFace_castSucc, contractNth_comp_val, Fin.val_castSucc]

private theorem hochschildFace_last_comp_val (b : ℕ → A) :
    hochschildFace (Fin.last (n + 1)) (fun k : Fin (n + 2) ↦ b k) =
      fun k : Fin (n + 1) ↦ natContract 0 (natRotate (n + 1) b) k := by
  rw [hochschildFace_last_eq_contractNth, comp_finRotate_symm_comp_val, contractNth_comp_val,
    Fin.val_zero]

/-- The zeroth face of the rotated tuple `(aₙ₊₁, a₀, …, aₙ)` is the last face of `a`. -/
theorem hochschildFace_zero_comp_finRotate_symm (a : Fin (n + 2) → A) :
    hochschildFace 0 (a ∘ (finRotate (n + 2)).symm) = hochschildFace (Fin.last (n + 1)) a := by
  rw [← Fin.castSucc_zero, hochschildFace_castSucc, hochschildFace_last_eq_contractNth,
    Fin.castSucc_zero]

/-- The faces commute with cyclic rotation: `d_{i+1} ∘ t = t ∘ dᵢ`. -/
theorem hochschildFace_succ_comp_finRotate_symm (i : Fin (n + 1)) (a : Fin (n + 2) → A) :
    hochschildFace i.succ (a ∘ (finRotate (n + 2)).symm) =
      hochschildFace i.castSucc a ∘ (finRotate (n + 1)).symm := by
  obtain ⟨b, rfl⟩ := exists_eq_comp_val a
  rw [comp_finRotate_symm_comp_val]
  induction i using Fin.lastCases with
  | last =>
    rw [Fin.succ_last, hochschildFace_last_comp_val, hochschildFace_castSucc_comp_val,
      comp_finRotate_symm_comp_val]
    funext k
    exact natContract_natRotate_natRotate b (Nat.le_of_lt_succ k.2)
  | cast i =>
    rw [Fin.succ_castSucc, hochschildFace_castSucc_comp_val, hochschildFace_castSucc_comp_val,
      comp_finRotate_symm_comp_val]
    funext k
    exact natContract_succ_natRotate i.2 b k

end Mul

/-- The simplicial identity `dᵢ ∘ d_{j+1} = d_j ∘ dᵢ` for `i ≤ j` between Hochschild faces. -/
theorem hochschildFace_hochschildFace [Semigroup A] {i j : Fin (n + 2)} (hij : i ≤ j)
    (a : Fin (n + 3) → A) :
    hochschildFace i (hochschildFace j.succ a) =
      hochschildFace j (hochschildFace i.castSucc a) := by
  obtain ⟨b, rfl⟩ := exists_eq_comp_val a
  induction j using Fin.lastCases with
  | last =>
    rw [Fin.succ_last, hochschildFace_last_comp_val]
    induction i using Fin.lastCases with
    | last =>
      rw [hochschildFace_last_comp_val, hochschildFace_castSucc_comp_val,
        hochschildFace_last_comp_val]
      funext k
      exact natContract_natRotate_natContract_natRotate b (Nat.le_of_lt_succ k.2)
    | cast i =>
      rw [hochschildFace_castSucc_comp_val, hochschildFace_castSucc_comp_val,
        hochschildFace_last_comp_val]
      funext k
      exact natContract_natContract_natRotate (Nat.le_of_lt_succ i.2) b (Nat.le_of_lt_succ k.2)
  | cast j =>
    induction i using Fin.lastCases with
    | last => exact absurd hij (not_le.2 (Fin.castSucc_lt_last j))
    | cast i =>
      rw [Fin.succ_castSucc, hochschildFace_castSucc_comp_val, hochschildFace_castSucc_comp_val,
        hochschildFace_castSucc_comp_val, hochschildFace_castSucc_comp_val]
      funext k
      exact natContract_natContract (Fin.castSucc_le_castSucc_iff.1 hij) b k

end Face

/-! ### Cochains and the Hochschild coboundary -/

section Cochain

variable (R A M : Type*) [Semiring R] [NonUnitalNonAssocSemiring A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A] [AddCommMonoid M] [Module R M]
  [SMulCommClass R R M] {n : ℕ}

/-- Updating one entry of a tuple only changes one entry of a contraction of it. -/
private theorem contractNth_update_comp_val (j : Fin (n + 1)) (b : ℕ → A) (k : Fin (n + 2))
    (x : A) :
    Fin.contractNth j.castSucc (· * ·) (update (fun m : Fin (n + 2) ↦ b m) k x) =
      update (fun m : Fin (n + 1) ↦ natContract j b m)
        ⟨natContractPos j k, natContractPos_lt j.2 k.2⟩
        (natContract j (update b k x) (natContractPos j k)) := by
  have hupd : update (fun m : Fin (n + 2) ↦ b m) k x = fun m : Fin (n + 2) ↦ update b k x m :=
    (update_comp_eq_of_injective b Fin.val_injective k x).symm
  rw [hupd, contractNth_comp_val]
  funext m
  by_cases hm : (m : ℕ) = natContractPos j k
  · obtain rfl : m = ⟨natContractPos j k, natContractPos_lt j.2 k.2⟩ := Fin.ext hm
    rw [update_self, Fin.val_castSucc]
  · rw [update_of_ne (fun h ↦ hm (congrArg Fin.val h)), Fin.val_castSucc,
      natContract_update_of_ne hm]

variable {R A M} in
/-- Precomposition of a cochain with the contraction of the entries `j` and `j + 1`. -/
private def contractCoface (j : Fin (n + 1)) (φ : MultilinearMap R (fun _ : Fin (n + 1) ↦ A) M) :
    MultilinearMap R (fun _ : Fin (n + 2) ↦ A) M where
  toFun a := φ (Fin.contractNth j.castSucc (· * ·) a)
  map_update_add' := by
    intro _ a k x y
    obtain rfl : ‹DecidableEq (Fin (n + 2))› = instDecidableEqFin _ := Subsingleton.elim _ _
    obtain ⟨b, rfl⟩ := exists_eq_comp_val a
    simp only [contractNth_update_comp_val, natContract_update_add, MultilinearMap.map_update_add]
  map_update_smul' := by
    intro _ a k c x
    obtain rfl : ‹DecidableEq (Fin (n + 2))› = instDecidableEqFin _ := Subsingleton.elim _ _
    obtain ⟨b, rfl⟩ := exists_eq_comp_val a
    simp only [contractNth_update_comp_val, natContract_update_smul,
      MultilinearMap.map_update_smul]

omit [SMulCommClass R R M] in
private theorem contractCoface_apply (j : Fin (n + 1))
    (φ : MultilinearMap R (fun _ : Fin (n + 1) ↦ A) M) (a : Fin (n + 2) → A) :
    contractCoface j φ a = φ (Fin.contractNth j.castSucc (· * ·) a) :=
  rfl

variable {R A M} in
/-- The multilinear map `a ↦ φ (dᵢ a)`, assembled from contractions and a cyclic reindexing. -/
private def cofaceAux (i : Fin (n + 2)) (φ : MultilinearMap R (fun _ : Fin (n + 1) ↦ A) M) :
    MultilinearMap R (fun _ : Fin (n + 2) ↦ A) M :=
  Fin.lastCases ((contractCoface 0 φ).domDomCongr (finRotate (n + 2)).symm)
    (fun j ↦ contractCoface j φ) i

omit [SMulCommClass R R M] in
private theorem cofaceAux_apply (i : Fin (n + 2))
    (φ : MultilinearMap R (fun _ : Fin (n + 1) ↦ A) M) (a : Fin (n + 2) → A) :
    cofaceAux i φ a = φ (hochschildFace i a) := by
  induction i using Fin.lastCases with
  | last =>
    simp only [cofaceAux, Fin.lastCases_last, MultilinearMap.domDomCongr_apply,
      contractCoface_apply, hochschildFace_last_eq_contractNth, Function.comp_def,
      Fin.castSucc_zero]
  | cast j =>
    simp only [cofaceAux, Fin.lastCases_castSucc, contractCoface_apply, hochschildFace_castSucc]

/-- The `i`-th Hochschild coface, sending an `n`-cochain `φ` (a multilinear map in `n + 1`
arguments) to the `(n + 1)`-cochain `a ↦ φ (dᵢ a)`. -/
def hochschildCoface (i : Fin (n + 2)) :
    MultilinearMap R (fun _ : Fin (n + 1) ↦ A) M →ₗ[R]
      MultilinearMap R (fun _ : Fin (n + 2) ↦ A) M where
  toFun φ :=
    { toFun a := φ (hochschildFace i a)
      map_update_add' a k x y := by
        simpa only [cofaceAux_apply] using (cofaceAux i φ).map_update_add a k x y
      map_update_smul' a k c x := by
        simpa only [cofaceAux_apply] using (cofaceAux i φ).map_update_smul a k c x }
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The `i`-th coface evaluates a cochain on the `i`-th Hochschild face of the tuple. -/
@[simp]
theorem hochschildCoface_apply (i : Fin (n + 2))
    (φ : MultilinearMap R (fun _ : Fin (n + 1) ↦ A) M) (a : Fin (n + 2) → A) :
    hochschildCoface R A M i φ a = φ (hochschildFace i a) :=
  (rfl)

end Cochain

/-! ### Cyclic cochains -/

section Cyclic

variable (R A M : Type*) [Semiring R] [AddCommMonoid A] [Module R A] [AddCommGroup M]
  [Module R M] [SMulCommClass R R M] {n : ℕ}

/-- The cyclic `n`-cochains: the multilinear maps `φ` in `n + 1` arguments with
`φ(aₙ, a₀, …, aₙ₋₁) = (-1)ⁿ φ(a₀, …, aₙ)`. -/
def cyclicCochains (n : ℕ) : Submodule R (MultilinearMap R (fun _ : Fin (n + 1) ↦ A) M) where
  carrier := {φ | ∀ a, φ (a ∘ (finRotate (n + 1)).symm) = (-1 : ℤ) ^ n • φ a}
  add_mem' {φ ψ} hφ hψ a := by simp [hφ a, hψ a]
  zero_mem' a := by simp
  smul_mem' c φ hφ a := by simp [hφ a, smul_comm c]

variable {R A M} in
/-- A cochain is cyclic exactly when rotating its arguments multiplies its value by `(-1)ⁿ`. -/
@[simp]
theorem mem_cyclicCochains_iff {φ : MultilinearMap R (fun _ : Fin (n + 1) ↦ A) M} :
    φ ∈ cyclicCochains R A M n ↔
      ∀ a : Fin (n + 1) → A, φ (a ∘ (finRotate (n + 1)).symm) = (-1 : ℤ) ^ n • φ a :=
  Iff.rfl

/-- A bundled cyclic cochain satisfies the characteristic cyclic rotation identity. -/
@[simp]
theorem cyclicCochains_apply_finRotate_symm (φ : cyclicCochains R A M n)
    (a : Fin (n + 1) → A) :
    (φ : MultilinearMap R (fun _ : Fin (n + 1) ↦ A) M)
        (a ∘ (finRotate (n + 1)).symm) =
      (-1 : ℤ) ^ n • (φ : MultilinearMap R (fun _ : Fin (n + 1) ↦ A) M) a :=
  (mem_cyclicCochains_iff.1 φ.property) a

end Cyclic

section Coboundary

section NonAssoc

variable (R A M : Type*) [Semiring R] [NonUnitalNonAssocSemiring A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A] [AddCommGroup M] [Module R M]
  [SMulCommClass R R M]

/-- The Hochschild coboundary `b` on `M`-valued cochains of `A`, the alternating sum
`∑ᵢ (-1)ⁱ φ ∘ dᵢ` of the cofaces. Explicitly (`hochschildCoboundary_apply_eq_sum_contractNth_add`),
`(bφ)(a₀, …, aₙ₊₁) = ∑_{j ≤ n} (-1)ʲ φ(a₀, …, aⱼaⱼ₊₁, …, aₙ₊₁) + (-1)ⁿ⁺¹ φ(aₙ₊₁a₀, a₁, …, aₙ)`. -/
def hochschildCoboundary (n : ℕ) :
    MultilinearMap R (fun _ : Fin (n + 1) ↦ A) M →ₗ[R]
      MultilinearMap R (fun _ : Fin (n + 2) ↦ A) M :=
  ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • hochschildCoface R A M i

variable {R A M} {n : ℕ}

/-- The Hochschild coboundary evaluates as the alternating sum of `φ` on the faces of the tuple. -/
@[simp]
theorem hochschildCoboundary_apply (φ : MultilinearMap R (fun _ : Fin (n + 1) ↦ A) M)
    (a : Fin (n + 2) → A) :
    hochschildCoboundary R A M n φ a =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • φ (hochschildFace i a) := by
  simp [hochschildCoboundary]

/-- The Hochschild coboundary in the explicit form of the multiplication of adjacent entries,
followed by the cyclic term. -/
theorem hochschildCoboundary_apply_eq_sum_contractNth_add
    (φ : MultilinearMap R (fun _ : Fin (n + 1) ↦ A) M) (a : Fin (n + 2) → A) :
    hochschildCoboundary R A M n φ a =
      ∑ j : Fin (n + 1), (-1 : ℤ) ^ (j : ℕ) • φ (Fin.contractNth j.castSucc (· * ·) a) +
        (-1 : ℤ) ^ (n + 1) •
          φ (Fin.cons (a (Fin.last (n + 1)) * a 0) fun k ↦ a k.castSucc.succ) := by
  rw [hochschildCoboundary_apply, Fin.sum_univ_castSucc]
  simp

end NonAssoc

section Assoc

variable (R A M : Type*) [Semiring R] [NonUnitalSemiring A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A] [AddCommGroup M] [Module R M]
  [SMulCommClass R R M] {n : ℕ}

/-- The Hochschild coboundary squares to zero. -/
@[simp]
theorem hochschildCoboundary_hochschildCoboundary
    (φ : MultilinearMap R (fun _ : Fin (n + 1) ↦ A) M) :
    hochschildCoboundary R A M (n + 1) (hochschildCoboundary R A M n φ) = 0 := by
  ext a
  simp only [hochschildCoboundary_apply, zero_apply]
  exact sum_neg_one_pow_smul_sum_neg_one_pow_smul_eq_zero
    (fun i j ↦ φ (hochschildFace j (hochschildFace i a)))
    fun i j hij ↦ by simp only [hochschildFace_hochschildFace hij]

/-- The Hochschild coboundary squares to zero, as a composite of linear maps. -/
theorem hochschildCoboundary_comp_hochschildCoboundary :
    hochschildCoboundary R A M (n + 1) ∘ₗ hochschildCoboundary R A M n = 0 :=
  LinearMap.ext fun φ ↦ hochschildCoboundary_hochschildCoboundary (R := R) (A := A) (M := M) φ

end Assoc

section NonAssoc

variable (R A M : Type*) [Semiring R] [NonUnitalNonAssocSemiring A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A] [AddCommGroup M] [Module R M]
  [SMulCommClass R R M] {n : ℕ}

/-- In degree zero, `(bφ)(a₀, a₁) = φ(a₀a₁) - φ(a₁a₀)`. -/
theorem hochschildCoboundary_zero_apply (φ : MultilinearMap R (fun _ : Fin 1 ↦ A) M)
    (a : Fin 2 → A) :
    hochschildCoboundary R A M 0 φ a = φ (fun _ ↦ a 0 * a 1) - φ (fun _ ↦ a 1 * a 0) := by
  have h₀ : Fin.contractNth (0 : Fin 1).castSucc (· * ·) a = fun _ ↦ a 0 * a 1 := by
    funext k
    fin_cases k
    rfl
  have h₁ : (Fin.cons (a (Fin.last 1) * a 0) fun k : Fin 0 ↦ a k.castSucc.succ : Fin 1 → A) =
      fun _ ↦ a 1 * a 0 := by
    funext k
    fin_cases k
    rfl
  rw [hochschildCoboundary_apply_eq_sum_contractNth_add, Fin.sum_univ_one, h₀, h₁]
  simp [sub_eq_add_neg]

/-- A degree-zero cochain is a Hochschild cocycle exactly when it is a trace. -/
theorem hochschildCoboundary_zero_eq_zero_iff (φ : MultilinearMap R (fun _ : Fin 1 ↦ A) M) :
    hochschildCoboundary R A M 0 φ = 0 ↔ ∀ x y : A, φ (fun _ ↦ x * y) = φ (fun _ ↦ y * x) := by
  refine ⟨fun h x y ↦ ?_, fun h ↦ ?_⟩
  · have hxy := DFunLike.congr_fun h ![x, y]
    rw [hochschildCoboundary_zero_apply, zero_apply, sub_eq_zero] at hxy
    simpa using hxy
  · ext a
    rw [hochschildCoboundary_zero_apply, h, sub_self, zero_apply]

/-- The Hochschild coboundary preserves cyclic cochains, so they form a subcomplex. -/
theorem hochschildCoboundary_mem_cyclicCochains
    {φ : MultilinearMap R (fun _ : Fin (n + 1) ↦ A) M} (hφ : φ ∈ cyclicCochains R A M n) :
    hochschildCoboundary R A M n φ ∈ cyclicCochains R A M (n + 1) := by
  rw [mem_cyclicCochains_iff] at hφ ⊢
  intro a
  rw [hochschildCoboundary_apply, hochschildCoboundary_apply, Fin.sum_univ_succ,
    Fin.sum_univ_castSucc (n := n + 1), hochschildFace_zero_comp_finRotate_symm]
  simp only [hochschildFace_succ_comp_finRotate_symm, hφ _, smul_add, Finset.smul_sum, smul_smul,
    ← pow_add, Fin.val_zero, Fin.val_succ, Fin.val_castSucc, Fin.val_last, pow_zero, one_smul]
  rw [add_comm]
  congr 1
  · refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [add_right_comm, add_comm _ n, add_right_comm]
  · rw [← two_mul, pow_mul, neg_one_sq, one_pow, one_smul]

/-- The Hochschild coboundary `b` restricted to the cyclic subcomplex, as a linear map
`C_λⁿ → C_λⁿ⁺¹`. -/
def cyclicHochschildCoboundary (n : ℕ) :
    cyclicCochains R A M n →ₗ[R] cyclicCochains R A M (n + 1) :=
  (hochschildCoboundary R A M n).restrict fun _ ↦ hochschildCoboundary_mem_cyclicCochains R A M

/-- The restricted coboundary agrees with `b` on underlying cochains. -/
@[simp]
theorem coe_cyclicHochschildCoboundary_apply (φ : cyclicCochains R A M n) :
    (cyclicHochschildCoboundary R A M n φ : MultilinearMap R (fun _ : Fin (n + 2) ↦ A) M) =
      hochschildCoboundary R A M n φ := by
  simp [cyclicHochschildCoboundary]

end NonAssoc

section Assoc

variable (R A M : Type*) [Semiring R] [NonUnitalSemiring A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A] [AddCommGroup M] [Module R M]
  [SMulCommClass R R M] {n : ℕ}

/-- The restricted coboundary on cyclic cochains squares to zero. -/
@[simp]
theorem cyclicHochschildCoboundary_cyclicHochschildCoboundary (φ : cyclicCochains R A M n) :
    cyclicHochschildCoboundary R A M (n + 1) (cyclicHochschildCoboundary R A M n φ) = 0 := by
  ext a
  simp

/-- The restricted coboundary on cyclic cochains squares to zero, as a composite of linear
maps. -/
theorem cyclicHochschildCoboundary_comp_cyclicHochschildCoboundary :
    cyclicHochschildCoboundary R A M (n + 1) ∘ₗ cyclicHochschildCoboundary R A M n = 0 :=
  LinearMap.ext fun φ ↦
    cyclicHochschildCoboundary_cyclicHochschildCoboundary (R := R) (A := A) (M := M) φ

end Assoc

end Coboundary

end TauCeti
