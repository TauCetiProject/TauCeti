/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.QuotientGroup.Basic
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.UpperUnitriangular.Nilpotent
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.UpperUnitriangular.Transvection

/-!
# The adjacent quotient of an upper-unitriangular group

For a ring `R` and `n : ℕ`, write `U = Uₙ₊₁(R)` for the upper-unitriangular `(n+1) × (n+1)`
matrices, indexed by `Fin (n + 1)`, and `U^2` for the subgroup of matrices whose first
superdiagonal vanishes (`superdiagonalSubgroup 2`, following the numbering of `Nilpotent.lean`,
where `U^1 = U`; Harpaz–Wittenberg call this subgroup `U¹`). Entries one step above the diagonal add
under multiplication, even though the entries further out acquire cross terms: the `(0, 2)` entry
of `gh` contains `g₀₁h₁₂`. So reading off the first superdiagonal is a homomorphism

```text
U → (Rⁿ, +),  g ↦ (g_{i,i+1})ᵢ,
```

which is surjective, with kernel exactly `U^2`. It identifies the adjacent quotient `U/U^2` with
`Rⁿ`. A homomorphism into `U` thus has adjacent quotient a tuple of homomorphisms into `(R, +)`,
the adjacent entries; this is how characters `χ₀, …, χₙ₋₁` enter the lifting problems for
unitriangular groups behind Massey products, and how `U/U^2` acts on the higher layers of the
filtration by conjugation.

## Main declarations

* `TauCeti.UpperUnitriangularGroup.adjacentHom`: the homomorphism `U →* Multiplicative (Fin n → R)`
  reading off the first superdiagonal.
* `TauCeti.UpperUnitriangularGroup.adjacentHom_transvection`: the first superdiagonal of a
  transvection.
* `TauCeti.UpperUnitriangularGroup.sparseLift`: the section `a ↦ 1 + ∑ᵢ aᵢ E_{i,i+1}`.
* `TauCeti.UpperUnitriangularGroup.ker_adjacentHom`: the kernel is `U^2`.
* `TauCeti.UpperUnitriangularGroup.adjacentQuotientEquiv`: `U ⧸ U^2 ≃* Multiplicative (Fin n → R)`.
* `TauCeti.UpperUnitriangularGroup.adjacentHom_comp_map` and
  `TauCeti.UpperUnitriangularGroup.adjacentQuotientEquiv_map`: naturality in the coefficient
  ring.

## References

* Y. Harpaz and O. Wittenberg, *The Massey vanishing conjecture for number fields*, §2.
-/

public section

open Matrix

namespace TauCeti.UpperUnitriangularGroup

variable {R : Type*} {n : ℕ}

section Ring

variable [Ring R]

/-- The entry of a product of upper-unitriangular matrices one step above the diagonal is the sum
of the entries of the factors. -/
private theorem mul_apply_castSucc_succ (g h : upperUnitriangularGroup (Fin (n + 1)) R)
    (i : Fin n) :
    ((g * h : upperUnitriangularGroup (Fin (n + 1)) R) : GL (Fin (n + 1)) R) i.castSucc i.succ =
      (g : GL (Fin (n + 1)) R) i.castSucc i.succ + (h : GL (Fin (n + 1)) R) i.castSucc i.succ := by
  have hIoo : Finset.Ioo i.castSucc i.succ = ∅ :=
    Finset.coe_eq_empty.1 (by rw [Finset.coe_Ioo]; exact (Fin.covBy_iff.2 (by simp)).Ioo_eq)
  rw [mul_apply_of_lt g h Fin.castSucc_lt_succ, hIoo, Finset.sum_empty, add_zero]

variable (R n) in
/-- The homomorphism `Uₙ₊₁(R) → (Rⁿ, +)` sending an upper-unitriangular matrix to its entries
`g_{i,i+1}` one step above the diagonal. -/
def adjacentHom : upperUnitriangularGroup (Fin (n + 1)) R →* Multiplicative (Fin n → R) where
  toFun g := Multiplicative.ofAdd fun i ↦ (g : GL (Fin (n + 1)) R) i.castSucc i.succ
  map_one' := by
    rw [← ofAdd_zero]
    congr 1
    funext i
    simp [Matrix.one_apply_ne (Fin.castSucc_lt_succ (i := i)).ne]
  map_mul' g h := by
    rw [← ofAdd_add]
    congr 1
    funext i
    exact mul_apply_castSucc_succ g h i

/-- The `i`-th coordinate of `adjacentHom g` is the entry `g_{i,i+1}`. -/
@[simp]
theorem toAdd_adjacentHom_apply (g : upperUnitriangularGroup (Fin (n + 1)) R) (i : Fin n) :
    (adjacentHom R n g).toAdd i = (g : GL (Fin (n + 1)) R) i.castSucc i.succ :=
  (rfl)

/-- The first superdiagonal of a transvection: its entry `c` when the transvection sits on the
first superdiagonal at `(k.castSucc, k.succ)`, and zero otherwise. -/
theorem adjacentHom_transvection {i j : Fin (n + 1)} (hij : i < j) (c : R) (k : Fin n) :
    (adjacentHom R n (transvection hij c)).toAdd k =
      if (i, j) = (k.castSucc, k.succ) then c else 0 := by
  rw [toAdd_adjacentHom_apply, coe_transvection, coe_transvectionUnit_eq_one_add_single]
  simp only [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply, Prod.mk.injEq,
    ite_eq_right (Fin.castSucc_lt_succ (i := k)).ne, zero_add]

/-- An upper-unitriangular matrix lies in the kernel of `adjacentHom` exactly when its first
superdiagonal vanishes. -/
theorem ker_adjacentHom :
    (adjacentHom R n).ker = superdiagonalSubgroup (R := R) (n := n + 1) 2 := by
  ext g
  rw [MonoidHom.mem_ker, mem_superdiagonalSubgroup_iff, ← toAdd_eq_zero, funext_iff]
  simp only [toAdd_adjacentHom_apply, Pi.zero_apply]
  constructor
  · intro hg i j hij
    rcases lt_trichotomy j i with hji | rfl | hij'
    · rw [isUpperTriangular g hji, Matrix.one_apply_ne hji.ne']
    · rw [apply_diag, Matrix.one_apply_eq]
    · -- `i < j < i + 2`, so `j` is the successor of `i`.
      obtain ⟨k, rfl⟩ : ∃ k : Fin n, i = k.castSucc :=
        ⟨⟨i, by omega⟩, rfl⟩
      obtain rfl : j = k.succ := Fin.ext (by simp [Fin.lt_def] at hij hij' ⊢; omega)
      rw [hg k, Matrix.one_apply_ne (Fin.castSucc_lt_succ (i := k)).ne]
  · intro hg i
    rw [hg i.castSucc i.succ (by simp),
      Matrix.one_apply_ne (Fin.castSucc_lt_succ (i := i)).ne]

/-- The matrix `1 + ∑ᵢ aᵢ E_{i,i+1}`, with the entries of `a` one step above the diagonal, is upper
unitriangular. -/
private theorem isUpperUnitriangular_sparse (a : Fin n → R) :
    (1 + ∑ k : Fin n, Matrix.single k.castSucc k.succ (a k)).IsUpperUnitriangular := by
  refine (isUpperUnitriangular_def _).2 ⟨fun i j (hji : j < i) ↦ ?_, fun i ↦ ?_⟩
  · rw [Matrix.add_apply, Matrix.one_apply_ne hji.ne', Matrix.sum_apply, zero_add]
    refine Finset.sum_eq_zero fun k _ ↦ Matrix.single_apply_of_ne _ _ _ _ _ ?_
    rintro ⟨rfl, rfl⟩
    exact (Fin.castSucc_lt_succ (i := k)).not_gt hji
  · rw [Matrix.add_apply, Matrix.one_apply_eq, Matrix.sum_apply, add_eq_left]
    refine Finset.sum_eq_zero fun k _ ↦ Matrix.single_apply_of_ne _ _ _ _ _ ?_
    rintro ⟨rfl, h⟩
    exact (Fin.castSucc_lt_succ (i := k)).ne h.symm

variable (R) in
/-- The sparse lift `1 + ∑ᵢ aᵢ E_{i,i+1}` of a tuple `a`: the upper-unitriangular matrix with
first superdiagonal `a` and zero entries further above the diagonal. It is a set-theoretic section
of `adjacentHom`, not a homomorphism. -/
noncomputable def sparseLift (a : Fin n → R) : upperUnitriangularGroup (Fin (n + 1)) R :=
  ⟨(isUpperUnitriangular_sparse a).toGL, toGL_mem_upperUnitriangularGroup _⟩

/-- The matrix of `sparseLift R a` is `1 + ∑ᵢ aᵢ E_{i,i+1}`. -/
theorem coe_sparseLift (a : Fin n → R) :
    ((sparseLift R a : GL (Fin (n + 1)) R) : Matrix (Fin (n + 1)) (Fin (n + 1)) R) =
      1 + ∑ k : Fin n, Matrix.single k.castSucc k.succ (a k) :=
  IsUpperUnitriangular.coe_toGL _

/-- The entry of `sparseLift R a` at `(i, i + 1)` is `aᵢ`. -/
@[simp]
theorem sparseLift_apply_castSucc_succ (a : Fin n → R) (i : Fin n) :
    (sparseLift R a : GL (Fin (n + 1)) R) i.castSucc i.succ = a i := by
  rw [coe_sparseLift, Matrix.add_apply, Matrix.one_apply_ne (Fin.castSucc_lt_succ (i := i)).ne,
    zero_add, Matrix.sum_apply, Finset.sum_eq_single i]
  · exact Matrix.single_apply_same _ _ _
  · intro k _ hki
    exact Matrix.single_apply_of_ne _ _ _ _ _ fun h ↦ hki (Fin.castSucc_injective n h.1)
  · simp

/-- The sparse lift is a section of `adjacentHom`. -/
@[simp]
theorem adjacentHom_sparseLift (a : Fin n → R) :
    adjacentHom R n (sparseLift R a) = Multiplicative.ofAdd a := by
  refine Multiplicative.toAdd.injective (funext fun i ↦ ?_)
  simp

/-- Every tuple of entries one step above the diagonal is realised by an upper-unitriangular
matrix. -/
theorem adjacentHom_surjective : Function.Surjective (adjacentHom R n) :=
  fun x ↦ ⟨sparseLift R x.toAdd, by simp⟩

variable (R n) in
/-- The adjacent quotient `Uₙ₊₁(R) ⧸ U^2` is identified with `(Rⁿ, +)` by the entries one step
above the diagonal. -/
noncomputable def adjacentQuotientEquiv :
    upperUnitriangularGroup (Fin (n + 1)) R ⧸ superdiagonalSubgroup (R := R) (n := n + 1) 2 ≃*
      Multiplicative (Fin n → R) :=
  (QuotientGroup.quotientMulEquivOfEq ker_adjacentHom.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ adjacentHom_surjective)

/-- The class of `g` in the adjacent quotient corresponds to its entries one step above the
diagonal. -/
@[simp]
theorem adjacentQuotientEquiv_mk (g : upperUnitriangularGroup (Fin (n + 1)) R) :
    adjacentQuotientEquiv R n (g : upperUnitriangularGroup (Fin (n + 1)) R ⧸
      superdiagonalSubgroup (R := R) (n := n + 1) 2) = adjacentHom R n g :=
  (rfl)

/-- The inverse of `adjacentQuotientEquiv` sends a tuple to the class of its sparse lift. -/
@[simp]
theorem adjacentQuotientEquiv_symm_apply (x : Multiplicative (Fin n → R)) :
    (adjacentQuotientEquiv R n).symm x = (sparseLift R x.toAdd : upperUnitriangularGroup
      (Fin (n + 1)) R ⧸ superdiagonalSubgroup (R := R) (n := n + 1) 2) := by
  rw [MulEquiv.symm_apply_eq, adjacentQuotientEquiv_mk, adjacentHom_sparseLift, ofAdd_toAdd]

/-- The adjacent quotient has `|R|ⁿ` elements. -/
theorem natCard_adjacentQuotient :
    Nat.card (upperUnitriangularGroup (Fin (n + 1)) R ⧸
      superdiagonalSubgroup (R := R) (n := n + 1) 2) = Nat.card R ^ n := by
  rw [Nat.card_congr (adjacentQuotientEquiv R n).toEquiv, Nat.card_congr Multiplicative.toAdd,
    Nat.card_fun, Nat.card_fin]

end Ring

section CommRing

variable {S : Type*} [CommRing R] [CommRing S]

/-- Reading off the entries one step above the diagonal commutes with base change along a ring
homomorphism `f`, which acts on the tuple coordinatewise. -/
theorem adjacentHom_comp_map (f : R →+* S) :
    (adjacentHom S n).comp (map f) =
      (AddMonoidHom.compLeft (f : R →+ S) (Fin n)).toMultiplicative.comp (adjacentHom R n) := by
  ext g i
  simp

/-- The adjacent quotient is natural in the coefficient ring: base change on `Uₙ₊₁` descends to the
quotients by `U^2`, and corresponds to applying `f` coordinatewise to the tuple. -/
theorem adjacentQuotientEquiv_map (f : R →+* S)
    (x : upperUnitriangularGroup (Fin (n + 1)) R ⧸ superdiagonalSubgroup (R := R) (n := n + 1) 2) :
    adjacentQuotientEquiv S n
        (QuotientGroup.map _ _ (map f) (superdiagonalSubgroup_le_comap_map f 2) x) =
      (AddMonoidHom.compLeft (f : R →+ S) (Fin n)).toMultiplicative
        (adjacentQuotientEquiv R n x) := by
  induction x using QuotientGroup.induction_on with
  | H g =>
    rw [QuotientGroup.map_mk, adjacentQuotientEquiv_mk, adjacentQuotientEquiv_mk]
    exact DFunLike.congr_fun (adjacentHom_comp_map f) g

end CommRing

end TauCeti.UpperUnitriangularGroup
