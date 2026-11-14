/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.CyclicCohomology.Matrix
public import TauCeti.RingTheory.HochschildCohomology.Complex
import TauCeti.Data.Fin.Basic

/-!
# Matrix Morita invariance of Hochschild cohomology

For an algebra `A` over a commutative ring `R`, an `R`-module `M`, and a finite index type `ι`,
the generalized matrix trace `φ ↦ φ#Tr` (`TauCeti.matrixCochainExtension`) commutes with the
Hochschild coboundary and therefore induces a linear map
`hochschildCohomology.matrixExtension` from `HHⁿ(A, Hom_R(A, M))` to
`HHⁿ(Matrix ι ι A, Hom_R(Matrix ι ι A, M))` in every degree `n`. In the opposite direction,
fixing an index `r : ι`, the diagonal corner inclusion `x ↦ Matrix.single r r x` is a
homomorphism of nonunital algebras and induces `hochschildCohomology.cornerRestriction` by pulling
cochains back to the `(r, r)` corner. Because restricting `φ#Tr` to a diagonal corner recovers `φ`
(`TauCeti.matrixCochainExtension_single`), corner restriction is a left inverse to matrix extension
already at the cochain level.

When `A` is unital, matrix extension and corner restriction are also inverse in the other order on
cohomology: this file constructs the explicit prism chain homotopy `matrixHochschildHomotopy`
between the identity on `C*(Matrix ι ι A; M)` and `(cornerCochainRestriction r)#Tr`, formed by
summing over open matrix-index paths `q : Fin (k + 1) → ι` and inserting the off-diagonal matrix
units `E_{q₀, r}` and `E_{r, q_s}`. On degree-zero cocycles (traces) this shows directly that every
trace on `Matrix ι ι A` is the generalized matrix trace of its corner restriction; in positive
degrees `b (h_{n-1} Θ) + h_n (b Θ) = Θ - (res_r Θ)#Tr`. Consequently, for every nonempty finite
index type `ι`, `hochschildCohomology.matrixExtension` is an isomorphism in all degrees over every
commutative ring `R`, and `hochschildCohomology.cornerRestriction` is independent of the chosen
corner `r : ι`.

## Main definitions

* `TauCeti.cornerCochainRestriction`: restriction of multilinear cochains on `Matrix ι ι A` to the
  `(r, r)` diagonal corner.
* `TauCeti.matrixHochschildHomotopy`: the prism homotopy
  `Cⁿ⁺¹(Matrix ι ι A; M) →ₗ[R] Cⁿ(Matrix ι ι A; M)` between the identity and
  `(cornerCochainRestriction r)#Tr`.
* `TauCeti.hochschildCohomology.matrixExtension`: the generalized-trace map on Hochschild
  cohomology.
* `TauCeti.hochschildCohomology.cornerRestriction`: the corner-restriction map on Hochschild
  cohomology.
* `TauCeti.hochschildCohomology.matrixExtensionEquiv`: the matrix Morita linear equivalence
  `HHⁿ(A, Hom_R(A, M)) ≃ₗ[R] HHⁿ(Matrix ι ι A, Hom_R(Matrix ι ι A, M))`.

## Main results

* `TauCeti.cornerCochainRestriction_matrixCochainExtension`: restricting `φ#Tr` to any diagonal
  corner recovers `φ`.
* `TauCeti.matrixHochschildHomotopy_hochschildCoboundary_zero` and
  `TauCeti.hochschildCoboundary_matrixHochschildHomotopy_add`: the chain-homotopy identities in
  degree zero and in positive degrees.
* `TauCeti.hochschildCohomology.bijective_matrixExtension`: matrix extension on Hochschild
  cohomology is bijective for every unital algebra and nonempty finite index type.
* `TauCeti.hochschildCohomology.cornerRestriction_eq`: corner restriction on Hochschild cohomology
  is independent of the chosen diagonal corner.

## References

* A. Connes, *Non-commutative differential geometry*, Publ. Math. IHÉS 62 (1985), Part II,
  Corollary 24.
* J.-L. Loday, *Cyclic Homology*, §§1.2, 1.5.
-/

public section

noncomputable section

namespace TauCeti

open scoped BigOperators

/-! ### Corner restriction of cochains -/

section CornerCochains

variable {R A M ι : Type*}

section Linear

variable [Semiring R] [AddCommMonoid A] [Module R A] [AddCommMonoid M] [Module R M]
  [SMulCommClass R R M] [DecidableEq ι]

/-- Restrict a degree-`n` cochain on `Matrix ι ι A` to the `(r, r)` diagonal corner by precomposing
every argument with `Matrix.singleLinearMap R r r`. -/
def cornerCochainRestriction (r : ι) (n : ℕ) :
    MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ Matrix ι ι A) M →ₗ[R]
      MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ A) M where
  toFun φ := φ.compLinearMap fun _ ↦ Matrix.singleLinearMap R r r
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Evaluating the `(r, r)` corner restriction on `(x₀, …, xₙ)` evaluates the original cochain on
the diagonal-corner matrices `Matrix.single r r (xⱼ)`. -/
@[simp]
theorem cornerCochainRestriction_apply (r : ι) (n : ℕ)
    (φ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ Matrix ι ι A) M)
    (x : Fin (n + 1) → A) :
    cornerCochainRestriction r n φ x = φ (fun j ↦ Matrix.single r r (x j)) :=
  (rfl)

/-- Restricting the matrix extension `φ#Tr` to any diagonal corner recovers `φ`. -/
@[simp]
theorem cornerCochainRestriction_matrixCochainExtension [Fintype ι] (r : ι) (n : ℕ)
    (φ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ A) M) :
    cornerCochainRestriction r n (matrixCochainExtension ι n φ) = φ := by
  ext x
  exact matrixCochainExtension_single ι r n φ x

end Linear

section Coboundary

variable [Semiring R] [NonUnitalNonAssocSemiring A] [Module R A] [IsScalarTower R A A]
  [SMulCommClass R A A] [AddCommGroup M] [Module R M] [SMulCommClass R R M]
  [Fintype ι] [DecidableEq ι]

/-- Corner restriction commutes with the Hochschild coboundary, since the diagonal corner inclusion
`x ↦ Matrix.single r r x` is a homomorphism of nonunital algebras. -/
theorem cornerCochainRestriction_hochschildCoboundary (r : ι) (n : ℕ)
    (φ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ Matrix ι ι A) M) :
    cornerCochainRestriction r (n + 1) (hochschildCoboundary R (Matrix ι ι A) M n φ) =
      hochschildCoboundary R A M n (cornerCochainRestriction r n φ) := by
  let cornerHom : A →ₙₐ[R] Matrix ι ι A :=
    { Matrix.singleLinearMap R r r with
      map_zero' := (Matrix.singleLinearMap R r r).map_zero
      map_mul' := fun x y ↦ (Matrix.single_mul_single_same x r r r y).symm }
  exact (hochschildCoboundary_compLinearMap cornerHom φ).symm

end Coboundary

section Cocycles

variable [Semiring R] [NonUnitalSemiring A] [Module R A] [IsScalarTower R A A]
  [SMulCommClass R A A] [AddCommGroup M] [Module R M] [SMulCommClass R R M] {n : ℕ}

/-- Matrix extension maps Hochschild cocycles to Hochschild cocycles. -/
theorem matrixCochainExtension_mem_hochschildCocycles [Fintype ι]
    {φ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ A) M}
    (hφ : φ ∈ hochschildCocycles R A M n) :
    matrixCochainExtension ι n φ ∈ hochschildCocycles R (Matrix ι ι A) M n := by
  rw [mem_hochschildCocycles_iff] at hφ ⊢
  rw [← matrixCochainExtension_hochschildCoboundary, hφ, map_zero]

/-- Matrix extension maps Hochschild coboundaries to Hochschild coboundaries. -/
theorem matrixCochainExtension_mem_hochschildCoboundaries [Fintype ι]
    {φ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ A) M}
    (hφ : φ ∈ hochschildCoboundaries R A M n) :
    matrixCochainExtension ι n φ ∈ hochschildCoboundaries R (Matrix ι ι A) M n := by
  cases n with
  | zero =>
    rw [hochschildCoboundaries_zero, Submodule.mem_bot] at hφ ⊢
    rw [hφ, map_zero]
  | succ n =>
    obtain ⟨ψ, rfl⟩ := mem_hochschildCoboundaries_succ_iff.1 hφ
    exact mem_hochschildCoboundaries_succ_iff.2
      ⟨matrixCochainExtension ι n ψ, (matrixCochainExtension_hochschildCoboundary ι n ψ).symm⟩

/-- Corner restriction maps Hochschild cocycles to Hochschild cocycles. -/
theorem cornerCochainRestriction_mem_hochschildCocycles [Fintype ι] [DecidableEq ι] (r : ι)
    {φ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ Matrix ι ι A) M}
    (hφ : φ ∈ hochschildCocycles R (Matrix ι ι A) M n) :
    cornerCochainRestriction r n φ ∈ hochschildCocycles R A M n := by
  rw [mem_hochschildCocycles_iff] at hφ ⊢
  rw [← cornerCochainRestriction_hochschildCoboundary, hφ, map_zero]

/-- Corner restriction maps Hochschild coboundaries to Hochschild coboundaries. -/
theorem cornerCochainRestriction_mem_hochschildCoboundaries [Fintype ι] [DecidableEq ι] (r : ι)
    {φ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ Matrix ι ι A) M}
    (hφ : φ ∈ hochschildCoboundaries R (Matrix ι ι A) M n) :
    cornerCochainRestriction r n φ ∈ hochschildCoboundaries R A M n := by
  cases n with
  | zero =>
    rw [hochschildCoboundaries_zero, Submodule.mem_bot] at hφ ⊢
    rw [hφ, map_zero]
  | succ n =>
    obtain ⟨ψ, rfl⟩ := mem_hochschildCoboundaries_succ_iff.1 hφ
    exact mem_hochschildCoboundaries_succ_iff.2
      ⟨cornerCochainRestriction r n ψ, (cornerCochainRestriction_hochschildCoboundary r n ψ).symm⟩

end Cocycles

end CornerCochains

/-! ### The prism homotopy on Hochschild cochains -/

section PrismHomotopy

variable {R A M ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Right-multiplying a matrix `x` by the matrix unit `E_{j, r}` extracts column `j` into
column `r`. -/
private theorem mul_single_one_eq_sum_single [Semiring A] (x : Matrix ι ι A) (j r : ι) :
    x * Matrix.single j r 1 = ∑ i : ι, Matrix.single i r (x i j) := by
  ext a b
  simp only [Matrix.mul_apply, Matrix.sum_apply, Matrix.single_apply]
  by_cases hb : r = b
  · subst hb
    rw [Finset.sum_eq_single j, Finset.sum_eq_single a]
    · simp
    · intro i _ hia; simp [hia]
    · intro ha; exact (ha (Finset.mem_univ a)).elim
    · intro k _ hkj; simp [hkj.symm]
    · intro hj; exact (hj (Finset.mem_univ j)).elim
  · simp [hb]

/-- Left-multiplying a matrix `x` by the matrix unit `E_{r, i}` extracts row `i` into row `r`. -/
private theorem single_one_mul_eq_sum_single [Semiring A] (r i : ι) (x : Matrix ι ι A) :
    Matrix.single r i 1 * x = ∑ j : ι, Matrix.single r j (x i j) := by
  ext a b
  simp only [Matrix.mul_apply, Matrix.sum_apply, Matrix.single_apply]
  by_cases ha : r = a
  · subst ha
    rw [Finset.sum_eq_single i, Finset.sum_eq_single b]
    · simp
    · intro j _ hjb; simp [hjb]
    · intro hb; exact (hb (Finset.mem_univ b)).elim
    · intro k _ hki; simp [hki.symm]
    · intro hi; exact (hi (Finset.mem_univ i)).elim
  · simp [ha]

private theorem comp_perm_pow_zero_symm {α β : Type*} (f : α → β) (σ : Equiv.Perm α) :
    f ∘ (σ ^ 0).symm = f := by
  rw [pow_zero]
  rfl

private theorem comp_perm_pow_add_symm {α β : Type*} (f : α → β) (σ : Equiv.Perm α)
    (p q : ℕ) :
    f ∘ (σ ^ (p + q)).symm = (f ∘ (σ ^ p).symm) ∘ (σ ^ q).symm := by
  rw [Nat.add_comm p q, pow_add, Equiv.Perm.mul_def, Equiv.symm_trans, Equiv.coe_trans,
    ← Function.comp_assoc]

private theorem comp_perm_pow_succ_symm {α β : Type*} (f : α → β) (σ : Equiv.Perm α) (p : ℕ) :
    f ∘ (σ ^ (p + 1)).symm = (f ∘ (σ ^ p).symm) ∘ σ.symm := by
  rw [comp_perm_pow_add_symm, pow_one]

/-- Iterating cyclic rotation shifts Hochschild faces: `d_{i+c} (a ∘ t⁻ᶜ) = (dᵢ a) ∘ t⁻ᶜ`. -/
private theorem hochschildFace_add_comp_finRotate_symm_pow {B : Type*} [Mul B] {d : ℕ}
    (a : Fin (d + 2) → B) {i c : ℕ} (h : i + c < d + 2) :
    hochschildFace ⟨i + c, h⟩ (a ∘ (finRotate (d + 2) ^ c).symm) =
      hochschildFace ⟨i, by omega⟩ a ∘ (finRotate (d + 1) ^ c).symm := by
  induction c with
  | zero =>
    rw [comp_perm_pow_zero_symm, comp_perm_pow_zero_symm]
    congr
  | succ c ih =>
    have hidx : (⟨i + (c + 1), h⟩ : Fin (d + 2)) = (⟨i + c, by omega⟩ : Fin (d + 1)).succ :=
      Fin.ext (by simp [Nat.add_assoc])
    rw [comp_perm_pow_succ_symm, hidx, hochschildFace_succ_comp_finRotate_symm, Fin.castSucc_mk,
      ih (by omega), ← comp_perm_pow_succ_symm]

/-- For `m ≤ k'`, `d_m (a ∘ t⁻⁽ᵏ'⁺¹⁾) = (d_{d+1+m-k'} a) ∘ t⁻ᵏ'`. -/
private theorem hochschildFace_lt_comp_finRotate_symm_pow_succ {B : Type*} [Mul B] {d : ℕ}
    (a : Fin (d + 2) → B) (m k' : Fin (d + 1)) (hmk : (m : ℕ) ≤ k') :
    hochschildFace m.castSucc (a ∘ (finRotate (d + 2) ^ ((k' : ℕ) + 1)).symm) =
      hochschildFace ⟨d + 1 + m - k', by omega⟩ a ∘ (finRotate (d + 1) ^ (k' : ℕ)).symm := by
  have hk₁ : (k' : ℕ) + 1 = ((k' : ℕ) - m + 1) + m := by omega
  have hm_eq : m.castSucc = ⟨0 + (m : ℕ), by omega⟩ := Fin.ext (by simp)
  have hzero : (⟨0, by omega⟩ : Fin (d + 2)) = 0 := rfl
  have hlast : Fin.last (d + 1) = ⟨(d + 1 + m - k') + ((k' : ℕ) - m), by omega⟩ :=
    Fin.ext (by simp; omega)
  have hk₂ : (k' : ℕ) - m + m = k' := by omega
  rw [hk₁, comp_perm_pow_add_symm, hm_eq, hochschildFace_add_comp_finRotate_symm_pow _ (by omega),
    comp_perm_pow_succ_symm, hzero, hochschildFace_zero_comp_finRotate_symm, hlast,
    hochschildFace_add_comp_finRotate_symm_pow _ (by omega), ← comp_perm_pow_add_symm, hk₂]

/-- The inverse of the `n`-th power of `finRotate (n + 1)` is `finRotate (n + 1)` itself. -/
private theorem finRotate_pow_pred_symm (n : ℕ) :
    ((finRotate (n + 1) ^ n).symm : Fin (n + 1) ≃ Fin (n + 1)) = finRotate (n + 1) := by
  ext j
  have h : (finRotate (n + 1) ^ n) (finRotate (n + 1) j) = j := by
    have hpow :
        (finRotate (n + 1) ^ (n + 1)) j = (finRotate (n + 1) ^ n) (finRotate (n + 1) j) := by
      rw [pow_succ, Equiv.Perm.mul_def, Equiv.coe_trans, Function.comp_apply]
    rw [← hpow]
    ext
    rw [Fin.coe_finRotate_pow, Nat.add_mod_right, Nat.mod_eq_of_lt j.isLt]
  exact congrArg Fin.val ((finRotate (n + 1) ^ n).symm_apply_eq.2 h.symm)

section Semiring

variable [Semiring R] [Semiring A] [Module R A] [SMulCommClass R A A]

/-- Coordinatewise linear maps building the tail of the `(k, q)` prism tuple: entries `< k` are
projected onto the `(r, r)` corner along `(q s, q (s + 1))`, entry `k` is left-multiplied by
`E_{r, q_k}`, and entries `> k` are left unchanged. -/
private def prismCoordLinearMap (r : ι) {n : ℕ} (k : Fin (n + 1)) (q : Fin (k + 1) → ι)
    (s : Fin (n + 1)) : Matrix ι ι A →ₗ[R] Matrix ι ι A :=
  if hs : (s : ℕ) < k then
    Matrix.singleLinearMap R r r ∘ₗ
      Matrix.entryLinearMap R A (q ⟨s, by omega⟩) (q ⟨s + 1, by omega⟩)
  else if (s : ℕ) = k then
    LinearMap.mulLeft R (Matrix.single r (q (Fin.last k)) (1 : A))
  else
    LinearMap.id

private theorem prismCoordLinearMap_of_lt (r : ι) {n : ℕ} (k : Fin (n + 1))
    (q : Fin (k + 1) → ι) (s : Fin (n + 1)) (hs : (s : ℕ) < k) (x : Matrix ι ι A) :
    prismCoordLinearMap (R := R) r k q s x =
      Matrix.single r r (x (q ⟨s, by omega⟩) (q ⟨s + 1, by omega⟩)) := by
  simp [prismCoordLinearMap, Fin.lt_def.2 hs]

private theorem prismCoordLinearMap_of_eq (r : ι) {n : ℕ} (k : Fin (n + 1))
    (q : Fin (k + 1) → ι) (s : Fin (n + 1)) (hs : (s : ℕ) = k) (x : Matrix ι ι A) :
    prismCoordLinearMap (R := R) r k q s x =
      Matrix.single r (q (Fin.last k)) 1 * x := by
  simp [prismCoordLinearMap, hs]

private theorem prismCoordLinearMap_of_gt (r : ι) {n : ℕ} (k : Fin (n + 1))
    (q : Fin (k + 1) → ι) (s : Fin (n + 1)) (hs : (k : ℕ) < s) (x : Matrix ι ι A) :
    prismCoordLinearMap (R := R) r k q s x = x := by
  have hlt : ¬ (s < k) := by rw [Fin.lt_def]; omega
  have hne : (s : ℕ) ≠ k := by omega
  simp [prismCoordLinearMap, hlt, hne]

/-- The tail of the `(k, q)` prism tuple applied to `b : Fin (n + 1) → Matrix ι ι A`. -/
private def prismTail (r : ι) {n : ℕ} (k : Fin (n + 1)) (q : Fin (k + 1) → ι)
    (b : Fin (n + 1) → Matrix ι ι A) : Fin (n + 1) → Matrix ι ι A :=
  fun s ↦ prismCoordLinearMap (R := R) r k q s (b s)

/-- The `(k, q)` prism tuple `(E_{q₀, r}, E_{r, q₀} b₀ E_{q₁, r}, …, E_{r, q_k} b_k, b_{k+1}, …)`
of length `n + 2` built from `b : Fin (n + 1) → Matrix ι ι A`. -/
private def prismTuple (r : ι) {n : ℕ} (k : Fin (n + 1)) (q : Fin (k + 1) → ι)
    (b : Fin (n + 1) → Matrix ι ι A) : Fin (n + 2) → Matrix ι ι A :=
  Fin.cons (Matrix.single (q 0) r 1) (prismTail (R := R) r k q b)

variable [AddCommGroup M] [Module R M] [SMulCommClass R R M]

/-- Fix the zeroth argument of a multilinear map in `n + 2` variables to obtain a multilinear map
in `n + 1` variables. -/
private def multilinearConsLeft {N₁ : Type*} [AddCommMonoid N₁] [Module R N₁] {n : ℕ} (x₀ : N₁)
    (Θ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 2) ↦ N₁) M) :
    MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ N₁) M :=
  MultilinearMap.mk' (fun y ↦ Θ (Fin.cons x₀ y))
    (fun y i u v ↦ by simp)
    (fun y i c u ↦ by simp)

/-- The `(k, q)` summand of the prism homotopy as an `R`-linear map on cochains. -/
private def prismTerm (r : ι) {n : ℕ} (k : Fin (n + 1)) (q : Fin (k + 1) → ι) :
    MultilinearMap (RingHom.id R) (fun _ : Fin (n + 2) ↦ Matrix ι ι A) M →ₗ[R]
      MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ Matrix ι ι A) M where
  toFun Θ :=
    MultilinearMap.domDomCongr (finRotate (n + 1) ^ (k : ℕ)).symm
      ((multilinearConsLeft (R := R) (Matrix.single (q 0) r 1) Θ).compLinearMap
        (prismCoordLinearMap (R := R) r k q))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem prismTerm_apply (r : ι) {n : ℕ} (k : Fin (n + 1)) (q : Fin (k + 1) → ι)
    (Θ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 2) ↦ Matrix ι ι A) M)
    (a : Fin (n + 1) → Matrix ι ι A) :
    prismTerm r k q Θ a =
      Θ (prismTuple (R := R) r k q (a ∘ (finRotate (n + 1) ^ (k : ℕ)).symm)) :=
  rfl

/-- **The prism chain homotopy on Hochschild cochains of `Matrix ι ι A`.** Fixing a corner index
`r : ι`, `matrixHochschildHomotopy r n` maps `(n + 1)`-cochains to `n`-cochains and satisfies
`b ∘ h + h ∘ b = id - (res_r)#Tr`. -/
def matrixHochschildHomotopy (r : ι) (n : ℕ) :
    MultilinearMap (RingHom.id R) (fun _ : Fin (n + 2) ↦ Matrix ι ι A) M →ₗ[R]
      MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ Matrix ι ι A) M :=
  ∑ k : Fin (n + 1), (-1 : ℤ) ^ (n * (k : ℕ)) • ∑ q : Fin (k + 1) → ι, prismTerm r k q

/-- Explicit formula for `matrixHochschildHomotopy`. -/
private theorem matrixHochschildHomotopy_apply (r : ι) (n : ℕ)
    (Θ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 2) ↦ Matrix ι ι A) M)
    (a : Fin (n + 1) → Matrix ι ι A) :
    matrixHochschildHomotopy r n Θ a =
      ∑ k : Fin (n + 1), (-1 : ℤ) ^ (n * (k : ℕ)) •
        ∑ q : Fin (k + 1) → ι,
          Θ (prismTuple (R := R) r k q (a ∘ (finRotate (n + 1) ^ (k : ℕ)).symm)) := by
  simp [matrixHochschildHomotopy, LinearMap.sum_apply, prismTerm_apply]

/-! #### Endpoint and face identities for the prism tuples -/

omit [SMulCommClass R R M] in
/-- At `k = 0`, summing the zeroth face of `prismTuple` over `q` recovers `Θ a`
because `∑ᵢ E_{i, i} = 1`. -/
private theorem sum_hochschildFace_zero_prismTuple_zero (r : ι) {n : ℕ}
    (k : Fin (n + 1)) (hk : k = 0)
    (Θ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ Matrix ι ι A) M)
    (a : Fin (n + 1) → Matrix ι ι A) :
    ∑ q : Fin ((k : ℕ) + 1) → ι,
        Θ (hochschildFace 0
          (prismTuple (R := R) r k q (a ∘ (finRotate (n + 1) ^ (k : ℕ)).symm))) =
      Θ a := by
  subst hk
  have hrot : a ∘ (finRotate (n + 1) ^ ((0 : Fin (n + 1)) : ℕ)).symm = a := by
    rw [Fin.val_zero, comp_perm_pow_zero_symm]
  have hface (q : Fin (((0 : Fin (n + 1)) : ℕ) + 1) → ι) :
      hochschildFace 0
          (prismTuple (R := R) r 0 q (a ∘ (finRotate (n + 1) ^ ((0 : Fin (n + 1)) : ℕ)).symm)) =
        Function.update a 0 (Matrix.single (q 0) (q 0) (1 : A) * a 0) := by
    rw [hrot, ← Fin.castSucc_zero, hochschildFace_castSucc]
    funext s
    cases s using Fin.cases with
    | zero =>
      simp [Fin.contractNth, prismTuple, prismTail, prismCoordLinearMap, ← mul_assoc]
      rfl
    | succ s =>
      simp [Fin.contractNth, prismTuple, prismTail, prismCoordLinearMap]
  simp_rw [hface]
  have hbij :
      ∑ q : Fin (((0 : Fin (n + 1)) : ℕ) + 1) → ι,
          Θ (Function.update a 0 (Matrix.single (q 0) (q 0) (1 : A) * a 0)) =
        ∑ i : ι, Θ (Function.update a 0 (Matrix.single i i (1 : A) * a 0)) :=
    Finset.sum_bij (fun q _ ↦ q 0) (fun _ _ ↦ Finset.mem_univ _)
      (fun q₁ _ q₂ _ h ↦ funext fun x ↦ by
        have hx : x = 0 := Fin.ext (by
          have hxlt : (x : ℕ) < 1 := x.isLt
          change (x : ℕ) = 0
          omega)
        rw [hx]
        exact h)
      (fun i _ ↦ ⟨fun _ ↦ i, Finset.mem_univ _, rfl⟩)
      (fun _ _ ↦ rfl)
  rw [hbij, ← Θ.map_update_sum, ← Finset.sum_mul, Matrix.sum_single_one, one_mul,
    Function.update_eq_self]

/-- At the top step `k = Fin.last n`, summing the last face of `prismTuple` over `q` produces
the matrix extension of the `(r, r)` corner restriction of `Θ`. -/
private theorem sum_hochschildFace_last_prismTuple_last (r : ι) {n : ℕ}
    (k : Fin (n + 1)) (hk : k = Fin.last n)
    (Θ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ Matrix ι ι A) M)
    (a : Fin (n + 1) → Matrix ι ι A) :
    ∑ q : Fin ((k : ℕ) + 1) → ι,
        Θ (hochschildFace (Fin.last (n + 1))
          (prismTuple (R := R) r k q (a ∘ (finRotate (n + 1) ^ (k : ℕ)).symm))) =
      matrixCochainExtension ι n (cornerCochainRestriction r n Θ) a := by
  subst hk
  have hrot : a ∘ (finRotate (n + 1) ^ ((Fin.last n) : ℕ)).symm = a ∘ finRotate (n + 1) := by
    rw [Fin.val_last, finRotate_pow_pred_symm]
  let e : Fin (n + 1) ≃ Fin (((Fin.last n) : ℕ) + 1) :=
    (finRotate (n + 1)).symm.trans
      (finCongr (show n + 1 = ((Fin.last n) : ℕ) + 1 by rw [Fin.val_last]))
  have hface (q : Fin (((Fin.last n) : ℕ) + 1) → ι) :
      hochschildFace (Fin.last (n + 1))
          (prismTuple (R := R) r (Fin.last n) q
            (a ∘ (finRotate (n + 1) ^ ((Fin.last n) : ℕ)).symm)) =
        fun j ↦ Matrix.single r r (a j (q (e j)) (q (e (finRotate (n + 1) j)))) := by
    rw [hrot, hochschildFace_last]
    funext j
    cases j using Fin.cases with
    | zero =>
      have hrot0 : (finRotate (n + 1)).symm 0 = Fin.last n := by
        rw [Equiv.symm_apply_eq, finRotate_last]
      have he0 : e 0 = Fin.last ((Fin.last n) : ℕ) := by
        ext
        simp [e, hrot0]
      have he1 : e (finRotate (n + 1) 0) = 0 := by
        ext
        simp [e]
      rw [he0, he1]
      simp [prismTuple, prismTail, prismCoordLinearMap]
    | succ s =>
      have hrots : (finRotate (n + 1)).symm s.succ = s.castSucc := by
        rw [Equiv.symm_apply_eq, Fin.finRotate_castSucc]
      have hes0 : e s.succ = ⟨s, by rw [Fin.val_last]; omega⟩ := by
        ext
        simp [e, hrots]
      have hes1 : e (finRotate (n + 1) s.succ) = ⟨(s : ℕ) + 1, by rw [Fin.val_last]; omega⟩ := by
        ext
        simp [e]
      rw [hes0, hes1]
      simp only [Fin.cons_succ, prismTuple, prismTail, Function.comp_apply, Fin.finRotate_castSucc]
      rw [prismCoordLinearMap_of_lt _ _ _ _ (by simp [Fin.val_last])]
      rfl
  simp_rw [hface]
  rw [matrixCochainExtension_apply]
  exact (Equiv.arrowCongr e.symm (Equiv.refl ι)).sum_comp fun p ↦
    Θ fun j ↦ Matrix.single r r (a j (p j) (p (finRotate (n + 1) j)))

omit [SMulCommClass R R M] in
/-- Telescoping between adjacent steps of the prism: the last face at step `l.castSucc` equals
the zeroth face at step `l.succ` on the rotated tuple. -/
private theorem sum_hochschildFace_last_eq_sum_hochschildFace_zero_succ (r : ι) {d : ℕ}
    (Θ : MultilinearMap (RingHom.id R) (fun _ : Fin (d + 2) ↦ Matrix ι ι A) M)
    (l : Fin (d + 1)) (c : Fin (d + 2) → Matrix ι ι A) :
    ∑ p : Fin ((l.castSucc : ℕ) + 1) → ι,
        Θ (hochschildFace (Fin.last (d + 2)) (prismTuple (R := R) r l.castSucc p c)) =
      ∑ q : Fin ((l.succ : ℕ) + 1) → ι,
        Θ (hochschildFace 0
          (prismTuple (R := R) r l.succ q (c ∘ (finRotate (d + 2)).symm))) := by
  have hlast_eq (p : Fin ((l : ℕ) + 1) → ι) :
      hochschildFace (Fin.last (d + 2)) (prismTuple (R := R) r l.castSucc p c) =
        Function.update
          (Fin.cons (0 : Matrix ι ι A) (prismTail (R := R) r l.castSucc p c ∘ Fin.castSucc)) 0
          (∑ i : ι, Matrix.single i r (c (Fin.last (d + 1)) i (p 0))) := by
    rw [hochschildFace_last, ← mul_single_one_eq_sum_single (c (Fin.last (d + 1))) (p 0) r]
    funext s
    cases s using Fin.cases with
    | zero =>
      simp [prismTuple, prismTail, prismCoordLinearMap,
        show ¬ (d + 1 < (l : ℕ)) by omega, show d + 1 ≠ (l : ℕ) by omega]
    | succ s =>
      simp [prismTuple]
  have hzero_eq (i : ι) (p : Fin ((l : ℕ) + 1) → ι) :
      Function.update
          (Fin.cons (0 : Matrix ι ι A) (prismTail (R := R) r l.castSucc p c ∘ Fin.castSucc)) 0
          (Matrix.single i r (c (Fin.last (d + 1)) i (p 0))) =
        hochschildFace 0
          (prismTuple (R := R) r l.succ (Fin.cons i p) (c ∘ (finRotate (d + 2)).symm)) := by
    conv_rhs => rw [← Fin.castSucc_zero, hochschildFace_castSucc]
    funext s
    cases s using Fin.cases with
    | zero =>
      have hrot0 : (finRotate (d + 2)).symm 0 = Fin.last (d + 1) := by
        rw [Equiv.symm_apply_eq, finRotate_last]
      simp [Fin.contractNth, prismTuple, prismTail, prismCoordLinearMap, hrot0]
    | succ s =>
      have hrots : (finRotate (d + 2)).symm s.succ = s.castSucc := by
        rw [Equiv.symm_apply_eq, Fin.finRotate_castSucc]
      rw [Function.update_of_ne (Fin.succ_ne_zero s), Fin.cons_succ, Function.comp_apply,
        Fin.contractNth_apply_of_ne _ _ _ _ (by simp), Fin.castSucc_zero, Fin.succAbove_zero]
      simp only [prismTuple, Fin.cons_succ, prismTail, Function.comp_apply, hrots]
      rcases lt_trichotomy (s : ℕ) (l : ℕ) with hsl | hse | hsg
      · rw [prismCoordLinearMap_of_lt _ _ _ _ (by simpa using hsl),
          prismCoordLinearMap_of_lt _ _ _ _ (by simp; omega)]
        have hc0 : (⟨(s.succ : ℕ), by simp; omega⟩ : Fin ((l.succ : ℕ) + 1)) =
            (⟨s, by omega⟩ : Fin ((l : ℕ) + 1)).succ := rfl
        have hc1 : (⟨(s.succ : ℕ) + 1, by simp; omega⟩ : Fin ((l.succ : ℕ) + 1)) =
            (⟨(s : ℕ) + 1, by omega⟩ : Fin ((l : ℕ) + 1)).succ := rfl
        rw [hc0, hc1, Fin.cons_succ, Fin.cons_succ]
        rfl
      · rw [prismCoordLinearMap_of_eq _ _ _ _ (by simpa using hse),
          prismCoordLinearMap_of_eq _ _ _ _ (by simp [hse])]
        have hlast_cons : (Fin.cons i p : Fin ((l.succ : ℕ) + 1) → ι) (Fin.last (l.succ : ℕ)) =
            p (Fin.last (l.castSucc : ℕ)) := by
          change (Fin.cons i p : Fin ((l : ℕ) + 2) → ι) (Fin.last ((l : ℕ) + 1)) = p (Fin.last l)
          rw [← Fin.succ_last, Fin.cons_succ]
        rw [hlast_cons]
      · rw [prismCoordLinearMap_of_gt _ _ _ _ (by simpa using hsg),
          prismCoordLinearMap_of_gt _ _ _ _ (by simp; omega)]
  have hbij :
      ∑ q : Fin ((l.succ : ℕ) + 1) → ι,
          Θ (hochschildFace 0
            (prismTuple (R := R) r l.succ q (c ∘ (finRotate (d + 2)).symm))) =
        ∑ p : Fin ((l.castSucc : ℕ) + 1) → ι, ∑ i : ι,
          Θ (hochschildFace 0
            (prismTuple (R := R) r l.succ (Fin.cons i p) (c ∘ (finRotate (d + 2)).symm))) := by
    rw [← (Fin.consEquiv (fun _ : Fin ((l.succ : ℕ) + 1) ↦ ι)).sum_comp, Fintype.sum_prod_type,
      Finset.sum_comm]
    rfl
  rw [hbij]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  rw [hlast_eq p, Θ.map_update_sum]
  exact Finset.sum_congr rfl fun i _ ↦ congrArg Θ (hzero_eq i p)

/-- Inner face of `prismTuple` when `k' ≤ m`: the contraction occurs at or after slot `k'`, so it
commutes pointwise with `prismTuple`. -/
private theorem hochschildFace_succ_prismTuple_of_le (r : ι) {d : ℕ}
    (k' m : Fin (d + 1)) (hkm : (k' : ℕ) ≤ m) (q : Fin ((k' : ℕ) + 1) → ι)
    (b : Fin (d + 2) → Matrix ι ι A) :
    hochschildFace m.succ.castSucc (prismTuple (R := R) r k'.castSucc q b) =
      prismTuple (R := R) r k' q (hochschildFace m.castSucc b) := by
  rw [prismTuple, prismTuple, hochschildFace_succ_castSucc_cons]
  congr 1
  rw [hochschildFace_castSucc, hochschildFace_castSucc]
  funext s
  by_cases hsm : s = m
  · subst hsm
    rw [Fin.contractNth_apply_of_eq s.castSucc _ _ s rfl]
    dsimp only [prismTail]
    rw [Fin.contractNth_apply_of_eq s.castSucc _ _ s rfl,
      prismCoordLinearMap_of_gt r k'.castSucc q s.succ (by simp; omega)]
    rcases lt_or_eq_of_le hkm with hlt | heq
    · rw [prismCoordLinearMap_of_gt r k'.castSucc q s.castSucc (by simpa using hlt),
        prismCoordLinearMap_of_gt r k' q s hlt]
    · rw [prismCoordLinearMap_of_eq r k'.castSucc q s.castSucc (by simpa using heq.symm),
        prismCoordLinearMap_of_eq r k' q s heq.symm, mul_assoc]
      rfl
  · have hsm' : (m.castSucc : ℕ) ≠ s := by simpa [Fin.ext_iff, eq_comm] using hsm
    rw [Fin.contractNth_apply_of_ne _ _ _ _ hsm']
    dsimp only [prismTail]
    rw [Fin.contractNth_apply_of_ne _ _ _ _ hsm']
    by_cases hlt_m : (s : ℕ) < m
    · rw [Fin.succAbove_of_castSucc_lt _ _ hlt_m]
      rfl
    · have hgt_m : (m : ℕ) < s := Nat.lt_of_le_of_ne (Nat.not_lt.1 hlt_m) (by
        intro heq; exact hsm (Fin.ext heq.symm))
      have hsa : m.castSucc.succAbove s = s.succ :=
        Fin.succAbove_of_le_castSucc _ _ (Fin.le_def.2 (Nat.le_of_lt hgt_m))
      rw [hsa, prismCoordLinearMap_of_gt r k'.castSucc q s.succ (by simp; omega),
        prismCoordLinearMap_of_gt r k' q s (by omega)]

omit [SMulCommClass R R M] in
/-- Inner face of `prismTuple` when `m ≤ k'`: summing over the intermediate index at position
`m + 1` contracts `prismTuple` at step `k'.succ` to `prismTuple` at step `k'`. -/
private theorem sum_hochschildFace_succ_prismTuple_of_gt (r : ι) {d : ℕ}
    (Θ : MultilinearMap (RingHom.id R) (fun _ : Fin (d + 2) ↦ Matrix ι ι A) M)
    (k' m : Fin (d + 1)) (hmk : (m : ℕ) ≤ k') (b : Fin (d + 2) → Matrix ι ι A) :
    ∑ q : Fin ((k'.succ : ℕ) + 1) → ι,
        Θ (hochschildFace m.succ.castSucc (prismTuple (R := R) r k'.succ q b)) =
      ∑ p : Fin ((k' : ℕ) + 1) → ι,
        Θ (prismTuple (R := R) r k' p (hochschildFace m.castSucc b)) := by
  let idx : Fin ((k' : ℕ) + 2) := ⟨(m : ℕ) + 1, by omega⟩
  change ∑ q : Fin ((k' : ℕ) + 2) → ι, _ = _
  rw [← (Fin.insertNthEquiv (fun _ : Fin ((k' : ℕ) + 2) ↦ ι) idx).sum_comp,
    Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  have hhead (j : ι) : Fin.insertNth (α := fun _ ↦ ι) idx j p 0 = p 0 := by
    have h0 : (0 : Fin ((k' : ℕ) + 2)) = idx.succAbove 0 := by
      ext
      simp [idx]
    rw [h0, Fin.insertNth_apply_succAbove]
  have htail_eq (j : ι) :
      hochschildFace m.succ.castSucc
          (prismTuple (R := R) r k'.succ (Fin.insertNth idx j p) b) =
        Function.update (prismTuple (R := R) r k' p (hochschildFace m.castSucc b)) m.succ
          (prismCoordLinearMap (R := R) r k'.succ (Fin.insertNth idx j p) m.castSucc
              (b m.castSucc) *
            prismCoordLinearMap (R := R) r k'.succ (Fin.insertNth idx j p) m.succ (b m.succ)) := by
    rw [prismTuple, hochschildFace_succ_castSucc_cons, hhead j, hochschildFace_castSucc]
    funext t
    cases t using Fin.cases with
    | zero =>
      rw [Function.update_of_ne (Fin.succ_ne_zero m).symm]
      simp [prismTuple]
    | succ s =>
      by_cases hsm : s = m
      · subst hsm
        rw [Function.update_self, Fin.cons_succ, Fin.contractNth_apply_of_eq s.castSucc _ _ s rfl]
        rfl
      · have hne_succ : s.succ ≠ m.succ := (Fin.succ_injective _).ne hsm
        have hsm' : (m.castSucc : ℕ) ≠ s := by simpa [Fin.ext_iff, eq_comm] using hsm
        rw [Function.update_of_ne hne_succ, Fin.cons_succ, prismTuple, Fin.cons_succ,
          Fin.contractNth_apply_of_ne _ _ _ _ hsm', prismTail, prismTail, hochschildFace_castSucc,
          Fin.contractNth_apply_of_ne _ _ _ _ hsm']
        by_cases hlt_m : (s : ℕ) < m
        · have hsa : m.castSucc.succAbove s = s.castSucc := Fin.succAbove_of_castSucc_lt _ _ hlt_m
          have hs_lt_k : (s : ℕ) < k' := Nat.lt_of_lt_of_le hlt_m hmk
          have hs_lt_ks : (s : ℕ) < (k'.succ : ℕ) := by simp [Fin.val_succ]; omega
          have hq0 : Fin.insertNth (α := fun _ ↦ ι) idx j p ⟨s, by omega⟩ = p ⟨s, by omega⟩ := by
            have heq : (⟨s, by omega⟩ : Fin ((k' : ℕ) + 2)) =
                idx.succAbove ⟨s, by omega⟩ := by
              ext; simp [idx, Fin.val_succAbove, show (s : ℕ) < (m : ℕ) + 1 by omega]
            rw [heq, Fin.insertNth_apply_succAbove]
          have hq1 : Fin.insertNth (α := fun _ ↦ ι) idx j p ⟨(s : ℕ) + 1, by omega⟩ =
              p ⟨(s : ℕ) + 1, by omega⟩ := by
            have heq : (⟨(s : ℕ) + 1, by omega⟩ : Fin ((k' : ℕ) + 2)) =
                idx.succAbove ⟨(s : ℕ) + 1, by omega⟩ := by
              ext; simp [idx, Fin.val_succAbove, show (s : ℕ) + 1 < (m : ℕ) + 1 by omega]
            rw [heq, Fin.insertNth_apply_succAbove]
          rw [hsa]
          simp only [prismCoordLinearMap, Fin.val_castSucc, hs_lt_k, hs_lt_ks, ↓reduceDIte,
            LinearMap.comp_apply, Matrix.singleLinearMap_apply, Matrix.entryLinearMap_apply,
            hq0, hq1]
        · have hgt_m : (m : ℕ) < s := Nat.lt_of_le_of_ne (Nat.not_lt.1 hlt_m) (by
            intro heq; exact hsm (Fin.ext heq.symm))
          have hsa : m.castSucc.succAbove s = s.succ :=
            Fin.succAbove_of_le_castSucc _ _ (Fin.le_def.2 (Nat.le_of_lt hgt_m))
          rw [hsa]
          by_cases hs_lt_k : (s : ℕ) < k'
          · have hq0 : Fin.insertNth (α := fun _ ↦ ι) idx j p ⟨(s : ℕ) + 1, by omega⟩ =
                p ⟨s, by omega⟩ := by
              have heq : (⟨(s : ℕ) + 1, by omega⟩ : Fin ((k' : ℕ) + 2)) =
                  idx.succAbove ⟨s, by omega⟩ := by
                ext; simp [idx, Fin.val_succAbove, show ¬ ((s : ℕ) < (m : ℕ) + 1) by omega]
              rw [heq, Fin.insertNth_apply_succAbove]
            have hq1 : Fin.insertNth (α := fun _ ↦ ι) idx j p ⟨(s : ℕ) + 2, by omega⟩ =
                p ⟨(s : ℕ) + 1, by omega⟩ := by
              have heq : (⟨(s : ℕ) + 2, by omega⟩ : Fin ((k' : ℕ) + 2)) =
                  idx.succAbove ⟨(s : ℕ) + 1, by omega⟩ := by
                ext; simp [idx, Fin.val_succAbove, show ¬ ((s : ℕ) + 1 < (m : ℕ) + 1) by omega]
              rw [heq, Fin.insertNth_apply_succAbove]
            simp only [prismCoordLinearMap, Fin.val_succ, hs_lt_k,
              show (s : ℕ) + 1 < (k' : ℕ) + 1 by omega, ↓reduceDIte,
              LinearMap.comp_apply, Matrix.singleLinearMap_apply, Matrix.entryLinearMap_apply,
              hq0, hq1]
          · simp only [prismCoordLinearMap, hs_lt_k, Fin.val_succ,
              show ¬ ((s : ℕ) + 1 < (k' : ℕ) + 1) by omega, ↓reduceDIte]
            by_cases hse : (s : ℕ) = k'
            · have hqlast : Fin.insertNth (α := fun _ ↦ ι) idx j p (Fin.last ((k' : ℕ) + 1)) =
                  p (Fin.last k') := by
                have heq : Fin.last ((k' : ℕ) + 1) = idx.succAbove (Fin.last k') := by
                  ext; simp [idx, Fin.val_succAbove, show ¬ ((k' : ℕ) < (m : ℕ) + 1) by omega]
                rw [heq, Fin.insertNth_apply_succAbove]
              simp only [hse, ↓reduceIte, LinearMap.mulLeft_apply, hqlast]
            · simp only [hse, show (s : ℕ) + 1 ≠ (k' : ℕ) + 1 by omega, ↓reduceIte,
                LinearMap.id_apply]
  have hsum_mid :
      ∑ j : ι,
          prismCoordLinearMap (R := R) r k'.succ (Fin.insertNth idx j p) m.castSucc
              (b m.castSucc) *
            prismCoordLinearMap (R := R) r k'.succ (Fin.insertNth idx j p) m.succ (b m.succ) =
        prismTuple (R := R) r k' p (hochschildFace m.castSucc b) m.succ := by
    have hqm : ∀ j : ι, Fin.insertNth (α := fun _ ↦ ι) idx j p ⟨m, by omega⟩ =
        p ⟨m, by omega⟩ := fun j ↦ by
      have heq : (⟨m, by omega⟩ : Fin ((k' : ℕ) + 2)) = idx.succAbove ⟨m, by omega⟩ := by
        ext; simp [idx, Fin.val_succAbove]
      rw [heq, Fin.insertNth_apply_succAbove]
    have hidx_self : ∀ j : ι, Fin.insertNth (α := fun _ ↦ ι) idx j p idx = j :=
      fun j ↦ Fin.insertNth_apply_same (α := fun _ ↦ ι) idx j p
    simp only [prismTuple, Fin.cons_succ, prismTail, hochschildFace_castSucc,
      Fin.contractNth_apply_of_eq m.castSucc _ _ m rfl]
    rcases lt_or_eq_of_le hmk with hlt | heq
    · have hqm1 : ∀ j : ι, Fin.insertNth (α := fun _ ↦ ι) idx j p ⟨(m : ℕ) + 2, by omega⟩ =
          p ⟨(m : ℕ) + 1, by omega⟩ := fun j ↦ by
        have heq : (⟨(m : ℕ) + 2, by omega⟩ : Fin ((k' : ℕ) + 2)) =
            idx.succAbove ⟨(m : ℕ) + 1, by omega⟩ := by
          ext; simp [idx, Fin.val_succAbove]
        rw [heq, Fin.insertNth_apply_succAbove]
      have hidx_eq : (⟨(m : ℕ) + 1, by omega⟩ : Fin ((k' : ℕ) + 2)) = idx := rfl
      have hlhs_j (j : ι) :
          prismCoordLinearMap (R := R) r k'.succ (Fin.insertNth idx j p) m.castSucc
              (b m.castSucc) *
            prismCoordLinearMap (R := R) r k'.succ (Fin.insertNth idx j p) m.succ (b m.succ) =
            Matrix.single r r
              (b m.castSucc (p ⟨m, by omega⟩) j * b m.succ j (p ⟨(m : ℕ) + 1, by omega⟩)) := by
        rw [prismCoordLinearMap_of_lt _ _ _ _ (by simp; omega),
          prismCoordLinearMap_of_lt _ _ _ _ (by simp; omega)]
        simp only [Fin.val_castSucc, Fin.val_succ, hqm, hqm1, hidx_eq, hidx_self,
          Matrix.single_mul_single_same]
      simp_rw [hlhs_j, ← Matrix.singleLinearMap_apply R r r, ← map_sum, ← Matrix.mul_apply]
      rw [prismCoordLinearMap_of_lt _ _ _ _ hlt, Matrix.singleLinearMap_apply]
    · have hlast_idx : Fin.last (k'.succ : ℕ) = idx := Fin.ext (by simp [idx, heq])
      have hidx_eq : (⟨(m : ℕ) + 1, by omega⟩ : Fin ((k' : ℕ) + 2)) = idx := rfl
      have hk_last : (⟨m, by omega⟩ : Fin ((k' : ℕ) + 1)) = Fin.last k' :=
        Fin.ext (by simp [heq])
      have hlhs_j (j : ι) :
          prismCoordLinearMap (R := R) r k'.succ (Fin.insertNth idx j p) m.castSucc
              (b m.castSucc) *
            prismCoordLinearMap (R := R) r k'.succ (Fin.insertNth idx j p) m.succ (b m.succ) =
            Matrix.single r j (b m.castSucc (p (Fin.last k')) j) * b m.succ := by
        rw [prismCoordLinearMap_of_lt _ _ _ _ (by simp; omega),
          prismCoordLinearMap_of_eq _ _ _ _ (by simp [heq])]
        simp only [Fin.val_castSucc, hqm, hk_last, hidx_eq, hlast_idx, hidx_self, ← mul_assoc,
          Matrix.single_mul_single_same, mul_one]
      simp_rw [hlhs_j, ← Finset.sum_mul,
        ← single_one_mul_eq_sum_single r (p (Fin.last k')) (b m.castSucc), mul_assoc]
      rw [prismCoordLinearMap_of_eq _ _ _ _ heq]
  simp only [Fin.insertNthEquiv_apply, htail_eq, ← Θ.map_update_sum, hsum_mid,
    Function.update_eq_self]

/-! #### Decomposition of the prism coboundary sums -/

/-- Partition a double sum over `(m, k) : Fin (d + 1) × Fin (d + 2)` into the lower triangle
`k = k'.castSucc` (`k' ≤ m`) and the upper triangle `k = k'.succ` (`m ≤ k'`). -/
private theorem sum_fin_succ_split {N : Type*} [AddCommMonoid N] (d : ℕ)
    (g : Fin (d + 1) → Fin (d + 2) → N) :
    ∑ m : Fin (d + 1), ∑ k : Fin (d + 2), g m k =
      (∑ k' : Fin (d + 1), ∑ m ∈ Finset.Ici k', g m k'.castSucc) +
        (∑ k' : Fin (d + 1), ∑ m ∈ Finset.Iic k', g m k'.succ) := by
  have hrow (m : Fin (d + 1)) :
      ∑ k : Fin (d + 2), g m k =
        (∑ k' ∈ Finset.Iic m, g m k'.castSucc) + (∑ k' ∈ Finset.Ici m, g m k'.succ) := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun k : Fin (d + 2) ↦ (k : ℕ) ≤ m)]
    congr 1
    · refine Finset.sum_bij
        (fun k hk ↦ (⟨k, by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk; omega⟩ : Fin (d + 1)))
        (fun k hk ↦ by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
          exact Finset.mem_Iic.2 (Fin.le_def.2 hk))
        (fun k₁ _ k₂ _ h ↦ Fin.ext (Fin.mk.inj h))
        (fun k' hk' ↦ ⟨k'.castSucc,
          Finset.mem_filter.2 ⟨Finset.mem_univ _, Fin.le_def.1 (Finset.mem_Iic.1 hk')⟩,
          Fin.ext rfl⟩)
        fun _ _ ↦ rfl
    · refine Finset.sum_bij
        (fun k hk ↦ (⟨(k : ℕ) - 1, by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_le] at hk; omega⟩ :
            Fin (d + 1)))
        (fun k hk ↦ by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_le] at hk
          exact Finset.mem_Ici.2 (by simp only [Fin.le_def]; omega))
        (fun k₁ hk₁ k₂ hk₂ h ↦ by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_le] at hk₁ hk₂
          have hv := Fin.mk.inj h
          exact Fin.ext (by omega))
        (fun k' hk' ↦ ⟨k'.succ, by
          have hk'_le := Fin.le_def.1 (Finset.mem_Ici.1 hk')
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_le, Fin.val_succ]
          omega, Fin.ext (by simp)⟩)
        fun k hk ↦ by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_le] at hk
          exact congrArg (g m) (Fin.ext (by simp only [Fin.val_succ]; omega))
  simp_rw [hrow, Finset.sum_add_distrib]
  congr 1
  · rw [Finset.sum_sigma', Finset.sum_sigma']
    refine Finset.sum_bij (fun x _ ↦ ⟨x.2, x.1⟩)
      (fun x hx ↦ by
        simp only [Finset.mem_sigma, Finset.mem_univ, Finset.mem_Iic, Finset.mem_Ici,
          true_and] at hx ⊢
        exact hx)
      (fun x₁ _ x₂ _ h ↦ by
        cases x₁; cases x₂
        simp only [Sigma.mk.inj_iff, heq_eq_eq] at h
        exact Sigma.ext h.2 (heq_of_eq h.1))
      (fun y hy ↦ ⟨⟨y.2, y.1⟩, by
        simp only [Finset.mem_sigma, Finset.mem_univ, Finset.mem_Ici, Finset.mem_Iic,
          true_and] at hy ⊢
        exact hy, rfl⟩)
      fun _ _ ↦ rfl
  · rw [Finset.sum_sigma', Finset.sum_sigma']
    refine Finset.sum_bij (fun x _ ↦ ⟨x.2, x.1⟩)
      (fun x hx ↦ by
        simp only [Finset.mem_sigma, Finset.mem_univ, Finset.mem_Ici, Finset.mem_Iic,
          true_and] at hx ⊢
        exact hx)
      (fun x₁ _ x₂ _ h ↦ by
        cases x₁; cases x₂
        simp only [Sigma.mk.inj_iff, heq_eq_eq] at h
        exact Sigma.ext h.2 (heq_of_eq h.1))
      (fun y hy ↦ ⟨⟨y.2, y.1⟩, by
        simp only [Finset.mem_sigma, Finset.mem_univ, Finset.mem_Iic, Finset.mem_Ici,
          true_and] at hy ⊢
        exact hy, rfl⟩)
      fun _ _ ↦ rfl

private theorem endpoints_rearrange {G : Type*} [AddCommGroup G] (u v x y : G) (h : x + y = 0) :
    (u + x) + (y + -v) = u - v := by
  have h1 : (u + x) + (y + -v) = (u - v) + (x + y) := by abel
  rw [h1, h, add_zero]

private theorem coboundary_homotopy_rearrange {G : Type*} [AddCommGroup G] (u x y : G) :
    u + (x + -u + y) = x + y := by
  abel

/-- The zeroth and last face sums in `h_{d+1} (b Θ) a` telescope across `k` to
`Θ a - ((res_r Θ)#Tr) a`. -/
private theorem prismHomotopy_endpoints_sum (r : ι) (d : ℕ)
    (Θ : MultilinearMap (RingHom.id R) (fun _ : Fin (d + 2) ↦ Matrix ι ι A) M)
    (a : Fin (d + 2) → Matrix ι ι A) :
    (∑ k : Fin (d + 2), (-1 : ℤ) ^ ((d + 1) * (k : ℕ)) •
        ∑ q : Fin ((k : ℕ) + 1) → ι,
          Θ (hochschildFace 0
            (prismTuple (R := R) r k q (a ∘ (finRotate (d + 2) ^ (k : ℕ)).symm)))) +
      (∑ k : Fin (d + 2), (-1 : ℤ) ^ ((d + 1) * (k : ℕ)) •
        ∑ q : Fin ((k : ℕ) + 1) → ι,
          (-1 : ℤ) ^ (d + 2) •
            Θ (hochschildFace (Fin.last (d + 2))
              (prismTuple (R := R) r k q (a ∘ (finRotate (d + 2) ^ (k : ℕ)).symm)))) =
      Θ a - matrixCochainExtension ι (d + 1) (cornerCochainRestriction r (d + 1) Θ) a := by
  have hzero0 :
      (-1 : ℤ) ^ ((d + 1) * ((0 : Fin (d + 2)) : ℕ)) •
        ∑ q : Fin (((0 : Fin (d + 2)) : ℕ) + 1) → ι,
          Θ (hochschildFace 0
            (prismTuple (R := R) r 0 q
              (a ∘ (finRotate (d + 2) ^ ((0 : Fin (d + 2)) : ℕ)).symm))) = Θ a := by
    have h1 : (-1 : ℤ) ^ ((d + 1) * ((0 : Fin (d + 2)) : ℕ)) = 1 := by simp
    rw [h1, one_smul]
    exact sum_hochschildFace_zero_prismTuple_zero r 0 rfl Θ a
  have hlast_top :
      (-1 : ℤ) ^ ((d + 1) * ((Fin.last (d + 1)) : ℕ)) •
        ∑ q : Fin (((Fin.last (d + 1)) : ℕ) + 1) → ι,
          (-1 : ℤ) ^ (d + 2) •
            Θ (hochschildFace (Fin.last (d + 2))
              (prismTuple (R := R) r (Fin.last (d + 1)) q
                (a ∘ (finRotate (d + 2) ^ ((Fin.last (d + 1)) : ℕ)).symm))) =
        -matrixCochainExtension ι (d + 1) (cornerCochainRestriction r (d + 1) Θ) a := by
    rw [← Finset.smul_sum, smul_smul, ← pow_add]
    have hsign : (-1 : ℤ) ^ ((d + 1) * ((Fin.last (d + 1)) : ℕ) + (d + 2)) = -1 := by
      rw [Fin.val_last]
      have heven : Even ((d + 1) * (d + 2)) := Nat.even_mul_succ_self (d + 1)
      have hexp : (d + 1) * (d + 1) + (d + 2) = (d + 1) * (d + 2) + 1 := by ring
      rw [hexp, pow_add, heven.neg_one_pow, one_mul, pow_one]
    rw [hsign, neg_one_smul]
    exact congrArg Neg.neg
      (sum_hochschildFace_last_prismTuple_last r (Fin.last (d + 1)) rfl Θ a)
  have htel :
      (∑ l : Fin (d + 1), (-1 : ℤ) ^ ((d + 1) * (l.succ : ℕ)) •
          ∑ q : Fin ((l.succ : ℕ) + 1) → ι,
            Θ (hochschildFace 0
              (prismTuple (R := R) r l.succ q
                (a ∘ (finRotate (d + 2) ^ (l.succ : ℕ)).symm)))) +
        (∑ l : Fin (d + 1), (-1 : ℤ) ^ ((d + 1) * (l.castSucc : ℕ)) •
          ∑ p : Fin ((l.castSucc : ℕ) + 1) → ι,
            (-1 : ℤ) ^ (d + 2) •
              Θ (hochschildFace (Fin.last (d + 2))
                (prismTuple (R := R) r l.castSucc p
                  (a ∘ (finRotate (d + 2) ^ (l.castSucc : ℕ)).symm)))) = 0 := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun l _ ↦ ?_
    let c := a ∘ (finRotate (d + 2) ^ (l.castSucc : ℕ)).symm
    let S₁ : M := ∑ q : Fin ((l.succ : ℕ) + 1) → ι,
      Θ (hochschildFace 0
        (prismTuple (R := R) r l.succ q (a ∘ (finRotate (d + 2) ^ (l.succ : ℕ)).symm)))
    have hrot : a ∘ (finRotate (d + 2) ^ (l.succ : ℕ)).symm = c ∘ (finRotate (d + 2)).symm := by
      simp only [c, Fin.val_succ, Fin.val_castSucc]
      exact comp_perm_pow_succ_symm a (finRotate (d + 2)) l
    have hS :
        (∑ p : Fin ((l.castSucc : ℕ) + 1) → ι,
            Θ (hochschildFace (Fin.last (d + 2)) (prismTuple (R := R) r l.castSucc p c))) =
          S₁ :=
      (sum_hochschildFace_last_eq_sum_hochschildFace_zero_succ (R := R) r Θ l c).trans
        (Finset.sum_congr rfl fun q _ ↦ by rw [hrot])
    have hsign : (-1 : ℤ) ^ ((d + 1) * (l.castSucc : ℕ) + (d + 2)) =
        -((-1 : ℤ) ^ ((d + 1) * (l.succ : ℕ))) := by
      simp only [Fin.val_succ, Fin.val_castSucc]
      have hexp : (d + 1) * (l : ℕ) + (d + 2) = (d + 1) * ((l : ℕ) + 1) + 1 := by ring
      rw [hexp, pow_succ, mul_neg_one]
    have hterm2 :
        (-1 : ℤ) ^ ((d + 1) * (l.castSucc : ℕ)) •
          ∑ p : Fin ((l.castSucc : ℕ) + 1) → ι,
            (-1 : ℤ) ^ (d + 2) •
              Θ (hochschildFace (Fin.last (d + 2)) (prismTuple (R := R) r l.castSucc p c)) =
          -((-1 : ℤ) ^ ((d + 1) * (l.succ : ℕ)) • S₁) := by
      rw [← Finset.smul_sum, hS, smul_smul, ← pow_add, hsign, neg_smul]
    exact (congrArg ((-1 : ℤ) ^ ((d + 1) * (l.succ : ℕ)) • S₁ + ·) hterm2).trans
      (add_neg_cancel _)
  have hfirst := (Fin.sum_univ_succ fun k : Fin (d + 2) ↦
    (-1 : ℤ) ^ ((d + 1) * (k : ℕ)) • ∑ q : Fin ((k : ℕ) + 1) → ι,
      Θ (hochschildFace 0
        (prismTuple (R := R) r k q (a ∘ (finRotate (d + 2) ^ (k : ℕ)).symm)))).trans
    (congrArg (· + _) hzero0)
  have hsecond := (Fin.sum_univ_castSucc fun k : Fin (d + 2) ↦
    (-1 : ℤ) ^ ((d + 1) * (k : ℕ)) • ∑ q : Fin ((k : ℕ) + 1) → ι,
      (-1 : ℤ) ^ (d + 2) • Θ (hochschildFace (Fin.last (d + 2))
        (prismTuple (R := R) r k q (a ∘ (finRotate (d + 2) ^ (k : ℕ)).symm)))).trans
    (congrArg (_ + ·) hlast_top)
  exact (congrArg₂ HAdd.hAdd hfirst hsecond).trans (endpoints_rearrange _ _ _ _ htel)

variable [IsScalarTower R A A]

/-- The inner-face sum in `h_{d+1} (b Θ) a` equals `-b (h_d Θ) a`. -/
private theorem prismHomotopy_inner_sum (r : ι) (d : ℕ)
    (Θ : MultilinearMap (RingHom.id R) (fun _ : Fin (d + 2) ↦ Matrix ι ι A) M)
    (a : Fin (d + 2) → Matrix ι ι A) :
    (∑ k : Fin (d + 2), (-1 : ℤ) ^ ((d + 1) * (k : ℕ)) •
        ∑ q : Fin ((k : ℕ) + 1) → ι,
          ∑ m : Fin (d + 1), (-1 : ℤ) ^ ((m : ℕ) + 1) •
            Θ (hochschildFace m.succ.castSucc
              (prismTuple (R := R) r k q (a ∘ (finRotate (d + 2) ^ (k : ℕ)).symm)))) =
      -hochschildCoboundary R (Matrix ι ι A) M d (matrixHochschildHomotopy r d Θ) a := by
  have hlhs :
      (∑ k : Fin (d + 2), (-1 : ℤ) ^ ((d + 1) * (k : ℕ)) •
          ∑ q : Fin ((k : ℕ) + 1) → ι,
            ∑ m : Fin (d + 1), (-1 : ℤ) ^ ((m : ℕ) + 1) •
              Θ (hochschildFace m.succ.castSucc
                (prismTuple (R := R) r k q (a ∘ (finRotate (d + 2) ^ (k : ℕ)).symm)))) =
        ∑ m : Fin (d + 1), ∑ k : Fin (d + 2),
          (-1 : ℤ) ^ ((d + 1) * (k : ℕ) + ((m : ℕ) + 1)) •
            ∑ q : Fin ((k : ℕ) + 1) → ι,
              Θ (hochschildFace m.succ.castSucc
                (prismTuple (R := R) r k q (a ∘ (finRotate (d + 2) ^ (k : ℕ)).symm))) := by
    simp_rw [Finset.sum_comm (s := Finset.univ (α := Fin _ → ι)), ← Finset.smul_sum,
      Finset.smul_sum, smul_smul, ← pow_add]
    exact Finset.sum_comm
  let F (i : Fin (d + 2)) (k' : Fin (d + 1)) : M :=
    (-1 : ℤ) ^ ((i : ℕ) + d * (k' : ℕ)) •
      ∑ p : Fin ((k' : ℕ) + 1) → ι,
        Θ (prismTuple (R := R) r k' p
          (hochschildFace i a ∘ (finRotate (d + 1) ^ (k' : ℕ)).symm))
  have hrhs :
      -hochschildCoboundary R (Matrix ι ι A) M d (matrixHochschildHomotopy r d Θ) a =
        ∑ k' : Fin (d + 1), ∑ i : Fin (d + 2), -F i k' := by
    rw [hochschildCoboundary_apply, ← Finset.sum_neg_distrib]
    have hinner (i : Fin (d + 2)) :
        -((-1 : ℤ) ^ (i : ℕ) • matrixHochschildHomotopy r d Θ (hochschildFace i a)) =
          ∑ k' : Fin (d + 1), -F i k' := by
      rw [matrixHochschildHomotopy_apply, Finset.smul_sum, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun k' _ ↦ ?_
      dsimp only [F]
      rw [smul_smul, ← pow_add]
    simp_rw [hinner]
    exact Finset.sum_comm
  rw [hlhs, sum_fin_succ_split d, ← Finset.sum_add_distrib, hrhs]
  refine Finset.sum_congr rfl fun k' _ ↦ ?_
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun i : Fin (d + 2) ↦ (i : ℕ) + k' ≤ d)]
  congr 1
  · refine Finset.sum_bij (fun m _ ↦ (⟨(m : ℕ) - k', by omega⟩ : Fin (d + 2)))
      (fun m hm ↦ by
        have hkm := Fin.le_def.1 (Finset.mem_Ici.1 hm)
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        omega)
      (fun m₁ hm₁ m₂ hm₂ h ↦ by
        have hkm₁ := Fin.le_def.1 (Finset.mem_Ici.1 hm₁)
        have hkm₂ := Fin.le_def.1 (Finset.mem_Ici.1 hm₂)
        have hv := Fin.mk.inj h
        exact Fin.ext (by omega))
      (fun i hi ↦ ⟨⟨(i : ℕ) + k', by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi; omega⟩,
        Finset.mem_Ici.2 (Fin.le_def.2 (Nat.le_add_left _ _)), Fin.ext (by simp)⟩)
      fun m hm ↦ ?_
    have hkm : (k' : ℕ) ≤ m := Fin.le_def.1 (Finset.mem_Ici.1 hm)
    simp only [Fin.val_castSucc, hochschildFace_succ_prismTuple_of_le r k' m hkm]
    have hm_eq : m.castSucc = ⟨((m : ℕ) - k') + k', by omega⟩ := Fin.ext (by simp; omega)
    rw [hm_eq, hochschildFace_add_comp_finRotate_symm_pow a (by omega)]
    have hsign : (-1 : ℤ) ^ ((d + 1) * (k' : ℕ) + ((m : ℕ) + 1)) =
        -((-1 : ℤ) ^ (((m : ℕ) - k') + d * (k' : ℕ))) := by
      have hmul_dk : (d + 1) * (k' : ℕ) = d * k' + k' := Nat.succ_mul d k'
      have hexp : (d + 1) * (k' : ℕ) + ((m : ℕ) + 1) =
          (((m : ℕ) - k') + d * (k' : ℕ)) + (2 * (k' : ℕ) + 1) := by omega
      rw [hexp, pow_add, Odd.neg_one_pow ⟨k', rfl⟩, mul_neg_one]
    dsimp only [F]
    rw [hsign, neg_smul]
  · refine Finset.sum_bij (fun m hm ↦ (⟨d + 1 + m - k', by
        have := Fin.le_def.1 (Finset.mem_Iic.1 hm); omega⟩ : Fin (d + 2)))
      (fun m hm ↦ by
        have := Fin.le_def.1 (Finset.mem_Iic.1 hm)
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_le]
        omega)
      (fun m₁ hm₁ m₂ hm₂ h ↦ by
        have := Fin.le_def.1 (Finset.mem_Iic.1 hm₁)
        have := Fin.le_def.1 (Finset.mem_Iic.1 hm₂)
        have hv := Fin.mk.inj h
        exact Fin.ext (by omega))
      (fun i hi ↦ ⟨⟨(i : ℕ) + k' - (d + 1), by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_le] at hi; omega⟩,
        by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_le] at hi
          exact Finset.mem_Iic.2 (by simp only [Fin.le_def]; have := i.isLt; omega),
        Fin.ext (by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_le] at hi
          dsimp only
          have := i.isLt
          have := k'.isLt
          omega)⟩)
      fun m hm ↦ ?_
    have hmk : (m : ℕ) ≤ k' := Fin.le_def.1 (Finset.mem_Iic.1 hm)
    rw [sum_hochschildFace_succ_prismTuple_of_gt r Θ k' m hmk]
    simp only [Fin.val_succ]
    rw [hochschildFace_lt_comp_finRotate_symm_pow_succ a m k' hmk]
    have hsign : (-1 : ℤ) ^ ((d + 1) * ((k' : ℕ) + 1) + ((m : ℕ) + 1)) =
        -((-1 : ℤ) ^ ((d + 1 + m - k') + d * (k' : ℕ))) := by
      have hexp_dk : (d + 1) * ((k' : ℕ) + 1) = d * k' + d + k' + 1 := by ring
      have := k'.isLt
      have hsum_odd : Odd (((d + 1) * ((k' : ℕ) + 1) + ((m : ℕ) + 1)) +
          ((d + 1 + m - k') + d * (k' : ℕ))) :=
        ⟨d * k' + d + m + 1, by omega⟩
      have hmul : (-1 : ℤ) ^ ((d + 1) * ((k' : ℕ) + 1) + ((m : ℕ) + 1)) *
          (-1 : ℤ) ^ ((d + 1 + m - k') + d * (k' : ℕ)) = -1 := by
        rw [← pow_add, hsum_odd.neg_one_pow]
      have hsq : (-1 : ℤ) ^ ((d + 1 + m - k') + d * (k' : ℕ)) *
          (-1 : ℤ) ^ ((d + 1 + m - k') + d * (k' : ℕ)) = 1 := by
        rw [← pow_add, ← two_mul, pow_mul]
        norm_num
      calc (-1 : ℤ) ^ ((d + 1) * ((k' : ℕ) + 1) + ((m : ℕ) + 1))
          = (-1 : ℤ) ^ ((d + 1) * ((k' : ℕ) + 1) + ((m : ℕ) + 1)) *
              ((-1 : ℤ) ^ ((d + 1 + m - k') + d * (k' : ℕ)) *
                (-1 : ℤ) ^ ((d + 1 + m - k') + d * (k' : ℕ))) := by rw [hsq, mul_one]
        _ = ((-1 : ℤ) ^ ((d + 1) * ((k' : ℕ) + 1) + ((m : ℕ) + 1)) *
              (-1 : ℤ) ^ ((d + 1 + m - k') + d * (k' : ℕ))) *
              (-1 : ℤ) ^ ((d + 1 + m - k') + d * (k' : ℕ)) := by ring
        _ = -((-1 : ℤ) ^ ((d + 1 + m - k') + d * (k' : ℕ))) := by rw [hmul, neg_one_mul]
    dsimp only [F]
    rw [hsign, neg_smul]

/-! #### The chain-homotopy theorems -/

/-- **Degree-zero homotopy identity.** On `0`-cochains of `Matrix ι ι A`,
`h₀ (b Ψ) = Ψ - (res_r Ψ)#Tr`. In particular, every trace on `Matrix ι ι A` equals the matrix
extension of its `(r, r)` corner restriction. -/
theorem matrixHochschildHomotopy_hochschildCoboundary_zero (r : ι)
    (Ψ : MultilinearMap (RingHom.id R) (fun _ : Fin 1 ↦ Matrix ι ι A) M) :
    matrixHochschildHomotopy r 0 (hochschildCoboundary R (Matrix ι ι A) M 0 Ψ) =
      Ψ - matrixCochainExtension ι 0 (cornerCochainRestriction r 0 Ψ) := by
  ext a
  rw [matrixHochschildHomotopy_apply, Fin.sum_univ_one, sub_apply]
  have h1 : (-1 : ℤ) ^ (0 * ((0 : Fin 1) : ℕ)) = 1 := rfl
  rw [h1, one_smul]
  have hb (q : Fin (((0 : Fin 1) : ℕ) + 1) → ι) :
      hochschildCoboundary R (Matrix ι ι A) M 0 Ψ
          (prismTuple (R := R) r 0 q (a ∘ (finRotate 1 ^ ((0 : Fin 1) : ℕ)).symm)) =
        Ψ (hochschildFace 0
            (prismTuple (R := R) r 0 q (a ∘ (finRotate 1 ^ ((0 : Fin 1) : ℕ)).symm))) -
          Ψ (hochschildFace (Fin.last 1)
            (prismTuple (R := R) r 0 q (a ∘ (finRotate 1 ^ ((0 : Fin 1) : ℕ)).symm))) := by
    rw [hochschildCoboundary_apply, Fin.sum_univ_two]
    simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_one, neg_one_smul,
      ← sub_eq_add_neg]
    rfl
  simp_rw [hb, Finset.sum_sub_distrib]
  exact congrArg₂ Sub.sub (sum_hochschildFace_zero_prismTuple_zero r 0 rfl Ψ a)
    (sum_hochschildFace_last_prismTuple_last r 0 rfl Ψ a)

/-- **Positive-degree homotopy identity.** On `(d + 1)`-cochains of `Matrix ι ι A`,
`b (h_d Θ) + h_{d+1} (b Θ) = Θ - (res_r Θ)#Tr`. -/
theorem hochschildCoboundary_matrixHochschildHomotopy_add (r : ι) (d : ℕ)
    (Θ : MultilinearMap (RingHom.id R) (fun _ : Fin (d + 2) ↦ Matrix ι ι A) M) :
    hochschildCoboundary R (Matrix ι ι A) M d (matrixHochschildHomotopy r d Θ) +
        matrixHochschildHomotopy r (d + 1)
          (hochschildCoboundary R (Matrix ι ι A) M (d + 1) Θ) =
      Θ - matrixCochainExtension ι (d + 1) (cornerCochainRestriction r (d + 1) Θ) := by
  ext a
  have hb_split (k : Fin (d + 2)) (q : Fin ((k : ℕ) + 1) → ι)
      (b : Fin (d + 2) → Matrix ι ι A) :
      hochschildCoboundary R (Matrix ι ι A) M (d + 1) Θ (prismTuple (R := R) r k q b) =
        Θ (hochschildFace 0 (prismTuple (R := R) r k q b)) +
          (∑ m : Fin (d + 1), (-1 : ℤ) ^ ((m : ℕ) + 1) •
            Θ (hochschildFace m.succ.castSucc (prismTuple (R := R) r k q b))) +
          (-1 : ℤ) ^ (d + 2) •
            Θ (hochschildFace (Fin.last (d + 2)) (prismTuple (R := R) r k q b)) := by
    rw [hochschildCoboundary_apply, Fin.sum_univ_castSucc, Fin.sum_univ_succ]
    simp [add_assoc]
  rw [add_apply, sub_apply, matrixHochschildHomotopy_apply r (d + 1)]
  simp_rw [hb_split, Finset.sum_add_distrib, smul_add, Finset.sum_add_distrib]
  rw [prismHomotopy_inner_sum r d Θ a, coboundary_homotopy_rearrange]
  exact prismHomotopy_endpoints_sum r d Θ a

/-- Every Hochschild cocycle on `Matrix ι ι A` differs from the matrix extension of its `(r, r)`
corner restriction by a Hochschild coboundary. -/
theorem sub_matrixCochainExtension_cornerCochainRestriction_mem_hochschildCoboundaries
    (r : ι) {n : ℕ}
    {Θ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ Matrix ι ι A) M}
    (hΘ : Θ ∈ hochschildCocycles R (Matrix ι ι A) M n) :
    Θ - matrixCochainExtension ι n (cornerCochainRestriction r n Θ) ∈
      hochschildCoboundaries R (Matrix ι ι A) M n := by
  rw [mem_hochschildCocycles_iff] at hΘ
  cases n with
  | zero =>
    rw [hochschildCoboundaries_zero, Submodule.mem_bot,
      ← matrixHochschildHomotopy_hochschildCoboundary_zero r Θ, hΘ, map_zero]
  | succ d =>
    rw [mem_hochschildCoboundaries_succ_iff]
    refine ⟨matrixHochschildHomotopy r d Θ, ?_⟩
    have h := hochschildCoboundary_matrixHochschildHomotopy_add r d Θ
    rwa [hΘ, map_zero, add_zero] at h

end Semiring

end PrismHomotopy

/-! ### Matrix Morita invariance on Hochschild cohomology -/

namespace hochschildCohomology

section NonUnital

variable {R A M : Type*} [CommRing R] [NonUnitalSemiring A] [Module R A] [IsScalarTower R A A]
  [SMulCommClass R A A] [AddCommGroup M] [Module R M]

variable (M) in
/-- **Matrix extension on Hochschild cohomology**, sending the class of a Hochschild cocycle `φ` to
the class of its generalized matrix trace `φ#Tr`. -/
def matrixExtension (ι : Type*) [Fintype ι] (n : ℕ) :
    hochschildCohomology R A M n →ₗ[R] hochschildCohomology R (Matrix ι ι A) M n :=
  desc n
    (mk R (Matrix ι ι A) M n ∘ₗ (matrixCochainExtension ι n).restrict
      fun _ ↦ matrixCochainExtension_mem_hochschildCocycles)
    fun _ hφ ↦ (mk_eq_zero_iff R (Matrix ι ι A) M n _).2
      (matrixCochainExtension_mem_hochschildCoboundaries hφ)

/-- `matrixExtension` sends `[φ]` to `[φ#Tr]`. -/
@[simp]
theorem matrixExtension_mk (ι : Type*) [Fintype ι] {n : ℕ} (φ : hochschildCocycles R A M n) :
    matrixExtension M ι n (mk R A M n φ) =
      mk R (Matrix ι ι A) M n
        ⟨matrixCochainExtension ι n φ.1, matrixCochainExtension_mem_hochschildCocycles φ.2⟩ :=
  desc_mk _ _ _ φ

variable (M) in
/-- **Corner restriction on Hochschild cohomology**, sending the class of a Hochschild cocycle on
`Matrix ι ι A` to the class of its restriction to the `(r, r)` diagonal corner. -/
def cornerRestriction {ι : Type*} [Fintype ι] [DecidableEq ι] (r : ι) (n : ℕ) :
    hochschildCohomology R (Matrix ι ι A) M n →ₗ[R] hochschildCohomology R A M n :=
  desc n
    (mk R A M n ∘ₗ (cornerCochainRestriction r n).restrict
      fun _ ↦ cornerCochainRestriction_mem_hochschildCocycles r)
    fun _ hφ ↦ (mk_eq_zero_iff R A M n _).2
      (cornerCochainRestriction_mem_hochschildCoboundaries r hφ)

/-- `cornerRestriction` sends `[Θ]` to `[cornerCochainRestriction r n Θ]`. -/
@[simp]
theorem cornerRestriction_mk {ι : Type*} [Fintype ι] [DecidableEq ι] (r : ι) {n : ℕ}
    (Θ : hochschildCocycles R (Matrix ι ι A) M n) :
    cornerRestriction M r n (mk R (Matrix ι ι A) M n Θ) =
      mk R A M n
        ⟨cornerCochainRestriction r n Θ.1,
          cornerCochainRestriction_mem_hochschildCocycles r Θ.2⟩ :=
  desc_mk _ _ _ Θ

/-- Corner restriction is a left inverse to matrix extension on Hochschild cohomology, even for
nonunital algebras. -/
@[simp]
theorem cornerRestriction_matrixExtension {ι : Type*} [Fintype ι] [DecidableEq ι] (r : ι)
    (n : ℕ) (c : hochschildCohomology R A M n) :
    cornerRestriction M r n (matrixExtension M ι n c) = c := by
  obtain ⟨φ, rfl⟩ := mk_surjective R A M n c
  rw [matrixExtension_mk, cornerRestriction_mk]
  congr 1
  exact Subtype.ext (cornerCochainRestriction_matrixCochainExtension r n φ.1)

/-- Matrix extension on Hochschild cohomology is injective for every nonempty finite index type,
even for nonunital algebras. -/
theorem injective_matrixExtension (ι : Type*) [Fintype ι] [Nonempty ι] (n : ℕ) :
    Function.Injective (matrixExtension (R := R) (A := A) M ι n) := by
  classical
  obtain ⟨r⟩ := ‹Nonempty ι›
  exact Function.LeftInverse.injective (cornerRestriction_matrixExtension r n)

end NonUnital

section Unital

variable {R A M : Type*} [CommRing R] [Semiring A] [Module R A] [IsScalarTower R A A]
  [SMulCommClass R A A] [AddCommGroup M] [Module R M]

/-- For a unital algebra, matrix extension is also a left inverse to corner restriction on
Hochschild cohomology. -/
@[simp]
theorem matrixExtension_cornerRestriction {ι : Type*} [Fintype ι] [DecidableEq ι] (r : ι)
    (n : ℕ) (c : hochschildCohomology R (Matrix ι ι A) M n) :
    matrixExtension M ι n (cornerRestriction M r n c) = c := by
  obtain ⟨Θ, rfl⟩ := mk_surjective R (Matrix ι ι A) M n c
  rw [cornerRestriction_mk, matrixExtension_mk, eq_comm, mk_eq_mk_iff]
  exact sub_matrixCochainExtension_cornerCochainRestriction_mem_hochschildCoboundaries r Θ.2

/-- **Matrix Morita invariance of Hochschild cohomology.** For a unital algebra `A` over any
commutative ring `R`, coefficients in an `R`-module `M`, and a nonempty finite index type `ι`,
matrix extension `HHⁿ(A, Hom_R(A, M)) → HHⁿ(Matrix ι ι A, Hom_R(Matrix ι ι A, M))` is bijective in
every degree `n`. -/
theorem bijective_matrixExtension (ι : Type*) [Fintype ι] [Nonempty ι] (n : ℕ) :
    Function.Bijective (matrixExtension (R := R) (A := A) M ι n) := by
  classical
  obtain ⟨r⟩ := ‹Nonempty ι›
  exact ⟨Function.LeftInverse.injective (cornerRestriction_matrixExtension r n),
    Function.RightInverse.surjective (matrixExtension_cornerRestriction r n)⟩

variable (M) in
/-- **Matrix Morita equivalence for Hochschild cohomology** as an `R`-linear equivalence
`HHⁿ(A, Hom_R(A, M)) ≃ₗ[R] HHⁿ(Matrix ι ι A, Hom_R(Matrix ι ι A, M))`. -/
def matrixExtensionEquiv (ι : Type*) [Fintype ι] [Nonempty ι] (n : ℕ) :
    hochschildCohomology R A M n ≃ₗ[R] hochschildCohomology R (Matrix ι ι A) M n :=
  LinearEquiv.ofBijective (matrixExtension M ι n) (bijective_matrixExtension ι n)

/-- Applying `matrixExtensionEquiv` agrees with `matrixExtension`. -/
@[simp]
theorem matrixExtensionEquiv_apply (ι : Type*) [Fintype ι] [Nonempty ι] (n : ℕ)
    (c : hochschildCohomology R A M n) :
    matrixExtensionEquiv M ι n c = matrixExtension M ι n c :=
  (rfl)

/-- The inverse of `matrixExtensionEquiv` is corner restriction at any index `r : ι`. -/
theorem matrixExtensionEquiv_symm_apply {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (r : ι) (n : ℕ) (c : hochschildCohomology R (Matrix ι ι A) M n) :
    (matrixExtensionEquiv M ι n).symm c = cornerRestriction M r n c := by
  apply (matrixExtensionEquiv M ι n).injective
  rw [LinearEquiv.apply_symm_apply, matrixExtensionEquiv_apply, matrixExtension_cornerRestriction]

/-- For a unital algebra, corner restriction on Hochschild cohomology is independent of the chosen
diagonal corner. -/
theorem cornerRestriction_eq {ι : Type*} [Fintype ι] [DecidableEq ι] (r s : ι) (n : ℕ) :
    cornerRestriction (R := R) (A := A) M r n = cornerRestriction (R := R) (A := A) M s n := by
  have : Nonempty ι := ⟨r⟩
  refine LinearMap.ext fun c ↦ ?_
  rw [← matrixExtensionEquiv_symm_apply r n c, ← matrixExtensionEquiv_symm_apply s n c]

end Unital

end hochschildCohomology

end TauCeti
