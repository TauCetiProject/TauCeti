/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import TauCeti.RingTheory.Polynomial.RootEnumeration
import TauCeti.Data.Multiset.Fintype
import TauCeti.LinearAlgebra.Matrix.Charpoly.Roots
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Map
import TauCeti.LinearAlgebra.Matrix.Nonsingular.Inverse
import TauCeti.RingTheory.Polynomial.Roots

/-!
# Generic Frobenius eigenvalues

Let `ℓ ≠ p` be primes, `L/ℚ_p` a finite extension whose residue field has `q` elements and `k` a
finite field of characteristic `ℓ`. Allen, Calegari, Caraiani, Gee, Helm, Le Hung, Newton,
Scholze, Taylor and Thorne call a continuous `r : G_L → GL_n(k)` *generic* if it is unramified
and the eigenvalues `α₁, …, αₙ` of `r(Frob_L)` in an algebraic closure of `k`, listed with
multiplicity, satisfy `αᵢ / αⱼ ≠ q` for all `i ≠ j`. Caraiani and Scholze use the stronger
condition that moreover `αᵢ ≠ αⱼ` for `i ≠ j`. Imposed at the places above a rational prime that
splits completely in the base field, these local conditions are the genericity hypotheses on
residual representations under which those authors control the torsion in the cohomology of
locally symmetric spaces and Shimura varieties.

This file sets up these conditions at three levels.

* For a family `α` of eigenvalues, `TauCeti.IsGenericEigenvalues q α` says that `αᵢ ≠ q αⱼ`
  whenever `i ≠ j`, and `TauCeti.IsStronglyGenericEigenvalues q α` says that moreover
  `αᵢ ≠ αⱼ`. Repeated eigenvalues are allowed by the first condition (as long as `q ≠ 1`), and
  pairwise distinct eigenvalues need not satisfy it. Both conditions are invariant under
  reindexing, a common cancellable scalar, inversion and injective multiplicative maps, and
  depend only on the multiset of eigenvalues.
* For a square matrix `A` over a field `K`, `Matrix.IsGenericAt A q` and
  `Matrix.IsStronglyGenericAt A q` ask the same of the characteristic roots of `A` in an
  algebraic closure of `K`. They can be tested on any listing of these roots, with one entry per
  row of `A`, in any field extension (`Matrix.isGenericAt_iff_of_isRootEnumeration`), and are
  invariant under conjugation, inversion and extension of scalars.
* For a representation `ρ : G →* GL n K`, a subgroup `I` (the inertia group) and an element
  `frob` (a Frobenius lift), `MonoidHom.IsGenericAt ρ I frob q` says that `I` acts trivially and
  `ρ frob` is generic at `q`; similarly `MonoidHom.IsStronglyGenericAt`. When `I` acts trivially
  the condition does not depend on the choice of Frobenius lift, and arithmetic and geometric
  Frobenius give the same condition.

## Main definitions

* `TauCeti.IsGenericEigenvalues`, `TauCeti.IsStronglyGenericEigenvalues`: the eigenvalue
  conditions.
* `Matrix.IsGenericAt`, `Matrix.IsStronglyGenericAt`: genericity of the characteristic roots of a
  matrix.
* `MonoidHom.IsGenericAt`, `MonoidHom.IsStronglyGenericAt`: genericity of a representation at a
  Frobenius element, including the triviality of inertia.

## Main statements

* `TauCeti.isStronglyGenericEigenvalues_iff_injective_and`: strong genericity is genericity
  together with pairwise distinctness.
* `TauCeti.isStronglyGenericEigenvalues_iff_div_notMem`: for nonzero eigenvalues, strong
  genericity excludes the two ratios `1` and `q`.
* `TauCeti.isGenericEigenvalues_iff_of_map_univ_val_eq`,
  `TauCeti.isStronglyGenericEigenvalues_iff_of_map_univ_val_eq`: genericity and strong genericity
  depend only on the multiset of eigenvalues.
* `Matrix.isGenericAt_iff_of_isRootEnumeration`: genericity of a matrix is genericity of any
  listing of its characteristic roots with one entry per row of the matrix.
* `Matrix.isGenericAt_one_iff`: a matrix is generic at `1` exactly when its characteristic
  polynomial is separable; in particular strongly generic matrices and representations have
  pairwise distinct Frobenius eigenvalues.
* `Matrix.isGenericAt_diagonal_iff`: a diagonal matrix is generic exactly when its diagonal is.
* `MonoidHom.isGenericAt_iff_of_inv_mul_mem`: independence of the Frobenius lift.
* `MonoidHom.isGenericAt_inv_iff`: arithmetic and geometric Frobenius give the same condition.

## References

* P. B. Allen, F. Calegari, A. Caraiani, T. Gee, D. Helm, B. V. Le Hung, J. Newton, P. Scholze,
  R. Taylor and J. A. Thorne, *Potential automorphy over CM fields*, Ann. of Math. 197 (2023),
  Definition 4.3.1.
* A. Caraiani and P. Scholze, *On the generic part of the cohomology of compact unitary Shimura
  varieties*, Ann. of Math. 186 (2017), Definition 1.9.
-/

public section

open Polynomial

namespace TauCeti

section Eigenvalues

variable {ι κ R : Type*}

/-- A family of eigenvalues `α` is **generic** at `q` if `α i ≠ q * α j` whenever `i ≠ j`: no
ordered pair of eigenvalues at distinct positions has ratio `q`. Eigenvalues are counted with
multiplicity, so for `q = 1` this asks the eigenvalues to be distinct. -/
def IsGenericEigenvalues [Mul R] (q : R) (α : ι → R) : Prop :=
  Pairwise fun i j ↦ α i ≠ q * α j

/-- A family of eigenvalues `α` is **strongly generic** at `q` if `α i ≠ α j` and
`α i ≠ q * α j` whenever `i ≠ j`: no ordered pair of eigenvalues at distinct positions has ratio
`1` or `q`. -/
def IsStronglyGenericEigenvalues [Mul R] (q : R) (α : ι → R) : Prop :=
  Pairwise fun i j ↦ α i ≠ α j ∧ α i ≠ q * α j

section Mul

variable [Mul R] {q : R} {α : ι → R}

/-- The defining condition of `TauCeti.IsGenericEigenvalues`. -/
theorem isGenericEigenvalues_iff :
    IsGenericEigenvalues q α ↔ ∀ i j, i ≠ j → α i ≠ q * α j :=
  Iff.rfl

/-- The defining condition of `TauCeti.IsStronglyGenericEigenvalues`. -/
theorem isStronglyGenericEigenvalues_iff :
    IsStronglyGenericEigenvalues q α ↔ ∀ i j, i ≠ j → α i ≠ α j ∧ α i ≠ q * α j :=
  Iff.rfl

/-- Strong genericity is genericity together with pairwise distinctness of the eigenvalues. -/
theorem isStronglyGenericEigenvalues_iff_injective_and :
    IsStronglyGenericEigenvalues q α ↔ Function.Injective α ∧ IsGenericEigenvalues q α := by
  rw [Function.injective_iff_pairwise_ne]
  exact ⟨fun h ↦ ⟨fun i j hij ↦ (h hij).1, fun i j hij ↦ (h hij).2⟩,
    fun h i j hij ↦ ⟨h.1 hij, h.2 hij⟩⟩

/-- Strongly generic eigenvalues are pairwise distinct. -/
theorem IsStronglyGenericEigenvalues.injective (h : IsStronglyGenericEigenvalues q α) :
    Function.Injective α :=
  (isStronglyGenericEigenvalues_iff_injective_and.1 h).1

/-- Strongly generic eigenvalues are generic. -/
theorem IsStronglyGenericEigenvalues.isGenericEigenvalues
    (h : IsStronglyGenericEigenvalues q α) : IsGenericEigenvalues q α :=
  (isStronglyGenericEigenvalues_iff_injective_and.1 h).2

/-- A family with at most one eigenvalue is generic at every `q`. -/
theorem isGenericEigenvalues_of_subsingleton [Subsingleton ι] : IsGenericEigenvalues q α :=
  Subsingleton.pairwise

/-- A family with at most one eigenvalue is strongly generic at every `q`. -/
theorem isStronglyGenericEigenvalues_of_subsingleton [Subsingleton ι] :
    IsStronglyGenericEigenvalues q α :=
  Subsingleton.pairwise

/-- Genericity passes to subfamilies. -/
theorem IsGenericEigenvalues.comp_injective (h : IsGenericEigenvalues q α) {f : κ → ι}
    (hf : Function.Injective f) : IsGenericEigenvalues q (α ∘ f) :=
  fun _ _ hij ↦ h (hf.ne hij)

/-- Strong genericity passes to subfamilies. -/
theorem IsStronglyGenericEigenvalues.comp_injective (h : IsStronglyGenericEigenvalues q α)
    {f : κ → ι} (hf : Function.Injective f) : IsStronglyGenericEigenvalues q (α ∘ f) :=
  fun _ _ hij ↦ h (hf.ne hij)

/-- Genericity does not depend on the order in which the eigenvalues are listed. -/
@[simp]
theorem isGenericEigenvalues_comp_equiv (e : κ ≃ ι) :
    IsGenericEigenvalues q (α ∘ e) ↔ IsGenericEigenvalues q α :=
  ⟨fun h ↦ by simpa [Function.comp_def] using h.comp_injective e.symm.injective,
    fun h ↦ h.comp_injective e.injective⟩

/-- Strong genericity does not depend on the order in which the eigenvalues are listed. -/
@[simp]
theorem isStronglyGenericEigenvalues_comp_equiv (e : κ ≃ ι) :
    IsStronglyGenericEigenvalues q (α ∘ e) ↔ IsStronglyGenericEigenvalues q α :=
  ⟨fun h ↦ by simpa [Function.comp_def] using h.comp_injective e.symm.injective,
    fun h ↦ h.comp_injective e.injective⟩

/-- Genericity is preserved and reflected by an injective multiplicative map, such as an
extension of the coefficient field. -/
@[simp]
theorem isGenericEigenvalues_comp_iff {S F : Type*} [Mul S] [FunLike F R S] [MulHomClass F R S]
    {f : F} (hf : Function.Injective f) :
    IsGenericEigenvalues (f q) (f ∘ α) ↔ IsGenericEigenvalues q α := by
  simp only [isGenericEigenvalues_iff, Function.comp_apply, ← map_mul, hf.ne_iff]

/-- Strong genericity is preserved and reflected by an injective multiplicative map, such as an
extension of the coefficient field. -/
@[simp]
theorem isStronglyGenericEigenvalues_comp_iff {S F : Type*} [Mul S] [FunLike F R S]
    [MulHomClass F R S] {f : F} (hf : Function.Injective f) :
    IsStronglyGenericEigenvalues (f q) (f ∘ α) ↔ IsStronglyGenericEigenvalues q α := by
  simp only [isStronglyGenericEigenvalues_iff, Function.comp_apply, ← map_mul, hf.ne_iff]

end Mul

section MulOneClass

variable [MulOneClass R] {q : R} {α : ι → R}

/-- Genericity at `1` is pairwise distinctness of the eigenvalues. -/
@[simp]
theorem isGenericEigenvalues_one_iff : IsGenericEigenvalues 1 α ↔ Function.Injective α := by
  simp only [IsGenericEigenvalues, one_mul]
  exact Function.injective_iff_pairwise_ne.symm

/-- Strong genericity at `q` is genericity at both `1` and `q`. -/
theorem isStronglyGenericEigenvalues_iff_and :
    IsStronglyGenericEigenvalues q α ↔ IsGenericEigenvalues 1 α ∧ IsGenericEigenvalues q α := by
  rw [isGenericEigenvalues_one_iff, isStronglyGenericEigenvalues_iff_injective_and]

end MulOneClass

section Multiset

variable [Fintype ι] [Fintype κ] [Mul R] {q : R} {α : ι → R}

/-- Genericity read off the multiset of eigenvalues: no two-element submultiset `{a, b}` has
`a = q * b`. -/
theorem isGenericEigenvalues_iff_forall_cons_le :
    IsGenericEigenvalues q α ↔ ∀ a b, a ::ₘ {b} ≤ Finset.univ.val.map α → a ≠ q * b := by
  simp only [Multiset.cons_le_map_univ_val_iff]
  exact ⟨fun h a b ⟨i, j, hij, hi, hj⟩ ↦ hi ▸ hj ▸ h hij,
    fun h i j hij ↦ h _ _ ⟨i, j, hij, rfl, rfl⟩⟩

/-- **Genericity depends only on the multiset of eigenvalues.** Two families with the same
values, counted with multiplicity, are generic together. -/
theorem isGenericEigenvalues_iff_of_map_univ_val_eq {β : κ → R}
    (h : Finset.univ.val.map α = Finset.univ.val.map β) :
    IsGenericEigenvalues q α ↔ IsGenericEigenvalues q β := by
  rw [isGenericEigenvalues_iff_forall_cons_le, isGenericEigenvalues_iff_forall_cons_le, h]

/-- **Strong genericity depends only on the multiset of eigenvalues.** Two families with the same
values, counted with multiplicity, are strongly generic together. -/
theorem isStronglyGenericEigenvalues_iff_of_map_univ_val_eq {R : Type*} [MulOneClass R] {q : R}
    {α : ι → R} {β : κ → R} (h : Finset.univ.val.map α = Finset.univ.val.map β) :
    IsStronglyGenericEigenvalues q α ↔ IsStronglyGenericEigenvalues q β := by
  rw [isStronglyGenericEigenvalues_iff_and, isStronglyGenericEigenvalues_iff_and,
    isGenericEigenvalues_iff_of_map_univ_val_eq h, isGenericEigenvalues_iff_of_map_univ_val_eq h]

end Multiset

/-- Genericity is invariant under multiplying all eigenvalues by a common cancellable scalar,
such as a nonzero element of a field. -/
theorem isGenericEigenvalues_mul_left_iff [CommSemigroup R] {q c : R} (hc : IsLeftRegular c)
    {α : ι → R} : IsGenericEigenvalues q (fun i ↦ c * α i) ↔ IsGenericEigenvalues q α := by
  simp only [isGenericEigenvalues_iff, mul_left_comm q c, ne_eq, hc.eq_iff]

/-- Strong genericity is invariant under multiplying all eigenvalues by a common cancellable
scalar, such as a nonzero element of a field. -/
theorem isStronglyGenericEigenvalues_mul_left_iff [CommSemigroup R] {q c : R}
    (hc : IsLeftRegular c) {α : ι → R} :
    IsStronglyGenericEigenvalues q (fun i ↦ c * α i) ↔ IsStronglyGenericEigenvalues q α := by
  simp only [isStronglyGenericEigenvalues_iff, mul_left_comm q c, ne_eq, hc.eq_iff]

section GroupWithZero

variable [CommGroupWithZero R] {q : R} {α : ι → R}

/-- **Inverting the eigenvalues preserves genericity**: arithmetic and geometric Frobenius
eigenvalues are generic together. -/
@[simp]
theorem isGenericEigenvalues_inv_iff :
    IsGenericEigenvalues q α⁻¹ ↔ IsGenericEigenvalues q α := by
  rcases eq_or_ne q 0 with rfl | hq
  · simp [isGenericEigenvalues_iff]
  -- For `q ≠ 0`, inverting two eigenvalues reverses their ratio.
  have key (a b : R) : a⁻¹ = q * b⁻¹ ↔ b = q * a := by
    rcases eq_or_ne a 0 with rfl | ha
    · simp [hq, eq_comm]
    rcases eq_or_ne b 0 with rfl | -
    · simp [ha, hq]
    rw [inv_eq_iff_eq_inv, mul_inv, inv_inv, eq_inv_mul_iff_mul_eq₀ hq, eq_comm]
  simp only [isGenericEigenvalues_iff, Pi.inv_apply, ne_eq, key]
  exact ⟨fun h i j hij ↦ h j i (Ne.symm hij), fun h i j hij ↦ h j i (Ne.symm hij)⟩

/-- **Inverting the eigenvalues preserves strong genericity.** -/
@[simp]
theorem isStronglyGenericEigenvalues_inv_iff :
    IsStronglyGenericEigenvalues q α⁻¹ ↔ IsStronglyGenericEigenvalues q α := by
  simp only [isStronglyGenericEigenvalues_iff_injective_and, isGenericEigenvalues_inv_iff,
    and_congr_left_iff]
  exact fun _ ↦ ⟨fun h ↦ by simpa [Function.comp_def] using inv_injective.comp h,
    fun h ↦ inv_injective.comp h⟩

/-- For nonzero eigenvalues, genericity at `q` says that no ratio `α i / α j` with `i ≠ j`
equals `q`. -/
theorem isGenericEigenvalues_iff_div_ne (hα : ∀ i, α i ≠ 0) :
    IsGenericEigenvalues q α ↔ ∀ i j, i ≠ j → α i / α j ≠ q := by
  simp only [isGenericEigenvalues_iff, ne_eq, div_eq_iff (hα _), mul_comm q]

/-- For nonzero eigenvalues, strong genericity at `q` says that no ratio `α i / α j` with `i ≠ j`
equals `1` or `q`. -/
theorem isStronglyGenericEigenvalues_iff_div_notMem (hα : ∀ i, α i ≠ 0) :
    IsStronglyGenericEigenvalues q α ↔ ∀ i j, i ≠ j → α i / α j ∉ ({1, q} : Set R) := by
  simp only [isStronglyGenericEigenvalues_iff, Set.mem_insert_iff, Set.mem_singleton_iff,
    not_or, ne_eq, div_eq_iff (hα _), one_mul, mul_comm q]

end GroupWithZero

end Eigenvalues

end TauCeti

namespace Matrix

variable {n m K : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m] [Field K]

/-- A square matrix `A` over a field `K` is **generic** at `q` if its characteristic roots in an
algebraic closure of `K`, listed with multiplicity, are generic at `q`
(`TauCeti.IsGenericEigenvalues`). By `Matrix.isGenericAt_iff_of_isRootEnumeration` the condition
can be tested on any listing of the characteristic roots with as many entries as the size of `A`,
in any field extension of `K`. -/
def IsGenericAt (A : Matrix n n K) (q : K) : Prop :=
  ∃ α : n → AlgebraicClosure K, A.charpoly.IsRootEnumeration α ∧
    TauCeti.IsGenericEigenvalues (algebraMap K (AlgebraicClosure K) q) α

/-- A square matrix `A` over a field `K` is **strongly generic** at `q` if its characteristic
roots in an algebraic closure of `K`, listed with multiplicity, are strongly generic at `q`
(`TauCeti.IsStronglyGenericEigenvalues`). -/
def IsStronglyGenericAt (A : Matrix n n K) (q : K) : Prop :=
  ∃ α : n → AlgebraicClosure K, A.charpoly.IsRootEnumeration α ∧
    TauCeti.IsStronglyGenericEigenvalues (algebraMap K (AlgebraicClosure K) q) α

variable {A : Matrix n n K} {q : K}

/-- A listing of the characteristic roots in a field extension `L` of `K` with one entry per row
of `A` and one in an algebraic closure of `K` list generic families together: both are sent to the
roots of the characteristic polynomial in an algebraic closure of `L`. -/
private theorem isGenericEigenvalues_iff_of_isRootEnumeration {ι L : Type*} [Fintype ι]
    [Field L] [Algebra K L] {α : ι → L} {β : n → AlgebraicClosure K}
    (hβ : A.charpoly.IsRootEnumeration β) (hα : A.charpoly.IsRootEnumeration α)
    (hcard : Fintype.card ι = Fintype.card n) :
    TauCeti.IsGenericEigenvalues (algebraMap K (AlgebraicClosure K) q) β ↔
      TauCeti.IsGenericEigenvalues (algebraMap K L q) α := by
  let Ω := AlgebraicClosure L
  let ψ : L →ₐ[K] Ω := IsScalarTower.toAlgHom K L Ω
  let φ : AlgebraicClosure K →ₐ[K] Ω := IsAlgClosed.lift
  have hβ' := hβ.map (by rw [(charpoly_monic A).natDegree_map, charpoly_natDegree_eq_dim]) φ
    φ.injective
  have hα' := hα.map (by rw [(charpoly_monic A).natDegree_map, charpoly_natDegree_eq_dim, hcard])
    ψ ψ.injective
  have hφ := TauCeti.isGenericEigenvalues_comp_iff (q := algebraMap K (AlgebraicClosure K) q)
    (α := β) (f := φ) φ.injective
  have hψ := TauCeti.isGenericEigenvalues_comp_iff (q := algebraMap K L q) (α := α) (f := ψ)
    ψ.injective
  rw [φ.commutes] at hφ
  rw [ψ.commutes] at hψ
  rw [← hφ, ← hψ]
  exact TauCeti.isGenericEigenvalues_iff_of_map_univ_val_eq
    ((isRootEnumeration_iff.1 hβ').symm.trans (isRootEnumeration_iff.1 hα'))

/-- A listing of the characteristic roots in a field extension `L` of `K` with one entry per row
of `A` and one in an algebraic closure of `K` list strongly generic families together. -/
private theorem isStronglyGenericEigenvalues_iff_of_isRootEnumeration {ι L : Type*} [Fintype ι]
    [Field L] [Algebra K L] {α : ι → L} {β : n → AlgebraicClosure K}
    (hβ : A.charpoly.IsRootEnumeration β) (hα : A.charpoly.IsRootEnumeration α)
    (hcard : Fintype.card ι = Fintype.card n) :
    TauCeti.IsStronglyGenericEigenvalues (algebraMap K (AlgebraicClosure K) q) β ↔
      TauCeti.IsStronglyGenericEigenvalues (algebraMap K L q) α := by
  have h1 := isGenericEigenvalues_iff_of_isRootEnumeration (q := 1) hβ hα hcard
  rw [_root_.map_one, _root_.map_one] at h1
  rw [TauCeti.isStronglyGenericEigenvalues_iff_and, TauCeti.isStronglyGenericEigenvalues_iff_and,
    h1, isGenericEigenvalues_iff_of_isRootEnumeration hβ hα hcard]

/-- **Genericity of a matrix is genericity of any listing of its characteristic roots**, in any
field extension `L` of `K`, provided the listing has as many entries as the size of the
matrix. -/
theorem isGenericAt_iff_of_isRootEnumeration {ι L : Type*} [Fintype ι] [Field L] [Algebra K L]
    {α : ι → L} (hα : A.charpoly.IsRootEnumeration α) (hcard : Fintype.card ι = Fintype.card n) :
    A.IsGenericAt q ↔ TauCeti.IsGenericEigenvalues (algebraMap K L q) α := by
  refine ⟨fun ⟨β, hβ, h⟩ ↦ (isGenericEigenvalues_iff_of_isRootEnumeration hβ hα hcard).1 h,
    fun h ↦ ?_⟩
  obtain ⟨β, hβ⟩ := exists_isRootEnumeration_charpoly (E := AlgebraicClosure K) A
  exact ⟨β, hβ, (isGenericEigenvalues_iff_of_isRootEnumeration hβ hα hcard).2 h⟩

/-- **Strong genericity of a matrix is strong genericity of any listing of its characteristic
roots**, in any field extension `L` of `K`, provided the listing has as many entries as the size
of the matrix. -/
theorem isStronglyGenericAt_iff_of_isRootEnumeration {ι L : Type*} [Fintype ι] [Field L]
    [Algebra K L] {α : ι → L} (hα : A.charpoly.IsRootEnumeration α)
    (hcard : Fintype.card ι = Fintype.card n) :
    A.IsStronglyGenericAt q ↔ TauCeti.IsStronglyGenericEigenvalues (algebraMap K L q) α := by
  refine ⟨fun ⟨β, hβ, h⟩ ↦ (isStronglyGenericEigenvalues_iff_of_isRootEnumeration hβ hα hcard).1 h,
    fun h ↦ ?_⟩
  obtain ⟨β, hβ⟩ := exists_isRootEnumeration_charpoly (E := AlgebraicClosure K) A
  exact ⟨β, hβ, (isStronglyGenericEigenvalues_iff_of_isRootEnumeration hβ hα hcard).2 h⟩

/-- Strong genericity of a matrix is genericity at both `1` and `q`. -/
theorem isStronglyGenericAt_iff_and :
    A.IsStronglyGenericAt q ↔ A.IsGenericAt 1 ∧ A.IsGenericAt q := by
  obtain ⟨β, hβ⟩ := exists_isRootEnumeration_charpoly (E := AlgebraicClosure K) A
  rw [isStronglyGenericAt_iff_of_isRootEnumeration hβ rfl,
    isGenericAt_iff_of_isRootEnumeration hβ rfl, isGenericAt_iff_of_isRootEnumeration hβ rfl,
    _root_.map_one, TauCeti.isStronglyGenericEigenvalues_iff_and]

/-- A strongly generic matrix is generic. -/
theorem IsStronglyGenericAt.isGenericAt (h : A.IsStronglyGenericAt q) : A.IsGenericAt q :=
  (isStronglyGenericAt_iff_and.1 h).2

/-- A matrix is generic at `1` exactly when its characteristic polynomial is separable, that is,
when its characteristic roots are pairwise distinct. -/
@[simp]
theorem isGenericAt_one_iff : A.IsGenericAt 1 ↔ A.charpoly.Separable := by
  obtain ⟨β, hβ⟩ := exists_isRootEnumeration_charpoly (E := AlgebraicClosure K) A
  rw [isGenericAt_iff_of_isRootEnumeration hβ rfl, _root_.map_one,
    TauCeti.isGenericEigenvalues_one_iff,
    hβ.injective_iff_separable (charpoly_natDegree_eq_dim A).le (charpoly_monic A).ne_zero]

/-- A strongly generic matrix has a separable characteristic polynomial: its characteristic roots
are pairwise distinct. -/
theorem IsStronglyGenericAt.separable_charpoly (h : A.IsStronglyGenericAt q) :
    A.charpoly.Separable :=
  isGenericAt_one_iff.1 (isStronglyGenericAt_iff_and.1 h).1

/-- Genericity of a matrix is genericity of the roots in any factorization of its characteristic
polynomial into linear factors over a field extension `L` of `K`. -/
theorem isGenericAt_iff_of_charpoly_map_eq_prod {L : Type*} [Field L] [Algebra K L]
    {α : n → L} (h : (A.map (algebraMap K L)).charpoly = ∏ i, (X - C (α i))) :
    A.IsGenericAt q ↔ TauCeti.IsGenericEigenvalues (algebraMap K L q) α :=
  isGenericAt_iff_of_isRootEnumeration
    (by rw [isRootEnumeration_iff, ← charpoly_map, h, roots_prod_X_sub_C_map]) rfl

/-- Strong genericity of a matrix is strong genericity of the roots in any factorization of its
characteristic polynomial into linear factors over a field extension `L` of `K`. -/
theorem isStronglyGenericAt_iff_of_charpoly_map_eq_prod {L : Type*} [Field L] [Algebra K L]
    {α : n → L} (h : (A.map (algebraMap K L)).charpoly = ∏ i, (X - C (α i))) :
    A.IsStronglyGenericAt q ↔ TauCeti.IsStronglyGenericEigenvalues (algebraMap K L q) α := by
  rw [isStronglyGenericAt_iff_and, isGenericAt_iff_of_charpoly_map_eq_prod h,
    isGenericAt_iff_of_charpoly_map_eq_prod h, _root_.map_one,
    TauCeti.isStronglyGenericEigenvalues_iff_and]

/-- A matrix of size at most one is generic at every `q`. -/
theorem isGenericAt_of_subsingleton [Subsingleton n] (A : Matrix n n K) (q : K) :
    A.IsGenericAt q := by
  obtain ⟨β, hβ⟩ := exists_isRootEnumeration_charpoly (E := AlgebraicClosure K) A
  exact ⟨β, hβ, TauCeti.isGenericEigenvalues_of_subsingleton⟩

/-- A matrix of size at most one is strongly generic at every `q`. -/
theorem isStronglyGenericAt_of_subsingleton [Subsingleton n] (A : Matrix n n K) (q : K) :
    A.IsStronglyGenericAt q := by
  obtain ⟨β, hβ⟩ := exists_isRootEnumeration_charpoly (E := AlgebraicClosure K) A
  exact ⟨β, hβ, TauCeti.isStronglyGenericEigenvalues_of_subsingleton⟩

/-- A diagonal matrix is generic exactly when its diagonal entries are. -/
@[simp]
theorem isGenericAt_diagonal_iff {α : n → K} :
    (diagonal α).IsGenericAt q ↔ TauCeti.IsGenericEigenvalues q α := by
  simpa using isGenericAt_iff_of_charpoly_map_eq_prod (L := K) (q := q)
    (by simpa using charpoly_diagonal α)

/-- A diagonal matrix is strongly generic exactly when its diagonal entries are. -/
@[simp]
theorem isStronglyGenericAt_diagonal_iff {α : n → K} :
    (diagonal α).IsStronglyGenericAt q ↔ TauCeti.IsStronglyGenericEigenvalues q α := by
  simpa using isStronglyGenericAt_iff_of_charpoly_map_eq_prod (L := K) (q := q)
    (by simpa using charpoly_diagonal α)

/-- Genericity depends only on the characteristic polynomial. -/
theorem isGenericAt_iff_of_charpoly_eq {B : Matrix m m K} (h : A.charpoly = B.charpoly) :
    A.IsGenericAt q ↔ B.IsGenericAt q := by
  obtain ⟨β, hβ⟩ := exists_isRootEnumeration_charpoly (E := AlgebraicClosure K) B
  have hβA : A.charpoly.IsRootEnumeration β := by rwa [h]
  have hcard : Fintype.card m = Fintype.card n := by
    rw [← charpoly_natDegree_eq_dim B, ← h, charpoly_natDegree_eq_dim A]
  rw [isGenericAt_iff_of_isRootEnumeration hβA hcard, isGenericAt_iff_of_isRootEnumeration hβ rfl]

/-- Strong genericity depends only on the characteristic polynomial. -/
theorem isStronglyGenericAt_iff_of_charpoly_eq {B : Matrix m m K}
    (h : A.charpoly = B.charpoly) : A.IsStronglyGenericAt q ↔ B.IsStronglyGenericAt q := by
  simp only [isStronglyGenericAt_iff_and, isGenericAt_iff_of_charpoly_eq h]

/-- Genericity is invariant under conjugation. -/
@[simp]
theorem isGenericAt_units_conj (P : (Matrix n n K)ˣ) :
    (P.val * A * P.val⁻¹).IsGenericAt q ↔ A.IsGenericAt q :=
  isGenericAt_iff_of_charpoly_eq (charpoly_units_conj P A)

/-- Strong genericity is invariant under conjugation. -/
@[simp]
theorem isStronglyGenericAt_units_conj (P : (Matrix n n K)ˣ) :
    (P.val * A * P.val⁻¹).IsStronglyGenericAt q ↔ A.IsStronglyGenericAt q :=
  isStronglyGenericAt_iff_of_charpoly_eq (charpoly_units_conj P A)

/-- **Genericity is invariant under extension of scalars.** -/
@[simp]
theorem isGenericAt_map_iff {L : Type*} [Field L] [Algebra K L] :
    (A.map (algebraMap K L)).IsGenericAt (algebraMap K L q) ↔ A.IsGenericAt q := by
  obtain ⟨β, hβ⟩ :=
    exists_isRootEnumeration_charpoly (E := AlgebraicClosure L) (A.map (algebraMap K L))
  have hβK : A.charpoly.IsRootEnumeration β := by
    rwa [charpoly_map, isRootEnumeration_map] at hβ
  rw [isGenericAt_iff_of_isRootEnumeration hβ rfl, isGenericAt_iff_of_isRootEnumeration hβK rfl,
    ← IsScalarTower.algebraMap_apply]

/-- **Strong genericity is invariant under extension of scalars.** -/
@[simp]
theorem isStronglyGenericAt_map_iff {L : Type*} [Field L] [Algebra K L] :
    (A.map (algebraMap K L)).IsStronglyGenericAt (algebraMap K L q) ↔
      A.IsStronglyGenericAt q := by
  simp only [isStronglyGenericAt_iff_and, ← _root_.map_one (algebraMap K L), isGenericAt_map_iff]

/-- **Inverting a matrix preserves genericity.** -/
theorem isGenericAt_inv_iff (hA : IsUnit A) : A⁻¹.IsGenericAt q ↔ A.IsGenericAt q := by
  let L := AlgebraicClosure K
  obtain ⟨β, hprod⟩ := exists_charpoly_map_eq_prod_X_sub_C (E := L) A
  have hAL : IsUnit (A.map (algebraMap K L)) := by
    simpa using hA.map (algebraMap K L).mapMatrix
  have hinv : (A⁻¹.map (algebraMap K L)).charpoly = ∏ i, (X - C (β i)⁻¹) := by
    rw [map_nonsing_inv (algebraMap K L) A]
    exact charpoly_inv_eq_prod_X_sub_C hAL hprod
  rw [isGenericAt_iff_of_charpoly_map_eq_prod hinv, isGenericAt_iff_of_charpoly_map_eq_prod hprod]
  exact TauCeti.isGenericEigenvalues_inv_iff

/-- **Inverting a matrix preserves strong genericity.** -/
theorem isStronglyGenericAt_inv_iff (hA : IsUnit A) :
    A⁻¹.IsStronglyGenericAt q ↔ A.IsStronglyGenericAt q := by
  simp only [isStronglyGenericAt_iff_and, isGenericAt_inv_iff hA]

end Matrix

namespace MonoidHom

variable {G n K : Type*} [Group G] [Fintype n] [DecidableEq n] [Field K]
  {ρ : G →* GL n K} {I : Subgroup G} {frob frob' : G} {q : K}

/-- A matrix representation `ρ` of `G` is **generic** at `frob` with respect to `I` and `q` if
`I` acts trivially and the eigenvalues of `ρ frob` are generic at `q`
(`Matrix.IsGenericAt`). For a representation of the absolute Galois group of a `p`-adic field,
`I` is the inertia group, `frob` a Frobenius lift and `q` the cardinality of the residue
field. -/
def IsGenericAt (ρ : G →* GL n K) (I : Subgroup G) (frob : G) (q : K) : Prop :=
  I ≤ ρ.ker ∧ (ρ frob : Matrix n n K).IsGenericAt q

/-- A matrix representation `ρ` of `G` is **strongly generic** at `frob` with respect to `I` and
`q` if `I` acts trivially and the eigenvalues of `ρ frob` are strongly generic at `q`
(`Matrix.IsStronglyGenericAt`). -/
def IsStronglyGenericAt (ρ : G →* GL n K) (I : Subgroup G) (frob : G) (q : K) : Prop :=
  I ≤ ρ.ker ∧ (ρ frob : Matrix n n K).IsStronglyGenericAt q

/-- The defining condition of `MonoidHom.IsGenericAt`. -/
theorem isGenericAt_iff :
    ρ.IsGenericAt I frob q ↔ I ≤ ρ.ker ∧ (ρ frob : Matrix n n K).IsGenericAt q :=
  Iff.rfl

/-- The defining condition of `MonoidHom.IsStronglyGenericAt`. -/
theorem isStronglyGenericAt_iff :
    ρ.IsStronglyGenericAt I frob q ↔ I ≤ ρ.ker ∧ (ρ frob : Matrix n n K).IsStronglyGenericAt q :=
  Iff.rfl

/-- A generic representation is trivial on `I`. -/
theorem IsGenericAt.le_ker (h : ρ.IsGenericAt I frob q) : I ≤ ρ.ker :=
  h.1

/-- A strongly generic representation is trivial on `I`. -/
theorem IsStronglyGenericAt.le_ker (h : ρ.IsStronglyGenericAt I frob q) : I ≤ ρ.ker :=
  h.1

/-- Strong genericity at `q` is genericity at both `1` and `q`. -/
theorem isStronglyGenericAt_iff_and :
    ρ.IsStronglyGenericAt I frob q ↔ ρ.IsGenericAt I frob 1 ∧ ρ.IsGenericAt I frob q := by
  rw [isStronglyGenericAt_iff, isGenericAt_iff, isGenericAt_iff,
    Matrix.isStronglyGenericAt_iff_and, and_and_left]

/-- A strongly generic representation is generic. -/
theorem IsStronglyGenericAt.isGenericAt (h : ρ.IsStronglyGenericAt I frob q) :
    ρ.IsGenericAt I frob q :=
  (isStronglyGenericAt_iff_and.1 h).2

/-- If a representation is strongly generic at `frob`, then the characteristic polynomial of
`ρ frob` is separable: the Frobenius eigenvalues are pairwise distinct. -/
theorem IsStronglyGenericAt.separable_charpoly (h : ρ.IsStronglyGenericAt I frob q) :
    (ρ frob : Matrix n n K).charpoly.Separable :=
  h.2.separable_charpoly

/-- **Independence of the Frobenius lift.** Genericity at `frob` and at `frob'` agree when the two
elements differ by an element of `I`. -/
theorem isGenericAt_iff_of_inv_mul_mem (h : frob⁻¹ * frob' ∈ I) :
    ρ.IsGenericAt I frob q ↔ ρ.IsGenericAt I frob' q := by
  refine and_congr_right fun hI ↦ ?_
  rw [show frob' = frob * (frob⁻¹ * frob') by group, _root_.map_mul, mem_ker.1 (hI h), mul_one]

/-- **Independence of the Frobenius lift** for strong genericity. -/
theorem isStronglyGenericAt_iff_of_inv_mul_mem (h : frob⁻¹ * frob' ∈ I) :
    ρ.IsStronglyGenericAt I frob q ↔ ρ.IsStronglyGenericAt I frob' q := by
  simp only [isStronglyGenericAt_iff_and, isGenericAt_iff_of_inv_mul_mem h]

/-- **Arithmetic and geometric Frobenius give the same condition**: genericity at `frob⁻¹` is
genericity at `frob`. -/
@[simp]
theorem isGenericAt_inv_iff : ρ.IsGenericAt I frob⁻¹ q ↔ ρ.IsGenericAt I frob q := by
  refine and_congr_right fun _ ↦ ?_
  rw [_root_.map_inv, Matrix.coe_units_inv, Matrix.isGenericAt_inv_iff (ρ frob).isUnit]

/-- Arithmetic and geometric Frobenius give the same strong genericity condition. -/
@[simp]
theorem isStronglyGenericAt_inv_iff :
    ρ.IsStronglyGenericAt I frob⁻¹ q ↔ ρ.IsStronglyGenericAt I frob q := by
  simp only [isStronglyGenericAt_iff_and, isGenericAt_inv_iff]

/-- **Genericity is invariant under extension of scalars.** -/
@[simp]
theorem isGenericAt_map_iff {L : Type*} [Field L] [Algebra K L] :
    ((Matrix.GeneralLinearGroup.map (algebraMap K L)).comp ρ).IsGenericAt I frob
      (algebraMap K L q) ↔ ρ.IsGenericAt I frob q := by
  rw [isGenericAt_iff, isGenericAt_iff,
    ker_comp_of_injective _ _ (Matrix.GeneralLinearGroup.map_injective (algebraMap K L).injective),
    comp_apply,
    Matrix.GeneralLinearGroup.val_map_apply, Matrix.isGenericAt_map_iff]

/-- **Strong genericity is invariant under extension of scalars.** -/
@[simp]
theorem isStronglyGenericAt_map_iff {L : Type*} [Field L] [Algebra K L] :
    ((Matrix.GeneralLinearGroup.map (algebraMap K L)).comp ρ).IsStronglyGenericAt I frob
      (algebraMap K L q) ↔ ρ.IsStronglyGenericAt I frob q := by
  simp only [isStronglyGenericAt_iff_and, ← _root_.map_one (algebraMap K L), isGenericAt_map_iff]

/-- **Genericity is invariant under conjugation** of the representation. -/
@[simp]
theorem isGenericAt_conj (P : GL n K) :
    ((MulAut.conj P : GL n K →* GL n K).comp ρ).IsGenericAt I frob q ↔ ρ.IsGenericAt I frob q := by
  rw [isGenericAt_iff, isGenericAt_iff, ker_comp_of_injective _ _ (MulEquiv.injective _)]
  refine and_congr_right fun _ ↦ ?_
  simp [Matrix.coe_units_inv]

/-- Strong genericity is invariant under conjugation of the representation. -/
@[simp]
theorem isStronglyGenericAt_conj (P : GL n K) :
    ((MulAut.conj P : GL n K →* GL n K).comp ρ).IsStronglyGenericAt I frob q ↔
      ρ.IsStronglyGenericAt I frob q := by
  simp only [isStronglyGenericAt_iff_and, isGenericAt_conj]

/-- When `ρ frob` is diagonal, genericity is the triviality of `I` together with genericity of
the diagonal entries. -/
theorem isGenericAt_iff_of_coe_eq_diagonal {α : n → K}
    (h : (ρ frob : Matrix n n K) = Matrix.diagonal α) :
    ρ.IsGenericAt I frob q ↔ I ≤ ρ.ker ∧ TauCeti.IsGenericEigenvalues q α := by
  rw [isGenericAt_iff, h, Matrix.isGenericAt_diagonal_iff]

/-- When `ρ frob` is diagonal, strong genericity is the triviality of `I` together with strong
genericity of the diagonal entries. -/
theorem isStronglyGenericAt_iff_of_coe_eq_diagonal {α : n → K}
    (h : (ρ frob : Matrix n n K) = Matrix.diagonal α) :
    ρ.IsStronglyGenericAt I frob q ↔ I ≤ ρ.ker ∧ TauCeti.IsStronglyGenericEigenvalues q α := by
  rw [isStronglyGenericAt_iff, h, Matrix.isStronglyGenericAt_diagonal_iff]

/-- A representation of dimension at most one is generic at every `q` exactly when `I` acts
trivially. -/
theorem isGenericAt_iff_le_ker_of_subsingleton [Subsingleton n] :
    ρ.IsGenericAt I frob q ↔ I ≤ ρ.ker :=
  and_iff_left (Matrix.isGenericAt_of_subsingleton _ q)

/-- A representation of dimension at most one is strongly generic at every `q` exactly when `I`
acts trivially. -/
theorem isStronglyGenericAt_iff_le_ker_of_subsingleton [Subsingleton n] :
    ρ.IsStronglyGenericAt I frob q ↔ I ≤ ρ.ker :=
  and_iff_left (Matrix.isStronglyGenericAt_of_subsingleton _ q)

end MonoidHom
