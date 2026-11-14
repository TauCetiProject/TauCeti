/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Opposite
public import Mathlib.LinearAlgebra.Matrix.Symmetric
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Cellular algebras

A **cellular algebra**, in the sense of Graham and Lehrer, is an algebra `A` over a commutative
ring `R` together with a *cell datum*: a poset `Λ` of cells, a finite set `M μ` for each cell
`μ`, an `R`-basis `C μ s t` of `A` indexed by a cell `μ` and two elements `s t : M μ`, and an
`R`-linear anti-involution `*` of `A` with `(C μ s t)* = C μ t s`, such that for every `a : A`

`a * C μ s t ≡ ∑ u, r_a(u, s) • C μ u t` modulo `A(<μ)`,

where `A(<μ)` is the span of the basis vectors in the cells strictly below `μ` and the
coefficients `r_a(u, s)` do not depend on `t`. Temperley–Lieb, Brauer, Hecke and partition
algebras are cellular, and their representation theory (cell modules, the bilinear forms on
them, the classification of simple modules over a field and the semisimplicity criterion) is
uniform in the cell datum.

This file defines cellular bases and develops the cell-by-cell linear algebra underlying cell
modules and their forms:

* `A(<μ)` is a two-sided ideal of `A`, stable under the anti-involution;
* the coefficients `r_a(u, s)` form an algebra homomorphism `A → Matrix (M μ) (M μ) R`, the
  matrix of the action of `A` on the cell module `W(μ)`, the free `R`-module on `M μ` with basis
  vector `C μ s` acted on by `a • C μ s = ∑ u, r_a(u, s) • C μ u`; it kills `A(<μ)`;
* the **Gram matrix** `φ_μ` of the cell `μ`, determined by
  `C μ s t * C μ u v ≡ φ_μ(t, u) • C μ s v` modulo `A(<μ)`, is symmetric, and it is invariant
  in the sense that `ρ(a*)ᵀ φ_μ = φ_μ ρ(a)`, where `ρ` is the cell representation. This is the
  matrix of the bilinear form on `W(μ)` in its standard basis, and the invariance says that the
  form satisfies `φ(a* x, y) = φ(x, a y)`.

## Main definitions

* `TauCeti.CellularBasis R A M`: a cellular basis of the `R`-algebra `A` with cells
  `μ : Λ` and index sets `M μ`.
* `TauCeti.CellularBasis.lowerSpan c μ`: the span `A(<μ)` of the basis vectors in lower cells.
* `TauCeti.CellularBasis.cellRep c μ`: the cell representation of `A` on the cell `μ`.
* `TauCeti.CellularBasis.gramMatrix c μ`: the Gram matrix of the bilinear form of the cell `μ`.
* `TauCeti.CellularBasis.map`: transport a cellular basis along an `R`-algebra isomorphism.

## Main results

* `TauCeti.CellularBasis.mul_mem_lowerSpan`, `TauCeti.CellularBasis.mem_lowerSpan_mul`:
  `A(<μ)` is a two-sided ideal.
* `TauCeti.CellularBasis.mul_basis_sub_sum_mem`, `TauCeti.CellularBasis.basis_mul_sub_sum_mem`:
  the cellular axiom and its right-handed form, with coefficients given by `cellRep`.
* `TauCeti.CellularBasis.basis_mul_basis_sub_mem`: `C μ s t * C μ u v ≡ φ_μ(t, u) • C μ s v`.
* `TauCeti.CellularBasis.cellRep_basis`, `TauCeti.CellularBasis.cellRep_basis_of_ne_of_not_lt`,
  `TauCeti.CellularBasis.cellRep_basis_of_not_le`: `C μ s t` acts on the cell module by
  `C μ u ↦ φ_μ(t, u) • C μ s`, and basis vectors from cells `ν ≠ μ` with `¬ μ < ν` act by zero.
* `TauCeti.CellularBasis.isSymm_gramMatrix`: the Gram matrix is symmetric.
* `TauCeti.CellularBasis.cellRep_transpose_mul_gramMatrix`: the Gram matrix is invariant.
* `TauCeti.CellularBasis.cellRep_map`, `TauCeti.CellularBasis.gramMatrix_map`: `map` intertwines
  `cellRep` and preserves `gramMatrix`.

## Implementation notes

The anti-involution is an algebra isomorphism `A ≃ₐ[R] Aᵐᵒᵖ`, as for Mathlib's
`Matrix.transposeAlgEquiv`. That it squares to the identity is not part of the data: it follows
from its action on the basis (`TauCeti.CellularBasis.unop_antiInvolution_unop_antiInvolution`).
The coefficients `r_a(u, s)` are not part of the data either, since they are determined by the
basis: the structure only asserts that they exist, and `cellRep` reads them off from the
coordinates of `a * C μ s s`. Graham and Lehrer take `Λ` to be a finite poset; nothing here needs
finiteness or antisymmetry, so `Λ` is any preorder.

## References

* J. J. Graham and G. I. Lehrer, *Cellular algebras*, Invent. Math. 123 (1996), 1–34,
  Definition 1.1, Proposition 1.7 and Proposition 2.4.
-/

public section

open Module Submodule
open scoped Matrix

namespace TauCeti

variable {R A Λ : Type*} [CommRing R] [Ring A] [Algebra R A] [Preorder Λ]
  {M : Λ → Type*} [∀ μ, Fintype (M μ)]

variable (R A M) in
/-- A **cellular basis** of an `R`-algebra `A`, in the sense of Graham and Lehrer: a basis
`C μ s t` indexed by a cell `μ` of the poset `Λ` and by `s t : M μ`, together with an
anti-involution of `A` sending `C μ s t` to `C μ t s`, such that left multiplication by any
`a : A` acts on `C μ s t`, modulo the basis vectors of the cells strictly below `μ`, by a
combination of the `C μ u t` whose coefficients do not depend on `t`. -/
structure CellularBasis where
  /-- The cellular basis vector `C μ s t`, indexed by a cell `μ` and two elements of `M μ`. -/
  basis : Basis (Σ μ, M μ × M μ) R A
  /-- The anti-involution of `A`, as an algebra isomorphism with the opposite algebra. -/
  antiInvolution : A ≃ₐ[R] Aᵐᵒᵖ
  /-- The anti-involution transposes the cellular basis: `(C μ s t)* = C μ t s`. -/
  unop_antiInvolution_basis (μ : Λ) (s t : M μ) :
    (antiInvolution (basis ⟨μ, s, t⟩)).unop = basis ⟨μ, t, s⟩
  /-- The cellular axiom: `a * C μ s t` is `∑ u, r u • C μ u t` modulo the span of the basis
  vectors of the cells strictly below `μ`, with coefficients `r` independent of `t`. -/
  exists_mul_basis (a : A) (μ : Λ) (s : M μ) : ∃ r : M μ → R, ∀ t : M μ,
    a * basis ⟨μ, s, t⟩ - ∑ u, r u • basis ⟨μ, u, t⟩ ∈ span R (basis '' {i | i.1 < μ})

namespace CellularBasis

attribute [simp] unop_antiInvolution_basis

/-- A cellular basis is determined by its basis: the anti-involution is pinned down by its values
`C μ t s` on the basis vectors `C μ s t`. -/
@[ext]
theorem ext {c c' : CellularBasis R A M} (h : c.basis = c'.basis) : c = c' := by
  revert h
  obtain ⟨b, ι, hι, -⟩ := c
  obtain ⟨b', ι', hι', -⟩ := c'
  rintro rfl
  obtain rfl : ι = ι' := by
    have : (MulOpposite.opLinearEquiv R).symm.toLinearMap ∘ₗ ι.toLinearMap =
        (MulOpposite.opLinearEquiv R).symm.toLinearMap ∘ₗ ι'.toLinearMap :=
      b.ext fun ⟨μ, s, t⟩ => by simp [hι, hι']
    exact AlgEquiv.ext fun a => MulOpposite.unop_injective (LinearMap.congr_fun this a)
  rfl

variable (c : CellularBasis R A M)

/-- The span `A(<μ)` of the cellular basis vectors in the cells strictly below `μ`. -/
noncomputable def lowerSpan (μ : Λ) : Submodule R A :=
  span R (c.basis '' {i | i.1 < μ})

/-- `A(<μ)` is the span of the basis vectors `C ν s t` with `ν < μ`. -/
theorem lowerSpan_def (μ : Λ) : c.lowerSpan μ = span R (c.basis '' {i | i.1 < μ}) := (rfl)

/-- An element lies in `A(<μ)` exactly when its coordinates outside the cells strictly below
`μ` vanish. -/
theorem mem_lowerSpan_iff {μ : Λ} {x : A} :
    x ∈ c.lowerSpan μ ↔ ∀ i : Σ μ, M μ × M μ, ¬ i.1 < μ → c.basis.repr x i = 0 := by
  rw [lowerSpan_def, c.basis.mem_span_image]
  exact ⟨fun h i hi => by_contra fun hx => hi (h (Finsupp.mem_support_iff.2 hx)),
    fun h i hi => by_contra fun hx => Finsupp.mem_support_iff.1 hi (h i hx)⟩

/-- The basis vectors of a cell `ν < μ` lie in `A(<μ)`. -/
theorem basis_mem_lowerSpan {ν μ : Λ} (h : ν < μ) (s t : M ν) :
    c.basis ⟨ν, s, t⟩ ∈ c.lowerSpan μ :=
  subset_span ⟨_, h, rfl⟩

/-- `A(<μ)` grows with `μ`. -/
theorem lowerSpan_mono : Monotone c.lowerSpan := fun _ _ h =>
  span_mono <| Set.image_mono fun _ hi => lt_of_lt_of_le hi h

/-- Two elements congruent modulo `A(<μ)` have the same coordinates in the cell `μ`. -/
theorem repr_eq_of_sub_mem_lowerSpan {μ : Λ} {x y : A} (h : x - y ∈ c.lowerSpan μ)
    (s t : M μ) : c.basis.repr x ⟨μ, s, t⟩ = c.basis.repr y ⟨μ, s, t⟩ := by
  rw [← sub_eq_zero, ← Finsupp.sub_apply, ← map_sub]
  exact c.mem_lowerSpan_iff.1 h _ (lt_irrefl μ)

private theorem repr_sum_smul_basis (μ : Λ) [DecidableEq (M μ)] (r : M μ → R) (t u v : M μ) :
    c.basis.repr (∑ w, r w • c.basis ⟨μ, w, t⟩) ⟨μ, u, v⟩ = if v = t then r u else 0 := by
  classical
  simp [Finsupp.single_apply, ite_and, eq_comm]

private theorem repr_sum_smul_basis' (μ : Λ) [DecidableEq (M μ)] (r : M μ → R) (s u v : M μ) :
    c.basis.repr (∑ w, r w • c.basis ⟨μ, s, w⟩) ⟨μ, u, v⟩ = if u = s then r v else 0 := by
  classical
  simp [Finsupp.single_apply, ite_and, eq_comm]

/-- The cellular axiom with the coefficients read off from the coordinates of `a * C μ s s`. -/
private theorem mul_basis_sub_sum_mem' (a : A) (μ : Λ) (s t : M μ) :
    a * c.basis ⟨μ, s, t⟩ -
        ∑ u, c.basis.repr (a * c.basis ⟨μ, s, s⟩) ⟨μ, u, s⟩ • c.basis ⟨μ, u, t⟩ ∈
      c.lowerSpan μ := by
  classical
  obtain ⟨r, hr⟩ := c.exists_mul_basis a μ s
  have key (t u : M μ) : c.basis.repr (a * c.basis ⟨μ, s, t⟩) ⟨μ, u, t⟩ = r u := by
    rw [c.repr_eq_of_sub_mem_lowerSpan (hr t), repr_sum_smul_basis]
    simp
  simp only [key]
  exact hr t

/-- `A(<μ)` is a left ideal. -/
theorem mul_mem_lowerSpan (a : A) {μ : Λ} {x : A} (hx : x ∈ c.lowerSpan μ) :
    a * x ∈ c.lowerSpan μ := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨⟨ν, s, t⟩, hν : ν < μ, rfl⟩ := hy
    have h := add_mem (c.lowerSpan_mono hν.le (c.mul_basis_sub_sum_mem' a ν s t))
      (sum_mem (t := Finset.univ) fun u _ =>
        smul_mem _ (c.basis.repr (a * c.basis ⟨ν, s, s⟩) ⟨ν, u, s⟩) (c.basis_mem_lowerSpan hν u t))
    rwa [sub_add_cancel] at h
  | zero => simp
  | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
  | smul r x _ hx => rw [mul_smul_comm]; exact smul_mem _ r hx

/-- The anti-involution of a cellular basis squares to the identity. -/
@[simp]
theorem unop_antiInvolution_unop_antiInvolution (a : A) :
    (c.antiInvolution (c.antiInvolution a).unop).unop = a := by
  let f : A →ₗ[R] A :=
    (MulOpposite.opLinearEquiv R).symm.toLinearMap ∘ₗ c.antiInvolution.toLinearMap
  have : f ∘ₗ f = LinearMap.id := c.basis.ext fun ⟨μ, s, t⟩ => by simp [f]
  exact LinearMap.congr_fun this a

/-- The anti-involution preserves `A(<μ)`. -/
theorem unop_antiInvolution_mem_lowerSpan {μ : Λ} {x : A} (hx : x ∈ c.lowerSpan μ) :
    (c.antiInvolution x).unop ∈ c.lowerSpan μ := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨⟨ν, s, t⟩, hν, rfl⟩ := hy
    simpa using c.basis_mem_lowerSpan hν t s
  | zero => simp
  | add x y _ _ hx hy => simpa using add_mem hx hy
  | smul r x _ hx => simpa using smul_mem _ r hx

/-- `A(<μ)` is a right ideal. -/
theorem mem_lowerSpan_mul (a : A) {μ : Λ} {x : A} (hx : x ∈ c.lowerSpan μ) :
    x * a ∈ c.lowerSpan μ := by
  simpa using c.unop_antiInvolution_mem_lowerSpan
    (c.mul_mem_lowerSpan (c.antiInvolution a).unop (c.unop_antiInvolution_mem_lowerSpan hx))

section Map

variable {B C : Type*} [Ring B] [Algebra R B] [Ring C] [Algebra R C]

private theorem span_basis_map_image_lt (e : A ≃ₐ[R] B) (μ : Λ) :
    span R (c.basis.map e.toLinearEquiv '' {i | i.1 < μ}) =
      (c.lowerSpan μ).map e.toLinearMap := by
  rw [lowerSpan_def, Submodule.map_span, ← Set.image_comp]
  exact congrArg (span R) (congrArg (· '' _)
    (funext fun i ↦ c.basis.map_apply e.toLinearEquiv i))

/-- Transport a cellular basis along an `R`-algebra equivalence `e : A ≃ₐ[R] B`. -/
noncomputable def map (e : A ≃ₐ[R] B) : CellularBasis R B M where
  basis := c.basis.map e.toLinearEquiv
  antiInvolution := e.symm.trans (c.antiInvolution.trans (AlgEquiv.op e))
  unop_antiInvolution_basis μ s t := by simp
  exists_mul_basis b μ s := by
    obtain ⟨r, hr⟩ := c.exists_mul_basis (e.symm b) μ s
    refine ⟨r, fun t ↦ ?_⟩
    rw [c.span_basis_map_image_lt e μ]
    have hmem : e.symm b * c.basis ⟨μ, s, t⟩ - ∑ u, r u • c.basis ⟨μ, u, t⟩ ∈ c.lowerSpan μ := by
      rw [lowerSpan_def]
      exact hr t
    refine ⟨e.symm b * c.basis ⟨μ, s, t⟩ - ∑ u, r u • c.basis ⟨μ, u, t⟩, hmem, ?_⟩
    simp [map_sub, map_mul, map_sum, map_smul]

/-- The cellular basis transported along `e` applies `e` to each basis vector. -/
@[simp]
theorem map_basis (e : A ≃ₐ[R] B) (i : Σ μ, M μ × M μ) :
    (c.map e).basis i = e (c.basis i) :=
  c.basis.map_apply e.toLinearEquiv i

/-- Coordinates in the transported cellular basis pull back along `e.symm`. -/
@[simp]
theorem map_basis_repr (e : A ≃ₐ[R] B) (b : B) :
    (c.map e).basis.repr b = c.basis.repr (e.symm b) := by
  simp [map]

/-- Transporting along the identity algebra equivalence does nothing. -/
@[simp]
theorem map_refl : c.map (AlgEquiv.refl : A ≃ₐ[R] A) = c := by
  ext i
  simp

/-- Transporting along `e` and then `e'` is transporting along `e.trans e'`. -/
@[simp]
theorem map_trans (e : A ≃ₐ[R] B) (e' : B ≃ₐ[R] C) :
    (c.map e).map e' = c.map (e.trans e') := by
  ext i
  simp

/-- The anti-involution of `c.map e` conjugates `c.antiInvolution` by `e`. -/
@[simp]
theorem unop_antiInvolution_map (e : A ≃ₐ[R] B) (b : B) :
    ((c.map e).antiInvolution b).unop = e (c.antiInvolution (e.symm b)).unop :=
  (rfl)

/-- Lower cell spans push forward under `e`. -/
theorem lowerSpan_map (e : A ≃ₐ[R] B) (μ : Λ) :
    (c.map e).lowerSpan μ = (c.lowerSpan μ).map e.toLinearMap := by
  rw [lowerSpan_def, map, c.span_basis_map_image_lt]

/-- Membership in `(c.map e).lowerSpan μ` pulls back via `e.symm`. -/
@[simp]
theorem mem_lowerSpan_map_iff (e : A ≃ₐ[R] B) {μ : Λ} {b : B} :
    b ∈ (c.map e).lowerSpan μ ↔ e.symm b ∈ c.lowerSpan μ := by
  rw [mem_lowerSpan_iff, mem_lowerSpan_iff]
  simp

end Map

variable [∀ μ, DecidableEq (M μ)]

private theorem repr_mul_basis' (a : A) (μ : Λ) (s t u v : M μ) :
    c.basis.repr (a * c.basis ⟨μ, s, t⟩) ⟨μ, u, v⟩ =
      if v = t then c.basis.repr (a * c.basis ⟨μ, s, s⟩) ⟨μ, u, s⟩ else 0 := by
  rw [c.repr_eq_of_sub_mem_lowerSpan (c.mul_basis_sub_sum_mem' a μ s t), repr_sum_smul_basis]

/-- The **cell representation** of `A` on the cell `μ`: the matrix of the action of `a : A` on
the cell module `W(μ)`, the free `R`-module on `M μ`, in its standard basis. Its entry `(u, s)` is
the coefficient `r_a(u, s)` of `C μ u t` in `a * C μ s t` modulo `A(<μ)`, for any `t`. -/
noncomputable def cellRep (μ : Λ) : A →ₐ[R] Matrix (M μ) (M μ) R where
  toFun a := Matrix.of fun u s => c.basis.repr (a * c.basis ⟨μ, s, s⟩) ⟨μ, u, s⟩
  map_one' := by
    classical
    ext u s
    simp [Matrix.one_apply, Finsupp.single_apply, eq_comm]
  map_mul' a b := by
    ext w s
    have h := c.mul_mem_lowerSpan a (c.mul_basis_sub_sum_mem' b μ s s)
    rw [mul_sub, ← mul_assoc] at h
    have key (u : M μ) : c.basis.repr (a * c.basis ⟨μ, u, s⟩) ⟨μ, w, s⟩ =
        c.basis.repr (a * c.basis ⟨μ, u, u⟩) ⟨μ, w, u⟩ := by
      simp [repr_mul_basis' _ a μ u s]
    simp [c.repr_eq_of_sub_mem_lowerSpan h, Finset.mul_sum, key, mul_comm, Matrix.mul_apply]
  map_zero' := by ext; simp
  map_add' a b := by ext; simp [add_mul]
  commutes' r := by
    classical
    ext u s
    simp [Algebra.algebraMap_eq_smul_one, Matrix.algebraMap_matrix_apply, Finsupp.single_apply,
      eq_comm]

/-- The entries of the cell representation are coordinates of `a * C μ s s`. Use
`TauCeti.CellularBasis.repr_mul_basis` for the coordinates of `a * C μ s t` for every `t`. -/
theorem cellRep_apply (μ : Λ) (a : A) (u s : M μ) :
    c.cellRep μ a u s = c.basis.repr (a * c.basis ⟨μ, s, s⟩) ⟨μ, u, s⟩ := (rfl)

/-- The coordinates of `a * C μ s t` in the cell `μ` are given by the cell representation: the
coefficient of `C μ u v` is `cellRep μ a u s` if `v = t`, and zero otherwise. -/
@[simp]
theorem repr_mul_basis (a : A) (μ : Λ) (s t u v : M μ) :
    c.basis.repr (a * c.basis ⟨μ, s, t⟩) ⟨μ, u, v⟩ = if v = t then c.cellRep μ a u s else 0 :=
  c.repr_mul_basis' a μ s t u v

/-- The cellular axiom: modulo `A(<μ)`, `a * C μ s t = ∑ u, cellRep μ a u s • C μ u t`. -/
theorem mul_basis_sub_sum_mem (a : A) (μ : Λ) (s t : M μ) :
    a * c.basis ⟨μ, s, t⟩ - ∑ u, c.cellRep μ a u s • c.basis ⟨μ, u, t⟩ ∈ c.lowerSpan μ :=
  c.mul_basis_sub_sum_mem' a μ s t

/-- The right-handed cellular axiom: modulo `A(<μ)`,
`C μ s t * a = ∑ v, cellRep μ a* v t • C μ s v`, where `a*` is the anti-involution of `a`. -/
theorem basis_mul_sub_sum_mem (a : A) (μ : Λ) (s t : M μ) :
    c.basis ⟨μ, s, t⟩ * a -
        ∑ v, c.cellRep μ (c.antiInvolution a).unop v t • c.basis ⟨μ, s, v⟩ ∈ c.lowerSpan μ := by
  simpa using c.unop_antiInvolution_mem_lowerSpan
    (c.mul_basis_sub_sum_mem (c.antiInvolution a).unop μ t s)

/-- The cell representation of the cell `μ` kills `A(<μ)`. -/
theorem cellRep_eq_zero_of_mem_lowerSpan {μ : Λ} {x : A} (hx : x ∈ c.lowerSpan μ) :
    c.cellRep μ x = 0 := by
  ext u s
  exact c.mem_lowerSpan_iff.1 (c.mem_lowerSpan_mul _ hx) _ (lt_irrefl μ)

/-- Elements congruent modulo `A(<μ)` have the same cell representation on `μ`. -/
theorem cellRep_eq_of_sub_mem_lowerSpan {μ : Λ} {x y : A} (h : x - y ∈ c.lowerSpan μ) :
    c.cellRep μ x = c.cellRep μ y := by
  rw [← sub_eq_zero, ← map_sub, c.cellRep_eq_zero_of_mem_lowerSpan h]

/-- The **Gram matrix** `φ_μ` of the cell `μ`, the matrix of the bilinear form of the cell module
`W(μ)` in its standard basis. It is characterized by `C μ s t * C μ u v ≡ φ_μ(t, u) • C μ s v`
modulo `A(<μ)` (`TauCeti.CellularBasis.basis_mul_basis_sub_mem`); here it is read off at
`s = t` and `v = u`. -/
noncomputable def gramMatrix (μ : Λ) : Matrix (M μ) (M μ) R :=
  Matrix.of fun t u => c.cellRep μ (c.basis ⟨μ, t, t⟩) t u

private theorem cellRep_basis' (μ : Λ) (s t u v w : M μ) :
    c.cellRep μ (c.basis ⟨μ, s, t⟩) w u =
      if w = s then c.cellRep μ (c.basis ⟨μ, v, u⟩) v t else 0 := by
  have h := c.repr_eq_of_sub_mem_lowerSpan
    (c.basis_mul_sub_sum_mem (c.basis ⟨μ, u, v⟩) μ s t) w v
  rw [repr_mul_basis, repr_sum_smul_basis'] at h
  simpa using h

/-- The basis vector `C μ s t` acts on the cell module `W(μ)` by `C μ u ↦ φ_μ(t, u) • C μ s`. -/
@[simp]
theorem cellRep_basis (μ : Λ) (s t u w : M μ) :
    c.cellRep μ (c.basis ⟨μ, s, t⟩) w u = if w = s then c.gramMatrix μ t u else 0 := by
  rw [c.cellRep_basis' μ s t u u, gramMatrix, Matrix.of_apply, c.cellRep_basis' μ t t u u]
  simp

/-- The defining property of the Gram matrix: modulo `A(<μ)`,
`C μ s t * C μ u v = φ_μ(t, u) • C μ s v`. -/
theorem basis_mul_basis_sub_mem (μ : Λ) (s t u v : M μ) :
    c.basis ⟨μ, s, t⟩ * c.basis ⟨μ, u, v⟩ - c.gramMatrix μ t u • c.basis ⟨μ, s, v⟩ ∈
      c.lowerSpan μ := by
  simpa [cellRep_basis, ite_smul] using c.mul_basis_sub_sum_mem (c.basis ⟨μ, s, t⟩) μ u v

/-- The Gram matrix is symmetric. -/
theorem isSymm_gramMatrix (μ : Λ) : (c.gramMatrix μ).IsSymm := by
  ext t u
  have h := c.unop_antiInvolution_mem_lowerSpan (c.basis_mul_basis_sub_mem μ u u t t)
  simp only [map_sub, MulOpposite.unop_sub, map_mul, MulOpposite.unop_mul, map_smul,
    MulOpposite.unop_smul, unop_antiInvolution_basis] at h
  have h₁ := c.repr_eq_of_sub_mem_lowerSpan h t u
  simp only [map_smul, Basis.repr_self, Finsupp.smul_single, Finsupp.single_eq_same, smul_eq_mul,
    mul_one] at h₁
  rw [Matrix.transpose_apply, ← h₁]
  simp

/-- The Gram matrix is invariant under the cell representation: `ρ(a*)ᵀ φ_μ = φ_μ ρ(a)`, where
`ρ` is the cell representation and `a*` the anti-involution of `a`. Equivalently, the bilinear
form of the cell module satisfies `φ(a* x, y) = φ(x, a y)`. -/
theorem cellRep_transpose_mul_gramMatrix (a : A) (μ : Λ) :
    (c.cellRep μ (c.antiInvolution a).unop)ᵀ * c.gramMatrix μ = c.gramMatrix μ * c.cellRep μ a := by
  ext t u
  have h := congrFun (congrFun
    (c.cellRep_eq_of_sub_mem_lowerSpan (c.basis_mul_sub_sum_mem a μ t t)) t) u
  simpa [Matrix.mul_apply, Matrix.sum_apply, cellRep_basis, mul_comm] using h.symm

/-- A cellular basis vector from a cell `ν` with `μ ≠ ν` and `¬ μ < ν` acts by zero in the cell
representation at `μ`. -/
theorem cellRep_basis_of_ne_of_not_lt {μ ν : Λ} (hne : μ ≠ ν) (hnlt : ¬ μ < ν) (x y : M ν) :
    c.cellRep μ (c.basis ⟨ν, x, y⟩) = 0 := by
  have hsum (r : M ν → R) (u s : M μ) :
      c.basis.repr (∑ v, r v • c.basis ⟨ν, x, v⟩) ⟨μ, u, s⟩ = 0 := by
    simp [hne.symm]
  ext u s
  rw [Matrix.zero_apply, cellRep_apply]
  have hsub := c.basis_mul_sub_sum_mem (c.basis ⟨μ, s, s⟩) ν x y
  have hzero := c.mem_lowerSpan_iff.1 hsub ⟨μ, u, s⟩ hnlt
  rw [map_sub, Finsupp.sub_apply, sub_eq_zero] at hzero
  exact hzero.trans (hsum _ u s)

/-- A cellular basis vector from a cell `ν` with `¬ μ ≤ ν` acts by zero in the cell representation
at `μ`. -/
theorem cellRep_basis_of_not_le {μ ν : Λ} (h : ¬ μ ≤ ν) (x y : M ν) :
    c.cellRep μ (c.basis ⟨ν, x, y⟩) = 0 :=
  c.cellRep_basis_of_ne_of_not_lt (fun hEq ↦ h hEq.le) (fun hlt ↦ h hlt.le) x y

section MapDecidable

variable {B : Type*} [Ring B] [Algebra R B]

/-- The cell representation of `c.map e` pulls back `c.cellRep` along `e.symm`. -/
@[simp]
theorem cellRep_map (e : A ≃ₐ[R] B) (μ : Λ) (b : B) :
    (c.map e).cellRep μ b = c.cellRep μ (e.symm b) := by
  ext u s
  rw [cellRep_apply, cellRep_apply, map_basis_repr, map_basis, map_mul, e.symm_apply_apply]

/-- Transporting a cellular basis along an algebra isomorphism preserves every Gram matrix. -/
@[simp]
theorem gramMatrix_map (e : A ≃ₐ[R] B) (μ : Λ) :
    (c.map e).gramMatrix μ = c.gramMatrix μ := by
  ext t u
  have h₁ := (c.map e).cellRep_basis μ t t u t
  have h₂ := c.cellRep_basis μ t t u t
  simp only [↓reduceIte, cellRep_map, map_basis, AlgEquiv.symm_apply_apply] at h₁ h₂
  exact h₁.symm.trans h₂

end MapDecidable

end CellularBasis

end TauCeti
