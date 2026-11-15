/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.LinearAlgebra.Basis.Defs
public import TauCeti.Algebra.Homology.Interleave

/-!
# Bases of interleaved complexes of modules

Let `X₁`, `X₂`, `X₃` be three `ℤ`-indexed families of free modules over a ring `R`, with ordered
bases of ranks `m₁ q`, `m₂ q` and `m₃ q`, and maps making up an interleaved chain complex
`ChainComplex.interleave`. This file assembles bases of the terms of that complex. The rank in
degree `n` is `ChainComplex.interleave.rank`, which is `m₁ q`, `m₂ q` or `m₃ q` according as
`n = 3q + 2`, `3q + 1` or `3q`, and it has finite support when the three rank functions do
(`ChainComplex.interleave.finite_setOf_rank_ne_zero`).

The main application is the based long exact homology sequence, whose Reidemeister torsion is
the correction term in Milnor's multiplicativity formula
(`TauCeti.Algebra.Homology.ReidemeisterTorsion.HomologySequence`).

## Main declarations

* `ChainComplex.interleave.rank`: the rank function of the interleaved complex.
* `ChainComplex.interleave.basis`: the basis of the interleaved complex in each degree.
* `ChainComplex.interleave.XIso₁_hom_basis` and its two companions: the basis vectors are the given
  ones under the identifications of the terms.
* `ChainComplex.interleave.boundaryEquiv₁`, `boundaryEquiv₂`, `boundaryEquiv₃`: the identifications
  of the boundaries in degrees `3q + 2`, `3q + 1` and `3q` with `range (δ q)`, `range (f q)` and
  `range (g q)`.
* `ChainComplex.interleave.boundaryBasis`, `ChainComplex.interleave.boundaryLift`,
  `ChainComplex.interleave.boundaryLift_spec`: bases of the boundaries and their lifts in each
  degree, assembled from boundary bases and lifts of `δ`, `f` and `g`.
-/

public section

noncomputable section

open CategoryTheory Module

namespace ChainComplex.interleave

section Rank

variable (m₁ m₂ m₃ : ℤ → ℕ)

/-- The rank in degree `n` of an interleaved complex whose three families have ranks
`m₁`, `m₂` and `m₃`: it is `m₃ q`, `m₂ q` or `m₁ q` according as `n = 3q`, `3q + 1` or
`3q + 2`. -/
def rank (n : ℤ) : ℕ :=
  if n % 3 = 0 then m₃ (n / 3) else if n % 3 = 1 then m₂ (n / 3) else m₁ (n / 3)

variable {m₁ m₂ m₃}

theorem rank_of_eq_three_mul_add_two {n q : ℤ} (h : n = 3 * q + 2) : rank m₁ m₂ m₃ n = m₁ q := by
  have h₁ : n % 3 = 2 := by omega
  have h₂ : n / 3 = q := by omega
  simp [rank, h₁, h₂]

theorem rank_of_eq_three_mul_add_one {n q : ℤ} (h : n = 3 * q + 1) : rank m₁ m₂ m₃ n = m₂ q := by
  have h₁ : n % 3 = 1 := by omega
  have h₂ : n / 3 = q := by omega
  simp [rank, h₁, h₂]

theorem rank_of_eq_three_mul {n q : ℤ} (h : n = 3 * q) : rank m₁ m₂ m₃ n = m₃ q := by
  have h₁ : n % 3 = 0 := by omega
  have h₂ : n / 3 = q := by omega
  simp [rank, h₁, h₂]

/-- If each of the three rank functions has finite support, so does `rank`. -/
theorem finite_setOf_rank_ne_zero (h₁ : {q | m₁ q ≠ 0}.Finite) (h₂ : {q | m₂ q ≠ 0}.Finite)
    (h₃ : {q | m₃ q ≠ 0}.Finite) : {n | rank m₁ m₂ m₃ n ≠ 0}.Finite := by
  refine (((h₁.image fun q ↦ 3 * q + 2).union (h₂.image fun q ↦ 3 * q + 1)).union
    (h₃.image fun q ↦ 3 * q)).subset fun n hn ↦ ?_
  obtain ⟨q, hq | hq | hq⟩ : ∃ q, n = 3 * q + 2 ∨ n = 3 * q + 1 ∨ n = 3 * q :=
    ⟨n / 3, by omega⟩
  · exact .inl <| .inl ⟨q, (rank_of_eq_three_mul_add_two hq).symm.trans_ne hn, hq.symm⟩
  · exact .inl <| .inr ⟨q, (rank_of_eq_three_mul_add_one hq).symm.trans_ne hn, hq.symm⟩
  · exact .inr ⟨q, (rank_of_eq_three_mul hq).symm.trans_ne hn, hq.symm⟩

end Rank

variable {R : Type*} [Ring R] {X₁ X₂ X₃ : ℤ → ModuleCat R} {f : ∀ q, X₁ q ⟶ X₂ q}
  {g : ∀ q, X₂ q ⟶ X₃ q} {δ : ∀ q, X₃ (q + 1) ⟶ X₁ q} (hfg : ∀ q, f q ≫ g q = 0)
  (hgδ : ∀ q, g (q + 1) ≫ δ q = 0) (hδf : ∀ q, δ q ≫ f q = 0)

section Basis

variable {m₁ m₂ m₃ : ℤ → ℕ} (b₁ : ∀ q, Basis (Fin (m₁ q)) R (X₁ q))
  (b₂ : ∀ q, Basis (Fin (m₂ q)) R (X₂ q)) (b₃ : ∀ q, Basis (Fin (m₃ q)) R (X₃ q))

/-- The basis of the interleaved complex in degree `n`: the basis `b₃ q`, `b₂ q` or `b₁ q`
according as `n = 3q`, `3q + 1` or `3q + 2`, transported along the identification of the term. -/
def basis (n : ℤ) :
    Basis (Fin (rank m₁ m₂ m₃ n)) R ((interleave X₁ X₂ X₃ f g δ hfg hgδ hδf).X n) :=
  if _ : n % 3 = 0 then
    ((b₃ (n / 3)).reindex (finCongr (rank_of_eq_three_mul (by omega)).symm)).map
      (XIso₃ hfg hgδ hδf n (n / 3) (by omega)).symm.toLinearEquiv
  else if _ : n % 3 = 1 then
    ((b₂ (n / 3)).reindex (finCongr (rank_of_eq_three_mul_add_one (by omega)).symm)).map
      (XIso₂ hfg hgδ hδf n (n / 3) (by omega)).symm.toLinearEquiv
  else
    ((b₁ (n / 3)).reindex (finCongr (rank_of_eq_three_mul_add_two (by omega)).symm)).map
      (XIso₁ hfg hgδ hδf n (n / 3) (by omega)).symm.toLinearEquiv

/-- In degree `n = 3q + 2` the basis of the interleaved complex is `b₁ q`. -/
@[simp]
theorem XIso₁_hom_basis {n q : ℤ} (h : n = 3 * q + 2) (i : Fin (rank m₁ m₂ m₃ n)) :
    (XIso₁ hfg hgδ hδf n q h).hom (basis hfg hgδ hδf b₁ b₂ b₃ n i) =
      b₁ q (Fin.cast (rank_of_eq_three_mul_add_two h) i) := by
  obtain rfl : n / 3 = q := by omega
  rw [basis, dite_eq_right (by omega), dite_eq_right (by omega)]
  simp

/-- In degree `n = 3q + 1` the basis of the interleaved complex is `b₂ q`. -/
@[simp]
theorem XIso₂_hom_basis {n q : ℤ} (h : n = 3 * q + 1) (i : Fin (rank m₁ m₂ m₃ n)) :
    (XIso₂ hfg hgδ hδf n q h).hom (basis hfg hgδ hδf b₁ b₂ b₃ n i) =
      b₂ q (Fin.cast (rank_of_eq_three_mul_add_one h) i) := by
  obtain rfl : n / 3 = q := by omega
  rw [basis, dite_eq_right (by omega), dite_eq_left (by omega)]
  simp

/-- In degree `n = 3q` the basis of the interleaved complex is `b₃ q`. -/
@[simp]
theorem XIso₃_hom_basis {n q : ℤ} (h : n = 3 * q) (i : Fin (rank m₁ m₂ m₃ n)) :
    (XIso₃ hfg hgδ hδf n q h).hom (basis hfg hgδ hδf b₁ b₂ b₃ n i) =
      b₃ q (Fin.cast (rank_of_eq_three_mul h) i) := by
  obtain rfl : n / 3 = q := by omega
  rw [basis, dite_eq_left (by omega)]
  simp

end Basis

section Boundaries

/-- Under `XIso₁`, the boundaries of `ChainComplex.interleave` in degree `n = 3q + 2` are the
image of `δ q`. -/
theorem map_range_d_of_eq_three_mul_add_two {n q : ℤ} (h : n = 3 * q + 2) :
    (LinearMap.range ((interleave X₁ X₂ X₃ f g δ hfg hgδ hδf).d (n + 1) n).hom).map
        ((XIso₁ hfg hgδ hδf n q h).toLinearEquiv : _ →ₗ[R] X₁ q) =
      LinearMap.range (δ q).hom := by
  have hd : ((XIso₁ hfg hgδ hδf n q h).toLinearEquiv : _ →ₗ[R] X₁ q) ∘ₗ
      ((interleave X₁ X₂ X₃ f g δ hfg hgδ hδf).d (n + 1) n).hom =
      (δ q).hom ∘ₗ
        ((XIso₃ hfg hgδ hδf (n + 1) (q + 1) (by omega)).toLinearEquiv : _ →ₗ[R] X₃ (q + 1)) := by
    ext x
    simp [interleave_d_eq_of_eq_three_mul_add_two hfg hgδ hδf h]
  rw [← LinearMap.range_comp, hd, LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range _)]

/-- Under `XIso₂`, the boundaries of `ChainComplex.interleave` in degree `n = 3q + 1` are the
image of `f q`. -/
theorem map_range_d_of_eq_three_mul_add_one {n q : ℤ} (h : n = 3 * q + 1) :
    (LinearMap.range ((interleave X₁ X₂ X₃ f g δ hfg hgδ hδf).d (n + 1) n).hom).map
        ((XIso₂ hfg hgδ hδf n q h).toLinearEquiv : _ →ₗ[R] X₂ q) =
      LinearMap.range (f q).hom := by
  have hd : ((XIso₂ hfg hgδ hδf n q h).toLinearEquiv : _ →ₗ[R] X₂ q) ∘ₗ
      ((interleave X₁ X₂ X₃ f g δ hfg hgδ hδf).d (n + 1) n).hom =
      (f q).hom ∘ₗ ((XIso₁ hfg hgδ hδf (n + 1) q (by omega)).toLinearEquiv : _ →ₗ[R] X₁ q) := by
    ext x
    simp [interleave_d_eq_of_eq_three_mul_add_one hfg hgδ hδf h]
  rw [← LinearMap.range_comp, hd, LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range _)]

/-- Under `XIso₃`, the boundaries of `ChainComplex.interleave` in degree `n = 3q` are the
image of `g q`. -/
theorem map_range_d_of_eq_three_mul {n q : ℤ} (h : n = 3 * q) :
    (LinearMap.range ((interleave X₁ X₂ X₃ f g δ hfg hgδ hδf).d (n + 1) n).hom).map
        ((XIso₃ hfg hgδ hδf n q h).toLinearEquiv : _ →ₗ[R] X₃ q) =
      LinearMap.range (g q).hom := by
  have hd : ((XIso₃ hfg hgδ hδf n q h).toLinearEquiv : _ →ₗ[R] X₃ q) ∘ₗ
      ((interleave X₁ X₂ X₃ f g δ hfg hgδ hδf).d (n + 1) n).hom =
      (g q).hom ∘ₗ ((XIso₂ hfg hgδ hδf (n + 1) q (by omega)).toLinearEquiv : _ →ₗ[R] X₂ q) := by
    ext x
    simp [interleave_d_eq_of_eq_three_mul hfg hgδ hδf h]
  rw [← LinearMap.range_comp, hd, LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range _)]

/-- The linear equivalence identifying the boundaries of `ChainComplex.interleave` in degree
`n = 3q + 2` with `LinearMap.range (δ q).hom`. -/
def boundaryEquiv₁ {n q : ℤ} (h : n = 3 * q + 2) :
    LinearMap.range ((interleave X₁ X₂ X₃ f g δ hfg hgδ hδf).d (n + 1) n).hom ≃ₗ[R]
      LinearMap.range (δ q).hom :=
  ((XIso₁ hfg hgδ hδf n q h).toLinearEquiv.submoduleMap _).trans
    (LinearEquiv.ofEq _ _ (map_range_d_of_eq_three_mul_add_two hfg hgδ hδf h))

@[simp]
theorem coe_boundaryEquiv₁ {n q : ℤ} (h : n = 3 * q + 2)
    (x : LinearMap.range ((interleave X₁ X₂ X₃ f g δ hfg hgδ hδf).d (n + 1) n).hom) :
    (boundaryEquiv₁ hfg hgδ hδf h x : X₁ q) = (XIso₁ hfg hgδ hδf n q h).hom x := by
  rfl

@[simp]
theorem XIso₁_hom_boundaryEquiv₁_symm {n q : ℤ} (h : n = 3 * q + 2)
    (y : LinearMap.range (δ q).hom) :
    (XIso₁ hfg hgδ hδf n q h).hom ((boundaryEquiv₁ hfg hgδ hδf h).symm y : _) = y := by
  simpa only [coe_boundaryEquiv₁] using
    congrArg Subtype.val ((boundaryEquiv₁ hfg hgδ hδf h).apply_symm_apply y)

/-- The linear equivalence identifying the boundaries of `ChainComplex.interleave` in degree
`n = 3q + 1` with `LinearMap.range (f q).hom`. -/
def boundaryEquiv₂ {n q : ℤ} (h : n = 3 * q + 1) :
    LinearMap.range ((interleave X₁ X₂ X₃ f g δ hfg hgδ hδf).d (n + 1) n).hom ≃ₗ[R]
      LinearMap.range (f q).hom :=
  ((XIso₂ hfg hgδ hδf n q h).toLinearEquiv.submoduleMap _).trans
    (LinearEquiv.ofEq _ _ (map_range_d_of_eq_three_mul_add_one hfg hgδ hδf h))

@[simp]
theorem coe_boundaryEquiv₂ {n q : ℤ} (h : n = 3 * q + 1)
    (x : LinearMap.range ((interleave X₁ X₂ X₃ f g δ hfg hgδ hδf).d (n + 1) n).hom) :
    (boundaryEquiv₂ hfg hgδ hδf h x : X₂ q) = (XIso₂ hfg hgδ hδf n q h).hom x := by
  rfl

@[simp]
theorem XIso₂_hom_boundaryEquiv₂_symm {n q : ℤ} (h : n = 3 * q + 1)
    (y : LinearMap.range (f q).hom) :
    (XIso₂ hfg hgδ hδf n q h).hom ((boundaryEquiv₂ hfg hgδ hδf h).symm y : _) = y := by
  simpa only [coe_boundaryEquiv₂] using
    congrArg Subtype.val ((boundaryEquiv₂ hfg hgδ hδf h).apply_symm_apply y)

/-- The linear equivalence identifying the boundaries of `ChainComplex.interleave` in degree
`n = 3q` with `LinearMap.range (g q).hom`. -/
def boundaryEquiv₃ {n q : ℤ} (h : n = 3 * q) :
    LinearMap.range ((interleave X₁ X₂ X₃ f g δ hfg hgδ hδf).d (n + 1) n).hom ≃ₗ[R]
      LinearMap.range (g q).hom :=
  ((XIso₃ hfg hgδ hδf n q h).toLinearEquiv.submoduleMap _).trans
    (LinearEquiv.ofEq _ _ (map_range_d_of_eq_three_mul hfg hgδ hδf h))

@[simp]
theorem coe_boundaryEquiv₃ {n q : ℤ} (h : n = 3 * q)
    (x : LinearMap.range ((interleave X₁ X₂ X₃ f g δ hfg hgδ hδf).d (n + 1) n).hom) :
    (boundaryEquiv₃ hfg hgδ hδf h x : X₃ q) = (XIso₃ hfg hgδ hδf n q h).hom x := by
  rfl

@[simp]
theorem XIso₃_hom_boundaryEquiv₃_symm {n q : ℤ} (h : n = 3 * q)
    (y : LinearMap.range (g q).hom) :
    (XIso₃ hfg hgδ hδf n q h).hom ((boundaryEquiv₃ hfg hgδ hδf h).symm y : _) = y := by
  simpa only [coe_boundaryEquiv₃] using
    congrArg Subtype.val ((boundaryEquiv₃ hfg hgδ hδf h).apply_symm_apply y)

variable {r₁ r₂ r₃ : ℤ → ℕ}
  (u₁ : ∀ q, Basis (Fin (r₁ q)) R (LinearMap.range (δ q).hom))
  (u₂ : ∀ q, Basis (Fin (r₂ q)) R (LinearMap.range (f q).hom))
  (u₃ : ∀ q, Basis (Fin (r₃ q)) R (LinearMap.range (g q).hom))

/-- The basis of the boundaries of `ChainComplex.interleave` in degree `n`, transported from
`u₃ q`, `u₂ q` or `u₁ q` according as `n = 3q`, `3q + 1` or `3q + 2`. -/
def boundaryBasis (n : ℤ) :
    Basis (Fin (rank r₁ r₂ r₃ n)) R
      (LinearMap.range ((interleave X₁ X₂ X₃ f g δ hfg hgδ hδf).d (n + 1) n).hom) :=
  if _ : n % 3 = 0 then
    ((u₃ (n / 3)).reindex (finCongr (rank_of_eq_three_mul (by omega)).symm)).map
      (boundaryEquiv₃ hfg hgδ hδf (by omega)).symm
  else if _ : n % 3 = 1 then
    ((u₂ (n / 3)).reindex (finCongr (rank_of_eq_three_mul_add_one (by omega)).symm)).map
      (boundaryEquiv₂ hfg hgδ hδf (by omega)).symm
  else
    ((u₁ (n / 3)).reindex (finCongr (rank_of_eq_three_mul_add_two (by omega)).symm)).map
      (boundaryEquiv₁ hfg hgδ hδf (by omega)).symm

@[simp]
theorem XIso₁_hom_boundaryBasis {n q : ℤ} (h : n = 3 * q + 2) (k : Fin (rank r₁ r₂ r₃ n)) :
    (XIso₁ hfg hgδ hδf n q h).hom (boundaryBasis hfg hgδ hδf u₁ u₂ u₃ n k) =
      u₁ q (Fin.cast (rank_of_eq_three_mul_add_two h) k) := by
  obtain rfl : n / 3 = q := by omega
  rw [boundaryBasis, dite_eq_right (by omega), dite_eq_right (by omega)]
  simp

@[simp]
theorem XIso₂_hom_boundaryBasis {n q : ℤ} (h : n = 3 * q + 1) (k : Fin (rank r₁ r₂ r₃ n)) :
    (XIso₂ hfg hgδ hδf n q h).hom (boundaryBasis hfg hgδ hδf u₁ u₂ u₃ n k) =
      u₂ q (Fin.cast (rank_of_eq_three_mul_add_one h) k) := by
  obtain rfl : n / 3 = q := by omega
  rw [boundaryBasis, dite_eq_right (by omega), dite_eq_left (by omega)]
  simp

@[simp]
theorem XIso₃_hom_boundaryBasis {n q : ℤ} (h : n = 3 * q) (k : Fin (rank r₁ r₂ r₃ n)) :
    (XIso₃ hfg hgδ hδf n q h).hom (boundaryBasis hfg hgδ hδf u₁ u₂ u₃ n k) =
      u₃ q (Fin.cast (rank_of_eq_three_mul h) k) := by
  obtain rfl : n / 3 = q := by omega
  rw [boundaryBasis, dite_eq_left (by omega)]
  simp

variable (r₁ r₂ r₃) in
/-- Lifts in degree `n + 1` of `boundaryBasis` through the differential of
`ChainComplex.interleave`, assembled from lifts `s₃ q`, `s₁ q` and `s₂ q` through `δ q`, `f q` and
`g q`. -/
def boundaryLift (s₁ : ∀ q, Fin (r₂ q) → X₁ q) (s₂ : ∀ q, Fin (r₃ q) → X₂ q)
    (s₃ : ∀ q, Fin (r₁ q) → X₃ (q + 1)) (n : ℤ) (k : Fin (rank r₁ r₂ r₃ n)) :
    (interleave X₁ X₂ X₃ f g δ hfg hgδ hδf).X (n + 1) :=
  if _ : n % 3 = 0 then
    (XIso₂ hfg hgδ hδf (n + 1) (n / 3) (by omega)).inv
      (s₂ (n / 3) (Fin.cast (rank_of_eq_three_mul (by omega)) k))
  else if _ : n % 3 = 1 then
    (XIso₁ hfg hgδ hδf (n + 1) (n / 3) (by omega)).inv
      (s₁ (n / 3) (Fin.cast (rank_of_eq_three_mul_add_one (by omega)) k))
  else
    (XIso₃ hfg hgδ hδf (n + 1) (n / 3 + 1) (by omega)).inv
      (s₃ (n / 3) (Fin.cast (rank_of_eq_three_mul_add_two (by omega)) k))

@[simp]
theorem XIso₃_hom_boundaryLift (s₁ : ∀ q, Fin (r₂ q) → X₁ q) (s₂ : ∀ q, Fin (r₃ q) → X₂ q)
    (s₃ : ∀ q, Fin (r₁ q) → X₃ (q + 1)) {n q : ℤ} (h : n + 1 = 3 * (q + 1))
    (k : Fin (rank r₁ r₂ r₃ n)) :
    (XIso₃ hfg hgδ hδf (n + 1) (q + 1) h).hom
        (boundaryLift hfg hgδ hδf r₁ r₂ r₃ s₁ s₂ s₃ n k) =
      s₃ q (Fin.cast (rank_of_eq_three_mul_add_two (by omega)) k) := by
  obtain rfl : n / 3 = q := by omega
  rw [boundaryLift, dite_eq_right (by omega), dite_eq_right (by omega)]
  simp

@[simp]
theorem XIso₁_hom_boundaryLift (s₁ : ∀ q, Fin (r₂ q) → X₁ q) (s₂ : ∀ q, Fin (r₃ q) → X₂ q)
    (s₃ : ∀ q, Fin (r₁ q) → X₃ (q + 1)) {n q : ℤ} (h : n + 1 = 3 * q + 2)
    (k : Fin (rank r₁ r₂ r₃ n)) :
    (XIso₁ hfg hgδ hδf (n + 1) q h).hom
        (boundaryLift hfg hgδ hδf r₁ r₂ r₃ s₁ s₂ s₃ n k) =
      s₁ q (Fin.cast (rank_of_eq_three_mul_add_one (by omega)) k) := by
  obtain rfl : n / 3 = q := by omega
  rw [boundaryLift, dite_eq_right (by omega), dite_eq_left (by omega)]
  simp

@[simp]
theorem XIso₂_hom_boundaryLift (s₁ : ∀ q, Fin (r₂ q) → X₁ q) (s₂ : ∀ q, Fin (r₃ q) → X₂ q)
    (s₃ : ∀ q, Fin (r₁ q) → X₃ (q + 1)) {n q : ℤ} (h : n + 1 = 3 * q + 1)
    (k : Fin (rank r₁ r₂ r₃ n)) :
    (XIso₂ hfg hgδ hδf (n + 1) q h).hom
        (boundaryLift hfg hgδ hδf r₁ r₂ r₃ s₁ s₂ s₃ n k) =
      s₂ q (Fin.cast (rank_of_eq_three_mul (by omega)) k) := by
  obtain rfl : n / 3 = q := by omega
  rw [boundaryLift, dite_eq_left (by omega)]
  simp

/-- The differential of `ChainComplex.interleave` sends `boundaryLift` to `boundaryBasis`. -/
theorem boundaryLift_spec {s₁ : ∀ q, Fin (r₂ q) → X₁ q} {s₂ : ∀ q, Fin (r₃ q) → X₂ q}
    {s₃ : ∀ q, Fin (r₁ q) → X₃ (q + 1)} (hs₁ : ∀ q k, (f q).hom (s₁ q k) = u₂ q k)
    (hs₂ : ∀ q k, (g q).hom (s₂ q k) = u₃ q k) (hs₃ : ∀ q k, (δ q).hom (s₃ q k) = u₁ q k)
    (n : ℤ) (k : Fin (rank r₁ r₂ r₃ n)) :
    ((interleave X₁ X₂ X₃ f g δ hfg hgδ hδf).d (n + 1) n).hom
        (boundaryLift hfg hgδ hδf r₁ r₂ r₃ s₁ s₂ s₃ n k) =
      boundaryBasis hfg hgδ hδf u₁ u₂ u₃ n k := by
  obtain ⟨q, hq | hq | hq⟩ : ∃ q, n = 3 * q + 2 ∨ n = 3 * q + 1 ∨ n = 3 * q := ⟨n / 3, by omega⟩
  · apply (XIso₁ hfg hgδ hδf n q hq).toLinearEquiv.injective
    simp [interleave_d_eq_of_eq_three_mul_add_two hfg hgδ hδf hq, hs₃]
  · apply (XIso₂ hfg hgδ hδf n q hq).toLinearEquiv.injective
    simp [interleave_d_eq_of_eq_three_mul_add_one hfg hgδ hδf hq, hs₁]
  · apply (XIso₃ hfg hgδ hδf n q hq).toLinearEquiv.injective
    simp [interleave_d_eq_of_eq_three_mul hfg hgδ hδf hq, hs₂]

end Boundaries

end ChainComplex.interleave
