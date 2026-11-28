/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.NumberTheory.Padics.Complex
import TauCeti.Analysis.InnerProductSpace.Projection.Completeness

/-!
# Coordinate integrality and projection denominators

A complex basis `b : Module.Basis ι ℂ E` determines an integral model of a complex vector space
`E`. For any ring homomorphism `place : ℂ →+* K` into a normed field `K`, a vector is
coordinate-integral at `place` (`TauCeti.ThetaLift.IsCoordinateIntegralAt`) when every coordinate
has norm at most one. When `K` is ultrametric, the coordinate-integral vectors form an additive
subgroup `TauCeti.ThetaLift.coordinateIntegralLattice`. A vector is globally coordinate-integral at
a prime `p` (`TauCeti.ThetaLift.IsCoordinateIntegralEverywhere`) if it is coordinate-integral at
every complex embedding `ℂ →+* ℂ_[p]`.

For a finite-dimensional subspace `Z` of a complex inner product space `E`, an ultrametric place
`place : ℂ →+* K`, a rank factor `r`, an admissible subspace `admissible`, and a real budget `β`,
the predicate `TauCeti.ThetaLift.DenominatorLe` asserts the existence of an endomorphism `Λ` of `Z`
whose determinant at `place` satisfies `exp(-(finrank ℂ Z * r) * β) ≤ ‖place (det Λ)‖` and which
maps the orthogonal projection `Z.orthogonalProjectionOnto y` of every locally integral vector
`y ∈ admissible` into the local coordinate lattice with integral pairings against every globally
coordinate-integral vector.

## Main declarations

* `TauCeti.ThetaLift.IsCoordinateIntegralAt`: coordinate norm bound at a complex place.
* `TauCeti.ThetaLift.coordinateIntegralLattice`: the local coordinate lattice as an `AddSubgroup`.
* `TauCeti.ThetaLift.IsCoordinateIntegralEverywhere`: global coordinate integrality at a prime `p`.
* `TauCeti.ThetaLift.DenominatorLe`: determinant-controlled denominator bound for orthogonal
  projection onto a finite-dimensional subspace.
* `TauCeti.ThetaLift.denominatorLe_bot`, `TauCeti.ThetaLift.denominatorLe_top_zero`,
  `TauCeti.ThetaLift.DenominatorLe.mono_beta`, `TauCeti.ThetaLift.DenominatorLe.mono_rank`,
  `TauCeti.ThetaLift.DenominatorLe.restrict_admissible`,
  `TauCeti.ThetaLift.DenominatorLe.sup_of_orthogonal`: structural API for `DenominatorLe`,
  including closure under orthogonal direct sums.

## References

* L. Sernau, `lsernau/grh-lean` at commit `72fead1`, `New/OneLift/TestedForms.lean`
  (`New.Selmer.DenominatorLe`).
-/

public section

open scoped InnerProductSpace

open Module

namespace TauCeti.ThetaLift

universe u v w

section CoordinateIntegrality

variable {ι : Type u} {E : Type v} [AddCommGroup E] [Module ℂ E]

/-- A vector is coordinate-integral under a ring homomorphism into a normed field if all its
coordinates in the given complex basis have norm at most one. -/
def IsCoordinateIntegralAt {K : Type w} [NormedField K] (place : ℂ →+* K)
    (b : Basis ι ℂ E) (x : E) : Prop :=
  ∀ j, ‖place (b.repr x j)‖ ≤ 1

/-- A vector is coordinate-integral exactly when each coordinate has norm at most one at
`place`. -/
theorem isCoordinateIntegralAt_def {K : Type w} [NormedField K] {place : ℂ →+* K}
    {b : Basis ι ℂ E} {x : E} :
    IsCoordinateIntegralAt place b x ↔ ∀ j, ‖place (b.repr x j)‖ ≤ 1 := Iff.rfl

/-- The coordinate lattice at an ultrametric place, as an additive subgroup of the ambient space. -/
def coordinateIntegralLattice {K : Type w} [NormedField K] [IsUltrametricDist K]
    (place : ℂ →+* K) (b : Basis ι ℂ E) : AddSubgroup E :=
  ⨅ j, (IsUltrametricDist.closedBall_openAddSubgroup K one_pos).toAddSubgroup.comap
    { toFun := fun x ↦ place (b.repr x j)
      map_zero' := by simp
      map_add' := fun x y ↦ by simp }

/-- Membership in `coordinateIntegralLattice` is coordinate integrality at `place`. -/
@[simp]
theorem mem_coordinateIntegralLattice {K : Type w} [NormedField K] [IsUltrametricDist K]
    {place : ℂ →+* K} {b : Basis ι ℂ E} {x : E} :
    x ∈ coordinateIntegralLattice place b ↔ IsCoordinateIntegralAt place b x := by
  simp [coordinateIntegralLattice, IsCoordinateIntegralAt,
    IsUltrametricDist.closedBall_openAddSubgroup]

/-- Global coordinate integrality at a prime `p` means coordinate integrality under every complex
embedding into `ℂ_[p]`. -/
def IsCoordinateIntegralEverywhere (p : ℕ) [Fact p.Prime] (b : Basis ι ℂ E) (x : E) : Prop :=
  ∀ place : ℂ →+* ℂ_[p], IsCoordinateIntegralAt place b x

/-- Global coordinate integrality is equivalent to integrality at every place over `p`. -/
theorem isCoordinateIntegralEverywhere_def {p : ℕ} [Fact p.Prime] {b : Basis ι ℂ E} {x : E} :
    IsCoordinateIntegralEverywhere p b x ↔
      ∀ place : ℂ →+* ℂ_[p], IsCoordinateIntegralAt place b x := Iff.rfl

/-- Every basis vector is coordinate-integral at every place. -/
theorem isCoordinateIntegralEverywhere_basis (p : ℕ) [Fact p.Prime] (b : Basis ι ℂ E) (i : ι) :
    IsCoordinateIntegralEverywhere p b (b i) := by
  classical
  intro place j
  simp only [Basis.repr_self, Finsupp.single_apply]
  split <;> simp

end CoordinateIntegrality

section Denominator

variable {ι : Type u} {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The projection to `Z` has denominator at most `β` at `place` if some endomorphism `Λ` of `Z`
has determinant norm at least `exp(-(finrank ℂ Z * r) * β)` and clears the projection denominators
on `admissible`, with integral pairings against every globally integral vector. -/
def DenominatorLe (p : ℕ) [Fact p.Prime] {K : Type w} [NormedField K] [IsUltrametricDist K]
    (place : ℂ →+* K) (b : Basis ι ℂ E) (Z : Submodule ℂ E) [FiniteDimensional ℂ Z]
    (admissible : Submodule ℂ E) (r : ℕ) (β : ℝ) : Prop :=
  ∃ Λ : Module.End ℂ Z,
    Real.exp (-((Module.finrank ℂ Z * r : ℕ) : ℝ) * β) ≤ ‖place (LinearMap.det Λ)‖ ∧
    ∀ y ∈ coordinateIntegralLattice place b, y ∈ admissible →
      ((Λ (Z.orthogonalProjectionOnto y) : Z) : E) ∈ coordinateIntegralLattice place b ∧
      ∀ y', IsCoordinateIntegralEverywhere p b y' →
        ‖place ⟪y', ((Λ (Z.orthogonalProjectionOnto y) : Z) : E)⟫_ℂ‖ ≤ 1

/-- A denominator bound is equivalent to the existence of a denominator-clearing endomorphism
with the required determinant bound and integral pairings on `admissible`. -/
theorem denominatorLe_def {p : ℕ} [Fact p.Prime] {K : Type w} [NormedField K] [IsUltrametricDist K]
    {place : ℂ →+* K} {b : Basis ι ℂ E} {Z : Submodule ℂ E} [FiniteDimensional ℂ Z]
    {admissible : Submodule ℂ E} {r : ℕ} {β : ℝ} :
    DenominatorLe p place b Z admissible r β ↔
      ∃ Λ : Module.End ℂ Z,
        Real.exp (-((Module.finrank ℂ Z * r : ℕ) : ℝ) * β) ≤ ‖place (LinearMap.det Λ)‖ ∧
        ∀ y ∈ coordinateIntegralLattice place b, y ∈ admissible →
          ((Λ (Z.orthogonalProjectionOnto y) : Z) : E) ∈ coordinateIntegralLattice place b ∧
          ∀ y', IsCoordinateIntegralEverywhere p b y' →
            ‖place ⟪y', ((Λ (Z.orthogonalProjectionOnto y) : Z) : E)⟫_ℂ‖ ≤ 1 := Iff.rfl

/-- The projection to the zero subspace has every denominator bound, witnessed by the zero
endomorphism, whose determinant is one on the zero space. -/
theorem denominatorLe_bot (p : ℕ) [Fact p.Prime] {K : Type w} [NormedField K] [IsUltrametricDist K]
    (place : ℂ →+* K) (b : Basis ι ℂ E) (admissible : Submodule ℂ E) (r : ℕ) (β : ℝ) :
    DenominatorLe p place b ⊥ admissible r β := by
  refine ⟨0, ?_, ?_⟩
  · simp
  · intro y _ _
    simp

/-- If every globally integral vector pairs integrally with the locally integral vectors in
`admissible`, then the projection to the whole space has denominator zero, witnessed by
`LinearMap.id`. -/
theorem denominatorLe_top_zero (p : ℕ) [Fact p.Prime] {K : Type w} [NormedField K]
    [IsUltrametricDist K] (place : ℂ →+* K) (b : Basis ι ℂ E) [FiniteDimensional ℂ E]
    (admissible : Submodule ℂ E) (r : ℕ)
    (hpair : ∀ y', IsCoordinateIntegralEverywhere p b y' →
      ∀ y ∈ coordinateIntegralLattice place b, y ∈ admissible → ‖place ⟪y', y⟫_ℂ‖ ≤ 1) :
    DenominatorLe p place b ⊤ admissible r 0 := by
  refine ⟨LinearMap.id, by simp, ?_⟩
  intro y hy hadm
  simpa [Submodule.starProjection_top] using And.intro hy (fun y' hy' ↦ hpair y' hy' y hy hadm)

/-- Increasing the real denominator budget preserves `DenominatorLe`. -/
theorem DenominatorLe.mono_beta {p : ℕ} [Fact p.Prime] {K : Type w} [NormedField K]
    [IsUltrametricDist K] {place : ℂ →+* K} {b : Basis ι ℂ E} {Z : Submodule ℂ E}
    [FiniteDimensional ℂ Z] {admissible : Submodule ℂ E} {r : ℕ} {β₁ β₂ : ℝ}
    (hβ : β₁ ≤ β₂) (h : DenominatorLe p place b Z admissible r β₁) :
    DenominatorLe p place b Z admissible r β₂ := by
  obtain ⟨Λ, hdet, hΛ⟩ := h
  refine ⟨Λ, ?_, hΛ⟩
  apply (Real.exp_le_exp.mpr ?_).trans hdet
  nlinarith [mul_le_mul_of_nonneg_left hβ (Nat.cast_nonneg (α := ℝ) (Module.finrank ℂ Z * r))]

/-- For a nonnegative denominator budget, increasing the rank factor preserves `DenominatorLe`. -/
theorem DenominatorLe.mono_rank {p : ℕ} [Fact p.Prime] {K : Type w} [NormedField K]
    [IsUltrametricDist K] {place : ℂ →+* K} {b : Basis ι ℂ E} {Z : Submodule ℂ E}
    [FiniteDimensional ℂ Z] {admissible : Submodule ℂ E} {r₁ r₂ : ℕ} {β : ℝ}
    (hr : r₁ ≤ r₂) (hβ : 0 ≤ β) (h : DenominatorLe p place b Z admissible r₁ β) :
    DenominatorLe p place b Z admissible r₂ β := by
  obtain ⟨Λ, hdet, hΛ⟩ := h
  refine ⟨Λ, ?_, hΛ⟩
  apply (Real.exp_le_exp.mpr ?_).trans hdet
  have hr' : ((Module.finrank ℂ Z * r₁ : ℕ) : ℝ) ≤
      ((Module.finrank ℂ Z * r₂ : ℕ) : ℝ) := by
    exact_mod_cast Nat.mul_le_mul_left (Module.finrank ℂ Z) hr
  nlinarith [mul_le_mul_of_nonneg_left hr' hβ]

/-- Restricting to a smaller admissible subspace preserves `DenominatorLe`. -/
theorem DenominatorLe.restrict_admissible {p : ℕ} [Fact p.Prime] {K : Type w} [NormedField K]
    [IsUltrametricDist K] {place : ℂ →+* K} {b : Basis ι ℂ E} {Z : Submodule ℂ E}
    [FiniteDimensional ℂ Z] {U W : Submodule ℂ E} {r : ℕ} {β : ℝ} (hUW : U ≤ W)
    (h : DenominatorLe p place b Z W r β) : DenominatorLe p place b Z U r β := by
  obtain ⟨Λ, hdet, hΛ⟩ := h
  exact ⟨Λ, hdet, fun y hy hyU ↦ hΛ y hy (hUW hyU)⟩

/-- Denominator bounds are closed under orthogonal direct sums: if `Z₁` and `Z₂` are orthogonal
finite-dimensional subspaces satisfying `DenominatorLe` with the same budget `β`, then `Z₁ ⊔ Z₂`
also satisfies `DenominatorLe` with budget `β`. -/
theorem DenominatorLe.sup_of_orthogonal {p : ℕ} [Fact p.Prime] {K : Type w} [NormedField K]
    [IsUltrametricDist K] {place : ℂ →+* K} {b : Basis ι ℂ E} {Z₁ Z₂ : Submodule ℂ E}
    [FiniteDimensional ℂ Z₁] [FiniteDimensional ℂ Z₂] {admissible : Submodule ℂ E}
    {r : ℕ} {β : ℝ} (hZ : Z₁ ≤ Z₂ᗮ)
    (h₁ : DenominatorLe p place b Z₁ admissible r β)
    (h₂ : DenominatorLe p place b Z₂ admissible r β) :
    DenominatorLe p place b (Z₁ ⊔ Z₂) admissible r β := by
  obtain ⟨Λ₁, hdet₁, hΛ₁⟩ := h₁
  obtain ⟨Λ₂, hdet₂, hΛ₂⟩ := h₂
  have hortho : Z₁.IsOrtho Z₂ := Submodule.isOrtho_iff_le.mpr hZ
  have hdisj : Disjoint Z₁ Z₂ := hortho.disjoint
  let e : (Z₁ × Z₂) ≃ₗ[ℂ] ↥(Z₁ ⊔ Z₂) :=
    (LinearEquiv.ofInjective (Z₁.subtype.coprod Z₂.subtype)
      (by rw [← LinearMap.ker_eq_bot, LinearMap.ker_coprod_of_disjoint_range] <;> simp [hdisj]))
      |>.trans (LinearEquiv.ofEq _ _ (Submodule.sup_eq_range Z₁ Z₂).symm)
  refine ⟨e.toLinearMap ∘ₗ LinearMap.prodMap Λ₁ Λ₂ ∘ₗ e.symm.toLinearMap, ?_, ?_⟩
  · have hdim : Module.finrank ℂ ↥(Z₁ ⊔ Z₂) = Module.finrank ℂ Z₁ + Module.finrank ℂ Z₂ := by
      rw [← e.finrank_eq, Module.finrank_prod]
    rw [LinearMap.det_conj, LinearMap.det_prodMap, map_mul, norm_mul, hdim, Nat.add_mul,
      Nat.cast_add, neg_add, add_mul, Real.exp_add]
    exact mul_le_mul hdet₁ hdet₂ (Real.exp_nonneg _) (norm_nonneg _)
  · intro y hy hadm
    have hproj : e.symm ((Z₁ ⊔ Z₂).orthogonalProjectionOnto y) =
        (Z₁.orthogonalProjectionOnto y, Z₂.orthogonalProjectionOnto y) := by
      apply e.injective
      ext
      simpa [e] using DFunLike.congr_fun hortho.starProjection_sup y
    have hval : (((e.toLinearMap ∘ₗ LinearMap.prodMap Λ₁ Λ₂ ∘ₗ e.symm.toLinearMap)
        ((Z₁ ⊔ Z₂).orthogonalProjectionOnto y) : ↥(Z₁ ⊔ Z₂)) : E) =
        ((Λ₁ (Z₁.orthogonalProjectionOnto y) : Z₁) : E) +
          ((Λ₂ (Z₂.orthogonalProjectionOnto y) : Z₂) : E) := by
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, hproj, LinearMap.prodMap_apply]
      simp [e]
    rw [hval]
    refine ⟨add_mem (hΛ₁ y hy hadm).1 (hΛ₂ y hy hadm).1, fun y' hy' ↦ ?_⟩
    rw [inner_add_right, map_add]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans
      (max_le ((hΛ₁ y hy hadm).2 y' hy') ((hΛ₂ y hy hadm).2 y' hy'))

end Denominator

end TauCeti.ThetaLift
