/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.ProjectiveLattice
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Cartan.DiscreteValuationRing
public import TauCeti.RingTheory.AffineGrassmannian.Lattice.Filtration
import TauCeti.Algebra.Algebra.IsUnit

/-!
# The orbits of `GLₙ` of the integers on lattices

Let `B` be a commutative ring, `K` a `B`-algebra with `B → K` injective, and `ξ ∈ B` an element
that becomes a unit in `K`. For an exponent vector `k : n → ℤ`, the lattice
`TauCeti.diagonalLattice k hξ = ⊕ ξ^{k_i} B` of the cocharacter `μ = (k_i)` of the diagonal torus
is the image `diag(ξ^k) Bⁿ` of the standard lattice, so it is a finite projective lattice
(`TauCeti.ProjectiveLattice.diagonal`). When `ξ` is not a unit of `B`, these lattices are ordered
by the reverse of the pointwise order of the exponents.

For a discrete valuation ring `R` with fraction field `K` and uniformizer `ϖ`, the Cartan
decomposition of `GLₙ(K)` (`TauCeti.existsUnique_monotone_mem_doubleCoset_diagGL_zpow`) becomes
the classification of the lattices in `Kⁿ` up to `GLₙ(R)`: since `GLₙ(K)` acts transitively on
lattices with stabilizer `GLₙ(R)` at the standard lattice
(`TauCeti.ProjectiveLattice.exists_GL_smul_standard_eq`,
`TauCeti.ProjectiveLattice.stabilizer_standard`), every lattice lies in the `GLₙ(R)`-orbit of
exactly one lattice `diag(ϖ^a) Rⁿ` with `a₀ ≤ ⋯ ≤ aₙ₋₁`. For a field `F`, `R = F⟦X⟧` and
`K = F⸨X⸩` with the algebra structure of Mathlib, for which `K` is the fraction field of `R`, and
`ϖ = X`, these are the rational points of the loop Grassmannian of `GLₙ` and the indexing of the
orbits of the positive loop group by the dominant coweights. Moreover, the lattice of the orbit of
`a` lies between `ϖ^N Rⁿ` and `ϖ^{-N} Rⁿ` exactly when every `|a_i| ≤ N`.

## Main definitions

* `TauCeti.ProjectiveLattice.diagonal k hξ`: the lattice `diag(ξ^k) Bⁿ`, whose underlying
  submodule is `TauCeti.diagonalLattice k hξ`.

## Main results

* `TauCeti.ProjectiveLattice.diagonal_le_diagonal_iff`: if `ξ` is not a unit of `B`, then
  `diag(ξ^a) Bⁿ ⊆ diag(ξ^b) Bⁿ` exactly when `b ≤ a`; in particular `diag(ξ^a) Bⁿ` determines
  `a` (`TauCeti.ProjectiveLattice.diagonal_inj`).
* `TauCeti.ProjectiveLattice.map_smul_diagonal_mem_Icc_iff`: `g diag(ξ^a) Bⁿ` for `g ∈ GLₙ(B)`
  lies between `ξ^N Bⁿ` and `ξ^{-N} Bⁿ` exactly when every `|a_i| ≤ N`.
* `TauCeti.ProjectiveLattice.existsUnique_monotone_map_smul_diagonal_eq`: over a discrete
  valuation ring, every lattice is `g diag(ϖ^a) Rⁿ` for some `g ∈ GLₙ(R)` and exactly one
  monotone `a`.

## References

* X. Zhu, *An introduction to affine Grassmannians and the geometric Satake equivalence*, in
  *Geometry of Moduli Spaces and Representation Theory*, IAS/Park City Math. Ser. 24 (2017),
  §1.1 and §2.1.
* I. G. Macdonald, *Spherical Functions on a Group of p-adic Type*, Ramanujan Institute (1971),
  Chapter II, §2.6.
-/

public section

open Matrix DoubleCoset

namespace TauCeti.ProjectiveLattice

section Diagonal

variable {B K : Type*} [CommRing B] [CommRing K] [Algebra B K] [FaithfulSMul B K]
  {n : Type*} [Fintype n] [DecidableEq n] {ξ : B}

/-- **The lattice of a diagonal cocharacter** as a finite projective lattice: for `k : n → ℤ` and
`ξ ∈ B` invertible in `K`, the image `diag(ξ^k) Bⁿ` of the standard lattice. Its underlying
submodule is `TauCeti.diagonalLattice k hξ` (`TauCeti.ProjectiveLattice.toSubmodule_diagonal`). -/
noncomputable def diagonal (k : n → ℤ) (hξ : IsUnit (algebraMap B K ξ)) :
    ProjectiveLattice B K (n → K) :=
  diagGL (fun i ↦ hξ.unit ^ k i) • standard B K n

theorem diagGL_smul_standard (k : n → ℤ) (hξ : IsUnit (algebraMap B K ξ)) :
    diagGL (fun i ↦ hξ.unit ^ k i) • standard B K n = diagonal k hξ :=
  (rfl)

@[simp]
theorem mem_diagonal {k : n → ℤ} {hξ : IsUnit (algebraMap B K ξ)} {v : n → K} :
    v ∈ diagonal k hξ ↔ ∀ i, ∃ b : B, v i = (hξ.unit ^ k i : Kˣ) * algebraMap B K b := by
  rw [← diagGL_smul_standard, mem_GL_smul, ← map_inv, diagGL_coe, mem_standard]
  simp only [mulVec_diagonal, Set.mem_range]
  refine forall_congr' fun i ↦ exists_congr fun b ↦ ?_
  rw [eq_comm, Pi.inv_apply, Units.inv_mul_eq_iff_eq_mul]

@[simp]
theorem toSubmodule_diagonal (k : n → ℤ) (hξ : IsUnit (algebraMap B K ξ)) :
    (diagonal k hξ).toSubmodule = diagonalLattice k hξ := by
  ext v
  rw [mem_toSubmodule, mem_diagonal, mem_diagonalLattice]

/-- The lattice of the zero cocharacter is the standard lattice. -/
@[simp]
theorem diagonal_zero (hξ : IsUnit (algebraMap B K ξ)) :
    diagonal (0 : n → ℤ) hξ = standard B K n := by
  rw [← diagGL_smul_standard]
  simp

/-- The lattice of a constant cocharacter `m` is `ξ^m` times the standard lattice. -/
theorem diagonal_const (m : ℤ) (hξ : IsUnit (algebraMap B K ξ)) :
    diagonal (fun _ : n ↦ m) hξ = GeneralLinearGroup.scalar n (hξ.unit ^ m) • standard B K n := by
  rw [← diagGL_smul_standard, diagGL_const]

/-- `diag(ξ^a)` sends the lattice of `b` to the lattice of `a + b`. -/
theorem diagGL_smul_diagonal (a b : n → ℤ) (hξ : IsUnit (algebraMap B K ξ)) :
    diagGL (fun i ↦ hξ.unit ^ a i) • diagonal b hξ = diagonal (a + b) hξ := by
  rw [← diagGL_smul_standard, ← diagGL_smul_standard, smul_smul, ← map_mul]
  congr 2
  funext i
  simp [_root_.zpow_add]

/-- The image of `GLₙ(B)` fixes the lattice `ξ^m Bⁿ` of a constant cocharacter. -/
@[simp]
theorem map_smul_diagonal_const (A : GL n B) (m : ℤ) (hξ : IsUnit (algebraMap B K ξ)) :
    GeneralLinearGroup.map (algebraMap B K) A • diagonal (fun _ : n ↦ m) hξ =
      diagonal (fun _ : n ↦ m) hξ := by
  rw [diagonal_const, smul_smul, ← GeneralLinearGroup.scalar_commute, mul_smul,
    map_smul_standard]

/-- If `ξ` is not a unit of `B`, then `diag(ξ^a) Bⁿ ⊆ diag(ξ^b) Bⁿ` exactly when `b ≤ a`
pointwise. -/
@[simp]
theorem diagonal_le_diagonal_iff (hξ' : ¬IsUnit ξ) {a b : n → ℤ}
    (hξ : IsUnit (algebraMap B K ξ)) : diagonal a hξ ≤ diagonal b hξ ↔ b ≤ a := by
  refine ⟨fun h i ↦ ?_, fun h v hv ↦ mem_diagonal.mpr fun i ↦ ?_⟩
  · by_contra hlt
    rw [not_le] at hlt
    -- `ξ^{a i} e_i` lies in `diag(ξ^a) Bⁿ`, hence `ξ^{a i} ∈ ξ^{b i} B`, making `ξ` a unit.
    have hv : Pi.single i ((hξ.unit ^ a i : Kˣ) : K) ∈ diagonal a hξ := mem_diagonal.mpr fun j ↦ by
      by_cases hj : j = i
      · subst hj
        exact ⟨1, by simp⟩
      · exact ⟨0, by simp [hj]⟩
    obtain ⟨c, hc⟩ := mem_diagonal.mp (h hv) i
    rw [Pi.single_eq_same, IsUnit.val_unit_zpow_eq_mul_algebraMap_pow_of_le hξ hlt.le,
      mul_assoc, ← map_mul] at hc
    have h1 : ξ ^ (b i - a i).toNat * c = 1 := FaithfulSMul.algebraMap_injective B K <|
      ((Units.mul_right_inj _).mp (by rw [mul_one]; exact hc.symm)).trans (map_one _).symm
    have hlt' : a i < b i := hlt
    have hm : (b i - a i).toNat ≠ 0 := by omega
    exact hξ' ((isUnit_pow_iff hm).mp (.of_mul_eq_one _ h1))
  · obtain ⟨c, hc⟩ := mem_diagonal.mp hv i
    exact ⟨ξ ^ (a i - b i).toNat * c, by
      rw [hc, IsUnit.val_unit_zpow_eq_mul_algebraMap_pow_of_le hξ (h i), mul_assoc, map_mul]⟩

/-- If `ξ` is not a unit of `B`, a diagonal lattice determines its exponent vector. -/
@[simp]
theorem diagonal_inj (hξ' : ¬IsUnit ξ) {a b : n → ℤ} (hξ : IsUnit (algebraMap B K ξ)) :
    diagonal a hξ = diagonal b hξ ↔ a = b := by
  rw [le_antisymm_iff, diagonal_le_diagonal_iff hξ', diagonal_le_diagonal_iff hξ', and_comm,
    ← le_antisymm_iff]

/-- A lattice translated by `GLₙ(B)` contains `ξ^m Bⁿ` exactly when the lattice does. -/
@[simp]
theorem diagonal_const_le_map_smul_iff (A : GL n B) (m : ℤ) (hξ : IsUnit (algebraMap B K ξ))
    (Λ : ProjectiveLattice B K (n → K)) :
    diagonal (fun _ : n ↦ m) hξ ≤ GeneralLinearGroup.map (algebraMap B K) A • Λ ↔
      diagonal (fun _ : n ↦ m) hξ ≤ Λ := by
  rw [← map_smul_diagonal_const A m hξ, ProjectiveLattice.smul_le_smul_iff,
    map_smul_diagonal_const]

/-- A lattice translated by `GLₙ(B)` lies in `ξ^m Bⁿ` exactly when the lattice does. -/
@[simp]
theorem map_smul_le_diagonal_const_iff (A : GL n B) (m : ℤ) (hξ : IsUnit (algebraMap B K ξ))
    (Λ : ProjectiveLattice B K (n → K)) :
    GeneralLinearGroup.map (algebraMap B K) A • Λ ≤ diagonal (fun _ : n ↦ m) hξ ↔
      Λ ≤ diagonal (fun _ : n ↦ m) hξ := by
  rw [← map_smul_diagonal_const A m hξ, ProjectiveLattice.smul_le_smul_iff,
    map_smul_diagonal_const]

/-- **Bounded lattices.** If `ξ` is not a unit of `B` and `g ∈ GLₙ(B)`, the lattice
`g diag(ξ^a) Bⁿ` lies between `ξ^N Bⁿ` and `ξ^{-N} Bⁿ` exactly when every `|a_i| ≤ N`. -/
theorem map_smul_diagonal_mem_Icc_iff (hξ' : ¬IsUnit ξ) (hξ : IsUnit (algebraMap B K ξ))
    (A : GL n B) (a : n → ℤ) (N : ℤ) :
    GeneralLinearGroup.map (algebraMap B K) A • diagonal a hξ ∈
        Set.Icc (diagonal (fun _ : n ↦ N) hξ) (diagonal (fun _ : n ↦ -N) hξ) ↔ ∀ i, |a i| ≤ N := by
  rw [Set.mem_Icc, diagonal_const_le_map_smul_iff, map_smul_le_diagonal_const_iff,
    diagonal_le_diagonal_iff hξ', diagonal_le_diagonal_iff hξ']
  simp only [Pi.le_def, abs_le]
  exact ⟨fun h i ↦ ⟨h.2 i, h.1 i⟩, fun h ↦ ⟨fun i ↦ (h i).2, fun i ↦ (h i).1⟩⟩

end Diagonal

section DiscreteValuationRing

variable {R K : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K]
  [Algebra R K] [IsFractionRing R K] {ϖ : R} {n : ℕ}

/-- **Existence of the Cartan invariant of a lattice.** Over a discrete valuation ring `R` with
fraction field `K` and uniformizer `ϖ`, every lattice in `Kⁿ` is `g diag(ϖ^a) Rⁿ` for some
`g ∈ GLₙ(R)` and some monotone `a`. -/
theorem exists_monotone_map_smul_diagonal_eq (hϖ : Irreducible ϖ)
    (hξ : IsUnit (algebraMap R K ϖ)) (Λ : ProjectiveLattice R K (Fin n → K)) :
    ∃ a : Fin n → ℤ, Monotone a ∧
      ∃ g : GL (Fin n) R, GeneralLinearGroup.map (algebraMap R K) g • diagonal a hξ = Λ := by
  obtain ⟨h, rfl⟩ := exists_GL_smul_standard_eq (ι := Fin n) (nonZeroDivisors R) Λ
  obtain ⟨a, ha, hh⟩ := exists_monotone_mem_doubleCoset_diagGL_zpow hϖ hξ.unit_spec.symm h
  obtain ⟨_, ⟨x, rfl⟩, _, ⟨y, rfl⟩, rfl⟩ := mem_doubleCoset.mp hh
  exact ⟨a, ha, x, by rw [mul_smul, mul_smul, map_smul_standard, diagGL_smul_standard]⟩

/-- **Uniqueness of the Cartan invariant of a lattice.** Over a discrete valuation ring with
uniformizer `ϖ`, if `g diag(ϖ^a) Rⁿ = g' diag(ϖ^b) Rⁿ` for `g, g' ∈ GLₙ(R)` and monotone `a`, `b`,
then `a = b`. -/
theorem eq_of_monotone_of_map_smul_diagonal_eq (hϖ : Irreducible ϖ)
    (hξ : IsUnit (algebraMap R K ϖ)) {a b : Fin n → ℤ} (ha : Monotone a) (hb : Monotone b)
    {g g' : GL (Fin n) R}
    (h : GeneralLinearGroup.map (algebraMap R K) g • diagonal a hξ =
      GeneralLinearGroup.map (algebraMap R K) g' • diagonal b hξ) : a = b := by
  set φ := GeneralLinearGroup.map (n := Fin n) (algebraMap R K)
  -- `diag(ϖ^b)⁻¹ (φ g')⁻¹ (φ g) diag(ϖ^a)` fixes the standard lattice, so it is integral.
  have hs : (diagGL fun i ↦ hξ.unit ^ b i)⁻¹ * (φ g')⁻¹ * φ g * diagGL (fun i ↦ hξ.unit ^ a i) ∈
      MulAction.stabilizer (GL (Fin n) K) (standard R K (Fin n)) := by
    rw [MulAction.mem_stabilizer_iff, mul_smul, mul_smul, mul_smul, diagGL_smul_standard, h,
      smul_smul (φ g')⁻¹, inv_mul_cancel, one_smul, ← diagGL_smul_standard, inv_smul_smul]
  rw [stabilizer_standard] at hs
  obtain ⟨s, hs⟩ := hs
  refine eq_of_monotone_of_mem_doubleCoset_diagGL_zpow hϖ hξ.unit_spec.symm ha hb
    (mem_doubleCoset_self _ _ _) (mem_doubleCoset.mpr ⟨φ (g⁻¹ * g'), ⟨_, rfl⟩, φ s, ⟨s, rfl⟩, ?_⟩)
  rw [hs, map_mul, map_inv]
  group

/-- **The Cartan decomposition for lattices.** Over a discrete valuation ring `R` with fraction
field `K` and uniformizer `ϖ`, every lattice in `Kⁿ` lies in the `GLₙ(R)`-orbit of
`diag(ϖ^a) Rⁿ` for exactly one monotone exponent vector `a`. -/
theorem existsUnique_monotone_map_smul_diagonal_eq (hϖ : Irreducible ϖ)
    (hξ : IsUnit (algebraMap R K ϖ)) (Λ : ProjectiveLattice R K (Fin n → K)) :
    ∃! a : Fin n → ℤ, Monotone a ∧
      ∃ g : GL (Fin n) R, GeneralLinearGroup.map (algebraMap R K) g • diagonal a hξ = Λ :=
  let ⟨a, ha, g, hg⟩ := exists_monotone_map_smul_diagonal_eq hϖ hξ Λ
  ⟨a, ⟨ha, g, hg⟩, fun _ ⟨hb, _, hg'⟩ ↦
    (eq_of_monotone_of_map_smul_diagonal_eq hϖ hξ ha hb (hg.trans hg'.symm)).symm⟩

end DiscreteValuationRing

end TauCeti.ProjectiveLattice
