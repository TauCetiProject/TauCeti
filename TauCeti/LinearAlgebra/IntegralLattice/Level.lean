/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.Discriminant.Quadratic
public import TauCeti.LinearAlgebra.IntegralLattice.Unimodular
public import TauCeti.LinearAlgebra.Matrix.BilinearForm

/-!
# The level of an integral lattice

The **level** of a nondegenerate integral lattice `L` with Gram matrix `G` is classically the
least positive integer `N` for which `N • G⁻¹` is an integral matrix with even diagonal. Since
`G⁻¹` is the Gram matrix of the dual basis, this says that the form `N • B` is integral and even
on the dual lattice `Lᵛ`. Evenness alone already forces integrality, by polarization, so this file
defines the level intrinsically as the nonnegative generator of the ideal of integers `N` with

```text
N · B(x, x) ∈ 2ℤ   for every x ∈ Lᵛ,
```

and then proves the classical description in every carrier basis.

For an even lattice, `N · B(x, x) ∈ 2ℤ` says that `N` kills the half-norm `q_L(x) = B(x, x) / 2`
modulo `ℤ`, so the level is the least `N` with `N • q_L = 0` on the discriminant group. In general
the level divides `2 · det L`, and it kills the discriminant group `A_L = Lᵛ / L`.

## Main definitions and results

* `TauCeti.IntegralLattice.level`: the level of an integral lattice.
* `TauCeti.IntegralLattice.level_dvd_iff`: the level divides `N` exactly when `N · B(x, x)` is an
  even integer for every dual vector `x`.
* `TauCeti.IntegralLattice.mul_form_mem_one_of_level_dvd`: a multiple `N` of the level makes
  `N · B` integral on the dual lattice.
* `TauCeti.IntegralLattice.level_dvd_iff_gramMatrix` and `TauCeti.IntegralLattice.isLeast_level`:
  in every carrier basis with Gram matrix `G`, the level is the least positive `N` for which
  `N • G⁻¹` is integral with even diagonal.
* `TauCeti.IntegralLattice.IsEven.level_dvd_iff`: for an even lattice, the level divides `N`
  exactly when `N` kills the discriminant quadratic form.
* `TauCeti.IntegralLattice.level_nsmul_mem_carrier` and
  `TauCeti.IntegralLattice.exponent_discriminantGroup_dvd_level`: the level kills `A_L`.
* `TauCeti.IntegralLattice.level_dvd_two_mul_determinant`: the level divides `2 · det L`.
* `TauCeti.IntegralLattice.level_pos`: a nondegenerate lattice has positive level.
* `TauCeti.IntegralLattice.level_eq_one_iff`: a nondegenerate lattice has level one exactly when
  it is even and unimodular.
* `TauCeti.IntegralLattice.IsUnimodular.level_eq_two_iff`: a unimodular lattice has level two
  exactly when it is odd.
* `TauCeti.IntegralLattice.Isometry.level_eq`: the level is an isometry invariant.

## References

* T. Miyake, *Modular Forms*, §4.9.
* W. Ebeling, *Lattices and Codes*, Chapter 3.
-/

public section

open Module

namespace TauCeti

universe u v

namespace IntegralLattice

variable {V : Type u} [AddCommGroup V] [Module ℚ V]

/-- The ideal of integers `N` such that `N · B(x, x)` is an even integer for every dual vector
`x`. Its nonnegative generator is the level. -/
private def levelIdeal (L : IntegralLattice V) : Ideal ℤ where
  carrier := {N | ∀ x ∈ L.dualCarrier, ∃ k : ℤ, (N : ℚ) * L.norm x = 2 * k}
  zero_mem' _ _ := ⟨0, by simp⟩
  add_mem' {a b} ha hb x hx := by
    obtain ⟨k, hk⟩ := ha x hx
    obtain ⟨l, hl⟩ := hb x hx
    exact ⟨k + l, by push_cast; linear_combination hk + hl⟩
  smul_mem' c N hN x hx := by
    obtain ⟨k, hk⟩ := hN x hx
    exact ⟨c * k, by rw [smul_eq_mul]; push_cast; linear_combination (c : ℚ) * hk⟩

private theorem mem_levelIdeal_iff (L : IntegralLattice V) (N : ℤ) :
    N ∈ L.levelIdeal ↔ ∀ x ∈ L.dualCarrier, ∃ k : ℤ, (N : ℚ) * L.norm x = 2 * k :=
  Iff.rfl

/-- The **level** of an integral lattice: the nonnegative generator of the ideal of integers `N`
such that `N · B(x, x)` is an even integer for every vector `x` of the dual lattice `Lᵛ`
(`level_dvd_iff`). It is positive when `L` is nondegenerate (`level_pos`).

For a nondegenerate lattice this is the least positive `N` for which `N • G⁻¹` is an integral
matrix with even diagonal, `G` being a Gram matrix of `L` (`isLeast_level`). -/
noncomputable def level (L : IntegralLattice V) : ℕ :=
  (Submodule.IsPrincipal.generator L.levelIdeal).natAbs

/-- **The defining property of the level**: it divides `N` exactly when `N · B(x, x)` is an even
integer for every dual vector `x`. -/
theorem level_dvd_iff (L : IntegralLattice V) (N : ℤ) :
    (L.level : ℤ) ∣ N ↔ ∀ x ∈ L.dualCarrier, ∃ k : ℤ, (N : ℚ) * L.norm x = 2 * k := by
  rw [level, Int.natAbs_dvd, ← Submodule.IsPrincipal.mem_iff_generator_dvd, mem_levelIdeal_iff]

/-- For a multiple `N` of the level, the form `N · B` is integral on the dual lattice. -/
theorem mul_form_mem_one_of_level_dvd {L : IntegralLattice V} {N : ℤ} (hN : (L.level : ℤ) ∣ N)
    {x y : V} (hx : x ∈ L.dualCarrier) (hy : y ∈ L.dualCarrier) :
    (N : ℚ) * L.form x y ∈ (1 : Submodule ℤ ℚ) := by
  rw [level_dvd_iff] at hN
  obtain ⟨a, ha⟩ := hN (x + y) (add_mem hx hy)
  obtain ⟨b, hb⟩ := hN x hx
  obtain ⟨c, hc⟩ := hN y hy
  rw [L.norm_add] at ha
  refine Submodule.mem_one.mpr ⟨a - b - c, ?_⟩
  rw [eq_intCast]
  push_cast
  linear_combination (hb + hc - ha) / 2

/-! ## The level kills the discriminant group -/

/-- A multiple of the level by a dual vector lies in the lattice, when `L` is nondegenerate. -/
theorem level_nsmul_mem_carrier {L : IntegralLattice V} [L.IsNondegenerate] {x : V}
    (hx : x ∈ L.dualCarrier) :
    L.level • x ∈ L.carrier := by
  rw [← L.forall_form_mem_one_dualCarrier_iff]
  intro y hy
  have := mul_form_mem_one_of_level_dvd (dvd_refl (L.level : ℤ)) hx hy
  simpa [nsmul_eq_mul] using this

/-- The exponent of the discriminant group of a nondegenerate lattice divides its level. -/
theorem exponent_discriminantGroup_dvd_level (L : IntegralLattice V) [L.IsNondegenerate] :
    AddMonoid.exponent L.DiscriminantGroup ∣ L.level := by
  refine AddMonoid.exponent_dvd_of_forall_nsmul_eq_zero fun a ↦ ?_
  induction a using Submodule.Quotient.induction_on with
  | H x =>
    rw [← Submodule.Quotient.mk_smul, discriminantGroup_mk_eq_zero_iff]
    exact level_nsmul_mem_carrier x.2

/-- **The level divides twice the determinant.** -/
theorem level_dvd_two_mul_determinant (L : IntegralLattice V) :
    (L.level : ℤ) ∣ 2 * L.determinant := by
  by_cases hdet : L.determinant = 0
  · simp [hdet]
  have : L.IsNondegenerate := ⟨(L.determinant_ne_zero_iff).mp hdet⟩
  rw [← Int.dvd_natAbs, Int.natAbs_mul, ← discriminant_def, ← L.natCard_discriminantGroup]
  refine (L.level_dvd_iff _).mpr fun x hx ↦ ?_
  -- The order of `A_L` kills the class of `x`, so `#A_L • x` lies in `L` and pairs integrally
  -- with `x`.
  have hmem : Nat.card L.DiscriminantGroup • x ∈ L.carrier := by
    have h := card_nsmul_eq_zero' (G := L.DiscriminantGroup)
      (x := Submodule.Quotient.mk (⟨x, hx⟩ : L.dualCarrier))
    rw [← Submodule.Quotient.mk_smul, discriminantGroup_mk_eq_zero_iff] at h
    exact h
  rw [LinearMap.BilinForm.mem_dualSubmodule] at hx
  obtain ⟨k, hk⟩ := Submodule.mem_one.mp (hx _ hmem)
  refine ⟨k, ?_⟩
  rw [eq_intCast, map_nsmul, nsmul_eq_mul] at hk
  rw [norm_apply, hk]
  push_cast
  ring

/-- A nondegenerate lattice has positive level. -/
theorem level_pos (L : IntegralLattice V) [L.IsNondegenerate] : 0 < L.level := by
  refine Nat.pos_of_ne_zero fun h ↦ (L.determinant_ne_zero_iff.mpr L.form_nondegenerate) ?_
  have := L.level_dvd_two_mul_determinant
  rw [h, Nat.cast_zero, zero_dvd_iff] at this
  omega

/-! ## The level in a carrier basis -/

section Gram

open scoped Matrix

variable (L : IntegralLattice V)

/-- The level can be checked on any rational basis `f` whose integral span is the dual lattice:
the level divides `N` exactly when `N · B` is integral on `f` with even values on its diagonal. -/
private theorem level_dvd_iff_of_dualCarrier_eq_span {ι : Type*} [Finite ι] (f : Basis ι ℚ V)
    (hspan : L.dualCarrier = Submodule.span ℤ (Set.range f)) (N : ℤ) :
    (L.level : ℤ) ∣ N ↔ (∀ i j, (N : ℚ) * L.form (f i) (f j) ∈ (1 : Submodule ℤ ℚ)) ∧
      ∀ i, ∃ z : ℤ, (N : ℚ) * L.form (f i) (f i) = 2 * z := by
  have hf (i : ι) : f i ∈ L.dualCarrier := hspan ▸ Submodule.subset_span (Set.mem_range_self i)
  refine ⟨fun hN ↦ ⟨fun i j ↦ mul_form_mem_one_of_level_dvd hN (hf i) (hf j), fun i ↦ ?_⟩, ?_⟩
  · simpa only [norm_apply] using (L.level_dvd_iff N).mp hN (f i) (hf i)
  · rintro ⟨hint, heven⟩
    -- The scaled form `N • B` makes the dual carrier an even integral lattice.
    let D := ofBasis f ((N : ℚ) • L.form) (L.isSymm.smul (N : ℚ)) hint
    have hD : D.IsEven := (isEven_ofBasis_iff f _ _ hint).mpr heven
    rw [level_dvd_iff]
    intro x hx
    rw [hspan] at hx
    have hxD : x ∈ D.carrier := by simpa only [D, ofBasis_carrier] using hx
    obtain ⟨k, hk⟩ := hD.exists_norm_eq_two_mul ⟨x, hxD⟩
    exact ⟨k, by simpa [D, norm_apply] using hk⟩

variable [L.IsNondegenerate]

/-- **Basis independence of the level.** In any carrier basis with Gram matrix `G`, the level of
a nondegenerate lattice divides `N` exactly when `N • G⁻¹` is an integral matrix with even
diagonal. -/
theorem level_dvd_iff_gramMatrix {ι : Type v} [Fintype ι] [DecidableEq ι] (b : Basis ι ℤ L)
    (N : ℤ) :
    (L.level : ℤ) ∣ N ↔ ∃ M : Matrix ι ι ℤ, (∀ i, Even (M i i)) ∧
      M.map (Int.cast : ℤ → ℚ) = (N : ℚ) • ((L.gramMatrix b).map (Int.cast : ℤ → ℚ))⁻¹ := by
  set f := L.form.dualBasis L.form_nondegenerate (b.extendOfIsLattice ℚ)
  -- The inverse Gram matrix is the Gram matrix of the dual basis.
  have hinv (i j : ι) : ((L.gramMatrix b).map (Int.cast : ℤ → ℚ))⁻¹ i j = L.form (f i) (f j) := by
    have hsymm : ((L.gramMatrix b).map (Int.cast : ℤ → ℚ))ᵀ =
        (L.gramMatrix b).map (Int.cast : ℤ → ℚ) := by
      rw [← Matrix.transpose_map, (L.isSymm_gramMatrix b).eq]
    have hmap : (L.gramMatrix b).map (Int.cast : ℤ → ℚ) =
        LinearMap.BilinForm.toMatrix (b.extendOfIsLattice ℚ) L.form := by
      rw [← L.map_gramMatrix b, algebraMap_int_eq, Int.coe_castRingHom]
    rw [← hsymm, hmap, ← LinearMap.BilinForm.toMatrix_dualBasis _ L.form_nondegenerate,
      LinearMap.BilinForm.toMatrix_apply]
  rw [L.level_dvd_iff_of_dualCarrier_eq_span f (by convert L.dualCarrier_eq_span_dualBasis b) N]
  constructor
  · rintro ⟨hint, heven⟩
    choose M hM using fun i j ↦ Submodule.mem_one.mp (hint i j)
    refine ⟨Matrix.of M, fun i ↦ ?_, ?_⟩
    · obtain ⟨z, hz⟩ := heven i
      refine ⟨z, Int.cast_injective (α := ℚ) ?_⟩
      have := hM i i
      rw [eq_intCast] at this
      push_cast
      rw [Matrix.of_apply, this, hz]
      ring
    · ext i j
      have := hM i j
      rw [eq_intCast] at this
      simp only [Matrix.map_apply, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, hinv]
      exact this
  · rintro ⟨M, heven, hM⟩
    have hentry (i j : ι) : (N : ℚ) * L.form (f i) (f j) = M i j := by
      have := congrFun (congrFun hM i) j
      simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, hinv] at this
      exact this.symm
    refine ⟨fun i j ↦ Submodule.mem_one.mpr ⟨M i j, by rw [eq_intCast, hentry]⟩, fun i ↦ ?_⟩
    obtain ⟨z, hz⟩ := heven i
    exact ⟨z, by rw [hentry, hz]; push_cast; ring⟩

/-- **The level as a least element.** In any carrier basis with Gram matrix `G`, the level of a
nondegenerate lattice is the least positive `N` for which `N • G⁻¹` is an integral matrix with
even diagonal. -/
theorem isLeast_level {ι : Type v} [Fintype ι] [DecidableEq ι] (b : Basis ι ℤ L) :
    IsLeast {N : ℕ | 0 < N ∧ ∃ M : Matrix ι ι ℤ, (∀ i, Even (M i i)) ∧
      M.map (Int.cast : ℤ → ℚ) = (N : ℚ) • ((L.gramMatrix b).map (Int.cast : ℤ → ℚ))⁻¹}
      L.level := by
  refine ⟨⟨L.level_pos, ?_⟩, fun N ⟨hN, hM⟩ ↦ Nat.le_of_dvd hN ?_⟩
  · simpa using (L.level_dvd_iff_gramMatrix b L.level).mp dvd_rfl
  · exact Int.natCast_dvd_natCast.mp ((L.level_dvd_iff_gramMatrix b N).mpr (by simpa using hM))

end Gram

/-! ## Even lattices: the level annihilates the discriminant form -/

/-- **The level of an even lattice is the annihilator of its discriminant form**: the level
divides `N` exactly when `N • q_L = 0` on the discriminant group. -/
theorem IsEven.level_dvd_iff {L : IntegralLattice V} (hL : L.IsEven) (N : ℤ) :
    (L.level : ℤ) ∣ N ↔ ∀ a : L.DiscriminantGroup, N • L.discriminantQuadraticMap hL a = 0 := by
  rw [L.level_dvd_iff]
  constructor
  · intro h a
    induction a using Submodule.Quotient.induction_on with
    | H x =>
      obtain ⟨k, hk⟩ := h x x.2
      rw [discriminantQuadraticMap_mk]
      refine AddCircle.zsmul_coe_eq_zero (c := k) ?_
      rw [norm_apply] at hk
      linear_combination hk / 2
  · intro h x hx
    have h' := h (Submodule.Quotient.mk ⟨x, hx⟩)
    rw [discriminantQuadraticMap_mk, ← AddCircle.coe_zsmul,
      AddCircle.coe_eq_zero_iff_mem_one] at h'
    obtain ⟨k, hk⟩ := Submodule.mem_one.mp h'
    rw [eq_intCast, zsmul_eq_mul] at hk
    refine ⟨k, ?_⟩
    rw [norm_apply]
    linear_combination -2 * hk

/-! ## Unimodular lattices -/

/-- A nondegenerate lattice has level one exactly when it is even and unimodular.

Nondegeneracy is needed: the zero form on `ℤ` has the whole rational line as its dual lattice, on
which every norm vanishes, so its level is one although it is not unimodular. -/
theorem level_eq_one_iff (L : IntegralLattice V) [L.IsNondegenerate] :
    L.level = 1 ↔ L.IsEven ∧ L.IsUnimodular := by
  constructor
  · intro h
    refine ⟨L.isEven_iff_forall_norm.mpr fun x ↦ ?_,
      L.isUnimodular_iff_dualCarrier_le.mpr fun x hx ↦ ?_⟩
    · obtain ⟨k, hk⟩ := (L.level_dvd_iff 1).mp (by simp [h]) x (L.le_dualCarrier x.2)
      exact ⟨k, by simpa using hk⟩
    · simpa [h] using level_nsmul_mem_carrier hx
  · rintro ⟨he, hu⟩
    have h : (L.level : ℤ) ∣ 1 := (L.level_dvd_iff 1).mpr fun x hx ↦ by
      obtain ⟨k, hk⟩ := he.exists_norm_eq_two_mul ⟨x, (L.isUnimodular_def.mp hu).symm ▸ hx⟩
      exact ⟨k, by simpa using hk⟩
    exact Nat.dvd_one.mp (Int.natCast_dvd_natCast.mp h)

/-- A unimodular lattice has level dividing two. -/
theorem IsUnimodular.level_dvd_two {L : IntegralLattice V} (hL : L.IsUnimodular) :
    L.level ∣ 2 := by
  have : L.IsNondegenerate := ⟨hL.nondegenerate⟩
  have h := L.level_dvd_two_mul_determinant
  rcases Int.isUnit_iff.mp ((L.isUnimodular_iff_isUnit_determinant).mp hL) with hd | hd <;>
    rw [hd] at h
  · exact Int.natCast_dvd_natCast.mp h
  · exact Int.natCast_dvd_natCast.mp (dvd_neg.mp (by simpa using h))

/-- A unimodular lattice has level two exactly when it is odd, and level one otherwise. -/
theorem IsUnimodular.level_eq_two_iff {L : IntegralLattice V} (hL : L.IsUnimodular) :
    L.level = 2 ↔ ¬ L.IsEven := by
  have : L.IsNondegenerate := ⟨hL.nondegenerate⟩
  have h1 : L.level = 1 ↔ L.IsEven := by rw [L.level_eq_one_iff, and_iff_left hL]
  have h2 := hL.level_dvd_two
  have h0 := L.level_pos
  have : L.level ≤ 2 := Nat.le_of_dvd two_pos h2
  rw [← h1]
  interval_cases h : L.level <;> simp_all

/-! ## Isometry invariance -/

namespace Isometry

variable {W : Type v} [AddCommGroup W] [Module ℚ W] {L : IntegralLattice V}
  {M : IntegralLattice W}

/-- **The level is an isometry invariant.** -/
theorem level_eq (e : Isometry L M) : L.level = M.level := by
  have h (N : ℤ) : (L.level : ℤ) ∣ N ↔ (M.level : ℤ) ∣ N := by
    rw [L.level_dvd_iff, M.level_dvd_iff]
    constructor
    · intro h y hy
      obtain ⟨k, hk⟩ := h (e.symm y) ((e.apply_mem_dualCarrier_iff _).mp
        (by rwa [e.apply_symm_apply]))
      exact ⟨k, by rwa [← e.apply_symm_apply y, e.norm_apply]⟩
    · intro h x hx
      obtain ⟨k, hk⟩ := h (e x) ((e.apply_mem_dualCarrier_iff x).mpr hx)
      exact ⟨k, by rwa [← e.norm_apply]⟩
  exact Nat.dvd_antisymm (Int.natCast_dvd_natCast.mp ((h _).mpr dvd_rfl))
    (Int.natCast_dvd_natCast.mp ((h _).mp dvd_rfl))

end Isometry

end IntegralLattice

end TauCeti
