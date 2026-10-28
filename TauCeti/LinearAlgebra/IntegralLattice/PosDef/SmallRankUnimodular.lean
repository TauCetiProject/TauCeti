/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.Characteristic.EvenSublattice
public import TauCeti.LinearAlgebra.IntegralLattice.Index
public import TauCeti.LinearAlgebra.IntegralLattice.Neighbor.Isotropic
public import TauCeti.LinearAlgebra.IntegralLattice.Neighbor.UnitLattice
public import TauCeti.LinearAlgebra.IntegralLattice.Orthogonal.UnitNorm
public import TauCeti.LinearAlgebra.IntegralLattice.PosDef.Covolume
public import TauCeti.LinearAlgebra.IntegralLattice.PosDef.Hermite
public import TauCeti.LinearAlgebra.IntegralLattice.PosDef.UnitNormSplitting

/-!
# Positive definite unimodular lattices of rank at most nine

A positive definite unimodular lattice of rank at most nine is the standard lattice `Iₙ`, the root
lattice `E₈`, or `I₁ ⊕ E₈`. In particular `E₈` is the unique even unimodular positive definite
lattice of rank eight.

For a positive definite unimodular lattice `L` of rank `n`, Hermite's inequality
`3 ^ (n choose 2) · (min L)ⁿ ≤ 4 ^ (n choose 2)` bounds the minimum:

* if `1 ≤ n ≤ 5`, then `min L = 1`, since `3 ^ (n choose 2) · 2ⁿ > 4 ^ (n choose 2)`;
* if `n ≤ 8`, then `min L ≤ 2`: in rank zero the minimum is zero, and if `1 ≤ n ≤ 8`, then
  `3 ^ (n choose 2) · 3ⁿ > 4 ^ (n choose 2)`.

Both ranges are the exact ones in which this inequality excludes the next value of the minimum.
Combined with the splitting `L ≅ I_k ⊕ L₀` of the vectors of norm one, the first bound shows
that a positive definite unimodular lattice of rank at most five is `Iₙ`; equivalently, a nonzero
positive definite unimodular lattice without vectors of norm one has rank at least six.

Hermite's inequality also gives vectors of norm two up to rank nine. Applied to the even
sublattice, which has determinant at most four, it shows that a positive definite unimodular
lattice of rank between two and nine has a vector `r` of norm two. Applied to the orthogonal
complement of `r` inside the vectors pairing evenly with `r`, which has rank `n - 1` and
determinant two, it gives a second vector `s` of norm at most two orthogonal to `r`.

Now let `L` have no vectors of norm one, so `r` and `s` both have norm two. The two-neighbor of
`L` along `r + s` contains the orthonormal vectors `(r + s) / 2` and `(r - s) / 2`, so it is
`I_k ⊕ M₀` with `k ≥ 2` and `M₀` of rank `n - k ≤ n - 2 ≤ 7` and without vectors of norm one.
In rank at most seven such an `M₀` is zero: by induction from rank at most five, since otherwise
the neighbor is `Iₙ` and `4 ∣ n`. Hence the neighbor is `Iₙ`. A two-neighbor of `Iₙ` without
vectors of norm one has `4 ∣ n` and, in rank eight, is `E₈`. So `L` is zero or `E₈`, and the
classification follows from the splitting `L ≅ I_k ⊕ L₀`.

## Main declarations

* `TauCeti.IntegralLattice.IsPosDef.minimum_eq_one_of_isUnimodular`: a nonzero lattice of rank
  at most five has minimum one.
* `TauCeti.IntegralLattice.IsPosDef.minimum_le_two_of_isUnimodular`: in rank at most eight the
  minimum is at most two.
* `TauCeti.IntegralLattice.IsPosDef.six_le_finrank_of_vectorsOfNorm_one_eq_empty`: a nonzero
  positive definite unimodular lattice without vectors of norm one has rank at least six.
* `TauCeti.IntegralLattice.IsPosDef.minimum_eq_two_of_vectorsOfNorm_one_eq_empty` and
  `TauCeti.IntegralLattice.IsPosDef.minimum_eq_two_of_isUnimodular_of_isEven`: in rank at most
  eight such a lattice, and in particular a nonzero even unimodular lattice, has minimum two.
* `TauCeti.IntegralLattice.IsPosDef.nonempty_isometry_unitLattice_of_isUnimodular`: a positive
  definite unimodular lattice of rank at most five is `Iₙ`.
* `TauCeti.IntegralLattice.IsPosDef.exists_integralNorm_eq_two_of_isUnimodular`: in rank between
  two and nine there is a vector of norm two.
* `TauCeti.IntegralLattice.IsPosDef.exists_integralForm_eq_zero_of_integralNorm_eq_two`: in rank
  between two and nine a vector of norm two is orthogonal to a nonzero vector of norm at most two.
* `TauCeti.IntegralLattice.IsPosDef.subsingleton_of_vectorsOfNorm_one_eq_empty_of_finrank_le_seven`:
  without vectors of norm one, a lattice of rank at most seven is zero.
* `IsPosDef.nonempty_isometry_typeE₈RootLattice_of_vectorsOfNorm_one_eq_empty`: without vectors
  of norm one, a nonzero lattice of rank at most nine is `E₈`.
* `TauCeti.IntegralLattice.IsPosDef.nonempty_isometry_of_isUnimodular_of_finrank_le_nine`: a
  lattice of rank at most nine is `Iₙ`, `E₈` or `I₁ ⊕ E₈`.
* `TauCeti.IntegralLattice.IsPosDef.nonempty_isometry_typeE₈RootLattice_of_isEven`: an even
  lattice of rank eight is `E₈`.

## References

* C. Hermite, *Extraits de lettres de M. Ch. Hermite à M. Jacobi sur différents objets de la
  théorie des nombres*, J. Reine Angew. Math. 40 (1850), 261–315.
* M. Kneser, *Klassenzahlen definiter quadratischer Formen*, Arch. Math. 8 (1957), 241--250.
* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, Chapter 16.
* O. T. O'Meara, *Introduction to Quadratic Forms*, §106.
-/

public section

open Module

namespace TauCeti.IntegralLattice

universe u

variable {V : Type u} [AddCommGroup V] [Module ℚ V] {L : IntegralLattice V}

/-- A vector of a unimodular lattice that is not twice a lattice vector pairs oddly with some
lattice vector. -/
private theorem exists_isCoprime_integralForm_two (hU : L.IsUnimodular) {v : L}
    (hv : ∀ y : L, v ≠ (2 : ℤ) • y) : ∃ w : L, IsCoprime (L.integralForm v w) 2 := by
  have : L.IsNondegenerate := ⟨hU.nondegenerate⟩
  by_contra! h
  have hmem := L.inv_smul_mem_carrier_of_forall_dvd (p := 2)
    (by rw [L.isUnimodular_iff_discriminant_eq_one.1 hU]; norm_num) fun w ↦
      even_iff_two_dvd.1 (Int.not_odd_iff_even.1 fun ho ↦ h w (Int.isCoprime_two_right.2 ho))
  refine hv ⟨_, hmem⟩ (Subtype.ext ?_)
  simp only [SetLike.val_smul, ← Int.cast_smul_eq_zsmul ℚ, Int.cast_ofNat, Nat.cast_ofNat,
    smul_inv_smul₀ (two_ne_zero (α := ℚ))]

namespace IsPosDef

/-- Hermite's inequality for a lattice of determinant at most `d`: the minimum lies below every
`k` with `4 ^ (n choose 2) · d < 3 ^ (n choose 2) · kⁿ`. -/
private theorem minimum_lt_of_four_pow_mul_lt (hL : L.IsPosDef) {d : ℤ} (hd : L.determinant ≤ d)
    {k : ℕ}
    (hk : 4 ^ (finrank ℤ L).choose 2 * d < 3 ^ (finrank ℤ L).choose 2 * k ^ finrank ℤ L) :
    L.minimum < k := by
  by_contra! h
  have hH := hL.three_pow_mul_minimum_pow_le
  have hle : (3 : ℤ) ^ (finrank ℤ L).choose 2 * (k : ℤ) ^ finrank ℤ L ≤
      3 ^ (finrank ℤ L).choose 2 * (L.minimum : ℤ) ^ finrank ℤ L := by
    gcongr
  have hd' : (4 : ℤ) ^ (finrank ℤ L).choose 2 * L.determinant ≤
      4 ^ (finrank ℤ L).choose 2 * d := by
    gcongr
  omega

variable (hL : L.IsPosDef) (hU : L.IsUnimodular)
include hL hU

/-- **A nonzero positive definite unimodular lattice of rank at most five has minimum one.** -/
theorem minimum_eq_one_of_isUnimodular [Nontrivial L] (hn : finrank ℤ L ≤ 5) :
    L.minimum = 1 := by
  have h1 : 0 < finrank ℤ L := finrank_pos
  have h := hL.minimum_lt_of_four_pow_mul_lt (hL.determinant_eq_one_of_isUnimodular hU).le
    (k := 2) <| by
    interval_cases finrank ℤ L <;> norm_num [Nat.choose_two_right]
  have := hL.minimum_pos
  omega

/-- **A positive definite unimodular lattice of rank at most eight has minimum at most two.** -/
theorem minimum_le_two_of_isUnimodular (hn : finrank ℤ L ≤ 8) : L.minimum ≤ 2 := by
  rcases subsingleton_or_nontrivial L with hL0 | hL0
  · rw [minimum_eq_zero_of_subsingleton]
    exact zero_le_two
  have h1 : 0 < finrank ℤ L := finrank_pos
  have h := hL.minimum_lt_of_four_pow_mul_lt (hL.determinant_eq_one_of_isUnimodular hU).le
    (k := 3) <| by
    interval_cases finrank ℤ L <;> norm_num [Nat.choose_two_right]
  omega

/-- **A nonzero positive definite unimodular lattice without vectors of norm one has rank at least
six.** -/
theorem six_le_finrank_of_vectorsOfNorm_one_eq_empty [Nontrivial L]
    (h1 : L.vectorsOfNorm 1 = ∅) : 6 ≤ finrank ℤ L := by
  by_contra! hn
  exact hL.isPosSemidef.minimum_ne_of_vectorsOfNorm_eq_empty (n := 1) (by exact_mod_cast h1)
    (hL.minimum_eq_one_of_isUnimodular hU (by omega))

/-- **A nonzero positive definite unimodular lattice of rank at most eight without vectors of norm
one has minimum two.** -/
theorem minimum_eq_two_of_vectorsOfNorm_one_eq_empty [Nontrivial L]
    (h1 : L.vectorsOfNorm 1 = ∅) (hn : finrank ℤ L ≤ 8) : L.minimum = 2 := by
  have hle := hL.minimum_le_two_of_isUnimodular hU hn
  have hpos := hL.minimum_pos
  have hne :=
    hL.isPosSemidef.minimum_ne_of_vectorsOfNorm_eq_empty (n := 1) (by exact_mod_cast h1)
  omega

/-- **A nonzero even positive definite unimodular lattice of rank at most eight has minimum
two.** -/
theorem minimum_eq_two_of_isUnimodular_of_isEven [Nontrivial L] (he : L.IsEven)
    (hn : finrank ℤ L ≤ 8) : L.minimum = 2 :=
  le_antisymm (hL.minimum_le_two_of_isUnimodular hU hn) (hL.two_le_minimum he)

/-- **A positive definite unimodular lattice of rank at most five is the standard lattice
`Iₙ`.** -/
theorem nonempty_isometry_unitLattice_of_isUnimodular (hn : finrank ℤ L ≤ 5) :
    Nonempty (Isometry (unitLattice (Fin (finrank ℤ L))) L) := by
  refine hL.nonempty_isometry_unitLattice_of_unitNormSubmodule_eq_top <|
    (hL.unitNormSubmodule_eq_top_iff).2 ?_
  have hL₀ := hL.isPosDef_unitNormComplement
  have hU₀ := (hL.isUnimodular_unitNormComplement_iff).2 hU
  have hrank := hL.finrank_unitNormSubmodule_add_finrank_unitNormComplement
  by_contra hns
  have : Nontrivial L.unitNormComplement := not_subsingleton_iff_nontrivial.1 hns
  have := hL₀.six_le_finrank_of_vectorsOfNorm_one_eq_empty hU₀
    L.vectorsOfNorm_one_unitNormComplement
  omega

/-- **A positive definite unimodular lattice of rank between two and nine has a vector of norm
two.** Such a vector already lies in the even sublattice. -/
theorem exists_integralNorm_eq_two_of_isUnimodular (h2 : 2 ≤ finrank ℤ L)
    (h9 : finrank ℤ L ≤ 9) : ∃ x : L, L.integralNorm x = 2 := by
  have hE : L.evenSublattice.IsPosDef := by
    rw [isPosDef_iff, evenSublattice_form]
    exact (isPosDef_iff L).1 hL
  have hrank : finrank ℤ L.evenSublattice = finrank ℤ L := by rw [finrank_carrier, finrank_carrier]
  have : Nontrivial L.evenSublattice := Module.nontrivial_of_finrank_pos (R := ℤ) (by omega)
  have hdet : L.evenSublattice.determinant ≤ 4 := by
    rw [determinant_eq_mul_relIndex_sq _ _ L.evenSublattice_form L.evenSublattice_carrier_le,
      hL.determinant_eq_one_of_isUnimodular hU, one_mul]
    have hidx := L.relIndex_evenSublattice_le_two
    interval_cases L.evenSublattice.carrier.toAddSubgroup.relIndex L.carrier.toAddSubgroup <;>
      norm_num
  have hlt := hE.minimum_lt_of_four_pow_mul_lt hdet (k := 4) <| by
    rw [hrank]
    interval_cases finrank ℤ L <;> norm_num [Nat.choose_two_right]
  have hge := hE.two_le_minimum L.isEven_evenSublattice
  obtain ⟨x, hx0, hx⟩ := hE.isPosSemidef.exists_ne_zero_integralNorm_eq_minimum
  obtain ⟨z, hz⟩ := (L.evenSublattice.even_integralNorm_iff x).2
    (L.isEven_evenSublattice.exists_norm_eq_two_mul x)
  refine ⟨Submodule.inclusion L.evenSublattice_carrier_le x, ?_⟩
  rw [integralNorm_apply, integralForm_inclusion _ _ L.evenSublattice_form, ← integralNorm_apply]
  omega

/-- **In a positive definite unimodular lattice of rank between two and nine, every vector of
norm two is orthogonal to a nonzero vector of norm at most two.** -/
theorem exists_integralForm_eq_zero_of_integralNorm_eq_two (h2 : 2 ≤ finrank ℤ L)
    (h9 : finrank ℤ L ≤ 9) {r : L} (hr : L.integralNorm r = 2) :
    ∃ s : L, s ≠ 0 ∧ L.integralForm r s = 0 ∧ L.integralNorm s ≤ 2 := by
  obtain ⟨w, hw⟩ := exists_isCoprime_integralForm_two hU (v := r) fun y hy ↦ by
    rw [hy, QuadraticMap.map_smul, smul_eq_mul] at hr
    omega
  -- The vectors pairing evenly with `r` form a sublattice `N` of index two, so of determinant 4.
  let N := L.restrictFull (L.neighborKernel 2 r) (L.neighborKernel_le 2 r)
  have hNL : N.carrier ≤ L.carrier := (restrictFull_carrier ..).trans_le (L.neighborKernel_le 2 r)
  have hNform : N.form = L.form := restrictFull_form ..
  have hdetN : N.determinant = 4 := by
    rw [determinant_eq_mul_relIndex_sq N L hNform hNL, hL.determinant_eq_one_of_isUnimodular hU,
      restrictFull_carrier, L.relIndex_neighborKernel 2 hw]
    norm_num
  have hBN (x y : N) : N.integralForm x y =
      L.integralForm (Submodule.inclusion hNL x) (Submodule.inclusion hNL y) :=
    (integralForm_inclusion N L hNform hNL x y).symm
  have hrr : L.integralForm r r = 2 := by rw [← integralNorm_apply, hr]
  let r' : N := ⟨r, (restrictFull_carrier ..).ge
    (L.coe_mem_neighborKernel_self 2 (by rw [hr]; norm_num))⟩
  have hr' : Submodule.inclusion hNL r' = r := rfl
  have hrr' : N.integralForm r' r' = 2 := by rw [hBN, hr', hrr]
  have hr'0 : r' ≠ 0 := fun h ↦ by simp [h] at hrr'
  -- In `N`, the vector `r` splits off: `N = ℤ r ⊕ T` with `T` its orthogonal complement.
  have hST := N.integralForm.isCompl_span_singleton_orthogonal_of_dvd
    (mem_nonZeroDivisors_of_ne_zero (by rw [hrr']; norm_num)) fun x ↦ by
    rw [hrr', hBN, hr']
    exact (L.coe_mem_neighborKernel_iff 2 r _).1 ((restrictFull_carrier ..).le x.2)
  let T := N.integralForm.orthogonal (ℤ ∙ r')
  have e := N.orthogonalSumIsometryOfIsCompl _ T hST le_rfl
  have eS := N.spanSingletonIsometry r' hr'0
  -- Hence `T` has rank `n - 1` and determinant two.
  have hdetT : (ofIntegralForm _ (N.isSymm_integralForm.restrict T)).determinant = 2 := by
    have h := e.determinant_eq
    rw [determinant_orthogonalSum, ← eS.determinant_eq, determinant_ofGramMatrix,
      Matrix.det_unique, Matrix.of_apply, hrr', hdetN] at h
    omega
  have hrankT : finrank ℤ (ofIntegralForm _ (N.isSymm_integralForm.restrict T)) + 1 =
      finrank ℤ L := by
    have h := e.finrank_carrier_eq
    rw [finrank_orthogonalSum, ← eS.finrank_carrier_eq, finrank_carrier, Module.finrank_self,
      finrank_carrier N, ← finrank_carrier L] at h
    omega
  have hNpos : N.IsPosDef := by rwa [IsPosDef, hNform]
  have hLT := hNpos.isPosDef_ofIntegralForm_restrict T
  have : Nontrivial (ofIntegralForm _ (N.isSymm_integralForm.restrict T)) :=
    Module.nontrivial_of_finrank_pos (R := ℤ) (by omega)
  -- Hermite's inequality in rank `n - 1 ≤ 8` and determinant two bounds the minimum of `T` by two.
  have hlt := hLT.minimum_lt_of_four_pow_mul_lt hdetT.le (k := 3) <| by
    obtain ⟨m, hm⟩ : ∃ m, finrank ℤ (ofIntegralForm _ (N.isSymm_integralForm.restrict T)) = m :=
      ⟨_, rfl⟩
    rw [hm]
    have : m ≤ 8 := by omega
    have : 1 ≤ m := by omega
    interval_cases m <;> norm_num [Nat.choose_two_right]
  obtain ⟨y, hy0, hy⟩ := hLT.isPosSemidef.exists_ne_zero_integralNorm_eq_minimum
  obtain ⟨t, rfl⟩ := (ofIntegralForm.carrierEquiv _ _).surjective y
  rw [integralNorm_apply, ofIntegralForm.integralForm_carrierEquiv,
    LinearMap.BilinForm.restrict_apply, LinearMap.domRestrict_apply, hBN,
    ← integralNorm_apply] at hy
  refine ⟨Submodule.inclusion hNL t, fun ht ↦ hy0 ?_, ?_, by omega⟩
  · have : t = 0 := Subtype.ext (Submodule.inclusion_injective hNL (ht.trans (map_zero _).symm))
    rw [this, LinearEquiv.map_zero]
  · rw [← hr', ← hBN]
    exact t.2 r' (Submodule.mem_span_singleton_self r')

/-- **Two orthogonal vectors of norm two give a neighbor with two orthonormal vectors.** Let `L` be
positive definite and unimodular without vectors of norm one, and `r`, `s` orthogonal of norm two.
The two-neighbor `M` of `L` along `r + s` contains the orthogonal vectors `(r + s) / 2` and
`(r - s) / 2` of norm one, so the complement of its unit-norm sublattice has rank at most
`rank L - 2`. -/
private theorem exists_isNeighbor_finrank_unitNormComplement_add_two_le
    (h1 : L.vectorsOfNorm 1 = ∅) {r s : L} (hr : L.integralNorm r = 2)
    (hs : L.integralNorm s = 2) (hrs : L.integralForm r s = 0) :
    ∃ M : IntegralLattice V, L.IsNeighbor M 2 ∧ M.IsPosDef ∧ M.IsUnimodular ∧
      finrank ℤ M.unitNormComplement + 2 ≤ finrank ℤ L := by
  have h4 : L.integralNorm (r + s) = 4 := by
    rw [integralNorm_add, hr, hs, hrs]
    norm_num
  have hv : (2 : ℤ) ^ 2 ∣ L.integralNorm (r + s) := by
    rw [h4]
    norm_num
  -- `r + s` is not twice a lattice vector, which would have norm one.
  obtain ⟨w, hw⟩ := exists_isCoprime_integralForm_two hU (v := r + s) fun y hy ↦ by
    rw [hy, QuadraticMap.map_smul, smul_eq_mul] at h4
    have hy1 : L.integralForm y y = 1 := by
      rw [← integralNorm_apply]
      omega
    simpa [h1] using (L.mem_vectorsOfNorm_one_iff (x := y)).2 hy1
  set M := L.neighbor 2 (r + s) hv
  have hN : L.IsNeighbor M 2 := isNeighbor_neighbor hv hw
  have hM : M.IsPosDef := (isPosDef_neighbor_iff hv).2 hL
  refine ⟨M, hN, hM, hN.isUnimodular hU, ?_⟩
  -- The rational form of `M` is that of `L`.
  have hrq : L.form r r = 2 := by rw [← integralForm_cast, ← integralNorm_apply, hr]; norm_num
  have hsq : L.form s s = 2 := by rw [← integralForm_cast, ← integralNorm_apply, hs]; norm_num
  have hrsq : L.form r s = 0 := by rw [← integralForm_cast, hrs]; norm_num
  have hsrq : L.form s r = 0 := by rw [L.isSymm.eq, hrsq]
  have hsM : (s : V) ∈ M.carrier := neighborKernel_le_neighbor_carrier hv <|
    (L.coe_mem_neighborKernel_iff 2 (r + s) s).2 ⟨1, by
      rw [map_add, LinearMap.add_apply, hrs, ← integralNorm_apply, hs]; norm_num⟩
  let u₁ : M := ⟨(2 : ℚ)⁻¹ • ((r + s : L) : V), inv_smul_mem_neighbor_carrier hv⟩
  let u₂ : M := u₁ - ⟨s, hsM⟩
  have hform (x y : M) : (M.integralForm x y : ℚ) = L.form x y := by
    rw [integralForm_cast, neighbor_form]
  have h11 : M.integralForm u₁ u₁ = 1 := by
    apply Int.cast_injective (α := ℚ)
    rw [hform]
    simp [u₁, hrq, hsq, hrsq, hsrq]
    norm_num
  have h22 : M.integralForm u₂ u₂ = 1 := by
    apply Int.cast_injective (α := ℚ)
    rw [hform]
    simp [u₂, u₁, hrq, hsq, hrsq, hsrq]
    norm_num
  have h12 : M.integralForm u₁ u₂ = 0 := by
    apply Int.cast_injective (α := ℚ)
    rw [hform]
    simp [u₂, u₁, hrq, hsq, hrsq, hsrq]
    norm_num
  have hk := M.two_le_finrank_unitNormSubmodule h11 h22 h12
  have hsum := hM.finrank_unitNormSubmodule_add_finrank_unitNormComplement
  rw [finrank_carrier M, ← finrank_carrier L] at hsum
  omega

/-- A nonzero positive definite unimodular lattice of rank at most nine without vectors of norm
one has a two-neighbor `M`, positive definite and unimodular, for which the complement of the
unit-norm sublattice has rank at most `rank L - 2`. -/
private theorem exists_isNeighbor_of_vectorsOfNorm_one_eq_empty [Nontrivial L]
    (h1 : L.vectorsOfNorm 1 = ∅) (hn : finrank ℤ L ≤ 9) :
    ∃ M : IntegralLattice V, L.IsNeighbor M 2 ∧ M.IsPosDef ∧ M.IsUnimodular ∧
      finrank ℤ M.unitNormComplement + 2 ≤ finrank ℤ L := by
  have h6 := hL.six_le_finrank_of_vectorsOfNorm_one_eq_empty hU h1
  obtain ⟨r, hr⟩ := hL.exists_integralNorm_eq_two_of_isUnimodular hU (by omega) hn
  obtain ⟨s, hs0, hrs, hs⟩ :=
    hL.exists_integralForm_eq_zero_of_integralNorm_eq_two hU (by omega) hn hr
  have hs1 : L.integralNorm s ≠ 1 := fun h ↦ by
    simpa [h1] using (L.mem_vectorsOfNorm_one_iff (x := s)).2 (by rwa [← integralNorm_apply])
  have hpos := hL.posDef_integralNorm s hs0
  exact hL.exists_isNeighbor_finrank_unitNormComplement_add_two_le hU h1 hr (by omega) hrs

/-- **A positive definite unimodular lattice of rank at most seven without vectors of norm one is
zero.** -/
theorem subsingleton_of_vectorsOfNorm_one_eq_empty_of_finrank_le_seven
    (h1 : L.vectorsOfNorm 1 = ∅) (hn : finrank ℤ L ≤ 7) : Subsingleton L := by
  by_contra hns
  have : Nontrivial L := not_subsingleton_iff_nontrivial.1 hns
  have h6 := hL.six_le_finrank_of_vectorsOfNorm_one_eq_empty hU h1
  obtain ⟨M, hN, hM, hMU, hrank⟩ := hL.exists_isNeighbor_of_vectorsOfNorm_one_eq_empty hU h1
    (by omega)
  -- The complement of the unit-norm sublattice of `M` has rank at most five, so it is zero.
  have hsub : Subsingleton M.unitNormComplement := by
    by_contra hns'
    have : Nontrivial M.unitNormComplement := not_subsingleton_iff_nontrivial.1 hns'
    have := hM.isPosDef_unitNormComplement.six_le_finrank_of_vectorsOfNorm_one_eq_empty
      (hM.isUnimodular_unitNormComplement_iff.2 hMU) M.vectorsOfNorm_one_unitNormComplement
    omega
  obtain ⟨e⟩ := hM.nonempty_isometry_unitLattice_of_unitNormSubmodule_eq_top
    (hM.unitNormSubmodule_eq_top_iff.2 hsub)
  have h4 := four_dvd_of_isNeighbor_of_isometry_unitLattice e hN h1
  rw [finrank_carrier M, ← finrank_carrier L] at h4
  omega

/-- **A nonzero positive definite unimodular lattice of rank at most nine without vectors of norm
one is `E₈`.** -/
theorem nonempty_isometry_typeE₈RootLattice_of_vectorsOfNorm_one_eq_empty [Nontrivial L]
    (h1 : L.vectorsOfNorm 1 = ∅) (hn : finrank ℤ L ≤ 9) :
    Nonempty (Isometry typeE₈RootLattice L) := by
  have h6 := hL.six_le_finrank_of_vectorsOfNorm_one_eq_empty hU h1
  obtain ⟨M, hN, hM, hMU, hrank⟩ := hL.exists_isNeighbor_of_vectorsOfNorm_one_eq_empty hU h1 hn
  -- The complement of the unit-norm sublattice of `M` has rank at most seven, so it is zero.
  have hsub : Subsingleton M.unitNormComplement :=
    hM.isPosDef_unitNormComplement.subsingleton_of_vectorsOfNorm_one_eq_empty_of_finrank_le_seven
      (hM.isUnimodular_unitNormComplement_iff.2 hMU) M.vectorsOfNorm_one_unitNormComplement
      (by omega)
  obtain ⟨e⟩ := hM.nonempty_isometry_unitLattice_of_unitNormSubmodule_eq_top
    (hM.unitNormSubmodule_eq_top_iff.2 hsub)
  have h4 := four_dvd_of_isNeighbor_of_isometry_unitLattice e hN h1
  have h8 : finrank ℤ M = 8 := by
    rw [finrank_carrier M, ← finrank_carrier L] at h4 ⊢
    omega
  rw [h8] at e
  exact nonempty_isometry_typeE₈RootLattice_of_isNeighbor_of_isometry_unitLattice e hN h1

/-- **Positive definite unimodular lattices of rank at most nine.** Such a lattice is the
standard lattice `Iₙ`, the root lattice `E₈`, or `I₁ ⊕ E₈`. -/
theorem nonempty_isometry_of_isUnimodular_of_finrank_le_nine (hn : finrank ℤ L ≤ 9) :
    Nonempty (Isometry (unitLattice (Fin (finrank ℤ L))) L) ∨
      Nonempty (Isometry typeE₈RootLattice L) ∨
      Nonempty (Isometry ((unitLattice (Fin 1)).orthogonalSum typeE₈RootLattice) L) := by
  rcases subsingleton_or_nontrivial L.unitNormComplement with h0 | h0
  · exact Or.inl (hL.nonempty_isometry_unitLattice_of_unitNormSubmodule_eq_top
      (hL.unitNormSubmodule_eq_top_iff.2 h0))
  have hrank := hL.finrank_unitNormSubmodule_add_finrank_unitNormComplement
  obtain ⟨e₀⟩ :=
    hL.isPosDef_unitNormComplement.nonempty_isometry_typeE₈RootLattice_of_vectorsOfNorm_one_eq_empty
      (hL.isUnimodular_unitNormComplement_iff.2 hU) L.vectorsOfNorm_one_unitNormComplement
      (by omega)
  have h8 : finrank ℤ L.unitNormComplement = 8 := by
    rw [← e₀.finrank_carrier_eq, finrank_carrier, Module.finrank_fin_fun]
  obtain hk | hk : finrank ℤ L.unitNormSubmodule = 0 ∨ finrank ℤ L.unitNormSubmodule = 1 := by
    omega
  · -- Without vectors of norm one, `L` itself is `E₈`.
    have h1 : L.vectorsOfNorm 1 = ∅ := by
      have h := hL.two_mul_finrank_unitNormSubmodule
      rw [hk, mul_zero, eq_comm, Set.ncard_eq_zero (hL.finite_vectorsOfNorm 1)] at h
      exact h
    have : Nontrivial L := Module.nontrivial_of_finrank_pos (R := ℤ) (by omega)
    exact Or.inr (Or.inl (hL.nonempty_isometry_typeE₈RootLattice_of_vectorsOfNorm_one_eq_empty
      hU h1 hn))
  · have d := hL.unitNormDecomposition
    rw [hk] at d
    exact Or.inr (Or.inr ⟨((Isometry.refl _).orthogonalSum e₀).trans d⟩)

/-- **`E₈` is the unique even unimodular positive definite lattice of rank eight.** -/
theorem nonempty_isometry_typeE₈RootLattice_of_isEven (he : L.IsEven)
    (hn : finrank ℤ L = 8) : Nonempty (Isometry typeE₈RootLattice L) := by
  have : Nontrivial L := Module.nontrivial_of_finrank_pos (R := ℤ) (by omega)
  exact hL.nonempty_isometry_typeE₈RootLattice_of_vectorsOfNorm_one_eq_empty hU
    (by exact_mod_cast IsEven.vectorsOfNorm_eq_empty_of_not_even L he (n := 1) (by decide))
    (by omega)

end IsPosDef

end TauCeti.IntegralLattice
