/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.IntegralLattice.Localization.Discriminant.Form
import Mathlib.NumberTheory.LegendreSymbol.Basic
import TauCeti.Data.Fintype.Fiber
import TauCeti.LinearAlgebra.BilinearForm.Diagonalization
import TauCeti.LinearAlgebra.FiniteBilinearModule.Comparison
import TauCeti.LinearAlgebra.FiniteBilinearModule.OddCyclic.PiClassification
import TauCeti.LinearAlgebra.QuadraticForm.Diagonal.Henselian
import TauCeti.NumberTheory.IntegralLattice.Diagonalization
import TauCeti.NumberTheory.IntegralLattice.Localization.Discriminant.Diagonal
import TauCeti.NumberTheory.IntegralLattice.Localization.Unimodular
import TauCeti.NumberTheory.Padics.PadicIntegers
import TauCeti.NumberTheory.Padics.RingHoms
import TauCeti.RingTheory.Henselian.SquareClasses

/-!
# Classification of odd-prime localizations by their discriminant forms

Let `L` and `M` be nondegenerate integral lattices and `p` an odd prime. An integral isometry
`L_p ≃ M_p` of their `p`-adic localizations preserves the rank, the `p`-adic square class of the
signed determinant, and the `p`-primary component of the discriminant bilinear form `b_L`
(`TauCeti.IntegralLattice.localIntegralForm_equivalent_imp` and
`TauCeti.IntegralLattice.primaryDiscriminantBilinearIsometry`). This file proves the converse:
at an odd prime, these three invariants classify the integral localization up to isometry.

In diagonal Jordan coordinates `B(bᵢ, bᵢ) = uᵢ pᵏⁱ` on `L_p` and `B(b'ⱼ, b'ⱼ) = vⱼ pˡʲ` on `M_p`,
the `p`-primary discriminant forms are isometric to the orthogonal sums of odd cyclic generators
`⊕ᵢ q_{θᵢ}^{(p)}(pᵏⁱ)` and `⊕ⱼ q_{ηⱼ}^{(p)}(pˡʲ)` for integer truncations `θᵢ ≡ uᵢ` and
`ηⱼ ≡ vⱼ` modulo `p^{kᵢ + 1}` and `p^{lⱼ + 1}`
(`TauCeti.IntegralLattice.nonempty_isometry_pi_oddCyclic_primaryComponent`). On a group of odd
prime-power order, bilinear isometry and quadratic isometry coincide
(`TauCeti.FiniteQuadraticModule.nonempty_isometry_iff_bilinear_isometry_of_odd`), so the odd-cyclic
classification (`TauCeti.FiniteQuadraticModule.nonempty_isometry_pi_oddCyclic_iff`) equates the
numbers of summands and the level products of Legendre symbols `(θᵢ/p)` for every positive exponent
`m ≥ 1`. Equal total ranks then force the unimodular (`m = 0`) constituent ranks and total
valuations `∑ kᵢ = ∑ lⱼ` to agree as well, after which the determinant square-class condition
recovers the remaining `m = 0` Legendre product. Hensel's lemma lifts each fiberwise Legendre
equality to a square-class equality of unit products in `ℤ_p`, and the fiberwise diagonal
classification (`TauCeti.equivalent_weightedSumSquares_mul_of_forall_isSquare_prod_mul_prod`)
produces the desired local integral isometry.

## Main results

* `TauCeti.IntegralLattice.localIntegralForm_equivalent_iff_of_ne_two`: for nondegenerate lattices
  and an odd prime `p`, the localizations `L_p` and `M_p` are isometric if and only if `L` and `M`
  have the same rank, `(det L) * (det M)` is a square in `ℤ_p`, and the `p`-primary components of
  `b_L` and `b_M` are isometric.
* `TauCeti.IntegralLattice.localIntegralForm_equivalent_iff_of_isEven`: the corresponding statement
  for even lattices in terms of the `p`-primary components of the discriminant quadratic forms
  `q_L` and `q_M`.
* `TauCeti.IntegralLattice.localIntegralForm_equivalent_of_determinant_eq`: when `L` and `M` have
  equal rank and equal signed determinant, isometry of the `p`-primary discriminant bilinear forms
  suffices for local integral isometry at every odd prime `p`.

## References

* V. V. Nikulin, *Integral symmetric bilinear forms and some of their applications*, Proposition
  1.9.2 and §§1.8–1.9, 1.16.
* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, Chapter 15, §7.
* O. T. O'Meara, *Introduction to Quadratic Forms*, §92.
-/

public section

open Module AddCommGroup Finset Function

namespace TauCeti.IntegralLattice

variable {V W : Type*} [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]

section Arithmetic

variable {p : ℕ} [Fact p.Prime]

/-- At an odd prime, a `p`-adic unit is a square in `ℤ_p` if and only if its reduction modulo `p`
is a square in `ℤ/pℤ`. -/
private theorem isSquare_padicInt_iff_toZMod (hp : p ≠ 2) {a : ℤ_[p]} (ha : IsUnit a) :
    IsSquare a ↔ IsSquare (PadicInt.toZMod a) := by
  rw [HenselianLocalRing.isSquare_iff_residue_isSquare (PadicInt.isUnit_two hp) ha,
    PadicInt.toZMod_eq_residueField_comp_residue, RingHom.comp_apply]
  exact ⟨fun h ↦ h.map PadicInt.residueField.toRingHom.toMonoidHom, fun h ↦ by
    simpa using h.map PadicInt.residueField.symm.toRingHom.toMonoidHom⟩

/-- An integer congruent modulo `p` to a `p`-adic unit reduces to the same unit in `ℤ/pℤ` and is
coprime to `p`. -/
private theorem toZMod_eq_intCast_and_isCoprime {u : ℤ_[p]ˣ} {θ : ℤ}
    (h : (p : ℤ_[p]) ∣ (u : ℤ_[p]) - θ) :
    PadicInt.toZMod (u : ℤ_[p]) = (θ : ZMod p) ∧ IsCoprime (p : ℤ) θ := by
  have hmod : PadicInt.toZMod (u : ℤ_[p]) = (θ : ZMod p) := by
    have h0 := (PadicInt.toZMod_eq_zero_iff_dvd _).mpr h
    rw [map_sub, map_intCast, sub_eq_zero] at h0
    exact h0
  have hunit : IsUnit (θ : ZMod p) := hmod ▸ u.isUnit.map PadicInt.toZMod
  exact ⟨hmod, (ZMod.isUnit_intCast_iff_isCoprime θ p).mp hunit⟩

/-- At an odd prime, the product of two finite products of `p`-adic units is a square in `ℤ_p` if
and only if the corresponding products of Legendre symbols of congruent integers agree. -/
private theorem isSquare_prod_mul_prod_iff_prod_legendreSym_eq {ι κ : Type*} (hp : p ≠ 2)
    (s : Finset ι) (t : Finset κ) {u : ι → ℤ_[p]ˣ} {v : κ → ℤ_[p]ˣ} {θ : ι → ℤ} {η : κ → ℤ}
    (hθ : ∀ i ∈ s, (p : ℤ_[p]) ∣ (u i : ℤ_[p]) - θ i)
    (hη : ∀ j ∈ t, (p : ℤ_[p]) ∣ (v j : ℤ_[p]) - η j) :
    IsSquare ((∏ i ∈ s, (u i : ℤ_[p])) * ∏ j ∈ t, (v j : ℤ_[p])) ↔
      ∏ i ∈ s, legendreSym p (θ i) = ∏ j ∈ t, legendreSym p (η j) := by
  have hunit : IsUnit ((∏ i ∈ s, (u i : ℤ_[p])) * ∏ j ∈ t, (v j : ℤ_[p])) := by
    rw [← Units.coe_prod, ← Units.coe_prod, ← Units.val_mul]
    exact Units.isUnit _
  have hres : PadicInt.toZMod ((∏ i ∈ s, (u i : ℤ_[p])) * ∏ j ∈ t, (v j : ℤ_[p])) =
      (((∏ i ∈ s, θ i) * ∏ j ∈ t, η j : ℤ) : ZMod p) := by
    simp only [map_mul, map_prod, Int.cast_mul, Int.cast_prod]
    exact congrArg₂ (· * ·)
      (Finset.prod_congr rfl fun i hi ↦ (toZMod_eq_intCast_and_isCoprime (hθ i hi)).1)
      (Finset.prod_congr rfl fun j hj ↦ (toZMod_eq_intCast_and_isCoprime (hη j hj)).1)
  have hne : (((∏ i ∈ s, θ i) * ∏ j ∈ t, η j : ℤ) : ZMod p) ≠ 0 :=
    hres ▸ (hunit.map PadicInt.toZMod).ne_zero
  have hleg : legendreSym p ((∏ i ∈ s, θ i) * ∏ j ∈ t, η j) =
      (∏ i ∈ s, legendreSym p (θ i)) * ∏ j ∈ t, legendreSym p (η j) := by
    simpa only [legendreSym.hom_apply] using
      map_mul (legendreSym.hom p) (∏ i ∈ s, θ i) (∏ j ∈ t, η j) |>.trans <|
        congrArg₂ (· * ·) (map_prod (legendreSym.hom p) θ s) (map_prod (legendreSym.hom p) η t)
  have hsq : (∏ j ∈ t, legendreSym p (η j)) ^ 2 = 1 := by
    rw [← Finset.prod_pow]
    refine Finset.prod_eq_one fun j hj ↦ legendreSym.sq_one p ?_
    exact ((ZMod.isUnit_intCast_iff_isCoprime (η j) p).mpr
      (toZMod_eq_intCast_and_isCoprime (hη j hj)).2).ne_zero
  rw [isSquare_padicInt_iff_toZMod hp hunit, hres, ← quadraticChar_one_iff_isSquare hne]
  -- `legendreSym p a` is definitionally `quadraticChar (ZMod p) (a : ZMod p)`.
  change legendreSym p ((∏ i ∈ s, θ i) * ∏ j ∈ t, η j) = 1 ↔ _
  rw [hleg]
  exact ⟨fun h ↦ by linear_combination (∏ j ∈ t, legendreSym p (η j)) * h -
      (∏ i ∈ s, legendreSym p (θ i)) * hsq,
    fun h ↦ by rw [h, ← sq, hsq]⟩

end Arithmetic

section Combinatorics

/-- Two families `k, l : Fin n → ℕ` whose fiber cardinalities agree at every positive value also
agree at `0`, have the same sum, and differ by a permutation of `Fin n`. -/
private theorem occCount_eq_and_sum_eq_and_exists_perm {n : ℕ} {k l : Fin n → ℕ}
    (hcard : ∀ m, 0 < m → #{i | k i = m} = #{j | l j = m}) :
    (∀ m, occCount k m = occCount l m) ∧ ∑ i, k i = ∑ j, l j ∧
      ∃ σ : Equiv.Perm (Fin n), l ∘ σ = k := by
  let T : Finset ℕ := insert 0 (Finset.univ.image k ∪ Finset.univ.image l)
  have hTk (i : Fin n) : k i ∈ T :=
    mem_insert_of_mem (mem_union_left _ (mem_image_of_mem k (mem_univ i)))
  have hTl (j : Fin n) : l j ∈ T :=
    mem_insert_of_mem (mem_union_right _ (mem_image_of_mem l (mem_univ j)))
  have hpos {m : ℕ} (hm : m ≠ 0) : occCount k m = occCount l m := by
    rw [occCount_eq_card_filter, occCount_eq_card_filter]
    exact hcard m (Nat.pos_of_ne_zero hm)
  have h0 : occCount k 0 = occCount l 0 := by
    have hk := sum_occCount_eq_card k hTk
    have hl := sum_occCount_eq_card l hTl
    rw [← add_sum_erase T _ (mem_insert_self 0 _)] at hk hl
    have herase : ∑ m ∈ T.erase 0, occCount k m = ∑ m ∈ T.erase 0, occCount l m :=
      Finset.sum_congr rfl fun m hm ↦ hpos (ne_of_mem_erase hm)
    omega
  have hall (m : ℕ) : occCount k m = occCount l m := by
    rcases eq_or_ne m 0 with rfl | hm
    · exact h0
    · exact hpos hm
  have hsum : ∑ i, k i = ∑ j, l j := by
    rw [← sum_occCount_nsmul k hTk (fun m ↦ m), ← sum_occCount_nsmul l hTl (fun m ↦ m)]
    exact Finset.sum_congr rfl fun m _ ↦ by rw [hall m]
  exact ⟨hall, hsum, exists_perm_of_occCount_eq hall⟩

/-- If the total products of nonzero integer weights on `Fin n` agree and the fiber products agree
at every positive level, then the fiber products agree at level `0` as well. -/
private theorem prod_filter_eq_zero_of_prod_eq {n : ℕ} (k l : Fin n → ℕ) {f g : Fin n → ℤ}
    (hg : ∀ j, g j ≠ 0) (htot : ∏ i, f i = ∏ j, g j)
    (hpos : ∀ m, 0 < m → ∏ i with k i = m, f i = ∏ j with l j = m, g j) :
    ∏ i with k i = 0, f i = ∏ j with l j = 0, g j := by
  let T : Finset ℕ := insert 0 (Finset.univ.image k ∪ Finset.univ.image l)
  have hfk : (∏ m ∈ T, ∏ i with k i = m, f i) = ∏ i, f i :=
    Finset.prod_fiberwise_of_maps_to
      (fun i _ ↦ mem_insert_of_mem (mem_union_left _ (mem_image_of_mem k (mem_univ i)))) f
  have hfl : (∏ m ∈ T, ∏ j with l j = m, g j) = ∏ j, g j :=
    Finset.prod_fiberwise_of_maps_to
      (fun j _ ↦ mem_insert_of_mem (mem_union_right _ (mem_image_of_mem l (mem_univ j)))) g
  rw [← mul_prod_erase T _ (mem_insert_self 0 _)] at hfk hfl
  have herase : (∏ m ∈ T.erase 0, ∏ i with k i = m, f i) =
      ∏ m ∈ T.erase 0, ∏ j with l j = m, g j :=
    Finset.prod_congr rfl fun m hm ↦ hpos m (Nat.pos_of_ne_zero (ne_of_mem_erase hm))
  have hne : (∏ m ∈ T.erase 0, ∏ j with l j = m, g j) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun m _ ↦ Finset.prod_ne_zero_iff.mpr fun j _ ↦ hg j
  rw [herase] at hfk
  exact mul_right_cancel₀ hne (hfk.trans (htot.trans hfl.symm))

end Combinatorics

section Classification

variable {L : IntegralLattice V} {M : IntegralLattice W} {p : ℕ} [Fact p.Prime]

/-- In a diagonal Jordan basis `B(bᵢ, bᵢ) = uᵢ pᵏⁱ` indexed by `Fin n` (for `n = finrank ℤ L`),
the signed determinant of `L` differs from `(∏ uᵢ) p^{∑ kᵢ}` by the square of a `p`-adic unit. -/
private theorem exists_unit_sq_mul_determinant_eq {n : ℕ} (hn : finrank ℤ L = n)
    {b : Basis (Fin n) ℤ_[p] (L.LocalCarrier p)} {u : Fin n → ℤ_[p]ˣ} {k : Fin n → ℕ}
    (hb : (L.localIntegralForm p).iIsOrtho b)
    (hbu : ∀ i, L.localIntegralForm p (b i) (b i) = u i * (p : ℤ_[p]) ^ k i) :
    ∃ w : ℤ_[p]ˣ, (L.determinant : ℤ_[p]) =
      (w : ℤ_[p]) ^ 2 * ((∏ i, (u i : ℤ_[p])) * (p : ℤ_[p]) ^ ∑ i, k i) := by
  classical
  let c0 := (Module.finBasis ℤ L).reindex (finCongr hn)
  let e0 := c0.baseChange ℤ_[p]
  have hunit : IsUnit (b.toMatrix e0).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp (@isUnit_of_invertible _ _ _ (b.invertibleToMatrix e0))
  refine ⟨hunit.unit, ?_⟩
  rw [← L.det_toMatrix_localIntegralForm p c0,
    LinearMap.BilinForm.det_toMatrix_eq_det_sq_mul_det b e0, IsUnit.unit_spec, hb.det_toMatrix]
  congr 1
  simp_rw [hbu, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]

/-- Diagonal Jordan decomposition of `L_p` reindexed by `Fin n` (`finrank ℤ L = n`), together with
integer approximations modulo `p ^ (kᵢ + 1)`. -/
private theorem exists_jordan_data [L.IsNondegenerate] {n : ℕ} (hn : finrank ℤ L = n)
    (hp : p ≠ 2) :
    ∃ (b : Basis (Fin n) ℤ_[p] (L.LocalCarrier p))
      (u : Fin n → ℤ_[p]ˣ) (k : Fin n → ℕ) (θ : Fin n → ℤ),
      (L.localIntegralForm p).iIsOrtho b ∧
        (∀ i, L.localIntegralForm p (b i) (b i) = u i * (p : ℤ_[p]) ^ k i) ∧
        (∀ i, (p : ℤ_[p]) ^ k i ∣ (u i : ℤ_[p]) - θ i) ∧
        (∀ i, (p : ℤ_[p]) ∣ (u i : ℤ_[p]) - θ i) := by
  obtain ⟨b0, u0, k0, hb0, hbu0⟩ :=
    L.exists_basis_iIsOrtho_localIntegralForm_eq_unit_mul_pow hp L.form_nondegenerate
  have hdim : finrank ℤ_[p] (L.LocalCarrier p) = n := by
    rw [Module.finrank_eq_card_basis ((Module.finBasis ℤ L).baseChange ℤ_[p]), Fintype.card_fin, hn]
  let e := finCongr hdim
  let b := b0.reindex e
  let u := fun i ↦ u0 (e.symm i)
  let k := fun i ↦ k0 (e.symm i)
  let θ : Fin n → ℤ := fun i ↦ ((u i : ℤ_[p]).appr (k i + 1) : ℤ)
  have hdiv (i : Fin n) : (p : ℤ_[p]) ^ (k i + 1) ∣ (u i : ℤ_[p]) - θ i := by
    simp [θ]
  refine ⟨b, u, k, θ, ?_, fun i ↦ ?_,
    fun i ↦ (pow_dvd_pow _ (Nat.le_succ _)).trans (hdiv i),
    fun i ↦ (dvd_pow_self _ (Nat.succ_ne_zero _)).trans (hdiv i)⟩
  · intro i j hij
    simpa only [Function.onFun, b, Module.Basis.reindex_apply] using hb0 (e.symm.injective.ne hij)
  · simp [b, u, k, hbu0]

/-- At an odd prime, the `p`-primary discriminant group of a nondegenerate lattice has odd order. -/
private theorem odd_natCard_primaryComponent_discriminantGroup [L.IsNondegenerate] (hp : p ≠ 2) :
    Odd (Nat.card (primaryComponent L.DiscriminantGroup p)) := by
  rw [AddCommGroup.natCard_primaryComponent _ Fact.out]
  exact ((Fact.out : p.Prime).odd_of_ne_two hp).pow

/-- When `∑ kᵢ = ∑ lⱼ` and `(det L) * (det M)` is a `p`-adic square, cancelling the unit-square and
even-`p`-power factors yields a square-class relation on the total unit products. -/
private theorem isSquare_prod_mul_prod_of_determinant_isSquare
    {n : ℕ} (hnL : finrank ℤ L = n) (hnM : finrank ℤ M = n)
    {b : Basis (Fin n) ℤ_[p] (L.LocalCarrier p)} {u : Fin n → ℤ_[p]ˣ} {k : Fin n → ℕ}
    (hb : (L.localIntegralForm p).iIsOrtho b)
    (hbu : ∀ i, L.localIntegralForm p (b i) (b i) = u i * (p : ℤ_[p]) ^ k i)
    {b' : Basis (Fin n) ℤ_[p] (M.LocalCarrier p)} {v : Fin n → ℤ_[p]ˣ} {l : Fin n → ℕ}
    (hb' : (M.localIntegralForm p).iIsOrtho b')
    (hbv : ∀ j, M.localIntegralForm p (b' j) (b' j) = v j * (p : ℤ_[p]) ^ l j)
    (hsum : ∑ i, k i = ∑ j, l j)
    (hdet : IsSquare ((L.determinant : ℤ_[p]) * (M.determinant : ℤ_[p]))) :
    IsSquare ((∏ i, (u i : ℤ_[p])) * ∏ j, (v j : ℤ_[p])) := by
  obtain ⟨wL, hwL⟩ := L.exists_unit_sq_mul_determinant_eq hnL hb hbu
  obtain ⟨wM, hwM⟩ := M.exists_unit_sq_mul_determinant_eq hnM hb' hbv
  rw [hwL, hwM, ← hsum] at hdet
  have hp0 : (p : ℤ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  refine IsSquare.of_mul_right
    (y := ((wL : ℤ_[p]) * wM * (p : ℤ_[p]) ^ ∑ i, k i) ^ 2)
    (pow_ne_zero 2 (mul_ne_zero (mul_ne_zero wL.ne_zero wM.ne_zero) (pow_ne_zero _ hp0)))
    ?_ (IsSquare.sq _)
  convert hdet using 1
  ring

/-- Given diagonal Jordan bases of `L_p` and `M_p` with matching positive-level Legendre data and
square determinant product, the localized integral forms are isometric. -/
private theorem localIntegralForm_equivalent_of_jordan_data (hp : p ≠ 2)
    {n : ℕ} (hnL : finrank ℤ L = n) (hnM : finrank ℤ M = n)
    {b : Basis (Fin n) ℤ_[p] (L.LocalCarrier p)} {u : Fin n → ℤ_[p]ˣ} {k : Fin n → ℕ}
    {θ : Fin n → ℤ} (hb : (L.localIntegralForm p).iIsOrtho b)
    (hbu : ∀ i, L.localIntegralForm p (b i) (b i) = u i * (p : ℤ_[p]) ^ k i)
    (hθ1 : ∀ i, (p : ℤ_[p]) ∣ (u i : ℤ_[p]) - θ i)
    {b' : Basis (Fin n) ℤ_[p] (M.LocalCarrier p)} {v : Fin n → ℤ_[p]ˣ} {l : Fin n → ℕ}
    {η : Fin n → ℤ} (hb' : (M.localIntegralForm p).iIsOrtho b')
    (hbv : ∀ j, M.localIntegralForm p (b' j) (b' j) = v j * (p : ℤ_[p]) ^ l j)
    (hη1 : ∀ j, (p : ℤ_[p]) ∣ (v j : ℤ_[p]) - η j)
    (hdet : IsSquare ((L.determinant : ℤ_[p]) * (M.determinant : ℤ_[p])))
    (hpi : ∀ m, 0 < m → #{i | k i = m} = #{j | l j = m} ∧
      ∏ i with k i = m, legendreSym p (θ i) = ∏ j with l j = m, legendreSym p (η j)) :
    (L.localIntegralForm p).Equivalent (M.localIntegralForm p) := by
  obtain ⟨_, hsum, ⟨σ, hσ⟩⟩ := occCount_eq_and_sum_eq_and_exists_perm fun m hm ↦ (hpi m hm).1
  have hσi (i : Fin n) : l (σ i) = k i := congrFun hσ i
  have hunitSq := isSquare_prod_mul_prod_of_determinant_isSquare hnL hnM hb hbu hb' hbv hsum hdet
  have htot := (isSquare_prod_mul_prod_iff_prod_legendreSym_eq hp univ univ
    (fun i _ ↦ hθ1 i) (fun j _ ↦ hη1 j)).mp hunitSq
  have hηne (j : Fin n) : legendreSym p (η j) ≠ 0 := by
    intro h0
    exact ((ZMod.isUnit_intCast_iff_isCoprime (η j) p).mpr
      (toZMod_eq_intCast_and_isCoprime (hη1 j)).2).ne_zero ((legendreSym.eq_zero_iff p _).mp h0)
  have h0 := prod_filter_eq_zero_of_prod_eq k l hηne htot fun m hm ↦ (hpi m hm).2
  have hall (m : ℕ) :
      ∏ i with k i = m, legendreSym p (θ i) = ∏ i with k i = m, legendreSym p (η (σ i)) := by
    have hm : ∏ i with k i = m, legendreSym p (θ i) = ∏ j with l j = m, legendreSym p (η j) := by
      rcases Nat.eq_zero_or_pos m with rfl | hm
      · exact h0
      · exact (hpi m hm).2
    rw [hm, Finset.prod_filter, Finset.prod_filter, ← Equiv.prod_comp (σ : Fin n ≃ Fin n)]
    exact Finset.prod_congr rfl fun i _ ↦ by simp [hσi i]
  have hfib (m : ℕ) :
      IsSquare ((∏ i with k i = m, u i) * ∏ i with k i = m, v (σ i)) := by
    rw [← Units.isSquare_coe_iff, Units.val_mul, Units.coe_prod, Units.coe_prod]
    exact (isSquare_prod_mul_prod_iff_prod_legendreSym_eq hp _ _
      (fun i _ ↦ hθ1 i) (fun i _ ↦ hη1 (σ i))).mpr (hall m)
  -- Reindex `b'` by `σ⁻¹` so its `i`-th basis vector is `b' (σ i)` with exponent `l (σ i) = k i`.
  let b'' := b'.reindex σ.symm
  have hb'' : (M.localIntegralForm p).iIsOrtho b'' := fun i j hij ↦ by
    simpa only [Function.onFun, b'', Module.Basis.reindex_apply, Equiv.symm_symm] using
      hb' (σ.injective.ne hij)
  have hbv'' (i : Fin n) :
      M.localIntegralForm p (b'' i) (b'' i) = (v (σ i) : ℤ_[p]) * (p : ℤ_[p]) ^ k i := by
    simp [b'', hbv, hσi i]
  let _ : Invertible (2 : ℤ_[p]) := (PadicInt.isUnit_two hp).invertible
  rw [(L.isSymm_localIntegralForm p).equivalent_iff_toQuadraticMap_equivalent
    (M.isSymm_localIntegralForm p)]
  have eQ := equivalent_weightedSumSquares_mul_of_forall_isSquare_prod_mul_prod
    (PadicInt.isUnit_two hp) k (fun m : ℕ ↦ (p : ℤ_[p]) ^ m) u (fun i ↦ v (σ i)) hfib
  have eL := hb.equivalent_weightedSumSquares
  have eM := hb''.equivalent_weightedSumSquares
  simp_rw [hbu] at eL
  simp_rw [hbv''] at eM
  exact eL.trans (eQ.trans eM.symm)

/-- **Odd-prime local classification by the discriminant bilinear form.** Let `L` and `M` be
nondegenerate integral lattices and `p` an odd prime. Their `p`-adic integral localizations `L_p`
and `M_p` are isometric if and only if `L` and `M` have the same rank, `(det L) * (det M)` is a
square in `ℤ_p`, and the `p`-primary components of their discriminant bilinear modules are
isometric. -/
theorem localIntegralForm_equivalent_iff_of_ne_two
    [L.IsNondegenerate] [M.IsNondegenerate] (hp : p ≠ 2) :
    (L.localIntegralForm p).Equivalent (M.localIntegralForm p) ↔
      finrank ℤ L = finrank ℤ M ∧
        IsSquare ((L.determinant : ℤ_[p]) * (M.determinant : ℤ_[p])) ∧
        Nonempty (FiniteBilinearModule.Isometry
          (L.discriminantBilinearModule.restrict
            (primaryComponent L.discriminantBilinearModule p))
          (M.discriminantBilinearModule.restrict
            (primaryComponent M.discriminantBilinearModule p))) := by
  constructor
  · intro h
    obtain ⟨hrank, hdet⟩ := L.localIntegralForm_equivalent_imp M p h
    exact ⟨hrank, hdet, h.map primaryDiscriminantBilinearIsometry⟩
  · rintro ⟨hrank, hdet, ⟨f⟩⟩
    have hpodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp
    obtain ⟨b, u, k, θ, hb, hbu, hθk, hθ1⟩ := L.exists_jordan_data rfl hp
    obtain ⟨b', v, l, η, hb', hbv, hηl, hη1⟩ := M.exists_jordan_data hrank.symm hp
    obtain ⟨eL⟩ := nonempty_isometry_pi_oddCyclic_primaryComponent hpodd hb hbu hθk
    obtain ⟨eM⟩ := nonempty_isometry_pi_oddCyclic_primaryComponent hpodd hb' hbv hηl
    have hoddQ : Odd (Nat.card (FiniteQuadraticModule.pi fun i ↦
        FiniteQuadraticModule.oddCyclic (p ^ k i) hpodd.pow (θ i))) := by
      rw [Nat.card_congr eL.toAddEquiv.toEquiv]
      exact L.odd_natCard_primaryComponent_discriminantGroup hp
    have hquad := (FiniteQuadraticModule.nonempty_isometry_iff_bilinear_isometry_of_odd hoddQ).mpr
      ⟨eL.trans (f.trans eM.symm)⟩
    have hpi := (FiniteQuadraticModule.nonempty_isometry_pi_oddCyclic_iff hpodd k l
      (fun i ↦ (toZMod_eq_intCast_and_isCoprime (hθ1 i)).2)
      (fun j ↦ (toZMod_eq_intCast_and_isCoprime (hη1 j)).2)).mp hquad
    exact localIntegralForm_equivalent_of_jordan_data hp rfl hrank.symm hb hbu hθ1 hb' hbv hη1 hdet
      hpi

/-- **Odd-prime local classification for even lattices by the discriminant quadratic form.** Let
`L` and `M` be even nondegenerate integral lattices and `p` an odd prime. Their `p`-adic integral
localizations `L_p` and `M_p` are isometric if and only if `L` and `M` have the same rank,
`(det L) * (det M)` is a square in `ℤ_p`, and the `p`-primary components of their discriminant
quadratic modules are isometric. -/
theorem localIntegralForm_equivalent_iff_of_isEven
    [L.IsNondegenerate] [M.IsNondegenerate] (hL : L.IsEven) (hM : M.IsEven) (hp : p ≠ 2) :
    (L.localIntegralForm p).Equivalent (M.localIntegralForm p) ↔
      finrank ℤ L = finrank ℤ M ∧
        IsSquare ((L.determinant : ℤ_[p]) * (M.determinant : ℤ_[p])) ∧
        Nonempty (FiniteQuadraticModule.Isometry
          ((L.discriminantQuadraticModule hL).restrict
            (primaryComponent (L.discriminantQuadraticModule hL) p))
          ((M.discriminantQuadraticModule hM).restrict
            (primaryComponent (M.discriminantQuadraticModule hM) p))) := by
  have hodd : Odd (Nat.card ((L.discriminantQuadraticModule hL).restrict
      (primaryComponent (L.discriminantQuadraticModule hL) p))) :=
    L.odd_natCard_primaryComponent_discriminantGroup hp
  rw [L.localIntegralForm_equivalent_iff_of_ne_two (M := M) hp,
    FiniteQuadraticModule.nonempty_isometry_iff_bilinear_isometry_of_odd hodd]
  rfl

/-- When two nondegenerate integral lattices have the same rank and the same signed determinant,
their `p`-adic integral localizations at an odd prime `p` are isometric as soon as the `p`-primary
components of their discriminant bilinear modules are isometric. -/
theorem localIntegralForm_equivalent_of_determinant_eq
    [L.IsNondegenerate] [M.IsNondegenerate] (hrank : finrank ℤ L = finrank ℤ M)
    (hdet : L.determinant = M.determinant) (hp : p ≠ 2)
    (hiso : Nonempty (FiniteBilinearModule.Isometry
      (L.discriminantBilinearModule.restrict
        (primaryComponent L.discriminantBilinearModule p))
      (M.discriminantBilinearModule.restrict
        (primaryComponent M.discriminantBilinearModule p)))) :
    (L.localIntegralForm p).Equivalent (M.localIntegralForm p) :=
  (L.localIntegralForm_equivalent_iff_of_ne_two hp).mpr
    ⟨hrank, hdet ▸ IsSquare.mul_self (L.determinant : ℤ_[p]), hiso⟩

end Classification

end TauCeti.IntegralLattice
