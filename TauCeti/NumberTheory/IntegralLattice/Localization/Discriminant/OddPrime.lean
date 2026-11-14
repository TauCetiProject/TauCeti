/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Torsion
public import TauCeti.Data.Fintype.Fiber
public import TauCeti.LinearAlgebra.IntegralLattice.Discriminant.Quadratic
public import TauCeti.NumberTheory.IntegralLattice.Localization.Basic
import TauCeti.LinearAlgebra.BilinearForm.Diagonalization
import TauCeti.LinearAlgebra.BilinearForm.Henselian
import TauCeti.LinearAlgebra.FiniteBilinearModule.OddCyclic.PiClassification
import TauCeti.NumberTheory.IntegralLattice.Diagonalization
import TauCeti.NumberTheory.IntegralLattice.Localization.Discriminant.Diagonal
import TauCeti.NumberTheory.IntegralLattice.Localization.Discriminant.Form
import TauCeti.NumberTheory.IntegralLattice.Localization.Unimodular
import TauCeti.NumberTheory.Padics.PadicIntegers
import TauCeti.NumberTheory.Padics.RingHoms
import TauCeti.NumberTheory.Padics.UnitSquares
import TauCeti.RingTheory.Henselian.Basic

/-!
# Classification of odd-prime localizations by discriminant forms

Let `L` and `M` be nondegenerate integral lattices and `p` an odd prime. An integral isometry
`L_p ≃ M_p` of their `p`-adic localizations preserves the rank, the `p`-adic square class of the
signed determinant (`TauCeti.IntegralLattice.localIntegralForm_equivalent_imp`), and the `p`-primary
component of the discriminant bilinear form
(`TauCeti.IntegralLattice.primaryDiscriminantBilinearIsometry`). This file proves the converse at
every odd prime `p`: those three invariants classify `L_p` up to `ℤ_p`-isometry.

In diagonal Jordan form `B(bᵢ, bᵢ) = uᵢ pᵏⁱ` and `B(cⱼ, cⱼ) = vⱼ pˡʲ`
(`TauCeti.IntegralLattice.exists_basis_iIsOrtho_localIntegralForm_eq_unit_mul_pow`), the `p`-primary
discriminant bilinear modules are the orthogonal sums `⊕ᵢ q_{θᵢ}^{(p)}(pᵏⁱ)` and
`⊕ⱼ q_{ηⱼ}^{(p)}(pˡʲ)` (`TauCeti.IntegralLattice.nonempty_isometry_pi_oddCyclic_primaryComponent`).
Isometry of those sums matches the constituent ranks `#{i | kᵢ = m}` and the unit determinant
square classes `∏_{kᵢ = m} uᵢ` at every positive scale `m ≥ 1`
(`TauCeti.FiniteQuadraticModule.nonempty_isometry_pi_oddCyclic_toFiniteBilinearModule_iff`). Total
rank and the global determinant square class then isolate the unimodular `m = 0` constituent
(`Function.occCount_eq_of_forall_ne`, `Function.isSquare_prod_fiber_subtype_mul_of_forall_ne`), and
diagonal Jordan classification over Henselian local domains
(`LinearMap.BilinForm.iIsOrtho.equivalent_iff_forall_occCount_eq_and_isSquare`) assembles the
isometry over `ℤ_p`.

## Main results

* `TauCeti.IntegralLattice.localIntegralForm_equivalent_iff_forall_occCount_eq_and_isSquare`: two
  diagonal Jordan forms at an odd prime are integrally isometric if and only if they have the same
  rank and the same unit determinant square class at every scale `p^m`, `m ≥ 0`.
* `TauCeti.IntegralLattice.occCount_eq_and_isSquare_of_iIsOrtho_localIntegralForm`: uniqueness of
  the diagonal Jordan invariants of `L_p` at an odd prime, including the unimodular `m = 0`
  constituent.
* `TauCeti.IntegralLattice.localIntegralForm_equivalent_iff_primaryDiscriminantBilinear`: `L_p` and
  `M_p` are integrally isometric at an odd prime `p` if and only if `L` and `M` have equal rank,
  their signed determinants agree modulo squares in `ℤ_p`, and the `p`-primary components of their
  discriminant bilinear modules are isometric.
* `TauCeti.IntegralLattice.localIntegralForm_equivalent_iff_primaryDiscriminantQuadratic`: the
  corresponding criterion for even lattices in terms of the `p`-primary discriminant quadratic
  modules.

## References

* V. V. Nikulin, *Integral symmetric bilinear forms and some of their applications*, §1.9 and
  §1.16.
* O. T. O'Meara, *Introduction to Quadratic Forms*, §92.
* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, Chapter 15, §7.
-/

public section

open AddCommGroup Function Module

namespace TauCeti.IntegralLattice

/-! ### Positive-scale Jordan invariants from the `p`-primary discriminant form -/

/-- Isometry of the `p`-primary discriminant bilinear modules of two diagonal Jordan forms at an
odd prime `p` gives equal exponent sums and matches the multiplicities and unit-product square
classes at all positive scales `m ≥ 1`. -/
private theorem sum_eq_and_pos_invariants_of_primaryDiscriminantBilinear
    {V W : Type*} [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]
    {L : IntegralLattice V} {M : IntegralLattice W} [L.IsNondegenerate] [M.IsNondegenerate]
    {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) {ι κ : Type*} [Fintype ι] [Fintype κ]
    {b : Basis ι ℤ_[p] (L.LocalCarrier p)} {c : Basis κ ℤ_[p] (M.LocalCarrier p)}
    {u : ι → ℤ_[p]ˣ} {v : κ → ℤ_[p]ˣ} {k : ι → ℕ} {l : κ → ℕ}
    (hb : (L.localIntegralForm p).iIsOrtho b)
    (hbu : ∀ i, L.localIntegralForm p (b i) (b i) = u i * (p : ℤ_[p]) ^ k i)
    (hc : (M.localIntegralForm p).iIsOrtho c)
    (hcv : ∀ j, M.localIntegralForm p (c j) (c j) = v j * (p : ℤ_[p]) ^ l j)
    (hdisc : Nonempty (FiniteBilinearModule.Isometry
      (L.discriminantBilinearModule.restrict (primaryComponent L.discriminantBilinearModule p))
      (M.discriminantBilinearModule.restrict (primaryComponent M.discriminantBilinearModule p)))) :
    ∑ i, k i = ∑ j, l j ∧
      ∀ m, 0 < m → occCount k m = occCount l m ∧
        IsSquare ((∏ i : {i // k i = m}, u i) * ∏ j : {j // l j = m}, v j) := by
  classical
  have hp_odd : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp
  let θ : ι → ℤ := fun i ↦ ((u i : ℤ_[p]).appr (max (k i) 1) : ℤ)
  let η : κ → ℤ := fun j ↦ ((v j : ℤ_[p]).appr (max (l j) 1) : ℤ)
  have hθ_pow (i : ι) : (p : ℤ_[p]) ^ k i ∣ u i - θ i :=
    (pow_dvd_pow (p : ℤ_[p]) (le_max_left (k i) 1)).trans (by simp [θ])
  have hη_pow (j : κ) : (p : ℤ_[p]) ^ l j ∣ v j - η j :=
    (pow_dvd_pow (p : ℤ_[p]) (le_max_left (l j) 1)).trans (by simp [η])
  have hθ_p (i : ι) : (p : ℤ_[p]) ∣ u i - θ i :=
    (pow_one (p : ℤ_[p]) ▸ pow_dvd_pow (p : ℤ_[p]) (le_max_right (k i) 1)).trans (by simp [θ])
  have hη_p (j : κ) : (p : ℤ_[p]) ∣ v j - η j :=
    (pow_one (p : ℤ_[p]) ▸ pow_dvd_pow (p : ℤ_[p]) (le_max_right (l j) 1)).trans (by simp [η])
  obtain ⟨eL⟩ := nonempty_isometry_pi_oddCyclic_primaryComponent hp_odd hb hbu hθ_pow
  obtain ⟨eM⟩ := nonempty_isometry_pi_oddCyclic_primaryComponent hp_odd hc hcv hη_pow
  let e := eL.trans (hdisc.some.trans eM.symm)
  have hsum : ∑ i, k i = ∑ j, l j := by
    have hcard := Nat.card_congr e.toAddEquiv.toEquiv
    rw [Nat.card_pi, Nat.card_pi] at hcard
    simp_rw [FiniteQuadraticModule.natCard_oddCyclic, Finset.prod_pow_eq_pow_sum] at hcard
    exact Nat.pow_right_injective (Fact.out : p.Prime).one_lt hcard
  have hpi := (FiniteQuadraticModule.nonempty_isometry_pi_oddCyclic_toFiniteBilinearModule_iff
    hp_odd k l (fun i ↦ PadicInt.isCoprime_of_dvd_unit_sub (hθ_p i))
    (fun j ↦ PadicInt.isCoprime_of_dvd_unit_sub (hη_p j))).mp ⟨e⟩
  refine ⟨hsum, fun m hm ↦ ?_⟩
  obtain ⟨hcnt, hleg⟩ := hpi m hm
  refine ⟨by rwa [occCount_eq_card_filter, occCount_eq_card_filter], ?_⟩
  rw [PadicInt.isSquare_prod_mul_prod_iff_prod_legendreSym_eq hp
    (fun i : {i // k i = m} ↦ u i.1) (fun j : {j // l j = m} ↦ v j.1)
    (fun i ↦ hθ_p i.1) (fun j ↦ hη_p j.1)]
  have hksub : (∏ i : {i // k i = m}, legendreSym p (θ i.1)) =
      ∏ i with k i = m, legendreSym p (θ i) :=
    (Finset.prod_subtype (p := fun i ↦ k i = m)
      (Finset.univ.filter (k · = m)) (by simp) (fun i ↦ legendreSym p (θ i))).symm
  have hlsub : (∏ j : {j // l j = m}, legendreSym p (η j.1)) =
      ∏ j with l j = m, legendreSym p (η j) :=
    (Finset.prod_subtype (p := fun j ↦ l j = m)
      (Finset.univ.filter (l · = m)) (by simp) (fun j ↦ legendreSym p (η j))).symm
  rw [hksub, hlsub, hleg]

/-! ### Diagonal Jordan classification and uniqueness at odd primes -/

/-- **Classification of diagonal Jordan forms at an odd prime.** Let `p` be an odd prime and let
`b` and `c` be orthogonal bases of the localizations `L_p` and `M_p` of two integral lattices, with
`B(bᵢ, bᵢ) = uᵢ pᵏⁱ` and `B(cⱼ, cⱼ) = vⱼ pˡʲ` for units `uᵢ, vⱼ ∈ ℤ_pˣ`. Then `L_p` and `M_p` are
integrally isometric if and only if, at every scale `m ≥ 0` (including the unimodular scale
`m = 0`), they have the same number of summands of scale `p^m` and the products of the unit parts at
scale `p^m` agree modulo squares in `ℤ_pˣ`. -/
theorem localIntegralForm_equivalent_iff_forall_occCount_eq_and_isSquare
    {V W : Type*} [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]
    {L : IntegralLattice V} {M : IntegralLattice W}
    {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) {ι κ : Type*} [Fintype ι] [Fintype κ]
    {b : Basis ι ℤ_[p] (L.LocalCarrier p)} {c : Basis κ ℤ_[p] (M.LocalCarrier p)}
    {u : ι → ℤ_[p]ˣ} {v : κ → ℤ_[p]ˣ} {k : ι → ℕ} {l : κ → ℕ}
    (hb : (L.localIntegralForm p).iIsOrtho b)
    (hbu : ∀ i, L.localIntegralForm p (b i) (b i) = u i * (p : ℤ_[p]) ^ k i)
    (hc : (M.localIntegralForm p).iIsOrtho c)
    (hcv : ∀ j, M.localIntegralForm p (c j) (c j) = v j * (p : ℤ_[p]) ^ l j) :
    (L.localIntegralForm p).Equivalent (M.localIntegralForm p) ↔
      ∀ m : ℕ, occCount k m = occCount l m ∧
        IsSquare ((∏ i : {i // k i = m}, u i) * ∏ j : {j // l j = m}, v j) :=
  hb.equivalent_iff_forall_occCount_eq_and_isSquare hc (PadicInt.isUnit_two hp)
    (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)
    (PadicInt.not_isUnit_iff_dvd.mpr dvd_rfl) hbu hcv

/-- **Uniqueness of diagonal Jordan invariants at an odd prime.** Any two diagonal Jordan bases of
the localization `L_p` of an integral lattice at an odd prime `p` have the same multiplicity and
the same unit determinant square class at every scale `p^m`, `m ≥ 0`. -/
theorem occCount_eq_and_isSquare_of_iIsOrtho_localIntegralForm
    {V : Type*} [AddCommGroup V] [Module ℚ V] {L : IntegralLattice V}
    {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) {ι κ : Type*} [Fintype ι] [Fintype κ]
    {b : Basis ι ℤ_[p] (L.LocalCarrier p)} {c : Basis κ ℤ_[p] (L.LocalCarrier p)}
    {u : ι → ℤ_[p]ˣ} {v : κ → ℤ_[p]ˣ} {k : ι → ℕ} {l : κ → ℕ}
    (hb : (L.localIntegralForm p).iIsOrtho b)
    (hbu : ∀ i, L.localIntegralForm p (b i) (b i) = u i * (p : ℤ_[p]) ^ k i)
    (hc : (L.localIntegralForm p).iIsOrtho c)
    (hcv : ∀ j, L.localIntegralForm p (c j) (c j) = v j * (p : ℤ_[p]) ^ l j) (m : ℕ) :
    occCount k m = occCount l m ∧
      IsSquare ((∏ i : {i // k i = m}, u i) * ∏ j : {j // l j = m}, v j) :=
  hb.occCount_eq_and_isSquare_of_iIsOrtho hc (PadicInt.isUnit_two hp)
    (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)
    (PadicInt.not_isUnit_iff_dvd.mpr dvd_rfl) hbu hcv m

/-! ### Local isometry from rank, determinant, and `p`-primary discriminant form -/

/-- The signed determinant of `K` in `ℤ_p` differs from the diagonal Jordan Gram determinant
`(∏ i, u i) · p ^ (∑ i, k i)` by the square of the change-of-basis unit. -/
private theorem exists_isUnit_determinant_eq_sq_mul_prod
    {V : Type*} [AddCommGroup V] [Module ℚ V] (K : IntegralLattice V)
    {p : ℕ} [Fact p.Prime]
    {b : Basis (Fin (finrank ℤ_[p] (K.LocalCarrier p))) ℤ_[p] (K.LocalCarrier p)}
    {u : Fin (finrank ℤ_[p] (K.LocalCarrier p)) → ℤ_[p]ˣ}
    {k : Fin (finrank ℤ_[p] (K.LocalCarrier p)) → ℕ}
    (hb : (K.localIntegralForm p).iIsOrtho b)
    (hbu : ∀ i, K.localIntegralForm p (b i) (b i) = u i * (p : ℤ_[p]) ^ k i) :
    ∃ d : ℤ_[p], IsUnit d ∧
      (K.determinant : ℤ_[p]) = d ^ 2 * ((∏ i, (u i : ℤ_[p])) * (p : ℤ_[p]) ^ ∑ i, k i) := by
  classical
  have hfin : finrank ℤ_[p] (K.LocalCarrier p) = finrank ℤ K := Module.finrank_baseChange
  let b₀ := ((Module.finBasis ℤ K).baseChange ℤ_[p]).reindex (finCongr hfin.symm)
  refine ⟨(b.toMatrix b₀).det, ?_, ?_⟩
  · rw [← LinearMap.toMatrix_id_eq_basis_toMatrix b₀ b]
    exact (LinearEquiv.refl ℤ_[p] _).isUnit_det b₀ b
  · calc (K.determinant : ℤ_[p])
        = ((K.localIntegralForm p).toMatrix ((Module.finBasis ℤ K).baseChange ℤ_[p])).det :=
          (K.det_toMatrix_localIntegralForm p (Module.finBasis ℤ K)).symm
      _ = ((K.localIntegralForm p).toMatrix b₀).det :=
          (LinearMap.BilinForm.det_toMatrix_reindex _ _ _).symm
      _ = (b.toMatrix b₀).det ^ 2 * ((K.localIntegralForm p).toMatrix b).det :=
          LinearMap.BilinForm.det_toMatrix_eq_det_sq_mul_det b b₀ _
      _ = (b.toMatrix b₀).det ^ 2 * ((∏ i, (u i : ℤ_[p])) * (p : ℤ_[p]) ^ ∑ i, k i) := by
          rw [hb.det_toMatrix]
          simp_rw [hbu, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]

/-- **Odd-prime local classification by the discriminant bilinear form.** At an odd prime `p`, the
integral localizations `L_p` and `M_p` of two nondegenerate integral lattices are isometric if and
only if `L` and `M` have the same rank, their signed determinants agree modulo squares in `ℤ_p`,
and the `p`-primary components of their discriminant bilinear modules are isometric. -/
theorem localIntegralForm_equivalent_iff_primaryDiscriminantBilinear
    {V W : Type*} [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]
    (L : IntegralLattice V) (M : IntegralLattice W) [L.IsNondegenerate] [M.IsNondegenerate]
    {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) :
    (L.localIntegralForm p).Equivalent (M.localIntegralForm p) ↔
      finrank ℤ L = finrank ℤ M ∧
        IsSquare ((L.determinant : ℤ_[p]) * (M.determinant : ℤ_[p])) ∧
        Nonempty (FiniteBilinearModule.Isometry
          (L.discriminantBilinearModule.restrict
            (primaryComponent L.discriminantBilinearModule p))
          (M.discriminantBilinearModule.restrict
            (primaryComponent M.discriminantBilinearModule p))) := by
  classical
  constructor
  · intro h
    obtain ⟨hrank, hdet⟩ := L.localIntegralForm_equivalent_imp M p h
    exact ⟨hrank, hdet, h.map primaryDiscriminantBilinearIsometry⟩
  · rintro ⟨hrank, hdet, hdisc⟩
    obtain ⟨b, u, k, hb, hbu⟩ :=
      L.exists_basis_iIsOrtho_localIntegralForm_eq_unit_mul_pow hp L.form_nondegenerate
    obtain ⟨c, v, l, hc, hcv⟩ :=
      M.exists_basis_iIsOrtho_localIntegralForm_eq_unit_mul_pow hp M.form_nondegenerate
    have hcard : Nat.card (Fin (finrank ℤ_[p] (L.LocalCarrier p))) =
        Nat.card (Fin (finrank ℤ_[p] (M.LocalCarrier p))) := by
      simp [LocalCarrier, hrank]
    obtain ⟨hsum, hpos⟩ :=
      sum_eq_and_pos_invariants_of_primaryDiscriminantBilinear hp hb hbu hc hcv hdisc
    obtain ⟨dL, hdL, hdetL⟩ := exists_isUnit_determinant_eq_sq_mul_prod L hb hbu
    obtain ⟨dM, hdM, hdetM⟩ := exists_isUnit_determinant_eq_sq_mul_prod M hc hcv
    have hw : dL * dM * (p : ℤ_[p]) ^ ∑ j, l j ≠ 0 :=
      mul_ne_zero (mul_ne_zero hdL.ne_zero hdM.ne_zero)
        (pow_ne_zero _ (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero))
    have hdet' : IsSquare
        ((((∏ i, u i) * ∏ j, v j : ℤ_[p]ˣ) : ℤ_[p]) * (dL * dM * (p : ℤ_[p]) ^ ∑ j, l j) ^ 2) := by
      convert hdet using 1
      rw [hdetL, hdetM, hsum]
      push_cast
      ring
    have hsq_all : IsSquare ((∏ i, u i) * ∏ j, v j) :=
      Units.isSquare_coe_iff.mp (hdet'.of_mul_right (pow_ne_zero 2 hw) (IsSquare.sq _))
    refine (localIntegralForm_equivalent_iff_forall_occCount_eq_and_isSquare hp hb hbu hc hcv).mpr
      fun m ↦ ?_
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · exact ⟨occCount_eq_of_forall_ne hcard fun a ha ↦ (hpos a (Nat.pos_of_ne_zero ha)).1,
        isSquare_prod_fiber_subtype_mul_of_forall_ne hsq_all
          fun a ha ↦ (hpos a (Nat.pos_of_ne_zero ha)).2⟩
    · exact hpos m hm

/-- When two nondegenerate integral lattices have equal signed determinants, their localizations at
an odd prime `p` are isometric if and only if they have the same rank and isometric `p`-primary
discriminant bilinear modules. -/
theorem localIntegralForm_equivalent_iff_primaryDiscriminantBilinear_of_determinant_eq
    {V W : Type*} [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]
    (L : IntegralLattice V) (M : IntegralLattice W) [L.IsNondegenerate] [M.IsNondegenerate]
    {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) (hdet : L.determinant = M.determinant) :
    (L.localIntegralForm p).Equivalent (M.localIntegralForm p) ↔
      finrank ℤ L = finrank ℤ M ∧
        Nonempty (FiniteBilinearModule.Isometry
          (L.discriminantBilinearModule.restrict
            (primaryComponent L.discriminantBilinearModule p))
          (M.discriminantBilinearModule.restrict
            (primaryComponent M.discriminantBilinearModule p))) := by
  rw [localIntegralForm_equivalent_iff_primaryDiscriminantBilinear L M hp]
  simp [hdet, IsSquare.mul_self]

/-- **Odd-prime local classification for even lattices by the discriminant quadratic form.** At an
odd prime `p`, the integral localizations `L_p` and `M_p` of two even nondegenerate integral
lattices are isometric if and only if `L` and `M` have the same rank, their signed determinants
agree modulo squares in `ℤ_p`, and the `p`-primary components of their discriminant quadratic
modules are isometric. -/
theorem localIntegralForm_equivalent_iff_primaryDiscriminantQuadratic
    {V W : Type*} [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]
    (L : IntegralLattice V) (M : IntegralLattice W) [L.IsNondegenerate] [M.IsNondegenerate]
    {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) (hL : L.IsEven) (hM : M.IsEven) :
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
    (L.discriminantQuadraticModule hL).odd_natCard_restrict_primaryComponent Fact.out hp
  rw [localIntegralForm_equivalent_iff_primaryDiscriminantBilinear L M hp,
    ← L.discriminantQuadraticModule_toFiniteBilinearModule hL,
    ← M.discriminantQuadraticModule_toFiniteBilinearModule hM,
    ← FiniteQuadraticModule.restrict_toFiniteBilinearModule,
    ← FiniteQuadraticModule.restrict_toFiniteBilinearModule,
    FiniteQuadraticModule.nonempty_isometry_iff_bilinear_isometry_of_odd hodd]

/-- When two even nondegenerate integral lattices have equal signed determinants, their
localizations at an odd prime `p` are isometric if and only if they have the same rank and
isometric `p`-primary discriminant quadratic modules. -/
theorem localIntegralForm_equivalent_iff_primaryDiscriminantQuadratic_of_determinant_eq
    {V W : Type*} [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]
    (L : IntegralLattice V) (M : IntegralLattice W) [L.IsNondegenerate] [M.IsNondegenerate]
    {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) (hL : L.IsEven) (hM : M.IsEven)
    (hdet : L.determinant = M.determinant) :
    (L.localIntegralForm p).Equivalent (M.localIntegralForm p) ↔
      finrank ℤ L = finrank ℤ M ∧
        Nonempty (FiniteQuadraticModule.Isometry
          ((L.discriminantQuadraticModule hL).restrict
            (primaryComponent (L.discriminantQuadraticModule hL) p))
          ((M.discriminantQuadraticModule hM).restrict
            (primaryComponent (M.discriminantQuadraticModule hM) p))) := by
  rw [localIntegralForm_equivalent_iff_primaryDiscriminantQuadratic L M hp hL hM]
  simp [hdet, IsSquare.mul_self]

end TauCeti.IntegralLattice
