/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.IntegralLattice.Localization.Discriminant.Form
public import TauCeti.NumberTheory.IntegralLattice.Localization.Unimodular
import TauCeti.LinearAlgebra.BilinearForm.Diagonalization
import TauCeti.LinearAlgebra.BilinearForm.Henselian
import TauCeti.LinearAlgebra.Matrix.BilinearForm
import TauCeti.NumberTheory.IntegralLattice.Diagonalization
import TauCeti.NumberTheory.IntegralLattice.Localization.Discriminant.Diagonal.Basic
import TauCeti.NumberTheory.Padics.BilinearForm.OddPrime
import TauCeti.NumberTheory.Padics.PadicIntegers
import TauCeti.NumberTheory.Padics.RingHoms
import TauCeti.NumberTheory.Padics.Squares
import TauCeti.RingTheory.Henselian.Basic

/-!
# Localizations at odd primes from the discriminant bilinear form

Let `L` and `M` be nondegenerate integral lattices and `p` an odd prime. The localizations
`L_p = ℤ_p ⊗[ℤ] L` and `M_p` are integrally isometric exactly when `L` and `M` have the same rank,
their determinants lie in one square class of `ℤ_p`, and the `p`-primary components of their
discriminant bilinear modules are isometric
(`TauCeti.IntegralLattice.localIntegralForm_equivalent_iff_nonempty_isometry_primaryComponent`).

Necessity is the invariance of the rank, of the determinant square class and of the discriminant
form under local isometry. For sufficiency, diagonalize: `L_p` has an orthogonal basis with
self-pairings `uᵢ pᵏⁱ`, `uᵢ` a unit, and the `p`-primary component of `b_L` is the orthogonal sum
of the odd cyclic pairings `b_{θᵢ}^{(p)}(pᵏⁱ)` for integers `θᵢ ≡ uᵢ (mod p^{max kᵢ 1})` coprime to
`p` (`PadicInt.exists_int_isCoprime_and_pow_dvd_sub`). The classification of such sums gives, for
every `m ≥ 1`, equally many basis vectors of `L_p` and of `M_p` with exponent `m`, and equal
products of the Legendre symbols of their coefficients, so that the products of the corresponding
units of `L_p` and `M_p` lie in one square class. The rank then fixes the number of unimodular basis
vectors, and the determinant fixes the square class of the product of their units. An orthogonal
basis with these data determines the form up to isometry
(`LinearMap.BilinForm.iIsOrtho.equivalent_of_card_eq_of_isSquare_prod_mul_prod`).

So, away from `2`, the genus of a nondegenerate lattice is determined by its signature and its
discriminant bilinear form: two nondegenerate lattices lie in one genus exactly when their
signatures agree, their discriminant bilinear modules are isometric, and their localizations at
`2` are isometric
(`TauCeti.IntegralLattice.sameGenus_iff_nonempty_isometry_and_localIntegralForm_two_equivalent`).

## Main results

* `TauCeti.IntegralLattice.localIntegralForm_equivalent_iff_nonempty_isometry_primaryComponent`:
  at an odd prime, the localization of a nondegenerate lattice is determined up to isometry by
  the rank, the determinant square class and the `p`-primary discriminant bilinear form.
* `TauCeti.IntegralLattice.sameGenus_iff_nonempty_isometry_and_localIntegralForm_two_equivalent`:
  the genus of a nondegenerate lattice is determined by its signature, its discriminant bilinear
  form and its localization at `2`.

## References

* V. V. Nikulin, *Integral symmetric bilinear forms and some of their applications*, §1.9 and
  Corollary 1.16.3.
* O. T. O'Meara, *Introduction to Quadratic Forms*, 92:2.
* J. W. S. Cassels, *Rational Quadratic Forms*, Chapter 8.
-/

public section

open AddCommGroup Finset Module

namespace TauCeti.IntegralLattice

variable {V W : Type*} [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]
  {p : ℕ} [Fact p.Prime]

/-! ### Positive-exponent Jordan invariants from the discriminant form -/

variable {L : IntegralLattice V} {M : IntegralLattice W} [L.IsNondegenerate] [M.IsNondegenerate]

/-- From a `p`-primary discriminant bilinear isometry between two nondegenerate lattices equipped
with diagonal Jordan bases at an odd prime `p`, every positive exponent `m ≥ 1` has equal
multiplicity and unit product in the same square class of `ℤ_p`. -/
theorem forall_pos_card_filter_eq_and_isSquare_of_isometry_primaryComponent
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    {b : Basis ι ℤ_[p] (L.LocalCarrier p)} {c : Basis κ ℤ_[p] (M.LocalCarrier p)}
    {u : ι → ℤ_[p]ˣ} {v : κ → ℤ_[p]ˣ} {k : ι → ℕ} {l : κ → ℕ}
    (hp_odd : Odd p)
    (hb : (L.localIntegralForm p).iIsOrtho b)
    (hbu : ∀ i, L.localIntegralForm p (b i) (b i) = u i * (p : ℤ_[p]) ^ k i)
    (hc : (M.localIntegralForm p).iIsOrtho c)
    (hcv : ∀ j, M.localIntegralForm p (c j) (c j) = v j * (p : ℤ_[p]) ^ l j)
    (f : FiniteBilinearModule.Isometry
      (L.discriminantBilinearModule.restrict (primaryComponent L.discriminantBilinearModule p))
      (M.discriminantBilinearModule.restrict (primaryComponent M.discriminantBilinearModule p))) :
    ∀ m, 0 < m → #{i | k i = m} = #{j | l j = m} ∧
      IsSquare ((∏ i with k i = m, u i) * ∏ j with l j = m, v j) := by
  choose θ _ hθ using fun i ↦
    _root_.PadicInt.exists_int_isCoprime_and_pow_dvd_sub (u i).isUnit (k i)
  choose η _ hη using fun j ↦
    _root_.PadicInt.exists_int_isCoprime_and_pow_dvd_sub (v j).isUnit (l j)
  obtain ⟨g⟩ := L.nonempty_isometry_pi_oddCyclic_primaryComponent hp_odd hb hbu fun i ↦
    (pow_dvd_pow (p : ℤ_[p]) (le_max_left (k i) 1)).trans (hθ i)
  obtain ⟨g'⟩ := M.nonempty_isometry_pi_oddCyclic_primaryComponent hp_odd hc hcv fun j ↦
    (pow_dvd_pow (p : ℤ_[p]) (le_max_left (l j) 1)).trans (hη j)
  exact FiniteQuadraticModule.forall_pos_card_filter_eq_and_isSquare_of_isometry_pi_oddCyclic
    hp_odd
    (fun i ↦ by simpa only [pow_one] using
      (pow_dvd_pow (p : ℤ_[p]) (le_max_right (k i) 1)).trans (hθ i))
    (fun j ↦ by simpa only [pow_one] using
      (pow_dvd_pow (p : ℤ_[p]) (le_max_right (l j) 1)).trans (hη j))
    ⟨g.trans (f.trans g'.symm)⟩

/-! ### The classification -/

/-- **Sufficiency.** At an odd prime, lattices of equal rank, with determinants in one square class
of `ℤ_p` and isometric `p`-primary discriminant bilinear forms, have isometric localizations. -/
private theorem localIntegralForm_equivalent_of_isometry (hp : p ≠ 2)
    (hrank : finrank ℤ L = finrank ℤ M)
    (hdet : IsSquare ((L.determinant : ℤ_[p]) * (M.determinant : ℤ_[p])))
    (f : FiniteBilinearModule.Isometry
      (L.discriminantBilinearModule.restrict (primaryComponent L.discriminantBilinearModule p))
      (M.discriminantBilinearModule.restrict (primaryComponent M.discriminantBilinearModule p))) :
    (L.localIntegralForm p).Equivalent (M.localIntegralForm p) := by
  have hodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp
  obtain ⟨b, u, k, hb, hbu⟩ :=
    L.exists_basis_iIsOrtho_localIntegralForm_eq_unit_mul_pow hp L.form_nondegenerate
  obtain ⟨c, v, l, hc, hcv⟩ :=
    M.exists_basis_iIsOrtho_localIntegralForm_eq_unit_mul_pow hp M.form_nondegenerate
  have hpos := forall_pos_card_filter_eq_and_isSquare_of_isometry_primaryComponent
    hodd hb hbu hc hcv f
  -- The numbers of unimodular basis vectors agree as well, the total numbers being the ranks.
  set T : Finset ℕ := insert 0 (univ.image k ∪ univ.image l)
  have hcard m : #{i | k i = m} = #{j | l j = m} := by
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · have hkT : ∑ m ∈ T, #{i | k i = m} = finrank ℤ L := by
        simpa [T, Fintype.card_fin] using (Finset.card_eq_sum_card_fiberwise
          (f := k) (s := univ) (t := T) fun i _ ↦ by simp [T]).symm
      have hlT : ∑ m ∈ T, #{j | l j = m} = finrank ℤ M := by
        simpa [T, Fintype.card_fin] using (Finset.card_eq_sum_card_fiberwise
          (f := l) (s := univ) (t := T) fun j _ ↦ by simp [T]).symm
      rw [← add_sum_erase T _ (mem_insert_self 0 _)] at hkT hlT
      have hrest : ∑ m ∈ T.erase 0, #{i | k i = m} = ∑ m ∈ T.erase 0, #{j | l j = m} :=
        sum_congr rfl fun m hm ↦ (hpos m (Nat.pos_of_ne_zero (ne_of_mem_erase hm))).1
      omega
    · exact (hpos m hm).1
  -- The product of all the units is a square, by comparison with the determinants.
  obtain ⟨w, hw⟩ := L.exists_unit_sq_mul_determinant_eq_prod_mul_pow hb hbu
  obtain ⟨w', hw'⟩ := M.exists_unit_sq_mul_determinant_eq_prod_mul_pow hc hcv
  obtain ⟨r, hr⟩ := hdet
  have htot : IsSquare ((∏ i, u i) * ∏ j, v j) := by
    refine Units.isSquare_coe_iff.mp (PadicInt.isSquare_of_isUnit_of_mul_pow_eq_sq (Units.isUnit _)
      (n := ∑ i, k i + ∑ j, l j) (s := w * w' * r) ?_)
    rw [Units.val_mul, Units.coe_prod, Units.coe_prod, pow_add]
    linear_combination -((∏ j, (v j : ℤ_[p])) * (p : ℤ_[p]) ^ ∑ j, l j) * hw -
      ((w : ℤ_[p]) ^ 2 * L.determinant) * hw' + ((w : ℤ_[p]) ^ 2 * (w' : ℤ_[p]) ^ 2) * hr
  refine LinearMap.BilinForm.iIsOrtho.equivalent_of_card_eq_of_isSquare_prod_mul_prod
    (PadicInt.isUnit_two hp) hb hc hbu hcv hcard fun m ↦ ?_
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have hsplit : (∏ i, u i) * ∏ j, v j =
        ∏ m ∈ T, (∏ i with k i = m, u i) * ∏ j with l j = m, v j := by
      rw [prod_mul_distrib, prod_fiberwise_of_maps_to (g := k) fun i _ ↦ by simp [T],
        prod_fiberwise_of_maps_to (g := l) fun j _ ↦ by simp [T]]
    rw [hsplit, ← mul_prod_erase T _ (mem_insert_self 0 _)] at htot
    have hrest := isSquare_prod (s := T.erase 0) _ fun m hm ↦
      (hpos m (Nat.pos_of_ne_zero (ne_of_mem_erase hm))).2
    simpa using htot.div hrest
  · exact (hpos m hm).2

/-- **Localizations at odd primes from the discriminant bilinear form.** At an odd prime `p`, the
localizations of two nondegenerate lattices are integrally isometric exactly when the lattices
have the same rank, their determinants lie in one square class of `ℤ_p`, and the `p`-primary
components of their discriminant bilinear modules are isometric. When the determinants are units
at `p` the last condition is empty, and this is the unimodular classification
`TauCeti.IntegralLattice.localIntegralForm_equivalent_iff`. -/
theorem localIntegralForm_equivalent_iff_nonempty_isometry_primaryComponent (hp : p ≠ 2) :
    (L.localIntegralForm p).Equivalent (M.localIntegralForm p) ↔
      finrank ℤ L = finrank ℤ M ∧
        IsSquare ((L.determinant : ℤ_[p]) * (M.determinant : ℤ_[p])) ∧
          Nonempty (FiniteBilinearModule.Isometry
            (L.discriminantBilinearModule.restrict
              (primaryComponent L.discriminantBilinearModule p))
            (M.discriminantBilinearModule.restrict
              (primaryComponent M.discriminantBilinearModule p))) := by
  refine ⟨fun h ↦ ⟨(L.localIntegralForm_equivalent_imp M p h).1,
    (L.localIntegralForm_equivalent_imp M p h).2, h.map primaryDiscriminantBilinearIsometry⟩,
    fun ⟨hrank, hdet, ⟨f⟩⟩ ↦ localIntegralForm_equivalent_of_isometry hp hrank hdet f⟩

/-- **The genus away from `2`.** Two nondegenerate lattices lie in one genus exactly when their
signatures agree, their discriminant bilinear modules are isometric, and their localizations at
`2` are isometric. So away from `2` the genus is determined by the signature and the discriminant
bilinear form. -/
theorem sameGenus_iff_nonempty_isometry_and_localIntegralForm_two_equivalent :
    L.SameGenus M ↔ L.signature = M.signature ∧
      Nonempty (FiniteBilinearModule.Isometry L.discriminantBilinearModule
        M.discriminantBilinearModule) ∧
      (L.localIntegralForm 2).Equivalent (M.localIntegralForm 2) := by
  refine ⟨fun h ↦ ⟨h.signature_eq, h.nonempty_isometry_discriminantBilinearModule,
    h.localIntegralForm_equivalent 2⟩, fun ⟨hsig, ⟨f⟩, h2⟩ ↦ (sameGenus_iff L M).mpr
    ⟨hsig, fun p _ ↦ ?_⟩⟩
  obtain rfl | hp := eq_or_ne p 2
  · exact h2
  -- At an odd prime the signature supplies the rank, the signature together with the order of the
  -- discriminant group supplies the determinant, and `f` supplies the `p`-primary component.
  have hdet := L.determinant_eq_of_signature_eq_of_discriminant_eq hsig
    (discriminant_eq_of_discriminantBilinearIsometry f)
  exact (localIntegralForm_equivalent_iff_nonempty_isometry_primaryComponent hp).mpr
    ⟨L.finrank_eq_of_signature_eq hsig, ⟨L.determinant, by rw [hdet]⟩,
      ⟨f.restrictPrimaryComponent p⟩⟩

end TauCeti.IntegralLattice
