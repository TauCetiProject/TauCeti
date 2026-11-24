/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.IntegralLattice.Localization.Discriminant.Form
public import TauCeti.NumberTheory.IntegralLattice.Localization.Unimodular
import Mathlib.NumberTheory.LegendreSymbol.Basic
import TauCeti.Data.Fintype.Fiber
import TauCeti.LinearAlgebra.BilinearForm.Diagonalization
import TauCeti.LinearAlgebra.FiniteBilinearModule.OddCyclic.Bilinear
import TauCeti.LinearAlgebra.Matrix.BilinearForm
import TauCeti.NumberTheory.IntegralLattice.Diagonalization
import TauCeti.NumberTheory.IntegralLattice.Localization.Discriminant.Diagonal.Basic
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
of the odd cyclic pairings `b_{θᵢ}^{(p)}(pᵏⁱ)` for integers `θᵢ ≡ uᵢ (mod pᵏⁱ)` with the same
reduction modulo `p` as `uᵢ` (`PadicInt.exists_intCast_dvd_sub_and_toZMod_eq`). The
classification of such sums gives, for every `m ≥ 1`, equally many basis vectors of `L_p` and of
`M_p` with exponent `m`, and equal products of the Legendre symbols of their coefficients, so that
the products of the corresponding units of `L_p` and `M_p` lie in one square class. The rank then
fixes the number of unimodular basis vectors, and the determinant fixes the square class of the
product of their units. An orthogonal basis with these data determines the form up to isometry
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

/-! ### Diagonal Jordan data -/

/-- In an orthogonal basis of `L_p` with self-pairings `uᵢ pᵏⁱ`, the Gram determinant
`(∏ uᵢ) p^{∑ kᵢ}` is the determinant of `L` up to the square of a unit. -/
private theorem exists_prod_mul_pow_eq_unit_sq_mul_determinant {ι : Type*} [Fintype ι]
    (L : IntegralLattice V) {b : Basis ι ℤ_[p] (L.LocalCarrier p)}
    {u : ι → ℤ_[p]ˣ} {k : ι → ℕ} (hb : (L.localIntegralForm p).iIsOrtho b)
    (hbu : ∀ i, L.localIntegralForm p (b i) (b i) = u i * (p : ℤ_[p]) ^ k i) :
    ∃ w : ℤ_[p]ˣ, ((∏ i, u i : ℤ_[p]ˣ) : ℤ_[p]) * (p : ℤ_[p]) ^ (∑ i, k i) =
      (w : ℤ_[p]) ^ 2 * (L.determinant : ℤ_[p]) := by
  classical
  obtain ⟨w, hw⟩ := LinearMap.BilinForm.Equivalent.exists_det_eq_unit_sq_mul_det
    ⟨LinearMap.BilinForm.IsometryEquiv.refl (L.localIntegralForm p)⟩ b
    ((Module.finBasis ℤ L).baseChange ℤ_[p])
  refine ⟨w, ?_⟩
  rw [← L.det_toMatrix_localIntegralForm p (Module.finBasis ℤ L), ← hw, hb.toMatrix_eq_diagonal,
    Matrix.det_diagonal]
  simp [hbu, prod_mul_distrib, prod_pow_eq_pow_sum]

/-- **Square classes of the diagonal Jordan data.** Let `u` and `v` be families of `p`-adic units,
grouped by exponents `k` and `l`, with integer representatives `θ` and `η` modulo `p`. If the
products of the Legendre symbols of the representatives agree in every positive exponent, and the
product of all the units is a square, then in every exponent the products of the units lie in one
square class. -/
private theorem isSquare_prod_filter_mul_prod_filter (hp : p ≠ 2) {ι κ : Type*} [Fintype ι]
    [Fintype κ] {u : ι → ℤ_[p]ˣ} {v : κ → ℤ_[p]ˣ} {k : ι → ℕ} {l : κ → ℕ} {θ : ι → ℤ} {η : κ → ℤ}
    (hθz : ∀ i, PadicInt.toZMod (u i : ℤ_[p]) = θ i)
    (hηz : ∀ j, PadicInt.toZMod (v j : ℤ_[p]) = η j) (hθ0 : ∀ i, (θ i : ZMod p) ≠ 0)
    (hleg : ∀ m, 0 < m →
      ∏ i with k i = m, legendreSym p (θ i) = ∏ j with l j = m, legendreSym p (η j))
    (htot : IsSquare ((∏ i, u i) * ∏ j, v j)) (m : ℕ) :
    IsSquare ((∏ i with k i = m, u i) * ∏ j with l j = m, v j) := by
  have hpos m (hm : 0 < m) : IsSquare ((∏ i with k i = m, u i) * ∏ j with l j = m, v j) := by
    set θm := (∏ i with k i = m, θ i) * ∏ j with l j = m, η j
    have hθmz : PadicInt.toZMod ((∏ i with k i = m, u i) * ∏ j with l j = m, v j : ℤ_[p]ˣ) =
        (θm : ZMod p) := by
      simp [θm, map_prod, hθz, hηz]
    refine Units.isSquare_coe_iff.mp
      ((PadicInt.isSquare_iff_isSquare_toZMod hp (Units.isUnit _)).mpr
        (hθmz ▸ (legendreSym.eq_one_iff p (hθmz ▸ ((Units.isUnit _).map _).ne_zero)).mp ?_))
    have hθm : legendreSym p (∏ i with k i = m, θ i) = ∏ i with k i = m, legendreSym p (θ i) :=
      map_prod (legendreSym.hom p) _ _
    have hηm : legendreSym p (∏ j with l j = m, η j) = ∏ j with l j = m, legendreSym p (η j) :=
      map_prod (legendreSym.hom p) _ _
    rw [legendreSym.mul, hθm, hηm, ← hleg m hm, ← prod_mul_distrib]
    exact prod_eq_one fun i _ ↦ by rw [← sq, legendreSym.sq_one p (hθ0 i)]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · -- The unimodular part is the quotient of the total product by the positive exponents.
    set T := insert 0 (univ.image k ∪ univ.image l)
    have hsplit : (∏ i, u i) * ∏ j, v j =
        ∏ m ∈ T, (∏ i with k i = m, u i) * ∏ j with l j = m, v j := by
      rw [prod_mul_distrib, prod_fiberwise_of_maps_to (g := k) fun i _ ↦ by simp [T],
        prod_fiberwise_of_maps_to (g := l) fun j _ ↦ by simp [T]]
    rw [hsplit, ← mul_prod_erase T _ (mem_insert_self 0 _)] at htot
    have hrest := isSquare_prod (s := T.erase 0) _ fun m hm ↦
      hpos m (Nat.pos_of_ne_zero (ne_of_mem_erase hm))
    simpa using htot.div hrest
  · exact hpos m hm

/-! ### The classification -/

variable {L : IntegralLattice V} {M : IntegralLattice W} [L.IsNondegenerate] [M.IsNondegenerate]

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
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp Fact.out
  obtain ⟨b, u, k, hb, hbu⟩ :=
    L.exists_basis_iIsOrtho_localIntegralForm_eq_unit_mul_pow hp L.form_nondegenerate
  obtain ⟨c, v, l, hc, hcv⟩ :=
    M.exists_basis_iIsOrtho_localIntegralForm_eq_unit_mul_pow hp M.form_nondegenerate
  -- Integer representatives of the units, nonzero modulo `p`.
  choose θ hθ hθz using fun i ↦ PadicInt.exists_intCast_dvd_sub_and_toZMod_eq (u i).val (k i)
  choose η hη hηz using fun j ↦ PadicInt.exists_intCast_dvd_sub_and_toZMod_eq (v j).val (l j)
  have hθ0 i : (θ i : ZMod p) ≠ 0 := hθz i ▸ ((u i).isUnit.map PadicInt.toZMod).ne_zero
  have hη0 j : (η j : ZMod p) ≠ 0 := hηz j ▸ ((v j).isUnit.map PadicInt.toZMod).ne_zero
  have hcop {a : ℤ} (ha : (a : ZMod p) ≠ 0) : IsCoprime (p : ℤ) a :=
    (Prime.coprime_iff_not_dvd hpZ).mpr fun h ↦ ha ((ZMod.intCast_zmod_eq_zero_iff_dvd a p).mpr h)
  -- The `p`-primary discriminant forms are orthogonal sums of odd cyclic pairings.
  obtain ⟨g⟩ := nonempty_isometry_pi_oddCyclic_primaryComponent hodd hb hbu hθ
  obtain ⟨g'⟩ := nonempty_isometry_pi_oddCyclic_primaryComponent hodd hc hcv hη
  have hdata := (FiniteBilinearModule.nonempty_isometry_pi_oddCyclic_iff hodd k l
    (fun i ↦ hcop (hθ0 i)) (fun j ↦ hcop (hη0 j))).mp ⟨g.trans (f.trans g'.symm)⟩
  -- The numbers of unimodular basis vectors agree as well, the total numbers being the ranks.
  have hcard m : #{i | k i = m} = #{j | l j = m} := by
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · obtain ⟨σ, -⟩ := Function.exists_equiv_subtype_ne_of_occCount_eq (u := k) (v := l)
        (z := 0) fun a ha ↦ by
          rw [Function.occCount_eq_card_filter, Function.occCount_eq_card_filter]
          exact (hdata a (Nat.pos_of_ne_zero ha)).1
      have hσ := Fintype.card_congr σ
      rw [Fintype.card_subtype, Fintype.card_subtype] at hσ
      have hn : finrank ℤ_[p] (L.LocalCarrier p) = finrank ℤ_[p] (M.LocalCarrier p) := by
        rw [finrank_baseChange, finrank_baseChange, hrank]
      have hk0 := card_filter_add_card_filter_not (s := univ) (k · = 0)
      have hl0 := card_filter_add_card_filter_not (s := univ) (l · = 0)
      rw [card_univ, Fintype.card_fin] at hk0 hl0
      simp only [ne_eq] at hσ
      omega
    · exact (hdata m hm).1
  -- The product of all the units is a square, by comparison with the determinants.
  obtain ⟨w, hw⟩ := exists_prod_mul_pow_eq_unit_sq_mul_determinant L hb hbu
  obtain ⟨w', hw'⟩ := exists_prod_mul_pow_eq_unit_sq_mul_determinant M hc hcv
  obtain ⟨r, hr⟩ := hdet
  have htot : IsSquare ((∏ i, u i) * ∏ j, v j) := by
    refine Units.isSquare_coe_iff.mp (PadicInt.isSquare_of_isUnit_of_mul_pow_eq_sq (Units.isUnit _)
      (n := ∑ i, k i + ∑ j, l j) (s := w * w' * r) ?_)
    rw [Units.val_mul, pow_add]
    linear_combination ((∏ j, v j : ℤ_[p]ˣ) * (p : ℤ_[p]) ^ ∑ j, l j : ℤ_[p]) * hw +
      ((w : ℤ_[p]) ^ 2 * L.determinant) * hw' + ((w : ℤ_[p]) ^ 2 * (w' : ℤ_[p]) ^ 2) * hr
  exact LinearMap.BilinForm.iIsOrtho.equivalent_of_card_eq_of_isSquare_prod_mul_prod
    (PadicInt.isUnit_two hp) hb hc hbu hcv hcard
    (isSquare_prod_filter_mul_prod_filter hp hθz hηz hθ0 (fun m hm ↦ (hdata m hm).2) htot)

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
  have hdet : L.determinant = M.determinant := by
    have hcard : L.discriminant = M.discriminant := by
      rw [← natCard_discriminantGroup, ← natCard_discriminantGroup]
      exact Nat.card_congr f.toAddEquiv.toEquiv
    have hneg : L.sigNeg = M.sigNeg := congrArg (fun s ↦ s.2.2) hsig
    rw [L.determinant_eq_neg_one_pow_sigNeg_mul_discriminant,
      M.determinant_eq_neg_one_pow_sigNeg_mul_discriminant, hcard, hneg]
  exact (localIntegralForm_equivalent_iff_nonempty_isometry_primaryComponent hp).mpr
    ⟨L.finrank_eq_of_signature_eq hsig, ⟨L.determinant, by rw [hdet]⟩,
      ⟨f.restrictPrimaryComponent p⟩⟩

end TauCeti.IntegralLattice
