/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Rank
public import TauCeti.LinearAlgebra.FiniteBilinearModule.Primary.Component
public import TauCeti.LinearAlgebra.IntegralLattice.Discriminant.Quadratic
public import TauCeti.NumberTheory.IntegralLattice.Localization.Basic
import Mathlib.RingTheory.Polynomial.RationalRoot
import TauCeti.Algebra.Group.Even
import TauCeti.Data.Fintype.Fiber
import TauCeti.LinearAlgebra.BilinearForm.Orthogonal
import TauCeti.LinearAlgebra.FiniteBilinearModule.OddCyclic.PiClassification
import TauCeti.NumberTheory.IntegralLattice.Diagonalization
import TauCeti.NumberTheory.IntegralLattice.Localization.Discriminant.Diagonal.Basic
import TauCeti.NumberTheory.IntegralLattice.Localization.Discriminant.Form
import TauCeti.NumberTheory.IntegralLattice.Localization.Unimodular
import TauCeti.NumberTheory.Padics.BilinearForm.OddPrime
import TauCeti.NumberTheory.Padics.PadicIntegers
import TauCeti.NumberTheory.Padics.RingHoms
import TauCeti.RingTheory.IntegralClosure.IntegrallyClosed

/-!
# Odd-prime classification of integral localizations by the discriminant form

Classification of localized integral forms `L_p` over `ℤ_p` at an odd prime `p` (Nikulin,
Theorem 1.9.1 and Corollaries 1.9.4 and 1.16.3): `L_p ≃ M_p` iff `rank L = rank M`,
`det L · det M` is a square in `ℤ_p`, and `(A_L)_p ≅ (A_M)_p` (with rank and determinant
redundant when `finrank ℤ L = AddGroup.rank (A_L)_p` and `finrank ℤ M = AddGroup.rank (A_M)_p`).

## Main results

* `IntegralLattice.localIntegralForm_equivalent_iff_isSquare_and_discriminantBilinearModule`
* `IntegralLattice.localIntegralForm_equivalent_iff_exists_unit_sq_and_discriminantBilinearModule`
* `IntegralLattice.localIntegralForm_equivalent_iff_isSquare_and_discriminantQuadraticModule`
* `TauCeti.IntegralLattice.localIntegralForm_equivalent_iff_of_finrank_eq_rank`
* `TauCeti.IntegralLattice.localIntegralForm_equivalent_iff_of_isEven_of_finrank_eq_rank`
-/

public section

open Module Finset AddCommGroup

namespace TauCeti.IntegralLattice

variable {V W : Type*} [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]

/-! ### Assembling an integral `ℤ_p`-isometry from fiberwise unit-diagonal equivalences -/

/-- From a diagonal Jordan basis of `L_p` at an odd prime `p`, extract integer lifts `θᵢ ≡ uᵢ
(mod p)` together with an isometry between the orthogonal sum of the odd cyclic generators
`q_{θᵢ}^{(p)}(p^{kᵢ})` and the `p`-primary discriminant bilinear module of `L`. -/
private theorem exists_int_lifts_and_isometry_pi_oddCyclic_primaryComponent
    {L : IntegralLattice V} [L.IsNondegenerate]
    {p : ℕ} [Fact p.Prime] (hp_odd : Odd p) {ι : Type*} [Fintype ι]
    {b : Basis ι ℤ_[p] (L.LocalCarrier p)} {u : ι → ℤ_[p]ˣ} {k : ι → ℕ}
    (hb : (L.localIntegralForm p).iIsOrtho b)
    (hbu : ∀ i, L.localIntegralForm p (b i) (b i) = u i * (p : ℤ_[p]) ^ k i) :
    ∃ θ : ι → ℤ, (∀ i, (p : ℤ_[p]) ∣ (u i : ℤ_[p]) - θ i) ∧
      Nonempty (FiniteBilinearModule.Isometry
        (FiniteQuadraticModule.pi fun i ↦
          FiniteQuadraticModule.oddCyclic (p ^ k i) hp_odd.pow (θ i)).toFiniteBilinearModule
        (L.discriminantBilinearModule.restrict
          (primaryComponent L.discriminantBilinearModule p))) := by
  choose θ _ hθ_dvd using fun i ↦
    _root_.PadicInt.exists_int_isCoprime_and_pow_dvd_sub (u i).isUnit (k i)
  refine ⟨θ, fun i ↦ by simpa only [pow_one] using
    (pow_dvd_pow (p : ℤ_[p]) (le_max_right (k i) 1)).trans (hθ_dvd i), ?_⟩
  exact L.nonempty_isometry_pi_oddCyclic_primaryComponent hp_odd hb hbu fun i ↦
    (pow_dvd_pow (p : ℤ_[p]) (le_max_left (k i) 1)).trans (hθ_dvd i)

/-- Given two diagonal Jordan forms of the same rank at an odd prime `p` whose `p`-primary
discriminant bilinear modules are isometric, `k` and `l` agree up to a permutation `σ` and every
positive-scale fiber has square unit product. -/
private theorem exists_perm_and_isSquare_pos_of_isometry_primaryComponent
    {L : IntegralLattice V} {M : IntegralLattice W} [L.IsNondegenerate] [M.IsNondegenerate]
    {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) {n : ℕ}
    {b : Basis (Fin n) ℤ_[p] (L.LocalCarrier p)} {c : Basis (Fin n) ℤ_[p] (M.LocalCarrier p)}
    {u v : Fin n → ℤ_[p]ˣ} {k l : Fin n → ℕ}
    (hb : (L.localIntegralForm p).iIsOrtho b) (hc : (M.localIntegralForm p).iIsOrtho c)
    (hbu : ∀ i, L.localIntegralForm p (b i) (b i) = u i * (p : ℤ_[p]) ^ k i)
    (hcv : ∀ i, M.localIntegralForm p (c i) (c i) = v i * (p : ℤ_[p]) ^ l i)
    (hdisc : Nonempty (FiniteBilinearModule.Isometry
      (L.discriminantBilinearModule.restrict (primaryComponent L.discriminantBilinearModule p))
      (M.discriminantBilinearModule.restrict (primaryComponent M.discriminantBilinearModule p)))) :
    ∃ σ : Equiv.Perm (Fin n), (∀ i, l (σ i) = k i) ∧
      ∀ m, 0 < m → IsSquare ((∏ i with k i = m, u i) * ∏ i with k i = m, v (σ i)) := by
  classical
  have hp_odd : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp
  obtain ⟨θL, hθL, ⟨fL⟩⟩ :=
    exists_int_lifts_and_isometry_pi_oddCyclic_primaryComponent hp_odd hb hbu
  obtain ⟨θM, hθM, ⟨fM⟩⟩ :=
    exists_int_lifts_and_isometry_pi_oddCyclic_primaryComponent hp_odd hc hcv
  obtain ⟨fLM⟩ := hdisc
  have hpos := FiniteQuadraticModule.forall_pos_card_filter_eq_and_isSquare_of_isometry_pi_oddCyclic
    (u := u) (v := v) (k := k) (l := l) hp_odd hθL hθM ⟨fL.trans (fLM.trans fM.symm)⟩
  obtain ⟨σ, hσ⟩ :=
    Function.exists_perm_of_occCount_eq_of_ne (u := k) (v := l) (z := 0) fun m hm ↦ by
      rw [Function.occCount_eq_card_filter, Function.occCount_eq_card_filter]
      exact (hpos m (Nat.pos_of_ne_zero hm)).1
  have hσi : ∀ i, l (σ i) = k i := congrFun hσ
  refine ⟨σ, hσi, fun m hm ↦ ?_⟩
  rw [Finset.prod_filter_equiv k l v m (σ : Fin n ≃ Fin n) hσi]; exact (hpos m hm).2

/-! ### Odd-prime classification theorems -/

/-- **Odd-prime local classification by the discriminant bilinear module.** Let `p` be an odd prime
and let `L` and `M` be nondegenerate integral lattices. Their localized integral forms over `ℤ_p`
are isometric if and only if `L` and `M` have the same rank, the product of their signed
determinants is a square in `ℤ_p`, and the `p`-primary components of their discriminant bilinear
modules are isometric. -/
theorem localIntegralForm_equivalent_iff_isSquare_and_discriminantBilinearModule
    (L : IntegralLattice V) (M : IntegralLattice W) [L.IsNondegenerate] [M.IsNondegenerate]
    {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) :
    (L.localIntegralForm p).Equivalent (M.localIntegralForm p) ↔
      finrank ℤ L = finrank ℤ M ∧
        IsSquare ((L.determinant : ℤ_[p]) * (M.determinant : ℤ_[p])) ∧
        Nonempty (FiniteBilinearModule.Isometry
          (L.discriminantBilinearModule.restrict (primaryComponent L.discriminantBilinearModule p))
          (M.discriminantBilinearModule.restrict
            (primaryComponent M.discriminantBilinearModule p))) := by
  classical
  constructor
  · intro h
    obtain ⟨hrank, hsq⟩ := L.localIntegralForm_equivalent_imp M p h
    exact ⟨hrank, hsq, h.map primaryDiscriminantBilinearIsometry⟩
  · rintro ⟨hrank, hsq, hdisc⟩
    obtain ⟨b, u, k, hb, hbu⟩ :=
      L.exists_fin_basis_iIsOrtho_localIntegralForm_eq_unit_mul_pow hp L.form_nondegenerate
        (rfl : finrank ℤ L = _)
    obtain ⟨c, v, l, hc, hcv⟩ :=
      M.exists_fin_basis_iIsOrtho_localIntegralForm_eq_unit_mul_pow hp M.form_nondegenerate
        hrank.symm
    obtain ⟨σ, hσ, hpos⟩ :=
      exists_perm_and_isSquare_pos_of_isometry_primaryComponent hp hb hc hbu hcv hdisc
    obtain ⟨dL, hdL⟩ := L.exists_unit_sq_mul_determinant_eq_prod_mul_pow hb hbu
    obtain ⟨dM, hdM⟩ := M.exists_unit_sq_mul_determinant_eq_prod_mul_pow hc hcv
    have hsum_eq : ∑ j, l j = ∑ i, k i :=
      (Equiv.sum_comp (σ : Fin _ ≃ Fin _) l).symm.trans (Finset.sum_congr rfl fun i _ ↦ hσ i)
    have hprod_v : ∏ j, (v j : ℤ_[p]) = ∏ i, (v (σ i) : ℤ_[p]) :=
      (Equiv.prod_comp (σ : Fin _ ≃ Fin _) fun j ↦ (v j : ℤ_[p])).symm
    have hfull : IsSquare ((∏ i, u i) * ∏ i, v (σ i)) := by
      rw [← Units.isSquare_coe_iff, Units.val_mul, Units.coe_prod, Units.coe_prod,
        ← TauCeti.IsIntegrallyClosed.isSquare_mul_sq_iff
          (pow_ne_zero (∑ i, k i) (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero))]
      obtain ⟨z, hz⟩ := hsq
      refine ⟨z * dL * dM, ?_⟩
      have hmul := congrArg₂ (· * ·) hdL hdM
      rw [hsum_eq, hprod_v] at hmul; rw [sq]
      linear_combination -hmul + (dL : ℤ_[p]) ^ 2 * (dM : ℤ_[p]) ^ 2 * hz
    have hzero : IsSquare ((∏ i with k i = 0, u i) * ∏ i with k i = 0, v (σ i)) := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.univ.isSquare_prod_filter_of_isSquare_prod k (fun i ↦ u i * v (σ i)) 0
        (by rwa [Finset.prod_mul_distrib]) fun m hm ↦ ?_
      rw [Finset.prod_mul_distrib]; exact hpos m (Nat.pos_of_ne_zero hm)
    exact (L.localIntegralForm p).equivalent_of_iIsOrtho_of_forall_fiber
      (M.localIntegralForm p) hp hb hc hbu hcv σ hσ fun m ↦ by
        rcases Nat.eq_zero_or_pos m with rfl | hm <;> [exact hzero; exact hpos m hm]

/-- Unit-square determinant formulation of
`localIntegralForm_equivalent_iff_isSquare_and_discriminantBilinearModule`. -/
theorem localIntegralForm_equivalent_iff_exists_unit_sq_and_discriminantBilinearModule
    (L : IntegralLattice V) (M : IntegralLattice W) [L.IsNondegenerate] [M.IsNondegenerate]
    {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) :
    (L.localIntegralForm p).Equivalent (M.localIntegralForm p) ↔
      finrank ℤ L = finrank ℤ M ∧
        (∃ u : ℤ_[p]ˣ, (L.determinant : ℤ_[p]) = (u : ℤ_[p]) ^ 2 * (M.determinant : ℤ_[p])) ∧
        Nonempty (FiniteBilinearModule.Isometry
          (L.discriminantBilinearModule.restrict (primaryComponent L.discriminantBilinearModule p))
          (M.discriminantBilinearModule.restrict
            (primaryComponent M.discriminantBilinearModule p))) := by
  constructor
  · intro h
    exact ⟨(L.localIntegralForm_equivalent_imp M p h).1,
      L.exists_determinant_eq_unit_sq_mul_of_localIntegralForm_equivalent M p h,
      h.map primaryDiscriminantBilinearIsometry⟩
  · rintro ⟨hrank, ⟨u, hu⟩, hdisc⟩
    refine (L.localIntegralForm_equivalent_iff_isSquare_and_discriminantBilinearModule M hp).mpr
      ⟨hrank, ?_, hdisc⟩
    exact ⟨(u : ℤ_[p]) * (M.determinant : ℤ_[p]), by rw [hu]; ring⟩

/-- **Odd-prime local classification for even lattices.** For even nondegenerate lattices `L` and
`M` and an odd prime `p`, `L_p ≃ M_p` iff `rank L = rank M`, `det L · det M` is a square in `ℤ_p`,
and the `p`-primary components of their discriminant quadratic modules are isometric. -/
theorem localIntegralForm_equivalent_iff_isSquare_and_discriminantQuadraticModule
    (L : IntegralLattice V) (M : IntegralLattice W) [L.IsNondegenerate] [M.IsNondegenerate]
    (hL : L.IsEven) (hM : M.IsEven) {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) :
    (L.localIntegralForm p).Equivalent (M.localIntegralForm p) ↔
      finrank ℤ L = finrank ℤ M ∧
        IsSquare ((L.determinant : ℤ_[p]) * (M.determinant : ℤ_[p])) ∧
        Nonempty (FiniteQuadraticModule.Isometry
          ((L.discriminantQuadraticModule hL).restrict
            (primaryComponent (L.discriminantQuadraticModule hL) p))
          ((M.discriminantQuadraticModule hM).restrict
            (primaryComponent (M.discriminantQuadraticModule hM) p))) := by
  rw [L.localIntegralForm_equivalent_iff_isSquare_and_discriminantBilinearModule M hp,
    L.nonempty_isometry_restrict_discriminantQuadraticModule_primaryComponent_iff M hL hM
      ((Fact.out : p.Prime).odd_of_ne_two hp)]

/-! ### Minimal-rank uniqueness at odd primes (Nikulin Theorem 1.9.1) -/

/-- **Uniqueness of minimal-rank `p`-adic localizations at odd primes (Nikulin, Theorem 1.9.1).**
If `p` is an odd prime and both `L` and `M` achieve the minimal rank
`finrank ℤ L = AddGroup.rank (A_L)_p` and `finrank ℤ M = AddGroup.rank (A_M)_p`, then `L_p` and
`M_p` are isometric if and only if the `p`-primary components of their discriminant bilinear
modules are isometric; neither equal rank nor a determinant hypothesis needs to be supplied
separately. -/
theorem localIntegralForm_equivalent_iff_of_finrank_eq_rank
    (L : IntegralLattice V) (M : IntegralLattice W) [L.IsNondegenerate] [M.IsNondegenerate]
    {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (hLrank : finrank ℤ L = AddGroup.rank (primaryComponent L.DiscriminantGroup p))
    (hMrank : finrank ℤ M = AddGroup.rank (primaryComponent M.DiscriminantGroup p)) :
    (L.localIntegralForm p).Equivalent (M.localIntegralForm p) ↔
      Nonempty (FiniteBilinearModule.Isometry
        (L.discriminantBilinearModule.restrict (primaryComponent L.discriminantBilinearModule p))
        (M.discriminantBilinearModule.restrict
          (primaryComponent M.discriminantBilinearModule p))) := by
  classical
  refine ⟨fun h ↦ h.map primaryDiscriminantBilinearIsometry, fun ⟨fLM⟩ ↦ ?_⟩
  have hp_odd : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp
  obtain ⟨b, u, k, hb, hbu⟩ :=
    L.exists_fin_basis_iIsOrtho_localIntegralForm_eq_unit_mul_pow hp L.form_nondegenerate
      (rfl : finrank ℤ L = _)
  obtain ⟨c, v, l, hc, hcv⟩ :=
    M.exists_fin_basis_iIsOrtho_localIntegralForm_eq_unit_mul_pow hp M.form_nondegenerate
      (rfl : finrank ℤ M = _)
  obtain ⟨θL, hθL, ⟨fL⟩⟩ :=
    exists_int_lifts_and_isometry_pi_oddCyclic_primaryComponent hp_odd hb hbu
  obtain ⟨θM, hθM, ⟨fM⟩⟩ :=
    exists_int_lifts_and_isometry_pi_oddCyclic_primaryComponent hp_odd hc hcv
  exact (L.localIntegralForm p).equivalent_of_iIsOrtho_of_isometry_pi_oddCyclic
    (M.localIntegralForm p) hb hc hbu hcv
    (L.ne_zero_of_finrank_eq_rank hb hbu hLrank)
    (M.ne_zero_of_finrank_eq_rank hc hcv hMrank)
    (hp_odd := hp_odd) (θ := θL) (η := θM) hθL hθM
    ⟨fL.trans (fLM.trans fM.symm)⟩

/-- Even-lattice counterpart of `localIntegralForm_equivalent_iff_of_finrank_eq_rank`. -/
theorem localIntegralForm_equivalent_iff_of_isEven_of_finrank_eq_rank
    (L : IntegralLattice V) (M : IntegralLattice W) [L.IsNondegenerate] [M.IsNondegenerate]
    (hL : L.IsEven) (hM : M.IsEven) {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (hLrank : finrank ℤ L = AddGroup.rank (primaryComponent L.DiscriminantGroup p))
    (hMrank : finrank ℤ M = AddGroup.rank (primaryComponent M.DiscriminantGroup p)) :
    (L.localIntegralForm p).Equivalent (M.localIntegralForm p) ↔
      Nonempty (FiniteQuadraticModule.Isometry
        ((L.discriminantQuadraticModule hL).restrict
          (primaryComponent (L.discriminantQuadraticModule hL) p))
        ((M.discriminantQuadraticModule hM).restrict
          (primaryComponent (M.discriminantQuadraticModule hM) p))) := by
  rw [L.localIntegralForm_equivalent_iff_of_finrank_eq_rank M hp hLrank hMrank,
    L.nonempty_isometry_restrict_discriminantQuadraticModule_primaryComponent_iff M hL hM
      ((Fact.out : p.Prime).odd_of_ne_two hp)]

end TauCeti.IntegralLattice
