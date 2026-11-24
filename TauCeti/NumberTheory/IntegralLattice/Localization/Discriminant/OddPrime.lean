/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Rank
public import TauCeti.LinearAlgebra.IntegralLattice.Discriminant.Quadratic
public import TauCeti.NumberTheory.IntegralLattice.Localization.Basic
import TauCeti.NumberTheory.IntegralLattice.Diagonalization
import TauCeti.NumberTheory.IntegralLattice.Localization.Discriminant.Classification
import TauCeti.NumberTheory.IntegralLattice.Localization.Discriminant.Diagonal.Basic
import TauCeti.NumberTheory.IntegralLattice.Localization.Discriminant.Form
import TauCeti.NumberTheory.Padics.BilinearForm.OddPrime
import TauCeti.NumberTheory.Padics.RingHoms

/-!
# Odd-prime classification of integral localizations by the discriminant form

Classification of localized integral forms `L_p` over `ℤ_p` at an odd prime `p` (Nikulin,
Theorem 1.9.1 and Corollaries 1.9.4 and 1.16.3), building on
`TauCeti.IntegralLattice.localIntegralForm_equivalent_iff_nonempty_isometry_primaryComponent`:
unit-square determinant and even-lattice variants, and minimal-rank uniqueness when
`finrank ℤ L = AddGroup.rank (A_L)_p` and `finrank ℤ M = AddGroup.rank (A_M)_p`.

## Main results

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
    (pow_dvd_pow (p : ℤ_[p]) (le_max_right (k i) 1)).trans (hθ_dvd i),
    L.nonempty_isometry_pi_oddCyclic_primaryComponent hp_odd hb hbu fun i ↦
      (pow_dvd_pow (p : ℤ_[p]) (le_max_left (k i) 1)).trans (hθ_dvd i)⟩

/-! ### Odd-prime classification theorems -/

/-- Unit-square determinant formulation of
`localIntegralForm_equivalent_iff_nonempty_isometry_primaryComponent`. -/
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
  refine ⟨fun h ↦ ⟨(L.localIntegralForm_equivalent_imp M p h).1,
    L.exists_determinant_eq_unit_sq_mul_of_localIntegralForm_equivalent M p h,
    h.map primaryDiscriminantBilinearIsometry⟩, fun ⟨hrank, ⟨u, hu⟩, hdisc⟩ ↦ ?_⟩
  refine (localIntegralForm_equivalent_iff_nonempty_isometry_primaryComponent (L := L) (M := M)
    hp).mpr ⟨hrank, ⟨(u : ℤ_[p]) * (M.determinant : ℤ_[p]), by rw [hu]; ring⟩, hdisc⟩

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
  rw [localIntegralForm_equivalent_iff_nonempty_isometry_primaryComponent (L := L) (M := M) hp,
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
  obtain ⟨b, u, k, hb, hbu⟩ := L.exists_fin_basis_iIsOrtho_localIntegralForm_eq_unit_mul_pow
    hp L.form_nondegenerate (rfl : finrank ℤ L = _)
  obtain ⟨c, v, l, hc, hcv⟩ := M.exists_fin_basis_iIsOrtho_localIntegralForm_eq_unit_mul_pow
    hp M.form_nondegenerate (rfl : finrank ℤ M = _)
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
