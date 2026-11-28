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
import TauCeti.LinearAlgebra.FiniteBilinearModule.OddCyclic.Bilinear
import TauCeti.LinearAlgebra.FiniteBilinearModule.Primary.Component
import TauCeti.LinearAlgebra.FiniteBilinearModule.Quadratic.Refinement
import TauCeti.NumberTheory.IntegralLattice.Localization.Discriminant.Classification
import TauCeti.NumberTheory.IntegralLattice.Localization.Discriminant.Diagonal
import TauCeti.NumberTheory.Padics.RingHoms
import TauCeti.NumberTheory.Padics.Unit.Squares

/-!
# Classification of odd-prime localizations by discriminant forms

For nondegenerate integral lattices `L, M` and an odd prime `p`, `L_p ≃ M_p` is classified by equal
rank, equal `p`-adic determinant square class, and isometric `p`-primary discriminant bilinear
(`TauCeti.IntegralLattice.localIntegralForm_equivalent_iff_nonempty_isometry_primaryComponent`) or,
for even lattices, quadratic
(`TauCeti.IntegralLattice.localIntegralForm_equivalent_iff_primaryDiscriminantQuadratic`) modules.

## References

* V. V. Nikulin, *Integral symmetric bilinear forms and some of their applications*, §1.9, §1.16.
* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, Chapter 15, §7.
-/

public section

open AddCommGroup Function Module

namespace TauCeti.IntegralLattice

/-! ### Positive-scale Jordan invariants from the `p`-primary discriminant form -/

/-- **Positive-scale Jordan invariants from the `p`-primary discriminant form.** At an odd prime
`p`, if two nondegenerate integral lattices `L` and `M` have diagonal Jordan bases of `L_p` and
`M_p` with unit entries `u i, v j` and valuations `k i, l j`, and the `p`-primary components of
their discriminant bilinear modules are isometric, then the total valuations `∑ i, k i` and
`∑ j, l j` agree and at every positive scale `m > 0` the fiber multiplicities and unit-product
square classes coincide. -/
theorem sum_eq_and_forall_pos_occCount_eq_and_isSquare_of_primaryDiscriminantBilinear
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
    ∑ i, k i = ∑ j, l j ∧ ∀ m, 0 < m → occCount k m = occCount l m ∧
      IsSquare ((∏ i : {i // k i = m}, u i) * ∏ j : {j // l j = m}, v j) := by
  classical
  have hp_odd : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp
  choose θ hθ using fun i ↦ PadicInt.exists_intCast_dvd_sub_and_toZMod_eq (u i : ℤ_[p]) (k i)
  choose η hη using fun j ↦ PadicInt.exists_intCast_dvd_sub_and_toZMod_eq (v j : ℤ_[p]) (l j)
  have hθp i : (p : ℤ_[p]) ∣ (u i : ℤ_[p]) - θ i :=
    PadicInt.toZMod_eq_iff_dvd_sub.mp ((map_intCast PadicInt.toZMod (θ i)).trans (hθ i).2.symm)
  have hηp j : (p : ℤ_[p]) ∣ (v j : ℤ_[p]) - η j :=
    PadicInt.toZMod_eq_iff_dvd_sub.mp ((map_intCast PadicInt.toZMod (η j)).trans (hη j).2.symm)
  obtain ⟨eL⟩ :=
    nonempty_isometry_pi_oddCyclic_primaryComponent hp_odd hb hbu fun i ↦ (hθ i).1
  obtain ⟨eM⟩ :=
    nonempty_isometry_pi_oddCyclic_primaryComponent hp_odd hc hcv fun j ↦ (hη j).1
  let e := eL.trans (hdisc.some.trans eM.symm)
  have hsum : ∑ i, k i = ∑ j, l j := by
    have hcard := Nat.card_congr e.toAddEquiv.toEquiv
    rw [Nat.card_pi, Nat.card_pi] at hcard
    simp_rw [FiniteQuadraticModule.natCard_oddCyclic, Finset.prod_pow_eq_pow_sum] at hcard
    exact Nat.pow_right_injective (Fact.out : p.Prime).one_lt hcard
  have hpi := (FiniteBilinearModule.nonempty_isometry_pi_oddCyclic_iff hp_odd k l
    (fun i ↦ PadicInt.isCoprime_of_dvd_unit_sub (hθp i))
    (fun j ↦ PadicInt.isCoprime_of_dvd_unit_sub (hηp j))).mp ⟨e⟩
  refine ⟨hsum, fun m hm ↦ ?_⟩
  obtain ⟨hcnt, hleg⟩ := hpi m hm
  refine ⟨by rwa [occCount_eq_card_filter, occCount_eq_card_filter], ?_⟩
  rw [PadicInt.isSquare_prod_mul_prod_iff_prod_legendreSym_eq hp
    (fun i : {i // k i = m} ↦ u i.val) (fun j : {j // l j = m} ↦ v j.val)
    (fun i ↦ hθp i.val) (fun j ↦ hηp j.val),
    ← Finset.prod_subtype (Finset.univ.filter (k · = m)) (by simp) (fun i ↦ legendreSym p (θ i)),
    ← Finset.prod_subtype (Finset.univ.filter (l · = m)) (by simp) (fun j ↦ legendreSym p (η j)),
    hleg]

/-! ### Local isometry from rank, determinant, and `p`-primary discriminant form -/

/-- When two nondegenerate integral lattices have equal signed determinants, their localizations at
an odd prime `p` are isometric if and only if they have the same rank and isometric `p`-primary
discriminant bilinear modules. -/
theorem localIntegralForm_equivalent_iff_primaryDiscriminantBilinear_of_determinant_eq
    {V W : Type*} [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]
    (L : IntegralLattice V) (M : IntegralLattice W) [L.IsNondegenerate] [M.IsNondegenerate]
    {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) (hdet : L.determinant = M.determinant) :
    (L.localIntegralForm p).Equivalent (M.localIntegralForm p) ↔ finrank ℤ L = finrank ℤ M ∧
      Nonempty (FiniteBilinearModule.Isometry
        (L.discriminantBilinearModule.restrict (primaryComponent L.discriminantBilinearModule p))
        (M.discriminantBilinearModule.restrict
          (primaryComponent M.discriminantBilinearModule p))) := by
  rw [localIntegralForm_equivalent_iff_nonempty_isometry_primaryComponent hp]
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
      finrank ℤ L = finrank ℤ M ∧ IsSquare ((L.determinant : ℤ_[p]) * (M.determinant : ℤ_[p])) ∧
        Nonempty (FiniteQuadraticModule.Isometry
          ((L.discriminantQuadraticModule hL).restrict
            (primaryComponent (L.discriminantQuadraticModule hL) p))
          ((M.discriminantQuadraticModule hM).restrict
            (primaryComponent (M.discriminantQuadraticModule hM) p))) := by
  rw [localIntegralForm_equivalent_iff_nonempty_isometry_primaryComponent hp,
    ← L.discriminantQuadraticModule_toFiniteBilinearModule hL,
    ← M.discriminantQuadraticModule_toFiniteBilinearModule hM,
    ← FiniteQuadraticModule.restrict_toFiniteBilinearModule,
    ← FiniteQuadraticModule.restrict_toFiniteBilinearModule,
    FiniteQuadraticModule.nonempty_isometry_iff_bilinear_isometry_of_odd
      ((L.discriminantQuadraticModule hL).odd_natCard_restrict_primaryComponent Fact.out hp)]

/-- When two even nondegenerate integral lattices have equal signed determinants, their
localizations at an odd prime `p` are isometric if and only if they have the same rank and
isometric `p`-primary discriminant quadratic modules. -/
theorem localIntegralForm_equivalent_iff_primaryDiscriminantQuadratic_of_determinant_eq
    {V W : Type*} [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]
    (L : IntegralLattice V) (M : IntegralLattice W) [L.IsNondegenerate] [M.IsNondegenerate]
    {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) (hL : L.IsEven) (hM : M.IsEven)
    (hdet : L.determinant = M.determinant) :
    (L.localIntegralForm p).Equivalent (M.localIntegralForm p) ↔ finrank ℤ L = finrank ℤ M ∧
      Nonempty (FiniteQuadraticModule.Isometry
        ((L.discriminantQuadraticModule hL).restrict
          (primaryComponent (L.discriminantQuadraticModule hL) p))
        ((M.discriminantQuadraticModule hM).restrict
          (primaryComponent (M.discriminantQuadraticModule hM) p))) := by
  rw [localIntegralForm_equivalent_iff_primaryDiscriminantQuadratic L M hp hL hM]
  simp [hdet, IsSquare.mul_self]

end TauCeti.IntegralLattice
