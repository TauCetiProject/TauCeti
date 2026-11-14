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
import Mathlib.Algebra.Squarefree.Basic
import TauCeti.Algebra.Group.Primary.Card
import TauCeti.LinearAlgebra.BilinearForm.Diagonalization
import TauCeti.LinearAlgebra.FiniteBilinearModule.Comparison
import TauCeti.LinearAlgebra.FiniteBilinearModule.OddCyclic.PiClassification
import TauCeti.LinearAlgebra.QuadraticForm.Diagonal.Henselian
import TauCeti.NumberTheory.IntegralLattice.Diagonalization
import TauCeti.NumberTheory.IntegralLattice.Localization.Discriminant.Diagonal
import TauCeti.NumberTheory.IntegralLattice.Localization.Discriminant.Form
import TauCeti.NumberTheory.IntegralLattice.Localization.Unimodular
import TauCeti.NumberTheory.Padics.PadicIntegers
import TauCeti.NumberTheory.Padics.RingHoms
import TauCeti.RingTheory.Henselian.SquareClasses

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
rank and the global determinant square class then isolate the unimodular `m = 0` constituent, and
unit diagonal forms over `ℤ_p` of equal rank and determinant square class are integrally isometric
(`TauCeti.equivalent_weightedSumSquares_iff_isSquare_prod_mul_prod_of_isUnit_two`).

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

open AddCommGroup Function Module QuadraticMap

namespace TauCeti.IntegralLattice

/-! ### Square classes and fiberwise diagonal forms over `ℤ_p` -/

private theorem toZMod_eq_intCast_of_dvd {p : ℕ} [Fact p.Prime] {u : ℤ_[p]} {t : ℤ}
    (ht : (p : ℤ_[p]) ∣ u - t) : PadicInt.toZMod u = (t : ZMod p) := by
  have h0 : PadicInt.toZMod (u - (t : ℤ_[p])) = 0 :=
    (PadicInt.toZMod_eq_zero_iff_dvd _).mpr ht
  rwa [map_sub, map_intCast, sub_eq_zero] at h0

private theorem isCoprime_of_dvd_unit_sub {p : ℕ} [Fact p.Prime] {u : ℤ_[p]ˣ} {t : ℤ}
    (ht : (p : ℤ_[p]) ∣ u - t) : IsCoprime (p : ℤ) t := by
  refine (ZMod.isUnit_intCast_iff_isCoprime t p).mp ?_
  rw [← toZMod_eq_intCast_of_dvd ht]
  exact u.isUnit.map PadicInt.toZMod

/-- Over `ℤ_p` for `p ≠ 2`, two finite products of units agree modulo squares if and only if the
Legendre symbols of any integer representatives modulo `p` have equal products. -/
private theorem isSquare_prod_mul_prod_iff_prod_legendreSym_eq {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    {α β : Type*} [Fintype α] [Fintype β] (u : α → ℤ_[p]ˣ) (v : β → ℤ_[p]ˣ)
    {θ : α → ℤ} {η : β → ℤ} (hθ : ∀ i, (p : ℤ_[p]) ∣ u i - θ i)
    (hη : ∀ j, (p : ℤ_[p]) ∣ v j - η j) :
    IsSquare ((∏ i, u i) * ∏ j, v j) ↔
      ∏ i, legendreSym p (θ i) = ∏ j, legendreSym p (η j) := by
  set U : ℤ_[p]ˣ := (∏ i, u i) * ∏ j, v j
  set Θ : ℤ := (∏ i, θ i) * ∏ j, η j
  have htoZMod : PadicInt.toZMod (U : ℤ_[p]) = (Θ : ZMod p) := by
    simp only [U, Θ]
    push_cast
    rw [map_mul, map_prod, map_prod]
    congr 1
    · exact Finset.prod_congr rfl fun i _ ↦ toZMod_eq_intCast_of_dvd (hθ i)
    · exact Finset.prod_congr rfl fun j _ ↦ toZMod_eq_intCast_of_dvd (hη j)
  have hΘ0 : (Θ : ZMod p) ≠ 0 := by
    rw [← htoZMod]
    exact (U.isUnit.map PadicInt.toZMod).ne_zero
  have hres : IsSquare (IsLocalRing.residue ℤ_[p] (U : ℤ_[p])) ↔
      IsSquare (PadicInt.toZMod (U : ℤ_[p])) := by
    simp only [PadicInt.toZMod_eq_residueField_comp_residue, RingHom.comp_apply,
      RingEquiv.toRingHom_eq_coe, RingHom.coe_coe]
    exact ⟨fun h ↦ h.map PadicInt.residueField,
      fun h ↦ by simpa using h.map PadicInt.residueField.symm⟩
  rw [← Units.isSquare_coe_iff,
    TauCeti.HenselianLocalRing.isSquare_iff_residue_isSquare (PadicInt.isUnit_two hp) U.isUnit,
    hres, htoZMod, ← legendreSym.eq_one_iff p hΘ0,
    show Θ = (∏ i, θ i) * ∏ j, η j from rfl, legendreSym.mul,
    show legendreSym p (∏ i, θ i) = ∏ i, legendreSym p (θ i) from
      map_prod (legendreSym.hom p) _ _,
    show legendreSym p (∏ j, η j) = ∏ j, legendreSym p (η j) from
      map_prod (legendreSym.hom p) _ _]
  have hηsq : (∏ j, legendreSym p (η j)) * ∏ j, legendreSym p (η j) = 1 := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one fun j _ ↦ ?_
    simpa only [pow_two] using legendreSym.sq_one p
      ((ZMod.isUnit_intCast_iff_isCoprime (η j) p).mpr (isCoprime_of_dvd_unit_sub (hη j))).ne_zero
  constructor
  · intro h
    calc ∏ i, legendreSym p (θ i)
        = (∏ i, legendreSym p (θ i)) * ((∏ j, legendreSym p (η j)) * ∏ j, legendreSym p (η j)) := by
          rw [hηsq, mul_one]
      _ = ∏ j, legendreSym p (η j) := by rw [← mul_assoc, h, one_mul]
  · intro h
    rw [h, hηsq]

/-- Over `ℤ_p` for `p ≠ 2`, two diagonal forms `∑ uᵢ pᵏⁱ xᵢ²` and `∑ vⱼ pˡʲ yⱼ²` with unit `uᵢ, vⱼ`
are isometric when every scale `m ≥ 0` has the same multiplicity and the same unit-product square
class. -/
private theorem equivalent_localIntegralForm_of_forall_occCount_eq_and_isSquare
    {V W : Type*} [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]
    {L : IntegralLattice V} {M : IntegralLattice W} {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    {b : Basis ι ℤ_[p] (L.LocalCarrier p)} {c : Basis κ ℤ_[p] (M.LocalCarrier p)}
    {u : ι → ℤ_[p]ˣ} {v : κ → ℤ_[p]ˣ} {k : ι → ℕ} {l : κ → ℕ}
    (hb : (L.localIntegralForm p).iIsOrtho b)
    (hbu : ∀ i, L.localIntegralForm p (b i) (b i) = u i * (p : ℤ_[p]) ^ k i)
    (hc : (M.localIntegralForm p).iIsOrtho c)
    (hcv : ∀ j, M.localIntegralForm p (c j) (c j) = v j * (p : ℤ_[p]) ^ l j)
    (h : ∀ m : ℕ, occCount k m = occCount l m ∧
      IsSquare ((∏ i : {i // k i = m}, u i) * ∏ j : {j // l j = m}, v j)) :
    (L.localIntegralForm p).Equivalent (M.localIntegralForm p) := by
  classical
  let := (PadicInt.isUnit_two hp).invertible
  obtain ⟨σ, hσ⟩ := exists_equiv_of_occCount_eq fun m ↦ (h m).1
  have hlσ (i : ι) : l (σ i) = k i := congrFun hσ i
  rw [(L.isSymm_localIntegralForm p).equivalent_iff_toQuadraticMap_equivalent
    (M.isSymm_localIntegralForm p)]
  refine hb.equivalent_weightedSumSquares.trans ?_
  refine ( ?_ : (weightedSumSquares ℤ_[p] fun i ↦ L.localIntegralForm p (b i) (b i)).Equivalent
    (weightedSumSquares ℤ_[p] fun j ↦ M.localIntegralForm p (c j) (c j))).trans
    hc.equivalent_weightedSumSquares.symm
  simp_rw [hbu, hcv]
  refine ( ?_ : (weightedSumSquares ℤ_[p] fun i ↦ (u i : ℤ_[p]) * (p : ℤ_[p]) ^ k i).Equivalent
    (weightedSumSquares ℤ_[p] fun i ↦ (v (σ i) : ℤ_[p]) * (p : ℤ_[p]) ^ k i)).trans ?_
  · refine TauCeti.equivalent_weightedSumSquares_mul_of_forall_fiber k
      (fun i ↦ (u i : ℤ_[p])) (fun i ↦ (v (σ i) : ℤ_[p])) (fun m ↦ (p : ℤ_[p]) ^ m) fun m ↦ ?_
    let F := {i : ι // k i = m}
    let τ : Fin (Fintype.card F) ≃ F := (Fintype.equivFin F).symm
    have hsqF : IsSquare ((∏ r, u (τ r).1) * ∏ r, v (σ (τ r).1)) := by
      rw [τ.prod_comp (fun i : F ↦ u i.1), τ.prod_comp (fun i : F ↦ v (σ i.1))]
      let σF : F ≃ {j : κ // l j = m} :=
        { toFun := fun i ↦ ⟨σ i.1, (hlσ i.1).trans i.2⟩
          invFun := fun j ↦ ⟨σ.symm j.1, by
            have h1 := hlσ (σ.symm j.1)
            rw [σ.apply_symm_apply, j.2] at h1
            exact h1.symm⟩
          left_inv := fun i ↦ Subtype.ext (σ.symm_apply_apply i.1)
          right_inv := fun j ↦ Subtype.ext (σ.apply_symm_apply j.1) }
      have hσF : (∏ i : F, v (σ i.1)) = ∏ j : {j : κ // l j = m}, v j.1 :=
        σF.prod_comp (fun j ↦ v j.1)
      rw [hσF]
      exact (h m).2
    have heqFin := (equivalent_weightedSumSquares_iff_isSquare_prod_mul_prod_of_isUnit_two
      (PadicInt.isUnit_two hp) (fun r ↦ u (τ r).1) (fun r ↦ v (σ (τ r).1))).mpr hsqF
    rw [weightedSumSquares_units, weightedSumSquares_units] at heqFin
    exact (equivalent_weightedSumSquares_comp (fun i : F ↦ (u i.1 : ℤ_[p])) τ).trans
      (heqFin.trans (equivalent_weightedSumSquares_comp (fun i : F ↦ (v (σ i.1) : ℤ_[p])) τ).symm)
  · convert (equivalent_weightedSumSquares_comp
      (fun j : κ ↦ (v j : ℤ_[p]) * (p : ℤ_[p]) ^ l j) σ).symm using 2
    ext i
    simp [hlσ i]

/-! ### Isolating the `m = 0` Jordan constituent and positive-scale invariants -/

/-- Positive-scale invariants together with equal total cardinality and equal total unit-product
square class determine the `m = 0` multiplicity and unit-product square class as well. -/
private theorem forall_occCount_eq_and_isSquare_of_pos {G ι κ : Type*} [CommGroup G]
    [Fintype ι] [Fintype κ] {u : ι → G} {v : κ → G} {k : ι → ℕ} {l : κ → ℕ}
    (hcard : Fintype.card ι = Fintype.card κ)
    (hsq_all : IsSquare ((∏ i, u i) * ∏ j, v j))
    (hpos : ∀ m, 0 < m → occCount k m = occCount l m ∧
      IsSquare ((∏ i : {i // k i = m}, u i) * ∏ j : {j // l j = m}, v j)) :
    ∀ m : ℕ, occCount k m = occCount l m ∧
      IsSquare ((∏ i : {i // k i = m}, u i) * ∏ j : {j // l j = m}, v j) := by
  classical
  intro m
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · let T : Finset ℕ := insert 0 (Finset.univ.image k ∪ Finset.univ.image l)
    have h0T : 0 ∈ T := Finset.mem_insert_self 0 _
    have hkT (i : ι) : k i ∈ T :=
      Finset.mem_insert_of_mem
        (Finset.mem_union_left _ (Finset.mem_image_of_mem k (Finset.mem_univ i)))
    have hlT (j : κ) : l j ∈ T :=
      Finset.mem_insert_of_mem
        (Finset.mem_union_right _ (Finset.mem_image_of_mem l (Finset.mem_univ j)))
    have hocc0 : occCount k 0 = occCount l 0 := by
      have hsumk := sum_occCount_eq_card k hkT
      have hsuml := sum_occCount_eq_card l hlT
      rw [← Finset.add_sum_erase _ _ h0T] at hsumk hsuml
      have herase : ∑ a ∈ T.erase 0, occCount k a = ∑ a ∈ T.erase 0, occCount l a :=
        Finset.sum_congr rfl fun a ha ↦
          (hpos a (Nat.pos_of_ne_zero (Finset.mem_erase.mp ha).1)).1
      have htot : Nat.card ι = Nat.card κ := by
        simpa only [Nat.card_eq_fintype_card] using hcard
      omega
    have hmul :
        ((∏ i : {i // k i = 0}, u i.1) * ∏ j : {j // l j = 0}, v j.1) *
          ∏ a ∈ T.erase 0, ((∏ i : {i // k i = a}, u i.1) * ∏ j : {j // l j = a}, v j.1) =
        (∏ i, u i) * ∏ j, v j := by
      rw [Finset.prod_mul_distrib]
      calc ((∏ i : {i // k i = 0}, u i.1) * ∏ j : {j // l j = 0}, v j.1) *
            ((∏ a ∈ T.erase 0, ∏ i : {i // k i = a}, u i.1) *
              ∏ a ∈ T.erase 0, ∏ j : {j // l j = a}, v j.1)
          = ((∏ i : {i // k i = 0}, u i.1) * ∏ a ∈ T.erase 0, ∏ i : {i // k i = a}, u i.1) *
              ((∏ j : {j // l j = 0}, v j.1) * ∏ a ∈ T.erase 0, ∏ j : {j // l j = a}, v j.1) := by
            ac_rfl
        _ = (∏ i, u i) * ∏ j, v j := by
            rw [Finset.mul_prod_erase T (fun a ↦ ∏ i : {i // k i = a}, u i.1) h0T,
              prod_fiber_subtype k hkT u,
              Finset.mul_prod_erase T (fun a ↦ ∏ j : {j // l j = a}, v j.1) h0T,
              prod_fiber_subtype l hlT v]
    have hsq_pos : IsSquare
        (∏ a ∈ T.erase 0, ((∏ i : {i // k i = a}, u i.1) * ∏ j : {j // l j = a}, v j.1)) :=
      Finset.prod_induction _ IsSquare (fun _ _ ↦ IsSquare.mul) IsSquare.one fun a ha ↦
        (hpos a (Nat.pos_of_ne_zero (Finset.mem_erase.mp ha).1)).2
    refine ⟨hocc0, ?_⟩
    obtain ⟨s, hs⟩ := hsq_pos
    obtain ⟨t, ht⟩ := hsq_all
    refine ⟨t * s⁻¹, ?_⟩
    have hmul' : ((∏ i : {i // k i = 0}, u i.1) * ∏ j : {j // l j = 0}, v j.1) * (s * s) =
        t * t := by rw [← hs, hmul, ht]
    calc (∏ i : {i // k i = 0}, u i.1) * ∏ j : {j // l j = 0}, v j.1
        = (((∏ i : {i // k i = 0}, u i.1) * ∏ j : {j // l j = 0}, v j.1) * (s * s)) *
            (s⁻¹ * s⁻¹) := by simp [mul_assoc]
      _ = (t * s⁻¹) * (t * s⁻¹) := by rw [hmul', mul_mul_mul_comm]
  · exact hpos m hm

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
    hp_odd k l (fun i ↦ isCoprime_of_dvd_unit_sub (hθ_p i))
    (fun j ↦ isCoprime_of_dvd_unit_sub (hη_p j))).mp ⟨e⟩
  refine ⟨hsum, fun m hm ↦ ?_⟩
  obtain ⟨hcnt, hleg⟩ := hpi m hm
  refine ⟨by rwa [occCount_eq_card_filter, occCount_eq_card_filter], ?_⟩
  rw [isSquare_prod_mul_prod_iff_prod_legendreSym_eq hp
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
`b` and `c` be orthogonal bases of the localizations `L_p` and `M_p` of two nondegenerate integral
lattices, with `B(bᵢ, bᵢ) = uᵢ pᵏⁱ` and `B(cⱼ, cⱼ) = vⱼ pˡʲ` for units `uᵢ, vⱼ ∈ ℤ_pˣ`. Then `L_p`
and `M_p` are integrally isometric if and only if, at every scale `m ≥ 0` (including the unimodular
scale `m = 0`), they have the same number of summands of scale `p^m` and the products of the unit
parts at scale `p^m` agree modulo squares in `ℤ_pˣ`. -/
theorem localIntegralForm_equivalent_iff_forall_occCount_eq_and_isSquare
    {V W : Type*} [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]
    {L : IntegralLattice V} {M : IntegralLattice W} [L.IsNondegenerate] [M.IsNondegenerate]
    {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) {ι κ : Type*} [Fintype ι] [Fintype κ]
    {b : Basis ι ℤ_[p] (L.LocalCarrier p)} {c : Basis κ ℤ_[p] (M.LocalCarrier p)}
    {u : ι → ℤ_[p]ˣ} {v : κ → ℤ_[p]ˣ} {k : ι → ℕ} {l : κ → ℕ}
    (hb : (L.localIntegralForm p).iIsOrtho b)
    (hbu : ∀ i, L.localIntegralForm p (b i) (b i) = u i * (p : ℤ_[p]) ^ k i)
    (hc : (M.localIntegralForm p).iIsOrtho c)
    (hcv : ∀ j, M.localIntegralForm p (c j) (c j) = v j * (p : ℤ_[p]) ^ l j) :
    (L.localIntegralForm p).Equivalent (M.localIntegralForm p) ↔
      ∀ m : ℕ, occCount k m = occCount l m ∧
        IsSquare ((∏ i : {i // k i = m}, u i) * ∏ j : {j // l j = m}, v j) := by
  classical
  refine ⟨fun heq ↦ ?_,
    equivalent_localIntegralForm_of_forall_occCount_eq_and_isSquare hp hb hbu hc hcv⟩
  obtain ⟨φ⟩ := id heq
  have hcard : Fintype.card ι = Fintype.card κ := by
    have h := φ.toLinearEquiv.finrank_eq
    rwa [Module.finrank_eq_card_basis b, Module.finrank_eq_card_basis c] at h
  obtain ⟨hsum, hpos⟩ := sum_eq_and_pos_invariants_of_primaryDiscriminantBilinear hp hb hbu hc hcv
    ⟨primaryDiscriminantBilinearIsometry φ⟩
  let σ : κ ≃ ι := Fintype.equivOfCardEq hcard.symm
  have hdet := heq.isSquare_det_mul_det b (c.reindex σ)
  rw [LinearMap.BilinForm.det_toMatrix_reindex, hb.det_toMatrix, hc.det_toMatrix] at hdet
  simp_rw [hbu, hcv, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hsum] at hdet
  have hp_ne : (p : ℤ_[p]) ^ ∑ j, l j ≠ 0 :=
    pow_ne_zero _ (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)
  have hdet' : IsSquare
      ((((∏ i, u i) * ∏ j, v j : ℤ_[p]ˣ) : ℤ_[p]) * ((p : ℤ_[p]) ^ ∑ j, l j) ^ 2) := by
    convert hdet using 1
    push_cast
    ring
  have hsq_all : IsSquare ((∏ i, u i) * ∏ j, v j) :=
    Units.isSquare_coe_iff.mp (hdet'.of_mul_right (pow_ne_zero 2 hp_ne) (IsSquare.sq _))
  exact forall_occCount_eq_and_isSquare_of_pos hcard hsq_all hpos

/-- **Uniqueness of diagonal Jordan invariants at an odd prime.** Any two diagonal Jordan bases of
the localization `L_p` of a nondegenerate integral lattice at an odd prime `p` have the same
multiplicity and the same unit determinant square class at every scale `p^m`, `m ≥ 0`. -/
theorem occCount_eq_and_isSquare_of_iIsOrtho_localIntegralForm
    {V : Type*} [AddCommGroup V] [Module ℚ V] {L : IntegralLattice V} [L.IsNondegenerate]
    {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) {ι κ : Type*} [Fintype ι] [Fintype κ]
    {b : Basis ι ℤ_[p] (L.LocalCarrier p)} {c : Basis κ ℤ_[p] (L.LocalCarrier p)}
    {u : ι → ℤ_[p]ˣ} {v : κ → ℤ_[p]ˣ} {k : ι → ℕ} {l : κ → ℕ}
    (hb : (L.localIntegralForm p).iIsOrtho b)
    (hbu : ∀ i, L.localIntegralForm p (b i) (b i) = u i * (p : ℤ_[p]) ^ k i)
    (hc : (L.localIntegralForm p).iIsOrtho c)
    (hcv : ∀ j, L.localIntegralForm p (c j) (c j) = v j * (p : ℤ_[p]) ^ l j) (m : ℕ) :
    occCount k m = occCount l m ∧
      IsSquare ((∏ i : {i // k i = m}, u i) * ∏ j : {j // l j = m}, v j) :=
  (localIntegralForm_equivalent_iff_forall_occCount_eq_and_isSquare hp hb hbu hc hcv).mp
    (LinearMap.BilinForm.Equivalent.refl (L.localIntegralForm p)) m

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
  have hfin : finrank ℤ_[p] (K.LocalCarrier p) = finrank ℤ K := by
    have := Module.finrank_eq_card_basis ((Module.finBasis ℤ K).baseChange ℤ_[p])
    simp [this]
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
    have hcard : Fintype.card (Fin (finrank ℤ_[p] (L.LocalCarrier p))) =
        Fintype.card (Fin (finrank ℤ_[p] (M.LocalCarrier p))) := by
      have hfinL := Module.finrank_eq_card_basis ((Module.finBasis ℤ L).baseChange ℤ_[p])
      have hfinM := Module.finrank_eq_card_basis ((Module.finBasis ℤ M).baseChange ℤ_[p])
      simp [hfinL, hfinM, hrank]
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
    exact (localIntegralForm_equivalent_iff_forall_occCount_eq_and_isSquare hp hb hbu hc hcv).mpr
      (forall_occCount_eq_and_isSquare_of_pos hcard hsq_all hpos)

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
      (primaryComponent (L.discriminantQuadraticModule hL) p))) := by
    -- The carrier of `(L.discriminantQuadraticModule hL).restrict P` is definitionally `P`.
    change Odd (Nat.card (primaryComponent L.DiscriminantGroup p))
    rw [TauCeti.AddCommGroup.natCard_primaryComponent _ Fact.out]
    exact ((Fact.out : p.Prime).odd_of_ne_two hp).pow
  rw [localIntegralForm_equivalent_iff_primaryDiscriminantBilinear L M hp,
    FiniteQuadraticModule.nonempty_isometry_iff_bilinear_isometry_of_odd hodd]
  rfl

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
