/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.ThetaSeries.BoundedAtCusp
public import TauCeti.NumberTheory.ModularForms.ThetaSeries.GaussSum
public import TauCeti.NumberTheory.ModularForms.ThetaSeries.QExpansion
import TauCeti.Algebra.Module.ZLattice.Milgram
import TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.PositiveOdd.Slash

/-!
# Coset theta series as principal-congruence modular forms

For an even full lattice `L` of rank `2k` and level `N`, the theta series of every class in
`L^∨ / L` is a modular form of weight `k` on `Γ(N)`. The bundled form `ZLattice.thetaCosetForm`
is indexed by the discriminant group, so it is independent of a choice of representative.
Its coercion is `thetaCosetClass`, and its expansion in `q_N = exp (2 π i τ / N)` has the coset
representation numbers as coefficients.

The coset-splitting formula and the evaluated Gauss sum give invariance first for matrices
whose lower-left entry is positive and whose upper-left entry is positive and odd. The Jacobi
symbol is `1` because that upper-left entry is congruent to `1` modulo `N`. The general
principal-congruence reduction uses inversion and translations by multiples of `N`, not matrix
negation or arbitrary translations, which need not preserve `Γ(N)`. At levels dividing `2`,
the weight is even by Milgram's theorem, so the central element `-I` also acts trivially.
Holomorphy and boundedness at every rational cusp then supply the analytic conditions.

## Main statements

* `ZLattice.IsEven.thetaCoset_slash_of_mem_Gamma`: invariance for every matrix of `Γ(N)`.
* `ZLattice.thetaCosetForm`: the modular form associated to a discriminant class.
* `ZLattice.qExpansion_thetaCosetForm_coeff`: its coefficients count vectors in the coset.

## References

* B. Schoeneberg, *Elliptic Modular Functions*, Chapter IX.
* W. Ebeling, *Lattices and Codes*, third edition, Chapter 3.
-/

public section

open Module Matrix.SpecialLinearGroup UpperHalfPlane
open scoped MatrixGroups ModularForm

namespace ZLattice

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {L : Submodule ℤ E} [DiscreteTopology L] [IsZLattice ℝ L] {k : ℕ}

/-- The theta series of every dual coset of an even full lattice of rank `2k` and level `N`
is invariant in weight `k` under every matrix of the principal congruence subgroup `Γ(N)`. -/
theorem IsEven.thetaCoset_slash_of_mem_Gamma (hL : IsEven L) (hk : finrank ℝ E = 2 * k)
    {γ : E} (hγ : γ ∈ dual L) {A : SL(2, ℤ)}
    (hA : A ∈ CongruenceSubgroup.Gamma (level L)) :
    thetaCoset L γ ∣[(k : ℤ)] A = thetaCoset L γ := by
  borelize E
  apply TauCeti.ModularForm.slash_eq_self_of_mem_Gamma_of_pos_odd
    (hL.thetaCoset_slash_T_zpow_level hγ k) ?_ ?_ hA
  · intro h2
    have heven : Even (k : ℤ) := by exact_mod_cast hL.even_of_level_dvd_two h2 hk
    simp [heven.neg_one_zpow]
  · intro B hB hc ha hao
    obtain ⟨a, haeq⟩ := Int.eq_ofNat_of_zero_le ha.le
    obtain ⟨c, hceq⟩ := Int.eq_ofNat_of_zero_le hc.le
    have : NeZero c := ⟨by omega⟩
    have haodd : Odd a := by rw [haeq] at hao; exact_mod_cast hao
    have hN : level L ∣ c := by
      have h := (CongruenceSubgroup.Gamma_mem.mp hB).2.2.1
      rw [hceq] at h
      exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h
    have hmod : a ≡ 1 [MOD level L] := by
      have h := (CongruenceSubgroup.Gamma_mem.mp hB).1
      rw [haeq] at h
      exact (ZMod.natCast_eq_natCast_iff a 1 (level L)).mp (by simpa using h)
    have hcop : a.Coprime c := by
      have h := B.isCoprime_col 0
      rw [haeq, hceq] at h
      exact h.natCoprime
    rw [hL.thetaCoset_slash_eq_gaussSum_smul_of_mem_Gamma hk hB hceq ⟨γ, hγ⟩, haeq,
      hL.normalized_gaussSum_eq_jacobiSym hk haodd hN hcop,
      ← signedDiscr_of_finrank_eq L hk, hL.jacobiSym_signedDiscr_eq_one hk haodd hmod,
      Int.cast_one, one_smul]

/-- The theta series of a discriminant class is invariant under the principal congruence
subgroup at the lattice's level, in weight half the rank. -/
theorem IsEven.thetaCosetClass_slash_of_mem_Gamma (hL : IsEven L)
    (hk : finrank ℝ E = 2 * k) (δ : DiscriminantGroup L) {A : SL(2, ℤ)}
    (hA : A ∈ CongruenceSubgroup.Gamma (level L)) :
    thetaCosetClass L δ ∣[(k : ℤ)] A = thetaCosetClass L δ := by
  induction δ using Submodule.Quotient.induction_on with
  | H γ => simpa using hL.thetaCoset_slash_of_mem_Gamma hk γ.2 hA

/-- The coset theta series of a discriminant class of an even full lattice, as a modular form
of weight half the rank on the principal congruence subgroup at the lattice's level. -/
noncomputable def thetaCosetForm (hL : IsEven L) (hk : finrank ℝ E = 2 * k)
    (δ : DiscriminantGroup L) :
    ModularForm ((CongruenceSubgroup.Gamma (level L)).map (mapGL ℝ)) k where
  toFun := thetaCosetClass L δ
  slash_action_eq' A hA := by
    obtain ⟨A, hA, rfl⟩ := hA
    exact hL.thetaCosetClass_slash_of_mem_Gamma hk δ hA
  holo' := by
    induction δ using Submodule.Quotient.induction_on with
    | H γ => simpa using mdifferentiable_thetaCoset L (γ : E)
  bdd_at_cusps' hc := by
    induction δ using Submodule.Quotient.induction_on with
    | H γ =>
      simpa using hL.isBoundedAt_thetaCoset hk γ.2 (hc.mono (Subgroup.map_le_range _ _))

/-- The underlying function of the coset theta form is the theta series of its class. -/
@[simp]
theorem coe_thetaCosetForm (hL : IsEven L) (hk : finrank ℝ E = 2 * k)
    (δ : DiscriminantGroup L) : ⇑(thetaCosetForm hL hk δ) = thetaCosetClass L δ :=
  (rfl)

/-- The coefficients of a coset theta form in `q_N = exp (2 π i τ / N)` count the vectors in
that coset of squared norm `2m / N`, where `N` is the lattice's level. -/
theorem qExpansion_thetaCosetForm_coeff (hL : IsEven L) (hk : finrank ℝ E = 2 * k)
    (δ : DiscriminantGroup L) (m : ℕ) :
    (qExpansion (level L) (thetaCosetForm hL hk δ)).coeff m =
      cosetRepresentationNumberClass L δ (2 * m / level L) := by
  rw [coe_thetaCosetForm, hL.qExpansion_level_thetaCosetClass_coeff]

end ZLattice
