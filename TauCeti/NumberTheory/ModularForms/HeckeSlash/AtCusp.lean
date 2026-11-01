/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.Cusps.ConstantTerm
public import TauCeti.NumberTheory.ModularForms.HeckeSlash.Operators

import TauCeti.NumberTheory.ModularForms.Cusps.Basic
import TauCeti.Data.ZMod.Divisibility
import TauCeti.NumberTheory.ModularForms.HeckeSlash.Diagonal.QExpansion
import TauCeti.NumberTheory.ModularForms.HeckeSlash.Independence
import TauCeti.NumberTheory.ModularForms.HeckeSlash.UpperTri.QExpansion

/-!
# The Hecke operator `Tₚ` at the other cusps

For a prime `p ∤ N`, the `q`-expansion of `Tₚ f` at `∞` is read off from the expansion of `f`
at `∞` and of `⟨p⟩ f` at `∞` (`HeckeSlash/Recurrence.lean`). This file computes the expansion of
`Tₚ f` at every other cusp. For `γ ∈ SL₂(ℤ)` the proof writes

`(Tₚ f) ∣ γ = ∑_{c < p} (f ∣ δ₁) ∣ !![1, N c; 0, p]  +  (f ∣ δ₂) ∣ !![p, 0; 0, 1]`

for suitable `δ₁, δ₂ ∈ SL₂(ℤ)`, so that at the common period `N` of all the cusps of `Γ₁(N)`

`aₙ((Tₚ f) ∣ γ) = a_{p n}(f ∣ δ₁) + p^{k−1} a_{n/p}(f ∣ δ₂)`,

where the second term is present only when `p ∣ n`. The expansion of `Tₚ f` at one cusp is thus
assembled from the expansions of `f` at two other cusps. This is the computation behind
Deligne–Serre's observation that the forms whose expansions at *all* cusps are integral are
stable under `Tₚ`.

The decomposition comes from the right cosets of `Γ₁(N) · diag(1, p) · Γ₁(N)`. Each
representative `r` is `diag(1, p) · ρ` with `ρ ∈ Γ₁(N)`. Every `diag(1, p) · g` with
`g ∈ SL₂(ℤ)` factors as `ξ · u` with `ξ ∈ SL₂(ℤ)` and `u` one of the `p + 1` matrices
`!![1, N c; 0, p]` (`c < p`) and `!![p, 0; 0, 1]`. The offsets `N c` run over all residues
modulo `p` because `p ∤ N`. Applied to `r γ`, the factorisation sends the `p + 1` representatives
bijectively to these matrices, since the `r` lie in distinct right cosets of `SL₂(ℤ)`. The left
factors `ξ` attached to the upper-triangular matrices all lie in one right coset of `Γ₁(N)`.
The reason is that `!![1, N c; 0, p]⁻¹ · !![1, N c'; 0, p] = T^{N (c' − c)}` lies in `Γ(N)`.
The offsets `N c`, rather than `c`, make this work; with them the roots of unity in the
expansion at period `N` are `p`-th roots of unity, and they sum to `p` or `0`.

## Main results

* `HeckeRing.GL2.exists_qExpansion_coeff_translate_heckeTNat`: the expansion of `Tₚ f` at any
  cusp, at period `N`, in terms of the expansions of `f` at two cusps.

## References

* [F. Diamond and J. Shurman, *A first course in modular forms*][diamondshurman2005],
  Proposition 5.2.1.
* P. Deligne and J.-P. Serre, *Formes modulaires de poids 1*, Ann. Sci. École Norm. Sup. (4) 7
  (1974), 507–530, §2.7.
-/

public section

open Matrix Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup HeckeRing.GLn Function
  ModularForm

open scoped MatrixGroups ModularForm Manifold Pointwise

local notation "𝕢" => Function.Periodic.qParam

namespace HeckeRing.GL2

variable {N p : ℕ} (k : ℤ)

local notation "D" => natDiagGL 2 ![1, p]

/-- `diag(1, p) · T ^ (N c) = !![1, N c; 0, p]`. -/
private noncomputable def shiftRep (N p : ℕ) (c : Fin p) : GL (Fin 2) ℚ :=
  natDiagGL 2 ![1, p] * mapGL ℚ (ModularGroup.T ^ ((N : ℤ) * c))

/-- The matrix of `shiftRep N p c`. -/
private lemma coe_shiftRep (hp : 0 < p) (c : Fin p) :
    (↑(shiftRep N p c) : Matrix (Fin 2) (Fin 2) ℚ) = !![1, (N : ℚ) * c; 0, (p : ℚ)] := by
  rw [shiftRep, Units.val_mul, coe_natDiagGL_one hp, coe_mapGL_int_rat_fin_two,
    Matrix.mul_fin_two]
  simp [ModularGroup.coe_T_zpow]

/-- The `p + 1` matrices `!![1, N c; 0, p]` and `!![p, 0; 0, 1]`. -/
private noncomputable def shiftPrimeRep (N p : ℕ) : Option (Fin p) → GL (Fin 2) ℚ
  | some c => shiftRep N p c
  | none => scaleRep p

@[simp] private lemma shiftPrimeRep_some (c : Fin p) :
    shiftPrimeRep N p (some c) = shiftRep N p c := (rfl)

@[simp] private lemma shiftPrimeRep_none : shiftPrimeRep N p none = scaleRep p := (rfl)

/-- Every `diag(1, p) · g` lies in `SL₂(ℤ) · shiftPrimeRep N p j` for some `j`. -/
private lemma exists_natDiagGL_mul_eq_mul_shiftPrimeRep (hp : p.Prime) (hpN : p.Coprime N)
    (g : SL(2, ℤ)) : ∃ (ξ : SL(2, ℤ)) (j : Option (Fin p)),
      D * mapGL ℚ g = mapGL ℚ ξ * shiftPrimeRep N p j := by
  have hg := Matrix.SpecialLinearGroup.fin_two_mul_sub_mul_eq_one g
  by_cases hpa : (p : ℤ) ∣ g 0 0
  · obtain ⟨a, ha⟩ := hpa
    obtain ⟨ξ, e00, e01, e10, e11⟩ : ∃ ξ : SL(2, ℤ), ξ 0 0 = a ∧ ξ 0 1 = g 0 1 ∧
        ξ 1 0 = g 1 0 ∧ ξ 1 1 = p * g 1 1 :=
      ⟨⟨!![a, g 0 1; g 1 0, p * g 1 1], by
        rw [Matrix.det_fin_two_of]
        linear_combination hg - g 1 1 * ha⟩, rfl, rfl, rfl, rfl⟩
    refine ⟨ξ, none, Units.ext ?_⟩
    have haQ : ((g 0 0 : ℤ) : ℚ) = p * a := by exact_mod_cast ha
    rw [Units.val_mul, Units.val_mul, coe_natDiagGL_one hp.pos, coe_mapGL_int_rat_fin_two,
      coe_mapGL_int_rat_fin_two, shiftPrimeRep, coe_scaleRep p hp.pos, Matrix.mul_fin_two,
      Matrix.mul_fin_two, e00, e01, e10, e11, haQ]
    congrm !![?_, ?_; ?_, ?_] <;> push_cast <;> ring
  · have : NeZero p := ⟨hp.ne_zero⟩
    have hunit : IsUnit (((g 0 0 * N : ℤ) : ℤ) : ZMod p) := by
      rw [Int.cast_mul, IsUnit.mul_iff, CharP.isUnit_intCast_iff hp, Int.cast_natCast]
      exact ⟨hpa, (ZMod.isUnit_iff_coprime N p).mpr hpN.symm⟩
    obtain ⟨c, t, ht⟩ : ∃ (c : Fin p) (t : ℤ), g 0 1 - (c : ℤ) * (g 0 0 * N) = p * t := by
      obtain ⟨j, t, hj⟩ := ZMod.exists_dvd_sub_val_mul p (g 0 1) (g 0 0 * N) hunit
      exact ⟨⟨j.val, j.val_lt⟩, t, hj⟩
    obtain ⟨ξ, e00, e01, e10, e11⟩ : ∃ ξ : SL(2, ℤ), ξ 0 0 = g 0 0 ∧ ξ 0 1 = t ∧
        ξ 1 0 = p * g 1 0 ∧ ξ 1 1 = g 1 1 - g 1 0 * N * c :=
      ⟨⟨!![g 0 0, t; p * g 1 0, g 1 1 - g 1 0 * N * c], by
        rw [Matrix.det_fin_two_of]
        linear_combination hg + g 1 0 * ht⟩, rfl, rfl, rfl, rfl⟩
    refine ⟨ξ, some c, Units.ext ?_⟩
    have htQ : ((g 0 1 : ℤ) : ℚ) - (c : ℚ) * ((g 0 0 : ℤ) * N) = p * t := by exact_mod_cast ht
    rw [Units.val_mul, Units.val_mul, coe_natDiagGL_one hp.pos, coe_mapGL_int_rat_fin_two,
      coe_mapGL_int_rat_fin_two, shiftPrimeRep, coe_shiftRep hp.pos, Matrix.mul_fin_two,
      Matrix.mul_fin_two, e00, e01, e10, e11]
    push_cast
    congrm !![?_, ?_; ?_, ?_]
    · ring
    · linear_combination htQ
    · ring
    · ring

/-- If `E · diag(1, p) = diag(1, p) · A` with `A ∈ Γ₁(N)`, then `E ∈ Γ₁(N)`: the lower rows are
`(p A₁₀, A₁₁)` and `(A₁₀, A₁₁)` scaled by `p`. -/
private lemma mem_Gamma1_of_mul_natDiagGL_eq (hp : 0 < p) {E A : SL(2, ℤ)} (hA : A ∈ Gamma1 N)
    (h : mapGL ℚ E * D = D * mapGL ℚ A) : E ∈ Gamma1 N := by
  have hmat := congrArg (fun x : GL (Fin 2) ℚ ↦ (x : Matrix (Fin 2) (Fin 2) ℚ)) h
  simp only [Units.val_mul, coe_natDiagGL_one hp, coe_mapGL_int_rat_fin_two,
    Matrix.mul_fin_two] at hmat
  have hp0 : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne'
  have h10 : E 1 0 = p * A 1 0 := by
    have : ((E 1 0 : ℤ) : ℚ) = p * A 1 0 := by simpa using congrFun (congrFun hmat 1) 0
    exact_mod_cast this
  have h11 : E 1 1 = A 1 1 := by
    have := congrFun (congrFun hmat 1) 1
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one, Matrix.empty_val',
      Matrix.cons_val_fin_one] at this
    have : ((E 1 1 : ℤ) : ℚ) = A 1 1 := by
      apply mul_left_cancel₀ hp0
      linear_combination this
    exact_mod_cast this
  obtain ⟨hc, hd⟩ := mem_Gamma1_iff_dvd_lowerRow.mp hA
  exact mem_Gamma1_of_dvd_lowerRow (h10 ▸ hc.mul_left _) (h11 ▸ hd)

/-- Two factorizations `diag(1, p) · g = ξ · !![1, N c; 0, p]` through the upper-triangular
representatives, with `g, g'` in the same right coset of `Γ₁(N)`, have `ξ, ξ'` in the same right
coset of `Γ₁(N)`. -/
private lemma mul_inv_mem_Gamma1_of_eq_mul_shiftRep (hp : 0 < p) {g g' ξ ξ' : SL(2, ℤ)}
    {c c' : Fin p}
    (h : D * mapGL ℚ g = mapGL ℚ ξ * shiftRep N p c)
    (h' : D * mapGL ℚ g' = mapGL ℚ ξ' * shiftRep N p c') (hg : g * g'⁻¹ ∈ Gamma1 N) :
    ξ * ξ'⁻¹ ∈ Gamma1 N := by
  have hA : g * ModularGroup.T ^ ((N : ℤ) * c' - N * c) * g'⁻¹ ∈ Gamma1 N := by
    have : g * ModularGroup.T ^ ((N : ℤ) * c' - N * c) * g'⁻¹ =
        (g * g'⁻¹) * (g' * ModularGroup.T ^ ((N : ℤ) * c' - N * c) * g'⁻¹) := by
      group
    rw [this]
    refine mul_mem hg (Gamma_le_Gamma1 N ((Gamma_normal N).conj_mem _ ?_ g'))
    simpa using ModularGroup_T_pow_mem_Gamma N _ ⟨_, (mul_sub _ _ _).symm⟩
  refine mem_Gamma1_of_mul_natDiagGL_eq hp hA ?_
  rw [shiftRep, map_zpow] at h h'
  simp only [map_mul, map_inv, map_zpow, eq_mul_inv_iff_mul_eq.mpr h.symm,
    eq_mul_inv_iff_mul_eq.mpr h'.symm]
  group

/-- **`Tₚ f` translated to a cusp, as a slash sum.** The proof translates the `p + 1` right-coset
representatives `r = diag(1, p) · ρ` of `Γ₁(N) · diag(1, p) · Γ₁(N)` by `γ`, factors each `r γ`
as `ξ · u` with `u` one of the `shiftPrimeRep` matrices, checks that `r ↦ u` is a bijection, and
finally that the `ξ` paired with the upper-triangular `u` all lie in one right coset of
`Γ₁(N)`, so that they slash `f` alike. -/
private lemma exists_slash_heckeTNat_eq [NeZero N] (hp : p.Prime) (hpN : p.Coprime N)
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) (γ : SL(2, ℤ)) :
    ∃ δ₁ δ₂ : SL(2, ℤ), ⇑(heckeTNat k p (_hn := ⟨hp.ne_zero⟩) f) ∣[k] mapGL ℚ γ =
      ∑ c : Fin p, ⇑f ∣[k] (mapGL ℚ δ₁ * shiftRep N p c) + ⇑f ∣[k] (mapGL ℚ δ₂ * scaleRep p) := by
  have : NeZero p := ⟨hp.ne_zero⟩
  have hσ10 := gamma0Twist_apply_one_zero hpN
  have hσ11 := gamma0Twist_apply_one_one hpN
  have hT : ⇑(heckeTNat k p f) = ∑ i, ⇑f ∣[k] primeRep (gamma0Twist N p hpN) p i := by
    rw [coe_heckeTNat]
    exact heckeSlashSum_coe_eq_sum_of_rightCosets k (diagCosetGamma1 N p) _
      (doubleCoset_out_diagCosetGamma1_eq_iUnion_rightCosets_of_prime hp hσ10 hσ11)
      (op_primeRep_smul_injective (G := Gamma1 N) hp.one_lt hσ11) f
  -- each representative of the double coset is `diag(1, p)` times an element of `Γ₁(N)`
  have hρ : ∀ i, ∃ ρ ∈ Gamma1 N, D * mapGL ℚ ρ = primeRep (gamma0Twist N p hpN) p i := by
    rintro (_ | b)
    · exact exists_mem_Gamma1_natDiagGL_mul_eq_primeRep_none hp.pos hσ10 hσ11
    · exact ⟨ModularGroup.T ^ (b : ℤ), T_zpow_mem_Gamma1 N _,
        (natDiagGL_mul_mapGL_T_zpow hp.pos b).trans (primeRep_some _ _ _).symm⟩
  choose ρ hρmem hρ using hρ
  choose ξ j hξ using fun i ↦ exists_natDiagGL_mul_eq_mul_shiftPrimeRep (N := N) hp hpN (ρ i * γ)
  have hrep : ∀ i, primeRep (gamma0Twist N p hpN) p i * mapGL ℚ γ =
      mapGL ℚ (ξ i) * shiftPrimeRep N p (j i) := fun i ↦ by
    rw [← hρ i, mul_assoc, ← map_mul, hξ i]
  -- the translated representatives lie in distinct right cosets of `SL₂(ℤ)`
  have hj : Function.Bijective j := by
    refine Finite.injective_iff_bijective.mp fun i i' hii' ↦
      op_primeRep_smul_injective (G := ⊤) hp.one_lt hσ11 ?_
    refine (rightCoset_eq_iff _).mpr ⟨ξ i' * (ξ i)⁻¹, Subgroup.mem_top _, ?_⟩
    rw [eq_mul_inv_iff_mul_eq.mpr (hrep i), eq_mul_inv_iff_mul_eq.mpr (hrep i'), hii',
      map_mul, map_inv]
    group
  let e := Equiv.ofBijective j hj
  have he : ∀ x, j (e.symm x) = x := Equiv.ofBijective_apply_symm_apply j hj
  set i₀ := e.symm (some ⟨0, hp.pos⟩)
  refine ⟨ξ i₀, ξ (e.symm none), ?_⟩
  rw [hT, SlashAction.sum_slash]
  simp_rw [← SlashAction.slash_mul, hrep]
  rw [← e.symm.sum_comp, Fintype.sum_option, add_comm, he, shiftPrimeRep_none]
  simp only [he, shiftPrimeRep_some]
  congr 1
  refine Finset.sum_congr rfl fun c _ ↦ ?_
  -- the upper-triangular terms all come from a single right coset of `Γ₁(N)`
  have h₁ := hξ (e.symm (some c))
  have h₀ := hξ i₀
  rw [he, shiftPrimeRep_some] at h₁ h₀
  have hg : ρ (e.symm (some c)) * γ * (ρ i₀ * γ)⁻¹ ∈ Gamma1 N := by
    simpa only [_root_.mul_inv_rev, mul_assoc, mul_inv_cancel_left] using
      mul_mem (hρmem (e.symm (some c))) (inv_mem (hρmem i₀))
  have hmem := mul_inv_mem_Gamma1_of_eq_mul_shiftRep hp.pos h₁ h₀ hg
  rw [SlashAction.slash_mul, SlashAction.slash_mul]
  congr 1
  calc ⇑f ∣[k] mapGL ℚ (ξ (e.symm (some c)))
      = ⇑f ∣[k] (mapGL ℚ (ξ (e.symm (some c)) * (ξ i₀)⁻¹) * mapGL ℚ (ξ i₀)) := by
        rw [← map_mul, inv_mul_cancel_right]
    _ = ⇑f ∣[k] mapGL ℚ (ξ i₀) := by
        rw [SlashAction.slash_mul,
          SlashInvariantFormClass.slash_eq_of_mem_map_mapGL f (Subgroup.mem_map_of_mem _ hmem)]

/-- **`Tₚ` at a cusp, for a prime `p ∤ N`.** For every `γ ∈ SL₂(ℤ)` there are
`δ₁, δ₂ ∈ SL₂(ℤ)` such that at the period `N`

`aₙ((Tₚ f) ∣ γ) = a_{p n}(f ∣ δ₁) + p^{k−1} a_{n/p}(f ∣ δ₂)`,

the second term being present only when `p ∣ n`. -/
theorem exists_qExpansion_coeff_translate_heckeTNat [NeZero N] (hp : p.Prime)
    (hpN : p.Coprime N) (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) (γ : SL(2, ℤ)) :
    ∃ δ₁ δ₂ : SL(2, ℤ), ∀ n : ℕ,
      (qExpansion N (translate (heckeTNat k p (_hn := ⟨hp.ne_zero⟩) f) (mapGL ℝ γ))).coeff n =
        (qExpansion N (translate f (mapGL ℝ δ₁))).coeff (p * n) +
          if p ∣ n then (p : ℂ) ^ (k - 1) * (qExpansion N (translate f (mapGL ℝ δ₂))).coeff (n / p)
          else 0 := by
  have : NeZero p := ⟨hp.ne_zero⟩
  have hΓ := Subgroup.map_mono (f := mapGL ℝ) (Gamma_le_Gamma1 N)
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hN' : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hNδ := TauCeti.natCast_mem_strictPeriods_conjAct_of_Gamma_le hΓ
  obtain ⟨δ₁, δ₂, hδ⟩ := exists_slash_heckeTNat_eq k hp hpN f γ
  refine ⟨δ₁, δ₂, fun n ↦ ?_⟩
  -- the translates of `f`, of level `δ⁻¹ Γ₁(N) δ`, are `N`-periodic and bounded at `i∞`
  have hper : ∀ δ : SL(2, ℤ), Periodic (⇑(translate f (mapGL ℝ δ)) ∘ ofComplex) N := fun δ ↦
    SlashInvariantFormClass.periodic_comp_ofComplex _ (hNδ δ)
  have hbdd : ∀ δ : SL(2, ℤ), IsBoundedAtImInfty ⇑(translate f (mapGL ℝ δ)) := fun δ ↦
    have : Fact (IsCusp OnePoint.infty
        (ConjAct.toConjAct (mapGL ℝ δ)⁻¹ • (Gamma1 N).map (mapGL ℝ))) :=
      ⟨Subgroup.isCusp_of_mem_strictPeriods hN' (hNδ δ)⟩
    ModularFormClass.bdd_at_infty _
  have hfun : ⇑(translate (heckeTNat k p f) (mapGL ℝ γ)) =
      ∑ c : Fin p, ⇑(translate f (mapGL ℝ δ₁)) ∣[k] shiftRep N p c +
        ⇑(translate f (mapGL ℝ δ₂)) ∣[k] scaleRep p := by
    simp only [coe_translate, ← ModularForm.rat_slash_mapGL, ← SlashAction.slash_mul, hδ]
  have hsum : ∀ τ : ℍ, HasSum (fun m : ℕ ↦
      ((qExpansion N (translate f (mapGL ℝ δ₁))).coeff (p * m) +
        if p ∣ m then (p : ℂ) ^ (k - 1) * (qExpansion N (translate f (mapGL ℝ δ₂))).coeff (m / p)
        else 0) • 𝕢 N (τ : ℂ) ^ m) (translate (heckeTNat k p f) (mapGL ℝ γ) τ) := fun τ ↦ by
    rw [hfun, Pi.add_apply, Finset.sum_apply]
    simp_rw [add_smul]
    exact (hasSum_qExpansion_sum_slash_of_coe_eq_upperTri k p hp.pos hN (coe_shiftRep hp.pos)
      (hper δ₁) (ModularFormClass.holo _) (hbdd δ₁) τ).add
      (scaleRep_def p ▸ TauCeti.hasSum_slash_natDiagGL_d_one k hN (hper δ₂)
        (ModularFormClass.holo _) (hbdd δ₂) τ)
  exact (TauCeti.UpperHalfPlane.qExpansion_coeff_unique hN'
    (ModularFormClass.analyticAt_cuspFunction_zero (translate (heckeTNat k p f) (mapGL ℝ γ))
      hN' (hNδ γ)) hsum n).symm

end HeckeRing.GL2
