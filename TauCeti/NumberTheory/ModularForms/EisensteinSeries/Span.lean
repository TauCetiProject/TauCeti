/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.EisensteinSeries.Subspace
public import TauCeti.NumberTheory.ModularForms.EisensteinSeries.Congruence
import TauCeti.Data.ZMod.Divisibility

/-!
# Character Eisenstein series in the primitive Eisenstein span

Residue-weighted lattice Eisenstein series are finite linear combinations of the primitive
residue-class series. The coefficient of the primitive class `a` is the absolutely convergent
sum `∑' r : ℕ, r⁻ᵏ W(r • a)`. Consequently every residue-weighted Eisenstein series belongs to
the primitive Eisenstein subspace.

The same inclusion holds for every raised character Eisenstein series, including its normalized
form. Restricting the raised lattice sum to `Γ(N)` gives a residue-weighted series by replacing
the first lattice coordinate with its multiple by the raising parameter. Thus the existing
prescribed-nebentypus Eisenstein subspace is contained in the congruence Eisenstein subspace,
and its intersection with the image of the cusp forms of that nebentypus is zero.

The decomposition uses `weightedEisensteinSeries_eq_tsum_eisensteinSeries`, which separates
integer pairs by their gcd and primitive residue class.

## Main results

* `weightedEisensteinSeriesMF_eq_sum_eisensteinSeriesMF`: the finite primitive decomposition.
* `charEisensteinSeriesMFRaise_mem_congruenceEisensteinSubspace`: the raised character inclusion.
* `TauCeti.disjoint_eisensteinSubspace_range_cuspToModFormCharSpace`: directness of the character
  Eisenstein span and the cusp-form image in weight at least three.

## References

* [F. Diamond and J. Shurman, *A first course in modular forms*][diamondshurman2005],
  Sections 4.2 and 4.5.
-/

public noncomputable section

open ModularForm UpperHalfPlane CongruenceSubgroup
open _root_.EisensteinSeries
open scoped MatrixGroups

namespace TauCeti.EisensteinSeries

variable {N : ℕ} {k : ℤ} [NeZero N] (W : (Fin 2 → ZMod N) → ℂ)

/-- A residue-weighted Eisenstein series is a finite linear combination of the primitive
residue-class series, with coefficients obtained by summing over positive gcds. -/
theorem weightedEisensteinSeriesMF_eq_sum_eisensteinSeriesMF (hk : 3 ≤ k) :
    weightedEisensteinSeriesMF W hk =
      ∑ a, (∑' r : ℕ, ((r : ℂ) ^ k)⁻¹ * W (r • a)) • eisensteinSeriesMF hk a := by
  classical
  have hk' : -(k : ℝ) < -1 := by exact_mod_cast (by omega : -k < -1)
  have hscoeff (a : Fin 2 → ZMod N) :
      Summable fun r : ℕ ↦ ((r : ℂ) ^ k)⁻¹ * W (r • a) := by
    have hs : Summable fun r : ℕ ↦ ‖((r : ℂ) ^ k)⁻¹‖ := by
      simpa only [norm_inv, norm_zpow, Complex.norm_natCast, ← zpow_neg,
        ← Real.rpow_intCast, Int.cast_neg] using (Real.summable_nat_rpow.mpr hk')
    refine Summable.of_norm ((hs.mul_right (∑ b, ‖W b‖)).of_nonneg_of_le
      (fun _ ↦ norm_nonneg _) fun r ↦ ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left
      (Finset.single_le_sum (fun b _ ↦ norm_nonneg (W b)) (Finset.mem_univ (r • a)))
      (norm_nonneg _)
  ext z
  simp only [coe_weightedEisensteinSeriesMF, FunLike.coe_sum, Finset.sum_apply,
    FunLike.coe_smul, Pi.smul_apply, smul_eq_mul, coe_eisensteinSeriesMF]
  rw [weightedEisensteinSeries_eq_tsum_eisensteinSeries W hk z]
  simp_rw [Finset.mul_sum, ← mul_assoc]
  rw [Summable.tsum_finsetSum]
  · exact Finset.sum_congr rfl fun a _ ↦ tsum_mul_right
  · intro a _
    exact (hscoeff a).mul_right _

/-- Every residue-weighted Eisenstein series belongs to the primitive Eisenstein span. -/
theorem weightedEisensteinSeriesMF_mem_primitiveEisensteinSubspace (hk : 3 ≤ k) :
    weightedEisensteinSeriesMF W hk ∈ primitiveEisensteinSubspace N hk := by
  rw [weightedEisensteinSeriesMF_eq_sum_eisensteinSeriesMF W hk]
  exact Submodule.sum_mem _ fun a _ ↦ Submodule.smul_mem _ _
    (mem_primitiveEisensteinSubspace hk a)

variable {u v t : ℕ} (ψ : DirichletCharacter ℂ u) (φ : DirichletCharacter ℂ v)

private def raisedCharWeight (N t : ℕ) (ψ : DirichletCharacter ℂ u)
    (φ : DirichletCharacter ℂ v) (a : Fin 2 → ZMod N) : ℂ :=
  if t * v ∣ (a 0).val then
    ψ (((a 0).val / (t * v) : ℕ) : ZMod u) * φ⁻¹ ((a 1).val : ZMod v) else 0

private lemma raisedCharWeight_intCast (htuv : t * (u * v) ∣ N) (x : Fin 2 → ℤ) :
    raisedCharWeight N t ψ φ ((↑) ∘ x) =
      if ((t * v : ℕ) : ℤ) ∣ x 0 then
        ψ ((x 0 / ((t * v : ℕ) : ℤ) : ℤ) : ZMod u) * φ⁻¹ (x 1 : ZMod v) else 0 := by
  have hv : v ∣ N := (dvd_mul_left v u).trans ((dvd_mul_left (u * v) t).trans htuv)
  have hud : u * (t * v) ∣ N := by
    simpa only [mul_left_comm u t v] using htuv
  simp only [raisedCharWeight, Function.comp_apply]
  have h1 : (((x 1 : ZMod N).val : ℕ) : ZMod v) = (x 1 : ZMod v) := by
    rw [ZMod.natCast_val, ZMod.cast_intCast hv]
  have hdvd : t * v ∣ (x 0 : ZMod N).val ↔ ((t * v : ℕ) : ℤ) ∣ x 0 := by
    rw [← ZMod.natCast_eq_zero_iff, ZMod.natCast_val,
      ZMod.cast_intCast (dvd_of_mul_left_dvd hud), ZMod.intCast_zmod_eq_zero_iff_dvd]
  rw [h1]
  simp only [hdvd]
  split_ifs with h
  · rw [ZMod.natCast_val_div_eq_intCast_div hud h]
  · rfl

private lemma charEisensteinSeriesMFRaise_eq_weighted (hk : 3 ≤ k)
    (htuv : t * (u * v) ∣ N) :
    ModularForm.ofLe (Subgroup.map_mono (Gamma_le_Gamma1 N))
      (charEisensteinSeriesMFRaise ψ φ t hk htuv) =
        weightedEisensteinSeriesMF (raisedCharWeight N t ψ φ) hk := by
  let _ : NeZero t := NeZero.of_dvd (dvd_of_mul_right_dvd htuv)
  have ht0 : (t : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr (NeZero.ne t)
  let f : (Fin 2 → ℤ) → (Fin 2 → ℤ) := fun x ↦ ![(t : ℤ) * x 0, x 1]
  have hinj : Function.Injective f := by
    intro x y h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    simp only [f, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] at h0 h1
    ext i
    fin_cases i
    · exact mul_left_cancel₀ ht0 h0
    · exact h1
  ext z
  simp only [ModularForm.coe_ofLe, coe_weightedEisensteinSeriesMF,
    weightedEisensteinSeries_def]
  rw [charEisensteinSeriesMFRaise_apply_eq_tsum ψ φ hk htuv]
  -- The raised weight is supported on the image of the diagonal lattice embedding.
  have hsupp : Function.support (fun x : Fin 2 → ℤ ↦
      raisedCharWeight N t ψ φ ((↑) ∘ x) * eisSummand k x z) ⊆ Set.range f := by
    intro x hx
    have htv : ((t * v : ℕ) : ℤ) ∣ x 0 := by
      by_contra h
      exact hx (by
        dsimp only
        rw [raisedCharWeight_intCast ψ φ htuv, ite_eq_right h, zero_mul])
    have ht : (t : ℤ) ∣ x 0 := (dvd_mul_right (t : ℤ) v).trans (by exact_mod_cast htv)
    obtain ⟨c, hc⟩ := ht
    refine ⟨![c, x 1], ?_⟩
    ext i
    fin_cases i <;> simp [f, hc]
  -- Reindex along the embedding; division recovers the original first coordinate.
  rw [← hinj.tsum_eq hsupp]
  apply tsum_congr
  intro x
  rw [raisedCharWeight_intCast ψ φ htuv]
  have hdvd : ((t * v : ℕ) : ℤ) ∣ f x 0 ↔ (v : ℤ) ∣ x 0 := by
    simp only [f, Matrix.cons_val_zero, Nat.cast_mul]
    exact mul_dvd_mul_iff_left ht0
  simp only [hdvd]
  have hq : f x 0 / ((t * v : ℕ) : ℤ) = x 0 / v := by
    simp only [f, Matrix.cons_val_zero, Nat.cast_mul]
    exact Int.mul_ediv_mul_of_pos _ _ (Int.natCast_pos.mpr (NeZero.pos t))
  simp only [hq, f, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  congr 1
  simp [eisSummand, TauCeti.coe_scaleGL_smul, mul_assoc, mul_comm]

/-- Every raised character Eisenstein series belongs to the congruence Eisenstein span at
its target level, without requiring primitive characters or a parity assumption. -/
theorem charEisensteinSeriesMFRaise_mem_congruenceEisensteinSubspace (hk : 3 ≤ k)
    (htuv : t * (u * v) ∣ N) :
    charEisensteinSeriesMFRaise ψ φ t hk htuv ∈
      congruenceEisensteinSubspace (Gamma_le_Gamma1 N) hk := by
  rw [mem_congruenceEisensteinSubspace_iff,
    charEisensteinSeriesMFRaise_eq_weighted ψ φ hk htuv]
  exact weightedEisensteinSeriesMF_mem_primitiveEisensteinSubspace _ hk

/-- Every normalized raised character Eisenstein series belongs to the congruence Eisenstein
span at its target level. -/
theorem normalizedCharEisensteinSeriesMFRaise_mem_congruenceEisensteinSubspace
    {k : ℕ} (hk : 3 ≤ (k : ℤ)) (htuv : t * (u * v) ∣ N) :
    normalizedCharEisensteinSeriesMFRaise ψ φ t hk htuv ∈
      congruenceEisensteinSubspace (Gamma_le_Gamma1 N) hk := by
  rw [normalizedCharEisensteinSeriesMFRaise_eq_smul]
  exact Submodule.smul_mem _ _
    (charEisensteinSeriesMFRaise_mem_congruenceEisensteinSubspace ψ φ hk htuv)

/-- Every primitive, parity-compatible indexed character generator belongs to the congruence
Eisenstein span. -/
theorem CharIndex.form_mem_congruenceEisensteinSubspace {k : ℕ} (a : CharIndex N k)
    (hk : 3 ≤ (k : ℤ)) :
    a.form hk ∈ congruenceEisensteinSubspace (Gamma_le_Gamma1 N) hk := by
  rw [a.form_def]
  exact normalizedCharEisensteinSeriesMFRaise_mem_congruenceEisensteinSubspace
    a.psi a.phi hk a.level_dvd

end TauCeti.EisensteinSeries

namespace TauCeti

open TauCeti.EisensteinSeries
open _root_.Matrix.SpecialLinearGroup

variable {N k : ℕ} [NeZero N] (χ : (ZMod N)ˣ →* ℂˣ)

/-- The prescribed-nebentypus Eisenstein span is contained in the congruence Eisenstein span
after forgetting character-space membership. -/
theorem eisensteinSubspace_le_congruenceEisensteinSubspace (hk : 3 ≤ (k : ℤ)) :
    eisensteinSubspace χ hk ≤
      (congruenceEisensteinSubspace (Gamma_le_Gamma1 N) hk).comap
        (modFormCharSpace (k : ℤ) χ).subtype := by
  apply eisensteinSubspace_le
  intro a hχ
  simpa only [Submodule.mem_comap, Submodule.subtype_apply, CharIndex.coe_inCharSpace] using
    a.form_mem_congruenceEisensteinSubspace hk

/-- The prescribed-nebentypus Eisenstein subspace has zero intersection with the image of the
cusp forms of the same nebentypus, in weight at least three. -/
theorem disjoint_eisensteinSubspace_range_cuspToModFormCharSpace (hk : 3 ≤ (k : ℤ)) :
    Disjoint (eisensteinSubspace χ hk)
      (LinearMap.range (cuspToModFormCharSpace (k : ℤ) χ)) := by
  rw [Submodule.disjoint_def]
  intro f hfE hfS
  apply Subtype.ext
  have hfCE := eisensteinSubspace_le_congruenceEisensteinSubspace χ hk hfE
  have hfC : (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) (k : ℤ)) ∈
      cuspFormSubmodule ((Gamma1 N).map (mapGL ℝ)) (k : ℤ) := by
    obtain ⟨g, hg⟩ := hfS
    rw [← hg, coe_cuspToModFormCharSpace]
    exact CuspForm.isCuspForm_toModularFormₗ g.1
  exact (Submodule.disjoint_def.mp
    (disjoint_congruenceEisensteinSubspace_cuspFormSubmodule (Gamma_le_Gamma1 N) hk)) _
      hfCE hfC

end TauCeti
