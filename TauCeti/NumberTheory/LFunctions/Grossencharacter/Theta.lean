/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.Grossencharacter.ArchWeight
public import TauCeti.NumberTheory.LFunctions.Grossencharacter.FiniteCharacter
public import TauCeti.NumberTheory.LFunctions.Theta.Decay
import TauCeti.NumberTheory.NumberField.CanonicalEmbedding.IdealLattice
import TauCeti.NumberTheory.NumberField.CanonicalEmbedding.UnitAction

/-!
# Hecke's twisted theta series of a Grossencharacter

For a presented algebraic Hecke character `χ : Grossencharacter K 𝔪`, an integral ideal `𝔞` of
`𝓞 K`, and archimedean parameters `y : realSpace K`, Hecke's twisted theta series (Neukirch VII
(8.1)) is

`θ_χ(𝔞, y) = ε(χ) + ∑_{a ∈ 𝔞} χ_f(a) * χ.harmonicFactor (σ a) * archGaussian y (σ a)`,

where `σ = mixedEmbedding K`, `ε(χ) = χ.heckeEpsilon` is `1` when `χ` has trivial finite conductor
and `χ.harmonicDegree = 0` (and `0` otherwise), and `χ_f = χ.finiteCharacter` vanishes at `0` as
well as at integers not prime to `𝔪`.

## Main definitions

* `TauCeti.LFunctions.Grossencharacter.heckeTheta`: Hecke's twisted theta series `θ_χ(𝔞, y)`.

## Main results

* `TauCeti.LFunctions.Grossencharacter.summable_heckeTheta` and
  `TauCeti.LFunctions.Grossencharacter.summable_norm_heckeTheta`: absolute convergence for positive
  parameters `y`.
* `TauCeti.LFunctions.Grossencharacter.finiteCharacter_mul_harmonicFactor_unit` and
  `TauCeti.LFunctions.Grossencharacter.archWeight_mul_heckeTheta_unitScale`: unit invariance of
  `χ.archWeight y * χ.heckeTheta 𝔞 y` (Neukirch VII (8.2)).
* `TauCeti.LFunctions.Grossencharacter.continuousAt_heckeTheta`: continuity at positive parameters.
* `TauCeti.LFunctions.Grossencharacter.exists_norm_heckeTheta_sub_heckeEpsilon_le` and
  `TauCeti.LFunctions.Grossencharacter.exists_norm_heckeTheta_surfaceScale_sub_heckeEpsilon_le`:
  exponential decay of `χ.heckeTheta 𝔞 y - χ.heckeEpsilon`.
* `TauCeti.LFunctions.Grossencharacter.heckeTheta_ofRayClassCharacter_one`: at `Modulus.one K`, the
  trivial ray class character recovers `latticeTheta`.

## References

* E. Hecke, *Eine neue Art von Zetafunktionen und ihre Beziehungen zur Verteilung der Primzahlen
  (Zweite Mitteilung)*, Math. Z. **6** (1920), 11–51.
* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §8, (8.1)–(8.2).
-/

public section

noncomputable section

open Complex Filter NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
  TauCeti.NumberField.mixedEmbedding TauCeti.NumberField.Units
open scoped Real Topology nonZeroDivisors

namespace TauCeti.LFunctions.Grossencharacter

open GlobalNumberFields

variable {K : Type*} [Field K] [NumberField K] {𝔪 : Modulus K}

/-- **Hecke's twisted theta series** (Neukirch VII (8.1)) attached to a presentation `χ` of an
algebraic Hecke character, an integral ideal `𝔞` of `𝓞 K`, and archimedean parameters
`y : realSpace K`. -/
def heckeTheta (χ : Grossencharacter K 𝔪) (𝔞 : Ideal (𝓞 K)) (y : realSpace K) : ℂ :=
  χ.heckeEpsilon +
    ∑' a : 𝔞, χ.finiteCharacter (a : 𝓞 K) *
      χ.harmonicFactor (mixedEmbedding K ((a : 𝓞 K) : K)) *
      archGaussian y (mixedEmbedding K ((a : 𝓞 K) : K))

/-- The defining equation of `Grossencharacter.heckeTheta`. -/
theorem heckeTheta_def (χ : Grossencharacter K 𝔪) (𝔞 : Ideal (𝓞 K)) (y : realSpace K) :
    χ.heckeTheta 𝔞 y =
      χ.heckeEpsilon +
        ∑' a : 𝔞, χ.finiteCharacter (a : 𝓞 K) *
          χ.harmonicFactor (mixedEmbedding K ((a : 𝓞 K) : K)) *
          archGaussian y (mixedEmbedding K ((a : 𝓞 K) : K)) :=
  (rfl)

/-- For positive archimedean parameters `y`, the norms of the terms of `χ.heckeTheta 𝔞 y` are
summable. -/
theorem summable_norm_heckeTheta (χ : Grossencharacter K 𝔪) (𝔞 : Ideal (𝓞 K))
    {y : realSpace K} (hy : ∀ w, 0 < y w) :
    Summable fun a : 𝔞 ↦ ‖χ.finiteCharacter (a : 𝓞 K) *
      χ.harmonicFactor (mixedEmbedding K ((a : 𝓞 K) : K)) *
      archGaussian y (mixedEmbedding K ((a : 𝓞 K) : K))‖ := by
  let f : idealLattice K 1 → ℂ := fun x ↦
    χ.harmonicFactor (x : mixedSpace K) * archGaussian y (x : mixedSpace K)
  have hdom : Summable fun a : 𝔞 ↦ ‖f (idealToIntegerLattice 𝔞 a)‖ :=
    (χ.summable_harmonicFactor_mul_archGaussian (idealLattice K 1) y hy).norm.comp_injective
      (idealToIntegerLattice_injective 𝔞)
  refine Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun a ↦ ?_) hdom
  dsimp only [f]
  rw [coe_idealToIntegerLattice, norm_mul, norm_mul, mul_assoc, ← norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg (χ.harmonicFactor _ * archGaussian y _))
    (χ.norm_finiteCharacter_le_one (a : 𝓞 K))

/-- For positive archimedean parameters `y`, the defining series of `χ.heckeTheta 𝔞 y` is
summable. -/
theorem summable_heckeTheta (χ : Grossencharacter K 𝔪) (𝔞 : Ideal (𝓞 K))
    {y : realSpace K} (hy : ∀ w, 0 < y w) :
    Summable fun a : 𝔞 ↦ χ.finiteCharacter (a : 𝓞 K) *
      χ.harmonicFactor (mixedEmbedding K ((a : 𝓞 K) : K)) *
      archGaussian y (mixedEmbedding K ((a : 𝓞 K) : K)) :=
  (χ.summable_norm_heckeTheta 𝔞 hy).of_norm

/-- Monotone domination of `‖χ.heckeTheta 𝔞 y‖` by the absolute series majorant at any smaller
positive parameter `y' ≤ y`. -/
theorem norm_heckeTheta_le (χ : Grossencharacter K 𝔪) (𝔞 : Ideal (𝓞 K))
    {y y' : realSpace K} (hy' : ∀ w, 0 < y' w) (h : ∀ w, y' w ≤ y w) :
    ‖χ.heckeTheta 𝔞 y‖ ≤ ‖χ.heckeEpsilon‖ +
      ∑' a : 𝔞, ‖χ.finiteCharacter (a : 𝓞 K) *
        χ.harmonicFactor (mixedEmbedding K ((a : 𝓞 K) : K)) *
        archGaussian y' (mixedEmbedding K ((a : 𝓞 K) : K))‖ := by
  have hy : ∀ w, 0 < y w := fun w ↦ (hy' w).trans_le (h w)
  rw [heckeTheta_def]
  refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
  refine (norm_tsum_le_tsum_norm (χ.summable_norm_heckeTheta 𝔞 hy)).trans ?_
  refine (χ.summable_norm_heckeTheta 𝔞 hy).tsum_le_tsum (fun a ↦ ?_)
    (χ.summable_norm_heckeTheta 𝔞 hy')
  rw [norm_mul, norm_mul, norm_mul, norm_mul]
  exact mul_le_mul_of_nonneg_left (norm_archGaussian_le h _)
    (mul_nonneg (norm_nonneg _) (norm_nonneg _))

/-- On any global unit `u : (𝓞 K)ˣ`, multiplying `χ.finiteCharacter u` by
`χ.harmonicFactor (mixedEmbedding K u)` cancels all finite and archimedean signs and phases,
leaving `∏_w |u_w| ^ P_w`. -/
theorem finiteCharacter_mul_harmonicFactor_unit (χ : Grossencharacter K 𝔪) (u : (𝓞 K)ˣ) :
    χ.finiteCharacter (u : 𝓞 K) * χ.harmonicFactor (mixedEmbedding K (u : K)) =
      ((∏ w : InfinitePlace K,
        normAtPlace w (mixedEmbedding K (u : K)) ^ χ.harmonicExponent w : ℝ) : ℂ) := by
  rw [χ.finiteCharacter_unit u, χ.archimedeanValue_apply,
    Units.coe_prod, χ.prod_infiniteComponent_unit_mul_harmonicFactor u]

/-- **Unit invariance of Hecke's twisted theta series** (Neukirch VII (8.2)): for any unit
`u : (𝓞 K)ˣ` and any `y : realSpace K`,
`χ.archWeight (unitScale u y) * χ.heckeTheta 𝔞 (unitScale u y) = χ.archWeight y * χ.heckeTheta 𝔞 y`.
-/
theorem archWeight_mul_heckeTheta_unitScale (χ : Grossencharacter K 𝔪) (𝔞 : Ideal (𝓞 K))
    (u : (𝓞 K)ˣ) (y : realSpace K) :
    (χ.archWeight (unitScale u y) : ℂ) * χ.heckeTheta 𝔞 (unitScale u y) =
      (χ.archWeight y : ℂ) * χ.heckeTheta 𝔞 y := by
  set P : ℂ := ((∏ w : InfinitePlace K,
    normAtPlace w (mixedEmbedding K (u : K)) ^ χ.harmonicExponent w : ℝ) : ℂ)
  have hPeps : P * χ.heckeEpsilon = χ.heckeEpsilon := by
    by_cases hdeg : χ.harmonicDegree = 0
    · have hw : ∀ w, χ.harmonicExponent w = 0 := by
        classical simpa [harmonicDegree_def] using hdeg
      simp [P, hw]
    · simp [χ.heckeEpsilon_eq_zero_of_harmonicDegree_ne_zero hdeg]
  let e : 𝔞 ≃ 𝔞 :=
    Equiv.subtypeEquiv u.mulLeft fun _ ↦ (𝔞.unit_mul_mem_iff_mem u.isUnit).symm
  have hterm (a : 𝔞) :
      P * (χ.finiteCharacter (a : 𝓞 K) *
          χ.harmonicFactor (mixedEmbedding K ((a : 𝓞 K) : K)) *
          archGaussian (unitScale u y) (mixedEmbedding K ((a : 𝓞 K) : K))) =
        χ.finiteCharacter ((e a : 𝔞) : 𝓞 K) *
          χ.harmonicFactor (mixedEmbedding K (((e a : 𝔞) : 𝓞 K) : K)) *
          archGaussian y (mixedEmbedding K (((e a : 𝔞) : 𝓞 K) : K)) := by
    have hP : P = χ.finiteCharacter (u : 𝓞 K) * χ.harmonicFactor (mixedEmbedding K (u : K)) :=
      (χ.finiteCharacter_mul_harmonicFactor_unit u).symm
    have he_coe : ((e a : 𝔞) : 𝓞 K) = (u : 𝓞 K) * (a : 𝓞 K) := rfl
    have hcoe : (((e a : 𝔞) : 𝓞 K) : K) = (u : K) * ((a : 𝓞 K) : K) := by
      simp [he_coe]
    rw [hP, hcoe, he_coe, map_mul (χ.finiteCharacter : 𝓞 K →*₀ ℂ),
      map_mul (mixedEmbedding K), ← unitSMul_smul, archGaussian_unit_smul,
      χ.harmonicFactor_unit_smul]
    ring
  set S₁ : ℂ := ∑' a : 𝔞, χ.finiteCharacter (a : 𝓞 K) *
    χ.harmonicFactor (mixedEmbedding K ((a : 𝓞 K) : K)) *
    archGaussian (unitScale u y) (mixedEmbedding K ((a : 𝓞 K) : K))
  set S₂ : ℂ := ∑' a : 𝔞, χ.finiteCharacter (a : 𝓞 K) *
    χ.harmonicFactor (mixedEmbedding K ((a : 𝓞 K) : K)) *
    archGaussian y (mixedEmbedding K ((a : 𝓞 K) : K))
  have htsum : P * S₁ = S₂ := by
    rw [← tsum_mul_left, tsum_congr hterm]
    exact e.tsum_eq fun b ↦ χ.finiteCharacter (b : 𝓞 K) *
      χ.harmonicFactor (mixedEmbedding K ((b : 𝓞 K) : K)) *
      archGaussian y (mixedEmbedding K ((b : 𝓞 K) : K))
  rw [χ.archWeight_unitScale u y, ofReal_mul, heckeTheta_def, heckeTheta_def]
  calc (P * (χ.archWeight y : ℂ)) * (χ.heckeEpsilon + S₁)
      = (χ.archWeight y : ℂ) * (P * χ.heckeEpsilon + P * S₁) := by ring
    _ = (χ.archWeight y : ℂ) * (χ.heckeEpsilon + S₂) := by rw [hPeps, htsum]

/-- Hecke's twisted theta series is continuous at every positive parameter `y₀ : realSpace K`. -/
theorem continuousAt_heckeTheta (χ : Grossencharacter K 𝔪) (𝔞 : Ideal (𝓞 K))
    {y₀ : realSpace K} (hy₀ : ∀ w, 0 < y₀ w) : ContinuousAt (χ.heckeTheta 𝔞) y₀ := by
  rw [funext (χ.heckeTheta_def 𝔞)]
  refine continuousAt_const.add ?_
  simpa only [mul_assoc] using continuousAt_tsum_mul_archGaussian
    (fun a : 𝔞 ↦ χ.finiteCharacter (a : 𝓞 K) *
      χ.harmonicFactor (mixedEmbedding K ((a : 𝓞 K) : K)))
    (fun a ↦ mixedEmbedding K ((a : 𝓞 K) : K))
    (fun δ hδ ↦ by simpa only [mul_assoc] using χ.summable_norm_heckeTheta 𝔞 fun _ ↦ hδ) hy₀

/-- Exponential decay of `χ.heckeTheta 𝔞 y - χ.heckeEpsilon` when every parameter coordinate is
at least `t ≥ 1`. -/
theorem exists_norm_heckeTheta_sub_heckeEpsilon_le (χ : Grossencharacter K 𝔪) (𝔞 : Ideal (𝓞 K)) :
    ∃ c > 0, ∃ C ≥ 0, ∀ t : ℝ, 1 ≤ t → ∀ y : realSpace K, (∀ w, t ≤ y w) →
      ‖χ.heckeTheta 𝔞 y - χ.heckeEpsilon‖ ≤ C * Real.exp (-c * t) := by
  classical
  obtain ⟨δ, hδ, hL⟩ := exists_pos_le_mixedInner (idealLattice K 1)
  have ha : Summable fun a : ({a : 𝔞 | a ≠ 0} : Set 𝔞) ↦
      ‖(χ.finiteCharacter (a : 𝓞 K) * χ.harmonicFactor (mixedEmbedding K ((a : 𝓞 K) : K))) *
        archGaussian (fun _ ↦ (1 / 2 : ℝ)) (mixedEmbedding K ((a : 𝓞 K) : K))‖ := by
    simpa only [mul_assoc, Function.comp_def] using
      (χ.summable_norm_heckeTheta 𝔞 (fun _ ↦ by norm_num)).subtype (· ∈ ({a : 𝔞 | a ≠ 0} : Set 𝔞))
  obtain ⟨c, hc, C, hC, h⟩ := exists_norm_tsum_mul_archGaussian_le
    (fun a : ({a : 𝔞 | a ≠ 0} : Set 𝔞) ↦
      χ.finiteCharacter (a : 𝓞 K) * χ.harmonicFactor (mixedEmbedding K ((a : 𝓞 K) : K)))
    (fun a ↦ mixedEmbedding K ((a : 𝓞 K) : K)) hδ
    (fun a ↦ by
      simpa only [coe_idealToIntegerLattice] using hL (idealToIntegerLattice 𝔞 a.val) fun h0 ↦
        a.property (idealToIntegerLattice_injective 𝔞 (h0.trans (map_zero _).symm))) ha
  refine ⟨c, hc, C, hC, fun t ht y hy ↦ ?_⟩
  have hsupp : Function.support (fun a : 𝔞 ↦ χ.finiteCharacter (a : 𝓞 K) *
      χ.harmonicFactor (mixedEmbedding K ((a : 𝓞 K) : K)) *
      archGaussian y (mixedEmbedding K ((a : 𝓞 K) : K))) ⊆ {a : 𝔞 | a ≠ 0} := by
    intro a ha h0
    simp [h0] at ha
  rw [heckeTheta_def, add_sub_cancel_left, ← tsum_subtype_eq_of_support_subset hsupp]
  simpa only [mul_assoc] using h t ht y hy

/-- Uniform stretched-exponential decay of `χ.heckeTheta 𝔞 (surfaceScale x u) - χ.heckeEpsilon`
along any bounded subset of `normOneSurface K`. -/
theorem exists_norm_heckeTheta_surfaceScale_sub_heckeEpsilon_le (χ : Grossencharacter K 𝔪)
    (𝔞 : Ideal (𝓞 K)) {D : Set (realSpace K)} (hD : Bornology.IsBounded D)
    (hS : D ⊆ normOneSurface K) :
    ∃ c > 0, ∃ C ≥ 0, ∀ᶠ u : ℝ in atTop, ∀ x ∈ D,
      ‖χ.heckeTheta 𝔞 (surfaceScale x u) - χ.heckeEpsilon‖ ≤
        C * Real.exp (-c * u ^ (Module.finrank ℚ K : ℝ)⁻¹) := by
  obtain ⟨c, hc, C, hC, h⟩ := χ.exists_norm_heckeTheta_sub_heckeEpsilon_le 𝔞
  exact exists_norm_surfaceScale_le_of_forall_le hc hC h hD hS

/-- For the trivial ray class character at `Modulus.one K`, `heckeTheta` recovers `latticeTheta`
of the corresponding ideal lattice at all positive parameters `y`. -/
@[simp]
theorem heckeTheta_ofRayClassCharacter_one (𝔞 : (Ideal (𝓞 K))⁰)
    {y : realSpace K} (hy : ∀ w, 0 < y w) :
    (ofRayClassCharacter (1 : RayClassCharacter (Modulus.one K))).heckeTheta
        (𝔞 : Ideal (𝓞 K)) y =
      latticeTheta (idealLattice K (FractionalIdeal.mk0 K 𝔞)) y := by
  classical
  set χ := ofRayClassCharacter (1 : RayClassCharacter (Modulus.one K))
  have hfin {a : 𝓞 K} (ha : a ≠ 0) : χ.finiteCharacter a = 1 := by
    rw [χ.finiteCharacter_eq_residueCharacter ha]
    have hsub : Subsingleton (𝓞 K ⧸ (Modulus.one K).finitePart) := by
      rw [Modulus.one_finitePart]
      exact Ideal.Quotient.subsingleton_iff.mpr rfl
    rw [Subsingleton.elim (Ideal.Quotient.mk (Modulus.one K).finitePart a) 1, map_one]
  have hsupp : Function.support (fun a : (𝔞 : Ideal (𝓞 K)) ↦ χ.finiteCharacter (a : 𝓞 K) *
      χ.harmonicFactor (mixedEmbedding K ((a : 𝓞 K) : K)) *
      archGaussian y (mixedEmbedding K ((a : 𝓞 K) : K))) ⊆ {a : (𝔞 : Ideal (𝓞 K)) | a ≠ 0} := by
    intro a ha h0
    simp [h0] at ha
  rw [heckeTheta_def, heckeEpsilon_ofRayClassCharacter_one,
    ← tsum_subtype_eq_of_support_subset hsupp, latticeTheta_eq_one_add _ y hy,
    ← (neZeroIdealEquivIdealLattice 𝔞).tsum_eq]
  congr 1
  refine tsum_congr fun a ↦ ?_
  have ha0 : ((a : (𝔞 : Ideal (𝓞 K))) : 𝓞 K) ≠ 0 := fun h ↦
    a.property (Subtype.ext h)
  rw [hfin ha0, harmonicFactor_ofRayClassCharacter_one, one_mul, one_mul,
    coe_neZeroIdealEquivIdealLattice]

end TauCeti.LFunctions.Grossencharacter
