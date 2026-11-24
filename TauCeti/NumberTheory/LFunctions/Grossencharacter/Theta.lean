/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.Grossencharacter.ArchWeight
public import TauCeti.NumberTheory.LFunctions.Grossencharacter.Conductor
public import TauCeti.NumberTheory.LFunctions.Grossencharacter.FiniteCharacter
public import TauCeti.NumberTheory.LFunctions.Theta.Decay
import TauCeti.NumberTheory.NumberField.CanonicalEmbedding.IdealLattice
import TauCeti.NumberTheory.NumberField.CanonicalEmbedding.UnitAction

/-!
# Hecke's twisted theta series of a Grossencharacter

For a presented algebraic Hecke character `χ : Grossencharacter K 𝔪`, an invertible fractional ideal
`I : (FractionalIdeal (𝓞 K)⁰ K)ˣ`, and archimedean parameters `y : realSpace K`, Hecke's twisted
theta series (Neukirch VII (8.1)) is

`θ_χ(I, y) = ε(χ) + ∑_{a ∈ I} χ_f(a) * χ.harmonicFactor (σ a) * archGaussian y (σ a)`,

where `σ = mixedEmbedding K`, `ε(χ) = χ.heckeEpsilon` is `1` when `χ` has trivial finite conductor
and `χ.harmonicDegree = 0` (and `0` otherwise), and `χ_f` is the primitive finite character
`χ.primitive.finiteCharacterK` extended by `0` outside `primeToSubgroup χ.conductor`.

## Main definitions

* `TauCeti.LFunctions.Grossencharacter.heckeTheta`: Hecke's twisted theta series `θ_χ(I, y)`.

## Main results

* `TauCeti.LFunctions.Grossencharacter.heckeTheta_congr`,
  `TauCeti.LFunctions.Grossencharacter.heckeTheta_primitive`, and
  `TauCeti.LFunctions.Grossencharacter.heckeTheta_mk0`: modulus independence and specialization to
  integral ideals.
* `TauCeti.LFunctions.Grossencharacter.summable_heckeTheta` and
  `TauCeti.LFunctions.Grossencharacter.summable_norm_heckeTheta`: absolute convergence for positive
  parameters `y`.
* `TauCeti.LFunctions.Grossencharacter.finiteCharacter_mul_harmonicFactor_unit` and
  `TauCeti.LFunctions.Grossencharacter.archWeight_mul_heckeTheta_unitScale`: unit invariance of
  `χ.archWeight y * χ.heckeTheta I y` (Neukirch VII (8.2)).
* `TauCeti.LFunctions.Grossencharacter.continuousAt_heckeTheta`: continuity at positive parameters.
* `TauCeti.LFunctions.Grossencharacter.exists_norm_heckeTheta_sub_heckeEpsilon_le` and
  `TauCeti.LFunctions.Grossencharacter.exists_norm_heckeTheta_surfaceScale_sub_heckeEpsilon_le`:
  exponential decay of `χ.heckeTheta I y - χ.heckeEpsilon`.
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

open scoped Classical in
/-- **Hecke's twisted theta series** (Neukirch VII (8.1)) attached to a presentation `χ` of an
algebraic Hecke character, an invertible fractional ideal `I` of `K`, and archimedean parameters
`y : realSpace K`. The finite character is evaluated on the primitive reduction `χ.primitive`,
extended by `0` outside fractions prime to `χ.conductor`. -/
def heckeTheta (χ : Grossencharacter K 𝔪) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (y : realSpace K) : ℂ :=
  χ.heckeEpsilon +
    ∑' a : (I : Submodule (𝓞 K) K),
      (if h : ∃ ha : (a : K) ≠ 0, Units.mk0 (a : K) ha ∈ primeToSubgroup χ.conductor then
        (χ.primitive.finiteCharacterK ⟨Units.mk0 (a : K) h.1, h.2⟩ : ℂ) else 0) *
      χ.harmonicFactor (mixedEmbedding K (a : K)) *
      archGaussian y (mixedEmbedding K (a : K))

open scoped Classical in
/-- The defining equation of `Grossencharacter.heckeTheta`. -/
theorem heckeTheta_def (χ : Grossencharacter K 𝔪) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (y : realSpace K) :
    χ.heckeTheta I y =
      χ.heckeEpsilon +
        ∑' a : (I : Submodule (𝓞 K) K),
          (if h : ∃ ha : (a : K) ≠ 0, Units.mk0 (a : K) ha ∈ primeToSubgroup χ.conductor then
            (χ.primitive.finiteCharacterK ⟨Units.mk0 (a : K) h.1, h.2⟩ : ℂ) else 0) *
          χ.harmonicFactor (mixedEmbedding K (a : K)) *
          archGaussian y (mixedEmbedding K (a : K)) :=
  (rfl)

open scoped Classical in
private theorem norm_heckeCoeff_le_one (χ : Grossencharacter K 𝔪) (a : K) :
    ‖if h : ∃ ha : a ≠ 0, Units.mk0 a ha ∈ primeToSubgroup χ.conductor then
      (χ.primitive.finiteCharacterK ⟨Units.mk0 a h.1, h.2⟩ : ℂ) else 0‖ ≤ 1 := by
  split_ifs
  · simp
  · norm_num

/-- Two presentations of the same Hecke character have the same twisted theta series. -/
theorem heckeTheta_congr {𝔫 : Modulus K} {χ : Grossencharacter K 𝔪}
    {ψ : Grossencharacter K 𝔫} (h : χ.toHeckeCharacter = ψ.toHeckeCharacter)
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (y : realSpace K) :
    χ.heckeTheta I y = ψ.heckeTheta I y := by
  classical
  have hcond : χ.conductor = ψ.conductor := conductor_congr h
  rw [heckeTheta_def, heckeTheta_def, heckeEpsilon_congr h]
  congr 1
  refine tsum_congr fun a ↦ ?_
  rw [harmonicFactor_congr h]
  congr 2
  by_cases ha : ∃ ha0 : (a : K) ≠ 0, Units.mk0 (a : K) ha0 ∈ primeToSubgroup χ.conductor
  · have ha' : ∃ ha0 : (a : K) ≠ 0, Units.mk0 (a : K) ha0 ∈ primeToSubgroup ψ.conductor :=
      ⟨ha.1, hcond ▸ ha.2⟩
    simp only [ha, ha', ↓reduceDIte]
    exact congrArg Units.val (finiteCharacterK_congr
      (χ.toHeckeCharacter_primitive.trans (h.trans ψ.toHeckeCharacter_primitive.symm)) rfl)
  · have ha' : ¬ ∃ ha0 : (a : K) ≠ 0, Units.mk0 (a : K) ha0 ∈ primeToSubgroup ψ.conductor :=
      fun ⟨ha0, hmem⟩ ↦ ha ⟨ha0, hcond.symm ▸ hmem⟩
    simp only [ha, ha', ↓reduceDIte]

/-- Passing to `χ.primitive` does not change `heckeTheta`. -/
@[simp]
theorem heckeTheta_primitive (χ : Grossencharacter K 𝔪) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (y : realSpace K) :
    χ.primitive.heckeTheta I y = χ.heckeTheta I y :=
  heckeTheta_congr χ.toHeckeCharacter_primitive I y

open scoped Classical in
/-- At an integral ideal `𝔞`, `χ.heckeTheta (FractionalIdeal.mk0 K 𝔞) y` is the sum over `a : 𝔞`
weighted by `χ.primitive.finiteCharacter (a : 𝓞 K)`. -/
theorem heckeTheta_mk0 (χ : Grossencharacter K 𝔪) (𝔞 : (Ideal (𝓞 K))⁰) (y : realSpace K) :
    χ.heckeTheta (FractionalIdeal.mk0 K 𝔞) y =
      χ.heckeEpsilon +
        ∑' a : (𝔞 : Ideal (𝓞 K)), χ.primitive.finiteCharacter (a : 𝓞 K) *
          χ.harmonicFactor (mixedEmbedding K ((a : 𝓞 K) : K)) *
          archGaussian y (mixedEmbedding K ((a : 𝓞 K) : K)) := by
  let e : (𝔞 : Ideal (𝓞 K)) ≃ (FractionalIdeal.mk0 K 𝔞 : Submodule (𝓞 K) K) :=
    (Submodule.equivMapOfInjective (Algebra.linearMap (𝓞 K) K)
      (IsFractionRing.injective (𝓞 K) K) (𝔞 : Ideal (𝓞 K))).toEquiv
  have he_coe (a : (𝔞 : Ideal (𝓞 K))) :
      ((e a : (FractionalIdeal.mk0 K 𝔞 : Submodule (𝓞 K) K)) : K) = ((a : 𝓞 K) : K) :=
    rfl
  rw [heckeTheta_def, ← e.tsum_eq]
  congr 1
  refine tsum_congr fun a ↦ ?_
  rw [he_coe a]
  congr 2
  split_ifs with ha
  · exact (χ.primitive.finiteCharacter_eq_finiteCharacterK
      ⟨Units.mk0 ((a : 𝓞 K) : K) ha.1, ha.2⟩ rfl).symm
  · refine (χ.primitive.finiteCharacter_eq_zero_of_not_isCoprimeTo fun hcop ↦ ?_).symm
    obtain ⟨x, hx⟩ := Modulus.isCoprimeTo_span_singleton_iff.mp hcop
    have hx0 : ((a : 𝓞 K) : K) ≠ 0 := by
      rw [← hx]
      exact (x : Kˣ).ne_zero
    have hmem : Units.mk0 ((a : 𝓞 K) : K) hx0 ∈ primeToSubgroup χ.conductor := by
      convert x.property using 1
      ext1
      exact hx.symm
    exact ha ⟨hx0, hmem⟩

open scoped Classical in
/-- For positive archimedean parameters `y`, the norms of the terms of `χ.heckeTheta I y` are
summable. -/
theorem summable_norm_heckeTheta (χ : Grossencharacter K 𝔪) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {y : realSpace K} (hy : ∀ w, 0 < y w) :
    Summable fun a : (I : Submodule (𝓞 K) K) ↦
      ‖(if h : ∃ ha : (a : K) ≠ 0, Units.mk0 (a : K) ha ∈ primeToSubgroup χ.conductor then
          (χ.primitive.finiteCharacterK ⟨Units.mk0 (a : K) h.1, h.2⟩ : ℂ) else 0) *
        χ.harmonicFactor (mixedEmbedding K (a : K)) *
        archGaussian y (mixedEmbedding K (a : K))‖ := by
  let f : idealLattice K I → ℂ := fun x ↦
    χ.harmonicFactor (x : mixedSpace K) * archGaussian y (x : mixedSpace K)
  have hdom : Summable fun a : (I : Submodule (𝓞 K) K) ↦
      ‖f (fractionalIdealEquivIdealLattice I a)‖ :=
    (χ.summable_harmonicFactor_mul_archGaussian (idealLattice K I) y hy).norm.comp_injective
      (fractionalIdealEquivIdealLattice I).injective
  refine Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun a ↦ ?_) hdom
  dsimp only [f]
  rw [coe_fractionalIdealEquivIdealLattice, norm_mul, norm_mul, mul_assoc, ← norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg (χ.harmonicFactor _ * archGaussian y _))
    (χ.norm_heckeCoeff_le_one (a : K))

open scoped Classical in
/-- For positive archimedean parameters `y`, the defining series of `χ.heckeTheta I y` is
summable. -/
theorem summable_heckeTheta (χ : Grossencharacter K 𝔪) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {y : realSpace K} (hy : ∀ w, 0 < y w) :
    Summable fun a : (I : Submodule (𝓞 K) K) ↦
      (if h : ∃ ha : (a : K) ≠ 0, Units.mk0 (a : K) ha ∈ primeToSubgroup χ.conductor then
        (χ.primitive.finiteCharacterK ⟨Units.mk0 (a : K) h.1, h.2⟩ : ℂ) else 0) *
      χ.harmonicFactor (mixedEmbedding K (a : K)) *
      archGaussian y (mixedEmbedding K (a : K)) :=
  (χ.summable_norm_heckeTheta I hy).of_norm

open scoped Classical in
/-- Monotone domination of `‖χ.heckeTheta I y‖` by the absolute series majorant at any smaller
positive parameter `y' ≤ y`. -/
theorem norm_heckeTheta_le (χ : Grossencharacter K 𝔪) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {y y' : realSpace K} (hy' : ∀ w, 0 < y' w) (h : ∀ w, y' w ≤ y w) :
    ‖χ.heckeTheta I y‖ ≤ ‖χ.heckeEpsilon‖ +
      ∑' a : (I : Submodule (𝓞 K) K),
        ‖(if h0 : ∃ ha : (a : K) ≠ 0, Units.mk0 (a : K) ha ∈ primeToSubgroup χ.conductor then
            (χ.primitive.finiteCharacterK ⟨Units.mk0 (a : K) h0.1, h0.2⟩ : ℂ) else 0) *
          χ.harmonicFactor (mixedEmbedding K (a : K)) *
          archGaussian y' (mixedEmbedding K (a : K))‖ := by
  have hy : ∀ w, 0 < y w := fun w ↦ (hy' w).trans_le (h w)
  rw [heckeTheta_def]
  refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
  refine (norm_tsum_le_tsum_norm (χ.summable_norm_heckeTheta I hy)).trans ?_
  refine (χ.summable_norm_heckeTheta I hy).tsum_le_tsum (fun a ↦ ?_)
    (χ.summable_norm_heckeTheta I hy')
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
`χ.archWeight (unitScale u y) * χ.heckeTheta I (unitScale u y) = χ.archWeight y * χ.heckeTheta I y`.
-/
theorem archWeight_mul_heckeTheta_unitScale (χ : Grossencharacter K 𝔪)
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (u : (𝓞 K)ˣ) (y : realSpace K) :
    (χ.archWeight (unitScale u y) : ℂ) * χ.heckeTheta I (unitScale u y) =
      (χ.archWeight y : ℂ) * χ.heckeTheta I y := by
  classical
  set P : ℂ := ((∏ w : InfinitePlace K,
    normAtPlace w (mixedEmbedding K (u : K)) ^ χ.harmonicExponent w : ℝ) : ℂ)
  have hPeps : P * χ.heckeEpsilon = χ.heckeEpsilon := by
    by_cases hdeg : χ.harmonicDegree = 0
    · have hw : ∀ w, χ.harmonicExponent w = 0 := by
        simpa [harmonicDegree_def] using hdeg
      simp [P, hw]
    · simp [χ.heckeEpsilon_eq_zero_of_harmonicDegree_ne_zero hdeg]
  let uK : Kˣ := Units.map (algebraMap (𝓞 K) K).toMonoidHom u
  let e : (I : Submodule (𝓞 K) K) ≃ (I : Submodule (𝓞 K) K) :=
    Equiv.subtypeEquiv (Units.mulLeft uK) fun a ↦
      ⟨fun h ↦ by
         simpa [uK, Algebra.smul_def] using (I : Submodule (𝓞 K) K).smul_mem (u : 𝓞 K) h,
       fun h ↦ by
         simpa [uK, Algebra.smul_def, ← mul_assoc, ← map_mul] using
           (I : Submodule (𝓞 K) K).smul_mem ((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K) h⟩
  have hcoeff (a : K) :
      (χ.primitive.finiteCharacter (u : 𝓞 K)) *
          (if h : ∃ ha : a ≠ 0, Units.mk0 a ha ∈ primeToSubgroup χ.conductor then
            (χ.primitive.finiteCharacterK ⟨Units.mk0 a h.1, h.2⟩ : ℂ) else 0) =
        if h : ∃ ha : (u : K) * a ≠ 0, Units.mk0 ((u : K) * a) ha ∈ primeToSubgroup χ.conductor then
          (χ.primitive.finiteCharacterK ⟨Units.mk0 ((u : K) * a) h.1, h.2⟩ : ℂ) else 0 := by
    by_cases ha : ∃ ha0 : a ≠ 0, Units.mk0 a ha0 ∈ primeToSubgroup χ.conductor
    · have ha' : ∃ ha0 : (u : K) * a ≠ 0,
          Units.mk0 ((u : K) * a) ha0 ∈ primeToSubgroup χ.conductor := by
        refine ⟨mul_ne_zero uK.ne_zero ha.1, ?_⟩
        have hmk : Units.mk0 ((u : K) * a) (mul_ne_zero uK.ne_zero ha.1) =
            uK * Units.mk0 a ha.1 := by
          ext1; rfl
        rw [hmk]
        exact (primeToSubgroup χ.conductor).mul_mem (unitsMap_mem_primeToSubgroup _ u) ha.2
      simp only [ha, ha', ↓reduceDIte]
      rw [χ.primitive.finiteCharacter_unit u,
        ← χ.primitive.finiteCharacterK_unitsToPrimeToSubgroup u, ← Units.val_mul, ← map_mul]
      congr 2
      ext
      simp
    · have ha' : ¬ ∃ ha0 : (u : K) * a ≠ 0,
          Units.mk0 ((u : K) * a) ha0 ∈ primeToSubgroup χ.conductor := by
        rintro ⟨hb0, hbmem⟩
        have ha0 : a ≠ 0 := right_ne_zero_of_mul hb0
        have hmk : Units.mk0 a ha0 = uK⁻¹ * Units.mk0 ((u : K) * a) hb0 := by
          ext1
          simp [uK]
        refine ha ⟨ha0, ?_⟩
        rw [hmk]
        exact (primeToSubgroup χ.conductor).mul_mem
          ((primeToSubgroup χ.conductor).inv_mem (unitsMap_mem_primeToSubgroup _ u)) hbmem
      simp only [ha, ha', ↓reduceDIte, mul_zero]
  have hterm (a : (I : Submodule (𝓞 K) K)) :
      P * ((if h : ∃ ha : (a : K) ≠ 0, Units.mk0 (a : K) ha ∈ primeToSubgroup χ.conductor then
            (χ.primitive.finiteCharacterK ⟨Units.mk0 (a : K) h.1, h.2⟩ : ℂ) else 0) *
          χ.harmonicFactor (mixedEmbedding K (a : K)) *
          archGaussian (unitScale u y) (mixedEmbedding K (a : K))) =
        (if h : ∃ ha : ((e a : (I : Submodule (𝓞 K) K)) : K) ≠ 0,
            Units.mk0 ((e a : (I : Submodule (𝓞 K) K)) : K) ha ∈
              primeToSubgroup χ.conductor then
          (χ.primitive.finiteCharacterK
            ⟨Units.mk0 ((e a : (I : Submodule (𝓞 K) K)) : K) h.1, h.2⟩ : ℂ) else 0) *
          χ.harmonicFactor (mixedEmbedding K ((e a : (I : Submodule (𝓞 K) K)) : K)) *
          archGaussian y (mixedEmbedding K ((e a : (I : Submodule (𝓞 K) K)) : K)) := by
    have hP : P = χ.primitive.finiteCharacter (u : 𝓞 K) *
        χ.harmonicFactor (mixedEmbedding K (u : K)) := by
      simpa only [harmonicFactor_congr χ.toHeckeCharacter_primitive,
        harmonicExponent_congr χ.toHeckeCharacter_primitive] using
        (χ.primitive.finiteCharacter_mul_harmonicFactor_unit u).symm
    have hcoe : ((e a : (I : Submodule (𝓞 K) K)) : K) = (u : K) * (a : K) := rfl
    rw [hP, hcoe, map_mul (mixedEmbedding K), ← unitSMul_smul, archGaussian_unit_smul,
      χ.harmonicFactor_unit_smul, ← hcoeff (a : K)]
    ring
  set S₁ : ℂ := ∑' a : (I : Submodule (𝓞 K) K),
    (if h : ∃ ha : (a : K) ≠ 0, Units.mk0 (a : K) ha ∈ primeToSubgroup χ.conductor then
      (χ.primitive.finiteCharacterK ⟨Units.mk0 (a : K) h.1, h.2⟩ : ℂ) else 0) *
    χ.harmonicFactor (mixedEmbedding K (a : K)) *
    archGaussian (unitScale u y) (mixedEmbedding K (a : K))
  set S₂ : ℂ := ∑' a : (I : Submodule (𝓞 K) K),
    (if h : ∃ ha : (a : K) ≠ 0, Units.mk0 (a : K) ha ∈ primeToSubgroup χ.conductor then
      (χ.primitive.finiteCharacterK ⟨Units.mk0 (a : K) h.1, h.2⟩ : ℂ) else 0) *
    χ.harmonicFactor (mixedEmbedding K (a : K)) *
    archGaussian y (mixedEmbedding K (a : K))
  have htsum : P * S₁ = S₂ := by
    rw [← tsum_mul_left, tsum_congr hterm]
    exact e.tsum_eq fun b ↦
      (if h : ∃ ha : (b : K) ≠ 0, Units.mk0 (b : K) ha ∈ primeToSubgroup χ.conductor then
        (χ.primitive.finiteCharacterK ⟨Units.mk0 (b : K) h.1, h.2⟩ : ℂ) else 0) *
      χ.harmonicFactor (mixedEmbedding K (b : K)) *
      archGaussian y (mixedEmbedding K (b : K))
  rw [χ.archWeight_unitScale u y, ofReal_mul, heckeTheta_def, heckeTheta_def]
  calc (P * (χ.archWeight y : ℂ)) * (χ.heckeEpsilon + S₁)
      = (χ.archWeight y : ℂ) * (P * χ.heckeEpsilon + P * S₁) := by ring
    _ = (χ.archWeight y : ℂ) * (χ.heckeEpsilon + S₂) := by rw [hPeps, htsum]

open scoped Classical in
/-- Hecke's twisted theta series is continuous at every positive parameter `y₀ : realSpace K`. -/
theorem continuousAt_heckeTheta (χ : Grossencharacter K 𝔪) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {y₀ : realSpace K} (hy₀ : ∀ w, 0 < y₀ w) : ContinuousAt (χ.heckeTheta I) y₀ := by
  rw [funext (χ.heckeTheta_def I)]
  refine continuousAt_const.add ?_
  simpa only [mul_assoc] using continuousAt_tsum_mul_archGaussian
    (fun a : (I : Submodule (𝓞 K) K) ↦
      (if h : ∃ ha : (a : K) ≠ 0, Units.mk0 (a : K) ha ∈ primeToSubgroup χ.conductor then
        (χ.primitive.finiteCharacterK ⟨Units.mk0 (a : K) h.1, h.2⟩ : ℂ) else 0) *
      χ.harmonicFactor (mixedEmbedding K (a : K)))
    (fun a ↦ mixedEmbedding K (a : K))
    (fun δ hδ ↦ by simpa only [mul_assoc] using χ.summable_norm_heckeTheta I fun _ ↦ hδ) hy₀

open scoped Classical in
/-- Separating the constant term `χ.heckeEpsilon` from the nonzero elements of `I` in
`χ.heckeTheta I y`. -/
theorem heckeTheta_eq_heckeEpsilon_add (χ : Grossencharacter K 𝔪)
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (y : realSpace K) :
    χ.heckeTheta I y =
      χ.heckeEpsilon +
        ∑' a : {a : (I : Submodule (𝓞 K) K) // a ≠ 0},
          (if h : ∃ ha : ((a : (I : Submodule (𝓞 K) K)) : K) ≠ 0,
              Units.mk0 ((a : (I : Submodule (𝓞 K) K)) : K) ha ∈
                primeToSubgroup χ.conductor then
            (χ.primitive.finiteCharacterK
              ⟨Units.mk0 ((a : (I : Submodule (𝓞 K) K)) : K) h.1, h.2⟩ : ℂ) else 0) *
          χ.harmonicFactor (mixedEmbedding K ((a : (I : Submodule (𝓞 K) K)) : K)) *
          archGaussian y (mixedEmbedding K ((a : (I : Submodule (𝓞 K) K)) : K)) := by
  have hsupp : Function.support (fun a : (I : Submodule (𝓞 K) K) ↦
      (if h : ∃ ha : (a : K) ≠ 0, Units.mk0 (a : K) ha ∈ primeToSubgroup χ.conductor then
        (χ.primitive.finiteCharacterK ⟨Units.mk0 (a : K) h.1, h.2⟩ : ℂ) else 0) *
      χ.harmonicFactor (mixedEmbedding K (a : K)) *
      archGaussian y (mixedEmbedding K (a : K))) ⊆
      {a : (I : Submodule (𝓞 K) K) | a ≠ 0} := by
    intro a ha h0
    simp [h0] at ha
  rw [heckeTheta_def, ← tsum_subtype_eq_of_support_subset hsupp]
  rfl

/-- Exponential decay of `χ.heckeTheta I y - χ.heckeEpsilon` when every parameter coordinate is
at least `t ≥ 1`. -/
theorem exists_norm_heckeTheta_sub_heckeEpsilon_le (χ : Grossencharacter K 𝔪)
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ∃ c > 0, ∃ C ≥ 0, ∀ t : ℝ, 1 ≤ t → ∀ y : realSpace K, (∀ w, t ≤ y w) →
      ‖χ.heckeTheta I y - χ.heckeEpsilon‖ ≤ C * Real.exp (-c * t) := by
  classical
  obtain ⟨δ, hδ, hL⟩ := exists_pos_le_mixedInner (idealLattice K I)
  have ha : Summable fun a : {a : (I : Submodule (𝓞 K) K) // a ≠ 0} ↦
      ‖((if h : ∃ ha : ((a : (I : Submodule (𝓞 K) K)) : K) ≠ 0,
            Units.mk0 ((a : (I : Submodule (𝓞 K) K)) : K) ha ∈
              primeToSubgroup χ.conductor then
          (χ.primitive.finiteCharacterK
            ⟨Units.mk0 ((a : (I : Submodule (𝓞 K) K)) : K) h.1, h.2⟩ : ℂ) else 0) *
        χ.harmonicFactor (mixedEmbedding K ((a : (I : Submodule (𝓞 K) K)) : K))) *
        archGaussian (fun _ ↦ (1 / 2 : ℝ))
          (mixedEmbedding K ((a : (I : Submodule (𝓞 K) K)) : K))‖ := by
    simpa only [mul_assoc, Function.comp_def] using
      (χ.summable_norm_heckeTheta I (fun _ ↦ by norm_num)).comp_injective Subtype.coe_injective
  obtain ⟨c, hc, C, hC, h⟩ := exists_norm_tsum_mul_archGaussian_le
    (fun a : {a : (I : Submodule (𝓞 K) K) // a ≠ 0} ↦
      (if h : ∃ ha : ((a : (I : Submodule (𝓞 K) K)) : K) ≠ 0,
          Units.mk0 ((a : (I : Submodule (𝓞 K) K)) : K) ha ∈
            primeToSubgroup χ.conductor then
        (χ.primitive.finiteCharacterK
          ⟨Units.mk0 ((a : (I : Submodule (𝓞 K) K)) : K) h.1, h.2⟩ : ℂ) else 0) *
      χ.harmonicFactor (mixedEmbedding K ((a : (I : Submodule (𝓞 K) K)) : K)))
    (fun a ↦ mixedEmbedding K ((a : (I : Submodule (𝓞 K) K)) : K)) hδ
    (fun a ↦ by
      simpa only [coe_fractionalIdealEquivIdealLattice] using
        hL (fractionalIdealEquivIdealLattice I a.val) fun h0 ↦
          a.property ((fractionalIdealEquivIdealLattice I).injective (h0.trans (map_zero _).symm)))
    ha
  refine ⟨c, hc, C, hC, fun t ht y hy ↦ ?_⟩
  rw [χ.heckeTheta_eq_heckeEpsilon_add I y, add_sub_cancel_left]
  simpa only [mul_assoc] using h t ht y hy

/-- Uniform stretched-exponential decay of `χ.heckeTheta I (surfaceScale x u) - χ.heckeEpsilon`
along any bounded subset of `normOneSurface K`. -/
theorem exists_norm_heckeTheta_surfaceScale_sub_heckeEpsilon_le (χ : Grossencharacter K 𝔪)
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {D : Set (realSpace K)} (hD : Bornology.IsBounded D)
    (hS : D ⊆ normOneSurface K) :
    ∃ c > 0, ∃ C ≥ 0, ∀ᶠ u : ℝ in atTop, ∀ x ∈ D,
      ‖χ.heckeTheta I (surfaceScale x u) - χ.heckeEpsilon‖ ≤
        C * Real.exp (-c * u ^ (Module.finrank ℚ K : ℝ)⁻¹) := by
  obtain ⟨c, hc, C, hC, h⟩ := χ.exists_norm_heckeTheta_sub_heckeEpsilon_le I
  exact exists_norm_surfaceScale_le_of_forall_le hc hC h hD hS

/-- For the trivial ray class character at `Modulus.one K`, `heckeTheta` recovers `latticeTheta`
of the corresponding ideal lattice at all positive parameters `y`. -/
@[simp]
theorem heckeTheta_ofRayClassCharacter_one (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {y : realSpace K} (hy : ∀ w, 0 < y w) :
    (ofRayClassCharacter (1 : RayClassCharacter (Modulus.one K))).heckeTheta I y =
      latticeTheta (idealLattice K I) y := by
  classical
  set χ := ofRayClassCharacter (1 : RayClassCharacter (Modulus.one K))
  have hcond_hecke : χ.toHeckeCharacter.finiteConductor = ⊤ := by
    rw [show χ.toHeckeCharacter = 1 from by
      simp [χ, toHeckeCharacter_ofRayClassCharacter], HeckeCharacter.finiteConductor_one]
  have hcond_fin : χ.conductor.finitePart = ⊤ := by
    rw [finitePart_conductor, hcond_hecke]
  have : Subsingleton (𝓞 K ⧸ χ.conductor.finitePart) :=
    Ideal.Quotient.subsingleton_iff.mpr hcond_fin
  have hfin {a : K} (ha : a ≠ 0) :
      (if h : ∃ ha0 : a ≠ 0, Units.mk0 a ha0 ∈ primeToSubgroup χ.conductor then
        (χ.primitive.finiteCharacterK ⟨Units.mk0 a h.1, h.2⟩ : ℂ) else 0) = 1 := by
    have hmem : Units.mk0 a ha ∈ primeToSubgroup χ.conductor :=
      mem_primeToSubgroup.mpr fun v hv ↦
        False.elim (v.prime.not_dvd_one (by simpa [hcond_hecke] using hv))
    split_ifs with h
    · rw [χ.primitive.finiteCharacterK_eq_one_of_residueHom_eq_one (Subsingleton.elim _ _),
        Units.val_one]
    · exact absurd ⟨ha, hmem⟩ h
  rw [χ.heckeTheta_eq_heckeEpsilon_add I y, heckeEpsilon_ofRayClassCharacter_one,
    latticeTheta_eq_one_add _ y hy, ← (neZeroFractionalIdealEquivIdealLattice I).tsum_eq]
  congr 1
  refine tsum_congr fun a ↦ ?_
  have ha0 : ((a : (I : Submodule (𝓞 K) K)) : K) ≠ 0 := fun h ↦
    a.property (Subtype.ext h)
  rw [hfin ha0, harmonicFactor_ofRayClassCharacter_one, one_mul, one_mul,
    coe_neZeroFractionalIdealEquivIdealLattice]

end TauCeti.LFunctions.Grossencharacter
