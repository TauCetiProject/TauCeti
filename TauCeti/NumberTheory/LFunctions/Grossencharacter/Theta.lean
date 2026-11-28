/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.Grossencharacter.Conductor
public import TauCeti.NumberTheory.LFunctions.Grossencharacter.FiniteCharacter
public import TauCeti.NumberTheory.LFunctions.Grossencharacter.Harmonic
import TauCeti.NumberTheory.NumberField.CanonicalEmbedding.IdealLattice
import TauCeti.RingTheory.FractionalIdeal.LinearEquiv

/-!
# Hecke's twisted theta series of a Grossencharacter

Let `χ` be a presentation of an algebraic Hecke character, with finite character `χ_f`, harmonic
polynomial `N(x ^ p) = χ.harmonicFactor x` and theta constant `ε(χ) = χ.heckeEpsilon`. For a
fractional ideal `𝔞` and a positive parameter `y`, one per infinite place, Hecke's twisted theta
series is

`θ_χ(𝔞, y) = ε(χ) + ∑_{a ∈ 𝔞} χ_f(a) N(a ^ p) exp(-π ∑_w y_w |a_w|²)`,

Neukirch's `θ^p(𝔎, χ_f, z)` of VII §7 on the imaginary axis `z = i y`, with one parameter per
infinite place. The finite character is that of the primitive presentation, extended to `K` by
`Grossencharacter.finiteCharacterField`, so the series is a function of the Hecke character alone
(`Grossencharacter.heckeTheta_congr`). It is the series whose average over a fundamental domain
for the units is the Mellin kernel of the completed L-function of `χ`.

That average makes sense because of Neukirch VII (8.2): weighted by the archimedean weight
`N(y ^ (p/2)) = χ.archWeight y`, the series is invariant under the action `y ↦ |u|² y` of a unit
(`Grossencharacter.archWeight_mul_heckeTheta_unitScale`). Reindexing the sum by `a ↦ u a`
multiplies it by `(χ_f(u) N(u ^ p))⁻¹`, and on a unit the finite character cancels the signs and
phases of the harmonic polynomial, `χ_f(u) N(u ^ p) = ∏_w |u_w| ^ P_w`
(`Grossencharacter.finiteCharacter_mul_harmonicFactor_unit`), which is exactly the factor the
weight gains. The constant `ε(χ)` does not move, and it is nonzero only when the polynomial is
constant, where that factor is `1`.

When the finite conductor is trivial and the polynomial is constant, as for the trivial
character, the finite character is `1` off `0` and the twisted series is the theta series of the
ideal lattice (`Grossencharacter.heckeTheta_eq_latticeTheta`).

## Main definitions

All names are in the namespace `TauCeti.LFunctions.Grossencharacter`.

* `heckeTheta`: the twisted theta series `θ_χ(𝔞, y)`.

## Main results

* `finiteCharacter_mul_harmonicFactor_unit`: `χ_f(u) N(u ^ p) = ∏_w |u_w| ^ P_w` on a unit.
* `summable_finiteCharacterField_mul_harmonicFactor_mul_archGaussian`: the series converges
  absolutely at positive parameters.
* `heckeTheta_mk0`: specialization to integral ideals.
* `norm_heckeTheta_le`: monotone domination by the absolute series majorant.
* `archWeight_mul_heckeTheta_unitScale`: Neukirch VII (8.2).
* `continuousAt_heckeTheta`: continuity at positive parameters.
* `exists_norm_heckeTheta_sub_heckeEpsilon_le` and
  `exists_norm_heckeTheta_surfaceScale_sub_heckeEpsilon_le`: exponential and stretched-exponential
  decay of `χ.heckeTheta I y - χ.heckeEpsilon`.
* `heckeTheta_eq_latticeTheta`: the untwisted case.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §§7–8, (8.2).
-/

public section
noncomputable section

open Complex Filter NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
  TauCeti.NumberField.mixedEmbedding
open scoped NumberField Topology nonZeroDivisors

namespace TauCeti.LFunctions

open GlobalNumberFields

namespace Grossencharacter

variable {K : Type*} [Field K] [NumberField K] {𝔪 𝔫 : Modulus K}

/-! ### The finite character at units -/

/-- **On a unit the finite character cancels the harmonic polynomial up to absolute values**:
`χ_f(u) N(u ^ p) = ∏_w |u_w| ^ P_w`. The sign of `u_w ^ ε_w` at a real place and the phase of the
monomial at a complex place are cancelled by the archimedean value, which is the finite character
on a unit (`finiteCharacter_unit`). At `u = -1` for the odd character modulo `4∞` both factors
are `-1`. -/
theorem finiteCharacter_mul_harmonicFactor_unit (χ : Grossencharacter K 𝔪) (u : (𝓞 K)ˣ) :
    χ.finiteCharacter (u : 𝓞 K) * χ.harmonicFactor (mixedEmbedding K (u : K)) =
      ((∏ w : InfinitePlace K,
        normAtPlace w (mixedEmbedding K (u : K)) ^ χ.harmonicExponent w : ℝ) : ℂ) := by
  rw [finiteCharacter_unit, archimedeanValue_apply, Units.coe_prod]
  exact χ.prod_infiniteComponent_unit_mul_harmonicFactor u

/-! ### The twisted theta series -/

/-- **Hecke's twisted theta series** `θ_χ(𝔞, y)` of the fractional ideal `𝔞` at the parameter
`y`, one coordinate per infinite place: the theta constant `ε(χ)` plus the sum over `a ∈ 𝔞` of
`χ_f(a) N(a ^ p) exp(-π ∑_w y_w |a_w|²)`. This is Neukirch's `θ^p(𝔎, χ_f, z)` (VII §7) at
`z = i y`. The finite character `χ_f` is that of the primitive presentation `χ.primitive`, read on
`K` by `finiteCharacterField`, so it vanishes at `0` and at every element that is not a unit at
some prime dividing the finite conductor. The series converges absolutely when every coordinate of
`y` is positive (`summable_finiteCharacterField_mul_harmonicFactor_mul_archGaussian`). -/
def heckeTheta (χ : Grossencharacter K 𝔪) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (y : realSpace K) :
    ℂ :=
  χ.heckeEpsilon + ∑' a : (I : Submodule (𝓞 K) K),
    χ.primitive.finiteCharacterField a * χ.harmonicFactor (mixedEmbedding K a) *
      archGaussian y (mixedEmbedding K a)

/-- The defining formula of `Grossencharacter.heckeTheta`. -/
theorem heckeTheta_def (χ : Grossencharacter K 𝔪) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (y : realSpace K) :
    χ.heckeTheta I y = χ.heckeEpsilon + ∑' a : (I : Submodule (𝓞 K) K),
      χ.primitive.finiteCharacterField a * χ.harmonicFactor (mixedEmbedding K a) *
        archGaussian y (mixedEmbedding K a) :=
  (rfl)

/-- **The twisted theta series converges absolutely** at every parameter with positive
coordinates: its terms are dominated by the harmonic Gaussian on the ideal lattice, since the
finite character has values of norm at most `1`. -/
theorem summable_finiteCharacterField_mul_harmonicFactor_mul_archGaussian
    (χ : Grossencharacter K 𝔪) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {y : realSpace K}
    (hy : ∀ w, 0 < y w) :
    Summable fun a : (I : Submodule (𝓞 K) K) ↦
      χ.primitive.finiteCharacterField a * χ.harmonicFactor (mixedEmbedding K a) *
        archGaussian y (mixedEmbedding K a) := by
  have hL : Summable fun a : (I : Submodule (𝓞 K) K) ↦
      ‖χ.harmonicFactor (mixedEmbedding K a) * archGaussian y (mixedEmbedding K a)‖ := by
    simpa only [Function.comp_def, coe_idealLatticeEquiv] using
      ((idealLatticeEquiv I).summable_iff.mpr
        (χ.summable_harmonicFactor_mul_archGaussian (idealLattice K I) y hy)).norm
  refine Summable.of_norm_bounded hL fun a ↦ ?_
  rw [mul_assoc, norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (χ.primitive.norm_finiteCharacterField_le _)

/-- The twisted theta series is continuous at every parameter with positive coordinates. -/
theorem continuousAt_heckeTheta (χ : Grossencharacter K 𝔪)
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {y : realSpace K} (hy : ∀ w, 0 < y w) :
    ContinuousAt (χ.heckeTheta I) y := by
  rw [funext (χ.heckeTheta_def I)]
  refine continuousAt_const.add ?_
  simpa only [mul_assoc] using continuousAt_tsum_mul_archGaussian
    (fun a : (I : Submodule (𝓞 K) K) ↦
      χ.primitive.finiteCharacterField (a : K) * χ.harmonicFactor (mixedEmbedding K (a : K)))
    (fun a ↦ mixedEmbedding K (a : K))
    (fun δ hδ ↦ by
      simpa only [mul_assoc] using
        (χ.summable_finiteCharacterField_mul_harmonicFactor_mul_archGaussian I fun _ ↦ hδ).norm)
    hy

/-- The weighted, centered twisted theta series is bounded by a constant times the centered
ordinary theta series at half the parameter. The bound is uniform in the fractional ideal
and holds throughout the positive orthant. -/
theorem exists_norm_archWeight_mul_heckeTheta_sub_le (χ : Grossencharacter K 𝔪) :
    ∃ C ≥ 0, ∀ (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (y : realSpace K), (∀ w, 0 < y w) →
      ‖(χ.archWeight y : ℂ) * (χ.heckeTheta J y - χ.heckeEpsilon)‖ ≤
        C * ‖latticeTheta (idealLattice K J) ((1 / 2 : ℝ) • y) - 1‖ := by
  classical
  obtain ⟨C, hC, hbound⟩ := exists_norm_archWeight_mul_harmonicFactor_mul_archGaussian_le χ
  refine ⟨C, hC, fun J y hy ↦ ?_⟩
  let g : ↥(J : Submodule (𝓞 K) K) → ℂ :=
    fun a ↦ archGaussian ((1 / 2 : ℝ) • y) (mixedEmbedding K a)
  have hg : Summable g := by
    simpa only [g, Function.comp_def, coe_idealLatticeEquiv] using
      (idealLatticeEquiv J).summable_iff.mpr (summable_archGaussian (idealLattice K J)
        ((1 / 2 : ℝ) • y) (fun w ↦ mul_pos (by norm_num) (hy w)))
  let a : ↥(J : Submodule (𝓞 K) K) → ℝ :=
    Set.indicator ({0} : Set ↥(J : Submodule (𝓞 K) K))ᶜ fun x ↦ ‖g x‖
  have ha : Summable a := hg.norm.indicator {0}ᶜ
  have hnorm : ‖latticeTheta (idealLattice K J) ((1 / 2 : ℝ) • y) - 1‖ = ∑' x, a x := by
    have hθ : latticeTheta (idealLattice K J) ((1 / 2 : ℝ) • y) = ∑' x, g x := by
      rw [latticeTheta_def, ← (idealLatticeEquiv J).tsum_eq]
      simp only [g, coe_idealLatticeEquiv]
    have hg0 : g 0 = 1 := by simp [g]
    have hgPos (x : ↥(J : Submodule (𝓞 K) K)) : g x = (‖g x‖ : ℂ) := by
      simp only [g, archGaussian_apply, Complex.norm_real, Real.norm_eq_abs, Real.abs_exp]
    have hgCast (x : ↥(J : Submodule (𝓞 K) K)) :
        (if x = 0 then 0 else g x) = (a x : ℂ) := by
      by_cases hx : x = 0
      · simp [a, hx]
      simp only [a, ite_eq_right hx, Set.indicator_of_mem
        (by simpa using hx : x ∈ ({0} : Set ↥(J : Submodule (𝓞 K) K))ᶜ)]
      exact hgPos x
    rw [hθ, hg.tsum_eq_add_tsum_ite 0, hg0, add_sub_cancel_left, tsum_congr hgCast,
      ← Complex.ofReal_tsum, Complex.norm_real, Real.norm_eq_abs]
    exact abs_of_nonneg (tsum_nonneg (Set.indicator_nonneg fun _ _ ↦ norm_nonneg _))
  rw [heckeTheta_def, add_sub_cancel_left, ← tsum_mul_left, hnorm, ← tsum_mul_left]
  refine tsum_of_norm_bounded (ha.mul_left C).hasSum fun x ↦ ?_
  by_cases hx : x = 0
  · simp [hx, a]
  have hx' : x ∈ ({0}ᶜ : Set ↥(J : Submodule (𝓞 K) K)) := by simpa using hx
  simp only [a, Set.indicator_of_mem hx', g]
  calc
    _ = ‖χ.primitive.finiteCharacterField x‖ *
        ‖(χ.archWeight y : ℂ) * χ.harmonicFactor (mixedEmbedding K x) *
          archGaussian y (mixedEmbedding K x)‖ := by simp only [norm_mul]; ring
    _ ≤ _ := (mul_le_of_le_one_left (norm_nonneg _)
      (χ.primitive.norm_finiteCharacterField_le _)).trans (hbound y hy (mixedEmbedding K x))

/-- **The twisted theta series depends only on the Hecke character**, not on the presentation
modulus. -/
theorem heckeTheta_congr {χ : Grossencharacter K 𝔪} {ψ : Grossencharacter K 𝔫}
    (h : χ.toHeckeCharacter = ψ.toHeckeCharacter) : χ.heckeTheta = ψ.heckeTheta := by
  have hf : χ.primitive.finiteCharacterField = ψ.primitive.finiteCharacterField :=
    finiteCharacterField_congr (by rw [toHeckeCharacter_primitive, toHeckeCharacter_primitive, h])
      (congrArg Modulus.finitePart (conductor_congr h))
  funext I y
  simp only [heckeTheta_def, heckeEpsilon_congr h, harmonicFactor_congr h, hf]

/-- The primitive presentation has the same twisted theta series. -/
@[simp]
theorem heckeTheta_primitive (χ : Grossencharacter K 𝔪) : χ.primitive.heckeTheta = χ.heckeTheta :=
  heckeTheta_congr χ.toHeckeCharacter_primitive

open scoped Classical in
/-- At an integral ideal `𝔞`, `χ.heckeTheta (FractionalIdeal.mk0 K 𝔞) y` is the sum over `a : 𝔞`
weighted by `χ.primitive.finiteCharacter (a : 𝓞 K)`. -/
theorem heckeTheta_mk0 (χ : Grossencharacter K 𝔪) (𝔞 : (Ideal (𝓞 K))⁰) (y : realSpace K) :
    χ.heckeTheta (FractionalIdeal.mk0 K 𝔞) y =
      χ.heckeEpsilon +
        ∑' a : (𝔞 : Ideal (𝓞 K)), χ.primitive.finiteCharacter (a : 𝓞 K) *
          χ.harmonicFactor (mixedEmbedding K ((a : 𝓞 K) : K)) *
          archGaussian y (mixedEmbedding K ((a : 𝓞 K) : K)) := by
  rw [heckeTheta_def, FractionalIdeal.coe_mk0,
    ← (FractionalIdeal.coeIdealEquiv (S := (𝓞 K)⁰) (P := K)
      (𝔞 : Ideal (𝓞 K))).symm.toEquiv.tsum_eq]
  congr 1
  refine tsum_congr fun a ↦ ?_
  rw [LinearEquiv.coe_toEquiv, FractionalIdeal.coe_coeIdealEquiv_symm_apply,
    χ.primitive.finiteCharacterField_algebraMap]

/-- Monotone domination of `‖χ.heckeTheta I y‖` by the absolute series majorant at any smaller
positive parameter `y' ≤ y`. -/
theorem norm_heckeTheta_le (χ : Grossencharacter K 𝔪) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {y y' : realSpace K} (hy' : ∀ w, 0 < y' w) (h : ∀ w, y' w ≤ y w) :
    ‖χ.heckeTheta I y‖ ≤ ‖χ.heckeEpsilon‖ +
      ∑' a : (I : Submodule (𝓞 K) K),
        ‖χ.primitive.finiteCharacterField (a : K) *
          χ.harmonicFactor (mixedEmbedding K (a : K)) *
          archGaussian y' (mixedEmbedding K (a : K))‖ := by
  have hsum' := χ.summable_finiteCharacterField_mul_harmonicFactor_mul_archGaussian I hy'
  rw [heckeTheta_def]
  refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
  refine tsum_of_norm_bounded hsum'.norm.hasSum fun a ↦ ?_
  rw [norm_mul, norm_mul, norm_mul, norm_mul]
  exact mul_le_mul_of_nonneg_left (norm_archGaussian_le h _)
    (mul_nonneg (norm_nonneg _) (norm_nonneg _))

open scoped Classical in
/-- Separating the constant term `χ.heckeEpsilon` from the nonzero elements of `I` in
`χ.heckeTheta I y`. -/
theorem heckeTheta_eq_heckeEpsilon_add (χ : Grossencharacter K 𝔪)
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (y : realSpace K) :
    χ.heckeTheta I y =
      χ.heckeEpsilon +
        ∑' a : {a : (I : Submodule (𝓞 K) K) // a ≠ 0},
          χ.primitive.finiteCharacterField ((a : (I : Submodule (𝓞 K) K)) : K) *
            χ.harmonicFactor (mixedEmbedding K ((a : (I : Submodule (𝓞 K) K)) : K)) *
            archGaussian y (mixedEmbedding K ((a : (I : Submodule (𝓞 K) K)) : K)) := by
  have hsupp : Function.support (fun a : (I : Submodule (𝓞 K) K) ↦
      χ.primitive.finiteCharacterField (a : K) * χ.harmonicFactor (mixedEmbedding K (a : K)) *
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
      ‖(χ.primitive.finiteCharacterField ((a : (I : Submodule (𝓞 K) K)) : K) *
          χ.harmonicFactor (mixedEmbedding K ((a : (I : Submodule (𝓞 K) K)) : K))) *
        archGaussian (fun _ ↦ (1 / 2 : ℝ))
          (mixedEmbedding K ((a : (I : Submodule (𝓞 K) K)) : K))‖ := by
    simpa only [mul_assoc, Function.comp_def] using
      (χ.summable_finiteCharacterField_mul_harmonicFactor_mul_archGaussian I
        (fun _ ↦ by norm_num)).norm.comp_injective Subtype.coe_injective
  obtain ⟨c, hc, C, hC, h⟩ := exists_norm_tsum_mul_archGaussian_le
    (fun a : {a : (I : Submodule (𝓞 K) K) // a ≠ 0} ↦
      χ.primitive.finiteCharacterField ((a : (I : Submodule (𝓞 K) K)) : K) *
        χ.harmonicFactor (mixedEmbedding K ((a : (I : Submodule (𝓞 K) K)) : K)))
    (fun a ↦ mixedEmbedding K ((a : (I : Submodule (𝓞 K) K)) : K)) hδ
    (fun a ↦ by
      simpa only [coe_idealLatticeEquiv] using
        hL (idealLatticeEquiv I a.val) fun h0 ↦ a.property (Subtype.ext
          (mixedEmbedding_injective K
            (by simpa [coe_idealLatticeEquiv] using congrArg Subtype.val h0))))
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

/-! ### Unit invariance, Neukirch VII (8.2) -/

/-- **Reindexing the twisted theta series by a unit.** Moving a unit `u` from the parameter to
the lattice point multiplies the nonconstant part of the series by `(χ_f(u) N(u ^ p))⁻¹`, that is,
by `∏_w |u_w| ^ (-P_w)` (`finiteCharacter_mul_harmonicFactor_unit`):
`∏_w |u_w| ^ P_w (θ_χ(𝔞, |u|² y) - ε(χ)) = θ_χ(𝔞, y) - ε(χ)`. No positivity of `y` is needed:
the reindexing is a bijection of the lattice points. -/
theorem prod_mul_heckeTheta_unitScale_sub_heckeEpsilon (χ : Grossencharacter K 𝔪)
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (u : (𝓞 K)ˣ) (y : realSpace K) :
    ((∏ w : InfinitePlace K,
        normAtPlace w (mixedEmbedding K (u : K)) ^ χ.harmonicExponent w : ℝ) : ℂ) *
        (χ.heckeTheta I (unitScale u y) - χ.heckeEpsilon) =
      χ.heckeTheta I y - χ.heckeEpsilon := by
  -- multiplication by `u` permutes the points of `𝔞`
  let e : (I : Submodule (𝓞 K) K) ≃ (I : Submodule (𝓞 K) K) :=
    Equiv.subtypeEquiv (MulAction.toPerm u) fun a ↦ (Submodule.smul_mem_iff' _ u).symm
  have he (a : (I : Submodule (𝓞 K) K)) : (e a : K) = (u : K) * a :=
    (Units.smul_def u (a : K)).trans (Algebra.smul_def _ _)
  -- on a unit the finite character of the primitive presentation is the archimedean factor
  have hu : χ.primitive.finiteCharacterField (u : K) * χ.harmonicFactor (mixedEmbedding K u) =
      ((∏ w : InfinitePlace K,
        normAtPlace w (mixedEmbedding K (u : K)) ^ χ.harmonicExponent w : ℝ) : ℂ) := by
    rw [finiteCharacterField_algebraMap,
      ← harmonicFactor_congr χ.toHeckeCharacter_primitive,
      χ.primitive.finiteCharacter_mul_harmonicFactor_unit u]
    simp_rw [harmonicExponent_congr χ.toHeckeCharacter_primitive]
  have hmul (a : K) : χ.primitive.finiteCharacterField ((u : K) * a) =
      χ.primitive.finiteCharacterField (u : K) * χ.primitive.finiteCharacterField a := by
    have hcoe : (u : K) = ((unitsToPrimeToSubgroup χ.conductor u : Kˣ) : K) := by
      simp
    rw [hcoe, finiteCharacterField_coe_mul, finiteCharacterField_coe]
  simp only [heckeTheta_def, add_sub_cancel_left, ← tsum_mul_left]
  conv_rhs => rw [← e.tsum_eq]
  refine tsum_congr fun a ↦ ?_
  rw [he, map_mul, χ.harmonicFactor_mul, hmul, ← unitSMul_smul, archGaussian_unit_smul, ← hu]
  ring

/-- **Neukirch VII (8.2): the weighted twisted theta series is invariant under the units.**
For every unit `u`, `N((|u|² y) ^ (p/2)) θ_χ(𝔞, |u|² y) = N(y ^ (p/2)) θ_χ(𝔞, y)`: the weight
gains the factor `∏_w |u_w| ^ P_w` (`archWeight_unitScale`) that the reindexed series loses
(`prod_mul_heckeTheta_unitScale_sub_heckeEpsilon`), and the constant `ε(χ)` is nonzero only when
every `P_w` vanishes. -/
theorem archWeight_mul_heckeTheta_unitScale (χ : Grossencharacter K 𝔪)
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (u : (𝓞 K)ˣ) (y : realSpace K) :
    (χ.archWeight (unitScale u y) : ℂ) * χ.heckeTheta I (unitScale u y) =
      (χ.archWeight y : ℂ) * χ.heckeTheta I y := by
  rw [archWeight_unitScale, ofReal_mul]
  have key := χ.prod_mul_heckeTheta_unitScale_sub_heckeEpsilon I u y
  set μ : ℝ := ∏ w : InfinitePlace K,
    normAtPlace w (mixedEmbedding K (u : K)) ^ χ.harmonicExponent w
  -- the constant term is `0` unless every local degree vanishes, and then `μ = 1`
  have hεμ : χ.heckeEpsilon * ((μ : ℂ) - 1) = 0 := by
    by_cases hε : χ.heckeEpsilon = 0
    · rw [hε, zero_mul]
    obtain ⟨-, hdeg⟩ := not_or.mp (mt χ.heckeEpsilon_eq_zero_iff.mpr hε)
    have hexp := χ.harmonicExponent_eq_zero_of_harmonicDegree_eq_zero (not_not.mp hdeg)
    simp [μ, hexp]
  linear_combination (χ.archWeight y : ℂ) * key + (χ.archWeight y : ℂ) * hεμ

/-! ### The untwisted case -/

/-- **With trivial finite conductor and constant harmonic polynomial, the twisted theta series is
the theta series of the ideal lattice**: then `ε(χ) = 1`, the polynomial is `1`, and the finite
character is `1` at every nonzero element. This covers the trivial character, whose twisted theta
series is Hecke's theta series of `𝔞`, and the odd norm powers of `ℚ`, which have presentation
conductor `∞` and the same series. The positivity of `y` is needed: at `y = 0` the theta series of
the lattice is `0`, by the convention for nonsummable series, while the twisted series is `1`. -/
theorem heckeTheta_eq_latticeTheta (χ : Grossencharacter K 𝔪) (hχ : χ.heckeEpsilon = 1)
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {y : realSpace K} (hy : ∀ w, 0 < y w) :
    χ.heckeTheta I y = latticeTheta (idealLattice K I) y := by
  classical
  obtain ⟨hf, hdeg⟩ := χ.heckeEpsilon_eq_one_iff.mp hχ
  have hsum :
      Summable fun a : (I : Submodule (𝓞 K) K) ↦ archGaussian y (mixedEmbedding K a) := by
    simpa only [Function.comp_def, coe_idealLatticeEquiv] using
      (idealLatticeEquiv I).summable_iff.mpr (summable_archGaussian (idealLattice K I) y hy)
  have hterm (a : (I : Submodule (𝓞 K) K)) :
      χ.primitive.finiteCharacterField a * χ.harmonicFactor (mixedEmbedding K a) *
          archGaussian y (mixedEmbedding K a) =
        if a = 0 then 0 else archGaussian y (mixedEmbedding K a) := by
    split_ifs with ha
    · simp [ha]
    · rw [χ.primitive.finiteCharacterField_eq_one_of_finitePart_eq_top
          (by rwa [finitePart_conductor]) (by simpa using (Subtype.ext_iff.not.mp ha)),
        χ.harmonicFactor_eq_one_of_harmonicDegree_eq_zero hdeg, one_mul, one_mul]
  rw [heckeTheta_def, hχ, latticeTheta_def, ← (idealLatticeEquiv I).tsum_eq]
  simp only [coe_idealLatticeEquiv]
  rw [hsum.tsum_eq_add_tsum_ite 0, tsum_congr hterm]
  simp

end Grossencharacter

end TauCeti.LFunctions
