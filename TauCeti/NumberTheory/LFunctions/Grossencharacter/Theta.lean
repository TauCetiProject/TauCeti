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
* `archWeight_mul_heckeTheta_unitScale`: Neukirch VII (8.2).
* `heckeTheta_eq_latticeTheta`: the untwisted case.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §§7–8, (8.2).
-/

public section
noncomputable section

open Complex NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
  TauCeti.NumberField.mixedEmbedding
open scoped NumberField nonZeroDivisors
open scoped Topology

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
  let z : realSpace K := fun w ↦ y w / 2
  let U : Set (realSpace K) := {p | ∀ w, z w < p w}
  have hU : IsOpen U := by
    simp only [U, Set.ofPred_forall]
    exact isOpen_iInter_of_finite fun w ↦ isOpen_lt continuous_const (continuous_apply w)
  have hyU : y ∈ U := fun w ↦ half_lt_self (hy w)
  have hsum := (χ.summable_finiteCharacterField_mul_harmonicFactor_mul_archGaussian I
    (y := z) (fun w ↦ half_pos (hy w))).norm
  rw [funext (χ.heckeTheta_def I)]
  refine continuousAt_const.add ((continuousOn_tsum (s := U) ?_ hsum ?_).continuousAt
    (hU.mem_nhds hyU))
  · exact fun a ↦ (continuous_const.mul (continuous_archGaussian (mixedEmbedding K a))).continuousOn
  · intro a p hp
    simp only [norm_mul]
    exact mul_le_mul_of_nonneg_left
      (norm_archGaussian_le (fun w ↦ (hp w).le) (mixedEmbedding K a)) (by positivity)

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
