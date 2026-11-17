/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.BesselPotential.Inclusion
import Mathlib.Analysis.Normed.Operator.Extend
import TauCeti.Analysis.Distribution.SchwartzSpace.Fourier

/-!
# Extensions of Schwartz-space operators to Bessel-potential spaces

A continuous linear map `A : 𝓢(E, F) →L[ℂ] 𝓢(E, G)` between complete complex normed fibres *extends*
to a bounded operator `H^s(E, F) → H^r(E, G)` between Mathlib's Bessel-potential spaces
`H^s = H^{s,2}` if some `T : H^s(E, F) →L[ℂ] H^r(E, G)` agrees with `A` on Schwartz functions
(`SchwartzMap.HasSobolevExtension`). Operators such as pseudodifferential operators are first
defined and estimated on Schwartz functions, and their Sobolev mapping properties are statements of
this form.

More generally, `SchwartzMap.extendBesselPotentialSpace` packages the canonical continuous extension
`H^{s,p}(E, F) →L[ℂ] H^{r,p}(E, G)` via `LinearMap.extendOfNorm` for any `1 ≤ p ≤ ∞`; when `p < ∞`
and `A` satisfies an `H^{s,p} → H^{r,p}` estimate on Schwartz functions, it is the unique bounded
operator agreeing with `A` on Schwartz space (and `0` otherwise).

This file proves that such extensions are closed under composition and linear combinations, that
the target order may be lowered, and that the Bessel multiplier `J^t`, the Fourier multiplier with
symbol `⟨ξ⟩ ^ t = (1 + ‖ξ‖ ^ 2) ^ (t / 2)`, extends to an operator `H^s → H^{s - t}`.

## Main declarations

* `SchwartzMap.extendBesselPotentialSpace`: canonical continuous extension
  `H^{s,p}(E, F) →L[ℂ] H^{r,p}(E, G)` with Schwartz agreement, norm bound, uniqueness, linearity
  (`_zero`, `_add`, `_smul`, `_neg`, `_sub`), composition (`_comp`), and order compatibility
  (`inclusion_comp_extendBesselPotentialSpace_of_eq`).
* `SchwartzMap.HasSobolevExtension`: `A` extends to a bounded operator `H^s → H^r`, characterised
  by `SchwartzMap.hasSobolevExtension_iff`.
* `SchwartzMap.hasSobolevExtension_iff_exists_norm_le`: `A` extends to `H^s → H^r` exactly when
  `‖A u‖_{H^r} ≤ C ‖u‖_{H^s}` for every Schwartz function `u`, since Schwartz functions are dense
  in `H^s`.
* `SchwartzMap.hasSobolevExtension_zero`, `SchwartzMap.hasSobolevExtension_id`: the zero map and the
  identity extend.
* `SchwartzMap.HasSobolevExtension.comp`, `SchwartzMap.HasSobolevExtension.add`,
  `SchwartzMap.HasSobolevExtension.neg`, `SchwartzMap.HasSobolevExtension.smul`,
  `SchwartzMap.HasSobolevExtension.sub`: extensions compose and form a vector space.
* `SchwartzMap.HasSobolevExtension.mono`: an extension into `H^r` is one into every `H^{r'}` with
  `r' ≤ r`.
* `SchwartzMap.hasSobolevExtension_besselMultiplier`: `J^t` extends to `H^s → H^{s - t}`.
-/

public section

noncomputable section

open MeasureTheory
open scoped ENNReal SchwartzMap BesselPotentialSpace

namespace SchwartzMap

variable {E F G K : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [NormedSpace ℂ G] [CompleteSpace G]
  [NormedAddCommGroup K] [NormedSpace ℂ K] [CompleteSpace K]

/-- The canonical continuous extension of `A : 𝓢(E, F) →L[ℂ] 𝓢(E, G)` to
`H^{s,p}(E, F) →L[ℂ] H^{r,p}(E, G)` via `LinearMap.extendOfNorm`. When `p < ∞` and `A` satisfies an
`H^{s,p} → H^{r,p}` estimate on Schwartz functions, it is the unique continuous linear map agreeing
with `A` on Schwartz space; without such an estimate it is `0`. -/
def extendBesselPotentialSpace (A : 𝓢(E, F) →L[ℂ] 𝓢(E, G)) (s r : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    H^{s, p}(E, F) →L[ℂ] H^{r, p}(E, G) :=
  ((toBesselPotentialSpaceCLM (E := E) (F := G) r p).comp A).toLinearMap.extendOfNorm
    (toBesselPotentialSpaceCLM (E := E) (F := F) s p).toLinearMap

section Extend

variable {A B : 𝓢(E, F) →L[ℂ] 𝓢(E, G)} {s r q : ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- On Schwartz functions, `extendBesselPotentialSpace A s r p` agrees with `A` whenever `p < ∞`
and `A` satisfies an `H^{s,p} → H^{r,p}` norm bound. -/
theorem extendBesselPotentialSpace_toBesselPotentialSpaceCLM (hp : p ≠ ∞)
    (hC : ∃ C, ∀ u, ‖toBesselPotentialSpaceCLM r p (A u)‖ ≤ C * ‖toBesselPotentialSpaceCLM s p u‖)
    (u : 𝓢(E, F)) :
    extendBesselPotentialSpace A s r p (toBesselPotentialSpaceCLM s p u) =
      toBesselPotentialSpaceCLM r p (A u) :=
  LinearMap.extendOfNorm_eq (denseRange_toBesselPotentialSpaceCLM s hp) hC u

/-- Operator-norm bound for `extendBesselPotentialSpace A s r p` from a Schwartz-space estimate. -/
theorem norm_extendBesselPotentialSpace_le {C : ℝ} (hp : p ≠ ∞) (hC0 : 0 ≤ C)
    (hC : ∀ u, ‖toBesselPotentialSpaceCLM r p (A u)‖ ≤ C * ‖toBesselPotentialSpaceCLM s p u‖) :
    ‖extendBesselPotentialSpace A s r p‖ ≤ C :=
  LinearMap.opNorm_extendOfNorm_le (denseRange_toBesselPotentialSpaceCLM s hp) hC0 hC

/-- Uniqueness of the canonical extension: any continuous linear map `T : H^{s,p} →L[ℂ] H^{r,p}`
agreeing with `A` on Schwartz functions equals `extendBesselPotentialSpace A s r p` (`p < ∞`). -/
theorem extendBesselPotentialSpace_eq_of_forall (hp : p ≠ ∞)
    {T : H^{s, p}(E, F) →L[ℂ] H^{r, p}(E, G)}
    (hT : ∀ u, T (toBesselPotentialSpaceCLM s p u) = toBesselPotentialSpaceCLM r p (A u)) :
    extendBesselPotentialSpace A s r p = T :=
  BesselPotentialSpace.continuousLinearMap_ext hp fun u ↦ by
    rw [extendBesselPotentialSpace_toBesselPotentialSpaceCLM hp
      ⟨‖T‖, fun v ↦ by rw [← hT v]; exact T.le_opNorm _⟩ u, hT u]

/-- The canonical extension of the zero operator is `0`. -/
@[simp] theorem extendBesselPotentialSpace_zero (s r : ℝ) (hp : p ≠ ∞) :
    extendBesselPotentialSpace (0 : 𝓢(E, F) →L[ℂ] 𝓢(E, G)) s r p = 0 :=
  extendBesselPotentialSpace_eq_of_forall hp fun _ ↦ by simp

/-- The canonical extension is additive on bounded operators. -/
theorem extendBesselPotentialSpace_add (hp : p ≠ ∞)
    (hA : ∃ C, ∀ u, ‖toBesselPotentialSpaceCLM r p (A u)‖ ≤ C * ‖toBesselPotentialSpaceCLM s p u‖)
    (hB : ∃ C, ∀ u, ‖toBesselPotentialSpaceCLM r p (B u)‖ ≤ C * ‖toBesselPotentialSpaceCLM s p u‖) :
    extendBesselPotentialSpace (A + B) s r p =
      extendBesselPotentialSpace A s r p + extendBesselPotentialSpace B s r p :=
  extendBesselPotentialSpace_eq_of_forall hp fun u ↦ by
    simp [extendBesselPotentialSpace_toBesselPotentialSpaceCLM hp hA u,
      extendBesselPotentialSpace_toBesselPotentialSpaceCLM hp hB u]

/-- The canonical extension is homogeneous on bounded operators. -/
theorem extendBesselPotentialSpace_smul (hp : p ≠ ∞)
    (hA : ∃ C, ∀ u, ‖toBesselPotentialSpaceCLM r p (A u)‖ ≤ C * ‖toBesselPotentialSpaceCLM s p u‖)
    (c : ℂ) :
    extendBesselPotentialSpace (c • A) s r p = c • extendBesselPotentialSpace A s r p :=
  extendBesselPotentialSpace_eq_of_forall hp fun u ↦ by
    simp [extendBesselPotentialSpace_toBesselPotentialSpaceCLM hp hA u]

/-- The canonical extension preserves negation on bounded operators. -/
theorem extendBesselPotentialSpace_neg (hp : p ≠ ∞)
    (hA : ∃ C, ∀ u, ‖toBesselPotentialSpaceCLM r p (A u)‖ ≤ C * ‖toBesselPotentialSpaceCLM s p u‖) :
    extendBesselPotentialSpace (-A) s r p = -extendBesselPotentialSpace A s r p :=
  extendBesselPotentialSpace_eq_of_forall hp fun u ↦ by
    simp [extendBesselPotentialSpace_toBesselPotentialSpaceCLM hp hA u]

/-- The canonical extension preserves subtraction on bounded operators. -/
theorem extendBesselPotentialSpace_sub (hp : p ≠ ∞)
    (hA : ∃ C, ∀ u, ‖toBesselPotentialSpaceCLM r p (A u)‖ ≤ C * ‖toBesselPotentialSpaceCLM s p u‖)
    (hB : ∃ C, ∀ u, ‖toBesselPotentialSpaceCLM r p (B u)‖ ≤ C * ‖toBesselPotentialSpaceCLM s p u‖) :
    extendBesselPotentialSpace (A - B) s r p =
      extendBesselPotentialSpace A s r p - extendBesselPotentialSpace B s r p :=
  extendBesselPotentialSpace_eq_of_forall hp fun u ↦ by
    simp [extendBesselPotentialSpace_toBesselPotentialSpaceCLM hp hA u,
      extendBesselPotentialSpace_toBesselPotentialSpaceCLM hp hB u]

/-- The canonical extension preserves composition of bounded operators. -/
theorem extendBesselPotentialSpace_comp {C : 𝓢(E, G) →L[ℂ] 𝓢(E, K)} (hp : p ≠ ∞)
    (hC : ∃ M, ∀ u, ‖toBesselPotentialSpaceCLM q p (C u)‖ ≤ M * ‖toBesselPotentialSpaceCLM r p u‖)
    (hA : ∃ M, ∀ u, ‖toBesselPotentialSpaceCLM r p (A u)‖ ≤ M * ‖toBesselPotentialSpaceCLM s p u‖) :
    extendBesselPotentialSpace (C ∘L A) s q p =
      extendBesselPotentialSpace C r q p ∘L extendBesselPotentialSpace A s r p :=
  extendBesselPotentialSpace_eq_of_forall hp fun u ↦ by
    simp [extendBesselPotentialSpace_toBesselPotentialSpaceCLM hp hA u,
      extendBesselPotentialSpace_toBesselPotentialSpaceCLM hp hC (A u)]

end Extend

/-- Composing `extendBesselPotentialSpace` with the inclusion across equal target orders. -/
theorem inclusion_comp_extendBesselPotentialSpace_of_eq {A : 𝓢(E, F) →L[ℂ] 𝓢(E, G)}
    {s r r' : ℝ} (h : r = r') (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    BesselPotentialSpace.inclusion h.ge ∘L extendBesselPotentialSpace A s r p =
      extendBesselPotentialSpace A s r' p := by
  subst h; ext1 u; simp

/-- A continuous linear map `A` of Schwartz spaces extends to a bounded operator `H^s → H^r`: some
continuous linear map `T : H^s(E, F) →L[ℂ] H^r(E, G)` agrees with `A` on Schwartz functions. -/
def HasSobolevExtension (A : 𝓢(E, F) →L[ℂ] 𝓢(E, G)) (s r : ℝ) : Prop :=
  ∃ T : H^{s}(E, F) →L[ℂ] H^{r}(E, G),
    T ∘L toBesselPotentialSpaceCLM s 2 = toBesselPotentialSpaceCLM r 2 ∘L A

/-- `A` extends to a bounded operator `H^s → H^r` if and only if some continuous linear map
`T : H^s(E, F) →L[ℂ] H^r(E, G)` agrees with `A` on Schwartz functions. -/
theorem hasSobolevExtension_iff {A : 𝓢(E, F) →L[ℂ] 𝓢(E, G)} {s r : ℝ} :
    HasSobolevExtension A s r ↔ ∃ T : H^{s}(E, F) →L[ℂ] H^{r}(E, G),
      T ∘L toBesselPotentialSpaceCLM s 2 = toBesselPotentialSpaceCLM r 2 ∘L A :=
  Iff.rfl

/-- `A` extends to a bounded operator `H^s → H^r` if and only if the a priori estimate
`‖A u‖_{H^r} ≤ C ‖u‖_{H^s}` holds for some `C ≥ 0` and every Schwartz function `u`. -/
theorem hasSobolevExtension_iff_exists_norm_le {A : 𝓢(E, F) →L[ℂ] 𝓢(E, G)} {s r : ℝ} :
    HasSobolevExtension A s r ↔ ∃ C ≥ 0, ∀ u,
      ‖toBesselPotentialSpaceCLM r 2 (A u)‖ ≤ C * ‖toBesselPotentialSpaceCLM s 2 u‖ := by
  constructor
  · rintro ⟨T, hT⟩
    refine ⟨‖T‖, norm_nonneg T, fun u ↦ ?_⟩
    rw [← ContinuousLinearMap.comp_apply (toBesselPotentialSpaceCLM r 2) A, ← hT,
      ContinuousLinearMap.comp_apply]
    exact T.le_opNorm _
  · rintro ⟨C, -, hC⟩
    exact ⟨extendBesselPotentialSpace A s r 2, ContinuousLinearMap.ext fun u ↦
      extendBesselPotentialSpace_toBesselPotentialSpaceCLM ENNReal.ofNat_ne_top ⟨C, hC⟩ u⟩

/-- The zero map extends to a bounded operator `H^s → H^r`. -/
theorem hasSobolevExtension_zero (s r : ℝ) :
    HasSobolevExtension (0 : 𝓢(E, F) →L[ℂ] 𝓢(E, G)) s r :=
  ⟨0, by rw [ContinuousLinearMap.zero_comp, ContinuousLinearMap.comp_zero]⟩

/-- The identity extends to a bounded operator `H^s → H^s`. -/
theorem hasSobolevExtension_id (s : ℝ) :
    HasSobolevExtension (ContinuousLinearMap.id ℂ 𝓢(E, F)) s s :=
  ⟨ContinuousLinearMap.id ℂ _, by rw [ContinuousLinearMap.id_comp, ContinuousLinearMap.comp_id]⟩

namespace HasSobolevExtension

variable {A B : 𝓢(E, F) →L[ℂ] 𝓢(E, G)} {s r q : ℝ}

/-- On Schwartz functions, `extendBesselPotentialSpace A s r 2` agrees with `A` whenever `A` has a
Sobolev extension `H^s → H^r`. -/
theorem extendBesselPotentialSpace_toBesselPotentialSpaceCLM (hA : HasSobolevExtension A s r)
    (u : 𝓢(E, F)) :
    extendBesselPotentialSpace A s r 2 (toBesselPotentialSpaceCLM s 2 u) =
      toBesselPotentialSpaceCLM r 2 (A u) := by
  obtain ⟨T, hT⟩ := hA
  rw [extendBesselPotentialSpace_eq_of_forall (p := 2) ENNReal.ofNat_ne_top fun v ↦
    congrArg (fun S ↦ S v) hT]
  exact congrArg (fun S ↦ S u) hT

/-- Extensions `H^s → H^r` and `H^r → H^q` compose to an extension `H^s → H^q`. -/
theorem comp {C : 𝓢(E, G) →L[ℂ] 𝓢(E, K)} (hC : HasSobolevExtension C r q)
    (hA : HasSobolevExtension A s r) : HasSobolevExtension (C ∘L A) s q := by
  obtain ⟨T, hT⟩ := hA
  obtain ⟨T', hT'⟩ := hC
  exact ⟨T' ∘L T, by rw [ContinuousLinearMap.comp_assoc, hT, ← ContinuousLinearMap.comp_assoc,
    hT', ContinuousLinearMap.comp_assoc]⟩

/-- The sum of operators extending to `H^s → H^r` extends to `H^s → H^r`. -/
theorem add (hA : HasSobolevExtension A s r) (hB : HasSobolevExtension B s r) :
    HasSobolevExtension (A + B) s r := by
  obtain ⟨T, hT⟩ := hA
  obtain ⟨T', hT'⟩ := hB
  exact ⟨T + T', by rw [ContinuousLinearMap.add_comp, hT, hT', ContinuousLinearMap.comp_add]⟩

/-- The negative of an operator extending to `H^s → H^r` extends to `H^s → H^r`. -/
theorem neg (hA : HasSobolevExtension A s r) : HasSobolevExtension (-A) s r := by
  obtain ⟨T, hT⟩ := hA
  exact ⟨-T, by rw [ContinuousLinearMap.neg_comp, hT, ContinuousLinearMap.comp_neg]⟩

/-- A complex multiple of an operator extending to `H^s → H^r` extends to `H^s → H^r`. -/
theorem smul (hA : HasSobolevExtension A s r) (c : ℂ) : HasSobolevExtension (c • A) s r := by
  obtain ⟨T, hT⟩ := hA
  exact ⟨c • T, by rw [ContinuousLinearMap.smul_comp, hT, ContinuousLinearMap.comp_smul]⟩

/-- A real multiple of an operator extending to `H^s → H^r` extends to `H^s → H^r`. -/
theorem smul_real (hA : HasSobolevExtension A s r) (c : ℝ) : HasSobolevExtension (c • A) s r := by
  simpa only [Complex.coe_smul] using hA.smul (c : ℂ)

/-- The difference of operators extending to `H^s → H^r` extends to `H^s → H^r`. -/
theorem sub (hA : HasSobolevExtension A s r) (hB : HasSobolevExtension B s r) :
    HasSobolevExtension (A - B) s r := by
  simpa only [sub_eq_add_neg] using hA.add hB.neg

/-- Extensions into `H^r` are extensions into every `H^{r'}` with `r' ≤ r`. -/
theorem mono (hA : HasSobolevExtension A s r) {r' : ℝ} (h : r' ≤ r) :
    HasSobolevExtension A s r' := by
  obtain ⟨T, hT⟩ := hA
  refine ⟨BesselPotentialSpace.inclusion h ∘L T, ?_⟩
  rw [ContinuousLinearMap.comp_assoc, hT, ← ContinuousLinearMap.comp_assoc]
  congr 1
  exact ContinuousLinearMap.ext (BesselPotentialSpace.inclusion_toBesselPotentialSpaceCLM h)

end HasSobolevExtension

/-- The Bessel multiplier `J^t`, the Fourier multiplier with symbol `⟨ξ⟩ ^ t`, extends to a
bounded operator `H^s → H^r` when `r + t = s`. -/
theorem hasSobolevExtension_besselMultiplier {s r : ℝ} (t : ℝ) (h : r + t = s) :
    HasSobolevExtension (fourierMultiplierCLM F
      (fun ζ : E ↦ (((1 + ‖ζ‖ ^ 2) ^ (t / 2) : ℝ) : ℂ))) s r := by
  refine ⟨((BesselPotentialSpace.toLpₗᵢ E F r 2).symm.toContinuousLinearEquiv :
      Lp F 2 (volume : Measure E) →L[ℂ] H^{r}(E, F)) ∘L
    ((BesselPotentialSpace.toLpₗᵢ E F s 2).toContinuousLinearEquiv :
      H^{s}(E, F) →L[ℂ] Lp F 2 (volume : Measure E)), ?_⟩
  ext1 u
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv, BesselPotentialSpace.toLpₗᵢ_apply,
    toLp_toBesselPotentialSpaceCLM, LinearIsometryEquiv.symm_apply_eq,
    fourierMultiplierCLM_one_add_norm_sq_rpow_fourierMultiplierCLM, h]

end SchwartzMap
