/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.PowerSeries.Derivative
public import TauCeti.RingTheory.PowerSeries.OpenDisc.Rescale

/-!
# Hasse derivatives, ordinary derivatives, and the chain rule on open discs

Over any normed ring `R`, Hasse derivatives `D⁽ᵏ⁾` preserve the open-disc radius condition: any
polynomial growth of binomial coefficients is absorbed at an intermediate radius inside the open
disc. Hence `D⁽ᵏ⁾` restricts to an `R`-linear endomorphism
`TauCeti.PowerSeries.OnOpenDisc.hasseDeriv` of `PowerSeries.OnOpenDisc.subring R R₀` without any
commutativity or ultrametric hypothesis, satisfying the ordered Leibniz rule, the composition law
`D⁽ᵏ⁾ ∘ D⁽ˡ⁾ = (k + l).choose k • D⁽ᵏ⁺ˡ⁾`, and naturality with bounded coefficient maps.

Over a normed commutative ring `R`, the first Hasse derivative upgrades to an `R`-derivation
`TauCeti.PowerSeries.OnOpenDisc.derivative` on `OnOpenDisc.subring R R₀`, related to higher Hasse
derivatives by `k ! • hasseDeriv k f = derivative^[k] f`, and having kernel reduced to scalar
constants when `R` has no additive torsion (`[HasUniqueDiv R]`).

Over an ultrametric normed ring, `hasseDeriv k` satisfies the closed-disc Cauchy estimate
`‖restrict r (hasseDeriv k f)‖ ≤ r⁻ᵏ ‖restrict r f‖` at every radius `0 < r < R₀` and is
uniformly continuous for the Gauss uniformity; when `R` is also commutative, `derivative` satisfies
`‖restrict r (derivative f)‖ ≤ r⁻¹ ‖restrict r f‖` and is likewise uniformly continuous. Over a
complete ultrametric normed commutative
ring, derivatives commute with Taylor translation, intertwine with rescaling and affine coordinate
changes by the appropriate power of the scaling factor, and satisfy the **chain rule for analytic
substitution**:

```text
derivative (analyticSubst g hg f) = analyticSubst g hg (derivative f) * derivative g,
```

valid for inner series `g` with arbitrary (possibly non-nilpotent) constant term.

## Main definitions

* `TauCeti.PowerSeries.OnOpenDisc.hasseDeriv`: the `k`th Hasse derivative as an `R`-linear map on
  `OnOpenDisc.subring R R₀` over any normed ring.
* `TauCeti.PowerSeries.OnOpenDisc.derivative`: the formal derivative as an `R`-derivation on
  `OnOpenDisc.subring R R₀` over any normed commutative ring.

## Main results

* `TauCeti.PowerSeries.OnOpenDisc.hasseDeriv_comp` and
  `TauCeti.PowerSeries.OnOpenDisc.hasseDeriv_mul`: composition law and noncommutative Leibniz rule
  for Hasse derivatives on an open disc.
* `TauCeti.PowerSeries.OnOpenDisc.norm_restrict_hasseDeriv_le`,
  `TauCeti.PowerSeries.OnOpenDisc.uniformContinuous_hasseDeriv`,
  `TauCeti.PowerSeries.OnOpenDisc.norm_restrict_derivative_le`, and
  `TauCeti.PowerSeries.OnOpenDisc.uniformContinuous_derivative`: Cauchy estimates and uniform
  continuity in the open-disc Gauss uniformity.
* `TauCeti.PowerSeries.OnOpenDisc.derivative_eq_zero_iff`: over `[HasUniqueDiv R]`, open-disc
  series with vanishing derivative are constants.
* `TauCeti.PowerSeries.OnOpenDisc.mapHom_hasseDeriv`,
  `TauCeti.PowerSeries.OnOpenDisc.hasseDeriv_taylorHom`,
  `TauCeti.PowerSeries.OnOpenDisc.hasseDeriv_rescaleAlgHom`, and
  `TauCeti.PowerSeries.OnOpenDisc.hasseDeriv_affineAlgHom` (and their `derivative` companions):
  compatibilities with coefficient maps, translation, rescaling, and affine coordinate changes.
* `TauCeti.PowerSeries.OnOpenDisc.derivative_analyticSubst`: the chain rule for analytic
  substitution on open discs.

## References

* P. Colmez, *Fonctions d'une variable p-adique*, Astérisque 330 (2010), §I.4.
* S. Bosch, U. Güntzer and R. Remmert, *Non-Archimedean Analysis*, Grundlehren 261, §5.1.
-/

public section

open Filter PowerSeries
open scoped Topology

namespace TauCeti.PowerSeries.OnOpenDisc

section HasseDeriv

variable {R : Type*} [NormedRing R] {R₀ : ℝ}

/-- The `k`th Hasse derivative as a left `R`-linear endomorphism of the open-disc series ring
`OnOpenDisc.subring R R₀`. Neither commutativity nor an ultrametric norm is required. -/
noncomputable def hasseDeriv (k : ℕ) :
    OnOpenDisc.subring R R₀ →ₗ[R] OnOpenDisc.subring R R₀ where
  toFun f := ⟨PowerSeries.hasseDeriv k (f : R⟦X⟧),
    OnOpenDisc.mem_subring.mpr ((OnOpenDisc.mem_subring.mp f.2).hasseDeriv k)⟩
  map_add' f g := Subtype.ext (map_add (PowerSeries.hasseDeriv k) (f : R⟦X⟧) g)
  map_smul' a f := Subtype.ext (map_smul (PowerSeries.hasseDeriv k) a (f : R⟦X⟧))

/-- `hasseDeriv` acts as `PowerSeries.hasseDeriv` on the underlying formal power series. -/
@[simp]
theorem coe_hasseDeriv (k : ℕ) (f : OnOpenDisc.subring R R₀) :
    (hasseDeriv k f : R⟦X⟧) = PowerSeries.hasseDeriv k (f : R⟦X⟧) := (rfl)

/-- The `n`th coefficient of `hasseDeriv k f` is `(n + k).choose k * coeff (n + k) f`. -/
theorem coeff_hasseDeriv (k : ℕ) (f : OnOpenDisc.subring R R₀) (n : ℕ) :
    coeff n (hasseDeriv k f : R⟦X⟧) = ((n + k).choose k : R) * coeff (n + k) (f : R⟦X⟧) := by
  rw [coe_hasseDeriv, PowerSeries.coeff_hasseDeriv]

/-- The `0`th Hasse derivative on an open disc is the identity. -/
@[simp]
theorem hasseDeriv_zero :
    hasseDeriv (R := R) (R₀ := R₀) 0 = LinearMap.id :=
  LinearMap.ext fun f ↦ Subtype.ext (by simp)

/-- On polynomials, `hasseDeriv` agrees with `Polynomial.hasseDeriv`. -/
@[simp]
theorem hasseDeriv_polynomialHom (k : ℕ) (p : Polynomial R) :
    hasseDeriv k (OnOpenDisc.polynomialHom (R₀ := R₀) p) =
      OnOpenDisc.polynomialHom (p.hasseDeriv k) :=
  Subtype.ext (by simp)

/-- Positive Hasse derivatives vanish on `1`. -/
theorem hasseDeriv_apply_one {k : ℕ} (hk : 0 < k) :
    hasseDeriv k (1 : OnOpenDisc.subring R R₀) = 0 :=
  Subtype.ext <| by simpa using PowerSeries.hasseDeriv_C (R := R) hk 1

/-- Positive Hasse derivatives vanish on scalar constants. -/
theorem hasseDeriv_algebraMap {S : Type*} [CommSemiring S] [Algebra S R] {k : ℕ} (hk : 0 < k)
    (s : S) :
    hasseDeriv k (algebraMap S (OnOpenDisc.subring R R₀) s) = 0 :=
  Subtype.ext <| by simp [PowerSeries.hasseDeriv_C hk]

/-- **Composition of Hasse derivatives on an open disc**:
`hasseDeriv k ∘ hasseDeriv l = (k + l).choose k • hasseDeriv (k + l)`. -/
theorem hasseDeriv_comp (k l : ℕ) :
    (hasseDeriv (R := R) (R₀ := R₀) k).comp (hasseDeriv l) =
      (k + l).choose k • hasseDeriv (k + l) :=
  LinearMap.ext fun f ↦ Subtype.ext <| by
    simpa using LinearMap.congr_fun (PowerSeries.hasseDeriv_comp (R := R) k l) (f : R⟦X⟧)

/-- **The Leibniz rule for Hasse derivatives on an open disc**, with factors in their original
order so that `R` need not be commutative. -/
theorem hasseDeriv_mul (k : ℕ) (f g : OnOpenDisc.subring R R₀) :
    hasseDeriv k (f * g) =
      ∑ ij ∈ Finset.antidiagonal k, hasseDeriv ij.1 f * hasseDeriv ij.2 g :=
  Subtype.ext (by simp [PowerSeries.hasseDeriv_mul])

/-- Bounded coefficient maps commute with Hasse derivatives on open discs. -/
@[simp]
theorem mapHom_hasseDeriv {S : Type*} [NormedRing S] (φ : R →+* S) {C : ℝ}
    (hφ : ∀ x, ‖φ x‖ ≤ C * ‖x‖) (k : ℕ) (f : OnOpenDisc.subring R R₀) :
    mapHom φ hφ (hasseDeriv k f) = hasseDeriv k (mapHom φ hφ f) :=
  Subtype.ext (by simp)

/-- Radius restriction commutes with Hasse derivatives on open discs. -/
@[simp]
theorem radiusHom_hasseDeriv {R₁ : ℝ} (h : R₁ ≤ R₀) (k : ℕ) (f : OnOpenDisc.subring R R₀) :
    radiusHom h (hasseDeriv k f) = hasseDeriv k (radiusHom h f) :=
  Subtype.ext (by simp)

end HasseDeriv

section UltrametricHasseDeriv

variable {R : Type*} [NormedRing R] [IsUltrametricDist R] {R₀ : ℝ}

attribute [local instance] radius_pos

/-- **The Cauchy estimate for Hasse derivatives on smaller closed discs**:
`‖restrict r (hasseDeriv k f)‖ ≤ (r : ℝ)⁻¹ ^ k * ‖restrict r f‖`. -/
theorem norm_restrict_hasseDeriv_le (r : Set.Ioo (0 : ℝ) R₀) (k : ℕ)
    (f : OnOpenDisc.subring R R₀) :
    ‖restrict r (hasseDeriv k f)‖ ≤ (r : ℝ)⁻¹ ^ k * ‖restrict r f‖ := by
  have hf : (f : R⟦X⟧).IsRestricted r := (mem_subring_iff_forall_isRestricted.mp f.2) r
  rw [norm_eq_gaussNorm, norm_eq_gaussNorm, coe_restrict, coe_restrict, coe_hasseDeriv]
  exact PowerSeries.gaussNorm_hasseDeriv_le (R := R) r.2.1 (hasGaussNorm_of_isRestricted hf) k

/-- Hasse derivatives on an open disc are uniformly continuous for the Gauss uniformity. -/
theorem uniformContinuous_hasseDeriv (k : ℕ) :
    UniformContinuous (hasseDeriv (R := R) (R₀ := R₀) k) := by
  refine uniformContinuous_iff.mpr fun r ↦
    uniformContinuous_of_continuousAt_zero
      ((restrict (R := R) r).toAddMonoidHom.comp (hasseDeriv k).toAddMonoidHom) ?_
  rw [ContinuousAt, map_zero]
  exact squeeze_zero_norm (norm_restrict_hasseDeriv_le r k) <| by
    simpa using (((uniformContinuous_restrict (R := R) r).continuous.tendsto 0).norm.const_mul
      ((r : ℝ)⁻¹ ^ k))

/-- Hasse derivatives on an open disc are continuous for the Gauss topology. -/
@[continuity]
theorem continuous_hasseDeriv (k : ℕ) : Continuous (hasseDeriv (R := R) (R₀ := R₀) k) :=
  (uniformContinuous_hasseDeriv k).continuous

end UltrametricHasseDeriv

section Derivative

variable {R : Type*} [NormedCommRing R] {R₀ S₀ : ℝ}

/-- The formal derivative `d/dX` as an `R`-derivation of the open-disc algebra
`OnOpenDisc.subring R R₀`. -/
noncomputable def derivative :
    Derivation R (OnOpenDisc.subring R R₀) (OnOpenDisc.subring R R₀) where
  toFun f := ⟨d⁄dX (f : R⟦X⟧),
    OnOpenDisc.mem_subring.mpr (OnOpenDisc.mem_subring.mp f.2).derivative⟩
  map_add' f g := Subtype.ext (map_add PowerSeries.derivative (f : R⟦X⟧) g)
  map_smul' a f := Subtype.ext (Derivation.map_smul PowerSeries.derivative a (f : R⟦X⟧))
  map_one_eq_zero' := Subtype.ext PowerSeries.derivative_one
  leibniz' f g := Subtype.ext (by simp [Derivation.leibniz, smul_eq_mul])

/-- `derivative` acts as `PowerSeries.derivative` on the underlying formal power series. -/
@[simp]
theorem coe_derivative (f : OnOpenDisc.subring R R₀) :
    (derivative f : R⟦X⟧) = d⁄dX (f : R⟦X⟧) := (rfl)

/-- Iterated `derivative` acts as iterated `PowerSeries.derivative` on the underlying series. -/
@[simp]
theorem coe_iterate_derivative (k : ℕ) (f : OnOpenDisc.subring R R₀) :
    ((derivative^[k] f : OnOpenDisc.subring R R₀) : R⟦X⟧) = d⁄dX^[k] (f : R⟦X⟧) := by
  induction k generalizing f with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply, ih, coe_derivative, Function.iterate_succ_apply]

/-- Coefficient formula for `derivative` on an open disc. -/
theorem coeff_derivative (f : OnOpenDisc.subring R R₀) (n : ℕ) :
    coeff n (derivative f : R⟦X⟧) = coeff (n + 1) (f : R⟦X⟧) * (n + 1) := by
  rw [coe_derivative, PowerSeries.coeff_derivative]

/-- The first Hasse derivative on an open disc is the ordinary derivative. -/
@[simp]
theorem hasseDeriv_one_apply (f : OnOpenDisc.subring R R₀) :
    hasseDeriv 1 f = derivative f :=
  Subtype.ext (PowerSeries.hasseDeriv_one_apply (f : R⟦X⟧))

/-- `k.factorial` times the `k`th Hasse derivative on an open disc is the `k`th iterated
derivative. -/
theorem factorial_smul_hasseDeriv (k : ℕ) (f : OnOpenDisc.subring R R₀) :
    k.factorial • hasseDeriv k f = derivative^[k] f := by
  apply Subtype.ext
  rw [← Subring.subtype_apply, map_nsmul, Subring.subtype_apply, coe_hasseDeriv,
    coe_iterate_derivative, PowerSeries.factorial_smul_hasseDeriv]

/-- On polynomials, `derivative` agrees with `Polynomial.derivative`. -/
@[simp]
theorem derivative_polynomialHom (p : Polynomial R) :
    derivative (OnOpenDisc.polynomialHom (R₀ := R₀) p) =
      OnOpenDisc.polynomialHom (Polynomial.derivative p) :=
  Subtype.ext (by simp [PowerSeries.derivative_coe])

/-- The derivative of the coordinate `X` on an open disc is `1`. -/
theorem derivative_X :
    derivative (OnOpenDisc.polynomialHom Polynomial.X : OnOpenDisc.subring R R₀) = 1 :=
  Subtype.ext (by simp)

/-- The derivative of a polynomial constant `C a` on an open disc is `0`. -/
theorem derivative_C (a : R) :
    derivative (OnOpenDisc.polynomialHom (Polynomial.C a) : OnOpenDisc.subring R R₀) = 0 :=
  Subtype.ext (by simp)

/-- Over `[HasUniqueDiv R]`, an open-disc series is determined by its derivative and constant
coefficient. -/
theorem derivative_ext [HasUniqueDiv R] {f g : OnOpenDisc.subring R R₀}
    (hD : derivative f = derivative g)
    (hc : constantCoeff (f : R⟦X⟧) = constantCoeff (g : R⟦X⟧)) : f = g :=
  Subtype.ext <| PowerSeries.derivative.ext (by simpa using congrArg Subtype.val hD) hc

/-- Over `[HasUniqueDiv R]`, an open-disc series has zero derivative if and only if it is a
scalar constant. -/
theorem derivative_eq_zero_iff [HasUniqueDiv R] {f : OnOpenDisc.subring R R₀} :
    derivative f = 0 ↔ f = algebraMap R _ (constantCoeff (f : R⟦X⟧)) :=
  ⟨fun h ↦ derivative_ext (by simp [h]) (by simp),
    fun h ↦ by rw [h]; exact Derivation.map_algebraMap derivative _⟩

/-- Bounded coefficient maps commute with `derivative` on open discs. -/
@[simp]
theorem mapHom_derivative {S : Type*} [NormedCommRing S] (φ : R →+* S) {C : ℝ}
    (hφ : ∀ x, ‖φ x‖ ≤ C * ‖x‖) (f : OnOpenDisc.subring R R₀) :
    mapHom φ hφ (derivative f) = derivative (mapHom φ hφ f) :=
  Subtype.ext (by simp)

/-- **Hasse derivatives under rescaling** on open discs:
`hasseDeriv k (rescaleAlgHom hu f) = u ^ k • rescaleAlgHom hu (hasseDeriv k f)`. -/
theorem hasseDeriv_rescaleAlgHom {u : R} (hu : ‖u‖ * S₀ ≤ R₀) (k : ℕ)
    (f : OnOpenDisc.subring R R₀) :
    hasseDeriv k (rescaleAlgHom hu f) = u ^ k • rescaleAlgHom hu (hasseDeriv k f) :=
  Subtype.ext (by simp [PowerSeries.hasseDeriv_rescale, Algebra.smul_def])

/-- **The chain rule for rescaling** on open discs:
`derivative (rescaleAlgHom hu f) = u • rescaleAlgHom hu (derivative f)`. -/
theorem derivative_rescaleAlgHom {u : R} (hu : ‖u‖ * S₀ ≤ R₀)
    (f : OnOpenDisc.subring R R₀) :
    derivative (rescaleAlgHom hu f) = u • rescaleAlgHom hu (derivative f) := by
  simpa using hasseDeriv_rescaleAlgHom hu 1 f

/-- Radius restriction commutes with `derivative` on open discs. -/
@[simp]
theorem radiusHom_derivative {R₁ : ℝ} (h : R₁ ≤ R₀) (f : OnOpenDisc.subring R R₀) :
    radiusHom h (derivative f) = derivative (radiusHom h f) :=
  Subtype.ext (by simp)

end Derivative

section ChainRule

variable {R : Type*} [NormedCommRing R] [IsUltrametricDist R] {R₀ S₀ : ℝ}

attribute [local instance] radius_pos

/-- **The Cauchy estimate for `derivative` on smaller closed discs**:
`‖restrict r (derivative f)‖ ≤ (r : ℝ)⁻¹ * ‖restrict r f‖`. -/
theorem norm_restrict_derivative_le (r : Set.Ioo (0 : ℝ) R₀) (f : OnOpenDisc.subring R R₀) :
    ‖restrict r (derivative f)‖ ≤ (r : ℝ)⁻¹ * ‖restrict r f‖ := by
  simpa only [← hasseDeriv_one_apply, pow_one] using norm_restrict_hasseDeriv_le r 1 f

/-- `derivative` is uniformly continuous for the open-disc Gauss uniformity. -/
theorem uniformContinuous_derivative :
    UniformContinuous (derivative (R := R) (R₀ := R₀)) := by
  have h : (derivative (R := R) (R₀ := R₀) : OnOpenDisc.subring R R₀ → _) = hasseDeriv 1 :=
    funext fun f ↦ (hasseDeriv_one_apply f).symm
  exact h ▸ uniformContinuous_hasseDeriv 1

/-- `derivative` is continuous for the open-disc Gauss topology. -/
@[continuity]
theorem continuous_derivative : Continuous (derivative (R := R) (R₀ := R₀)) :=
  uniformContinuous_derivative.continuous

variable [CompleteSpace R]

/-- **Hasse derivatives commute with Taylor translation** on an open disc. -/
theorem hasseDeriv_taylorHom {a : R} (ha : ‖a‖ < R₀) (k : ℕ) (f : OnOpenDisc.subring R R₀) :
    hasseDeriv k (taylorHom ha f) = taylorHom ha (hasseDeriv k f) := by
  apply Subtype.ext
  rw [coe_hasseDeriv, coe_taylorHom, coe_taylorHom, coe_hasseDeriv]
  exact (OnOpenDisc.mem_subring.mp f.2).hasseDeriv_taylor ha k

/-- **The derivative commutes with Taylor translation** on an open disc. -/
theorem derivative_taylorHom {a : R} (ha : ‖a‖ < R₀) (f : OnOpenDisc.subring R R₀) :
    derivative (taylorHom ha f) = taylorHom ha (derivative f) := by
  simpa only [← hasseDeriv_one_apply] using hasseDeriv_taylorHom ha 1 f

/-- **Hasse derivatives under affine coordinate changes** on open discs:
`hasseDeriv k (affineAlgHom ha hu f) = u ^ k • affineAlgHom ha hu (hasseDeriv k f)`. -/
theorem hasseDeriv_affineAlgHom {a u : R} (ha : ‖a‖ < R₀) (hu : ‖u‖ * S₀ ≤ R₀) (k : ℕ)
    (f : OnOpenDisc.subring R R₀) :
    hasseDeriv k (affineAlgHom ha hu f) = u ^ k • affineAlgHom ha hu (hasseDeriv k f) := by
  rw [affineAlgHom_apply, hasseDeriv_rescaleAlgHom, hasseDeriv_taylorHom, ← affineAlgHom_apply]

/-- **The derivative under affine coordinate changes** on open discs:
`derivative (affineAlgHom ha hu f) = u • affineAlgHom ha hu (derivative f)`. -/
theorem derivative_affineAlgHom {a u : R} (ha : ‖a‖ < R₀) (hu : ‖u‖ * S₀ ≤ R₀)
    (f : OnOpenDisc.subring R R₀) :
    derivative (affineAlgHom ha hu f) = u • affineAlgHom ha hu (derivative f) := by
  simpa using hasseDeriv_affineAlgHom ha hu 1 f

/-- **The chain rule for analytic substitution on open discs.** If `g` lies on the open disc of
radius `S₀ > 0` with `‖restrict s g‖ < R₀` on every smaller closed disc, then
`derivative (analyticSubst g hg f) = analyticSubst g hg (derivative f) * derivative g`. Neither
`NormOneClass R` nor nilpotence of `constantCoeff g` is needed. -/
theorem derivative_analyticSubst [Fact (0 < S₀)] (g : OnOpenDisc.subring R S₀)
    (hg : ∀ s : Set.Ioo (0 : ℝ) S₀, ‖restrict s g‖ < R₀)
    (f : OnOpenDisc.subring R R₀) :
    derivative (analyticSubst g hg f) =
      analyticSubst g hg (derivative f) * derivative g := by
  refine congrFun (Continuous.ext_on denseRange_polynomialHom
    (continuous_derivative.comp (continuous_analyticSubst g hg))
    (((continuous_analyticSubst g hg).comp continuous_derivative).mul continuous_const) ?_) f
  rintro _ ⟨p, rfl⟩
  simp only [Pi.mul_apply, Function.comp_apply, analyticSubst_polynomialHom,
    derivative_polynomialHom, Derivation.map_aeval, smul_eq_mul]

end ChainRule

end TauCeti.PowerSeries.OnOpenDisc
