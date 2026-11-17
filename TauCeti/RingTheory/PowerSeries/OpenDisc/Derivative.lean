/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.PowerSeries.HasseDeriv.GaussNorm
public import TauCeti.RingTheory.PowerSeries.OpenDisc.Map
public import TauCeti.RingTheory.PowerSeries.OpenDisc.Taylor
import TauCeti.RingTheory.PowerSeries.Derivative

/-!
# Hasse derivatives and the ordinary derivative on open discs

Over any normed ring `R`, the `k`th Hasse derivative `D⁽ᵏ⁾` preserves the open-disc condition:
any polynomial growth of the binomial coefficients is absorbed on a slightly larger radius strictly
inside the disc (`PowerSeries.OnOpenDisc.hasseDeriv`). Bundling this action gives the additive
endomorphism `TauCeti.PowerSeries.OnOpenDisc.hasseDeriv k` of `OnOpenDisc.subring R R₀`, which is
linear over every commutative base algebra, satisfies the Hasse composition law and the ordered
Leibniz rule (even for noncommutative coefficients), and commutes with polynomial inclusion,
radius restriction, and bounded coefficient maps.

When `R` is commutative, the first Hasse derivative is the ordinary formal derivative, which
bundles into an `R`-derivation `TauCeti.PowerSeries.OnOpenDisc.derivative` satisfying
`k! • hasseDeriv k f = derivative^[k] f` and the rescaling chain rule
`derivative (rescaleHom u hu f) = u • rescaleHom u hu (derivative f)`.

Over an ultrametric coefficient ring, restricting to a smaller closed disc of radius `0 < r < R₀`
yields the Cauchy estimates `‖restrict r (hasseDeriv k f)‖ ≤ r⁻ᵏ ‖restrict r f‖` and
`‖restrict r (derivative f)‖ ≤ r⁻¹ ‖restrict r f‖`, making Hasse derivatives and the ordinary
derivative uniformly continuous for the open-disc Gauss uniformity and commuting with Taylor
translation.

## Main definitions

* `TauCeti.PowerSeries.OnOpenDisc.hasseDeriv`: the `k`th Hasse derivative as an additive
  endomorphism of `OnOpenDisc.subring R R₀`.
* `TauCeti.PowerSeries.OnOpenDisc.derivative`: the ordinary derivative `d⁄dX` as an `R`-derivation
  of `OnOpenDisc.subring R R₀`.

## Main results

* `TauCeti.PowerSeries.OnOpenDisc.hasseDeriv_comp` and
  `TauCeti.PowerSeries.OnOpenDisc.hasseDeriv_mul`: composition identity and ordered Leibniz rule on
  open discs.
* `TauCeti.PowerSeries.OnOpenDisc.factorial_smul_hasseDeriv`: `k! • D⁽ᵏ⁾ f = (d/dX)^[k] f`.
* `TauCeti.PowerSeries.OnOpenDisc.derivative_rescaleHom`,
  `TauCeti.PowerSeries.OnOpenDisc.hasseDeriv_taylorHom`, and
  `TauCeti.PowerSeries.OnOpenDisc.derivative_taylorHom`: compatibility with rescaling and Taylor
  translation.
* `TauCeti.PowerSeries.OnOpenDisc.norm_restrict_hasseDeriv_le`,
  `TauCeti.PowerSeries.OnOpenDisc.norm_restrict_derivative_le`,
  `TauCeti.PowerSeries.OnOpenDisc.uniformContinuous_hasseDeriv`, and
  `TauCeti.PowerSeries.OnOpenDisc.uniformContinuous_derivative`: closed-disc Cauchy estimates and
  uniform continuity.

## References

* P. Colmez, *Fonctions d'une variable p-adique*, Astérisque 330 (2010), §I.4.
* S. Bosch, U. Güntzer and R. Remmert, *Non-Archimedean Analysis*, Grundlehren 261, §5.1.
-/

public section

open Filter PowerSeries
open scoped Topology

namespace TauCeti.PowerSeries.OnOpenDisc

section HasseDeriv

variable {R : Type*} [NormedRing R] {R₀ S₀ : ℝ}

/-- The `k`th Hasse derivative as an additive endomorphism of the open-disc subring, over a
possibly noncommutative normed ring without an ultrametric assumption. -/
noncomputable def hasseDeriv (k : ℕ) :
    OnOpenDisc.subring R R₀ →+ OnOpenDisc.subring R R₀ :=
  AddMonoidHom.mk' (fun f ↦ ⟨PowerSeries.hasseDeriv k (f : R⟦X⟧),
      OnOpenDisc.mem_subring.mpr ((OnOpenDisc.mem_subring.mp f.2).hasseDeriv k)⟩)
    fun f g ↦ Subtype.ext (map_add (PowerSeries.hasseDeriv k) (f : R⟦X⟧) g)

/-- The underlying formal power series of `hasseDeriv k f` is `PowerSeries.hasseDeriv k f`. -/
@[simp]
theorem coe_hasseDeriv (k : ℕ) (f : OnOpenDisc.subring R R₀) :
    (hasseDeriv k f : R⟦X⟧) = PowerSeries.hasseDeriv k (f : R⟦X⟧) :=
  (rfl)

/-- The `n`th coefficient of `hasseDeriv k f` is `(n + k).choose k` times the `(n + k)`th
coefficient of `f`. -/
theorem coeff_hasseDeriv (k : ℕ) (f : OnOpenDisc.subring R R₀) (n : ℕ) :
    coeff n (hasseDeriv k f : R⟦X⟧) = ((n + k).choose k : R) * coeff (n + k) (f : R⟦X⟧) :=
  PowerSeries.coeff_hasseDeriv k (f : R⟦X⟧) n

/-- The `0`th Hasse derivative on an open disc is the identity. -/
@[simp]
theorem hasseDeriv_zero (f : OnOpenDisc.subring R R₀) :
    hasseDeriv 0 f = f :=
  Subtype.ext (by simp)

/-- Hasse derivatives on an open disc commute with scalar multiplication from any base algebra. -/
@[simp]
theorem hasseDeriv_smul {S : Type*} [CommSemiring S] [Algebra S R] (k : ℕ) (s : S)
    (f : OnOpenDisc.subring R R₀) :
    hasseDeriv k (s • f) = s • hasseDeriv k f :=
  Subtype.ext <| by
    rw [coe_hasseDeriv, OnOpenDisc.coe_smul, OnOpenDisc.coe_smul, ← algebraMap_smul R,
      (PowerSeries.hasseDeriv k).map_smul, algebraMap_smul, coe_hasseDeriv]

/-- On polynomials, `hasseDeriv` agrees with `Polynomial.hasseDeriv`. -/
@[simp]
theorem hasseDeriv_polynomialHom (k : ℕ) (p : Polynomial R) :
    hasseDeriv k (OnOpenDisc.polynomialHom p : OnOpenDisc.subring R R₀) =
      OnOpenDisc.polynomialHom (p.hasseDeriv k) :=
  Subtype.ext (by simp)

/-- Positive Hasse derivatives vanish on constant series. -/
theorem hasseDeriv_C {k : ℕ} (hk : 0 < k) (a : R) :
    hasseDeriv k (OnOpenDisc.polynomialHom (Polynomial.C a) : OnOpenDisc.subring R R₀) = 0 :=
  Subtype.ext <| by
    rw [coe_hasseDeriv, OnOpenDisc.coe_polynomialHom, Polynomial.coe_C,
      PowerSeries.hasseDeriv_C hk, ZeroMemClass.coe_zero]

/-- **Composition of Hasse derivatives** on an open disc:
`D⁽ᵏ⁾ ∘ D⁽ˡ⁾ = (k + l).choose k • D⁽ᵏ⁺ˡ⁾`. -/
theorem hasseDeriv_comp (k l : ℕ) :
    (hasseDeriv (R := R) (R₀ := R₀) k).comp (hasseDeriv l) =
      (k + l).choose k • hasseDeriv (k + l) := by
  ext f : 1
  apply Subtype.ext
  simpa using LinearMap.congr_fun (PowerSeries.hasseDeriv_comp (R := R) k l) (f : R⟦X⟧)

/-- Applying `D⁽ˡ⁾` and then `D⁽ᵏ⁾` gives `(k + l).choose k • D⁽ᵏ⁺ˡ⁾`. -/
theorem hasseDeriv_hasseDeriv (k l : ℕ) (f : OnOpenDisc.subring R R₀) :
    hasseDeriv k (hasseDeriv l f) = (k + l).choose k • hasseDeriv (k + l) f :=
  DFunLike.congr_fun (hasseDeriv_comp k l) f

/-- **The Leibniz rule** for Hasse derivatives on an open disc, preserving factor order over
possibly noncommutative coefficient rings. -/
theorem hasseDeriv_mul (k : ℕ) (f g : OnOpenDisc.subring R R₀) :
    hasseDeriv k (f * g) =
      ∑ ij ∈ Finset.antidiagonal k, hasseDeriv ij.1 f * hasseDeriv ij.2 g :=
  Subtype.ext <| by
    simpa using PowerSeries.hasseDeriv_mul k (f : R⟦X⟧) (g : R⟦X⟧)

/-- Hasse derivatives commute with radius restriction between open discs. -/
@[simp]
theorem radiusHom_hasseDeriv (h : S₀ ≤ R₀) (k : ℕ) (f : OnOpenDisc.subring R R₀) :
    radiusHom h (hasseDeriv k f) = hasseDeriv k (radiusHom h f) :=
  Subtype.ext (by simp)

/-- Hasse derivatives commute with bounded coefficient maps. -/
@[simp]
theorem mapHom_hasseDeriv {S : Type*} [NormedRing S] (φ : R →+* S) {C : ℝ}
    (hφ : ∀ x, ‖φ x‖ ≤ C * ‖x‖) (k : ℕ) (f : OnOpenDisc.subring R R₀) :
    mapHom φ hφ (hasseDeriv k f) = hasseDeriv k (mapHom φ hφ f) :=
  Subtype.ext (by simp)

end HasseDeriv

section Derivative

variable {R : Type*} [NormedCommRing R] {R₀ S₀ : ℝ}

/-- The ordinary formal derivative `d⁄dX`, bundled as an `R`-derivation of the open-disc algebra.
No ultrametric hypothesis is needed. -/
noncomputable def derivative :
    Derivation R (OnOpenDisc.subring R R₀) (OnOpenDisc.subring R R₀) where
  toFun f := ⟨d⁄dX (f : R⟦X⟧),
    OnOpenDisc.mem_subring.mpr (OnOpenDisc.mem_subring.mp f.2).derivative⟩
  map_add' f g := Subtype.ext (map_add (PowerSeries.derivative (R := R)) (f : R⟦X⟧) g)
  map_smul' a f := Subtype.ext (by simp)
  map_one_eq_zero' := Subtype.ext (derivative_one (R := R))
  leibniz' f g := Subtype.ext <| by
    simp [Derivation.leibniz (PowerSeries.derivative (R := R)) (f : R⟦X⟧) (g : R⟦X⟧), smul_eq_mul]

/-- The underlying formal power series of `derivative f` is `d⁄dX f`. -/
@[simp]
theorem coe_derivative (f : OnOpenDisc.subring R R₀) :
    (derivative f : R⟦X⟧) = d⁄dX (f : R⟦X⟧) :=
  (rfl)

/-- The `n`th coefficient of `derivative f` is `coeff (n + 1) f * (n + 1)`. -/
theorem coeff_derivative (f : OnOpenDisc.subring R R₀) (n : ℕ) :
    coeff n (derivative f : R⟦X⟧) = coeff (n + 1) (f : R⟦X⟧) * (n + 1 : R) :=
  PowerSeries.coeff_derivative (f : R⟦X⟧) n

/-- Over a commutative ring, the first Hasse derivative is the ordinary derivative. -/
@[simp]
theorem hasseDeriv_one (f : OnOpenDisc.subring R R₀) :
    hasseDeriv 1 f = derivative f :=
  Subtype.ext (PowerSeries.hasseDeriv_one_apply (f : R⟦X⟧))

/-- `k!` times the `k`th Hasse derivative is the `k`th iterated derivative on an open disc. -/
theorem factorial_smul_hasseDeriv (k : ℕ) (f : OnOpenDisc.subring R R₀) :
    Nat.factorial k • hasseDeriv k f = (derivative (R := R) (R₀ := R₀))^[k] f := by
  apply Subtype.ext
  have hiter (m : ℕ) (g : OnOpenDisc.subring R R₀) :
      ((derivative (R := R) (R₀ := R₀))^[m] g : R⟦X⟧) = (d⁄dX)^[m] (g : R⟦X⟧) := by
    induction m generalizing g with
    | zero => rfl
    | succ m ih => simp [Function.iterate_succ_apply', ih]
  simpa [hiter] using PowerSeries.factorial_smul_hasseDeriv k (f : R⟦X⟧)

/-- Constant series have zero derivative. -/
theorem derivative_C (a : R) :
    derivative (OnOpenDisc.polynomialHom (Polynomial.C a) : OnOpenDisc.subring R R₀) = 0 :=
  Subtype.ext (by simp)

/-- The derivative of `X` is `1`. -/
theorem derivative_X :
    derivative (OnOpenDisc.polynomialHom Polynomial.X : OnOpenDisc.subring R R₀) = 1 :=
  Subtype.ext (by simp)

/-- On polynomials, `derivative` agrees with `Polynomial.derivative`. -/
@[simp]
theorem derivative_polynomialHom (p : Polynomial R) :
    derivative (OnOpenDisc.polynomialHom p : OnOpenDisc.subring R R₀) =
      OnOpenDisc.polynomialHom p.derivative :=
  Subtype.ext (by simp [derivative_coe])

/-- The ordinary derivative commutes with radius restriction between open discs. -/
@[simp]
theorem radiusHom_derivative (h : S₀ ≤ R₀) (f : OnOpenDisc.subring R R₀) :
    radiusHom h (derivative f) = derivative (radiusHom h f) :=
  Subtype.ext (by simp)

/-- The ordinary derivative commutes with bounded coefficient maps. -/
@[simp]
theorem mapHom_derivative {S : Type*} [NormedCommRing S] (φ : R →+* S) {C : ℝ}
    (hφ : ∀ x, ‖φ x‖ ≤ C * ‖x‖) (f : OnOpenDisc.subring R R₀) :
    mapHom φ hφ (derivative f) = derivative (mapHom φ hφ f) :=
  Subtype.ext (by simp)

/-- **Hasse derivatives of a rescaled series** on open discs:
`D⁽ᵏ⁾ (f(u X)) = uᵏ · (D⁽ᵏ⁾ f)(u X)`. -/
theorem hasseDeriv_rescaleHom (u : R) (hu : ‖u‖ * S₀ ≤ R₀) (k : ℕ)
    (f : OnOpenDisc.subring R R₀) :
    hasseDeriv k (rescaleHom u hu f) = u ^ k • rescaleHom u hu (hasseDeriv k f) :=
  Subtype.ext <| PowerSeries.ext fun n ↦ by
    simp only [coe_hasseDeriv, coe_rescaleHom, OnOpenDisc.coe_smul, coeff_smul, smul_eq_mul,
      PowerSeries.coeff_hasseDeriv, coeff_rescale, pow_add]
    ring

/-- **The rescaling chain rule** on open discs: `(f(u X))' = u · f'(u X)`. -/
theorem derivative_rescaleHom (u : R) (hu : ‖u‖ * S₀ ≤ R₀) (f : OnOpenDisc.subring R R₀) :
    derivative (rescaleHom u hu f) = u • rescaleHom u hu (derivative f) :=
  Subtype.ext <| by
    simp [PowerSeries.derivative_rescale, smul_eq_C_mul]

end Derivative

section Ultrametric

variable {R : Type*} [NormedRing R] [IsUltrametricDist R] {R₀ : ℝ}

attribute [local instance] radius_pos

/-- **The Cauchy estimate for Hasse derivatives** on smaller closed discs:
`‖restrict r (hasseDeriv k f)‖ ≤ r⁻ᵏ ‖restrict r f‖`. -/
theorem norm_restrict_hasseDeriv_le (r : Set.Ioo (0 : ℝ) R₀) (k : ℕ)
    (f : OnOpenDisc.subring R R₀) :
    ‖restrict r (hasseDeriv k f)‖ ≤ (r : ℝ)⁻¹ ^ k * ‖restrict r f‖ := by
  have hf := TauCeti.PowerSeries.hasGaussNorm_of_isRestricted (restrict r f).2
  rw [coe_restrict] at hf
  rw [TauCeti.PowerSeries.norm_eq_gaussNorm, TauCeti.PowerSeries.norm_eq_gaussNorm,
    coe_restrict, coe_restrict, coe_hasseDeriv]
  exact PowerSeries.gaussNorm_hasseDeriv_le r.2.1 hf k

/-- Hasse derivatives are uniformly continuous for the open-disc Gauss uniformity. -/
theorem uniformContinuous_hasseDeriv (k : ℕ) :
    UniformContinuous (hasseDeriv (R := R) (R₀ := R₀) k) := by
  refine uniformContinuous_of_continuousAt_zero (hasseDeriv k) ?_
  rw [ContinuousAt, map_zero, tendsto_iff]
  intro r
  rw [map_zero]
  refine squeeze_zero_norm (norm_restrict_hasseDeriv_le r k) ?_
  simpa only [map_zero, norm_zero, mul_zero] using
    (((uniformContinuous_restrict (R := R) r).continuous.tendsto 0).norm.const_mul ((r : ℝ)⁻¹ ^ k))

/-- Hasse derivatives are continuous for the open-disc Gauss topology. -/
@[continuity]
theorem continuous_hasseDeriv (k : ℕ) :
    Continuous (hasseDeriv (R := R) (R₀ := R₀) k) :=
  (uniformContinuous_hasseDeriv k).continuous

end Ultrametric

section UltrametricComm

variable {R : Type*} [NormedCommRing R] [IsUltrametricDist R] {R₀ : ℝ}

attribute [local instance] radius_pos

/-- **The Cauchy estimate for the ordinary derivative** on smaller closed discs:
`‖restrict r (derivative f)‖ ≤ r⁻¹ ‖restrict r f‖`. -/
theorem norm_restrict_derivative_le (r : Set.Ioo (0 : ℝ) R₀) (f : OnOpenDisc.subring R R₀) :
    ‖restrict r (derivative f)‖ ≤ (r : ℝ)⁻¹ * ‖restrict r f‖ := by
  simpa [← hasseDeriv_one] using norm_restrict_hasseDeriv_le r 1 f

/-- The ordinary derivative is uniformly continuous for the open-disc Gauss uniformity. -/
theorem uniformContinuous_derivative :
    UniformContinuous (derivative (R := R) (R₀ := R₀)) := by
  have heq : (derivative (R := R) (R₀ := R₀) :
      OnOpenDisc.subring R R₀ → OnOpenDisc.subring R R₀) = hasseDeriv 1 :=
    funext fun f ↦ (hasseDeriv_one f).symm
  rw [heq]
  exact uniformContinuous_hasseDeriv 1

/-- The ordinary derivative is continuous for the open-disc Gauss topology. -/
@[continuity]
theorem continuous_derivative :
    Continuous (derivative (R := R) (R₀ := R₀)) :=
  uniformContinuous_derivative.continuous

variable [CompleteSpace R] {a : R}

/-- Hasse derivatives commute with Taylor translation on an open disc. -/
@[simp]
theorem hasseDeriv_taylorHom (ha : ‖a‖ < R₀) (k : ℕ) (f : OnOpenDisc.subring R R₀) :
    hasseDeriv k (taylorHom ha f) = taylorHom ha (hasseDeriv k f) :=
  Subtype.ext (by simp [(OnOpenDisc.mem_subring.mp f.2).hasseDeriv_taylor ha k])

/-- The ordinary derivative commutes with Taylor translation on an open disc. -/
@[simp]
theorem derivative_taylorHom (ha : ‖a‖ < R₀) (f : OnOpenDisc.subring R R₀) :
    derivative (taylorHom ha f) = taylorHom ha (derivative f) := by
  rw [← hasseDeriv_one, ← hasseDeriv_one, hasseDeriv_taylorHom]

end UltrametricComm

end TauCeti.PowerSeries.OnOpenDisc
