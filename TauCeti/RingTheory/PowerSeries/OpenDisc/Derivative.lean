/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.PowerSeries.OpenDisc.Map
import TauCeti.RingTheory.PowerSeries.Derivative

/-!
# Hasse derivatives and formal differentiation on open discs

Over any normed ring `R`, the Hasse derivatives `PowerSeries.hasseDeriv k` preserve series on the
open disc of radius `R₀`: the polynomial growth of binomial coefficients is absorbed on every
strictly smaller radius (`PowerSeries.OnOpenDisc.hasseDeriv`). They assemble into `R`-linear
endomorphisms `TauCeti.PowerSeries.OnOpenDisc.hasseDeriv k` satisfying composition, commutativity,
and the noncommutative Leibniz rule, and commuting with bounded coefficient maps. Over an
ultrametric normed ring, restricting to a smaller closed disc of radius `r` bounds `hasseDeriv k`
by `r⁻ᵏ`, making each Hasse derivative uniformly continuous for the open-disc Gauss uniformity.

When `R` is commutative, formal differentiation `d⁄dX` is an `R`-derivation
`TauCeti.PowerSeries.OnOpenDisc.derivative` of `OnOpenDisc.subring R R₀`, equal to the first Hasse
derivative and satisfying `k! • hasseDeriv k f = derivative^[k] f`. Over a complete ultrametric
normed commutative ring, differentiation commutes with Taylor translation and satisfies the chain
rules for rescaling, affine changes of coordinates, and general analytic substitution
(`TauCeti.PowerSeries.OnOpenDisc.derivative_analyticSubst`).

## Main definitions

* `TauCeti.PowerSeries.OnOpenDisc.hasseDeriv`: the `k`-th Hasse derivative as an `R`-linear map on
  `OnOpenDisc.subring R R₀`.
* `TauCeti.PowerSeries.OnOpenDisc.derivative`: formal differentiation as an `R`-derivation of
  `OnOpenDisc.subring R R₀`.

## Main results

* `TauCeti.PowerSeries.OnOpenDisc.hasseDeriv_comp`,
  `TauCeti.PowerSeries.OnOpenDisc.hasseDeriv_comm`, and
  `TauCeti.PowerSeries.OnOpenDisc.hasseDeriv_mul`: composition, commutativity, and Leibniz rule for
  Hasse derivatives on an open disc.
* `TauCeti.PowerSeries.OnOpenDisc.norm_restrict_hasseDeriv_le`,
  `TauCeti.PowerSeries.OnOpenDisc.uniformContinuous_hasseDeriv`,
  `TauCeti.PowerSeries.OnOpenDisc.norm_restrict_derivative_le`, and
  `TauCeti.PowerSeries.OnOpenDisc.uniformContinuous_derivative`: closed-disc Gauss-norm bounds and
  uniform continuity.
* `TauCeti.PowerSeries.OnOpenDisc.hasseDeriv_taylorHom` and
  `TauCeti.PowerSeries.OnOpenDisc.derivative_taylorHom`: Hasse derivatives and formal
  differentiation commute with Taylor translation.
* `TauCeti.PowerSeries.OnOpenDisc.derivative_rescaleHom`,
  `TauCeti.PowerSeries.OnOpenDisc.derivative_affineHom`, and
  `TauCeti.PowerSeries.OnOpenDisc.derivative_analyticSubst`: the chain rules for rescaling, affine
  coordinate changes, and analytic substitution on open discs.

## References

* P. Colmez, *Fonctions d'une variable p-adique*, Astérisque 330 (2010), §I.4.
* S. Bosch, U. Güntzer and R. Remmert, *Non-Archimedean Analysis*, Grundlehren 261, §5.1.
-/

public section

open Filter PowerSeries
open scoped Topology

namespace TauCeti.PowerSeries.OnOpenDisc

section NormedRing

variable {R : Type*} [NormedRing R] {R₀ : ℝ}

/-- The `k`-th Hasse derivative as an `R`-linear endomorphism of series on the open disc of radius
`R₀`. Neither commutativity nor ultrametricity of `R` is required. -/
noncomputable def hasseDeriv (k : ℕ) :
    OnOpenDisc.subring R R₀ →ₗ[R] OnOpenDisc.subring R R₀ where
  toFun f := ⟨PowerSeries.hasseDeriv k (f : R⟦X⟧),
    OnOpenDisc.mem_subring.mpr ((OnOpenDisc.mem_subring.mp f.2).hasseDeriv k)⟩
  map_add' f g := Subtype.ext (map_add (PowerSeries.hasseDeriv k) (f : R⟦X⟧) g)
  map_smul' a f := Subtype.ext <| by
    simp only [RingHom.id_apply, coe_smul_subring, map_smul]

/-- `hasseDeriv k` acts as `PowerSeries.hasseDeriv k` on the underlying formal power series. -/
@[simp]
theorem coe_hasseDeriv (k : ℕ) (f : OnOpenDisc.subring R R₀) :
    (hasseDeriv k f : R⟦X⟧) = PowerSeries.hasseDeriv k (f : R⟦X⟧) :=
  (rfl)

/-- Coefficient formula for the `k`-th Hasse derivative on an open disc. -/
theorem coeff_hasseDeriv (k : ℕ) (f : OnOpenDisc.subring R R₀) (n : ℕ) :
    coeff n (hasseDeriv k f : R⟦X⟧) = ((n + k).choose k : R) * coeff (n + k) (f : R⟦X⟧) := by
  rw [coe_hasseDeriv, PowerSeries.coeff_hasseDeriv]

/-- The `0`-th Hasse derivative on an open disc is the identity. -/
@[simp]
theorem hasseDeriv_zero :
    hasseDeriv (R := R) (R₀ := R₀) 0 = LinearMap.id :=
  LinearMap.ext fun _ ↦ Subtype.ext (by simp)

/-- On polynomials, the open-disc Hasse derivative agrees with `Polynomial.hasseDeriv`. -/
@[simp]
theorem hasseDeriv_polynomialHom (k : ℕ) (p : Polynomial R) :
    hasseDeriv (R₀ := R₀) k (OnOpenDisc.polynomialHom p) =
      OnOpenDisc.polynomialHom (p.hasseDeriv k) :=
  Subtype.ext (by simp)

/-- Positive Hasse derivatives vanish on constant open-disc series. -/
theorem hasseDeriv_C {k : ℕ} (hk : 0 < k) (a : R) :
    hasseDeriv (R₀ := R₀) k (OnOpenDisc.polynomialHom (Polynomial.C a)) = 0 :=
  Subtype.ext <| by
    rw [coe_hasseDeriv, OnOpenDisc.coe_polynomialHom, Polynomial.coe_C,
      PowerSeries.hasseDeriv_C hk, ZeroMemClass.coe_zero]

/-- Positive Hasse derivatives vanish on `1`. -/
theorem hasseDeriv_one {k : ℕ} (hk : 0 < k) :
    hasseDeriv (R₀ := R₀) k (1 : OnOpenDisc.subring R R₀) = 0 := by
  simpa using hasseDeriv_C (R₀ := R₀) hk (1 : R)

/-- Hasse derivatives commute with bounded coefficient maps on open discs. -/
theorem mapHom_hasseDeriv {S : Type*} [NormedRing S] (φ : R →+* S) {C : ℝ}
    (hφ : ∀ x, ‖φ x‖ ≤ C * ‖x‖) (k : ℕ) (f : OnOpenDisc.subring R R₀) :
    mapHom φ hφ (hasseDeriv k f) = hasseDeriv k (mapHom φ hφ f) :=
  Subtype.ext (by simp)

/-- Composition law `D⁽ᵏ⁾ ∘ D⁽ˡ⁾ = (k + l).choose k • D⁽ᵏ⁺ˡ⁾` on an open disc. -/
theorem hasseDeriv_comp (k l : ℕ) :
    (hasseDeriv (R := R) (R₀ := R₀) k).comp (hasseDeriv l) =
      (k + l).choose k • hasseDeriv (k + l) :=
  LinearMap.ext fun f ↦ Subtype.ext <| by
    simpa [coe_smul_subring] using
      LinearMap.congr_fun (PowerSeries.hasseDeriv_comp (R := R) k l) (f : R⟦X⟧)

/-- Hasse derivatives of any two orders commute on open-disc series. -/
theorem hasseDeriv_comm (k l : ℕ) (f : OnOpenDisc.subring R R₀) :
    hasseDeriv k (hasseDeriv l f) = hasseDeriv l (hasseDeriv k f) := by
  have hk := LinearMap.congr_fun (hasseDeriv_comp (R := R) (R₀ := R₀) k l) f
  have hl := LinearMap.congr_fun (hasseDeriv_comp (R := R) (R₀ := R₀) l k) f
  rw [LinearMap.comp_apply] at hk hl
  rw [hk, hl, add_comm l k, Nat.choose_symm_add]

/-- The Leibniz rule for Hasse derivatives on an open disc, over a possibly noncommutative normed
ring. -/
theorem hasseDeriv_mul (k : ℕ) (f g : OnOpenDisc.subring R R₀) :
    hasseDeriv k (f * g) =
      ∑ ij ∈ Finset.antidiagonal k, hasseDeriv ij.1 f * hasseDeriv ij.2 g :=
  Subtype.ext (by simp [PowerSeries.hasseDeriv_mul])

end NormedRing

section UltrametricHasseDeriv

variable {R : Type*} [NormedRing R] [IsUltrametricDist R] {R₀ : ℝ}

attribute [local instance] radius_pos

/-- On each smaller positive closed disc of radius `r`, the `k`-th Hasse derivative has Gauss norm
at most `r⁻ᵏ` times that of the input series. -/
theorem norm_restrict_hasseDeriv_le (k : ℕ) (r : Set.Ioo (0 : ℝ) R₀)
    (f : OnOpenDisc.subring R R₀) :
    ‖restrict r (hasseDeriv k f)‖ ≤ (r : ℝ)⁻¹ ^ k * ‖restrict r f‖ := by
  have hf := hasGaussNorm_of_isRestricted (restrict r f).2
  rw [coe_restrict] at hf
  rw [norm_eq_gaussNorm, norm_eq_gaussNorm, coe_restrict, coe_restrict, coe_hasseDeriv]
  exact gaussNorm_hasseDeriv_le r.2.1 hf k

/-- Every Hasse derivative is uniformly continuous for the open-disc Gauss uniformity. -/
theorem uniformContinuous_hasseDeriv (k : ℕ) :
    UniformContinuous (hasseDeriv (R := R) (R₀ := R₀) k) :=
  uniformContinuous_of_norm_restrict_le _ fun r ↦
    ⟨r, (r : ℝ)⁻¹ ^ k, norm_restrict_hasseDeriv_le k r⟩

/-- Every Hasse derivative is continuous for the open-disc Gauss topology. -/
@[continuity]
theorem continuous_hasseDeriv (k : ℕ) :
    Continuous (hasseDeriv (R := R) (R₀ := R₀) k) :=
  (uniformContinuous_hasseDeriv k).continuous

end UltrametricHasseDeriv

section NormedCommRing

variable {R : Type*} [NormedCommRing R] {R₀ : ℝ}

/-- Formal differentiation `d⁄dX` as an `R`-derivation of the open-disc algebra. -/
noncomputable def derivative :
    Derivation R (OnOpenDisc.subring R R₀) (OnOpenDisc.subring R R₀) where
  toFun f := ⟨d⁄dX (f : R⟦X⟧),
    OnOpenDisc.mem_subring.mpr (OnOpenDisc.mem_subring.mp f.2).derivative⟩
  map_add' f g := Subtype.ext (map_add (d⁄dX) (f : R⟦X⟧) g)
  map_smul' a f := Subtype.ext <| by
    simp only [RingHom.id_apply, coe_smul_subring, Derivation.map_smul]
  map_one_eq_zero' := Subtype.ext (Derivation.map_one_eq_zero (d⁄dX))
  leibniz' f g := Subtype.ext <| by
    simpa only [LinearMap.coe_mk, AddHom.coe_mk, Subring.coe_mul, Subring.coe_add, smul_eq_mul]
      using (d⁄dX).leibniz (f : R⟦X⟧) (g : R⟦X⟧)

/-- `derivative` acts as `PowerSeries.derivative` on the underlying formal power series. -/
@[simp]
theorem coe_derivative (f : OnOpenDisc.subring R R₀) :
    (derivative f : R⟦X⟧) = d⁄dX (f : R⟦X⟧) :=
  (rfl)

/-- Coefficient formula for formal differentiation on an open disc. -/
theorem coeff_derivative (f : OnOpenDisc.subring R R₀) (n : ℕ) :
    coeff n (derivative f : R⟦X⟧) = coeff (n + 1) (f : R⟦X⟧) * (n + 1) := by
  rw [coe_derivative, PowerSeries.coeff_derivative]

/-- Iterated open-disc differentiation agrees with iterated formal differentiation. -/
@[simp]
theorem coe_iterate_derivative (k : ℕ) (f : OnOpenDisc.subring R R₀) :
    ((derivative (R := R) (R₀ := R₀))^[k] f : R⟦X⟧) = (d⁄dX)^[k] (f : R⟦X⟧) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', coe_derivative, ih,
      Function.iterate_succ_apply']

/-- The first Hasse derivative on an open disc is formal differentiation. -/
theorem hasseDeriv_one_eq_derivative (f : OnOpenDisc.subring R R₀) :
    hasseDeriv 1 f = derivative f :=
  Subtype.ext (PowerSeries.hasseDeriv_one_apply (f : R⟦X⟧))

/-- `k!` times the `k`-th Hasse derivative is the `k`-th iterated derivative on an open disc. -/
theorem factorial_smul_hasseDeriv (k : ℕ) (f : OnOpenDisc.subring R R₀) :
    k.factorial • hasseDeriv k f = (derivative (R := R) (R₀ := R₀))^[k] f :=
  Subtype.ext <| by
    rw [← Subring.subtype_apply, map_nsmul, Subring.subtype_apply, coe_hasseDeriv,
      coe_iterate_derivative, PowerSeries.factorial_smul_hasseDeriv]

/-- Formal differentiation commutes with every Hasse derivative on an open disc. -/
theorem derivative_hasseDeriv (k : ℕ) (f : OnOpenDisc.subring R R₀) :
    derivative (hasseDeriv k f) = hasseDeriv k (derivative f) := by
  rw [← hasseDeriv_one_eq_derivative, ← hasseDeriv_one_eq_derivative, hasseDeriv_comm]

/-- On polynomials, open-disc differentiation agrees with `Polynomial.derivative`. -/
@[simp]
theorem derivative_polynomialHom (p : Polynomial R) :
    derivative (OnOpenDisc.polynomialHom (R₀ := R₀) p) =
      OnOpenDisc.polynomialHom (Polynomial.derivative p) :=
  Subtype.ext (by simp [PowerSeries.derivative_coe])

/-- Bounded coefficient maps commute with formal differentiation on open discs. -/
theorem mapHom_derivative {S : Type*} [NormedCommRing S] (φ : R →+* S) {C : ℝ}
    (hφ : ∀ x, ‖φ x‖ ≤ C * ‖x‖) (f : OnOpenDisc.subring R R₀) :
    mapHom φ hφ (derivative f) = derivative (mapHom φ hφ f) :=
  Subtype.ext (by simp [PowerSeries.derivative_map])

/-- **Chain rule for rescaling** on open discs: `(f(uX))' = u • f'(uX)`. -/
theorem derivative_rescaleHom {S₀ : ℝ} {u : R} (hu : ‖u‖ * S₀ ≤ R₀)
    (f : OnOpenDisc.subring R R₀) :
    derivative (rescaleHom hu f) = u • rescaleHom hu (derivative f) :=
  Subtype.ext <| by
    rw [coe_derivative, coe_rescaleHom, PowerSeries.derivative_rescale, coe_smul_subring,
      coe_rescaleHom, coe_derivative, smul_eq_C_mul]

end NormedCommRing

section UltrametricDerivative

variable {R : Type*} [NormedCommRing R] [IsUltrametricDist R] {R₀ : ℝ}

attribute [local instance] radius_pos

/-- On each smaller positive closed disc of radius `r`, formal differentiation has Gauss norm at
most `r⁻¹` times that of the input series. -/
theorem norm_restrict_derivative_le (r : Set.Ioo (0 : ℝ) R₀) (f : OnOpenDisc.subring R R₀) :
    ‖restrict r (derivative f)‖ ≤ (r : ℝ)⁻¹ * ‖restrict r f‖ := by
  simpa only [hasseDeriv_one_eq_derivative, pow_one] using norm_restrict_hasseDeriv_le 1 r f

/-- Formal differentiation is uniformly continuous for the open-disc Gauss uniformity. -/
theorem uniformContinuous_derivative :
    UniformContinuous (derivative (R := R) (R₀ := R₀)) := by
  have hfun : (derivative : OnOpenDisc.subring R R₀ → OnOpenDisc.subring R R₀) = hasseDeriv 1 :=
    funext fun f ↦ (hasseDeriv_one_eq_derivative f).symm
  rw [hfun]
  exact uniformContinuous_hasseDeriv 1

/-- Formal differentiation is continuous for the open-disc Gauss topology. -/
@[continuity]
theorem continuous_derivative :
    Continuous (derivative (R := R) (R₀ := R₀)) :=
  uniformContinuous_derivative.continuous

section Complete

variable [CompleteSpace R]

/-- The `k`-th coefficient of a Taylor translate on the open disc is the value at the centre of
the `k`-th open-disc Hasse derivative. -/
theorem coeff_taylorHom {a : R} (ha : ‖a‖ < R₀) (f : OnOpenDisc.subring R R₀) (k : ℕ) :
    coeff k (taylorHom ha f : R⟦X⟧) = (hasseDeriv k f : R⟦X⟧).evalAt a := by
  rw [coe_taylorHom, coeff_taylor, coe_hasseDeriv]

/-- Hasse derivatives commute with Taylor translation on open discs. -/
theorem hasseDeriv_taylorHom {a : R} (ha : ‖a‖ < R₀) (k : ℕ) (f : OnOpenDisc.subring R R₀) :
    hasseDeriv k (taylorHom ha f) = taylorHom ha (hasseDeriv k f) :=
  Subtype.ext <| by
    rw [coe_hasseDeriv, coe_taylorHom, coe_taylorHom, coe_hasseDeriv]
    exact (OnOpenDisc.mem_subring.mp f.2).hasseDeriv_taylor ha k

/-- Formal differentiation commutes with Taylor translation on open discs. -/
theorem derivative_taylorHom {a : R} (ha : ‖a‖ < R₀) (f : OnOpenDisc.subring R R₀) :
    derivative (taylorHom ha f) = taylorHom ha (derivative f) := by
  rw [← hasseDeriv_one_eq_derivative, ← hasseDeriv_one_eq_derivative, hasseDeriv_taylorHom]

/-- **Chain rule for affine coordinate changes** on open discs: `(f(a + uX))' = u • f'(a + uX)`. -/
theorem derivative_affineHom {S₀ : ℝ} {a u : R} (ha : ‖a‖ < R₀) (hu : ‖u‖ * S₀ ≤ R₀)
    (f : OnOpenDisc.subring R R₀) :
    derivative (affineHom ha hu f) = u • affineHom ha hu (derivative f) := by
  rw [affineHom_apply, affineHom_apply, derivative_rescaleHom, derivative_taylorHom]

/-- **Chain rule for analytic substitution on open discs.** Differentiating `f(g(X))` produces
`f'(g(X)) * g'(X)`, even when `g` has a nonzero constant coefficient. -/
theorem derivative_analyticSubst {S₀ : ℝ} [Fact (0 < S₀)] (g : OnOpenDisc.subring R S₀)
    (hg : ∀ s : Set.Ioo (0 : ℝ) S₀, ‖restrict s g‖ < R₀) (f : OnOpenDisc.subring R R₀) :
    derivative (analyticSubst g hg f) = analyticSubst g hg (derivative f) * derivative g := by
  let L (h : OnOpenDisc.subring R R₀) := derivative (analyticSubst g hg h)
  let M (h : OnOpenDisc.subring R R₀) := analyticSubst g hg (derivative h) * derivative g
  have hmul {x y} (hx : L x = M x) (hy : L y = M y) : L (x * y) = M (x * y) := by
    simp only [L, M, map_mul, Derivation.leibniz, smul_eq_mul, map_add] at hx hy ⊢
    rw [hx, hy]
    ring
  have hpoly (p : Polynomial R) : L (OnOpenDisc.polynomialHom p) =
      M (OnOpenDisc.polynomialHom p) := by
    induction p using Polynomial.induction_on with
    | C a => simp [L, M]
    | add p q hp hq => simp only [L, M, map_add, add_mul] at hp hq ⊢; rw [hp, hq]
    | monomial n a ih =>
      rw [pow_succ, ← mul_assoc, map_mul]
      exact hmul ih (by simp [L, M])
  have hL : Continuous L := continuous_derivative.comp (continuous_analyticSubst g hg)
  have hM : Continuous M :=
    ((continuous_analyticSubst g hg).comp continuous_derivative).mul continuous_const
  exact congrFun (hL.ext_on denseRange_polynomialHom hM fun _ ⟨p, hp⟩ ↦ hp ▸ hpoly p) f

end Complete

end UltrametricDerivative

end TauCeti.PowerSeries.OnOpenDisc
