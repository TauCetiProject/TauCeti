/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.Sigma0
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Moebius
import TauCeti.Analysis.Normed.Ring.MulUnit
import TauCeti.Analysis.Normed.Ring.UnitBall

/-!
# Analytic weights and their automorphy factors on Tate algebras

Let `O` be a commutative ring (the integers `𝒪_v` of a local field), `I` an ideal of `O` inside
its Jacobson radical (a power `𝔭_vᵗ` of the maximal ideal), and `R` a complete ultrametric
normed commutative ring with `‖1‖ = 1`, reached from `O` by ring homomorphisms
`σ₁, …, σ_k : O → R` into the closed unit ball (the embeddings `F_v → K` followed by
`K → R`). The matrices `!![a, b; c, d]` over `O` with `c ∈ I` and `d` a unit form a monoid
`Σ₀(I)` (`TauCeti.Matrix.sigma0Submonoid`); over `ℤ_p` with `I = pᵗ ℤ_p`, its matrices of
nonzero determinant form Jacobs's monoid `Σ_t`. When `σᵢ` maps `I` into the open unit ball, each
`γ ∈ Σ₀(I)` acts on the closed unit polydisc in the coordinates `z₁, …, z_k` by the Möbius
transformations
`w_{γ,i} = (σᵢ(a) zᵢ + σᵢ(b)) / (σᵢ(c) zᵢ + σᵢ(d))`
(`TauCeti.MvPowerSeries.sigma0ToMoebius`).

An **analytic weight** (`TauCeti.MvPowerSeries.AnalyticWeight`) for `σ` and polyradius `r` is a
character `n : Oˣ →* R` together with a restricted series `N ∈ R{y/r}` expanding it near `1`:

* `n (1 + y) = N(σ₁ y, …, σ_k y)` whenever `‖σᵢ y‖ ≤ rᵢ` for every `i`, and
* `N(x ⊕ x') = N(x) N(x')` as formal power series in `2k` variables, where
  `(x ⊕ x')ᵢ = xᵢ + x'ᵢ + xᵢ x'ᵢ` is the multiplicative formal group law in each coordinate.

The second condition is the multiplicativity of `n` on `1 + I` stated without evaluation at
points, so it is meaningful over nonreduced and integral coefficient rings. On its own it only
forces `N(0)` to be idempotent; the first condition gives `N(0) = n(1) = 1`
(`TauCeti.MvPowerSeries.AnalyticWeight.constantCoeff_expansion`). For `k = 1`, the two together
say that `N - 1` is an endomorphism of the multiplicative formal group law.

For an analytic weight whose radii lie below one and contain the images of `I`, the factor

`j(γ) = n(d) · N(σ₁(c/d) z₁, …, σ_k(c/d) z_k)`,

the expansion of `n(c z + d) = n(d) n(1 + c z / d)`, satisfies the cocycle law
`j(γ δ) = j(γ)(w_δ) · j(δ)` (`TauCeti.MvPowerSeries.AnalyticWeight.factor_mul`). Together with the
Möbius substitutions it is a restricted automorphy factor
(`TauCeti.MvPowerSeries.AnalyticWeight.automorphyFactor`), so `f ↦ j(γ) · f(w_γ)` is a right action
of `Σ₀(I)` on the unit Tate algebra `R⟨z₁, …, z_k⟩` by bounded operators. Twisting by a character
of the determinant (`TauCeti.MvPowerSeries.RestrictedAutomorphyFactor.twist`) adds the
determinant part `ν(det γ)` of the weight.

The algebraic weight `u ↦ ∏ᵢ σᵢ(u) ^ mᵢ`, with expansion `∏ᵢ (1 + yᵢ) ^ mᵢ`
(`TauCeti.MvPowerSeries.AnalyticWeight.algebraic`), recovers the polynomial automorphy factor
`∏ᵢ (σᵢ(c) zᵢ + σᵢ(d)) ^ mᵢ` of `TauCeti.MvPowerSeries.moebiusAutomorphyFactor`
(`TauCeti.MvPowerSeries.AnalyticWeight.automorphyFactor_algebraic`).

## Main definitions

* `TauCeti.MvPowerSeries.sigma0ToMoebius`: the action of `Σ₀(I)` on the unit polydisc through
  the `σᵢ`.
* `TauCeti.MvPowerSeries.AnalyticWeight`: a character of `Oˣ` with a restricted expansion near
  `1` that is multiplicative as a formal power series.
* `TauCeti.MvPowerSeries.AnalyticWeight.automorphyFactor`: the automorphy factor
  `γ ↦ (w_γ, n(d) · N(σ(c/d) z))` of an analytic weight.
* `TauCeti.MvPowerSeries.AnalyticWeight.algebraic`: the algebraic weight `u ↦ ∏ᵢ σᵢ(u) ^ mᵢ`.

## Main results

* `TauCeti.MvPowerSeries.AnalyticWeight.restrictedAnalyticSubst_expansion_add_add_mul`: the
  expansion is multiplicative for the group law `x ⊕ x'` at every pair of arguments of Gauss norm
  at most `rᵢ ≤ 1` in any Tate algebra, including arguments with nonzero constant terms.
* `TauCeti.MvPowerSeries.AnalyticWeight.factor_mul`: the cocycle law of the analytic factor.
* `TauCeti.MvPowerSeries.AnalyticWeight.norm_factor_le`: the bound `‖j(γ)‖ ≤ ‖n(d)‖ ‖N‖`.
* `TauCeti.MvPowerSeries.AnalyticWeight.norm_automorphyFactor_slash_apply_le`: each slash operator
  has norm at most `‖n(d)‖ ‖N‖`.
* `TauCeti.MvPowerSeries.AnalyticWeight.automorphyFactor_algebraic`: the algebraic weights give the
  polynomial automorphy factors.

## References

* K. Buzzard, *Eigenvarieties*, in *L-functions and Galois representations*, LMS Lecture Note
  Ser. 320 (2007), 59–120, §§9–10.
* D. Jacobs, *Slopes of compact Hecke operators*, PhD thesis, Imperial College London (2003),
  §1.5.
-/

public section

open MvPowerSeries TauCeti.Matrix

namespace TauCeti.MvPowerSeries

section Sigma0

variable {O : Type*} [CommRing O]

variable {I : Ideal O} {hI : I ≤ Ring.jacobson O} {γ : Matrix (Fin 2) (Fin 2) O}

variable {R : Type*} [NormedCommRing R] [NormOneClass R] [IsUltrametricDist R] [CompleteSpace R]

/-- A ring homomorphism into the closed unit ball of `R` mapping `I` into the open unit ball maps
`Σ₀(I)` into the monoid of matrices acting on the closed unit disc by Möbius transformations. -/
theorem map_mem_moebiusSubmonoid_of_mem_sigma0Submonoid (σ : O →+* R) (hσ : ∀ x, ‖σ x‖ ≤ 1)
    (hσI : ∀ y ∈ I, ‖σ y‖ < 1) (hγ : γ ∈ sigma0Submonoid I hI) :
    σ.mapMatrix γ ∈ moebiusSubmonoid R := by
  obtain ⟨hc, u, hu⟩ := mem_sigma0Submonoid_iff.mp hγ
  have hσu : ‖σ ↑u‖ = 1 := norm_map_eq_one_of_isUnit hσ u.isUnit
  have hσu' : ‖σ ↑u⁻¹‖ = 1 := norm_map_eq_one_of_isUnit hσ u⁻¹.isUnit
  refine mem_moebiusSubmonoid_iff.mpr ⟨hσ _, hσ _, hσI _ hc, ?_, ?_⟩
  · simp only [RingHom.mapMatrix_apply, Matrix.map_apply, ← hu]
    refine (Units.isNormMulUnit_iff_norm_inv (Units.map σ.toMonoidHom u)).mpr ?_
    simp [hσu, hσu']
  · simpa [← hu] using hσu

variable {k : ℕ}

/-- The action of `Σ₀(I)` on the closed unit polydisc in `k` variables: the `i`-th coordinate of
`γ` acts through `σᵢ`, by the Möbius transformation of `σᵢ(γ)`. -/
noncomputable def sigma0ToMoebius (σ : Fin k → O →+* R) (hσ : ∀ i x, ‖σ i x‖ ≤ 1)
    (hσI : ∀ i, ∀ y ∈ I, ‖σ i y‖ < 1) :
    sigma0Submonoid I hI →* (Fin k → moebiusSubmonoid R) where
  toFun γ i := ⟨(σ i).mapMatrix (γ : Matrix (Fin 2) (Fin 2) O),
    map_mem_moebiusSubmonoid_of_mem_sigma0Submonoid (σ i) (hσ i) (hσI i) γ.property⟩
  map_one' := funext fun i ↦ Subtype.ext (map_one (σ i).mapMatrix)
  map_mul' γ δ := funext fun i ↦ Subtype.ext
    (map_mul (σ i).mapMatrix (γ : Matrix (Fin 2) (Fin 2) O) δ)

@[simp]
theorem coe_sigma0ToMoebius_apply (σ : Fin k → O →+* R) (hσ : ∀ i x, ‖σ i x‖ ≤ 1)
    (hσI : ∀ i, ∀ y ∈ I, ‖σ i y‖ < 1) (γ : sigma0Submonoid I hI) (i : Fin k) :
    (sigma0ToMoebius σ hσ hσI γ i : Matrix (Fin 2) (Fin 2) R) =
      (σ i).mapMatrix (γ : Matrix (Fin 2) (Fin 2) O) :=
  (rfl)

/-- If each `σᵢ` maps `I` into the closed ball of radius `rᵢ < 1`, then each `σᵢ(γ)` for
`γ ∈ Σ₀(I)` acts on the closed unit disc by a Möbius transformation. -/
theorem mapMatrix_mem_moebiusSubmonoid {r : Fin k → ℝ} (σ : Fin k → O →+* R)
    (hσ : ∀ i x, ‖σ i x‖ ≤ 1) (hσI : ∀ i, ∀ y ∈ I, ‖σ i y‖ ≤ r i) (hr : ∀ i, r i < 1)
    (γ : sigma0Submonoid I hI) (i : Fin k) :
    (σ i).mapMatrix (γ : Matrix (Fin 2) (Fin 2) O) ∈ moebiusSubmonoid R :=
  map_mem_moebiusSubmonoid_of_mem_sigma0Submonoid (σ i) (hσ i)
    (fun y hy ↦ (hσI i y hy).trans_lt (hr i)) γ.property

end Sigma0

section AnalyticWeight

variable {O : Type*} [CommRing O] (R : Type*) [NormedCommRing R] [IsUltrametricDist R]
  [CompleteSpace R] {k : ℕ}

/-- An **analytic weight** for the ring homomorphisms `σ : Fin k → O →+* R` and the polyradius
`r`: a character `n : Oˣ →* R` together with a restricted series `N ∈ R{y/r}` such that

* `n (1 + y) = N(σ₁ y, …, σ_k y)` whenever every `‖σᵢ y‖ ≤ rᵢ`, and
* `N(x ⊕ x') = N(x) N(x')` as formal power series in the `2k` variables `x₁, …, x_k`,
  `x'₁, …, x'_k`, where `(x ⊕ x')ᵢ = xᵢ + x'ᵢ + xᵢ x'ᵢ`.

The series `N` is the expansion of `y ↦ n(1 + y)` in the coordinates `σᵢ y`; the second condition
is the multiplicativity of `n` on `1 + y`, as an identity of power series. -/
@[ext]
structure AnalyticWeight (σ : Fin k → O →+* R) (r : Fin k → ℝ) where
  /-- The character `n : Oˣ →* R`. -/
  char : Oˣ →* R
  /-- The expansion `N ∈ R{y/r}` of `y ↦ n(1 + y)`. -/
  expansion : IsRestricted.subring (R := R) r
  /-- The expansion is multiplicative for the multiplicative formal group law in each
  coordinate: `N(x ⊕ x') = N(x) N(x')`. -/
  subst_expansion_add_add_mul :
    subst (fun i : Fin k ↦ (X (Fin.castAdd k i) + X (Fin.natAdd k i) +
        X (Fin.castAdd k i) * X (Fin.natAdd k i) : MvPowerSeries (Fin (k + k)) R))
        (expansion : MvPowerSeries (Fin k) R) =
      subst (fun i : Fin k ↦ (X (Fin.castAdd k i) : MvPowerSeries (Fin (k + k)) R))
          (expansion : MvPowerSeries (Fin k) R) *
        subst (fun i : Fin k ↦ (X (Fin.natAdd k i) : MvPowerSeries (Fin (k + k)) R))
          (expansion : MvPowerSeries (Fin k) R)
  /-- The expansion computes the character: `n (1 + y) = N(σ y)` on the polydisc of radii `r`. -/
  char_eq_restrictedEval₂ : ∀ (u : Oˣ) (y : O) (hy : ∀ i, ‖σ i y‖ ≤ r i), (u : O) = 1 + y →
    char u = restrictedEval₂ (RingHom.id R) (fun i ↦ σ i y) (fun _ ↦ le_rfl) hy expansion

namespace AnalyticWeight

variable {R} {σ : Fin k → O →+* R} {r : Fin k → ℝ} (κ : AnalyticWeight R σ r)

section Expansion

variable [NormOneClass R] [∀ i, Fact (0 < r i)]

/-- The polyradius `(r, r)` of the `2k` variables `x, x'` is positive. -/
private theorem fact_pos_append (j : Fin (k + k)) : Fact (0 < Fin.append r r j) :=
  ⟨Fin.addCases (fun i ↦ by rw [Fin.append_left]; exact Fact.out)
    (fun i ↦ by rw [Fin.append_right]; exact Fact.out) j⟩

attribute [local instance] fact_pos_append

/-- The variable `x_i` of the first factor, in `R{(x, x')/(r, r)}`. -/
private noncomputable abbrev leftX (i : Fin k) :
    IsRestricted.subring (R := R) (Fin.append r r) :=
  ⟨X (Fin.castAdd k i), isRestricted_monomial _ (Finsupp.single _ 1) 1⟩

/-- The variable `x'_i` of the second factor, in `R{(x, x')/(r, r)}`. -/
private noncomputable abbrev rightX (i : Fin k) :
    IsRestricted.subring (R := R) (Fin.append r r) :=
  ⟨X (Fin.natAdd k i), isRestricted_monomial _ (Finsupp.single _ 1) 1⟩

omit [CompleteSpace R] in
private theorem norm_leftX (i : Fin k) : ‖leftX (R := R) (r := r) i‖ ≤ r i :=
  ((norm_X _).trans (Fin.append_left r r i)).le

omit [CompleteSpace R] in
private theorem norm_rightX (i : Fin k) : ‖rightX (R := R) (r := r) i‖ ≤ r i :=
  ((norm_X _).trans (Fin.append_right r r i)).le

/-- **The expansion is multiplicative for the group law at every pair of arguments.** For series
`aᵢ, bᵢ` of Gauss norm at most `rᵢ ≤ 1` in any Tate algebra, `N(a ⊕ b) = N(a) N(b)`, where
`(a ⊕ b)ᵢ = aᵢ + bᵢ + aᵢ bᵢ`. The arguments may have nonzero constant terms. -/
theorem restrictedAnalyticSubst_expansion_add_add_mul (hr : ∀ i, r i ≤ 1) {τ : Type*}
    {s : τ → ℝ} [∀ j, Fact (0 < s j)] (a b : Fin k → IsRestricted.subring (R := R) s)
    (ha : ∀ i, ‖a i‖ ≤ r i) (hb : ∀ i, ‖b i‖ ≤ r i) (hab : ∀ i, ‖a i + b i + a i * b i‖ ≤ r i) :
    restrictedAnalyticSubst (fun i ↦ a i + b i + a i * b i) hab κ.expansion =
      restrictedAnalyticSubst a ha κ.expansion * restrictedAnalyticSubst b hb κ.expansion := by
  -- the formal law, read in the Tate algebra `R{(x, x')/(r, r)}`
  have hlaw : restrictedAnalyticSubst (fun i ↦ leftX i + rightX i + leftX i * rightX i)
      (fun i ↦ norm_add_add_mul_le (R := IsRestricted.subring (R := R) (Fin.append r r)) (hr i)
        (norm_leftX i) (norm_rightX i)) κ.expansion =
      restrictedAnalyticSubst leftX norm_leftX κ.expansion *
        restrictedAnalyticSubst rightX norm_rightX κ.expansion := by
    refine Subtype.ext ?_
    rw [Subring.coe_mul,
      coe_restrictedAnalyticSubst_eq_subst _ _ (hasSubst_of_constantCoeff_zero fun i ↦ by simp),
      coe_restrictedAnalyticSubst_eq_subst _ _ (hasSubst_of_constantCoeff_zero fun i ↦ by simp),
      coe_restrictedAnalyticSubst_eq_subst _ _ (hasSubst_of_constantCoeff_zero fun i ↦ by simp)]
    -- unfold the subring coercions of `+`, `*` and of the variables `leftX`, `rightX`
    simp only [Subring.coe_add, Subring.coe_mul, leftX, rightX]
    exact κ.subst_expansion_add_add_mul
  -- substitute `(x, x') ↦ (a, b)`
  have hab' (j : Fin (k + k)) : ‖Fin.append a b j‖ ≤ Fin.append r r j :=
    Fin.addCases (fun i ↦ by rw [Fin.append_left, Fin.append_left]; exact ha i)
      (fun i ↦ by rw [Fin.append_right, Fin.append_right]; exact hb i) j
  have h := congrArg (restrictedAnalyticSubst (Fin.append a b) hab') hlaw
  simp only [map_mul, restrictedAnalyticSubst_restrictedAnalyticSubst, map_add,
    restrictedAnalyticSubst_X, Fin.append_left, Fin.append_right] at h
  exact h

omit [NormOneClass R] in
/-- The expansion has constant coefficient `n(1) = 1`. -/
@[simp]
theorem constantCoeff_expansion :
    constantCoeff (κ.expansion : MvPowerSeries (Fin k) R) = 1 := by
  have hy : ∀ i, ‖σ i 0‖ ≤ r i := fun i ↦ by simpa using (Fact.out : 0 < r i).le
  -- evaluating at `0` is substituting `0`, which reads off the constant coefficient
  have h : algebraMap R (IsRestricted.subring (R := R) fun _ : Fin k ↦ (1 : ℝ))
      (constantCoeff (κ.expansion : MvPowerSeries (Fin k) R)) = 1 := by
    rw [← restrictedAnalyticSubst_zero_apply (fun i ↦ by simpa using (Fact.out : 0 < r i).le)]
    calc _ = restrictedAnalyticSubst (fun i ↦ algebraMap R _ (σ i 0))
          (fun i ↦ (norm_algebraMap_isRestrictedSubring _).trans_le (hy i)) κ.expansion :=
          restrictedAnalyticSubst_congr (funext fun i ↦ by simp) _
      _ = 1 := by
          rw [restrictedAnalyticSubst_algebraMap _ hy, ← κ.char_eq_restrictedEval₂ 1 0 hy (by simp),
            map_one, map_one]
  simpa using congrArg (fun f : IsRestricted.subring (R := R) (fun _ : Fin k ↦ (1 : ℝ)) ↦
    constantCoeff (f : MvPowerSeries (Fin k) R)) h

end Expansion

/-- The identity behind the cocycle law of an analytic factor, in any commutative ring. Read
`P, Q, P', Q', B'` as `σ(c), σ(d), σ(c'), σ(d'), σ(b')`, `C'', Q''` as the lower row of
`σ(γ δ)`, `E, E', E''` as the inverses of `σ(d), σ(d'), σ(d'')`, `W` as the Möbius series of `δ`
and `x` as the variable. From the denominator law `(c w + d)(c' x + d') = c'' x + d''` it follows
that `y_A ⊕ y_B = y_C ⊕ y₀` for `y_A = (c/d) w`, `y_B = (c'/d') x`, `y_C = (c''/d'') x` and
`y₀ = c b'/(d d')`. -/
private theorem add_add_mul_eq_of_denom {A : Type*} [CommRing A]
    {P Q E P' Q' E' B' C'' Q'' E'' W x : A} (h1 : Q * E = 1) (h2 : Q' * E' = 1)
    (h3 : Q'' * E'' = 1) (h4 : Q'' = P * B' + Q * Q')
    (H : (P * W + Q) * (P' * x + Q') = C'' * x + Q'') :
    P * E * W + P' * E' * x + P * E * W * (P' * E' * x) =
      C'' * E'' * x + P * B' * E * E' + C'' * E'' * x * (P * B' * E * E') := by
  have ha : 1 + P * E * W = E * (P * W + Q) := by linear_combination -h1
  have hb : 1 + P' * E' * x = E' * (P' * x + Q') := by linear_combination -h2
  have hc : 1 + C'' * E'' * x = E'' * (C'' * x + Q'') := by linear_combination -h3
  have hd : 1 + P * B' * E * E' = E * E' * Q'' := by
    linear_combination -h1 - E * Q * h2 - E * E' * h4
  have h : (1 + P * E * W) * (1 + P' * E' * x) = (1 + C'' * E'' * x) * (1 + P * B' * E * E') := by
    rw [ha, hb, hc, hd]
    linear_combination E * E' * H - E * E' * (C'' * x + Q'') * h3
  linear_combination h

section Factor

variable [NormOneClass R] [∀ i, Fact (0 < r i)] {I : Ideal O} {hI : I ≤ Ring.jacobson O}

variable (σ) in
/-- The argument `(σᵢ(c/d) zᵢ)ᵢ` at which the expansion is substituted in the factor of `γ`. -/
noncomputable def factorArg (γ : sigma0Submonoid I hI) (i : Fin k) :
    IsRestricted.subring (R := R) fun _ : Fin k ↦ (1 : ℝ) :=
  σ i ((γ : Matrix (Fin 2) (Fin 2) O) 1 0 * ↑(sigma0LowerRightUnit γ)⁻¹) •
    ⟨X i, isRestricted_monomial _ (Finsupp.single i 1) 1⟩

omit [CompleteSpace R] [NormOneClass R] [∀ i, Fact (0 < r i)] in
theorem factorArg_apply (γ : sigma0Submonoid I hI) (i : Fin k) :
    factorArg σ γ i =
      σ i ((γ : Matrix (Fin 2) (Fin 2) O) 1 0 * ↑(sigma0LowerRightUnit γ)⁻¹) •
        ⟨X i, isRestricted_monomial _ (Finsupp.single i 1) 1⟩ :=
  (rfl)

omit [CompleteSpace R] [NormOneClass R] [∀ i, Fact (0 < r i)] in
theorem norm_factorArg_le (hσI : ∀ i, ∀ y ∈ I, ‖σ i y‖ ≤ r i) (γ : sigma0Submonoid I hI)
    (i : Fin k) : ‖factorArg σ γ i‖ ≤ r i := by
  rw [factorArg, norm_smul_X, mul_one]
  exact hσI i _ (I.mul_mem_right _ (lowerLeft_mem_of_mem_sigma0Submonoid γ.property))

omit [CompleteSpace R] [NormOneClass R] [∀ i, Fact (0 < r i)] in
/-- For an upper triangular `γ`, with `c = 0`, the argument of the factor vanishes. -/
theorem factorArg_eq_zero_of_lowerLeft_eq_zero {γ : sigma0Submonoid I hI}
    (hc : (γ : Matrix (Fin 2) (Fin 2) O) 1 0 = 0) : factorArg σ γ = 0 :=
  funext fun i ↦ by simp [factorArg, hc]

omit [CompleteSpace R] [NormOneClass R] [∀ i, Fact (0 < r i)] in
@[simp]
theorem factorArg_one : factorArg σ (1 : sigma0Submonoid I hI) = 0 :=
  factorArg_eq_zero_of_lowerLeft_eq_zero (by simp)

/-- The **analytic factor** `j(γ) = n(d) · N(σ₁(c/d) z₁, …, σ_k(c/d) z_k)` of `γ ∈ Σ₀(I)`, the
expansion of `n(c z + d) = n(d) n(1 + c z / d)` in the unit Tate algebra `R⟨z₁, …, z_k⟩`. -/
noncomputable def factor (hσI : ∀ i, ∀ y ∈ I, ‖σ i y‖ ≤ r i) (γ : sigma0Submonoid I hI) :
    IsRestricted.subring (R := R) fun _ : Fin k ↦ (1 : ℝ) :=
  κ.char (sigma0LowerRightUnit γ) •
    restrictedAnalyticSubst (factorArg σ γ) (norm_factorArg_le hσI γ) κ.expansion

omit [NormOneClass R] [∀ i, Fact (0 < r i)] in
theorem factor_def (hσI : ∀ i, ∀ y ∈ I, ‖σ i y‖ ≤ r i) (γ : sigma0Submonoid I hI) :
    κ.factor hσI γ = κ.char (sigma0LowerRightUnit γ) •
      restrictedAnalyticSubst (factorArg σ γ) (norm_factorArg_le hσI γ) κ.expansion :=
  (rfl)

omit [NormOneClass R] in
/-- For an upper triangular `γ`, with `c = 0`, the analytic factor is the constant `n(d)`. For
instance a scalar matrix `u I` has factor `n(u)`. -/
theorem factor_eq_algebraMap_of_lowerLeft_eq_zero (hσI : ∀ i, ∀ y ∈ I, ‖σ i y‖ ≤ r i)
    {γ : sigma0Submonoid I hI} (hc : (γ : Matrix (Fin 2) (Fin 2) O) 1 0 = 0) :
    κ.factor hσI γ = algebraMap R _ (κ.char (sigma0LowerRightUnit γ)) := by
  have h0 := factorArg_eq_zero_of_lowerLeft_eq_zero (σ := σ) hc
  rw [factor_def, restrictedAnalyticSubst_congr (hg' := h0 ▸ norm_factorArg_le hσI γ) h0,
    restrictedAnalyticSubst_zero_apply, constantCoeff_expansion, map_one, Algebra.smul_def,
    mul_one]

omit [NormOneClass R] in
/-- The analytic factor of the identity is one. -/
@[simp]
theorem factor_one (hσI : ∀ i, ∀ y ∈ I, ‖σ i y‖ ≤ r i) :
    κ.factor hσI (1 : sigma0Submonoid I hI) = 1 := by
  rw [κ.factor_eq_algebraMap_of_lowerLeft_eq_zero hσI (by simp), sigma0LowerRightUnit_one,
    map_one, map_one]

omit [NormOneClass R] in
/-- The analytic factor is bounded by `‖n(d)‖ ‖N‖`. -/
theorem norm_factor_le (hσI : ∀ i, ∀ y ∈ I, ‖σ i y‖ ≤ r i) (γ : sigma0Submonoid I hI) :
    ‖κ.factor hσI γ‖ ≤ ‖κ.char (sigma0LowerRightUnit γ)‖ * ‖κ.expansion‖ := by
  rw [factor_def]
  exact (norm_smul_le _ _).trans (mul_le_mul_of_nonneg_left
    (norm_restrictedAnalyticSubst_le _ _ _) (norm_nonneg _))

/-- The element `y₀ = c b' / (d d')` of `I` for which `d'' = d d' (1 + y₀)`, where `d''` is the
lower right entry of `γ δ`. -/
private noncomputable def crossTerm (γ δ : sigma0Submonoid I hI) : O :=
  (γ : Matrix (Fin 2) (Fin 2) O) 1 0 * (δ : Matrix (Fin 2) (Fin 2) O) 0 1 *
    ↑(sigma0LowerRightUnit γ)⁻¹ * ↑(sigma0LowerRightUnit δ)⁻¹

private theorem crossTerm_mem (γ δ : sigma0Submonoid I hI) : crossTerm γ δ ∈ I :=
  I.mul_mem_right _ (I.mul_mem_right _
    (I.mul_mem_right _ (lowerLeft_mem_of_mem_sigma0Submonoid γ.property)))

private theorem lowerRight_mul (γ δ : sigma0Submonoid I hI) :
    ((γ * δ : sigma0Submonoid I hI) : Matrix (Fin 2) (Fin 2) O) 1 1 =
      (γ : Matrix (Fin 2) (Fin 2) O) 1 0 * (δ : Matrix (Fin 2) (Fin 2) O) 0 1 +
        (γ : Matrix (Fin 2) (Fin 2) O) 1 1 * (δ : Matrix (Fin 2) (Fin 2) O) 1 1 := by
  simp [Matrix.mul_apply, Fin.sum_univ_two]

omit [NormOneClass R] [∀ i, Fact (0 < r i)] in
/-- The constant part of the cocycle law: `n(d'') = n(d) n(d') N(σ y₀)`, since
`d'' = d d' (1 + y₀)`. -/
private theorem char_sigma0LowerRightUnit_mul (hσI : ∀ i, ∀ y ∈ I, ‖σ i y‖ ≤ r i)
    (γ δ : sigma0Submonoid I hI) :
    κ.char (sigma0LowerRightUnit (γ * δ)) =
      κ.char (sigma0LowerRightUnit γ) * κ.char (sigma0LowerRightUnit δ) *
        restrictedEval₂ (RingHom.id R) (fun i ↦ σ i (crossTerm γ δ)) (fun _ ↦ le_rfl)
          (fun i ↦ hσI i _ (crossTerm_mem γ δ)) κ.expansion := by
  set D := sigma0LowerRightUnit γ
  set D' := sigma0LowerRightUnit δ
  have hu : ((D⁻¹ * D'⁻¹ * sigma0LowerRightUnit (γ * δ) : Oˣ) : O) = 1 + crossTerm γ δ := by
    have e1 : (↑D⁻¹ : O) * (γ : Matrix (Fin 2) (Fin 2) O) 1 1 = 1 := by
      rw [← coe_sigma0LowerRightUnit, Units.inv_mul]
    have e2 : (↑D'⁻¹ : O) * (δ : Matrix (Fin 2) (Fin 2) O) 1 1 = 1 := by
      rw [← coe_sigma0LowerRightUnit, Units.inv_mul]
    rw [Units.val_mul, Units.val_mul, coe_sigma0LowerRightUnit, lowerRight_mul, crossTerm]
    linear_combination (↑D'⁻¹ * (δ : Matrix (Fin 2) (Fin 2) O) 1 1 : O) * e1 + e2
  rw [← κ.char_eq_restrictedEval₂ _ _ _ hu, ← map_mul, ← map_mul]
  congr 1
  rw [mul_comm D⁻¹ D'⁻¹]
  group

omit [∀ i, Fact (0 < r i)] in
/-- The variable part of the cocycle law: with `w = w_δ`, the denominator law
`(c w + d)(c' z + d') = c'' z + d''` gives `y_A ⊕ y_B = y_C ⊕ y₀` for `y_A = σ(c/d) w`,
`y_B = σ(c'/d') z`, `y_C = σ(c''/d'') z` and the constant `y₀`. -/
private theorem factorArg_add_add_mul (γ δ : sigma0Submonoid I hI)
    (hδ : ∀ j, (σ j).mapMatrix (δ : Matrix (Fin 2) (Fin 2) O) ∈ moebiusSubmonoid R) (i : Fin k) :
    σ i ((γ : Matrix (Fin 2) (Fin 2) O) 1 0 * ↑(sigma0LowerRightUnit γ)⁻¹) •
        moebius i ((σ i).mapMatrix (δ : Matrix (Fin 2) (Fin 2) O)) + factorArg σ δ i +
      σ i ((γ : Matrix (Fin 2) (Fin 2) O) 1 0 * ↑(sigma0LowerRightUnit γ)⁻¹) •
        moebius i ((σ i).mapMatrix (δ : Matrix (Fin 2) (Fin 2) O)) * factorArg σ δ i =
    factorArg σ (γ * δ) i + algebraMap R _ (σ i (crossTerm γ δ)) +
      factorArg σ (γ * δ) i * algebraMap R _ (σ i (crossTerm γ δ)) := by
  have H := restrictedAnalyticSubst_moebiusDenom_mul_moebiusDenom (i := i)
    (g := (σ i).mapMatrix (γ : Matrix (Fin 2) (Fin 2) O)) hδ
  rw [restrictedAnalyticSubst_moebiusDenom, moebiusDenom_def, moebiusDenom_def, ← map_mul] at H
  set φ : O →+* IsRestricted.subring (R := R) (fun _ : Fin k ↦ (1 : ℝ)) :=
    (algebraMap R _).comp (σ i)
  have hinv (γ' : sigma0Submonoid I hI) :
      φ ((γ' : Matrix (Fin 2) (Fin 2) O) 1 1) * φ ↑(sigma0LowerRightUnit γ')⁻¹ = 1 := by
    rw [← map_mul, ← coe_sigma0LowerRightUnit, Units.mul_inv, map_one]
  set g : Matrix (Fin 2) (Fin 2) O := ↑γ
  set h : Matrix (Fin 2) (Fin 2) O := ↑δ
  set gh : Matrix (Fin 2) (Fin 2) O := ↑(γ * δ)
  have hgh : gh 1 1 = g 1 0 * h 0 1 + g 1 1 * h 1 1 := lowerRight_mul γ δ
  have := add_add_mul_eq_of_denom (P := φ (g 1 0)) (Q := φ (g 1 1))
    (E := φ ↑(sigma0LowerRightUnit γ)⁻¹) (P' := φ (h 1 0)) (Q' := φ (h 1 1))
    (E' := φ ↑(sigma0LowerRightUnit δ)⁻¹) (B' := φ (h 0 1)) (C'' := φ (gh 1 0))
    (Q'' := φ (gh 1 1)) (E'' := φ ↑(sigma0LowerRightUnit (γ * δ))⁻¹)
    (W := moebius i ((σ i).mapMatrix h))
    (x := ⟨X i, isRestricted_monomial _ (Finsupp.single i 1) 1⟩)
    (hinv γ) (hinv δ) (hinv (γ * δ))
    (by rw [hgh, map_add, map_mul, map_mul])
    (by simpa only [φ, RingHom.comp_apply, RingHom.mapMatrix_apply, Matrix.map_apply,
      Algebra.smul_def, gh, Submonoid.coe_mul] using H)
  simpa only [φ, RingHom.comp_apply, factorArg, crossTerm, Algebra.smul_def, map_mul] using this

variable (hσ : ∀ i x, ‖σ i x‖ ≤ 1) (hσI : ∀ i, ∀ y ∈ I, ‖σ i y‖ ≤ r i) (hr : ∀ i, r i < 1)

include hσ hr in
/-- **The cocycle law of the analytic factor**: `j(γ δ) = j(γ)(w_δ) · j(δ)`, where `w_δ` is the
Möbius substitution of `δ`. -/
theorem factor_mul (γ δ : sigma0Submonoid I hI) :
    κ.factor hσI (γ * δ) =
      restrictedAnalyticSubst (fun i ↦ moebius i ((σ i).mapMatrix (δ : Matrix (Fin 2) (Fin 2) O)))
        (fun i ↦ norm_moebius_le (mapMatrix_mem_moebiusSubmonoid σ hσ hσI hr δ i))
        (κ.factor hσI γ) * κ.factor hσI δ := by
  have hδ := mapMatrix_mem_moebiusSubmonoid σ hσ hσI hr δ
  -- the arguments `y_A = σ(c/d) w_δ`, `y_B`, `y_C` and `y₀` of the expansion, in the closed
  -- polydisc of radii `r`
  set yA := fun i ↦ σ i ((γ : Matrix (Fin 2) (Fin 2) O) 1 0 * ↑(sigma0LowerRightUnit γ)⁻¹) •
    moebius i ((σ i).mapMatrix (δ : Matrix (Fin 2) (Fin 2) O))
  have hA (i : Fin k) : ‖yA i‖ ≤ r i := (norm_smul_le _ _).trans
    ((mul_le_of_le_one_right (norm_nonneg _) (norm_moebius_le (hδ i))).trans
      (hσI i _ (I.mul_mem_right _ (lowerLeft_mem_of_mem_sigma0Submonoid γ.property))))
  set y0 := fun i ↦ algebraMap R (IsRestricted.subring (R := R) fun _ : Fin k ↦ (1 : ℝ))
    (σ i (crossTerm γ δ))
  have h0 (i : Fin k) : ‖y0 i‖ ≤ r i :=
    (norm_algebraMap_isRestrictedSubring _).trans_le (hσI i _ (crossTerm_mem γ δ))
  have hB := norm_factorArg_le hσI δ
  have hC := norm_factorArg_le hσI (γ * δ)
  have hr1 (i : Fin k) : r i ≤ 1 := (hr i).le
  -- `j(γ)(w_δ) = n(d) N(y_A)`
  have hsubst : restrictedAnalyticSubst
      (fun i ↦ moebius i ((σ i).mapMatrix (δ : Matrix (Fin 2) (Fin 2) O)))
      (fun i ↦ norm_moebius_le (hδ i)) (κ.factor hσI γ) =
      κ.char (sigma0LowerRightUnit γ) • restrictedAnalyticSubst yA hA κ.expansion := by
    rw [factor_def, map_smul, restrictedAnalyticSubst_restrictedAnalyticSubst]
    exact congrArg _ (restrictedAnalyticSubst_congr (funext fun i ↦ by
      rw [factorArg, map_smul, restrictedAnalyticSubst_X]) _)
  -- `N(y_A) N(y_B) = N(y_A ⊕ y_B) = N(y_C ⊕ y₀) = N(y_C) N(y₀)`
  rw [hsubst, factor_def, factor_def, smul_mul_smul_comm,
    ← κ.restrictedAnalyticSubst_expansion_add_add_mul hr1 _ _ hA hB
      (fun i ↦ norm_add_add_mul_le (hr1 i) (hA i) (hB i)),
    restrictedAnalyticSubst_congr (hg' := fun i ↦ norm_add_add_mul_le (hr1 i) (hC i) (h0 i))
      (funext (factorArg_add_add_mul γ δ hδ)),
    κ.restrictedAnalyticSubst_expansion_add_add_mul hr1 _ _ hC h0,
    restrictedAnalyticSubst_algebraMap _ (fun i ↦ hσI i _ (crossTerm_mem γ δ)),
    κ.char_sigma0LowerRightUnit_mul hσI]
  simp only [Algebra.smul_def, map_mul]
  ring

/-- The **automorphy factor of an analytic weight**: `γ ∈ Σ₀(I)` acts on the unit Tate algebra
`R⟨z₁, …, z_k⟩` through the Möbius substitution `w_γ` of the matrices `σᵢ(γ)` and the analytic
factor `j(γ) = n(d) · N(σ(c/d) z)`. Its slash operators `f ↦ j(γ) · f(w_γ)`
(`TauCeti.MvPowerSeries.RestrictedAutomorphyFactor.slash`) form a right action of `Σ₀(I)`. -/
noncomputable def automorphyFactor : RestrictedAutomorphyFactor (sigma0Submonoid I hI) R k where
  subst γ i := moebius i ((σ i).mapMatrix (γ : Matrix (Fin 2) (Fin 2) O))
  norm_subst_le γ i := norm_moebius_le (mapMatrix_mem_moebiusSubmonoid σ hσ hσI hr γ i)
  factor := κ.factor hσI
  subst_one i := by simp
  subst_mul γ δ i := by
    rw [Submonoid.coe_mul, map_mul]
    exact (restrictedAnalyticSubst_moebius (mapMatrix_mem_moebiusSubmonoid σ hσ hσI hr γ i)
      (mapMatrix_mem_moebiusSubmonoid σ hσ hσI hr δ)).symm
  factor_one := κ.factor_one hσI
  factor_mul γ δ := κ.factor_mul hσ hσI hr γ δ

@[simp]
theorem automorphyFactor_subst (γ : sigma0Submonoid I hI) (i : Fin k) :
    (κ.automorphyFactor hσ hσI hr).subst γ i =
      moebius i ((σ i).mapMatrix (γ : Matrix (Fin 2) (Fin 2) O)) :=
  (rfl)

@[simp]
theorem automorphyFactor_factor (γ : sigma0Submonoid I hI) :
    (κ.automorphyFactor hσ hσI hr).factor γ = κ.factor hσI γ :=
  (rfl)

/-- The slash operators of an analytic weight are bounded: `‖f|γ‖ ≤ ‖n(d)‖ ‖N‖ ‖f‖`. -/
theorem norm_automorphyFactor_slash_apply_le (γ : sigma0Submonoid I hI)
    (f : IsRestricted.subring (R := R) fun _ : Fin k ↦ (1 : ℝ)) :
    ‖(κ.automorphyFactor hσ hσI hr).slash (MulOpposite.op γ) f‖ ≤
      ‖κ.char (sigma0LowerRightUnit γ)‖ * ‖κ.expansion‖ * ‖f‖ :=
  ((κ.automorphyFactor hσ hσI hr).norm_slash_apply_le γ f).trans
    (mul_le_mul_of_nonneg_right (κ.norm_factor_le hσI γ) (norm_nonneg f))

end Factor

section Algebraic

variable (σ r) in
/-- The **algebraic weight** `u ↦ ∏ᵢ σᵢ(u) ^ mᵢ`, whose expansion `∏ᵢ (1 + yᵢ) ^ mᵢ` is a
polynomial, restricted at every polyradius. -/
noncomputable def algebraic (m : Fin k → ℕ) : AnalyticWeight R σ r where
  char :=
    { toFun u := ∏ i, σ i u ^ m i
      map_one' := by simp
      map_mul' u v := by simp [mul_pow, Finset.prod_mul_distrib] }
  expansion := ∏ i, (1 + ⟨X i, isRestricted_monomial _ (Finsupp.single i 1) 1⟩) ^ m i
  subst_expansion_add_add_mul := by
    have h₁ : HasSubst (fun i : Fin k ↦ (X (Fin.castAdd k i) + X (Fin.natAdd k i) +
        X (Fin.castAdd k i) * X (Fin.natAdd k i) : MvPowerSeries (Fin (k + k)) R)) :=
      hasSubst_of_constantCoeff_zero fun i ↦ by simp
    have h₂ : HasSubst (fun i : Fin k ↦ (X (Fin.castAdd k i) : MvPowerSeries (Fin (k + k)) R)) :=
      hasSubst_of_constantCoeff_zero fun i ↦ by simp
    have h₃ : HasSubst (fun i : Fin k ↦ (X (Fin.natAdd k i) : MvPowerSeries (Fin (k + k)) R)) :=
      hasSubst_of_constantCoeff_zero fun i ↦ by simp
    simp only [SubmonoidClass.coe_finsetProd, SubmonoidClass.coe_pow, Subring.coe_add,
      Subring.coe_one]
    rw [← coe_substAlgHom h₁, ← coe_substAlgHom h₂, ← coe_substAlgHom h₃]
    simp only [map_prod, map_pow, map_add, map_one, coe_substAlgHom, subst_X h₁, subst_X h₂,
      subst_X h₃, ← Finset.prod_mul_distrib, ← mul_pow]
    exact Finset.prod_congr rfl fun i _ ↦ by ring
  char_eq_restrictedEval₂ u y hy hu := by
    simp only [MonoidHom.coe_mk, OneHom.coe_mk, map_prod, map_pow, map_add, map_one,
      restrictedEval₂_X, hu]

@[simp]
theorem algebraic_char_apply (m : Fin k → ℕ) (u : Oˣ) :
    (algebraic σ r m).char u = ∏ i, σ i u ^ m i :=
  (rfl)

@[simp]
theorem algebraic_expansion (m : Fin k → ℕ) :
    (algebraic σ r m).expansion =
      ∏ i, (1 + ⟨X i, isRestricted_monomial _ (Finsupp.single i 1) 1⟩) ^ m i :=
  (rfl)

end Algebraic

section Comparison

variable [NormOneClass R] [∀ i, Fact (0 < r i)] {I : Ideal O} {hI : I ≤ Ring.jacobson O}
  (hσ : ∀ i x, ‖σ i x‖ ≤ 1) (hσI : ∀ i, ∀ y ∈ I, ‖σ i y‖ ≤ r i) (hr : ∀ i, r i < 1)

/-- **The algebraic weights give the polynomial automorphy factors**: the analytic factor of
`u ↦ ∏ᵢ σᵢ(u) ^ mᵢ` is `∏ᵢ (σᵢ(c) zᵢ + σᵢ(d)) ^ mᵢ`, so its automorphy factor is the weight-`m`
Möbius automorphy factor pulled back along `sigma0ToMoebius : Σ₀(I) → ∏ᵢ moebiusSubmonoid R`. -/
theorem automorphyFactor_algebraic (m : Fin k → ℕ) :
    (algebraic σ r m).automorphyFactor (hI := hI) hσ hσI hr =
      (moebiusAutomorphyFactor R m).comp
        (sigma0ToMoebius σ hσ fun i y hy ↦ (hσI i y hy).trans_lt (hr i)) := by
  refine RestrictedAutomorphyFactor.ext (funext fun γ ↦ funext fun i ↦ ?_) (funext fun γ ↦ ?_)
  · rw [automorphyFactor_subst, RestrictedAutomorphyFactor.comp_subst,
      moebiusAutomorphyFactor_subst, coe_sigma0ToMoebius_apply]
  rw [automorphyFactor_factor, RestrictedAutomorphyFactor.comp_factor,
    moebiusAutomorphyFactor_factor, factor_def, Algebra.smul_def, algebraic_expansion,
    algebraic_char_apply, map_prod, map_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  rw [map_pow, map_pow, map_add, map_one, restrictedAnalyticSubst_X, ← mul_pow]
  congr 1
  have hinv : algebraMap R (IsRestricted.subring (R := R) fun _ : Fin k ↦ (1 : ℝ))
      (σ i ((γ : Matrix (Fin 2) (Fin 2) O) 1 1)) *
        algebraMap R _ (σ i ↑(sigma0LowerRightUnit γ)⁻¹) = 1 := by
    rw [← map_mul, ← map_mul, ← coe_sigma0LowerRightUnit, Units.mul_inv, map_one, map_one]
  simp only [factorArg, moebiusDenom_def, coe_sigma0ToMoebius_apply, RingHom.mapMatrix_apply,
    Matrix.map_apply, coe_sigma0LowerRightUnit, Algebra.smul_def, map_mul]
  linear_combination algebraMap R _ (σ i ((γ : Matrix (Fin 2) (Fin 2) O) 1 0)) *
    (⟨X i, isRestricted_monomial _ (Finsupp.single i 1) 1⟩ :
      IsRestricted.subring (R := R) fun _ : Fin k ↦ (1 : ℝ)) * hinv

end Comparison

end AnalyticWeight

end AnalyticWeight

end TauCeti.MvPowerSeries
