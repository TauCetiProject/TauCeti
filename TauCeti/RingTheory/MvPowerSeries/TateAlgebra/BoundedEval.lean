/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Eval
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Map
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Polynomial

/-!
# Evaluation along bounded coefficient homomorphisms

A coefficient homomorphism `φ : R →+* S` satisfying `‖φ r‖ ≤ C * ‖r‖` need not be
contractive. Nevertheless, restricted series at positive polyradii `c` can be evaluated at
arguments `a i` with `‖a i‖ ≤ c i`, provided `S` is complete and ultrametric. Evaluation has
bound `C` and is the unique continuous ring homomorphism with the prescribed values on
constants and variables.

`RingHom.restrictedEval₂OfBound` first applies the bounded coefficient map
`TauCeti.MvPowerSeries.restrictedMap`, then evaluates over `S` along its identity map using
`MvPowerSeries.restrictedEval₂`. Thus it uses the same convergent monomial sum as contractive
evaluation, and agrees with that evaluation whenever the coefficient map is contractive.
The construction commutes with bounded coefficient maps and continuous maps of target rings.

More generally, `RingHom.restrictedEval₂OfPowBound` evaluates at arguments whose monomials are
bounded by a constant multiple of the monomials in the radii,
`‖∏ i, a i ^ t i‖ ≤ D * ∏ i, c i ^ t i`. Such arguments may have norm larger than the radii, as a
nilpotent element or a root of a monic polynomial with small coefficients may. Evaluation then
has bound `C * D`, and is again the unique continuous ring homomorphism with the prescribed values
on constants and variables. This is the form needed to map the algebra of a polydisc into a
quotient of another one, where the images of the variables are only known to have small spectral
radius.

## References

* Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*, §5.1.
-/

public section

namespace RingHom

open MvPowerSeries
open TauCeti.Huber
open TauCeti.MvPowerSeries (restrictedMap coe_restrictedMap norm_restrictedMap_le
  continuous_restrictedMap polynomialToRestricted restrictedMap_polynomialToRestricted
  denseRange_polynomialToRestricted)

variable {k : ℕ} {R S : Type*} [NormedCommRing R] [IsUltrametricDist R]
  [NormedCommRing S] [IsUltrametricDist S] [CompleteSpace S]
  {c : Fin k → ℝ} (φ : R →+* S) (a : Fin k → S) {C : ℝ}
  (hφ : ∀ r, ‖φ r‖ ≤ C * ‖r‖) (ha : ∀ i, ‖a i‖ ≤ c i)

/-- Evaluate restricted series along a coefficient homomorphism bounded by `C`. The arguments
are bounded by the source polyradii; evaluation increases the Gauss norm by at most `C`. -/
noncomputable def restrictedEval₂OfBound : IsRestricted.subring (R := R) c →+* S :=
  (restrictedEval₂ (RingHom.id S) a (fun _ ↦ le_rfl) ha).comp (restrictedMap φ hφ)

/-- Bounded evaluation is the usual convergent monomial sum. -/
theorem restrictedEval₂OfBound_apply (f : IsRestricted.subring (R := R) c) :
    restrictedEval₂OfBound φ a hφ ha f = weightedEval φ a f := by
  simp only [restrictedEval₂OfBound, RingHom.comp_apply, restrictedEval₂_apply,
    weightedEval_def, coe_restrictedMap, weightedEvalTerm_def, coeff_map, RingHom.id_apply]

/-- The monomial sum converges to bounded evaluation. -/
theorem hasSum_restrictedEval₂OfBound (f : IsRestricted.subring (R := R) c) :
    HasSum (weightedEvalTerm φ a f) (restrictedEval₂OfBound φ a hφ ha f) := by
  have ht : weightedEvalTerm (RingHom.id S) a
      (restrictedMap φ hφ f : MvPowerSeries (Fin k) S) = weightedEvalTerm φ a f := by
    funext t
    simp only [weightedEvalTerm_def, coe_restrictedMap, coeff_map, RingHom.id_apply]
  simpa only [ht, restrictedEval₂OfBound, RingHom.comp_apply] using
    hasSum_restrictedEval₂ (RingHom.id S) a (fun _ ↦ le_rfl) ha (restrictedMap φ hφ f)

/-- Bounded evaluation extends the coefficient map on constants. -/
@[simp]
theorem restrictedEval₂OfBound_algebraMap (r : R) :
    restrictedEval₂OfBound φ a hφ ha (algebraMap R _ r) = φ r := by
  rw [restrictedEval₂OfBound_apply, coe_algebraMap_isRestrictedSubring, weightedEval_C]

/-- Bounded evaluation sends the variable `X i` to the specified argument. -/
@[simp]
theorem restrictedEval₂OfBound_X (i : Fin k) :
    restrictedEval₂OfBound φ a hφ ha ⟨X i, isRestricted_X c i⟩ = a i := by
  rw [restrictedEval₂OfBound_apply, weightedEval_X]

/-- On polynomials, bounded evaluation is polynomial evaluation. -/
@[simp]
theorem restrictedEval₂OfBound_polynomial (p : MvPolynomial (Fin k) R) :
    restrictedEval₂OfBound φ a hφ ha (polynomialToRestricted c p) =
      MvPolynomial.eval₂ φ a p := by
  rw [restrictedEval₂OfBound, RingHom.comp_apply, restrictedMap_polynomialToRestricted,
    TauCeti.MvPowerSeries.polynomialToRestricted_apply, restrictedEval₂_polynomial]
  simp only [MvPolynomial.eval₂_map, RingHom.id_comp]

/-- The bounded construction agrees with contractive evaluation when both apply. -/
theorem restrictedEval₂OfBound_eq_restrictedEval₂ (hφ' : ∀ r, ‖φ r‖ ≤ ‖r‖) :
    restrictedEval₂OfBound φ a hφ ha = restrictedEval₂ φ a hφ' ha := by
  ext f
  rw [restrictedEval₂OfBound_apply, restrictedEval₂_apply]

section PositivePolyradii

variable [∀ i, Fact (0 < c i)]

/-- Evaluation has the same bound as the coefficient homomorphism. No multiplicativity of
coefficient norms, norm-one hypothesis, or completeness of `R` is required. -/
theorem norm_restrictedEval₂OfBound_le (f : IsRestricted.subring (R := R) c) :
    ‖restrictedEval₂OfBound φ a hφ ha f‖ ≤ C * ‖f‖ :=
  (norm_restrictedEval₂_le (RingHom.id S) a (fun _ ↦ le_rfl) ha _).trans
    (norm_restrictedMap_le φ hφ f)

/-- Bounded evaluation is Lipschitz for the Gauss norm topology. -/
theorem lipschitzWith_restrictedEval₂OfBound :
    LipschitzWith (Real.toNNReal C) (restrictedEval₂OfBound φ a hφ ha) :=
  AddMonoidHomClass.lipschitz_of_bound _ C (norm_restrictedEval₂OfBound_le φ a hφ ha)

/-- Bounded evaluation is continuous for the Gauss norm topology. -/
@[continuity]
theorem continuous_restrictedEval₂OfBound : Continuous (restrictedEval₂OfBound φ a hφ ha) :=
  (lipschitzWith_restrictedEval₂OfBound φ a hφ ha).continuous

/-- A continuous homomorphism with the prescribed values on constants and variables is
bounded evaluation. Uniqueness requires continuity, but not a supplied norm bound on the map. -/
theorem eq_restrictedEval₂OfBound (ψ : IsRestricted.subring (R := R) c →+* S)
    (hψ : Continuous ψ) (hC : ∀ r, ψ (algebraMap R _ r) = φ r)
    (hX : ∀ i, ψ ⟨X i, isRestricted_X c i⟩ = a i) :
    ψ = restrictedEval₂OfBound φ a hφ ha := by
  have hp : ψ.comp (polynomialToRestricted c).toRingHom =
      (restrictedEval₂OfBound φ a hφ ha).comp (polynomialToRestricted c).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [← MvPolynomial.algebraMap_eq, hC]
    · intro i
      simpa using (hX i).trans (restrictedEval₂OfBound_X φ a hφ ha i).symm
  exact DFunLike.coe_injective (denseRange_polynomialToRestricted.equalizer hψ
    (continuous_restrictedEval₂OfBound φ a hφ ha) (funext (DFunLike.congr_fun hp)))

include hφ ha in
/-- The universal property at bounded arguments for an arbitrary bounded coefficient map. -/
theorem existsUnique_continuous_ringHom_of_bound :
    ∃! ψ : IsRestricted.subring (R := R) c →+* S,
      Continuous ψ ∧ (∀ r, ψ (algebraMap R _ r) = φ r) ∧
        ∀ i, ψ ⟨X i, isRestricted_X c i⟩ = a i :=
  ⟨restrictedEval₂OfBound φ a hφ ha,
    ⟨continuous_restrictedEval₂OfBound φ a hφ ha,
      restrictedEval₂OfBound_algebraMap φ a hφ ha, restrictedEval₂OfBound_X φ a hφ ha⟩,
    fun ψ ⟨hψ, hC, hX⟩ ↦ eq_restrictedEval₂OfBound φ a hφ ha ψ hψ hC hX⟩

end PositivePolyradii

section Naturality

variable {T : Type*} [NormedCommRing T] [IsUltrametricDist T]

/-- Bounded evaluation commutes with a bounded map of source coefficients. The bound on the
composite may be chosen independently of the bounds used to construct either map. -/
theorem restrictedEval₂OfBound_restrictedMap (θ : T →+* R) {D E : ℝ}
    (hθ : ∀ t, ‖θ t‖ ≤ D * ‖t‖) (hφθ : ∀ t, ‖(φ.comp θ) t‖ ≤ E * ‖t‖)
    (f : IsRestricted.subring (R := T) c) :
    restrictedEval₂OfBound φ a hφ ha (restrictedMap θ hθ f) =
      restrictedEval₂OfBound (φ.comp θ) a hφθ ha f := by
  simp only [restrictedEval₂OfBound_apply, coe_restrictedMap, weightedEval_def,
    weightedEvalTerm_def, coeff_map, RingHom.comp_apply]

/-- Applying a continuous target homomorphism to an evaluated series agrees with evaluating
its images, whenever the composite coefficient map is bounded and the image arguments still
lie in the prescribed polydisc. -/
theorem map_restrictedEval₂OfBound [CompleteSpace T] (θ : S →+* T) (hθ : Continuous θ) {D : ℝ}
    (hθφ : ∀ r, ‖(θ.comp φ) r‖ ≤ D * ‖r‖) (hθa : ∀ i, ‖θ (a i)‖ ≤ c i)
    (f : IsRestricted.subring (R := R) c) :
    θ (restrictedEval₂OfBound φ a hφ ha f) =
      restrictedEval₂OfBound (θ.comp φ) (θ ∘ a) hθφ hθa f := by
  have ht : θ ∘ weightedEvalTerm φ a (f : MvPowerSeries (Fin k) R) =
      weightedEvalTerm (θ.comp φ) (θ ∘ a) f := by
    funext t
    simp only [Function.comp_apply, weightedEvalTerm_def, map_mul, map_prod, map_pow,
      RingHom.comp_apply]
  exact (ht ▸ (hasSum_restrictedEval₂OfBound φ a hφ ha f).map θ hθ).unique
    (hasSum_restrictedEval₂OfBound (θ.comp φ) (θ ∘ a) hθφ hθa f)

end Naturality

section PowerBound

/-! ### Arguments with bounded powers

The arguments need not lie in the polydisc of radii `c` itself: it suffices that their monomials
are bounded by a constant multiple of the corresponding monomials in the radii,
`‖∏ i, a i ^ t i‖ ≤ D * ∏ i, c i ^ t i`. For instance a nilpotent element of large norm can be
substituted for a variable of any radius. -/

omit [IsUltrametricDist S] [CompleteSpace S] in
/-- Coordinatewise bounds `‖a i ^ j‖ ≤ Dᵢ * c i ^ j` on the powers of the arguments give a bound
`‖∏ i, a i ^ t i‖ ≤ D * ∏ i, c i ^ t i` on their monomials, as required by
`RingHom.restrictedEval₂OfPowBound`. -/
theorem _root_.exists_forall_norm_prod_pow_le_mul_prod (hc : ∀ i, 0 ≤ c i)
    (h : ∀ i, ∃ Dᵢ, ∀ j, ‖a i ^ j‖ ≤ Dᵢ * c i ^ j) :
    ∃ D, ∀ t : Fin k →₀ ℕ, ‖∏ i, a i ^ t i‖ ≤ D * t.prod (c · ^ ·) := by
  choose Dᵢ hDᵢ using h
  refine ⟨max ‖(1 : S)‖ (∏ i, Dᵢ i), fun t ↦ ?_⟩
  rw [Finsupp.prod_fintype _ _ fun _ ↦ pow_zero _]
  rcases isEmpty_or_nonempty (Fin k) with hk | hk
  · simp [Finset.univ_eq_empty]
  calc ‖∏ i, a i ^ t i‖ ≤ ∏ i, ‖a i ^ t i‖ := Finset.norm_prod_le' _ Finset.univ_nonempty _
    _ ≤ ∏ i, (Dᵢ i * c i ^ t i) :=
      Finset.prod_le_prod₀ (fun _ _ ↦ norm_nonneg _) fun i _ ↦ hDᵢ i _
    _ = (∏ i, Dᵢ i) * ∏ i, c i ^ t i := Finset.prod_mul_distrib
    _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _)
      (Finset.prod_nonneg fun i _ ↦ pow_nonneg (hc i) _)

variable {D : ℝ} (hpow : ∀ t : Fin k →₀ ℕ, ‖∏ i, a i ^ t i‖ ≤ D * t.prod (c · ^ ·))

omit [IsUltrametricDist R] [IsUltrametricDist S] [CompleteSpace S] in
include hφ hpow in
/-- A monomial value `φ(fₜ) aᵗ` at arguments with bounded powers is bounded by `C * D` times the
weighted coefficient norm `‖fₜ‖ cᵗ`. -/
private theorem norm_weightedEvalTerm_le_of_powBound (f : MvPowerSeries (Fin k) R)
    (t : Fin k →₀ ℕ) :
    ‖weightedEvalTerm φ a f t‖ ≤ C * D * (‖coeff t f‖ * t.prod (c · ^ ·)) := by
  rw [weightedEvalTerm_def]
  calc _ ≤ ‖φ (coeff t f)‖ * ‖∏ i, a i ^ t i‖ := norm_mul_le _ _
    _ ≤ C * ‖coeff t f‖ * (D * t.prod (c · ^ ·)) :=
      mul_le_mul (hφ _) (hpow t) (norm_nonneg _) ((norm_nonneg _).trans (hφ _))
    _ = _ := by ring

omit [IsUltrametricDist R] in
include hφ hpow in
/-- The monomial values of a restricted series at arguments with bounded powers are summable. -/
theorem _root_.MvPowerSeries.IsRestricted.summable_weightedEvalTerm_of_powBound
    {f : MvPowerSeries (Fin k) R} (hf : IsRestricted c f) : Summable (weightedEvalTerm φ a f) := by
  refine NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
    (squeeze_zero_norm (norm_weightedEvalTerm_le_of_powBound φ a hφ hpow f) ?_)
  simpa using hf.const_mul (C * D)

/-- **Evaluation at arguments with bounded powers.** For a coefficient homomorphism `φ` bounded by
`C` and arguments whose monomials satisfy `‖∏ i, a i ^ t i‖ ≤ D * ∏ i, c i ^ t i`, the ring
homomorphism `R{X/c} → S` sending `f = ∑ₜ fₜ Xᵗ` to `f(a) = ∑ₜ φ(fₜ) aᵗ`. -/
noncomputable def restrictedEval₂OfPowBound : IsRestricted.subring (R := R) c →+* S where
  toFun f := weightedEval φ a f
  map_one' := by simpa using weightedEval_C φ a 1
  map_mul' f g := by
    -- the ultrametric norm makes `S` a nonarchimedean ring, for the summability of products
    have : NonarchimedeanRing S :=
      { toIsTopologicalRing := inferInstance
        is_nonarchimedean := NonarchimedeanAddGroup.is_nonarchimedean }
    have hf := f.property.summable_weightedEvalTerm_of_powBound φ a hφ hpow
    have hg := g.property.summable_weightedEvalTerm_of_powBound φ a hφ hpow
    exact weightedEval_mul_of_summable hf hg (hf.mul_of_nonarchimedean hg)
  map_zero' := weightedEval_zero φ a
  map_add' f g := weightedEval_add_of_summable
    (f.property.summable_weightedEvalTerm_of_powBound φ a hφ hpow)
    (g.property.summable_weightedEvalTerm_of_powBound φ a hφ hpow)

/-- Evaluation at arguments with bounded powers is the usual convergent monomial sum. -/
theorem restrictedEval₂OfPowBound_apply (f : IsRestricted.subring (R := R) c) :
    restrictedEval₂OfPowBound φ a hφ hpow f = weightedEval φ a f :=
  (rfl)

/-- The monomial sum converges to the evaluation at arguments with bounded powers. -/
theorem hasSum_restrictedEval₂OfPowBound (f : IsRestricted.subring (R := R) c) :
    HasSum (weightedEvalTerm φ a f) (restrictedEval₂OfPowBound φ a hφ hpow f) := by
  rw [restrictedEval₂OfPowBound_apply, weightedEval_def]
  exact (f.property.summable_weightedEvalTerm_of_powBound φ a hφ hpow).hasSum

/-- Evaluation at arguments with bounded powers extends the coefficient map on constants. -/
@[simp]
theorem restrictedEval₂OfPowBound_algebraMap (r : R) :
    restrictedEval₂OfPowBound φ a hφ hpow (algebraMap R _ r) = φ r := by
  rw [restrictedEval₂OfPowBound_apply, coe_algebraMap_isRestrictedSubring, weightedEval_C]

/-- Evaluation at arguments with bounded powers sends the variable `X i` to `a i`. -/
@[simp]
theorem restrictedEval₂OfPowBound_X (i : Fin k) :
    restrictedEval₂OfPowBound φ a hφ hpow ⟨X i, isRestricted_X c i⟩ = a i := by
  rw [restrictedEval₂OfPowBound_apply, weightedEval_X]

/-- On polynomials, evaluation at arguments with bounded powers is polynomial evaluation. -/
@[simp]
theorem restrictedEval₂OfPowBound_polynomial (p : MvPolynomial (Fin k) R) :
    restrictedEval₂OfPowBound φ a hφ hpow (polynomialToRestricted c p) =
      MvPolynomial.eval₂ φ a p := by
  rw [← MvPolynomial.coe_eval₂Hom]
  refine DFunLike.congr_fun (MvPolynomial.ringHom_ext
    (f := (restrictedEval₂OfPowBound φ a hφ hpow).comp (polynomialToRestricted c).toRingHom)
    (fun r ↦ ?_) fun i ↦ ?_) p
  · simp [← MvPolynomial.algebraMap_eq]
  · simp [TauCeti.MvPowerSeries.polynomialToRestricted_X]

/-- When the arguments lie in the polydisc of radii `c`, the evaluation at arguments with bounded
powers is the bounded evaluation `restrictedEval₂OfBound`. -/
theorem restrictedEval₂OfPowBound_eq_restrictedEval₂OfBound :
    restrictedEval₂OfPowBound φ a hφ hpow = restrictedEval₂OfBound φ a hφ ha := by
  ext f
  rw [restrictedEval₂OfPowBound_apply, restrictedEval₂OfBound_apply]

variable [∀ i, Fact (0 < c i)]

/-- Evaluation at arguments with bounded powers increases the Gauss norm by at most `C * D`. -/
theorem norm_restrictedEval₂OfPowBound_le (hC : 0 ≤ C) (f : IsRestricted.subring (R := R) c) :
    ‖restrictedEval₂OfPowBound φ a hφ hpow f‖ ≤ C * D * ‖f‖ := by
  -- the constant monomial gives `‖1‖ ≤ D`, so `D` is nonnegative
  have hD : 0 ≤ D := by simpa using (norm_nonneg _).trans (hpow 0)
  rw [restrictedEval₂OfPowBound_apply, weightedEval_def]
  exact IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (by positivity) fun t ↦
    (norm_weightedEvalTerm_le_of_powBound φ a hφ hpow _ t).trans
      (mul_le_mul_of_nonneg_left (norm_coeff_mul_prod_le f t) (mul_nonneg hC hD))

/-- Evaluation at arguments with bounded powers is continuous for the Gauss norm. -/
theorem continuous_restrictedEval₂OfPowBound (hC : 0 ≤ C) :
    Continuous (restrictedEval₂OfPowBound φ a hφ hpow) :=
  AddMonoidHomClass.continuous_of_bound _ (C * D)
    (norm_restrictedEval₂OfPowBound_le φ a hφ hpow hC)

/-- A continuous homomorphism with the prescribed values on constants and variables is the
evaluation at arguments with bounded powers. -/
theorem eq_restrictedEval₂OfPowBound (hC : 0 ≤ C) (ψ : IsRestricted.subring (R := R) c →+* S)
    (hψ : Continuous ψ) (hC' : ∀ r, ψ (algebraMap R _ r) = φ r)
    (hX : ∀ i, ψ ⟨X i, isRestricted_X c i⟩ = a i) :
    ψ = restrictedEval₂OfPowBound φ a hφ hpow := by
  have hp : ψ.comp (polynomialToRestricted c).toRingHom =
      (restrictedEval₂OfPowBound φ a hφ hpow).comp (polynomialToRestricted c).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [← MvPolynomial.algebraMap_eq, hC']
    · intro i
      simpa using (hX i).trans (restrictedEval₂OfPowBound_X φ a hφ hpow i).symm
  exact DFunLike.coe_injective (denseRange_polynomialToRestricted.equalizer hψ
    (continuous_restrictedEval₂OfPowBound φ a hφ hpow hC) (funext (DFunLike.congr_fun hp)))

end PowerBound

end RingHom
