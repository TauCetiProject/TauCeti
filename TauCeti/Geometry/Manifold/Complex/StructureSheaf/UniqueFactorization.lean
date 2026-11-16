/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Complex.StructureSheaf.SmoothComparison
public import TauCeti.Geometry.Manifold.Complex.StructureSheaf.Weierstrass
public import TauCeti.RingTheory.Polynomial.Rueckert

import TauCeti.Analysis.Analytic.Uniqueness
import TauCeti.Geometry.Manifold.Complex.Analytic
import TauCeti.Geometry.Manifold.Complex.StructureSheaf.Domain
import TauCeti.Geometry.Manifold.Complex.StructureSheaf.StalkPullback
import TauCeti.RingTheory.Polynomial.Distinguished

/-!
# Holomorphic stalks are unique factorization domains

The ring `𝒪_{X, x}` of germs of holomorphic functions at a point of a finite-dimensional complex
manifold without boundary is a unique factorization domain (`stalkUniqueFactorizationMonoid`), and
so is the stalk of Mathlib's complex-smooth structure sheaf (`smoothStalkUniqueFactorizationMonoid`)
via `smoothStalkIso`.

In a chart this is the ring of convergent power series in `n` variables, proved factorial by
induction on `n` through Weierstrass preparation and Rückert's descent principle
(`RingHom.IsRueckert`). On `E × ℂ`, the vertical evaluation map
`evalVertical x₀ w₀ : (𝒪_{E, x₀})[X] →+* 𝒪_{E × ℂ, (x₀, w₀)}` satisfies `RingHom.IsRueckert` for
the set of polynomials distinguished at the maximal ideal of `𝒪_{E, x₀}`
(`isRueckert_evalVertical`):

* `evalVertical x₀ w₀` is injective (`evalVertical_injective`);
* monic divisors of distinguished polynomials at a radical ideal are distinguished
  (`Polynomial.IsDistinguishedAt.of_dvd`);
* Weierstrass division gives the divisibility reflection and remainder representation modulo any
  distinguished polynomial (`evalVertical_dvd_iff_of_isDistinguishedAt`,
  `existsUnique_weierstrassDivision_of_isDistinguishedAt`);
* every nonzero germ at `(x₀, w₀)` becomes regular in the vertical variable after a centered
  affine change of coordinates (`AnalyticAt.exists_continuousLinearEquiv_analyticOrderAt_ne_top`,
  `stalkPullback_bijective`), and Weierstrass preparation (`existsUnique_weierstrassPreparation`)
  then makes it a unit multiple of the image of a distinguished polynomial.

Factorial descent (`RingHom.IsRueckert.uniqueFactorizationMonoid`) passes unique factorization
from `𝒪_{E, x₀}` to `𝒪_{E × ℂ, (x₀, w₀)}`, with the zero-dimensional base case `Fin 0 → ℂ`
identified with `ℂ` by evaluation. Charts and `smoothStalkIso` transport the result to every
finite-dimensional boundaryless complex manifold.

We also record the Weierstrass–Gauss factorization comparisons for a distinguished polynomial
`P ∈ (𝒪_{E, x₀})[X]`: units, divisors, primality, irreducibility, and relative primality with an
arbitrary polynomial `Q ∈ (𝒪_{E, x₀})[X]` all agree in `(𝒪_{E, x₀})[X]` and in
`𝒪_{E × ℂ, (x₀, w₀)}`.

## Main declarations

* `TauCeti.holomorphicStructureSheaf.isRueckert_evalVertical`: `evalVertical x₀ w₀` satisfies the
  Rückert hypotheses for distinguished polynomials at the maximal ideal of `𝒪_{E, x₀}`.
* `TauCeti.holomorphicStructureSheaf.stalkUniqueFactorizationMonoid`: holomorphic stalks are
  unique factorization domains.
* `TauCeti.holomorphicStructureSheaf.smoothStalkUniqueFactorizationMonoid`: stalks of Mathlib's
  complex-smooth structure sheaf are unique factorization domains.
* `TauCeti.holomorphicStructureSheaf.isUnit_evalVertical_iff_of_isDistinguishedAt`,
  `TauCeti.holomorphicStructureSheaf.map_residue_verticalPowerSeries_ne_zero_of_dvd`,
  `TauCeti.holomorphicStructureSheaf.existsUnique_isDistinguishedAt_dvd_of_dvd_evalVertical`,
  `TauCeti.holomorphicStructureSheaf.isPrime_span_evalVertical_iff_of_isDistinguishedAt`,
  `TauCeti.holomorphicStructureSheaf.prime_evalVertical_iff_of_isDistinguishedAt`,
  `TauCeti.holomorphicStructureSheaf.irreducible_evalVertical_iff_of_isDistinguishedAt`,
  `TauCeti.holomorphicStructureSheaf.isRelPrime_evalVertical_iff_of_isDistinguishedAt`:
  comparison of units, divisors, primality, irreducibility, and relative primality for
  distinguished polynomials.

## References

* J.-P. Demailly, *Complex Analytic and Differential Geometry*, Chapter II, (2.9)–(2.10).
* R. C. Gunning and H. Rossi, *Analytic Functions of Several Complex Variables*, Ch. II, §B.
* L. Hörmander, *An Introduction to Complex Analysis in Several Variables*, §6.1.
* H. Grauert and R. Remmert, *Coherent Analytic Sheaves*, Ch. 2, §2.
* S. Bosch, U. Güntzer and R. Remmert, *Non-Archimedean Analysis*, §5.2.5.
-/

public noncomputable section

open Filter Module Polynomial Topology
open scoped ContDiff Manifold

namespace TauCeti.holomorphicStructureSheaf

/-! ### Rückert hypotheses for vertical polynomial evaluation -/

section Rueckert

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- **Holomorphic stalks satisfy the Rückert hypotheses.** On `E × ℂ` with `E` finite-dimensional,
vertical evaluation `evalVertical x₀ w₀ : (𝒪_{E, x₀})[X] →+* 𝒪_{E × ℂ, (x₀, w₀)}` satisfies
`RingHom.IsRueckert` for the set of polynomials distinguished at the maximal ideal of `𝒪_{E, x₀}`.
-/
theorem isRueckert_evalVertical [FiniteDimensional ℂ E] (x₀ : E) (w₀ : ℂ) :
    (evalVertical x₀ w₀).IsRueckert
      {P | P.IsDistinguishedAt
        (IsLocalRing.maximalIdeal ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀))} where
  injective := evalVertical_injective x₀ w₀
  monic hw := hw.monic
  mem_of_dvd hw hp hpw :=
    hw.of_dvd (IsLocalRing.maximalIdeal.isMaximal _).isPrime.isRadical hp hpw
  dvd_iff hw p := (evalVertical_dvd_iff_of_isDistinguishedAt hw).symm
  exists_dvd_sub {w} hw b := by
    obtain ⟨⟨q, r⟩, ⟨_, hb⟩, _⟩ := existsUnique_weierstrassDivision_of_isDistinguishedAt hw b
    exact ⟨r, q, by rw [hb, add_sub_cancel_right]⟩
  exists_mul_eq {b} hb := by
    obtain ⟨F, hF, hbF⟩ := exists_analyticAt_toFilterGerm_eq (x₀, w₀) b
    obtain ⟨L, q, hLq, hslice⟩ := hF.exists_continuousLinearEquiv_analyticOrderAt_ne_top
      ((eq_zero_iff_of_toFilterGerm_eq (hbF _ le_rfl)).not.1 hb)
    -- Center `L` at `(x₀, w₀)` so pullback is an automorphism of the stalk.
    let φ : E × ℂ → E × ℂ := fun p ↦ (x₀, w₀) + L (p - (x₀, w₀))
    let ψ : E × ℂ → E × ℂ := fun p ↦ (x₀, w₀) + L.symm (p - (x₀, w₀))
    have hφ : ContMDiff 𝓘(ℂ, E × ℂ) 𝓘(ℂ, E × ℂ) ω φ :=
      contMDiff_iff_contDiff.2
        (contDiff_const.add (L.contDiff.comp (contDiff_id.sub contDiff_const)))
    have hψ : ContMDiff 𝓘(ℂ, E × ℂ) 𝓘(ℂ, E × ℂ) ω ψ :=
      contMDiff_iff_contDiff.2
        (contDiff_const.add (L.symm.contDiff.comp (contDiff_id.sub contDiff_const)))
    obtain ⟨α, hαb⟩ : ∃ α :
        (holomorphicStructureSheaf 𝓘(ℂ, E × ℂ) (E × ℂ)).presheaf.stalk (x₀, w₀) ≃+*
          (holomorphicStructureSheaf 𝓘(ℂ, E × ℂ) (E × ℂ)).presheaf.stalk (x₀, w₀),
        toFilterGerm 𝓘(ℂ, E × ℂ) (E × ℂ) (x₀, w₀) (𝓝 (x₀, w₀)) le_rfl (α b) = ↑(F ∘ φ) := by
      have haux : ∀ {p : E × ℂ} (_ : φ (x₀, w₀) = p)
          (s : (holomorphicStructureSheaf 𝓘(ℂ, E × ℂ) (E × ℂ)).presheaf.stalk p),
          toFilterGerm 𝓘(ℂ, E × ℂ) (E × ℂ) p (𝓝 p) le_rfl s = ↑F →
          ∃ α : (holomorphicStructureSheaf 𝓘(ℂ, E × ℂ) (E × ℂ)).presheaf.stalk p ≃+*
              (holomorphicStructureSheaf 𝓘(ℂ, E × ℂ) (E × ℂ)).presheaf.stalk (x₀, w₀),
            toFilterGerm 𝓘(ℂ, E × ℂ) (E × ℂ) (x₀, w₀) (𝓝 (x₀, w₀)) le_rfl (α s) = ↑(F ∘ φ) := by
        rintro _ rfl s hs
        refine ⟨RingEquiv.ofBijective
          (stalkPullback (Eventually.of_forall fun _ ↦ hφ.contMDiffAt))
          (stalkPullback_bijective _ (Eventually.of_forall fun _ ↦ hψ.contMDiffAt)
            (Eventually.of_forall fun p ↦ by simp [φ, ψ])
            (Eventually.of_forall fun p ↦ by simp [φ, ψ])), ?_⟩
        rw [RingEquiv.ofBijective_apply, toFilterGerm_stalkPullback, hs, Germ.coe_compTendsto]
      exact haux (by simp [φ]) b (hbF _ le_rfl)
    -- The vertical slice of `F ∘ φ` at `(x₀, w₀)` translates the nonvanishing slice of `F ∘ L`.
    have hslice' : analyticOrderAt (fun w ↦ (F ∘ φ) (x₀, w)) w₀ ≠ ⊤ := by
      rw [Ne, analyticOrderAt_eq_top]
      intro h0
      refine analyticOrderAt_eq_top.not.1 hslice ?_
      have ht : Tendsto (fun t : ℂ ↦ t + (w₀ - q.2)) (𝓝 q.2) (𝓝 w₀) := by
        have : Continuous fun t : ℂ ↦ t + (w₀ - q.2) := by fun_prop
        simpa using this.tendsto q.2
      filter_upwards [ht.eventually h0] with t ht0
      have hφt : φ (x₀, t + (w₀ - q.2)) = L (q.1, t) := by
        have hsub : ((x₀, t + (w₀ - q.2)) : E × ℂ) - (x₀, w₀) = (0, t - q.2) := by
          ext
          · exact sub_self x₀
          · simp only [Prod.snd_sub]; ring
        dsimp only [φ]
        rw [hsub, ← hLq, ← L.map_add]
        congr 1
        ext
        · simp
        · simp only [Prod.snd_add]; ring
      simpa only [Function.comp_apply, hφt] using ht0
    obtain ⟨⟨P, u⟩, ⟨hP, hu, hfac⟩, _⟩ := existsUnique_weierstrassPreparation
      ((map_residue_verticalPowerSeries_ne_zero_iff hαb).2 hslice')
    obtain ⟨u₀, hu₀⟩ := hu
    refine ⟨α, u₀⁻¹, P, hP, ?_⟩
    rw [hfac, ← hu₀, mul_comm (evalVertical x₀ w₀ P), ← mul_assoc, Units.inv_mul, one_mul]

end Rueckert

/-! ### Unique factorization on holomorphic stalks -/

section Induction

/-- Holomorphic stalks of `Fin n → ℂ` are unique factorization domains, by induction on `n` via
Rückert's factorial descent. -/
private theorem uniqueFactorizationMonoid_stalk_fin :
    ∀ (n : ℕ) (x : Fin n → ℂ),
      UniqueFactorizationMonoid
        ((holomorphicStructureSheaf 𝓘(ℂ, Fin n → ℂ) (Fin n → ℂ)).presheaf.stalk x)
  | 0, x => by
    refine (RingEquiv.ofBijective (eval 𝓘(ℂ, Fin 0 → ℂ) (Fin 0 → ℂ) x)
      ⟨(injective_iff_map_eq_zero _).2 fun s hs ↦ ?_, eval_surjective _ _ x⟩).symm.toMulEquiv
      |>.uniqueFactorizationMonoid inferInstance
    obtain ⟨φ, -, hφ⟩ := exists_toFilterGerm_eq x s
    refine (eq_zero_iff_of_toFilterGerm_eq (hφ _ le_rfl)).2 (Eventually.of_forall fun y ↦ ?_)
    rw [Subsingleton.elim y x, ← eval_eq_of_toFilterGerm_eq (hφ _ le_rfl), hs, Pi.zero_apply]
  | n + 1, x => by
    let e : (Fin (n + 1) → ℂ) ≃L[ℂ] (Fin n → ℂ) × ℂ :=
      ContinuousLinearEquiv.ofFinrankEq (by simp)
    have : UniqueFactorizationMonoid
        ((holomorphicStructureSheaf 𝓘(ℂ, Fin n → ℂ) (Fin n → ℂ)).presheaf.stalk (e x).1) :=
      uniqueFactorizationMonoid_stalk_fin n (e x).1
    have hprod : UniqueFactorizationMonoid
        ((holomorphicStructureSheaf 𝓘(ℂ, (Fin n → ℂ) × ℂ) ((Fin n → ℂ) × ℂ)).presheaf.stalk
          (e x)) :=
      (isRueckert_evalVertical (e x).1 (e x).2).uniqueFactorizationMonoid
    exact (RingEquiv.ofBijective _ (e.holomorphicStalkPullback_bijective x)).toMulEquiv
      |>.uniqueFactorizationMonoid hprod

end Induction

section Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℂ E H} [I.Boundaryless]
  {X : Type} [TopologicalSpace X] [ChartedSpace H X] [IsManifold I 1 X]

/-- **Holomorphic stalks are unique factorization domains.** The stalk of holomorphic functions at
any point of a finite-dimensional complex manifold without boundary is a unique factorization
domain. -/
instance stalkUniqueFactorizationMonoid (x : X) :
    UniqueFactorizationMonoid ((holomorphicStructureSheaf I X).presheaf.stalk x) := by
  let : IsManifold I ω X := IsManifold.of_ne_zero ω one_ne_zero inferInstance
  -- Compose the chart at `x` with a linear isomorphism onto `Fin (finrank ℂ E) → ℂ` in `Type`.
  let e : E ≃L[ℂ] (Fin (finrank ℂ E) → ℂ) := ContinuousLinearEquiv.ofFinrankEq (by simp)
  have hE' := uniqueFactorizationMonoid_stalk_fin (finrank ℂ E) ((e ∘ extChartAt I x) x)
  exact (RingEquiv.ofBijective _ (stalkPullback_comp_extChartAt_bijective x e)).toMulEquiv
    |>.uniqueFactorizationMonoid hE'

/-- A stalk of Mathlib's complex-smooth structure sheaf on a finite-dimensional complex manifold
without boundary is a unique factorization domain, via its comparison with holomorphic germs. -/
instance smoothStalkUniqueFactorizationMonoid (x : X) :
    UniqueFactorizationMonoid ((smoothSheafCommRing I 𝓘(ℂ) X ℂ).presheaf.stalk x) :=
  (smoothStalkIso I X x).commRingCatIsoToRingEquiv.toMulEquiv.uniqueFactorizationMonoid
    (stalkUniqueFactorizationMonoid x)

end Manifold

/-! ### Factorization of distinguished polynomials -/

section DistinguishedFactorization

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- A distinguished polynomial `P` over `𝒪_{E, x₀}` maps to a unit in `𝒪_{E × ℂ, (x₀, w₀)}` if and
only if `P` is already a unit in `(𝒪_{E, x₀})[X]` (equivalently `P = 1`). No finite-dimensionality
assumption is required. -/
theorem isUnit_evalVertical_iff_of_isDistinguishedAt {x₀ : E} {w₀ : ℂ}
    {P : ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀)[X]}
    (hP : P.IsDistinguishedAt
      (IsLocalRing.maximalIdeal ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀))) :
    IsUnit (evalVertical x₀ w₀ P) ↔ IsUnit P := by
  rw [isUnit_stalk_iff, eval_evalVertical,
    hP.isUnit_iff_coeff_zero_notMem (IsLocalRing.maximalIdeal.isMaximal _).ne_top,
    maximalIdeal_stalk, RingHom.mem_ker]

/-- Any divisor in `𝒪_{E × ℂ, (x₀, w₀)}` of a germ whose vertical power series has nonzero
residue-field reduction also has nonzero residue-field vertical power series. No
finite-dimensionality assumption is required. -/
theorem map_residue_verticalPowerSeries_ne_zero_of_dvd {x₀ : E} {w₀ : ℂ}
    {f g : (holomorphicStructureSheaf 𝓘(ℂ, E × ℂ) (E × ℂ)).presheaf.stalk (x₀, w₀)}
    (hf : (verticalPowerSeries x₀ w₀ f).map
      (IsLocalRing.residue ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀)) ≠ 0)
    (hg : g ∣ f) :
    (verticalPowerSeries x₀ w₀ g).map
      (IsLocalRing.residue ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀)) ≠ 0 := by
  intro h0
  obtain ⟨q, rfl⟩ := hg
  exact hf (by rw [map_mul, map_mul, h0, zero_mul])

variable [FiniteDimensional ℂ E]

/-- Every divisor `g ∈ 𝒪_{E × ℂ, (x₀, w₀)}` of `evalVertical x₀ w₀ P`, for a distinguished
polynomial `P`, admits a unique factorization `g = evalVertical x₀ w₀ R * u` with `R`
distinguished, `u` a unit, and `R ∣ P` in `(𝒪_{E, x₀})[X]`. -/
theorem existsUnique_isDistinguishedAt_dvd_of_dvd_evalVertical {x₀ : E} {w₀ : ℂ}
    {P : ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀)[X]}
    (hP : P.IsDistinguishedAt
      (IsLocalRing.maximalIdeal ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀)))
    {g : (holomorphicStructureSheaf 𝓘(ℂ, E × ℂ) (E × ℂ)).presheaf.stalk (x₀, w₀)}
    (hg : g ∣ evalVertical x₀ w₀ P) :
    ∃! Ru : ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀)[X] ×
        (holomorphicStructureSheaf 𝓘(ℂ, E × ℂ) (E × ℂ)).presheaf.stalk (x₀, w₀),
      Ru.1.IsDistinguishedAt
          (IsLocalRing.maximalIdeal ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀)) ∧
        IsUnit Ru.2 ∧ Ru.1 ∣ P ∧ g = evalVertical x₀ w₀ Ru.1 * Ru.2 := by
  obtain ⟨⟨R, u⟩, ⟨hR, hu, hfac⟩, huniq⟩ := existsUnique_weierstrassPreparation
    (map_residue_verticalPowerSeries_ne_zero_of_dvd
      (map_residue_verticalPowerSeries_evalVertical_ne_zero_of_isDistinguishedAt hP) hg)
  have hRP : R ∣ P := (evalVertical_dvd_iff_of_isDistinguishedAt hR).2 <|
    dvd_trans ⟨u, hfac⟩ hg
  exact ⟨(R, u), ⟨hR, hu, hRP, hfac⟩, fun Ru' ⟨hR', hu', _, hfac'⟩ ↦ huniq Ru' ⟨hR', hu', hfac'⟩⟩

/-- A distinguished polynomial `P ∈ (𝒪_{E, x₀})[X]` generates a prime ideal of `𝒪_{E × ℂ, (x₀, w₀)}`
if and only if it generates a prime ideal of `(𝒪_{E, x₀})[X]`. -/
theorem isPrime_span_evalVertical_iff_of_isDistinguishedAt {x₀ : E} {w₀ : ℂ}
    {P : ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀)[X]}
    (hP : P.IsDistinguishedAt
      (IsLocalRing.maximalIdeal ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀))) :
    (Ideal.span {evalVertical x₀ w₀ P}).IsPrime ↔ (Ideal.span {P}).IsPrime := by
  rw [← Ideal.Quotient.isDomain_iff_prime, ← Ideal.Quotient.isDomain_iff_prime]
  exact (quotientEquivOfIsDistinguishedAt x₀ w₀ hP).toMulEquiv.isDomain_iff.symm

/-- A distinguished polynomial `P ∈ (𝒪_{E, x₀})[X]` is prime in `𝒪_{E × ℂ, (x₀, w₀)}` if and only if
it is prime in `(𝒪_{E, x₀})[X]`. -/
theorem prime_evalVertical_iff_of_isDistinguishedAt {x₀ : E} {w₀ : ℂ}
    {P : ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀)[X]}
    (hP : P.IsDistinguishedAt
      (IsLocalRing.maximalIdeal ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀))) :
    Prime (evalVertical x₀ w₀ P) ↔ Prime P := by
  have hP0 : P ≠ 0 := hP.monic.ne_zero
  have hev0 : evalVertical x₀ w₀ P ≠ 0 :=
    (map_ne_zero_iff _ (evalVertical_injective x₀ w₀)).2 hP0
  rw [← Ideal.span_singleton_prime hev0, ← Ideal.span_singleton_prime hP0,
    isPrime_span_evalVertical_iff_of_isDistinguishedAt hP]

/-- **Weierstrass–Gauss irreducibility comparison.** A distinguished polynomial `P ∈ (𝒪_{E, x₀})[X]`
is irreducible in `𝒪_{E × ℂ, (x₀, w₀)}` if and only if it is irreducible in `(𝒪_{E, x₀})[X]`. -/
theorem irreducible_evalVertical_iff_of_isDistinguishedAt {x₀ : E} {w₀ : ℂ}
    {P : ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀)[X]}
    (hP : P.IsDistinguishedAt
      (IsLocalRing.maximalIdeal ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀))) :
    Irreducible (evalVertical x₀ w₀ P) ↔ Irreducible P := by
  rw [UniqueFactorizationMonoid.irreducible_iff_prime,
    UniqueFactorizationMonoid.irreducible_iff_prime,
    prime_evalVertical_iff_of_isDistinguishedAt hP]

/-- **Relative primality comparison for a distinguished polynomial.** If `P ∈ (𝒪_{E, x₀})[X]` is
distinguished at the maximal ideal and `Q ∈ (𝒪_{E, x₀})[X]` is any polynomial, then
`evalVertical x₀ w₀ P` and `evalVertical x₀ w₀ Q` are relatively prime in `𝒪_{E × ℂ, (x₀, w₀)}` if
and only if `P` and `Q` are relatively prime in `(𝒪_{E, x₀})[X]`. -/
theorem isRelPrime_evalVertical_iff_of_isDistinguishedAt {x₀ : E} {w₀ : ℂ}
    {P : ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀)[X]}
    (hP : P.IsDistinguishedAt
      (IsLocalRing.maximalIdeal ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀)))
    (Q : ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀)[X]) :
    IsRelPrime (evalVertical x₀ w₀ P) (evalVertical x₀ w₀ Q) ↔ IsRelPrime P Q := by
  refine ⟨fun hrel d hdP hdQ ↦ ?_, fun hrel g hgP hgQ ↦ ?_⟩
  · -- Any divisor of `P` in `(𝒪_{E, x₀})[X]` is a unit-constant multiple of a distinguished one.
    obtain ⟨u, R, hR, rfl⟩ := hP.exists_C_mul_isDistinguishedAt_of_dvd
      (IsLocalRing.maximalIdeal.isMaximal _).isPrime.isRadical hdP
    have hunit : IsUnit (evalVertical x₀ w₀ (C u.val * R)) :=
      hrel (map_dvd (evalVertical x₀ w₀) hdP) (map_dvd (evalVertical x₀ w₀) hdQ)
    have hRunit : IsUnit (evalVertical x₀ w₀ R) := by
      rw [map_mul] at hunit
      exact isUnit_of_mul_isUnit_right hunit
    exact (u.isUnit.map C).mul ((isUnit_evalVertical_iff_of_isDistinguishedAt hR).1 hRunit)
  · -- Any divisor of `evalVertical P` admits a Weierstrass preparation by a distinguished `R ∣ P`.
    obtain ⟨⟨R, u⟩, ⟨hR, hu, hRP, rfl⟩, _⟩ :=
      existsUnique_isDistinguishedAt_dvd_of_dvd_evalVertical hP hgP
    have hRQ : R ∣ Q := (evalVertical_dvd_iff_of_isDistinguishedAt hR).2 <|
      dvd_trans (dvd_mul_right _ u) hgQ
    exact ((isUnit_evalVertical_iff_of_isDistinguishedAt hR).2 (hrel hRP hRQ)).mul hu

end DistinguishedFactorization

end TauCeti.holomorphicStructureSheaf
