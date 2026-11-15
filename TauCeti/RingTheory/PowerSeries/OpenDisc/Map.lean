/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.PowerSeries.Map
public import TauCeti.RingTheory.PowerSeries.OpenDisc.AnalyticSubst
public import TauCeti.RingTheory.PowerSeries.OpenDisc.Taylor

/-!
# Bounded coefficient maps on power series on an open disc

A bounded ring homomorphism `φ : R →+* S` between normed rings (`‖φ x‖ ≤ C * ‖x‖`) carries power
series on the open disc of radius `R₀` over `R` coefficientwise to power series on the open disc of
the same radius over `S`, giving a ring homomorphism
`TauCeti.PowerSeries.OnOpenDisc.mapHom`. Neither commutativity nor an ultrametric norm is needed
for the ring homomorphism or for lifting along strict surjections: if every `s ∈ S` lifts along
`φ` to some `r ∈ R` with `‖r‖ ≤ C' * ‖s‖`, then `mapHom` is surjective, with a coefficientwise
norm-controlled lift.

Over ultrametric rings, `mapHom` satisfies the bound
`‖restrict r (mapHom φ hφ f)‖ ≤ C * ‖restrict r f‖` on every smaller positive closed disc, so it is
uniformly continuous for the open-disc Gauss uniformities, and is a uniform embedding when `φ`
preserves norms. Over complete commutative ultrametric rings it commutes with point evaluation,
Taylor translation, and analytic substitution.

## Main definitions

* `TauCeti.PowerSeries.OnOpenDisc.mapHom`: the coefficientwise ring homomorphism on open-disc
  power series induced by a bounded ring homomorphism on the coefficients.

## Main results

* `TauCeti.PowerSeries.OnOpenDisc.mapHom_injective_iff` and
  `TauCeti.PowerSeries.OnOpenDisc.mapHom_surjective`: injectivity characterization and surjectivity
  along strict surjections.
* `TauCeti.PowerSeries.OnOpenDisc.norm_restrict_mapHom_le`,
  `TauCeti.PowerSeries.OnOpenDisc.uniformContinuous_mapHom`, and
  `TauCeti.PowerSeries.OnOpenDisc.isUniformEmbedding_mapHom`: closed-disc Gauss bounds, uniform
  continuity, and uniform embeddings from norm-preserving maps.
* `TauCeti.PowerSeries.OnOpenDisc.evalAt_mapHom`, `TauCeti.PowerSeries.OnOpenDisc.mapHom_taylorHom`,
  and `TauCeti.PowerSeries.OnOpenDisc.mapHom_analyticSubst`: compatibility with point evaluation,
  Taylor translation, and analytic substitution.

## References

* P. Colmez, *Fonctions d'une variable p-adique*, Astérisque 330 (2010), §I.4.
* S. Bosch, U. Güntzer and R. Remmert, *Non-Archimedean Analysis*, Grundlehren 261, §5.1.
-/

public section

open Filter PowerSeries
open scoped Topology

namespace TauCeti.PowerSeries.OnOpenDisc

section NormedRing

variable {R S : Type*} [NormedRing R] [NormedRing S] {R₀ : ℝ}
  (φ : R →+* S) {C : ℝ} (hφ : ∀ x, ‖φ x‖ ≤ C * ‖x‖)

/-- **Bounded coefficient map on an open disc.** A ring homomorphism `φ : R →+* S` satisfying
`‖φ x‖ ≤ C * ‖x‖` induces a coefficientwise ring homomorphism on series on the open disc of
radius `R₀`. -/
noncomputable def mapHom : OnOpenDisc.subring R R₀ →+* OnOpenDisc.subring S R₀ :=
  ((PowerSeries.map φ).comp (OnOpenDisc.subring R R₀).subtype).codRestrict _ fun f ↦
    OnOpenDisc.mem_subring.mpr ((OnOpenDisc.mem_subring.mp f.2).map φ hφ)

/-- `mapHom` acts by `PowerSeries.map` on the underlying formal power series. -/
@[simp]
theorem coe_mapHom (f : OnOpenDisc.subring R R₀) :
    (mapHom φ hφ f : S⟦X⟧) = PowerSeries.map φ (f : R⟦X⟧) := (rfl)

/-- `mapHom` applies `φ` to each coefficient. -/
theorem coeff_mapHom (f : OnOpenDisc.subring R R₀) (n : ℕ) :
    coeff n (mapHom φ hφ f : S⟦X⟧) = φ (coeff n (f : R⟦X⟧)) := by
  rw [coe_mapHom, coeff_map]

/-- A series lies in the kernel of `mapHom φ hφ` if and only if every coefficient lies in the
kernel of `φ`. -/
@[simp]
theorem mapHom_eq_zero_iff (f : OnOpenDisc.subring R R₀) :
    mapHom φ hφ f = 0 ↔ ∀ n, φ (coeff n (f : R⟦X⟧)) = 0 := by
  refine ⟨fun h n ↦ ?_, fun h ↦ Subtype.ext (PowerSeries.ext fun n ↦ ?_)⟩
  · simpa only [coeff_mapHom, ZeroMemClass.coe_zero, map_zero] using
      congrArg (fun g : OnOpenDisc.subring S R₀ ↦ coeff n (g : S⟦X⟧)) h
  · simpa only [coeff_mapHom, ZeroMemClass.coe_zero, map_zero] using h n

/-- `mapHom φ hφ` is injective if and only if `φ` is injective. -/
theorem mapHom_injective_iff :
    Function.Injective (mapHom (R₀ := R₀) φ hφ) ↔ Function.Injective φ := by
  refine ⟨fun hinj x y hxy ↦ ?_, fun hinj f g hfg ↦ Subtype.ext (PowerSeries.ext fun n ↦ hinj ?_)⟩
  · have hC : mapHom (R₀ := R₀) φ hφ (OnOpenDisc.polynomialHom (Polynomial.C x)) =
        mapHom (R₀ := R₀) φ hφ (OnOpenDisc.polynomialHom (Polynomial.C y)) :=
      Subtype.ext (by ext n; simp [hxy])
    simpa using congrArg (fun f : OnOpenDisc.subring R R₀ ↦ coeff 0 (f : R⟦X⟧)) (hinj hC)
  · simpa only [coeff_mapHom] using
      congrArg (fun h : OnOpenDisc.subring S R₀ ↦ coeff n (h : S⟦X⟧)) hfg

/-- The identity ring homomorphism induces the identity on open-disc series. -/
@[simp]
theorem mapHom_id {C₁ : ℝ} (hC : ∀ x : R, ‖RingHom.id R x‖ ≤ C₁ * ‖x‖) :
    mapHom (R₀ := R₀) (RingHom.id R) hC = RingHom.id _ :=
  RingHom.ext fun _ ↦ Subtype.ext (by simp)

/-- Bounded coefficient maps compose functorially. -/
theorem mapHom_comp {T : Type*} [NormedRing T] (ψ : S →+* T) {C₂ C₃ : ℝ}
    (hψ : ∀ y, ‖ψ y‖ ≤ C₂ * ‖y‖) (hψφ : ∀ x, ‖ψ.comp φ x‖ ≤ C₃ * ‖x‖) :
    mapHom (R₀ := R₀) (ψ.comp φ) hψφ = (mapHom ψ hψ).comp (mapHom φ hφ) :=
  RingHom.ext fun _ ↦ Subtype.ext <| PowerSeries.ext fun _ ↦ by simp

/-- Applying two bounded coefficient maps in turn applies the map of their composite. -/
@[simp]
theorem mapHom_mapHom {T : Type*} [NormedRing T] (ψ : S →+* T) {C₂ : ℝ}
    (hψ : ∀ y, ‖ψ y‖ ≤ C₂ * ‖y‖) (f : OnOpenDisc.subring R R₀) :
    mapHom ψ hψ (mapHom φ hφ f) =
      mapHom (ψ.comp φ) (C := max C₂ 0 * C) (fun x ↦ by
        rw [mul_assoc]
        exact (hψ (φ x)).trans <| (mul_le_mul_of_nonneg_right (le_max_left C₂ 0)
          (norm_nonneg _)).trans <| mul_le_mul_of_nonneg_left (hφ x) (le_max_right C₂ 0)) f :=
  Subtype.ext <| PowerSeries.ext fun _ ↦ by simp

/-- `mapHom` intertwines polynomial inclusions with `Polynomial.map`. -/
@[simp]
theorem mapHom_polynomialHom (p : Polynomial R) :
    mapHom (R₀ := R₀) φ hφ (OnOpenDisc.polynomialHom p) =
      OnOpenDisc.polynomialHom (Polynomial.map φ p) :=
  Subtype.ext <| PowerSeries.ext fun _ ↦ by simp

/-- **Coefficientwise bounded lifts on an open disc.** If every element of `S` lifts along `φ`
with norm bounded by `C'`, then every open-disc series over `S` lifts to an open-disc series over
`R` with the same coefficientwise norm bound. Neither ultrametricity nor completeness is needed. -/
theorem exists_mapHom_eq_and_norm_coeff_le {C' : ℝ}
    (hlift : ∀ s, ∃ r, φ r = s ∧ ‖r‖ ≤ C' * ‖s‖) (g : OnOpenDisc.subring S R₀) :
    ∃ f : OnOpenDisc.subring R R₀, mapHom φ hφ f = g ∧
      ∀ n, ‖coeff n (f : R⟦X⟧)‖ ≤ C' * ‖coeff n (g : S⟦X⟧)‖ := by
  choose lift hφ_lift hnorm_lift using hlift
  let f : R⟦X⟧ := PowerSeries.mk fun n ↦ lift (coeff n (g : S⟦X⟧))
  have hf : f.OnOpenDisc R₀ := onOpenDisc_iff.mpr fun r hr hrR ↦ by
    have hg_r := (isRestricted_iff' r (g : S⟦X⟧)).mp
      (onOpenDisc_iff.mp (OnOpenDisc.mem_subring.mp g.2) r hr hrR)
    rw [isRestricted_iff']
    refine squeeze_zero (fun n ↦ by positivity) (fun n ↦ ?_)
      (by simpa only [mul_zero] using hg_r.const_mul C')
    rw [coeff_mk, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (hnorm_lift _) (pow_nonneg hr.le n)
  refine ⟨⟨f, OnOpenDisc.mem_subring.mpr hf⟩, Subtype.ext (PowerSeries.ext fun n ↦ ?_),
    fun n ↦ by simpa only [f, coeff_mk] using hnorm_lift _⟩
  rw [coeff_mapHom, coeff_mk, hφ_lift]

/-- **Strict surjections induce surjections on open-disc series.** If every `s ∈ S` lifts along
`φ` to some `r ∈ R` with `‖r‖ ≤ C' * ‖s‖`, then `mapHom φ hφ` is surjective. -/
theorem mapHom_surjective {C' : ℝ} (hlift : ∀ s, ∃ r, φ r = s ∧ ‖r‖ ≤ C' * ‖s‖) :
    Function.Surjective (mapHom (R₀ := R₀) φ hφ) := fun g ↦
  let ⟨f, hf, _⟩ := exists_mapHom_eq_and_norm_coeff_le φ hφ hlift g
  ⟨f, hf⟩

end NormedRing

section NormedCommRing

variable {R S : Type*} [NormedCommRing R] [NormedCommRing S] {R₀ : ℝ}
  (φ : R →+* S) {C : ℝ} (hφ : ∀ x, ‖φ x‖ ≤ C * ‖x‖)

/-- `mapHom` sends scalar constants to scalar constants. -/
@[simp]
theorem mapHom_algebraMap (a : R) :
    mapHom (R₀ := R₀) φ hφ (algebraMap R _ a) = algebraMap S _ (φ a) :=
  Subtype.ext (by simp)

end NormedCommRing

section Ultrametric

variable {R S : Type*} [NormedRing R] [IsUltrametricDist R] [NormedRing S] [IsUltrametricDist S]
  {R₀ : ℝ}

attribute [local instance] radius_pos

variable (φ : R →+* S) {C : ℝ} (hφ : ∀ x, ‖φ x‖ ≤ C * ‖x‖)

/-- Restricting `mapHom φ hφ f` to a smaller positive closed disc applies `restrictedMap φ hφ`
to `restrict r f`. -/
@[simp]
theorem restrict_mapHom (r : Set.Ioo (0 : ℝ) R₀) (f : OnOpenDisc.subring R R₀) :
    restrict r (mapHom φ hφ f) = TauCeti.MvPowerSeries.restrictedMap φ hφ (restrict r f) := by
  apply Subtype.ext
  rw [coe_restrict, coe_mapHom, TauCeti.PowerSeries.coe_restrictedMap_powerSeries, coe_restrict]

/-- On every smaller positive closed disc, `mapHom φ hφ` multiplies the Gauss norm by at
most `C`. -/
theorem norm_restrict_mapHom_le (r : Set.Ioo (0 : ℝ) R₀) (f : OnOpenDisc.subring R R₀) :
    ‖restrict r (mapHom φ hφ f)‖ ≤ C * ‖restrict r f‖ := by
  rw [restrict_mapHom]
  exact TauCeti.MvPowerSeries.norm_restrictedMap_le φ hφ (restrict r f)

/-- A norm-preserving ring homomorphism preserves every smaller-radius Gauss norm. -/
theorem norm_restrict_mapHom (hφ' : ∀ x, ‖φ x‖ = ‖x‖) (r : Set.Ioo (0 : ℝ) R₀)
    (f : OnOpenDisc.subring R R₀) :
    ‖restrict r (mapHom φ hφ f)‖ = ‖restrict r f‖ := by
  rw [restrict_mapHom]
  exact TauCeti.MvPowerSeries.norm_restrictedMap φ hφ hφ' (restrict r f)

/-- Bounded coefficient maps are uniformly continuous for the open-disc Gauss uniformities. -/
theorem uniformContinuous_mapHom : UniformContinuous (mapHom (R₀ := R₀) φ hφ) := by
  refine uniformContinuous_iff.mpr fun r ↦ ?_
  simp_rw [restrict_mapHom]
  exact (TauCeti.MvPowerSeries.lipschitzWith_restrictedMap φ hφ).uniformContinuous.comp
    (uniformContinuous_restrict r)

/-- Bounded coefficient maps are continuous for the open-disc Gauss topologies. -/
@[continuity]
theorem continuous_mapHom : Continuous (mapHom (R₀ := R₀) φ hφ) :=
  (uniformContinuous_mapHom φ hφ).continuous

/-- A norm-preserving ring homomorphism induces a uniform-inducing map on open-disc series. -/
theorem isUniformInducing_mapHom (hφ' : ∀ x, ‖φ x‖ = ‖x‖) :
    IsUniformInducing (mapHom (R₀ := R₀) φ hφ) := by
  let θ (r : Set.Ioo (0 : ℝ) R₀) :
      IsRestricted.subring (R := R) (r : ℝ) →+* IsRestricted.subring (R := S) (r : ℝ) :=
    TauCeti.MvPowerSeries.restrictedMap φ hφ
  have hθ (r : Set.Ioo (0 : ℝ) R₀) : IsUniformInducing (θ r) :=
    ((AddMonoidHomClass.isometry_iff_norm (θ r)).mpr fun x ↦
      TauCeti.MvPowerSeries.norm_restrictedMap φ hφ hφ' x).isUniformInducing
  let ψ : (∀ r : Set.Ioo (0 : ℝ) R₀, IsRestricted.subring (R := R) (r : ℝ)) →
      ∀ r : Set.Ioo (0 : ℝ) R₀, IsRestricted.subring (R := S) (r : ℝ) :=
    fun g r ↦ θ r (g r)
  have hψ : IsUniformInducing ψ := by
    rw [isUniformInducing_iff_uniformSpace, Pi.uniformSpace_eq, Pi.uniformSpace_eq,
      UniformSpace.comap_iInf]
    refine iInf_congr fun r ↦ ?_
    rw [← UniformSpace.comap_comap]
    have hfun : Function.eval r ∘ ψ = θ r ∘ Function.eval r := rfl
    rw [hfun, UniformSpace.comap_comap]
    exact congrArg (UniformSpace.comap (Function.eval r)) (hθ r).comap_uniformSpace
  have hcomp : restrictFamily ∘ mapHom (R₀ := R₀) φ hφ = ψ ∘ restrictFamily := by
    funext f r
    dsimp [ψ, θ]
    rw [restrictFamily_apply, restrictFamily_apply, restrict_mapHom]
    rfl
  exact IsUniformInducing.of_comp (uniformContinuous_mapHom φ hφ)
    isUniformInducing_restrictFamily.uniformContinuous
    (hcomp ▸ hψ.comp isUniformInducing_restrictFamily)

/-- A norm-preserving ring homomorphism induces a uniform embedding on open-disc series. -/
theorem isUniformEmbedding_mapHom (hφ' : ∀ x, ‖φ x‖ = ‖x‖) :
    IsUniformEmbedding (mapHom (R₀ := R₀) φ hφ) :=
  ⟨isUniformInducing_mapHom φ hφ hφ', (mapHom_injective_iff φ hφ).mpr <|
    (AddMonoidHomClass.isometry_iff_norm φ).mpr hφ' |>.injective⟩

end Ultrametric

section Compatibilities

variable {R S : Type*} [NormedCommRing R] [IsUltrametricDist R] [CompleteSpace R]
  [NormedCommRing S] [IsUltrametricDist S] [CompleteSpace S] {R₀ S₀ : ℝ}
  (φ : R →+* S) {C : ℝ} (hφ : ∀ x, ‖φ x‖ ≤ C * ‖x‖)

attribute [local instance] radius_pos

omit [IsUltrametricDist R] [IsUltrametricDist S] [CompleteSpace S] in
/-- Evaluating `mapHom φ hφ f` at `φ a` gives `φ (f(a))` for any point `a` of the open disc. -/
theorem evalAt_mapHom {a : R} (ha : ‖a‖ < R₀) (f : OnOpenDisc.subring R R₀) :
    (mapHom φ hφ f : S⟦X⟧).evalAt (φ a) = φ ((f : R⟦X⟧).evalAt a) :=
  (OnOpenDisc.mem_subring.mp f.2).evalAt_map φ
    (AddMonoidHomClass.continuous_of_bound φ C hφ) ha

/-- **Bounded coefficient maps commute with Taylor translation** on an open disc. -/
theorem mapHom_taylorHom {a : R} (ha : ‖a‖ < R₀) (hφa : ‖φ a‖ < R₀)
    (f : OnOpenDisc.subring R R₀) :
    mapHom φ hφ (taylorHom ha f) = taylorHom hφa (mapHom φ hφ f) := by
  refine Subtype.ext <| PowerSeries.ext fun n ↦ ?_
  rw [coeff_mapHom, coe_taylorHom, coe_taylorHom, coeff_taylor, coeff_taylor, coe_mapHom,
    hasseDeriv_map]
  exact (((OnOpenDisc.mem_subring.mp f.2).hasseDeriv n).evalAt_map φ
    (AddMonoidHomClass.continuous_of_bound φ C hφ) ha).symm

/-- **Bounded coefficient maps commute with analytic substitution** on open discs whenever the
mapped inner series satisfies the target-to-source Gauss-norm bound (for instance when `C ≤ 1`). -/
theorem mapHom_analyticSubst [Fact (0 < S₀)] (g : OnOpenDisc.subring R S₀)
    (hg : ∀ s : Set.Ioo (0 : ℝ) S₀, ‖restrict s g‖ < R₀)
    (hg' : ∀ s : Set.Ioo (0 : ℝ) S₀, ‖restrict s (mapHom φ hφ g)‖ < R₀)
    (f : OnOpenDisc.subring R R₀) :
    mapHom φ hφ (analyticSubst g hg f) =
      analyticSubst (mapHom φ hφ g) hg' (mapHom φ hφ f) := by
  have heq : (mapHom (R₀ := S₀) φ hφ).comp (analyticSubst g hg).toRingHom =
      (analyticSubst (mapHom φ hφ g) hg').toRingHom.comp (mapHom (R₀ := R₀) φ hφ) :=
    ringHom_ext ((continuous_mapHom φ hφ).comp (continuous_analyticSubst g hg))
      ((continuous_analyticSubst (mapHom φ hφ g) hg').comp (continuous_mapHom φ hφ))
      (fun a ↦ by simp [mapHom_polynomialHom])
      (by simp [mapHom_polynomialHom])
  exact RingHom.congr_fun heq f

end Compatibilities

end TauCeti.PowerSeries.OnOpenDisc
