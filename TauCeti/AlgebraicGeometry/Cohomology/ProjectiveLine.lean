/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Cohomology.Genus
public import TauCeti.AlgebraicGeometry.Cohomology.MayerVietoris
public import TauCeti.AlgebraicGeometry.Cohomology.SectionsQuotient.Basic
public import TauCeti.AlgebraicGeometry.Cohomology.Trivial
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.ProjectiveLine

/-!
# Cohomology of the structure sheaf of the projective line

Let `ℙ¹_R = Proj R[X₀, X₁]` be the projective line over a commutative ring `R`
(`TauCeti.AlgebraicGeometry.projectiveLine`). This file computes the cohomology of its structure
sheaf: `H⁰(ℙ¹_R, 𝒪) = R` over any ring, and `Hⁿ(ℙ¹_R, 𝒪) = 0` for `n ≥ 1` when `R` is
Noetherian. This is the case `m = 0` of the computation of `Hⁿ(ℙ¹_R, 𝒪(m))` (Hartshorne,
Theorem III.5.1).

The computation uses the cover of `ℙ¹_R` by the standard charts `D₊(X₀)` and `D₊(X₁)`, with
overlap `D₊(X₀X₁)`. Their rings of functions are the degree-zero homogeneous localizations, which
are `R[t]`, `R[t⁻¹]` and `R[t, t⁻¹]` for `t = X₁ / X₀`. The Čech complex
`0 → R → R[t] × R[t⁻¹] → R[t, t⁻¹] → 0` of this cover is exact: a pair of polynomials `p(t)` and
`q(t⁻¹)` that agree is a constant, and every Laurent polynomial is a sum of a polynomial in `t` and
a polynomial in `t⁻¹`. Exactness at `R[t] × R[t⁻¹]` identifies the global functions with `R` over
any ring. Over a Noetherian ring, quasi-coherent sheaves on the affine charts have no higher
cohomology, so the two-open description of `H¹` as overlap functions modulo differences of
restrictions (`TauCeti.AlgebraicGeometry.sectionsQuotientEquivCohomologyOne`) shows that
`H¹(ℙ¹_R, 𝒪) = 0`, and Mayer–Vietoris kills every quasi-coherent sheaf in degrees at least two.

## Main results

All in the namespace `TauCeti.AlgebraicGeometry.projectiveLine`:

* `bijective_baseRingToGlobalSections`: the global functions on `ℙ¹_R` are the constants `R`.
* `cohomologyZeroTrivialLinearEquiv`: `H⁰(ℙ¹_R, 𝒪) ≃ₗ[R] R`.
* `subsingleton_cohomology_one_trivial`: `H¹(ℙ¹_R, 𝒪) = 0` over a Noetherian ring.
* `subsingleton_cohomology_of_two_le`: `Hⁿ(ℙ¹_R, M) = 0` for `n ≥ 2` and `M` quasi-coherent, over
  a Noetherian ring.
* `genus_eq_zero`: the projective line over a field has genus zero.

## References

* R. Hartshorne, *Algebraic Geometry*, GTM 52, Springer, 1977, Theorem III.5.1.
* The Stacks Project, Section 30.8 (Tag 01XS), cohomology of projective space.
-/

public section

open CategoryTheory Limits AlgebraicGeometry HomogeneousLocalization Polynomial

universe u

namespace TauCeti.AlgebraicGeometry.projectiveLine

variable (R : Type u) [CommRing R]

local notation "𝒜" => SymmetricAlgebra.homogeneousSubmodule R (Fin 2 → R)

/-- The ring `R[X₀, X₁]_(X₀X₁)` of the overlap `D₊(X₀X₁)` of the two standard charts. -/
local notation "B" => Away 𝒜 (coord R 0 * coord R 1)

/-- Restriction from the chart `D₊(X₀)` to the overlap. -/
private noncomputable abbrev ρ₀ : Away 𝒜 (coord R 0) →+* B :=
  awayMap 𝒜 (coord_mem R 1) rfl

/-- Restriction from the chart `D₊(X₁)` to the overlap. -/
private noncomputable abbrev ρ₁ : Away 𝒜 (coord R 1) →+* B :=
  awayMap 𝒜 (coord_mem R 0) (mul_comm _ _)

/-- The overlap restriction of a polynomial on the chart `D₊(X₀)`, whose functions are identified
with polynomials in `X₁ / X₀`. -/
private noncomputable abbrev ψ₀ : R[X] →+* B :=
  (ρ₀ R).comp (awayEquivPolynomial R 0).symm.toRingEquiv.toRingHom

/-- The overlap restriction of a polynomial on the chart `D₊(X₁)`. -/
private noncomputable abbrev ψ₁ : R[X] →+* B :=
  (ρ₁ R).comp (awayEquivPolynomial R 1).symm.toRingEquiv.toRingHom

/-- On the overlap, the coordinate `X₁ / X₀` of the first chart and the coordinate `X₀ / X₁` of
the second chart are inverse to each other. -/
private theorem ψ₀_X_mul_ψ₁_X : ψ₀ R X * ψ₁ R X = 1 := by
  simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
    AlgEquiv.coe_toRingEquiv, awayEquivPolynomial_symm_X, awayMap_mk]
  ext
  simp only [val_mul, Away.val_mk, val_one, Localization.mk_mul]
  rw [← Localization.mk_one, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  exact ⟨1, by simp; ring⟩

/-- Restriction to the overlap respects the constants. -/
private theorem ψ₀_C (r : R) : ψ₀ R (C r) = algebraMap R B r := by
  rw [← Polynomial.algebraMap_eq]
  exact (congrArg (ρ₀ R) ((awayEquivPolynomial R 0).symm.commutes r)).trans
    (awayMap_algebraMap _ _ r)

/-- Restriction to the overlap respects the constants. -/
private theorem ψ₁_C (r : R) : ψ₁ R (C r) = algebraMap R B r := by
  rw [← Polynomial.algebraMap_eq]
  exact (congrArg (ρ₁ R) ((awayEquivPolynomial R 1).symm.commutes r)).trans
    (awayMap_algebraMap _ _ r)

/-- `ψ₀` evaluates a polynomial at the coordinate `X₁ / X₀` of the overlap. -/
private theorem ψ₀_eq_aeval (p : R[X]) : ψ₀ R p = aeval (ψ₀ R X) p :=
  DFunLike.congr_fun (Polynomial.ringHom_ext (g := (aeval (ψ₀ R X)).toRingHom)
    (fun r ↦ by simp [ψ₀_C]) (by simp)) p

/-- `ψ₁` evaluates a polynomial at the coordinate `X₀ / X₁` of the overlap. -/
private theorem ψ₁_eq_aeval (p : R[X]) : ψ₁ R p = aeval (ψ₁ R X) p :=
  DFunLike.congr_fun (Polynomial.ringHom_ext (g := (aeval (ψ₁ R X)).toRingHom)
    (fun r ↦ by simp [ψ₁_C]) (by simp)) p

/-- The overlap ring is the localization of the first chart ring away from `X₁ / X₀`. -/
private theorem isLocalization_ρ₀ :
    letI := (ρ₀ R).toAlgebra
    IsLocalization.Away ((awayEquivPolynomial R 0).symm X) B := by
  have h := Away.isLocalization_mul (coord_mem R 0) (coord_mem R 1) rfl one_ne_zero
  convert h using 2
  rw [awayEquivPolynomial_symm_X]
  ext
  simp [Away.val_mk]

/-- Restriction from the first chart to the overlap is injective. -/
private theorem ψ₀_injective : Function.Injective (ψ₀ R) := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · exact Function.injective_of_subsingleton _
  let := (ρ₀ R).toAlgebra
  have := isLocalization_ρ₀ R
  have hX : (awayEquivPolynomial R 0).symm X ∈ nonZeroDivisors (Away 𝒜 (coord R 0)) :=
    mem_nonZeroDivisors_of_injective (awayEquivPolynomial R 0).injective
      (by rw [AlgEquiv.apply_symm_apply]; exact X_mem_nonZeroDivisors)
  exact (IsLocalization.injective B (Submonoid.powers_le.mpr hX)).comp
    (awayEquivPolynomial R 0).symm.injective

/-- Every function on the overlap is `ψ₀ p * (X₀ / X₁)ⁿ` for a polynomial `p`. -/
private theorem exists_eq_ψ₀_mul_pow (b : B) : ∃ (p : R[X]) (n : ℕ), b = ψ₀ R p * ψ₁ R X ^ n := by
  let := (ρ₀ R).toAlgebra
  have := isLocalization_ρ₀ R
  obtain ⟨⟨a, _, n, rfl⟩, h⟩ := IsLocalization.surj (Submonoid.powers
    ((awayEquivPolynomial R 0).symm X)) b
  refine ⟨awayEquivPolynomial R 0 a, n, ?_⟩
  have h' : b * ψ₀ R X ^ n = ψ₀ R (awayEquivPolynomial R 0 a) := by
    simpa [RingHom.algebraMap_toAlgebra] using h
  calc b = b * (ψ₀ R X * ψ₁ R X) ^ n := by rw [ψ₀_X_mul_ψ₁_X, one_pow, mul_one]
    _ = ψ₀ R (awayEquivPolynomial R 0 a) * ψ₁ R X ^ n := by rw [← h', mul_pow]; ring

/-- **Every function on the overlap is a difference of functions on the two charts.** -/
private theorem exists_ρ₀_sub_ρ₁_eq (b : B) :
    ∃ (a₀ : Away 𝒜 (coord R 0)) (a₁ : Away 𝒜 (coord R 1)), ρ₀ R a₀ - ρ₁ R a₁ = b := by
  suffices h : ∀ (n : ℕ) (p : R[X]), ∃ (a₀ : Away 𝒜 (coord R 0)) (a₁ : Away 𝒜 (coord R 1)),
      ρ₀ R a₀ - ρ₁ R a₁ = ψ₀ R p * ψ₁ R X ^ n by
    obtain ⟨p, n, rfl⟩ := exists_eq_ψ₀_mul_pow R b
    exact h n p
  intro n
  induction n with
  | zero => exact fun p ↦ ⟨(awayEquivPolynomial R 0).symm p, 0, by simp⟩
  | succ n ih =>
    intro p
    -- write `p = c + X q`, so that `p · (X₀/X₁)ⁿ⁺¹ = q · (X₀/X₁)ⁿ + c · (X₀/X₁)ⁿ⁺¹`
    obtain ⟨a₀, a₁, h⟩ := ih p.divX
    refine ⟨a₀, a₁ - (awayEquivPolynomial R 1).symm (C (p.coeff 0) * X ^ (n + 1)), ?_⟩
    have hψ : ψ₁ R (C (p.coeff 0) * X ^ (n + 1)) =
        ρ₁ R ((awayEquivPolynomial R 1).symm (C (p.coeff 0) * X ^ (n + 1))) := rfl
    have hp : ψ₀ R p = ψ₀ R X * ψ₀ R p.divX + algebraMap R B (p.coeff 0) := by
      conv_lhs => rw [← X_mul_divX_add p]
      rw [map_add, map_mul, ψ₀_C]
    rw [map_sub, ← hψ, sub_sub_eq_add_sub, add_sub_right_comm, h, hp, map_mul, map_pow, ψ₁_C]
    linear_combination (-(ψ₀ R p.divX * ψ₁ R X ^ n)) * ψ₀_X_mul_ψ₁_X R

/-- **A pair of chart functions agreeing on the overlap is a constant.** -/
private theorem exists_eq_algebraMap_of_ρ₀_eq_ρ₁ {a₀ : Away 𝒜 (coord R 0)}
    {a₁ : Away 𝒜 (coord R 1)} (h : ρ₀ R a₀ = ρ₁ R a₁) :
    ∃ r : R, a₀ = algebraMap R _ r ∧ a₁ = algebraMap R _ r := by
  set p := awayEquivPolynomial R 0 a₀
  set q := awayEquivPolynomial R 1 a₁
  have hpq : ψ₀ R p = ψ₁ R q := by simpa [p, q] using h
  -- reflecting `q` at its degree `N` turns `q(X₀/X₁)` into `(X₀/X₁)^N · q'(X₁/X₀)`
  set N := q.natDegree
  let : Invertible (ψ₁ R X) := ⟨ψ₀ R X, ψ₀_X_mul_ψ₁_X R, (mul_comm _ _).trans (ψ₀_X_mul_ψ₁_X R)⟩
  have href : ψ₀ R (q.reflect N) * ψ₁ R X ^ N = ψ₁ R q := by
    rw [ψ₀_eq_aeval R (q.reflect N), ψ₁_eq_aeval R q, aeval_def, aeval_def]
    exact eval₂_reflect_mul_pow _ _ N q le_rfl
  have hrefl : q.reflect N = p * X ^ N := by
    apply ψ₀_injective R
    rw [map_mul, map_pow, hpq, ← href, mul_assoc, ← mul_pow, mul_comm (ψ₁ R X),
      ψ₀_X_mul_ψ₁_X, one_pow, mul_one]
  -- comparing degrees, `p` is a constant `c`, and then so is `q`
  obtain ⟨c, hp⟩ : ∃ c, p = C c := by
    refine ⟨p.coeff 0, eq_C_of_natDegree_le_zero ?_⟩
    nontriviality R
    by_cases hp0 : p = 0
    · simp [hp0]
    · have h1 := natDegree_reflect_le (N := N) (p := q)
      rw [hrefl, natDegree_mul_X_pow N hp0, max_self] at h1
      omega
  have hq : q = C c := by
    rw [← reflect_reflect (N := N) (p := q), hrefl, hp, ← reflect_C, reflect_reflect]
  refine ⟨c, (awayEquivPolynomial R 0).injective ?_, (awayEquivPolynomial R 1).injective ?_⟩
  · rw [AlgEquiv.commutes, Polynomial.algebraMap_eq]
    exact hp
  · rw [AlgEquiv.commutes, Polynomial.algebraMap_eq]
    exact hq

/-! ### Functions on the standard charts -/

/-- The product `X₀X₁` is a form of degree two. -/
private theorem coord_mul_coord_mem : coord R 0 * coord R 1 ∈ 𝒜 (1 + 1) :=
  SetLike.mul_mem_graded (coord_mem R 0) (coord_mem R 1)

/-- Restricting a function on `D₊(X₀)` to `D₊(X₀X₁)` is `ρ₀` on fractions. -/
private theorem map_awayToSection_ρ₀ (h : Proj.basicOpen 𝒜 (coord R 0 * coord R 1) ≤
    Proj.basicOpen 𝒜 (coord R 0)) (a : Away 𝒜 (coord R 0)) :
    (projectiveLine R).presheaf.map (homOfLE h).op (Proj.awayToSection 𝒜 (coord R 0) a) =
      Proj.awayToSection 𝒜 (coord R 0 * coord R 1) (ρ₀ R a) :=
  congr($(Proj.awayMap_awayToSection 𝒜 (coord_mem R 1) (rfl : coord R 0 * coord R 1 = _)) a).symm

/-- Restricting a function on `D₊(X₁)` to `D₊(X₀X₁)` is `ρ₁` on fractions. -/
private theorem map_awayToSection_ρ₁ (h : Proj.basicOpen 𝒜 (coord R 0 * coord R 1) ≤
    Proj.basicOpen 𝒜 (coord R 1)) (a : Away 𝒜 (coord R 1)) :
    (projectiveLine R).presheaf.map (homOfLE h).op (Proj.awayToSection 𝒜 (coord R 1) a) =
      Proj.awayToSection 𝒜 (coord R 0 * coord R 1) (ρ₁ R a) :=
  congr($(Proj.awayMap_awayToSection 𝒜 (coord_mem R 0) (mul_comm (coord R 0) (coord R 1))) a).symm

/-- **Every function on `D₊(X₀) ∩ D₊(X₁)` is a difference of restrictions from the two charts.** -/
private theorem exists_map_sub_map_eq (b : Γ(projectiveLine R,
    Proj.basicOpen 𝒜 (coord R 0) ⊓ Proj.basicOpen 𝒜 (coord R 1))) :
    ∃ (s : Γ(projectiveLine R, Proj.basicOpen 𝒜 (coord R 0)))
      (t : Γ(projectiveLine R, Proj.basicOpen 𝒜 (coord R 1))),
      (projectiveLine R).presheaf.map (homOfLE inf_le_left).op s -
        (projectiveLine R).presheaf.map (homOfLE inf_le_right).op t = b := by
  -- the overlap is `D₊(X₀X₁)`, whose functions are the fractions of `A_(X₀X₁)`
  suffices h : ∀ (W : (projectiveLine R).Opens) (_ : Proj.basicOpen 𝒜 (coord R 0 * coord R 1) = W)
      (h₀ : W ≤ Proj.basicOpen 𝒜 (coord R 0)) (h₁ : W ≤ Proj.basicOpen 𝒜 (coord R 1))
      (b : Γ(projectiveLine R, W)), ∃ s t, (projectiveLine R).presheaf.map (homOfLE h₀).op s -
        (projectiveLine R).presheaf.map (homOfLE h₁).op t = b from
    h _ (Proj.basicOpen_mul _ _ _) inf_le_left inf_le_right b
  rintro W rfl h₀ h₁ b
  have hσ : Function.Surjective (Proj.awayToSection 𝒜 (coord R 0 * coord R 1)) :=
    (Proj.basicOpenIsoAway 𝒜 _ (coord_mul_coord_mem R) two_pos).commRingCatIsoToRingEquiv.surjective
  obtain ⟨c, rfl⟩ := hσ b
  obtain ⟨a₀, a₁, rfl⟩ := exists_ρ₀_sub_ρ₁_eq R c
  exact ⟨Proj.awayToSection 𝒜 _ a₀, Proj.awayToSection 𝒜 _ a₁, by
    rw [map_awayToSection_ρ₀, map_awayToSection_ρ₁, map_sub]⟩

/-! ### Cohomology of the structure sheaf -/

open Scheme.Modules

/-- **The global functions on the projective line are the constants**: the map from `R` to
`Γ(ℙ¹_R, 𝒪)` is bijective. -/
theorem bijective_baseRingToGlobalSections :
    Function.Bijective (baseRingToGlobalSections R (projectiveLine R)) := by
  have hσ (i : Fin 2) : Function.Bijective (Proj.awayToSection 𝒜 (coord R i)) :=
    (Proj.basicOpenIsoAway 𝒜 _ (coord_mem R i) one_pos).commRingCatIsoToRingEquiv.bijective
  have hres (i : Fin 2) (c : R) : Proj.awayToSection 𝒜 (coord R i) (algebraMap R _ c) =
      (projectiveLine R).presheaf.map (homOfLE le_top).op
        (baseRingToGlobalSections R (projectiveLine R) c) := by
    rw [baseRingToGlobalSections_apply]
    exact awayToSection_algebraMap R i c
  refine ⟨fun c c' h ↦ ?_, fun s ↦ ?_⟩
  · -- restricted to `D₊(X₀)`, the constants `c` and `c'` are the constant polynomials
    have h₀ := congrArg ((projectiveLine R).presheaf.map
      (homOfLE (le_top (a := Proj.basicOpen 𝒜 (coord R 0)))).op) h
    rw [← hres, ← hres] at h₀
    have := congrArg (awayEquivPolynomial R 0) ((hσ 0).1 h₀)
    simp only [AlgEquiv.commutes] at this
    exact C_injective this
  · -- the restrictions of `s` to the two charts agree on the overlap, so they are a constant
    obtain ⟨a₀, ha₀⟩ := (hσ 0).2 ((projectiveLine R).presheaf.map
      (homOfLE (le_top (a := Proj.basicOpen 𝒜 (coord R 0)))).op s)
    obtain ⟨a₁, ha₁⟩ := (hσ 1).2 ((projectiveLine R).presheaf.map
      (homOfLE (le_top (a := Proj.basicOpen 𝒜 (coord R 1)))).op s)
    have hW (i : Fin 2) :
        Proj.basicOpen 𝒜 (coord R 0 * coord R 1) ≤ Proj.basicOpen 𝒜 (coord R i) :=
      (Proj.basicOpen_mul _ _ _).trans_le (by fin_cases i; exacts [inf_le_left, inf_le_right])
    have h : ρ₀ R a₀ = ρ₁ R a₁ := by
      have hσ₀₁ : Function.Injective (Proj.awayToSection 𝒜 (coord R 0 * coord R 1)) :=
        (Proj.basicOpenIsoAway 𝒜 _ (coord_mul_coord_mem R)
          two_pos).commRingCatIsoToRingEquiv.injective
      refine hσ₀₁ ?_
      rw [← map_awayToSection_ρ₀ R (hW 0), ← map_awayToSection_ρ₁ R (hW 1), ha₀, ha₁,
        ← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← Functor.map_comp, ← Functor.map_comp]
      congr 2
    obtain ⟨c, rfl, rfl⟩ := exists_eq_algebraMap_of_ρ₀_eq_ρ₁ R h
    refine ⟨c, (projectiveLine R).sheaf.eq_of_locally_eq₂
      (homOfLE (le_top (a := Proj.basicOpen 𝒜 (coord R 0))))
      (homOfLE (le_top (a := Proj.basicOpen 𝒜 (coord R 1))))
      (basicOpen_coord_sup_eq_top R).ge _ _ ?_ ?_⟩
    · exact (hres 0 c).symm.trans ha₀
    · exact (hres 1 c).symm.trans ha₁

/-- Over a Noetherian ring, the functions on a standard chart form a Noetherian ring. -/
private theorem isNoetherianRing_basicOpen_coord [IsNoetherianRing R] (i : Fin 2) :
    IsNoetherianRing Γ(projectiveLine R, Proj.basicOpen 𝒜 (coord R i)) :=
  image_awayι_top R i ▸ isNoetherianRing_of_ringEquiv R[X] (chartSectionsEquiv R i).symm

/-- **The structure sheaf of the projective line has no first cohomology** over a Noetherian
ring. -/
instance subsingleton_cohomology_one_trivial [IsNoetherianRing R] :
    Subsingleton (Cohomology (InvertibleSheaf.trivial (projectiveLine R)).obj 1) := by
  let M : (projectiveLine R).Modules := SheafOfModules.unit (projectiveLine R).ringCatSheaf
  suffices Subsingleton (Cohomology M 1) from
    (trivialCohomologyBaseLinearEquiv R (projectiveLine R) 1).toEquiv.subsingleton
  have hacyclic (i : Fin 2) : Subsingleton (cohomologyOn M 1 (Proj.basicOpen 𝒜 (coord R i))) :=
    have := isNoetherianRing_basicOpen_coord R i
    subsingleton_cohomologyOn_succ_of_isAffineOpen M
      (Proj.isAffineOpen_basicOpen 𝒜 _ (coord_mem R i) one_pos) 0
  -- `H¹` is the quotient of the functions on the overlap by the differences of restrictions
  have hrange : (mayerVietorisSectionsDifference M _ _).range = ⊤ :=
    AddMonoidHom.range_eq_top.mpr fun b ↦
      have ⟨s, t, h⟩ := exists_map_sub_map_eq R b
      ⟨(s, t), (mayerVietorisSectionsDifference_apply M _ _ s t).trans h⟩
  have : Subsingleton (Γ(M, Proj.basicOpen 𝒜 (coord R 0) ⊓ Proj.basicOpen 𝒜 (coord R 1)) ⧸
      (mayerVietorisSectionsDifference M _ _).range) := by
    rw [hrange]
    exact QuotientAddGroup.subsingleton_quotient_top
  exact (sectionsQuotientEquivCohomologyOne M _ _ (basicOpen_coord_sup_eq_top R) (hacyclic 0)
    (hacyclic 1)).symm.toEquiv.subsingleton

/-- **Vanishing above dimension one**: over a Noetherian ring, a quasi-coherent sheaf on the
projective line has no cohomology in degrees at least two. -/
theorem subsingleton_cohomology_of_two_le [IsNoetherianRing R] (M : (projectiveLine R).Modules)
    [M.IsQuasicoherent] (n : ℕ) (hn : 2 ≤ n) : Subsingleton (Cohomology M n) := by
  have : IsLocallyNoetherian (projectiveLine R) :=
    LocallyOfFiniteType.isLocallyNoetherian (projectiveLine R ↘ Spec (.of R))
  exact subsingleton_cohomology_of_two_le_of_isAffineOpen M
    (Proj.isAffineOpen_basicOpen 𝒜 _ (coord_mem R 0) one_pos)
    (Proj.isAffineOpen_basicOpen 𝒜 _ (coord_mem R 1) one_pos)
    (Proj.basicOpen_mul 𝒜 _ _ ▸ Proj.isAffineOpen_basicOpen 𝒜 _ (coord_mul_coord_mem R) two_pos)
    (basicOpen_coord_sup_eq_top R) n hn

/-- **The zeroth cohomology of the structure sheaf of the projective line is the base ring**:
`H⁰(ℙ¹_R, 𝒪) ≅ R`, as `R`-modules. -/
noncomputable def cohomologyZeroTrivialLinearEquiv :
    Cohomology (InvertibleSheaf.trivial (projectiveLine R)).obj 0 ≃ₗ[R] R :=
  letI : Algebra R Γ(projectiveLine R, ⊤) :=
    (((projectiveLine R).baseRingToStructurePresheaf R).app (.op ⊤)).hom.toAlgebra
  ((trivialCohomologyBaseLinearEquiv R _ 0).trans ((cohomologyZeroBaseLinearEquiv R _ _).trans
    (structureSheafSectionsBaseLinearEquiv R _))).trans
    (LinearEquiv.ofBijective (Algebra.linearMap R Γ(projectiveLine R, ⊤)) (by
      convert bijective_baseRingToGlobalSections R
      exact _root_.funext fun x ↦ ConcreteCategory.congr_hom
        (Scheme.baseRingToStructurePresheaf_app_top R (projectiveLine R)) x)).symm

/-- Under `cohomologyZeroTrivialLinearEquiv`, an element `r` of the base ring is the class of the
constant function `r`. -/
theorem cohomologyZeroTrivialLinearEquiv_symm_apply (r : R) :
    (cohomologyZeroTrivialLinearEquiv R).symm r = (trivialCohomologyBaseLinearEquiv R _ 0).symm
      ((cohomologyZeroBaseLinearEquiv R _
        (SheafOfModules.unit (projectiveLine R).ringCatSheaf)).symm
          (baseRingToGlobalSections R (projectiveLine R) r)) := by
  simp only [cohomologyZeroTrivialLinearEquiv, LinearEquiv.trans_symm, LinearEquiv.symm_symm,
    LinearEquiv.trans_apply, LinearEquiv.ofBijective_apply, Algebra.linearMap_apply,
    structureSheafSectionsBaseLinearEquiv_symm_apply]
  exact congrArg _ <| congrArg _ <| ConcreteCategory.congr_hom
    (Scheme.baseRingToStructurePresheaf_app_top R (projectiveLine R)) r

variable (k : Type u) [Field k]

/-- **The projective line has genus zero.** -/
theorem genus_eq_zero : (projectiveLine k).genus k = 0 := by
  rw [Scheme.genus_def]
  exact Module.finrank_zero_of_subsingleton

end TauCeti.AlgebraicGeometry.projectiveLine
