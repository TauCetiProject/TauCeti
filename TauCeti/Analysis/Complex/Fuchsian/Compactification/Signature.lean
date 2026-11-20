/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cellular.EulerCharacteristic.Genus
public import TauCeti.Analysis.Complex.Fuchsian.Compactification.Divisor
public import TauCeti.Analysis.Complex.Fuchsian.Compactification.RamificationDegree
import TauCeti.Analysis.Complex.Fuchsian.Compactification.CellStructure
import TauCeti.Analysis.Complex.Fuchsian.DirichletDomain.Cofinite
import TauCeti.Analysis.Complex.Fuchsian.Polygon.LocallyFinite

/-!
# The signature area formula and Riemann–Hurwitz for cofinite Fuchsian groups

Centring a Dirichlet domain of a cofinite Fuchsian group `Γ ≤ PSL(2, ℝ)` in its free locus gives a
fundamental polygon `(P, σ)` (`Subgroup.IsCofinite.exists_sidePairing_of_mem_freeLocus`). Applying
the CW structure of `TauCeti.Analysis.Complex.Fuchsian.Compactification.CellStructure` yields:

* `Subgroup.IsCofinite.finiteCWType_compactifiedQuotient`: `X(Γ)` has finite CW type;
* `Subgroup.IsCofinite.eulerChar_compactifiedQuotient_eq_two_sub_two_mul_genus`:
  `χ(X(Γ)) = 2 - 2 · genus X(Γ)`;
* `Subgroup.IsCofinite.covolume_eq_two_pi_mul_neg_eulerChar_add_cusps` and
  `Subgroup.IsCofinite.covolume_eq_two_pi_mul_signature`: the orbifold area formulas;
* `Subgroup.IsCofinite.eulerChar_compactifiedQuotient_lt_finsum_mem_ellipticOrbits_add_cusps` and
  `Subgroup.IsCofinite.two_mul_genus_compactifiedQuotient_sub_two_add_pos`: signature positivity;
* `Subgroup.IsCofinite.eulerChar_sub_finsum_mem_ellipticOrbits_sub_cusps_eq_index_mul`:
  multiplicativity of the orbifold Euler characteristic;
* `Fuchsian.eulerChar_compactifiedQuotient_eq_index_mul_sub_ramificationDegree_of_isCofinite` and
  `Fuchsian.two_mul_genus_compactifiedQuotient_sub_two_eq_index_mul_add_ramificationDegree`:
  unconditional Riemann–Hurwitz for finite-index inclusions of cofinite Fuchsian groups.

## References

* Alan Beardon, *The Geometry of Discrete Groups*, GTM 91, Springer, 1983, §10.4.
* Fred Diamond and Jerry Shurman, *A First Course in Modular Forms*, GTM 228, Springer, 2005,
  Theorem 3.1.1.
* Svetlana Katok, *Fuchsian Groups*, University of Chicago Press, 1992, §§4.2–4.3.
-/

public section

noncomputable section

open MeasureTheory MulAction Set UpperHalfPlane TauCeti TauCeti.UpperHalfPlane
open scoped MatrixGroups Pointwise

namespace Subgroup.IsCofinite

variable {Γ : Subgroup PSL(2, ℝ)} [DiscreteTopology Γ]

private theorem exists_convexPolygon_sidePairing (hΓ : Γ.IsCofinite) :
    ∃ (n : ℕ) (_ : NeZero n) (P : ConvexPolygon n) (σ : P.SidePairing),
      (∀ i, σ.map i ∈ Γ) ∧
      (LocallyFinite fun γ : Γ ↦ (γ : PSL(2, ℝ)) • P.carrier) ∧
      ∀ γ : Γ, γ ≠ 1 → Disjoint ((γ : PSL(2, ℝ)) • interior P.carrier) (interior P.carrier) := by
  obtain ⟨p, hp⟩ := freeLocus_nonempty Γ
  obtain ⟨n, hn, P, σ, hmap, hP, hcusp⟩ := hΓ.exists_sidePairing_of_mem_freeLocus hp
  exact ⟨n, hn, P, σ, hmap, P.locallyFinite_smul_carrier_of_isCuspPoint hcusp,
    ConvexPolygon.disjoint_smul_interior_carrier_of_carrier_eq_dirichletDomain hP hp⟩

/-- **The compactified quotient of a cofinite Fuchsian group has finite CW type.** -/
theorem finiteCWType_compactifiedQuotient (hΓ : Γ.IsCofinite) :
    FiniteCWType Γ.CompactifiedQuotient := by
  obtain ⟨_, _, _, σ, hmap, hlf, hdisj⟩ := hΓ.exists_convexPolygon_sidePairing
  exact σ.finiteCWType_compactifiedQuotient hmap hlf hdisj

/-- **The genus bridge for a cofinite Fuchsian group:** `χ(X(Γ)) = 2 - 2 · genus X(Γ)`. -/
theorem eulerChar_compactifiedQuotient_eq_two_sub_two_mul_genus (hΓ : Γ.IsCofinite) :
    haveI := hΓ.finiteCWType_compactifiedQuotient
    eulerChar Γ.CompactifiedQuotient = 2 - 2 * RiemannSurface.genus Γ.CompactifiedQuotient := by
  obtain ⟨_, _, _, σ, hmap, hlf, hdisj⟩ := hΓ.exists_convexPolygon_sidePairing
  exact σ.eulerChar_compactifiedQuotient_eq_two_sub_two_mul_genus hmap hlf hdisj

/-- **The orbifold area formula through the Euler characteristic:**
`covolume Γ ℍ = 2π (-χ(X(Γ)) + ∑ₑ (1 - 1 / mₑ) + c)`. -/
theorem covolume_eq_two_pi_mul_neg_eulerChar_add_cusps (hΓ : Γ.IsCofinite) :
    haveI := hΓ.finiteCWType_compactifiedQuotient
    covolume Γ ℍ = ENNReal.ofReal (2 * Real.pi * (-(eulerChar Γ.CompactifiedQuotient : ℝ) +
      ∑ᶠ e ∈ Γ.ellipticOrbits, (1 - (cardStabilizerOnOrbit e : ℝ)⁻¹) +
        Nat.card Γ.CuspOrbit)) := by
  obtain ⟨_, _, _, σ, hmap, hlf, hdisj⟩ := hΓ.exists_convexPolygon_sidePairing
  exact σ.covolume_eq_two_pi_mul_neg_eulerChar_add_cusps hmap hlf hdisj

/-- **The signature area formula for a cofinite Fuchsian group:**
`covolume Γ ℍ = 2π (2g - 2 + ∑ₑ (1 - 1 / mₑ) + c)`. -/
theorem covolume_eq_two_pi_mul_signature (hΓ : Γ.IsCofinite) :
    haveI := hΓ.finiteCWType_compactifiedQuotient
    covolume Γ ℍ = ENNReal.ofReal (2 * Real.pi *
      (2 * (RiemannSurface.genus Γ.CompactifiedQuotient : ℝ) - 2 +
        ∑ᶠ e ∈ Γ.ellipticOrbits, (1 - (cardStabilizerOnOrbit e : ℝ)⁻¹) +
          Nat.card Γ.CuspOrbit)) := by
  obtain ⟨_, _, _, σ, hmap, hlf, hdisj⟩ := hΓ.exists_convexPolygon_sidePairing
  exact σ.covolume_eq_two_pi_mul_signature hmap hlf hdisj

/-- **The hyperbolicity inequality in Euler-characteristic form:**
`χ(X(Γ)) < ∑ₑ (1 - 1 / mₑ) + c`. -/
theorem eulerChar_compactifiedQuotient_lt_finsum_mem_ellipticOrbits_add_cusps (hΓ : Γ.IsCofinite) :
    haveI := hΓ.finiteCWType_compactifiedQuotient
    (eulerChar Γ.CompactifiedQuotient : ℝ) <
      ∑ᶠ e ∈ Γ.ellipticOrbits, (1 - (cardStabilizerOnOrbit e : ℝ)⁻¹) + Nat.card Γ.CuspOrbit := by
  have hpos : 0 < covolume Γ ℍ := covolume_pos <|
    Measure.measure_univ_pos.mp (isOpen_univ.measure_pos volume univ_nonempty)
  rw [hΓ.covolume_eq_two_pi_mul_neg_eulerChar_add_cusps, ENNReal.ofReal_pos] at hpos
  nlinarith [Real.pi_pos]

/-- **The hyperbolicity inequality for the signature:** `2g - 2 + ∑ₑ (1 - 1 / mₑ) + c > 0`. -/
theorem two_mul_genus_compactifiedQuotient_sub_two_add_pos (hΓ : Γ.IsCofinite) :
    haveI := hΓ.finiteCWType_compactifiedQuotient
    0 < 2 * (RiemannSurface.genus Γ.CompactifiedQuotient : ℝ) - 2 +
      ∑ᶠ e ∈ Γ.ellipticOrbits, (1 - (cardStabilizerOnOrbit e : ℝ)⁻¹) +
        Nat.card Γ.CuspOrbit := by
  have hlt := hΓ.eulerChar_compactifiedQuotient_lt_finsum_mem_ellipticOrbits_add_cusps
  rw [hΓ.eulerChar_compactifiedQuotient_eq_two_sub_two_mul_genus] at hlt
  push_cast at hlt; linarith

/-- **Multiplicativity of the orbifold Euler characteristic** under finite-index subgroups:
`χ(X(Δ)) - ∑ₑ (1 - 1 / mₑ) - c(Δ) = [Γ : Δ] · (χ(X(Γ)) - ∑ₑ (1 - 1 / mₑ) - c(Γ))`. -/
theorem eulerChar_sub_finsum_mem_ellipticOrbits_sub_cusps_eq_index_mul (hΓ : Γ.IsCofinite)
    {Δ : Subgroup PSL(2, ℝ)} (h : Δ ≤ Γ) [Δ.IsFiniteRelIndex Γ] :
    letI : DiscreteTopology Δ := DiscreteTopology.of_subset ‹DiscreteTopology Γ› h
    haveI := hΓ.finiteCWType_compactifiedQuotient
    haveI := ((isCofinite_iff_isCofinite_and_finiteIndex h).mpr
      ⟨hΓ, inferInstance⟩).finiteCWType_compactifiedQuotient
    (eulerChar Δ.CompactifiedQuotient : ℝ) -
        ∑ᶠ e ∈ Δ.ellipticOrbits, (1 - (cardStabilizerOnOrbit e : ℝ)⁻¹) -
        Nat.card Δ.CuspOrbit =
      (Δ.subgroupOf Γ).index * ((eulerChar Γ.CompactifiedQuotient : ℝ) -
        ∑ᶠ e ∈ Γ.ellipticOrbits, (1 - (cardStabilizerOnOrbit e : ℝ)⁻¹) -
        Nat.card Γ.CuspOrbit) := by
  let : DiscreteTopology Δ := DiscreteTopology.of_subset ‹DiscreteTopology Γ› h
  have hΔ : Δ.IsCofinite := (isCofinite_iff_isCofinite_and_finiteIndex h).mpr ⟨hΓ, inferInstance⟩
  have hcov := covolume_eq_index_mul_covolume (α := ℍ) (μ := volume) h
  rw [hΔ.covolume_eq_two_pi_mul_neg_eulerChar_add_cusps,
    hΓ.covolume_eq_two_pi_mul_neg_eulerChar_add_cusps,
    ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)] at hcov
  have hltΔ := hΔ.eulerChar_compactifiedQuotient_lt_finsum_mem_ellipticOrbits_add_cusps
  have hltΓ := hΓ.eulerChar_compactifiedQuotient_lt_finsum_mem_ellipticOrbits_add_cusps
  have hπ := Real.pi_pos
  rw [ENNReal.ofReal_eq_ofReal_iff (by nlinarith) (mul_nonneg (Nat.cast_nonneg _) (by nlinarith))]
    at hcov
  apply mul_left_cancel₀ (by positivity : (2 * Real.pi) ≠ 0)
  linear_combination -hcov

end Subgroup.IsCofinite

open Subgroup TauCeti.RiemannSurface

namespace TauCeti.Fuchsian

variable {Δ Γ : Subgroup PSL(2, ℝ)} [DiscreteTopology Γ]

/-- **The Riemann–Hurwitz formula in Euler-characteristic form** for cofinite Fuchsian groups:
`χ(X(Δ)) = [Γ : Δ] · χ(X(Γ)) - R`. -/
theorem eulerChar_compactifiedQuotient_eq_index_mul_sub_ramificationDegree_of_isCofinite
    (h : Δ ≤ Γ) [Δ.IsFiniteRelIndex Γ] (hΓ : Γ.IsCofinite) :
    letI : DiscreteTopology Δ := DiscreteTopology.of_subset ‹DiscreteTopology Γ› h
    haveI := hΓ.finiteCWType_compactifiedQuotient
    haveI := ((isCofinite_iff_isCofinite_and_finiteIndex h).mpr
      ⟨hΓ, inferInstance⟩).finiteCWType_compactifiedQuotient
    eulerChar Δ.CompactifiedQuotient =
      (Δ.subgroupOf Γ).index * eulerChar Γ.CompactifiedQuotient -
        ramificationDegree (compactifiedQuotientMap h) := by
  let : DiscreteTopology Δ := DiscreteTopology.of_subset ‹DiscreteTopology Γ› h
  have hΔ : Δ.IsCofinite := (isCofinite_iff_isCofinite_and_finiteIndex h).mpr ⟨hΓ, inferInstance⟩
  have := hΓ.finiteCWType_compactifiedQuotient; have := hΔ.finiteCWType_compactifiedQuotient
  have hR := ramificationDegree_eq_index_mul_cusps_add_elliptic_sub h hΓ
  have hχ := hΓ.eulerChar_sub_finsum_mem_ellipticOrbits_sub_cusps_eq_index_mul h
  have hreal : (eulerChar Δ.CompactifiedQuotient : ℝ) =
      (Δ.subgroupOf Γ).index * eulerChar Γ.CompactifiedQuotient -
        ramificationDegree (compactifiedQuotientMap h) := by rw [hR]; linear_combination hχ
  exact_mod_cast hreal

/-- **The Riemann–Hurwitz formula in Euler-characteristic form** with explicit elliptic and cusp
ramification. -/
theorem eulerChar_compactifiedQuotient_eq_index_mul_sub_interior_sub_cusps_of_isCofinite
    (h : Δ ≤ Γ) [Δ.IsFiniteRelIndex Γ] (hΓ : Γ.IsCofinite)
    (z : orbitRel.Quotient Δ ℍ → ℍ) (hz : ∀ q, Quotient.mk'' (z q) = q)
    (c : Δ.CuspOrbit → Δ.cuspPoints) (hc : ∀ C, Δ.cuspOrbitMk (c C) = C) :
    letI : DiscreteTopology Δ := DiscreteTopology.of_subset ‹DiscreteTopology Γ› h
    haveI := hΓ.finiteCWType_compactifiedQuotient
    haveI := ((isCofinite_iff_isCofinite_and_finiteIndex h).mpr
      ⟨hΓ, inferInstance⟩).finiteCWType_compactifiedQuotient
    eulerChar Δ.CompactifiedQuotient =
      (Δ.subgroupOf Γ).index * eulerChar Γ.CompactifiedQuotient -
        (∑ᶠ q : orbitRel.Quotient Δ ℍ, (ellipticRamificationIndex h (z q) - 1) : ℕ) -
        (∑ᶠ C : Δ.CuspOrbit,
          ((Δ.subgroupOf Γ).relIndex (stabilizer Γ (c C : OnePoint ℝ)) - 1) : ℕ) := by
  let : DiscreteTopology Δ := DiscreteTopology.of_subset ‹DiscreteTopology Γ› h
  have hΔ : Δ.IsCofinite := (isCofinite_iff_isCofinite_and_finiteIndex h).mpr ⟨hΓ, inferInstance⟩
  have := hΔ.compactSpace_compactifiedQuotient
  rw [eulerChar_compactifiedQuotient_eq_index_mul_sub_ramificationDegree_of_isCofinite h hΓ,
    ramificationDegree_eq_interior_add_cusps h z hz c hc]
  push_cast; ring

/-- **The Riemann–Hurwitz formula in genus form** for cofinite Fuchsian groups:
`2g(X(Δ)) - 2 = [Γ : Δ] · (2g(X(Γ)) - 2) + R`. -/
theorem two_mul_genus_compactifiedQuotient_sub_two_eq_index_mul_add_ramificationDegree
    (h : Δ ≤ Γ) [Δ.IsFiniteRelIndex Γ] (hΓ : Γ.IsCofinite) :
    letI : DiscreteTopology Δ := DiscreteTopology.of_subset ‹DiscreteTopology Γ› h
    haveI := hΓ.finiteCWType_compactifiedQuotient
    haveI := ((isCofinite_iff_isCofinite_and_finiteIndex h).mpr
      ⟨hΓ, inferInstance⟩).finiteCWType_compactifiedQuotient
    2 * (genus Δ.CompactifiedQuotient : ℤ) - 2 =
      (Δ.subgroupOf Γ).index * (2 * (genus Γ.CompactifiedQuotient : ℤ) - 2) +
        ramificationDegree (compactifiedQuotientMap h) := by
  let : DiscreteTopology Δ := DiscreteTopology.of_subset ‹DiscreteTopology Γ› h
  have hΔ : Δ.IsCofinite := (isCofinite_iff_isCofinite_and_finiteIndex h).mpr ⟨hΓ, inferInstance⟩
  have hχ := eulerChar_compactifiedQuotient_eq_index_mul_sub_ramificationDegree_of_isCofinite h hΓ
  rw [hΔ.eulerChar_compactifiedQuotient_eq_two_sub_two_mul_genus,
    hΓ.eulerChar_compactifiedQuotient_eq_two_sub_two_mul_genus] at hχ
  linarith

/-- **The Riemann–Hurwitz formula in genus form with explicit elliptic and cusp ramification**
(Diamond–Shurman, Theorem 3.1.1). -/
theorem two_mul_genus_compactifiedQuotient_sub_two_eq_index_mul_add_interior_add_cusps
    (h : Δ ≤ Γ) [Δ.IsFiniteRelIndex Γ] (hΓ : Γ.IsCofinite)
    (z : orbitRel.Quotient Δ ℍ → ℍ) (hz : ∀ q, Quotient.mk'' (z q) = q)
    (c : Δ.CuspOrbit → Δ.cuspPoints) (hc : ∀ C, Δ.cuspOrbitMk (c C) = C) :
    letI : DiscreteTopology Δ := DiscreteTopology.of_subset ‹DiscreteTopology Γ› h
    haveI := hΓ.finiteCWType_compactifiedQuotient
    haveI := ((isCofinite_iff_isCofinite_and_finiteIndex h).mpr
      ⟨hΓ, inferInstance⟩).finiteCWType_compactifiedQuotient
    2 * (genus Δ.CompactifiedQuotient : ℤ) - 2 =
      (Δ.subgroupOf Γ).index * (2 * (genus Γ.CompactifiedQuotient : ℤ) - 2) +
        (∑ᶠ q : orbitRel.Quotient Δ ℍ, (ellipticRamificationIndex h (z q) - 1) : ℕ) +
        (∑ᶠ C : Δ.CuspOrbit,
          ((Δ.subgroupOf Γ).relIndex (stabilizer Γ (c C : OnePoint ℝ)) - 1) : ℕ) := by
  let : DiscreteTopology Δ := DiscreteTopology.of_subset ‹DiscreteTopology Γ› h
  have hΔ : Δ.IsCofinite := (isCofinite_iff_isCofinite_and_finiteIndex h).mpr ⟨hΓ, inferInstance⟩
  have := hΔ.compactSpace_compactifiedQuotient
  rw [two_mul_genus_compactifiedQuotient_sub_two_eq_index_mul_add_ramificationDegree h hΓ,
    ramificationDegree_eq_interior_add_cusps h z hz c hc]
  push_cast; ring

end TauCeti.Fuchsian

end
