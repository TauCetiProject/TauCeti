/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Fuchsian.Compactification.Cocompact
public import TauCeti.Analysis.Complex.Fuchsian.Compactification.RamificationDegree
public import TauCeti.Analysis.Complex.Fuchsian.DirichletDomain.SidePairing
public import TauCeti.Analysis.Complex.Fuchsian.Polygon.EulerCharacteristic

/-!
# The Euler characteristic and area of a cocompact Fuchsian group

Let `Γ ≤ PSL(2, ℝ)` be discrete with compact orbit space `Γ \ ℍ`. Then `Γ` has no cusps, so its
compactified quotient `X(Γ)` is `Γ \ ℍ` itself, with the same complex structure
(`Subgroup.CompactifiedQuotient.ofQuotientBiholomorph`). A Dirichlet domain of `Γ` centred at a
point with trivial stabilizer is a compact convex polygon, whose side pairing by elements of `Γ`
has locally finite translates with disjoint interiors. The cell structure that such a fundamental
polygon induces on `Γ \ ℍ` shows that `X(Γ)` has finite CW type, and the orbifold area formula
for that polygon becomes an intrinsic statement about `Γ`:

`covolume Γ = 2π (-χ(X(Γ)) + ∑ₑ (1 - 1 / mₑ))`,

the sum running over the elliptic orbits of `Γ`, with stabilizer orders `mₑ`. Writing
`χ(X(Γ)) = 2 - 2g` for the topological genus `g` of the compact Riemann surface `X(Γ)`, this is
the signature form `2π (2g - 2 + ∑ₑ (1 - 1 / mₑ))` of the area of a cocompact group. Since the
covolume is positive, the signature satisfies the hyperbolicity inequality
`χ(X(Γ)) < ∑ₑ (1 - 1 / mₑ)`, that is, `2g - 2 + ∑ₑ (1 - 1 / mₑ) > 0`.

For a subgroup `Δ ≤ Γ` of finite index, `Δ` is again cocompact
(`Subgroup.compactSpace_orbitRel_quotient_of_le`), and covolume is multiplicative
in the index. The area formula therefore makes the orbifold Euler characteristic
`χ(X(Γ)) - ∑ₑ (1 - 1 / mₑ)` multiplicative in the index. Combined with the expression of the
ramification degree of `X(Δ) → X(Γ)` through elliptic orders
(`TauCeti.Fuchsian.ramificationDegree_eq_index_mul_cusps_add_elliptic_sub`), this gives the
Riemann–Hurwitz formula `χ(X(Δ)) = [Γ : Δ] · χ(X(Γ)) - R` for cocompact groups without any
finite-CW-type hypothesis; the general form
`TauCeti.Fuchsian.eulerChar_compactifiedQuotient_eq_index_mul_sub_ramificationDegree` also asks
for finite CW type of the free-locus quotient.

## Main results

* `Subgroup.finiteCWType_orbitRel_quotient`: a cocompact Fuchsian group has a coarse quotient of
  finite CW type.
* `Subgroup.finiteCWType_compactifiedQuotient`: the same for its compactified quotient.
* `Subgroup.eulerChar_compactifiedQuotient_eq_eulerChar_orbitRel_quotient`:
  `χ(X(Γ)) = χ(Γ \ ℍ)`.
* `Subgroup.covolume_eq_two_pi_mul_neg_eulerChar_add`: the orbifold area formula
  `covolume Γ = 2π (-χ(X(Γ)) + ∑ₑ (1 - 1 / mₑ))`.
* `Subgroup.eulerChar_compactifiedQuotient_lt_finsum_mem_ellipticOrbits`: the hyperbolicity
  inequality `χ(X(Γ)) < ∑ₑ (1 - 1 / mₑ)`.
* `Subgroup.eulerChar_sub_finsum_mem_ellipticOrbits_eq_index_mul`: multiplicativity of the
  orbifold Euler characteristic.
* `Fuchsian.eulerChar_compactifiedQuotient_eq_index_mul_sub_ramificationDegree_of_compactSpace`:
  the Riemann–Hurwitz formula for cocompact Fuchsian groups.

## References

* Svetlana Katok, *Fuchsian Groups*, Chicago Lectures in Mathematics, University of Chicago
  Press, 1992, §§4.2–4.3 (the signature and the area of a cocompact Fuchsian group).
* Alan Beardon, *The Geometry of Discrete Groups*, Graduate Texts in Mathematics 91, Springer,
  1983, §10.4 (the area of a fundamental polygon and the signature).
-/

public section

noncomputable section

open MeasureTheory MulAction Set UpperHalfPlane TauCeti TauCeti.UpperHalfPlane
open scoped MatrixGroups Pointwise Real

namespace Subgroup

variable {Γ : Subgroup PSL(2, ℝ)} [DiscreteTopology Γ] [CompactSpace (orbitRel.Quotient Γ ℍ)]

/-- A cocompact Fuchsian group has a compact fundamental polygon: a Dirichlet polygon centred at
a point with trivial stabilizer, with its side pairing by elements of `Γ`, whose translates are
locally finite and have pairwise disjoint interiors. These are the hypotheses of the cell
structure in `TauCeti.UpperHalfPlane.ConvexPolygon.SidePairing.finiteCWType_orbitRel_quotient`. -/
private theorem exists_compactConvexPolygon_sidePairing :
    ∃ (n : ℕ) (_ : NeZero n) (P : CompactConvexPolygon n) (σ : P.toConvexPolygon.SidePairing),
      (∀ i, σ.map i ∈ Γ) ∧
      (LocallyFinite fun γ : Γ ↦ (γ : PSL(2, ℝ)) • P.toConvexPolygon.carrier) ∧
      ∀ γ : Γ, γ ≠ 1 → Disjoint ((γ : PSL(2, ℝ)) • interior P.toConvexPolygon.carrier)
        (interior P.toConvexPolygon.carrier) := by
  obtain ⟨p, hp⟩ := freeLocus_nonempty Γ
  obtain ⟨n, _, P, σ, hσ, hP⟩ := Γ.exists_sidePairing_of_compactSpace hp
  exact ⟨n, ‹_›, P, σ, hσ, hP ▸ locallyFinite_smul_dirichletDomain p,
    ConvexPolygon.disjoint_smul_interior_carrier_of_carrier_eq_dirichletDomain hP hp⟩

/-- **The quotient of a cocompact Fuchsian group has finite CW type**, through the cell structure
induced by a compact Dirichlet polygon. -/
instance finiteCWType_orbitRel_quotient : FiniteCWType (orbitRel.Quotient Γ ℍ) := by
  obtain ⟨n, _, P, σ, hmap, hlf, hdisj⟩ := exists_compactConvexPolygon_sidePairing (Γ := Γ)
  exact σ.finiteCWType_orbitRel_quotient hmap hlf hdisj

/-- **The compactified quotient of a cocompact Fuchsian group has finite CW type.** It has no
cusps, so it is homeomorphic to the coarse quotient. -/
instance finiteCWType_compactifiedQuotient : FiniteCWType Γ.CompactifiedQuotient :=
  have := CompactifiedQuotient.isEmpty_cuspOrbit_of_compactSpace (Γ := Γ)
  CompactifiedQuotient.ofQuotientBiholomorph.toHomeomorph.symm.finiteCWType

/-- For a cocompact Fuchsian group, the compactified quotient and the coarse quotient have the
same Euler characteristic: no cusp is adjoined. -/
theorem eulerChar_compactifiedQuotient_eq_eulerChar_orbitRel_quotient :
    eulerChar Γ.CompactifiedQuotient = eulerChar (orbitRel.Quotient Γ ℍ) :=
  have := CompactifiedQuotient.isEmpty_cuspOrbit_of_compactSpace (Γ := Γ)
  CompactifiedQuotient.ofQuotientBiholomorph.toHomeomorph.eulerChar_eq.symm

/-- **The orbifold area formula for a cocompact Fuchsian group.** The covolume of `Γ` is
`2π (-χ(X(Γ)) + ∑ₑ (1 - 1 / mₑ))`, where `X(Γ)` is the compactified quotient, of finite CW type,
and `e` runs over the elliptic orbits of `Γ`, with stabilizer orders `mₑ`. With `χ = 2 - 2g`
this is `2π (2g - 2 + ∑ₑ (1 - 1 / mₑ))`. -/
theorem covolume_eq_two_pi_mul_neg_eulerChar_add :
    covolume Γ ℍ = ENNReal.ofReal (2 * π * (-(eulerChar Γ.CompactifiedQuotient : ℝ) +
      ∑ᶠ e ∈ Γ.ellipticOrbits, (1 - (cardStabilizerOnOrbit e : ℝ)⁻¹))) := by
  obtain ⟨n, _, P, σ, hmap, hlf, hdisj⟩ := exists_compactConvexPolygon_sidePairing (Γ := Γ)
  rw [σ.covolume_eq_two_pi_mul_neg_eulerChar_add hmap hlf hdisj,
    eulerChar_compactifiedQuotient_eq_eulerChar_orbitRel_quotient]

/-- **The hyperbolicity inequality for the signature of a cocompact Fuchsian group.** The Euler
characteristic of the compactified quotient is less than `∑ₑ (1 - 1 / mₑ)`, the sum running over
the elliptic orbits with stabilizer orders `mₑ`. With `χ = 2 - 2g` this is
`2g - 2 + ∑ₑ (1 - 1 / mₑ) > 0`: the area of a cocompact group is positive. -/
theorem eulerChar_compactifiedQuotient_lt_finsum_mem_ellipticOrbits :
    (eulerChar Γ.CompactifiedQuotient : ℝ) <
      ∑ᶠ e ∈ Γ.ellipticOrbits, (1 - (cardStabilizerOnOrbit e : ℝ)⁻¹) := by
  have hpos : 0 < covolume Γ ℍ := covolume_pos <|
    Measure.measure_univ_pos.mp (isOpen_univ.measure_pos volume univ_nonempty)
  rw [covolume_eq_two_pi_mul_neg_eulerChar_add, ENNReal.ofReal_pos] at hpos
  nlinarith [Real.pi_pos]

/-- **Multiplicativity of the orbifold Euler characteristic for cocompact groups.** Let `Γ` be a
cocompact Fuchsian group and `Δ ≤ Γ` a subgroup of finite index, so that `Δ` is cocompact as
well. Then `χ(X(Δ)) - ∑ₑ (1 - 1 / mₑ) = [Γ : Δ] · (χ(X(Γ)) - ∑ₑ (1 - 1 / mₑ))`, each sum running
over the elliptic orbits of the respective group with stabilizer orders `mₑ`. Both sides are
`-1 / 2π` times a covolume, and covolume is multiplicative in the index. -/
theorem eulerChar_sub_finsum_mem_ellipticOrbits_eq_index_mul {Δ : Subgroup PSL(2, ℝ)}
    (h : Δ ≤ Γ) [Δ.IsFiniteRelIndex Γ] :
    letI : DiscreteTopology Δ := DiscreteTopology.of_subset ‹DiscreteTopology Γ› h
    haveI := compactSpace_orbitRel_quotient_of_le h
    (eulerChar Δ.CompactifiedQuotient : ℝ) -
        ∑ᶠ e ∈ Δ.ellipticOrbits, (1 - (cardStabilizerOnOrbit e : ℝ)⁻¹) =
      (Δ.subgroupOf Γ).index * ((eulerChar Γ.CompactifiedQuotient : ℝ) -
        ∑ᶠ e ∈ Γ.ellipticOrbits, (1 - (cardStabilizerOnOrbit e : ℝ)⁻¹)) := by
  let : DiscreteTopology Δ := DiscreteTopology.of_subset ‹DiscreteTopology Γ› h
  have := compactSpace_orbitRel_quotient_of_le h
  have hcov := covolume_eq_index_mul_covolume (α := ℍ) (μ := volume) h
  rw [covolume_eq_two_pi_mul_neg_eulerChar_add, covolume_eq_two_pi_mul_neg_eulerChar_add,
    ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)] at hcov
  have hΔ := eulerChar_compactifiedQuotient_lt_finsum_mem_ellipticOrbits (Γ := Δ)
  have hΓ := eulerChar_compactifiedQuotient_lt_finsum_mem_ellipticOrbits (Γ := Γ)
  have hπ := Real.pi_pos
  rw [ENNReal.ofReal_eq_ofReal_iff (by nlinarith) (mul_nonneg (Nat.cast_nonneg _) (by nlinarith))]
    at hcov
  apply mul_left_cancel₀ (by positivity : (2 * π) ≠ 0)
  linear_combination -hcov

end Subgroup

open Subgroup Subgroup.CompactifiedQuotient TauCeti.RiemannSurface

namespace TauCeti.Fuchsian

variable {Δ Γ : Subgroup PSL(2, ℝ)} [DiscreteTopology Γ] [CompactSpace (orbitRel.Quotient Γ ℍ)]

/-- **The Riemann–Hurwitz formula for cocompact Fuchsian groups.** Let `Δ ≤ Γ` be discrete
subgroups of `PSL(2, ℝ)` of finite index, with `Γ \ ℍ` compact. Then
`χ(X(Δ)) = [Γ : Δ] · χ(X(Γ)) - R`, where `R` is the ramification degree of `X(Δ) → X(Γ)`. Unlike
`TauCeti.Fuchsian.eulerChar_compactifiedQuotient_eq_index_mul_sub_ramificationDegree`, this carries
no finite-CW-type hypotheses: both compactified quotients have finite CW type, and the formula
follows from multiplicativity of the orbifold Euler characteristic together with the expression
of `R` through elliptic orders. -/
theorem eulerChar_compactifiedQuotient_eq_index_mul_sub_ramificationDegree_of_compactSpace
    (h : Δ ≤ Γ) [Δ.IsFiniteRelIndex Γ] :
    letI : DiscreteTopology Δ := DiscreteTopology.of_subset ‹DiscreteTopology Γ› h
    haveI := compactSpace_orbitRel_quotient_of_le h
    eulerChar Δ.CompactifiedQuotient =
      (Δ.subgroupOf Γ).index * eulerChar Γ.CompactifiedQuotient -
        ramificationDegree (compactifiedQuotientMap h) := by
  let : DiscreteTopology Δ := DiscreteTopology.of_subset ‹DiscreteTopology Γ› h
  have := compactSpace_orbitRel_quotient_of_le h
  have := CompactifiedQuotient.isEmpty_cuspOrbit_of_compactSpace (Γ := Γ)
  have := CompactifiedQuotient.isEmpty_cuspOrbit_of_compactSpace (Γ := Δ)
  have hR := ramificationDegree_eq_index_mul_cusps_add_elliptic_sub h isCofinite_of_compactSpace
  have hχ := eulerChar_sub_finsum_mem_ellipticOrbits_eq_index_mul h
  rw [Nat.card_of_isEmpty, Nat.card_of_isEmpty] at hR
  have : (eulerChar Δ.CompactifiedQuotient : ℝ) =
      (Δ.subgroupOf Γ).index * eulerChar Γ.CompactifiedQuotient -
        ramificationDegree (compactifiedQuotientMap h) := by
    rw [hR]
    linear_combination hχ
  exact_mod_cast this

end TauCeti.Fuchsian
