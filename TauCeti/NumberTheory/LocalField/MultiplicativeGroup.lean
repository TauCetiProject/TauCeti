/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.UnitsDecomposition

/-!
# The multiplicative group of a nonarchimedean local field

Let `K` be a nonarchimedean local field, with normalized valuation `v_K`, integer ring `𝒪[K]`,
residue field `𝓀[K]` of cardinality `q`, and unit filtration `U(K,i)`. This file resolves `Kˣ`
into its three standard pieces:

`TauCeti.unitsEquivProd`, attached to a choice of uniformizer `π`, is the isomorphism

`Kˣ ≃* Multiplicative ℤ × 𝒪[K]ˣ`,

whose first component is `v_K` and whose inverse sends `(n, u)` to `π ^ n * u`, and

`TauCeti.integerUnitsEquivProd`, which needs no choice, is the isomorphism

`𝒪[K]ˣ ≃* 𝓀[K]ˣ × U(K,1)`,

whose first component is reduction and whose inverse sends `(α, y)` to `ω(α) * y`, where `ω` is
the Teichmüller lift. Since `ω` identifies `𝓀[K]ˣ` with the group `μ_{q-1}` of `(q-1)`-st roots
of unity of `𝒪[K]` (`TauCeti.range_teichmuller`), the second isomorphism is the
splitting of the units of `𝒪[K]` into their prime-to-`p` torsion and the principal units.

Both splittings come from the same mechanism: an exact sequence of abelian groups with a
distinguished section. For the first, the surjection is `v_K`, whose kernel is `U(K,0)`
(`TauCeti.ker_normalizedValuation`), and the section is `n ↦ π ^ n`; the dependence on `π` is
confined to that section, and the first component of the splitting is `v_K` no matter which
uniformizer is chosen. For the second, the surjection is reduction `𝒪[K]ˣ → 𝓀[K]ˣ`, whose
kernel is `U(K,1)` (`TauCeti.mem_unitFiltration_one_iff_residue_eq_one`), and the section is the
Teichmüller lift.

Together the two reduce every multiplicative question about `K` to one about `ℤ`, about the
finite group `𝓀[K]ˣ`, and about the principal units `U(K,1)`, whose own structure is read off
the graded pieces of the unit filtration. This is the shape used to count power classes
`Kˣ / (Kˣ)ⁿ` and to compute norm groups.

## Main definitions

* `TauCeti.unitsProdHom` and `TauCeti.unitsEquivProd`: the splitting
  `Kˣ ≃* Multiplicative ℤ × 𝒪[K]ˣ` attached to a uniformizer.
* `TauCeti.integerUnitsProdHom` and `TauCeti.integerUnitsEquivProd`: the Teichmüller splitting
  `𝒪[K]ˣ ≃* 𝓀[K]ˣ × U(K,1)`.

## Main results

* `TauCeti.ker_normalizedValuation`: the kernel of the normalized valuation is `U(K,0)`.
* `TauCeti.fst_unitsEquivProd`: the `ℤ`-component of the first splitting is the normalized
  valuation; in particular it does not depend on the uniformizer.
* `TauCeti.fst_integerUnitsEquivProd`: the `𝓀[K]ˣ`-component of the second splitting is
  reduction.
* `TauCeti.unitsMap_subtype_snd_unitsEquivProd` and
  `TauCeti.unitFiltrationToIntegerUnits_snd_integerUnitsEquivProd`: the remaining components,
  which are what is left after dividing by the image of the section.

## References

* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter II, §§4–5.
* J. Neukirch, *Algebraic Number Theory*, Chapter II, §5.
-/

public section

noncomputable section

open IsLocalRing ValuativeRel IsNonarchimedeanLocalField

namespace TauCeti

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

-- Provenance: the multiplicative decomposition below follows the human-authored specification
-- in `TauCetiRoadmap/LocalFieldsRamification/Suggested.lean`.
/-! ### The kernel of the normalized valuation -/

attribute [simp] ker_normalizedValuation

/-- The normalized valuation is trivial on the units of `𝒪[K]`. -/
@[simp]
theorem normalizedValuation_integerUnits (u : 𝒪[K]ˣ) :
    normalizedValuation K (Units.map (Subring.subtype 𝒪[K] : 𝒪[K] →* K) u) = 1 := by
  rw [← MonoidHom.mem_ker, ker_normalizedValuation]
  exact mem_unitFiltration_iff_exists.mpr ⟨u, by simp, rfl⟩

/-! ### The valuation splitting `Kˣ ≃ ℤ × 𝒪[K]ˣ` -/

section Uniformizer

variable {π : 𝒪[K]}

/-- The homomorphism `(n, u) ↦ π ^ n * u` out of `Multiplicative ℤ × 𝒪[K]ˣ`, built from a
uniformizer `π` of `K`. It is the section-and-inclusion map of the exact sequence
`1 → 𝒪[K]ˣ → Kˣ → ℤ → 1`, and `unitsProdHom_bijective` shows that it splits it. -/
def unitsProdHom (hπ : Irreducible π) : Multiplicative ℤ × 𝒪[K]ˣ →* Kˣ :=
  (zpowersHom Kˣ (Units.mk0 (π : K) fun h ↦ hπ.ne_zero (Subtype.ext h))).coprod
    (Units.map (Subring.subtype 𝒪[K] : 𝒪[K] →* K))

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- The defining formula of `unitsProdHom`. -/
@[simp]
theorem unitsProdHom_apply (hπ : Irreducible π) (p : Multiplicative ℤ × 𝒪[K]ˣ) :
    unitsProdHom hπ p =
      (Units.mk0 (π : K) fun h ↦ hπ.ne_zero (Subtype.ext h)) ^ p.1.toAdd *
        Units.map (Subring.subtype 𝒪[K] : 𝒪[K] →* K) p.2 := (rfl)

/-- **A uniformizer splits `Kˣ`.** Every unit of `K` is uniquely `π ^ n * u` with `n : ℤ` and
`u` a unit of `𝒪[K]`. -/
theorem unitsProdHom_bijective (hπ : Irreducible π) :
    Function.Bijective (unitsProdHom hπ) := by
  refine ⟨?_, ?_⟩
  · rw [injective_iff_map_eq_one]
    rintro ⟨n, u⟩ hnu
    rw [unitsProdHom_apply] at hnu
    -- The valuation of the product reads off the `ℤ`-coordinate, since `u` has valuation `0`.
    have hv := congrArg (normalizedValuation K) hnu
    simp only [map_mul, map_zpow, map_one, normalizedValuation_irreducible hπ,
      normalizedValuation_integerUnits u, mul_one] at hv
    have hn : n = 1 := Multiplicative.toAdd.injective (by simpa using hv)
    subst hn
    have hu : u = 1 := Units.map_injective (f := (Subring.subtype 𝒪[K] : 𝒪[K] →* K))
      Subtype.coe_injective (by simpa using hnu)
    simp [hu]
  · intro x
    obtain ⟨u, n, hu, rfl⟩ := exists_eq_mul_zpow_of_irreducible hπ x
    obtain ⟨w, -, hw⟩ := mem_unitFiltration_iff_exists.mp ((mem_unitFiltration_zero u).mpr hu)
    have hwu : Units.map (Subring.subtype 𝒪[K] : 𝒪[K] →* K) w = u := Units.ext hw
    refine ⟨(Multiplicative.ofAdd n, w), ?_⟩
    rw [unitsProdHom_apply, hwu]
    simp [mul_comm]

/-- **The multiplicative group of a local field, split by a uniformizer**: `Kˣ` is the product
of `ℤ`, through the normalized valuation, and the units of `𝒪[K]`. The isomorphism depends on
the uniformizer `π` only through its inverse `unitsEquivProd_symm_apply`; its first component is
`normalizedValuation K`, by `fst_unitsEquivProd`. -/
def unitsEquivProd (hπ : Irreducible π) : Kˣ ≃* Multiplicative ℤ × 𝒪[K]ˣ :=
  (MulEquiv.ofBijective _ (unitsProdHom_bijective hπ)).symm

/-- The inverse of the splitting attached to `π` is `(n, u) ↦ π ^ n * u`. -/
@[simp]
theorem unitsEquivProd_symm_apply (hπ : Irreducible π) (p : Multiplicative ℤ × 𝒪[K]ˣ) :
    (unitsEquivProd hπ).symm p = unitsProdHom hπ p := (rfl)

/-- The `ℤ`-component of the splitting attached to a uniformizer is the normalized valuation.
In particular it is the same for every uniformizer. -/
@[simp]
theorem fst_unitsEquivProd (hπ : Irreducible π) (x : Kˣ) :
    (unitsEquivProd hπ x).1 = normalizedValuation K x := by
  conv_rhs => rw [← (unitsEquivProd hπ).symm_apply_apply x]
  rw [unitsEquivProd_symm_apply, unitsProdHom_apply, map_mul, map_zpow,
    normalizedValuation_irreducible hπ, normalizedValuation_integerUnits, mul_one]
  simp [← ofAdd_zsmul]

/-- The `𝒪[K]ˣ`-component of the splitting attached to `π` is `x` divided by `π ^ v_K(x)`. -/
@[simp]
theorem unitsMap_subtype_snd_unitsEquivProd (hπ : Irreducible π) (x : Kˣ) :
    Units.map (Subring.subtype 𝒪[K] : 𝒪[K] →* K) (unitsEquivProd hπ x).2 =
      x * (Units.mk0 (π : K) fun h ↦ hπ.ne_zero (Subtype.ext h)) ^
        (-(normalizedValuation K x).toAdd) := by
  have h := (unitsEquivProd hπ).symm_apply_apply x
  rw [unitsEquivProd_symm_apply, unitsProdHom_apply, fst_unitsEquivProd] at h
  rw [zpow_neg, eq_mul_inv_iff_mul_eq, mul_comm]
  exact h

end Uniformizer

/-! ### The Teichmüller splitting `𝒪[K]ˣ ≃ 𝓀[K]ˣ × U(K,1)` -/

section Teichmuller

/-- The homomorphism `(α, y) ↦ ω(α) * y` out of `𝓀[K]ˣ × U(K,1)`, where `ω` is the Teichmüller
lift. It is the section-and-inclusion map of the reduction sequence
`1 → U(K,1) → 𝒪[K]ˣ → 𝓀[K]ˣ → 1`, and `integerUnitsProdHom_bijective` shows that it splits
it. -/
def integerUnitsProdHom : 𝓀[K]ˣ × unitFiltration K 1 →* 𝒪[K]ˣ :=
  (TauCeti.teichmuller 𝒪[K]).coprod (unitFiltrationToIntegerUnits 1)

/-- The defining formula of `integerUnitsProdHom`. -/
@[simp]
theorem integerUnitsProdHom_apply (p : 𝓀[K]ˣ × unitFiltration K 1) :
    integerUnitsProdHom p =
      TauCeti.teichmuller 𝒪[K] p.1 * unitFiltrationToIntegerUnits 1 p.2 :=
  by simp [integerUnitsProdHom]

/-- **The Teichmüller lift splits the units of `𝒪[K]`.** Every unit of `𝒪[K]` is uniquely the
product of a `(q-1)`-st root of unity and a principal unit. -/
theorem integerUnitsProdHom_bijective :
    Function.Bijective (integerUnitsProdHom (K := K)) := by
  refine ⟨?_, ?_⟩
  · rw [injective_iff_map_eq_one]
    intro p h
    rw [integerUnitsProdHom_apply] at h
    -- Reduction reads off the `𝓀[K]ˣ`-coordinate, since the other factor reduces to `1`.
    have hres := congrArg (Units.map (residue 𝒪[K] : 𝒪[K] →* 𝓀[K])) h
    rw [map_mul, unitsMap_residue_unitFiltrationToIntegerUnits_one, mul_one, map_one,
      TauCeti.unitsMap_residue_teichmuller] at hres
    rw [hres, map_one, one_mul] at h
    exact Prod.ext hres (unitFiltrationToIntegerUnits_injective 1 (by simp [h]))
  · intro u
    set α := Units.map (residue 𝒪[K] : 𝒪[K] →* 𝓀[K]) u with hα
    have hw : Units.map (residue 𝒪[K] : 𝒪[K] →* 𝓀[K])
        ((TauCeti.teichmuller 𝒪[K] α)⁻¹ * u) = 1 := by
      rw [map_mul, map_inv, TauCeti.unitsMap_residue_teichmuller, ← hα,
        inv_mul_cancel]
    have hres : residue 𝒪[K]
        ((((TauCeti.teichmuller 𝒪[K] α)⁻¹ * u : 𝒪[K]ˣ) : 𝒪[K])) = 1 := by
      simpa using congrArg Units.val hw
    have hmem : Units.map (Subring.subtype 𝒪[K] : 𝒪[K] →* K)
        ((TauCeti.teichmuller 𝒪[K] α)⁻¹ * u) ∈ unitFiltration K 1 :=
      (mem_unitFiltration_one_iff_residue_eq_one _).mpr hres
    refine ⟨(α, ⟨_, hmem⟩), ?_⟩
    have hcoe : unitFiltrationToIntegerUnits 1 (⟨_, hmem⟩ : unitFiltration K 1) =
        (TauCeti.teichmuller 𝒪[K] α)⁻¹ * u :=
      Units.map_injective (f := (Subring.subtype 𝒪[K] : 𝒪[K] →* K)) Subtype.coe_injective
        (by rw [unitsMap_subtype_unitFiltrationToIntegerUnits])
    rw [integerUnitsProdHom_apply, hcoe]
    group

/-- **The units of the integer ring of a local field, split by the Teichmüller lift**: `𝒪[K]ˣ`
is the product of the multiplicative group of the residue field, through reduction, and the
principal units `U(K,1)`. The residue-field factor is carried by the `(q-1)`-st roots of unity
of `𝒪[K]`, which `TauCeti.range_teichmuller` identifies with the image of the lift. -/
def integerUnitsEquivProd : 𝒪[K]ˣ ≃* 𝓀[K]ˣ × unitFiltration K 1 :=
  (MulEquiv.ofBijective _ integerUnitsProdHom_bijective).symm

/-- The inverse of the Teichmüller splitting is `(α, y) ↦ ω(α) * y`. -/
@[simp]
theorem integerUnitsEquivProd_symm_apply (p : 𝓀[K]ˣ × unitFiltration K 1) :
    (integerUnitsEquivProd (K := K)).symm p = integerUnitsProdHom p := (rfl)

/-- The residue-field component of the Teichmüller splitting is reduction. -/
@[simp]
theorem fst_integerUnitsEquivProd (u : 𝒪[K]ˣ) :
    (integerUnitsEquivProd u).1 = Units.map (residue 𝒪[K] : 𝒪[K] →* 𝓀[K]) u := by
  conv_rhs => rw [← (integerUnitsEquivProd (K := K)).symm_apply_apply u]
  rw [integerUnitsEquivProd_symm_apply, integerUnitsProdHom_apply, map_mul,
    unitsMap_residue_unitFiltrationToIntegerUnits_one, mul_one,
    TauCeti.unitsMap_residue_teichmuller]

/-- The principal-unit component of the Teichmüller splitting is `u` divided by the Teichmüller
representative of its residue. -/
@[simp]
theorem unitFiltrationToIntegerUnits_snd_integerUnitsEquivProd (u : 𝒪[K]ˣ) :
    unitFiltrationToIntegerUnits 1 (integerUnitsEquivProd u).2 =
      (TauCeti.teichmuller 𝒪[K]
        (Units.map (residue 𝒪[K] : 𝒪[K] →* 𝓀[K]) u))⁻¹ * u := by
  have h := (integerUnitsEquivProd (K := K)).symm_apply_apply u
  rw [integerUnitsEquivProd_symm_apply, integerUnitsProdHom_apply,
    fst_integerUnitsEquivProd] at h
  rw [eq_inv_mul_iff_mul_eq]
  exact h

end Teichmuller

end TauCeti
