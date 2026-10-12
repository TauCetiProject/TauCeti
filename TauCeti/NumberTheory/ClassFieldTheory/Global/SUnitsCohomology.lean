/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex, Claude
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Global.IdeleClass.SIdeles
public import TauCeti.NumberTheory.ClassFieldTheory.Global.PlacePermutation.Basic
public import TauCeti.RepresentationTheory.Homological.TateCohomology.FiniteGeneration
import Mathlib.NumberTheory.NumberField.ClassNumber
import TauCeti.NumberTheory.NumberField.Units.SUnit

/-!
# Tate cohomology of `S`-units

For a finite set `S` of finite places of a number field `K` and an extension of number fields
`L/K`, the `S`-units `U_{L,S}` of `L` are finitely generated. Consequently their degree-zero and
degree-minus-one Tate cohomology groups are finite. These are the finiteness inputs in the short
exact sequence `U_{L,S} → I_{L,S} → C_L` used to compute the Herbrand quotient of idele classes.

The file then computes the Herbrand quotient of the `S`-units from that of the group `U_{L,∅}` of
units at every finite place, which `Set.unitEmptyEquivUnits` identifies with `(𝓞 L)ˣ`. Recording
at each prime `w` of `L` above `S` the valuation of an `S`-unit (`Set.unitValuation`) gives an
exact sequence of representations of `Aut(L/K)`

```text
0 → U_{L,∅} → U_{L,S} → ℤ[S_L],
```

where `ℤ[S_L]` is the permutation lattice on the primes of `L` above `S`. The last map has finite
cokernel: the class number of `L` kills the class of every prime, so its multiple of every vector
of `ℤ[S_L]` is the valuation vector of an `S`-unit. When the group of `K`-automorphisms of `L` is
cyclic the Herbrand quotient is therefore multiplicative along the sequence
(`herbrandQuotient_sUnitsRep_eq_mul`), and for a cyclic Galois extension the permutation lattice
contributes the local degrees (`herbrandQuotient_sUnitsRep`):

```text
h(U_{L,S}) = h(U_{L,∅}) · ∏_{v ∈ S} [L_w : K_v].
```

This is the finite-place part of the Herbrand quotient of the `S`-units, which enters the
computation of the Herbrand quotient `h(C_L) = [L : K]` of the idele classes. The quotient formula
`h(C_L) = h(I_{L,S}) / h(U_{L,S})`, for `S` whose primes generate the class group of `L`, is
`herbrandQuotient_ideleClassRep`.

## Main results

* `TauCeti.ClassFieldTheory.finite_tateCohomology_zero_sUnitsRep` and
  `TauCeti.ClassFieldTheory.finite_tateCohomology_negOne_sUnitsRep`: the low-degree Tate groups of
  the `S`-units are finite.
* `TauCeti.ClassFieldTheory.herbrandQuotient_sUnitsRep_eq_mul`: when `Aut(L/K)` is cyclic,
  `h(U_{L,S}) = h(U_{L,∅}) · h(ℤ[S_L])`.
* `TauCeti.ClassFieldTheory.herbrandQuotient_sUnitsRep`: for cyclic Galois `L/K`,
  `h(U_{L,S}) = h(U_{L,∅}) · ∏_{v ∈ S} [L_w : K_v]`.

## References

* J. S. Milne, *Class Field Theory*, Chapter VII, §3.
* J. Tate, *Global class field theory*, in J. W. S. Cassels and A. Fröhlich (eds.),
  *Algebraic Number Theory*, Chapter VII, §6.
-/

public noncomputable section

open CategoryTheory CategoryTheory.Limits IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
  NumberField
open scoped Pointwise

namespace TauCeti.ClassFieldTheory

open GlobalNumberFields

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

section Set

variable (S : Set (HeightOneSpectrum (𝓞 K)))

section Finiteness

variable [Finite S]

/-- The integral representation on the `S`-units of `L` is finitely generated when `S` is
finite. -/
theorem moduleFinite_sUnitsRep : Module.Finite ℤ (sUnitsRep L S) := by
  let : Finite ↥(HeightOneSpectrum.primesAbove (𝓞 K) (𝓞 L) S) :=
    (HeightOneSpectrum.primesAbove_finite (𝓞 K) (𝓞 L) (Set.toFinite S)).to_subtype
  have hfg : AddGroup.FG
      (Additive ((HeightOneSpectrum.primesAbove (𝓞 K) (𝓞 L) S).unit L)) :=
    AddGroup.fg_iff_mul_fg.mpr inferInstance
  exact Module.Finite.iff_addGroup_fg.mpr hfg

/-- The degree-zero Tate cohomology of the `S`-units is finite. -/
theorem finite_tateCohomology_zero_sUnitsRep :
    Finite (tateCohomology (sUnitsRep L S) 0) := by
  have := moduleFinite_sUnitsRep (L := L) S
  exact TateCohomology.finite_tateCohomology_zero_of_moduleFinite (sUnitsRep L S)

/-- The degree-minus-one Tate cohomology of the `S`-units is finite. -/
theorem finite_tateCohomology_negOne_sUnitsRep :
    Finite (tateCohomology (sUnitsRep L S) (-1)) := by
  have := moduleFinite_sUnitsRep (L := L) S
  exact TateCohomology.finite_tateCohomology_negOne_of_moduleFinite (sUnitsRep L S)

end Finiteness

/-! ### The valuation sequence -/

section Valuation

omit [NumberField K] in
variable (L) in
private theorem unit_primesAbove_empty_le :
    (primesAbove (𝓞 K) (𝓞 L) ∅).unit L ≤ (primesAbove (𝓞 K) (𝓞 L) S).unit L :=
  Set.unit_mono L (primesAbove_mono (𝓞 K) (𝓞 L) (Set.empty_subset S))

variable (L) in
/-- The inclusion `U_{L,∅} → U_{L,S}` of the units at every finite place into the `S`-units. -/
private def unitsToSUnits : sUnitsRep L ∅ ⟶ sUnitsRep L S :=
  Rep.ofHom <| LinearMap.intertwiningMap_of_isIntertwiningMap _ _
    (Subgroup.inclusion (unit_primesAbove_empty_le L S)).toAdditive.toIntLinearMap
      fun _ _ ↦ (rfl)

/-- An automorphism `σ` carries the valuation at `σ⁻¹ • w` to the valuation at `w`. -/
private theorem valuation_apply_smul (σ : L ≃ₐ[K] L) (w : ↥(primesAbove (𝓞 K) (𝓞 L) S))
    (x : L) : w.1.valuation L (σ x) = (σ⁻¹ • w).1.valuation L x :=
  valuation_apply_eq_of_asIdeal_eq_smul σ (by
    rw [asIdeal_smul_primesAbove_ringOfIntegers, smul_inv_smul]) x

variable [Finite S]

variable (L) in
/-- The valuation map `U_{L,S} → ℤ[S_L]`, Mathlib's `Set.unitValuation` at the primes of `L`
above `S` read additively. -/
private def sUnitsValuationHom :
    Additive ((primesAbove (𝓞 K) (𝓞 L) S).unit L) →+
      MonoidAlgebra ℤ ↥(primesAbove (𝓞 K) (𝓞 L) S) :=
  haveI := (primesAbove_finite (𝓞 K) (𝓞 L) (Set.toFinite S)).to_subtype
  { toFun x := MonoidAlgebra.ofCoeff <| Finsupp.equivFunOnFinite.symm fun w ↦
      Multiplicative.toAdd (Set.unitValuation _ L x.toMul w)
    map_zero' := by
      ext w
      simp
    map_add' x y := by
      ext w
      simp }

omit [NumberField K] in
private theorem coeff_sUnitsValuationHom (x : Additive ((primesAbove (𝓞 K) (𝓞 L) S).unit L))
    (w : ↥(primesAbove (𝓞 K) (𝓞 L) S)) :
    (sUnitsValuationHom L S x).coeff w =
      Multiplicative.toAdd (Set.unitValuation _ L x.toMul w) := by
  simp [sUnitsValuationHom]

variable (L) in
/-- The valuation map `U_{L,S} → ℤ[S_L]` as a morphism of representations of `Aut(L/K)`. -/
private def sUnitsValuation :
    sUnitsRep L S ⟶ Rep.ofMulAction ℤ (L ≃ₐ[K] L) ↥(primesAbove (𝓞 K) (𝓞 L) S) :=
  Rep.ofHom <| LinearMap.intertwiningMap_of_isIntertwiningMap _ _
    (sUnitsValuationHom L S).toIntLinearMap fun σ x ↦ by
      ext w
      simp [coeff_sUnitsValuationHom, Set.unitValuation_apply, valuation_apply_smul]

omit [NumberField K] in
/-- The kernel of the valuation map on the `S`-units is `U_{L,∅}`. -/
private theorem sUnitsValuationHom_eq_zero_iff
    (x : Additive ((primesAbove (𝓞 K) (𝓞 L) S).unit L)) :
    sUnitsValuationHom L S x = 0 ↔ (x.toMul : Lˣ) ∈ (primesAbove (𝓞 K) (𝓞 L) ∅).unit L := by
  rw [primesAbove_empty, ← Subgroup.mem_subgroupOf, ← Set.unitValuation_ker, MonoidHom.mem_ker,
    ← MonoidAlgebra.coeff_inj, funext_iff, Finsupp.ext_iff]
  simp [coeff_sUnitsValuationHom]

variable (L) in
/-- The valuation sequence `U_{L,∅} → U_{L,S} → ℤ[S_L]`. -/
private def sUnitsValuationShortComplex : ShortComplex (Rep ℤ (L ≃ₐ[K] L)) :=
  ShortComplex.mk (unitsToSUnits L S) (sUnitsValuation L S) <| by
    -- the carriers of the two unit representations are `Additive` of the unit groups by
    -- definition, which `ext` does not see through
    refine Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext
      fun (x : Additive ((primesAbove (𝓞 K) (𝓞 L) ∅).unit L)) ↦ ?_))
    exact (sUnitsValuationHom_eq_zero_iff S _).2 x.toMul.2

private theorem sUnitsValuationShortComplex_exact : (sUnitsValuationShortComplex L S).Exact := by
  rw [Rep.exact_iff_function_exact]
  intro (x : Additive ((primesAbove (𝓞 K) (𝓞 L) S).unit L))
  refine ⟨fun hx ↦ ⟨Additive.ofMul ⟨_, (sUnitsValuationHom_eq_zero_iff S x).1 hx⟩, rfl⟩, ?_⟩
  rintro ⟨(y : Additive ((primesAbove (𝓞 K) (𝓞 L) ∅).unit L)), rfl⟩
  exact (sUnitsValuationHom_eq_zero_iff S _).2 y.toMul.2

private instance : Mono (sUnitsValuationShortComplex L S).f :=
  (Rep.mono_iff_injective _).2 fun (_ _ : Additive ((primesAbove (𝓞 K) (𝓞 L) ∅).unit L)) h ↦
    Additive.toMul.injective <| Subgroup.inclusion_injective (unit_primesAbove_empty_le L S)
      (congrArg Additive.toMul h)

/-- The valuation map has finite cokernel: its range is Mathlib's finite-index valuation lattice
`finiteIndex_range_unitValuation`, read in `ℤ[S_L]`. -/
private instance : Finite ↑(cokernel (sUnitsValuationShortComplex L S).g) := by
  have := (primesAbove_finite (𝓞 K) (𝓞 L) (Set.toFinite S)).to_subtype
  -- read a vector of `ℤ[S_L]` as a tuple of valuations
  let e : MonoidAlgebra ℤ ↥(primesAbove (𝓞 K) (𝓞 L) S) →+
      Additive (↥(primesAbove (𝓞 K) (𝓞 L) S) → Multiplicative ℤ) :=
    { toFun f := .ofMul fun w ↦ .ofAdd (f.coeff w)
      map_zero' := by ext; simp
      map_add' _ _ := by ext; simp }
  have : (Set.unitValuation (primesAbove (𝓞 K) (𝓞 L) S) L).range.toAddSubgroup.FiniteIndex :=
    Subgroup.finiteIndex_toAddSubgroup_iff.mpr (finiteIndex_range_unitValuation (𝓞 L) L _)
  have : (LinearMap.range ((forget₂ (Rep ℤ (L ≃ₐ[K] L)) (ModuleCat ℤ)).map
      (sUnitsValuationShortComplex L S).g).hom).toAddSubgroup.FiniteIndex := by
    refine AddSubgroup.finiteIndex_of_le
      (H := (Set.unitValuation (primesAbove (𝓞 K) (𝓞 L) S) L).range.toAddSubgroup.comap e) ?_
    rintro f ⟨u, hu⟩
    refine ⟨Additive.ofMul u, MonoidAlgebra.ext (Finsupp.ext fun w ↦ ?_)⟩
    -- the forgotten morphism applies `sUnitsValuationHom` by definition
    change (sUnitsValuationHom L S (Additive.ofMul u)).coeff w = f.coeff w
    simpa [coeff_sUnitsValuationHom, e] using congrArg Multiplicative.toAdd (congrFun hu w)
  -- the cokernel is computed in `ModuleCat ℤ`, as the quotient by the range
  have : Finite (MonoidAlgebra ℤ ↥(primesAbove (𝓞 K) (𝓞 L) S) ⧸ LinearMap.range
      ((forget₂ (Rep ℤ (L ≃ₐ[K] L)) (ModuleCat ℤ)).map (sUnitsValuationShortComplex L S).g).hom) :=
    inferInstanceAs (Finite (_ ⧸ (LinearMap.range ((forget₂ (Rep ℤ (L ≃ₐ[K] L))
      (ModuleCat ℤ)).map (sUnitsValuationShortComplex L S).g).hom).toAddSubgroup))
  exact Finite.of_equiv _ (PreservesCokernel.iso (forget₂ (Rep ℤ (L ≃ₐ[K] L)) (ModuleCat ℤ))
    (sUnitsValuationShortComplex L S).g ≪≫
      ModuleCat.cokernelIsoRangeQuotient _).toLinearEquiv.toEquiv.symm

end Valuation

/-! ### The Herbrand quotient -/

variable (L) [Finite S] [IsCyclic (L ≃ₐ[K] L)] in
/-- **The Herbrand quotient of the `S`-units** of an extension `L/K` of number fields whose group of
`K`-automorphisms is cyclic, for a finite set `S` of finite places of `K`, is that of the units at
every finite place times that of the permutation lattice on the primes of `L` above `S`:
`h(U_{L,S}) = h(U_{L,∅}) · h(ℤ[S_L])`. -/
theorem herbrandQuotient_sUnitsRep_eq_mul :
    TateCohomology.herbrandQuotient (sUnitsRep L S) =
      TateCohomology.herbrandQuotient (sUnitsRep L (∅ : Set (HeightOneSpectrum (𝓞 K)))) *
        TateCohomology.herbrandQuotient
          (Rep.ofMulAction ℤ (L ≃ₐ[K] L) ↥(primesAbove (𝓞 K) (𝓞 L) S)) := by
  have := (primesAbove_finite (𝓞 K) (𝓞 L) (Set.toFinite S)).to_subtype
  -- the outer terms of `sUnitsValuationShortComplex L S` are `U_{L,∅}` and `ℤ[S_L]` by
  -- definition, which instance search does not see through
  have : Finite (tateCohomology (sUnitsValuationShortComplex L S).X₁ (-1)) :=
    finite_tateCohomology_negOne_sUnitsRep (L := L) ∅
  have : Module.Finite ℤ (sUnitsValuationShortComplex L S).X₃ :=
    inferInstanceAs (Module.Finite ℤ (MonoidAlgebra ℤ ↥(primesAbove (𝓞 K) (𝓞 L) S)))
  have : Finite (tateCohomology (sUnitsValuationShortComplex L S).X₃ (-1)) :=
    TateCohomology.finite_tateCohomology_negOne_of_moduleFinite _
  exact TateCohomology.herbrandQuotient_eq_mul_of_exact_of_finite_cokernel
    (S := sUnitsValuationShortComplex L S) (sUnitsValuationShortComplex_exact S)

end Set

open scoped AdicCompletionExtension in
/-- **The Herbrand quotient of the `S`-units** of a cyclic Galois extension `L/K` of number fields,
for a finite set `S` of finite places of `K`: `h(U_{L,S}) = h(U_{L,∅}) · ∏_{v ∈ S} [L_w : K_v]`,
where `U_{L,∅}` is the group of units at every finite place. The places `w` above each `v` may be
chosen arbitrarily. -/
theorem herbrandQuotient_sUnitsRep [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)]
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (w : ∀ v : S, {w : HeightOneSpectrum (𝓞 L) // w.asIdeal.LiesOver v.1.asIdeal}) :
    TateCohomology.herbrandQuotient (sUnitsRep L (S : Set (HeightOneSpectrum (𝓞 K)))) =
      TateCohomology.herbrandQuotient (sUnitsRep L (∅ : Set (HeightOneSpectrum (𝓞 K)))) *
        ∏ v : S, (Module.finrank (v.1.adicCompletion K) ((w v).1.adicCompletion L) : ℚ) := by
  rw [herbrandQuotient_sUnitsRep_eq_mul, herbrandQuotient_ofMulAction_primesAbove S w]

end TauCeti.ClassFieldTheory
