/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Global.RelativeBrauerLocalization

/-!
# Idele-class `H¹` and the kernel of Brauer localization

Let `L/K` be a finite Galois extension of number fields with Galois group `G`, embedded in `Kˢ`
by `σ`. The long exact cohomology sequence of `0 → Lˣ → I_L → C_L → 0`
(`principalIdeleShortComplex_shortExact`) contains

```text
H¹(G, I_L) → H¹(G, C_L) → H²(G, Lˣ) → H²(G, I_L).
```

Its first term vanishes by Hilbert 90 for ideles (`subsingleton_groupCohomology_one_idelesRep`), so
the connecting map `ideleClassToUnitsH2 K L : H¹(G, C_L) → H²(G, Lˣ)` is injective
(`ideleClassToUnitsH2_injective`), and its image is the kernel of the map induced by the principal
ideles (`mem_range_ideleClassToUnitsH2_iff`). A class `x ∈ H²(G, Lˣ)` dies in `H²(G, I_L)` exactly
when every localization of its Brauer class `relBrInfl K L σ x` vanishes
(`map_unitsToIdeles_eq_zero_iff_brLocalization_eq_zero`). Hence the split Brauer classes with
trivial localizations are exactly the images of `H¹(G, C_L)`
(`brLocalization_relBrInfl_eq_zero_iff_mem_range_ideleClassToUnitsH2`), and

```text
0 → H¹(G, C_L) → Br(L/K) → ⨁_v Br K_v
```

is exact. In particular `H¹(G, C_L)` vanishes exactly when localization is injective on the
Brauer classes split by `L` (`subsingleton_groupCohomology_one_ideleClassRep_iff`). Since every
Brauer class is split by some finite Galois extension, the injectivity of `Br K → ⨁_v Br K_v`
(Albert–Brauer–Hasse–Noether) follows from the vanishing of `H¹(Gal(L/K), C_L)` for all finite
Galois `L/K` (`brLocalization_injective_of_subsingleton_groupCohomology_one`), which comes from
the fundamental inequalities.

## Main definitions

* `TauCeti.ClassFieldTheory.ideleClassToUnitsH2 K L`: the connecting map
  `H¹(G, C_L) → H²(G, Lˣ)`.

## Main results

* `TauCeti.ClassFieldTheory.ideleClassToUnitsH2_injective`: the connecting map is injective.
* `TauCeti.ClassFieldTheory.mem_range_ideleClassToUnitsH2_iff`: its image is the kernel of
  `H²(G, Lˣ) → H²(G, I_L)`.
* `TauCeti.ClassFieldTheory.brLocalization_relBrInfl_eq_zero_iff_mem_range_ideleClassToUnitsH2`:
  a split Brauer class has trivial localizations exactly when it comes from `H¹(G, C_L)`.
* `TauCeti.ClassFieldTheory.subsingleton_groupCohomology_one_ideleClassRep_iff`: `H¹(G, C_L) = 0`
  exactly when every Brauer class split by `L` with trivial localizations is zero.
* `TauCeti.ClassFieldTheory.brLocalization_injective_of_subsingleton_groupCohomology_one`: the
  Hasse principle `Br K ↪ ⨁_v Br K_v`, if idele-class `H¹` vanishes for every finite Galois
  extension of `K`.

## References

* J. S. Milne, *Class Field Theory*, v4.03, Chapter VII, Proposition 2.5 and Corollary 2.6, and
  Chapter VIII, §4.
* J. Tate, *Global class field theory*, in J. W. S. Cassels and A. Fröhlich (eds.),
  *Algebraic Number Theory*, Chapter VII, §§6–7 and §9.
-/

public section

noncomputable section

open CategoryTheory

namespace TauCeti.ClassFieldTheory

variable (K : Type) [Field K] [NumberField K] (L : Type) [Field L] [NumberField L] [Algebra K L]

/-- **The connecting map `H¹(Gal(L/K), C_L) → H²(Gal(L/K), Lˣ)`** of the exact sequence
`0 → Lˣ → I_L → C_L → 0`. -/
def ideleClassToUnitsH2 :
    groupCohomology (ideleClassRep K L) 1 →+
      groupCohomology (Rep.ofMulDistribMulAction (L ≃ₐ[K] L) Lˣ) 2 :=
  (groupCohomology.δ (principalIdeleShortComplex_shortExact K L) 1 2 rfl).hom.toAddMonoidHom

variable {K L}

omit [NumberField K] in
/-- **Exactness at `H²(Gal(L/K), Lˣ)`**: a class comes from `H¹(Gal(L/K), C_L)` exactly when it
dies in `H²(Gal(L/K), I_L)`. -/
theorem mem_range_ideleClassToUnitsH2_iff
    (x : groupCohomology (Rep.ofMulDistribMulAction (L ≃ₐ[K] L) Lˣ) 2) :
    x ∈ (ideleClassToUnitsH2 K L).range ↔
      groupCohomology.map (MonoidHom.id _) (unitsToIdeles K L) 2 x = 0 :=
  SetLike.ext_iff.1 (congrArg Submodule.toAddSubgroup <|
    (ShortComplex.moduleCat_exact_iff_range_eq_ker _).1 <|
      groupCohomology.mapShortComplex₁_exact (principalIdeleShortComplex_shortExact K L) rfl) x

variable [IsGalois K L]

/-- **The connecting map `H¹(Gal(L/K), C_L) → H²(Gal(L/K), Lˣ)` is injective**, since
`H¹(Gal(L/K), I_L)` vanishes by Hilbert 90 for ideles. -/
theorem ideleClassToUnitsH2_injective : Function.Injective (ideleClassToUnitsH2 K L) :=
  (ModuleCat.mono_iff_injective _).1 <| groupCohomology.mono_δ_of_isZero _ 1 <|
    ModuleCat.isZero_of_subsingleton (groupCohomology (idelesRep K L) 1)

/-- **A split Brauer class has trivial localizations exactly when it comes from idele-class
`H¹`.** For `L/K` finite Galois, embedded in `Kˢ` by `σ`, every localization of the Brauer class
`relBrInfl K L σ x` of `x ∈ H²(Gal(L/K), Lˣ)` vanishes exactly when `x` is the image of a class of
`H¹(Gal(L/K), C_L)` under the connecting map of `0 → Lˣ → I_L → C_L → 0`. -/
theorem brLocalization_relBrInfl_eq_zero_iff_mem_range_ideleClassToUnitsH2
    (σ : L →ₐ[K] SeparableClosure K)
    (x : groupCohomology (Rep.ofMulDistribMulAction (L ≃ₐ[K] L) Lˣ) 2) :
    brLocalization K (relBrInfl K L σ x) = 0 ↔ x ∈ (ideleClassToUnitsH2 K L).range :=
  (map_unitsToIdeles_eq_zero_iff_brLocalization_eq_zero σ x).symm.trans
    (mem_range_ideleClassToUnitsH2_iff x).symm

/-- **Idele-class `H¹` vanishes exactly when localization is injective on the Brauer classes split
by `L`.** For `L/K` finite Galois, embedded in `Kˢ` by `σ`, `H¹(Gal(L/K), C_L) = 0` exactly when
every `x ∈ H²(Gal(L/K), Lˣ)` whose Brauer class `relBrInfl K L σ x` has trivial localizations at all
places of `K` is zero. -/
theorem subsingleton_groupCohomology_one_ideleClassRep_iff (σ : L →ₐ[K] SeparableClosure K) :
    Subsingleton (groupCohomology (ideleClassRep K L) 1) ↔
      ∀ x : groupCohomology (Rep.ofMulDistribMulAction (L ≃ₐ[K] L) Lˣ) 2,
        brLocalization K (relBrInfl K L σ x) = 0 → x = 0 := by
  simp_rw [brLocalization_relBrInfl_eq_zero_iff_mem_range_ideleClassToUnitsH2 σ,
    AddMonoidHom.mem_range]
  refine ⟨fun _ x ⟨c, hc⟩ ↦ ?_, fun h ↦ ⟨fun c d ↦ ideleClassToUnitsH2_injective ?_⟩⟩
  · rw [← hc, Subsingleton.elim c 0, map_zero]
  · rw [h _ ⟨c, rfl⟩, h _ ⟨d, rfl⟩]

variable (K) in
/-- **The Hasse principle for Brauer classes, from idele-class `H¹`.** If `H¹(Gal(L/K), C_L)`
vanishes for every finite Galois extension `L/K`, then a Brauer class of `K` whose localizations
at all places vanish is zero: `Br K → ⨁_v Br K_v` is injective. -/
theorem brLocalization_injective_of_subsingleton_groupCohomology_one
    (h : ∀ (L : Type) [Field L] [NumberField L] [Algebra K L] [IsGalois K L],
      Subsingleton (groupCohomology (ideleClassRep K L) 1)) :
    Function.Injective (brLocalization K) := by
  refine (injective_iff_map_eq_zero _).2 fun x hx ↦ ?_
  obtain ⟨E, _, _, y, rfl⟩ := exists_relBrInfl_eq x
  have : NumberField E := NumberField.of_module_finite K E
  have : IsGalois K E := {}
  rw [(subsingleton_groupCohomology_one_ideleClassRep_iff E.val).1 (h E) y hx, map_zero]

end TauCeti.ClassFieldTheory
