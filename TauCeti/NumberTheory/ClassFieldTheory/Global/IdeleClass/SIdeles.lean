/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.Ideles.GaloisAction
public import TauCeti.RepresentationTheory.Homological.TateCohomology.HerbrandQuotient
public import TauCeti.RepresentationTheory.Rep.TensorShortExact

/-!
# The idele classes as `S`-ideles modulo `S`-units

Let `L/K` be an extension of number fields and `S` a set of finite places of `K` such that the
classes of the primes of `L` above `S` generate the ideal class group of `L`; a finite such `S`
exists because the class group is finite. Write `I_{L,S}` for the `S`-ideles of `L`, the ideles
that are units at every finite place not above `S`, and `U_{L,S}` for the `S`-units of `L`. The
inclusion of the principal ideles and the quotient map onto the idele classes give a short exact
sequence of representations of `Aut(L/K)`

```text
0 → U_{L,S} → I_{L,S} → C_L → 0
```

(`sIdeleShortComplex_shortExact`): `I_L = Lˣ · I_{L,S}` because the primes above `S` generate the
class group, and `Lˣ ∩ I_{L,S} = U_{L,S}`.

For a cyclic extension this computes the Herbrand quotient of the idele classes from those of the
`S`-ideles and the `S`-units (`herbrandQuotient_ideleClassRep`):

```text
h(C_L) = h(I_{L,S}) / h(U_{L,S}).
```

This is the comparison through which the first fundamental inequality `h(C_L) = [L : K]` for a
cyclic extension reduces to the local computation `h(I_{L,S}) = ∏_{v ∈ S} [L_w : K_v]`, with `S`
also containing the archimedean places and the ramified primes, and the `S`-unit computation
`h(U_{L,S}) = (∏_{v ∈ S} [L_w : K_v]) / [L : K]`.

## Main definitions

* `TauCeti.ClassFieldTheory.sUnitsRep L S`, `TauCeti.ClassFieldTheory.sIdelesRep L S` and
  `TauCeti.ClassFieldTheory.ideleClassRep K L`: the `S`-units, the `S`-ideles and the idele classes
  of `L` as integral representations of `Aut(L/K)`.
* `TauCeti.ClassFieldTheory.sIdeleShortComplex L S`: the sequence `U_{L,S} → I_{L,S} → C_L`.

## Main results

* `TauCeti.ClassFieldTheory.sIdeleShortComplex_shortExact`: `0 → U_{L,S} → I_{L,S} → C_L → 0` is
  exact when the primes above `S` generate the class group.
* `TauCeti.ClassFieldTheory.herbrandQuotient_ideleClassRep`: `h(C_L) = h(I_{L,S}) / h(U_{L,S})`
  for a cyclic extension.

## References

* J. S. Milne, *Class Field Theory*, Chapter VII, §4, proof of Theorem 4.3.
* J. Neukirch, *Algebraic Number Theory*, Chapter VI, §2.
-/

public section

noncomputable section

open CategoryTheory IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField
open scoped AdeleGaloisAction

namespace TauCeti.ClassFieldTheory

open GlobalNumberFields

variable {K : Type} [Field K] [NumberField K] (L : Type) [Field L] [NumberField L] [Algebra K L]
  (S : Set (HeightOneSpectrum (𝓞 K)))

/-! ### The three representations -/

/-- The `S`-units of `L`, the units at every finite place not above `S`, as an integral
representation of `Aut(L/K)`. -/
abbrev sUnitsRep : Rep ℤ (L ≃ₐ[K] L) :=
  Rep.ofMulDistribMulAction (L ≃ₐ[K] L) ((primesAbove (𝓞 K) (𝓞 L) S).unit L)

/-- The `S`-ideles of `L`, the ideles that are units at every finite place not above `S`, as an
integral representation of `Aut(L/K)`. -/
abbrev sIdelesRep : Rep ℤ (L ≃ₐ[K] L) :=
  Rep.ofMulDistribMulAction (L ≃ₐ[K] L) (sIdeles L S)

variable (K) in
/-- The idele class group `C_L` of `L`, as an integral representation of `Aut(L/K)`. -/
abbrev ideleClassRep : Rep ℤ (L ≃ₐ[K] L) :=
  Rep.ofMulDistribMulAction (L ≃ₐ[K] L) (IdeleClassGroup (𝓞 L) L)

/-! ### The maps -/

/-- The principal `S`-idele of an `S`-unit, as a homomorphism `U_{L,S} → I_{L,S}`. -/
private def sUnitsToSIdelesHom : (primesAbove (𝓞 K) (𝓞 L) S).unit L →* sIdeles L S where
  toFun a := ⟨IdeleGroup.unitEmbedding (𝓞 L) L a.1, (unitEmbedding_mem_sIdeles_iff S a.1).2 a.2⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' _ _ := Subtype.ext (map_mul _ _ _)

private theorem sUnitsToSIdelesHom_smul (σ : L ≃ₐ[K] L) (a : (primesAbove (𝓞 K) (𝓞 L) S).unit L) :
    sUnitsToSIdelesHom L S (σ • a) = σ • sUnitsToSIdelesHom L S a :=
  Subtype.ext <| by
    rw [coe_smul_sIdeles]
    exact (congrArg _ (coe_smul_unit_primesAbove σ a)).trans (smul_unitEmbedding σ a.1).symm

/-- The inclusion `U_{L,S} → I_{L,S}` of the `S`-units as principal `S`-ideles, as a morphism of
representations of `Aut(L/K)`. -/
def sUnitsToSIdeles : sUnitsRep L S ⟶ sIdelesRep L S :=
  Rep.ofHom <| LinearMap.intertwiningMap_of_isIntertwiningMap _ _
    (sUnitsToSIdelesHom L S).toAdditive.toIntLinearMap fun σ a ↦
      congrArg Additive.ofMul (sUnitsToSIdelesHom_smul L S σ a.toMul)

/-- `sUnitsToSIdeles` sends an `S`-unit to its principal idele. -/
@[simp]
theorem sUnitsToSIdeles_hom_apply (a : Additive ((primesAbove (𝓞 K) (𝓞 L) S).unit L)) :
    (sUnitsToSIdeles L S).hom a = Additive.ofMul ⟨IdeleGroup.unitEmbedding (𝓞 L) L a.toMul,
      (unitEmbedding_mem_sIdeles_iff S _).2 a.toMul.2⟩ :=
  (rfl)

/-- The quotient map `I_{L,S} → C_L` sending an `S`-idele to its idele class, as a morphism of
representations of `Aut(L/K)`. -/
def sIdelesToIdeleClass : sIdelesRep L S ⟶ ideleClassRep K L :=
  Rep.ofHom <| LinearMap.intertwiningMap_of_isIntertwiningMap _ _
    ((QuotientGroup.mk' (IdeleGroup.principalSubgroup (𝓞 L) L)).comp
      (sIdeles L S).subtype).toAdditive.toIntLinearMap fun σ x ↦
      congrArg Additive.ofMul <| by
        simp

/-- `sIdelesToIdeleClass` sends an `S`-idele to its idele class. -/
@[simp]
theorem sIdelesToIdeleClass_hom_apply (x : Additive (sIdeles L S)) :
    (sIdelesToIdeleClass L S).hom x =
      Additive.ofMul ((x.toMul : IdeleGroup (𝓞 L) L) : IdeleClassGroup (𝓞 L) L) :=
  (rfl)

/-! ### The short exact sequence -/

/-- **The sequence `U_{L,S} → I_{L,S} → C_L`** of representations of `Aut(L/K)`, given by the
principal ideles and the quotient map onto the idele classes. -/
def sIdeleShortComplex : ShortComplex (Rep ℤ (L ≃ₐ[K] L)) :=
  ShortComplex.mk (sUnitsToSIdeles L S) (sIdelesToIdeleClass L S) <| by
    ext a
    exact congrArg Additive.ofMul (QuotientGroup.eq_one_iff _ |>.2 ⟨a.toMul.1, rfl⟩)

variable {S} in
/-- **The sequence `0 → U_{L,S} → I_{L,S} → C_L → 0` is exact** when the classes of the primes
of `L` above `S` generate the ideal class group of `L`: the principal `S`-ideles are those of the
`S`-units, and every idele class is the class of an `S`-idele. -/
theorem sIdeleShortComplex_shortExact
    (hS : Subgroup.closure (classGroupMk '' (primesAbove (𝓞 K) (𝓞 L) S)) = ⊤) :
    (sIdeleShortComplex L S).ShortExact where
  exact := by
    rw [Rep.exact_iff_function_exact]
    intro (x : Additive (sIdeles L S))
    refine ⟨fun hx ↦ ?_, ?_⟩
    · have hx : (x.toMul : IdeleGroup (𝓞 L) L) ∈ IdeleGroup.principalSubgroup (𝓞 L) L :=
        (QuotientGroup.eq_one_iff _).1 (congrArg Additive.toMul hx)
      obtain ⟨a, ha, hax⟩ :=
        (mem_principalSubgroup_iff_exists_mem_unit_of_mem_sIdeles x.toMul.2).1 hx
      exact ⟨Additive.ofMul ⟨a, ha⟩, congrArg Additive.ofMul (Subtype.ext hax)⟩
    · rintro ⟨a, rfl⟩
      exact congrArg Additive.ofMul (QuotientGroup.eq_one_iff _ |>.2 ⟨a.toMul.1, rfl⟩)
  mono_f := by
    rw [Rep.mono_iff_injective]
    intro (a : Additive ((primesAbove (𝓞 K) (𝓞 L) S).unit L)) b hab
    have h := congrArg (fun x : Additive (sIdeles L S) ↦ (x.toMul : IdeleGroup (𝓞 L) L)) hab
    exact Additive.toMul.injective <| Subtype.ext <|
      Units.map_injective (AdeleRing.algebraMap_injective (𝓞 L) L) h
  epi_g := by
    rw [Rep.epi_iff_surjective]
    intro c
    obtain ⟨x, hx, hxc⟩ := exists_mem_sIdeles_mk_eq hS c.toMul
    exact ⟨Additive.ofMul ⟨x, hx⟩, congrArg Additive.ofMul hxc⟩

/-! ### The Herbrand quotient -/

variable {S} in
/-- **The Herbrand quotient of the idele classes** of a cyclic extension `L/K` is the quotient of
the Herbrand quotients of the `S`-ideles and of the `S`-units, when the classes of the primes above
`S` generate the ideal class group of `L` and the relevant Tate groups are finite:
`h(C_L) = h(I_{L,S}) / h(U_{L,S})`. -/
theorem herbrandQuotient_ideleClassRep [IsCyclic (L ≃ₐ[K] L)]
    (hS : Subgroup.closure (classGroupMk '' (primesAbove (𝓞 K) (𝓞 L) S)) = ⊤)
    [Finite (tateCohomology (sUnitsRep L S) 0)] [Finite (tateCohomology (sUnitsRep L S) (-1))]
    [Finite (tateCohomology (sIdelesRep L S) (-1))] :
    TateCohomology.herbrandQuotient (ideleClassRep K L) =
      TateCohomology.herbrandQuotient (sIdelesRep L S) /
        TateCohomology.herbrandQuotient (sUnitsRep L S) := by
  -- The outer terms of `sIdeleShortComplex L S` are `sUnitsRep L S` and `sIdelesRep L S` by
  -- definition, which instance search does not see through.
  have : Finite (tateCohomology (sIdeleShortComplex L S).X₁ 0) :=
    inferInstanceAs (Finite (tateCohomology (sUnitsRep L S) 0))
  have : Finite (tateCohomology (sIdeleShortComplex L S).X₁ (-1)) :=
    inferInstanceAs (Finite (tateCohomology (sUnitsRep L S) (-1)))
  have : Finite (tateCohomology (sIdeleShortComplex L S).X₂ (-1)) :=
    inferInstanceAs (Finite (tateCohomology (sIdelesRep L S) (-1)))
  exact TateCohomology.herbrandQuotient_eq_div_of_shortExact (sIdeleShortComplex_shortExact L hS)

end TauCeti.ClassFieldTheory
