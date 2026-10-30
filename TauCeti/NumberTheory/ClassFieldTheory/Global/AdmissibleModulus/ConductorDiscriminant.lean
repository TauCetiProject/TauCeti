/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Global.AdmissibleModulus.Ramification
public import TauCeti.NumberTheory.LocalField.Herbrand.ArtinConductor
public import TauCeti.RingTheory.DedekindDomain.Discriminant.Basic
import TauCeti.GroupTheory.Abelianization.Basic
import TauCeti.GroupTheory.FiniteAbelian.Duality
import TauCeti.NumberTheory.ClassFieldTheory.Local.ArtinMap
import TauCeti.NumberTheory.ClassFieldTheory.Local.Conductor.UpperNumbering
import TauCeti.NumberTheory.LocalField.Discriminant.Conductor
import TauCeti.NumberTheory.NumberField.LocalGlobal.Discriminant
import TauCeti.RingTheory.DedekindDomain.PrimesAbove

/-!
# The conductor–discriminant formula

Let `L/K` be a finite abelian extension of number fields with group `G`, and let `M` be a
commutative monoid with enough roots of unity (for instance `M = ℂ`). For a character
`χ : G →* Mˣ`, the fixed field `L^{ker χ}` is the cyclic subextension cut out by `χ`, and its
conductor `abelianConductor K L^{ker χ}` is the conductor `𝔣(χ)` of `χ`. The
**conductor–discriminant formula** says that the relative discriminant of `L/K` is the product of
the finite parts of these conductors (`relDiscr_eq_finprod_finitePart_abelianConductor`):

`𝔡_{L/K} = ∏_χ 𝔣(χ)`.

The proof reads both sides at a finite place `v` of `K`, through a place `w` of `L` above it, with
decomposition group `D_w ≅ Gal(L_w/K_v)`.

* **The character dictionary.** The class of the idele concentrated at `v` with component
  `u ∈ K_vˣ` is a norm from the fixed field of `H ≤ G` exactly when the global Artin symbol of `u`,
  which is its local Artin symbol in `D_w` (`globalArtinMap_local`), lies in `H`. By local
  reciprocity this happens exactly when `u` is a norm from the fixed field of `H ∩ D_w` in `L_w`
  (`mem_normGroup_fixedField_iff`). Hence the exponent of `v` in the conductor of the fixed field
  of `H` is the local conductor exponent of the fixed field of `H ∩ D_w`
  (`exponent_abelianConductor_fixedField`). For `H = ker χ` the local conductor exponent of the
  fixed field of `ker χ|_{D_w}` is the Artin conductor exponent `f(χ|_{D_w})`
  (`conductorExponent_fixedField_ker`), so the exponent of `v` in `𝔣(χ)` is `f(χ|_{D_w})`
  (`exponent_abelianConductor_fixedField_ker`).
* **Counting characters.** Every character of `D_w` extends to `[G : D_w]` characters of `G`
  (`CommGroup.finsum_domRestrictHom`), so `∑_χ f(χ|_{D_w}) = [G : D_w] · ∑_ψ f(ψ)`, the second sum
  running over the characters of `Gal(L_w/K_v)`.
* **The local formula.** `∑_ψ f(ψ)` is the discriminant exponent `δ(L_w/K_v)`
  (`TauCeti.LocalFieldsRamification.finsum_artinConductorExponent_eq_discriminantExponent`), and
  the coefficient of `𝔡_{L/K}` at `v` is `[G : D_w] · δ(L_w/K_v)`
  (`IsDedekindDomain.HeightOneSpectrum.multiplicity_relDiscr_eq_index_mul_discriminantExponent`).

This gives the formula at every finite place
(`multiplicity_relDiscr_eq_finsum_exponent_abelianConductor`), hence as an identity of ideals.

## Main results

* `TauCeti.ClassFieldTheory.exponent_abelianConductor_fixedField`: the exponent of `v` in the
  conductor of the fixed field of `H ≤ Gal(L/K)` is the local conductor exponent of the fixed
  field of the corresponding subgroup of `Gal(L_w/K_v)`.
* `TauCeti.ClassFieldTheory.exponent_abelianConductor_fixedField_ker`: the exponent of `v` in the
  conductor of a character `χ` of `Gal(L/K)` is the Artin conductor exponent of the restriction of
  `χ` to `Gal(L_w/K_v)`.
* `TauCeti.ClassFieldTheory.multiplicity_relDiscr_eq_finsum_exponent_abelianConductor`: the
  conductor–discriminant formula at a finite place.
* `TauCeti.ClassFieldTheory.relDiscr_eq_finprod_finitePart_abelianConductor`: the
  conductor–discriminant formula `𝔡_{L/K} = ∏_χ 𝔣(χ)`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §11.
* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter VI, §3.
-/

public section

noncomputable section

namespace TauCeti.ClassFieldTheory

open IsDedekindDomain _root_.NumberField TauCeti.GlobalNumberFields _root_.IntermediateField
  TauCeti.LocalFieldsRamification
open scoped AdicCompletionExtension Pointwise

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsAbelianGalois K L]

/-! ### The character dictionary at a finite place -/

section Place

variable (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
  [w.asIdeal.LiesOver v.asIdeal]

/-- **Idele classes concentrated at one place that are norms from a subextension.** Let `L/K` be
abelian, `H` a subgroup of `Gal(L/K)`, `v` a finite place of `K` and `w` a place of `L` above it.
The class of the idele concentrated at `v` with component `u` is a norm from the fixed field of
`H` exactly when `u` is a norm from the fixed field in `L_w` of the subgroup of `Gal(L_w/K_v)`
corresponding to `H` under the decomposition group of `w`. -/
theorem ofAdicCompletion_mem_range_ideleClassNormMap_fixedField_iff (H : Subgroup Gal(L/K))
    (u : (v.adicCompletion K)ˣ) :
    (IdeleGroup.ofAdicCompletion (𝓞 K) K v u : IdeleClassGroup (𝓞 K) K) ∈
        (ideleClassNormMap K (fixedField H) :
          IdeleClassGroup (𝓞 (fixedField H)) (fixedField H) →* IdeleClassGroup (𝓞 K) K).range ↔
      u ∈ normGroup (v.adicCompletion K) (fixedField (H.comap
        ((MulAction.stabilizer Gal(L/K) w.asIdeal).subtype.comp
          (HeightOneSpectrum.decompositionEquiv v w).symm.toMonoidHom))) := by
  have := IsAbelianGalois.tower_bot K (fixedField H) L
  have := HeightOneSpectrum.isAbelianGalois_adicCompletion v w
  obtain ⟨ρ, hρ⟩ : ∃ ρ, Abelianization.of ρ =
      normResidue (v.adicCompletion K) (w.adicCompletion L) u :=
    QuotientGroup.mk_surjective _
  -- Both sides say that the local Artin symbol of `u`, an element of the decomposition group of
  -- `w`, lies in `H`.
  rw [mem_normGroup_fixedField_iff _ hρ, ← globalArtinMap_eq_zero_iff K _ IsSepClosed.lift,
    globalArtinMap_local, ofMul_eq_zero, ← localArtinAt_comp v (fixedField H).val,
    MonoidHom.comp_apply, localArtinAt_eq_map_normResidue v w, ← hρ, Abelianization.map_of,
    Abelianization.map_of, IntermediateField.restrictNormalHom_val,
    ← map_one (Abelianization.of (G := Gal(fixedField H/K))), Abelianization.of_injective.eq_iff,
    ← MonoidHom.mem_ker, IntermediateField.restrictNormalHom_ker,
    IntermediateField.fixingSubgroup_fixedField, Subgroup.mem_comap]

/-- **The conductor of a subextension at a finite place.** Let `L/K` be abelian, `H` a subgroup
of `Gal(L/K)`, `v` a finite place of `K` and `w` a place of `L` above it. The exponent of `v` in
the conductor of the fixed field of `H` is the conductor exponent of the fixed field in `L_w` of
the subgroup of `Gal(L_w/K_v)` corresponding to `H` under the decomposition group of `w`. -/
theorem exponent_abelianConductor_fixedField (H : Subgroup Gal(L/K)) :
    (abelianConductor K (fixedField H)).exponent v =
      conductorExponent (v.adicCompletion K) (fixedField (H.comap
        ((MulAction.stabilizer Gal(L/K) w.asIdeal).subtype.comp
          (HeightOneSpectrum.decompositionEquiv v w).symm.toMonoidHom))) :=
  eq_of_forall_ge_iff fun n ↦ by
    rw [exponent_abelianConductor_le_iff, conductorExponent_le_iff]
    exact forall₂_congr fun u _ ↦
      ofAdicCompletion_mem_range_ideleClassNormMap_fixedField_iff v w H u

/-- **The conductor of a character at a finite place is a local Artin conductor.** Let `L/K` be
abelian, `χ` a homomorphism on `Gal(L/K)`, `v` a finite place of `K` and `w` a place of `L` above
it. The exponent of `v` in the conductor of the fixed field of `ker χ` is the Artin conductor
exponent of `χ` restricted to `Gal(L_w/K_v)`, the decomposition group of `w`. -/
theorem exponent_abelianConductor_fixedField_ker {A : Type*} [MulOneClass A]
    (χ : Gal(L/K) →* A) :
    (abelianConductor K (fixedField χ.ker)).exponent v =
      artinConductorExponent (v.adicCompletion K) (w.adicCompletion L)
        (χ.comp ((MulAction.stabilizer Gal(L/K) w.asIdeal).subtype.comp
          (HeightOneSpectrum.decompositionEquiv v w).symm.toMonoidHom)) := by
  have := HeightOneSpectrum.isAbelianGalois_adicCompletion v w
  rw [exponent_abelianConductor_fixedField v w, MonoidHom.comap_ker,
    conductorExponent_fixedField_ker]

end Place

/-! ### The conductor–discriminant formula -/

open scoped IsMulCommutative in
/-- **The conductor–discriminant formula at a finite place.** For a finite abelian extension `L/K`
of number fields and a commutative monoid `M` with enough roots of unity (for instance `M = ℂ`),
the coefficient at a finite place `v` of the relative discriminant of `L/K` is the sum, over the
characters `χ : Gal(L/K) →* Mˣ`, of the exponents of `v` in the conductors of the fixed fields of
their kernels. -/
theorem multiplicity_relDiscr_eq_finsum_exponent_abelianConductor (M : Type*) [CommMonoid M]
    [HasEnoughRootsOfUnity M (Monoid.exponent Gal(L/K))] (v : HeightOneSpectrum (𝓞 K)) :
    multiplicity v.asIdeal (relDiscr (𝓞 K) (𝓞 L)) =
      ∑ᶠ χ : Gal(L/K) →* Mˣ, (abelianConductor K (fixedField χ.ker)).exponent v := by
  obtain ⟨w, rfl⟩ := HeightOneSpectrum.under_surjective (𝓞 K) (𝓞 L) v
  have := HeightOneSpectrum.isAbelianGalois_adicCompletion (w.under (𝓞 K)) w
  set D := MulAction.stabilizer Gal(L/K) w.asIdeal
  set e := HeightOneSpectrum.decompositionEquiv (w.under (𝓞 K)) w
  have : HasEnoughRootsOfUnity M
      (Monoid.exponent Gal(w.adicCompletion L/(w.under (𝓞 K)).adicCompletion K)) :=
    HasEnoughRootsOfUnity.of_dvd M ((Monoid.exponent_eq_of_mulEquiv e).symm ▸
      Monoid.exponent_submonoid_dvd D.toSubmonoid)
  -- Both sides are `[G : D_w]` times the sum of the Artin conductor exponents of the characters
  -- of `Gal(L_w/K_v) ≅ D_w`.
  rw [HeightOneSpectrum.multiplicity_relDiscr_eq_index_mul_discriminantExponent _ w,
    ← finsum_artinConductorExponent_eq_discriminantExponent _ _ M,
    finsum_congr fun χ ↦ exponent_abelianConductor_fixedField_ker _ w χ,
    ← finsum_comp_equiv (e.monoidHomCongrLeftEquiv (N := Mˣ))]
  exact (CommGroup.finsum_domRestrictHom M D fun ψ ↦ artinConductorExponent _ _
    (ψ.comp e.symm.toMonoidHom)).symm

open scoped IsMulCommutative in
/-- **The conductor–discriminant formula.** For a finite abelian extension `L/K` of number fields
and a commutative monoid `M` with enough roots of unity (for instance `M = ℂ`), the relative
discriminant of `L/K` is the product, over the characters `χ : Gal(L/K) →* Mˣ`, of the finite
parts of the conductors of the fixed fields of their kernels: `𝔡_{L/K} = ∏_χ 𝔣(χ)`. -/
theorem relDiscr_eq_finprod_finitePart_abelianConductor (M : Type*) [CommMonoid M]
    [HasEnoughRootsOfUnity M (Monoid.exponent Gal(L/K))] :
    relDiscr (𝓞 K) (𝓞 L) =
      ∏ᶠ χ : Gal(L/K) →* Mˣ, (abelianConductor K (fixedField χ.ker)).finitePart := by
  classical
  have := Fintype.ofFinite (Gal(L/K) →* Mˣ)
  set 𝔣 := fun χ : Gal(L/K) →* Mˣ ↦ (abelianConductor K (fixedField χ.ker)).finitePart
  have h𝔣 : ∀ s : Finset (Gal(L/K) →* Mˣ), ∏ χ ∈ s, 𝔣 χ ≠ 0 := fun s ↦
    Finset.prod_ne_zero_iff.2 fun χ _ ↦ Modulus.finitePart_ne_zero _
  -- Two nonzero ideals with the same coefficient at every prime are equal.
  rw [finprod_eq_prod_of_fintype,
    ← Ideal.finprod_heightOneSpectrum_pow_multiplicity (relDiscr_ne_bot (A := 𝓞 K)),
    ← Ideal.finprod_heightOneSpectrum_pow_multiplicity (h𝔣 Finset.univ)]
  refine finprod_congr fun v ↦ congrArg _ ?_
  rw [multiplicity_relDiscr_eq_finsum_exponent_abelianConductor M v, finsum_eq_sum_of_fintype,
    ← v.count_normalizedFactors_eq_multiplicity (h𝔣 Finset.univ)]
  induction (Finset.univ : Finset (Gal(L/K) →* Mˣ)) using Finset.induction_on with
  | empty => simp
  | insert χ s hχ ih =>
    rw [Finset.prod_insert hχ, Finset.sum_insert hχ, UniqueFactorizationMonoid.normalizedFactors_mul
      (Modulus.finitePart_ne_zero _) (h𝔣 s), Multiset.count_add, ih,
      v.count_normalizedFactors_eq_multiplicity (Modulus.finitePart_ne_zero _),
      Modulus.exponent_eq_multiplicity]

end TauCeti.ClassFieldTheory
