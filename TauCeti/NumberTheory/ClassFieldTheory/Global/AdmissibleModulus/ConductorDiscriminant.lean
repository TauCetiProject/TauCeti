/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Global.AdmissibleModulus.Ramification
public import TauCeti.RingTheory.DedekindDomain.Discriminant.Basic
import TauCeti.GroupTheory.FiniteAbelian.Duality
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

* **The character dictionary.** The exponent of `v` in `𝔣(χ)` is the Artin conductor exponent
  `f(χ|_{D_w})` (`exponent_abelianConductor_fixedField_ker`, from local reciprocity and local–global
  compatibility of the Artin map).
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
  -- The multiplicity of a prime in a product is the sum of its multiplicities in the factors.
  have hfin {I : Ideal (𝓞 K)} (hI : I ≠ 0) : FiniteMultiplicity v.asIdeal I :=
    .of_prime_left v.prime hI
  rw [multiplicity_relDiscr_eq_finsum_exponent_abelianConductor M v, finsum_eq_sum_of_fintype,
    ← Nat.cast_inj (R := ℕ∞), ← (hfin (h𝔣 Finset.univ)).emultiplicity_eq_multiplicity,
    Finset.emultiplicity_prod v.prime, Nat.cast_sum]
  exact Finset.sum_congr rfl fun χ _ ↦ by
    rw [Modulus.exponent_eq_multiplicity,
      (hfin (Modulus.finitePart_ne_zero _)).emultiplicity_eq_multiplicity]

end TauCeti.ClassFieldTheory
