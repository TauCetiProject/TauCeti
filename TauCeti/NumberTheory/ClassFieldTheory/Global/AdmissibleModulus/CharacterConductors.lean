/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Global.AdmissibleModulus.Basic
public import TauCeti.NumberTheory.ClassFieldTheory.Global.Reciprocity

/-!
# The conductor as a least common multiple of character conductors

For a finite abelian extension `L/K`, characters are homomorphisms `χ : Gal(L/K) →* Mˣ`,
where `M` is a commutative monoid satisfying
`HasEnoughRootsOfUnity M (Monoid.exponent Gal(L/K))`, for example `M = ℂ`.
A character's conductor means the conductor of the fixed field of its kernel. The conductor
of `L/K` is their least common multiple: its exponent at a finite place is the maximum of
their exponents, and its real places are the union of their real places.

The underlying norm criterion is global: an idele class is a norm from `L` exactly when
it is a norm from every character's fixed field. This follows from functoriality of
reciprocity and separation by characters of the finite abelian Galois group. Minimality
of the conductor then gives the least-common-multiple characterization, including the
infinite part, without imposing any condition on the ramification.

## Main results

* `TauCeti.ClassFieldTheory.abelianConductor_dvd_iff_forall_fixedField_ker`: the lcm property,
  characterized by divisibility into a modulus.
* `TauCeti.ClassFieldTheory.exponent_abelianConductor_eq_iSup_fixedField_ker`: the maximum formula
  at finite places.
* `TauCeti.ClassFieldTheory.mem_infinitePart_abelianConductor_iff_exists_fixedField_ker`: the union
  formula at real places.

These give the lcm half of the conductor–discriminant formula, complementing the product formula
`TauCeti.ClassFieldTheory.relDiscr_eq_finprod_finitePart_abelianConductor` in
`TauCeti.NumberTheory.ClassFieldTheory.Global.AdmissibleModulus.ConductorDiscriminant`.

## References

* J. S. Milne, *Class Field Theory*, v4.03, Chapter V, Theorem 3.27 and Remark 3.28.
-/

public noncomputable section

open IsDedekindDomain NumberField IntermediateField
open scoped IsMulCommutative

namespace TauCeti.ClassFieldTheory

open GlobalNumberFields

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsAbelianGalois K L]
variable (M : Type*) [CommMonoid M] [HasEnoughRootsOfUnity M (Monoid.exponent Gal(L/K))]

/-- The conductor of an abelian extension is the least common multiple of the conductors of
characters `χ : Gal(L/K) →* Mˣ`, characterized by divisibility into any modulus. Here `M` is a
commutative monoid satisfying `HasEnoughRootsOfUnity M (Monoid.exponent Gal(L/K))`. -/
theorem abelianConductor_dvd_iff_forall_fixedField_ker (𝔪 : Modulus K) :
    abelianConductor K L ∣ 𝔪 ↔
      ∀ χ : Gal(L/K) →* Mˣ, abelianConductor K (fixedField χ.ker) ∣ 𝔪 := by
  simp_rw [← isAdmissibleModulus_iff_abelianConductor_dvd]
  simp only [isAdmissibleModulus_iff, IsConcreteLE.le_iff,
    mem_range_ideleClassNormMap_iff_forall_fixedField_ker K L M]
  exact ⟨fun h χ c hc ↦ h hc χ, fun h c hc χ ↦ h χ hc⟩

/-- At each finite place, the conductor exponent of an abelian extension is the maximum
of the conductor exponents of the subextensions cut out by characters `χ : Gal(L/K) →* Mˣ`.
Here `M` is a commutative monoid satisfying
`HasEnoughRootsOfUnity M (Monoid.exponent Gal(L/K))`. -/
theorem exponent_abelianConductor_eq_iSup_fixedField_ker (v : HeightOneSpectrum (𝓞 K)) :
    (abelianConductor K L).exponent v =
      ⨆ χ : Gal(L/K) →* Mˣ, (abelianConductor K (fixedField χ.ker)).exponent v := by
  apply eq_of_forall_ge_iff
  intro n
  rw [ciSup_le_iff ⟨(abelianConductor K L).exponent v, by
    rintro _ ⟨χ, rfl⟩
    exact Modulus.exponent_mono (abelianConductor_dvd_abelianConductor L) v⟩]
  simp only [exponent_abelianConductor_le_iff,
    mem_range_ideleClassNormMap_iff_forall_fixedField_ker K L M]
  exact ⟨fun h χ u hu ↦ h u hu χ, fun h u hu χ ↦ h χ u hu⟩

/-- A real place occurs in the conductor of an abelian extension exactly when it occurs
in the conductor of a subextension cut out by a character `χ : Gal(L/K) →* Mˣ`.
Here `M` is a commutative monoid satisfying
`HasEnoughRootsOfUnity M (Monoid.exponent Gal(L/K))`. -/
theorem mem_infinitePart_abelianConductor_iff_exists_fixedField_ker
    (w : {w : InfinitePlace K // w.IsReal}) :
    w ∈ (abelianConductor K L).infinitePart ↔
      ∃ χ : Gal(L/K) →* Mˣ, w ∈ (abelianConductor K (fixedField χ.ker)).infinitePart := by
  classical
  have hdiv (χ : Gal(L/K) →* Mˣ) :
      abelianConductor K (fixedField χ.ker) ∣ abelianConductor K L :=
    abelianConductor_dvd_abelianConductor L
  constructor
  · intro hw
    let 𝔪 : Modulus K :=
      ⟨(abelianConductor K L).finitePart, (abelianConductor K L).finitePart_ne_bot,
        Finset.univ.filter fun w ↦
          ∃ χ : Gal(L/K) →* Mˣ, w ∈ (abelianConductor K (fixedField χ.ker)).infinitePart⟩
    have hd : abelianConductor K L ∣ 𝔪 :=
      (abelianConductor_dvd_iff_forall_fixedField_ker K L M 𝔪).2 fun χ ↦
        Modulus.dvd_iff.2 ⟨(Modulus.dvd_iff.1 (hdiv χ)).1,
          fun w hw ↦ Finset.mem_filter.2 ⟨Finset.mem_univ w, χ, hw⟩⟩
    exact (Finset.mem_filter.1 ((Modulus.dvd_iff.1 hd).2 hw)).2
  · rintro ⟨χ, hχ⟩
    exact (Modulus.dvd_iff.1 (hdiv χ)).2 hχ

end TauCeti.ClassFieldTheory
