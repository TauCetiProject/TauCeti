/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.FittingIdeal.BaseChange
public import TauCeti.RingTheory.FittingIdeal.LocalRing
public import TauCeti.RingTheory.Kaehler.Conormal
public import Mathlib.RingTheory.Etale.Field
public import TauCeti.RingTheory.Unramified.LocalRing

/-!
# The cotangent space at a nodal point

Let `A` be a local algebra, essentially of finite type over a field `K`, and let
`I = Fitt₁(Ω[A⁄K])` be the first Fitting ideal of its differentials. This ideal cuts out the
singular locus; the scheme-theoretic criterion for a nodal curve asks that `A ⧸ I` be unramified
over `K`. If the closed point is singular, that is `I ≠ A`, then:

* `I = 𝔪`: an unramified local `K`-algebra is a field, so the singular locus is reduced
  (`Ideal.eq_maximalIdeal_of_formallyUnramified_quotient`);
* `dim_κ κ ⊗[A] Ω[A⁄K] = 2`: it is at least two because the point is singular, and at most two
  because `Fitt₁(Ω[A⁄K]) ≤ 𝔪 ^ (dim_κ κ ⊗[A] Ω[A⁄K] - 1)`, while `𝔪 ≤ 𝔪²` would force `𝔪 = 0`
  by Nakayama's lemma, and then `Ω[A⁄K] = 0`;
* `dim_κ 𝔪/𝔪² = 2`: the residue field is separable over `K`, so the conormal sequence identifies
  the Zariski cotangent space `𝔪/𝔪²` with `κ ⊗[A] Ω[A⁄K]`.

Since `I = 𝔪`, the last statement says that the conormal space `I/I²` of the singular locus at a
node is a plane; the two branches through the node are lines in this plane. No syntomic or
dimension hypothesis is needed for these statements.

Localizing, the same holds at every point of the singular locus of an algebra `A` essentially of
finite type over `K` with `A ⧸ I` unramified over `K`: there the fibre of `Ω[A⁄K]` has dimension
two. This is the form used for nodal curves.

## Main results

* `TauCeti.finrank_residueField_tensor_kaehlerDifferential_eq_two`: `dim_κ κ ⊗[A] Ω[A⁄K] = 2`.
* `TauCeti.formallyEtale_residueField_of_fittingIdeal_ne_top`: the residue field is formally étale
  over `K`.
* `TauCeti.finrank_cotangentSpace_eq_two`: `dim_κ 𝔪/𝔪² = 2`.
* `TauCeti.formallyUnramified_localization_quotient_fittingIdeal`: the unramified singular locus
  localizes.
* `TauCeti.finrank_tensor_kaehlerDifferential_eq_two`: for `A` not necessarily local, the fibre of
  `Ω[A⁄K]` at every point of `V(I)` has dimension two.

## References

* [Stacks Project, Section 53.19, Tag 0C46](https://stacks.math.columbia.edu/tag/0C46): nodal
  curves; a node has a two-dimensional tangent space.
* [Stacks Project, Lemma 53.20.1, Tag 0C58](https://stacks.math.columbia.edu/tag/0C58): the
  singular-locus criterion for families of nodal curves.
-/

public section

noncomputable section

open Module IsLocalRing TensorProduct

namespace TauCeti

section LocalRing

variable {K A : Type*} [Field K] [CommRing A] [Algebra K A] [IsLocalRing A]
  [Algebra.EssFiniteType K A]

variable [Algebra.FormallyUnramified K (A ⧸ fittingIdeal A Ω[A⁄K] 1)]

/-- **The differentials at a node need two generators.** If the first Fitting ideal of `Ω[A⁄K]`
is a proper ideal of the local `K`-algebra `A` with unramified quotient, the fibre of `Ω[A⁄K]` at
the closed point is a plane. -/
theorem finrank_residueField_tensor_kaehlerDifferential_eq_two
    (h : fittingIdeal A Ω[A⁄K] 1 ≠ ⊤) :
    finrank (ResidueField A) (ResidueField A ⊗[A] Ω[A⁄K]) = 2 := by
  have hI := Ideal.eq_maximalIdeal_of_formallyUnramified_quotient K h
  have : IsNoetherianRing A := Algebra.EssFiniteType.isNoetherianRing K A
  set μ := finrank (ResidueField A) (ResidueField A ⊗[A] Ω[A⁄K])
  -- The closed point is singular, so the fibre has dimension at least two.
  have h1 : 1 < μ := by
    rw [← fittingIdeal_map_eq_bot_iff_lt_finrank, hI, Ideal.map_eq_bot_iff_le_ker,
      ResidueField.algebraMap_eq, ker_residue]
  refine le_antisymm (not_lt.1 fun h3 ↦ ?_) h1
  -- Otherwise `𝔪 = Fitt₁(Ω[A⁄K]) ≤ 𝔪²`, so `𝔪 = 0` by Nakayama's lemma.
  have hsq : maximalIdeal A ≤ maximalIdeal A • maximalIdeal A := by
    rw [smul_eq_mul, ← sq]
    exact hI.ge.trans <| (fittingIdeal_le_maximalIdeal_pow 1).trans <|
      Ideal.pow_le_pow_right (show 2 ≤ μ - 1 by omega)
  have hbot : maximalIdeal A = ⊥ :=
    Submodule.eq_bot_of_le_smul_of_le_jacobson_bot _ _ (IsNoetherian.noetherian _) hsq
      (jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge
  -- Then `A = A ⧸ Fitt₁(Ω[A⁄K])` is unramified over `K`, and `Ω[A⁄K] = 0`.
  have : Algebra.FormallyUnramified K A := .of_equiv
    ((Ideal.quotientEquivAlgOfEq K (hI.trans hbot)).trans (AlgEquiv.quotientBot K A))
  have : μ = 0 := finrank_zero_of_subsingleton
  omega

/-- **The residue field at a node is étale.** If the first Fitting ideal of `Ω[A⁄K]` is a proper
ideal of the local `K`-algebra `A` with unramified quotient, then the residue field of `A`, a
quotient of `A ⧸ Fitt₁(Ω[A⁄K])`, is separable and hence formally étale over `K`. -/
theorem formallyEtale_residueField_of_fittingIdeal_ne_top (h : fittingIdeal A Ω[A⁄K] 1 ≠ ⊤) :
    Algebra.FormallyEtale K (ResidueField A) := by
  have hI := Ideal.eq_maximalIdeal_of_formallyUnramified_quotient K h
  have : Algebra.FormallyUnramified K (ResidueField A) :=
    .of_surjective (Ideal.Quotient.liftₐ _ (IsScalarTower.toAlgHom K A (ResidueField A))
      fun a ha ↦ (residue_eq_zero_iff a).2 (hI ▸ ha))
      (Ideal.Quotient.lift_surjective_of_surjective _ _ residue_surjective)
  have : Algebra.EssFiniteType K (ResidueField A) := .comp K A (ResidueField A)
  have : Algebra.IsSeparable K (ResidueField A) := Algebra.FormallyUnramified.isSeparable K _
  exact .of_isSeparable K _

/-- **The tangent space at a node is a plane.** If the first Fitting ideal of `Ω[A⁄K]` is a
proper ideal of the local `K`-algebra `A` with unramified quotient, the Zariski cotangent space
`𝔪/𝔪²` has dimension two. -/
theorem finrank_cotangentSpace_eq_two (h : fittingIdeal A Ω[A⁄K] 1 ≠ ⊤) :
    finrank (ResidueField A) (CotangentSpace A) = 2 := by
  have := formallyEtale_residueField_of_fittingIdeal_ne_top h
  -- The conormal map `𝔪/𝔪² → κ ⊗[A] Ω[A⁄K]` is then a bijection.
  have hbij := KaehlerDifferential.kerCotangentToTensor_bijective_of_formallyEtale
    (R := K) (P := A) (S := ResidueField A) residue_surjective
  have hker : RingHom.ker (algebraMap A (ResidueField A)) = maximalIdeal A := by
    rw [ResidueField.algebraMap_eq, ker_residue]
  have e := LinearEquiv.ofBijective _ hbij
  rw [hker] at e
  rw [← finrank_residueField_tensor_kaehlerDifferential_eq_two h,
    (e.extendScalarsOfSurjective residue_surjective).finrank_eq]

end LocalRing

section Localization

variable {K A : Type*} [CommRing K] [CommRing A] [Algebra K A] [Algebra.EssFiniteType K A]
  [Algebra.FormallyUnramified K (A ⧸ fittingIdeal A Ω[A⁄K] 1)]

/-- **The unramified singular locus localizes.** Let `A` be essentially of finite type over a ring
`K`, with `A ⧸ Fitt₁(Ω[A⁄K])` unramified over `K`. Then the same holds for every localization of
`A`: its singular locus is the localization of that of `A`. -/
theorem formallyUnramified_localization_quotient_fittingIdeal (M : Submonoid A) :
    Algebra.FormallyUnramified K (Localization M ⧸
      fittingIdeal (Localization M) Ω[Localization M⁄K] 1) := by
  set I := fittingIdeal A Ω[A⁄K] 1
  let Aₘ := Localization M
  have : Algebra.FormallyUnramified (A ⧸ I) (Aₘ ⧸ I.map (algebraMap A Aₘ)) :=
    .of_isLocalization (Algebra.algebraMapSubmonoid (A ⧸ I) M)
  have : IsScalarTower K (A ⧸ I) (Aₘ ⧸ I.map (algebraMap A Aₘ)) :=
    .of_algebraMap_eq fun _ ↦ rfl
  have : Algebra.FormallyUnramified K (Aₘ ⧸ I.map (algebraMap A Aₘ)) := .comp K (A ⧸ I) _
  exact .of_equiv (Ideal.quotientEquivAlgOfEq K
    ((KaehlerDifferential.isBaseChange_of_formallyEtale K A Aₘ).fittingIdeal_eq_map 1).symm)

end Localization

variable {K A : Type*} [Field K] [CommRing A] [Algebra K A] [Algebra.EssFiniteType K A]
  [Algebra.FormallyUnramified K (A ⧸ fittingIdeal A Ω[A⁄K] 1)]

/-- **The differentials along an unramified singular locus.** Let `A` be essentially of
finite type over a field `K`, with `A ⧸ Fitt₁(Ω[A⁄K])` unramified over `K`. At every point of
the singular locus `V(Fitt₁(Ω[A⁄K]))`, given by a field `L` over `A`, the fibre of `Ω[A⁄K]` has
dimension two. -/
theorem finrank_tensor_kaehlerDifferential_eq_two {L : Type*} [Field L] [Algebra A L]
    (h : fittingIdeal A Ω[A⁄K] 1 ≤ RingHom.ker (algebraMap A L)) :
    finrank L (L ⊗[A] Ω[A⁄K]) = 2 := by
  set p := RingHom.ker (algebraMap A L)
  have : p.IsPrime := RingHom.ker_isPrime _
  let Aₚ := Localization.AtPrime p
  -- The differentials and their Fitting ideals localize.
  have hfit (k : ℕ) : fittingIdeal Aₚ Ω[Aₚ⁄K] k = (fittingIdeal A Ω[A⁄K] k).map (algebraMap A Aₚ) :=
    (KaehlerDifferential.isBaseChange_of_formallyEtale K A Aₚ).fittingIdeal_eq_map k
  have := formallyUnramified_localization_quotient_fittingIdeal (K := K) p.primeCompl
  have hne : fittingIdeal Aₚ Ω[Aₚ⁄K] 1 ≠ ⊤ := by
    rw [hfit 1]
    exact ne_top_of_le_ne_top (maximalIdeal.isMaximal Aₚ).ne_top
      ((Ideal.map_mono h).trans (Localization.AtPrime.map_eq_maximalIdeal (I := p)).le)
  have h2 := finrank_residueField_tensor_kaehlerDifferential_eq_two hne
  -- Compare the fibres at `L` and at the closed point of `Aₚ` through Fitting ideals.
  refine le_antisymm (not_lt.1 fun h3 ↦ ?_) ?_
  · rw [← fittingIdeal_map_eq_bot_iff_lt_finrank, Ideal.map_eq_bot_iff_le_ker] at h3
    have := (fittingIdeal_map_eq_bot_iff_lt_finrank (ResidueField Aₚ) 2).1 <| by
      rw [hfit 2, Ideal.map_map, Ideal.map_eq_bot_iff_le_ker, ← RingHom.comap_ker,
        ResidueField.algebraMap_eq, ker_residue]
      exact h3.trans (Localization.AtPrime.under_maximalIdeal (I := p)).ge
    omega
  · exact (fittingIdeal_map_eq_bot_iff_lt_finrank L 1).1 ((Ideal.map_eq_bot_iff_le_ker _).2 h)

end TauCeti
