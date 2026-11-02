/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.RegularLocalRing.FiniteNormal
public import TauCeti.RingTheory.CohenMacaulay.Basic
public import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.LocalProperties.Basic
import TauCeti.RingTheory.CohenMacaulay.RegularSequence
import TauCeti.RingTheory.Flat.LocalCriterion
import TauCeti.RingTheory.RegularLocalRing.DimensionTwo
import TauCeti.RingTheory.Regular.RegularSequence

/-!
# Miracle flatness

Let `R → S` be a local homomorphism of Noetherian local rings with `R` regular and `S`
Cohen–Macaulay. If `dim S = dim R + dim S ⧸ 𝔪_R S`, then `S` is flat over `R` (Stacks, Lemma
10.128.1 (00R4)). A regular system of parameters `x₁, …, x_d` of `R` generates `𝔪_R`, and the
dimension formula says that its image cuts the dimension of `S` down to that of the closed fibre
`S ⧸ 𝔪_R S`. As `S` is Cohen–Macaulay, the images of the `xᵢ` therefore form an `S`-regular
sequence (`Module.IsCohenMacaulay.isRegular_map_algebraMap`), and a local homomorphism carrying
generators of the maximal ideal of the source to a regular sequence is flat
(`Module.Flat.of_isWeaklyRegular_map_algebraMap`). The algebra `S` need not be finite over `R`;
this matters for the localizations `B_𝔮` of a finite algebra `B` at its maximal ideals, which are
in general not finite over `R`.

The file also proves finite normal cases in dimension two, where Cohen–Macaulayness of the target
comes from normality. A finite injective local algebra over a two-dimensional regular local ring
is free, and hence flat, if it is a normal local domain. More generally, a finite torsion-free
algebra `B` over a two-dimensional regular local ring `A` is free if every localization of `B` at
a maximal ideal is a normal domain; here `B` need not be local.

The two dimension-two proofs show that a pair `x, y` generating the maximal ideal of `A` is a
regular sequence on `B`, and then apply `TauCeti.IsRegularLocalRing.free_of_isWeaklyRegular`. In
the local case normality of `B` gives this directly. In general `x` is regular because `B` is
torsion free, and regularity of `y` modulo `x` may be checked after localizing at the maximal
ideals `𝔮` of `B`. As `A` is factorial, hence integrally closed, going down along `A → B` gives
`B_𝔮` dimension two, and the normal domain `B_𝔮` is then Cohen–Macaulay, so `x, y` is a regular
sequence on `B_𝔮`.

## Main results

* `TauCeti.Algebra.flat_of_isCohenMacaulay`: **miracle flatness**, Stacks, Lemma 10.128.1 (00R4).
* `TauCeti.Algebra.flat_of_normal_dim_two`: a finite injective normal local algebra over a
  two-dimensional regular local ring is flat.
* `TauCeti.Algebra.free_of_normal_dim_two`: a finite torsion-free algebra over a two-dimensional
  regular local ring whose localizations at maximal ideals are normal domains is free.

## References

* [The Stacks Project, Lemma 10.128.1](https://stacks.math.columbia.edu/tag/00R4), miracle
  flatness. Its induction on `dim R` is packaged here in the regular-sequence form of the local
  flatness criterion.
* The Stacks Project, Lemma 58.21.3 (0BMA), whose proof in dimension two needs the flatness of
  finite normal algebras that are not local.
-/

public section

open IsLocalRing Ideal RingTheory.Sequence

namespace TauCeti.Algebra

/-- **Miracle flatness.** Let `R → S` be a local homomorphism of Noetherian local rings with `R`
regular and `S` Cohen–Macaulay. If `dim S = dim R + dim S ⧸ 𝔪_R S`, then `S` is flat over `R`.
Here `S` need not be finite over `R`. -/
@[stacks 00R4]
theorem flat_of_isCohenMacaulay {R S : Type*} [CommRing R] [IsRegularLocalRing R] [CommRing S]
    [IsLocalRing S] [IsNoetherianRing S] [Algebra R S] [IsLocalHom (algebraMap R S)]
    (hS : Module.IsCohenMacaulay S S) (hdim : ringKrullDim S =
      ringKrullDim R + ringKrullDim (S ⧸ (maximalIdeal R).map (algebraMap R S))) :
    Module.Flat R S := by
  -- A regular system of parameters of `R` maps to an `S`-regular sequence.
  obtain ⟨s, hcard, hspan⟩ :=
    Submodule.FG.exists_span_finset_card_eq_spanFinrank (maximalIdeal R).fg_of_isNoetherianRing
  have hofList : ofList s.toList = maximalIdeal R := by simpa [ofList] using hspan
  refine Module.Flat.of_isWeaklyRegular_map_algebraMap hofList
    (hS.isRegular_map_algebraMap hofList ?_).toIsWeaklyRegular
  rw [Finset.length_toList, hcard, IsRegularLocalRing.spanFinrank_maximalIdeal, hdim, add_comm]

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] [IsRegularLocalRing A]
  [Module.Finite A B]

/-- A finite injective algebra over a two-dimensional regular local ring is flat if it is a
normal local domain. Locality of the algebra map follows from finiteness and injectivity. -/
theorem flat_of_normal_dim_two [IsLocalRing B] [IsDomain B] [IsIntegrallyClosed B]
    (hinj : Function.Injective (algebraMap A B)) (hdim : ringKrullDim A = 2) :
    Module.Flat A B := by
  have : FaithfulSMul A B := (faithfulSMul_iff_algebraMap_injective A B).mpr hinj
  have : IsLocalHom (algebraMap A B) := inferInstance
  -- Normality makes a parameter pair of the base regular on the algebra.
  obtain ⟨x, y, hxy, -, hreg⟩ :=
    TauCeti.IsRegularLocalRing.exists_regular_parameters_of_finite_normal hinj hdim
  have := TauCeti.IsRegularLocalRing.free_of_isWeaklyRegular hdim hxy hreg.toIsWeaklyRegular
  infer_instance

/-- A finite torsion-free algebra over a two-dimensional regular local ring is free if its
localizations at maximal ideals are normal domains. The algebra need not be local, and its
localizations need not be finite over the base. -/
theorem free_of_normal_dim_two [Module.IsTorsionFree A B] (hdim : ringKrullDim A = 2)
    (hnormal : ∀ (𝔮 : Ideal B) [𝔮.IsMaximal],
      IsDomain (Localization.AtPrime 𝔮) ∧ IsIntegrallyClosed (Localization.AtPrime 𝔮)) :
    Module.Free A B := by
  -- The base is factorial, hence integrally closed, so going down applies to `A → B`.
  have : UniqueFactorizationMonoid A :=
    TauCeti.IsRegularLocalRing.uniqueFactorizationMonoid_of_ringKrullDim_le_two hdim.le
  obtain ⟨x, y, hxy⟩ := TauCeti.IsRegularLocalRing.exists_span_pair_eq_maximalIdeal hdim
  have hx0 := TauCeti.IsLocalRing.ne_zero_of_span_pair_eq_maximalIdeal hdim hxy
  refine TauCeti.IsRegularLocalRing.free_of_isWeaklyRegular hdim hxy
    ((isWeaklyRegular_cons_iff B x [y]).mpr ⟨IsSMulRegular.of_ne_zero hx0,
      (isWeaklyRegular_singleton_iff _ _).mpr
        (TauCeti.isSMulRegular_quotSMulTop_iff.mpr fun b c hc ↦ ?_)⟩)
  -- It suffices to show `b ∈ (x)` after localizing at every maximal ideal of `B`.
  suffices hb : b ∈ span {algebraMap A B x} by
    obtain ⟨e, rfl⟩ := mem_span_singleton'.mp hb
    rw [Submodule.mem_smul_pointwise_iff_exists]
    exact ⟨e, Submodule.mem_top, by rw [Algebra.smul_def, mul_comm]⟩
  refine Ideal.mem_of_localization_maximal fun 𝔮 _ ↦ ?_
  obtain ⟨_, _⟩ := hnormal 𝔮
  set L := Localization.AtPrime 𝔮
  -- The images of `x, y` form a regular sequence on `B_𝔮`, by going down and normality.
  have hreg := TauCeti.isRegular_pair_localization_of_isIntegrallyClosed hdim 𝔮 hxy
  obtain ⟨-, hyreg⟩ := (isWeaklyRegular_cons_iff L _ _).mp hreg.toIsWeaklyRegular
  replace hyreg := (isWeaklyRegular_singleton_iff _ _).mp hyreg
  have hcL : algebraMap A L x * algebraMap B L c = algebraMap A L y * algebraMap B L b := by
    simpa [Algebra.smul_def, IsScalarTower.algebraMap_apply A B L] using
      congrArg (algebraMap B L) hc
  obtain ⟨d, -, hd⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp
    (TauCeti.isSMulRegular_quotSMulTop_iff.mp hyreg _ _ hcL)
  rw [Ideal.map_span, Set.image_singleton, ← IsScalarTower.algebraMap_apply, ← hd]
  exact mem_span_singleton'.mpr ⟨d, mul_comm _ _⟩

end TauCeti.Algebra
