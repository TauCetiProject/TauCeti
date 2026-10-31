/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.RegularLocalRing.FiniteNormal
public import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.LocalProperties.Basic
import TauCeti.RingTheory.CohenMacaulay.RegularSequence
import TauCeti.RingTheory.RegularLocalRing.DimensionTwo
import TauCeti.RingTheory.Regular.RegularSequence

/-!
# Flatness of finite normal algebras in dimension two

A finite injective local algebra over a two-dimensional regular local ring is free, and hence
flat, if it is a normal local domain. More generally, a finite torsion-free algebra `B` over a
two-dimensional regular local ring `A` is free if every localization of `B` at a maximal ideal is
a normal domain; here `B` need not be local. These are finite cases of miracle flatness.

Both proofs show that a pair `x, y` generating the maximal ideal of `A` is a regular sequence on
`B`, and then apply `TauCeti.IsRegularLocalRing.free_of_isWeaklyRegular`. In the local case
normality of `B` gives this directly. In general `x` is regular because `B` is torsion free, and
regularity of `y` modulo `x` may be checked after localizing at the maximal ideals `𝔮` of `B`. As
`A` is factorial, hence integrally closed, going down along `A → B` gives `B_𝔮` dimension two, and
the normal domain `B_𝔮` is then Cohen–Macaulay, so `x, y` is a regular sequence on `B_𝔮`.

## Main results

* `TauCeti.Algebra.flat_of_normal_dim_two`: a finite injective normal local algebra is flat.
* `TauCeti.Algebra.free_of_normal_dim_two`: a finite torsion-free algebra whose localizations at
  maximal ideals are normal domains is free.

## References

* The Stacks Project, Lemma 10.128.1 (00R4), miracle flatness. This file proves finite normal
  dimension-two cases, rather than the general Cohen–Macaulay statement.
* The Stacks Project, Lemma 58.21.3 (0BMA), whose proof in dimension two needs the flatness of
  finite normal algebras that are not local.
-/

public section

open IsLocalRing Ideal RingTheory.Sequence

namespace TauCeti.Algebra

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
