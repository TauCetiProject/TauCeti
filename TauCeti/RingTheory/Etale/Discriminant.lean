/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Mathlib.RingTheory.Etale.Field
public import TauCeti.RingTheory.Discriminant.BaseChange
public import TauCeti.RingTheory.Trace.Form
import Mathlib.Algebra.DualNumber
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Ideal.Nonunits
import Mathlib.RingTheory.Smooth.Fiber
import TauCeti.RingTheory.Unramified.Fiber

/-!
# The discriminant criterion for étaleness

A finite-dimensional algebra over a field is étale iff its trace form is nondegenerate, and a
finite free algebra over any commutative ring is étale iff the discriminant of a basis is a unit
(Stacks, Lemma 49.3.1 (0BJF), affine form).

## Main results

* `TauCeti.Algebra.etale_iff_traceForm_nondegenerate`: a finite-dimensional algebra over a field is
  étale iff its trace form is nondegenerate.
* `TauCeti.Algebra.algebraMap_discr_ne_zero_iff_etale_baseChange`: the discriminant of a basis has
  nonzero image in a field `K` iff the fibre `K ⊗[A] B` is étale over `K`.
* `TauCeti.Algebra.etale_of_isUnit_discr`: a finite free algebra over any ring whose basis has unit
  discriminant is étale.
* `TauCeti.Algebra.etale_iff_isUnit_discr`: a finite free algebra is étale iff the discriminant of
  a basis is a unit.
* `TauCeti.Algebra.isUnit_algebraMap_discr_iff_etale_baseChange`: the discriminant of a basis maps
  to a unit in an `A`-algebra `A'` iff the base change to `A'` is étale.
* `TauCeti.Algebra.isUnit_discr_localization_iff`: the discriminant of a basis
  is a unit at a prime `𝔭` iff the base change to `A_𝔭` is étale over `A_𝔭`.

## References

* [Stacks Project, Lemma 49.3.1](https://stacks.math.columbia.edu/tag/0BJF).
* Ported from T. Dupuy, T. Tucker and Z. Wang,
  [pcfawd-formalization](https://github.com/tdupu/pcfawd-formalization) at commit
  `9a20b3f351446d64e6015d704198bc71c7002008` (Apache-2.0),
  `lean/Pcf/Stacks/Purity/DiscriminantFiber.lean` and
  `lean/Pcf/Stacks/Purity/DiscriminantGlobal.lean`, namespace `Pcf.Stacks`:
  `etale_iff_traceForm_nondegenerate` combines its
  `Algebra.traceForm_nondegenerate_of_formallyEtale` and
  `Algebra.formallyEtale_of_discr_ne_zero_of_basis_global`; `etale_of_isUnit_discr` generalizes its
  `Algebra.etale_of_isUnit_discr_of_basis_global` from a local base to any base;
  `etale_iff_isUnit_discr` adds the converse, its
  `Algebra.isUnit_discr_of_etale_of_basis`, likewise generalized from a local base to any base;
  and `isUnit_discr_localization_iff` extends its
  `Algebra.isUnit_map_discr_of_etale_baseChange` to an equivalence.
-/

public section

open scoped TensorProduct

namespace TauCeti

/-- A finite-dimensional algebra over a field is étale iff its trace form is nondegenerate. The
fibre case in the proof of Stacks, Lemma 49.3.1 (0BJF). -/
@[stacks 0BJF "the case of a field"]
theorem Algebra.etale_iff_traceForm_nondegenerate (K B : Type*) [Field K] [CommRing B]
    [Algebra K B] [FiniteDimensional K B] :
    Algebra.Etale K B ↔ (Algebra.traceForm K B).Nondegenerate := by
  classical
  constructor
  · intro hB
    obtain ⟨I, _, Ai, _, _, e, hAi⟩ := (Algebra.Etale.iff_exists_algEquiv_prod K B).mp hB
    have : Fintype I := Fintype.ofFinite I
    have hfin : ∀ i, Module.Finite K (Ai i) := fun i ↦ (hAi i).1
    have hsep : ∀ i, Algebra.IsSeparable K (Ai i) := fun i ↦ (hAi i).2
    exact (Algebra.traceForm_nondegenerate_congr e).mpr
      ((Algebra.traceForm_pi_nondegenerate_iff Ai).mpr fun i ↦ traceForm_nondegenerate K (Ai i))
  · intro h
    have : IsReduced B := Algebra.isReduced_of_traceForm_nondegenerate h
    have : IsArtinianRing B := isArtinian_of_tower K inferInstance
    let F (m : MaximalSpectrum B) : Type _ := B ⧸ m.asIdeal
    let (m : MaximalSpectrum B) : Field (F m) := Ideal.Quotient.field m.asIdeal
    let e : B ≃ₐ[K] ∀ m, F m := (IsArtinianRing.equivPi B).restrictScalars K
    have hfin (m : MaximalSpectrum B) : Module.Finite K (F m) :=
      Module.Finite.of_surjective ((LinearMap.proj m).comp e.toLinearMap)
        ((Function.surjective_eval m).comp e.surjective)
    have hF : ∀ m, (Algebra.traceForm K (F m)).Nondegenerate :=
      (Algebra.traceForm_pi_nondegenerate_iff F).mp ((Algebra.traceForm_nondegenerate_congr e).mp h)
    refine (Algebra.Etale.iff_exists_algEquiv_prod K B).mpr
      ⟨MaximalSpectrum B, inferInstance, F, inferInstance, inferInstance, e, fun m ↦ ?_⟩
    exact ⟨hfin m, ((traceForm_nondegenerate_tfae K (F m)).out 3 1).mp (hF m)⟩

/-- The discriminant of a basis of a finite free `A`-algebra `B` has nonzero image in a field `K`
over `A` iff the fibre `K ⊗[A] B` is étale over `K`. -/
theorem Algebra.algebraMap_discr_ne_zero_iff_etale_baseChange {A B ι : Type*} [CommRing A]
    [CommRing B] [Algebra A B] [Fintype ι] [DecidableEq ι] (b : Module.Basis ι A B)
    (K : Type*) [Field K] [Algebra A K] :
    algebraMap A K (Algebra.discr A b) ≠ 0 ↔ Algebra.Etale K (K ⊗[A] B) := by
  have : FiniteDimensional K (K ⊗[A] B) := Module.Finite.of_basis (Algebra.TensorProduct.basis K b)
  rw [Algebra.etale_iff_traceForm_nondegenerate,
    ← Algebra.discr_ne_zero_iff_traceForm_nondegenerate (Algebra.TensorProduct.basis K b),
    Algebra.discr_basis_baseChange]

/-- A finite free algebra whose basis has unit discriminant is étale. -/
theorem Algebra.etale_of_isUnit_discr {A B ι : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [Fintype ι] [DecidableEq ι] (b : Module.Basis ι A B) (hb : IsUnit (Algebra.discr A b)) :
    Algebra.Etale A B := by
  have : Module.Free A B := Module.Free.of_basis b
  have : Module.Finite A B := Module.Finite.of_basis b
  have : Module.FinitePresentation A B := Module.finitePresentation_of_projective A B
  have : Algebra.FormallyUnramified A B :=
    Algebra.FormallyUnramified.of_formallyUnramified_baseChange_field fun K _ _ ↦ by
      have : Algebra.Etale K (K ⊗[A] B) :=
        (Algebra.algebraMap_discr_ne_zero_iff_etale_baseChange b K).mp
          (hb.map (algebraMap A K)).ne_zero
      infer_instance
  exact Algebra.Etale.of_formallyUnramified_of_flat

/-- **The discriminant criterion.** A finite free algebra is étale iff the discriminant of a basis
is a unit. Stacks, Lemma 49.3.1 (0BJF), affine form. -/
@[stacks 0BJF "affine form"]
theorem Algebra.etale_iff_isUnit_discr (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι A B) :
    Algebra.Etale A B ↔ IsUnit (Algebra.discr A b) := by
  refine ⟨fun hB ↦ ?_, Algebra.etale_of_isUnit_discr b⟩
  by_contra hunit
  obtain ⟨m, hm, hdm⟩ := exists_max_ideal_of_mem_nonunits hunit
  let : Field (A ⧸ m) := Ideal.Quotient.field m
  refine (Algebra.algebraMap_discr_ne_zero_iff_etale_baseChange b (A ⧸ m)).mpr inferInstance ?_
  rw [Ideal.Quotient.algebraMap_eq]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr hdm

/-- The discriminant of a basis of a finite free `A`-algebra `B` maps to a unit in an `A`-algebra
`A'` iff the base change `A' ⊗[A] B` is étale over `A'`. -/
theorem Algebra.isUnit_algebraMap_discr_iff_etale_baseChange {A B ι : Type*} [CommRing A]
    [CommRing B] [Algebra A B] [Fintype ι] [DecidableEq ι] (b : Module.Basis ι A B)
    (A' : Type*) [CommRing A'] [Algebra A A'] :
    IsUnit (algebraMap A A' (Algebra.discr A b)) ↔ Algebra.Etale A' (A' ⊗[A] B) := by
  rw [Algebra.etale_iff_isUnit_discr _ _ (Algebra.TensorProduct.basis A' b),
    Algebra.discr_basis_baseChange]

/-- The discriminant of a basis of a finite free algebra is a unit at a prime `𝔭` iff the base
change to the localization `A_𝔭` is étale over `A_𝔭`. -/
theorem Algebra.isUnit_discr_localization_iff {A B ι : Type*} [CommRing A]
    [CommRing B] [Algebra A B] [Fintype ι] [DecidableEq ι] (b : Module.Basis ι A B) (p : Ideal A)
    [p.IsPrime] :
    IsUnit (algebraMap A (Localization.AtPrime p) (Algebra.discr A b)) ↔
      Algebra.Etale (Localization.AtPrime p) (Localization.AtPrime p ⊗[A] B) :=
  Algebra.isUnit_algebraMap_discr_iff_etale_baseChange b _

/-- The dual numbers over a field are not étale, and the discriminant of every basis vanishes. -/
example (k : Type*) [Field k] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι k (DualNumber k)) :
    ¬ Algebra.Etale k (DualNumber k) ∧ Algebra.discr k b = 0 := by
  have hnot : ¬ Algebra.Etale k (DualNumber k) := by
    intro h
    have : IsReduced (DualNumber k) := Algebra.FormallyUnramified.isReduced_of_field k _
    have hε : IsNilpotent (DualNumber.eps : DualNumber k) := ⟨2, DualNumber.eps_pow_two⟩
    simpa using congrArg TrivSqZeroExt.snd hε.eq_zero
  refine ⟨hnot, ?_⟩
  by_contra hd
  exact hnot ((Algebra.etale_iff_isUnit_discr k _ b).mpr (Ne.isUnit hd))

end TauCeti
