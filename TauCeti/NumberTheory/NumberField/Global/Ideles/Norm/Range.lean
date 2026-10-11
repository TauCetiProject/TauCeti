/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.Ideles.Norm.Relative
public import TauCeti.NumberTheory.NumberField.LocalGlobal.Semilocal.Norm.Units
import TauCeti.NumberTheory.Chebotarev.RamifiedPrimes

/-!
# Placewise characterization of idele norms

An idele is a norm precisely when each coordinate is a norm from the corresponding local
étale algebra for a number-field extension `L/K`. No restrictedness hypothesis on local
preimages is needed: outside the finitely many ramified places and nonunit target coordinates,
preimages can be chosen as integral units by unramified unit-norm surjectivity and assembled
into an idele.

This is an arithmetic property of the idele norm map, independent of global reciprocity and
of the Hasse norm principle for field elements.

## Main results

* `TauCeti.GlobalNumberFields.mem_range_ideleNormMap_iff`: the purely placewise norm criterion.
* `TauCeti.GlobalNumberFields.mem_range_normUnits_ideleFiniteCoord_ideleNormMap` and
  `TauCeti.GlobalNumberFields.mem_range_normUnits_ideleInfiniteCoord_ideleNormMap`:
  every coordinate of a relative idele norm is a norm from the local étale algebra.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VI, §2.
* J. S. Milne, *Class Field Theory*, Chapter VII, §2.

The assembly uses Mathlib's `RestrictedProduct.mkUnit`; unit-norm surjectivity is
`TauCeti.map_normUnits_unitFiltration`.
-/

public section
noncomputable section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField NumberField.InfinitePlace
  WithZeroMulInt
open scoped TensorProduct AdicCompletionExtension NumberField.LiesOver WithZero

namespace TauCeti.GlobalNumberFields

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

private theorem exists_restricted_finite_preimages (x : IdeleGroup (𝓞 K) K)
    (hfin : ∀ v : HeightOneSpectrum (𝓞 K),
      v.ideleFiniteCoord x ∈
        (Algebra.normUnits (v.adicCompletion K) (S := v.adicCompletion K ⊗[K] L)).range) :
    ∃ u : (v : HeightOneSpectrum (𝓞 K)) →
        (w : {w : HeightOneSpectrum (𝓞 L) // w.asIdeal.LiesOver v.asIdeal}) →
          (w.1.adicCompletion L)ˣ,
      (∀ v, (∏ᶠ w, Algebra.normUnits (v.adicCompletion K) (u v w)) = v.ideleFiniteCoord x) ∧
        ∀ᶠ w in Filter.cofinite,
          u (w.under (𝓞 K)) ⟨w, inferInstance⟩ ∈ (w.adicCompletionIntegers L).units := by
  classical
  -- Only ramified places, or places with a nonunit target coordinate, require arbitrary
  -- local preimages; every other place admits unit preimages.
  let good (v : HeightOneSpectrum (𝓞 K)) :=
    (∀ w : {w : HeightOneSpectrum (𝓞 L) // w.asIdeal.LiesOver v.asIdeal},
      Algebra.IsUnramifiedAt (𝓞 K) w.1.asIdeal) ∧
      Valued.v (v.ideleFiniteCoord x : v.adicCompletion K) = 1
  have hg : ∀ᶠ v in Filter.cofinite, good v := by
    have hu := eventually_isUnramifiedAt_liesOver K L
    have hx := (FiniteAdeleRing.isUnit_iff.mp
      (IdeleGroup.toFiniteIdele (𝓞 K) K x).isUnit).2
    filter_upwards [hu, hx] with v hv hxv
    exact ⟨hv, by simpa using hxv⟩
  have hchoose (v : HeightOneSpectrum (𝓞 K)) :
      ∃ u : (w : {w : HeightOneSpectrum (𝓞 L) // w.asIdeal.LiesOver v.asIdeal}) →
          (w.1.adicCompletion L)ˣ,
        (∏ᶠ w, Algebra.normUnits (v.adicCompletion K) (u w)) = v.ideleFiniteCoord x ∧
          (good v → ∀ w, Valued.v (u w : w.1.adicCompletion L) = 1) := by
    by_cases h : good v
    · obtain ⟨u, hu, hv⟩ :=
        exists_unit_preimages_of_isUnramifiedAt K L v (v.ideleFiniteCoord x) h.2 (by
        obtain ⟨P, hP, hPv⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral
          (S := 𝓞 L) v.asIdeal
        have hP0 := Ideal.ne_bot_of_mem_primesOver v.ne_bot ⟨hP.isPrime, hPv⟩
        exact ⟨⟨⟨P, hP.isPrime, hP0⟩, hPv⟩, h.1 _⟩)
      exact ⟨u, hu, fun _ ↦ hv⟩
    · obtain ⟨u, hu⟩ := (mem_range_normUnits_adicCompletion_iff K L v _).mp (hfin v)
      exact ⟨u, hu, fun hv ↦ (h hv).elim⟩
  choose u hu huunit using hchoose
  refine ⟨u, hu, ?_⟩
  filter_upwards [(HeightOneSpectrum.tendsto_under_cofinite (𝓞 K) (𝓞 L)).eventually hg] with w hw
  rw [adicCompletionIntegers.mem_units_iff_valued_eq_one]
  exact huunit _ hw ⟨w, inferInstance⟩

/-- Every finite coordinate of an idele norm is a norm from the local étale algebra. -/
theorem mem_range_normUnits_ideleFiniteCoord_ideleNormMap (x : IdeleGroup (𝓞 L) L)
    (v : HeightOneSpectrum (𝓞 K)) :
    v.ideleFiniteCoord (GlobalNumberFields.ideleNormMap K L x) ∈
      (Algebra.normUnits (v.adicCompletion K) (S := v.adicCompletion K ⊗[K] L)).range := by
  rw [mem_range_normUnits_adicCompletion_iff]
  exact ⟨fun w ↦ w.1.ideleFiniteCoord x,
    (GlobalNumberFields.ideleFiniteCoord_ideleNormMap v x).symm⟩

/-- Every infinite coordinate of an idele norm is a norm from the local étale algebra. -/
theorem mem_range_normUnits_ideleInfiniteCoord_ideleNormMap (x : IdeleGroup (𝓞 L) L)
    (v : InfinitePlace K) :
    v.ideleInfiniteCoord (GlobalNumberFields.ideleNormMap K L x) ∈
      (Algebra.normUnits v.Completion (S := v.Completion ⊗[K] L)).range := by
  rw [mem_range_normUnits_completion_iff]
  exact ⟨fun w ↦ w.1.ideleInfiniteCoord x,
    (GlobalNumberFields.ideleInfiniteCoord_ideleNormMap v x).symm⟩

/-- An arbitrary idele is a norm exactly when each finite and infinite coordinate is a norm
from the actual local étale algebra. No cyclicity or Galois hypothesis is required. -/
theorem mem_range_ideleNormMap_iff (x : IdeleGroup (𝓞 K) K) :
    x ∈ (GlobalNumberFields.ideleNormMap K L).toMonoidHom.range ↔
      (∀ v : HeightOneSpectrum (𝓞 K),
        v.ideleFiniteCoord x ∈
          (Algebra.normUnits (v.adicCompletion K) (S := v.adicCompletion K ⊗[K] L)).range) ∧
      ∀ v : InfinitePlace K,
        v.ideleInfiniteCoord x ∈
          (Algebra.normUnits v.Completion (S := v.Completion ⊗[K] L)).range := by
  classical
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨mem_range_normUnits_ideleFiniteCoord_ideleNormMap K L y,
      mem_range_normUnits_ideleInfiniteCoord_ideleNormMap K L y⟩
  rintro ⟨hfin, hinf⟩
  obtain ⟨u, hu, hz⟩ := exists_restricted_finite_preimages K L x hfin
  let z (w : HeightOneSpectrum (𝓞 L)) : (w.adicCompletion L)ˣ :=
    u (w.under (𝓞 K)) ⟨w, inferInstance⟩
  choose t ht using fun v ↦ (mem_range_normUnits_completion_iff K L v _).mp (hinf v)
  let zi (w : InfinitePlace L) : w.Completionˣ :=
    t (w.comap (algebraMap K L)) ⟨w, inferInstance⟩
  let y : IdeleGroup (𝓞 L) L :=
    ideleOfUnits zi z hz
  refine ⟨y, ?_⟩
  refine IdeleGroup.ext (fun v ↦ ?_) (fun v ↦ ?_)
  · have hv := GlobalNumberFields.ideleInfiniteCoord_ideleNormMap v y
    have hz' (w : {w : InfinitePlace L // w.LiesOver v}) : w.1.ideleInfiniteCoord y = t v w := by
      obtain ⟨w, hw⟩ := w
      have hwv := LiesOver.comap_eq w v
      subst v
      exact ideleInfiniteCoord_ideleOfUnits _ _ _ _
    simp_rw [hz'] at hv
    rw [ht] at hv
    exact hv
  · have hv := GlobalNumberFields.ideleFiniteCoord_ideleNormMap v y
    have hz' (w : {w : HeightOneSpectrum (𝓞 L) // w.asIdeal.LiesOver v.asIdeal}) :
        w.1.ideleFiniteCoord y = u v w := by
      obtain ⟨w, hw⟩ := w
      have hwv : w.under (𝓞 K) = v := HeightOneSpectrum.ext hw.over.symm
      subst v
      exact ideleFiniteCoord_ideleOfUnits _ _ _ _
    simp_rw [hz'] at hv
    rw [hu] at hv
    exact hv

end TauCeti.GlobalNumberFields
