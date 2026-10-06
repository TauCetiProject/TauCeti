/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Global.LocalNorm
import TauCeti.NumberTheory.LocalField.Norm.Unramified.Basic
import TauCeti.RingTheory.DedekindDomain.AdicValuation.RamificationIndex
import Mathlib.RingTheory.DedekindDomain.Different

/-!
# Placewise characterization of idele norms

An idele is a norm precisely when each coordinate is a norm from the corresponding local
étale algebra. The restricted-product condition is essential: arbitrary local preimages need
not form an idele. Outside the finitely many ramified places, a unit coordinate has unit
preimages by norm-surjectivity on the units of an unramified extension.

This is an arithmetic property of the idele norm map, independent of global reciprocity and
of the Hasse norm principle for field elements.

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

namespace TauCeti.ClassFieldTheory

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

private theorem exists_unit_preimages (v : HeightOneSpectrum (𝓞 K))
    (a : (v.adicCompletion K)ˣ) (ha : Valued.v (a : v.adicCompletion K) = 1)
    (hU : ∀ w : {w : HeightOneSpectrum (𝓞 L) // w.asIdeal.LiesOver v.asIdeal},
      Algebra.IsUnramifiedAt (𝓞 K) w.1.asIdeal) :
    ∃ u : (w : {w : HeightOneSpectrum (𝓞 L) // w.asIdeal.LiesOver v.asIdeal}) →
        (w.1.adicCompletion L)ˣ,
      (∏ᶠ w, Algebra.normUnits (v.adicCompletion K) (u w)) = a ∧
        ∀ w, Valued.v (u w : w.1.adicCompletion L) = 1 := by
  classical
  obtain ⟨P, hP, hPv⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral
    (S := 𝓞 L) v.asIdeal
  have hP0 := Ideal.ne_bot_of_mem_primesOver v.ne_bot ⟨hP.isPrime, hPv⟩
  let w : {w : HeightOneSpectrum (𝓞 L) // w.asIdeal.LiesOver v.asIdeal} :=
    ⟨⟨P, hP.isPrime, hP0⟩, hPv⟩
  let : Algebra.IsUnramifiedAt (𝓞 K) w.1.asIdeal := hU w
  have haU : a ∈ unitFiltration (v.adicCompletion K) 0 := by
    rw [mem_unitFiltration_zero]
    exact (ValuativeRel.isEquiv (ValuativeRel.valuation (v.adicCompletion K))
      (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰)).eq_one_iff_eq_one.mpr ha
  obtain ⟨b, hb, hba⟩ := (Subgroup.mem_map.mp
    ((map_normUnits_unitFiltration (v.adicCompletion K) (w.1.adicCompletion L) 0).symm ▸ haU))
  refine ⟨Pi.mulSingle w b, ?_, ?_⟩
  · rw [finprod_eq_single _ w]
    · simpa using hba
    · intro w' hw'
      simp [Pi.mulSingle_eq_of_ne hw']
  · intro w'
    by_cases hw' : w' = w
    · subst w'
      simp only [Pi.mulSingle_eq_same]
      exact (ValuativeRel.isEquiv (ValuativeRel.valuation (w.1.adicCompletion L))
        (Valued.v : Valuation (w.1.adicCompletion L) ℤᵐ⁰)).eq_one_iff_eq_one.mp
          ((mem_unitFiltration_zero b).mp hb)
    · simp [Pi.mulSingle_eq_of_ne hw']

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
  -- Only places below the different, or with a nonunit target coordinate, require arbitrary
  -- local preimages; every other place admits unit preimages.
  let good (v : HeightOneSpectrum (𝓞 K)) :=
    (∀ w : {w : HeightOneSpectrum (𝓞 L) // w.asIdeal.LiesOver v.asIdeal},
      Algebra.IsUnramifiedAt (𝓞 K) w.1.asIdeal) ∧
      Valued.v (v.ideleFiniteCoord x : v.adicCompletion K) = 1
  have hg : ∀ᶠ v in Filter.cofinite, good v := by
    have hd := Ideal.finite_factors
      (differentIdeal_ne_bot (A := 𝓞 K) (B := 𝓞 L))
    have hu : ∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite,
        ∀ w : {w : HeightOneSpectrum (𝓞 L) // w.asIdeal.LiesOver v.asIdeal},
          Algebra.IsUnramifiedAt (𝓞 K) w.1.asIdeal := by
      refine Filter.eventually_cofinite.mpr ((hd.image (HeightOneSpectrum.under (𝓞 K))).subset ?_)
      intro v hv
      push Not at hv
      obtain ⟨w, hw⟩ := hv
      exact ⟨w.1, dvd_differentIdeal_iff.mpr hw, HeightOneSpectrum.ext w.2.over.symm⟩
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
    · obtain ⟨u, hu, hv⟩ := exists_unit_preimages K L v (v.ideleFiniteCoord x) h.2 h.1
      exact ⟨u, hu, fun _ ↦ hv⟩
    · obtain ⟨u, hu⟩ := (mem_range_finite_normUnits_iff K L v _).mp (hfin v)
      exact ⟨u, hu, fun hv ↦ (h hv).elim⟩
  choose u hu huunit using hchoose
  refine ⟨u, hu, ?_⟩
  filter_upwards [(HeightOneSpectrum.tendsto_under_cofinite (𝓞 K) (𝓞 L)).eventually hg] with w hw
  rw [adicCompletionIntegers.mem_units_iff_valued_eq_one]
  exact huunit _ hw ⟨w, inferInstance⟩

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
    exact ⟨ideleFiniteCoord_mem_range_normUnits K L y,
      ideleInfiniteCoord_mem_range_normUnits K L y⟩
  rintro ⟨hfin, hinf⟩
  obtain ⟨u, hu, hz⟩ := exists_restricted_finite_preimages K L x hfin
  let z (w : HeightOneSpectrum (𝓞 L)) : (w.adicCompletion L)ˣ :=
    u (w.under (𝓞 K)) ⟨w, inferInstance⟩
  choose t ht using fun v ↦ (mem_range_infinite_normUnits_iff K L v _).mp (hinf v)
  let zi (w : InfinitePlace L) : w.Completionˣ :=
    t (w.comap (algebraMap K L)) ⟨w, inferInstance⟩
  let y : IdeleGroup (𝓞 L) L :=
    MulEquiv.prodUnits.symm (MulEquiv.piUnits.symm zi, RestrictedProduct.mkUnit z hz)
  refine ⟨y, ?_⟩
  apply Units.ext
  apply Prod.ext
  · funext v
    have hv := GlobalNumberFields.ideleInfiniteCoord_ideleNormMap v y
    have hz' (w : {w : InfinitePlace L // w.LiesOver v}) : w.1.ideleInfiniteCoord y = t v w := by
      obtain ⟨w, hw⟩ := w
      have hwv := LiesOver.comap_eq w v
      subst v
      apply Units.ext
      rw [coe_ideleInfiniteCoord]
      -- The product-unit constructor reads coordinates componentwise after the dependent
      -- place index is identified with its contraction.
      rfl
    simp_rw [hz'] at hv
    rw [ht] at hv
    simpa only [coe_ideleInfiniteCoord, ContinuousMonoidHom.coe_toMonoidHom,
      MonoidHom.coe_ofClass] using congrArg Units.val hv
  · apply FiniteAdeleRing.ext K
    intro v
    have hv := GlobalNumberFields.ideleFiniteCoord_ideleNormMap v y
    have hz' (w : {w : HeightOneSpectrum (𝓞 L) // w.asIdeal.LiesOver v.asIdeal}) :
        w.1.ideleFiniteCoord y = u v w := by
      obtain ⟨w, hw⟩ := w
      have hwv : w.under (𝓞 K) = v := HeightOneSpectrum.ext hw.over.symm
      subst v
      apply Units.ext
      rw [coe_ideleFiniteCoord]
      -- `RestrictedProduct.mkUnit` has the prescribed coordinate, with the dependent index
      -- now written as the contraction of `w`.
      rfl
    simp_rw [hz'] at hv
    rw [hu] at hv
    simpa only [coe_ideleFiniteCoord, ContinuousMonoidHom.coe_toMonoidHom,
      MonoidHom.coe_ofClass] using congrArg Units.val hv

end TauCeti.ClassFieldTheory
