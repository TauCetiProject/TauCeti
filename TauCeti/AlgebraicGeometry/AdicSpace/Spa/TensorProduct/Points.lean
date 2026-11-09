/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.TensorProduct.Plus
public import TauCeti.RingTheory.Huber.TensorProduct.Pushout
import TauCeti.AlgebraicGeometry.AdicSpace.ValuationSpectrum.Amalgamation
import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Completion.Basic
import TauCeti.RingTheory.Valuation.Continuous.Horizontal

/-!
# Points of completed tensor products over Tate rings

Compatible points of two Huber pairs over a Tate ring lift to their completed tensor product.
There is no sheafiness or finite-type hypothesis, and valuations can have arbitrary rank.
The lift is not asserted to be unique.

Algebraic valuation amalgamation gives a valuation on the uncompleted tensor product. Its
horizontal restriction is continuous and preserves the two factor valuations. Finally the
invariance of the adic spectrum under completion gives the required point of the completed
pair, with its integral-closure plus ring.

## References

* R. Huber, *A generalization of formal schemes and rigid analytic varieties*, Math. Z. 217
  (1994), proof of Lemma 3.9(i).
* T. Wedhorn, *Adic Spaces*, arXiv:1910.05934v1, §7.1.2 and Proposition 7.48.
-/

public section

open Algebra.TensorProduct TensorProduct Topology Filter UniformSpace
open scoped Pointwise

namespace TauCeti.ValuationSpectrum

variable (A : Type*) {B C : Type*} [CommRing A] [CommRing B] [CommRing C]
  [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
  [IsTopologicalRing A] [IsTopologicalRing B] [IsTopologicalRing C]
  [Huber.IsTateRing A] [Huber.IsHuberRing B] [Huber.IsHuberRing C]
  [Algebra A B] [Algebra A C]
  [Huber.IsAdicHom (algebraMap A B)] [Huber.IsAdicHom (algebraMap A C)]

open Huber in
/-- Compatible points of two Huber pairs over a Tate base amalgamate to a point of the tensor
product whose valuation is `< 1` on a neighbourhood of zero for the tensor topology; both factor
restrictions of the amalgam are continuous. -/
private lemma exists_amalgam_lt_one_mem_nhds (S : Pair B) (T : Pair C)
    (y : spa S.plus) (x : spa T.plus)
    (h : comap (algebraMap A B) y.1 = comap (algebraMap A C) x.1) :
    ∃ v : Spv (B ⊗[A] C), comap includeLeftRingHom v = y.1 ∧
      comap (includeRight : C →ₐ[A] B ⊗[A] C).toRingHom v = x.1 ∧
      (v.valuation.comap includeLeftRingHom).IsContinuous ∧
      (v.valuation.comap (includeRight : C →ₐ[A] B ⊗[A] C).toRingHom).IsContinuous ∧
      letI := tensorTopology A B C; {a : B ⊗[A] C | v.valuation a < 1} ∈ 𝓝 0 := by
  let := tensorTopology A B C
  have := isTopologicalRing_tensorTopology A B C
  have := isHuberRing_tensorTopology A B C
  let Q : Subring (B ⊗[A] C) := S.plus.map includeLeftRingHom ⊔
    T.plus.map (includeRight : C →ₐ[A] B ⊗[A] C).toRingHom
  -- First amalgamate algebraically and bound the valuation on the open tensor plus subring.
  obtain ⟨v, hy, hx⟩ := exists_amalgamation y.1 x.1 h
  have hcy : (v.valuation.comap includeLeftRingHom).IsContinuous := by
    rw [← isContinuous_ofValuation_iff, ← comap_ofValuation, ofValuation_valuation, hy]
    exact (mem_spa_iff _ _).mp y.2 |>.1
  have hcx : (v.valuation.comap (includeRight : C →ₐ[A] B ⊗[A] C).toRingHom).IsContinuous := by
    rw [← isContinuous_ofValuation_iff, ← comap_ofValuation, ofValuation_valuation, hx]
    exact (mem_spa_iff _ _).mp x.2 |>.1
  have hQ : Q ≤ v.valuation.integer := by
    refine sup_le (Subring.map_le_iff_le_comap.mpr ?_)
      (Subring.map_le_iff_le_comap.mpr ?_)
    · intro b hb
      have hb' := ((mem_spa_iff _ _).mp y.2).2 b hb
      rw [← hy, comap_vle] at hb'
      exact (Valuation.mem_integer_iff _ _).mpr (by
        simpa only [map_one] using (valuation_le_iff v _ _).mpr hb')
    · intro c hc
      have hc' := ((mem_spa_iff _ _).mp x.2).2 c hc
      rw [← hx, comap_vle] at hc'
      exact (Valuation.mem_integer_iff _ _).mpr (by
        simpa only [map_one] using (valuation_le_iff v _ _).mpr hc')
  obtain ⟨ϖ, hϖ⟩ := IsTateRing.exists_isPseudoUniformizer (A := A)
  have hϖB := hϖ.map (φ := algebraMap A B) (IsAdicHom.continuous inferInstance)
  have hϖC := hϖ.map (φ := algebraMap A C) (IsAdicHom.continuous inferInstance)
  let t := includeLeftRingHom (R := A) (B := C) (algebraMap A B ϖ)
  have ht : IsUnit t := (hϖB.isUnit.map includeLeftRingHom)
  have htlt : v.valuation t < 1 := hcy.lt_one_of_isTopologicallyNilpotent
    hϖB.isTopologicallyNilpotent
  have hU : {a : B ⊗[A] C | v.valuation a < 1} ∈ 𝓝 0 := by
    have hn := ht.smul_mem_nhds_smul_iff (a := (0 : B ⊗[A] C)) (s := (Q : Set _))
    rw [smul_zero] at hn
    filter_upwards [hn.mpr ((S.isOpen_sup_map_tensorTopology T).mem_nhds Q.zero_mem)] with a ha
    obtain ⟨b, hb, rfl⟩ := ha
    have hb' : v.valuation b ≤ 1 := (Valuation.mem_integer_iff _ _).mp (hQ hb)
    simpa only [smul_eq_mul, map_mul] using
      (mul_le_of_le_one_right' hb' (a := v.valuation t)).trans_lt htlt
  exact ⟨v, hy, hx, hcy, hcx, hU⟩

open Huber in
/-- An amalgam with continuous factor restrictions whose valuation is `< 1` near zero for the
tensor topology has a continuous horizontal restriction with the same two restrictions. -/
private lemma exists_isContinuous_amalgam (S : Pair B) (T : Pair C)
    (y : spa S.plus) (x : spa T.plus) (v : Spv (B ⊗[A] C))
    (hy : comap includeLeftRingHom v = y.1)
    (hx : comap (includeRight : C →ₐ[A] B ⊗[A] C).toRingHom v = x.1)
    (hcy : (v.valuation.comap includeLeftRingHom).IsContinuous)
    (hcx : (v.valuation.comap (includeRight : C →ₐ[A] B ⊗[A] C).toRingHom).IsContinuous)
    (hU : letI := tensorTopology A B C; {a : B ⊗[A] C | v.valuation a < 1} ∈ 𝓝 0) :
    ∃ w : Spv (B ⊗[A] C), (letI := tensorTopology A B C; w.IsContinuous) ∧
      comap includeLeftRingHom w = y.1 ∧
      comap (includeRight : C →ₐ[A] B ⊗[A] C).toRingHom w = x.1 := by
  let := tensorTopology A B C
  have := isTopologicalRing_tensorTopology A B C
  obtain ⟨ϖ, hϖ⟩ := IsTateRing.exists_isPseudoUniformizer (A := A)
  have hϖB := hϖ.map (φ := algebraMap A B) (IsAdicHom.continuous inferInstance)
  have hϖC := hϖ.map (φ := algebraMap A C) (IsAdicHom.continuous inferInstance)
  -- Horizontal restriction makes the amalgam continuous without altering either factor.
  let w := v.valuation.restrictToIdeal ⊤ ⟨⊤, Ideal.fg_top _, rfl⟩
  have hw : w.IsContinuous := v.valuation.isContinuous_restrictToIdeal_top hU
  have hwy : comap includeLeftRingHom (ofValuation w) = y.1 := by
    rw [comap_ofValuation]
    exact (ofValuation_eq_of_isEquiv (v.valuation.isEquiv_restrictToIdeal_comap _ _ _ hcy
      hϖB.isUnit hϖB.isTopologicallyNilpotent)).trans (by
        simpa only [← comap_ofValuation, ofValuation_valuation] using hy)
  have hwx : comap (includeRight : C →ₐ[A] B ⊗[A] C).toRingHom (ofValuation w) = x.1 := by
    rw [comap_ofValuation]
    exact (ofValuation_eq_of_isEquiv (v.valuation.isEquiv_restrictToIdeal_comap _ _ _ hcx
      hϖC.isUnit hϖC.isTopologicallyNilpotent)).trans (by
        simpa only [← comap_ofValuation, ofValuation_valuation] using hx)
  exact ⟨ofValuation w, (isContinuous_ofValuation_iff w).mpr hw, hwy, hwx⟩

open Huber in
/-- Compatible points over a Tate base lift to the completed tensor product of Huber pairs.
Neither completeness of the inputs nor sheafiness is required. -/
theorem exists_spaPoint_completedTensor (S : Pair B) (T : Pair C)
    (y : spa S.plus) (x : spa T.plus)
    (h : comap (algebraMap A B) y.1 = comap (algebraMap A C) x.1) :
    ∃ z : spa (S.completedTensor A T).plus,
      comap (CompletedTensor.inl A B C) z.1 = y.1 ∧
      comap (CompletedTensor.inr A B C) z.1 = x.1 := by
  let := tensorTopology A B C
  have := isTopologicalRing_tensorTopology A B C
  have := isHuberRing_tensorTopology A B C
  let : UniformSpace (B ⊗[A] C) := IsTopologicalAddGroup.rightUniformSpace _
  have : IsUniformAddGroup (B ⊗[A] C) := isUniformAddGroup_of_addCommGroup
  obtain ⟨v, hy, hx, hcy, hcx, hU⟩ := exists_amalgam_lt_one_mem_nhds A S T y x h
  obtain ⟨w, hwc, hwy, hwx⟩ := exists_isContinuous_amalgam A S T y x v hy hx hcy hcx hU
  -- Extend to the completion; the factor criterion recovers the specified tensor plus ring.
  obtain ⟨z, hzcont, hz⟩ := exists_isContinuous_comap_coeRingHom_eq hwc
  let z' := comap (CompletedTensor.equivCompletion A B C).toRingHom z
  have hz'cont : z'.IsContinuous := hzcont.comap
    (CompletedTensor.isHomeomorph_equivCompletion A B C).continuous
  have hcomp : comap (CompletedTensor.toCompletion A B C) z' = w := by
    have he : (CompletedTensor.equivCompletion A B C).toRingHom.comp
        (CompletedTensor.toCompletion A B C) = Completion.coeRingHom :=
      RingHom.ext (CompletedTensor.equivCompletion_toCompletion A B C)
    simpa only [z', comap_comap, he] using hz
  have hinl : (CompletedTensor.toCompletion A B C).comp includeLeftRingHom =
      CompletedTensor.inl A B C := RingHom.ext fun b ↦ by simp
  have hinr : (CompletedTensor.toCompletion A B C).comp
      (includeRight : C →ₐ[A] B ⊗[A] C).toRingHom =
      CompletedTensor.inr A B C := RingHom.ext fun c ↦ by simp
  have hleft : comap (CompletedTensor.inl A B C) z' = y.1 := by
    rw [← hinl, ← comap_comap, hcomp]
    exact hwy
  have hright : comap (CompletedTensor.inr A B C) z' = x.1 := by
    rw [← hinr, ← comap_comap, hcomp]
    exact hwx
  have hzmem : z' ∈ spa (S.completedTensor A T).plus := by
    rw [Pair.completedTensor.mem_spa_iff S T hz'cont, hleft, hright]
    exact ⟨y.2, x.2⟩
  exact ⟨⟨z', hzmem⟩, hleft, hright⟩

end TauCeti.ValuationSpectrum

namespace TauCeti.Huber

open ValuationSpectrum

universe u

variable {A B C D : Type u} [CommRing A] [CommRing B] [CommRing C] [CommRing D]
  [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C] [TopologicalSpace D]
  [IsTopologicalRing A] [IsTopologicalRing B] [IsTopologicalRing C] [IsTopologicalRing D]
  [IsTateRing A] [IsHuberRing B] [IsHuberRing C] [IsHuberRing D]
  {S : Pair A} {T : Pair B} {U : Pair C} {V : Pair D}
  {f : Pair.Hom S T} {g : Pair.Hom S U} {i : Pair.Hom T V} {j : Pair.Hom U V}

/-- Points of two Huber pairs agreeing over a Tate base lift to any completed pushout.
This is a point-lifting statement, not uniqueness or a point-set pullback isomorphism. -/
theorem exists_spaPoint_of_isCompletedPushout (h : IsCompletedPushout f g i j)
    (x : spa T.plus) (y : spa U.plus) (hxy : f.spaComap x = g.spaComap y) :
    ∃ z : spa V.plus, i.spaComap z = x ∧ j.spaComap z = y := by
  let := f.toRingHom.toAlgebra
  let := g.toRingHom.toAlgebra
  have : IsAdicHom (algebraMap A B) := IsAdicHom.of_isTateRing f.continuous_toRingHom
  have : IsAdicHom (algebraMap A C) := IsAdicHom.of_isTateRing g.continuous_toRingHom
  obtain ⟨z, hzx, hzy⟩ := exists_spaPoint_completedTensor A T U x y (by
    rw [RingHom.algebraMap_toAlgebra, RingHom.algebraMap_toAlgebra]
    simpa only [Pair.Hom.spaComap_val] using congrArg Subtype.val hxy)
  let l := Pair.completedTensor.inl A T U
  let r := Pair.completedTensor.inr A T U
  have hlr : l.comp f = r.comp g := Pair.completedTensor.inl_comp
    (RingHom.algebraMap_toAlgebra _) (RingHom.algebraMap_toAlgebra _)
  let d := h.desc l r hlr
  refine ⟨d.spaComap z, ?_, ?_⟩
  · have hd := congrFun (Pair.Hom.spaComap_comp d i) z
    rw [h.desc_comp_left] at hd
    exact hd.symm.trans (Subtype.ext (by simpa [l] using hzx))
  · have hd := congrFun (Pair.Hom.spaComap_comp d j) z
    rw [h.desc_comp_right] at hd
    exact hd.symm.trans (Subtype.ext (by simpa [r] using hzy))

end TauCeti.Huber
