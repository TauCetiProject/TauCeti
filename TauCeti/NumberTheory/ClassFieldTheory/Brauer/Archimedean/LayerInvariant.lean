/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Brauer.Archimedean.ClassFormation
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic

/-!
# Finite-layer invariants at archimedean places

Inflation from a finite Galois layer over an archimedean completion, followed by its Brauer
invariant, is injective and has image precisely the degree-torsion subgroup of `ℚ/ℤ`.
At a real place the absolute Galois group has order two: the full quadratic layer accounts for
the entire real Brauer group, whereas the trivial layer has zero invariant. At a complex place
every layer is trivial.

These results supply the invariant maps and their range axiom for the archimedean units class
formation on layers whose ground subgroup is the whole absolute Galois group. They use the same
`infiniteInvMap` as the global sum of local invariants.

## References

* E. Artin and J. Tate, *Class Field Theory*, Chapter XIV, §§1–3.
* J.-P. Serre, *Local Fields*, Chapter XIII, §1.

The construction uses `brInfl` and `infiniteInvMap`. The real Galois-group comparison follows
the field-isomorphism transport in `brCongr` and `realBrEquivRelative`.
-/

public noncomputable section

open NumberField NumberField.InfinitePlace

open TauCeti TauCeti.ClassFieldTheory

namespace NumberField.InfinitePlace

/-- The absolute Galois group of a real infinite completion has order two. -/
theorem natCard_absoluteGaloisGroup_of_isReal {K : Type*} [Field K]
    (w : InfinitePlace K) (hw : w.IsReal) :
    Nat.card (AbsoluteGaloisGroup w.Completion) = 2 := by
  let e := Completion.ringEquivRealOfIsReal hw
  let _ : Algebra w.Completion ℝ := e.toRingHom.toAlgebra
  let eA : w.Completion ≃ₐ[w.Completion] ℝ := { e with commutes' := fun _ => rfl }
  let σ : ℝ →ₐ[w.Completion] SeparableClosure w.Completion :=
    (Algebra.ofId w.Completion (SeparableClosure w.Completion)).comp eA.symm.toAlgHom
  have hrange : σ.fieldRange = ⊥ := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact IntermediateField.mem_bot.mpr ⟨e.symm y, rfl⟩
    · intro hx
      obtain ⟨y, rfl⟩ := IntermediateField.mem_bot.mp hx
      exact ⟨e y, congrArg (algebraMap w.Completion (SeparableClosure w.Completion))
        (eA.symm_apply_apply y)⟩
  have htop : σ.fieldRange.fixingSubgroup = ⊤ := by simp [hrange]
  have hcard := Nat.card_congr
    (absoluteGaloisGroupEquivFixingSubgroup w.Completion ℝ σ).toEquiv
  rw [htop, Subgroup.card_top] at hcard
  rw [← hcard]
  let _ : IsAlgClosure ℝ ℂ := ⟨inferInstance, inferInstance⟩
  rw [Nat.card_congr (IsSepClosure.equiv ℝ (SeparableClosure ℝ) ℂ).autCongr.toEquiv,
    IsGalois.card_aut_eq_finrank, Complex.finrank_real_complex]

variable {K : Type} [Field K]

/-- The invariant of a finite Galois layer over an archimedean completion: inflate its class
into the Brauer group and take the normalized archimedean invariant. -/
def infiniteLayerInv (w : InfinitePlace K)
    (V : OpenNormalSubgroup (AbsoluteGaloisGroup w.Completion)) :
    (NormalLayer.ofOpenNormal V).H (unitsFormation w.Completion) 2 →+ AddCircle (1 : ℚ) :=
  (infiniteInvMap w).comp (brInfl V)

/-- The finite-layer invariant is the archimedean invariant of the inflated Brauer class. -/
theorem infiniteLayerInv_apply (w : InfinitePlace K)
    (V : OpenNormalSubgroup (AbsoluteGaloisGroup w.Completion))
    (x : (NormalLayer.ofOpenNormal V).H (unitsFormation w.Completion) 2) :
    infiniteLayerInv w V x = infiniteInvMap w (brInfl V x) :=
  (rfl)

/-- The archimedean finite-layer invariant detects every class. -/
theorem infiniteLayerInv_injective (w : InfinitePlace K)
    (V : OpenNormalSubgroup (AbsoluteGaloisGroup w.Completion)) :
    Function.Injective (infiniteLayerInv w V) :=
  (infiniteInvMap_injective w).comp (brInfl_injective V)

/-- A finite-layer archimedean invariant vanishes exactly when the class vanishes. -/
@[simp]
theorem infiniteLayerInv_eq_zero_iff (w : InfinitePlace K)
    (V : OpenNormalSubgroup (AbsoluteGaloisGroup w.Completion))
    (x : (NormalLayer.ofOpenNormal V).H (unitsFormation w.Completion) 2) :
    infiniteLayerInv w V x = 0 ↔ x = 0 :=
  map_eq_zero_iff _ (infiniteLayerInv_injective w V)

open scoped Classical in
/-- At a real place, the finite-layer invariant is zero on the zero class and `1/2` on every
nonzero class. -/
theorem infiniteLayerInv_apply_of_isReal (w : InfinitePlace K) (hw : w.IsReal)
    (V : OpenNormalSubgroup (AbsoluteGaloisGroup w.Completion))
    (x : (NormalLayer.ofOpenNormal V).H (unitsFormation w.Completion) 2) :
    infiniteLayerInv w V x = if x = 0 then 0 else ((1 / 2 : ℚ) : AddCircle (1 : ℚ)) := by
  classical
  rw [infiniteLayerInv_apply, infiniteInvMap_apply_of_isReal w hw,
    map_eq_zero_iff _ (brInfl_injective V)]

/-- At a complex place every finite-layer archimedean invariant is zero. -/
@[simp]
theorem infiniteLayerInv_apply_of_isComplex (w : InfinitePlace K) (hw : w.IsComplex)
    (V : OpenNormalSubgroup (AbsoluteGaloisGroup w.Completion))
    (x : (NormalLayer.ofOpenNormal V).H (unitsFormation w.Completion) 2) :
    infiniteLayerInv w V x = 0 := by
  rw [infiniteLayerInv_apply, infiniteInvMap_eq_zero_of_isComplex w hw]

/-- The image of a finite-layer archimedean invariant is exactly the degree-torsion subgroup of
`ℚ/ℤ`, including the trivial layers of degree one. -/
@[simp]
theorem range_infiniteLayerInv (w : InfinitePlace K)
    (V : OpenNormalSubgroup (AbsoluteGaloisGroup w.Completion)) :
    Set.range (infiniteLayerInv w V) =
      (AddSubgroup.torsionBy (AddCircle (1 : ℚ)) (NormalLayer.ofOpenNormal V).degree :
        Set (AddCircle (1 : ℚ))) := by
  classical
  rcases w.isReal_or_isComplex with hw | hw
  · have hcard := natCard_absoluteGaloisGroup_of_isReal w hw
    let _ : Fact (Nat.card (AbsoluteGaloisGroup w.Completion)).Prime := ⟨hcard ▸ Nat.prime_two⟩
    rcases V.toSubgroup.eq_bot_or_eq_top_of_prime_card with hV | hV
    · have hdegree : (NormalLayer.ofOpenNormal V).degree = 2 := by
        rw [NormalLayer.degree_eq_natCard_gal,
          Nat.card_congr (NormalLayer.galOfOpenNormalEquiv V).toEquiv,
          hV, Nat.card_congr
            (QuotientGroup.quotientBot (G := AbsoluteGaloisGroup w.Completion)).toEquiv, hcard]
      rw [hdegree, infiniteLayerInv, AddMonoidHom.coe_comp, Set.range_comp,
        (brInfl_surjective_of_toSubgroup_eq_bot hV).range_eq,
        Set.image_univ, range_infiniteInvMap_of_isReal w hw]
      norm_num
    · have hL : (NormalLayer.ofOpenNormal V).top = (NormalLayer.ofOpenNormal V).ground := by
        rw [NormalLayer.top_ofOpenNormal, NormalLayer.ground_ofOpenNormal]
        exact OpenSubgroup.toSubgroup_injective hV
      let _ : Subsingleton (NormalLayer.ofOpenNormal V).Gal :=
        NormalLayer.subsingleton_gal_of_top_eq_ground _ hL
      let _ : Subsingleton ((NormalLayer.ofOpenNormal V).H (unitsFormation w.Completion) 2) :=
        ModuleCat.subsingleton_of_isZero
          (isZero_groupCohomology_succ_of_subsingleton _ 1)
      rw [NormalLayer.degree_eq_one_of_top_eq_ground _ hL]
      have hz : infiniteLayerInv w V = 0 := by
        ext x
        rw [Subsingleton.elim x 0, map_zero, AddMonoidHom.zero_apply]
      rw [hz]
      ext x
      simp [AddSubgroup.torsionBy, eq_comm]
  · let _ : Subsingleton (AbsoluteGaloisGroup w.Completion) :=
      subsingleton_absoluteGaloisGroup_of_isComplex w hw
    rw [NormalLayer.degree_eq_one_of_top_eq_ground _
      (NormalLayer.top_eq_ground_of_subsingleton _)]
    ext x
    simp [AddSubgroup.torsionBy, eq_comm, infiniteLayerInv_apply_of_isComplex w hw]

end NumberField.InfinitePlace
