/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Brauer.Formation
public import TauCeti.NumberTheory.ClassFieldTheory.Brauer.InfinitePlace
public import TauCeti.NumberTheory.ClassFieldTheory.Formation.TrivialLayer
public import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.Congr

/-!
# Class formations at archimedean places

At a real place, the absolute Galois group of the completion has order two. Hence its finite normal
layers are either trivial or the unique quadratic layer. Inflation identifies the second
cohomology of that layer with the real Brauer group, and the normalized invariant takes its
nonzero class to `1/2`. At a complex place, the absolute Galois group is trivial and every
finite normal layer is trivial.

In both cases, the resulting invariant agrees with `infiniteInvMap` after inflation into the
Brauer group. Thus the constructions have the normalization required by the global sum of local
invariants, rather than merely providing abstract class formations on the same coefficient module.

## Main definitions

* `TauCeti.ClassFieldTheory.infiniteClassFormationOfIsReal`: the units class formation at a real
  infinite place.
* `TauCeti.ClassFieldTheory.infiniteClassFormationOfIsComplex`: the units class formation at a
  complex infinite place.
* `TauCeti.ClassFieldTheory.infiniteClassFormation`: the units class formation at any infinite
  place.

## Main results

* `TauCeti.ClassFieldTheory.infiniteClassFormationOfIsReal_inv`: the real-place invariant agrees
  with the archimedean Brauer invariant after inflation.
* `TauCeti.ClassFieldTheory.infiniteClassFormationOfIsComplex_inv`: its invariant agrees with the
  archimedean Brauer invariant after inflation.
* `TauCeti.ClassFieldTheory.infiniteClassFormationOfIsComplex_artinMap`: every finite-layer Artin
  map at a complex place is zero.
* `TauCeti.ClassFieldTheory.finite_absoluteGaloisGroup`: the absolute Galois group of every
  infinite completion is finite.
* `TauCeti.ClassFieldTheory.subsingleton_fieldAbsoluteGaloisGroup_of_isComplex`,
  `TauCeti.ClassFieldTheory.natCard_fieldAbsoluteGaloisGroup_of_isReal`: Mathlib's absolute Galois
  group `Gal(AlgebraicClosure K_w/K_w)` is trivial at a complex place and of order two at a real
  place.
* `TauCeti.ClassFieldTheory.sq_eq_one_fieldAbsoluteGaloisGroupAbelianization_of_isReal`,
  `TauCeti.ClassFieldTheory.eq_of_ne_one_fieldAbsoluteGaloisGroupAbelianization_of_isReal`: at a
  real place every element of `G_{K_w}^ab` squares to `1`, and any two nontrivial elements of it
  are equal.
* `TauCeti.ClassFieldTheory.fieldAbsoluteGaloisGroup_apply_eq_inv_of_isReal`: at a real place the
  nontrivial automorphism of `AlgebraicClosure K_w` inverts every root of unity.

## References

* E. Artin and J. Tate, *Class Field Theory*, Chapter XIV, §§1–4.
* J. S. Milne, *Class Field Theory*, Chapter VIII, §4.
-/

public noncomputable section

open NumberField NumberField.InfinitePlace TauCeti

namespace NumberField.InfinitePlace

variable {K : Type*} [Field K]

private noncomputable def absoluteGaloisGroupEquivReal (w : InfinitePlace K) (hw : w.IsReal) :
    AbsoluteGaloisGroup w.Completion ≃* (ℂ ≃ₐ[ℝ] ℂ) := by
  letI : IsAlgClosure ℝ ℂ := ⟨inferInstance, inferInstance⟩
  let eC := IsSepClosure.equiv ℝ (SeparableClosure ℝ) ℂ
  exact (Completion.ringEquivRealOfIsReal hw).absoluteGaloisGroupCongr.symm.toMulEquiv.trans
    eC.autCongr

/-- The absolute Galois group of a real infinite completion has order two. -/
theorem natCard_absoluteGaloisGroup_of_isReal (w : InfinitePlace K) (hw : w.IsReal) :
    Nat.card (AbsoluteGaloisGroup w.Completion) = 2 := by
  rw [Nat.card_congr (absoluteGaloisGroupEquivReal w hw).toEquiv,
    IsGalois.card_aut_eq_finrank, Complex.finrank_real_complex]

end NumberField.InfinitePlace

namespace TauCeti.ClassFieldTheory

variable {K : Type} [Field K]

/-- Every subgroup of the absolute Galois group of a real infinite completion is either trivial
or the whole group. -/
theorem subgroup_eq_bot_or_eq_top_of_isReal (w : InfinitePlace K) (hw : w.IsReal)
    (U : Subgroup (AbsoluteGaloisGroup w.Completion)) : U = ⊥ ∨ U = ⊤ := by
  let _ : Fact (Nat.card (AbsoluteGaloisGroup w.Completion)).Prime :=
    ⟨by rw [natCard_absoluteGaloisGroup_of_isReal w hw]; exact Nat.prime_two⟩
  exact U.eq_bot_or_eq_top_of_prime_card

/-- The trivial open normal subgroup of the two-element absolute Galois group at a real place. -/
noncomputable def realOpenNormalSubgroup (w : InfinitePlace K) (hw : w.IsReal) :
    OpenNormalSubgroup (AbsoluteGaloisGroup w.Completion) := by
  let _ : Finite (AbsoluteGaloisGroup w.Completion) :=
    Nat.finite_of_card_ne_zero (by rw [natCard_absoluteGaloisGroup_of_isReal w hw]; decide)
  exact openNormalSubgroupBot _

@[simp]
theorem realOpenNormalSubgroup_toSubgroup (w : InfinitePlace K) (hw : w.IsReal) :
    (realOpenNormalSubgroup w hw).toSubgroup = ⊥ := by
  let _ : Finite (AbsoluteGaloisGroup w.Completion) :=
    Nat.finite_of_card_ne_zero (by rw [natCard_absoluteGaloisGroup_of_isReal w hw]; decide)
  exact openNormalSubgroupBot_toSubgroup _

/-- A finite normal layer over a real infinite completion is either trivial or the unique
quadratic layer from the trivial subgroup to the full absolute Galois group. -/
theorem NormalLayer.top_eq_ground_or_eq_realLayer_of_isReal (w : InfinitePlace K) (hw : w.IsReal)
    (L : NormalLayer (AbsoluteGaloisGroup w.Completion)) :
    L.top = L.ground ∨ L = NormalLayer.ofOpenNormal (realOpenNormalSubgroup w hw) := by
  rcases subgroup_eq_bot_or_eq_top_of_isReal w hw L.ground.toSubgroup with hground | hground
  · left
    apply OpenSubgroup.toSubgroup_injective
    exact le_antisymm L.top_le_ground (hground ▸ bot_le)
  · rcases subgroup_eq_bot_or_eq_top_of_isReal w hw L.top.toSubgroup with htop | htop
    · right
      apply NormalLayer.ext
      · apply OpenSubgroup.toSubgroup_injective
        simpa using hground
      · apply OpenSubgroup.toSubgroup_injective
        simpa using htop
    · left
      exact OpenSubgroup.toSubgroup_injective (htop.trans hground.symm)

/-- The unique nontrivial layer at a real place has degree two. -/
theorem degree_realLayer (w : InfinitePlace K) (hw : w.IsReal) :
    (NormalLayer.ofOpenNormal (realOpenNormalSubgroup w hw)).degree = 2 := by
  rw [NormalLayer.degree_eq_relIndex, NormalLayer.top_ofOpenNormal,
    NormalLayer.ground_ofOpenNormal, realOpenNormalSubgroup_toSubgroup,
    OpenSubgroup.toSubgroup_top, Subgroup.relIndex_bot_left,
    Subgroup.card_top,
    natCard_absoluteGaloisGroup_of_isReal w hw]

/-- The invariant of a finite normal layer at a real place. It is zero on a trivial layer; on the
unique quadratic layer it is the archimedean invariant after inflation into the Brauer group. -/
noncomputable def realLayerInv (w : InfinitePlace K) (hw : w.IsReal)
    (L : NormalLayer (AbsoluteGaloisGroup w.Completion)) :
    L.H (unitsFormation w.Completion) 2 →+ AddCircle (1 : ℚ) := by
  classical
  exact if h : L.top = L.ground then 0 else by
      have hL := (L.top_eq_ground_or_eq_realLayer_of_isReal w hw).resolve_left h
      subst L
      exact (infiniteInvMap w).comp (brInfl (realOpenNormalSubgroup w hw))

/-- The invariant of a trivial real-place layer is zero. -/
@[simp]
theorem realLayerInv_of_top_eq_ground (w : InfinitePlace K) (hw : w.IsReal)
    (L : NormalLayer (AbsoluteGaloisGroup w.Completion)) (hL : L.top = L.ground) :
    realLayerInv w hw L = 0 := by
  classical
  simp [realLayerInv, hL]

/-- On the unique quadratic layer, `realLayerInv` is the archimedean Brauer invariant after
inflation. -/
@[simp]
theorem realLayerInv_realLayer (w : InfinitePlace K) (hw : w.IsReal) :
    realLayerInv w hw (NormalLayer.ofOpenNormal (realOpenNormalSubgroup w hw)) =
      (infiniteInvMap w).comp (brInfl (realOpenNormalSubgroup w hw)) := by
  classical
  rw [realLayerInv]
  split_ifs with h
  · have hcontra : (2 : ℕ) = 1 := by
      rw [← degree_realLayer w hw]
      exact (NormalLayer.ofOpenNormal (realOpenNormalSubgroup w hw))
        |>.degree_eq_one_of_top_eq_ground h
    omega
  · rfl

/-- The invariant on every finite normal layer at a real place is injective. -/
theorem realLayerInv_injective (w : InfinitePlace K) (hw : w.IsReal)
    (L : NormalLayer (AbsoluteGaloisGroup w.Completion)) :
    Function.Injective (realLayerInv w hw L) := by
  rcases L.top_eq_ground_or_eq_realLayer_of_isReal w hw with hL | hL
  · let _ := L.subsingleton_H_succ_of_top_eq_ground (unitsFormation w.Completion) hL 1
    exact fun _ _ _ => Subsingleton.elim _ _
  · subst L
    rw [realLayerInv_realLayer]
    exact (infiniteInvMap_injective w).comp
      (brInfl_injective (realOpenNormalSubgroup w hw))

/-- The range of the invariant on a real-place layer is the torsion subgroup of order equal to
the degree of that layer. -/
theorem range_realLayerInv (w : InfinitePlace K) (hw : w.IsReal)
    (L : NormalLayer (AbsoluteGaloisGroup w.Completion)) :
    Set.range (realLayerInv w hw L) =
      (AddSubgroup.torsionBy (AddCircle (1 : ℚ)) L.degree : Set (AddCircle (1 : ℚ))) := by
  rcases L.top_eq_ground_or_eq_realLayer_of_isReal w hw with hL | hL
  · rw [realLayerInv_of_top_eq_ground w hw L hL, L.degree_eq_one_of_top_eq_ground hL]
    ext x
    simp [AddSubgroup.torsionBy, eq_comm]
  · subst L
    rw [realLayerInv_realLayer, AddMonoidHom.coe_comp, Set.range_comp,
      (brInfl_surjective_of_toSubgroup_eq_bot (realOpenNormalSubgroup_toSubgroup w hw)).range_eq,
      Set.image_univ,
      range_infiniteInvMap_of_isReal w hw, degree_realLayer]
    norm_num

/-- Real-place invariants have the class-formation restriction law. -/
theorem realLayerInv_cohomologyRes (w : InfinitePlace K) (hw : w.IsReal)
    {small big : NormalLayer (AbsoluteGaloisGroup w.Completion)}
    (T : LayerRestriction small big) (x : big.H (unitsFormation w.Completion) 2) :
    realLayerInv w hw small (T.cohomologyRes (unitsFormation w.Completion) 2 x) =
      T.relativeDegree • realLayerInv w hw big x := by
  rcases small.top_eq_ground_or_eq_realLayer_of_isReal w hw with hsmall | hsmall
  · rcases big.top_eq_ground_or_eq_realLayer_of_isReal w hw with hbig | hbig
    · let _ := big.subsingleton_H_succ_of_top_eq_ground (unitsFormation w.Completion) hbig 1
      have hx : x = 0 := Subsingleton.elim _ _
      subst x
      simp
    · subst big
      have hrel : T.relativeDegree = 2 := by
        have hdegree := T.degree_mul_relativeDegree
        rw [small.degree_eq_one_of_top_eq_ground hsmall, degree_realLayer] at hdegree
        omega
      rw [realLayerInv_of_top_eq_ground w hw small hsmall, AddMonoidHom.zero_apply,
        hrel]
      have hx : realLayerInv w hw
          (NormalLayer.ofOpenNormal (realOpenNormalSubgroup w hw)) x ∈
          Set.range (realLayerInv w hw
            (NormalLayer.ofOpenNormal (realOpenNormalSubgroup w hw))) := ⟨x, rfl⟩
      rw [range_realLayerInv w hw, degree_realLayer, SetLike.mem_coe,
        AddSubgroup.torsionBy.nsmul_iff] at hx
      exact hx.symm
  · subst small
    have hbig : big = NormalLayer.ofOpenNormal (realOpenNormalSubgroup w hw) := by
      apply NormalLayer.ext
      · apply OpenSubgroup.toSubgroup_injective
        apply le_antisymm
        · simp
        · exact OpenSubgroup.toSubgroup_le.2 T.ground_le
      · exact T.same_top.symm
    subst big
    have hrel : T.relativeDegree = 1 := by
      have hdegree : 2 * T.relativeDegree = 2 := by
        simpa only [degree_realLayer] using T.degree_mul_relativeDegree
      omega
    rw [LayerRestriction.cohomologyRes_self, CategoryTheory.id_apply, hrel, one_nsmul]

/-- Real-place invariants have the class-formation inflation law. -/
theorem realLayerInv_cohomologyInfl (w : InfinitePlace K) (hw : w.IsReal)
    {old new : NormalLayer (AbsoluteGaloisGroup w.Completion)}
    (T : LayerRefinement old new) (x : old.H (unitsFormation w.Completion) 2) :
    realLayerInv w hw new (T.cohomologyInfl (unitsFormation w.Completion) 2 x) =
      realLayerInv w hw old x := by
  rcases old.top_eq_ground_or_eq_realLayer_of_isReal w hw with hold | hold
  · let _ := old.subsingleton_H_succ_of_top_eq_ground (unitsFormation w.Completion) hold 1
    have hx : x = 0 := Subsingleton.elim _ _
    subst x
    simp
  · subst old
    have hnew : new = NormalLayer.ofOpenNormal (realOpenNormalSubgroup w hw) := by
      apply NormalLayer.ext
      · exact T.same_ground.symm
      · apply OpenSubgroup.toSubgroup_injective
        apply le_antisymm
        · exact OpenSubgroup.toSubgroup_le.2 T.top_le
        · simp
    subst new
    rw [LayerRefinement.cohomologyInfl_self, CategoryTheory.id_apply]

open scoped Classical in
/-- The invariant at a real place is zero on zero and `1/2` on every nonzero finite-layer
cohomology class. -/
theorem realLayerInv_apply (w : InfinitePlace K) (hw : w.IsReal)
    (L : NormalLayer (AbsoluteGaloisGroup w.Completion))
    (x : L.H (unitsFormation w.Completion) 2) :
    realLayerInv w hw L x =
      if x = 0 then 0 else ((1 / 2 : ℚ) : AddCircle (1 : ℚ)) := by
  classical
  rcases L.top_eq_ground_or_eq_realLayer_of_isReal w hw with hL | hL
  · have hx : x = 0 :=
      (L.subsingleton_H_succ_of_top_eq_ground (unitsFormation w.Completion) hL 1).elim _ _
    subst x
    simp
  · subst L
    rw [realLayerInv_realLayer, AddMonoidHom.comp_apply,
      infiniteInvMap_apply_of_isReal w hw]
    rw [_root_.map_eq_zero_iff _ (brInfl_injective (realOpenNormalSubgroup w hw))]

/-- Real-place invariants are unchanged by conjugating a finite normal layer. -/
theorem realLayerInv_conjugateCohomologyIso (w : InfinitePlace K) (hw : w.IsReal)
    (L : NormalLayer (AbsoluteGaloisGroup w.Completion))
    (g : AbsoluteGaloisGroup w.Completion) (x : L.H (unitsFormation w.Completion) 2) :
    realLayerInv w hw (L.conjugate g)
        ((L.conjugateCohomologyIso (unitsFormation w.Completion) g 2).hom x) =
      realLayerInv w hw L x := by
  classical
  rw [realLayerInv_apply, realLayerInv_apply]
  have hinj : Function.Injective
      (L.conjugateCohomologyIso (unitsFormation w.Completion) g 2).hom := by
    intro a b hab
    simpa using congrArg
      (L.conjugateCohomologyIso (unitsFormation w.Completion) g 2).inv hab
  rw [_root_.map_eq_zero_iff _ hinj]

/-- **The class formation at a real place.** Its invariant on the unique nontrivial layer is the
archimedean Brauer invariant after inflation, and it is zero on every trivial layer. -/
noncomputable def infiniteClassFormationOfIsReal (w : InfinitePlace K) (hw : w.IsReal) :
    ClassFormation (unitsFormation w.Completion) where
  subsingleton_h1 := subsingleton_h1_unitsFormation
  inv := realLayerInv w hw
  inv_injective := realLayerInv_injective w hw
  range_inv := range_realLayerInv w hw
  inv_restrict := realLayerInv_cohomologyRes w hw
  inv_infl := realLayerInv_cohomologyInfl w hw
  inv_conj := realLayerInv_conjugateCohomologyIso w hw

/-- The invariant of the real-place class formation is `realLayerInv`. -/
@[simp]
theorem infiniteClassFormationOfIsReal_inv_apply (w : InfinitePlace K) (hw : w.IsReal)
    (L : NormalLayer (AbsoluteGaloisGroup w.Completion))
    (x : L.H (unitsFormation w.Completion) 2) :
    (infiniteClassFormationOfIsReal w hw).inv L x = realLayerInv w hw L x := by
  unfold infiniteClassFormationOfIsReal
  rfl

/-- The invariant of the real-place class formation is the normalized archimedean Brauer
invariant of the inflated class. -/
theorem infiniteClassFormationOfIsReal_inv (w : InfinitePlace K) (hw : w.IsReal)
    (V : OpenNormalSubgroup (AbsoluteGaloisGroup w.Completion))
    (x : (NormalLayer.ofOpenNormal V).H (unitsFormation w.Completion) 2) :
    (infiniteClassFormationOfIsReal w hw).inv (NormalLayer.ofOpenNormal V) x =
      infiniteInvMap w (brInfl V x) := by
  rcases subgroup_eq_bot_or_eq_top_of_isReal w hw V.toSubgroup with hV | hV
  · have hV' : V = realOpenNormalSubgroup w hw := by
      apply OpenNormalSubgroup.toSubgroup_injective
      simpa using hV
    subst V
    rw [infiniteClassFormationOfIsReal_inv_apply, realLayerInv_realLayer,
      AddMonoidHom.comp_apply]
  · have htrivial : (NormalLayer.ofOpenNormal V).top =
        (NormalLayer.ofOpenNormal V).ground := by
      apply OpenSubgroup.toSubgroup_injective
      simpa using hV
    let _ := (NormalLayer.ofOpenNormal V).subsingleton_H_succ_of_top_eq_ground
      (unitsFormation w.Completion) htrivial 1
    have hx : x = 0 := Subsingleton.elim _ _
    subst x
    simp

/-- The absolute Galois group of a complex infinite completion is trivial. -/
theorem subsingleton_absoluteGaloisGroup_of_isComplex (w : InfinitePlace K) (hw : w.IsComplex) :
    Subsingleton (AbsoluteGaloisGroup w.Completion) := by
  let _ : IsAlgClosed w.Completion :=
    IsAlgClosed.of_ringEquiv ℂ w.Completion
      (Completion.ringEquivComplexOfIsComplex hw).symm
  infer_instance

/-- The absolute Galois group of an infinite completion is finite: it has order two at a real
place and is trivial at a complex place. -/
instance finite_absoluteGaloisGroup (w : InfinitePlace K) :
    Finite (AbsoluteGaloisGroup w.Completion) := by
  rcases w.isReal_or_isComplex with hw | hw
  · exact Nat.finite_of_card_ne_zero (by rw [natCard_absoluteGaloisGroup_of_isReal w hw]; decide)
  · let _ := subsingleton_absoluteGaloisGroup_of_isComplex w hw
    infer_instance

/-- **The class formation at a complex place.** The absolute Galois group of the completion is
trivial, so the units formation carries the canonical class formation with zero invariant maps. -/
def infiniteClassFormationOfIsComplex (w : InfinitePlace K) (hw : w.IsComplex) :
    ClassFormation (unitsFormation w.Completion) := by
  let _ : Subsingleton (AbsoluteGaloisGroup w.Completion) :=
    subsingleton_absoluteGaloisGroup_of_isComplex w hw
  exact ClassFormation.ofSubsingleton (unitsFormation w.Completion)

/-- The invariant of the complex-place class formation is zero on every layer. -/
@[simp]
theorem infiniteClassFormationOfIsComplex_inv_apply (w : InfinitePlace K) (hw : w.IsComplex)
    (L : NormalLayer (AbsoluteGaloisGroup w.Completion))
    (x : L.H (unitsFormation w.Completion) 2) :
    (infiniteClassFormationOfIsComplex w hw).inv L x = 0 := by
  let _ : Subsingleton (AbsoluteGaloisGroup w.Completion) :=
    subsingleton_absoluteGaloisGroup_of_isComplex w hw
  exact ClassFormation.ofSubsingleton_inv_apply (unitsFormation w.Completion) L x

/-- The invariant of the complex-place class formation is the archimedean Brauer invariant of the
inflated class. This is the complex-place specialization of the normalization required of
`infiniteClassFormation`. -/
theorem infiniteClassFormationOfIsComplex_inv (w : InfinitePlace K) (hw : w.IsComplex)
    (V : OpenNormalSubgroup (AbsoluteGaloisGroup w.Completion))
    (x : (NormalLayer.ofOpenNormal V).H (unitsFormation w.Completion) 2) :
    (infiniteClassFormationOfIsComplex w hw).inv (NormalLayer.ofOpenNormal V) x =
      infiniteInvMap w (brInfl V x) := by
  rw [infiniteClassFormationOfIsComplex_inv_apply,
    infiniteInvMap_eq_zero_of_isComplex w hw]

/-- Every finite-layer Artin map of the complex-place class formation is zero. -/
@[simp]
theorem infiniteClassFormationOfIsComplex_artinMap (w : InfinitePlace K) (hw : w.IsComplex)
    (L : NormalLayer (AbsoluteGaloisGroup w.Completion)) :
    (infiniteClassFormationOfIsComplex w hw).artinMap L = 0 := by
  let _ : Subsingleton (AbsoluteGaloisGroup w.Completion) :=
    subsingleton_absoluteGaloisGroup_of_isComplex w hw
  exact (infiniteClassFormationOfIsComplex w hw).artinMap_trivialLayer L
    L.top_eq_ground_of_subsingleton

/-- **The class formation at an infinite place.** This selects the real or complex construction
according to the type of the place. -/
noncomputable def infiniteClassFormation (w : InfinitePlace K) :
    ClassFormation (unitsFormation w.Completion) := by
  classical
  exact if hw : w.IsReal then infiniteClassFormationOfIsReal w hw
    else infiniteClassFormationOfIsComplex w (not_isReal_iff_isComplex.mp hw)

/-- At a real place, `infiniteClassFormation` is the real-place construction. -/
@[simp]
theorem infiniteClassFormation_of_isReal (w : InfinitePlace K) (hw : w.IsReal) :
    infiniteClassFormation w = infiniteClassFormationOfIsReal w hw := by
  simp [infiniteClassFormation, hw]

/-- At a complex place, `infiniteClassFormation` is the complex-place construction. -/
@[simp]
theorem infiniteClassFormation_of_isComplex (w : InfinitePlace K) (hw : w.IsComplex) :
    infiniteClassFormation w = infiniteClassFormationOfIsComplex w hw := by
  simp [infiniteClassFormation, not_isReal_iff_isComplex.mpr hw]

/-- The invariant of the archimedean class formation is the archimedean Brauer invariant after
inflation, at both real and complex places. -/
theorem infiniteClassFormation_inv (w : InfinitePlace K)
    (V : OpenNormalSubgroup (AbsoluteGaloisGroup w.Completion))
    (x : (NormalLayer.ofOpenNormal V).H (unitsFormation w.Completion) 2) :
    (infiniteClassFormation w).inv (NormalLayer.ofOpenNormal V) x =
      infiniteInvMap w (brInfl V x) := by
  rcases w.isReal_or_isComplex with hw | hw
  · rw [infiniteClassFormation_of_isReal w hw]
    exact infiniteClassFormationOfIsReal_inv w hw V x
  · rw [infiniteClassFormation_of_isComplex w hw]
    exact infiniteClassFormationOfIsComplex_inv w hw V x

/-! ### Mathlib's absolute Galois group at an infinite place -/

/-- At a complex place `Gal(AlgebraicClosure K_w/K_w)` is trivial. -/
theorem subsingleton_fieldAbsoluteGaloisGroup_of_isComplex (w : InfinitePlace K)
    (hw : w.IsComplex) : Subsingleton (Field.absoluteGaloisGroup w.Completion) :=
  have := subsingleton_absoluteGaloisGroup_of_isComplex w hw
  (absoluteGaloisGroupRestrictEquiv w.Completion).toEquiv.subsingleton

section Real

variable (w : InfinitePlace K) (hw : w.IsReal)
include hw

/-- At a real place `Gal(AlgebraicClosure K_w/K_w)` has order two. -/
theorem natCard_fieldAbsoluteGaloisGroup_of_isReal :
    Nat.card (Field.absoluteGaloisGroup w.Completion) = 2 := by
  rw [Nat.card_congr (absoluteGaloisGroupRestrictEquiv w.Completion).toEquiv,
    natCard_absoluteGaloisGroup_of_isReal w hw]

/-- At a real place an automorphism of `AlgebraicClosure K_w` with trivial class in `G_{K_w}^ab` is
the identity: `G_{K_w}` has order two, so its closed commutator subgroup is trivial. -/
theorem eq_one_of_mk_eq_one_of_isReal {σ : Field.absoluteGaloisGroup w.Completion}
    (hσ : (σ : Field.absoluteGaloisGroupAbelianization w.Completion) = 1) : σ = 1 := by
  have : Fact (Nat.card (Field.absoluteGaloisGroup w.Completion)).Prime :=
    ⟨natCard_fieldAbsoluteGaloisGroup_of_isReal w hw ▸ Nat.prime_two⟩
  have : IsCyclic (Field.absoluteGaloisGroup w.Completion) := isCyclic_of_prime_card rfl
  have hclosure :
      (commutator (Field.absoluteGaloisGroup w.Completion)).topologicalClosure = ⊥ := by
    rw [commutator_eq_bot]
    exact le_bot_iff.mp (Subgroup.topologicalClosure_minimal _ le_rfl isClosed_singleton)
  have hmem := (QuotientGroup.eq_one_iff σ).mp hσ
  rwa [hclosure, Subgroup.mem_bot] at hmem

/-- At a real place every element of `G_{K_w}^ab` squares to `1`, since `G_{K_w}` has order two. -/
theorem sq_eq_one_fieldAbsoluteGaloisGroupAbelianization_of_isReal
    (y : Field.absoluteGaloisGroupAbelianization w.Completion) : y ^ 2 = 1 := by
  obtain ⟨σ, rfl⟩ := QuotientGroup.mk_surjective y
  rw [← QuotientGroup.mk_pow, ← natCard_fieldAbsoluteGaloisGroup_of_isReal w hw,
    pow_card_eq_one', QuotientGroup.mk_one]

/-- At a real place any two nontrivial elements of `G_{K_w}^ab` are equal, since `G_{K_w}` has
order two. -/
theorem eq_of_ne_one_fieldAbsoluteGaloisGroupAbelianization_of_isReal
    {a b : Field.absoluteGaloisGroupAbelianization w.Completion} (ha : a ≠ 1) (hb : b ≠ 1) :
    a = b := by
  obtain ⟨σ, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨τ, rfl⟩ := QuotientGroup.mk_surjective b
  have hσ : σ ≠ 1 := by
    rintro rfl
    exact ha (QuotientGroup.mk_one _)
  have hτ : τ ≠ 1 := by
    rintro rfl
    exact hb (QuotientGroup.mk_one _)
  rw [((Nat.card_eq_two_iff' 1).mp (natCard_fieldAbsoluteGaloisGroup_of_isReal w hw)).unique hσ hτ]

/-- At a real place an element of `AlgebraicClosure K_w` fixed by a nontrivial automorphism lies in
`K_w`: that automorphism and the identity are all of `G_{K_w}`, which has order two. -/
theorem mem_range_algebraMap_of_fieldAbsoluteGaloisGroup_apply_eq_of_isReal
    {σ : Gal(AlgebraicClosure w.Completion/w.Completion)} (hσ : σ ≠ 1)
    {y : AlgebraicClosure w.Completion} (hy : σ y = y) :
    y ∈ Set.range (algebraMap w.Completion (AlgebraicClosure w.Completion)) := by
  have := (Completion.extensionEmbedding w).charZero
  refine IntermediateField.mem_bot.mp ((InfiniteGalois.mem_bot_iff_fixed y).mpr fun τ ↦ ?_)
  by_cases hτ : τ = 1
  · rw [hτ, AlgEquiv.one_apply]
  · -- `Field.absoluteGaloisGroup w.Completion` is by definition
    -- `Gal(AlgebraicClosure w.Completion/w.Completion)`.
    rwa [((Nat.card_eq_two_iff' 1).mp (natCard_fieldAbsoluteGaloisGroup_of_isReal w hw)).unique
      hτ hσ]

/-- At a real place a nontrivial automorphism of `AlgebraicClosure K_w` inverts every root of
unity: writing `z = a + b i` with `a, b ∈ K_w`, the product `z σ(z) = a² + b²` is a nonnegative root
of unity in `K_w ≅ ℝ`, hence `1`. -/
theorem fieldAbsoluteGaloisGroup_apply_eq_inv_of_isReal
    {σ : Gal(AlgebraicClosure w.Completion/w.Completion)} (hσ : σ ≠ 1) {m : ℕ} (hm : m ≠ 0)
    {z : AlgebraicClosure w.Completion} (hz : z ^ m = 1) : σ z = z⁻¹ := by
  let ι := algebraMap w.Completion (AlgebraicClosure w.Completion)
  have := (Completion.extensionEmbedding w).charZero
  -- `Field.absoluteGaloisGroup w.Completion` is by definition
  -- `Gal(AlgebraicClosure w.Completion/w.Completion)`, so the latter has order two.
  have hcard : Nat.card Gal(AlgebraicClosure w.Completion/w.Completion) = 2 :=
    natCard_fieldAbsoluteGaloisGroup_of_isReal w hw
  have hσσ (y : AlgebraicClosure w.Completion) : σ (σ y) = y := by
    rw [← AlgEquiv.mul_apply, ← sq, ← hcard, pow_card_eq_one', AlgEquiv.one_apply]
  -- `K_w ≅ ℝ` has no square root of `-1`, but its algebraic closure has one, `i`, with `σ i = -i`.
  have hnsq (c : w.Completion) : c ^ 2 ≠ -1 := fun hc ↦ by
    have h := congrArg (Completion.extensionEmbeddingOfIsReal hw) hc
    rw [map_pow, map_neg, map_one] at h
    nlinarith [sq_nonneg (Completion.extensionEmbeddingOfIsReal hw c)]
  obtain ⟨i, hi⟩ := IsAlgClosed.exists_pow_nat_eq (-1 : AlgebraicClosure w.Completion) two_pos
  have hσi : σ i = -i := by
    have h2 : σ i ^ 2 = i ^ 2 := by rw [← map_pow, hi, map_neg, map_one]
    refine (sq_eq_sq_iff_eq_or_eq_neg.mp h2).resolve_left fun h ↦ ?_
    obtain ⟨c, hc⟩ := mem_range_algebraMap_of_fieldAbsoluteGaloisGroup_apply_eq_of_isReal w hw hσ h
    exact hnsq c (ι.injective (by rw [map_pow, hc, hi, map_neg, map_one]))
  have hi0 : i ≠ 0 := by
    rintro rfl
    norm_num at hi
  -- The real and imaginary parts of `z` are fixed by `σ`, so they lie in `K_w`.
  obtain ⟨a, ha⟩ := mem_range_algebraMap_of_fieldAbsoluteGaloisGroup_apply_eq_of_isReal w hw hσ
    (y := (z + σ z) / 2) (by
    rw [map_div₀, map_add, hσσ, map_ofNat, add_comm])
  obtain ⟨b, hb⟩ := mem_range_algebraMap_of_fieldAbsoluteGaloisGroup_apply_eq_of_isReal w hw hσ
    (y := (z - σ z) / (2 * i)) (by
    rw [map_div₀, map_sub, map_mul, hσσ, map_ofNat, hσi, mul_neg, div_neg, ← neg_div, neg_sub])
  have hzz : z * σ z = ι (a ^ 2 + b ^ 2) := by
    rw [map_add, map_pow, map_pow, ha, hb, div_pow, div_pow, mul_pow, hi]
    ring
  -- `a² + b²` is a nonnegative root of unity in `K_w`, hence `1`.
  have hpow : (a ^ 2 + b ^ 2) ^ m = 1 := ι.injective <| by
    rw [map_pow, ← hzz, mul_pow, ← map_pow, hz, map_one, one_mul, map_one]
  have hone : Completion.extensionEmbeddingOfIsReal hw (a ^ 2 + b ^ 2) = 1 :=
    (pow_eq_one_iff_of_nonneg (by simp only [map_add, map_pow]; positivity) hm).mp
      (by rw [← map_pow, hpow, map_one])
  have h1 : a ^ 2 + b ^ 2 = 1 :=
    (Completion.extensionEmbeddingOfIsReal hw).injective (hone.trans (map_one _).symm)
  rw [h1, map_one] at hzz
  exact eq_inv_of_mul_eq_one_right hzz

end Real

end TauCeti.ClassFieldTheory
