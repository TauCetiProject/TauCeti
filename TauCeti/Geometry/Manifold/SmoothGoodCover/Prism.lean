/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.SmoothGoodCover
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import TauCeti.Topology.LocallyFinite.Basic

/-!
# Smooth good covers of products and of prisms `M × [a, b]`

The product of two smooth good covers is a smooth good cover of the product manifold
(`TauCeti.SmoothGoodCover.prod`): its members are the products `U × V` of members, a finite
intersection of products is the product of the finite intersections of the factors
(`TauCeti.SmoothGoodCover.coe_inf_prod_openSet`), and the contractions of the two factors run
simultaneously.

A locally finite cover of a segment `[a, b]` by relatively open order-connected sets, that is, by
relatively open intervals possibly containing an endpoint, is a smooth good cover of `[a, b]` with
its boundary model `𝓡∂ 1` (`TauCeti.SmoothGoodCover.ofOrdConnected`). Finite intersections of
intervals are intervals, and each nonempty one is contracted to a chosen point `c` by the affine
homotopy `(t, x) ↦ c + τ(t) (x - c)` reparametrized by `τ = Real.smoothTransition`, which stays
inside the interval.

Together, for a smooth good cover `C` of a manifold `M` and an interval cover
`J = SmoothGoodCover.ofOrdConnected ...` of `[0, 1]`, the product `C.prod J` is a smooth good cover
of the prism `M × [0, 1]` with its model `I.prod (𝓡∂ 1)`. Its
nonempty finite intersections are products `U × J` of a nonempty finite intersection `U` of `C`
with an interval `J`, which may contain an endpoint of `[0, 1]`. They are smoothly contractible
in this boundary model, but need not be diffeomorphic to a model space. Such covers carry the
local exactness of forms on a prism used to compare Čech–de Rham data on `M × [0, 1]` (see
`TauCeti.SmoothGoodCover.mextDeriv_homotopyOperator_add_homotopyOperator_mextDeriv`).

The requirement that the members of an interval cover be intervals is what makes it good: with
`J₁ = [0, 2/3)` and `J₂' = (1/3, 1/2) ∪ (1/2, 1]` the intersection `J₁ ∩ J₂'` is disconnected.

## Main definitions and results

* `TauCeti.SmoothGoodCover.prod`: the product of two smooth good covers.
* `TauCeti.SmoothGoodCover.coe_inf_prod_openSet`: a finite intersection of members of a product
  cover is the product of the finite intersections of the factors.
* `TauCeti.SmoothGoodCover.ofOrdConnected`: the smooth good cover of `[a, b]` given by a locally
  finite cover by relatively open order-connected sets.

## References

* R. Bott, L. W. Tu, *Differential Forms in Algebraic Topology*, Springer GTM 82 (1982), §5.
-/

public section

noncomputable section

open Set TopologicalSpace
open scoped ContDiff Manifold

namespace TauCeti

namespace SmoothGoodCover

/-! ### Products of smooth good covers -/

section Prod

universe u v

variable {E H E' H' : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  {N : Type v} [TopologicalSpace N] [ChartedSpace H' N]
  (C : SmoothGoodCover I (M := M)) (D : SmoothGoodCover I' (M := N))

/-- The product family of open sets `(i, j) ↦ C.openSet i ×ˢ D.openSet j`. -/
private def prodOpenSet (p : C.Index × D.Index) : Opens (M × N) :=
  ⟨(C.openSet p.1 : Set M) ×ˢ (D.openSet p.2 : Set N), (C.openSet p.1).isOpen.prod
    (D.openSet p.2).isOpen⟩

/-- A finite intersection of products is the product of the finite intersections of the
components. -/
private theorem coe_inf_prodOpenSet (s : Finset (C.Index × D.Index)) :
    ((s.inf (prodOpenSet C D) : Opens (M × N)) : Set (M × N)) =
      ((s.inf fun p ↦ C.openSet p.1 : Opens M) : Set M) ×ˢ
        ((s.inf fun p ↦ D.openSet p.2 : Opens N) : Set N) := by
  ext x
  simp only [Opens.coe_finset_inf, Finset.inf_set_eq_iInter, mem_prod, mem_iInter]
  exact ⟨fun h ↦ ⟨fun p hp ↦ (h p hp).1, fun p hp ↦ (h p hp).2⟩,
    fun h p hp ↦ ⟨h.1 p hp, h.2 p hp⟩⟩

/-- A point lies in a finite intersection of products exactly when its components lie in the
finite intersections over the two projections of the index set. -/
private theorem mem_inf_prodOpenSet [DecidableEq C.Index] [DecidableEq D.Index]
    {s : Finset (C.Index × D.Index)} {x : M × N} :
    x ∈ s.inf (prodOpenSet C D) ↔
      x.1 ∈ (s.image Prod.fst).inf C.openSet ∧ x.2 ∈ (s.image Prod.snd).inf D.openSet := by
  rw [← SetLike.mem_coe, coe_inf_prodOpenSet, Finset.inf_image, Finset.inf_image]
  simp only [mem_prod, SetLike.mem_coe, Function.comp_def]

variable {C D}

open Classical in
/-- The first component of a point of a finite intersection of products. -/
private def infFst {s : Finset (C.Index × D.Index)} (x : ↥(s.inf (prodOpenSet C D))) :
    ↥((s.image Prod.fst).inf C.openSet) :=
  ⟨x.val.1, ((mem_inf_prodOpenSet C D).1 x.property).1⟩

open Classical in
/-- The second component of a point of a finite intersection of products. -/
private def infSnd {s : Finset (C.Index × D.Index)} (x : ↥(s.inf (prodOpenSet C D))) :
    ↥((s.image Prod.snd).inf D.openSet) :=
  ⟨x.val.2, ((mem_inf_prodOpenSet C D).1 x.property).2⟩

private theorem contMDiff_infFst {s : Finset (C.Index × D.Index)} :
    ContMDiff (I.prod I') I ∞ (infFst (s := s)) :=
  (ContMDiff.subtypeVal_comp_iff _ infFst).1 (contMDiff_fst.comp contMDiff_subtypeVal)

private theorem contMDiff_infSnd {s : Finset (C.Index × D.Index)} :
    ContMDiff (I.prod I') I' ∞ (infSnd (s := s)) :=
  (ContMDiff.subtypeVal_comp_iff _ infSnd).1 (contMDiff_snd.comp contMDiff_subtypeVal)

open Classical in
/-- The finite intersection of `C` over the first projection of a nonempty finite intersection of
products is nonempty. -/
private theorem nonempty_inf_fst {s : Finset (C.Index × D.Index)}
    (hW : ((s.inf (prodOpenSet C D) : Opens (M × N)) : Set (M × N)).Nonempty) :
    (((s.image Prod.fst).inf C.openSet : Opens M) : Set M).Nonempty :=
  ⟨_, ((mem_inf_prodOpenSet C D).1 hW.some_mem).1⟩

open Classical in
/-- The finite intersection of `D` over the second projection of a nonempty finite intersection of
products is nonempty. -/
private theorem nonempty_inf_snd {s : Finset (C.Index × D.Index)}
    (hW : ((s.inf (prodOpenSet C D) : Opens (M × N)) : Set (M × N)).Nonempty) :
    (((s.image Prod.snd).inf D.openSet : Opens N) : Set N).Nonempty :=
  ⟨_, ((mem_inf_prodOpenSet C D).1 hW.some_mem).2⟩

variable (C D)

open Classical in
/-- The **product of two smooth good covers**: the members of the product cover of `M × N` are the
products `C.openSet i ×ˢ D.openSet j`, indexed by `C.Index × D.Index`
(`SmoothGoodCover.prodIndexEquiv`). A nonempty finite intersection of members is the product of
nonempty finite intersections of `C` and of `D` (`SmoothGoodCover.coe_inf_prod_openSet`); its
center is the pair of centers, and it contracts by running the two contractions simultaneously. -/
def prod : SmoothGoodCover (I.prod I') (M := M × N) where
  Index := C.Index × D.Index
  openSet := prodOpenSet C D
  covers x :=
    let ⟨i, hi⟩ := C.covers x.1
    let ⟨j, hj⟩ := D.covers x.2
    ⟨(i, j), hi, hj⟩
  locallyFinite :=
    (C.locallyFinite.preimage_continuous continuous_fst).inter
      (D.locallyFinite.preimage_continuous continuous_snd)
  center s hs hW :=
    ⟨(C.center _ (hs.image _) (nonempty_inf_fst hW), D.center _ (hs.image _) (nonempty_inf_snd hW)),
      (mem_inf_prodOpenSet C D).2 ⟨Subtype.prop _, Subtype.prop _⟩⟩
  contract s hs hW p :=
    ⟨(C.contract _ (hs.image _) (nonempty_inf_fst hW) (p.1, infFst p.2),
      D.contract _ (hs.image _) (nonempty_inf_snd hW) (p.1, infSnd p.2)),
      (mem_inf_prodOpenSet C D).2 ⟨Subtype.prop _, Subtype.prop _⟩⟩
  smooth s hs hW := (ContMDiff.subtypeVal_comp_iff _ _).1 <|
    (contMDiff_subtypeVal.comp ((C.smooth _ _ _).comp
      (contMDiff_fst.prodMk (contMDiff_infFst.comp contMDiff_snd)))).prodMk
    (contMDiff_subtypeVal.comp ((D.smooth _ _ _).comp
      (contMDiff_fst.prodMk (contMDiff_infSnd.comp contMDiff_snd))))
  at_zero s hs hW x := by ext <;> simp
  at_one s hs hW x := by ext <;> simp [infFst, infSnd]
  fixes_center s hs hW t := by
    ext
    · exact congrArg Subtype.val (C.fixes_center _ _ _ t)
    · exact congrArg Subtype.val (D.fixes_center _ _ _ t)

/-- Identification of the index type of `SmoothGoodCover.prod` with `C.Index × D.Index`. -/
def prodIndexEquiv : (C.prod D).Index ≃ C.Index × D.Index :=
  Equiv.refl _

/-- The members of a product cover are the products of members. -/
@[simp]
theorem coe_prod_openSet (p : (C.prod D).Index) :
    ((C.prod D).openSet p : Set (M × N)) =
      (C.openSet (C.prodIndexEquiv D p).1 : Set M) ×ˢ
        (D.openSet (C.prodIndexEquiv D p).2 : Set N) :=
  (rfl)

/-- A finite intersection of members of a product cover is the product of the finite
intersections of the corresponding members of the two factors. -/
theorem coe_inf_prod_openSet (s : Finset (C.prod D).Index) :
    ((s.inf (C.prod D).openSet : Opens (M × N)) : Set (M × N)) =
      ((s.inf fun p ↦ C.openSet (C.prodIndexEquiv D p).1 : Opens M) : Set M) ×ˢ
        ((s.inf fun p ↦ D.openSet (C.prodIndexEquiv D p).2 : Opens N) : Set N) :=
  coe_inf_prodOpenSet C D s

/-- A point lies in a finite intersection of members of a product cover exactly when its
components lie in the finite intersections of the corresponding members of the two factors. -/
theorem mem_inf_prod_openSet [DecidableEq C.Index] [DecidableEq D.Index]
    {s : Finset (C.prod D).Index} {x : M × N} :
    x ∈ s.inf (C.prod D).openSet ↔
      x.1 ∈ (s.image fun p ↦ (C.prodIndexEquiv D p).1).inf C.openSet ∧
        x.2 ∈ (s.image fun p ↦ (C.prodIndexEquiv D p).2).inf D.openSet :=
  mem_inf_prodOpenSet C D

/-- The center of a finite intersection of members of a product cover is the pair of centers of
the corresponding finite intersections of the factors. -/
@[simp]
theorem coe_prod_center [DecidableEq C.Index] [DecidableEq D.Index]
    (s : Finset (C.prod D).Index) (hs : s.Nonempty)
    (hW : ((s.inf (C.prod D).openSet : Opens (M × N)) : Set (M × N)).Nonempty) :
    ((C.prod D).center s hs hW : M × N) =
      ((C.center _ (hs.image _) ⟨_, ((C.mem_inf_prod_openSet D).1 hW.some_mem).1⟩ : M),
        (D.center _ (hs.image _) ⟨_, ((C.mem_inf_prod_openSet D).1 hW.some_mem).2⟩ : N)) := by
  rcases Subsingleton.elim ‹DecidableEq C.Index› (Classical.decEq C.Index) with rfl
  rcases Subsingleton.elim ‹DecidableEq D.Index› (Classical.decEq D.Index) with rfl
  rfl

/-- The contraction of a finite intersection of members of a product cover runs the contractions
of the corresponding finite intersections of the two factors simultaneously. -/
@[simp]
theorem coe_prod_contract [DecidableEq C.Index] [DecidableEq D.Index]
    (s : Finset (C.prod D).Index) (hs : s.Nonempty)
    (hW : ((s.inf (C.prod D).openSet : Opens (M × N)) : Set (M × N)).Nonempty)
    (p : ℝ × ↥(s.inf (C.prod D).openSet)) :
    ((C.prod D).contract s hs hW p : M × N) =
      ((C.contract _ (hs.image _) ⟨_, ((C.mem_inf_prod_openSet D).1 hW.some_mem).1⟩
          (p.1, ⟨_, ((C.mem_inf_prod_openSet D).1 p.2.property).1⟩) : M),
        (D.contract _ (hs.image _) ⟨_, ((C.mem_inf_prod_openSet D).1 hW.some_mem).2⟩
          (p.1, ⟨_, ((C.mem_inf_prod_openSet D).1 p.2.property).2⟩) : N)) := by
  rcases Subsingleton.elim ‹DecidableEq C.Index› (Classical.decEq C.Index) with rfl
  rcases Subsingleton.elim ‹DecidableEq D.Index› (Classical.decEq D.Index) with rfl
  rfl

/-- The cylinder contraction of a finite intersection of members of a product cover runs the
cylinder contractions of the corresponding finite intersections of the two factors
simultaneously. -/
@[simp]
theorem coe_cylinderContract_prod [DecidableEq C.Index] [DecidableEq D.Index]
    (s : Finset (C.prod D).Index) (hs : s.Nonempty)
    (hW : ((s.inf (C.prod D).openSet : Opens (M × N)) : Set (M × N)).Nonempty)
    (p : ↥(s.inf (C.prod D).openSet) × Icc (0 : ℝ) 1) :
    ((C.prod D).cylinderContract s hs hW p : M × N) =
      ((C.cylinderContract _ (hs.image _) ⟨_, ((C.mem_inf_prod_openSet D).1 hW.some_mem).1⟩
          (⟨_, ((C.mem_inf_prod_openSet D).1 p.1.property).1⟩, p.2) : M),
        (D.cylinderContract _ (hs.image _) ⟨_, ((C.mem_inf_prod_openSet D).1 hW.some_mem).2⟩
          (⟨_, ((C.mem_inf_prod_openSet D).1 p.1.property).2⟩, p.2) : N)) := by
  rw [cylinderContract_apply, coe_prod_contract]
  exact Prod.ext (congrArg Subtype.val (C.cylinderContract_apply _ _ _ (_, p.2)).symm)
    (congrArg Subtype.val (D.cylinderContract_apply _ _ _ (_, p.2)).symm)

end Prod

/-! ### Interval covers of a segment -/

section Interval

variable {a b : ℝ} [Fact (a < b)]

omit [Fact (a < b)] in
/-- The affine contraction `c + τ(t) (x - c)` of a segment to `c`, reparametrized in time by
`τ = Real.smoothTransition`, stays in the segment. -/
private theorem add_smoothTransition_mul_sub_mem_Icc (c x : Icc a b) (t : ℝ) :
    (c : ℝ) + Real.smoothTransition t * (x - c) ∈ Icc a b := by
  simpa only [smul_eq_mul] using (convex_Icc a b).add_smul_sub_mem c.property x.property
    ⟨Real.smoothTransition.nonneg t, Real.smoothTransition.le_one t⟩

omit [Fact (a < b)] in
/-- The affine contraction of a segment to `c` stays inside every order-connected set containing
`c` and the moving point. -/
private theorem add_smoothTransition_mul_sub_mem {S : Set (Icc a b)} (hS : S.OrdConnected)
    {c x : Icc a b} (hc : c ∈ S) (hx : x ∈ S) (t : ℝ) :
    (⟨_, add_smoothTransition_mul_sub_mem_Icc c x t⟩ : Icc a b) ∈ S := by
  refine hS.uIcc_subset hc hx ?_
  have h := (convex_uIcc (c : ℝ) x).add_smul_sub_mem left_mem_uIcc right_mem_uIcc
    ⟨Real.smoothTransition.nonneg t, Real.smoothTransition.le_one t⟩
  simpa only [mem_uIcc, smul_eq_mul, ← Subtype.coe_le_coe] using h

private theorem contMDiff_add_smoothTransition_mul_sub (c : Icc a b) :
    ContMDiff (𝓘(ℝ, ℝ).prod (𝓡∂ 1)) (𝓡∂ 1) ∞ fun p : ℝ × Icc a b ↦
      (⟨_, add_smoothTransition_mul_sub_mem_Icc c p.2 p.1⟩ : Icc a b) := by
  have hval : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡∂ 1)) 𝓘(ℝ, ℝ) ∞
      fun p : ℝ × Icc a b ↦ (c : ℝ) + Real.smoothTransition p.1 * ((p.2 : ℝ) - c) :=
    contMDiff_const.add ((Real.smoothTransition.contDiff.contMDiff.comp contMDiff_fst).mul
      ((contMDiff_subtypeVal_Icc.comp contMDiff_snd).sub contMDiff_const))
  exact contMDiff_iff_comp_subtypeVal_Icc.2 ⟨(hval.continuous.subtype_mk _), hval⟩

/-- The **interval cover** of a segment: a locally finite cover of `[a, b]` by relatively open
order-connected sets, that is, by relatively open intervals possibly containing an endpoint, is a
smooth good cover of `[a, b]` with its boundary model `𝓡∂ 1`. A nonempty finite intersection `W`
of its members is again an interval; its center is a chosen point `c` of `W`, and it contracts by
the affine homotopy `(t, x) ↦ c + τ(t) (x - c)` with `τ = Real.smoothTransition`. -/
def ofOrdConnected {ι : Type} (J : ι → Opens (Icc a b)) (covers : ∀ x, ∃ i, x ∈ J i)
    (locallyFinite : LocallyFinite fun i ↦ (J i : Set (Icc a b)))
    (ordConnected : ∀ i, (J i : Set (Icc a b)).OrdConnected) :
    SmoothGoodCover (𝓡∂ 1) (M := Icc a b) where
  Index := ι
  openSet := J
  covers := covers
  locallyFinite := locallyFinite
  center _ _ hne := ⟨hne.some, hne.some_mem⟩
  contract s _ hne p :=
    ⟨⟨_, add_smoothTransition_mul_sub_mem_Icc hne.some p.2 p.1⟩,
      add_smoothTransition_mul_sub_mem
        (by
          rw [Opens.coe_finset_inf, Finset.inf_set_eq_iInter]
          exact ordConnected_biInter fun i _ ↦ ordConnected i)
        hne.some_mem p.2.property p.1⟩
  smooth _ _ hne := (ContMDiff.subtypeVal_comp_iff _ _).1 <|
    (contMDiff_add_smoothTransition_mul_sub hne.some).comp
      (contMDiff_fst.prodMk (contMDiff_subtypeVal.comp contMDiff_snd))
  at_zero _ _ _ x := by ext; simp
  at_one _ _ _ x := by ext; simp
  fixes_center _ _ _ t := by ext; simp

variable {ι : Type} (J : ι → Opens (Icc a b)) (covers : ∀ x, ∃ i, x ∈ J i)
  (locallyFinite : LocallyFinite fun i ↦ (J i : Set (Icc a b)))
  (ordConnected : ∀ i, (J i : Set (Icc a b)).OrdConnected)

/-- Identification of the index type of `SmoothGoodCover.ofOrdConnected` with `ι`. -/
def ofOrdConnectedIndexEquiv : (ofOrdConnected J covers locallyFinite ordConnected).Index ≃ ι :=
  Equiv.refl _

/-- The members of an interval cover are the given intervals. -/
@[simp]
theorem ofOrdConnected_openSet (i : (ofOrdConnected J covers locallyFinite ordConnected).Index) :
    (ofOrdConnected J covers locallyFinite ordConnected).openSet i =
      J (ofOrdConnectedIndexEquiv J covers locallyFinite ordConnected i) :=
  (rfl)

/-- The center of a nonempty finite intersection of an interval cover is the chosen point
`hW.some`. -/
@[simp]
theorem coe_center_ofOrdConnected
    (s : Finset (ofOrdConnected J covers locallyFinite ordConnected).Index) (hs : s.Nonempty)
    (hW : ((s.inf (ofOrdConnected J covers locallyFinite ordConnected).openSet :
      Opens (Icc a b)) : Set (Icc a b)).Nonempty) :
    ((ofOrdConnected J covers locallyFinite ordConnected).center s hs hW : Icc a b) = hW.some :=
  (rfl)

/-- The contraction of a nonempty finite intersection of an interval cover is the affine
contraction `(t, x) ↦ c + τ(t) (x - c)` to its center `c = hW.some`, reparametrized by
`τ = Real.smoothTransition`. -/
@[simp]
theorem coe_ofOrdConnected_contract
    (s : Finset (ofOrdConnected J covers locallyFinite ordConnected).Index) (hs : s.Nonempty)
    (hW : ((s.inf (ofOrdConnected J covers locallyFinite ordConnected).openSet :
      Opens (Icc a b)) : Set (Icc a b)).Nonempty)
    (p : ℝ × ↥(s.inf (ofOrdConnected J covers locallyFinite ordConnected).openSet)) :
    (((ofOrdConnected J covers locallyFinite ordConnected).contract s hs hW p : Icc a b) : ℝ) =
      (hW.some : ℝ) + Real.smoothTransition p.1 * ((p.2 : ℝ) - hW.some) :=
  (rfl)

end Interval

end SmoothGoodCover

end TauCeti
