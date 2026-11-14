/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Spectral.ProConstructible
public import TauCeti.Topology.Spectral.WLocal
public import Mathlib.Topology.Compactification.OnePoint.Basic
import TauCeti.Topology.ConnectedComponents
import TauCeti.Topology.Spectral.ConnectedComponents
import TauCeti.Topology.Spectral.Limits.Basic
import TauCeti.Topology.Spectral.SpectralMap
import Mathlib.Topology.Order.UpperLowerSetTopology
import Mathlib.Topology.Separation.Regular
import Mathlib.Topology.UnitInterval

/-!
# Worked examples and counterexamples for split open covers and w-local spaces

This file tests the definitions and theorems of `TauCeti.Topology.ConnectedComponents`,
`TauCeti.Topology.Spectral.ConnectedComponents`, and `TauCeti.Topology.Spectral.WLocal` across basic
examples and boundary counterexamples:

* Empty and profinite spaces (`Empty`, `Bool`, the Cantor space `ℕ → Bool`) are w-local and have
  split open covers.
* The Sierpiński space `Prop` is a connected non-Hausdorff w-local spectral space whose unique
  closed point `False` maps homeomorphically to its singleton component space.
* On the compact connected unit interval `unitInterval`, open covers do not split because `0` and
  `1` are distinct closed points in a single connected component.
* Discrete `ℕ` satisfies `OpenCoversSplit ℕ` and has a closed locus of closed points, yet is not
  w-local because it is not compact (hence not spectral).
* Inside `OnePoint ℕ × Prop`, the pro-constructible subspace
  `({∞} ×ˢ univ) ∪ (univ ×ˢ {True})` is spectral and has split open covers, yet its closed points
  omit only `(∞, True)`, which is not isolated; thus it is not w-local, showing both that the
  closed-point condition in `IsWLocalSpace` is independent of `OpenCoversSplit` on spectral spaces
  and that `IsWLocalSpace.isClosed` cannot be weakened to pro-constructible subspaces.
-/

public section

open Set Topology TopologicalSpace
open scoped OnePoint

namespace TauCeti.Examples.WLocal

/-- The empty space is w-local, has split open covers, and has an empty component space. -/
example : IsWLocalSpace Empty ∧ OpenCoversSplit Empty ∧ IsEmpty (ConnectedComponents Empty) :=
  ⟨.of_isEmpty Empty, .of_isEmpty Empty,
    ⟨fun c ↦ (ConnectedComponents.surjective_coe c).choose.elim⟩⟩

private theorem isClosed_false_prop : IsClosed ({False} : Set Prop) := by
  convert isOpen_singleton_true.isClosed_compl
  exact Set.ext fun p ↦ ⟨fun hp hpT ↦
    ((mem_singleton_iff.1 hp).symm.trans (mem_singleton_iff.1 hpT)).mpr trivial,
    fun hpT ↦ eq_false fun hp ↦ hpT (eq_true hp)⟩

private theorem not_isClosed_true_prop : ¬ IsClosed ({True} : Set Prop) := fun hc ↦ by
  have h : True ∈ ({True} : Set Prop)ᶜ :=
    Topology.IsUpperSet.isOpen_iff_isUpperSet.1 hc.isOpen_compl
      (fun h ↦ h.elim : False ≤ True) (by simp)
  exact h rfl

private theorem connectedSpace_prop : ConnectedSpace Prop :=
  { toNonempty := inferInstance
    isPreconnected_univ := fun u v hu hv huv ⟨p, _, hp⟩ ⟨q, _, hq⟩ ↦ by
      have hup {t : Set Prop} (ht : IsOpen t) (hF : False ∈ t) : True ∈ t :=
        Topology.IsUpperSet.isOpen_iff_isUpperSet.1 ht (fun h ↦ h.elim : False ≤ True) hF
      rcases huv (mem_univ False) with hFu | hFv
      · refine ⟨q, trivial, ?_, hq⟩
        by_cases hqT : q
        · exact (eq_true hqT) ▸ hup hu hFu
        · exact (eq_false hqT) ▸ hFu
      · refine ⟨p, trivial, hp, ?_⟩
        by_cases hpT : p
        · exact (eq_true hpT) ▸ hup hv hFv
        · exact (eq_false hpT) ▸ hFv }

/-- In the Sierpiński space `Prop`, `{True}` is open and `{False}` is the unique closed singleton;
hence `Prop` is a connected w-local space that is not Hausdorff. -/
example : ConnectedSpace Prop ∧ IsWLocalSpace Prop ∧ ¬ T2Space Prop ∧
    IsHomeomorph (fun x : {p : Prop | IsClosed ({p} : Set Prop)} ↦
      ConnectedComponents.mk (x : Prop)) := by
  have : SpectralSpace Prop := spectralSpace_prop
  have := connectedSpace_prop
  have hcl_eq : {p : Prop | IsClosed ({p} : Set Prop)} = {False} := Set.ext fun p ↦ by
    by_cases hp : p
    · simp [eq_true hp, not_isClosed_true_prop]
    · simp [eq_false hp, isClosed_false_prop]
  have hsplit : OpenCoversSplit Prop := (openCoversSplit_iff Prop).2 fun _ ↦
    ⟨False, ⟨by simp [PreconnectedSpace.connectedComponent_eq_univ], isClosed_false_prop⟩,
      fun q ⟨_, hq⟩ ↦
        mem_singleton_iff.1 (hcl_eq ▸ (hq : q ∈ {p : Prop | IsClosed ({p} : Set Prop)}))⟩
  have hw : IsWLocalSpace Prop :=
    (isWLocalSpace_def Prop).2 ⟨spectralSpace_prop, hsplit, hcl_eq ▸ isClosed_false_prop⟩
  exact ⟨this, hw, fun _ ↦ not_isClosed_true_prop isClosed_singleton,
    hw.isHomeomorph_connectedComponentsMk⟩

/-- On discrete `Bool`, `connectedComponentsClopensOrderIso` sends a singleton component clopen to
the corresponding singleton clopen, and the Cantor space `ℕ → Bool` is w-local. -/
example : (((connectedComponentsClopensOrderIso Bool).symm
      ⟨{false}, isClopen_discrete _⟩ : Clopens (ConnectedComponents Bool)) :
      Set (ConnectedComponents Bool)) = {ConnectedComponents.mk false} ∧
    IsWLocalSpace (ℕ → Bool) := by
  have : SpectralSpace Bool := spectralSpace_of_zeroDimensionalSpace Bool
  exact ⟨by simp, .of_zeroDimensionalSpace (ℕ → Bool)⟩

/-- The compact connected unit interval `[0, 1]` does not have split open covers because `0` and `1`
are distinct closed points in the same connected component. -/
example : CompactSpace unitInterval ∧ ConnectedSpace unitInterval ∧
    ¬ OpenCoversSplit unitInterval := by
  refine ⟨inferInstance, inferInstance, fun h ↦ ?_⟩
  have h01 : (0 : unitInterval) = 1 :=
    h.eq_of_mem_connectedComponent
      (by simp [PreconnectedSpace.connectedComponent_eq_univ])
      isClosed_singleton isClosed_singleton
  exact zero_ne_one (congrArg Subtype.val h01)

/-- Discrete `ℕ` has split open covers and closed locus of closed points, yet is not w-local because
it is not compact. -/
example : OpenCoversSplit ℕ ∧ IsClosed {n : ℕ | IsClosed ({n} : Set ℕ)} ∧ ¬ IsWLocalSpace ℕ := by
  refine ⟨.of_discreteTopology ℕ, isClosed_discrete _, fun h ↦ ?_⟩
  have hc : CompactSpace ℕ := h.spectralSpace.toCompactSpace
  exact infinite_univ (isCompact_iff_finite.1 hc.isCompact_univ)

private theorem zeroDimensionalSpace_onePoint_nat : ZeroDimensionalSpace (OnePoint ℕ) := by
  have hcl (n : ℕ) : IsClopen ({(n : OnePoint ℕ)} : Set (OnePoint ℕ)) :=
    ⟨isClosed_singleton, by
      simpa [image_singleton] using OnePoint.isOpenEmbedding_coe.isOpenMap {n} (isOpen_discrete _)⟩
  have : TotallySeparatedSpace (OnePoint ℕ) := totallySeparatedSpace_iff_exists_isClopen.2
    fun x y hxy ↦ by
      cases x using OnePoint.rec with
      | infty =>
        cases y using OnePoint.rec with
        | infty => exact (hxy rfl).elim
        | coe n =>
          exact ⟨{(n : OnePoint ℕ)}ᶜ, (hcl n).compl, (OnePoint.coe_ne_infty n).symm, fun h ↦ h rfl⟩
      | coe n => exact ⟨{(n : OnePoint ℕ)}, hcl n, rfl, hxy.symm⟩
  infer_instance

private def OnePointOrProp : Bool → Type
  | false => Prop
  | true => OnePoint ℕ

private instance (b : Bool) : TopologicalSpace (OnePointOrProp b) :=
  match b with
  | false => inferInstanceAs (TopologicalSpace Prop)
  | true => inferInstanceAs (TopologicalSpace (OnePoint ℕ))

private instance (b : Bool) : SpectralSpace (OnePointOrProp b) :=
  match b with
  | false => spectralSpace_prop
  | true =>
    have := zeroDimensionalSpace_onePoint_nat
    spectralSpace_of_zeroDimensionalSpace (OnePoint ℕ)

private theorem spectralSpace_onePoint_prod_prop : SpectralSpace (OnePoint ℕ × Prop) := by
  let e : (OnePoint ℕ × Prop) ≃ₜ ∀ b, OnePointOrProp b :=
    { toFun := fun p b ↦ match b with | false => p.2 | true => p.1
      invFun := fun f ↦ (f true, f false)
      left_inv := fun ⟨_, _⟩ ↦ rfl
      right_inv := fun f ↦ funext fun b ↦ by cases b <;> rfl
      continuous_toFun := continuous_pi fun b ↦ by
        cases b
        · exact continuous_snd
        · exact continuous_fst
      continuous_invFun := (continuous_apply true).prodMk (continuous_apply false) }
  exact e.isOpenEmbedding.spectralSpace

/-- The pro-constructible comb `({∞} ×ˢ univ) ∪ (univ ×ˢ {True})` inside `OnePoint ℕ × Prop`. -/
def combSpace : Set (OnePoint ℕ × Prop) :=
  ({(∞ : OnePoint ℕ)} ×ˢ Set.univ) ∪ (Set.univ ×ˢ {True})

/-- `combSpace` is pro-constructible in `OnePoint ℕ × Prop`. -/
theorem isProConstructible_combSpace : IsProConstructible combSpace := by
  have := spectralSpace_onePoint_prod_prop
  have : SpectralSpace Prop := spectralSpace_prop
  have : ZeroDimensionalSpace (OnePoint ℕ) := zeroDimensionalSpace_onePoint_nat
  have : SpectralSpace (OnePoint ℕ) := spectralSpace_of_zeroDimensionalSpace (OnePoint ℕ)
  refine (OnePoint.isClosed_infty.isProConstructible.prod isClosed_univ.isProConstructible).union ?_
  exact isClosed_univ.isProConstructible.prod
    ((Set.toFinite ({True} : Set Prop)).isCompact.isProConstructible isOpen_singleton_true)

private theorem isClopen_combSpace_coe (n : ℕ) :
    IsClopen
      ({(⟨((n : OnePoint ℕ), True), Or.inr ⟨trivial, rfl⟩⟩ : combSpace)} : Set combSpace) := by
  have hn_open : IsOpen ({(n : OnePoint ℕ)} : Set (OnePoint ℕ)) := by
    simpa [image_singleton] using OnePoint.isOpenEmbedding_coe.isOpenMap {n} (isOpen_discrete _)
  constructor
  · convert (isClosed_singleton (x := (n : OnePoint ℕ)).prod (isClosed_univ (X := Prop))).preimage
      (continuous_subtype_val (p := (· ∈ combSpace)))
    ext ⟨⟨a, p⟩, hz⟩
    simp only [mem_singleton_iff, Subtype.ext_iff, Prod.ext_iff, mem_preimage, mem_prod, mem_univ,
      and_true]
    exact ⟨fun h ↦ h.1, fun ha ↦ ⟨ha, (hz.resolve_left fun h ↦
      OnePoint.coe_ne_infty n (ha ▸ h.1)).2⟩⟩
  · convert (hn_open.prod isOpen_singleton_true).preimage
      (continuous_subtype_val (p := (· ∈ combSpace)))
    ext ⟨⟨a, p⟩, hz⟩
    simp [Subtype.ext_iff]

private def combInfty (p : Prop) : combSpace := ⟨(∞, p), Or.inl ⟨rfl, trivial⟩⟩

private theorem isClosed_combInfty_false : IsClosed ({combInfty False} : Set combSpace) := by
  convert (OnePoint.isClosed_infty.prod isClosed_false_prop).preimage
    (continuous_subtype_val (p := (· ∈ combSpace)))
  ext ⟨⟨a, p⟩, _⟩
  simp [combInfty, Subtype.ext_iff]

private theorem not_isClosed_combInfty_true : ¬ IsClosed ({combInfty True} : Set combSpace) := by
  intro hc
  have hι : Continuous combInfty := Continuous.subtype_mk (continuous_const.prodMk continuous_id) _
  have hcP : IsClosed ({True} : Set Prop) := by
    convert hc.preimage hι
    ext p
    simp [combInfty, Subtype.ext_iff]
  exact not_isClosed_true_prop hcP

/-- Every open cover of `combSpace` splits. -/
theorem openCoversSplit_combSpace : OpenCoversSplit combSpace := by
  have := spectralSpace_onePoint_prod_prop
  have : SpectralSpace combSpace := isProConstructible_combSpace.spectralSpace
  have := connectedSpace_prop
  have hι : Continuous combInfty := Continuous.subtype_mk (continuous_const.prodMk continuous_id) _
  have hTF : combInfty False ∈ connectedComponent (combInfty True) :=
    (isPreconnected_univ.image combInfty hι.continuousOn).subset_connectedComponent
      ⟨True, trivial, rfl⟩ ⟨False, trivial, rfl⟩
  refine (openCoversSplit_iff combSpace).2 fun ⟨⟨a, p⟩, hz⟩ ↦ ?_
  cases a using OnePoint.rec with
  | coe n =>
    have hp : p = True := (hz.resolve_left fun h ↦ OnePoint.coe_ne_infty n h.1).2
    subst hp
    refine ⟨⟨((n : OnePoint ℕ), True), hz⟩,
      ⟨mem_connectedComponent, (isClopen_combSpace_coe n).isClosed⟩, fun w ⟨hw, _⟩ ↦ ?_⟩
    exact mem_singleton_iff.1 ((isClopen_combSpace_coe n).connectedComponent_subset rfl hw)
  | infty =>
    have hzc : combInfty False ∈ connectedComponent ⟨(∞, p), hz⟩ := by
      by_cases hp : p
      · simpa [combInfty, eq_true hp] using hTF
      · simp [combInfty, eq_false hp, mem_connectedComponent]
    refine ⟨combInfty False, ⟨hzc, isClosed_combInfty_false⟩, fun ⟨⟨b, q⟩, hwz⟩ ⟨hw, hwcl⟩ ↦ ?_⟩
    cases b using OnePoint.rec with
    | coe n =>
      have hq : q = True := (hwz.resolve_left fun h ↦ OnePoint.coe_ne_infty n h.1).2
      subst hq
      have heq : combInfty False = ⟨((n : OnePoint ℕ), True), hwz⟩ := mem_singleton_iff.1
        ((isClopen_combSpace_coe n).connectedComponent_subset rfl
          ((connectedComponent_eq hw) ▸ hzc))
      exact (OnePoint.coe_ne_infty n (congrArg (fun z : combSpace ↦ z.1.1) heq).symm).elim
    | infty =>
      by_cases hq : q
      · exact (not_isClosed_combInfty_true (by simpa [combInfty, eq_true hq] using hwcl)).elim
      · simp [combInfty, eq_false hq]

/-- The spectral space `combSpace` satisfies `OpenCoversSplit combSpace`, yet is not w-local because
its closed points omit only the non-isolated point `(∞, True)`. -/
example : SpectralSpace combSpace ∧ OpenCoversSplit combSpace ∧ ¬ IsWLocalSpace combSpace := by
  have := spectralSpace_onePoint_prod_prop
  refine ⟨isProConstructible_combSpace.spectralSpace, openCoversSplit_combSpace, fun hw ↦ ?_⟩
  have hcompl_eq : ({z : combSpace | IsClosed ({z} : Set combSpace)})ᶜ = {combInfty True} := by
    ext ⟨⟨a, p⟩, hz⟩
    simp only [mem_compl_iff, Set.mem_ofPred_eq, mem_singleton_iff]
    cases a using OnePoint.rec with
    | coe n =>
      have hp : p = True := (hz.resolve_left fun h ↦ OnePoint.coe_ne_infty n h.1).2
      subst hp
      exact ⟨fun h ↦ (h (isClopen_combSpace_coe n).isClosed).elim,
        fun h ↦ (OnePoint.coe_ne_infty n (congrArg (fun z : combSpace ↦ z.1.1) h)).elim⟩
    | infty =>
      by_cases hp : p
      · have hpT : p = True := eq_true hp
        subst hpT
        exact ⟨fun _ ↦ rfl, fun _ ↦ not_isClosed_combInfty_true⟩
      · have hpF : p = False := eq_false hp
        subst hpF
        exact ⟨fun h ↦ (h isClosed_combInfty_false).elim, fun h ↦
          ((congrArg (fun z : combSpace ↦ z.1.2) h).symm.mp trivial).elim⟩
  have hzT_open : IsOpen ({combInfty True} : Set combSpace) :=
    hcompl_eq ▸ hw.isClosed_closedPoints.isOpen_compl
  obtain ⟨W, hWo, hWpre⟩ := isOpen_induced_iff.1 hzT_open
  have hW_inf : ((∞ : OnePoint ℕ), True) ∈ W := by
    have : combInfty True ∈ Subtype.val ⁻¹' W := by rw [hWpre]; rfl
    exact this
  have hU_open : IsOpen {a : OnePoint ℕ | (a, True) ∈ W} :=
    hWo.preimage (continuous_id.prodMk continuous_const)
  have : NoncompactSpace ℕ := ⟨fun hc ↦ infinite_univ (isCompact_iff_finite.1 hc)⟩
  have hmem : {a : OnePoint ℕ | (a, True) ∈ W} ∩ {(∞ : OnePoint ℕ)}ᶜ ∈ 𝓝[≠] (∞ : OnePoint ℕ) :=
    Filter.inter_mem (nhdsWithin_le_nhds (hU_open.mem_nhds hW_inf)) self_mem_nhdsWithin
  obtain ⟨a, haW, ha_ne⟩ :=
    Filter.NeBot.nonempty_of_mem (OnePoint.nhdsNE_infty_neBot (X := ℕ)) hmem
  obtain ⟨n, rfl⟩ := OnePoint.ne_infty_iff_exists.1 ha_ne
  have hzn : (⟨((n : OnePoint ℕ), True), Or.inr ⟨trivial, rfl⟩⟩ : combSpace) ∈
      ({combInfty True} : Set combSpace) := by
    rw [← hWpre]
    exact haW
  exact OnePoint.coe_ne_infty n (congrArg (fun z : combSpace ↦ z.1.1) (mem_singleton_iff.1 hzn))

end TauCeti.Examples.WLocal
