/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.Local.Orientation
public import TauCeti.Topology.VectorBundle.MayerVietoris
public import TauCeti.Topology.VectorBundle.Orientation.Basic
import TauCeti.Algebra.Module.Equiv.SpanSingleton

/-!
# The integral Thom class of an oriented vector bundle

Let `E → B` be a real vector bundle whose model fibre `F` has dimension `n + 1`, with an
orientation `o` (`TauCeti.VectorBundleOrientation`). A linear trivialization `e` at a point `b`
reads the orientation `o b` of the fibre `E_b` as an orientation of `F`
(`Bundle.Trivialization.mapOrientation`), which selects a generator of `Hⁿ⁺¹(F, F ∖ {0}; ℤ)`
(`Orientation.localCohomologyClass`). Its pull-back along the isomorphism of fibre pairs
`(E_b, E_b ∖ {0}) ≅ (F, F ∖ {0})` given by `e` is a generator of `Hⁿ⁺¹(E_b, E_b ∖ {0}; ℤ)`, and it
does not depend on `e` (`Orientation.singularCohomologyMap_localCohomologyClass_map_eq`). The *Thom
class* of the oriented bundle is the class `U ∈ Hⁿ⁺¹(E, E₀; ℤ)` restricting to these generators on
all fibres.

Near a point `c`, the fibre orientations read in the trivialization at `c` are a single
orientation `ω` of `F`, so pulling back the generator selected by `ω` along that trivialization
gives a class over a neighbourhood of `c` with the prescribed restrictions to the fibres
(`Bundle.Trivialization.exists_singularCohomology_thomPairOver_fiber`). Over a compact base these
local classes glue, by Mayer–Vietoris over a finite trivializing cover
(`TauCeti.exists_singularCohomology_thomPair_fiber_of_compactSpace`), to the Thom class
(`TauCeti.VectorBundleOrientation.thomClass`). It is characterized by its restrictions to the
fibres (`TauCeti.VectorBundleOrientation.eq_thomClass_iff`), it is a Thom class in the sense of
`TauCeti.IsThomClass` (`TauCeti.VectorBundleOrientation.isThomClass_thomClass`), and the opposite
orientation has the opposite Thom class (`TauCeti.VectorBundleOrientation.thomClass_neg`).

The Thom class lives in degree `n + 1`, the degree in which the fibre generators are indexed;
`TauCeti.IsThomClass` is stated in degree `finrank ℝ F`, so `isThomClass_thomClass` transports it
along `finrank ℝ F = n + 1`. Integral coefficients are `ULift ℤ`, as for the fibre generators. The
rank zero case, where an orientation is a locally constant sign, is not treated here.

## Main definitions

* `TauCeti.VectorBundleOrientation.thomClass`: the integral Thom class of an oriented real vector
  bundle of positive rank over a compact base.

## Main results

* `TauCeti.VectorBundleOrientation.singularCohomologyMap_fiberThomPairMap_thomClass`: the Thom
  class restricts on each fibre to the generator selected by the fibre orientation, read in any
  linear trivialization.
* `TauCeti.VectorBundleOrientation.eq_thomClass_iff`: this property characterizes it.
* `TauCeti.VectorBundleOrientation.thomClass_neg`: reversing the orientation negates it.
* `TauCeti.VectorBundleOrientation.isThomClass_thomClass`: it is a Thom class.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §10, Theorem 10.4 and its proof (the fundamental class of an oriented bundle,
  glued from local classes over a finite trivializing cover).
* A. Hatcher, *Algebraic Topology*, Section 4.D, Theorem 4D.10.
-/

public section

noncomputable section

open Bundle CategoryTheory Module Set
open scoped Topology

universe w

namespace TauCeti.VectorBundleOrientation

variable {B : Type w} [TopologicalSpace B] [CompactSpace B] {F : Type w} [NormedAddCommGroup F]
  [NormedSpace ℝ F] {E : B → Type w} [TopologicalSpace (TotalSpace F E)] [∀ b, AddCommMonoid (E b)]
  [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E] [VectorBundle ℝ F E]
  {n : ℕ} (o : VectorBundleOrientation F E (Fin (n + 1))) (hF : finrank ℝ F = n + 1)

omit [CompactSpace B] in
/-- The generators of `Hⁿ⁺¹(E_b, E_b ∖ {0}; ℤ)` selected by `o b` read in two linear
trivializations agree. -/
private theorem fiberGenerator_eq (e e' : Trivialization F (π F E)) [e.IsLinear ℝ]
    [e'.IsLinear ℝ] {b : B} (hb : b ∈ e.baseSet) (hb' : b ∈ e'.baseSet) :
    TopPair.singularCohomologyMap (e.continuousLinearEquivAt ℝ b hb).complZeroPairIso.hom (n + 1)
        ((e.mapOrientation (Fin (n + 1)) hb (o b)).localCohomologyClass hF) =
      TopPair.singularCohomologyMap (e'.continuousLinearEquivAt ℝ b hb').complZeroPairIso.hom
        (n + 1) ((e'.mapOrientation (Fin (n + 1)) hb' (o b)).localCohomologyClass hF) := by
  rw [Trivialization.mapOrientation_eq_map_continuousLinearEquivAt,
    Trivialization.mapOrientation_eq_map_continuousLinearEquivAt]
  exact Orientation.singularCohomologyMap_localCohomologyClass_map_eq _ _ _ hF

omit [VectorBundle ℝ F E] in
/-- `TauCeti.exists_singularCohomology_thomPair_fiber_of_compactSpace`, in a degree `d` equal to
`finrank ℝ F`. -/
private theorem exists_singularCohomology_thomPair_fiber [FiniteDimensional ℝ F] {d : ℕ}
    (hd : finrank ℝ F = d)
    (g : ∀ b, (TopPair.ofSubset (X := TopCat.of (E b)) ({0}ᶜ : Set (E b))).singularCohomology
      (ModuleCat.of ℤ (ULift.{w} ℤ)) ℤ (ModuleCat.of ℤ (ULift.{w} ℤ)) d)
    (hg : ∀ c, ∃ W : Set B, IsOpen W ∧ c ∈ W ∧
      (∃ (e : Trivialization F (π F E)) (_ : e.IsLinear ℝ), W ⊆ e.baseSet) ∧
      ∃ u : (thomPairOver F E W).singularCohomology (ModuleCat.of ℤ (ULift.{w} ℤ)) ℤ
        (ModuleCat.of ℤ (ULift.{w} ℤ)) d, ∀ b (hb : b ∈ W),
        TopPair.singularCohomologyMap (fiberThomPairOverMap F E hb) _ u = g b) :
    ∃ x : (thomPair F E).singularCohomology (ModuleCat.of ℤ (ULift.{w} ℤ)) ℤ
        (ModuleCat.of ℤ (ULift.{w} ℤ)) d,
      ∀ b, TopPair.singularCohomologyMap (fiberThomPairMap F E b) _ x = g b := by
  subst hd
  exact exists_singularCohomology_thomPair_fiber_of_compactSpace g hg

/-- `TauCeti.singularCohomology_thomPair_ext_of_compactSpace`, in a degree `d` equal to
`finrank ℝ F`. -/
private theorem singularCohomology_thomPair_ext [FiniteDimensional ℝ F] {d : ℕ}
    (hd : finrank ℝ F = d)
    {u v : (thomPair F E).singularCohomology (ModuleCat.of ℤ (ULift.{w} ℤ)) ℤ
      (ModuleCat.of ℤ (ULift.{w} ℤ)) d}
    (h : ∀ b, TopPair.singularCohomologyMap (fiberThomPairMap F E b) _ u =
      TopPair.singularCohomologyMap (fiberThomPairMap F E b) _ v) : u = v := by
  subst hd
  exact singularCohomology_thomPair_ext_of_compactSpace h

/-- A class of `Hⁿ⁺¹(E, E₀; ℤ)` restricting on every fibre to the generator selected by the fibre
orientation, read in the trivialization at that point. -/
private theorem exists_thomClass :
    ∃ x : (thomPair F E).singularCohomology (ModuleCat.of ℤ (ULift.{w} ℤ)) ℤ
        (ModuleCat.of ℤ (ULift.{w} ℤ)) (n + 1),
      ∀ b, TopPair.singularCohomologyMap (fiberThomPairMap F E b) _ x =
        TopPair.singularCohomologyMap ((trivializationAt F E b).continuousLinearEquivAt ℝ b
          (FiberBundle.mem_baseSet_trivializationAt' b)).complZeroPairIso.hom (n + 1)
          (((trivializationAt F E b).mapOrientation (Fin (n + 1))
            (FiberBundle.mem_baseSet_trivializationAt' b) (o b)).localCohomologyClass hF) := by
  have := FiniteDimensional.of_finrank_eq_succ hF
  refine exists_singularCohomology_thomPair_fiber hF _ fun c ↦ ?_
  -- Near `c` the fibre orientations read in the trivialization `e` at `c` are a single
  -- orientation `ω` of `F`; pull back the generator it selects along `e`.
  let e := trivializationAt F E c
  have hc : c ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' c
  obtain ⟨t, ht, hto, hct⟩ := eventually_nhds_iff.1 (o.eventually_mapOrientation_eq' c)
  obtain ⟨u, hu⟩ := e.exists_singularCohomology_thomPairOver_fiber ℝ (W := t ∩ e.baseSet)
    inter_subset_right ((e.mapOrientation (Fin (n + 1)) hc (o c)).localCohomologyClass hF)
  refine ⟨t ∩ e.baseSet, hto.inter e.open_baseSet, ⟨hct, hc⟩,
    ⟨e, inferInstance, inter_subset_right⟩, u, fun b hb ↦ ?_⟩
  have hω : e.mapOrientation (Fin (n + 1)) hb.2 (o b) = e.mapOrientation (Fin (n + 1)) hc (o c) :=
    ht b hb.1 hb.2
  rw [hu b hb, ← hω]
  exact fiberGenerator_eq o hF _ _ _ _

/-- **The integral Thom class of an oriented vector bundle.** For an orientation `o` of a real
vector bundle `E` over a compact base, with model fibre `F` of dimension `n + 1`, this is the class
`U ∈ Hⁿ⁺¹(E, E₀; ℤ)` whose restriction to the fibre pair `(E_b, E_b ∖ {0})` over every point `b`
is the generator of `Hⁿ⁺¹(E_b, E_b ∖ {0}; ℤ)` selected by the orientation `o b`: the pull-back,
along any linear trivialization at `b`, of the generator of `Hⁿ⁺¹(F, F ∖ {0}; ℤ)` selected by `o b`
read in that trivialization
(`TauCeti.VectorBundleOrientation.singularCohomologyMap_fiberThomPairMap_thomClass`). This
property determines it (`TauCeti.VectorBundleOrientation.eq_thomClass_iff`). -/
def thomClass :
    (thomPair F E).singularCohomology (ModuleCat.of ℤ (ULift.{w} ℤ)) ℤ
      (ModuleCat.of ℤ (ULift.{w} ℤ)) (n + 1) :=
  (exists_thomClass o hF).choose

/-- The Thom class of an oriented bundle restricts on the fibre pair over every point `b` to the
generator of `Hⁿ⁺¹(E_b, E_b ∖ {0}; ℤ)` selected by the orientation of `E_b`, read in any linear
trivialization `e` at `b`. -/
theorem singularCohomologyMap_fiberThomPairMap_thomClass (e : Trivialization F (π F E))
    [e.IsLinear ℝ] {b : B} (hb : b ∈ e.baseSet) :
    TopPair.singularCohomologyMap (fiberThomPairMap F E b) _ (o.thomClass hF) =
      TopPair.singularCohomologyMap (e.continuousLinearEquivAt ℝ b hb).complZeroPairIso.hom
        (n + 1) ((e.mapOrientation (Fin (n + 1)) hb (o b)).localCohomologyClass hF) :=
  ((exists_thomClass o hF).choose_spec b).trans (fiberGenerator_eq o hF _ _ _ _)

/-- **Uniqueness of the Thom class.** A class of `Hⁿ⁺¹(E, E₀; ℤ)` is the Thom class of the oriented
bundle exactly when it restricts on every fibre to the generator selected by the fibre
orientation, read in a linear trivialization at that point. -/
theorem eq_thomClass_iff
    (u : (thomPair F E).singularCohomology (ModuleCat.of ℤ (ULift.{w} ℤ)) ℤ
      (ModuleCat.of ℤ (ULift.{w} ℤ)) (n + 1)) :
    u = o.thomClass hF ↔ ∀ (e : Trivialization F (π F E)) [e.IsLinear ℝ] (b : B)
      (hb : b ∈ e.baseSet), TopPair.singularCohomologyMap (fiberThomPairMap F E b) _ u =
        TopPair.singularCohomologyMap (e.continuousLinearEquivAt ℝ b hb).complZeroPairIso.hom
          (n + 1) ((e.mapOrientation (Fin (n + 1)) hb (o b)).localCohomologyClass hF) := by
  have := FiniteDimensional.of_finrank_eq_succ hF
  refine ⟨fun h e _ b hb ↦ h ▸ o.singularCohomologyMap_fiberThomPairMap_thomClass hF e hb,
    fun h ↦ singularCohomology_thomPair_ext hF fun b ↦ ?_⟩
  have hb := FiberBundle.mem_baseSet_trivializationAt' (F := F) (E := E) b
  rw [h _ b hb, o.singularCohomologyMap_fiberThomPairMap_thomClass hF _ hb]

/-- Reversing the orientation negates the Thom class. -/
@[simp]
theorem thomClass_neg : (-o).thomClass hF = -o.thomClass hF := by
  symm
  refine (eq_thomClass_iff (-o) hF _).2 fun e _ b hb ↦ ?_
  rw [map_neg, o.singularCohomologyMap_fiberThomPairMap_thomClass hF e hb, neg_apply,
    Trivialization.mapOrientation_neg, Orientation.localCohomologyClass_neg, map_neg]

/-- **The Thom class of an oriented bundle is a Thom class**: transported to the degree
`finrank ℝ F = n + 1`, it restricts to a generator of the integral cohomology of every fibre
pair. -/
theorem isThomClass_thomClass :
    IsThomClass F E (hF ▸ o.thomClass hF :
      (thomPair F E).singularCohomology (ModuleCat.of ℤ (ULift.{w} ℤ)) ℤ
        (ModuleCat.of ℤ (ULift.{w} ℤ)) (finrank ℝ F)) := by
  have := FiniteDimensional.of_finrank_eq_succ hF
  -- Transport along `finrank ℝ F = d` commutes with the fibre restrictions.
  have key {d : ℕ} (hd : finrank ℝ F = d)
      (x : (thomPair F E).singularCohomology (ModuleCat.of ℤ (ULift.{w} ℤ)) ℤ
        (ModuleCat.of ℤ (ULift.{w} ℤ)) d)
      (hx : ∀ b, Submodule.span ℤ
        {(TopPair.singularCohomologyMap (fiberThomPairMap F E b) d x)} = ⊤) :
      IsThomClass F E (hd ▸ x : (thomPair F E).singularCohomology
        (ModuleCat.of ℤ (ULift.{w} ℤ)) ℤ (ModuleCat.of ℤ (ULift.{w} ℤ)) (finrank ℝ F)) := by
    subst hd
    exact isThomClass_iff.2 ⟨inferInstance, hx⟩
  refine key hF _ fun b ↦ ?_
  have hb := FiberBundle.mem_baseSet_trivializationAt' (F := F) (E := E) b
  rw [o.singularCohomologyMap_fiberThomPairMap_thomClass hF _ hb]
  -- An isomorphism of pairs induces a linear isomorphism in cohomology, carrying generators to
  -- generators.
  exact ((TopPair.singularCohomologyFunctor (ModuleCat.of ℤ (ULift.{w} ℤ)) ℤ
    (ModuleCat.of ℤ (ULift.{w} ℤ)) (n + 1)).mapIso
      ((trivializationAt F E b).continuousLinearEquivAt ℝ b hb).complZeroPairIso.op
    ).toLinearEquiv.span_singleton_apply_eq_top_iff.2 (Orientation.span_localCohomologyClass _ _)

end TauCeti.VectorBundleOrientation
