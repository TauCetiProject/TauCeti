/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.CompactOpen
public import Mathlib.Topology.Convenient.HomSpace
public import Mathlib.Topology.Homeomorph.Lemmas
public import TauCeti.Topology.Convenient.GeneratedBy

/-!
# Products with locally compact spaces and compact-open comparisons for generated spaces

For a generating family `X : ι → Type u` of topological spaces, the convenient product in the
category of `X`-generated spaces refines the ordinary product topology by
`WithGeneratedByTopology X (Y × Z)`. When every member `X i` is locally compact and every pairwise
product `X i × X j` is `X`-generated, this refinement is unnecessary as soon as one of the factors
is locally compact: if `Y` and `Z` are `X`-generated and `Y` (or `Z`) is locally compact, then the
ordinary product `Y × Z` is already `X`-generated
(`Topology.IsGeneratedBy.prod_of_locallyCompactSpace_left` and
`Topology.IsGeneratedBy.prod_of_locallyCompactSpace_right`), so the counit is a homeomorphism
`WithGeneratedByTopology X (Y × Z) ≃ₜ Y × Z`.

The proof splits according to whether some `X i` is nonempty. When some `X i₀` is nonempty, every
point of an `X`-generated space is hit by a constant map out of `X i₀`, so the single coinducing
evaluation map out of `Σ (p : (i : ι) × C(X i, W)), X p.1` is surjective and therefore a quotient
map (`Topology.IsGeneratedBy.isQuotientMap_sigmaEval`). Applying Whitehead's quotient-product
lemma (`Topology.IsQuotientMap.continuous_lift_prod_left` and `continuous_lift_prod_right`) first
along each locally compact test space `X j` and then along the locally compact factor `Y` reduces
continuity on `Y × Z` to continuity on the `X`-generated spaces `X i × X j`. When every `X i` is
empty, every `X`-generated space is discrete, and so is `Y × Z`.

Under the same hypotheses on `X`, we also compare the `X`-continuous mapping space
`Topology.ContinuousMapGeneratedBy X Y T` with the ordinary compact-open mapping space `C(Y, T)`:

* `ContinuousMap.toContinuousMapGeneratedBy` embeds `C(Y, T)` continuously into
  `ContinuousMapGeneratedBy X Y T` for arbitrary `Y` and `T`.
* When `Y` is `X`-generated, `Topology.ContinuousMapGeneratedBy.equivContinuousMap` identifies
  `ContinuousMapGeneratedBy X Y T` as a type with `C(Y, T)`.
* When `Y` is `X`-generated, a map from any test space `X i` into `C(Y, T)` is continuous once its
  uncurrying `X i × Y → T` is continuous (compact-open currying needs no local compactness on `Y`),
  which by `X`-generation of `X i × Y` agrees with continuity into `ContinuousMapGeneratedBy X Y T`.
  Consequently their `X`-generated refinements are homeomorphic for every `X`-generated space `Y`
  (`Topology.ContinuousMapGeneratedBy.generatedByHomeomorphContinuousMap`).

## References

* R. H. Fox, *On topologies for function spaces*, Bull. Amer. Math. Soc. 51 (1945), 429–432.
* J. H. C. Whitehead, *Note on a theorem due to Borsuk*, Bull. Amer. Math. Soc. 54 (1948),
  1125–1132.
* R. M. Vogt, *Convenient categories of topological spaces for homotopy theory*, Arch. Math.
  (Basel) 22 (1971), 545–555.
* M. Escardó, J. Lawson and A. Simpson, *Comparing Cartesian closed categories of (core) compactly
  generated spaces*, Topology Appl. 143 (2004), 105–145.
-/

public section

universe t u v v' v''

open Topology

section Product

variable {ι : Type t} (X : ι → Type u) [∀ i, TopologicalSpace (X i)]

namespace Topology.IsGeneratedBy

/-- The canonical evaluation map from the disjoint union of all continuous test maps `X i → Y`
into `Y`. -/
def sigmaEval (Y : Type v) [TopologicalSpace Y] (p : (f : (i : ι) × C(X i, Y)) × X f.1) : Y :=
  p.1.2 p.2

theorem sigmaEval_def (Y : Type v) [TopologicalSpace Y] :
    sigmaEval X Y = fun p : (f : (i : ι) × C(X i, Y)) × X f.1 ↦ p.1.2 p.2 :=
  (rfl)

@[simp]
theorem sigmaEval_apply {Y : Type v} [TopologicalSpace Y]
    (i : ι) (f : C(X i, Y)) (x : X i) :
    sigmaEval X Y ⟨⟨i, f⟩, x⟩ = f x :=
  (rfl)

/-- The canonical evaluation map out of the sigma space of continuous test maps is always
continuous. -/
@[continuity, fun_prop]
theorem continuous_sigmaEval (Y : Type v) [TopologicalSpace Y] :
    Continuous (sigmaEval X Y) :=
  continuous_sigma fun ⟨_, f⟩ ↦ f.continuous

/-- For an `X`-generated space `Y`, the canonical evaluation map `sigmaEval X Y` coinduces the
topology of `Y`. -/
theorem isCoinducing_sigmaEval (Y : Type v) [TopologicalSpace Y] [IsGeneratedBy X Y] :
    IsCoinducing (sigmaEval X Y) where
  eq_coinduced :=
    (generatedBy_eq (X := X) (Y := Y)).symm.trans <|
      (TopologicalSpace.generatedBy_eq_coinduced X).trans <| by
        rw [sigmaEval_def]

/-- When at least one test space `X i` is nonempty, `sigmaEval X Y` is surjective, since every
point of `Y` is hit by a constant map from that test space. -/
theorem surjective_sigmaEval (Y : Type v) [TopologicalSpace Y] (hX : ∃ i, Nonempty (X i)) :
    Function.Surjective (sigmaEval X Y) := by
  obtain ⟨i₀, ⟨x₀⟩⟩ := hX
  exact fun y ↦ ⟨⟨⟨i₀, ContinuousMap.const (X i₀) y⟩, x₀⟩, rfl⟩

/-- When at least one test space `X i` is nonempty and `Y` is `X`-generated, `sigmaEval X Y` is a
quotient map. -/
theorem isQuotientMap_sigmaEval (Y : Type v) [TopologicalSpace Y] [IsGeneratedBy X Y]
    (hX : ∃ i, Nonempty (X i)) :
    IsQuotientMap (sigmaEval X Y) :=
  ⟨isCoinducing_sigmaEval X Y, surjective_sigmaEval X Y hX⟩

/-- When every test space `X i` is empty, every `X`-generated space carries the discrete topology,
because the preimage of any set along a map from an empty space is empty and hence open. -/
theorem discreteTopology_of_forall_isEmpty {Y : Type v} [TopologicalSpace Y] [IsGeneratedBy X Y]
    (hX : ∀ i, IsEmpty (X i)) :
    DiscreteTopology Y := by
  rw [discreteTopology_iff_forall_isOpen]
  intro U
  rw [isOpen_iff X]
  intro i f
  have := hX i
  rw [Set.eq_empty_of_isEmpty (f ⁻¹' U)]
  exact isOpen_empty

variable {X}

/-- **Whitehead product theorem for generated spaces (left locally compact factor).**
Suppose every test space `X i` is locally compact and every pairwise product `X i × X j` is
`X`-generated. If `Y` and `Z` are `X`-generated and `Y` is locally compact, then the ordinary
product `Y × Z` is `X`-generated. -/
theorem prod_of_locallyCompactSpace_left
    [∀ i, LocallyCompactSpace (X i)] [∀ i j, IsGeneratedBy X (X i × X j)]
    {Y : Type v} [TopologicalSpace Y] [IsGeneratedBy X Y] [LocallyCompactSpace Y]
    {Z : Type v'} [TopologicalSpace Z] [IsGeneratedBy X Z] :
    IsGeneratedBy X (Y × Z) := by
  by_cases hX : ∃ i, Nonempty (X i)
  · constructor
    have htest : ∀ (i : ι) (f : C(X i, Y)) (j : ι) (g : C(X j, Z)),
        Continuous (fun p : X i × X j ↦
          (WithGeneratedByTopology.equiv (X := X) (Y := Y × Z)).symm (f p.1, g p.2)) := by
      intro i f j g
      rw [continuous_iff X]
      intro k r
      have hfg : Continuous (fun p : X i × X j ↦ (f p.1, g p.2)) := by fun_prop
      exact (equiv_symm_comp_continuous_iff X
        (fun w : X k ↦ (f (r w).1, g (r w).2))).2 (hfg.comp r.continuous)
    have hmid : ∀ (j : ι) (g : C(X j, Z)),
        Continuous (fun p : Y × X j ↦
          (WithGeneratedByTopology.equiv (X := X) (Y := Y × Z)).symm (p.1, g p.2)) := by
      intro j g
      refine (isQuotientMap_sigmaEval X Y hX).continuous_lift_prod_left ?_
      refine Homeomorph.sigmaProdDistrib.symm.isQuotientMap.continuous_iff.2 ?_
      exact continuous_sigma fun ⟨i, f⟩ ↦ htest i f j g
    refine (isQuotientMap_sigmaEval X Z hX).continuous_lift_prod_right ?_
    let e : Y × ((p : (j : ι) × C(X j, Z)) × X p.1) ≃ₜ
        (p : (j : ι) × C(X j, Z)) × X p.1 × Y :=
      (Homeomorph.prodComm _ _).trans Homeomorph.sigmaProdDistrib
    refine e.symm.isQuotientMap.continuous_iff.2 ?_
    exact continuous_sigma fun ⟨j, g⟩ ↦ (hmid j g).comp continuous_swap
  · push Not at hX
    have : DiscreteTopology Y := discreteTopology_of_forall_isEmpty X hX
    have : DiscreteTopology Z := discreteTopology_of_forall_isEmpty X hX
    refine iff_le_generatedBy.2 ?_
    rw [DiscreteTopology.eq_bot (α := Y × Z)]
    exact bot_le

/-- **Whitehead product theorem for generated spaces (right locally compact factor).**
Suppose every test space `X i` is locally compact and every pairwise product `X i × X j` is
`X`-generated. If `Y` and `Z` are `X`-generated and `Z` is locally compact, then the ordinary
product `Y × Z` is `X`-generated. -/
theorem prod_of_locallyCompactSpace_right
    [∀ i, LocallyCompactSpace (X i)] [∀ i j, IsGeneratedBy X (X i × X j)]
    {Y : Type v} [TopologicalSpace Y] [IsGeneratedBy X Y]
    {Z : Type v'} [TopologicalSpace Z] [IsGeneratedBy X Z] [LocallyCompactSpace Z] :
    IsGeneratedBy X (Y × Z) := by
  have : IsGeneratedBy X (Z × Y) := prod_of_locallyCompactSpace_left (X := X)
  exact (Homeomorph.prodComm Z Y).isQuotientMap.isGeneratedBy

end Topology.IsGeneratedBy

namespace Topology.WithGeneratedByTopology

/-- Refining a Hausdorff space `Y` to its `X`-generated topology preserves `T2Space`, since the
counit bijection `WithGeneratedByTopology X Y → Y` is continuous and injective. -/
instance instT2Space {Y : Type v} [TopologicalSpace Y] [T2Space Y] :
    T2Space (WithGeneratedByTopology X Y) :=
  .of_injective_continuous (equiv (X := X) (Y := Y)).injective
    (continuous_equiv (X := X) (Y := Y))

variable [∀ i, LocallyCompactSpace (X i)] [∀ i j, IsGeneratedBy X (X i × X j)]

/-- When `Y` and `Z` are `X`-generated and `Y` is locally compact, the counit refines `Y × Z` by a
homeomorphism `WithGeneratedByTopology X (Y × Z) ≃ₜ Y × Z`. -/
def prodHomeomorphOfLocallyCompactLeft
    (Y : Type v) [TopologicalSpace Y] [IsGeneratedBy X Y] [LocallyCompactSpace Y]
    (Z : Type v') [TopologicalSpace Z] [IsGeneratedBy X Z] :
    WithGeneratedByTopology X (Y × Z) ≃ₜ Y × Z :=
  have : IsGeneratedBy X (Y × Z) := IsGeneratedBy.prod_of_locallyCompactSpace_left
  IsGeneratedBy.homeomorph

@[simp]
theorem prodHomeomorphOfLocallyCompactLeft_apply
    {Y : Type v} [TopologicalSpace Y] [IsGeneratedBy X Y] [LocallyCompactSpace Y]
    {Z : Type v'} [TopologicalSpace Z] [IsGeneratedBy X Z]
    (p : WithGeneratedByTopology X (Y × Z)) :
    prodHomeomorphOfLocallyCompactLeft X Y Z p = equiv p :=
  (rfl)

@[simp]
theorem prodHomeomorphOfLocallyCompactLeft_symm_apply
    {Y : Type v} [TopologicalSpace Y] [IsGeneratedBy X Y] [LocallyCompactSpace Y]
    {Z : Type v'} [TopologicalSpace Z] [IsGeneratedBy X Z]
    (p : Y × Z) :
    (prodHomeomorphOfLocallyCompactLeft X Y Z).symm p = equiv.symm p :=
  (rfl)

/-- When `Y` and `Z` are `X`-generated and `Z` is locally compact, the counit refines `Y × Z` by a
homeomorphism `WithGeneratedByTopology X (Y × Z) ≃ₜ Y × Z`. -/
def prodHomeomorphOfLocallyCompactRight
    (Y : Type v) [TopologicalSpace Y] [IsGeneratedBy X Y]
    (Z : Type v') [TopologicalSpace Z] [IsGeneratedBy X Z] [LocallyCompactSpace Z] :
    WithGeneratedByTopology X (Y × Z) ≃ₜ Y × Z :=
  have : IsGeneratedBy X (Y × Z) := IsGeneratedBy.prod_of_locallyCompactSpace_right
  IsGeneratedBy.homeomorph

@[simp]
theorem prodHomeomorphOfLocallyCompactRight_apply
    {Y : Type v} [TopologicalSpace Y] [IsGeneratedBy X Y]
    {Z : Type v'} [TopologicalSpace Z] [IsGeneratedBy X Z] [LocallyCompactSpace Z]
    (p : WithGeneratedByTopology X (Y × Z)) :
    prodHomeomorphOfLocallyCompactRight X Y Z p = equiv p :=
  (rfl)

@[simp]
theorem prodHomeomorphOfLocallyCompactRight_symm_apply
    {Y : Type v} [TopologicalSpace Y] [IsGeneratedBy X Y]
    {Z : Type v'} [TopologicalSpace Z] [IsGeneratedBy X Z] [LocallyCompactSpace Z]
    (p : Y × Z) :
    (prodHomeomorphOfLocallyCompactRight X Y Z).symm p = equiv.symm p :=
  (rfl)

end Topology.WithGeneratedByTopology

end Product

section HomSpace

variable {ι : Type t} {X : ι → Type u} [∀ i, TopologicalSpace (X i)]
  {Y : Type v} [TopologicalSpace Y] {T : Type v''} [TopologicalSpace T]

namespace ContinuousMap

/-- View an ordinary continuous map `f : C(Y, T)` as an `X`-continuous map. -/
def toContinuousMapGeneratedBy (f : C(Y, T)) (X : ι → Type u) [∀ i, TopologicalSpace (X i)] :
    Topology.ContinuousMapGeneratedBy X Y T where
  toFun := f
  prop := f.continuous.continuousGeneratedBy

@[simp]
theorem toContinuousMapGeneratedBy_apply (f : C(Y, T)) (y : Y) :
    f.toContinuousMapGeneratedBy X y = f y :=
  (rfl)

/-- The canonical inclusion from the compact-open mapping space `C(Y, T)` into
`ContinuousMapGeneratedBy X Y T` is continuous, because precomposition with every continuous map
`X i → Y` is continuous for the compact-open topology. -/
@[continuity, fun_prop]
theorem continuous_toContinuousMapGeneratedBy :
    Continuous (fun f : C(Y, T) ↦ f.toContinuousMapGeneratedBy X) :=
  Topology.ContinuousMapGeneratedBy.continuous_iff.2 fun _ g ↦ ContinuousMap.continuous_precomp g

end ContinuousMap

namespace Topology.ContinuousMapGeneratedBy

/-- When `Y` is `X`-generated, every `X`-continuous map `Y → T` is genuinely continuous. -/
def toContinuousMap [IsGeneratedBy X Y] (g : ContinuousMapGeneratedBy X Y T) : C(Y, T) where
  toFun := g
  continuous_toFun := (IsGeneratedBy.continuous_iff X g).2 g.prop

@[simp]
theorem toContinuousMap_apply [IsGeneratedBy X Y] (g : ContinuousMapGeneratedBy X Y T) (y : Y) :
    g.toContinuousMap y = g y :=
  (rfl)

/-- When `Y` is `X`-generated, `ContinuousMapGeneratedBy X Y T` has the exact same elements as
`C(Y, T)`. -/
def equivContinuousMap [IsGeneratedBy X Y] :
    ContinuousMapGeneratedBy X Y T ≃ C(Y, T) where
  toFun := toContinuousMap
  invFun f := f.toContinuousMapGeneratedBy X
  left_inv _ := by ext; rfl
  right_inv _ := by ext; rfl

@[simp]
theorem equivContinuousMap_apply [IsGeneratedBy X Y]
    (g : ContinuousMapGeneratedBy X Y T) :
    equivContinuousMap g = g.toContinuousMap :=
  (rfl)

@[simp]
theorem equivContinuousMap_symm_apply [IsGeneratedBy X Y] (f : C(Y, T)) :
    (equivContinuousMap (X := X)).symm f = f.toContinuousMapGeneratedBy X :=
  (rfl)

/-- When every test space `X i` is locally compact, pairwise products `X i × X j` are
`X`-generated, and the source `Y` is `X`-generated, a test map from `X i` into
`ContinuousMapGeneratedBy X Y T` is continuous if and only if the corresponding map into the
compact-open space `C(Y, T)` is continuous. Consequently their `X`-generated refinements are
homeomorphic, with no local compactness or Hausdorffness assumption on `Y`. -/
def generatedByHomeomorphContinuousMap
    [∀ i, LocallyCompactSpace (X i)] [∀ i j, IsGeneratedBy X (X i × X j)]
    [IsGeneratedBy X Y] :
    WithGeneratedByTopology X (ContinuousMapGeneratedBy X Y T) ≃ₜ
      WithGeneratedByTopology X C(Y, T) where
  toEquiv :=
    WithGeneratedByTopology.equiv.trans
      (equivContinuousMap.trans WithGeneratedByTopology.equiv.symm)
  continuous_toFun := by
    rw [WithGeneratedByTopology.continuous_from_iff]
    intro i f
    simp only [Equiv.toFun_as_coe, Equiv.coe_trans, Function.comp_def, Equiv.apply_symm_apply]
    refine (IsGeneratedBy.equiv_symm_comp_continuous_iff X
      (fun x : X i ↦ equivContinuousMap (f x))).2 ?_
    have hf : ContinuousGeneratedBy X (f : X i → ContinuousMapGeneratedBy X Y T) :=
      f.continuous.continuousGeneratedBy
    rw [continuousGeneratedBy_iff_uncurry] at hf
    have : IsGeneratedBy X (X i × Y) := IsGeneratedBy.prod_of_locallyCompactSpace_left
    have hunc : Continuous (fun p : X i × Y ↦ f p.1 p.2) := by
      rw [IsGeneratedBy.continuous_iff X]
      intro k r
      have hprod := hf (ContinuousMap.fst.comp r) (ContinuousMap.snd.comp r)
      exact hprod.comp (continuous_id.prodMk continuous_id)
    exact (ContinuousMap.curry ⟨_, hunc⟩).continuous
  continuous_invFun := by
    rw [WithGeneratedByTopology.continuous_from_iff]
    intro i f
    simp only [Equiv.invFun_as_coe, Equiv.symm_trans_apply, Equiv.symm_symm, Function.comp_def,
      Equiv.apply_symm_apply]
    refine (IsGeneratedBy.equiv_symm_comp_continuous_iff X
      (fun x : X i ↦ (equivContinuousMap (X := X)).symm (f x))).2 ?_
    exact ContinuousMap.continuous_toContinuousMapGeneratedBy.comp f.continuous

@[simp]
theorem generatedByHomeomorphContinuousMap_apply
    [∀ i, LocallyCompactSpace (X i)] [∀ i j, IsGeneratedBy X (X i × X j)]
    [IsGeneratedBy X Y]
    (g : WithGeneratedByTopology X (ContinuousMapGeneratedBy X Y T)) :
    WithGeneratedByTopology.equiv (generatedByHomeomorphContinuousMap g) =
      (WithGeneratedByTopology.equiv g).toContinuousMap :=
  (rfl)

@[simp]
theorem generatedByHomeomorphContinuousMap_symm_apply
    [∀ i, LocallyCompactSpace (X i)] [∀ i j, IsGeneratedBy X (X i × X j)]
    [IsGeneratedBy X Y]
    (f : WithGeneratedByTopology X C(Y, T)) :
    WithGeneratedByTopology.equiv (generatedByHomeomorphContinuousMap.symm f) =
      (WithGeneratedByTopology.equiv f).toContinuousMapGeneratedBy X :=
  (rfl)

end Topology.ContinuousMapGeneratedBy

end HomSpace
