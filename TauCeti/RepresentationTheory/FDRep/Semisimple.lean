/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Semisimple.Finrank
public import TauCeti.RepresentationTheory.Maschke
public import TauCeti.RepresentationTheory.Simple.Basic
import Mathlib.Algebra.BigOperators.Fin
import TauCeti.Algebra.Category.ModuleCat.Finrank
import TauCeti.RepresentationTheory.FDRep.Basic

/-!
# Semisimple decompositions in `FDRep`

When the order of `G` is nonzero in an algebraically closed field `k`, `FDRep k G` is a split
finite semisimple category (`TauCeti.FDRep.instIsFiniteSemisimpleCategory`). Every
`W : FDRep k G` decomposes as a finite biproduct of simple objects, each occurring with multiplicity
`TauCeti.finrank_hom_simple_eq_simpleMultiplicities`, so the dimension of `W` is the sum over simple
isomorphism classes `S : TauCeti.SimpleClasses (FDRep k G)` of `S.finrankHom W * S.finrank`
(`FDRep.finrank_eq_sum_finrankHom_mul_finrank`).

## Main results

* `FDRep.finrank_eq_sum_finrankHom_mul_finrank`: dimension decomposition of an object of
  `FDRep k G` over `TauCeti.SimpleClasses (FDRep k G)`.
-/

public section

open CategoryTheory CategoryTheory.Limits TauCeti

universe u v

namespace FDRep

private theorem finrank_biproduct {k : Type u} {G : Type v} [Field k] [Monoid G]
    {ι : Type} [Fintype ι] (f : ι → FDRep k G) [HasBiproduct f] :
    Module.finrank k (⨁ f : FDRep k G) = ∑ i : ι, Module.finrank k (f i) := by
  let F : FDRep k G ⥤ ModuleCat.{u} k := Action.forget (FGModuleCat.{u} k) G ⋙ ObjectProperty.ι _
  have : PreservesFiniteBiproducts (Action.forget (FGModuleCat.{u} k) G) := inferInstance
  have : PreservesFiniteBiproducts (ObjectProperty.ι (ModuleCat.isFG.{u} k)) := inferInstance
  have : ∀ i, Module.Finite k ((F.obj ∘ f) i) := fun i ↦ (f i).V.property
  change Module.finrank k (F.obj (⨁ f)) = ∑ i : ι, Module.finrank k (f i)
  rw [(F.mapBiproduct f).toLinearEquiv.finrank_eq, ModuleCat.finrank_biproduct (F.obj ∘ f)]
  rfl

/-- **Dimension decomposition into simple classes.** For a finite group `G` over an algebraically
closed field `k` in which `|G|` is nonzero, every `W : FDRep k G` has dimension
`∑ S, S.finrankHom W * S.finrank`. -/
theorem finrank_eq_sum_finrankHom_mul_finrank {k : Type u} {G : Type v} [Field k] [IsAlgClosed k]
    [Group G] [NeZero (Nat.card G : k)] [Fintype (SimpleClasses (FDRep k G))] (W : FDRep k G) :
    Module.finrank k W = ∑ S : SimpleClasses (FDRep k G), S.finrankHom W * S.finrank := by
  classical
  obtain ⟨ι, hι, f, hf, hbf, ⟨e⟩⟩ := IsFiniteSemisimpleCategory.exists_biproduct_simples W
  let := hι
  let := hf
  let := hbf
  rw [(FDRep.isoToLinearEquiv e).finrank_eq, finrank_biproduct f]
  have hsum : ∑ i : ι, Module.finrank k (f i) =
      ∑ i : ι, (SimpleClasses.classOf (f i)).finrank :=
    Finset.sum_congr rfl fun i _ ↦ (SimpleClasses.finrank_classOf (f i)).symm
  rw [hsum, ← Finset.sum_fiberwise (Finset.univ : Finset ι) fun i ↦ SimpleClasses.classOf (f i)]
  refine Finset.sum_congr rfl fun S _ ↦ ?_
  rw [Finset.sum_congr rfl fun i hi ↦ congrArg SimpleClasses.finrank (Finset.mem_filter.mp hi).2,
    Finset.sum_const, smul_eq_mul]
  have hcard : (Finset.univ.filter fun i : ι ↦ SimpleClasses.classOf (f i) = S).card =
      S.finrankHom W := by
    rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card,
      ← simpleMultiplicities_apply_eq_card f e S, ← SimpleClasses.classOf_repr S,
      ← finrank_hom_simple_eq_simpleMultiplicities k S.repr W, SimpleClasses.finrankHom_classOf]
  rw [hcard]

end FDRep
