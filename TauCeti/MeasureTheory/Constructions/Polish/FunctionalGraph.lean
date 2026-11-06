/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Data.Set.Graph
public import TauCeti.MeasureTheory.Constructions.Polish.Graph

/-!
# Evaluating functional Borel graphs

A Borel set `G ⊆ X × Y` in a product of standard Borel spaces, with at most one point over each
`x`, defines a measurable function on its domain. The function is `Set.InjOn.graphValue`, and
`Set.InjOn.measurable_graphValue` proves its measurability. Its membership and uniqueness laws
are available without any measurable-space assumptions in `TauCeti.Data.Set.Graph`.

`MeasurableSet.graphDomainEquiv` identifies `G` measurably with its domain `Prod.fst '' G` by
the first projection; the inverse sends `x` to `(x, graphValue x)`. Neither construction
requires the graph or the target to be nonempty. The domain is Borel by Lusin–Souslin, as
expressed by `MeasurableSet.image_of_measurable_injOn` applied to `Prod.fst`.

## References

* A. S. Kechris, *Classical Descriptive Set Theory*, Springer, 1995, Theorem 15.1
  (Lusin–Souslin). The projection embedding used here is proved in
  `TauCeti.MeasureTheory.Constructions.Polish.Graph`.
-/

public section

open Set Function

variable {X Y : Type*} [MeasurableSpace X] [StandardBorelSpace X]
  [MeasurableSpace Y] [StandardBorelSpace Y] {G : Set (X × Y)}

/-- The function defined by a functional Borel graph is measurable on its domain. -/
@[fun_prop]
theorem Set.InjOn.measurable_graphValue (hinj : InjOn Prod.fst G) (hG : MeasurableSet G) :
    Measurable hinj.graphValue := by
  have hm : Measurable (fun x : Prod.fst '' G ↦ ((x : X), hinj.graphValue x)) :=
    (hG.measurable_iff_measurable_fst hinj hinj.graphValue_mem).2 measurable_subtype_coe
  exact hm.snd

/-- First projection identifies a functional Borel graph measurably with its domain. -/
noncomputable def MeasurableSet.graphDomainEquiv (hG : MeasurableSet G)
    (hinj : InjOn Prod.fst G) : G ≃ᵐ (Prod.fst '' G) where
  toEquiv := hinj.bijOn_image.equiv Prod.fst
  measurable_toFun := (measurable_fst.comp measurable_subtype_coe).subtype_mk
  measurable_invFun := by
    let e := hinj.bijOn_image.equiv Prod.fst
    apply Measurable.subtype_mk
    apply (hG.measurable_iff_measurable_fst hinj (fun x ↦ (e.symm x).property)).2
    have heq : (fun x ↦ (e.symm x).val.1) = fun x : Prod.fst '' G ↦ (x : X) :=
      funext fun x ↦ congrArg Subtype.val (e.apply_symm_apply x)
    rw [heq]
    exact measurable_subtype_coe

/-- The domain equivalence is the first projection. -/
@[simp]
theorem MeasurableSet.graphDomainEquiv_apply (hG : MeasurableSet G)
    (hinj : InjOn Prod.fst G) (p : G) :
    hG.graphDomainEquiv hinj p = ⟨p.val.1, mem_image_of_mem Prod.fst p.property⟩ := (rfl)

/-- The inverse of the domain equivalence evaluates the function defined by the graph. -/
@[simp]
theorem MeasurableSet.graphDomainEquiv_symm_apply (hG : MeasurableSet G)
    (hinj : InjOn Prod.fst G) (x : Prod.fst '' G) :
    (hG.graphDomainEquiv hinj).symm x = ⟨((x : X), hinj.graphValue x), hinj.graphValue_mem x⟩ := by
  apply Subtype.ext
  apply hinj (Subtype.mem _) (hinj.graphValue_mem x)
  exact congrArg (fun y : Prod.fst '' G ↦ (y : X)) ((hG.graphDomainEquiv hinj).apply_symm_apply x)
