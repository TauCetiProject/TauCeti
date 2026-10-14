/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.TamelyRamified.BaseChange
public import TauCeti.FieldTheory.Normal.Closure

/-!
# Tame ramification of normal closures

For a finite tamely ramified extension `L/K` of nonarchimedean local fields, Mathlib's
`IntermediateField.normalClosure K L Ω`, the compositum of all `K`-embedding images of `L` in
`Ω`, is tamely ramified. It may carry any compatible local-field structures extending the
base; the ambient field needs no valuation or topology.

When `Ω/K` is normal and admits a `K`-embedding of `L`, this compositum is a normal closure
in the sense of `IsNormalClosure`. In particular, taking `Ω` to be an algebraic closure proves
that the usual normal closure is tame, permitting tame ramification to be tested in a normal
extension without requiring `L/K` to be Galois. For an arbitrary ambient field the result
still applies to the compositum of its embedding images; if there are no embeddings, that
compositum is the degree-one extension `⊥`.

## References

* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter IV, §2.
* J. Neukirch, *Algebraic Number Theory*, Chapter II, §7.
-/

public section
noncomputable section

open IntermediateField ValuativeRel

namespace TauCeti

variable {K L Ω : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L]
  [Field Ω] [Algebra K Ω]
  [ValuativeRel (normalClosure K L Ω)] [TopologicalSpace (normalClosure K L Ω)]
  [IsNonarchimedeanLocalField (normalClosure K L Ω)]
  [ValuativeExtension K (normalClosure K L Ω)]

/-- The compositum of all `K`-embedding images of a tamely ramified finite extension `L/K` in
`Ω` is tamely ramified, for any compatible local-field structures over the base. If `Ω/K` is
normal and admits such an embedding, this is a normal closure of `L/K` in the sense of
`IsNormalClosure`; otherwise it is Mathlib's embedding-image compositum (possibly `⊥`). -/
theorem IsTamelyRamified.normalClosure (hL : IsTamelyRamified K L) :
    IsTamelyRamified K (IntermediateField.normalClosure K L Ω) := by
  have := finite_of_valuativeExtension K L
  let N := IntermediateField.normalClosure K L Ω
  -- Each intermediate field of the finite extension `N/K` has canonical local-field structures.
  let (E : IntermediateField K N) : ValuativeRel E :=
    finiteIntermediateFieldValuativeRel K N E
  let (E : IntermediateField K N) : TopologicalSpace E :=
    finiteIntermediateFieldTopology K N E
  let (E : IntermediateField K N) : IsNonarchimedeanLocalField E :=
    finiteIntermediateField_isNonarchimedeanLocalField K N E
  let (E : IntermediateField K N) : ValuativeExtension K E :=
    finiteIntermediateField_valuativeExtension K N E
  let P (E : IntermediateField K N) : Prop := IsTamelyRamified K E
  have hbot : P ⊥ := isTamelyRamified_of_finrank_eq_one IntermediateField.finrank_bot
  have hsup (E F : IntermediateField K N) (hE : P E) (hF : P F) : P (E ⊔ F) := by
    exact isTamelyRamified_sup_iff.2 ⟨hE, hF⟩
  have hrange (f : L →ₐ[K] N) : P f.fieldRange := hL.of_algEquiv f.equivFieldRange
  let _ := Fintype.ofFinite (L →ₐ[K] N)
  have htop : (Finset.univ.sup fun f : L →ₐ[K] N ↦ f.fieldRange) = ⊤ := by
    simpa only [Finset.sup_eq_iSup, Finset.mem_univ, iSup_true] using
      normalClosure_iSup_fieldRange_eq_top K L Ω
  have hPt : P ⊤ := htop ▸ Finset.sup_induction hbot (fun E hE F hF ↦ hsup E F hE hF)
    (fun f _ ↦ hrange f)
  exact hPt.of_algEquiv topEquiv

end TauCeti
