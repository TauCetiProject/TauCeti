/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.TamelyRamified.BaseChange
public import Mathlib.FieldTheory.Normal.Closure
import TauCeti.RingTheory.Valuation.ValuativeRel.Basic

/-!
# Tame ramification of normal closures

The normal closure of a finite tamely ramified extension of nonarchimedean local fields is
again tamely ramified. This permits testing tame ramification in a normal extension without
requiring the original extension to be Galois. The normal closure may carry any compatible
local-field structures extending the base; the ambient field needs no valuation or topology.

Mathlib's `IntermediateField.normalClosure` is the compositum of the images of all embeddings
of the extension. There are finitely many such embeddings, and tameness is preserved by
embeddings and finite composita.

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

/-- The normal closure of a tamely ramified finite extension is tamely ramified, for any
compatible local-field structures over the base. The ambient field need not be normal,
algebraically closed, or valued. -/
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
  have hbot : P ⊥ := by
    dsimp only [P]
    have hef := ramificationIndex_mul_inertiaDegree K (⊥ : IntermediateField K N)
    rw [IntermediateField.finrank_bot] at hef
    rw [isTamelyRamified_iff, (mul_eq_one.mp hef).1]
    exact (CharP.prime_ringChar 𝓀[K]).not_dvd_one
  have hsup (E F : IntermediateField K N) (hE : P E) (hF : P F) : P (E ⊔ F) := by
    exact isTamelyRamified_sup_iff.2 ⟨hE, hF⟩
  have hrange (f : L →ₐ[K] N) : P f.fieldRange := by
    let g := f.equivFieldRange.toAlgHom
    have hg : Function.Surjective g := f.equivFieldRange.surjective
    exact hL.of_adjoin_range_eq_top g (by rw [Set.range_eq_univ.2 hg, adjoin_univ])
  let _ := Fintype.ofFinite (L →ₐ[K] N)
  have htop : (Finset.univ.sup fun f : L →ₐ[K] N ↦ f.fieldRange) = ⊤ := by
    apply IntermediateField.lift_injective
    simp only [Finset.sup_eq_iSup, Finset.mem_univ, iSup_true, IntermediateField.lift,
      IntermediateField.map_iSup, AlgHom.map_fieldRange, ← AlgHom.fieldRange_eq_map,
      IntermediateField.fieldRange_val]
    exact (normalClosure.algHomEquiv K L Ω).iSup_comp.trans
      (normalClosure_def K L Ω).symm
  have hPt : P ⊤ := htop ▸ Finset.sup_induction hbot (fun E hE F hF ↦ hsup E F hE hF)
    (fun f _ ↦ hrange f)
  -- Base change along the surjective top-field equivalence transports the tame compositum to `N`.
  let g := (topEquiv : (⊤ : IntermediateField K N) ≃ₐ[K] N).toAlgHom
  have hg : Function.Surjective g := topEquiv.surjective
  exact hPt.of_adjoin_range_eq_top g (by rw [Set.range_eq_univ.2 hg, adjoin_univ])

end TauCeti
