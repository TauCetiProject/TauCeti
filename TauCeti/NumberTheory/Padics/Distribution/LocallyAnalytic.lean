/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Colimit.Module
public import TauCeti.NumberTheory.Padics.Distribution.AnalyticStage

/-!
# The algebraic direct limit of analytic stages

`TauCeti.LocallyAnalytic p S E` is Mathlib's native `Module.DirectLimit` of the analytic
coefficient stages along `AnalyticStage.transitionLE S`. Its canonical maps `ofStage S h`
identify a vector with each of its re-expansions. Mathlib's `Module.DirectLimit.exists_of`
gives a stage representative for every element. Compatible linear maps extend uniquely
by `Module.DirectLimit.lift` and `Module.DirectLimit.hom_ext`.
The equation `ofStage_def` connects the named stage maps with this native API without
unfolding their bodies.

When multiplication by `p` on `E` is injective, `ofStage_injective` makes each stage a
submodule of this direct limit. The carrier and universal property also make sense for
torsion coefficients, where distinct vectors can become equal after re-expansion.

Evaluation descends to a linear map into continuous functions, with range equal to the
union of the stage evaluation images. For p-regular coefficients, `eval_injective` makes this
a linear identification with that union. The equivalence is the native
`LinearEquiv.ofInjective (eval S) (eval_injective S hpE)`, whose target is the range submodule
described by `range_eval`. No topology is put on the algebraic direct limit here.
-/

public section

namespace TauCeti

variable {p : ℕ} [Fact p.Prime] {E : Type*} [NormedAddCommGroup E]
  [Module ℤ_[p] E] [IsBoundedSMul ℤ_[p] E] [IsUltrametricDist E] [CompleteSpace E]

variable (S : Type*) [Semiring S] [Module S E] [ContinuousConstSMul S E]
  [SMulCommClass ℤ_[p] S E]

/-- The algebraic direct limit of analytic coefficient stages under re-expansion. -/
abbrev LocallyAnalytic (p : ℕ) [Fact p.Prime] (S E : Type*) [Semiring S]
    [NormedAddCommGroup E] [Module ℤ_[p] E] [IsBoundedSMul ℤ_[p] E]
    [IsUltrametricDist E] [CompleteSpace E] [Module S E] [ContinuousConstSMul S E]
    [SMulCommClass ℤ_[p] S E] : Type _ :=
  Module.DirectLimit (fun h ↦ AnalyticStage p h E)
    (fun _ _ hhk ↦ (AnalyticStage.transitionLE S hhk).toLinearMap)

namespace LocallyAnalytic

/-- The canonical linear map from an analytic stage to the algebraic direct limit. -/
noncomputable def ofStage (h : ℕ) : AnalyticStage p h E →ₗ[S] LocallyAnalytic p S E :=
  Module.DirectLimit.of S ℕ (fun h ↦ AnalyticStage p h E)
    (fun _ _ hhk ↦ (AnalyticStage.transitionLE S hhk).toLinearMap) h

/-- The canonical stage map agrees with Mathlib's direct-limit constructor. -/
theorem ofStage_def (h : ℕ) :
    ofStage (p := p) (E := E) S h =
      Module.DirectLimit.of S ℕ (fun k ↦ AnalyticStage p k E)
        (fun _ _ hhk ↦ (AnalyticStage.transitionLE S hhk).toLinearMap) h := (rfl)

/-- A stage vector and its re-expansion define the same direct-limit element. -/
@[simp]
theorem ofStage_transitionLE {h k : ℕ} (hhk : h ≤ k) (c : AnalyticStage p h E) :
    ofStage S k (AnalyticStage.transitionLE S hhk c) = ofStage S h c :=
  Module.DirectLimit.of_f

/-- Adjacent re-expansion does not change a direct-limit element. -/
@[simp]
theorem ofStage_transition {h : ℕ} (c : AnalyticStage p h E) :
    ofStage S (h + 1) (AnalyticStage.transition S c) = ofStage S h c := by
  simpa using ofStage_transitionLE S (Nat.le_succ h) c

/-- With p-regular coefficients, each stage maps faithfully into the algebraic direct limit. -/
theorem ofStage_injective (hpE : IsSMulRegular E (p : ℤ_[p])) (h : ℕ) :
    Function.Injective (ofStage (p := p) (E := E) S h) := by
  intro c d hcd
  obtain ⟨k, hhk, hcd⟩ := Module.DirectLimit.exists_eq_of_of_eq hcd
  exact AnalyticStage.transitionLE_injective S hpE hhk hcd

/-- Stage evaluation descends to the algebraic direct limit. -/
noncomputable def eval : LocallyAnalytic p S E →ₗ[S] C(ℤ_[p], E) :=
  Module.DirectLimit.lift S ℕ _ _ (fun _ ↦ (AnalyticStage.eval S).toLinearMap)
    (fun _ _ hhk c ↦ AnalyticStage.eval_transitionLE S hhk c)

/-- Direct-limit evaluation restricts to evaluation at every analytic stage. -/
@[simp]
theorem eval_ofStage (h : ℕ) (c : AnalyticStage p h E) :
    eval S (ofStage S h c) = AnalyticStage.eval S c :=
  Module.DirectLimit.lift_of
    (fun k ↦ (AnalyticStage.eval (p := p) (h := k) (E := E) S).toLinearMap)
    (fun _ _ hhk c ↦ AnalyticStage.eval_transitionLE S hhk c) c

/-- Evaluation of the algebraic direct limit is injective when multiplication by `p` on
the coefficient module is injective. -/
theorem eval_injective (hpE : IsSMulRegular E (p : ℤ_[p])) :
    Function.Injective (eval (p := p) (E := E) S) :=
  Module.DirectLimit.lift_injective
    (fun h ↦ (AnalyticStage.eval (p := p) (h := h) (E := E) S).toLinearMap)
    (fun _ _ hhk c ↦ AnalyticStage.eval_transitionLE S hhk c)
    (fun h ↦ AnalyticStage.eval_injective (h := h) S hpE)

/-- The evaluation range is exactly the union of the stage evaluation images, without an
injectivity assertion. -/
theorem range_eval :
    Set.range (eval (p := p) (E := E) S) =
      ⋃ h, Set.range (AnalyticStage.eval (p := p) (h := h) (E := E) S) := by
  ext f
  constructor
  · rintro ⟨z, rfl⟩
    obtain ⟨h, c, rfl⟩ := Module.DirectLimit.exists_of z
    exact Set.mem_iUnion.mpr ⟨h, c, (eval_ofStage S h c).symm⟩
  · intro hf
    obtain ⟨h, c, rfl⟩ := Set.mem_iUnion.mp hf
    exact ⟨ofStage S h c, eval_ofStage S h c⟩

end LocallyAnalytic

end TauCeti
