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
identify a vector with each of its re-expansions. Every element comes from a stage, and
compatible linear maps from the stages extend uniquely by `lift` and `hom_ext`.

When multiplication by `p` on `E` is injective, `ofStage_injective` makes each stage a
submodule of this direct limit. The carrier and universal property also make sense for
torsion coefficients, where distinct vectors can become equal after re-expansion.

Evaluation descends to a linear map into continuous functions, with range equal to the
union of the stage evaluation images. This is a range statement: evaluation injectivity,
and hence an identification of the direct limit with that union, requires a separate proof.
No topology is put on the algebraic direct limit here.
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

/-- Every algebraic locally analytic vector is represented at a finite stage. -/
theorem exists_ofStage (z : LocallyAnalytic p S E) :
    ∃ h c, ofStage S h c = z := Module.DirectLimit.exists_of z

variable {F : Type*} [AddCommMonoid F] [Module S F]

/-- Compatible linear maps from all stages induce a linear map out of their direct limit. -/
noncomputable def lift (g : ∀ h, AnalyticStage p h E →ₗ[S] F)
    (hg : ∀ h k hhk c, g k (AnalyticStage.transitionLE S hhk c) = g h c) :
    LocallyAnalytic p S E →ₗ[S] F :=
  Module.DirectLimit.lift S ℕ _ _ g hg

/-- The induced linear map agrees with the specified map on each stage. -/
@[simp]
theorem lift_ofStage (g : ∀ h, AnalyticStage p h E →ₗ[S] F)
    (hg : ∀ h k hhk c, g k (AnalyticStage.transitionLE S hhk c) = g h c)
    (h : ℕ) (c : AnalyticStage p h E) :
    lift S g hg (ofStage S h c) = g h c := Module.DirectLimit.lift_of g hg c

/-- Linear maps from the direct limit are determined by their restrictions to the stages. -/
@[ext]
theorem hom_ext {f g : LocallyAnalytic p S E →ₗ[S] F}
    (h : ∀ k, f.comp (ofStage S k) = g.comp (ofStage S k)) : f = g :=
  Module.DirectLimit.hom_ext h

/-- With p-regular coefficients, each stage maps faithfully into the algebraic direct limit. -/
theorem ofStage_injective (hpE : IsSMulRegular E (p : ℤ_[p])) (h : ℕ) :
    Function.Injective (ofStage (p := p) (E := E) S h) := by
  intro c d hcd
  obtain ⟨k, hhk, hcd⟩ := Module.DirectLimit.exists_eq_of_of_eq hcd
  exact AnalyticStage.transitionLE_injective S hpE hhk hcd

/-- Stage evaluation descends to the algebraic direct limit. -/
noncomputable def eval : LocallyAnalytic p S E →ₗ[S] C(ℤ_[p], E) :=
  lift S (fun _ ↦ (AnalyticStage.eval S).toLinearMap)
    (fun _ _ hhk c ↦ AnalyticStage.eval_transitionLE S hhk c)

/-- Direct-limit evaluation restricts to evaluation at every analytic stage. -/
@[simp]
theorem eval_ofStage (h : ℕ) (c : AnalyticStage p h E) :
    eval S (ofStage S h c) = AnalyticStage.eval S c := lift_ofStage S _ _ h c

/-- The evaluation range is exactly the union of the stage evaluation images, without an
injectivity assertion. -/
theorem range_eval :
    Set.range (eval (p := p) (E := E) S) =
      ⋃ h, Set.range (AnalyticStage.eval (p := p) (h := h) (E := E) S) := by
  ext f
  constructor
  · rintro ⟨z, rfl⟩
    obtain ⟨h, c, rfl⟩ := exists_ofStage S z
    exact Set.mem_iUnion.mpr ⟨h, c, (eval_ofStage S h c).symm⟩
  · intro hf
    obtain ⟨h, c, rfl⟩ := Set.mem_iUnion.mp hf
    exact ⟨ofStage S h c, eval_ofStage S h c⟩

end LocallyAnalytic

end TauCeti
