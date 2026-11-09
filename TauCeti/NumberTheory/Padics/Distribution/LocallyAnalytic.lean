/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Colimit.Module
public import TauCeti.NumberTheory.Padics.Distribution.Polynomial

/-!
# The algebraic direct limit of analytic stages

`TauCeti.LocallyAnalytic p S E` is Mathlib's native `Module.DirectLimit` of the analytic
coefficient stages along `AnalyticStage.transitionLE S`. Its canonical maps `ofStage S h`
identify a vector with each of its re-expansions. Mathlib's `Module.DirectLimit.exists_of`
gives a stage representative for every element. Compatible linear maps extend uniquely
by `Module.DirectLimit.lift` and `Module.DirectLimit.hom_ext`; `lift_ofStage` reads the
extension on the named stage maps.
The equation `ofStage_def` connects the named stage maps with this native API without
unfolding their bodies.

When multiplication by `p` on `E` is injective, `ofStage_injective` makes each stage a
submodule of this direct limit. The carrier and universal property also make sense for
torsion coefficients, where distinct vectors can become equal after re-expansion.

Evaluation descends to a linear map into continuous functions, with range equal to the
union of the stage evaluation images. For p-regular coefficients, `eval_injective` makes this
a linear identification with that union. The equivalence is the native
`LinearEquiv.ofInjective (eval S) (eval_injective S hpE)`, whose target is the range submodule
described by `range_eval_eq_iSup`. Its stage formulas are `ofInjective_eval_ofStage` and
`ofInjective_eval_symm_apply`. No topology is put on the algebraic direct limit here.

The evaluated functions are dense in `C(ℤ_p, E)` (`denseRange_eval`): by uniform continuity, a
continuous function is uniformly close to the function equal to its value at `a` on each disc
`a + pʰℤ_p` of a small enough radius, and that step function is the evaluation of a coefficient
vector of degree zero at level `h`. Hence a continuous linear functional on `C(ℤ_p, E)` is
determined by its values on locally analytic functions.
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

/-- Mathlib's universal property of the direct limit, read on the named stage maps: the linear
map induced by a compatible family restricts to each member of the family. -/
@[simp]
theorem lift_ofStage {P : Type*} [AddCommMonoid P] [Module S P]
    (g : ∀ h, AnalyticStage p h E →ₗ[S] P)
    (hg : ∀ h k (hhk : h ≤ k) c, g k (AnalyticStage.transitionLE S hhk c) = g h c) (h : ℕ)
    (c : AnalyticStage p h E) :
    Module.DirectLimit.lift S ℕ (fun k ↦ AnalyticStage p k E)
      (fun _ _ hhk ↦ (AnalyticStage.transitionLE S hhk).toLinearMap) g hg (ofStage S h c) =
      g h c :=
  Module.DirectLimit.lift_of g hg c

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

/-- The native evaluation equivalence sends a stage class to its evaluated function. -/
@[simp]
theorem ofInjective_eval_ofStage (hpE : IsSMulRegular E (p : ℤ_[p])) {h : ℕ}
    (c : AnalyticStage p h E) :
    LinearEquiv.ofInjective (eval S) (eval_injective S hpE) (ofStage S h c) =
      ⟨AnalyticStage.eval S c, LinearMap.mem_range.mpr ⟨ofStage S h c, eval_ofStage S h c⟩⟩ := by
  ext
  simp

/-- The inverse evaluation equivalence sends a stage function to its stage class. -/
@[simp]
theorem ofInjective_eval_symm_apply (hpE : IsSMulRegular E (p : ℤ_[p])) {h : ℕ}
    (c : AnalyticStage p h E) (hc : AnalyticStage.eval S c ∈ (eval S).range) :
    (LinearEquiv.ofInjective (eval S) (eval_injective S hpE)).symm
      ⟨AnalyticStage.eval S c, hc⟩ = ofStage S h c := by
  apply eval_injective S hpE
  simp

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

/-- The evaluation range is the supremum of the stage evaluation submodules. -/
theorem range_eval_eq_iSup :
    LinearMap.range (eval (p := p) (E := E) S) =
      ⨆ h, LinearMap.range (AnalyticStage.eval (p := p) (h := h) (E := E) S).toLinearMap := by
  have hmono : Monotone (fun h ↦
      LinearMap.range (AnalyticStage.eval (p := p) (h := h) (E := E) S).toLinearMap) := by
    intro h k hhk f ⟨c, hc⟩
    exact ⟨AnalyticStage.transitionLE S hhk c, (AnalyticStage.eval_transitionLE S hhk c).trans hc⟩
  apply SetLike.coe_injective
  rw [Submodule.coe_iSup_of_directed _ hmono.directed_le]
  simpa only [LinearMap.coe_range, ContinuousLinearMap.coe_coe] using
    range_eval (p := p) (E := E) S

/-- Locally analytic functions are dense in the continuous functions. A continuous function is
uniformly approximated by the function equal to its value at `a.val` on each disc `a + pʰℤ_p`,
which is the evaluation of a coefficient vector of degree zero at level `h`. -/
theorem denseRange_eval : DenseRange (eval (p := p) (E := E) S) := by
  refine Metric.denseRange_iff.mpr fun f ε hε ↦ ?_
  obtain ⟨δ, hδ, hf⟩ := f.uniform_continuity ε hε
  obtain ⟨h, hh⟩ := exists_pow_lt_of_lt_one hδ (PadicInt.norm_p_lt_one (p := p))
  let c := (AnalyticStage.polynomialEquiv (p := p) (h := h) (E := E) S 0).symm
    fun i ↦ f (i.1.val : ℤ_[p])
  refine ⟨ofStage S h c.val, ?_⟩
  rw [eval_ofStage, ContinuousMap.dist_lt_iff hε]
  intro x
  have hx := PadicInt.natCast_val_toZModPow_add_mul_snd_discHomeomorph_symm h x
  set a := PadicInt.toZModPow h x
  set w := ((PadicInt.discHomeomorph p h).symm x).2
  have heval : AnalyticStage.eval S c.val x = f (a.val : ℤ_[p]) := by
    rw [← hx, AnalyticStage.eval_polynomial_natCast_val_add_mul]
    simp [c]
  rw [heval]
  apply hf
  rw [dist_eq_norm, ← hx, add_sub_cancel_left, norm_mul, norm_pow]
  exact (mul_le_of_le_one_right (by positivity) (PadicInt.norm_le_one w)).trans_lt hh

end LocallyAnalytic

end TauCeti
