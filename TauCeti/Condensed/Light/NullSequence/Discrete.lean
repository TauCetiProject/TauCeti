/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti contributors
-/
module

public import Mathlib.Condensed.Discrete.Module
public import Mathlib.Data.Finsupp.Defs
public import TauCeti.Condensed.Light.NullSequence.Basic

/-!
# Discrete coefficients of the marked null sequence

A locally constant section of the convergent sequence that vanishes at infinity
has finite support. Thus maps from the reduced free module into a discrete light
condensed module are finitely supported sequences of coefficients. The marked
shift acts on these coefficients by dropping the zeroth term.
-/

public section

open CategoryTheory LightCondensed OnePoint Filter
open scoped Topology

universe u

namespace TauCeti

variable {R : Type u} [Ring R] (M : ModuleCat.{u} R)

private noncomputable def discreteSectionsEquivFinsupp :
    {s : LocallyConstant liftedSequence.{u} M // s (ULift.up ∞) = 0} ≃ (ℕ →₀ M) := by
  letI : TopologicalSpace M := ⊥
  letI : DiscreteTopology M := ⟨rfl⟩
  refine
    { toFun := fun s ↦ Finsupp.ofSupportFinite (fun n ↦ s.val (ULift.up ↑n)) ?_
      invFun := fun b ↦ ⟨⟨fun x ↦ x.down.elim 0 b, ?_⟩, rfl⟩
      left_inv := ?_
      right_inv := ?_ }
  · have hcont : Continuous (fun x : OnePoint ℕ ↦ s.val (ULift.up x)) :=
      s.val.continuous.comp continuous_uliftUp
    have h := (OnePoint.continuous_iff_from_nat _).mp hcont
    rw [s.property, nhds_discrete, tendsto_pure, ← Nat.cofinite_eq_atTop] at h
    exact eventually_cofinite.mp h
  · apply (IsLocallyConstant.iff_continuous _).mpr
    have h : Continuous (fun x : OnePoint ℕ ↦ x.elim (0 : M) b) := by
      rw [OnePoint.continuous_iff_from_nat]
      simp only [OnePoint.elim_infty, nhds_discrete, tendsto_pure, ← Nat.cofinite_eq_atTop]
      exact eventually_cofinite.mpr b.hasFiniteSupport
    exact h.comp continuous_uliftDown
  · intro s
    apply Subtype.ext
    apply LocallyConstant.ext
    intro ⟨x⟩
    induction x using OnePoint.rec with
    | infty => exact s.property.symm
    | coe n => rfl
  · intro b
    ext n
    rfl

/-- Maps from the marked null sequence into the locally constant realization of a discrete
module are parametrized by the finitely supported coefficient sequences in that module. -/
noncomputable def nullSeqHomEquivFinsupp :
    (nullSeq R ⟶ (LightCondMod.LocallyConstant.functor R).obj M) ≃+ (ℕ →₀ M) := by
  let D := (LightCondMod.LocallyConstant.functor R).obj M
  let e : {s : LocallyConstant liftedSequence.{u} M // D.obj.map inftyPoint.op s = 0} ≃
      {s : LocallyConstant liftedSequence.{u} M // s (ULift.up ∞) = 0} :=
    Equiv.subtypeEquivRight fun s ↦ by
      have hval (x : LightProfinite.of PUnit.{u + 1}) :
          DFunLike.coe (F := LocallyConstant (LightProfinite.of PUnit.{u + 1}) M)
            (D.obj.map inftyPoint.op s) x =
            s (ULift.up ∞) :=
        congrArg s (inftyPoint_apply x)
      refine ⟨fun h ↦ ?_, fun h ↦ LocallyConstant.ext fun x ↦ (hval x).trans h⟩
      rw [← hval PUnit.unit, h]
      rfl
  let X := Under.mk inftyPoint.{u}
  let coeffs := (reducedLightFreeHomEquiv R X D).trans (e.trans (discreteSectionsEquivFinsupp M))
  refine { toEquiv := coeffs, map_add' := ?_ }
  intro g h
  ext n
  simp only [Finsupp.add_apply]
  let evaluate : (D.obj.obj (Opposite.op X.right)) → M :=
    fun s ↦ DFunLike.coe (F := LocallyConstant liftedSequence.{u} M) s (ULift.up ↑n)
  let q := (toReducedLightFree R).app X
  have heval (f : nullSeq R ⟶ D) : coeffs f n = evaluate (X.right.freeModuleHomEquiv (q ≫ f)) :=
    congrArg evaluate (reducedLightFreeHomEquiv_apply R X f)
  -- Expose function application of the equivalence for the coefficient formula.
  change coeffs (g + h) n = coeffs g n + coeffs h n
  rw [heval, heval g, heval h, Preadditive.comp_add, map_add]
  rfl

lemma nullSeqHomEquivFinsupp_apply
    (g : nullSeq R ⟶ (LightCondMod.LocallyConstant.functor R).obj M) (n : ℕ) :
    nullSeqHomEquivFinsupp M g n =
      DFunLike.coe (F := LocallyConstant liftedSequence.{u} M)
        (reducedLightFreeHomEquiv R (Under.mk inftyPoint.{u}) _ g).val
        (ULift.up (n : OnePoint ℕ)) := (rfl)

/-- Precomposition with the marked shift takes the coefficient at n + 1 to n. -/
@[simp↓]
lemma nullSeqHomEquivFinsupp_nullShift
    (g : nullSeq R ⟶ (LightCondMod.LocallyConstant.functor R).obj M) (n : ℕ) :
    nullSeqHomEquivFinsupp M (nullShift R ≫ g) n = nullSeqHomEquivFinsupp M g (n + 1) := by
  rw [nullSeqHomEquivFinsupp_apply, nullSeqHomEquivFinsupp_apply,
    reducedLightFreeHomEquiv_nullShift]
  exact congrArg _ (natShift_apply_coe n)

end TauCeti
