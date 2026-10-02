/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.ContinuousMulEquiv
public import TauCeti.Topology.Algebra.Group.Profinite.Free.ProP
import TauCeti.Topology.Connected.TotallyDisconnected
import Mathlib.Algebra.Group.Shrink
import Mathlib.Basic.Countable.Small

/-!
# Free pro-`p` groups across universes

The free pro-`p` group `freeProP p X` lives in the universe of its generating type `X`, and its
universal property `TauCeti.freeProP.lift` only reaches pro-`p` groups in that universe. A
topologically finitely generated pro-`p` group `G : Type u` therefore gets its minimal
presentations on generating types in `Type u`, such as `ULift.{u} (Fin n)`, while the normal-form
relators of the Demushkin classification are words in `freeProP p (Fin n)`. This file identifies
the two free pro-`p` groups: `TauCeti.freeProP.uliftEquiv` is the topological isomorphism
`freeProP p (ULift X) ≃ₜ* freeProP p X` matching the generator at `⟨x⟩` with the generator at `x`.

## Main declarations

* `TauCeti.freeProP.uliftEquiv`: the topological isomorphism
  `freeProP p (ULift X) ≃ₜ* freeProP p X`.
* `TauCeti.freeProP.uliftEquiv_of`, `TauCeti.freeProP.uliftEquiv_symm_of`: it matches the
  generators.
-/

public section

namespace TauCeti

universe u v

namespace freeProP

variable (p : ℕ) (X : Type u)

/-- The continuous homomorphism `freeProP p (ULift X) →ₜ* freeProP p X` carrying the generator at
`⟨x⟩` to the generator at `x`: the lift of `x ↦ ⟨of x⟩` into the universe lift of the target. -/
private noncomputable def uliftDown : freeProP p (ULift.{v} X) →ₜ* freeProP p X :=
  ((ContinuousMulEquiv.ulift : ULift.{v} (freeProP p X) ≃ₜ* freeProP p X) :
      ULift.{v} (freeProP p X) →ₜ* freeProP p X).comp
    (lift ((isProP_freeProP p X).of_equiv ContinuousMulEquiv.ulift.symm)
      fun x : ULift.{v} X ↦ ULift.up (of x.down))

private theorem uliftDown_of (x : ULift.{v} X) : uliftDown p X (of x) = of x.down := by
  simp [uliftDown, lift_of]

private theorem uliftDown_surjective :
    Function.Surjective (uliftDown p X : freeProP p (ULift.{v} X) →ₜ* freeProP p X) := by
  set ψ : freeProP p (ULift.{v} X) →ₜ* freeProP p X := uliftDown p X
  refine (MonoidHom.range_eq_top (f := (ψ : freeProP p (ULift.{v} X) →* freeProP p X))).1
    (top_le_iff.1 ?_)
  rw [← topologicalClosure_closure_range_of_eq_top p X]
  refine Subgroup.topologicalClosure_minimal _ ((Subgroup.closure_le _).2 ?_) ?_
  · rintro _ ⟨x, rfl⟩
    exact ⟨of (ULift.up x), uliftDown_of p X _⟩
  · exact (isCompact_range ψ.continuous).isClosed

private theorem uliftDown_injective :
    Function.Injective (uliftDown p X : freeProP p (ULift.{v} X) →ₜ* freeProP p X) := by
  set ψ : freeProP p (ULift.{v} X) →ₜ* freeProP p X := uliftDown p X
  refine (MonoidHom.ker_eq_bot_iff (ψ : freeProP p (ULift.{v} X) →* freeProP p X)).1
    (le_bot_iff.1 ?_)
  rw [← Subgroup.iInf_openNormalSubgroup_eq_bot (G := freeProP p (ULift.{v} X))]
  refine le_iInf fun U ↦ fun g hg ↦ ?_
  -- The quotient by `U` is a finite `p`-group; shrink it to the universe of `X`.
  set Q := freeProP p (ULift.{v} X) ⧸ U.toSubgroup
  have hQ : IsPGroup p Q := isProP_iff.1 (isProP_freeProP p (ULift.{v} X)) U
  have : Finite Q :=
    inferInstanceAs (Finite (freeProP p (ULift.{v} X) ⧸ U.toOpenSubgroup.toSubgroup))
  have : Small.{u} Q := Countable.toSmall Q
  let e : Shrink.{u} Q ≃* Q := Shrink.mulEquiv
  let _ : TopologicalSpace (Shrink.{u} Q) := ⊥
  have : DiscreteTopology (Shrink.{u} Q) := ⟨rfl⟩
  have : Finite (Shrink.{u} Q) := Finite.of_equiv Q (equivShrink Q : Q ≃ Shrink.{u} Q)
  -- The quotient map and its factorization through `freeProP p X`.
  let π : freeProP p (ULift.{v} X) →ₜ* Q :=
    { toMonoidHom := QuotientGroup.mk' U.toSubgroup
      continuous_toFun := QuotientGroup.continuous_mk }
  let θ : freeProP p X →ₜ* Shrink.{u} Q :=
    lift (hQ.of_equiv e.symm).isProP fun x ↦ e.symm (π (of (ULift.up x)))
  let eC : Shrink.{u} Q →ₜ* Q :=
    { toMonoidHom := e.toMonoidHom
      continuous_toFun := continuous_of_discreteTopology }
  have hcomp : (eC.comp θ).comp (uliftDown p X) = π := hom_ext fun x ↦ by
    simp [θ, eC, uliftDown_of, lift_of]
  have hg1 : uliftDown p X g = 1 := hg
  have h := DFunLike.congr_fun hcomp g
  rw [ContinuousMonoidHom.coe_comp, Function.comp_apply, hg1, map_one] at h
  exact (QuotientGroup.eq_one_iff g).1 h.symm

/-- **Free pro-`p` groups across universes.** The free pro-`p` group on the universe lift of `X`
is topologically isomorphic to the free pro-`p` group on `X`, by the isomorphism matching the
generator at `⟨x⟩` with the generator at `x`. -/
noncomputable def uliftEquiv : freeProP p (ULift.{v} X) ≃ₜ* freeProP p X :=
  (MulEquiv.ofBijective (uliftDown p X : freeProP p (ULift.{v} X) →* freeProP p X)
    ⟨uliftDown_injective p X, uliftDown_surjective p X⟩).toContinuousMulEquiv fun _ ↦
      ((uliftDown p X).continuous.homeoOfEquivCompactToT2
        (f := (MulEquiv.ofBijective _ ⟨uliftDown_injective p X, uliftDown_surjective p X⟩).toEquiv)
        ).isOpen_preimage

/-- The universe-lift isomorphism carries the generator at `⟨x⟩` to the generator at `x`. -/
@[simp]
theorem uliftEquiv_of (x : ULift.{v} X) : uliftEquiv p X (of x) = of x.down :=
  uliftDown_of p X x

/-- The inverse of the universe-lift isomorphism carries the generator at `x` to the generator at
`⟨x⟩`. -/
@[simp]
theorem uliftEquiv_symm_of (x : X) : (uliftEquiv p X).symm (of x) = of (ULift.up.{v} x) :=
  (uliftEquiv p X).symm_apply_eq.2 (uliftEquiv_of p X _).symm

end freeProP

end TauCeti
