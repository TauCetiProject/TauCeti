/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.RingTheory.Finiteness.Small
import TauCeti.Algebra.Module.Dual.ProjectiveInjective
import TauCeti.Algebra.Module.Opposite
import TauCeti.RingTheory.Artinian.FiniteLength
import TauCeti.RingTheory.Artinian.Module
public import TauCeti.RingTheory.MatlisDuality.Basic
public import TauCeti.RingTheory.MatlisDuality.Semilocal

/-!
# Matlis duality for Artin algebras

Let `R` be a commutative Artinian ring with an injective hull `E` of `R ⧸ J(R)`, and let `A` be an
Artin `R`-algebra, an `R`-algebra that is finitely generated as an `R`-module. The Matlis dual
`D_R N = Hom_R(N, E)` of `TauCeti/RingTheory/MatlisDuality/Basic.lean` exchanges left and right
`A`-modules. This file proves that it preserves finite generation, that it exchanges finitely
generated projective and injective modules, and that `D_R A` is an injective cogenerator, so that
every finitely generated `A`-module has a finitely generated injective hull.

Right `A`-modules are modules over `Aᵐᵒᵖ`.

## Main results

* `TauCeti.IsInjectiveEnvelope.moduleInjective_op_matlisDual_iff_projective` and
  `TauCeti.IsInjectiveEnvelope.moduleProjective_op_matlisDual_iff_injective`, with the right-module
  forms `moduleInjective_matlisDual_iff_projective_op` and
  `moduleProjective_matlisDual_iff_injective_op`: a finitely generated module is projective exactly
  when its dual is injective, and injective exactly when its dual is projective.
  `TauCeti.moduleInjective_matlisDual_iff_projective_op` and
  `TauCeti.moduleProjective_op_matlisDual_iff_injective` are the forms for any injective `E` such
  that each `Hom_R(R ⧸ 𝔪, E)` has length one.
* `TauCeti.IsInjectiveEnvelope.exists_injective_linearMap_pi_matlisDual`: every Artinian
  `A`-module embeds into a finite power of the injective module `D_R A`.
* `TauCeti.exists_isInjectiveEnvelope_finite`: every finitely generated `A`-module has a finitely
  generated injective hull.

## Implementation notes

In a lemma such as `finite_op_matlisDual`, `op` names the scalars `Aᵐᵒᵖ` of the conclusion, as
`finite_matlisDual_of_finite_op` does for its hypothesis.

## References

* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*, Sections II.3 and
  II.4.
-/

public section

noncomputable section

namespace TauCeti

open MulOpposite MatlisDual

universe u v w t

attribute [local instance] opOpModule isScalarTower_opOpModule RingHomInvPair.of_ringEquiv

section Artin

variable {R : Type u} [CommRing R] [IsArtinianRing R] {E : Type v} [AddCommGroup E] [Module R E]
  [Small.{v} R] {f : R ⧸ Ring.jacobson R →ₗ[R] E} {A : Type t} [Ring A] [Algebra R A]
  {N : Type w} [AddCommGroup N] [Module R N]

/-- The Matlis dual of a finitely generated module over a commutative Artinian ring is finitely
generated. -/
theorem IsInjectiveEnvelope.finite_matlisDual (hf : IsInjectiveEnvelope f) (N : Type w)
    [AddCommGroup N] [Module R N] [Module.Finite R N] : Module.Finite R (MatlisDual R E N) := by
  have hN := isFiniteLength_of_finite R N
  have hD : IsFiniteLength R (MatlisDual R E N) := by
    rw [← Module.length_ne_top_iff, (equivLinearMap R E N).length_eq,
      hf.length_linearMap_quotient_jacobson, Module.length_ne_top_iff]
    exact hN
  have := (isFiniteLength_iff_isNoetherian_isArtinian.mp hD).1
  infer_instance

section Finite

variable [Module.Finite R A]

/-- The Matlis dual of a finitely generated left `A`-module is a finitely generated right
`A`-module. -/
theorem IsInjectiveEnvelope.finite_op_matlisDual [Module A N] [IsScalarTower R A N]
    [Module.Finite A N] (hf : IsInjectiveEnvelope f) :
    Module.Finite Aᵐᵒᵖ (MatlisDual R E N) :=
  have : Module.Finite R N := Module.Finite.trans A N
  have := hf.finite_matlisDual N
  Module.Finite.of_restrictScalars_finite R Aᵐᵒᵖ _

/-- The Matlis dual of a finitely generated right `A`-module is a finitely generated left
`A`-module. -/
theorem IsInjectiveEnvelope.finite_matlisDual_of_finite_op [Module Aᵐᵒᵖ N]
    [IsScalarTower R Aᵐᵒᵖ N] [Module.Finite Aᵐᵒᵖ N] (hf : IsInjectiveEnvelope f) :
    Module.Finite A (MatlisDual R E N) :=
  have : Module.Finite R N := Module.Finite.trans Aᵐᵒᵖ N
  have := hf.finite_matlisDual N
  Module.Finite.of_restrictScalars_finite R A _

/-- A finitely generated left `A`-module is projective exactly when its Matlis dual is an injective
right module. -/
theorem IsInjectiveEnvelope.moduleInjective_op_matlisDual_iff_projective [Module A N]
    [IsScalarTower R A N] [Module.Finite A N] (hf : IsInjectiveEnvelope f) :
    Module.Injective Aᵐᵒᵖ (MatlisDual R E N) ↔ Module.Projective A N := by
  have := hf.moduleInjective
  have : Small.{max w v} Aᵐᵒᵖ :=
    have : Small.{v} A := Module.Finite.small R A
    have : Small.{max w v} A := small_lift A
    small_of_injective MulOpposite.unop_injective
  have : Module.Finite R N := Module.Finite.trans A N
  have : Module.Finite Aᵐᵒᵖᵐᵒᵖ N := Module.Finite.of_restrictScalars_finite R _ N
  exact ((equivLinearMap R E N).moduleInjective_iff_projective_of_dual_of_bijective (A := Aᵐᵒᵖ)
    (fun a φ x => smul_op_apply a φ x)
    (hf.bijective_applyₗ_quotient_jacobson (isFiniteLength_of_finite R _))
    (hf.bijective_applyₗ_quotient_jacobson
      (isFiniteLength_of_finite_trans R A N))).trans
    ⟨fun _ => .of_equiv (opOpSemilinearEquiv (A := A)).symm,
      fun _ => .of_equiv (opOpSemilinearEquiv (A := A))⟩

/-- A finitely generated right `A`-module is projective exactly when its Matlis dual is an injective
left module, for an injective `E` such that each `Hom_R(R ⧸ 𝔪, E)` has length one. -/
theorem moduleInjective_matlisDual_iff_projective_op [Module.Injective R E]
    (hE : ∀ 𝔪 : Ideal R, 𝔪.IsMaximal → Module.length R (R ⧸ 𝔪 →ₗ[R] E) = 1) [Module Aᵐᵒᵖ N]
    [IsScalarTower R Aᵐᵒᵖ N] [Module.Finite Aᵐᵒᵖ N] :
    Module.Injective A (MatlisDual R E N) ↔ Module.Projective Aᵐᵒᵖ N :=
  have : Small.{v} A := Module.Finite.small R A
  have : Small.{max w v} A := small_lift A
  (equivLinearMap R E N).moduleInjective_iff_projective_of_dual_of_bijective smul_apply
    (bijective_applyₗ_of_forall_isMaximal hE (isFiniteLength_of_finite R _))
    (bijective_applyₗ_of_forall_isMaximal hE (isFiniteLength_of_finite_trans R Aᵐᵒᵖ N))

/-- A finitely generated right `A`-module is projective exactly when its Matlis dual is an injective
left module. -/
theorem IsInjectiveEnvelope.moduleInjective_matlisDual_iff_projective_op [Module Aᵐᵒᵖ N]
    [IsScalarTower R Aᵐᵒᵖ N] [Module.Finite Aᵐᵒᵖ N] (hf : IsInjectiveEnvelope f) :
    Module.Injective A (MatlisDual R E N) ↔ Module.Projective Aᵐᵒᵖ N :=
  have := hf.moduleInjective
  TauCeti.moduleInjective_matlisDual_iff_projective_op hf.length_quotient_linearMap_eq_one

omit [Module.Finite R A] in
/-- **`D_R A` is a cogenerator.** Every Artinian left module over an `R`-algebra `A` embeds into a
finite power of `D_R A`. -/
theorem IsInjectiveEnvelope.exists_injective_linearMap_pi_matlisDual [Module A N]
    [IsScalarTower R A N] [IsArtinian A N] (hf : IsInjectiveEnvelope f) :
    ∃ (n : ℕ) (g : N →ₗ[A] (Fin n → MatlisDual R E A)), Function.Injective g := by
  have := hf.moduleInjective
  refine IsArtinian.exists_injective_linearMap_pi fun x hx ↦ ?_
  -- As `E` is a cogenerator, some functional `φ` on `N` does not kill `x`; its adjoint
  -- `N → D_R A` does not kill `x` either, evaluating at `1`.
  obtain ⟨φ, hφ⟩ : ∃ φ : MatlisDual R E N, equivLinearMap R E N φ x ≠ 0 := by
    by_contra! h
    exact hx (MatlisDual.injective_evalₗ
      (nontrivial_linearMap_of_isMaximal hf.length_quotient_linearMap_eq_one)
      (MatlisDual.ext fun φ ↦ by simpa using h φ))
  refine ⟨equivLinearMapDualRegular φ, fun h ↦ hφ ?_⟩
  simpa using congr(equivLinearMap R E A $h 1)

variable [Small.{w} A]

/-- The dual of a finitely generated injective right `A`-module is a projective left module. -/
theorem IsInjectiveEnvelope.moduleProjective_matlisDual_of_injective_op [Module Aᵐᵒᵖ N]
    [IsScalarTower R Aᵐᵒᵖ N] [Module.Finite Aᵐᵒᵖ N] [Module.Injective Aᵐᵒᵖ N]
    (hf : IsInjectiveEnvelope f) : Module.Projective A (MatlisDual R E N) :=
  have := hf.finite_matlisDual_of_finite_op (A := A) (N := N)
  have : Small.{w} Aᵐᵒᵖ := small_of_injective MulOpposite.unop_injective
  (equivLinearMap R E N).moduleProjective_of_dual_injective_of_bijective smul_apply
    (hf.bijective_applyₗ_quotient_jacobson (isFiniteLength_of_finite R A))
    (hf.bijective_applyₗ_quotient_jacobson
      (isFiniteLength_of_finite_trans R Aᵐᵒᵖ N)).1

/-- The dual of a finitely generated injective left `A`-module is a projective right module, for an
injective `E` such that each `Hom_R(R ⧸ 𝔪, E)` has length one. -/
theorem moduleProjective_op_matlisDual_of_injective [Module.Injective R E]
    (hE : ∀ 𝔪 : Ideal R, 𝔪.IsMaximal → Module.length R (R ⧸ 𝔪 →ₗ[R] E) = 1) [Module A N]
    [IsScalarTower R A N] [Module.Finite A N] [Module.Injective A N] :
    Module.Projective Aᵐᵒᵖ (MatlisDual R E N) :=
  have hN := isFiniteLength_of_finite_trans R A N
  have := (isFiniteLength_iff_isNoetherian_isArtinian.mp (MatlisDual.isFiniteLength hE hN)).1
  have : Module.Finite Aᵐᵒᵖ (MatlisDual R E N) := Module.Finite.of_restrictScalars_finite R _ _
  have : Small.{w} Aᵐᵒᵖᵐᵒᵖ := small_of_surjective (RingEquiv.opOp A).surjective
  have : Module.Injective Aᵐᵒᵖᵐᵒᵖ N :=
    Module.Injective.of_ringEquiv (RingEquiv.opOp A) (opOpSemilinearEquiv (A := A))
  (equivLinearMap R E N).moduleProjective_of_dual_injective_of_bijective (A := Aᵐᵒᵖ)
    (fun a φ x => smul_op_apply a φ x)
    (bijective_applyₗ_of_forall_isMaximal hE (isFiniteLength_of_finite R _))
    (bijective_applyₗ_of_forall_isMaximal hE hN).1

/-- The dual of a finitely generated injective left `A`-module is a projective right module. -/
theorem IsInjectiveEnvelope.moduleProjective_op_matlisDual_of_injective [Module A N]
    [IsScalarTower R A N] [Module.Finite A N] [Module.Injective A N]
    (hf : IsInjectiveEnvelope f) : Module.Projective Aᵐᵒᵖ (MatlisDual R E N) :=
  have := hf.moduleInjective
  TauCeti.moduleProjective_op_matlisDual_of_injective hf.length_quotient_linearMap_eq_one

/-- A finitely generated left `A`-module is injective exactly when its Matlis dual is a projective
right module, for an injective `E` such that each `Hom_R(R ⧸ 𝔪, E)` has length one. -/
theorem moduleProjective_op_matlisDual_iff_injective [Module.Injective R E]
    (hE : ∀ 𝔪 : Ideal R, 𝔪.IsMaximal → Module.length R (R ⧸ 𝔪 →ₗ[R] E) = 1) [Module A N]
    [IsScalarTower R A N] [Module.Finite A N] :
    Module.Projective Aᵐᵒᵖ (MatlisDual R E N) ↔ Module.Injective A N :=
  ⟨fun _ => moduleInjective_of_projective_op_matlisDual hE (isFiniteLength_of_finite_trans R A N),
    fun _ => moduleProjective_op_matlisDual_of_injective hE⟩

/-- A finitely generated left `A`-module is injective exactly when its Matlis dual is a projective
right module. -/
theorem IsInjectiveEnvelope.moduleProjective_op_matlisDual_iff_injective [Module A N]
    [IsScalarTower R A N] [Module.Finite A N] (hf : IsInjectiveEnvelope f) :
    Module.Projective Aᵐᵒᵖ (MatlisDual R E N) ↔ Module.Injective A N :=
  have := hf.moduleInjective
  TauCeti.moduleProjective_op_matlisDual_iff_injective hf.length_quotient_linearMap_eq_one

/-- A finitely generated right `A`-module is injective exactly when its Matlis dual is a projective
left module. -/
theorem IsInjectiveEnvelope.moduleProjective_matlisDual_iff_injective_op [Module Aᵐᵒᵖ N]
    [IsScalarTower R Aᵐᵒᵖ N] [Module.Finite Aᵐᵒᵖ N] (hf : IsInjectiveEnvelope f) :
    Module.Projective A (MatlisDual R E N) ↔ Module.Injective Aᵐᵒᵖ N :=
  have := hf.moduleInjective
  ⟨fun _ => moduleInjective_op_of_projective_matlisDual hf.length_quotient_linearMap_eq_one
    (isFiniteLength_of_finite_trans R Aᵐᵒᵖ N),
    fun _ => hf.moduleProjective_matlisDual_of_injective_op⟩

end Finite

end Artin

/-- **Finitely generated injective hulls.** Every finitely generated left module over an Artin
algebra has an injective hull which is finitely generated. -/
theorem exists_isInjectiveEnvelope_finite (R : Type u) [CommRing R] [IsArtinianRing R]
    {A : Type t} [Ring A] [Algebra R A] [Module.Finite R A] (N : Type w) [AddCommGroup N]
    [Module R N] [Module A N] [IsScalarTower R A N] [Module.Finite A N] :
    ∃ (Q : Type (max u t)) (_ : AddCommGroup Q) (_ : Module A Q) (_ : Module.Finite A Q)
      (i : N →ₗ[A] Q), IsInjectiveEnvelope i := by
  obtain ⟨E, _, _, f, hf, -⟩ := exists_isInjectiveEnvelope_quotient_jacobson.{u, u} R
  have := IsArtinianRing.of_finite R A
  obtain ⟨n, g, hg⟩ := hf.exists_injective_linearMap_pi_matlisDual (A := A) (N := N)
  have := hf.moduleInjective
  have : Small.{max u t} A := small_max A
  have : Module.Injective A (Fin n → MatlisDual R E A) := Module.Injective.pi A _
  obtain ⟨P, _, hP⟩ := g.exists_isInjectiveEnvelope_submodule hg
  have := hf.finite_matlisDual A
  have : Module.Finite R P :=
    Module.Finite.of_injective (P.subtype.restrictScalars R) P.injective_subtype
  exact ⟨P, inferInstance, inferInstance, Module.Finite.of_restrictScalars_finite R A P, _, hP⟩

end TauCeti
