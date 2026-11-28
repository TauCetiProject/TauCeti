/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.ZMod
public import TauCeti.Algebra.Module.ZMod.SMulCommClass
public import TauCeti.RepresentationTheory.NormSplit.Basic

/-!
# Higman's criterion for modules over a group algebra

Let `Δ` be a finite group and `R` a semiring. An `R[Δ]`-module `P` satisfies Higman's criterion if
some additive endomorphism `τ` of `P` has `∑ g, g • τ (g⁻¹ • x) = x` for every `x`; following
Higman, such a module is called Higman-projective. The scalars of `R` play no role, so `τ` is only
asked to be additive.

When `P` is killed by `n`, that is, a `ZMod n`-module, additive maps of `P` are `ZMod n`-linear,
and the criterion says that the identity of `P` is a norm for the conjugation action of `Δ` on
`End_{ZMod n}(P)`. For `R = ZMod ℓ` with `ℓ` prime, this norm condition characterizes the
projective modules (`Rep.projective_iff_id_mem_range_norm_linHom`).

## Main definitions

* `TauCeti.IsHigmanProjective`: an `R[Δ]`-module satisfies Higman's criterion.

## Main results

* `TauCeti.isHigmanProjective_iff`: the criterion in terms of its witness `τ`.
* `TauCeti.isHigmanProjective_iff_id_mem_range_norm_linHom`: for a module killed by `n`, the
  criterion says that the identity is a norm for the conjugation action on `End_{ZMod n}(P)`.

## References

* D. G. Higman, *Modules with a group of operators*, Duke Math. J. 21 (1954), 369–376.
-/

public section

open scoped MonoidAlgebra

namespace TauCeti

section Semiring

variable (R Δ P : Type*) [Semiring R] [Group Δ] [Fintype Δ] [AddCommMonoid P] [Module R[Δ] P]

/-- An `R[Δ]`-module `P` is **Higman-projective**, that is, satisfies Higman's criterion, if some
additive endomorphism `τ` of `P` has `∑ g, g • τ (g⁻¹ • x) = x` for every `x`. -/
def IsHigmanProjective : Prop :=
  ∃ τ : P →+ P, ∀ x : P, ∑ g : Δ, MonoidAlgebra.of R Δ g • τ (MonoidAlgebra.of R Δ g⁻¹ • x) = x

/-- Higman's criterion holds when some additive `τ` has `∑ g, g • τ (g⁻¹ • x) = x`. -/
theorem isHigmanProjective_iff : IsHigmanProjective R Δ P ↔
    ∃ τ : P →+ P, ∀ x : P,
      ∑ g : Δ, MonoidAlgebra.of R Δ g • τ (MonoidAlgebra.of R Δ g⁻¹ • x) = x :=
  Iff.rfl

end Semiring

variable {R Δ P : Type*} [Semiring R] [Group Δ] [Fintype Δ] [AddCommGroup P] [Module R[Δ] P]

/-- **Higman's criterion as a norm condition.** For an `R[Δ]`-module `P` killed by `n`, Higman's
criterion says that the identity of `P` is the norm of a `ZMod n`-linear endomorphism for the
conjugation action of `Δ`, acting on `P` through `R[Δ]`. -/
theorem isHigmanProjective_iff_id_mem_range_norm_linHom (n : ℕ) [Module (ZMod n) P] :
    IsHigmanProjective R Δ P ↔ LinearMap.id ∈ LinearMap.range (Representation.linHom
      ((Module.toModuleEnd (ZMod n) (S := R[Δ]) P).toMonoidHom.comp (MonoidAlgebra.of R Δ))
      ((Module.toModuleEnd (ZMod n) (S := R[Δ]) P).toMonoidHom.comp
        (MonoidAlgebra.of R Δ))).norm := by
  rw [isHigmanProjective_iff]
  constructor
  · rintro ⟨τ, hτ⟩
    refine ⟨τ.toZModLinearMap n, LinearMap.ext fun x ↦ ?_⟩
    simp only [Representation.norm_linHom_apply, LinearMap.id_apply, MonoidHom.comp_apply,
      RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, Module.toModuleEnd_apply,
      DistribSMul.toLinearMap_apply, AddMonoidHom.coe_toZModLinearMap]
    exact hτ x
  · rintro ⟨φ, hφ⟩
    refine ⟨φ.toAddMonoidHom, fun x ↦ ?_⟩
    have h := LinearMap.congr_fun hφ x
    simp only [Representation.norm_linHom_apply, LinearMap.id_apply, MonoidHom.comp_apply,
      RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, Module.toModuleEnd_apply,
      DistribSMul.toLinearMap_apply] at h
    exact h

end TauCeti
