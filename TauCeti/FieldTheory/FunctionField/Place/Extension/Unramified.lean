/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Normal.Closure
public import TauCeti.FieldTheory.FunctionField.Place.Extension.Inertia

/-!
# Unramified places in composita and Galois closures

A place `P` of `F / k` is **unramified** in an algebraic extension `F' / k'` when every place
`P'` of `F'` above it has ramification index `e(P' ∣ P) = 1` and separable residue extension
`F'_{P'} / F_P`. Over a perfect residue field the second condition is automatic, and this is
Stichtenoth's notion (Definition 3.1.13). In general it cannot be dropped. Over `𝔽_p(s)(t)`, the
Artin–Schreier extensions `y^p - y = s t^{-p}` and `y^p - y = (s + t) t^{-p}` both have `e = 1`
at `t = 0`, with residue extension `𝔽_p(s^{1/p}) / 𝔽_p(s)`. Their compositum contains a root of
`y^p - y = -t^{1 - p}`, so it is ramified there.

In a finite Galois extension `M / F`, the restriction of a place `Q` of `M` to an intermediate
field `E` is unramified over `F` exactly when `E` lies in the inertia field of `Q`
(`TauCeti.Place.le_inertiaField_iff`). This file draws the two consequences of Stichtenoth's
Corollary 3.9.3, for arbitrary residue fields. The fixing subgroup of a compositum is the
intersection of the fixing subgroups, so a place is unramified in `E₁ E₂` exactly when it is
unramified in `E₁` and in `E₂`. The Galois group permutes the places above `P` and carries their
inertia fields along (`TauCeti.Place.inertiaField_smul`), so a place unramified in `E` is
unramified in every conjugate of `E`, hence in the Galois closure of `E`, which those conjugates
generate. Every finite separable extension of `F` embeds into a finite Galois one, so these
statements cover the composita and Galois closures of finite separable extensions.

## Main definitions

* `TauCeti.Place.IsUnramified`: a place is unramified in an extension, with
  `TauCeti.Place.isUnramified_iff`.

## Main results

* `TauCeti.Place.isUnramified_iff_forall_le_inertiaField`: a place is unramified in `E` exactly
  when `E` lies in the inertia field of every place of `M` above it.
* `TauCeti.Place.isUnramified_sup_iff`: **a place is unramified in a compositum exactly when it
  is unramified in both constituents**.
* `TauCeti.Place.isUnramified_normalClosure_iff`: **a place is unramified in the Galois closure
  of `E` exactly when it is unramified in `E`**.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Definition 3.1.13 and Corollary 3.9.3.
-/

public section

open scoped Pointwise

namespace TauCeti

namespace Place

section Definition

universe u u' v v'

variable {k : Type u} {k' : Type u'} {F : Type v} {F' : Type v'}
variable [Field k] [Field k'] [Field F] [Field F']
variable [Algebra k k'] [Algebra k F] [Algebra k' F'] [Algebra F F'] [Algebra k F']
variable [IsScalarTower k k' F'] [IsScalarTower k F F']
variable [Algebra.IsIntegral F F']

/-- A place `P` of `F / k` is **unramified** in `F' / k'` when every place `P'` of `F'` above it
has ramification index `e(P' ∣ P) = 1` and a separable residue extension `F'_{P'} / F_P`
(Stichtenoth, Definition 3.1.13, where the residue extensions are separable because the constant
field is perfect). -/
def IsUnramified (P : Place k F) : Prop :=
  ∀ P' : Place k' F', P'.restrict k F = P →
    ramificationIdx F P' = 1 ∧ Algebra.IsSeparable (P'.restrict k F).ResidueField P'.ResidueField

/-- The characteristic property of an unramified place. -/
theorem isUnramified_iff (P : Place k F) :
    P.IsUnramified (k' := k') (F' := F') ↔
      ∀ P' : Place k' F', P'.restrict k F = P →
        ramificationIdx F P' = 1 ∧
          Algebra.IsSeparable (P'.restrict k F).ResidueField P'.ResidueField :=
  Iff.rfl

end Definition

universe u v w

variable {k : Type u} {F : Type v} {M : Type w}
variable [Field k] [Field F] [Field M] [Algebra k F] [Algebra k M] [Algebra F M]
variable [IsScalarTower k F M] [FiniteDimensional F M] [IsGalois F M]

/-- A place is unramified in an intermediate field `E` of a finite Galois extension `M` exactly
when `E` lies in the inertia field of every place of `M` above it. -/
theorem isUnramified_iff_forall_le_inertiaField
    (hF : TauCeti.IsFunctionField k F) (P : Place k F) (E : IntermediateField F M) :
    P.IsUnramified (k' := k) (F' := E) ↔
      ∀ Q : Place k M, Q.restrict k F = P → E ≤ inertiaField F Q := by
  refine ⟨fun h Q hQ ↦ (le_inertiaField_iff F Q E).mpr (h _ ?_), fun h R hR ↦ ?_⟩
  · simpa only [restrict_restrict] using hQ
  · obtain ⟨Q, rfl⟩ := restrict_surjective_of_finiteDimensional
      (hF.finite_extension (E := E)) (hF.finite_extension (E := M)) R
    exact (le_inertiaField_iff F Q E).mp (h Q (by simpa only [restrict_restrict] using hR))

/-- **Unramifiedness in a compositum** (Stichtenoth, Corollary 3.9.3): a place is unramified in
the compositum of two intermediate fields of a finite Galois extension exactly when it is
unramified in each of them. -/
@[simp]
theorem isUnramified_sup_iff
    (hF : TauCeti.IsFunctionField k F) (P : Place k F) (E₁ E₂ : IntermediateField F M) :
    P.IsUnramified (k' := k) (F' := ↥(E₁ ⊔ E₂)) ↔
      P.IsUnramified (k' := k) (F' := E₁) ∧ P.IsUnramified (k' := k) (F' := E₂) := by
  simp only [isUnramified_iff_forall_le_inertiaField hF, sup_le_iff, ← forall_and]

/-- **Unramifiedness in a Galois closure** (Stichtenoth, Corollary 3.9.3): a place is unramified
in the normal closure of an intermediate field `E` of a finite Galois extension `M / F` exactly
when it is unramified in `E`. -/
@[simp]
theorem isUnramified_normalClosure_iff
    (hF : TauCeti.IsFunctionField k F) (P : Place k F) (E : IntermediateField F M) :
    P.IsUnramified (k' := k) (F' := IntermediateField.normalClosure F E M) ↔
      P.IsUnramified (k' := k) (F' := E) := by
  simp only [isUnramified_iff_forall_le_inertiaField hF]
  refine ⟨fun h Q hQ ↦ (IntermediateField.le_normalClosure E).trans (h Q hQ),
    fun h Q hQ ↦ ?_⟩
  -- The normal closure is generated by the conjugates `σ E`, and `σ E` lies in the inertia field
  -- of `Q` because `E` lies in the inertia field of the conjugate place `σ⁻¹ • Q`.
  rw [IntermediateField.normalClosure_def'', iSup_le_iff]
  intro σ
  have hσ := IntermediateField.map_mono σ.toAlgHom (h (σ⁻¹ • Q) (by rw [restrict_smul, hQ]))
  rwa [← inertiaField_smul, smul_inv_smul] at hσ

end Place

end TauCeti
