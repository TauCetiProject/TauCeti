/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.GroupAction.OrbitRelQuotient

/-!
# Commutation of quotient descent with fibrewise operations and orbit maps

Unary and binary fibrewise operations over an orbit space `MulAction.orbitRel.Quotient G X` commute
algebraically with `TauCeti.MulAction.orbitRelQuotientRec` and scalar
`TauCeti.MulAction.orbitRelQuotientLift` (`TauCeti.MulAction.apply_orbitRelQuotientRec`,
`TauCeti.MulAction.apply_orbitRelQuotientRec_eq_orbitRelQuotientLift`,
`TauCeti.MulAction.apply₂_orbitRelQuotientRec`,
`TauCeti.MulAction.apply₂_orbitRelQuotientRec_eq_orbitRelQuotientLift`). Dependent descent is
also natural along `MulActionHom.orbitRelQuotientMap`
(`MulActionHom.orbitRelQuotientRec_orbitRelQuotientMap_apply`).
-/

public section

namespace TauCeti

section Rec

variable {G X : Type*} [Group G] [MulAction G X] {V : MulAction.orbitRel.Quotient G X → Sort*}
  {t : ∀ x : X, V (Quotient.mk (MulAction.orbitRel G X) x)}

/-- Applying a fibrewise operation over the orbit space to an invariant pulled-back section yields
an invariant pulled-back section of the target family. -/
theorem MulAction.apply_smul_heq {W : MulAction.orbitRel.Quotient G X → Sort*}
    (F : ∀ q : MulAction.orbitRel.Quotient G X, V q → W q)
    (ht : ∀ (g : G) (x : X), t (g • x) ≍ t x) (g : G) (x : X) :
    F (Quotient.mk (MulAction.orbitRel G X) (g • x)) (t (g • x)) ≍
      F (Quotient.mk (MulAction.orbitRel G X) x) (t x) := by
  have aux {q₁ q₂} {v₁ : V q₁} {v₂ : V q₂} (hq : q₁ = q₂) (hv : v₁ ≍ v₂) :
      F q₁ v₁ ≍ F q₂ v₂ := by subst hq; subst hv; rfl
  exact aux (Quotient.sound ⟨g, rfl⟩) (ht g x)

/-- **Fibrewise operations commute with quotient descent.** Applying a fibrewise map `F` over the
orbit space to the descent of `t` is the descent of `x ↦ F [x] (t x)`. -/
theorem MulAction.apply_orbitRelQuotientRec {W : MulAction.orbitRel.Quotient G X → Sort*}
    (F : ∀ q : MulAction.orbitRel.Quotient G X, V q → W q)
    (ht : ∀ (g : G) (x : X), t (g • x) ≍ t x) (q : MulAction.orbitRel.Quotient G X) :
    F q (MulAction.orbitRelQuotientRec t ht q) =
      MulAction.orbitRelQuotientRec (fun x ↦ F (Quotient.mk (MulAction.orbitRel G X) x) (t x))
        (MulAction.apply_smul_heq F ht) q := by
  induction q using Quotient.inductionOn
  simp only [MulAction.orbitRelQuotientRec_mk]

/-- Applying a fibrewise map into a fixed codomain `Z` to an invariant pulled-back section yields a
`G`-invariant map into `Z`. -/
theorem MulAction.apply_smul_eq {Z : Type*} (F : ∀ q : MulAction.orbitRel.Quotient G X, V q → Z)
    (ht : ∀ (g : G) (x : X), t (g • x) ≍ t x) (g : G) (x : X) :
    F (Quotient.mk (MulAction.orbitRel G X) (g • x)) (t (g • x)) =
      F (Quotient.mk (MulAction.orbitRel G X) x) (t x) :=
  eq_of_heq (MulAction.apply_smul_heq (W := fun _ ↦ Z) F ht g x)

/-- Evaluating a fibrewise map into a fixed codomain `Z` on a descended section agrees with the
non-dependent descent `orbitRelQuotientLift` of the upstairs composite. -/
theorem MulAction.apply_orbitRelQuotientRec_eq_orbitRelQuotientLift {Z : Type*}
    (F : ∀ q : MulAction.orbitRel.Quotient G X, V q → Z)
    (ht : ∀ (g : G) (x : X), t (g • x) ≍ t x) (q : MulAction.orbitRel.Quotient G X) :
    F q (MulAction.orbitRelQuotientRec t ht q) =
      MulAction.orbitRelQuotientLift (fun x ↦ F (Quotient.mk (MulAction.orbitRel G X) x) (t x))
        (MulAction.apply_smul_eq F ht) q := by
  induction q using Quotient.inductionOn
  simp only [MulAction.orbitRelQuotientRec_mk, MulAction.orbitRelQuotientLift_mk]

/-- Applying a binary fibrewise operation over the orbit space to two invariant pulled-back
sections yields an invariant pulled-back section. -/
theorem MulAction.apply₂_smul_heq {V₁ V₂ V₃ : MulAction.orbitRel.Quotient G X → Sort*}
    (B : ∀ q : MulAction.orbitRel.Quotient G X, V₁ q → V₂ q → V₃ q)
    {t₁ : ∀ x : X, V₁ (Quotient.mk (MulAction.orbitRel G X) x)}
    {t₂ : ∀ x : X, V₂ (Quotient.mk (MulAction.orbitRel G X) x)}
    (ht₁ : ∀ (g : G) (x : X), t₁ (g • x) ≍ t₁ x)
    (ht₂ : ∀ (g : G) (x : X), t₂ (g • x) ≍ t₂ x) (g : G) (x : X) :
    B (Quotient.mk (MulAction.orbitRel G X) (g • x)) (t₁ (g • x)) (t₂ (g • x)) ≍
      B (Quotient.mk (MulAction.orbitRel G X) x) (t₁ x) (t₂ x) := by
  have aux {q₁ q₂} {v₁ : V₁ q₁} {v₂ : V₁ q₂} {w₁ : V₂ q₁} {w₂ : V₂ q₂}
      (hq : q₁ = q₂) (hv : v₁ ≍ v₂) (hw : w₁ ≍ w₂) : B q₁ v₁ w₁ ≍ B q₂ v₂ w₂ := by
    subst hq; subst hv; subst hw; rfl
  exact aux (Quotient.sound ⟨g, rfl⟩) (ht₁ g x) (ht₂ g x)

/-- **Binary fibrewise operations commute with quotient descent.** Applying `B` fibrewise to two
descended sections is the descent of `x ↦ B [x] (t₁ x) (t₂ x)`. -/
theorem MulAction.apply₂_orbitRelQuotientRec {V₁ V₂ V₃ : MulAction.orbitRel.Quotient G X → Sort*}
    (B : ∀ q : MulAction.orbitRel.Quotient G X, V₁ q → V₂ q → V₃ q)
    {t₁ : ∀ x : X, V₁ (Quotient.mk (MulAction.orbitRel G X) x)}
    {t₂ : ∀ x : X, V₂ (Quotient.mk (MulAction.orbitRel G X) x)}
    (ht₁ : ∀ (g : G) (x : X), t₁ (g • x) ≍ t₁ x)
    (ht₂ : ∀ (g : G) (x : X), t₂ (g • x) ≍ t₂ x) (q : MulAction.orbitRel.Quotient G X) :
    B q (MulAction.orbitRelQuotientRec t₁ ht₁ q) (MulAction.orbitRelQuotientRec t₂ ht₂ q) =
      MulAction.orbitRelQuotientRec (fun x ↦ B (Quotient.mk (MulAction.orbitRel G X) x) (t₁ x)
        (t₂ x)) (MulAction.apply₂_smul_heq B ht₁ ht₂) q := by
  induction q using Quotient.inductionOn
  simp only [MulAction.orbitRelQuotientRec_mk]

/-- Applying a binary fibrewise pairing into a fixed codomain `Z` to two invariant pulled-back
sections yields a `G`-invariant map into `Z`. -/
theorem MulAction.apply₂_smul_eq {V₁ V₂ : MulAction.orbitRel.Quotient G X → Sort*} {Z : Type*}
    (B : ∀ q : MulAction.orbitRel.Quotient G X, V₁ q → V₂ q → Z)
    {t₁ : ∀ x : X, V₁ (Quotient.mk (MulAction.orbitRel G X) x)}
    {t₂ : ∀ x : X, V₂ (Quotient.mk (MulAction.orbitRel G X) x)}
    (ht₁ : ∀ (g : G) (x : X), t₁ (g • x) ≍ t₁ x)
    (ht₂ : ∀ (g : G) (x : X), t₂ (g • x) ≍ t₂ x) (g : G) (x : X) :
    B (Quotient.mk (MulAction.orbitRel G X) (g • x)) (t₁ (g • x)) (t₂ (g • x)) =
      B (Quotient.mk (MulAction.orbitRel G X) x) (t₁ x) (t₂ x) :=
  eq_of_heq (MulAction.apply₂_smul_heq (V₃ := fun _ ↦ Z) B ht₁ ht₂ g x)

/-- Evaluating a binary fibrewise pairing into a fixed codomain `Z` on two descended sections
agrees with the non-dependent descent `orbitRelQuotientLift` of the upstairs pairing. -/
theorem MulAction.apply₂_orbitRelQuotientRec_eq_orbitRelQuotientLift
    {V₁ V₂ : MulAction.orbitRel.Quotient G X → Sort*} {Z : Type*}
    (B : ∀ q : MulAction.orbitRel.Quotient G X, V₁ q → V₂ q → Z)
    {t₁ : ∀ x : X, V₁ (Quotient.mk (MulAction.orbitRel G X) x)}
    {t₂ : ∀ x : X, V₂ (Quotient.mk (MulAction.orbitRel G X) x)}
    (ht₁ : ∀ (g : G) (x : X), t₁ (g • x) ≍ t₁ x)
    (ht₂ : ∀ (g : G) (x : X), t₂ (g • x) ≍ t₂ x) (q : MulAction.orbitRel.Quotient G X) :
    B q (MulAction.orbitRelQuotientRec t₁ ht₁ q) (MulAction.orbitRelQuotientRec t₂ ht₂ q) =
      MulAction.orbitRelQuotientLift (fun x ↦ B (Quotient.mk (MulAction.orbitRel G X) x) (t₁ x)
        (t₂ x)) (MulAction.apply₂_smul_eq B ht₁ ht₂) q := by
  induction q using Quotient.inductionOn
  simp only [MulAction.orbitRelQuotientRec_mk, MulAction.orbitRelQuotientLift_mk]

end Rec

end TauCeti

namespace MulActionHom

open TauCeti

variable {G X : Type*} [Group G] [MulAction G X] {H Y : Type*} [Group H] [MulAction H Y]
  {σ : G → H}

/-- If a family `t'` over the pulled-back fibre family `q ↦ V (orbitRelQuotientMap φ q)` agrees
heterogeneously with `x ↦ t (φ x)` for an `H`-invariant family `t`, then `t'` is `G`-invariant. -/
theorem smul_heq_of_comp_orbitRelQuotientMap {V : MulAction.orbitRel.Quotient H Y → Sort*}
    (φ : X →ₑ[σ] Y) {t : ∀ y : Y, V (Quotient.mk (MulAction.orbitRel H Y) y)}
    (ht : ∀ (h : H) (y : Y), t (h • y) ≍ t y)
    {t' : ∀ x : X, V (orbitRelQuotientMap φ (Quotient.mk (MulAction.orbitRel G X) x))}
    (ht' : ∀ x : X, t' x ≍ t (φ x)) (g : G) (x : X) :
    t' (g • x) ≍ t' x := by
  have aux {y₁ y₂ : Y} (hy : y₁ = y₂) : t y₁ ≍ t y₂ := hy ▸ HEq.rfl
  exact (ht' (g • x)).trans ((aux (map_smulₛₗ φ g x)).trans ((ht (σ g) (φ x)).trans (ht' x).symm))

/-- **Dependent naturality of section descent.** Pulling back the `H`-orbit descent of `t` along
`orbitRelQuotientMap φ` agrees with the `G`-orbit descent of any family `t'` representing
`x ↦ t (φ x)` over `q ↦ V (orbitRelQuotientMap φ q)`. -/
theorem orbitRelQuotientRec_orbitRelQuotientMap_apply
    {V : MulAction.orbitRel.Quotient H Y → Sort*} (φ : X →ₑ[σ] Y)
    {t : ∀ y : Y, V (Quotient.mk (MulAction.orbitRel H Y) y)}
    (ht : ∀ (h : H) (y : Y), t (h • y) ≍ t y)
    {t' : ∀ x : X, V (orbitRelQuotientMap φ (Quotient.mk (MulAction.orbitRel G X) x))}
    (ht' : ∀ x : X, t' x ≍ t (φ x)) (q : MulAction.orbitRel.Quotient G X) :
    MulAction.orbitRelQuotientRec t ht (orbitRelQuotientMap φ q) =
      MulAction.orbitRelQuotientRec (V := fun q ↦ V (orbitRelQuotientMap φ q))
        t' (smul_heq_of_comp_orbitRelQuotientMap φ ht ht') q := by
  induction q using Quotient.inductionOn with | h x =>
  rw [MulAction.orbitRelQuotientRec_mk]
  exact eq_of_heq <| (congr_arg_heq (MulAction.orbitRelQuotientRec t ht)
    (orbitRelQuotientMap_mk φ x)).trans <|
    (heq_of_eq (MulAction.orbitRelQuotientRec_mk (φ x))).trans (ht' x).symm

end MulActionHom
