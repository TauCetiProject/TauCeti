/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Galois.Abelian

/-!
# Commutativity of Galois groups

Mathlib carries abelianness of a Galois extension as the class `IsAbelianGalois`, and its
instance `IsAbelianGalois K K'` for an intermediate field `K'` says that every subextension of an
abelian extension is again abelian. A construction whose ambient group is the Galois group of a
*general* extension cannot ask for that class, since a bundled commutative structure on
`Gal(L/K)` would be an assumption about `L/K`; it carries commutativity as a hypothesis
`∀ σ τ : Gal(L/K), Commute σ τ` instead. This file reads Mathlib's instance in that unbundled
form. The same hypothesis supplies the scoped `IsMulCommutative` instance used by constructions
that need Mathlib's bundled commutativity API, and it passes to every field in a tower under `L`.

The file also extends Mathlib's `IsAbelianGalois.sup` from two subextensions to an arbitrary
family: a compositum of abelian Galois subextensions is abelian Galois.

## Main results

* `TauCeti.isMulCommutative_galoisGroup_of_commute`
* `TauCeti.commute_of_tower`
* `IntermediateField.isAbelianGalois_iSup`
-/

public section

namespace TauCeti

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [IsGalois K L]

omit [IsGalois K L] in
/-- An explicit proof that a Galois group is commutative supplies Mathlib's bundled
`IsMulCommutative` structure on that group. -/
theorem isMulCommutative_galoisGroup_of_commute
    (hab : ∀ σ τ : L ≃ₐ[K] L, Commute σ τ) : IsMulCommutative (L ≃ₐ[K] L) :=
  .of_comm fun σ τ ↦ (hab σ τ).eq

open scoped IsMulCommutative in
/-- **Commutativity of the Galois group passes down a field tower.** Every subextension of an
abelian extension is abelian, so a proof that `Gal(L/K)` is commutative is already a proof that
`Gal(M/K)` is for every field `M` in a tower under `L`. -/
theorem commute_of_tower {M : Type*} [Field M] [Algebra K M] [Algebra M L]
    [IsScalarTower K M L] (hab : ∀ σ τ : L ≃ₐ[K] L, Commute σ τ)
    (σ τ : M ≃ₐ[K] M) :
    Commute σ τ := by
  let _ := isMulCommutative_galoisGroup_of_commute hab
  have : IsAbelianGalois K L := {}
  have : IsAbelianGalois K M := .tower_bot K M L
  exact Commute.all σ τ

section iSup

open IntermediateField

variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]

/-- Two automorphisms of a compositum of abelian Galois subextensions commute on each of them. -/
private theorem mul_apply_eq_mul_apply_of_isAbelianGalois {ι : Type*}
    (E : ι → IntermediateField K Ω) [∀ i, IsAbelianGalois K (E i)] (σ τ : Gal(↥(⨆ i, E i)/K))
    (i : ι) (x : Ω) (hx : x ∈ E i) :
    ((σ * τ) ⟨x, le_iSup E i hx⟩ : Ω) = ((τ * σ) ⟨x, le_iSup E i hx⟩ : Ω) := by
  -- An automorphism of the compositum maps `E i` into itself, and its restriction there is the
  -- restriction of automorphisms of `E i`, whose Galois group is commutative.
  -- Read `E i` as an intermediate field of the compositum.
  let E' : IntermediateField K ↥(⨆ i, E i) := IntermediateField.restrict (le_iSup E i)
  have : IsAbelianGalois K E' :=
    .of_algHom (IntermediateField.restrictAlgEquiv (le_iSup E i)).symm.toAlgHom
  have hcomm : AlgEquiv.restrictNormalHom E' (σ * τ) = AlgEquiv.restrictNormalHom E' (τ * σ) := by
    rw [map_mul, map_mul, mul_comm']
  have hx' : (⟨x, le_iSup E i hx⟩ : ↥(⨆ i, E i)) ∈ E' := (mem_restrict _ _).mpr hx
  have h := congrArg (fun ρ : Gal(E'/K) ↦ ((ρ ⟨_, hx'⟩ : ↥(⨆ i, E i)) : Ω)) hcomm
  simpa only [AlgEquiv.restrictNormalHom_apply, AlgEquiv.restrictNormal_commutes] using h

/-- **The compositum of abelian Galois subextensions is abelian Galois.** This extends
`IsAbelianGalois.sup` from two subextensions to an arbitrary family. -/
instance _root_.IntermediateField.isAbelianGalois_iSup {ι : Type*} (E : ι → IntermediateField K Ω)
    [∀ i, IsAbelianGalois K (E i)] : IsAbelianGalois K ↥(⨆ i, E i) := by
  -- It is Galois as a compositum of Galois extensions, and two automorphisms of it commute
  -- because they commute on each `E i`, and those generate it.
  have : IsGalois K ↥(⨆ i, E i) := ⟨⟩
  refine { is_comm := ⟨fun σ τ ↦ ?_⟩ }
  -- Two automorphisms of the compositum agree once they agree on a generating set, here the
  -- union of the `E i`.
  have h := algHom_ext_of_eq_adjoin K (S := ⨆ i, E i) (s := ⋃ i, (E i : Set Ω))
    (by rw [iSup_eq_adjoin])
    (φ₁ := (⨆ i, E i).val.comp (σ * τ).toAlgHom)
    (φ₂ := (⨆ i, E i).val.comp (τ * σ).toAlgHom) (fun x hx ↦ by
      obtain ⟨i, hxE⟩ := Set.mem_iUnion.mp hx
      exact mul_apply_eq_mul_apply_of_isAbelianGalois E σ τ i x hxE)
  exact AlgEquiv.ext fun x ↦ Subtype.ext (AlgHom.congr_fun h x)

end iSup

end TauCeti
