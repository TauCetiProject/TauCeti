/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.DifferentialOperator.Basic
public import TauCeti.AlgebraicGeometry.Modules.AffineGlobalSections

/-!
# Differential operators on the spectrum of a localization of the base ring

Let `k` be a commutative ring and `X` an affine scheme over `Spec k` whose ring of global
sections is a localization of `k` at a submonoid `M`, for instance `X = Spec k`, or `Spec R` for a
localization `R` of `k`. Then `D_X = O_X`: every `k`-linear endomorphism of the structure sheaf
over an open `U` is multiplication by a unique section of `O_X` over `U`.

Indeed, on a basic open `D(g)` the sections of `O_X` are the localization of `Γ(X, ⊤)` at `g`,
and a `k`-linear map between modules over them is `Γ(X, ⊤)`-linear and then linear over the
sections on `D(g)` (`IsLocalization.linearMap_compatibleSMul`, applied twice), so it has order
zero. Since the basic opens form a basis of `X` and the order is local
(`Scheme.endApp_mem_differentialOperators_of_le_iSup`), every endomorphism has order zero on
every open. Hence the filtration of `D_X` is constant, `F_m D_X = F_0 D_X`, and the ring map
`Scheme.toPresheafOfDifferentialOperators` from `O_X` to `D_X` is an isomorphism of presheaves of
rings. Both hypotheses are needed: the derivative on the affine line `Spec k[X]`
(`TauCeti.derivativeEnd`) and the global vector fields on the projective line over a nonzero
ring `k`, whose global sections are `k`, have order one and not zero.

## Main results

* `Scheme.mem_differentialOperators_zero_of_isLocalization`: every `k`-linear endomorphism of
  the structure sheaf over an open `U` has order zero.
* `Scheme.bijective_toStructureEnd_of_isLocalization`: every such endomorphism is multiplication
  by a unique section of `O_X` over `U`.
* `Scheme.differentialOperators_eq_differentialOperators_zero_of_isLocalization`:
  `F_m D_X = F_0 D_X` for every `m`.
* `Scheme.differentialOperatorsSubring_eq_top_of_isLocalization`: every endomorphism is a
  differential operator.
* `Scheme.isIso_toPresheafOfDifferentialOperators_of_isLocalization`: `O_X → D_X` is an
  isomorphism of presheaves of rings; for `X = Spec k` this is the instance
  `Scheme.isIso_toPresheafOfDifferentialOperators_spec`.

The `k`-algebra structure on sections is `Scheme.algebraOfOver`, activated locally in this file
as in `TauCeti.AlgebraicGeometry.DifferentialOperator.Basic`.

## References

* A. Grothendieck, *Éléments de géométrie algébrique IV*, Quatrième partie, §16.8.
-/

public section

open CategoryTheory Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

attribute [local instance] algebraOfOver

variable {k : Type u} [CommRing k]

section Affine

variable {X : Scheme.{u}} [X.Over (Spec (.of k))] [IsAffine X] (M : Submonoid k)
  [IsLocalization M Γ(X, ⊤)]

include M

/-- On a basic open `D(g)` of an affine scheme over `Spec k` whose global sections are a
localization of `k`, every `k`-linear endomorphism of the sections has order zero: the sections
are a localization of the global sections, so a `k`-linear map between them is linear over the
global sections, and then over the sections on `D(g)`. -/
private theorem mem_differentialOperators_zero_basicOpen (g : Γ(X, ⊤))
    (L : Γ(X, X.basicOpen g) →ₗ[k] Γ(X, X.basicOpen g)) :
    L ∈ TauCeti.differentialOperators k Γ(X, X.basicOpen g) Γ(X, X.basicOpen g)
      Γ(X, X.basicOpen g) 0 := by
  -- `Γ(X, ⊤)` acts on `Γ(X, X.basicOpen g)` through restriction, which is `k`-linear
  have : IsScalarTower k Γ(X, ⊤) Γ(X, X.basicOpen g) :=
    .of_algebraMap_eq fun c ↦ (presheaf_map_algebraMap _ c).symm
  have := IsLocalization.linearMap_compatibleSMul M Γ(X, ⊤) Γ(X, X.basicOpen g)
    Γ(X, X.basicOpen g)
  have := IsLocalization.linearMap_compatibleSMul (.powers g) Γ(X, X.basicOpen g)
    Γ(X, X.basicOpen g) Γ(X, X.basicOpen g)
  exact TauCeti.mem_differentialOperators_zero_iff.2 fun a x ↦
    ((L.restrictScalars Γ(X, ⊤)).restrictScalars Γ(X, X.basicOpen g)).map_smul a x

/-- On an affine scheme over `Spec k` whose global sections are a localization of `k`, every
`k`-linear endomorphism of the structure sheaf over an open `U` has order zero. -/
theorem mem_differentialOperators_zero_of_isLocalization {U : X.Opens} (D : X.StructureEnd k U) :
    D ∈ (X.differentialOperators k 0).obj (op U) :=
  -- the order is detected on the basic opens contained in `V`, which cover `V`
  mem_differentialOperators_iff.2 fun V ↦ endApp_mem_differentialOperators_of_le_iSup D V
    (fun g : {g : Γ(X, ⊤) // X.basicOpen g ≤ V.left} ↦
      Over.mk (homOfLE (g.property.trans V.hom.le)))
    (fun g ↦ Over.homMk (homOfLE g.property))
    (fun x hx ↦ by
      obtain ⟨_, ⟨g, rfl⟩, hxg, hgV⟩ := Opens.isBasis_iff_nbhd.1 (isBasis_basicOpen X) hx
      exact Opens.mem_iSup.2 ⟨⟨g, hgV⟩, hxg⟩)
    fun g ↦ mem_differentialOperators_zero_basicOpen M g.val _

/-- On an affine scheme over `Spec k` whose global sections are a localization of `k`, every
`k`-linear endomorphism of the structure sheaf over an open `U` is multiplication by a unique
section over `U`. -/
theorem bijective_toStructureEnd_of_isLocalization (U : X.Opens) :
    Function.Bijective (X.toStructureEnd k U) :=
  ⟨toStructureEnd_injective U, fun D ↦
    mem_differentialOperators_zero_iff.1 (mem_differentialOperators_zero_of_isLocalization M D)⟩

variable (X) in
/-- On an affine scheme over `Spec k` whose global sections are a localization of `k`, the
filtration of the sheaf of differential operators is constant: `F_m D_X = F_0 D_X`. -/
theorem differentialOperators_eq_differentialOperators_zero_of_isLocalization (m : ℕ) :
    X.differentialOperators k m = X.differentialOperators k 0 :=
  le_antisymm (fun _ D _ ↦ mem_differentialOperators_zero_of_isLocalization M D)
    (differentialOperators_mono (Nat.zero_le m))

variable (X) in
/-- On an affine scheme over `Spec k` whose global sections are a localization of `k`, every
`k`-linear endomorphism of the structure sheaf is a differential operator. -/
theorem differentialOperatorsSubring_eq_top_of_isLocalization (U : X.Opens) :
    X.differentialOperatorsSubring k U = ⊤ :=
  eq_top_iff.2 fun D _ ↦
    mem_differentialOperatorsSubring_of_mem (mem_differentialOperators_zero_of_isLocalization M D)

variable (X) in
/-- On an affine scheme over `Spec k` whose global sections are a localization of `k`,
`D_X = O_X`: the ring map from the structure sheaf to the sheaf of differential operators is an
isomorphism of presheaves of rings. -/
theorem isIso_toPresheafOfDifferentialOperators_of_isLocalization :
    IsIso (X.toPresheafOfDifferentialOperators k) := by
  have (U : X.Opensᵒᵖ) : IsIso ((X.toPresheafOfDifferentialOperators k).app U) := by
    refine (ConcreteCategory.isIso_iff_bijective _).2 ⟨fun f g h ↦ ?_, fun D ↦ ?_⟩
    · have h' := congrArg Subtype.val h
      rw [coe_toPresheafOfDifferentialOperators_app_apply,
        coe_toPresheafOfDifferentialOperators_app_apply] at h'
      exact (bijective_toStructureEnd_of_isLocalization M U.unop).1 h'
    · obtain ⟨f, hf⟩ := (bijective_toStructureEnd_of_isLocalization M U.unop).2 D.val
      exact ⟨f, Subtype.ext ((coe_toPresheafOfDifferentialOperators_app_apply U f).trans hf)⟩
  exact NatIso.isIso_of_isIso_app _

end Affine

variable (M : Submonoid k)

/-! ### Spectra of localizations of the base ring -/

/-- For a localization `R` of `k`, the global sections of `Spec R` over `Spec k` are a
localization of `k` at the same submonoid. -/
instance isLocalization_spec_top (R : CommRingCat.{u}) [Algebra k R] [IsLocalization M R] :
    IsLocalization M Γ(Spec R, ⊤) :=
  -- `algebraMap R Γ(Spec R, ⊤)` is the inverse of `Scheme.ΓSpecIso R`, followed by the
  -- restriction from `⊤` to itself (`algebraMap_Spec_obj`)
  IsLocalization.isLocalization_of_algEquiv M (AlgEquiv.ofBijective
    (IsScalarTower.toAlgHom k R Γ(Spec R, ⊤))
    (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv.symm.bijective)

/-- The global sections of `Spec k` over itself are `k`, the localization of `k` at the trivial
submonoid. -/
instance isLocalization_bot_spec_top : IsLocalization (⊥ : Submonoid k) Γ(Spec (.of k), ⊤) :=
  have : IsLocalization (⊥ : Submonoid k) (CommRingCat.of k) := IsLocalization.self bot_le
  isLocalization_spec_top ⊥ (.of k)

/-- `D_X = O_X` for `X = Spec k`: the ring map from the structure sheaf to the sheaf of
differential operators is an isomorphism of presheaves of rings. -/
instance isIso_toPresheafOfDifferentialOperators_spec :
    IsIso ((Spec (.of k)).toPresheafOfDifferentialOperators k) :=
  isIso_toPresheafOfDifferentialOperators_of_isLocalization _ ⊥

end AlgebraicGeometry.Scheme
