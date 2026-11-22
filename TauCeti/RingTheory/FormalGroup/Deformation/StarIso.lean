/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.FormalGroup.Deformation.Basic
public import TauCeti.RingTheory.FormalGroup.Rigidity
-- Proof-only: characteristic transfer along injective ring homomorphisms and the embedding of the
-- residue field defined by a local homomorphism to a field.
import Mathlib.Algebra.CharP.Algebra
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# ⋆-isomorphisms of formal group laws

Fix a coefficient homomorphism `π : A →+* k`. An isomorphism `e : F ≅ G` of formal group laws
over `A` is a **⋆-isomorphism relative to `π`** (`TauCeti.FormalGroupIso.IsStarIso`) when its
forward series reduces along `π` to the identity series `X`. These are the isomorphisms by which
Lubin and Tate identify two deformations of a formal group law over `k`: the reduction of a
⋆-isomorphism is the identity of the common special fibre, so ⋆-isomorphic laws have the same
reduction (`TauCeti.FormalGroupIso.IsStarIso.map_eq`), whereas an arbitrary isomorphism between
laws with equal reductions need not reduce to `X`.

⋆-isomorphisms contain the identities and are closed under composition, inverses and base change
along homomorphisms compatible with the maps to `k`. Two lifts of a commutative law `F₀` define
the same deformation (`TauCeti.FormalGroupDeformation`) exactly when a ⋆-isomorphism joins them
(`TauCeti.FormalGroupDeformation.mk_eq_mk_iff_exists_isStarIso`), since the isomorphism attached
to a change of coordinate `φ` is a ⋆-isomorphism exactly when `φ` reduces to the identity
coordinate (`FormalGroup.isStarIso_smulIso_iff`). For instance, the homothety `X ↦ u X` is a
⋆-isomorphism exactly when `π u = 1` (`FormalGroup.isStarIso_smulIso_homothety_iff`); applied to
the multiplicative law, the homothety from `X + Y + X Y` to `X + Y + u⁻¹ X Y` is a ⋆-isomorphism
precisely when `u` reduces to `1`.

Over an `𝔪`-adically Hausdorff local ring `A` with `π` a local homomorphism to a field of
characteristic `p`, a ⋆-isomorphism between commutative laws is unique when the reduction of the
source has finite height (`TauCeti.FormalGroupIso.eq_of_isStarIso`), by Lubin–Tate rigidity
`TauCeti.FormalGroupIso.eq_of_map_residue_eq`. Hence deformations of a law of finite height have
no nontrivial ⋆-automorphisms.

## Main definitions

* `TauCeti.FormalGroupIso.IsStarIso π e`: the forward series of `e` reduces along `π` to `X`.

## Main results

* `TauCeti.FormalGroupIso.IsStarIso.map_eq`: ⋆-isomorphic laws have the same reduction.
* `TauCeti.FormalGroupIso.IsStarIso.map`: base change of ⋆-isomorphisms.
* `TauCeti.FormalGroupIso.isStarIso_comp_iff`: the ⋆ condition is unchanged by an injective
  homomorphism of residue rings.
* `FormalGroup.isStarIso_smulIso_iff`: the isomorphism `F ≅ φ • F` is ⋆ exactly when `φ` reduces
  to the identity coordinate.
* `TauCeti.FormalGroupDeformation.mk_eq_mk_iff_exists_isStarIso`: deformations are lifts modulo
  ⋆-isomorphism.
* `TauCeti.FormalGroupIso.eq_of_isStarIso`: uniqueness of ⋆-isomorphisms in finite height.

## References

* J. Lubin and J. Tate, *Formal moduli for one-parameter formal Lie groups*, Bull. Soc. Math.
  France 94 (1966), §1 and Proposition 2.4.
-/

public section

open PowerSeries

namespace TauCeti

namespace FormalGroupIso

variable {A B k k' : Type*} [CommRing A] [CommRing B] [CommRing k] [CommRing k']
  {F G H : FormalGroup A}

/-- An isomorphism `e` of formal group laws over `A` is a **⋆-isomorphism relative to
`π : A →+* k`** when its forward series reduces along `π` to the identity series `X`
(Lubin–Tate). -/
class IsStarIso (π : A →+* k) (e : FormalGroupIso F G) : Prop where
  /-- The forward series reduces to `X`. -/
  map_toPowerSeries : e.toHom.toPowerSeries.map π = X

/-- `e` is a ⋆-isomorphism relative to `π` exactly when its forward series reduces to `X`. -/
theorem isStarIso_iff (π : A →+* k) (e : FormalGroupIso F G) :
    e.IsStarIso π ↔ e.toHom.toPowerSeries.map π = X :=
  ⟨fun h ↦ h.map_toPowerSeries, fun h ↦ ⟨h⟩⟩

variable {π : A →+* k}

/-- The identity isomorphism is a ⋆-isomorphism. -/
instance (π : A →+* k) (F : FormalGroup A) : (refl F).IsStarIso π where
  map_toPowerSeries := by simp

/-- A composite of ⋆-isomorphisms is a ⋆-isomorphism. -/
instance (e : FormalGroupIso F G) (e' : FormalGroupIso G H) [e.IsStarIso π] [e'.IsStarIso π] :
    (e.trans e').IsStarIso π where
  map_toPowerSeries := by
    rw [trans_toHom, ← FormalGroupHom.map_toPowerSeries, FormalGroupHom.map_comp,
      FormalGroupHom.comp_toPowerSeries, FormalGroupHom.map_toPowerSeries,
      FormalGroupHom.map_toPowerSeries, IsStarIso.map_toPowerSeries,
      IsStarIso.map_toPowerSeries, subst_X HasSubst.X']

/-- The inverse series of a ⋆-isomorphism also reduces to `X`. -/
theorem IsStarIso.map_invHom_toPowerSeries (e : FormalGroupIso F G) [e.IsStarIso π] :
    e.invHom.toPowerSeries.map π = X := by
  have h := (e.map π).subst_toHom_invHom
  rwa [map_toHom, map_invHom, FormalGroupHom.map_toPowerSeries,
    FormalGroupHom.map_toPowerSeries, IsStarIso.map_toPowerSeries, X_subst] at h

/-- The inverse of a ⋆-isomorphism is a ⋆-isomorphism. -/
instance (e : FormalGroupIso F G) [e.IsStarIso π] : e.symm.IsStarIso π where
  map_toPowerSeries := by
    rw [symm_toHom]
    exact IsStarIso.map_invHom_toPowerSeries e

/-- **⋆-isomorphic laws have the same reduction**: the reduced series `X` of a ⋆-isomorphism is a
homomorphism between the two reductions. -/
theorem IsStarIso.map_eq (e : FormalGroupIso F G) [e.IsStarIso π] : F.map π = G.map π := by
  have h := (e.toHom.map π).homDefect_toPowerSeries
  rw [FormalGroupHom.map_toPowerSeries, IsStarIso.map_toPowerSeries,
    FormalGroup.homDefect_X, sub_eq_zero] at h
  exact FormalGroup.ext h

/-- **Base change of ⋆-isomorphisms**: along a homomorphism `φ : A →+* B` compatible with the
maps `π : A →+* k` and `ρ : B →+* k`, a ⋆-isomorphism relative to `π` becomes one relative to
`ρ`. -/
theorem IsStarIso.map (e : FormalGroupIso F G) [e.IsStarIso π] {ρ : B →+* k} (φ : A →+* B)
    (h : ρ.comp φ = π) : (e.map φ).IsStarIso ρ where
  map_toPowerSeries := by
    rw [map_toHom, FormalGroupHom.map_toPowerSeries, ← RingHom.comp_apply, ← PowerSeries.map_comp,
      h, IsStarIso.map_toPowerSeries]

/-- **Changing the residue ring by an injective homomorphism** does not change the ⋆ condition:
`e` reduces to `X` along `ψ ∘ π` exactly when it does along `π`. -/
theorem isStarIso_comp_iff {ψ : k →+* k'} (hψ : Function.Injective ψ) (e : FormalGroupIso F G) :
    e.IsStarIso (ψ.comp π) ↔ e.IsStarIso π := by
  rw [isStarIso_iff, isStarIso_iff, PowerSeries.map_comp, RingHom.comp_apply, ← map_X ψ]
  exact (map_injective ψ hψ).eq_iff

open IsLocalRing in
/-- **Uniqueness of ⋆-isomorphisms** (Lubin–Tate rigidity). Let `A` be an `𝔪`-adically
Hausdorff local ring and `π : A →+* K` a local homomorphism to a field of characteristic `p`.
Two ⋆-isomorphisms relative to `π` between commutative formal group laws over `A` are equal,
provided the reduction of the source along `π` has finite height. -/
theorem eq_of_isStarIso [IsLocalRing A] [IsHausdorff (maximalIdeal A) A] [F.IsComm] [G.IsComm]
    {K : Type*} [Field K] {p : ℕ} [Fact p.Prime] [CharP K p] (π : A →+* K) [IsLocalHom π]
    (e₁ e₂ : FormalGroupIso F G) [e₁.IsStarIso π] [e₂.IsStarIso π] {h : ℕ}
    (hF : (F.map π).height p = h) : e₁ = e₂ := by
  -- `π` is the residue map followed by an embedding `ι` of the residue field into `K`.
  set ι := ResidueField.lift π
  have hι : ι.comp (residue A) = π := ResidueField.lift_comp_residue π
  have : CharP (ResidueField A) p := ι.charP ι.injective p
  have hres (e : FormalGroupIso F G) [e.IsStarIso π] :
      e.toHom.toPowerSeries.map (residue A) = X := by
    have : e.IsStarIso (ι.comp (residue A)) := hι ▸ ‹_›
    exact ((isStarIso_comp_iff ι.injective e).mp this).map_toPowerSeries
  refine e₁.eq_of_map_residue_eq e₂ (p := p) (h := h) ?_ ((hres e₁).trans (hres e₂).symm)
  rw [← (F.map (residue A)).height_map ι, FormalGroup.map_comp, hι, hF]

end FormalGroupIso

end TauCeti

namespace FormalGroup

open TauCeti

variable {A k : Type*} [CommRing A] [CommRing k] {π : A →+* k}

/-- The isomorphism `F ≅ φ • F` given by a formal coordinate `φ` is a ⋆-isomorphism exactly when
`φ` reduces to the identity coordinate. -/
theorem isStarIso_smulIso_iff (φ : FormalCoordinate A) (F : FormalGroup A) :
    (smulIso φ F).IsStarIso π ↔ FormalCoordinate.map π φ = 1 := by
  rw [FormalGroupIso.isStarIso_iff, smulIso_toHom_toPowerSeries, FormalCoordinate.ext_iff,
    FormalCoordinate.toPowerSeries_map, FormalCoordinate.toPowerSeries_one]

/-- The homothety `X ↦ u X`, an isomorphism from `F` to `F.rescale u⁻¹`, is a ⋆-isomorphism
exactly when `u` reduces to `1`. -/
theorem isStarIso_smulIso_homothety_iff (u : Aˣ) (F : FormalGroup A) :
    (smulIso (FormalCoordinate.homothety u) F).IsStarIso π ↔ π u = 1 := by
  rw [FormalGroupIso.isStarIso_iff, smulIso_toHom_toPowerSeries,
    FormalCoordinate.toPowerSeries_homothety]
  constructor
  · intro h
    simpa using congrArg (coeff 1) h
  · intro h
    ext n
    rcases eq_or_ne n 1 with rfl | hn
    · simp [h]
    · simp [coeff_X, hn]

end FormalGroup

namespace TauCeti.FormalGroupDeformation

variable {A k : Type*} [CommRing A] [CommRing k] {π : A →+* k} {F₀ : FormalGroup k}

/-- **Deformations are lifts modulo ⋆-isomorphism**: two lifts of `F₀` define the same deformation
exactly when some ⋆-isomorphism relative to `π` joins their laws. -/
theorem mk_eq_mk_iff_exists_isStarIso (F G : FormalGroupLift π F₀) :
    (⟦F⟧ : FormalGroupDeformation π F₀) = ⟦G⟧ ↔
      ∃ e : FormalGroupIso F.formalGroup G.formalGroup, e.IsStarIso π := by
  rw [mk_eq_mk_iff]
  constructor
  · rintro ⟨φ, hφ, hFG⟩
    rw [← hFG]
    exact ⟨FormalGroup.smulIso φ _, (FormalGroup.isStarIso_smulIso_iff φ _).mpr hφ⟩
  · rintro ⟨e, he⟩
    let φ : FormalCoordinate A :=
      { toPowerSeries := e.toHom.toPowerSeries
        constantCoeff_toPowerSeries := e.toHom.zero_constantCoeff
        isUnit_coeff_one := e.isUnit_coeff_one }
    refine ⟨φ, FormalCoordinate.ext ?_, e.toHom.smul_eq rfl⟩
    rw [FormalCoordinate.toPowerSeries_map, FormalCoordinate.toPowerSeries_one]
    exact he.map_toPowerSeries

end TauCeti.FormalGroupDeformation
