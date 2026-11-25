/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.IsIso
public import TauCeti.AlgebraicGeometry.Grassmannian.Proper
public import TauCeti.AlgebraicGeometry.Grassmannian.Relative.Basic
public import TauCeti.AlgebraicGeometry.Modules.FinitePresentation.Basic
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Global properties of the relative Grassmannian

Let `E` be a quasi-coherent `𝒪_X`-module on a scheme `X` and `k` a natural number. Over each
affine open `U` of `X`, the relative Grassmannian
`AlgebraicGeometry.Scheme.Modules.grassmannian E k` is the Grassmannian `G(k, Γ(E, U))` over
`Spec Γ(X, U)` (`AlgebraicGeometry.Scheme.Modules.isPullback_grassmannianι_fromSpec`). So a
property of morphisms that is local on the target holds for its structure morphism to `X` exactly
when it holds for the structure morphisms `G(k, Γ(E, U)) ⟶ Spec Γ(X, U)`
(`AlgebraicGeometry.Scheme.Modules.grassmannianToBase_iff`). From the properties of the
Grassmannian of a module this gives:

* the relative Grassmannian is separated over `X`;
* it is proper over `X` when `E` is of finite type, and locally of finite presentation when `E` is
  of finite presentation;
* `G(0, E) ⟶ X` is an isomorphism, and so is `G(n, E) ⟶ X` when the sections of `E` over the
  affine opens are projective of constant rank `n`;
* the relative Grassmannian is empty when the sections of `E` over the affine opens are flat of
  rank less than `k`.

For `E = 𝒪_X^n` these are the computations `G(0, 𝒪_X^n) = X`, `G(n, 𝒪_X^n) = X` and
`G(k, 𝒪_X^n) = ∅` for `k > n`.

## Main results

* `AlgebraicGeometry.Scheme.Modules.grassmannianToBase_iff`: a property local on the target holds
  for `G(k, E) ⟶ X` exactly when it holds over every affine open.
* `AlgebraicGeometry.Scheme.Modules.isSeparated_grassmannianToBase`,
  `AlgebraicGeometry.Scheme.Modules.isProper_grassmannianToBase`,
  `AlgebraicGeometry.Scheme.Modules.locallyOfFinitePresentation_grassmannianToBase`: separatedness,
  properness and local finite presentation.
* `AlgebraicGeometry.Scheme.Modules.isIso_grassmannianToBase_zero`,
  `AlgebraicGeometry.Scheme.Modules.isIso_grassmannianToBase_of_rankAtStalk_eq`,
  `AlgebraicGeometry.Scheme.Modules.isEmpty_grassmannian_of_rankAtStalk_lt`: the extreme ranks.

## References

* A. Grothendieck, J. Dieudonné, *Éléments de géométrie algébrique I* (Springer, 1971), 9.7.
-/

public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} (E : X.Modules) [E.IsQuasicoherent] (k : ℕ)

/-- **Locality on the base.** A property of morphisms local on the target holds for the structure
morphism `G(k, E) ⟶ X` of the relative Grassmannian exactly when it holds for the structure
morphisms `G(k, Γ(E, U)) ⟶ Spec Γ(X, U)` over the affine opens `U` of `X`. -/
theorem grassmannianToBase_iff (P : MorphismProperty Scheme.{u}) [IsZariskiLocalAtTarget P] :
    P (grassmannianToBase E k) ↔
      ∀ U : X.affineOpens, P (Module.Grassmannian.toSpec Γ(X, U.val) Γ(E, U.val) k) := by
  refine ⟨fun h U ↦ ?_, fun h ↦ ?_⟩
  · have := U.property.isOpenImmersion_fromSpec
    exact IsZariskiLocalAtTarget.of_isPullback (isPullback_grassmannianι_fromSpec E k U).flip h
  refine IsZariskiLocalAtTarget.of_iSup_eq_top (fun U : X.affineOpens ↦ U.val)
    (iSup_affineOpens_eq_top X) fun U ↦ ?_
  -- Over `U`, the restriction of `G(k, E) ⟶ X` and `G(k, Γ(E, U)) ⟶ Spec Γ(X, U) ≅ U` are two
  -- pullbacks of the same cospan.
  have h₁ := isPullback_grassmannianι E k U
  let e := h₁.isoIsPullback _ _ (isPullback_morphismRestrict (grassmannianToBase E k) U.val)
  rw [← P.cancel_left_of_respectsIso e.hom, h₁.isoIsPullback_hom_fst,
    P.cancel_right_of_respectsIso]
  exact h U

/-- The relative Grassmannian of a quasi-coherent sheaf is separated over the base. -/
instance isSeparated_grassmannianToBase : IsSeparated (grassmannianToBase E k) :=
  (grassmannianToBase_iff E k @IsSeparated).mpr fun _ ↦ inferInstance

/-- The relative Grassmannian of a quasi-coherent sheaf of finite type is proper over the base. -/
instance isProper_grassmannianToBase [E.IsFiniteType] : IsProper (grassmannianToBase E k) :=
  (grassmannianToBase_iff E k @IsProper).mpr fun U ↦
    have := E.finite_sections_of_isAffineOpen U.val U.property
    inferInstance

/-- The relative Grassmannian of a finitely presented sheaf is locally of finite presentation over
the base. -/
instance locallyOfFinitePresentation_grassmannianToBase [E.IsFinitePresentation] :
    LocallyOfFinitePresentation (grassmannianToBase E k) :=
  have := HasRingHomProperty.instIsZariskiLocalAtTarget (P := @LocallyOfFinitePresentation)
  (grassmannianToBase_iff E k @LocallyOfFinitePresentation).mpr fun U ↦
    have := E.finitePresentation_sections_of_isAffineOpen U.val U.property
    inferInstance

/-- The relative Grassmannian of rank-zero quotients is the base: `G(0, E) ⟶ X` is an
isomorphism. -/
instance isIso_grassmannianToBase_zero : IsIso (grassmannianToBase E 0) :=
  (grassmannianToBase_iff E 0 (MorphismProperty.isomorphisms _)).mpr fun _ ↦
    (MorphismProperty.isomorphisms.iff _).mpr inferInstance

variable {E k}

/-- If the sections of a sheaf of finite type over the affine opens are projective of constant
rank `k`, the relative Grassmannian `G(k, E) ⟶ X` is an isomorphism. -/
theorem isIso_grassmannianToBase_of_rankAtStalk_eq [E.IsFiniteType]
    (hE : ∀ U : X.affineOpens, Module.Projective Γ(X, U.val) Γ(E, U.val))
    (h : ∀ (U : X.affineOpens) p, Module.rankAtStalk (R := Γ(X, U.val)) Γ(E, U.val) p = k) :
    IsIso (grassmannianToBase E k) :=
  (MorphismProperty.isomorphisms.iff _).mp <|
    (grassmannianToBase_iff E k (MorphismProperty.isomorphisms _)).mpr fun U ↦
      have := E.finite_sections_of_isAffineOpen U.val U.property
      have := hE U
      (MorphismProperty.isomorphisms.iff _).mpr
        (Module.Grassmannian.isIso_toSpec_of_rankAtStalk_eq (h U))

/-- If the sections of a sheaf of finite type over the affine opens are flat of rank less than
`k`, the relative Grassmannian `G(k, E)` is empty. -/
theorem isEmpty_grassmannian_of_rankAtStalk_lt [E.IsFiniteType]
    (hE : ∀ U : X.affineOpens, Module.Flat Γ(X, U.val) Γ(E, U.val))
    (h : ∀ (U : X.affineOpens) p, Module.rankAtStalk (R := Γ(X, U.val)) Γ(E, U.val) p < k) :
    IsEmpty (grassmannian E k) := by
  refine ⟨fun x ↦ ?_⟩
  -- The point `x` lies over an affine open `U`, hence in the Grassmannian `G(k, Γ(E, U))`.
  obtain ⟨U, hU⟩ := TopologicalSpace.Opens.mem_iSup.mp
    ((iSup_affineOpens_eq_top X).ge (Set.mem_univ (grassmannianToBase E k x)))
  have := E.finite_sections_of_isAffineOpen U.val U.property
  have := hE U
  have := Module.Grassmannian.isEmpty_scheme_of_rankAtStalk_lt (h U)
  obtain ⟨z, -, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := U.val.ι)
    (g := grassmannianToBase E k) ⟨_, hU⟩ x rfl
  exact isEmptyElim ((isPullback_grassmannianι E k U).isoPullback.inv z)

end AlgebraicGeometry.Scheme.Modules
