/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Localization
public import Mathlib.RingTheory.LocalProperties.Exactness
public import Mathlib.RingTheory.Localization.BaseChange

/-!
# Sections of quasi-coherent modules over nested affine opens

Let `M` be a quasi-coherent `𝒪_X`-module on a scheme `X` and let `V ≤ U` be affine opens of `X`.
Then restriction of sections exhibits `Γ(M, V)` as the base change of `Γ(M, U)` along the
restriction of functions `Γ(X, U) → Γ(X, V)`:

`Γ(X, V) ⊗[Γ(X, U)] Γ(M, U) ≅ Γ(M, V)`.

When `V` is a basic open `X.basicOpen f` of `U` this is the localization statement
`Scheme.Modules.isLocalizedModule_basicOpenRestrict`, and the general case is reduced to it: `V`
is covered by basic opens of `U`, which are also basic opens of `V`, and bijectivity of the
comparison map `Γ(X, V) ⊗[Γ(X, U)] Γ(M, U) → Γ(M, V)` can be checked after localizing at
functions on `V` generating the unit ideal (`bijective_of_isLocalized_span`).

The `Γ(X, U)`-algebra structure on `Γ(X, V)` and the `Γ(X, U)`-module structure on `Γ(M, V)` are
caller parameters, subject only to the algebra map being restriction of functions and the scalar
tower condition. This lets the statement apply both to the module structures on basic opens used
in `TauCeti.AlgebraicGeometry.Modules.Localization` and to those obtained by restriction of
scalars.

## Main declarations

* `AlgebraicGeometry.Scheme.Modules.isBaseChange_sectionsRestriction`: for a quasi-coherent `M`
  and affine opens `V ≤ U`, restriction `Γ(M, U) → Γ(M, V)` is a base change along
  `Γ(X, U) → Γ(X, V)`.

## References

* R. Hartshorne, *Algebraic Geometry*, Lemma II.5.3 and Proposition II.5.4.
* A. Grothendieck and J. Dieudonné, *Éléments de géométrie algébrique I* (1971),
  Théorème 1.4.1.
-/

public section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry TensorProduct

namespace TauCeti

universe u

noncomputable section

variable {X : Scheme.{u}} (M : X.Modules) {U V : X.Opens}

/-- Over a basic open `D = X.basicOpen f` of an affine open `U`, restriction `Γ(M, U) → Γ(M, D)` is
the base change along `Γ(X, U) → Γ(X, D)`, for any module structures compatible with
restriction. The open `D` is arbitrary up to the equality `X.basicOpen f = D`. -/
private theorem isBaseChange_sectionsRestriction_basicOpen [M.IsQuasicoherent]
    (hU : IsAffineOpen U) (f : Γ(X, U)) {D : X.Opens} (hD : X.basicOpen f = D) (hDU : D ≤ U)
    [Algebra Γ(X, U) Γ(X, D)] [Module Γ(X, U) Γ(M, D)] [IsScalarTower Γ(X, U) Γ(X, D) Γ(M, D)]
    (hA : ∀ r, algebraMap Γ(X, U) Γ(X, D) r = X.presheaf.map (homOfLE hDU).op r)
    (ρ : Γ(M, U) →ₗ[Γ(X, U)] Γ(M, D)) (hρ : ∀ s, ρ s = M.presheaf.map (homOfLE hDU).op s) :
    IsBaseChange Γ(X, D) ρ := by
  subst hD
  -- Replace the given structures by the canonical ones on basic opens.
  obtain rfl :
      ‹Algebra Γ(X, U) Γ(X, X.basicOpen f)› = Scheme.algebra_section_section_basicOpen f :=
    Algebra.algebra_ext _ _ hA
  obtain rfl : ‹Module Γ(X, U) Γ(M, X.basicOpen f)› = M.moduleBasicOpen f :=
    Module.ext' _ _ fun r s ↦ (algebraMap_smul Γ(X, X.basicOpen f) r s).symm
  obtain rfl : ρ = M.basicOpenRestrict f :=
    LinearMap.ext fun s ↦ (hρ s).trans (M.basicOpenRestrict_apply f s).symm
  have : IsLocalization.Away f Γ(X, X.basicOpen f) := hU.isLocalization_basicOpen f
  exact (isLocalizedModule_iff_isBaseChange (Submonoid.powers f) Γ(X, X.basicOpen f) _).mp
    (M.isLocalizedModule_basicOpenRestrict hU f)

/-- The functions on an affine open `V ≤ U` that are restrictions of functions on `U` whose basic
open lies in `V` generate the unit ideal of `Γ(X, V)`. -/
private theorem span_restrict_basicOpen_le_eq_top (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (hVU : V ≤ U) :
    Ideal.span {g : Γ(X, V) | ∃ f : Γ(X, U), X.basicOpen f ≤ V ∧
      X.presheaf.map (homOfLE hVU).op f = g} = ⊤ := by
  refine (hV.self_le_iSup_basicOpen_iff).mp fun x hx ↦ ?_
  obtain ⟨f, hfV, hxf⟩ := hU.exists_basicOpen_le ⟨x, hx⟩ (hVU hx)
  refine TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨_, f, hfV, rfl⟩, ?_⟩
  rw [Scheme.basicOpen_res]
  exact ⟨hx, hxf⟩

variable [Algebra Γ(X, U) Γ(X, V)] [Module Γ(X, U) Γ(M, V)]
  [IsScalarTower Γ(X, U) Γ(X, V) Γ(M, V)]

/-- Let `V ≤ U` be affine and let `g = f|_V` for a function `f` on `U` whose basic open lies in `V`.
The comparison map `Γ(X, V) ⊗[Γ(X, U)] Γ(M, U) → Γ(M, V)` followed by the localization
`Γ(M, V) → Γ(M, X.basicOpen g)` is a localization away from `g`: it is the localization
`Γ(X, V) ⊗[Γ(X, U)] Γ(M, U) → Γ(X, X.basicOpen g) ⊗[Γ(X, U)] Γ(M, U)` followed by the base-change
isomorphism for the basic open `X.basicOpen g = X.basicOpen f` of `U`. -/
private theorem isLocalizedModule_basicOpenRestrict_comp_liftBaseChange [M.IsQuasicoherent]
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hVU : V ≤ U)
    (hA : ∀ r, algebraMap Γ(X, U) Γ(X, V) r = X.presheaf.map (homOfLE hVU).op r)
    (ρ : Γ(M, U) →ₗ[Γ(X, U)] Γ(M, V)) (hρ : ∀ s, ρ s = M.presheaf.map (homOfLE hVU).op s)
    {f : Γ(X, U)} (hfV : X.basicOpen f ≤ V) :
    IsLocalizedModule.Away (X.presheaf.map (homOfLE hVU).op f)
      (M.basicOpenRestrict (X.presheaf.map (homOfLE hVU).op f) ∘ₗ ρ.liftBaseChange Γ(X, V)) := by
  set g := X.presheaf.map (homOfLE hVU).op f
  have hD : X.basicOpen f = X.basicOpen g := by
    rw [Scheme.basicOpen_res, inf_eq_right.mpr hfV]
  -- `Γ(X, X.basicOpen g)` and `Γ(M, X.basicOpen g)` as a `Γ(X, U)`-algebra and module through
  -- `Γ(X, V)`.
  let := ((algebraMap Γ(X, V) Γ(X, X.basicOpen g)).comp (algebraMap Γ(X, U) Γ(X, V))).toAlgebra
  have : IsScalarTower Γ(X, U) Γ(X, V) Γ(X, X.basicOpen g) := .of_algebraMap_eq fun _ ↦ rfl
  let := Module.compHom Γ(M, X.basicOpen g) (algebraMap Γ(X, U) Γ(X, X.basicOpen g))
  -- By definition of `Module.compHom`, `r` acts through its image in `Γ(X, X.basicOpen g)`.
  have : IsScalarTower Γ(X, U) Γ(X, X.basicOpen g) Γ(M, X.basicOpen g) :=
    .of_algebraMap_smul fun _ _ ↦ rfl
  have : IsScalarTower Γ(X, U) Γ(X, V) Γ(M, X.basicOpen g) :=
    .of_algebraMap_smul fun r x ↦ by
      rw [← algebraMap_smul Γ(X, X.basicOpen g) (algebraMap Γ(X, U) Γ(X, V) r) x,
        ← IsScalarTower.algebraMap_apply]
      rfl
  let ρD : Γ(M, U) →ₗ[Γ(X, U)] Γ(M, X.basicOpen g) :=
    (M.basicOpenRestrict g).restrictScalars Γ(X, U) ∘ₗ ρ
  have hρD : IsBaseChange Γ(X, X.basicOpen g) ρD := by
    refine isBaseChange_sectionsRestriction_basicOpen M hU f hD
      ((X.basicOpen_le g).trans hVU) (fun r ↦ ?_) ρD fun x ↦ ?_
    · rw [IsScalarTower.algebraMap_apply Γ(X, U) Γ(X, V), hA]
      exact (X.presheaf.map_comp_apply _ _ r).symm
    · simp only [ρD, LinearMap.comp_apply, LinearMap.restrictScalars_apply, hρ,
        Scheme.Modules.basicOpenRestrict_apply]
      exact (M.presheaf.map_comp_apply _ _ x).symm
  have : IsLocalization.Away g Γ(X, X.basicOpen g) := hV.isLocalization_basicOpen g
  have : IsLocalizedModule (Submonoid.powers g) (Algebra.linearMap Γ(X, V) Γ(X, X.basicOpen g)) :=
    isLocalizedModule_iff_isLocalization.mpr inferInstance
  convert IsLocalizedModule.of_linearEquiv (Submonoid.powers g)
    (AlgebraTensorModule.rTensor Γ(X, U) Γ(M, U) (Algebra.linearMap Γ(X, V) Γ(X, X.basicOpen g)))
    (hρD.equiv.restrictScalars Γ(X, V)) using 1
  refine TensorProduct.AlgebraTensorModule.ext fun a x ↦ ?_
  simp only [LinearMap.comp_apply, LinearMap.liftBaseChange_tmul, LinearEquiv.coe_coe,
    LinearEquiv.restrictScalars_apply, AlgebraTensorModule.rTensor_tmul, Algebra.linearMap_apply,
    IsBaseChange.equiv_tmul, map_smul]
  exact (algebraMap_smul Γ(X, X.basicOpen g) a _).symm

/-- **Sections of a quasi-coherent module over nested affine opens.** For a quasi-coherent
`𝒪_X`-module `M` and affine opens `V ≤ U`, restriction of sections `Γ(M, U) → Γ(M, V)` exhibits
`Γ(M, V)` as the base change of `Γ(M, U)` along the restriction of functions
`Γ(X, U) → Γ(X, V)`. The module structures are any ones compatible with restriction. -/
theorem _root_.AlgebraicGeometry.Scheme.Modules.isBaseChange_sectionsRestriction
    [M.IsQuasicoherent] (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hVU : V ≤ U)
    (hA : ∀ r, algebraMap Γ(X, U) Γ(X, V) r = X.presheaf.map (homOfLE hVU).op r)
    (ρ : Γ(M, U) →ₗ[Γ(X, U)] Γ(M, V)) (hρ : ∀ s, ρ s = M.presheaf.map (homOfLE hVU).op s) :
    IsBaseChange Γ(X, V) ρ := by
  let s : Set Γ(X, V) := {g | ∃ f : Γ(X, U), X.basicOpen f ≤ V ∧
    X.presheaf.map (homOfLE hVU).op f = g}
  -- The comparison map `F : Γ(X, V) ⊗[Γ(X, U)] Γ(M, U) → Γ(M, V)` is bijective, because it is so
  -- after localizing at the elements of `s`, which generate the unit ideal.
  let F : Γ(X, V) ⊗[Γ(X, U)] Γ(M, U) →ₗ[Γ(X, V)] Γ(M, V) := ρ.liftBaseChange Γ(X, V)
  suffices hF : Function.Bijective F from IsBaseChange.of_equiv (.ofBijective F hF) fun x ↦ by
    rw [LinearEquiv.ofBijective_apply, LinearMap.liftBaseChange_tmul, one_smul]
  let G (g : s) : Γ(M, V) →ₗ[Γ(X, V)] Γ(M, X.basicOpen g.1) := M.basicOpenRestrict g.1
  have _ (g : s) : IsLocalizedModule.Away g.1 (G g) := M.isLocalizedModule_basicOpenRestrict hV g.1
  have _ : ∀ g : s, IsLocalizedModule.Away g.1 (G g ∘ₗ F) := by
    rintro ⟨_, f, hfV, rfl⟩
    exact isLocalizedModule_basicOpenRestrict_comp_liftBaseChange M hU hV hVU hA ρ hρ hfV
  refine bijective_of_isLocalized_span s (span_restrict_basicOpen_le_eq_top hU hV hVU)
    (fun g ↦ Γ(M, X.basicOpen g.1)) (fun g ↦ G g ∘ₗ F) (fun g ↦ Γ(M, X.basicOpen g.1)) G F
    fun g ↦ ?_
  -- Both localizations of `F` at `g` land in `Γ(M, X.basicOpen g)`, where the localized map is
  -- the identity.
  have h : IsLocalizedModule.map (Submonoid.powers g.1) (G g ∘ₗ F) (G g) F = LinearMap.id :=
    IsLocalizedModule.linearMap_ext (Submonoid.powers g.1) (G g ∘ₗ F) (G g ∘ₗ F)
      (IsLocalizedModule.map_comp _ _ _ _)
  rw [h]
  exact Function.bijective_id

end

end TauCeti
