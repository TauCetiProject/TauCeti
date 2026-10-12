/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
public import Mathlib.AlgebraicGeometry.ResidueField
public import TauCeti.AlgebraicGeometry.Modules.Localization
public import TauCeti.RingTheory.FittingIdeal.BaseChange
public import TauCeti.AlgebraicGeometry.IdealSheaf.OfIdealTop
public import TauCeti.AlgebraicGeometry.Modules.TensorProduct

/-!
# Fitting ideal sheaves of quasi-coherent modules

Let `M` be a quasi-coherent `𝒪_X`-module on a scheme `X` whose sections over every affine open
are finitely generated, that is, a quasi-coherent module of finite type. For `k : ℕ`, the `k`-th
Fitting ideals `Fitt_k(Γ(M, U)) ⊆ Γ(X, U)` of its modules of sections over the affine opens `U`
glue to a quasi-coherent ideal sheaf `Fitt_k(M) ⊆ 𝒪_X`: over a basic open `D(f) ⊆ U`, the sections
of `M` are the localization of `Γ(M, U)` at `f`, and Fitting ideals commute with localization.

The closed subscheme cut out by `Fitt_k(M)` is supported exactly at the points `x` whose fibre
`M ⊗ κ(x)` has dimension greater than `k`, so it is a scheme-theoretic structure on the locus
where `M` needs more than `k` local generators. Applied to the sheaf of relative differentials of
a relative curve, the first Fitting ideal defines the relative singular locus.

## Main definitions

* `AlgebraicGeometry.Scheme.Modules.fittingIdeal M hM k`: the `k`-th Fitting ideal sheaf of a
  quasi-coherent module `M` with finitely generated modules of sections `hM` over affine opens.

## Main results

* `AlgebraicGeometry.Scheme.Modules.fittingIdeal_ideal`: over an affine open `U`, it is the
  Fitting ideal `Fitt_k(Γ(M, U))`.
* `AlgebraicGeometry.Scheme.Modules.fittingIdeal_monotone`: `Fitt₀(M) ≤ Fitt₁(M) ≤ ⋯`.
* `AlgebraicGeometry.Scheme.Modules.fittingIdeal_congr`: invariance under module isomorphisms.
* `AlgebraicGeometry.Scheme.Modules.fittingIdeal_Spec`: the affine global-sections description.
* `AlgebraicGeometry.Scheme.Modules.mem_support_fittingIdeal_iff`: a point `x` of an affine open
  `U` lies in the support of `Fitt_k(M)` exactly when `k < dim_{κ(x)} κ(x) ⊗ Γ(M, U)`.

`FittingIdeal.Pullback` proves compatibility with arbitrary pullback of quasicoherent modules
of finite type.

## Implementation notes

The finiteness of `M` is the hypothesis that `Γ(M, U)` is a finite `Γ(X, U)`-module for every
affine open `U`. For quasi-coherent modules this is equivalent to being of finite type
([Stacks, Tag 01PB](https://stacks.math.columbia.edu/tag/01PB)).

## References

* [Stacks Project, Tag 0C3C](https://stacks.math.columbia.edu/tag/0C3C): Fitting ideals of a
  finite type quasi-coherent module.
* [Stacks Project, Tag 0C3D](https://stacks.math.columbia.edu/tag/0C3D): the zero loci of the
  Fitting ideals.
-/

public section

open CategoryTheory AlgebraicGeometry

open scoped TensorProduct

namespace TauCeti

universe u

noncomputable section

variable {X : Scheme.{u}} (M : X.Modules) [M.IsQuasicoherent]
  (hM : ∀ U : X.affineOpens, Module.Finite Γ(X, U) Γ(M, U))

/-- The `k`-th **Fitting ideal sheaf** `Fitt_k(M)` of a quasi-coherent module `M` whose sections
over every affine open `U` form a finite `Γ(X, U)`-module: over `U` it is the `k`-th Fitting ideal
of `Γ(M, U)`. Its support is the set of points at which the fibre of `M` has dimension greater
than `k` (`AlgebraicGeometry.Scheme.Modules.mem_support_fittingIdeal_iff`). -/
def _root_.AlgebraicGeometry.Scheme.Modules.fittingIdeal (k : ℕ) : X.IdealSheafData where
  ideal U := haveI := hM U; TauCeti.fittingIdeal Γ(X, U) Γ(M, U) k
  map_ideal_basicOpen U f := by
    have := hM U
    have := M.isLocalizedModule_basicOpenRestrict U.2 f
    have := U.2.isLocalization_basicOpen f
    -- Sections over `D(f)` are the base change of `Γ(M, U)` to the localization `Γ(X, D(f))`.
    exact ((IsLocalizedModule.isBaseChange (.powers f) Γ(X, X.basicOpen f)
      (M.basicOpenRestrict f)).fittingIdeal_eq_map k).symm

/-- Over an affine open `U`, the Fitting ideal sheaf `Fitt_k(M)` is the `k`-th Fitting ideal of
the module of sections `Γ(M, U)`. -/
@[simp]
theorem _root_.AlgebraicGeometry.Scheme.Modules.fittingIdeal_ideal (k : ℕ) (U : X.affineOpens) :
    (M.fittingIdeal hM k).ideal U = (haveI := hM U; TauCeti.fittingIdeal Γ(X, U) Γ(M, U) k) :=
  (rfl)

/-- The Fitting ideal sheaves increase: `Fitt₀(M) ≤ Fitt₁(M) ≤ ⋯`. -/
theorem _root_.AlgebraicGeometry.Scheme.Modules.fittingIdeal_monotone :
    Monotone (M.fittingIdeal hM) := fun _ _ hkl U ↦ by
  have := hM U
  exact TauCeti.fittingIdeal_monotone Γ(X, U) Γ(M, U) hkl

/-- **The support of a Fitting ideal sheaf.** A point `x` of an affine open `U` lies in the support
of `Fitt_k(M)` exactly when the fibre `κ(x) ⊗ Γ(M, U)` of `M` at `x` has dimension greater than
`k`, that is, when `M` needs more than `k` generators near `x`. -/
theorem _root_.AlgebraicGeometry.Scheme.Modules.mem_support_fittingIdeal_iff {x : X}
    {U : X.affineOpens} (hx : x ∈ U.1) (k : ℕ) :
    x ∈ (M.fittingIdeal hM k).support ↔
      letI := (X.evaluation U x hx).hom.toAlgebra
      k < Module.finrank (X.residueField x) (X.residueField x ⊗[Γ(X, U)] Γ(M, U)) := by
  let := (X.evaluation U x hx).hom.toAlgebra
  have := hM U
  rw [Scheme.IdealSheafData.mem_support_iff_of_mem hx, Scheme.Modules.fittingIdeal_ideal,
    ← fittingIdeal_map_eq_bot_iff_lt_finrank, Ideal.map_eq_bot_iff_le_ker, Scheme.mem_zeroLocus_iff]
  simp [IsConcreteLE.le_iff, RingHom.algebraMap_toAlgebra]

end

/-- Isomorphic quasicoherent modules have the same Fitting ideal sheaves. -/
theorem _root_.AlgebraicGeometry.Scheme.Modules.fittingIdeal_congr
    {X : Scheme.{u}} {M N : X.Modules} [M.IsQuasicoherent]
    (hM : ∀ U : X.affineOpens, Module.Finite Γ(X, U) Γ(M, U))
    (e : M ≅ N) (k : ℕ) :
    letI : N.IsQuasicoherent :=
      (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso e inferInstance
    let hN : ∀ U : X.affineOpens, Module.Finite Γ(X, U) Γ(N, U) := fun U ↦ by
      have := hM U
      apply Module.Finite.equiv (M := Γ(M, U))
      -- The sections functor uses ModuleCat wrappers for the same underlying sections.
      convert! ((Scheme.Modules.sectionsFunctor U).mapIso e).toLinearEquiv
    M.fittingIdeal hM k = N.fittingIdeal hN k := by
  dsimp only
  apply Scheme.IdealSheafData.ext
  funext U
  have := hM U
  let l : Γ(M, U) ≃ₗ[Γ(X, U)] Γ(N, U) := by
    -- The sections functor uses ModuleCat wrappers for the same underlying sections.
    convert! ((Scheme.Modules.sectionsFunctor U).mapIso e).toLinearEquiv
  have := Module.Finite.equiv l
  rw [Scheme.Modules.fittingIdeal_ideal, Scheme.Modules.fittingIdeal_ideal]
  exact TauCeti.fittingIdeal_congr l k

/-- On a spectrum, the Fitting ideal of global sections is the image of the Fitting
ideal computed over the original ring under the canonical global-sections isomorphism. -/
theorem _root_.AlgebraicGeometry.Scheme.Modules.fittingIdeal_ideal_top_Spec
    {R : CommRingCat.{u}} (M : (Spec R).Modules) [M.IsQuasicoherent]
    (hM : ∀ U : (Spec R).affineOpens, Module.Finite Γ(Spec R, U) Γ(M, U))
    (k : ℕ) :
    letI : Module.Finite R Γ(M, ⊤) := ⟨by
      simpa only [Submodule.restrictScalars_top] using
        (hM ⟨⊤, isAffineOpen_top _⟩).fg_top.restrictScalars_of_surjective (R := R) (by
          simpa [IsAffineOpen.algebraMap_Spec_obj] using
            (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso R).inv).surjective)⟩
    (M.fittingIdeal hM k).ideal ⟨⊤, isAffineOpen_top _⟩ =
      (TauCeti.fittingIdeal R Γ(M, ⊤) k).map (Scheme.ΓSpecIso R).inv.hom := by
  have := hM ⟨⊤, isAffineOpen_top _⟩
  have : Module.Finite R Γ(M, ⊤) := ⟨by
    simpa only [Submodule.restrictScalars_top] using
      (hM ⟨⊤, isAffineOpen_top _⟩).fg_top.restrictScalars_of_surjective (R := R) (by
        simpa [IsAffineOpen.algebraMap_Spec_obj] using
          (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso R).inv).surjective)⟩
  have hmap : algebraMap R Γ(Spec R, ⊤) = (Scheme.ΓSpecIso R).inv.hom := by
    rw [IsAffineOpen.algebraMap_Spec_obj]
    simp
  let : IsLocalization (⊥ : Submonoid R) Γ(Spec R, ⊤) :=
    IsLocalization.of_le_isUnit_of_bijective (by simp [Algebra.algebraMapSubmonoid])
      (hmap ▸ ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso R).inv)
  have := isLocalizedModule_id (S := (⊥ : Submonoid R)) Γ(Spec R, ⊤)
    (M := Γ(M, ⊤))
  rw [Scheme.Modules.fittingIdeal_ideal, ← hmap]
  exact (IsLocalizedModule.isBaseChange (⊥ : Submonoid R) Γ(Spec R, ⊤)
    (LinearMap.id : Γ(M, ⊤) →ₗ[R] _)).fittingIdeal_eq_map k

/-- The Fitting ideal sheaf of a quasicoherent module on a spectrum is generated by
the Fitting ideal of its module of global sections. -/
theorem _root_.AlgebraicGeometry.Scheme.Modules.fittingIdeal_Spec
    {R : CommRingCat.{u}} (M : (Spec R).Modules) [M.IsQuasicoherent]
    (hM : ∀ U : (Spec R).affineOpens, Module.Finite Γ(Spec R, U) Γ(M, U))
    (k : ℕ) :
    letI : Module.Finite R Γ(M, ⊤) := ⟨by
      simpa only [Submodule.restrictScalars_top] using
        (hM ⟨⊤, isAffineOpen_top _⟩).fg_top.restrictScalars_of_surjective (R := R) (by
          simpa [IsAffineOpen.algebraMap_Spec_obj] using
            (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso R).inv).surjective)⟩
    M.fittingIdeal hM k = Scheme.IdealSheafData.ofIdealTop
      ((TauCeti.fittingIdeal R Γ(M, ⊤) k).map (Scheme.ΓSpecIso R).inv.hom) := by
  apply Scheme.IdealSheafData.ext_of_isAffine
  rw [Scheme.IdealSheafData.ofIdealTop_ideal]
  simpa using M.fittingIdeal_ideal_top_Spec hM k

end TauCeti
