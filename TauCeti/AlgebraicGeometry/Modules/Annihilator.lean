/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.FittingIdeal.Basic
public import TauCeti.AlgebraicGeometry.Modules.Sheaf
public import TauCeti.RingTheory.Localization.Annihilator
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.Support

/-!
# Annihilator ideal sheaves of quasi-coherent modules

Let `M` be a quasi-coherent `𝒪_X`-module on a scheme `X` whose sections over every affine open
are finitely generated, that is, a quasi-coherent module of finite type. The annihilators
`Ann(Γ(M, U)) ⊆ Γ(X, U)` of its modules of sections over the affine opens `U` glue to a
quasi-coherent ideal sheaf `Ann(M) ⊆ 𝒪_X`: over a basic open `D(f) ⊆ U`, the sections of `M` are
the localization of `Γ(M, U)` at `f`, and annihilators of finite modules commute with
localization.

The closed subscheme cut out by `Ann(M)` is a scheme structure on the support of `M`: a point
lies in it exactly when the fibre `M ⊗ κ(x)` is nonzero. It has the same support as the zeroth
Fitting ideal sheaf `Fitt₀(M)`, but in general a different scheme structure. For the cokernel of
`𝒪_X → ν_*𝒪_{X'}` along a finite morphism `ν : X' → X`, such as the normalization of a reduced
curve, the annihilator ideal sheaf is the conductor of `ν`.

## Main definitions

* `AlgebraicGeometry.Scheme.Modules.annihilator M hM`: the annihilator ideal sheaf of a
  quasi-coherent module `M` with finitely generated modules of sections `hM` over affine opens.

## Main results

* `AlgebraicGeometry.Scheme.Modules.annihilator_ideal`: over an affine open `U`, it is the
  annihilator of `Γ(M, U)`.
* `AlgebraicGeometry.Scheme.Modules.annihilator_congr`: invariance under module isomorphisms.
* `AlgebraicGeometry.Scheme.Modules.annihilator_Spec`: the affine global-sections description.
* `AlgebraicGeometry.Scheme.Modules.support_annihilator`: `Ann(M)` and `Fitt₀(M)` have the same
  support.
* `AlgebraicGeometry.Scheme.Modules.mem_support_annihilator_iff`: a point `x` of an affine open
  `U` lies in the support of `Ann(M)` exactly when the fibre `κ(x) ⊗ Γ(M, U)` is nonzero.

## References

* [Stacks Project, Tag 01PB](https://stacks.math.columbia.edu/tag/01PB): quasi-coherent modules
  of finite type have finitely generated modules of sections over affine opens.
* [Stacks Project, Tag 00L2](https://stacks.math.columbia.edu/tag/00L2): the support of a finite
  module is the zero locus of its annihilator.
-/

public section

open CategoryTheory AlgebraicGeometry

open scoped TensorProduct

namespace TauCeti

universe u

noncomputable section

variable {X : Scheme.{u}} (M : X.Modules) [M.IsQuasicoherent]
  (hM : ∀ U : X.affineOpens, Module.Finite Γ(X, U) Γ(M, U))

/-- The **annihilator ideal sheaf** `Ann(M)` of a quasi-coherent module `M` whose sections over
every affine open `U` form a finite `Γ(X, U)`-module: over `U` it is the annihilator of
`Γ(M, U)`. Its support is the set of points at which the fibre of `M` is nonzero
(`AlgebraicGeometry.Scheme.Modules.mem_support_annihilator_iff`). -/
def _root_.AlgebraicGeometry.Scheme.Modules.annihilator : X.IdealSheafData where
  ideal U := Module.annihilator Γ(X, U) Γ(M, U)
  map_ideal_basicOpen U f := by
    have := hM U
    have := M.isLocalizedModule_basicOpenRestrict U.2 f
    have := U.2.isLocalization_basicOpen f
    -- Sections over `D(f)` are the localization of `Γ(M, U)` at `f`.
    exact (IsLocalizedModule.annihilator_eq_map (.powers f) Γ(X, X.basicOpen f)
      (M.basicOpenRestrict f)).symm

/-- Over an affine open `U`, the annihilator ideal sheaf `Ann(M)` is the annihilator of the
module of sections `Γ(M, U)`. -/
@[simp]
theorem _root_.AlgebraicGeometry.Scheme.Modules.annihilator_ideal (U : X.affineOpens) :
    (M.annihilator hM).ideal U = Module.annihilator Γ(X, U) Γ(M, U) :=
  (rfl)

/-- The annihilator ideal sheaf and the zeroth Fitting ideal sheaf have the same support, the set
of points at which the fibre of `M` is nonzero. -/
theorem _root_.AlgebraicGeometry.Scheme.Modules.support_annihilator :
    (M.annihilator hM).support = (M.fittingIdeal hM 0).support := by
  ext x
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ x) isOpen_univ
  let U' : X.affineOpens := ⟨U, hU⟩
  have := hM U'
  let p : PrimeSpectrum Γ(X, U) := ⟨RingHom.ker (X.evaluation U x hxU).hom, RingHom.ker_isPrime _⟩
  have : p.asIdeal.IsPrime := p.isPrime
  -- Over `U`, the point `x` lies in the support of an ideal sheaf `I` iff `I(U) ⊆ p`.
  have hsupp (I : X.IdealSheafData) : x ∈ I.support ↔ I.ideal U' ≤ p.asIdeal := by
    simp [Scheme.IdealSheafData.mem_support_iff_of_mem (U := U') hxU, Scheme.mem_zeroLocus_iff,
      IsConcreteLE.le_iff, p]
  simp only [SetLike.mem_coe, hsupp, Scheme.Modules.annihilator_ideal,
    Scheme.Modules.fittingIdeal_ideal]
  -- Both ideals lie in `p` exactly when the fibre `κ(p) ⊗ Γ(M, U)` is nonzero.
  rw [← Module.mem_support_iff_of_finite,
    Module.mem_support_iff_nontrivial_residueField_tensorProduct, fittingIdeal_le_iff_lt_finrank,
    Module.finrank_pos_iff]

/-- **The support of an annihilator ideal sheaf.** A point `x` of an affine open `U` lies in the
support of `Ann(M)` exactly when the fibre `κ(x) ⊗ Γ(M, U)` of `M` at `x` is nonzero. -/
theorem _root_.AlgebraicGeometry.Scheme.Modules.mem_support_annihilator_iff {x : X}
    {U : X.affineOpens} (hx : x ∈ U.1) :
    x ∈ (M.annihilator hM).support ↔
      letI := (X.evaluation U x hx).hom.toAlgebra
      0 < Module.finrank (X.residueField x) (X.residueField x ⊗[Γ(X, U)] Γ(M, U)) := by
  rw [M.support_annihilator hM, M.mem_support_fittingIdeal_iff hM hx]

end

/-- Isomorphic quasicoherent modules have the same annihilator ideal sheaves. -/
theorem _root_.AlgebraicGeometry.Scheme.Modules.annihilator_congr
    {X : Scheme.{u}} {M N : X.Modules} [M.IsQuasicoherent]
    (hM : ∀ U : X.affineOpens, Module.Finite Γ(X, U) Γ(M, U)) (e : M ≅ N) :
    letI : N.IsQuasicoherent :=
      (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso e inferInstance
    let hN : ∀ U : X.affineOpens, Module.Finite Γ(X, U) Γ(N, U) := fun U ↦
      have := hM U
      .equiv (Scheme.Modules.sectionsLinearEquiv e U)
    M.annihilator hM = N.annihilator hN := by
  dsimp only
  apply Scheme.IdealSheafData.ext
  funext U
  rw [Scheme.Modules.annihilator_ideal, Scheme.Modules.annihilator_ideal]
  exact (Scheme.Modules.sectionsLinearEquiv e U).annihilator_eq

/-- On a spectrum, the annihilator ideal of global sections is the image of the annihilator
computed over the original ring under the canonical global-sections isomorphism. -/
theorem _root_.AlgebraicGeometry.Scheme.Modules.annihilator_ideal_top_Spec
    {R : CommRingCat.{u}} (M : (Spec R).Modules) [M.IsQuasicoherent]
    (hM : ∀ U : (Spec R).affineOpens, Module.Finite Γ(Spec R, U) Γ(M, U)) :
    (M.annihilator hM).ideal ⟨⊤, isAffineOpen_top _⟩ =
      (Module.annihilator R Γ(M, ⊤)).map (Scheme.ΓSpecIso R).inv.hom := by
  have hmap : algebraMap R Γ(Spec R, ⊤) = (Scheme.ΓSpecIso R).inv.hom := by
    rw [IsAffineOpen.algebraMap_Spec_obj]
    simp
  have hsurj : Function.Surjective (algebraMap R Γ(Spec R, ⊤)) :=
    hmap ▸ (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso R).inv).surjective
  -- `R → Γ(Spec R, ⊤)` is surjective, so the annihilator over `Γ(Spec R, ⊤)` is the image of
  -- its contraction, the annihilator over `R`.
  rw [Scheme.Modules.annihilator_ideal, ← hmap,
    ← Module.comap_annihilator (R₀ := R) (R := Γ(Spec R, ⊤)) (M := Γ(M, ⊤)),
    Ideal.map_comap_of_surjective _ hsurj]

/-- The annihilator ideal sheaf of a quasicoherent module on a spectrum is generated by the
annihilator of its module of global sections. -/
theorem _root_.AlgebraicGeometry.Scheme.Modules.annihilator_Spec
    {R : CommRingCat.{u}} (M : (Spec R).Modules) [M.IsQuasicoherent]
    (hM : ∀ U : (Spec R).affineOpens, Module.Finite Γ(Spec R, U) Γ(M, U)) :
    M.annihilator hM = Scheme.IdealSheafData.ofIdealTop
      ((Module.annihilator R Γ(M, ⊤)).map (Scheme.ΓSpecIso R).inv.hom) := by
  apply Scheme.IdealSheafData.ext_of_isAffine
  rw [Scheme.IdealSheafData.ofIdealTop_ideal]
  simpa using M.annihilator_ideal_top_Spec hM

end TauCeti
