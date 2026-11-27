/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Cohomology.Affine
public import TauCeti.AlgebraicGeometry.Cohomology.Localization
public import TauCeti.AlgebraicGeometry.Cohomology.Support
public import TauCeti.AlgebraicGeometry.Modules.Tensor.Product
public import TauCeti.AlgebraicGeometry.Modules.Unit

/-!
# Cohomology with supports in `V(f)`

Let `M` be a quasi-coherent sheaf of modules on a quasi-compact quasi-separated scheme `X` and `f`
a global function. Take `Z = V(f)`, whose complement is the basic open `D(f)`. The restriction
`Hⁿ(X, M) → Hⁿ(D(f), M)` is the localization at the powers of `f`, so when `H^{n+1}(X, M) = 0`,
for instance when `X` is affine, the long exact sequence of supports
(`AlgebraicGeometry.Scheme.Modules.cohomologyWithSupportSuccLinearEquiv`) gives
`H^{n+1}_{V(f)}(X, M) ≅ Hⁿ(X, M)_f / Hⁿ(X, M)`, linearly over global functions
(`AlgebraicGeometry.Scheme.Modules.cohomologyWithSupportSuccComplBasicOpenLinearEquiv`). The same
holds with any localization of `Hⁿ(X, M)` at the powers of `f` in place of `Hⁿ(X, M)_f`
(`Scheme.Modules.cohomologyWithSupportSuccComplBasicOpenLinearEquivOfIsLocalizedModule`).
For the structure sheaf on an affine scheme, in degree one, this is
`H¹_{V(f)}(X, 𝒪) ≅ Γ(X, 𝒪)_f / Γ(X, 𝒪)`
(`AlgebraicGeometry.Scheme.Modules.cohomologyWithSupportOneComplBasicOpenUnitLinearEquiv`). For the
affine line `Spec R[t]` with `Z` the origin this is `R[t, t⁻¹] / R[t]`
(`TauCeti/Examples/AlgebraicGeometry/Cohomology/Support/DegreeOne.lean`).

## Main declarations

* `AlgebraicGeometry.Scheme.Modules.cohomologyOnComplComplBasicOpenLinearEquiv`: on a
  quasi-compact quasi-separated scheme, for quasi-coherent `M`, `Hⁿ(D(f), M)` is any localization
  of `Hⁿ(X, M)` at the powers of `f`.
* `Scheme.Modules.cohomologyWithSupportSuccComplBasicOpenLinearEquivOfIsLocalizedModule`:
  on a quasi-compact quasi-separated scheme with `H^{n+1}(X, M) = 0`,
  `H^{n+1}_{V(f)}(X, M) ≅ N / Hⁿ(X, M)` for a localization `Hⁿ(X, M) → N` at the powers of `f`,
  with the specialization `cohomologyWithSupportSuccComplBasicOpenLinearEquiv` (`N = Hⁿ(X, M)_f`).
* `AlgebraicGeometry.Scheme.Modules.cohomologyWithSupportOneComplBasicOpenUnitLinearEquiv`: on an
  affine scheme, `H¹_{V(f)}(X, 𝒪) ≅ Γ(X, 𝒪)_f / Γ(X, 𝒪)`.

## References

* [Stacks Project, Tag 0A39](https://stacks.math.columbia.edu/tag/0A39) (cohomology with
  supports)
-/

public section

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} (M : X.Modules) (f : Γ(X, ⊤))

/-- On a quasi-compact quasi-separated scheme, for a quasi-coherent `M` the restriction
`Hⁿ(X, M) → Hⁿ(D(f), M)`, with `D(f)` written as the complement of `V(f)`, is the localization at
the powers of `f`. -/
instance isLocalizedModule_cohomologyOnResLinear_complComplBasicOpen [CompactSpace X]
    [QuasiSeparatedSpace X] {M : X.Modules} [M.IsQuasicoherent] {n : ℕ} :
    IsLocalizedModule (.powers f) (cohomologyOnResLinear M n
      (inf_le_left : ⊤ ⊓ (X.basicOpen f).compl.compl ≤ ⊤)) :=
  isLocalizedModule_cohomologyOnResLinear_inf_basicOpen M f isCompact_univ isQuasiSeparated_univ
    _ (by rw [Opens.compl_compl]) n

section QuasiCompactQuasiSeparated

variable [CompactSpace X] [QuasiSeparatedSpace X] [M.IsQuasicoherent] {n : ℕ}

section IsLocalizedModule

variable {N : Type*} [AddCommGroup N] [Module Γ(X, ⊤) N] (g : cohomologyOn M n ⊤ →ₗ[Γ(X, ⊤)] N)
  [IsLocalizedModule (.powers f) g]

/-- On a quasi-compact quasi-separated scheme, for a quasi-coherent `M` and a localization
`g : Hⁿ(X, M) → N` at the powers of a global function `f`, the cohomology `Hⁿ(D(f), M)` of `M` on
the basic open `D(f)`, written as the complement of `V(f)`, is `N`, linearly over global
functions: both localize `Hⁿ(X, M)` at the powers of `f`. -/
noncomputable def cohomologyOnComplComplBasicOpenLinearEquiv :
    cohomologyOn M n (⊤ ⊓ (X.basicOpen f).compl.compl) ≃ₗ[Γ(X, ⊤)] N :=
  IsLocalizedModule.linearEquiv (.powers f) (cohomologyOnResLinear M n inf_le_left) g

/-- The identification of `Hⁿ(D(f), M)` with `N` sends the restriction of a global class `x` to
`g x`. -/
@[simp]
lemma cohomologyOnComplComplBasicOpenLinearEquiv_cohomologyOnRes (x : cohomologyOn M n ⊤) :
    M.cohomologyOnComplComplBasicOpenLinearEquiv f g
        (cohomologyOnRes M n (inf_le_left : ⊤ ⊓ (X.basicOpen f).compl.compl ≤ ⊤) x) =
      g x := by
  rw [← cohomologyOnResLinear_apply]
  exact IsLocalizedModule.linearEquiv_apply (.powers f) (cohomologyOnResLinear M n inf_le_left) g x

/-- The inverse of the identification of `Hⁿ(D(f), M)` with `N` sends `g x` to the restriction of
the global class `x`. -/
@[simp]
lemma cohomologyOnComplComplBasicOpenLinearEquiv_symm_apply (x : cohomologyOn M n ⊤) :
    (M.cohomologyOnComplComplBasicOpenLinearEquiv f g).symm (g x) =
      cohomologyOnRes M n (inf_le_left : ⊤ ⊓ (X.basicOpen f).compl.compl ≤ ⊤) x := by
  rw [← cohomologyOnResLinear_apply]
  exact IsLocalizedModule.linearEquiv_symm_apply (.powers f)
    (cohomologyOnResLinear M n inf_le_left) g x

/-- The identification of `Hⁿ(D(f), M)` with `N` carries the restrictions of global classes onto
the image of `g`. -/
theorem map_range_cohomologyOnComplComplBasicOpenLinearEquiv :
    (LinearMap.range (cohomologyOnResLinear M n
        (inf_le_left : ⊤ ⊓ (X.basicOpen f).compl.compl ≤ ⊤))).map
      (M.cohomologyOnComplComplBasicOpenLinearEquiv f g).toLinearMap = LinearMap.range g := by
  rw [← LinearMap.range_comp]
  refine congrArg LinearMap.range (LinearMap.ext fun x ↦ ?_)
  rw [LinearMap.comp_apply, LinearEquiv.coe_coe, cohomologyOnResLinear_apply,
    cohomologyOnComplComplBasicOpenLinearEquiv_cohomologyOnRes]

variable [Subsingleton (cohomologyOn M (n + 1) ⊤)]

/-- **Local cohomology along `V(f)`.** For a quasi-coherent `M` on a quasi-compact quasi-separated
scheme `X` with `H^{n+1}(X, M) = 0`, a global function `f` and any localization
`g : Hⁿ(X, M) → N` at the powers of `f`, `H^{n+1}_{V(f)}(X, M)` is the cokernel
`N / g(Hⁿ(X, M))`, linearly over global functions. -/
noncomputable def cohomologyWithSupportSuccComplBasicOpenLinearEquivOfIsLocalizedModule :
    M.cohomologyWithSupport (X.basicOpen f).compl ⊤ (n + 1) ≃ₗ[Γ(X, ⊤)] N ⧸ LinearMap.range g :=
  (cohomologyWithSupportSuccLinearEquiv M (X.basicOpen f).compl ⊤ (add_comm 1 n)).symm.trans
    (Submodule.Quotient.equiv _ _ (M.cohomologyOnComplComplBasicOpenLinearEquiv f g)
      (M.map_range_cohomologyOnComplComplBasicOpenLinearEquiv f g))

/-- The identification of `H^{n+1}_{V(f)}(X, M)` with `N / g(Hⁿ(X, M))` sends the image under the
connecting map of a class on `D(f)` to the class of the corresponding element of `N`. -/
lemma cohomologyWithSupportSuccComplBasicOpenLinearEquivOfIsLocalizedModule_cohomologyWithSupportδ
    (x : cohomologyOn M n (⊤ ⊓ (X.basicOpen f).compl.compl)) :
    M.cohomologyWithSupportSuccComplBasicOpenLinearEquivOfIsLocalizedModule f g
        (M.cohomologyWithSupportδ (X.basicOpen f).compl ⊤ (add_comm 1 n) x) =
      Submodule.Quotient.mk (M.cohomologyOnComplComplBasicOpenLinearEquiv f g x) := by
  rw [cohomologyWithSupportSuccComplBasicOpenLinearEquivOfIsLocalizedModule,
    LinearEquiv.trans_apply, cohomologyWithSupportSuccLinearEquiv_symm_cohomologyWithSupportδ,
    Submodule.Quotient.equiv_apply, Submodule.mapQ_apply, LinearEquiv.coe_coe]

/-- The identification of `H^{n+1}_{V(f)}(X, M)` with `N / g(Hⁿ(X, M))` sends the class of an
element of `N` back to the image under the connecting map of the corresponding class on `D(f)`. -/
@[simp]
lemma cohomologyWithSupportSuccComplBasicOpenLinearEquivOfIsLocalizedModule_symm_mk (y : N) :
    (M.cohomologyWithSupportSuccComplBasicOpenLinearEquivOfIsLocalizedModule f g).symm
        (Submodule.Quotient.mk y) =
      M.cohomologyWithSupportδ (X.basicOpen f).compl ⊤ (add_comm 1 n)
        ((M.cohomologyOnComplComplBasicOpenLinearEquiv f g).symm y) := by
  rw [LinearEquiv.symm_apply_eq,
    cohomologyWithSupportSuccComplBasicOpenLinearEquivOfIsLocalizedModule_cohomologyWithSupportδ,
    LinearEquiv.apply_symm_apply]

end IsLocalizedModule

variable (n) [Subsingleton (cohomologyOn M (n + 1) ⊤)]

/-- **Local cohomology along `V(f)`.** For a quasi-coherent `M` on a quasi-compact quasi-separated
scheme `X` with `H^{n+1}(X, M) = 0` and a global function `f`, `H^{n+1}_{V(f)}(X, M)` is the
quotient `Hⁿ(X, M)_f / Hⁿ(X, M)` of the localization at the powers of `f` by the image of
`Hⁿ(X, M)`, linearly over global functions. -/
noncomputable def cohomologyWithSupportSuccComplBasicOpenLinearEquiv :
    M.cohomologyWithSupport (X.basicOpen f).compl ⊤ (n + 1) ≃ₗ[Γ(X, ⊤)]
      LocalizedModule (.powers f) (cohomologyOn M n ⊤) ⧸
        LinearMap.range (LocalizedModule.mkLinearMap (.powers f) (cohomologyOn M n ⊤)) :=
  M.cohomologyWithSupportSuccComplBasicOpenLinearEquivOfIsLocalizedModule f _

/-- The identification of `H^{n+1}_{V(f)}(X, M)` with `Hⁿ(X, M)_f / Hⁿ(X, M)` sends the class of
an element of `Hⁿ(X, M)_f` back to the image under the connecting map of the corresponding class
on `D(f)`. -/
@[simp]
lemma cohomologyWithSupportSuccComplBasicOpenLinearEquiv_symm_mk
    (y : LocalizedModule (.powers f) (cohomologyOn M n ⊤)) :
    (M.cohomologyWithSupportSuccComplBasicOpenLinearEquiv f n).symm (Submodule.Quotient.mk y) =
      M.cohomologyWithSupportδ (X.basicOpen f).compl ⊤ (add_comm 1 n)
        ((M.cohomologyOnComplComplBasicOpenLinearEquiv f
          (LocalizedModule.mkLinearMap (.powers f) (cohomologyOn M n ⊤))).symm y) :=
  M.cohomologyWithSupportSuccComplBasicOpenLinearEquivOfIsLocalizedModule_symm_mk f _ y

/-- The identification of `H^{n+1}_{V(f)}(X, M)` with `Hⁿ(X, M)_f / Hⁿ(X, M)` sends the image
under the connecting map of a class on `D(f)` to the class of the corresponding element of
`Hⁿ(X, M)_f`. -/
lemma cohomologyWithSupportSuccComplBasicOpenLinearEquiv_cohomologyWithSupportδ
    (x : cohomologyOn M n (⊤ ⊓ (X.basicOpen f).compl.compl)) :
    M.cohomologyWithSupportSuccComplBasicOpenLinearEquiv f n
        (M.cohomologyWithSupportδ (X.basicOpen f).compl ⊤ (add_comm 1 n) x) =
      Submodule.Quotient.mk (M.cohomologyOnComplComplBasicOpenLinearEquiv f
        (LocalizedModule.mkLinearMap (.powers f) (cohomologyOn M n ⊤)) x) :=
  M.cohomologyWithSupportSuccComplBasicOpenLinearEquivOfIsLocalizedModule_cohomologyWithSupportδ f
    _ x

end QuasiCompactQuasiSeparated

/-- A localization `Γ(X, 𝒪) → A` of the global functions, composed with the identification of
`H⁰(⊤, 𝒪_X)` with the global sections of `𝒪_X`, is a localization of `H⁰(⊤, 𝒪_X)`. This is
`IsLocalizedModule.of_linearEquiv_right`; instance search cannot apply it directly because the
global sections of `𝒪_X` are the ring `Γ(X, 𝒪)` as a module over itself only after unfolding
beyond instance transparency. -/
instance isLocalizedModule_algebraLinearMap_comp_cohomologyOnZeroTopLinearEquiv_unit
    {S : Submonoid Γ(X, ⊤)} {A : Type*} [CommRing A] [Algebra Γ(X, ⊤) A] [IsLocalization S A] :
    IsLocalizedModule S (Algebra.linearMap Γ(X, ⊤) A ∘ₗ
      (cohomologyOnZeroTopLinearEquiv (Scheme.Modules.unit X)).toLinearMap) :=
  IsLocalizedModule.of_linearEquiv_right _ _ _

variable (X) [IsAffine X]

/-- **Local cohomology of the structure sheaf in degree one along `V(f)`.** For a global function
`f` on an affine scheme `X`, `H¹_{V(f)}(X, 𝒪_X)` is the quotient `Γ(X, 𝒪)_f / Γ(X, 𝒪)` of the
localization by the image of the global functions, linearly over global functions. -/
noncomputable def cohomologyWithSupportOneComplBasicOpenUnitLinearEquiv :
    (Scheme.Modules.unit X).cohomologyWithSupport (X.basicOpen f).compl ⊤ 1 ≃ₗ[Γ(X, ⊤)]
      Localization.Away f ⧸ LinearMap.range (Algebra.linearMap Γ(X, ⊤) (Localization.Away f)) :=
  ((Scheme.Modules.unit X).cohomologyWithSupportSuccComplBasicOpenLinearEquivOfIsLocalizedModule f
    (Algebra.linearMap Γ(X, ⊤) (Localization.Away f) ∘ₗ
      (cohomologyOnZeroTopLinearEquiv (Scheme.Modules.unit X)).toLinearMap)).trans
    (Submodule.quotEquivOfEq _ _ (LinearEquiv.range_comp _ _))

/-- The identification of `H¹_{V(f)}(X, 𝒪)` with `Γ(X, 𝒪)_f / Γ(X, 𝒪)` sends the image under the
connecting map of a class on `D(f)` to the class of the corresponding element of the
localization. -/
lemma cohomologyWithSupportOneComplBasicOpenUnitLinearEquiv_cohomologyWithSupportδ
    (x : cohomologyOn (Scheme.Modules.unit X) 0 (⊤ ⊓ (X.basicOpen f).compl.compl)) :
    cohomologyWithSupportOneComplBasicOpenUnitLinearEquiv X f
        ((Scheme.Modules.unit X).cohomologyWithSupportδ (X.basicOpen f).compl ⊤ (add_zero 1) x) =
      Submodule.Quotient.mk ((Scheme.Modules.unit X).cohomologyOnComplComplBasicOpenLinearEquiv f
        (Algebra.linearMap Γ(X, ⊤) (Localization.Away f) ∘ₗ
          (cohomologyOnZeroTopLinearEquiv (Scheme.Modules.unit X)).toLinearMap) x) := by
  rw [cohomologyWithSupportOneComplBasicOpenUnitLinearEquiv, LinearEquiv.trans_apply,
    cohomologyWithSupportSuccComplBasicOpenLinearEquivOfIsLocalizedModule_cohomologyWithSupportδ,
    Submodule.quotEquivOfEq_mk]

/-- The identification of `H¹_{V(f)}(X, 𝒪)` with `Γ(X, 𝒪)_f / Γ(X, 𝒪)` sends the class of an
element of the localization back to the image under the connecting map of the corresponding class
on `D(f)`. -/
@[simp]
lemma cohomologyWithSupportOneComplBasicOpenUnitLinearEquiv_symm_mk (y : Localization.Away f) :
    (cohomologyWithSupportOneComplBasicOpenUnitLinearEquiv X f).symm (Submodule.Quotient.mk y) =
      (Scheme.Modules.unit X).cohomologyWithSupportδ (X.basicOpen f).compl ⊤ (add_zero 1)
        (((Scheme.Modules.unit X).cohomologyOnComplComplBasicOpenLinearEquiv f
          (Algebra.linearMap Γ(X, ⊤) (Localization.Away f) ∘ₗ
            (cohomologyOnZeroTopLinearEquiv (Scheme.Modules.unit X)).toLinearMap)).symm y) := by
  rw [LinearEquiv.symm_apply_eq,
    cohomologyWithSupportOneComplBasicOpenUnitLinearEquiv_cohomologyWithSupportδ,
    LinearEquiv.apply_symm_apply]

end AlgebraicGeometry.Scheme.Modules
