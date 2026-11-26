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
# Cohomology with supports in degree one

Let `M` be a sheaf of modules on a scheme `X`, `Z ⊆ X` closed and `W ⊆ X` open. The long exact
sequence of supports begins
`H⁰(W, M) → H⁰(W ∖ Z, M) → H¹_Z(W, M) → H¹(W, M)`. When `H¹(W, M) = 0`, for instance when `M` is
quasi-coherent and `W` is affine, the connecting map is therefore surjective with kernel the
restrictions of classes on `W`, and
`H¹_Z(W, M) ≅ H⁰(W ∖ Z, M) / H⁰(W, M)`, linearly over global functions. The same argument gives
`H^{q+1}_Z(W, M) ≅ H^q(W ∖ Z, M) / H^q(W, M)` whenever `H^{q+1}(W, M) = 0`
(`AlgebraicGeometry.Scheme.Modules.cohomologyWithSupportSuccLinearEquiv`).

On an affine scheme `X` with a global function `f`, take `Z = V(f)`, whose complement is the basic
open `D(f)`. For quasi-coherent `M`, the restriction `H⁰(X, M) → H⁰(D(f), M)` is the localization
at the powers of `f`, so `H¹_{V(f)}(X, M) ≅ H⁰(X, M)_f / H⁰(X, M)`, linearly over global functions
(`AlgebraicGeometry.Scheme.Modules.cohomologyWithSupportOneComplBasicOpenLinearEquiv`), and the
same holds with any localization of `H⁰(X, M)` at the powers of `f` in place of `H⁰(X, M)_f`
(`Scheme.Modules.cohomologyWithSupportOneComplBasicOpenLinearEquivOfIsLocalizedModule`).
For the structure sheaf this is `H¹_{V(f)}(X, 𝒪) ≅ Γ(X, 𝒪)_f / Γ(X, 𝒪)`
(`AlgebraicGeometry.Scheme.Modules.cohomologyWithSupportOneComplBasicOpenUnitLinearEquiv`). For the
affine line `Spec R[t]` with `Z` the origin this is `R[t, t⁻¹] / R[t]`
(`TauCeti/Examples/AlgebraicGeometry/Cohomology/Support/DegreeOne.lean`).

## Main declarations

* `AlgebraicGeometry.Scheme.Modules.cohomologyWithSupportδ_surjective`: the connecting map
  `H^q(W ∖ Z, M) → H^{q+1}_Z(W, M)` is surjective when `H^{q+1}(W, M) = 0`.
* `AlgebraicGeometry.Scheme.Modules.cohomologyWithSupportSuccLinearEquiv`: when
  `H^{q+1}(W, M) = 0`, `H^{q+1}_Z(W, M)` is the quotient of `H^q(W ∖ Z, M)` by the restrictions
  from `H^q(W, M)`.
* `AlgebraicGeometry.Scheme.Modules.cohomologyOnComplComplBasicOpenLinearEquiv`: on a
  quasi-compact quasi-separated scheme, for quasi-coherent `M`, `Hⁿ(D(f), M)` is any localization
  of `Hⁿ(X, M)` at the powers of `f`.
* `Scheme.Modules.cohomologyWithSupportOneComplBasicOpenLinearEquivOfIsLocalizedModule`:
  on an affine scheme, `H¹_{V(f)}(X, M) ≅ N / H⁰(X, M)` for a localization `H⁰(X, M) → N` at the
  powers of `f`, with the instances `cohomologyWithSupportOneComplBasicOpenLinearEquiv`
  (`N = H⁰(X, M)_f`) and `cohomologyWithSupportOneComplBasicOpenUnitLinearEquiv`
  (`M = 𝒪`, `N = Γ(X, 𝒪)_f`).

## References

* [Stacks Project, Tag 0A39](https://stacks.math.columbia.edu/tag/0A39) (cohomology with
  supports)
-/

public section

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} (M : X.Modules) (Z : Closeds X) (W : X.Opens)

/-- The connecting map `H^q(W ∖ Z, M) → H^{q+1}_Z(W, M)` of the long exact sequence of supports is
surjective when `H^{q+1}(W, M)` vanishes. -/
theorem cohomologyWithSupportδ_surjective {q₀ q₁ : ℕ} (h : 1 + q₀ = q₁)
    [Subsingleton (cohomologyOn M q₁ W)] :
    Function.Surjective (M.cohomologyWithSupportδ Z W h) := fun x ↦
  (exact_cohomologyWithSupportδ_cohomologyWithSupportToCohomologyOn M Z W h x).mp
    (Subsingleton.elim _ _)

/-- **Cohomology with supports in positive degree.** When `H^{q+1}(W, M)` vanishes, the connecting
map identifies `H^{q+1}_Z(W, M)` with the quotient of `H^q(W ∖ Z, M)` by the restrictions of
classes in `H^q(W, M)`, linearly over global functions. -/
noncomputable def cohomologyWithSupportSuccLinearEquiv {q₀ q₁ : ℕ} (h : 1 + q₀ = q₁)
    [Subsingleton (cohomologyOn M q₁ W)] :
    (cohomologyOn M q₀ (W ⊓ Z.compl) ⧸
        LinearMap.range (cohomologyOnResLinear M q₀ (inf_le_left : W ⊓ Z.compl ≤ W))) ≃ₗ[Γ(X, ⊤)]
      M.cohomologyWithSupport Z W q₁ :=
  (exact_cohomologyOnResLinear_cohomologyWithSupportδ M Z W h).linearEquivOfSurjective
    (cohomologyWithSupportδ_surjective M Z W h)

/-- The identification of `H^{q+1}_Z(W, M)` with a quotient of `H^q(W ∖ Z, M)` sends the class of
a cohomology class to its image under the connecting map. -/
@[simp]
lemma cohomologyWithSupportSuccLinearEquiv_mk {q₀ q₁ : ℕ} (h : 1 + q₀ = q₁)
    [Subsingleton (cohomologyOn M q₁ W)] (x : cohomologyOn M q₀ (W ⊓ Z.compl)) :
    M.cohomologyWithSupportSuccLinearEquiv Z W h (Submodule.Quotient.mk x) =
      M.cohomologyWithSupportδ Z W h x :=
  (rfl)

/-- The inverse of the identification of `H^{q+1}_Z(W, M)` with a quotient of `H^q(W ∖ Z, M)`
sends the image of a class under the connecting map to its class in the quotient. -/
lemma cohomologyWithSupportSuccLinearEquiv_symm_cohomologyWithSupportδ {q₀ q₁ : ℕ}
    (h : 1 + q₀ = q₁) [Subsingleton (cohomologyOn M q₁ W)] (x : cohomologyOn M q₀ (W ⊓ Z.compl)) :
    (M.cohomologyWithSupportSuccLinearEquiv Z W h).symm (M.cohomologyWithSupportδ Z W h x) =
      Submodule.Quotient.mk x :=
  (LinearEquiv.symm_apply_eq _).mpr (M.cohomologyWithSupportSuccLinearEquiv_mk Z W h x).symm

section BasicOpen

variable (f : Γ(X, ⊤))

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

variable [CompactSpace X] [QuasiSeparatedSpace X] [M.IsQuasicoherent] {n : ℕ} {N : Type*}
  [AddCommGroup N] [Module Γ(X, ⊤) N] (g : cohomologyOn M n ⊤ →ₗ[Γ(X, ⊤)] N)
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

end QuasiCompactQuasiSeparated

variable [IsAffine X] [M.IsQuasicoherent]

/-- **Local cohomology in degree one along `V(f)` on an affine scheme.** For a quasi-coherent `M`
on an affine scheme `X`, a global function `f` and any localization `g : H⁰(X, M) → N` at the
powers of `f`, `H¹_{V(f)}(X, M)` is the cokernel `N / g(H⁰(X, M))`, linearly over global
functions. -/
noncomputable def cohomologyWithSupportOneComplBasicOpenLinearEquivOfIsLocalizedModule
    {N : Type*} [AddCommGroup N] [Module Γ(X, ⊤) N] (g : cohomologyOn M 0 ⊤ →ₗ[Γ(X, ⊤)] N)
    [IsLocalizedModule (.powers f) g] :
    M.cohomologyWithSupport (X.basicOpen f).compl ⊤ 1 ≃ₗ[Γ(X, ⊤)] N ⧸ LinearMap.range g :=
  (cohomologyWithSupportSuccLinearEquiv M (X.basicOpen f).compl ⊤ (add_zero 1)).symm.trans
    (Submodule.Quotient.equiv _ _ (M.cohomologyOnComplComplBasicOpenLinearEquiv f g)
      (M.map_range_cohomologyOnComplComplBasicOpenLinearEquiv f g))

/-- The identification of `H¹_{V(f)}(X, M)` with `N / g(H⁰(X, M))` sends the class of an element
of `N` back to the image under the connecting map of the corresponding class on `D(f)`. -/
@[simp]
lemma cohomologyWithSupportOneComplBasicOpenLinearEquivOfIsLocalizedModule_symm_mk {N : Type*}
    [AddCommGroup N] [Module Γ(X, ⊤) N] (g : cohomologyOn M 0 ⊤ →ₗ[Γ(X, ⊤)] N)
    [IsLocalizedModule (.powers f) g] (y : N) :
    (M.cohomologyWithSupportOneComplBasicOpenLinearEquivOfIsLocalizedModule f g).symm
        (Submodule.Quotient.mk y) =
      M.cohomologyWithSupportδ (X.basicOpen f).compl ⊤ (add_zero 1)
        ((M.cohomologyOnComplComplBasicOpenLinearEquiv f g).symm y) :=
  (rfl)

/-- The identification of `H¹_{V(f)}(X, M)` with `N / g(H⁰(X, M))` sends the image under the
connecting map of a class on `D(f)` to the class of the corresponding element of `N`. -/
lemma cohomologyWithSupportOneComplBasicOpenLinearEquivOfIsLocalizedModule_cohomologyWithSupportδ
    {N : Type*} [AddCommGroup N] [Module Γ(X, ⊤) N] (g : cohomologyOn M 0 ⊤ →ₗ[Γ(X, ⊤)] N)
    [IsLocalizedModule (.powers f) g] (x : cohomologyOn M 0 (⊤ ⊓ (X.basicOpen f).compl.compl)) :
    M.cohomologyWithSupportOneComplBasicOpenLinearEquivOfIsLocalizedModule f g
        (M.cohomologyWithSupportδ (X.basicOpen f).compl ⊤ (add_zero 1) x) =
      Submodule.Quotient.mk (M.cohomologyOnComplComplBasicOpenLinearEquiv f g x) := by
  refine (LinearEquiv.eq_symm_apply _).mp ?_
  rw [cohomologyWithSupportOneComplBasicOpenLinearEquivOfIsLocalizedModule_symm_mk,
    LinearEquiv.symm_apply_apply]

/-- **Local cohomology in degree one along `V(f)` on an affine scheme.** For a quasi-coherent `M`
on an affine scheme `X` and a global function `f`, `H¹_{V(f)}(X, M)` is the quotient
`H⁰(X, M)_f / H⁰(X, M)` of the localization at the powers of `f` by the image of `H⁰(X, M)`,
linearly over global functions. -/
noncomputable def cohomologyWithSupportOneComplBasicOpenLinearEquiv :
    M.cohomologyWithSupport (X.basicOpen f).compl ⊤ 1 ≃ₗ[Γ(X, ⊤)]
      LocalizedModule (.powers f) (cohomologyOn M 0 ⊤) ⧸
        LinearMap.range (LocalizedModule.mkLinearMap (.powers f) (cohomologyOn M 0 ⊤)) :=
  M.cohomologyWithSupportOneComplBasicOpenLinearEquivOfIsLocalizedModule f _

/-- The identification of `H¹_{V(f)}(X, M)` with `H⁰(X, M)_f / H⁰(X, M)` sends the class of an
element of `H⁰(X, M)_f` back to the image under the connecting map of the corresponding class on
`D(f)`. -/
@[simp]
lemma cohomologyWithSupportOneComplBasicOpenLinearEquiv_symm_mk
    (y : LocalizedModule (.powers f) (cohomologyOn M 0 ⊤)) :
    (M.cohomologyWithSupportOneComplBasicOpenLinearEquiv f).symm (Submodule.Quotient.mk y) =
      M.cohomologyWithSupportδ (X.basicOpen f).compl ⊤ (add_zero 1)
        ((M.cohomologyOnComplComplBasicOpenLinearEquiv f
          (LocalizedModule.mkLinearMap (.powers f) (cohomologyOn M 0 ⊤))).symm y) :=
  (rfl)

/-- The identification of `H¹_{V(f)}(X, M)` with `H⁰(X, M)_f / H⁰(X, M)` sends the image under the
connecting map of a class on `D(f)` to the class of the corresponding element of `H⁰(X, M)_f`. -/
lemma cohomologyWithSupportOneComplBasicOpenLinearEquiv_cohomologyWithSupportδ
    (x : cohomologyOn M 0 (⊤ ⊓ (X.basicOpen f).compl.compl)) :
    M.cohomologyWithSupportOneComplBasicOpenLinearEquiv f
        (M.cohomologyWithSupportδ (X.basicOpen f).compl ⊤ (add_zero 1) x) =
      Submodule.Quotient.mk (M.cohomologyOnComplComplBasicOpenLinearEquiv f
        (LocalizedModule.mkLinearMap (.powers f) (cohomologyOn M 0 ⊤)) x) :=
  M.cohomologyWithSupportOneComplBasicOpenLinearEquivOfIsLocalizedModule_cohomologyWithSupportδ f
    _ x

variable (X)

/-- **Local cohomology of the structure sheaf in degree one along `V(f)`.** For a global function
`f` on an affine scheme `X`, `H¹_{V(f)}(X, 𝒪_X)` is the quotient `Γ(X, 𝒪)_f / Γ(X, 𝒪)` of the
localization by the image of the global functions, linearly over global functions. -/
noncomputable def cohomologyWithSupportOneComplBasicOpenUnitLinearEquiv :
    (Scheme.Modules.unit X).cohomologyWithSupport (X.basicOpen f).compl ⊤ 1 ≃ₗ[Γ(X, ⊤)]
      Localization.Away f ⧸ LinearMap.range (Algebra.linearMap Γ(X, ⊤) (Localization.Away f)) :=
  ((Scheme.Modules.unit X).cohomologyWithSupportOneComplBasicOpenLinearEquivOfIsLocalizedModule f
    (Algebra.linearMap Γ(X, ⊤) (Localization.Away f) ∘ₗ
      (cohomologyOnZeroTopUnitLinearEquiv X).toLinearMap)).trans
    (Submodule.quotEquivOfEq _ _ (LinearEquiv.range_comp _ _))

/-- The identification of `H¹_{V(f)}(X, 𝒪)` with `Γ(X, 𝒪)_f / Γ(X, 𝒪)` sends the class of an
element of the localization back to the image under the connecting map of the corresponding class
on `D(f)`. -/
@[simp]
lemma cohomologyWithSupportOneComplBasicOpenUnitLinearEquiv_symm_mk (y : Localization.Away f) :
    (cohomologyWithSupportOneComplBasicOpenUnitLinearEquiv X f).symm (Submodule.Quotient.mk y) =
      (Scheme.Modules.unit X).cohomologyWithSupportδ (X.basicOpen f).compl ⊤ (add_zero 1)
        (((Scheme.Modules.unit X).cohomologyOnComplComplBasicOpenLinearEquiv f
          (Algebra.linearMap Γ(X, ⊤) (Localization.Away f) ∘ₗ
            (cohomologyOnZeroTopUnitLinearEquiv X).toLinearMap)).symm y) :=
  (rfl)

/-- The identification of `H¹_{V(f)}(X, 𝒪)` with `Γ(X, 𝒪)_f / Γ(X, 𝒪)` sends the image under the
connecting map of a class on `D(f)` to the class of the corresponding element of the
localization. -/
lemma cohomologyWithSupportOneComplBasicOpenUnitLinearEquiv_cohomologyWithSupportδ
    (x : cohomologyOn (Scheme.Modules.unit X) 0 (⊤ ⊓ (X.basicOpen f).compl.compl)) :
    cohomologyWithSupportOneComplBasicOpenUnitLinearEquiv X f
        ((Scheme.Modules.unit X).cohomologyWithSupportδ (X.basicOpen f).compl ⊤ (add_zero 1) x) =
      Submodule.Quotient.mk ((Scheme.Modules.unit X).cohomologyOnComplComplBasicOpenLinearEquiv f
        (Algebra.linearMap Γ(X, ⊤) (Localization.Away f) ∘ₗ
          (cohomologyOnZeroTopUnitLinearEquiv X).toLinearMap) x) := by
  refine (LinearEquiv.eq_symm_apply _).mp ?_
  rw [cohomologyWithSupportOneComplBasicOpenUnitLinearEquiv_symm_mk, LinearEquiv.symm_apply_apply]

end BasicOpen

end AlgebraicGeometry.Scheme.Modules
