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
`H¹_Z(W, M) ≅ H⁰(W ∖ Z, M) / H⁰(W, M)`
(`AlgebraicGeometry.Scheme.Modules.cohomologyWithSupportOneLinearEquiv`), linearly over global
functions.

On an affine scheme `X` with a global function `f`, take `Z = V(f)`, whose complement is the basic
open `D(f)`. For quasi-coherent `M`, the restriction `H⁰(X, M) → H⁰(D(f), M)` is the localization
at the powers of `f`, so `H¹_{V(f)}(X, M) ≅ H⁰(X, M)_f / H⁰(X, M)`, linearly over global functions
(`AlgebraicGeometry.Scheme.Modules.cohomologyWithSupportOneComplBasicOpenLinearEquiv`), and the
same holds with any localization of `H⁰(X, M)` at the powers of `f` in place of `H⁰(X, M)_f`
(`Scheme.Modules.cohomologyWithSupportOneComplBasicOpenLinearEquivOfIsLocalizedModule`).
For the structure sheaf this is `H¹_{V(f)}(X, 𝒪) ≅ Γ(X, 𝒪)_f / Γ(X, 𝒪)`
(`AlgebraicGeometry.Scheme.Modules.cohomologyWithSupportOneComplBasicOpenUnitLinearEquiv`). For the
affine line `Spec R[t]` with `Z` the origin this is `R[t, t⁻¹] / R[t]`
(`TauCeti/Examples/AlgebraicGeometry/Cohomology/SupportDegreeOne.lean`).

## Main declarations

* `AlgebraicGeometry.Scheme.Modules.cohomologyWithSupportδ_surjective`: the connecting map
  `H^q(W ∖ Z, M) → H^{q+1}_Z(W, M)` is surjective when `H^{q+1}(W, M) = 0`.
* `AlgebraicGeometry.Scheme.Modules.cohomologyWithSupportOneLinearEquiv`: when `H¹(W, M) = 0`,
  `H¹_Z(W, M)` is the quotient of `H⁰(W ∖ Z, M)` by the restrictions from `H⁰(W, M)`.
* `AlgebraicGeometry.Scheme.Modules.cohomologyOnZeroComplComplBasicOpenLinearEquiv`: on a
  quasi-compact quasi-separated scheme, for quasi-coherent `M`, `H⁰(D(f), M)` is any localization
  of `H⁰(X, M)` at the powers of `f`.
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

/-- **Cohomology with supports in degree one.** When `H¹(W, M)` vanishes, the connecting map
identifies `H¹_Z(W, M)` with the quotient of `H⁰(W ∖ Z, M)` by the restrictions of classes in
`H⁰(W, M)`, linearly over global functions. -/
noncomputable def cohomologyWithSupportOneLinearEquiv [Subsingleton (cohomologyOn M 1 W)] :
    (cohomologyOn M 0 (W ⊓ Z.compl) ⧸
        LinearMap.range (cohomologyOnResLinear M 0 (inf_le_left : W ⊓ Z.compl ≤ W))) ≃ₗ[Γ(X, ⊤)]
      M.cohomologyWithSupport Z W 1 :=
  (exact_cohomologyOnResLinear_cohomologyWithSupportδ M Z W (add_zero 1)).linearEquivOfSurjective
    (cohomologyWithSupportδ_surjective M Z W (add_zero 1))

/-- The identification of `H¹_Z(W, M)` with a quotient of `H⁰(W ∖ Z, M)` sends the class of a
section to its image under the connecting map. -/
@[simp]
lemma cohomologyWithSupportOneLinearEquiv_mk [Subsingleton (cohomologyOn M 1 W)]
    (x : cohomologyOn M 0 (W ⊓ Z.compl)) :
    M.cohomologyWithSupportOneLinearEquiv Z W (Submodule.Quotient.mk x) =
      M.cohomologyWithSupportδ Z W (add_zero 1) x :=
  (rfl)

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

variable [CompactSpace X] [QuasiSeparatedSpace X] [M.IsQuasicoherent] {N : Type*} [AddCommGroup N]
  [Module Γ(X, ⊤) N] (g : cohomologyOn M 0 ⊤ →ₗ[Γ(X, ⊤)] N) [IsLocalizedModule (.powers f) g]

/-- On a quasi-compact quasi-separated scheme, for a quasi-coherent `M` and a localization
`g : H⁰(X, M) → N` at the powers of a global function `f`, the degree-zero cohomology of `M` on
the basic open `D(f)`, written as the complement of `V(f)`, is `N`, linearly over global
functions: both localize `H⁰(X, M)` at the powers of `f`. -/
noncomputable def cohomologyOnZeroComplComplBasicOpenLinearEquiv :
    cohomologyOn M 0 (⊤ ⊓ (X.basicOpen f).compl.compl) ≃ₗ[Γ(X, ⊤)] N :=
  IsLocalizedModule.linearEquiv (.powers f) (cohomologyOnResLinear M 0 inf_le_left) g

/-- The identification of `H⁰(D(f), M)` with `N` sends the restriction of a global class `x` to
`g x`. -/
@[simp]
lemma cohomologyOnZeroComplComplBasicOpenLinearEquiv_cohomologyOnRes
    (x : cohomologyOn M 0 ⊤) :
    M.cohomologyOnZeroComplComplBasicOpenLinearEquiv f g
        (cohomologyOnRes M 0 (inf_le_left : ⊤ ⊓ (X.basicOpen f).compl.compl ≤ ⊤) x) =
      g x := by
  rw [← cohomologyOnResLinear_apply]
  exact IsLocalizedModule.linearEquiv_apply (.powers f) (cohomologyOnResLinear M 0 inf_le_left) g x

/-- The identification of `H⁰(D(f), M)` with `N` carries the restrictions of global classes onto
the image of `g`. -/
theorem map_range_cohomologyOnZeroComplComplBasicOpenLinearEquiv :
    (LinearMap.range (cohomologyOnResLinear M 0
        (inf_le_left : ⊤ ⊓ (X.basicOpen f).compl.compl ≤ ⊤))).map
      (M.cohomologyOnZeroComplComplBasicOpenLinearEquiv f g).toLinearMap = LinearMap.range g := by
  ext y
  simp only [Submodule.mem_map, LinearMap.mem_range, LinearEquiv.coe_coe,
    cohomologyOnResLinear_apply]
  constructor
  · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨x, (M.cohomologyOnZeroComplComplBasicOpenLinearEquiv_cohomologyOnRes f g x).symm⟩
  · rintro ⟨x, rfl⟩
    exact ⟨_, ⟨x, rfl⟩,
      M.cohomologyOnZeroComplComplBasicOpenLinearEquiv_cohomologyOnRes f g x⟩

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
  (cohomologyWithSupportOneLinearEquiv M (X.basicOpen f).compl ⊤).symm.trans
    (Submodule.Quotient.equiv _ _ (M.cohomologyOnZeroComplComplBasicOpenLinearEquiv f g)
      (M.map_range_cohomologyOnZeroComplComplBasicOpenLinearEquiv f g))

/-- The identification of `H¹_{V(f)}(X, M)` with `N / g(H⁰(X, M))` sends the class of an element
of `N` back to the image under the connecting map of the corresponding class on `D(f)`. -/
@[simp]
lemma cohomologyWithSupportOneComplBasicOpenLinearEquivOfIsLocalizedModule_symm_mk {N : Type*}
    [AddCommGroup N] [Module Γ(X, ⊤) N] (g : cohomologyOn M 0 ⊤ →ₗ[Γ(X, ⊤)] N)
    [IsLocalizedModule (.powers f) g] (y : N) :
    (M.cohomologyWithSupportOneComplBasicOpenLinearEquivOfIsLocalizedModule f g).symm
        (Submodule.Quotient.mk y) =
      M.cohomologyWithSupportδ (X.basicOpen f).compl ⊤ (add_zero 1)
        ((M.cohomologyOnZeroComplComplBasicOpenLinearEquiv f g).symm y) :=
  (rfl)

/-- **Local cohomology in degree one along `V(f)` on an affine scheme.** For a quasi-coherent `M`
on an affine scheme `X` and a global function `f`, `H¹_{V(f)}(X, M)` is the quotient
`H⁰(X, M)_f / H⁰(X, M)` of the localization at the powers of `f` by the image of `H⁰(X, M)`,
linearly over global functions. -/
noncomputable def cohomologyWithSupportOneComplBasicOpenLinearEquiv :
    M.cohomologyWithSupport (X.basicOpen f).compl ⊤ 1 ≃ₗ[Γ(X, ⊤)]
      LocalizedModule (.powers f) (cohomologyOn M 0 ⊤) ⧸
        LinearMap.range (LocalizedModule.mkLinearMap (.powers f) (cohomologyOn M 0 ⊤)) :=
  M.cohomologyWithSupportOneComplBasicOpenLinearEquivOfIsLocalizedModule f _

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
        (((Scheme.Modules.unit X).cohomologyOnZeroComplComplBasicOpenLinearEquiv f
          (Algebra.linearMap Γ(X, ⊤) (Localization.Away f) ∘ₗ
            (cohomologyOnZeroTopUnitLinearEquiv X).toLinearMap)).symm y) :=
  (rfl)

end BasicOpen

end AlgebraicGeometry.Scheme.Modules
