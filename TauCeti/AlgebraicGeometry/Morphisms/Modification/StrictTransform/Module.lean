/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Morphisms.Modification.StrictTransform.Basic
public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.SupportedKernel.Basic
public import TauCeti.AlgebraicGeometry.Modules.Pullback.Basic

/-!
# Strict transforms of modules along modifications

Let `f : X ⟶ S` and `φ : S' ⟶ S` be morphisms of schemes and `U ⊆ S` an open, typically a
modification witness of `φ`. Put `Y = X ×_S S'`, let `V = X ×_S φ⁻¹(U)` be the open over `U`
(`AlgebraicGeometry.Scheme.Hom.strictTransformOpen f φ U`) and `j : V ⟶ Y` its inclusion. For an
`𝒪_X`-module `M`, the *strict transform* of `M` is the quotient of `N = pr_X^* M` by its sections
vanishing on `V`, the kernel of `N ⟶ j_* (N|_V)`
(`AlgebraicGeometry.Scheme.Hom.strictTransformModule f φ U M`, built from
`AlgebraicGeometry.Scheme.Modules.supportedQuotient`). For the blowup of `S` along a closed
subscheme and `U` its complement, this is the strict transform of Stacks 080D.

For quasi-compact `j` and quasi-coherent `M`, the strict transform of `M` is quasi-coherent. For
`N = 𝒪_Y`, the kernel cuts out the strict transform of `f`, the scheme-theoretic closure of `V`
(`AlgebraicGeometry.Scheme.Modules.mem_range_supportedKernelι_app_iff_mem_ker_ideal` with
`AlgebraicGeometry.Scheme.Hom.strictTransform_def`), whose support is the closure of `V`
(`AlgebraicGeometry.Scheme.Hom.support_strictTransform`). When `Y ∖ V` is cut out on a
quasi-compact open `W` by finitely many sections `a₁, …, aᵣ` of `𝒪_Y`, a section of `N` over `W`
dies in the strict transform of `M` exactly when it is killed by a power of `(a₁, …, aᵣ)`.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.strictTransformModule f φ U M`: the strict transform of `M`, with
  projection `AlgebraicGeometry.Scheme.Hom.strictTransformModuleπ f φ U M` from `pr_X^* M` and
  factorization `AlgebraicGeometry.Scheme.Hom.strictTransformModuleDesc`.

## Main results

* `AlgebraicGeometry.Scheme.Hom.isQuasicoherent_strictTransformModule`: for quasi-compact `j`
  and quasi-coherent `M`, the strict transform of `M` is quasi-coherent.
* `AlgebraicGeometry.Scheme.Hom.strictTransformModuleπ_app_eq_zero_iff`: the sections of `pr_X^* M`
  dying in the strict transform of `M` are those vanishing on `V`.
* `AlgebraicGeometry.Scheme.Hom.strictTransformModuleπ_app_eq_zero_iff_mem_primaryComponent`: they
  are the power torsion for an ideal cutting out `Y ∖ V`.

## References

* [Stacks, Definition 31.34.1 (080D)](https://stacks.math.columbia.edu/tag/080D): the strict
  transform of a module along a blowup, which `strictTransformModule` generalises to
  modifications.
* [Stacks, Lemma 26.24.1 (01LC)](https://stacks.math.columbia.edu/tag/01LC) and
  [Stacks, Lemma 29.6.3 (01R8)](https://stacks.math.columbia.edu/tag/01R8).
* [Stacks, Lemma 47.9.1 (0A6R)](https://stacks.math.columbia.edu/tag/0A6R).
-/

public section

noncomputable section

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Hom

universe u

variable {X S S' : Scheme.{u}} (f : X ⟶ S) (φ : S' ⟶ S) (U : S.Opens) (M : X.Modules)

/-- The **strict transform of a module** `M` on `X` along `φ : S' ⟶ S` with respect to the open
`U ⊆ S`: the quotient of `pr_X^* M` on `X ×_S S'` by its sections vanishing on the open
`X ×_S φ⁻¹(U)` lying over `U`. This generalises the strict transform along a blowup. -/
@[stacks 080D "generalised from blowups to modifications"]
def strictTransformModule : (pullback f φ).Modules :=
  ((Modules.pullback (pullback.fst f φ)).obj M).supportedQuotient (strictTransformOpen f φ U).ι

/-- The strict transform of `M` is the supported quotient of `pr_X^* M` along the open over
`U`. -/
theorem strictTransformModule_def :
    strictTransformModule f φ U M =
      ((Modules.pullback (pullback.fst f φ)).obj M).supportedQuotient
        (strictTransformOpen f φ U).ι :=
  (rfl)

/-- The projection of `pr_X^* M` onto the strict transform of `M`. -/
def strictTransformModuleπ :
    (Modules.pullback (pullback.fst f φ)).obj M ⟶ strictTransformModule f φ U M :=
  ((Modules.pullback (pullback.fst f φ)).obj M).supportedQuotientπ (strictTransformOpen f φ U).ι

/-- The projection onto the strict transform of `M` is the projection onto the supported quotient
of `pr_X^* M` along the open over `U`, transported along `strictTransformModule_def`. -/
theorem strictTransformModuleπ_def :
    strictTransformModuleπ f φ U M =
      ((Modules.pullback (pullback.fst f φ)).obj M).supportedQuotientπ
        (strictTransformOpen f φ U).ι ≫ eqToHom (strictTransformModule_def f φ U M).symm :=
  (rfl)

instance epi_strictTransformModuleπ :
    Epi (strictTransformModuleπ f φ U M) :=
  inferInstanceAs (Epi (Modules.supportedQuotientπ _ _))

/-- The sections of `pr_X^* M` vanishing on the open over `U` die in the strict transform of
`M`. -/
@[reassoc (attr := simp)]
theorem supportedKernelι_comp_strictTransformModuleπ :
    ((Modules.pullback (pullback.fst f φ)).obj M).supportedKernelι (strictTransformOpen f φ U).ι ≫
      strictTransformModuleπ f φ U M = 0 :=
  Modules.supportedKernelι_comp_supportedQuotientπ _ _

/-- A morphism out of `pr_X^* M` killing the sections that vanish on the open over `U` factors
through the strict transform of `M`. -/
def strictTransformModuleDesc {P : (pullback f φ).Modules}
    (g : (Modules.pullback (pullback.fst f φ)).obj M ⟶ P)
    (hg : ((Modules.pullback (pullback.fst f φ)).obj M).supportedKernelι
      (strictTransformOpen f φ U).ι ≫ g = 0) :
    strictTransformModule f φ U M ⟶ P :=
  Modules.supportedQuotientDesc _ _ g hg

/-- The factorization through the strict transform of `M` recovers the original morphism. -/
@[reassoc (attr := simp)]
theorem strictTransformModuleπ_desc {P : (pullback f φ).Modules}
    (g : (Modules.pullback (pullback.fst f φ)).obj M ⟶ P)
    (hg : ((Modules.pullback (pullback.fst f φ)).obj M).supportedKernelι
      (strictTransformOpen f φ U).ι ≫ g = 0) :
    strictTransformModuleπ f φ U M ≫ strictTransformModuleDesc f φ U M g hg = g :=
  Modules.supportedQuotientπ_desc _ _ g hg

/-- **The strict transform of a quasi-coherent module is quasi-coherent** when the inclusion of
the open over `U` is quasi-compact. -/
instance isQuasicoherent_strictTransformModule [M.IsQuasicoherent]
    [QuasiCompact (strictTransformOpen f φ U).ι] :
    (strictTransformModule f φ U M).IsQuasicoherent :=
  Modules.isQuasicoherent_supportedQuotient _ _

/-- **The sections dying in the strict transform.** Over an open `W` of `Y = X ×_S S'`, a section
of `pr_X^* M` maps to zero in the strict transform of `M` exactly when it vanishes on the open over
`U`, that is, comes from the supported kernel. -/
theorem strictTransformModuleπ_app_eq_zero_iff {W : (pullback f φ).Opens}
    (s : Γ((Modules.pullback (pullback.fst f φ)).obj M, W)) :
    (strictTransformModuleπ f φ U M).app W s = 0 ↔
      s ∈ Set.range ((((Modules.pullback (pullback.fst f φ)).obj M).supportedKernelι
        (strictTransformOpen f φ U).ι).app W) :=
  Modules.supportedQuotientπ_app_eq_zero_iff _ _ s

/-- **The kernel of the strict transform of `M` is power torsion.** Let `W` be a quasi-compact open
of `Y = X ×_S S'` and `G` a finite set of sections of `𝒪_Y` over `W` whose basic opens cover
exactly the part of `W` over `U`. For quasi-coherent `M`, a section of `pr_X^* M` over `W` dies in
the strict transform of `M` exactly when it is killed by a power of the ideal generated by `G`. -/
theorem strictTransformModuleπ_app_eq_zero_iff_mem_primaryComponent [M.IsQuasicoherent]
    {W : (pullback f φ).Opens} (hW : IsCompact (SetLike.coe W))
    (G : Finset ((pullback f φ).presheaf.obj (.op W)))
    (hG : W ⊓ strictTransformOpen f φ U = ⨆ g : G, (pullback f φ).basicOpen g.val)
    (s : Γ((Modules.pullback (pullback.fst f φ)).obj M, W)) :
    (strictTransformModuleπ f φ U M).app W s = 0 ↔
      s ∈ (Ideal.span (G : Set ((pullback f φ).presheaf.obj (.op W)))).primaryComponent
        Γ((Modules.pullback (pullback.fst f φ)).obj M, W) := by
  rw [strictTransformModuleπ_app_eq_zero_iff]
  exact Modules.mem_range_supportedKernelι_app_iff_mem_primaryComponent_of_inf_eq _ _ hW G
    (by rwa [Scheme.Opens.opensRange_ι]) s

end AlgebraicGeometry.Scheme.Hom
