/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Exact.Basic
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import TauCeti.Algebra.Category.ModuleCat.Biproducts
public import TauCeti.AlgebraicTopology.Cohomology.MayerVietoris.Basic

/-!
# The Mayer–Vietoris sequence in singular cohomology as exact sequences of modules

Let `U` and `V` be open subsets of a space `X` with `U ∪ V = X`. The Mayer–Vietoris sequence

`⋯ ⟶ Hⁿ(X) ⟶ Hⁿ(U) × Hⁿ(V) ⟶ Hⁿ(U ∩ V) ⟶ Hⁿ⁺¹(X) ⟶ ⋯`

of `TauCeti.AlgebraicTopology.Cohomology.MayerVietoris.Basic` is stated there with the biproduct
`Hⁿ(U) ⊞ Hⁿ(V)` of the category of `k`-modules as middle term, and its exactness as exactness of
short complexes. This file restates it with the product module `Hⁿ(U) × Hⁿ(V)` as middle term and
its exactness as `Function.Exact` of linear maps, the form in which it is used in diagram chases
such as the five lemma (`LinearMap.bijective_of_surjective_of_bijective_of_bijective_of_injective`).

## Main definitions and results

* `TopCat.singularCohomologyMayerVietorisToProd`: the restrictions `Hⁿ(X) ⟶ Hⁿ(U) × Hⁿ(V)`.
* `TopCat.singularCohomologyMayerVietorisFromProd`: the difference of the restrictions
  `Hⁿ(U) × Hⁿ(V) ⟶ Hⁿ(U ∩ V)`.
* `TopCat.exact_singularCohomologyMayerVietorisToProd_fromProd`,
  `TopCat.exact_singularCohomologyMayerVietorisFromProd_δ`,
  `TopCat.exact_singularCohomologyMayerVietorisδ_toProd`: exactness of the Mayer–Vietoris sequence
  at its three kinds of terms.
* `TopCat.injective_singularCohomologyMayerVietorisToProd_zero`: injectivity of its first map in
  degree `0`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.1 (the Mayer–Vietoris sequences in cohomology).
-/

public section

noncomputable section

open CategoryTheory Limits

universe u v w

namespace TopCat

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] (R : C)
  (k : Type*) [Ring k] [Linear k C] (M : C) {X : TopCat.{w}}

section Maps

variable (U V : Set X)

/-- The first map `Hⁿ(X) ⟶ Hⁿ(U) × Hⁿ(V)` of the Mayer–Vietoris sequence in singular cohomology,
as a linear map to the product module, with components the restrictions to `U` and `V`. -/
def singularCohomologyMayerVietorisToProd (n : ℕ) :
    X.singularCohomology R k M n →ₗ[k]
      (of U).singularCohomology R k M n × (of V).singularCohomology R k M n :=
  (TopCat.singularCohomologyMap (ofHom (ContinuousMap.subtypeVal U)) n).hom.prod
    (TopCat.singularCohomologyMap (ofHom (ContinuousMap.subtypeVal V)) n).hom

@[simp]
lemma singularCohomologyMayerVietorisToProd_apply (n : ℕ) (x : X.singularCohomology R k M n) :
    singularCohomologyMayerVietorisToProd R k M U V n x =
      (TopCat.singularCohomologyMap (ofHom (ContinuousMap.subtypeVal U)) n x,
        TopCat.singularCohomologyMap (ofHom (ContinuousMap.subtypeVal V)) n x) :=
  LinearMap.prod_apply _ _ x

/-- The second map `Hⁿ(U) × Hⁿ(V) ⟶ Hⁿ(U ∩ V)` of the Mayer–Vietoris sequence in singular
cohomology, as a linear map from the product module: the difference of the restrictions. -/
def singularCohomologyMayerVietorisFromProd (n : ℕ) :
    (of U).singularCohomology R k M n × (of V).singularCohomology R k M n →ₗ[k]
      (of ↥(U ∩ V)).singularCohomology R k M n :=
  (TopCat.singularCohomologyMap (ofHom (ContinuousMap.inclusion Set.inter_subset_left))
      n).hom.coprod
    (-(TopCat.singularCohomologyMap (ofHom (ContinuousMap.inclusion Set.inter_subset_right))
      n).hom)

@[simp]
lemma singularCohomologyMayerVietorisFromProd_apply (n : ℕ)
    (y : (of U).singularCohomology R k M n) (z : (of V).singularCohomology R k M n) :
    singularCohomologyMayerVietorisFromProd R k M U V n (y, z) =
      TopCat.singularCohomologyMap (ofHom (ContinuousMap.inclusion Set.inter_subset_left)) n y -
        TopCat.singularCohomologyMap (ofHom (ContinuousMap.inclusion Set.inter_subset_right))
          n z := by
  simp [singularCohomologyMayerVietorisFromProd, sub_eq_add_neg]

/-- Under the identification of the biproduct with the product module, the first map of the
Mayer–Vietoris sequence is `TopCat.singularCohomologyMayerVietorisToProd`. -/
@[simp]
lemma biprodIsoProd_hom_singularCohomologyMayerVietorisToBiprod_apply (n : ℕ)
    (x : X.singularCohomology R k M n) :
    (ModuleCat.biprodIsoProd _ _).hom (singularCohomologyMayerVietorisToBiprod R k M U V n x) =
      singularCohomologyMayerVietorisToProd R k M U V n x := by
  rw [ModuleCat.biprodIsoProd_hom_apply, singularCohomologyMayerVietorisToProd_apply,
    ← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
    singularCohomologyMayerVietorisToBiprod_fst, singularCohomologyMayerVietorisToBiprod_snd]

/-- Under the identification of the biproduct with the product module, the second map of the
Mayer–Vietoris sequence is `TopCat.singularCohomologyMayerVietorisFromProd`. -/
lemma singularCohomologyMayerVietorisFromBiprod_apply (n : ℕ)
    (x : ↑((of U).singularCohomology R k M n ⊞ (of V).singularCohomology R k M n)) :
    singularCohomologyMayerVietorisFromBiprod R k M U V n x =
      singularCohomologyMayerVietorisFromProd R k M U V n
        ((ModuleCat.biprodIsoProd _ _).hom x) := by
  have h : singularCohomologyMayerVietorisFromBiprod R k M U V n =
      (ModuleCat.biprodIsoProd _ _).hom ≫
        ModuleCat.ofHom (singularCohomologyMayerVietorisFromProd R k M U V n) := by
    apply biprod.hom_ext' <;> ext y <;> simp
  rw [h, ConcreteCategory.comp_apply, ModuleCat.ofHom_apply]

end Maps

/-! ### Exactness -/

variable {U V : Set X} (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = Set.univ)

include hU hV hUV in
/-- **Exactness of the Mayer–Vietoris sequence at `Hⁿ(U) × Hⁿ(V)`**, as linear maps. -/
lemma exact_singularCohomologyMayerVietorisToProd_fromProd (n : ℕ) :
    Function.Exact (singularCohomologyMayerVietorisToProd R k M U V n)
      (singularCohomologyMayerVietorisFromProd R k M U V n) :=
  Function.Exact.of_ladder_linearEquiv_of_exact (e₁ := LinearEquiv.refl k _)
    (e₂ := (ModuleCat.biprodIsoProd _ _).toLinearEquiv) (e₃ := LinearEquiv.refl k _)
    (LinearMap.ext fun x ↦
      (biprodIsoProd_hom_singularCohomologyMayerVietorisToBiprod_apply R k M U V n x).symm)
    (LinearMap.ext fun x ↦ (singularCohomologyMayerVietorisFromBiprod_apply R k M U V n x).symm)
    ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
      (singularCohomologyMayerVietoris_exact₂ R k M hU hV hUV n))

/-- **Exactness of the Mayer–Vietoris sequence at `Hⁿ(U ∩ V)`**, as linear maps. -/
lemma exact_singularCohomologyMayerVietorisFromProd_δ (n m : ℕ) (h : n + 1 = m := by lia) :
    Function.Exact (singularCohomologyMayerVietorisFromProd R k M U V n)
      (singularCohomologyMayerVietorisδ R k M hU hV hUV n m h).hom :=
  Function.Exact.of_ladder_linearEquiv_of_exact
    (e₁ := (ModuleCat.biprodIsoProd _ _).toLinearEquiv) (e₂ := LinearEquiv.refl k _)
    (e₃ := LinearEquiv.refl k _)
    (LinearMap.ext fun x ↦ (singularCohomologyMayerVietorisFromBiprod_apply R k M U V n x).symm)
    (LinearMap.ext fun _ ↦ rfl)
    ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
      (singularCohomologyMayerVietoris_exact₃ R k M hU hV hUV n m h))

/-- **Exactness of the Mayer–Vietoris sequence at `Hᵐ(X)`**, as linear maps. -/
lemma exact_singularCohomologyMayerVietorisδ_toProd (n m : ℕ) (h : n + 1 = m := by lia) :
    Function.Exact (singularCohomologyMayerVietorisδ R k M hU hV hUV n m h).hom
      (singularCohomologyMayerVietorisToProd R k M U V m) :=
  Function.Exact.of_ladder_linearEquiv_of_exact (e₁ := LinearEquiv.refl k _)
    (e₂ := LinearEquiv.refl k _) (e₃ := (ModuleCat.biprodIsoProd _ _).toLinearEquiv)
    (LinearMap.ext fun _ ↦ rfl)
    (LinearMap.ext fun x ↦
      (biprodIsoProd_hom_singularCohomologyMayerVietorisToBiprod_apply R k M U V m x).symm)
    ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
      (singularCohomologyMayerVietoris_exact₁ R k M hU hV hUV n m h))

include hU hV hUV in
/-- The map `H⁰(X) ⟶ H⁰(U) × H⁰(V)` at the start of the Mayer–Vietoris sequence is injective. -/
lemma injective_singularCohomologyMayerVietorisToProd_zero :
    Function.Injective (singularCohomologyMayerVietorisToProd R k M U V 0) := by
  have := mono_singularCohomologyMayerVietorisToBiprod_zero R k M hU hV hUV
  intro x y hxy
  refine (ModuleCat.mono_iff_injective _).1 this
    ((ConcreteCategory.bijective_of_isIso (ModuleCat.biprodIsoProd _ _).hom).1 ?_)
  rwa [biprodIsoProd_hom_singularCohomologyMayerVietorisToBiprod_apply,
    biprodIsoProd_hom_singularCohomologyMayerVietorisToBiprod_apply]

end TopCat
