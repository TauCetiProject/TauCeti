/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.Homotopy
public import TauCeti.RepresentationTheory.Continuous.Coinduced
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Resolution.Basic

/-!
# Comparing a contractible complex with the coinduced resolution

Mathlib computes continuous cohomology from the shifted coinduced resolution
`TopRep.resolution' X`, the complex `C(G, X) → C(G, C(G, X)) → ⋯` augmented by the constant
functions `X → C(G, X)`. Each of its terms is coinduced, so equivariant maps into it are determined
by linear maps evaluated at `1` (`ContRepresentation.coind₁Lift`). This file records the
consequence that makes it the target of comparison maps: every complex `J` of topological
representations augmented by `X` and contractible by maps that need **not** be equivariant maps
equivariantly into it, over the identity of `X`, and uniquely up to homotopy.

The contraction data is `TopRep.ResolutionContraction X J`: an equivariant augmentation
`ι : X ⟶ J⁰`, linear maps `proj : J⁰ → X` and `hom n : Jⁿ⁺¹ → Jⁿ` with
`proj ∘ ι = id`, `ι ∘ proj + hom 0 ∘ d = id` and `d ∘ hom n + hom (n + 1) ∘ d = id`, together with
joint continuity of their conjugates `x • hom n (x⁻¹ • v)` in `v` and `x`. For smooth discrete
representations the continuity is automatic (`TauCeti.IsSmoothDiscrete.continuous_conj`, in the
smooth discrete module).

The comparison `TopRep.ResolutionContraction.comparison` is built degree by degree from the lift
into a coinduced representation: `F⁰ v x = x • proj (x⁻¹ • v)` and
`Fⁿ⁺¹ v x = Fⁿ (x • hom n (x⁻¹ • v))`. The conjugate `x • hom n (x⁻¹ • -)` of the contraction is
again a contraction, and this is what makes `F` commute with the differentials. For a locally
compact group, any two chain maps from `J` into a coinduced resolution `TopRep.resolution' Z`
agreeing on the augmentation are homotopic (`TopRep.ResolutionContraction.homotopy`), for any
`Z`: an equivariant map into a coinduced term that vanishes on the image of the previous
differential extends along the next one
(`TopRep.ResolutionContraction.desc`), which builds the homotopy degree by degree. Consequently the
map `Hⁿ(Jᴳ) → Hⁿ(G, X)` on the cohomology of invariants does not depend on the choice of comparison.

The coinduced resolution is itself contracted by evaluation at `1`
(`TopRep.resolutionContraction`), and the comparison it produces is the identity
(`TopRep.comparison_resolutionContraction`).

A cocycle on a complex built from other resolutions, such as the tensor-induced resolution of an
open subgroup in Evens' multiplicative transfer, defines a class in continuous cohomology through
this comparison; the resulting maps and classes are in
`TauCeti.RepresentationTheory.Homological.ContCohomology.Resolution.Cohomology`.

## Main definitions

* `TopRep.ResolutionContraction X J`: a non-equivariant contraction of a complex `J` of
  topological representations onto the augmentation `X → J⁰`.
* `TopRep.ResolutionContraction.comparison`: the equivariant comparison map from `J` to the
  shifted coinduced resolution of `X`.
* `TopRep.ResolutionContraction.homotopy`: two chain maps into a coinduced resolution agreeing
  on the augmentation are homotopic.
* `TopRep.resolutionContraction`: the contraction of the coinduced resolution by evaluation at `1`.

## Main results

* `TopRep.ResolutionContraction.ι_comp_comparison_f_zero`: the comparison lies over the identity
  of `X`, carrying the augmentation `ι` to the constant functions.
* `TopRep.ResolutionContraction.comparison_f_zero_apply_apply` and
  `TopRep.ResolutionContraction.comparison_f_succ_apply_apply`: the pointwise formulas, and
  `TopRep.ResolutionContraction.d_comparison_f_apply`: commutation with the differentials.
* `TopRep.ResolutionContraction.homologyMap_eq_homologyMap_comparison`: every chain map over the
  identity of `X` induces the same map on the cohomology of invariants as the comparison.
* `TopRep.comparison_resolutionContraction`: evaluation at `1` compares the coinduced resolution
  with itself by the identity.

## References

* C. A. Weibel, *An Introduction to Homological Algebra*, Comparison Theorem 2.2.6 and its dual
  2.3.7, for the comparison of a resolution with one by relatively injective objects.
* L. Evens, *A generalization of the transfer map in the cohomology of groups*, Trans. Amer. Math.
  Soc. 108 (1963), §§2–5, for the comparison of tensor-induced resolutions.
-/

public section

open CategoryTheory ContRepresentation

namespace TopRep

universe u v w

variable {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] [TopologicalSpace G]

/-- A **contraction of a complex `J` of topological representations onto `X`**: an equivariant
augmentation `ι : X ⟶ J⁰` together with linear maps `proj : J⁰ → X` and `hom n : Jⁿ⁺¹ → Jⁿ`, not
assumed equivariant, satisfying `proj ∘ ι = id`, `ι ∘ proj + hom 0 ∘ d = id` on `J⁰` and
`d ∘ hom n + hom (n + 1) ∘ d = id` on `Jⁿ⁺¹`. The conjugates `x • proj (x⁻¹ • v)` and
`x • hom n (x⁻¹ • v)` are required to be jointly continuous in `v` and `x`. Such a contraction
makes `X → J` exact, and gives the equivariant comparison
`TopRep.ResolutionContraction.comparison` from `J` to the coinduced resolution of `X`. -/
structure ResolutionContraction (X : TopRep.{max v w} k G)
    (J : CochainComplex (TopRep.{max v w} k G) ℕ) where
  /-- The equivariant augmentation `X ⟶ J⁰`. -/
  ι : X ⟶ J.X 0
  /-- The retraction `J⁰ → X` of the augmentation, which need not be equivariant. -/
  proj : (J.X 0).V →ₗ[k] X.V
  /-- The contracting homotopy `Jⁿ⁺¹ → Jⁿ`, which need not be equivariant. -/
  hom (n : ℕ) : (J.X (n + 1)).V →ₗ[k] (J.X n).V
  /-- The retraction is a left inverse of the augmentation. -/
  proj_ι (x : X.V) : proj (ι.hom x) = x
  /-- The contraction identity on `J⁰`: `ι ∘ proj + hom 0 ∘ d = id`. -/
  ι_proj_add_hom_d (v : (J.X 0).V) : ι.hom (proj v) + hom 0 ((J.d 0 1).hom v) = v
  /-- The contraction identity on `Jⁿ⁺¹`: `d ∘ hom n + hom (n + 1) ∘ d = id`. -/
  d_hom_add_hom_d (n : ℕ) (v : (J.X (n + 1)).V) :
    (J.d n (n + 1)).hom (hom n v) + hom (n + 1) ((J.d (n + 1) (n + 2)).hom v) = v
  /-- The conjugates `x • proj (x⁻¹ • v)` of the retraction are jointly continuous. -/
  continuous_proj : Continuous fun p : (J.X 0).V × G ↦ X.ρ p.2 (proj ((J.X 0).ρ p.2⁻¹ p.1))
  /-- The conjugates `x • hom n (x⁻¹ • v)` of the contracting homotopy are jointly continuous. -/
  continuous_hom (n : ℕ) :
    Continuous fun p : (J.X (n + 1)).V × G ↦ (J.X n).ρ p.2 (hom n ((J.X (n + 1)).ρ p.2⁻¹ p.1))

namespace ResolutionContraction

variable {X : TopRep.{max v w} k G} {J : CochainComplex (TopRep.{max v w} k G) ℕ}
  (c : ResolutionContraction X J)

/-- The conjugate of the degree-zero contraction identity by `x : G`. -/
private theorem ι_proj_add_hom_d_conj (x : G) (v : (J.X 0).V) :
    c.ι.hom (X.ρ x (c.proj ((J.X 0).ρ x⁻¹ v))) +
      (J.X 0).ρ x (c.hom 0 ((J.X 1).ρ x⁻¹ ((J.d 0 1).hom v))) = v := by
  rw [c.ι.hom.isIntertwining, ← (J.d 0 1).hom.isIntertwining, ← map_add, c.ι_proj_add_hom_d]
  exact Representation.self_inv_apply (J.X 0).ρ.toRepresentation x v

/-- The conjugate of the positive-degree contraction identity by `x : G`. -/
private theorem d_hom_add_hom_d_conj (n : ℕ) (x : G) (v : (J.X (n + 1)).V) :
    (J.d n (n + 1)).hom ((J.X n).ρ x (c.hom n ((J.X (n + 1)).ρ x⁻¹ v))) +
      (J.X (n + 1)).ρ x
        (c.hom (n + 1) ((J.X (n + 2)).ρ x⁻¹ ((J.d (n + 1) (n + 2)).hom v))) = v := by
  rw [(J.d n (n + 1)).hom.isIntertwining, ← (J.d (n + 1) (n + 2)).hom.isIntertwining,
    ← map_add, c.d_hom_add_hom_d]
  exact Representation.self_inv_apply (J.X (n + 1)).ρ.toRepresentation x v

variable [IsTopologicalGroup G]

/-- The components of the comparison map `TopRep.ResolutionContraction.comparison`. -/
private noncomputable def comparisonF : (n : ℕ) → J.X n ⟶ (resolution' X).X n
  | 0 => ofHom (coind₁Lift c.proj c.continuous_proj)
  | n + 1 => ofHom (coind₁Lift ((comparisonF n).hom.toLinearMap ∘ₗ c.hom n) <|
      (comparisonF n).hom.continuous.comp (c.continuous_hom n) |>.congr fun p ↦
        (comparisonF n).hom.isIntertwining p.2 _)

private theorem comparisonF_zero_apply_apply (v : (J.X 0).V) (x : G) :
    (c.comparisonF 0).hom v x = X.ρ x (c.proj ((J.X 0).ρ x⁻¹ v)) :=
  coind₁Lift_apply_apply _ _ v x

private theorem comparisonF_succ_apply_apply (n : ℕ) (v : (J.X (n + 1)).V) (x : G) :
    (c.comparisonF (n + 1)).hom v x =
      (c.comparisonF n).hom ((J.X n).ρ x (c.hom n ((J.X (n + 1)).ρ x⁻¹ v))) :=
  (coind₁Lift_apply_apply _ _ v x).trans ((c.comparisonF n).hom.isIntertwining x _).symm

private theorem comparisonF_zero_ι (a : X.V) :
    (c.comparisonF 0).hom (c.ι.hom a) = (d X 0).hom a := by
  ext x
  rw [comparisonF_zero_apply_apply, ← c.ι.hom.isIntertwining, c.proj_ι]
  exact Representation.self_inv_apply X.ρ.toRepresentation x a

private theorem d_comparisonF (n : ℕ) (v : (J.X n).V) :
    (d X (n + 1)).hom ((c.comparisonF n).hom v) =
      (c.comparisonF (n + 1)).hom ((J.d n (n + 1)).hom v) := by
  induction n with
  | zero =>
    ext x : 1
    rw [hom_d_succ_apply_apply, comparisonF_succ_apply_apply, comparisonF_zero_apply_apply,
      ← comparisonF_zero_ι, sub_eq_iff_eq_add', ← map_add]
    -- `J.X (0 + 1)` and `J.X 1` agree by evaluation of the numeral, as do `J.d 0 (0 + 1)` and
    -- `J.d 0 1`, so the conjugated contraction identity applies as stated.
    exact congrArg _ (c.ι_proj_add_hom_d_conj x v).symm
  | succ n ih =>
    ext x : 1
    rw [hom_d_succ_apply_apply, comparisonF_succ_apply_apply, comparisonF_succ_apply_apply, ih,
      sub_eq_iff_eq_add', ← map_add]
    exact congrArg _ (c.d_hom_add_hom_d_conj n x v).symm

/-- The **comparison map** from a complex contracted onto `X` to the shifted coinduced resolution
of `X`. It is equivariant, commutes with the differentials, and lies over the identity of `X`
(`TopRep.ResolutionContraction.ι_comp_comparison_f_zero`). In degree `0` it is
`v ↦ (x ↦ x • proj (x⁻¹ • v))`, and in degree `n + 1` it is
`v ↦ (x ↦ Fⁿ (x • hom n (x⁻¹ • v)))` for the degree-`n` component `Fⁿ`. -/
noncomputable def comparison : J ⟶ resolution' X where
  f := c.comparisonF
  comm' i j hij := by
    obtain rfl : i + 1 = j := hij
    ext v : 3
    simp only [hom_comp, ContIntertwiningMap.toContinuousLinearMap_comp,
      ContinuousLinearMap.comp_apply, ContIntertwiningMap.toContinuousLinearMap_apply,
      CochainComplex.of_d, resolution'd_eq]
    exact c.d_comparisonF i v

/-- The comparison in degree `0`, at a point: `F⁰ v x = x • proj (x⁻¹ • v)`. -/
@[simp]
theorem comparison_f_zero_apply_apply (v : (J.X 0).V) (x : G) :
    (c.comparison.f 0).hom v x = X.ρ x (c.proj ((J.X 0).ρ x⁻¹ v)) :=
  c.comparisonF_zero_apply_apply v x

/-- The comparison in degree `n + 1`, at a point: `Fⁿ⁺¹ v x = Fⁿ (x • hom n (x⁻¹ • v))`. -/
@[simp]
theorem comparison_f_succ_apply_apply (n : ℕ) (v : (J.X (n + 1)).V) (x : G) :
    (c.comparison.f (n + 1)).hom v x =
      (c.comparison.f n).hom ((J.X n).ρ x (c.hom n ((J.X (n + 1)).ρ x⁻¹ v))) :=
  c.comparisonF_succ_apply_apply n v x

/-- The comparison lies over the identity of `X`: it carries the augmentation `ι` to the
augmentation `d X 0` of the coinduced resolution by constant functions. -/
@[reassoc (attr := simp)]
theorem ι_comp_comparison_f_zero : c.ι ≫ c.comparison.f 0 = d X 0 := by
  ext a : 3
  simp only [hom_comp, ContIntertwiningMap.toContinuousLinearMap_comp,
    ContinuousLinearMap.comp_apply, ContIntertwiningMap.toContinuousLinearMap_apply]
  exact c.comparisonF_zero_ι a

/-- The comparison commutes with the differentials, on elements. -/
theorem d_comparison_f_apply (n : ℕ) (v : (J.X n).V) :
    (d X (n + 1)).hom ((c.comparison.f n).hom v) =
      (c.comparison.f (n + 1)).hom ((J.d n (n + 1)).hom v) :=
  c.d_comparisonF n v

section Homotopy

variable [LocallyCompactSpace G] {Y Z : TopRep.{max v w} k G}

/-- The extension of an equivariant map `r : Jⁿ ⟶ C(G, Y)` along the differential
`Jⁿ → Jⁿ⁺¹`: the lift to the coinduced representation of `v ↦ r (hom n v) 1`. When `r` vanishes
on the image of the previous differential, or on the augmentation if `n = 0`, it is an extension
(`TopRep.ResolutionContraction.d_comp_desc_zero`, `TopRep.ResolutionContraction.d_comp_desc_succ`).
-/
noncomputable def desc (n : ℕ) (r : J.X n ⟶ coind₁ Y) : J.X (n + 1) ⟶ coind₁ Y :=
  ofHom (coind₁Lift
    ((ContinuousMap.evalCLM k (1 : G)).toLinearMap ∘ₗ r.hom.toLinearMap ∘ₗ c.hom n) <|
      continuous_eval.comp ((r.hom.continuous.comp (c.continuous_hom n)).prodMk continuous_snd)
        |>.congr fun p ↦ by
          have h := congrArg (fun F : C(G, Y.V) ↦ F p.2)
            (r.hom.isIntertwining p.2 (c.hom n ((J.X (n + 1)).ρ p.2⁻¹ p.1)))
          simp only [coind₁_apply_apply, inv_mul_cancel] at h
          -- The two sides differ only in how the maps are coerced to functions: through
          -- `toContinuousLinearMap` and `LinearMap.comp` in the goal, directly in `h`.
          exact h)

/-- The extension `desc` at the point `1`: `desc n r v 1 = r (hom n v) 1`. -/
theorem desc_apply_one (n : ℕ) (r : J.X n ⟶ coind₁ Y) (v : (J.X (n + 1)).V) :
    (c.desc n r).hom v 1 = r.hom (c.hom n v) 1 :=
  coind₁Lift_apply_one _ _ v

/-- In degree `0`, `desc` extends a map killing the augmentation along the first differential. -/
theorem d_comp_desc_zero (r : J.X 0 ⟶ coind₁ Y) (hr : c.ι ≫ r = 0) :
    J.d 0 1 ≫ c.desc 0 r = r := by
  ext1
  refine ContIntertwiningMap.coind₁_ext fun v ↦ ?_
  have hr' : r.hom (c.ι.hom (c.proj v)) = 0 := congrArg (fun f ↦ f.hom (c.proj v)) hr
  have h : c.hom 0 ((J.d 0 1).hom v) = v - c.ι.hom (c.proj v) :=
    eq_sub_of_add_eq' (c.ι_proj_add_hom_d v)
  calc (J.d 0 1 ≫ c.desc 0 r).hom v 1 = r.hom (c.hom 0 ((J.d 0 1).hom v)) 1 :=
        c.desc_apply_one 0 r _
    _ = r.hom v 1 := by rw [h, map_sub, hr', sub_zero]

/-- In positive degree, `desc` extends a map killing the image of the previous differential
along the next one. -/
theorem d_comp_desc_succ (n : ℕ) (r : J.X (n + 1) ⟶ coind₁ Y) (hr : J.d n (n + 1) ≫ r = 0) :
    J.d (n + 1) (n + 2) ≫ c.desc (n + 1) r = r := by
  ext1
  refine ContIntertwiningMap.coind₁_ext fun v ↦ ?_
  have hr' : r.hom ((J.d n (n + 1)).hom (c.hom n v)) = 0 :=
    congrArg (fun f ↦ f.hom (c.hom n v)) hr
  have h : c.hom (n + 1) ((J.d (n + 1) (n + 2)).hom v) = v - (J.d n (n + 1)).hom (c.hom n v) :=
    eq_sub_of_add_eq' (c.d_hom_add_hom_d n v)
  calc (J.d (n + 1) (n + 2) ≫ c.desc (n + 1) r).hom v 1 =
        r.hom (c.hom (n + 1) ((J.d (n + 1) (n + 2)).hom v)) 1 :=
        c.desc_apply_one (n + 1) r _
    _ = r.hom v 1 := by rw [h, map_sub, hr', sub_zero]

/-- **A chain map into a coinduced resolution killing the augmentation is null-homotopic**,
by an equivariant homotopy whose components are built degree by degree with `desc`. The target
is the coinduced resolution of any `Z`, not only of `X`. -/
noncomputable def nullHomotopy (e : J ⟶ resolution' Z) (he : c.ι ≫ e.f 0 = 0) : Homotopy e 0 :=
  Homotopy.mkCoinductive e (c.desc (Y := resolutionX Z 0) 0 (e.f 0))
    (c.d_comp_desc_zero _ he).symm
    (c.desc (Y := resolutionX Z 1) 1 (e.f 1 - c.desc 0 (e.f 0) ≫ (resolution' Z).d 0 1))
    (by
      rw [c.d_comp_desc_succ (Y := resolutionX Z 1) 0 _ ?_, add_sub_cancel]
      rw [Preadditive.comp_sub, ← e.comm 0 1, ← Category.assoc,
        c.d_comp_desc_zero (Y := resolutionX Z 0) _ he, sub_self])
    fun n ⟨f, f', hf⟩ ↦ ⟨c.desc (Y := resolutionX Z (n + 2)) (n + 2)
        (e.f (n + 2) - f' ≫ (resolution' Z).d (n + 1) (n + 2)), by
      rw [c.d_comp_desc_succ (Y := resolutionX Z (n + 2)) (n + 1) _ ?_, add_sub_cancel]
      rw [Preadditive.comp_sub, ← e.comm (n + 1) (n + 2), ← Category.assoc, hf,
        Preadditive.add_comp, Category.assoc, HomologicalComplex.d_comp_d, Limits.comp_zero,
        zero_add]
      exact sub_self _⟩

/-- **Uniqueness of comparisons up to homotopy.** Two chain maps from `J` to the coinduced
resolution of `Z` that agree on the augmentation `ι` are homotopic. Taking `Z = X` gives
uniqueness of the comparison; other `Z` compare chain maps lying over a coefficient morphism
`X ⟶ Z`. -/
noncomputable def homotopy (φ ψ : J ⟶ resolution' Z) (h : c.ι ≫ φ.f 0 = c.ι ≫ ψ.f 0) :
    Homotopy φ ψ :=
  Homotopy.equivSubZero.symm <| c.nullHomotopy (φ - ψ) <| by
    rw [HomologicalComplex.sub_f_apply, Preadditive.comp_sub, h, sub_self]

/-- Every chain map from `J` to the coinduced resolution of `X` over the identity of `X` is
homotopic to the comparison. -/
noncomputable def homotopyComparison (φ : J ⟶ resolution' X) (hφ : c.ι ≫ φ.f 0 = d X 0) :
    Homotopy φ c.comparison :=
  c.homotopy φ c.comparison (by rw [hφ, ι_comp_comparison_f_zero])

/-- **The comparison is canonical on cohomology.** On the cohomology of the invariants, every chain
map from `J` to the coinduced resolution of `X` over the identity of `X` induces the same map
`Hⁿ(Jᴳ) → Hⁿ(G, X)` as the comparison. -/
theorem homologyMap_eq_homologyMap_comparison (φ : J ⟶ resolution' X)
    (hφ : c.ι ≫ φ.f 0 = d X 0) (n : ℕ) :
    HomologicalComplex.homologyMap
        (((invariantsFunctor k G).mapHomologicalComplex _).map φ) n =
      HomologicalComplex.homologyMap
        (((invariantsFunctor k G).mapHomologicalComplex _).map c.comparison) n :=
  ((invariantsFunctor k G).mapHomotopy (c.homotopyComparison φ hφ)).homologyMap_eq n

end Homotopy

end ResolutionContraction

variable [IsTopologicalGroup G]

/-- The **contraction of the coinduced resolution by evaluation at `1`**: the augmentation is the
inclusion of constant functions, and both the retraction and the contracting homotopy evaluate
the outermost variable at `1`. Its conjugates are evaluations at other points, which are jointly
continuous because `G` is locally compact. -/
noncomputable def resolutionContraction [LocallyCompactSpace G] (X : TopRep.{max v w} k G) :
    ResolutionContraction X (resolution' X) where
  ι := d X 0
  proj := (ContinuousMap.evalCLM k (1 : G)).toLinearMap
  hom n := (ContinuousMap.evalCLM k (1 : G)).toLinearMap
  proj_ι _ := (rfl)
  ι_proj_add_hom_d v := by
    have hd : (resolution' X).d 0 1 = d X 1 := CochainComplex.of_d _ _ 0
    have h := hom_d_succ_apply_apply X 0 v 1
    rw [hd]
    simp only [ContinuousLinearMap.coe_coe, ContinuousMap.evalCLM_apply]
    rw [h, add_sub_cancel]
  d_hom_add_hom_d n v := by
    have hd (m : ℕ) : (resolution' X).d m (m + 1) = d X (m + 1) := CochainComplex.of_d _ _ m
    rw [hd, hd]
    simp only [ContinuousLinearMap.coe_coe, ContinuousMap.evalCLM_apply]
    rw [hom_d_succ_apply_apply, add_sub_cancel]
  continuous_proj := continuous_eval.congr fun p ↦ by
    simp only [ContinuousLinearMap.coe_coe, ContinuousMap.evalCLM_apply, coind₁_apply_apply,
      inv_inv, mul_one]
    exact (Representation.self_inv_apply X.ρ.toRepresentation p.2 _).symm
  continuous_hom n := continuous_eval.congr fun p ↦ by
    simp only [ContinuousLinearMap.coe_coe, ContinuousMap.evalCLM_apply, coind₁_apply_apply,
      inv_inv, mul_one]
    exact (Representation.self_inv_apply (resolutionX X (n + 1)).ρ.toRepresentation p.2 _).symm

section ResolutionContraction

variable [LocallyCompactSpace G] (X : TopRep.{max v w} k G)

/-- The augmentation of the coinduced resolution is the inclusion of constant functions. -/
@[simp]
theorem resolutionContraction_ι : (resolutionContraction X).ι = d X 0 :=
  (rfl)

/-- The retraction of the coinduced resolution evaluates at `1`. -/
@[simp]
theorem resolutionContraction_proj_apply (v : ((resolution' X).X 0).V) :
    (resolutionContraction X).proj v = v 1 :=
  (rfl)

/-- The contracting homotopy of the coinduced resolution evaluates at `1`. -/
@[simp]
theorem resolutionContraction_hom_apply (n : ℕ) (v : ((resolution' X).X (n + 1)).V) :
    (resolutionContraction X).hom n v = v 1 :=
  (rfl)

/-- **The coinduced resolution compares with itself by the identity**: the comparison map given by
its contraction by evaluation at `1` is the identity. -/
theorem comparison_resolutionContraction :
    (resolutionContraction X).comparison = 𝟙 (resolution' X) := by
  have h (n : ℕ) (v : ((resolution' X).X n).V) :
      ((resolutionContraction X).comparison.f n).hom v = v := by
    induction n with
    | zero =>
      ext x : 1
      rw [ResolutionContraction.comparison_f_zero_apply_apply, resolutionContraction_proj_apply,
        resolutionX_succ_ρ_apply_apply, inv_inv, mul_one]
      exact Representation.self_inv_apply X.ρ.toRepresentation x _
    | succ n ih =>
      ext x : 1
      rw [ResolutionContraction.comparison_f_succ_apply_apply, ih,
        resolutionContraction_hom_apply, resolutionX_succ_ρ_apply_apply, inv_inv, mul_one]
      exact Representation.self_inv_apply (resolutionX X (n + 1)).ρ.toRepresentation x _
  ext n v : 4
  exact h n v

end ResolutionContraction

end TopRep
