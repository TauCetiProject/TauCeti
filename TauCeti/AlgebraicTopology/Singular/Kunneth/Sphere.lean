/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.ProdThomPair

/-!
# The homology of a product with a sphere

Let `E` be a real normed space of dimension `d + 1`, so that its unit sphere `S = sphere 0 1` is a
`d`-sphere, and let `B` be any space. This file describes the singular homology of `S × B` in
terms of that of `B`, with coefficients in any object of an abelian category with coproducts:
there are short exact sequences

`0 ⟶ Hₘ₊₁(B × E, B × (E ∖ {0})) ⟶ Hₘ(B × (E ∖ {0})) ⟶ Hₘ(B × E) ⟶ 0`

(`TauCeti.shortExact_singularHomology_prodThomPair`), in which `B × (E ∖ {0})` is homotopy
equivalent to `S × B` (`TauCeti.prodThomPairPuncturedHomotopyEquivSphere`), `B × E` to `B`,
and the relative term is `H_{m-d}(B)` (`TauCeti.prodThomPairSingularHomologyIso`). The
sequence is the long exact sequence of the Thom pair of the product bundle `B × E → B`, which
breaks up because `b ↦ (b, x)` is a section of the punctured bundle for every `x ≠ 0`.

Read on `S × B`, for a point `x` of the sphere:

* the inclusion `B → S × B`, `b ↦ (x, b)`, is an isomorphism on `Hₘ` exactly when
  `H_{m-d}(B)` vanishes (`TauCeti.isIso_singularHomologyMap_prodMk_sphere_iff`), and always for
  `m < d` (`TauCeti.isIso_singularHomologyMap_prodMk_sphere_of_lt`);
* `Hₘ(S × B)` vanishes exactly when `Hₘ(B)` and `H_{m-d}(B)` do
  (`TauCeti.isZero_singularHomology_sphere_prod_iff`), and for `m < d` exactly when `Hₘ(B)`
  does (`TauCeti.isZero_singularHomology_sphere_prod_iff_of_lt`).

The sequences split, through the section, which is the Künneth formula
`Hₘ(Sᵈ × B) ≅ Hₘ(B) ⊕ H_{m-d}(B)` for a sphere factor, with no hypothesis on the coefficients or
on `B`; the splitting itself is not packaged here. When `Hₘ(B)` vanishes, the connecting
morphism gives `Hₘ(S × B) ≅ H_{m-d}(B)` (`TauCeti.singularHomologySphereProdIso`). For the unit
circle the same vanishing and isomorphism criteria are
`TauCeti.isZero_singularHomology_circle_prod_succ_iff` and
`TauCeti.isIso_singularHomologyMap_prodMk_const_one_succ_iff`, through the Wang sequence of a
mapping torus. These are the forms in which the homology of a space weakly equivalent to a product
with a sphere, such as the loop space of a quaternionic projective space, is computed.

## Main results

* `TauCeti.isIso_singularHomologyMap_prodMk_sphere_iff`: `H_{n+d}(B) → H_{n+d}(S × B)` is an
  isomorphism if and only if `Hₙ(B) = 0`.
* `TauCeti.isZero_singularHomology_sphere_prod_iff`: `H_{n+d}(S × B) = 0` if and only if
  `H_{n+d}(B) = 0` and `Hₙ(B) = 0`.
* `TauCeti.singularHomologySphereProdIso`: `H_{n+d}(S × B) ≅ Hₙ(B)` when `H_{n+d}(B) = 0`.

## References

* A. Hatcher, *Algebraic Topology*, Section 3.B, the Künneth formula, and Section 4.D, the Thom
  isomorphism of a product bundle.
-/

public section

noncomputable section

open CategoryTheory Limits Metric Module AlgebraicTopology

universe w v u

namespace TauCeti

variable {A : Type u} [Category.{v} A] [HasCoproducts.{w} A] [Abelian A] (R : A)
  {B : Type w} [TopologicalSpace B] {E : Type w} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The homotopy equivalence `B × (E ∖ {0}) ≃ₕ S × B` as a morphism of `TopCat`. -/
private abbrev puncturedHom : (prodThomPair B E).snd ⟶ TopCat.of (sphere (0 : E) 1 × B) :=
  TopCat.ofHom (prodThomPairPuncturedHomotopyEquivSphere B E).toFun

/-- The section at a point `x` of the unit sphere, followed by the homotopy equivalence with
`S × B`, is the inclusion `b ↦ (x, b)`. -/
private lemma prodThomPairPuncturedSection_comp_puncturedHom (x : sphere (0 : E) 1) :
    prodThomPairPuncturedSection B (x : E) (ne_zero_of_mem_unit_sphere x) ≫ puncturedHom =
      TopCat.ofHom ((ContinuousMap.const B x).prodMk (ContinuousMap.id B)) := by
  ext b : 1
  refine Prod.ext (Subtype.ext ?_) ?_
  · -- Radial projection fixes the points of the unit sphere.
    refine (coe_prodThomPairPuncturedHomotopyEquivSphere_apply_fst _).trans ?_
    refine (congrArg (fun y : E ↦ ‖y‖⁻¹ • y)
      (congrArg Prod.snd (prodThomPairPuncturedSection_apply _ _ b))).trans ?_
    simp [norm_eq_of_mem_sphere x]
  · exact (prodThomPairPuncturedHomotopyEquivSphere_apply_snd _).trans
      (congrArg Prod.fst (prodThomPairPuncturedSection_apply _ _ b))

variable (B) in
/-- The inclusion `b ↦ (x, b)` at a point of the unit sphere is an isomorphism on `Hₘ` exactly
when the inclusion `B × (E ∖ {0}) → B × E` is. -/
private lemma isIso_singularHomologyMap_prodMk_sphere_iff_isIso (x : sphere (0 : E) 1)
    (m : ℕ) :
    IsIso (((singularHomologyFunctor A m).obj R).map
        (TopCat.ofHom ((ContinuousMap.const B x).prodMk (ContinuousMap.id B)))) ↔
      IsIso (((singularHomologyFunctor A m).obj R).map (prodThomPair B E).map) := by
  have : IsIso (((singularHomologyFunctor A m).obj R).map (puncturedHom (B := B) (E := E))) :=
    (prodThomPairPuncturedHomotopyEquivSphere B E).isIso_homologyMap R m
  have hs := isIso_singularHomologyMap_prodThomPairPuncturedSection_comp_map R B (x : E)
    (ne_zero_of_mem_unit_sphere x) m
  rw [Functor.map_comp] at hs
  rw [← prodThomPairPuncturedSection_comp_puncturedHom x, Functor.map_comp, isIso_comp_right_iff]
  exact ⟨fun _ ↦ IsIso.of_isIso_comp_left (((singularHomologyFunctor A m).obj R).map
      (prodThomPairPuncturedSection B (x : E) (ne_zero_of_mem_unit_sphere x))) _,
    fun h ↦ IsIso.of_isIso_comp_right _ (((singularHomologyFunctor A m).obj R).map
      (prodThomPair B E).map)⟩

variable {R} (B) in
/-- `Hₘ(S × B)` vanishes exactly when `Hₘ(B)` and `Hₘ₊₁(B × E, B × (E ∖ {0}))` do. -/
private lemma isZero_singularHomology_sphere_prod_iff_isZero [Nontrivial E] (m : ℕ) :
    IsZero (((singularHomologyFunctor A m).obj R).obj (TopCat.of (sphere (0 : E) 1 × B))) ↔
      IsZero (((singularHomologyFunctor A m).obj R).obj (TopCat.of B)) ∧
        IsZero ((prodThomPair B E).singularHomology R (m + 1)) := by
  have hS := shortExact_singularHomology_prodThomPair R B E m
  rw [← ((prodThomPairPuncturedHomotopyEquivSphere B E).singularHomologyIso R m).isZero_iff,
    ← ((ContinuousMap.HomotopyEquiv.prodContractible B E).singularHomologyIso R m).isZero_iff]
  -- The middle term of a short exact sequence vanishes exactly when the outer two do.
  exact ⟨fun h ↦ ⟨@IsZero.of_epi _ _ _ _ _ _ hS.epi_g h,
      @IsZero.of_mono _ _ _ _ _ _ hS.mono_f h⟩,
    fun ⟨h₃, h₁⟩ ↦ hS.exact.isZero_X₂ (h₁.eq_of_src _ _) (h₃.eq_of_tgt _ _)⟩

variable {d : ℕ}

/-- **The inclusion `B → S × B` at a point of a `d`-sphere is an isomorphism on `H_{n+d}` exactly
when `Hₙ(B)` vanishes.** Here `S` is the unit sphere of a real normed space of dimension `d + 1`,
the inclusion is `b ↦ (x, b)`, and the coefficients lie in any abelian category with
coproducts. -/
theorem isIso_singularHomologyMap_prodMk_sphere_iff (hE : finrank ℝ E = d + 1)
    (x : sphere (0 : E) 1) {n m : ℕ} (h : n + d = m) :
    IsIso (((singularHomologyFunctor A m).obj R).map
        (TopCat.ofHom ((ContinuousMap.const B x).prodMk (ContinuousMap.id B)))) ↔
      IsZero (((singularHomologyFunctor A n).obj R).obj (TopCat.of B)) := by
  have := Module.finite_of_finrank_eq_succ hE
  have := Module.nontrivial_of_finrank_eq_succ hE
  exact (isIso_singularHomologyMap_prodMk_sphere_iff_isIso R B x m).trans
    (((shortExact_singularHomology_prodThomPair R B E m).isIso_g_iff).trans
      (prodThomPairSingularHomologyIso R B E n (m + 1) (by omega)).isZero_iff)

/-- **Below the dimension of the sphere, the inclusion `B → S × B` at a point is an isomorphism
on homology**: for `m < d` and `S` the unit sphere of a real normed space of dimension `d + 1`,
`b ↦ (x, b)` induces `Hₘ(B) ≅ Hₘ(S × B)`. -/
theorem isIso_singularHomologyMap_prodMk_sphere_of_lt (hE : finrank ℝ E = d + 1)
    (x : sphere (0 : E) 1) {m : ℕ} (hm : m < d) :
    IsIso (((singularHomologyFunctor A m).obj R).map
      (TopCat.ofHom ((ContinuousMap.const B x).prodMk (ContinuousMap.id B)))) := by
  have := Module.finite_of_finrank_eq_succ hE
  have := Module.nontrivial_of_finrank_eq_succ hE
  exact (isIso_singularHomologyMap_prodMk_sphere_iff_isIso R B x m).2
    (((shortExact_singularHomology_prodThomPair R B E m).isIso_g_iff).2
      (isZero_singularHomology_prodThomPair R B E (by omega)))

/-- **`H_{n+d}(S × B)` vanishes exactly when `H_{n+d}(B)` and `Hₙ(B)` do**, for `S` the unit
sphere of a real normed space of dimension `d + 1`, with coefficients in any abelian category with
coproducts. -/
theorem isZero_singularHomology_sphere_prod_iff (hE : finrank ℝ E = d + 1) {n m : ℕ}
    (h : n + d = m) :
    IsZero (((singularHomologyFunctor A m).obj R).obj (TopCat.of (sphere (0 : E) 1 × B))) ↔
      IsZero (((singularHomologyFunctor A m).obj R).obj (TopCat.of B)) ∧
        IsZero (((singularHomologyFunctor A n).obj R).obj (TopCat.of B)) := by
  have := Module.finite_of_finrank_eq_succ hE
  have := Module.nontrivial_of_finrank_eq_succ hE
  rw [isZero_singularHomology_sphere_prod_iff_isZero,
    (prodThomPairSingularHomologyIso R B E n (m + 1) (by omega)).isZero_iff]

/-- **Below the dimension of the sphere, `Hₘ(S × B)` vanishes exactly when `Hₘ(B)` does**, for
`m < d` and `S` the unit sphere of a real normed space of dimension `d + 1`. -/
theorem isZero_singularHomology_sphere_prod_iff_of_lt (hE : finrank ℝ E = d + 1) {m : ℕ}
    (hm : m < d) :
    IsZero (((singularHomologyFunctor A m).obj R).obj (TopCat.of (sphere (0 : E) 1 × B))) ↔
      IsZero (((singularHomologyFunctor A m).obj R).obj (TopCat.of B)) := by
  have := Module.finite_of_finrank_eq_succ hE
  have := Module.nontrivial_of_finrank_eq_succ hE
  rw [isZero_singularHomology_sphere_prod_iff_isZero,
    and_iff_left (isZero_singularHomology_prodThomPair R B E (by omega))]

/-- **`H_{n+d}(S × B) ≅ Hₙ(B)` when `H_{n+d}(B)` vanishes**, for `S` the unit sphere of a real
normed space `E` of dimension `d + 1`, with coefficients in any abelian category with coproducts.
It is the inverse of the connecting morphism `H_{n+d+1}(B × E, B × (E ∖ {0})) ⟶ H_{n+d}(B × (E ∖
{0}))` of the Thom pair of the product bundle, which is an isomorphism because the next term
`H_{n+d}(B × E) ≅ H_{n+d}(B)` vanishes, read on `S × B` through the homotopy equivalence
`B × (E ∖ {0}) ≃ S × B` and followed by the Thom isomorphism with `Hₙ(B)`. -/
def singularHomologySphereProdIso (hE : finrank ℝ E = d + 1) {n m : ℕ} (h : n + d = m)
    (hB : IsZero (((singularHomologyFunctor A m).obj R).obj (TopCat.of B))) :
    ((singularHomologyFunctor A m).obj R).obj (TopCat.of (sphere (0 : E) 1 × B)) ≅
      ((singularHomologyFunctor A n).obj R).obj (TopCat.of B) :=
  have := Module.finite_of_finrank_eq_succ hE
  have := Module.nontrivial_of_finrank_eq_succ hE
  have hδ := (shortExact_singularHomology_prodThomPair R B E m).isIso_f_iff.2
    (hB.of_iso ((ContinuousMap.HomotopyEquiv.prodContractible B E).singularHomologyIso R m))
  ((prodThomPairPuncturedHomotopyEquivSphere B E).singularHomologyIso R m).symm ≪≫
    (@asIso _ _ _ _ ((prodThomPair B E).singularHomologyδ R (m + 1) m) hδ).symm ≪≫
    prodThomPairSingularHomologyIso R B E n (m + 1) (by omega)

end TauCeti
