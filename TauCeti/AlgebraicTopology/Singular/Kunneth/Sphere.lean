/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.ProdThomPair
import TauCeti.Topology.Homotopy.PuncturedStarConvex

/-!
# The homology of a product with a sphere

Let `E` be a real normed space of dimension `d + 1`, so that its unit sphere `S = sphere 0 1` is a
`d`-sphere, and let `B` be any space. This file describes the singular homology of `S × B` in
terms of that of `B`, with coefficients in any object of an abelian category with coproducts:
there are short exact sequences

`0 ⟶ Hₘ₊₁(B × E, B × (E ∖ {0})) ⟶ Hₘ(B × (E ∖ {0})) ⟶ Hₘ(B × E) ⟶ 0`

(`TauCeti.shortExact_singularHomology_prodThomPair`), in which `B × (E ∖ {0})` is homotopy
equivalent to `S × B`, `B × E` to `B`, and the relative term is `H_{m-d}(B)`
(`TauCeti.prodThomPairSingularHomologyIso`). The sequence is the long exact sequence of the Thom
pair of the product bundle `B × E → B`, which breaks up because `b ↦ (b, x)` is a section of the
punctured bundle for every `x ≠ 0`.

Read on `S × B`, for a point `x` of the sphere:

* the inclusion `B → S × B`, `b ↦ (x, b)`, is an isomorphism on `Hₘ` exactly when
  `H_{m-d}(B)` vanishes (`TauCeti.isIso_singularHomologyMap_prodMk_sphere_iff`), and always for
  `m < d` (`TauCeti.isIso_singularHomologyMap_prodMk_sphere_of_lt`);
* `Hₘ(S × B)` vanishes exactly when `Hₘ(B)` and `H_{m-d}(B)` do
  (`TauCeti.isZero_singularHomology_sphere_prod_iff`), and for `m < d` exactly when `Hₘ(B)`
  does (`TauCeti.isZero_singularHomology_sphere_prod_iff_of_lt`).

The sequences split, through the section, which is the Künneth formula
`Hₘ(Sᵈ × B) ≅ Hₘ(B) ⊕ H_{m-d}(B)` for a sphere factor, with no hypothesis on the coefficients or
on `B`; the splitting itself is not packaged here. For the unit circle the same vanishing and
isomorphism criteria are `TauCeti.isZero_singularHomology_circle_prod_succ_iff` and
`TauCeti.isIso_singularHomologyMap_prodMk_const_one_succ_iff`, through the Wang sequence of a
mapping torus. These are the forms in which the homology of a space weakly equivalent to a product
with a sphere, such as the loop space of a quaternionic projective space, is computed.

## Main results

* `TauCeti.shortExact_singularHomology_prodThomPair`: the long exact sequence of the Thom pair
  of a product bundle breaks up into short exact sequences.
* `TauCeti.isIso_singularHomologyMap_prodMk_sphere_iff`: `H_{n+d}(B) → H_{n+d}(S × B)` is an
  isomorphism if and only if `Hₙ(B) = 0`.
* `TauCeti.isZero_singularHomology_sphere_prod_iff`: `H_{n+d}(S × B) = 0` if and only if
  `H_{n+d}(B) = 0` and `Hₙ(B) = 0`.

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

namespace SphereProd

/-- The section `b ↦ (b, x)` of the punctured product bundle `B × (E ∖ {0}) → B`, for
`x ≠ 0`. -/
private def punctSection (x : E) (hx : x ≠ 0) : TopCat.of B ⟶ (prodThomPair B E).snd :=
  TopCat.ofHom ⟨fun b ↦ ⟨(b, x), hx⟩, (continuous_id.prodMk continuous_const).subtype_mk _⟩

omit [NormedSpace ℝ E] in
/-- The section `b ↦ (b, x)` followed by the projections onto `B` is the identity. -/
private lemma punctSection_comp (x : E) (hx : x ≠ 0) :
    punctSection (B := B) x hx ≫ (prodThomPair B E).map ≫ prodThomPairProj B E = 𝟙 _ :=
  TopCat.ext fun b ↦ prodThomPairProj_apply E (b, x)

/-- The punctured product `B × (E ∖ {0})` is `B × (E ∖ {0})` as a product space. -/
private def puncturedHomeomorph : (prodThomPair B E).snd ≃ₜ B × ({0}ᶜ : Set E) where
  toFun p := (p.1.1, ⟨p.1.2, p.2⟩)
  invFun q := ⟨(q.1, q.2), q.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.fst).prodMk
    (continuous_subtype_val.snd.subtype_mk _)
  continuous_invFun :=
    (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)).subtype_mk _

/-- The punctured product `B × (E ∖ {0})` is homotopy equivalent to `S × B`, for `S` the unit
sphere of `E`, by `(b, y) ↦ (y / ‖y‖, b)`. -/
private def puncturedHomotopyEquiv :
    ContinuousMap.HomotopyEquiv (prodThomPair B E).snd (sphere (0 : E) 1 × B) :=
  (puncturedHomeomorph.toHomotopyEquiv.trans
    ((ContinuousMap.HomotopyEquiv.refl B).prodCongr (complSingletonHomotopyEquivSphere 0))).trans
    (Homeomorph.prodComm _ _).toHomotopyEquiv

/-- The homotopy equivalence `B × (E ∖ {0}) ≃ₕ S × B` as a morphism of `TopCat`. -/
private abbrev puncturedHom : (prodThomPair B E).snd ⟶ TopCat.of (sphere (0 : E) 1 × B) :=
  TopCat.ofHom puncturedHomotopyEquiv.toFun

/-- The section at a point `x` of the unit sphere, followed by the homotopy equivalence with
`S × B`, is the inclusion `b ↦ (x, b)`. -/
private lemma punctSection_comp_puncturedHom (x : sphere (0 : E) 1) :
    punctSection (B := B) (x : E) (ne_zero_of_mem_unit_sphere x) ≫ puncturedHom =
      TopCat.ofHom ((ContinuousMap.const B x).prodMk (ContinuousMap.id B)) := by
  ext b : 1
  refine Prod.ext (Subtype.ext ?_) rfl
  -- Radial projection fixes the points of the unit sphere.
  refine (coe_complSingletonHomotopyEquivSphere_apply 0 ⟨(x : E), _⟩).trans ?_
  simp [norm_eq_of_mem_sphere x]

variable (B E) in
/-- The projection `B × E → B` induces isomorphisms on homology, since `E` is contractible. -/
private lemma isIso_singularHomologyMap_prodThomPairProj (m : ℕ) :
    IsIso (((singularHomologyFunctor A m).obj R).map (prodThomPairProj B E)) := by
  have h : prodThomPairProj B E =
      TopCat.ofHom (ContinuousMap.HomotopyEquiv.prodContractible B E).toFun := by
    rw [ContinuousMap.HomotopyEquiv.prodContractible_toFun]
    exact TopCat.ext fun p ↦ prodThomPairProj_apply E p
  rw [h]
  exact (ContinuousMap.HomotopyEquiv.prodContractible B E).isIso_homologyMap R m

/-- The homotopy equivalence `B × (E ∖ {0}) ≃ₕ S × B` induces isomorphisms on homology. -/
private lemma isIso_singularHomologyMap_puncturedHom (m : ℕ) :
    IsIso (((singularHomologyFunctor A m).obj R).map (puncturedHom (B := B) (E := E))) :=
  puncturedHomotopyEquiv.isIso_homologyMap R m

variable (B) in
/-- The section `b ↦ (b, x)` followed by the inclusion `B × (E ∖ {0}) → B × E` induces
isomorphisms on homology. -/
private lemma isIso_singularHomologyMap_punctSection_comp_map (x : E) (hx : x ≠ 0) (m : ℕ) :
    IsIso (((singularHomologyFunctor A m).obj R).map
      (punctSection (B := B) x hx ≫ (prodThomPair B E).map)) := by
  have := isIso_singularHomologyMap_prodThomPairProj R B E m
  have h := congrArg ((singularHomologyFunctor A m).obj R).map
    (punctSection_comp (B := B) x hx)
  rw [CategoryTheory.Functor.map_id, ← Category.assoc, Functor.map_comp] at h
  have : IsIso (((singularHomologyFunctor A m).obj R).map
      (punctSection (B := B) x hx ≫ (prodThomPair B E).map) ≫
        ((singularHomologyFunctor A m).obj R).map (prodThomPairProj B E)) := by
    rw [h]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (((singularHomologyFunctor A m).obj R).map
    (prodThomPairProj B E))

variable (B) in
/-- The inclusion `B × (E ∖ {0}) → B × E` is an epimorphism on homology, split by the section
`b ↦ (b, x)` for any `x ≠ 0`. -/
private lemma epi_singularHomologyMap_map [Nontrivial E] (m : ℕ) :
    Epi (((singularHomologyFunctor A m).obj R).map (prodThomPair B E).map) := by
  obtain ⟨x, hx⟩ := exists_ne (0 : E)
  have := isIso_singularHomologyMap_punctSection_comp_map R B x hx m
  rw [Functor.map_comp] at this
  exact epi_of_epi (((singularHomologyFunctor A m).obj R).map (punctSection (B := B) x hx)) _

end SphereProd

open SphereProd

variable (B E) in
/-- **The long exact sequence of the Thom pair of a product bundle breaks up** into short exact
sequences

`0 ⟶ Hₘ₊₁(B × E, B × (E ∖ {0})) ⟶ Hₘ(B × (E ∖ {0})) ⟶ Hₘ(B × E) ⟶ 0`,

with maps the connecting morphism and the inclusion, for every nonzero real normed space `E`:
each nonzero `x : E` gives a section `b ↦ (b, x)` of the punctured product bundle, so the
inclusion is a split epimorphism on homology. -/
theorem shortExact_singularHomology_prodThomPair [Nontrivial E] (m : ℕ) :
    (ShortComplex.mk _ _ ((prodThomPair B E).singularHomologyδ_comp R (m + 1) m)).ShortExact :=
  .mk' ((prodThomPair B E).singularHomology_exact_subspace R (m + 1) m)
    -- The map from ambient to relative homology vanishes, since the inclusion is onto.
    (((prodThomPair B E).singularHomology_exact_relative R (m + 1) m).mono_g
      (((prodThomPair B E).singularHomology_exact_space R (m + 1)).epi_f_iff.1
        (epi_singularHomologyMap_map R B (m + 1))))
    (epi_singularHomologyMap_map R B m)

variable (B) in
/-- The inclusion `b ↦ (x, b)` at a point of the unit sphere is an isomorphism on `Hₘ` exactly
when the inclusion `B × (E ∖ {0}) → B × E` is. -/
private lemma isIso_singularHomologyMap_prodMk_sphere_iff_isIso (x : sphere (0 : E) 1)
    (m : ℕ) :
    IsIso (((singularHomologyFunctor A m).obj R).map
        (TopCat.ofHom ((ContinuousMap.const B x).prodMk (ContinuousMap.id B)))) ↔
      IsIso (((singularHomologyFunctor A m).obj R).map (prodThomPair B E).map) := by
  have := isIso_singularHomologyMap_puncturedHom R (B := B) (E := E) m
  have hs := isIso_singularHomologyMap_punctSection_comp_map R B (x : E)
    (ne_zero_of_mem_unit_sphere x) m
  rw [Functor.map_comp] at hs
  rw [← punctSection_comp_puncturedHom x, Functor.map_comp, isIso_comp_right_iff]
  exact ⟨fun _ ↦ IsIso.of_isIso_comp_left (((singularHomologyFunctor A m).obj R).map
      (punctSection (B := B) (x : E) (ne_zero_of_mem_unit_sphere x))) _,
    fun h ↦ IsIso.of_isIso_comp_right _ (((singularHomologyFunctor A m).obj R).map
      (prodThomPair B E).map)⟩

variable {R} (B) in
/-- `Hₘ(S × B)` vanishes exactly when `Hₘ(B)` and `Hₘ₊₁(B × E, B × (E ∖ {0}))` do. -/
private lemma isZero_singularHomology_sphere_prod_iff_isZero [Nontrivial E] (m : ℕ) :
    IsZero (((singularHomologyFunctor A m).obj R).obj (TopCat.of (sphere (0 : E) 1 × B))) ↔
      IsZero (((singularHomologyFunctor A m).obj R).obj (TopCat.of B)) ∧
        IsZero ((prodThomPair B E).singularHomology R (m + 1)) := by
  have hS := shortExact_singularHomology_prodThomPair R B E m
  rw [← ((puncturedHomotopyEquiv (B := B) (E := E)).singularHomologyIso R m).isZero_iff,
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

end TauCeti
