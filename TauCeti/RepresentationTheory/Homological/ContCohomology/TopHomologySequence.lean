/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.ConcreteCategory
public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import TauCeti.Algebra.Category.ModuleCat.Topology.Homology
public import TauCeti.RepresentationTheory.Homological.ContCohomology.ExactCochains.Basic

/-!
# The long exact sequence of continuous cohomology for topological coefficients

Let `G` be a locally compact group (for instance a profinite group) and let
`0 → X₁ → X₂ → X₃ → 0` be a topologically short exact sequence of topological representations
(`CategoryTheory.ShortComplex.TopShortExact`): `X₁ → X₂` is a topological embedding, the sequence
is exact at `X₂`, `X₂ → X₃` has a continuous set-theoretic section, and `G` acts jointly
continuously on `X₂`. Then there is a long exact sequence

```text
⋯ → Hⁿ(G, X₁) → Hⁿ(G, X₂) → Hⁿ(G, X₃) --δ--> Hⁿ⁺¹(G, X₁) → Hⁿ⁺¹(G, X₂) → ⋯
```

of Mathlib's canonical continuous cohomology `continuousCohomology n`, natural in the short exact
sequence. This applies to compact coefficients, for which the section exists whenever the
modules are profinite as additive groups
(`AddMonoidHom.exists_continuous_section_of_surjective`), and to sequences such as
`0 → T → V → V/T → 0` for a lattice `T` in a `ℚ_p`-vector space, where the quotient is discrete.
For discrete coefficients it is the long exact sequence of
`TauCeti.RepresentationTheory.Homological.ContCohomology.HomologySequence`.

The connecting map `δ` is the snake-lemma connecting map of the short exact sequence of
homogeneous continuous cochains (`TopShortExact.cochains_shortExact_moduleCat`), after
forgetting topologies; `CategoryTheory.ShortComplex.mapHomologyIso` identifies the homology of the
forgotten complexes with the underlying modules of continuous cohomology. For non-discrete
coefficients the cohomology modules carry non-discrete topologies, and `δ` is stated as a linear
map, a morphism of `ModuleCat R`, between their underlying modules.

## Main definitions

* `CategoryTheory.ShortComplex.TopShortExact.delta`: the connecting map
  `Hⁿ(G, X₃) ⟶ Hⁿ⁺¹(G, X₁)` of underlying modules.

## Main results

* `CategoryTheory.ShortComplex.TopShortExact.delta_apply`: `δ` on representatives: lift a cocycle
  on `X₃` to a cochain on `X₂`, differentiate, and read the result as a cocycle on `X₁`; such
  representatives exist by `CategoryTheory.ShortComplex.TopShortExact.exists_delta_witness`.
* `CategoryTheory.ShortComplex.TopShortExact.longExact_exact₁`, `longExact_exact₂` and
  `longExact_exact₃`: exactness at `Hⁿ⁺¹(G, X₁)`, `Hⁿ(G, X₂)` and `Hⁿ(G, X₃)`.
* `CategoryTheory.ShortComplex.TopShortExact.delta_naturality`: a morphism of topologically short
  exact sequences commutes with `δ`.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Springer (2008),
  Chapter II, §7, Lemma 2.7.2.
* K. Rubin, *Euler Systems*, Annals of Mathematics Studies 147, Princeton University Press (2000),
  Appendix B, §2, Definition 2.1.
-/

public section

open CategoryTheory

namespace CategoryTheory.ShortComplex.TopShortExact

open _root_.ContinuousCohomology TauCeti.ContinuousCohomology

universe u v

variable {R : Type u} [Ring R] [TopologicalSpace R]
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  {S : ShortComplex (TopRep.{v} R G)} (hS : S.TopShortExact)

/-- **The connecting map of continuous cohomology** `δ : Hⁿ(G, X₃) ⟶ Hⁿ⁺¹(G, X₁)` attached to a
topologically short exact sequence `0 → X₁ → X₂ → X₃ → 0`, in every degree `n`, as a linear map
of the underlying modules. It is the snake-lemma connecting map of the short exact sequence of
homogeneous continuous cochains (`delta_def`), and is computed on representatives by
`delta_apply`. -/
noncomputable def delta (n : ℕ) :
    (forget₂ (TopModuleCat R) (ModuleCat R)).obj (continuousCohomology n S.X₃) ⟶
      (forget₂ (TopModuleCat R) (ModuleCat R)).obj (continuousCohomology (n + 1) S.X₁) :=
  ((S.X₃.homogeneousCochains.sc n).mapHomologyIso (forget₂ (TopModuleCat R) (ModuleCat R))).inv ≫
    hS.cochains_shortExact_moduleCat.δ n (n + 1) rfl ≫
      ((S.X₁.homogeneousCochains.sc (n + 1)).mapHomologyIso
        (forget₂ (TopModuleCat R) (ModuleCat R))).hom

/-- `δ` is the connecting map of the snake lemma for the forgotten short exact sequence of
homogeneous-cochain complexes, conjugated by the identifications
`CategoryTheory.ShortComplex.mapHomologyIso` of the homology of the forgotten complexes with the
underlying modules of continuous cohomology. -/
theorem delta_def (n : ℕ) :
    hS.delta n =
      ((S.X₃.homogeneousCochains.sc n).mapHomologyIso
          (forget₂ (TopModuleCat R) (ModuleCat R))).inv ≫
        hS.cochains_shortExact_moduleCat.δ n (n + 1) rfl ≫
          ((S.X₁.homogeneousCochains.sc (n + 1)).mapHomologyIso
            (forget₂ (TopModuleCat R) (ModuleCat R))).hom :=
  (rfl)

/-- **The connecting map on representatives.** Let `z₃` be a homogeneous `n`-cocycle with values in
`X₃`, `x₂` a homogeneous `n`-cochain with values in `X₂` lifting it, and `z₁` a homogeneous
`(n + 1)`-cocycle with values in `X₁` whose image in `X₂` is the differential of `x₂`. Then `δ`
sends the class of `z₃` to the class of `z₁`. This is the continuous counterpart of Mathlib's
`CategoryTheory.ShortComplex.ShortExact.δ_apply`. -/
theorem delta_apply (n : ℕ) (z₃ : cocycles S.X₃ n)
    (x₂ : S.X₂.homogeneousCochains.X n)
    (hx₂ : ((cochainsMap (ContinuousMonoidHom.id G) S.g).f n).hom x₂ =
      S.X₃.homogeneousCochains.iCycles n z₃)
    (z₁ : cocycles S.X₁ (n + 1))
    (hx₁ : ((cochainsMap (ContinuousMonoidHom.id G) S.f).f (n + 1)).hom
        (S.X₁.homogeneousCochains.iCycles (n + 1) z₁) =
      (S.X₂.homogeneousCochains.d n (n + 1)).hom x₂) :
    hS.delta n (π S.X₃ n z₃) = π S.X₁ (n + 1) z₁ := by
  let F := forget₂ (TopModuleCat.{v} R) (ModuleCat.{v} R)
  let hS' := hS.cochains_shortExact_moduleCat
  -- The snake lemma in `ModuleCat R`, on the cycles built from `z₃` and `z₁`, which are the images
  -- of `z₃` and `z₁` under `mapCyclesIso`.
  let S' := (S.map (continuousCochainsFunctor R G)).map (F.mapHomologicalComplex (.up ℕ))
  have hx₃ : (forget₂ (ModuleCat R) AddCommGrpCat).map (S'.X₃.d n (n + 1))
      (S.X₃.homogeneousCochains.iCycles n z₃) = 0 :=
    ConcreteCategory.congr_hom (S.X₃.homogeneousCochains.iCycles_d n (n + 1)) z₃
  have hδ := hS'.δ_apply n (n + 1) rfl _ hx₃ x₂ hx₂ _ hx₁ (n + 2) (by simp)
  have hc₃ : S'.X₃.cyclesMk (S.X₃.homogeneousCochains.iCycles n z₃) (n + 1) (by simp) hx₃ =
      ((S.X₃.homogeneousCochains.sc n).mapCyclesIso F).inv z₃ :=
    HomologicalComplex.forget₂_cyclesMk_iCycles _ _ _ _ _
  have hc₁ : S'.X₁.cyclesMk (S.X₁.homogeneousCochains.iCycles (n + 1) z₁) (n + 2) (by simp)
      (hS'.d_eq_zero_of_f_eq_d_apply n (n + 1) _ _ hx₁ _) =
      ((S.X₁.homogeneousCochains.sc (n + 1)).mapCyclesIso F).inv z₁ :=
    HomologicalComplex.forget₂_cyclesMk_iCycles _ _ _ _ _
  rw [hc₃, hc₁] at hδ
  -- Transport through `mapHomologyIso` on both sides: it carries the class of the image of a cycle
  -- under `mapCyclesIso` to the class of the cycle (`forget₂_mapHomologyIso_hom_homologyπ`).
  refine (congrArg (fun f ↦ f.hom (π S.X₃ n z₃)) (hS.delta_def n)).trans ?_
  refine (congrArg (fun y ↦ ((S.X₁.homogeneousCochains.sc (n + 1)).mapHomologyIso F).hom
    (hS'.δ n (n + 1) rfl y)) ?_).trans ((congrArg _ hδ).trans
      ((S.X₁.homogeneousCochains.sc (n + 1)).forget₂_mapHomologyIso_hom_homologyπ z₁))
  exact (congrArg _ ((S.X₃.homogeneousCochains.sc n).forget₂_mapHomologyIso_hom_homologyπ
    z₃).symm).trans (Iso.hom_inv_id_apply ((S.X₃.homogeneousCochains.sc n).mapHomologyIso F) _)

include hS in
/-- The data from which `CategoryTheory.ShortComplex.TopShortExact.delta_apply` computes the
connecting map exists: a lift `x₂` of the cocycle `z` to `X₂`, and a cocycle `z₁` on `X₁` whose
image is `d x₂`. -/
theorem exists_delta_witness (n : ℕ) (z : cocycles S.X₃ n) :
    ∃ (x₂ : S.X₂.homogeneousCochains.X n) (z₁ : cocycles S.X₁ (n + 1)),
      ((cochainsMap (ContinuousMonoidHom.id G) S.g).f n).hom x₂ =
          S.X₃.homogeneousCochains.iCycles n z ∧
        ((cochainsMap (ContinuousMonoidHom.id G) S.f).f (n + 1)).hom
            (S.X₁.homogeneousCochains.iCycles (n + 1) z₁) =
          (S.X₂.homogeneousCochains.d n (n + 1)).hom x₂ := by
  let f := cochainsMap (ContinuousMonoidHom.id G) S.f
  let g := cochainsMap (ContinuousMonoidHom.id G) S.g
  obtain ⟨x₂, hx₂⟩ := hS.cochainsMap_g_f_surjective n (S.X₃.homogeneousCochains.iCycles n z)
  -- `d x₂` maps to `d z = 0` in `X₃`, so it comes from a cochain `w` on `X₁`.
  have hg : (g.f (n + 1)).hom ((S.X₂.homogeneousCochains.d n (n + 1)).hom x₂) = 0 := by
    rw [← ConcreteCategory.comp_apply, ← g.comm, ConcreteCategory.comp_apply, hx₂]
    exact ConcreteCategory.congr_hom (S.X₃.homogeneousCochains.iCycles_d n (n + 1)) z
  obtain ⟨w, hw⟩ := (cochainsMap_id_f_exact hS.isEmbedding_f hS.exact (n + 1) _).1 hg
  -- `w` is a cocycle: its differential maps to `d (d x₂) = 0`, and `f` is injective.
  have hdw : (S.X₁.homogeneousCochains.d (n + 1) (n + 1 + 1)).hom w = 0 := by
    have h₁ := ConcreteCategory.congr_hom (f.comm (n + 1) (n + 1 + 1)) w
    have h₂ := ConcreteCategory.congr_hom
      (S.X₂.homogeneousCochains.d_comp_d n (n + 1) (n + 1 + 1)) x₂
    simp only [ConcreteCategory.comp_apply] at h₁ h₂
    rw [hw] at h₁
    apply cochainsMap_f_injective (ContinuousMonoidHom.id G) S.f Function.surjective_id
      hS.injective_f (n + 1 + 1)
    exact h₁.symm.trans (h₂.trans (_root_.map_zero _).symm)
  refine ⟨x₂, S.X₁.homogeneousCochains.cyclesMkOfEq w (n + 1 + 1) (CochainComplex.next ℕ (n + 1))
    hdw, hx₂, ?_⟩
  exact (congrArg (f.f (n + 1)).hom (HomologicalComplex.iCycles_cyclesMkOfEq _ _ _ _ _)).trans hw

/-- **Exactness at `Hⁿ⁺¹(G, X₁)`**: the image of the connecting map `Hⁿ(G, X₃) ⟶ Hⁿ⁺¹(G, X₁)` is
the kernel of the coefficient map induced by `X₁ → X₂`. -/
theorem longExact_exact₁ (n : ℕ) :
    Function.Exact (hS.delta n)
      ((forget₂ (TopModuleCat R) (ModuleCat R)).map (coeffMap S.f (n + 1))) := by
  -- Transport the snake-lemma exactness along the three `mapHomologyIso`s. Both maps are
  -- conjugates `e.inv ≫ φ ≫ e'.hom` (`delta_def`, `forget₂_map_coeffMap`), so each ladder square
  -- `e.hom ≫ (e.inv ≫ φ ≫ e'.hom) = φ ≫ e'.hom` is read off by `Iso.inv_comp_eq`.
  exact ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
    (hS.cochains_shortExact_moduleCat.homology_exact₁ n (n + 1) rfl)).of_ladder_linearEquiv_of_exact
    (e₁ := ((S.X₃.homogeneousCochains.sc n).mapHomologyIso _).toLinearEquiv)
    (e₂ := ((S.X₁.homogeneousCochains.sc (n + 1)).mapHomologyIso _).toLinearEquiv)
    (e₃ := ((S.X₂.homogeneousCochains.sc (n + 1)).mapHomologyIso _).toLinearEquiv)
    (congrArg ModuleCat.Hom.hom ((Iso.inv_comp_eq _).1 (hS.delta_def n).symm).symm)
    (congrArg ModuleCat.Hom.hom
      ((Iso.inv_comp_eq _).1 (forget₂_map_coeffMap S.f (n + 1)).symm).symm)

include hS in
/-- **Exactness at `Hⁿ(G, X₂)`**: the image of the coefficient map induced by `X₁ → X₂` is the
kernel of the coefficient map induced by `X₂ → X₃`. -/
theorem longExact_exact₂ (n : ℕ) : Function.Exact (coeffMap S.f n) (coeffMap S.g n) :=
  TopModuleCat.exact_of_forget₂_map_eq (forget₂_map_coeffMap _ _) (forget₂_map_coeffMap _ _)
    ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
      (hS.cochains_shortExact_moduleCat.homology_exact₂ n))

/-- **Exactness at `Hⁿ(G, X₃)`**: the image of the coefficient map induced by `X₂ → X₃` is the
kernel of the connecting map `Hⁿ(G, X₃) ⟶ Hⁿ⁺¹(G, X₁)`. -/
theorem longExact_exact₃ (n : ℕ) :
    Function.Exact ((forget₂ (TopModuleCat R) (ModuleCat R)).map (coeffMap S.g n))
      (hS.delta n) := by
  -- Transport the snake-lemma exactness along the three `mapHomologyIso`s, as in
  -- `longExact_exact₁`.
  exact ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
    (hS.cochains_shortExact_moduleCat.homology_exact₃ n (n + 1) rfl)).of_ladder_linearEquiv_of_exact
    (e₁ := ((S.X₂.homogeneousCochains.sc n).mapHomologyIso _).toLinearEquiv)
    (e₂ := ((S.X₃.homogeneousCochains.sc n).mapHomologyIso _).toLinearEquiv)
    (e₃ := ((S.X₁.homogeneousCochains.sc (n + 1)).mapHomologyIso _).toLinearEquiv)
    (congrArg ModuleCat.Hom.hom ((Iso.inv_comp_eq _).1 (forget₂_map_coeffMap S.g n).symm).symm)
    (congrArg ModuleCat.Hom.hom ((Iso.inv_comp_eq _).1 (hS.delta_def n).symm).symm)

/-- The connecting map kills the image of `Hⁿ(G, X₂) → Hⁿ(G, X₃)`. -/
@[reassoc (attr := simp)]
theorem coeffMap_g_comp_delta (n : ℕ) :
    (forget₂ (TopModuleCat R) (ModuleCat R)).map (coeffMap S.g n) ≫ hS.delta n = 0 :=
  ModuleCat.hom_ext <| LinearMap.ext fun x ↦ (hS.longExact_exact₃ n).apply_apply_eq_zero x

/-- The coefficient map `Hⁿ⁺¹(G, X₁) → Hⁿ⁺¹(G, X₂)` kills the image of the connecting map. -/
@[reassoc (attr := simp)]
theorem delta_comp_coeffMap_f (n : ℕ) :
    hS.delta n ≫ (forget₂ (TopModuleCat R) (ModuleCat R)).map (coeffMap S.f (n + 1)) = 0 :=
  ModuleCat.hom_ext <| LinearMap.ext fun x ↦ (hS.longExact_exact₁ n).apply_apply_eq_zero x

/-- **Naturality of the connecting map.** A morphism `φ` from one topologically short exact
sequence to another carries the connecting map of the first to that of the second:

```text
Hⁿ(G, X₃) ---δ---> Hⁿ⁺¹(G, X₁)
    |                   |
   φ.τ₃                φ.τ₁
    v                   v
Hⁿ(G, X₃') --δ--> Hⁿ⁺¹(G, X₁')
```
-/
@[reassoc]
theorem delta_naturality {S' : ShortComplex (TopRep.{v} R G)} (hS' : S'.TopShortExact)
    (φ : S ⟶ S') (n : ℕ) :
    hS.delta n ≫ (forget₂ (TopModuleCat R) (ModuleCat R)).map (coeffMap φ.τ₁ (n + 1)) =
      (forget₂ (TopModuleCat R) (ModuleCat R)).map (coeffMap φ.τ₃ n) ≫ hS'.delta n := by
  -- The morphism of short exact sequences of homogeneous-cochain complexes induced by `φ`, and
  -- its image on the forgotten complexes.
  let Φ := ((forget₂ (TopModuleCat R) (ModuleCat R)).mapHomologicalComplex _).mapShortComplex.map
    ((continuousCochainsFunctor R G).mapShortComplex.map φ)
  -- Three commuting squares in `ModuleCat R`: the snake-lemma naturality in the middle, and the
  -- coefficient maps read through `mapHomologyIso` on either side (`forget₂_map_coeffMap`).
  have h := HomologicalComplex.HomologySequence.δ_naturality Φ
    hS.cochains_shortExact_moduleCat hS'.cochains_shortExact_moduleCat n (n + 1) rfl
  have h₁ := (Iso.eq_inv_comp _).1 (forget₂_map_coeffMap φ.τ₁ (n + 1))
  have h₃ := (Iso.eq_comp_inv _).2 ((Category.assoc _ _ _).trans
    (forget₂_map_coeffMap φ.τ₃ n).symm)
  rw [delta_def, delta_def]
  -- Paste the three squares. `Category.assoc` cannot be rewritten here because the objects of the
  -- two sides agree only after unfolding `continuousCohomology`.
  exact ((CommSq.mk h₃).horiz_comp ((CommSq.mk h).horiz_comp (CommSq.mk h₁))).w

end CategoryTheory.ShortComplex.TopShortExact
