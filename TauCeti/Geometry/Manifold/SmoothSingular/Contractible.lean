/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.AlgebraicTopology.SingularHomology.Basic
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Geometry.Manifold.Algebra.LieGroup
public import Mathlib.Geometry.Manifold.Algebra.SMul
public import TauCeti.AlgebraicTopology.Singular.Empty
public import TauCeti.Geometry.Manifold.ContMDiff.Subtype
public import TauCeti.Geometry.Manifold.SmoothSingular.Homotopy

import TauCeti.Geometry.Manifold.ContMDiff.Contraction

/-!
# Smooth and singular chains of smoothly contractible manifolds

Let `M` be a manifold whose identity is joined to a constant map `x ↦ c` by a smooth map
`F : ℝ × M → M`, with `F (0, x) = x` and `F (1, x) = c`. This file proves that on such a smoothly
contractible manifold the inclusion of smooth singular chains into singular chains, with
coefficients in any object `R` of a preadditive category with coproducts, is a chain homotopy
equivalence (`TauCeti.smoothSingularChainHomotopyEquivOfContraction`). In particular it is a
quasi-isomorphism (`TauCeti.quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_of_contraction`).

A constant singular simplex is smooth, so the map of singular simplicial sets induced by the
constant map `x ↦ c` factors through the smooth singular subcomplex
(`TauCeti.smoothSingularSubcomplexConst`). The induced map of chain complexes is the homotopy
inverse. Composed with the inclusion on either side it is the map induced by the constant map, on
smooth chains (`TauCeti.ι_comp_smoothSingularSubcomplexConst`) and on singular chains
(`TauCeti.smoothSingularSubcomplexConst_comp_ι`). The smooth prism operator of `F`
(`TauCeti.smoothSingularChainHomotopy`) and the singular prism operator of its restriction to
`[0, 1] × M` (`TauCeti.homotopyOfRealProd` and Mathlib's `TopCat.Homotopy.toSSet`) join these maps
to the identities. Degree zero needs no separate argument: the inverse sends every point to `c`,
and the smooth paths `t ↦ F (t, x)` make every point homologous to `c` in smooth chains. Homotopy
invariance alone already shows that the smooth singular homology of such a manifold vanishes in
positive degrees (`TauCeti.isZero_homology_smoothSingularSubcomplex_of_contMDiff`).

The same holds for the empty manifold, where both complexes vanish
(`TauCeti.quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_of_isEmpty`). For an open set `U` of
the model space `H` of a model with corners `I : ModelWithCorners ℝ E H` whose image `I '' U` is
star-convex about `c`, the map `(t, x) ↦ I.symm (c + (1 - ψ t) • (I x - c))`, with `ψ` the smooth
transition function from `0` to `1`, is such a smooth contraction
(`TauCeti.exists_contMDiff_contraction_of_starConvex`), so the inclusion is a quasi-isomorphism
(`TauCeti.quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_of_starConvex`), and the smooth
singular homology of `U` vanishes in positive degrees
(`TauCeti.isZero_homology_smoothSingularSubcomplex_of_starConvex`). The model may have boundary
and corners: the contraction stays in `range I` because `I '' U` does. A star-convex open subset of
a normed space `V` is the case `I = 𝓘(ℝ, V)`.

These are the base cases of the Mayer–Vietoris induction (`TauCeti.mayerVietoris_induction`) that
compares smooth with continuous singular homology on manifolds with corners: the empty open set,
and the open sets of the model space with convex image, which form a basis closed under
intersection. The step for countable disjoint unions is
`TauCeti.quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_iSup`.

Also recorded here are the `0`-simplex inverse computations and homology-isomorphism corollaries
(`TauCeti.smoothSingularChainHomotopyEquivOfContractible` for the reversed-time endpoint convention
`Φ (0, ·) = c`, `Φ (1, ·) = id`), together with the unconditional smooth-chain homotopy
equivalences for any real model space with corners
(`ModelWithCorners.smoothSingularChainHomotopyEquivModelSpace`) and for any star-convex open subset
of a real normed space (`StarConvex.smoothSingularChainHomotopyEquivOfStarConvex`).

## Main definitions and results

* `TauCeti.smoothSingularChainHomotopyEquivOfContraction`,
  `TauCeti.smoothSingularChainHomotopyEquivOfContractible`: on a smoothly contractible manifold,
  the inclusion of smooth singular chains into singular chains is a chain homotopy equivalence.
* `TauCeti.quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_of_contraction`,
  `TauCeti.isIso_homologyMap_smoothSingularSubcomplex_ι_of_contractible`,
  `TauCeti.quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_of_isEmpty`,
  `TauCeti.quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_of_starConvex`: the inclusion is a
  quasi-isomorphism on a smoothly contractible manifold, on the empty manifold, and on an open set
  of the model space with star-convex image.
* `ModelWithCorners.smoothSingularChainHomotopyEquivModelSpace`,
  `StarConvex.smoothSingularChainHomotopyEquivOfStarConvex`: unconditional smooth-chain homotopy
  equivalences on real model spaces with corners and star-convex open subsets of normed spaces.
* `TauCeti.exists_contMDiff_contraction_of_starConvex`: an open set of the model space with
  star-convex image is smoothly contractible.
* `TauCeti.isZero_homology_smoothSingularSubcomplex_of_contMDiff`: a smoothly contractible manifold
  has no smooth singular homology in positive degrees.
* `TauCeti.isZero_homology_smoothSingularSubcomplex_of_starConvex`: neither has an open set of
  the model space with star-convex image.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Chapter 18, proof of Theorem 18.7 (the
  smooth singular homology of a convex set).
-/

public section

noncomputable section

open CategoryTheory Limits Set Convexity Simplicial
open scoped Manifold ContDiff

universe u

namespace TauCeti

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type u} [TopologicalSpace M] [ChartedSpace H M]

/-! ### The empty manifold -/

variable {C : Type*} [Category C] [Preadditive C] [HasCoproducts.{u} C] (R : C)

/-- On the empty manifold, the inclusion of smooth singular chains into singular chains is a
quasi-isomorphism: both complexes vanish. -/
theorem quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_of_isEmpty [CategoryWithHomology C]
    [IsEmpty M] : QuasiIso (SSet.chainComplexMap (smoothSingularSubcomplex I M).ι R) := by
  have := (SSet.isZero_chainComplex (smoothSingularSubcomplex I M : SSet) R).isIso
    (SSet.isZero_chainComplex _ R) (SSet.chainComplexMap (smoothSingularSubcomplex I M).ι R)
  infer_instance

/-! ### Open sets with star-convex image in the model -/

/-- **The straight-line contraction of an open set with star-convex image in the model.** Let `U`
be an open set of the model space `H` of a model with corners `I` whose image `I '' U` is
star-convex about `c`. Then `(t, x) ↦ I.symm (c + (1 - ψ t) • (I x - c))`, with `ψ` the smooth
transition function from `0` to `1`, is a smooth map `ℝ × U → U` joining the identity to the
constant map with value `I.symm c`. This is the case `M = H` of
`exists_contMDiff_contraction_of_starConvex_image_extChartAt`, where the extended chart is `I`. -/
theorem exists_contMDiff_contraction_of_starConvex {U : TopologicalSpace.Opens H} {c : E}
    (hU : StarConvex ℝ c (I '' U)) :
    ∃ F : ℝ × U → U, ContMDiff (𝓘(ℝ).prod I) I ∞ F ∧ (∀ x, F (0, x) = x) ∧
      ∀ x, (F (1, x) : H) = I.symm c := by
  rcases (U : Set H).eq_empty_or_nonempty with hempty | hne
  · have : IsEmpty U := ⟨fun x ↦ eq_empty_iff_forall_notMem.1 hempty x x.property⟩
    exact ⟨fun p ↦ isEmptyElim p.2, fun p ↦ isEmptyElim p.2, isEmptyElim, isEmptyElim⟩
  obtain ⟨y₀, hy₀, rfl⟩ := hU.mem (hne.image I)
  obtain ⟨F, hF, h₀, h₁⟩ := exists_contMDiff_contraction_of_starConvex_image_extChartAt
    (I := I) (M := H) (n := ⊤) (x := y₀) (by simp) ⟨y₀, hy₀⟩
    (by simpa [extChartAt_self_eq] using hU)
  exact ⟨F, hF, h₀, fun x ↦ by rw [h₁, I.left_inv]⟩

/-! ### Smoothly contractible manifolds -/

/-- **The smoothing theorem for a smoothly contractible manifold.** If a smooth map
`F : ℝ × M → M` joins the identity `F (0, ·) = id` to a constant map `F (1, ·) = c`, then the
inclusion of smooth singular chains into singular chains with coefficients in `R` is a chain
homotopy equivalence. Its homotopy inverse is induced by the constant map `x ↦ c`. -/
def smoothSingularChainHomotopyEquivOfContraction {F : ℝ × M → M}
    (hF : ContMDiff (𝓘(ℝ).prod I) I ∞ F) (c : M) (h₀ : ∀ x, F (0, x) = x)
    (h₁ : ∀ x, F (1, x) = c) :
    HomotopyEquiv ((smoothSingularSubcomplex I M : SSet).chainComplex R)
      ((TopCat.toSSet.obj (TopCat.of M)).chainComplex R) where
  hom := SSet.chainComplexMap (smoothSingularSubcomplex I M).ι R
  inv := SSet.chainComplexMap (smoothSingularSubcomplexConst I (TopCat.of M) c) R
  homotopyHomInvId :=
    -- Both composites are the maps induced by the constant map, which the prism operators of the
    -- contraction join to the maps induced by the identity.
    (Homotopy.ofEq (by rw [← Functor.map_comp, ι_comp_smoothSingularSubcomplexConst])).trans <|
      (smoothSingularChainHomotopy contMDiff_id contMDiff_const
          (homotopyOfRealProd (f := ContinuousMap.id M) (g := ⟨fun _ ↦ c, continuous_const⟩)
            hF.continuous h₀ h₁) hF
          (fun p ↦ (homotopyOfRealProd_apply hF.continuous h₀ h₁ p).symm) R).symm.trans <|
        Homotopy.ofEq (by
          rw [smoothSingularSubcomplexMap_id]
          exact ((SSet.chainComplexFunctor C).obj R).map_id _)
  homotopyInvHomId :=
    (Homotopy.ofEq (by rw [← Functor.map_comp, smoothSingularSubcomplexConst_comp_ι])).trans <|
      ((TopCat.Homotopy.toSSet (f := TopCat.ofHom (ContinuousMap.id M))
          (g := TopCat.ofHom ⟨fun _ ↦ c, continuous_const⟩)
          (homotopyOfRealProd hF.continuous h₀ h₁)).chainComplexMap R).symm.trans <|
        Homotopy.ofEq (by
          rw [TopCat.ofHom_id, CategoryTheory.Functor.map_id]
          exact ((SSet.chainComplexFunctor C).obj R).map_id _)

/-- The forward map of the equivalence is the inclusion of smooth singular chains. -/
@[simp]
theorem smoothSingularChainHomotopyEquivOfContraction_hom {F : ℝ × M → M}
    (hF : ContMDiff (𝓘(ℝ).prod I) I ∞ F) (c : M) (h₀ : ∀ x, F (0, x) = x)
    (h₁ : ∀ x, F (1, x) = c) :
    (smoothSingularChainHomotopyEquivOfContraction R hF c h₀ h₁).hom =
      SSet.chainComplexMap (smoothSingularSubcomplex I M).ι R :=
  (rfl)

/-- The homotopy inverse of the equivalence is induced by the constant map `x ↦ c`. -/
@[simp]
theorem smoothSingularChainHomotopyEquivOfContraction_inv {F : ℝ × M → M}
    (hF : ContMDiff (𝓘(ℝ).prod I) I ∞ F) (c : M) (h₀ : ∀ x, F (0, x) = x)
    (h₁ : ∀ x, F (1, x) = c) :
    (smoothSingularChainHomotopyEquivOfContraction R hF c h₀ h₁).inv =
      SSet.chainComplexMap (smoothSingularSubcomplexConst I (TopCat.of M) c) R :=
  (rfl)

/-- On a smoothly contractible manifold with contraction centre `c`, the homotopy inverse sends the
summand of every singular `0`-simplex to the summand of the smooth `0`-simplex at `c`. -/
@[reassoc]
theorem ι_smoothSingularChainHomotopyEquivOfContraction_inv_f_zero {F : ℝ × M → M}
    (hF : ContMDiff (𝓘(ℝ).prod I) I ∞ F) (c : M) (h₀ : ∀ x, F (0, x) = x)
    (h₁ : ∀ x, F (1, x) = c) (σ : (TopCat.toSSet.obj (TopCat.of M)) _⦋0⦌) :
    (TopCat.toSSet.obj (TopCat.of M)).ιChainComplex σ ≫
        (smoothSingularChainHomotopyEquivOfContraction R hF c h₀ h₁).inv.f 0 =
      (smoothSingularSubcomplex I M : SSet).ιChainComplex ((SmoothSimplex.equiv₀ I M).symm c) := by
  rw [smoothSingularChainHomotopyEquivOfContraction_inv, SSet.ι_chainComplexMap_f]
  congr 1
  exact SmoothSimplex.ext fun x ↦ by
    rw [SmoothSimplex.toContinuousMap_apply, coe_smoothSingularSubcomplexConst_app,
      TopCat.toSSetObjEquiv_toSSet_map_app]
    simp

/-- On a smoothly contractible manifold, the inclusion of smooth singular chains into singular
chains is a quasi-isomorphism. -/
theorem quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_of_contraction [CategoryWithHomology C]
    {F : ℝ × M → M} (hF : ContMDiff (𝓘(ℝ).prod I) I ∞ F) (c : M) (h₀ : ∀ x, F (0, x) = x)
    (h₁ : ∀ x, F (1, x) = c) :
    QuasiIso (SSet.chainComplexMap (smoothSingularSubcomplex I M).ι R) :=
  (smoothSingularChainHomotopyEquivOfContraction R hF c h₀ h₁).quasiIso_hom

/-- **A smoothly contractible manifold has the smooth singular homology of a point.** If a smooth
map `F : ℝ × M → M` joins the identity `F (0, ·) = id` to a constant map `F (1, ·) = c`, then the
smooth singular homology of `M` vanishes in every positive degree. -/
theorem isZero_homology_smoothSingularSubcomplex_of_contMDiff [CategoryWithHomology C]
    {F : ℝ × M → M} (hF : ContMDiff (𝓘(ℝ).prod I) I ∞ F) (c : M) (h₀ : ∀ x, F (0, x) = x)
    (h₁ : ∀ x, F (1, x) = c) {n : ℕ} (hn : n ≠ 0) :
    IsZero ((smoothSingularSubcomplex I M : SSet).homology R n) := by
  let pt : TopCat.{u} := TopCat.of PUnit
  -- The constant map factors through the singular simplicial set of a point.
  let a : TopCat.of M ⟶ pt := TopCat.ofHom (ContinuousMap.const M PUnit.unit)
  have hab : a ≫ TopCat.ofHom ⟨fun _ ↦ c, continuous_const⟩ =
      TopCat.ofHom ⟨fun _ ↦ c, continuous_const⟩ := by
    ext
    rfl
  let p : (smoothSingularSubcomplex I M : SSet) ⟶ TopCat.toSSet.obj pt :=
    (smoothSingularSubcomplex I M).ι ≫ TopCat.toSSet.map a
  let s := smoothSingularSubcomplexConst I pt c
  have hps : smoothSingularSubcomplexMap (fun _ ↦ c) (contMDiff_const : ContMDiff I I ∞ _) =
      p ≫ s := by
    rw [← cancel_mono (smoothSingularSubcomplex I M).ι, smoothSingularSubcomplexMap_ι,
      Category.assoc, smoothSingularSubcomplexConst_comp_ι, Category.assoc, ← Functor.map_comp,
      hab]
  have hpt : IsZero ((TopCat.toSSet.obj pt).homology R n) :=
    AlgebraicTopology.isZero_singularHomologyFunctor_of_totallyDisconnectedSpace C n R pt hn
  have hid : SSet.homologyMap (smoothSingularSubcomplexMap id (contMDiff_id (I := I))) R n =
      SSet.homologyMap (p ≫ s) R n := by
    rw [← hps]
    exact homologyMap_smoothSingularSubcomplexMap_eq_of_contMDiff R contMDiff_id contMDiff_const hF
      h₀ h₁ n
  rw [smoothSingularSubcomplexMap_id, SSet.homologyMap_id, SSet.homologyMap_comp] at hid
  rw [IsZero.iff_id_eq_zero, hid, hpt.eq_of_src (SSet.homologyMap s R n) 0, comp_zero]

/-- **The smoothing theorem for an open set with star-convex image in the model.** Let `U` be an
open set of the model space `H` of a model with corners `I` whose image `I '' U` is star-convex.
Then the inclusion of smooth singular chains of `U` into singular chains is a quasi-isomorphism. -/
theorem quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_of_starConvex [CategoryWithHomology C]
    {H : Type u} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {U : TopologicalSpace.Opens H} {c : E} (hU : StarConvex ℝ c (I '' U)) :
    QuasiIso (SSet.chainComplexMap (smoothSingularSubcomplex I U).ι R) := by
  rcases (U : Set H).eq_empty_or_nonempty with hempty | ⟨x₀, hx₀⟩
  · have : IsEmpty U := ⟨fun x ↦ eq_empty_iff_forall_notMem.1 hempty x x.property⟩
    exact quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_of_isEmpty R
  obtain ⟨F, hF, h₀, h₁⟩ := exists_contMDiff_contraction_of_starConvex hU
  exact quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_of_contraction R hF (F (1, ⟨x₀, hx₀⟩))
    h₀ fun x ↦ Subtype.ext ((h₁ x).trans (h₁ _).symm)

/-- **An open set with star-convex image in the model has vanishing positive-degree smooth
singular homology.** Let `U` be an open set of the model space `H` of a model with corners `I` whose
image `I '' U` is star-convex. The smooth contraction `(t, x) ↦ I.symm (c + (1 - ψ t) • (I x - c))`
towards the centre `c`, with `ψ` the smooth transition function from `0` to `1`, stays in `U`, so
the smooth singular homology of `U` vanishes in every positive degree. For a star-convex open
subset of a normed space `V`, take `I = 𝓘(ℝ, V)`. -/
theorem isZero_homology_smoothSingularSubcomplex_of_starConvex [CategoryWithHomology C]
    {H : Type u} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {U : TopologicalSpace.Opens H} {c : E} (hU : StarConvex ℝ c (I '' U)) {n : ℕ} (hn : n ≠ 0) :
    IsZero ((smoothSingularSubcomplex I U : SSet).homology R n) := by
  rcases (U : Set H).eq_empty_or_nonempty with hempty | ⟨x₀, hx₀⟩
  · -- An empty open set has no smooth simplices at all.
    have : IsEmpty U := ⟨fun x ↦ eq_empty_iff_forall_notMem.1 hempty x x.property⟩
    exact (HomologicalComplex.homologyFunctor C _ n).map_isZero (SSet.isZero_chainComplex _ R)
  obtain ⟨F, hF, h₀, h₁⟩ := exists_contMDiff_contraction_of_starConvex hU
  exact isZero_homology_smoothSingularSubcomplex_of_contMDiff R hF (F (1, ⟨x₀, hx₀⟩)) h₀
    (fun x ↦ Subtype.ext ((h₁ x).trans (h₁ _).symm)) hn

/-- **Smooth-chain homotopy equivalence for smoothly contractible manifolds.** If `Φ : ℝ × M → M`
is a smooth map joining a constant map `Φ (0, ·) = c` to the identity `Φ (1, ·) = id`, then the
inclusion of smooth singular chains into continuous singular chains on `M` is a chain homotopy
equivalence, obtained by time-reversing `Φ` and applying
`smoothSingularChainHomotopyEquivOfContraction`. -/
def smoothSingularChainHomotopyEquivOfContractible (c : M) {Φ : ℝ × M → M}
    (hΦ : ContMDiff (𝓘(ℝ).prod I) I ∞ Φ) (hΦ₀ : ∀ x, Φ (0, x) = c)
    (hΦ₁ : ∀ x, Φ (1, x) = x) (R : C) :
    HomotopyEquiv ((smoothSingularSubcomplex I M : SSet).chainComplex R)
      ((TopCat.toSSet.obj (TopCat.of M)).chainComplex R) :=
  smoothSingularChainHomotopyEquivOfContraction R
    (hΦ.comp ((contMDiff_const.sub contMDiff_fst).prodMk contMDiff_snd)) c
    (fun x ↦ by simpa using hΦ₁ x) (fun x ↦ by simpa using hΦ₀ x)

/-- The forward map of `smoothSingularChainHomotopyEquivOfContractible` is the inclusion of smooth
singular chains into continuous singular chains on `M`. -/
@[simp]
theorem smoothSingularChainHomotopyEquivOfContractible_hom (c : M) {Φ : ℝ × M → M}
    (hΦ : ContMDiff (𝓘(ℝ).prod I) I ∞ Φ) (hΦ₀ : ∀ x, Φ (0, x) = c)
    (hΦ₁ : ∀ x, Φ (1, x) = x) (R : C) :
    (smoothSingularChainHomotopyEquivOfContractible c hΦ hΦ₀ hΦ₁ R).hom =
      SSet.chainComplexMap (smoothSingularSubcomplex I M).ι R :=
  (rfl)

/-- On a smoothly contractible manifold with contraction centre `c`, the homotopy inverse sends
the summand of every singular `0`-simplex to the summand of the smooth `0`-simplex at `c`. -/
@[reassoc (attr := simp)]
theorem ι_smoothSingularChainHomotopyEquivOfContractible_inv_f_zero (c : M) {Φ : ℝ × M → M}
    (hΦ : ContMDiff (𝓘(ℝ).prod I) I ∞ Φ) (hΦ₀ : ∀ x, Φ (0, x) = c)
    (hΦ₁ : ∀ x, Φ (1, x) = x) (R : C) (σ : (TopCat.toSSet.obj (TopCat.of M)) _⦋0⦌) :
    (TopCat.toSSet.obj (TopCat.of M)).ιChainComplex σ ≫
        (smoothSingularChainHomotopyEquivOfContractible c hΦ hΦ₀ hΦ₁ R).inv.f 0 =
      (smoothSingularSubcomplex I M : SSet).ιChainComplex ((SmoothSimplex.equiv₀ I M).symm c) :=
  ι_smoothSingularChainHomotopyEquivOfContraction_inv_f_zero R _ c _ _ σ

/-- On a smoothly contractible manifold, the inclusion of smooth singular simplices induces an
isomorphism on homology in every degree (including degree zero). -/
theorem isIso_homologyMap_smoothSingularSubcomplex_ι_of_contractible [CategoryWithHomology C]
    (c : M) {Φ : ℝ × M → M} (hΦ : ContMDiff (𝓘(ℝ).prod I) I ∞ Φ)
    (hΦ₀ : ∀ x, Φ (0, x) = c) (hΦ₁ : ∀ x, Φ (1, x) = x) (R : C) (n : ℕ) :
    IsIso (SSet.homologyMap (smoothSingularSubcomplex I M).ι R n) := by
  have h := ((smoothSingularChainHomotopyEquivOfContractible c hΦ hΦ₀ hΦ₁ R).toHomologyIso
    n).isIso_hom
  change IsIso (HomologicalComplex.homologyMap
    (smoothSingularChainHomotopyEquivOfContractible c hΦ hΦ₀ hΦ₁ R).hom n) at h
  rwa [smoothSingularChainHomotopyEquivOfContractible_hom] at h

end TauCeti

section ModelSpace

open TauCeti

namespace ModelWithCorners

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type u} [TopologicalSpace H]
  {C : Type*} [Category* C] [Preadditive C] [HasCoproducts.{u} C]

/-- **Smooth-chain homotopy equivalence on any model space with corners.** Because `range I` is
convex in `E` with nonempty interior, the straight-line contraction
`(t, x) ↦ I.symm (I x₀ + ψ(t) • (I x - I x₀))` towards an interior point `x₀` stays in `range I`
and is jointly smooth on `ℝ × H`, so the inclusion of smooth singular chains on `H` is a chain
homotopy equivalence. -/
def smoothSingularChainHomotopyEquivModelSpace (I : ModelWithCorners ℝ E H) (R : C) :
    HomotopyEquiv ((smoothSingularSubcomplex I H : SSet).chainComplex R)
      ((TopCat.toSSet.obj (TopCat.of H)).chainComplex R) := by
  let x₀ : H := I.symm I.nonempty_interior.some
  let ΦE : ℝ × H → E := fun p ↦
    I x₀ + Real.smoothTransition p.1 • (I p.2 - I x₀)
  have hψ : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) ∞ fun p : ℝ × H ↦ Real.smoothTransition p.1 :=
    Real.smoothTransition.contDiff.contMDiff.comp contMDiff_fst
  have hI : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ, E) ∞ fun p : ℝ × H ↦ I p.2 :=
    I.contMDiff.comp contMDiff_snd
  have hΦE : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ, E) ∞ ΦE :=
    contMDiff_const.add (hψ.smul (hI.sub contMDiff_const))
  have hmem : ∀ p : ℝ × H, ΦE p ∈ range I := fun p ↦
    (I.convex_range.starConvex (mem_range_self x₀)).add_smul_sub_mem (mem_range_self p.2)
      (Real.smoothTransition.nonneg p.1) (Real.smoothTransition.le_one p.1)
  have hΦ : ContMDiff (𝓘(ℝ).prod I) I ∞ (fun p : ℝ × H ↦ I.symm (ΦE p)) :=
    I.contMDiffOn_symm.comp_contMDiff hΦE hmem
  exact smoothSingularChainHomotopyEquivOfContractible x₀ hΦ
    (fun x ↦ by simp [ΦE, Real.smoothTransition.zero])
    (fun x ↦ by simp [ΦE, Real.smoothTransition.one]) R

/-- The forward map of `smoothSingularChainHomotopyEquivModelSpace` is the inclusion of smooth
singular chains into continuous singular chains on `H`. -/
@[simp]
theorem smoothSingularChainHomotopyEquivModelSpace_hom (I : ModelWithCorners ℝ E H) (R : C) :
    (I.smoothSingularChainHomotopyEquivModelSpace R).hom =
      SSet.chainComplexMap (smoothSingularSubcomplex I H).ι R := by
  simp [smoothSingularChainHomotopyEquivModelSpace]

end ModelWithCorners

end ModelSpace

section StarConvex

open TauCeti

namespace StarConvex

variable {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {C : Type*} [Category* C] [Preadditive C] [HasCoproducts.{u} C]

open Classical in
/-- **Smooth-chain homotopy equivalence on star-convex open subsets of normed spaces.** For every
star-convex open subset `U` of a real normed space `V` (empty or nonempty, without finite-dimension
assumptions), the inclusion of smooth singular chains into continuous singular chains on `U` is a
chain homotopy equivalence. -/
def smoothSingularChainHomotopyEquivOfStarConvex {U : TopologicalSpace.Opens V} {c : V}
    (hU : StarConvex ℝ c (U : Set V)) (R : C) :
    HomotopyEquiv ((smoothSingularSubcomplex 𝓘(ℝ, V) U : SSet).chainComplex R)
      ((TopCat.toSSet.obj (TopCat.of U)).chainComplex R) :=
  if hne : (U : Set V).Nonempty then
    smoothSingularChainHomotopyEquivOfContractible ⟨c, hU.mem hne⟩
      hU.contMDiff_smoothContraction
      hU.smoothContraction_zero
      hU.smoothContraction_one R
  else
    have : Subsingleton U := ⟨fun x _ ↦ False.elim (hne ⟨x.val, x.property⟩)⟩
    𝓘(ℝ, V).smoothSingularChainHomotopyEquivOfSubsingleton U R

private lemma smoothSingularChainHomotopyEquivOfStarConvex_of_mem
    {U : TopologicalSpace.Opens V} {c : V} (hU : StarConvex ℝ c (U : Set V)) (hc : c ∈ U)
    (R : C) :
    hU.smoothSingularChainHomotopyEquivOfStarConvex R =
      smoothSingularChainHomotopyEquivOfContractible ⟨c, hc⟩
        hU.contMDiff_smoothContraction
        hU.smoothContraction_zero
        hU.smoothContraction_one R := by
  unfold smoothSingularChainHomotopyEquivOfStarConvex
  exact dite_eq_left_of_eq_true (eq_true (⟨c, hc⟩ : (U : Set V).Nonempty))

/-- The forward map of `smoothSingularChainHomotopyEquivOfStarConvex` is the inclusion of smooth
singular chains into continuous singular chains on `U`. -/
@[simp]
theorem smoothSingularChainHomotopyEquivOfStarConvex_hom {U : TopologicalSpace.Opens V} {c : V}
    (hU : StarConvex ℝ c (U : Set V)) (R : C) :
    (hU.smoothSingularChainHomotopyEquivOfStarConvex R).hom =
      SSet.chainComplexMap (smoothSingularSubcomplex 𝓘(ℝ, V) U).ι R := by
  unfold smoothSingularChainHomotopyEquivOfStarConvex
  split_ifs <;> simp

/-- On a nonempty star-convex open subset `U` with star-centre `c`, the inverse of
`smoothSingularChainHomotopyEquivOfStarConvex` sends every singular `0`-simplex to the smooth
`0`-simplex at `c`. -/
@[reassoc]
theorem ι_smoothSingularChainHomotopyEquivOfStarConvex_inv_f_zero
    {U : TopologicalSpace.Opens V} {c : V}
    (hU : StarConvex ℝ c (U : Set V)) (hc : c ∈ U) (R : C)
    (σ : (TopCat.toSSet.obj (TopCat.of U)) _⦋0⦌) :
    (TopCat.toSSet.obj (TopCat.of U)).ιChainComplex σ ≫
        (hU.smoothSingularChainHomotopyEquivOfStarConvex R).inv.f 0 =
      (smoothSingularSubcomplex 𝓘(ℝ, V) U : SSet).ιChainComplex
        ((SmoothSimplex.equiv₀ 𝓘(ℝ, V) U).symm ⟨c, hc⟩) := by
  rw [hU.smoothSingularChainHomotopyEquivOfStarConvex_of_mem hc R,
    ι_smoothSingularChainHomotopyEquivOfContractible_inv_f_zero]

end StarConvex

end StarConvex
