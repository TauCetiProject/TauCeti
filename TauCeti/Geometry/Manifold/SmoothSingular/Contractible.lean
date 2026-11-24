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

## Main definitions and results

* `TauCeti.smoothSingularChainHomotopyEquivOfContraction`: on a smoothly contractible manifold,
  the inclusion of smooth singular chains into singular chains is a chain homotopy equivalence.
* `TauCeti.quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_of_contraction`,
  `TauCeti.quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_of_isEmpty`,
  `TauCeti.quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_of_starConvex`: the inclusion is a
  quasi-isomorphism on a smoothly contractible manifold, on the empty manifold, and on an open set
  of the model space with star-convex image.
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

open CategoryTheory Limits Set Convexity
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

end TauCeti
