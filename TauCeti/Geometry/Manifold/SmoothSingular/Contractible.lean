/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.AlgebraicTopology.SingularHomology.Basic
public import TauCeti.AlgebraicTopology.Singular.Empty
public import TauCeti.Geometry.Manifold.ContMDiff.Subtype
public import TauCeti.Geometry.Manifold.SmoothSingular.Homotopy

import TauCeti.Geometry.Manifold.ContMDiff.Contraction

/-!
# Smooth and singular chains of smoothly contractible manifolds

Let `M` be a manifold whose identity is joined to a constant map `x ↦ c` by a smooth map
`F : ℝ × M → M`, with `F (0, x) = x` and `F (1, x) = c`. The inclusion of smooth singular chains
into singular chains, with coefficients in any object `R` of a preadditive category with coproducts,
is a chain homotopy equivalence (`TauCeti.smoothSingularChainHomotopyEquivOfContMDiff`), and in
particular a quasi-isomorphism
(`TauCeti.quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_of_contMDiff`). Homotopy invariance
alone shows that the smooth singular homology of such a manifold vanishes in positive degrees
(`TauCeti.isZero_homology_smoothSingularSubcomplex_of_contMDiff`).

The same holds for the empty manifold, where both complexes vanish
(`TauCeti.quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_of_isEmpty`). For an open set `U` of
the model space `H` of a model with corners `I` whose image `I '' U` is star-convex about `c`:
when `U` is nonempty, `TauCeti.exists_contMDiff_contraction_of_starConvex` provides a smooth
contraction to `I.symm c`, so `TauCeti.smoothSingularChainHomotopyEquivOfContMDiff` yields the
chain homotopy equivalence; when `U` is empty, `U` is a subsingleton and
`ModelWithCorners.smoothSingularChainHomotopyEquivOfSubsingleton` applies instead. Combining the two
cases gives `TauCeti.smoothSingularChainHomotopyEquivOfStarConvex`, hence the quasi-isomorphism
`TauCeti.quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_of_starConvex` and the vanishing of
positive-degree smooth singular homology
(`TauCeti.isZero_homology_smoothSingularSubcomplex_of_starConvex`). The model may have boundary
and corners: the contraction stays in `range I` because `I '' U` does. A star-convex open subset of
a normed space `V` is the case `I = 𝓘(ℝ, V)`.

These are the base cases of the Mayer–Vietoris induction (`TauCeti.mayerVietoris_induction`) that
compares smooth with continuous singular homology on manifolds with corners: the empty open set,
and the open sets of the model space with convex image, which form a basis closed under
intersection. The step for countable disjoint unions is
`TauCeti.quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_iSup`.

On a nonempty star-convex open set `U` with `I.symm c ∈ U`,
`TauCeti.smoothSingularChainHomotopyEquivOfStarConvex_inv` identifies the homotopy inverse with the
chain map induced by collapsing `U` to `I.symm c`, yielding the `0`-simplex computation
`TauCeti.ι_smoothSingularChainHomotopyEquivOfStarConvex_inv_f_zero`.

## Main definitions and results

* `TauCeti.smoothSingularChainHomotopyEquivOfStarConvex`: on an open set of the model space with
  star-convex image, the inclusion of smooth singular chains into singular chains is a chain
  homotopy equivalence (handling both nonempty and empty opens).
* `TauCeti.smoothSingularChainHomotopyEquivOfStarConvex_inv`,
  `TauCeti.ι_smoothSingularChainHomotopyEquivOfStarConvex_inv_f_zero`: on a nonempty star-convex
  open set, the homotopy inverse is induced by the constant map to `I.symm c`, sending every
  singular `0`-simplex to the smooth `0`-simplex at `I.symm c`.
* `TauCeti.quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_of_isEmpty`,
  `TauCeti.quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_of_starConvex`: the inclusion is a
  quasi-isomorphism on the empty manifold and on an open set of the model space with star-convex
  image.
* `TauCeti.exists_contMDiff_contraction_of_starConvex`: when nonempty, an open set of the model
  space with star-convex image about `c` admits a smooth contraction to `I.symm c` (for empty
  opens, the universal conditions hold vacuously).
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
star-convex about `c`. When `U` is nonempty, `(t, x) ↦ I.symm (c + (1 - ψ t) • (I x - c))`, with
`ψ` the smooth transition function from `0` to `1`, is a smooth map `ℝ × U → U` joining the
identity to the constant map with value `I.symm c ∈ U`. This is the case `M = H` of
`exists_contMDiff_contraction_of_starConvex_image_extChartAt`, where the extended chart is `I`;
when `U` is empty, the universal conditions over `U` hold vacuously. -/
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

open Classical in
/-- **Smooth-chain homotopy equivalence on an open set with star-convex image in the model.**
Let `U` be an open set of the model space `H` of a model with corners `I` whose image `I '' U` is
star-convex about `c`. When `U` is nonempty, `U` contracts smoothly to `I.symm c`, so the inclusion
of smooth singular chains of `U` into continuous singular chains of `U` is a chain homotopy
equivalence via `TauCeti.smoothSingularChainHomotopyEquivOfContMDiff`; when `U` is empty, `U` is a
subsingleton and `ModelWithCorners.smoothSingularChainHomotopyEquivOfSubsingleton` gives the
equivalence. -/
def smoothSingularChainHomotopyEquivOfStarConvex
    {H : Type u} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {U : TopologicalSpace.Opens H} {c : E} (hU : StarConvex ℝ c (I '' U)) :
    HomotopyEquiv ((smoothSingularSubcomplex I U : SSet).chainComplex R)
      ((TopCat.toSSet.obj (TopCat.of U)).chainComplex R) :=
  if hne : (U : Set H).Nonempty then
    let hex := exists_contMDiff_contraction_of_starConvex hU
    let y₀ : H := I.symm c
    have hy₀ : y₀ ∈ U := by
      obtain ⟨x₀, hx₀⟩ := hne
      obtain ⟨z, hzU, hz⟩ := hU.mem ⟨I x₀, Set.mem_image_of_mem I hx₀⟩
      simpa [y₀, ← hz, I.left_inv] using hzU
    smoothSingularChainHomotopyEquivOfContMDiff R hex.choose_spec.1 ⟨y₀, hy₀⟩
      hex.choose_spec.2.1 (fun x ↦ Subtype.ext (hex.choose_spec.2.2 x))
  else
    have : Subsingleton U := ⟨fun x _ ↦ False.elim (hne ⟨x.val, x.property⟩)⟩
    I.smoothSingularChainHomotopyEquivOfSubsingleton U R

/-- The forward map of `smoothSingularChainHomotopyEquivOfStarConvex` is the inclusion of smooth
singular chains into continuous singular chains on `U`. -/
@[simp]
theorem smoothSingularChainHomotopyEquivOfStarConvex_hom
    {H : Type u} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {U : TopologicalSpace.Opens H} {c : E} (hU : StarConvex ℝ c (I '' U)) :
    (smoothSingularChainHomotopyEquivOfStarConvex R hU).hom =
      SSet.chainComplexMap (smoothSingularSubcomplex I U).ι R := by
  unfold smoothSingularChainHomotopyEquivOfStarConvex
  split_ifs <;> simp

/-- On a nonempty open set `U` with star-convex image `I '' U` around `c`, the homotopy inverse of
`smoothSingularChainHomotopyEquivOfStarConvex` is induced by collapsing `U` to the constant smooth
`0`-simplex at `I.symm c`. -/
@[simp]
theorem smoothSingularChainHomotopyEquivOfStarConvex_inv
    {H : Type u} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {U : TopologicalSpace.Opens H} {c : E} (hU : StarConvex ℝ c (I '' U))
    (hc : I.symm c ∈ U) :
    (smoothSingularChainHomotopyEquivOfStarConvex R hU).inv =
      SSet.chainComplexMap
        (constToSmoothSingularSubcomplex I (TopCat.of U) ⟨I.symm c, hc⟩) R := by
  unfold smoothSingularChainHomotopyEquivOfStarConvex
  split_ifs with hne
  · simp
  · exact absurd ⟨I.symm c, hc⟩ hne

/-- On a nonempty open set `U` with star-convex image `I '' U` around `c`, the inverse of
`smoothSingularChainHomotopyEquivOfStarConvex` sends every singular `0`-simplex to the smooth
`0`-simplex at `I.symm c`. -/
@[reassoc]
theorem ι_smoothSingularChainHomotopyEquivOfStarConvex_inv_f_zero
    {H : Type u} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {U : TopologicalSpace.Opens H} {c : E} (hU : StarConvex ℝ c (I '' U))
    (hc : I.symm c ∈ U) (σ : (TopCat.toSSet.obj (TopCat.of U)) _⦋0⦌) :
    (TopCat.toSSet.obj (TopCat.of U)).ιChainComplex σ ≫
        (smoothSingularChainHomotopyEquivOfStarConvex R hU).inv.f 0 =
      (smoothSingularSubcomplex I U : SSet).ιChainComplex
        ((SmoothSimplex.equiv₀ I U).symm ⟨I.symm c, hc⟩) := by
  rw [smoothSingularChainHomotopyEquivOfStarConvex_inv R hU hc, SSet.ι_chainComplexMap_f,
    constToSmoothSingularSubcomplex_app_zero]

/-- **The smoothing theorem for an open set with star-convex image in the model.** Let `U` be an
open set of the model space `H` of a model with corners `I` whose image `I '' U` is star-convex.
Then the inclusion of smooth singular chains of `U` into singular chains is a quasi-isomorphism. -/
theorem quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_of_starConvex [CategoryWithHomology C]
    {H : Type u} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {U : TopologicalSpace.Opens H} {c : E} (hU : StarConvex ℝ c (I '' U)) :
    QuasiIso (SSet.chainComplexMap (smoothSingularSubcomplex I U).ι R) := by
  rw [← smoothSingularChainHomotopyEquivOfStarConvex_hom R hU]
  exact (smoothSingularChainHomotopyEquivOfStarConvex R hU).quasiIso_hom

/-- **An open set with star-convex image in the model has vanishing positive-degree smooth
singular homology.** Let `U` be an open set of the model space `H` of a model with corners `I` whose
image `I '' U` is star-convex. When `U` is empty, it has no smooth simplices; when `U` is nonempty,
the smooth contraction `(t, x) ↦ I.symm (c + (1 - ψ t) • (I x - c))` towards `c`, with `ψ` the
smooth transition function from `0` to `1`, stays in `U`, so the smooth singular homology of `U`
vanishes in every positive degree. For a star-convex open subset of a normed space `V`, take
`I = 𝓘(ℝ, V)`. -/
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
