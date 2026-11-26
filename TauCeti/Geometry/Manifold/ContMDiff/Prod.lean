/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.ContMDiff.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-!
# Smooth maps from products

Mathlib equips a product of model vector spaces both with the product of their self-models and
with the self-model of the product. This file provides the `C^n` bridge between those
definitionally distinct presentations.

These bridges are useful when transporting `C^n` and `C^n`-on-a-set statements between product
chart coordinates and the self-model of the product model space.

The file also records a tube lemma: a map from a product which is `C^n` at every point of a
compact slice `{x} × K` is `C^n` on a product of open neighbourhoods of `x` and of `K`. For a family
`f : N → M → M` of self-maps, read as the map `(p, x) ↦ f p x` from `N × M`, joint smoothness along
a slice `{p₀} × M` passes to the iterates `p ↦ (f p)^[k]`, since the orbits of `f p₀` stay in that
slice.

## Main results

* `contMDiff_prod_modelWithCornersSelf_iff`: a map from a product of model vector spaces is `C^n`
  for the product of the self-models if and only if it is `C^n` for the self-model of the product.
* `contMDiffOn_prod_modelWithCornersSelf_iff`, `contMDiffAt_prod_modelWithCornersSelf_iff`: the
  same bridge for `C^n` maps on a set and at a point.
* `ContMDiffAt.contMDiffAt_prod_fst_slice`, `ContMDiffAt.contMDiffAt_prod_snd_slice`: fixing
  one of the last two factors of a three-factor product preserves joint regularity.
* `TauCeti.contMDiff_prod_prod_modelWithCornersSelf_iff`,
  `TauCeti.contMDiffOn_prod_prod_modelWithCornersSelf_iff`,
  `TauCeti.contMDiffAt_prod_prod_modelWithCornersSelf_iff`: the same bridge on the left factor of
  a product `(E₁ × E₂) × N₃` with an arbitrary manifold `N₃`.
* `TauCeti.exists_isOpen_prod_contMDiffOn`: the tube lemma for maps from a product which are
  `C^n` along a compact slice.
* `TauCeti.contMDiffAt_uncurry_iterate`: the iterates of a family of self-maps which is jointly
  `C^n` along a slice `{p₀} × M` are jointly `C^n` along it.
* `TauCeti.eventually_mdifferentiableAt_slice`: a jointly `C¹` family along a compact slice
  has differentiable slices uniformly on that compact set for all nearby parameters.
* `TauCeti.contMDiff_prodMap_id_prodMap_equivRealProdCLM_symm`: reading the complex factor of
  `ℝ × ℂ × V` in real coordinates is `C^n` from the self-model of `ℝ × (ℝ × ℝ) × V`.
* `TauCeti.contMDiff_prodMk_equivRealProdCLM_symm`: the same on `(P × (ℝ × ℝ)) × M` for a
  manifold `M`, with the factors regrouped as `P × (ℂ × M)`.
* `TauCeti.contMDiff_uncurry_const_mul_comp_const_mul`: `(t, x) ↦ ε * H (ε * t) x` is `C^n`
  when `H` is.

-/

public section

open Set
open scoped ContDiff Manifold Topology

variable {𝕜 E₁ E₂ E' H' M : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E₁] [NormedSpace 𝕜 E₁]
  [NormedAddCommGroup E₂] [NormedSpace 𝕜 E₂]
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
  [TopologicalSpace M] [ChartedSpace H' M]
  {n : WithTop ℕ∞} {f : E₁ × E₂ → M} {s : Set (E₁ × E₂)}

/-- A map from a product of model vector spaces is `C^n` for the product of the self-models if and
only if it is `C^n` for the self-model of the product. -/
theorem contMDiff_prod_modelWithCornersSelf_iff :
    ContMDiff (𝓘(𝕜, E₁).prod 𝓘(𝕜, E₂)) I' n f ↔
      ContMDiff 𝓘(𝕜, E₁ × E₂) I' n f := by
  rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]

/-- A map from a product of model vector spaces is `C^n` on a set for the product of the
self-models if and only if it is `C^n` on that set for the self-model of the product. -/
theorem contMDiffOn_prod_modelWithCornersSelf_iff :
    ContMDiffOn (𝓘(𝕜, E₁).prod 𝓘(𝕜, E₂)) I' n f s ↔
      ContMDiffOn 𝓘(𝕜, E₁ × E₂) I' n f s := by
  rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]

/-- A map from a product of model vector spaces is `C^n` at a point for the product of the
self-models if and only if it is `C^n` at that point for the self-model of the product. -/
theorem contMDiffAt_prod_modelWithCornersSelf_iff {x : E₁ × E₂} :
    ContMDiffAt (𝓘(𝕜, E₁).prod 𝓘(𝕜, E₂)) I' n f x ↔
      ContMDiffAt 𝓘(𝕜, E₁ × E₂) I' n f x := by
  rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]

section Slices

variable {E₃ : Type*} [NormedAddCommGroup E₃] [NormedSpace 𝕜 E₃]

/-- Fixing the last factor of a three-factor family preserves joint regularity in
its first two factors. -/
theorem ContMDiffAt.contMDiffAt_prod_fst_slice {f : E₁ → E₂ × E₃ → M}
    {q : E₁} {z : E₂ × E₃}
    (hf : ContMDiffAt 𝓘(𝕜, E₁ × (E₂ × E₃)) I' n (Function.uncurry f) (q, z)) :
    ContMDiffAt 𝓘(𝕜, E₁ × E₂) I' n (fun p : E₁ × E₂ ↦ f p.1 (p.2, z.2)) (q, z.1) :=
  hf.comp (q, z.1) (contMDiff_iff_contDiff.mpr (by fun_prop :
    ContDiff 𝕜 n (fun p : E₁ × E₂ ↦ (p.1, (p.2, z.2))))).contMDiffAt

/-- Fixing the middle factor of a three-factor family preserves joint regularity in
its first and last factors. -/
theorem ContMDiffAt.contMDiffAt_prod_snd_slice {f : E₁ → E₂ × E₃ → M}
    {q : E₁} {z : E₂ × E₃}
    (hf : ContMDiffAt 𝓘(𝕜, E₁ × (E₂ × E₃)) I' n (Function.uncurry f) (q, z)) :
    ContMDiffAt 𝓘(𝕜, E₁ × E₃) I' n (fun p : E₁ × E₃ ↦ f p.1 (z.1, p.2)) (q, z.2) :=
  hf.comp (q, z.2) (contMDiff_iff_contDiff.mpr (by fun_prop :
    ContDiff 𝕜 n (fun p : E₁ × E₃ ↦ (p.1, (z.1, p.2))))).contMDiffAt

end Slices

namespace TauCeti

section NestedProd

variable {E₃ H₃ N₃ : Type*} [NormedAddCommGroup E₃] [NormedSpace 𝕜 E₃] [TopologicalSpace H₃]
  {J₃ : ModelWithCorners 𝕜 E₃ H₃} [TopologicalSpace N₃] [ChartedSpace H₃ N₃]
  {g : (E₁ × E₂) × N₃ → M} {t : Set ((E₁ × E₂) × N₃)}

/-- A map from a product `(E₁ × E₂) × N₃`, whose left factor is a product of model vector spaces,
is `C^n` for the product of the self-models on the left factor if and only if it is `C^n` for the
self-model of `E₁ × E₂` on the left factor. -/
theorem contMDiff_prod_prod_modelWithCornersSelf_iff :
    ContMDiff ((𝓘(𝕜, E₁).prod 𝓘(𝕜, E₂)).prod J₃) I' n g ↔
      ContMDiff (𝓘(𝕜, E₁ × E₂).prod J₃) I' n g := by
  rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]

/-- The bridge `contMDiff_prod_prod_modelWithCornersSelf_iff` for `C^n` maps on a set. -/
theorem contMDiffOn_prod_prod_modelWithCornersSelf_iff :
    ContMDiffOn ((𝓘(𝕜, E₁).prod 𝓘(𝕜, E₂)).prod J₃) I' n g t ↔
      ContMDiffOn (𝓘(𝕜, E₁ × E₂).prod J₃) I' n g t := by
  rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]

/-- The bridge `contMDiff_prod_prod_modelWithCornersSelf_iff` for `C^n` maps at a point. -/
theorem contMDiffAt_prod_prod_modelWithCornersSelf_iff {x : (E₁ × E₂) × N₃} :
    ContMDiffAt ((𝓘(𝕜, E₁).prod 𝓘(𝕜, E₂)).prod J₃) I' n g x ↔
      ContMDiffAt (𝓘(𝕜, E₁ × E₂).prod J₃) I' n g x := by
  rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]

end NestedProd

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [ChartedSpace H' (X × Y)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners 𝕜 F G}
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]

/-- **The tube lemma for `C^n` maps from a product.** If `f : X × Y → N` is `C^n` at every point
of `{x} × K` with `K` compact and `n ≠ ∞`, then `f` is `C^n` on `U ×ˢ V` for some open
neighbourhoods `U` of `x` and `V` of `K`. -/
theorem exists_isOpen_prod_contMDiffOn [IsManifold I' n (X × Y)] [IsManifold J n N]
    {f : X × Y → N} {x : X} {K : Set Y} (hK : IsCompact K) (hn : n ≠ ∞)
    (hf : ∀ y ∈ K, ContMDiffAt I' J n f (x, y)) :
    ∃ U V, IsOpen U ∧ IsOpen V ∧ x ∈ U ∧ K ⊆ V ∧ ContMDiffOn I' J n f (U ×ˢ V) := by
  have hsub : {x} ×ˢ K ⊆ {z | ContMDiffAt I' J n f z} := by
    rintro ⟨x', y⟩ ⟨hx', hy⟩
    rw [mem_singleton_iff] at hx'
    subst hx'
    exact hf y hy
  obtain ⟨U, V, hUo, hVo, hU, hV, hUV⟩ :=
    generalized_tube_lemma isCompact_singleton hK (isOpen_setOfPred_contMDiffAt hn) hsub
  exact ⟨U, V, hUo, hVo, hU (mem_singleton x), hV, fun z hz ↦ (hUV hz).contMDiffWithinAt⟩

/-- A jointly `C¹` family along a compact slice has differentiable nearby slices,
uniformly at every point of the compact set. -/
theorem eventually_mdifferentiableAt_slice [IsManifold I' 1 M]
    {F : E₁ → E₂ → M} {x : E₁} {K : Set E₂} (hK : IsCompact K)
    (hF : ∀ y ∈ K,
      ContMDiffAt 𝓘(𝕜, E₁ × E₂) I' 1 (fun z : E₁ × E₂ ↦ F z.1 z.2) (x, y)) :
    ∀ᶠ u in 𝓝 x, ∀ y ∈ K, MDifferentiableAt 𝓘(𝕜, E₂) I' (F u) y := by
  obtain ⟨U, O, hUo, hOo, hxU, hO, hFUO⟩ :=
    exists_isOpen_prod_contMDiffOn hK (by simp) hF
  filter_upwards [hUo.mem_nhds hxU] with u hu y hy
  have hpt : ContMDiffAt 𝓘(𝕜, E₁ × E₂) I' 1
      (fun z : E₁ × E₂ ↦ F z.1 z.2) (u, y) :=
    hFUO.contMDiffAt ((hUo.prod hOo).mem_nhds ⟨hu, hO hy⟩)
  exact (hpt.comp y (contDiff_prodMk_right u).contMDiff.contMDiffAt).mdifferentiableAt
    one_ne_zero

/-- A jointly `C^n` family in the model space, fixing the base point of an extended chart at time
zero, gives a family on the manifold, jointly `C^n` at the base point and time zero, by
conjugating with the extended chart. The base point is an interior point, as every point of a
boundaryless manifold is (`BoundarylessManifold.isInteriorPoint`). -/
theorem contMDiffAt_extChartAt_symm_comp_extChartAt_prod (a : M) (ha : I'.IsInteriorPoint a)
    {φ : E' → 𝕜 → E'} (hφ : ContDiffAt 𝕜 n (fun p : E' × 𝕜 ↦ φ p.1 p.2) (extChartAt I' a a, 0))
    (hφ0 : φ (extChartAt I' a a) 0 = extChartAt I' a a) :
    ContMDiffAt (I'.prod 𝓘(𝕜, 𝕜)) I' n
      (fun p : M × 𝕜 ↦ (extChartAt I' a).symm (φ (extChartAt I' a p.1) p.2)) (a, 0) := by
  have hchart : ContMDiffAt (I'.prod 𝓘(𝕜, 𝕜)) 𝓘(𝕜, E') n
      (fun p : M × 𝕜 ↦ extChartAt I' a p.1) (a, 0) :=
    contMDiffAt_extChartAt.comp (a, 0) contMDiffAt_fst
  have hcoord : ContMDiffAt (I'.prod 𝓘(𝕜, 𝕜)) (𝓘(𝕜, E').prod 𝓘(𝕜, 𝕜)) n
      (fun p : M × 𝕜 ↦ (extChartAt I' a p.1, p.2)) (a, 0) :=
    hchart.prodMk contMDiffAt_snd
  have hφM := hφ.contMDiffAt
  rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod] at hφM
  have hinner : ContMDiffAt (I'.prod 𝓘(𝕜, 𝕜)) 𝓘(𝕜, E') n
      (fun p : M × 𝕜 ↦ φ (extChartAt I' a p.1) p.2) (a, 0) := by
    have h := hφM.comp (a, 0) hcoord
    simpa only [Function.comp_def] using h
  -- At an interior point the range of the model is a neighbourhood of the chart point.
  have hinv : ContMDiffAt 𝓘(𝕜, E') I' n (extChartAt I' a).symm (extChartAt I' a a) :=
    (contMDiffWithinAt_extChartAt_symm_range_self a).contMDiffAt
      (Filter.mem_of_superset (isOpen_interior.mem_nhds (I'.isInteriorPoint_iff.mp ha))
        (interior_subset.trans (extChartAt_target_subset_range a)))
  have hcomp := hinv.comp_of_eq hinner hφ0
  simpa only [Function.comp_def] using hcomp

/-- **Iterates of a jointly `C^n` family.** If a family `f : N → M → M` of self-maps is jointly
`C^n` at every point of the slice `{p₀} × M`, then so is the family of its `k`-th iterates
`p ↦ (f p)^[k]`. -/
theorem contMDiffAt_uncurry_iterate {f : N → M → M} {p₀ : N}
    (hf : ∀ x, ContMDiffAt (J.prod I') I' n (Function.uncurry f) (p₀, x)) (k : ℕ) (x : M) :
    ContMDiffAt (J.prod I') I' n (Function.uncurry fun p ↦ (f p)^[k]) (p₀, x) := by
  induction k generalizing x with
  | zero => exact contMDiffAt_snd
  | succ k ih =>
    have hk : (Function.uncurry fun p ↦ (f p)^[k + 1]) =
        Function.uncurry f ∘ fun q ↦ (q.1, (f q.1)^[k] q.2) := by
      funext ⟨p, y⟩
      exact Function.iterate_succ_apply' (f p) k y
    rw [hk]
    exact (hf _).comp_of_eq (contMDiffAt_fst.prodMk (ih x)) rfl

section RealCoords

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Reading the domain point in real coordinates is smooth: the map `(c, z, x) ↦ (c, z, x)` from
`ℝ × (ℝ × ℝ) × V` to `ℝ × ℂ × V` is `C^n` from the self-model of the product to the product of the
self-models. Composing with it turns the smoothness of data on `ℝ × ℂ × V` into smoothness in real
coordinates. -/
theorem contMDiff_prodMap_id_prodMap_equivRealProdCLM_symm :
    ContMDiff 𝓘(ℝ, ℝ × ((ℝ × ℝ) × V)) (𝓘(ℝ, ℝ).prod (𝓘(ℝ, ℂ).prod 𝓘(ℝ, V))) n
      (Prod.map id (Prod.map Complex.equivRealProdCLM.symm id) :
        ℝ × ((ℝ × ℝ) × V) → ℝ × (ℂ × V)) :=
  contDiff_fst.contMDiff.prodMk
    ((Complex.equivRealProdCLM.symm.contDiff.comp (contDiff_fst.comp contDiff_snd)).contMDiff.prodMk
      (contDiff_snd.comp contDiff_snd).contMDiff)

/-- Reading the domain point in real coordinates is smooth on a product with a manifold: the map
`((c, z), x) ↦ (c, (z, x))` from `(P × (ℝ × ℝ)) × M` to `P × (ℂ × M)` is `C^n`. Composing with it
turns the smoothness of a family on `P × (ℂ × M)` into smoothness in real coordinates. -/
theorem contMDiff_prodMk_equivRealProdCLM_symm {P E H₀ X : Type*} [NormedAddCommGroup P]
    [NormedSpace ℝ P] [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H₀]
    {I : ModelWithCorners ℝ E H₀} [TopologicalSpace X] [ChartedSpace H₀ X] :
    ContMDiff (𝓘(ℝ, P × (ℝ × ℝ)).prod I) (𝓘(ℝ, P).prod (𝓘(ℝ, ℂ).prod I)) n
      (fun p : (P × (ℝ × ℝ)) × X ↦ (p.1.1, (Complex.equivRealProdCLM.symm p.1.2, p.2))) :=
  (contDiff_fst.contMDiff.comp contMDiff_fst).prodMk
    (((Complex.equivRealProdCLM.symm.contDiff.comp contDiff_snd).contMDiff.comp
      contMDiff_fst).prodMk contMDiff_snd)

/-- Reflecting and rescaling a time-dependent function by a real constant preserves smoothness:
if `(t, x) ↦ H t x` is `C^n` on `ℝ × M`, then so is `(t, x) ↦ ε * H (ε * t) x`. With `ε = ±1`,
this is the Hamiltonian of a cylindrical end read in its positive end coordinate. -/
theorem contMDiff_uncurry_const_mul_comp_const_mul {E H₀ : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace H₀] {I : ModelWithCorners ℝ E H₀} {X : Type*}
    [TopologicalSpace X] [ChartedSpace H₀ X] {Ham : ℝ → X → ℝ} (ε : ℝ)
    (hHam : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) n (Function.uncurry Ham)) :
    ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) n (Function.uncurry fun t x ↦ ε * Ham (ε * t) x) :=
  (contDiff_const.mul contDiff_id).contMDiff.comp (hHam.comp
    (((contDiff_const.mul contDiff_id).contMDiff.comp contMDiff_fst).prodMk contMDiff_snd))

end RealCoords

end TauCeti
