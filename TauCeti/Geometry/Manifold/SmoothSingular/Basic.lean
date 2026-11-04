/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Subcomplex
public import TauCeti.AlgebraicTopology.SimplicialSet.TopAdj
public import TauCeti.Geometry.Convex.FullSimplex
public import TauCeti.Geometry.Manifold.ContMDiff.OnSubset

/-!
# Smooth singular simplices

A singular `k`-simplex `σ` of a manifold `M` is *smooth* when, read on the full-dimensional
standard simplex `Δᵏ = {x ∈ ℝᵏ | 0 ≤ xᵢ, ∑ xᵢ ≤ 1}` through `fullSimplexEquivStdSimplex`, it is
smooth in the sense of maps on arbitrary subsets (`TauCeti.ContMDiffOnSubset`): near every point
of `Δᵏ`, including the points of its faces and corners, it agrees with a smooth map defined on a
neighbourhood in `ℝᵏ`.

Every simplicial operator of the standard simplices is the restriction of a continuous affine map
of the ambient Euclidean spaces (`TauCeti.simplexMapAmbient_coe`), so the
smooth simplices are closed under faces and degeneracies and form a subcomplex
`TauCeti.smoothSingularSubcomplex` of Mathlib's singular simplicial set `TopCat.toSSet.obj M`.
Applying Mathlib's simplicial chain functor gives the complex of smooth singular chains
`(smoothSingularSubcomplex I M : SSet).chainComplex R`, with boundary the alternating sum of the
faces, and `SSet.chainComplexMap (smoothSingularSubcomplex I M).ι R` is its inclusion into singular
chains. A smooth map of manifolds carries smooth simplices to smooth simplices
(`TauCeti.smoothSingularSubcomplexMap`).

The `p`-simplices of the subcomplex form the type `TauCeti.SmoothSimplex I M p`. A smooth simplex
is determined by the continuous map it induces on `Δᵖ` (`TauCeti.SmoothSimplex.toContinuousMap`),
and every continuous map on `Δᵖ` that is smooth in the sense of maps on arbitrary subsets is one
(`TauCeti.SmoothSimplex.mk`). Its extension to `ℝᵖ` by its value at the origin
(`TauCeti.SmoothSimplex.extension`) is smooth within `Δᵖ`.

These are the chains on which forms are integrated in the comparison of de Rham cohomology with
singular cohomology. Only a charted space is required for the definitions.

## Main definitions and results

* `TauCeti.smoothSingularSubcomplex`: the subcomplex of smooth singular simplices.
* `TauCeti.smoothSingularSubcomplex_le_preimage`: smooth maps preserve smooth simplices.
* `TauCeti.smoothSingularSubcomplexMap`: the induced map of smooth singular subcomplexes.
* `TauCeti.SmoothSimplex`: the smooth singular `p`-simplices, the `p`-simplices of
  `TauCeti.smoothSingularSubcomplex`.
* `TauCeti.SmoothSimplex.toContinuousMap`, `TauCeti.SmoothSimplex.mk`: a smooth simplex as a
  continuous map on `Δᵖ`, and back.
* `TauCeti.SmoothSimplex.toContinuousMap_map_apply`,
  `TauCeti.SmoothSimplex.toContinuousMap_δ_apply`,
  `TauCeti.SmoothSimplex.toContinuousMap_σ_apply`: simplicial operators read on `Δᵖ`.
* `TauCeti.SmoothSimplex.equiv₀`: smooth `0`-simplices identified with points of `M`.
* `TauCeti.SmoothSimplex.ofContMDiffOn`, `TauCeti.SmoothSimplex.ofContMDiff`,
  `TauCeti.SmoothSimplex.ofCurve`: smooth simplices from smooth maps on `ℝᵖ` and smooth curves.
* `TauCeti.SmoothSimplex.extension`: a smooth simplex extended to `ℝᵖ`, smooth within `Δᵖ`.
* `TauCeti.SmoothSimplex.toContinuousMap_smoothSingularSubcomplexMap_app`: a smooth map acts on
  smooth simplices by composition.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Chapter 18, *Smooth Singular Homology*.
-/

public section

noncomputable section

open CategoryTheory Convexity Set Topology Simplicial Opposite
open scoped Manifold ContDiff

universe u

namespace TauCeti

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H) (M : Type u) [TopologicalSpace M] [ChartedSpace H M]

/-- The smooth singular simplices of `M`: those singular simplices which, read on the
full-dimensional standard simplex, are smooth in the sense of maps on arbitrary subsets. They form a
subcomplex of the singular simplicial set, since every simplicial operator is the restriction of a
smooth map of the ambient Euclidean spaces. -/
def smoothSingularSubcomplex : (TopCat.toSSet.obj (TopCat.of M)).Subcomplex where
  obj k := {σ | ContMDiffOnSubset I ∞
    ((TopCat.of M).toSSetObjEquiv k σ ∘ fullSimplexEquivStdSimplex k.unop.len)}
  map {k l} f σ hσ := by
    let A := simplexMapAmbient f.unop.toOrderHom
    have hst : MapsTo A (fullSimplex l.unop.len) (fullSimplex k.unop.len) := fun x hx ↦
      simplexMapAmbient_coe _ ⟨x, hx⟩ ▸ Subtype.prop _
    rw [Set.mem_preimage, Set.mem_ofPred_eq]
    convert hσ.comp_contDiff A.contDiff hst using 2
    funext x
    have hx : hst.restrict A _ _ x = (fullSimplexEquivStdSimplex _).symm
        ((fullSimplexEquivStdSimplex _ x).map f.unop.toOrderHom) :=
      Subtype.ext (simplexMapAmbient_coe _ x)
    simp only [Function.comp_apply, hx, Homeomorph.apply_symm_apply]
    exact TopCat.toSSetObjEquiv_naturality_apply f.unop σ _

variable {I M}

/-- A singular simplex is smooth exactly when, read on the full-dimensional standard simplex, it is
smooth in the sense of maps on arbitrary subsets. -/
@[simp]
theorem mem_smoothSingularSubcomplex_iff {k : SimplexCategoryᵒᵖ}
    (σ : (TopCat.toSSet.obj (TopCat.of M)).obj k) :
    σ ∈ (smoothSingularSubcomplex I M).obj k ↔ ContMDiffOnSubset I ∞
      ((TopCat.of M).toSSetObjEquiv k σ ∘ fullSimplexEquivStdSimplex k.unop.len) :=
  Iff.rfl

/-- A singular simplex which, read on the full-dimensional standard simplex, is the restriction of
a map that is smooth on a neighbourhood of the simplex in `ℝᵏ` is smooth. -/
theorem mem_smoothSingularSubcomplex_of_contMDiffOn {k : SimplexCategoryᵒᵖ}
    (σ : (TopCat.toSSet.obj (TopCat.of M)).obj k) {U : Set (EuclideanSpace ℝ (Fin k.unop.len))}
    {g : EuclideanSpace ℝ (Fin k.unop.len) → M}
    (hg : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin k.unop.len)) I ∞ g U)
    (hU : U ∈ 𝓝ˢ (fullSimplex k.unop.len))
    (hσ : ∀ x, (TopCat.of M).toSSetObjEquiv k σ (fullSimplexEquivStdSimplex _ x) = g x) :
    σ ∈ (smoothSingularSubcomplex I M).obj k := by
  rw [mem_smoothSingularSubcomplex_iff]
  convert hg.contMDiffOnSubset hU using 1
  exact funext hσ

/-- Every singular `0`-simplex of `M` is smooth, since `Δ⁰` is a point. -/
@[simp]
theorem smoothSingularSubcomplex_obj_zero :
    (smoothSingularSubcomplex I M).obj (op ⦋0⦌) = Set.univ := by
  refine Set.eq_univ_of_forall fun σ ↦ ?_
  refine mem_smoothSingularSubcomplex_of_contMDiffOn σ
    (g := fun _ ↦ TopCat.toSSetObj₀Equiv σ) contMDiffOn_const Filter.univ_mem fun x ↦ ?_
  rw [Subsingleton.elim (fullSimplexEquivStdSimplex 0 x) default]
  exact (TopCat.toSSetObj₀Equiv_apply σ).symm

variable (I M) in
/-- The smooth singular `p`-simplices of `M`: the `p`-simplices of the subcomplex
`TauCeti.smoothSingularSubcomplex I M` of the singular simplicial set. They generate the smooth
singular chains. -/
abbrev SmoothSimplex (p : ℕ) : Type u :=
  (smoothSingularSubcomplex I M : SSet.{u}) _⦋p⦌

namespace SmoothSimplex

variable {p : ℕ}

/-- A smooth singular simplex as a continuous map on the full-dimensional simplex `Δᵖ`. -/
def toContinuousMap (σ : SmoothSimplex I M p) : C(fullSimplex p, M) :=
  ((TopCat.of M).toSSetObjEquiv _ σ.1).comp
    ⟨fullSimplexEquivStdSimplex p, (fullSimplexEquivStdSimplex p).continuous⟩

/-- A smooth singular simplex read on `Δᵖ` is the underlying singular simplex read through the
identification of `Δᵖ` with the barycentric standard simplex. -/
theorem toContinuousMap_apply (σ : SmoothSimplex I M p) (x : fullSimplex p) :
    σ.toContinuousMap x = (TopCat.of M).toSSetObjEquiv _ σ.1 (fullSimplexEquivStdSimplex p x) :=
  (rfl)

/-- A smooth singular simplex is smooth on `Δᵖ` in the sense of maps on arbitrary subsets. -/
theorem contMDiffOnSubset_toContinuousMap (σ : SmoothSimplex I M p) :
    ContMDiffOnSubset I ∞ σ.toContinuousMap :=
  (mem_smoothSingularSubcomplex_iff σ.1).mp σ.2

/-- A smooth singular simplex is determined by the map it induces on `Δᵖ`. -/
theorem toContinuousMap_injective :
    Function.Injective (toContinuousMap : SmoothSimplex I M p → C(fullSimplex p, M)) := by
  intro σ τ h
  refine Subtype.ext (((TopCat.of M).toSSetObjEquiv _).injective (ContinuousMap.ext fun y ↦ ?_))
  simpa only [toContinuousMap_apply, Homeomorph.apply_symm_apply] using
    DFunLike.congr_fun h ((fullSimplexEquivStdSimplex p).symm y)

/-- Two smooth singular simplices agreeing on `Δᵖ` are equal. -/
@[ext]
theorem ext {σ τ : SmoothSimplex I M p} (h : ∀ x, σ.toContinuousMap x = τ.toContinuousMap x) :
    σ = τ :=
  toContinuousMap_injective (ContinuousMap.ext h)

/-- The smooth singular simplex given by a continuous map on `Δᵖ` that is smooth in the sense of
maps on arbitrary subsets. -/
def mk (f : C(fullSimplex p, M)) (hf : ContMDiffOnSubset I ∞ f) : SmoothSimplex I M p :=
  ⟨((TopCat.of M).toSSetObjEquiv _).symm (f.comp (fullSimplexEquivStdSimplex p).symm),
    by simpa [mem_smoothSingularSubcomplex_iff, Function.comp_def] using hf⟩

/-- The smooth simplex given by a map on `Δᵖ` induces that map. -/
@[simp]
theorem toContinuousMap_mk (f : C(fullSimplex p, M)) (hf : ContMDiffOnSubset I ∞ f) :
    (mk f hf).toContinuousMap = f := by
  ext x
  simp [toContinuousMap_apply, mk]

/-- The extension of a smooth singular simplex to `ℝᵖ` by its value at the origin off `Δᵖ`. Only
its values on `Δᵖ` and its derivatives within `Δᵖ` carry information. -/
def extension (σ : SmoothSimplex I M p) : EuclideanSpace ℝ (Fin p) → M :=
  Function.extend Subtype.val σ.toContinuousMap
    fun _ ↦ σ.toContinuousMap ⟨0, zero_mem_fullSimplex p⟩

/-- The extension of a smooth simplex agrees with it on `Δᵖ`. -/
@[simp]
theorem extension_coe (σ : SmoothSimplex I M p) (x : fullSimplex p) :
    σ.extension x = σ.toContinuousMap x :=
  Subtype.val_injective.extend_apply _ _ x

/-- The extension of a smooth simplex is smooth within `Δᵖ`. -/
theorem contMDiffOn_extension (σ : SmoothSimplex I M p) :
    ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) I ∞ σ.extension (fullSimplex p) :=
  σ.contMDiffOnSubset_toContinuousMap.contMDiffOn σ.extension_coe

/-- A simplicial operator on smooth simplices acts on `Δ^q` by precomposition with the ambient
affine map `simplexMapAmbient`. -/
theorem toContinuousMap_map_apply {q p : ℕ} (f : ⦋q⦌ ⟶ ⦋p⦌) (σ : SmoothSimplex I M p)
    (x : fullSimplex q) :
    toContinuousMap ((smoothSingularSubcomplex I M : SSet).map f.op σ) x =
      σ.toContinuousMap ⟨simplexMapAmbient f.toOrderHom x, mapsTo_simplexMapAmbient _ x.2⟩ := by
  have hx : (⟨simplexMapAmbient f.toOrderHom x, mapsTo_simplexMapAmbient _ x.2⟩ : fullSimplex p) =
      (fullSimplexEquivStdSimplex p).symm ((fullSimplexEquivStdSimplex q x).map f.toOrderHom) :=
    Subtype.ext (simplexMapAmbient_coe _ x)
  rw [toContinuousMap_apply, hx, toContinuousMap_apply, Homeomorph.apply_symm_apply]
  exact TopCat.toSSetObjEquiv_naturality_apply f σ.1 (fullSimplexEquivStdSimplex q x)

-- `simp` reduces `SmoothSimplex` (`(smoothSingularSubcomplex I M).toSSet.obj _`) in implicit type
-- arguments via `Subfunctor.toFunctor_obj` before looking up a lemma, so `simp` lemmas involving
-- simplicial operators, `equiv₀`, or `smoothSingularSubcomplexMap` normalize their left-hand sides
-- with `dsimp% only [Subfunctor.toFunctor_obj]`.
/-- The `i`-th face of a smooth `(p + 1)`-simplex, read on `Δᵖ`, is its restriction along the
`i`-th face inclusion `simplexFace p i`. -/
@[simp]
theorem toContinuousMap_δ_apply (i : Fin (p + 2)) (σ : SmoothSimplex I M (p + 1))
    (x : fullSimplex p) :
    (dsimp% only [Subfunctor.toFunctor_obj]
      (toContinuousMap ((smoothSingularSubcomplex I M : SSet).δ i σ) x)) =
      σ.toContinuousMap (simplexFace p i x) := by
  refine (toContinuousMap_map_apply (SimplexCategory.δ i) σ x).trans ?_
  exact congrArg σ.toContinuousMap (Subtype.ext (simplexMapAmbient_succAbove_coe i x))

/-- The `i`-th degeneracy of a smooth `p`-simplex, read on `Δᵖ⁺¹`, precomposes with the ambient
projection `simplexMapAmbient i.predAbove`. -/
theorem toContinuousMap_σ_apply (i : Fin (p + 1)) (σ : SmoothSimplex I M p)
    (x : fullSimplex (p + 1)) :
    toContinuousMap ((smoothSingularSubcomplex I M : SSet).σ i σ) x =
      σ.toContinuousMap ⟨simplexMapAmbient i.predAbove x, mapsTo_simplexMapAmbient _ x.2⟩ :=
  toContinuousMap_map_apply (SimplexCategory.σ i) σ x

variable (I M) in
/-- Smooth `0`-simplices of `M` correspond bijectively to points of `M`, restricting
`TopCat.toSSetObj₀Equiv`. -/
def equiv₀ : SmoothSimplex I M 0 ≃ M where
  toFun σ := (TopCat.of M).toSSetObj₀Equiv σ.1
  invFun x₀ := ⟨(TopCat.of M).toSSetObj₀Equiv.symm x₀, by simp⟩
  left_inv σ := Subtype.ext ((TopCat.of M).toSSetObj₀Equiv.symm_apply_apply σ.1)
  right_inv x₀ := (TopCat.of M).toSSetObj₀Equiv.apply_symm_apply x₀

/-- The underlying singular `0`-simplex of `(equiv₀ I M).symm x₀` is
`TopCat.toSSetObj₀Equiv.symm x₀`. -/
@[simp]
theorem coe_equiv₀_symm (x₀ : M) :
    (dsimp% only [Subfunctor.toFunctor_obj] (((equiv₀ I M).symm x₀).1)) =
      (TopCat.of M).toSSetObj₀Equiv.symm x₀ :=
  (rfl)

/-- The point of `M` corresponding to a smooth `0`-simplex is its value at the unique point of
`Δ⁰`. -/
@[simp]
theorem equiv₀_apply (σ : SmoothSimplex I M 0) :
    (dsimp% only [Subfunctor.toFunctor_obj] (equiv₀ I M σ)) =
      σ.toContinuousMap ⟨0, zero_mem_fullSimplex 0⟩ := by
  rw [equiv₀, Equiv.coe_fn_mk, TopCat.toSSetObj₀Equiv_apply, toContinuousMap_apply,
    Subsingleton.elim (fullSimplexEquivStdSimplex 0 ⟨0, zero_mem_fullSimplex 0⟩) default]

/-- Read on `Δ⁰`, the smooth `0`-simplex of `x₀` is the constant map to `x₀`. -/
@[simp]
theorem toContinuousMap_equiv₀_symm_apply (x₀ : M) (x : fullSimplex 0) :
    (dsimp% only [Subfunctor.toFunctor_obj] (((equiv₀ I M).symm x₀).toContinuousMap x)) = x₀ := by
  rw [Subsingleton.elim x ⟨0, zero_mem_fullSimplex 0⟩, ← equiv₀_apply, Equiv.apply_symm_apply]

/-- A map `g : ℝᵖ → M` that is smooth on a neighbourhood of `Δᵖ` restricts to a smooth
`p`-simplex. -/
def ofContMDiffOn {U : Set (EuclideanSpace ℝ (Fin p))} {g : EuclideanSpace ℝ (Fin p) → M}
    (hg : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) I ∞ g U) (hU : U ∈ 𝓝ˢ (fullSimplex p)) :
    SmoothSimplex I M p :=
  mk ⟨(fullSimplex p).domRestrict g, (hg.continuousOn.mono (subset_of_mem_nhdsSet hU)).domRestrict⟩
    (hg.contMDiffOnSubset hU)

/-- Read on `Δᵖ`, `ofContMDiffOn` evaluates the ambient map. -/
@[simp]
theorem toContinuousMap_ofContMDiffOn_apply {U : Set (EuclideanSpace ℝ (Fin p))}
    {g : EuclideanSpace ℝ (Fin p) → M}
    (hg : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) I ∞ g U) (hU : U ∈ 𝓝ˢ (fullSimplex p))
    (x : fullSimplex p) :
    (ofContMDiffOn hg hU).toContinuousMap x = g x := by
  simp [ofContMDiffOn]

/-- A smooth map `g : ℝᵖ → M` restricts to a smooth `p`-simplex. -/
def ofContMDiff {g : EuclideanSpace ℝ (Fin p) → M}
    (hg : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) I ∞ g) : SmoothSimplex I M p :=
  ofContMDiffOn hg.contMDiffOn Filter.univ_mem

/-- Read on `Δᵖ`, `ofContMDiff` evaluates the smooth map. -/
@[simp]
theorem toContinuousMap_ofContMDiff_apply {g : EuclideanSpace ℝ (Fin p) → M}
    (hg : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) I ∞ g) (x : fullSimplex p) :
    (ofContMDiff hg).toContinuousMap x = g x :=
  toContinuousMap_ofContMDiffOn_apply hg.contMDiffOn Filter.univ_mem x

/-- A smooth curve `γ : ℝ → M` defines a smooth `1`-simplex `x ↦ γ (x 0)`, lifting
`TauCeti.TopCat.simplex₁`. -/
def ofCurve {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ) : SmoothSimplex I M 1 :=
  ⟨TauCeti.TopCat.simplex₁ (X := TopCat.of M)
      ⟨fun t ↦ γ t, hγ.continuous.comp continuous_subtype_val⟩,
    mem_smoothSingularSubcomplex_of_contMDiffOn _ (g := fun y ↦ γ (y 0))
      (hγ.comp (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 1) 0).contDiff.contMDiff).contMDiffOn
      Filter.univ_mem fun x ↦ by
        rw [TauCeti.TopCat.toSSetObjEquiv_simplex₁, ContinuousMap.comp_apply,
          ContinuousMap.coe_mk, ContinuousMap.coe_ofClass, StdSimplex.homeomorphI_apply_coe]
        -- `(0 : Fin 1).succ` is definitionally `1 : Fin 2`.
        exact congrArg γ (fullSimplexEquivStdSimplex_weights_succ x 0)⟩

/-- The underlying singular `1`-simplex of `SmoothSimplex.ofCurve` is `TauCeti.TopCat.simplex₁`. -/
@[simp]
theorem coe_ofCurve {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ) :
    (ofCurve hγ).1 = TauCeti.TopCat.simplex₁ (X := TopCat.of M)
      ⟨fun t ↦ γ t, hγ.continuous.comp continuous_subtype_val⟩ :=
  (rfl)

/-- Read on `Δ¹`, the smooth `1`-simplex of `γ` evaluates `γ` at the unique coordinate. -/
@[simp]
theorem toContinuousMap_ofCurve_apply {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ)
    (x : fullSimplex 1) :
    (ofCurve hγ).toContinuousMap x = γ (x.1 0) := by
  rw [toContinuousMap_apply, coe_ofCurve, TauCeti.TopCat.toSSetObjEquiv_simplex₁,
    ContinuousMap.comp_apply, ContinuousMap.coe_mk, ContinuousMap.coe_ofClass,
    StdSimplex.homeomorphI_apply_coe]
  -- `(0 : Fin 1).succ` is definitionally `1 : Fin 2`.
  exact congrArg γ (fullSimplexEquivStdSimplex_weights_succ x 0)

/-- The `0`-th face of the smooth `1`-simplex of `γ` is the smooth vertex `γ 1`. -/
@[simp]
theorem δ_zero_ofCurve {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ) :
    (dsimp% only [Subfunctor.toFunctor_obj]
      ((smoothSingularSubcomplex I M : SSet).δ 0 (ofCurve hγ))) = (equiv₀ I M).symm (γ 1) :=
  Subtype.ext (TauCeti.TopCat.δ_zero_simplex₁ _)

/-- The `1`-st face of the smooth `1`-simplex of `γ` is the smooth vertex `γ 0`. -/
@[simp]
theorem δ_one_ofCurve {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ) :
    (dsimp% only [Subfunctor.toFunctor_obj]
      ((smoothSingularSubcomplex I M : SSet).δ 1 (ofCurve hγ))) = (equiv₀ I M).symm (γ 0) :=
  Subtype.ext (TauCeti.TopCat.δ_one_simplex₁ _)

end SmoothSimplex

variable {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} {N : Type u} [TopologicalSpace N] [ChartedSpace H' N]
  {φ : M → N}

/-- A smooth map carries smooth singular simplices to smooth singular simplices. -/
theorem smoothSingularSubcomplex_le_preimage (hφ : ContMDiff I J ∞ φ) :
    smoothSingularSubcomplex I M ≤ (smoothSingularSubcomplex J N).preimage
      (TopCat.toSSet.map (TopCat.ofHom ⟨φ, hφ.continuous⟩)) := fun k σ hσ ↦ by
  rw [SSet.Subcomplex.preimage_obj, Set.mem_preimage, mem_smoothSingularSubcomplex_iff,
    TopCat.toSSetObjEquiv_toSSet_map_app, ConcreteCategory.hom_ofHom, ContinuousMap.coe_comp,
    ContinuousMap.coe_mk, Function.comp_assoc]
  exact hφ.comp_contMDiffOnSubset hσ

variable (φ) in
/-- The map of smooth singular subcomplexes induced by a smooth map. -/
def smoothSingularSubcomplexMap (hφ : ContMDiff I J ∞ φ) :
    (smoothSingularSubcomplex I M : SSet) ⟶ (smoothSingularSubcomplex J N : SSet) :=
  SSet.Subcomplex.lift
    ((smoothSingularSubcomplex I M).ι ≫ TopCat.toSSet.map (TopCat.ofHom ⟨φ, hφ.continuous⟩)) (by
      rintro k _ ⟨σ, rfl⟩
      exact smoothSingularSubcomplex_le_preimage hφ k σ.2)

/-- The map of smooth singular subcomplexes is the restriction of the map of singular simplicial
sets. -/
@[reassoc (attr := simp)]
theorem smoothSingularSubcomplexMap_ι (hφ : ContMDiff I J ∞ φ) :
    smoothSingularSubcomplexMap φ hφ ≫ (smoothSingularSubcomplex J N).ι =
      (smoothSingularSubcomplex I M).ι ≫ TopCat.toSSet.map (TopCat.ofHom ⟨φ, hφ.continuous⟩) :=
  SSet.Subcomplex.lift_ι _ _

/-- The identity of `M` induces the identity of its smooth singular subcomplex. -/
@[simp]
theorem smoothSingularSubcomplexMap_id :
    smoothSingularSubcomplexMap (I := I) (J := I) (M := M) id contMDiff_id = 𝟙 _ := by
  -- Both sides send a smooth simplex to the same underlying singular simplex.
  ext k σ
  rfl

/-- The map of smooth singular subcomplexes induced by a composite is the composite of the induced
maps. -/
theorem smoothSingularSubcomplexMap_comp {E'' H'' : Type*} [NormedAddCommGroup E'']
    [NormedSpace ℝ E''] [TopologicalSpace H''] {K : ModelWithCorners ℝ E'' H''} {P : Type u}
    [TopologicalSpace P] [ChartedSpace H'' P] {ψ : N → P} (hψ : ContMDiff J K ∞ ψ)
    (hφ : ContMDiff I J ∞ φ) :
    smoothSingularSubcomplexMap (ψ ∘ φ) (hψ.comp hφ) =
      smoothSingularSubcomplexMap φ hφ ≫ smoothSingularSubcomplexMap ψ hψ := by
  -- Both sides postcompose the underlying singular simplex with `ψ ∘ φ`.
  ext k σ
  rfl

/-- The image of a smooth simplex under a smooth map, read on `Δᵖ`, is the composite. -/
theorem SmoothSimplex.toContinuousMap_smoothSingularSubcomplexMap_app {p : ℕ}
    (hφ : ContMDiff I J ∞ φ) (σ : SmoothSimplex I M p) :
    toContinuousMap ((smoothSingularSubcomplexMap φ hφ).app (op ⦋p⦌) σ) =
      (ContinuousMap.mk φ hφ.continuous).comp σ.toContinuousMap := by
  have h := ConcreteCategory.congr_hom
    (NatTrans.congr_app (smoothSingularSubcomplexMap_ι hφ) (op ⦋p⦌)) σ
  simp only [NatTrans.comp_app, ConcreteCategory.comp_apply, Subfunctor.ι_app,
    TypeCat.ofHom_apply] at h
  ext x
  rw [toContinuousMap_apply, h, TopCat.toSSetObjEquiv_toSSet_map_app]
  simp [toContinuousMap_apply]

/-- A smooth map carries the smooth `0`-simplex of `x₀` to that of `φ x₀`. -/
@[simp]
theorem SmoothSimplex.smoothSingularSubcomplexMap_app_equiv₀_symm
    (hφ : ContMDiff I J ∞ φ) (x₀ : M) :
    (dsimp% only [Subfunctor.toFunctor_obj]
      ((smoothSingularSubcomplexMap φ hφ).app (op ⦋0⦌) ((equiv₀ I M).symm x₀))) =
      (equiv₀ J N).symm (φ x₀) := by
  refine SmoothSimplex.ext fun x ↦ ?_
  rw [toContinuousMap_smoothSingularSubcomplexMap_app]
  simp

/-- A smooth map acts on `ofContMDiff` by postcomposition. -/
@[simp]
theorem SmoothSimplex.smoothSingularSubcomplexMap_app_ofContMDiff {p : ℕ}
    (hφ : ContMDiff I J ∞ φ) {g : EuclideanSpace ℝ (Fin p) → M}
    (hg : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) I ∞ g) :
    (dsimp% only [Subfunctor.toFunctor_obj]
      ((smoothSingularSubcomplexMap φ hφ).app (op ⦋p⦌) (ofContMDiff hg))) =
      ofContMDiff (hφ.comp hg) := by
  refine SmoothSimplex.ext fun x ↦ ?_
  rw [toContinuousMap_smoothSingularSubcomplexMap_app]
  simp

/-- A smooth map acts on `ofCurve` by postcomposition of the curve. -/
@[simp]
theorem SmoothSimplex.smoothSingularSubcomplexMap_app_ofCurve
    (hφ : ContMDiff I J ∞ φ) {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ) :
    (dsimp% only [Subfunctor.toFunctor_obj]
      ((smoothSingularSubcomplexMap φ hφ).app (op ⦋1⦌) (ofCurve hγ))) =
      ofCurve (hφ.comp hγ) := by
  refine SmoothSimplex.ext fun x ↦ ?_
  rw [toContinuousMap_smoothSingularSubcomplexMap_app]
  simp

end TauCeti
