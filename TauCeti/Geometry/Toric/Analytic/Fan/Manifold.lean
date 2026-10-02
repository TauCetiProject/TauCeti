/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Gluing
public import TauCeti.Geometry.Toric.Analytic.Fan.GlueData

/-!
# The complex manifold of a regular fan

The analytic realization `TauCeti.Toric.Fan.analyticRealization` of a regular fan is glued from
the affine analytic charts of its cones along the face localizations. This file installs its
complex atlas and proves that it is a complex manifold, modelled on `ℂ ^ n` for `n` the rank of
the lattice.

The complex structure on the affine chart of a regular cone comes from an extending integral
basis, which identifies the chart with the open subset `ℂ ^ k × (ℂˣ) ^ l` of `ℂ ^ k × ℂ ^ l`,
where `k` is the number of rays and `k + l = n`. Choosing such a basis for every cone and
identifying `ℂ ^ k × ℂ ^ l` linearly with `ℂ ^ n` makes every affine chart a manifold modelled on
`ℂ ^ n`. A map into an affine chart is holomorphic for this structure exactly when its values on
all monomials are, which lets every statement be transferred to the structure of any other
extending basis.

Two affine charts are glued along the chart of the intersection cone, through the open face
localizations into both. A face localization is a biholomorphism onto its open image, so the
charts are glued along holomorphic maps, and `TauCeti.chartedSpaceOfIsOpenEmbedding` gives the
realization a complex atlas making it a complex manifold. For this atlas, the inclusion of every
affine chart, with the complex structure of any extending basis, is a biholomorphism onto its
open image.

## Main declarations

* `TauCeti.Toric.Fan.analyticChartedSpace`: the complex atlas of the analytic realization.
* `TauCeti.Toric.Fan.isManifold_analyticRealization`: the analytic realization is a complex
  manifold.
* `TauCeti.Toric.Fan.analyticAffineChartPartialDiffeomorph`: the inclusion of an affine analytic
  chart is a biholomorphism onto its open image.
* `TauCeti.Toric.Fan.contMDiff_analyticAffineChartι`: the inclusion of an affine analytic chart is
  holomorphic.

## References

* W. Fulton, *Introduction to Toric Varieties*, §§1.4 and 2.1.
* D. Cox, J. Little and H. Schenck, *Toric Varieties*, §§3.1 and 3.4.
-/

public section

open CategoryTheory Set Topology
open scoped ContDiff Manifold

namespace TauCeti.Toric

variable {N V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V] {i : N →+ V}

/-- The data of a regular affine chart of a cone modelled on `ℂ ^ n`, for `n` the rank of the
lattice: an extending basis, a numbering of the rays, and a linear identification of the mixed
coordinate space `ℂ ^ k × ℂ ^ l` with `ℂ ^ n`. -/
private structure RankChartData (i : N →+ V) (σ : PointedCone ℝ V) where
  /-- The number of rays. -/
  k : ℕ
  /-- The number of complementary basis vectors. -/
  l : ℕ
  /-- An integral basis indexed by the rays and the complementary indices. -/
  B : Module.Basis (ToricRay σ ⊕ Fin l) ℤ N
  /-- The basis vector indexed by a ray is its primitive generator. -/
  hB : ∀ ρ, IsPrimitiveGenerator i ρ (B (Sum.inl ρ))
  /-- A numbering of the rays. -/
  κ : ToricRay σ ≃ Fin k
  /-- A linear identification of the mixed coordinate space with `ℂ ^ n`. -/
  L : ((Fin k → ℂ) × (Fin l → ℂ)) ≃L[ℂ] (Fin (Module.finrank ℤ N) → ℂ)

/-- Every regular cone has a regular affine chart modelled on `ℂ ^ n`: the ray coordinates and the
complementary coordinates of an extending basis are `n` coordinates in total. -/
private theorem nonempty_rankChartData {σ : PointedCone ℝ V} (hσ : IsRegularCone i σ) :
    Nonempty (RankChartData i σ) := by
  obtain ⟨l, B, hB⟩ := hσ.exists_basis_sum
  have : Finite (ToricRay σ) := ToricRay.finite_of_fg hσ.fg
  have hn : Nat.card (ToricRay σ) + l = Module.finrank ℤ N := by
    rw [Module.finrank_eq_nat_card_basis B, Nat.card_sum, Nat.card_eq_fintype_card (α := Fin l),
      Fintype.card_fin]
  let e : Fin (Nat.card (ToricRay σ)) ⊕ Fin l ≃ Fin (Module.finrank ℤ N) :=
    finSumFinEquiv.trans (finCongr hn)
  exact ⟨⟨_, l, B, hB, Finite.equivFin _,
    ((LinearEquiv.sumArrowLequivProdArrow _ _ ℂ ℂ).symm.trans
      (LinearEquiv.funCongrLeft ℂ ℂ e.symm)).toContinuousLinearEquiv⟩⟩

namespace Fan

universe u

variable {N V : Type u} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} (Φ : Fan i) (hΦ : Φ.IsRegular)

/-- A chosen regular affine chart of each cone of a regular fan, modelled on `ℂ ^ n`. -/
private noncomputable def chartData (σ : Φ.cones) : RankChartData i σ.1 :=
  Classical.choice (nonempty_rankChartData ((isRegular_iff.mp hΦ) σ.1 σ.2))

/-- The chosen chart of the affine analytic chart of a cone, in `ℂ ^ n`. -/
private noncomputable def rankChart (σ : Φ.cones) :
    (Φ.analyticGlueData hΦ).U σ → (Fin (Module.finrank ℤ N) → ℂ) :=
  fun x ↦ (Φ.chartData hΦ σ).L (coneChartAmbient Φ.lattice
    ((isRegular_iff.mp hΦ) σ.1 σ.2).toIsToricCone (Φ.chartData hΦ σ).hB (Φ.chartData hΦ σ).κ x)

/-- The chosen chart is an open embedding into `ℂ ^ n`. -/
private theorem isOpenEmbedding_rankChart (σ : Φ.cones) :
    IsOpenEmbedding (Φ.rankChart hΦ σ) :=
  (Φ.chartData hΦ σ).L.toHomeomorph.isOpenEmbedding.comp
    (isOpenEmbedding_coneChartAmbient Φ.lattice _ _ _
      (analyticChartGenerators Φ σ ((isRegular_iff.mp hΦ) σ.1 σ.2)).2)

/-- An affine analytic chart is nonempty. -/
private instance nonempty_piece (σ : Φ.cones) : Nonempty ((Φ.analyticGlueData hΦ).U σ) :=
  inferInstanceAs (Nonempty (AffineSemigroupComplexPoint (dualSemigroup Φ.lattice σ.1)))

/-- The charted-space structure on an affine analytic chart given by its chosen chart. -/
@[instance_reducible]
private noncomputable def pieceChartedSpace (σ : Φ.cones) :
    ChartedSpace (Fin (Module.finrank ℤ N) → ℂ) ((Φ.analyticGlueData hΦ).U σ) :=
  (Φ.isOpenEmbedding_rankChart hΦ σ).singletonChartedSpace

attribute [local instance] pieceChartedSpace

/-- An affine analytic chart, with its chosen structure, is a complex manifold. -/
private theorem isManifold_piece (σ : Φ.cones) (n : ℕ∞ω) :
    IsManifold 𝓘(ℂ, Fin (Module.finrank ℤ N) → ℂ) n ((Φ.analyticGlueData hΦ).U σ) :=
  (Φ.isOpenEmbedding_rankChart hΦ σ).isManifold_singleton

attribute [local instance] isManifold_piece

/-! The same structures, indexed by the index type of the gluing data. Instance search does not
identify this index type with `Φ.cones`, so the gluing theorems need these forms. -/

private instance nonempty_piece' (j : (Φ.analyticGlueData hΦ).J) :
    Nonempty ((Φ.analyticGlueData hΦ).U j) :=
  Φ.nonempty_piece hΦ j

@[instance_reducible]
private noncomputable def pieceChartedSpace' (j : (Φ.analyticGlueData hΦ).J) :
    ChartedSpace (Fin (Module.finrank ℤ N) → ℂ) ((Φ.analyticGlueData hΦ).U j) :=
  Φ.pieceChartedSpace hΦ j

attribute [local instance] pieceChartedSpace'

private theorem isManifold_piece' (j : (Φ.analyticGlueData hΦ).J) (n : ℕ∞ω) :
    IsManifold 𝓘(ℂ, Fin (Module.finrank ℤ N) → ℂ) n ((Φ.analyticGlueData hΦ).U j) :=
  Φ.isManifold_piece hΦ j n

attribute [local instance] isManifold_piece'

/-- A point of the affine analytic chart of a cone, viewed as a complex point of its affine toric
scheme. -/
private def toPoint (σ : Φ.cones) :
    (Φ.analyticGlueData hΦ).U σ → AffineSemigroupComplexPoint (dualSemigroup Φ.lattice σ.1) :=
  id

/-- A complex point of the affine toric scheme of a cone, viewed as a point of its affine analytic
chart. -/
private def ofPoint (σ : Φ.cones) :
    AffineSemigroupComplexPoint (dualSemigroup Φ.lattice σ.1) → (Φ.analyticGlueData hΦ).U σ :=
  id

/-- The identity from the chosen structure on an affine analytic chart to the regular cone
structure of the chosen chart data is holomorphic. -/
private theorem contMDiff_toCone (σ : Φ.cones) (n : ℕ∞ω) :
    let hσ := (isRegular_iff.mp hΦ) σ.1 σ.2
    let D := Φ.chartData hΦ σ
    let _ := affinePointTopology (analyticChartGenerators Φ σ hσ).2
    let _ := coneChartedSpace Φ.lattice hσ.toIsToricCone D.hB D.κ
      (analyticChartGenerators Φ σ hσ).2
    ContMDiff 𝓘(ℂ, Fin (Module.finrank ℤ N) → ℂ) 𝓘(ℂ, (Fin D.k → ℂ) × (Fin D.l → ℂ)) n
      (Φ.toPoint hΦ σ) := by
  intro hσ D _ _
  refine (contMDiff_coneChartAmbient_comp_iff Φ.lattice hσ.toIsToricCone D.hB D.κ _).1 ?_
  refine (((D.L.symm : _ →L[ℂ] _).contMDiff (n := n)).comp
    (contMDiff_isOpenEmbedding (Φ.isOpenEmbedding_rankChart hΦ σ))).congr fun x ↦ ?_
  simp only [Function.comp_apply, rankChart, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.symm_apply_apply, D]
  -- `toPoint` is the identity.
  rfl

/-- The identity from the regular cone structure of the chosen chart data to the chosen structure
on an affine analytic chart is holomorphic. -/
private theorem contMDiff_ofCone (σ : Φ.cones) (n : ℕ∞ω) :
    let hσ := (isRegular_iff.mp hΦ) σ.1 σ.2
    let D := Φ.chartData hΦ σ
    let _ := affinePointTopology (analyticChartGenerators Φ σ hσ).2
    let _ := coneChartedSpace Φ.lattice hσ.toIsToricCone D.hB D.κ
      (analyticChartGenerators Φ σ hσ).2
    ContMDiff 𝓘(ℂ, (Fin D.k → ℂ) × (Fin D.l → ℂ)) 𝓘(ℂ, Fin (Module.finrank ℤ N) → ℂ) n
      (Φ.ofPoint hΦ σ) := by
  intro hσ D _ _
  refine ContMDiff.of_comp_isOpenEmbedding (Φ.isOpenEmbedding_rankChart hΦ σ) ?_
  -- The chosen chart is `D.L` after the ambient cone chart, and `ofPoint` is the identity.
  exact (((D.L : _ →L[ℂ] _).contMDiff (n := n)).comp
    (contMDiff_coneChartAmbient Φ.lattice hσ.toIsToricCone D.hB D.κ _ n)).congr fun x ↦ rfl

/-- A map into an affine analytic chart, with its chosen structure, is holomorphic on a set exactly
when its value on every monomial is. -/
private theorem contMDiffOn_piece_iff (σ : Φ.cones) {E' H' M : Type*} [NormedAddCommGroup E']
    [NormedSpace ℂ E'] [TopologicalSpace H'] {I : ModelWithCorners ℂ E' H'} [TopologicalSpace M]
    [ChartedSpace H' M] {f : M → (Φ.analyticGlueData hΦ).U σ} {t : Set M} {n : ℕ∞ω} :
    ContMDiffOn I 𝓘(ℂ, Fin (Module.finrank ℤ N) → ℂ) n f t ↔
      ∀ m : dualSemigroup Φ.lattice σ.1, ContMDiffOn I 𝓘(ℂ, ℂ) n
        (fun x ↦ Φ.toPoint hΦ σ (f x) (MonoidAlgebra.single (Multiplicative.ofAdd m) 1)) t := by
  have hσ := (isRegular_iff.mp hΦ) σ.1 σ.2
  let D := Φ.chartData hΦ σ
  let _ := affinePointTopology (analyticChartGenerators Φ σ hσ).2
  let _ := coneChartedSpace Φ.lattice hσ.toIsToricCone D.hB D.κ (analyticChartGenerators Φ σ hσ).2
  have hc := contMDiffOn_iff_forall_contMDiffOn_apply_single Φ.lattice hσ.toIsToricCone D.hB D.κ
    (analyticChartGenerators Φ σ hσ).2 (I := I) (t := t) (n := n)
    (f := Φ.toPoint hΦ σ ∘ f)
  exact ⟨fun hf ↦ hc.1 ((Φ.contMDiff_toCone hΦ σ n).comp_contMDiffOn hf),
    fun hf ↦ (Φ.contMDiff_ofCone hΦ σ n).comp_contMDiffOn (hc.2 hf)⟩

/-- A map of affine analytic charts along a face inclusion, as a map of pieces of the gluing
data. -/
private noncomputable def pieceMap {τ σ : Φ.cones} (f : τ ⟶ σ) :
    (Φ.analyticGlueData hΦ).U τ → (Φ.analyticGlueData hΦ).U σ :=
  (Φ.analyticAffineChartDiagram hΦ).map f

/-- A map of affine analytic charts along a face inclusion is an open embedding. -/
private theorem isOpenEmbedding_pieceMap {τ σ : Φ.cones} (f : τ ⟶ σ) :
    IsOpenEmbedding (Φ.pieceMap hΦ f) :=
  Φ.isOpenEmbedding_analyticAffineChartDiagram_map hΦ f

/-- A map of affine analytic charts along a face inclusion restricts complex points. -/
private theorem toPoint_pieceMap {τ σ : Φ.cones} (f : τ ⟶ σ) (x : (Φ.analyticGlueData hΦ).U τ) :
    Φ.toPoint hΦ σ (Φ.pieceMap hΦ f x) =
      faceAffinePointMap Φ.lattice (Φ.isFaceOf_of_le σ.2 τ.2 (leOfHom f)) (Φ.toPoint hΦ τ x) :=
  Φ.analyticFaceMap_apply _ _ f x

/-- The gluing of two pieces is compatible with a map along a face inclusion. -/
private theorem ι_pieceMap {τ σ : Φ.cones} (f : τ ⟶ σ) (x : (Φ.analyticGlueData hΦ).U τ) :
    (Φ.analyticGlueData hΦ).ι σ (Φ.pieceMap hΦ f x) = (Φ.analyticGlueData hΦ).ι τ x := by
  rw [← analyticAffineChartι_def, ← analyticAffineChartι_def]
  exact ConcreteCategory.congr_hom
    (Φ.analyticAffineChartDiagram_map_comp_analyticAffineChartι hΦ f) x

/-- A map of affine analytic charts along a face inclusion is holomorphic. -/
private theorem contMDiff_pieceMap {τ σ : Φ.cones} (f : τ ⟶ σ) (n : ℕ∞ω) :
    ContMDiff 𝓘(ℂ, Fin (Module.finrank ℤ N) → ℂ) 𝓘(ℂ, Fin (Module.finrank ℤ N) → ℂ) n
      (Φ.pieceMap hΦ f) := by
  rw [← contMDiffOn_univ, contMDiffOn_piece_iff]
  intro m
  refine ((Φ.contMDiffOn_piece_iff hΦ τ (f := id) (t := univ)).1 contMDiffOn_id
    ⟨m, dualSemigroup_anti Φ.lattice (leOfHom f) m.2⟩).congr fun x _ ↦ ?_
  rw [toPoint_pieceMap, faceAffinePointMap_apply_single]
  -- `toPoint` is the identity.
  rfl

/-- The inverse of a map of affine analytic charts along a face inclusion is holomorphic on its
image. -/
private theorem contMDiffOn_pieceMap_symm {τ σ : Φ.cones} (f : τ ⟶ σ) (n : ℕ∞ω) :
    ContMDiffOn 𝓘(ℂ, Fin (Module.finrank ℤ N) → ℂ) 𝓘(ℂ, Fin (Module.finrank ℤ N) → ℂ) n
      ((Φ.isOpenEmbedding_pieceMap hΦ f).toOpenPartialHomeomorph _).symm
      (range (Φ.pieceMap hΦ f)) := by
  have hσ := (isRegular_iff.mp hΦ) σ.1 σ.2
  have hτ := (isRegular_iff.mp hΦ) τ.1 τ.2
  have hτσ := Φ.isFaceOf_of_le σ.2 τ.2 (leOfHom f)
  let Dσ := Φ.chartData hΦ σ
  let Dτ := Φ.chartData hΦ τ
  let gσ := (analyticChartGenerators Φ σ hσ).2
  let gτ := (analyticChartGenerators Φ τ hτ).2
  let _ := affinePointTopology gσ
  let _ := affinePointTopology gτ
  let _ := coneChartedSpace Φ.lattice hσ.toIsToricCone Dσ.hB Dσ.κ gσ
  let _ := coneChartedSpace Φ.lattice hτ.toIsToricCone Dτ.hB Dτ.κ gτ
  set e := (Φ.isOpenEmbedding_pieceMap hΦ f).toOpenPartialHomeomorph _
  refine (Φ.contMDiffOn_piece_iff hΦ τ).2 ?_
  refine (contMDiffOn_iff_forall_contMDiffOn_apply_single Φ.lattice hτ.toIsToricCone Dτ.hB Dτ.κ gτ
    (f := Φ.toPoint hΦ τ ∘ e.symm)).1 ?_
  refine (IsRegularCone.contMDiffOn_faceAffinePointMap_comp_iff Φ.lattice hσ hτσ Dσ.hB Dσ.κ gσ
    Dτ.hB Dτ.κ gτ (f := Φ.toPoint hΦ τ ∘ e.symm)).1 ?_
  refine (Φ.contMDiff_toCone hΦ σ n).contMDiffOn.congr fun w hw ↦ ?_
  rw [Function.comp_apply, Function.comp_apply, ← toPoint_pieceMap,
    (Φ.isOpenEmbedding_pieceMap hΦ f).toOpenPartialHomeomorph_right_inv _ hw]

/-- Two pieces of the gluing data are glued along holomorphic maps. -/
private theorem exists_contMDiffAt_transition (σ τ : Φ.cones) (x : (Φ.analyticGlueData hΦ).U σ)
    (y : (Φ.analyticGlueData hΦ).U τ)
    (h : (Φ.analyticGlueData hΦ).ι σ x = (Φ.analyticGlueData hΦ).ι τ y) (n : ℕ∞ω) :
    ∃ T : (Φ.analyticGlueData hΦ).U σ → (Φ.analyticGlueData hΦ).U τ,
      ContMDiffAt 𝓘(ℂ, Fin (Module.finrank ℤ N) → ℂ) 𝓘(ℂ, Fin (Module.finrank ℤ N) → ℂ) n T x ∧
        (Φ.analyticGlueData hΦ).ι τ ∘ T =ᶠ[𝓝 x] (Φ.analyticGlueData hΦ).ι σ := by
  rw [← analyticAffineChartι_def, ← analyticAffineChartι_def] at h
  obtain ⟨z, rfl, rfl⟩ := (Φ.analyticAffineChartι_eq_analyticAffineChartι_iff hΦ x y).1 h
  let l : σ ⊓ τ ⟶ σ := homOfLE inf_le_left
  let r : σ ⊓ τ ⟶ τ := homOfLE inf_le_right
  have hl := Φ.isOpenEmbedding_pieceMap hΦ l
  let e := hl.toOpenPartialHomeomorph _
  have hleft : ∀ v, e.symm (Φ.pieceMap hΦ l v) = v := fun v ↦
    hl.toOpenPartialHomeomorph_left_inv _
  have hz : Φ.analyticOverlapLeft hΦ σ τ z = Φ.pieceMap hΦ l z := by
    rw [analyticOverlapLeft_def]
    -- `pieceMap` is the map of the chart diagram.
    rfl
  have hrange : range (Φ.pieceMap hΦ l) ∈ 𝓝 (Φ.pieceMap hΦ l z) :=
    hl.isOpen_range.mem_nhds (mem_range_self z)
  refine ⟨Φ.pieceMap hΦ r ∘ e.symm, ?_, ?_⟩
  · rw [hz]
    exact (Φ.contMDiff_pieceMap hΦ r n).contMDiffAt.comp _
      ((Φ.contMDiffOn_pieceMap_symm hΦ l n).contMDiffAt hrange)
  · rw [hz]
    filter_upwards [hrange] with w hw
    obtain ⟨v, rfl⟩ := hw
    exact (congrArg (fun u ↦ (Φ.analyticGlueData hΦ).ι τ (Φ.pieceMap hΦ r u)) (hleft v)).trans
      ((Φ.ι_pieceMap hΦ r v).trans (Φ.ι_pieceMap hΦ l v).symm)

/-! ### The complex manifold -/

/-- The complex atlas of the analytic realization of a regular fan, modelled on `ℂ ^ n` for `n` the
rank of the lattice. Its charts are regular affine charts of the cones, transported along the chart
inclusions. -/
@[instance_reducible]
noncomputable def analyticChartedSpace :
    ChartedSpace (Fin (Module.finrank ℤ N) → ℂ) (Φ.analyticRealization hΦ) :=
  chartedSpaceOfIsOpenEmbedding (J := (Φ.analyticGlueData hΦ).J)
    (U := fun σ ↦ (Φ.analyticGlueData hΦ).U σ) (M := Φ.analyticRealization hΦ)
    (φ := fun σ ↦ ⇑((Φ.analyticGlueData hΦ).ι σ)) (Φ.analyticGlueData hΦ).ι_isOpenEmbedding
    (Φ.analyticGlueData hΦ).ι_jointly_surjective

/-- The analytic realization of a regular fan is a complex manifold. -/
theorem isManifold_analyticRealization (n : ℕ∞ω) :
    letI := Φ.analyticChartedSpace hΦ
    IsManifold 𝓘(ℂ, Fin (Module.finrank ℤ N) → ℂ) n (Φ.analyticRealization hΦ) :=
  isManifold_chartedSpaceOfIsOpenEmbedding (J := (Φ.analyticGlueData hΦ).J)
    (U := fun σ ↦ (Φ.analyticGlueData hΦ).U σ) (M := Φ.analyticRealization hΦ)
    (φ := fun σ ↦ ⇑((Φ.analyticGlueData hΦ).ι σ)) _ _
    fun σ τ x y h ↦ Φ.exists_contMDiffAt_transition hΦ σ τ x y h n

/-- The inclusion of the affine analytic chart of a cone, with its chosen structure, as a
biholomorphism onto its image in the analytic realization. -/
private noncomputable def piecePartialDiffeomorph (σ : Φ.cones) (n : ℕ∞ω) :
    letI := Φ.analyticChartedSpace hΦ
    PartialDiffeomorph 𝓘(ℂ, Fin (Module.finrank ℤ N) → ℂ) 𝓘(ℂ, Fin (Module.finrank ℤ N) → ℂ)
      ((Φ.analyticGlueData hΦ).U σ) (Φ.analyticRealization hΦ) n :=
  partialDiffeomorphOfIsOpenEmbedding (J := (Φ.analyticGlueData hΦ).J)
    (U := fun σ ↦ (Φ.analyticGlueData hΦ).U σ) (M := Φ.analyticRealization hΦ)
    (φ := fun σ ↦ ⇑((Φ.analyticGlueData hΦ).ι σ)) _ _
    (fun σ τ x y h ↦ Φ.exists_contMDiffAt_transition hΦ σ τ x y h n) σ

private theorem piecePartialDiffeomorph_source (σ : Φ.cones) (n : ℕ∞ω) :
    (Φ.piecePartialDiffeomorph hΦ σ n).source = univ :=
  partialDiffeomorphOfIsOpenEmbedding_source _ _ _ _

private theorem piecePartialDiffeomorph_target (σ : Φ.cones) (n : ℕ∞ω) :
    (Φ.piecePartialDiffeomorph hΦ σ n).target = range (Φ.analyticAffineChartι hΦ σ) := by
  rw [analyticAffineChartι_def]
  exact partialDiffeomorphOfIsOpenEmbedding_target _ _ _ _

private theorem piecePartialDiffeomorph_apply (σ : Φ.cones) (n : ℕ∞ω)
    (x : (Φ.analyticGlueData hΦ).U σ) :
    Φ.piecePartialDiffeomorph hΦ σ n x = Φ.analyticAffineChartι hΦ σ x := by
  rw [analyticAffineChartι_def]
  exact congrFun (coe_partialDiffeomorphOfIsOpenEmbedding (J := (Φ.analyticGlueData hΦ).J)
    (U := fun σ ↦ (Φ.analyticGlueData hΦ).U σ) (M := Φ.analyticRealization hΦ)
    (φ := fun σ ↦ ⇑((Φ.analyticGlueData hΦ).ι σ)) _ _
    (fun σ τ x y h ↦ Φ.exists_contMDiffAt_transition hΦ σ τ x y h n) σ) x

section ChartInclusion

variable (σ : Φ.cones) {k l s : ℕ} {B : Module.Basis (ToricRay σ.1 ⊕ Fin l) ℤ N}
  (hB : ∀ ρ, IsPrimitiveGenerator i ρ (B (Sum.inl ρ))) (κ : ToricRay σ.1 ≃ Fin k)
  (g : AddGeneratingFamily (dualSemigroup Φ.lattice σ.1) s)

/-- The identity from the complex structure of an extending basis on the affine analytic chart of
a cone to its chosen structure is holomorphic. -/
private theorem contMDiff_ofPoint (n : ℕ∞ω) :
    let _ := affinePointTopology g
    let _ := coneChartedSpace Φ.lattice ((isRegular_iff.mp hΦ) σ.1 σ.2).toIsToricCone hB κ g
    ContMDiff 𝓘(ℂ, (Fin k → ℂ) × (Fin l → ℂ)) 𝓘(ℂ, Fin (Module.finrank ℤ N) → ℂ) n
      (Φ.ofPoint hΦ σ) := by
  intro _ _
  rw [← contMDiffOn_univ, contMDiffOn_piece_iff]
  exact fun m ↦ (contMDiff_apply_single Φ.lattice _ hB κ g m n).contMDiffOn

/-- The identity from the chosen structure on the affine analytic chart of a cone to the complex
structure of an extending basis is holomorphic. -/
private theorem contMDiff_toPoint (n : ℕ∞ω) :
    let _ := affinePointTopology g
    let _ := coneChartedSpace Φ.lattice ((isRegular_iff.mp hΦ) σ.1 σ.2).toIsToricCone hB κ g
    ContMDiff 𝓘(ℂ, Fin (Module.finrank ℤ N) → ℂ) 𝓘(ℂ, (Fin k → ℂ) × (Fin l → ℂ)) n
      (Φ.toPoint hΦ σ) := by
  intro _ _
  refine (contMDiff_iff_forall_contMDiff_apply_single Φ.lattice _ hB κ g).2 fun m ↦ ?_
  rw [← contMDiffOn_univ]
  exact (Φ.contMDiffOn_piece_iff hΦ σ (f := id)).1 contMDiffOn_id m

/-- The inclusion of the affine analytic chart of a cone into the analytic realization, as a
biholomorphism onto its open image. The chart carries the complex structure of any extending basis
of the cone. -/
noncomputable def analyticAffineChartPartialDiffeomorph (n : ℕ∞ω) :
    let _ := affinePointTopology g
    let _ := coneChartedSpace Φ.lattice ((isRegular_iff.mp hΦ) σ.1 σ.2).toIsToricCone hB κ g
    letI := Φ.analyticChartedSpace hΦ
    PartialDiffeomorph 𝓘(ℂ, (Fin k → ℂ) × (Fin l → ℂ)) 𝓘(ℂ, Fin (Module.finrank ℤ N) → ℂ)
      (AffineSemigroupComplexPoint (dualSemigroup Φ.lattice σ.1)) (Φ.analyticRealization hΦ) n :=
  let _ := affinePointTopology g
  let _ := coneChartedSpace Φ.lattice ((isRegular_iff.mp hΦ) σ.1 σ.2).toIsToricCone hB κ g
  letI := Φ.analyticChartedSpace hΦ
  { toPartialEquiv := (Φ.piecePartialDiffeomorph hΦ σ n).toPartialEquiv
    open_source := by
      rw [piecePartialDiffeomorph_source]
      exact isOpen_univ
    open_target := (Φ.piecePartialDiffeomorph hΦ σ n).open_target
    contMDiffOn_toFun := (Φ.piecePartialDiffeomorph hΦ σ n).contMDiffOn_toFun.comp
      (Φ.contMDiff_ofPoint hΦ σ hB κ g n).contMDiffOn fun _ _ ↦ by
        rw [piecePartialDiffeomorph_source]
        exact mem_univ _
    contMDiffOn_invFun := (Φ.contMDiff_toPoint hΦ σ hB κ g n).comp_contMDiffOn
      (Φ.piecePartialDiffeomorph hΦ σ n).contMDiffOn_invFun }

/-- The chart-inclusion biholomorphism is defined on the whole affine analytic chart. -/
@[simp]
theorem analyticAffineChartPartialDiffeomorph_source (n : ℕ∞ω) :
    (Φ.analyticAffineChartPartialDiffeomorph hΦ σ hB κ g n).source = univ :=
  Φ.piecePartialDiffeomorph_source hΦ σ n

/-- The target of the chart-inclusion biholomorphism is the image of the affine analytic chart. -/
@[simp]
theorem analyticAffineChartPartialDiffeomorph_target (n : ℕ∞ω) :
    (Φ.analyticAffineChartPartialDiffeomorph hΦ σ hB κ g n).target =
      range (Φ.analyticAffineChartι hΦ σ) :=
  Φ.piecePartialDiffeomorph_target hΦ σ n

/-- The chart-inclusion biholomorphism is the inclusion of the affine analytic chart. -/
@[simp]
theorem analyticAffineChartPartialDiffeomorph_apply (n : ℕ∞ω)
    (x : AffineSemigroupComplexPoint (dualSemigroup Φ.lattice σ.1)) :
    Φ.analyticAffineChartPartialDiffeomorph hΦ σ hB κ g n x = Φ.analyticAffineChartι hΦ σ x :=
  Φ.piecePartialDiffeomorph_apply hΦ σ n x

/-- The inclusion of the affine analytic chart of a cone into the analytic realization is
holomorphic, for the complex structure of any extending basis of the cone. -/
theorem contMDiff_analyticAffineChartι (n : ℕ∞ω) :
    let _ := affinePointTopology g
    let _ := coneChartedSpace Φ.lattice ((isRegular_iff.mp hΦ) σ.1 σ.2).toIsToricCone hB κ g
    letI := Φ.analyticChartedSpace hΦ
    ContMDiff 𝓘(ℂ, (Fin k → ℂ) × (Fin l → ℂ)) 𝓘(ℂ, Fin (Module.finrank ℤ N) → ℂ) n
      fun x : AffineSemigroupComplexPoint (dualSemigroup Φ.lattice σ.1) ↦
        Φ.analyticAffineChartι hΦ σ x := by
  intro _ _
  let _ := Φ.analyticChartedSpace hΦ
  have h := (Φ.analyticAffineChartPartialDiffeomorph hΦ σ hB κ g n).contMDiffOn_toFun
  rw [analyticAffineChartPartialDiffeomorph_source, contMDiffOn_univ] at h
  exact h.congr fun x ↦ (Φ.analyticAffineChartPartialDiffeomorph_apply hΦ σ hB κ g n x).symm

end ChartInclusion

end Fan

end TauCeti.Toric
