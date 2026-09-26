/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.Topology.MetricSpace.HausdorffDimension
public import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Lipschitz-parametrizable sets

A set is Lipschitz parametrizable in dimension `d` when finitely many Lipschitz images of the
unit `d`-cube cover it.  This is the boundary regularity condition used in lattice-point counting:
a codimension-one parametrization gives quantitative control on how many lattice cells can meet a
boundary.

This file supplies the elementary API needed to assemble parametrizations: the property is
monotone in the set, is preserved by Lipschitz images, by locally Lipschitz images, by products
and by finite unions, and holds for finite sets.
It also supplies the way in from smoothness: a map that is `C¹` on the compact cube is Lipschitz
there, so the image of a cube of the right dimension is a single chart.
It also records the basic dimension consequence.  A Lipschitz-parametrizable subset of a
finite-dimensional real normed space has additive Haar measure zero whenever the parameter
dimension is strictly smaller than the ambient dimension.  The proof compares additive Haar
measure with Hausdorff measure and uses the fact that Lipschitz maps do not increase Hausdorff
dimension.

It also records the quantitative form of a single chart: cutting the unit `d`-cube into `m ^ d`
subcubes of side `1 / m` covers a Lipschitz image of it by `m ^ d` pieces of diameter `C / m`.
That is what turns a parametrization in a given dimension into a count.

## Main declarations

* `TauCeti.IsLipschitzParametrizable`: finite Lipschitz parametrizability by a
  unit cube;
* `TauCeti.isLipschitzParametrizable_iff`: the finite-chart characterization of the predicate;
* `TauCeti.IsLipschitzParametrizable.union`: closure under binary unions;
* `TauCeti.IsLipschitzParametrizable.image`: closure under Lipschitz images;
* `TauCeti.IsLipschitzParametrizable.image_of_locallyLipschitz`: closure under locally Lipschitz
  images, which is what a chart-by-chart compactness argument buys over `image`;
* `TauCeti.IsLipschitzParametrizable.iUnion`: closure under unions over a finite index type;
* `TauCeti.IsLipschitzParametrizable.prod`: a product is parametrized in the sum of the
  dimensions;
* `TauCeti.IsLipschitzParametrizable.image_unitCube_of_contDiffOn`: a unit cube's image under a
  map that is `C¹` on it is parametrized by that cube;
* `TauCeti.IsLipschitzParametrizable.of_isBounded`: a bounded subset of a finite-dimensional real
  normed space is parametrized in the ambient dimension;
* `TauCeti.IsLipschitzParametrizable.of_isBounded_of_subset_ker`: a bounded subset of a hyperplane
  is parametrized in codimension one;
* `TauCeti.IsLipschitzParametrizable.measure_zero`: a parametrized set has
  additive Haar measure zero below the ambient dimension;
* `LipschitzOnWith.exists_cover_image_unitCube`: a Lipschitz image of the unit `d`-cube is
  covered by `m ^ d` pieces of arbitrarily small diameter.

## References

* S. Lang, *Algebraic Number Theory*, Chapter VI, Section 2, which the definition and its use in
  the lattice-point estimate follow.
* C. Birkbeck, [*AINTLIB*](https://github.com/CBirkbeck/AINTLIB) at commit
  `db14b34cc5e3d79603e67c205dfa86b7b989000c` (Apache-2.0),
  `projects/Chebotarev/CebotarevDensity/ForMathlib/IdealCongruenceCount.lean`, whose
  `exists_lipschitz_cube_cover_hyperplane_slab` is the concrete precursor of
  `of_isBounded` and `of_isBounded_of_subset_ker`: it covers a bounded slab of a coordinate
  hyperplane of `ι → ℝ` by a single chart, through the same affine rescaling
  `c ↦ 2 * M * c - M` of the unit cube onto the box `[-M, M]`. The two lemmas here say the
  same thing without reference to coordinates, for any finite-dimensional real normed space
  and any hyperplane in it.
-/

public section

open MeasureTheory Set

namespace TauCeti

/-- A set is Lipschitz parametrizable in dimension `d` if it is covered by finitely many
Lipschitz images of the unit cube in `Fin d → ℝ`. -/
def IsLipschitzParametrizable {E : Type*} [PseudoEMetricSpace E] (d : ℕ) (S : Set E) : Prop :=
  ∃ (n : ℕ) (C : NNReal) (f : Fin n → (Fin d → ℝ) → E),
    (∀ i, LipschitzOnWith C (f i) (Icc (0 : Fin d → ℝ) 1)) ∧
      S ⊆ ⋃ i, f i '' Icc (0 : Fin d → ℝ) 1

/-- A set is Lipschitz parametrizable in dimension `d` if and only if finitely many unit-cube
charts, all Lipschitz with a common constant on the unit cube, cover it. -/
theorem isLipschitzParametrizable_iff {E : Type*} [PseudoEMetricSpace E] {d : ℕ} {S : Set E} :
    IsLipschitzParametrizable d S ↔
      ∃ (n : ℕ) (C : NNReal) (f : Fin n → (Fin d → ℝ) → E),
        (∀ i, LipschitzOnWith C (f i) (Icc (0 : Fin d → ℝ) 1)) ∧
          S ⊆ ⋃ i, f i '' Icc (0 : Fin d → ℝ) 1 :=
  Iff.rfl

namespace IsLipschitzParametrizable

variable {E F : Type*} [PseudoEMetricSpace E] [PseudoEMetricSpace F]
  {d : ℕ} {S T : Set E}

/-- Every subset of a Lipschitz-parametrizable set is Lipschitz parametrizable with the same
charts. -/
theorem mono (hT : IsLipschitzParametrizable d T) (hST : S ⊆ T) :
    IsLipschitzParametrizable d S := by
  obtain ⟨n, C, f, hf, hT⟩ := isLipschitzParametrizable_iff.1 hT
  exact isLipschitzParametrizable_iff.2 ⟨n, C, f, hf, hST.trans hT⟩

/-- The empty set is Lipschitz parametrizable in every dimension. -/
@[simp]
theorem empty : IsLipschitzParametrizable d (∅ : Set E) := by
  exact isLipschitzParametrizable_iff.2 ⟨0, 0, Fin.elim0, fun i ↦ i.elim0, Set.empty_subset _⟩

/-- A singleton is Lipschitz parametrizable in every dimension. -/
@[simp]
theorem singleton (x : E) : IsLipschitzParametrizable d ({x} : Set E) := by
  refine isLipschitzParametrizable_iff.2 ⟨1, 0, fun (_ : Fin 1) (_ : Fin d → ℝ) ↦ x,
    fun _ ↦ (LipschitzWith.const (α := Fin d → ℝ) x).lipschitzOnWith, ?_⟩
  intro y hy
  have hyx : y = x := Set.mem_singleton_iff.mp hy
  subst y
  refine Set.mem_iUnion.2 ⟨0, ?_⟩
  exact ⟨0, by simp⟩

/-- The union of two Lipschitz-parametrizable sets in the same dimension is Lipschitz
parametrizable. -/
theorem union (hS : IsLipschitzParametrizable d S) (hT : IsLipschitzParametrizable d T) :
    IsLipschitzParametrizable d (S ∪ T) := by
  obtain ⟨m, C, f, hf, hSf⟩ := isLipschitzParametrizable_iff.1 hS
  obtain ⟨n, D, g, hg, hTg⟩ := isLipschitzParametrizable_iff.1 hT
  let e : Fin m ⊕ Fin n ≃ Fin (m + n) := finSumFinEquiv
  let charts : Fin (m + n) → (Fin d → ℝ) → E := fun i ↦
    Sum.elim f g (e.symm i)
  refine isLipschitzParametrizable_iff.2 ⟨m + n, max C D, charts, ?_, ?_⟩
  · intro i
    rcases h : e.symm i with j | j
    · simpa only [charts, h, Sum.elim_inl] using (hf j).weaken (le_max_left C D)
    · simpa only [charts, h, Sum.elim_inr] using (hg j).weaken (le_max_right C D)
  · rintro x (hx | hx)
    · obtain ⟨i, hi⟩ := Set.mem_iUnion.1 (hSf hx)
      refine Set.mem_iUnion.2 ⟨e (Sum.inl i), ?_⟩
      simpa only [charts, Equiv.symm_apply_apply, Sum.elim_inl] using hi
    · obtain ⟨i, hi⟩ := Set.mem_iUnion.1 (hTg hx)
      refine Set.mem_iUnion.2 ⟨e (Sum.inr i), ?_⟩
      simpa only [charts, Equiv.symm_apply_apply, Sum.elim_inr] using hi

/-- A finite union of sets parametrized in the same dimension is Lipschitz parametrizable. -/
theorem biUnion_finset {I : Type*} (s : Finset I) {A : I → Set E}
    (hA : ∀ i ∈ s, IsLipschitzParametrizable d (A i)) :
    IsLipschitzParametrizable d (⋃ i ∈ s, A i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.set_biUnion_insert]
      exact (hA i (Finset.mem_insert_self i s)).union
        (ih fun j hj ↦ hA j (Finset.mem_insert_of_mem hj))

/-- A union over a finite index type of sets parametrized in dimension `d` is Lipschitz
parametrizable in dimension `d`. -/
theorem iUnion {I : Type*} [Finite I] {A : I → Set E}
    (hA : ∀ i, IsLipschitzParametrizable d (A i)) :
    IsLipschitzParametrizable d (⋃ i, A i) := by
  classical
  cases nonempty_fintype I
  rw [← Set.biUnion_univ, ← Finset.coe_univ, Finset.set_biUnion_coe]
  exact biUnion_finset Finset.univ fun i _ ↦ hA i

/-- A product of parametrized sets is Lipschitz parametrizable in the sum of the dimensions. -/
theorem prod {G : Type*} [PseudoEMetricSpace G] {e : ℕ} {T : Set G}
    (hS : IsLipschitzParametrizable d S) (hT : IsLipschitzParametrizable e T) :
    IsLipschitzParametrizable (d + e) (S ×ˢ T) := by
  obtain ⟨m, C, f, hf, hSf⟩ := isLipschitzParametrizable_iff.1 hS
  obtain ⟨n, D, g, hg, hTg⟩ := isLipschitzParametrizable_iff.1 hT
  -- Reading off a block of coordinates is `1`-Lipschitz and carries the cube into the cube.
  have hlip : ∀ {a : ℕ} (σ : Fin a → Fin (d + e)),
      LipschitzOnWith 1 (fun (x : Fin (d + e) → ℝ) k ↦ x (σ k)) (Icc 0 1) := fun _ ↦
    (LipschitzWith.of_edist_le fun x y ↦
      edist_pi_le_iff.2 fun k ↦ edist_le_pi_edist x y _).lipschitzOnWith
  have hmaps : ∀ {a : ℕ} (σ : Fin a → Fin (d + e)),
      Set.MapsTo (fun (x : Fin (d + e) → ℝ) k ↦ x (σ k)) (Icc 0 1) (Icc 0 1) :=
    fun _ _ hz ↦ ⟨fun _ ↦ hz.1 _, fun _ ↦ hz.2 _⟩
  refine isLipschitzParametrizable_iff.2 ⟨m * n, max C D, fun p x ↦
    (f (finProdFinEquiv.symm p).1 fun k ↦ x (Fin.castAdd e k),
      g (finProdFinEquiv.symm p).2 fun k ↦ x (Fin.natAdd d k)),
    fun p ↦ LipschitzOnWith.prodMk ?_ ?_, ?_⟩
  · simpa [Function.comp_def] using (hf _).comp (hlip _) (hmaps _)
  · simpa [Function.comp_def] using (hg _).comp (hlip _) (hmaps _)
  · rintro ⟨u, v⟩ ⟨hu, hv⟩
    obtain ⟨i, a, ha, rfl⟩ := Set.mem_iUnion.1 (hSf hu)
    obtain ⟨j, b, hb, rfl⟩ := Set.mem_iUnion.1 (hTg hv)
    -- `Fin.append a b` is the cube point whose two blocks parametrize `u` and `v`.
    refine Set.mem_iUnion.2 ⟨finProdFinEquiv (i, j), Fin.append a b, ⟨?_, ?_⟩, by simp⟩
    · exact Fin.addCases (fun l ↦ by simpa using ha.1 l) fun l ↦ by simpa using hb.1 l
    · exact Fin.addCases (fun l ↦ by simpa using ha.2 l) fun l ↦ by simpa using hb.2 l

/-- A finite set is Lipschitz parametrizable in every dimension. -/
theorem finite (hS : S.Finite) : IsLipschitzParametrizable d S := by
  induction S, hS using Set.Finite.induction_on with
  | empty => exact empty
  | @insert x S hx hS ih =>
      rw [insert_eq, singleton_union]
      exact (singleton (d := d) x).union ih

/-- The image of a Lipschitz-parametrizable set under a Lipschitz map is Lipschitz
parametrizable. -/
theorem image {g : E → F} {K : NNReal} (hg : LipschitzWith K g)
    (hS : IsLipschitzParametrizable d S) : IsLipschitzParametrizable d (g '' S) := by
  obtain ⟨n, C, f, hf, hSf⟩ := isLipschitzParametrizable_iff.1 hS
  refine isLipschitzParametrizable_iff.2
    ⟨n, K * C, fun i ↦ g ∘ f i, fun i ↦ hg.comp_lipschitzOnWith (hf i), ?_⟩
  rintro y ⟨x, hx, rfl⟩
  obtain ⟨i, z, hz, rfl⟩ := Set.mem_iUnion.1 (hSf hx)
  exact Set.mem_iUnion.2 ⟨i, z, hz, rfl⟩

/-- The image of the unit cube of `ι → ℝ` under a map that is `C¹` on that cube is Lipschitz
parametrizable in dimension `#ι`. The cube is indexed by an arbitrary finite type `ι` of
cardinality `d`, not by `Fin d` itself. -/
theorem image_unitCube_of_contDiffOn {ι G : Type*} [Fintype ι] [NormedAddCommGroup G]
    [NormedSpace ℝ G] {d : ℕ} (hd : Fintype.card ι = d) {f : (ι → ℝ) → G}
    (hf : ContDiffOn ℝ 1 f (Icc 0 1)) :
    IsLipschitzParametrizable d (f '' Icc (0 : ι → ℝ) 1) := by
  set e := Fintype.equivFinOfCardEq hd
  set T : (Fin d → ℝ) → (ι → ℝ) := fun x i ↦ x (e i)
  have hmaps : Set.MapsTo T (Icc (0 : Fin d → ℝ) 1) (Icc (0 : ι → ℝ) 1) :=
    fun y hy ↦ ⟨fun i ↦ hy.1 _, fun i ↦ hy.2 _⟩
  have hdiff : ContDiffOn ℝ 1 (f ∘ T) (Icc (0 : Fin d → ℝ) 1) :=
    ContDiffOn.comp hf (ContDiff.contDiffOn (contDiff_pi.mpr fun i ↦ contDiff_apply ℝ ℝ (e i)))
      hmaps
  -- A `C¹` map is Lipschitz on the compact convex cube, so `f ∘ T` is a single chart.
  obtain ⟨C, hC⟩ :=
    ContDiffOn.exists_lipschitzOnWith hdiff one_ne_zero (convex_Icc _ _) isCompact_Icc
  refine isLipschitzParametrizable_iff.2 ⟨1, C, fun _ ↦ f ∘ T, fun _ ↦ hC,
    Set.subset_iUnion_of_subset 0 ?_⟩
  -- Reindexing by `e` maps the `Fin d`-cube onto the `ι`-cube, so that chart covers the image.
  rw [Set.image_comp]
  exact Set.image_mono fun y hy ↦ ⟨fun j ↦ y (e.symm j),
    ⟨fun j ↦ hy.1 _, fun j ↦ hy.2 _⟩, funext fun i ↦ congrArg y (e.symm_apply_apply i)⟩

/-- **A bounded subset of a finite-dimensional real normed space is Lipschitz parametrizable in
the ambient dimension.** Linear coordinates carry the set into a box, and a box is the image of
the unit cube under an affine — hence `C¹` — map, so one chart suffices.

This is the trivial bound on the dimension: it is useful only for pieces of a set that are
genuinely lower dimensional for another reason, such as a bounded piece of a hyperplane. -/
theorem of_isBounded {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {S : Set E} (hS : Bornology.IsBounded S) :
    IsLipschitzParametrizable (Module.finrank ℝ E) S := by
  set n := Module.finrank ℝ E
  set e : E ≃L[ℝ] (Fin n → ℝ) :=
    ContinuousLinearEquiv.ofFinrankEq (Module.finrank_fin_fun ℝ).symm
  -- Coordinates carry `S` into the box `[-M, M] ^ n`, with `M ≥ 1` so that `2 * M ≠ 0`.
  obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.mp (e.lipschitzWith.isBounded_image hS)
  set M : ℝ := max R 1
  have hM0 : (0 : ℝ) < M := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hcd : ContDiff ℝ 1 fun t : Fin n → ℝ ↦ e.symm fun i ↦ 2 * M * t i - M := by fun_prop
  refine .mono (.image_unitCube_of_contDiffOn (Fintype.card_fin n) hcd.contDiffOn) fun x hx ↦ ?_
  have key : ∀ i, -M ≤ e x i ∧ e x i ≤ M := fun i ↦ abs_le.mp <| by
    rw [← Real.norm_eq_abs]
    exact (norm_le_pi_norm (e x) i).trans ((hR _ ⟨x, hx, rfl⟩).trans (le_max_left _ _))
  -- The cube point is the coordinate vector of `x`, rescaled from `[-M, M]` to `[0, 1]`.
  -- Cube membership is two pointwise inequalities: `Set.mem_Icc` splits the interval and the
  -- order on `Fin n → ℝ` is pointwise, so `Pi.zero_apply` / `Pi.one_apply` name the endpoints.
  refine ⟨fun i ↦ (e x i + M) / (2 * M), Set.mem_Icc.mpr ⟨fun i ↦ ?_, fun i ↦ ?_⟩, ?_⟩
  · rw [Pi.zero_apply]
    exact div_nonneg (by linarith [(key i).1]) (by linarith)
  · rw [Pi.one_apply]
    exact (div_le_one (by linarith)).2 (by linarith [(key i).2])
  · -- The parametrisation sends the cube point back through `e.symm`, so the image equation is an
    -- equation in `E`; `e.symm_apply_eq` moves it to `Fin n → ℝ`, where it is coordinatewise.
    rw [e.symm_apply_eq]
    funext i
    rw [mul_div_cancel₀ _ (by positivity : (2 * M : ℝ) ≠ 0), add_sub_cancel_right]

/-- **A bounded subset of a hyperplane is Lipschitz parametrizable in codimension one.** The
hyperplane is the kernel of a nonzero linear functional, a subspace of dimension
`finrank ℝ E - 1`; inside it the set is still bounded, because the inclusion is an isometry. -/
theorem of_isBounded_of_subset_ker {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {f : E →ₗ[ℝ] ℝ} (hf : f ≠ 0) {S : Set E} (hS : Bornology.IsBounded S)
    (hSf : S ⊆ LinearMap.ker f) : IsLipschitzParametrizable (Module.finrank ℝ E - 1) S := by
  -- Pull `S` back to the kernel, parametrize it there, and push it forward again: `S` is the
  -- image of its own preimage exactly because it lies in the kernel.
  have hiso : Isometry (Subtype.val : LinearMap.ker f → E) := isometry_subtype_coe
  have h := (of_isBounded (hiso.antilipschitzWith.isBounded_preimage hS)).image hiso.lipschitzWith
  rwa [Set.image_preimage_eq_of_subset (by rwa [Subtype.range_coe]),
    Nat.eq_sub_of_add_eq (Module.Dual.finrank_ker_add_one_of_ne_zero hf)] at h

/-- The image of a Lipschitz-parametrizable set under a locally Lipschitz map is Lipschitz
parametrizable. -/
theorem image_of_locallyLipschitz {E F : Type*} [PseudoMetricSpace E] [PseudoMetricSpace F] {d : ℕ}
    {S : Set E} {g : E → F} (hg : LocallyLipschitz g) (hS : IsLipschitzParametrizable d S) :
    IsLipschitzParametrizable d (g '' S) := by
  obtain ⟨n, C, f, hf, hSf⟩ := isLipschitzParametrizable_iff.1 hS
  -- Each chart has compact image, so `g` is Lipschitz on it with some constant `D i`.
  choose D hD using fun i ↦ hg.locallyLipschitzOn.exists_lipschitzOnWith_of_compact
    (isCompact_Icc.image_of_continuousOn (hf i).continuousOn)
  -- Finitely many charts, so the constants `D i * C` admit a common bound.
  refine isLipschitzParametrizable_iff.2 ⟨n, Finset.univ.sup fun i ↦ D i * C, fun i ↦ g ∘ f i,
    fun i ↦ ((hD i).comp (hf i) (Set.mapsTo_image _ _)).weaken
      (Finset.le_sup (f := fun i ↦ D i * C) (Finset.mem_univ i)), ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨i, z, hz, rfl⟩ := Set.mem_iUnion.1 (hSf hx)
  exact Set.mem_iUnion.2 ⟨i, z, hz, rfl⟩

/-- A set Lipschitz parametrized in dimension `d` has zero additive Haar measure in a
finite-dimensional real normed space of dimension strictly larger than `d`.

This statement is formulated for an arbitrary additive Haar measure, so it applies directly to
the volume normalization used by a lattice and is invariant under later linear coordinate
changes. -/
theorem measure_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure] {d : ℕ} {S : Set E}
    (hS : IsLipschitzParametrizable d S) (hd : d < Module.finrank ℝ E) : μ S = 0 := by
  obtain ⟨n, C, f, hf, hSf⟩ := isLipschitzParametrizable_iff.1 hS
  have hμ : μ ≪ μH[(Module.finrank ℝ E : ℝ)] :=
    Measure.absolutelyContinuous_isAddHaarMeasure μ _
  have hdim : dimH (Set.univ : Set (Fin d → ℝ)) = d := by
    rw [Real.dimH_univ_eq_finrank, Module.finrank_pi]
    simp only [Fintype.card_fin]
  apply measure_mono_null hSf
  apply measure_iUnion_null
  intro i
  apply measure_zero_of_dimH_lt (μ := μ) (d := (Module.finrank ℝ E : NNReal)) hμ
  calc
    dimH (f i '' Icc (0 : Fin d → ℝ) 1) ≤ dimH (Icc (0 : Fin d → ℝ) 1) :=
      (hf i).dimH_image_le
    _ ≤ dimH (Set.univ : Set (Fin d → ℝ)) := dimH_mono (Set.subset_univ _)
    _ = d := hdim
    _ < Module.finrank ℝ E := by exact_mod_cast hd

end IsLipschitzParametrizable

end TauCeti

namespace LipschitzOnWith

variable {E : Type*} [PseudoMetricSpace E]

/-- A map that is Lipschitz with constant `C` on the unit cube `Icc 0 1` of `Fin d → ℝ` carries
that cube into a union of `m ^ d` pieces — one for each subcube of side `1 / m` — each of
diameter at most `C / m`.

This is the quantitative content of a chart of a Lipschitz parametrization: cutting the cube
finely enough covers the image by a prescribed number of arbitrarily small pieces, which is what
bounds the number of lattice cells such an image can meet. -/
theorem exists_cover_image_unitCube {d : ℕ} {C : NNReal} {f : (Fin d → ℝ) → E}
    (hf : LipschitzOnWith C f (Icc 0 1)) {m : ℕ} (hm : 0 < m) :
    ∃ T : (Fin d → Fin m) → Set E,
      (f '' Icc (0 : Fin d → ℝ) 1 ⊆ ⋃ k, T k) ∧
        ∀ k, ∀ x ∈ T k, ∀ y ∈ T k, dist x y ≤ C / m := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  -- `Q k` is the subcube of side `1 / m` with lower corner `k / m`.
  set Q : (Fin d → Fin m) → Set (Fin d → ℝ) :=
    fun k ↦ {x | ∀ i, x i ∈ Icc (((k i : ℕ) : ℝ) / m) ((((k i : ℕ) : ℝ) + 1) / m)}
  have hQsub : ∀ k, Q k ⊆ Icc (0 : Fin d → ℝ) 1 := by
    intro k x hx
    simp only [Set.mem_Icc, Pi.le_def, Pi.zero_apply, Pi.one_apply]
    refine ⟨fun i ↦ le_trans (by positivity) (hx i).1, fun i ↦ (hx i).2.trans ?_⟩
    rw [div_le_one hmR]
    exact_mod_cast (Nat.succ_le_of_lt (k i).isLt : (k i : ℕ) + 1 ≤ m)
  have hQcov : Icc (0 : Fin d → ℝ) 1 ⊆ ⋃ k, Q k := by
    intro x hx
    simp only [Set.mem_Icc, Pi.le_def, Pi.zero_apply, Pi.one_apply] at hx
    -- The subcube containing `x` is indexed by the integer parts of the scaled coordinates,
    -- capped at `m - 1` so that the coordinate `1` lands in the last subcube.
    refine mem_iUnion.2 ⟨fun i ↦ ⟨min ⌊x i * m⌋₊ (m - 1),
      lt_of_le_of_lt (min_le_right _ _) (Nat.sub_lt hm Nat.one_pos)⟩, fun i ↦ ?_⟩
    -- Evaluate the index family just chosen at `i`.
    dsimp only
    have hx0 : 0 ≤ x i := hx.1 i
    have hx1 : x i ≤ 1 := hx.2 i
    have hfloor : ((min ⌊x i * m⌋₊ (m - 1) : ℕ) : ℝ) ≤ x i * m :=
      le_trans (by exact_mod_cast min_le_left ⌊x i * m⌋₊ (m - 1))
        (Nat.floor_le (by positivity))
    refine ⟨(div_le_iff₀ hmR).2 hfloor, (le_div_iff₀ hmR).2 ?_⟩
    rcases le_total ⌊x i * m⌋₊ (m - 1) with h | h
    · rw [min_eq_left h]
      exact (Nat.lt_floor_add_one _).le
    · rw [min_eq_right h, Nat.cast_sub hm, Nat.cast_one, sub_add_cancel]
      nlinarith
  have hQdist : ∀ k, ∀ x ∈ Q k, ∀ y ∈ Q k, dist x y ≤ 1 / m := by
    intro k x hx y hy
    refine (dist_pi_le_iff (by positivity)).2 fun i ↦ ?_
    refine (Real.dist_le_of_mem_Icc (hx i) (hy i)).trans_eq ?_
    ring
  refine ⟨fun k ↦ f '' Q k, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨k, hk⟩ := mem_iUnion.1 (hQcov hx)
    exact mem_iUnion.2 ⟨k, x, hk, rfl⟩
  · rintro k _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    calc dist (f x) (f y) ≤ (C : ℝ) * dist x y :=
          hf.dist_le_mul x (hQsub k hx) y (hQsub k hy)
      _ ≤ (C : ℝ) * (1 / m) := by gcongr; exact hQdist k x hx y hy
      _ = (C : ℝ) / m := by ring

end LipschitzOnWith
