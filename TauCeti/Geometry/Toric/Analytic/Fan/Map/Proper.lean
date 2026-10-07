/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Convex.Cone.ErrorBound
public import TauCeti.Geometry.Toric.Analytic.Fan.Compact
public import TauCeti.Geometry.Toric.Analytic.Fan.Map.Orbit
public import Mathlib.Topology.Maps.Proper.CompactlyGenerated

/-!
# The cone-by-cone properness criterion for analytic toric maps

Let `f : Φ → Ψ` be a morphism of regular fans with real-linear map `f_ℝ`, and let `τ` be a cone
of `Ψ`. The source cones `σ` with `f_ℝ σ ⊆ τ` are exactly those whose charts the analytic map
sends into the chart of `τ`, and their union always lies in the inverse image `f_ℝ⁻¹ τ`. The
support condition for `τ` asks that the two sets be equal. This file proves that, for a nonempty
source fan, the analytic map is proper exactly when the support condition holds for every target
cone.

For the necessity of the support condition, the proof follows the one for compact realizations
(`TauCeti.Toric.Fan.isComplete_of_compactSpace_analyticRealization`). Given `w` with `f_ℝ w ∈ τ`,
the torus points `t k` at which each character `m` has absolute value `exp (-k ⟨m, w⟩)` are sent
by the analytic map to torus points at which every character of the dual semigroup of `τ` has
absolute value at most `1`. These lie in a compact part of the chart of `τ`, so properness gives
a cluster point `p` of the `t k`. The image of `p` lies in the chart of `τ`, so `p` lies in the
orbit of a source cone `σ` with `f_ℝ σ ⊆ τ`, hence in the chart of `σ`, and then `w ∈ σ`.

For the sufficiency, every compact subset of the target realization is covered by finitely many
parts of charts, of cones `τ`, where the generators of the dual semigroup of `τ` have absolute
value less than some `R`. The torus points `t` mapped into such a part are those for which the
point `w` of `V` with `⟨m, w⟩ = -log ‖t m‖` satisfies `-log R ≤ ⟨m, f_ℝ w⟩` for the generators
`m`. By Hoffman's error bound (`TauCeti.exists_forall_abs_apply_sub_le_of_forall_neg_le`) such a
`w` is within bounded distance of a point of `f_ℝ⁻¹ τ`, which by the support condition lies in a
source cone `σ` mapped into `τ`. So `t` lies in a part of the chart of `σ` where the generators of
the dual semigroup of `σ` are bounded by a constant depending only on `R`. These finitely many
compact sets contain the torus points of the open preimage, hence its closure.

The nonemptiness hypothesis is necessary for the criterion: the empty subfan of a nonempty fan
has a proper inclusion, but `0` lies in the inverse image of every ambient cone and in no cone of
the empty subfan. Sufficiency holds without it.

## Main declarations

* `TauCeti.Toric.FanHom.preimage_realMap_eq_iUnion_of_isProperMap`: if the analytic map of a
  morphism of regular fans with nonempty source is proper, then for every target cone `τ` the
  inverse image of `τ` is the union of the source cones mapped into `τ`.
* `TauCeti.Toric.FanHom.isProperMap_analyticMap_of_preimage_realMap_subset`: conversely, if for
  every target cone `τ` the inverse image of `τ` is covered by the source cones mapped into `τ`,
  then the analytic map is proper.
* `TauCeti.Toric.FanHom.isProperMap_analyticMap_iff`: the cone-by-cone properness criterion for a
  nonempty source fan.

## References

* W. Fulton, *Introduction to Toric Varieties*, §2.4.
* D. Cox, J. Little and H. Schenck, *Toric Varieties*, §3.4.
-/

public section

open Filter Multiplicative Set Topology

namespace TauCeti.Toric.FanHom

universe u

variable {N N' V V' : Type u} [AddCommGroup N] [AddCommGroup N']
  [AddCommGroup V] [AddCommGroup V'] [Module ℝ V] [Module ℝ V']
  {i : N →+ V} {i' : N' →+ V'} {Φ : Fan i} {Ψ : Fan i'}
  (f : FanHom Φ Ψ) (hΦ : Φ.IsRegular) (hΨ : Ψ.IsRegular)

/-- If the analytic map of a morphism of regular fans with nonempty source is proper, then for
every target cone `τ` the inverse image of `τ` under the real-linear map is the union of the
source cones mapped into `τ`. The nonemptiness hypothesis is necessary: the inclusion of the
empty subfan is proper, but `0` lies in the inverse image of every cone and in no cone of the
empty fan. -/
theorem preimage_realMap_eq_iUnion_of_isProperMap (hΦ0 : Nonempty Φ.cones)
    (hf : IsProperMap (f.analyticMap hΦ hΨ)) (τ : Ψ.cones) :
    f.realMap ⁻¹' (τ.1 : Set V') =
      ⋃ σ : Φ.cones, ⋃ (_ : σ.1.map f.realMap ≤ τ.1), (σ.1 : Set V) := by
  refine Subset.antisymm (fun w hw ↦ ?_) (iUnion₂_subset fun σ hστ x hx ↦
    hστ (Submodule.mem_map_of_mem hx))
  -- The torus points `t k` with `‖t k m‖ = exp (-k ⟨m, w⟩)` are sent into the compact part `K`
  -- of the chart of `τ` where every monomial has absolute value at most `1`.
  choose t ht using fun k : ℕ ↦ Φ.lattice.exists_complexTorus_norm_eq ((k : ℝ) • w)
  let K := Ψ.analyticAffineChartι hΨ τ ''
    {x : AffineSemigroupComplexPoint (dualSemigroup Ψ.lattice τ.1) |
      ∀ s, ‖x (MonoidAlgebra.single (Multiplicative.ofAdd s) 1)‖ ≤ 1}
  have hK : IsCompact K :=
    Ψ.isCompact_image_analyticAffineChartι_setOf_forall_norm_apply_single_le_one hΨ τ
  have htK (k : ℕ) : f.analyticMap hΦ hΨ (Φ.analyticTorusι hΦ hΦ0 (t k)) ∈ K := by
    rw [f.analyticMap_analyticTorusι]
    refine Ψ.analyticTorusι_mem_image_setOf_forall_norm_apply_single_le_one hΨ _ fun m ↦ ?_
    have hm : 0 ≤ Ψ.lattice.realCharacter m (f.realMap ((k : ℝ) • w)) :=
      (mem_dualSemigroup _ _).1 m.2 (by rw [map_smul]; exact τ.1.smul_mem k.cast_nonneg hw)
    rw [complexTorusMap_apply, characterEvaluation_apply, ← Real.exp_zero]
    convert Real.exp_le_exp.2 (neg_nonpos.2 hm) using 1
    rw [← LinearMap.comp_apply, ← Φ.lattice.realCharacter_comp Ψ.lattice f.latticeMap
      f.realMap f.map_lattice]
    exact ht k _
  -- By properness the `t k` cluster at a point `p` whose image lies in the chart of `τ`.
  obtain ⟨p, hpK, hp⟩ := (hf.isCompact_preimage hK).exists_mapClusterPt
    (u := fun k ↦ Φ.analyticTorusι hΦ hΦ0 (t k)) (f := atTop)
    (tendsto_principal.2 (Eventually.of_forall fun k ↦ htK k))
  have hpτ : f.analyticMap hΦ hΨ p ∈ range (Ψ.analyticAffineChartι hΨ τ) :=
    image_subset_range _ _ hpK
  -- The point `p` lies in the orbit of a source cone `σ` mapped into `τ`, hence in its chart.
  rw [← mem_preimage, f.preimage_analyticMap_range_analyticAffineChartι hΦ hΨ τ,
    mem_iUnion₂] at hpτ
  obtain ⟨σ, hστ, hpσ⟩ := hpτ
  obtain ⟨y, rfl⟩ := (Φ.mem_range_analyticAffineChartι_iff hΦ hpσ).2 le_rfl
  exact mem_iUnion₂.2 ⟨σ, hστ, Φ.mem_of_mapClusterPt_analyticTorusι hΦ hΦ0 ht hp⟩

/-- Under the support condition, the part of the realization of the source fan that the analytic
map sends into the part of the chart of a target cone `τ` where the generators of the dual
semigroup of `τ` have absolute value less than `R` is contained in a compact set. -/
private theorem exists_isCompact_preimage_analyticMap_subset (hΦ0 : Nonempty Φ.cones)
    (h : ∀ τ : Ψ.cones, f.realMap ⁻¹' (τ.1 : Set V') ⊆
      ⋃ σ : Φ.cones, ⋃ (_ : σ.1.map f.realMap ≤ τ.1), (σ.1 : Set V))
    (τ : Ψ.cones) (R : ℝ) :
    ∃ L : Set (Φ.analyticRealization hΦ), IsCompact L ∧
      f.analyticMap hΦ hΨ ⁻¹' (Ψ.analyticAffineChartι hΨ τ ''
        {y : AffineSemigroupComplexPoint (dualSemigroup Ψ.lattice τ.1) |
          ∀ j, ‖y (MonoidAlgebra.single (ofAdd ((Ψ.analyticChartGenerators τ).2.toFun j)) 1)‖ <
            R}) ⊆ L := by
  let g := (Ψ.analyticChartGenerators τ).2
  let G := fun σ : Φ.cones ↦ (Φ.analyticChartGenerators σ).2
  have := Φ.lattice.finiteDimensional
  -- The error bound for the inequalities cutting out `f_ℝ⁻¹ τ`, tested on the characters of the
  -- generators of the dual semigroups of all source cones.
  obtain ⟨C, -, hC⟩ := exists_forall_abs_apply_sub_le_of_forall_neg_le
    (fun j ↦ (Ψ.lattice.realCharacter (g.toFun j : N' →+ ℤ)).comp f.realMap)
    (fun k : Σ σ : Φ.cones, Fin (Φ.analyticChartGenerators σ).1 ↦
      Φ.lattice.realCharacter ((G k.1).toFun k.2 : N →+ ℤ))
  let c := Real.log (max R 1)
  have hc : 0 ≤ c := Real.log_nonneg (le_max_right _ _)
  let L := ⋃ σ : Φ.cones, Φ.analyticAffineChartι hΦ σ ''
    {x : AffineSemigroupComplexPoint (dualSemigroup Φ.lattice σ.1) |
      ∀ k, ‖x (MonoidAlgebra.single (ofAdd ((G σ).toFun k)) 1)‖ ≤ Real.exp (C * c)}
  have hL : IsCompact L := isCompact_iUnion fun σ ↦
    Φ.isCompact_image_analyticAffineChartι_setOf_forall_norm_apply_single_toFun_le hΦ σ (G σ) _
  refine ⟨L, hL, ?_⟩
  -- The preimage is open, so it lies in the closure of its torus points.
  have hU := (Ψ.isOpen_image_analyticAffineChartι_setOf_forall_norm_apply_single_toFun_lt hΨ τ g
    R).preimage (f.analyticMap hΦ hΨ).hom.continuous
  have hd : Dense (range (Φ.analyticTorusι hΦ hΦ0)) := by
    rw [Φ.range_analyticTorusι hΦ hΦ0]
    exact Φ.dense_analyticDenseTorus hΦ hΦ0
  refine (hd.open_subset_closure_inter hU).trans (closure_minimal ?_ hL.isClosed)
  rintro _ ⟨⟨y, hy, hyt⟩, t, rfl⟩
  -- At the torus point `t`, the characters `g j ∘ f` have absolute value less than `R`.
  rw [f.analyticMap_analyticTorusι, Ψ.analyticTorusι_eq_analyticAffineChartι hΨ _ τ] at hyt
  obtain rfl := (Ψ.isOpenEmbedding_analyticAffineChartι hΨ τ).injective hyt
  -- The point `w` of `V` recording `-log ‖t m‖` almost satisfies the inequalities of `f_ℝ⁻¹ τ`.
  obtain ⟨w, hw⟩ := Φ.lattice.exists_realCharacter_apply_eq_neg_log_norm t
  have ha (j : Fin (Ψ.analyticChartGenerators τ).1) :
      -c ≤ (Ψ.lattice.realCharacter (g.toFun j : N' →+ ℤ)).comp f.realMap w := by
    have hj := hy j
    rw [AffineSemigroupComplexPoint.ambient_smul_apply_single, default_apply_single, mul_one,
      complexTorusMap_apply, characterEvaluation_apply] at hj
    rw [← Φ.lattice.realCharacter_comp Ψ.lattice f.latticeMap f.realMap f.map_lattice, hw,
      neg_le_neg_iff]
    exact Real.log_le_log (norm_pos_iff.2 (Units.ne_zero _)) (hj.le.trans (le_max_left _ _))
  obtain ⟨w', hw', hww'⟩ := hC c hc w ha
  -- The nearby point `w'` lies in a source cone `σ` mapped into `τ`.
  have hw'τ : f.realMap w' ∈ τ.1 :=
    (IsRegularCone.mem_iff_forall_realCharacter_nonneg_of_closure_range_eq_top Ψ.lattice
      ((Fan.isRegular_iff.mp hΨ) τ.1 τ.2) g.spans).2 fun j ↦ by
      simpa only [LinearMap.comp_apply] using hw' j
  obtain ⟨σ, hστ, hw'σ⟩ := mem_iUnion₂.1 (h τ hw'τ)
  -- Hence the generators of the dual semigroup of `σ` are bounded at `t`.
  refine mem_iUnion.2 ⟨σ, t • (default : AffineSemigroupComplexPoint (dualSemigroup Φ.lattice σ.1)),
    fun k ↦ ?_, (Φ.analyticTorusι_eq_analyticAffineChartι hΦ hΦ0 σ t).symm⟩
  rw [AffineSemigroupComplexPoint.ambient_smul_apply_single, default_apply_single, mul_one,
    ← Real.log_le_iff_le_exp (norm_pos_iff.2 (Units.ne_zero _))]
  have hk := hww' ⟨σ, k⟩
  have hσk : 0 ≤ Φ.lattice.realCharacter ((G σ).toFun k : N →+ ℤ) w' :=
    (mem_dualSemigroup _ _).1 ((G σ).toFun k).2 hw'σ
  rw [map_sub, hw] at hk
  linarith [(abs_le.1 hk).1]

/-- If, for every target cone `τ`, the inverse image of `τ` under the real-linear map is covered by
the source cones mapped into `τ`, then the analytic map of a morphism of regular fans is proper.
The inverse inclusion always holds. -/
theorem isProperMap_analyticMap_of_preimage_realMap_subset
    (h : ∀ τ : Ψ.cones, f.realMap ⁻¹' (τ.1 : Set V') ⊆
      ⋃ σ : Φ.cones, ⋃ (_ : σ.1.map f.realMap ≤ τ.1), (σ.1 : Set V)) :
    IsProperMap (f.analyticMap hΦ hΨ) := by
  refine isProperMap_iff_isCompact_preimage.2
    ⟨(f.analyticMap hΦ hΨ).hom.continuous, fun K hK ↦ ?_⟩
  rcases isEmpty_or_nonempty Φ.cones with hΦ0 | hΦ0
  · -- The realization of the empty fan is empty.
    have : IsEmpty (Φ.analyticRealization hΦ) :=
      ⟨fun x ↦ isEmptyElim (Φ.exists_analyticAffineChartι_apply_eq hΦ x).choose⟩
    exact (Set.toFinite _).isCompact
  -- Cover `K` by finitely many parts of charts where the generators are bounded.
  let U : Ψ.cones × ℕ → Set (Ψ.analyticRealization hΨ) := fun p ↦
    Ψ.analyticAffineChartι hΨ p.1 ''
      {y : AffineSemigroupComplexPoint (dualSemigroup Ψ.lattice p.1.1) |
        ∀ j, ‖y (MonoidAlgebra.single
          (ofAdd ((Ψ.analyticChartGenerators p.1).2.toFun j)) 1)‖ < p.2}
  have hUo (p : Ψ.cones × ℕ) : IsOpen (U p) :=
    Ψ.isOpen_image_analyticAffineChartι_setOf_forall_norm_apply_single_toFun_lt hΨ p.1 _ _
  have hcover : K ⊆ ⋃ p, U p := fun x _ ↦ by
    obtain ⟨τ, y, rfl⟩ := Ψ.exists_analyticAffineChartι_apply_eq hΨ x
    let y' : AffineSemigroupComplexPoint (dualSemigroup Ψ.lattice τ.1) := y
    let b := fun j ↦ ‖y' (MonoidAlgebra.single (ofAdd ((Ψ.analyticChartGenerators τ).2.toFun j)) 1)‖
    obtain ⟨n, hn⟩ := exists_nat_gt (∑ j, b j)
    exact mem_iUnion.2 ⟨(τ, n), y, fun j ↦
      (Finset.single_le_sum (f := b) (fun _ _ ↦ norm_nonneg _) (Finset.mem_univ j)).trans_lt hn,
      rfl⟩
  obtain ⟨F, hF⟩ := hK.elim_finite_subcover U hUo hcover
  choose L hL hLU using fun p : Ψ.cones × ℕ ↦
    f.exists_isCompact_preimage_analyticMap_subset hΦ hΨ hΦ0 h p.1 p.2
  refine (F.isCompact_biUnion fun p _ ↦ hL p).of_isClosed_subset
    (hK.isClosed.preimage (f.analyticMap hΦ hΨ).hom.continuous) fun x hx ↦ ?_
  obtain ⟨p, hp, hxp⟩ := mem_iUnion₂.1 (hF hx)
  exact mem_iUnion₂.2 ⟨p, hp, hLU p hxp⟩

/-- **The cone-by-cone properness criterion.** The analytic map of a morphism of regular fans
with nonempty source is proper exactly when, for every target cone `τ`, the inverse image of `τ`
under the real-linear map is the union of the source cones mapped into `τ`. The nonemptiness
hypothesis is necessary: the inclusion of the empty subfan is proper, but `0` lies in the inverse
image of every cone and in no cone of the empty fan. -/
theorem isProperMap_analyticMap_iff (hΦ0 : Nonempty Φ.cones) :
    IsProperMap (f.analyticMap hΦ hΨ) ↔ ∀ τ : Ψ.cones, f.realMap ⁻¹' (τ.1 : Set V') =
      ⋃ σ : Φ.cones, ⋃ (_ : σ.1.map f.realMap ≤ τ.1), (σ.1 : Set V) :=
  ⟨fun hf ↦ f.preimage_realMap_eq_iUnion_of_isProperMap hΦ hΨ hΦ0 hf, fun h ↦
    f.isProperMap_analyticMap_of_preimage_realMap_subset hΦ hΨ fun τ ↦ (h τ).subset⟩

end TauCeti.Toric.FanHom
