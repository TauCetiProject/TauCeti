/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.FundamentalGroupoid.CoverGeneration
public import TauCeti.Topology.MetricSpace.Lebesgue
public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.CategoryTheory.Functor.OfSequence

/-!
# Gluing functors out of the fundamental groupoid

Let `U : ι → Set X` be a family of subsets such that every point of `X` has some `U i` as a
neighbourhood, and let `F i` be functors, with values in any category, out of the fundamental
groupoids of the sets `U i`, which agree on the fundamental groupoids of the pairwise
intersections `U i ∩ U j`. This file constructs the functor `TauCeti.FundamentalGroupoid.glue`
out of the fundamental groupoid of `X` which restricts to every `F i`. Together with the
uniqueness statement `TauCeti.FundamentalGroupoid.functor_ext`, this is the universal property
behind the groupoid Seifert--van Kampen theorem; no connectedness assumption is made on the sets
`U i` or on their intersections.

The covering hypothesis holds for every open cover of `X`, and more generally for every family
whose interiors cover `X`. To define a functor out of the fundamental groupoid of `X`, it
therefore suffices to give compatible functors out of the fundamental groupoids of the members
of such a cover; `map_subtypeVal_comp_glue` and `glue_obj_mk` compute the result on each member.
This is how `TauCeti.FundamentalGroupoid.isColimitCechCocone` constructs the functor induced by
a cocone over the Čech diagram of an open cover.

## Main declarations

* `TauCeti.FundamentalGroupoid.glue`: the functor glued from the functors `F i`.
* `TauCeti.FundamentalGroupoid.map_subtypeVal_comp_glue`: the glued functor restricts to `F i`
  on the fundamental groupoid of `U i`.
* `TauCeti.FundamentalGroupoid.eq_glue`: it is the only functor with this property.

## References

* R. Brown, *Topology and Groupoids*, 3rd ed., Section 6.7.
* A. Hatcher, *Algebraic Topology*, Section 1.2, proof of Theorem 1.20.
-/

public section

noncomputable section

open CategoryTheory Set Topology Metric
open scoped unitInterval

namespace TauCeti.FundamentalGroupoid

open _root_.FundamentalGroupoid

variable {X : Type*} [TopologicalSpace X] {ι : Type*} {U : ι → Set X}
  {D : Type*} [Category D]

variable (hU : ∀ x, ∃ i, U i ∈ 𝓝 x)

section Partition

/-- The `k`-th point of the uniform partition of the unit interval into `N` pieces; it is constant
at `1` from `k = N` on. -/
private def pt (N k : ℕ) : I := Set.Icc.addNSMul zero_le_one (1 / N : ℝ) k

private lemma coe_pt {N k : ℕ} (hk : k ≤ N) : (pt N k : ℝ) = k / N := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · obtain rfl : k = 0 := by omega
    simp [pt, Set.Icc.addNSMul_zero]
  rw [pt, Set.Icc.addNSMul, projIcc_of_mem]
  · simp [div_eq_mul_inv]
  · simp only [zero_add, nsmul_eq_mul, mem_Icc]
    refine ⟨by positivity, ?_⟩
    rw [mul_one_div, div_le_one (by exact_mod_cast hN)]
    exact_mod_cast hk

private lemma pt_zero (N : ℕ) : pt N 0 = 0 := Subtype.ext (by simp [pt, Set.Icc.addNSMul_zero])

private lemma pt_self {N : ℕ} (hN : N ≠ 0) : pt N N = 1 :=
  Subtype.ext (by rw [coe_pt le_rfl]; simp [hN])

private lemma pt_mono (N : ℕ) : Monotone (pt N) :=
  Set.Icc.monotone_addNSMul _ (by positivity)

private lemma pt_mul {M N k : ℕ} (hM : M ≠ 0) (hk : k ≤ N) : pt (M * N) (M * k) = pt N k := by
  apply Subtype.ext
  rw [coe_pt hk, coe_pt (Nat.mul_le_mul_left M hk)]
  push_cast
  rw [mul_div_mul_left _ _ (by exact_mod_cast hM)]

private lemma abs_sub_pt_le {N k : ℕ} {t : I} (ht : t ∈ Icc (pt N k) (pt N (k + 1))) :
    |(t : ℝ) - pt N k| ≤ 1 / N :=
  Set.Icc.abs_sub_addNSMul_le _ (by positivity) k ht

private lemma coe_convexComb_pt {N k : ℕ} (hk : k < N) (t : I) :
    (Icc.convexComb (pt N k) (pt N (k + 1)) t : ℝ) = (k + t) / N := by
  have hN : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.zero_lt_of_lt hk).ne'
  rw [Icc.coe_convexComb, coe_pt hk.le, coe_pt hk]
  push_cast
  field_simp
  ring

private lemma mem_Icc_pt {N k : ℕ} : pt N k ∈ Icc (pt N k) (pt N (k + 1)) :=
  left_mem_Icc.2 (pt_mono N k.le_succ)

private lemma mem_Icc_pt_succ {N k : ℕ} : pt N (k + 1) ∈ Icc (pt N k) (pt N (k + 1)) :=
  right_mem_Icc.2 (pt_mono N k.le_succ)

end Partition

variable (U) in
/-- `γ` maps every piece of the uniform partition of the unit interval into `N` pieces into a
single member of `U`. -/
private def IsFine {x y : X} (γ : Path x y) (N : ℕ) : Prop :=
  ∀ k, ∃ i, ∀ t ∈ Icc (pt N k) (pt N (k + 1)), γ t ∈ U i

include hU in
private lemma exists_isFine {x y : X} (γ : Path x y) :
    ∃ N₀, ∀ N, N₀ ≤ N → N ≠ 0 ∧ IsFine U γ N := by
  obtain ⟨δ, hδ, h⟩ := lebesgue_number_lemma_of_metric_of_mem_nhds isCompact_univ
    (c := fun i ↦ γ ⁻¹' U i) fun t _ ↦
      (hU (γ t)).imp fun _ ↦ γ.continuous.continuousAt.preimage_mem_nhds
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hδ
  refine ⟨n + 1, fun N hN ↦ ⟨by omega, fun k ↦ ?_⟩⟩
  obtain ⟨i, hi⟩ := h (pt N k) (mem_univ _)
  refine ⟨i, fun t ht ↦ hi ?_⟩
  rw [mem_ball, Subtype.dist_eq, Real.dist_eq]
  exact (abs_sub_pt_le ht).trans_lt <|
    (one_div_le_one_div_of_le (by positivity) (by exact_mod_cast hN)).trans_lt hn

private lemma IsFine.subpath_mem {x y : X} {γ : Path x y} {N : ℕ} (h : IsFine U γ N) (k : ℕ) :
    ∃ i, ∀ t, γ.subpath (pt N k) (pt N (k + 1)) t ∈ U i :=
  (h k).imp fun _ hi ↦ Path.subpath_apply_mem hi mem_Icc_pt mem_Icc_pt_succ

section Construction

variable (F : ∀ i, _root_.FundamentalGroupoid (U i) ⥤ D)
  (hF : ∀ i j, map (ContinuousMap.inclusion (inter_subset_left : U i ∩ U j ⊆ U i)) ⋙ F i =
    map (ContinuousMap.inclusion (inter_subset_right : U i ∩ U j ⊆ U j)) ⋙ F j)

/-- The object of `D` assigned to a point, through a chosen member of the cover. -/
private def glueObj (x : X) : D :=
  (F (hU x).choose).obj (mk ⟨x, mem_of_mem_nhds (hU x).choose_spec⟩)

include hF in
private lemma obj_eq (i : ι) {x : X} (hx : x ∈ U i) :
    (F i).obj (mk ⟨x, hx⟩) = glueObj hU F x :=
  Functor.congr_obj (hF i (hU x).choose) (mk ⟨x, hx, mem_of_mem_nhds (hU x).choose_spec⟩)

include hF in
/-- The value of the local functor `F i` on a path lying in `U i`. -/
private def locVal (i : ι) {x y : X} (P : Path x y) (hP : ∀ t, P t ∈ U i) :
    glueObj hU F x ⟶ glueObj hU F y :=
  eqToHom (obj_eq hU F hF i (P.source ▸ hP 0)).symm ≫
    (F i).map (Path.Homotopic.Quotient.mk
      (P.codRestrict (x := ⟨x, P.source ▸ hP 0⟩) (y := ⟨y, P.target ▸ hP 1⟩) hP)) ≫
    eqToHom (obj_eq hU F hF i (P.target ▸ hP 1))

include hF in
/-- The local value does not depend on the member of the cover containing the path. -/
private lemma locVal_congr_index (i j : ι) {x y : X} (P : Path x y) (hi : ∀ t, P t ∈ U i)
    (hj : ∀ t, P t ∈ U j) : locVal hU F hF i P hi = locVal hU F hF j P hj := by
  have hx : x ∈ U i ∩ U j := P.source ▸ ⟨hi 0, hj 0⟩
  have hy : y ∈ U i ∩ U j := P.target ▸ ⟨hi 1, hj 1⟩
  have h := Functor.congr_hom (hF i j) (Path.Homotopic.Quotient.mk
    (P.codRestrict (x := ⟨x, hx⟩) (y := ⟨y, hy⟩) fun t ↦ ⟨hi t, hj t⟩) : mk _ ⟶ mk _)
  have hPi : (P.codRestrict (x := ⟨x, hx⟩) (y := ⟨y, hy⟩) fun t ↦ ⟨hi t, hj t⟩).map
      (ContinuousMap.inclusion inter_subset_left).continuous =
      P.codRestrict (x := ⟨x, hx.1⟩) (y := ⟨y, hy.1⟩) hi := by
    ext t
    exact (Path.codRestrict_coe (s := U i ∩ U j) (x := ⟨x, hx⟩) (y := ⟨y, hy⟩) P _ t).trans
      (Path.codRestrict_coe (x := ⟨x, hx.1⟩) (y := ⟨y, hy.1⟩) P hi t).symm
  have hPj : (P.codRestrict (x := ⟨x, hx⟩) (y := ⟨y, hy⟩) fun t ↦ ⟨hi t, hj t⟩).map
      (ContinuousMap.inclusion inter_subset_right).continuous =
      P.codRestrict (x := ⟨x, hx.2⟩) (y := ⟨y, hy.2⟩) hj := by
    ext t
    exact (Path.codRestrict_coe (s := U i ∩ U j) (x := ⟨x, hx⟩) (y := ⟨y, hy⟩) P _ t).trans
      (Path.codRestrict_coe (x := ⟨x, hx.2⟩) (y := ⟨y, hy.2⟩) P hj t).symm
  have h' : ((F i).map (Path.Homotopic.Quotient.mk (P.codRestrict hi) :
        mk (⟨x, hx.1⟩ : U i) ⟶ mk (⟨y, hy.1⟩ : U i))) =
      eqToHom ((obj_eq hU F hF i hx.1).trans (obj_eq hU F hF j hx.2).symm) ≫
        (F j).map (Path.Homotopic.Quotient.mk (P.codRestrict hj) :
          mk (⟨x, hx.2⟩ : U j) ⟶ mk (⟨y, hy.2⟩ : U j)) ≫
        eqToHom ((obj_eq hU F hF j hy.2).trans (obj_eq hU F hF i hy.1).symm) := by
    rw [← hPi, ← hPj]
    exact h
  simp only [locVal]
  rw [h']
  simp

include hF in
/-- The local value of a concatenation is the composite of the local values. -/
private lemma locVal_trans (i : ι) {x y z : X} (P : Path x y) (Q : Path y z)
    (hP : ∀ t, P t ∈ U i) (hQ : ∀ t, Q t ∈ U i) (hPQ : ∀ t, P.trans Q t ∈ U i) :
    locVal hU F hF i (P.trans Q) hPQ = locVal hU F hF i P hP ≫ locVal hU F hF i Q hQ := by
  have h : (P.trans Q).codRestrict (x := ⟨x, P.source ▸ hP 0⟩) (y := ⟨z, Q.target ▸ hQ 1⟩) hPQ =
      (P.codRestrict (x := ⟨x, P.source ▸ hP 0⟩) (y := ⟨y, P.target ▸ hP 1⟩) hP).trans
        (Q.codRestrict (x := ⟨y, P.target ▸ hP 1⟩) (y := ⟨z, Q.target ▸ hQ 1⟩) hQ) := by
    ext t
    simp only [Path.codRestrict_coe, Path.trans_apply]
    split_ifs <;> simp
  simp only [locVal, h, Path.Homotopic.Quotient.mk_trans]
  rw [← comp_eq, Functor.map_comp]
  simp

include hF in
/-- Local values compose along a relation `[P] ⬝ [Q] = [R]` between the homotopy classes of the
restrictions of the paths to `U i`. -/
private lemma locVal_comp_eq_of_trans (i : ι) {x y z : X} (P : Path x y) (Q : Path y z)
    (R : Path x z) (hP : ∀ t, P t ∈ U i) (hQ : ∀ t, Q t ∈ U i) (hR : ∀ t, R t ∈ U i)
    (h : Path.Homotopic.Quotient.trans
        (Path.Homotopic.Quotient.mk
          (P.codRestrict (x := ⟨x, P.source ▸ hP 0⟩) (y := ⟨y, P.target ▸ hP 1⟩) hP))
        (Path.Homotopic.Quotient.mk
          (Q.codRestrict (x := ⟨y, P.target ▸ hP 1⟩) (y := ⟨z, Q.target ▸ hQ 1⟩) hQ)) =
      Path.Homotopic.Quotient.mk
        (R.codRestrict (x := ⟨x, P.source ▸ hP 0⟩) (y := ⟨z, Q.target ▸ hQ 1⟩) hR)) :
    locVal hU F hF i P hP ≫ locVal hU F hF i Q hQ = locVal hU F hF i R hR := by
  simp only [locVal, ← h]
  rw [← comp_eq, Functor.map_comp]
  simp

include hF in
/-- The local value only depends on the underlying function of the path, up to transport of
its endpoints. -/
private lemma locVal_congr (i : ι) {x y x' y' : X} (P : Path x y) (Q : Path x' y')
    (hx : x = x') (hy : y = y') (h : ∀ t, P t = Q t) (hP : ∀ t, P t ∈ U i)
    (hQ : ∀ t, Q t ∈ U i) :
    locVal hU F hF i P hP =
      eqToHom (congrArg (glueObj hU F) hx) ≫ locVal hU F hF i Q hQ ≫
        eqToHom (congrArg (glueObj hU F) hy).symm := by
  subst hx hy
  obtain rfl : P = Q := Path.ext (funext h)
  simp

include hF in
/-- Local values along the images of two paths with the same endpoints in a simply connected
space agree. -/
private lemma locVal_eq_of_simplyConnected (i : ι) {Y : Type*} [TopologicalSpace Y]
    [SimplyConnectedSpace Y] (g : C(Y, X)) (hg : ∀ y, g y ∈ U i) {y₀ y₁ : Y}
    (α β : Path y₀ y₁) {x₀ x₁ : X} (P Q : Path x₀ x₁) (hPα : ∀ t, P t = g (α t))
    (hQβ : ∀ t, Q t = g (β t)) (hP : ∀ t, P t ∈ U i) (hQ : ∀ t, Q t ∈ U i) :
    locVal hU F hF i P hP = locVal hU F hF i Q hQ := by
  have hx : x₀ = g y₀ := by rw [← P.source, hPα, α.source]
  have hy : x₁ = g y₁ := by rw [← P.target, hPα, α.target]
  subst hx hy
  obtain rfl : P = α.map g.continuous := Path.ext (funext hPα)
  obtain rfl : Q = β.map g.continuous := Path.ext (funext hQβ)
  let g' : C(Y, U i) := ⟨fun y ↦ ⟨g y, hg y⟩, g.continuous.codRestrict hg⟩
  have hα : (α.map g.continuous).codRestrict (x := ⟨g y₀, hg y₀⟩) (y := ⟨g y₁, hg y₁⟩) hP =
      α.map g'.continuous := by
    ext t
    exact Path.codRestrict_coe (x := ⟨g y₀, hg y₀⟩) (y := ⟨g y₁, hg y₁⟩) _ hP t
  have hβ : (β.map g.continuous).codRestrict (x := ⟨g y₀, hg y₀⟩) (y := ⟨g y₁, hg y₁⟩) hQ =
      β.map g'.continuous := by
    ext t
    exact Path.codRestrict_coe (x := ⟨g y₀, hg y₀⟩) (y := ⟨g y₁, hg y₁⟩) _ hQ t
  simp only [locVal, hα, hβ,
    Path.Homotopic.Quotient.eq.2 ((SimplyConnectedSpace.paths_homotopic α β).map g')]

include hF in
private lemma locVal_refl (i : ι) (x : X) (h : ∀ t, Path.refl x t ∈ U i) :
    locVal hU F hF i (Path.refl x) h = 𝟙 _ := by
  have hr : (Path.refl x).codRestrict (x := ⟨x, h 0⟩) (y := ⟨x, h 0⟩) h =
      Path.refl (⟨x, h 0⟩ : U i) := by
    ext t
    exact Path.codRestrict_coe (x := ⟨x, h 0⟩) (y := ⟨x, h 0⟩) _ h t
  have hid : (Path.Homotopic.Quotient.mk (Path.refl (⟨x, h 0⟩ : U i)) : mk _ ⟶ mk _) =
      𝟙 (mk (⟨x, h 0⟩ : U i)) :=
    (id_eq_path_refl _).symm
  simp [locVal, hr, hid]

include hF in
/-- The local value of a path which stays at its starting point is the identity, up to
transport. -/
private lemma locVal_eq_eqToHom (i : ι) {x y : X} (P : Path x y) (hP : ∀ t, P t ∈ U i)
    (hconst : ∀ t, P t = x) :
    locVal hU F hF i P hP = eqToHom (congrArg (glueObj hU F) (P.target ▸ hconst 1).symm) := by
  have hy : y = x := P.target ▸ hconst 1
  rw [locVal_congr hU F hF i P (Path.refl x) rfl hy hconst hP fun _ ↦ P.source ▸ hP 0,
    locVal_refl]
  simp

include hF in
/-- The local value of a path lying in some member of the cover. -/
private def pathVal {x y : X} (P : Path x y) (h : ∃ i, ∀ t, P t ∈ U i) :
    glueObj hU F x ⟶ glueObj hU F y :=
  locVal hU F hF h.choose P h.choose_spec

include hF in
private lemma pathVal_eq (i : ι) {x y : X} (P : Path x y) (h : ∃ i, ∀ t, P t ∈ U i)
    (hi : ∀ t, P t ∈ U i) : pathVal hU F hF P h = locVal hU F hF i P hi :=
  locVal_congr_index hU F hF _ _ P _ _

include hF in
/-- Local values are additive along consecutive subpaths inside one member of the cover. -/
private lemma pathVal_subpath_trans {x y : X} (γ : Path x y) (i : ι) {lo hi : I}
    (hγ : ∀ t ∈ Icc lo hi, γ t ∈ U i) {a b c : I} (ha : a ∈ Icc lo hi) (hb : b ∈ Icc lo hi)
    (hc : c ∈ Icc lo hi) (hab : ∃ i, ∀ t, γ.subpath a b t ∈ U i)
    (hbc : ∃ i, ∀ t, γ.subpath b c t ∈ U i) (hac : ∃ i, ∀ t, γ.subpath a c t ∈ U i) :
    pathVal hU F hF (γ.subpath a b) hab ≫ pathVal hU F hF (γ.subpath b c) hbc =
      pathVal hU F hF (γ.subpath a c) hac := by
  rw [pathVal_eq hU F hF i _ _ (Path.subpath_apply_mem hγ ha hb),
    pathVal_eq hU F hF i _ _ (Path.subpath_apply_mem hγ hb hc),
    pathVal_eq hU F hF i _ _ (Path.subpath_apply_mem hγ ha hc)]
  have hlohi : lo ≤ hi := ha.1.trans ha.2
  obtain ⟨a', rfl⟩ : ∃ a', Icc.convexComb lo hi a' = a := ⟨_, (Icc.eq_convexComb ha.1 ha.2).symm⟩
  obtain ⟨b', rfl⟩ : ∃ b', Icc.convexComb lo hi b' = b := ⟨_, (Icc.eq_convexComb hb.1 hb.2).symm⟩
  obtain ⟨c', rfl⟩ : ∃ c', Icc.convexComb lo hi c' = c := ⟨_, (Icc.eq_convexComb hc.1 hc.2).symm⟩
  have haU : γ (Icc.convexComb lo hi a') ∈ U i := hγ _ ha
  have hbU : γ (Icc.convexComb lo hi b') ∈ U i := hγ _ hb
  have hcU : γ (Icc.convexComb lo hi c') ∈ U i := hγ _ hc
  let g : C(I, X) := γ.toContinuousMap.comp ⟨_, Icc.continuous_convexComb lo hi⟩
  let g' : C(I, U i) := ⟨fun t ↦ ⟨g t,
    hγ _ ⟨Icc.le_convexComb hlohi t, Icc.convexComb_le hlohi t⟩⟩,
    g.continuous.codRestrict _⟩
  let p : Path (g' 0) (g' 1) := Path.id.map g'.continuous
  have hpa : (⟨γ (Icc.convexComb lo hi a'), haU⟩ : U i) = p a' := by
    apply Subtype.ext
    rfl
  have hpb : (⟨γ (Icc.convexComb lo hi b'), hbU⟩ : U i) = p b' := by
    apply Subtype.ext
    rfl
  have hpc : (⟨γ (Icc.convexComb lo hi c'), hcU⟩ : U i) = p c' := by
    apply Subtype.ext
    rfl
  let qab : Path (⟨γ (Icc.convexComb lo hi a'), haU⟩ : U i)
      ⟨γ (Icc.convexComb lo hi b'), hbU⟩ :=
    (γ.subpath (Icc.convexComb lo hi a') (Icc.convexComb lo hi b')).codRestrict
      (Path.subpath_apply_mem hγ ha hb)
  let qbc : Path (⟨γ (Icc.convexComb lo hi b'), hbU⟩ : U i)
      ⟨γ (Icc.convexComb lo hi c'), hcU⟩ :=
    (γ.subpath (Icc.convexComb lo hi b') (Icc.convexComb lo hi c')).codRestrict
      (Path.subpath_apply_mem hγ hb hc)
  let qac : Path (⟨γ (Icc.convexComb lo hi a'), haU⟩ : U i)
      ⟨γ (Icc.convexComb lo hi c'), hcU⟩ :=
    (γ.subpath (Icc.convexComb lo hi a') (Icc.convexComb lo hi c')).codRestrict
      (Path.subpath_apply_mem hγ ha hc)
  have cast_subpath_eq_codRestrict (r s : I)
      (hrU : γ (Icc.convexComb lo hi r) ∈ U i) (hsU : γ (Icc.convexComb lo hi s) ∈ U i)
      (hr : (⟨γ (Icc.convexComb lo hi r), hrU⟩ : U i) = p r)
      (hs : (⟨γ (Icc.convexComb lo hi s), hsU⟩ : U i) = p s)
      (hrs : ∀ t, γ.subpath (Icc.convexComb lo hi r) (Icc.convexComb lo hi s) t ∈ U i) :
      (p.subpath r s).cast hr hs =
        (γ.subpath (Icc.convexComb lo hi r) (Icc.convexComb lo hi s)).codRestrict hrs := by
    apply Path.ext
    funext t
    apply Subtype.ext
    simp only [Path.cast_coe, Path.codRestrict_coe, Path.subpath, p, Path.map_coe, g', g]
    have hcomb : Icc.convexComb (Icc.convexComb lo hi r) (Icc.convexComb lo hi s) t =
        Icc.convexComb lo hi (Icc.convexComb r s t) := by
      ext
      simp only [Icc.coe_convexComb]
      ring
    exact congrArg γ hcomb.symm
  have hab' : (p.subpath a' b').cast hpa hpb = qab :=
    cast_subpath_eq_codRestrict a' b' haU hbU hpa hpb (Path.subpath_apply_mem hγ ha hb)
  have hbc' : (p.subpath b' c').cast hpb hpc = qbc :=
    cast_subpath_eq_codRestrict b' c' hbU hcU hpb hpc (Path.subpath_apply_mem hγ hb hc)
  have hac' : (p.subpath a' c').cast hpa hpc = qac :=
    cast_subpath_eq_codRestrict a' c' haU hcU hpa hpc (Path.subpath_apply_mem hγ ha hc)
  have hquot : Path.Homotopic.Quotient.trans (Path.Homotopic.Quotient.mk qab)
      (Path.Homotopic.Quotient.mk qbc) = Path.Homotopic.Quotient.mk qac := by
    rw [← hab', ← hbc', ← hac']
    exact Path.Homotopic.Quotient.subpath_cast_trans p a' b' c' hpa hpb hpc
  exact locVal_comp_eq_of_trans hU F hF i _ _ _ _ _ _ hquot

include hF in
private lemma pathVal_congr {x y x' y' : X} (P : Path x y) (Q : Path x' y') (hx : x = x')
    (hy : y = y') (h : ∀ t, P t = Q t) (hP : ∃ i, ∀ t, P t ∈ U i) (hQ : ∃ i, ∀ t, Q t ∈ U i) :
    pathVal hU F hF P hP =
      eqToHom (congrArg (glueObj hU F) hx) ≫ pathVal hU F hF Q hQ ≫
        eqToHom (congrArg (glueObj hU F) hy).symm := by
  obtain ⟨i, hi⟩ := hQ
  rw [pathVal_eq hU F hF i P hP fun t ↦ h t ▸ hi t, pathVal_eq hU F hF i Q _ hi]
  exact locVal_congr hU F hF i P Q hx hy h _ hi

include hF in
/-- The value of `γ` on the `k`-th piece of the uniform partition into `N` pieces. -/
private def segVal {x y : X} (γ : Path x y) {N : ℕ} (h : IsFine U γ N) (k : ℕ) :
    glueObj hU F (γ (pt N k)) ⟶ glueObj hU F (γ (pt N (k + 1))) :=
  pathVal hU F hF (γ.subpath (pt N k) (pt N (k + 1))) (h.subpath_mem k)

include hF in
/-- On a run of partition points inside an interval which `γ` maps into one member of the cover,
the composite of the segment values is the value of the subpath between the extreme points. -/
private lemma map_segVal_eq {x y : X} (γ : Path x y) {N : ℕ} (h : IsFine U γ N) (i : ι)
    {lo hi : I} (hγ : ∀ t ∈ Icc lo hi, γ t ∈ U i) {a b : ℕ} (hab : a ≤ b)
    (hpt : ∀ j, a ≤ j → j ≤ b → pt N j ∈ Icc lo hi) :
    Functor.OfSequence.map (segVal hU F hF γ h) a b hab =
      pathVal hU F hF (γ.subpath (pt N a) (pt N b))
        ⟨i, Path.subpath_apply_mem hγ (hpt a le_rfl hab) (hpt b hab le_rfl)⟩ := by
  induction b, hab using Nat.le_induction with
  | base =>
    rw [Functor.OfSequence.map_id, pathVal_eq hU F hF i _ _
      (Path.subpath_apply_mem hγ (hpt a le_rfl le_rfl) (hpt a le_rfl le_rfl)),
      locVal_eq_eqToHom hU F hF i _ _ fun t ↦ by simp]
    simp
  | succ b hab ih =>
    rw [Functor.OfSequence.map_comp _ a b (b + 1) hab b.le_succ,
      ih fun j hj hj' ↦ hpt j hj (by omega), Functor.OfSequence.map_le_succ, segVal,
      pathVal_subpath_trans hU F hF γ i hγ (hpt a le_rfl (by omega)) (hpt b hab (by omega))
        (hpt (b + 1) (by omega) le_rfl)]

include hF in
/-- The value of `γ` computed along the uniform partition into `N` pieces. -/
private def liftN {x y : X} (γ : Path x y) {N : ℕ} (h : IsFine U γ N) (hN : N ≠ 0) :
    glueObj hU F x ⟶ glueObj hU F y :=
  eqToHom (by rw [pt_zero, γ.source]) ≫
    Functor.OfSequence.map (segVal hU F hF γ h) 0 N N.zero_le ≫
      eqToHom (by rw [pt_self hN, γ.target])

include hF in
/-- For a path inside one member of the cover, the partition value is the local value. -/
private lemma liftN_eq_locVal {x y : X} (γ : Path x y) {N : ℕ} (h : IsFine U γ N) (hN : N ≠ 0)
    (i : ι) (hγ : ∀ t, γ t ∈ U i) : liftN hU F hF γ h hN = locVal hU F hF i γ hγ := by
  have hmem : ∀ t, γ.subpath (pt N 0) (pt N N) t ∈ U i := fun _ ↦ hγ _
  rw [liftN, map_segVal_eq hU F hF γ h i (lo := 0) (hi := 1) (fun t _ ↦ hγ t) (Nat.zero_le N)
    fun j _ _ ↦ ⟨unitInterval.nonneg', unitInterval.le_one'⟩, pathVal_eq hU F hF i _ _ hmem,
    locVal_congr hU F hF i _ γ (by rw [pt_zero, γ.source]) (by rw [pt_self hN, γ.target])
      (fun t ↦ by simp [Path.subpath, pt_zero, pt_self hN]) hmem hγ]
  simp

include hF in
private lemma liftN_congr {x y : X} (γ : Path x y) {N N' : ℕ} (hNN' : N = N') (h : IsFine U γ N)
    (h' : IsFine U γ N') (hN : N ≠ 0) (hN' : N' ≠ 0) :
    liftN hU F hF γ h hN = liftN hU F hF γ h' hN' := by
  subst hNN'
  rfl

include hF in
/-- Refining the uniform partition does not change the partition value. -/
private lemma liftN_mul {x y : X} (γ : Path x y) {M N : ℕ} (hM : M ≠ 0) (hN : N ≠ 0)
    (h : IsFine U γ N) (h' : IsFine U γ (M * N)) :
    liftN hU F hF γ h' (mul_ne_zero hM hN) = liftN hU F hF γ h hN := by
  have key : ∀ k (hk : k ≤ N),
      Functor.OfSequence.map (segVal hU F hF γ h') 0 (M * k) (M * k).zero_le =
        eqToHom (by rw [pt_zero, pt_zero]) ≫
          Functor.OfSequence.map (segVal hU F hF γ h) 0 k k.zero_le ≫
            eqToHom (by rw [pt_mul hM hk]) := by
    intro k hk
    induction k with
    | zero => simp [Functor.OfSequence.map_id]
    | succ k ih =>
      obtain ⟨i, hi⟩ := h k
      rw [Functor.OfSequence.map_comp _ 0 (M * k) (M * (k + 1)) (M * k).zero_le
          (Nat.mul_le_mul_left M k.le_succ),
        map_segVal_eq hU F hF γ h' i hi (Nat.mul_le_mul_left M k.le_succ) fun j hj hj' ↦
          ⟨pt_mul hM (k.le_succ.trans hk) ▸ pt_mono _ hj, pt_mul hM hk ▸ pt_mono _ hj'⟩,
        ih (by omega), Functor.OfSequence.map_comp _ 0 k (k + 1) k.zero_le k.le_succ,
        Functor.OfSequence.map_le_succ, segVal,
        pathVal_congr hU F hF _ _ (by rw [pt_mul hM (k.le_succ.trans hk)])
          (by rw [pt_mul hM hk]) (fun t ↦ by rw [pt_mul hM (k.le_succ.trans hk), pt_mul hM hk]) _
          (h.subpath_mem k)]
      simp
  rw [liftN, liftN, key N le_rfl]
  simp

include hU in
private lemma exists_isFine_homotopy {x y : X} {p q : Path x y} (H : p.Homotopy q) :
    ∃ N, N ≠ 0 ∧ ∀ l k, ∃ i, ∀ t ∈ Icc (pt N l) (pt N (l + 1)),
      ∀ s ∈ Icc (pt N k) (pt N (k + 1)), H (t, s) ∈ U i := by
  obtain ⟨δ, hδ, h⟩ := lebesgue_number_lemma_of_metric_of_mem_nhds isCompact_univ
    (c := fun i ↦ H ⁻¹' U i) fun ts _ ↦
      (hU (H ts)).imp fun _ ↦ H.continuous.continuousAt.preimage_mem_nhds
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hδ
  have hN : (1 / ((n + 1 : ℕ) : ℝ)) < δ := by exact_mod_cast hn
  refine ⟨n + 1, n.succ_ne_zero, fun l k ↦ ?_⟩
  obtain ⟨i, hi⟩ := h (pt (n + 1) l, pt (n + 1) k) (mem_univ _)
  refine ⟨i, fun t ht s hs ↦ hi ?_⟩
  rw [mem_ball, Prod.dist_eq, max_lt_iff, Subtype.dist_eq, Subtype.dist_eq, Real.dist_eq,
    Real.dist_eq]
  exact ⟨(abs_sub_pt_le ht).trans_lt hN, (abs_sub_pt_le hs).trans_lt hN⟩

private lemma pt_eq_one {N k : ℕ} (hN : N ≠ 0) (hk : N ≤ k) : pt N k = 1 := by
  rw [pt, Set.Icc.addNSMul, projIcc_of_right_le]
  · rfl
  · rw [zero_add, nsmul_eq_mul, mul_one_div, le_div_iff₀ (by positivity), one_mul]
    exact_mod_cast hk

private lemma trans_pt_left {x y z : X} (γ : Path x y) (δ : Path y z) {N k : ℕ} (hk : k ≤ N) :
    γ.trans δ (pt (N + N) k) = γ (pt N k) := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · obtain rfl : k = 0 := by omega
    simp [pt_zero]
  have _ : (0 : ℝ) < N := by exact_mod_cast hN
  refine Path.trans_apply_of_le γ δ ?_ _ ?_
  · rw [coe_pt (by omega : k ≤ N + N), div_le_iff₀ (by push_cast; positivity)]
    push_cast
    have hk' : (k : ℝ) ≤ N := by exact_mod_cast hk
    linarith
  · rw [coe_pt hk, coe_pt (by omega : k ≤ N + N)]
    push_cast
    field_simp
    ring

private lemma trans_pt_right {x y z : X} (γ : Path x y) (δ : Path y z) {N : ℕ} (hN : N ≠ 0)
    (k : ℕ) : γ.trans δ (pt (N + N) (N + k)) = δ (pt N k) := by
  rcases le_or_gt k N with hk | hk
  · have _ : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
    refine Path.trans_apply_of_ge γ δ ?_ _ ?_
    · rw [coe_pt (by omega : N + k ≤ N + N), le_div_iff₀ (by push_cast; positivity)]
      push_cast
      have _ : (0 : ℝ) ≤ k := by positivity
      linarith
    · rw [coe_pt hk, coe_pt (by omega : N + k ≤ N + N)]
      push_cast
      field_simp
      ring
  · rw [pt_eq_one (by omega) (by omega), pt_eq_one hN hk.le, Path.target, Path.target]

private lemma trans_subpath_left {x y z : X} (γ : Path x y) (δ : Path y z) {N k : ℕ} (hk : k < N)
    (t : I) : (γ.trans δ).subpath (pt (N + N) k) (pt (N + N) (k + 1)) t =
      γ.subpath (pt N k) (pt N (k + 1)) t := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast Nat.zero_lt_of_lt hk
  refine Path.trans_apply_of_le γ δ ?_ _ ?_
  · rw [coe_convexComb_pt (by omega : k < N + N), div_le_iff₀ (by push_cast; positivity)]
    push_cast
    have hk' : (k : ℝ) + 1 ≤ N := by exact_mod_cast hk
    linarith [t.2.2]
  · rw [coe_convexComb_pt hk, coe_convexComb_pt (by omega : k < N + N)]
    push_cast
    field_simp
    ring

private lemma trans_subpath_right {x y z : X} (γ : Path x y) (δ : Path y z) {N k : ℕ}
    (hk : k < N) (t : I) :
    (γ.trans δ).subpath (pt (N + N) (N + k)) (pt (N + N) (N + k + 1)) t =
      δ.subpath (pt N k) (pt N (k + 1)) t := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast Nat.zero_lt_of_lt hk
  refine Path.trans_apply_of_ge γ δ ?_ _ ?_
  · rw [coe_convexComb_pt (by omega : N + k < N + N), le_div_iff₀ (by push_cast; positivity)]
    push_cast
    have _ : (0 : ℝ) ≤ k := by positivity
    linarith [t.2.1]
  · rw [coe_convexComb_pt hk, coe_convexComb_pt (by omega : N + k < N + N)]
    push_cast
    field_simp
    ring

include hF in
private lemma pathVal_eq_eqToHom {x y : X} (P : Path x y) (hP : ∃ i, ∀ t, P t ∈ U i)
    (hconst : ∀ t, P t = x) :
    pathVal hU F hF P hP = eqToHom (congrArg (glueObj hU F) (P.target ▸ hconst 1).symm) := by
  obtain ⟨i, hi⟩ := hP
  rw [pathVal_eq hU F hF i P _ hi]
  exact locVal_eq_eqToHom hU F hF i P hi hconst

include hF in
/-- The value of a path: its partition value along any sufficiently fine uniform partition. -/
private def lift {x y : X} (γ : Path x y) : glueObj hU F x ⟶ glueObj hU F y :=
  liftN hU F hF γ ((exists_isFine hU γ).choose_spec _ le_rfl).2
    ((exists_isFine hU γ).choose_spec _ le_rfl).1

include hF in
private lemma lift_eq_liftN {x y : X} (γ : Path x y) {N : ℕ} (h : IsFine U γ N) (hN : N ≠ 0) :
    lift hU F hF γ = liftN hU F hF γ h hN := by
  have hspec := (exists_isFine hU γ).choose_spec
  have hN₀ := (hspec _ le_rfl).1
  rw [lift, ← liftN_mul hU F hF γ hN hN₀ _
      (hspec _ (Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero hN))).2,
    ← liftN_mul hU F hF γ hN₀ hN h (hspec _ (Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hN))).2]
  exact liftN_congr hU F hF γ (Nat.mul_comm _ _) _ _ _ _

include hF in
/-- For a path inside one member of the cover, the value is the local value. -/
private lemma lift_eq_locVal {x y : X} (γ : Path x y) (i : ι) (hγ : ∀ t, γ t ∈ U i) :
    lift hU F hF γ = locVal hU F hF i γ hγ := by
  obtain ⟨N₀, hN₀⟩ := exists_isFine hU γ
  rw [lift_eq_liftN hU F hF γ (hN₀ N₀ le_rfl).2 (hN₀ N₀ le_rfl).1, liftN_eq_locVal]

include hF in
private lemma lift_refl (x : X) : lift hU F hF (Path.refl x) = 𝟙 _ := by
  obtain ⟨i, hi⟩ := hU x
  rw [lift_eq_locVal hU F hF _ i fun _ ↦ mem_of_mem_nhds hi, locVal_refl]

include hF in
private lemma lift_trans {x y z : X} (γ : Path x y) (δ : Path y z) :
    lift hU F hF (γ.trans δ) = lift hU F hF γ ≫ lift hU F hF δ := by
  obtain ⟨N₁, h₁⟩ := exists_isFine hU γ
  obtain ⟨N₂, h₂⟩ := exists_isFine hU δ
  obtain ⟨N₃, h₃⟩ := exists_isFine hU (γ.trans δ)
  set N := N₁ + N₂ + N₃
  obtain ⟨hN, hγ⟩ := h₁ N (by omega)
  obtain ⟨-, hδ⟩ := h₂ N (by omega)
  obtain ⟨hNN, hγδ⟩ := h₃ (N + N) (by omega)
  have first : ∀ k (hk : k ≤ N),
      Functor.OfSequence.map (segVal hU F hF (γ.trans δ) hγδ) 0 k k.zero_le =
        eqToHom (by rw [pt_zero, pt_zero, Path.source, Path.source]) ≫
          Functor.OfSequence.map (segVal hU F hF γ hγ) 0 k k.zero_le ≫
            eqToHom (by rw [trans_pt_left γ δ hk]) := by
    intro k hk
    induction k with
    | zero => simp [Functor.OfSequence.map_id]
    | succ k ih =>
      rw [Functor.OfSequence.map_comp _ 0 k (k + 1) k.zero_le k.le_succ,
        Functor.OfSequence.map_comp _ 0 k (k + 1) k.zero_le k.le_succ,
        Functor.OfSequence.map_le_succ, Functor.OfSequence.map_le_succ, ih (by omega), segVal,
        segVal,
        pathVal_congr hU F hF _ _ (trans_pt_left γ δ (by omega)) (trans_pt_left γ δ hk)
          (trans_subpath_left γ δ (by omega)) _ (hγ.subpath_mem k)]
      simp
  have second : ∀ k (_ : k ≤ N),
      Functor.OfSequence.map (segVal hU F hF (γ.trans δ) hγδ) N (N + k) (N.le_add_right k) =
        eqToHom (by rw [← trans_pt_right γ δ hN 0, Nat.add_zero]) ≫
          Functor.OfSequence.map (segVal hU F hF δ hδ) 0 k k.zero_le ≫
            eqToHom (by rw [trans_pt_right γ δ hN]) := by
    intro k hk
    induction k with
    | zero => simp [Functor.OfSequence.map_id]
    | succ k ih =>
      have step : Functor.OfSequence.map (segVal hU F hF (γ.trans δ) hγδ) (N + k) (N + (k + 1))
          (by omega) = segVal hU F hF (γ.trans δ) hγδ (N + k) :=
        Functor.OfSequence.map_le_succ _ (N + k)
      rw [Functor.OfSequence.map_comp _ N (N + k) (N + (k + 1)) (N.le_add_right k) (by omega),
        Functor.OfSequence.map_comp _ 0 k (k + 1) k.zero_le k.le_succ, step,
        Functor.OfSequence.map_le_succ, ih (by omega), segVal,
        segVal, pathVal_congr hU F hF _ _ (trans_pt_right γ δ hN k)
          (trans_pt_right γ δ hN (k + 1)) (trans_subpath_right γ δ (by omega)) _
          (hδ.subpath_mem k)]
      simp
  rw [lift_eq_liftN hU F hF _ hγδ hNN, lift_eq_liftN hU F hF _ hγ hN,
    lift_eq_liftN hU F hF _ hδ hN, liftN, liftN, liftN,
    Functor.OfSequence.map_comp _ 0 N (N + N) N.zero_le (N.le_add_right N), first N le_rfl,
    second N le_rfl]
  simp

/-- A path traced by a homotopy of paths: the `k`-th partition point, while the homotopy
parameter runs through the `l`-th piece of the uniform partition into `N` pieces. -/
private def colSeg {x y : X} {p q : Path x y} (H : p.Homotopy q) (N l k : ℕ) :
    Path (H.eval (pt N l) (pt N k)) (H.eval (pt N (l + 1)) (pt N k)) where
  toFun u := H (Icc.convexComb (pt N l) (pt N (l + 1)) u, pt N k)
  continuous_toFun := H.continuous.comp ((Icc.continuous_convexComb _ _).prodMk continuous_const)
  source' := by simp
  target' := by simp

private lemma convexComb_mem_Icc_pt (N k : ℕ) (u : I) :
    Icc.convexComb (pt N k) (pt N (k + 1)) u ∈ Icc (pt N k) (pt N (k + 1)) :=
  ⟨Icc.le_convexComb (pt_mono N k.le_succ) u, Icc.convexComb_le (pt_mono N k.le_succ) u⟩

include hF in
/-- The values along the boundary of one cell of a homotopy of paths satisfy the square relation
of the cell. -/
private lemma pathVal_cell {x y : X} {p q : Path x y} (H : p.Homotopy q) (N l k : ℕ) (i : ι)
    (hi : ∀ t ∈ Icc (pt N l) (pt N (l + 1)), ∀ s ∈ Icc (pt N k) (pt N (k + 1)), H (t, s) ∈ U i)
    (h₁ : ∃ i, ∀ t, (H.eval (pt N l)).subpath (pt N k) (pt N (k + 1)) t ∈ U i)
    (h₂ : ∃ i, ∀ t, colSeg H N l (k + 1) t ∈ U i) (h₃ : ∃ i, ∀ t, colSeg H N l k t ∈ U i)
    (h₄ : ∃ i, ∀ t, (H.eval (pt N (l + 1))).subpath (pt N k) (pt N (k + 1)) t ∈ U i) :
    pathVal hU F hF _ h₁ ≫ pathVal hU F hF _ h₂ = pathVal hU F hF _ h₃ ≫ pathVal hU F hF _ h₄ := by
  have : ContractibleSpace I := (convex_Icc (0 : ℝ) 1).contractibleSpace ⟨0, by simp⟩
  have m₁ : ∀ t, (H.eval (pt N l)).subpath (pt N k) (pt N (k + 1)) t ∈ U i := fun t ↦ by
    simpa [Path.subpath] using hi _ mem_Icc_pt _ (convexComb_mem_Icc_pt N k t)
  have m₂ : ∀ t, colSeg H N l (k + 1) t ∈ U i := fun t ↦
    hi _ (convexComb_mem_Icc_pt N l t) _ mem_Icc_pt_succ
  have m₃ : ∀ t, colSeg H N l k t ∈ U i := fun t ↦
    hi _ (convexComb_mem_Icc_pt N l t) _ mem_Icc_pt
  have m₄ : ∀ t, (H.eval (pt N (l + 1))).subpath (pt N k) (pt N (k + 1)) t ∈ U i := fun t ↦ by
    simpa [Path.subpath] using hi _ mem_Icc_pt_succ _ (convexComb_mem_Icc_pt N k t)
  rw [pathVal_eq hU F hF i _ _ m₁, pathVal_eq hU F hF i _ _ m₂, pathVal_eq hU F hF i _ _ m₃,
    pathVal_eq hU F hF i _ _ m₄, ← locVal_trans hU F hF i _ _ m₁ m₂ (range_subset_iff.1 <|
      (Path.trans_range _ _).trans_subset <| union_subset (range_subset_iff.2 m₁)
        (range_subset_iff.2 m₂)),
    ← locVal_trans hU F hF i _ _ m₃ m₄ (range_subset_iff.1 <|
      (Path.trans_range _ _).trans_subset <| union_subset (range_subset_iff.2 m₃)
        (range_subset_iff.2 m₄))]
  -- Both composites are images of paths from `(0, 0)` to `(1, 1)` in the square `I × I` under the
  -- affine parametrisation of the cell by the square.
  let g : C(I × I, X) := H.toContinuousMap.comp
    ((ContinuousMap.mk _ (Icc.continuous_convexComb (pt N l) (pt N (l + 1)))).prodMap
      (ContinuousMap.mk _ (Icc.continuous_convexComb (pt N k) (pt N (k + 1)))))
  refine locVal_eq_of_simplyConnected hU F hF i g
    (fun z ↦ hi _ (convexComb_mem_Icc_pt N l z.1) _ (convexComb_mem_Icc_pt N k z.2))
    (((Path.refl 0).trans Path.id).prod (Path.id.trans (Path.refl 1)))
    ((Path.id.trans (Path.refl 1)).prod ((Path.refl 0).trans Path.id)) _ _ (fun t ↦ ?_)
    (fun t ↦ ?_) _ _ <;>
  · rw [Path.trans_apply]
    split_ifs with h <;> rw [one_div] at h <;> simp [g, colSeg, Path.subpath, Path.trans_apply, h]

include hF in
/-- Homotopic paths have the same value. -/
private lemma lift_eq_of_homotopy {x y : X} {p q : Path x y} (H : p.Homotopy q) :
    lift hU F hF p = lift hU F hF q := by
  obtain ⟨N, hN, hcell⟩ := exists_isFine_homotopy hU H
  have hrow : ∀ l, IsFine U (H.eval (pt N l)) N := fun l k ↦
    (hcell l k).imp fun i hi s hs ↦ by simpa using hi _ mem_Icc_pt s hs
  have hcol : ∀ l k, ∃ i, ∀ t, colSeg H N l k t ∈ U i := fun l k ↦
    (hcell l k).imp fun i hi t ↦ hi _ (convexComb_mem_Icc_pt N l t) _ mem_Icc_pt
  have hstep : ∀ l, liftN hU F hF _ (hrow l) hN = liftN hU F hF _ (hrow (l + 1)) hN := by
    intro l
    -- The values of the columns of the `l`-th row of cells form a natural transformation between
    -- the sequences of segment values along its two sides.
    have hsq : Functor.OfSequence.map (segVal hU F hF _ (hrow l)) 0 N N.zero_le ≫
        pathVal hU F hF (colSeg H N l N) (hcol l N) =
          pathVal hU F hF (colSeg H N l 0) (hcol l 0) ≫
            Functor.OfSequence.map (segVal hU F hF _ (hrow (l + 1))) 0 N N.zero_le :=
      (NatTrans.ofSequence (F := Functor.ofSequence (segVal hU F hF _ (hrow l)))
        (G := Functor.ofSequence (segVal hU F hF _ (hrow (l + 1))))
        (fun k ↦ pathVal hU F hF (colSeg H N l k) (hcol l k)) fun k ↦ by
          obtain ⟨i, hi⟩ := hcell l k
          rw [Functor.ofSequence_map_homOfLE_succ, Functor.ofSequence_map_homOfLE_succ]
          exact pathVal_cell hU F hF H N l k i hi _ _ _ _).naturality (homOfLE N.zero_le)
    rw [pathVal_eq_eqToHom hU F hF (colSeg H N l 0) _ fun t ↦ by simp [colSeg, pt_zero],
      pathVal_eq_eqToHom hU F hF (colSeg H N l N) _ fun t ↦ by simp [colSeg, pt_self hN],
      comp_eqToHom_iff] at hsq
    rw [liftN, liftN, hsq]
    simp
  have hall : ∀ l, liftN hU F hF _ (hrow 0) hN = liftN hU F hF _ (hrow l) hN := fun l ↦ by
    induction l with
    | zero => rfl
    | succ l ih => exact ih.trans (hstep l)
  calc lift hU F hF p = lift hU F hF (H.eval (pt N 0)) := by rw [pt_zero, Path.Homotopy.eval_zero]
    _ = lift hU F hF (H.eval (pt N N)) := by
      rw [lift_eq_liftN hU F hF _ (hrow 0) hN, lift_eq_liftN hU F hF _ (hrow N) hN, hall N]
    _ = lift hU F hF q := by rw [pt_self hN, Path.Homotopy.eval_one]

/-- **Gluing functors out of fundamental groupoids.** Let every point of `X` have some `U i` as a
neighbourhood, and let `F i` be functors out of the fundamental groupoids of the sets `U i` which
agree on the fundamental groupoids of the pairwise intersections. This is the functor out of the
fundamental groupoid of `X` which restricts to every `F i`
(`TauCeti.FundamentalGroupoid.map_subtypeVal_comp_glue`); it is the unique such functor
(`TauCeti.FundamentalGroupoid.eq_glue`). -/
def glue : _root_.FundamentalGroupoid X ⥤ D where
  obj x := glueObj hU F x.as
  map {x y} := Quotient.lift (lift hU F hF (x := x.as) (y := y.as))
    fun _ _ h ↦ lift_eq_of_homotopy hU F hF h.some
  map_id x := lift_refl hU F hF x.as
  map_comp := by
    rintro _ _ _ ⟨γ⟩ ⟨δ⟩
    exact lift_trans hU F hF γ δ

/-- The glued functor restricts to `F i` on the fundamental groupoid of `U i`. -/
@[simp] theorem map_subtypeVal_comp_glue (i : ι) :
    map (ContinuousMap.subtypeVal (U i)) ⋙ glue hU F hF = F i := by
  refine CategoryTheory.Functor.ext (fun a ↦ (obj_eq hU F hF i a.as.2).symm) fun a b γ ↦ ?_
  induction γ using Path.Homotopic.Quotient.ind with | mk γ =>
  let γ' := γ.map continuous_subtype_val
  have hγ' : ∀ t, γ' t ∈ U i := fun t ↦ (γ t).2
  have hγ : γ'.codRestrict (x := a.as) (y := b.as) hγ' = γ := by
    ext t
    exact Path.codRestrict_coe (x := a.as) (y := b.as) _ _ t
  have key : locVal hU F hF i γ' hγ' = eqToHom (obj_eq hU F hF i a.as.2).symm ≫
      (F i).map (Path.Homotopic.Quotient.mk γ) ≫ eqToHom (obj_eq hU F hF i b.as.2) := by
    unfold locVal
    rw [hγ]
  -- By the definitions of `FundamentalGroupoid.map` and of `glue`, the left-hand side is the
  -- value `lift hU F hF γ'` of the image path `γ'`.
  exact (lift_eq_locVal hU F hF γ' i hγ').trans key

/-- On objects, the glued functor agrees with each `F i`. -/
theorem glue_obj_mk (i : ι) {x : X} (hx : x ∈ U i) :
    (glue hU F hF).obj (mk x) = (F i).obj (mk ⟨x, hx⟩) :=
  Functor.congr_obj (map_subtypeVal_comp_glue hU F hF i) (mk ⟨x, hx⟩)

/-- A functor out of the fundamental groupoid of `X` which restricts to `F i` on the fundamental
groupoid of every `U i` is the glued functor. -/
theorem eq_glue {G : _root_.FundamentalGroupoid X ⥤ D}
    (hG : ∀ i, map (ContinuousMap.subtypeVal (U i)) ⋙ G = F i) : G = glue hU F hF :=
  functor_ext hU fun i ↦ (hG i).trans (map_subtypeVal_comp_glue hU F hF i).symm

end Construction

end TauCeti.FundamentalGroupoid
