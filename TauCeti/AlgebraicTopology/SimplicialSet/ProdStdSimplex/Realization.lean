/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Convex.ConvexSpace.CompactSpaceStdSimplex
public import TauCeti.AlgebraicTopology.SimplicialSet.PrismRealization

import Mathlib.Data.Finset.Sort
import Mathlib.Order.Fin.Prod
import TauCeti.Algebra.BigOperators.Finset.PartialSum
import TauCeti.AlgebraicTopology.SimplicialSet.ProdStdSimplex.Basic
import TauCeti.Geometry.Convex.ConvexSpace.Defs

/-!
# Geometric realization of binary products of standard simplices

The canonical projection morphism `|Δ[p] ⊗ Δ[q]| ⟶ |Δ[p]| ⊗ |Δ[q]|` in `TopCat` is an isomorphism,
giving a homeomorphism `SSet.prodStdSimplex.toTopHomeo` between `|Δ[p] ⊗ Δ[q]|` and the product of
standard topological simplices `StdSimplex ℝ (Fin (p + 1)) × StdSimplex ℝ (Fin (q + 1))`.

Geometrically, the Eilenberg–Zilber shuffle simplices — the nondegenerate `(p + q)`-simplices of
`Δ[p] ⊗ Δ[q]` — triangulate the product `StdSimplex ℝ (Fin (p + 1)) × StdSimplex ℝ (Fin (q + 1))`.
Rather than enumerating shuffle paths directly, we describe the inverse map intrinsically via the
comonotone (or Fréchet–Hoeffding) coupling of barycentric weight distributions:

* Given `s : StdSimplex ℝ (Fin (p + 1))` and `t : StdSimplex ℝ (Fin (q + 1))`, the weight assigned
  to a vertex `(i, j) : Fin (p + 1) × Fin (q + 1)` is the length of the intersection of the
  cumulative-weight intervals `[s₀ + ⋯ + s_(i-1), s₀ + ⋯ + s_i]` and
  `[t₀ + ⋯ + t_(j-1), t₀ + ⋯ + t_j]`.
* The sum of these weights over any lower rectangle `Finset.Iic (i, j)` telescopes to
  `min (prefixSum (i + 1) s.weights) (prefixSum (j + 1) t.weights)`, showing both that the coupling
  has marginals `s` and `t` and that every simplex `x` of `Δ[p] ⊗ Δ[q]` pushes any barycentric
  weight `w` forward to the coupling of its two marginals (`map_objEquiv_eq_coupling`).
* Because overlapping subintervals of `[0, 1]` are linearly ordered when neither can skip past the
  other in both coordinates, the support of the coupling is a chain in
  `Fin (p + 1) × Fin (q + 1)`, hence lies in the vertex set of a nondegenerate `(p + q)`-simplex
  of `Δ[p] ⊗ Δ[q]` by `SSet.prodStdSimplex.exists_nonDegenerate_max_dim`.
* Gluing over the finitely many closed pieces indexed by the nondegenerate `(p + q)`-simplices via
  `SSet.prodStdSimplex.toTopObjMk_eq_of_map_eq` yields the continuous inverse
  `SSet.prodStdSimplex.triangulate`.

## Main declarations

* `SimplexCategory.toTopHomeo_toTopObjMk`: `⦋p⦌.toTopHomeo` sends `SSet.toTopObjMk a w` to
  `w.map (SSet.stdSimplex.objEquiv a)`.
* `SSet.prodStdSimplex.triangulate`: the continuous triangulation map
  `C(StdSimplex ℝ (Fin (p + 1)) × StdSimplex ℝ (Fin (q + 1)), |Δ[p] ⊗ Δ[q]|)`.
* `SSet.prodStdSimplex.toTopHomeo`: the homeomorphism
  `|Δ[p] ⊗ Δ[q]| ≃ₜ StdSimplex ℝ (Fin (p + 1)) × StdSimplex ℝ (Fin (q + 1))`.
* `SSet.prodStdSimplex.instIsIsoCartesianProdComparison`,
  `SSet.prodStdSimplex.instPreservesLimitPairToTop`: `SSet.toTop` preserves the binary product
  `Δ[p] ⨯ Δ[q]`.

## References

* S. Eilenberg and J. A. Zilber, *On products of complexes*, Amer. J. Math. 75 (1953), 200–204.
* J. Milnor, *The geometric realization of a semi-simplicial complex*, Ann. of Math. 65 (1957),
  357–362, Lemma 2.
-/

public section

open CategoryTheory Limits MonoidalCategory Opposite Convexity Simplicial
open TauCeti (prefixSum)

universe u

namespace SimplexCategory

/-- Under `SimplexCategory.toTopHomeo`, the point `SSet.toTopObjMk a w` of `|Δ[p]|` determined by an
`n`-simplex `a` and barycentric coordinates `w` corresponds to pushing `w` forward along the vertex
map of `a`. -/
@[simp]
theorem toTopHomeo_toTopObjMk {p n : ℕ} (a : (Δ[p] : SSet.{u}) _⦋n⦌)
    (w : StdSimplex ℝ (Fin (n + 1))) :
    ⦋p⦌.toTopHomeo (SSet.toTopObjMk a w) = w.map (SSet.stdSimplex.objEquiv a) := by
  have hunit := sSetTopAdj_unit_app_app_down Δ[p] (op ⦋n⦌) a
  rw [SSet.yonedaEquiv.symm_apply_eq.2
    (by rw [SSet.yonedaEquiv_map, Equiv.symm_apply_apply])] at hunit
  -- Evaluate `hunit` at `ULift.up w` to identify `toTopObjMk a w`.
  rw [SSet.toTopObjMk_def,
    show TopCat.toSSetObjEquiv _ _ ((sSetTopAdj.unit.app Δ[p]).app (op ⦋n⦌) a) w =
      SSet.toTop.map (SSet.stdSimplex.map (SSet.stdSimplex.objEquiv a)) (⦋n⦌.toTopHomeo.symm w)
    from ConcreteCategory.congr_hom hunit (ULift.up w),
    toTopHomeo_naturality_apply, Homeomorph.apply_symm_apply]

/-- The inverse of `SimplexCategory.toTopHomeo ⦋p⦌` sends `s` to the point of the identity
`p`-simplex with barycentric coordinates `s`. -/
theorem toTopHomeo_symm_apply {p : ℕ} (s : StdSimplex ℝ (Fin (p + 1))) :
    ⦋p⦌.toTopHomeo.symm s = SSet.toTopObjMk (SSet.stdSimplex.objEquiv.symm (𝟙 ⦋p⦌)) s := by
  apply ⦋p⦌.toTopHomeo.injective
  rw [Homeomorph.apply_symm_apply, toTopHomeo_toTopObjMk, Equiv.apply_symm_apply]
  exact (StdSimplex.map_id s).symm

end SimplexCategory

namespace SSet

/-- The geometric realization of a standard simplex is compact. -/
instance stdSimplex.instCompactSpaceToTopObj (p : ℕ) : CompactSpace |(Δ[p] : SSet.{u})| :=
  ⦋p⦌.toTopHomeo.symm.compactSpace

/-- The geometric realization of a standard simplex is Hausdorff. -/
instance stdSimplex.instT2SpaceToTopObj (p : ℕ) : T2Space |(Δ[p] : SSet.{u})| :=
  ⦋p⦌.toTopHomeo.symm.t2Space

/-- The geometric realization of a standard simplex is locally compact. -/
instance stdSimplex.instLocallyCompactSpaceToTopObj (p : ℕ) :
    LocallyCompactSpace |(Δ[p] : SSet.{u})| :=
  inferInstance

namespace prodStdSimplex

variable {p q : ℕ}

/-- The length of the intersection `[a, a'] ∩ [b, b']` of two intervals `a ≤ a'` and `b ≤ b'`
equals the two-dimensional difference of `(u, v) ↦ min u v` across `[a, a'] × [b, b']`. -/
private lemma max_zero_min_sub_max {a a' b b' : ℝ} (ha : a ≤ a') (hb : b ≤ b') :
    max 0 (min a' b' - max a b) = min a' b' - min a b' - min a' b + min a b := by
  rcases le_total a' b with h₁ | h₁
  · rw [min_eq_left (h₁.trans hb), max_eq_right (ha.trans h₁), max_eq_left (by linarith),
      min_eq_left (ha.trans (h₁.trans hb)), min_eq_left h₁, min_eq_left (ha.trans h₁)]
    ring
  · rcases le_total b' a with h₂ | h₂
    · rw [min_eq_right (h₂.trans ha), max_eq_left (hb.trans h₂), max_eq_left (by linarith),
        min_eq_right h₂, min_eq_right (hb.trans (h₂.trans ha)), min_eq_right (hb.trans h₂)]
      ring
    · have hmax : max a b ≤ min a' b' := max_le (le_min ha h₂) (le_min h₁ hb)
      rw [max_eq_right (sub_nonneg.2 hmax), min_eq_left h₂, min_eq_right h₁]
      linarith [min_add_max a b]

/-- The comonotone coupling weights on `Fin (p + 1) × Fin (q + 1)` associated to barycentric
coordinates `s` on `Fin (p + 1)` and `t` on `Fin (q + 1)`: the overlap length of the `i`th
cumulative-weight interval of `s` with the `j`th cumulative-weight interval of `t`. -/
private noncomputable def couplingWeights (s : StdSimplex ℝ (Fin (p + 1)))
    (t : StdSimplex ℝ (Fin (q + 1))) (x : Fin (p + 1) × Fin (q + 1)) : ℝ :=
  max 0 (min (prefixSum (x.1.val + 1) s.weights) (prefixSum (x.2.val + 1) t.weights) -
    max (prefixSum x.1.val s.weights) (prefixSum x.2.val t.weights))

@[fun_prop]
private lemma continuous_couplingWeights (x : Fin (p + 1) × Fin (q + 1)) :
    Continuous fun z : StdSimplex ℝ (Fin (p + 1)) × StdSimplex ℝ (Fin (q + 1)) ↦
      couplingWeights z.1 z.2 x := by
  unfold couplingWeights
  fun_prop

private lemma couplingWeights_eq_sub (s : StdSimplex ℝ (Fin (p + 1)))
    (t : StdSimplex ℝ (Fin (q + 1))) (i : Fin (p + 1)) (j : Fin (q + 1)) :
    couplingWeights s t (i, j) =
      (min (prefixSum (i.val + 1) s.weights) (prefixSum (j.val + 1) t.weights) -
        min (prefixSum i.val s.weights) (prefixSum (j.val + 1) t.weights)) -
      (min (prefixSum (i.val + 1) s.weights) (prefixSum j.val t.weights) -
        min (prefixSum i.val s.weights) (prefixSum j.val t.weights)) := by
  have h := max_zero_min_sub_max
    (TauCeti.monotone_prefixSum s.nonneg (Nat.le_succ i.val))
    (TauCeti.monotone_prefixSum t.nonneg (Nat.le_succ j.val))
  unfold couplingWeights
  linarith

/-- Summing `couplingWeights s t` over a lower rectangle `{i | i < K} × {j | j < L}` telescopes in
both coordinates to `min (prefixSum K s.weights) (prefixSum L t.weights)`. -/
private lemma sum_couplingWeights_lt (s : StdSimplex ℝ (Fin (p + 1)))
    (t : StdSimplex ℝ (Fin (q + 1))) (K L : ℕ) :
    (∑ i : Fin (p + 1) with i.val < K, ∑ j : Fin (q + 1) with j.val < L,
      couplingWeights s t (i, j)) =
      min (prefixSum K s.weights) (prefixSum L t.weights) := by
  have hinner (i : Fin (p + 1)) :
      (∑ j : Fin (q + 1) with j.val < L, couplingWeights s t (i, j)) =
        min (prefixSum (i.val + 1) s.weights) (prefixSum L t.weights) -
          min (prefixSum i.val s.weights) (prefixSum L t.weights) := by
    simp_rw [couplingWeights_eq_sub]
    rw [TauCeti.sum_sub_prefixSum
      (fun v ↦ min (prefixSum (i.val + 1) s.weights) v - min (prefixSum i.val s.weights) v)
      L t.weights]
    simp [min_eq_right (StdSimplex.prefixSum_weights_nonneg s _)]
  simp_rw [hinner]
  rw [TauCeti.sum_sub_prefixSum (fun u ↦ min u (prefixSum L t.weights)) K s.weights]
  simp [min_eq_left (StdSimplex.prefixSum_weights_nonneg t _)]

private lemma sum_couplingWeights (s : StdSimplex ℝ (Fin (p + 1)))
    (t : StdSimplex ℝ (Fin (q + 1))) :
    ∑ x, couplingWeights s t x = 1 := by
  have h := sum_couplingWeights_lt s t (p + 1) (q + 1)
  have hi : (Finset.univ.filter fun i : Fin (p + 1) ↦ i.val < p + 1) = Finset.univ :=
    Finset.filter_true_of_mem fun i _ ↦ i.isLt
  have hj : (Finset.univ.filter fun j : Fin (q + 1) ↦ j.val < q + 1) = Finset.univ :=
    Finset.filter_true_of_mem fun j _ ↦ j.isLt
  simp_rw [hi, hj] at h
  rw [TauCeti.prefixSum_of_le le_rfl, StdSimplex.total_of_fintype,
    TauCeti.prefixSum_of_le le_rfl, StdSimplex.total_of_fintype, min_self] at h
  rwa [Fintype.sum_prod_type]

/-- The comonotone coupling of `s : StdSimplex ℝ (Fin (p + 1))` and
`t : StdSimplex ℝ (Fin (q + 1))` as a point of `StdSimplex ℝ (Fin (p + 1) × Fin (q + 1))`. -/
private noncomputable def coupling (s : StdSimplex ℝ (Fin (p + 1)))
    (t : StdSimplex ℝ (Fin (q + 1))) : StdSimplex ℝ (Fin (p + 1) × Fin (q + 1)) where
  weights := Finsupp.equivFunOnFinite.symm (couplingWeights s t)
  nonneg _ := le_max_left 0 _
  total := by
    rw [Finsupp.sum_fintype _ _ (by simp)]
    exact sum_couplingWeights s t

private lemma coupling_weights (s : StdSimplex ℝ (Fin (p + 1)))
    (t : StdSimplex ℝ (Fin (q + 1))) (x : Fin (p + 1) × Fin (q + 1)) :
    (coupling s t).weights x = couplingWeights s t x :=
  (rfl)

private lemma sum_Iic_coupling (s : StdSimplex ℝ (Fin (p + 1)))
    (t : StdSimplex ℝ (Fin (q + 1))) (u : Fin (p + 1) × Fin (q + 1)) :
    (∑ x ∈ Finset.Iic u, (coupling s t).weights x) =
      min (prefixSum (u.1.val + 1) s.weights) (prefixSum (u.2.val + 1) t.weights) := by
  rw [← sum_couplingWeights_lt s t (u.1.val + 1) (u.2.val + 1), ← Finset.sum_product']
  refine Finset.sum_congr ?_ fun _ _ ↦ rfl
  ext ⟨i, j⟩
  simp only [Finset.mem_Iic, Prod.le_def, Finset.mem_product, Finset.mem_filter,
    Finset.mem_univ, true_and, Fin.le_def]
  omega

/-- The first marginal of `coupling s t` is `s`. -/
private lemma map_fst_coupling (s : StdSimplex ℝ (Fin (p + 1)))
    (t : StdSimplex ℝ (Fin (q + 1))) :
    (coupling s t).map Prod.fst = s := by
  rw [← StdSimplex.weights_inj, DFunLike.ext_iff, ← funext_iff]
  refine TauCeti.eq_of_forall_prefixSum_eq fun K ↦ ?_
  rw [TauCeti.prefixSum_def, StdSimplex.sum_filter_weights_map Prod.fst (coupling s t)
    (fun i ↦ i.val < K)]
  have h : (Finset.univ.filter fun x : Fin (p + 1) × Fin (q + 1) ↦ x.1.val < K) =
      (Finset.univ.filter fun i : Fin (p + 1) ↦ i.val < K) ×ˢ Finset.univ := by
    ext ⟨i, j⟩
    simp
  rw [h, Finset.sum_product]
  simp_rw [coupling_weights]
  have hrect := sum_couplingWeights_lt s t K (q + 1)
  have hfilt : (Finset.univ.filter fun j : Fin (q + 1) ↦ j.val < q + 1) = Finset.univ :=
    Finset.filter_true_of_mem fun j _ ↦ j.isLt
  simp_rw [hfilt] at hrect
  rwa [TauCeti.prefixSum_of_le le_rfl, StdSimplex.total_of_fintype,
    min_eq_left (StdSimplex.prefixSum_weights_le_one s K)] at hrect

/-- The second marginal of `coupling s t` is `t`. -/
private lemma map_snd_coupling (s : StdSimplex ℝ (Fin (p + 1)))
    (t : StdSimplex ℝ (Fin (q + 1))) :
    (coupling s t).map Prod.snd = t := by
  rw [← StdSimplex.weights_inj, DFunLike.ext_iff, ← funext_iff]
  refine TauCeti.eq_of_forall_prefixSum_eq fun L ↦ ?_
  rw [TauCeti.prefixSum_def, StdSimplex.sum_filter_weights_map Prod.snd (coupling s t)
    (fun j ↦ j.val < L)]
  have h : (Finset.univ.filter fun x : Fin (p + 1) × Fin (q + 1) ↦ x.2.val < L) =
      Finset.univ ×ˢ (Finset.univ.filter fun j : Fin (q + 1) ↦ j.val < L) := by
    ext ⟨i, j⟩
    simp
  rw [h, Finset.sum_product]
  simp_rw [coupling_weights]
  have hrect := sum_couplingWeights_lt s t (p + 1) L
  have hfilt : (Finset.univ.filter fun i : Fin (p + 1) ↦ i.val < p + 1) = Finset.univ :=
    Finset.filter_true_of_mem fun i _ ↦ i.isLt
  simp_rw [hfilt] at hrect
  rwa [TauCeti.prefixSum_of_le le_rfl, StdSimplex.total_of_fintype,
    min_eq_right (StdSimplex.prefixSum_weights_le_one t L)] at hrect

/-- For a morphism `f : ⦋n⦌ ⟶ ⦋m⦌` in `SimplexCategory`, the preimage of `{i | i < N}` is an
initial segment `{k | k < a}` whose prefix sum equals `prefixSum N (w.map f).weights`. -/
private lemma exists_lt_iff_and_prefixSum_map {n m : ℕ} (f : ⦋n⦌ ⟶ ⦋m⦌)
    (w : StdSimplex ℝ (Fin (n + 1))) (N : ℕ) :
    ∃ a : ℕ, (∀ k : Fin (n + 1), (f k).val < N ↔ k.val < a) ∧
      prefixSum N (w.map f).weights = prefixSum a w.weights := by
  have hs : IsLowerSet {k | (f k).val < N} := fun _ _ h hk ↦
    (Fin.le_def.1 (f.toOrderHom.monotone h)).trans_lt hk
  obtain ⟨a, ha⟩ : ∃ a : ℕ, ∀ k : Fin (n + 1), (f k).val < N ↔ k.val < a := by
    rcases hs.eq_univ_or_Iio with h | ⟨a, h⟩
    · exact ⟨n + 1, fun k ↦ ⟨fun _ ↦ k.isLt, fun _ ↦ (Set.ext_iff.1 h k).2 (Set.mem_univ k)⟩⟩
    · exact ⟨a, fun k ↦ (Set.ext_iff.1 h k).trans (Set.mem_Iio.trans Fin.lt_def)⟩
  refine ⟨a, ha, ?_⟩
  rw [TauCeti.prefixSum_def, StdSimplex.sum_filter_weights_map f w (fun i ↦ i.val < N),
    TauCeti.prefixSum_def]
  exact Finset.sum_congr (Finset.filter_congr fun k _ ↦ ha k) fun _ _ ↦ rfl

/-- Any simplex `x` of `Δ[p] ⊗ Δ[q]` pushes barycentric weights `w` forward to the comonotone
coupling of the two coordinate marginals of `w`. -/
private lemma map_objEquiv_eq_coupling {n : ℕ} (x : (Δ[p] : SSet.{u}) _⦋n⦌ ⊗ Δ[q] _⦋n⦌)
    (w : StdSimplex ℝ (Fin (n + 1))) :
    w.map (objEquiv x) =
      coupling (w.map (stdSimplex.objEquiv x.1)) (w.map (stdSimplex.objEquiv x.2)) := by
  have hzero : (fun u ↦ (w.map (objEquiv x)).weights u -
      (coupling (w.map (stdSimplex.objEquiv x.1)) (w.map (stdSimplex.objEquiv x.2))).weights u) =
      0 :=
    TauCeti.eq_zero_of_forall_sum_Iic_eq_zero fun u ↦ by
      simp only [Finset.sum_sub_distrib, sub_eq_zero]
      rw [sum_Iic_coupling]
      obtain ⟨a, ha, hpa⟩ :=
        exists_lt_iff_and_prefixSum_map (stdSimplex.objEquiv x.1) w (u.1.val + 1)
      obtain ⟨b, hb, hpb⟩ :=
        exists_lt_iff_and_prefixSum_map (stdSimplex.objEquiv x.2) w (u.2.val + 1)
      have hIic :
          Finset.Iic u = Finset.univ.filter (fun z : Fin (p + 1) × Fin (q + 1) ↦ z ≤ u) := by
        ext z
        simp
      rw [hIic, StdSimplex.sum_filter_weights_map (objEquiv x) w (fun z ↦ z ≤ u), hpa, hpb,
        ← (TauCeti.monotone_prefixSum w.nonneg).map_min, TauCeti.prefixSum_def]
      refine Finset.sum_congr (Finset.filter_congr fun k _ ↦ ?_) fun _ _ ↦ rfl
      simp only [Prod.le_def, objEquiv_apply_fst, objEquiv_apply_snd, Fin.le_def, lt_min_iff]
      exact ⟨fun ⟨h₁, h₂⟩ ↦ ⟨(ha k).1 (Nat.lt_succ_of_le h₁), (hb k).1 (Nat.lt_succ_of_le h₂)⟩,
        fun ⟨h₁, h₂⟩ ↦ ⟨Nat.le_of_lt_succ ((ha k).2 h₁), Nat.le_of_lt_succ ((hb k).2 h₂)⟩⟩
  ext u
  exact sub_eq_zero.1 (congrFun hzero u)

/-- The support of `coupling s t` is a chain in `Fin (p + 1) × Fin (q + 1)`. -/
private lemma isChain_support_coupling (s : StdSimplex ℝ (Fin (p + 1)))
    (t : StdSimplex ℝ (Fin (q + 1))) :
    IsChain (· ≤ ·) ((coupling s t).weights.support : Set (Fin (p + 1) × Fin (q + 1))) := by
  intro u hu v hv _
  simp only [Finset.mem_coe, Finsupp.mem_support_iff, coupling_weights] at hu hv
  have hu' : max (prefixSum u.1.val s.weights) (prefixSum u.2.val t.weights) <
      min (prefixSum (u.1.val + 1) s.weights) (prefixSum (u.2.val + 1) t.weights) := by
    by_contra! h
    exact hu (max_eq_left (sub_nonpos.2 h))
  have hv' : max (prefixSum v.1.val s.weights) (prefixSum v.2.val t.weights) <
      min (prefixSum (v.1.val + 1) s.weights) (prefixSum (v.2.val + 1) t.weights) := by
    by_contra! h
    exact hv (max_eq_left (sub_nonpos.2 h))
  have hms := TauCeti.monotone_prefixSum s.nonneg
  have hmt := TauCeti.monotone_prefixSum t.nonneg
  by_cases hle : u ≤ v
  · exact Or.inl hle
  · refine Or.inr ?_
    rw [Prod.le_def, not_and_or] at hle
    rcases hle with h₁ | h₂
    · replace h₁ : v.1 < u.1 := not_le.1 h₁
      have hstep : prefixSum (v.1.val + 1) s.weights ≤ prefixSum u.1.val s.weights :=
        hms (Nat.succ_le_of_lt h₁)
      have hlt : prefixSum v.2.val t.weights < prefixSum (u.2.val + 1) t.weights :=
        lt_of_lt_of_le (lt_of_le_of_lt (le_max_right _ _) hv')
          ((min_le_left _ _).trans (hstep.trans ((le_max_left _ _).trans
            (le_of_lt (lt_of_lt_of_le hu' (min_le_right _ _))))))
      refine ⟨h₁.le, ?_⟩
      by_contra! h₂
      exact not_le_of_gt hlt (hmt (Nat.succ_le_of_lt h₂))
    · replace h₂ : v.2 < u.2 := not_le.1 h₂
      have hstep : prefixSum (v.2.val + 1) t.weights ≤ prefixSum u.2.val t.weights :=
        hmt (Nat.succ_le_of_lt h₂)
      have hlt : prefixSum v.1.val s.weights < prefixSum (u.1.val + 1) s.weights :=
        lt_of_lt_of_le (lt_of_le_of_lt (le_max_left _ _) hv')
          ((min_le_right _ _).trans (hstep.trans ((le_max_right _ _).trans
            (le_of_lt (lt_of_lt_of_le hu' (min_le_left _ _))))))
      refine ⟨?_, h₂.le⟩
      by_contra! h₁
      exact not_le_of_gt hlt (hms (Nat.succ_le_of_lt h₁))

/-- The closed piece of `StdSimplex ℝ (Fin (p + 1)) × StdSimplex ℝ (Fin (q + 1))` covered by a
nondegenerate `(p + q)`-simplex `σ` of `Δ[p] ⊗ Δ[q]`. -/
private def piece (σ : (Δ[p] ⊗ Δ[q] : SSet.{u}).nonDegenerate (p + q)) :
    Set (StdSimplex ℝ (Fin (p + 1)) × StdSimplex ℝ (Fin (q + 1))) :=
  {z | ∀ x ∉ Set.range (objEquiv σ.val), couplingWeights z.1 z.2 x = 0}

private lemma isClosed_piece (σ : (Δ[p] ⊗ Δ[q] : SSet.{u}).nonDegenerate (p + q)) :
    IsClosed (piece σ) := by
  have h : piece σ = ⋂ (x : Fin (p + 1) × Fin (q + 1)) (_ : x ∉ Set.range (objEquiv σ.val)),
      {z | couplingWeights z.1 z.2 x = 0} := by
    ext z
    simp [piece]
  rw [h]
  exact isClosed_iInter fun x ↦ isClosed_iInter fun _ ↦
    isClosed_eq (continuous_couplingWeights x) continuous_const

private lemma support_coupling_subset {σ : (Δ[p] ⊗ Δ[q] : SSet.{u}).nonDegenerate (p + q)}
    {z : StdSimplex ℝ (Fin (p + 1)) × StdSimplex ℝ (Fin (q + 1))} (hz : z ∈ piece σ) :
    ↑(coupling z.1 z.2).weights.support ⊆ Set.range (objEquiv σ.val) := by
  intro x hx
  by_contra hnot
  exact Finsupp.mem_support_iff.1 hx (hz x hnot)

/-- Every point of the product of standard simplices lies in `piece σ` for some nondegenerate
`(p + q)`-simplex `σ`. -/
private lemma exists_mem_piece
    (z : StdSimplex ℝ (Fin (p + 1)) × StdSimplex ℝ (Fin (q + 1))) :
    ∃ σ : (Δ[p] ⊗ Δ[q] : SSet.{u}).nonDegenerate (p + q), z ∈ piece σ := by
  classical
  let S := (coupling z.1 z.2).weights.support
  have hS : S.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    have htot := (coupling z.1 z.2).total
    dsimp only [S] at h
    rw [Finsupp.sum, h, Finset.sum_empty] at htot
    exact zero_ne_one htot
  let S' : Finset (Lex (Fin (p + 1) × Fin (q + 1))) := S.map toLex.toEmbedding
  have hcard : S'.card = (S.card - 1) + 1 := by
    rw [Finset.card_map]
    exact (Nat.sub_add_cancel (Finset.card_pos.2 hS)).symm
  let e : Fin ((S.card - 1) + 1) → Fin (p + 1) × Fin (q + 1) :=
    fun k ↦ ofLex (S'.orderEmbOfFin hcard k)
  have he_mem (k : Fin ((S.card - 1) + 1)) : e k ∈ S := by
    have hk := S'.orderEmbOfFin_mem hcard k
    simpa [S', e] using hk
  have he_strict : StrictMono e := by
    intro k₁ k₂ hk
    have hlex : toLex (e k₁) < toLex (e k₂) := (S'.orderEmbOfFin hcard).strictMono hk
    have hne : e k₁ ≠ e k₂ := fun h ↦ hlex.ne (congrArg toLex h)
    rcases isChain_support_coupling z.1 z.2 (he_mem k₁) (he_mem k₂) hne with hle | hle
    · exact lt_of_le_of_ne hle hne
    · exact absurd (Prod.Lex.toLex_mono hle) hlex.not_ge
  let x₀ : (Δ[p] ⊗ Δ[q] : SSet.{u}).nonDegenerate (S.card - 1) :=
    ⟨objEquiv.symm ⟨e, he_strict.monotone⟩, (nonDegenerate_iff_strictMono_objEquiv _).2
      (by simpa using he_strict)⟩
  obtain ⟨σ, hσ⟩ := exists_nonDegenerate_max_dim x₀ rfl
  have hsub : Set.range (objEquiv x₀.val) ⊆ Set.range (objEquiv σ.val) :=
    (ofSimplex_le_ofSimplex_iff x₀.val σ.val).1 ((Subcomplex.ofSimplex_le_iff _ _).2 hσ)
  refine ⟨σ, fun x hx ↦ by_contra fun hne ↦ hx (hsub ?_)⟩
  have hxS' : toLex x ∈ (S' : Set _) := by
    simp only [S', S, Finset.coe_map, Function.Embedding.coeFn_mk, Set.mem_image, Finset.mem_coe,
      Finsupp.mem_support_iff, coupling_weights]
    exact ⟨x, hne, rfl⟩
  rw [← S'.range_orderEmbOfFin hcard] at hxS'
  obtain ⟨k, hk⟩ := hxS'
  exact ⟨k, by simp [x₀, e, hk]⟩

private lemma iUnion_piece :
    ⋃ σ : (Δ[p] ⊗ Δ[q] : SSet.{u}).nonDegenerate (p + q), piece σ = Set.univ :=
  Set.eq_univ_of_forall fun z ↦ Set.mem_iUnion.2 (exists_mem_piece z)

private lemma injective_objEquiv_nonDegenerate
    (σ : (Δ[p] ⊗ Δ[q] : SSet.{u}).nonDegenerate (p + q)) :
    Function.Injective (objEquiv σ.val) :=
  (nonDegenerate_iff_injective_objEquiv σ.val).1 σ.prop

private noncomputable def pieceWeights (σ : (Δ[p] ⊗ Δ[q] : SSet.{u}).nonDegenerate (p + q))
    (z : StdSimplex ℝ (Fin (p + 1)) × StdSimplex ℝ (Fin (q + 1))) (hz : z ∈ piece σ) :
    StdSimplex ℝ (Fin (p + q + 1)) :=
  StdSimplex.comap (injective_objEquiv_nonDegenerate σ) (coupling z.1 z.2)
    (support_coupling_subset hz)

private lemma map_pieceWeights (σ : (Δ[p] ⊗ Δ[q] : SSet.{u}).nonDegenerate (p + q))
    (z : StdSimplex ℝ (Fin (p + 1)) × StdSimplex ℝ (Fin (q + 1))) (hz : z ∈ piece σ) :
    (pieceWeights σ z hz).map (objEquiv σ.val) = coupling z.1 z.2 :=
  StdSimplex.map_comap _ _ _

private lemma continuous_pieceWeights (σ : (Δ[p] ⊗ Δ[q] : SSet.{u}).nonDegenerate (p + q)) :
    Continuous fun z : piece σ ↦ pieceWeights σ z.1 z.2 := by
  rw [(StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (p + q + 1))).continuous_iff]
  refine continuous_pi fun k ↦ ?_
  simp only [Function.comp_apply, pieceWeights, StdSimplex.weights_comap_apply, coupling_weights]
  exact (continuous_couplingWeights _).comp continuous_subtype_val

private noncomputable def triangulateFun (p q : ℕ)
    (z : StdSimplex ℝ (Fin (p + 1)) × StdSimplex ℝ (Fin (q + 1))) :
    |(Δ[p] ⊗ Δ[q] : SSet.{u})| :=
  toTopObjMk (exists_mem_piece.{u} z).choose.val
    (pieceWeights _ z (exists_mem_piece.{u} z).choose_spec)

private lemma triangulateFun_eq {s : StdSimplex ℝ (Fin (p + 1))} {t : StdSimplex ℝ (Fin (q + 1))}
    {n : ℕ} (x : (Δ[p] ⊗ Δ[q] : SSet.{u}) _⦋n⦌) (w : StdSimplex ℝ (Fin (n + 1)))
    (h : w.map (objEquiv x) = coupling s t) :
    triangulateFun.{u} p q (s, t) = toTopObjMk x w :=
  toTopObjMk_eq_of_map_eq ((map_pieceWeights _ _ _).trans h.symm)

variable (p q) in
/-- The Eilenberg–Zilber triangulation of `StdSimplex ℝ (Fin (p + 1)) × StdSimplex ℝ (Fin (q + 1))`
into `|Δ[p] ⊗ Δ[q]|`, sending `(s, t)` to the unique point whose barycentric coordinates on the
vertices `Fin (p + 1) × Fin (q + 1)` are the comonotone coupling of `s` and `t`. -/
noncomputable def triangulate :
    C(StdSimplex ℝ (Fin (p + 1)) × StdSimplex ℝ (Fin (q + 1)), |(Δ[p] ⊗ Δ[q] : SSet.{u})|) where
  toFun := triangulateFun p q
  continuous_toFun := by
    have : Finite ((Δ[p] ⊗ Δ[q] : SSet.{u}).nonDegenerate (p + q)) :=
      Finite.of_injective (fun σ ↦ ⇑(objEquiv σ.val)) fun _ _ h ↦
        Subtype.ext (objEquiv.injective (DFunLike.coe_injective h))
    refine (locallyFinite_of_finite _).continuous iUnion_piece isClosed_piece fun σ ↦ ?_
    rw [continuousOn_iff_continuous_domRestrict]
    have hdom : (piece σ).domRestrict (triangulateFun.{u} p q) =
        fun z : piece σ ↦ toTopObjMk σ.val (pieceWeights σ z.1 z.2) :=
      funext fun z ↦ triangulateFun_eq _ _ (map_pieceWeights σ z.1 z.2)
    rw [hdom]
    exact (continuous_toTopObjMk _).comp (continuous_pieceWeights σ)

/-- Evaluating `triangulate` on the pair of barycentric marginals of a simplex `x` of `Δ[p] ⊗ Δ[q]`
recovers `toTopObjMk x w`. -/
theorem triangulate_map_objEquiv {n : ℕ}
    (x : (Δ[p] : SSet.{u}) _⦋n⦌ ⊗ Δ[q] _⦋n⦌) (w : StdSimplex ℝ (Fin (n + 1))) :
    triangulate p q (w.map (stdSimplex.objEquiv x.1), w.map (stdSimplex.objEquiv x.2)) =
      toTopObjMk (X := Δ[p] ⊗ Δ[q]) x w :=
  triangulateFun_eq x w (map_objEquiv_eq_coupling x w)

variable (p q) in
private noncomputable def toTopProj :
    C(|(Δ[p] ⊗ Δ[q] : SSet.{u})|, StdSimplex ℝ (Fin (p + 1)) × StdSimplex ℝ (Fin (q + 1))) where
  toFun u :=
    (⦋p⦌.toTopHomeo (toTop.map (CartesianMonoidalCategory.fst Δ[p] Δ[q]) u),
      ⦋q⦌.toTopHomeo (toTop.map (CartesianMonoidalCategory.snd Δ[p] Δ[q]) u))
  continuous_toFun :=
    (⦋p⦌.toTopHomeo.continuous.comp (toTop.map _).hom.continuous).prodMk
      (⦋q⦌.toTopHomeo.continuous.comp (toTop.map _).hom.continuous)

private lemma toTopProj_fst (u : |(Δ[p] ⊗ Δ[q] : SSet.{u})|) :
    (toTopProj p q u).1 =
      ⦋p⦌.toTopHomeo (toTop.map (CartesianMonoidalCategory.fst Δ[p] Δ[q]) u) :=
  rfl

private lemma toTopProj_snd (u : |(Δ[p] ⊗ Δ[q] : SSet.{u})|) :
    (toTopProj p q u).2 =
      ⦋q⦌.toTopHomeo (toTop.map (CartesianMonoidalCategory.snd Δ[p] Δ[q]) u) :=
  rfl

private lemma triangulate_toTopProj (u : |(Δ[p] ⊗ Δ[q] : SSet.{u})|) :
    triangulate p q (toTopProj p q u) = u := by
  have h : TopCat.ofHom ((triangulate.{u} p q).comp (toTopProj p q)) =
      𝟙 |(Δ[p] ⊗ Δ[q] : SSet.{u})| :=
    toTop_hom_ext fun n x w ↦ by
      -- Unfold composition in `TopCat` to evaluate on `toTopObjMk x w`.
      change triangulate p q (toTopProj p q (toTopObjMk x w)) = toTopObjMk x w
      have hproj : toTopProj p q (toTopObjMk x w) =
          (w.map (stdSimplex.objEquiv x.1), w.map (stdSimplex.objEquiv x.2)) := by
        refine Prod.ext ?_ ?_
        · rw [toTopProj_fst, toTop_map_toTopObjMk, SimplexCategory.toTopHomeo_toTopObjMk]
          rfl
        · rw [toTopProj_snd, toTop_map_toTopObjMk, SimplexCategory.toTopHomeo_toTopObjMk]
          rfl
      rw [hproj]
      exact triangulate_map_objEquiv x w
  exact ConcreteCategory.congr_hom h u

private lemma toTopProj_triangulate
    (z : StdSimplex ℝ (Fin (p + 1)) × StdSimplex ℝ (Fin (q + 1))) :
    toTopProj.{u} p q (triangulate p q z) = z := by
  obtain ⟨σ, hσ⟩ := exists_mem_piece.{u} z
  let σ₀ : (Δ[p] : SSet.{u}) _⦋p + q⦌ ⊗ Δ[q] _⦋p + q⦌ := σ.val
  have htri : triangulate.{u} p q z = toTopObjMk σ.val (pieceWeights σ z hσ) :=
    triangulateFun_eq _ _ (map_pieceWeights σ z hσ)
  rw [htri]
  refine Prod.ext ?_ ?_
  · rw [toTopProj_fst, toTop_map_toTopObjMk, SimplexCategory.toTopHomeo_toTopObjMk]
    -- On `Δ[p] ⊗ Δ[q]`, the first projection of `σ` composes `objEquiv σ` with `Prod.fst`.
    change (pieceWeights σ z hσ).map (Prod.fst ∘ ⇑(objEquiv σ₀)) = z.1
    rw [StdSimplex.map_comp, map_pieceWeights, map_fst_coupling]
  · rw [toTopProj_snd, toTop_map_toTopObjMk, SimplexCategory.toTopHomeo_toTopObjMk]
    -- On `Δ[p] ⊗ Δ[q]`, the second projection of `σ` composes `objEquiv σ` with `Prod.snd`.
    change (pieceWeights σ z hσ).map (Prod.snd ∘ ⇑(objEquiv σ₀)) = z.2
    rw [StdSimplex.map_comp, map_pieceWeights, map_snd_coupling]

variable (p q) in
/-- The geometric realization `|Δ[p] ⊗ Δ[q]|` is homeomorphic to the product of standard
topological simplices `StdSimplex ℝ (Fin (p + 1)) × StdSimplex ℝ (Fin (q + 1))`. -/
noncomputable def toTopHomeo :
    |(Δ[p] ⊗ Δ[q] : SSet.{u})| ≃ₜ StdSimplex ℝ (Fin (p + 1)) × StdSimplex ℝ (Fin (q + 1)) where
  toFun := toTopProj p q
  invFun := triangulate p q
  left_inv := triangulate_toTopProj
  right_inv := toTopProj_triangulate
  continuous_toFun := (toTopProj p q).continuous
  continuous_invFun := (triangulate p q).continuous

@[simp]
theorem toTopHomeo_fst (u : |(Δ[p] ⊗ Δ[q] : SSet.{u})|) :
    (toTopHomeo p q u).1 =
      ⦋p⦌.toTopHomeo (toTop.map (CartesianMonoidalCategory.fst Δ[p] Δ[q]) u) := by
  rfl

@[simp]
theorem toTopHomeo_snd (u : |(Δ[p] ⊗ Δ[q] : SSet.{u})|) :
    (toTopHomeo p q u).2 =
      ⦋q⦌.toTopHomeo (toTop.map (CartesianMonoidalCategory.snd Δ[p] Δ[q]) u) := by
  rfl

@[simp]
theorem coe_toTopHomeo_symm :
    ⇑(toTopHomeo.{u} p q).symm = triangulate p q := by
  rfl

variable (p q) in
/-- The homeomorphism `|Δ[p] ⊗ Δ[q]| ≃ₜ |Δ[p]| × |Δ[q]|` whose forward map is the Cartesian
monoidal product comparison morphism. -/
@[expose]
noncomputable def toTopProdHomeo :
    |(Δ[p] ⊗ Δ[q] : SSet.{u})| ≃ₜ |(Δ[p] : SSet.{u})| × |(Δ[q] : SSet.{u})| :=
  (toTopHomeo p q).trans (⦋p⦌.toTopHomeo.prodCongr ⦋q⦌.toTopHomeo).symm

@[simp]
theorem toTopProdHomeo_apply (u : |(Δ[p] ⊗ Δ[q] : SSet.{u})|) :
    toTopProdHomeo p q u =
      (toTop.map (CartesianMonoidalCategory.fst Δ[p] Δ[q]) u,
        toTop.map (CartesianMonoidalCategory.snd Δ[p] Δ[q]) u) := by
  refine Prod.ext ?_ ?_ <;> simp [toTopProdHomeo]

/-- The Cartesian monoidal product comparison `|Δ[p] ⊗ Δ[q]| ⟶ |Δ[p]| ⊗ |Δ[q]|` is an isomorphism
in `TopCat`. -/
instance instIsIsoCartesianProdComparison (p q : ℕ) :
    IsIso (CartesianMonoidalCategory.prodComparison SSet.toTop.{u} Δ[p] Δ[q]) := by
  have h : CartesianMonoidalCategory.prodComparison SSet.toTop.{u} Δ[p] Δ[q] =
      (TopCat.isoOfHomeo (X := |(Δ[p] ⊗ Δ[q] : SSet.{u})|)
        (Y := |(Δ[p] : SSet.{u})| ⊗ |(Δ[q] : SSet.{u})|) (toTopProdHomeo p q)).hom :=
    TopCat.ext fun u ↦ by
      -- In `TopCat`, `prodComparison` evaluates componentwise via `TopCat.lift_apply`.
      change CartesianMonoidalCategory.lift
        (toTop.map (CartesianMonoidalCategory.fst Δ[p] Δ[q]))
        (toTop.map (CartesianMonoidalCategory.snd Δ[p] Δ[q])) u = toTopProdHomeo p q u
      rw [TopCat.lift_apply, toTopProdHomeo_apply]
  rw [h]
  infer_instance

/-- Geometric realization preserves the binary product of any two standard simplices in `TopCat`. -/
instance instPreservesLimitPairToTop (p q : ℕ) :
    PreservesLimit (Limits.pair (Δ[p] : SSet.{u}) Δ[q]) SSet.toTop.{u} :=
  CartesianMonoidalCategory.preservesLimit_pair_of_isIso_prodComparison SSet.toTop.{u} Δ[p] Δ[q]

end prodStdSimplex

end SSet
