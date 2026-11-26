/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.ProdStdSimplex
public import TauCeti.AlgebraicTopology.SimplicialSet.TopAdj
public import TauCeti.CategoryTheory.Monoidal.Cartesian.Basic
public import TauCeti.Geometry.Convex.ConvexSpace.Coupling

import Mathlib.Order.Fin.Prod
import TauCeti.AlgebraicTopology.SimplicialSet.ProdStdSimplex.Basic
import TauCeti.Data.Set.Function

/-!
# Geometric realization of binary products of standard simplices

The canonical projection morphism `|Δ[p] ⊗ Δ[q]| ⟶ |Δ[p]| ⊗ |Δ[q]|` in `TopCat` is an isomorphism,
giving a homeomorphism `SSet.prodStdSimplex.toTopHomeo` between `|Δ[p] ⊗ Δ[q]|` and the product of
standard topological simplices `StdSimplex ℝ (Fin (p + 1)) × StdSimplex ℝ (Fin (q + 1))`.

Geometrically, the Eilenberg–Zilber shuffle simplices — the nondegenerate `(p + q)`-simplices of
`Δ[p] ⊗ Δ[q]` — triangulate the product `StdSimplex ℝ (Fin (p + 1)) × StdSimplex ℝ (Fin (q + 1))`.
Rather than enumerating shuffle paths directly, we describe the inverse map intrinsically via the
comonotone coupling `Convexity.StdSimplex.coupling` of barycentric weight distributions:

* Every point `SSet.toTopObjMk x w` of `|Δ[p] ⊗ Δ[q]|` is uniquely determined by the pushforward
  `w.map (SSet.prodStdSimplex.objEquiv x)` of its barycentric coordinates to the vertices
  `Fin (p + 1) × Fin (q + 1)` (`SSet.prodStdSimplex.toTopObjMk_eq_of_map_eq`).
* Every simplex `x` of `Δ[p] ⊗ Δ[q]` pushes `w` forward to the comonotone coupling of its two
  coordinate marginals (`Convexity.StdSimplex.map_prodMk_eq_coupling`).
* Because the support of `s.coupling t` is a chain in `Fin (p + 1) × Fin (q + 1)`
  (`Convexity.StdSimplex.isChain_support_coupling`), it lies in the vertex set of a nondegenerate
  `(p + q)`-simplex of `Δ[p] ⊗ Δ[q]` by `SSet.prodStdSimplex.exists_nonDegenerate_max_dim`.
* Gluing over the finitely many closed pieces indexed by the nondegenerate `(p + q)`-simplices via
  `SSet.prodStdSimplex.toTopObjMk_eq_of_map_eq` yields the continuous inverse
  `SSet.prodStdSimplex.triangulate`.

## Main declarations

* `SSet.prodStdSimplex.toTopObjMk_eq_of_map_eq`: points of `|Δ[p] ⊗ Δ[q]|` are determined by their
  barycentric coordinates on the vertices `Fin (p + 1) × Fin (q + 1)`.
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

universe u

namespace SSet.prodStdSimplex

variable {p q : ℕ}

/-- Every point of the realization of a simplex of `Δ[p] ⊗ Δ[q]` is the point, with nowhere
vanishing coordinates, of a simplex with injective vertex map, with the same distribution of
coordinates on the vertices. -/
private lemma exists_injective_toTopObjMk_eq {n : ℕ} (x : (Δ[p] ⊗ Δ[q] : SSet.{u}) _⦋n⦌)
    (w : StdSimplex ℝ (Fin (n + 1))) :
    ∃ (r : ℕ) (y : (Δ[p] ⊗ Δ[q] : SSet.{u}) _⦋r⦌) (w' : StdSimplex ℝ (Fin (r + 1))),
      Function.Injective (objEquiv y) ∧ (∀ j, w'.weights j ≠ 0) ∧
      toTopObjMk x w = toTopObjMk y w' ∧
      StdSimplex.map (objEquiv x) w = StdSimplex.map (objEquiv y) w' := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  by_cases h0 : ∃ j, w.weights j = 0
  · -- Pass to the face opposite a vertex with vanishing coordinate.
    obtain ⟨j, hj⟩ := h0
    obtain _ | n := n
    · simp at hj
    have hsupp : Set.BijOn j.succAbove (j.succAbove ⁻¹' ↑w.weights.support) ↑w.weights.support :=
      Set.bijOn_preimage_iff.2 ⟨Fin.succAbove_right_injective.injOn, by
        simp [Fin.range_succAbove, Set.subset_compl_singleton_iff, hj]⟩
    obtain ⟨r, y, w'', hy, hw'', h₁, h₂⟩ :=
      ih n (by lia) ((Δ[p] ⊗ Δ[q]).δ j x) (StdSimplex.comap w hsupp)
    refine ⟨r, y, w'', hy, hw'', ?_, ?_⟩
    · rw [← h₁, SimplicialObject.δ, toTopObjMk_map]
      exact congrArg _ (StdSimplex.map_comap w hsupp).symm
    · rw [← h₂]
      conv_lhs => rw [← StdSimplex.map_comap w hsupp]
      rw [StdSimplex.map_map, objEquiv_δ, Function.comp_def]
  · push Not at h0
    by_cases hi : Function.Injective (objEquiv x)
    · exact ⟨n, x, w, hi, h0, rfl, rfl⟩
    -- Pass to a degeneracy of the face opposite a repeated vertex.
    obtain _ | n := n
    · exact absurd (fun a b _ ↦ Fin.ext (by have := a.isLt; have := b.isLt; lia)) hi
    obtain ⟨j, hj⟩ : ∃ j : Fin (n + 1), objEquiv x j.castSucc = objEquiv x j.succ := by
      have h : ¬ StrictMono (objEquiv x) := fun h ↦ hi h.injective
      rw [Fin.strictMono_iff_lt_succ] at h
      push Not at h
      obtain ⟨j, hj⟩ := h
      exact ⟨j, ((objEquiv x).monotone (Fin.castSucc_le_succ j)).eq_of_not_lt hj⟩
    have hx := (σ_δ_succ_of_eq x j hj).symm
    obtain ⟨r, y, w'', hy, hw'', h₁, h₂⟩ :=
      ih n (by lia) ((Δ[p] ⊗ Δ[q]).δ j.succ x) (StdSimplex.map j.predAbove w)
    refine ⟨r, y, w'', hy, hw'', ?_, ?_⟩
    · rw [← h₁]
      conv_lhs => rw [hx]
      rw [SimplicialObject.σ, toTopObjMk_map, SimplexCategory.coe_σ]
    · rw [← h₂, StdSimplex.map_map]
      conv_lhs => rw [hx]
      rw [objEquiv_σ, Function.comp_def]

/-- Two points of the realizations of simplices of `Δ[p] ⊗ Δ[q]` with injective vertex maps and
nowhere vanishing coordinates agree if their coordinates have the same distribution on the
vertices. -/
private lemma toTopObjMk_eq_of_injective {r r' : ℕ} {y : (Δ[p] ⊗ Δ[q] : SSet.{u}) _⦋r⦌}
    {y' : (Δ[p] ⊗ Δ[q] : SSet.{u}) _⦋r'⦌} {w : StdSimplex ℝ (Fin (r + 1))}
    {w' : StdSimplex ℝ (Fin (r' + 1))} (hy : Function.Injective (objEquiv y))
    (hy' : Function.Injective (objEquiv y')) (hw : ∀ j, w.weights j ≠ 0)
    (hw' : ∀ j, w'.weights j ≠ 0)
    (h : StdSimplex.map (objEquiv y) w = StdSimplex.map (objEquiv y') w') :
    toTopObjMk y w = toTopObjMk y' w' := by
  classical
  have hsupp {r : ℕ} (w : StdSimplex ℝ (Fin (r + 1))) (hw : ∀ j, w.weights j ≠ 0) :
      w.weights.support = Finset.univ :=
    Finset.eq_univ_iff_forall.2 fun j ↦ by simpa using hw j
  have himage : Finset.univ.image (objEquiv y) = Finset.univ.image (objEquiv y') := by
    have := congrArg (fun w ↦ w.weights.support) h
    simpa only [StdSimplex.weights_map, Finsupp.mapDomain_support_of_injective hy,
      Finsupp.mapDomain_support_of_injective hy', hsupp w hw, hsupp w' hw'] using this
  obtain rfl : r = r' := by
    simpa [Finset.card_image_of_injective _ hy, Finset.card_image_of_injective _ hy'] using
      congrArg Finset.card himage
  have hmono {y : (Δ[p] ⊗ Δ[q] : SSet.{u}) _⦋r⦌} (hy : Function.Injective (objEquiv y)) :
      StrictMono (toLex ∘ objEquiv y) :=
    (Prod.Lex.toLex_mono.comp (objEquiv y).monotone).strictMono_of_injective
      (toLex.injective.comp hy)
  have hrange : Set.range (toLex ∘ objEquiv y) = Set.range (toLex ∘ objEquiv y') := by
    have : Set.range (objEquiv y) = Set.range (objEquiv y') := by
      rw [← Set.image_univ, ← Set.image_univ, ← Finset.coe_univ, ← Finset.coe_image,
        ← Finset.coe_image, himage]
    rw [Set.range_comp, Set.range_comp, this]
  obtain rfl : y = y' := by
    apply objEquiv.injective
    refine OrderHom.ext _ _ (funext fun k ↦ ?_)
    exact toLex.injective
      (congrFun ((StrictMono.range_inj_of_wellFoundedLT (hmono hy) (hmono hy')).1 hrange) k)
  obtain rfl : w = w' := by
    rw [← StdSimplex.weights_inj, StdSimplex.weights_map, StdSimplex.weights_map] at h
    exact (StdSimplex.weights_inj).1 (Finsupp.mapDomain_injective hy h)
  rfl

/-- A point of the geometric realization of `Δ[p] ⊗ Δ[q]` is determined by the distribution of its
barycentric coordinates on the vertices `Fin (p + 1) × Fin (q + 1)`: the points of two simplices
agree when their coordinates push forward to the same coordinates on the vertices. -/
theorem toTopObjMk_eq_of_map_eq {n n' : ℕ} {x : (Δ[p] ⊗ Δ[q] : SSet.{u}) _⦋n⦌}
    {x' : (Δ[p] ⊗ Δ[q] : SSet.{u}) _⦋n'⦌} {w : StdSimplex ℝ (Fin (n + 1))}
    {w' : StdSimplex ℝ (Fin (n' + 1))}
    (h : StdSimplex.map (objEquiv x) w = StdSimplex.map (objEquiv x') w') :
    toTopObjMk x w = toTopObjMk x' w' := by
  obtain ⟨r, y, v, hy, hv, h₁, h₂⟩ := exists_injective_toTopObjMk_eq x w
  obtain ⟨r', y', v', hy', hv', h₁', h₂'⟩ := exists_injective_toTopObjMk_eq x' w'
  rw [h₁, h₁']
  exact toTopObjMk_eq_of_injective hy hy' hv hv' (h₂.symm.trans (h.trans h₂'))

/-- Any simplex `x` of `Δ[p] ⊗ Δ[q]` pushes barycentric weights `w` forward to the comonotone
coupling of the two coordinate marginals of `w`. -/
private lemma map_objEquiv_eq_coupling {n : ℕ} (x : (Δ[p] : SSet.{u}) _⦋n⦌ ⊗ Δ[q] _⦋n⦌)
    (w : StdSimplex ℝ (Fin (n + 1))) :
    w.map (objEquiv x) =
      (w.map (stdSimplex.objEquiv x.1)).coupling (w.map (stdSimplex.objEquiv x.2)) := by
  have hfn : ⇑(objEquiv x) =
      fun i ↦ (stdSimplex.objEquiv x.1 i, stdSimplex.objEquiv x.2 i) :=
    funext fun i ↦ Prod.ext (objEquiv_apply_fst x i) (objEquiv_apply_snd x i)
  rw [hfn]
  exact w.map_prodMk_eq_coupling
    (stdSimplex.objEquiv x.1).toOrderHom.monotone
    (stdSimplex.objEquiv x.2).toOrderHom.monotone

/-- The closed piece of `StdSimplex ℝ (Fin (p + 1)) × StdSimplex ℝ (Fin (q + 1))` covered by a
nondegenerate `(p + q)`-simplex `σ` of `Δ[p] ⊗ Δ[q]`. -/
private def piece (σ : (Δ[p] ⊗ Δ[q] : SSet.{u}).nonDegenerate (p + q)) :
    Set (StdSimplex ℝ (Fin (p + 1)) × StdSimplex ℝ (Fin (q + 1))) :=
  {z | ∀ x ∉ Set.range (objEquiv σ.val), z.1.couplingWeights z.2 x = 0}

private lemma isClosed_piece (σ : (Δ[p] ⊗ Δ[q] : SSet.{u}).nonDegenerate (p + q)) :
    IsClosed (piece σ) := by
  have h : piece σ = ⋂ (x : Fin (p + 1) × Fin (q + 1)) (_ : x ∉ Set.range (objEquiv σ.val)),
      {z | z.1.couplingWeights z.2 x = 0} := by
    ext z
    simp [piece]
  rw [h]
  exact isClosed_iInter fun x ↦ isClosed_iInter fun _ ↦
    isClosed_eq (StdSimplex.continuous_couplingWeights x) continuous_const

private lemma support_coupling_subset {σ : (Δ[p] ⊗ Δ[q] : SSet.{u}).nonDegenerate (p + q)}
    {z : StdSimplex ℝ (Fin (p + 1)) × StdSimplex ℝ (Fin (q + 1))} (hz : z ∈ piece σ) :
    ↑(z.1.coupling z.2).weights.support ⊆ Set.range (objEquiv σ.val) := by
  intro x hx
  by_contra hnot
  exact Finsupp.mem_support_iff.1 hx ((StdSimplex.coupling_weights z.1 z.2 x).trans (hz x hnot))

/-- Every point of the product of standard simplices lies in `piece σ` for some nondegenerate
`(p + q)`-simplex `σ`. -/
private lemma exists_mem_piece
    (z : StdSimplex ℝ (Fin (p + 1)) × StdSimplex ℝ (Fin (q + 1))) :
    ∃ σ : (Δ[p] ⊗ Δ[q] : SSet.{u}).nonDegenerate (p + q), z ∈ piece σ := by
  classical
  let S := (z.1.coupling z.2).weights.support
  have hS : S.Nonempty := (z.1.coupling z.2).support_weights_nonempty
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
    rcases z.1.isChain_support_coupling z.2 (he_mem k₁) (he_mem k₂) hne with hle | hle
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
      Finsupp.mem_support_iff, StdSimplex.coupling_weights]
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
  (nonDegenerate_iff_injective_objEquiv σ.val).1 σ.property

private noncomputable def pieceWeights (σ : (Δ[p] ⊗ Δ[q] : SSet.{u}).nonDegenerate (p + q))
    (z : StdSimplex ℝ (Fin (p + 1)) × StdSimplex ℝ (Fin (q + 1))) (hz : z ∈ piece σ) :
    StdSimplex ℝ (Fin (p + q + 1)) :=
  StdSimplex.comap (f := objEquiv σ.val) (z.1.coupling z.2)
    (Set.bijOn_preimage_iff.2
      ⟨(injective_objEquiv_nonDegenerate σ).injOn, support_coupling_subset hz⟩)

private lemma map_pieceWeights (σ : (Δ[p] ⊗ Δ[q] : SSet.{u}).nonDegenerate (p + q))
    (z : StdSimplex ℝ (Fin (p + 1)) × StdSimplex ℝ (Fin (q + 1))) (hz : z ∈ piece σ) :
    (pieceWeights σ z hz).map (objEquiv σ.val) = z.1.coupling z.2 :=
  StdSimplex.map_comap _ _

private lemma continuous_pieceWeights (σ : (Δ[p] ⊗ Δ[q] : SSet.{u}).nonDegenerate (p + q)) :
    Continuous fun z : piece σ ↦ pieceWeights.{u} σ z.val z.property := by
  rw [(StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (p + q + 1))).continuous_iff]
  refine continuous_pi fun k ↦ ?_
  have h : (fun z : piece σ ↦ (pieceWeights.{u} σ z.val z.property).weights k) =
      fun z ↦ z.val.1.couplingWeights z.val.2 (objEquiv σ.val k) :=
    funext fun z ↦ (StdSimplex.weights_comap_apply _ _ k).trans
      (StdSimplex.coupling_weights z.val.1 z.val.2 _)
  simp only [Function.comp_apply, h]
  exact (StdSimplex.continuous_couplingWeights _).comp continuous_subtypeVal

private noncomputable def triangulateFun (p q : ℕ)
    (z : StdSimplex ℝ (Fin (p + 1)) × StdSimplex ℝ (Fin (q + 1))) :
    |(Δ[p] ⊗ Δ[q] : SSet.{u})| :=
  toTopObjMk (exists_mem_piece.{u} z).choose.val
    (pieceWeights _ z (exists_mem_piece.{u} z).choose_spec)

private lemma triangulateFun_eq {s : StdSimplex ℝ (Fin (p + 1))} {t : StdSimplex ℝ (Fin (q + 1))}
    {n : ℕ} (x : (Δ[p] ⊗ Δ[q] : SSet.{u}) _⦋n⦌) (w : StdSimplex ℝ (Fin (n + 1)))
    (h : w.map (objEquiv x) = s.coupling t) :
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
        fun z : piece σ ↦ toTopObjMk σ.val (pieceWeights σ z.val z.property) :=
      funext fun z ↦ triangulateFun_eq _ _ (map_pieceWeights σ z.val z.property)
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
          -- Levelwise on `SSet`, `CartesianMonoidalCategory.fst` is `Prod.fst` by definition.
          rfl
        · rw [toTopProj_snd, toTop_map_toTopObjMk, SimplexCategory.toTopHomeo_toTopObjMk]
          -- Levelwise on `SSet`, `CartesianMonoidalCategory.snd` is `Prod.snd` by definition.
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
    rw [StdSimplex.map_comp, map_pieceWeights, StdSimplex.map_fst_coupling]
  · rw [toTopProj_snd, toTop_map_toTopObjMk, SimplexCategory.toTopHomeo_toTopObjMk]
    -- On `Δ[p] ⊗ Δ[q]`, the second projection of `σ` composes `objEquiv σ` with `Prod.snd`.
    change (pieceWeights σ z hσ).map (Prod.snd ∘ ⇑(objEquiv σ₀)) = z.2
    rw [StdSimplex.map_comp, map_pieceWeights, StdSimplex.map_snd_coupling]

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
      ⦋p⦌.toTopHomeo (toTop.map (CartesianMonoidalCategory.fst Δ[p] Δ[q]) u) :=
  (rfl)

@[simp]
theorem toTopHomeo_snd (u : |(Δ[p] ⊗ Δ[q] : SSet.{u})|) :
    (toTopHomeo p q u).2 =
      ⦋q⦌.toTopHomeo (toTop.map (CartesianMonoidalCategory.snd Δ[p] Δ[q]) u) :=
  (rfl)

@[simp]
theorem coe_toTopHomeo_symm :
    ⇑(toTopHomeo.{u} p q).symm = triangulate p q :=
  (rfl)

/-- `SSet.prodStdSimplex.triangulate` is a right inverse to `SSet.prodStdSimplex.toTopHomeo`. -/
@[simp]
theorem toTopHomeo_triangulate
    (z : StdSimplex ℝ (Fin (p + 1)) × StdSimplex ℝ (Fin (q + 1))) :
    toTopHomeo p q (triangulate.{u} p q z) = z :=
  toTopProj_triangulate z

/-- `SSet.prodStdSimplex.triangulate` is a left inverse to `SSet.prodStdSimplex.toTopHomeo`. -/
@[simp]
theorem triangulate_toTopHomeo (u : |(Δ[p] ⊗ Δ[q] : SSet.{u})|) :
    triangulate p q (toTopHomeo p q u) = u :=
  triangulate_toTopProj u

/-- Projecting `triangulate p q z` to `|Δ[p]|` recovers `⦋p⦌.toTopHomeo.symm z.1`. -/
@[simp]
theorem toTop_map_fst_triangulate
    (z : StdSimplex ℝ (Fin (p + 1)) × StdSimplex ℝ (Fin (q + 1))) :
    toTop.map (CartesianMonoidalCategory.fst Δ[p] Δ[q]) (triangulate.{u} p q z) =
      ⦋p⦌.toTopHomeo.symm z.1 := by
  apply ⦋p⦌.toTopHomeo.injective
  rw [Homeomorph.apply_symm_apply, ← toTopHomeo_fst, toTopHomeo_triangulate]

/-- Projecting `triangulate p q z` to `|Δ[q]|` recovers `⦋q⦌.toTopHomeo.symm z.2`. -/
@[simp]
theorem toTop_map_snd_triangulate
    (z : StdSimplex ℝ (Fin (p + 1)) × StdSimplex ℝ (Fin (q + 1))) :
    toTop.map (CartesianMonoidalCategory.snd Δ[p] Δ[q]) (triangulate.{u} p q z) =
      ⦋q⦌.toTopHomeo.symm z.2 := by
  apply ⦋q⦌.toTopHomeo.injective
  rw [Homeomorph.apply_symm_apply, ← toTopHomeo_snd, toTopHomeo_triangulate]

/-- `triangulate` is natural with respect to morphisms of standard simplices in both factors. -/
theorem triangulate_naturality {m n p q : ℕ} (f : ⦋m⦌ ⟶ ⦋n⦌) (g : ⦋p⦌ ⟶ ⦋q⦌)
    (s : StdSimplex ℝ (Fin (m + 1))) (t : StdSimplex ℝ (Fin (p + 1))) :
    toTop.map (stdSimplex.map f ⊗ₘ stdSimplex.map g) (triangulate.{u} m p (s, t)) =
      triangulate n q (s.map f, t.map g) := by
  apply (toTopHomeo n q).injective
  refine Prod.ext ?_ ?_ <;> simp [SimplexCategory.toTopHomeo_naturality_apply]

/-- The Cartesian monoidal product comparison `|Δ[p] ⊗ Δ[q]| ⟶ |Δ[p]| ⊗ |Δ[q]|` is an isomorphism
in `TopCat`. -/
instance instIsIsoCartesianProdComparison (p q : ℕ) :
    IsIso (CartesianMonoidalCategory.prodComparison SSet.toTop.{u} Δ[p] Δ[q]) := by
  let e : |(Δ[p] ⊗ Δ[q] : SSet.{u})| ≃ₜ |(Δ[p] : SSet.{u})| × |(Δ[q] : SSet.{u})| :=
    (toTopHomeo p q).trans (⦋p⦌.toTopHomeo.prodCongr ⦋q⦌.toTopHomeo).symm
  have h : CartesianMonoidalCategory.prodComparison SSet.toTop.{u} Δ[p] Δ[q] =
      (TopCat.isoOfHomeo (X := |(Δ[p] ⊗ Δ[q] : SSet.{u})|)
        (Y := |(Δ[p] : SSet.{u})| ⊗ |(Δ[q] : SSet.{u})|) e).hom :=
    TopCat.ext fun u ↦ by
      -- In `TopCat`, `prodComparison` evaluates componentwise via `TopCat.lift_apply`.
      change CartesianMonoidalCategory.lift
        (toTop.map (CartesianMonoidalCategory.fst Δ[p] Δ[q]))
        (toTop.map (CartesianMonoidalCategory.snd Δ[p] Δ[q])) u = e u
      rw [TopCat.lift_apply]
      refine Prod.ext ?_ ?_ <;> simp [e]
  rw [h]
  infer_instance

/-- Geometric realization preserves the binary product of any two standard simplices in `TopCat`. -/
instance instPreservesLimitPairToTop (p q : ℕ) :
    PreservesLimit (Limits.pair (Δ[p] : SSet.{u}) Δ[q]) SSet.toTop.{u} :=
  CartesianMonoidalCategory.preservesLimit_pair_of_isIso_prodComparison SSet.toTop.{u} Δ[p] Δ[q]

end SSet.prodStdSimplex
