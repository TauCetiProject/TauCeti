/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.Map
public import TauCeti.GroupTheory.Perm.FinThree.ChainComplex
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.A
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.Reduced
public import TauCeti.LinearAlgebra.RootSystem.Weyl.TypeA.Presentation
public import TauCeti.RepresentationTheory.LSPath.Simplex.Basic

import Mathlib.Data.Finset.Sort
import TauCeti.LinearAlgebra.RootSystem.Weyl.IntervalBondGcd

/-!
# The Bruhat-chain complex of `W / W_λ`, its polyhedron, and the `S₃` realization

For a weight `λ` of a finite reduced root datum `(P, b)`, the minimal coset representatives of
`W / W_λ` carry the restricted Bruhat partial order. Their order complex
`TauCeti.LSPath.bruhatChainComplex` has the cosets of `W / W_λ` as vertices and the nonempty finite
Bruhat chains as faces. Each weakly decreasing Bruhat sequence `τ₀ ≥ τ₁ ≥ ⋯ ≥ τ_l` induces a
continuous simplex map `TauCeti.LSPath.chainSimplexToRealization` from the closed `l`-simplex into
the geometric realization `(bruhatChainComplex P b lam).Realization`.

Summing barycentric weights over equal directions gives both simplicial operations inside the same
polyhedron:

* face inclusions (`w.map p.succAbove`) restrict a simplex map to a subchain face;
* adjacent-direction merges (`w.map p.predAbove` when `dir p.castSucc = dir p.succ`) leave the
  realized point in `(bruhatChainComplex P b lam).Realization` unchanged; and
* two closed chain simplices meet precisely along the face spanned by their shared directions.

Evaluating any point of `(bruhatChainComplex P b lam).Realization` on its strictly decreasing
carrier chain yields a global piecewise-linear path map `TauCeti.LSPath.bruhatRealizationPath` into
`PLPath ℝ V`, compatible with every weakly decreasing chain presentation and injective whenever `λ`
is dominant and distinct orbit weights lie in distinct rays.

The Lakshmibai–Seshadri paths of shape `λ` embed injectively into this polyhedron via
`TauCeti.LSPath.toBruhatRealization`, but for dominant `λ` their image is finite, whereas the
polyhedron is uncountable (hence strictly larger) if and only if `⟨λ, αᵢ^∨⟩ ≠ 0` for some simple
root `αᵢ`.

In rank two of Cartan type `A₂` at any regular weight `λ`, the Bruhat-chain complex is isomorphic
to `TauCeti.symmetricThreeBruhatComplex` on the six permutations of `Fin 3`, with homeomorphic
polyhedron (`TauCeti.LSPath.typeATwoBruhatRealizationHomeomorph`), six vertices, and four maximal
tetrahedra (`TauCeti.LSPath.typeATwoBruhatTetrahedron`). At any weight with unit simple-coroot
pairings `⟨λ, αᵢ^∨⟩ = 1` (such as `![1, 1]` on `DynkinType.typeASimplyConnectedRootDatum 2`), every
Lakshmibai–Seshadri path has at most two internal breaks (`π.length < 3`), so the fixed-`λ` finite
LS path set is disjoint from the open interior of all four maximal tetrahedra.

## Main definitions

* `TauCeti.LSPath.bruhatChainComplex`: the order complex of Bruhat chains in `W / W_λ`.
* `TauCeti.LSPath.chainSimplexToRealization`: continuous map from a closed fixed-chain simplex into
  the Bruhat-chain polyhedron, merging equal directions.
* `TauCeti.LSPath.bruhatRealizationPath`: piecewise-linear path attached to a point of the
  Bruhat-chain polyhedron.
* `TauCeti.LSPath.toBruhatRealization`: embedding of `LSPath P b lam` into the Bruhat-chain
  polyhedron.
* `TauCeti.LSPath.typeATwoMinimalCosetRepEquiv`,
  `TauCeti.LSPath.typeATwoBruhatRealizationHomeomorph`, and
  `TauCeti.LSPath.typeATwoBruhatTetrahedron`: the six-vertex `S₃` identification and four maximal
  tetrahedra for regular weights in type `A₂`.

## Main results

* `TauCeti.LSPath.chainSimplexToRealization_map_orderHom`,
  `TauCeti.LSPath.chainSimplexToRealization_map_succAbove`,
  `TauCeti.LSPath.chainSimplexToRealization_map_predAbove`, and
  `TauCeti.LSPath.range_chainSimplexToRealization_inter`: face inclusions, equal-adjacent-direction
  merges, and common-face intersections in `(bruhatChainComplex P b lam).Realization`.
* `TauCeti.LSPath.bruhatRealizationPath_chainSimplexToRealization` and
  `TauCeti.LSPath.bruhatRealizationPath_injective`: compatibility with fixed-chain simplex paths
  and injectivity of global path evaluation.
* `TauCeti.LSPath.toBruhatRealization_injective`,
  `TauCeti.LSPath.finite_range_toBruhatRealization`, and
  `TauCeti.LSPath.range_toBruhatRealization_ssubset_univ_iff`: injectivity, finiteness, and exact
  strict-containment criterion for the LS subset inside the Bruhat-chain polyhedron.
* `TauCeti.LSPath.maximal_typeATwo_bruhatChainComplex_iff`,
  `TauCeti.LSPath.length_lt_three_of_hasCartanType_A_two`, and
  `TauCeti.LSPath.length_lt_three_typeASimplyConnectedRootDatum_two`: the four maximal tetrahedra
  in type `A₂` and empty open-tetrahedron interiors for unit simple-coroot pairings.

## References

* A. Björner and F. Brenti, *Combinatorics of Coxeter Groups*, GTM 231, Springer (2005), §§2.2–2.5.
* P. Littelmann, *A Littlewood–Richardson rule for symmetrizable Kac–Moody algebras*, Invent.
  Math. 116 (1994), 329–346, §4.
* P. Littelmann, *Paths and root operators in representation theory*, Ann. of Math. 142 (1995),
  499–525, §4.
-/

public section

universe u w x

namespace TauCeti.LSPath

open RootPairing

attribute [local instance] Classical.propDecidable

section BruhatChainComplex

variable {ι : Type u} {M : Type w} {N : Type x} [AddCommGroup M] [AddCommGroup N]
  {P : RootPairing ι ℤ M N} {b : P.Base} [Finite ι] [P.IsReduced] {lam : M}

variable (P b lam) in
/-- The **Bruhat-chain simplicial complex** of `W / W_λ`: the order complex of the Bruhat order on
minimal coset representatives of the stabilizer parabolic `W_λ`. -/
noncomputable def bruhatChainComplex :
    _root_.AbstractSimplicialComplex
      {w // (weylCoxeterSystem P b).IsMinimalCosetRep (P.wallIndices b lam) w} :=
  letI := (weylCoxeterSystem P b).bruhatPartialOrder
  AbstractSimplicialComplex.orderComplex
    {w // (weylCoxeterSystem P b).IsMinimalCosetRep (P.wallIndices b lam) w}

/-- A finite set of minimal coset representatives is a face of `bruhatChainComplex` exactly when it
is nonempty and pairwise comparable in Bruhat order. -/
@[simp]
theorem mem_bruhatChainComplex_iff
    {σ : Finset {w // (weylCoxeterSystem P b).IsMinimalCosetRep (P.wallIndices b lam) w}} :
    σ ∈ bruhatChainComplex P b lam ↔
      σ.Nonempty ∧ ∀ u ∈ σ, ∀ v ∈ σ,
        (weylCoxeterSystem P b).BruhatLE u.1 v.1 ∨
          (weylCoxeterSystem P b).BruhatLE v.1 u.1 := by
  let : PartialOrder P.weylGroup := (weylCoxeterSystem P b).bruhatPartialOrder
  rw [bruhatChainComplex, AbstractSimplicialComplex.mem_orderComplex_iff']
  simp only [← Subtype.coe_le_coe, CoxeterSystem.bruhatPartialOrder_le]

private theorem image_dir_mem_bruhatChainComplex {l : ℕ}
    (dir : Fin (l + 1) →
      {w // (weylCoxeterSystem P b).IsMinimalCosetRep (P.wallIndices b lam) w})
    (hdir : ∀ j : Fin l, (weylCoxeterSystem P b).BruhatLE (dir j.succ).1 (dir j.castSucc).1) :
    Finset.univ.image dir ∈ bruhatChainComplex P b lam := by
  let : PartialOrder P.weylGroup := (weylCoxeterSystem P b).bruhatPartialOrder
  have hant : Antitone dir := Fin.antitone_iff_succ_le.mpr fun j ↦ by
    simpa only [← Subtype.coe_le_coe, CoxeterSystem.bruhatPartialOrder_le] using hdir j
  rw [mem_bruhatChainComplex_iff]
  refine ⟨Finset.univ_nonempty.image dir, fun u hu v hv ↦ ?_⟩
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hu
  obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hv
  exact (le_total j i).imp
    (fun hji ↦ by
      simpa only [← Subtype.coe_le_coe, CoxeterSystem.bruhatPartialOrder_le] using hant hji)
    (fun hij ↦ by
      simpa only [← Subtype.coe_le_coe, CoxeterSystem.bruhatPartialOrder_le] using hant hij)

/-- Continuous map from the closed standard `l`-simplex into the geometric realization of
`bruhatChainComplex P b lam` along any weakly decreasing Bruhat sequence `dir`. Equal directions
have their barycentric coordinates summed. -/
noncomputable def chainSimplexToRealization {l : ℕ}
    (dir : Fin (l + 1) →
      {w // (weylCoxeterSystem P b).IsMinimalCosetRep (P.wallIndices b lam) w})
    (hdir : ∀ j : Fin l, (weylCoxeterSystem P b).BruhatLE (dir j.succ).1 (dir j.castSucc).1) :
    C(Convexity.StdSimplex ℝ (Fin (l + 1)), (bruhatChainComplex P b lam).Realization) where
  toFun w :=
    let σ := Finset.univ.image dir
    let g : Fin (l + 1) → σ := fun j ↦ ⟨dir j, Finset.mem_image_of_mem dir (Finset.mem_univ j)⟩
    _root_.AbstractSimplicialComplex.faceInclusion (bruhatChainComplex P b lam)
      ⟨σ, image_dir_mem_bruhatChainComplex dir hdir⟩
      ((Finset.standardSimplexHomeomorph σ).symm (w.map g))
  continuous_toFun := by
    let σ := Finset.univ.image dir
    let g : Fin (l + 1) → σ := fun j ↦ ⟨dir j, Finset.mem_image_of_mem dir (Finset.mem_univ j)⟩
    exact (_root_.AbstractSimplicialComplex.continuous_faceInclusion _ _).comp
      ((Finset.standardSimplexHomeomorph σ).symm.continuous.comp
        (Convexity.StdSimplex.continuous_map ℝ g))

/-- The barycentric coordinates of `chainSimplexToRealization` are the pushforward of `w.weights`
along `dir`. -/
@[simp]
theorem chainSimplexToRealization_val {l : ℕ}
    (dir : Fin (l + 1) →
      {w // (weylCoxeterSystem P b).IsMinimalCosetRep (P.wallIndices b lam) w})
    (hdir : ∀ j : Fin l, (weylCoxeterSystem P b).BruhatLE (dir j.succ).1 (dir j.castSucc).1)
    (w : Convexity.StdSimplex ℝ (Fin (l + 1))) :
    (chainSimplexToRealization dir hdir w :
        {w // (weylCoxeterSystem P b).IsMinimalCosetRep (P.wallIndices b lam) w} →₀ ℝ) =
      w.weights.mapDomain dir := by
  simp only [chainSimplexToRealization, ContinuousMap.coe_mk,
    _root_.AbstractSimplicialComplex.faceInclusion_val, Finset.standardSimplexHomeomorph_symm_val,
    Convexity.StdSimplex.weights_map, ← Finsupp.mapDomain_comp]
  rfl

/-- Pulling back a weakly decreasing Bruhat sequence along a monotone map preserves the Bruhat
monotonicity condition. -/
theorem bruhatLE_comp_orderHom {m l : ℕ}
    {dir : Fin (l + 1) →
      {w // (weylCoxeterSystem P b).IsMinimalCosetRep (P.wallIndices b lam) w}}
    (hdir : ∀ j : Fin l, (weylCoxeterSystem P b).BruhatLE (dir j.succ).1 (dir j.castSucc).1)
    (φ : Fin (m + 1) →o Fin (l + 1)) (j : Fin m) :
    (weylCoxeterSystem P b).BruhatLE ((dir ∘ φ) j.succ).1 ((dir ∘ φ) j.castSucc).1 := by
  let : PartialOrder P.weylGroup := (weylCoxeterSystem P b).bruhatPartialOrder
  have hant : Antitone dir := Fin.antitone_iff_succ_le.mpr fun i ↦ by
    simpa only [← Subtype.coe_le_coe, CoxeterSystem.bruhatPartialOrder_le] using hdir i
  simpa only [Function.comp_apply, ← Subtype.coe_le_coe, CoxeterSystem.bruhatPartialOrder_le] using
    hant (φ.monotone j.castSucc_le_succ)

/-- Pulling back a weakly decreasing Bruhat sequence along `Fin.succAbove` preserves the Bruhat
monotonicity condition. -/
theorem bruhatLE_comp_succAbove {l : ℕ}
    {dir : Fin (l + 2) →
      {w // (weylCoxeterSystem P b).IsMinimalCosetRep (P.wallIndices b lam) w}}
    (hdir : ∀ j : Fin (l + 1), (weylCoxeterSystem P b).BruhatLE (dir j.succ).1 (dir j.castSucc).1)
    (p : Fin (l + 2)) (j : Fin l) :
    (weylCoxeterSystem P b).BruhatLE
      ((dir ∘ p.succAbove) j.succ).1 ((dir ∘ p.succAbove) j.castSucc).1 :=
  bruhatLE_comp_orderHom hdir p.succAboveOrderEmb.toOrderHom j

/-- **Simplicial functoriality in the Bruhat-chain polyhedron.** Pushing simplex coordinates
forward along any monotone map `φ` agrees with mapping along the pulled-back chain `dir ∘ φ`. -/
theorem chainSimplexToRealization_map_orderHom {m l : ℕ}
    (dir : Fin (l + 1) →
      {w // (weylCoxeterSystem P b).IsMinimalCosetRep (P.wallIndices b lam) w})
    (hdir : ∀ j : Fin l, (weylCoxeterSystem P b).BruhatLE (dir j.succ).1 (dir j.castSucc).1)
    (φ : Fin (m + 1) →o Fin (l + 1)) (w : Convexity.StdSimplex ℝ (Fin (m + 1))) :
    chainSimplexToRealization dir hdir (w.map φ) =
      chainSimplexToRealization (dir ∘ φ) (bruhatLE_comp_orderHom hdir φ) w := by
  apply Subtype.ext
  simp only [chainSimplexToRealization_val, Convexity.StdSimplex.weights_map,
    Finsupp.mapDomain_comp]

/-- **Face inclusion in the Bruhat-chain polyhedron.** Restricting to the facet opposite `p`
agrees with mapping the `(l - 1)`-simplex along the subchain `dir ∘ p.succAbove`. -/
@[simp]
theorem chainSimplexToRealization_map_succAbove {l : ℕ}
    (dir : Fin (l + 2) →
      {w // (weylCoxeterSystem P b).IsMinimalCosetRep (P.wallIndices b lam) w})
    (hdir : ∀ j : Fin (l + 1), (weylCoxeterSystem P b).BruhatLE (dir j.succ).1 (dir j.castSucc).1)
    (p : Fin (l + 2)) (w : Convexity.StdSimplex ℝ (Fin (l + 1))) :
    chainSimplexToRealization dir hdir (w.map p.succAbove) =
      chainSimplexToRealization (dir ∘ p.succAbove) (bruhatLE_comp_succAbove hdir p) w :=
  chainSimplexToRealization_map_orderHom dir hdir p.succAboveOrderEmb.toOrderHom w

/-- **Merging equal adjacent directions in the Bruhat-chain polyhedron.** When
`dir p.castSucc = dir p.succ`, collapsing the `(l + 1)`-simplex along `p.predAbove` onto the
merged chain `dir ∘ p.succ.succAbove` gives the exact same point in the realization. -/
theorem chainSimplexToRealization_map_predAbove {l : ℕ}
    {dir : Fin (l + 2) →
      {w // (weylCoxeterSystem P b).IsMinimalCosetRep (P.wallIndices b lam) w}}
    (hdir : ∀ j : Fin (l + 1), (weylCoxeterSystem P b).BruhatLE (dir j.succ).1 (dir j.castSucc).1)
    {p : Fin (l + 1)} (hmerge : dir p.castSucc = dir p.succ)
    (w : Convexity.StdSimplex ℝ (Fin (l + 2))) :
    chainSimplexToRealization (dir ∘ p.succ.succAbove)
        (bruhatLE_comp_succAbove hdir p.succ) (w.map p.predAbove) =
      chainSimplexToRealization dir hdir w := by
  have hcomp : (dir ∘ p.succ.succAbove) ∘ p.predAbove = dir := by
    funext i
    by_cases hi : i = p.succ
    · subst hi
      have hpred : p.predAbove p.succ = p := by
        rw [Fin.predAbove_of_castSucc_lt _ _ p.castSucc_lt_succ, Fin.pred_succ]
      simp [Function.comp_apply, hpred, Fin.succAbove_of_castSucc_lt _ _ p.castSucc_lt_succ,
        hmerge]
    · simp [Function.comp_apply, Fin.succ_succAbove_predAbove hi]
  apply Subtype.ext
  simp only [chainSimplexToRealization_val, Convexity.StdSimplex.weights_map,
    ← Finsupp.mapDomain_comp, hcomp]

/-- When all directions in `dir` are distinct (in particular for any strictly decreasing Bruhat
chain), `chainSimplexToRealization` embeds the closed `l`-simplex injectively into the
Bruhat-chain polyhedron. -/
theorem chainSimplexToRealization_injective {l : ℕ}
    {dir : Fin (l + 1) →
      {w // (weylCoxeterSystem P b).IsMinimalCosetRep (P.wallIndices b lam) w}}
    (hdir : ∀ j : Fin l, (weylCoxeterSystem P b).BruhatLE (dir j.succ).1 (dir j.castSucc).1)
    (hinj : Function.Injective dir) :
    Function.Injective (chainSimplexToRealization dir hdir) := by
  intro w₁ w₂ h
  apply Convexity.StdSimplex.ext
  exact Finsupp.mapDomain_injective hinj
    (by simpa only [chainSimplexToRealization_val] using congrArg Subtype.val h)

/-- The image of `chainSimplexToRealization dir hdir` consists of all realization points supported
within `Set.range dir`. -/
theorem range_chainSimplexToRealization {l : ℕ}
    (dir : Fin (l + 1) →
      {w // (weylCoxeterSystem P b).IsMinimalCosetRep (P.wallIndices b lam) w})
    (hdir : ∀ j : Fin l, (weylCoxeterSystem P b).BruhatLE (dir j.succ).1 (dir j.castSucc).1) :
    Set.range (chainSimplexToRealization dir hdir) =
      {x | (x.1.support : Set _) ⊆ Set.range dir} := by
  ext x
  constructor
  · rintro ⟨w, rfl⟩ u hu
    rw [Finset.mem_coe, chainSimplexToRealization_val] at hu
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hu)
    exact ⟨j, rfl⟩
  · intro hx
    let x' : Convexity.StdSimplex ℝ
        {w // (weylCoxeterSystem P b).IsMinimalCosetRep (P.wallIndices b lam) w} :=
      ⟨x.1, _root_.AbstractSimplicialComplex.Realization.nonneg _ x,
        _root_.AbstractSimplicialComplex.Realization.sum_eq_one _ x⟩
    let s : {w // (weylCoxeterSystem P b).IsMinimalCosetRep (P.wallIndices b lam) w} →
        Fin (l + 1) :=
      fun u ↦ if hu : u ∈ Set.range dir then hu.choose else 0
    refine ⟨x'.map s, Subtype.ext ?_⟩
    rw [chainSimplexToRealization_val, Convexity.StdSimplex.weights_map, ← Finsupp.mapDomain_comp]
    refine (Finsupp.mapDomain_congr fun u hu ↦ ?_).trans Finsupp.mapDomain_id
    have hur : u ∈ Set.range dir := hx hu
    simp only [Function.comp_apply, s, dite_eq_left hur, hur.choose_spec, id_eq]

/-- **Gluing along shared subchains.** Two closed chain simplices in the Bruhat-chain polyhedron
intersect precisely in the points supported on their common directions. -/
theorem range_chainSimplexToRealization_inter {l₁ l₂ : ℕ}
    (dir₁ : Fin (l₁ + 1) →
      {w // (weylCoxeterSystem P b).IsMinimalCosetRep (P.wallIndices b lam) w})
    (hdir₁ : ∀ j : Fin l₁, (weylCoxeterSystem P b).BruhatLE (dir₁ j.succ).1 (dir₁ j.castSucc).1)
    (dir₂ : Fin (l₂ + 1) →
      {w // (weylCoxeterSystem P b).IsMinimalCosetRep (P.wallIndices b lam) w})
    (hdir₂ : ∀ j : Fin l₂, (weylCoxeterSystem P b).BruhatLE (dir₂ j.succ).1 (dir₂ j.castSucc).1) :
    Set.range (chainSimplexToRealization dir₁ hdir₁) ∩
        Set.range (chainSimplexToRealization dir₂ hdir₂) =
      {x | (x.1.support : Set _) ⊆ Set.range dir₁ ∩ Set.range dir₂} := by
  rw [range_chainSimplexToRealization, range_chainSimplexToRealization]
  ext x
  exact Set.subset_inter_iff.symm

end BruhatChainComplex

section GlobalPath

variable {ι : Type u} {M : Type w} {N : Type x} [AddCommGroup M] [AddCommGroup N]
  {P : RootPairing ι ℤ M N} {b : P.Base} [Finite ι] [P.IsReduced] {lam : M}
  {V : Type*} [AddCommGroup V] [Module ℝ V]

private noncomputable def supportStandardSimplex
    (x : (bruhatChainComplex P b lam).Realization) :
    _root_.AbstractSimplicialComplex.StandardSimplex x.1.support :=
  ⟨x.1, by
    simpa only [_root_.AbstractSimplicialComplex.carrier_val] using
      _root_.AbstractSimplicialComplex.mem_convexHull_carrier _ x⟩

@[instance_reducible]
private noncomputable def chainLinearOrder
    {σ : Finset {w // (weylCoxeterSystem P b).IsMinimalCosetRep (P.wallIndices b lam) w}}
    (hσ : σ ∈ bruhatChainComplex P b lam) : LinearOrder ↥σ :=
  letI := (weylCoxeterSystem P b).bruhatPartialOrder
  have hchain : IsChain (· ≤ ·) (↑σ : Set _) :=
    (AbstractSimplicialComplex.mem_orderComplex_iff.mp hσ).2
  IsChain.linearOrder fun _ hx _ hy hne ↦
    (hchain hx hy hne).imp (lt_of_le_of_ne · hne) (lt_of_le_of_ne · hne.symm)

private noncomputable def chainVertexEquiv
    {σ : Finset {w // (weylCoxeterSystem P b).IsMinimalCosetRep (P.wallIndices b lam) w}}
    (hσ : σ ∈ bruhatChainComplex P b lam) : Fin σ.card ≃ ↥σ :=
  letI := (weylCoxeterSystem P b).bruhatPartialOrder
  letI := chainLinearOrder hσ
  (Fintype.orderIsoFinOfCardEq (OrderDual ↥σ) (k := σ.card) (by simp)).toEquiv.trans
    OrderDual.ofDual

private theorem bruhatLE_chainVertexEquiv_iff
    {σ : Finset {w // (weylCoxeterSystem P b).IsMinimalCosetRep (P.wallIndices b lam) w}}
    (hσ : σ ∈ bruhatChainComplex P b lam) {i j : Fin σ.card} :
    (weylCoxeterSystem P b).BruhatLE
      (chainVertexEquiv hσ j).1.1 (chainVertexEquiv hσ i).1.1 ↔ i ≤ j := by
  let : PartialOrder P.weylGroup := (weylCoxeterSystem P b).bruhatPartialOrder
  let : LinearOrder ↥σ := chainLinearOrder hσ
  let e : Fin σ.card ≃o OrderDual ↥σ :=
    Fintype.orderIsoFinOfCardEq (OrderDual ↥σ) (k := σ.card) (by simp)
  have hj : (chainVertexEquiv hσ j).1.1 = (OrderDual.ofDual (e j)).1.1 := rfl
  have hi : (chainVertexEquiv hσ i).1.1 = (OrderDual.ofDual (e i)).1.1 := rfl
  rw [hj, hi, ← CoxeterSystem.bruhatPartialOrder_le, Subtype.coe_le_coe, Subtype.coe_le_coe]
  exact OrderDual.ofDual_le_ofDual.trans e.le_iff_le

private noncomputable def bruhatFacePath (f : M →+ V)
    (σ : Finset {w // (weylCoxeterSystem P b).IsMinimalCosetRep (P.wallIndices b lam) w})
    (hσ : σ ∈ bruhatChainComplex P b lam) (w : Convexity.StdSimplex ℝ ↥σ) : PLPath ℝ V :=
  PLPath.chainSimplexPath
    (fun k : Fin σ.card ↦ f ((chainVertexEquiv hσ k).1.1 • lam))
    (w.map (chainVertexEquiv hσ).symm)

private theorem bruhatFacePath_mono (f : M →+ V)
    {σ τ : Finset {w // (weylCoxeterSystem P b).IsMinimalCosetRep (P.wallIndices b lam) w}}
    (hσ : σ ∈ bruhatChainComplex P b lam) (hτ : τ ∈ bruhatChainComplex P b lam) (hστ : σ ⊆ τ)
    (w : Convexity.StdSimplex ℝ ↥σ) :
    bruhatFacePath f τ hτ (w.map fun a ↦ ⟨a.1, hστ a.2⟩) = bruhatFacePath f σ hσ w := by
  let φ : Fin σ.card →o Fin τ.card :=
    ⟨fun k ↦ (chainVertexEquiv hτ).symm ⟨(chainVertexEquiv hσ k).1, hστ (chainVertexEquiv hσ k).2⟩,
      fun i j hij ↦ (bruhatLE_chainVertexEquiv_iff hτ).mp (by
        simpa using (bruhatLE_chainVertexEquiv_iff hσ).mpr hij)⟩
  have hmap :
      ((w.map fun a : ↥σ ↦ (⟨a.1, hστ a.2⟩ : ↥τ)).map (chainVertexEquiv hτ).symm) =
        (w.map (chainVertexEquiv hσ).symm).map φ := by
    rw [← Convexity.StdSimplex.map_comp, ← Convexity.StdSimplex.map_comp]
    congr 1
    funext a
    change (chainVertexEquiv hτ).symm ⟨a.1, hστ a.2⟩ =
      (chainVertexEquiv hτ).symm
        ⟨(chainVertexEquiv hσ ((chainVertexEquiv hσ).symm a)).1, _⟩
    simp
  have hvel :
      ((fun k : Fin τ.card ↦ f ((chainVertexEquiv hτ k).1.1 • lam)) ∘ φ) =
        fun k : Fin σ.card ↦ f ((chainVertexEquiv hσ k).1.1 • lam) := by
    funext k
    change f ((chainVertexEquiv hτ
      ((chainVertexEquiv hτ).symm ⟨(chainVertexEquiv hσ k).1, hστ (chainVertexEquiv hσ k).2⟩)).1.1 •
        lam) = f ((chainVertexEquiv hσ k).1.1 • lam)
    simp
  simp only [bruhatFacePath]
  rw [hmap, PLPath.chainSimplexPath_map_orderHom _ φ _, hvel]

/-- Evaluate a point of the Bruhat-chain polyhedron as a piecewise-linear path in `V`, traversing
its support directions in strictly decreasing Bruhat order with durations equal to its barycentric
coordinates. -/
noncomputable def bruhatRealizationPath (f : M →+ V)
    (x : (bruhatChainComplex P b lam).Realization) : PLPath ℝ V :=
  bruhatFacePath f x.1.support
    (_root_.AbstractSimplicialComplex.support_mem (bruhatChainComplex P b lam) x)
    (Finset.standardSimplexHomeomorph x.1.support (supportStandardSimplex x))

/-- **Compatibility of global path evaluation with fixed-chain simplices.** On every weakly
decreasing Bruhat sequence `dir`, `bruhatRealizationPath` agrees with `PLPath.chainSimplexPath`
(automatically merging equal adjacent directions and dropping zero-weight vertices). -/
@[simp]
theorem bruhatRealizationPath_chainSimplexToRealization (f : M →+ V) {l : ℕ}
    (dir : Fin (l + 1) →
      {w // (weylCoxeterSystem P b).IsMinimalCosetRep (P.wallIndices b lam) w})
    (hdir : ∀ j : Fin l, (weylCoxeterSystem P b).BruhatLE (dir j.succ).1 (dir j.castSucc).1)
    (w : Convexity.StdSimplex ℝ (Fin (l + 1))) :
    bruhatRealizationPath f (chainSimplexToRealization dir hdir w) =
      PLPath.chainSimplexPath (fun j ↦ f ((dir j).1 • lam)) w := by
  set x := chainSimplexToRealization dir hdir w
  let τ := Finset.univ.image dir
  have hτ : τ ∈ bruhatChainComplex P b lam := image_dir_mem_bruhatChainComplex dir hdir
  have hστ : x.1.support ⊆ τ := fun u hu ↦ by
    rw [chainSimplexToRealization_val] at hu
    exact Finset.image_subset_image (Finset.subset_univ _) (Finsupp.mapDomain_support hu)
  let g : Fin (l + 1) → ↥τ := fun j ↦ ⟨dir j, Finset.mem_image_of_mem dir (Finset.mem_univ j)⟩
  have hpush :
      (Finset.standardSimplexHomeomorph x.1.support (supportStandardSimplex x)).map
        (fun a ↦ (⟨a.1, hστ a.2⟩ : ↥τ)) = w.map g := by
    apply Convexity.StdSimplex.ext
    apply Finsupp.mapDomain_injective Subtype.val_injective
    rw [Convexity.StdSimplex.weights_map, Convexity.StdSimplex.weights_map,
      ← Finsupp.mapDomain_comp, ← Finsupp.mapDomain_comp]
    have hcomp₁ :
        (Subtype.val : ↥τ → _) ∘ (fun a : ↥x.1.support ↦ (⟨a.1, hστ a.2⟩ : ↥τ)) =
          (Subtype.val : ↥x.1.support → _) := rfl
    have hcomp₂ : (Subtype.val : ↥τ → _) ∘ g = dir := rfl
    rw [hcomp₁, hcomp₂, ← Finset.standardSimplexHomeomorph_symm_val, Homeomorph.symm_apply_apply]
    exact chainSimplexToRealization_val dir hdir w
  rw [bruhatRealizationPath, ← bruhatFacePath_mono f _ hτ hστ, hpush]
  let ψ : Fin (l + 1) →o Fin τ.card :=
    ⟨fun j ↦ (chainVertexEquiv hτ).symm (g j),
      Fin.monotone_iff_le_succ.mpr fun j ↦ (bruhatLE_chainVertexEquiv_iff hτ).mp (by
        simpa [g] using hdir j)⟩
  have hcomp : ((w.map g).map (chainVertexEquiv hτ).symm) = w.map ψ := by
    rw [← Convexity.StdSimplex.map_comp]
    rfl
  simp only [bruhatFacePath]
  rw [hcomp, PLPath.chainSimplexPath_map_orderHom _ ψ w]
  congr 1
  funext j
  simp [ψ, g]

private noncomputable def bruhatSupportVertex
    (x : (bruhatChainComplex P b lam).Realization) :
    Fin x.1.support.card ≃ ↥x.1.support :=
  chainVertexEquiv (_root_.AbstractSimplicialComplex.support_mem _ x)

private noncomputable def bruhatSupportSimplex
    (x : (bruhatChainComplex P b lam).Realization) :
    Convexity.StdSimplex ℝ (Fin x.1.support.card) :=
  (Finset.standardSimplexHomeomorph x.1.support (supportStandardSimplex x)).map
    (bruhatSupportVertex x).symm

private theorem weights_bruhatSupportSimplex_apply
    (x : (bruhatChainComplex P b lam).Realization) (k : Fin x.1.support.card) :
    (bruhatSupportSimplex x).weights k = x.1 (bruhatSupportVertex x k).1 := by
  have hk : k = (bruhatSupportVertex x).symm (bruhatSupportVertex x k) :=
    ((bruhatSupportVertex x).symm_apply_apply k).symm
  nth_rw 1 [hk]
  rw [bruhatSupportSimplex,
    Convexity.StdSimplex.weights_map_apply_of_injective (bruhatSupportVertex x).symm.injective]
  simp [supportStandardSimplex]

private theorem isDistinguished_bruhatSupportTimed {f : M →+ V}
    (hlam : lam ∈ dominantChamber P b)
    (hf : Set.InjOn f (Set.range fun w : P.weylGroup ↦ w • lam))
    (x : (bruhatChainComplex P b lam).Realization) :
    PLPath.IsDistinguished (Set.range fun w : P.weylGroup ↦ f (w • lam))
      (PLPath.chainSimplexTimed
        (fun k ↦ f ((bruhatSupportVertex x k).1.1 • lam)) (bruhatSupportSimplex x)) := by
  have := P.flip_isReduced
  refine PLPath.isDistinguished_chainSimplexTimed
    (S := Set.range fun w : P.weylGroup ↦ f (w • lam))
    (fun k ↦ ⟨(bruhatSupportVertex x k).1.1, rfl⟩) (fun k hk h ↦ ?_) (fun k ↦ ?_)
  · have heq := eq_of_isMinimalCosetRep_of_smul_eq hlam
      (bruhatSupportVertex x k).1.2 (bruhatSupportVertex x ⟨k.val + 1, hk⟩).1.2
      (hf ⟨_, rfl⟩ ⟨_, rfl⟩ h)
    exact (Fin.ne_of_lt (Nat.lt_succ_self k.val) : k ≠ ⟨k.val + 1, hk⟩)
      ((bruhatSupportVertex x).injective (Subtype.ext (Subtype.ext heq)))
  · rw [weights_bruhatSupportSimplex_apply]
    exact _root_.AbstractSimplicialComplex.Realization.pos_of_mem_support _ x
      (bruhatSupportVertex x k).2

private theorem eq_of_bruhatSupportVertex_eq
    {x₁ x₂ : (bruhatChainComplex P b lam).Realization}
    (hcard : x₁.1.support.card = x₂.1.support.card)
    (hval : ∀ k : Fin x₁.1.support.card,
      x₁.1 (bruhatSupportVertex x₁ k).1 = x₂.1 (bruhatSupportVertex x₂ (k.cast hcard)).1 ∧
        (bruhatSupportVertex x₁ k).1 = (bruhatSupportVertex x₂ (k.cast hcard)).1) :
    x₁ = x₂ := by
  have hsupp : x₁.1.support = x₂.1.support := by
    ext u
    constructor
    · intro hu
      let k := (bruhatSupportVertex x₁).symm ⟨u, hu⟩
      have hk : (bruhatSupportVertex x₁ k).1 = u :=
        congrArg Subtype.val ((bruhatSupportVertex x₁).apply_symm_apply ⟨u, hu⟩)
      rw [← hk, (hval k).2]
      exact (bruhatSupportVertex x₂ (k.cast hcard)).2
    · intro hu
      let k₂ := (bruhatSupportVertex x₂).symm ⟨u, hu⟩
      let k := k₂.cast hcard.symm
      have hk₂ : (bruhatSupportVertex x₂ (k.cast hcard)).1 = u := by simp [k, k₂]
      rw [← hk₂, ← (hval k).2]
      exact (bruhatSupportVertex x₁ k).2
  apply Subtype.ext
  ext u
  by_cases hu : u ∈ x₁.1.support
  · let k := (bruhatSupportVertex x₁).symm ⟨u, hu⟩
    have hk : (bruhatSupportVertex x₁ k).1 = u :=
      congrArg Subtype.val ((bruhatSupportVertex x₁).apply_symm_apply ⟨u, hu⟩)
    rw [← hk, (hval k).1, (hval k).2]
  · have hu₂ : u ∉ x₂.1.support := hsupp ▸ hu
    rw [Finsupp.notMem_support_iff.mp hu, Finsupp.notMem_support_iff.mp hu₂]

/-- **Global injectivity of path evaluation on the Bruhat-chain polyhedron.** For a dominant
weight `λ` whose realized Weyl orbit has no two distinct weights in the same ray, distinct points
of `(bruhatChainComplex P b lam).Realization` evaluate to distinct piecewise-linear paths. -/
theorem bruhatRealizationPath_injective {f : M →+ V} (hlam : lam ∈ dominantChamber P b)
    (hf : Set.InjOn f (Set.range fun w : P.weylGroup ↦ w • lam))
    (hS : (Set.range fun w : P.weylGroup ↦ f (w • lam)).Pairwise fun u v ↦ ¬ SameRay ℝ u v) :
    Function.Injective (bruhatRealizationPath (P := P) (b := b) (lam := lam) f) := by
  have := P.flip_isReduced
  intro x₁ x₂ hp
  have htimed :
      PLPath.chainSimplexTimed
          (fun k ↦ f ((bruhatSupportVertex x₁ k).1.1 • lam)) (bruhatSupportSimplex x₁) =
        PLPath.chainSimplexTimed
          (fun k ↦ f ((bruhatSupportVertex x₂ k).1.1 • lam)) (bruhatSupportSimplex x₂) :=
    (isDistinguished_bruhatSupportTimed hlam hf x₁).unique
      (isDistinguished_bruhatSupportTimed hlam hf x₂) hS
      (by simpa [PLPath.ofSegments_map_snd_chainSimplexTimed, bruhatRealizationPath, bruhatFacePath,
        bruhatSupportSimplex, bruhatSupportVertex] using hp)
  have hcard : x₁.1.support.card = x₂.1.support.card := by
    simpa [PLPath.chainSimplexTimed_def] using congrArg List.length htimed
  rw [PLPath.chainSimplexTimed_def, PLPath.chainSimplexTimed_def,
    List.ofFn_congr hcard.symm] at htimed
  have hentry (k : Fin x₁.1.support.card) := congrFun (List.ofFn_injective htimed) k
  refine eq_of_bruhatSupportVertex_eq hcard fun k ↦ ?_
  have hfst : x₁.1 (bruhatSupportVertex x₁ k).1 =
      x₂.1 (bruhatSupportVertex x₂ (k.cast hcard)).1 := by
    simpa [weights_bruhatSupportSimplex_apply] using congrArg Prod.fst (hentry k)
  have hsnd : x₁.1 (bruhatSupportVertex x₁ k).1 • f ((bruhatSupportVertex x₁ k).1.1 • lam) =
      x₂.1 (bruhatSupportVertex x₂ (k.cast hcard)).1 •
        f ((bruhatSupportVertex x₂ (k.cast hcard)).1.1 • lam) := by
    simpa [weights_bruhatSupportSimplex_apply] using congrArg Prod.snd (hentry k)
  rw [hfst] at hsnd
  have hpos := _root_.AbstractSimplicialComplex.Realization.pos_of_mem_support _ x₂
    (bruhatSupportVertex x₂ (k.cast hcard)).2
  exact ⟨hfst, Subtype.ext (eq_of_isMinimalCosetRep_of_smul_eq hlam
    (bruhatSupportVertex x₁ k).1.2 (bruhatSupportVertex x₂ (k.cast hcard)).1.2
    (hf ⟨_, rfl⟩ ⟨_, rfl⟩ (smul_right_injective V hpos.ne' hsnd)))⟩

end GlobalPath

section LSSubset

variable {ι : Type u} {M : Type w} {N : Type x} [AddCommGroup M] [AddCommGroup N]
  {P : RootPairing ι ℤ M N} {b : P.Base} [Finite ι] [P.IsReduced] {lam : M}

/-- Embed a Lakshmibai–Seshadri path `π` into the Bruhat-chain polyhedron at the barycentric point
determined by its segment durations along `π.dir`. -/
noncomputable def toBruhatRealization (π : LSPath P b lam) :
    (bruhatChainComplex P b lam).Realization :=
  chainSimplexToRealization π.dir (fun j ↦ π.bruhatLE_dir_succ j)
    (π.durationSimplex.mapRange (Rat.castHom ℝ) Rat.cast_mono)

/-- The barycentric coordinates of `π.toBruhatRealization` push its rational segment durations
forward along `π.dir`. -/
@[simp]
theorem toBruhatRealization_val (π : LSPath P b lam) :
    (π.toBruhatRealization :
        {w // (weylCoxeterSystem P b).IsMinimalCosetRep (P.wallIndices b lam) w} →₀ ℝ) =
      ((π.durationSimplex.mapRange (Rat.castHom ℝ) Rat.cast_mono).weights).mapDomain π.dir :=
  chainSimplexToRealization_val _ _ _

/-- The support of `π.toBruhatRealization` is the exact set of directions visited by `π`. -/
theorem coe_support_toBruhatRealization (π : LSPath P b lam) :
    (π.toBruhatRealization.1.support : Set _) = Set.range π.dir := by
  ext u
  constructor
  · intro hu
    rw [Finset.mem_coe, toBruhatRealization_val] at hu
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hu)
    exact ⟨j, rfl⟩
  · rintro ⟨j, rfl⟩
    rw [Finset.mem_coe, Finsupp.mem_support_iff, toBruhatRealization_val,
      Finsupp.mapDomain_apply_of_injective π.dir_injective]
    simpa using (π.duration_pos j).ne'

/-- Global path evaluation on `π.toBruhatRealization` recovers `π.toPLPath ℝ f`. -/
@[simp]
theorem bruhatRealizationPath_toBruhatRealization {V : Type*} [AddCommGroup V] [Module ℝ V]
    (f : M →+ V) (π : LSPath P b lam) :
    bruhatRealizationPath f π.toBruhatRealization = π.toPLPath ℝ f := by
  rw [toBruhatRealization, bruhatRealizationPath_chainSimplexToRealization,
    π.chainSimplexPath_durationSimplex ℝ f]

private theorem eq_of_strictAnti_of_range_eq {α : Type*} [PartialOrder α] {n : ℕ}
    {f₁ f₂ : Fin n → α} (hf₁ : StrictAnti f₁) (hf₂ : StrictAnti f₂)
    (hrange : Set.range f₁ = Set.range f₂) : f₁ = f₂ := by
  have hmem₁ (i : Fin n) : f₁ i ∈ Set.range f₂ := hrange ▸ ⟨i, rfl⟩
  have hmem₂ (k : Fin n) : f₂ k ∈ Set.range f₁ := hrange.symm ▸ ⟨k, rfl⟩
  let σ : Fin n → Fin n := fun i ↦ (hmem₁ i).choose
  let τ : Fin n → Fin n := fun k ↦ (hmem₂ k).choose
  have hσ (i : Fin n) : f₂ (σ i) = f₁ i := (hmem₁ i).choose_spec
  have hτ (k : Fin n) : f₁ (τ k) = f₂ k := (hmem₂ k).choose_spec
  have hσ_mono : StrictMono σ := fun i j hij ↦ by
    by_contra! hle
    exact (hf₁ hij).not_ge (by rw [← hσ i, ← hσ j]; exact hf₂.antitone hle)
  have hτ_mono : StrictMono τ := fun i j hij ↦ by
    by_contra! hle
    exact (hf₂ hij).not_ge (by rw [← hτ i, ← hτ j]; exact hf₁.antitone hle)
  funext i
  have hτσ : τ (σ i) = i := hf₁.injective (by rw [hτ, hσ])
  have h1 : i ≤ σ i := hσ_mono.id_le i
  have h2 : σ i ≤ i := by simpa [hτσ] using hτ_mono.id_le (σ i)
  rw [← hσ i, le_antisymm h2 h1]

private theorem dir_eq_of_toBruhatRealization_eq {π₁ π₂ : LSPath P b lam}
    (h : π₁.toBruhatRealization = π₂.toBruhatRealization) :
    ∃ hlen : π₁.length = π₂.length,
      π₁.dir = fun j ↦ π₂.dir (j.cast (congrArg (· + 1) hlen)) := by
  let : PartialOrder P.weylGroup := (weylCoxeterSystem P b).bruhatPartialOrder
  have hrange : Set.range π₁.dir = Set.range π₂.dir := by
    rw [← coe_support_toBruhatRealization, ← coe_support_toBruhatRealization, h]
  have hlen : π₁.length = π₂.length := by
    have hcard := congrArg Set.ncard hrange
    rw [Set.ncard_range_of_injective π₁.dir_injective,
      Set.ncard_range_of_injective π₂.dir_injective, Nat.card_fin, Nat.card_fin] at hcard
    omega
  let g : Fin (π₁.length + 1) → _ := fun j ↦ π₂.dir (j.cast (congrArg (· + 1) hlen))
  have hg_range : Set.range π₁.dir = Set.range g := by
    refine hrange.trans ?_
    ext u
    exact ⟨fun ⟨k, hk⟩ ↦ ⟨k.cast (congrArg (· + 1) hlen.symm), by simpa [g] using hk⟩,
      fun ⟨j, hj⟩ ↦ ⟨_, hj⟩⟩
  have hanti₁ : StrictAnti π₁.dir := Fin.strictAnti_iff_succ_lt.mpr fun j ↦
    lt_of_le_of_ne
      (by simpa only [← Subtype.coe_le_coe, CoxeterSystem.bruhatPartialOrder_le] using
        π₁.bruhatLE_dir_succ j)
      (π₁.dir_succ_ne j)
  have hanti₂ : StrictAnti g := Fin.strictAnti_iff_succ_lt.mpr fun j ↦ by
    let j' : Fin π₂.length := j.cast hlen
    have hs : j'.succ = j.succ.cast (congrArg (· + 1) hlen) := Fin.ext rfl
    have hc : j'.castSucc = j.castSucc.cast (congrArg (· + 1) hlen) := Fin.ext rfl
    have hle := π₂.bruhatLE_dir_succ j'
    have hne := π₂.dir_succ_ne j'
    rw [hs, hc] at hle hne
    exact lt_of_le_of_ne
      (by simpa only [← Subtype.coe_le_coe, CoxeterSystem.bruhatPartialOrder_le, g] using hle)
      hne
  exact ⟨hlen, eq_of_strictAnti_of_range_eq hanti₁ hanti₂ hg_range⟩

/-- `LSPath.toBruhatRealization` is injective for every weight `λ`. -/
theorem toBruhatRealization_injective :
    Function.Injective (toBruhatRealization (P := P) (b := b) (lam := lam)) := by
  intro π₁ π₂ h
  obtain ⟨hlen, hdir_eq⟩ := dir_eq_of_toBruhatRealization_eq h
  have hdur (j : Fin (π₁.length + 1)) :
      π₁.duration j = π₂.duration (j.cast (congrArg (· + 1) hlen)) := by
    have hval := congrArg (fun x : (bruhatChainComplex P b lam).Realization ↦ x.1 (π₁.dir j)) h
    rw [toBruhatRealization_val, toBruhatRealization_val,
      Finsupp.mapDomain_apply_of_injective π₁.dir_injective] at hval
    have hgj : π₁.dir j = π₂.dir (j.cast (congrArg (· + 1) hlen)) := congrFun hdir_eq j
    rw [hgj, Finsupp.mapDomain_apply_of_injective π₂.dir_injective] at hval
    simpa using hval
  apply LSPath.ext
  · rw [List.ofFn_congr (congrArg (· + 1) hlen).symm]
    exact congrArg List.ofFn hdir_eq
  · rw [List.ofFn_congr (congrArg (· + 2) hlen).symm]
    apply congrArg List.ofFn
    have hfun :
        (⇑π₁.durationSimplex.weights : Fin (π₁.length + 1) → ℚ) =
          fun j ↦ π₂.duration (j.cast (congrArg (· + 1) hlen)) := by
      funext j
      simpa using hdur j
    have hfun₂ : (⇑π₂.durationSimplex.weights : Fin (π₂.length + 1) → ℚ) = π₂.duration := by
      funext j
      simp
    have hval (m : ℕ) (hm : m ≤ π₁.length + 1) :
        prefixSum m (fun j : Fin (π₁.length + 1) ↦
            π₂.duration (j.cast (congrArg (· + 1) hlen))) =
          prefixSum m π₂.duration := by
      induction m with
      | zero => simp
      | succ m ih =>
        rw [prefixSum_succ hm, prefixSum_succ (by omega), ih (by omega)]
        rfl
    funext k
    rw [← π₁.breakTime_durationSimplex, ← π₂.breakTime_durationSimplex,
      Convexity.StdSimplex.breakTime_def, Convexity.StdSimplex.breakTime_def, hfun, hfun₂]
    exact hval k.val (Nat.le_of_lt_succ k.isLt)

/-- For a dominant shape `λ`, the Lakshmibai–Seshadri subset of the Bruhat-chain polyhedron is
finite. -/
theorem finite_range_toBruhatRealization (hlam : lam ∈ dominantChamber P b) :
    (Set.range (toBruhatRealization (P := P) (b := b) (lam := lam))).Finite := by
  have := LSPath.finite hlam
  exact Set.finite_range _

/-- Whenever `⟨λ, αᵢ^∨⟩ ≠ 0` for some simple root `αᵢ`, the Bruhat-chain polyhedron contains the
embedded real `1`-simplex on `{sᵢ, 1}` and is therefore uncountable. -/
theorem not_countable_bruhatChainRealization
    (h : ∃ i : b.support, P.coroot' i lam ≠ 0) :
    ¬ Countable (bruhatChainComplex P b lam).Realization := by
  obtain ⟨i, hi⟩ := h
  have hcov := minimalCosetRepCovBy_one_simple_of_coroot'_ne_zero hi
  let dir : Fin 2 →
      {w // (weylCoxeterSystem P b).IsMinimalCosetRep (P.wallIndices b lam) w} :=
    ![⟨(weylCoxeterSystem P b).simple i, hcov.isMinimalCosetRep_right⟩,
      ⟨1, hcov.isMinimalCosetRep_left⟩]
  have hdir : ∀ j : Fin 1, (weylCoxeterSystem P b).BruhatLE (dir j.succ).1 (dir j.castSucc).1 := by
    intro j
    rw [Subsingleton.elim j 0]
    exact hcov.bruhatLE
  have hinj : Function.Injective dir := by
    intro a c hac
    fin_cases a <;> fin_cases c
    · rfl
    · exact absurd (congrArg Subtype.val hac).symm hcov.ne
    · exact absurd (congrArg Subtype.val hac) hcov.ne
    · rfl
  intro hcount
  exact Convexity.StdSimplex.not_countable_real (X := Fin 2)
    (@Function.Injective.countable _ _ hcount _ (chainSimplexToRealization_injective hdir hinj))

/-- **Exact strict-containment criterion.** For a dominant weight `λ`, the finite LS subset is a
strict subset of `(bruhatChainComplex P b lam).Realization` if and only if `λ` pairs nontrivially
with at least one simple coroot. (When all simple-coroot pairings vanish, `W_λ = W` and the
polyhedron is a single vertex hit by `LSPath.straight`.) -/
theorem range_toBruhatRealization_ssubset_univ_iff (hlam : lam ∈ dominantChamber P b) :
    Set.range (toBruhatRealization (P := P) (b := b) (lam := lam)) ⊂ Set.univ ↔
      ∃ i : b.support, P.coroot' i lam ≠ 0 := by
  rw [Set.ssubset_univ_iff]
  constructor
  · intro hne
    by_contra! hall
    apply hne
    have hwall : P.wallIndices b lam = Set.univ :=
      Set.eq_univ_of_forall fun i ↦ mem_wallIndices.mpr (hall i)
    let u₀ : {w // (weylCoxeterSystem P b).IsMinimalCosetRep (P.wallIndices b lam) w} :=
      ⟨1, (weylCoxeterSystem P b).isMinimalCosetRep_one _⟩
    have huniq : ∀ u : {w // (weylCoxeterSystem P b).IsMinimalCosetRep (P.wallIndices b lam) w},
        u = u₀ := by
      intro u
      apply Subtype.ext
      by_contra hu1
      obtain ⟨i, hdesc⟩ := (weylCoxeterSystem P b).exists_rightDescent_of_ne_one hu1
      exact ((weylCoxeterSystem P b).isMinimalCosetRep_iff.mp u.2) i (hwall ▸ Set.mem_univ i) hdesc
    ext x
    simp only [Set.mem_range, Set.mem_univ, iff_true]
    refine ⟨straight lam, Subtype.ext ?_⟩
    ext u
    rw [huniq u]
    have hsum₁ := _root_.AbstractSimplicialComplex.Realization.sum_eq_one _
      (straight (P := P) (b := b) lam).toBruhatRealization
    have hsum₂ := _root_.AbstractSimplicialComplex.Realization.sum_eq_one _ x
    rw [Finsupp.sum_eq_single u₀ (fun v _ hvu ↦ absurd (huniq v) hvu) (by simp)] at hsum₁ hsum₂
    exact hsum₁.trans hsum₂.symm
  · intro hex heq
    have hcount : Countable (Set.univ : Set (bruhatChainComplex P b lam).Realization) := by
      rw [← heq]
      exact (finite_range_toBruhatRealization hlam).countable
    exact not_countable_bruhatChainRealization hex (Set.countable_univ_iff.mp hcount)

end LSSubset

section TypeATwo

variable {ι : Type u} {M : Type w} {N : Type x} [AddCommGroup M] [AddCommGroup N]
  {P : RootPairing ι ℤ M N} {b : P.Base} [Finite ι] [P.IsReduced] {lam : M}

private theorem mem_symmetricThreeBruhatComplex_iff_bruhatLE
    {σ : Finset (Equiv.Perm (Fin 3))} :
    σ ∈ symmetricThreeBruhatComplex ↔
      σ.Nonempty ∧ ∀ u ∈ σ, ∀ v ∈ σ,
        (permCoxeterSystem 3).BruhatLE u v ∨ (permCoxeterSystem 3).BruhatLE v u := by
  rw [mem_symmetricThreeBruhatComplex_iff]
  refine and_congr_right fun _ ↦ ⟨fun hinj u hu v hv ↦ ?_, fun h u hu v hv he ↦ ?_⟩
  · simp only [Equiv.Perm.bruhatLE_three_iff]
    rcases lt_trichotomy ((permCoxeterSystem 3).length u)
        ((permCoxeterSystem 3).length v) with hlt | he | hlt
    · exact Or.inl (Or.inr hlt)
    · exact Or.inl (Or.inl (hinj hu hv he))
    · exact Or.inr (Or.inr hlt)
  · rcases h u hu v hv with hle | hle
    · exact (Equiv.Perm.bruhatLE_three_iff u v).mp hle |>.resolve_right (by omega)
    · exact ((Equiv.Perm.bruhatLE_three_iff v u).mp hle |>.resolve_right (by omega)).symm

/-- In type `A₂` at a regular weight `λ` (`∀ i : b.support, ⟨λ, αᵢ^∨⟩ ≠ 0`), `W_λ` is trivial and
the minimal coset representatives identify with `Equiv.Perm (Fin 3)` via
`RootPairing.typeAWeylGroupEquiv`. -/
noncomputable def typeATwoMinimalCosetRepEquiv (e : b.support ≃ Fin 2)
    (he : ∀ i j, b.cartanMatrix i j = CartanMatrix.A 2 (e i) (e j))
    (hreg : ∀ i : b.support, P.coroot' i lam ≠ 0) :
    {w // (weylCoxeterSystem P b).IsMinimalCosetRep (P.wallIndices b lam) w} ≃
      Equiv.Perm (Fin 3) where
  toFun u := P.typeAWeylGroupEquiv b e he u.1
  invFun σ := ⟨(P.typeAWeylGroupEquiv b e he).symm σ, by
    have hwall : P.wallIndices b lam = ∅ :=
      Set.eq_empty_iff_forall_notMem.mpr fun i hi ↦ hreg i (mem_wallIndices.mp hi)
    simp [hwall]⟩
  left_inv u := Subtype.ext ((P.typeAWeylGroupEquiv b e he).symm_apply_apply u.1)
  right_inv σ := (P.typeAWeylGroupEquiv b e he).apply_symm_apply σ

/-- `typeATwoMinimalCosetRepEquiv` preserves and reflects the Bruhat order. -/
@[simp]
theorem bruhatLE_typeATwoMinimalCosetRepEquiv_iff (e : b.support ≃ Fin 2)
    (he : ∀ i j, b.cartanMatrix i j = CartanMatrix.A 2 (e i) (e j))
    (hreg : ∀ i : b.support, P.coroot' i lam ≠ 0)
    {u v : {w // (weylCoxeterSystem P b).IsMinimalCosetRep (P.wallIndices b lam) w}} :
    (permCoxeterSystem 3).BruhatLE
        (typeATwoMinimalCosetRepEquiv e he hreg u)
        (typeATwoMinimalCosetRepEquiv e he hreg v) ↔
      (weylCoxeterSystem P b).BruhatLE u.1 v.1 :=
  P.bruhatLE_typeAWeylGroupEquiv_iff b e he

/-- Under `typeATwoMinimalCosetRepEquiv`, a finite set of minimal coset representatives is a face of
`bruhatChainComplex P b lam` if and only if its image in `Equiv.Perm (Fin 3)` is a face of
`symmetricThreeBruhatComplex`. -/
theorem map_mem_symmetricThreeBruhatComplex_iff (e : b.support ≃ Fin 2)
    (he : ∀ i j, b.cartanMatrix i j = CartanMatrix.A 2 (e i) (e j))
    (hreg : ∀ i : b.support, P.coroot' i lam ≠ 0)
    {σ : Finset {w // (weylCoxeterSystem P b).IsMinimalCosetRep (P.wallIndices b lam) w}} :
    σ.map (typeATwoMinimalCosetRepEquiv e he hreg).toEmbedding ∈ symmetricThreeBruhatComplex ↔
      σ ∈ bruhatChainComplex P b lam := by
  let eqv := typeATwoMinimalCosetRepEquiv e he hreg
  rw [mem_symmetricThreeBruhatComplex_iff_bruhatLE, mem_bruhatChainComplex_iff,
    Finset.map_nonempty]
  refine and_congr_right fun _ ↦ ⟨fun h u hu v hv ↦ ?_, fun h x hx y hy ↦ ?_⟩
  · exact (h (eqv u) (Finset.mem_map_of_mem _ hu) (eqv v) (Finset.mem_map_of_mem _ hv)).imp
      (bruhatLE_typeATwoMinimalCosetRepEquiv_iff e he hreg).mp
      (bruhatLE_typeATwoMinimalCosetRepEquiv_iff e he hreg).mp
  · obtain ⟨u, hu, rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨v, hv, rfl⟩ := Finset.mem_map.mp hy
    exact (h u hu v hv).imp
      (bruhatLE_typeATwoMinimalCosetRepEquiv_iff e he hreg).mpr
      (bruhatLE_typeATwoMinimalCosetRepEquiv_iff e he hreg).mpr

/-- The Bruhat-chain complex of `W / W_λ` for a regular weight in type `A₂` has `6` vertices. -/
theorem card_typeATwo_minimalCosetRep (e : b.support ≃ Fin 2)
    (he : ∀ i j, b.cartanMatrix i j = CartanMatrix.A 2 (e i) (e j))
    (hreg : ∀ i : b.support, P.coroot' i lam ≠ 0) :
    Nat.card {w // (weylCoxeterSystem P b).IsMinimalCosetRep (P.wallIndices b lam) w} = 6 := by
  rw [Nat.card_congr (typeATwoMinimalCosetRepEquiv e he hreg), Nat.card_perm, Nat.card_fin]
  rfl

/-- **Homeomorphism of the `A₂` regular Bruhat-chain polyhedron with the six-vertex `S₃`
four-tetrahedron complex.** -/
noncomputable def typeATwoBruhatRealizationHomeomorph (e : b.support ≃ Fin 2)
    (he : ∀ i j, b.cartanMatrix i j = CartanMatrix.A 2 (e i) (e j))
    (hreg : ∀ i : b.support, P.coroot' i lam ≠ 0) :
    (bruhatChainComplex P b lam).Realization ≃ₜ symmetricThreeBruhatComplex.Realization := by
  let eqv := typeATwoMinimalCosetRepEquiv e he hreg
  let fSimp : _root_.PreAbstractSimplicialComplex.SimplicialMap
      (bruhatChainComplex P b lam).toPreAbstractSimplicialComplex
      symmetricThreeBruhatComplex.toPreAbstractSimplicialComplex :=
    { toFun := eqv
      map_face' := fun σ hσ ↦ by
        rw [_root_.AbstractSimplicialComplex.mem_toPreAbstractSimplicialComplex,
          ← eqv.coe_toEmbedding, ← Finset.map_eq_image,
          map_mem_symmetricThreeBruhatComplex_iff e he hreg]
        exact hσ }
  let gSimp : _root_.PreAbstractSimplicialComplex.SimplicialMap
      symmetricThreeBruhatComplex.toPreAbstractSimplicialComplex
      (bruhatChainComplex P b lam).toPreAbstractSimplicialComplex :=
    { toFun := eqv.symm
      map_face' := fun σ hσ ↦ by
        rw [_root_.AbstractSimplicialComplex.mem_toPreAbstractSimplicialComplex,
          ← eqv.symm.coe_toEmbedding, ← Finset.map_eq_image,
          ← map_mem_symmetricThreeBruhatComplex_iff e he hreg]
        have hmap : (σ.map eqv.symm.toEmbedding).map eqv.toEmbedding = σ := by
          simp [Finset.map_map]
        rwa [hmap] }
  exact fSimp.realizationHomeomorph gSimp
    (DFunLike.coe_injective (funext fun u ↦ by simp [fSimp, gSimp, eqv]))
    (DFunLike.coe_injective (funext fun σ ↦ by simp [fSimp, gSimp, eqv]))

/-- The four maximal tetrahedra of `bruhatChainComplex P b lam` for a regular weight in type `A₂`,
transported from `symmetricThreeBruhatTetrahedron`. -/
noncomputable def typeATwoBruhatTetrahedron (e : b.support ≃ Fin 2)
    (he : ∀ i j, b.cartanMatrix i j = CartanMatrix.A 2 (e i) (e j))
    (hreg : ∀ i : b.support, P.coroot' i lam ≠ 0) (a c : Fin 2) :
    Finset {w // (weylCoxeterSystem P b).IsMinimalCosetRep (P.wallIndices b lam) w} :=
  (symmetricThreeBruhatTetrahedron a c).map
    (typeATwoMinimalCosetRepEquiv e he hreg).symm.toEmbedding

/-- Each maximal tetrahedron of `bruhatChainComplex P b lam` in type `A₂` has `4` vertices. -/
@[simp]
theorem card_typeATwoBruhatTetrahedron (e : b.support ≃ Fin 2)
    (he : ∀ i j, b.cartanMatrix i j = CartanMatrix.A 2 (e i) (e j))
    (hreg : ∀ i : b.support, P.coroot' i lam ≠ 0) (a c : Fin 2) :
    (typeATwoBruhatTetrahedron e he hreg a c).card = 4 := by
  simp [typeATwoBruhatTetrahedron]

/-- Each `typeATwoBruhatTetrahedron` is a face of `bruhatChainComplex P b lam`. -/
theorem typeATwoBruhatTetrahedron_mem (e : b.support ≃ Fin 2)
    (he : ∀ i j, b.cartanMatrix i j = CartanMatrix.A 2 (e i) (e j))
    (hreg : ∀ i : b.support, P.coroot' i lam ≠ 0) (a c : Fin 2) :
    typeATwoBruhatTetrahedron e he hreg a c ∈ bruhatChainComplex P b lam := by
  rw [← map_mem_symmetricThreeBruhatComplex_iff e he hreg]
  have hmap : (typeATwoBruhatTetrahedron e he hreg a c).map
      (typeATwoMinimalCosetRepEquiv e he hreg).toEmbedding =
      symmetricThreeBruhatTetrahedron a c := by
    simp [typeATwoBruhatTetrahedron, Finset.map_map]
  rw [hmap]
  exact symmetricThreeBruhatTetrahedron_mem a c

/-- The four tetrahedra `typeATwoBruhatTetrahedron e he hreg a c` are pairwise distinct. -/
theorem typeATwoBruhatTetrahedron_injective (e : b.support ≃ Fin 2)
    (he : ∀ i j, b.cartanMatrix i j = CartanMatrix.A 2 (e i) (e j))
    (hreg : ∀ i : b.support, P.coroot' i lam ≠ 0) :
    Function.Injective
      (fun ac : Fin 2 × Fin 2 ↦ typeATwoBruhatTetrahedron e he hreg ac.1 ac.2) := by
  intro ac bd h
  apply symmetricThreeBruhatTetrahedron_injective
  have hmap := congrArg (Finset.map (typeATwoMinimalCosetRepEquiv e he hreg).toEmbedding) h
  simpa [typeATwoBruhatTetrahedron, Finset.map_map] using hmap

/-- The maximal faces of `bruhatChainComplex P b lam` for a regular weight in type `A₂` are
precisely the four tetrahedra `typeATwoBruhatTetrahedron e he hreg a c`. -/
theorem maximal_typeATwo_bruhatChainComplex_iff (e : b.support ≃ Fin 2)
    (he : ∀ i j, b.cartanMatrix i j = CartanMatrix.A 2 (e i) (e j))
    (hreg : ∀ i : b.support, P.coroot' i lam ≠ 0)
    {σ : Finset {w // (weylCoxeterSystem P b).IsMinimalCosetRep (P.wallIndices b lam) w}} :
    Maximal (· ∈ bruhatChainComplex P b lam) σ ↔
      ∃ a c, σ = typeATwoBruhatTetrahedron e he hreg a c := by
  let eqv := typeATwoMinimalCosetRepEquiv e he hreg
  constructor
  · intro hmax
    have hmax' : Maximal (· ∈ symmetricThreeBruhatComplex) (σ.map eqv.toEmbedding) := by
      refine ⟨(map_mem_symmetricThreeBruhatComplex_iff e he hreg).mpr hmax.prop,
        fun ρ hρ hsub ↦ ?_⟩
      let τ := ρ.map eqv.symm.toEmbedding
      have hτρ : τ.map eqv.toEmbedding = ρ := by simp [τ, Finset.map_map]
      have hστ : σ ⊆ τ := fun u hu ↦ by
        simpa [τ] using Finset.mem_map_of_mem eqv.symm.toEmbedding
          (hsub (Finset.mem_map_of_mem eqv.toEmbedding hu))
      have heq := le_antisymm hστ
        (hmax.2 ((map_mem_symmetricThreeBruhatComplex_iff e he hreg).mp (hτρ ▸ hρ)) hστ)
      rw [← hτρ, ← heq]
    obtain ⟨a, c, hac⟩ := maximal_symmetricThreeBruhatComplex_iff.mp hmax'
    refine ⟨a, c, ?_⟩
    have hmap := congrArg (Finset.map eqv.symm.toEmbedding) hac
    simpa [typeATwoBruhatTetrahedron, Finset.map_map] using hmap
  · rintro ⟨a, c, rfl⟩
    refine ⟨typeATwoBruhatTetrahedron_mem e he hreg a c, fun τ hτ hsub ↦ ?_⟩
    have hmax' := maximal_symmetricThreeBruhatComplex_iff.mpr ⟨a, c, rfl⟩
    have hsub' : symmetricThreeBruhatTetrahedron a c ⊆ τ.map eqv.toEmbedding := fun x hx ↦ by
      have hmem := hsub (Finset.mem_map_of_mem eqv.symm.toEmbedding hx)
      simpa using Finset.mem_map_of_mem eqv.toEmbedding hmem
    have heq := le_antisymm hsub'
      (hmax'.2 ((map_mem_symmetricThreeBruhatComplex_iff e he hreg).mpr hτ) hsub')
    have hmap := congrArg (Finset.map eqv.symm.toEmbedding) heq
    have heq' : τ = typeATwoBruhatTetrahedron e he hreg a c := by
      simpa [typeATwoBruhatTetrahedron, Finset.map_map] using hmap.symm
    exact heq'.le

private theorem dir_two_three_of_hasCartanType_A_two (hA : HasCartanType P b (.A 2))
    {π : LSPath P b lam} (hlen : 3 ≤ π.length) :
    (π.dir ⟨3, by omega⟩).1 = 1 ∧
      ∃ i : b.support, (π.dir ⟨2, by omega⟩).1 = (weylCoxeterSystem P b).simple i := by
  have htop : (weylCoxeterSystem P b).length (π.dir ⟨0, by omega⟩).1 ≤ 3 := by
    rw [length_weylCoxeterSystem_eq]
    exact (ncard_inversions_le P b _).trans (by rw [P.ncard_posRoots_of_hasCartanType_A b hA])
  have h01 : (weylCoxeterSystem P b).length (π.dir ⟨1, by omega⟩).1 <
      (weylCoxeterSystem P b).length (π.dir ⟨0, by omega⟩).1 :=
    π.strictAnti_length_dir (show (⟨0, by omega⟩ : Fin (π.length + 1)) < ⟨1, by omega⟩
      from by simp [Fin.lt_def])
  have h12 : (weylCoxeterSystem P b).length (π.dir ⟨2, by omega⟩).1 <
      (weylCoxeterSystem P b).length (π.dir ⟨1, by omega⟩).1 :=
    π.strictAnti_length_dir (show (⟨1, by omega⟩ : Fin (π.length + 1)) < ⟨2, by omega⟩
      from by simp [Fin.lt_def])
  have h23 : (weylCoxeterSystem P b).length (π.dir ⟨3, by omega⟩).1 <
      (weylCoxeterSystem P b).length (π.dir ⟨2, by omega⟩).1 :=
    π.strictAnti_length_dir (show (⟨2, by omega⟩ : Fin (π.length + 1)) < ⟨3, by omega⟩
      from by simp [Fin.lt_def])
  have hl3 : (weylCoxeterSystem P b).length (π.dir ⟨3, by omega⟩).1 = 0 := by omega
  have hl2 : (weylCoxeterSystem P b).length (π.dir ⟨2, by omega⟩).1 = 1 := by omega
  obtain ⟨ω, hω, hprod⟩ := (weylCoxeterSystem P b).exists_isReduced (π.dir ⟨2, by omega⟩).1
  rw [hprod] at hl2
  obtain ⟨i, rfl⟩ := List.length_eq_one_iff.mp (hω.eq.symm.trans hl2)
  exact ⟨(weylCoxeterSystem P b).length_eq_zero_iff.mp hl3, i, by simpa using hprod⟩

/-- **Distinguishing the four-tetrahedron `S₃` realization from the fixed-`λ` LS path set at unit
simple-coroot pairings.** On any root datum of Cartan type `A₂` and any weight `λ` with
`⟨λ, αᵢ^∨⟩ = 1` on both simple coroots, every LS path of shape `λ` has `π.length < 3` (at most
three directions). Consequently no LS path of shape `λ` enters the open interior of any of the
four maximal tetrahedra. -/
theorem length_lt_three_of_hasCartanType_A_two (hA : HasCartanType P b (.A 2))
    (hρ : ∀ i : b.support, P.coroot' i lam = 1) (π : LSPath P b lam) :
    π.length < 3 := by
  by_contra! hlen
  have hlam : lam ∈ dominantChamber P b :=
    (mem_dominantChamber P b lam).mpr fun i hi ↦ by rw [hρ ⟨i, hi⟩]; exact zero_le_one
  obtain ⟨hd3, i, hd2⟩ := dir_two_three_of_hasCartanType_A_two hA hlen
  let j : Fin π.length := ⟨2, by omega⟩
  obtain ⟨C, hCh, hCl, hC⟩ := π.exists_isAChain j
  have hdvd : (π.time j.castSucc.succ).den ∣
      intervalBondGcd b lam ((weylCoxeterSystem P b).simple i) 1 := by
    rw [isAChain_iff_den_dvd_intervalBondGcd hlam, hCh, hCl] at hC
    simpa [j, hd2, hd3] using hC
  have hcov := minimalCosetRepCovBy_one_simple_of_coroot'_ne_zero (i := i)
    (by rw [hρ i]; exact one_ne_zero)
  rw [intervalBondGcd_of_minimalCosetRepCovBy hlam hcov,
    reflectionBond_simple_smul_one_smul, hρ i] at hdvd
  have hden : (π.time j.castSucc.succ).den = 1 := Nat.dvd_one.mp hdvd
  have h0 : (0 : ℚ) < π.time j.castSucc.succ := by
    rw [← π.time_zero]
    exact π.strictMono_time (Fin.succ_pos _)
  have h1 : π.time j.castSucc.succ < 1 := by
    rw [← π.time_last]
    exact π.strictMono_time (by simp [Fin.lt_def, j]; omega)
  have hnum : ((π.time j.castSucc.succ).num : ℚ) = π.time j.castSucc.succ :=
    Rat.intCast_num_of_den_eq_one hden
  rw [← hnum] at h0 h1
  have h0' : (0 : ℤ) < (π.time j.castSucc.succ).num := Int.cast_pos.mp h0
  have h1' : (π.time j.castSucc.succ).num < 1 := by exact_mod_cast h1
  omega

/-- No LS path of shape `λ` with unit simple-coroot pairings in type `A₂` has support equal to any
of the four maximal Bruhat tetrahedra. -/
theorem support_toBruhatRealization_ne_typeATwoBruhatTetrahedron (e : b.support ≃ Fin 2)
    (he : ∀ i j, b.cartanMatrix i j = CartanMatrix.A 2 (e i) (e j))
    (hρ : ∀ i : b.support, P.coroot' i lam = 1) (π : LSPath P b lam) (a c : Fin 2) :
    π.toBruhatRealization.1.support ≠
      typeATwoBruhatTetrahedron e he (fun i ↦ by rw [hρ i]; exact one_ne_zero) a c := by
  intro heq
  have hA : HasCartanType P b (.A 2) := by
    rw [hasCartanType_iff, DynkinType.cartanMatrix_A]
    exact ⟨e, he⟩
  have hlt := length_lt_three_of_hasCartanType_A_two hA hρ π
  have hcard : π.toBruhatRealization.1.support.card = π.length + 1 := by
    rw [← Set.ncard_coe_finset, coe_support_toBruhatRealization,
      Set.ncard_range_of_injective π.dir_injective, Nat.card_fin]
  have h4 := congrArg Finset.card heq
  rw [hcard, card_typeATwoBruhatTetrahedron] at h4
  omega

/-- Concrete specialization to the pinned simply connected root datum of type `A₂` at the
fundamental-weight sum `![1, 1]`: every Lakshmibai–Seshadri path has fewer than `3` internal
breaks, so none meets the open interior of any of the four maximal Bruhat tetrahedra. -/
theorem length_lt_three_typeASimplyConnectedRootDatum_two
    (π : LSPath (DynkinType.typeASimplyConnectedRootDatum 2)
      (DynkinType.typeASimplyConnectedBase 2) ![1, 1]) :
    π.length < 3 := by
  refine length_lt_three_of_hasCartanType_A_two
    (DynkinType.hasCartanType_typeASimplyConnectedRootDatum 2) (fun i ↦ ?_) π
  have hi : (i.1 : ℕ) < 2 := DynkinType.mem_typeASimplyConnectedBase_support.mp i.2
  let k : Fin 2 := ⟨i.1, hi⟩
  have hik : i.1 = DynkinType.typeASimpleIndex 2 k := Fin.ext (by simp [k])
  simp only [RootPairing.coroot', LinearMap.flip_apply,
    DynkinType.toLinearMap_typeASimplyConnectedRootDatum, hik,
    DynkinType.coroot_typeASimpleIndex, dotProduct_single, mul_one]
  have hk01 : k = 0 ∨ k = 1 := by omega
  rcases hk01 with h | h <;> simp [h]

end TypeATwo

end TauCeti.LSPath
