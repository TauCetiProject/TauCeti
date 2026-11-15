/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.LerayHirsch.Basic
public import TauCeti.AlgebraicTopology.Cohomology.MayerVietoris.PullbackCup
public import TauCeti.AlgebraicTopology.Cohomology.Point

/-!
# The Mayer–Vietoris step for the Leray–Hirsch map

For a pair `P = (X, A)`, a map `g : X ⟶ Y` and a family of classes `c p : ι p → Hᵖ(X, A; K)`, the
Leray–Hirsch map `⨁_{p + q = n} ⨁_{i : ι p} H^q(Y; M) ⟶ Hⁿ(X, A; M)`,
`(a_{p,i}) ↦ ∑ g^*a_{p,i} ⌣ c p i`, is `TopPair.lerayHirsch`, defined in
`TauCeti.AlgebraicTopology.Cohomology.LerayHirsch.Basic`. When `g` is the projection of a fibre
bundle, `A` is empty and the classes restrict on every fibre to a basis of its cohomology, the
Leray–Hirsch theorem asserts that it is bijective.

This file proves that bijectivity of the Leray–Hirsch map is local on the base, as in the proof of
the theorem by Mayer–Vietoris over trivializing open sets. For a map `π : X ⟶ Y`, a subset
`Z ⊆ X`, classes `c p : ι p → Hᵖ(X, Z; K)` and a subset `S ⊆ Y`, restricting the classes to the pair
`(π⁻¹ S, π⁻¹ S ∩ Z)` and `π` to `π⁻¹ S ⟶ S` gives the Leray–Hirsch map over `S`
(`TopCat.lerayHirschRestrict`).

* **The Mayer–Vietoris step** (`TopCat.bijective_lerayHirschRestrict_union`): for open sets `U` and
  `V` of `Y`, if the Leray–Hirsch maps over `U`, `V` and `U ∩ V` are bijective in degrees
  `q ≤ n`, then so is the map over `U ∪ V` in degree `n`. Unlike the Thom map, no vanishing
  hypothesis is needed below the degree of the classes: the source in degree `n` contains the
  summands of all the classes of degree at most `n`.
* **Finite unions** (`TopCat.bijective_lerayHirschRestrict_biUnion`): if finitely many open sets
  `W i` are such that the Leray–Hirsch maps over their open subsets are bijective in every degree,
  as for the base sets of trivializations of a fibre bundle, then so is the map over their union.
* **Compact bases** (`TopCat.bijective_lerayHirsch_of_compactSpace`): if every point of a compact
  base has such a neighbourhood, then the Leray–Hirsch map of `(X, Z)` is bijective in every
  degree.

The step is first proved for open covers `{U', V'}` of `X` and `{U, V}` of `Y` with
`π(U') ⊆ U` and `π(V') ⊆ V` and pairs `(U', A)`, `(V', B)` (`TopPair.bijective_lerayHirsch_union`),
by comparing the direct sum of shifted copies of the Mayer–Vietoris sequence of the cover
`{U, V}` of `Y` with the Mayer–Vietoris sequence of the two pairs. The Leray–Hirsch maps commute
with the restrictions by naturality of the cup product, and with the connecting morphisms because
each summand does (`TopPair.singularCohomologyPairMayerVietorisδ_pullbackCup`), the connecting
morphism of the source raising the base degree of each summand by one. The four lemmas are then
checked by a diagram chase, summand by summand on the source. The version for subsets of a fixed
base follows by restricting `π`, as for `TopCat.bijective_pullbackCupRestrict_union`.

## Main definitions and results

* `TopPair.bijective_lerayHirsch_union`: the Mayer–Vietoris step for two pairs.
* `TopCat.lerayHirschRestrict`: the Leray–Hirsch map over a subset of the base.
* `TopCat.bijective_lerayHirsch_of_union_eq_univ`, `TopCat.bijective_lerayHirschRestrict_union`:
  the Mayer–Vietoris step over an open cover of the base and over a union of two open sets.
* `TopCat.bijective_lerayHirschRestrict_biUnion`, `TopCat.bijective_lerayHirsch_of_compactSpace`:
  finite unions and compact bases.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Theorem 4D.1 (Leray–Hirsch).
* R. Bott, L. W. Tu, *Differential Forms in Algebraic Topology*, Graduate Texts in Mathematics 82,
  Springer (1982), §5 (the Leray–Hirsch theorem, proved by Mayer–Vietoris over a finite cover).
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory Set TopCat
open scoped DirectSum

universe w

namespace TopCat

/-! ### Elementwise Mayer–Vietoris exactness -/

section Exactness

variable {K : Type w} [CommRing K] {M : ModuleCat.{w} K} {X : TopCat.{w}}

section Absolute

variable {U V : Set X} (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = univ)

include hU hV hUV in
/-- A class of degree `0` restricting to `0` on `U` and on `V` is `0`. -/
private lemma eq_zero_of_restrict_eq_zero
    (a : X.singularCohomology (ModuleCat.of K K) K M 0)
    (haU : TopCat.singularCohomologyMap (ofHom (ContinuousMap.subtypeVal U)) 0 a = 0)
    (haV : TopCat.singularCohomologyMap (ofHom (ContinuousMap.subtypeVal V)) 0 a = 0) : a = 0 := by
  refine (ModuleCat.mono_iff_injective _).1
    (mono_singularCohomologyMayerVietorisToBiprod_zero (ModuleCat.of K K) K M hU hV hUV) ?_
  rw [map_zero, ← ModuleCat.biprod_inl_fst_add_inr_snd_apply
    (singularCohomologyMayerVietorisToBiprod (ModuleCat.of K K) K M U V 0 a)]
  simp [← ConcreteCategory.comp_apply, haU, haV]

/-- A class restricting to `0` on `U` and on `V` is in the image of the connecting morphism. -/
private lemma exists_singularCohomologyMayerVietorisδ_eq {q : ℕ}
    (a : X.singularCohomology (ModuleCat.of K K) K M (q + 1))
    (haU : TopCat.singularCohomologyMap (ofHom (ContinuousMap.subtypeVal U)) (q + 1) a = 0)
    (haV : TopCat.singularCohomologyMap (ofHom (ContinuousMap.subtypeVal V)) (q + 1) a = 0) :
    ∃ b, singularCohomologyMayerVietorisδ (ModuleCat.of K K) K M hU hV hUV q (q + 1) rfl b = a := by
  refine ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
    (singularCohomologyMayerVietoris_exact₁ (ModuleCat.of K K) K M hU hV hUV q (q + 1) rfl) a).1 ?_
  rw [← ModuleCat.biprod_inl_fst_add_inr_snd_apply
    (singularCohomologyMayerVietorisToBiprod (ModuleCat.of K K) K M U V (q + 1) a)]
  simp [← ConcreteCategory.comp_apply, haU, haV]

/-- The connecting morphism vanishes on restrictions from `U`. -/
private lemma singularCohomologyMayerVietorisδ_restrict_left {q : ℕ}
    (x : (of U).singularCohomology (ModuleCat.of K K) K M q) :
    singularCohomologyMayerVietorisδ (ModuleCat.of K K) K M hU hV hUV q (q + 1) rfl
      (TopCat.singularCohomologyMap (ofHom (ContinuousMap.inclusion inter_subset_left)) q x) =
      0 := by
  have h := ConcreteCategory.congr_hom
    (inl_singularCohomologyMayerVietorisFromBiprod (ModuleCat.of K K) K M U V q) x
  have h₀ := ConcreteCategory.congr_hom (singularCohomologyMayerVietorisFromBiprod_δ
    (ModuleCat.of K K) K M hU hV hUV q (q + 1) rfl)
    ((biprod.inl : _ ⟶ _ ⊞ (of V).singularCohomology (ModuleCat.of K K) K M q) x)
  rw [ConcreteCategory.comp_apply] at h h₀
  rw [h] at h₀
  simpa using h₀

/-- The connecting morphism vanishes on restrictions from `V`. -/
private lemma singularCohomologyMayerVietorisδ_restrict_right {q : ℕ}
    (y : (of V).singularCohomology (ModuleCat.of K K) K M q) :
    singularCohomologyMayerVietorisδ (ModuleCat.of K K) K M hU hV hUV q (q + 1) rfl
      (TopCat.singularCohomologyMap (ofHom (ContinuousMap.inclusion inter_subset_right)) q y) =
      0 := by
  have h := ConcreteCategory.congr_hom
    (inr_singularCohomologyMayerVietorisFromBiprod (ModuleCat.of K K) K M U V q) y
  have h₀ := ConcreteCategory.congr_hom (singularCohomologyMayerVietorisFromBiprod_δ
    (ModuleCat.of K K) K M hU hV hUV q (q + 1) rfl)
    ((biprod.inr : _ ⟶ (of U).singularCohomology (ModuleCat.of K K) K M q ⊞ _) y)
  rw [ConcreteCategory.comp_apply] at h h₀
  rw [h] at h₀
  simpa using h₀

include hU hV hUV in
/-- Classes over `U` and `V` with the same restriction to `U ∩ V` glue to a class over `X`. -/
private lemma exists_restrict_eq {q : ℕ} (x : (of U).singularCohomology (ModuleCat.of K K) K M q)
    (y : (of V).singularCohomology (ModuleCat.of K K) K M q)
    (hxy : TopCat.singularCohomologyMap (ofHom (ContinuousMap.inclusion inter_subset_left)) q x =
      TopCat.singularCohomologyMap (ofHom (ContinuousMap.inclusion inter_subset_right)) q y) :
    ∃ z, TopCat.singularCohomologyMap (ofHom (ContinuousMap.subtypeVal U)) q z = x ∧
      TopCat.singularCohomologyMap (ofHom (ContinuousMap.subtypeVal V)) q z = y := by
  obtain ⟨z, hz⟩ := ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
    (singularCohomologyMayerVietoris_exact₂ (ModuleCat.of K K) K M hU hV hUV q)
      ((biprod.inl : _ ⟶ _ ⊞ (of V).singularCohomology (ModuleCat.of K K) K M q) x +
        (biprod.inr : _ ⟶ (of U).singularCohomology (ModuleCat.of K K) K M q ⊞ _) y)).1
    (by simp [← ConcreteCategory.comp_apply, hxy])
  refine ⟨z, ?_, ?_⟩
  · simpa [← ConcreteCategory.comp_apply] using congrArg (biprod.fst : _ ⊞
      (of V).singularCohomology (ModuleCat.of K K) K M q ⟶ _) hz
  · simpa [← ConcreteCategory.comp_apply] using congrArg (biprod.snd :
      (of U).singularCohomology (ModuleCat.of K K) K M q ⊞ _ ⟶ _) hz

end Absolute

section Pair

attribute [local instance] TopPair.mono_toSSetPair_map_ofInclusionMap_inclusion_left
  TopPair.mono_toSSetPair_map_ofInclusionMap_inclusion_right

variable {A B C D : Set X} (hCA : C ⊆ A) (hDB : D ⊆ B)
  (hA : IsOpen ((↑) ⁻¹' A : Set ↥(A ∪ B))) (hB : IsOpen ((↑) ⁻¹' B : Set ↥(A ∪ B)))
  (hC : IsOpen ((↑) ⁻¹' C : Set ↥(C ∪ D))) (hD : IsOpen ((↑) ⁻¹' D : Set ↥(C ∪ D)))

include hA hB hC hD in
/-- A relative class of degree `0` restricting to `0` on both pairs is `0`. -/
private lemma pair_eq_zero_of_restrict_eq_zero
    (y : (TopPair.ofInclusion (union_subset_union hCA hDB)).singularCohomology
      (ModuleCat.of K K) K M 0)
    (hyA : TopPair.singularCohomologyMap (leftToUnionMap hCA hDB) 0 y = 0)
    (hyB : TopPair.singularCohomologyMap (rightToUnionMap hCA hDB) 0 y = 0) : y = 0 := by
  refine (ModuleCat.mono_iff_injective _).1
    (mono_singularCohomologyPairMayerVietorisToBiprod_zero (ModuleCat.of K K) K M hCA hDB hA hB hC
      hD) ?_
  rw [map_zero, ← ModuleCat.biprod_inl_fst_add_inr_snd_apply
    (singularCohomologyPairMayerVietorisToBiprod (ModuleCat.of K K) K M hCA hDB 0 y)]
  simp [← ConcreteCategory.comp_apply, hyA, hyB]

/-- A relative class restricting to `0` on both pairs is in the image of the connecting
morphism. -/
private lemma exists_singularCohomologyPairMayerVietorisδ_eq {m : ℕ}
    (y : (TopPair.ofInclusion (union_subset_union hCA hDB)).singularCohomology
      (ModuleCat.of K K) K M (m + 1))
    (hyA : TopPair.singularCohomologyMap (leftToUnionMap hCA hDB) (m + 1) y = 0)
    (hyB : TopPair.singularCohomologyMap (rightToUnionMap hCA hDB) (m + 1) y = 0) :
    ∃ t, singularCohomologyPairMayerVietorisδ (ModuleCat.of K K) K M hCA hDB hA hB hC hD m (m + 1)
      rfl t = y := by
  refine ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
    (singularCohomologyPairMayerVietoris_exact₁ (ModuleCat.of K K) K M hCA hDB hA hB hC hD m
      (m + 1) rfl) y).1 ?_
  rw [← ModuleCat.biprod_inl_fst_add_inr_snd_apply
    (singularCohomologyPairMayerVietorisToBiprod (ModuleCat.of K K) K M hCA hDB (m + 1) y)]
  simp [← ConcreteCategory.comp_apply, hyA, hyB]

/-- A relative class over the intersection killed by the connecting morphism is a difference of
restrictions from the two pairs. -/
private lemma exists_sub_eq_of_singularCohomologyPairMayerVietorisδ_eq_zero {m : ℕ}
    (t : (TopPair.ofInclusion (inter_subset_inter hCA hDB)).singularCohomology
      (ModuleCat.of K K) K M m)
    (ht : singularCohomologyPairMayerVietorisδ (ModuleCat.of K K) K M hCA hDB hA hB hC hD m (m + 1)
      rfl t = 0) :
    ∃ x y, TopPair.singularCohomologyMap (interToLeftMap hCA hDB) m x -
      TopPair.singularCohomologyMap (interToRightMap hCA hDB) m y = t := by
  obtain ⟨z, rfl⟩ := ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
    (singularCohomologyPairMayerVietoris_exact₃ (ModuleCat.of K K) K M hCA hDB hA hB hC hD m
      (m + 1) rfl) t).1 ht
  refine ⟨(biprod.fst : _ ⊞ (TopPair.ofInclusion hDB).singularCohomology (ModuleCat.of K K) K M m
    ⟶ _) z, (biprod.snd : (TopPair.ofInclusion hCA).singularCohomology (ModuleCat.of K K) K M m ⊞
      _ ⟶ _) z, ?_⟩
  have h₁ := ConcreteCategory.congr_hom
    (inl_singularCohomologyPairMayerVietorisFromBiprod (ModuleCat.of K K) K M hCA hDB m)
    ((biprod.fst : _ ⊞ (TopPair.ofInclusion hDB).singularCohomology (ModuleCat.of K K) K M m ⟶ _) z)
  have h₂ := ConcreteCategory.congr_hom
    (inr_singularCohomologyPairMayerVietorisFromBiprod (ModuleCat.of K K) K M hCA hDB m)
    ((biprod.snd : (TopPair.ofInclusion hCA).singularCohomology (ModuleCat.of K K) K M m ⊞ _ ⟶ _)
      z)
  rw [ConcreteCategory.comp_apply] at h₁ h₂
  conv_rhs => rw [← ModuleCat.biprod_inl_fst_add_inr_snd_apply z]
  rw [map_add, h₁, h₂]
  simp [sub_eq_add_neg]

/-- Restricting from the union pair to the intersection pair through either pair agrees. -/
private lemma singularCohomologyMap_interToLeftMap_leftToUnionMap {m : ℕ}
    (y : (TopPair.ofInclusion (union_subset_union hCA hDB)).singularCohomology
      (ModuleCat.of K K) K M m) :
    TopPair.singularCohomologyMap (interToLeftMap hCA hDB) m
        (TopPair.singularCohomologyMap (leftToUnionMap hCA hDB) m y) =
      TopPair.singularCohomologyMap (interToRightMap hCA hDB) m
        (TopPair.singularCohomologyMap (rightToUnionMap hCA hDB) m y) := by
  rw [← TopPair.singularCohomologyMap_comp_apply, ← TopPair.singularCohomologyMap_comp_apply,
    interToLeftMap_comp_leftToUnionMap, interToRightMap_comp_rightToUnionMap]

end Pair

end Exactness

end TopCat

namespace TopPair

/-! ### The Mayer–Vietoris step -/

section MayerVietoris

variable {K : Type w} [CommRing K] {M : ModuleCat.{w} K} {ι : ℕ → Type w}
  [∀ p, DecidableEq (ι p)]

attribute [local instance] TopPair.mono_toSSetPair_map_ofInclusionMap_inclusion_left
  TopPair.mono_toSSetPair_map_ofInclusionMap_inclusion_right

section Source

variable {Y : TopCat.{w}} {U V : Set Y} (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = univ)

/-- The Mayer–Vietoris connecting morphism of the cover `{U, V}` of `Y`, applied in each summand of
the source of the Leray–Hirsch map: the summand indexed by `p + q = n` and `i` is sent to the
summand indexed by `p + (q + 1) = n + 1` and `i`. -/
private def sourceδ (n : ℕ) :
    (TopCat.of ↥(U ∩ V)).LerayHirschSource M ι n →ₗ[K] Y.LerayHirschSource M ι (n + 1) :=
  DirectSum.toModule K _ _ fun j ↦
    DirectSum.lof K _ (fun j : Σ pq : {pq : ℕ × ℕ // pq.1 + pq.2 = n + 1}, ι pq.1.1 ↦
        Y.singularCohomology (ModuleCat.of K K) K M j.1.1.2)
        ⟨⟨(j.1.1.1, j.1.1.2 + 1), by rw [← add_assoc, j.1.2]⟩, j.2⟩ ∘ₗ
      (singularCohomologyMayerVietorisδ (ModuleCat.of K K) K M hU hV hUV j.1.1.2 (j.1.1.2 + 1)
        rfl).hom

/-- The connecting morphism of the source on a summand. -/
private lemma sourceδ_lof {n p q : ℕ} (h : p + q = n) (i : ι p)
    (b : (TopCat.of ↥(U ∩ V)).singularCohomology (ModuleCat.of K K) K M q) :
    sourceδ hU hV hUV n (DirectSum.lof K _ (fun j : Σ pq : {pq : ℕ × ℕ // pq.1 + pq.2 = n},
        ι pq.1.1 ↦ (TopCat.of ↥(U ∩ V)).singularCohomology (ModuleCat.of K K) K M j.1.1.2)
        ⟨⟨(p, q), h⟩, i⟩ b) =
      DirectSum.lof K _ (fun j : Σ pq : {pq : ℕ × ℕ // pq.1 + pq.2 = n + 1}, ι pq.1.1 ↦
        Y.singularCohomology (ModuleCat.of K K) K M j.1.1.2)
        ⟨⟨(p, q + 1), by rw [← add_assoc, h]⟩, i⟩
        (singularCohomologyMayerVietorisδ (ModuleCat.of K K) K M hU hV hUV q (q + 1) rfl b) := by
  simp [sourceδ]

/-- The connecting morphism vanishes on restrictions from `U`. -/
private lemma sourceδ_restrict_left {n : ℕ} (x : (TopCat.of U).LerayHirschSource M ι n) :
    sourceδ hU hV hUV n
      (lerayHirschSourceMap (TopCat.ofHom (ContinuousMap.inclusion inter_subset_left)) n x) =
      0 := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | of j x =>
    obtain ⟨⟨⟨p, q⟩, h⟩, i⟩ := j
    rw [← DirectSum.lof_eq_of K, lerayHirschSourceMap_lof, sourceδ_lof,
      singularCohomologyMayerVietorisδ_restrict_left, map_zero]
  | add x y hx hy => simp only [map_add, hx, hy, add_zero]

/-- The connecting morphism vanishes on restrictions from `V`. -/
private lemma sourceδ_restrict_right {n : ℕ} (y : (TopCat.of V).LerayHirschSource M ι n) :
    sourceδ hU hV hUV n
      (lerayHirschSourceMap (TopCat.ofHom (ContinuousMap.inclusion inter_subset_right)) n y) =
      0 := by
  induction y using DirectSum.induction_on with
  | zero => simp
  | of j y =>
    obtain ⟨⟨⟨p, q⟩, h⟩, i⟩ := j
    rw [← DirectSum.lof_eq_of K, lerayHirschSourceMap_lof, sourceδ_lof,
      singularCohomologyMayerVietorisδ_restrict_right, map_zero]
  | add x y hx hy => simp only [map_add, hx, hy, add_zero]

/-- A source element over `Y` whose restrictions to `U` and `V` vanish is in the image of the
connecting morphism. -/
private lemma exists_sourceδ_eq {n : ℕ} (a : Y.LerayHirschSource M ι (n + 1))
    (haU : lerayHirschSourceMap (TopCat.ofHom (ContinuousMap.subtypeVal U)) (n + 1) a = 0)
    (haV : lerayHirschSourceMap (TopCat.ofHom (ContinuousMap.subtypeVal V)) (n + 1) a = 0) :
    ∃ b, sourceδ (M := M) (ι := ι) hU hV hUV n b = a := by
  classical
  suffices a ∈ LinearMap.range (sourceδ (M := M) (ι := ι) hU hV hUV n) from this
  rw [← DirectSum.sum_support_of a]
  refine Submodule.sum_mem _ fun j _ ↦ ?_
  obtain ⟨⟨⟨p, q⟩, h⟩, i⟩ := j
  have hjU := DFunLike.congr_fun haU ⟨⟨(p, q), h⟩, i⟩
  have hjV := DFunLike.congr_fun haV ⟨⟨(p, q), h⟩, i⟩
  rw [lerayHirschSourceMap_apply, DirectSum.zero_apply] at hjU hjV
  cases q with
  | zero =>
    rw [eq_zero_of_restrict_eq_zero hU hV hUV _ hjU hjV, map_zero]
    exact zero_mem _
  | succ q =>
    obtain ⟨b, hb⟩ := exists_singularCohomologyMayerVietorisδ_eq hU hV hUV _ hjU hjV
    refine ⟨DirectSum.lof K _ (fun j : Σ pq : {pq : ℕ × ℕ // pq.1 + pq.2 = n}, ι pq.1.1 ↦
      (TopCat.of ↥(U ∩ V)).singularCohomology (ModuleCat.of K K) K M j.1.1.2)
      ⟨⟨(p, q), by omega⟩, i⟩ b, ?_⟩
    rw [sourceδ_lof, hb, DirectSum.lof_eq_of]

omit [∀ p, DecidableEq (ι p)] in
include hU hV hUV in
/-- A source element of degree `0` over `Y` whose restrictions to `U` and `V` vanish is zero. -/
private lemma source_eq_zero_of_restrict_eq_zero (a : Y.LerayHirschSource M ι 0)
    (haU : lerayHirschSourceMap (TopCat.ofHom (ContinuousMap.subtypeVal U)) 0 a = 0)
    (haV : lerayHirschSourceMap (TopCat.ofHom (ContinuousMap.subtypeVal V)) 0 a = 0) : a = 0 := by
  ext ⟨⟨⟨p, q⟩, h⟩, i⟩
  obtain rfl : q = 0 := by omega
  have hjU := DFunLike.congr_fun haU ⟨⟨(p, 0), h⟩, i⟩
  have hjV := DFunLike.congr_fun haV ⟨⟨(p, 0), h⟩, i⟩
  rw [lerayHirschSourceMap_apply, DirectSum.zero_apply] at hjU hjV
  exact eq_zero_of_restrict_eq_zero hU hV hUV _ hjU hjV

omit [∀ p, DecidableEq (ι p)] in
include hU hV hUV in
/-- Source elements over `U` and `V` with the same restrictions to `U ∩ V` are the restrictions of
one source element over `Y`. -/
private lemma exists_source_restrict_eq {n : ℕ} (x : (TopCat.of U).LerayHirschSource M ι n)
    (y : (TopCat.of V).LerayHirschSource M ι n)
    (hxy : lerayHirschSourceMap (TopCat.ofHom (ContinuousMap.inclusion inter_subset_left)) n x =
      lerayHirschSourceMap (TopCat.ofHom (ContinuousMap.inclusion inter_subset_right)) n y) :
    ∃ z, lerayHirschSourceMap (TopCat.ofHom (ContinuousMap.subtypeVal U)) n z = x ∧
      lerayHirschSourceMap (TopCat.ofHom (ContinuousMap.subtypeVal V)) n z = y := by
  let : ∀ p, DecidableEq (ι p) := fun _ ↦ Classical.decEq _
  classical
  have hz := fun j ↦ exists_restrict_eq hU hV hUV (x j) (y j) (by
    have := DFunLike.congr_fun hxy j
    rwa [lerayHirschSourceMap_apply, lerayHirschSourceMap_apply] at this)
  choose z hzU hzV using hz
  let s := x.support ∪ y.support
  refine ⟨∑ j ∈ s, DirectSum.lof K _ (fun j : Σ pq : {pq : ℕ × ℕ // pq.1 + pq.2 = n}, ι pq.1.1 ↦
    Y.singularCohomology (ModuleCat.of K K) K M j.1.1.2) j (z j), ?_, ?_⟩
  · rw [map_sum]
    simp only [lerayHirschSourceMap_lof, hzU]
    conv_rhs => rw [← DirectSum.sum_support_of x]
    simp only [← DirectSum.lof_eq_of K]
    refine (Finset.sum_subset Finset.subset_union_left fun j _ hj ↦ ?_).symm
    rw [DFinsupp.notMem_support_iff.1 hj, map_zero]
  · rw [map_sum]
    simp only [lerayHirschSourceMap_lof, hzV]
    conv_rhs => rw [← DirectSum.sum_support_of y]
    simp only [← DirectSum.lof_eq_of K]
    refine (Finset.sum_subset Finset.subset_union_right fun j _ hj ↦ ?_).symm
    rw [DFinsupp.notMem_support_iff.1 hj, map_zero]

end Source

section Step

variable {X Y : TopCat.{w}} (π : X ⟶ Y) {U' V' : Set X} {A B : Set X} (hAU : A ⊆ U')
  (hBV : B ⊆ V') {U V : Set Y} (hπU : MapsTo π U' U) (hπV : MapsTo π V' V)
  (c : ∀ p, ι p → (TopPair.ofInclusion (union_subset_union hAU hBV)).singularCohomology
    (ModuleCat.of K K) K (ModuleCat.of K K) p)

/-- The restriction `U' ⟶ U` of `π`. -/
private abbrev restrictLeft : (TopPair.ofInclusion hAU).fst ⟶ TopCat.of U :=
  TopCat.ofHom ⟨hπU.restrict, π.hom.continuous.restrict hπU⟩

/-- The restriction `V' ⟶ V` of `π`. -/
private abbrev restrictRight : (TopPair.ofInclusion hBV).fst ⟶ TopCat.of V :=
  TopCat.ofHom ⟨hπV.restrict, π.hom.continuous.restrict hπV⟩

/-- The restriction `U' ∩ V' ⟶ U ∩ V` of `π`. -/
private abbrev restrictInter :
    (TopPair.ofInclusion (inter_subset_inter hAU hBV)).fst ⟶ TopCat.of ↥(U ∩ V) :=
  TopCat.ofHom ⟨(hπU.inter_inter hπV).restrict, π.hom.continuous.restrict (hπU.inter_inter hπV)⟩

/-- The restriction `U' ∪ V' ⟶ Y` of `π`. -/
private abbrev restrictUnion : (TopPair.ofInclusion (union_subset_union hAU hBV)).fst ⟶ Y :=
  TopCat.ofHom (ContinuousMap.subtypeVal (U' ∪ V')) ≫ π

/-- The Leray–Hirsch map over `Y`. -/
private abbrev ΦY (n : ℕ) :=
  (TopPair.ofInclusion (union_subset_union hAU hBV)).lerayHirsch M (restrictUnion π hAU hBV) c n

/-- The Leray–Hirsch map over `U`. -/
private abbrev ΦU (n : ℕ) :=
  (TopPair.ofInclusion hAU).lerayHirsch M (restrictLeft π hAU hπU)
    (fun p i ↦ TopPair.singularCohomologyMap (leftToUnionMap hAU hBV) p (c p i)) n

/-- The Leray–Hirsch map over `V`. -/
private abbrev ΦV (n : ℕ) :=
  (TopPair.ofInclusion hBV).lerayHirsch M (restrictRight π hBV hπV)
    (fun p i ↦ TopPair.singularCohomologyMap (rightToUnionMap hAU hBV) p (c p i)) n

/-- The Leray–Hirsch map over `U ∩ V`. -/
private abbrev ΦI (n : ℕ) :=
  (TopPair.ofInclusion (inter_subset_inter hAU hBV)).lerayHirsch M
    (restrictInter π hAU hBV hπU hπV)
    (fun p i ↦ TopPair.singularCohomologyMap (interToUnionMap hAU hBV) p (c p i)) n

/-- The Leray–Hirsch maps over `Y` and over `U` commute with the restrictions. -/
private lemma ΦU_restrict (n : ℕ) (a : Y.LerayHirschSource M ι n) :
    ΦU π hAU hBV hπU c n (lerayHirschSourceMap (TopCat.ofHom (ContinuousMap.subtypeVal U)) n a) =
      TopPair.singularCohomologyMap (leftToUnionMap hAU hBV) n (ΦY π hAU hBV c n a) :=
  -- In the side condition both maps `U' ⟶ Y` are the restriction of `π`, so `rfl` closes it.
  lerayHirsch_naturality (leftToUnionMap hAU hBV) (restrictLeft π hAU hπU)
    (restrictUnion π hAU hBV) (TopCat.ofHom (ContinuousMap.subtypeVal U))
    (by rw [ofInclusionMap_fst]; rfl) c n a

/-- The Leray–Hirsch maps over `Y` and over `V` commute with the restrictions. -/
private lemma ΦV_restrict (n : ℕ) (a : Y.LerayHirschSource M ι n) :
    ΦV π hAU hBV hπV c n (lerayHirschSourceMap (TopCat.ofHom (ContinuousMap.subtypeVal V)) n a) =
      TopPair.singularCohomologyMap (rightToUnionMap hAU hBV) n (ΦY π hAU hBV c n a) :=
  -- In the side condition both maps `V' ⟶ Y` are the restriction of `π`, so `rfl` closes it.
  lerayHirsch_naturality (rightToUnionMap hAU hBV) (restrictRight π hBV hπV)
    (restrictUnion π hAU hBV) (TopCat.ofHom (ContinuousMap.subtypeVal V))
    (by rw [ofInclusionMap_fst]; rfl) c n a

/-- The Leray–Hirsch maps over `U` and over `U ∩ V` commute with the restrictions. -/
private lemma ΦI_restrict_left (n : ℕ) (x : (TopCat.of U).LerayHirschSource M ι n) :
    ΦI π hAU hBV hπU hπV c n
        (lerayHirschSourceMap (TopCat.ofHom (ContinuousMap.inclusion inter_subset_left)) n x) =
      TopPair.singularCohomologyMap (interToLeftMap hAU hBV) n (ΦU π hAU hBV hπU c n x) := by
  have hc : (fun p i ↦ TopPair.singularCohomologyMap (interToUnionMap hAU hBV) p (c p i)) =
      fun p i ↦ TopPair.singularCohomologyMap (interToLeftMap hAU hBV) p
        (TopPair.singularCohomologyMap (leftToUnionMap hAU hBV) p (c p i)) := by
    simp only [← TopPair.singularCohomologyMap_comp_apply, interToLeftMap_comp_leftToUnionMap]
  rw [ΦI, hc]
  -- In the side condition both maps `U' ∩ V' ⟶ U` are the restriction of `π`, so `rfl` closes it.
  exact lerayHirsch_naturality (interToLeftMap hAU hBV) (restrictInter π hAU hBV hπU hπV)
    (restrictLeft π hAU hπU) (TopCat.ofHom (ContinuousMap.inclusion inter_subset_left))
    (by rw [ofInclusionMap_fst]; rfl) _ n x

/-- The Leray–Hirsch maps over `V` and over `U ∩ V` commute with the restrictions. -/
private lemma ΦI_restrict_right (n : ℕ) (y : (TopCat.of V).LerayHirschSource M ι n) :
    ΦI π hAU hBV hπU hπV c n
        (lerayHirschSourceMap (TopCat.ofHom (ContinuousMap.inclusion inter_subset_right)) n y) =
      TopPair.singularCohomologyMap (interToRightMap hAU hBV) n (ΦV π hAU hBV hπV c n y) := by
  have hc : (fun p i ↦ TopPair.singularCohomologyMap (interToUnionMap hAU hBV) p (c p i)) =
      fun p i ↦ TopPair.singularCohomologyMap (interToRightMap hAU hBV) p
        (TopPair.singularCohomologyMap (rightToUnionMap hAU hBV) p (c p i)) := by
    simp only [← TopPair.singularCohomologyMap_comp_apply, interToRightMap_comp_rightToUnionMap]
  rw [ΦI, hc]
  -- In the side condition both maps `U' ∩ V' ⟶ V` are the restriction of `π`, so `rfl` closes it.
  exact lerayHirsch_naturality (interToRightMap hAU hBV) (restrictInter π hAU hBV hπU hπV)
    (restrictRight π hBV hπV) (TopCat.ofHom (ContinuousMap.inclusion inter_subset_right))
    (by rw [ofInclusionMap_fst]; rfl) _ n y

variable (hU' : IsOpen U') (hV' : IsOpen V') (hUV' : U' ∪ V' = univ)
  (hA : IsOpen ((↑) ⁻¹' A : Set ↥(A ∪ B))) (hB : IsOpen ((↑) ⁻¹' B : Set ↥(A ∪ B)))
  (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = univ)

include hUV' in
/-- The Leray–Hirsch maps over `U ∩ V` and over `Y` commute with the connecting morphisms. -/
private lemma ΦY_sourceδ (n : ℕ) (b : (TopCat.of ↥(U ∩ V)).LerayHirschSource M ι n) :
    ΦY π hAU hBV c (n + 1) (sourceδ hU hV hUV n b) =
      singularCohomologyPairMayerVietorisδ (ModuleCat.of K K) K M hAU hBV
        (hU'.preimage continuous_subtype_val) (hV'.preimage continuous_subtype_val) hA hB n
        (n + 1) rfl (ΦI π hAU hBV hπU hπV c n b) := by
  induction b using DirectSum.induction_on with
  | zero => simp
  | of j x =>
    obtain ⟨⟨⟨p, q⟩, h⟩, i⟩ := j
    rw [← DirectSum.lof_eq_of K, sourceδ_lof, lerayHirsch_lof, lerayHirsch_lof]
    exact (singularCohomologyPairMayerVietorisδ_pullbackCup π hAU hBV hπU hπV (c p i) hU' hV' hUV'
      hA hB hU hV hUV (q := q) (mq := n) (m := n + 1) (by omega) rfl (by omega) x).symm
  | add x y hx hy => simp only [map_add, hx, hy]

include hU' hV' hUV' hA hB hU hV hUV in
/-- Injectivity in the Mayer–Vietoris step, by the four lemma. -/
private lemma injective_ΦY {n : ℕ} (hΦU : Function.Injective (ΦU π hAU hBV hπU c (M := M) n))
    (hΦV : Function.Injective (ΦV π hAU hBV hπV c (M := M) n))
    (hΦU' : ∀ m, m + 1 = n → Function.Surjective (ΦU π hAU hBV hπU c (M := M) m))
    (hΦV' : ∀ m, m + 1 = n → Function.Surjective (ΦV π hAU hBV hπV c (M := M) m))
    (hΦI' : ∀ m, m + 1 = n → Function.Injective (ΦI π hAU hBV hπU hπV c (M := M) m)) :
    Function.Injective (ΦY π hAU hBV c (M := M) n) := by
  have hU'' := hU'.preimage (continuous_subtype_val (p := (· ∈ U' ∪ V')))
  have hV'' := hV'.preimage (continuous_subtype_val (p := (· ∈ U' ∪ V')))
  refine (injective_iff_map_eq_zero _).2 fun a ha ↦ ?_
  -- The restrictions of `a` to `U` and `V` are sent to the restrictions of `ΦY a = 0`.
  have haU : lerayHirschSourceMap (TopCat.ofHom (ContinuousMap.subtypeVal U)) n a = 0 :=
    hΦU (by rw [ΦU_restrict, ha, map_zero, map_zero])
  have haV : lerayHirschSourceMap (TopCat.ofHom (ContinuousMap.subtypeVal V)) n a = 0 :=
    hΦV (by rw [ΦV_restrict, ha, map_zero, map_zero])
  cases n with
  | zero => exact source_eq_zero_of_restrict_eq_zero hU hV hUV a haU haV
  | succ m =>
    -- So `a = δ b`, and `ΦI b` is in the kernel of the connecting morphism of the pairs, hence
    -- a difference of restrictions `x - y`, which come from classes over `U` and `V`.
    obtain ⟨b, rfl⟩ := exists_sourceδ_eq hU hV hUV a haU haV
    rw [ΦY_sourceδ π hAU hBV hπU hπV c hU' hV' hUV' hA hB hU hV hUV] at ha
    obtain ⟨x, y, hxy⟩ :=
      exists_sub_eq_of_singularCohomologyPairMayerVietorisδ_eq_zero hAU hBV hU'' hV'' hA hB _ ha
    obtain ⟨x, rfl⟩ := hΦU' m rfl x
    obtain ⟨y, rfl⟩ := hΦV' m rfl y
    -- By injectivity over `U ∩ V`, `b` is the difference of the restrictions of `x` and `y`, which
    -- the connecting morphism kills.
    obtain rfl : b = lerayHirschSourceMap (TopCat.ofHom (ContinuousMap.inclusion inter_subset_left))
        m x -
          lerayHirschSourceMap (TopCat.ofHom (ContinuousMap.inclusion inter_subset_right)) m y :=
      hΦI' m rfl (by rw [map_sub, ΦI_restrict_left, ΦI_restrict_right, hxy])
    rw [map_sub, sourceδ_restrict_left, sourceδ_restrict_right, sub_zero]

include hU' hV' hUV' hA hB hU hV hUV in
/-- Surjectivity in the Mayer–Vietoris step, by the four lemma. -/
private lemma surjective_ΦY {n : ℕ} (hΦU : Function.Surjective (ΦU π hAU hBV hπU c (M := M) n))
    (hΦV : Function.Surjective (ΦV π hAU hBV hπV c (M := M) n))
    (hΦI : Function.Injective (ΦI π hAU hBV hπU hπV c (M := M) n))
    (hΦI' : ∀ m, m + 1 = n → Function.Surjective (ΦI π hAU hBV hπU hπV c (M := M) m)) :
    Function.Surjective (ΦY π hAU hBV c (M := M) n) := by
  have hU'' := hU'.preimage (continuous_subtype_val (p := (· ∈ U' ∪ V')))
  have hV'' := hV'.preimage (continuous_subtype_val (p := (· ∈ U' ∪ V')))
  intro y
  -- Lift the restrictions of `y` to `U` and `V`. Their restrictions to `U ∩ V` have the same image
  -- over `U ∩ V`, so they agree, and they glue to a source element `a` over `Y`.
  obtain ⟨sU, hsU⟩ := hΦU (TopPair.singularCohomologyMap (leftToUnionMap hAU hBV) n y)
  obtain ⟨sV, hsV⟩ := hΦV (TopPair.singularCohomologyMap (rightToUnionMap hAU hBV) n y)
  obtain ⟨a, haU, haV⟩ := exists_source_restrict_eq hU hV hUV sU sV (hΦI (by
    rw [ΦI_restrict_left, ΦI_restrict_right, hsU, hsV,
      singularCohomologyMap_interToLeftMap_leftToUnionMap]))
  -- Then `y - ΦY a` restricts to `0` on `U` and on `V`.
  have hyU : TopPair.singularCohomologyMap (leftToUnionMap hAU hBV) n
      (y - ΦY π hAU hBV c n a) = 0 := by
    rw [map_sub, ← ΦU_restrict π hAU hBV hπU c, haU, hsU, sub_self]
  have hyV : TopPair.singularCohomologyMap (rightToUnionMap hAU hBV) n
      (y - ΦY π hAU hBV c n a) = 0 := by
    rw [map_sub, ← ΦV_restrict π hAU hBV hπV c, haV, hsV, sub_self]
  cases n with
  | zero =>
    exact ⟨a, (sub_eq_zero.1
      (pair_eq_zero_of_restrict_eq_zero hAU hBV hU'' hV'' hA hB _ hyU hyV)).symm⟩
  | succ m =>
    -- So `y - ΦY a` is the image of the connecting morphism of some `ΦI b`, which is `ΦY (δ b)`.
    obtain ⟨t, ht⟩ :=
      exists_singularCohomologyPairMayerVietorisδ_eq hAU hBV hU'' hV'' hA hB _ hyU hyV
    obtain ⟨b, rfl⟩ := hΦI' m rfl t
    refine ⟨a + sourceδ hU hV hUV m b, ?_⟩
    rw [map_add, ΦY_sourceδ π hAU hBV hπU hπV c hU' hV' hUV' hA hB hU hV hUV, ht,
      add_sub_cancel]

include hU' hV' hUV' hA hB hU hV hUV in
/-- **The Mayer–Vietoris step for the Leray–Hirsch map.** Let `π : X ⟶ Y` carry the members of an
open cover `{U', V'}` of `X` into those of an open cover `{U, V}` of `Y`, let `A ⊆ U'` and
`B ⊆ V'` be open in `A ∪ B`, and let `c p : ι p → Hᵖ(U' ∪ V', A ∪ B; K)` be a family of classes.
Suppose that the Leray–Hirsch maps over `U`, `V` and `U ∩ V`, with values in the cohomology of
`(U', A)`, `(V', B)` and `(U' ∩ V', A ∩ B)` and the restrictions of `π` and of the classes, are
bijective in degrees `q ≤ n`. Then the Leray–Hirsch map
`⨁_{p + q = n} ⨁_{i : ι p} H^q(Y; M) ⟶ Hⁿ(U' ∪ V', A ∪ B; M)` of the classes `c` is bijective. -/
theorem bijective_lerayHirsch_union {n : ℕ}
    (hΦU : ∀ q ≤ n, Function.Bijective ((TopPair.ofInclusion hAU).lerayHirsch M
      (TopCat.ofHom ⟨hπU.restrict, π.hom.continuous.restrict hπU⟩)
      (fun p i ↦ TopPair.singularCohomologyMap (leftToUnionMap hAU hBV) p (c p i)) q))
    (hΦV : ∀ q ≤ n, Function.Bijective ((TopPair.ofInclusion hBV).lerayHirsch M
      (TopCat.ofHom ⟨hπV.restrict, π.hom.continuous.restrict hπV⟩)
      (fun p i ↦ TopPair.singularCohomologyMap (rightToUnionMap hAU hBV) p (c p i)) q))
    (hΦI : ∀ q ≤ n, Function.Bijective
      ((TopPair.ofInclusion (inter_subset_inter hAU hBV)).lerayHirsch M
        (TopCat.ofHom ⟨(hπU.inter_inter hπV).restrict,
          π.hom.continuous.restrict (hπU.inter_inter hπV)⟩)
        (fun p i ↦ TopPair.singularCohomologyMap (interToUnionMap hAU hBV) p (c p i)) q)) :
    Function.Bijective ((TopPair.ofInclusion (union_subset_union hAU hBV)).lerayHirsch M
      (TopCat.ofHom (ContinuousMap.subtypeVal (U' ∪ V')) ≫ π) c n) :=
  ⟨injective_ΦY π hAU hBV hπU hπV c hU' hV' hUV' hA hB hU hV hUV (hΦU n le_rfl).1
      (hΦV n le_rfl).1 (fun m hm ↦ (hΦU m (by omega)).2) (fun m hm ↦ (hΦV m (by omega)).2)
      (fun m hm ↦ (hΦI m (by omega)).1),
    surjective_ΦY π hAU hBV hπU hπV c hU' hV' hUV' hA hB hU hV hUV (hΦU n le_rfl).2
      (hΦV n le_rfl).2 (hΦI n le_rfl).1 (fun m hm ↦ (hΦI m (by omega)).2)⟩

end Step

end MayerVietoris

end TopPair

namespace TopCat

/-! ### The Leray–Hirsch map over a subset of the base -/

variable {K : Type w} [CommRing K] {X Y : TopCat.{w}} (π : X ⟶ Y) (Z : Set X)
  (M : ModuleCat.{w} K) {ι : ℕ → Type w} [∀ p, DecidableEq (ι p)]

/-- The Leray–Hirsch map over a subset `S` of the base: the Leray–Hirsch map
`TopPair.lerayHirsch` of the restrictions of the classes `c p : ι p → Hᵖ(X, Z; K)` to the pair
`(π⁻¹ S, π⁻¹ S ∩ Z)` and of the restriction `π⁻¹ S ⟶ S` of `π`, from
`⨁_{p + q = n} ⨁_{i : ι p} H^q(S; M)` to `Hⁿ(π⁻¹ S, π⁻¹ S ∩ Z; M)`. -/
def lerayHirschRestrict (S : Set Y)
    (c : ∀ p, ι p → (TopPair.ofSubset Z).singularCohomology (ModuleCat.of K K) K
      (ModuleCat.of K K) p) (n : ℕ) :
    (of S).LerayHirschSource M ι n →ₗ[K]
      (TopPair.ofInclusion (inter_subset_left : π ⁻¹' S ∩ Z ⊆ π ⁻¹' S)).singularCohomology
        (ModuleCat.of K K) K M n :=
  (TopPair.ofInclusion (inter_subset_left : π ⁻¹' S ∩ Z ⊆ π ⁻¹' S)).lerayHirsch M
    (ofHom (π.hom.restrictPreimage S))
    (fun p i ↦ TopPair.singularCohomologyMap (restrictPreimagePairMap π Z S) p (c p i)) n

/-- The Leray–Hirsch map over `S` is that of the restrictions of the classes to the pair over
`S`. -/
theorem lerayHirschRestrict_def (S : Set Y)
    (c : ∀ p, ι p → (TopPair.ofSubset Z).singularCohomology (ModuleCat.of K K) K
      (ModuleCat.of K K) p) (n : ℕ) :
    lerayHirschRestrict π Z M S c n =
      (TopPair.ofInclusion (inter_subset_left : π ⁻¹' S ∩ Z ⊆ π ⁻¹' S)).lerayHirsch M
        (ofHom (π.hom.restrictPreimage S))
        (fun p i ↦ TopPair.singularCohomologyMap (restrictPreimagePairMap π Z S) p (c p i)) n :=
  (rfl)

/-- Over the whole base, the Leray–Hirsch map over `S` is bijective exactly when the Leray–Hirsch
map of the pair `(X, Z)` and `π` is. -/
theorem bijective_lerayHirschRestrict_univ_iff
    (c : ∀ p, ι p → (TopPair.ofSubset Z).singularCohomology (ModuleCat.of K K) K
      (ModuleCat.of K K) p) (n : ℕ) :
    Function.Bijective (lerayHirschRestrict π Z M univ c n) ↔
      Function.Bijective ((TopPair.ofSubset Z).lerayHirsch M π c n) := by
  have := isIso_restrictPreimagePairMap π Z (S := univ) fun _ ↦ mem_univ _
  rw [lerayHirschRestrict_def]
  exact TopPair.bijective_lerayHirsch_iff_of_isIso (restrictPreimagePairMap π Z univ)
    (isoOfHomeo (Homeomorph.Set.univ Y)).hom
    (TopCat.ext fun x ↦ congrArg π (restrictPreimagePairMap_fst_apply π Z univ x)) c n

/-! ### The Mayer–Vietoris step over a cover and over a union -/

section Cover

variable {M} {U V : Set Y}

/-- Restricting a class of `(X, Z)` to the union of the pairs over `U` and `V` and then along a
map of pairs `φ` is restricting it to the pair over `S` and then along `ψ`, when `φ` and `ψ` agree
on the points of `X`: a map of pairs into `(X, Z)` is determined by its map of ambient spaces. -/
private lemma singularCohomologyMap_restrictPreimagePairUnionIso {P : TopPair.{w}} {S : Set Y}
    (φ : P ⟶ TopPair.ofInclusion (union_subset_union
      (inter_subset_left : π ⁻¹' U ∩ Z ⊆ π ⁻¹' U) (inter_subset_left : π ⁻¹' V ∩ Z ⊆ π ⁻¹' V)))
    (ψ : P ⟶ TopPair.ofInclusion (inter_subset_left : π ⁻¹' S ∩ Z ⊆ π ⁻¹' S))
    (hφψ : ∀ x, (TopPair.Hom.fst φ x).1 = (TopPair.Hom.fst ψ x).1) (p : ℕ)
    (u : (TopPair.ofSubset Z).singularCohomology (ModuleCat.of K K) K M p) :
    TopPair.singularCohomologyMap φ p (TopPair.singularCohomologyMap
        ((restrictPreimagePairUnionIso π Z U V).hom ≫ restrictPreimagePairMap π Z (U ∪ V)) p u) =
      TopPair.singularCohomologyMap ψ p
        (TopPair.singularCohomologyMap (restrictPreimagePairMap π Z S) p u) := by
  rw [← TopPair.singularCohomologyMap_comp_apply, ← TopPair.singularCohomologyMap_comp_apply]
  exact congrArg (fun f ↦ TopPair.singularCohomologyMap f p u) (TopPair.hom_ext_of_fst _
    (TopCat.ext fun x ↦ ((restrictPreimagePairMap_fst_apply π Z (U ∪ V) _).trans
      (restrictPreimagePairUnionIso_hom_fst_apply π Z U V _)).trans
      ((hφψ x).trans (restrictPreimagePairMap_fst_apply π Z S _).symm)))

/-- **The Mayer–Vietoris step for the Leray–Hirsch map of the pair `(X, Z)` and an open cover of
the base.** Let `π : X ⟶ Y` be a map, `Z ⊆ X`, `c p : ι p → Hᵖ(X, Z; K)` a family of classes, and
let `U` and `V` be open sets covering `Y`. If the Leray–Hirsch maps over `U`, `V` and `U ∩ V` are
bijective in degrees `q ≤ n`, then the Leray–Hirsch map
`⨁_{p + q = n} ⨁_{i : ι p} H^q(Y; M) ⟶ Hⁿ(X, Z; M)` of `c` and `π` is bijective. -/
theorem bijective_lerayHirsch_of_union_eq_univ (hU : IsOpen U) (hV : IsOpen V)
    (hUV : U ∪ V = univ)
    (c : ∀ p, ι p → (TopPair.ofSubset Z).singularCohomology (ModuleCat.of K K) K
      (ModuleCat.of K K) p) {n : ℕ}
    (hU' : ∀ q ≤ n, Function.Bijective (lerayHirschRestrict π Z M U c q))
    (hV' : ∀ q ≤ n, Function.Bijective (lerayHirschRestrict π Z M V c q))
    (hUV' : ∀ q ≤ n, Function.Bijective (lerayHirschRestrict π Z M (U ∩ V) c q)) :
    Function.Bijective ((TopPair.ofSubset Z).lerayHirsch M π c n) := by
  have hUV'' : π ⁻¹' U ∪ π ⁻¹' V = univ := by rw [← preimage_union, hUV, preimage_univ]
  have := isIso_restrictPreimagePairMap π Z (S := U ∪ V) fun _ ↦ hUV ▸ mem_univ _
  have hZ : π ⁻¹' U ∩ Z ∪ π ⁻¹' V ∩ Z ⊆ Z := union_subset inter_subset_right inter_subset_right
  have hZ' {W : Set Y} (hW : IsOpen W) :
      IsOpen (((↑) : ↥(π ⁻¹' U ∩ Z ∪ π ⁻¹' V ∩ Z) → X) ⁻¹' (π ⁻¹' W ∩ Z)) := by
    rw [preimage_inter, preimage_val_eq_univ_of_subset hZ, inter_univ]
    exact (hW.preimage π.hom.continuous).preimage continuous_subtype_val
  -- The pair `(X, Z)` is the union of the pairs over `U` and over `V`.
  refine (TopPair.bijective_lerayHirsch_iff_of_isIso
    ((restrictPreimagePairUnionIso π Z U V).hom ≫ restrictPreimagePairMap π Z (U ∪ V)) (𝟙 Y)
    (g := ofHom (ContinuousMap.subtypeVal _) ≫ π) (by
      rw [TopPair.Hom.fst_comp, restrictPreimagePairUnionIso_hom_fst, restrictPreimagePairMap_fst]
      exact TopCat.ext fun _ ↦ rfl) c n).1 ?_
  refine TopPair.bijective_lerayHirsch_union π (inter_subset_left : π ⁻¹' U ∩ Z ⊆ π ⁻¹' U)
    (inter_subset_left : π ⁻¹' V ∩ Z ⊆ π ⁻¹' V) (mapsTo_preimage π U) (mapsTo_preimage π V) _
    (hU.preimage π.hom.continuous) (hV.preimage π.hom.continuous) hUV''
    (hZ' hU) (hZ' hV) hU hV hUV ?_ ?_ ?_
  · intro q hq
    simp only [singularCohomologyMap_restrictPreimagePairUnionIso π Z (leftToUnionMap _ _) (𝟙 _)
      fun x ↦ congrArg Subtype.val (TopPair.ofInclusionMap_fst_apply _ _ x),
      TopPair.singularCohomologyMap_id, ModuleCat.id_apply]
    exact hU' q hq
  · intro q hq
    simp only [singularCohomologyMap_restrictPreimagePairUnionIso π Z (rightToUnionMap _ _) (𝟙 _)
      fun x ↦ congrArg Subtype.val (TopPair.ofInclusionMap_fst_apply _ _ x),
      TopPair.singularCohomologyMap_id, ModuleCat.id_apply]
    exact hV' q hq
  · intro q hq
    simp only [singularCohomologyMap_restrictPreimagePairUnionIso π Z (interToUnionMap _ _)
      (restrictPreimagePairInterIso π Z U V).hom
      fun x ↦ (congrArg Subtype.val (TopPair.ofInclusionMap_fst_apply _ _ x)).trans
        (restrictPreimagePairInterIso_hom_fst_apply π Z U V x).symm]
    exact (TopPair.bijective_lerayHirsch_iff_of_isIso (restrictPreimagePairInterIso π Z U V).hom
      (𝟙 (of ↥(U ∩ V))) (g' := ofHom (π.hom.restrictPreimage (U ∩ V)))
      (by
        rw [restrictPreimagePairInterIso_hom_fst]
        exact TopCat.ext fun _ ↦ rfl) _ q).2 (hUV' q hq)

end Cover

section Union

variable {M} {W S : Set Y}

variable (W) in
/-- The restrictions of the classes `c` to the pair formed by `π⁻¹ W` and its points lying in
`Z`. -/
private abbrev restrictClasses
    (c : ∀ p, ι p → (TopPair.ofSubset Z).singularCohomology (ModuleCat.of K K) K
      (ModuleCat.of K K) p) (p : ℕ) (i : ι p) :
    (TopPair.ofSubset (X := of ↥(π ⁻¹' W))
      (((↑) : ↥(π ⁻¹' W) → X) ⁻¹' (π ⁻¹' W ∩ Z))).singularCohomology
        (ModuleCat.of K K) K (ModuleCat.of K K) p :=
  TopPair.singularCohomologyMap (TopPair.ofSubsetPreimageValIso
      (inter_subset_left : π ⁻¹' W ∩ Z ⊆ π ⁻¹' W)).hom p
    (TopPair.singularCohomologyMap (restrictPreimagePairMap π Z W) p (c p i))

/-- For `S ⊆ W`, the Leray–Hirsch map over `S` agrees with the map over the preimage of `S` in `W`
of the restriction of `π` over `W`, up to homeomorphisms; so the two are bijective together. -/
private theorem bijective_lerayHirschRestrict_restrict_iff (hSW : S ⊆ W)
    (c : ∀ p, ι p → (TopPair.ofSubset Z).singularCohomology (ModuleCat.of K K) K
      (ModuleCat.of K K) p) (n : ℕ) :
    Function.Bijective (lerayHirschRestrict (ofHom (π.hom.restrictPreimage W))
      (((↑) : ↥(π ⁻¹' W) → X) ⁻¹' (π ⁻¹' W ∩ Z)) M ((↑) ⁻¹' S) (restrictClasses π Z W c) n) ↔
      Function.Bijective (lerayHirschRestrict π Z M S c n) := by
  have hc : (fun p i ↦ TopPair.singularCohomologyMap (restrictPreimagePairMap
      (ofHom (π.hom.restrictPreimage W)) (((↑) : ↥(π ⁻¹' W) → X) ⁻¹' (π ⁻¹' W ∩ Z))
      ((↑) ⁻¹' S)) p
        (restrictClasses π Z W c p i)) =
      fun p i ↦ TopPair.singularCohomologyMap (restrictPreimagePairRestrictPreimageIso π Z hSW).hom
        p (TopPair.singularCohomologyMap (restrictPreimagePairMap π Z S) p (c p i)) := by
    funext p i
    rw [← TopPair.singularCohomologyMap_comp_apply, ← TopPair.singularCohomologyMap_comp_apply,
      ← TopPair.singularCohomologyMap_comp_apply]
    exact congrArg (fun f ↦ TopPair.singularCohomologyMap f p (c p i))
      (TopPair.hom_ext_of_fst _ (by
        simp only [TopPair.Hom.fst_comp, TopPair.ofSubsetPreimageValIso_hom_fst,
          restrictPreimagePairRestrictPreimageIso_hom_fst, restrictPreimagePairMap_fst]
        exact TopCat.ext fun _ ↦ rfl))
  rw [lerayHirschRestrict_def, lerayHirschRestrict_def π Z M S, hc]
  have hS : S ⊆ range ((↑) : W → Y) := by rwa [Subtype.range_coe]
  let g := isoOfHomeo (X := of ↥((↑) ⁻¹' S : Set ↥W)) (Y := of ↥S)
    (Topology.IsEmbedding.subtypeVal.homeomorphOfSubsetRange hS)
  exact TopPair.bijective_lerayHirsch_iff_of_isIso
    (restrictPreimagePairRestrictPreimageIso π Z hSW).hom g.hom
    (by
      rw [restrictPreimagePairRestrictPreimageIso_hom_fst]
      exact TopCat.ext fun _ ↦ Subtype.ext rfl) _ n

/-- **The Mayer–Vietoris step for the Leray–Hirsch map over a union.** Let `π : X ⟶ Y` be a map,
`Z ⊆ X`, `c p : ι p → Hᵖ(X, Z; K)` a family of classes, and let `U` and `V` be open sets of `Y`.
If the Leray–Hirsch maps of `c` over `U`, `V` and `U ∩ V` are bijective in degrees `q ≤ n`, then
the Leray–Hirsch map of `c` over `U ∪ V` is bijective in degree `n`. -/
theorem bijective_lerayHirschRestrict_union {U V : Set Y} (hU : IsOpen U) (hV : IsOpen V)
    (c : ∀ p, ι p → (TopPair.ofSubset Z).singularCohomology (ModuleCat.of K K) K
      (ModuleCat.of K K) p) {n : ℕ}
    (hU' : ∀ q ≤ n, Function.Bijective (lerayHirschRestrict π Z M U c q))
    (hV' : ∀ q ≤ n, Function.Bijective (lerayHirschRestrict π Z M V c q))
    (hUV' : ∀ q ≤ n, Function.Bijective (lerayHirschRestrict π Z M (U ∩ V) c q)) :
    Function.Bijective (lerayHirschRestrict π Z M (U ∪ V) c n) := by
  have hUVW : U ∩ V ⊆ U ∪ V := inter_subset_left.trans subset_union_left
  -- The cover case, for the restriction of `π` over `U ∪ V` and the cover of `U ∪ V` by the
  -- preimages of `U` and `V`, whose hypotheses are those over `U`, `V` and `U ∩ V`.
  have key := bijective_lerayHirsch_of_union_eq_univ (X := of ↥(π ⁻¹' (U ∪ V)))
    (ofHom (π.hom.restrictPreimage (U ∪ V)))
    (((↑) : ↥(π ⁻¹' (U ∪ V)) → X) ⁻¹' (π ⁻¹' (U ∪ V) ∩ Z)) (M := M)
    (U := ((↑) : ↥(U ∪ V) → Y) ⁻¹' U) (V := ((↑) : ↥(U ∪ V) → Y) ⁻¹' V)
    (hU.preimage continuous_subtype_val) (hV.preimage continuous_subtype_val)
    (eq_univ_of_forall fun x ↦ x.2) (restrictClasses π Z (U ∪ V) c) (n := n)
    (fun q hq ↦ (bijective_lerayHirschRestrict_restrict_iff π Z subset_union_left c q).2
      (hU' q hq))
    (fun q hq ↦ (bijective_lerayHirschRestrict_restrict_iff π Z subset_union_right c q).2
      (hV' q hq))
    (fun q hq ↦ (bijective_lerayHirschRestrict_restrict_iff π Z hUVW c q).2 (hUV' q hq))
  rw [lerayHirschRestrict_def]
  exact (TopPair.bijective_lerayHirsch_iff_of_isIso (TopPair.ofSubsetPreimageValIso
    (inter_subset_left : π ⁻¹' (U ∪ V) ∩ Z ⊆ π ⁻¹' (U ∪ V))).hom (𝟙 _)
    (g := ofHom (π.hom.restrictPreimage (U ∪ V)))
    (by rw [TopPair.ofSubsetPreimageValIso_hom_fst]; exact TopCat.ext fun _ ↦ rfl) _ n).1 key

end Union

/-! ### Finite unions and compact bases -/

section FiniteUnion

variable {M}

/-- Over the empty subset of the base, the Leray–Hirsch map is bijective in every degree: its
source and target vanish. -/
theorem bijective_lerayHirschRestrict_empty
    (c : ∀ p, ι p → (TopPair.ofSubset Z).singularCohomology (ModuleCat.of K K) K
      (ModuleCat.of K K) p) (n : ℕ) :
    Function.Bijective (lerayHirschRestrict π Z M ∅ c n) := by
  have : Subsingleton ((of ↥(∅ : Set Y)).LerayHirschSource M ι n) :=
    ⟨fun a b ↦ DFinsupp.ext fun j ↦ (ModuleCat.isZero_iff_subsingleton.1
      (TauCeti.isZero_singularCohomology_of_isEmpty (ModuleCat.of K K) K M
        (of ↥(∅ : Set Y)) j.1.1.2)).elim _ _⟩
  have : IsEmpty (of ↥(π ⁻¹' (∅ : Set Y))) := ⟨fun x ↦ x.2⟩
  have hP : IsEmpty (TopPair.ofInclusion
      (inter_subset_left : π ⁻¹' (∅ : Set Y) ∩ Z ⊆ π ⁻¹' ∅)).snd :=
    ⟨fun x ↦ x.2.1⟩
  have : Subsingleton ((TopPair.ofInclusion (inter_subset_left : π ⁻¹' (∅ : Set Y) ∩ Z ⊆
      π ⁻¹' ∅)).singularCohomology (ModuleCat.of K K) K M n) := by
    refine ModuleCat.isZero_iff_subsingleton.1 ((TauCeti.isZero_singularCohomology_of_isEmpty
      (ModuleCat.of K K) K M (of ↥(π ⁻¹' (∅ : Set Y))) n).of_iso ?_)
    exact @asIso _ _ _ _ ((TopPair.ofInclusion (inter_subset_left : π ⁻¹' (∅ : Set Y) ∩ Z ⊆
      π ⁻¹' ∅)).singularCohomologyπ (ModuleCat.of K K) K M n)
      (TopPair.isIso_singularCohomologyπ_of_isEmpty _ (ModuleCat.of K K) K M n)
  exact ⟨fun _ _ _ ↦ Subsingleton.elim _ _, fun y ↦ ⟨0, Subsingleton.elim _ _⟩⟩

/-- **The Leray–Hirsch map over a finite union of open sets.** Let `π : X ⟶ Y` be a map, `Z ⊆ X`
and `c p : ι p → Hᵖ(X, Z; K)` a family of classes. If each of the finitely many open sets `W i`,
`i ∈ s`, of `Y` is such that the Leray–Hirsch maps of `c` over its open subsets are bijective in
every degree, as over the base set of a trivialization of a fibre bundle, then the Leray–Hirsch
map of `c` over their union is bijective in every degree. -/
theorem bijective_lerayHirschRestrict_biUnion {κ : Type*} (s : Finset κ) {W : κ → Set Y}
    (hWo : ∀ i ∈ s, IsOpen (W i))
    (c : ∀ p, ι p → (TopPair.ofSubset Z).singularCohomology (ModuleCat.of K K) K
      (ModuleCat.of K K) p)
    (hW : ∀ i ∈ s, ∀ O ⊆ W i, IsOpen O → ∀ n,
      Function.Bijective (lerayHirschRestrict π Z M O c n)) (n : ℕ) :
    Function.Bijective (lerayHirschRestrict π Z M (⋃ i ∈ s, W i) c n) := by
  classical
  induction s using Finset.induction_on generalizing W n with
  | empty =>
    rw [show (⋃ i ∈ (∅ : Finset κ), W i) = ∅ by simp]
    exact bijective_lerayHirschRestrict_empty π Z c n
  | insert a s _ ih =>
    rw [Finset.set_biUnion_insert]
    have ha := Finset.mem_insert_self a s
    have hs (i : κ) (hi : i ∈ s) : i ∈ insert a s := Finset.mem_insert_of_mem hi
    refine bijective_lerayHirschRestrict_union π Z (hWo a ha)
      (isOpen_biUnion fun i hi ↦ hWo i (hs i hi)) c
      (fun q _ ↦ hW a ha _ subset_rfl (hWo a ha) q)
      (fun q _ ↦ ih (fun i hi ↦ hWo i (hs i hi)) (fun i hi ↦ hW i (hs i hi)) q) fun q _ ↦ ?_
    -- `W a ∩ ⋃ i ∈ s, W i` is the union of the open sets `W a ∩ W i`, `i ∈ s`, whose open subsets
    -- are open subsets of the `W i`.
    rw [inter_iUnion₂]
    exact ih (fun i hi ↦ (hWo a ha).inter (hWo i (hs i hi)))
      (fun i hi O hO ↦ hW i (hs i hi) O (hO.trans inter_subset_right)) q

/-- **The Leray–Hirsch map over a compact base.** Let `π : X ⟶ Y` be a map to a compact space,
`Z ⊆ X` and `c p : ι p → Hᵖ(X, Z; K)` a family of classes. If every point of `Y` has an open
neighbourhood `W` such that the Leray–Hirsch maps of `c` over the open subsets of `W` are
bijective in every degree, as for a trivializing neighbourhood of a fibre bundle, then the
Leray–Hirsch map `⨁_{p + q = n} ⨁_{i : ι p} H^q(Y; M) ⟶ Hⁿ(X, Z; M)` of `c` and `π` is bijective
in every degree. -/
theorem bijective_lerayHirsch_of_compactSpace [CompactSpace Y]
    (c : ∀ p, ι p → (TopPair.ofSubset Z).singularCohomology (ModuleCat.of K K) K
      (ModuleCat.of K K) p)
    (h : ∀ y : Y, ∃ W : Set Y, IsOpen W ∧ y ∈ W ∧ ∀ O ⊆ W, IsOpen O → ∀ n,
      Function.Bijective (lerayHirschRestrict π Z M O c n)) (n : ℕ) :
    Function.Bijective ((TopPair.ofSubset Z).lerayHirsch M π c n) := by
  choose W hWo hyW hW using h
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover W hWo fun y _ ↦ mem_iUnion.2 ⟨y, hyW y⟩
  have key := bijective_lerayHirschRestrict_biUnion π Z t (fun y _ ↦ hWo y) c
    (fun y _ ↦ hW y) n
  rw [univ_subset_iff.1 ht] at key
  exact (bijective_lerayHirschRestrict_univ_iff π Z M c n).1 key

end FiniteUnion

end TopCat
