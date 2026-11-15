/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Excision
public import TauCeti.AlgebraicTopology.Singular.Homotopy.Invariance
public import TauCeti.AlgebraicTopology.Singular.Relative
public import TauCeti.Geometry.Manifold.Boundary.Collar.Retraction

/-!
# Relative homology modulo a collar

Let `A` be a subset of a space `X` with a collar `c : A × [0, 1) → X` (`TauCeti.IsCollar`), for
instance the boundary of a compact manifold (`TauCeti.isCollared_subtypeVal_boundary`). The image
`U = c (A × [0, 1))` of the collar is an open neighbourhood of `A` which deformation retracts onto
it (`TauCeti.IsCollar.homotopyEquivRange`). So the inclusion of pairs `(X, A) → (X, U)`, the
identity of `X`, induces isomorphisms on relative singular homology in every degree
(`TauCeti.IsCollar.isIso_singularHomologyMap`): it is an isomorphism on the homology of `X` and of
the subspaces, and the five lemma applies.

For a compact manifold `M` with boundary and an open collar `U` of `∂M`, the boundary lies in the
interior of `U`, so excising it identifies `H_*(M, U)` with the homology of the interior of `M`
relative to the complement of the compact set `M ∖ U`. Combined with the comparison here, this
reads `H_*(M, ∂M)` in the interior of `M`, which has no boundary; this is how a class relative to
the boundary, such as the fundamental class of `M`, is built from the local homology of the
interior.

## Main results

* `TauCeti.IsCollar.isIso_singularHomologyMap`: for a collar `c` of `A ⊆ X`, the map
  `H_n(X, A) → H_n(X, c (A × [0, 1)))` is an isomorphism.
* `TauCeti.IsCollar.isZero_singularHomology_compl_image_prod`: removing a compact column of a
  collar does not change homology.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 3.3 (the fundamental
  class of a compact manifold with boundary, through a collar of the boundary).
-/

public section

open CategoryTheory Set

universe w v u

namespace TauCeti.IsCollar

variable {X : TopCat.{w}} {A : Set X} {c : A × Ico (0 : ℝ) 1 → X}
  {C : Type u} [Category.{v} C] [Limits.HasCoproducts.{w} C] [Abelian C]

/-- **Relative homology modulo a collar.** If `c` is a collar of `A ⊆ X`, the inclusion of pairs
`(X, A) → (X, c (A × [0, 1)))` induces an isomorphism `H_n(X, A) ≅ H_n(X, c (A × [0, 1)))` on
relative singular homology, in every degree and for every coefficient object. -/
theorem isIso_singularHomologyMap (h : IsCollar ((↑) : A → X) c) (R : C) (n : ℕ) :
    IsIso (TopPair.singularHomologyMap
      (TopPair.ofSubsetMap (𝟙 X) fun x hx ↦ h.range_subset_range ⟨⟨x, hx⟩, rfl⟩) R n) := by
  -- On the ambient space the map of pairs is the identity, and on the subspaces it is the zero
  -- slice of the collar, a homotopy equivalence.
  refine TopPair.isIso_singularHomologyMap_of_homotopyEquiv _ (.refl X) h.homotopyEquivRange
    (TopPair.ofSubsetMap_fst _ _) ?_ R n
  ext x
  exact Subtype.ext ((TopPair.ofSubsetMap_snd_apply _ _ x).trans
    (h.coe_homotopyEquivRange_apply x).symm)

section Column

variable {X : Type w} {N : Type*} [TopologicalSpace X] [TopologicalSpace N] {f : N → X}
  {c : N × Ico (0 : ℝ) 1 → X}

/-- Pushing the collar coordinate `u` up to `u + τ (1 - u) θ` at time `τ ∈ [0, 1]`, for
`0 ≤ θ < 1`: at time `1` every point has moved a fraction `θ` of the way to `1`. -/
private def collarPush (θ : ℝ) (hθ₀ : 0 ≤ θ) (hθ₁ : θ < 1) :
    C(unitInterval × (N × Ico (0 : ℝ) 1), N × Ico (0 : ℝ) 1) where
  toFun r := (r.2.1, ⟨r.2.2 + r.1 * ((1 - r.2.2) * θ),
    add_nonneg r.2.2.2.1 (mul_nonneg r.1.2.1 (mul_nonneg (by linarith [r.2.2.2.2]) hθ₀)), by
      nlinarith [r.2.2.2.1, r.2.2.2.2, r.1.2.1, r.1.2.2,
        mul_le_mul_of_nonneg_right r.1.2.2 (mul_nonneg (by linarith [r.2.2.2.2] :
          (0 : ℝ) ≤ 1 - r.2.2) hθ₀)]⟩)

private lemma collarPush_fst (θ : ℝ) (hθ₀ : 0 ≤ θ) (hθ₁ : θ < 1)
    (r : unitInterval × (N × Ico (0 : ℝ) 1)) : (collarPush θ hθ₀ hθ₁ r).1 = r.2.1 :=
  rfl

private lemma coe_collarPush_snd (θ : ℝ) (hθ₀ : 0 ≤ θ) (hθ₁ : θ < 1)
    (r : unitInterval × (N × Ico (0 : ℝ) 1)) :
    ((collarPush θ hθ₀ hθ₁ r).2 : ℝ) = r.2.2 + r.1 * ((1 - r.2.2) * θ) :=
  rfl

/-- The push never moves a point into a column `K × [0, s]`. -/
private lemma collarPush_notMem {θ : ℝ} (hθ₀ : 0 ≤ θ) (hθ₁ : θ < 1) {K : Set N} {s : ℝ}
    (τ : unitInterval) {q : N × Ico (0 : ℝ) 1} (hq : q ∉ K ×ˢ (Subtype.val ⁻¹' Icc 0 s)) :
    collarPush θ hθ₀ hθ₁ (τ, q) ∉ K ×ˢ (Subtype.val ⁻¹' Icc 0 s) := by
  simp only [mem_prod, mem_preimage, mem_Icc, not_and, not_le, collarPush_fst,
    coe_collarPush_snd] at hq ⊢
  intro hqK _
  nlinarith [hq hqK q.2.2.1, mul_nonneg τ.2.1
    (mul_nonneg (by linarith [q.2.2.2] : (0 : ℝ) ≤ 1 - q.2) hθ₀)]

/-- At time `1` the push moves every point off a column `K × [0, s]` with `s < θ`. -/
private lemma collarPush_one_notMem {θ : ℝ} (hθ₀ : 0 ≤ θ) (hθ₁ : θ < 1) {K : Set N} {s : ℝ}
    (hθs : s < θ) (q : N × Ico (0 : ℝ) 1) :
    collarPush θ hθ₀ hθ₁ (1, q) ∉ K ×ˢ (Subtype.val ⁻¹' Icc 0 s) := by
  simp only [mem_prod, mem_preimage, mem_Icc, not_and, not_le, collarPush_fst,
    coe_collarPush_snd, Set.Icc.coe_one, one_mul]
  intro _ _
  nlinarith [q.2.2.1, q.2.2.2]

/-- **A compact column of a collar is homologically invisible.** For a collar `c` of `f : N → X`,
a compact set `K ⊆ N` and `s < 1`, removing the column `c(K × [0, s])` from a Hausdorff space `X`
does not change singular homology: `Hₖ(X, X ∖ c(K × [0, s])) = 0` in every degree and for every
coefficient object. -/
theorem isZero_singularHomology_compl_image_prod (hc : IsCollar f c) [T2Space X] {K : Set N}
    (hK : IsCompact K) {s : ℝ} (hs : s < 1) (R : C) (k : ℕ) :
    Limits.IsZero ((TopPair.ofSubset ((c '' (K ×ˢ (Subtype.val ⁻¹' Icc 0 s)))ᶜ :
      Set (TopCat.of X))).singularHomology R k) := by
  set S : Set (N × Ico (0 : ℝ) 1) := K ×ˢ (Subtype.val ⁻¹' Icc 0 s)
  have hS : IsCompact S := hK.prod (Topology.IsInducing.subtypeVal.isCompact_preimage'
    isCompact_Icc (by rw [Subtype.range_coe]; exact Icc_subset_Ico_right hs))
  -- Excise the complement of the collar.
  have := TopPair.isIso_singularHomologyMap_excisionMap_of_isClosed_subset R (X := TopCat.of X)
    hc.isOpenEmbedding.isOpen_range (hS.image hc.isOpenEmbedding.continuous).isClosed
    (image_subset_range c S) k
  refine Limits.IsZero.of_iso ?_ (asIso (TopPair.singularHomologyMap
    (TopPair.excisionMap (X := TopCat.of X) (range c) (c '' S)ᶜ) R k)).symm
  -- In the collar, push the collar coordinate a fraction `θ > s` of the way to `1`.
  obtain ⟨θ, hθ₀, hθ₁, hθs⟩ : ∃ θ : ℝ, 0 ≤ θ ∧ θ < 1 ∧ s < θ :=
    ⟨(1 + max s 0) / 2, by positivity, by linarith [max_lt hs one_pos],
      by linarith [le_max_left s 0]⟩
  set e := hc.isOpenEmbedding.isEmbedding.toHomeomorph
  let ρ : TopCat.of (range c) ⟶ TopCat.of (range c) :=
    TopCat.ofHom ⟨fun w ↦ e (collarPush θ hθ₀ hθ₁ (1, e.symm w)), by fun_prop⟩
  let H : (TopCat.Hom.hom (𝟙 (TopCat.of (range c)))).Homotopy ρ.hom :=
    { toFun r := e (collarPush θ hθ₀ hθ₁ (r.1, e.symm r.2))
      continuous_toFun := by fun_prop
      map_zero_left w := by
        refine (congrArg e (Prod.ext (collarPush_fst _ _ _ _) (Subtype.ext ?_))).trans
          (e.apply_symm_apply w)
        simp [coe_collarPush_snd]
      map_one_left _ := rfl }
  have hH (r : unitInterval × range c) : H r = e (collarPush θ hθ₀ hθ₁ (r.1, e.symm r.2)) := rfl
  have hρ (w : range c) : ρ w = e (collarPush θ hθ₀ hθ₁ (1, e.symm w)) := rfl
  -- A point of the collar lies in the column exactly when its collar coordinates do. The push
  -- never moves a point into the column, and at time `1` moves every point off it.
  have hmem (q : N × Ico (0 : ℝ) 1) : ((e q : range c) : X) ∈ c '' S ↔ q ∈ S :=
    hc.isOpenEmbedding.injective.mem_set_image
  have hB (τ : unitInterval) (w : TopCat.of (range c)) (hw : w ∈ Subtype.val ⁻¹' (c '' S)ᶜ) :
      H (τ, w) ∈ Subtype.val ⁻¹' (c '' S)ᶜ := by
    rw [← e.apply_symm_apply w, mem_preimage, mem_compl_iff, hmem] at hw
    rw [mem_preimage, mem_compl_iff, hH, hmem]
    exact collarPush_notMem hθ₀ hθ₁ τ hw
  have hρS : MapsTo ρ (∅ : Set (TopCat.of (range c)))ᶜ (Subtype.val ⁻¹' (c '' S)ᶜ) := by
    intro w _
    rw [mem_preimage, mem_compl_iff, hρ, hmem]
    exact collarPush_one_notMem hθ₀ hθ₁ hθs _
  -- So the inclusion `(U, U ∖ c(S)) ⟶ (U, U)` of the collar `U` induces isomorphisms.
  have := TopPair.isIso_singularHomologyMap_ofSubsetMap_id_of_homotopy
    (X := TopCat.of (range c)) (B := Subtype.val ⁻¹' (c '' S)ᶜ) (N := (∅ : Set _)ᶜ)
    (fun _ _ ↦ not_false) H hB (fun _ _ _ ↦ not_false) hρS R k
  exact (TopPair.isZero_singularHomology_of_surjective_map
    (P := TopPair.ofSubset ((∅ : Set (TopCat.of (range c)))ᶜ)) R
    (fun w ↦ ⟨⟨w, not_false⟩, rfl⟩) k).of_iso (asIso (TopPair.singularHomologyMap
      (TopPair.ofSubsetMap (𝟙 (TopCat.of (range c))) (B := Subtype.val ⁻¹' (c '' S)ᶜ)
        (B' := (∅ : Set _)ᶜ) fun _ _ ↦ not_false) R k))

end Column

end TauCeti.IsCollar
