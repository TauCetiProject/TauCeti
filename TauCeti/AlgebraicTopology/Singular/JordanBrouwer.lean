/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.CubeComplement
public import TauCeti.Analysis.InnerProductSpace.Hemisphere
public import Mathlib.Algebra.Category.ModuleCat.Products
public import Mathlib.Algebra.Field.ULift
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# The complement of an embedded sphere and the Jordan–Brouwer separation theorem

Let `Y` be a Hausdorff space in which the complement of every point has vanishing reduced
homology, such as a sphere. If `h : Sᵈ⁻¹ → Y` is an embedding of the unit sphere of a
`d`-dimensional real normed space, then the reduced homology of `Y ∖ h(Sᵈ⁻¹)` is that of `Y`
shifted down by `d`: `H_redᵢ(Y ∖ h(Sᵈ⁻¹)) ≅ H_redᵢ₊d(Y)`. For `Y = Sⁿ` this is the second half of
Hatcher's Proposition 2B.1: the complement of an embedded `k`-sphere in `Sⁿ` has the reduced
homology of an `(n - k - 1)`-sphere.

The sphere of a `d`-dimensional real normed space is homeomorphic to that of a Euclidean space of
the same dimension (`TauCeti.sphereHomeomorphOfFinrankEq`), so it suffices to treat inner
product spaces. The proof is then by induction on `d`. The unit sphere `Sᵈ⁻¹` is empty when
`d = 0`. Otherwise it is the union of the two closed hemispheres around a unit vector `p`, which
meet in the equator, the unit sphere of `(ℝ ∙ p)ᗮ`. The hemispheres are discs
(`TauCeti.hemisphereHomeomorph`), so the complements of their images are acyclic
(`TauCeti.isZero_reducedSingularHomologyFunctor_compl_range_closedBall`). These two complements
are open, their intersection is `Y ∖ h(Sᵈ⁻¹)` and their union is the complement of the image of the
equator, so the Mayer–Vietoris sequence (`TopCat.reducedMayerVietorisIsoOfIsZero`) shifts degrees
by one while lowering the dimension of the sphere by one.

In the top case of a sphere `Sᵈ⁻¹` embedded in `Sᵈ`, the reduced homology of the complement in
degree zero is one copy of the coefficients. With field coefficients, this says that the
complement has exactly two path components: the **Jordan–Brouwer separation theorem**.

## Main results

* `TauCeti.reducedSingularHomologyComplRangeSphereIso`: in a Hausdorff space `Y` whose point
  complements are acyclic, `H_redᵢ(Y ∖ h(Sᵈ⁻¹)) ≅ H_redᵢ₊d(Y)` for every embedding `h` of the unit
  sphere of a `d`-dimensional real normed space.
* `TauCeti.isZero_reducedSingularHomologyFunctor_sphere_compl_range_sphere` and
  `TauCeti.reducedSingularHomologySphereComplRangeSphereIso`: for `Y = Sⁿ`, the reduced homology of
  the complement of an embedded `Sᵈ⁻¹` vanishes in degrees `i ≠ n - d` and is one copy of the
  coefficients in degree `n - d`.
* `TauCeti.natCard_zerothHomotopy_sphere_compl_range_eq_two`: **the Jordan–Brouwer separation
  theorem**: the complement of an embedded `Sⁿ⁻¹` in `Sⁿ` has exactly two path components.

## References

* A. Hatcher, *Algebraic Topology*, Section 2.B, Proposition 2B.1(b) and Corollary 2B.2.
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicTopology Topology Set TopCat Metric Module
open scoped RealInnerProductSpace

universe w u

namespace TauCeti

section General

variable {A : Type w} [Ring A] (M : ModuleCat.{w} A) {Y : Type w} [TopologicalSpace Y] [T2Space Y]
  (hY : ∀ (y : Y) (n : ℕ), IsZero ((reducedSingularHomologyFunctor M n).obj (of ↥({y}ᶜ : Set Y))))

section InnerProduct

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

variable [FiniteDimensional ℝ E]

include hY in
/-- The complement of the image of a closed hemisphere is acyclic: the hemisphere is a disc. -/
private lemma isZero_compl_image_hemisphere {h : sphere (0 : E) 1 → Y} (hc : Continuous h)
    (hi : Function.Injective h) (p : sphere (0 : E) 1) (n : ℕ) :
    IsZero ((reducedSingularHomologyFunctor M n).obj
      (of ↥(h '' {x : sphere (0 : E) 1 | 0 ≤ ⟪(x : E), (p : E)⟫})ᶜ)) := by
  have hrange : range (h ∘ Subtype.val ∘ (hemisphereHomeomorph p).symm) =
      h '' {x : sphere (0 : E) 1 | 0 ≤ ⟪(x : E), (p : E)⟫} := by
    rw [range_comp, range_comp, (hemisphereHomeomorph p).symm.range_coe, image_univ,
      Subtype.range_coe_subtype]
  rw [← hrange]
  exact isZero_reducedSingularHomologyFunctor_compl_range_closedBall M hY
    (hc.comp (continuous_subtype_val.comp (hemisphereHomeomorph p).symm.continuous))
    (hi.comp (Subtype.val_injective.comp (hemisphereHomeomorph p).symm.injective)) n

/-- The image of a closed hemisphere is closed, so the complement of its image is open. -/
private lemma isOpen_compl_image_hemisphere {h : sphere (0 : E) 1 → Y} (hc : Continuous h)
    (p : sphere (0 : E) 1) : IsOpen (h '' {x : sphere (0 : E) 1 | 0 ≤ ⟪(x : E), (p : E)⟫})ᶜ :=
  ((isClosed_le continuous_const (by fun_prop)).isCompact.image hc).isClosed.isOpen_compl

include hY in
/-- The recursion behind `TauCeti.reducedSingularHomologyComplRangeSphereIso`, with the dimension
and the space as explicit arguments so that they can vary along the induction. -/
private def reducedSingularHomologyComplRangeSphereIsoAux :
    (d : ℕ) → (E : Type u) → [NormedAddCommGroup E] → [InnerProductSpace ℝ E] →
      [FiniteDimensional ℝ E] → finrank ℝ E = d → (h : sphere (0 : E) 1 → Y) → Continuous h →
      Function.Injective h → (i : ℕ) →
      ((reducedSingularHomologyFunctor M i).obj (of ↥(range h)ᶜ) ≅
        (reducedSingularHomologyFunctor M (i + d)).obj (of Y))
  | 0, E, _, _, _, hd, h, _, _, i =>
    -- A zero-dimensional space has an empty unit sphere, whose image has complement `Y`.
    haveI : Subsingleton E := finrank_zero_iff.1 hd
    haveI : IsEmpty (sphere (0 : E) 1) :=
      isEmpty_coe_sort.2 (sphere_eq_empty_of_subsingleton one_ne_zero)
    (reducedSingularHomologyFunctor M i).mapIso (isoOfHomeo
      ((Homeomorph.setCongr (by rw [range_eq_empty, compl_empty])).trans (Homeomorph.Set.univ Y)))
  | d + 1, E, _, _, _, hd, h, hc, hi, i =>
    haveI : Nontrivial E := Module.nontrivial_of_finrank_eq_succ hd
    haveI := (NormedSpace.sphere_nonempty (E := E) (x := 0).mpr zero_le_one).coe_sort
    haveI : Fact (finrank ℝ E = d + 1) := ⟨hd⟩
    let p : sphere (0 : E) 1 := Classical.arbitrary _
    -- Cut the sphere into the closed hemispheres around `p` and `-p`, which meet in the equator.
    let D₁ : Set (sphere (0 : E) 1) := {x | 0 ≤ ⟪(x : E), (p : E)⟫}
    let D₂ : Set (sphere (0 : E) 1) := {x | 0 ≤ ⟪(x : E), ((-p : sphere (0 : E) 1) : E)⟫}
    have hinter : (h '' D₁)ᶜ ∩ (h '' D₂)ᶜ = (range h)ᶜ := by
      rw [← compl_union, ← image_union, ← image_univ]
      congr 2
      refine eq_univ_of_forall fun x ↦ ?_
      simp only [D₁, D₂, mem_union, mem_ofPred_eq, coe_neg_sphere, inner_neg_right, neg_nonneg]
      exact le_total _ _
    have hunion : (h '' D₁)ᶜ ∪ (h '' D₂)ᶜ = (range (h ∘ equatorInclusion p))ᶜ := by
      rw [← compl_inter, ← image_inter hi, range_comp, range_equatorInclusion]
    (TopCat.reducedMayerVietorisIsoOfIsZero M (Y := of Y) (isOpen_compl_image_hemisphere hc p)
      (isOpen_compl_image_hemisphere hc (-p)) hinter hunion
      (isZero_compl_image_hemisphere M hY hc hi p _)
      (isZero_compl_image_hemisphere M hY hc hi (-p) _)
      (isZero_compl_image_hemisphere M hY hc hi p _)
      (isZero_compl_image_hemisphere M hY hc hi (-p) _)).symm ≪≫
      reducedSingularHomologyComplRangeSphereIsoAux d (ℝ ∙ (p : E))ᗮ
        (Submodule.finrank_orthogonal_span_singleton (ne_zero_of_mem_unit_sphere p))
        (h ∘ equatorInclusion p) (hc.comp (continuous_equatorInclusion p))
        (hi.comp (injective_equatorInclusion p)) (i + 1) ≪≫
      eqToIso (congrArg (fun k ↦ (reducedSingularHomologyFunctor M k).obj (of Y)) (by omega))

end InnerProduct

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

include hY in
/-- **The homology of the complement of an embedded sphere.** Let `Y` be a Hausdorff space in which
the complement of every point has vanishing reduced homology, and let `h` be a continuous injection
into `Y` of the unit sphere of a real normed space of dimension `d`. Then
`H_redᵢ(Y ∖ h(Sᵈ⁻¹)) ≅ H_redᵢ₊d(Y)`, with coefficients in any module.

This is Hatcher, *Algebraic Topology*, Proposition 2B.1(b), in a general form. Like
`TauCeti.reducedSingularHomologySphereIso`, the isomorphism depends on a chosen point of each
sphere in the induction on the dimension, and is not a canonical identification. -/
def reducedSingularHomologyComplRangeSphereIso {h : sphere (0 : E) 1 → Y} (hc : Continuous h)
    (hi : Function.Injective h) (i : ℕ) :
    (reducedSingularHomologyFunctor M i).obj (of ↥(range h)ᶜ) ≅
      (reducedSingularHomologyFunctor M (i + finrank ℝ E)).obj (of Y) :=
  -- Replace `E` by a Euclidean space of the same dimension, which has the same unit sphere.
  let e := sphereHomeomorphOfFinrankEq (E := E) (F := EuclideanSpace ℝ (Fin (finrank ℝ E)))
    finrank_euclideanSpace_fin.symm
  (reducedSingularHomologyFunctor M i).mapIso
      (isoOfHomeo (Homeomorph.setCongr (by rw [e.symm.surjective.range_comp h]))) ≪≫
    reducedSingularHomologyComplRangeSphereIsoAux M hY _ _ finrank_euclideanSpace_fin
      (h ∘ e.symm) (hc.comp e.symm.continuous) (hi.comp e.symm.injective) i

end General

section Sphere

variable {A : Type w} [Ring A] (M : ModuleCat.{w} A)
  {F : Type w} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {h : sphere (0 : E) 1 → sphere (0 : F) 1}

/-- **The complement of an embedded sphere in a sphere is acyclic outside one degree.** Let `h` be a
continuous injection of the unit sphere of a finite-dimensional real normed space `E` into the unit
sphere of an `(n + 1)`-dimensional one. Then the reduced homology of the complement of its image
vanishes in every degree `i` with `i + dim E ≠ n` (Hatcher, *Algebraic Topology*,
Proposition 2B.1(b)). -/
theorem isZero_reducedSingularHomologyFunctor_sphere_compl_range_sphere {n : ℕ}
    (hF : finrank ℝ F = n + 1) (hc : Continuous h) (hi : Function.Injective h) {i : ℕ}
    (hin : i + finrank ℝ E ≠ n) :
    IsZero ((reducedSingularHomologyFunctor M i).obj (of ↥(range h)ᶜ)) :=
  haveI : FiniteDimensional ℝ F := .of_finrank_pos (by omega)
  ((isZero_reducedSingularHomologyFunctor_sphere_of_ne M (by simp) hin).of_iso
    (reducedSingularHomologySphereIsoOfFinrankEq M
      (F := EuclideanSpace ℝ (ULift.{w} (Fin (n + 1)))) (by simp [hF]) _)).of_iso
    (reducedSingularHomologyComplRangeSphereIso M
      (isZero_reducedSingularHomologyFunctor_sphere_compl_singleton M) hc hi i)

/-- **The complement of an embedded sphere in a sphere has the homology of a sphere.** Let `h` be a
continuous injection of the unit sphere of a finite-dimensional real normed space `E` into the unit
sphere of a real normed space of dimension `i + dim E + 1`. Then the reduced homology of the
complement of its image in degree `i` is one copy of the coefficients (Hatcher, *Algebraic
Topology*, Proposition 2B.1(b)). Like `TauCeti.reducedSingularHomologySphereIso`, the isomorphism
depends on chosen points, and is one choice of generator rather than a canonical identification. -/
def reducedSingularHomologySphereComplRangeSphereIso {i : ℕ}
    (hF : finrank ℝ F = i + finrank ℝ E + 1) (hc : Continuous h) (hi : Function.Injective h) :
    (reducedSingularHomologyFunctor M i).obj (of ↥(range h)ᶜ) ≅ M :=
  haveI : FiniteDimensional ℝ F := .of_finrank_pos (by omega)
  reducedSingularHomologyComplRangeSphereIso M
      (isZero_reducedSingularHomologyFunctor_sphere_compl_singleton M) hc hi i ≪≫
    reducedSingularHomologySphereIsoOfFinrankEq M
      (F := EuclideanSpace ℝ (ULift.{w} (Fin (i + finrank ℝ E + 1)))) (by simp [hF]) _ ≪≫
    reducedSingularHomologySphereIso M (by simp)

/-- **The Jordan–Brouwer separation theorem.** The complement of the image of a continuous injection
of the unit sphere of a finite-dimensional real normed space `E` into the unit sphere of a real
normed space of dimension `dim E + 1` has exactly two path components (Hatcher,
*Algebraic Topology*, Corollary 2B.2). -/
theorem natCard_zerothHomotopy_sphere_compl_range_eq_two (hEF : finrank ℝ F = finrank ℝ E + 1)
    (hc : Continuous h) (hi : Function.Injective h) :
    Nat.card (ZerothHomotopy ↥(range h)ᶜ) = 2 := by
  classical
  let K := ULift.{w} ℚ
  let e := reducedSingularHomologySphereComplRangeSphereIso (ModuleCat.of K K) (i := 0)
    (by rw [hEF, zero_add]) hc hi
  -- The complement is nonempty, as its reduced zeroth homology is not zero.
  obtain ⟨x⟩ : Nonempty ↥(range h)ᶜ := by
    by_contra hX
    rw [not_nonempty_iff] at hX
    exact not_subsingleton K (ModuleCat.subsingleton_of_isZero
      ((isZero_reducedSingularHomologyFunctor_of_isEmpty (ModuleCat.of K K) _ 0).of_iso e.symm))
  -- By `TauCeti.reducedSingularHomologySphereComplRangeSphereIso`, the reduced zeroth homology is
  -- `K`. It is also the direct sum of copies of `K` indexed by the path components other than
  -- that of `x`, so there is exactly one of them.
  have hrank := ((ModuleCat.coprodIsoDirectSum _).symm ≪≫
    (reducedSingularHomology₀Iso (ModuleCat.of K K) (X := of ↥(range h)ᶜ) x).symm ≪≫
      e).toLinearEquiv.rank_eq
  simp only [rank_directSum, rank_self, Cardinal.sum_const', mul_one] at hrank
  obtain ⟨hsub, hne⟩ := Cardinal.eq_one_iff_unique.1 hrank
  have : Unique {c : ZerothHomotopy ↥(range h)ᶜ // c ≠ ZerothHomotopy.mk x} :=
    @Unique.mk' _ ⟨Classical.arbitrary _⟩ hsub
  rw [← Nat.card_congr (Equiv.optionSubtypeNe (ZerothHomotopy.mk x)), Finite.card_option,
    Nat.card_unique]

end Sphere

end TauCeti
