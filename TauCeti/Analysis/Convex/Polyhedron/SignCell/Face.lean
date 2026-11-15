/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.ContinuousAffineEquiv
public import TauCeti.Analysis.Convex.Polyhedron.Face
public import TauCeti.Analysis.Convex.Polyhedron.SignCell.Interior

/-!
# Faces, transport, and polyhedral unions of arrangement sign cells

For a finite family `g : ι → (V →ᴬ[ℝ] ℝ)` of continuous affine functionals, every nonempty
convex extreme subset of a weak sign cell `weakSignCell g σ` is again a weak sign cell
`weakSignCell g τ` for a realized sign assignment `τ` specializing `σ`
(`IsExtreme.exists_signSpecializes_weakSignCell`). Consequently, the nonempty closed cells
`realizedSignCellClosures g` are closed under nonempty convex extreme subsets, nonempty exposed
faces, and nonempty pairwise intersections, and in a topological additive group any two realized
closed cells intersect in an exposed subset of each.

Sign cells also pull back under continuous affine maps, commute with continuous affine
equivalences and surjective reindexings, and refine under enlargement of the defining functional
family up to sign. Any intersection of closed half-spaces `{x | ∀ k, f k x ≤ 0}` whose rows
agree up to sign with rows of `g` is the union of the realized closed sign cells of `g` that it
contains (`TauCeti.Convex.setOf_forall_le_eq_biUnion_realizedSignCellClosures`), and in a normed
space a realized closed cell lies in such a polyhedron precisely when its relative interior meets
it (`TauCeti.Convex.subset_setOf_forall_le_iff_inter_intrinsicInterior_nonempty`).

## References

* G. M. Ziegler, *Lectures on Polytopes*, Springer, 1995, Chapter 1 and Lecture 7.
* A. Schrijver, *Theory of Linear and Integer Programming*, Wiley, 1986, Section 8.3.
-/

public section

namespace TauCeti.Convex

section Order

variable {ι : Type*}

/-- Sign specialization is antisymmetric: two sign assignments specializing each other are
equal. -/
theorem SignSpecializes.antisymm {σ τ : ι → SignType}
    (hστ : SignSpecializes σ τ) (hτσ : SignSpecializes τ σ) : σ = τ := by
  funext j
  rcases signSpecializes_iff.mp hστ j with hσ0 | hστj
  · rcases signSpecializes_iff.mp hτσ j with hτ0 | hτσj
    · exact hσ0.trans hτ0.symm
    · exact hτσj.symm
  · exact hστj

end Order

section WeakSignCell

variable {V ι : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]

/-- Inclusion of weak sign cells recovers sign specialization whenever the smaller cell's strict
sign locus is nonempty. Nonemptiness is needed because an inconsistent strict sign assignment can
have an empty or collapsed weak cell. -/
theorem signSpecializes_of_weakSignCell_subset {g : ι → (V →ᴬ[ℝ] ℝ)}
    {σ τ : ι → SignType} (hne : (signCell g σ).Nonempty)
    (hsub : weakSignCell g σ ⊆ weakSignCell g τ) : SignSpecializes σ τ := by
  obtain ⟨p, hp⟩ := hne
  have hpτ := signSpecializes_iff.mp
    (mem_weakSignCell_iff_specializes.mp (hsub (signCell_subset_weakSignCell g σ hp)))
  refine signSpecializes_iff.mpr fun j => ?_
  simpa only [mem_signCell.mp hp j] using hpτ j

/-- For a realized strict sign assignment `σ`, inclusion `weakSignCell g σ ⊆ weakSignCell g τ`
is equivalent to `SignSpecializes σ τ`. -/
theorem weakSignCell_subset_weakSignCell_iff {g : ι → (V →ᴬ[ℝ] ℝ)}
    {σ τ : ι → SignType} (hne : (signCell g σ).Nonempty) :
    weakSignCell g σ ⊆ weakSignCell g τ ↔ SignSpecializes σ τ :=
  ⟨signSpecializes_of_weakSignCell_subset hne, weakSignCell_subset_of_specializes⟩

/-- Realized strict sign assignments with the same weak sign cell are equal. -/
theorem eq_of_weakSignCell_eq {g : ι → (V →ᴬ[ℝ] ℝ)} {σ τ : ι → SignType}
    (hσ : (signCell g σ).Nonempty) (hτ : (signCell g τ).Nonempty)
    (heq : weakSignCell g σ = weakSignCell g τ) : σ = τ :=
  (signSpecializes_of_weakSignCell_subset hσ heq.subset).antisymm
    (signSpecializes_of_weakSignCell_subset hτ heq.superset)

/-- Realized strict sign assignments with the same closed cell are equal. -/
theorem eq_of_closure_signCell_eq [ContinuousAdd V] [ContinuousSMul ℝ V]
    {g : ι → (V →ᴬ[ℝ] ℝ)} {σ τ : ι → SignType}
    (hσ : (signCell g σ).Nonempty) (hτ : (signCell g τ).Nonempty)
    (heq : closure (signCell g σ) = closure (signCell g τ)) : σ = τ := by
  rw [closure_signCell hσ, closure_signCell hτ] at heq
  exact eq_of_weakSignCell_eq hσ hτ heq

/-- Every nonempty weak sign cell of a finite affine arrangement coincides with the weak sign
cell of a realized strict sign assignment specializing the given one. -/
theorem exists_nonempty_signCell_eq_weakSignCell [Finite ι]
    {g : ι → (V →ᴬ[ℝ] ℝ)} {σ : ι → SignType}
    (hne : (weakSignCell g σ).Nonempty) :
    ∃ τ, SignSpecializes τ σ ∧ (signCell g τ).Nonempty ∧
      weakSignCell g σ = weakSignCell g τ := by
  obtain ⟨p, hp, hzero⟩ := (convex_weakSignCell g σ).exists_mem_zero_iff_forall hne
    (fun r => (weakSignCellRows g σ r).toAffineMap)
    (fun r _ hx => mem_weakSignCell_iff_rows.mp hx r)
  let τ : ι → SignType := fun j => SignType.sign (g j p)
  have hτσ : SignSpecializes τ σ := mem_weakSignCell_iff_specializes.mp hp
  refine ⟨τ, hτσ, ⟨p, mem_signCell_sign g p⟩,
    Set.Subset.antisymm ?_ (weakSignCell_subset_of_specializes hτσ)⟩
  intro x hx
  apply mem_weakSignCell_iff_specializes.mpr
  refine signSpecializes_iff.mpr fun j => ?_
  by_cases hτj : τ j = 0
  · have hp0 : weakSignCellRows g σ (j, true) p = 0 :=
      weakSignCellRows_eq_zero_iff.mpr (sign_eq_zero_iff.mp hτj)
    have hx0 : g j x = 0 := weakSignCellRows_eq_zero_iff.mp ((hzero (j, true)).mp hp0 x hx)
    exact Or.inl (sign_eq_zero_iff.mpr hx0)
  · have hστj : τ j = σ j := (signSpecializes_iff.mp hτσ j).resolve_left hτj
    simpa only [hστj] using signSpecializes_iff.mp (mem_weakSignCell_iff_specializes.mp hx) j

end WeakSignCell

end TauCeti.Convex

section ExtremeAndExposed

variable {V ι : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]

/-- Every nonempty convex extreme subset of a weak sign cell of a finite affine arrangement is a
weak sign cell of a realized strict sign assignment specializing the ambient pattern. -/
theorem IsExtreme.exists_signSpecializes_weakSignCell [Finite ι]
    {g : ι → (V →ᴬ[ℝ] ℝ)} {σ : ι → SignType} {F : Set V}
    (hF : IsExtreme ℝ (TauCeti.Convex.weakSignCell g σ) F)
    (hconv : Convex ℝ F) (hne : F.Nonempty) :
    ∃ τ, TauCeti.Convex.SignSpecializes τ σ ∧
      (TauCeti.Convex.signCell g τ).Nonempty ∧
      F = TauCeti.Convex.weakSignCell g τ := by
  classical
  have hF' : IsExtreme ℝ
      {x | ∀ r, (TauCeti.Convex.weakSignCellRows g σ r).toAffineMap x ≤ 0} F := by
    simpa only [ContinuousAffineMap.coe_toAffineMap,
      ← TauCeti.Convex.weakSignCell_eq_setOf_rows] using hF
  obtain ⟨I, rfl⟩ := hF'.eq_setOf_active
    (fun r => (TauCeti.Convex.weakSignCellRows g σ r).toAffineMap) hconv hne
  let τ₀ : ι → SignType := fun j => if (j, true) ∈ I ∨ (j, false) ∈ I then 0 else σ j
  have hτ₀σ : TauCeti.Convex.SignSpecializes τ₀ σ :=
    TauCeti.Convex.signSpecializes_iff.mpr fun j => by
      by_cases hj : (j, true) ∈ I ∨ (j, false) ∈ I <;> simp [τ₀, hj]
  have hFeq : {x : V |
      (∀ r, (TauCeti.Convex.weakSignCellRows g σ r).toAffineMap x ≤ 0) ∧
      ∀ r ∈ I, (TauCeti.Convex.weakSignCellRows g σ r).toAffineMap x = 0} =
      TauCeti.Convex.weakSignCell g τ₀ := by
    ext x
    simp only [Set.mem_ofPred_eq, ContinuousAffineMap.coe_toAffineMap,
      ← TauCeti.Convex.mem_weakSignCell_iff_rows]
    constructor
    · rintro ⟨hx, hxI⟩
      apply TauCeti.Convex.mem_weakSignCell.mpr
      intro j
      by_cases hj : (j, true) ∈ I ∨ (j, false) ∈ I
      · have hgx : g j x = 0 := by
          rcases hj with hjt | hjf
          · exact TauCeti.Convex.weakSignCellRows_eq_zero_iff.mp (hxI (j, true) hjt)
          · exact TauCeti.Convex.weakSignCellRows_eq_zero_iff.mp (hxI (j, false) hjf)
        simp [τ₀, hj, hgx]
      · simpa [τ₀, hj] using TauCeti.Convex.mem_weakSignCell.mp hx j
    · intro hx
      refine ⟨TauCeti.Convex.weakSignCell_subset_of_specializes hτ₀σ hx, ?_⟩
      rintro ⟨j, b⟩ hjb
      have hj : (j, true) ∈ I ∨ (j, false) ∈ I := by
        cases b
        · exact Or.inr hjb
        · exact Or.inl hjb
      have hτ₀j : τ₀ j = .zero := ite_eq_left hj
      exact TauCeti.Convex.weakSignCellRows_eq_zero_iff.mpr
        ((TauCeti.Convex.mem_weakSignCell.mp hx j).1 hτ₀j)
  rw [hFeq] at hne ⊢
  obtain ⟨τ, hττ₀, hτne, heq⟩ :=
    TauCeti.Convex.exists_nonempty_signCell_eq_weakSignCell hne
  exact ⟨τ, hττ₀.trans hτ₀σ, hτne, heq⟩

/-- Every nonempty exposed subset of a weak sign cell of a finite affine arrangement is the weak
sign cell of a realized strict sign assignment specializing the ambient pattern. -/
theorem IsExposed.exists_signSpecializes_weakSignCell [Finite ι]
    {g : ι → (V →ᴬ[ℝ] ℝ)} {σ : ι → SignType} {F : Set V}
    (hF : IsExposed ℝ (TauCeti.Convex.weakSignCell g σ) F) (hne : F.Nonempty) :
    ∃ τ, TauCeti.Convex.SignSpecializes τ σ ∧
      (TauCeti.Convex.signCell g τ).Nonempty ∧
      F = TauCeti.Convex.weakSignCell g τ :=
  hF.isExtreme.exists_signSpecializes_weakSignCell
    (hF.convex (TauCeti.Convex.convex_weakSignCell g σ)) hne

/-- The realized closed sign cells of a finite affine arrangement are closed under taking
nonempty convex extreme subsets. -/
theorem IsExtreme.mem_realizedSignCellClosures [ContinuousAdd V] [ContinuousSMul ℝ V]
    [Finite ι] {g : ι → (V →ᴬ[ℝ] ℝ)} {P F : Set V}
    (hF : IsExtreme ℝ P F) (hP : P ∈ TauCeti.Convex.realizedSignCellClosures g)
    (hconv : Convex ℝ F) (hne : F.Nonempty) :
    F ∈ TauCeti.Convex.realizedSignCellClosures g := by
  obtain ⟨σ, hσ, rfl⟩ := TauCeti.Convex.mem_realizedSignCellClosures.mp hP
  rw [TauCeti.Convex.closure_signCell hσ] at hF
  obtain ⟨τ, -, hτ, rfl⟩ := hF.exists_signSpecializes_weakSignCell hconv hne
  exact TauCeti.Convex.mem_realizedSignCellClosures.mpr
    ⟨τ, hτ, (TauCeti.Convex.closure_signCell hτ).symm⟩

/-- The realized closed sign cells of a finite affine arrangement are closed under taking
nonempty exposed faces. -/
theorem IsExposed.mem_realizedSignCellClosures [ContinuousAdd V] [ContinuousSMul ℝ V]
    [Finite ι] {g : ι → (V →ᴬ[ℝ] ℝ)} {P F : Set V}
    (hF : IsExposed ℝ P F) (hP : P ∈ TauCeti.Convex.realizedSignCellClosures g)
    (hne : F.Nonempty) :
    F ∈ TauCeti.Convex.realizedSignCellClosures g :=
  hF.isExtreme.mem_realizedSignCellClosures hP
    (hF.convex (TauCeti.Convex.isConvexPolyhedron_of_mem_realizedSignCellClosures hP).convex) hne

end ExtremeAndExposed

namespace TauCeti.Convex

section ClosuresAndExposed

variable {V ι : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]

/-- Every nonempty weak sign cell of a finite affine arrangement belongs to its family of
realized closed sign cells, even if the given sign assignment itself has empty strict locus. -/
theorem weakSignCell_mem_realizedSignCellClosures [ContinuousAdd V] [ContinuousSMul ℝ V]
    [Finite ι] {g : ι → (V →ᴬ[ℝ] ℝ)} {σ : ι → SignType}
    (hne : (weakSignCell g σ).Nonempty) :
    weakSignCell g σ ∈ realizedSignCellClosures g := by
  obtain ⟨τ, -, hτ, heq⟩ := exists_nonempty_signCell_eq_weakSignCell hne
  exact mem_realizedSignCellClosures.mpr ⟨τ, hτ, heq.trans (closure_signCell hτ).symm⟩

/-- A nonempty intersection of two realized closed sign cells of a finite arrangement is again a
realized closed sign cell. -/
theorem inter_mem_realizedSignCellClosures [ContinuousAdd V] [ContinuousSMul ℝ V]
    [Finite ι] {g : ι → (V →ᴬ[ℝ] ℝ)} {P Q : Set V}
    (hP : P ∈ realizedSignCellClosures g) (hQ : Q ∈ realizedSignCellClosures g)
    (hne : (P ∩ Q).Nonempty) :
    P ∩ Q ∈ realizedSignCellClosures g := by
  obtain ⟨σ, hσ, rfl⟩ := mem_realizedSignCellClosures.mp hP
  obtain ⟨τ, hτ, rfl⟩ := mem_realizedSignCellClosures.mp hQ
  rw [closure_signCell hσ, closure_signCell hτ, weakSignCell_inter] at hne ⊢
  exact weakSignCell_mem_realizedSignCellClosures hne

/-- In a topological additive group, every zero-specialized weak sign cell of a finite affine
arrangement is an exposed subset of the original weak sign cell, including when empty. -/
theorem isExposed_weakSignCell_of_specializes [IsTopologicalAddGroup V] [Finite ι]
    {g : ι → (V →ᴬ[ℝ] ℝ)} {σ τ : ι → SignType} (h : SignSpecializes τ σ) :
    IsExposed ℝ (weakSignCell g σ) (weakSignCell g τ) :=
  (isExtreme_weakSignCell_of_specializes h).isExposed_of_isConvexPolyhedron
    (isConvexPolyhedron_weakSignCell g σ) (convex_weakSignCell g τ)

/-- The nonempty exposed faces of a weak sign cell of a finite arrangement are precisely the
weak sign cells of realized sign assignments specializing its sign pattern. -/
theorem nonempty_and_isExposed_weakSignCell_iff [IsTopologicalAddGroup V] [Finite ι]
    {g : ι → (V →ᴬ[ℝ] ℝ)} {σ : ι → SignType} {F : Set V} :
    (F.Nonempty ∧ IsExposed ℝ (weakSignCell g σ) F) ↔
      ∃ τ, SignSpecializes τ σ ∧ (signCell g τ).Nonempty ∧ F = weakSignCell g τ := by
  constructor
  · rintro ⟨hne, hF⟩
    exact hF.exists_signSpecializes_weakSignCell hne
  · rintro ⟨τ, hτσ, ⟨p, hp⟩, rfl⟩
    exact ⟨⟨p, signCell_subset_weakSignCell g τ hp⟩, isExposed_weakSignCell_of_specializes hτσ⟩

/-- Any two realized closed sign cells of a finite arrangement intersect in an exposed subset of
each, including when their intersection is empty. -/
theorem isExposed_inter_of_mem_realizedSignCellClosures
    [IsTopologicalAddGroup V] [ContinuousSMul ℝ V] [Finite ι]
    {g : ι → (V →ᴬ[ℝ] ℝ)} {P Q : Set V}
    (hP : P ∈ realizedSignCellClosures g) (hQ : Q ∈ realizedSignCellClosures g) :
    IsExposed ℝ P (P ∩ Q) :=
  (isExtreme_inter_of_mem_realizedSignCellClosures hP hQ).isExposed_of_isConvexPolyhedron
    (isConvexPolyhedron_of_mem_realizedSignCellClosures hP)
    ((isConvexPolyhedron_of_mem_realizedSignCellClosures hP).convex.inter
      (isConvexPolyhedron_of_mem_realizedSignCellClosures hQ).convex)

end ClosuresAndExposed

section TransportAndRefinement

variable {V W ι κ : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
  [AddCommGroup W] [Module ℝ W] [TopologicalSpace W]

/-- Pulling back the defining affine functionals pulls back every strict sign cell. -/
@[simp]
theorem signCell_comp (g : ι → (V →ᴬ[ℝ] ℝ)) (f : W →ᴬ[ℝ] V) (σ : ι → SignType) :
    signCell (fun j => (g j).comp f) σ = f ⁻¹' signCell g σ := by
  ext x
  simp [mem_signCell]

/-- Pulling back the defining affine functionals pulls back every weak sign cell. -/
@[simp]
theorem weakSignCell_comp (g : ι → (V →ᴬ[ℝ] ℝ)) (f : W →ᴬ[ℝ] V) (σ : ι → SignType) :
    weakSignCell (fun j => (g j).comp f) σ = f ⁻¹' weakSignCell g σ := by
  ext x
  simp [mem_weakSignCell]

/-- A continuous affine equivalence transports strict sign cells by composing the arrangement
with its inverse. -/
theorem image_signCell (g : ι → (V →ᴬ[ℝ] ℝ)) (e : V ≃ᴬ[ℝ] W) (σ : ι → SignType) :
    e '' signCell g σ = signCell (fun j => (g j).comp e.symm.toContinuousAffineMap) σ := by
  rw [signCell_comp]
  exact e.toEquiv.image_eq_preimage_symm (signCell g σ)

/-- A continuous affine equivalence transports weak sign cells by composing the arrangement with
its inverse. -/
theorem image_weakSignCell (g : ι → (V →ᴬ[ℝ] ℝ)) (e : V ≃ᴬ[ℝ] W) (σ : ι → SignType) :
    e '' weakSignCell g σ = weakSignCell (fun j => (g j).comp e.symm.toContinuousAffineMap) σ := by
  rw [weakSignCell_comp]
  exact e.toEquiv.image_eq_preimage_symm (weakSignCell g σ)

/-- A continuous affine equivalence commutes with taking closures of strict sign cells. -/
theorem image_closure_signCell (g : ι → (V →ᴬ[ℝ] ℝ)) (e : V ≃ᴬ[ℝ] W) (σ : ι → SignType) :
    e '' closure (signCell g σ) =
      closure (signCell (fun j => (g j).comp e.symm.toContinuousAffineMap) σ) := by
  rw [← image_signCell]
  exact e.toHomeomorph.image_closure (signCell g σ)

/-- Transporting the realized closed sign cells of `g` along a continuous affine equivalence `e`
yields the realized closed sign cells of `g` pulled back along `e.symm`. -/
theorem image_realizedSignCellClosures (g : ι → (V →ᴬ[ℝ] ℝ)) (e : V ≃ᴬ[ℝ] W) :
    (fun P => e '' P) '' realizedSignCellClosures g =
      realizedSignCellClosures (fun j => (g j).comp e.symm.toContinuousAffineMap) := by
  ext Q
  simp only [Set.mem_image, mem_realizedSignCellClosures]
  constructor
  · rintro ⟨_, ⟨σ, hσ, rfl⟩, rfl⟩
    refine ⟨σ, ?_, image_closure_signCell g e σ⟩
    rw [← image_signCell]
    exact hσ.image e
  · rintro ⟨σ, hσ, rfl⟩
    rw [← image_signCell] at hσ
    exact ⟨closure (signCell g σ), ⟨σ, hσ.of_image, rfl⟩, image_closure_signCell g e σ⟩

/-- Reindexing an affine arrangement along a surjective map leaves its realized closed sign
cells unchanged: duplicate rows impose identical sign constraints. -/
theorem realizedSignCellClosures_comp_of_surjective (g : ι → (V →ᴬ[ℝ] ℝ)) {α : κ → ι}
    (hα : Function.Surjective α) :
    realizedSignCellClosures (g ∘ α) = realizedSignCellClosures g := by
  have hcell (σ : ι → SignType) : signCell (g ∘ α) (σ ∘ α) = signCell g σ := by
    ext x
    simp only [mem_signCell, Function.comp_apply]
    exact (hα.forall (p := fun y => SignType.sign (g y x) = σ y)).symm
  ext P
  simp only [mem_realizedSignCellClosures]
  constructor
  · rintro ⟨τ, ⟨p, hp⟩, rfl⟩
    let σ : ι → SignType := fun j => SignType.sign (g j p)
    have hτ : τ = σ ∘ α := funext fun k => (mem_signCell.mp hp k).symm
    rw [hτ, hcell]
    exact ⟨σ, ⟨p, mem_signCell_sign g p⟩, rfl⟩
  · rintro ⟨σ, hσ, rfl⟩
    exact ⟨σ ∘ α, by rwa [hcell], by rw [hcell]⟩

/-- If every row of `f` agrees up to sign with some row of `g`, then every realized closed sign
cell of `g` lies in a realized closed sign cell of `f`. -/
theorem exists_mem_realizedSignCellClosures_subset
    {g : ι → (V →ᴬ[ℝ] ℝ)} {f : κ → (V →ᴬ[ℝ] ℝ)}
    (hf : ∀ k, ∃ j, f k = g j ∨ f k = -g j)
    {P : Set V} (hP : P ∈ realizedSignCellClosures g) :
    ∃ Q ∈ realizedSignCellClosures f, P ⊆ Q := by
  obtain ⟨σ, ⟨p, hp⟩, rfl⟩ := mem_realizedSignCellClosures.mp hP
  let τ : κ → SignType := fun k => SignType.sign (f k p)
  refine ⟨closure (signCell f τ),
    mem_realizedSignCellClosures.mpr ⟨τ, ⟨p, mem_signCell_sign f p⟩, rfl⟩,
    closure_mono ?_⟩
  intro x hx
  apply mem_signCell.mpr
  intro k
  obtain ⟨j, hpos | hneg⟩ := hf k
  · simp only [hpos, τ]
    exact (mem_signCell.mp hx j).trans (mem_signCell.mp hp j).symm
  · simp only [hneg, ContinuousAffineMap.neg_apply, τ]
    have hxj := mem_signCell.mp hx j
    have hpj := mem_signCell.mp hp j
    cases hs : σ j with
    | zero =>
      have hx0 : g j x = 0 := sign_eq_zero_iff.mp (by simpa [hs] using hxj)
      have hp0 : g j p = 0 := sign_eq_zero_iff.mp (by simpa [hs] using hpj)
      rw [hx0, hp0]
    | neg =>
      have hxl : 0 < -g j x := neg_pos.mpr (sign_eq_neg_one_iff.mp (by simpa [hs] using hxj))
      have hpl : 0 < -g j p := neg_pos.mpr (sign_eq_neg_one_iff.mp (by simpa [hs] using hpj))
      rw [sign_pos hxl, sign_pos hpl]
    | pos =>
      have hxl : -g j x < 0 := neg_neg_of_pos (sign_eq_one_iff.mp (by simpa [hs] using hxj))
      have hpl : -g j p < 0 := neg_neg_of_pos (sign_eq_one_iff.mp (by simpa [hs] using hpj))
      rw [sign_neg hxl, sign_neg hpl]

/-- The realized closed sign cells of a disjoint union `Sum.elim g₁ g₂` of two finite affine
arrangements are precisely the nonempty pairwise intersections of their realized closed sign
cells. -/
theorem mem_realizedSignCellClosures_sum_iff [ContinuousAdd V] [ContinuousSMul ℝ V]
    [Finite ι] [Finite κ] {g₁ : ι → (V →ᴬ[ℝ] ℝ)} {g₂ : κ → (V →ᴬ[ℝ] ℝ)} {R : Set V} :
    R ∈ realizedSignCellClosures (Sum.elim g₁ g₂) ↔
      ∃ P ∈ realizedSignCellClosures g₁, ∃ Q ∈ realizedSignCellClosures g₂,
        (P ∩ Q).Nonempty ∧ P ∩ Q = R := by
  constructor
  · intro hR
    obtain ⟨ρ, ⟨p, hp⟩, rfl⟩ := mem_realizedSignCellClosures.mp hR
    let σ : ι → SignType := ρ ∘ Sum.inl
    let τ : κ → SignType := ρ ∘ Sum.inr
    have hρ : ρ = Sum.elim σ τ := by
      ext a
      cases a <;> rfl
    rw [hρ] at hp ⊢
    have hp' : p ∈ signCell g₁ σ ∩ signCell g₂ τ := by rwa [← signCell_sum]
    have hσ : (signCell g₁ σ).Nonempty := ⟨p, hp'.1⟩
    have hτ : (signCell g₂ τ).Nonempty := ⟨p, hp'.2⟩
    refine ⟨closure (signCell g₁ σ), mem_realizedSignCellClosures.mpr ⟨σ, hσ, rfl⟩,
      closure (signCell g₂ τ), mem_realizedSignCellClosures.mpr ⟨τ, hτ, rfl⟩,
      ⟨p, subset_closure hp'.1, subset_closure hp'.2⟩, ?_⟩
    rw [closure_signCell hσ, closure_signCell hτ,
      closure_signCell ⟨p, hp⟩, weakSignCell_sum]
  · rintro ⟨P, hP, Q, hQ, hne, rfl⟩
    obtain ⟨σ, hσ, rfl⟩ := mem_realizedSignCellClosures.mp hP
    obtain ⟨τ, hτ, rfl⟩ := mem_realizedSignCellClosures.mp hQ
    rw [closure_signCell hσ, closure_signCell hτ, ← weakSignCell_sum] at hne ⊢
    exact weakSignCell_mem_realizedSignCellClosures hne

end TransportAndRefinement

section PolyhedralUnions

variable {V ι κ : Type*}

section Topological

variable [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]

/-- If a strict sign cell of `g` contains a point satisfying a family of inequalities `f k x ≤ 0`
whose rows each agree up to sign with some row of `g`, then the entire weak sign cell lies in
`{x | ∀ k, f k x ≤ 0}`. -/
theorem weakSignCell_subset_setOf_forall_le_of_mem_signCell
    {g : ι → (V →ᴬ[ℝ] ℝ)} {f : κ → (V →ᴬ[ℝ] ℝ)}
    (hf : ∀ k, ∃ j, f k = g j ∨ f k = -g j)
    {σ : ι → SignType} {x : V} (hx : x ∈ signCell g σ) (hfx : ∀ k, f k x ≤ 0) :
    weakSignCell g σ ⊆ {y | ∀ k, f k y ≤ 0} := by
  intro y hy k
  have hkx := hfx k
  obtain ⟨j, hpos | hneg⟩ := hf k
  · rw [hpos] at hkx ⊢
    have hxj := mem_signCell.mp hx j
    rcases mem_weakSignCell.mp hy j with ⟨hz, hneg', -⟩
    cases hs : σ j with
    | zero => exact (hz hs).le
    | neg => exact hneg' hs
    | pos =>
      exfalso
      exact not_lt_of_ge hkx (sign_eq_one_iff.mp (by simpa [hs] using hxj))
  · rw [hneg] at hkx ⊢
    simp only [ContinuousAffineMap.neg_apply, neg_nonpos] at hkx ⊢
    have hxj := mem_signCell.mp hx j
    rcases mem_weakSignCell.mp hy j with ⟨hz, -, hpos'⟩
    cases hs : σ j with
    | zero => exact (hz hs).ge
    | neg =>
      exfalso
      exact not_lt_of_ge hkx (sign_eq_neg_one_iff.mp (by simpa [hs] using hxj))
    | pos => exact hpos' hs

/-- If a strict sign cell of `g` meets `{x | ∀ k, f k x ≤ 0}` and every row of `f` agrees up to
sign with some row of `g`, then the closure of that sign cell lies in `{x | ∀ k, f k x ≤ 0}`. -/
theorem closure_signCell_subset_setOf_forall_le_of_mem_signCell
    {g : ι → (V →ᴬ[ℝ] ℝ)} {f : κ → (V →ᴬ[ℝ] ℝ)}
    (hf : ∀ k, ∃ j, f k = g j ∨ f k = -g j)
    {σ : ι → SignType} {x : V} (hx : x ∈ signCell g σ) (hfx : ∀ k, f k x ≤ 0) :
    closure (signCell g σ) ⊆ {y | ∀ k, f k y ≤ 0} :=
  (closure_minimal (signCell_subset_weakSignCell g σ) (isClosed_weakSignCell g σ)).trans
    (weakSignCell_subset_setOf_forall_le_of_mem_signCell hf hx hfx)

/-- Every intersection of closed half-spaces cut out by rows that agree up to sign with rows of
`g` is the union of the realized closed sign cells of `g` that it contains. Neither finiteness
of the arrangement nor topological-group structure on `V` is required. -/
theorem setOf_forall_le_eq_biUnion_realizedSignCellClosures
    {g : ι → (V →ᴬ[ℝ] ℝ)} {f : κ → (V →ᴬ[ℝ] ℝ)}
    (hf : ∀ k, ∃ j, f k = g j ∨ f k = -g j) :
    {x | ∀ k, f k x ≤ 0} =
      ⋃ P ∈ realizedSignCellClosures g, ⋃ (_ : P ⊆ {x | ∀ k, f k x ≤ 0}), P := by
  apply Set.Subset.antisymm
  · intro x hx
    let σ : ι → SignType := fun j => SignType.sign (g j x)
    have hxs : x ∈ signCell g σ := mem_signCell_sign g x
    exact Set.mem_iUnion₂.mpr ⟨closure (signCell g σ),
      mem_realizedSignCellClosures.mpr ⟨σ, ⟨x, hxs⟩, rfl⟩,
      Set.mem_iUnion.mpr ⟨closure_signCell_subset_setOf_forall_le_of_mem_signCell hf hxs hx,
        subset_closure hxs⟩⟩
  · exact Set.iUnion₂_subset fun P _ => Set.iUnion_subset fun hP => hP

/-- Each negative closed half-space `{x | g j x ≤ 0}` is the union of the realized closed sign
cells of `g` contained in it. -/
theorem setOf_nonpos_eq_biUnion_realizedSignCellClosures
    (g : ι → (V →ᴬ[ℝ] ℝ)) (j : ι) :
    {x | g j x ≤ 0} =
      ⋃ P ∈ realizedSignCellClosures g, ⋃ (_ : P ⊆ {x | g j x ≤ 0}), P := by
  simpa using setOf_forall_le_eq_biUnion_realizedSignCellClosures (g := g)
    (f := fun _ : Unit => g j) (fun _ => ⟨j, Or.inl rfl⟩)

/-- Each positive closed half-space `{x | 0 ≤ g j x}` is the union of the realized closed sign
cells of `g` contained in it. -/
theorem setOf_nonneg_eq_biUnion_realizedSignCellClosures
    (g : ι → (V →ᴬ[ℝ] ℝ)) (j : ι) :
    {x | 0 ≤ g j x} =
      ⋃ P ∈ realizedSignCellClosures g, ⋃ (_ : P ⊆ {x | 0 ≤ g j x}), P := by
  simpa using setOf_forall_le_eq_biUnion_realizedSignCellClosures (g := g)
    (f := fun _ : Unit => -g j) (fun _ => ⟨j, Or.inr rfl⟩)

/-- Each defining affine hyperplane `{x | g j x = 0}` is the union of the realized closed sign
cells of `g` contained in it. -/
theorem setOf_eq_zero_eq_biUnion_realizedSignCellClosures
    (g : ι → (V →ᴬ[ℝ] ℝ)) (j : ι) :
    {x | g j x = 0} =
      ⋃ P ∈ realizedSignCellClosures g, ⋃ (_ : P ⊆ {x | g j x = 0}), P := by
  have heq : {x : V | g j x = 0} =
      {x : V | ∀ b : Bool, (if b then g j else -g j) x ≤ 0} := by
    ext x
    simp only [Set.mem_ofPred_eq, Bool.forall_bool, Bool.false_eq_true, ↓reduceIte,
      ContinuousAffineMap.neg_apply, neg_nonpos]
    exact ⟨fun h => ⟨h.ge, h.le⟩, fun ⟨hge, hle⟩ => le_antisymm hle hge⟩
  rw [heq]
  exact setOf_forall_le_eq_biUnion_realizedSignCellClosures (g := g)
    (f := fun b : Bool => if b then g j else -g j)
    (fun b => ⟨j, by cases b <;> simp⟩)

end Topological

section Normed

variable [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- If the relative interior of a realized closed sign cell `P` of `g` meets a half-space
intersection `S = {x | ∀ k, f k x ≤ 0}` whose rows agree up to sign with rows of `g`, then all of
`P` lies in `S`. Finiteness of `ι` is not required. -/
theorem subset_setOf_forall_le_of_inter_intrinsicInterior_nonempty
    {g : ι → (V →ᴬ[ℝ] ℝ)} {f : κ → (V →ᴬ[ℝ] ℝ)}
    (hf : ∀ k, ∃ j, f k = g j ∨ f k = -g j)
    {P : Set V} (hP : P ∈ realizedSignCellClosures g)
    (hinter : (intrinsicInterior ℝ P ∩ {x | ∀ k, f k x ≤ 0}).Nonempty) :
    P ⊆ {x | ∀ k, f k x ≤ 0} := by
  obtain ⟨x, hxP, hfx⟩ := hinter
  obtain ⟨σ, hσ, rfl⟩ := mem_realizedSignCellClosures.mp hP
  rw [closure_signCell hσ] at hxP
  exact closure_signCell_subset_setOf_forall_le_of_mem_signCell hf
    (intrinsicInterior_weakSignCell_subset_signCell hσ hxP) hfx

/-- At any relative interior point `x` of a realized closed sign cell `P` of `g`, satisfying a
family of inequalities `f k x ≤ 0` whose rows agree up to sign with rows of `g` is equivalent to
`P ⊆ {y | ∀ k, f k y ≤ 0}`. Finiteness of `ι` is not required. -/
theorem forall_le_iff_subset_of_mem_intrinsicInterior
    {g : ι → (V →ᴬ[ℝ] ℝ)} {f : κ → (V →ᴬ[ℝ] ℝ)}
    (hf : ∀ k, ∃ j, f k = g j ∨ f k = -g j)
    {P : Set V} (hP : P ∈ realizedSignCellClosures g)
    {x : V} (hx : x ∈ intrinsicInterior ℝ P) :
    (∀ k, f k x ≤ 0) ↔ P ⊆ {y | ∀ k, f k y ≤ 0} :=
  ⟨fun hfx => subset_setOf_forall_le_of_inter_intrinsicInterior_nonempty hf hP ⟨x, hx, hfx⟩,
    fun hsub => hsub (intrinsicInterior_subset hx)⟩

/-- Relative-interior dichotomy for realized closed sign cells against a half-space intersection
cut out by signed arrangement rows: either the entire closed cell lies in the polyhedron, or its
relative interior is disjoint from it. Finiteness of `ι` is not required. -/
theorem subset_or_disjoint_intrinsicInterior_setOf_forall_le
    {g : ι → (V →ᴬ[ℝ] ℝ)} {f : κ → (V →ᴬ[ℝ] ℝ)}
    (hf : ∀ k, ∃ j, f k = g j ∨ f k = -g j)
    {P : Set V} (hP : P ∈ realizedSignCellClosures g) :
    P ⊆ {x | ∀ k, f k x ≤ 0} ∨
      Disjoint (intrinsicInterior ℝ P) {x | ∀ k, f k x ≤ 0} := by
  by_cases hdisj : Disjoint (intrinsicInterior ℝ P) {x | ∀ k, f k x ≤ 0}
  · exact Or.inr hdisj
  · exact Or.inl (subset_setOf_forall_le_of_inter_intrinsicInterior_nonempty hf hP
      (Set.not_disjoint_iff.mp hdisj))

/-- For a realized closed sign cell `P` of a finite arrangement `g` and a polyhedron
`S = {x | ∀ k, f k x ≤ 0}` cut out by rows agreeing up to sign with rows of `g`, `P` lies in `S`
if and only if the relative interior of `P` meets `S`. -/
theorem subset_setOf_forall_le_iff_inter_intrinsicInterior_nonempty [Finite ι]
    {g : ι → (V →ᴬ[ℝ] ℝ)} {f : κ → (V →ᴬ[ℝ] ℝ)}
    (hf : ∀ k, ∃ j, f k = g j ∨ f k = -g j)
    {P : Set V} (hP : P ∈ realizedSignCellClosures g) :
    P ⊆ {x | ∀ k, f k x ≤ 0} ↔
      (intrinsicInterior ℝ P ∩ {x | ∀ k, f k x ≤ 0}).Nonempty := by
  refine ⟨fun hsub => ?_, subset_setOf_forall_le_of_inter_intrinsicInterior_nonempty hf hP⟩
  obtain ⟨σ, hσ, rfl⟩ := mem_realizedSignCellClosures.mp hP
  rw [intrinsicInterior_closure_signCell]
  obtain ⟨p, hp⟩ := hσ
  exact ⟨p, hp, hsub (subset_closure hp)⟩

end Normed

end PolyhedralUnions

end TauCeti.Convex
