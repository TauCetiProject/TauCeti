/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.RealAlgebraic.Multiprojective.Basic
public import TauCeti.Geometry.RealAlgebraic.Semialgebraic.Local

/-!
# Local-to-global semialgebraicity on real multiprojective and mixed spaces

Over `ℝ`, compactness of `M = ∀ i : ι, ℙ ℝ (Fin (n i + 1) → ℝ)` upgrades local chartwise
semialgebraicity (`TauCeti.SemialgebraicAt`) at every point of `M` to global semialgebraicity
(`TauCeti.isMultiprojectiveSemialgebraic_iff_forall_semialgebraicAt`,
`TauCeti.isMultiprojectiveSemialgebraic_iff_exists_semialgebraicAt`), derived as the empty-affine
case of `TauCeti.isMixedSemialgebraic_of_isBounded_fst`: when `S ⊆ (σ → ℝ) × M` has bounded
affine projection `Prod.fst '' S`, its closure is compact by Tychonoff's theorem, finitely many
chart preimages of open semialgebraic neighbourhoods cover `closure S`, and rational transition
pullbacks (`TauCeti.isSemialgebraic_mixedAffineChart_image_inter`) assemble them in every target
chart without assuming finiteness of `σ`.

## Main results

* `TauCeti.isMixedSemialgebraic_of_isBounded_fst`: a subset of `(σ → ℝ) × M` with bounded affine
  projection that is locally semialgebraic in some standard chart at every point of `closure S` is
  mixed semialgebraic.
* `TauCeti.isMultiprojectiveSemialgebraic_iff_exists_semialgebraicAt`,
  `TauCeti.isMultiprojectiveSemialgebraic_iff_forall_semialgebraicAt`: local-to-global chartwise
  characterizations of `TauCeti.IsMultiprojectiveSemialgebraic` over `ℝ`.

## References

* S. Łojasiewicz, *Triangulation of semi-analytic sets*, Annali della Scuola Normale Superiore di
  Pisa (3) 18 (1964), 449–474, §3, p. 464.
* J. Bochnak, M. Coste, and M.-F. Roy, *Real Algebraic Geometry*, Ergebnisse der Mathematik
  und ihrer Grenzgebiete 36, Springer (1998), Chapter 2 and Section 3.4.
-/

public section

open MvPolynomial Set Topology
open scoped LinearAlgebra.Projectivization

namespace TauCeti

section RealLocalToGlobal

variable {ι σ : Type*} {n : ι → ℕ}

/-- **Local-to-global chart criterion on mixed spaces with bounded affine projection.**
If `S ⊆ (σ → ℝ) × ∀ i : ι, ℙ ℝ (Fin (n i + 1) → ℝ)` has bounded projection to `σ → ℝ` and is
locally semialgebraic at every point of `closure S` in some standard product affine chart
containing that point, then `S` is mixed semialgebraic. -/
theorem isMixedSemialgebraic_of_isBounded_fst [Finite ι]
    {S : Set ((σ → ℝ) × ∀ i, ℙ ℝ (Fin (n i + 1) → ℝ))}
    (hb : Bornology.IsBounded (Prod.fst '' S))
    (hloc : ∀ x ∈ closure S, ∃ I, x ∈ mixedAffineOpen σ I ∧
      SemialgebraicAt (mixedAffineChart σ I '' (S ∩ mixedAffineOpen σ I))
        (mixedAffineChart σ I x)) :
    IsMixedSemialgebraic S := by
  have hK : IsCompact (closure S) :=
    ((isCompact_univ_pi fun a ↦ (hb.image_eval a).isCompact_closure).prod
      isCompact_univ).of_isClosed_subset isClosed_closure <|
      closure_minimal (fun x hx ↦ ⟨fun a _ ↦ subset_closure ⟨x.1, ⟨x, hx, rfl⟩, rfl⟩, mem_univ _⟩)
        ((isClosed_set_pi fun _ _ ↦ isClosed_closure).prod isClosed_univ)
  choose I hxI hsemi using fun x : closure S ↦ hloc x.1 x.2
  choose B hBo hxB _ hSB using fun x : closure S ↦ semialgebraicAt_def.1 (hsemi x)
  let V : closure S → Set ((σ → ℝ) × ∀ i, ℙ ℝ (Fin (n i + 1) → ℝ)) :=
    fun x ↦ mixedAffineOpen σ (I x) ∩ mixedAffineChart σ (I x) ⁻¹' B x
  have hV_open (x : closure S) : IsOpen (V x) := by
    simpa [V] using (mixedAffineOpenPartialHomeomorph (K := ℝ) σ (I x)).isOpen_inter_preimage
      (hBo x)
  have hxV (x : closure S) : x.1 ∈ V x := ⟨hxI x, hxB x⟩
  obtain ⟨t, ht⟩ := hK.elim_nhds_subcover' (fun x hx ↦ V ⟨x, hx⟩)
    fun x hx ↦ (hV_open ⟨x, hx⟩).mem_nhds (hxV ⟨x, hx⟩)
  rw [isMixedSemialgebraic_iff_forall_chart]
  intro J
  have hcover : mixedAffineChart σ J '' (S ∩ mixedAffineOpen σ J) =
      ⋃ x ∈ t, mixedAffineChart σ J '' ((S ∩ V x) ∩ mixedAffineOpen σ J) := by
    ext w
    simp only [mem_iUnion, mem_image, mem_inter_iff]
    constructor
    · rintro ⟨y, ⟨hyS, hyJ⟩, hyw⟩
      obtain ⟨x, hxt, hyx⟩ := mem_iUnion₂.1 (ht (subset_closure hyS))
      exact ⟨x, hxt, y, ⟨⟨hyS, hyx⟩, hyJ⟩, hyw⟩
    · rintro ⟨_, _, y, ⟨⟨hyS, _⟩, hyJ⟩, hyw⟩
      exact ⟨y, ⟨hyS, hyJ⟩, hyw⟩
  rw [hcover]
  exact .biUnion t.finite_toSet fun x _ ↦
    isSemialgebraic_mixedAffineChart_image_inter (hSB x)

/-- **Local-to-global chart criterion on real multiprojective space (existential chart form).**
A subset `S` of `M = ∀ i : ι, ℙ ℝ (Fin (n i + 1) → ℝ)` is multiprojective semialgebraic if and
only if at every point `p : M` there is a standard product affine chart `I` around `p` in which
`S` is locally semialgebraic (`TauCeti.SemialgebraicAt`) at `multiprojectiveAffineChart I p`. -/
theorem isMultiprojectiveSemialgebraic_iff_exists_semialgebraicAt [Finite ι]
    {S : Set (∀ i, ℙ ℝ (Fin (n i + 1) → ℝ))} :
    IsMultiprojectiveSemialgebraic S ↔
      ∀ p, ∃ I : ∀ i, Fin (n i + 1), p ∈ multiprojectiveAffineOpen I ∧
        SemialgebraicAt (multiprojectiveAffineChart I '' (S ∩ multiprojectiveAffineOpen I))
          (multiprojectiveAffineChart I p) := by
  refine ⟨fun hS p ↦ ?_, fun hloc ↦ ?_⟩
  · obtain ⟨I, hpI⟩ := exists_mem_multiprojectiveAffineOpen p
    exact ⟨I, hpI, (hS.isSemialgebraic_chart I).semialgebraicAt _⟩
  · rw [← isMixedSemialgebraic_univ_prod_iff (σ := Empty)]
    refine isMixedSemialgebraic_of_isBounded_fst
      (isCompact_univ.isBounded.subset (subset_univ _)) fun ⟨x₀, p⟩ _ ↦ ?_
    obtain ⟨I, hpI, hSp⟩ := hloc p
    refine ⟨I, mem_mixedAffineOpen.2 hpI, ?_⟩
    rw [mixedAffineChart_image_univ_prod_inter_affineOpen]
    let f : (Σ i, Fin (n i)) → MvPolynomial (Empty ⊕ Σ i, Fin (n i)) ℝ := fun q ↦ X (.inr q)
    have hpre : (fun w : (Empty ⊕ Σ i, Fin (n i)) → ℝ ↦ w ∘ Sum.inr) =
        fun y q ↦ eval y (f q) := by
      ext w q
      simp [f]
    rw [hpre]
    refine SemialgebraicAt.preimage_eval f ?_
    convert hSp using 1
    ext q
    simp [f]

/-- **Local-to-global chart criterion on real multiprojective space (universal chart form).**
A subset `S` of `M = ∀ i : ι, ℙ ℝ (Fin (n i + 1) → ℝ)` is multiprojective semialgebraic if and
only if at every point `p : M` and in every standard product affine chart `I` containing `p`, the
chart image of `S` is locally semialgebraic at `multiprojectiveAffineChart I p`. -/
theorem isMultiprojectiveSemialgebraic_iff_forall_semialgebraicAt [Finite ι]
    {S : Set (∀ i, ℙ ℝ (Fin (n i + 1) → ℝ))} :
    IsMultiprojectiveSemialgebraic S ↔
      ∀ p (I : ∀ i, Fin (n i + 1)), p ∈ multiprojectiveAffineOpen I →
        SemialgebraicAt (multiprojectiveAffineChart I '' (S ∩ multiprojectiveAffineOpen I))
          (multiprojectiveAffineChart I p) := by
  refine ⟨fun hS p I _ ↦ (hS.isSemialgebraic_chart I).semialgebraicAt _, fun h ↦ ?_⟩
  rw [isMultiprojectiveSemialgebraic_iff_exists_semialgebraicAt]
  intro p
  obtain ⟨I, hpI⟩ := exists_mem_multiprojectiveAffineOpen p
  exact ⟨I, hpI, h p I hpI⟩

end RealLocalToGlobal

end TauCeti
