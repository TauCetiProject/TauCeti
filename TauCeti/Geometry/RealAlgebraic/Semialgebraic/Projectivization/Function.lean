/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.RealAlgebraic.Semialgebraic.Projectivization.Mixed

/-!
# Semialgebraic maps between mixed and multiprojective spaces

Because the Cartesian product of two mixed spaces `(σ → K) × M` and `(τ → K) × M'` identifies via
`TauCeti.prodAffineMultiprojectiveEquiv` with a single mixed space
`(σ ⊕ τ → K) × ((k : ι ⊕ ι') → ℙ K (Sum.elim κ κ' k → K))`, semialgebraic maps between mixed
spaces (`TauCeti.IsAffineMultiprojectiveSemialgebraicOn` and
`TauCeti.IsAffineMultiprojectiveSemialgebraicMap`) are defined purely by their graphs, with no
continuity hypothesis.

Over **any** ordered field, transporting graphs along the injective embedding
`Projectivization.affinePiProjectorCoords` identifies mixed semialgebraic maps with affine
semialgebraic functions on the embedded projector models via `Function.extend`
(`TauCeti.isAffineMultiprojectiveSemialgebraicOn_iff_isSemialgebraicOn_extend`). Over an ordered
field with semialgebraic projections, closure under images, inverse images, composition, and left
inverses follows directly from `TauCeti.Geometry.RealAlgebraic.Semialgebraic.Image` assuming only
`[Finite ...]` on the relevant coordinate index types.

Pure multiprojective semialgebraic maps (`TauCeti.IsMultiprojectiveSemialgebraicOn` and
`TauCeti.IsMultiprojectiveSemialgebraicMap`) and maps between affine domains and multiprojective
spaces—including inverse maps on subsets of the flattened product projector locus—are then
obtained as specializations without duplicating proofs.

## Main declarations

* `TauCeti.IsAffineMultiprojectiveSemialgebraicOn` and
  `TauCeti.IsAffineMultiprojectiveSemialgebraicMap`: semialgebraic maps between mixed
  affine-multiprojective spaces, defined by their graphs, with restriction, gluing, constant,
  identity, image, preimage, composition, and left-inverse theorems.
* `TauCeti.isAffineMultiprojectiveSemialgebraicOn_iff_isSemialgebraicOn_extend`: equivalence with
  semialgebraicity of the transported map on `affinePiProjectorCoords '' S`.
* `TauCeti.IsMultiprojectiveSemialgebraicOn` and `TauCeti.IsMultiprojectiveSemialgebraicMap`: pure
  multiprojective semialgebraic maps as the `Empty`-affine specialization, with image, preimage,
  composition, and left-inverse theorems.
* `TauCeti.isAffineMultiprojectiveSemialgebraic_graphOn_iff`,
  `TauCeti.IsSemialgebraicOn.isMultiprojectiveSemialgebraic_image`,
  `TauCeti.IsSemialgebraicOn.isSemialgebraic_inter_preimage_multiprojective`, and
  `TauCeti.isSemialgebraicOn_piProjectorCoords_comp_of_rightInvOn`: projector criteria and
  image/preimage transport for maps between affine coordinate spaces and multiprojective spaces.

## References

* S. Łojasiewicz, *Triangulation of semi-analytic sets*, Annali della Scuola Normale Superiore di
  Pisa (3) 18 (1964), 449–474, §3, p. 464.
* J. Bochnak, M. Coste and M.-F. Roy, *Real Algebraic Geometry*, Ergebnisse der Mathematik und
  ihrer Grenzgebiete (3) 36, Springer, 1998, §§2.2, 3.4.
-/

public section

universe v

open Projectivization Set
open scoped LinearAlgebra.Projectivization

namespace TauCeti

/-! ### Semialgebraic maps between mixed affine-multiprojective spaces -/

section MixedMaps

section Basic

variable {σ τ ι ι' : Type*} {κ : ι → Type v} {κ' : ι' → Type v}
  {K : Type*} [Field K] [LinearOrder K]

/-- A map between mixed affine-multiprojective spaces is *affine-multiprojective semialgebraic on
`S`* if both `S` and the graph `S.graphOn f` (viewed in the combined mixed space via
`prodAffineMultiprojectiveEquiv`) are affine-multiprojective semialgebraic. No continuity is
assumed. -/
def IsAffineMultiprojectiveSemialgebraicOn
    (f : (σ → K) × ((i : ι) → ℙ K (κ i → K)) →
         (τ → K) × ((j : ι') → ℙ K (κ' j → K)))
    (S : Set ((σ → K) × ((i : ι) → ℙ K (κ i → K)))) : Prop :=
  IsAffineMultiprojectiveSemialgebraic S ∧
    IsAffineMultiprojectiveSemialgebraic
      (prodAffineMultiprojectiveEquiv σ τ κ κ' K ⁻¹' S.graphOn f)

/-- A map between mixed affine-multiprojective spaces is *affine-multiprojective semialgebraic* if
it is affine-multiprojective semialgebraic on `univ`. -/
def IsAffineMultiprojectiveSemialgebraicMap
    (f : (σ → K) × ((i : ι) → ℙ K (κ i → K)) →
         (τ → K) × ((j : ι') → ℙ K (κ' j → K))) : Prop :=
  IsAffineMultiprojectiveSemialgebraicOn f univ

@[simp]
theorem isAffineMultiprojectiveSemialgebraicOn_univ
    {f : (σ → K) × ((i : ι) → ℙ K (κ i → K)) →
         (τ → K) × ((j : ι') → ℙ K (κ' j → K))} :
    IsAffineMultiprojectiveSemialgebraicOn f univ ↔
      IsAffineMultiprojectiveSemialgebraicMap f :=
  Iff.rfl

theorem isAffineMultiprojectiveSemialgebraicOn_def
    {f : (σ → K) × ((i : ι) → ℙ K (κ i → K)) →
         (τ → K) × ((j : ι') → ℙ K (κ' j → K))}
    {S : Set ((σ → K) × ((i : ι) → ℙ K (κ i → K)))} :
    IsAffineMultiprojectiveSemialgebraicOn f S ↔
      IsAffineMultiprojectiveSemialgebraic S ∧
        IsAffineMultiprojectiveSemialgebraic
          (prodAffineMultiprojectiveEquiv σ τ κ κ' K ⁻¹' S.graphOn f) :=
  Iff.rfl

theorem IsAffineMultiprojectiveSemialgebraicOn.isAffineMultiprojectiveSemialgebraic
    {f : (σ → K) × ((i : ι) → ℙ K (κ i → K)) →
         (τ → K) × ((j : ι') → ℙ K (κ' j → K))}
    {S : Set ((σ → K) × ((i : ι) → ℙ K (κ i → K)))}
    (hf : IsAffineMultiprojectiveSemialgebraicOn f S) :
    IsAffineMultiprojectiveSemialgebraic S :=
  hf.1

theorem IsAffineMultiprojectiveSemialgebraicOn.graph
    {f : (σ → K) × ((i : ι) → ℙ K (κ i → K)) →
         (τ → K) × ((j : ι') → ℙ K (κ' j → K))}
    {S : Set ((σ → K) × ((i : ι) → ℙ K (κ i → K)))}
    (hf : IsAffineMultiprojectiveSemialgebraicOn f S) :
    IsAffineMultiprojectiveSemialgebraic
      (prodAffineMultiprojectiveEquiv σ τ κ κ' K ⁻¹' S.graphOn f) :=
  hf.2

@[simp]
theorem isAffineMultiprojectiveSemialgebraicOn_empty
    (f : (σ → K) × ((i : ι) → ℙ K (κ i → K)) →
         (τ → K) × ((j : ι') → ℙ K (κ' j → K))) :
    IsAffineMultiprojectiveSemialgebraicOn f ∅ := by
  simp [IsAffineMultiprojectiveSemialgebraicOn]

/-- Restricting an affine-multiprojective semialgebraic map to an affine-multiprojective
semialgebraic subset preserves semialgebraicity. -/
theorem IsAffineMultiprojectiveSemialgebraicOn.mono
    [Finite ι'] [∀ j, Finite (κ' j)]
    {f : (σ → K) × ((i : ι) → ℙ K (κ i → K)) →
         (τ → K) × ((j : ι') → ℙ K (κ' j → K))}
    {S T : Set ((σ → K) × ((i : ι) → ℙ K (κ i → K)))}
    (hf : IsAffineMultiprojectiveSemialgebraicOn f S)
    (hT : IsAffineMultiprojectiveSemialgebraic T) (hTS : T ⊆ S) :
    IsAffineMultiprojectiveSemialgebraicOn f T := by
  refine ⟨hT, ?_⟩
  have hsub : T.graphOn f = S.graphOn f ∩ T ×ˢ univ := by
    ext ⟨x, y⟩
    simp only [mem_graphOn, mem_inter_iff, mem_prod, mem_univ, and_true]
    exact ⟨fun ⟨hxT, hy⟩ ↦ ⟨⟨hTS hxT, hy⟩, hxT⟩, fun ⟨⟨_, hy⟩, hxT⟩ ↦ ⟨hxT, hy⟩⟩
  rw [hsub, preimage_inter]
  exact hf.graph.inter (hT.prod isAffineMultiprojectiveSemialgebraic_univ)

theorem IsAffineMultiprojectiveSemialgebraicMap.isAffineMultiprojectiveSemialgebraicOn
    [Finite ι'] [∀ j, Finite (κ' j)]
    {f : (σ → K) × ((i : ι) → ℙ K (κ i → K)) →
         (τ → K) × ((j : ι') → ℙ K (κ' j → K))}
    (hf : IsAffineMultiprojectiveSemialgebraicMap f)
    {S : Set ((σ → K) × ((i : ι) → ℙ K (κ i → K)))}
    (hS : IsAffineMultiprojectiveSemialgebraic S) :
    IsAffineMultiprojectiveSemialgebraicOn f S :=
  hf.mono hS (subset_univ S)

theorem IsAffineMultiprojectiveSemialgebraicOn.congr
    {f g : (σ → K) × ((i : ι) → ℙ K (κ i → K)) →
           (τ → K) × ((j : ι') → ℙ K (κ' j → K))}
    {S : Set ((σ → K) × ((i : ι) → ℙ K (κ i → K)))}
    (hf : IsAffineMultiprojectiveSemialgebraicOn f S) (h : S.EqOn f g) :
    IsAffineMultiprojectiveSemialgebraicOn g S := by
  refine ⟨hf.1, ?_⟩
  rw [← Set.graphOn_inj.2 h]
  exact hf.2

/-- Piecewise gluing of two affine-multiprojective semialgebraic functions on `S ∩ T` and
`S \ T`. -/
theorem IsAffineMultiprojectiveSemialgebraicOn.glue
    {f g h : (σ → K) × ((i : ι) → ℙ K (κ i → K)) →
             (τ → K) × ((j : ι') → ℙ K (κ' j → K))}
    {S T : Set ((σ → K) × ((i : ι) → ℙ K (κ i → K)))}
    (hf : IsAffineMultiprojectiveSemialgebraicOn f (S ∩ T))
    (hg : IsAffineMultiprojectiveSemialgebraicOn g (S \ T))
    (hft : (S ∩ T).EqOn h f) (hgt : (S \ T).EqOn h g) :
    IsAffineMultiprojectiveSemialgebraicOn h S := by
  have hh1 := hf.congr hft.symm
  have hh2 := hg.congr hgt.symm
  have hST : S = (S ∩ T) ∪ (S \ T) := (inter_union_sdiff S T).symm
  refine ⟨hST ▸ hh1.1.union hh2.1, ?_⟩
  rw [hST, Set.graphOn_union, preimage_union]
  exact hh1.2.union hh2.2

/-- A constant map into a mixed space with finite output coordinates is affine-multiprojective
semialgebraic on every affine-multiprojective semialgebraic domain. -/
theorem isAffineMultiprojectiveSemialgebraicOn_const
    [Finite τ] [Finite ι'] [∀ j, Finite (κ' j)]
    (c : (τ → K) × ((j : ι') → ℙ K (κ' j → K)))
    {S : Set ((σ → K) × ((i : ι) → ℙ K (κ i → K)))}
    (hS : IsAffineMultiprojectiveSemialgebraic S) :
    IsAffineMultiprojectiveSemialgebraicOn (fun _ ↦ c) S := by
  refine ⟨hS, ?_⟩
  have hgraph : S.graphOn (fun _ ↦ c) = S ×ˢ {c} := by
    ext ⟨x, y⟩
    simp [eq_comm]
  rw [hgraph]
  exact hS.prod (isAffineMultiprojectiveSemialgebraic_singleton c)

/-- A constant map into a mixed space with finite output coordinates is affine-multiprojective
semialgebraic when the input multiprojective coordinates are finite. -/
theorem isAffineMultiprojectiveSemialgebraicMap_const
    [Finite ι] [∀ i, Finite (κ i)] [Finite τ] [Finite ι'] [∀ j, Finite (κ' j)]
    (c : (τ → K) × ((j : ι') → ℙ K (κ' j → K))) :
    IsAffineMultiprojectiveSemialgebraicMap
      (fun _ : (σ → K) × ((i : ι) → ℙ K (κ i → K)) ↦ c) :=
  isAffineMultiprojectiveSemialgebraicOn_const c isAffineMultiprojectiveSemialgebraic_univ

/-- The identity map on a mixed space with finite coordinates is affine-multiprojective
semialgebraic. -/
@[simp]
theorem isAffineMultiprojectiveSemialgebraicMap_id
    [Finite σ] [Finite ι] [∀ i, Finite (κ i)] :
    IsAffineMultiprojectiveSemialgebraicMap
      (id : (σ → K) × ((i : ι) → ℙ K (κ i → K)) → (σ → K) × ((i : ι) → ℙ K (κ i → K))) := by
  refine ⟨isAffineMultiprojectiveSemialgebraic_univ, ?_⟩
  have h : (univ : Set ((σ → K) × ((i : ι) → ℙ K (κ i → K)))).graphOn id =
      diagonal ((σ → K) × ((i : ι) → ℙ K (κ i → K))) := by
    ext ⟨x, y⟩
    simp [mem_diagonal_iff]
  rw [h]
  exact isAffineMultiprojectiveSemialgebraic_diagonal

end Basic

section ExtendCharacterization

variable {σ τ ι ι' : Type*}
  {κ : ι → Type v} {κ' : ι' → Type v}
  [hκ : ∀ i, Fintype (κ i)] [hκ' : ∀ j, Fintype (κ' j)]
  {K : Type*} [Field K]

private theorem affinePiProjectorCoords_prodAffineMultiprojectiveEquiv_symm
    (x : (σ → K) × ((i : ι) → ℙ K (κ i → K)))
    (y : (τ → K) × ((j : ι') → ℙ K (κ' j → K))) :
    letI : ∀ k : ι ⊕ ι', Fintype (Sum.elim κ κ' k) := Sum.rec hκ hκ'
    affinePiProjectorCoords ((prodAffineMultiprojectiveEquiv σ τ κ κ' K).symm (x, y)) ∘
        (graphProjectorIndexEquiv σ τ κ κ').symm =
      Sum.elim (affinePiProjectorCoords x) (affinePiProjectorCoords y) := by
  let _ : ∀ k : ι ⊕ ι', Fintype (Sum.elim κ κ' k) := Sum.rec hκ hκ'
  funext u
  rcases u with ((s | ⟨i, a, b⟩) | (t | ⟨j, c, d⟩)) <;>
    simp [affinePiProjectorCoords_def] <;> rfl

variable [LinearOrder K] [IsStrictOrderedRing K]

private theorem image_affinePiProjectorCoords_graphOn_eq
    (f : (σ → K) × ((i : ι) → ℙ K (κ i → K)) →
         (τ → K) × ((j : ι') → ℙ K (κ' j → K)))
    (S : Set ((σ → K) × ((i : ι) → ℙ K (κ i → K)))) :
    letI : ∀ k : ι ⊕ ι', Fintype (Sum.elim κ κ' k) := Sum.rec hκ hκ'
    (fun w ↦ w ∘ (graphProjectorIndexEquiv σ τ κ κ').symm) ⁻¹'
        (Equiv.sumArrowEquivProdArrow
          (σ ⊕ (Σ i, κ i × κ i)) (τ ⊕ (Σ j, κ' j × κ' j)) K ⁻¹'
          (affinePiProjectorCoords '' S).graphOn
            (Function.extend affinePiProjectorCoords (affinePiProjectorCoords ∘ f) 0)) =
      affinePiProjectorCoords ''
        (prodAffineMultiprojectiveEquiv σ τ κ κ' K ⁻¹' S.graphOn f) := by
  let _ : ∀ k : ι ⊕ ι', Fintype (Sum.elim κ κ' k) := Sum.rec hκ hκ'
  ext w
  rw [mem_preimage, mem_preimage_sumArrowEquivProdArrow_graphOn]
  simp only [mem_image]
  constructor
  · rintro ⟨⟨x, hxS, hwx⟩, hfy⟩
    rw [← hwx, affinePiProjectorCoords_injective.extend_apply, Function.comp_apply] at hfy
    refine ⟨(prodAffineMultiprojectiveEquiv σ τ κ κ' K).symm (x, f x), by simp [hxS], ?_⟩
    have hkey := affinePiProjectorCoords_prodAffineMultiprojectiveEquiv_symm x (f x)
    rw [hwx, hfy] at hkey
    have hsum : Sum.elim ((w ∘ (graphProjectorIndexEquiv σ τ κ κ').symm) ∘ Sum.inl)
        ((w ∘ (graphProjectorIndexEquiv σ τ κ κ').symm) ∘ Sum.inr) =
        w ∘ (graphProjectorIndexEquiv σ τ κ κ').symm := by ext (a | b) <;> rfl
    simpa [Function.comp_def] using congrArg (· ∘ graphProjectorIndexEquiv σ τ κ κ')
      (hkey.trans hsum)
  · rintro ⟨z, hz, rfl⟩
    rcases mem_graphOn.1 hz with ⟨hxS, hfz⟩
    let xy := prodAffineMultiprojectiveEquiv σ τ κ κ' K z
    have hkey : affinePiProjectorCoords z ∘ (graphProjectorIndexEquiv σ τ κ κ').symm =
        Sum.elim (affinePiProjectorCoords xy.1) (affinePiProjectorCoords xy.2) := by
      simpa only [Prod.mk.eta, Equiv.symm_apply_apply, xy] using
        affinePiProjectorCoords_prodAffineMultiprojectiveEquiv_symm xy.1 xy.2
    have hinl :
        (affinePiProjectorCoords z ∘ (graphProjectorIndexEquiv σ τ κ κ').symm) ∘ Sum.inl =
          affinePiProjectorCoords xy.1 := by
      rw [hkey]; ext a; rfl
    have hinr :
        (affinePiProjectorCoords z ∘ (graphProjectorIndexEquiv σ τ κ κ').symm) ∘ Sum.inr =
          affinePiProjectorCoords xy.2 := by
      rw [hkey]; ext b; rfl
    refine ⟨⟨xy.1, hxS, hinl.symm⟩, ?_⟩
    rw [hinl, hinr, affinePiProjectorCoords_injective.extend_apply, Function.comp_apply, hfz]

/-- **Embedded characterization of mixed semialgebraic maps.** Over any ordered field, `f` is
affine-multiprojective semialgebraic on `S` if and only if the transported map
`Function.extend affinePiProjectorCoords (affinePiProjectorCoords ∘ f) 0` is semialgebraic on
`affinePiProjectorCoords '' S`. -/
theorem isAffineMultiprojectiveSemialgebraicOn_iff_isSemialgebraicOn_extend
    [Finite ι] [Finite ι']
    {f : (σ → K) × ((i : ι) → ℙ K (κ i → K)) →
         (τ → K) × ((j : ι') → ℙ K (κ' j → K))}
    {S : Set ((σ → K) × ((i : ι) → ℙ K (κ i → K)))} :
    IsAffineMultiprojectiveSemialgebraicOn f S ↔
      IsSemialgebraicOn
        (Function.extend affinePiProjectorCoords (affinePiProjectorCoords ∘ f) 0)
        (affinePiProjectorCoords '' S) := by
  let _ : ∀ k : ι ⊕ ι', Fintype (Sum.elim κ κ' k) := Sum.rec hκ hκ'
  have : Finite (ι ⊕ ι') := inferInstance
  rw [isAffineMultiprojectiveSemialgebraicOn_def, isSemialgebraicOn_def,
    isAffineMultiprojectiveSemialgebraic_iff_isSemialgebraic_image_affinePiProjectorCoords,
    isAffineMultiprojectiveSemialgebraic_iff_isSemialgebraic_image_affinePiProjectorCoords,
    ← image_affinePiProjectorCoords_graphOn_eq]
  refine and_congr_right fun _ ↦ ⟨fun h ↦ ?_, fun h ↦ h.preimage_comp _⟩
  convert h.preimage_comp (graphProjectorIndexEquiv σ τ κ κ') using 1
  ext u
  have hu : (u ∘ graphProjectorIndexEquiv σ τ κ κ') ∘
      (graphProjectorIndexEquiv σ τ κ κ').symm = u := by ext a; simp
  simp [mem_preimage, hu]

end ExtendCharacterization

section ProjectionClosure

variable {σ τ ι ι' : Type*}
  {κ : ι → Type v} {κ' : ι' → Type v}
  [Finite ι] [∀ i, Finite (κ i)]
  [Finite ι'] [∀ j, Finite (κ' j)]
  {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [HasSemialgebraicProjections K]

/-- When the output affine coordinate set `τ` is also finite, `f` is affine-multiprojective
semialgebraic on `S` if and only if its graph over `S` is affine-multiprojective semialgebraic. -/
theorem isAffineMultiprojectiveSemialgebraicOn_iff_graph [Finite τ]
    {f : (σ → K) × ((i : ι) → ℙ K (κ i → K)) →
         (τ → K) × ((j : ι') → ℙ K (κ' j → K))}
    {S : Set ((σ → K) × ((i : ι) → ℙ K (κ i → K)))} :
    IsAffineMultiprojectiveSemialgebraicOn f S ↔
      IsAffineMultiprojectiveSemialgebraic
        (prodAffineMultiprojectiveEquiv σ τ κ κ' K ⁻¹' S.graphOn f) := by
  let hκ : ∀ i, Fintype (κ i) := fun i ↦ Fintype.ofFinite (κ i)
  let hκ' : ∀ j, Fintype (κ' j) := fun j ↦ Fintype.ofFinite (κ' j)
  let _ : ∀ k : ι ⊕ ι', Fintype (Sum.elim κ κ' k) := Sum.rec hκ hκ'
  have : Finite (ι ⊕ ι') := inferInstance
  have : Finite (τ ⊕ (Σ j, κ' j × κ' j)) := inferInstance
  rw [isAffineMultiprojectiveSemialgebraicOn_iff_isSemialgebraicOn_extend,
    isSemialgebraicOn_iff_graph,
    isAffineMultiprojectiveSemialgebraic_iff_isSemialgebraic_image_affinePiProjectorCoords,
    ← image_affinePiProjectorCoords_graphOn_eq]
  refine ⟨fun h ↦ h.preimage_comp _, fun h ↦ ?_⟩
  convert h.preimage_comp (graphProjectorIndexEquiv σ τ κ κ') using 1
  ext u
  have hu : (u ∘ graphProjectorIndexEquiv σ τ κ κ') ∘
      (graphProjectorIndexEquiv σ τ κ κ').symm = u := by ext a; simp
  simp [mem_preimage, hu]

/-- **Image of a mixed semialgebraic set under a mixed semialgebraic map.** When the input affine
coordinate set `σ` is finite, `f '' S` is affine-multiprojective semialgebraic. -/
theorem IsAffineMultiprojectiveSemialgebraicOn.isAffineMultiprojectiveSemialgebraic_image
    [Finite σ]
    {f : (σ → K) × ((i : ι) → ℙ K (κ i → K)) →
         (τ → K) × ((j : ι') → ℙ K (κ' j → K))}
    {S : Set ((σ → K) × ((i : ι) → ℙ K (κ i → K)))}
    (hf : IsAffineMultiprojectiveSemialgebraicOn f S) :
    IsAffineMultiprojectiveSemialgebraic (f '' S) := by
  let _ : ∀ i, Fintype (κ i) := fun i ↦ Fintype.ofFinite (κ i)
  let _ : ∀ j, Fintype (κ' j) := fun j ↦ Fintype.ofFinite (κ' j)
  have : Finite (σ ⊕ (Σ i, κ i × κ i)) := inferInstance
  have hf' := isAffineMultiprojectiveSemialgebraicOn_iff_isSemialgebraicOn_extend.1 hf
  rw [isAffineMultiprojectiveSemialgebraic_iff_isSemialgebraic_image_affinePiProjectorCoords]
  convert hf'.isSemialgebraic_image using 1
  ext z
  simp only [mem_image, exists_exists_and_eq_and, affinePiProjectorCoords_injective.extend_apply,
    Function.comp_apply]

theorem IsAffineMultiprojectiveSemialgebraicMap.isAffineMultiprojectiveSemialgebraic_image
    [Finite σ]
    {f : (σ → K) × ((i : ι) → ℙ K (κ i → K)) →
         (τ → K) × ((j : ι') → ℙ K (κ' j → K))}
    (hf : IsAffineMultiprojectiveSemialgebraicMap f)
    {S : Set ((σ → K) × ((i : ι) → ℙ K (κ i → K)))}
    (hS : IsAffineMultiprojectiveSemialgebraic S) :
    IsAffineMultiprojectiveSemialgebraic (f '' S) :=
  (hf.isAffineMultiprojectiveSemialgebraicOn hS).isAffineMultiprojectiveSemialgebraic_image

/-- **Preimage of a mixed semialgebraic set under a mixed semialgebraic map.** When the output
affine coordinate set `τ` is finite, `S ∩ f ⁻¹' T` is affine-multiprojective semialgebraic. -/
theorem IsAffineMultiprojectiveSemialgebraicOn.isAffineMultiprojectiveSemialgebraic_inter_preimage
    [Finite τ]
    {f : (σ → K) × ((i : ι) → ℙ K (κ i → K)) →
         (τ → K) × ((j : ι') → ℙ K (κ' j → K))}
    {S : Set ((σ → K) × ((i : ι) → ℙ K (κ i → K)))}
    (hf : IsAffineMultiprojectiveSemialgebraicOn f S)
    {T : Set ((τ → K) × ((j : ι') → ℙ K (κ' j → K)))}
    (hT : IsAffineMultiprojectiveSemialgebraic T) :
    IsAffineMultiprojectiveSemialgebraic (S ∩ f ⁻¹' T) := by
  let _ : ∀ i, Fintype (κ i) := fun i ↦ Fintype.ofFinite (κ i)
  let _ : ∀ j, Fintype (κ' j) := fun j ↦ Fintype.ofFinite (κ' j)
  have : Finite (τ ⊕ (Σ j, κ' j × κ' j)) := inferInstance
  have hf' := isAffineMultiprojectiveSemialgebraicOn_iff_isSemialgebraicOn_extend.1 hf
  have hT' :=
    isAffineMultiprojectiveSemialgebraic_iff_isSemialgebraic_image_affinePiProjectorCoords.1 hT
  rw [isAffineMultiprojectiveSemialgebraic_iff_isSemialgebraic_image_affinePiProjectorCoords]
  convert hf'.isSemialgebraic_inter_preimage hT' using 1
  ext z
  simp only [mem_image, mem_inter_iff, mem_preimage]
  constructor
  · rintro ⟨x, ⟨hxS, hfxT⟩, rfl⟩
    refine ⟨⟨x, hxS, rfl⟩, ?_⟩
    rw [affinePiProjectorCoords_injective.extend_apply]
    exact ⟨f x, hfxT, rfl⟩
  · rintro ⟨⟨x, hxS, rfl⟩, y, hyT, hfy⟩
    rw [affinePiProjectorCoords_injective.extend_apply, Function.comp_apply] at hfy
    exact ⟨x, ⟨hxS, affinePiProjectorCoords_injective hfy.symm ▸ hyT⟩, rfl⟩

theorem IsAffineMultiprojectiveSemialgebraicMap.isAffineMultiprojectiveSemialgebraic_preimage
    [Finite τ]
    {f : (σ → K) × ((i : ι) → ℙ K (κ i → K)) →
         (τ → K) × ((j : ι') → ℙ K (κ' j → K))}
    (hf : IsAffineMultiprojectiveSemialgebraicMap f)
    {T : Set ((τ → K) × ((j : ι') → ℙ K (κ' j → K)))}
    (hT : IsAffineMultiprojectiveSemialgebraic T) :
    IsAffineMultiprojectiveSemialgebraic (f ⁻¹' T) := by
  simpa using hf.isAffineMultiprojectiveSemialgebraic_inter_preimage hT

/-- **Composition of mixed semialgebraic maps.** When the intermediate affine coordinate set `τ` is
finite, `g ∘ f` is affine-multiprojective semialgebraic on `S`. -/
theorem IsAffineMultiprojectiveSemialgebraicOn.comp
    {υ ι'' : Type*} {κ'' : ι'' → Type v}
    [Finite τ] [Finite ι''] [∀ k, Finite (κ'' k)]
    {g : (τ → K) × ((j : ι') → ℙ K (κ' j → K)) →
         (υ → K) × ((k : ι'') → ℙ K (κ'' k → K))}
    {f : (σ → K) × ((i : ι) → ℙ K (κ i → K)) →
         (τ → K) × ((j : ι') → ℙ K (κ' j → K))}
    {S : Set ((σ → K) × ((i : ι) → ℙ K (κ i → K)))}
    {T : Set ((τ → K) × ((j : ι') → ℙ K (κ' j → K)))}
    (hg : IsAffineMultiprojectiveSemialgebraicOn g T)
    (hf : IsAffineMultiprojectiveSemialgebraicOn f S) (hST : MapsTo f S T) :
    IsAffineMultiprojectiveSemialgebraicOn (g ∘ f) S := by
  let _ : ∀ i, Fintype (κ i) := fun i ↦ Fintype.ofFinite (κ i)
  let _ : ∀ j, Fintype (κ' j) := fun j ↦ Fintype.ofFinite (κ' j)
  let _ : ∀ k, Fintype (κ'' k) := fun k ↦ Fintype.ofFinite (κ'' k)
  have : Finite (τ ⊕ (Σ j, κ' j × κ' j)) := inferInstance
  have hf' := isAffineMultiprojectiveSemialgebraicOn_iff_isSemialgebraicOn_extend.1 hf
  have hg' := isAffineMultiprojectiveSemialgebraicOn_iff_isSemialgebraicOn_extend.1 hg
  refine isAffineMultiprojectiveSemialgebraicOn_iff_isSemialgebraicOn_extend.2 ?_
  have hmaps : MapsTo
      (Function.extend affinePiProjectorCoords (affinePiProjectorCoords ∘ f) 0)
      (affinePiProjectorCoords '' S) (affinePiProjectorCoords '' T) := by
    rintro _ ⟨x, hxS, rfl⟩
    rw [affinePiProjectorCoords_injective.extend_apply]
    exact ⟨f x, hST hxS, rfl⟩
  refine (hg'.comp hf' hmaps).congr ?_
  rintro _ ⟨x, _, rfl⟩
  simp [Function.comp_apply, affinePiProjectorCoords_injective.extend_apply]

theorem IsAffineMultiprojectiveSemialgebraicMap.comp
    {υ ι'' : Type*} {κ'' : ι'' → Type v}
    [Finite τ] [Finite ι''] [∀ k, Finite (κ'' k)]
    {g : (τ → K) × ((j : ι') → ℙ K (κ' j → K)) →
         (υ → K) × ((k : ι'') → ℙ K (κ'' k → K))}
    {f : (σ → K) × ((i : ι) → ℙ K (κ i → K)) →
         (τ → K) × ((j : ι') → ℙ K (κ' j → K))}
    (hg : IsAffineMultiprojectiveSemialgebraicMap g)
    (hf : IsAffineMultiprojectiveSemialgebraicMap f) :
    IsAffineMultiprojectiveSemialgebraicMap (g ∘ f) :=
  IsAffineMultiprojectiveSemialgebraicOn.comp hg hf (mapsTo_univ f _)

/-- **Left inverse of a mixed semialgebraic map.** If `f` is affine-multiprojective semialgebraic
on `S` (with finite `σ`) and `g` is a left inverse of `f` on `S`, then `g` is
affine-multiprojective semialgebraic on `f '' S`. -/
theorem IsAffineMultiprojectiveSemialgebraicOn.of_leftInvOn [Finite σ]
    {f : (σ → K) × ((i : ι) → ℙ K (κ i → K)) →
         (τ → K) × ((j : ι') → ℙ K (κ' j → K))}
    {g : (τ → K) × ((j : ι') → ℙ K (κ' j → K)) →
         (σ → K) × ((i : ι) → ℙ K (κ i → K))}
    {S : Set ((σ → K) × ((i : ι) → ℙ K (κ i → K)))}
    (hf : IsAffineMultiprojectiveSemialgebraicOn f S) (hgf : LeftInvOn g f S) :
    IsAffineMultiprojectiveSemialgebraicOn g (f '' S) := by
  refine ⟨hf.isAffineMultiprojectiveSemialgebraic_image, ?_⟩
  have hswap : (f '' S).graphOn g = Prod.swap ⁻¹' S.graphOn f := by
    ext ⟨y, x⟩
    simp only [mem_graphOn, mem_image, mem_preimage, Prod.swap]
    constructor
    · rintro ⟨⟨x', hx'S, rfl⟩, rfl⟩
      rw [hgf hx'S]
      exact ⟨hx'S, rfl⟩
    · rintro ⟨hxS, rfl⟩
      exact ⟨⟨x, hxS, rfl⟩, hgf hxS⟩
  rw [hswap]
  exact hf.graph.prod_swap

end ProjectionClosure

end MixedMaps

/-! ### Pure multiprojective semialgebraic maps and maps from affine domains -/

section PureMultiprojectiveMaps

variable {ι ι' : Type*} {κ : ι → Type v} {κ' : ι' → Type v}
  {K : Type*} [Field K] [LinearOrder K]

/-- A map between multiprojective spaces is *multiprojective semialgebraic on `S`* if both `S` and
its graph `S.graphOn f` (viewed in the `Sum`-indexed multiprojective space) are multiprojective
semialgebraic. No continuity is assumed. -/
def IsMultiprojectiveSemialgebraicOn
    (f : ((i : ι) → ℙ K (κ i → K)) → ((j : ι') → ℙ K (κ' j → K)))
    (S : Set ((i : ι) → ℙ K (κ i → K))) : Prop :=
  IsMultiprojectiveSemialgebraic S ∧
    IsMultiprojectiveSemialgebraic
      (Equiv.sumPiEquivProdPi (fun k ↦ ℙ K (Sum.elim κ κ' k → K)) ⁻¹' S.graphOn f)

/-- A map between multiprojective spaces is *multiprojective semialgebraic* if it is
multiprojective semialgebraic on `univ`. -/
def IsMultiprojectiveSemialgebraicMap
    (f : ((i : ι) → ℙ K (κ i → K)) → ((j : ι') → ℙ K (κ' j → K))) : Prop :=
  IsMultiprojectiveSemialgebraicOn f univ

@[simp]
theorem isMultiprojectiveSemialgebraicOn_univ
    {f : ((i : ι) → ℙ K (κ i → K)) → ((j : ι') → ℙ K (κ' j → K))} :
    IsMultiprojectiveSemialgebraicOn f univ ↔ IsMultiprojectiveSemialgebraicMap f :=
  Iff.rfl

theorem isMultiprojectiveSemialgebraicOn_def
    {f : ((i : ι) → ℙ K (κ i → K)) → ((j : ι') → ℙ K (κ' j → K))}
    {S : Set ((i : ι) → ℙ K (κ i → K))} :
    IsMultiprojectiveSemialgebraicOn f S ↔
      IsMultiprojectiveSemialgebraic S ∧
        IsMultiprojectiveSemialgebraic
          (Equiv.sumPiEquivProdPi (fun k ↦ ℙ K (Sum.elim κ κ' k → K)) ⁻¹' S.graphOn f) :=
  Iff.rfl

theorem IsMultiprojectiveSemialgebraicOn.isMultiprojectiveSemialgebraic
    {f : ((i : ι) → ℙ K (κ i → K)) → ((j : ι') → ℙ K (κ' j → K))}
    {S : Set ((i : ι) → ℙ K (κ i → K))}
    (hf : IsMultiprojectiveSemialgebraicOn f S) :
    IsMultiprojectiveSemialgebraic S :=
  hf.1

theorem IsMultiprojectiveSemialgebraicOn.graph
    {f : ((i : ι) → ℙ K (κ i → K)) → ((j : ι') → ℙ K (κ' j → K))}
    {S : Set ((i : ι) → ℙ K (κ i → K))}
    (hf : IsMultiprojectiveSemialgebraicOn f S) :
    IsMultiprojectiveSemialgebraic
      (Equiv.sumPiEquivProdPi (fun k ↦ ℙ K (Sum.elim κ κ' k → K)) ⁻¹' S.graphOn f) :=
  hf.2

@[simp]
theorem isMultiprojectiveSemialgebraicOn_empty
    (f : ((i : ι) → ℙ K (κ i → K)) → ((j : ι') → ℙ K (κ' j → K))) :
    IsMultiprojectiveSemialgebraicOn f ∅ :=
  ⟨isMultiprojectiveSemialgebraic_empty,
    (Set.graphOn_empty f).symm ▸ isMultiprojectiveSemialgebraic_empty⟩

/-- Pure multiprojective semialgebraic maps are the `Empty`-affine specialization of mixed
affine-multiprojective semialgebraic maps. -/
theorem isMultiprojectiveSemialgebraicOn_iff_isAffineMultiprojectiveSemialgebraicOn
    {f : ((i : ι) → ℙ K (κ i → K)) → ((j : ι') → ℙ K (κ' j → K))}
    {S : Set ((i : ι) → ℙ K (κ i → K))} :
    IsMultiprojectiveSemialgebraicOn f S ↔
      IsAffineMultiprojectiveSemialgebraicOn
        (fun x : (Empty → K) × ((i : ι) → ℙ K (κ i → K)) ↦ ((0 : Empty → K), f x.2))
        ((Prod.snd : (Empty → K) × ((i : ι) → ℙ K (κ i → K)) → _) ⁻¹' S) := by
  have hgr : prodAffineMultiprojectiveEquiv Empty Empty κ κ' K ⁻¹'
        ((Prod.snd : (Empty → K) × ((i : ι) → ℙ K (κ i → K)) → _) ⁻¹' S).graphOn
          (fun x : (Empty → K) × ((i : ι) → ℙ K (κ i → K)) ↦ ((0 : Empty → K), f x.2)) =
      (Prod.snd : (Empty ⊕ Empty → K) × _ → _) ⁻¹'
        (Equiv.sumPiEquivProdPi (fun k ↦ ℙ K (Sum.elim κ κ' k → K)) ⁻¹' S.graphOn f) := by
    ext ⟨u, p⟩
    constructor
    · intro h
      rcases mem_graphOn.1 (mem_preimage.1 h) with ⟨hpS, hfp⟩
      rw [prodAffineMultiprojectiveEquiv_apply] at hpS hfp
      exact mem_preimage.2 (mem_preimage.2 (mem_graphOn.2 ⟨hpS, congrArg Prod.snd hfp⟩))
    · intro h
      rcases mem_graphOn.1 (mem_preimage.1 (mem_preimage.1 h)) with ⟨hpS, hfp⟩
      refine mem_preimage.2 (mem_graphOn.2 ?_)
      rw [prodAffineMultiprojectiveEquiv_apply]
      exact ⟨hpS, Prod.ext (Subsingleton.elim _ _) hfp⟩
  rw [IsMultiprojectiveSemialgebraicOn, isAffineMultiprojectiveSemialgebraicOn_def, hgr,
    isAffineMultiprojectiveSemialgebraic_preimage_snd_iff,
    isAffineMultiprojectiveSemialgebraic_preimage_snd_iff]

/-- Restriction of a multiprojective semialgebraic map to a multiprojective semialgebraic subset. -/
theorem IsMultiprojectiveSemialgebraicOn.mono [Finite ι'] [∀ j, Finite (κ' j)]
    {f : ((i : ι) → ℙ K (κ i → K)) → ((j : ι') → ℙ K (κ' j → K))}
    {S T : Set ((i : ι) → ℙ K (κ i → K))}
    (hf : IsMultiprojectiveSemialgebraicOn f S)
    (hT : IsMultiprojectiveSemialgebraic T) (hTS : T ⊆ S) :
    IsMultiprojectiveSemialgebraicOn f T := by
  rw [isMultiprojectiveSemialgebraicOn_iff_isAffineMultiprojectiveSemialgebraicOn] at hf ⊢
  exact hf.mono (isAffineMultiprojectiveSemialgebraic_preimage_snd_iff.2 hT)
    (preimage_mono hTS)

/-- A globally multiprojective semialgebraic map is multiprojective semialgebraic on every
multiprojective semialgebraic subset. -/
theorem IsMultiprojectiveSemialgebraicMap.isMultiprojectiveSemialgebraicOn
    [Finite ι'] [∀ j, Finite (κ' j)]
    {f : ((i : ι) → ℙ K (κ i → K)) → ((j : ι') → ℙ K (κ' j → K))}
    (hf : IsMultiprojectiveSemialgebraicMap f)
    {S : Set ((i : ι) → ℙ K (κ i → K))} (hS : IsMultiprojectiveSemialgebraic S) :
    IsMultiprojectiveSemialgebraicOn f S :=
  hf.mono hS (subset_univ S)

/-- Congruence of `IsMultiprojectiveSemialgebraicOn` under `Set.EqOn`. -/
theorem IsMultiprojectiveSemialgebraicOn.congr
    {f g : ((i : ι) → ℙ K (κ i → K)) → ((j : ι') → ℙ K (κ' j → K))}
    {S : Set ((i : ι) → ℙ K (κ i → K))}
    (hf : IsMultiprojectiveSemialgebraicOn f S) (h : S.EqOn f g) :
    IsMultiprojectiveSemialgebraicOn g S :=
  ⟨hf.1, Set.graphOn_inj.2 h ▸ hf.2⟩

/-- A constant map on a multiprojective semialgebraic set into a finite-coordinate multiprojective
space is multiprojective semialgebraic on that set. -/
theorem isMultiprojectiveSemialgebraicOn_const [Finite ι'] [∀ j, Finite (κ' j)]
    (c : (j : ι') → ℙ K (κ' j → K)) {S : Set ((i : ι) → ℙ K (κ i → K))}
    (hS : IsMultiprojectiveSemialgebraic S) :
    IsMultiprojectiveSemialgebraicOn (fun _ ↦ c) S := by
  rw [isMultiprojectiveSemialgebraicOn_iff_isAffineMultiprojectiveSemialgebraicOn]
  exact isAffineMultiprojectiveSemialgebraicOn_const ((0 : Empty → K), c)
    (isAffineMultiprojectiveSemialgebraic_preimage_snd_iff.2 hS)

/-- A constant map between finite-coordinate multiprojective spaces is multiprojective
semialgebraic. -/
theorem isMultiprojectiveSemialgebraicMap_const
    [Finite ι] [∀ i, Finite (κ i)] [Finite ι'] [∀ j, Finite (κ' j)]
    (c : (j : ι') → ℙ K (κ' j → K)) :
    IsMultiprojectiveSemialgebraicMap (fun _ : (i : ι) → ℙ K (κ i → K) ↦ c) :=
  isMultiprojectiveSemialgebraicOn_const c isMultiprojectiveSemialgebraic_univ

/-- The identity map on a finite-coordinate multiprojective space is multiprojective
semialgebraic. -/
@[simp]
theorem isMultiprojectiveSemialgebraicMap_id [Finite ι] [∀ i, Finite (κ i)] :
    IsMultiprojectiveSemialgebraicMap
      (id : ((i : ι) → ℙ K (κ i → K)) → ((i : ι) → ℙ K (κ i → K))) := by
  refine ⟨isMultiprojectiveSemialgebraic_univ, ?_⟩
  have h : (univ : Set ((i : ι) → ℙ K (κ i → K))).graphOn id =
      diagonal ((i : ι) → ℙ K (κ i → K)) := by
    ext ⟨p, q⟩
    simp [mem_diagonal_iff]
  exact h.symm ▸ isMultiprojectiveSemialgebraic_diagonal

omit [LinearOrder K] in
private theorem image_zero_prod_preimage_snd
    (f : ((i : ι) → ℙ K (κ i → K)) → ((j : ι') → ℙ K (κ' j → K)))
    (S : Set ((i : ι) → ℙ K (κ i → K))) :
    (fun x : (Empty → K) × ((i : ι) → ℙ K (κ i → K)) ↦ ((0 : Empty → K), f x.2)) ''
        ((Prod.snd : (Empty → K) × ((i : ι) → ℙ K (κ i → K)) → _) ⁻¹' S) =
      (Prod.snd : (Empty → K) × ((j : ι') → ℙ K (κ' j → K)) → _) ⁻¹' (f '' S) := by
  ext ⟨_, q⟩
  simp only [mem_image, mem_preimage, Prod.exists, Prod.mk.injEq]
  exact ⟨fun ⟨_, p, hpS, _, hfp⟩ ↦ ⟨p, hpS, hfp⟩,
    fun ⟨p, hpS, hfp⟩ ↦ ⟨0, p, hpS, Subsingleton.elim _ _, hfp⟩⟩

section ProjectionClosure

variable [Finite ι] [∀ i, Finite (κ i)] [Finite ι'] [∀ j, Finite (κ' j)]
  [IsStrictOrderedRing K] [HasSemialgebraicProjections K]

/-- Image of a multiprojective semialgebraic set under a multiprojective semialgebraic map. -/
theorem IsMultiprojectiveSemialgebraicOn.isMultiprojectiveSemialgebraic_image
    {f : ((i : ι) → ℙ K (κ i → K)) → ((j : ι') → ℙ K (κ' j → K))}
    {S : Set ((i : ι) → ℙ K (κ i → K))}
    (hf : IsMultiprojectiveSemialgebraicOn f S) :
    IsMultiprojectiveSemialgebraic (f '' S) := by
  have hf' := isMultiprojectiveSemialgebraicOn_iff_isAffineMultiprojectiveSemialgebraicOn.1 hf
  have himg := hf'.isAffineMultiprojectiveSemialgebraic_image
  rw [image_zero_prod_preimage_snd, isAffineMultiprojectiveSemialgebraic_preimage_snd_iff] at himg
  exact himg

/-- Image of a multiprojective semialgebraic set under a globally multiprojective semialgebraic
map. -/
theorem IsMultiprojectiveSemialgebraicMap.isMultiprojectiveSemialgebraic_image
    {f : ((i : ι) → ℙ K (κ i → K)) → ((j : ι') → ℙ K (κ' j → K))}
    (hf : IsMultiprojectiveSemialgebraicMap f)
    {S : Set ((i : ι) → ℙ K (κ i → K))} (hS : IsMultiprojectiveSemialgebraic S) :
    IsMultiprojectiveSemialgebraic (f '' S) :=
  (hf.isMultiprojectiveSemialgebraicOn hS).isMultiprojectiveSemialgebraic_image

/-- Preimage in `S` of a multiprojective semialgebraic set under a map multiprojective
semialgebraic on `S`. -/
theorem IsMultiprojectiveSemialgebraicOn.isMultiprojectiveSemialgebraic_inter_preimage
    {f : ((i : ι) → ℙ K (κ i → K)) → ((j : ι') → ℙ K (κ' j → K))}
    {S : Set ((i : ι) → ℙ K (κ i → K))}
    (hf : IsMultiprojectiveSemialgebraicOn f S)
    {T : Set ((j : ι') → ℙ K (κ' j → K))}
    (hT : IsMultiprojectiveSemialgebraic T) :
    IsMultiprojectiveSemialgebraic (S ∩ f ⁻¹' T) := by
  have hf' := isMultiprojectiveSemialgebraicOn_iff_isAffineMultiprojectiveSemialgebraicOn.1 hf
  have hpre := hf'.isAffineMultiprojectiveSemialgebraic_inter_preimage
    (isAffineMultiprojectiveSemialgebraic_preimage_snd_iff.2 hT)
  have heq :
      ((Prod.snd : (Empty → K) × ((i : ι) → ℙ K (κ i → K)) → _) ⁻¹' S) ∩
        (fun x : (Empty → K) × ((i : ι) → ℙ K (κ i → K)) ↦ ((0 : Empty → K), f x.2)) ⁻¹'
          ((Prod.snd : (Empty → K) × ((j : ι') → ℙ K (κ' j → K)) → _) ⁻¹' T) =
      (Prod.snd : (Empty → K) × ((i : ι) → ℙ K (κ i → K)) → _) ⁻¹' (S ∩ f ⁻¹' T) := by
    ext ⟨_, p⟩
    simp
  rw [heq, isAffineMultiprojectiveSemialgebraic_preimage_snd_iff] at hpre
  exact hpre

/-- Preimage of a multiprojective semialgebraic set under a globally multiprojective semialgebraic
map. -/
theorem IsMultiprojectiveSemialgebraicMap.isMultiprojectiveSemialgebraic_preimage
    {f : ((i : ι) → ℙ K (κ i → K)) → ((j : ι') → ℙ K (κ' j → K))}
    (hf : IsMultiprojectiveSemialgebraicMap f)
    {T : Set ((j : ι') → ℙ K (κ' j → K))} (hT : IsMultiprojectiveSemialgebraic T) :
    IsMultiprojectiveSemialgebraic (f ⁻¹' T) := by
  simpa using hf.isMultiprojectiveSemialgebraic_inter_preimage hT

/-- Composition of multiprojective semialgebraic maps on subsets. -/
theorem IsMultiprojectiveSemialgebraicOn.comp
    {ι'' : Type*} {κ'' : ι'' → Type v} [Finite ι''] [∀ k, Finite (κ'' k)]
    {g : ((j : ι') → ℙ K (κ' j → K)) → ((k : ι'') → ℙ K (κ'' k → K))}
    {f : ((i : ι) → ℙ K (κ i → K)) → ((j : ι') → ℙ K (κ' j → K))}
    {S : Set ((i : ι) → ℙ K (κ i → K))} {T : Set ((j : ι') → ℙ K (κ' j → K))}
    (hg : IsMultiprojectiveSemialgebraicOn g T)
    (hf : IsMultiprojectiveSemialgebraicOn f S) (hST : MapsTo f S T) :
    IsMultiprojectiveSemialgebraicOn (g ∘ f) S := by
  rw [isMultiprojectiveSemialgebraicOn_iff_isAffineMultiprojectiveSemialgebraicOn] at hg hf ⊢
  exact hg.comp hf fun (x : (Empty → K) × ((i : ι) → ℙ K (κ i → K))) hx ↦ hST hx

/-- Composition of globally multiprojective semialgebraic maps. -/
theorem IsMultiprojectiveSemialgebraicMap.comp
    {ι'' : Type*} {κ'' : ι'' → Type v} [Finite ι''] [∀ k, Finite (κ'' k)]
    {g : ((j : ι') → ℙ K (κ' j → K)) → ((k : ι'') → ℙ K (κ'' k → K))}
    {f : ((i : ι) → ℙ K (κ i → K)) → ((j : ι') → ℙ K (κ' j → K))}
    (hg : IsMultiprojectiveSemialgebraicMap g) (hf : IsMultiprojectiveSemialgebraicMap f) :
    IsMultiprojectiveSemialgebraicMap (g ∘ f) :=
  IsMultiprojectiveSemialgebraicOn.comp hg hf (mapsTo_univ f _)

/-- A left inverse on `S` of a map multiprojective semialgebraic on `S` is multiprojective
semialgebraic on `f '' S`. -/
theorem IsMultiprojectiveSemialgebraicOn.of_leftInvOn
    {f : ((i : ι) → ℙ K (κ i → K)) → ((j : ι') → ℙ K (κ' j → K))}
    {g : ((j : ι') → ℙ K (κ' j → K)) → ((i : ι) → ℙ K (κ i → K))}
    {S : Set ((i : ι) → ℙ K (κ i → K))}
    (hf : IsMultiprojectiveSemialgebraicOn f S) (hgf : LeftInvOn g f S) :
    IsMultiprojectiveSemialgebraicOn g (f '' S) := by
  have hf' := isMultiprojectiveSemialgebraicOn_iff_isAffineMultiprojectiveSemialgebraicOn.1 hf
  have hleft : LeftInvOn
      (fun y : (Empty → K) × ((j : ι') → ℙ K (κ' j → K)) ↦ ((0 : Empty → K), g y.2))
      (fun x : (Empty → K) × ((i : ι) → ℙ K (κ i → K)) ↦ ((0 : Empty → K), f x.2))
      ((Prod.snd : (Empty → K) × ((i : ι) → ℙ K (κ i → K)) → _) ⁻¹' S) :=
    fun ⟨_, p⟩ hp ↦ Prod.ext (Subsingleton.elim _ _) (hgf hp)
  have hg' := hf'.of_leftInvOn hleft
  rw [image_zero_prod_preimage_snd] at hg'
  exact isMultiprojectiveSemialgebraicOn_iff_isAffineMultiprojectiveSemialgebraicOn.2 hg'

end ProjectionClosure

end PureMultiprojectiveMaps

section AffineToMultiprojective

section GraphTransport

variable {σ ι : Type*} {κ : ι → Type*} [∀ i, Fintype (κ i)] {K : Type*} [Field K]

/-- Under `affinePiProjectorCoords`, the graph `s.graphOn f` of a map `f : (σ → K) → M` over an
affine set `s ⊆ σ → K` maps onto the encoded graph of `piProjectorCoords ∘ f` over `s`. -/
theorem image_affinePiProjectorCoords_graphOn
    (f : (σ → K) → ((i : ι) → ℙ K (κ i → K))) (s : Set (σ → K)) :
    affinePiProjectorCoords '' s.graphOn f =
      Equiv.sumArrowEquivProdArrow σ (Σ i, κ i × κ i) K ⁻¹'
        s.graphOn (piProjectorCoords ∘ f) := by
  ext z
  simp only [mem_image, mem_graphOn, Prod.exists, mem_preimage_sumArrowEquivProdArrow_graphOn,
    Function.comp_apply]
  constructor
  · rintro ⟨x, _, ⟨hx, rfl⟩, rfl⟩
    simp [hx]
  · rintro ⟨hx, hfz⟩
    refine ⟨z ∘ Sum.inl, f (z ∘ Sum.inl), ⟨hx, rfl⟩, ?_⟩
    ext (a | q)
    · simp
    · simpa using congr_fun hfz q

variable [LinearOrder K] [IsStrictOrderedRing K] [Finite ι]

/-- **Projector criterion for maps from affine sets into multiprojective spaces.** Over any ordered
field, a map `f : (σ → K) → (i : ι) → ℙ K (κ i → K)` over an affine domain `s : Set (σ → K)` has
semialgebraic domain `s` and affine-multiprojective semialgebraic graph `s.graphOn f` if and only
if `piProjectorCoords ∘ f` is semialgebraic on `s`. -/
theorem isAffineMultiprojectiveSemialgebraic_graphOn_iff
    {f : (σ → K) → ((i : ι) → ℙ K (κ i → K))} {s : Set (σ → K)} :
    (IsSemialgebraic s ∧ IsAffineMultiprojectiveSemialgebraic (s.graphOn f)) ↔
      IsSemialgebraicOn (piProjectorCoords ∘ f) s := by
  rw [isSemialgebraicOn_def,
    isAffineMultiprojectiveSemialgebraic_iff_isSemialgebraic_image_affinePiProjectorCoords,
    image_affinePiProjectorCoords_graphOn]

variable [HasSemialgebraicProjections K]

/-- If `piProjectorCoords ∘ f` is semialgebraic on a finite-coordinate affine set `s`, then
`f '' s` is multiprojective semialgebraic. -/
theorem IsSemialgebraicOn.isMultiprojectiveSemialgebraic_image [Finite σ]
    {f : (σ → K) → ((i : ι) → ℙ K (κ i → K))} {s : Set (σ → K)}
    (hf : IsSemialgebraicOn (piProjectorCoords ∘ f) s) :
    IsMultiprojectiveSemialgebraic (f '' s) := by
  rw [isMultiprojectiveSemialgebraic_iff_isSemialgebraic_image_piProjectorCoords, ← image_comp]
  exact hf.isSemialgebraic_image

/-- If `piProjectorCoords ∘ f` is semialgebraic on `s`, then the preimage in `s` of every
multiprojective semialgebraic subset `T` is semialgebraic. -/
theorem IsSemialgebraicOn.isSemialgebraic_inter_preimage_multiprojective
    {f : (σ → K) → ((i : ι) → ℙ K (κ i → K))} {s : Set (σ → K)}
    (hf : IsSemialgebraicOn (piProjectorCoords ∘ f) s)
    {T : Set ((i : ι) → ℙ K (κ i → K))} (hT : IsMultiprojectiveSemialgebraic T) :
    IsSemialgebraic (s ∩ f ⁻¹' T) := by
  cases nonempty_fintype ι
  have hT' := isMultiprojectiveSemialgebraic_iff_isSemialgebraic_image_piProjectorCoords.1 hT
  have hpre : s ∩ f ⁻¹' T = s ∩ (piProjectorCoords ∘ f) ⁻¹' (piProjectorCoords '' T) := by
    ext x
    simp [piProjectorCoords_injective.mem_set_image]
  rw [hpre]
  exact hf.isSemialgebraic_inter_preimage hT'

end GraphTransport

section RightInverse

variable {ι : Type*} {κ : ι → Type*} [∀ i, Fintype (κ i)]
  {K : Type*} [Field K] [LinearOrder K]

omit [LinearOrder K] in
private theorem projector_apply_eq_one_of_forall_eq {α : Type*} [Fintype α]
    (q : ℙ K (α → K)) {a₀ : α} (ha₀ : ∀ b : α, b = a₀) :
    projector q a₀ a₀ = 1 := by
  induction q using ind with
  | h w hw =>
    have hw₀ : w a₀ ≠ 0 := by
      obtain ⟨b, hb⟩ := Function.ne_iff.1 hw
      rwa [ha₀ b] at hb
    have hsum : (∑ r : α, w r * w r) = w a₀ * w a₀ :=
      Finset.sum_eq_single a₀ (fun b _ hb ↦ (hb (ha₀ b)).elim)
        (fun h ↦ (h (Finset.mem_univ a₀)).elim)
    rw [projector_mk, rankOneProjector_apply, dotProduct, hsum,
      div_self (mul_ne_zero hw₀ hw₀)]

private theorem eq_empty_of_infinite_of_rightInvOn [Infinite ι]
    {τ : ((Σ i, κ i × κ i) → K) → ((i : ι) → ℙ K (κ i → K))}
    {s : Set ((Σ i, κ i × κ i) → K)} (hs : IsSemialgebraic s)
    (hτ : ∀ x ∈ s, piProjectorCoords (τ x) = x) :
    s = ∅ := by
  classical
  obtain ⟨F, hF⟩ := hs.exists_finset_mem_iff_of_eqOn
  obtain ⟨i₀, hi₀⟩ := Infinite.exists_notMem_finset (F.image Sigma.fst)
  have hnotMem (a b : κ i₀) : (⟨i₀, a, b⟩ : Σ i, κ i × κ i) ∉ F :=
    fun h ↦ hi₀ (Finset.mem_image.2 ⟨⟨i₀, a, b⟩, h, rfl⟩)
  ext x
  simp only [mem_empty_iff_false, iff_false]
  intro hx
  obtain ⟨a₀, _⟩ := Function.ne_iff.1 (τ x i₀).rep_ne_zero
  by_cases hsub : ∃ b₀ : κ i₀, b₀ ≠ a₀
  · obtain ⟨b₀, hb₀⟩ := hsub
    let y := Function.update (Function.update x ⟨i₀, a₀, b₀⟩ 1) ⟨i₀, b₀, a₀⟩ 0
    have hy : y ∈ s := (hF x y fun q hq ↦ by
      have h1 : q ≠ ⟨i₀, b₀, a₀⟩ := fun h ↦ hnotMem b₀ a₀ (h ▸ hq)
      have h2 : q ≠ ⟨i₀, a₀, b₀⟩ := fun h ↦ hnotMem a₀ b₀ (h ▸ hq)
      simp [y, h1, h2]).1 hx
    have hne : (⟨i₀, a₀, b₀⟩ : Σ i, κ i × κ i) ≠ ⟨i₀, b₀, a₀⟩ := by
      simp [hb₀.symm]
    have hsymm : projector (τ y i₀) a₀ b₀ = projector (τ y i₀) b₀ a₀ := by
      induction (τ y i₀) using ind with
      | h w hw => rw [projector_mk, rankOneProjector_apply, rankOneProjector_apply, mul_comm]
    have hya : projector (τ y i₀) a₀ b₀ = 1 := by
      simpa [y, hne] using congr_fun (hτ y hy) ⟨i₀, a₀, b₀⟩
    have hyb : projector (τ y i₀) b₀ a₀ = 0 := by
      simpa [y] using congr_fun (hτ y hy) ⟨i₀, b₀, a₀⟩
    exact one_ne_zero (hya.symm.trans (hsymm.trans hyb))
  · push Not at hsub
    let y := Function.update x ⟨i₀, a₀, a₀⟩ 0
    have hy : y ∈ s := (hF x y fun q hq ↦ by
      have h1 : q ≠ ⟨i₀, a₀, a₀⟩ := fun h ↦ hnotMem a₀ a₀ (h ▸ hq)
      simp [y, h1]).1 hx
    have hy0 : projector (τ y i₀) a₀ a₀ = 0 := by
      simpa [y] using congr_fun (hτ y hy) ⟨i₀, a₀, a₀⟩
    exact one_ne_zero ((projector_apply_eq_one_of_forall_eq (τ y i₀) hsub).symm.trans hy0)

/-- **Inverse projector transport on semialgebraic subsets of the flattened product projector
locus.** Any map `τ : ((Σ i, κ i × κ i) → K) → (i : ι) → ℙ K (κ i → K)` that is a right inverse of
`piProjectorCoords` on a semialgebraic set `s` satisfies
`IsSemialgebraicOn (piProjectorCoords ∘ τ) s`, so `τ` pushes semialgebraic subsets of `s` forward to
multiprojective semialgebraic sets and pulls multiprojective semialgebraic sets back to
semialgebraic subsets of `s`. -/
theorem isSemialgebraicOn_piProjectorCoords_comp_of_rightInvOn
    {τ : ((Σ i, κ i × κ i) → K) → ((i : ι) → ℙ K (κ i → K))}
    {s : Set ((Σ i, κ i × κ i) → K)} (hs : IsSemialgebraic s)
    (hτ : ∀ x ∈ s, piProjectorCoords (τ x) = x) :
    IsSemialgebraicOn (piProjectorCoords ∘ τ) s := by
  by_cases hι : Finite ι
  · exact (isSemialgebraicMap_id.isSemialgebraicOn hs).congr fun x hx ↦ (hτ x hx).symm
  · have : Infinite ι := not_finite_iff_infinite.1 hι
    rw [eq_empty_of_infinite_of_rightInvOn hs hτ]
    exact isSemialgebraicOn_empty _

end RightInverse

end AffineToMultiprojective

end TauCeti
