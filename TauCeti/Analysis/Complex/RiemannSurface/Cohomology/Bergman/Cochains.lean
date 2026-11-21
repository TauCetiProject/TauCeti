/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.HolomorphicFunctions.Bergman.Restriction
public import TauCeti.Geometry.Manifold.Complex.StructureSheaf.Basic
public import TauCeti.Geometry.Manifold.Complex.StructureSheaf.LineBundle.Basic
public import TauCeti.Topology.VectorBundle.Trivialization
public import TauCeti.Topology.OpenPartialHomeomorph.ChartOpens
import TauCeti.Geometry.Manifold.MFDeriv.Opens
import TauCeti.Geometry.Manifold.Complex.StructureSheaf.Coordinate

/-!
# Square-integrable holomorphic Čech cochains on a Riemann surface

Let `X` be a Riemann surface with a finite family of holomorphic charts `e i` and opens
`W i ⊆ (e i).source`. A holomorphic Čech one-cochain of the cover `W` assigns to every ordered
pair `(i, j)`, repetitions allowed, a holomorphic function on `W i ∩ W j`. Reading it in the
first chart `e i` gives a holomorphic function on the plane open
`(e i).imageOpens (W i ⊓ W j) = e i (W i ∩ W j)`. The square-integrable ones form the
Bergman space of that plane open, and the finite product of these Bergman spaces is the Banach
space of square-integrable one-cochains. Zero-cochains are read in the chart of their index.

The cochain spaces and their cocycle conditions are stated for coordinates in local frames of a
line bundle: overlap scalars `g i j : X → ℂ` convert coordinates in the frame of `j` into the frame
of `i` on `W i ∩ W j`, and a component indexed by `(i, j)` is read in the frame of `i`. The
structure sheaf `𝒪` is the case `g = 1`. No regularity of `g` is needed, because all conditions
are point evaluations.

* A coordinate change need not preserve Lebesgue measure, and the hypotheses here do not guarantee
  that the Čech differential is a bounded map between the chart-read Bergman products. The cocycle
  condition is therefore stated as the vanishing of continuous point evaluations
  (`BergmanSpace.evalCLM`) on triple overlaps, which needs no such bound; `cocycles₁` is closed and
  complete.
* For a smaller family `W' i ⊆ W i` with the same charts, componentwise Bergman restriction
  (`BergmanSpace.restrictPi`, `BergmanSpace.restrictPi₂`) preserves cocycles and is a compact
  operator when every `closure (W' i)` is compact and lies in `W i`
  (`isCompactOperator_restrictCocycles₁`).
* For three nested families `W'' ≤ W' ≤ W` with the same charts, `compatibleTriples` is the space of
  `(ξ, ξ', η)`, with `ξ` and `ξ'` square-integrable cocycles on `W` and `W'` and `η` a
  square-integrable zero-cochain on `W''`, such that `ξ' = ξ + δη` on `W''`. The Čech coboundary
  converts `ηⱼ` into the frame of `i`: in chart coordinates `(δη)ᵢⱼ` is
  `g i j x * ηⱼ (e j x) - ηᵢ (e i x)`, which is `ηⱼ - ηᵢ` for `g = 1`. It is closed, hence
  complete (`isClosed_compatibleTriples`).

For the structure sheaf, these spaces are realized with its native holomorphic sections.

* `chartSection` sends a Bergman class read in a chart to the native section of the structure sheaf
  with the same values; it is complex linear and injective. `toSections₀` and `toSections₁` are the
  resulting injective realizations of cochains as families of native sections.
* For `g = 1`, membership in `cocycles₁` is the native cocycle identity of section values
  (`mem_cocycles₁_iff_toSections₁`), restriction is the native restriction of sections
  (`toSections₁_restrictCochains₁`), and membership in `compatibleTriples` is the native
  coboundary identity (`mem_compatibleTriples_iff_toSections`).

For a holomorphic line bundle with any normed rank-one model, actual holomorphic frames and
scalar model coordinates give the injective realizations `toBundleSections₀` and
`toBundleSections₁`. Their native cocycle and coboundary identities use the actual
`Bundle.Trivialization.scalarCoordChange` factors and native presheaf restrictions.
`Bundle.Trivialization.bergmanRestriction` reads a section on a larger open as a Bergman class
only after compact shrinking; `bundleSections₁ToBergman` shrinks both overlap indices. The
round trips recover restrictions. No unbounded frame change is asserted to induce a Bergman
isomorphism, and no arbitrary section is asserted to be square-integrable up to the boundary
of its original domain.


The continuous linear `middleProjection` retains the middle cocycle of a compatible triple.
`exists_representative_eq` and `exists_cocycle_representative_eq` give native Bergman
representatives with the same pointwise values after restriction to smaller opens whose
closures are compact and contained in the original holomorphic domains. `Bergman.Lifting` proves
surjectivity and uniform bounded lifting of the middle projection.
These Banach spaces and compact restrictions enter the analytic finiteness argument for `H¹`.

## References

* O. Forster, *Lectures on Riemann Surfaces*, GTM 81, §14.
* J. Wehler, *Riemann Surfaces*, lecture notes, LMU München, 2019, Chapter 7.
-/

public noncomputable section

open CategoryTheory Metric Opposite Set TopologicalSpace
open scoped ContDiff Manifold

namespace TauCeti.RiemannSurface

open OpenPartialHomeomorph (closure_imageOpens_subset imageOpens_mono isCompact_closure_imageOpens
  map_mem_imageOpens mem_imageOpens)

/-! ### Square-integrable cochains of a chart family -/

namespace ChartBergman

variable {X : Type*} [TopologicalSpace X] {ι : Type*} {e : ι → OpenPartialHomeomorph X ℂ}
  {W W' W'' : ι → Opens X}

/-- Overlaps `W i ⊓ W j` lie in the source of the first chart. -/
theorem inf_subset_source (hW : ∀ i, (W i : Set X) ⊆ (e i).source) (i j : ι) :
    ((W i ⊓ W j : Opens X) : Set X) ⊆ (e i).source :=
  fun _ hx ↦ hW i hx.1

/-- A smaller family lies in the chart sources. -/
theorem subset_source_of_le (hW : ∀ i, (W i : Set X) ⊆ (e i).source) (h : ∀ i, W' i ≤ W i)
    (i : ι) : (W' i : Set X) ⊆ (e i).source :=
  (SetLike.coe_subset_coe.2 (h i)).trans (hW i)

/-- The projection of a one-cochain to its component on the overlap `W i ⊓ W j`. -/
def proj₁ (i j : ι) :
    ((i j : ι) → bergmanSpace ℂ ((e i).imageOpens (W i ⊓ W j))) →L[ℂ]
      bergmanSpace ℂ ((e i).imageOpens (W i ⊓ W j)) :=
  (ContinuousLinearMap.proj (φ := fun j ↦ bergmanSpace ℂ ((e i).imageOpens (W i ⊓ W j))) j).comp
    (ContinuousLinearMap.proj
      (φ := fun i ↦ (j : ι) → bergmanSpace ℂ ((e i).imageOpens (W i ⊓ W j))) i)

@[simp]
theorem proj₁_apply (ξ : (i j : ι) → bergmanSpace ℂ ((e i).imageOpens (W i ⊓ W j))) (i j : ι) :
    proj₁ i j ξ = ξ i j := (rfl)

variable (g : ι → ι → X → ℂ) (hW : ∀ i, (W i : Set X) ⊆ (e i).source)

/-- The Čech coboundary `ξⱼₖ - ξᵢₖ + ξᵢⱼ` of a one-cochain at a point `x` of a triple overlap, in
the frame of `i`: each component is evaluated in its own first chart, and the component `ξⱼₖ`,
read in the frame of `j`, is converted by the factor `g i j x`. -/
private def cocycleEval (i j k : ι) {x : X} (hx : x ∈ W i ⊓ W j ⊓ W k) :
    ((i j : ι) → bergmanSpace ℂ ((e i).imageOpens (W i ⊓ W j))) →L[ℂ] ℂ :=
  g i j x • (BergmanSpace.evalCLM
      (map_mem_imageOpens (hW j hx.1.2) (V := W j ⊓ W k) ⟨hx.1.2, hx.2⟩)).comp (proj₁ j k) -
    (BergmanSpace.evalCLM
      (map_mem_imageOpens (hW i hx.1.1) (V := W i ⊓ W k) ⟨hx.1.1, hx.2⟩)).comp (proj₁ i k) +
    (BergmanSpace.evalCLM (map_mem_imageOpens (hW i hx.1.1) hx.1)).comp (proj₁ i j)

/-- The square-integrable holomorphic Čech one-cocycles of the chart family, for the overlap
scalars `g`. -/
def cocycles₁ : Submodule ℂ ((i j : ι) → bergmanSpace ℂ ((e i).imageOpens (W i ⊓ W j))) :=
  ⨅ (i) (j) (k) (x) (hx : x ∈ W i ⊓ W j ⊓ W k),
    LinearMap.ker (cocycleEval g hW i j k hx : _ →ₗ[ℂ] ℂ)

/-- A cochain is a cocycle when its chart-read representatives satisfy the Čech cocycle identity,
in the frame of the first index, at every point of every triple overlap. -/
theorem mem_cocycles₁_iff {ξ : (i j : ι) → bergmanSpace ℂ ((e i).imageOpens (W i ⊓ W j))} :
    ξ ∈ cocycles₁ g hW ↔ ∀ i j k, ∀ x ∈ W i ⊓ W j ⊓ W k,
      g i j x * BergmanSpace.representative (ξ j k) (e j x) -
          BergmanSpace.representative (ξ i k) (e i x) +
        BergmanSpace.representative (ξ i j) (e i x) = 0 := by
  simp [cocycles₁, cocycleEval]

/-- Square-integrable cocycles form a closed subspace: they are cut out by continuous point
evaluations, so no bound on the coboundary map between different charts is needed. -/
theorem isClosed_cocycles₁ :
    IsClosed (cocycles₁ g hW :
      Set ((i j : ι) → bergmanSpace ℂ ((e i).imageOpens (W i ⊓ W j)))) := by
  simp only [cocycles₁, Submodule.coe_iInf]
  exact isClosed_iInter fun i ↦ isClosed_iInter fun j ↦ isClosed_iInter fun k ↦
    isClosed_iInter fun x ↦ isClosed_iInter fun hx ↦ (cocycleEval g hW i j k hx).isClosed_ker

instance completeSpace_cocycles₁ : CompleteSpace (cocycles₁ g hW) :=
  (isClosed_cocycles₁ g hW).completeSpace_coe

/-! ### Restriction to a smaller family in the same charts -/

/-- Componentwise restriction of one-cochains to a smaller family in the same charts. -/
def restrictCochains₁ (h : ∀ i, W' i ≤ W i) :
    ((i j : ι) → bergmanSpace ℂ ((e i).imageOpens (W i ⊓ W j))) →L[ℂ]
      ((i j : ι) → bergmanSpace ℂ ((e i).imageOpens (W' i ⊓ W' j))) :=
  BergmanSpace.restrictPi₂ fun i j ↦ imageOpens_mono (inf_le_inf (h i) (h j))

omit g hW in
@[simp]
theorem restrictCochains₁_apply (h : ∀ i, W' i ≤ W i)
    (ξ : (i j : ι) → bergmanSpace ℂ ((e i).imageOpens (W i ⊓ W j))) (i j : ι) :
    restrictCochains₁ h ξ i j = BergmanSpace.restrict (imageOpens_mono (inf_le_inf (h i) (h j)))
      (ξ i j) :=
  BergmanSpace.restrictPi₂_apply _ ξ i j

omit g hW in
/-- Restricting one-cochains to the same family is the identity. -/
@[simp]
theorem restrictCochains₁_refl :
    restrictCochains₁ (e := e) (W := W) (fun _ ↦ le_rfl) = ContinuousLinearMap.id ℂ _ :=
  BergmanSpace.restrictPi₂_refl

omit g hW in
/-- Successive restrictions of one-cochains agree with direct restriction. -/
theorem restrictCochains₁_comp_restrictCochains₁ (h' : ∀ i, W' i ≤ W i)
    (h'' : ∀ i, W'' i ≤ W' i) :
    (restrictCochains₁ h'').comp (restrictCochains₁ h') =
      restrictCochains₁ (e := e) fun i ↦ (h'' i).trans (h' i) :=
  BergmanSpace.restrictPi₂_comp_restrictPi₂ _ _

/-- Restricting a cocycle to a smaller family in the same charts gives a cocycle. -/
theorem restrictCochains₁_mem_cocycles₁ (h : ∀ i, W' i ≤ W i) {ξ} (hξ : ξ ∈ cocycles₁ g hW) :
    restrictCochains₁ h ξ ∈ cocycles₁ g (subset_source_of_le hW h) := by
  rw [mem_cocycles₁_iff] at hξ ⊢
  intro i j k x hx
  have hjk := map_mem_imageOpens (hW j (h j hx.1.2)) (V := W' j ⊓ W' k) ⟨hx.1.2, hx.2⟩
  have hik := map_mem_imageOpens (hW i (h i hx.1.1)) (V := W' i ⊓ W' k) ⟨hx.1.1, hx.2⟩
  have hij := map_mem_imageOpens (hW i (h i hx.1.1)) (V := W' i ⊓ W' j) hx.1
  simpa only [restrictCochains₁_apply, BergmanSpace.representative_restrict _ _ hjk,
    BergmanSpace.representative_restrict _ _ hik, BergmanSpace.representative_restrict _ _ hij]
    using hξ i j k x ⟨⟨h i hx.1.1, h j hx.1.2⟩, h k hx.2⟩

/-- Restriction between the closed spaces of square-integrable cocycles. -/
def restrictCocycles₁ (h : ∀ i, W' i ≤ W i) :
    cocycles₁ g hW →L[ℂ] cocycles₁ g (subset_source_of_le hW h) :=
  ((restrictCochains₁ h).comp (cocycles₁ g hW).subtypeL).codRestrict _ fun ξ ↦
    restrictCochains₁_mem_cocycles₁ g hW h ξ.property

@[simp]
theorem coe_restrictCocycles₁ (h : ∀ i, W' i ≤ W i) (ξ : cocycles₁ g hW) :
    (restrictCocycles₁ g hW h ξ :
        (i j : ι) → bergmanSpace ℂ ((e i).imageOpens (W' i ⊓ W' j))) =
      restrictCochains₁ h ξ.val := (rfl)

/-- Restricting cocycles to the same family is the identity. -/
@[simp]
theorem restrictCocycles₁_refl :
    restrictCocycles₁ g hW (fun _ ↦ le_rfl) = ContinuousLinearMap.id ℂ _ :=
  ContinuousLinearMap.ext fun ξ ↦ Subtype.ext <| by simp

/-- Successive restrictions of cocycles agree with direct restriction. -/
theorem restrictCocycles₁_comp_restrictCocycles₁ (h' : ∀ i, W' i ≤ W i)
    (h'' : ∀ i, W'' i ≤ W' i) :
    (restrictCocycles₁ g (subset_source_of_le hW h') h'').comp (restrictCocycles₁ g hW h') =
      restrictCocycles₁ g hW fun i ↦ (h'' i).trans (h' i) :=
  ContinuousLinearMap.ext fun ξ ↦ Subtype.ext <|
    DFunLike.congr_fun (restrictCochains₁_comp_restrictCochains₁ h' h'') ξ.val

section Compact

variable [Finite ι]

omit g in
include hW in
/-- If each `closure (W' i)` is compact and lies in `W i`, restriction of one-cochains is a compact
operator. -/
theorem isCompactOperator_restrictCochains₁ (hK : ∀ i, IsCompact (closure (W' i : Set X)))
    (hKW : ∀ i, closure (W' i : Set X) ⊆ W i) :
    IsCompactOperator (restrictCochains₁ (e := e) fun i ↦ subset_closure.trans (hKW i)) := by
  have hKij (i j : ι) : IsCompact (closure ((W' i ⊓ W' j : Opens X) : Set X)) :=
    (hK i).of_isClosed_subset isClosed_closure (closure_mono inter_subset_left)
  have hKWij (i j : ι) : closure ((W' i ⊓ W' j : Opens X) : Set X) ⊆ (W i ⊓ W j : Opens X) :=
    fun x hx ↦ ⟨hKW i (closure_mono inter_subset_left hx),
      hKW j (closure_mono inter_subset_right hx)⟩
  have hKe (i j : ι) : closure ((W' i ⊓ W' j : Opens X) : Set X) ⊆ (e i).source :=
    (hKWij i j).trans (inf_subset_source hW i j)
  exact BergmanSpace.isCompactOperator_restrictPi₂ (F := ℂ)
    (fun i j ↦ isCompact_closure_imageOpens (hKij i j) (hKe i j))
    fun i j ↦ closure_imageOpens_subset (hKij i j) (hKe i j) (hKWij i j)

/-- If each `closure (W' i)` is compact and lies in `W i`, restriction of square-integrable
cocycles is a compact operator. -/
theorem isCompactOperator_restrictCocycles₁ (hK : ∀ i, IsCompact (closure (W' i : Set X)))
    (hKW : ∀ i, closure (W' i : Set X) ⊆ W i) :
    IsCompactOperator (restrictCocycles₁ g hW fun i ↦ subset_closure.trans (hKW i)) :=
  ((isCompactOperator_restrictCochains₁ hW hK hKW).comp_clm
      (cocycles₁ g hW).subtypeL).codRestrict
    (fun ξ ↦ restrictCochains₁_mem_cocycles₁ g hW _ ξ.property) (isClosed_cocycles₁ g _)

end Compact

/-! ### Compatible triples -/

variable (h' : ∀ i, W' i ≤ W i) (h'' : ∀ i, W'' i ≤ W' i)

/-- The defect of `ξ' = ξ + δη` at a point of an overlap `W'' i ⊓ W'' j`, in the frame of `i`, as
a continuous linear functional of the triple of cochains `(ξ, ξ', η)`; the component `ηⱼ`, read in
the frame of `j`, is converted by the factor `g i j x`. -/
private def tripleEval (i j : ι) {x : X} (hx : x ∈ W'' i ⊓ W'' j) :
    (((i j : ι) → bergmanSpace ℂ ((e i).imageOpens (W i ⊓ W j))) ×
      ((i j : ι) → bergmanSpace ℂ ((e i).imageOpens (W' i ⊓ W' j))) ×
        ((i : ι) → bergmanSpace ℂ ((e i).imageOpens (W'' i)))) →L[ℂ] ℂ :=
  (BergmanSpace.evalCLM (map_mem_imageOpens (hW i (h' i (h'' i hx.1)))
      (V := W' i ⊓ W' j) ⟨h'' i hx.1, h'' j hx.2⟩)).comp ((proj₁ i j).comp
        ((ContinuousLinearMap.fst ℂ _ _).comp (ContinuousLinearMap.snd ℂ _ _))) -
    (BergmanSpace.evalCLM (map_mem_imageOpens (hW i (h' i (h'' i hx.1)))
      (V := W i ⊓ W j) ⟨h' i (h'' i hx.1), h' j (h'' j hx.2)⟩)).comp
        ((proj₁ i j).comp (ContinuousLinearMap.fst ℂ _ _)) -
    g i j x • (BergmanSpace.evalCLM (map_mem_imageOpens (hW j (h' j (h'' j hx.2))) hx.2)).comp
      ((ContinuousLinearMap.proj j).comp
        ((ContinuousLinearMap.snd ℂ _ _).comp (ContinuousLinearMap.snd ℂ _ _))) +
    (BergmanSpace.evalCLM (map_mem_imageOpens (hW i (h' i (h'' i hx.1))) hx.1)).comp
      ((ContinuousLinearMap.proj i).comp
        ((ContinuousLinearMap.snd ℂ _ _).comp (ContinuousLinearMap.snd ℂ _ _)))

/-- The compatible triples `(ξ, ξ', η)` for overlap scalars `g`: square-integrable cocycles `ξ` on
`W` and `ξ'` on `W'`, and a square-integrable zero-cochain `η` on `W''`, with `ξ' = ξ + δη` on
`W''`. Here `ηⱼ` is converted into the frame of `i` by `g i j`, so `(δη)ᵢⱼ` is
`g i j * ηⱼ - ηᵢ` in chart coordinates. -/
def compatibleTriples :
    Submodule ℂ (((i j : ι) → bergmanSpace ℂ ((e i).imageOpens (W i ⊓ W j))) ×
      ((i j : ι) → bergmanSpace ℂ ((e i).imageOpens (W' i ⊓ W' j))) ×
        ((i : ι) → bergmanSpace ℂ ((e i).imageOpens (W'' i)))) :=
  (cocycles₁ g hW).prod ((cocycles₁ g (subset_source_of_le hW h')).prod ⊤) ⊓
    ⨅ (i) (j) (x) (hx : x ∈ W'' i ⊓ W'' j),
      LinearMap.ker (tripleEval g hW h' h'' i j hx : _ →ₗ[ℂ] ℂ)

/-- A triple is compatible when `ξ` and `ξ'` are cocycles and the chart-read representatives
satisfy `ξ'ᵢⱼ (eᵢ x) = ξᵢⱼ (eᵢ x) + gᵢⱼ x * ηⱼ (eⱼ x) - ηᵢ (eᵢ x)`, in the frame of `i`, at every
point `x` of every overlap of `W''`. -/
theorem mem_compatibleTriples_iff
    {t : ((i j : ι) → bergmanSpace ℂ ((e i).imageOpens (W i ⊓ W j))) ×
      ((i j : ι) → bergmanSpace ℂ ((e i).imageOpens (W' i ⊓ W' j))) ×
        ((i : ι) → bergmanSpace ℂ ((e i).imageOpens (W'' i)))} :
    t ∈ compatibleTriples g hW h' h'' ↔ t.1 ∈ cocycles₁ g hW ∧
      t.2.1 ∈ cocycles₁ g (subset_source_of_le hW h') ∧ ∀ i j, ∀ x ∈ W'' i ⊓ W'' j,
        BergmanSpace.representative (t.2.1 i j) (e i x) =
          BergmanSpace.representative (t.1 i j) (e i x) +
            (g i j x * BergmanSpace.representative (t.2.2 j) (e j x) -
              BergmanSpace.representative (t.2.2 i) (e i x)) := by
  simp only [compatibleTriples, Submodule.mem_inf, Submodule.mem_prod, Submodule.mem_top,
    and_true, Submodule.mem_iInf, LinearMap.mem_ker, and_assoc]
  refine and_congr_right' (and_congr_right' (forall₄_congr fun i j x hx ↦ ?_))
  simp only [tripleEval, ContinuousLinearMap.coe_coe, add_apply, sub_apply,
    smul_apply, smul_eq_mul,
    ContinuousLinearMap.comp_apply, BergmanSpace.evalCLM_apply, proj₁_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', ContinuousLinearMap.proj_apply]
  constructor <;> intro h <;> linear_combination h

/-- The compatible triples form a closed subspace, cut out by continuous point evaluations. -/
theorem isClosed_compatibleTriples :
    IsClosed (compatibleTriples g hW h' h'' :
      Set (((i j : ι) → bergmanSpace ℂ ((e i).imageOpens (W i ⊓ W j))) ×
        ((i j : ι) → bergmanSpace ℂ ((e i).imageOpens (W' i ⊓ W' j))) ×
          ((i : ι) → bergmanSpace ℂ ((e i).imageOpens (W'' i))))) := by
  simp only [compatibleTriples, Submodule.coe_inf, Submodule.coe_iInf]
  refine IsClosed.inter ((isClosed_cocycles₁ g hW).prod ((isClosed_cocycles₁ g _).prod
    isClosed_univ)) ?_
  exact isClosed_iInter fun i ↦ isClosed_iInter fun j ↦ isClosed_iInter fun x ↦
    isClosed_iInter fun hx ↦ (tripleEval g hW h' h'' i j hx).isClosed_ker

instance completeSpace_compatibleTriples : CompleteSpace (compatibleTriples g hW h' h'') :=
  (isClosed_compatibleTriples g hW h' h'').completeSpace_coe

/-- The continuous linear projection of a compatible triple to its middle cocycle. -/
def middleProjection :
    compatibleTriples g hW h' h'' →L[ℂ] cocycles₁ g (subset_source_of_le hW h') :=
  (((ContinuousLinearMap.fst ℂ _ _).comp (ContinuousLinearMap.snd ℂ _ _)).comp
    (compatibleTriples g hW h' h'').subtypeL).codRestrict _ fun t ↦
      ((mem_compatibleTriples_iff g hW h' h'').mp t.property).2.1

/-- The projection retains the middle cochain of the original compatible triple. -/
@[simp]
theorem coe_middleProjection (t : compatibleTriples g hW h' h'') :
    (middleProjection g hW h' h'' t).val = t.val.2.1 := by
  unfold middleProjection
  exact ContinuousLinearMap.coe_codRestrict_apply _ _ _ t

end ChartBergman

/-! ### Compact holomorphic representatives -/

namespace ChartBergman

open MeasureTheory
open scoped ENNReal Topology

universe u

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ℂ M]
  {ι : Type*} {e : ι → OpenPartialHomeomorph M ℂ}
  {W : ι → Opens M} {U : ι → Set M}

/-- A holomorphic function on a larger chart domain gives a Bergman class on a relatively
compact smaller open, with exactly the original values. -/
theorem exists_representative_eq {e : OpenPartialHomeomorph M ℂ} {V : Opens M} {S : Set M}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ) 1 M)
    (hK : IsCompact (closure (V : Set M))) (hKS : closure (V : Set M) ⊆ S)
    (hKe : closure (V : Set M) ⊆ e.source) {f : M → ℂ} (hf : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) f S) :
    ∃ u : bergmanSpace ℂ (e.imageOpens V),
      ∀ x ∈ V, BergmanSpace.representative u (e x) = f x := by
  have hfe : DifferentiableOn ℂ (f ∘ e.symm) (e.imageOpens V) :=
    ((hf.mono (subset_closure.trans hKS)).comp
      (((contMDiffOn_symm_of_mem_maximalAtlas he).mdifferentiableOn one_ne_zero).mono
        e.imageOpens_subset_target) fun z hz ↦ (e.mem_imageOpens.mp hz).2).differentiableOn
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hf.continuousOn.mono hKS)
  let := e.isFiniteMeasure_restrict_imageOpens volume hK hKe
  let B := BoundedHolomorphicFunctions.of (e.imageOpens V) (f ∘ e.symm) hfe C
    fun z hz ↦ hC _ (subset_closure (e.mem_imageOpens.mp hz).2)
  refine ⟨BergmanSpace.ofBounded B, fun x hx ↦ ?_⟩
  have hxe := hKe (subset_closure hx)
  have hex := e.map_mem_imageOpens hxe hx
  rw [BergmanSpace.representative_ofBounded _ hex,
    BoundedHolomorphicFunctions.extend_apply _ ⟨e x, hex⟩,
    BoundedHolomorphicFunctions.of_apply, Function.comp_apply, e.left_inv hxe]

/-- A native Bergman representative pulled back by its own holomorphic chart is holomorphic. -/
theorem mdifferentiableOn_representative_comp_chart
    {e : OpenPartialHomeomorph M ℂ} {A : Opens M}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ) 1 M) (hA : (A : Set M) ⊆ e.source)
    (u : bergmanSpace ℂ (e.imageOpens A)) :
    MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) (BergmanSpace.representative u ∘ e) A := by
  exact (BergmanSpace.differentiableOn_representative u).mdifferentiableOn.comp
    (((contMDiffOn_of_mem_maximalAtlas he).mdifferentiableOn one_ne_zero).mono hA)
    fun x hx ↦ e.map_mem_imageOpens (hA hx) hx

/-- Restricting a holomorphic cocycle to relatively compact chart opens gives an actual
native Bergman cocycle with the same pointwise readings. -/
theorem exists_cocycle_representative_eq
    (g : ι → ι → M → ℂ)
    (he : ∀ i, e i ∈ IsManifold.maximalAtlas 𝓘(ℂ) 1 M)
    (hKW : ∀ i, IsCompact (closure (W i : Set M)))
    (hWU : ∀ i, closure (W i : Set M) ⊆ U i)
    (hKeW : ∀ i, closure (W i : Set M) ⊆ (e i).source)
    (ζ : ι → ι → M → ℂ)
    (hζ : ∀ i j, MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) (ζ i j) (U i ∩ U j))
    (hζc : ∀ i j k, ∀ x ∈ U i ∩ U j ∩ U k,
      ζ i j x + g i j x • ζ j k x = ζ i k x) :
    ∃ Z : (i j : ι) → bergmanSpace ℂ ((e i).imageOpens (W i ⊓ W j)),
      Z ∈ cocycles₁ g (fun i ↦ subset_closure.trans (hKeW i)) ∧ ∀ i j, ∀ x ∈ W i ⊓ W j,
        BergmanSpace.representative (Z i j) (e i x) = ζ i j x := by
  have hKij (i j : ι) : IsCompact (closure ((W i ⊓ W j : Opens M) : Set M)) :=
    (hKW i).of_isClosed_subset isClosed_closure (closure_mono inter_subset_left)
  have hKUij (i j : ι) : closure ((W i ⊓ W j : Opens M) : Set M) ⊆ U i ∩ U j :=
    fun x hx ↦ ⟨hWU i (closure_mono inter_subset_left hx),
      hWU j (closure_mono inter_subset_right hx)⟩
  choose Z hZ using fun i j ↦ exists_representative_eq (he i) (hKij i j) (hKUij i j)
    ((closure_mono inter_subset_left).trans (hKeW i)) (hζ i j)
  refine ⟨Z, ?_, hZ⟩
  rw [mem_cocycles₁_iff]
  intro i j k x hx
  rw [hZ j k x ⟨hx.1.2, hx.2⟩, hZ i k x ⟨hx.1.1, hx.2⟩, hZ i j x hx.1]
  have hh := hζc i j k x
    ⟨⟨hWU i (subset_closure hx.1.1), hWU j (subset_closure hx.1.2)⟩,
      hWU k (subset_closure hx.2)⟩
  simp only [smul_eq_mul] at hh
  linear_combination hh

end ChartBergman

/-! ### Native sections from chart-read Bergman classes -/

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
  {e : OpenPartialHomeomorph X ℂ} {V V' : Opens X}

/-- A Bergman class on the plane open read from `V ⊆ e.source`, as the native holomorphic section
`x ↦ u (e x)` of the structure sheaf over `V`. -/
def chartSection (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ) 1 X) (hV : (V : Set X) ⊆ e.source) :
    bergmanSpace ℂ (e.imageOpens V) →ₗ[ℂ]
      (holomorphicStructureSheafModules 𝓘(ℂ) X).obj.obj (op V) where
  toFun u := holomorphicStructureSheafModules.ofContMDiff
    (fun x : V ↦ BergmanSpace.representative u (e x))
    (Manifold.mdifferentiable_restrict_comp_chart he hV fun x hx ↦
      ((BergmanSpace.differentiableOn_representative u).differentiableAt
        ((e.imageOpens V).isOpen.mem_nhds
          (map_mem_imageOpens (hV hx) hx))).mdifferentiableAt).contMDiff
  map_add' u v := by
    ext x
    simp [BergmanSpace.representative_add _ _ (map_mem_imageOpens (hV x.property) x.property)]
  map_smul' c u := by
    ext x
    simp [BergmanSpace.representative_smul _ _ (map_mem_imageOpens (hV x.property) x.property)]

@[simp]
theorem chartSection_apply (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ) 1 X)
    (hV : (V : Set X) ⊆ e.source) (u : bergmanSpace ℂ (e.imageOpens V)) (x : V) :
    chartSection he hV u x = BergmanSpace.representative u (e x) :=
  holomorphicStructureSheafModules.ofContMDiff_apply _ _ x

/-- A chart-read Bergman class is determined by its native section. -/
theorem chartSection_injective (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ) 1 X)
    (hV : (V : Set X) ⊆ e.source) : Function.Injective (chartSection he hV) := by
  intro u v h
  apply BergmanSpace.ext
  intro z hz
  obtain ⟨hzt, hzV⟩ := mem_imageOpens.1 hz
  have := congrArg (fun s ↦ s ⟨e.symm z, hzV⟩) h
  simp only at this
  rwa [chartSection_apply, chartSection_apply, e.right_inv hzt] at this

/-- Restricting a chart-read Bergman class to a smaller open read in the same chart is the native
restriction of its section. -/
theorem chartSection_restrict (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ) 1 X)
    (hV : (V : Set X) ⊆ e.source) (h : V' ≤ V) (u : bergmanSpace ℂ (e.imageOpens V)) :
    chartSection he ((SetLike.coe_subset_coe.2 h).trans hV)
        (BergmanSpace.restrict (imageOpens_mono h) u) =
      (holomorphicStructureSheafModules 𝓘(ℂ) X).obj.map (homOfLE h).op (chartSection he hV u) := by
  ext x
  rw [holomorphicStructureSheafModules.map_apply, chartSection_apply, chartSection_apply]
  exact BergmanSpace.representative_restrict _ _
    (map_mem_imageOpens (hV (h x.property)) x.property)

namespace ChartBergman

variable {ι : Type*} {e : ι → OpenPartialHomeomorph X ℂ} {W W' W'' : ι → Opens X}
  (he : ∀ i, e i ∈ IsManifold.maximalAtlas 𝓘(ℂ) 1 X) (hW : ∀ i, (W i : Set X) ⊆ (e i).source)

/-- Square-integrable zero-cochains realized as native sections over the `W i`. -/
def toSections₀ :
    ((i : ι) → bergmanSpace ℂ ((e i).imageOpens (W i))) →ₗ[ℂ]
      ((i : ι) → (holomorphicStructureSheafModules 𝓘(ℂ) X).obj.obj (op (W i))) :=
  LinearMap.piMap fun i ↦ chartSection (he i) (hW i)

/-- Square-integrable one-cochains realized as native sections over the overlaps `W i ⊓ W j`. -/
def toSections₁ :
    ((i j : ι) → bergmanSpace ℂ ((e i).imageOpens (W i ⊓ W j))) →ₗ[ℂ]
      ((i j : ι) → (holomorphicStructureSheafModules 𝓘(ℂ) X).obj.obj (op (W i ⊓ W j))) :=
  LinearMap.piMap fun i ↦ LinearMap.piMap fun j ↦
    chartSection (he i) (inf_subset_source hW i j)

@[simp]
theorem toSections₀_apply (η : (i : ι) → bergmanSpace ℂ ((e i).imageOpens (W i))) (i : ι)
    (x : W i) : toSections₀ he hW η i x = BergmanSpace.representative (η i) (e i x) :=
  chartSection_apply (he i) (hW i) _ x

@[simp]
theorem toSections₁_apply (ξ : (i j : ι) → bergmanSpace ℂ ((e i).imageOpens (W i ⊓ W j)))
    (i j : ι) (x : ↥(W i ⊓ W j)) :
    toSections₁ he hW ξ i j x = BergmanSpace.representative (ξ i j) (e i x) :=
  chartSection_apply (he i) (inf_subset_source hW i j) _ x

/-- A square-integrable zero-cochain is determined by its native sections. -/
theorem toSections₀_injective : Function.Injective (toSections₀ he hW) :=
  fun _ _ h ↦ funext fun i ↦ chartSection_injective (he i) (hW i) (congrFun h i)

/-- A square-integrable one-cochain is determined by its native sections. -/
theorem toSections₁_injective : Function.Injective (toSections₁ he hW) :=
  fun _ _ h ↦ funext fun i ↦ funext fun j ↦
    chartSection_injective (he i) (inf_subset_source hW i j) (congrFun (congrFun h i) j)

/-- For the structure sheaf (`g = 1`), the cocycle condition is the native cocycle identity for
the realized sections. -/
theorem mem_cocycles₁_iff_toSections₁
    {ξ : (i j : ι) → bergmanSpace ℂ ((e i).imageOpens (W i ⊓ W j))} :
    ξ ∈ cocycles₁ 1 hW ↔ ∀ i j k, ∀ x (hx : x ∈ W i ⊓ W j ⊓ W k),
      toSections₁ he hW ξ j k ⟨x, hx.1.2, hx.2⟩ - toSections₁ he hW ξ i k ⟨x, hx.1.1, hx.2⟩ +
        toSections₁ he hW ξ i j ⟨x, hx.1⟩ = 0 := by
  rw [mem_cocycles₁_iff]
  refine forall₄_congr fun i j k x ↦ forall_congr' fun hx ↦ ?_
  rw [toSections₁_apply, toSections₁_apply, toSections₁_apply, Pi.one_apply, Pi.one_apply,
    Pi.one_apply, one_mul]

/-- Restriction of zero-cochains is the native restriction of their sections. -/
theorem toSections₀_restrictPi (h : ∀ i, W' i ≤ W i)
    (η : (i : ι) → bergmanSpace ℂ ((e i).imageOpens (W i))) (i : ι) :
    toSections₀ he (subset_source_of_le hW h)
        (BergmanSpace.restrictPi (fun i ↦ imageOpens_mono (h i)) η) i =
      (holomorphicStructureSheafModules 𝓘(ℂ) X).obj.map (homOfLE (h i)).op
        (toSections₀ he hW η i) :=
  (congrArg (chartSection (he i) _) (BergmanSpace.restrictPi_apply _ η i)).trans
    (chartSection_restrict (he i) (hW i) (h i) (η i))

/-- Restriction of one-cochains is the native restriction of their sections. -/
theorem toSections₁_restrictCochains₁ (h : ∀ i, W' i ≤ W i)
    (ξ : (i j : ι) → bergmanSpace ℂ ((e i).imageOpens (W i ⊓ W j))) (i j : ι) :
    toSections₁ he (subset_source_of_le hW h) (restrictCochains₁ h ξ) i j =
      (holomorphicStructureSheafModules 𝓘(ℂ) X).obj.map (homOfLE (inf_le_inf (h i) (h j))).op
        (toSections₁ he hW ξ i j) :=
  (congrArg (chartSection (he i) _) (restrictCochains₁_apply h ξ i j)).trans
    (chartSection_restrict (he i) (inf_subset_source hW i j) _ (ξ i j))

/-- For the structure sheaf (`g = 1`), a triple is compatible when `ξ` and `ξ'` are cocycles and
the native sections satisfy `ξ' = ξ + δη` over each overlap `W'' i ⊓ W'' j`, with
`(δη)ᵢⱼ = ηⱼ - ηᵢ`. -/
theorem mem_compatibleTriples_iff_toSections (h' : ∀ i, W' i ≤ W i) (h'' : ∀ i, W'' i ≤ W' i)
    {t : ((i j : ι) → bergmanSpace ℂ ((e i).imageOpens (W i ⊓ W j))) ×
      ((i j : ι) → bergmanSpace ℂ ((e i).imageOpens (W' i ⊓ W' j))) ×
        ((i : ι) → bergmanSpace ℂ ((e i).imageOpens (W'' i)))} :
    t ∈ compatibleTriples 1 hW h' h'' ↔ t.1 ∈ cocycles₁ 1 hW ∧
      t.2.1 ∈ cocycles₁ 1 (subset_source_of_le hW h') ∧ ∀ i j,
      (holomorphicStructureSheafModules 𝓘(ℂ) X).obj.map
          (homOfLE (inf_le_inf (h'' i) (h'' j))).op
            (toSections₁ he (subset_source_of_le hW h') t.2.1 i j) =
        (holomorphicStructureSheafModules 𝓘(ℂ) X).obj.map
            (homOfLE (inf_le_inf ((h'' i).trans (h' i)) ((h'' j).trans (h' j)))).op
            (toSections₁ he hW t.1 i j) +
          ((holomorphicStructureSheafModules 𝓘(ℂ) X).obj.map (homOfLE inf_le_right).op
              (toSections₀ he (subset_source_of_le (subset_source_of_le hW h') h'') t.2.2 j) -
            (holomorphicStructureSheafModules 𝓘(ℂ) X).obj.map (homOfLE inf_le_left).op
              (toSections₀ he (subset_source_of_le (subset_source_of_le hW h') h'') t.2.2 i)) := by
  rw [mem_compatibleTriples_iff]
  refine and_congr_right' (and_congr_right' (forall₂_congr fun i j ↦ ?_))
  rw [holomorphicStructureSheafModules.ext_iff, Subtype.forall]
  refine forall₂_congr fun x hx ↦ ?_
  simp only [holomorphicStructureSheafModules.add_apply, holomorphicStructureSheafModules.sub_apply,
    holomorphicStructureSheafModules.map_apply]
  rw [toSections₁_apply, toSections₁_apply, toSections₀_apply, toSections₀_apply, Pi.one_apply,
    Pi.one_apply, Pi.one_apply, one_mul]

end ChartBergman

end TauCeti.RiemannSurface


namespace Bundle.Trivialization

open CategoryTheory Opposite Set TopologicalSpace
open TauCeti

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
  {V : X → Type} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℂ (V x)] [∀ x, TopologicalSpace (V x)]
  [FiberBundle F V] [VectorBundle ℂ F V] [ContMDiffVectorBundle ω F V 𝓘(ℂ)]
  (τ : Trivialization F (π F V)) [τ.IsLinear ℂ] (q : F ≃L[ℂ] ℂ)
  (hτa : τ.toOpenPartialHomeomorph ∈
    (contMDiffFiberwiseLinear X F 𝓘(ℂ) ω).maximalAtlas (TotalSpace F V))
  {e : OpenPartialHomeomorph X ℂ} {U U' : Opens X}

/-- A scalar Bergman class, read in an actual holomorphic line-bundle frame, gives a native
holomorphic section. No boundedness of the frame or compact containment is required. -/
def bergmanSection (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ) 1 X)
    (hU : (U : Set X) ⊆ e.source) (hτ : (U : Set X) ⊆ τ.baseSet) :
    bergmanSpace ℂ (e.imageOpens U) →ₗ[ℂ]
      (holomorphicSectionSheaf 𝓘(ℂ) F V).obj.obj (op U) :=
  (τ.holomorphicSectionLinearEquiv q hτa hτ).symm.toLinearMap.comp
    (RiemannSurface.chartSection he hU)

/-- Evaluation of the native section in the chosen frame. -/
@[simp]
theorem bergmanSection_apply (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ) 1 X)
    (hU : (U : Set X) ⊆ e.source) (hτ : (U : Set X) ⊆ τ.baseSet)
    (u : bergmanSpace ℂ (e.imageOpens U)) (x : U) :
    τ.bergmanSection q hτa he hU hτ u x =
      τ.symmL ℂ x (q.symm (BergmanSpace.representative u (e x))) := by
  rw [bergmanSection, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    τ.holomorphicSectionLinearEquiv_symm_apply q hτa hτ
      (RiemannSurface.chartSection he hU u) x, RiemannSurface.chartSection_apply he hU u x]

/-- The chosen scalar coordinate of a realized section is its original Bergman representative. -/
theorem bergmanSection_coordinate_self (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ) 1 X)
    (hU : (U : Set X) ⊆ e.source) (hτ : (U : Set X) ⊆ τ.baseSet)
    (u : bergmanSpace ℂ (e.imageOpens U)) (x : U) :
    q (τ.continuousLinearMapAt ℂ x (τ.bergmanSection q hτa he hU hτ u x)) =
      BergmanSpace.representative u (e x) := by
  rw [bergmanSection_apply, τ.continuousLinearMapAt_symmL (hτ x.property), q.apply_symm_apply]

/-- Realization in a line-bundle frame retains every Bergman class. -/
theorem bergmanSection_injective (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ) 1 X)
    (hU : (U : Set X) ⊆ e.source) (hτ : (U : Set X) ⊆ τ.baseSet) :
    Function.Injective (τ.bergmanSection q hτa he hU hτ) := by
  exact (τ.holomorphicSectionLinearEquiv q hτa hτ).symm.injective.comp
    (RiemannSurface.chartSection_injective he hU)

/-- Restricting the Bergman class restricts its native bundle section. -/
theorem bergmanSection_restrict (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ) 1 X)
    (hU : (U : Set X) ⊆ e.source) (hτ : (U : Set X) ⊆ τ.baseSet) (h : U' ≤ U)
    (u : bergmanSpace ℂ (e.imageOpens U)) :
    τ.bergmanSection q hτa he ((SetLike.coe_subset_coe.2 h).trans hU)
        ((SetLike.coe_subset_coe.2 h).trans hτ)
        (BergmanSpace.restrict (OpenPartialHomeomorph.imageOpens_mono h) u) =
      (holomorphicSectionSheaf 𝓘(ℂ) F V).obj.map (homOfLE h).op
        (τ.bergmanSection q hτa he hU hτ u) := by
  apply holomorphicSectionSheaf.ext
  intro x
  rw [holomorphicSectionSheaf.map_apply, bergmanSection_apply, bergmanSection_apply,
    BergmanSpace.representative_restrict _ _ (OpenPartialHomeomorph.map_mem_imageOpens
      (hU (h x.property)) x.property)]

end Bundle.Trivialization


namespace OpenPartialHomeomorph

open CategoryTheory MeasureTheory Opposite Set TopologicalSpace
open TauCeti

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
  (e : OpenPartialHomeomorph X ℂ) (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ) 1 X)
  {U W : Opens X} (hU : (U : Set X) ⊆ e.source)
  (hK : IsCompact (closure (W : Set X))) (hKU : closure (W : Set X) ⊆ U)

private def holomorphicSectionBoundedAux
    (s : (holomorphicStructureSheafModules 𝓘(ℂ) X).obj.obj (op U)) :
    boundedHolomorphicFunctions ℂ (e.imageOpens W) := by
  let f : (holomorphicStructureSheaf 𝓘(ℂ) X).obj.obj (op U) :=
    holomorphicStructureSheafModules.sectionsLinearEquiv 𝓘(ℂ) X (op U) s
  let G : ℂ → ℂ := (Function.extend Subtype.val
    (holomorphicStructureSheaf.toFun 𝓘(ℂ) X (op U) f) (fun _ ↦ 0)) ∘ e.symm
  have ha : AnalyticOnNhd ℂ G (e.imageOpens U) := by
    intro z hz
    obtain ⟨hzt, hzU⟩ := mem_imageOpens.1 hz
    have h := e.analyticAt_holomorphicSection_extend_comp_symm he (e.symm z)
      (e.map_target hzt) U hzU f
    simpa only [e.right_inv hzt] using h
  have hcl := e.isCompact_closure_imageOpens hK (hKU.trans hU)
  have hinc := e.closure_imageOpens_subset hK (hKU.trans hU) hKU
  let bound := hcl.exists_bound_of_continuousOn (ha.continuousOn.mono hinc)
  exact BoundedHolomorphicFunctions.of _ G
    (ha.differentiableOn.mono (subset_closure.trans hinc)) bound.choose
    (fun z hz ↦ bound.choose_spec z (subset_closure hz))

private theorem holomorphicSectionBoundedAux_apply
    (s : (holomorphicStructureSheafModules 𝓘(ℂ) X).obj.obj (op U)) (z : e.imageOpens W) :
    (holomorphicSectionBoundedAux e he hU hK hKU s :
      BoundedContinuousFunction (e.imageOpens W) ℂ) z =
      s ⟨e.symm z, hKU (subset_closure (mem_imageOpens.1 z.property).2)⟩ := by
  simp only [holomorphicSectionBoundedAux, BoundedHolomorphicFunctions.of_apply,
    Function.comp_apply]
  exact (Subtype.val_injective.extend_apply _ _
    ⟨e.symm z, hKU (subset_closure (mem_imageOpens.1 z.property).2)⟩).trans
      (holomorphicStructureSheafModules.sectionsLinearEquiv_apply _ _ _ _ _)

/-- Read a native holomorphic function on a larger chart open as a Bergman class on a
relatively compact smaller open. There is no integrability assertion on the larger open. -/
def holomorphicSectionToBergman :
    (holomorphicStructureSheafModules 𝓘(ℂ) X).obj.obj (op U) →ₗ[ℂ]
      bergmanSpace ℂ (e.imageOpens W) := by
  letI : IsFiniteMeasure (volume.restrict (e.imageOpens W : Set ℂ)) :=
    e.isFiniteMeasure_restrict_imageOpens volume hK (hKU.trans hU)
  let T : (holomorphicStructureSheafModules 𝓘(ℂ) X).obj.obj (op U) →ₗ[ℂ]
      boundedHolomorphicFunctions ℂ (e.imageOpens W) :=
    { toFun := holomorphicSectionBoundedAux e he hU hK hKU
      map_add' s t := by
        apply Subtype.ext
        apply BoundedContinuousFunction.ext
        intro z
        simp [holomorphicSectionBoundedAux_apply, holomorphicStructureSheafModules.add_apply]
      map_smul' c s := by
        apply Subtype.ext
        apply BoundedContinuousFunction.ext
        intro z
        simp [holomorphicSectionBoundedAux_apply, holomorphicStructureSheafModules.smul_apply] }
  exact (BergmanSpace.ofBounded (F := ℂ)).toLinearMap.comp T

/-- On the smaller open, the Bergman representative is exactly the original native function. -/
@[simp]
theorem holomorphicSectionToBergman_apply
    (s : (holomorphicStructureSheafModules 𝓘(ℂ) X).obj.obj (op U)) (x : W) :
    BergmanSpace.representative (e.holomorphicSectionToBergman he hU hK hKU s) (e x) =
      s ⟨x, hKU (subset_closure x.property)⟩ := by
  let : IsFiniteMeasure (volume.restrict (e.imageOpens W : Set ℂ)) :=
    e.isFiniteMeasure_restrict_imageOpens volume hK (hKU.trans hU)
  have hx := map_mem_imageOpens (hU (hKU (subset_closure x.property))) x.property
  calc
    BergmanSpace.representative (e.holomorphicSectionToBergman he hU hK hKU s) (e x) =
        BoundedHolomorphicFunctions.extend (holomorphicSectionBoundedAux e he hU hK hKU s)
          (e x) := by
      exact BergmanSpace.representative_ofBounded
        (holomorphicSectionBoundedAux e he hU hK hKU s) hx
    _ = s ⟨x, hKU (subset_closure x.property)⟩ := by
      rw [BoundedHolomorphicFunctions.extend_apply _ ⟨e x, hx⟩,
        holomorphicSectionBoundedAux_apply]
      congr 1
      exact Subtype.ext (e.left_inv (hU (hKU (subset_closure x.property))))

end OpenPartialHomeomorph

namespace Bundle.Trivialization

open CategoryTheory Opposite Set TopologicalSpace TauCeti

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
  {V : X → Type} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℂ (V x)] [∀ x, TopologicalSpace (V x)]
  [FiberBundle F V] [VectorBundle ℂ F V] [ContMDiffVectorBundle ω F V 𝓘(ℂ)]
  (τ : Trivialization F (π F V)) [τ.IsLinear ℂ] (q : F ≃L[ℂ] ℂ)
  (hτa : τ.toOpenPartialHomeomorph ∈
    (contMDiffFiberwiseLinear X F 𝓘(ℂ) ω).maximalAtlas (TotalSpace F V))
  {e : OpenPartialHomeomorph X ℂ} {U W : Opens X}
  (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ) 1 X)
  (hU : (U : Set X) ⊆ e.source) (hτ : (U : Set X) ⊆ τ.baseSet)

/-- Realize the restriction of a native bundle section as a Bergman class, using compact
containment to bound its actual holomorphic frame coordinate. -/
def bergmanRestriction (hK : IsCompact (closure (W : Set X)))
    (hKU : closure (W : Set X) ⊆ U) :
    (holomorphicSectionSheaf 𝓘(ℂ) F V).obj.obj (op U) →ₗ[ℂ]
      bergmanSpace ℂ (e.imageOpens W) :=
  (e.holomorphicSectionToBergman he hU hK hKU).comp
    (τ.holomorphicSectionLinearEquiv q hτa hτ).toLinearMap

omit [IsManifold 𝓘(ℂ) 1 X] in
/-- The compact-shrink realization reads the actual fibre coordinate. -/
@[simp]
theorem bergmanRestriction_apply (hK : IsCompact (closure (W : Set X)))
    (hKU : closure (W : Set X) ⊆ U)
    (s : (holomorphicSectionSheaf 𝓘(ℂ) F V).obj.obj (op U)) (x : W) :
    BergmanSpace.representative (τ.bergmanRestriction q hτa he hU hτ hK hKU s) (e x) =
      q (τ.continuousLinearMapAt ℂ x (s ⟨x, hKU (subset_closure x.property)⟩)) := by
  rw [bergmanRestriction, LinearMap.comp_apply, e.holomorphicSectionToBergman_apply]
  exact τ.holomorphicSectionLinearEquiv_apply q hτa hτ s
    ⟨x, hKU (subset_closure x.property)⟩

/-- Returning from the Bergman realization gives the native restriction of the original
section, rather than an assertion that it was square-integrable on the larger open. -/
theorem bergmanSection_bergmanRestriction (hK : IsCompact (closure (W : Set X)))
    (hKU : closure (W : Set X) ⊆ U)
    (s : (holomorphicSectionSheaf 𝓘(ℂ) F V).obj.obj (op U)) :
    τ.bergmanSection q hτa he ((subset_closure.trans hKU).trans hU)
        ((subset_closure.trans hKU).trans hτ)
        (τ.bergmanRestriction q hτa he hU hτ hK hKU s) =
      (holomorphicSectionSheaf 𝓘(ℂ) F V).obj.map
        (homOfLE (show W ≤ U from subset_closure.trans hKU)).op s := by
  apply holomorphicSectionSheaf.ext
  intro x
  rw [bergmanSection_apply, bergmanRestriction_apply, q.symm_apply_apply,
    τ.symmL_continuousLinearMapAt (hτ (hKU (subset_closure x.property))),
    holomorphicSectionSheaf.map_apply]

/-- Starting with a Bergman class, the native compact-shrink realization is the canonical
Bergman restriction. -/
theorem bergmanRestriction_bergmanSection (hK : IsCompact (closure (W : Set X)))
    (hKU : closure (W : Set X) ⊆ U) (u : bergmanSpace ℂ (e.imageOpens U)) :
    τ.bergmanRestriction q hτa he hU hτ hK hKU (τ.bergmanSection q hτa he hU hτ u) =
      BergmanSpace.restrict
        (OpenPartialHomeomorph.imageOpens_mono
          (show W ≤ U from subset_closure.trans hKU)) u := by
  apply BergmanSpace.ext
  intro z hz
  obtain ⟨hzt, hzx⟩ := OpenPartialHomeomorph.mem_imageOpens.1 hz
  have hx : e.symm z ∈ W := hzx
  have hez := e.right_inv hzt
  have h := τ.bergmanRestriction_apply q hτa he hU hτ hK hKU
    (τ.bergmanSection q hτa he hU hτ u) ⟨e.symm z, hx⟩
  rw [bergmanSection_apply, τ.continuousLinearMapAt_symmL (hτ (hKU (subset_closure hx))),
    q.apply_symm_apply, hez] at h
  exact h.trans (BergmanSpace.representative_restrict _ u hz).symm

/-- Reading a realized section in another actual frame multiplies by the native transition
scalar, with source frame first and target frame second. -/
theorem bergmanSection_coordinate (τ' : Trivialization F (π F V)) [τ'.IsLinear ℂ]
    (q' : F ≃L[ℂ] ℂ) (u : bergmanSpace ℂ (e.imageOpens U)) (x : U)
    (hx' : (x : X) ∈ τ'.baseSet) :
    q' (τ'.continuousLinearMapAt ℂ x (τ.bergmanSection q hτa he hU hτ u x)) =
      τ.scalarCoordChange τ' q q' x * BergmanSpace.representative u (e x) := by
  rw [← τ.scalarCoordChange_mul_coordinate τ' q q' (hτ x.property) hx',
    bergmanSection_apply, τ.continuousLinearMapAt_symmL (hτ x.property), q.apply_symm_apply]


/-- A different holomorphic frame can read a realized section after compact shrinking. The
actual transition factor appears in its representative, without a global bounded multiplier
or a Bergman-space isomorphism. -/
theorem bergmanRestriction_bergmanSection_coordinate
    (τ' : Trivialization F (π F V)) [τ'.IsLinear ℂ] (q' : F ≃L[ℂ] ℂ)
    (hτ'a : τ'.toOpenPartialHomeomorph ∈
      (contMDiffFiberwiseLinear X F 𝓘(ℂ) ω).maximalAtlas (TotalSpace F V))
    (hτ' : (U : Set X) ⊆ τ'.baseSet) (hK : IsCompact (closure (W : Set X)))
    (hKU : closure (W : Set X) ⊆ U) (u : bergmanSpace ℂ (e.imageOpens U)) (x : W) :
    BergmanSpace.representative
        (τ'.bergmanRestriction q' hτ'a he hU hτ' hK hKU
          (τ.bergmanSection q hτa he hU hτ u)) (e x) =
      τ.scalarCoordChange τ' q q' x * BergmanSpace.representative u (e x) := by
  rw [τ'.bergmanRestriction_apply]
  exact τ.bergmanSection_coordinate q hτa he hU hτ τ' q' u
    ⟨x, hKU (subset_closure x.property)⟩ (hτ' (hKU (subset_closure x.property)))

end Bundle.Trivialization

namespace TauCeti.RiemannSurface.ChartBergman

open Bundle

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
  {V : X → Type} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℂ (V x)] [∀ x, TopologicalSpace (V x)]
  [FiberBundle F V] [VectorBundle ℂ F V] [ContMDiffVectorBundle ω F V 𝓘(ℂ)]
  {ι : Type*} (τ : ι → Trivialization F (π F V)) [∀ i, Bundle.Trivialization.IsLinear ℂ (τ i)]
  (q : ι → F ≃L[ℂ] ℂ)
  (hτa : ∀ i, (τ i).toOpenPartialHomeomorph ∈
    (contMDiffFiberwiseLinear X F 𝓘(ℂ) ω).maximalAtlas (TotalSpace F V))
  {e : ι → OpenPartialHomeomorph X ℂ} (he : ∀ i, e i ∈ IsManifold.maximalAtlas 𝓘(ℂ) 1 X)
  {W W' W'' : ι → Opens X} (hW : ∀ i, (W i : Set X) ⊆ (e i).source)
  (hτ : ∀ i, (W i : Set X) ⊆ (τ i).baseSet)

/-- Realize a Bergman zero-cochain in the native bundle section sheaf using its actual frames. -/
def toBundleSections₀ :
    ((i : ι) → bergmanSpace ℂ ((e i).imageOpens (W i))) →ₗ[ℂ]
      ((i : ι) → (holomorphicSectionSheaf 𝓘(ℂ) F V).obj.obj (op (W i))) :=
  LinearMap.piMap fun i ↦ (τ i).bergmanSection (q i) (hτa i) (he i) (hW i) (hτ i)

/-- Realize a one-cochain in the frame of its first index, with no bounded frame-change
hypothesis. -/
def toBundleSections₁ :
    ((i j : ι) → bergmanSpace ℂ ((e i).imageOpens (W i ⊓ W j))) →ₗ[ℂ]
      ((i j : ι) → (holomorphicSectionSheaf 𝓘(ℂ) F V).obj.obj (op (W i ⊓ W j))) :=
  LinearMap.piMap fun i ↦ LinearMap.piMap fun j ↦
    (τ i).bergmanSection (q i) (hτa i) (he i) (inf_subset_source hW i j)
      (fun _ hx ↦ hτ i hx.1)

/-- The component of a realized zero-cochain is the native section in its chosen frame. -/
@[simp]
theorem toBundleSections₀_apply
    (η : (i : ι) → bergmanSpace ℂ ((e i).imageOpens (W i))) (i : ι) :
    toBundleSections₀ τ q hτa he hW hτ η i =
      (τ i).bergmanSection (q i) (hτa i) (he i) (hW i) (hτ i) (η i) := by rfl

/-- Each overlap component is realized in the actual frame of its first index. -/
@[simp]
theorem toBundleSections₁_apply
    (ξ : (i j : ι) → bergmanSpace ℂ ((e i).imageOpens (W i ⊓ W j))) (i j : ι) :
    toBundleSections₁ τ q hτa he hW hτ ξ i j =
      (τ i).bergmanSection (q i) (hτa i) (he i) (inf_subset_source hW i j)
        (fun _ hx ↦ hτ i hx.1) (ξ i j) := by rfl

/-- Each native zero-component retains its original Bergman class. -/
theorem toBundleSections₀_injective : Function.Injective (toBundleSections₀ τ q hτa he hW hτ) :=
  fun _ _ h ↦ funext fun i ↦ (τ i).bergmanSection_injective (q i) (hτa i)
    (he i) (hW i) (hτ i) (congrFun h i)

/-- Each native overlap component retains its original Bergman class. -/
theorem toBundleSections₁_injective : Function.Injective (toBundleSections₁ τ q hτa he hW hτ) :=
  fun _ _ h ↦ funext fun i ↦ funext fun j ↦ (τ i).bergmanSection_injective (q i) (hτa i)
    (he i) (inf_subset_source hW i j) _ (congrFun (congrFun h i) j)

/-- Restricting a zero-cochain commutes with its realization in native bundle sections. -/
theorem toBundleSections₀_restrictPi (h : ∀ i, W' i ≤ W i)
    (η : (i : ι) → bergmanSpace ℂ ((e i).imageOpens (W i))) (i : ι) :
    toBundleSections₀ τ q hτa he (subset_source_of_le hW h) (fun i _ hx ↦ hτ i (h i hx))
        (BergmanSpace.restrictPi (fun i ↦ OpenPartialHomeomorph.imageOpens_mono (h i)) η) i =
      (holomorphicSectionSheaf 𝓘(ℂ) F V).obj.map (homOfLE (h i)).op
        (toBundleSections₀ τ q hτa he hW hτ η i) :=
  (congrArg ((τ i).bergmanSection (q i) (hτa i) (he i) _ _)
    (BergmanSpace.restrictPi_apply _ η i)).trans
      ((τ i).bergmanSection_restrict (q i) (hτa i) (he i) (hW i) (hτ i) (h i) (η i))

/-- Bergman restriction of twisted one-cochains is native restriction on every overlap. -/
theorem toBundleSections₁_restrictCochains₁ (h : ∀ i, W' i ≤ W i)
    (ξ : (i j : ι) → bergmanSpace ℂ ((e i).imageOpens (W i ⊓ W j))) (i j : ι) :
    toBundleSections₁ τ q hτa he (subset_source_of_le hW h) (fun i _ hx ↦ hτ i (h i hx))
        (restrictCochains₁ h ξ) i j =
      (holomorphicSectionSheaf 𝓘(ℂ) F V).obj.map
        (homOfLE (inf_le_inf (h i) (h j))).op (toBundleSections₁ τ q hτa he hW hτ ξ i j) :=
  (congrArg ((τ i).bergmanSection (q i) (hτa i) (he i) _ _)
    (restrictCochains₁_apply h ξ i j)).trans
      ((τ i).bergmanSection_restrict (q i) (hτa i) (he i)
        (inf_subset_source hW i j) _ _ (ξ i j))

/-- The native cocycle identity has exactly the scalar transition factors computed from the
actual holomorphic frames. The scalar for `(i,j)` converts frame `j` into frame `i`. -/
theorem mem_cocycles₁_iff_toBundleSections₁_apply
    {ξ : (i j : ι) → bergmanSpace ℂ ((e i).imageOpens (W i ⊓ W j))} :
    ξ ∈ cocycles₁ (fun i j ↦ (τ j).scalarCoordChange (τ i) (q j) (q i)) hW ↔
      ∀ i j k, ∀ x (hx : x ∈ W i ⊓ W j ⊓ W k),
        toBundleSections₁ τ q hτa he hW hτ ξ j k ⟨x, hx.1.2, hx.2⟩ -
            toBundleSections₁ τ q hτa he hW hτ ξ i k ⟨x, hx.1.1, hx.2⟩ +
          toBundleSections₁ τ q hτa he hW hτ ξ i j ⟨x, hx.1⟩ = 0 := by
  rw [mem_cocycles₁_iff]
  refine forall₄_congr fun i j k x ↦ forall_congr' fun hx ↦ ?_
  let L := ((τ i).continuousLinearEquivAt ℂ x (hτ i hx.1.1)).trans (q i)
  rw [← L.map_eq_zero_iff]
  simp only [map_add, map_sub, L, ContinuousLinearEquiv.trans_apply,
    Trivialization.coe_continuousLinearEquivAt_eq, toBundleSections₁_apply]
  rw [(τ j).bergmanSection_coordinate (q j) (hτa j) (he j)
    (inf_subset_source hW j k) (fun _ hy ↦ hτ j hy.1) (τ i) (q i)
    (ξ j k) ⟨x, hx.1.2, hx.2⟩ (hτ i hx.1.1)]
  rw [(τ i).bergmanSection_coordinate_self (q i) (hτa i) (he i)
      (inf_subset_source hW i k) (fun _ hy ↦ hτ i hy.1) (ξ i k) ⟨x, hx.1.1, hx.2⟩,
    (τ i).bergmanSection_coordinate_self (q i) (hτa i) (he i)
      (inf_subset_source hW i j) (fun _ hy ↦ hτ i hy.1) (ξ i j) ⟨x, hx.1⟩]

/-- A native overlap section on a larger cover becomes square-integrable after shrinking
both indices. Compact containment of only one of the two opens is not assumed to suffice. -/
def bundleSections₁ToBergman (hK : ∀ i, IsCompact (closure (W' i : Set X)))
    (hKW : ∀ i, closure (W' i : Set X) ⊆ W i) :
    ((i j : ι) → (holomorphicSectionSheaf 𝓘(ℂ) F V).obj.obj (op (W i ⊓ W j))) →ₗ[ℂ]
      ((i j : ι) → bergmanSpace ℂ ((e i).imageOpens (W' i ⊓ W' j))) :=
  LinearMap.piMap fun i ↦ LinearMap.piMap fun j ↦
    (τ i).bergmanRestriction (q i) (hτa i) (he i) (inf_subset_source hW i j)
      (fun _ hx ↦ hτ i hx.1)
      ((hK i).of_isClosed_subset isClosed_closure (closure_mono inter_subset_left))
      (fun _ hx ↦ ⟨hKW i (closure_mono inter_subset_left hx),
        hKW j (closure_mono inter_subset_right hx)⟩)

omit [IsManifold 𝓘(ℂ) 1 X] in
/-- The reverse realization reads each native overlap section after compact shrinking in
both indices. -/
@[simp]
theorem bundleSections₁ToBergman_apply
    (hK : ∀ i, IsCompact (closure (W' i : Set X)))
    (hKW : ∀ i, closure (W' i : Set X) ⊆ W i)
    (s : (i j : ι) → (holomorphicSectionSheaf 𝓘(ℂ) F V).obj.obj (op (W i ⊓ W j)))
    (i j : ι) :
    bundleSections₁ToBergman τ q hτa he hW hτ hK hKW s i j =
      (τ i).bergmanRestriction (q i) (hτa i) (he i) (inf_subset_source hW i j)
        (fun _ hx ↦ hτ i hx.1)
        ((hK i).of_isClosed_subset isClosed_closure (closure_mono inter_subset_left))
        (fun _ hx ↦ ⟨hKW i (closure_mono inter_subset_left hx),
          hKW j (closure_mono inter_subset_right hx)⟩) (s i j) := by rfl

/-- A Bergman one-cochain, realized as native sections and read back after shrinking, is exactly
its canonical Bergman restriction. -/
theorem bundleSections₁ToBergman_toBundleSections₁
    (hK : ∀ i, IsCompact (closure (W' i : Set X)))
    (hKW : ∀ i, closure (W' i : Set X) ⊆ W i)
    (ξ : (i j : ι) → bergmanSpace ℂ ((e i).imageOpens (W i ⊓ W j))) :
    bundleSections₁ToBergman τ q hτa he hW hτ hK hKW
        (toBundleSections₁ τ q hτa he hW hτ ξ) =
      restrictCochains₁ (fun i ↦ subset_closure.trans (hKW i)) ξ := by
  funext i j
  rw [bundleSections₁ToBergman_apply τ q hτa he hW hτ hK hKW _ i j,
    toBundleSections₁_apply τ q hτa he hW hτ ξ i j,
    restrictCochains₁_apply (fun i ↦ subset_closure.trans (hKW i)) ξ i j]
  exact (τ i).bergmanRestriction_bergmanSection (q i) (hτa i) (he i)
    (inf_subset_source hW i j) _ _ _ (ξ i j)

/-- The compact-shrink realization of native overlaps returns exactly their native
restrictions, simultaneously in both indices. -/
theorem toBundleSections₁_bundleSections₁ToBergman
    (hK : ∀ i, IsCompact (closure (W' i : Set X)))
    (hKW : ∀ i, closure (W' i : Set X) ⊆ W i)
    (s : (i j : ι) → (holomorphicSectionSheaf 𝓘(ℂ) F V).obj.obj (op (W i ⊓ W j)))
    (i j : ι) :
    toBundleSections₁ τ q hτa he
        (subset_source_of_le hW fun i ↦ subset_closure.trans (hKW i))
        (fun i ↦ (subset_closure.trans (hKW i)).trans (hτ i))
        (bundleSections₁ToBergman τ q hτa he hW hτ hK hKW s) i j =
      (holomorphicSectionSheaf 𝓘(ℂ) F V).obj.map
        (homOfLE (inf_le_inf (subset_closure.trans (hKW i))
          (subset_closure.trans (hKW j)))).op (s i j) := by
  rw [toBundleSections₁_apply, bundleSections₁ToBergman_apply]
  exact (τ i).bergmanSection_bergmanRestriction (q i) (hτa i) (he i)
    (inf_subset_source hW i j) _ _ _ (s i j)

/-- Twisted scalar cocycles are precisely native section cocycles, with the three actual
presheaf restrictions to the triple overlap and the usual alternating signs. -/
theorem mem_cocycles₁_iff_toBundleSections₁
    {ξ : (i j : ι) → bergmanSpace ℂ ((e i).imageOpens (W i ⊓ W j))} :
    ξ ∈ cocycles₁ (fun i j ↦ (τ j).scalarCoordChange (τ i) (q j) (q i)) hW ↔
      ∀ i j k,
        (holomorphicSectionSheaf 𝓘(ℂ) F V).obj.map
            (homOfLE (show W i ⊓ W j ⊓ W k ≤ W j ⊓ W k from
              fun _ hx ↦ ⟨hx.1.2, hx.2⟩)).op (toBundleSections₁ τ q hτa he hW hτ ξ j k) -
          (holomorphicSectionSheaf 𝓘(ℂ) F V).obj.map
            (homOfLE (show W i ⊓ W j ⊓ W k ≤ W i ⊓ W k from
              fun _ hx ↦ ⟨hx.1.1, hx.2⟩)).op (toBundleSections₁ τ q hτa he hW hτ ξ i k) +
          (holomorphicSectionSheaf 𝓘(ℂ) F V).obj.map
            (homOfLE inf_le_left).op (toBundleSections₁ τ q hτa he hW hτ ξ i j) = 0 := by
  rw [mem_cocycles₁_iff_toBundleSections₁_apply τ q hτa he hW hτ]
  refine forall₃_congr fun i j k ↦ ?_
  rw [holomorphicSectionSheaf.ext_iff, Subtype.forall]
  simp only [holomorphicSectionSheaf.add_apply, holomorphicSectionSheaf.sub_apply,
    holomorphicSectionSheaf.map_apply, holomorphicSectionSheaf.zero_apply]

private theorem bundleSections_coboundary_iff
    (h' : ∀ i, W' i ≤ W i) (h'' : ∀ i, W'' i ≤ W' i)
    (t : ((i j : ι) → bergmanSpace ℂ ((e i).imageOpens (W i ⊓ W j))) ×
      ((i j : ι) → bergmanSpace ℂ ((e i).imageOpens (W' i ⊓ W' j))) ×
        ((i : ι) → bergmanSpace ℂ ((e i).imageOpens (W'' i))))
    (i j : ι) (x : X) (hx : x ∈ W'' i ⊓ W'' j) :
      BergmanSpace.representative (t.2.1 i j) (e i x) =
          BergmanSpace.representative (t.1 i j) (e i x) +
            ((τ j).scalarCoordChange (τ i) (q j) (q i) x *
              BergmanSpace.representative (t.2.2 j) (e j x) -
                BergmanSpace.representative (t.2.2 i) (e i x)) ↔
      toBundleSections₁ τ q hτa he (subset_source_of_le hW h')
          (fun i _ hx ↦ hτ i (h' i hx)) t.2.1 i j ⟨x, h'' i hx.1, h'' j hx.2⟩ =
        toBundleSections₁ τ q hτa he hW hτ t.1 i j
          ⟨x, h' i (h'' i hx.1), h' j (h'' j hx.2)⟩ +
        (toBundleSections₀ τ q hτa he
            (subset_source_of_le (subset_source_of_le hW h') h'')
            (fun i _ hx ↦ hτ i (h' i (h'' i hx))) t.2.2 j ⟨x, hx.2⟩ -
          toBundleSections₀ τ q hτa he
            (subset_source_of_le (subset_source_of_le hW h') h'')
            (fun i _ hx ↦ hτ i (h' i (h'' i hx))) t.2.2 i ⟨x, hx.1⟩) := by
  let L := ((τ i).continuousLinearEquivAt ℂ x (hτ i (h' i (h'' i hx.1)))).trans (q i)
  rw [← L.injective.eq_iff]
  simp only [map_add, map_sub, L, ContinuousLinearEquiv.trans_apply,
    Trivialization.coe_continuousLinearEquivAt_eq]
  -- Fix the nested-cover witnesses before rewriting their dependent section components.
  rw [toBundleSections₁_apply τ q hτa he (subset_source_of_le hW h')
      (fun i _ hx ↦ hτ i (h' i hx)) t.2.1 i j,
    toBundleSections₁_apply τ q hτa he hW hτ t.1 i j,
    toBundleSections₀_apply τ q hτa he
      (subset_source_of_le (subset_source_of_le hW h') h'')
      (fun i _ hx ↦ hτ i (h' i (h'' i hx))) t.2.2 j,
    toBundleSections₀_apply τ q hτa he
      (subset_source_of_le (subset_source_of_le hW h') h'')
      (fun i _ hx ↦ hτ i (h' i (h'' i hx))) t.2.2 i]
  rw [(τ j).bergmanSection_coordinate (q j) (hτa j) (he j)
    (subset_source_of_le (subset_source_of_le hW h') h'' j)
    (fun _ hy ↦ hτ j (h' j (h'' j hy))) (τ i) (q i) (t.2.2 j)
    ⟨x, hx.2⟩ (hτ i (h' i (h'' i hx.1)))]
  rw [(τ i).bergmanSection_coordinate_self (q i) (hτa i) (he i)
      (inf_subset_source (subset_source_of_le hW h') i j)
      (fun _ hy ↦ hτ i (h' i hy.1)) (t.2.1 i j) ⟨x, h'' i hx.1, h'' j hx.2⟩,
    (τ i).bergmanSection_coordinate_self (q i) (hτa i) (he i)
      (inf_subset_source hW i j) (fun _ hy ↦ hτ i hy.1) (t.1 i j)
      ⟨x, h' i (h'' i hx.1), h' j (h'' j hx.2)⟩,
    (τ i).bergmanSection_coordinate_self (q i) (hτa i) (he i)
      (subset_source_of_le (subset_source_of_le hW h') h'' i)
      (fun _ hy ↦ hτ i (h' i (h'' i hy))) (t.2.2 i) ⟨x, hx.1⟩]

/-- Compatible twisted triples have the actual native coboundary on the innermost overlaps.
No assertion that multiplication by the frame changes is bounded on the larger Bergman
spaces is needed. -/
theorem mem_compatibleTriples_iff_toBundleSections
    (h' : ∀ i, W' i ≤ W i) (h'' : ∀ i, W'' i ≤ W' i)
    {t : ((i j : ι) → bergmanSpace ℂ ((e i).imageOpens (W i ⊓ W j))) ×
      ((i j : ι) → bergmanSpace ℂ ((e i).imageOpens (W' i ⊓ W' j))) ×
        ((i : ι) → bergmanSpace ℂ ((e i).imageOpens (W'' i)))} :
    t ∈ compatibleTriples (fun i j ↦ (τ j).scalarCoordChange (τ i) (q j) (q i)) hW h' h'' ↔
      t.1 ∈ cocycles₁ (fun i j ↦ (τ j).scalarCoordChange (τ i) (q j) (q i)) hW ∧
      t.2.1 ∈ cocycles₁ (fun i j ↦ (τ j).scalarCoordChange (τ i) (q j) (q i))
        (subset_source_of_le hW h') ∧ ∀ i j,
      (holomorphicSectionSheaf 𝓘(ℂ) F V).obj.map
          (homOfLE (inf_le_inf (h'' i) (h'' j))).op
            (toBundleSections₁ τ q hτa he (subset_source_of_le hW h')
              (fun i _ hx ↦ hτ i (h' i hx)) t.2.1 i j) =
        (holomorphicSectionSheaf 𝓘(ℂ) F V).obj.map
            (homOfLE (inf_le_inf ((h'' i).trans (h' i)) ((h'' j).trans (h' j)))).op
            (toBundleSections₁ τ q hτa he hW hτ t.1 i j) +
          ((holomorphicSectionSheaf 𝓘(ℂ) F V).obj.map (homOfLE inf_le_right).op
              (toBundleSections₀ τ q hτa he
                (subset_source_of_le (subset_source_of_le hW h') h'')
                (fun i _ hx ↦ hτ i (h' i (h'' i hx))) t.2.2 j) -
            (holomorphicSectionSheaf 𝓘(ℂ) F V).obj.map (homOfLE inf_le_left).op
              (toBundleSections₀ τ q hτa he
                (subset_source_of_le (subset_source_of_le hW h') h'')
                (fun i _ hx ↦ hτ i (h' i (h'' i hx))) t.2.2 i)) := by
  rw [mem_compatibleTriples_iff]
  refine and_congr_right' (and_congr_right' (forall₂_congr fun i j ↦ ?_))
  rw [holomorphicSectionSheaf.ext_iff, Subtype.forall]
  simpa only [holomorphicSectionSheaf.add_apply, holomorphicSectionSheaf.sub_apply,
    holomorphicSectionSheaf.map_apply] using
      (forall₂_congr fun x hx ↦ bundleSections_coboundary_iff τ q hτa he hW hτ h' h'' t i j x hx)

end TauCeti.RiemannSurface.ChartBergman
