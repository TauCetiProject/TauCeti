/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.HolomorphicFunctions.Bergman.Restriction
public import TauCeti.Geometry.Manifold.Complex.StructureSheaf.Basic
public import TauCeti.Topology.OpenPartialHomeomorph.ChartOpens
import TauCeti.Geometry.Manifold.MFDeriv.Opens

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

These are the analytic Banach stages of the finiteness theorem for `H¹(X, 𝒪)`; the surjectivity of
the projection of `compatibleTriples` to its middle cocycle, the Schwartz argument and the
comparison with native Čech cohomology are not part of this file.

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
    simp [BergmanSpace.representative_add _ _ (map_mem_imageOpens (hV x.2) x.2)]
  map_smul' c u := by
    ext x
    simp [BergmanSpace.representative_smul _ _ (map_mem_imageOpens (hV x.2) x.2)]

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
    (map_mem_imageOpens (hV (h x.2)) x.2)

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
