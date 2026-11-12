/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.HolomorphicFunctions.Bergman.Restriction
public import TauCeti.Analysis.Normed.Operator.Compact.Pi
public import TauCeti.Geometry.Manifold.Complex.StructureSheaf.Basic
public import TauCeti.Topology.OpenPartialHomeomorph.ChartOpens

/-!
# Square-integrable holomorphic Čech cochains on a Riemann surface

Let `X` be a Riemann surface with a finite family of holomorphic charts `e i` and opens
`W i ⊆ (e i).source`. A holomorphic Čech one-cochain of the cover `W` assigns to every ordered
pair `(i, j)`, repetitions allowed, a holomorphic function on `W i ∩ W j`. Reading it in the
first chart `e i` gives a holomorphic function on the plane open
`(e i).chartRead (W i ⊓ W j) = e i (W i ∩ W j)`. The square-integrable ones form the
Bergman space of that plane open, and the finite product of these Bergman spaces is the Banach
space of square-integrable one-cochains. Zero-cochains are read in the chart of their index.

This file constructs these spaces with the native holomorphic sections of the structure sheaf.

* `chartSection` sends a Bergman class read in a chart to the native section of the structure sheaf
  with the same values; it is complex linear and injective. `toSections₀` and `toSections₁` are the
  resulting injective realizations of cochains as families of native sections.
* A coordinate change need not preserve Lebesgue measure, and the hypotheses here do not guarantee
  that the Čech differential is a bounded map between the chart-read Bergman products. The cocycle
  condition is therefore stated as the vanishing of continuous point evaluations
  (`BergmanSpace.evalCLM`) on triple overlaps, which needs no such bound; `cocycles₁` is closed and
  complete, and its membership is the native cocycle identity of section values
  (`mem_cocycles₁_iff_toSections₁`).
* For a smaller family `W' i ⊆ W i` with the same charts, componentwise Bergman restriction is the
  native restriction of sections (`toSections₁_restrictCochains₁`), preserves cocycles, and is a
  compact operator when every `closure (W' i)` is compact and lies in `W i`
  (`isCompactOperator_restrictCocycles₁`).
* For three nested families `W'' ≤ W' ≤ W` with the same charts, `compatibleTriples` is the space of
  `(ξ, ξ', η)`, with `ξ` and `ξ'` square-integrable cocycles on `W` and `W'` and `η` a
  square-integrable zero-cochain on `W''`, such that `ξ' = ξ + δη` on `W''`, with the Čech
  convention `(δη)ᵢⱼ = ηⱼ - ηᵢ`. It is closed, hence complete
  (`isClosed_compatibleTriples`), and membership is the native coboundary identity
  (`mem_compatibleTriples_iff_toSections`).

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

open OpenPartialHomeomorph (chartRead_mono isCompact_closure_chartRead map_mem_chartRead
  mem_chartRead)

variable {X : Type} [TopologicalSpace X] {e : OpenPartialHomeomorph X ℂ} {V V' : Opens X}

/-! ### Square-integrable cochains of a chart family -/

namespace ChartBergman

variable {ι : Type*} {e : ι → OpenPartialHomeomorph X ℂ} {W W' W'' : ι → Opens X}

/-- Overlaps `W i ⊓ W j` lie in the source of the first chart. -/
theorem inf_subset_source (hW : ∀ i, (W i : Set X) ⊆ (e i).source) (i j : ι) :
    ((W i ⊓ W j : Opens X) : Set X) ⊆ (e i).source :=
  fun _ hx ↦ hW i hx.1

/-- The projection of a one-cochain to its component on the overlap `W i ⊓ W j`. -/
def proj₁ (i j : ι) :
    ((i j : ι) → bergmanSpace ℂ ((e i).chartRead (W i ⊓ W j))) →L[ℂ]
      bergmanSpace ℂ ((e i).chartRead (W i ⊓ W j)) :=
  (ContinuousLinearMap.proj (φ := fun j ↦ bergmanSpace ℂ ((e i).chartRead (W i ⊓ W j))) j).comp
    (ContinuousLinearMap.proj
      (φ := fun i ↦ (j : ι) → bergmanSpace ℂ ((e i).chartRead (W i ⊓ W j))) i)

@[simp]
theorem proj₁_apply (ξ : (i j : ι) → bergmanSpace ℂ ((e i).chartRead (W i ⊓ W j))) (i j : ι) :
    proj₁ i j ξ = ξ i j := (rfl)

variable (hW : ∀ i, (W i : Set X) ⊆ (e i).source)

/-- The Čech coboundary `ξⱼₖ - ξᵢₖ + ξᵢⱼ` of a one-cochain at a point `x` of a triple overlap, each
component evaluated in its own first chart. -/
private def cocycleEval (i j k : ι) {x : X} (hx : x ∈ W i ⊓ W j ⊓ W k) :
    ((i j : ι) → bergmanSpace ℂ ((e i).chartRead (W i ⊓ W j))) →L[ℂ] ℂ :=
  (BergmanSpace.evalCLM (map_mem_chartRead (inf_subset_source hW j k) ⟨hx.1.2, hx.2⟩)).comp
      (proj₁ j k) -
    (BergmanSpace.evalCLM (map_mem_chartRead (inf_subset_source hW i k) ⟨hx.1.1, hx.2⟩)).comp
      (proj₁ i k) +
    (BergmanSpace.evalCLM (map_mem_chartRead (inf_subset_source hW i j) hx.1)).comp (proj₁ i j)

/-- The square-integrable holomorphic Čech one-cocycles of the chart family. -/
def cocycles₁ : Submodule ℂ ((i j : ι) → bergmanSpace ℂ ((e i).chartRead (W i ⊓ W j))) :=
  ⨅ (i) (j) (k) (x) (hx : x ∈ W i ⊓ W j ⊓ W k),
    LinearMap.ker (cocycleEval hW i j k hx : _ →ₗ[ℂ] ℂ)

/-- A cochain is a cocycle when its chart-read representatives satisfy the Čech cocycle identity at
every point of every triple overlap. -/
theorem mem_cocycles₁_iff {ξ : (i j : ι) → bergmanSpace ℂ ((e i).chartRead (W i ⊓ W j))} :
    ξ ∈ cocycles₁ hW ↔ ∀ i j k, ∀ x ∈ W i ⊓ W j ⊓ W k,
      BergmanSpace.representative (ξ j k) (e j x) - BergmanSpace.representative (ξ i k) (e i x) +
        BergmanSpace.representative (ξ i j) (e i x) = 0 := by
  simp [cocycles₁, cocycleEval]

/-- Square-integrable cocycles form a closed subspace: they are cut out by continuous point
evaluations, so no bound on the coboundary map between different charts is needed. -/
theorem isClosed_cocycles₁ :
    IsClosed (cocycles₁ hW : Set ((i j : ι) → bergmanSpace ℂ ((e i).chartRead (W i ⊓ W j)))) := by
  simp only [cocycles₁, Submodule.coe_iInf]
  exact isClosed_iInter fun i ↦ isClosed_iInter fun j ↦ isClosed_iInter fun k ↦
    isClosed_iInter fun x ↦ isClosed_iInter fun hx ↦ (cocycleEval hW i j k hx).isClosed_ker

instance completeSpace_cocycles₁ : CompleteSpace (cocycles₁ hW) :=
  (isClosed_cocycles₁ hW).completeSpace_coe

/-! ### Restriction to a smaller family in the same charts -/

/-- Componentwise restriction of zero-cochains to a smaller family in the same charts. -/
def restrictCochains₀ (h : ∀ i, W' i ≤ W i) :
    ((i : ι) → bergmanSpace ℂ ((e i).chartRead (W i))) →L[ℂ]
      ((i : ι) → bergmanSpace ℂ ((e i).chartRead (W' i))) :=
  ContinuousLinearMap.piMap fun i ↦ BergmanSpace.restrict (chartRead_mono (h i))

omit hW in
@[simp]
theorem restrictCochains₀_apply (h : ∀ i, W' i ≤ W i)
    (η : (i : ι) → bergmanSpace ℂ ((e i).chartRead (W i))) (i : ι) :
    restrictCochains₀ h η i = BergmanSpace.restrict (chartRead_mono (h i)) (η i) := (rfl)

omit hW in
/-- Restricting zero-cochains to the same family is the identity. -/
@[simp]
theorem restrictCochains₀_refl :
    restrictCochains₀ (e := e) (W := W) (fun _ ↦ le_rfl) = ContinuousLinearMap.id ℂ _ :=
  ContinuousLinearMap.ext fun η ↦ funext fun i ↦ by simp

omit hW in
/-- Successive restrictions of zero-cochains agree with direct restriction. -/
theorem restrictCochains₀_comp (h' : ∀ i, W' i ≤ W i) (h'' : ∀ i, W'' i ≤ W' i) :
    (restrictCochains₀ h'').comp (restrictCochains₀ h') =
      restrictCochains₀ (e := e) fun i ↦ (h'' i).trans (h' i) :=
  ContinuousLinearMap.ext fun η ↦ funext fun i ↦
    DFunLike.congr_fun (BergmanSpace.restrict_comp_restrict _ _) (η i)

/-- Componentwise restriction of one-cochains to a smaller family in the same charts. -/
def restrictCochains₁ (h : ∀ i, W' i ≤ W i) :
    ((i j : ι) → bergmanSpace ℂ ((e i).chartRead (W i ⊓ W j))) →L[ℂ]
      ((i j : ι) → bergmanSpace ℂ ((e i).chartRead (W' i ⊓ W' j))) :=
  ContinuousLinearMap.piMap fun i ↦ ContinuousLinearMap.piMap fun j ↦
    BergmanSpace.restrict (chartRead_mono (inf_le_inf (h i) (h j)))

omit hW in
@[simp]
theorem restrictCochains₁_apply (h : ∀ i, W' i ≤ W i)
    (ξ : (i j : ι) → bergmanSpace ℂ ((e i).chartRead (W i ⊓ W j))) (i j : ι) :
    restrictCochains₁ h ξ i j = BergmanSpace.restrict (chartRead_mono (inf_le_inf (h i) (h j)))
      (ξ i j) := (rfl)

omit hW in
/-- Restricting one-cochains to the same family is the identity. -/
@[simp]
theorem restrictCochains₁_refl :
    restrictCochains₁ (e := e) (W := W) (fun _ ↦ le_rfl) = ContinuousLinearMap.id ℂ _ :=
  ContinuousLinearMap.ext fun ξ ↦ funext fun i ↦ funext fun j ↦ by simp

omit hW in
/-- Successive restrictions of one-cochains agree with direct restriction. -/
theorem restrictCochains₁_comp (h' : ∀ i, W' i ≤ W i) (h'' : ∀ i, W'' i ≤ W' i) :
    (restrictCochains₁ h'').comp (restrictCochains₁ h') =
      restrictCochains₁ (e := e) fun i ↦ (h'' i).trans (h' i) :=
  ContinuousLinearMap.ext fun ξ ↦ funext fun i ↦ funext fun j ↦
    DFunLike.congr_fun (BergmanSpace.restrict_comp_restrict _ _) (ξ i j)

/-- Restricting a cocycle to a smaller family in the same charts gives a cocycle. -/
theorem restrictCochains₁_mem_cocycles₁ (h : ∀ i, W' i ≤ W i)
    (hW' : ∀ i, (W' i : Set X) ⊆ (e i).source) {ξ} (hξ : ξ ∈ cocycles₁ hW) :
    restrictCochains₁ h ξ ∈ cocycles₁ hW' := by
  rw [mem_cocycles₁_iff] at hξ ⊢
  intro i j k x hx
  have hjk := map_mem_chartRead (inf_subset_source hW' j k) ⟨hx.1.2, hx.2⟩
  have hik := map_mem_chartRead (inf_subset_source hW' i k) ⟨hx.1.1, hx.2⟩
  have hij := map_mem_chartRead (inf_subset_source hW' i j) hx.1
  simpa only [restrictCochains₁_apply, BergmanSpace.representative_restrict _ _ hjk,
    BergmanSpace.representative_restrict _ _ hik, BergmanSpace.representative_restrict _ _ hij]
    using hξ i j k x ⟨⟨h i hx.1.1, h j hx.1.2⟩, h k hx.2⟩

/-- Restriction between the closed spaces of square-integrable cocycles. -/
def restrictCocycles₁ (h : ∀ i, W' i ≤ W i) (hW' : ∀ i, (W' i : Set X) ⊆ (e i).source) :
    cocycles₁ hW →L[ℂ] cocycles₁ hW' :=
  ((restrictCochains₁ h).comp (cocycles₁ hW).subtypeL).codRestrict _ fun ξ ↦
    restrictCochains₁_mem_cocycles₁ hW h hW' ξ.property

@[simp]
theorem coe_restrictCocycles₁ (h : ∀ i, W' i ≤ W i) (hW' : ∀ i, (W' i : Set X) ⊆ (e i).source)
    (ξ : cocycles₁ hW) :
    (restrictCocycles₁ hW h hW' ξ : (i j : ι) → bergmanSpace ℂ ((e i).chartRead (W' i ⊓ W' j))) =
      restrictCochains₁ h ξ.val := (rfl)

/-- Restricting cocycles to the same family is the identity. -/
@[simp]
theorem restrictCocycles₁_refl :
    restrictCocycles₁ hW (fun _ ↦ le_rfl) hW = ContinuousLinearMap.id ℂ _ :=
  ContinuousLinearMap.ext fun ξ ↦ Subtype.ext <| by simp

/-- Successive restrictions of cocycles agree with direct restriction. -/
theorem restrictCocycles₁_comp (h' : ∀ i, W' i ≤ W i) (hW' : ∀ i, (W' i : Set X) ⊆ (e i).source)
    (h'' : ∀ i, W'' i ≤ W' i) (hW'' : ∀ i, (W'' i : Set X) ⊆ (e i).source) :
    (restrictCocycles₁ hW' h'' hW'').comp (restrictCocycles₁ hW h' hW') =
      restrictCocycles₁ hW (fun i ↦ (h'' i).trans (h' i)) hW'' :=
  ContinuousLinearMap.ext fun ξ ↦ Subtype.ext <|
    DFunLike.congr_fun (restrictCochains₁_comp h' h'') ξ.val

section Compact

variable [Finite ι]

include hW in
/-- If each `closure (W' i)` is compact and lies in `W i`, restriction of one-cochains is a compact
operator. -/
theorem isCompactOperator_restrictCochains₁ (hK : ∀ i, IsCompact (closure (W' i : Set X)))
    (hKW : ∀ i, closure (W' i : Set X) ⊆ W i) :
    IsCompactOperator (restrictCochains₁ (e := e) fun i ↦ subset_closure.trans (hKW i)) := by
  apply IsCompactOperator.pi
  intro i
  apply IsCompactOperator.pi
  intro j
  have hKij : IsCompact (closure ((W' i ⊓ W' j : Opens X) : Set X)) :=
    (hK i).of_isClosed_subset isClosed_closure (closure_mono inter_subset_left)
  have hKWij : closure ((W' i ⊓ W' j : Opens X) : Set X) ⊆ (W i ⊓ W j : Opens X) :=
    fun x hx ↦ ⟨hKW i (closure_mono inter_subset_left hx),
      hKW j (closure_mono inter_subset_right hx)⟩
  obtain ⟨hc, hsub⟩ := isCompact_closure_chartRead (inf_subset_source hW i j) hKij hKWij
  exact (BergmanSpace.isCompactOperator_restrict (F := ℂ) hc hsub).comp_clm (proj₁ i j)

/-- If each `closure (W' i)` is compact and lies in `W i`, restriction of square-integrable
cocycles is a compact operator. -/
theorem isCompactOperator_restrictCocycles₁ (hK : ∀ i, IsCompact (closure (W' i : Set X)))
    (hKW : ∀ i, closure (W' i : Set X) ⊆ W i) (hW' : ∀ i, (W' i : Set X) ⊆ (e i).source) :
    IsCompactOperator
      (restrictCocycles₁ hW (fun i ↦ subset_closure.trans (hKW i)) hW') :=
  ((isCompactOperator_restrictCochains₁ hW hK hKW).comp_clm (cocycles₁ hW).subtypeL).codRestrict
    (fun ξ ↦ restrictCochains₁_mem_cocycles₁ hW _ hW' ξ.property) (isClosed_cocycles₁ hW')

end Compact

/-! ### Compatible triples -/

omit hW in
/-- A smaller family lies in the chart sources. -/
theorem subset_source_of_le (hW' : ∀ i, (W' i : Set X) ⊆ (e i).source)
    (h'' : ∀ i, W'' i ≤ W' i) (i : ι) : (W'' i : Set X) ⊆ (e i).source :=
  (SetLike.coe_subset_coe.2 (h'' i)).trans (hW' i)

variable (hW' : ∀ i, (W' i : Set X) ⊆ (e i).source) (h' : ∀ i, W' i ≤ W i)
  (h'' : ∀ i, W'' i ≤ W' i)

/-- The defect of `ξ' = ξ + δη` at a point of an overlap `W'' i ⊓ W'' j`, as a continuous linear
functional of the triple of cochains `(ξ, ξ', η)`. -/
private def tripleEval (i j : ι) {x : X} (hx : x ∈ W'' i ⊓ W'' j) :
    (((i j : ι) → bergmanSpace ℂ ((e i).chartRead (W i ⊓ W j))) ×
      ((i j : ι) → bergmanSpace ℂ ((e i).chartRead (W' i ⊓ W' j))) ×
        ((i : ι) → bergmanSpace ℂ ((e i).chartRead (W'' i)))) →L[ℂ] ℂ :=
  (BergmanSpace.evalCLM (map_mem_chartRead (inf_subset_source hW' i j)
      ⟨h'' i hx.1, h'' j hx.2⟩)).comp ((proj₁ i j).comp
        ((ContinuousLinearMap.fst ℂ _ _).comp (ContinuousLinearMap.snd ℂ _ _))) -
    (BergmanSpace.evalCLM (map_mem_chartRead (inf_subset_source hW i j)
      ⟨h' i (h'' i hx.1), h' j (h'' j hx.2)⟩)).comp
        ((proj₁ i j).comp (ContinuousLinearMap.fst ℂ _ _)) -
    (BergmanSpace.evalCLM (map_mem_chartRead (subset_source_of_le hW' h'' j) hx.2)).comp
      ((ContinuousLinearMap.proj j).comp
        ((ContinuousLinearMap.snd ℂ _ _).comp (ContinuousLinearMap.snd ℂ _ _))) +
    (BergmanSpace.evalCLM (map_mem_chartRead (subset_source_of_le hW' h'' i) hx.1)).comp
      ((ContinuousLinearMap.proj i).comp
        ((ContinuousLinearMap.snd ℂ _ _).comp (ContinuousLinearMap.snd ℂ _ _)))

/-- The compatible triples `(ξ, ξ', η)`: square-integrable cocycles `ξ` on `W` and `ξ'` on `W'`, and
a square-integrable zero-cochain `η` on `W''`, with `ξ' = ξ + δη` on `W''`, where
`(δη)ᵢⱼ = ηⱼ - ηᵢ`. -/
def compatibleTriples :
    Submodule ℂ (((i j : ι) → bergmanSpace ℂ ((e i).chartRead (W i ⊓ W j))) ×
      ((i j : ι) → bergmanSpace ℂ ((e i).chartRead (W' i ⊓ W' j))) ×
        ((i : ι) → bergmanSpace ℂ ((e i).chartRead (W'' i)))) :=
  (cocycles₁ hW).prod ((cocycles₁ hW').prod ⊤) ⊓
    ⨅ (i) (j) (x) (hx : x ∈ W'' i ⊓ W'' j),
      LinearMap.ker (tripleEval hW hW' h' h'' i j hx : _ →ₗ[ℂ] ℂ)

/-- A triple is compatible when `ξ` and `ξ'` are cocycles and the chart-read representatives
satisfy `ξ'ᵢⱼ = ξᵢⱼ + ηⱼ - ηᵢ` at every point of every overlap of `W''`. -/
theorem mem_compatibleTriples_iff
    {t : ((i j : ι) → bergmanSpace ℂ ((e i).chartRead (W i ⊓ W j))) ×
      ((i j : ι) → bergmanSpace ℂ ((e i).chartRead (W' i ⊓ W' j))) ×
        ((i : ι) → bergmanSpace ℂ ((e i).chartRead (W'' i)))} :
    t ∈ compatibleTriples hW hW' h' h'' ↔ t.1 ∈ cocycles₁ hW ∧ t.2.1 ∈ cocycles₁ hW' ∧
      ∀ i j, ∀ x ∈ W'' i ⊓ W'' j,
        BergmanSpace.representative (t.2.1 i j) (e i x) =
          BergmanSpace.representative (t.1 i j) (e i x) +
            (BergmanSpace.representative (t.2.2 j) (e j x) -
              BergmanSpace.representative (t.2.2 i) (e i x)) := by
  simp only [compatibleTriples, Submodule.mem_inf, Submodule.mem_prod, Submodule.mem_top,
    and_true, Submodule.mem_iInf, LinearMap.mem_ker, and_assoc]
  refine and_congr_right' (and_congr_right' (forall₄_congr fun i j x hx ↦ ?_))
  simp only [tripleEval, ContinuousLinearMap.coe_coe, add_apply, sub_apply,
    ContinuousLinearMap.comp_apply, BergmanSpace.evalCLM_apply, proj₁_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', ContinuousLinearMap.proj_apply]
  constructor <;> intro h <;> linear_combination h

/-- The compatible triples form a closed subspace, cut out by continuous point evaluations. -/
theorem isClosed_compatibleTriples :
    IsClosed (compatibleTriples hW hW' h' h'' :
      Set (((i j : ι) → bergmanSpace ℂ ((e i).chartRead (W i ⊓ W j))) ×
        ((i j : ι) → bergmanSpace ℂ ((e i).chartRead (W' i ⊓ W' j))) ×
          ((i : ι) → bergmanSpace ℂ ((e i).chartRead (W'' i))))) := by
  simp only [compatibleTriples, Submodule.coe_inf, Submodule.coe_iInf]
  refine IsClosed.inter ((isClosed_cocycles₁ hW).prod ((isClosed_cocycles₁ hW').prod
    isClosed_univ)) ?_
  exact isClosed_iInter fun i ↦ isClosed_iInter fun j ↦ isClosed_iInter fun x ↦
    isClosed_iInter fun hx ↦ (tripleEval hW hW' h' h'' i j hx).isClosed_ker

instance completeSpace_compatibleTriples : CompleteSpace (compatibleTriples hW hW' h' h'') :=
  (isClosed_compatibleTriples hW hW' h' h'').completeSpace_coe

end ChartBergman

/-! ### Native sections from chart-read Bergman classes -/

variable [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]

/-- A Bergman class on the plane open read from `V ⊆ e.source`, as the native holomorphic section
`x ↦ u (e x)` of the structure sheaf over `V`. -/
def chartSection (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ) 1 X) (hV : (V : Set X) ⊆ e.source) :
    bergmanSpace ℂ (e.chartRead V) →ₗ[ℂ]
      (holomorphicStructureSheafModules 𝓘(ℂ) X).obj.obj (op V) where
  toFun u := holomorphicStructureSheafModules.ofContMDiff
    (fun x : V ↦ BergmanSpace.representative u (e x)) <| MDifferentiable.contMDiff fun x ↦
      ((BergmanSpace.differentiableOn_representative u).differentiableAt
        ((e.chartRead V).isOpen.mem_nhds (map_mem_chartRead hV x.2))).mdifferentiableAt.comp x
        ((mdifferentiableAt_of_mem_maximalAtlas he (hV x.2)).comp x
          (contMDiff_subtype_val.mdifferentiable one_ne_zero x))
  map_add' u v := by
    ext x
    simp [BergmanSpace.representative_add _ _ (map_mem_chartRead hV x.2)]
  map_smul' c u := by
    ext x
    simp [BergmanSpace.representative_smul _ _ (map_mem_chartRead hV x.2)]

@[simp]
theorem chartSection_apply (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ) 1 X)
    (hV : (V : Set X) ⊆ e.source) (u : bergmanSpace ℂ (e.chartRead V)) (x : V) :
    chartSection he hV u x = BergmanSpace.representative u (e x) :=
  holomorphicStructureSheafModules.ofContMDiff_apply _ _ x

/-- A chart-read Bergman class is determined by its native section. -/
theorem chartSection_injective (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ) 1 X)
    (hV : (V : Set X) ⊆ e.source) : Function.Injective (chartSection he hV) := by
  intro u v h
  apply BergmanSpace.ext
  intro z hz
  obtain ⟨hzt, hzV⟩ := mem_chartRead.1 hz
  have := congrArg (fun s ↦ s ⟨e.symm z, hzV⟩) h
  simp only at this
  rwa [chartSection_apply, chartSection_apply, e.right_inv hzt] at this

/-- Restricting a chart-read Bergman class to a smaller open read in the same chart is the native
restriction of its section. -/
theorem chartSection_restrict (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ) 1 X)
    (hV : (V : Set X) ⊆ e.source) (h : V' ≤ V) (u : bergmanSpace ℂ (e.chartRead V)) :
    chartSection he ((SetLike.coe_subset_coe.2 h).trans hV)
        (BergmanSpace.restrict (chartRead_mono h) u) =
      (holomorphicStructureSheafModules 𝓘(ℂ) X).obj.map (homOfLE h).op (chartSection he hV u) := by
  ext x
  rw [holomorphicStructureSheafModules.map_apply, chartSection_apply, chartSection_apply]
  exact BergmanSpace.representative_restrict _ _
    (map_mem_chartRead ((SetLike.coe_subset_coe.2 h).trans hV) x.2)

namespace ChartBergman

variable {ι : Type*} {e : ι → OpenPartialHomeomorph X ℂ} {W W' W'' : ι → Opens X}
  (he : ∀ i, e i ∈ IsManifold.maximalAtlas 𝓘(ℂ) 1 X) (hW : ∀ i, (W i : Set X) ⊆ (e i).source)

/-- Square-integrable zero-cochains realized as native sections over the `W i`. -/
def toSections₀ :
    ((i : ι) → bergmanSpace ℂ ((e i).chartRead (W i))) →ₗ[ℂ]
      ((i : ι) → (holomorphicStructureSheafModules 𝓘(ℂ) X).obj.obj (op (W i))) :=
  LinearMap.piMap fun i ↦ chartSection (he i) (hW i)

/-- Square-integrable one-cochains realized as native sections over the overlaps `W i ⊓ W j`. -/
def toSections₁ :
    ((i j : ι) → bergmanSpace ℂ ((e i).chartRead (W i ⊓ W j))) →ₗ[ℂ]
      ((i j : ι) → (holomorphicStructureSheafModules 𝓘(ℂ) X).obj.obj (op (W i ⊓ W j))) :=
  LinearMap.piMap fun i ↦ LinearMap.piMap fun j ↦
    chartSection (he i) (inf_subset_source hW i j)

@[simp]
theorem toSections₀_apply (η : (i : ι) → bergmanSpace ℂ ((e i).chartRead (W i))) (i : ι)
    (x : W i) : toSections₀ he hW η i x = BergmanSpace.representative (η i) (e i x) :=
  chartSection_apply (he i) (hW i) _ x

@[simp]
theorem toSections₁_apply (ξ : (i j : ι) → bergmanSpace ℂ ((e i).chartRead (W i ⊓ W j)))
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

/-- The cocycle condition is the native cocycle identity for the realized sections. -/
theorem mem_cocycles₁_iff_toSections₁
    {ξ : (i j : ι) → bergmanSpace ℂ ((e i).chartRead (W i ⊓ W j))} :
    ξ ∈ cocycles₁ hW ↔ ∀ i j k, ∀ x (hx : x ∈ W i ⊓ W j ⊓ W k),
      toSections₁ he hW ξ j k ⟨x, hx.1.2, hx.2⟩ - toSections₁ he hW ξ i k ⟨x, hx.1.1, hx.2⟩ +
        toSections₁ he hW ξ i j ⟨x, hx.1⟩ = 0 := by
  rw [mem_cocycles₁_iff]
  refine forall₄_congr fun i j k x ↦ forall_congr' fun hx ↦ ?_
  rw [toSections₁_apply, toSections₁_apply, toSections₁_apply]

/-- Restriction of zero-cochains is the native restriction of their sections. -/
theorem toSections₀_restrictCochains₀ (h : ∀ i, W' i ≤ W i)
    (η : (i : ι) → bergmanSpace ℂ ((e i).chartRead (W i))) (i : ι) :
    toSections₀ he (subset_source_of_le hW h) (restrictCochains₀ h η) i =
      (holomorphicStructureSheafModules 𝓘(ℂ) X).obj.map (homOfLE (h i)).op
        (toSections₀ he hW η i) :=
  chartSection_restrict (he i) (hW i) (h i) (η i)

/-- Restriction of one-cochains is the native restriction of their sections. -/
theorem toSections₁_restrictCochains₁ (h : ∀ i, W' i ≤ W i)
    (ξ : (i j : ι) → bergmanSpace ℂ ((e i).chartRead (W i ⊓ W j))) (i j : ι) :
    toSections₁ he (subset_source_of_le hW h) (restrictCochains₁ h ξ) i j =
      (holomorphicStructureSheafModules 𝓘(ℂ) X).obj.map (homOfLE (inf_le_inf (h i) (h j))).op
        (toSections₁ he hW ξ i j) :=
  chartSection_restrict (he i) (inf_subset_source hW i j) _ (ξ i j)

/-- A triple is compatible when `ξ` and `ξ'` are cocycles and the native sections satisfy
`ξ' = ξ + δη` over each overlap `W'' i ⊓ W'' j`, with `(δη)ᵢⱼ = ηⱼ - ηᵢ`. -/
theorem mem_compatibleTriples_iff_toSections (hW' : ∀ i, (W' i : Set X) ⊆ (e i).source)
    (h' : ∀ i, W' i ≤ W i) (h'' : ∀ i, W'' i ≤ W' i)
    {t : ((i j : ι) → bergmanSpace ℂ ((e i).chartRead (W i ⊓ W j))) ×
      ((i j : ι) → bergmanSpace ℂ ((e i).chartRead (W' i ⊓ W' j))) ×
        ((i : ι) → bergmanSpace ℂ ((e i).chartRead (W'' i)))} :
    t ∈ compatibleTriples hW hW' h' h'' ↔ t.1 ∈ cocycles₁ hW ∧ t.2.1 ∈ cocycles₁ hW' ∧ ∀ i j,
      (holomorphicStructureSheafModules 𝓘(ℂ) X).obj.map
          (homOfLE (inf_le_inf (h'' i) (h'' j))).op (toSections₁ he hW' t.2.1 i j) =
        (holomorphicStructureSheafModules 𝓘(ℂ) X).obj.map
            (homOfLE (inf_le_inf ((h'' i).trans (h' i)) ((h'' j).trans (h' j)))).op
            (toSections₁ he hW t.1 i j) +
          ((holomorphicStructureSheafModules 𝓘(ℂ) X).obj.map (homOfLE inf_le_right).op
              (toSections₀ he (subset_source_of_le hW' h'') t.2.2 j) -
            (holomorphicStructureSheafModules 𝓘(ℂ) X).obj.map (homOfLE inf_le_left).op
              (toSections₀ he (subset_source_of_le hW' h'') t.2.2 i)) := by
  rw [mem_compatibleTriples_iff]
  refine and_congr_right' (and_congr_right' (forall₂_congr fun i j ↦ ?_))
  rw [holomorphicStructureSheafModules.ext_iff, Subtype.forall]
  refine forall₂_congr fun x hx ↦ ?_
  simp only [holomorphicStructureSheafModules.add_apply, holomorphicStructureSheafModules.sub_apply,
    holomorphicStructureSheafModules.map_apply]
  rw [toSections₁_apply, toSections₁_apply, toSections₀_apply, toSections₀_apply]

end ChartBergman

end TauCeti.RiemannSurface
