/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Topology.VectorBundle.Constructions
public import Mathlib.Topology.VectorBundle.Hom
import TauCeti.Topology.Algebra.Module.BilinearForm
import TauCeti.Topology.VectorBundle.Section
import TauCeti.Topology.VectorBundle.Smul

/-!
# Evaluation, positivity, and comparison in bilinear bundles

For a finite-rank real vector bundle, strict diagonal positivity is an open condition in the
total space of the bilinear bundle. No symmetry condition is included: symmetric positive forms
are open relative to the symmetric subbundle, rather than in the full bilinear bundle.

Consequently a continuous family of bilinear fields that is positive at one parameter on a
compact subset of the base remains positive there for nearby parameters. This applies to
families of symmetric fields when constructing and perturbing Riemannian metrics. The bundle
fibres need only carry their original topological vector space structures; no background metric
or choice of norms on the fibres is required.

The file also records that pulling back a fixed bilinear form on the model fibre along a
trivialization gives a bilinear field continuous on its base set
(`TauCeti.continuousOn_trivializationAt_pullbackForm`), the local building block for continuous
Riemannian metrics.

Bilinear evaluation on two continuous maps into the fibres is continuous, over any
nontrivially normed field and with any normed-space codomain (`Continuous.bilin_bundle_apply`
and its within-at, at, and on variants). Diagonal evaluation is `ContinuousOn.bilin_bundle_self`.
For finite-rank real bundles, two bilinear fields continuous and positive on a compact set
have uniform positive two-sided comparison constants
(`IsCompact.exists_pos_mul_bilin_self_le_and_le`). No fibre norm instances, symmetry, or
positivity outside the compact set are needed.

The openness proof uses the matrix-cone openness theorem
`TauCeti.isOpen_setOfPred_re_dotProduct_pos`, transported through a basis and the native
iterated hom-bundle trivializations.
-/

public section

noncomputable section

open Bundle ContinuousLinearMap Filter Set
open scoped Topology

section Evaluation

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {B : Type*} [TopologicalSpace B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {E : B → Type*} [TopologicalSpace (TotalSpace F E)]
  [∀ x, TopologicalSpace (E x)] [∀ x, AddCommGroup (E x)] [∀ x, Module 𝕜 (E x)]
  [FiberBundle F E] [VectorBundle 𝕜 F E]
  {X : Type*} [TopologicalSpace X] {f : X → B} {v w : ∀ x, E (f x)}
  {ψ : ∀ x, E (f x) →L[𝕜] E (f x) →L[𝕜] G} {s : Set X} {x : X}

/-- Evaluation of a bilinear field on two maps into its fibres is continuous within a set. -/
theorem ContinuousWithinAt.bilin_bundle_apply
    (hψ : ContinuousWithinAt (fun x ↦ TotalSpace.mk' (F →L[𝕜] F →L[𝕜] G)
      (E := fun y ↦ E y →L[𝕜] E y →L[𝕜] G) (f x) (ψ x)) s x)
    (hv : ContinuousWithinAt (fun x ↦ (v x : TotalSpace F E)) s x)
    (hw : ContinuousWithinAt (fun x ↦ (w x : TotalSpace F E)) s x) :
    ContinuousWithinAt (fun x ↦ ψ x (v x) (w x)) s x :=
  continuous_snd.continuousAt.comp_continuousWithinAt
    ((Bundle.Trivial.homeomorphProd B G).continuous.continuousAt.comp_continuousWithinAt
      (hψ.clm_bundle_apply₂ hv hw))

/-- Evaluation of a bilinear field on two maps into its fibres is continuous at a point. -/
theorem ContinuousAt.bilin_bundle_apply
    (hψ : ContinuousAt (fun x ↦ TotalSpace.mk' (F →L[𝕜] F →L[𝕜] G)
      (E := fun y ↦ E y →L[𝕜] E y →L[𝕜] G) (f x) (ψ x)) x)
    (hv : ContinuousAt (fun x ↦ (v x : TotalSpace F E)) x)
    (hw : ContinuousAt (fun x ↦ (w x : TotalSpace F E)) x) :
    ContinuousAt (fun x ↦ ψ x (v x) (w x)) x := by
  simp only [← continuousWithinAt_univ] at hψ hv hw ⊢
  exact hψ.bilin_bundle_apply hv hw

/-- Evaluation of a bilinear field on two maps into its fibres is continuous on a set. -/
theorem ContinuousOn.bilin_bundle_apply
    (hψ : ContinuousOn (fun x ↦ TotalSpace.mk' (F →L[𝕜] F →L[𝕜] G)
      (E := fun y ↦ E y →L[𝕜] E y →L[𝕜] G) (f x) (ψ x)) s)
    (hv : ContinuousOn (fun x ↦ (v x : TotalSpace F E)) s)
    (hw : ContinuousOn (fun x ↦ (w x : TotalSpace F E)) s) :
    ContinuousOn (fun x ↦ ψ x (v x) (w x)) s :=
  fun x hx ↦ (hψ x hx).bilin_bundle_apply (hv x hx) (hw x hx)

/-- Evaluation of a bilinear field on two continuous maps into its fibres is continuous. -/
theorem Continuous.bilin_bundle_apply
    (hψ : Continuous (fun x ↦ TotalSpace.mk' (F →L[𝕜] F →L[𝕜] G)
      (E := fun y ↦ E y →L[𝕜] E y →L[𝕜] G) (f x) (ψ x)))
    (hv : Continuous (fun x ↦ (v x : TotalSpace F E)))
    (hw : Continuous (fun x ↦ (w x : TotalSpace F E))) :
    Continuous (fun x ↦ ψ x (v x) (w x)) :=
  continuous_iff_continuousAt.2 fun _ ↦ hψ.continuousAt.bilin_bundle_apply
    hv.continuousAt hw.continuousAt

/-- Diagonal evaluation of a continuous bilinear field is continuous over its domain. -/
theorem ContinuousOn.bilin_bundle_self {K : Set B}
    {b : ∀ x, E x →L[𝕜] E x →L[𝕜] G}
    (hb : ContinuousOn (fun x ↦ TotalSpace.mk' (F →L[𝕜] F →L[𝕜] G) x (b x)) K) :
    ContinuousOn (fun z : TotalSpace F E ↦ b z.proj z.snd z.snd) (TotalSpace.proj ⁻¹' K) :=
  (hb.comp (FiberBundle.continuous_proj F E).continuousOn (fun _ hz ↦ hz)).bilin_bundle_apply
    continuousOn_id continuousOn_id

end Evaluation

namespace TauCeti

variable {B : Type*} [TopologicalSpace B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : B → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, TopologicalSpace (V x)] [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V]

/-- Reading a real bilinear form in a bundle chart preserves and reflects strict diagonal
positivity wherever the chart is defined. -/
@[simp]
theorem forall_inCoordinates_bilinear_apply_self_pos_iff {x₀ x : B}
    (hx : x ∈ (trivializationAt F V x₀).baseSet) (b : V x →L[ℝ] V x →L[ℝ] ℝ) :
    (∀ v : F, v ≠ 0 →
      0 < inCoordinates F V (F →L[ℝ] ℝ) (fun y ↦ V y →L[ℝ] ℝ) x₀ x x₀ x b v v) ↔
      ∀ v : V x, v ≠ 0 → 0 < b v v := by
  let e := (trivializationAt F V x₀).continuousLinearEquivAt ℝ x hx
  have heval (v w : F) :
      inCoordinates F V (F →L[ℝ] ℝ) (fun y ↦ V y →L[ℝ] ℝ) x₀ x x₀ x b v w =
        b (e.symm v) (e.symm w) := by
    rw [inCoordinates_apply_eq₂ hx hx (by simp)]
    simp [e]
  simp only [heval]
  constructor
  · intro h v hv
    simpa using h (e v) (by simpa using hv)
  · intro h v hv
    exact h (e.symm v) (by simpa using hv)

/-- The field of bilinear forms `b ↦ φ (e b ·) (e b ·)` obtained by pulling back a fixed bilinear
form `φ` on the model fibre along the preferred trivialization `e` at `x` is continuous on the base
set of `e`. -/
theorem continuousOn_trivializationAt_pullbackForm (φ : F →L[ℝ] F →L[ℝ] ℝ) (x : B) :
    ContinuousOn
      (fun b ↦ TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ) b
        ((ContinuousLinearMap.precomp ℝ ((trivializationAt F V x).continuousLinearMapAt ℝ b)).comp
          (φ.comp ((trivializationAt F V x).continuousLinearMapAt ℝ b))))
      (trivializationAt F V x).baseSet := by
  rw [Trivialization.continuousOn_section_iff (F := F →L[ℝ] F →L[ℝ] ℝ)
    (E := fun b ↦ V b →L[ℝ] V b →L[ℝ] ℝ) (trivializationAt _ _ x)
    (by simp [hom_trivializationAt_baseSet])]
  -- Read in the corresponding trivialization of the bundle of bilinear forms, the field is the
  -- constant `φ`.
  refine (continuousOn_const (c := φ)).congr fun b hb ↦ ?_
  ext v w
  simp [hom_trivializationAt_apply, ContinuousLinearMap.inCoordinates, hb]

variable [FiniteDimensional ℝ F]

/-- In a finite-rank real bilinear bundle, strict positivity on nonzero diagonal vectors
defines an open subset of the total space. The forms are not required to be symmetric. -/
theorem isOpen_setOf_forall_bilinear_bundle_apply_self_pos :
    IsOpen {z : TotalSpace (F →L[ℝ] F →L[ℝ] ℝ)
      (fun x ↦ V x →L[ℝ] V x →L[ℝ] ℝ) | ∀ v, v ≠ 0 → 0 < z.snd v v} := by
  rw [isOpen_iff_mem_nhds]
  intro z hz
  have hcoord := (continuousAt_hom_bundle (RingHom.id ℝ) _).mp
    (continuousAt_id : ContinuousAt
      (id : TotalSpace (F →L[ℝ] F →L[ℝ] ℝ)
        (fun x ↦ V x →L[ℝ] V x →L[ℝ] ℝ) → _) z)
  have hbase : ∀ᶠ w in 𝓝 z, w.proj ∈ (trivializationAt F V z.proj).baseSet :=
    hcoord.1 ((trivializationAt F V z.proj).open_baseSet.mem_nhds
      (mem_baseSet_trivializationAt F V z.proj))
  have hpos : ∀ᶠ w in 𝓝 z, ∀ v : F, v ≠ 0 →
      0 < inCoordinates F V (F →L[ℝ] ℝ) (fun x ↦ V x →L[ℝ] ℝ)
        z.proj w.proj z.proj w.proj w.snd v v :=
    hcoord.2 (isOpen_setOf_forall_bilinear_apply_self_pos.mem_nhds
      ((forall_inCoordinates_bilinear_apply_self_pos_iff
        (mem_baseSet_trivializationAt F V z.proj) z.snd).mpr hz))
  filter_upwards [hbase, hpos] with w hw hp
  exact (forall_inCoordinates_bilinear_apply_self_pos_iff hw w.snd).mp hp

/-- Positivity of a continuous family of bilinear fields on a compact subset of the base is
an open condition on the parameter. This applies in particular to symmetric metric fields. -/
theorem _root_.IsCompact.isOpen_setOf_forall_mem_forall_bilinear_apply_self_pos
    {P : Type*} [TopologicalSpace P] {K : Set B} (hK : IsCompact K)
    (b : P → ∀ x : B, V x →L[ℝ] V x →L[ℝ] ℝ)
    (hb : Continuous (fun z : P × B ↦
      TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ)
        (E := fun x ↦ V x →L[ℝ] V x →L[ℝ] ℝ) z.2 (b z.1 z.2))) :
    IsOpen {p | ∀ x ∈ K, ∀ v, v ≠ 0 → 0 < b p x v v} := by
  rw [isOpen_iff_mem_nhds]
  intro p hp
  exact hK.eventually_forall_of_forall_eventually fun x hx ↦
    (isOpen_setOf_forall_bilinear_bundle_apply_self_pos.preimage hb).mem_nhds (hp x hx)

end TauCeti

section Comparison

variable {B : Type*} [TopologicalSpace B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type*} [TopologicalSpace (TotalSpace F E)]
  [∀ x, TopologicalSpace (E x)] [∀ x, AddCommGroup (E x)] [∀ x, Module ℝ (E x)]
  [FiberBundle F E] [VectorBundle ℝ F E] [FiniteDimensional ℝ F]
  {K : Set B} {b b₀ : ∀ x, E x →L[ℝ] E x →L[ℝ] ℝ}

/-- On a compact set in a finite-rank bundle, a continuous positive bilinear field dominates
some positive multiple of any continuous bilinear field. No symmetry is required. -/
theorem IsCompact.exists_pos_mul_bilin_self_le (hK : IsCompact K)
    (hb : ContinuousOn (fun x ↦ TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ) x (b x)) K)
    (hb₀ : ContinuousOn (fun x ↦ TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ) x (b₀ x)) K)
    (hpos : ∀ x ∈ K, ∀ v : E x, v ≠ 0 → 0 < b x v v) :
    ∃ c > 0, ∀ x ∈ K, ∀ v : E x, c * b₀ x v v ≤ b x v v := by
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hb' := hb.domRestrict.comp (continuous_snd : Continuous (Prod.snd : ℝ × K → K))
  have hb₀' := hb₀.domRestrict.comp (continuous_snd : Continuous (Prod.snd : ℝ × K → K))
  have hsmul := (TauCeti.VectorBundle.continuous_smul ℝ (F →L[ℝ] F →L[ℝ] ℝ)
    (fun x ↦ E x →L[ℝ] E x →L[ℝ] ℝ)).comp (continuous_fst.neg.prodMk hb₀')
  have hcont : Continuous (fun p : ℝ × K ↦
      TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ) (E := fun x ↦ E x →L[ℝ] E x →L[ℝ] ℝ)
        (p.snd : B) (b p.snd + (-p.fst) • b₀ p.snd)) :=
    hb'.add_totalSpace ℝ hsmul
  have hopen := TauCeti.isOpen_setOf_forall_bilinear_bundle_apply_self_pos.preimage hcont
  have hevent : ∀ᶠ t : ℝ in 𝓝 0, ∀ x : K, ∀ v : E x, v ≠ 0 →
      0 < (b x + (-t) • b₀ x) v v := by
    simpa only [mem_univ, forall_const] using
      (isCompact_univ : IsCompact (univ : Set K)).eventually_forall_of_forall_eventually
        (P := fun t (x : K) ↦ ∀ v : E x, v ≠ 0 → 0 < (b x + (-t) • b₀ x) v v)
        (x₀ := (0 : ℝ)) (fun x _ ↦ hopen.mem_nhds (x := (0, x))
          (by simpa only [mem_preimage, mem_ofPred_eq, neg_zero, _root_.add_apply,
            _root_.smul_apply, smul_eq_mul, zero_mul, add_zero] using hpos x x.property))
  obtain ⟨ε, hε, he⟩ := Metric.mem_nhds_iff.mp hevent
  have ht : ε / 2 ∈ Metric.ball (0 : ℝ) ε := by
    simpa [Real.dist_eq, abs_of_pos hε] using half_lt_self hε
  refine ⟨ε / 2, half_pos hε, fun x hx v ↦ ?_⟩
  by_cases hv : v = 0
  · simp [hv]
  · have h := he ht ⟨x, hx⟩ v hv
    simp only [add_apply, smul_apply, smul_eq_mul, neg_mul] at h
    linarith

/-- Two bilinear fields continuous and positive on a compact set in a finite-rank bundle have
uniform positive two-sided comparison constants. Symmetry and positivity elsewhere are not
required; empty compact sets and rank-zero bundles are allowed. -/
theorem IsCompact.exists_pos_mul_bilin_self_le_and_le (hK : IsCompact K)
    (hb : ContinuousOn (fun x ↦ TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ) x (b x)) K)
    (hb₀ : ContinuousOn (fun x ↦ TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ) x (b₀ x)) K)
    (hpos : ∀ x ∈ K, ∀ v : E x, v ≠ 0 → 0 < b x v v)
    (hpos₀ : ∀ x ∈ K, ∀ v : E x, v ≠ 0 → 0 < b₀ x v v) :
    ∃ c > 0, ∃ C > 0, ∀ x ∈ K, ∀ v : E x,
      c * b₀ x v v ≤ b x v v ∧ b x v v ≤ C * b₀ x v v := by
  obtain ⟨c, hc, h⟩ := hK.exists_pos_mul_bilin_self_le hb hb₀ hpos
  obtain ⟨d, hd, h'⟩ := hK.exists_pos_mul_bilin_self_le hb₀ hb hpos₀
  refine ⟨c, hc, d⁻¹, inv_pos.mpr hd, fun x hx v ↦ ⟨h x hx v, ?_⟩⟩
  rw [← div_eq_inv_mul, le_div_iff₀ hd]
  simpa only [mul_comm] using h' x hx v

end Comparison
