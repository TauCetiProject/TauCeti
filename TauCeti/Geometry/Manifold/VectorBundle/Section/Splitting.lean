/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Projection
public import TauCeti.Geometry.Manifold.VectorBundle.Subbundle
public import TauCeti.Geometry.Manifold.VectorBundle.Prod
public import TauCeti.Geometry.Manifold.VectorBundle.Section.Generic
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import Mathlib.Topology.VectorBundle.FiniteDimensional
import Mathlib.LinearAlgebra.Dimension.OrzechProperty
import TauCeti.Geometry.Manifold.ContMDiff.LeftInverse
import TauCeti.Geometry.Manifold.VectorBundle.Scalar
import TauCeti.Geometry.Manifold.VectorBundle.Translate
import TauCeti.Topology.VectorBundle.RestrictScalars
import TauCeti.Topology.VectorBundle.Trivialization

/-!
# Splitting off the complex line of a nowhere-zero section

Let `V` be a smooth complex vector bundle of complex rank `k + 1` over a real manifold, with a
smooth Hermitian metric `g`, and let `s` be a nowhere-zero smooth section. The Hermitian
orthogonal complements `(ℂ ∙ s x)ᗮ` form a smooth complex subbundle of rank `k`
(`Bundle.ContMDiffRiemannianMetric.orthogonalSpan`), and

  `V ≅ (B × ℂ) ⊕ s^⊥`, `(x, c, w) ↦ c • s x + w`,

as smooth bundles (`Bundle.ContMDiffRiemannianMetric.trivialProdOrthogonalSpanDiffeomorph`). The
inverse sends a vector to its coefficient along `s` and its orthogonal projection onto `s^⊥`.

The subbundle structure on `s^⊥` uses the frame trivializations
`TauCeti.IsSubbundleFrameOn.trivialization`. Near a point, a trivialization of `V` supplies a
smooth local frame `σ₀, …, σ_k` of `V` such that `s, σ₁, …, σ_k` is still a frame; the orthogonal
projections of `σ₁, …, σ_k` onto `s^⊥` are a smooth complex frame of `s^⊥`
(`Bundle.ContMDiffRiemannianMetric.exists_isSubbundleFrameOn_orthogonalSpan`). The atlas consists
of all smooth complex frames of `s^⊥`; their coordinate changes are smooth over `ℝ` by
`TauCeti.IsSubbundleFrameOn.contMDiffOn_coordChangeL`. The fibres keep their given complex module
structure, so the complement is again a smooth complex vector bundle.

On a compact boundaryless base of real dimension less than the real rank of `V`, such data exist
(`TauCeti.exists_hermitian_and_contMDiffSection_forall_ne_zero`), by the generic section theorem
`TauCeti.exists_contMDiffSection_forall_ne_zero_of_finrank_lt`. In particular every
smooth complex bundle of complex rank at least two over a compact surface splits off a trivial
complex line.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS (2012),
  proof of Theorem C.1.10.
* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer (2013), Lemma 10.32.
-/

public noncomputable section

open Bundle Module Set TauCeti
open scoped Manifold ContDiff InnerProductSpace Topology

namespace Bundle.ContMDiffRiemannianMetric

variable {X H B F : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [TopologicalSpace H] {IB : ModelWithCorners ℝ X H}
  [TopologicalSpace B] [ChartedSpace H B]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]
  {V : B → Type*}
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [∀ x, Module ℂ (V x)]
  [∀ x, IsScalarTower ℝ ℂ (V x)] [∀ x, TopologicalSpace (V x)]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℂ F V]
  {n : ℕ∞ω} {k : ℕ}

local instance instVectorBundleRealOrthogonalSpan : VectorBundle ℝ F V :=
  VectorBundle.restrictScalars ℝ ℂ F V

/-- The Hermitian orthogonal complement `(ℂ ∙ s x)ᗮ` of a section `s`, for the complex inner
product of an `i`-invariant smooth metric `g`. -/
@[expose]
def orthogonalSpan (g : ContMDiffRiemannianMetric IB n F V)
    (hI : ∀ x (v w : V x), g.inner x (Complex.I • v) (Complex.I • w) = g.inner x v w)
    (s : ∀ x, V x) (x : B) : Submodule ℂ (V x) :=
  letI : RiemannianBundle V := ⟨g.toRiemannianMetric⟩
  letI := g.complexInnerProductSpace hI x
  (ℂ ∙ s x)ᗮ

variable (g : ContMDiffRiemannianMetric IB n F V)
  (hI : ∀ x (v w : V x), g.inner x (Complex.I • v) (Complex.I • w) = g.inner x v w)
  (s : ∀ x, V x)

/-- The orthogonal complement of `s` is the kernel of the Hermitian pairing with `s`. -/
theorem mem_orthogonalSpan_iff {x : B} {w : V x} :
    letI : RiemannianBundle V := ⟨g.toRiemannianMetric⟩
    letI := g.complexInnerProductSpace hI x
    w ∈ g.orthogonalSpan hI s x ↔ ⟪s x, w⟫_ℂ = 0 := by
  let : RiemannianBundle V := ⟨g.toRiemannianMetric⟩
  let := g.complexInnerProductSpace hI x
  exact Submodule.mem_orthogonal_singleton_iff_inner_right

/-- The total space of `s^⊥` carries the subspace topology of the total space of `V`. -/
instance instTopologicalSpaceTotalSpaceOrthogonalSpan {F' : Type*} :
    TopologicalSpace (TotalSpace F' fun x ↦ g.orthogonalSpan hI s x) :=
  subbundleTopology F (g.orthogonalSpan hI s)

/-- For a nowhere-zero section of a bundle of complex rank `k + 1`, its orthogonal complement has
complex dimension `k` in every fibre. -/
theorem finrank_orthogonalSpan (hne : ∀ x, s x ≠ 0)
    (hk : finrank ℂ F = k + 1) (x : B) :
    finrank ℂ (g.orthogonalSpan hI s x) = k := by
  let : RiemannianBundle V := ⟨g.toRiemannianMetric⟩
  let := g.complexInnerProductSpace hI x
  have : Fact (finrank ℂ (V x) = k + 1) := ⟨(VectorBundle.finrank_eq ℂ F V x).trans hk⟩
  exact Submodule.finrank_orthogonal_span_singleton (hne x)

variable [FiniteDimensional ℂ F] [ContMDiffVectorBundle n F V IB]

/-- **Smooth frames of the orthogonal complement.** Near every point, the orthogonal complement of
a nowhere-zero smooth section of a bundle of complex rank `k + 1` has a smooth complex local frame
with `k` members. -/
theorem exists_isSubbundleFrameOn_orthogonalSpan
    (hs : ContMDiff IB (IB.prod 𝓘(ℝ, F)) n (fun x ↦ (⟨x, s x⟩ : TotalSpace F V)))
    (hne : ∀ x, s x ≠ 0) (hk : finrank ℂ F = k + 1) (x₀ : B) :
    ∃ U : Set B, IsOpen U ∧ x₀ ∈ U ∧ ∃ Y : Fin k → ∀ x, V x,
      IsSubbundleFrameOn F (g.orthogonalSpan hI s) Y U ∧
        ∀ i, ContMDiffOn IB (IB.prod 𝓘(ℝ, F)) n (fun x ↦ TotalSpace.mk' F x (Y i x)) U := by
  let : RiemannianBundle V := ⟨g.toRiemannianMetric⟩
  let : ∀ x, InnerProductSpace ℂ (V x) := g.complexInnerProductSpace hI
  let e := trivializationAt F V x₀
  have hx₀ : x₀ ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' x₀
  have he (x : B) (hx : x ∈ e.baseSet) (v : V x) :
      e.continuousLinearEquivAt ℂ x hx v = (e ⟨x, v⟩).2 :=
    congrFun (e.continuousLinearEquivAt_apply ℂ x hx) v
  -- Choose a basis of `F` in which the zeroth coordinate of `s x₀` is nonzero.
  let b₀ := Module.finBasisOfFinrankEq ℂ F hk
  have hv₀ : (e ⟨x₀, s x₀⟩).2 ≠ 0 := by
    rw [← he x₀ hx₀]
    exact (map_ne_zero_iff _ (e.continuousLinearEquivAt ℂ x₀ hx₀).injective).mpr (hne x₀)
  obtain ⟨i₀, hi₀⟩ : ∃ i, b₀.repr (e ⟨x₀, s x₀⟩).2 i ≠ 0 := by
    by_contra! h
    exact hv₀ (b₀.repr.injective (by ext i; simp [h i]))
  let b := b₀.reindex (Equiv.swap i₀ 0)
  have hb (v : F) : b.repr v 0 = b₀.repr v i₀ := by simp [b]
  let ℓ : B → ℂ := fun x ↦ b.repr (e ⟨x, s x⟩).2 0
  have hsec (x : B) (hx : x ∈ e.baseSet) :
      ContMDiffAt IB 𝓘(ℝ, F) n (fun y ↦ (e ⟨y, s y⟩).2) x :=
    (e.contMDiffAt_section_iff hx).mp (hs x)
  have hℓ : ContinuousOn ℓ e.baseSet := fun x hx ↦
    ((b.coord 0).continuous_of_finiteDimensional.continuousAt.comp
      (hsec x hx).continuousAt).continuousWithinAt
  let U := e.baseSet ∩ ℓ ⁻¹' {0}ᶜ
  have hU : IsOpen U := hℓ.isOpen_inter_preimage e.open_baseSet isOpen_compl_singleton
  -- The local frame of `V` read off from the basis `b`.
  let σ : Fin (k + 1) → ∀ x, V x := fun i x ↦ e.symm x (b i)
  have hσ (i : Fin (k + 1)) :
      ContMDiffOn IB (IB.prod 𝓘(ℝ, F)) n (fun x ↦ TotalSpace.mk' F x (σ i x)) e.baseSet := by
    intro x hx
    refine ((e.contMDiffAt_section_iff hx).mpr ?_).contMDiffWithinAt
    refine (contMDiffAt_const (c := b i)).congr_of_eventuallyEq ?_
    filter_upwards [e.open_baseSet.mem_nhds hx] with y hy
    simp [σ, e.apply_mk_symm hy]
  -- Its projections onto `s^⊥`, omitting the zeroth member.
  let Y : Fin k → ∀ x, V x := fun j x ↦ (ℂ ∙ s x)ᗮ.starProjection (σ j.succ x)
  have hY (j : Fin k) :
      ContMDiffOn IB (IB.prod 𝓘(ℝ, F)) n (fun x ↦ TotalSpace.mk' F x (Y j x)) U :=
    (g.contMDiff_starProjection_orthogonal_span_singleton hI s hs hne).comp_contMDiffOn
      ((hσ j.succ).mono inter_subset_left)
  have hspan (x : B) (hx : x ∈ U) :
      Submodule.span ℂ (range (Y · x)) = g.orthogonalSpan hI s x := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      exact Submodule.starProjection_apply_mem (ℂ ∙ s x)ᗮ _
    intro w hw
    let ex := e.continuousLinearEquivAt ℂ x hx.1
    have hℓx : b.repr (ex (s x)) 0 ≠ 0 := by rw [he]; exact hx.2
    set t := b.repr (ex w) 0 / b.repr (ex (s x)) 0
    set d : Fin k → ℂ := fun j ↦ b.repr (ex (w - t • s x)) j.succ
    have hd : w - t • s x = ∑ j, d j • σ j.succ x := by
      apply ex.injective
      have h0 : b.repr (ex (w - t • s x)) 0 = 0 := by
        simp only [map_sub, map_smul, Finsupp.coe_sub, Finsupp.coe_smul, Pi.sub_apply,
          Pi.smul_apply, smul_eq_mul, t]
        field_simp
        ring
      have hσx (i : Fin (k + 1)) : ex (σ i x) = b i := by
        simp [ex, σ, he, e.apply_mk_symm hx.1]
      rw [← b.sum_repr (ex (w - t • s x)), Fin.sum_univ_succ, h0, zero_smul, zero_add,
        map_sum]
      simp [map_smul, hσx, d]
    have hw' : (ℂ ∙ s x)ᗮ.starProjection w = w :=
      Submodule.starProjection_eq_self_iff.mpr hw
    have hs' : (ℂ ∙ s x)ᗮ.starProjection (s x) = 0 := by
      rw [Submodule.starProjection_orthogonal', sub_apply,
        Submodule.starProjection_eq_self_iff.mpr (Submodule.mem_span_singleton_self _),
        one_apply_eq_self, sub_self]
    have hsum : w = ∑ j, d j • Y j x := by
      rw [← hw', ← sub_add_cancel w (t • s x), map_add, map_smul, hs', smul_zero, add_zero,
        hd, map_sum]
      simp [map_smul, Y]
    rw [hsum]
    exact Submodule.sum_mem _ fun j _ ↦
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  refine ⟨U, hU, ⟨hx₀, by simp [ℓ, hb, hi₀]⟩, Y, ?_, hY⟩
  exact
    { continuousOn := fun j ↦ (hY j).continuousOn
      linearIndependent := fun hx ↦ by
        rw [linearIndependent_iff_card_eq_finrank_span, Set.finrank, hspan _ hx,
          g.finrank_orthogonalSpan hI s hne hk, Fintype.card_fin]
      span_eq := fun hx ↦ hspan _ hx }

variable (hs : ContMDiff IB (IB.prod 𝓘(ℝ, F)) n (fun x ↦ (⟨x, s x⟩ : TotalSpace F V)))
  (hne : ∀ x, s x ≠ 0) (hk : finrank ℂ F = k + 1)

/-- The fibre bundle structure on the orthogonal complement `s^⊥` of a nowhere-zero smooth
section, with model fibre `Fin k → ℂ` and the subspace topology of the total space of `V`. Its
trivializations are those of all smooth complex local frames of `s^⊥` on open sets. Use this
definition as a local instance; it chooses a local frame near every point. -/
@[instance_reducible]
def orthogonalSpanFiberBundle : FiberBundle (Fin k → ℂ) fun x ↦ g.orthogonalSpan hI s x :=
  have h := g.exists_isSubbundleFrameOn_orthogonalSpan hI s hs hne hk
  { totalSpaceMk_isInducing' :=
      isInducing_totalSpaceMk_subbundle F (Fin k → ℂ) (g.orthogonalSpan hI s)
    trivializationAtlas' :=
      {e | ∃ (U : Set B) (hU : IsOpen U) (Y : Fin k → ∀ x, V x)
        (hY : IsSubbundleFrameOn F (g.orthogonalSpan hI s) Y U),
        (∀ i, ContMDiffOn IB (IB.prod 𝓘(ℝ, F)) n (fun x ↦ TotalSpace.mk' F x (Y i x)) U) ∧
          hY.trivialization hU = e}
    trivializationAt' := fun x ↦
      (h x).choose_spec.2.2.choose_spec.1.trivialization (h x).choose_spec.1
    mem_baseSet_trivializationAt' := fun x ↦ by
      rw [IsSubbundleFrameOn.trivialization_baseSet]
      exact (h x).choose_spec.2.1
    trivialization_mem_atlas' := fun x ↦
      ⟨_, (h x).choose_spec.1, _, (h x).choose_spec.2.2.choose_spec.1,
        (h x).choose_spec.2.2.choose_spec.2, rfl⟩ }

/-- The trivializations of `g.orthogonalSpanFiberBundle` are the trivializations of the smooth
complex local frames of `s^⊥` on open sets. -/
theorem mem_trivializationAtlas_orthogonalSpanFiberBundle_iff
    (e : Trivialization (Fin k → ℂ) (π (Fin k → ℂ) fun x ↦ g.orthogonalSpan hI s x)) :
    letI := g.orthogonalSpanFiberBundle hI s hs hne hk
    e ∈ trivializationAtlas (Fin k → ℂ) (fun x ↦ g.orthogonalSpan hI s x) ↔
      ∃ (U : Set B) (hU : IsOpen U) (Y : Fin k → ∀ x, V x)
        (hY : IsSubbundleFrameOn F (g.orthogonalSpan hI s) Y U),
        (∀ i, ContMDiffOn IB (IB.prod 𝓘(ℝ, F)) n (fun x ↦ TotalSpace.mk' F x (Y i x)) U) ∧
          hY.trivialization hU = e :=
  Iff.rfl

/-- The orthogonal complement of a nowhere-zero smooth section is a complex vector bundle. -/
theorem orthogonalSpanVectorBundle :
    letI := g.orthogonalSpanFiberBundle hI s hs hne hk
    VectorBundle ℂ (Fin k → ℂ) fun x ↦ g.orthogonalSpan hI s x :=
  vectorBundle_of_forall_mem_trivializationAtlas (g.orthogonalSpanFiberBundle hI s hs hne hk)
    fun _ he ↦ by
      obtain ⟨U, hU, Y, hY, -, rfl⟩ := he
      exact ⟨U, hU, Y, hY, rfl⟩

/-- **The orthogonal complement is a smooth subbundle.** The orthogonal complement of a
nowhere-zero smooth section is a smooth complex vector bundle over the real base: its complex
structure is the given fibrewise one, and its coordinate changes are smooth over `ℝ`. -/
theorem orthogonalSpanContMDiffVectorBundle :
    letI := g.orthogonalSpanFiberBundle hI s hs hne hk
    letI := g.orthogonalSpanVectorBundle hI s hs hne hk
    letI := VectorBundle.restrictScalars ℝ ℂ (Fin k → ℂ) fun x ↦ g.orthogonalSpan hI s x
    ContMDiffVectorBundle n (Fin k → ℂ) (fun x ↦ g.orthogonalSpan hI s x) IB := by
  let := g.orthogonalSpanFiberBundle hI s hs hne hk
  let := g.orthogonalSpanVectorBundle hI s hs hne hk
  let := VectorBundle.restrictScalars ℝ ℂ (Fin k → ℂ) fun x ↦ g.orthogonalSpan hI s x
  refine ⟨fun e e' he he' ↦ ?_⟩
  obtain ⟨U, hU, Y, hY, hYn, rfl⟩ := he.out
  obtain ⟨U', hU', Y', hY', hYn', rfl⟩ := he'.out
  have h := hY.contMDiffOn_coordChangeL hU hYn hY' hU' hYn'
  have hr : ContMDiffOn IB 𝓘(ℝ, (Fin k → ℂ) →L[ℝ] Fin k → ℂ) n
      (fun x ↦ ((hY.trivialization hU).coordChangeL ℂ (hY'.trivialization hU') x :
        (Fin k → ℂ) →L[ℂ] Fin k → ℂ).restrictScalars ℝ) (U ∩ U') :=
    fun x hx ↦ (ContinuousLinearMap.restrictScalarsIsometry ℂ (Fin k → ℂ) (Fin k → ℂ) ℝ ℝ
      ).toContinuousLinearMap.contDiff.comp_contMDiffWithinAt (h x hx)
  simpa only [IsSubbundleFrameOn.trivialization_baseSet] using
    hr.congr fun x hx ↦ (Trivialization.restrictScalars_coordChangeL ℝ ℂ _ _
      (by simpa only [IsSubbundleFrameOn.trivialization_baseSet] using hx)).symm

/-- The canonical inclusion of the orthogonal complement into the total space of `V` is smooth. -/
theorem contMDiff_orthogonalSpan_inclusion :
    letI := g.orthogonalSpanFiberBundle hI s hs hne hk
    letI := g.orthogonalSpanVectorBundle hI s hs hne hk
    letI := VectorBundle.restrictScalars ℝ ℂ (Fin k → ℂ) fun x ↦ g.orthogonalSpan hI s x
    ContMDiff (IB.prod 𝓘(ℝ, Fin k → ℂ)) (IB.prod 𝓘(ℝ, F)) n
      (fun v : TotalSpace (Fin k → ℂ) (fun x ↦ g.orthogonalSpan hI s x) ↦
        (⟨v.proj, v.2⟩ : TotalSpace F V)) := by
  let := g.orthogonalSpanFiberBundle hI s hs hne hk
  let := g.orthogonalSpanVectorBundle hI s hs hne hk
  let := VectorBundle.restrictScalars ℝ ℂ (Fin k → ℂ) fun x ↦ g.orthogonalSpan hI s x
  let := g.orthogonalSpanContMDiffVectorBundle hI s hs hne hk
  intro p
  obtain ⟨U, hU, hp, Y, hY, hYn⟩ := g.exists_isSubbundleFrameOn_orthogonalSpan hI s hs hne hk p.proj
  have : MemTrivializationAtlas (hY.trivialization hU) := ⟨⟨U, hU, Y, hY, hYn, rfl⟩⟩
  exact hY.contMDiffAt_totalSpace_subbundle hU hYn hp

section Maps

variable {XM HM M : Type*} [NormedAddCommGroup XM] [NormedSpace ℝ XM]
  [TopologicalSpace HM] {IM : ModelWithCorners ℝ XM HM}
  [TopologicalSpace M] [ChartedSpace HM M]

/-- A smooth bundle-valued map with values in the orthogonal complement of `s` is smooth as a map
into the orthogonal complement bundle. -/
theorem contMDiffAt_orthogonalSpan_mk {b : M → B} {w : ∀ m, V (b m)} {m₀ : M}
    (hw : ContMDiffAt IM (IB.prod 𝓘(ℝ, F)) n (fun m ↦ (⟨b m, w m⟩ : TotalSpace F V)) m₀)
    (hmem : ∀ m, w m ∈ g.orthogonalSpan hI s (b m)) :
    letI := g.orthogonalSpanFiberBundle hI s hs hne hk
    letI := g.orthogonalSpanVectorBundle hI s hs hne hk
    letI := VectorBundle.restrictScalars ℝ ℂ (Fin k → ℂ) fun x ↦ g.orthogonalSpan hI s x
    ContMDiffAt IM (IB.prod 𝓘(ℝ, Fin k → ℂ)) n
      (fun m ↦ (⟨b m, ⟨w m, hmem m⟩⟩ :
        TotalSpace (Fin k → ℂ) fun x ↦ g.orthogonalSpan hI s x)) m₀ := by
  let := g.orthogonalSpanFiberBundle hI s hs hne hk
  let := g.orthogonalSpanVectorBundle hI s hs hne hk
  let := VectorBundle.restrictScalars ℝ ℂ (Fin k → ℂ) fun x ↦ g.orthogonalSpan hI s x
  let := g.orthogonalSpanContMDiffVectorBundle hI s hs hne hk
  obtain ⟨hb, hv⟩ := Bundle.contMDiffAt_totalSpace.mp hw
  obtain ⟨U, hU, hbU, Y, hY, hYn⟩ :=
    g.exists_isSubbundleFrameOn_orthogonalSpan hI s hs hne hk (b m₀)
  let eV := hY.trivialization hU
  have : MemTrivializationAtlas eV := ⟨⟨U, hU, Y, hY, hYn, rfl⟩⟩
  refine (eV.contMDiffAt_iff (IM := IM) (f := fun m ↦ (⟨b m, ⟨w m, hmem m⟩⟩ :
    TotalSpace (Fin k → ℂ) fun x ↦ g.orthogonalSpan hI s x))
    (eV.mem_source.mpr (by simpa [eV] using hbU))).mpr
    ⟨hb, ?_⟩
  -- Frame coordinates are recovered by a smooth left inverse of the frame read in `V`.
  let eE := trivializationAt F V (b m₀)
  have hbE : b m₀ ∈ eE.baseSet := FiberBundle.mem_baseSet_trivializationAt' _
  obtain ⟨L, hL, hLinv⟩ := ContMDiffAt.exists_contMDiffAt_leftInverse
    (IsSubbundleFrameOn.contMDiffAt_trivOperator (𝕜 := ℝ) (𝕜' := ℂ) (y₀ := b m₀)
      (fun i ↦ (hYn i).contMDiffAt (hU.mem_nhds hbU)) hbE)
    (.of_injective_of_finiteDimensional_domain (hY.injective_trivOperator hbU))
  have hLr : ContMDiffAt IM 𝓘(ℝ, F →L[ℝ] Fin k → ℂ) n (fun m ↦ (L (b m)).restrictScalars ℝ) m₀ :=
    (ContinuousLinearMap.restrictScalarsIsometry ℂ F (Fin k → ℂ) ℝ ℝ
      ).toContinuousLinearMap.contDiff.comp_contMDiffAt (hL.comp m₀ hb)
  refine (hLr.clm_apply hv).congr_of_eventuallyEq ?_
  filter_upwards [hb.continuousAt.eventually hLinv, hb.continuousAt.eventually
    (hU.mem_nhds hbU), hb.continuousAt.eventually (eE.open_baseSet.mem_nhds hbE)]
    with m hmL hmU hmE
  rw [IsSubbundleFrameOn.trivialization_apply hY hU (p := ⟨b m, ⟨w m, hmem m⟩⟩) hmU]
  dsimp only
  rw [ContinuousLinearMap.coe_restrictScalars', ← hmL ((hY.basis hmU).equivFun ⟨w m, hmem m⟩),
    IsSubbundleFrameOn.trivOperator_apply hmE, ← IsSubbundleFrameOn.coe_basis_equivFun_symm hY hmU,
    LinearEquiv.symm_apply_apply]

end Maps

/-- **Splitting off the line of a nowhere-zero section.** For a nowhere-zero smooth section `s`
of a smooth Hermitian bundle `V` of complex rank `k + 1`, the map `(x, c, w) ↦ c • s x + w` is a
smooth bundle isomorphism from the sum of the trivial complex line bundle and the orthogonal
complement `s^⊥` onto `V`. Its inverse sends `v ∈ V x` to its coefficient
`‖s x‖⁻² ⟪s x, v⟫` along `s x` and to its orthogonal projection onto `s^⊥`. -/
@[expose]
def trivialProdOrthogonalSpanDiffeomorph :
    letI := g.orthogonalSpanFiberBundle hI s hs hne hk
    Diffeomorph (IB.prod 𝓘(ℝ, ℂ × (Fin k → ℂ))) (IB.prod 𝓘(ℝ, F))
      (TotalSpace (ℂ × (Fin k → ℂ)) (Bundle.Trivial B ℂ ×ᵇ fun x ↦ g.orthogonalSpan hI s x))
      (TotalSpace F V) n := by
  let := g.orthogonalSpanFiberBundle hI s hs hne hk
  let := g.orthogonalSpanVectorBundle hI s hs hne hk
  let := VectorBundle.restrictScalars ℝ ℂ (Fin k → ℂ) fun x ↦ g.orthogonalSpan hI s x
  let := g.orthogonalSpanContMDiffVectorBundle hI s hs hne hk
  let : RiemannianBundle V := ⟨g.toRiemannianMetric⟩
  let : ∀ x, InnerProductSpace ℂ (V x) := g.complexInnerProductSpace hI
  have hb := Bundle.contMDiff_proj V (F := F) (IB := IB) (n := n)
  have hsp := hs.comp hb
  have hs' (x : B) : (ℂ ∙ s x)ᗮ.starProjection (s x) = 0 := by
    rw [Submodule.starProjection_orthogonal', sub_apply,
      Submodule.starProjection_eq_self_iff.mpr (Submodule.mem_span_singleton_self _),
      one_apply_eq_self, sub_self]
  have hnorm (x : B) : (‖s x‖ ^ 2 : ℝ) ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr (hne x))
  refine
    { toFun := fun v ↦ ⟨v.proj, (v.2.1 : ℂ) • s v.proj + (v.2.2 : V v.proj)⟩
      invFun := fun p ↦ ⟨p.proj, ((‖s p.proj‖ ^ 2)⁻¹ • ⟪s p.proj, p.2⟫_ℂ,
        ⟨(ℂ ∙ s p.proj)ᗮ.starProjection p.2,
          Submodule.starProjection_apply_mem (ℂ ∙ s p.proj)ᗮ _⟩)⟩
      left_inv := ?_
      right_inv := ?_
      contMDiff_toFun := ?_
      contMDiff_invFun := ?_ }
  · rintro ⟨x, c, w, hw⟩
    have hw' : ⟪s x, w⟫_ℂ = 0 := (g.mem_orthogonalSpan_iff hI s).mp hw
    have h₁ : (‖s x‖ ^ 2)⁻¹ • ⟪s x, (c : ℂ) • s x + w⟫_ℂ = c := by
      simp only [inner_add_right, inner_smul_right, hw', add_zero, inner_self_eq_norm_sq_to_K]
      rw [Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_pow, ← div_eq_inv_mul]
      exact mul_div_cancel_right₀ _ (by simpa using hnorm x)
    have h₂ : (ℂ ∙ s x)ᗮ.starProjection ((c : ℂ) • s x + w) = w := by
      rw [map_add, map_smul, hs', smul_zero, zero_add]
      exact Submodule.starProjection_eq_self_iff.mpr hw
    exact congrArg (TotalSpace.mk x) (Prod.ext h₁ (Subtype.ext h₂))
  · rintro ⟨x, v⟩
    apply congrArg (TotalSpace.mk x)
    dsimp only
    conv_rhs => rw [← Submodule.starProjection_add_starProjection_orthogonal (K := ℂ ∙ s x) v,
      Submodule.starProjection_singleton]
    simp only [Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_pow, div_eq_inv_mul]
    norm_cast
  · intro v
    have hc := Bundle.contMDiffAt_totalSpace_prod_iff.mp
      (contMDiffAt_id (I := IB.prod 𝓘(ℝ, ℂ × (Fin k → ℂ))) (n := n) (x := v))
    obtain ⟨hpr, ha⟩ := Bundle.contMDiffAt_totalSpace.mp hc.1
    have ha' : ContMDiffAt (IB.prod 𝓘(ℝ, ℂ × (Fin k → ℂ))) 𝓘(ℝ, ℂ) n
        (fun y : TotalSpace (ℂ × (Fin k → ℂ))
          (Bundle.Trivial B ℂ ×ᵇ fun x ↦ g.orthogonalSpan hI s x) ↦ (y.2.1 : ℂ)) v := by
      exact ha
    have h₁ := ha'.smul_totalSpace (g := fun y ↦ (⟨y.proj, s y.proj⟩ : TotalSpace F V))
      ((hs v.proj).comp v hpr)
    have h₂ := (g.contMDiff_orthogonalSpan_inclusion hI s hs hne hk ⟨v.proj, v.2.2⟩).comp v hc.2
    exact ContMDiffAt.add_sectionAlong
      (b := fun y : TotalSpace (ℂ × (Fin k → ℂ))
        (Bundle.Trivial B ℂ ×ᵇ fun x ↦ g.orthogonalSpan hI s x) ↦ y.proj)
      (s := fun y ↦ (y.2.1 : ℂ) • s y.proj) (t := fun y ↦ (y.2.2 : V y.proj)) h₁ h₂
  · intro p
    refine Bundle.contMDiffAt_totalSpace_prod_iff.mpr ⟨?_, ?_⟩
    · refine Bundle.contMDiffAt_totalSpace.mpr ⟨hb p, ?_⟩
      have hn := g.contMDiff_hermitianPairing hI hsp contMDiff_id
      have hd := hsp.inner_bundle hsp
      have hz (q : TotalSpace F V) : Inner.inner ℝ (s q.proj) (s q.proj) ≠ 0 :=
        inner_self_ne_zero.mpr (hne q.proj)
      have hcoef : ContMDiffAt (IB.prod 𝓘(ℝ, F)) 𝓘(ℝ, ℂ) n
          (fun q : TotalSpace F V ↦ (‖s q.proj‖ ^ 2)⁻¹ • ⟪s q.proj, q.2⟫_ℂ) p :=
        (((hd.inv₀ hz).smul hn) p).congr_of_eventuallyEq
          (Filter.Eventually.of_forall fun q ↦ by
            simp only [Pi.smul_apply', real_inner_self_eq_norm_sq])
      exact hcoef
    · exact g.contMDiffAt_orthogonalSpan_mk hI s hs hne hk
        (g.contMDiff_starProjection_orthogonal_span_singleton hI s hs hne p)
        (fun q ↦ Submodule.starProjection_apply_mem (ℂ ∙ s q.proj)ᗮ _)

/-- The smooth splitting sends `(x, c, w)` to `c • s x + w`. -/
theorem trivialProdOrthogonalSpanDiffeomorph_apply
    (v : TotalSpace (ℂ × (Fin k → ℂ)) (Bundle.Trivial B ℂ ×ᵇ fun x ↦ g.orthogonalSpan hI s x)) :
    letI := g.orthogonalSpanFiberBundle hI s hs hne hk
    g.trivialProdOrthogonalSpanDiffeomorph hI s hs hne hk v =
      ⟨v.proj, (v.2.1 : ℂ) • s v.proj + (v.2.2 : V v.proj)⟩ :=
  rfl

/-- The inverse smooth splitting sends `v ∈ V x` to its coefficient `‖s x‖⁻² ⟪s x, v⟫` along
`s x` and its orthogonal projection onto `s^⊥`. -/
theorem trivialProdOrthogonalSpanDiffeomorph_symm_apply (p : TotalSpace F V) :
    letI := g.orthogonalSpanFiberBundle hI s hs hne hk
    letI : RiemannianBundle V := ⟨g.toRiemannianMetric⟩
    letI : ∀ x, InnerProductSpace ℂ (V x) := g.complexInnerProductSpace hI
    (g.trivialProdOrthogonalSpanDiffeomorph hI s hs hne hk).symm p =
      ⟨p.proj, ((‖s p.proj‖ ^ 2)⁻¹ • ⟪s p.proj, p.2⟫_ℂ,
        ⟨(ℂ ∙ s p.proj)ᗮ.starProjection p.2,
          Submodule.starProjection_apply_mem (ℂ ∙ s p.proj)ᗮ _⟩)⟩ :=
  rfl

end Bundle.ContMDiffRiemannianMetric

namespace TauCeti

variable {X B F : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
  [TopologicalSpace B] [ChartedSpace X B] [T2Space B] [CompactSpace B]
  [IsManifold 𝓘(ℝ, X) ∞ B]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]
  [FiniteDimensional ℂ F]
  {V : B → Type*}
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [∀ x, Module ℂ (V x)]
  [∀ x, IsScalarTower ℝ ℂ (V x)] [∀ x, TopologicalSpace (V x)]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [∀ x, ContinuousConstSMul ℂ (V x)]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℂ F V]

local instance instVectorBundleRealSplitting : VectorBundle ℝ F V :=
  VectorBundle.restrictScalars ℝ ℂ F V

/-- **Existence of a splitting.** A smooth complex bundle over a compact boundaryless manifold
whose real dimension is less than the real rank of the bundle has a smooth Hermitian metric and a
nowhere-zero smooth section, the input of
`Bundle.ContMDiffRiemannianMetric.trivialProdOrthogonalSpanDiffeomorph`. Over a compact surface
this applies to every bundle of complex rank at least two. -/
theorem exists_hermitian_and_contMDiffSection_forall_ne_zero
    [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, X)] (hdim : finrank ℝ X < finrank ℝ F) :
    ∃ g : Bundle.ContMDiffRiemannianMetric 𝓘(ℝ, X) ∞ F V,
      (∀ x (v w : V x), g.inner x (Complex.I • v) (Complex.I • w) = g.inner x v w) ∧
        ∃ s : ContMDiffSection 𝓘(ℝ, X) F ∞ V, ∀ x, s x ≠ 0 := by
  let : FiniteDimensional ℝ F := Module.Finite.trans ℂ F
  let : SigmaCompactSpace B := inferInstance
  obtain ⟨g, hg⟩ := exists_contMDiffRiemannianMetric_inner_smul_I (IB := 𝓘(ℝ, X)) (n := ⊤)
    (F := F) (V := V)
  exact ⟨g, hg, exists_contMDiffSection_forall_ne_zero_of_finrank_lt hdim⟩

end TauCeti
