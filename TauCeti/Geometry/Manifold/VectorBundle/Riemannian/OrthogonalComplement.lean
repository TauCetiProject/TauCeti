/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Projection
public import TauCeti.Geometry.Manifold.VectorBundle.Subbundle
public import TauCeti.Geometry.Manifold.VectorBundle.Prod
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import TauCeti.Analysis.InnerProductSpace.Projection.Basic
import TauCeti.LinearAlgebra.Basis.Fin
public import Mathlib.Topology.VectorBundle.FiniteDimensional
import Mathlib.LinearAlgebra.Dimension.OrzechProperty
import TauCeti.Geometry.Manifold.VectorBundle.LocalFrame
import TauCeti.Geometry.Manifold.VectorBundle.Scalar
import TauCeti.Geometry.Manifold.VectorBundle.Translate

/-!
# The orthogonal complement of a nowhere-zero section or an orthonormal family

Let `V` be a smooth complex vector bundle of complex rank `k + 1` over a real manifold, with a
smooth Hermitian metric `g`, and let `s` be a nowhere-zero smooth section. The Hermitian
orthogonal complements `(ℂ ∙ s x)ᗮ` (`Bundle.ContMDiffRiemannianMetric.orthogonalSpan`) have smooth
complex local frames with `k` members
(`Bundle.ContMDiffRiemannianMetric.hasLocalContMDiffSubbundleFrames_orthogonalSpan`), so the smooth
local frame criterion `TauCeti.HasLocalContMDiffSubbundleFrames.contMDiffVectorBundle` makes them a
smooth complex subbundle `s^⊥` of `V`, with the given fibrewise complex structure. Moreover

  `V ≅ (B × ℂ) ⊕ s^⊥`, `(x, c, w) ↦ c • s x + w`,

as smooth bundles (`Bundle.ContMDiffRiemannianMetric.trivialProdOrthogonalSpanDiffeomorph`). The
inverse sends a vector to its coefficient along `s` and its orthogonal projection onto `s^⊥`.

Near a point, a trivialization of `V` and a basis of the model fibre in which the zeroth coordinate
of `s` is nonzero give a smooth local frame `σ₀, …, σ_k` of `V`; the orthogonal projections of
`σ₁, …, σ_k` onto `s^⊥` span it (`Submodule.span_range_starProjection_orthogonal_basis_succ`).

A smooth Hermitian metric exists on a σ-compact base
(`TauCeti.exists_contMDiffRiemannianMetric_inner_smul_I`), and a nowhere-zero smooth section exists
on a compact boundaryless base whose dimension is less than the real rank of `V`
(`TauCeti.exists_contMDiffSection_forall_ne_zero_of_finrank_lt`). Together with
`Bundle.ContMDiffRiemannianMetric.trivialProdOrthogonalSpanDiffeomorph` they split a trivial complex
line off every smooth complex bundle of complex rank at least two over a compact surface.

More generally, let `s₁, …, s_k` be smooth sections of `V` that are orthonormal at every point. The
Hermitian orthogonal complements `{s₁ x, …, s_k x}ᗮ`
(`Bundle.ContMDiffRiemannianMetric.orthogonalSpanFamily`) have smooth complex local frames
(`Bundle.ContMDiffRiemannianMetric.hasLocalContMDiffSubbundleFrames_orthogonalSpanFamily`), so they
form a smooth complex subbundle `s^⊥` of `V`, and

  `V ≅ (B × ℂᵏ) ⊕ s^⊥`, `(x, c, w) ↦ ∑ i, c i • s i x + w`,

as smooth bundles (`Bundle.ContMDiffRiemannianMetric.trivialProdOrthogonalSpanFamilyDiffeomorph`).
The inverse sends `v` to its coefficients `⟪s i x, v⟫` and to `v - ∑ i, ⟪s i x, v⟫ • s i x`.
Near a point, the orthogonal projections of a local frame of `V` read off from a trivialization span
the complement; a linearly independent subfamily at the point stays linearly independent nearby,
and has the right size, so it is a local frame of the complement.

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
product of an `i`-invariant smooth metric `g` (`orthogonalSpan_eq`). -/
def orthogonalSpan (g : ContMDiffRiemannianMetric IB n F V)
    (hI : ∀ x (v w : V x), g.inner x (Complex.I • v) (Complex.I • w) = g.inner x v w)
    (s : ∀ x, V x) (x : B) : Submodule ℂ (V x) :=
  letI : RiemannianBundle V := ⟨g.toRiemannianMetric⟩
  letI := g.complexInnerProductSpace hI x
  (ℂ ∙ s x)ᗮ

variable (g : ContMDiffRiemannianMetric IB n F V)
  (hI : ∀ x (v w : V x), g.inner x (Complex.I • v) (Complex.I • w) = g.inner x v w)
  (s : ∀ x, V x)

/-- `g.orthogonalSpan hI s x` is the orthogonal complement of `s x` for the Hermitian inner
product of `g`. -/
theorem orthogonalSpan_eq (x : B) :
    letI : RiemannianBundle V := ⟨g.toRiemannianMetric⟩
    letI := g.complexInnerProductSpace hI x
    g.orthogonalSpan hI s x = (ℂ ∙ s x)ᗮ :=
  (rfl)

/-- The orthogonal complement of `s` is the kernel of the Hermitian pairing with `s`. -/
theorem mem_orthogonalSpan_iff {x : B} {w : V x} :
    letI : RiemannianBundle V := ⟨g.toRiemannianMetric⟩
    letI := g.complexInnerProductSpace hI x
    w ∈ g.orthogonalSpan hI s x ↔ ⟪s x, w⟫_ℂ = 0 := by
  let : RiemannianBundle V := ⟨g.toRiemannianMetric⟩
  let := g.complexInnerProductSpace hI x
  rw [orthogonalSpan_eq]
  exact Submodule.mem_orthogonal_singleton_iff_inner_right

/-- The orthogonal projection onto `(ℂ ∙ s x)ᗮ` takes values in `g.orthogonalSpan hI s x`. -/
theorem starProjection_mem_orthogonalSpan (x : B) (v : V x) :
    letI : RiemannianBundle V := ⟨g.toRiemannianMetric⟩
    letI := g.complexInnerProductSpace hI x
    (ℂ ∙ s x)ᗮ.starProjection v ∈ g.orthogonalSpan hI s x := by
  let : RiemannianBundle V := ⟨g.toRiemannianMetric⟩
  let := g.complexInnerProductSpace hI x
  rw [orthogonalSpan_eq]
  exact Submodule.starProjection_apply_mem _ _

/-- The total space of `s^⊥` carries the subspace topology of the total space of `V`. -/
instance instTopologicalSpaceTotalSpaceOrthogonalSpan {F' : Type*} :
    TopologicalSpace (TotalSpace F' fun x ↦ g.orthogonalSpan hI s x) :=
  subbundleTopology F (g.orthogonalSpan hI s)

/-- In a bundle of complex rank `k + 1`, the orthogonal complement of a nonzero vector `s x` has
complex dimension `k`. -/
theorem finrank_orthogonalSpan {x : B} (hx : s x ≠ 0) (hk : finrank ℂ F = k + 1) :
    finrank ℂ (g.orthogonalSpan hI s x) = k := by
  let : RiemannianBundle V := ⟨g.toRiemannianMetric⟩
  let := g.complexInnerProductSpace hI x
  have : Fact (finrank ℂ (V x) = k + 1) := ⟨(VectorBundle.finrank_eq ℂ F V x).trans hk⟩
  rw [orthogonalSpan_eq]
  exact Submodule.finrank_orthogonal_span_singleton hx

variable [ContMDiffVectorBundle n F V IB]
  (hs : ContMDiff IB (IB.prod 𝓘(ℝ, F)) n (fun x ↦ (⟨x, s x⟩ : TotalSpace F V)))
  (hne : ∀ x, s x ≠ 0)

include hs hne in
/-- **Smooth frames of the orthogonal complement.** Near every point, the orthogonal complement of
a nowhere-zero smooth section of a bundle of complex rank `k + 1` has a smooth complex local frame
with `k` members. Hence it is a smooth complex subbundle
(`TauCeti.HasLocalContMDiffSubbundleFrames.contMDiffVectorBundle`). -/
theorem hasLocalContMDiffSubbundleFrames_orthogonalSpan [FiniteDimensional ℂ F]
    (hk : finrank ℂ F = k + 1) :
    HasLocalContMDiffSubbundleFrames IB n F (Fin k) (g.orthogonalSpan hI s) := by
  let : RiemannianBundle V := ⟨g.toRiemannianMetric⟩
  let : ∀ x, InnerProductSpace ℂ (V x) := g.complexInnerProductSpace hI
  refine hasLocalContMDiffSubbundleFrames_iff.mpr fun x₀ ↦ ?_
  let e := trivializationAt F V x₀
  have hx₀ : x₀ ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' x₀
  have he (x : B) (hx : x ∈ e.baseSet) (v : V x) :
      e.continuousLinearEquivAt ℂ x hx v = (e ⟨x, v⟩).2 :=
    congrFun (e.continuousLinearEquivAt_apply ℂ x hx) v
  obtain ⟨b, hb⟩ := Module.Basis.exists_repr_zero_ne_zero hk (v := (e ⟨x₀, s x₀⟩).2) (by
    rw [← he x₀ hx₀]
    exact (map_ne_zero_iff _ (e.continuousLinearEquivAt ℂ x₀ hx₀).injective).mpr (hne x₀))
  -- The open set where the zeroth coordinate of `s` stays nonzero.
  let ℓ : B → ℂ := fun x ↦ b.repr (e ⟨x, s x⟩).2 0
  have hℓ : ContinuousOn ℓ e.baseSet := fun x hx ↦
    ((b.coord 0).continuous_of_finiteDimensional.continuousAt.comp
      ((e.contMDiffAt_section_iff hx).mp (hs x)).continuousAt).continuousWithinAt
  let U := e.baseSet ∩ ℓ ⁻¹' {0}ᶜ
  -- The local frame of `V` read off from `b`, and its projections onto `s^⊥`.
  let σ : Fin (k + 1) → ∀ x, V x := fun i x ↦ e.symm x (b i)
  have hσ (i : Fin (k + 1)) :
      ContMDiffOn IB (IB.prod 𝓘(ℝ, F)) n (fun x ↦ TotalSpace.mk' F x (σ i x)) e.baseSet := by
    intro x hx
    refine ((e.contMDiffAt_section_iff hx).mpr ?_).contMDiffWithinAt
    refine (contMDiffAt_const (c := b i)).congr_of_eventuallyEq ?_
    filter_upwards [e.open_baseSet.mem_nhds hx] with y hy
    simp [σ, e.apply_mk_symm hy]
  let Y : Fin k → ∀ x, V x := fun j x ↦ (ℂ ∙ s x)ᗮ.starProjection (σ j.succ x)
  have hY (j : Fin k) :
      ContMDiffOn IB (IB.prod 𝓘(ℝ, F)) n (fun x ↦ TotalSpace.mk' F x (Y j x)) U :=
    (g.contMDiff_starProjection_orthogonal_span_singleton hI s hs hne).comp_contMDiffOn
      ((hσ j.succ).mono inter_subset_left)
  -- In the fibre at `x ∈ U`, `σ` is the basis `b` transported by the trivialization.
  have hspan (x : B) (hx : x ∈ U) :
      Submodule.span ℂ (range (Y · x)) = g.orthogonalSpan hI s x := by
    let ex := e.continuousLinearEquivAt ℂ x hx.1
    have hσx (i : Fin (k + 1)) : σ i x = b.map ex.symm.toLinearEquiv i := by
      apply ex.injective
      simp [ex, σ, he, e.apply_mk_symm hx.1]
    have hbx : (b.map ex.symm.toLinearEquiv).repr (s x) 0 ≠ 0 := by
      simpa [ex, he] using hx.2
    rw [orthogonalSpan_eq, ← Submodule.span_range_starProjection_orthogonal_basis_succ _ hbx]
    simp only [Y, hσx]
  refine ⟨U, hℓ.isOpen_inter_preimage e.open_baseSet isOpen_compl_singleton,
    ⟨hx₀, by simpa [ℓ] using hb⟩, Y, ?_, hY⟩
  exact
    { continuousOn := fun j ↦ (hY j).continuousOn
      linearIndependent := fun hx ↦ by
        rw [linearIndependent_iff_card_eq_finrank_span, Set.finrank, hspan _ hx,
          g.finrank_orthogonalSpan hI s (hne _) hk, Fintype.card_fin]
      span_eq := fun hx ↦ hspan _ hx }

variable (hV : HasLocalContMDiffSubbundleFrames IB n F (Fin k) (g.orthogonalSpan hI s))

include hs in
/-- The map `(x, c, w) ↦ c • s x + w` from the sum of the trivial complex line bundle and `s^⊥`
to `V` is smooth. -/
theorem contMDiff_trivialProdOrthogonalSpan_sum :
    letI := hV.fiberBundle
    ContMDiff (IB.prod 𝓘(ℝ, ℂ × (Fin k → ℂ))) (IB.prod 𝓘(ℝ, F)) n
      (fun v : TotalSpace (ℂ × (Fin k → ℂ))
          (Bundle.Trivial B ℂ ×ᵇ fun x ↦ g.orthogonalSpan hI s x) ↦
        (⟨v.proj, (v.2.1 : ℂ) • s v.proj + (v.2.2 : V v.proj)⟩ : TotalSpace F V)) := by
  let := hV.fiberBundle
  let := hV.vectorBundle
  let := VectorBundle.restrictScalars ℝ ℂ (Fin k → ℂ) fun x ↦ g.orthogonalSpan hI s x
  let := hV.contMDiffVectorBundle
  intro v
  have hc := Bundle.contMDiffAt_totalSpace_prod_iff.mp
    (contMDiffAt_id (I := IB.prod 𝓘(ℝ, ℂ × (Fin k → ℂ))) (n := n) (x := v))
  obtain ⟨hpr, ha⟩ := Bundle.contMDiffAt_totalSpace_iff.mp hc.1
  -- `ha` reads the `Bundle.Trivial B ℂ` component in its trivialization, whose fibre map is the
  -- identity of `ℂ`; so it is literally the smoothness of the first fibre coordinate.
  have ha' : ContMDiffAt (IB.prod 𝓘(ℝ, ℂ × (Fin k → ℂ))) 𝓘(ℝ, ℂ) n
      (fun y : TotalSpace (ℂ × (Fin k → ℂ))
        (Bundle.Trivial B ℂ ×ᵇ fun x ↦ g.orthogonalSpan hI s x) ↦ (y.2.1 : ℂ)) v := ha
  have h₁ := ha'.smul_totalSpace (g := fun y ↦ (⟨y.proj, s y.proj⟩ : TotalSpace F V))
    ((hs v.proj).comp v hpr)
  have h₂ := (hV.contMDiff_totalSpace_inclusion ⟨v.proj, v.2.2⟩).comp v hc.2
  exact ContMDiffAt.add_sectionAlong
    (b := fun y : TotalSpace (ℂ × (Fin k → ℂ))
      (Bundle.Trivial B ℂ ×ᵇ fun x ↦ g.orthogonalSpan hI s x) ↦ y.proj)
    (s := fun y ↦ (y.2.1 : ℂ) • s y.proj) (t := fun y ↦ (y.2.2 : V y.proj)) h₁ h₂

include hs hne in
/-- The decomposition of `v ∈ V x` into its coefficient `‖s x‖⁻² ⟪s x, v⟫` along `s x` and its
orthogonal projection onto `s^⊥` is smooth. -/
theorem contMDiff_orthogonalSpan_decompose :
    letI := hV.fiberBundle
    letI : RiemannianBundle V := ⟨g.toRiemannianMetric⟩
    letI : ∀ x, InnerProductSpace ℂ (V x) := g.complexInnerProductSpace hI
    ContMDiff (IB.prod 𝓘(ℝ, F)) (IB.prod 𝓘(ℝ, ℂ × (Fin k → ℂ))) n
      (fun p : TotalSpace F V ↦ (⟨p.proj, ((‖s p.proj‖ ^ 2)⁻¹ • ⟪s p.proj, p.2⟫_ℂ,
        ⟨(ℂ ∙ s p.proj)ᗮ.starProjection p.2, g.starProjection_mem_orthogonalSpan hI s _ _⟩)⟩ :
        TotalSpace (ℂ × (Fin k → ℂ)) (Bundle.Trivial B ℂ ×ᵇ fun x ↦ g.orthogonalSpan hI s x))) := by
  let := hV.fiberBundle
  let := hV.vectorBundle
  let := VectorBundle.restrictScalars ℝ ℂ (Fin k → ℂ) fun x ↦ g.orthogonalSpan hI s x
  let := hV.contMDiffVectorBundle
  let : RiemannianBundle V := ⟨g.toRiemannianMetric⟩
  let : ∀ x, InnerProductSpace ℂ (V x) := g.complexInnerProductSpace hI
  have hb := Bundle.contMDiff_proj V (F := F) (IB := IB) (n := n)
  have hsp := hs.comp hb
  intro p
  refine Bundle.contMDiffAt_totalSpace_prod_iff.mpr ⟨?_, ?_⟩
  · refine Bundle.contMDiffAt_totalSpace_iff.mpr ⟨hb p, ?_⟩
    have hz (q : TotalSpace F V) : Inner.inner ℝ (s q.proj) (s q.proj) ≠ 0 :=
      inner_self_ne_zero.mpr (hne q.proj)
    -- The trivialization of `Bundle.Trivial B ℂ` is the identity on the fibre coordinate.
    exact (((hsp.inner_bundle hsp).inv₀ hz).smul (g.contMDiff_hermitianPairing hI hsp
      contMDiff_id) p).congr_of_eventuallyEq (Filter.Eventually.of_forall fun q ↦ by
        simp only [Pi.smul_apply', real_inner_self_eq_norm_sq]
        rfl)
  · exact hV.contMDiffAt_totalSpace_mk
      (g.contMDiff_starProjection_orthogonal_span_singleton hI s hs hne p) _

/-- **Splitting off the line of a nowhere-zero section.** For a nowhere-zero smooth section `s`
of a smooth Hermitian bundle `V`, the map `(x, c, w) ↦ c • s x + w` is a smooth bundle isomorphism
from the sum of the trivial complex line bundle and the orthogonal complement `s^⊥` onto `V`
(`trivialProdOrthogonalSpanDiffeomorph_apply`). Its inverse sends `v ∈ V x` to its coefficient
`‖s x‖⁻² ⟪s x, v⟫` along `s x` and to its orthogonal projection onto `s^⊥`
(`trivialProdOrthogonalSpanDiffeomorph_symm_apply`). -/
def trivialProdOrthogonalSpanDiffeomorph :
    letI := hV.fiberBundle
    Diffeomorph (IB.prod 𝓘(ℝ, ℂ × (Fin k → ℂ))) (IB.prod 𝓘(ℝ, F))
      (TotalSpace (ℂ × (Fin k → ℂ)) (Bundle.Trivial B ℂ ×ᵇ fun x ↦ g.orthogonalSpan hI s x))
      (TotalSpace F V) n := by
  let := hV.fiberBundle
  let : RiemannianBundle V := ⟨g.toRiemannianMetric⟩
  let : ∀ x, InnerProductSpace ℂ (V x) := g.complexInnerProductSpace hI
  have hnorm (x : B) : (‖s x‖ ^ 2 : ℝ) ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr (hne x))
  refine
    { toFun := fun v ↦ ⟨v.proj, (v.2.1 : ℂ) • s v.proj + (v.2.2 : V v.proj)⟩
      invFun := fun p ↦ ⟨p.proj, ((‖s p.proj‖ ^ 2)⁻¹ • ⟪s p.proj, p.2⟫_ℂ,
        ⟨(ℂ ∙ s p.proj)ᗮ.starProjection p.2, g.starProjection_mem_orthogonalSpan hI s _ _⟩)⟩
      left_inv := ?_
      right_inv := ?_
      contMDiff_toFun := g.contMDiff_trivialProdOrthogonalSpan_sum hI s hs hV
      contMDiff_invFun := g.contMDiff_orthogonalSpan_decompose hI s hs hne hV }
  · rintro ⟨x, c, w, hw⟩
    have hw' : w ∈ (ℂ ∙ s x)ᗮ := by rwa [← orthogonalSpan_eq]
    have h₁ : (‖s x‖ ^ 2)⁻¹ • ⟪s x, (c : ℂ) • s x + w⟫_ℂ = c := by
      simp only [inner_add_right, inner_smul_right,
        Submodule.mem_orthogonal_singleton_iff_inner_right.mp hw', add_zero,
        inner_self_eq_norm_sq_to_K]
      rw [Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_pow, ← div_eq_inv_mul]
      exact mul_div_cancel_right₀ _ (by simpa using hnorm x)
    have h₂ : (ℂ ∙ s x)ᗮ.starProjection ((c : ℂ) • s x + w) = w := by
      rw [map_add, map_smul, Submodule.starProjection_orthogonalComplement_singleton_eq_zero,
        smul_zero, zero_add]
      exact Submodule.starProjection_eq_self_iff.mpr hw'
    exact congrArg (TotalSpace.mk x) (Prod.ext h₁ (Subtype.ext h₂))
  · rintro ⟨x, v⟩
    apply congrArg (TotalSpace.mk x)
    dsimp only
    conv_rhs => rw [← Submodule.starProjection_add_starProjection_orthogonal (K := ℂ ∙ s x) v,
      Submodule.starProjection_singleton]
    simp only [Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_pow, div_eq_inv_mul]
    norm_cast

/-- The smooth splitting sends `(x, c, w)` to `c • s x + w`. -/
@[simp]
theorem trivialProdOrthogonalSpanDiffeomorph_apply
    (v : TotalSpace (ℂ × (Fin k → ℂ)) (Bundle.Trivial B ℂ ×ᵇ fun x ↦ g.orthogonalSpan hI s x)) :
    letI := hV.fiberBundle
    g.trivialProdOrthogonalSpanDiffeomorph hI s hs hne hV v =
      ⟨v.proj, (v.2.1 : ℂ) • s v.proj + (v.2.2 : V v.proj)⟩ :=
  (rfl)

/-- The inverse smooth splitting sends `v ∈ V x` to its coefficient `‖s x‖⁻² ⟪s x, v⟫` along
`s x` and its orthogonal projection onto `s^⊥`. -/
@[simp]
theorem trivialProdOrthogonalSpanDiffeomorph_symm_apply (p : TotalSpace F V) :
    letI := hV.fiberBundle
    letI : RiemannianBundle V := ⟨g.toRiemannianMetric⟩
    letI : ∀ x, InnerProductSpace ℂ (V x) := g.complexInnerProductSpace hI
    (g.trivialProdOrthogonalSpanDiffeomorph hI s hs hne hV).symm p =
      ⟨p.proj, ((‖s p.proj‖ ^ 2)⁻¹ • ⟪s p.proj, p.2⟫_ℂ,
        ⟨(ℂ ∙ s p.proj)ᗮ.starProjection p.2, g.starProjection_mem_orthogonalSpan hI s _ _⟩)⟩ :=
  (rfl)

end Bundle.ContMDiffRiemannianMetric

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
  {n : ℕ∞ω} {ι : Type*} {r : ℕ}

local instance instVectorBundleRealOrthogonalSpanFamily : VectorBundle ℝ F V :=
  VectorBundle.restrictScalars ℝ ℂ F V

/-- The Hermitian orthogonal complement `{s i x | i}ᗮ` of a family of sections, for the complex
inner product of an `i`-invariant smooth metric `g` (`orthogonalSpanFamily_eq`). -/
def orthogonalSpanFamily (g : ContMDiffRiemannianMetric IB n F V)
    (hI : ∀ x (v w : V x), g.inner x (Complex.I • v) (Complex.I • w) = g.inner x v w)
    (s : ι → ∀ x, V x) (x : B) : Submodule ℂ (V x) :=
  letI : RiemannianBundle V := ⟨g.toRiemannianMetric⟩
  letI := g.complexInnerProductSpace hI x
  (Submodule.span ℂ (range fun i ↦ s i x))ᗮ

variable (g : ContMDiffRiemannianMetric IB n F V)
  (hI : ∀ x (v w : V x), g.inner x (Complex.I • v) (Complex.I • w) = g.inner x v w)
  (s : ι → ∀ x, V x)

/-- `g.orthogonalSpanFamily hI s x` is the orthogonal complement of the span of the `s i x` for
the Hermitian inner product of `g`. -/
theorem orthogonalSpanFamily_eq (x : B) :
    letI : RiemannianBundle V := ⟨g.toRiemannianMetric⟩
    letI := g.complexInnerProductSpace hI x
    g.orthogonalSpanFamily hI s x = (Submodule.span ℂ (range fun i ↦ s i x))ᗮ :=
  (rfl)

/-- A vector lies in the orthogonal complement of the family `s` iff it is orthogonal to every
member of the family. -/
@[simp]
theorem mem_orthogonalSpanFamily_iff {x : B} {w : V x} :
    letI : RiemannianBundle V := ⟨g.toRiemannianMetric⟩
    letI := g.complexInnerProductSpace hI x
    w ∈ g.orthogonalSpanFamily hI s x ↔ ∀ i, ⟪s i x, w⟫_ℂ = 0 := by
  let : RiemannianBundle V := ⟨g.toRiemannianMetric⟩
  let := g.complexInnerProductSpace hI x
  rw [orthogonalSpanFamily_eq]
  exact (Submodule.mem_orthogonalBilin_span (B := innerₛₗ ℂ)).trans Set.forall_mem_range

/-- The total space of `s^⊥` carries the subspace topology of the total space of `V`. -/
instance instTopologicalSpaceTotalSpaceOrthogonalSpanFamily {F' : Type*} :
    TopologicalSpace (TotalSpace F' fun x ↦ g.orthogonalSpanFamily hI s x) :=
  subbundleTopology F (g.orthogonalSpanFamily hI s)

variable [Fintype ι]

/-- In a bundle of complex rank `card ι + r`, the orthogonal complement of an orthonormal family
indexed by `ι` has complex dimension `r`. -/
theorem finrank_orthogonalSpanFamily [FiniteDimensional ℂ F] {x : B}
    (hon : letI : RiemannianBundle V := ⟨g.toRiemannianMetric⟩
      letI := g.complexInnerProductSpace hI x
      Orthonormal ℂ fun i ↦ s i x)
    (hk : finrank ℂ F = Fintype.card ι + r) :
    finrank ℂ (g.orthogonalSpanFamily hI s x) = r := by
  let : RiemannianBundle V := ⟨g.toRiemannianMetric⟩
  let := g.complexInnerProductSpace hI x
  have : FiniteDimensional ℂ (V x) := VectorBundle.finiteDimensional ℂ F V x
  have h := (Submodule.span ℂ (range fun i ↦ s i x)).finrank_add_finrank_orthogonal
  rw [finrank_span_eq_card hon.linearIndependent, VectorBundle.finrank_eq ℂ F V x, hk] at h
  rw [orthogonalSpanFamily_eq]
  omega

/-- Removing from `v` its components `⟪s i x, v⟫ • s i x` along an orthonormal family leaves a
vector orthogonal to the family. -/
theorem sub_sum_inner_smul_mem_orthogonalSpanFamily {x : B}
    (hon : letI : RiemannianBundle V := ⟨g.toRiemannianMetric⟩
      letI := g.complexInnerProductSpace hI x
      Orthonormal ℂ fun i ↦ s i x) (v : V x) :
    letI : RiemannianBundle V := ⟨g.toRiemannianMetric⟩
    letI := g.complexInnerProductSpace hI x
    v - ∑ i, ⟪s i x, v⟫_ℂ • s i x ∈ g.orthogonalSpanFamily hI s x := by
  let : RiemannianBundle V := ⟨g.toRiemannianMetric⟩
  let := g.complexInnerProductSpace hI x
  refine (g.mem_orthogonalSpanFamily_iff hI s).mpr fun i ↦ ?_
  rw [inner_sub_right, hon.inner_right_fintype, sub_self]

/-- On the orthogonal complement of the family, removing the components along the family does
nothing. -/
theorem sub_sum_inner_smul_eq_self_of_mem_orthogonalSpanFamily {x : B} {w : V x}
    (hw : w ∈ g.orthogonalSpanFamily hI s x) :
    letI : RiemannianBundle V := ⟨g.toRiemannianMetric⟩
    letI := g.complexInnerProductSpace hI x
    w - ∑ i, ⟪s i x, w⟫_ℂ • s i x = w := by
  let : RiemannianBundle V := ⟨g.toRiemannianMetric⟩
  let := g.complexInnerProductSpace hI x
  have h := (g.mem_orthogonalSpanFamily_iff hI s).mp hw
  simp [h]

variable [ContMDiffVectorBundle n F V IB]
  (hs : ∀ i, ContMDiff IB (IB.prod 𝓘(ℝ, F)) n (fun x ↦ (⟨x, s i x⟩ : TotalSpace F V)))

omit [ContMDiffVectorBundle n F V IB] in
include hs in
/-- Removing the components along a family of smooth sections, `v ↦ v - ∑ i, ⟪s i x, v⟫ • s i x`,
is smooth on the total space. For an orthonormal family it is the orthogonal projection onto the
complement of the family. -/
theorem contMDiff_sub_sum_inner_smul :
    letI : RiemannianBundle V := ⟨g.toRiemannianMetric⟩
    letI : ∀ x, InnerProductSpace ℂ (V x) := g.complexInnerProductSpace hI
    ContMDiff (IB.prod 𝓘(ℝ, F)) (IB.prod 𝓘(ℝ, F)) n
      (fun p : TotalSpace F V ↦
        (⟨p.proj, p.2 - ∑ i, ⟪s i p.proj, p.2⟫_ℂ • s i p.proj⟩ : TotalSpace F V)) := by
  let : RiemannianBundle V := ⟨g.toRiemannianMetric⟩
  let : ∀ x, InnerProductSpace ℂ (V x) := g.complexInnerProductSpace hI
  have hb := Bundle.contMDiff_proj V (F := F) (IB := IB) (n := n)
  have hsp (i : ι) := (hs i).comp hb
  have hc (i : ι) := (g.contMDiff_hermitianPairing hI (hsp i) contMDiff_id).neg
  have hsum := ContMDiff.sum_sectionAlong (b := TotalSpace.proj) Finset.univ
    (fun i (p : TotalSpace F V) ↦ (-⟪s i p.proj, p.2⟫_ℂ) • s i p.proj) hb
    (fun i _ ↦ (hc i).smul_totalSpace (hsp i))
  apply (ContMDiff.add_sectionAlong (b := TotalSpace.proj) (s := fun p ↦ p.2) contMDiff_id
    hsum).congr
  intro p
  apply congrArg (TotalSpace.mk p.proj)
  simp only [neg_smul, Finset.sum_neg_distrib, sub_eq_add_neg]

include hs in
/-- **Smooth frames of the orthogonal complement of an orthonormal family.** Near every point, the
orthogonal complement of a pointwise orthonormal family of smooth sections, indexed by `ι`, of a
bundle of complex rank `card ι + r` has a smooth complex local frame with `r` members. Hence it is
a smooth complex subbundle (`TauCeti.HasLocalContMDiffSubbundleFrames.contMDiffVectorBundle`). -/
theorem hasLocalContMDiffSubbundleFrames_orthogonalSpanFamily [FiniteDimensional ℂ F]
    (hon : letI : RiemannianBundle V := ⟨g.toRiemannianMetric⟩
      letI : ∀ x, InnerProductSpace ℂ (V x) := g.complexInnerProductSpace hI
      ∀ x, Orthonormal ℂ fun i ↦ s i x)
    (hk : finrank ℂ F = Fintype.card ι + r) :
    HasLocalContMDiffSubbundleFrames IB n F (Fin r) (g.orthogonalSpanFamily hI s) := by
  let : RiemannianBundle V := ⟨g.toRiemannianMetric⟩
  let : ∀ x, InnerProductSpace ℂ (V x) := g.complexInnerProductSpace hI
  refine hasLocalContMDiffSubbundleFrames_iff.mpr fun x₀ ↦ ?_
  let e := trivializationAt F V x₀
  have hx₀ : x₀ ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' x₀
  have he (x : B) (hx : x ∈ e.baseSet) (v : V x) :
      e.continuousLinearEquivAt ℂ x hx v = (e ⟨x, v⟩).2 :=
    congrFun (e.continuousLinearEquivAt_apply ℂ x hx) v
  let b := Module.finBasis ℂ F
  -- The local frame of `V` read off from `b`, and its projections onto `s^⊥`.
  let σ : Fin (finrank ℂ F) → ∀ x, V x := fun j x ↦ e.symm x (b j)
  have hσ (j : Fin (finrank ℂ F)) :
      ContMDiffOn IB (IB.prod 𝓘(ℝ, F)) n (fun x ↦ TotalSpace.mk' F x (σ j x)) e.baseSet :=
    Manifold.contMDiffOn_symm_baseSet (I := IB) (e := e) (b j)
  let Y : Fin (finrank ℂ F) → ∀ x, V x := fun j x ↦ σ j x - ∑ i, ⟪s i x, σ j x⟫_ℂ • s i x
  have hY (j : Fin (finrank ℂ F)) :
      ContMDiffOn IB (IB.prod 𝓘(ℝ, F)) n (fun x ↦ TotalSpace.mk' F x (Y j x)) e.baseSet :=
    (g.contMDiff_sub_sum_inner_smul hI s hs).comp_contMDiffOn (hσ j)
  have hYmem (j : Fin (finrank ℂ F)) (x : B) : Y j x ∈ g.orthogonalSpanFamily hI s x :=
    g.sub_sum_inner_smul_mem_orthogonalSpanFamily hI s (hon x) _
  -- On the base set, the `Y j x` span the complement.
  have hspan (x : B) (hx : x ∈ e.baseSet) :
      Submodule.span ℂ (range (Y · x)) = g.orthogonalSpanFamily hI s x := by
    let ex := e.continuousLinearEquivAt ℂ x hx
    have hσx : (σ · x) = b.map ex.symm.toLinearEquiv := by
      funext j
      apply ex.injective
      simp [ex, σ, he, e.apply_mk_symm hx]
    refine le_antisymm (Submodule.span_le.mpr (range_subset_iff.mpr fun j ↦ hYmem j x))
      fun w hw ↦ ?_
    -- Expand `w` in the frame `σ · x`; removing the components along `s` fixes `w`.
    let P : V x →ₗ[ℂ] V x :=
      LinearMap.id - ∑ i, (innerₛₗ ℂ (s i x)).smulRight (s i x)
    have hP (v : V x) : P v = v - ∑ i, ⟪s i x, v⟫_ℂ • s i x := by
      simp [P, LinearMap.sum_apply]
    have hYP : (Y · x) = P ∘ (σ · x) := funext fun j ↦ (hP _).symm
    have hwP : P w = w :=
      (hP w).trans (g.sub_sum_inner_smul_eq_self_of_mem_orthogonalSpanFamily hI s hw)
    rw [hYP, range_comp, ← Submodule.map_span, hσx, (b.map _).span_eq]
    exact ⟨w, Submodule.mem_top, hwP⟩
  -- A linearly independent subfamily of the `Y j x₀` spanning the complement at `x₀`.
  obtain ⟨κ, a, ha, hsa, hla⟩ := exists_linearIndependent' ℂ (Y · x₀)
  have : Finite κ := Finite.of_injective a ha
  let := Fintype.ofFinite κ
  have hκ : Fintype.card κ = r := by
    rw [← finrank_span_eq_card hla, hsa, hspan x₀ hx₀,
      g.finrank_orthogonalSpanFamily hI s (hon x₀) hk]
  let f : Fin r → Fin (finrank ℂ F) := a ∘ (Fintype.equivFinOfCardEq hκ).symm
  let Z : Fin r → ∀ x, V x := fun j ↦ Y (f j)
  -- Read in the trivialization, linear independence of the frame is an open condition.
  let T : B → Fin r → F := fun x j ↦ (e ⟨x, Z j x⟩).2
  have hT : ContinuousOn T e.baseSet := continuousOn_pi.mpr fun j ↦
    continuous_snd.comp_continuousOn ((e.continuousOn).comp (hY (f j)).continuousOn
      fun x hx ↦ e.mem_source.mpr hx)
  have hTli (x : B) (hx : x ∈ e.baseSet) :
      LinearIndependent ℂ (T x) ↔ LinearIndependent ℂ (Z · x) := by
    have : T x = (e.continuousLinearEquivAt ℂ x hx) ∘ (Z · x) := funext fun j ↦ (he x hx _).symm
    rw [this]
    exact LinearMap.linearIndependent_iff (e.continuousLinearEquivAt ℂ x hx).toLinearMap
      (LinearEquiv.ker _)
  let U := e.baseSet ∩ T ⁻¹' {v | LinearIndependent ℂ v}
  have hUli {x : B} (hx : x ∈ U) : LinearIndependent ℂ (Z · x) := (hTli x hx.1).mp hx.2
  refine ⟨U, hT.isOpen_inter_preimage e.open_baseSet isOpen_setOfPred_linearIndependent,
    ⟨hx₀, (hTli x₀ hx₀).mpr (hla.comp _ (Fintype.equivFinOfCardEq hκ).symm.injective)⟩, Z, ?_,
    fun j ↦ (hY (f j)).mono inter_subset_left⟩
  exact
    { continuousOn := fun j ↦ ((hY (f j)).mono inter_subset_left).continuousOn
      linearIndependent := hUli
      span_eq := fun {x} hx ↦ by
        have : FiniteDimensional ℂ (V x) := VectorBundle.finiteDimensional ℂ F V x
        refine Submodule.eq_of_le_of_finrank_eq
          (Submodule.span_le.mpr (range_subset_iff.mpr fun j ↦ hYmem (f j) x)) ?_
        rw [finrank_span_eq_card (hUli hx), Fintype.card_fin,
          g.finrank_orthogonalSpanFamily hI s (hon x) hk] }

variable (hV : HasLocalContMDiffSubbundleFrames IB n F (Fin r) (g.orthogonalSpanFamily hI s))

include hs in
/-- The map `(x, c, w) ↦ ∑ i, c i • s i x + w` from the sum of the trivial bundle with fibre
`ι → ℂ` and `s^⊥` to `V` is smooth. -/
theorem contMDiff_trivialProdOrthogonalSpanFamily_sum :
    letI := hV.fiberBundle
    ContMDiff (IB.prod 𝓘(ℝ, (ι → ℂ) × (Fin r → ℂ))) (IB.prod 𝓘(ℝ, F)) n
      (fun v : TotalSpace ((ι → ℂ) × (Fin r → ℂ))
          (Bundle.Trivial B (ι → ℂ) ×ᵇ fun x ↦ g.orthogonalSpanFamily hI s x) ↦
        (⟨v.proj, ∑ i, (v.2.1 : ι → ℂ) i • s i v.proj + (v.2.2 : V v.proj)⟩ :
          TotalSpace F V)) := by
  let := hV.fiberBundle
  let := hV.vectorBundle
  let := VectorBundle.restrictScalars ℝ ℂ (Fin r → ℂ) fun x ↦ g.orthogonalSpanFamily hI s x
  let := hV.contMDiffVectorBundle
  intro v
  have hc := Bundle.contMDiffAt_totalSpace_prod_iff.mp
    (contMDiffAt_id (I := IB.prod 𝓘(ℝ, (ι → ℂ) × (Fin r → ℂ))) (n := n) (x := v))
  obtain ⟨hpr, ha⟩ := Bundle.contMDiffAt_totalSpace_iff.mp hc.1
  -- `ha` reads the `Bundle.Trivial B (ι → ℂ)` component in its trivialization, whose fibre map is
  -- the identity of `ι → ℂ`; so it is literally the smoothness of the first fibre coordinate.
  have ha' : ContMDiffAt (IB.prod 𝓘(ℝ, (ι → ℂ) × (Fin r → ℂ))) 𝓘(ℝ, ι → ℂ) n
      (fun y : TotalSpace ((ι → ℂ) × (Fin r → ℂ))
        (Bundle.Trivial B (ι → ℂ) ×ᵇ fun x ↦ g.orthogonalSpanFamily hI s x) ↦
          (y.2.1 : ι → ℂ)) v := ha
  have h₁ := ContMDiffAt.sum_sectionAlong
    (b := fun y : TotalSpace ((ι → ℂ) × (Fin r → ℂ))
      (Bundle.Trivial B (ι → ℂ) ×ᵇ fun x ↦ g.orthogonalSpanFamily hI s x) ↦ y.proj)
    Finset.univ (fun i y ↦ (y.2.1 : ι → ℂ) i • s i y.proj) hpr fun i _ ↦
      ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : ι ↦ ℂ) i).restrictScalars ℝ
        |>.contMDiff.contMDiffAt.comp v ha').smul_totalSpace
        (g := fun y ↦ (⟨y.proj, s i y.proj⟩ : TotalSpace F V)) ((hs i v.proj).comp v hpr)
  have h₂ := (hV.contMDiff_totalSpace_inclusion ⟨v.proj, v.2.2⟩).comp v hc.2
  exact ContMDiffAt.add_sectionAlong
    (b := fun y : TotalSpace ((ι → ℂ) × (Fin r → ℂ))
      (Bundle.Trivial B (ι → ℂ) ×ᵇ fun x ↦ g.orthogonalSpanFamily hI s x) ↦ y.proj)
    (s := fun y ↦ ∑ i, (y.2.1 : ι → ℂ) i • s i y.proj) (t := fun y ↦ (y.2.2 : V y.proj)) h₁ h₂

include hs in
/-- For an orthonormal family, the decomposition of `v ∈ V x` into its coefficients `⟪s i x, v⟫`
and its orthogonal projection `v - ∑ i, ⟪s i x, v⟫ • s i x` onto `s^⊥` is smooth. -/
theorem contMDiff_orthogonalSpanFamily_decompose
    (hon : letI : RiemannianBundle V := ⟨g.toRiemannianMetric⟩
      letI : ∀ x, InnerProductSpace ℂ (V x) := g.complexInnerProductSpace hI
      ∀ x, Orthonormal ℂ fun i ↦ s i x) :
    letI := hV.fiberBundle
    letI : RiemannianBundle V := ⟨g.toRiemannianMetric⟩
    letI : ∀ x, InnerProductSpace ℂ (V x) := g.complexInnerProductSpace hI
    ContMDiff (IB.prod 𝓘(ℝ, F)) (IB.prod 𝓘(ℝ, (ι → ℂ) × (Fin r → ℂ))) n
      (fun p : TotalSpace F V ↦ (⟨p.proj, (fun i ↦ ⟪s i p.proj, p.2⟫_ℂ,
        ⟨p.2 - ∑ i, ⟪s i p.proj, p.2⟫_ℂ • s i p.proj,
          g.sub_sum_inner_smul_mem_orthogonalSpanFamily hI s (hon _) _⟩)⟩ :
        TotalSpace ((ι → ℂ) × (Fin r → ℂ))
          (Bundle.Trivial B (ι → ℂ) ×ᵇ fun x ↦ g.orthogonalSpanFamily hI s x))) := by
  let := hV.fiberBundle
  let := hV.vectorBundle
  let := VectorBundle.restrictScalars ℝ ℂ (Fin r → ℂ) fun x ↦ g.orthogonalSpanFamily hI s x
  let := hV.contMDiffVectorBundle
  let : RiemannianBundle V := ⟨g.toRiemannianMetric⟩
  let : ∀ x, InnerProductSpace ℂ (V x) := g.complexInnerProductSpace hI
  have hb := Bundle.contMDiff_proj V (F := F) (IB := IB) (n := n)
  intro p
  refine Bundle.contMDiffAt_totalSpace_prod_iff.mpr ⟨?_, ?_⟩
  · refine Bundle.contMDiffAt_totalSpace_iff.mpr ⟨hb p, ?_⟩
    -- The trivialization of `Bundle.Trivial B (ι → ℂ)` is the identity on the fibre coordinate.
    exact contMDiffAt_pi_module_iff.mpr fun i ↦
      g.contMDiff_hermitianPairing hI ((hs i).comp hb) contMDiff_id p
  · exact hV.contMDiffAt_totalSpace_mk (g.contMDiff_sub_sum_inner_smul hI s hs p) _

/-- **Splitting off the span of an orthonormal family.** For a pointwise orthonormal family `s` of
smooth sections of a smooth Hermitian bundle `V`, the map `(x, c, w) ↦ ∑ i, c i • s i x + w` is a
smooth bundle isomorphism from the sum of the trivial bundle with fibre `ι → ℂ` and the orthogonal
complement `s^⊥` onto `V` (`trivialProdOrthogonalSpanFamilyDiffeomorph_apply`). Its inverse sends
`v ∈ V x` to its coefficients `⟪s i x, v⟫` and to `v - ∑ i, ⟪s i x, v⟫ • s i x`
(`trivialProdOrthogonalSpanFamilyDiffeomorph_symm_apply`). -/
def trivialProdOrthogonalSpanFamilyDiffeomorph
    (hon : letI : RiemannianBundle V := ⟨g.toRiemannianMetric⟩
      letI : ∀ x, InnerProductSpace ℂ (V x) := g.complexInnerProductSpace hI
      ∀ x, Orthonormal ℂ fun i ↦ s i x) :
    letI := hV.fiberBundle
    Diffeomorph (IB.prod 𝓘(ℝ, (ι → ℂ) × (Fin r → ℂ))) (IB.prod 𝓘(ℝ, F))
      (TotalSpace ((ι → ℂ) × (Fin r → ℂ))
        (Bundle.Trivial B (ι → ℂ) ×ᵇ fun x ↦ g.orthogonalSpanFamily hI s x))
      (TotalSpace F V) n := by
  let := hV.fiberBundle
  let : RiemannianBundle V := ⟨g.toRiemannianMetric⟩
  let : ∀ x, InnerProductSpace ℂ (V x) := g.complexInnerProductSpace hI
  refine
    { toFun := fun v ↦ ⟨v.proj, ∑ i, (v.2.1 : ι → ℂ) i • s i v.proj + (v.2.2 : V v.proj)⟩
      invFun := fun p ↦ ⟨p.proj, (fun i ↦ ⟪s i p.proj, p.2⟫_ℂ,
        ⟨p.2 - ∑ i, ⟪s i p.proj, p.2⟫_ℂ • s i p.proj,
          g.sub_sum_inner_smul_mem_orthogonalSpanFamily hI s (hon _) _⟩)⟩
      left_inv := ?_
      right_inv := ?_
      contMDiff_toFun := g.contMDiff_trivialProdOrthogonalSpanFamily_sum hI s hs hV
      contMDiff_invFun := g.contMDiff_orthogonalSpanFamily_decompose hI s hs hV hon }
  · rintro ⟨x, c, w, hw⟩
    have hw' := (g.mem_orthogonalSpanFamily_iff hI s).mp hw
    have h₁ : (fun i ↦ ⟪s i x, ∑ j, c j • s j x + w⟫_ℂ) = c := by
      funext i
      rw [inner_add_right, (hon x).inner_right_fintype, hw', add_zero]
    have h₂ : ∑ j, c j • s j x + w - ∑ i, ⟪s i x, ∑ j, c j • s j x + w⟫_ℂ • s i x = w := by
      have h₁' (i : ι) : ⟪s i x, ∑ j, c j • s j x + w⟫_ℂ = c i := congrFun h₁ i
      simp only [h₁', add_sub_cancel_left]
    exact congrArg (TotalSpace.mk x) (Prod.ext h₁ (Subtype.ext h₂))
  · rintro ⟨x, v⟩
    apply congrArg (TotalSpace.mk x)
    dsimp only
    abel

/-- The smooth splitting sends `(x, c, w)` to `∑ i, c i • s i x + w`. -/
@[simp]
theorem trivialProdOrthogonalSpanFamilyDiffeomorph_apply
    (hon : letI : RiemannianBundle V := ⟨g.toRiemannianMetric⟩
      letI : ∀ x, InnerProductSpace ℂ (V x) := g.complexInnerProductSpace hI
      ∀ x, Orthonormal ℂ fun i ↦ s i x)
    (v : TotalSpace ((ι → ℂ) × (Fin r → ℂ))
      (Bundle.Trivial B (ι → ℂ) ×ᵇ fun x ↦ g.orthogonalSpanFamily hI s x)) :
    letI := hV.fiberBundle
    g.trivialProdOrthogonalSpanFamilyDiffeomorph hI s hs hV hon v =
      ⟨v.proj, ∑ i, (v.2.1 : ι → ℂ) i • s i v.proj + (v.2.2 : V v.proj)⟩ :=
  (rfl)

/-- The inverse smooth splitting sends `v ∈ V x` to its coefficients `⟪s i x, v⟫` and to
`v - ∑ i, ⟪s i x, v⟫ • s i x`. -/
@[simp]
theorem trivialProdOrthogonalSpanFamilyDiffeomorph_symm_apply
    (hon : letI : RiemannianBundle V := ⟨g.toRiemannianMetric⟩
      letI : ∀ x, InnerProductSpace ℂ (V x) := g.complexInnerProductSpace hI
      ∀ x, Orthonormal ℂ fun i ↦ s i x)
    (p : TotalSpace F V) :
    letI := hV.fiberBundle
    letI : RiemannianBundle V := ⟨g.toRiemannianMetric⟩
    letI : ∀ x, InnerProductSpace ℂ (V x) := g.complexInnerProductSpace hI
    (g.trivialProdOrthogonalSpanFamilyDiffeomorph hI s hs hV hon).symm p =
      ⟨p.proj, (fun i ↦ ⟪s i p.proj, p.2⟫_ℂ,
        ⟨p.2 - ∑ i, ⟪s i p.proj, p.2⟫_ℂ • s i p.proj,
          g.sub_sum_inner_smul_mem_orthogonalSpanFamily hI s (hon _) _⟩)⟩ :=
  (rfl)

end Bundle.ContMDiffRiemannianMetric
