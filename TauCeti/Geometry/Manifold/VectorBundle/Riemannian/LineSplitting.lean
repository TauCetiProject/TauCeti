/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.OrthogonalComplement
public import TauCeti.Geometry.Manifold.VectorBundle.Section.Generic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import TauCeti.Geometry.Manifold.VectorBundle.Scalar
import TauCeti.Geometry.Manifold.VectorBundle.Translate

/-!
# Splitting a complex bundle into a trivial bundle and a line bundle

Let `V` be a smooth complex vector bundle over a real manifold with a smooth Hermitian metric `g`,
and let `s₁, …, s_k` be smooth sections of `V` that are orthonormal at every point. The Hermitian
orthogonal complements `{s₁ x, …, s_k x}ᗮ` (`Bundle.ContMDiffRiemannianMetric.orthogonalSpanFamily`)
have smooth complex local frames
(`Bundle.ContMDiffRiemannianMetric.hasLocalContMDiffSubbundleFrames_orthogonalSpanFamily`), so they
form a smooth complex subbundle `s^⊥` of `V`, and

  `V ≅ (B × ℂᵏ) ⊕ s^⊥`, `(x, c, w) ↦ ∑ i, c i • s i x + w`,

as smooth bundles (`Bundle.ContMDiffRiemannianMetric.trivialProdOrthogonalSpanFamilyDiffeomorph`).
The inverse sends `v` to its coefficients `⟪s i x, v⟫` and to `v - ∑ i, ⟪s i x, v⟫ • s i x`.

Near a point, the orthogonal projections of a local frame of `V` read off from a trivialization span
the complement; a linearly independent subfamily at the point stays linearly independent nearby,
and has the right size, so it is a local frame of the complement.

Over a compact boundaryless manifold of real dimension less than four, a smooth complex bundle `V`
of complex rank `n + 1` has `n` pointwise orthonormal smooth sections
(`TauCeti.exists_orthonormal_contMDiffSection_of_finrank_lt`): the complement of the sections chosen
so far is a smooth complex bundle of real rank at least four, so it has a nowhere-zero smooth
section (`TauCeti.exists_contMDiffSection_forall_ne_zero_of_finrank_lt`), which is normalized and
appended. Their complement `L` is a smooth complex line subbundle and `V ≅ (B × ℂⁿ) ⊕ L`
(`TauCeti.exists_trivialProdLineSubbundle_diffeomorph`). This is the splitting step of the proof
of the Riemann–Roch theorem for Cauchy–Riemann operators over a closed surface.

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
theorem mem_orthogonalSpanFamily_iff {x : B} {w : V x} :
    letI : RiemannianBundle V := ⟨g.toRiemannianMetric⟩
    letI := g.complexInnerProductSpace hI x
    w ∈ g.orthogonalSpanFamily hI s x ↔ ∀ i, ⟪s i x, w⟫_ℂ = 0 := by
  let : RiemannianBundle V := ⟨g.toRiemannianMetric⟩
  let := g.complexInnerProductSpace hI x
  rw [orthogonalSpanFamily_eq, Submodule.mem_orthogonal]
  refine ⟨fun h i ↦ h _ (Submodule.subset_span (mem_range_self i)), fun h u hu ↦ ?_⟩
  induction hu using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨i, rfl⟩ := hu
    exact h i
  | zero => exact inner_zero_left _
  | add u v _ _ hu hv => rw [inner_add_left, hu, hv, add_zero]
  | smul c u _ hu => rw [inner_smul_left, hu, mul_zero]

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
      ContMDiffOn IB (IB.prod 𝓘(ℝ, F)) n (fun x ↦ TotalSpace.mk' F x (σ j x)) e.baseSet := by
    intro x hx
    refine ((e.contMDiffAt_section_iff hx).mpr ?_).contMDiffWithinAt
    refine (contMDiffAt_const (c := b j)).congr_of_eventuallyEq ?_
    filter_upwards [e.open_baseSet.mem_nhds hx] with y hy
    simp [σ, e.apply_mk_symm hy]
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
  obtain ⟨hpr, ha⟩ := Bundle.contMDiffAt_totalSpace.mp hc.1
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
  · refine Bundle.contMDiffAt_totalSpace.mpr ⟨hb p, ?_⟩
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

namespace TauCeti

open Bundle.ContMDiffRiemannianMetric

variable {X B F : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
  [TopologicalSpace B] [ChartedSpace X B] [T2Space B] [CompactSpace B]
  [IsManifold 𝓘(ℝ, X) ∞ B]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]
  [FiniteDimensional ℂ F]
  {V : B → Type*}
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [∀ x, Module ℂ (V x)]
  [∀ x, IsScalarTower ℝ ℂ (V x)] [∀ x, TopologicalSpace (V x)]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℂ F V]

local instance instVectorBundleRealLineSplitting : VectorBundle ℝ F V :=
  VectorBundle.restrictScalars ℝ ℂ F V

variable [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, X)]

/-- **Orthonormal smooth sections.** Let `V` be a smooth Hermitian bundle of complex rank `k + r`
over a compact boundaryless manifold of real dimension less than `2 (r + 1)`. Then `V` has `k`
smooth sections that are orthonormal at every point. The sections are chosen one at a time: the
orthogonal complement of the sections chosen so far is a smooth complex bundle of real rank
at least `2 (r + 1)`, so it has a nowhere-zero smooth section, which is normalized. -/
theorem exists_orthonormal_contMDiffSection_of_finrank_lt
    (g : ContMDiffRiemannianMetric 𝓘(ℝ, X) ∞ F V)
    (hI : ∀ x (v w : V x), g.inner x (Complex.I • v) (Complex.I • w) = g.inner x v w)
    {k r : ℕ} (hk : finrank ℂ F = k + r) (hdim : finrank ℝ X < 2 * (r + 1)) :
    ∃ s : Fin k → ∀ x, V x,
      (∀ i, ContMDiff 𝓘(ℝ, X) (𝓘(ℝ, X).prod 𝓘(ℝ, F)) ∞
        (fun x ↦ (⟨x, s i x⟩ : TotalSpace F V))) ∧
      letI : RiemannianBundle V := ⟨g.toRiemannianMetric⟩
      letI : ∀ x, InnerProductSpace ℂ (V x) := g.complexInnerProductSpace hI
      ∀ x, Orthonormal ℂ fun i ↦ s i x := by
  let : RiemannianBundle V := ⟨g.toRiemannianMetric⟩
  let : ∀ x, InnerProductSpace ℂ (V x) := g.complexInnerProductSpace hI
  induction k generalizing r with
  | zero => exact ⟨Fin.elim0, fun i ↦ i.elim0, fun _ ↦ ⟨fun i ↦ i.elim0, fun i ↦ i.elim0⟩⟩
  | succ k ih =>
    obtain ⟨s, hs, hon⟩ := ih (r := r + 1) (by rw [hk]; ring) (by omega)
    have hW := g.hasLocalContMDiffSubbundleFrames_orthogonalSpanFamily hI s hs hon (r := r + 1)
      (by rw [hk, Fintype.card_fin]; ring)
    let W := g.orthogonalSpanFamily hI s
    let := hW.fiberBundle
    let := hW.vectorBundle
    let := VectorBundle.restrictScalars ℝ ℂ (Fin (r + 1) → ℂ) fun x ↦ W x
    let := hW.contMDiffVectorBundle
    -- A nowhere-zero smooth section of the complement of the sections chosen so far.
    have hr : finrank ℝ X < finrank ℝ (Fin (r + 1) → ℂ) := by
      simp [Module.finrank_pi_fintype, Complex.finrank_real_complex]
      omega
    obtain ⟨t, ht⟩ := exists_contMDiffSection_forall_ne_zero_of_finrank_lt
      (V := fun x ↦ W x) (F := Fin (r + 1) → ℂ) hr
    let u : ∀ x, V x := fun x ↦ (t x : V x)
    have hu : ContMDiff 𝓘(ℝ, X) (𝓘(ℝ, X).prod 𝓘(ℝ, F)) ∞
        (fun x ↦ (⟨x, u x⟩ : TotalSpace F V)) :=
      hW.contMDiff_totalSpace_inclusion.comp t.contMDiff
    have hu₀ (x : B) : u x ≠ 0 := by simpa [u] using ht x
    -- Normalize it.
    let c : B → ℂ := fun x ↦ ((‖u x‖⁻¹ : ℝ) : ℂ)
    have hc : ContMDiff 𝓘(ℝ, X) 𝓘(ℝ, ℂ) ∞ c := by
      refine Complex.ofRealCLM.contMDiff.comp fun x ↦ ?_
      have hd := hu.inner_bundle hu x
      have hne : Inner.inner ℝ (u x) (u x) ≠ 0 := inner_self_ne_zero.mpr (hu₀ x)
      refine (ContDiffAt.comp_contMDiffAt (f := fun y ↦ Inner.inner ℝ (u y) (u y))
        ((Real.contDiffAt_sqrt hne).inv (Real.sqrt_ne_zero'.mpr
        (lt_of_le_of_ne real_inner_self_nonneg hne.symm))) hd).congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun y ↦ ?_)
      change ‖u y‖⁻¹ = (√(Inner.inner ℝ (u y) (u y)))⁻¹
      rw [real_inner_self_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]
    let s' : Fin (k + 1) → ∀ x, V x := Fin.snoc (α := fun _ ↦ ∀ x, V x) s fun x ↦ c x • u x
    refine ⟨s', fun i ↦ ?_, fun x ↦ ?_⟩
    · induction i using Fin.lastCases with
      | last => simpa [s'] using hc.smul_totalSpace hu
      | cast i => simpa [s'] using hs i
    · have hux : u x ∈ W x := (t x).2
      have horth (i : Fin k) : ⟪s i x, c x • u x⟫_ℂ = 0 := by
        rw [inner_smul_right, (g.mem_orthogonalSpanFamily_iff hI s).mp hux i, mul_zero]
      have hnorm : ‖c x • u x‖ = 1 := by
        rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_norm,
          inv_mul_cancel₀ (norm_ne_zero_iff.mpr (hu₀ x))]
      rw [orthonormal_iff_ite]
      intro i j
      induction i using Fin.lastCases with
      | last =>
        induction j using Fin.lastCases with
        | last => simp [s', inner_self_eq_norm_sq_to_K, hnorm]
        | cast j =>
          simp [s', (Fin.castSucc_ne_last j).symm, inner_eq_zero_symm.mp (horth j)]
      | cast i =>
        induction j using Fin.lastCases with
        | last => simp [s', (Fin.castSucc_ne_last i), horth i]
        | cast j =>
          simpa [s', Fin.castSucc_inj] using orthonormal_iff_ite.mp (hon x) i j

/-- **Splitting off a trivial bundle.** A smooth complex vector bundle `V` of complex rank `n + 1`
over a compact boundaryless manifold of real dimension less than four, in particular over a closed
surface, has a smooth Hermitian metric `g` and `n` pointwise orthonormal smooth sections `s` whose
orthogonal complement `L = s^⊥` is a smooth complex line subbundle, and
`V ≅ (B × ℂⁿ) ⊕ L` as smooth bundles, by `(x, c, w) ↦ ∑ i, c i • s i x + w`
(`Bundle.ContMDiffRiemannianMetric.trivialProdOrthogonalSpanFamilyDiffeomorph`). -/
theorem exists_trivialProdLineSubbundle_diffeomorph [∀ x, ContinuousConstSMul ℂ (V x)] {n : ℕ}
    (hn : finrank ℂ F = n + 1) (hdim : finrank ℝ X < 4) :
    ∃ (g : ContMDiffRiemannianMetric 𝓘(ℝ, X) ∞ F V)
      (hI : ∀ x (v w : V x), g.inner x (Complex.I • v) (Complex.I • w) = g.inner x v w)
      (s : Fin n → ∀ x, V x),
      (∀ i, ContMDiff 𝓘(ℝ, X) (𝓘(ℝ, X).prod 𝓘(ℝ, F)) ∞
        (fun x ↦ (⟨x, s i x⟩ : TotalSpace F V))) ∧
      (letI : RiemannianBundle V := ⟨g.toRiemannianMetric⟩
       letI : ∀ x, InnerProductSpace ℂ (V x) := g.complexInnerProductSpace hI
       ∀ x, Orthonormal ℂ fun i ↦ s i x) ∧
      ∃ hL : HasLocalContMDiffSubbundleFrames 𝓘(ℝ, X) ∞ F (Fin 1) (g.orthogonalSpanFamily hI s),
        letI := hL.fiberBundle
        Nonempty (Diffeomorph (𝓘(ℝ, X).prod 𝓘(ℝ, (Fin n → ℂ) × (Fin 1 → ℂ)))
          (𝓘(ℝ, X).prod 𝓘(ℝ, F))
          (TotalSpace ((Fin n → ℂ) × (Fin 1 → ℂ))
            (Bundle.Trivial B (Fin n → ℂ) ×ᵇ fun x ↦ g.orthogonalSpanFamily hI s x))
          (TotalSpace F V) ∞) := by
  obtain ⟨g, hI⟩ := exists_contMDiffRiemannianMetric_inner_smul_I (IB := 𝓘(ℝ, X)) (n := ⊤)
    (F := F) (V := V)
  obtain ⟨s, hs, hon⟩ := exists_orthonormal_contMDiffSection_of_finrank_lt g hI hn (r := 1)
    (by omega)
  have hL := g.hasLocalContMDiffSubbundleFrames_orthogonalSpanFamily hI s hs hon (r := 1)
    (by rw [hn, Fintype.card_fin])
  exact ⟨g, hI, s, hs, hon, hL, ⟨g.trivialProdOrthogonalSpanFamilyDiffeomorph hI s hs hL hon⟩⟩

end TauCeti
