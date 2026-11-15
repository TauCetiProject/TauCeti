/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
public import Mathlib.Geometry.Manifold.VectorBundle.LocalFrame
public import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
public import TauCeti.Topology.VectorBundle.GramSchmidt
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Geometry.Manifold.Algebra.Structures
import TauCeti.Geometry.Manifold.VectorBundle.Translate
import TauCeti.Geometry.Manifold.VectorBundle.Scalar

/-!
# Smooth Gram–Schmidt in Riemannian vector bundles

Gram–Schmidt preserves the differentiability of a family of sections wherever the input
vectors are linearly independent. These local statements apply without choosing a bundle
trivialization and allow the construction of smooth orthonormal frames from smooth frames.
The orthogonalization and normalization are Mathlib's `InnerProductSpace.gramSchmidt` and
`InnerProductSpace.gramSchmidtNormed`.

The sectionwise induction follows `ContinuousWithinAt.gramSchmidt_bundle` in
`TauCeti.Topology.VectorBundle.GramSchmidt`, which adapts Patrick Massot and Michael Rothgang's
construction in Mathlib PR [#26221](https://github.com/leanprover-community/mathlib4/pull/26221).
Here smooth section operations replace the coordinate calculations of the continuity proof.
In particular, the Gram–Schmidt orthonormal basis `Bundle.Trivialization.orthonormalBasis` of a
compatible local trivialization of a finite-rank Riemannian bundle is smooth over its base set
(`Bundle.Trivialization.contMDiffOn_orthonormalBasis`).

Orthonormalizing the local frame of a bundle trivialization shows that every point of a `C^n`
Riemannian vector bundle with finite-dimensional model fibre has a neighbourhood carrying a `C^n`
orthonormal local frame (`TauCeti.exists_isLocalFrameOn_orthonormal`).
-/

public section

open Bundle InnerProductSpace
open scoped ContDiff Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  {n : ℕ∞ω} [hmetric : IsContMDiffRiemannianBundle I n F V]
  {ι : Type*} [LinearOrder ι] [LocallyFiniteOrderBot ι]
  {v : ι → Π x : M, V x} {x : M}

attribute [local instance] IsWellOrder.toHasWellFounded

section Along

variable {EP HP P : Type*} [NormedAddCommGroup EP] [NormedSpace ℝ EP]
  [TopologicalSpace HP] [TopologicalSpace P] [ChartedSpace HP P]
  {IP : ModelWithCorners ℝ EP HP} {b : P → M} {v : ι → ∀ y, V (b y)}
  {s : Set P} {x : P}

/-- Fiberwise Gram–Schmidt preserves `C^n` regularity within a set along an arbitrary base
map. Only the inputs through `j` need to be regular, and those before `j` independent. -/
theorem ContMDiffWithinAt.gramSchmidt_bundle (j : ι)
    (hv : ∀ i ≤ j, ContMDiffWithinAt IP (I.prod 𝓘(ℝ, F)) n
      (fun y ↦ TotalSpace.mk' F (b y) (v i y)) s x)
    (hli : LinearIndepOn ℝ (fun i ↦ v i x) (Set.Iio j)) :
    ContMDiffWithinAt IP (I.prod 𝓘(ℝ, F)) n
      (fun y ↦ TotalSpace.mk' F (b y) (gramSchmidt ℝ (fun i ↦ v i y) j)) s x := by
  classical
  induction j using WellFoundedLT.induction with
  | ind j ih =>
    have hg (i : ι) (hi : i < j) :=
      ih i hi (fun k hk ↦ hv k (hk.trans hi.le)) (hli.mono (Set.Iio_subset_Iio hi.le))
    have hc (i : ι) (hi : i < j) :
        ContMDiffWithinAt IP 𝓘(ℝ) n
          (fun y ↦ inner ℝ (gramSchmidt ℝ (fun k ↦ v k y) i) (v j y) /
            inner ℝ (gramSchmidt ℝ (fun k ↦ v k y) i)
              (gramSchmidt ℝ (fun k ↦ v k y) i)) s x :=
      ((hg i hi).inner_bundle (hv j le_rfl)).div₀ ((hg i hi).inner_bundle (hg i hi))
        (inner_self_ne_zero.mpr (gramSchmidt_ne_zero_coe i
          (hli.mono (Set.Iic_subset_Iio.mpr hi))))
    have hformula : (fun y ↦ gramSchmidt ℝ (fun i ↦ v i y) j) =
        v j - ∑ i ∈ Finset.Iio j,
          (fun y ↦ inner ℝ (gramSchmidt ℝ (fun k ↦ v k y) i) (v j y) /
            inner ℝ (gramSchmidt ℝ (fun k ↦ v k y) i)
              (gramSchmidt ℝ (fun k ↦ v k y) i)) •
            (fun y ↦ gramSchmidt ℝ (fun k ↦ v k y) i) := by
      funext y
      simp only [Pi.sub_apply, Finset.sum_apply, real_inner_self_eq_norm_sq]
      exact eq_sub_of_add_eq (gramSchmidt_def'' ℝ (fun i ↦ v i y) j).symm
    have hb := (contMDiffAt_proj V).comp_contMDiffWithinAt x (hv j le_rfl)
    have hs := (hv j le_rfl).sub_sectionAlong
      (ContMDiffWithinAt.sum_sectionAlong (Finset.Iio j) _ hb
        fun i hi ↦ (hc i (Finset.mem_Iio.mp hi)).smul_totalSpace (hg i (Finset.mem_Iio.mp hi)))
    have heq (y : P) := congrArg (TotalSpace.mk' F (b y)) (congrFun hformula y)
    exact hs.congr (fun y _ ↦ by simpa using heq y) (by simpa using heq x)

/-- Fiberwise Gram–Schmidt preserves `C^n` regularity along an arbitrary base map.
Only the inputs through `j` need to be regular, and those before `j` independent. -/
theorem ContMDiffAt.gramSchmidt_bundle (j : ι)
    (hv : ∀ i ≤ j, ContMDiffAt IP (I.prod 𝓘(ℝ, F)) n
      (fun y ↦ TotalSpace.mk' F (b y) (v i y)) x)
    (hli : LinearIndepOn ℝ (fun i ↦ v i x) (Set.Iio j)) :
    ContMDiffAt IP (I.prod 𝓘(ℝ, F)) n
      (fun y ↦ TotalSpace.mk' F (b y) (gramSchmidt ℝ (fun i ↦ v i y) j)) x :=
  ContMDiffWithinAt.gramSchmidt_bundle j hv hli

/-- Fiberwise normalized Gram–Schmidt preserves `C^n` regularity within a set along an
arbitrary base map, assuming regularity and independence only through the requested index. -/
theorem ContMDiffWithinAt.gramSchmidtNormed_bundle (j : ι)
    (hv : ∀ i ≤ j, ContMDiffWithinAt IP (I.prod 𝓘(ℝ, F)) n
      (fun y ↦ TotalSpace.mk' F (b y) (v i y)) s x)
    (hli : LinearIndepOn ℝ (fun i ↦ v i x) (Set.Iic j)) :
    ContMDiffWithinAt IP (I.prod 𝓘(ℝ, F)) n
      (fun y ↦ TotalSpace.mk' F (b y) (gramSchmidtNormed ℝ (fun i ↦ v i y) j)) s x := by
  have hg := ContMDiffWithinAt.gramSchmidt_bundle j hv (hli.mono Set.Iio_subset_Iic_self)
  have hh : ContMDiffWithinAt IP 𝓘(ℝ) n (fun y ↦ inner ℝ (gramSchmidt ℝ (fun i ↦ v i y) j)
      (gramSchmidt ℝ (fun i ↦ v i y) j)) s x := hg.inner_bundle hg
  have hn : ContMDiffWithinAt IP 𝓘(ℝ) n
      (fun y ↦ ‖gramSchmidt ℝ (fun i ↦ v i y) j‖) s x := by
    have hr : ContDiffAt ℝ n Real.sqrt ((fun y : P ↦
        inner ℝ (gramSchmidt ℝ (fun i ↦ v i y) j)
          (gramSchmidt ℝ (fun i ↦ v i y) j)) x) :=
      Real.contDiffAt_sqrt (inner_self_ne_zero.mpr (gramSchmidt_ne_zero_coe j hli))
    simpa only [Function.comp_def, ← norm_eq_sqrt_real_inner] using
      hr.comp_contMDiffWithinAt (I := IP)
        (f := fun y : P ↦ inner ℝ (gramSchmidt ℝ (fun i ↦ v i y) j)
          (gramSchmidt ℝ (fun i ↦ v i y) j)) hh
  exact (hn.inv₀ (norm_ne_zero_iff.mpr (gramSchmidt_ne_zero_coe j hli))).smul_totalSpace hg

/-- Fiberwise normalized Gram–Schmidt preserves `C^n` regularity along an arbitrary base
map, assuming regularity and independence only through the requested index. -/
theorem ContMDiffAt.gramSchmidtNormed_bundle (j : ι)
    (hv : ∀ i ≤ j, ContMDiffAt IP (I.prod 𝓘(ℝ, F)) n
      (fun y ↦ TotalSpace.mk' F (b y) (v i y)) x)
    (hli : LinearIndepOn ℝ (fun i ↦ v i x) (Set.Iic j)) :
    ContMDiffAt IP (I.prod 𝓘(ℝ, F)) n
      (fun y ↦ TotalSpace.mk' F (b y) (gramSchmidtNormed ℝ (fun i ↦ v i y) j)) x :=
  ContMDiffWithinAt.gramSchmidtNormed_bundle j hv hli

/-- Fiberwise Gram–Schmidt preserves regularity on a set along a base map, using only
regular inputs through `j` and independence before `j` at each point of the set. -/
theorem ContMDiffOn.gramSchmidt_bundle (j : ι)
    (hv : ∀ i ≤ j, ContMDiffOn IP (I.prod 𝓘(ℝ, F)) n
      (fun y ↦ TotalSpace.mk' F (b y) (v i y)) s)
    (hli : ∀ x ∈ s, LinearIndepOn ℝ (fun i ↦ v i x) (Set.Iio j)) :
    ContMDiffOn IP (I.prod 𝓘(ℝ, F)) n
      (fun y ↦ TotalSpace.mk' F (b y) (gramSchmidt ℝ (fun i ↦ v i y) j)) s :=
  fun x hx ↦ ContMDiffWithinAt.gramSchmidt_bundle j (fun i hi ↦ hv i hi x hx) (hli x hx)

/-- Fiberwise Gram–Schmidt preserves global regularity along a base map, using only
regular inputs through `j` and independence before `j`. -/
theorem ContMDiff.gramSchmidt_bundle (j : ι)
    (hv : ∀ i ≤ j, ContMDiff IP (I.prod 𝓘(ℝ, F)) n
      (fun y ↦ TotalSpace.mk' F (b y) (v i y)))
    (hli : ∀ x, LinearIndepOn ℝ (fun i ↦ v i x) (Set.Iio j)) :
    ContMDiff IP (I.prod 𝓘(ℝ, F)) n
      (fun y ↦ TotalSpace.mk' F (b y) (gramSchmidt ℝ (fun i ↦ v i y) j)) :=
  fun x ↦ ContMDiffAt.gramSchmidt_bundle j (fun i hi ↦ hv i hi x) (hli x)

/-- Fiberwise normalized Gram–Schmidt preserves regularity on a set along a base map,
using only regularity and independence through `j`. -/
theorem ContMDiffOn.gramSchmidtNormed_bundle (j : ι)
    (hv : ∀ i ≤ j, ContMDiffOn IP (I.prod 𝓘(ℝ, F)) n
      (fun y ↦ TotalSpace.mk' F (b y) (v i y)) s)
    (hli : ∀ x ∈ s, LinearIndepOn ℝ (fun i ↦ v i x) (Set.Iic j)) :
    ContMDiffOn IP (I.prod 𝓘(ℝ, F)) n
      (fun y ↦ TotalSpace.mk' F (b y) (gramSchmidtNormed ℝ (fun i ↦ v i y) j)) s :=
  fun x hx ↦ ContMDiffWithinAt.gramSchmidtNormed_bundle j
    (fun i hi ↦ hv i hi x hx) (hli x hx)

/-- Fiberwise normalized Gram–Schmidt preserves global regularity along a base map,
using only regularity and independence through `j`. -/
theorem ContMDiff.gramSchmidtNormed_bundle (j : ι)
    (hv : ∀ i ≤ j, ContMDiff IP (I.prod 𝓘(ℝ, F)) n
      (fun y ↦ TotalSpace.mk' F (b y) (v i y)))
    (hli : ∀ x, LinearIndepOn ℝ (fun i ↦ v i x) (Set.Iic j)) :
    ContMDiff IP (I.prod 𝓘(ℝ, F)) n
      (fun y ↦ TotalSpace.mk' F (b y) (gramSchmidtNormed ℝ (fun i ↦ v i y) j)) :=
  fun x ↦ ContMDiffAt.gramSchmidtNormed_bundle j (fun i hi ↦ hv i hi x) (hli x)

end Along

open scoped Classical in
/-- The vectors of the Gram–Schmidt orthonormal basis `e.orthonormalBasis c` of the fibres over the
base set of a compatible local trivialization are `C^n` sections over that base set (extended by
`0` outside it, as for `Bundle.Trivialization.localFrame`). This is the smooth counterpart of
`Bundle.Trivialization.continuous_orthonormalBasis`. -/
theorem Bundle.Trivialization.contMDiffOn_orthonormalBasis [ContMDiffVectorBundle n F V I]
    [Fintype ι] (e : Trivialization F (TotalSpace.proj : TotalSpace F V → M))
    [MemTrivializationAtlas e] (c : Module.Basis ι ℝ F) (i : ι) :
    CMDiff[e.baseSet] n
      (T% fun y ↦ (if hy : y ∈ e.baseSet then e.orthonormalBasis c ⟨y, hy⟩ i else 0 : V y)) := by
  have hfr := e.isLocalFrameOn_localFrame_baseSet I n c
  have heq {y : M} (hy : y ∈ e.baseSet) :
      (if hy : y ∈ e.baseSet then e.orthonormalBasis c ⟨y, hy⟩ i else 0 : V y) =
        gramSchmidtNormed ℝ (fun j ↦ e.localFrame c j y) i := by
    rw [dite_eq_left_of_eq_true (eq_true hy), orthonormalBasis_apply]
    congr 1
    funext j
    rw [e.localFrame_apply_of_mem_baseSet c hy, basisAt, Module.Basis.map_apply,
      e.symmL_apply hy, e.linearEquivAt_symm_apply]
  intro x hx
  refine ((ContMDiffAt.gramSchmidtNormed_bundle i (fun j _ ↦ hfr.contMDiffAt e.open_baseSet hx j)
    ((hfr.linearIndependent hx).linearIndepOn _)).contMDiffWithinAt).congr (fun y hy ↦ ?_) ?_
  · exact congrArg (TotalSpace.mk' F y) (heq hy)
  · exact congrArg (TotalSpace.mk' F x) (heq hx)

variable [ContMDiffVectorBundle n F V I] [FiniteDimensional ℝ F] in
/-- Every point of a `C^n` Riemannian vector bundle with finite-dimensional model fibre `F` has an
open neighbourhood carrying a `C^n` local frame which is orthonormal at each of its points. -/
theorem TauCeti.exists_isLocalFrameOn_orthonormal (x₀ : M) :
    ∃ U : Set M, IsOpen U ∧ x₀ ∈ U ∧ ∃ u : Fin (Module.finrank ℝ F) → Π x : M, V x,
      IsLocalFrameOn I F n u U ∧ ∀ x ∈ U, Orthonormal ℝ (u · x) := by
  let e := trivializationAt F V x₀
  have hs := e.isLocalFrameOn_localFrame_baseSet I n (Module.finBasis ℝ F)
  refine ⟨e.baseSet, e.open_baseSet, FiberBundle.mem_baseSet_trivializationAt' x₀,
    fun i x ↦ gramSchmidtNormed ℝ (fun j ↦ e.localFrame (Module.finBasis ℝ F) j x) i,
    ⟨fun hx ↦ (gramSchmidtNormed_orthonormal (hs.linearIndependent hx)).linearIndependent,
      fun hx ↦ ?_, fun i x hx ↦ ?_⟩,
    fun x hx ↦ gramSchmidtNormed_orthonormal (hs.linearIndependent hx)⟩
  · rw [span_gramSchmidtNormed_range, span_gramSchmidt]
    exact hs.generating hx
  · exact (ContMDiffAt.gramSchmidtNormed_bundle i
      (fun j _ ↦ hs.contMDiffAt e.open_baseSet hx j)
      ((hs.linearIndependent hx).linearIndepOn _)).contMDiffWithinAt

section Differentiable

variable [IsContMDiffRiemannianBundle I 1 F V]

omit [IsContMDiffRiemannianBundle I n F V] in
/-- Fiberwise Gram–Schmidt is differentiable at every point where the input sections up to and
including the index are differentiable and the input vectors strictly before the index are linearly
independent. The input vector at the index itself may lie in their span. -/
theorem MDifferentiableAt.gramSchmidt_bundle (j : ι)
    (hv : ∀ i ≤ j, MDiffAt (T% (v i)) x)
    (hli : LinearIndepOn ℝ (fun i ↦ v i x) (Set.Iio j)) :
    MDiffAt (T% (fun y ↦ gramSchmidt ℝ (fun i ↦ v i y) j)) x := by
  classical
  induction j using WellFoundedLT.induction with
  | ind j ih =>
    have hg (i : ι) (hi : i < j) :=
      ih i hi (fun k hk ↦ hv k (hk.trans hi.le)) (hli.mono (Set.Iio_subset_Iio hi.le))
    have hc (i : ι) (hi : i < j) :
        MDiffAt (fun y ↦ inner ℝ (gramSchmidt ℝ (fun k ↦ v k y) i) (v j y) /
          inner ℝ (gramSchmidt ℝ (fun k ↦ v k y) i)
            (gramSchmidt ℝ (fun k ↦ v k y) i)) x :=
      ((hg i hi).inner_bundle (hv j le_rfl)).div ((hg i hi).inner_bundle (hg i hi))
        (inner_self_ne_zero.mpr (gramSchmidt_ne_zero_coe i
          (hli.mono (Set.Iic_subset_Iio.2 hi)).linearIndependent))
    have hformula : (fun y ↦ gramSchmidt ℝ (fun i ↦ v i y) j) =
        v j - ∑ i ∈ Finset.Iio j,
          (fun y ↦ inner ℝ (gramSchmidt ℝ (fun k ↦ v k y) i) (v j y) /
            inner ℝ (gramSchmidt ℝ (fun k ↦ v k y) i)
              (gramSchmidt ℝ (fun k ↦ v k y) i)) •
            (fun y ↦ gramSchmidt ℝ (fun k ↦ v k y) i) := by
      funext y
      simp only [Pi.sub_apply, Finset.sum_apply, real_inner_self_eq_norm_sq]
      exact eq_sub_of_add_eq (gramSchmidt_def'' ℝ (fun i ↦ v i y) j).symm
    have hs := mdifferentiableAt_sub_section (hv j le_rfl) (MDifferentiableAt.sum_section fun i hi ↦
      (hc i (Finset.mem_Iio.mp hi)).smul_section (hg i (Finset.mem_Iio.mp hi)))
    apply hs.congr_of_eventuallyEq
    apply Filter.Eventually.of_forall
    intro y
    apply congrArg (TotalSpace.mk' F y)
    simpa only [Pi.sub_apply, Finset.sum_apply] using congrFun hformula y

end Differentiable

end
