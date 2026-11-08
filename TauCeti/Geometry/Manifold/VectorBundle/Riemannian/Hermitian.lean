/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Existence
public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Mean
public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Pullback
public import TauCeti.Geometry.Manifold.VectorBundle.Complexification
public import TauCeti.Geometry.Symplectic.Complex.InnerProductSpace

/-!
# Smooth Hermitian metrics on complex bundles over real manifolds

A real bundle metric becomes invariant under multiplication by `i` after averaging with its
pullback by `i`. The original real and complex scalar actions and fibre topology are retained.
The invariant metric gives the native complex inner product with that same real norm.

## References

* D. Huybrechts, *Complex Geometry: An Introduction*, Springer (2005), §2.6.
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed.,
  AMS (2012), Appendix C.
-/

public noncomputable section

open Bundle
open scoped Manifold ContDiff

namespace Bundle.ContMDiffRiemannianMetric

variable {X H B F : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [TopologicalSpace H] {IB : ModelWithCorners ℝ X H}
  [TopologicalSpace B] [ChartedSpace H B]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]
  {V : B → Type*}
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [∀ x, Module ℂ (V x)]
  [∀ x, IsScalarTower ℝ ℂ (V x)] [∀ x, TopologicalSpace (V x)]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [∀ x, ContinuousConstSMul ℂ (V x)]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℂ F V]
  {n : ℕ∞ω}

local instance : VectorBundle ℝ F V := VectorBundle.restrictScalars ℝ ℂ F V

/-- Average a real metric with its pullback by multiplication by `i`. -/
def hermitianAverage (g : ContMDiffRiemannianMetric IB n F V) :
    ContMDiffRiemannianMetric IB n F V :=
  TauCeti.meanRiemannianMetric (fun b : Bool ↦ if b then
    g.pullbackBundleEquiv (fun x ↦ Complex.smulIEquiv (V x))
      TauCeti.contMDiff_smulIEquiv_bundle else g)

/-- The averaged metric is the half-sum of the original metric and its `i`-translate. -/
@[simp]
theorem hermitianAverage_inner (g : ContMDiffRiemannianMetric IB n F V)
    (x : B) (v w : V x) :
    g.hermitianAverage.inner x v w =
      2⁻¹ * (g.inner x v w + g.inner x (Complex.I • v) (Complex.I • w)) := by
  simp [hermitianAverage, TauCeti.meanRiemannianMetric_inner, add_comm]

/-- Multiplication by `i` preserves the averaged real metric. -/
theorem hermitianAverage_inner_smul_I (g : ContMDiffRiemannianMetric IB n F V)
    (x : B) (v w : V x) :
    g.hermitianAverage.inner x (Complex.I • v) (Complex.I • w) =
      g.hermitianAverage.inner x v w := by
  simp only [hermitianAverage_inner, smul_smul, Complex.I_mul_I, neg_one_smul, map_neg,
    neg_apply, neg_neg]
  ring

/-- A real metric is unchanged by Hermitian averaging exactly when it is already `i`-invariant. -/
theorem hermitianAverage_eq_self_iff (g : ContMDiffRiemannianMetric IB n F V) :
    g.hermitianAverage = g ↔
      ∀ x (v w : V x), g.inner x (Complex.I • v) (Complex.I • w) = g.inner x v w := by
  constructor
  · intro h x v w
    rw [← h]
    exact g.hermitianAverage_inner_smul_I x v w
  · intro h
    ext x v w
    rw [hermitianAverage_inner, h]
    ring

/-- Hermitian averaging is idempotent. -/
@[simp]
theorem hermitianAverage_idempotent (g : ContMDiffRiemannianMetric IB n F V) :
    g.hermitianAverage.hermitianAverage = g.hermitianAverage :=
  g.hermitianAverage.hermitianAverage_eq_self_iff.mpr g.hermitianAverage_inner_smul_I

/-- The native complex inner product of an `i`-invariant real metric. Its norm and topology
are those of the original real metric, and its complex module is the caller's given module. -/
-- Typeclass parents must reduce to the caller's module when native Submodule operators are used.
@[expose, implicit_reducible]
def complexInnerProductSpace (g : ContMDiffRiemannianMetric IB n F V)
    (hI : ∀ x (v w : V x), g.inner x (Complex.I • v) (Complex.I • w) = g.inner x v w)
    (x : B) :
    letI : RiemannianBundle V := ⟨g.toRiemannianMetric⟩
    InnerProductSpace ℂ (V x) := by
  letI : RiemannianBundle V := ⟨g.toRiemannianMetric⟩
  let J := TauCeti.AlmostComplexStructure.ofComplexModule (V x)
  have hi (v w : V x) : Inner.inner ℝ v w = g.inner x v w := g.inner_eq x v w
  have hJ : ∀ v w : V x, @Inner.inner ℝ (V x) inferInstance (J v) (J w) =
      @Inner.inner ℝ (V x) inferInstance v w := by
    intro v w
    simpa only [J, TauCeti.AlmostComplexStructure.ofComplexModule_apply, hi] using hI x v w
  let k := J.complexInnerProductSpace (TauCeti.AlmostComplexStructure.norm_apply hJ)
  have hm : k.toNormedSpace.toModule = (inferInstance : Module ℂ (V x)) := by
    rw [TauCeti.AlmostComplexStructure.complexInnerProductSpace_toModule,
      TauCeti.AlmostComplexStructure.complexModule_ofComplexModule]
  let m : NormedSpace ℂ (V x) :=
    { toModule := inferInstance
      norm_smul_le := fun c v ↦ by
        have h := k.toNormedSpace.norm_smul_le c v
        rwa [hm] at h }
  refine
    { toNormedSpace := m
      toInner := k.toInner
      norm_sq_eq_re_inner := k.norm_sq_eq_re_inner
      conj_inner_symm := k.conj_inner_symm
      add_left := k.add_left
      smul_left := ?_ }
  intro v w c
  have h := k.smul_left v w c
  rwa [hm] at h

omit [∀ x, ContinuousConstSMul ℂ (V x)] in
/-- The Hermitian construction retains the caller's exact complex module structure. -/
@[simp]
theorem complexInnerProductSpace_toModule (g : ContMDiffRiemannianMetric IB n F V)
    (hI : ∀ x (v w : V x), g.inner x (Complex.I • v) (Complex.I • w) = g.inner x v w)
    (x : B) :
    letI : RiemannianBundle V := ⟨g.toRiemannianMetric⟩
    (g.complexInnerProductSpace hI x).toNormedSpace.toModule =
      (inferInstance : Module ℂ (V x)) := by
  rfl

omit [∀ x, ContinuousConstSMul ℂ (V x)] in
/-- The Hermitian pairing has real part the real metric and imaginary part its `i`-rotation. -/
@[simp]
theorem complexInnerProductSpace_inner (g : ContMDiffRiemannianMetric IB n F V)
    (hI : ∀ x (v w : V x), g.inner x (Complex.I • v) (Complex.I • w) = g.inner x v w)
    (x : B) (v w : V x) :
    letI : RiemannianBundle V := ⟨g.toRiemannianMetric⟩
    letI := g.complexInnerProductSpace hI x
    Inner.inner ℂ v w = (g.inner x v w : ℂ) + Complex.I * (g.inner x (Complex.I • v) w : ℂ) := by
  let : RiemannianBundle V := ⟨g.toRiemannianMetric⟩
  rw [TauCeti.AlmostComplexStructure.complexInnerProductSpace_inner,
    TauCeti.AlmostComplexStructure.ofComplexModule_apply, g.inner_eq, g.inner_eq]

variable {XM HM M : Type*} [NormedAddCommGroup XM] [NormedSpace ℝ XM]
  [TopologicalSpace HM] {IM : ModelWithCorners ℝ XM HM}
  [TopologicalSpace M] [ChartedSpace HM M]

omit [∀ x, ContinuousConstSMul ℂ (V x)] in
/-- Hermitian pairings of smooth bundle-valued maps with a common varying base are smooth. -/
theorem contMDiff_hermitianPairing (g : ContMDiffRiemannianMetric IB n F V)
    (hI : ∀ x (v w : V x), g.inner x (Complex.I • v) (Complex.I • w) = g.inner x v w)
    {b : M → B} {v w : ∀ m, V (b m)}
    (hv : ContMDiff IM (IB.prod 𝓘(ℝ, F)) n (fun m ↦ (⟨b m, v m⟩ : TotalSpace F V)))
    (hw : ContMDiff IM (IB.prod 𝓘(ℝ, F)) n (fun m ↦ (⟨b m, w m⟩ : TotalSpace F V))) :
    letI : RiemannianBundle V := ⟨g.toRiemannianMetric⟩
    letI : ∀ x, InnerProductSpace ℂ (V x) := g.complexInnerProductSpace hI
    ContMDiff IM 𝓘(ℝ, ℂ) n (fun m ↦ Inner.inner ℂ (v m) (w m)) := by
  let : RiemannianBundle V := ⟨g.toRiemannianMetric⟩
  let : ∀ x, InnerProductSpace ℂ (V x) := g.complexInnerProductSpace hI
  have hre := hv.inner_bundle hw
  have him := ((contMDiff_const (c := Complex.I)).smul_totalSpace hv).inner_bundle hw
  have hh := (Complex.ofRealCLM.contMDiff.comp hre).add
    (him.smul (contMDiff_const (I' := 𝓘(ℝ, ℂ)) (c := Complex.I)))
  apply hh.congr
  intro m
  rw [complexInnerProductSpace_inner]
  have hreal (x : B) (v w : V x) : Inner.inner ℝ v w = g.inner x v w := g.inner_eq x v w
  simp [hreal, Complex.real_smul, Pi.smul_def', mul_comm]

end Bundle.ContMDiffRiemannianMetric

namespace TauCeti

variable {X H B F : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [FiniteDimensional ℝ X] [TopologicalSpace H] {IB : ModelWithCorners ℝ X H}
  [TopologicalSpace B] [ChartedSpace H B] [T2Space B] [SigmaCompactSpace B]
  [IsManifold IB ∞ B]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]
  [FiniteDimensional ℂ F]
  {V : B → Type*}
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [∀ x, Module ℂ (V x)]
  [∀ x, IsScalarTower ℝ ℂ (V x)] [∀ x, TopologicalSpace (V x)]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [∀ x, ContinuousConstSMul ℂ (V x)]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℂ F V]

local instance : VectorBundle ℝ F V := VectorBundle.restrictScalars ℝ ℂ F V

/-- A finite-rank smooth complex bundle over a real σ-compact Hausdorff manifold admits a smooth
real metric invariant under multiplication by `i`, hence a compatible Hermitian metric. -/
theorem exists_contMDiffRiemannianMetric_inner_smul_I {n : ℕ∞}
    [ContMDiffVectorBundle n F V IB] :
    ∃ g : ContMDiffRiemannianMetric IB n F V,
      ∀ x (v w : V x), g.inner x (Complex.I • v) (Complex.I • w) = g.inner x v w := by
  let : FiniteDimensional ℝ F := Module.Finite.trans ℂ F
  obtain ⟨g⟩ := nonempty_contMDiffRiemannianMetric (IB := IB) (n := n) (F := F) (E := V)
  exact ⟨g.hermitianAverage, g.hermitianAverage_inner_smul_I⟩

end TauCeti
