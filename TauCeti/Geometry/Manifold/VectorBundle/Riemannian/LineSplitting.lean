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

/-!
# Splitting a complex bundle into a trivial bundle and a line bundle

Over a compact boundaryless manifold of real dimension less than four, a smooth complex bundle `V`
of complex rank `n + 1` with a smooth Hermitian metric has `n` pointwise orthonormal smooth sections
(`Bundle.ContMDiffRiemannianMetric.exists_orthonormal_contMDiffSection_of_finrank_lt`): the
complement of the sections chosen so far is a smooth complex bundle of real rank at least four, so
it has a nowhere-zero smooth section
(`TauCeti.exists_contMDiffSection_forall_ne_zero_of_finrank_lt`), which is normalized and appended.
Their orthogonal complement `L`
(`Bundle.ContMDiffRiemannianMetric.orthogonalSpanFamily`) is a smooth complex line subbundle and
`V ≅ (B × ℂⁿ) ⊕ L` (`TauCeti.exists_trivialProdLineSubbundle_diffeomorph`), by the splitting
`Bundle.ContMDiffRiemannianMetric.trivialProdOrthogonalSpanFamilyDiffeomorph` of
`Riemannian/OrthogonalComplement.lean`. This is the splitting step of the proof of the Riemann–Roch
theorem for Cauchy–Riemann operators over a closed surface.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS (2012),
  proof of Theorem C.1.10.
* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer (2013), Lemma 10.32.
-/

public noncomputable section

open Bundle Module Set TauCeti
open scoped Manifold ContDiff InnerProductSpace Topology

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

namespace Bundle.ContMDiffRiemannianMetric

/-- **Orthonormal smooth sections.** Let `V` be a smooth Hermitian bundle of complex rank `k + r`
over a compact boundaryless manifold of real dimension less than `2 (r + 1)`. Then `V` has `k`
smooth sections that are orthonormal at every point. -/
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
      refine Complex.ofRealCLM.contMDiff.comp (f := fun x ↦ ‖u x‖⁻¹) fun x ↦ ?_
      have hd := hu.inner_bundle hu x
      have hne : Inner.inner ℝ (u x) (u x) ≠ 0 := inner_self_ne_zero.mpr (hu₀ x)
      refine (ContDiffAt.comp_contMDiffAt (f := fun y ↦ Inner.inner ℝ (u y) (u y))
        ((Real.contDiffAt_sqrt hne).inv (Real.sqrt_ne_zero'.mpr
        (lt_of_le_of_ne real_inner_self_nonneg hne.symm))) hd).congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun y ↦ ?_)
      simp only [Function.comp_apply, Pi.inv_apply, real_inner_self_eq_norm_sq,
        Real.sqrt_sq (norm_nonneg _)]
    let s' : Fin (k + 1) → ∀ x, V x := Matrix.vecCons (fun x ↦ c x • u x) s
    refine ⟨s', fun i ↦ ?_, fun x ↦ ?_⟩
    · induction i using Fin.cases with
      | zero => simpa [s'] using hc.smul_totalSpace hu
      | succ i => simpa [s'] using hs i
    · have hux : u x ∈ W x := (t x).2
      have horth (i : Fin k) : ⟪s i x, c x • u x⟫_ℂ = 0 := by
        rw [inner_smul_right, (g.mem_orthogonalSpanFamily_iff hI s).mp hux i, mul_zero]
      have hnorm : ‖c x • u x‖ = 1 := by
        rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_norm,
          inv_mul_cancel₀ (norm_ne_zero_iff.mpr (hu₀ x))]
      have hs' : (fun i ↦ s' i x) = Matrix.vecCons (c x • u x) fun i ↦ s i x := by
        ext i
        induction i using Fin.cases <;> simp [s']
      rw [hs']
      exact orthonormal_vecCons_iff.mpr ⟨hnorm, fun i ↦ inner_eq_zero_symm.mp (horth i), hon x⟩

end Bundle.ContMDiffRiemannianMetric

namespace TauCeti

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
  obtain ⟨s, hs, hon⟩ := g.exists_orthonormal_contMDiffSection_of_finrank_lt hI hn (r := 1)
    (by omega)
  have hL := g.hasLocalContMDiffSubbundleFrames_orthogonalSpanFamily hI s hs hon (r := 1)
    (by rw [hn, Fintype.card_fin])
  exact ⟨g, hI, s, hs, hon, hL, ⟨g.trivialProdOrthogonalSpanFamilyDiffeomorph hI s hs hL hon⟩⟩

end TauCeti
