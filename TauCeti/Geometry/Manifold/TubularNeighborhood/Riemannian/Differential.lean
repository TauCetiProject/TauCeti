/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.TubularNeighborhood.Riemannian.Regularity
public import TauCeti.Geometry.Manifold.VectorBundle.ZeroSection
import TauCeti.Geometry.Manifold.VectorBundle.Scalar

/-!
# The differential of the normal exponential at zero

Under the canonical splitting of the tangent space along the zero section of the intrinsic
normal bundle, the differential of the normal exponential sends `(u, v)` to `df u + v`, where
the normal class `v` is read as its orthogonal representative. The total differential is
therefore invertible at every zero normal vector. These statements supply the linear input
to the inverse function theorem, without asserting injectivity away from the zero section.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, second edition, Theorem 6.24.
* M. W. Hirsch, *Differential Topology*, Chapter 4, Theorem 6.3.
-/

public noncomputable section

open Bundle Manifold Set
open scoped ContDiff Manifold

namespace TauCeti.SmoothEmbedding

variable {E V P H G M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ V G}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (1 + 1) M]
  [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N]
  [J.Boundaryless] [T2Space N] {n : ℕ∞ω}
  [RiemannianBundle (fun y : N ↦ TangentSpace J y)]
  [IsContMDiffRiemannianBundle J ∞ V (fun y : N ↦ TangentSpace J y)]

/-- The total differential of the normal exponential at zero is the sum of the embedded
tangent vector and the orthogonal representative of the normal class. -/
theorem mfderiv_normalExp_zeroSection_apply
    (f : SmoothEmbedding I J n M N) (hn : n ≠ 0) (h2 : 1 + 1 ≤ n)
    (hdim : Module.finrank ℝ P = Module.finrank ℝ V - Module.finrank ℝ E)
    (x : M) (u : TangentSpace I x) (v : f.NormalSpace x hn) :
    haveI : IsManifold I 1 M := .of_le (n := 1 + 1) le_add_self
    letI := f.normalSpaceFiberBundle hn hdim
    letI := f.normalSpaceVectorBundle hn hdim
    mfderiv (I.prod 𝓘(ℝ, P)) J (f.normalExp (P := P) hn)
        (zeroSection P (fun x ↦ f.NormalSpace x hn) x)
        ((Bundle.zeroSectionTangentEquiv (I := I) x).symm (u, v)) =
      mfderiv I J f x u + f.normalRepresentative x hn v := by
  have : IsManifold I 1 M := .of_le (n := 1 + 1) le_add_self
  have : IsManifold J (1 + 1) N := .of_le (n := ∞) (by norm_cast)
  let := f.normalSpaceFiberBundle hn hdim
  let := f.normalSpaceVectorBundle hn hdim
  let := f.normalSpaceContMDiffVectorBundle (m := 1) hn h2 hdim
  have he : MDifferentiableAt (I.prod 𝓘(ℝ, P)) J (f.normalExp (P := P) hn)
      (zeroSection P (fun x ↦ f.NormalSpace x hn) x) :=
    ((f.contMDiffOn_normalExp (m := 1) hn h2 hdim).contMDiffAt
      ((f.isOpen_normalExpDomain hn hdim).mem_nhds
        (f.zeroSection_mem_normalExpDomain hn x))).mdifferentiableAt one_ne_zero
  rw [Bundle.zeroSectionTangentEquiv_symm_eq, map_add]
  congr 1
  · have h := mfderiv_comp_apply x he (mdifferentiableAt_zeroSection ℝ _) u
    have hfun : f.normalExp (P := P) hn ∘ zeroSection P (fun x ↦ f.NormalSpace x hn) = f :=
      funext (f.normalExp_zeroSection hn)
    rw [hfun] at h
    exact h.symm
  · rw [Bundle.zeroSectionTangentEquiv_symm_inr]
    let line : ℝ → TotalSpace P (fun x ↦ f.NormalSpace x hn) := fun t ↦ ⟨x, t • v⟩
    have hl : ContMDiff 𝓘(ℝ) (I.prod 𝓘(ℝ, P)) 1 line :=
      contMDiff_id.smul_totalSpace (contMDiff_const (c := (⟨x, v⟩ :
        TotalSpace P (fun x ↦ f.NormalSpace x hn))))
    have h := mfderiv_comp_apply_of_eq (0 : ℝ) he
      (hl.mdifferentiableAt one_ne_zero) (by simp [line, zeroSection]) (1 : ℝ)
    have hfun : f.normalExp (P := P) hn ∘ line =
        Manifold.riemannianExp J N (f x) ∘ (fun t : ℝ ↦ t • f.normalRepresentative x hn v) := by
      funext t
      simp only [Function.comp_apply, line, normalExp_apply, map_smul]
    rw [hfun] at h
    have hexp₀ := Manifold.hasMFDerivAt_riemannianExp_zero (I := J) (f x)
    have hvec : HasMFDerivAt 𝓘(ℝ) 𝓘(ℝ, TangentSpace J (f x))
        (fun t : ℝ ↦ t • f.normalRepresentative x hn v) 0
        (ContinuousLinearMap.toSpanSingleton ℝ (f.normalRepresentative x hn v)) :=
      (ContinuousLinearMap.toSpanSingleton ℝ (f.normalRepresentative x hn v)).hasMFDerivAt
    have hc := mfderiv_comp_apply_of_eq (0 : ℝ) hexp₀.mdifferentiableAt
      hvec.mdifferentiableAt (by simp) (1 : ℝ)
    erw [Manifold.mfderiv_riemannianExp_apply_zero (I := J) (f x), hvec.mfderiv] at hc
    have hone := ContinuousLinearMap.toSpanSingleton_apply_one (M₁ := TangentSpace J (f x))
      ℝ (f.normalRepresentative x hn v)
    exact h.symm.trans (hc.trans hone)

/-- The total differential of the normal exponential at every zero normal vector is
invertible. This does not require compactness or a global normal framing. -/
theorem isInvertible_mfderiv_normalExp_zeroSection
    (f : SmoothEmbedding I J n M N) (hn : n ≠ 0) (h2 : 1 + 1 ≤ n)
    (hdim : Module.finrank ℝ P = Module.finrank ℝ V - Module.finrank ℝ E) (x : M) :
    haveI : IsManifold I 1 M := .of_le (n := 1 + 1) le_add_self
    letI := f.normalSpaceFiberBundle hn hdim
    (mfderiv (I.prod 𝓘(ℝ, P)) J (f.normalExp (P := P) hn)
      (zeroSection P (fun x ↦ f.NormalSpace x hn) x)).IsInvertible := by
  have : IsManifold I 1 M := .of_le (n := 1 + 1) le_add_self
  let := f.normalSpaceFiberBundle hn hdim
  let := f.normalSpaceVectorBundle hn hdim
  -- The value at zero is `f x`; use that tangent-space type for the linear algebra below.
  let D : TangentSpace (I.prod 𝓘(ℝ, P)) (zeroSection P (fun x ↦ f.NormalSpace x hn) x)
      →L[ℝ] TangentSpace J (f x) :=
    mfderiv (I.prod 𝓘(ℝ, P)) J (f.normalExp (P := P) hn)
      (zeroSection P (fun x ↦ f.NormalSpace x hn) x)
  let e := Bundle.zeroSectionTangentEquiv (I := I) (F := P) (V := fun x ↦ f.NormalSpace x hn) x
  have hD (u : TangentSpace I x) (v : f.NormalSpace x hn) :
      D (e.symm (u, v)) = mfderiv I J f x u + f.normalRepresentative x hn v :=
    f.mfderiv_normalExp_zeroSection_apply hn h2 hdim x u v
  have hinj : Function.Injective D := by
    refine (injective_iff_map_eq_zero D).2 fun w hw ↦ ?_
    obtain ⟨⟨u, v⟩, rfl⟩ := e.symm.surjective w
    have hv := congrArg (f.normalClass x hn) hw
    rw [hD, map_add, normalClass_mfderiv, normalClass_normalRepresentative,
      zero_add, map_zero] at hv
    subst v
    rw [hD, map_zero, add_zero] at hw
    have hu : u = 0 := by
      apply f.isImmersion.mfderiv_injective hn x
      simpa using hw
    simp [hu]
  have hsurj : Function.Surjective D := by
    intro w
    have ht : w - f.normalRepresentative x hn (f.normalClass x hn w) ∈ f.tangentRange x hn :=
      (f.normalClass_eq_zero_iff x hn _).mp (by simp)
    obtain ⟨u, hu⟩ := ht
    refine ⟨e.symm (u, f.normalClass x hn w), ?_⟩
    rw [hD]
    exact (congrArg (fun z ↦ z + f.normalRepresentative x hn (f.normalClass x hn w)) hu).trans
      (sub_add_cancel _ _)
  exact ⟨(LinearEquiv.ofBijective D.toLinearMap ⟨hinj, hsurj⟩).toContinuousLinearEquiv, rfl⟩

end TauCeti.SmoothEmbedding
