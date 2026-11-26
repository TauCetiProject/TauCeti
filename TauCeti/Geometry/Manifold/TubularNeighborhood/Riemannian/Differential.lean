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

The differential formula is an instance of a general computation for a vector bundle `V → B`:
along the zero section, the differential of `p ↦ exp_{b p.proj} (L p.proj p.2)`, for a map
`b : B → N` and fibrewise linear maps `L x : V x → T_{b x} N`, sends `(u, v)` to `db u + L v`
(`TauCeti.Bundle.mfderiv_riemannianExp_fiberwise_zeroSection_apply`). Invertibility also uses
that the normal representatives complement the image of `df`.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, second edition, Theorem 6.24.
* M. W. Hirsch, *Differential Topology*, Chapter 4, Theorem 6.3.
-/

public noncomputable section

open Bundle Manifold Set
open scoped ContDiff Manifold

namespace TauCeti.Bundle

section Fiberwise

variable {E F W H G B N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E H} {K : ModelWithCorners ℝ W G}
  [TopologicalSpace B] [ChartedSpace H B]
  {V : B → Type*} [∀ x, AddCommMonoid (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  [TopologicalSpace N] [ChartedSpace G N] [IsManifold K ∞ N] [K.Boundaryless] [T2Space N]
  [RiemannianBundle (fun y : N ↦ TangentSpace K y)]
  [IsContMDiffRiemannianBundle K ∞ W (fun y : N ↦ TangentSpace K y)]

omit [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace B]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℝ F V] in
/-- The exponential of a fibrewise linear image of a vector bundle sends the zero section to the
base map. -/
theorem riemannianExp_fiberwise_zeroSection {b : B → N}
    (L : ∀ x, V x →L[ℝ] TangentSpace K (b x)) (x : B) :
    Manifold.riemannianExp K N (b (zeroSection F V x).proj)
      (L (zeroSection F V x).proj (zeroSection F V x).snd) = b x := by
  -- The fibre value of the zero section is the zero of the fibre over its projection, which is
  -- only definitionally the fibre over `x`; restate it over `x` so that `map_zero` applies.
  change Manifold.riemannianExp K N (b x) (L x 0) = b x
  rw [map_zero, Manifold.riemannianExp_zero]

/-- Under the splitting of the tangent space along the zero section, the differential of
`p ↦ exp_{b p.proj} (L p.proj p.2)` sends `(u, v)` to `db u + L v`. -/
theorem mfderiv_riemannianExp_fiberwise_zeroSection_apply {b : B → N}
    (L : ∀ x, V x →L[ℝ] TangentSpace K (b x)) (x : B)
    (hd : MDifferentiableAt (I.prod 𝓘(ℝ, F)) K
      (fun p : TotalSpace F V ↦ Manifold.riemannianExp K N (b p.proj) (L p.proj p.snd))
      (zeroSection F V x))
    (u : TangentSpace I x) (v : V x) :
    mfderiv (I.prod 𝓘(ℝ, F)) K
        (fun p : TotalSpace F V ↦ Manifold.riemannianExp K N (b p.proj) (L p.proj p.snd))
        (zeroSection F V x) ((zeroSectionTangentEquiv (I := I) x).symm (u, v)) =
      mfderiv I K b x u + L x v := by
  rw [zeroSectionTangentEquiv_symm_eq, map_add]
  congr 1
  · have h := mfderiv_comp_apply x hd (mdifferentiableAt_zeroSection ℝ _) u
    rw [show (fun p : TotalSpace F V ↦ Manifold.riemannianExp K N (b p.proj) (L p.proj p.snd)) ∘
      zeroSection F V = b from funext (riemannianExp_fiberwise_zeroSection L)] at h
    exact h.symm
  · rw [zeroSectionTangentEquiv_symm_inr]
    -- Along the scalar line through `v`, the map is the exponential of the ray through `L x v`.
    have hl := (TotalSpace.hasMFDerivAt_smul_curve (IB := I) (⟨x, v⟩ : TotalSpace F V)
      (hasDerivAt_id' (0 : ℝ))).mdifferentiableAt
    have h := mfderiv_comp_apply_of_eq (0 : ℝ) hd hl (by simp [zeroSection]) (1 : ℝ)
    have hfun : (fun p : TotalSpace F V ↦ Manifold.riemannianExp K N (b p.proj) (L p.proj p.snd)) ∘
        (fun t : ℝ ↦ (⟨x, t • v⟩ : TotalSpace F V)) =
        Manifold.riemannianExp K N (b x) ∘ (fun t : ℝ ↦ t • L x v) := by
      funext t
      simp only [Function.comp_apply, map_smul]
    rw [hfun] at h
    have hexp₀ := Manifold.hasMFDerivAt_riemannianExp_zero (I := K) (b x)
    have hvec : HasMFDerivAt 𝓘(ℝ) 𝓘(ℝ, TangentSpace K (b x)) (fun t : ℝ ↦ t • L x v) 0
        (ContinuousLinearMap.toSpanSingleton ℝ (L x v)) :=
      (ContinuousLinearMap.toSpanSingleton ℝ (L x v)).hasMFDerivAt
    have hc := mfderiv_comp_apply_of_eq (0 : ℝ) hexp₀.mdifferentiableAt
      hvec.mdifferentiableAt (by simp) (1 : ℝ)
    -- The differential of `exp` at `0` is stated on the tangent space of the tangent space at
    -- `b x`, which is only definitionally that tangent space; `erw` sees through this.
    erw [Manifold.mfderiv_riemannianExp_apply_zero (I := K) (b x), hvec.mfderiv] at hc
    exact h.symm.trans (hc.trans (ContinuousLinearMap.toSpanSingleton_apply_one ℝ (L x v)))

end Fiberwise

end TauCeti.Bundle

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
    (x : M) (u : TangentSpace I x) (v : f.isImmersion.NormalSpace x hn) :
    haveI : IsManifold I 1 M := .of_le (n := 1 + 1) le_add_self
    letI := f.normalSpaceFiberBundle hn hdim
    letI := f.normalSpaceVectorBundle hn hdim
    mfderiv (I.prod 𝓘(ℝ, P)) J (f.normalExp (P := P) hn)
        (zeroSection P (fun x ↦ f.isImmersion.NormalSpace x hn) x)
        ((Bundle.zeroSectionTangentEquiv (I := I) x).symm (u, v)) =
      mfderiv I J f x u + f.normalRepresentative x hn v := by
  have : IsManifold I 1 M := .of_le (n := 1 + 1) le_add_self
  have : IsManifold J (1 + 1) N := .of_le (n := ∞) (by norm_cast)
  let := f.normalSpaceFiberBundle hn hdim
  let := f.normalSpaceVectorBundle hn hdim
  let := f.normalSpaceContMDiffVectorBundle (m := 1) hn h2 hdim
  have he : MDifferentiableAt (I.prod 𝓘(ℝ, P)) J (f.normalExp (P := P) hn)
      (zeroSection P (fun x ↦ f.isImmersion.NormalSpace x hn) x) :=
    ((f.contMDiffOn_normalExp (m := 1) hn h2 hdim).contMDiffAt
      ((f.isOpen_normalExpDomain hn hdim).mem_nhds
        (f.zeroSection_mem_normalExpDomain hn x))).mdifferentiableAt one_ne_zero
  rw [show f.normalExp (P := P) hn = fun p ↦
    Manifold.riemannianExp J N (f p.proj) (f.normalRepresentative p.proj hn p.snd) from
      funext (f.normalExp_apply hn)] at he ⊢
  exact Bundle.mfderiv_riemannianExp_fiberwise_zeroSection_apply
    (fun x ↦ f.normalRepresentative x hn) x he u v

/-- The total differential of the normal exponential at every zero normal vector is
invertible. This does not require compactness or a global normal framing. -/
theorem isInvertible_mfderiv_normalExp_zeroSection
    (f : SmoothEmbedding I J n M N) (hn : n ≠ 0) (h2 : 1 + 1 ≤ n)
    (hdim : Module.finrank ℝ P = Module.finrank ℝ V - Module.finrank ℝ E) (x : M) :
    haveI : IsManifold I 1 M := .of_le (n := 1 + 1) le_add_self
    letI := f.normalSpaceFiberBundle hn hdim
    (mfderiv (I.prod 𝓘(ℝ, P)) J (f.normalExp (P := P) hn)
      (zeroSection P (fun x ↦ f.isImmersion.NormalSpace x hn) x)).IsInvertible := by
  have : IsManifold I 1 M := .of_le (n := 1 + 1) le_add_self
  let := f.normalSpaceFiberBundle hn hdim
  let := f.normalSpaceVectorBundle hn hdim
  -- The value at zero is `f x`; use that tangent-space type for the linear algebra below.
  let D : TangentSpace (I.prod 𝓘(ℝ, P)) (zeroSection P (fun x ↦ f.isImmersion.NormalSpace x hn) x)
      →L[ℝ] TangentSpace J (f x) :=
    mfderiv (I.prod 𝓘(ℝ, P)) J (f.normalExp (P := P) hn)
      (zeroSection P (fun x ↦ f.isImmersion.NormalSpace x hn) x)
  let e := Bundle.zeroSectionTangentEquiv (I := I) (F := P)
      (V := fun x ↦ f.isImmersion.NormalSpace x hn) x
  have hD (u : TangentSpace I x) (v : f.isImmersion.NormalSpace x hn) :
      D (e.symm (u, v)) = mfderiv I J f x u + f.normalRepresentative x hn v :=
    f.mfderiv_normalExp_zeroSection_apply hn h2 hdim x u v
  have hinj : Function.Injective D := by
    refine (injective_iff_map_eq_zero D).2 fun w hw ↦ ?_
    obtain ⟨⟨u, v⟩, rfl⟩ := e.symm.surjective w
    have hv := congrArg (f.isImmersion.normalClass x hn) hw
    rw [hD, map_add, Manifold.IsImmersion.normalClass_mfderiv, normalClass_normalRepresentative,
      zero_add, map_zero] at hv
    subst v
    rw [hD, map_zero, add_zero] at hw
    have hu : u = 0 := by
      apply f.isImmersion.mfderiv_injective hn x
      simpa using hw
    simp [hu]
  have hsurj : Function.Surjective D := by
    intro w
    have ht : w - f.normalRepresentative x hn
        (f.isImmersion.normalClass x hn w) ∈ f.isImmersion.tangentRange x hn :=
      (f.isImmersion.normalClass_eq_zero_iff x hn _).mp (by simp)
    obtain ⟨u, hu⟩ := ht
    refine ⟨e.symm (u, f.isImmersion.normalClass x hn w), ?_⟩
    rw [hD]
    exact
        (congrArg
            (fun z ↦ z + f.normalRepresentative x hn (f.isImmersion.normalClass x hn w)) hu).trans
      (sub_add_cancel _ _)
  exact ⟨(LinearEquiv.ofBijective D.toLinearMap ⟨hinj, hsurj⟩).toContinuousLinearEquiv, rfl⟩

end TauCeti.SmoothEmbedding
