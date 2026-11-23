/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
public import TauCeti.Analysis.MvPolynomial.Sphere
public import TauCeti.Geometry.Manifold.Riemannian.Sphere.Laplacian
public import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Volume
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension
import TauCeti.Analysis.MvPolynomial.Jacobian
import TauCeti.Analysis.MvPolynomial.Laplacian
import TauCeti.Geometry.Manifold.Riemannian.DivergenceTheorem
import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Support

/-!
# Spherical harmonics as eigenfunctions of the round Laplace–Beltrami operator

This file connects the algebraic space `MvPolynomial.harmonicSubmodule σ ℝ d` of degree-`d`
harmonic homogeneous polynomials and its continuous sphere restriction
`MvPolynomial.harmonicSphereRestriction` to the Riemannian geometry and `L²` spectral theory of the
unit round sphere `Sᵐ ⊂ EuclideanSpace ℝ σ` (`dim = m + 1`), with the sign convention
`Δ_{Sᵐ} = div ∘ grad`.

1. **Smoothness and eigenvalue equation.** Every restricted harmonic homogeneous polynomial of
   degree `d` is analytic on `Sᵐ` and satisfies
   `Δ_{Sᵐ} (harmonicSphereRestriction σ d p) = -d (d + m - 1) (harmonicSphereRestriction σ d p)`
   for every `m ≥ 0` (`TauCeti.laplaceBeltrami_harmonicSphereRestriction`), obtained from Euler's
   homogeneity reduction `TauCeti.laplaceBeltrami_comp_coe_sphere_of_smul` and
   `MvPolynomial.laplacian_eval_euclidean`.
2. **Orthogonality.** For `m ≥ 1`, the sequence `d ↦ d (d + m - 1)` is strictly increasing
   (`TauCeti.strictMono_natCast_mul_add_sub_one`), so Green's second identity for
   `riemannianVolume` forces spherical harmonics of distinct degrees (and, more generally, any `C²`
   eigenfunction with `Δ_{Sᵐ} g = -λ g` and `λ ≠ d (d + m - 1)`) to be `L²`-orthogonal to
   degree-`d` spherical harmonics (`TauCeti.integral_harmonicSphereRestriction_mul_eq_zero`, and
   `TauCeti.inner_toLp_harmonicSphereRestriction_eq_zero` over any `[RCLike 𝕜]`).
3. **Complete `C²` eigenspace classification (`m ≥ 1`).** Combining `L²` completeness of spherical
   harmonics (`TauCeti.eq_zero_of_forall_inner_toLp_harmonicSphereRestriction_eq_zero`) with
   orthogonal projection onto the finite-dimensional degree-`d` harmonic subspace in `L²(Sᵐ, ℝ)`
   identifies the full `C²` eigenspace of `-d (d + m - 1)` with the range of
   `harmonicSphereRestriction σ d`
   (`TauCeti.laplaceBeltrami_eq_neg_mul_iff_exists_harmonicSphereRestriction`), and every nonzero
   `C²` solution of `Δ_{Sᵐ} f = -λ f` has `λ = d (d + m - 1)` and comes from a degree-`d` harmonic
   homogeneous polynomial (`TauCeti.eq_harmonicSphereRestriction_of_laplaceBeltrami_eq_neg_mul`).
   The hypothesis `1 ≤ m` is sharp: on `S⁰ = {±1}` the Laplace–Beltrami operator vanishes
   identically while `f(1) = 1, f(-1) = 2` is neither constant (`d = 0`) nor odd (`d = 1`).

## Main results

* `MvPolynomial.contMDiff_sphereEval`, `TauCeti.contMDiff_harmonicSphereRestriction`:
  polynomial restrictions and spherical harmonics are `C^k` (`k : ℕ∞ω`) on `Sᵐ`.
* `TauCeti.laplaceBeltrami_harmonicSphereRestriction`: degree-`d` spherical harmonics satisfy
  `Δ_{Sᵐ} f = -d (d + m - 1) f`.
* `TauCeti.integral_harmonicSphereRestriction_mul_eq_zero`,
  `TauCeti.inner_toLp_harmonicSphereRestriction_eq_zero`: orthogonality of distinct degrees
  (`m ≥ 1`, over `ℝ` and any `[RCLike 𝕜]`).
* `TauCeti.laplaceBeltrami_eq_neg_mul_iff_exists_harmonicSphereRestriction`,
  `TauCeti.eq_harmonicSphereRestriction_of_laplaceBeltrami_eq_neg_mul`: complete `C²` eigenspace
  identification on `Sᵐ` (`m ≥ 1`).

## References

* M. E. Taylor, *Introduction to Lie Groups*, §8.2, Proposition 8.2.1 (spherical harmonics and the
  spectrum of the round Laplacian).
* S. Axler, P. Bourdon and W. Ramey, *Harmonic Function Theory*, 2nd ed., Springer (2001),
  Chapter 5 (spherical harmonics and `L²` decomposition on the unit sphere).
* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018), Chapters 2
  and 8 (round metric, Riemannian volume, and Green's identities).
-/

public section

open Laplacian MeasureTheory Metric Module Set Topology
open scoped ContDiff ENNReal InnerProductSpace Manifold

noncomputable section

namespace MvPolynomial

/-- Restricting a polynomial over a normed commutative `ℝ`-algebra to the unit round sphere gives a
`C^k` map for every `k : ℕ∞ω` (including `ω` and `∞`). -/
theorem contMDiff_sphereEval {σ R : Type*} [Fintype σ] {m : ℕ}
    [Fact (finrank ℝ (EuclideanSpace ℝ σ) = m + 1)] [NormedCommRing R] [NormedAlgebra ℝ R]
    {k : ℕ∞ω} (p : MvPolynomial σ R) :
    ContMDiff (𝓡 m) 𝓘(ℝ, R) k (sphereEval p) := by
  have heq : ⇑(sphereEval p) =
      (fun x : EuclideanSpace ℝ σ ↦ eval (fun i ↦ algebraMap ℝ R (x i)) p) ∘ Subtype.val :=
    funext fun x ↦ sphereEval_apply p x
  rw [heq]
  exact (contDiff_eval_euclidean_algebraMap p).contMDiff.comp contMDiff_coe_sphere

end MvPolynomial

namespace TauCeti

/-- Every spherical harmonic in the image of `MvPolynomial.harmonicSphereRestriction` is `C^k` on
the round sphere for every `k : ℕ∞ω` (in particular analytic and `C^∞`). -/
theorem contMDiff_harmonicSphereRestriction {σ R : Type*} [Fintype σ] {m : ℕ}
    [Fact (finrank ℝ (EuclideanSpace ℝ σ) = m + 1)] [NormedCommRing R] [NormedAlgebra ℝ R]
    {k : ℕ∞ω} (d : ℕ) (p : MvPolynomial.harmonicSubmodule σ R d) :
    ContMDiff (𝓡 m) 𝓘(ℝ, R) k (MvPolynomial.harmonicSphereRestriction σ d p) := by
  rw [MvPolynomial.harmonicSphereRestriction_coe]
  exact MvPolynomial.contMDiff_sphereEval (p : MvPolynomial σ R)

section Eigenvalue

variable {σ : Type*} [Fintype σ] {m : ℕ} [Fact (finrank ℝ (EuclideanSpace ℝ σ) = m + 1)]

/-- **Spherical harmonics are round Laplace–Beltrami eigenfunctions.** Every real harmonic
homogeneous polynomial `p` of degree `d` restricts on `Sᵐ` to an eigenfunction of
`Manifold.laplaceBeltrami (𝓡 m)` with eigenvalue `-d (d + m - 1)` (`Δ_{Sᵐ} f = -d (d + m - 1) f`),
valid for every `m : ℕ` and `d : ℕ`. -/
theorem laplaceBeltrami_harmonicSphereRestriction (d : ℕ)
    (p : MvPolynomial.harmonicSubmodule σ ℝ d) (x : sphere (0 : EuclideanSpace ℝ σ) 1) :
    Manifold.laplaceBeltrami (𝓡 m) (MvPolynomial.harmonicSphereRestriction σ d p) x =
      -(d : ℝ) * ((d : ℝ) + m - 1) * MvPolynomial.harmonicSphereRestriction σ d p x := by
  obtain ⟨hp_hom, hp_lap⟩ := MvPolynomial.mem_harmonicSubmodule_iff.1 p.property
  let F : EuclideanSpace ℝ σ → ℝ := fun y ↦ MvPolynomial.eval y (p : MvPolynomial σ ℝ)
  have hF : ContDiffAt ℝ 2 F x := by
    simpa only [F, Algebra.algebraMap_self, RingHom.id_apply] using
      (MvPolynomial.contDiff_eval_euclidean_algebraMap (R := ℝ) (k := 2) p.val).contDiffAt
        (x := (x : EuclideanSpace ℝ σ))
  have hrestr : ⇑(MvPolynomial.harmonicSphereRestriction σ d p) = F ∘ Subtype.val := by
    funext y
    simp only [MvPolynomial.harmonicSphereRestriction_coe, MvPolynomial.sphereEval_apply,
      Algebra.algebraMap_self, RingHom.id_apply, Function.comp_apply, F]
  have hsmul : (fun t : ℝ ↦ F (t • (x : EuclideanSpace ℝ σ))) =ᶠ[𝓝 (1 : ℝ)]
      fun t ↦ t ^ (d : ℝ) * F x :=
    Filter.Eventually.of_forall fun t ↦ by
      dsimp only
      rw [Real.rpow_natCast]
      exact hp_hom.eval_smul t (x : EuclideanSpace ℝ σ)
  have hΔ : Δ F x = 0 := by
    rw [congrFun (MvPolynomial.laplacian_eval_euclidean p.val) x, hp_lap, map_zero]
  rw [hrestr, laplaceBeltrami_comp_coe_sphere_of_smul hF hsmul, hΔ]
  simp only [Function.comp_apply, F]
  ring

/-- For `1 ≤ m`, the eigenvalues `d ↦ d (d + m - 1)` of `-Δ_{Sᵐ}` are strictly increasing in the
degree `d : ℕ`. -/
theorem strictMono_natCast_mul_add_sub_one {m : ℕ} (hm : 1 ≤ m) :
    StrictMono fun d : ℕ ↦ (d : ℝ) * ((d : ℝ) + m - 1) := by
  intro d₁ d₂ hd
  have hd_lt : (d₁ : ℝ) < d₂ := Nat.cast_lt.2 hd
  have hm_ge : (1 : ℝ) ≤ m := Nat.one_le_cast.2 hm
  nlinarith [hd_lt, hm_ge, Nat.cast_nonneg (α := ℝ) d₁]

/-- Any `C²` function `g` on `Sᵐ` satisfying `Δ_{Sᵐ} g = -λ g` with `λ ≠ d (d + m - 1)` is
`L²`-orthogonal (with respect to `riemannianVolume`) to every degree-`d` spherical harmonic. -/
theorem integral_harmonicSphereRestriction_mul_eq_zero_of_laplaceBeltrami_eq_neg_mul
    {g : sphere (0 : EuclideanSpace ℝ σ) 1 → ℝ} (hg : ContMDiff (𝓡 m) 𝓘(ℝ, ℝ) 2 g) {lam : ℝ}
    (heig : ∀ x, Manifold.laplaceBeltrami (𝓡 m) g x = -lam * g x) {d : ℕ}
    (hlam : lam ≠ (d : ℝ) * ((d : ℝ) + m - 1))
    (p : MvPolynomial.harmonicSubmodule σ ℝ d) :
    ∫ x, MvPolynomial.harmonicSphereRestriction σ d p x * g x
      ∂riemannianVolume (𝓡 m) (sphere (0 : EuclideanSpace ℝ σ) 1) = 0 := by
  have : IsManifold (𝓡 m) ∞ (sphere (0 : EuclideanSpace ℝ σ) 1) := IsManifold.of_le le_top
  exact Manifold.integral_mul_eq_zero_of_laplaceBeltrami_eq_neg_mul
    (contMDiff_harmonicSphereRestriction d p) (HasCompactSupport.of_compactSpace _) hg
    (fun x ↦ by rw [laplaceBeltrami_harmonicSphereRestriction]; ring) heig hlam.symm

/-- Spherical harmonics of distinct degrees on `Sᵐ` (`m ≥ 1`) are orthogonal with respect to the
round `riemannianVolume`. -/
theorem integral_harmonicSphereRestriction_mul_eq_zero (hm : 1 ≤ m) {d₁ d₂ : ℕ} (hd : d₁ ≠ d₂)
    (p₁ : MvPolynomial.harmonicSubmodule σ ℝ d₁) (p₂ : MvPolynomial.harmonicSubmodule σ ℝ d₂) :
    ∫ x, MvPolynomial.harmonicSphereRestriction σ d₁ p₁ x *
        MvPolynomial.harmonicSphereRestriction σ d₂ p₂ x
      ∂riemannianVolume (𝓡 m) (sphere (0 : EuclideanSpace ℝ σ) 1) = 0 :=
  integral_harmonicSphereRestriction_mul_eq_zero_of_laplaceBeltrami_eq_neg_mul
    (contMDiff_harmonicSphereRestriction d₂ p₂)
    (fun x ↦ by rw [laplaceBeltrami_harmonicSphereRestriction]; ring)
    ((strictMono_natCast_mul_add_sub_one hm).injective.ne hd.symm) p₁

/-- In `L²(Sᵐ, 𝕜)` with the round Riemannian volume (`m ≥ 1`, `[RCLike 𝕜]`), spherical harmonics of
distinct degrees are orthogonal. -/
theorem inner_toLp_harmonicSphereRestriction_eq_zero {𝕜 : Type*} [RCLike 𝕜] (hm : 1 ≤ m)
    {d₁ d₂ : ℕ} (hd : d₁ ≠ d₂) (p₁ : MvPolynomial.harmonicSubmodule σ 𝕜 d₁)
    (p₂ : MvPolynomial.harmonicSubmodule σ 𝕜 d₂) :
    ⟪ContinuousMap.toLp (E := 𝕜) 2 (riemannianVolume (𝓡 m) (sphere (0 : EuclideanSpace ℝ σ) 1)) 𝕜
        (MvPolynomial.harmonicSphereRestriction σ d₁ p₁),
      ContinuousMap.toLp (E := 𝕜) 2 (riemannianVolume (𝓡 m) (sphere (0 : EuclideanSpace ℝ σ) 1)) 𝕜
        (MvPolynomial.harmonicSphereRestriction σ d₂ p₂)⟫_𝕜 = 0 := by
  have : IsManifold (𝓡 m) 1 (sphere (0 : EuclideanSpace ℝ σ) 1) := IsManifold.of_le le_top
  let μ := riemannianVolume (𝓡 m) (sphere (0 : EuclideanSpace ℝ σ) 1)
  let f₁ := MvPolynomial.harmonicSphereRestriction σ d₁ p₁
  let f₂ := MvPolynomial.harmonicSphereRestriction σ d₂ p₂
  let h₁ := MvPolynomial.harmonicSphereRestriction (R := ℝ) σ d₁
  let h₂ := MvPolynomial.harmonicSphereRestriction (R := ℝ) σ d₂
  let r₁ := MvPolynomial.mapHarmonicSubmodule (RCLike.reLm (K := 𝕜)).toAddMonoidHom d₁ p₁
  let i₁ := MvPolynomial.mapHarmonicSubmodule (RCLike.imLm (K := 𝕜)).toAddMonoidHom d₁ p₁
  let r₂ := MvPolynomial.mapHarmonicSubmodule (RCLike.reLm (K := 𝕜)).toAddMonoidHom d₂ p₂
  let i₂ := MvPolynomial.mapHarmonicSubmodule (RCLike.imLm (K := 𝕜)).toAddMonoidHom d₂ p₂
  have hint : Integrable (fun x ↦ f₂ x * starRingEnd 𝕜 (f₁ x)) μ :=
    (f₂.continuous.mul ((RCLike.conjCLE (K := 𝕜)).continuous.comp
      f₁.continuous)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hintMul (a b) : Integrable (fun x ↦ h₁ a x * h₂ b x) μ :=
    ((h₁ a).continuous.mul (h₂ b).continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hmul (a b) : ∫ x, h₁ a x * h₂ b x ∂μ = 0 :=
    integral_harmonicSphereRestriction_mul_eq_zero hm hd a b
  rw [ContinuousMap.inner_toLp]
  apply RCLike.ext
  · rw [map_zero, ← RCLike.reCLM_apply, ← RCLike.reCLM.integral_comp_comm hint]
    have hre : (fun x ↦ RCLike.reCLM (f₂ x * starRingEnd 𝕜 (f₁ x))) =
        fun x ↦ h₁ r₁ x * h₂ r₂ x + h₁ i₁ x * h₂ i₂ x := funext fun x ↦ by
      simp only [RCLike.reCLM_apply, RCLike.mul_re, RCLike.conj_re, RCLike.conj_im,
        MvPolynomial.harmonicSphereRestriction_mapHarmonicSubmodule_apply, RCLike.reLm_coe,
        RCLike.imLm_coe, f₁, f₂, h₁, h₂, r₁, i₁, r₂, i₂]
      ring
    rw [hre, integral_add (hintMul r₁ r₂) (hintMul i₁ i₂), hmul r₁ r₂, hmul i₁ i₂, add_zero]
  · rw [map_zero, ← RCLike.imCLM_apply, ← RCLike.imCLM.integral_comp_comm hint]
    have him : (fun x ↦ RCLike.imCLM (f₂ x * starRingEnd 𝕜 (f₁ x))) =
        fun x ↦ h₁ r₁ x * h₂ i₂ x - h₁ i₁ x * h₂ r₂ x := funext fun x ↦ by
      simp only [RCLike.imCLM_apply, RCLike.mul_im, RCLike.conj_re, RCLike.conj_im,
        MvPolynomial.harmonicSphereRestriction_mapHarmonicSubmodule_apply, RCLike.reLm_coe,
        RCLike.imLm_coe, f₁, f₂, h₁, h₂, r₁, i₁, r₂, i₂]
      ring
    rw [him, integral_sub (hintMul r₁ i₂) (hintMul i₁ r₂), hmul r₁ i₂, hmul i₁ r₂, sub_zero]

end Eigenvalue

section Completeness

variable {σ : Type*} [Fintype σ] {m : ℕ} [Fact (finrank ℝ (EuclideanSpace ℝ σ) = m + 1)]

/-- **Complete `C²` degree-`d` eigenspace identification on the round sphere (`m ≥ 1`).** A `C²`
function `f : Sᵐ → ℝ` satisfies `Δ_{Sᵐ} f = -d (d + m - 1) f` if and only if it is the restriction
of a real harmonic homogeneous polynomial of degree `d`. -/
theorem laplaceBeltrami_eq_neg_mul_iff_exists_harmonicSphereRestriction (hm : 1 ≤ m) (d : ℕ)
    {f : sphere (0 : EuclideanSpace ℝ σ) 1 → ℝ} (hf : ContMDiff (𝓡 m) 𝓘(ℝ, ℝ) 2 f) :
    (∀ x, Manifold.laplaceBeltrami (𝓡 m) f x = -(d : ℝ) * ((d : ℝ) + m - 1) * f x) ↔
      ∃ p : MvPolynomial.harmonicSubmodule σ ℝ d,
        ⇑(MvPolynomial.harmonicSphereRestriction σ d p) = f := by
  refine ⟨fun heig ↦ ?_, ?_⟩
  · have : IsManifold (𝓡 m) 1 (sphere (0 : EuclideanSpace ℝ σ) 1) := IsManifold.of_le le_top
    let μ := riemannianVolume (𝓡 m) (sphere (0 : EuclideanSpace ℝ σ) 1)
    let T := ContinuousMap.toLp (E := ℝ) 2 μ ℝ
    let fC : C(sphere (0 : EuclideanSpace ℝ σ) 1, ℝ) := ⟨f, hf.continuous⟩
    let K : Submodule ℝ (Lp ℝ 2 μ) :=
      LinearMap.range (T.toLinearMap.comp (MvPolynomial.harmonicSphereRestriction (R := ℝ) σ d))
    obtain ⟨p, hp⟩ := LinearMap.mem_range.1 (K.starProjection_apply_mem (T fC))
    simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe] at hp
    have hr_mem : T fC - K.starProjection (T fC) ∈ Kᗮ := K.sub_starProjection_mem_orthogonal (T fC)
    have hr_zero : T fC - K.starProjection (T fC) = 0 := by
      refine eq_zero_of_forall_inner_toLp_harmonicSphereRestriction_eq_zero fun e q ↦ ?_
      rcases eq_or_ne e d with rfl | hed
      · exact (K.mem_orthogonal _).1 hr_mem _ (LinearMap.mem_range.2 ⟨q, by simp [T]⟩)
      · rw [inner_sub_right, ← hp, inner_toLp_harmonicSphereRestriction_eq_zero hm hed q p,
          sub_zero, ContinuousMap.inner_toLp]
        have hne := (strictMono_natCast_mul_add_sub_one hm).injective.ne hed.symm
        simp only [RCLike.conj_to_real, fC, ContinuousMap.coe_mk, mul_comm (f _)]
        exact integral_harmonicSphereRestriction_mul_eq_zero_of_laplaceBeltrami_eq_neg_mul hf
          (fun x ↦ by rw [heig x]; ring) hne q
    have hTf : T (MvPolynomial.harmonicSphereRestriction σ d p) = T fC :=
      hp.trans (sub_eq_zero.1 hr_zero).symm
    exact ⟨p, congrArg DFunLike.coe ((ContinuousMap.toLp_injective (p := 2) (𝕜 := ℝ) μ) hTf)⟩
  · rintro ⟨p, rfl⟩ x
    exact laplaceBeltrami_harmonicSphereRestriction d p x

/-- **Smooth/`C²` eigenfunctions of the round sphere (`m ≥ 1`).** Every nonzero `C²` function `f`
on the unit round sphere `Sᵐ` satisfying `Δ_{Sᵐ} f = -λ f` has `λ = d (d + m - 1)` for some degree
`d : ℕ` and is the restriction of a real harmonic homogeneous polynomial of degree `d`. -/
theorem eq_harmonicSphereRestriction_of_laplaceBeltrami_eq_neg_mul (hm : 1 ≤ m)
    (f : sphere (0 : EuclideanSpace ℝ σ) 1 → ℝ) (hf : ContMDiff (𝓡 m) 𝓘(ℝ, ℝ) 2 f) (hf0 : f ≠ 0)
    {lam : ℝ} (heig : ∀ x, Manifold.laplaceBeltrami (𝓡 m) f x = -lam * f x) :
    ∃ d : ℕ, lam = (d : ℝ) * ((d : ℝ) + m - 1) ∧
      ∃ p : MvPolynomial.harmonicSubmodule σ ℝ d,
        ⇑(MvPolynomial.harmonicSphereRestriction σ d p) = f := by
  have : IsManifold (𝓡 m) 1 (sphere (0 : EuclideanSpace ℝ σ) 1) := IsManifold.of_le le_top
  let μ := riemannianVolume (𝓡 m) (sphere (0 : EuclideanSpace ℝ σ) 1)
  let T := ContinuousMap.toLp (E := ℝ) 2 μ ℝ
  let fC : C(sphere (0 : EuclideanSpace ℝ σ) 1, ℝ) := ⟨f, hf.continuous⟩
  have hex : ∃ d : ℕ, lam = (d : ℝ) * ((d : ℝ) + m - 1) := by
    by_contra! hne
    have hTf : T fC = 0 := by
      refine eq_zero_of_forall_inner_toLp_harmonicSphereRestriction_eq_zero fun d p ↦ ?_
      rw [ContinuousMap.inner_toLp]
      simp only [RCLike.conj_to_real, fC, ContinuousMap.coe_mk, mul_comm (f _)]
      exact integral_harmonicSphereRestriction_mul_eq_zero_of_laplaceBeltrami_eq_neg_mul hf heig
        (hne d) p
    have hfC : fC = 0 :=
      (ContinuousMap.toLp_injective (p := 2) (𝕜 := ℝ) μ) (hTf.trans T.map_zero.symm)
    exact hf0 (congrArg DFunLike.coe hfC)
  obtain ⟨d, rfl⟩ := hex
  refine ⟨d, rfl, (laplaceBeltrami_eq_neg_mul_iff_exists_harmonicSphereRestriction hm d hf).1 ?_⟩
  intro x
  rw [heig x]
  ring

end Completeness

end TauCeti

end
