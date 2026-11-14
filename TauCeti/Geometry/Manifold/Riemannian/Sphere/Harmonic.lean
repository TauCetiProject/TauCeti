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
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.Topology.Algebra.Module.FiniteDimension
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
2. **Orthogonality and `L²` completeness.** For `m ≥ 1`, the sequence `d ↦ d (d + m - 1)` is
   strictly increasing (`TauCeti.strictMono_natCast_mul_add_sub_one`), so Green's second identity
   for `riemannianVolume` forces spherical harmonics of distinct degrees (and, more generally, any
   `C²` eigenfunction with eigenvalue `λ ≠ d (d + m - 1)`) to be `L²`-orthogonal to degree-`d`
   spherical harmonics. Combining Stone–Weierstrass uniform density on `C(Sᵐ, 𝕜)` with density of
   continuous functions in `L²(Sᵐ, 𝕜)` shows that the span of spherical harmonics is dense in
   `L²(Sᵐ, 𝕜)` (`TauCeti.topologicalClosure_iSup_map_toLp_harmonicSphereRestriction`).
3. **Complete `C²` eigenspace classification (`m ≥ 1`).** Orthogonal projection onto the
   finite-dimensional degree-`d` harmonic subspace in `L²(Sᵐ, ℝ)` identifies the full `C²`
   eigenspace of `-d (d + m - 1)` with the range of `harmonicSphereRestriction σ d`
   (`TauCeti.laplaceBeltrami_eq_neg_mul_iff_exists_harmonicSphereRestriction`), and every nonzero
   `C²` solution of `Δ_{Sᵐ} f = -λ f` has `λ = d (d + m - 1)` and comes from a degree-`d` harmonic
   homogeneous polynomial (`TauCeti.eq_harmonicSphereRestriction_of_laplaceBeltrami_eq_neg_mul`).
   The hypothesis `1 ≤ m` is sharp: on `S⁰ = {±1}` the Laplace–Beltrami operator vanishes
   identically while `f(1) = 1, f(-1) = 2` is neither constant (`d = 0`) nor odd (`d = 1`).

## Main results

* `MvPolynomial.contMDiff_sphereEval`, `MvPolynomial.contMDiff_harmonicSphereRestriction`:
  polynomial restrictions and spherical harmonics are `C^k` (`k : ℕ∞ω`) on `Sᵐ`.
* `TauCeti.laplaceBeltrami_harmonicSphereRestriction`: degree-`d` spherical harmonics satisfy
  `Δ_{Sᵐ} f = -d (d + m - 1) f`.
* `TauCeti.integral_harmonicSphereRestriction_mul_eq_zero`,
  `TauCeti.inner_toLp_harmonicSphereRestriction_eq_zero`: orthogonality of distinct degrees
  (`m ≥ 1`).
* `TauCeti.topologicalClosure_iSup_map_toLp_harmonicSphereRestriction`: `L²(Sᵐ, 𝕜)` density of
  spherical harmonics (`[RCLike 𝕜]`).
* `TauCeti.laplaceBeltrami_eq_neg_mul_iff_exists_harmonicSphereRestriction`,
  `TauCeti.eq_harmonicSphereRestriction_of_laplaceBeltrami_eq_neg_mul`: complete `C²` eigenspace
  identification on `Sᵐ` (`m ≥ 1`).

## References

* M. E. Taylor, *Lectures on Lie Groups*, §8.2, Proposition 8.2.1 (spherical harmonics and the
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

/-- Evaluating a polynomial over a normed commutative `ℝ`-algebra on `EuclideanSpace ℝ σ` is `C^k`
for every `k : ℕ∞ω` (in particular real-analytic for `k = ω`). -/
theorem contDiff_eval_algebraMap {σ R : Type*} [Fintype σ] [NormedCommRing R] [NormedAlgebra ℝ R]
    {k : ℕ∞ω} (p : MvPolynomial σ R) :
    ContDiff ℝ k fun x : EuclideanSpace ℝ σ ↦ eval (fun i ↦ algebraMap ℝ R (x i)) p := by
  induction p using MvPolynomial.induction_on with
  | C a => simpa only [eval_C] using contDiff_const
  | add p q hp hq => simpa only [eval_add] using hp.add hq
  | mul_X p i hp =>
      have hfun : (fun x : EuclideanSpace ℝ σ ↦ algebraMap ℝ R (x i)) =
          ⇑(((1 : ℝ →L[ℝ] ℝ).smulRight (1 : R)).comp (EuclideanSpace.proj i)) :=
        funext fun x ↦ by simp [Algebra.algebraMap_eq_smul_one]
      have hcoord : ContDiff ℝ k fun x : EuclideanSpace ℝ σ ↦ algebraMap ℝ R (x i) := by
        rw [hfun]
        exact ContinuousLinearMap.contDiff _
      simpa only [eval_mul, eval_X] using hp.mul hcoord

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
  exact (contDiff_eval_algebraMap p).contMDiff.comp contMDiff_coe_sphere

/-- Every spherical harmonic in the image of `harmonicSphereRestriction` is `C^k` on the round
sphere for every `k : ℕ∞ω` (in particular analytic and `C^∞`). -/
theorem contMDiff_harmonicSphereRestriction {σ R : Type*} [Fintype σ] {m : ℕ}
    [Fact (finrank ℝ (EuclideanSpace ℝ σ) = m + 1)] [NormedCommRing R] [NormedAlgebra ℝ R]
    {k : ℕ∞ω} (d : ℕ) (p : harmonicSubmodule σ R d) :
    ContMDiff (𝓡 m) 𝓘(ℝ, R) k (harmonicSphereRestriction σ d p) := by
  rw [harmonicSphereRestriction_coe]
  exact contMDiff_sphereEval (p : MvPolynomial σ R)

/-- Away from the origin, multiplying the `0`-homogeneous radial extension `TauCeti.sphereExtend`
of a degree-`d` spherical harmonic by `‖x‖ ^ d` recovers the ambient harmonic polynomial. -/
theorem norm_pow_mul_sphereExtend_harmonicSphereRestriction {σ : Type*} [Fintype σ] (d : ℕ)
    (p : harmonicSubmodule σ ℝ d) {x : EuclideanSpace ℝ σ} (hx : x ≠ 0) :
    ‖x‖ ^ d * TauCeti.sphereExtend (harmonicSphereRestriction σ d p) x =
      eval x (p : MvPolynomial σ ℝ) := by
  rw [TauCeti.sphereExtend_of_ne_zero _ hx]
  simpa only [NormedSpace.normalize, harmonicSphereRestriction_coe] using
    ((mem_harmonicSubmodule_iff.1 p.2).1.eval_eq_norm_pow_mul_sphereEval hx).symm

end MvPolynomial

namespace TauCeti

section Eigenvalue

variable {σ : Type*} [Fintype σ] {m : ℕ} [Fact (finrank ℝ (EuclideanSpace ℝ σ) = m + 1)]

/-- **Spherical harmonics are round Laplace–Beltrami eigenfunctions.** Every real harmonic
homogeneous polynomial `p` of degree `d` restricts on `Sᵐ` to an eigenfunction of
`Manifold.laplaceBeltrami (𝓡 m)` with eigenvalue `d (d + m - 1)` (`Δ_{Sᵐ} f = -d (d + m - 1) f`),
valid for every `m : ℕ` and `d : ℕ`. -/
theorem laplaceBeltrami_harmonicSphereRestriction (d : ℕ)
    (p : MvPolynomial.harmonicSubmodule σ ℝ d) (x : sphere (0 : EuclideanSpace ℝ σ) 1) :
    Manifold.laplaceBeltrami (𝓡 m) (MvPolynomial.harmonicSphereRestriction σ d p) x =
      -(d : ℝ) * ((d : ℝ) + m - 1) * MvPolynomial.harmonicSphereRestriction σ d p x := by
  obtain ⟨hp_hom, hp_lap⟩ := MvPolynomial.mem_harmonicSubmodule_iff.1 p.2
  let F : EuclideanSpace ℝ σ → ℝ := fun y ↦ MvPolynomial.eval y (p : MvPolynomial σ ℝ)
  have hF_eq : F = fun y ↦ MvPolynomial.eval (fun i ↦ algebraMap ℝ ℝ (y i)) p.1 := by
    funext y
    simp only [F, Algebra.algebraMap_self, RingHom.id_apply]
  have hF : ContDiffAt ℝ 2 F x :=
    hF_eq ▸ (MvPolynomial.contDiff_eval_algebraMap (k := 2) p.1).contDiffAt
  have hrestr : ⇑(MvPolynomial.harmonicSphereRestriction σ d p) = F ∘ Subtype.val := by
    funext y
    simp only [MvPolynomial.harmonicSphereRestriction_coe, MvPolynomial.sphereEval_apply,
      Algebra.algebraMap_self, RingHom.id_apply, Function.comp_apply, F]
  have hsmul (t : ℝ) (_ : 0 < t) : F (t • (x : EuclideanSpace ℝ σ)) = t ^ (d : ℝ) * F x := by
    rw [Real.rpow_natCast]
    exact hp_hom.eval_smul t (x : EuclideanSpace ℝ σ)
  have hΔ : Δ F x = 0 := by
    rw [congrFun (MvPolynomial.laplacian_eval_euclidean p.1) x, hp_lap, map_zero]
  rw [hrestr, laplaceBeltrami_comp_coe_sphere_of_smul hF hsmul, hΔ]
  simp only [Function.comp_apply, F]
  ring

/-- For `1 ≤ m`, the spherical Laplace–Beltrami eigenvalues `d ↦ d (d + m - 1)` are strictly
increasing in the degree `d : ℕ`. -/
theorem strictMono_natCast_mul_add_sub_one {m : ℕ} (hm : 1 ≤ m) :
    StrictMono fun d : ℕ ↦ (d : ℝ) * ((d : ℝ) + m - 1) := by
  intro d₁ d₂ hd
  nlinarith [show (d₁ : ℝ) < d₂ from Nat.cast_lt.2 hd,
    show (1 : ℝ) ≤ m from Nat.one_le_cast.2 hm, Nat.cast_nonneg (α := ℝ) d₁]

/-- Green's second identity on the round sphere forces any `C²` eigenfunction with
`Δ_{Sᵐ} g = -λ g` and `λ ≠ d (d + m - 1)` to be `L²`-orthogonal to every degree-`d` spherical
harmonic. -/
theorem integral_harmonicSphereRestriction_mul_eq_zero_of_laplaceBeltrami_eq_neg_mul
    {g : sphere (0 : EuclideanSpace ℝ σ) 1 → ℝ} (hg : ContMDiff (𝓡 m) 𝓘(ℝ, ℝ) 2 g) {lam : ℝ}
    (heig : ∀ x, Manifold.laplaceBeltrami (𝓡 m) g x = -lam * g x) {d : ℕ}
    (hlam : lam ≠ (d : ℝ) * ((d : ℝ) + m - 1))
    (p : MvPolynomial.harmonicSubmodule σ ℝ d) :
    ∫ x, MvPolynomial.harmonicSphereRestriction σ d p x * g x
      ∂riemannianVolume (𝓡 m) (sphere (0 : EuclideanSpace ℝ σ) 1) = 0 := by
  have : IsManifold (𝓡 m) ∞ (sphere (0 : EuclideanSpace ℝ σ) 1) := IsManifold.of_le le_top
  let h : sphere (0 : EuclideanSpace ℝ σ) 1 → ℝ := MvPolynomial.harmonicSphereRestriction σ d p
  have hh : ContMDiff (𝓡 m) 𝓘(ℝ, ℝ) 2 h := MvPolynomial.contMDiff_harmonicSphereRestriction d p
  have hgreen := Manifold.integral_mul_laplaceBeltrami_right_eq_left hh
    (HasCompactSupport.of_compactSpace h) hg
  have hlhs : (fun x ↦ h x * Manifold.laplaceBeltrami (𝓡 m) g x) =
      fun x ↦ -lam * (h x * g x) := funext fun x ↦ by rw [heig x]; ring
  have hrhs : (fun x ↦ Manifold.laplaceBeltrami (𝓡 m) h x * g x) =
      fun x ↦ -((d : ℝ) * ((d : ℝ) + m - 1)) * (h x * g x) := funext fun x ↦ by
    rw [show Manifold.laplaceBeltrami (𝓡 m) h x = _ from
      laplaceBeltrami_harmonicSphereRestriction d p x]
    ring
  rw [hlhs, hrhs, integral_const_mul, integral_const_mul] at hgreen
  have hsub : (lam - (d : ℝ) * ((d : ℝ) + m - 1)) *
      ∫ x, h x * g x ∂riemannianVolume (𝓡 m) (sphere (0 : EuclideanSpace ℝ σ) 1) = 0 := by
    linarith
  exact (mul_eq_zero.1 hsub).resolve_left (sub_ne_zero.2 hlam)

/-- Spherical harmonics of distinct degrees on `Sᵐ` (`m ≥ 1`) are orthogonal with respect to the
round `riemannianVolume`. -/
theorem integral_harmonicSphereRestriction_mul_eq_zero (hm : 1 ≤ m) {d₁ d₂ : ℕ} (hd : d₁ ≠ d₂)
    (p₁ : MvPolynomial.harmonicSubmodule σ ℝ d₁) (p₂ : MvPolynomial.harmonicSubmodule σ ℝ d₂) :
    ∫ x, MvPolynomial.harmonicSphereRestriction σ d₁ p₁ x *
        MvPolynomial.harmonicSphereRestriction σ d₂ p₂ x
      ∂riemannianVolume (𝓡 m) (sphere (0 : EuclideanSpace ℝ σ) 1) = 0 :=
  integral_harmonicSphereRestriction_mul_eq_zero_of_laplaceBeltrami_eq_neg_mul
    (MvPolynomial.contMDiff_harmonicSphereRestriction d₂ p₂)
    (fun x ↦ by rw [laplaceBeltrami_harmonicSphereRestriction]; ring)
    ((strictMono_natCast_mul_add_sub_one hm).injective.ne hd.symm) p₁

/-- In `L²(Sᵐ, ℝ)` with the round Riemannian volume (`m ≥ 1`), spherical harmonics of distinct
degrees are orthogonal. -/
theorem inner_toLp_harmonicSphereRestriction_eq_zero (hm : 1 ≤ m) {d₁ d₂ : ℕ} (hd : d₁ ≠ d₂)
    (p₁ : MvPolynomial.harmonicSubmodule σ ℝ d₁) (p₂ : MvPolynomial.harmonicSubmodule σ ℝ d₂) :
    ⟪ContinuousMap.toLp (E := ℝ) 2 (riemannianVolume (𝓡 m) (sphere (0 : EuclideanSpace ℝ σ) 1)) ℝ
        (MvPolynomial.harmonicSphereRestriction σ d₁ p₁),
      ContinuousMap.toLp (E := ℝ) 2 (riemannianVolume (𝓡 m) (sphere (0 : EuclideanSpace ℝ σ) 1)) ℝ
        (MvPolynomial.harmonicSphereRestriction σ d₂ p₂)⟫_ℝ = 0 := by
  rw [ContinuousMap.inner_toLp]
  simp only [RCLike.conj_to_real, mul_comm (MvPolynomial.harmonicSphereRestriction σ d₂ p₂ _)]
  exact integral_harmonicSphereRestriction_mul_eq_zero hm hd p₁ p₂

end Eigenvalue

section Completeness

variable {σ : Type*} [Fintype σ] {m : ℕ} [Fact (finrank ℝ (EuclideanSpace ℝ σ) = m + 1)]

/-- **`L²` completeness of spherical harmonics on the round sphere.** For `[RCLike 𝕜]`, the span of
the images in `L²(Sᵐ, 𝕜)` (with respect to `riemannianVolume`) of all harmonic sphere-restriction
spaces is dense. -/
theorem topologicalClosure_iSup_map_toLp_harmonicSphereRestriction {𝕜 : Type*} [RCLike 𝕜] :
    Submodule.topologicalClosure
      (⨆ d, (LinearMap.range (MvPolynomial.harmonicSphereRestriction (R := 𝕜) σ d)).map
        (ContinuousMap.toLp (E := 𝕜) 2
          (riemannianVolume (𝓡 m) (sphere (0 : EuclideanSpace ℝ σ) 1)) 𝕜).toLinearMap) = ⊤ := by
  have : IsManifold (𝓡 m) 1 (sphere (0 : EuclideanSpace ℝ σ) 1) := IsManifold.of_le le_top
  let μ := riemannianVolume (𝓡 m) (sphere (0 : EuclideanSpace ℝ σ) 1)
  let T := ContinuousMap.toLp (E := 𝕜) 2 μ 𝕜
  let S₀ : Submodule 𝕜 C(sphere (0 : EuclideanSpace ℝ σ) 1, 𝕜) :=
    ⨆ d, LinearMap.range (MvPolynomial.harmonicSphereRestriction (R := 𝕜) σ d)
  rw [← Submodule.map_iSup]
  have hS₀ : Dense (S₀ : Set C(sphere (0 : EuclideanSpace ℝ σ) 1, 𝕜)) := by
    intro f
    rw [← Submodule.topologicalClosure_coe,
      MvPolynomial.topologicalClosure_iSup_range_harmonicSphereRestriction]
    trivial
  have hd : Dense ((S₀.map T.toLinearMap : Submodule 𝕜 (Lp 𝕜 2 μ)) : Set (Lp 𝕜 2 μ)) := by
    rw [Submodule.map_coe]
    exact (ContinuousMap.toLp_denseRange (p := 2) 𝕜 μ 𝕜
      (by simp)).dense_image T.continuous hS₀
  exact eq_top_iff.2 fun g _ ↦ hd g

/-- An element of `L²(Sᵐ, 𝕜)` orthogonal to every degree-`d` spherical harmonic is zero. -/
theorem eq_zero_of_forall_inner_toLp_harmonicSphereRestriction_eq_zero {𝕜 : Type*} [RCLike 𝕜]
    {g : Lp 𝕜 2 (riemannianVolume (𝓡 m) (sphere (0 : EuclideanSpace ℝ σ) 1))}
    (horth : ∀ (d : ℕ) (p : MvPolynomial.harmonicSubmodule σ 𝕜 d),
      ⟪ContinuousMap.toLp (E := 𝕜) 2
          (riemannianVolume (𝓡 m) (sphere (0 : EuclideanSpace ℝ σ) 1)) 𝕜
          (MvPolynomial.harmonicSphereRestriction σ d p), g⟫_𝕜 = 0) :
    g = 0 := by
  let μ := riemannianVolume (𝓡 m) (sphere (0 : EuclideanSpace ℝ σ) 1)
  let T := ContinuousMap.toLp (E := 𝕜) 2 μ 𝕜
  let W : Submodule 𝕜 (Lp 𝕜 2 μ) :=
    ⨆ d, (LinearMap.range (MvPolynomial.harmonicSphereRestriction (R := 𝕜) σ d)).map T.toLinearMap
  let K : Submodule 𝕜 (Lp 𝕜 2 μ) :=
    { carrier := {u | ⟪u, g⟫_𝕜 = 0}
      zero_mem' := inner_zero_left g
      add_mem' := fun {u v} hu hv ↦ by
        change ⟪u + v, g⟫_𝕜 = 0
        rw [inner_add_left, hu, hv, add_zero]
      smul_mem' := fun c {u} hu ↦ by
        change ⟪c • u, g⟫_𝕜 = 0
        rw [inner_smul_left, hu, mul_zero] }
  have hWK : W ≤ K := iSup_le fun d ↦ by
    rintro _ ⟨_, ⟨p, rfl⟩, rfl⟩
    exact horth d p
  have hclosed : IsClosed (K : Set (Lp 𝕜 2 μ)) :=
    isClosed_eq (continuous_id.inner continuous_const) continuous_const
  have hcl : closure (W : Set (Lp 𝕜 2 μ)) ⊆ K := closure_minimal hWK hclosed
  have hgW : g ∈ W.topologicalClosure := by
    rw [topologicalClosure_iSup_map_toLp_harmonicSphereRestriction]
    trivial
  exact inner_self_eq_zero.1 (hcl hgW)

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
    obtain ⟨p, hp⟩ : ∃ p, T (MvPolynomial.harmonicSphereRestriction σ d p) =
        K.starProjection (T fC) := (K.orthogonalProjectionOnto (T fC)).2
    have hr_mem : T fC - K.starProjection (T fC) ∈ Kᗮ := K.sub_starProjection_mem_orthogonal (T fC)
    have hr_zero : T fC - K.starProjection (T fC) = 0 := by
      refine eq_zero_of_forall_inner_toLp_harmonicSphereRestriction_eq_zero fun e q ↦ ?_
      rcases eq_or_ne e d with rfl | hed
      · exact (K.mem_orthogonal _).1 hr_mem _ ⟨q, rfl⟩
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
