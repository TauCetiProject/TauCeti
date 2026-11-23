/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giada Franz
-/
module

public import Mathlib.Analysis.InnerProductSpace.Reproducing
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Sphere.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Sphere.Harmonic
public import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Isometry
public import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Support
public import TauCeti.Geometry.Sphere.Connected

/-!
# Degree-specific harmonic subspaces of the round sphere and their reproducing kernels

The spherical harmonics of degree `d` on the unit sphere `Sᵐ ⊂ ℝᵐ⁺¹` form a finite-dimensional
space of continuous functions, which we view as a subspace `eigenspace m d` of `L²(Sᵐ)` for the
round Riemannian volume. Each of its elements has a continuous representative `repLinear m d w`.
For `1 ≤ m`, these harmonic subspaces are nonzero. Their identification with the full `C²`
eigenspaces of the round Laplace–Beltrami operator is supplied by
`TauCeti.laplaceBeltrami_eq_neg_mul_iff_exists_harmonicSphereRestriction`.
This file constructs the degree-specific harmonic subspaces in every dimension.

Pullback by linear isometries `e` of `ℝᵐ⁺¹` defines a right action `w ↦ w ∘ (e • ·)` on it,
by isometries, since they preserve the round volume. For an orthonormal basis `f₁, …, f_N` of
the harmonic subspace, the reproducing kernel
`K(x, y) = Σᵢ fᵢ(x) fᵢ(y)` does not depend on the basis: it is the inner product of the Riesz
representatives of the evaluations at `x` and at `y`. Hence it is invariant under the linear
isometries, and since they act transitively on the sphere, `Σᵢ fᵢ(x)²` is constant. Integrating,
the constant is `N / Vol(Sᵐ)`.

## Main definitions

* `TauCeti.Manifold.Eigenmap.eigenspace`: the degree-`d` spherical harmonics in `L²(Sᵐ)`.
* `TauCeti.Manifold.Eigenmap.repLinear`: the continuous representative map.
* `TauCeti.Manifold.Eigenmap.act`: the right pullback action of linear isometries.

## Main results

* `TauCeti.Manifold.Eigenmap.finrank_eigenspace_pos`: the harmonic subspaces are nonzero
  when `1 ≤ m`.
* `TauCeti.Manifold.Eigenmap.inner_eq_integral`: the inner product is `∫ f g`.
* `TauCeti.Manifold.Eigenmap.inner_act`: the right pullback action preserves inner products.
* `TauCeti.Manifold.Eigenmap.sum_rep_mul_rep_smul`: the reproducing kernel is invariant.
* `TauCeti.Manifold.Eigenmap.sum_rep_sq`: `Σᵢ fᵢ(x)² = N / Vol(Sᵐ)`.

## References

* T. Takahashi, *Minimal immersions of Riemannian manifolds*, J. Math. Soc. Japan 18 (1966),
  380–385.
-/

public section

open Bundle Function Manifold MeasureTheory Metric Module MvPolynomial Set
open scoped ContDiff InnerProductSpace Manifold

noncomputable section

namespace TauCeti.Manifold.Eigenmap

variable (m d : ℕ)

local notation "Eₘ" => EuclideanSpace ℝ (Fin (m + 1))
local notation "Sₘ" => sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1
local notation "volₘ" => riemannianVolume (𝓡 m) (sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1)

/-- `ℝᵐ⁺¹` has dimension `m + 1`, so its unit sphere is an `m`-manifold. -/
local instance instFactFinrankEigenmapBasic : Fact (finrank ℝ Eₘ = m + 1) := ⟨by simp⟩

/-- The spherical harmonics of degree `d`, as continuous functions on `Sₘᵐ`. -/
def harmonics : Submodule ℝ C(Sₘ, ℝ) :=
  LinearMap.range (harmonicSphereRestriction (Fin (m + 1)) (R := ℝ) d)

/-- The spaces of spherical harmonics on a sphere of positive dimension are nonzero. -/
theorem finrank_harmonics_pos (hm : 1 ≤ m) : 0 < finrank ℝ (harmonics m d) := by
  rw [harmonics,
    finrank_range_harmonicSphereRestriction_eq_choose_sub (K := ℝ) (Fintype.card_fin (m + 1)) d]
  split_ifs with hd
  · obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le' hd
    have h1 : (m + e + 1 + 1).choose (e + 1 + 1) =
        (m + e).choose e + (m + e).choose (e + 1) + (m + e + 1).choose (e + 1 + 1) := by
      rw [Nat.choose_succ_succ', Nat.choose_succ_succ']
    have h2 : 0 < (m + e + 1).choose (e + 1 + 1) := Nat.choose_pos (by omega)
    have h3 : m + (e + 2) = m + e + 1 + 1 := by omega
    rw [h3, show m + e + 1 + 1 - 2 = m + e by omega, show e + 2 - 2 = e by omega,
      show e + 2 = e + 1 + 1 by omega, h1]
    omega
  · rw [Nat.sub_zero]
    exact Nat.choose_pos (by omega)

/-- The degree-`d` harmonic subspace of `L²(Sᵐ)`, in every dimension. For `1 ≤ m`, it
corresponds to the full `C²` round Laplace–Beltrami eigenspace of eigenvalue
`-d * (d + m - 1)`, by
`TauCeti.laplaceBeltrami_eq_neg_mul_iff_exists_harmonicSphereRestriction`. -/
def eigenspace : Submodule ℝ (Lp ℝ 2 volₘ) :=
  (harmonics m d).map (ContinuousMap.toLp (E := ℝ) 2 volₘ ℝ).toLinearMap

/-- The eigenspace is identified with the continuous spherical harmonics. -/
def equiv : harmonics m d ≃ₗ[ℝ] eigenspace m d :=
  Submodule.equivMapOfInjective _ (ContinuousMap.toLp_injective volₘ) _

/-- **The eigenspaces of the round sphere of positive dimension are nonzero.** -/
theorem finrank_eigenspace_pos (hm : 1 ≤ m) : 0 < finrank ℝ (eigenspace m d) := by
  rw [← (equiv m d).finrank_eq]
  exact finrank_harmonics_pos m d hm

instance instFiniteDimensionalHarmonics : FiniteDimensional ℝ (harmonics m d) :=
  LinearMap.finiteDimensional_range _

instance instFiniteDimensionalEigenspace : FiniteDimensional ℝ (eigenspace m d) :=
  Module.Finite.map _ _

instance instCompleteSpaceEigenspace : CompleteSpace (eigenspace m d) :=
  FiniteDimensional.completeSpace ℝ _

/-- The continuous representative of an element of the eigenspace, as a linear map. -/
def repLinear : eigenspace m d →ₗ[ℝ] C(Sₘ, ℝ) :=
  (harmonics m d).subtype ∘ₗ (equiv m d).symm.toLinearMap

theorem rep_mem (w : eigenspace m d) : repLinear m d w ∈ harmonics m d :=
  ((equiv m d).symm w).property

theorem toL2_rep (w : eigenspace m d) :
    ContinuousMap.toLp (E := ℝ) 2 volₘ ℝ (repLinear m d w) = w :=
  Submodule.map_equivMapOfInjective_symm_apply _ (ContinuousMap.toLp_injective volₘ) _ w

/-- Evaluation of continuous representatives makes the harmonic subspace an RKHS. -/
instance instRKHSEigenspace : RKHS ℝ (eigenspace m d) Sₘ ℝ where
  coeCLM := (ContinuousMap.coeFnCLM ℝ).comp (repLinear m d).toContinuousLinearMap
  coeCLM_injective := by
    intro w w' h
    apply Subtype.ext
    rw [← toL2_rep m d w, ← toL2_rep m d w']
    exact congrArg (ContinuousMap.toLp (E := ℝ) 2 volₘ ℝ) (ContinuousMap.coe_injective h)

/-- The inner product of the eigenspace is the `L²` pairing of the representatives. -/
theorem inner_eq_integral (w w' : eigenspace m d) :
    ⟪w, w'⟫_ℝ = ∫ x, repLinear m d w x * repLinear m d w' x ∂volₘ := by
  rw [Submodule.coe_inner, ← toL2_rep m d w, ← toL2_rep m d w', ContinuousMap.inner_toLp]
  simp only [conj_trivial]
  exact integral_congr_ae (Filter.Eventually.of_forall fun x ↦ mul_comm _ _)

/-- **The reproducing kernel does not depend on the orthonormal basis.** -/
theorem sum_rep_mul_rep {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ (eigenspace m d))
    (x y : Sₘ) : ∑ i, repLinear m d (b i) x * repLinear m d (b i) y =
      ⟪RKHS.kerFun (eigenspace m d) x 1, RKHS.kerFun (eigenspace m d) y 1⟫_ℝ := by
  rw [← b.sum_inner_mul_inner]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp only [RKHS.kerFun_inner, RKHS.inner_kerFun, Real.inner_apply, mul_one, one_mul]
  rfl

theorem comp_unitSphereIsometryEquiv_mem {e : Eₘ ≃ₗᵢ[ℝ] Eₘ} {f : C(Sₘ, ℝ)}
    (hf : f ∈ harmonics m d) :
    f.comp ⟨e.unitSphereIsometryEquiv, e.unitSphereIsometryEquiv.isometry.continuous⟩ ∈
      harmonics m d := by
  obtain ⟨p, rfl⟩ := hf
  set g : Matrix.orthogonalGroup (Fin (m + 1)) ℝ :=
    (Matrix.UnitaryGroup.toLinearIsometryEquiv).symm e⁻¹
  have hg : Matrix.UnitaryGroup.toLinearIsometryEquiv g⁻¹ = e := by
    rw [map_inv, MulEquiv.apply_symm_apply, inv_inv]
  refine ⟨harmonicRep (Fin (m + 1)) ℝ d g p, ContinuousMap.ext fun x ↦ ?_⟩
  rw [harmonicSphereRestriction_harmonicRep_apply, hg]
  exact congrArg (harmonicSphereRestriction (Fin (m + 1)) (R := ℝ) d p)
    (e.unitSphereIsometryEquiv_apply_eq_smul x).symm

/-- The right pullback action of linear isometries on the eigenspace, `w ↦ w ∘ (e • ·)`.
Pullback reverses composition:
`act m d (e₁ * e₂) w = act m d e₂ (act m d e₁ w)`. -/
def act (e : Eₘ ≃ₗᵢ[ℝ] Eₘ) : eigenspace m d →ₗ[ℝ] eigenspace m d :=
  (equiv m d).toLinearMap ∘ₗ
    (((ContinuousMap.compCLM ℝ (M := ℝ)
      ⟨e.unitSphereIsometryEquiv,
        e.unitSphereIsometryEquiv.isometry.continuous⟩).toLinearMap.restrict
      fun _ hf ↦ comp_unitSphereIsometryEquiv_mem m d hf) ∘ₗ (equiv m d).symm.toLinearMap)

theorem rep_act (e : Eₘ ≃ₗᵢ[ℝ] Eₘ) (w : eigenspace m d) (x : Sₘ) :
    repLinear m d (act m d e w) x = repLinear m d w (e • x) := by
  simp only [repLinear, act, LinearMap.coe_comp, comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply, Submodule.coe_subtype]
  exact congrArg (repLinear m d w) (e.unitSphereIsometryEquiv_apply_eq_smul x)

/-- **The right pullback action preserves inner products**, since linear isometries preserve
the round volume. -/
theorem inner_act (e : Eₘ ≃ₗᵢ[ℝ] Eₘ) (w w' : eigenspace m d) :
    ⟪act m d e w, act m d e w'⟫_ℝ = ⟪w, w'⟫_ℝ := by
  have hemb : MeasurableEmbedding (fun x : Sₘ ↦ e • x) := by
    have h := (LinearIsometryEquiv.unitSphereIsometryEquiv e).toHomeomorph.measurableEmbedding
    have hcoe : ⇑(LinearIsometryEquiv.unitSphereIsometryEquiv e).toHomeomorph =
        fun x : Sₘ ↦ e • x :=
      funext (LinearIsometryEquiv.unitSphereIsometryEquiv_apply_eq_smul e)
    rwa [hcoe] at h
  rw [inner_eq_integral, inner_eq_integral]
  simp only [rep_act]
  have hvol : MeasurePreserving (fun x : Sₘ ↦ e • x) volₘ volₘ := by
    let Φ := LinearIsometryEquiv.unitSphereRiemannianIsometry (n := m) (k := m) e
    have heq : (Φ : Sₘ → Sₘ) = (fun x : Sₘ ↦ e • x) := funext fun x ↦
      LinearIsometryEquiv.unitSphereRiemannianIsometry_apply e x
    rw [← heq]
    exact Φ.measurePreserving_riemannianVolume
  exact hvol.integral_comp hemb (fun y ↦ repLinear m d w y * repLinear m d w' y)

/-- **The reproducing kernel is invariant under the linear isometries.** -/
theorem sum_rep_mul_rep_smul {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ (eigenspace m d))
    (e : Eₘ ≃ₗᵢ[ℝ] Eₘ) (x y : Sₘ) :
    ∑ i, repLinear m d (b i) (e • x) * repLinear m d (b i) (e • y) =
      ∑ i, repLinear m d (b i) x * repLinear m d (b i) y := by
  let A := (act m d e).isometryOfInner (inner_act m d e)
  let b' := b.map (LinearIsometryEquiv.ofSurjective A
    (LinearMap.surjective_of_injective A.injective))
  rw [sum_rep_mul_rep m d b x y, ← sum_rep_mul_rep m d b' x y]
  simp only [b', OrthonormalBasis.map_apply, LinearIsometryEquiv.coe_ofSurjective,
    LinearMap.coe_isometryOfInner, A, rep_act]

/-- The sum of squares of an orthonormal basis is constant on the sphere. -/
theorem sum_rep_sq_eq {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ (eigenspace m d))
    (x y : Sₘ) : ∑ i, repLinear m d (b i) x ^ 2 = ∑ i, repLinear m d (b i) y ^ 2 := by
  obtain ⟨e, rfl⟩ := MulAction.exists_smul_eq (M := Eₘ ≃ₗᵢ[ℝ] Eₘ) x y
  simp only [sq]
  exact (sum_rep_mul_rep_smul m d b e x x).symm

/-- **The sum of squares of an orthonormal basis of an eigenspace is `N / Vol(Sᵐ)`.** -/
theorem sum_rep_sq {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ (eigenspace m d)) (x : Sₘ) :
    ∑ i, repLinear m d (b i) x ^ 2 = Fintype.card ι / (volₘ).real univ := by
  have hint : ∫ y, ∑ i, repLinear m d (b i) y ^ 2 ∂volₘ = Fintype.card ι := by
    rw [integral_finsetSum (f := fun i y ↦ repLinear m d (b i) y ^ 2) _ fun i _ ↦
      ((repLinear m d (b i)).continuous.pow 2).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)]
    have hi (i : ι) : ∫ y, repLinear m d (b i) y ^ 2 ∂volₘ = 1 := by
      simp only [sq]
      rw [← inner_eq_integral, real_inner_self_eq_norm_sq, b.orthonormal.1 i, one_pow]
    simp [hi]
  have hconst : ∫ y, ∑ i, repLinear m d (b i) y ^ 2 ∂volₘ =
      (volₘ).real univ * ∑ i, repLinear m d (b i) x ^ 2 := by
    rw [integral_congr_ae (Filter.Eventually.of_forall fun y ↦ sum_rep_sq_eq m d b y x),
      integral_const, smul_eq_mul]
  rw [eq_div_iff (measureReal_univ_pos (μ := volₘ)).ne', mul_comm, ← hconst, hint]

end TauCeti.Manifold.Eigenmap
