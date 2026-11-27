/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giada Franz, The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Reproducing
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Sphere.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Sphere.Harmonic
public import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Isometry
public import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Support
public import TauCeti.Geometry.Sphere.Connected
import TauCeti.Geometry.Manifold.Instances.Sphere

/-!
# Degree-specific harmonic subspaces of the round sphere and their reproducing kernels

The spherical harmonics of degree `d` on the unit sphere `Sᵐ ⊂ ℝᵐ⁺¹` form a finite-dimensional
space of continuous functions, which we view as a subspace `harmonicsL2 m d` of `L²(Sᵐ)` for the
round Riemannian volume. Each of its elements has a continuous representative
`toContinuousMap m d w`.
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

* `TauCeti.Manifold.Eigenmap.harmonicsL2`: the degree-`d` spherical harmonics in `L²(Sᵐ)`.
* `TauCeti.Manifold.Eigenmap.toContinuousMap`: the continuous representative map.
* `TauCeti.Manifold.Eigenmap.act`: the right pullback action of linear isometries.

## Main results

* `TauCeti.Manifold.Eigenmap.finrank_harmonicsL2_pos`: the harmonic subspaces are nonzero
  when `1 ≤ m`.
* `TauCeti.Manifold.Eigenmap.inner_eq_integral`: the inner product is `∫ f g`.
* `TauCeti.Manifold.Eigenmap.inner_act`: the right pullback action preserves inner products.
* `TauCeti.Manifold.Eigenmap.sum_toContinuousMap_mul_toContinuousMap_smul`: the reproducing
  kernel is invariant.
* `TauCeti.Manifold.Eigenmap.sum_toContinuousMap_sq_eq_card_div_volume`: `Σᵢ fᵢ(x)² = N / Vol(Sᵐ)`.

Adapted from Giada Franz’s formalization in
[ColdingMinicozziTheory](https://github.com/riccardobrasca/ColdingMinicozziTheory/blob/cec8d4477da2d9786e275ed10f217513e9a52264/ForTauCeti/Geometry/Manifold/Riemannian/Sphere/Eigenmap/Basic.lean),
revision `cec8d4477da2d9786e275ed10f217513e9a52264`.

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

attribute [local instance] TauCeti.finrank_euclideanSpace_fin_succ_fact

/-- The spherical harmonics of degree `d`, as continuous functions on `Sᵐ`. -/
def harmonics : Submodule ℝ C(Sₘ, ℝ) :=
  LinearMap.range (harmonicSphereRestriction (Fin (m + 1)) (R := ℝ) d)

/-- The continuous harmonic subspace is the range of harmonic polynomial restriction. -/
theorem harmonics_def : harmonics m d =
    LinearMap.range (harmonicSphereRestriction (Fin (m + 1)) (R := ℝ) d) :=
  (rfl)

/-- The degree-`d` harmonic subspace of `L²(Sᵐ)`, in every dimension. For `1 ≤ m`, it
corresponds to the full `C²` round Laplace–Beltrami eigenspace of eigenvalue
`-d * (d + m - 1)`, by
`TauCeti.laplaceBeltrami_eq_neg_mul_iff_exists_harmonicSphereRestriction`. -/
def harmonicsL2 : Submodule ℝ (Lp ℝ 2 volₘ) :=
  (harmonics m d).map (ContinuousMap.toLp (E := ℝ) 2 volₘ ℝ).toLinearMap

/-- Membership in the `L²` harmonic subspace is represented by a continuous harmonic. -/
theorem mem_harmonicsL2_iff (w : Lp ℝ 2 volₘ) :
    w ∈ harmonicsL2 m d ↔ ∃ f ∈ harmonics m d,
      ContinuousMap.toLp (E := ℝ) 2 volₘ ℝ f = w :=
  (Iff.rfl)

/-- The `L²` harmonic subspace is identified with the continuous spherical harmonics. -/
def harmonicsEquivHarmonicsL2 : harmonics m d ≃ₗ[ℝ] harmonicsL2 m d :=
  Submodule.equivMapOfInjective _ (ContinuousMap.toLp_injective volₘ) _

/-- The degree-`d` harmonic subspace has positive dimension for every `d` when `1 ≤ m`. -/
theorem finrank_harmonicsL2_pos (hm : 1 ≤ m) : 0 < finrank ℝ (harmonicsL2 m d) := by
  rw [← (harmonicsEquivHarmonicsL2 m d).finrank_eq, harmonics_def]
  exact finrank_range_harmonicSphereRestriction_pos (K := ℝ) (Fintype.card_fin (m + 1)) d hm

instance instFiniteDimensionalHarmonics : FiniteDimensional ℝ (harmonics m d) :=
  LinearMap.finiteDimensional_range _

instance instFiniteDimensionalHarmonicsL2 : FiniteDimensional ℝ (harmonicsL2 m d) :=
  Module.Finite.map _ _

instance instCompleteSpaceHarmonicsL2 : CompleteSpace (harmonicsL2 m d) :=
  FiniteDimensional.completeSpace ℝ _

/-- The continuous representative of an element of the `L²` harmonic subspace, as a linear map. -/
def toContinuousMap : harmonicsL2 m d →ₗ[ℝ] C(Sₘ, ℝ) :=
  (harmonics m d).subtype ∘ₗ (harmonicsEquivHarmonicsL2 m d).symm.toLinearMap

/-- The continuous representative of the class of a continuous harmonic is itself. -/
@[simp]
theorem toContinuousMap_harmonicsEquivHarmonicsL2 (f : harmonics m d) :
    toContinuousMap m d (harmonicsEquivHarmonicsL2 m d f) = f := by
  simp [toContinuousMap]

/-- The underlying `L²` class of a continuous harmonic is its `toLp` image. -/
@[simp]
theorem coe_harmonicsEquivHarmonicsL2 (f : harmonics m d) :
    (harmonicsEquivHarmonicsL2 m d f : Lp ℝ 2 volₘ) =
      ContinuousMap.toLp (E := ℝ) 2 volₘ ℝ (f : C(Sₘ, ℝ)) :=
  Submodule.coe_equivMapOfInjective_apply _ (ContinuousMap.toLp_injective volₘ) _ f

theorem toContinuousMap_mem (w : harmonicsL2 m d) : toContinuousMap m d w ∈ harmonics m d :=
  ((harmonicsEquivHarmonicsL2 m d).symm w).property

/-- Sending a continuous representative back to `L²` recovers the original class. -/
@[simp]
theorem toLp_toContinuousMap (w : harmonicsL2 m d) :
    ContinuousMap.toLp (E := ℝ) 2 volₘ ℝ (toContinuousMap m d w) = w :=
  Submodule.map_equivMapOfInjective_symm_apply _ (ContinuousMap.toLp_injective volₘ) _ w

/-- Evaluation of continuous representatives makes the harmonic subspace an RKHS. -/
instance instRKHSHarmonicsL2 : RKHS ℝ (harmonicsL2 m d) Sₘ ℝ where
  coeCLM := (ContinuousMap.coeFnCLM ℝ).comp (toContinuousMap m d).toContinuousLinearMap
  coeCLM_injective := by
    intro w w' h
    apply Subtype.ext
    rw [← toLp_toContinuousMap m d w, ← toLp_toContinuousMap m d w']
    exact congrArg (ContinuousMap.toLp (E := ℝ) 2 volₘ ℝ) (ContinuousMap.coe_injective h)

/-- The RKHS function coercion evaluates the continuous representative. -/
@[simp]
theorem coe_eq_toContinuousMap (w : harmonicsL2 m d) : ⇑w = toContinuousMap m d w :=
  (rfl)

/-- The inner product of the harmonic subspace is the `L²` pairing of the representatives. -/
theorem inner_eq_integral (w w' : harmonicsL2 m d) :
    ⟪w, w'⟫_ℝ = ∫ x, toContinuousMap m d w x * toContinuousMap m d w' x ∂volₘ := by
  rw [Submodule.coe_inner, ← toLp_toContinuousMap m d w, ← toLp_toContinuousMap m d w',
    ContinuousMap.inner_toLp]
  simp only [conj_trivial]
  exact integral_congr_ae (Filter.Eventually.of_forall fun x ↦ mul_comm _ _)

/-- The right pullback action of linear isometries on the harmonic subspace, `w ↦ w ∘ (e • ·)`.
Pullback reverses composition:
`act m d (e₁ * e₂) w = act m d e₂ (act m d e₁ w)`. -/
def act (e : Eₘ ≃ₗᵢ[ℝ] Eₘ) : harmonicsL2 m d →ₗ[ℝ] harmonicsL2 m d :=
  (harmonicsEquivHarmonicsL2 m d).toLinearMap ∘ₗ
    (((ContinuousMap.compCLM ℝ (M := ℝ)
      ⟨e.unitSphereIsometryEquiv,
        e.unitSphereIsometryEquiv.isometry.continuous⟩).toLinearMap.restrict
      fun _ hf ↦ by
        rw [harmonics_def] at hf ⊢
        exact comp_unitSphereIsometryEquiv_mem_range_harmonicSphereRestriction hf) ∘ₗ
        (harmonicsEquivHarmonicsL2 m d).symm.toLinearMap)

/-- Pullback composes the continuous representative with the sphere action. -/
@[simp]
theorem toContinuousMap_act (e : Eₘ ≃ₗᵢ[ℝ] Eₘ) (w : harmonicsL2 m d) (x : Sₘ) :
    toContinuousMap m d (act m d e w) x = toContinuousMap m d w (e • x) := by
  simp only [toContinuousMap, act, LinearMap.coe_comp, comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply, Submodule.coe_subtype]
  exact congrArg (toContinuousMap m d w) (e.unitSphereIsometryEquiv_apply_eq_smul x)

/-- **The right pullback action preserves inner products**, since linear isometries preserve
the round volume. -/
theorem inner_act (e : Eₘ ≃ₗᵢ[ℝ] Eₘ) (w w' : harmonicsL2 m d) :
    ⟪act m d e w, act m d e w'⟫_ℝ = ⟪w, w'⟫_ℝ := by
  let Φ := LinearIsometryEquiv.unitSphereRiemannianIsometry (n := m) (k := m) e
  have hvol := Φ.measurePreserving_riemannianVolume
  have he : MeasurableEmbedding Φ := Φ.toDiffeomorph.toHomeomorph.measurableEmbedding
  have hint := hvol.integral_comp he
    (fun y ↦ toContinuousMap m d w y * toContinuousMap m d w' y)
  simpa only [inner_eq_integral, toContinuousMap_act, Φ,
    LinearIsometryEquiv.unitSphereRiemannianIsometry_apply] using hint

/-- Pullback by the identity fixes each harmonic class. -/
@[simp]
theorem act_one (w : harmonicsL2 m d) : act m d 1 w = w := by
  apply DFunLike.ext
  intro x
  simp only [coe_eq_toContinuousMap, toContinuousMap_act, one_smul]

/-- Pullback reverses multiplication of linear isometries. -/
theorem act_mul (e₁ e₂ : Eₘ ≃ₗᵢ[ℝ] Eₘ) (w : harmonicsL2 m d) :
    act m d (e₁ * e₂) w = act m d e₂ (act m d e₁ w) := by
  apply DFunLike.ext
  intro x
  simp only [coe_eq_toContinuousMap, toContinuousMap_act, mul_smul]

/-- Pullback by a linear isometry, bundled as a linear isometry equivalence. -/
def actEquiv (e : Eₘ ≃ₗᵢ[ℝ] Eₘ) : harmonicsL2 m d ≃ₗᵢ[ℝ] harmonicsL2 m d :=
  LinearIsometryEquiv.ofSurjective ((act m d e).isometryOfInner (inner_act m d e))
    (LinearMap.surjective_of_injective ((act m d e).isometryOfInner (inner_act m d e)).injective)

/-- The bundled pullback equivalence acts by `act`. -/
@[simp]
theorem actEquiv_apply (e : Eₘ ≃ₗᵢ[ℝ] Eₘ) (w : harmonicsL2 m d) :
    actEquiv m d e w = act m d e w :=
  (rfl)

/-- The scalar reproducing kernel is invariant under simultaneous sphere isometries. -/
theorem kernel_smul (e : Eₘ ≃ₗᵢ[ℝ] Eₘ) (x y : Sₘ) :
    RKHS.kernel (harmonicsL2 m d) (e • x) (e • y) 1 =
      RKHS.kernel (harmonicsL2 m d) x y 1 := by
  let b := stdOrthonormalBasis ℝ (harmonicsL2 m d)
  rw [← b.sum_apply_mul_conj_apply, ← (b.map (actEquiv m d e)).sum_apply_mul_conj_apply]
  simp only [coe_eq_toContinuousMap, OrthonormalBasis.map_apply, actEquiv_apply,
    toContinuousMap_act]

/-- **The reproducing kernel is invariant under the linear isometries.** -/
theorem sum_toContinuousMap_mul_toContinuousMap_smul {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ (harmonicsL2 m d))
    (e : Eₘ ≃ₗᵢ[ℝ] Eₘ) (x y : Sₘ) :
    ∑ i, toContinuousMap m d (b i) (e • x) * toContinuousMap m d (b i) (e • y) =
      ∑ i, toContinuousMap m d (b i) x * toContinuousMap m d (b i) y := by
  simpa only [← b.sum_apply_mul_conj_apply, conj_trivial, coe_eq_toContinuousMap] using
    kernel_smul m d e x y

/-- The sum of squares of an orthonormal basis is constant on the sphere. -/
theorem sum_toContinuousMap_sq_eq {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ (harmonicsL2 m d))
    (x y : Sₘ) : ∑ i, toContinuousMap m d (b i) x ^ 2 = ∑ i, toContinuousMap m d (b i) y ^ 2 := by
  obtain ⟨e, rfl⟩ := MulAction.exists_smul_eq (M := Eₘ ≃ₗᵢ[ℝ] Eₘ) x y
  simp only [sq]
  exact (sum_toContinuousMap_mul_toContinuousMap_smul m d b e x x).symm

/-- **The sum of squares of an orthonormal basis of a harmonic subspace is `N / Vol(Sᵐ)`.** -/
theorem sum_toContinuousMap_sq_eq_card_div_volume {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ (harmonicsL2 m d)) (x : Sₘ) :
    ∑ i, toContinuousMap m d (b i) x ^ 2 = Fintype.card ι / (volₘ).real univ := by
  have hint : ∫ y, ∑ i, toContinuousMap m d (b i) y ^ 2 ∂volₘ = Fintype.card ι := by
    rw [integral_finsetSum (f := fun i y ↦ toContinuousMap m d (b i) y ^ 2) _ fun i _ ↦
      ((toContinuousMap m d (b i)).continuous.pow 2).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)]
    have hi (i : ι) : ∫ y, toContinuousMap m d (b i) y ^ 2 ∂volₘ = 1 := by
      simp only [sq]
      rw [← inner_eq_integral, real_inner_self_eq_norm_sq, b.orthonormal.1 i, one_pow]
    simp [hi]
  have hconst : ∫ y, ∑ i, toContinuousMap m d (b i) y ^ 2 ∂volₘ =
      (volₘ).real univ * ∑ i, toContinuousMap m d (b i) x ^ 2 := by
    rw [integral_congr_ae (Filter.Eventually.of_forall fun y ↦ sum_toContinuousMap_sq_eq m d b y x),
      integral_const, smul_eq_mul]
  rw [eq_div_iff (measureReal_univ_pos (μ := volₘ)).ne', mul_comm, ← hconst, hint]

end TauCeti.Manifold.Eigenmap
