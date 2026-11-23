/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giada Franz
-/
module

public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Sphere.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Sphere.Harmonic
public import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Isometry
public import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Support

/-!
# The eigenspaces of the round sphere and their reproducing kernels

The spherical harmonics of degree `d` on the unit sphere `Sᵐ ⊂ ℝᵐ⁺¹` form a finite-dimensional
space of continuous functions, which we view as a subspace `eigenspace m d` of `L²(Sᵐ)` for the
round Riemannian volume. Each of its elements has a continuous representative `rep m d w`.

Pullback by linear isometries `e` of `ℝᵐ⁺¹` defines a right action `w ↦ w ∘ (e • ·)` on it,
by isometries, since they preserve the round volume. For an orthonormal basis `f₁, …, f_N` of
the eigenspace, the reproducing kernel
`K(x, y) = Σᵢ fᵢ(x) fᵢ(y)` does not depend on the basis: it is the inner product of the Riesz
representatives of the evaluations at `x` and at `y`. Hence it is invariant under the linear
isometries, and since they act transitively on the sphere, `Σᵢ fᵢ(x)²` is constant. Integrating,
the constant is `N / Vol(Sᵐ)`.

## Main definitions

* `TauCeti.Manifold.Eigenmap.eigenspace`: the degree-`d` spherical harmonics in `L²(Sᵐ)`.
* `TauCeti.Manifold.Eigenmap.rep`: the continuous representative of an element.
* `TauCeti.Manifold.Eigenmap.act`: the right pullback action of linear isometries.

## Main results

* `TauCeti.Manifold.Eigenmap.finrank_eigenspace_pos`: the eigenspaces are nonzero.
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

/-- The inclusion of continuous functions into `L²(Sₘᵐ)`. -/
def toL2 : C(Sₘ, ℝ) →L[ℝ] Lp ℝ 2 volₘ := ContinuousMap.toLp (E := ℝ) 2 volₘ ℝ

theorem injective_toL2 : Injective (toL2 m) := ContinuousMap.toLp_injective volₘ

/-- **The eigenspace**: the spherical harmonics of degree `d` in `L²(Sₘᵐ)`. -/
def eigenspace : Submodule ℝ (Lp ℝ 2 volₘ) := (harmonics m d).map (toL2 m).toLinearMap

/-- The eigenspace is identified with the continuous spherical harmonics. -/
def equiv : harmonics m d ≃ₗ[ℝ] eigenspace m d :=
  Submodule.equivMapOfInjective _ (injective_toL2 m) _

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

/-- The continuous representative of an element of the eigenspace. -/
def rep (w : eigenspace m d) : C(Sₘ, ℝ) := repLinear m d w

theorem repLinear_apply (w : eigenspace m d) : repLinear m d w = rep m d w := by
  rfl

theorem rep_mem (w : eigenspace m d) : rep m d w ∈ harmonics m d :=
  ((equiv m d).symm w).property

/-- The representative of an element of the eigenspace is a spherical harmonic. -/
theorem exists_eq_harmonicSphereRestriction (w : eigenspace m d) :
    ∃ p, harmonicSphereRestriction (Fin (m + 1)) (R := ℝ) d p = rep m d w :=
  rep_mem m d w

theorem toL2_rep (w : eigenspace m d) : toL2 m (rep m d w) = w := by
  have h := congrArg Subtype.val ((equiv m d).apply_symm_apply w)
  exact h

theorem rep_add (w w' : eigenspace m d) : rep m d (w + w') = rep m d w + rep m d w' :=
  map_add (repLinear m d) w w'

theorem rep_smul (c : ℝ) (w : eigenspace m d) : rep m d (c • w) = c • rep m d w :=
  map_smul (repLinear m d) c w

/-- The inner product of the eigenspace is the `L²` pairing of the representatives. -/
theorem inner_eq_integral (w w' : eigenspace m d) :
    ⟪w, w'⟫_ℝ = ∫ x, rep m d w x * rep m d w' x ∂volₘ := by
  rw [Submodule.coe_inner, ← toL2_rep m d w, ← toL2_rep m d w', toL2, ContinuousMap.inner_toLp]
  simp only [conj_trivial, mul_comm]

/-- Evaluation at a point of the sphere, on the eigenspace. -/
def eval (x : Sₘ) : eigenspace m d →ₗ[ℝ] ℝ :=
  (ContinuousMap.evalCLM ℝ x).toLinearMap ∘ₗ repLinear m d

theorem eval_apply (x : Sₘ) (w : eigenspace m d) : eval m d x w = rep m d w x := by
  rfl

/-- The Riesz representative of the evaluation at `x`. -/
def kernel (x : Sₘ) : eigenspace m d :=
  (InnerProductSpace.toDual ℝ (eigenspace m d)).symm (LinearMap.toContinuousLinearMap (eval m d x))

theorem inner_kernel (x : Sₘ) (w : eigenspace m d) : ⟪kernel m d x, w⟫_ℝ = rep m d w x := by
  rw [kernel, InnerProductSpace.toDual_symm_apply]
  rfl

/-- **The reproducing kernel does not depend on the orthonormal basis.** -/
theorem sum_rep_mul_rep {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ (eigenspace m d))
    (x y : Sₘ) : ∑ i, rep m d (b i) x * rep m d (b i) y = ⟪kernel m d x, kernel m d y⟫_ℝ := by
  rw [← b.sum_inner_mul_inner]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [inner_kernel, real_inner_comm, inner_kernel]

/-- The action of a linear isometry on the sphere, as a continuous map. -/
def sphereAct (e : Eₘ ≃ₗᵢ[ℝ] Eₘ) : C(Sₘ, Sₘ) :=
  ⟨fun x ↦ e • x, by
    have h := (LinearIsometryEquiv.contMDiff_unitSphereEquiv (n := m) (k := m)
      (m := 0) e).continuous
    exact h.congr fun x ↦ Subtype.ext (by simp)⟩

theorem comp_sphereAct_mem {e : Eₘ ≃ₗᵢ[ℝ] Eₘ} {f : C(Sₘ, ℝ)} (hf : f ∈ harmonics m d) :
    f.comp (sphereAct m e) ∈ harmonics m d := by
  obtain ⟨p, rfl⟩ := hf
  set g : Matrix.orthogonalGroup (Fin (m + 1)) ℝ :=
    (Matrix.UnitaryGroup.toLinearIsometryEquiv).symm e⁻¹
  have hg : Matrix.UnitaryGroup.toLinearIsometryEquiv g⁻¹ = e := by
    rw [map_inv, MulEquiv.apply_symm_apply, inv_inv]
  refine ⟨harmonicRep (Fin (m + 1)) ℝ d g p, ContinuousMap.ext fun x ↦ ?_⟩
  rw [harmonicSphereRestriction_harmonicRep_apply, hg]
  rfl

/-- The right pullback action of linear isometries on the eigenspace, `w ↦ w ∘ (e • ·)`.
Pullback reverses composition:
`act m d (e₁ * e₂) w = act m d e₂ (act m d e₁ w)`. -/
def act (e : Eₘ ≃ₗᵢ[ℝ] Eₘ) : eigenspace m d →ₗ[ℝ] eigenspace m d :=
  (equiv m d).toLinearMap ∘ₗ
    (((ContinuousMap.compCLM ℝ (M := ℝ) (sphereAct m e)).toLinearMap.restrict
      fun _ hf ↦ comp_sphereAct_mem m d hf) ∘ₗ (equiv m d).symm.toLinearMap)

theorem rep_act (e : Eₘ ≃ₗᵢ[ℝ] Eₘ) (w : eigenspace m d) (x : Sₘ) :
    rep m d (act m d e w) x = rep m d w (e • x) := by
  simp only [rep, repLinear, act, LinearMap.coe_comp, comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply, Submodule.coe_subtype]
  rfl

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
  exact hvol.integral_comp hemb (fun y ↦ rep m d w y * rep m d w' y)

/-- **The reproducing kernel is invariant under the linear isometries.** -/
theorem sum_rep_mul_rep_smul {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ (eigenspace m d))
    (e : Eₘ ≃ₗᵢ[ℝ] Eₘ) (x y : Sₘ) :
    ∑ i, rep m d (b i) (e • x) * rep m d (b i) (e • y) =
      ∑ i, rep m d (b i) x * rep m d (b i) y := by
  classical
  rcases isEmpty_or_nonempty ι with hι | hι
  · simp
  have hon : Orthonormal ℝ (fun i ↦ act m d e (b i)) := by
    rw [orthonormal_iff_ite]
    intro i j
    rw [inner_act]
    exact orthonormal_iff_ite.mp b.orthonormal i j
  have hcard : Fintype.card ι = finrank ℝ (eigenspace m d) :=
    (finrank_eq_card_basis b.toBasis).symm
  let b' : OrthonormalBasis ι ℝ (eigenspace m d) :=
    (basisOfOrthonormalOfCardEqFinrank hon hcard).toOrthonormalBasis
      (by simpa only [coe_basisOfOrthonormalOfCardEqFinrank] using hon)
  have hb' (i : ι) : b' i = act m d e (b i) := by
    simp [b', coe_basisOfOrthonormalOfCardEqFinrank]
  rw [sum_rep_mul_rep m d b x y, ← sum_rep_mul_rep m d b' x y]
  simp only [hb', rep_act]

theorem nonempty_sphere : Nonempty Sₘ :=
  ⟨⟨EuclideanSpace.single 0 1, by simp⟩⟩

theorem volume_real_univ_pos : 0 < (volₘ).real univ := by
  have := nonempty_sphere m
  exact ENNReal.toReal_pos (Measure.IsOpenPosMeasure.open_pos univ isOpen_univ univ_nonempty)
    (measure_ne_top _ _)

/-- The sum of squares of an orthonormal basis is constant on the sphere. -/
theorem sum_rep_sq_eq {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ (eigenspace m d))
    (x y : Sₘ) : ∑ i, rep m d (b i) x ^ 2 = ∑ i, rep m d (b i) y ^ 2 := by
  obtain ⟨e, rfl⟩ := MulAction.exists_smul_eq (M := Eₘ ≃ₗᵢ[ℝ] Eₘ) x y
  simp only [sq]
  exact (sum_rep_mul_rep_smul m d b e x x).symm

/-- **The sum of squares of an orthonormal basis of an eigenspace is `N / Vol(Sᵐ)`.** -/
theorem sum_rep_sq {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ (eigenspace m d)) (x : Sₘ) :
    ∑ i, rep m d (b i) x ^ 2 = Fintype.card ι / (volₘ).real univ := by
  have hint : ∫ y, ∑ i, rep m d (b i) y ^ 2 ∂volₘ = Fintype.card ι := by
    rw [integral_finsetSum (f := fun i y ↦ rep m d (b i) y ^ 2) _ fun i _ ↦
      ((rep m d (b i)).continuous.pow 2).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)]
    have hi (i : ι) : ∫ y, rep m d (b i) y ^ 2 ∂volₘ = 1 := by
      simp only [sq]
      rw [← inner_eq_integral, real_inner_self_eq_norm_sq, b.orthonormal.1 i, one_pow]
    simp [hi]
  have hconst : ∫ y, ∑ i, rep m d (b i) y ^ 2 ∂volₘ =
      (volₘ).real univ * ∑ i, rep m d (b i) x ^ 2 := by
    rw [integral_congr_ae (Filter.Eventually.of_forall fun y ↦ sum_rep_sq_eq m d b y x),
      integral_const, smul_eq_mul]
  rw [eq_div_iff (volume_real_univ_pos m).ne', mul_comm, ← hconst, hint]

end TauCeti.Manifold.Eigenmap
