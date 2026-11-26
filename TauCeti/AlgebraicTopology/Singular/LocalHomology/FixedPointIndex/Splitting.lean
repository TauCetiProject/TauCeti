/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.LocalHomology.FixedPointIndex.Basic
public import TauCeti.LinearAlgebra.Determinant.RealEigenvalue

/-!
# The fixed-point index at a fixed point expanding along a factor and contracting across it

Let `V` and `W` be finite-dimensional real normed spaces, `q = dim V`. Consider a map of
`V × W` whose linearization at a fixed point is a product `S × N`, with `S` expanding along `V`
and `N` contracting along `W`, in the weak sense that `S` has no real eigenvalue in `[0, 1]` and
`N` no real eigenvalue `μ ≥ 1` (strict expansion and contraction of norms suffice, by
`Module.End.not_hasEigenvalue_of_lt_norm_apply` and
`Module.End.not_hasEigenvalue_of_norm_apply_lt`). Its local fixed-point index there is

`(-1)^q ε`,   `ε = sign det S`,

where `ε = ±1` records whether the expansion preserves or reverses the orientation of `V`
(`ContinuousMap.localFixedPointIndex_eq_neg_one_pow_mul_sign_det`). The same holds for the
fixed-point index of an affine map `z ↦ (S × N) z + v` on every open set containing its fixed
point (`ContinuousMap.fixedPointIndex_eq_neg_one_pow_mul_sign_det_of_forall_eq`). The index
`sign det (1 - (S × N))` of a nondegenerate fixed point
(`ContinuousMap.localFixedPointIndex_eq_sign_det`) is computed by
`LinearMap.sign_det_one_sub_prodMap_of_not_hasEigenvalue`.

This is the local contribution in the simplicial proof of the Lefschetz fixed-point theorem: near
the barycentre of a `q`-simplex `σ` that it carries over itself, Hopf's modification of a
simplicial approximation expands along `σ` and contracts transversally, so its fixed point there
has index `(-1)^q ε`, with `ε` the coefficient `±1` of `σ` in its image chain. In particular, for
a scalar expansion `S = c • 1` with `c ∉ [0, 1]` the index is `(-1)^q (sign c)^q`
(`ContinuousMap.fixedPointIndex_eq_of_forall_eq_smul_prodMap`); a reflection, `c < 0`, has index
`1` in every dimension (`ContinuousMap.fixedPointIndex_eq_one_of_forall_eq_smul_prodMap`). So the
reflected `1`-simplex, with `ε = -1`, has index `+1`, while an expansion of the `1`-simplex
preserving its orientation has index `-1`.

## Main results

* `ContinuousMap.localFixedPointIndex_eq_neg_one_pow_mul_sign_det`: the local index
  `(-1)^q sign det S` at a fixed point with linearization `S × N`.
* `ContinuousMap.fixedPointIndex_eq_neg_one_pow_mul_sign_det_of_forall_eq`: the index of the
  affine map `z ↦ (S × N) z + v`.
* `ContinuousMap.fixedPointIndex_eq_of_forall_eq_smul_prodMap`,
  `ContinuousMap.fixedPointIndex_eq_one_of_forall_eq_smul_prodMap`: scalar expansions and
  reflections.

## References

* A. Dold, *Lectures on Algebraic Topology*, Springer, 1972, Chapter VII, §5 and §6 (the
  fixed-point index and the Lefschetz–Hopf theorem).
* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 2.C (the Lefschetz fixed-point theorem by simplicial approximation).
-/

public section

open Module Set Topology TopologicalSpace

namespace ContinuousMap

variable {V W : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] {U : Opens (V × W)}
  {S : V →L[ℝ] V} {N : W →L[ℝ] W}

/-- `sign det (1 - (S × N)) = (-1)^q sign det S` for the continuous linear maps `S` and `N`, read
through their underlying linear maps from
`LinearMap.sign_det_one_sub_prodMap_of_not_hasEigenvalue`. -/
private theorem sign_det_one_sub_prodMap
    (hS : ∀ μ ∈ Icc (0 : ℝ) 1, ¬ Module.End.HasEigenvalue (S : Module.End ℝ V) μ)
    (hN : ∀ μ : ℝ, 1 ≤ μ → ¬ Module.End.HasEigenvalue (N : Module.End ℝ W) μ) :
    SignType.sign (1 - S.prodMap N).det = (-1) ^ finrank ℝ V * SignType.sign S.det := by
  rw [ContinuousLinearMap.det, ContinuousLinearMap.det, ContinuousLinearMap.toLinearMap_sub,
    ContinuousLinearMap.toLinearMap_one, ContinuousLinearMap.coe_prodMap]
  exact LinearMap.sign_det_one_sub_prodMap_of_not_hasEigenvalue hS hN

/-- Under the hypotheses of `sign_det_one_sub_prodMap`, `1 - (S × N)` is invertible: `S` has no
eigenvalue `0`, so `det S ≠ 0`. -/
private theorem det_one_sub_prodMap_ne_zero
    (hS : ∀ μ ∈ Icc (0 : ℝ) 1, ¬ Module.End.HasEigenvalue (S : Module.End ℝ V) μ)
    (hN : ∀ μ : ℝ, 1 ≤ μ → ¬ Module.End.HasEigenvalue (N : Module.End ℝ W) μ) :
    (1 - S.prodMap N).det ≠ 0 := by
  have hdet : S.det ≠ 0 :=
    ((LinearMap.not_hasEigenvalue_zero_tfae (S : Module.End ℝ V)).out 1 4).mp
      (hS 0 ⟨le_rfl, zero_le_one⟩)
  rw [← sign_ne_zero, sign_det_one_sub_prodMap hS hN]
  simp [hdet]

/-- **The local fixed-point index at an expanding-contracting fixed point.** If `f : U → V × W`
agrees near its fixed point `x` with a map differentiable at `x` with derivative `S × N`, where `S`
has no real eigenvalue in `[0, 1]` and `N` no real eigenvalue `μ ≥ 1`, then the local fixed-point
index of `f` at `x` is `(-1)^q sign det S`, with `q = dim V`. -/
theorem localFixedPointIndex_eq_neg_one_pow_mul_sign_det {f : C(U, V × W)} {x : U} (hx : f x = x)
    {φ : V × W → V × W} (hφ : ∀ᶠ z : U in 𝓝 x, φ z = f z) (hd : HasFDerivAt φ (S.prodMap N) x)
    (hS : ∀ μ ∈ Icc (0 : ℝ) 1, ¬ Module.End.HasEigenvalue (S : Module.End ℝ V) μ)
    (hN : ∀ μ : ℝ, 1 ≤ μ → ¬ Module.End.HasEigenvalue (N : Module.End ℝ W) μ) :
    f.localFixedPointIndex x = (-1) ^ finrank ℝ V * SignType.sign S.det := by
  rw [f.localFixedPointIndex_eq_sign_det hx hφ hd (det_one_sub_prodMap_ne_zero hS hN),
    sign_det_one_sub_prodMap hS hN]
  simp

/-- **The fixed-point index of an expanding-contracting affine map.** If `f : U → V × W` is the
restriction of the affine map `z ↦ (S × N) z + v`, where `S` has no real eigenvalue in `[0, 1]`
and `N` no real eigenvalue `μ ≥ 1`, and its fixed point `x` lies in `U`, then the fixed-point
index of `f` is `(-1)^q sign det S`, with `q = dim V`. -/
theorem fixedPointIndex_eq_neg_one_pow_mul_sign_det_of_forall_eq {f : C(U, V × W)} {v x : V × W}
    (hx : x ∈ U) (hAx : S.prodMap N x + v = x) (hf : ∀ z : U, f z = S.prodMap N z + v)
    (hS : ∀ μ ∈ Icc (0 : ℝ) 1, ¬ Module.End.HasEigenvalue (S : Module.End ℝ V) μ)
    (hN : ∀ μ : ℝ, 1 ≤ μ → ¬ Module.End.HasEigenvalue (N : Module.End ℝ W) μ) :
    f.fixedPointIndex = (-1) ^ finrank ℝ V * SignType.sign S.det := by
  rw [f.fixedPointIndex_eq_sign_det_of_forall_eq hx hAx hf (det_one_sub_prodMap_ne_zero hS hN),
    sign_det_one_sub_prodMap hS hN]
  simp

/-- **Scalar expansions.** If `f : U → V × W` is the restriction of the affine map
`z ↦ (c • z.1, N z.2) + v` with `c ∉ [0, 1]`, where `N` has no real eigenvalue `μ ≥ 1`, and its
fixed point lies in `U`, then the fixed-point index of `f` is `(-1)^q (sign c)^q`: `-1` to the
power `q` for `c > 1`, and `1` for `c < 0`. -/
theorem fixedPointIndex_eq_of_forall_eq_smul_prodMap {f : C(U, V × W)} {c : ℝ} (hc : c ∉ Icc 0 1)
    {v x : V × W} (hx : x ∈ U) (hAx : (c • (1 : V →L[ℝ] V)).prodMap N x + v = x)
    (hf : ∀ z : U, f z = (c • (1 : V →L[ℝ] V)).prodMap N z + v)
    (hN : ∀ μ : ℝ, 1 ≤ μ → ¬ Module.End.HasEigenvalue (N : Module.End ℝ W) μ) :
    f.fixedPointIndex = (-1) ^ finrank ℝ V * (SignType.sign c : ℤ) ^ finrank ℝ V := by
  have hS : ∀ μ ∈ Icc (0 : ℝ) 1,
      ¬ Module.End.HasEigenvalue ((c • (1 : V →L[ℝ] V) : V →L[ℝ] V) : Module.End ℝ V) μ := by
    intro μ hμ h
    obtain ⟨u, hu⟩ := h.exists_hasEigenvector
    have hcu : c • u = μ • u := by simpa using Module.End.mem_eigenspace_iff.mp hu.1
    exact hc (smul_left_injective ℝ hu.2 hcu ▸ hμ)
  rw [fixedPointIndex_eq_neg_one_pow_mul_sign_det_of_forall_eq hx hAx hf hS hN,
    ContinuousLinearMap.det, ContinuousLinearMap.toLinearMap_smul, LinearMap.det_smul,
    ContinuousLinearMap.toLinearMap_one, map_one, mul_one, sign_pow]
  simp

/-- **Reflections have index one.** If `f : U → V × W` is the restriction of the affine map
`z ↦ (c • z.1, N z.2) + v` with `c < 0`, where `N` has no real eigenvalue `μ ≥ 1`, and its fixed
point lies in `U`, then the fixed-point index of `f` is `1`, whatever the dimension of `V`. For
`V = ℝ` this is the reflected `1`-simplex: its expansion reverses the orientation, `ε = -1`, and
the index is `(-1) ε = 1`. -/
theorem fixedPointIndex_eq_one_of_forall_eq_smul_prodMap {f : C(U, V × W)} {c : ℝ} (hc : c < 0)
    {v x : V × W} (hx : x ∈ U) (hAx : (c • (1 : V →L[ℝ] V)).prodMap N x + v = x)
    (hf : ∀ z : U, f z = (c • (1 : V →L[ℝ] V)).prodMap N z + v)
    (hN : ∀ μ : ℝ, 1 ≤ μ → ¬ Module.End.HasEigenvalue (N : Module.End ℝ W) μ) :
    f.fixedPointIndex = 1 := by
  rw [fixedPointIndex_eq_of_forall_eq_smul_prodMap (fun h ↦ hc.not_ge h.1) hx hAx hf hN,
    sign_neg hc, ← mul_pow]
  simp

end ContinuousMap
