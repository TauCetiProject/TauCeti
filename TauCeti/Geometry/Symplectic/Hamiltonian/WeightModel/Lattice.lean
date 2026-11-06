/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.WeightModel.Basic
public import TauCeti.Geometry.Toric.Algebraic.Lattice
public import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Orbits, fixed points and integral weights of the weight model

Let `α : ι → StrongDual ℝ 𝔱` be weights on the Lie algebra `𝔱` of a torus, acting on
`ℂ^ι = EuclideanSpace ℝ ι × EuclideanSpace ℝ ι` by `ξ • z = (exp(i α_j(ξ)) z_j)_j`
(`TauCeti.weightRotation`), with moment map `μ(z) = -½ Σ_j |z_j|² α_j`
(`TauCeti.weightMomentMap`). This file proves the global orbit and fixed-point structure of this
local model, and its dependence on the period lattice of the torus.

**Orbits and fixed points.** The rotation by angles `θ` is the identity exactly when every `θ_j`
lies in `2πℤ`. The full torus `(ℝ / 2πℤ)^ι` moves `z` to `w` exactly when `|z_j| = |w_j|` for every
`j`. A point is fixed by all of `𝔱` exactly when it vanishes along the nonzero weights. When the
weights are linearly independent, as for the weights dual to a lattice basis below:

* the moment map determines the moduli `|z_j|`, so every fibre of `μ` is a single orbit of `𝔱`;
* the only fixed point is the origin, the only point mapped to the apex `0` of the moment cone;
* the apex is an extreme point of the moment image.

Some such hypothesis is needed for the apex to be a vertex: finitely many dependent weights can
span a cone containing a line, so that `0` is not an extreme point of the image, or even all of
`𝔱*`, so that `0` is an interior point.

**Integral weights.** Let `i : N →+ 𝔱` be an integral lattice (`TauCeti.Toric.IsIntegralLattice`),
so that `2π i(N)` is the period lattice of the torus `𝔱 / 2π i(N)`. The action of `𝔱` on `ℂ^ι`
descends to this torus exactly when every weight takes integer values on `i(N)`, that is, when
every weight is the real extension of an integral character of `N`.

**Weights forming a lattice basis.** Suppose finally that the weights are dual to a `ℤ`-basis `b`
of `N`: `α_j(i n)` is the `j`-th coordinate of `n` in `b`. This is the local model of a symplectic
toric manifold at a fixed point. Then:

* `μ(z)` paired with `i(b_k)` is `-½ |z_k|²`, and the image of `μ` is the simplicial cone
  `{ν | ν(i(b_k)) ≤ 0 for all k}`;
* the stabilizer of `z` in `𝔱` is `2π i(N) + span{i(b_k) | z_k = 0}`, the preimage of the subtorus
  spanned by the normals `i(b_k)` of the facets `ν(i(b_k)) = 0` containing `μ(z)`;
* the torus acts effectively, and it acts freely at `z` exactly when `μ(z)` lies in the open cone
  `{ν | ν(i(b_k)) < 0 for all k}`.

## Main results

* `TauCeti.weightRotation_eq_id_iff`: the kernel of the rotation action.
* `TauCeti.exists_weightRotation_apply_eq_iff`: the orbits of the full rotation torus.
* `TauCeti.forall_weightRotation_apply_eq_self_iff`: the fixed points of the action of `𝔱`.
* `TauCeti.weightMomentMap_eq_weightMomentMap_iff_exists_weightRotation`: for linearly independent
  weights, the fibres of the moment map are orbits of `𝔱`.
* `TauCeti.forall_weightRotation_apply_eq_self_iff_weightMomentMap_eq_zero`,
  `TauCeti.zero_mem_extremePoints_range_weightMomentMap`: for linearly independent weights, the
  fixed points are the preimage of the apex, which is an extreme point of the image.
* `TauCeti.forall_weightRotation_two_pi_smul_eq_id_iff`: the action descends to the torus
  `𝔱 / 2π i(N)` exactly when the weights are integral.
* `TauCeti.weightRotation_apply_eq_self_iff_of_basis`: stabilizers for weights dual to a lattice
  basis.
* `TauCeti.weightRotation_apply_eq_self_iff_of_basis_weightMomentMap`: the stabilizer of `z` is
  determined by the facets of the moment cone through `μ(z)`.
* `TauCeti.range_weightMomentMap_of_basis`: the image is the simplicial cone of the basis.
* `TauCeti.weightRotation_eq_id_iff_of_basis`,
  `TauCeti.forall_weightRotation_apply_eq_self_imp_iff_of_basis`: the torus acts effectively, and
  freely exactly over the open cone.

## References

* Victor Guillemin and Shlomo Sternberg, *Convexity properties of the moment mapping*, Invent.
  Math. 67 (1982), Section 2.
* Thomas Delzant, *Hamiltoniens périodiques et images convexes de l'application moment*, Bull.
  Soc. Math. France 116 (1988), 315–339.
* Ana Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Math. 1764, Springer
  (2001), Sections 27–29.
-/

public section

noncomputable section

namespace TauCeti

open Real

variable {ι : Type*} [Fintype ι]

/-! ### Orbits of the rotation torus -/

/-- **The kernel of the rotation action.** The rotation by the angles `θ` is the identity of
`ℂ^ι` exactly when every `θ_j` lies in `2πℤ`. -/
theorem weightRotation_eq_id_iff (θ : ι → ℝ) :
    weightRotation θ = ContinuousLinearMap.id ℝ _ ↔ ∀ j, ∃ k : ℤ, k * (2 * π) = θ j := by
  refine ⟨fun h j ↦ ?_, fun h ↦ ContinuousLinearMap.ext fun x ↦
    (weightRotation_apply_eq_self_iff θ x).2 fun j _ ↦ h j⟩
  have hx : weightRotation θ (WithLp.toLp 2 fun _ ↦ (1 : ℝ), 0) = (WithLp.toLp 2 fun _ ↦ 1, 0) := by
    rw [h, ContinuousLinearMap.id_apply]
  exact (weightRotation_apply_eq_self_iff θ _).1 hx j (Or.inl (by simp))

/-- **Orbits of the rotation torus.** Some rotation of `ℂ^ι` carries `z` to `w` exactly when
`|z_j| = |w_j|` for every `j`. -/
theorem exists_weightRotation_apply_eq_iff (x y : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) :
    (∃ θ, weightRotation θ x = y) ↔ ∀ j, x.1 j ^ 2 + x.2 j ^ 2 = y.1 j ^ 2 + y.2 j ^ 2 := by
  constructor
  · rintro ⟨θ, rfl⟩ j
    simp only [weightRotation_apply_fst, weightRotation_apply_snd]
    linear_combination -(x.1 j ^ 2 + x.2 j ^ 2) * sin_sq_add_cos_sq (θ j)
  · intro h
    -- In each coordinate, rotate `q + i p` by the difference of the arguments of the two points.
    have hrot (j : ι) : ∃ θ : ℝ, cos θ * x.1 j - sin θ * x.2 j = y.1 j ∧
        sin θ * x.1 j + cos θ * x.2 j = y.2 j := by
      set z : ℂ := ⟨x.1 j, x.2 j⟩
      set w : ℂ := ⟨y.1 j, y.2 j⟩
      have hzw : ‖z‖ = ‖w‖ := by
        rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), Complex.sq_norm, Complex.sq_norm,
          Complex.normSq_mk, Complex.normSq_mk]
        linear_combination h j
      have hc := cos_add (w.arg - z.arg) z.arg
      have hs := sin_add (w.arg - z.arg) z.arg
      rw [sub_add_cancel] at hc hs
      refine ⟨w.arg - z.arg, ?_, ?_⟩
      · rw [show x.1 j = z.re from rfl, show x.2 j = z.im from rfl, show y.1 j = w.re from rfl,
          ← Complex.norm_mul_cos_arg z, ← Complex.norm_mul_sin_arg z,
          ← Complex.norm_mul_cos_arg w, ← hzw, hc]
        ring
      · rw [show x.1 j = z.re from rfl, show x.2 j = z.im from rfl, show y.2 j = w.im from rfl,
          ← Complex.norm_mul_cos_arg z, ← Complex.norm_mul_sin_arg z,
          ← Complex.norm_mul_sin_arg w, ← hzw, hs]
        ring
    choose θ hθ using hrot
    exact ⟨θ, by ext j <;> simp [hθ]⟩

variable {𝔱 : Type*} [NormedAddCommGroup 𝔱] [NormedSpace ℝ 𝔱]

/-- **Fixed points of the weight action.** A point of `ℂ^ι` is fixed by the action of every
`ξ ∈ 𝔱` exactly when its coordinates `z_j` vanish along the nonzero weights `α_j`. -/
theorem forall_weightRotation_apply_eq_self_iff (α : ι → StrongDual ℝ 𝔱)
    (x : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) :
    (∀ ξ, weightRotation (fun j ↦ α j ξ) x = x) ↔ ∀ j, α j ≠ 0 → x.1 j = 0 ∧ x.2 j = 0 := by
  simp only [weightRotation_apply_eq_self_iff]
  constructor
  · intro h j hj
    by_contra hx
    obtain ⟨η, hη⟩ : ∃ η, α j η ≠ 0 := by
      by_contra! H
      exact hj (ContinuousLinearMap.ext H)
    -- The element `ξ = (π / α_j(η)) η` rotates the `j`-th coordinate by the angle `π`.
    obtain ⟨k, hk⟩ := h ((π / α j η) • η) j (by tauto)
    rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hη] at hk
    have h2k : ((2 * k : ℤ) : ℝ) = (1 : ℤ) :=
      mul_right_cancel₀ pi_ne_zero (by push_cast; linear_combination hk)
    have := Int.cast_injective h2k
    omega
  · intro h ξ j hj
    by_cases hα : α j = 0
    · exact ⟨0, by simp [hα]⟩
    · exact absurd (h j hα) (by tauto)

/-! ### Linearly independent weights -/

/-- For linearly independent weights, the moment map determines the moduli `|z_j|`: two points of
`ℂ^ι` have the same moment image exactly when `|z_j| = |w_j|` for every `j`. -/
theorem weightMomentMap_eq_weightMomentMap_iff {α : ι → StrongDual ℝ 𝔱}
    (hα : LinearIndependent ℝ α) (x y : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) :
    weightMomentMap α x = weightMomentMap α y ↔
      ∀ j, x.1 j ^ 2 + x.2 j ^ 2 = y.1 j ^ 2 + y.2 j ^ 2 := by
  refine ⟨fun h j ↦ ?_, fun h ↦ ?_⟩
  · have hsum : ∑ j, ((-(1 / 2) * (x.1 j ^ 2 + x.2 j ^ 2)) - (-(1 / 2) * (y.1 j ^ 2 + y.2 j ^ 2)))
        • α j = 0 := by
      rw [Finset.sum_congr rfl fun j _ ↦ sub_smul _ _ (α j), Finset.sum_sub_distrib,
        ← weightMomentMap_def, ← weightMomentMap_def, h, sub_self]
    linarith [Fintype.linearIndependent_iff.1 hα _ hsum j]
  · simp only [weightMomentMap_def, h]

/-- **Fibres of the moment map are orbits.** For linearly independent weights, two points of
`ℂ^ι` have the same moment image exactly when the action of some `ξ ∈ 𝔱` carries one to the
other. -/
theorem weightMomentMap_eq_weightMomentMap_iff_exists_weightRotation {α : ι → StrongDual ℝ 𝔱}
    (hα : LinearIndependent ℝ α) (x y : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) :
    weightMomentMap α x = weightMomentMap α y ↔ ∃ ξ, weightRotation (fun j ↦ α j ξ) x = y := by
  refine ⟨fun h ↦ ?_, fun ⟨ξ, hξ⟩ ↦ hξ ▸ (weightMomentMap_weightRotation α _ x).symm⟩
  obtain ⟨θ, rfl⟩ := (exists_weightRotation_apply_eq_iff x y).2
    ((weightMomentMap_eq_weightMomentMap_iff hα x y).1 h)
  -- Linearly independent functionals take every family of values `θ` simultaneously.
  have hli : LinearIndependent ℝ fun j ↦ ⇑(α j) :=
    Fintype.linearIndependent_iff.2 fun g hg ↦ Fintype.linearIndependent_iff.1 hα g
      (ContinuousLinearMap.ext fun ξ ↦ by simpa using congrFun hg ξ)
  have hθ : θ ∈ Submodule.span ℝ (Set.range (flip fun j ↦ ⇑(α j))) := by
    rw [span_flip_eq_top_iff_linearIndependent.2 hli]
    trivial
  let A : 𝔱 →ₗ[ℝ] ι → ℝ := LinearMap.pi fun j ↦ (α j : 𝔱 →ₗ[ℝ] ℝ)
  have hA : Set.range (flip fun j ↦ ⇑(α j)) = (LinearMap.range A : Set (ι → ℝ)) := by
    ext v
    simp [A, flip, funext_iff]
  rw [hA, Submodule.span_eq] at hθ
  obtain ⟨ξ, hξ⟩ := hθ
  exact ⟨ξ, by rw [← hξ]; rfl⟩

/-- For linearly independent weights, the origin is the only point of `ℂ^ι` mapped to the apex
`0` of the moment cone. -/
theorem weightMomentMap_eq_zero_iff {α : ι → StrongDual ℝ 𝔱} (hα : LinearIndependent ℝ α)
    (x : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) : weightMomentMap α x = 0 ↔ x = 0 := by
  rw [← weightMomentMap_zero α, weightMomentMap_eq_weightMomentMap_iff hα]
  simp only [Prod.fst_zero, Prod.snd_zero, PiLp.zero_apply, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, add_zero, Prod.ext_iff, PiLp.ext_iff]
  refine ⟨fun h ↦ ⟨fun j ↦ ?_, fun j ↦ ?_⟩, fun h j ↦ by simp [h.1 j, h.2 j]⟩ <;>
    nlinarith [h j, sq_nonneg (x.1 j), sq_nonneg (x.2 j)]

/-- **Fixed points lie over the apex.** For linearly independent weights, a point of `ℂ^ι` is
fixed by the whole action of `𝔱` exactly when its moment image is the apex `0` of the moment
cone, and then it is the origin. -/
theorem forall_weightRotation_apply_eq_self_iff_weightMomentMap_eq_zero
    {α : ι → StrongDual ℝ 𝔱} (hα : LinearIndependent ℝ α)
    (x : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) :
    (∀ ξ, weightRotation (fun j ↦ α j ξ) x = x) ↔ weightMomentMap α x = 0 := by
  rw [forall_weightRotation_apply_eq_self_iff, weightMomentMap_eq_zero_iff hα]
  simp only [fun j ↦ hα.ne_zero j, ne_eq, not_false_eq_true, forall_const, Prod.ext_iff,
    PiLp.ext_iff, Prod.fst_zero, Prod.snd_zero, PiLp.zero_apply]
  exact ⟨fun h ↦ ⟨fun j ↦ (h j).1, fun j ↦ (h j).2⟩, fun h j ↦ ⟨h.1 j, h.2 j⟩⟩

/-- **The apex is a vertex.** For linearly independent weights, the apex `0` of the moment cone
is an extreme point of the image of the moment map. -/
theorem zero_mem_extremePoints_range_weightMomentMap {α : ι → StrongDual ℝ 𝔱}
    (hα : LinearIndependent ℝ α) :
    (0 : StrongDual ℝ 𝔱) ∈ Set.extremePoints ℝ (Set.range (weightMomentMap α)) := by
  refine mem_extremePoints_iff_left.2 ⟨⟨0, weightMomentMap_zero α⟩, ?_⟩
  rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ ⟨s, t, hs, ht, -, hst⟩
  -- The coefficients of `s μ(x) + t μ(y)` in the independent weights all vanish.
  have hsum : ∑ j, (s * (-(1 / 2) * (x.1 j ^ 2 + x.2 j ^ 2)) +
      t * (-(1 / 2) * (y.1 j ^ 2 + y.2 j ^ 2))) • α j = 0 := by
    rw [Finset.sum_congr rfl fun j _ ↦ (add_smul _ _ (α j)).trans
        (congrArg₂ (· + ·) (mul_smul _ _ _) (mul_smul _ _ _)), Finset.sum_add_distrib,
      ← Finset.smul_sum, ← Finset.smul_sum, ← weightMomentMap_def, ← weightMomentMap_def, hst]
  have hx (j : ι) : x.1 j ^ 2 + x.2 j ^ 2 = 0 := by
    have hc := Fintype.linearIndependent_iff.1 hα _ hsum j
    have hx : 0 ≤ s * (x.1 j ^ 2 + x.2 j ^ 2) := by positivity
    have hy : 0 ≤ t * (y.1 j ^ 2 + y.2 j ^ 2) := by positivity
    exact (mul_eq_zero.1 (by linarith : s * (x.1 j ^ 2 + x.2 j ^ 2) = 0)).resolve_left hs.ne'
  rw [← weightMomentMap_zero α, weightMomentMap_eq_weightMomentMap_iff hα]
  simpa using hx

/-! ### Integral weights -/

section Integral

variable {N : Type*} [AddCommGroup N] {i : N →+ 𝔱}

/-- The action of `2π v` fixes `z` exactly when the weights along the nonzero coordinates of `z`
take integer values at `v`. -/
theorem weightRotation_two_pi_smul_apply_eq_self_iff (α : ι → StrongDual ℝ 𝔱) (v : 𝔱)
    (x : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) :
    weightRotation (fun j ↦ α j ((2 * π) • v)) x = x ↔
      ∀ j, (x.1 j ≠ 0 ∨ x.2 j ≠ 0) → ∃ k : ℤ, α j v = k := by
  rw [weightRotation_apply_eq_self_iff]
  refine forall₂_congr fun j _ ↦ exists_congr fun k ↦ ?_
  rw [map_smul, smul_eq_mul, mul_comm (2 * π), mul_left_inj' two_pi_pos.ne', eq_comm]

/-- **Integral weights.** For an integral lattice `i : N →+ 𝔱`, the action of `𝔱` on `ℂ^ι`
descends to the torus `𝔱 / 2π i(N)`, that is, `2π i(n)` acts trivially for every `n : N`, exactly
when every weight is the real extension of an integral character of `N`. -/
theorem forall_weightRotation_two_pi_smul_eq_id_iff (h : Toric.IsIntegralLattice i)
    (α : ι → StrongDual ℝ 𝔱) :
    (∀ n, weightRotation (fun j ↦ α j ((2 * π) • i n)) = ContinuousLinearMap.id ℝ _) ↔
      ∀ j, ∃ m : N →+ ℤ, h.realCharacter m = (α j : 𝔱 →ₗ[ℝ] ℝ) := by
  simp only [h.exists_realCharacter_eq_iff, ContinuousLinearMap.coe_coe]
  constructor
  · intro hn j n
    refine (weightRotation_two_pi_smul_apply_eq_self_iff α (i n) (WithLp.toLp 2 fun _ ↦ 1, 0)).1
      ?_ j (Or.inl (by simp))
    rw [hn, ContinuousLinearMap.id_apply]
  · exact fun hα n ↦ ContinuousLinearMap.ext fun x ↦
      (weightRotation_two_pi_smul_apply_eq_self_iff α (i n) x).2 fun j _ ↦ hα j n

/-! ### Weights dual to a lattice basis -/

variable (h : Toric.IsIntegralLattice i) (b : Module.Basis ι ℤ N) {α : ι → StrongDual ℝ 𝔱}
  (hα : ∀ j n, α j (i n) = b.coord j n)
include hα

omit [Fintype ι] in
/-- The weight `α_j` dual to a lattice basis `b` pairs with `i(b_j)` to `1`. -/
private theorem apply_basis_self_of_basis (j : ι) : α j (i (b j)) = 1 := by
  rw [hα, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_eq_same, Int.cast_one]

omit [Fintype ι] in
/-- The weight `α_j` dual to a lattice basis `b` vanishes on `i(b_k)` for `k ≠ j`. -/
private theorem apply_basis_of_basis_of_ne {j k : ι} (hjk : j ≠ k) : α j (i (b k)) = 0 := by
  rw [hα, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_eq_of_ne hjk,
    Int.cast_zero]

/-- For weights dual to a lattice basis `b`, the moment image of `z` pairs with `i(b_k)` to
`-½ |z_k|²`. -/
theorem weightMomentMap_apply_basis (x : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) (k : ι) :
    weightMomentMap α x (i (b k)) = -(1 / 2) * (x.1 k ^ 2 + x.2 k ^ 2) := by
  rw [weightMomentMap_apply, Finset.sum_eq_single k
    (fun j _ hj ↦ by rw [apply_basis_of_basis_of_ne b hα hj, zero_mul]) (by simp),
    apply_basis_self_of_basis b hα, one_mul]

/-- For weights dual to a lattice basis `b`, the moment image of `z` lies on the facet
`ν(i(b_k)) = 0` of the moment cone exactly when the coordinate `z_k` vanishes. -/
theorem weightMomentMap_apply_basis_eq_zero_iff (x : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι)
    (k : ι) : weightMomentMap α x (i (b k)) = 0 ↔ x.1 k = 0 ∧ x.2 k = 0 := by
  rw [weightMomentMap_apply_basis b hα]
  constructor
  · intro hk
    constructor <;> nlinarith [sq_nonneg (x.1 k), sq_nonneg (x.2 k)]
  · rintro ⟨h1, h2⟩
    simp [h1, h2]

include h in
/-- For weights dual to a lattice basis `b`, every `ξ ∈ 𝔱` expands in the real basis `i(b_k)`
with coefficients `α_k(ξ)`. -/
theorem sum_apply_smul_of_basis (ξ : 𝔱) : ∑ k, α k ξ • i (b k) = ξ := by
  let B := h.isBaseChange.basis b
  have hB (k : ι) : B k = i (b k) := by simpa using h.isBaseChange.basis_apply b k
  have hcoord (k : ι) : (α k : 𝔱 →ₗ[ℝ] ℝ) = B.coord k :=
    B.ext fun j ↦ by
      rw [ContinuousLinearMap.coe_coe, Module.Basis.coord_apply, Module.Basis.repr_self, hB]
      by_cases hkj : k = j
      · rw [hkj, apply_basis_self_of_basis b hα, Finsupp.single_eq_same]
      · rw [apply_basis_of_basis_of_ne b hα hkj, Finsupp.single_eq_of_ne hkj]
  conv_rhs => rw [← B.sum_repr ξ]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [← hB, ← B.coord_apply, ← hcoord, ContinuousLinearMap.coe_coe]

omit [Fintype ι] in
/-- Weights dual to a lattice basis are linearly independent. -/
theorem linearIndependent_of_forall_apply_eq_coord [Finite ι] : LinearIndependent ℝ α := by
  have := Fintype.ofFinite ι
  refine Fintype.linearIndependent_iff.2 fun g hg k ↦ ?_
  have := congrArg (fun φ : StrongDual ℝ 𝔱 ↦ φ (i (b k))) hg
  simp only [_root_.sum_apply, FunLike.coe_smul, Pi.smul_apply, smul_eq_mul,
    zero_apply] at this
  rwa [Finset.sum_eq_single k (fun j _ hj ↦ by rw [apply_basis_of_basis_of_ne b hα hj, mul_zero])
    (by simp), apply_basis_self_of_basis b hα, mul_one] at this

include h in
/-- **Stabilizers for weights dual to a lattice basis.** The element `ξ ∈ 𝔱` fixes `z` exactly
when, modulo the period lattice `2π i(N)`, it lies in the span of the vectors `i(b_k)` for which
the coordinate `z_k` vanishes. -/
theorem weightRotation_apply_eq_self_iff_of_basis (ξ : 𝔱)
    (x : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) :
    weightRotation (fun j ↦ α j ξ) x = x ↔ ∃ n : N, ξ - (2 * π) • i n ∈
      Submodule.span ℝ ((fun k ↦ i (b k)) '' {k | x.1 k = 0 ∧ x.2 k = 0}) := by
  rw [weightRotation_apply_eq_self_iff]
  constructor
  · intro hfix
    choose! c hc using hfix
    -- Subtract `2π` times the lattice vector with coordinates `c` in the basis `b`.
    have hn (j : ι) : α j (i (b.equivFun.symm c)) = c j := by
      rw [hα, Module.Basis.coord_apply, ← Module.Basis.equivFun_apply,
        LinearEquiv.apply_symm_apply]
    refine ⟨b.equivFun.symm c, ?_⟩
    rw [← sum_apply_smul_of_basis h b hα (ξ - _)]
    refine Submodule.sum_mem _ fun k _ ↦ ?_
    by_cases hk : x.1 k = 0 ∧ x.2 k = 0
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, hk, rfl⟩)
    · rw [map_sub, map_smul, hn, smul_eq_mul, ← hc k (by tauto)]
      simp [mul_comm]
  · rintro ⟨n, hξ⟩ j hj
    -- `α_j` kills the span, since it kills every `i(b_k)` with `k ≠ j`.
    have hker : Submodule.span ℝ ((fun k ↦ i (b k)) '' {k | x.1 k = 0 ∧ x.2 k = 0}) ≤
        LinearMap.ker (α j : 𝔱 →ₗ[ℝ] ℝ) := by
      rw [Submodule.span_le]
      rintro _ ⟨k, hk, rfl⟩
      have hjk : j ≠ k := by
        rintro rfl
        rcases hk with ⟨h1, h2⟩
        tauto
      simp [apply_basis_of_basis_of_ne b hα hjk]
    have h0 := hker hξ
    simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, map_sub,
      map_smul, hα, smul_eq_mul] at h0
    exact ⟨b.coord j n, by linear_combination -h0⟩

include h in
/-- For weights dual to a lattice basis, the stabilizer of `z` in `𝔱` depends only on the face of
the moment cone containing `μ(z)`: it is the period lattice `2π i(N)` plus the span of the
`i(b_k)` for the facets `ν(i(b_k)) = 0` through `μ(z)`. -/
theorem weightRotation_apply_eq_self_iff_of_basis_weightMomentMap (ξ : 𝔱)
    (x : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) :
    weightRotation (fun j ↦ α j ξ) x = x ↔ ∃ n : N, ξ - (2 * π) • i n ∈
      Submodule.span ℝ ((fun k ↦ i (b k)) '' {k | weightMomentMap α x (i (b k)) = 0}) := by
  simp only [weightMomentMap_apply_basis_eq_zero_iff b hα]
  exact weightRotation_apply_eq_self_iff_of_basis h b hα ξ x

include h in
/-- **The torus acts freely on the open orthant.** For weights dual to a lattice basis, at a point
of `ℂ^ι` all of whose coordinates are nonzero, the stabilizer in `𝔱` is the period lattice
`2π i(N)`. -/
theorem weightRotation_apply_eq_self_iff_of_basis_of_forall_ne_zero
    {x : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι} (hx : ∀ k, x.1 k ≠ 0 ∨ x.2 k ≠ 0) (ξ : 𝔱) :
    weightRotation (fun j ↦ α j ξ) x = x ↔ ∃ n : N, ξ = (2 * π) • i n := by
  have hempty : {k | x.1 k = 0 ∧ x.2 k = 0} = ∅ :=
    Set.eq_empty_of_forall_notMem fun k ⟨h1, h2⟩ ↦ (hx k).elim (· h1) (· h2)
  simp only [weightRotation_apply_eq_self_iff_of_basis h b hα, hempty, Set.image_empty,
    Submodule.span_empty, Submodule.mem_bot, sub_eq_zero]

include h in
/-- **The torus acts effectively.** For weights dual to a lattice basis, `ξ ∈ 𝔱` acts trivially on
`ℂ^ι` exactly when it lies in the period lattice `2π i(N)`. -/
theorem weightRotation_eq_id_iff_of_basis (ξ : 𝔱) :
    weightRotation (fun j ↦ α j ξ) = ContinuousLinearMap.id ℝ _ ↔ ∃ n : N, ξ = (2 * π) • i n := by
  refine ⟨fun hid ↦ ?_, fun ⟨n, hn⟩ ↦ ContinuousLinearMap.ext fun x ↦
    (weightRotation_apply_eq_self_iff_of_basis h b hα ξ x).2 ⟨n, by simp [hn]⟩⟩
  refine (weightRotation_apply_eq_self_iff_of_basis_of_forall_ne_zero h b hα
    (x := (WithLp.toLp 2 fun _ ↦ 1, 0)) (fun k ↦ Or.inl (by simp)) ξ).1 ?_
  rw [hid, ContinuousLinearMap.id_apply]

include h in
/-- **The torus acts freely exactly over the open cone.** For weights dual to a lattice basis, the
stabilizer of `z` in `𝔱` is the period lattice `2π i(N)` exactly when `μ(z)` lies in the open cone
`{ν | ν(i(b_k)) < 0 for all k}`, that is, when every coordinate `z_k` is nonzero. -/
theorem forall_weightRotation_apply_eq_self_imp_iff_of_basis
    (x : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) :
    (∀ ξ, weightRotation (fun j ↦ α j ξ) x = x → ∃ n : N, ξ = (2 * π) • i n) ↔
      ∀ k, weightMomentMap α x (i (b k)) < 0 := by
  have hlt (k : ι) : weightMomentMap α x (i (b k)) < 0 ↔ x.1 k ≠ 0 ∨ x.2 k ≠ 0 := by
    rw [← not_and_or, ← weightMomentMap_apply_basis_eq_zero_iff b hα,
      weightMomentMap_apply_basis b hα]
    constructor
    · intro hk; linarith
    · intro hk; exact lt_of_le_of_ne (by nlinarith [sq_nonneg (x.1 k), sq_nonneg (x.2 k)]) hk
  simp only [hlt]
  refine ⟨fun hfree k ↦ ?_, fun hx ξ ↦
    (weightRotation_apply_eq_self_iff_of_basis_of_forall_ne_zero h b hα hx ξ).1⟩
  by_contra! hk
  -- The element `π i(b_k)` fixes `z`, but is not in the period lattice.
  have hmem : i (b k) ∈ Submodule.span ℝ ((fun k ↦ i (b k)) '' {k | x.1 k = 0 ∧ x.2 k = 0}) :=
    Submodule.subset_span ⟨k, hk, rfl⟩
  obtain ⟨n, hn⟩ := hfree (π • i (b k)) <|
    (weightRotation_apply_eq_self_iff_of_basis h b hα _ x).2
      ⟨0, by simpa using Submodule.smul_mem _ π hmem⟩
  have hk' := congrArg (α k) hn
  simp only [map_smul, apply_basis_self_of_basis b hα, smul_eq_mul, mul_one, hα] at hk'
  have h2 : (((2 * b.coord k n : ℤ)) : ℝ) = (1 : ℤ) :=
    mul_right_cancel₀ pi_ne_zero (by push_cast; linear_combination -hk')
  have := Int.cast_injective h2
  omega

include h in
/-- **The moment image is a simplicial cone.** For weights dual to a lattice basis `b`, the image
of the moment map is the cone `{ν | ν(i(b_k)) ≤ 0 for all k}` cut out by the facets
`ν(i(b_k)) = 0`. -/
theorem range_weightMomentMap_of_basis :
    Set.range (weightMomentMap α) = {ν | ∀ k, ν (i (b k)) ≤ 0} := by
  ext ν
  constructor
  · rintro ⟨x, rfl⟩ k
    rw [weightMomentMap_apply_basis b hα]
    nlinarith [sq_nonneg (x.1 k), sq_nonneg (x.2 k)]
  · intro hν
    refine ⟨(WithLp.toLp 2 fun k ↦ √(-2 * ν (i (b k))), 0), ?_⟩
    -- Both functionals agree on the real basis `i(b_k)` of `𝔱`.
    refine ContinuousLinearMap.ext fun ξ ↦ ?_
    rw [← sum_apply_smul_of_basis h b hα ξ, map_sum, map_sum]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [map_smul, map_smul, weightMomentMap_apply_basis b hα]
    simp only [PiLp.zero_apply]
    rw [Real.sq_sqrt (by linarith [hν k])]
    ring

end Integral

end TauCeti
