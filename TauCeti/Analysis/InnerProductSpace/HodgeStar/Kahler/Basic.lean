/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.ExteriorPower.Basic
public import TauCeti.Analysis.InnerProductSpace.HodgeStar.Isometry
public import TauCeti.Geometry.Symplectic.Complex.InnerProductSpace
public import TauCeti.Geometry.Symplectic.Complex.OrthonormalBasis
-- Private: orthonormal coordinates and the `4 × 4` determinant are used only in proofs.
import TauCeti.Analysis.InnerProductSpace.Orientation
import TauCeti.Analysis.InnerProductSpace.Orthonormal.Sum
import TauCeti.LinearAlgebra.ExteriorPower.Basic
import TauCeti.LinearAlgebra.ExteriorPower.Square
import TauCeti.LinearAlgebra.Matrix.Determinant.FinFour

/-!
# The Kähler two-vector of an orthogonal complex structure

Let `V` be a finite-dimensional real inner product space and `J` an almost complex structure on
`V` that is orthogonal, `⟪J v, J w⟫ = ⟪v, w⟫`. Its **Kähler form** `ω(v, w) = ⟪J v, w⟫`, so that
`⟪v, w⟫ = ω(v, J w)`, is identified through the inner product with the two-vector
`TauCeti.AlmostComplexStructure.kahlerForm J ∈ ⋀² V`, characterized by
`⟪ω, u ∧ w⟫ = ⟪J u, w⟫` (more generally `(⟪J u, w⟫ - ⟪J w, u⟫) / 2` without orthogonality), and
`‖ω‖² = dim V / 2`. In any adapted orthonormal basis `(b₀, J b₀, …, b_{2n-2}, J b_{2n-2})`, `J` is
orthogonal and `ω = ∑ j, b_{2j} ∧ b_{2j+1}` (in dimension four, `ω = e₁ ∧ e₂ + e₃ ∧ e₄`). The
endomorphism `J` acts on two-forms as a derivation `D_J (u ∧ w) = J u ∧ w + u ∧ J w`
(`exteriorPower.lieMap 2 J`), which is skew-adjoint and kills `ω`.

Conversely, if a two-vector `F` and an almost complex structure `J` satisfy
`⟪u, v⟫ = ⟪F, u ∧ J v⟫`, then `J` is the contraction `u ↦ u ⌟ F`
(`TauCeti.twoVectorContraction F`), so such a `J` is unique; it is orthogonal and `F` is its
Kähler two-vector.

In dimension four, for the complex orientation, the one in which unitary frames are positively
oriented, `ω` is self-dual, and on the self-dual two-forms
`Λ⁺ = ℝ ω ⊕ (ℝ ω)ᗮ` the operator `D_J / 2` is zero on `ω` and squares to `-1` on its
orthogonal complement: `D_J² η = 2 ⟪ω, η⟫ ω - 4 η`. This is the complex structure
`ρ ↦ ω_u × ρ`, `ω_u = ω / √2`, of the anti-`J`-invariant self-dual forms. On the
anti-self-dual two-forms `D_J` vanishes, so these are `J`-invariant. Finally the
self-dual part of `ξ ∧ J a - J ξ ∧ a` is `⟪ξ, a⟫ ω`; this is what makes the principal symbol of
the anti-self-dual deformation operator complex linear.

The Hodge-star and self-duality results in dimension four take a positively oriented
orthonormal basis `e` with
`J e₀ = e₁` and `J e₂ = e₃` as a witness that the orientation is the complex one; the
conclusions do not depend on the choice of such a frame. Once one witness exists, every unit
vector is the first vector of another (`exists_orthonormalBasis_apply_zero_eq`), so frame
computations at `e₀` hold at every unit vector.

## Main definitions

* `TauCeti.AlmostComplexStructure.kahlerForm J`: the Kähler two-vector `ω ∈ ⋀² V`.

## Main results

In the namespace `TauCeti.AlmostComplexStructure`:

* `inner_kahlerForm_ιMulti_eq_inv_two_mul_sub`: `⟪ω, u ∧ w⟫ = (⟪J u, w⟫ - ⟪J w, u⟫) / 2` for any
  almost complex structure `J`.
* `inner_apply_left`: an orthogonal `J` is skew-adjoint.
* `inner_kahlerForm_ιMulti`: `⟪ω, u ∧ w⟫ = ⟪J u, w⟫`.
* `sum_ιMulti_apply_eq_two_smul_kahlerForm`: `∑ᵢ bᵢ ∧ J bᵢ = 2 ω` in every orthonormal basis.
* `inner_kahlerForm_self`: `⟪ω, ω⟫ = dim V / 2`, so `‖ω‖² = 2` in dimension four
  (`norm_kahlerForm_sq_eq_two`).
* `norm_ιMulti_apply_sq`: `‖v ∧ J v‖² = ‖v‖⁴`.
* `lieMap_kahlerForm`: `D_J ω = 0`.
* `map_kahlerForm_of_isComplexLinearMap`: complex-linear isometries preserve `ω`.
* `lieMap_lieMap_lieMap`: `D_J³ = -4 D_J`, so `η + D_J² η / 4` is `J`-invariant
  (`lieMap_add_smul_lieMap_lieMap`).
* `inner_lieMap_lieMap_ιMulti`: `⟪D_J² η, u ∧ w⟫ = 2 (η(J u, J w) - η(u, w))`.
* `norm_lieMap_lieMap_le`: `‖D_J² η‖ ≤ 4 ‖η‖` for an orthogonal `J`.
* `lieMap_eq_zero_iff_forall_inner_ιMulti_apply`: `D_J η = 0` exactly when
  `η(J u, J w) = η(u, w)`.
* `toLinearMap_eq_twoVectorContraction`: a `J` with `⟪u, v⟫ = ⟪F, u ∧ J v⟫` is the
  contraction by `F`; it is orthogonal (`inner_apply_apply_of_inner_eq`) and `F` is its Kähler
  two-vector (`kahlerForm_eq_of_inner_eq`).
* `twoVectorContraction_kahlerForm`: for an orthogonal `J`, `twoVectorContraction J.kahlerForm`
  recovers `J.toLinearMap`.
* `kahlerForm_eq_sum_of_adapted`: in any adapted orthonormal basis in dimension `2 * n`,
  `ω = ∑ j, b_{2j} ∧ b_{2j+1}`.
* `repr_apply`: the coordinates of `J v` in a unitary frame.
* `kahlerForm_eq_ιMulti_add_ιMulti`: `ω = e₀ ∧ e₁ + e₂ ∧ e₃` in a unitary frame.
* `inner_ιMulti_of_antiinvariant`: the frame coordinates of an anti-`J`-invariant two-vector.
* `hodgeStar_kahlerForm`: `⋆ω = ω` for the complex orientation.
* `inner_kahlerForm_hodgeStar`: `⟪ω, ⋆F⟫ = ⟪ω, F⟫`.
* `exists_orthonormalBasis_apply_zero_eq`: every unit vector starts a positively oriented unitary
  frame.
* `inner_kahlerForm_eq_zero_of_hodgeStar_eq_neg`: `ω` is orthogonal to anti-self-dual forms.
* `lieMap_lieMap_of_hodgeStar_eq_self`:
  `D_J² η = 2 ⟪ω, η⟫ ω - 4 η` for self-dual `η`.
* `lieMap_of_hodgeStar_eq_neg`: `D_J η = 0` for anti-self-dual `η`.
* `ιMulti_sub_ιMulti_add_hodgeStar`: the self-dual part of `ξ ∧ J a - J ξ ∧ a` is `⟪ξ, a⟫ ω`.
* `hodgeStar_ιMulti_apply`: `⋆(x ∧ J x) = ‖x‖² ω - x ∧ J x` for the complex orientation.
* `eq_smul_kahlerForm_add_of_lieMap_eq_zero`: a `J`-invariant `η` is
  `(⟪ω, η⟫ / 2) ω + (η - ⋆η) / 2`; conversely, `D_J η = 0` when `η + ⋆η` is a multiple of `ω`
  (`lieMap_eq_zero_of_add_hodgeStar_eq_smul`).

The supporting norm-preservation and adapted-frame orthogonality/construction lemmas live in
`TauCeti.Geometry.Symplectic.Complex.InnerProductSpace` and
`TauCeti.Geometry.Symplectic.Complex.OrthonormalBasis`, respectively.

## References

* S. K. Donaldson and P. B. Kronheimer, *The Geometry of Four-Manifolds*, Oxford (1990).
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, Section 2.1.
-/

public section

noncomputable section

open Module exteriorPower
open scoped RealInnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

namespace TauCeti.AlmostComplexStructure

/-- The **Kähler form** of an almost complex structure `J` on a real inner product space, as a
two-vector: `ω = (1 / 2) ∑ᵢ bᵢ ∧ J bᵢ` for an orthonormal basis `b`. When `J` is orthogonal it
represents the two-form `ω(u, w) = ⟪J u, w⟫` (`inner_kahlerForm_ιMulti`), so it does not depend
on the basis. -/
def kahlerForm (J : AlmostComplexStructure V) : ⋀[ℝ]^2 V :=
  (2⁻¹ : ℝ) • ∑ i, ιMulti ℝ 2 ![stdOrthonormalBasis ℝ V i, J (stdOrthonormalBasis ℝ V i)]

/-- The Kähler two-vector is half the sum of `bᵢ ∧ J bᵢ` in the standard orthonormal basis. -/
theorem kahlerForm_def (J : AlmostComplexStructure V) :
    J.kahlerForm = (2⁻¹ : ℝ) • ∑ i,
      ιMulti ℝ 2 ![stdOrthonormalBasis ℝ V i, J (stdOrthonormalBasis ℝ V i)] := (rfl)

/-- For any almost complex structure `J` (not necessarily orthogonal), pairing `J.kahlerForm` with
`u ∧ w` evaluates the skew-symmetrization `(⟪J u, w⟫ - ⟪J w, u⟫) / 2`. -/
theorem inner_kahlerForm_ιMulti_eq_inv_two_mul_sub (J : AlmostComplexStructure V) (u w : V) :
    ⟪J.kahlerForm, ιMulti ℝ 2 ![u, w]⟫ = (2⁻¹ : ℝ) * (⟪J u, w⟫ - ⟪J w, u⟫) := by
  have hsum (x y : V) :
      ∑ i, ⟪stdOrthonormalBasis ℝ V i, x⟫ * ⟪J (stdOrthonormalBasis ℝ V i), y⟫ = ⟪J x, y⟫ := by
    calc ∑ i, ⟪stdOrthonormalBasis ℝ V i, x⟫ * ⟪J (stdOrthonormalBasis ℝ V i), y⟫
        = ⟪J (∑ i, ⟪stdOrthonormalBasis ℝ V i, x⟫ • stdOrthonormalBasis ℝ V i), y⟫ := by
          simp only [map_sum, map_smul, sum_inner, real_inner_smul_left]
      _ = ⟪J x, y⟫ := by rw [(stdOrthonormalBasis ℝ V).sum_repr' x]
  simp only [kahlerForm, real_inner_smul_left, sum_inner, inner_ιMulti_two,
    Finset.sum_sub_distrib, hsum]

/-! ### The derivation action of `J` on two-vectors -/

/-- `D_J² (u ∧ w) = 2 (J u ∧ J w) - 2 (u ∧ w)`. -/
theorem lieMap_lieMap_ιMulti (J : AlmostComplexStructure V) (u w : V) :
    lieMap 2 J.toLinearMap (lieMap 2 J.toLinearMap (ιMulti ℝ 2 ![u, w])) =
      (2 : ℝ) • ιMulti ℝ 2 ![J u, J w] - (2 : ℝ) • ιMulti ℝ 2 ![u, w] := by
  refine ext_inner_ιMulti_two fun a b ↦ ?_
  simp only [lieMap_two_apply_ιMulti, map_add, inner_add_left, inner_sub_left,
    real_inner_smul_left, inner_ιMulti_two, apply_apply, inner_neg_left]
  ring

/-- **`D_J³ = -4 D_J` on two-vectors.** Hence `D_J² / 4` is minus the projection onto the
anti-`J`-invariant two-vectors, the `-4`-eigenspace of `D_J²`, and `η + D_J² η / 4` is the
`J`-invariant part of `η`. -/
theorem lieMap_lieMap_lieMap (J : AlmostComplexStructure V) (η : ⋀[ℝ]^2 V) :
    lieMap 2 J.toLinearMap (lieMap 2 J.toLinearMap (lieMap 2 J.toLinearMap η)) =
      -(4 : ℝ) • lieMap 2 J.toLinearMap η := by
  set D := lieMap 2 J.toLinearMap
  have key : D ∘ₗ D ∘ₗ D = -(4 : ℝ) • D := by
    refine linearMap_ext_inner_ιMulti_two fun a b u w ↦ ?_
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, D]
    rw [lieMap_lieMap_ιMulti]
    simp only [map_sub, map_smul, lieMap_two_apply_ιMulti, inner_add_left, inner_sub_left,
      real_inner_smul_left, inner_ιMulti_two, apply_apply, inner_neg_left]
    ring
  exact LinearMap.congr_fun key η

/-- The two-form `η + D_J² η / 4` is `J`-invariant. -/
theorem lieMap_add_smul_lieMap_lieMap (J : AlmostComplexStructure V) (η : ⋀[ℝ]^2 V) :
    lieMap 2 J.toLinearMap
        (η + (4⁻¹ : ℝ) • lieMap 2 J.toLinearMap (lieMap 2 J.toLinearMap η)) = 0 := by
  rw [map_add, map_smul, lieMap_lieMap_lieMap, smul_smul]
  norm_num

section Orthogonal

variable {J : AlmostComplexStructure V} (hJ : ∀ v w, ⟪J v, J w⟫ = ⟪v, w⟫)
include hJ

omit [FiniteDimensional ℝ V] in
/-- An orthogonal almost complex structure is skew-adjoint, `⟪J v, w⟫ = -⟪v, J w⟫`. -/
theorem inner_apply_left (v w : V) : ⟪J v, w⟫ = -⟪v, J w⟫ :=
  J.bilinForm_apply_left_eq_neg_apply_right (g := innerₗ V) hJ v w

/-- In any orthonormal basis `b`, `⟪∑ᵢ bᵢ ∧ J bᵢ, u ∧ w⟫ = 2 ⟪J u, w⟫`. -/
private theorem inner_sum_ιMulti_apply {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ V)
    (u w : V) : ⟪∑ i, ιMulti ℝ 2 ![b i, J (b i)], ιMulti ℝ 2 ![u, w]⟫ = 2 * ⟪J u, w⟫ := by
  -- Expanding in the orthonormal basis `b`, each sum is `±⟪J u, w⟫`.
  have hsum (x y : V) : ∑ i, ⟪b i, x⟫ * ⟪J (b i), y⟫ = ⟪J x, y⟫ := by
    rw [inner_apply_left hJ x, ← b.sum_inner_mul_inner x (J y), ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [inner_apply_left hJ, real_inner_comm x]
    ring
  simp only [sum_inner, inner_ιMulti_two, Finset.sum_sub_distrib, hsum]
  rw [inner_apply_left hJ w u, real_inner_comm w (J u)]
  ring

/-- **The Kähler two-vector represents the Kähler form**: `⟪ω, u ∧ w⟫ = ⟪J u, w⟫`. -/
@[simp]
theorem inner_kahlerForm_ιMulti (u w : V) :
    ⟪J.kahlerForm, ιMulti ℝ 2 ![u, w]⟫ = ⟪J u, w⟫ := by
  rw [inner_kahlerForm_ιMulti_eq_inv_two_mul_sub, inner_apply_left hJ w u,
    real_inner_comm w (J u)]
  ring

/-- **The Kähler two-vector in any orthonormal basis**: `∑ᵢ bᵢ ∧ J bᵢ = 2 ω` for an orthogonal
`J`, as in the definition of `ω` through the standard orthonormal basis. -/
theorem sum_ιMulti_apply_eq_two_smul_kahlerForm {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ V) :
    ∑ i, ιMulti ℝ 2 ![b i, J (b i)] = (2 : ℝ) • J.kahlerForm :=
  ext_inner_ιMulti_two fun u w ↦ by
    rw [inner_sum_ιMulti_apply hJ, real_inner_smul_left, inner_kahlerForm_ιMulti hJ]

/-- `⟪ω, ω⟫ = dim V / 2`: in a unitary frame `ω = e₁ ∧ e₂ + e₃ ∧ e₄ + ⋯` is a sum of
`dim V / 2` orthonormal two-vectors. -/
theorem inner_kahlerForm_self : ⟪J.kahlerForm, J.kahlerForm⟫ = finrank ℝ V / 2 := by
  nth_rewrite 2 [kahlerForm]
  simp [inner_sum, real_inner_smul_right, inner_kahlerForm_ιMulti hJ, norm_apply hJ,
    div_eq_inv_mul]

/-- `‖ω‖² = dim V / 2`, the simp normal form of `inner_kahlerForm_self`. -/
@[simp]
theorem norm_kahlerForm_sq : ‖J.kahlerForm‖ ^ 2 = finrank ℝ V / 2 := by
  rw [← real_inner_self_eq_norm_sq, inner_kahlerForm_self hJ]

/-- `‖ω‖² = 2` in dimension four. -/
theorem norm_kahlerForm_sq_eq_two [Fact (finrank ℝ V = 4)] : ‖J.kahlerForm‖ ^ 2 = 2 := by
  rw [norm_kahlerForm_sq hJ, Fact.out (p := finrank ℝ V = 4)]
  norm_num

/-- `‖v ∧ J v‖² = ‖v‖⁴` for an orthogonal `J`, since `J v` is orthogonal to `v` and has the same
norm. -/
theorem norm_ιMulti_apply_sq (v : V) : ‖ιMulti ℝ 2 ![v, J v]‖ ^ 2 = ‖v‖ ^ 4 := by
  rw [← real_inner_self_eq_norm_sq, inner_ιMulti_two, hJ, real_inner_comm, inner_apply_self hJ,
    real_inner_self_eq_norm_sq]
  ring

/-- A complex-linear linear isometry equivalence between orthogonal almost complex inner product
spaces transports the Kähler two-vector. -/
theorem map_kahlerForm_of_isComplexLinearMap {V' : Type*} [NormedAddCommGroup V']
    [InnerProductSpace ℝ V'] [FiniteDimensional ℝ V'] {J' : AlmostComplexStructure V'}
    {f : V ≃ₗᵢ[ℝ] V'} (hfJ : IsComplexLinearMap J J' f.toLinearMap) :
    exteriorPower.map 2 f.toLinearMap J.kahlerForm = J'.kahlerForm := by
  have hfJ' : ∀ v, f (J v) = J' (f v) := (isComplexLinearMap_iff_apply J J' f.toLinearMap).1 hfJ
  have hJ' : ∀ u w, ⟪J' u, J' w⟫ = ⟪u, w⟫ := fun u w ↦ by
    obtain ⟨u, rfl⟩ := f.surjective u
    obtain ⟨w, rfl⟩ := f.surjective w
    rw [← hfJ', ← hfJ', f.inner_map_map, f.inner_map_map, hJ]
  refine ext_inner_ιMulti_two fun u' w' ↦ ?_
  obtain ⟨u, rfl⟩ := f.surjective u'
  obtain ⟨w, rfl⟩ := f.surjective w'
  have hmap : exteriorPower.map 2 f.toLinearMap (ιMulti ℝ 2 ![u, w]) = ιMulti ℝ 2 ![f u, f w] :=
    exteriorPower.map_apply_ιMulti_two f.toLinearMap u w
  rw [← hmap]
  refine (exteriorPower.inner_map_map f.toLinearIsometry J.kahlerForm
    (ιMulti ℝ 2 ![u, w])).trans ?_
  rw [inner_kahlerForm_ιMulti hJ, hmap, inner_kahlerForm_ιMulti hJ', ← hfJ', f.inner_map_map]

/-- `D_J² η` (minus four times the anti-`J`-invariant part of `η`), read on pairs of vectors:
`⟪D_J² η, u ∧ w⟫ = 2 (η(J u, J w) - η(u, w))` for an orthogonal `J`. -/
theorem inner_lieMap_lieMap_ιMulti (η : ⋀[ℝ]^2 V) (u w : V) :
    ⟪lieMap 2 J.toLinearMap (lieMap 2 J.toLinearMap η), ιMulti ℝ 2 ![u, w]⟫ =
      2 * (⟪η, ιMulti ℝ 2 ![J u, J w]⟫ - ⟪η, ιMulti ℝ 2 ![u, w]⟫) := by
  rw [inner_lieMap_left (inner_apply_left hJ), inner_lieMap_left (inner_apply_left hJ), neg_neg,
    lieMap_lieMap_ιMulti, inner_sub_right, real_inner_smul_right, real_inner_smul_right]
  ring

/-- **`D_J² / 4` has norm at most one**: `‖D_J² η‖ ≤ 4 ‖η‖` for an orthogonal `J`, so the
anti-`J`-invariant part `-D_J² η / 4` of `η` is no longer than `η`. Since `D_J` is skew-adjoint
and `D_J³ = -4 D_J`, `‖D_J² η‖ = 2 ‖D_J η‖` and `‖D_J η‖² = -⟪η, D_J² η⟫ ≤ 2 ‖η‖ ‖D_J η‖`. -/
theorem norm_lieMap_lieMap_le (η : ⋀[ℝ]^2 V) :
    ‖lieMap 2 J.toLinearMap (lieMap 2 J.toLinearMap η)‖ ≤ 4 * ‖η‖ := by
  set D := lieMap 2 J.toLinearMap
  have hskew (x y : ⋀[ℝ]^2 V) : ⟪D x, y⟫ = -⟪x, D y⟫ := inner_lieMap_left (inner_apply_left hJ) x y
  -- `‖D² η‖² = 4 ‖D η‖²`.
  have h₂ : ‖D (D η)‖ ^ 2 = 4 * ‖D η‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, hskew,
      lieMap_lieMap_lieMap, inner_smul_right]
    ring
  -- `‖D η‖² ≤ ‖η‖ ‖D² η‖`.
  have h₁ : ‖D η‖ ^ 2 ≤ ‖η‖ * ‖D (D η)‖ := by
    rw [← real_inner_self_eq_norm_sq, hskew]
    exact (neg_le_abs _).trans (abs_real_inner_le_norm _ _)
  have h₂' : ‖D (D η)‖ = 2 * ‖D η‖ :=
    (sq_eq_sq₀ (norm_nonneg _) (by positivity)).1 (by rw [h₂]; ring)
  rw [h₂'] at h₁ ⊢
  nlinarith [norm_nonneg (D η), norm_nonneg η]

/-- **The `J`-invariant two-forms are the kernel of `D_J`**: for an orthogonal `J`, `D_J η = 0`
exactly when `η(J u, J w) = η(u, w)` for all `u` and `w`, where `η(u, w) = ⟪η, u ∧ w⟫`. -/
theorem lieMap_eq_zero_iff_forall_inner_ιMulti_apply (η : ⋀[ℝ]^2 V) :
    lieMap 2 J.toLinearMap η = 0 ↔
      ∀ u w, ⟪η, ιMulti ℝ 2 ![J u, J w]⟫ = ⟪η, ιMulti ℝ 2 ![u, w]⟫ := by
  set D := lieMap 2 J.toLinearMap
  refine ⟨fun h u w ↦ ?_, fun h ↦ ?_⟩
  · have h2 := inner_lieMap_lieMap_ιMulti hJ η u w
    rw [h, map_zero, inner_zero_left] at h2
    linarith
  · -- `D_J² η = 0` on every wedge, and `‖D_J η‖² = -⟪η, D_J² η⟫` since `D_J` is skew-adjoint.
    have h2 : D (D η) = 0 := ext_inner_ιMulti_two fun u w ↦ by
      rw [inner_lieMap_lieMap_ιMulti hJ, h, sub_self, mul_zero, inner_zero_left]
    have h1 : ‖D η‖ ^ 2 = 0 := by
      rw [← real_inner_self_eq_norm_sq, inner_lieMap_left (inner_apply_left hJ), h2,
        inner_zero_right, neg_zero]
    exact norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h1)

end Orthogonal

/-- The derivation action of `J` kills each complex line `v ∧ J v`:
`D_J (v ∧ J v) = J v ∧ J v + v ∧ J (J v) = J v ∧ J v - v ∧ v = 0`. No orthogonality of `J` is
needed, nor any inner product on the underlying real module. -/
theorem lieMap_ιMulti_apply {W : Type*} [AddCommGroup W] [Module ℝ W]
    (J : AlmostComplexStructure W) (v : W) :
    exteriorPower.lieMap 2 J.toLinearMap (ιMulti ℝ 2 ![v, J v]) = 0 := by
  have h : ∀ x : W, ιMulti ℝ 2 ![x, x] = 0 := fun x ↦
    (ιMulti ℝ 2).map_eq_zero_of_eq _ (i := 0) (j := 1) (by simp) (by decide)
  have h' : ∀ x : W, ιMulti ℝ 2 ![x, -x] = 0 := fun x ↦ by
    rw [← neg_one_smul ℝ x, ιMulti_two_smul_right, h, smul_zero]
  rw [lieMap_two_apply_ιMulti]
  simp [AlmostComplexStructure.apply_apply, h, h']

/-- The derivation action of `J` on two-forms kills the Kähler form: `D_J ω = 0`. Each summand
`b ∧ J b` is killed by `lieMap_ιMulti_apply`; no orthogonality of `J` is needed. -/
@[simp]
theorem lieMap_kahlerForm (J : AlmostComplexStructure V) :
    exteriorPower.lieMap 2 J.toLinearMap J.kahlerForm = 0 := by
  simp only [kahlerForm_def, map_smul, map_sum, lieMap_ιMulti_apply, Finset.sum_const_zero,
    smul_zero]

/-! ### Almost complex structures represented by a two-vector -/

section Contraction

variable {F : ⋀[ℝ]^2 V} {J : AlmostComplexStructure V}
  (hJ : ∀ u v, ⟪u, v⟫ = ⟪F, ιMulti ℝ 2 ![u, J v]⟫)
include hJ

/-- **Uniqueness of the compatible complex structure.** An almost complex structure `J` with
`g(u, v) = ω(u, J v)`, where `ω(u, w) = ⟪F, u ∧ w⟫`, is the contraction by `F`. -/
theorem toLinearMap_eq_twoVectorContraction : J.toLinearMap = twoVectorContraction F := by
  -- Taking `v = -J w` gives `⟪u ⌟ F, w⟫ = -⟪u, J w⟫`.
  have hA (u w : V) : ⟪twoVectorContraction F u, w⟫ = -⟪u, J w⟫ := by
    have h := hJ u (-J w)
    rw [map_neg, J.apply_apply, neg_neg, inner_neg_right] at h
    rw [inner_twoVectorContraction_apply, ← h]
  refine LinearMap.ext fun u ↦ ext_inner_right ℝ fun w ↦ ?_
  rw [inner_twoVectorContraction_apply_left, real_inner_comm (twoVectorContraction F w) u, hA,
    neg_neg, real_inner_comm]

/-- An almost complex structure with `g(u, v) = ω(u, J v)` is orthogonal. -/
theorem inner_apply_apply_of_inner_eq (u v : V) : ⟪J u, J v⟫ = ⟪u, v⟫ := by
  have h : J u = twoVectorContraction F u :=
    LinearMap.congr_fun (toLinearMap_eq_twoVectorContraction hJ) u
  rw [h, inner_twoVectorContraction_apply, hJ]

/-- A two-vector `F` with `g(u, v) = ω(u, J v)` is the Kähler two-vector of `J`. -/
theorem kahlerForm_eq_of_inner_eq : J.kahlerForm = F := by
  refine ext_inner_ιMulti_two fun u w ↦ ?_
  have h : J u = twoVectorContraction F u :=
    LinearMap.congr_fun (toLinearMap_eq_twoVectorContraction hJ) u
  rw [inner_kahlerForm_ιMulti (inner_apply_apply_of_inner_eq hJ), h,
    inner_twoVectorContraction_apply]

end Contraction

/-- For an orthogonal almost complex structure `J`, the skew-adjoint contraction of its Kähler
two-vector is `J` itself. -/
@[simp]
theorem twoVectorContraction_kahlerForm {J : AlmostComplexStructure V}
    (hJ : ∀ u w, ⟪J u, J w⟫ = ⟪u, w⟫) :
    twoVectorContraction J.kahlerForm = J.toLinearMap :=
  (toLinearMap_eq_twoVectorContraction fun u w ↦ by
    rw [inner_kahlerForm_ιMulti hJ, hJ]).symm

/-! ### Adapted orthonormal bases in arbitrary even dimension -/

/-- In any adapted orthonormal basis `(b₀, J b₀, …, b_{2n-2}, J b_{2n-2})`, the Kähler two-vector
decomposes as `∑ j, b_{2j} ∧ b_{2j+1}`. -/
theorem kahlerForm_eq_sum_of_adapted {J : AlmostComplexStructure V} {n : ℕ}
    (b : OrthonormalBasis (Fin (2 * n)) ℝ V)
    (hb : ∀ j : Fin n, b ⟨2 * (j : ℕ) + 1, by omega⟩ = J (b ⟨2 * (j : ℕ), by omega⟩)) :
    J.kahlerForm = ∑ j : Fin n,
      ιMulti ℝ 2 ![b ⟨2 * (j : ℕ), by omega⟩, b ⟨2 * (j : ℕ) + 1, by omega⟩] := by
  let b₀ : OrthonormalBasis (Fin n × Fin 2) ℝ V := b.reindex (complexRealIndexEquiv n).symm
  have hb₀ (j : Fin n) : b₀ (j, 0) = b ⟨2 * (j : ℕ), by omega⟩ ∧
      b₀ (j, 1) = b ⟨2 * (j : ℕ) + 1, by omega⟩ := by
    simp [b₀]
  have hJ : ∀ u w, ⟪J u, J w⟫ = ⟪u, w⟫ := inner_apply_apply_of_adapted b hb
  simpa only [one_smul, hb₀] using
    twoVector_eq_sum_of_skew_normalForm J.kahlerForm b₀ (fun _ ↦ 1)
      (fun j ↦ by simp [hJ, (hb₀ j).1, (hb₀ j).2, (hb j).symm])
      (fun j ↦ by simp [hJ, (hb₀ j).1, (hb₀ j).2, hb j, J.apply_apply])

/-! ### Dimension four -/

section Frame

variable {e : OrthonormalBasis (Fin 4) ℝ V} {J : AlmostComplexStructure V}

variable (h₀ : J (e 0) = e 1) (h₂ : J (e 2) = e 3)

omit [FiniteDimensional ℝ V] in
include h₀ h₂ in
/-- The coordinates of `J v` in a unitary frame: `J` rotates each of the planes `⟨e₀, e₁⟩` and
`⟨e₂, e₃⟩` by a right angle. -/
theorem repr_apply (v : V) (i : Fin 4) :
    e.repr (J v) i = ![-e.repr v 1, e.repr v 0, -e.repr v 3, e.repr v 2] i := by
  have h₁ : J (e 1) = -e 0 := by rw [← h₀, J.apply_apply]
  have h₃ : J (e 3) = -e 2 := by rw [← h₂, J.apply_apply]
  have hv : J v = ∑ i, e.repr v i • J (e i) := by
    conv_lhs => rw [← e.sum_repr v]
    simp [map_sum, map_smul]
  rw [hv, Fin.sum_univ_four, h₀, h₁, h₂, h₃]
  fin_cases i <;> simp [OrthonormalBasis.repr_self]

include h₀ h₂ in
/-- In a unitary frame the Kähler two-vector is `ω = e₀ ∧ e₁ + e₂ ∧ e₃`. -/
theorem kahlerForm_eq_ιMulti_add_ιMulti :
    J.kahlerForm = ιMulti ℝ 2 ![e 0, e 1] + ιMulti ℝ 2 ![e 2, e 3] := by
  simpa [Fin.sum_univ_two] using
    kahlerForm_eq_sum_of_adapted (n := 2) e (fun k ↦ by fin_cases k <;> simp [h₀, h₂])

include h₀ h₂ in
/-- **The frame coordinates of an anti-`J`-invariant two-vector.** If
`⟪x, J a ∧ J b⟫ = -⟪x, a ∧ b⟫` for all `a`, `b`, then in a unitary frame, with
`xᵢⱼ = ⟪x, eᵢ ∧ eⱼ⟫`, `x₀₁ = x₂₃ = 0`, `x₁₃ = -x₀₂` and `x₁₂ = x₀₃`. -/
theorem inner_ιMulti_of_antiinvariant {x : ⋀[ℝ]^2 V}
    (hx : ∀ a b, ⟪x, ιMulti ℝ 2 ![J a, J b]⟫ = -⟪x, ιMulti ℝ 2 ![a, b]⟫) :
    ⟪x, ιMulti ℝ 2 ![e 0, e 1]⟫ = 0 ∧ ⟪x, ιMulti ℝ 2 ![e 2, e 3]⟫ = 0 ∧
      ⟪x, ιMulti ℝ 2 ![e 1, e 3]⟫ = -⟪x, ιMulti ℝ 2 ![e 0, e 2]⟫ ∧
      ⟪x, ιMulti ℝ 2 ![e 1, e 2]⟫ = ⟪x, ιMulti ℝ 2 ![e 0, e 3]⟫ := by
  have h₁ : J (e 1) = -e 0 := by rw [← h₀, J.apply_apply]
  have h₃ : J (e 3) = -e 2 := by rw [← h₂, J.apply_apply]
  have h01 := hx (e 0) (e 1)
  have h23 := hx (e 2) (e 3)
  have h02 := hx (e 0) (e 2)
  have h03 := hx (e 0) (e 3)
  rw [h₀, h₁, ιMulti_two_neg_right, ιMulti_two_swap, neg_neg] at h01
  rw [h₂, h₃, ιMulti_two_neg_right, ιMulti_two_swap, neg_neg] at h23
  rw [h₀, h₂] at h02
  rw [h₀, h₃, ιMulti_two_neg_right, inner_neg_right] at h03
  refine ⟨by linarith, by linarith, h02, by linarith⟩

variable [Fact (finrank ℝ V = 4)] {o : Orientation ℝ V (Fin 4)} (hkl : 2 + 2 = finrank ℝ V)
  (he : e.toBasis.orientation = o)

include he h₀ h₂ in
/-- **The Kähler two-vector is self-dual** for the complex orientation, `⋆ω = ω`: in a positively
oriented unitary frame, `⋆(e₀ ∧ e₁) = e₂ ∧ e₃`. -/
theorem hodgeStar_kahlerForm : o.hodgeStar hkl J.kahlerForm = J.kahlerForm := by
  refine ext_inner_ιMulti_two fun u w ↦ ?_
  rw [kahlerForm_eq_ιMulti_add_ιMulti h₀ h₂, map_add, inner_add_left, inner_add_left,
    o.inner_hodgeStar_ιMulti_two hkl, o.inner_hodgeStar_ιMulti_two hkl, inner_ιMulti_two,
    inner_ιMulti_two]
  simp [o.volumeForm_robust e he, Basis.det_apply, Matrix.det_fin_four, Basis.toMatrix_apply,
    ← e.repr_apply_apply, OrthonormalBasis.repr_self]
  ring

omit [FiniteDimensional ℝ V] in
include he h₀ h₂ in
/-- **Unitary frames through a unit vector.** If `J` has a positively oriented unitary frame,
`J e₀ = e₁` and `J e₂ = e₃`, then every unit vector `ξ` is the first vector of another: there is a
positively oriented orthonormal basis `e'` with `e'₀ = ξ`, `J e'₀ = e'₁` and `J e'₂ = e'₃`. -/
theorem exists_orthonormalBasis_apply_zero_eq {ξ : V} (hξ : ‖ξ‖ = 1) :
    ∃ e' : OrthonormalBasis (Fin 4) ℝ V, e'.toBasis.orientation = o ∧ e' 0 = ξ ∧
      J (e' 0) = e' 1 ∧ J (e' 2) = e' 3 := by
  have hJ := inner_apply_apply_of_orthonormalBasis h₀ h₂
  obtain ⟨e', he'₀, h₀', h₂'⟩ := exists_unitary_orthonormalBasis_of_norm_eq_one hJ hξ
  refine ⟨e', ?_, he'₀, h₀', h₂'⟩
  rw [toBasis_orientation_eq_symplecticForm_orientation_four (J.symplecticForm_apply hJ) h₀' h₂',
    ← toBasis_orientation_eq_symplecticForm_orientation_four (J.symplecticForm_apply hJ) h₀ h₂, he]

include he h₀ h₂ in
/-- **The Hodge star preserves the `ω`-component** of a two-form, `⟪ω, ⋆F⟫ = ⟪ω, F⟫`, since `ω`
is self-dual for the complex orientation. -/
theorem inner_kahlerForm_hodgeStar (F : ⋀[ℝ]^2 V) :
    ⟪J.kahlerForm, o.hodgeStar hkl F⟫ = ⟪J.kahlerForm, F⟫ :=
  o.inner_hodgeStar_right_of_hodgeStar_eq_self even_two hkl (hodgeStar_kahlerForm h₀ h₂ hkl he) F

include he h₀ h₂ in
/-- **The Kähler form is orthogonal to the anti-self-dual forms**: `⟪ω, μ⟫ = 0` when `⋆μ = -μ`,
since `ω` is self-dual for the complex orientation. -/
theorem inner_kahlerForm_eq_zero_of_hodgeStar_eq_neg {μ : ⋀[ℝ]^2 V}
    (hμ : o.hodgeStar hkl μ = -μ) : ⟪J.kahlerForm, μ⟫ = 0 := by
  have h := o.inner_hodgeStar_right_of_hodgeStar_eq_neg even_two hkl hμ J.kahlerForm
  rw [hodgeStar_kahlerForm h₀ h₂ hkl he, real_inner_comm] at h
  linarith

include he h₀ h₂ in
/-- The square of the derivation action of `J` on the self-dual part of a two-form:
`D_J² (x + ⋆x) = 4 ⟪ω, x⟫ ω - 4 (x + ⋆x)`. -/
private theorem lieMap_lieMap_add_hodgeStar
    (x : ⋀[ℝ]^2 V) :
    exteriorPower.lieMap 2 J.toLinearMap (exteriorPower.lieMap 2 J.toLinearMap
      (x + o.hodgeStar hkl x)) =
      (4 * ⟪J.kahlerForm, x⟫) • J.kahlerForm - (4 : ℝ) • (x + o.hodgeStar hkl x) := by
  have hJ := inner_apply_apply_of_orthonormalBasis h₀ h₂
  set D := exteriorPower.lieMap 2 J.toLinearMap
  -- Move both derivations to the right, where they act on the wedge `u ∧ w`.
  have hD (z y : ⋀[ℝ]^2 V) : ⟪D (D z), y⟫ = ⟪z, D (D y)⟫ := by
    rw [inner_lieMap_left (inner_apply_left hJ),
      inner_lieMap_left (inner_apply_left hJ), neg_neg]
  have key : D ∘ₗ D ∘ₗ (LinearMap.id + (o.hodgeStar hkl).toLinearMap) =
      (4 : ℝ) • (innerₗ _ J.kahlerForm).smulRight J.kahlerForm -
        (4 : ℝ) • (LinearMap.id + (o.hodgeStar hkl).toLinearMap) := by
    refine linearMap_ext_inner_ιMulti_two fun a b u w ↦ ?_
    simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.smul_apply,
      LinearMap.add_apply, LinearMap.id_apply, LinearEquiv.coe_coe, LinearMap.smulRight_apply,
      innerₗ_apply_apply, hD, D, exteriorPower.lieMap_two_apply_ιMulti, map_add,
      J.apply_apply, inner_add_left, inner_add_right, inner_sub_left, real_inner_smul_left,
      inner_kahlerForm_ιMulti hJ, o.inner_hodgeStar_ιMulti_two hkl, inner_ιMulti_two,
      o.volumeForm_robust e he, Basis.det_apply, Matrix.det_fin_four]
    simp only [e.inner_eq_sum_repr, conj_trivial, Fin.sum_univ_four, Basis.toMatrix_apply,
      OrthonormalBasis.coe_toBasis_repr_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, map_neg,
      Finsupp.neg_apply, PiLp.neg_apply, repr_apply h₀ h₂]
    ring
  simpa only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.add_apply, LinearMap.id_apply, LinearEquiv.coe_coe, LinearMap.smulRight_apply,
    innerₗ_apply_apply, smul_smul] using LinearMap.congr_fun key x

include he h₀ h₂ in
/-- **`J` acts on the self-dual two-forms as a rotation about `ω`**: for self-dual `η`,
`D_J² η = 2 ⟪ω, η⟫ ω - 4 η`. Since `⟪ω, ω⟫ = 2`, the map `D_J / 2` is zero on `ω` and squares to
`-1` on the orthogonal complement of `ω` in `Λ⁺`. -/
theorem lieMap_lieMap_of_hodgeStar_eq_self
    {η : ⋀[ℝ]^2 V} (hη : o.hodgeStar hkl η = η) :
    exteriorPower.lieMap 2 J.toLinearMap (exteriorPower.lieMap 2 J.toLinearMap η) =
      (2 * ⟪J.kahlerForm, η⟫) • J.kahlerForm - (4 : ℝ) • η := by
  have h := lieMap_lieMap_add_hodgeStar h₀ h₂ hkl he η
  rw [hη, map_add, map_add] at h
  linear_combination (norm := module) (2⁻¹ : ℝ) • h

include he h₀ h₂ in
/-- **`J` acts trivially on the anti-self-dual two-forms**: `D_J η = 0` for `⋆η = -η`. Since
`D_J` is skew-adjoint, this says that an anti-self-dual two-form is `J`-invariant,
`η(J u, J w) = η(u, w)`, as is `ω`; the anti-self-dual forms are the primitive `(1,1)`-forms. -/
theorem lieMap_of_hodgeStar_eq_neg {η : ⋀[ℝ]^2 V} (hη : o.hodgeStar hkl η = -η) :
    exteriorPower.lieMap 2 J.toLinearMap η = 0 := by
  have hJ := inner_apply_apply_of_orthonormalBasis h₀ h₂
  set D := exteriorPower.lieMap 2 J.toLinearMap
  -- `D_J` kills the anti-self-dual part `x - ⋆x` of every two-vector `x`.
  have key : D ∘ₗ (LinearMap.id - (o.hodgeStar hkl).toLinearMap) = 0 := by
    refine linearMap_ext_inner_ιMulti_two fun a b u w ↦ ?_
    simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply,
      LinearEquiv.coe_coe, LinearMap.zero_apply, inner_zero_left,
      inner_lieMap_left (inner_apply_left hJ), D, exteriorPower.lieMap_two_apply_ιMulti,
      inner_add_right, inner_sub_left, o.inner_hodgeStar_ιMulti_two hkl, inner_ιMulti_two,
      o.volumeForm_robust e he, Basis.det_apply, Matrix.det_fin_four]
    simp only [e.inner_eq_sum_repr, conj_trivial, Fin.sum_univ_four, Basis.toMatrix_apply,
      OrthonormalBasis.coe_toBasis_repr_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
      repr_apply h₀ h₂]
    ring
  have h := LinearMap.congr_fun key η
  rw [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply, LinearEquiv.coe_coe, hη,
    sub_neg_eq_add, map_add, LinearMap.zero_apply] at h
  rwa [← two_smul ℝ (D η), smul_eq_zero, or_iff_right two_ne_zero] at h

include he h₀ h₂ in
/-- **The self-dual part of `ξ ∧ J a - J ξ ∧ a` is `⟪ξ, a⟫ ω`**:
`z + ⋆z = 2 ⟪ξ, a⟫ ω` for `z = ξ ∧ J a - J ξ ∧ a`. For `a = ξ` a unit vector this says that
`2 ξ ∧ J ξ - ω` is anti-self-dual. -/
theorem ιMulti_sub_ιMulti_add_hodgeStar (ξ a : V) :
    ιMulti ℝ 2 ![ξ, J a] - ιMulti ℝ 2 ![J ξ, a] +
        o.hodgeStar hkl (ιMulti ℝ 2 ![ξ, J a] - ιMulti ℝ 2 ![J ξ, a]) =
      (2 * ⟪ξ, a⟫) • J.kahlerForm := by
  have hJ := inner_apply_apply_of_orthonormalBasis h₀ h₂
  refine ext_inner_ιMulti_two fun u w ↦ ?_
  simp only [map_sub, inner_add_left, inner_sub_left, real_inner_smul_left,
    inner_kahlerForm_ιMulti hJ, o.inner_hodgeStar_ιMulti_two hkl, inner_ιMulti_two,
    o.volumeForm_robust e he, Basis.det_apply, Matrix.det_fin_four]
  simp only [e.inner_eq_sum_repr, conj_trivial, Fin.sum_univ_four, Basis.toMatrix_apply,
    OrthonormalBasis.coe_toBasis_repr_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
    repr_apply h₀ h₂]
  ring

include he h₀ h₂ in
/-- **The star of a complex line**: for the complex orientation, `⋆(x ∧ J x) = ‖x‖² ω - x ∧ J x`.
For a unit vector `x` this is the complex line `u ∧ J u` orthogonal to `x` and `J x`, since
`ω = x ∧ J x + u ∧ J u` in a unitary frame starting with `x`. -/
theorem hodgeStar_ιMulti_apply (x : V) :
    o.hodgeStar hkl (ιMulti ℝ 2 ![x, J x]) = ‖x‖ ^ 2 • J.kahlerForm - ιMulti ℝ 2 ![x, J x] := by
  have h := ιMulti_sub_ιMulti_add_hodgeStar h₀ h₂ hkl he x x
  have hz : ιMulti ℝ 2 ![x, J x] - ιMulti ℝ 2 ![J x, x] = (2 : ℝ) • ιMulti ℝ 2 ![x, J x] :=
    ext_inner_ιMulti_two fun u w ↦ by
      rw [inner_sub_left, real_inner_smul_left, inner_ιMulti_two, inner_ιMulti_two]
      ring
  rw [hz, map_smul, real_inner_self_eq_norm_sq, ← smul_add, mul_smul] at h
  exact eq_sub_of_add_eq' (smul_right_injective (⋀[ℝ]^2 V) two_ne_zero h)

include he h₀ h₂ in
/-- **A `J`-invariant two-form is a multiple of `ω` plus an anti-self-dual form**: for
`D_J η = 0`, `η = (⟪ω, η⟫ / 2) ω + (η - ⋆η) / 2`. -/
theorem eq_smul_kahlerForm_add_of_lieMap_eq_zero {η : ⋀[ℝ]^2 V}
    (hη : lieMap 2 J.toLinearMap η = 0) :
    η = (⟪J.kahlerForm, η⟫ / 2) • J.kahlerForm + (2⁻¹ : ℝ) • (η - o.hodgeStar hkl η) := by
  set p := (2⁻¹ : ℝ) • (η + o.hodgeStar hkl η)
  set m := (2⁻¹ : ℝ) • (η - o.hodgeStar hkl η)
  have hp : o.hodgeStar hkl p = p := o.hodgeStar_smul_add_hodgeStar even_two hkl η
  have hm : o.hodgeStar hkl m = -m := o.hodgeStar_smul_sub_hodgeStar even_two hkl η
  have hpm : p + m = η := by simp only [p, m]; module
  -- The self-dual part `p` is `J`-invariant, as `η` and its anti-self-dual part are.
  have hDp : lieMap 2 J.toLinearMap p = 0 := by
    have h := congrArg (lieMap 2 J.toLinearMap) hpm
    rwa [map_add, lieMap_of_hodgeStar_eq_neg h₀ h₂ hkl he hm, add_zero, hη] at h
  have h2 := lieMap_lieMap_of_hodgeStar_eq_self h₀ h₂ hkl he hp
  rw [hDp, map_zero] at h2
  have hω : ⟪J.kahlerForm, p⟫ = ⟪J.kahlerForm, η⟫ := by
    rw [← hpm, inner_add_right, inner_kahlerForm_eq_zero_of_hodgeStar_eq_neg h₀ h₂ hkl he hm,
      add_zero]
  rw [hω] at h2
  calc η = p + m := hpm.symm
    _ = _ := by
      congr 1
      linear_combination (norm := module) (4⁻¹ : ℝ) • h2

include he h₀ h₂ in
/-- **A two-form whose self-dual part is a multiple of `ω` is `J`-invariant**: if
`η + ⋆η = c ω`, then `D_J η = 0`, so `η` has no `(2,0) + (0,2)` part. This is the converse of
`eq_smul_kahlerForm_add_of_lieMap_eq_zero`: `η` is `(c / 2) ω` plus its anti-self-dual part, and
both are `J`-invariant. -/
theorem lieMap_eq_zero_of_add_hodgeStar_eq_smul {η : ⋀[ℝ]^2 V} {c : ℝ}
    (hη : η + o.hodgeStar hkl η = c • J.kahlerForm) : lieMap 2 J.toLinearMap η = 0 := by
  set m := (2⁻¹ : ℝ) • (η - o.hodgeStar hkl η)
  have hm : o.hodgeStar hkl m = -m := o.hodgeStar_smul_sub_hodgeStar even_two hkl η
  have hpm : η = (2⁻¹ * c : ℝ) • J.kahlerForm + m := by
    rw [mul_smul, ← hη]
    module
  rw [hpm, map_add, map_smul, lieMap_kahlerForm, smul_zero, zero_add,
    lieMap_of_hodgeStar_eq_neg h₀ h₂ hkl he hm]

end Frame

end TauCeti.AlmostComplexStructure
