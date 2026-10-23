/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.ExteriorPower
public import Mathlib.Analysis.InnerProductSpace.Orientation
public import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
public import Mathlib.LinearAlgebra.ExteriorPower.HodgeStar
public import TauCeti.Analysis.InnerProductSpace.Nondegenerate
-- Private: `stdOrthonormalBasis`, `InnerProductSpace.ext_inner_right_basis`,
-- `Module.Basis.topVector_eq_ιMulti`, `exteriorPower.wedgePairing_exteriorPower_apply` and the
-- exterior-algebra contraction lemmas in `TauCeti.ExteriorAlgebra` are used only inside proofs.
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.PiL2
import TauCeti.LinearAlgebra.ExteriorAlgebra.Contraction
import TauCeti.LinearAlgebra.ExteriorPower.Basic
import TauCeti.LinearAlgebra.ExteriorPower.WedgePairing
-- The Gram-determinant formula `LinearMap.BilinForm.bilinForm_ιMulti_ιMulti` for the induced
-- bilinear form on an exterior power is private to its file, and the body of
-- `LinearMap.BilinForm.exteriorPower` is not exposed, so evaluating that form needs this import.
import all Mathlib.LinearAlgebra.ExteriorPower.BilinForm

/-!
# The Hodge star of an oriented real inner product space

Mathlib's `exteriorPower.hodgeStar` is built from a bilinear form and a trivialization `vol` of the
top exterior power, and is characterized by `B (⋆x) y = vol (x ∧ y)`. On an oriented real inner
product space `V` of dimension `n` both inputs are canonical: the bilinear form is the inner
product, and the trivialization is the one induced by Mathlib's `Orientation.volumeForm`, which
takes the value `1` on every positively oriented orthonormal basis. This file packages the
resulting pointwise Hodge star `⋆ : ⋀ᵏ V ≃ ⋀ˡ V` (for `k + l = n`), so that
`⟪⋆x, y⟫ = vol (x ∧ y)`, equivalently `x ∧ y = ⟪⋆x, y⟫ vol`.

Its value on the orthonormal basis of `⋀ᵏ V` induced by a positively oriented orthonormal basis
`e` of `V` is the familiar formula: `⋆ e_I = ε(I) e_{Iᶜ}`, where `e_I` is the increasing wedge
of the `eᵢ` with `i ∈ I` and `ε(I)` is the sign of the shuffle permutation listing `I` before its
complement. For instance, in an oriented four-dimensional space `⋆(e₁ ∧ e₂) = e₃ ∧ e₄`, so the
self-dual and anti-self-dual two-forms are the `±1` eigenvectors of `⋆` on `⋀² V`.

In dimension four a unit vector `s` splits a two-form as `F = s ∧ a + b`, where `a = s ⌟ F` is
the contraction of `F` by `⟪s, ·⟫` and `b` has no `s`-component. Since `b ∧ b = 0`, the pairing
of `s ∧ a` with `F + ⋆F` is `‖a‖² + vol (F ∧ F) / 2`. On a product `S¹ × Y` with `s = ds`, this is
the pointwise identity `2 ⟨ds ∧ ι_T F, F⁺⟩ = |ι_T F|² + (F ∧ F) / 2` between the mixed component
of a curvature form, its self-dual part and its Chern–Weil density.

## Main definitions

* `Orientation.volumeEquiv`: the trivialization of `⋀ⁿ V` induced by `Orientation.volumeForm`.
* `Orientation.hodgeStar`: the Hodge star `⋀ᵏ V ≃ ⋀ˡ V` of the oriented inner product space.

## Main results

* `TauCeti.exteriorPower_innerₗ`: the bilinear form that the inner product induces on
  `⋀ᵏ V` is the inner product of `⋀ᵏ V`.
* `Orientation.volumeEquiv_topVector`: the volume of the wedge of a positively oriented orthonormal
  basis is `1`.
* `Orientation.inner_hodgeStar_apply`: the characterization `⟪⋆x, y⟫ = vol (x ∧ y)`.
* `Orientation.hodgeStar_basis`: the formula `⋆ e_I = ε(I) e_{Iᶜ}` on an orthonormal basis.
* `Orientation.hodgeStar_hodgeStar`: `⋆⋆x = (-1) ^ (k * l) x`, and
  `Orientation.hodgeStar_hodgeStar_of_even`: `⋆⋆x = x` in an even middle degree.
* `TauCeti.inner_ιMulti_two_eq_inner_ιInv_contractLeft`: on two-forms, wedging with `u` is adjoint
  to contracting with `⟪u, ·⟫`, `⟪u ∧ w, b⟫ = ⟪w, u ⌟ b⟫`.
* `Orientation.inner_ιMulti_ιInv_contractLeft_add_hodgeStar`: for a unit vector `s` in dimension
  four, `⟪s ∧ (s ⌟ F), F + ⋆F⟫ = ‖s ⌟ F‖² + vol (F ∧ F) / 2`.

## References

* F. W. Warner, *Foundations of Differentiable Manifolds and Lie Groups*, Graduate Texts in
  Mathematics 94, Springer (1983), §6.1.
-/

public section

noncomputable section

open Module exteriorPower Set
open scoped RealInnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

namespace TauCeti

/-- The bilinear form induced by the inner product on the `k`-th exterior power, given on pure
wedges by the Gram determinant, is the inner product of `⋀ᵏ V`. -/
theorem exteriorPower_innerₗ (k : ℕ) :
    LinearMap.BilinForm.exteriorPower (innerₗ V) k = innerₗ (⋀[ℝ]^k V) := by
  ext v w
  simp [LinearMap.BilinForm.bilinForm_ιMulti_ιMulti, inner_ιMulti_ιMulti]

open CliffordAlgebra in
/-- **Wedging with a vector is adjoint to contracting with it**, on two-forms: for `u, w : V` and
`b ∈ ⋀² V`, `⟪u ∧ w, b⟫ = ⟪w, u ⌟ b⟫`. Here `u ⌟ b` is the contraction of `b` by the functional
`⟪u, ·⟫`, a vector of `V` read off with `ExteriorAlgebra.ιInv`. -/
theorem inner_ιMulti_two_eq_inner_ιInv_contractLeft (u w : V) (b : ⋀[ℝ]^2 V) :
    ⟪ιMulti ℝ 2 ![u, w], b⟫ =
      ⟪w, ExteriorAlgebra.ιInv (contractLeft (innerₗ V u) (b : ExteriorAlgebra ℝ V))⟫ := by
  -- Both sides are linear in `b`, so it suffices to compare them on `p ∧ q`.
  have key : innerₗ (⋀[ℝ]^2 V) (ιMulti ℝ 2 ![u, w]) =
      innerₗ V w ∘ₗ ExteriorAlgebra.ιInv ∘ₗ contractLeft (Q := (0 : QuadraticForm ℝ V))
        (innerₗ V u) ∘ₗ (⋀[ℝ]^2 V).subtype := by
    refine exteriorPower.linearMap_ext ?_
    ext v
    simp [inner_ιMulti_ιMulti, Matrix.det_fin_two, ExteriorAlgebra.ιMulti_apply,
      contractLeft_ι_mul, ← Algebra.commutes, ← Algebra.smul_def, ExteriorAlgebra.ι_leftInverse _,
      inner_sub_right, real_inner_smul_right, Matrix.vecTail]
    ring
  simpa using LinearMap.congr_fun key b

end TauCeti

namespace Orientation

variable {n : ℕ} [_i : Fact (finrank ℝ V = n)] (o : Orientation ℝ V (Fin n))

/-- The linear functional on the top exterior power induced by the volume form. -/
private def volumeLinearMap : ⋀[ℝ]^(finrank ℝ V) V →ₗ[ℝ] ℝ :=
  alternatingMapLinearEquiv (o.volumeForm.domDomCongr (finCongr _i.out.symm))

omit [FiniteDimensional ℝ V] in
private theorem volumeLinearMap_ιMulti (v : Fin (finrank ℝ V) → V) :
    o.volumeLinearMap (ιMulti ℝ _ v) = o.volumeForm (v ∘ finCongr _i.out.symm) := by
  simp [volumeLinearMap]

omit [FiniteDimensional ℝ V] in
private theorem volumeLinearMap_topVector (b : OrthonormalBasis (Fin n) ℝ V) :
    o.volumeLinearMap b.toBasis.topVector = o.volumeForm b := by
  rw [b.toBasis.topVector_eq_ιMulti _i.out, volumeLinearMap_ιMulti]
  simp [Function.comp_def]

private theorem bijective_volumeLinearMap : Function.Bijective o.volumeLinearMap := by
  -- The functional is nonzero on the wedge of any orthonormal basis, and the top exterior power
  -- is a line.
  set b : OrthonormalBasis (Fin n) ℝ V := (stdOrthonormalBasis ℝ V).reindex (finCongr _i.out)
  have hb : o.volumeLinearMap b.toBasis.topVector ≠ 0 := by
    rw [volumeLinearMap_topVector, ← abs_ne_zero, o.abs_volumeForm_apply_of_orthonormal]
    exact one_ne_zero
  have hsurj : Function.Surjective o.volumeLinearMap := fun t ↦
    ⟨(t / o.volumeLinearMap b.toBasis.topVector) • b.toBasis.topVector, by
      rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hb]⟩
  refine ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).2 hsurj, hsurj⟩
  rw [exteriorPower.finrank_eq, Nat.choose_self, finrank_self]

/-- The volume of an oriented real inner product space, as a trivialization of its top exterior
power: it sends the wedge `v₁ ∧ ⋯ ∧ vₙ` to `Orientation.volumeForm` of `(v₁, …, vₙ)`. -/
def volumeEquiv : ⋀[ℝ]^(finrank ℝ V) V ≃ₗ[ℝ] ℝ :=
  LinearEquiv.ofBijective o.volumeLinearMap o.bijective_volumeLinearMap

/-- The volume of a wedge of vectors is their `Orientation.volumeForm`. -/
theorem volumeEquiv_ιMulti (v : Fin (finrank ℝ V) → V) :
    o.volumeEquiv (ιMulti ℝ _ v) = o.volumeForm (v ∘ finCongr _i.out.symm) :=
  o.volumeLinearMap_ιMulti v

/-- The volume of the wedge of a positively oriented orthonormal basis is `1`. -/
theorem volumeEquiv_topVector (b : OrthonormalBasis (Fin n) ℝ V)
    (hb : b.toBasis.orientation = o) : o.volumeEquiv b.toBasis.topVector = 1 := by
  rw [volumeEquiv, LinearEquiv.ofBijective_apply, volumeLinearMap_topVector,
    o.volumeForm_robust b hb, ← OrthonormalBasis.coe_toBasis, Basis.det_self]

/-- The Hodge star `⋀ᵏ V ≃ ⋀ˡ V`, `k + l = finrank ℝ V`, of an oriented real inner product space:
Mathlib's `exteriorPower.hodgeStar` for the inner product and `Orientation.volumeEquiv`. It is
characterized by `⟪⋆x, y⟫ = vol (x ∧ y)` (`Orientation.inner_hodgeStar_apply`). -/
def hodgeStar {k l : ℕ} (hkl : k + l = finrank ℝ V) : ⋀[ℝ]^k V ≃ₗ[ℝ] ⋀[ℝ]^l V :=
  exteriorPower.hodgeStar (innerₗ V) TauCeti.bijective_innerₗ o.volumeEquiv hkl

/-- **The characterization of the Hodge star**: `⟪⋆x, y⟫ = vol (x ∧ y)`. -/
theorem inner_hodgeStar_apply {k l : ℕ} (hkl : k + l = finrank ℝ V) (x : ⋀[ℝ]^k V)
    (y : ⋀[ℝ]^l V) : ⟪o.hodgeStar hkl x, y⟫ = wedgePairing o.volumeEquiv hkl x y := by
  rw [← innerₗ_apply_apply, ← TauCeti.exteriorPower_innerₗ, hodgeStar]
  simp

/-- On the basis of `⋀ᵏ V` induced by any orthonormal basis `e`, `⋆ e_I = vol(e) ε(I) e_{Iᶜ}`,
where `vol(e) = ±1` is the volume form of `e` and `ε(I)` is the shuffle sign of `I`. -/
private theorem hodgeStar_orthonormalBasis (b : OrthonormalBasis (Fin n) ℝ V) {k l : ℕ}
    (hkl : k + l = finrank ℝ V) (s : powersetCard (Fin n) k) :
    o.hodgeStar hkl (b.toBasis.exteriorPower k s) =
      o.volumeForm b • powersetCard.sign s • b.toBasis.exteriorPower l
        (powersetCard.compl (by rw [Fintype.card_fin, ← _i.out]; omega) s) := by
  -- Pair both sides with the orthonormal basis of `⋀ˡ V`.
  refine InnerProductSpace.ext_inner_right_basis (b.toBasis.exteriorPower l) fun t ↦ ?_
  rw [inner_hodgeStar_apply, wedgePairing_exteriorPower_apply, volumeEquiv,
    LinearEquiv.ofBijective_apply, volumeLinearMap_topVector,
    ← OrthonormalBasis.toBasis_exteriorPower, OrthonormalBasis.coe_toBasis]
  simp only [Units.smul_def, ← Int.cast_smul_eq_zsmul ℝ, real_inner_smul_left,
    OrthonormalBasis.inner_eq_ite, smul_eq_mul]
  -- `s` and `t` are disjoint exactly when `t` is the complement of `s`.
  have hcard : l + k = Fintype.card (Fin n) := by rw [Fintype.card_fin, ← _i.out]; omega
  rw [if_congr (disjoint_comm.trans (powersetCard.disjoint_iff_eq_compl hcard) |>.trans eq_comm)
    rfl rfl]
  ring

/-- **The Hodge star on an orthonormal basis**: if `e` is a positively oriented orthonormal basis,
then `⋆ e_I = ε(I) e_{Iᶜ}`, where `e_I` is the increasing wedge of the `eᵢ` with `i ∈ I` and
`ε(I) = Set.powersetCard.sign I` is the sign of the shuffle listing `I` before its complement. -/
theorem hodgeStar_basis (b : OrthonormalBasis (Fin n) ℝ V) (hb : b.toBasis.orientation = o)
    {k l : ℕ} (hkl : k + l = finrank ℝ V) (s : powersetCard (Fin n) k) :
    o.hodgeStar hkl (b.toBasis.exteriorPower k s) =
      powersetCard.sign s • b.toBasis.exteriorPower l
        (powersetCard.compl (by rw [Fintype.card_fin, ← _i.out]; omega) s) := by
  rw [hodgeStar_orthonormalBasis, o.volumeForm_robust b hb, ← OrthonormalBasis.coe_toBasis,
    Basis.det_self, one_smul]

/-- **The square of the Hodge star**: `⋆⋆x = (-1) ^ (k * l) x` for `x ∈ ⋀ᵏ V` and
`k + l = finrank ℝ V`. -/
theorem hodgeStar_hodgeStar {k l : ℕ} (hkl : k + l = finrank ℝ V) (hlk : l + k = finrank ℝ V)
    (x : ⋀[ℝ]^k V) : o.hodgeStar hlk (o.hodgeStar hkl x) = (-1 : ℝ) ^ (k * l) • x := by
  -- Compare both sides on the basis of `⋀ᵏ V` induced by an orthonormal basis `e`; with
  -- `vol(e) = ±1` and `ε(I) ε(Iᶜ) = (-1) ^ (k * l)`, this is `hodgeStar_orthonormalBasis` twice.
  set b : OrthonormalBasis (Fin n) ℝ V := (stdOrthonormalBasis ℝ V).reindex (finCongr _i.out)
  refine LinearMap.congr_fun ((b.toBasis.exteriorPower k).ext
    (f₁ := (o.hodgeStar hlk).toLinearMap ∘ₗ (o.hodgeStar hkl).toLinearMap)
    (f₂ := (-1 : ℝ) ^ (k * l) • LinearMap.id) fun s ↦ ?_) x
  have hcard : l + k = Fintype.card (Fin n) := by rw [Fintype.card_fin, ← _i.out, hlk]
  have hs : powersetCard.compl (by rw [Fintype.card_fin, ← _i.out]; omega)
      (powersetCard.compl hcard s) = s := (powersetCard.compl hcard).symm_apply_apply s
  have hvol : o.volumeForm b * o.volumeForm b = 1 := by
    rw [← abs_mul_abs_self, o.abs_volumeForm_apply_of_orthonormal, one_mul]
  have hsign := congrArg (fun u : ℤˣ ↦ ((u : ℤ) : ℝ)) (powersetCard.sign_mul_sign_compl hcard s)
  push_cast at hsign
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.smul_apply, LinearMap.id_apply]
  rw [hodgeStar_orthonormalBasis, map_smul, map_zsmul_unit, hodgeStar_orthonormalBasis, hs]
  simp only [Units.smul_def, ← Int.cast_smul_eq_zsmul ℝ, smul_smul]
  congr 1
  set ε := powersetCard.sign s
  set ε' := powersetCard.sign (powersetCard.compl hcard s)
  linear_combination ((ε : ℤ) * (ε' : ℤ) : ℝ) * hvol + hsign

/-- In an even middle degree, `k + k = finrank ℝ V` with `k` even, the Hodge star is an
involution, `⋆⋆x = x`. This covers two-forms in dimension four, where the self-dual and
anti-self-dual two-forms are the `±1` eigenspaces of `⋆`. -/
@[simp]
theorem hodgeStar_hodgeStar_of_even {k : ℕ} (hk : Even k) (hkk : k + k = finrank ℝ V)
    (x : ⋀[ℝ]^k V) : o.hodgeStar hkk (o.hodgeStar hkk x) = x := by
  rw [hodgeStar_hodgeStar, (hk.mul_right k).neg_one_pow, one_smul]

/-! ### Two-forms split along a unit vector -/

open CliffordAlgebra in
/-- **The pointwise energy identity of a two-form split along a unit vector.** Let `s` be a unit
vector of an oriented four-dimensional real inner product space, let `F ∈ ⋀² V`, and let
`a = s ⌟ F` be the contraction of `F` by `⟪s, ·⟫`, read as a vector with
`ExteriorAlgebra.ιInv`. Then `⟪s ∧ a, F + ⋆F⟫ = ‖a‖² + vol (F ∧ F) / 2`; equivalently, with the
self-dual part `F⁺ = (F + ⋆F) / 2`, `2 ⟪s ∧ a, F⁺⟫ = ‖a‖² + vol (F ∧ F) / 2`.

On a product `S¹ × Y` with `s = ds` and `T = ∂ₛ`, this is the pointwise identity
`2 ⟨ds ∧ ι_T F, F⁺⟩ dvol = |ι_T F|² dvol + (F ∧ F) / 2` for a real two-form `F`. -/
theorem inner_ιMulti_ιInv_contractLeft_add_hodgeStar (hkk : 2 + 2 = finrank ℝ V) {s : V}
    (hs : ‖s‖ = 1) (F : ⋀[ℝ]^2 V) :
    ⟪ιMulti ℝ 2 ![s, ExteriorAlgebra.ιInv (contractLeft (innerₗ V s) (F : ExteriorAlgebra ℝ V))],
      F + o.hodgeStar hkk F⟫ =
      ‖ExteriorAlgebra.ιInv (contractLeft (innerₗ V s) (F : ExteriorAlgebra ℝ V))‖ ^ 2 +
        wedgePairing o.volumeEquiv hkk F F / 2 := by
  set a := ExteriorAlgebra.ιInv (contractLeft (innerₗ V s) (F : ExteriorAlgebra ℝ V)) with ha
  have hss : innerₗ V s s = 1 := by
    rw [innerₗ_apply_apply, real_inner_self_eq_norm_sq, hs, one_pow]
  -- The contraction `s ⌟ F` is a one-form, the image of the vector `a`.
  have hιa : ExteriorAlgebra.ι ℝ a = contractLeft (innerₗ V s) (F : ExteriorAlgebra ℝ V) :=
    TauCeti.ExteriorAlgebra.ι_ιInv_of_mem_exteriorPower_one
      (TauCeti.ExteriorAlgebra.contractLeft_mem_exteriorPower (innerₗ V s) (n := 1) F.2)
  -- In dimension four, `F ∧ F` is twice `F ∧ (s ∧ a)`.
  have hwedge : exteriorPower.wedge ℝ V 2 2 F F =
      2 • exteriorPower.wedge ℝ V 2 2 F (ιMulti ℝ 2 ![s, a]) := by
    apply Subtype.ext
    simp only [exteriorPower.coe_wedge, exteriorPower.ιMulti_apply_coe,
      ExteriorAlgebra.ιMulti_apply, Submodule.coe_smul_of_tower]
    simp only [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one,
      Matrix.cons_val_zero, Matrix.cons_val_succ, hιa]
    exact TauCeti.ExteriorAlgebra.mul_self_eq_two_smul_mul_ι_mul_contractLeft hss (by omega) F.2
  rw [inner_add_right, TauCeti.inner_ιMulti_two_eq_inner_ιInv_contractLeft, ← ha,
    real_inner_self_eq_norm_sq, real_inner_comm, inner_hodgeStar_apply]
  simp only [LinearMap.compr₂_apply, hwedge, map_nsmul, nsmul_eq_mul]
  ring

end Orientation
