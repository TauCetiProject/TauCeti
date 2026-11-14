/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.TensorProduct
public import TauCeti.LinearAlgebra.QuadraticForm.Signature
public import TauCeti.LinearAlgebra.QuadraticForm.TotallyIsotropic
import TauCeti.LinearAlgebra.TensorProduct.Torsion

/-!
# The real extension of an integral form spanned by a hyperbolic pair

Let `B` be a `ℤ`-valued bilinear form on an abelian group `H`, and let `v, t ∈ H` be a hyperbolic
pair, `B v v = B t t = 0` and `B v t = B t v = 1`, which spans `H` modulo torsion: every `x ∈ H`
differs from some `a v + c t` by an element of finite additive order. Such a form is even
(`LinearMap.BilinForm.even_apply_self_of_isOfFinAddOrder_span`). This file computes its scalar
extension `B_𝕜 = B.baseChange 𝕜` to `𝕜 ⊗[ℤ] H`, for a field `𝕜` of characteristic zero, typically
`ℝ`.

Torsion dies in `𝕜 ⊗[ℤ] H` (`TauCeti.tmul_eq_zero_of_isOfFinAddOrder`), so `𝕜 ⊗[ℤ] H` is the
direct sum of the lines through `1 ⊗ v` and `1 ⊗ t`. The quadratic form `x ↦ B_𝕜 x x` vanishes on
both lines, and its polar form pairs them perfectly: `polar (a (1 ⊗ v)) (c (1 ⊗ t)) = 2ac`. Hence:

* `𝕜 ⊗[ℤ] H` has dimension two
  (`LinearMap.BilinForm.finrank_tensorProduct_eq_two_of_isOfFinAddOrder_span`);
* the quadratic form of `B_𝕜` is nondegenerate
  (`LinearMap.BilinForm.nondegenerate_toQuadraticMap_baseChange_of_isOfFinAddOrder_span`);
* over a linearly ordered field both of its indices of inertia are one
  (`LinearMap.BilinForm.sigPos_toQuadraticMap_baseChange_eq_one_of_isOfFinAddOrder_span`,
  `LinearMap.BilinForm.sigNeg_toQuadraticMap_baseChange_eq_one_of_isOfFinAddOrder_span`), by the
  signature of a form split by complementary totally isotropic subspaces
  (`QuadraticForm.sigPos_eq_finrank_of_isCompl`).

The example is the intersection form of the symplectic product `X = (ℝ / ℤ) × Y_φ` of the circle
with the mapping torus `Y_φ` of a surface diffeomorphism with `b₁(Y_φ) = 1`, in the setting of
`TauCeti.SmoothMappingTorus.apply_self_sub_apply_canonical_eq`: `H = H²(X; ℤ)`, `v` is the pullback
of a class of `H²(Y_φ; ℤ)` pairing to one with the fibre, and `t = [ds ∧ dt]`. That `v, t` is a
hyperbolic pair spanning `H²(X; ℤ)` modulo torsion is a geometric input, not proved here. Given it,
and `ℝ ⊗[ℤ] H²(X; ℤ) = H²(X; ℝ)`, the results say `b₂(X) = 2` and `b₂⁺(X) = b₂⁻(X) = 1`. Together
with the evenness of the intersection form, which excludes classes of square `-1`, this places `X`
among the minimal four-manifolds with `b₂⁺ = 1`, where Seiberg–Witten invariants depend on a
chamber.

## References

* C. H. Taubes, *The Seiberg–Witten and Gromov invariants*, Math. Res. Lett. 2 (1995), 221–238.
* E.-N. Ionel and T. H. Parker, *Gromov invariants and symplectic maps*, Math. Ann. 314 (1999),
  127–158.
-/

public section

open scoped TensorProduct

namespace LinearMap.BilinForm

variable {𝕜 H : Type*} [Field 𝕜] [AddCommGroup H] {B : LinearMap.BilinForm ℤ H} {v t : H}

/-- The polar form of `B_𝕜` on `a (1 ⊗ v)` and `c (1 ⊗ t)`, for a hyperbolic pair `v, t`, is
`2ac`. -/
private theorem polar_toQuadraticMap_baseChange_smul_one_tmul (hvt : B v t = 1) (htv : B t v = 1)
    (a c : 𝕜) :
    QuadraticMap.polar (B.baseChange 𝕜).toQuadraticMap (a • (1 ⊗ₜ v)) (c • (1 ⊗ₜ t)) =
      2 * (a * c) := by
  rw [BilinMap.polar_toQuadraticMap]
  simp [hvt, htv]
  ring

/-- The line through `1 ⊗ x` is totally isotropic for `B_𝕜` when `x` is isotropic for `B`. -/
private theorem isTotallyIsotropic_span_one_tmul {x : H} (hx : B x x = 0) :
    (B.baseChange 𝕜).toQuadraticMap.IsTotallyIsotropic (𝕜 ∙ ((1 : 𝕜) ⊗ₜ[ℤ] x)) :=
  QuadraticMap.isTotallyIsotropic_span_singleton_iff.mpr <| by
    simp [BilinMap.toQuadraticMap_apply, hx]

variable [CharZero 𝕜]

/-- For a hyperbolic pair `v, t`, a multiple of `1 ⊗ v` and a multiple of `1 ⊗ t` which are
polar-orthogonal for `B_𝕜` cannot both be nonzero. -/
private theorem eq_zero_or_eq_zero_of_polar_toQuadraticMap_baseChange_eq_zero (hvt : B v t = 1)
    (htv : B t v = 1) {a c : 𝕜}
    (h : QuadraticMap.polar (B.baseChange 𝕜).toQuadraticMap (a • (1 ⊗ₜ v)) (c • (1 ⊗ₜ t)) = 0) :
    a = 0 ∨ c = 0 := by
  rw [polar_toQuadraticMap_baseChange_smul_one_tmul hvt htv] at h
  simpa using h

/-- For a hyperbolic pair `v, t`, the tensors `1 ⊗ v` and `1 ⊗ t` are nonzero, since their polar
pairing for `B_𝕜` is `2`. -/
private theorem one_tmul_ne_zero (hvt : B v t = 1) (htv : B t v = 1) :
    (1 : 𝕜) ⊗ₜ[ℤ] v ≠ 0 ∧ (1 : 𝕜) ⊗ₜ[ℤ] t ≠ 0 := by
  have h := polar_toQuadraticMap_baseChange_smul_one_tmul (𝕜 := 𝕜) hvt htv 1 1
  rw [one_smul, one_smul, mul_one, mul_one] at h
  constructor <;> intro h0
  · rw [h0, QuadraticMap.polar_zero_left] at h
    exact two_ne_zero h.symm
  · rw [h0, QuadraticMap.polar_zero_right] at h
    exact two_ne_zero h.symm

/-- If `v, t` is a hyperbolic pair spanning `H` modulo torsion, then `𝕜 ⊗[ℤ] H` is the direct sum
of the lines through `1 ⊗ v` and `1 ⊗ t`. -/
private theorem isCompl_span_one_tmul (ht : B t t = 0) (hvt : B v t = 1) (htv : B t v = 1)
    (hspan : ∀ x : H, ∃ a c : ℤ, IsOfFinAddOrder (x - (a • v + c • t))) :
    IsCompl (𝕜 ∙ ((1 : 𝕜) ⊗ₜ[ℤ] v)) (𝕜 ∙ ((1 : 𝕜) ⊗ₜ[ℤ] t)) := by
  -- The torsion of `H` dies in `𝕜 ⊗[ℤ] H`, so the two lines span it.
  have hsup : 𝕜 ∙ ((1 : 𝕜) ⊗ₜ[ℤ] v) ⊔ 𝕜 ∙ ((1 : 𝕜) ⊗ₜ[ℤ] t) = ⊤ := by
    have h := TauCeti.span_one_tmul_eq_top_of_isOfFinAddOrder (A := 𝕜) (s := {v, t}) fun x ↦ by
      obtain ⟨a, c, hx⟩ := hspan x
      exact ⟨a • v + c • t, add_mem (zsmul_mem (AddSubgroup.subset_closure (by simp)) a)
        (zsmul_mem (AddSubgroup.subset_closure (by simp)) c), hx⟩
    rwa [Set.image_pair, Submodule.span_insert] at h
  refine ⟨Submodule.disjoint_def.mpr fun x hxv hxt ↦ ?_, codisjoint_iff.mpr hsup⟩
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hxv
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hxt
  -- Pair `a • (1 ⊗ v) = c • (1 ⊗ t)` with `1 ⊗ t`: the left side gives `2a`, the right side
  -- gives `0` because `1 ⊗ t` is isotropic.
  have h : QuadraticMap.polar (B.baseChange 𝕜).toQuadraticMap (a • (1 ⊗ₜ v)) ((1 : 𝕜) • (1 ⊗ₜ t))
      = 0 := by
    rw [← hc, one_smul, QuadraticMap.polar_smul_left, QuadraticMap.polar_self]
    simp [BilinMap.toQuadraticMap_apply, ht]
  rcases eq_zero_or_eq_zero_of_polar_toQuadraticMap_baseChange_eq_zero hvt htv h with rfl | h1
  · exact zero_smul _ _
  · exact absurd h1 one_ne_zero

/-- **The scalar extension of a form spanned by a hyperbolic pair is a plane.** If `v, t` is a
hyperbolic pair of a `ℤ`-valued form `B` spanning `H` modulo torsion, then `𝕜 ⊗[ℤ] H` has
dimension two over any field `𝕜` of characteristic zero. When `B` is the intersection form on
`H = H²(X; ℤ)` of a closed oriented four-manifold `X`, this is `b₂(X) = 2`. -/
theorem finrank_tensorProduct_eq_two_of_isOfFinAddOrder_span (ht : B t t = 0) (hvt : B v t = 1)
    (htv : B t v = 1) (hspan : ∀ x : H, ∃ a c : ℤ, IsOfFinAddOrder (x - (a • v + c • t))) :
    Module.finrank 𝕜 (𝕜 ⊗[ℤ] H) = 2 := by
  have hAB := isCompl_span_one_tmul (𝕜 := 𝕜) ht hvt htv hspan
  have : Module.Finite 𝕜 (𝕜 ⊗[ℤ] H) := ⟨by
    rw [← hAB.sup_eq_top]
    exact (Submodule.fg_span_singleton _).sup (Submodule.fg_span_singleton _)⟩
  obtain ⟨hv0, ht0⟩ := one_tmul_ne_zero (𝕜 := 𝕜) hvt htv
  rw [← Submodule.finrank_add_eq_of_isCompl hAB, finrank_span_singleton hv0,
    finrank_span_singleton ht0]

/-- **The scalar extension of a form spanned by a hyperbolic pair is nondegenerate.** If `v, t` is
a hyperbolic pair of a `ℤ`-valued form `B` spanning `H` modulo torsion, then over any field `𝕜` of
characteristic zero the quadratic form `x ↦ B_𝕜 x x` on `𝕜 ⊗[ℤ] H` is nondegenerate. -/
theorem nondegenerate_toQuadraticMap_baseChange_of_isOfFinAddOrder_span (ht : B t t = 0)
    (hvt : B v t = 1) (htv : B t v = 1)
    (hspan : ∀ x : H, ∃ a c : ℤ, IsOfFinAddOrder (x - (a • v + c • t))) :
    (B.baseChange 𝕜).toQuadraticMap.Nondegenerate := by
  have hline (x : H) : (1 : 𝕜) • ((1 : 𝕜) ⊗ₜ[ℤ] x) ∈ 𝕜 ∙ ((1 : 𝕜) ⊗ₜ[ℤ] x) :=
    Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  refine QuadraticMap.nondegenerate_of_isCompl (isCompl_span_one_tmul ht hvt htv hspan)
    (isTotallyIsotropic_span_one_tmul ht) (fun x hx h ↦ ?_) (fun y hy h ↦ ?_)
  · obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
    rcases eq_zero_or_eq_zero_of_polar_toQuadraticMap_baseChange_eq_zero hvt htv
      (h _ (hline t)) with rfl | h1
    · exact zero_smul _ _
    · exact absurd h1 one_ne_zero
  · obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy
    rcases eq_zero_or_eq_zero_of_polar_toQuadraticMap_baseChange_eq_zero hvt htv
      (h _ (hline v)) with h1 | rfl
    · exact absurd h1 one_ne_zero
    · exact zero_smul _ _

variable [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

/-- **Positive index one.** If `v, t` is a hyperbolic pair of a `ℤ`-valued form `B` spanning `H`
modulo torsion, then over a linearly ordered field `𝕜` the quadratic form `x ↦ B_𝕜 x x` on
`𝕜 ⊗[ℤ] H` has positive index of inertia one. When `B` is the intersection form on
`H = H²(X; ℤ)` of a closed oriented four-manifold `X` and `𝕜 = ℝ`, this is `b₂⁺(X) = 1`. -/
theorem sigPos_toQuadraticMap_baseChange_eq_one_of_isOfFinAddOrder_span (hv : B v v = 0)
    (ht : B t t = 0) (hvt : B v t = 1) (htv : B t v = 1)
    (hspan : ∀ x : H, ∃ a c : ℤ, IsOfFinAddOrder (x - (a • v + c • t))) :
    sigPos (B.baseChange 𝕜).toQuadraticMap = 1 := by
  have : FiniteDimensional 𝕜 (𝕜 ⊗[ℤ] H) := Module.finite_of_finrank_eq_succ
    (finrank_tensorProduct_eq_two_of_isOfFinAddOrder_span ht hvt htv hspan)
  rw [QuadraticForm.sigPos_eq_finrank_of_isCompl _
      (nondegenerate_toQuadraticMap_baseChange_of_isOfFinAddOrder_span ht hvt htv hspan)
      (isCompl_span_one_tmul ht hvt htv hspan)
      (isTotallyIsotropic_span_one_tmul hv)
      (isTotallyIsotropic_span_one_tmul ht),
    finrank_span_singleton (one_tmul_ne_zero hvt htv).1]

/-- **Negative index one.** If `v, t` is a hyperbolic pair of a `ℤ`-valued form `B` spanning `H`
modulo torsion, then over a linearly ordered field `𝕜` the quadratic form `x ↦ B_𝕜 x x` on
`𝕜 ⊗[ℤ] H` has negative index of inertia one. When `B` is the intersection form on
`H = H²(X; ℤ)` of a closed oriented four-manifold `X` and `𝕜 = ℝ`, this is `b₂⁻(X) = 1`. -/
theorem sigNeg_toQuadraticMap_baseChange_eq_one_of_isOfFinAddOrder_span (hv : B v v = 0)
    (ht : B t t = 0) (hvt : B v t = 1) (htv : B t v = 1)
    (hspan : ∀ x : H, ∃ a c : ℤ, IsOfFinAddOrder (x - (a • v + c • t))) :
    sigNeg (B.baseChange 𝕜).toQuadraticMap = 1 := by
  rw [QuadraticForm.sigNeg_eq_sigPos_of_isCompl _ (isCompl_span_one_tmul ht hvt htv hspan)
      (isTotallyIsotropic_span_one_tmul hv)
      (isTotallyIsotropic_span_one_tmul ht),
    sigPos_toQuadraticMap_baseChange_eq_one_of_isOfFinAddOrder_span hv ht hvt htv hspan]

end LinearMap.BilinForm
