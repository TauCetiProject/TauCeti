/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
import TauCeti.RingTheory.Morita.ModuleEnd
import TauCeti.Analysis.InnerProductSpace.TensorProduct

/-!
# Sesquilinear forms across Morita evaluation

Suppose `A` acts on a finite-dimensional inner product space `S` as its full endomorphism
algebra. Any sesquilinear form `K` on the multiplicity space `Hom_A(S, E)` extends uniquely
to a form `H` on `E` with `H (T s) (U t) = inner 𝕜 s t * K T U`. This is the tensor-product
form transported through `TauCeti.isotypicTensorEquivOfBijective`.

In an orthonormal basis `(bᵢ)` of `S`, the components of a vector `x` are the intertwiners
`homOfDual h bᵢ* x`, and `H x y` is the sum of their `K`-pairings. The characterization
makes this construction independent of the basis. Positive definite Hermitian forms give
positive definite Hermitian extensions. Neither finite-dimensionality nor topology on `E`
is required; zero modules are included.

## References

* T. Y. Lam, *Lectures on Modules and Rings*, GTM 189 (1999), Chapter 7.
* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §5.
-/

public section

open scoped TensorProduct ComplexOrder

namespace TauCeti

variable {𝕜 A S E : Type*} [RCLike 𝕜] [Semiring A] [Algebra 𝕜 A]
  [NormedAddCommGroup S] [InnerProductSpace 𝕜 S] [FiniteDimensional 𝕜 S]
  [Module A S] [IsScalarTower 𝕜 A S]
  [AddCommGroup E] [Module 𝕜 E] [Module A E] [IsScalarTower 𝕜 A E]

/-- Every multiplicity form extends uniquely across Morita evaluation when the action on
`S` is an algebra isomorphism. No positivity or symmetry is needed. -/
theorem existsUnique_sesqForm_of_bijective_lsmul
    (hbij : Function.Bijective (Algebra.lsmul 𝕜 𝕜 S : A →ₐ[𝕜] Module.End 𝕜 S))
    (K : (S →ₗ[A] E) →ₗ⋆[𝕜] (S →ₗ[A] E) →ₗ[𝕜] 𝕜) :
    ∃! H : E →ₗ⋆[𝕜] E →ₗ[𝕜] 𝕜,
      ∀ T U s t, H (T s) (U t) = inner 𝕜 s t * K T U := by
  let b := stdOrthonormalBasis 𝕜 S
  let c := fun i ↦ homOfDual hbij (b.toBasis.coord i) (M := E)
  have hc (i) (T : S →ₗ[A] E) (s : S) :
      c i (T s) = inner 𝕜 (b i) s • T := by
    rw [homOfDual_apply_map]
    simp [Module.Basis.coord_apply, OrthonormalBasis.coe_toBasis_repr_apply,
      OrthonormalBasis.repr_apply_apply]
  have hdecomp (x : E) : ∑ i, c i x (b i) = x :=
    sum_homOfDual_coord_apply hbij b.toBasis x
  let H : E →ₗ⋆[𝕜] E →ₗ[𝕜] 𝕜 := ∑ i, (K.comp (c i)).compl₂ (c i)
  have hfactor (T U : S →ₗ[A] E) (s t : S) :
      H (T s) (U t) = inner 𝕜 s t * K T U := by
    simp only [H, LinearMap.sum_apply, LinearMap.compl₂_apply, LinearMap.comp_apply, hc,
      map_smul, map_smulₛₗ, LinearMap.smul_apply, starRingEnd_apply, smul_eq_mul]
    simp only [RCLike.star_def, inner_conj_symm]
    simp_rw [mul_left_comm (inner 𝕜 (b _) t), ← mul_assoc]
    rw [← Finset.sum_mul, b.sum_inner_mul_inner]
  refine ⟨H, hfactor, fun L hL ↦ ?_⟩
  ext x y
  conv_lhs => rw [← hdecomp x, ← hdecomp y]
  conv_rhs => rw [← hdecomp x, ← hdecomp y]
  simp only [map_sum, LinearMap.sum_apply, hL, hfactor]

/-- A positive definite Hermitian form on the multiplicity space extends to a positive
definite Hermitian form on the entire module, characterized by the evaluation equation. -/
theorem existsUnique_posDef_sesqForm_of_bijective_lsmul
    (hbij : Function.Bijective (Algebra.lsmul 𝕜 𝕜 S : A →ₐ[𝕜] Module.End 𝕜 S))
    (K : (S →ₗ[A] E) →ₗ⋆[𝕜] (S →ₗ[A] E) →ₗ[𝕜] 𝕜)
    (hpos : K.IsPosSemidef) (hdef : ∀ T, T ≠ 0 → K T T ≠ 0) :
    ∃! H : E →ₗ⋆[𝕜] E →ₗ[𝕜] 𝕜,
      (∀ T U s t, H (T s) (U t) = inner 𝕜 s t * K T U) ∧
        H.IsPosSemidef ∧ (∀ x, x ≠ 0 → H x x ≠ 0) := by
  obtain ⟨H, hfactor, huniq⟩ := existsUnique_sesqForm_of_bijective_lsmul hbij K
  let b := stdOrthonormalBasis 𝕜 S
  let c := fun i ↦ homOfDual hbij (b.toBasis.coord i) (M := E)
  have hdecomp (x : E) : ∑ i, c i x (b i) = x :=
    sum_homOfDual_coord_apply hbij b.toBasis x
  have hsum (x y : E) : H x y = ∑ i, K (c i x) (c i y) := by
    conv_lhs => rw [← hdecomp x, ← hdecomp y]
    simp [hfactor, b.inner_eq_ite]
  refine ⟨H, ⟨hfactor, ⟨⟨fun x y ↦ ?_⟩, ⟨fun x ↦ ?_⟩⟩, ?_⟩,
    fun L hL ↦ huniq L hL.1⟩
  · simp only [hsum, map_sum, hpos.isSymm.eq]
  · rw [hsum]
    exact Finset.sum_nonneg fun i _ ↦ hpos.isNonneg.nonneg _
  · intro x hx hzero
    let e := (isotypicTensorEquivOfBijective hbij (M := E)).restrictScalars 𝕜
    let G := (H.comp e.toLinearMap).compl₂ e.toLinearMap
    have hG (s T t U) : G (s ⊗ₜ T) (t ⊗ₜ U) = inner 𝕜 s t * K T U := by
      simp [G, e, hfactor]
    have hinner : (innerₛₗ 𝕜 : S →ₗ⋆[𝕜] S →ₗ[𝕜] 𝕜).IsSymm :=
      ⟨fun s t ↦ inner_conj_symm t s⟩
    have hgt := apply_self_pos_of_apply_tmul_tmul hG hinner hpos.isSymm
      (fun s hs ↦ RCLike.pos_iff.mpr ⟨re_inner_self_pos.mpr hs, inner_self_im s⟩)
      (fun T hT ↦ lt_of_le_of_ne (hpos.isNonneg.nonneg T) (hdef T hT).symm)
      (x := e.symm x) (by simpa using hx)
    exact hgt.ne' (by simpa [G] using hzero)

end TauCeti
