/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Action.CrossedProduct.Universal
public import TauCeti.Analysis.CStarAlgebra.Action.Ideal

/-!
# Surjectivity of full crossed-product maps

An equivariant coefficient homomorphism `φ : Hom α β` with dense range induces a surjective
homomorphism `φ.fullCrossedProductMap μ` of full crossed products, with no `T2Space G`,
separability, σ-finiteness, or unitality assumption. In particular, the canonical homomorphism from
the full crossed product to that of a closed invariant-ideal quotient is onto, establishing the
right endpoint of the invariant-ideal short exact sequence.

Because C⋆-homomorphisms have closed range (`NonUnitalStarAlgHom.surjective_of_denseRange`,
`NonUnitalStarAlgHom.isClosed_range`), `φ` is surjective on coefficients and
`R := (φ.fullCrossedProductMap μ).range` is a closed `⋆`-subalgebra of `FullCrossedProduct β μ`
invariant under all canonical left multipliers `i_B(b)` and `i_G(r)`. Commuting the Bochner integral
`FullCrossedProduct.integral_coefficientMultiplier_mul_groupMultiplier_fst` with the isometric
inclusion of `R` shows that `R` is a closed two-sided ideal `J`, and disintegrating the quotient
map `FullCrossedProduct β μ →⋆ₙₐ[ℂ] 𝓜(ℂ, (FullCrossedProduct β μ) ⧸ J)` via
`NonUnitalStarAlgHom.toCovariantMultiplierHom` forces `(FullCrossedProduct β μ) ⧸ J` to vanish.

## References

* Dana Williams, *Crossed Products of C*-Algebras*, Proposition 3.19.
* Iain Raeburn, *On crossed products and Takai duality*, Proc. Edinburgh Math. Soc. 31 (1988),
  321–330.
-/

public section

noncomputable section

open MeasureTheory TauCeti
open scoped CStarAlgebra MultiplierAlgebra

namespace TauCeti.CStarAction

universe u v

variable {G : Type u} {A B : Type v} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [LocallyCompactSpace G]
  [MeasurableSpace G] [BorelSpace G]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  {α : CStarAction G A} {β : CStarAction G B}
  (μ : Measure G) [μ.IsHaarMeasure]

namespace Hom

open FullCrossedProduct

private theorem mul_mem_range_fullCrossedProductMap_left (φ : Hom α β)
    (hsurj : Function.Surjective φ) (z : FullCrossedProduct β μ)
    {y : FullCrossedProduct β μ} (hy : y ∈ (φ.fullCrossedProductMap μ).range) :
    z * y ∈ (φ.fullCrossedProductMap μ).range := by
  let R := (φ.fullCrossedProductMap μ).range
  induction z using FullCrossedProduct.induction_on with
  | hp =>
    exact (NonUnitalStarAlgHom.isClosed_range (φ.fullCrossedProductMap μ)).preimage
      (continuous_mul_const y)
  | ih g =>
    have hmem (s : G) :
        (coefficientMultiplier β μ (g.ofConv s) *
          (groupMultiplier β μ s : 𝓜(ℂ, FullCrossedProduct β μ))).fst y ∈ R := by
      obtain ⟨a, ha⟩ := hsurj (g.ofConv s)
      obtain ⟨x, rfl⟩ := (φ.fullCrossedProductMap μ).mem_range.mp hy
      exact (φ.fullCrossedProductMap μ).mem_range.mpr
        ⟨(coefficientMultiplier α μ a).fst
          ((groupMultiplier α μ s : 𝓜(ℂ, FullCrossedProduct α μ)).fst x),
          by simp [ha, DoubleCentralizer.mul_fst]⟩
    have : CompleteSpace R.toSubmodule :=
      (NonUnitalStarAlgHom.isClosed_range (φ.fullCrossedProductMap μ)).completeSpace_coe
    let F : G → R := fun s => ⟨_, hmem s⟩
    have hint := R.toSubmodule.subtypeₗᵢ.integral_comp_comm (μ := μ) F
    simp only [Submodule.coe_subtypeₗᵢ, Submodule.subtype_apply, F] at hint
    rw [integral_coefficientMultiplier_mul_groupMultiplier_fst] at hint
    exact hint ▸ (∫ s, F s ∂μ).property

/-- A dense-range equivariant coefficient homomorphism induces a surjective full
crossed-product homomorphism. For a surjective coefficient map, use `hφ.denseRange`. -/
theorem surjective_fullCrossedProductMap (φ : Hom α β) (hφ : DenseRange φ) :
    Function.Surjective (φ.fullCrossedProductMap μ) := by
  have hsurj : Function.Surjective φ :=
    NonUnitalStarAlgHom.surjective_of_denseRange (φ := φ.toNonUnitalStarAlgHom) hφ
  let R := (φ.fullCrossedProductMap μ).range
  let J : TwoSidedIdeal (FullCrossedProduct β μ) :=
    TwoSidedIdeal.mk' (R : Set (FullCrossedProduct β μ)) R.zero_mem
      (fun hx hy => R.add_mem hx hy) (fun hx => R.neg_mem hx)
      (fun hy => mul_mem_range_fullCrossedProductMap_left μ φ hsurj _ hy)
      (fun hx => StarMemClass.mul_mem_right_of_mul_mem_left
        (mul_mem_range_fullCrossedProductMap_left μ φ hsurj) _ hx)
  have hJ : (J : Set (FullCrossedProduct β μ)) = R := by simp [J]
  have : IsClosed (J : Set (FullCrossedProduct β μ)) :=
    hJ ▸ NonUnitalStarAlgHom.isClosed_range (φ.fullCrossedProductMap μ)
  let ψ := TwoSidedIdeal.Quotient.mkStarAlgHom J
  have hΦ : ((DoubleCentralizer.coeHom (𝕜 := ℂ)).comp ψ).IsMultiplierNondegenerate :=
    NonUnitalStarAlgHom.isMultiplierNondegenerate_coeHom_comp
      (TwoSidedIdeal.Quotient.mkStarAlgHom_surjective J).denseRange
  let M := ((DoubleCentralizer.coeHom (𝕜 := ℂ)).comp ψ).toCovariantMultiplierHom hΦ
  have hM0 : M.coefficient = 0 := by
    refine NonUnitalStarAlgHom.ext fun b => ?_
    obtain ⟨a, rfl⟩ := hsurj b
    refine ((M.forall_mem_range_fullCrossedProductMap_integratedFull_eq_zero_iff μ φ).mp
      fun y hy => ?_) a
    have hyJ : y ∈ J := SetLike.mem_coe.mp (hJ.symm ▸ SetLike.mem_coe.mpr hy)
    have hψy : ψ y = 0 := (TwoSidedIdeal.Quotient.mkStarAlgHom_apply J y).trans
      (TwoSidedIdeal.Quotient.eq_zero_iff_mem.mpr hyJ)
    simp [M, hψy]
  have hzero : M.integratedFull μ = 0 := M.integratedFull_eq_zero_iff.mpr hM0
  rw [NonUnitalStarAlgHom.integratedFull_toCovariantMultiplierHom] at hzero
  intro y
  have hy : ψ y = 0 :=
    DoubleCentralizer.coe_injective (𝕜 := ℂ) (by simpa using DFunLike.congr_fun hzero y)
  have hyJ : y ∈ J := TwoSidedIdeal.Quotient.eq_zero_iff_mem.mp
    ((TwoSidedIdeal.Quotient.mkStarAlgHom_apply J y).symm.trans hy)
  exact (φ.fullCrossedProductMap μ).mem_range.mp
    (SetLike.mem_coe.mp (hJ ▸ SetLike.mem_coe.mpr hyJ))

end Hom

/-- The canonical homomorphism to the full crossed product of an invariant-ideal quotient is
surjective, including for nonunital coefficients and the zero quotient. -/
theorem surjective_fullCrossedProductMap_quotientMkHom (α : CStarAction G A)
    (I : TwoSidedIdeal A) [IsClosed (I : Set A)]
    (hI : IsInvariant (fun g a => α g a) (I : Set A)) :
    Function.Surjective ((α.quotientMkHom I hI).fullCrossedProductMap μ) :=
  (α.quotientMkHom I hI).surjective_fullCrossedProductMap μ
    (α.quotientMkHom_surjective I hI).denseRange

end TauCeti.CStarAction
