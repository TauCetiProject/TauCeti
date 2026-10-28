/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.Ideles.Norm.One
public import TauCeti.Topology.Algebra.ContinuousMonoidHom.KerProdEquiv
public import TauCeti.Topology.Algebra.ContinuousMonoidHom.QuotientKerEquiv
public import TauCeti.Topology.Algebra.Group.ClosedSubgroup

/-!
# The norm quotient of the idele class group

The idele class norm `‖·‖ : C_K → ℝ>0` of a number field `K` has a continuous homomorphic
section. Fix an infinite place `w` of `K`, with multiplicity `m_w ∈ {1, 2}`. The idele whose
`w`-coordinate is the positive real number `t ^ (1 / m_w)` and whose other coordinates are `1`
(`TauCeti.GlobalNumberFields.ideleNormSection`) has idele norm `t`, because the normalized absolute
value at `w` is `|·| ^ m_w`; its class is a section of the idele class norm.

A continuous map with a continuous right inverse is a quotient map, and a quotient homomorphism of
topological groups is open. So the idele norm and the idele class norm are open quotient maps,
and the topological first isomorphism theorem identifies the **norm quotient**
`C_K / C_K¹` with `ℝ>0` as a topological group. This refines the non-compactness of the full
idele class group (`TauCeti.GlobalNumberFields.IdeleClassGroup.noncompactSpace`), in contrast to
the compact norm-one idele class group `C_K¹`. The section also splits the idele class group as a
topological group: `C_K ≃ C_K¹ × ℝ>0`.

## Main definitions

* `TauCeti.GlobalNumberFields.ideleClassNormSection`: the continuous section of the idele class
  norm at an infinite place, the class of `TauCeti.GlobalNumberFields.ideleNormSection`.
* `TauCeti.GlobalNumberFields.quotientNormOneEquiv`: the isomorphism of
  topological groups `C_K / C_K¹ ≃ₜ* ℝ>0` induced by the idele class norm.
* `TauCeti.GlobalNumberFields.normOneProdEquiv`: the splitting
  `C_K ≃ₜ* C_K¹ × ℝ>0` determined by an infinite place, an instance of
  `ContinuousMulEquiv.kerProdOfRightInverse`.

## Main results

* `TauCeti.GlobalNumberFields.ideleClassNorm_ideleClassNormSection`: the section is right
  inverse to the idele class norm.
* `TauCeti.GlobalNumberFields.isOpenQuotientMap_ideleNorm` and
  `TauCeti.GlobalNumberFields.isOpenQuotientMap_ideleClassNorm`: the norms are open quotient maps.
* `TauCeti.GlobalNumberFields.quotientNormOneEquiv_mk`: the norm quotient
  isomorphism is induced by the idele class norm.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VI, §1.
* J. W. S. Cassels and A. Fröhlich, eds., *Algebraic Number Theory*, Chapter II, §16.
-/

public section
noncomputable section

open IsDedekindDomain NumberField NumberField.InfinitePlace
open scoped NNReal

namespace TauCeti.GlobalNumberFields

variable {K : Type*} [Field K] [NumberField K]

/-! ### The section at one infinite place -/

variable (K) in
/-- The continuous section of the idele class norm at the infinite place `w`: the class of
`ideleNormSection K w t`. -/
def ideleClassNormSection (w : InfinitePlace K) : ℝ≥0ˣ →ₜ* IdeleClassGroup (𝓞 K) K where
  toMonoidHom := (QuotientGroup.mk' _).comp (ideleNormSection K w).toMonoidHom
  continuous_toFun := continuous_quot_mk.comp (ideleNormSection K w).continuous

/-- The section of the idele class norm at `w` is the class of the section of the idele norm. -/
theorem ideleClassNormSection_apply (w : InfinitePlace K) (t : ℝ≥0ˣ) :
    ideleClassNormSection K w t = (ideleNormSection K w t : IdeleClassGroup (𝓞 K) K) :=
  (rfl)

/-- **The section is right inverse to the idele class norm.** -/
@[simp]
theorem ideleClassNorm_ideleClassNormSection (w : InfinitePlace K) (t : ℝ≥0ˣ) :
    ideleClassNorm (ideleClassNormSection K w t) = t := by
  rw [ideleClassNormSection_apply, ideleClassNorm_mk, ideleNorm_ideleNormSection]

/-! ### The norms are open quotient maps -/

/-- The idele norm is an open quotient map onto `ℝ>0`: it has a continuous section. -/
theorem isOpenQuotientMap_ideleNorm : IsOpenQuotientMap (ideleNorm (K := K)) := by
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace K))
  exact MonoidHom.isOpenQuotientMap_of_isQuotientMap <|
    .of_inverse (ideleNormSection K w).continuous continuous_ideleNorm
      (ideleNorm_ideleNormSection w)

/-- The idele class norm is an open quotient map onto `ℝ>0`: it has a continuous section. -/
theorem isOpenQuotientMap_ideleClassNorm : IsOpenQuotientMap (ideleClassNorm (K := K)) := by
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace K))
  exact MonoidHom.isOpenQuotientMap_of_isQuotientMap <|
    .of_inverse (ideleClassNormSection K w).continuous continuous_ideleClassNorm
      (ideleClassNorm_ideleClassNormSection w)

/-! ### The norm quotient -/

section NormQuotient

open IdeleClassGroup

variable (K) in
/-- **The norm quotient of the idele class group is `ℝ>0`**: the idele class norm induces an
isomorphism of topological groups `C_K / C_K¹ ≃ₜ* ℝ>0`. -/
def quotientNormOneEquiv : IdeleClassGroup (𝓞 K) K ⧸ normOne K ≃ₜ* ℝ≥0ˣ :=
  -- `normOne K` is the kernel of the idele class norm, but not by unfolding outside its module.
  ((ContinuousMulEquiv.refl _).quotientCongr (normOne K) (ideleClassNorm (K := K)).ker <|
    Subgroup.ext fun _ ↦ by simp).trans <|
  ContinuousMulEquiv.quotientKerEquivOfSurjective (ideleClassNorm (K := K))
    ((isOpenQuotientMap_ideleClassNorm (K := K)).isOpenMap.isStrictMap
      (continuous_ideleClassNorm (K := K)))
    ideleClassNorm_surjective

/-- The norm quotient isomorphism sends the class of an idele class to its idele class norm. -/
@[simp]
theorem quotientNormOneEquiv_mk (c : IdeleClassGroup (𝓞 K) K) :
    quotientNormOneEquiv K (c : IdeleClassGroup (𝓞 K) K ⧸ normOne K) = ideleClassNorm c := by
  rw [quotientNormOneEquiv, ContinuousMulEquiv.trans_apply, ContinuousMulEquiv.quotientCongr_mk,
    ContinuousMulEquiv.quotientKerEquivOfSurjective_apply_mk, ContinuousMulEquiv.refl_apply]

/-! ### The splitting `C_K ≃ C_K¹ × ℝ>0` -/

/-- **The idele class group splits as `C_K¹ × ℝ>0`.** The infinite place `w` determines the
isomorphism of topological groups sending an idele class `c` to its norm-one part
`c · s(‖c‖)⁻¹` and its norm `‖c‖`, where `s = ideleClassNormSection K w`. -/
def normOneProdEquiv (w : InfinitePlace K) :
    IdeleClassGroup (𝓞 K) K ≃ₜ* normOne K × ℝ≥0ˣ :=
  -- The hypotheses are stated before use: unifying them inside the application has to match
  -- the commutative-group instance of `IdeleClassGroup` with the quotient group instance.
  let f : IdeleClassGroup (𝓞 K) K →ₜ* ℝ≥0ˣ := .mk ideleClassNorm continuous_ideleClassNorm
  have hs : Function.RightInverse (ideleClassNormSection K w) f :=
    ideleClassNorm_ideleClassNormSection w
  have hN (c : IdeleClassGroup (𝓞 K) K) : c ∈ normOne K ↔ f c = 1 := mem_normOne_iff
  ContinuousMulEquiv.kerProdOfRightInverse (G := IdeleClassGroup (𝓞 K) K) (H := ℝ≥0ˣ) f
    (ideleClassNormSection K w) hs hN

/-- The norm-one component of the splitting at `w` is `c · s(‖c‖)⁻¹`. -/
@[simp]
theorem coe_normOneProdEquiv_fst (w : InfinitePlace K) (c : IdeleClassGroup (𝓞 K) K) :
    ((normOneProdEquiv w c).1 : IdeleClassGroup (𝓞 K) K) =
      c * (ideleClassNormSection K w (ideleClassNorm c))⁻¹ := by
  rw [normOneProdEquiv, ContinuousMulEquiv.coe_kerProdOfRightInverse_apply_fst]
  rfl

/-- The `ℝ>0` component of the splitting is the idele class norm. -/
@[simp]
theorem normOneProdEquiv_snd (w : InfinitePlace K) (c : IdeleClassGroup (𝓞 K) K) :
    (normOneProdEquiv w c).2 = ideleClassNorm c := by
  rw [normOneProdEquiv, ContinuousMulEquiv.kerProdOfRightInverse_apply_snd]
  rfl

/-- The inverse of the splitting multiplies a norm-one idele class by the section at `w`. -/
@[simp]
theorem normOneProdEquiv_symm_apply (w : InfinitePlace K) (p : normOne K × ℝ≥0ˣ) :
    (normOneProdEquiv w).symm p = p.1 * ideleClassNormSection K w p.2 := by
  rw [normOneProdEquiv, ContinuousMulEquiv.kerProdOfRightInverse_symm_apply]

end NormQuotient

end TauCeti.GlobalNumberFields
