/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.IdealSheaf.EulerCharacteristic
public import TauCeti.AlgebraicGeometry.Curves.Degree
public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Finite
public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Invertible

/-!
# The Euler-characteristic degree of an effective Cartier divisor

Let `X` be a scheme over a field `k` and `I ⊆ 𝒪_X` an ideal sheaf whose closed subscheme
`D = V(I)` is finite over `k`, of rank `dim_k Γ(D, 𝒪_D)`. The exact sequence
`0 ⟶ I ⟶ 𝒪_X ⟶ ι_* 𝒪_D ⟶ 0` and the vanishing of higher cohomology on the affine Noetherian
scheme `D` give

  `χ(I) = χ(𝒪_X) - dim_k Γ(D, 𝒪_D)`

(`Scheme.IdealSheafData.eulerCharBelow_sheaf`, in
`TauCeti.AlgebraicGeometry.IdealSheaf.EulerCharacteristic`), where `χ` is the degree-`2` truncation
`dim H⁰ - dim H¹` and `H⁰(X, 𝒪_X)`, `H¹(X, 𝒪_X)` are assumed finite-dimensional. When `I` is the
ideal sheaf `𝒪_X(-D)` of an effective Cartier divisor `D`, this says that the line bundle `𝒪_X(-D)`
has Euler-characteristic degree `-dim_k Γ(D, 𝒪_D)`
(`Scheme.IdealSheafData.IsEffectiveCartier.eulerDegree_toInvertibleSheaf`).

Twisting the exact sequence by a line bundle `L` with finite-dimensional `H⁰` and `H¹` gives
`χ(L ⊗ I) = χ(L) - dim_k Γ(D, 𝒪_D)` (`Scheme.IdealSheafData.eulerCharBelow_tensor_sheaf`), so
twisting by `𝒪_X(-D)` and by `𝒪_X(D)` is additive on degrees
(`Scheme.IdealSheafData.IsEffectiveCartier.eulerDegree_mk_mul_mk_toInvertibleSheaf` and
`Scheme.IdealSheafData.IsEffectiveCartier.eulerDegree_mk_mul_inv_mk_toInvertibleSheaf`), without
any integrality or regularity of `X`. In particular `𝒪_X(D)` has degree `dim_k Γ(D, 𝒪_D)`
(`Scheme.IdealSheafData.IsEffectiveCartier.eulerDegree_inv_mk_toInvertibleSheaf`); on a connected
smooth proper curve over `k` the finiteness hypotheses hold automatically
(`Scheme.IdealSheafData.IsEffectiveCartier.eulerDegree_inv_mk_toInvertibleSheaf_of_smooth`).
This is the classical `deg 𝒪_X(D) = deg D` for effective divisors, with the degree of `D` read off
as the rank of its closed subscheme, the notion of degree used for relative effective Cartier
divisors in families.

The rank is Mathlib's `Scheme.Hom.finrank` of the finite morphism `D ⟶ Spec k`, evaluated at the
unique point of `Spec k`; it is `dim_k Γ(D, 𝒪_D)` by
`AlgebraicGeometry.Scheme.Hom.finrank_eq_finrank_of_field`.

## References

* R. Hartshorne, *Algebraic Geometry*: Proposition II.6.18 (`𝒪_X(-D)` is the ideal sheaf of
  `D`), Lemma III.2.10 and Theorem III.3.5 (the cohomology of `𝒪_D`), and the proof of
  Theorem IV.1.3 (Riemann–Roch), where degrees are computed from the same kind of exact
  sequence.
* [The Stacks Project, Section 33.44](https://stacks.math.columbia.edu/tag/0AYQ): degrees on
  proper curves, and the change of Euler characteristic under twisting by an effective Cartier
  divisor.
-/

public section

open CategoryTheory Limits MonoidalCategory AlgebraicGeometry Order
open TauCeti.AlgebraicGeometry Scheme.Modules

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

noncomputable section

variable (k : Type u) [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))] (I : X.IdealSheafData)

section Finite

variable [IsFinite (I.subschemeι ≫ X ↘ Spec (.of k))]

section FiniteCohomology

variable [FiniteDimensional k (Cohomology (InvertibleSheaf.trivial X).obj 0)]
  [FiniteDimensional k (Cohomology (InvertibleSheaf.trivial X).obj 1)]

/-- **The degree of `𝒪_X(-D)`.** On a scheme over a field `k` with finite-dimensional
`H⁰(X, 𝒪_X)` and `H¹(X, 𝒪_X)`, the ideal sheaf `𝒪_X(-D)` of an effective Cartier divisor `D`
finite over `k` has Euler-characteristic degree `-dim_k Γ(D, 𝒪_D)`, the negative of the rank of
`D ⟶ Spec k`. -/
theorem IsEffectiveCartier.eulerDegree_toInvertibleSheaf (hI : I.IsEffectiveCartier)
    (s : Spec (.of k)) :
    hI.toInvertibleSheaf.eulerDegree k = -((I.subschemeι ≫ X ↘ Spec (.of k)).finrank s : ℤ) := by
  rw [InvertibleSheaf.eulerDegree_def, IsEffectiveCartier.toInvertibleSheaf_obj,
    eulerCharBelow_sheaf k I s]
  ring

/-- **Twisting by `𝒪_X(-D)` lowers the degree by `deg D`.** On a scheme over a field `k` with
finite-dimensional `H⁰(X, 𝒪_X)` and `H¹(X, 𝒪_X)`, let `D` be an effective Cartier divisor finite
over `k` and `L` a line bundle with finite-dimensional `H⁰(X, L)` and `H¹(X, L)`. Then
`deg (L ⊗ 𝒪_X(-D)) = deg L + deg 𝒪_X(-D)`. No integrality or regularity of `X` is needed. -/
theorem IsEffectiveCartier.eulerDegree_mk_mul_mk_toInvertibleSheaf (hI : I.IsEffectiveCartier)
    (L : InvertibleSheaf X) [FiniteDimensional k (Cohomology L.obj 0)]
    [FiniteDimensional k (Cohomology L.obj 1)] :
    LineBundleClass.eulerDegree k
        (LineBundleClass.mk L * LineBundleClass.mk hI.toInvertibleSheaf) =
      L.eulerDegree k + hI.toInvertibleSheaf.eulerDegree k := by
  rw [hI.eulerDegree_toInvertibleSheaf k I default, ← LineBundleClass.mk_tensorProduct,
    LineBundleClass.eulerDegree_mk, InvertibleSheaf.eulerDegree_def,
    InvertibleSheaf.eulerDegree_def,
    eulerCharBelow_congr k (InvertibleSheaf.tensorProductObjIso _ _) 2,
    IsEffectiveCartier.toInvertibleSheaf_obj, eulerCharBelow_tensor_sheaf k I L default]
  ring

/-- **Twisting by `𝒪_X(D)` raises the degree by `deg D`.** On a scheme over a field `k` with
finite-dimensional `H⁰(X, 𝒪_X)` and `H¹(X, 𝒪_X)`, let `D` be an effective Cartier divisor finite
over `k` and `L` a line bundle with finite-dimensional `H⁰(X, L)` and `H¹(X, L)`. Then
`deg (L ⊗ 𝒪_X(D)) = deg L - deg 𝒪_X(-D)`, the class of `𝒪_X(D)` being the inverse of that of
`𝒪_X(-D)`. -/
theorem IsEffectiveCartier.eulerDegree_mk_mul_inv_mk_toInvertibleSheaf
    (hI : I.IsEffectiveCartier) (L : InvertibleSheaf X) [FiniteDimensional k (Cohomology L.obj 0)]
    [FiniteDimensional k (Cohomology L.obj 1)] :
    LineBundleClass.eulerDegree k
        (LineBundleClass.mk L * (LineBundleClass.mk hI.toInvertibleSheaf)⁻¹) =
      L.eulerDegree k - hI.toInvertibleSheaf.eulerDegree k := by
  obtain ⟨M, hM⟩ := LineBundleClass.mk_surjective
    (LineBundleClass.mk L * (LineBundleClass.mk hI.toInvertibleSheaf)⁻¹)
  -- `M ⊗ 𝒪_X(-D)` is isomorphic to `L`, so `M` has finite-dimensional `H⁰` and `H¹` too.
  have hML : LineBundleClass.mk M * LineBundleClass.mk hI.toInvertibleSheaf =
      LineBundleClass.mk L := by
    rw [hM, inv_mul_cancel_right]
  obtain ⟨e⟩ := LineBundleClass.mk_eq_mk_iff.mp
    ((LineBundleClass.mk_tensorProduct M hI.toInvertibleSheaf).trans hML)
  let e' : M.obj ⊗ I.sheaf ≅ L.obj :=
    eqToIso (by rw [IsEffectiveCartier.toInvertibleSheaf_obj]) ≪≫
      (InvertibleSheaf.tensorProductObjIso M hI.toInvertibleSheaf).symm ≪≫ e
  have hfin := (I.finiteDimensional_cohomology_tensor_sheaf_iff (k := k) (L := M)).mp fun i hi ↦
    (finiteDimensional_cohomology_congr k e' i).mpr (by interval_cases i <;> infer_instance)
  have := hfin 0 (by omega)
  have := hfin 1 (by omega)
  have h := hI.eulerDegree_mk_mul_mk_toInvertibleSheaf k I M
  rw [hML, LineBundleClass.eulerDegree_mk] at h
  rw [← hM, LineBundleClass.eulerDegree_mk, h, add_sub_cancel_right]

/-- **The degree of `𝒪_X(D)`.** On a scheme over a field `k` with finite-dimensional
`H⁰(X, 𝒪_X)` and `H¹(X, 𝒪_X)`, as for a proper curve, the line bundle `𝒪_X(D)` of an
effective Cartier divisor `D` finite over `k` has Euler-characteristic degree `dim_k Γ(D, 𝒪_D)`,
the rank of the finite morphism `D ⟶ Spec k`. No integrality or regularity of `X` is needed. -/
theorem IsEffectiveCartier.eulerDegree_inv_mk_toInvertibleSheaf (hI : I.IsEffectiveCartier)
    (s : Spec (.of k)) :
    LineBundleClass.eulerDegree k (LineBundleClass.mk hI.toInvertibleSheaf)⁻¹ =
      (I.subschemeι ≫ X ↘ Spec (.of k)).finrank s := by
  have h := hI.eulerDegree_mk_mul_inv_mk_toInvertibleSheaf k I (InvertibleSheaf.trivial X)
  rw [LineBundleClass.mk_trivial, one_mul, InvertibleSheaf.eulerDegree_trivial,
    hI.eulerDegree_toInvertibleSheaf k I s, zero_sub, neg_neg] at h
  exact h

end FiniteCohomology

end Finite

section Smooth

variable [IsProper (X ↘ Spec (.of k))] [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))]
  [ConnectedSpace X]

/-- **The degree of `𝒪_X(D)` on a smooth curve.** On a connected smooth proper curve over a
field `k`, the line bundle `𝒪_X(D)` of an effective Cartier divisor `D` has Euler-characteristic
degree `dim_k Γ(D, 𝒪_D)`, the rank of the finite morphism `D ⟶ Spec k`. The geometric
hypotheses supply integrality, discrete valuation rings in codimension one and the finiteness of
`H¹(X, 𝒪_X)`; no rational point or perfect-field assumption is needed. -/
theorem IsEffectiveCartier.eulerDegree_inv_mk_toInvertibleSheaf_of_smooth
    (hI : I.IsEffectiveCartier) (s : Spec (.of k)) :
    LineBundleClass.eulerDegree k (LineBundleClass.mk hI.toInvertibleSheaf)⁻¹ =
      (I.subschemeι ≫ X ↘ Spec (.of k)).finrank s := by
  have := SmoothOfRelativeDimension.smooth 1 (X ↘ Spec (.of k))
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  have : ∀ x : X, IsRegularLocalRing (X.presheaf.stalk x) :=
    isRegularLocalRing_stalk_of_smooth (X ↘ Spec (.of k))
  have : IsIntegral X := isIntegral_of_connected_of_isRegularLocalRing_stalk X
  have : ∀ x : CodimensionOnePoint X, IsDiscreteValuationRing (X.presheaf.stalk (x : X)) :=
    fun x ↦ inferInstance
  have hdim : topologicalKrullDim X = 1 :=
    topologicalKrullDim_eq_of_smoothOfRelativeDimension (X ↘ Spec (.of k))
  have := finiteDimensional_cohomology_one_trivial_of_isProper k hdim
  have : RelativeDimensionLE 1 (X ↘ Spec (.of k)) :=
    (relativeDimensionLE_iff_of_field _).mpr (by exact_mod_cast hdim.le)
  -- Over a field every effective Cartier divisor is relative, hence finite over `k`.
  have : IsFinite (I.subschemeι ≫ X ↘ Spec (.of k)) := hI.isFinite_subschemeι_comp
  have := InvertibleSheaf.finiteDimensional_cohomology_zero k
    (coheight_le_of_relativeDimensionLE_of_field (d := 1) (X ↘ Spec (.of k)))
    (InvertibleSheaf.trivial X)
  exact hI.eulerDegree_inv_mk_toInvertibleSheaf k I s

end Smooth

end

end AlgebraicGeometry.Scheme.IdealSheafData
