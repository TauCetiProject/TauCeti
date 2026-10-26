/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Dynamic.Levi.Representability
public import TauCeti.Algebra.AlgebraicGroup.Dynamic.Unipotent.Representability
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Tangent
public import Mathlib.LinearAlgebra.Prod

/-!
# Tangent spaces of the dynamic Levi decomposition

For a cocharacter `λ` of an affine group scheme, the tangent space of its dynamic parabolic
is the direct sum of the tangent spaces of its dynamic unipotent subgroup and its Levi.
The summands are regarded as submodules of the ambient counit-valued derivations. Addition
therefore gives a canonical linear equivalence `Lie U(λ) × Lie Z(λ) ≃ Lie P(λ)`.

This infinitesimal decomposition supplies the tangent-space calculation for dimension and
smoothness arguments involving dynamic subgroups. It works over arbitrary commutative base
rings and coefficient algebras, without finite-type, reducedness or smoothness assumptions.
It is a linear decomposition; the Lie bracket generally has nonzero mixed terms.

The proof uses the pointwise dynamic Levi factorization from `Dynamic.Parabolic` and its
naturality under reduction of dual numbers. The passage between subgroup tangent vectors and
dual-number points is `HopfIdeal.mem_quotientPointsSubgroup_derivationMulEquivTangentKer_iff`.

## References

* B. Conrad, O. Gabber, G. Prasad, *Pseudo-reductive Groups*, §2.1.
* J. S. Milne, *Algebraic Groups* (2017), §§10 and 13.
-/

public section

open WithConv TauCeti TauCeti.Cocharacter

namespace BialgHom

universe u v w

variable {R : Type u} {H : Type v} {B : Type w}
variable [CommRing R] [CommRing H] [HopfAlgebra R H] [CommRing B] [Algebra R B]

private theorem tangentPoint_mem_parabolic_iff (l : H →ₐc[R] LaurentPolynomial R)
    (d : Derivation R H (Bialgebra.CounitAlgebra R H B)) :
    (derivationMulEquivTangentKer R H B (.ofAdd d)).val ∈
        parabolic (DualNumber (Bialgebra.CounitAlgebra R H B)) l ↔
      d ∈ (parabolicDefiningHopfIdeal l).lieSubalgebra (B := B) := by
  rw [← quotientPointsSubgroup_parabolicDefiningHopfIdeal (A := DualNumber
    (Bialgebra.CounitAlgebra R H B)) l]
  exact HopfIdeal.mem_quotientPointsSubgroup_derivationMulEquivTangentKer_iff _ d

private theorem tangentPoint_mem_unipotent_iff (l : H →ₐc[R] LaurentPolynomial R)
    (d : Derivation R H (Bialgebra.CounitAlgebra R H B)) :
    (derivationMulEquivTangentKer R H B (.ofAdd d)).val ∈
        unipotent (DualNumber (Bialgebra.CounitAlgebra R H B)) l ↔
      d ∈ (l.unipotentDefiningHopfIdeal).lieSubalgebra (B := B) := by
  rw [← BialgHom.quotientPointsSubgroup_unipotentDefiningHopfIdeal l]
  exact HopfIdeal.mem_quotientPointsSubgroup_derivationMulEquivTangentKer_iff _ d

private theorem tangentPoint_mem_levi_iff (l : H →ₐc[R] LaurentPolynomial R)
    (d : Derivation R H (Bialgebra.CounitAlgebra R H B)) :
    (derivationMulEquivTangentKer R H B (.ofAdd d)).val ∈
        levi (DualNumber (Bialgebra.CounitAlgebra R H B)) l ↔
      d ∈ (leviDefiningHopfIdeal l).lieSubalgebra (B := B) := by
  rw [← quotientPointsSubgroup_leviDefiningHopfIdeal l
    (CommAlgCat.of R (DualNumber (Bialgebra.CounitAlgebra R H B)))]
  exact HopfIdeal.mem_quotientPointsSubgroup_derivationMulEquivTangentKer_iff _ d

/-- The unipotent and Levi tangent spaces have zero intersection, even when the base or
coefficient algebra is nonreduced. -/
theorem disjoint_lieSubalgebra_unipotent_levi (l : H →ₐc[R] LaurentPolynomial R) :
    Disjoint (l.unipotentDefiningHopfIdeal.lieSubalgebra (B := B)).toSubmodule
      ((leviDefiningHopfIdeal l).lieSubalgebra (B := B)).toSubmodule := by
  rw [Submodule.disjoint_def]
  intro d hu hz
  have hmem := eq_one_of_mem_unipotent_of_mem_levi ((tangentPoint_mem_unipotent_iff l d).mpr hu)
    ((tangentPoint_mem_levi_iff l d).mpr hz)
  have hzero : derivationMulEquivTangentKer R H B (.ofAdd d) = 1 := Subtype.ext hmem
  exact Multiplicative.ofAdd.injective
    ((derivationMulEquivTangentKer R H B).injective (hzero.trans (map_one _).symm))

private theorem limit_mem_tangentKer (l : H →ₐc[R] LaurentPolynomial R)
    (g : parabolic (DualNumber (Bialgebra.CounitAlgebra R H B)) l)
    (hg : g.val ∈ tangentKer R H B) :
    limit _ l g ∈ tangentKer R H B := by
  rw [tangentKer_def, MonoidHom.mem_ker] at hg ⊢
  rw [dualNumberReduction_def] at hg ⊢
  rw [mapValue_limit]
  let φ := TrivSqZeroExt.fstHom R
    (Bialgebra.CounitAlgebra R H B) (Bialgebra.CounitAlgebra R H B)
  have hone :
      (⟨AlgHom.mapValue φ g.val, Subgroup.mem_comap.mp
        (parabolic_le_comap φ g.property)⟩ :
        parabolic (Bialgebra.CounitAlgebra R H B) l) = 1 := Subtype.ext hg
  rw [hone, map_one]

/-- Every parabolic tangent vector is a sum of a unipotent tangent vector and a Levi tangent
vector. No smoothness hypothesis is needed to differentiate the dynamic factorization. -/
theorem exists_add_lieSubalgebra_unipotent_levi (l : H →ₐc[R] LaurentPolynomial R)
    {d : Derivation R H (Bialgebra.CounitAlgebra R H B)}
    (hd : d ∈ (parabolicDefiningHopfIdeal l).lieSubalgebra (B := B)) :
    ∃ u ∈ l.unipotentDefiningHopfIdeal.lieSubalgebra (B := B),
      ∃ z ∈ (leviDefiningHopfIdeal l).lieSubalgebra (B := B), d = u + z := by
  let p := derivationMulEquivTangentKer R H B (.ofAdd d)
  have hp : p.val ∈ parabolic (DualNumber (Bialgebra.CounitAlgebra R H B)) l :=
    (tangentPoint_mem_parabolic_iff l d).mpr hd
  let z : tangentKer R H B := ⟨limit _ l ⟨p.val, hp⟩, limit_mem_tangentKer l _ p.property⟩
  let u : tangentKer R H B := p * z⁻¹
  let e := (derivationMulEquivTangentKer R H B).symm u
  let f := (derivationMulEquivTangentKer R H B).symm z
  have he : derivationMulEquivTangentKer R H B e = u :=
    (derivationMulEquivTangentKer R H B).apply_symm_apply u
  have hf : derivationMulEquivTangentKer R H B f = z :=
    (derivationMulEquivTangentKer R H B).apply_symm_apply z
  refine ⟨e.toAdd, ?_, f.toAdd, ?_, ?_⟩
  · rw [← tangentPoint_mem_unipotent_iff l, ofAdd_toAdd, he]
    exact mul_limit_inv_mem_unipotent hp
  · rw [← tangentPoint_mem_levi_iff l, ofAdd_toAdd, hf]
    exact limit_mem_levi ⟨p.val, hp⟩
  · have hsum : p = u * z := by simp [u]
    have h := congrArg (derivationMulEquivTangentKer R H B).symm hsum
    simpa [p] using congrArg Multiplicative.toAdd h

/-- The unipotent and Levi tangent submodules span exactly the parabolic tangent submodule. -/
theorem sup_lieSubalgebra_unipotent_levi (l : H →ₐc[R] LaurentPolynomial R) :
    (l.unipotentDefiningHopfIdeal.lieSubalgebra (B := B)).toSubmodule ⊔
        ((leviDefiningHopfIdeal l).lieSubalgebra (B := B)).toSubmodule =
      ((parabolicDefiningHopfIdeal l).lieSubalgebra (B := B)).toSubmodule := by
  apply le_antisymm
  · apply sup_le
    · intro d hd
      exact (tangentPoint_mem_parabolic_iff l d).mp
        (unipotent_le_parabolic ((tangentPoint_mem_unipotent_iff l d).mpr hd))
    · intro d hd
      exact (tangentPoint_mem_parabolic_iff l d).mp
        (levi_le_parabolic ((tangentPoint_mem_levi_iff l d).mpr hd))
  · intro d hd
    obtain ⟨u, hu, z, hz, rfl⟩ := exists_add_lieSubalgebra_unipotent_levi l hd
    exact Submodule.add_mem_sup hu hz

/-- Addition identifies the product of the unipotent and Levi tangent spaces with the
parabolic tangent space. This is an equivalence of modules, without an assertion that the
mixed Lie bracket vanishes. -/
noncomputable def leviDecompositionTangentEquiv (l : H →ₐc[R] LaurentPolynomial R) :
    ((l.unipotentDefiningHopfIdeal.lieSubalgebra (B := B)) ×
        ((leviDefiningHopfIdeal l).lieSubalgebra (B := B))) ≃ₗ[B]
      (parabolicDefiningHopfIdeal l).lieSubalgebra (B := B) := by
  let U := (l.unipotentDefiningHopfIdeal.lieSubalgebra (B := B)).toSubmodule
  let Z := ((leviDefiningHopfIdeal l).lieSubalgebra (B := B)).toSubmodule
  let s := U.subtype.coprod Z.subtype
  have hinj : Function.Injective s := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_coprod_of_disjoint_range,
      Submodule.ker_subtype, Submodule.ker_subtype, Submodule.prod_bot]
    simpa only [Submodule.range_subtype] using disjoint_lieSubalgebra_unipotent_levi
      (B := B) l
  exact (LinearEquiv.ofInjective s hinj).trans
    (LinearEquiv.ofEq _ _ ((Submodule.sup_eq_range U Z).symm.trans
      (sup_lieSubalgebra_unipotent_levi l)))

/-- The tangent Levi decomposition sends a pair to the sum of its ambient derivations. -/
@[simp]
theorem coe_leviDecompositionTangentEquiv_apply (l : H →ₐc[R] LaurentPolynomial R)
    (x : (l.unipotentDefiningHopfIdeal.lieSubalgebra (B := B)) ×
      ((leviDefiningHopfIdeal l).lieSubalgebra (B := B))) :
    (leviDecompositionTangentEquiv l x : Derivation R H (Bialgebra.CounitAlgebra R H B)) =
      x.1.val + x.2.val := (rfl)

end BialgHom
