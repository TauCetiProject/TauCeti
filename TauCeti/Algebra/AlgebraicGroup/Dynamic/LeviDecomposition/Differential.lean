/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Dynamic.Limit
public import TauCeti.Algebra.AlgebraicGroup.Dynamic.LeviDecomposition.Tangent
public import TauCeti.Algebra.AlgebraicGroup.Dynamic.Levi.Centralizer
public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Centralizer.Tangent
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Kernel.Tangent

/-!
# The differential of the dynamic limit

The represented limit `P(λ) → G` differentiates to the Levi projection on `Lie P(λ)`.
Its value on a tangent derivation is obtained by applying that derivation to the constant
Laurent coefficient of universal conjugation. Its kernel is exactly `Lie U(λ)`, and it
is the identity on `Lie Z(λ)`. It recovers the Levi coordinate of the canonical tangent
Levi decomposition.

These formulas relate the represented dynamic subgroups to the infinitesimal conjugation
action, for use in their dimension and smoothness comparisons. They hold over any commutative
base ring and with coefficients in any commutative base algebra; no smoothness, reducedness,
finite-type or field assumption is needed. When the ambient augmentation cotangent module is
finite projective, the image is also identified with the zero adjoint weight space for `λ`.

The construction uses `BialgHom.parabolicLimitCoordinateMap` and
`BialgHom.leviDecompositionTangentEquiv`. The kernel computation uses
`TauCeti.CommHopfAlgCat.lieSubalgebra_kernelHopfIdeal`.

## References

* B. Conrad, O. Gabber, G. Prasad, *Pseudo-reductive Groups*, §2.1.
* J. S. Milne, *Algebraic Groups* (2017), §§10 and 13.
-/

public section

open CategoryTheory TauCeti TauCeti.Cocharacter

namespace BialgHom

universe u v

variable {R H : Type u} [CommRing R] [CommRing H] [HopfAlgebra R H]
variable {B : Type v} [CommRing B] [Algebra R B]

/-- The differential of the represented dynamic limit, with its domain identified with
its image `Lie P(λ)` in the ambient Lie algebra. -/
noncomputable def parabolicLimitLieHom (l : H →ₐc[R] LaurentPolynomial R) :
    (parabolicDefiningHopfIdeal l).lieSubalgebra (B := B) →ₗ⁅B⁆
      Derivation R H (Bialgebra.CounitAlgebra R H B) :=
  (derivationCompLieHom (B := B) (parabolicLimitCoordinateMap l).hom).comp
    (HopfIdeal.quotientLieEquiv (B := B) (parabolicDefiningHopfIdeal l)).symm.toLieHom

/-- Under the canonical identification of the parabolic's intrinsic Lie algebra with its
ambient tangent subalgebra, this map is the differential of the represented limit. -/
@[simp]
theorem parabolicLimitLieHom_quotientLieEquiv (l : H →ₐc[R] LaurentPolynomial R)
    (d : Derivation R (H ⧸ (parabolicDefiningHopfIdeal l).toIdeal)
      (Bialgebra.CounitAlgebra R (H ⧸ (parabolicDefiningHopfIdeal l).toIdeal) B)) :
    parabolicLimitLieHom l (HopfIdeal.quotientLieEquiv (parabolicDefiningHopfIdeal l) d) =
      derivationCompLieHom (B := B) (parabolicLimitCoordinateMap l).hom d := by
  rw [parabolicLimitLieHom, LieHom.comp_apply, LieEquiv.coe_toLieHom,
    LieEquiv.symm_apply_apply]

/-- The dynamic limit differential is differentiation of the constant Laurent coefficient
of universal conjugation. -/
@[simp]
theorem parabolicLimitLieHom_apply_apply (l : H →ₐc[R] LaurentPolynomial R)
    (d : (parabolicDefiningHopfIdeal l).lieSubalgebra (B := B)) (h : H) :
    parabolicLimitLieHom l d h = d.val ((conjugationAlgHom l h).coeff 0) := by
  simp only [parabolicLimitLieHom, LieHom.comp_apply, LieEquiv.coe_toLieHom,
    derivationCompLieHom_apply, derivationComp_apply, BialgHom.coe_toAlgHom]
  rw [parabolicLimitCoordinateMap_apply, CommHopfAlgCat.mkQuotient_apply,
    Ideal.Quotient.mkₐ_eq_mk, HopfIdeal.quotientLieEquiv_symm_apply_mk]

/-- A tangent vector of the dynamic parabolic is killed by the limit differential exactly
when it belongs to the tangent Lie algebra of the dynamic unipotent subgroup. -/
@[simp]
theorem parabolicLimitLieHom_eq_zero_iff (l : H →ₐc[R] LaurentPolynomial R)
    (d : (parabolicDefiningHopfIdeal l).lieSubalgebra (B := B)) :
    parabolicLimitLieHom l d = 0 ↔ d.val ∈ l.unipotentDefiningHopfIdeal.lieSubalgebra := by
  -- Differentiate the scheme-theoretic kernel and transport it through the parabolic quotient.
  rw [parabolicLimitLieHom, LieHom.comp_apply, LieEquiv.coe_toLieHom,
    ← LieHom.mem_ker, ← LieIdeal.mem_toLieSubalgebra,
    ← CommHopfAlgCat.lieSubalgebra_kernelHopfIdeal,
    kernelHopfIdeal_parabolicLimitCoordinateMap, CommHopfAlgCat.hom_mkQuotient]
  exact HopfIdeal.quotientLieEquiv_symm_mem_lieSubalgebra_map_iff _ _ d

/-- The limit differential restricts to the identity on the Levi tangent Lie algebra. -/
@[simp]
theorem parabolicLimitLieHom_of_mem_levi (l : H →ₐc[R] LaurentPolynomial R)
    (d : (parabolicDefiningHopfIdeal l).lieSubalgebra (B := B))
    (hd : d.val ∈ (leviDefiningHopfIdeal l).lieSubalgebra) :
    parabolicLimitLieHom l d = d.val := by
  let e := (HopfIdeal.quotientLieEquiv (B := B) (leviDefiningHopfIdeal l)).symm ⟨d, hd⟩
  have he : HopfIdeal.quotientLieHom (leviDefiningHopfIdeal l) e = d.val := by
    rw [← HopfIdeal.quotientLieEquiv_apply_coe, LieEquiv.apply_symm_apply]
  ext h
  rw [parabolicLimitLieHom_apply_apply, ← he, HopfIdeal.quotientLieHom_apply_apply,
    HopfIdeal.quotientLieHom_apply_apply]
  have hc := congrArg (fun f => f.hom h)
    (parabolicLimitCoordinateMap_comp_quotientMapOfLe l)
  rw [_root_.CommHopfAlgCat.comp_apply, parabolicLimitCoordinateMap_apply,
    ← _root_.CommHopfAlgCat.comp_apply,
    CommHopfAlgCat.mkQuotient_comp_quotientMapOfLe] at hc
  rw [CommHopfAlgCat.mkQuotient_apply, CommHopfAlgCat.mkQuotient_apply] at hc
  exact congrArg (fun a => Bialgebra.CounitAlgebra.algEquivSelf R
    (H ⧸ (leviDefiningHopfIdeal l).toIdeal) B (e a)) hc

/-- On any unipotent--Levi sum, the limit differential returns its Levi summand. -/
theorem parabolicLimitLieHom_eq_of_eq_add (l : H →ₐc[R] LaurentPolynomial R)
    (d : (parabolicDefiningHopfIdeal l).lieSubalgebra (B := B))
    (u z : Derivation R H (Bialgebra.CounitAlgebra R H B))
    (hu : u ∈ l.unipotentDefiningHopfIdeal.lieSubalgebra)
    (hz : z ∈ (leviDefiningHopfIdeal l).lieSubalgebra) (hd : d.val = u + z) :
    parabolicLimitLieHom l d = z := by
  have hsum := sup_lieSubalgebra_unipotent_levi (B := B) l
  have huP : u ∈ (parabolicDefiningHopfIdeal l).lieSubalgebra := by
    rw [← LieSubalgebra.mem_toSubmodule, ← hsum]
    exact Submodule.mem_sup_left hu
  have hzP : z ∈ (parabolicDefiningHopfIdeal l).lieSubalgebra := by
    rw [← LieSubalgebra.mem_toSubmodule, ← hsum]
    exact Submodule.mem_sup_right hz
  have hd' : d = (⟨u, huP⟩ : (parabolicDefiningHopfIdeal l).lieSubalgebra) + ⟨z, hzP⟩ :=
    Subtype.ext hd
  rw [hd', map_add, (parabolicLimitLieHom_eq_zero_iff l _).mpr hu,
    parabolicLimitLieHom_of_mem_levi l _ hz, zero_add]

/-- The differential of the represented limit is the Levi coordinate of the canonical
tangent Levi decomposition. -/
@[simp]
theorem parabolicLimitLieHom_leviDecompositionTangentEquiv
    (l : H →ₐc[R] LaurentPolynomial R)
    (x : l.unipotentDefiningHopfIdeal.lieSubalgebra (B := B) ×
      (leviDefiningHopfIdeal l).lieSubalgebra (B := B)) :
    parabolicLimitLieHom l (leviDecompositionTangentEquiv l x) = x.2.val :=
  parabolicLimitLieHom_eq_of_eq_add l _ _ _ x.1.property x.2.property
    (coe_leviDecompositionTangentEquiv_apply l x)

/-- The image of the limit differential is exactly the Levi tangent Lie algebra. -/
@[simp]
theorem range_parabolicLimitLieHom (l : H →ₐc[R] LaurentPolynomial R) :
    (parabolicLimitLieHom (B := B) l).range = (leviDefiningHopfIdeal l).lieSubalgebra := by
  ext z
  constructor
  · rintro ⟨d, rfl⟩
    obtain ⟨u, hu, z, hz, hd⟩ := exists_add_lieSubalgebra_unipotent_levi l d.property
    exact (parabolicLimitLieHom_eq_of_eq_add l d u z hu hz hd).symm ▸ hz
  · intro hz
    have hzP : z ∈ (parabolicDefiningHopfIdeal l).lieSubalgebra := by
      rw [← LieSubalgebra.mem_toSubmodule, ← sup_lieSubalgebra_unipotent_levi (B := B) l]
      exact Submodule.mem_sup_right hz
    exact ⟨⟨z, hzP⟩, parabolicLimitLieHom_of_mem_levi l _ hz⟩

/-- On the cotangent-dual model of the ambient Lie algebra, the image of the limit
differential is the zero-weight space of the cocharacter's adjoint action. -/
-- The universal-point criterion for a diagonalizable centralizer takes the character group
-- in the same universe as the base and coordinate algebra; here that group is `Multiplicative ℤ`.
theorem range_parabolicLimitLieHom_toSubmodule
    {R H : Type} [CommRing R] [CommRing H] [HopfAlgebra R H]
    [Module.Finite R (Bialgebra.CotangentSpace R H)]
    [Module.Projective R (Bialgebra.CotangentSpace R H)]
    (l : H →ₐc[R] LaurentPolynomial R) :
    (parabolicLimitLieHom (B := R) l).range.toSubmodule =
      (Derivation.adjointWeightSpace
        ((AddMonoidAlgebra.toMultiplicativeBialgEquiv R R ℤ).toBialgHom.comp l) 1).map
        (Derivation.cotangentLinearEquiv (R := R) (A := H) (B := R)).toLinearMap := by
  rw [range_parabolicLimitLieHom, leviDefiningHopfIdeal_eq_centralizerHopfIdeal]
  exact lieSubalgebra_centralizerHopfIdeal_toSubmodule _

end BialgHom
