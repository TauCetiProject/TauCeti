/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Differential
public import TauCeti.Algebra.AlgebraicGroup.MultiplicativeGroup.Tangent
import TauCeti.Algebra.Bialgebra.MonoidAlgebra.Equiv

/-!
# Differentiated actions of cocharacters

For a cocharacter `l : H →ₐc[R] R[T;T⁻¹]` of a bialgebra `H` over a characteristic-zero domain `R`,
the unit tangent vector `(MultiplicativeGroup.tangentLinearEquiv).symm 1` of `𝔾ₘ` separates integer
characters `m ↦ (m : R)`. Consequently, on every torsion-free `H`-comodule `V`, the `m`-weight
space of `l` (transported to `R[Multiplicative ℤ]` via
`AddMonoidAlgebra.toMultiplicativeBialgEquiv`) equals the `(m : R)`-eigenspace of the unit tangent
differential of `l`.

This requires neither an antipode on `H` nor finiteness on `V`.

## Main declarations

* `BialgHom.weightSpace_cocharacter_eq_eigenspace`: over a characteristic-zero domain, cocharacter
  weight spaces on torsion-free comodules coincide with eigenspaces of the unit tangent
  differential.

## References

* J. C. Jantzen, *Representations of Algebraic Groups*, I.2 and I.7.
* J. S. Milne, *Algebraic Groups* (2017), Chapters 12 and 22.
-/

public section

open TauCeti
open scoped LaurentPolynomial

namespace BialgHom

/-- Over a characteristic-zero domain `R`, the `m`-weight space of `l : H →ₐc[R] R[T;T⁻¹]` on any
torsion-free `H`-comodule `V` equals the `(m : R)`-eigenspace of its unit tangent differential. -/
theorem weightSpace_cocharacter_eq_eigenspace {R H : Type*} [CommRing R] [IsDomain R] [CharZero R]
    [CommRing H] [Bialgebra R H] (l : H →ₐc[R] LaurentPolynomial R) (V : Type*) [AddCommGroup V]
    [Module R V] [Module.IsTorsionFree R V] [Comodule R H V] (m : ℤ) :
    DiagonalizableGroup.weightSpace V (((AddMonoidAlgebra.toMultiplicativeBialgEquiv R R
      ℤ).toBialgHom.comp l).toCoalgHom) (Multiplicative.ofAdd m) =
      Module.End.eigenspace (Comodule.differential (R := R) (H := H) (M := V)
        (derivationComp (B := R) l
          ((MultiplicativeGroup.tangentLinearEquiv (R := R) (B := R)).symm 1))) (m : R) := by
  let eMult := AddMonoidAlgebra.toMultiplicativeBialgEquiv R R ℤ
  let d₀ := derivationComp (B := R) eMult.symm.toBialgHom
    ((MultiplicativeGroup.tangentLinearEquiv (R := R) (B := R)).symm 1)
  have hd₀ (x : Multiplicative ℤ) : Bialgebra.CounitAlgebra.algEquivSelf R
      (MonoidAlgebra R (Multiplicative ℤ)) R (d₀ (MonoidAlgebra.single x 1)) = (x.toAdd : R) := by
    rw [algEquivSelf_derivationComp_apply, BialgHom.coe_toAlgHom, BialgEquiv.toBialgHom_eq_coe,
      BialgEquiv.coe_toBialgHom, AddMonoidAlgebra.toMultiplicativeBialgEquiv_symm_single,
      ← LaurentPolynomial.T, MultiplicativeGroup.tangentLinearEquiv_symm_apply_T, zsmul_one]
  have hinj : Function.Injective fun x : Multiplicative ℤ ↦ Bialgebra.CounitAlgebra.algEquivSelf R
      (MonoidAlgebra R (Multiplicative ℤ)) R (d₀ (MonoidAlgebra.single x 1)) := fun x y hxy ↦
    Multiplicative.toAdd.injective (Int.cast_inj.mp ((hd₀ x).symm.trans (hxy.trans (hd₀ y))))
  rw [DiagonalizableGroup.weightSpace_eq_eigenspace_differential_of_injective V
      (eMult.toBialgHom.comp l) d₀ hinj (Multiplicative.ofAdd m), derivationComp_comp,
    LinearMap.comp_apply, derivationComp_derivationComp_eq_self_of_comp_eq_id _ _
      (BialgHom.ext eMult.symm_apply_apply), hd₀, toAdd_ofAdd]

end BialgHom
