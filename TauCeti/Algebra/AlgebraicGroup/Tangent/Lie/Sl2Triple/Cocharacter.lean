/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Differential
public import TauCeti.Algebra.AlgebraicGroup.Dynamic.Tangent.Weights
public import TauCeti.Algebra.AlgebraicGroup.Dynamic.Unipotent.Representability
public import TauCeti.Algebra.AlgebraicGroup.MultiplicativeGroup.Tangent
public import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.DiagonalTorus.Coroot
public import TauCeti.Algebra.AlgebraicGroup.Tangent.FiniteType
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.Adjoint.Differential
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.Sl2Triple.Basic

/-!
# The cocharacter of an `sl₂` triple and its weight decomposition

An `sl₂` triple `t : IsSl2Triple h e f` in `Lie(G)` grades `Lie(G)` into the `(n : k)`-eigenspaces
`𝔤(n)` of `ad h`. Composing `IsSl2Triple.sl2CoordinateMap : H ⟶ O(SL₂)` with
`SpecialLinear.simpleCorootCocharacter 1 k 0` upgrades this grading to `G = Spec H` via
`IsSl2Triple.cocharacter : H →ₐc[k] k[T;T⁻¹]`, whose unit tangent differential is `h`. Via
`AddMonoidAlgebra.toMultiplicativeBialgEquiv`, the `m`-weight space on any `H`-comodule equals the
`(m : k)`-eigenspace of `h` (`weightSpace_cocharacter_eq_eigenspace`), and `P_G(t.cocharacter)` and
`U_G(t.cocharacter)` have Lie algebras spanned by `𝔤(n)` for `0 ≤ n` and `0 < n`.

## References

* A. Borel, *Linear Algebraic Groups*, 2nd ed., §7; B. Conrad, O. Gabber, G. Prasad,
  *Pseudo-reductive Groups*, 2nd ed., §2.1.
* D. H. Collingwood and W. M. McGovern, *Nilpotent Orbits in Semisimple Lie Algebras*, §3.3, §3.8.
* J. E. Humphreys, *Conjugacy Classes in Semisimple Algebraic Groups*, AMS, 1995, §8.4.
-/

public section

open CategoryTheory LieAlgebra TauCeti TauCeti.Cocharacter WithConv
open scoped LaurentPolynomial

attribute [local instance 100] LieRing.ofAssociativeRing

namespace IsSl2Triple

universe u w

variable {k H : Type u} [Field k] [CharZero k] [CommRing H] [HopfAlgebra k H]
  [Algebra.FiniteType k H] {h e f : Derivation k H (Bialgebra.CounitAlgebra k H k)}

/-- **The cocharacter `𝔾ₘ ⟶ G` attached to an `sl₂` triple.** -/
noncomputable def cocharacter (t : IsSl2Triple h e f) : H →ₐc[k] LaurentPolynomial k :=
  (SpecialLinear.simpleCorootCocharacter 1 k 0).comp t.sl2CoordinateMap.hom

/-- Unfolding `t.cocharacter` via `simpleCorootCocharacter 1 k 0` and `t.sl2CoordinateMap`. -/
theorem cocharacter_def (t : IsSl2Triple h e f) :
    t.cocharacter = (SpecialLinear.simpleCorootCocharacter 1 k 0).comp t.sl2CoordinateMap.hom :=
  (rfl)

/-- Differential of `t.cocharacter` on tangent vectors of `𝔾ₘ`. -/
@[simp] theorem derivationComp_cocharacter (t : IsSl2Triple h e f)
    (d : Derivation k (LaurentPolynomial k) (Bialgebra.CounitAlgebra k (LaurentPolynomial k) k)) :
    derivationComp (B := k) t.cocharacter d = MultiplicativeGroup.tangentLinearEquiv d • h := by
  rw [cocharacter_def, derivationComp_comp, LinearMap.comp_apply, t.derivationComp_sl2CoordinateMap,
    SpecialLinear.tangentLieEquivSl_apply,
    SpecialLinear.tangentMatrix_derivationComp_simpleCorootCocharacter, Fin.castSucc_zero,
    Fin.succ_zero_eq_one]
  have hsingle : SpecialLinear.singleSubSingle (0 : Fin 2) 1
      (MultiplicativeGroup.tangentLinearEquiv d) =
      MultiplicativeGroup.tangentLinearEquiv d • SpecialLinear.singleSubSingle (0 : Fin 2) 1 1 := by
    simpa only [smul_eq_mul, mul_one] using
      (SpecialLinear.singleSubSingle (0 : Fin 2) 1 (R := k)).map_smul
        (MultiplicativeGroup.tangentLinearEquiv d) 1
  rw [hsingle, map_smul, t.toLieHom_singleSubSingle k]

/-- The unit tangent vector of `𝔾ₘ` maps under `t.cocharacter` to `h`. -/
theorem derivationComp_cocharacter_unit (t : IsSl2Triple h e f) :
    derivationComp (B := k) t.cocharacter
        ((MultiplicativeGroup.tangentLinearEquiv (R := k) (B := k)).symm 1) = h := by
  rw [t.derivationComp_cocharacter, LinearEquiv.apply_symm_apply, one_smul]

/-- **Naturality of `t.cocharacter`** along a morphism of finite-type affine groups. -/
theorem cocharacter_map {H' : Type u} [CommRing H'] [HopfAlgebra k H'] [Algebra.FiniteType k H']
    (t : IsSl2Triple h e f) (ψ : CommHopfAlgCat.of k H' ⟶ CommHopfAlgCat.of k H)
    (hψ : derivationCompLieHom (B := k) ψ.hom h ≠ 0) :
    (t.map (derivationCompLieHom (B := k) ψ.hom) hψ).cocharacter = t.cocharacter.comp ψ.hom := by
  rw [cocharacter_def, t.sl2CoordinateMap_map ψ hψ, CommHopfAlgCat.hom_comp, ← BialgHom.comp_assoc,
    ← cocharacter_def]

/-- **Weight spaces of `t.cocharacter` are `h`-eigenspaces** on every `H`-comodule `V`. -/
theorem weightSpace_cocharacter_eq_eigenspace (t : IsSl2Triple h e f) (V : Type w) [AddCommGroup V]
    [Module k V] [Comodule k H V] (m : ℤ) :
    DiagonalizableGroup.weightSpace V
        (((AddMonoidAlgebra.toMultiplicativeBialgEquiv k k ℤ).toBialgHom.comp
          t.cocharacter).toCoalgHom) (Multiplicative.ofAdd m) =
      Module.End.eigenspace (Comodule.differential (R := k) (H := H) (M := V) h) (m : k) := by
  rw [t.cocharacter.weightSpace_cocharacter_eq_eigenspace V m, t.derivationComp_cocharacter_unit]

/-- **Adjoint weight spaces of `t.cocharacter` are `ad h`-eigenspaces.** -/
theorem adjointWeightSpace_cocharacter_eq_eigenspace (t : IsSl2Triple h e f) (m : ℤ) :
    Derivation.adjointWeightSpace
        ((AddMonoidAlgebra.toMultiplicativeBialgEquiv k k ℤ).toBialgHom.comp t.cocharacter)
        (Multiplicative.ofAdd m) =
      Module.End.eigenspace (ad k (Module.Dual k (Bialgebra.CotangentSpace k H))
        ((Derivation.cotangentDualLieEquiv (R := k) (H := H)).symm h)) (m : k) := by
  rw [t.cocharacter.adjointWeightSpace_cocharacter_eq_eigenspace m,
    t.derivationComp_cocharacter_unit]

/-- Transporting the `n`-adjoint weight space of `t.cocharacter` across `cotangentLinearEquiv`
yields the `(n : k)`-eigenspace of `ad h` on `Lie(G)`. -/
theorem map_cotangentLinearEquiv_adjointWeightSpace (t : IsSl2Triple h e f) (n : ℤ) :
    Submodule.map (Derivation.cotangentLinearEquiv (R := k) (A := H) (B := k) : _ →ₗ[k] _)
        (Derivation.adjointWeightSpace
          ((AddMonoidAlgebra.toMultiplicativeBialgEquiv k k ℤ).toBialgHom.comp t.cocharacter)
          (Multiplicative.ofAdd n)) =
      Module.End.eigenspace (ad k (Derivation k H (Bialgebra.CounitAlgebra k H k)) h) (n : k) := by
  rw [t.cocharacter.map_cotangentLinearEquiv_adjointWeightSpace_cocharacter n,
    t.derivationComp_cocharacter_unit]

/-- **The underlying submodule of `Lie(P_G(t.cocharacter))` is the supremum of the
`(n : k)`-eigenspaces of `ad h` on `Lie(G)` for `0 ≤ n`.** -/
theorem lieSubalgebra_parabolicDefiningHopfIdeal_cocharacter (t : IsSl2Triple h e f) :
    ((parabolicDefiningHopfIdeal t.cocharacter).lieSubalgebra (B := k)).toSubmodule =
      ⨆ (n : ℤ) (_ : 0 ≤ n), Module.End.eigenspace
        (ad k (Derivation k H (Bialgebra.CounitAlgebra k H k)) h) (n : k) := by
  rw [t.cocharacter.lieSubalgebra_parabolicDefiningHopfIdeal_eq_iSup_eigenspace,
    t.derivationComp_cocharacter_unit]

/-- **The underlying submodule of `Lie(U_G(t.cocharacter))` is the supremum of the
`(n : k)`-eigenspaces of `ad h` on `Lie(G)` for `0 < n`.** -/
theorem lieSubalgebra_unipotentDefiningHopfIdeal_cocharacter (t : IsSl2Triple h e f) :
    (t.cocharacter.unipotentDefiningHopfIdeal.lieSubalgebra (B := k)).toSubmodule =
      ⨆ (n : ℤ) (_ : 0 < n), Module.End.eigenspace
        (ad k (Derivation k H (Bialgebra.CounitAlgebra k H k)) h) (n : k) := by
  rw [t.cocharacter.lieSubalgebra_unipotentDefiningHopfIdeal_eq_iSup_eigenspace,
    t.derivationComp_cocharacter_unit]

end IsSl2Triple
