/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TypeAHeckeAlgebra.BalancedProjection.Complement
public import TauCeti.Algebra.TypeAHeckeAlgebra.BalancedProjection.HeckeComparison.Basic
public import TauCeti.Algebra.TypeAHeckeAlgebra.Complement

/-!
# Complement comparison between the balanced projection and type-A Hecke algebras

Whenever `τ * (q + q⁻¹) ^ 2 = 1`, `BalancedProjectionAlgebra.heckeEquiv` intertwines the
complement automorphisms (`BalancedProjectionAlgebra.heckeEquiv_complementEquiv`) without requiring
any star structure.

## Main results

* `TauCeti.BalancedProjectionAlgebra.heckeEquiv_complementEquiv`: `heckeEquiv` intertwines the
  complement automorphisms.

## References

* H. Wenzl, *Hecke algebras of type A_n and subfactors*, Invent. Math. 92 (1988), 349–383, §§2–3.
* V. F. R. Jones, *Hecke algebra representations of braid groups and link polynomials*,
  Ann. of Math. 126 (1987), 335–388, §§5, 11.
-/

public section

namespace TauCeti.BalancedProjectionAlgebra

variable {R : Type*} [CommRing R] {τ : R} {q : Rˣ}

/-- Under `heckeEquiv`, the projection complement `e i ↦ 1 - e i` corresponds to the Hecke
complement automorphism `T i ↦ -T i⁻¹ = (q - q⁻¹) - T i`. -/
theorem heckeEquiv_complementEquiv (hτ : τ * ((q : R) + ↑q⁻¹) ^ 2 = 1)
    (x : BalancedProjectionAlgebra R τ) :
    heckeEquiv q hτ (complementEquiv τ x) =
      InfiniteTypeAHeckeAlgebra.complementEquiv q (heckeEquiv q hτ x) :=
  DFunLike.congr_fun
    (hom_ext (F := (heckeEquiv q hτ).toAlgHom.comp (complementEquiv τ).toAlgHom)
      (G := (InfiniteTypeAHeckeAlgebra.complementEquiv q).toAlgHom.comp (heckeEquiv q hτ).toAlgHom)
      fun i ↦ by
        simpa only [AlgHom.comp_apply, AlgEquiv.toAlgHom_apply, complementEquiv_e, map_sub,
          map_one, heckeEquiv_e, ← val_inv_addInvUnit hτ] using
          (InfiniteTypeAHeckeAlgebra.complementEquiv_eigenprojection q (addInvUnit hτ)
            (val_addInvUnit hτ) i).symm) x

end TauCeti.BalancedProjectionAlgebra
