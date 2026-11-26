/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.DiagonalTorus.Maximal
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.SchematicClosure

/-!
# The schematic closure of the diagonal torus of `GL_n`

Let `O` be a ring with fraction field `K`. The diagonal torus of `GL_n` over `O` is cut out by
`TauCeti.GeneralLinear.diagonalTorusDefiningIdeal`, the kernel of the restriction
`O[GL_n] → O[t₁^{±1}, …, tₙ^{±1}]` to diagonal matrices. Its quotient is a Laurent polynomial ring,
so it is torsion-free over `O`, and the schematic closure in `GL_{n, O}` of the diagonal torus of
`GL_{n, K}` is the diagonal torus over `O`: the closure ideal of the diagonal-torus ideal of
`K ⊗_O O[GL_n] ≅ K[GL_n]` is the diagonal-torus ideal over `O`.
-/

public section

open CategoryTheory

namespace TauCeti.GeneralLinear

universe u

variable (O : Type u) [CommRing O] (n : ℕ)

/-- The coordinate ring `O[GL_n] ⧸ I_T` of the diagonal torus is torsion-free over `O`: it
embeds in the Laurent polynomial ring through the restriction to diagonal matrices. -/
instance isTorsionFree_quotient_diagonalTorusDefiningIdeal :
    Module.IsTorsionFree O
      (coordinateHopfAlgebra O n ⧸ (diagonalTorusDefiningIdeal O n).toIdeal) := by
  let f := (diagonalTorusCoordinateMap (R := O) (N := n)).hom.toAlgHom
  have hJ : (diagonalTorusDefiningIdeal O n).toIdeal = RingHom.ker f := by
    rw [diagonalTorusDefiningIdeal_eq_ker, HopfIdeal.kerOfSurjective_toIdeal]
  rw [hJ]
  exact Function.Injective.moduleIsTorsionFree (Ideal.kerLiftAlg f)
    (Ideal.kerLiftAlg_injective f) fun r x ↦ map_smul (Ideal.kerLiftAlg f) r x

variable (K : Type u) [Field K] [Algebra O K] [IsFractionRing O K]

/-- **The schematic closure of the diagonal torus** (in Hopf coordinates on `GL_{n, O}`): the
closure ideal of the base change of the diagonal-torus ideal is the diagonal-torus ideal over `O`.
-/
theorem closureIdeal_baseChangeHopfIdeal_diagonalTorusDefiningIdeal :
    SchematicClosure.closureIdeal K
        (CommHopfAlgCat.baseChangeHopfIdeal (K := K) (diagonalTorusDefiningIdeal O n)).toIdeal =
      (diagonalTorusDefiningIdeal O n).toIdeal :=
  CommHopfAlgCat.closureIdeal_baseChangeHopfIdeal _

/-- **The schematic closure of the diagonal torus of `GL_{n, K}`**: transporting the diagonal-torus
ideal of `K[GL_n]` to `K ⊗_O O[GL_n]` along the base-change isomorphism, its closure ideal is the
diagonal-torus ideal over `O`. -/
theorem closureIdeal_comap_diagonalTorusDefiningIdeal :
    SchematicClosure.closureIdeal K
        ((diagonalTorusDefiningIdeal K n).toIdeal.comap
          (((coordinateHopfAlgebraBaseChangeIso O K n).hom.hom :
              CommHopfAlgCat.baseChange (coordinateHopfAlgebra O n) →ₐc[K] _) :
            CommHopfAlgCat.baseChange (coordinateHopfAlgebra O n) →+*
              coordinateHopfAlgebra K n)) =
      (diagonalTorusDefiningIdeal O n).toIdeal := by
  rw [← map_baseChangeHopfIdeal_diagonalTorusDefiningIdeal O n K, HopfIdeal.map_toIdeal,
    Ideal.comap_map_of_bijective _ ?_]
  · exact closureIdeal_baseChangeHopfIdeal_diagonalTorusDefiningIdeal O n K
  · exact Function.bijective_iff_has_inverse.mpr
      ⟨(coordinateHopfAlgebraBaseChangeIso O K n).inv.hom,
      fun x ↦ Iso.hom_inv_id_apply (coordinateHopfAlgebraBaseChangeIso O K n) x,
      fun y ↦ Iso.inv_hom_id_apply (coordinateHopfAlgebraBaseChangeIso O K n) y⟩

end TauCeti.GeneralLinear
