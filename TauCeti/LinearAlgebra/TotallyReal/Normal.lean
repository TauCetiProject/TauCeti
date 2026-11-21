/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Quotient.Basic
public import TauCeti.LinearAlgebra.Orientation.Exact.Basic
public import TauCeti.LinearAlgebra.TotallyReal.Frame
import TauCeti.LinearAlgebra.Orientation.Shuffle

/-!
# The normal space of a maximal totally real subspace

Let `L` be a maximal totally real submodule of `E` for an endomorphism `J`, so that
`E = L ⊕ J L`, and suppose `J` is injective on `L`. Then `J` identifies `L` with its normal space
`E ⧸ L`, by `v ↦ [J v]` (`TauCeti.IsMaximalTotallyReal.normalEquiv`). For the tangent space `L` of
a totally real submanifold of an almost complex manifold this is the identification of the tangent
bundle with the normal bundle by the almost complex structure.

This file compares orientations along this identification. Over an ordered field, an orientation
`o` of `L` and its image under `J` on `E ⧸ L` induce, through the exact sequence
`0 → L → E → E ⧸ L → 0` (`Orientation.ofExact`, subspace first), an orientation of `E`. It is the
orientation of the basis `(a₁, …, aₙ, J a₁, …, J aₙ)` for any basis `a` of `L`, which differs
from the orientation of the interleaved basis `(a₁, J a₁, …, aₙ, J aₙ)` by the sign
`(-1) ^ n.choose 2` of the shuffle between the two orders
(`TauCeti.IsMaximalTotallyReal.ofExact_map_normalEquiv`). This orientation of `E` does not depend
on `o`: reversing `o` reverses both orientations it is built from.

For a complex structure the interleaved basis induces the complex orientation of `E`, and for an
almost complex structure tamed by a symplectic form it induces the symplectic orientation
(`TauCeti.SymplecticForm.Tames.orientation_reindex`). So for `n = 2` the identification of a
Lagrangian plane with its normal space by `J` reverses the orientation induced on the normal space
by those of `L` and of `E`; this is why an embedded Lagrangian sphere in a symplectic four-manifold
has self-intersection `-2`.

## Main definitions

* `TauCeti.IsMaximalTotallyReal.normalEquiv`: the identification `L ≃ E ⧸ L`, `v ↦ [J v]`.

## Main results

* `TauCeti.IsMaximalTotallyReal.normalEquiv_apply`: the identification sends `v` to the class of
  `J v`.
* `TauCeti.IsMaximalTotallyReal.finrank_quotient`: the normal space has the dimension of `L`.
* `TauCeti.IsMaximalTotallyReal.ofExact_map_normalEquiv`: an orientation of `L` followed by its
  `J`-image on the normal space induces `(-1) ^ n.choose 2` times the orientation of the
  interleaved doubled basis.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix E (the self-intersection of a Lagrangian sphere).
-/

public section

open Module

namespace TauCeti

namespace IsMaximalTotallyReal

section Ring

variable {R E : Type*} [Ring R] [AddCommGroup E] [Module R E] {J : E →ₗ[R] E}
  {L : Submodule R E}

/-- The **normal identification** of a maximal totally real submodule `L`: the linear equivalence
`L ≃ E ⧸ L` sending `v` to the class of `J v` in the normal space
(`TauCeti.IsMaximalTotallyReal.normalEquiv_apply`). It is defined when `J` is injective on `L`,
for instance when `J ∘ J = -1`. It is `J`, an isomorphism of `L` onto `J L`, followed by the
inverse of the isomorphism `E ⧸ L ≃ J L` given by the complement `J L` of `L`
(`Submodule.quotientEquivOfIsCompl`). -/
noncomputable def normalEquiv (hL : IsMaximalTotallyReal J L)
    (hJ : Function.Injective (J.domRestrict L)) : L ≃ₗ[R] E ⧸ L :=
  (LinearEquiv.ofInjective _ hJ).trans
    ((LinearEquiv.ofEq _ _ (LinearMap.range_domRestrict L J)).trans
      (Submodule.quotientEquivOfIsCompl L (L.map J) hL.isCompl).symm)

/-- The normal identification sends `v` to the class of `J v`. -/
@[simp]
theorem normalEquiv_apply (hL : IsMaximalTotallyReal J L)
    (hJ : Function.Injective (J.domRestrict L)) (v : L) :
    hL.normalEquiv hJ v = Submodule.Quotient.mk (J v) := by
  simp [normalEquiv]

/-- The normal space of a maximal totally real submodule has the dimension of the submodule. -/
theorem finrank_quotient (hL : IsMaximalTotallyReal J L)
    (hJ : Function.Injective (J.domRestrict L)) : finrank R (E ⧸ L) = finrank R L :=
  (hL.normalEquiv hJ).finrank_eq.symm

end Ring

section Field

variable {R E : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [AddCommGroup E]
  [Module R E] [FiniteDimensional R E] {J : E →ₗ[R] E} {L : Submodule R E} {n : ℕ}

/-- **The normal orientation of a totally real subspace.** Let `L` be a maximal totally real
submodule for `J`, with `J` injective on `L`, and `o` an orientation of `L`. Orient `E` by `o`
followed by its image under the normal identification `v ↦ [J v]` on `E ⧸ L`. For every basis `a`
of `L`, this is `(-1) ^ n.choose 2` times the orientation of the doubled basis listed in the
interleaved order `(a₁, J a₁, …, aₙ, J aₙ)`. In particular it does not depend on `o`. -/
theorem ofExact_map_normalEquiv (hL : IsMaximalTotallyReal J L)
    (hJ : Function.Injective (J.domRestrict L)) (o : Orientation R L (Fin n))
    (a : Basis (Fin n) R L) (hn : finrank R L = n) :
    Orientation.ofExact L.injective_subtype (LinearMap.exact_subtype_mkQ L) L.mkQ_surjective o
        (Orientation.map (Fin n) (hL.normalEquiv hJ) o) hn ((hL.finrank_quotient hJ).trans hn) =
      (-1 : Rˣ) ^ n.choose 2 • ((hL.doubledBasis hJ a).reindex
        (finProdFinEquiv.trans (finCongr (Nat.mul_two n)))).orientation := by
  -- The basis of `E` listing `a` before its image under `J`.
  set e : Fin n × Fin 2 ≃ Fin (n + n) :=
    (Equiv.prodComm _ _).trans (finProdFinEquiv.trans (finCongr (Nat.two_mul n)))
  have he₀ (i : Fin n) : e.symm (Fin.castAdd n i) = (i, 0) :=
    e.symm_apply_eq.2 (Fin.ext (by simp [e]))
  have he₁ (i : Fin n) : e.symm (Fin.natAdd n i) = (i, 1) :=
    e.symm_apply_eq.2 (Fin.ext (by simp [e, Nat.add_comm]))
  set c := (hL.doubledBasis hJ a).reindex e
  have hc : (Orientation.ofExact L.injective_subtype (LinearMap.exact_subtype_mkQ L)
      L.mkQ_surjective a.orientation (Orientation.map (Fin n) (hL.normalEquiv hJ) a.orientation)
      hn ((hL.finrank_quotient hJ).trans hn)) = c.orientation := by
    rw [← Basis.orientation_map]
    exact Orientation.ofExact_orientation _ _ _ a _ c
      (fun i ↦ by rw [Basis.reindex_apply, he₀, doubledBasis_apply_zero, Submodule.subtype_apply])
      (fun i ↦ by rw [Basis.reindex_apply, he₁, doubledBasis_apply_one, Basis.map_apply,
        normalEquiv_apply, Submodule.mkQ_apply]) _ _
  rw [← (hL.doubledBasis hJ a).orientation_eq_neg_one_pow_choose_two_smul_orientation_reindex c
    (fun i ↦ by rw [Basis.reindex_apply, he₀]) (fun i ↦ by rw [Basis.reindex_apply, he₁]), ← hc]
  -- Reversing `o` reverses both orientations it induces, so the result does not depend on `o`.
  rcases a.orientation_eq_or_eq_neg o with rfl | rfl
  · rfl
  · rw [Orientation.map_neg, Orientation.ofExact_neg_neg]

end Field

end IsMaximalTotallyReal

end TauCeti
