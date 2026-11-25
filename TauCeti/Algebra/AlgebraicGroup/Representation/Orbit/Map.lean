/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.Orbit.ClosureOrder
import TauCeti.LinearAlgebra.SymmetricAlgebra.Functoriality

/-!
# Maps of rational orbits along equivariant linear maps

Let `G = Spec H` and `G' = Spec K` be affine groups over a field `k`, acting on representations
`M` and `N`. A map `ψ : G'(k) → G(k)` on rational points and a linear map `ℓ : N → M` with
`ℓ (g • n) = ψ g • ℓ n` send rational orbits of `G'` in `N` to rational orbits of `G` in `M`
(`TauCeti.Comodule.VectorOrbit.map`).

Over an algebraically closed field, for finite-type groups and finite-dimensional
representations, this map is monotone for the closure order
(`TauCeti.Comodule.VectorOrbit.monotone_map`): if `w` lies in the closure of the orbit of `v`,
then `ℓ w` lies in the closure of the orbit of `ℓ v`. The proof pulls back polynomial functions
along `ℓ`, using the description of the closure order by polynomials vanishing on an orbit
(`TauCeti.Comodule.VectorOrbit.mk_le_mk_iff_forall_lift_eval_eq_zero`). No surjectivity of `ψ`
or `ℓ` is needed.

When `ψ` is surjective and `ℓ` is a linear equivalence, a section of `ψ` makes the inverse
linear equivalence equivariant as well, and the two maps are inverse bijections
(`TauCeti.Comodule.VectorOrbit.equivOfSurjective`). Over an algebraically closed field they
are inverse order isomorphisms (`TauCeti.Comodule.VectorOrbit.orderIsoOfSurjective`). This
applies to isogenies in characteristic zero acting on their Lie algebras: they are surjective on
rational points over algebraically closed fields, and their differential is a linear
equivalence.

## Main declarations

* `TauCeti.Comodule.VectorOrbit.map`: the map of rational orbits induced by an equivariant
  linear map.
* `TauCeti.Comodule.VectorOrbit.equivOfSurjective`: an equivariant linear equivalence over a
  surjection on rational points identifies the rational orbits.
* `TauCeti.Comodule.VectorOrbit.monotone_map`: it is monotone for the closure order.
* `TauCeti.Comodule.VectorOrbit.orderIsoOfSurjective`: an equivariant linear equivalence over
  a surjection on rational points identifies the rational orbits as ordered sets.

## References

* A. Borel, *Linear Algebraic Groups*, 2nd ed., GTM 126, §1.8.
-/

public section

namespace TauCeti.Comodule.VectorOrbit

universe u v w

section Map

variable {k : Type u} {H K : Type v} {M N : Type w} [Field k] [CommRing H] [HopfAlgebra k H]
  [CommRing K] [HopfAlgebra k K] [AddCommGroup M] [Module k M] [Comodule k H M]
  [AddCommGroup N] [Module k N] [Comodule k K N]

/-- The map of rational orbits induced by a linear map `ℓ : N → M` that is equivariant along a
map `ψ` of rational points: the orbit of `n` goes to the orbit of `ℓ n`. -/
def map (ψ : WithConv (K →ₐ[k] k) → WithConv (H →ₐ[k] k)) (ℓ : N →ₗ[k] M)
    (hℓ : ∀ g n, ℓ (basePointsRepresentation N g n) = basePointsRepresentation M (ψ g) (ℓ n)) :
    VectorOrbit k K N → VectorOrbit k H M :=
  lift (fun n ↦ mk (ℓ n)) fun g n ↦ by rw [hℓ, mk_basePointsRepresentation]

/-- The induced map sends the orbit of `n` to the orbit of `ℓ n`. -/
@[simp]
theorem map_mk (ψ : WithConv (K →ₐ[k] k) → WithConv (H →ₐ[k] k)) (ℓ : N →ₗ[k] M)
    (hℓ : ∀ g n, ℓ (basePointsRepresentation N g n) = basePointsRepresentation M (ψ g) (ℓ n))
    (n : N) :
    map ψ ℓ hℓ (mk n) = mk (ℓ n) := by
  simp [map]

/-- A linear equivalence equivariant along a surjection `ψ` on rational points has an inverse
equivariant along any section of `ψ`. -/
private theorem symm_apply_basePointsRepresentation
    {ψ : WithConv (K →ₐ[k] k) → WithConv (H →ₐ[k] k)} (hψ : Function.Surjective ψ)
    (e : N ≃ₗ[k] M)
    (he : ∀ g n, e (basePointsRepresentation N g n) = basePointsRepresentation M (ψ g) (e n))
    (g : WithConv (H →ₐ[k] k)) (m : M) :
    e.symm (basePointsRepresentation M g m) =
      basePointsRepresentation N (Function.surjInv hψ g) (e.symm m) := by
  rw [e.symm_apply_eq, he, e.apply_symm_apply, Function.surjInv_eq hψ]

/-- **Orbits along a surjection on rational points.** If `ψ : G'(k) → G(k)` is surjective and
`e : N ≃ M` is equivariant along `ψ`, then `e` identifies the rational orbits of `G'` in `N`
with those of `G` in `M`; the inverse is induced by `e.symm` along a section of `ψ`. -/
noncomputable def equivOfSurjective {ψ : WithConv (K →ₐ[k] k) → WithConv (H →ₐ[k] k)}
    (hψ : Function.Surjective ψ) (e : N ≃ₗ[k] M)
    (he : ∀ g n, e (basePointsRepresentation N g n) = basePointsRepresentation M (ψ g) (e n)) :
    VectorOrbit k K N ≃ VectorOrbit k H M where
  toFun := map ψ e he
  invFun := map (Function.surjInv hψ) e.symm (symm_apply_basePointsRepresentation hψ e he)
  left_inv O := by
    induction O using VectorOrbit.ind with | h n
    simp
  right_inv O := by
    induction O using VectorOrbit.ind with | h m
    simp

/-- The equivalence sends the orbit of `n` to the orbit of `e n`. -/
@[simp]
theorem equivOfSurjective_mk {ψ : WithConv (K →ₐ[k] k) → WithConv (H →ₐ[k] k)}
    (hψ : Function.Surjective ψ) (e : N ≃ₗ[k] M)
    (he : ∀ g n, e (basePointsRepresentation N g n) = basePointsRepresentation M (ψ g) (e n))
    (n : N) :
    equivOfSurjective hψ e he (mk n) = mk (e n) := by
  simp [equivOfSurjective]

/-- The inverse equivalence sends the orbit of `m` to the orbit of `e.symm m`. -/
@[simp]
theorem equivOfSurjective_symm_mk {ψ : WithConv (K →ₐ[k] k) → WithConv (H →ₐ[k] k)}
    (hψ : Function.Surjective ψ) (e : N ≃ₗ[k] M)
    (he : ∀ g n, e (basePointsRepresentation N g n) = basePointsRepresentation M (ψ g) (e n))
    (m : M) :
    (equivOfSurjective hψ e he).symm (mk m) = mk (e.symm m) := by
  simp [equivOfSurjective]

end Map

section ClosureOrder

variable {k H K M N : Type u} [Field k] [IsAlgClosed k] [CommRing H] [HopfAlgebra k H]
  [Algebra.FiniteType k H] [CommRing K] [HopfAlgebra k K] [Algebra.FiniteType k K]
  [AddCommGroup M] [Module k M] [Comodule k H M] [Module.Finite k M]
  [AddCommGroup N] [Module k N] [Comodule k K N] [Module.Finite k N]

/-- **Equivariant linear maps preserve orbit closures.** Over an algebraically closed field, the
map of rational orbits induced by an equivariant linear map is monotone for the closure order. -/
theorem monotone_map (ψ : WithConv (K →ₐ[k] k) → WithConv (H →ₐ[k] k)) (ℓ : N →ₗ[k] M)
    (hℓ : ∀ g n, ℓ (basePointsRepresentation N g n) = basePointsRepresentation M (ψ g) (ℓ n)) :
    Monotone (map ψ ℓ hℓ) := by
  intro O O' hle
  induction O using VectorOrbit.ind with | h w
  induction O' using VectorOrbit.ind with | h v
  rw [map_mk, map_mk, mk_le_mk_iff_forall_lift_eval_eq_zero]
  intro p hp
  -- Pull the polynomial function `p` on `M` back to `N` along `ℓ`.
  rw [← SymmetricAlgebra.lift_eval_map_dualMap k ℓ w]
  refine mk_le_mk_iff_forall_lift_eval_eq_zero.mp hle _ fun g ↦ ?_
  rw [SymmetricAlgebra.lift_eval_map_dualMap, hℓ]
  exact hp (ψ g)

/-- **Orbit closures along a surjection on rational points.** If `ψ : G'(k) → G(k)` is
surjective and `e : N ≃ M` is equivariant along `ψ`, then `e` identifies the rational orbits of
`G'` in `N` with those of `G` in `M`, as ordered sets for the closure order. -/
noncomputable def orderIsoOfSurjective {ψ : WithConv (K →ₐ[k] k) → WithConv (H →ₐ[k] k)}
    (hψ : Function.Surjective ψ) (e : N ≃ₗ[k] M)
    (he : ∀ g n, e (basePointsRepresentation N g n) = basePointsRepresentation M (ψ g) (e n)) :
    VectorOrbit k K N ≃o VectorOrbit k H M where
  toEquiv := equivOfSurjective hψ e he
  map_rel_iff' {O O'} := by
    induction O using VectorOrbit.ind with | h n
    induction O' using VectorOrbit.ind with | h n'
    simp only [equivOfSurjective_mk]
    refine ⟨fun h ↦ ?_, fun h ↦ by simpa using monotone_map ψ (e : N →ₗ[k] M) he h⟩
    simpa using monotone_map (Function.surjInv hψ) (e.symm : M →ₗ[k] N)
      (symm_apply_basePointsRepresentation hψ e he) h

/-- The order isomorphism sends the orbit of `n` to the orbit of `e n`. -/
@[simp]
theorem orderIsoOfSurjective_mk {ψ : WithConv (K →ₐ[k] k) → WithConv (H →ₐ[k] k)}
    (hψ : Function.Surjective ψ) (e : N ≃ₗ[k] M)
    (he : ∀ g n, e (basePointsRepresentation N g n) = basePointsRepresentation M (ψ g) (e n))
    (n : N) :
    orderIsoOfSurjective hψ e he (mk n) = mk (e n) := by
  simp [orderIsoOfSurjective]

/-- The inverse order isomorphism sends the orbit of `m` to the orbit of `e.symm m`. -/
@[simp]
theorem orderIsoOfSurjective_symm_mk {ψ : WithConv (K →ₐ[k] k) → WithConv (H →ₐ[k] k)}
    (hψ : Function.Surjective ψ) (e : N ≃ₗ[k] M)
    (he : ∀ g n, e (basePointsRepresentation N g n) = basePointsRepresentation M (ψ g) (e n))
    (m : M) :
    (orderIsoOfSurjective hψ e he).symm (mk m) = mk (e.symm m) := by
  rw [OrderIso.symm_apply_eq, orderIsoOfSurjective_mk, e.apply_symm_apply]

end ClosureOrder

end TauCeti.Comodule.VectorOrbit
