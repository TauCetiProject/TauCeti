/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Dynamic.ClosedImmersion.Parabolic
public import TauCeti.Algebra.AlgebraicGroup.Dynamic.Unipotent.Representability
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Order

/-!
# Defining ideals of dynamic subgroups under closed immersions

A closed immersion identifies the dynamic parabolic and unipotent subgroup with the
scheme-theoretic inverse images of the corresponding ambient subgroups. This file expresses
that compatibility as equality of defining Hopf ideals. In particular, differentiating these
equalities allows a faithful matrix representation to compute dynamic tangent spaces.
Read in the ambient group, the dynamic parabolic and unipotent subgroups of a closed subgroup `Z`
are the intersections `Z ∩ P_G(λ)` and `Z ∩ U_G(λ)`.

The comparison retains the infinitesimal structure; no reducedness or smoothness
assumption is required.

## References

* B. Conrad, O. Gabber, G. Prasad, *Pseudo-reductive Groups*, §2.1.
-/

public section

open TauCeti TauCeti.Cocharacter

namespace BialgHom

universe u v w

variable {R : Type u} {H : Type v} {K : Type w}
  [CommRing R] [CommRing H] [CommRing K] [HopfAlgebra R H] [HopfAlgebra R K]

/-- The dynamic parabolic of a closed subgroup is the scheme-theoretic inverse image
of the ambient dynamic parabolic. -/
theorem parabolicDefiningHopfIdeal_eq_map_of_surjective
    (φ : H →ₐc[R] K) (hφ : Function.Surjective φ)
    (l : K →ₐc[R] LaurentPolynomial R) :
    parabolicDefiningHopfIdeal l = (parabolicDefiningHopfIdeal (l.comp φ)).map φ := by
  -- Use the all-algebra point criteria of Dynamic.ClosedImmersion.Parabolic and
  -- HopfIdeal.eq_of_forall_quotientPointsSubgroup_eq.
  apply HopfIdeal.eq_of_forall_quotientPointsSubgroup_eq
    (H := _root_.CommHopfAlgCat.of R K)
  intro A
  ext g
  rw [quotientPointsSubgroup_parabolicDefiningHopfIdeal,
    mem_parabolic_iff_of_surjective φ hφ l g,
    ← quotientPointsSubgroup_parabolicDefiningHopfIdeal]
  rw [CommHopfAlgCat.mem_quotientPointsSubgroup_iff,
    CommHopfAlgCat.mem_quotientPointsSubgroup_iff]
  simp only [HopfIdeal.mem_map_iff_of_surjective hφ, BialgHom.mapDomain_apply_apply,
    forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]

/-- The dynamic unipotent subgroup of a closed subgroup is the scheme-theoretic inverse
image of the ambient dynamic unipotent subgroup. -/
theorem unipotentDefiningHopfIdeal_eq_map_of_surjective
    (φ : H →ₐc[R] K) (hφ : Function.Surjective φ)
    (l : K →ₐc[R] LaurentPolynomial R) :
    l.unipotentDefiningHopfIdeal = ((l.comp φ).unipotentDefiningHopfIdeal).map φ := by
  apply HopfIdeal.eq_of_forall_quotientPointsSubgroup_eq
    (H := _root_.CommHopfAlgCat.of R K)
  intro A
  ext g
  rw [quotientPointsSubgroup_unipotentDefiningHopfIdeal,
    mem_unipotent_iff_of_surjective φ hφ l g,
    ← quotientPointsSubgroup_unipotentDefiningHopfIdeal]
  rw [CommHopfAlgCat.mem_quotientPointsSubgroup_iff,
    CommHopfAlgCat.mem_quotientPointsSubgroup_iff]
  simp only [HopfIdeal.mem_map_iff_of_surjective hφ, BialgHom.mapDomain_apply_apply,
    forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]

/-- Pulling back the defining ideal of the dynamic parabolic of a closed subgroup `Z` along
`H → O(Z)` gives the ideal of `Z ∩ P_G(λ)`: the image of that parabolic under `Z ↪ G` is the
intersection of `Z` with the ambient dynamic parabolic. -/
theorem comapOfSurjective_parabolicDefiningHopfIdeal
    (φ : H →ₐc[R] K) (hφ : Function.Surjective φ)
    (l : K →ₐc[R] LaurentPolynomial R) :
    (parabolicDefiningHopfIdeal l).comapOfSurjective φ hφ =
      parabolicDefiningHopfIdeal (l.comp φ) ⊔ HopfIdeal.kerOfSurjective φ hφ := by
  rw [parabolicDefiningHopfIdeal_eq_map_of_surjective φ hφ l, HopfIdeal.comapOfSurjective_map]

/-- Pulling back the defining ideal of the dynamic unipotent subgroup of a closed subgroup `Z`
along `H → O(Z)` gives the ideal of `Z ∩ U_G(λ)`: the image of that subgroup under `Z ↪ G` is the
intersection of `Z` with the ambient dynamic unipotent subgroup. -/
theorem comapOfSurjective_unipotentDefiningHopfIdeal
    (φ : H →ₐc[R] K) (hφ : Function.Surjective φ)
    (l : K →ₐc[R] LaurentPolynomial R) :
    l.unipotentDefiningHopfIdeal.comapOfSurjective φ hφ =
      (l.comp φ).unipotentDefiningHopfIdeal ⊔ HopfIdeal.kerOfSurjective φ hφ := by
  rw [unipotentDefiningHopfIdeal_eq_map_of_surjective φ hφ l, HopfIdeal.comapOfSurjective_map]

end BialgHom
