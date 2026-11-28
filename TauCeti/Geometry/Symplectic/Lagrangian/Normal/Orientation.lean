/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Lagrangian.TotallyReal
public import TauCeti.Geometry.Symplectic.Orientation
public import TauCeti.LinearAlgebra.TotallyReal.Normal

/-!
# The normal orientation of a Lagrangian subspace

Let `ω` be a symplectic form on a real vector space `V` of dimension `2n` taming an almost complex
structure `J`, and let `L` be a maximal totally real subspace for `J`, for instance a Lagrangian
subspace (`TauCeti.SymplecticForm.IsLagrangian.isMaximalTotallyReal_of_tames`). The structure `J`
identifies `L` with its normal space `V ⧸ L` by `v ↦ [J v]`
(`TauCeti.IsMaximalTotallyReal.normalEquiv`). On the other hand an orientation `o` of `L` and the
symplectic orientation of `V` induce an orientation of `V ⧸ L`, the one which, preceded by `o`,
gives the orientation of `V` (`Orientation.cokerOfExact`). This file shows that the two
orientations of the normal space differ by `(-1) ^ n.choose 2`
(`TauCeti.SymplecticForm.Tames.cokerOfExact_orientation`).

The reason is that a basis `(a₁, …, aₙ)` of `L` gives the `J`-adapted basis
`(a₁, J a₁, …, aₙ, J aₙ)` of `V`, which is positive for the symplectic orientation
(`TauCeti.SymplecticForm.Tames.orientation_reindex`), while `o` followed by the image of `o` on the
normal space orients `V` by `(a₁, …, aₙ, J a₁, …, J aₙ)`. These two orders differ by a shuffle of
sign `(-1) ^ n.choose 2` (`TauCeti.IsMaximalTotallyReal.ofExact_map_normalEquiv`).

For `n = 2` the sign is `-1`: in a symplectic four-dimensional space, the identification of a
Lagrangian plane with its normal plane by a tamed `J` **reverses** the normal orientation induced
by the orientations of the plane and of the space
(`TauCeti.SymplecticForm.IsLagrangian.cokerOfExact_orientation_of_finrank_eq_two`). Applied
fibrewise along an embedded Lagrangian surface `S` of a symplectic four-manifold, the normal bundle
of `S` is its tangent bundle with the opposite orientation, so its Euler number is `-χ(S)`; for a
Lagrangian sphere this is `-2`. These global statements are
`SmoothEmbedding.evalFundamentalClass_eulerClass_lagrangianNormalOrientation_of_finrank_eq_two`
and `SmoothEmbedding.evalFundamentalClass_eulerClass_lagrangianNormalOrientation_sphere` in
`TauCeti.Geometry.Symplectic.Lagrangian.Normal.EulerClass`; the identification of this normal Euler
number with the homological self-intersection number is not formalized. For `n = 1`, a totally real
line in a plane, the sign is `+1`.

## Main results

* `TauCeti.SymplecticForm.Tames.ofExact_map_normalEquiv`: an orientation of `L` followed by its
  image on the normal space under `J` induces `(-1) ^ n.choose 2` times the symplectic
  orientation.
* `TauCeti.SymplecticForm.Tames.cokerOfExact_orientation`: the normal orientation induced by an
  orientation of `L` and the symplectic orientation is `(-1) ^ n.choose 2` times the image of the
  orientation of `L` under `J`.
* `TauCeti.SymplecticForm.IsLagrangian.cokerOfExact_orientation_of_finrank_eq_two`: for a
  Lagrangian plane in a four-dimensional symplectic space, `J` reverses the normal orientation.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix E, for the self-intersection of a Lagrangian sphere.
-/

public section

open Module

namespace TauCeti

namespace SymplecticForm

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
  {ω : SymplecticForm V} {J : AlmostComplexStructure V} {L : Submodule ℝ V} {n : ℕ}

/-- **The normal orientation of a totally real subspace of a tamed pair, in `V`.** Let `ω` tame
`J` and let `L` be maximal totally real for `J`, of dimension `n` in the `2n`-dimensional space
`V`. An orientation `o` of `L` followed by its image under the normal identification
`v ↦ [J v]` on `V ⧸ L` induces `(-1) ^ n.choose 2` times the symplectic orientation of `V`. -/
theorem Tames.ofExact_map_normalEquiv (hJ : ω.Tames J) (hL : IsMaximalTotallyReal J.toLinearMap L)
    (o : Orientation ℝ L (Fin n)) (hn : finrank ℝ L = n) (hk : finrank ℝ V = n + n) :
    Orientation.ofExact L.injective_subtype (LinearMap.exact_subtype_mkQ L) L.mkQ_surjective o
        (Orientation.map (Fin n) (hL.normalEquiv (J.injective_domRestrict L)) o) hn
        ((hL.finrank_quotient (J.injective_domRestrict L)).trans hn) =
      (-1 : ℝˣ) ^ n.choose 2 • ω.orientation hk := by
  rw [hL.ofExact_map_normalEquiv _ o (finBasisOfFinrankEq ℝ L hn) hn,
    hJ.orientation_reindex (fun i ↦ by
      rw [IsMaximalTotallyReal.doubledBasis_apply_one,
        IsMaximalTotallyReal.doubledBasis_apply_zero]) hk (Nat.mul_two n)]

/-- **The normal orientation of a totally real subspace of a tamed pair.** Let `ω` tame `J` and
let `L` be maximal totally real for `J`, of dimension `n` in the `2n`-dimensional space `V`. The
orientation of the normal space `V ⧸ L` induced by an orientation `o` of `L` and the symplectic
orientation of `V` is `(-1) ^ n.choose 2` times the image of `o` under the normal identification
`v ↦ [J v]`. -/
theorem Tames.cokerOfExact_orientation (hJ : ω.Tames J) (hL : IsMaximalTotallyReal J.toLinearMap L)
    (o : Orientation ℝ L (Fin n)) (hn : finrank ℝ L = n) (hk : finrank ℝ V = n + n) :
    Orientation.cokerOfExact L.injective_subtype (LinearMap.exact_subtype_mkQ L)
        L.mkQ_surjective o (ω.orientation hk) hn
        ((hL.finrank_quotient (J.injective_domRestrict L)).trans hn) =
      (-1 : ℝˣ) ^ n.choose 2 •
        Orientation.map (Fin n) (hL.normalEquiv (J.injective_domRestrict L)) o := by
  refine (Orientation.cokerOfExact_eq_iff _ _ _ _ _ _ _ _).2 ?_
  have h := hJ.ofExact_map_normalEquiv hL o hn hk
  -- The sign is `1` or `-1`; a sign on the quotient orientation moves to the induced one.
  rcases neg_one_pow_eq_or ℝˣ (n.choose 2) with hs | hs
  · simpa only [hs, one_smul] using h
  · simp only [hs, Module.Ray.neg_units_smul, one_smul, Orientation.ofExact_neg_right] at h ⊢
    rw [h]
    exact neg_neg (ω.orientation hk)

/-- **A tamed `J` reverses the normal orientation of a Lagrangian plane.** Let `L` be a Lagrangian
plane in a four-dimensional symplectic space `(V, ω)`, with `ω` taming `J`. The orientation of the
normal plane `V ⧸ L` induced by an orientation `o` of `L` and the symplectic orientation of `V` is
the opposite of the image of `o` under the normal identification `v ↦ [J v]`. This is the linear
algebra behind the self-intersection `-2` of a Lagrangian sphere in a symplectic four-manifold. -/
theorem IsLagrangian.cokerOfExact_orientation_of_finrank_eq_two (hL : ω.IsLagrangian L)
    (hJ : ω.Tames J) (o : Orientation ℝ L (Fin 2)) (hn : finrank ℝ L = 2) :
    Orientation.cokerOfExact L.injective_subtype (LinearMap.exact_subtype_mkQ L)
        L.mkQ_surjective o (ω.orientation (by rw [← hL.two_mul_finrank, hn] : finrank ℝ V = 2 + 2))
        hn (((hL.isMaximalTotallyReal_of_tames hJ).finrank_quotient
          (J.injective_domRestrict L)).trans hn) =
      -Orientation.map (Fin 2) ((hL.isMaximalTotallyReal_of_tames hJ).normalEquiv
        (J.injective_domRestrict L)) o := by
  refine (hJ.cokerOfExact_orientation (hL.isMaximalTotallyReal_of_tames hJ) o hn _).trans ?_
  rw [Nat.choose_self, pow_one, Module.Ray.neg_units_smul, one_smul]

end SymplecticForm

end TauCeti
