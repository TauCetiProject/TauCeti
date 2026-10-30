/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Basis.DiagonalTorus.CharacterMap
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.GeckLattice.Frobenius

/-!
# Character maps on the weight torus of the pinned Geck carrier

The points `TauCeti.DynkinType.geckPoints t ht A` of the pinned Geck carrier of a valid Dynkin type
contain the represented weight torus `TauCeti.DynkinType.geckWeightTorusPoints t ht A`, a
homomorphism from `Fin t.rank → Aˣ` indexed by the fundamental-weight coordinates. This file reads
the general theory of character maps (`TauCeti.IsCharacterMap`) on that torus.

* The `p ^ k`-power Frobenius `TauCeti.DynkinType.geckFrobenius` has character map `p ^ k • 1`.
* **Lang's equation on the torus.** Over a ring of characteristic `p` whose units are divisible,
  such as an algebraically closed field (`TauCeti.IsAlgClosed.unitsRootableByNat`), if an
  endomorphism `F` of the carrier points has a character map `φ` with `φ ^ n = p ^ r • 1` and
  `0 < r`, then every point `T s` of the weight torus is `T u * (F (T u))⁻¹` for some `u`. The
  hypothesis `0 < r` cannot be dropped: `F = id` with `φ = 1` satisfies `φ ^ 1 = p ^ 0 • 1`, and
  `T u * (T u)⁻¹ = 1`. In characteristic zero the hypothesis reads `φ ^ n = 0`.

The torus parametrization of this carrier is not injective in general: the Geck weights span the
root lattice `Q`, so a parameter in `Hom(P, Aˣ)`, for `P` the weight lattice, acts trivially
exactly when it kills `Q`. For example, in type `A₁` the weights are `2ϖ, 0, -2ϖ` and the
parameter `-1` acts trivially. Lang's equation is a statement about torus points and does not
need injectivity; uniqueness of character maps (`TauCeti.IsCharacterMap.unique`) does, and is
not asserted here.

## Main results

* `TauCeti.DynkinType.isCharacterMap_geckFrobenius`: the Frobenius acts on the weight torus
  through `p ^ k • 1`.
* `TauCeti.DynkinType.exists_geckWeightTorusPoints_eq_mul_inv`: Lang's equation on the weight
  torus.
* `TauCeti.DynkinType.exists_geckWeightTorusPoints_eq_mul_inv_geckFrobenius`: its instance for
  the Frobenius in prime characteristic.

## References

* R. Steinberg, *Endomorphisms of linear algebraic groups*, Mem. Amer. Math. Soc. **80** (1968),
  Theorem 10.1 (the Lang–Steinberg theorem).
* R. W. Carter, *Finite Groups of Lie Type: Conjugacy Classes and Complex Characters*, §1.17.
-/

public section

namespace TauCeti.DynkinType

universe v

variable (t : DynkinType) (ht : t.Valid)

/-- **The Frobenius acts on the weight torus of the Geck carrier through `p ^ k • 1`**, since it
raises every torus point to its `p ^ k`-th power. -/
theorem isCharacterMap_geckFrobenius (p k : ℕ) (A : Type v) [CommRing A] [ExpChar A p] :
    IsCharacterMap (t.geckWeightTorusPoints ht A) (t.geckFrobenius ht p k A) ((p ^ k : ℕ) • 1) :=
  isCharacterMap_iff.mpr fun s => by
    rw [geckFrobenius_geckWeightTorusPoints, torusPointMap_nsmul, torusPointMap_one,
      MonoidHom.pow_apply, MonoidHom.id_apply]

/-- **Lang's equation on the weight torus of the Geck carrier.** Over a ring of characteristic `p`
whose units are divisible, for instance an algebraically closed field, if `φ` is a character map
of an endomorphism `F` with `φ ^ n = p ^ r • 1` for some `r > 0`, then every point of the weight
torus is `T u * (F (T u))⁻¹` for some `u`. -/
theorem exists_geckWeightTorusPoints_eq_mul_inv {K : Type v} [CommRing K] [Nontrivial K]
    [RootableBy Kˣ ℕ] (p : ℕ) [CharP K p] {F : t.geckPoints ht K →* t.geckPoints ht K}
    {φ : Module.End ℤ (Fin t.rank → ℤ)} (hF : IsCharacterMap (t.geckWeightTorusPoints ht K) F φ)
    {n r : ℕ} (hr : 0 < r) (hφ : φ ^ n = (p ^ r : ℕ) • 1) (s : Fin t.rank → Kˣ) :
    ∃ u, t.geckWeightTorusPoints ht K s =
      t.geckWeightTorusPoints ht K u * (F (t.geckWeightTorusPoints ht K u))⁻¹ := by
  have hpr : ((p ^ r : ℕ) : ℤ) ≠ 1 := by
    rw [Nat.cast_ne_one, Ne, pow_eq_one_iff, not_or]
    exact ⟨CharP.char_ne_one K p, hr.ne'⟩
  exact hF.exists_eq_mul_inv
    (injective_one_sub_of_pow_eq_smul_one (by rwa [Nat.cast_smul_eq_nsmul]) hpr) s

/-- **Lang's equation on the weight torus for the Frobenius.** Over a ring of prime characteristic
`p` whose units are divisible, for instance an algebraically closed field, and for `k > 0`, every
point of the weight torus of the Geck carrier is `T u * (F (T u))⁻¹` for the `p ^ k`-power
Frobenius `F`: the equation `s = u * u ^ (-p ^ k)` is solvable coordinatewise. -/
theorem exists_geckWeightTorusPoints_eq_mul_inv_geckFrobenius {K : Type v} [CommRing K]
    [Nontrivial K] [RootableBy Kˣ ℕ] (p : ℕ) [Fact p.Prime] [CharP K p] {k : ℕ} (hk : 0 < k)
    (s : Fin t.rank → Kˣ) :
    ∃ u, t.geckWeightTorusPoints ht K s =
      t.geckWeightTorusPoints ht K u *
        (t.geckFrobenius ht p k K (t.geckWeightTorusPoints ht K u))⁻¹ :=
  t.exists_geckWeightTorusPoints_eq_mul_inv ht p (t.isCharacterMap_geckFrobenius ht p k K) hk
    (pow_one _) s

end TauCeti.DynkinType
