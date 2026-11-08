/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Basis.DiagonalTorus.CharacterMap
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.GeckLattice.TwistedFrobenius

/-!
# Character maps on the weight torus of the pinned Geck carrier

The points `TauCeti.DynkinType.geckPoints t ht A` of the pinned Geck carrier of a valid Dynkin type
contain the represented weight torus `TauCeti.DynkinType.geckWeightTorusPoints t ht A`, a
homomorphism from `Fin t.rank → Aˣ` indexed by the fundamental-weight coordinates. This file reads
the general theory of character maps (`TauCeti.IsCharacterMap`) on that torus.

* The `p ^ k`-power Frobenius `TauCeti.DynkinType.geckFrobenius` has character map `p ^ k • 1`.
* The graph automorphism `TauCeti.DynkinType.geckGraphAutPoints` of a diagram symmetry `σ` has
  character map the weight map of the inverse of the diagram automorphism
  `TauCeti.DynkinType.diagramAut σ` of the pinned root datum, which is precomposition of characters
  with `σ`. The inverse is forced by the pullback orientation of character maps: `γ` relabels the
  coordinates of a torus point by `σ⁻¹`, while `diagramAut σ` permutes the fundamental weights by
  `σ`. The graph-twisted Frobenius `TauCeti.DynkinType.geckTwistedFrobenius` therefore has the
  composite character map `p ^ k • (diagramAut σ)⁻¹.weightMap`.
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
* `TauCeti.DynkinType.isCharacterMap_geckGraphAutPoints` and
  `TauCeti.DynkinType.isCharacterMap_geckTwistedFrobenius`: the graph automorphism and the
  graph-twisted Frobenius act on the weight torus through the inverse diagram automorphism of the
  pinned root datum, after multiplication by `p ^ k` for the latter.
* `TauCeti.DynkinType.exists_geckWeightTorusPoints_eq_mul_inv_geckTwistedFrobenius`: Lang's
  equation on the weight torus for every graph-twisted Frobenius in prime characteristic.

## References

* R. Steinberg, *Endomorphisms of linear algebraic groups*, Mem. Amer. Math. Soc. **80** (1968),
  Theorem 10.1 (the Lang–Steinberg theorem).
* R. W. Carter, *Finite Groups of Lie Type: Conjugacy Classes and Complex Characters*, §1.17.
* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 10 (graph automorphisms).
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

/-! ## The graph automorphism and the graph-twisted Frobenius -/

variable {sigma : Equiv.Perm (Fin t.rank)} (hsigma : sigma ∈ t.diagramSymmetry)

/-- **The graph automorphism acts on the weight torus of the Geck carrier through the inverse
diagram automorphism** of the pinned simply connected root datum. It relabels the coordinates of a
torus point by `σ⁻¹`, so it pulls the fundamental weight `ϖᵢ` back to `ϖ_{σ⁻¹ i}`: that is the
weight map of `(diagramAut σ)⁻¹`, which is precomposition of characters with `σ`. -/
theorem isCharacterMap_geckGraphAutPoints (A : Type v) [CommRing A] :
    IsCharacterMap (t.geckWeightTorusPoints ht A) (t.geckGraphAutPoints ht hsigma A).toMonoidHom
      (diagramAut ht hsigma)⁻¹.toHom.weightMap :=
  isCharacterMap_iff.mpr fun s => by
    rw [MulEquiv.coe_toMonoidHom, geckGraphAutPoints_geckWeightTorusPoints,
      diagramAut_inv_weightMap, torusPointMap_funCongrLeft]
    simp only [Equiv.Perm.inv_def]

/-- **The graph-twisted Frobenius acts on the weight torus of the Geck carrier through
`p ^ k • (diagramAut σ)⁻¹.weightMap`**, the composite of the character maps of its two factors. -/
theorem isCharacterMap_geckTwistedFrobenius (p k : ℕ) (A : Type v) [CommRing A] [ExpChar A p] :
    IsCharacterMap (t.geckWeightTorusPoints ht A) (t.geckTwistedFrobenius ht hsigma p k A)
      ((p ^ k : ℕ) • (diagramAut ht hsigma)⁻¹.toHom.weightMap) := by
  have h := (t.isCharacterMap_geckGraphAutPoints ht hsigma A).comp
    (t.isCharacterMap_geckFrobenius ht p k A)
  rw [smul_mul_assoc, one_mul] at h
  refine isCharacterMap_iff.mpr fun s => ?_
  rw [geckTwistedFrobenius_apply]
  exact h.map_apply s

/-- **Lang's equation on the weight torus for the graph-twisted Frobenius.** Over a ring of prime
characteristic `p` whose units are divisible, for instance an algebraically closed field, and for
`k > 0`, every point of the weight torus of the Geck carrier is `T u * (F (T u))⁻¹` for the
graph-twisted `p ^ k`-power Frobenius `F`. Its character map raised to the order `e` of `σ` is
`p ^ (k * e) • 1`. -/
theorem exists_geckWeightTorusPoints_eq_mul_inv_geckTwistedFrobenius {K : Type v} [CommRing K]
    [Nontrivial K] [RootableBy Kˣ ℕ] (p : ℕ) [Fact p.Prime] [CharP K p] {k : ℕ} (hk : 0 < k)
    (s : Fin t.rank → Kˣ) :
    ∃ u, t.geckWeightTorusPoints ht K s =
      t.geckWeightTorusPoints ht K u *
        (t.geckTwistedFrobenius ht hsigma p k K (t.geckWeightTorusPoints ht K u))⁻¹ := by
  refine t.exists_geckWeightTorusPoints_eq_mul_inv ht p
    (t.isCharacterMap_geckTwistedFrobenius ht hsigma p k K) (n := orderOf sigma)
    (Nat.mul_pos hk (orderOf_pos sigma)) ?_ s
  -- The weight map is multiplicative in the automorphism, and `σ` has finite order.
  have hweight (g : (t.simplyConnectedRootDatum ht).Aut) : g.toHom.weightMap =
      LinearEquiv.automorphismGroup.toLinearMapMonoidHom
        (RootPairing.Equiv.weightHom (t.simplyConnectedRootDatum ht) g) := by
    ext
    simp
  rw [smul_pow, hweight, ← map_pow, ← map_pow, inv_pow,
    diagramAut_pow_eq_one ht hsigma (pow_orderOf_eq_one sigma), inv_one, map_one, map_one,
    ← pow_mul]

end TauCeti.DynkinType
