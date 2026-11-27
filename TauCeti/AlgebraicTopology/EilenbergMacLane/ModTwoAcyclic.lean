/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.ClassifyingSpace.EilenbergMacLane
public import TauCeti.AlgebraicTopology.EilenbergMacLane.UniquelyDivisible
public import TauCeti.AlgebraicTopology.Homotopy.Hurewicz.TwoDivisible
public import TauCeti.AlgebraicTopology.Singular.Coefficients.ModTwo

/-!
# Mod-two acyclic Eilenberg--Mac Lane spaces

Let `A` be an abelian group and `n ≥ 1`. Every Eilenberg--Mac Lane space of type `K(A, n)` has the
mod-two homology of a point exactly when `A` is uniquely two-divisible, that is when
multiplication by two is a bijection of `A`
(`TauCeti.IsEilenbergMacLaneSpace.forall_subsingleton_singularHomology_iff_isUniquelyTwoDivisible`).
Homology is taken with coefficients in the field `𝔽₂`, given as any ring `k` isomorphic to
`ZMod 2`. One direction is
`TauCeti.IsEilenbergMacLaneSpace.subsingleton_singularHomology_of_isUniquelyTwoDivisible`, the input
on Eilenberg--Mac Lane spaces of Serre's mod-two vanishing theorem. This file proves the converse
(`TauCeti.IsEilenbergMacLaneSpace.isUniquelyTwoDivisible_of_subsingleton_singularHomology`), which
shows that the hypothesis of that theorem excludes the groups that are not uniquely
two-divisible. In particular no `K(ℤ/2, n)` space, such as the infinite real projective space
`ℝP^∞ = K(ℤ/2, 1)` or Milnor's classifying space of `ℤ/2`, has the mod-two homology of a point
(`TauCeti.IsEilenbergMacLaneSpace.not_forall_subsingleton_singularHomology_zmod_two`).

The converse needs only the two homology groups in the degrees `n` and `n + 1`. Write `Hᵢ(X; ℤ)`
and `Hᵢ(X; ℤ/2)` for integral and mod-two singular homology. By the coefficient sequence
`0 ⟶ ℤ ⟶ ℤ ⟶ ℤ/2 ⟶ 0`, vanishing of `Hₙ(X; ℤ/2)` and `Hₙ₊₁(X; ℤ/2)` makes multiplication by two
bijective on `Hₙ(X; ℤ)` (`TopCat.isUniquelyTwoDivisible_singularHomology_of_isZero_mod_two`), and
for a `K(A, n)` space `Hₙ(X; ℤ) ≅ A` by the Hurewicz theorem: in degree one because the first
integral homology of a `K(G, 1)` space is the abelianization of `G`
(`TauCeti.IsEilenbergMacLaneSpaceOne.nonempty_addEquiv_singularHomology_one`), which for an abelian
group is the group itself
(`TauCeti.IsEilenbergMacLaneSpaceOne.nonempty_addEquiv_singularHomology_one_of_comm`), and for
`n ≥ 2` for an `(n - 1)`-connected space
(`TauCeti.isUniquelyTwoDivisible_homotopyGroup_of_subsingleton_mod_two`).

In degree one the first mod-two homology alone detects two-divisibility: since `H₀(X; ℤ)` is free,
`H₁(X; ℤ/2)` is `H₁(X; ℤ) ⧸ 2 H₁(X; ℤ)` (`TopCat.singularHomologyOneModTwoAddEquiv`), so it
vanishes exactly when multiplication by two is onto `H₁(X; ℤ)`
(`TopCat.subsingleton_singularHomology_one_iff_surjective_zsmul`). For a `K(A, 1)` space it thus
vanishes exactly when `A = 2 A`
(`TauCeti.IsEilenbergMacLaneSpaceOne.subsingleton_singularHomology_one_iff_surjective_zsmul`). For
`A = ℤ/2` this is the nonvanishing of `H₁(ℝP^∞; 𝔽₂)`.

## Main results

* `TauCeti.IsEilenbergMacLaneSpaceOne.subsingleton_singularHomology_one_iff_surjective_zsmul`: the
  first mod-two homology of a `K(A, 1)` space vanishes exactly when `A` is two-divisible.
* `TauCeti.IsEilenbergMacLaneSpace.isUniquelyTwoDivisible_of_subsingleton_singularHomology`: if a
  `K(A, n)` space has vanishing mod-two homology in the degrees `n` and `n + 1`, then `A` is
  uniquely two-divisible.
* `TauCeti.IsEilenbergMacLaneSpace.forall_subsingleton_singularHomology_iff_isUniquelyTwoDivisible`:
  a `K(A, n)` space has the mod-two homology of a point exactly when `A` is uniquely
  two-divisible.
* `TauCeti.IsEilenbergMacLaneSpace.not_forall_subsingleton_singularHomology_zmod_two` and
  `TauCeti.not_subsingleton_classifyingSpace_singularHomology_one_zmod_two`: `K(ℤ/2, n)` spaces
  are not mod-two acyclic, and Milnor's classifying space of `ℤ/2` has nonzero first mod-two
  homology.

## References

* J.-P. Serre, *Groupes d'homotopie et classes de groupes abéliens*, Ann. of Math. 58 (1953),
  258–294.
* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 2.A (Hurewicz in
  degree one), Section 3.A (change of coefficients) and Section 4.2.
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicTopology

universe u v

namespace TauCeti

variable {k : Type u} [CommRing k] {X : Type u} [TopologicalSpace X] {x : X}

namespace IsEilenbergMacLaneSpaceOne

variable {A : Type v} [AddCommGroup A]

/-- **The first mod-two homology of a `K(A, 1)` space vanishes exactly when `A` is
two-divisible.** For an abelian group `A`, a `K(A, 1)` space `X` and a ring `k` isomorphic to
`ZMod 2`, `H₁(X; k) = 0` exactly when multiplication by two is onto `A`. -/
theorem subsingleton_singularHomology_one_iff_surjective_zsmul (e : k ≃+* ZMod 2)
    (hX : IsEilenbergMacLaneSpaceOne (Multiplicative A) X x) :
    Subsingleton (((singularChains k).obj (TopCat.of X)).homology 1) ↔
      Function.Surjective fun a : A ↦ (2 : ℤ) • a := by
  obtain ⟨ψ⟩ := hX.nonempty_addEquiv_singularHomology_one_of_comm
  -- multiplication by two on `A` is conjugate through `ψ` to that on `H₁(X; ℤ)`
  have hψ : (fun a : A ↦ (2 : ℤ) • a) = ψ.symm ∘ (fun y ↦ (2 : ℤ) • y) ∘ ψ := by
    ext a
    simp
  rw [hψ, EquivLike.comp_surjective, EquivLike.surjective_comp,
    ← singularHomologyFunctor_obj_obj]
  exact (TopCat.of X).subsingleton_singularHomology_one_iff_surjective_zsmul e

/-- **A mod-two acyclic `K(A, 1)` space has a uniquely two-divisible group.** If a `K(A, 1)` space
`X` has vanishing first and second homology with coefficients in a ring `k` isomorphic to
`ZMod 2`, then multiplication by two is a bijection of `A`. -/
theorem isUniquelyTwoDivisible_of_subsingleton_singularHomology (e : k ≃+* ZMod 2)
    (hX : IsEilenbergMacLaneSpaceOne (Multiplicative A) X x)
    (h₁ : Subsingleton (((singularChains k).obj (TopCat.of X)).homology 1))
    (h₂ : Subsingleton (((singularChains k).obj (TopCat.of X)).homology 2)) :
    IsUniquelyTwoDivisible A := by
  obtain ⟨φ⟩ := hX.nonempty_addEquiv_singularHomology_one_of_comm
  rw [← singularHomologyFunctor_obj_obj] at h₁ h₂
  exact ((TopCat.of X).isUniquelyTwoDivisible_singularHomology_of_isZero_mod_two 1
    (((TopCat.of X).isZero_singularHomology_zmod_iff_of_ringEquiv 2 e 1).2
      (ModuleCat.isZero_iff_subsingleton.2 h₁))
    (((TopCat.of X).isZero_singularHomology_zmod_iff_of_ringEquiv 2 e 2).2
      (ModuleCat.isZero_iff_subsingleton.2 h₂))).of_addEquiv φ.symm

/-- **`K(ℤ/2, 1)` spaces have nonzero first mod-two homology.** For every `K(ℤ/2, 1)` space `X`,
such as `ℝP^∞`, and every ring `k` isomorphic to `ZMod 2`, the group `H₁(X; k)` is nonzero:
multiplication by two is not onto `ℤ/2`. -/
theorem not_subsingleton_singularHomology_one_zmod_two (e : k ≃+* ZMod 2)
    (hX : IsEilenbergMacLaneSpaceOne (Multiplicative (ZMod 2)) X x) :
    ¬Subsingleton (((singularChains k).obj (TopCat.of X)).homology 1) := by
  rw [subsingleton_singularHomology_one_iff_surjective_zsmul e hX]
  rintro h
  obtain ⟨a, ha⟩ := h 1
  -- in `ZMod 2`, twice every element is zero
  dsimp only at ha
  rw [two_zsmul, CharTwo.add_self_eq_zero] at ha
  exact zero_ne_one ha

end IsEilenbergMacLaneSpaceOne

namespace IsEilenbergMacLaneSpace

/-- **A mod-two acyclic `K(A, n)` space has a uniquely two-divisible group.** For an abelian
group `A`, `n ≥ 1` and a `K(A, n)` space `X` whose homology in the degrees `n` and `n + 1`
vanishes with coefficients in a ring `k` isomorphic to `ZMod 2`, multiplication by two is a
bijection of `A`. With vanishing in all positive degrees this is the converse of
`TauCeti.IsEilenbergMacLaneSpace.subsingleton_singularHomology_of_isUniquelyTwoDivisible`. -/
theorem isUniquelyTwoDivisible_of_subsingleton_singularHomology (e : k ≃+* ZMod 2)
    {A : Type v} [AddCommGroup A] {n : ℕ} [NeZero n]
    (hX : IsEilenbergMacLaneSpace (Multiplicative A) n X x)
    (hn : Subsingleton (((singularChains k).obj (TopCat.of X)).homology n))
    (hn' : Subsingleton (((singularChains k).obj (TopCat.of X)).homology (n + 1))) :
    IsUniquelyTwoDivisible A := by
  obtain _ | _ | n := n
  · exact (NeZero.ne 0 rfl).elim
  · exact IsEilenbergMacLaneSpaceOne.isUniquelyTwoDivisible_of_subsingleton_singularHomology e
      (isEilenbergMacLaneSpace_one_iff.1 hX) hn hn'
  · -- for `n ≥ 2` the space is `(n - 1)`-connected and `πₙ ≅ A` is its first nonzero group
    obtain ⟨φ⟩ := hX.nonempty_homotopyGroupMulEquiv
    exact (isUniquelyTwoDivisible_homotopyGroup_of_subsingleton_mod_two e
      (fun j hj ↦ hX.subsingleton_homotopyGroup hj.ne) hn hn').of_addEquiv
      (MulEquiv.toAdditiveLeft φ)

/-- **Mod-two acyclic Eilenberg--Mac Lane spaces.** For an abelian group `A` and `n ≥ 1`, a
`K(A, n)` space has the mod-two homology of a point, with coefficients in a ring `k` isomorphic
to `ZMod 2`, exactly when `A` is uniquely two-divisible. -/
theorem forall_subsingleton_singularHomology_iff_isUniquelyTwoDivisible (e : k ≃+* ZMod 2)
    {A : Type u} [AddCommGroup A] {n : ℕ} [NeZero n]
    (hX : IsEilenbergMacLaneSpace (Multiplicative A) n X x) :
    (∀ i, Subsingleton (((singularChains k).obj (TopCat.of X)).homology (i + 1))) ↔
      IsUniquelyTwoDivisible A := by
  have : IsSemisimpleRing k := e.symm.isSemisimpleRing
  have hk : (2 : k) = 0 := e.injective (by rw [map_ofNat, map_zero]; decide)
  refine ⟨fun h ↦ ?_, fun hA ↦ subsingleton_singularHomology_of_isUniquelyTwoDivisible k hk hA hX⟩
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero (NeZero.ne n)
  exact hX.isUniquelyTwoDivisible_of_subsingleton_singularHomology e (h m) (h (m + 1))

/-- **`K(ℤ/2, n)` spaces are not mod-two acyclic.** For `n ≥ 1`, no `K(ℤ/2, n)` space has the
mod-two homology of a point, with coefficients in a ring `k` isomorphic to `ZMod 2`: the group
`ℤ/2` is not uniquely two-divisible. -/
theorem not_forall_subsingleton_singularHomology_zmod_two (e : k ≃+* ZMod 2) {n : ℕ} [NeZero n]
    (hX : IsEilenbergMacLaneSpace (Multiplicative (ZMod 2)) n X x) :
    ¬∀ i, Subsingleton (((singularChains k).obj (TopCat.of X)).homology (i + 1)) := by
  intro h
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero (NeZero.ne n)
  exact Nat.not_odd_iff_even.2 even_two ((isUniquelyTwoDivisible_zmod_iff 2).1
    (hX.isUniquelyTwoDivisible_of_subsingleton_singularHomology e (h m) (h (m + 1))))

end IsEilenbergMacLaneSpace

/-- **Milnor's classifying space of `ℤ/2` has nonzero first mod-two homology.** It is a
`K(ℤ/2, 1)` space, so `H₁(B(ℤ/2); 𝔽₂)` is nonzero. -/
theorem not_subsingleton_classifyingSpace_singularHomology_one_zmod_two :
    ¬Subsingleton (((singularChains (ZMod 2)).obj
      (TopCat.of (classifyingSpace (Multiplicative (ZMod 2))))).homology 1) :=
  (isEilenbergMacLaneSpaceOne_classifyingSpace _).not_subsingleton_singularHomology_one_zmod_two
    (RingEquiv.refl _)

end TauCeti
