/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Basis.DiagonalTorus.CharacterMap
import Mathlib.Tactic.NormNum.IsSquare

/-!
# Restriction of the character lattice of a represented torus

Suppose the weights of a representation lie in a sublattice `Λ` of an ambient character
lattice `P`. Parametrizing the torus by `Hom(P, Rˣ)` gives only the image of restriction to
`Hom(Λ, Rˣ)`, not necessarily every point of the represented torus. In coordinates, restriction
is `TauCeti.torusPointMap φ`, where `φ` is the inclusion of character lattices in chosen bases.

This file identifies that image inside the automorphisms of a weighted basis. The comparison
applies to any lattice map, with no finite-index assumption. In particular, over a ring with
divisible units, an injective lattice map does give the entire point group. Over `ℚ`, doubling
the character lattice instead gives a proper subgroup: the torus coordinates must be squares.
For the adjoint `A₁` weights `2, 0, -2` in the full weight lattice, this is precisely the
distinction between `diag(s², 1, s⁻²)` and the actual torus `diag(a, 1, a⁻¹)`.

The lattice-coordinate formula `Module.Basis.weightTorus_submodule` makes the comparison
available for weights in an actual submodule, rather than just for an abstract lattice map.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Lemma 28(c).
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1.

The construction uses `TauCeti.torusPointMap` and its character-evaluation identity; no new
torus carrier is introduced.
-/

public section

namespace Module.Basis

open TauCeti

variable {ι κ ν R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [Fintype κ] [Fintype ν]

/-- Pulling back the weights along a lattice map is restriction of the torus parameters. -/
@[simp]
theorem weightTorus_torusPointMap [DecidableEq κ] (b : Basis ι R M) (wt : ι → κ → ℤ)
    (φ : (κ → ℤ) →ₗ[ℤ] (ν → ℤ)) (s : ν → Rˣ) :
    basisWeightTorus b wt (torusPointMap φ s) =
      basisWeightTorus b (fun i => φ (wt i)) s := by
  simp only [basisWeightTorus_apply, torusCharacter_torusPointMap]

/-- If the coordinate weights span, a point of the actual torus belongs to the ambient-lattice
parametrization exactly when its parameter extends along the character-lattice map. -/
theorem weightTorus_mem_range_iff [DecidableEq κ] (b : Basis ι R M) (wt : ι → κ → ℤ)
    (hwt : Submodule.span ℤ (Set.range wt) = ⊤)
    (φ : (κ → ℤ) →ₗ[ℤ] (ν → ℤ)) (s : κ → Rˣ) :
    basisWeightTorus b wt s ∈ (basisWeightTorus b (fun i => φ (wt i))).range ↔
      s ∈ (torusPointMap (R := R) φ).range := by
  constructor
  · rintro ⟨u, hu⟩
    exact ⟨u, basisWeightTorus_injective b hwt
      ((b.weightTorus_torusPointMap wt φ u).trans hu)⟩
  · rintro ⟨u, rfl⟩
    exact ⟨u, (b.weightTorus_torusPointMap wt φ u).symm⟩

/-- If the units are divisible, restricting along an injective lattice map does not change the
image of a represented torus on points. This need not hold over an arbitrary field. -/
theorem range_weightTorus_eq_of_injective [RootableBy Rˣ ℕ]
    (b : Basis ι R M) (wt : ι → κ → ℤ)
    {φ : (κ → ℤ) →ₗ[ℤ] (ν → ℤ)} (hφ : Function.Injective φ) :
    (basisWeightTorus b (fun i => φ (wt i))).range = (basisWeightTorus b wt).range := by
  classical
  ext g
  constructor
  · rintro ⟨s, rfl⟩
    exact ⟨torusPointMap φ s, b.weightTorus_torusPointMap wt φ s⟩
  · rintro ⟨s, rfl⟩
    obtain ⟨u, rfl⟩ := torusPointMap_surjective_of_injective hφ s
    exact ⟨u, (b.weightTorus_torusPointMap wt φ u).symm⟩

/-- For weights in a sublattice, reading them in the ambient lattice factors through the
restriction map, written using a basis of the sublattice. -/
theorem weightTorus_submodule [DecidableEq κ] (b : Basis ι R M) (Λ : Submodule ℤ (ν → ℤ))
    (c : Basis κ ℤ Λ) (wt : ι → Λ) (s : ν → Rˣ) :
    basisWeightTorus b (fun i => (wt i : ν → ℤ)) s =
      basisWeightTorus b (fun i => c.equivFun (wt i))
        (torusPointMap (Λ.subtype ∘ₗ c.equivFun.symm.toLinearMap) s) := by
  rw [weightTorus_torusPointMap]
  simp

/-- Doubling the character lattice reaches exactly the points whose coordinates are squares,
provided the original weights span the character lattice. -/
theorem weightTorus_mem_range_two_smul_iff (b : Basis ι R M) (wt : ι → κ → ℤ)
    (hwt : Submodule.span ℤ (Set.range wt) = ⊤) (s : κ → Rˣ) :
    basisWeightTorus b wt s ∈ (basisWeightTorus b (fun i => (2 : ℤ) • wt i)).range ↔
      ∀ j, IsSquare (s j) := by
  classical
  have htwo : (fun i => (2 : ℤ) • wt i) =
      (fun i => (2 • (1 : Module.End ℤ (κ → ℤ))) (wt i)) := by
    ext i j
    simp [two_smul, two_mul]
  rw [htwo, b.weightTorus_mem_range_iff wt hwt]
  simp only [torusPointMap_nsmul, torusPointMap_one, MonoidHom.mem_range,
    MonoidHom.pow_apply, MonoidHom.id_apply]
  constructor
  · rintro ⟨u, rfl⟩ j
    exact ⟨u j, pow_two _⟩
  · intro h
    choose u hu using h
    exact ⟨u, funext fun j => (pow_two _).trans (hu j).symm⟩

/-- Over the rationals, doubling the weights gives a proper subgroup of the torus whenever the
original weights span a nonzero character lattice. In rank one this is the full-weight versus
root-lattice parametrization of the adjoint `A₁` torus. -/
theorem range_weightTorus_two_smul_lt_rat {V : Type*} [AddCommGroup V] [Module ℚ V]
    [Nonempty κ] (b : Basis ι ℚ V) (wt : ι → κ → ℤ)
    (hwt : Submodule.span ℤ (Set.range wt) = ⊤) :
    (basisWeightTorus b (fun i => (2 : ℤ) • wt i)).range <
      (basisWeightTorus b wt).range := by
  classical
  refine lt_iff_le_not_ge.mpr ⟨?_, ?_⟩
  · rintro g ⟨s, rfl⟩
    refine ⟨torusPointMap (2 • (1 : Module.End ℤ (κ → ℤ))) s, ?_⟩
    exact b.weightTorus_torusPointMap wt _ s
  · intro h
    let a : ℚˣ := Units.mk0 2 (by norm_num)
    have ha := (b.weightTorus_mem_range_two_smul_iff wt hwt (fun _ => a)).mp
      (h ⟨fun _ => a, rfl⟩) (Classical.arbitrary κ)
    obtain ⟨u, hu⟩ := ha
    have hs : IsSquare (2 : ℚ) := ⟨(u : ℚ), congrArg Units.val hu⟩
    norm_num at hs

end Module.Basis
