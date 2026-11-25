/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Exponential.CommutativeGroup.Isogeny
public import TauCeti.Geometry.Lie.Subgroup.Kernel
public import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.RingTheory.RootsOfUnity.Complex
import TauCeti.Analysis.Fourier.AddCircle

/-!
# The power maps of the circle: characters and period lattices

For a natural number `n`, the power map `z ↦ zⁿ` of the circle is the continuous homomorphism
`ContinuousMonoidHom.id Circle ^ n`. For `n ≠ 0` it is an isogeny of the circle onto itself, and
this file computes how it acts on the two lattices attached to the circle as a compact connected
commutative Lie group.

* **Characters.** Every continuous character of the circle is a power `z ↦ zᵐ` for a unique
  integer `m` (`ContinuousMonoidHom.existsUnique_circle_eq_zpow`). Pulling back along the power
  map multiplies the exponent by `n`, so a character factors through `z ↦ zⁿ` exactly when its
  exponent is divisible by `n`
  (`ContinuousMonoidHom.exists_eq_comp_id_pow_iff`). The characters of the target circle form the
  sublattice `n ℤ` of the character lattice `ℤ` of the source.
* **Period lattices.** For `n > 0` the kernel of the power map is the group of `n`-th roots of
  unity, of order `n` (`TauCeti.card_ker_id_circle_pow`), so by the general index formula for
  isogenies (`ContinuousMonoidHom.relIndex_map_lieMap_periodLattice`) the Lie map of `z ↦ zⁿ`
  carries the period lattice `Λ_ℤ = (2π)⁻¹ ker(exp)` of the source onto a sublattice of index `n`
  in that of the target (`TauCeti.relIndex_map_lieMap_id_circle_pow_periodLattice`).

The case `n = 2` is the restriction of the double cover `SU(2) → SO(3)` to the maximal tori, which
is worked out in `TauCeti.RepresentationTheory.SU2.RotationTorus`.

## Main results

* `ContinuousMonoidHom.exists_eq_comp_id_pow_iff`: a character of the circle factors through
  `z ↦ zⁿ` exactly when it is `z ↦ z^(n k)` for an integer `k`.
* `TauCeti.card_ker_id_circle_pow`: the kernel of `z ↦ zⁿ` has `n` elements.
* `TauCeti.relIndex_map_lieMap_id_circle_pow_periodLattice`: the image of the period lattice under
  the Lie map of `z ↦ zⁿ` has index `n`.

## References

* T. Bröcker and T. tom Dieck, *Representations of Compact Lie Groups*, Springer GTM 98 (1985),
  Chapter I, § 3 (The Exponential Map) and Chapter II, § 8 (Characters of tori).
-/

public section

open scoped Manifold

namespace ContinuousMonoidHom

/-- **Characters through a power map of the circle.** A continuous character `χ` of the circle
factors through the power map `z ↦ zⁿ` exactly when it is `z ↦ z^(n k)` for some integer `k`:
the characters of the target circle pull back to the characters whose exponent is divisible by
`n`. -/
theorem exists_eq_comp_id_pow_iff (χ : Circle →ₜ* Circle) (n : ℕ) :
    (∃ ψ : Circle →ₜ* Circle, χ = ψ.comp (ContinuousMonoidHom.id Circle ^ n)) ↔
      ∃ k : ℤ, ∀ z : Circle, χ z = z ^ ((n : ℤ) * k) := by
  constructor
  · rintro ⟨ψ, rfl⟩
    obtain ⟨k, hk, -⟩ := existsUnique_circle_eq_zpow ψ
    exact ⟨k, fun z ↦ by simp [hk, zpow_mul]⟩
  · rintro ⟨k, hk⟩
    let ψ : Circle →ₜ* Circle := ⟨zpowGroupHom k, continuous_zpow k⟩
    have hψ (w : Circle) : ψ w = w ^ k := (rfl)
    refine ⟨ψ, ext fun z ↦ ?_⟩
    rw [hk, coe_comp, Function.comp_apply, pow_apply, coe_id, id_eq, hψ, zpow_mul, zpow_natCast]

end ContinuousMonoidHom

namespace TauCeti

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

/-- The kernel of the power map `z ↦ zⁿ` of the circle is the group of `n`-th roots of unity,
which has `n` elements. For `n = 0` the kernel is the whole infinite circle, of cardinality `0`
in the convention of `Nat.card`. -/
theorem card_ker_id_circle_pow (n : ℕ) :
    Nat.card (ContinuousMonoidHom.id Circle ^ n).ker = n := by
  rcases eq_or_ne n 0 with rfl | hn
  · have : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩
    have : Infinite Circle := .of_injective _ (AddCircle.injective_toCircle Real.two_pi_pos.ne')
    have : Infinite (ContinuousMonoidHom.id Circle ^ 0).ker :=
      .of_injective (fun z ↦ ⟨z, by simp [MonoidHom.mem_ker]⟩) fun _ _ h ↦ congrArg Subtype.val h
    exact Nat.card_eq_zero_of_infinite
  have : NeZero n := ⟨hn⟩
  have hmem (z : Circle) : z ∈ (ContinuousMonoidHom.id Circle ^ n).ker ↔ z ^ n = 1 := by
    simp [MonoidHom.mem_ker]
  have hroot (ζ : ℂˣ) : ζ ∈ rootsOfUnity n ℂ ↔ (ζ : ℂ) ^ n = 1 := by
    simp [mem_rootsOfUnity, Units.ext_iff]
  refine (Nat.card_congr
    { toFun := fun z ↦ ⟨Units.mk0 ((z : Circle) : ℂ) (Circle.coe_ne_zero _), (hroot _).2 <| by
        rw [Units.val_mk0, ← Circle.coe_pow, (hmem _).1 z.property, Circle.coe_one]⟩
      invFun := fun ζ ↦ ⟨⟨((ζ : ℂˣ) : ℂ), by
          simpa [Submonoid.unitSphere] using Complex.norm_eq_one_of_mem_rootsOfUnity ζ.property⟩,
        (hmem _).2 <| Circle.ext <| (Circle.coe_pow _ n).trans ((hroot _).1 ζ.property)⟩
      left_inv := fun z ↦ Subtype.ext (Circle.ext rfl)
      right_inv := fun ζ ↦ Subtype.ext (Units.ext rfl) }).trans (Complex.card_rootsOfUnity n)

/-- **The period lattices of a power map of the circle.** For `n > 0`, the Lie map of the power
map `z ↦ zⁿ` carries the period lattice `Λ_ℤ = (2π)⁻¹ ker(exp)` of the circle onto a sublattice of
index `n` in the period lattice of the circle. -/
theorem relIndex_map_lieMap_id_circle_pow_periodLattice (n : ℕ) [NeZero n] :
    ((periodLattice (𝓡 1) Circle).map
        ((ContinuousMonoidHom.id Circle ^ n).lieMap (I := 𝓡 1)
          (I' := 𝓡 1)).toLinearMap.toAddMonoidHom).relIndex
      (periodLattice (𝓡 1) Circle) = n := by
  have : Finite (ContinuousMonoidHom.id Circle ^ n).ker := Nat.finite_of_card_ne_zero (by
    rw [card_ker_id_circle_pow]; exact NeZero.ne n)
  have : FiniteDimensional ℝ (LeftInvariantDerivation (𝓡 1) Circle) :=
    finiteDimensional_leftInvariantDerivation BoundarylessManifold.isInteriorPoint
  -- The Lie map is injective because the kernel is finite, hence bijective in finite dimension.
  have hinj : Function.Injective
      ((ContinuousMonoidHom.id Circle ^ n).lieMap (I := 𝓡 1) (I' := 𝓡 1)).toLinearMap :=
    (ContinuousMonoidHom.id Circle ^ n).lieMap_injective_of_discreteTopology_ker
  rw [(ContinuousMonoidHom.id Circle ^ n).relIndex_map_lieMap_periodLattice
    ⟨hinj, LinearMap.injective_iff_surjective.1 hinj⟩, card_ker_id_circle_pow]

end TauCeti
