/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.SesquilinearForm.Basic
public import Mathlib.RepresentationTheory.Irreducible
import TauCeti.LinearAlgebra.SesquilinearForm.Separating

/-!
# Contravariant forms and Schur's lemma

Let `G` be a group with an involution `g ↦ star g`, such as `GL n ℂ` with the conjugate transpose.
A sesquilinear pairing `S` of two representations `ρ` and `σ` of `G` is **contravariant** if
`S (ρ g x) y = S x (σ (star g) y)` for all `g`, `x`, `y`. Such pairings are the analogue, for the
involution `star`, of invariant pairings, and they are governed by Schur's lemma: a separating
contravariant form `B` on `ρ`, for instance a nondegenerate one, turns a pairing `S` into an
intertwining map `T` from `σ` to `ρ` with `S x y = B x (T y)`
(`Representation.exists_intertwiningMap_forall_apply_eq_apply`). Hence:

* a contravariant pairing of two nonisomorphic irreducible representations vanishes
  (`Representation.eq_zero_of_isEmpty_equiv`);
* over an algebraically closed field a contravariant form on an irreducible representation is a
  scalar multiple of `B` (`Representation.exists_forall_apply_eq_mul_apply`), so a separating
  contravariant form is unique up to a scalar, if it exists.

## Main results

* `Representation.exists_intertwiningMap_forall_apply_eq_apply`: a contravariant pairing is
  represented through a separating contravariant form by an intertwining map.
* `Representation.eq_zero_of_isEmpty_equiv` and `Representation.exists_forall_apply_eq_mul_apply`:
  the two cases of Schur's lemma.
-/

public section

variable {𝕜 V W : Type*} [Field 𝕜] [StarRing 𝕜] [AddCommGroup V] [Module 𝕜 V] [AddCommGroup W]
  [Module 𝕜 W]

namespace Representation

variable {G : Type*} [Monoid G] [StarMul G] (ρ : Representation 𝕜 G V) (σ : Representation 𝕜 G W)

/-- **A contravariant pairing is an intertwining map.** If `B` is a separating contravariant form on
the finite-dimensional representation `ρ`, every contravariant pairing `S` of `ρ` with `σ` has the
form `S x y = B x (T y)` for an intertwining map `T` from `σ` to `ρ`. -/
theorem exists_intertwiningMap_forall_apply_eq_apply [FiniteDimensional 𝕜 V]
    {B : V →ₗ⋆[𝕜] V →ₗ[𝕜] 𝕜} (hB : B.SeparatingRight)
    (hρ : ∀ g x y, B (ρ g x) y = B x (ρ (star g) y)) {S : V →ₗ⋆[𝕜] W →ₗ[𝕜] 𝕜}
    (hS : ∀ g x y, S (ρ g x) y = S x (σ (star g) y)) :
    ∃ T : IntertwiningMap σ ρ, ∀ x y, S x y = B x (T y) := by
  obtain ⟨T, hT⟩ := LinearMap.exists_linearMap_forall_apply_eq_apply hB S
  refine ⟨.mk T fun g ↦ LinearMap.ext fun y ↦ ?_, hT⟩
  -- The vector `T (σ g y) - ρ g (T y)` pairs to zero with every vector.
  have h (z : V) : B z (T (σ g y)) = B z (ρ g (T y)) := calc
    _ = S z (σ (star (star g)) y) := by rw [star_star, hT]
    _ = S (ρ (star g) z) y := (hS _ _ _).symm
    _ = B (ρ (star g) z) (T y) := hT _ _
    _ = B z (ρ g (T y)) := by rw [hρ, star_star]
  rw [LinearMap.comp_apply, LinearMap.comp_apply]
  exact sub_eq_zero.mp (hB _ fun z ↦ by rw [map_sub, h, sub_self])

/-- **Schur's lemma for pairings of nonisomorphic representations.** A contravariant pairing of two
irreducible representations that are not isomorphic vanishes, provided the source carries a
separating contravariant form. -/
theorem eq_zero_of_isEmpty_equiv [FiniteDimensional 𝕜 V] [ρ.IsIrreducible] [σ.IsIrreducible]
    {B : V →ₗ⋆[𝕜] V →ₗ[𝕜] 𝕜} (hB : B.SeparatingRight)
    (hρ : ∀ g x y, B (ρ g x) y = B x (ρ (star g) y)) {S : V →ₗ⋆[𝕜] W →ₗ[𝕜] 𝕜}
    (hS : ∀ g x y, S (ρ g x) y = S x (σ (star g) y)) (hne : IsEmpty (σ.Equiv ρ)) : S = 0 := by
  obtain ⟨T, hT⟩ := exists_intertwiningMap_forall_apply_eq_apply ρ σ hB hρ hS
  have hT0 : T = 0 := by
    refine (IsIrreducible.bijective_or_eq_zero T).resolve_left fun hbij ↦ ?_
    exact hne.false (T.ofBijective hbij)
  ext x y
  simp [hT, hT0]

/-- **Schur's lemma for contravariant forms.** Over an algebraically closed field, a contravariant
form on a finite-dimensional irreducible representation is a scalar multiple of any separating
contravariant form. -/
theorem exists_forall_apply_eq_mul_apply [IsAlgClosed 𝕜] [FiniteDimensional 𝕜 V] [ρ.IsIrreducible]
    {B : V →ₗ⋆[𝕜] V →ₗ[𝕜] 𝕜} (hB : B.SeparatingRight)
    (hρ : ∀ g x y, B (ρ g x) y = B x (ρ (star g) y)) {S : V →ₗ⋆[𝕜] V →ₗ[𝕜] 𝕜}
    (hS : ∀ g x y, S (ρ g x) y = S x (ρ (star g) y)) : ∃ c : 𝕜, ∀ x y, S x y = c * B x y := by
  obtain ⟨T, hT⟩ := exists_intertwiningMap_forall_apply_eq_apply ρ ρ hB hρ hS
  obtain ⟨c, rfl⟩ :=
    (IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed (ρ := ρ)).surjective T
  refine ⟨c, fun x y ↦ ?_⟩
  simp [hT, Algebra.algebraMap_eq_smul_one]

end Representation
