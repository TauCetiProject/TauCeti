/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Idempotent
public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-!
# Cuspidal types

Let `R` be a commutative ring, `K` an `R`-algebra, `J` a subgroup of `GL n R` and `χ` a character
of `J`. For an idempotent `ε` of `M_n(K)`, the matrices `1 + ε * Y * (1 - ε)` form the unipotent
radical of the parabolic subgroup of `GL n K` stabilising the column space `W` of `ε`: they are the
invertible matrices acting trivially on `W` and on `Kⁿ / W`. The pair `(J, χ)` is a *cuspidal type*
relative to `K` if `χ` is nontrivial on the part of each of these unipotent radicals that lies in
`J`, for every idempotent `ε ≠ 0, 1`.

In the typical case `R` is the ring of integers of a nonarchimedean local field `K` and `J` is a
compact open subgroup; cuspidal types are used there to make the contributions of proper
parabolic subgroups to a trace formula vanish.

## Main definitions

* `TauCeti.IsCuspidalType K χ`: the character `χ` of a subgroup `J ≤ GL n R` is a cuspidal type
  relative to the `R`-algebra `K`.

## Main results

* `TauCeti.isCuspidalType_iff_mul_eq`: the unipotent radical of `ε` described by the equations
  `ε * X = X` and `X * ε = 0` on `X = j - 1`.
* `TauCeti.IsCuspidalType.of_comp`, `TauCeti.isCuspidalType_comp_iff`: composing `χ` with a
  homomorphism, injective for the converse.
* `TauCeti.IsCuspidalType.of_comp_inclusion`: a cuspidal type on a subgroup gives one on every
  larger subgroup to which the character extends.

## References

* C. J. Bushnell and P. C. Kutzko, *The admissible dual of `GL(N)` via compact open subgroups*,
  Annals of Mathematics Studies 129 (1993), for types of `GL(N)` over a local field.
* L. Alpöge and L. Sernau, Lean formalization of the generalized Riemann hypothesis for Dirichlet
  `L`-functions (`Lib/Shimura/HeckeTower/HeckeData.lean`, `New.Variety.IsCuspidalType`),
  <https://github.com/lsernau/grh-lean> (Apache 2.0), for the notion of cuspidal type used here.
-/

public section

open Matrix

namespace TauCeti

variable {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R] (K : Type*) [Ring K]
  [Algebra R K] {M N : Type*} [MulOneClass M] [MulOneClass N] {J : Subgroup (GL n R)}

/-- A character `χ` of a subgroup `J ≤ GL n R` is a **cuspidal type** relative to an `R`-algebra
`K` if for every idempotent `ε ≠ 0, 1` of `M_n(K)` some `j ∈ J` of the form `1 + ε * Y * (1 - ε)`,
read over `K`, has `χ j ≠ 1`. That is, `χ` is nontrivial on the intersection of `J` with the
unipotent radical of the parabolic subgroup of `GL n K` stabilising the column space of `ε`. -/
def IsCuspidalType (χ : J →* M) : Prop :=
  ∀ ε : Matrix n n K, IsIdempotentElem ε → ε ≠ 0 → ε ≠ 1 →
    ∃ j : J, (∃ Y : Matrix n n K,
      ((j : GL n R) : Matrix n n R).map (algebraMap R K) = 1 + ε * Y * (1 - ε)) ∧ χ j ≠ 1

variable {K}

/-- The defining property of a cuspidal type. -/
theorem isCuspidalType_iff {χ : J →* M} :
    IsCuspidalType K χ ↔ ∀ ε : Matrix n n K, IsIdempotentElem ε → ε ≠ 0 → ε ≠ 1 →
      ∃ j : J, (∃ Y : Matrix n n K,
        ((j : GL n R) : Matrix n n R).map (algebraMap R K) = 1 + ε * Y * (1 - ε)) ∧ χ j ≠ 1 :=
  Iff.rfl

/-- A cuspidal type in terms of `X = j - 1`: for an idempotent `ε`, the matrices
`ε * Y * (1 - ε)` are those `X` with `ε * X = X` and `X * ε = 0`, the endomorphisms with values in
the column space of `ε` that vanish on it. -/
theorem isCuspidalType_iff_mul_eq {χ : J →* M} :
    IsCuspidalType K χ ↔ ∀ ε : Matrix n n K, IsIdempotentElem ε → ε ≠ 0 → ε ≠ 1 →
      ∃ j : J, ε * (((j : GL n R) : Matrix n n R).map (algebraMap R K) - 1) =
          ((j : GL n R) : Matrix n n R).map (algebraMap R K) - 1 ∧
        (((j : GL n R) : Matrix n n R).map (algebraMap R K) - 1) * ε = 0 ∧ χ j ≠ 1 := by
  refine forall₄_congr fun ε hε _ _ ↦ exists_congr fun j ↦ ?_
  set A := ((j : GL n R) : Matrix n n R).map (algebraMap R K)
  rw [← and_assoc]
  refine and_congr_left' ⟨?_, fun ⟨h₁, h₂⟩ ↦ ⟨A - 1, ?_⟩⟩
  · rintro ⟨Y, hY⟩
    rw [hY, add_sub_cancel_left]
    exact ⟨by rw [← mul_assoc, ← mul_assoc, hε.eq],
      by rw [mul_assoc, one_sub_mul, hε.eq, sub_self, mul_zero]⟩
  · rw [mul_sub, mul_one, h₁, h₂, sub_zero, add_sub_cancel]

/-- If the composite of `χ` with a homomorphism `f` is a cuspidal type, so is `χ`. -/
theorem IsCuspidalType.of_comp {χ : J →* M} {f : M →* N} (h : IsCuspidalType K (f.comp χ)) :
    IsCuspidalType K χ := fun ε hε h₀ h₁ ↦
  let ⟨j, hj, hχ⟩ := h ε hε h₀ h₁
  ⟨j, hj, fun h' ↦ hχ (by rw [MonoidHom.comp_apply, h', map_one])⟩

/-- Composing a character with an injective homomorphism does not change whether it is a cuspidal
type. -/
@[simp]
theorem isCuspidalType_comp_iff {χ : J →* M} {f : M →* N} (hf : Function.Injective f) :
    IsCuspidalType K (f.comp χ) ↔ IsCuspidalType K χ :=
  ⟨IsCuspidalType.of_comp, fun h ε hε h₀ h₁ ↦
    let ⟨j, hj, hχ⟩ := h ε hε h₀ h₁
    ⟨j, hj, fun h' ↦ hχ (hf (by rw [← MonoidHom.comp_apply, h', map_one]))⟩⟩

/-- **Cuspidal types extend to larger subgroups.** If `J ≤ J'` and the restriction to `J` of a
character `χ` of `J'` is a cuspidal type, then so is `χ`. -/
theorem IsCuspidalType.of_comp_inclusion {J' : Subgroup (GL n R)} (hJ : J ≤ J') {χ : J' →* M}
    (h : IsCuspidalType K (χ.comp (Subgroup.inclusion hJ))) : IsCuspidalType K χ :=
  fun ε hε h₀ h₁ ↦
    let ⟨j, hj, hχ⟩ := h ε hε h₀ h₁
    ⟨Subgroup.inclusion hJ j, hj, hχ⟩

end TauCeti
