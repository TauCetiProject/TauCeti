/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.RepresentationTheory.Basic
public import TauCeti.GroupTheory.FixedSubgroup

/-!
# Finite fixed subgroups through matrix coordinates

Let a group `G` embed in the square matrices `Matrix n n K` over an integral domain `K`, with `n`
finite, and let `F` be an endomorphism of `G`. Suppose some iterate `F^[r]` acts on every matrix
coordinate by the power map `x ↦ x ^ m` for an exponent `m > 1`. A point fixed by `F` is fixed by
`F^[r]`, so each of its coordinates is a root of the nonzero polynomial `X ^ m - X`. There are
finitely many such roots, and the embedding is injective, so the fixed subgroup of `F` is finite.

This is the finiteness mechanism for the fixed points of a Steinberg endomorphism of a linear
algebraic group over the algebraic closure of `𝔽_p`. There `m` is a power of `p` and the iterate
`F^[r]` is a power of the entrywise Frobenius, so the fixed coordinates lie in a finite field. The
criterion needs neither the characteristic nor the finite field: it bounds the coordinates by the
roots of `X ^ m - X` directly. Nor does it need `r > 0`: at `r = 0` its hypothesis already bounds
the coordinates of every element of `G`.

The criterion is stated for an injective coordinate map `G → Matrix n n K`. It is packaged for an
iterate that agrees with an iterate of a separate entrywise power map, as when a Steinberg
endomorphism has a power that is a power of a Frobenius map, for subgroups of `GL n K`, and for a
faithful representation on a module with a finite basis. A finite fixed subgroup transports along
an isomorphism intertwining two endomorphisms by `TauCeti.fixedSubgroupCongr`, and passes to the
derived central quotient by `TauCeti.finiteFixedPointCandidate`.

## Main results

* `TauCeti.finite_fixedSubgroup_of_iterate_apply_eq_pow`: the criterion.
* `TauCeti.finite_fixedSubgroup_of_iterate_eq_iterate`: the criterion when an iterate of `F` is a
  nonzero iterate of an entrywise power map.
* `Subgroup.finite_fixedSubgroup_of_iterate_eq_iterate`: the same for a subgroup of `GL n K` and its
  matrix entries.
* `Representation.finite_fixedSubgroup_of_iterate_apply_eq_pow`: the criterion for a faithful
  representation, read in the coordinates of a finite basis.

## References

* R. Steinberg, *Endomorphisms of linear algebraic groups*, Memoirs AMS **80** (1968), §10.
* R. W. Carter, *Finite Groups of Lie Type: Conjugacy Classes and Complex Characters*, §1.17.
-/

public section

open Polynomial

namespace TauCeti

variable {G : Type*} [Group G] {n : Type*} [Finite n] {K : Type*} [CommRing K] [IsDomain K]

/-- **The finite-coordinate fixed-point criterion.** Let `ρ` embed a group `G` in the square
matrices over an integral domain, and let `F` be an endomorphism of `G`. If an iterate `F^[r]`
raises every matrix coordinate to the power `m > 1`, then the fixed subgroup of `F` is finite: the
coordinates of a fixed point are roots of `X ^ m - X`. -/
theorem finite_fixedSubgroup_of_iterate_apply_eq_pow (ρ : G → Matrix n n K)
    (hρ : Function.Injective ρ) (F : G →* G) (r : ℕ) {m : ℕ} (hm : 1 < m)
    (hF : ∀ g i j, ρ ((⇑F)^[r] g) i j = ρ g i j ^ m) : Finite (fixedSubgroup F) := by
  let roots : Set K := {x | IsRoot (X ^ m - X) x}
  have hroots : roots.Finite := finite_setOfPred_isRoot (X_pow_sub_X_ne_zero hm)
  have : Finite roots := hroots.to_subtype
  -- The coordinates of a fixed point are fixed by the power map, so they lie in `roots`.
  have hmem (g : fixedSubgroup F) (i j : n) : ρ g i j ∈ roots := by
    have hfix := hF g i j
    rw [Function.iterate_fixed (mem_fixedSubgroup.mp g.property)] at hfix
    simp [roots, sub_eq_zero, ← hfix]
  refine Finite.of_injective (fun g i j => (⟨ρ g i j, hmem g i j⟩ : roots)) fun g g' h => ?_
  refine Subtype.ext (hρ (Matrix.ext fun i j => ?_))
  exact congrArg Subtype.val (congrFun (congrFun h i) j)

/-- **The finite-coordinate criterion through a power map.** Let `Φ` raise every matrix coordinate
of `G` to the power `m > 1`. If an iterate of an endomorphism `F` agrees with a nonzero iterate of
`Φ`, then the fixed subgroup of `F` is finite. This is the form in which a power of a Steinberg
endomorphism is a power of a Frobenius map. -/
theorem finite_fixedSubgroup_of_iterate_eq_iterate (ρ : G → Matrix n n K)
    (hρ : Function.Injective ρ) {F : G →* G} {Φ : G → G} {r k m : ℕ} (hm : 1 < m) (hk : k ≠ 0)
    (hΦ : ∀ g i j, ρ (Φ g) i j = ρ g i j ^ m) (hF : ∀ g, (⇑F)^[r] g = Φ^[k] g) :
    Finite (fixedSubgroup F) := by
  -- Each application of `Φ` raises the coordinates to one more factor `m` of the exponent.
  have hiter (j : ℕ) (g : G) (a b : n) : ρ (Φ^[j] g) a b = ρ g a b ^ m ^ j := by
    induction j with
    | zero => simp
    | succ j ih => rw [Function.iterate_succ_apply', hΦ, ih, ← pow_mul, pow_succ]
  refine finite_fixedSubgroup_of_iterate_apply_eq_pow ρ hρ F r (Nat.one_lt_pow hk hm)
    fun g i j => ?_
  rw [hF, hiter]

end TauCeti

namespace Subgroup

open TauCeti

variable {n : Type*} [Fintype n] [DecidableEq n] {K : Type*} [CommRing K] [IsDomain K]

/-- **The finite-coordinate criterion for a group of invertible matrices.** Let `Φ` raise every
entry of a subgroup `S` of `GL n K` to the power `m > 1`. If an iterate of an endomorphism `F` of
`S` agrees with a nonzero iterate of `Φ`, then the fixed subgroup of `F` is finite. -/
theorem finite_fixedSubgroup_of_iterate_eq_iterate (S : Subgroup (GL n K)) {F : S →* S}
    {Φ : S → S} {r k m : ℕ} (hm : 1 < m) (hk : k ≠ 0)
    (hΦ : ∀ g i j, ((Φ g : GL n K) : Matrix n n K) i j = ((g : GL n K) : Matrix n n K) i j ^ m)
    (hF : ∀ g, (⇑F)^[r] g = Φ^[k] g) : Finite (fixedSubgroup F) :=
  TauCeti.finite_fixedSubgroup_of_iterate_eq_iterate (fun g : S => ((g : GL n K) : Matrix n n K))
    (Units.val_injective.comp Subtype.val_injective) hm hk hΦ hF

end Subgroup

namespace Representation

open TauCeti

variable {G : Type*} [Group G] {n : Type*} [Fintype n] [DecidableEq n]
  {K : Type*} [CommRing K] [IsDomain K] {V : Type*} [AddCommGroup V] [Module K V]

/-- **The finite-coordinate criterion for a faithful representation.** Let `ρ` be a faithful
representation of `G` on a module with a finite basis `b`, and let `F` be an endomorphism of `G`.
If an iterate `F^[r]` raises every matrix coordinate in the basis `b` to the power `m > 1`, then
the fixed subgroup of `F` is finite. -/
theorem finite_fixedSubgroup_of_iterate_apply_eq_pow (ρ : Representation K G V)
    (hρ : Function.Injective ρ) (b : Module.Basis n K V) (F : G →* G) (r : ℕ) {m : ℕ}
    (hm : 1 < m)
    (hF : ∀ g i j, LinearMap.toMatrix b b (ρ ((⇑F)^[r] g)) i j =
      LinearMap.toMatrix b b (ρ g) i j ^ m) :
    Finite (fixedSubgroup F) :=
  TauCeti.finite_fixedSubgroup_of_iterate_apply_eq_pow _
    ((LinearMap.toMatrix b b).injective.comp hρ) F r hm hF

end Representation
