/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Closure
public import Mathlib.RingTheory.Nullstellensatz
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.LinearAlgebra.Pi
import Mathlib.RingTheory.Finiteness.Cardinality

/-!
# Zariski closure of sets of points

Let `K` be a field and `k` a field with `K` a `k`-algebra. The Zariski closure of a set
`S ⊆ K^σ` with respect to equations over `k` is `Z(I(S))`, the common zero locus in `K^σ` of the
ideal of polynomials in `k[X_σ]` vanishing on `S`. This file packages it as a
`ClosureOperator` on `Set (σ → K)`, built from Mathlib's Galois connection
`MvPolynomial.zeroLocus_vanishingIdeal_galoisConnection`. Its closed sets are exactly the zero
loci of ideals of `k[X_σ]`, so the general closure-operator API (`ClosureOperator.le_closure`,
`ClosureOperator.monotone`, `ClosureOperator.idempotent`, `ClosureOperator.closure_min`, ...)
supplies extensivity, monotonicity, idempotence and minimality among zero loci.

No algebraic closedness of `K` is assumed, so no Nullstellensatz is used: over `ℝ`, for instance,
the closure is still the smallest real zero locus of real equations containing `S`.

A box `∏ᵢ sᵢ` whose sides are infinite subsets of `K` is Zariski dense, since only the zero
polynomial vanishes on it; for instance the closed half-line `[0, ∞)` is Zariski dense in `ℝ`.
Polynomial maps send the closure of a set into the closure of its image, and over finitely many
coordinates an invertible `K`-linear change of coordinates commutes with the closure and
preserves closedness. Extension by zero along an injective map of coordinate types, such as the
zero-padding of coefficient vectors when a degree bound is raised, also commutes with the closure
and preserves and reflects closedness, for any number of coordinates; the padding coordinates
vanish on the closure.

Over an infinite field, a point that is the limit at `t = 0` of a family `x + t • v` lying in `S`
for `t ≠ 0` is in the Zariski closure of `S`: a polynomial vanishing on `S` restricts to a
one-variable polynomial with infinitely many roots, so it also vanishes at `t = 0`. This is the
algebraic form of a degeneration argument. The analogue for the usual closure needs a topological
field in which `0` is not isolated: then `x` is the limit of the points `x + t • v` as `t → 0` with
`t ≠ 0`, by continuity of `t ↦ x + t • v`. Over a discrete field, for instance, it fails.

## Main definitions and results

* `MvPolynomial.zariskiClosure`: the closure operator `S ↦ Z(I(S))`.
* `MvPolynomial.zariskiClosure_isClosed_iff`: the closed sets are the zero loci of ideals.
* `MvPolynomial.vanishingIdeal_zariskiClosure`: `I(Z(I(S))) = I(S)`.
* `MvPolynomial.zariskiClosure_pi_eq_univ`: a box with infinite sides is Zariski dense.
* `MvPolynomial.image_zariskiClosure_subset_zariskiClosure_image`: polynomial maps are
  continuous for the Zariski closure.
* `MvPolynomial.zariskiClosure_image_linearEquiv`: invariance under linear coordinate changes.
* `MvPolynomial.zariskiClosure_image_extendByZero`: invariance under extension by zero along an
  injective map of coordinate types.
* `MvPolynomial.mem_zeroLocus_vanishingIdeal_of_forall_add_smul_mem`: the Zariski closure of a set
  containing a punctured line contains the missing point.
-/

public section

namespace MvPolynomial

variable {k K σ τ : Type*} [Field k] [Field K] [Algebra k K]

variable (k) in
/-- The Zariski closure of a set `S ⊆ K^σ` with respect to equations over `k`: the common zero
locus of all polynomials in `k[X_σ]` vanishing on `S`. Its closed sets are the zero loci of
ideals of `k[X_σ]`. -/
def zariskiClosure : ClosureOperator (Set (σ → K)) :=
  .ofPred (fun S => zeroLocus K (vanishingIdeal k S))
    (fun S => ∃ I : Ideal (MvPolynomial σ k), zeroLocus K I = S)
    zeroLocus_vanishingIdeal_le (fun S => ⟨_, rfl⟩) <| by
      rintro S _ hS ⟨I, rfl⟩
      exact zeroLocus_anti_mono (le_zeroLocus_iff_le_vanishingIdeal.1 hS)

/-- The Zariski closure is the zero locus of the vanishing ideal. -/
theorem zariskiClosure_apply (S : Set (σ → K)) :
    zariskiClosure k S = zeroLocus K (vanishingIdeal k S) := (rfl)

/-- A point lies in the Zariski closure of `S` exactly when every polynomial over `k` vanishing
on `S` also vanishes at that point. -/
@[simp] theorem mem_zariskiClosure_iff {S : Set (σ → K)} {x : σ → K} :
    x ∈ zariskiClosure k S ↔ ∀ p : MvPolynomial σ k, (∀ y ∈ S, aeval y p = 0) → aeval x p = 0 :=
  Iff.rfl

/-- The sets closed for the Zariski closure are exactly the zero loci of ideals of `k[X_σ]`. -/
theorem zariskiClosure_isClosed_iff {S : Set (σ → K)} :
    (zariskiClosure k).IsClosed S ↔ ∃ I : Ideal (MvPolynomial σ k), zeroLocus K I = S :=
  Iff.rfl

/-- The zero locus of an ideal is closed for the Zariski closure. -/
theorem zariskiClosure_isClosed_zeroLocus (I : Ideal (MvPolynomial σ k)) :
    (zariskiClosure k).IsClosed (zeroLocus K I) :=
  ⟨I, rfl⟩

/-- The Zariski closure of a zero locus is that zero locus. -/
@[simp] theorem zariskiClosure_zeroLocus (I : Ideal (MvPolynomial σ k)) :
    zariskiClosure k (zeroLocus K I) = zeroLocus K I :=
  (zariskiClosure_isClosed_zeroLocus I).closure_eq

/-- The Zariski closure of `S` is the smallest zero locus containing `S`: it lies in a zero
locus exactly when `S` does. -/
theorem zariskiClosure_le_zeroLocus_iff {S : Set (σ → K)} {I : Ideal (MvPolynomial σ k)} :
    zariskiClosure k S ≤ zeroLocus K I ↔ S ≤ zeroLocus K I :=
  (zariskiClosure_isClosed_zeroLocus I).closure_le_iff

/-- A set and its Zariski closure have the same vanishing ideal. -/
@[simp] theorem vanishingIdeal_zariskiClosure (S : Set (σ → K)) :
    vanishingIdeal k (zariskiClosure k S) = vanishingIdeal k S :=
  zeroLocus_vanishingIdeal_galoisConnection.u_l_u_eq_u (OrderDual.toDual S)

/-- The empty set is Zariski closed. -/
@[simp] theorem zariskiClosure_empty : zariskiClosure k (∅ : Set (σ → K)) = ∅ := by
  rw [zariskiClosure_apply, vanishingIdeal_empty, zeroLocus_top, Set.bot_eq_empty]

/-- The whole affine space is Zariski closed. -/
@[simp] theorem zariskiClosure_univ : zariskiClosure k (Set.univ : Set (σ → K)) = Set.univ :=
  (zariskiClosure k).closure_top

/-- Only the zero polynomial over `k` vanishes on a box `∏ᵢ sᵢ ⊆ K^σ` whose sides are infinite. -/
theorem vanishingIdeal_pi_eq_bot {s : σ → Set K} (hs : ∀ i, (s i).Infinite) :
    vanishingIdeal k (Set.univ.pi s) = ⊥ := by
  refine eq_bot_iff.2 fun p hp => (Ideal.mem_bot).2 ?_
  apply map_injective _ (algebraMap k K).injective
  rw [map_zero]
  refine funext_set s hs fun x hx => ?_
  rw [eval_map, ← aeval_def, hp x hx, map_zero]

/-- A box `∏ᵢ sᵢ ⊆ K^σ` whose sides are infinite is Zariski dense. -/
theorem zariskiClosure_pi_eq_univ {s : σ → Set K} (hs : ∀ i, (s i).Infinite) :
    zariskiClosure k (Set.univ.pi s) = Set.univ := by
  rw [zariskiClosure_apply, vanishingIdeal_pi_eq_bot hs, zeroLocus_bot, Set.top_eq_univ]

/-- A polynomial map `x ↦ (aeval x (P t))ₜ` sends the Zariski closure of a set into the Zariski
closure of its image. -/
theorem image_zariskiClosure_subset_zariskiClosure_image (P : τ → MvPolynomial σ k)
    (S : Set (σ → K)) :
    (fun x t => aeval x (P t)) '' zariskiClosure k S ⊆
      zariskiClosure k ((fun x t => aeval x (P t)) '' S) := by
  rintro _ ⟨x, hx, rfl⟩
  rw [mem_zariskiClosure_iff]
  intro q hq
  rw [← aeval_bind₁]
  refine mem_zariskiClosure_iff.1 hx _ fun y hy => ?_
  rw [aeval_bind₁]
  exact hq _ ⟨y, hy, rfl⟩

/-- Over finitely many source coordinates, a `K`-linear map sends the Zariski closure of a set
into the Zariski closure of its image. -/
theorem image_zariskiClosure_subset_zariskiClosure_image_linearMap [Finite σ]
    (f : (σ → K) →ₗ[K] (τ → K)) (S : Set (σ → K)) :
    f '' zariskiClosure K S ⊆ zariskiClosure K (f '' S) := by
  classical
  have := Fintype.ofFinite σ
  have hf : ⇑f = fun x t => aeval x
      (∑ s, C (f (fun j => if s = j then 1 else 0) t) * X s : MvPolynomial σ K) := by
    funext x t
    rw [f.pi_apply_eq_sum_univ x]
    simp [mul_comm]
  rw [hf]
  exact image_zariskiClosure_subset_zariskiClosure_image _ S

/-- An invertible `K`-linear change of finitely many coordinates commutes with the Zariski
closure. -/
theorem zariskiClosure_image_linearEquiv [Finite σ] (e : (σ → K) ≃ₗ[K] (τ → K))
    (S : Set (σ → K)) : zariskiClosure K (e '' S) = e '' zariskiClosure K S := by
  -- The target coordinates are finite too, so `e.symm` is also a polynomial map.
  have : Module.Finite K (τ → K) := .equiv e
  have : Module.Finite K (τ →₀ K) := .of_injective Finsupp.lcoeFun DFunLike.coe_injective
  have : Finite τ := Module.Finite.finite_basis (Finsupp.basisSingleOne (R := K) (ι := τ))
  refine subset_antisymm (fun x hx => ⟨e.symm x, ?_, e.apply_symm_apply x⟩)
    (image_zariskiClosure_subset_zariskiClosure_image_linearMap e.toLinearMap S)
  have h := image_zariskiClosure_subset_zariskiClosure_image_linearMap e.symm.toLinearMap
    (e '' S) ⟨x, hx, rfl⟩
  simpa [Set.image_image] using h

/-- An invertible `K`-linear change of finitely many coordinates preserves and reflects
Zariski closedness. -/
theorem zariskiClosure_isClosed_image_linearEquiv_iff [Finite σ]
    (e : (σ → K) ≃ₗ[K] (τ → K)) {S : Set (σ → K)} :
    (zariskiClosure K).IsClosed (e '' S) ↔ (zariskiClosure K).IsClosed S := by
  rw [ClosureOperator.isClosed_iff_closure_le, ClosureOperator.isClosed_iff_closure_le,
    zariskiClosure_image_linearEquiv, Set.image_subset_image_iff e.injective]

section ExtendByZero

variable (s : σ → τ)

/-- Every point in the Zariski closure of a set extended by zero along `s : σ → τ` vanishes at
the coordinates outside the range of `s`. -/
theorem apply_eq_zero_of_mem_zariskiClosure_image_extendByZero {S : Set (σ → K)} {x : τ → K}
    (hx : x ∈ zariskiClosure k (Function.ExtendByZero.linearMap K K s '' S)) {t : τ}
    (ht : t ∉ Set.range s) : x t = 0 := by
  have h := mem_zariskiClosure_iff.1 hx (X t) <| by
    rintro _ ⟨y, -, rfl⟩
    simpa using Function.extend_apply' y (0 : τ → K) t ht
  simpa using h

/-- For injective `s : σ → τ`, extension by zero along `s` commutes with the Zariski closure. No
finiteness of the coordinates is needed. -/
theorem zariskiClosure_image_extendByZero {s : σ → τ} (hs : Function.Injective s)
    (S : Set (σ → K)) :
    zariskiClosure k (Function.ExtendByZero.linearMap K K s '' S) =
      Function.ExtendByZero.linearMap K K s '' zariskiClosure k S := by
  apply subset_antisymm
  · intro x hx
    refine ⟨x ∘ s, ?_, ?_⟩
    · -- Restricting to the coordinates in the range of `s` is a polynomial map inverting the
      -- extension by zero.
      have h := image_zariskiClosure_subset_zariskiClosure_image (k := k) (X ∘ s)
        (Function.ExtendByZero.linearMap K K s '' S) ⟨x, hx, rfl⟩
      simpa [Set.image_image, Function.comp_def, hs.extend_apply] using h
    · ext t
      by_cases ht : t ∈ Set.range s
      · obtain ⟨i, rfl⟩ := ht
        simp [hs.extend_apply]
      · simp [Function.extend_apply' _ _ t (by simpa using ht),
          apply_eq_zero_of_mem_zariskiClosure_image_extendByZero s hx ht]
  · -- Extension by zero is the polynomial map with coordinates `X i` and `0`.
    have h := image_zariskiClosure_subset_zariskiClosure_image (k := k)
      (Function.extend s X 0) S
    have he : (fun (x : σ → K) t => aeval x (Function.extend s (X (R := k)) 0 t)) =
        Function.ExtendByZero.linearMap K K s := by
      funext x t
      rw [Function.apply_extend (aeval x), Function.ExtendByZero.linearMap_apply]
      congr 1
      funext i
      simp
    rwa [he] at h

/-- For injective `s : σ → τ`, extension by zero along `s` preserves and reflects Zariski
closedness. -/
theorem zariskiClosure_isClosed_image_extendByZero_iff {s : σ → τ} (hs : Function.Injective s)
    {S : Set (σ → K)} :
    (zariskiClosure k).IsClosed (Function.ExtendByZero.linearMap K K s '' S) ↔
      (zariskiClosure k).IsClosed S := by
  rw [ClosureOperator.isClosed_iff_closure_le, ClosureOperator.isClosed_iff_closure_le,
    zariskiClosure_image_extendByZero hs, Set.image_subset_image_iff]
  exact Function.extend_injective hs (0 : τ → K)

end ExtendByZero

section PuncturedLine

open Polynomial

variable [Infinite K]

/-- Over an infinite field, a point `x` lies in the Zariski closure of any set `S` containing the
points `x + t • v` for all `t ≠ 0`. -/
theorem mem_zeroLocus_vanishingIdeal_of_forall_add_smul_mem {S : Set (σ → K)} {x v : σ → K}
    (h : ∀ t : K, t ≠ 0 → x + t • v ∈ S) : x ∈ zeroLocus K (vanishingIdeal k S) := by
  refine mem_zeroLocus_iff.2 fun p hp => ?_
  -- The restriction of `p` to the line through `x` in direction `v`, as a polynomial in `t`.
  set Q : K[X] := aeval (fun s => Polynomial.C (x s) + Polynomial.C (v s) * Polynomial.X) p
  have hQ (t : K) : Q.eval t = aeval (x + t • v) p := by
    have := congrArg (· p) (comp_aeval (R := k)
      (fun s => Polynomial.C (x s) + Polynomial.C (v s) * Polynomial.X)
      ((Polynomial.aeval t).restrictScalars k))
    simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply] at this
    rw [Polynomial.coe_aeval_eq_eval] at this
    rw [this]
    congr 2
    funext s
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_comm]
  have hQ0 : Q = 0 := by
    refine Polynomial.eq_zero_of_infinite_isRoot Q
      ((Set.finite_singleton (0 : K)).infinite_compl.mono fun t ht => ?_)
    rw [Set.mem_ofPred_eq, IsRoot, hQ]
    exact mem_vanishingIdeal_iff.1 hp _ (h t ht)
  simpa [hQ0] using (hQ 0).symm

end PuncturedLine

end MvPolynomial
