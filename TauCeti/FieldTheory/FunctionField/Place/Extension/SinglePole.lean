/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Place.Extension.Fundamental
public import TauCeti.FieldTheory.FunctionField.Place.Extension.Tower

/-!
# A function with a single pole at an unramified place is a generator

Let `F / K` be a finite extension of algebraic function fields over `k`, and let `P` be a place
of `F` with ramification index `e(P ∣ K) = 1` and relative degree `f(P ∣ K) = 1` over the place
of `K` below it. If `z ∈ F` has a pole at `P` and no other pole, then `F = K(z)`.

Indeed, put `E = K(z)` and let `Q` be the place of `E` below `P`. Ramification indices and
relative degrees are multiplicative in the tower `K ⊆ E ⊆ F`, so `e(P ∣ Q) = f(P ∣ Q) = 1`. Every
place `P'` of `F` over `Q` has `ord_{P'} z = e(P' ∣ Q) · ord_Q z`, and `ord_Q z = ord_P z < 0`, so
`z` has a pole at `P'` and `P' = P`. The fundamental identity over `Q` then reads
`[F : E] = e(P ∣ Q) · f(P ∣ Q) = 1`.

Geometrically, `F / K` is a map of curves `X → Y` and `z` is a function on `X` with a single pole,
at a point where the map is unramified and induces no residue field extension: then `X` is
birational to its image under the pair of the map and `z`. Over an algebraically closed field of
constants every place has degree one, so the relative degree hypothesis is automatic. This is how
a function field over `ℂ(t)` is presented by a single generator whose minimal polynomial can be
descended, in Köck's proof that Belyi pairs over `ℂ` are defined over number fields.

## Main results

* `TauCeti.Place.adjoin_simple_eq_top_of_forall_ne_ord_nonneg`: a function whose only pole is at
  a place with `e = f = 1` over `K` generates `F` over `K`.

## References

* B. Köck, *Belyi's theorem revisited*, Beiträge zur Algebra und Geometrie 45 (2004), 253–265,
  proof of (2.2) Theorem.
* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Proposition 3.1.6 and Theorem 3.1.11.
-/

public section

open scoped IntermediateField

namespace TauCeti

namespace Place

variable {k K F : Type*} [Field k] [Field K] [Field F] [Algebra k K] [Algebra k F] [Algebra K F]
  [IsScalarTower k K F] [FiniteDimensional K F]

/-- **A function with a single pole at an unramified place generates the extension.** Let `F / K`
be a finite extension of algebraic function fields over `k`, and let `P` be a place of `F` with
ramification index and relative degree `1` over `K`. If `z` has a pole at `P` and is regular at
every other place of `F`, then `F = K(z)`. -/
theorem adjoin_simple_eq_top_of_forall_ne_ord_nonneg (hK : IsFunctionField k K)
    {P : Place k F} (he : ramificationIdx K P = 1) (hf : relativeDegree k K P = 1) {z : F}
    (hz : P.ord z < 0) (hreg : ∀ P' : Place k F, P' ≠ P → 0 ≤ P'.ord z) : K⟮z⟯ = ⊤ := by
  classical
  set E := K⟮z⟯
  -- Mathlib registers the tower `K → E → F` (`IntermediateField.isScalarTower_mid'`) but not the
  -- one over the constants `k`; both maps `k → F` are `algebraMap k F` by definition.
  have : IsScalarTower k E F := .of_algebraMap_eq fun _ ↦ rfl
  set w : E := IntermediateField.AdjoinSimple.gen K z
  have hw : algebraMap E F w = z := IntermediateField.AdjoinSimple.algebraMap_gen K z
  -- In the tower `K ⊆ E ⊆ F`, the place `P` has `e = f = 1` over `E`.
  have heE : ramificationIdx E P = 1 := by
    have h := ramificationIdx_restrict_mul (k₁ := k) (F₀ := K) (F₁ := E) P
    rw [he] at h
    exact Nat.eq_one_of_mul_eq_one_right h.symm
  have hfE : relativeDegree k E P = 1 := by
    have h := relativeDegree_restrict_mul (k₀ := k) (k₁ := k) (F₀ := K) (F₁ := E) P
    rw [hf] at h
    exact Nat.eq_one_of_mul_eq_one_right h.symm
  -- Every place of `F` over the place of `E` below `P` is a pole of `z`, hence is `P`.
  have hfibre (P' : Place k F) : P'.restrict k E = P.restrict k E ↔ P' = P := by
    refine ⟨fun hP' ↦ ?_, fun h ↦ h ▸ rfl⟩
    have hQ : (P.restrict k E).ord w < 0 := by
      have h := ord_algebraMap_restrict k E P w
      rw [hw, heE, Nat.cast_one, one_mul] at h
      exact h ▸ hz
    by_contra hne
    have h := hreg P' hne
    rw [← hw, ord_algebraMap_restrict k E P', hP'] at h
    exact (mul_neg_of_pos_of_neg (by exact_mod_cast ramificationIdx_pos E P') hQ).not_ge h
  -- The fundamental identity at that place gives `[F : E] = e · f = 1`.
  have hfin := sum_ramificationIdx_mul_relativeDegree_eq_finrank_of_isFunctionField k E
    (hK.finite_extension (E := E)) (P.restrict k E) (s := {P}) fun P' ↦ by
      rw [Finset.mem_singleton, hfibre]
  rw [Finset.sum_singleton, heE, hfE] at hfin
  exact IntermediateField.finrank_eq_one_iff_eq_top.mp hfin.symm

end Place

end TauCeti
