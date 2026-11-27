/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Matrix.Order
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Topology.Semicontinuity.Defs
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Topology.Algebra.Monoid
import TauCeti.LinearAlgebra.Matrix.PosSemidef

/-!
# Sieve systems

A *sieve system* is a list of conditions on a family of forms `J i p q ∈ ℂ`, `0 ≤ i ≤ n + 1`, on
pairs of sequences `p, q : ℕ → U` (the *heads*), over a ring `C` with a measure: each form but the
top one is the integral of the next over a common entry `u c` of the two heads at position `i`, the
twisted integrals against `ψ (ξ c)` at units `ξ` are bounded by a decay `β ξ` times weights
`Λ i p · Λ i q`, the top form is continuous and positive semidefinite on heads with a common last
entry, and the bottom form is bounded by `En`. These are the hypotheses of the sieve over all places
in the shorter formal proof of the Riemann hypothesis for Dirichlet `L`-functions, where `C` is a
completion of a number field (or a product of completions) and the forms come from local integrals.

The conditions are stable under finite products, factor by factor: Fubini's theorem for the
recursion and the twisted integrals, Schur's product theorem for positivity, and products of the
local bounds. Summed over the pairs of a finite family of heads, the forms are again integrals of
the next ones, they are nonnegative, and they are lower semicontinuous in a parameter on which the
heads depend continuously.

## Main definitions and results

* `TauCeti.SieveSystem`: the conditions.
* `TauCeti.SieveSystem.prod`: the product of two sieve systems is a sieve system on `C₁ × C₂`.
* `TauCeti.SieveSystem.pi`: the product of a finite family of sieve systems is a sieve system on
  `∀ v, C v`. Together with `prod`, the products `(∏_v J^v i) · J i` of finitely many systems
  `J^v` and one more system `J` form the sieve system `(SieveSystem.pi hJ').prod hJ`.
* `TauCeti.SieveSystem.integrable_sum_update`, `TauCeti.SieveSystem.integral_sum_update`,
  `TauCeti.SieveSystem.norm_integral_mul_sum_update_le`: the forms `J (i + 1)` summed over all pairs
  from a finite family of heads with a common entry `u c` at position `i ≤ n` are integrable in `c`,
  with integral the sum of the forms `J i`, and twisted integrals at most `β ξ (∑_p Λ i p) ^ 2`.
* `TauCeti.SieveSystem.sum_nonneg`, `TauCeti.SieveSystem.lowerSemicontinuousAt_sum`: such a sum is
  nonnegative, and its real part is lower semicontinuous at every point where every head is
  continuous.

## Implementation notes

The two product results cover any finite family of systems on arbitrary rings `C v`, with arbitrary
entry maps and twists. Products of finitely many systems on `ℂ` (entry map `c ↦ c` on units and `1`
at `0`, twist `c ↦ exp (c - conj c)`) and one more system on `C` are the special case
`(SieveSystem.pi hJ').prod hJ` with constant families. The forms of a product are evaluated on the
components of the heads: `Prod.fst ∘ p` and `Prod.snd ∘ p` for `prod`, and `fun k ↦ p k v` for
`pi`.

Integrability of `c ↦ ψ (ξ c) J (i + 1)` with integral `J i` at `ξ = 0` is split into the fields
`integrable_mul_update` and `integral_update`; given `ψ 0 = 1` the two formulations are equivalent.
The ring `C` need not be commutative.

## References

* The definition and the results are adapted from the shorter formal proof of the Riemann
  hypothesis for Dirichlet `L`-functions, grh-lean (https://github.com/lsernau/grh-lean, commit
  `72fead1`, Apache 2.0, Copyright 2026 Anthropic, PBC), file
  `src/New/Spanning/MainTerm/SieveSystem.lean`: the structure `New.SieveSystem`, the product
  `New.SieveSystem.pi`, and `New.SieveSystem.integrable_update`,
  `New.SieveSystem.integrable_sum_update`, `New.SieveSystem.integral_sum_update`,
  `New.SieveSystem.norm_integral_mul_sum_update_le`, `New.SieveSystem.sum_nonneg` and
  `New.SieveSystem.lowerSemicontinuousAt_sum`. There a product of finitely many systems on `ℂ`
  and one system on `C` is treated in one step; here it is split into `prod` and `pi`.
* I. Schur, *Bemerkungen zur Theorie der beschränkten Bilinearformen mit unendlich vielen
  Veränderlichen*, J. Reine Angew. Math. 140 (1911), for the product theorem.
-/

public section

open MeasureTheory Finset Function Matrix
open scoped ComplexOrder

namespace TauCeti

variable {C U : Type*} [Ring C] [MeasureSpace C] [TopologicalSpace U]

/-- The conditions of a sieve at a place or a product of places. `C` is a ring with a measure,
`u c` is the entry given by `c ∈ C`, and `ι` maps entries back to `C`. The forms `J i p q`,
`i ≤ n + 1`, pair two sequences of entries, the heads, with weights `Λ i p`. Each form `J i` with
`i ≤ n` is the integral of `J (i + 1)` over a common entry `u c` at position `i`, and the same
integral twisted by `ψ (ξ * c)` at a unit `ξ` is bounded in terms of the decay `β ξ`. The top form
`J (n + 1)` is continuous, and positive semidefinite on heads with a common entry at position `n`.
The bottom form `J 0` has modulus at most `En`. -/
structure SieveSystem (u : C → U) (ι : U → C) (n : ℕ) (J : ℕ → (ℕ → U) → (ℕ → U) → ℂ)
    (ψ : C → ℂ) (En : ℝ) (Λ : ℕ → (ℕ → U) → ℝ) (β : C → ℝ) : Prop where
  /-- The twist `ψ` takes the value `1` at `0`. -/
  psi_zero : ψ 0 = 1
  /-- For `i ≤ n`, give both heads the entry `u c` at position `i`. Then `ψ (ξ * c)` times the
  form `J (i + 1)` is integrable in `c`. -/
  integrable_mul_update (i : ℕ) (hi : i ≤ n) (p q : ℕ → U) (ξ : C) :
    Integrable fun c : C ↦ ψ (ξ * c) * J (i + 1) (update p i (u c)) (update q i (u c))
  /-- For `i ≤ n`, the form `J i` is the integral of `J (i + 1)` over a common entry `u c` at
  position `i`. -/
  integral_update (i : ℕ) (hi : i ≤ n) (p q : ℕ → U) :
    ∫ c : C, J (i + 1) (update p i (u c)) (update q i (u c)) = J i p q
  /-- For `i ≤ n` and a unit `ξ`, the integral of `J (i + 1)` over a common entry `u c` at
  position `i`, twisted by `ψ (ξ * c)`, has modulus at most `β ξ * (Λ i p * Λ i q)`. -/
  norm_integral_mul_update_le (i : ℕ) (hi : i ≤ n) (p q : ℕ → U) {ξ : C} (hξ : IsUnit ξ) :
    ‖∫ c : C, ψ (ξ * c) * J (i + 1) (update p i (u c)) (update q i (u c))‖ ≤
      β ξ * (Λ i p * Λ i q)
  /-- The top form `J (n + 1)` is positive semidefinite on heads with the same entry at
  position `n`. -/
  posSemidef {κ : Type} [Fintype κ] (a : κ → ℕ → U) (t : U) (ha : ∀ k, a k n = t) :
    (Matrix.of fun k l : κ ↦ J (n + 1) (a k) (a l)).PosSemidef
  /-- The top form `J (n + 1)` is jointly continuous. -/
  continuous : Continuous (J (n + 1)).uncurry
  /-- The bottom form `J 0` has modulus at most `En`. -/
  norm_bot_le (p q : ℕ → U) : ‖J 0 p q‖ ≤ En
  /-- For `i < n`, if `ξ = ι (p i) - ι (q i)` is a unit, then `J (i + 1) p q` has modulus at most
  `β ξ * (Λ (i + 1) p * Λ (i + 1) q)`. -/
  norm_le_of_isUnit_sub (i : ℕ) (hi : i < n) (p q : ℕ → U) (hξ : IsUnit (ι (p i) - ι (q i))) :
    ‖J (i + 1) p q‖ ≤ β (ι (p i) - ι (q i)) * (Λ (i + 1) p * Λ (i + 1) q)

namespace SieveSystem

variable {u : C → U} {ι : U → C} {n : ℕ} {J : ℕ → (ℕ → U) → (ℕ → U) → ℂ} {ψ : C → ℂ} {En : ℝ}
  {Λ : ℕ → (ℕ → U) → ℝ} {β : C → ℝ}

/-- For `i ≤ n`, the form `J (i + 1)` is integrable in a common entry `u c` at position `i`. -/
theorem integrable_update (K : SieveSystem u ι n J ψ En Λ β) {i : ℕ} (hi : i ≤ n) (p q : ℕ → U) :
    Integrable fun c : C ↦ J (i + 1) (update p i (u c)) (update q i (u c)) := by
  simpa only [zero_mul, K.psi_zero, one_mul] using K.integrable_mul_update i hi p q 0

/-! ### Products -/

section Prod

variable {C₁ C₂ U₁ U₂ : Type*} [Ring C₁] [Ring C₂] [MeasureSpace C₁] [MeasureSpace C₂]
  [TopologicalSpace U₁] [TopologicalSpace U₂]
  {u₁ : C₁ → U₁} {ι₁ : U₁ → C₁} {J₁ : ℕ → (ℕ → U₁) → (ℕ → U₁) → ℂ} {ψ₁ : C₁ → ℂ} {E₁ : ℝ}
  {Λ₁ : ℕ → (ℕ → U₁) → ℝ} {β₁ : C₁ → ℝ}
  {u₂ : C₂ → U₂} {ι₂ : U₂ → C₂} {J₂ : ℕ → (ℕ → U₂) → (ℕ → U₂) → ℂ} {ψ₂ : C₂ → ℂ} {E₂ : ℝ}
  {Λ₂ : ℕ → (ℕ → U₂) → ℝ} {β₂ : C₂ → ℝ}

omit [MeasureSpace C₁] [MeasureSpace C₂] [TopologicalSpace U₁] [TopologicalSpace U₂] in
/-- At a common entry of the heads, the integrand of a product of two systems is the product of
the integrands of the factors. -/
private theorem prod_integrand_eq (i : ℕ) (p q : ℕ → U₁ × U₂) (ξ : C₁ × C₂) :
    (fun c : C₁ × C₂ ↦ ψ₁ (ξ * c).1 * ψ₂ (ξ * c).2 *
      (J₁ (i + 1) (Prod.fst ∘ update p i (Prod.map u₁ u₂ c))
          (Prod.fst ∘ update q i (Prod.map u₁ u₂ c)) *
        J₂ (i + 1) (Prod.snd ∘ update p i (Prod.map u₁ u₂ c))
          (Prod.snd ∘ update q i (Prod.map u₁ u₂ c)))) =
    fun c ↦ (ψ₁ (ξ.1 * c.1) *
        J₁ (i + 1) (update (Prod.fst ∘ p) i (u₁ c.1)) (update (Prod.fst ∘ q) i (u₁ c.1))) *
      (ψ₂ (ξ.2 * c.2) *
        J₂ (i + 1) (update (Prod.snd ∘ p) i (u₂ c.2)) (update (Prod.snd ∘ q) i (u₂ c.2))) := by
  classical
  ext c
  simp only [comp_update, Prod.fst_mul, Prod.snd_mul, Prod.map_fst, Prod.map_snd]
  ring

omit [Ring C₁] [Ring C₂] [MeasureSpace C₁] [MeasureSpace C₂] in
/-- The top form of a product of two systems is continuous if both top forms are. -/
private theorem continuous_prod_uncurry (h₁ : Continuous (J₁ (n + 1)).uncurry)
    (h₂ : Continuous (J₂ (n + 1)).uncurry) :
    Continuous (fun pq : (ℕ → U₁ × U₂) × (ℕ → U₁ × U₂) ↦
      J₁ (n + 1) (Prod.fst ∘ pq.1) (Prod.fst ∘ pq.2) *
        J₂ (n + 1) (Prod.snd ∘ pq.1) (Prod.snd ∘ pq.2)) := by
  have h_fst : Continuous fun p : ℕ → U₁ × U₂ ↦ Prod.fst ∘ p :=
    continuous_pi fun k ↦ continuous_fst.comp (continuous_apply k)
  have h_snd : Continuous fun p : ℕ → U₁ × U₂ ↦ Prod.snd ∘ p :=
    continuous_pi fun k ↦ continuous_snd.comp (continuous_apply k)
  exact (h₁.comp ((h_fst.comp continuous_fst).prodMk (h_fst.comp continuous_snd))).mul
    (h₂.comp ((h_snd.comp continuous_fst).prodMk (h_snd.comp continuous_snd)))

/-- **The product of two sieve systems.** If `J₁` and `J₂` are sieve systems on `C₁` and `C₂`
with the same `n`, then the products `J₁ i (Prod.fst ∘ p) (Prod.fst ∘ q) * J₂ i (Prod.snd ∘ p)
(Prod.snd ∘ q)` form a sieve system on `C₁ × C₂`, with the product measure, entry map, map back,
twist, mass bound, weights and decay. -/
theorem prod [SFinite (volume : Measure C₁)] [SFinite (volume : Measure C₂)]
    (K₁ : SieveSystem u₁ ι₁ n J₁ ψ₁ E₁ Λ₁ β₁)
    (K₂ : SieveSystem u₂ ι₂ n J₂ ψ₂ E₂ Λ₂ β₂) :
    SieveSystem (Prod.map u₁ u₂) (Prod.map ι₁ ι₂) n
      (fun i p q ↦ J₁ i (Prod.fst ∘ p) (Prod.fst ∘ q) * J₂ i (Prod.snd ∘ p) (Prod.snd ∘ q))
      (fun x ↦ ψ₁ x.1 * ψ₂ x.2) (E₁ * E₂)
      (fun i p ↦ Λ₁ i (Prod.fst ∘ p) * Λ₂ i (Prod.snd ∘ p)) (fun ξ ↦ β₁ ξ.1 * β₂ ξ.2) := by
  -- The integrand at a common entry factors into the integrands of the two systems.
  have h_split := prod_integrand_eq (u₁ := u₁) (u₂ := u₂) (J₁ := J₁) (J₂ := J₂) (ψ₁ := ψ₁)
    (ψ₂ := ψ₂)
  constructor
  case psi_zero => simp [K₁.psi_zero, K₂.psi_zero]
  case integrable_mul_update =>
    intro i hi p q ξ
    rw [Measure.volume_eq_prod, h_split]
    exact (K₁.integrable_mul_update i hi _ _ _).mul_prod (K₂.integrable_mul_update i hi _ _ _)
  case integral_update =>
    intro i hi p q
    have := congrFun (h_split i p q 0)
    simp only [zero_mul, Prod.fst_zero, Prod.snd_zero, K₁.psi_zero, K₂.psi_zero, one_mul] at this
    simp only [Measure.volume_eq_prod, this]
    rw [← K₁.integral_update i hi, ← K₂.integral_update i hi]
    exact integral_prod_mul
      (fun c ↦ J₁ (i + 1) (update (Prod.fst ∘ p) i (u₁ c)) (update (Prod.fst ∘ q) i (u₁ c)))
      (fun c ↦ J₂ (i + 1) (update (Prod.snd ∘ p) i (u₂ c)) (update (Prod.snd ∘ q) i (u₂ c)))
  case norm_integral_mul_update_le =>
    intro i hi p q ξ hξ
    rw [Prod.isUnit_iff] at hξ
    rw [Measure.volume_eq_prod, h_split, integral_prod_mul
      (fun c ↦ ψ₁ (ξ.1 * c) *
        J₁ (i + 1) (update (Prod.fst ∘ p) i (u₁ c)) (update (Prod.fst ∘ q) i (u₁ c)))
      (fun c ↦ ψ₂ (ξ.2 * c) *
        J₂ (i + 1) (update (Prod.snd ∘ p) i (u₂ c)) (update (Prod.snd ∘ q) i (u₂ c)))]
    refine (norm_mul_le_of_le (K₁.norm_integral_mul_update_le i hi _ _ hξ.1)
      (K₂.norm_integral_mul_update_le i hi _ _ hξ.2)).trans_eq ?_
    ring
  case posSemidef =>
    intro κ _ a t ha
    exact (K₁.posSemidef (fun k ↦ Prod.fst ∘ a k) t.1 fun k ↦ by simp [ha]).hadamard
      (K₂.posSemidef (fun k ↦ Prod.snd ∘ a k) t.2 fun k ↦ by simp [ha])
  case continuous => exact continuous_prod_uncurry K₁.continuous K₂.continuous
  case norm_bot_le =>
    exact fun p q ↦ norm_mul_le_of_le (K₁.norm_bot_le _ _) (K₂.norm_bot_le _ _)
  case norm_le_of_isUnit_sub =>
    intro i hi p q hξ
    rw [Prod.isUnit_iff] at hξ
    simp only [Prod.fst_sub, Prod.snd_sub, Prod.map_fst, Prod.map_snd] at hξ ⊢
    refine (norm_mul_le_of_le (K₁.norm_le_of_isUnit_sub i hi (Prod.fst ∘ p) (Prod.fst ∘ q) hξ.1)
      (K₂.norm_le_of_isUnit_sub i hi (Prod.snd ∘ p) (Prod.snd ∘ q) hξ.2)).trans_eq ?_
    simp only [Function.comp_apply]
    ring

end Prod

section Pi

variable {τ : Type*} [Fintype τ] {C : τ → Type*} {U : τ → Type*} [∀ v, Ring (C v)]
  [∀ v, MeasureSpace (C v)] [∀ v, SigmaFinite (volume : Measure (C v))]
  [∀ v, TopologicalSpace (U v)]
  {u : ∀ v, C v → U v} {ι : ∀ v, U v → C v} {J : ∀ v, ℕ → (ℕ → U v) → (ℕ → U v) → ℂ}
  {ψ : ∀ v, C v → ℂ} {En : τ → ℝ} {Λ : ∀ v, ℕ → (ℕ → U v) → ℝ} {β : ∀ v, C v → ℝ}

omit [∀ v, MeasureSpace (C v)] [∀ v, SigmaFinite (volume : Measure (C v))]
  [∀ v, TopologicalSpace (U v)] in
/-- At a common entry of the heads, the integrand of a product of finitely many systems is the
product of the integrands of the factors. -/
private theorem pi_integrand_eq (i : ℕ) (p q : ℕ → ∀ v, U v) (ξ : ∀ v, C v) :
    (fun c : ∀ v, C v ↦ (∏ v, ψ v ((ξ * c) v)) *
      ∏ v, J v (i + 1) (fun k ↦ update p i (fun v ↦ u v (c v)) k v)
        (fun k ↦ update q i (fun v ↦ u v (c v)) k v)) =
    fun c ↦ ∏ v, ψ v (ξ v * c v) *
      J v (i + 1) (update (fun k ↦ p k v) i (u v (c v)))
        (update (fun k ↦ q k v) i (u v (c v))) := by
  ext c
  have h (r : ℕ → ∀ v, U v) (v : τ) : (fun k ↦ update r i (fun v ↦ u v (c v)) k v) =
      update (fun k ↦ r k v) i (u v (c v)) :=
    comp_update (fun y : ∀ v, U v ↦ y v) r i _
  simp only [h, Pi.mul_apply, prod_mul_distrib]

/-- **The product of finitely many sieve systems.** If `J v` is a sieve system on `C v` for each
`v` in a finite type `τ`, all with the same `n`, then the products `∏_v J v i (fun k ↦ p k v)
(fun k ↦ q k v)` form a sieve system on `∀ v, C v`, with the product measure, entry maps, maps
back, twists, mass bounds, weights and decays. -/
theorem pi (K : ∀ v, SieveSystem (u v) (ι v) n (J v) (ψ v) (En v) (Λ v) (β v)) :
    SieveSystem (fun c v ↦ u v (c v)) (fun x v ↦ ι v (x v)) n
      (fun i p q ↦ ∏ v, J v i (fun k ↦ p k v) (fun k ↦ q k v)) (fun c ↦ ∏ v, ψ v (c v))
      (∏ v, En v) (fun i p ↦ ∏ v, Λ v i (fun k ↦ p k v)) (fun ξ ↦ ∏ v, β v (ξ v)) := by
  -- The integrand at a common entry is the product of the integrands of the factors.
  have h_split := pi_integrand_eq (u := u) (J := J) (ψ := ψ)
  have h_bound {a : τ → ℂ} {r : τ → ℝ} (h : ∀ v, ‖a v‖ ≤ r v) : ‖∏ v, a v‖ ≤ ∏ v, r v :=
    (Finset.norm_prod_le _ _).trans (by gcongr with v; exact h v)
  constructor
  case psi_zero => simp [fun v ↦ (K v).psi_zero]
  case integrable_mul_update =>
    intro i hi p q ξ
    rw [h_split, volume_pi]
    exact Integrable.fintype_prod_dep fun v ↦ (K v).integrable_mul_update i hi _ _ _
  case integral_update =>
    intro i hi p q
    have := congrFun (h_split i p q 0)
    simp only [zero_mul, Pi.zero_apply, (K _).psi_zero, prod_const_one, one_mul] at this
    simp only [this]
    rw [integral_fintype_prod_volume_eq_prod (fun v c ↦
      J v (i + 1) (update (fun k ↦ p k v) i (u v c)) (update (fun k ↦ q k v) i (u v c)))]
    exact prod_congr rfl fun v _ ↦ (K v).integral_update i hi _ _
  case norm_integral_mul_update_le =>
    intro i hi p q ξ hξ
    rw [Pi.isUnit_iff] at hξ
    rw [h_split, integral_fintype_prod_volume_eq_prod (fun v c ↦ ψ v (ξ v * c) *
      J v (i + 1) (update (fun k ↦ p k v) i (u v c)) (update (fun k ↦ q k v) i (u v c)))]
    refine (h_bound fun v ↦ (K v).norm_integral_mul_update_le i hi _ _ (hξ v)).trans_eq ?_
    simp only [prod_mul_distrib]
  case posSemidef =>
    intro κ _ a t ha
    exact posSemidef_schur_finset_prod (s := univ) fun v _ ↦
      (K v).posSemidef (fun k j ↦ a k j v) (t v) fun k ↦ by simp [ha]
  case continuous =>
    have h_comp (v : τ) : Continuous fun p : ℕ → ∀ v, U v ↦ fun k ↦ p k v :=
      continuous_pi fun k ↦ (continuous_apply v).comp (continuous_apply k)
    exact continuous_finsetProd _ fun v _ ↦ (K v).continuous.comp
      (((h_comp v).comp continuous_fst).prodMk ((h_comp v).comp continuous_snd))
  case norm_bot_le =>
    exact fun p q ↦ h_bound fun v ↦ (K v).norm_bot_le _ _
  case norm_le_of_isUnit_sub =>
    intro i hi p q hξ
    rw [Pi.isUnit_iff] at hξ
    refine (h_bound fun v ↦ (K v).norm_le_of_isUnit_sub i hi _ _ (hξ v)).trans_eq ?_
    simp only [Pi.sub_apply, prod_mul_distrib]

end Pi

/-! ### Sums over a finite family of heads -/

variable {κ : Type} [Fintype κ]

/-- For `i ≤ n` and finitely many heads `a k`, the sum of `J (i + 1)` over all pairs of heads is
integrable in a common entry `u c` at position `i`. -/
theorem integrable_sum_update (K : SieveSystem u ι n J ψ En Λ β) {i : ℕ} (hi : i ≤ n)
    (a : κ → ℕ → U) :
    Integrable fun c : C ↦
      ∑ k, ∑ l, J (i + 1) (update (a k) i (u c)) (update (a l) i (u c)) :=
  integrable_finsetSum _ fun _ _ ↦ integrable_finsetSum _ fun _ _ ↦ K.integrable_update hi _ _

/-- The recursion summed over all pairs from finitely many heads `a k`: for `i ≤ n`, the sum of the
forms `J i` is the integral of the sum of the forms `J (i + 1)` over a common entry `u c` at
position `i`. -/
theorem integral_sum_update (K : SieveSystem u ι n J ψ En Λ β) {i : ℕ} (hi : i ≤ n)
    (a : κ → ℕ → U) :
    ∫ c : C, ∑ k, ∑ l, J (i + 1) (update (a k) i (u c)) (update (a l) i (u c)) =
      ∑ k, ∑ l, J i (a k) (a l) := by
  rw [integral_finsetSum _ fun _ _ ↦ integrable_finsetSum _ fun _ _ ↦ K.integrable_update hi _ _]
  refine sum_congr rfl fun k _ ↦ ?_
  rw [integral_finsetSum _ fun _ _ ↦ K.integrable_update hi _ _]
  exact sum_congr rfl fun l _ ↦ K.integral_update i hi _ _

/-- For `i ≤ n`, finitely many heads `a k` and a unit `ξ`, the integral of the sum of the forms
`J (i + 1)` over all pairs of heads with a common entry `u c` at position `i`, twisted by
`ψ (ξ * c)`, has modulus at most `β ξ * (∑ k, Λ i (a k)) ^ 2`. -/
theorem norm_integral_mul_sum_update_le (K : SieveSystem u ι n J ψ En Λ β) {i : ℕ} (hi : i ≤ n)
    (a : κ → ℕ → U) {ξ : C} (hξ : IsUnit ξ) :
    ‖∫ c : C, ψ (ξ * c) *
        ∑ k, ∑ l, J (i + 1) (update (a k) i (u c)) (update (a l) i (u c))‖ ≤
      β ξ * (∑ k, Λ i (a k)) ^ 2 :=
  calc _ = ‖∑ k, ∑ l,
        ∫ c, ψ (ξ * c) * J (i + 1) (update (a k) i (u c)) (update (a l) i (u c))‖ := by
        simp only [mul_sum]
        rw [integral_finsetSum _ fun _ _ ↦
          integrable_finsetSum _ fun _ _ ↦ K.integrable_mul_update i hi _ _ _]
        congr 1
        exact sum_congr rfl fun k _ ↦
          integral_finsetSum _ fun _ _ ↦ K.integrable_mul_update i hi _ _ _
    _ ≤ ∑ k, ∑ l, β ξ * (Λ i (a k) * Λ i (a l)) :=
        norm_sum_le_of_le _ fun k _ ↦ norm_sum_le_of_le _ fun l _ ↦
          K.norm_integral_mul_update_le i hi (a k) (a l) hξ
    _ = β ξ * (∑ k, Λ i (a k)) ^ 2 := by simp only [sq, sum_mul_sum, ← mul_sum]

/-- If finitely many heads `a k` have a common entry `t` at position `i ≤ n`, then the sum of
`J (i + 1)` over all pairs of heads is a nonnegative real number. -/
theorem sum_nonneg (K : SieveSystem u ι n J ψ En Λ β) {i : ℕ} (hi : i ≤ n) (a : κ → ℕ → U)
    {t : U} (h_common : ∀ k, a k i = t) :
    0 ≤ ∑ k, ∑ l, J (i + 1) (a k) (a l) := by
  -- Descend on `i`. At `i = n` the sum is the value of a positive semidefinite form at
  -- `(1, …, 1)`. Below, it is the integral over a common next entry of the same sums for `i + 1`.
  induction hi using Nat.decreasingInduction generalizing a t with
  | self =>
    simpa [mulVec, dotProduct] using (K.posSemidef a t h_common).dotProduct_mulVec_nonneg 1
  | of_succ i hi ih =>
    rw [← K.integral_sum_update hi a]
    exact integral_nonneg fun c ↦ ih _ fun k ↦ update_self (i + 1) (u c) (a k)

/-- Let finitely many heads `b y k`, depending on a parameter `y` in a first-countable space `X`,
have a common entry `c y` at position `i ≤ n` for each `y`. The sum of `J (i + 1)` over all pairs
of heads, a nonnegative real number, is lower semicontinuous in `y` at each point `x` where the
heads are continuous. This is stated for `ENNReal.ofReal` of its real part. -/
theorem lowerSemicontinuousAt_sum {X : Type*} [TopologicalSpace X] [FirstCountableTopology X]
    (K : SieveSystem u ι n J ψ En Λ β) {i : ℕ} (hi : i ≤ n) (b : X → κ → ℕ → U) {c : X → U}
    (h_common : ∀ y k, b y k i = c y) {x : X} (h_cont : ∀ k, ContinuousAt (fun y ↦ b y k) x) :
    LowerSemicontinuousAt
      (fun y ↦ ENNReal.ofReal (RCLike.re (∑ k, ∑ l, J (i + 1) (b y k) (b y l)))) x := by
  -- Descend on `i`. At `i = n` the sum is continuous at `x`. Below, it is the integral over a
  -- common next entry `u z` of the same sums for `i + 1`, and Fatou's lemma applies.
  induction hi using Nat.decreasingInduction generalizing b c with
  | self =>
    have hJ : Continuous (J (n + 1)).uncurry := K.continuous
    exact ContinuousAt.lowerSemicontinuousAt (by fun_prop [ENNReal.ofReal])
  | of_succ i hi ih =>
    -- `G y z` is the sum for `i + 1` at the heads `b y k` with the entry `u z` at `i + 1`.
    let G (y : X) (z : C) : ℂ :=
      ∑ k, ∑ l, J (i + 1 + 1) (update (b y k) (i + 1) (u z)) (update (b y l) (i + 1) (u z))
    have h_lsc (z : C) : LowerSemicontinuousAt (fun y ↦ ENNReal.ofReal (RCLike.re (G y z))) x :=
      ih _ (fun y k ↦ update_self (i + 1) (u z) (b y k)) (by fun_prop)
    have h_int (y : X) : Integrable (G y) := K.integrable_sum_update hi (b y)
    have h_re (y : X) : ENNReal.ofReal (RCLike.re (∑ k, ∑ l, J (i + 1) (b y k) (b y l))) =
        ∫⁻ z, ENNReal.ofReal (RCLike.re (G y z)) := by
      have h_nonneg (z : C) : 0 ≤ G y z :=
        K.sum_nonneg hi _ fun k ↦ update_self (i + 1) (u z) (b y k)
      rw [← K.integral_sum_update hi (b y), ← integral_re (h_int y),
        ofReal_integral_eq_lintegral_ofReal (h_int y).re
          (.of_forall fun z ↦ (RCLike.nonneg_iff.1 (h_nonneg z)).1)]
    simp only [lowerSemicontinuousAt_iff_le_liminf, h_re] at h_lsc ⊢
    calc ∫⁻ z, ENNReal.ofReal (RCLike.re (G x z))
      _ ≤ ∫⁻ z, Filter.liminf (fun y ↦ ENNReal.ofReal (RCLike.re (G y z))) (nhds x) :=
          lintegral_mono h_lsc
      _ ≤ Filter.liminf (fun y ↦ ∫⁻ z, ENNReal.ofReal (RCLike.re (G y z))) (nhds x) :=
          lintegral_liminf_le' fun y ↦ (h_int y).re.aemeasurable.ennreal_ofReal

end SieveSystem

end TauCeti
