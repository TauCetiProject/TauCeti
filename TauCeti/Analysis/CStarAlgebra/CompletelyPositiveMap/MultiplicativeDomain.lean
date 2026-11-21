/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.Subalgebra
public import TauCeti.Analysis.CStarAlgebra.CompletelyPositiveMap
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

/-!
# The multiplicative domain of a unital `2`-positive map

For a unital `2`-positive map `φ : A → B` between unital C⋆-algebras, the Kadison–Schwarz
inequality `φ(a)⋆ φ(a) ≤ φ(a⋆a)` holds for every `a`. The **multiplicative domain** of `φ` is the
set of `a` at which both Schwarz inequalities are equalities:

`φ(a⋆a) = φ(a)⋆ φ(a)` and `φ(aa⋆) = φ(a) φ(a)⋆`.

Choi's theorem says that the first equality already forces `φ(ba) = φ(b) φ(a)` for every `b`, and
the second forces `φ(ab) = φ(a) φ(b)`. Hence the multiplicative domain is exactly the set of `a`
against which `φ` is multiplicative on both sides. It is a closed unital star subalgebra of `A`,
the restriction of `φ` to it is a unital star homomorphism, and a unital `2`-positive map from `A`
to itself that fixes a star subalgebra pointwise is bimodular over that subalgebra.

Every unital completely positive map is `2`-positive (`CompletelyPositiveMapClass.isNPositive`),
so everything here applies to unital completely positive maps.

Both Schwarz equalities are needed. A single one does not give a star-closed set: for the
compression `a ↦ pap` by a projection `p`, the first equality alone describes the elements with
`(1 - p) a p = 0`.

## Main declarations

* `TauCeti.eq_zero_of_forall_nonneg_add_smul_add_star_smul_star`: if
  `0 ≤ p + t • u + star t • star u` for every complex `t`, then `u = 0`.
* `TauCeti.IsNPositive.map_mul_of_map_star_mul_self_eq`: if `φ(a⋆a) = φ(a)⋆ φ(a)` then
  `φ(ba) = φ(b) φ(a)` for every `b`, and `TauCeti.IsNPositive.map_mul_of_map_mul_star_self_eq`:
  if `φ(aa⋆) = φ(a) φ(a)⋆` then `φ(ab) = φ(a) φ(b)` for every `b`.
* `TauCeti.IsNPositive.multiplicativeDomain`: the multiplicative domain as a star subalgebra,
  with `TauCeti.IsNPositive.mem_multiplicativeDomain_iff_forall_map_mul` (Choi's
  characterization) and `TauCeti.IsNPositive.isClosed_multiplicativeDomain`.
* `TauCeti.IsNPositive.multiplicativeDomainHom`: the restriction of `φ` to its multiplicative
  domain, as a unital star homomorphism.
* `TauCeti.IsNPositive.le_multiplicativeDomain_of_forall_map_eq`: a star subalgebra fixed
  pointwise lies in the multiplicative domain, so `φ(sa) = s φ(a)` and `φ(as) = φ(a) s` for its
  elements `s` (`TauCeti.IsNPositive.map_mul_left_of_forall_map_eq`,
  `TauCeti.IsNPositive.map_mul_right_of_forall_map_eq`).

## References

* M.-D. Choi, *A Schwarz inequality for positive linear maps on C⋆-algebras*, Illinois J. Math.
  18 (1974), Theorem 3.1.
* V. Paulsen, *Completely Bounded Maps and Operator Algebras*, Theorem 3.18.
-/

public section

namespace TauCeti

/-- In a C⋆-algebra, if `0 ≤ p + t • u + star t • star u` for every complex `t`, then `u = 0`. -/
theorem eq_zero_of_forall_nonneg_add_smul_add_star_smul_star {B : Type*}
    [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B] {p u : B}
    (h : ∀ t : ℂ, 0 ≤ p + t • u + star t • star u) : u = 0 := by
  -- Comparing `t` with `-t` bounds `t • u + star t • star u` in norm by `3 ‖p‖`; the choices
  -- `t = r` and `t = r * I` for real `r` then bound `‖(2 * r) • u‖` by `6 ‖p‖`.
  set w : ℂ → B := fun t => t • u + star t • star u
  have hw : ∀ t, ‖w t‖ ≤ 3 * ‖p‖ := fun t => by
    have hle : p + w t ≤ (2 : ℝ) • p := by
      have := h (-t)
      rw [← sub_nonneg]
      convert this using 1
      simp only [w, star_neg, neg_smul]
      module
    have hp : ‖p + w t‖ ≤ 2 * ‖p‖ := by
      simpa [norm_smul] using CStarAlgebra.norm_le_norm_of_le_of_nonneg hle
        (by simpa [add_assoc, w] using h t)
    calc ‖w t‖ = ‖(p + w t) - p‖ := by rw [add_sub_cancel_left]
      _ ≤ ‖p + w t‖ + ‖p‖ := norm_sub_le _ _
      _ ≤ 3 * ‖p‖ := by linarith
  -- `w r - I • w (r * I) = (2 * r) • u` for real `r`.
  have hu : ∀ r : ℝ, 0 ≤ r → 2 * r * ‖u‖ ≤ 6 * ‖p‖ := fun r hr => by
    have heq : w r - Complex.I • w (r * Complex.I) = ((2 * r : ℝ) : ℂ) • u := by
      simp only [w, Complex.star_def, map_mul, Complex.conj_ofReal, Complex.conj_I, smul_add,
        smul_smul]
      ring_nf
      simp only [Complex.I_sq]
      module
    calc 2 * r * ‖u‖ = ‖w r - Complex.I • w (r * Complex.I)‖ := by
          rw [heq, norm_smul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      _ ≤ ‖w r‖ + ‖w (r * Complex.I)‖ := (norm_sub_le _ _).trans_eq (by
          rw [norm_smul, Complex.norm_I, one_mul])
      _ ≤ 6 * ‖p‖ := by linarith [hw r, hw (r * Complex.I)]
  by_contra hne
  have hpos : 0 < ‖u‖ := norm_pos_iff.mpr hne
  have := hu ((3 * ‖p‖ + 1) / ‖u‖) (by positivity)
  rw [mul_assoc, div_mul_cancel₀ _ hpos.ne'] at this
  linarith

variable {A B : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B] {φ : A →ₗ[ℂ] B}

/-- **Choi's theorem.** If a unital `2`-positive map satisfies the Schwarz equality
`φ(a⋆a) = φ(a)⋆ φ(a)`, then `φ(ba) = φ(b) φ(a)` for every `b`. -/
theorem IsNPositive.map_mul_of_map_star_mul_self_eq (hφ : IsNPositive 2 φ) (h1 : φ 1 = 1)
    {a : A} (ha : φ (star a * a) = star (φ a) * φ a) (b : A) : φ (b * a) = φ b * φ a := by
  -- The Schwarz inequality at `star b + t • a` is linear in `t` because of `ha`.
  have hq : ∀ t : ℂ, 0 ≤ (φ (b * star b) - φ b * star (φ b)) + t • (φ (b * a) - φ b * φ a) +
      star t • star (φ (b * a) - φ b * φ a) := fun t => by
    have := sub_nonneg.mpr (hφ.star_map_mul_map_le_of_map_one h1 (star b + t • a))
    convert this using 1
    have hs : φ (star a * star b) = star (φ (b * a)) := by
      rw [← star_mul, hφ.map_star two_pos]
    simp only [star_add, star_star, star_smul, add_mul, mul_add, smul_mul_assoc, mul_smul_comm,
      map_add, map_smul, hφ.map_star two_pos, star_sub, star_mul, ha, hs, smul_sub]
    module
  exact sub_eq_zero.mp (eq_zero_of_forall_nonneg_add_smul_add_star_smul_star hq)

/-- **Choi's theorem.** If a unital `2`-positive map satisfies the Schwarz equality
`φ(aa⋆) = φ(a) φ(a)⋆`, then `φ(ab) = φ(a) φ(b)` for every `b`. -/
theorem IsNPositive.map_mul_of_map_mul_star_self_eq (hφ : IsNPositive 2 φ) (h1 : φ 1 = 1)
    {a : A} (ha : φ (a * star a) = φ a * star (φ a)) (b : A) : φ (a * b) = φ a * φ b := by
  have ha' : φ (star (star a) * star a) = star (φ (star a)) * φ (star a) := by
    rw [star_star, hφ.map_star two_pos, star_star, ha]
  simpa [← hφ.map_star two_pos] using
    congrArg star (hφ.map_mul_of_map_star_mul_self_eq h1 ha' (star b))

/-- The **multiplicative domain** of a unital `2`-positive map `φ`: the closed unital star
subalgebra of the elements `a` with `φ(a⋆a) = φ(a)⋆ φ(a)` and `φ(aa⋆) = φ(a) φ(a)⋆`. By
`TauCeti.IsNPositive.mem_multiplicativeDomain_iff_forall_map_mul`, these are the elements against
which `φ` is multiplicative on both sides. -/
def IsNPositive.multiplicativeDomain (hφ : IsNPositive 2 φ) (h1 : φ 1 = 1) :
    StarSubalgebra ℂ A where
  carrier := {a | φ (star a * a) = star (φ a) * φ a ∧ φ (a * star a) = φ a * star (φ a)}
  mul_mem' {a c} ha hc := by
    have hac : φ (a * c) = φ a * φ c := hφ.map_mul_of_map_mul_star_self_eq h1 ha.2 c
    refine ⟨?_, ?_⟩
    · rw [← mul_assoc, hφ.map_mul_of_map_star_mul_self_eq h1 hc.1,
        hφ.map_mul_of_map_star_mul_self_eq h1 ha.1, mul_assoc, ← hac, hφ.map_star two_pos]
    · rw [mul_assoc, hφ.map_mul_of_map_mul_star_self_eq h1 ha.2,
        hφ.map_mul_of_map_mul_star_self_eq h1 hc.2, ← mul_assoc, ← hac, hφ.map_star two_pos]
  one_mem' := by simp [h1]
  add_mem' {a c} ha hc := by
    have hac : φ (star a * c) = star (φ a) * φ c := by
      rw [hφ.map_mul_of_map_star_mul_self_eq h1 hc.1, hφ.map_star two_pos]
    have hca : φ (star c * a) = star (φ c) * φ a := by
      rw [hφ.map_mul_of_map_star_mul_self_eq h1 ha.1, hφ.map_star two_pos]
    have hac' : φ (a * star c) = φ a * star (φ c) := by
      rw [hφ.map_mul_of_map_mul_star_self_eq h1 ha.2, hφ.map_star two_pos]
    have hca' : φ (c * star a) = φ c * star (φ a) := by
      rw [hφ.map_mul_of_map_mul_star_self_eq h1 hc.2, hφ.map_star two_pos]
    refine ⟨?_, ?_⟩
    · simp only [star_add, add_mul, mul_add, map_add, ha.1, hc.1, hac, hca]
    · simp only [star_add, add_mul, mul_add, map_add, ha.2, hc.2, hac', hca']
  zero_mem' := by simp
  algebraMap_mem' z := by
    simp [Algebra.algebraMap_eq_smul_one, h1]
  star_mem' {a} ha := by
    simp only [Set.mem_ofPred_eq, star_star, hφ.map_star two_pos] at ha ⊢
    exact ⟨ha.2, ha.1⟩

variable (hφ : IsNPositive 2 φ) (h1 : φ 1 = 1)

@[simp]
theorem IsNPositive.mem_multiplicativeDomain {a : A} :
    a ∈ hφ.multiplicativeDomain h1 ↔
      φ (star a * a) = star (φ a) * φ a ∧ φ (a * star a) = φ a * star (φ a) :=
  Iff.rfl

/-- **Choi's characterization** of the multiplicative domain: `a` lies in it exactly when `φ` is
multiplicative against `a` on both sides. -/
theorem IsNPositive.mem_multiplicativeDomain_iff_forall_map_mul {a : A} :
    a ∈ hφ.multiplicativeDomain h1 ↔ ∀ b, φ (a * b) = φ a * φ b ∧ φ (b * a) = φ b * φ a := by
  refine ⟨fun ha b => ⟨hφ.map_mul_of_map_mul_star_self_eq h1 ha.2 b,
    hφ.map_mul_of_map_star_mul_self_eq h1 ha.1 b⟩, fun h => ⟨?_, ?_⟩⟩
  · rw [(h (star a)).2, hφ.map_star two_pos]
  · rw [(h (star a)).1, hφ.map_star two_pos]

theorem IsNPositive.map_mul_of_mem_multiplicativeDomain_left {a : A}
    (ha : a ∈ hφ.multiplicativeDomain h1) (b : A) : φ (a * b) = φ a * φ b :=
  hφ.map_mul_of_map_mul_star_self_eq h1 ha.2 b

theorem IsNPositive.map_mul_of_mem_multiplicativeDomain_right {a : A}
    (ha : a ∈ hφ.multiplicativeDomain h1) (b : A) : φ (b * a) = φ b * φ a :=
  hφ.map_mul_of_map_star_mul_self_eq h1 ha.1 b

/-- The multiplicative domain of a unital `2`-positive map is norm closed. -/
theorem IsNPositive.isClosed_multiplicativeDomain :
    IsClosed (hφ.multiplicativeDomain h1 : Set A) := by
  have hc : Continuous φ := funext (hφ.toPositiveLinearMap_apply two_pos) ▸
    map_continuous (hφ.toPositiveLinearMap two_pos)
  exact (isClosed_eq (hc.comp (continuous_star.mul continuous_id))
      ((continuous_star.comp hc).mul hc)).inter
    (isClosed_eq (hc.comp (continuous_id.mul continuous_star)) (hc.mul (continuous_star.comp hc)))

/-- The multiplicative domain of a unital `2`-positive map is everything exactly when the map is
multiplicative. -/
theorem IsNPositive.multiplicativeDomain_eq_top_iff :
    hφ.multiplicativeDomain h1 = ⊤ ↔ ∀ a b, φ (a * b) = φ a * φ b := by
  refine ⟨fun h a b => hφ.map_mul_of_mem_multiplicativeDomain_left h1 (h ▸ trivial) b,
    fun h => eq_top_iff.mpr fun a _ => ?_⟩
  rw [hφ.mem_multiplicativeDomain_iff_forall_map_mul]
  exact fun b => ⟨h a b, h b a⟩

/-- The restriction of a unital `2`-positive map to its multiplicative domain, as a unital star
homomorphism. -/
def IsNPositive.multiplicativeDomainHom : hφ.multiplicativeDomain h1 →⋆ₐ[ℂ] B where
  toFun a := φ a
  map_one' := h1
  map_mul' a c := hφ.map_mul_of_mem_multiplicativeDomain_left h1 a.property c
  map_zero' := map_zero φ
  map_add' a c := map_add φ (a : A) c
  commutes' z := by simp [Algebra.algebraMap_eq_smul_one, h1]
  map_star' a := hφ.map_star two_pos a

@[simp]
theorem IsNPositive.multiplicativeDomainHom_apply (a : hφ.multiplicativeDomain h1) :
    hφ.multiplicativeDomainHom h1 a = φ (a : A) :=
  (rfl)

end TauCeti

namespace TauCeti

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  {φ : A →ₗ[ℂ] A} {S : StarSubalgebra ℂ A}

/-- A star subalgebra fixed pointwise by a unital `2`-positive map lies in its multiplicative
domain. -/
theorem IsNPositive.le_multiplicativeDomain_of_forall_map_eq (hφ : IsNPositive 2 φ)
    (h1 : φ 1 = 1) (hS : ∀ s ∈ S, φ s = s) :
    S ≤ hφ.multiplicativeDomain h1 := fun s hs => by
  have hs' : star s ∈ S := star_mem hs
  rw [hφ.mem_multiplicativeDomain, hS s hs, hS _ (S.mul_mem hs' hs),
    hS _ (S.mul_mem hs hs')]
  exact ⟨rfl, rfl⟩

/-- A unital `2`-positive map fixing a star subalgebra pointwise is a left module map over it. -/
theorem IsNPositive.map_mul_left_of_forall_map_eq (hφ : IsNPositive 2 φ) (h1 : φ 1 = 1)
    (hS : ∀ s ∈ S, φ s = s) {s : A} (hs : s ∈ S)
    (a : A) : φ (s * a) = s * φ a := by
  rw [hφ.map_mul_of_mem_multiplicativeDomain_left h1
    (hφ.le_multiplicativeDomain_of_forall_map_eq h1 hS hs), hS s hs]

/-- A unital `2`-positive map fixing a star subalgebra pointwise is a right module map over it. -/
theorem IsNPositive.map_mul_right_of_forall_map_eq (hφ : IsNPositive 2 φ) (h1 : φ 1 = 1)
    (hS : ∀ s ∈ S, φ s = s) {s : A} (hs : s ∈ S)
    (a : A) : φ (a * s) = φ a * s := by
  rw [hφ.map_mul_of_mem_multiplicativeDomain_right h1
    (hφ.le_multiplicativeDomain_of_forall_map_eq h1 hS hs), hS s hs]

end TauCeti
