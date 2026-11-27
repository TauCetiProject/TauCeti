/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Ring.Subring.Units
public import Mathlib.GroupTheory.GroupAction.SubMulAction

/-!
# Maximal invariants

A function `M : α → β` is a *maximal invariant* of an action of `G` on `α` if it is invariant,
`M (g • x) = M x`, and separates orbits: `M x = M y` only when `y = g • x` for some `g`. This is
the reduction by invariance of testing theory: an invariant test is a function of a maximal
invariant (Ferguson, *Mathematical Statistics: A Decision Theoretic Approach*, §5.6).

Inverting a family of invariant tests gives an invariant confidence set; the duality of tests and
confidence sets used there is `TauCeti.hasConfidenceCoverage_iff_forall_hasTestLevel` in
`TauCeti.Statistics.Experiments.ConfidenceSets`.

## Main definitions

* `MulAction.IsMaximalInvariant G M`: `M` is invariant under `G` and separates `G`-orbits.
* `SubMulAction.posHalfPlane K`: the pairs `(x, s)` with `s > 0`, as a set stable under the
  diagonal scaling by the positive units of an ordered semiring `K`.

## Main results

* `MulAction.IsMaximalInvariant.factorsThrough_iff`: a function factors through a maximal
  invariant `M` (`Function.FactorsThrough`) if and only if it is invariant (Ferguson, §5.6, Thm 1).
* `MulAction.isMaximalInvariant_mk`: the projection to the orbit quotient is a maximal invariant.
* `SubMulAction.isMaximalInvariant_posHalfPlane_div`: `x / s` is a maximal invariant of the scale
  group acting on pairs `(x, s)` with `s > 0` (Ferguson, §5.6, Example 2).

The results are adapted from `CKSD.invariant_iff_factors_through_maximal_invariant` and
`CKSD.mean_scale_ratio_eq_iff` in lean-CKSD's `CKSD/Inference/InvariantTesting.lean`.

## References

* T. S. Ferguson, *Mathematical Statistics: A Decision Theoretic Approach*, Academic Press, 1967,
  §5.6, pp. 244–246.
-/

public section

namespace MulAction

variable {G α β γ : Type*}

/-- A function `M : α → β` is a **maximal invariant** of the action of `G` on `α` if it is
invariant under `G` and takes equal values only on points of the same orbit. -/
structure IsMaximalInvariant (G : Type*) [SMul G α] (M : α → β) : Prop where
  /-- A maximal invariant is invariant. -/
  apply_smul (g : G) (x : α) : M (g • x) = M x
  /-- A maximal invariant separates orbits. -/
  exists_smul_eq ⦃x y : α⦄ : M x = M y → ∃ g : G, g • x = y

section SMul

variable [SMul G α] {M : α → β}

/-- `M` is a maximal invariant if and only if `M x = M y` holds exactly when `y = g • x` for some
`g`. -/
theorem isMaximalInvariant_iff :
    IsMaximalInvariant G M ↔ ∀ x y, M x = M y ↔ ∃ g : G, g • x = y where
  mp h x y := ⟨(h.exists_smul_eq ·), by rintro ⟨g, rfl⟩; exact (h.apply_smul g x).symm⟩
  mpr h := ⟨fun g x ↦ ((h x (g • x)).2 ⟨g, rfl⟩).symm, fun x y ↦ (h x y).1⟩

/-- A maximal invariant takes equal values exactly on points of the same orbit. -/
theorem IsMaximalInvariant.apply_eq_apply_iff (hM : IsMaximalInvariant G M) {x y : α} :
    M x = M y ↔ ∃ g : G, g • x = y :=
  isMaximalInvariant_iff.1 hM x y

/-- A function factors through a maximal invariant `M` if and only if it is invariant. -/
theorem IsMaximalInvariant.factorsThrough_iff (hM : IsMaximalInvariant G M) (f : α → γ) :
    f.FactorsThrough M ↔ ∀ (g : G) (x : α), f (g • x) = f x where
  mp hf g x := hf (hM.apply_smul g x)
  mpr hf x y hxy := by
    obtain ⟨g, rfl⟩ := hM.exists_smul_eq hxy
    exact (hf g x).symm

end SMul

/-- The projection of `α` onto its orbit quotient is a maximal invariant. -/
theorem isMaximalInvariant_mk [Group G] [MulAction G α] :
    IsMaximalInvariant G (Quotient.mk (orbitRel G α)) where
  apply_smul g x := Quotient.sound (mem_orbit x g)
  exists_smul_eq _ _ hxy := mem_orbit_iff.1 (orbitRel_apply.1 (Quotient.exact hxy.symm))

end MulAction

namespace SubMulAction

section Semiring

variable (K : Type*) [Semiring K] [LinearOrder K] [IsStrictOrderedRing K]

/-- The pairs `(x, s)` with `s > 0`, stable under the diagonal action `(x, s) ↦ (c x, c s)` of the
positive units `c` of `K`. -/
def posHalfPlane : SubMulAction (Units.posSubgroup K) (K × K) where
  carrier := {p | 0 < p.2}
  smul_mem' c _ hp := mul_pos c.prop hp

variable {K}

/-- A pair lies in `SubMulAction.posHalfPlane K` if and only if its second coordinate is
positive. -/
@[simp]
theorem mem_posHalfPlane {p : K × K} : p ∈ posHalfPlane K ↔ 0 < p.2 :=
  Iff.rfl

end Semiring

variable {K : Type*} [Semifield K] [LinearOrder K] [IsStrictOrderedRing K]

/-- The ratio `x / s` is a maximal invariant of the scale group of positive units acting on the
pairs `(x, s)` with `s > 0`. -/
theorem isMaximalInvariant_posHalfPlane_div :
    MulAction.IsMaximalInvariant (Units.posSubgroup K)
      (fun p : posHalfPlane K ↦ (p : K × K).1 / (p : K × K).2) where
  -- `c • (x, s)` unfolds definitionally to `(c * x, c * s)`.
  apply_smul c _ := mul_div_mul_left _ _ (Units.ne_zero (c : Kˣ))
  exists_smul_eq := by
    -- Membership in `posHalfPlane K` is `0 < s` by definition (`mem_posHalfPlane`).
    rintro ⟨⟨x, s⟩, hs : 0 < s⟩ ⟨⟨y, t⟩, ht : 0 < t⟩ (h : x / s = y / t)
    have hc : Units.mk0 (t / s) (div_pos ht hs).ne' ∈ Units.posSubgroup K :=
      (Units.mem_posSubgroup _).2 (div_pos ht hs)
    refine ⟨⟨_, hc⟩, ?_⟩
    ext <;> simp only [SubMulAction.val_smul, Prod.smul_fst, Prod.smul_snd, Subgroup.mk_smul,
      Units.smul_mk0, smul_eq_mul]
    · rw [div_mul_comm, h, div_mul_cancel₀ y ht.ne']
    · exact div_mul_cancel₀ t hs.ne'

end SubMulAction
