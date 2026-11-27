/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.Span
public import TauCeti.Algebra.Category.ModuleCat.Filtration
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.RingTheory.Multiplicity
import Mathlib.Tactic.LinearCombination

/-!
# Checks: exhaustive, separated and complete filtrations of `ℤ`

An antitone family of submodules, read at `ℤᵒᵖ`, is a decreasingly filtered module
(`CategoryTheory.FilteredObject.ofSubmodules`), whose exhaustiveness and separatedness read in the
lattice of submodules. Checks on `ℤ` as a `ℤ`-module:

* the constant filtration `F^p = ℤ` is exhaustive and not separated
  (`isExhaustive_const_top`, `not_isSeparated_const_top`);
* the zero filtration `F^p = 0` is separated and not exhaustive
  (`isSeparated_const_bot`, `not_isExhaustive_const_bot`);
* the `ℓ`-adic filtration `F^p = ℓ^p ℤ` for `p ≥ 0`, and `ℤ` for `p ≤ 0`, is exhaustive
  (`isExhaustive_adicFiltration`), and separated for `|ℓ| ≠ 1` (`isSeparated_adicFiltration`):
  by Mathlib's `Int.finiteMultiplicity_iff`, an integer divisible by every power of `ℓ` is `0`.
  For `ℓ ≥ 2` it is not complete (`not_isComplete_adicFiltration`): the partial sums
  `∑_{i < p} (-ℓ)^i` of the `ℓ`-adic expansion of `1 / (1 + ℓ)` are a compatible family in the
  quotients `ℤ / ℓ^p` that no integer represents.
-/

public section

open CategoryTheory Opposite

namespace TauCeti.Examples.DecreasingFiltration

open FilteredObject

/-! ### Constant filtrations of `ℤ` -/

/-- The constant filtration `F^p = ℤ` of `ℤ` is exhaustive. -/
theorem isExhaustive_const_top :
    (ofSubmodules (fun _ : ℤᵒᵖ ↦ (⊤ : Submodule ℤ ℤ)) fun _ _ _ ↦ le_rfl).IsExhaustive :=
  isExhaustive_of_step_eq_top _ (i := op (0 : ℤ)) (by rw [step_ofSubmodules, map_top])

/-- The constant filtration `F^p = ℤ` of `ℤ` is not separated. -/
theorem not_isSeparated_const_top :
    ¬ (ofSubmodules (fun _ : ℤᵒᵖ ↦ (⊤ : Submodule ℤ ℤ)) fun _ _ _ ↦ le_rfl).IsSeparated := by
  rw [isSeparated_ofSubmodules_iff]
  exact fun h ↦ top_ne_bot (h ⊤ fun _ ↦ le_rfl)

/-- The zero filtration `F^p = 0` of `ℤ` is separated. -/
theorem isSeparated_const_bot :
    (ofSubmodules (fun _ : ℤᵒᵖ ↦ (⊥ : Submodule ℤ ℤ)) fun _ _ _ ↦ le_rfl).IsSeparated :=
  isSeparated_of_step_eq_bot _ (i := op (0 : ℤ)) (by rw [step_ofSubmodules, map_bot])

/-- The zero filtration `F^p = 0` of `ℤ` is not exhaustive. -/
theorem not_isExhaustive_const_bot :
    ¬ (ofSubmodules (fun _ : ℤᵒᵖ ↦ (⊥ : Submodule ℤ ℤ)) fun _ _ _ ↦ le_rfl).IsExhaustive := by
  rw [isExhaustive_ofSubmodules_iff]
  exact fun h ↦ bot_ne_top (h ⊥ fun _ ↦ le_rfl)

/-! ### The `ℓ`-adic filtration of `ℤ` -/

/-- The `ℓ`-adic filtration of `ℤ`: `F^p = ℓ^p ℤ` for `p ≥ 0`, and `ℤ` for `p ≤ 0`. -/
def adicStep (ℓ : ℤ) (p : ℤ) : Submodule ℤ ℤ :=
  Ideal.span {ℓ ^ p.toNat}

/-- An integer lies in the step `F^p` of the `ℓ`-adic filtration exactly when `ℓ^p` divides it
(with `ℓ^0 = 1` for `p ≤ 0`). -/
theorem mem_adicStep_iff {ℓ p x : ℤ} : x ∈ adicStep ℓ p ↔ ℓ ^ p.toNat ∣ x :=
  Ideal.mem_span_singleton

/-- The steps `F^p` of the `ℓ`-adic filtration with `p ≤ 0` are all of `ℤ`. -/
theorem adicStep_of_nonpos (ℓ : ℤ) {p : ℤ} (hp : p ≤ 0) : adicStep ℓ p = ⊤ := by
  rw [adicStep, Int.toNat_of_nonpos hp, pow_zero, Ideal.span_singleton_one]

/-- The `ℓ`-adic steps decrease. -/
theorem antitone_adicStep (ℓ : ℤ) : Antitone (adicStep ℓ) := fun p q hpq ↦ by
  rw [adicStep, adicStep, Ideal.span_singleton_le_span_singleton]
  exact pow_dvd_pow ℓ (Int.toNat_le_toNat hpq)

/-- The `ℓ`-adic filtration of `ℤ` as a decreasingly filtered `ℤ`-module. -/
noncomputable abbrev adicFiltration (ℓ : ℤ) : FilteredObject (ModuleCat.{0} ℤ) ℤᵒᵖ :=
  ofSubmodules (fun p ↦ adicStep ℓ p.unop) fun _ _ f ↦ antitone_adicStep ℓ (leOfHom f.unop)

/-- The `ℓ`-adic filtration of `ℤ` is exhaustive: its step `F^0` is `ℤ`. -/
theorem isExhaustive_adicFiltration (ℓ : ℤ) : (adicFiltration ℓ).IsExhaustive :=
  isExhaustive_of_step_eq_top _ (i := op (0 : ℤ)) (by
    rw [step_ofSubmodules, unop_op, adicStep_of_nonpos ℓ le_rfl, map_top])

/-- The `ℓ`-adic filtration of `ℤ`, for `|ℓ| ≠ 1`, is separated: an integer divisible by every
power of `ℓ` is `0`. -/
theorem isSeparated_adicFiltration {ℓ : ℤ} (hℓ : ℓ.natAbs ≠ 1) :
    (adicFiltration ℓ).IsSeparated := by
  refine (isSeparated_ofSubmodules_iff_forall_mem _ _).2 fun n hn ↦ ?_
  by_contra h0
  refine FiniteMultiplicity.not_iff_forall.2 (fun k ↦ ?_) (Int.finiteMultiplicity_iff.2 ⟨hℓ, h0⟩)
  have := hn (op (k : ℤ))
  rwa [unop_op, mem_adicStep_iff, Int.toNat_natCast] at this

/-- The partial sums `sₖ = ∑_{i < k} (-ℓ)^i` of the `ℓ`-adic expansion of `1 / (1 + ℓ)`. -/
private def adicPartialSum (ℓ : ℤ) (k : ℕ) : ℤ :=
  ∑ i ∈ Finset.range k, (-ℓ) ^ i

/-- `(1 + ℓ) sₖ = 1 - (-ℓ)^k`. -/
private theorem one_add_mul_adicPartialSum (ℓ : ℤ) (k : ℕ) :
    (1 + ℓ) * adicPartialSum ℓ k = 1 - (-ℓ) ^ k := by
  have := geom_sum_mul (-ℓ) k
  rw [adicPartialSum]
  linear_combination -this

/-- The partial sums are compatible: `ℓ^j ∣ s_k - s_j` for `j ≤ k`. -/
private theorem pow_dvd_adicPartialSum_sub (ℓ : ℤ) {j k : ℕ} (hjk : j ≤ k) :
    ℓ ^ j ∣ adicPartialSum ℓ k - adicPartialSum ℓ j := by
  rw [adicPartialSum, adicPartialSum, ← Finset.sum_range_add_sum_Ico _ hjk, add_sub_cancel_left]
  refine Finset.dvd_sum fun i hi ↦ ?_
  rw [neg_pow]
  exact Dvd.dvd.mul_left (pow_dvd_pow ℓ (Finset.mem_Ico.1 hi).1) _

/-- The `ℓ`-adic filtration of `ℤ`, for `ℓ ≥ 2`, is not complete: the partial sums of
`1 / (1 + ℓ) = ∑ (-ℓ)^i` form a compatible family of classes in the quotients `ℤ / ℓ^p`, which no
integer `n` represents, since `(1 + ℓ) n - 1` would be divisible by every power of `ℓ`. -/
theorem not_isComplete_adicFiltration {ℓ : ℤ} (hℓ : 2 ≤ ℓ) :
    ¬ (adicFiltration ℓ).IsComplete := by
  rw [FilteredObject.isComplete_iff]
  rintro ⟨hL⟩
  set s := adicPartialSum ℓ
  -- The maps `ℤ ⟶ ℤ`, `1 ↦ sₖ`, into the vertex of the cone of quotients.
  let g (k : ℕ) : ModuleCat.of ℤ ℤ ⟶ (adicFiltration ℓ).quotientCone.pt :=
    ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ ℤ (s k))
  let c : Limits.Cone (adicFiltration ℓ).quotientDiagram :=
    { pt := ModuleCat.of ℤ ℤ
      π :=
        { app p := g p.unop.toNat ≫ (adicFiltration ℓ).quotientCone.π.app p
          naturality p q f := by
            simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp,
              Category.assoc, Limits.Cone.w]
            rw [quotientCone_π_app]
            refine (comp_cokernel_π_stepι_ofSubmodules_eq_iff (fun p : ℤᵒᵖ ↦ adicStep ℓ p.unop) _ q
              (g _) (g _)).2 fun a ↦ ?_
            have h : s q.unop.toNat - s p.unop.toNat ∈ adicStep ℓ q.unop := by
              rw [mem_adicStep_iff, ← dvd_neg, neg_sub]
              exact pow_dvd_adicPartialSum_sub ℓ (Int.toNat_le_toNat (leOfHom f.unop))
            simp only [g, ModuleCat.hom_ofHom, LinearMap.toSpanSingleton_apply, ← smul_sub]
            exact Submodule.smul_mem _ a h } }
  -- The vertex `quotientCone.pt` of the cone of quotients is the filtered module `X`
  -- (`quotientCone_pt`, which holds by unfolding `quotientCone`).
  let φ : ModuleCat.of ℤ ℤ ⟶ (adicFiltration ℓ).X := hL.lift c
  set n : ℤ := φ.hom (1 : ℤ)
  have hdvd (k : ℕ) : ℓ ^ k ∣ (1 + ℓ) * n - 1 := by
    -- The leg of `c` at `op k` is `g k` followed by the projection, as `(k : ℤ).toNat = k`; the
    -- rewrite closes this by `rfl`.
    have hfac : hL.lift c ≫ (adicFiltration ℓ).quotientCone.π.app (op (k : ℤ)) =
        g k ≫ (adicFiltration ℓ).quotientCone.π.app (op (k : ℤ)) := by
      rw [hL.fac c (op (k : ℤ))]
    rw [quotientCone_π_app] at hfac
    have h' := (comp_cokernel_π_stepι_ofSubmodules_eq_iff (fun p : ℤᵒᵖ ↦ adicStep ℓ p.unop) _
      (op (k : ℤ)) φ (g k)).1 hfac 1
    simp only [g, ModuleCat.hom_ofHom, LinearMap.toSpanSingleton_apply, one_smul] at h'
    rw [mem_adicStep_iff, Int.toNat_natCast] at h'
    have : (1 + ℓ) * n - 1 = (1 + ℓ) * (n - s k) - (-ℓ) ^ k := by
      have := one_add_mul_adicPartialSum ℓ k
      linear_combination this
    rw [this, neg_pow]
    exact dvd_sub (h'.mul_left _) (dvd_mul_left _ _)
  have h1 : (1 + ℓ) * n = 1 := by
    by_contra h0
    exact FiniteMultiplicity.not_iff_forall.2 hdvd
      (Int.finiteMultiplicity_iff.2 ⟨by omega, sub_ne_zero.2 h0⟩)
  rcases Int.eq_one_or_neg_one_of_mul_eq_one h1 with h | h <;> omega

end TauCeti.Examples.DecreasingFiltration
