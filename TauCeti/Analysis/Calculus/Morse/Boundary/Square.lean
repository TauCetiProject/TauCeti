/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Morse.Boundary.Basic
import TauCeti.Analysis.Calculus.Morse.Stable

/-!
# The square of the mod-two Morse boundary counts broken trajectories

For critical points `p` and `r` whose Morse indices differ by two, a *broken trajectory* from `p`
to `r` is a pair of trajectories, from `p` to a critical point `q` of the intermediate index and
from `q` to `r`. Representing each component by its point on the middle level between its
endpoints, the broken trajectories form the set `TauCeti.morseBrokenTrajectorySet` of triples
`(q, z₁, z₂)`.

Under the compact-sublevel and Morse--Smale hypotheses of the mod-two Morse boundary `∂`, this
set is finite, and the `r`-coefficient of `∂ (∂ p)` is its cardinality modulo two. Consequently
`∂ ∘ ∂ = 0` holds exactly when every set of broken index-two trajectories has even cardinality.
This isolates the algebraic half of `∂² = 0`; the geometric half, that broken trajectories are
the boundary of a compact one-dimensional manifold of trajectories and therefore come in pairs,
requires the compactification and gluing of index-two trajectory spaces and is not proved here.

## Main declarations

* `TauCeti.morseBoundaryCoeff_eq_ncard`: for consecutive indices, the boundary coefficient is the
  parity of the middle-level trajectory slice, with no condition on the critical values.
* `TauCeti.morseBrokenTrajectorySet`: the broken index-two trajectories from `p` to `r`.
* `TauCeti.finite_morseBrokenTrajectorySet_of_isCompact_sublevel`: there are finitely many.
* `TauCeti.morseBoundary_morseBoundaryOnGenerator_apply`: the coefficients of `∂ (∂ p)` count
  broken trajectories modulo two.
* `TauCeti.morseBoundary_comp_morseBoundary_eq_zero_iff`: `∂ ∘ ∂ = 0` exactly when every set of
  broken trajectories has even cardinality.

## Reference

M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
Chapter 4 (the Morse complex): the proof that `∂ ∘ ∂ = 0` counts the coefficient of `r` in
`∂ (∂ p)` as the number of broken trajectories from `p` to `r`.
-/

public section

open Set
open scoped Gradient NNReal

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {f : E → ℝ} {K : ℝ≥0}

/-- The broken index-two trajectories from `p` to `r`: triples `(q, z₁, z₂)` of a critical
point `q` whose Morse index lies one below that of `p` and one above that of `r`, a point `z₁`
on the middle-level slice of trajectories from `p` to `q`, and a point `z₂` on the middle-level
slice of trajectories from `q` to `r`. -/
noncomputable def morseBrokenTrajectorySet (hf : LipschitzWith K (∇ f)) (p r : E) :
    Set (MorseCriticalPoint f × E × E) :=
  {x | morseIndex f p = morseIndex f x.1 + 1 ∧ morseIndex f x.1 = morseIndex f r + 1 ∧
    x.2.1 ∈ morseTrajectorySlice hf p x.1 ∧ x.2.2 ∈ morseTrajectorySlice hf x.1 r}

/-- Membership in the set of broken index-two trajectories. -/
@[simp]
theorem mem_morseBrokenTrajectorySet {hf : LipschitzWith K (∇ f)} {p r : E}
    {x : MorseCriticalPoint f × E × E} :
    x ∈ morseBrokenTrajectorySet hf p r ↔
      morseIndex f p = morseIndex f x.1 + 1 ∧ morseIndex f x.1 = morseIndex f r + 1 ∧
        x.2.1 ∈ morseTrajectorySlice hf p x.1 ∧ x.2.2 ∈ morseTrajectorySlice hf x.1 r :=
  Iff.rfl

/-- A point of the middle-level slice between distinct endpoints forces the critical value to
drop strictly. -/
theorem value_lt_of_mem_morseTrajectorySlice (hfd : Differentiable ℝ f)
    {hf : LipschitzWith K (∇ f)} {p q z : E} (hpq : p ≠ q)
    (hz : z ∈ morseTrajectorySlice hf p q) :
    f q < f p := by
  rw [mem_morseTrajectorySlice] at hz
  exact (isNegativeGradient_negativeGradientFlow f hf).value_lt_of_mem_unstableSet_inter_stableSet
    (fun _ ↦ hfd.differentiableAt) hfd.continuous.continuousAt hfd.continuous.continuousAt hpq
    ⟨hz.1, hz.2.1⟩

/-- The intermediate critical point of a broken trajectory has strictly smaller critical value
than its source. -/
theorem value_lt_of_mem_morseBrokenTrajectorySet (hfd : Differentiable ℝ f)
    {hf : LipschitzWith K (∇ f)} {p r : E} {x : MorseCriticalPoint f × E × E}
    (hx : x ∈ morseBrokenTrajectorySet hf p r) :
    f x.1 < f p := by
  have hpq : p ≠ x.1 := fun h ↦ by simp [h] at hx
  exact value_lt_of_mem_morseTrajectorySlice hfd hpq hx.2.2.1

/-- The broken trajectories through a fixed intermediate critical point `q` are the products of
the two middle-level slices, tagged by `q`. -/
private theorem sep_morseBrokenTrajectorySet_fst_eq {hf : LipschitzWith K (∇ f)} {p r : E}
    (q : MorseCriticalPoint f) (hpq : morseIndex f p = morseIndex f q + 1)
    (hqr : morseIndex f q = morseIndex f r + 1) :
    {x ∈ morseBrokenTrajectorySet hf p r | x.1 = q} =
      (fun z ↦ (q, z)) '' (morseTrajectorySlice hf p q ×ˢ morseTrajectorySlice hf q r) := by
  ext ⟨q', z₁, z₂⟩
  constructor
  · rintro ⟨⟨-, -, h₁, h₂⟩, rfl⟩
    exact ⟨(z₁, z₂), ⟨h₁, h₂⟩, rfl⟩
  · rintro ⟨⟨z₁', z₂'⟩, ⟨h₁, h₂⟩, h⟩
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨⟨hpq, hqr, h₁, h₂⟩, rfl⟩

/-- Without the intermediate index, there are no broken trajectories through `q`. -/
private theorem sep_morseBrokenTrajectorySet_fst_eq_empty {hf : LipschitzWith K (∇ f)}
    {p r : E} (q : MorseCriticalPoint f)
    (hind : ¬(morseIndex f p = morseIndex f q + 1 ∧ morseIndex f q = morseIndex f r + 1)) :
    {x ∈ morseBrokenTrajectorySet hf p r | x.1 = q} = ∅ :=
  eq_empty_of_forall_notMem fun _ ⟨hx, hxq⟩ ↦ hind (hxq ▸ ⟨hx.1, hx.2.1⟩)

/-- There are finitely many broken index-two trajectories between two critical points, under
the compact-sublevel and Morse--Smale hypotheses of the Morse boundary. -/
theorem finite_morseBrokenTrajectorySet_of_isCompact_sublevel
    (hfs : ContDiff ℝ 2 f) (hf : LipschitzWith K (∇ f))
    (hM : HasNondegenerateCriticalPointsOn f univ)
    (hcompact : ∀ c : ℝ, IsCompact {z | f z ≤ c})
    (htr : IsMorseSmale f hf)
    (p r : MorseCriticalPoint f) :
    (morseBrokenTrajectorySet hf p r).Finite := by
  have hfd : Differentiable ℝ f := hfs.differentiable (by norm_num)
  -- For consecutive indices a slice is finite: empty unless the critical value drops.
  have hslice : ∀ {a b : MorseCriticalPoint f}, morseIndex f a = morseIndex f b + 1 →
      (morseTrajectorySlice hf a b).Finite := fun {a b} hind ↦ by
    by_cases hba : f b < f a
    · exact finite_morseTrajectorySlice_of_isCompact_sublevel hfs hf hM hcompact
        a.isNondegenerate b.isNondegenerate hind hba htr
    · have hab : (a : E) ≠ b := fun h ↦ by simp [h] at hind
      exact finite_empty.subset fun z hz ↦
        hba (value_lt_of_mem_morseTrajectorySlice hfd hab hz)
  refine ((finite_setOf_value_le_of_isCompact_sublevel hfs hM hcompact (f p)).biUnion fun q _ ↦
    (?_ : {x ∈ morseBrokenTrajectorySet hf p r | x.1 = q}.Finite)).subset fun x hx ↦
      mem_biUnion (x := x.1) (value_lt_of_mem_morseBrokenTrajectorySet hfd hx).le ⟨hx, rfl⟩
  by_cases hind : morseIndex f p = morseIndex f q + 1 ∧ morseIndex f q = morseIndex f r + 1
  · rw [sep_morseBrokenTrajectorySet_fst_eq q hind.1 hind.2]
    exact ((hslice hind.1).prod (hslice hind.2)).image _
  · rw [sep_morseBrokenTrajectorySet_fst_eq_empty q hind]
    exact finite_empty

section Boundary

variable (hfs : ContDiff ℝ 2 f) (hf : LipschitzWith K (∇ f))
  (hM : HasNondegenerateCriticalPointsOn f univ)
  (hcompact : ∀ c : ℝ, IsCompact {z | f z ≤ c})
  (htr : IsMorseSmale f hf)

/-- For critical points of consecutive index, the boundary coefficient is the cardinality of the
middle-level trajectory slice modulo two. No comparison of critical values is needed: when the
value does not drop, the slice is empty. -/
theorem morseBoundaryCoeff_eq_ncard {p q : MorseCriticalPoint f}
    (hind : morseIndex f p = morseIndex f q + 1) :
    morseBoundaryCoeff hfs hf hM hcompact htr p q =
      ((morseTrajectorySlice hf p q).ncard : ZMod 2) := by
  by_cases hqp : f q < f p
  · rw [morseBoundaryCoeff_eq_trajectoryCount hfs hf hM hcompact htr p q hind hqp,
      morseTrajectoryCount_eq_ncard]
  · have hpq : (p : E) ≠ q := fun h ↦ by simp [h] at hind
    have hempty : morseTrajectorySlice hf p q = ∅ :=
      eq_empty_of_forall_notMem fun z hz ↦
        hqp (value_lt_of_mem_morseTrajectorySlice (hfs.differentiable (by norm_num)) hpq hz)
    rw [morseBoundaryCoeff_eq_zero_of_value_le hfs hf hM hcompact htr p q (not_lt.mp hqp),
      hempty, ncard_empty, Nat.cast_zero]

/-- The `r`-coefficient of the boundary of the boundary of `p` is the number of broken
index-two trajectories from `p` to `r`, modulo two. -/
theorem morseBoundary_morseBoundaryOnGenerator_apply (p r : MorseCriticalPoint f) :
    morseBoundary hfs hf hM hcompact htr (morseBoundaryOnGenerator hfs hf hM hcompact htr p) r =
      ((morseBrokenTrajectorySet hf p r).ncard : ZMod 2) := by
  classical
  have hT := finite_setOf_value_le_of_isCompact_sublevel hfs hM hcompact (f p)
  have hfin := finite_morseBrokenTrajectorySet_of_isCompact_sublevel hfs hf hM hcompact htr p r
  have hsupp : (morseBoundaryOnGenerator hfs hf hM hcompact htr p).support ⊆ hT.toFinset :=
    fun q hq ↦ hT.mem_toFinset.mpr
      (value_lt_of_mem_support_morseBoundaryOnGenerator hfs hf hM hcompact htr hq).le
  have hfst : ∀ x ∈ hfin.toFinset, x.1 ∈ hT.toFinset := fun x hx ↦
    hT.mem_toFinset.mpr (value_lt_of_mem_morseBrokenTrajectorySet
      (hfs.differentiable (by norm_num)) (hfin.mem_toFinset.mp hx)).le
  rw [morseBoundary_apply, Finsupp.sum_of_support_subset _ hsupp
      (fun q a ↦ a * morseBoundaryCoeff hfs hf hM hcompact htr q r) fun _ _ ↦ zero_mul _,
    ncard_eq_toFinset_card _ hfin, Finset.card_eq_sum_card_fiberwise hfst, Nat.cast_sum]
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  rw [morseBoundaryOnGenerator_apply, ← ncard_coe_finset, Finset.coe_filter]
  simp only [Finite.mem_toFinset]
  by_cases hind : morseIndex f p = morseIndex f q + 1 ∧ morseIndex f q = morseIndex f r + 1
  · rw [sep_morseBrokenTrajectorySet_fst_eq q hind.1 hind.2,
      ncard_image_of_injective _ (Prod.mk_right_injective q), ncard_prod, Nat.cast_mul,
      morseBoundaryCoeff_eq_ncard hfs hf hM hcompact htr hind.1,
      morseBoundaryCoeff_eq_ncard hfs hf hM hcompact htr hind.2]
  · rw [sep_morseBrokenTrajectorySet_fst_eq_empty q hind, ncard_empty, Nat.cast_zero]
    rcases not_and_or.mp hind with h | h
    · rw [morseBoundaryCoeff_eq_zero_of_morseIndex_ne_add_one hfs hf hM hcompact htr p q h,
        zero_mul]
    · rw [morseBoundaryCoeff_eq_zero_of_morseIndex_ne_add_one hfs hf hM hcompact htr q r h,
        mul_zero]

/-- The mod-two Morse boundary squares to zero exactly when, between any two critical points,
the number of broken index-two trajectories is even. -/
theorem morseBoundary_comp_morseBoundary_eq_zero_iff :
    morseBoundary hfs hf hM hcompact htr ∘ₗ morseBoundary hfs hf hM hcompact htr = 0 ↔
      ∀ p r : MorseCriticalPoint f, Even (morseBrokenTrajectorySet hf p r).ncard := by
  simp_rw [← ZMod.natCast_eq_zero_iff_even,
    ← morseBoundary_morseBoundaryOnGenerator_apply hfs hf hM hcompact htr]
  constructor
  · intro h p r
    simpa using DFunLike.congr_fun (LinearMap.congr_fun h (Finsupp.single p 1)) r
  · intro h
    refine Finsupp.lhom_ext fun p a ↦ Finsupp.ext fun r ↦ ?_
    simp [h]

end Boundary

end TauCeti

end
