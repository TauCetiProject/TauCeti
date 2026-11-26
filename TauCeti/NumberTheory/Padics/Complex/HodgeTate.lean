/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Cyclotomic.CyclotomicCharacter
public import TauCeti.NumberTheory.Padics.Complex.GaloisAction

import TauCeti.NumberTheory.Padics.Complex.FixedPoints
import TauCeti.NumberTheory.Padics.Complex.TateTwist

/-!
# Twisted-stable subspaces of `ℂ_p^ι`

Let `G_{ℚ_p} = Gal(PadicAlgCl p / ℚ_p)` act on `ℂ_p`, let `χ` be the cyclotomic character, and let
`u : ι → ℤ` be weights on a finite set `ι`. Then `G_{ℚ_p}` acts semilinearly on `ℂ_p^ι` by
`g ⋆ a = (χ(g) ^ u i · g(a i))_i`: this is the direct sum of the Tate twists `ℂ_p(u i)`.

This file shows that every `ℂ_p`-subspace `W` of `ℂ_p^ι` stable under this action is spanned by
vectors of a special shape: vectors with coordinates in `PadicAlgCl p` of norm at most `1`, equal
to `1` at some coordinate `k`, vanishing at the coordinates `i` with `u i ≠ u k`, and fixed by the
untwisted Galois action. Stability is only asked along a filter `F` on `G_{ℚ_p}` whose members
are neighbourhoods of `1`: for each `a ∈ W`, `g ⋆ a ∈ W` for `F`-almost all `g`, and the spanning
vectors are then fixed by `F`-almost all `g`. Taking `F = ⊤` asks for stability under the whole
group, and `F = 𝓝 1` for stability under the elements of a neighbourhood of `1` that may depend
on `a`. In particular a nonzero stable subspace contains a vector of this shape.

Each spanning vector has a single weight, so `W` is the sum of its intersections with the
summands of `ℂ_p^ι` of a single weight, each spanned by vectors with coordinates in
`PadicAlgCl p`: this is a form of the Hodge–Tate decomposition. It rests on Tate's theorem that
no nonzero `x ∈ ℂ_p` has `χ(g) ^ u g(x) = χ(g) ^ v x` for all `g` near `1` when `u ≠ v`
(`PadicComplex.eq_zero_of_eventually_cyclotomicCharacter_zpow_mul_smul_eq`), and on the
Ax–Sen–Tate theorem that the elements of `ℂ_p` fixed near `1` are algebraic
(`PadicComplex.mem_range_coe_iff_eventually_smul_eq`).

## Main results

* `PadicComplex.eq_span_of_forall_eventually_cyclotomicCharacter_zpow_mul_smul_mem`: a subspace of
  `ℂ_p^ι` stable under the twisted action along `F` is spanned by its algebraic, integral vectors
  of a single weight fixed by `F`-almost all `g`.

## References

* J. Tate, *p-divisible groups*, Proceedings of a Conference on Local Fields (Driebergen, 1966),
  Springer, 1967, §3.
* J.-P. Serre, *Groupes algébriques associés aux modules de Hodge–Tate*, Astérisque 65 (1979).

The argument on vectors of minimal support follows the method of
`New.Period.le_of_hodgeTate_stable` (`src/Lib/PadicHodge/TateSen.lean`) of grh-lean
(https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic, PBC).
-/

public section

open Topology Filter

namespace PadicComplex

variable {p : ℕ} [hp : Fact p.Prime] {ι : Type*} [Finite ι] {u : ι → ℤ}
  {F : Filter (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)} {W : Submodule ℂ_[p] (ι → ℂ_[p])}

omit [Finite ι] in
/-- If `a ∈ W` takes the value `1` at `k` and no nonzero vector of `W` has support strictly inside
that of `a`, then for `F`-almost all `g` the twisted translate of `a` is `χ(g) ^ u k • a`. -/
private theorem eventually_cyclotomicCharacter_zpow_mul_smul_eq
    (hW : ∀ a ∈ W, ∀ᶠ g in F, (fun i ↦ algebraMap ℚ_[p] ℂ_[p]
      (((cyclotomicCharacter (PadicAlgCl p) p g.toRingEquiv ^ u i : ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p]) *
        g • a i) ∈ W)
    {a : ι → ℂ_[p]} (ha : a ∈ W) {k : ι} (hak : a k = 1)
    (hmin : ∀ b ∈ W, Function.support b ⊂ Function.support a → b = 0) :
    ∀ᶠ g in F, ∀ i, algebraMap ℚ_[p] ℂ_[p]
        (((cyclotomicCharacter (PadicAlgCl p) p g.toRingEquiv ^ u i : ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p]) *
          g • a i =
      algebraMap ℚ_[p] ℂ_[p]
        (((cyclotomicCharacter (PadicAlgCl p) p g.toRingEquiv ^ u k : ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p]) *
          a i := by
  filter_upwards [hW a ha] with g hg
  set c : ℤ → ℂ_[p] := fun n ↦ algebraMap ℚ_[p] ℂ_[p]
    (((cyclotomicCharacter (PadicAlgCl p) p g.toRingEquiv ^ n : ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p])
  -- The difference `b` of the twisted translate and `χ(g) ^ u k • a` vanishes at `k` and outside
  -- the support of `a`, so it is `0` by minimality.
  set b : ι → ℂ_[p] := (fun i ↦ c (u i) * g • a i) - c (u k) • a
  have hb : b = 0 := by
    refine hmin b (W.sub_mem hg (W.smul_mem _ ha)) ((Set.ssubset_iff_of_subset fun i hi ↦ ?_).2
      ⟨k, by simp [hak], by simp [b, hak]⟩)
    contrapose hi
    simp [b, Function.notMem_support.mp hi]
  intro i
  simpa [b, sub_eq_zero] using congrFun hb i

/-- If, for `F`-almost all `g`, the twisted translate of `a` is `χ(g) ^ u k • a`, then `a` is fixed
by `F`-almost all `g`, and its coordinates are algebraic and vanish where `u i ≠ u k`. -/
private theorem eventually_smul_eq_and_forall_mem_range_coe (hF : 𝓝 1 ≤ F) {a : ι → ℂ_[p]}
    {k : ι}
    (ha : ∀ᶠ g in F, ∀ i, algebraMap ℚ_[p] ℂ_[p]
        (((cyclotomicCharacter (PadicAlgCl p) p g.toRingEquiv ^ u i : ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p]) *
          g • a i =
      algebraMap ℚ_[p] ℂ_[p]
        (((cyclotomicCharacter (PadicAlgCl p) p g.toRingEquiv ^ u k : ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p]) *
          a i) :
    (∀ᶠ g in F, g • a = a) ∧
      ∀ i, a i ∈ Set.range ((↑) : PadicAlgCl p → ℂ_[p]) ∧ (u i ≠ u k → a i = 0) := by
  -- Coordinates of weight `u k` are fixed by `F`-almost all `g`; the others vanish by Tate.
  have hzero (i : ι) (hi : u i ≠ u k) : a i = 0 :=
    eq_zero_of_eventually_cyclotomicCharacter_zpow_mul_smul_eq hi
      ((ha.mono fun g hg ↦ hg i).filter_mono hF)
  have hfix (i : ι) : ∀ᶠ g in F, g • a i = a i := by
    by_cases hi : u i = u k
    · filter_upwards [ha] with g hg
      exact mul_left_cancel₀ (by simp) (hi ▸ hg i)
    · simp [hzero i hi]
  refine ⟨(eventually_all.mpr hfix).mono fun g hg ↦ funext hg, fun i ↦ ⟨?_, hzero i⟩⟩
  exact mem_range_coe_iff_eventually_smul_eq.mpr ((hfix i).filter_mono hF)

/-- **Hodge–Tate decomposition of twisted-stable subspaces.** Let `ι` be finite, `u : ι → ℤ`, and
`F` a filter on `Gal(PadicAlgCl p / ℚ_p)` each of whose members is a neighbourhood of `1` (for
instance `⊤`, `𝓝 1`, or the principal filter of an open subgroup). Let `W ⊆ ℂ_p^ι` be a
`ℂ_p`-subspace such that for every `a ∈ W` the vector `(χ(g) ^ u i · g(a i))_i` lies in `W` for
`F`-almost all `g`. Then `W` is spanned by its vectors `a` fixed by `F`-almost all `g` such that,
for some `k`: `a k = 1`, and every coordinate `a i` lies in `PadicAlgCl p`, has norm at most `1`,
and vanishes unless `u i = u k`. -/
theorem eq_span_of_forall_eventually_cyclotomicCharacter_zpow_mul_smul_mem (hF : 𝓝 1 ≤ F)
    (hW : ∀ a ∈ W, ∀ᶠ g in F, (fun i ↦ algebraMap ℚ_[p] ℂ_[p]
      (((cyclotomicCharacter (PadicAlgCl p) p g.toRingEquiv ^ u i : ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p]) *
        g • a i) ∈ W) :
    W = Submodule.span ℂ_[p] {a | a ∈ W ∧ (∀ᶠ g in F, g • a = a) ∧ ∃ k, a k = 1 ∧
      ∀ i, a i ∈ Set.range ((↑) : PadicAlgCl p → ℂ_[p]) ∧ ‖a i‖ ≤ 1 ∧ (u i ≠ u k → a i = 0)} := by
  induction W using WellFoundedLT.induction with | ind W ih => ?_
  refine le_antisymm (fun w hw ↦ ?_) (Submodule.span_le.mpr fun a ha ↦ ha.1)
  obtain rfl | hW0 := eq_or_ne W ⊥
  · rw [(Submodule.mem_bot _).mp hw]
    exact zero_mem _
  -- A nonzero vector `a₀ ∈ W` of minimal support, and a coordinate `k` where `‖a₀ k‖` is largest.
  obtain ⟨a₀, ⟨ha₀W, ha₀⟩, hmin⟩ := (measure fun b : ι → ℂ_[p] ↦ b.support.ncard).wf.has_min
    {b | b ∈ W ∧ b ≠ 0} (by simpa [Set.Nonempty, Submodule.ne_bot_iff] using hW0)
  obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp ha₀
  have : Nonempty ι := ⟨i₀⟩
  obtain ⟨k, hk⟩ := Finite.exists_max fun i ↦ ‖a₀ i‖
  have hk0 : a₀ k ≠ 0 := norm_pos_iff.mp ((norm_pos_iff.mpr hi₀).trans_le (hk i₀))
  -- The vector `a = (a₀ k)⁻¹ • a₀` has the required shape.
  set a := (a₀ k)⁻¹ • a₀
  have haW : a ∈ W := W.smul_mem _ ha₀W
  have hak : a k = 1 := by simp [a, hk0]
  have hsupp : a.support = a₀.support := Function.support_const_smul_of_ne_zero _ _ (by simpa)
  have hmin' (b : ι → ℂ_[p]) (hb : b ∈ W) (hba : b.support ⊂ a.support) : b = 0 := by
    by_contra hb0
    exact hmin b ⟨hb, hb0⟩ (Set.ncard_lt_ncard (hsupp ▸ hba))
  obtain ⟨hfix, halg⟩ := eventually_smul_eq_and_forall_mem_range_coe hF
    (eventually_cyclotomicCharacter_zpow_mul_smul_eq hW haW hak hmin')
  have hnorm (i : ι) : ‖a i‖ ≤ 1 := by
    simpa [a, norm_inv] using inv_mul_le_one_of_le₀ (hk i) (norm_nonneg _)
  -- The vectors of `W` vanishing at `k` form a smaller stable subspace `W'`, and
  -- `w = w k • a + (w - w k • a)` with `w - w k • a ∈ W'`.
  set W' := W ⊓ LinearMap.ker (LinearMap.proj k : (ι → ℂ_[p]) →ₗ[ℂ_[p]] ℂ_[p])
  have hW'W : W' < W := inf_le_left.lt_of_ne fun h ↦ by
    simpa [W', hak] using h.ge haW
  have hW' := ih W' hW'W fun b hb ↦ by
    have hbk : b k = 0 := by simpa using (Submodule.mem_inf.mp hb).2
    filter_upwards [hW b (Submodule.mem_inf.mp hb).1] with g hg
    exact Submodule.mem_inf.mpr ⟨hg, by simp [hbk]⟩
  have hw' : w - w k • a ∈ W' :=
    Submodule.mem_inf.mpr ⟨W.sub_mem hw (W.smul_mem _ haW), by simp [hak]⟩
  rw [← sub_add_cancel w (w k • a)]
  refine add_mem ?_ (Submodule.smul_mem _ _ (Submodule.subset_span
    ⟨haW, hfix, k, hak, fun i ↦ ⟨(halg i).1, hnorm i, (halg i).2⟩⟩))
  rw [hW'] at hw'
  refine Submodule.span_mono ?_ hw'
  rintro b ⟨hb, hb'⟩
  exact ⟨(Submodule.mem_inf.mp hb).1, hb'⟩

end PadicComplex
