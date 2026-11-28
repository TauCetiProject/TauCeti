/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.ApproximateUnit
public import TauCeti.Analysis.Normed.Module.CohenFactorization.Basic
import TauCeti.Topology.ApproximateUnit

/-!
# Cohen–Hewitt factorization for right modules and pseudo-unital bimodules

This is the right-module and bimodule companion of the left-module Cohen–Hewitt theorem
`ContinuousLinearMap.exists_apply_eq_of_mem_essentialSubmodule` of
`TauCeti.Analysis.Normed.Module.CohenFactorization.Basic`, and it reuses that theorem rather than
repeating its construction.

Let `A` be a possibly nonunital Banach algebra over `𝕜` and `E` a Banach space. A *bounded right
action* of `A` on `E` is a bounded bilinear map `R : E →L[𝕜] A →L[𝕜] E` with
`R (R x a) b = R x (a * b)`, written `x · a = R x a`; it need not be contractive or unital. The
*essential part* of a right module is `R.flip.essentialSubmodule`, the closed linear span of
`E · A`. A Banach bimodule carries a bounded left action `L` and a bounded right action `R` with
`R (L a z) b = L a (R z b)`, and it is essential when `E = essentialBimoduleSubmodule L R.flip`.

## Main results

* `ContinuousLinearMap.exists_apply_eq_of_mem_essentialSubmodule_right`: Cohen–Hewitt
  factorization for right modules. A right approximate identity of `A` bounded by `C` factors
  every `x` in `R.flip.essentialSubmodule` as `x = y · a` with `‖a‖ ≤ C`, where `y` lies in the
  closure of `x · A` and within any prescribed distance `ε` of `x`.
* `ContinuousLinearMap.coe_essentialSubmodule_eq_range_right`: consequently `E · A` is
  already a closed linear subspace: it equals `R.flip.essentialSubmodule`.
* `ContinuousLinearMap.exists_apply_apply_eq_of_mem_essentialBimoduleSubmodule`: essential
  bimodules over an algebra with a bounded two-sided approximate identity are pseudo-unital, so
  every element of `essentialBimoduleSubmodule L R.flip` is a single triple product `a · z · b`.

## Implementation notes

The right-module statement is obtained from the left-module one by transporting the action to the
opposite algebra `Aᵐᵒᵖ`, where `a · z = z · a.unop`, so the Cohen–Hewitt construction is not
repeated; the bimodule statement is then one application of each of the two one-sided theorems.

## References

* H. G. Dales, *Banach Algebras and Automatic Continuity*, §2.9; the one-sided factorization is
  Theorem 2.9.24 there.
* E. Hewitt, *The ranges of certain convolution operators*, Math. Scand. 15 (1964), 147–155.
* P. J. Cohen, *Factorization in group algebras*, Duke Math. J. 26 (1959), 199–205.
-/

public section

open Filter Submodule Topology

namespace ContinuousLinearMap

variable {𝕜 A E : Type*} [RCLike 𝕜] [NonUnitalNormedRing A] [NormedSpace 𝕜 A]
  [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A] [CompleteSpace A]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]

/-- **Cohen–Hewitt factorization for right modules.** Let `A` be a Banach algebra with a right
approximate identity `l` bounded by `C`, acting boundedly on the right of a Banach space `E`
through `R`. Every `x` in the essential part `R.flip.essentialSubmodule` factors as `x = R y a`
with `‖a‖ ≤ C`, where `y` lies in the closure of `x · A` and within any prescribed distance `ε` of
`x`. -/
theorem exists_apply_eq_of_mem_essentialSubmodule_right (R : E →L[𝕜] A →L[𝕜] E)
    (hR : ∀ x a b, R (R x a) b = R x (a * b)) {l : Filter A} [l.NeBot] {C : ℝ}
    (hC : ∀ᶠ e in l, ‖e‖ ≤ C) (hl : ∀ a, Tendsto (a * ·) l (𝓝 a)) {x : E}
    (hx : x ∈ R.flip.essentialSubmodule) {ε : ℝ} (hε : 0 < ε) :
    ∃ a y, ‖a‖ ≤ C ∧ y ∈ closure (Set.range fun b ↦ R x b) ∧ ‖y - x‖ < ε ∧ R y a = x := by
  -- The opposite algebra acts on the left by `a · z = z · a.unop`.
  let Lop : Aᵐᵒᵖ →L[𝕜] E →L[𝕜] E := R.flip.compUnop
  have hLop' : ∀ (a b : Aᵐᵒᵖ) (z : E), Lop (a * b) z = Lop a (Lop b z) := by
    intro a b z
    simp only [Lop, compUnop_apply, flip_apply, MulOpposite.unop_mul]
    exact (hR z b.unop a.unop).symm
  have hx' : x ∈ Lop.essentialSubmodule := by
    simpa [Lop] using hx
  obtain ⟨a, y, ha, hy, hdist, hfac⟩ :=
    exists_apply_eq_of_mem_essentialSubmodule Lop hLop' (l := l.map MulOpposite.op)
      (Filter.eventually_map.2 hC) (TauCeti.tendsto_mul_right_map_op hl) hx' hε
  refine ⟨a.unop, y, by rw [MulOpposite.norm_unop]; exact ha, ?_, hdist,
    by simpa only [Lop, compUnop_apply, flip_apply] using hfac⟩
  have hset : Set.range (fun b : Aᵐᵒᵖ ↦ Lop b x) = Set.range fun b : A ↦ R x b := by
    simpa only [Lop, compUnop_apply, flip_apply, Function.comp_def] using
      MulOpposite.unop_surjective.range_comp (fun b : A ↦ R x b)
  rwa [hset] at hy

/-- Over a Banach algebra with a bounded right approximate identity, the set `E · A` of products
is already a closed linear subspace of a Banach right module `E`: it equals
`R.flip.essentialSubmodule`. -/
theorem coe_essentialSubmodule_eq_range_right (R : E →L[𝕜] A →L[𝕜] E)
    (hR : ∀ x a b, R (R x a) b = R x (a * b)) {l : Filter A} [l.NeBot] {C : ℝ}
    (hC : ∀ᶠ e in l, ‖e‖ ≤ C) (hl : ∀ a, Tendsto (a * ·) l (𝓝 a)) :
    (R.flip.essentialSubmodule : Set E) = Set.range fun p : E × A ↦ R p.1 p.2 := by
  refine subset_antisymm (fun x hx ↦ ?_) fun _ ⟨p, hp⟩ ↦
    hp ▸ R.flip.apply_mem_essentialSubmodule p.2 p.1
  obtain ⟨a, y, -, -, -, h⟩ :=
    exists_apply_eq_of_mem_essentialSubmodule_right R hR hC hl hx one_pos
  exact ⟨(y, a), h⟩

/-- **Pseudo-unitality of essential Banach bimodules.** Let `A` be a Banach algebra with a
two-sided approximate identity `l` bounded by `C`, and let `E` be a Banach `A`-bimodule with
bounded actions `L` and `R`. Every element of `essentialBimoduleSubmodule L R.flip` is a single
triple product: `x = L a (R z b)` with `‖a‖ ≤ C` and `‖b‖ ≤ C`. -/
theorem exists_apply_apply_eq_of_mem_essentialBimoduleSubmodule (L : A →L[𝕜] E →L[𝕜] E)
    (R : E →L[𝕜] A →L[𝕜] E) (hL : ∀ a b z, L (a * b) z = L a (L b z))
    (hR : ∀ x a b, R (R x a) b = R x (a * b)) (hLR : ∀ a z b, R (L a z) b = L a (R z b))
    {l : Filter A} (hl : l.IsApproximateUnit) {C : ℝ} (hC : ∀ᶠ e in l, ‖e‖ ≤ C) {x : E}
    (hx : x ∈ essentialBimoduleSubmodule L R.flip) :
    ∃ a z b, ‖a‖ ≤ C ∧ ‖b‖ ≤ C ∧ L a (R z b) = x := by
  -- `IsApproximateUnit.neBot` is `protected`, so instance search does not reach it from `hl` and
  -- `l.NeBot` has to be added to the context by hand: without this line the one-sided theorems
  -- below cannot synthesize `l.NeBot`.
  have hlneBot : l.NeBot := hl.neBot
  have hLR' : ∀ a b z, L a (R.flip b z) = R.flip b (L a z) := fun a b z ↦ (hLR a z b).symm
  have hxR : x ∈ R.flip.essentialSubmodule := essentialBimoduleSubmodule_le_right hLR' hx
  -- The distance bounds of the two one-sided theorems are discarded, so `ε = 1` will do.
  obtain ⟨b, y, hb, hy, -, hRyb⟩ :=
    exists_apply_eq_of_mem_essentialSubmodule_right R hR hC hl.tendsto_mul_left hxR one_pos
  -- The intermediate point stays in the bimodule essential part, being a multiple of `x`.
  have hyS : y ∈ essentialBimoduleSubmodule L R.flip := by
    refine (isClosed_essentialBimoduleSubmodule L R.flip).closure_subset_iff.2 ?_ hy
    rintro _ ⟨c, rfl⟩
    exact apply_right_mem_essentialBimoduleSubmodule (L := L) (R := R.flip)
      (fun a b z ↦ (hR z a b).symm) hLR' c hx
  have hyL : y ∈ L.essentialSubmodule := essentialBimoduleSubmodule_le_left L R.flip hyS
  obtain ⟨a, z, ha, -, -, hLaz⟩ :=
    exists_apply_eq_of_mem_essentialSubmodule L hL hC hl.tendsto_mul_right hyL one_pos
  refine ⟨a, z, b, ha, hb, ?_⟩
  rw [← hLR a z b, hLaz, hRyb]

end ContinuousLinearMap
