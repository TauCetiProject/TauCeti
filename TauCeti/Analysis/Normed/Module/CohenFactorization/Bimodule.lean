/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.ApproximateUnit
public import TauCeti.Analysis.Normed.Module.CohenFactorization.Basic

/-!
# Cohen–Hewitt factorization for right modules and pseudo-unital bimodules

This is the right-module and bimodule companion of the left-module Cohen–Hewitt theorem
`ContinuousLinearMap.exists_apply_eq_of_mem_topologicalClosure_span` of
`TauCeti.Analysis.Normed.Module.CohenFactorization.Basic`, and it reuses that theorem rather than
repeating its construction.

Let `A` be a possibly nonunital Banach algebra over `𝕜` and `E` a Banach space. A *bounded right
action* of `A` on `E` is a bounded bilinear map `R : E →L[𝕜] A →L[𝕜] E` with
`R (R x a) b = R x (a * b)`, written `x · a = R x a`; it need not be contractive or unital. The
*essential part* of a right module is the closed linear span of `E · A`. A Banach bimodule
carries a bounded left action `L` and a bounded right action `R` with `R (L a z) b = L a (R z b)`,
and it is essential when `E = closure (span (A · E · A))`.

## Main results

* `ContinuousLinearMap.exists_apply_eq_of_mem_topologicalClosure_span_right`: Cohen–Hewitt
  factorization for right modules. A right approximate identity of `A` bounded by `C` factors
  every `x` in the essential part of `E` as `x = y · a` with `‖a‖ ≤ C`, where `y` lies in the
  closure of `x · A` and within any prescribed distance `ε` of `x`.
* `ContinuousLinearMap.coe_topologicalClosure_span_range_eq_right`: consequently `E · A` is
  already a closed linear subspace: it equals the essential part of a right module.
* `ContinuousLinearMap.exists_apply_apply_eq_of_mem_topologicalClosure_span`: essential
  bimodules over an algebra with a bounded two-sided approximate identity are pseudo-unital, so
  every element is a single triple product `a · z · b`.

## Implementation notes

The right-module statement is obtained from the left-module one by transporting the action to the
opposite algebra `Aᵐᵒᵖ`, where `a · z = z · a.unop`, so the Cohen–Hewitt construction is not
repeated; the bimodule statement is then one application of each of the two one-sided theorems.

## References

* H. G. Dales, *Banach Algebras and Automatic Continuity*, §2.9.
-/

public section

open Filter Submodule Topology

namespace ContinuousLinearMap

variable {𝕜 A E : Type*} [RCLike 𝕜] [NonUnitalNormedRing A] [NormedSpace 𝕜 A]
  [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A] [CompleteSpace A]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]

/-- **Cohen–Hewitt factorization for right modules.** Let `A` be a Banach algebra with a right
approximate identity `l` bounded by `C`, acting boundedly on the right of a Banach space `E`
through `R`. Every `x` in the essential part `closure (span (E · A))` factors as `x = R y a` with
`‖a‖ ≤ C`, where `y` lies in the closure of `x · A` and within any prescribed distance `ε` of
`x`. -/
theorem exists_apply_eq_of_mem_topologicalClosure_span_right (R : E →L[𝕜] A →L[𝕜] E)
    (hR : ∀ x a b, R (R x a) b = R x (a * b)) {l : Filter A} [l.NeBot] {C : ℝ}
    (hC : ∀ᶠ e in l, ‖e‖ ≤ C) (hl : ∀ a, Tendsto (a * ·) l (𝓝 a)) {x : E}
    (hx : x ∈ (span 𝕜 (Set.range fun p : E × A ↦ R p.1 p.2)).topologicalClosure)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ a y, ‖a‖ ≤ C ∧ y ∈ closure (Set.range fun b ↦ R x b) ∧ ‖y - x‖ < ε ∧ R y a = x := by
  -- The opposite algebra acts on the left by `a · z = z · a.unop`.
  obtain ⟨Lop, hLop⟩ :
      ∃ Lop : Aᵐᵒᵖ →L[𝕜] E →L[𝕜] E, ∀ (a : Aᵐᵒᵖ) (z : E), Lop a z = R z a.unop :=
    ⟨R.flip.comp (MulOpposite.opContinuousLinearEquiv 𝕜 (M := A)).symm.toContinuousLinearMap,
      fun a z ↦ rfl⟩
  have hLop' : ∀ (a b : Aᵐᵒᵖ) (z : E), Lop (a * b) z = Lop a (Lop b z) := by
    intro a b z
    simp only [hLop, MulOpposite.unop_mul]
    exact (hR z b.unop a.unop).symm
  have hC' : ∀ᶠ e in l.map MulOpposite.op, ‖e‖ ≤ C := by
    rw [Filter.eventually_map]
    exact hC
  have hl' : ∀ a : Aᵐᵒᵖ, Tendsto (· * a) (l.map MulOpposite.op) (𝓝 a) := by
    intro a
    rw [Filter.tendsto_map'_iff]
    have h : Tendsto (fun x : A ↦ MulOpposite.op (a.unop * x)) l (𝓝 (MulOpposite.op a.unop)) :=
      (MulOpposite.continuous_op.tendsto a.unop).comp (hl a.unop)
    have heq : (fun x : A ↦ MulOpposite.op (a.unop * x)) = fun x ↦ MulOpposite.op x * a := by
      funext x
      rw [MulOpposite.op_mul, MulOpposite.op_unop]
    rwa [heq, MulOpposite.op_unop] at h
  have hx' : x ∈ (span 𝕜 (Set.range fun p : Aᵐᵒᵖ × E ↦ Lop p.1 p.2)).topologicalClosure := by
    have hset : Set.range (fun p : Aᵐᵒᵖ × E ↦ Lop p.1 p.2) =
        Set.range fun p : E × A ↦ R p.1 p.2 := by
      ext z
      constructor
      · rintro ⟨⟨a, w⟩, rfl⟩
        exact ⟨(w, a.unop), (hLop a w).symm⟩
      · rintro ⟨⟨w, a⟩, rfl⟩
        exact ⟨(MulOpposite.op a, w), by simp [hLop]⟩
    rw [hset]
    exact hx
  obtain ⟨a, y, ha, hy, hdist, hfac⟩ :=
    exists_apply_eq_of_mem_topologicalClosure_span Lop hLop' hC' hl' hx' hε
  refine ⟨a.unop, y, by rw [MulOpposite.norm_unop]; exact ha, ?_, hdist,
    (hLop a y).symm.trans hfac⟩
  have hset : Set.range (fun b : Aᵐᵒᵖ ↦ Lop b x) = Set.range fun b : A ↦ R x b := by
    ext z
    constructor
    · rintro ⟨b, rfl⟩
      exact ⟨b.unop, by simp [hLop]⟩
    · rintro ⟨b, rfl⟩
      exact ⟨MulOpposite.op b, by simp [hLop]⟩
  rwa [hset] at hy

/-- Over a Banach algebra with a bounded right approximate identity, the set `E · A` of products
is already a closed linear subspace of a Banach right module `E`: it equals the essential part
`closure (span (E · A))`. -/
theorem coe_topologicalClosure_span_range_eq_right (R : E →L[𝕜] A →L[𝕜] E)
    (hR : ∀ x a b, R (R x a) b = R x (a * b)) {l : Filter A} [l.NeBot] {C : ℝ}
    (hC : ∀ᶠ e in l, ‖e‖ ≤ C) (hl : ∀ a, Tendsto (a * ·) l (𝓝 a)) :
    ((span 𝕜 (Set.range fun p : E × A ↦ R p.1 p.2)).topologicalClosure : Set E) =
      Set.range fun p : E × A ↦ R p.1 p.2 := by
  refine subset_antisymm (fun x hx ↦ ?_) ((subset_span).trans (le_topologicalClosure _))
  obtain ⟨a, y, -, -, -, h⟩ :=
    exists_apply_eq_of_mem_topologicalClosure_span_right R hR hC hl hx one_pos
  exact ⟨(y, a), h⟩

omit [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A] [CompleteSpace A] [CompleteSpace E] in
/-- Right multiplication by a fixed element preserves the essential part of a Banach bimodule,
`closure (span (A · E · A))`, because `(a · z · b) · c = a · z · (b * c)`. -/
private lemma image_flip_span_le (L : A →L[𝕜] E →L[𝕜] E) (R : E →L[𝕜] A →L[𝕜] E)
    (hR : ∀ x a b, R (R x a) b = R x (a * b)) (c : A) :
    (R.flip c) '' (span 𝕜 (Set.range fun p : A × E × A ↦ R (L p.1 p.2.1) p.2.2)) ⊆
      span 𝕜 (Set.range fun p : A × E × A ↦ R (L p.1 p.2.1) p.2.2) :=
  (Submodule.image_span_subset (R.flip c).toLinearMap _ _).2 fun u hu ↦ by
    obtain ⟨⟨a, z, b⟩, rfl⟩ := hu
    -- `image_span_subset` states its goal about the coerced `LinearMap` of `R.flip c`, so the
    -- operand is not syntactically a bundled-map application and rewriting by `hR` needs the
    -- goal restated in the bundled form first.
    change R (R (L a z) b) c ∈ span 𝕜 (Set.range fun p : A × E × A ↦ R (L p.1 p.2.1) p.2.2)
    rw [hR (L a z) b c]
    exact Submodule.subset_span ⟨(a, z, b * c), rfl⟩

/-- **Pseudo-unitality of essential Banach bimodules.** Let `A` be a Banach algebra with a
two-sided approximate identity `l` bounded by `C`, and let `E` be a Banach `A`-bimodule with
bounded actions `L` and `R`. Every element of the essential part `closure (span (A · E · A))` is a
single triple product: `x = L a (R z b)` with `‖a‖ ≤ C` and `‖b‖ ≤ C`. -/
theorem exists_apply_apply_eq_of_mem_topologicalClosure_span (L : A →L[𝕜] E →L[𝕜] E)
    (R : E →L[𝕜] A →L[𝕜] E) (hL : ∀ a b z, L (a * b) z = L a (L b z))
    (hR : ∀ x a b, R (R x a) b = R x (a * b)) (hLR : ∀ a z b, R (L a z) b = L a (R z b))
    {l : Filter A} (hl : l.IsApproximateUnit) {C : ℝ} (hC : ∀ᶠ e in l, ‖e‖ ≤ C) {x : E}
    (hx : x ∈ (span 𝕜 (Set.range fun p : A × E × A ↦ R (L p.1 p.2.1) p.2.2)).topologicalClosure) :
    ∃ a z b, ‖a‖ ≤ C ∧ ‖b‖ ≤ C ∧ L a (R z b) = x := by
  -- `IsApproximateUnit`'s `neBot` field is `protected`, so the properness of `l` has to be
  -- restated as a local instance for the one-sided theorems.
  have hlneBot : l.NeBot := hl.neBot
  -- The essential part of the bimodule, whose elements are the triple products `a · z · b`.
  set S : Submodule 𝕜 E := span 𝕜 (Set.range fun p : A × E × A ↦ R (L p.1 p.2.1) p.2.2)
  -- `A · E · A` is contained in both one-sided essential parts.
  have hAE : S ≤ span 𝕜 (Set.range fun p : A × E ↦ L p.1 p.2) := by
    rw [Submodule.span_le]
    rintro _ ⟨⟨a, z, b⟩, rfl⟩
    simp only [hLR a z b]
    exact Submodule.subset_span ⟨(a, R z b), rfl⟩
  have hEA : S ≤ span 𝕜 (Set.range fun p : E × A ↦ R p.1 p.2) := by
    rw [Submodule.span_le]
    rintro _ ⟨⟨a, z, b⟩, rfl⟩
    exact Submodule.subset_span ⟨(L a z, b), rfl⟩
  -- The distance bounds of the two one-sided theorems are discarded, so `ε = 1` will do.
  obtain ⟨b, y, hb, hy, -, hRyb⟩ :=
    exists_apply_eq_of_mem_topologicalClosure_span_right R hR hC
      hl.tendsto_mul_left (Submodule.topologicalClosure_mono hEA hx) one_pos
  -- The intermediate point stays in the bimodule essential part, being a multiple of `x`.
  have hyS : y ∈ S.topologicalClosure := by
    refine closure_minimal ?_ isClosed_closure hy
    intro w hw
    obtain ⟨c, rfl⟩ := hw
    exact closure_mono (image_flip_span_le L R hR c)
      (image_closure_subset_closure_image (R.flip c).continuous
        (Set.mem_image_of_mem (R.flip c) hx))
  obtain ⟨a, z, ha, -, -, hLaz⟩ :=
    exists_apply_eq_of_mem_topologicalClosure_span L hL hC
      hl.tendsto_mul_right (Submodule.topologicalClosure_mono hAE hyS) one_pos
  refine ⟨a, z, b, ha, hb, ?_⟩
  rw [← hLR a z b, hLaz, hRyb]

end ContinuousLinearMap
