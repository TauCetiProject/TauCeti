/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Homotopy.MappingPath.Fiber

/-!
# Concatenating loops onto the mapping-path fibre

A point of the mapping-path fibre `MappingPathFiber f k` is a pair `(x, γ)` of a source point `x`
and a path `γ` on the unit interval from `f x` to `k`. A loop `ℓ` at `k` can be concatenated onto
the path, `(x, γ) ↦ (x, γ.trans ℓ)` (`TauCeti.MappingPathFiber.transLoop`), continuously in the
pair and the loop. This is the fixed-interval form of the action of the loops at `k` on the fibre.
It is not an action in general: concatenation of paths on the unit interval is associative and
unital only up to reparametrization. The Moore-path model of the same fibre,
`TauCeti.MooreReplacement.Fiber`, carries a strict action, and the two are compared in
`TauCeti.Topology.PathSpace.Moore.Replacement.MappingPathFiber`.

## Main definitions

* `TauCeti.MappingPathFiber.transLoop`: `((x, γ), ℓ) ↦ (x, γ.trans ℓ)`.

## References

* G. W. Whitehead, *Elements of Homotopy Theory*, GTM 61, Springer, 1978, Chapter I.7.
-/

public noncomputable section

open unitInterval

universe u v

namespace TauCeti.MappingPathFiber

variable {B : Type u} {K : Type v} [TopologicalSpace B] [TopologicalSpace K] (f : C(B, K)) (k : K)

/-- **Concatenation of loops onto the mapping-path fibre**: the path of `(x, γ)` followed by a loop
`ℓ` at `k`, `((x, γ), ℓ) ↦ (x, γ.trans ℓ)`, continuous in the pair and the loop. -/
def transLoop : C(MappingPathFiber f k × Path k k, MappingPathFiber f k) where
  toFun q := ⟨(q.1.val.1, ((toPath f k q.1).trans q.2).toContinuousMap), Path.source _,
    Path.target _⟩
  continuous_toFun := by
    refine ((continuous_subtypeVal.fst.comp continuous_fst).prodMk ?_).subtype_mk _
    apply ContinuousMap.continuous_of_continuous_uncurry
    have h : Continuous fun q : (MappingPathFiber f k × Path k k) × I ↦ toPath f k q.1.1 q.2 := by
      simp only [coe_toPath]
      exact ((continuous_subtypeVal.snd.comp continuous_fst).comp continuous_fst).eval
        continuous_snd
    exact Path.trans_continuous_family (fun q : MappingPathFiber f k × Path k k ↦ toPath f k q.1) h
      (fun q ↦ q.2) ((continuous_snd.comp continuous_fst).eval continuous_snd)

/-- Concatenating a loop keeps the source point. -/
@[simp]
theorem transLoop_val_fst (q : MappingPathFiber f k) (ℓ : Path k k) :
    (transLoop f k (q, ℓ)).val.1 = q.val.1 :=
  (rfl)

/-- The path of the concatenation is the path of `q` followed by the loop. -/
@[simp]
theorem transLoop_val_snd (q : MappingPathFiber f k) (ℓ : Path k k) :
    (transLoop f k (q, ℓ)).val.2 = ((toPath f k q).trans ℓ).toContinuousMap :=
  (rfl)

/-- The path of the concatenation, as a path from `f x` to `k`, is the path of `q` followed by
the loop. -/
@[simp]
theorem toPath_transLoop (q : MappingPathFiber f k) (ℓ : Path k k) :
    toPath f k (transLoop f k (q, ℓ)) =
      ((toPath f k q).trans ℓ).cast (congrArg f (transLoop_val_fst f k q ℓ)) rfl :=
  Path.ext <| by rw [coe_toPath, transLoop_val_snd, Path.cast_coe, Path.coe_toContinuousMap]

end TauCeti.MappingPathFiber
