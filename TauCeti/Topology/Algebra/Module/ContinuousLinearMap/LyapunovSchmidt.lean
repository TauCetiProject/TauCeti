/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Index
public import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.LeftInverse

/-!
# The linear Lyapunov–Schmidt reduction

Let `L : E →L[R] F` be an operator and `P : F →L[R] Y` an auxiliary operator with `P ∘ L`
invertible. Then `W = ker P` is a topological complement of the range of `L`
(`ContinuousLinearMap.isTopCompl_range_ker_of_isInvertible_comp`), with the projection
`Π : F →L[R] W` onto `W` along the range of `L`, and `K = (P ∘ L)⁻¹ P` is the left inverse of `L`
along `W` (`ContinuousLinearMap.leftInverseAlong`). Every vector splits as `y = L (K y) + Π y`
(`ContinuousLinearMap.apply_leftInverseAlong_add_projectionOntoL`), so the continuous linear
equivalence `y ↦ (P y, Π y) : F ≃L[R] Y × W` is Mathlib's
`ContinuousLinearEquiv.equivOfRightInverse` for `P` and its right inverse `L ∘ (P ∘ L)⁻¹`
(`ContinuousLinearMap.snd_equivOfRightInverse_eq_projectionOntoL`). These facts about `L` and `P`
alone are in `TauCeti.Topology.Algebra.Module.ContinuousLinearMap.LeftInverse`.

This file studies an operator `[L B] : E × G → F`, `(x, σ) ↦ L x + B σ`, obtained by adding to `L`
a second block `B : G →L[R] F`, in which `L` acts on fast variables `x` and `B` on slow variables
`σ`. Solving for the fast variables reduces `[L B]` to the **reduced operator**
`Π ∘ B : G →L[R] W`, the slow block followed by the projection onto the complement of the range
of `L`. The reduction loses nothing. The map `i : σ ↦ (-K (B σ), σ)` and the inclusion `j` of
`ker P` satisfy `[L B] (i σ) = j (Π (B σ))`, and this commutative square has the regularity
property of Tau Ceti's API `LinearMap.kerEquivOfRegularity`, `LinearMap.cokerEquivOfRegularity`:

* `L x + B σ = 0` exactly when `x = -K (B σ)` and `Π (B σ) = 0`
  (`ContinuousLinearMap.coprod_apply_eq_zero_iff_of_isInvertible_comp`), so `i` identifies the
  kernel of the reduced operator with that of `[L B]`;
* `y` lies in the range of `[L B]` exactly when `Π y` lies in the range of the reduced operator
  (`ContinuousLinearMap.mem_range_coprod_iff_of_isInvertible_comp`), and `j` identifies the
  cokernels;
* consequently `[L B]` and the reduced operator have the same index
  (`ContinuousLinearMap.index_coprod_of_isInvertible_comp`);
* hence `[L B]` is injective, respectively surjective, exactly when the reduced operator is
  (`ContinuousLinearMap.injective_coprod_iff_of_isInvertible_comp`,
  `ContinuousLinearMap.surjective_coprod_iff_of_isInvertible_comp`), and a right inverse `Q` of
  the reduced operator gives the right inverse
  `y ↦ (K (y - B (Q (Π y))), Q (Π y))` of `[L B]`
  (`ContinuousLinearMap.coprod_comp_prod_eq_id_of_isInvertible_comp`).

This is the linear algebra behind a Lyapunov–Schmidt reduction of a nonlinear equation
`S(x, σ) = 0` whose derivative in the fast variables is injective with complemented range: the
linearization `[L B]` of the full problem and the linearization `Π ∘ B` of the reduced problem
have the same kernel and cokernel, so the reduced problem is Fredholm with the same index exactly
when the full one is (`ContinuousLinearMap.isFredholm_coprod_iff_of_isInvertible_comp`, in
`TauCeti.Analysis.Fredholm.SchurComplement`), and surjectivity, together with an explicit right
inverse, passes from the reduced problem back to the full one. The reduced operator depends on
`P` only through its kernel `W`.

## References

* M. Golubitsky and D. G. Schaeffer, *Singularities and Groups in Bifurcation Theory*, Vol. I,
  Springer, 1985 (the Liapunov–Schmidt reduction).
* C. H. Taubes, *Gr ⇒ SW: from pseudo-holomorphic curves to Seiberg–Witten solutions*,
  J. Differential Geom. 51 (1999), 203–334.
-/

public section

namespace ContinuousLinearMap

open Function

variable {R E F G Y : Type*} [Ring R]
  [AddCommGroup E] [TopologicalSpace E] [Module R E]
  [AddCommGroup F] [TopologicalSpace F] [Module R F] [IsTopologicalAddGroup F]
  [AddCommGroup G] [TopologicalSpace G] [Module R G]
  [AddCommGroup Y] [TopologicalSpace Y] [Module R Y]
  {L : E →L[R] F} {P : F →L[R] Y}

/-! ### Kernel, range, cokernel and index of `[L B]` -/

variable {B : G →L[R] F}

/-- **The Lyapunov–Schmidt reduction of `[L B]`.** If `P ∘ L` is invertible, then
`L x + B σ = 0` exactly when `x = -(P ∘ L)⁻¹ P (B σ)` and the projection of `B σ` onto `ker P`
along the range of `L` vanishes. -/
theorem coprod_apply_eq_zero_iff_of_isInvertible_comp (h : (P ∘L L).IsInvertible) {x : E}
    {σ : G} :
    L.coprod B (x, σ) = 0 ↔ x = -leftInverseAlong L P (B σ) ∧
      P.ker.projectionOntoL L.range (isTopCompl_range_ker_of_isInvertible_comp h).symm (B σ) =
        0 := by
  rw [coprod_apply, apply_add_eq_zero_iff h, ← Submodule.coe_projectionOntoL_apply,
    ZeroMemClass.coe_eq_zero]

/-- The commutative square `[L B] (i σ) = j (Π (B σ))`, with `i σ = (-(P ∘ L)⁻¹ P (B σ), σ)` and
`j` the inclusion of `ker P`, fed to Tau Ceti's regularity API (`LinearMap.kerEquivOfRegularity`,
`LinearMap.cokerEquivOfRegularity`): it commutes, `i` is injective, it has the regularity
property, and the ranges of `[L B]` and `j` span `F`. -/
private theorem regularity_coprod_of_isInvertible_comp (h : (P ∘L L).IsInvertible) :
    (∀ σ, (L.coprod B : E × G →ₗ[R] F)
        ((leftInverseAlong L P ∘L (-B)).prod (.id R G) σ) =
      P.ker.subtype ((P.ker.projectionOntoL L.range
        (isTopCompl_range_ker_of_isInvertible_comp h).symm ∘L B : G →ₗ[R] P.ker) σ)) ∧
    Injective ((leftInverseAlong L P ∘L (-B)).prod (.id R G) : G →ₗ[R] E × G) ∧
    (∀ v w, (L.coprod B : E × G →ₗ[R] F) v = P.ker.subtype w →
      ∃ σ, ((leftInverseAlong L P ∘L (-B)).prod (.id R G) : G →ₗ[R] E × G) σ = v) ∧
    LinearMap.range (L.coprod B : E × G →ₗ[R] F) ⊔ LinearMap.range P.ker.subtype = ⊤ := by
  refine ⟨fun σ ↦ ?_, fun σ τ hστ ↦ congr_arg Prod.snd hστ, fun ⟨x, σ⟩ w hw ↦ ⟨σ, ?_⟩, ?_⟩
  · simpa using apply_neg_leftInverseAlong_add_eq_projectionL h (B σ)
  · have hx := w.property
    rw [← Submodule.subtype_apply, ← hw, coe_coe, coprod_apply] at hx
    simp [(apply_add_mem_ker_iff (x := x) (S := B σ) h).1 hx]
  · rw [Submodule.range_subtype, eq_top_iff,
      ← (isTopCompl_range_ker_of_isInvertible_comp h).isCompl.sup_eq_top]
    refine sup_le_sup_right ?_ _
    rintro _ ⟨x, rfl⟩
    exact ⟨(x, 0), by simp⟩

/-- **The range of `[L B]`.** If `P ∘ L` is invertible, `y` lies in the range of
`(x, σ) ↦ L x + B σ` exactly when its projection onto `ker P` along the range of `L` lies in the
range of the reduced operator `Π ∘ B`. -/
theorem mem_range_coprod_iff_of_isInvertible_comp (h : (P ∘L L).IsInvertible) {y : F} :
    y ∈ (L.coprod B).range ↔
      P.ker.projectionOntoL L.range (isTopCompl_range_ker_of_isInvertible_comp h).symm y ∈
        (P.ker.projectionOntoL L.range (isTopCompl_range_ker_of_isInvertible_comp h).symm ∘L
          B).range := by
  obtain ⟨hcomm, -, hreg, -⟩ := regularity_coprod_of_isInvertible_comp (B := B) h
  have hL : L (leftInverseAlong L P y) ∈ (L.coprod B).range :=
    ⟨(leftInverseAlong L P y, 0), by simp⟩
  rw [← LinearMap.comap_range_eq_range_of_regularity hcomm P.ker.injective_subtype hreg,
    Submodule.mem_comap, Submodule.subtype_apply]
  conv_lhs => rw [← apply_leftInverseAlong_add_projectionOntoL h y]
  exact Submodule.add_mem_iff_right _ hL

/-- **The index of `[L B]` is that of the reduced operator.** If `P ∘ L` is invertible, the
operator `(x, σ) ↦ L x + B σ` and the reduced operator `Π ∘ B` have isomorphic kernels and
cokernels (`LinearMap.kerEquivOfRegularity`, `LinearMap.cokerEquivOfRegularity`), so they have
the same index. No finiteness is assumed: when a kernel or cokernel is infinite-dimensional,
both indices take the same junk value. -/
theorem index_coprod_of_isInvertible_comp (h : (P ∘L L).IsInvertible) :
    (L.coprod B).index =
      (P.ker.projectionOntoL L.range (isTopCompl_range_ker_of_isInvertible_comp h).symm ∘L
        B).index := by
  obtain ⟨hcomm, hi, hreg, hsup⟩ := regularity_coprod_of_isInvertible_comp (B := B) h
  rw [index_def, index_def]
  exact (LinearMap.index_eq_of_regularity hcomm hi P.ker.injective_subtype hreg hsup).symm

/-- `[L B]` is injective exactly when the reduced operator `Π ∘ B` is. -/
theorem injective_coprod_iff_of_isInvertible_comp (h : (P ∘L L).IsInvertible) :
    Injective (L.coprod B) ↔
      Injective (P.ker.projectionOntoL L.range
        (isTopCompl_range_ker_of_isInvertible_comp h).symm ∘L B) := by
  obtain ⟨hcomm, hi, hreg, -⟩ := regularity_coprod_of_isInvertible_comp (B := B) h
  simp only [← coe_coe, ← LinearMap.ker_eq_bot, ← Submodule.subsingleton_iff_eq_bot]
  exact (LinearMap.kerEquivOfRegularity hcomm hi P.ker.injective_subtype
    hreg).toEquiv.subsingleton_congr.symm

/-- `[L B]` is surjective exactly when the reduced operator `Π ∘ B` is. -/
theorem surjective_coprod_iff_of_isInvertible_comp (h : (P ∘L L).IsInvertible) :
    Surjective (L.coprod B) ↔
      Surjective (P.ker.projectionOntoL L.range
        (isTopCompl_range_ker_of_isInvertible_comp h).symm ∘L B) := by
  refine ⟨fun hs w ↦ ?_, fun hs y ↦ ?_⟩
  · obtain ⟨σ, hσ⟩ := (mem_range_coprod_iff_of_isInvertible_comp (B := B) h).1 (hs w)
    exact ⟨σ, hσ.trans (Submodule.projectionOntoL_apply_left _ w)⟩
  · exact (mem_range_coprod_iff_of_isInvertible_comp h).2 (hs _)

/-- **A right inverse of `[L B]` from one of the reduced operator.** If `P ∘ L` is invertible and
`Q` is a right inverse of the reduced operator `Π ∘ B`, then
`y ↦ ((P ∘ L)⁻¹ P (y - B (Q (Π y))), Q (Π y))` is a right inverse of `(x, σ) ↦ L x + B σ`. -/
theorem coprod_comp_prod_eq_id_of_isInvertible_comp (h : (P ∘L L).IsInvertible)
    {Q : P.ker →L[R] G}
    (hQ : (P.ker.projectionOntoL L.range (isTopCompl_range_ker_of_isInvertible_comp h).symm ∘L
      B) ∘L Q = .id R P.ker) :
    L.coprod B ∘L
        ((leftInverseAlong L P ∘L (.id R F - B ∘L Q ∘L
            P.ker.projectionOntoL L.range (isTopCompl_range_ker_of_isInvertible_comp h).symm)).prod
          (Q ∘L P.ker.projectionOntoL L.range
            (isTopCompl_range_ker_of_isInvertible_comp h).symm)) =
      .id R F := by
  ext y
  have hy : P.ker.projectionOntoL L.range (isTopCompl_range_ker_of_isInvertible_comp h).symm
      (y - B (Q (P.ker.projectionOntoL L.range
        (isTopCompl_range_ker_of_isInvertible_comp h).symm y))) = 0 := by
    rw [map_sub, sub_eq_zero]
    exact congr($hQ _).symm
  simp only [comp_apply, prod_apply, coprod_apply, sub_apply, id_apply]
  rw [apply_leftInverseAlong_eq_self_of_projectionOntoL_eq_zero h hy, sub_add_cancel]

/-- **A right inverse of the reduced operator from one of `[L B]`.** If `P ∘ L` is invertible and
`Q` is a right inverse of `(x, σ) ↦ L x + B σ`, then `w ↦ (Q w).2` is a right inverse of the
reduced operator `Π ∘ B`. -/
theorem comp_snd_comp_eq_id_of_isInvertible_comp (h : (P ∘L L).IsInvertible) {Q : F →L[R] E × G}
    (hQ : L.coprod B ∘L Q = .id R F) :
    (P.ker.projectionOntoL L.range (isTopCompl_range_ker_of_isInvertible_comp h).symm ∘L B) ∘L
        (snd R E G ∘L Q ∘L P.ker.subtypeL) =
      .id R P.ker := by
  ext w
  have hw : L (Q w).1 + B (Q w).2 = w := by simpa using congr($hQ (w : F))
  have := congrArg
    (P.ker.projectionOntoL L.range (isTopCompl_range_ker_of_isInvertible_comp h).symm) hw
  rw [map_add, projectionOntoL_apply_eq_zero_of_isInvertible_comp h, zero_add,
    Submodule.projectionOntoL_apply_left] at this
  simp [this]

end ContinuousLinearMap
