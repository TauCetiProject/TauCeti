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
along `W` (`ContinuousLinearMap.leftInverseAlong`).

This file studies an operator `[L B] : E × G → F`, `(x, σ) ↦ L x + B σ`, obtained by adding to `L`
a second block `B : G →L[R] F`, in which `L` acts on fast variables `x` and `B` on slow variables
`σ`. Solving for the fast variables reduces `[L B]` to the **reduced operator**
`Π ∘ B : G →L[R] W`, the slow block followed by the projection onto the complement of the range
of `L`. The reduction loses nothing:

* every vector splits as `y = L (K y) + Π y`
  (`ContinuousLinearMap.apply_leftInverseAlong_add_projectionOntoL`), and `y ↦ (P y, Π y)` is a
  continuous linear equivalence `F ≃L[R] Y × W`
  (`ContinuousLinearMap.equivProdKerOfIsInvertibleComp`); this is the inverse of Mathlib's
  splitting `Submodule.prodEquivOfIsTopCompl` along the range of `L` and `W`, with the range of
  `L` identified with `Y` through `P`;
* `L x + B σ = 0` exactly when `x = -K (B σ)` and `Π (B σ) = 0`
  (`ContinuousLinearMap.coprod_apply_eq_zero_iff_of_isInvertible_comp`), so the kernel of `[L B]`
  is the kernel of the reduced operator, through `(x, σ) ↦ σ` with inverse
  `σ ↦ (-K (B σ), σ)` (`ContinuousLinearMap.kerCoprodEquivOfIsInvertibleComp`);
* `y` lies in the range of `[L B]` exactly when `Π y` lies in the range of the reduced operator
  (`ContinuousLinearMap.mem_range_coprod_iff_of_isInvertible_comp`), so `Π` identifies the
  cokernels (`ContinuousLinearMap.quotientRangeCoprodEquivOfIsInvertibleComp`);
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

/-! ### The splitting of the target -/

/-- **The splitting of the target.** If `P ∘ L` is invertible, every `y` is the sum of
`L ((P ∘ L)⁻¹ P y)` in the range of `L` and its projection onto `ker P` along that range. -/
theorem apply_leftInverseAlong_add_projectionOntoL (h : (P ∘L L).IsInvertible) (y : F) :
    L (leftInverseAlong L P y) +
        (P.ker.projectionOntoL L.range (isTopCompl_range_ker_of_isInvertible_comp h).symm y :
          F) = y := by
  rw [Submodule.coe_projectionOntoL_apply, ← id_sub_comp_leftInverseAlong_eq_projectionL h]
  simp

/-- The projection onto `ker P` along the range of `L` vanishes on the range of `L`. -/
@[simp]
theorem projectionOntoL_apply_eq_zero_of_isInvertible_comp (h : (P ∘L L).IsInvertible) (x : E) :
    P.ker.projectionOntoL L.range (isTopCompl_range_ker_of_isInvertible_comp h).symm (L x) = 0 :=
  Submodule.projectionOntoL_apply_right _ ⟨L x, LinearMap.mem_range_self _ x⟩

/-- On the range of `L`, that is on the kernel of the projection onto `ker P` along it,
`L ∘ (P ∘ L)⁻¹ P` is the identity. -/
theorem apply_leftInverseAlong_eq_self_of_projectionOntoL_eq_zero (h : (P ∘L L).IsInvertible)
    {y : F}
    (hy : P.ker.projectionOntoL L.range (isTopCompl_range_ker_of_isInvertible_comp h).symm y = 0) :
    L (leftInverseAlong L P y) = y := by
  simpa [hy] using apply_leftInverseAlong_add_projectionOntoL h y

/-- **The target as a product.** If `P ∘ L` is invertible, `y ↦ (P y, Π y)`, with `Π` the
projection onto `ker P` along the range of `L`, is a continuous linear equivalence
`F ≃L[R] Y × ker P`. Its inverse is `(u, w) ↦ L ((P ∘ L)⁻¹ u) + w`. -/
noncomputable def equivProdKerOfIsInvertibleComp (h : (P ∘L L).IsInvertible) :
    F ≃L[R] Y × P.ker :=
  .ofContinuousLinearMap
    (P.prod (P.ker.projectionOntoL L.range (isTopCompl_range_ker_of_isInvertible_comp h).symm))
    ((L ∘L (P ∘L L).inverse).coprod P.ker.subtypeL)
    (by
      have hPL (u : Y) : P (L ((P ∘L L).inverse u)) = u := by simpa using h.self_apply_inverse u
      ext u <;> simp [hPL])
    (by
      ext y
      simpa [leftInverseAlong_apply] using apply_leftInverseAlong_add_projectionOntoL h y)

@[simp]
theorem equivProdKerOfIsInvertibleComp_apply (h : (P ∘L L).IsInvertible) (y : F) :
    equivProdKerOfIsInvertibleComp h y =
      (P y, P.ker.projectionOntoL L.range (isTopCompl_range_ker_of_isInvertible_comp h).symm y) :=
  (rfl)

@[simp]
theorem equivProdKerOfIsInvertibleComp_symm_apply (h : (P ∘L L).IsInvertible) (u : Y)
    (w : P.ker) :
    (equivProdKerOfIsInvertibleComp h).symm (u, w) = L ((P ∘L L).inverse u) + w :=
  (rfl)

/-! ### Kernel and range of `[L B]` -/

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

/-- **The kernel of `[L B]` is that of the reduced operator.** If `P ∘ L` is invertible, the
kernel of `(x, σ) ↦ L x + B σ` is identified with the kernel of `Π ∘ B`, for the projection `Π`
onto `ker P` along the range of `L`, by `(x, σ) ↦ σ`; the inverse is `σ ↦ (-(P ∘ L)⁻¹ P (B σ), σ)`.
-/
noncomputable def kerCoprodEquivOfIsInvertibleComp (h : (P ∘L L).IsInvertible) :
    (L.coprod B).ker ≃L[R]
      (P.ker.projectionOntoL L.range (isTopCompl_range_ker_of_isInvertible_comp h).symm ∘L
        B).ker :=
  .ofContinuousLinearMap
    ((snd R E G ∘L (L.coprod B).ker.subtypeL).codRestrict _ fun v ↦
      LinearMap.mem_ker.2 ((coprod_apply_eq_zero_iff_of_isInvertible_comp h).1
        (LinearMap.mem_ker.1 v.property)).2)
    ((((leftInverseAlong L P ∘L (-B)).prod (.id R G)) ∘L
        (P.ker.projectionOntoL L.range (isTopCompl_range_ker_of_isInvertible_comp h).symm ∘L
          B).ker.subtypeL).codRestrict _ fun σ ↦
      LinearMap.mem_ker.2 ((coprod_apply_eq_zero_iff_of_isInvertible_comp h).2
        ⟨map_neg (leftInverseAlong L P) _, LinearMap.mem_ker.1 σ.property⟩))
    (ContinuousLinearMap.ext fun _ ↦ rfl)
    (ContinuousLinearMap.ext fun v ↦ Subtype.ext (Prod.ext ((map_neg _ _).trans
      ((coprod_apply_eq_zero_iff_of_isInvertible_comp h).1
        (LinearMap.mem_ker.1 v.property)).1.symm) rfl))

theorem coe_kerCoprodEquivOfIsInvertibleComp_apply (h : (P ∘L L).IsInvertible)
    (v : (L.coprod B).ker) :
    (kerCoprodEquivOfIsInvertibleComp h v : G) = (v : E × G).2 := by
  rw [kerCoprodEquivOfIsInvertibleComp, ContinuousLinearEquiv.coe_ofContinuousLinearMap]
  rfl

theorem coe_kerCoprodEquivOfIsInvertibleComp_symm_apply (h : (P ∘L L).IsInvertible)
    (σ : (P.ker.projectionOntoL L.range (isTopCompl_range_ker_of_isInvertible_comp h).symm ∘L
      B).ker) :
    ((kerCoprodEquivOfIsInvertibleComp h).symm σ : E × G) =
      (-leftInverseAlong L P (B σ), (σ : G)) := by
  rw [kerCoprodEquivOfIsInvertibleComp, ContinuousLinearEquiv.symm_ofContinuousLinearMap,
    ContinuousLinearEquiv.coe_ofContinuousLinearMap]
  exact Prod.ext (map_neg (leftInverseAlong L P) _) rfl

/-- **The range of `[L B]`.** If `P ∘ L` is invertible, `y` lies in the range of
`(x, σ) ↦ L x + B σ` exactly when its projection onto `ker P` along the range of `L` lies in the
range of the reduced operator `Π ∘ B`. -/
theorem mem_range_coprod_iff_of_isInvertible_comp (h : (P ∘L L).IsInvertible) {y : F} :
    y ∈ (L.coprod B).range ↔
      P.ker.projectionOntoL L.range (isTopCompl_range_ker_of_isInvertible_comp h).symm y ∈
        (P.ker.projectionOntoL L.range (isTopCompl_range_ker_of_isInvertible_comp h).symm ∘L
          B).range := by
  constructor
  · rintro ⟨⟨x, σ⟩, rfl⟩
    exact ⟨σ, by simp⟩
  · rintro ⟨σ, hσ⟩
    refine ⟨(leftInverseAlong L P (y - B σ), σ), ?_⟩
    have hy : P.ker.projectionOntoL L.range (isTopCompl_range_ker_of_isInvertible_comp h).symm
        (y - B σ) = 0 := by
      rw [map_sub, sub_eq_zero]
      exact hσ.symm
    rw [coe_coe, coprod_apply, apply_leftInverseAlong_eq_self_of_projectionOntoL_eq_zero h hy,
      sub_add_cancel]

/-- **The cokernel of `[L B]` is that of the reduced operator.** If `P ∘ L` is invertible, the
projection `Π` onto `ker P` along the range of `L` induces a linear equivalence between the
cokernel of `(x, σ) ↦ L x + B σ` and the cokernel of `Π ∘ B`. -/
noncomputable def quotientRangeCoprodEquivOfIsInvertibleComp (h : (P ∘L L).IsInvertible) :
    (F ⧸ (L.coprod B).range) ≃ₗ[R]
      P.ker ⧸ (P.ker.projectionOntoL L.range (isTopCompl_range_ker_of_isInvertible_comp h).symm ∘L
        B).range :=
  (Submodule.quotEquivOfEq (L.coprod B).range
      (LinearMap.ker ((P.ker.projectionOntoL L.range
          (isTopCompl_range_ker_of_isInvertible_comp h).symm ∘L B).range.mkQ ∘ₗ
        (P.ker.projectionOntoL L.range (isTopCompl_range_ker_of_isInvertible_comp h).symm :
          F →ₗ[R] P.ker))) (by
      ext y
      simp only [LinearMap.mem_ker, LinearMap.coe_comp, Function.comp_apply,
        Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, coe_coe]
      exact mem_range_coprod_iff_of_isInvertible_comp h)).trans
    (LinearMap.quotKerEquivOfSurjective
      ((P.ker.projectionOntoL L.range (isTopCompl_range_ker_of_isInvertible_comp h).symm ∘L
        B).range.mkQ ∘ₗ
          (P.ker.projectionOntoL L.range (isTopCompl_range_ker_of_isInvertible_comp h).symm :
            F →ₗ[R] P.ker))
      ((Submodule.mkQ_surjective _).comp (Submodule.projectionOntoL_surjective _)))

theorem quotientRangeCoprodEquivOfIsInvertibleComp_mk (h : (P ∘L L).IsInvertible) (y : F) :
    quotientRangeCoprodEquivOfIsInvertibleComp (B := B) h (Submodule.Quotient.mk y) =
      Submodule.Quotient.mk
        (P.ker.projectionOntoL L.range (isTopCompl_range_ker_of_isInvertible_comp h).symm y) :=
  (rfl)

/-- **The index of `[L B]` is that of the reduced operator.** If `P ∘ L` is invertible, the
operator `(x, σ) ↦ L x + B σ` and the reduced operator `Π ∘ B` have isomorphic kernels and
cokernels, so they have the same index. No finiteness is assumed: when a kernel or cokernel is
infinite-dimensional, both indices take the same junk value. -/
theorem index_coprod_of_isInvertible_comp (h : (P ∘L L).IsInvertible) :
    (L.coprod B).index =
      (P.ker.projectionOntoL L.range (isTopCompl_range_ker_of_isInvertible_comp h).symm ∘L
        B).index := by
  rw [index_eq_finrank_sub, index_eq_finrank_sub,
    (kerCoprodEquivOfIsInvertibleComp h).toLinearEquiv.finrank_eq,
    (quotientRangeCoprodEquivOfIsInvertibleComp h).finrank_eq]

/-- `[L B]` is injective exactly when the reduced operator `Π ∘ B` is. -/
theorem injective_coprod_iff_of_isInvertible_comp (h : (P ∘L L).IsInvertible) :
    Injective (L.coprod B) ↔
      Injective (P.ker.projectionOntoL L.range
        (isTopCompl_range_ker_of_isInvertible_comp h).symm ∘L B) := by
  simp only [← coe_coe, ← LinearMap.ker_eq_bot, ← Submodule.subsingleton_iff_eq_bot]
  exact (kerCoprodEquivOfIsInvertibleComp h).toEquiv.subsingleton_congr

/-- `[L B]` is surjective exactly when the reduced operator `Π ∘ B` is. -/
theorem surjective_coprod_iff_of_isInvertible_comp (h : (P ∘L L).IsInvertible) :
    Surjective (L.coprod B) ↔
      Surjective (P.ker.projectionOntoL L.range
        (isTopCompl_range_ker_of_isInvertible_comp h).symm ∘L B) := by
  refine ⟨fun hs w ↦ ?_, fun hs y ↦ ?_⟩
  · obtain ⟨σ, hσ⟩ := (mem_range_coprod_iff_of_isInvertible_comp (B := B) h).1
      (LinearMap.range_eq_top.2 hs ▸ Submodule.mem_top (x := (w : F)))
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
