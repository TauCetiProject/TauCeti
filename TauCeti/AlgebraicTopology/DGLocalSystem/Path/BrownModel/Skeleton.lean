/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Module.Filtration
public import TauCeti.Algebra.Homology.DG.Twisted.RowFinite.Filtration
public import TauCeti.AlgebraicTopology.DGLocalSystem.Path.BrownModel.Fibration
public import TauCeti.AlgebraicTopology.DGLocalSystem.Path.Skeleton

/-!
# The skeletal filtrations of the fibration comparison of a Brown model

Let `B` be a CW complex with a point `b`, `p : E → B` a continuous map, and `M` a Brown model at
`b` (`TauCeti.BrownModel`): a semi-free twisting cocycle `m` over the chains `C_*(Ω_b B)` on the
Moore loops at `b`, on generators `P` graded by `ind`, with a quasi-isomorphism
`g : K_m → C_*(P_b B)` onto the chains on the Moore paths from `b`. Its fibration comparison
(`TauCeti.BrownModel.fibrationComparison`)

`Ψ : C_*(F'_b) ⊗_{C_*(Ω_b B)} K_m → C_*(E')`,  `σ ⊗ x ↦ append_*(σ × g(x))`,

goes from the twisted complex of `m` with coefficients in the DG local system of `p` to the chains
on the total space `E'` of the Moore-path replacement of `p`. Both sides are filtered by the
skeleta of `B`:

* the twisted complex by the indices of the generators, the cell filtration
  `TauCeti.rowFiniteIndexFiltration`, which is exhaustive and, for generators of nonnegative index,
  zero in degree `-1`;
* the chains on `E'` by the chains supported over the preimages of the skeleta under the end point
  map `E' → B`, the filtration whose spectral sequence is the Serre spectral sequence of the
  fibration `E' → B`. It is exhaustive when the end points lie in the complex, since a cube of
  `E'` has compact image, and zero in degree `-1` for an absolute CW complex.

When the image `g(x)` of every generator lies over the `(ind x)`-skeleton, as for Brown's model of
a CW complex (`TauCeti.brownModel_comparison_mem_pathFromChainSkeleton`), the comparison preserves
these filtrations (`TauCeti.BrownModel.fibrationComparison_mem_cubicalChainModuleSupportedIn`):
appending a path does not move its end point.

The comparison theorem for filtered complexes
(`TauCeti.exists_differential_eq_and_add_eq_of_iSup_eq_top`) then reduces Brown's theorem, that
the fibration comparison is a quasi-isomorphism, to its graded pieces: if for every `q ≥ 0` the
comparison is a quasi-isomorphism from the generators of index `q` to the chains over the
`q`-skeleton modulo the `(q - 1)`-skeleton, it is a quasi-isomorphism
(`BrownModel.exists_coefficientDifferential_eq_and_fibrationComparison_add_eq_of_forall_exists`
in the namespace `TauCeti`). All quasi-isomorphisms are written on elements: every relative cycle
is a relative boundary, the form of the case of the inclusion of a point,
`BrownModel.exists_coefficientDifferential_eq_and_fibrationComparison_subtypeVal_add_eq`.
The graded pieces form the zeroth page of the index spectral sequence of the twisted complex and
of the Serre spectral sequence of `E' → B`, so a quasi-isomorphism on them is an isomorphism on the
first pages. The comparison on them is the cell-by-cell computation of the relative homology of
`E'` over the cells of `B`.

## Main results

* `TauCeti.BrownModel.fibrationComparison_mem_cubicalChainModuleSupportedIn`: the fibration
  comparison preserves the skeletal filtrations.
* `BrownModel.exists_coefficientDifferential_eq_and_fibrationComparison_add_eq_of_forall_exists`:
  the fibration comparison is a quasi-isomorphism as soon as it is one on the graded pieces of the
  skeletal filtrations.

## References

* E. H. Brown, *Twisted tensor products, I*, Ann. of Math. (2) 69 (1959), 223–246.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, §7.2 (Theorem 7.2.1).
* J.-P. Serre, *Homologie singulière des espaces fibrés. Applications*, Ann. of Math. 54 (1951),
  425–505, Chapter II.
-/

public section

noncomputable section

open Set Topology Topology.RelCWComplex

namespace TauCeti

namespace BrownModel

universe u

variable {E B : Type u} [TopologicalSpace E] [TopologicalSpace B] [T2Space B] {b : B}
  {H : Type*} {R : Type*} [CommRing R] {P : Type*} {ind : P → ℤ}

/-- **The fibration comparison preserves the skeletal filtrations.** If the image of every
generator `x` of a Brown model `M` lies over the `(ind x)`-skeleton of `B`, then the fibration
comparison of `M` sends the coefficient vectors carried by generators of index at most `q` to
chains of the total space of the Moore-path replacement of `p` supported over the `q`-skeleton. -/
theorem fibrationComparison_mem_cubicalChainModuleSupportedIn {C D : Set B} [RelCWComplex C D]
    (M : BrownModel B b H R P ind) (p : C(E, B))
    (hM : ∀ x, M.comparison x ∈ pathFromChainSkeleton b C H R (ind x)) {q : ℤ}
    {f : P →₀ cubicalChainModule (MooreReplacement.Fiber p b) (MooreLoopSpace B b) R}
    (hf : f ∈ rowFiniteIndexFiltration (R := R) ind q) :
    M.fibrationComparison p f ∈
      cubicalChainModuleSupportedIn H R (preimageSkeleton C (MooreReplacement.endpoint p) q) := by
  rw [fibrationComparison_def]
  refine coefficientPairing_mem_cubicalChainModuleSupportedIn
    (T := preimageSkeleton C (MoorePathFrom.endpoint B b) q) (fun σ δ hδ ↦ ?_) fun x hx ↦ ?_
  · simpa [mem_preimageSkeleton_iff, MoorePathFrom.endpoint_apply] using hδ
  · -- A generator carrying a nonzero coefficient has index at most `q`.
    have hx' : ind x ≤ q := not_lt.1 fun h ↦
      Finsupp.mem_support_iff.1 hx ((mem_rowFiniteIndexFiltration_iff ind).1 hf x h)
    exact mem_pathFromChainSkeleton.1 (monotone_pathFromChainSkeleton b C H R hx' (hM x))

/-- **Brown's theorem reduces to the graded pieces of the skeletal filtrations.** Let `B` be a CW
complex containing the end points of the Moore-path replacement of `p`, and `M` a Brown model at `b`
with generators of nonnegative index. Suppose that for every `q ≥ 0` the fibration comparison is a
quasi-isomorphism from the coefficient vectors carried by generators of index at most `q` to the
chains over the `q`-skeleton, modulo those carried by generators of index at most `q - 1` and the
chains over the `(q - 1)`-skeleton: every relative cycle of this graded piece is a relative
boundary there. Then the fibration comparison is a quasi-isomorphism: every relative cycle
`(u, w)`, with `D u = 0` and `Ψ u = ∂ w`, is a relative boundary `(D u', Ψ u' + ∂ w')`. -/
theorem exists_coefficientDifferential_eq_and_fibrationComparison_add_eq_of_forall_exists
    {C : Set B} [CWComplex C] (M : BrownModel B b H R P ind) (p : C(E, B))
    (hind : ∀ x, 0 ≤ ind x) (hC : range (MooreReplacement.endpoint p) ⊆ C)
    (hgr : ∀ q : ℤ, 0 ≤ q →
      ∀ u ∈ rowFiniteIndexFiltration (R := R) ind q,
      ∀ w ∈ cubicalChainModuleSupportedIn H R (preimageSkeleton C (MooreReplacement.endpoint p) q),
      M.cocycle.coefficientDifferential (cubicalChainModule_isDGRightModule
          (MooreReplacement.Fiber p b) (MooreLoopSpace B b) R) u ∈
        rowFiniteIndexFiltration (R := R) ind (q - 1) →
      M.fibrationComparison p u - cubicalChainModuleDifferential (MooreReplacement p) H R w ∈
        cubicalChainModuleSupportedIn H R
          (preimageSkeleton C (MooreReplacement.endpoint p) (q - 1)) →
      ∃ u' ∈ rowFiniteIndexFiltration (R := R) ind q,
      ∃ w' ∈ cubicalChainModuleSupportedIn H R
          (preimageSkeleton C (MooreReplacement.endpoint p) q),
        M.cocycle.coefficientDifferential (cubicalChainModule_isDGRightModule
            (MooreReplacement.Fiber p b) (MooreLoopSpace B b) R) u' - u ∈
          rowFiniteIndexFiltration (R := R) ind (q - 1) ∧
        M.fibrationComparison p u' + cubicalChainModuleDifferential (MooreReplacement p) H R w' -
            w ∈
          cubicalChainModuleSupportedIn H R
            (preimageSkeleton C (MooreReplacement.endpoint p) (q - 1)))
    {u : P →₀ cubicalChainModule (MooreReplacement.Fiber p b) (MooreLoopSpace B b) R}
    {w : cubicalChainModule (MooreReplacement p) H R}
    (hu : M.cocycle.coefficientDifferential (cubicalChainModule_isDGRightModule
      (MooreReplacement.Fiber p b) (MooreLoopSpace B b) R) u = 0)
    (hw : M.fibrationComparison p u = cubicalChainModuleDifferential (MooreReplacement p) H R w) :
    ∃ u' w', M.cocycle.coefficientDifferential (cubicalChainModule_isDGRightModule
        (MooreReplacement.Fiber p b) (MooreLoopSpace B b) R) u' = u ∧
      M.fibrationComparison p u' + cubicalChainModuleDifferential (MooreReplacement p) H R w' =
        w := by
  -- Both filtrations vanish in degree `-1`, so the comparison starts there.
  have hF : rowFiniteIndexFiltration (R := R)
      (A := cubicalChainModule (MooreReplacement.Fiber p b) (MooreLoopSpace B b) R) ind (-1) =
        ⊥ :=
    rowFiniteIndexFiltration_eq_bot ind fun x ↦ by linarith [hind x]
  have hN : cubicalChainModuleSupportedIn H R
      (preimageSkeleton C (MooreReplacement.endpoint p) (-1)) = ⊥ := by
    rw [preimageSkeleton_eq_empty _ (by norm_num), cubicalChainModuleSupportedIn_empty]
  refine exists_differential_eq_and_add_eq_of_iSup_eq_top
    (fun f ↦ M.fibrationComparison_coefficientDifferential p f)
    (M.cocycle.coefficientDifferential_sq_zero _)
    cubicalChainModuleDifferential_cubicalChainModuleDifferential
    (rowFiniteIndexFiltration_mono ind)
    (fun _ _ h ↦ cubicalChainModuleSupportedIn_mono (monotone_preimageSkeleton _ h))
    (iSup_rowFiniteIndexFiltration_eq_top ind)
    (iSup_cubicalChainModuleSupportedIn_eq_top fun _ hK ↦
      exists_subset_preimageSkeleton_of_isCompact (MooreReplacement.endpoint p).continuous hC hK)
    (q₀ := -1) ?_ (fun q hq ↦ ?_) hu hw
  · rw [hF, hN]
    rintro u hu w hw - -
    rw [Submodule.mem_bot] at hu hw
    exact ⟨0, zero_mem _, 0, zero_mem _, by simp [hu], by simp [hw]⟩
  · simpa only [add_sub_cancel_right] using hgr (q + 1) (by omega)

end BrownModel

end TauCeti
