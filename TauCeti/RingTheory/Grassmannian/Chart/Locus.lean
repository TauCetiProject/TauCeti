/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.FittingIdeal.Basic
public import TauCeti.RingTheory.Grassmannian.Chart.Basic

import TauCeti.LinearAlgebra.TensorProduct.Quotient
import TauCeti.RingTheory.FittingIdeal.BaseChange

/-!
# The standard charts of the Grassmannian are open and cover it

Let `M` be a module over a commutative ring `R`, and let `Module.Grassmannian.functor k` be the
Grassmannian functor `A ↦ G(k, A ⊗[R] M; A)` on commutative `R`-algebras. For `x : Fin k → M`, the
chart subfunctor `Module.Grassmannian.chartFunctor R x` consists over `A` of the points `N` for
which the images of the `1 ⊗ₜ x i` form a basis of `(A ⊗[R] M) ⧸ N`. This file proves the two
properties of these charts from which the Grassmannian scheme is glued: each chart is an open
subfunctor, and the charts cover the Grassmannian functor in the Zariski topology.

Openness is stated through an ideal. For a point `N ∈ G(k, P; A)` of an `A`-module `P` and a family
`y : Fin k → P`, the *chart locus* `Module.Grassmannian.chartLocus N y` is the zeroth Fitting ideal
of the cokernel of `A^k → P ⧸ N`, `v ↦ ∑ vᵢ yᵢ`. Over `Spec A`, its basic open `D(chartLocus N y)`
is the open subscheme over which the images of the `yᵢ` form a basis of `P ⧸ N`. Precisely, for a
point `N ∈ G(k, A ⊗[R] M; A)` and an algebra map `f : A → B`, the base change `map f N` lies in the
chart at `x` exactly when `chartLocus N (1 ⊗ₜ x)` extends to the unit ideal of `B`
(`Module.Grassmannian.map_mem_chart_iff`), that is, exactly when `Spec B ⟶ Spec A` factors through
`D(chartLocus N (1 ⊗ₜ x))`. This holds because the cokernel is finitely generated, its Fitting
ideals commute with base change, and its zeroth Fitting ideal is the unit ideal exactly when it
vanishes.

The charts cover: for every point `N ∈ G(k, A ⊗[R] M; A)`, the chart loci `chartLocus N (1 ⊗ₜ x)`
over all `x : Fin k → M` generate the unit ideal of `A`
(`Module.Grassmannian.iSup_chartLocus_tmul_eq_top`), so the opens `D(chartLocus N (1 ⊗ₜ x))` cover
`Spec A`. At a maximal ideal `m` of `A`, the fibre `κ(m) ⊗[A] ((A ⊗[R] M) ⧸ N)` is a
`k`-dimensional vector space spanned by the images of the `1 ⊗ₜ m'`, so `k` of them form a basis,
and the cokernel at the corresponding family vanishes at `m`.

## Main definitions

* `Module.Grassmannian.chartLocus N y`: the zeroth Fitting ideal of the cokernel of
  `A^k → P ⧸ N`, `v ↦ ∑ vᵢ yᵢ`.

## Main results

* `Module.Grassmannian.chartLocus_eq_top_iff`: the chart locus is the unit ideal exactly when `N`
  lies in the chart at `y`.
* `Module.Grassmannian.map_mem_chart_iff`: **the charts are open**; the base change of `N` along
  `f : A → B` lies in the chart at `x` exactly when the chart locus extends to the unit ideal of
  `B`.
* `Module.Grassmannian.iSup_chartLocus_eq_top`: the chart loci at the `k`-element subfamilies of a
  family generating `P ⧸ N` generate the unit ideal.
* `Module.Grassmannian.iSup_chartLocus_tmul_eq_top`: **the charts cover**; for every
  `N ∈ G(k, A ⊗[R] M; A)` the chart loci at all `x : Fin k → M` generate the unit ideal of `A`.

## References

* A. Grothendieck, J. Dieudonné, *Éléments de géométrie algébrique I* (Springer, 1971), 9.7.
* [The Stacks Project, Tag 089R](https://stacks.math.columbia.edu/tag/089R), for the Grassmannian
  functor, and [Tag 07ZA](https://stacks.math.columbia.edu/tag/07ZA) for Fitting ideals.
-/

public section

universe w

open TensorProduct

namespace Module.Grassmannian

section ChartLocus

variable {A : Type*} [CommRing A] {P : Type*} [AddCommGroup P] [Module A P] {k : ℕ}

/-- The **chart locus** of `N ∈ G(k, P; A)` at `y : Fin k → P`: the zeroth Fitting ideal of the
cokernel of `A^k → P ⧸ N`, `v ↦ ∑ vᵢ yᵢ`. Its basic open in `Spec A` is the locus over which the
images of the `yᵢ` form a basis of `P ⧸ N` (`Module.Grassmannian.chartLocus_eq_top_iff`,
`Module.Grassmannian.map_mem_chart_iff`). -/
noncomputable def chartLocus (N : G(k, P; A)) (y : Fin k → P) : Ideal A :=
  TauCeti.fittingIdeal A
    ((P ⧸ N.toSubmodule) ⧸ Submodule.span A (Set.range (N.toSubmodule.mkQ ∘ y))) 0

theorem chartLocus_def (N : G(k, P; A)) (y : Fin k → P) :
    chartLocus N y = TauCeti.fittingIdeal A
      ((P ⧸ N.toSubmodule) ⧸ Submodule.span A (Set.range (N.toSubmodule.mkQ ∘ y))) 0 :=
  (rfl)

/-- The chart locus of `N` at `y` is the unit ideal exactly when `N` lies in the chart at `y`. -/
@[simp]
theorem chartLocus_eq_top_iff {N : G(k, P; A)} {y : Fin k → P} :
    chartLocus N y = ⊤ ↔ N ∈ chart A y := by
  rw [chartLocus_def, TauCeti.fittingIdeal_zero_eq_top_iff, Submodule.Quotient.subsingleton_iff,
    Set.range_comp, ← Submodule.map_span, Submodule.map_mkQ_eq_top, mem_chart_iff_sup_eq_top]

/-- Let `v : ι → P` be a family whose images generate `P ⧸ N`. Then the chart loci of `N` at the
families `v ∘ y`, `y : Fin k → ι`, generate the unit ideal of `A`: every point of `Spec A` has a
neighbourhood over which the images of `k` of the `v i` form a basis of `P ⧸ N`. -/
theorem iSup_chartLocus_eq_top (N : G(k, P; A)) {ι : Type*} (v : ι → P)
    (hv : N.toSubmodule ⊔ Submodule.span A (Set.range v) = ⊤) :
    ⨆ y : Fin k → ι, chartLocus N (v ∘ y) = ⊤ := by
  by_contra h
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ h
  set K := m.ResidueField
  set Q := P ⧸ N.toSubmodule
  -- the images `w i` of the `v i` span the fibre `κ(m) ⊗[A] (P ⧸ N)`, of dimension `k`
  set u : ι → Q := N.toSubmodule.mkQ ∘ v
  set w : ι → K ⊗[A] Q := TensorProduct.mk A K Q 1 ∘ u
  have hspan (y : Fin k → ι) : Submodule.span K (Set.range (w ∘ y)) =
      (Submodule.span A (Set.range (u ∘ y))).baseChange K := by
    rw [Submodule.baseChange_span, ← Set.range_comp]
    rfl
  have hw : Submodule.span K (Set.range w) = ⊤ := by
    have hu : Submodule.span A (Set.range u) = ⊤ := by
      rwa [Set.range_comp, ← Submodule.map_span, Submodule.map_mkQ_eq_top]
    rw [Set.range_comp, ← Submodule.baseChange_span, hu, Submodule.baseChange_top]
  have hdim : finrank K (K ⊗[A] Q) = k :=
    (Ideal.finrank_fiber_eq_rankAtStalk m).trans (N.rankAtStalk_eq _)
  -- `k` of the `w i` form a basis of the fibre
  obtain ⟨κ, a, -, hκ, hli⟩ := exists_linearIndependent' K w
  rw [hw] at hκ
  let b := Basis.mk hli hκ.ge
  have : Finite κ := Module.Finite.finite_basis b
  let e : Fin k ≃ κ :=
    (Finite.equivFinOfCardEq ((finrank_eq_nat_card_basis b).symm.trans hdim)).symm
  have hy : Submodule.span K (Set.range (w ∘ (a ∘ e))) = ⊤ := by
    rw [← Function.comp_assoc, Set.range_comp, e.range_eq_univ, Set.image_univ, hκ]
  -- so the cokernel at the family `v ∘ a ∘ e` vanishes at `m`, against `chartLocus ≤ m`
  have hle' : chartLocus N (v ∘ (a ∘ e)) ≤ m :=
    (le_iSup (fun y : Fin k → ι ↦ chartLocus N (v ∘ y)) (a ∘ e)).trans hle
  rw [chartLocus_def, TauCeti.fittingIdeal_le_iff_lt_finrank, finrank_pos_iff,
    ← not_subsingleton_iff_nontrivial, ← Submodule.baseChange_eq_top_iff_subsingleton] at hle'
  exact hle' ((hspan (a ∘ e)).symm.trans hy)

end ChartLocus

section BaseChange

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M] {k : ℕ}
  {A B : Type w} [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]

/-- **The charts of the Grassmannian are open.** Let `N ∈ G(k, A ⊗[R] M; A)`, `x : Fin k → M` and
`f : A → B` an algebra map. The base change `map f N` lies in the chart at `x` exactly when the
chart locus of `N` at `1 ⊗ₜ x` extends to the unit ideal of `B`, that is, exactly when
`Spec B ⟶ Spec A` factors through the basic open `D(chartLocus N (1 ⊗ₜ x))`. -/
theorem map_mem_chart_iff (f : A →ₐ[R] B) (N : G(k, A ⊗[R] M; A)) (x : Fin k → M) :
    map f N ∈ chart B (fun i ↦ (1 : B) ⊗ₜ[R] x i) ↔
      (chartLocus N (fun i ↦ (1 : A) ⊗ₜ[R] x i)).map f = ⊤ := by
  algebraize [f.toRingHom]
  set Q := (A ⊗[R] M) ⧸ N.toSubmodule
  set g := baseChangeMkQ B N.toSubmodule
  -- `map f N` is the kernel of the surjection `g : B ⊗[R] M → B ⊗[A] Q`, so the chart condition
  -- says that the `g (1 ⊗ₜ x i) = 1 ⊗ₜ [1 ⊗ₜ x i]` span `B ⊗[A] Q`
  have hg : LinearMap.range g = ⊤ := LinearMap.range_eq_top.mpr (baseChangeMkQ_surjective _)
  rw [mem_chart_iff_sup_eq_top, map_toSubmodule f N, sup_comm, ← LinearMap.map_eq_top_iff hg,
    Submodule.map_span, ← Set.range_comp]
  -- and these vectors span the extension of scalars of the span of the `[1 ⊗ₜ x i]`
  have hspan : Submodule.span B (Set.range (g ∘ fun i ↦ (1 : B) ⊗ₜ[R] x i)) =
      (Submodule.span A (Set.range (N.toSubmodule.mkQ ∘ fun i ↦ (1 : A) ⊗ₜ[R] x i))).baseChange
        B := by
    rw [Submodule.baseChange_span, ← Set.range_comp]
    congr 2
    ext i
    simp [g]
  rw [hspan, Submodule.baseChange_eq_top_iff_subsingleton, chartLocus_def]
  exact (TauCeti.fittingIdeal_zero_map_eq_top_iff B).symm

/-- **The charts of the Grassmannian cover it.** For every `N ∈ G(k, A ⊗[R] M; A)`, the chart loci
of `N` at the families `1 ⊗ₜ x`, `x : Fin k → M`, generate the unit ideal of `A`, so the basic opens
`D(chartLocus N (1 ⊗ₜ x))` cover `Spec A`. -/
theorem iSup_chartLocus_tmul_eq_top (N : G(k, A ⊗[R] M; A)) :
    ⨆ x : Fin k → M, chartLocus N (fun i ↦ (1 : A) ⊗ₜ[R] x i) = ⊤ := by
  refine iSup_chartLocus_eq_top N (fun m : M ↦ (1 : A) ⊗ₜ[R] m) (eq_top_iff.mpr ?_)
  -- the `1 ⊗ₜ m` span `A ⊗[R] M` over `A`
  rw [← Submodule.baseChange_top A, ← Submodule.span_univ, Submodule.baseChange_span,
    Set.image_univ]
  exact le_sup_right

end BaseChange

end Module.Grassmannian
