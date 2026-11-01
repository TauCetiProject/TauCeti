/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Preadditive.Basic
public import TauCeti.CategoryTheory.Functor.ProZero
import TauCeti.CategoryTheory.Functor.InverseSystem

/-!
# The product–difference map of a tower

Let `F : ℕᵒᵖ ⥤ C` be a tower `F₀ ← F₁ ← F₂ ← ⋯` in a preadditive category whose terms have a
product. The *product–difference map* is the endomorphism `1 - s` of `∏ₙ Fₙ`, where the `n`-th
component of `s` is the projection to `Fₙ₊₁` followed by the transition `Fₙ₊₁ ⟶ Fₙ`. Its kernel is
the limit of the tower. Its cokernel is what we call `lim¹` of the tower; this agrees with the first
right derived functor of `lim` in an abelian category with exact countable products, such as a
category of modules, but not in general (for instance for sheaves). Likewise, the derived limit of
a tower of complexes is the fibre of the same map only when the products used compute derived
products, as products in the derived category do. Under such hypotheses this presentation is what
the Milnor sequence, relating `lim` and `lim¹` of cohomology to the cohomology of a derived limit,
is built on.

For a pro-zero tower the product–difference map is an isomorphism: since every term `Fₙ` is killed
by some composite transition `Fₙ₊ₖ ⟶ Fₙ`, the formal inverse `∑ₖ sᵏ` has only finitely many nonzero
terms in each component. Hence the kernel and the cokernel of the product–difference map of a
pro-zero tower vanish, in every preadditive category with the relevant product; no exactness of
products is needed for this.

## Main declarations

* `CategoryTheory.Functor.towerDifference`: the product–difference map `1 - s` of a tower.
* `CategoryTheory.Functor.towerDifference_naturality`: it is natural in morphisms of towers.
* `CategoryTheory.Functor.coneOfTowerDifference`: a morphism into the product killed by the
  product–difference map is a cone over the tower.
* `CategoryTheory.Functor.isLimitConeOfTowerDifference`,
  `CategoryTheory.Functor.isLimitKernelForkOfIsLimit`: a kernel of the product–difference map is a
  limit of the tower, and a limit of the tower is a kernel of the product–difference map.
* `CategoryTheory.Functor.IsProZero.isIso_towerDifference`: the product–difference map of a
  pro-zero tower is an isomorphism.

## References

* [Stacks: Derived Categories, Section 13.34, Tag 08TB](https://stacks.math.columbia.edu/tag/08TB)
* C. A. Weibel, *An introduction to homological algebra*, §3.5.
* B. Bhatt, *On the direct summand conjecture and its derived variant*, Invent. Math. 212 (2018),
  Lemma 3.4 (pro-zero towers, in their almost form).
-/

public section

noncomputable section

namespace CategoryTheory

open Limits Opposite

universe v u

namespace Functor

variable {C : Type u} [Category.{v} C] [Preadditive C]

section Difference

variable (F : ℕᵒᵖ ⥤ C) [HasProduct fun n : ℕ ↦ F.obj (op n)]

/-- The *product–difference map* `1 - s` of a tower `F₀ ← F₁ ← ⋯`: the endomorphism of `∏ₙ Fₙ` whose
`n`-th component is the projection to `Fₙ` minus the projection to `Fₙ₊₁` followed by the
transition `Fₙ₊₁ ⟶ Fₙ` (`towerDifference_π`). Its kernel is the limit of the tower
(`isLimitConeOfTowerDifference`). -/
def towerDifference : ∏ᶜ (fun n : ℕ ↦ F.obj (op n)) ⟶ ∏ᶜ (fun n : ℕ ↦ F.obj (op n)) :=
  Pi.lift fun n ↦ Pi.π _ n - Pi.π _ (n + 1) ≫ F.map (homOfLE (Nat.le_add_right n 1)).op

@[reassoc (attr := simp)]
lemma towerDifference_π (n : ℕ) :
    F.towerDifference ≫ Pi.π _ n =
      Pi.π _ n - Pi.π _ (n + 1) ≫ F.map (homOfLE (Nat.le_add_right n 1)).op := by
  simp [towerDifference]

/-- A morphism `ι` into `∏ₙ Fₙ` is killed by the product–difference map exactly when its components
are compatible with the transitions `Fₙ₊₁ ⟶ Fₙ`. -/
lemma comp_towerDifference_eq_zero_iff {X : C} (ι : X ⟶ ∏ᶜ fun n : ℕ ↦ F.obj (op n)) :
    ι ≫ F.towerDifference = 0 ↔
      ∀ n, ι ≫ Pi.π _ (n + 1) ≫ F.map (homOfLE (Nat.le_add_right n 1)).op = ι ≫ Pi.π _ n := by
  refine ⟨fun h n ↦ ?_, fun h ↦ Pi.hom_ext _ _ fun n ↦ ?_⟩
  · have h' := h =≫ Pi.π _ n
    simp only [Category.assoc, towerDifference_π, Preadditive.comp_sub, zero_comp] at h'
    exact (sub_eq_zero.1 h').symm
  · simp [Preadditive.comp_sub, h n]

variable {F} in
/-- A morphism into `∏ₙ Fₙ` killed by the product–difference map is a cone over the tower, with the
components of the morphism as its projections. -/
@[simps pt]
abbrev coneOfTowerDifference {X : C} (ι : X ⟶ ∏ᶜ fun n : ℕ ↦ F.obj (op n))
    (w : ι ≫ F.towerDifference = 0) : Cone F where
  pt := X
  π := NatTrans.ofOpSequence (fun n ↦ ι ≫ Pi.π _ n) fun n ↦ by
    simp [(F.comp_towerDifference_eq_zero_iff ι).1 w n]

@[simp]
lemma coneOfTowerDifference_π_app {X : C} (ι : X ⟶ ∏ᶜ fun n : ℕ ↦ F.obj (op n))
    (w : ι ≫ F.towerDifference = 0) (n : ℕᵒᵖ) :
    (coneOfTowerDifference ι w).π.app n = ι ≫ Pi.π _ n.unop :=
  rfl

/-- The projections of a cone over a tower are killed by the product–difference map. -/
@[reassoc (attr := simp)]
lemma lift_π_app_towerDifference (c : Cone F) :
    Pi.lift (fun n : ℕ ↦ c.π.app (op n)) ≫ F.towerDifference = 0 :=
  (F.comp_towerDifference_eq_zero_iff _).2 fun n ↦ by simp

variable {F} in
/-- A kernel of the product–difference map is a limit of the tower: the limit of a tower is the
object of compatible families in the product of its terms. -/
def isLimitConeOfTowerDifference {c : KernelFork F.towerDifference} (hc : IsLimit c) :
    IsLimit (coneOfTowerDifference c.ι c.condition) where
  lift s := (KernelFork.IsLimit.lift' hc _ (F.lift_π_app_towerDifference s)).1
  fac s n := by
    rw [coneOfTowerDifference_π_app, ← Category.assoc,
      (KernelFork.IsLimit.lift' hc _ (F.lift_π_app_towerDifference s)).2, Pi.lift_comp_π]
  uniq s m hm := Fork.IsLimit.hom_ext hc <| by
    rw [(KernelFork.IsLimit.lift' hc _ (F.lift_π_app_towerDifference s)).2]
    exact Pi.hom_ext _ _ fun n ↦ by simpa using hm (op n)

variable {F} in
/-- A limit of a tower is a kernel of its product–difference map, through the morphism into the
product of the terms given by the limit projections. -/
def isLimitKernelForkOfIsLimit {c : Cone F} (hc : IsLimit c) :
    IsLimit (KernelFork.ofι _ (F.lift_π_app_towerDifference c)) :=
  KernelFork.IsLimit.ofι _ _ (fun k hk ↦ hc.lift (coneOfTowerDifference k hk))
    (fun k hk ↦ Pi.hom_ext _ _ fun n ↦ by
      rw [Category.assoc, Pi.lift_comp_π]
      exact hc.fac (coneOfTowerDifference k hk) (op n))
    (fun k hk m hm ↦ hc.hom_ext fun n ↦ by
      rw [hc.fac, coneOfTowerDifference_π_app, ← hm]
      simp)

end Difference

/-- The product–difference map is natural: a morphism of towers `α : F ⟶ G` induces a morphism
of the products of their terms that intertwines the two product–difference maps. -/
@[reassoc]
lemma towerDifference_naturality {F G : ℕᵒᵖ ⥤ C} [HasProduct fun n : ℕ ↦ F.obj (op n)]
    [HasProduct fun n : ℕ ↦ G.obj (op n)] (α : F ⟶ G) :
    F.towerDifference ≫ Limits.Pi.map (fun n ↦ α.app (op n)) =
      Limits.Pi.map (fun n ↦ α.app (op n)) ≫ G.towerDifference :=
  Pi.hom_ext _ _ fun n ↦ by simp [Preadditive.sub_comp, Preadditive.comp_sub]

section ProZero

variable {F : ℕᵒᵖ ⥤ C}

/-- **Pro-zero towers have invertible product–difference map.** If every term of a tower is killed
by some composite transition, then `1 - s` is an isomorphism of `∏ₙ Fₙ`: its inverse is `∑ₖ sᵏ`,
whose `n`-th component is a finite sum because the composites `Fₙ₊ₖ ⟶ Fₙ` vanish for large `k`.
Consequently the kernel of the product–difference map, which is the limit of the tower, and its
cokernel, which is what we call `lim¹` of the tower, both vanish. -/
theorem IsProZero.isIso_towerDifference (hF : F.IsProZero)
    [HasProduct fun n : ℕ ↦ F.obj (op n)] : IsIso F.towerDifference := by
  -- `t n k` is the composite transition `Fₙ₊ₖ ⟶ Fₙ` and `S n N = ∑_{k < N} πₙ₊ₖ ≫ t n k`.
  let t (n k : ℕ) : F.obj (op (n + k)) ⟶ F.obj (op n) := F.map (homOfLE (Nat.le_add_right n k)).op
  let f (n k : ℕ) := Pi.π (fun n : ℕ ↦ F.obj (op n)) (n + k) ≫ t n k
  let S (n N : ℕ) := ∑ k ∈ Finset.range N, f n k
  -- Choose `N n` with `t n k = 0` for all `k ≥ N n`, so that `S n M = S n (N n)` for `M ≥ N n`.
  have hN : ∀ n, ∃ N, ∀ k, N ≤ k → t n k = 0 := fun n ↦ by
    obtain ⟨m, hnm, hm⟩ := (isProZero_iff_forall_exists_le F).1 hF n
    refine ⟨m - n, fun k hk ↦ ?_⟩
    have hmk : m ≤ n + k := by lia
    simp only [t, ← F.map_homOfLE_op_comp_map_homOfLE_op hnm hmk, hm, Limits.comp_zero]
  choose N hN using hN
  have hS : ∀ n M, N n ≤ M → S n M = S n (N n) := fun n M hM ↦
    (Finset.sum_subset (Finset.range_mono hM) fun k _ hk ↦ by
      simp [f, hN n k (by simpa using hk)]).symm
  have hf₀ (n : ℕ) : f n 0 = Pi.π _ n := by
    simp [f, t, F.π_comp_map_homOfLE_op_congr (Nat.add_zero n) (Nat.le_add_right n 0) le_rfl]
  have hf_succ (n k : ℕ) : Pi.π _ (n + k + 1) ≫ F.map (homOfLE (Nat.le_add_right (n + k) 1)).op ≫
      t n k = f n (k + 1) := by
    simp only [f, t, map_homOfLE_op_comp_map_homOfLE_op]
    exact F.π_comp_map_homOfLE_op_congr (by lia) _ _
  refine ⟨Pi.lift fun n ↦ S n (N n), Pi.hom_ext _ _ fun n ↦ ?_, Pi.hom_ext _ _ fun n ↦ ?_⟩
  · -- `(1 - s) ≫ ∑ₖ sᵏ` telescopes to `f n 0 - f n (N n) = πₙ`.
    have hD (k : ℕ) : F.towerDifference ≫ f n k = f n k - f n (k + 1) := by
      rw [← hf_succ]
      simp [f, Preadditive.sub_comp]
    rw [Category.assoc, Pi.lift_comp_π, Category.id_comp]
    simp only [S, Preadditive.comp_sum, hD]
    rw [Finset.sum_range_sub', hf₀]
    simp [f, hN n (N n) le_rfl]
  · -- Both partial sums are computed at a common large length `M`, and the second one is the
    -- first one without its initial term.
    set M := N n + N (n + 1)
    have hshift : S (n + 1) M ≫ F.map (homOfLE (Nat.le_add_right n 1)).op =
        ∑ k ∈ Finset.range M, f n (k + 1) := by
      simp only [S, Preadditive.sum_comp]
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      simp only [f, t, Category.assoc, map_homOfLE_op_comp_map_homOfLE_op]
      exact F.π_comp_map_homOfLE_op_congr (by lia) _ _
    simp only [Category.assoc, towerDifference_π, Preadditive.comp_sub, Pi.lift_comp_π_assoc,
      Pi.lift_comp_π, Category.id_comp]
    rw [← hS (n + 1) M (by lia), hshift, ← hS n (M + 1) (by lia)]
    simp only [S]
    rw [Finset.sum_range_succ', hf₀]
    abel

end ProZero

end Functor

end CategoryTheory
