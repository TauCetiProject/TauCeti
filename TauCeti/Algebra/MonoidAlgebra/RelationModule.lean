/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import TauCeti.Algebra.MonoidAlgebra.Exactness

/-!
# The relation module of a family of group elements

For a family `g : ι → G` of elements of a group, indexed by a finite type, the left
`R[G]`-linear map `R[G]^ι → R[G]`, `e_i ↦ g_i - 1`, lands in the augmentation ideal `I_G`, the
kernel of `TauCeti.MonoidAlgebra.augmentation R G`. Its kernel is the **relation module** of the
family. When the `g_i` generate `G`, the map is onto `I_G`, giving Lyndon's exact sequence
`0 → relationModule R G g → R[G]^ι → I_G → 0`.

When `G` is a group, the `g_i` generate `G` and `R = ℤ`, the relation module is the abelianised
relation group `N^ab` of the presentation `1 → N → F → G → 1` of `G` by the free group `F` on the
`g_i`, with its conjugation action of `G` (Lyndon's identification, NSW (5.6.6)). Since `ℤ[G]^ι`
and `I_G` are free abelian groups, for a general ring `R` it is the scalar extension `R ⊗_ℤ N^ab`.
Here the kernel is taken as the definition, so no group-theoretic carrier is needed. The module
`R^ab(p)` compared with the `p`-completed units of a local field in the computation of the
generator rank of its absolute Galois group (NSW (7.4.1)) is its analogue over `R = ℤ_p`.

## Main definitions

* `TauCeti.MonoidAlgebra.relationModule`: the kernel of `R[G]^ι → R[G]`, `e_i ↦ g_i - 1`.

## Main statements

* `TauCeti.MonoidAlgebra.mem_relationModule_iff`: membership as the relation `∑ c_i (g_i - 1) = 0`.
* `TauCeti.MonoidAlgebra.range_linearCombination_le_ker_augmentation`: the map lands in `I_G`.
* `TauCeti.MonoidAlgebra.range_linearCombination_eq_ker_augmentation`: the map is onto `I_G` when
  the `g_i` generate `G`, and `range_linearCombination_eq_ker_augmentation_iff` is the converse
  over a nontrivial ring.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, (5.6.6) and (7.4.1).
* R. C. Lyndon, *Cohomology theory of groups with a single defining relation*, Ann. of Math. 52
  (1950).
-/

public section

namespace TauCeti.MonoidAlgebra

open _root_.MonoidAlgebra

universe u v w

variable (R : Type u) [Ring R] (G : Type v) {ι : Type w} [Fintype ι]

section Monoid

variable [Monoid G]

/-- The **relation module** of a family `g : ι → G`: the kernel of the left `R[G]`-linear map
`R[G]^ι → R[G]` sending the `i`-th basis vector to `g_i - 1`. For a generating family of a group
it is `R ⊗_ℤ N^ab`, for `N^ab` the relation module of the presentation of `G` on the `g_i`
(NSW (5.6.6)); for `R = ℤ` it is `N^ab` itself. -/
@[expose]
noncomputable def relationModule (g : ι → G) :
    Submodule (MonoidAlgebra R G) (ι → MonoidAlgebra R G) :=
  LinearMap.ker (Fintype.linearCombination (MonoidAlgebra R G) fun i ↦ single (g i) (1 : R) - 1)

variable {R G}

/-- A family of coefficients lies in the relation module of `g` exactly when
`∑ c_i (g_i - 1) = 0`. -/
@[simp]
theorem mem_relationModule_iff {g : ι → G} {c : ι → MonoidAlgebra R G} :
    c ∈ relationModule R G g ↔ ∑ i, c i * (single (g i) (1 : R) - 1) = 0 := by
  simp [relationModule, Fintype.linearCombination_apply]

/-- The map `e_i ↦ g_i - 1` lands in the augmentation ideal. -/
theorem range_linearCombination_le_ker_augmentation (g : ι → G) :
    LinearMap.range (Fintype.linearCombination (MonoidAlgebra R G)
        fun i ↦ single (g i) (1 : R) - 1) ≤
      RingHom.ker (augmentation R G) := by
  rw [Fintype.range_linearCombination, ker_augmentation_eq_span]
  exact Submodule.span_mono (Set.range_subset_iff.2 fun i ↦ ⟨g i, rfl⟩)

end Monoid

section Group

variable [Group G] {R G}

/-- **Lyndon's sequence is exact at `I_G`.** When the `g_i` generate `G`, the map `e_i ↦ g_i - 1`
is onto the augmentation ideal, so `0 → relationModule R G g → R[G]^ι → I_G → 0` is exact. -/
theorem range_linearCombination_eq_ker_augmentation {g : ι → G}
    (hg : Subgroup.closure (Set.range g) = ⊤) :
    LinearMap.range (Fintype.linearCombination (MonoidAlgebra R G)
        fun i ↦ single (g i) (1 : R) - 1) =
      RingHom.ker (augmentation R G) := by
  rw [Fintype.range_linearCombination, ker_augmentation_eq_span_of_closure_eq_top R hg,
    ← Set.range_comp, Ideal.submodule_span_eq, Function.comp_def]

/-- Over a nontrivial ring, the map `e_i ↦ g_i - 1` is onto the augmentation ideal exactly when
the `g_i` generate `G`. -/
theorem range_linearCombination_eq_ker_augmentation_iff [Nontrivial R] {g : ι → G} :
    LinearMap.range (Fintype.linearCombination (MonoidAlgebra R G)
        fun i ↦ single (g i) (1 : R) - 1) =
      RingHom.ker (augmentation R G) ↔
      Subgroup.closure (Set.range g) = ⊤ := by
  rw [← ker_augmentation_eq_span_iff R, Fintype.range_linearCombination, ← Set.range_comp,
    Ideal.submodule_span_eq, eq_comm, Function.comp_def]

end Group

end TauCeti.MonoidAlgebra
