/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.LocalizedModule.Submodule
public import TauCeti.Algebra.Ring.Subgroup
public import TauCeti.RingTheory.IntegralOrder.Basic

/-!
# The left order of a lattice

Let `R` be a commutative ring and `E` an `R`-algebra, not necessarily commutative. The left order of
an `R`-submodule `M` of `E` is the `R`-subalgebra `O_l(M) = {x ∈ E | x * M ⊆ M}`, the largest
subalgebra of `E` over which `M` is a left module. When `R` is a noetherian ring with fraction field
`F`, `E` is an `F`-algebra and `M` is an `R`-lattice in `E`, the left order is an `R`-order in `E`.
This is the standard way of producing orders from lattices: for instance the associated order of a
Galois extension is the left order of the lattice corresponding to its ring of integers.

The lattice statement rests on clearing denominators, `Submodule.FG.exists_smul_mem_of_le_span` in
`TauCeti.Algebra.Module.LocalizedModule.Submodule`, the uniform version of Mathlib's
`multiple_mem_span_of_mem_localization_span`.

## Main definitions

* `Submodule.leftOrder M`: the left order `{x ∈ E | x * M ⊆ M}` of an `R`-submodule `M` of `E`.

## Main results

* `Submodule.mem_leftOrder_iff`: `x ∈ O_l(M)` exactly when `x * m ∈ M` for all `m ∈ M`.
* `Submodule.le_leftOrder_iff`: `O_l(M)` is the largest subalgebra `Λ` with `Λ * M ≤ M`.
* `Subalgebra.leftOrder_toSubmodule`: the left order of a subalgebra, and in particular of an order,
  is itself.
* `Submodule.leftOrder_smul`: rescaling `M` by a central left-regular element, for instance a
  nonzero element of a field, does not change its left order.
* `Submodule.toSubring_leftOrder`: over a ring, the left order has the same underlying subring as
  the multiplier ring `AddSubgroup.multiplierRing` of `M`, so results about either apply to both.
* `Submodule.leftOrder_isOrder`: over a noetherian `R`, the left order of an `R`-lattice is an
  `R`-order.

## References

* H. Johnston, *Notes on Galois modules*, Definition 3.11 and Proposition 3.12.
* J. Voight, *Quaternion algebras*, Lemma 10.2.7.
-/

public section

open scoped Pointwise nonZeroDivisors

namespace Submodule

section Basic

variable {R E : Type*} [CommSemiring R] [Semiring E] [Algebra R E]

/-- The **left order** `O_l(M) = {x ∈ E | x * M ⊆ M}` of an `R`-submodule `M` of an `R`-algebra
`E`: the largest `R`-subalgebra of `E` over which `M` is a left module. -/
def leftOrder (M : Submodule R E) : Subalgebra R E where
  carrier := {x | ∀ m ∈ M, x * m ∈ M}
  mul_mem' {x y} hx hy m hm := by
    rw [mul_assoc]
    exact hx _ (hy m hm)
  add_mem' {x y} hx hy m hm := by
    rw [add_mul]
    exact add_mem (hx m hm) (hy m hm)
  algebraMap_mem' r m hm := by
    rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
    exact smul_mem _ r hm

variable {M : Submodule R E}

/-- An element lies in the left order of `M` exactly when left multiplication by it preserves
`M`. -/
@[simp]
theorem mem_leftOrder_iff {x : E} : x ∈ M.leftOrder ↔ ∀ m ∈ M, x * m ∈ M :=
  Iff.rfl

/-- **Universal property of the left order.** A subalgebra `Λ` lies in the left order of `M` exactly
when `Λ * M ≤ M`, so `O_l(M)` is the largest subalgebra over which `M` is a left module. -/
theorem le_leftOrder_iff {Λ : Subalgebra R E} :
    Λ ≤ M.leftOrder ↔ Subalgebra.toSubmodule Λ * M ≤ M := by
  rw [mul_le]
  exact ⟨fun h x hx m hm => mem_leftOrder_iff.1 (h hx) m hm, fun h x hx => h x hx⟩

/-- **Rescaling does not change the left order.** For a central left-regular element `a` of `E`,
for instance a nonzero element when `E` is a field, `O_l(a • M) = O_l(M)`. -/
theorem leftOrder_smul (M : Submodule R E) {a : E} (ha : IsLeftRegular a)
    (hc : a ∈ Set.center E) : (a • M).leftOrder = M.leftOrder := by
  -- `x * (a * m) = a * (x * m)` by centrality, and `a * y ∈ a • M ↔ y ∈ M` by regularity
  have hcomm (x m : E) : x * (a * m) = a * (x * m) := by
    rw [← mul_assoc, Semigroup.mem_center_iff.1 hc x, mul_assoc]
  have hmem {y : E} : a * y ∈ a • M ↔ y ∈ M := by
    refine ⟨fun h => ?_, smul_mem_pointwise_smul y a M⟩
    obtain ⟨m, hm, hmy⟩ := mem_smul_pointwise_iff_exists _ _ _ |>.1 h
    rwa [← ha hmy]
  ext x
  simp only [mem_leftOrder_iff, mem_smul_pointwise_iff_exists, smul_eq_mul]
  refine ⟨fun h m hm => ?_, ?_⟩
  · rw [← hmem, ← hcomm]
    exact h _ ⟨m, hm, rfl⟩
  · rintro h _ ⟨m, hm, rfl⟩
    rw [hcomm]
    exact smul_mem_pointwise_smul _ a M (h m hm)

end Basic

section Ring

variable {R E : Type*} [CommRing R] [Ring E] [Algebra R E]

/-- Over a ring, the left order of `M` is the multiplier ring of the underlying additive subgroup
of `M` with the `R`-algebra structure added. -/
@[simp]
theorem toSubring_leftOrder (M : Submodule R E) :
    M.leftOrder.toSubring = M.toAddSubgroup.multiplierRing :=
  SetLike.ext fun _ => (AddSubgroup.mem_multiplierRing (W := M.toAddSubgroup)).symm

end Ring

section IsOrder

variable {R F E : Type*} [CommRing R] [IsNoetherianRing R] [Field F] [Ring E] [Algebra R F]
  [IsFractionRing R F] [Algebra F E] [Algebra R E] [IsScalarTower R F E]

/-- **The left order of a lattice is an order.** Over a noetherian ring `R` with fraction field `F`,
the left order of an `R`-lattice in an `F`-algebra `E` is an `R`-order in `E`. -/
theorem leftOrder_isOrder (M : Submodule R E) [M.IsLattice F] :
    TauCeti.IntegralOrder.IsOrder F M.leftOrder := by
  have : IsDomain R := (IsFractionRing.isDomain_iff_isField (K := F)).2 (Field.toIsField F)
  have hspan (v : E) : v ∈ span F (M : Set E) := by
    simp [IsLattice.span_eq_top (A := F) (M := M)]
  refine TauCeti.IntegralOrder.isOrder_iff_isLattice.2 ⟨?_, eq_top_iff.2 fun y _ => ?_⟩
  · -- some `s ∈ R⁰` has `s • 1 ∈ M`, and then `x ↦ s • x = x * (s • 1)` embeds `O_l(M)` into `M`
    obtain ⟨s, hs, hs1⟩ :=
      (fg_span_singleton (1 : E)).exists_smul_mem_of_le_span R⁰ fun v _ => hspan v
    replace hs1 := hs1 1 (mem_span_singleton_self 1)
    have hs' : algebraMap R F s ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hs
    refine fg_of_fg_map_injective (LinearMap.lsmul R E s) (fun x y hxy => ?_)
      ((IsLattice.fg (A := F) (M := M)).of_le (map_le_iff_le_comap.2 fun x hx => ?_))
    · simp only [LinearMap.lsmul_apply, ← algebraMap_smul F s] at hxy
      exact smul_right_injective E hs' hxy
    · simpa [mul_smul_comm] using mem_leftOrder_iff.1 hx _ hs1
  · -- `y * M` is a finitely generated submodule of `E`, so `r • (y * M) ≤ M` for some `r ∈ R⁰`;
    -- then `r • y ∈ O_l(M)` and `y = r⁻¹ • (r • y)`
    obtain ⟨r, hr, hry⟩ := (IsLattice.fg (A := F) (M := M)).map (LinearMap.mulLeft R y)
      |>.exists_smul_mem_of_le_span R⁰ fun v _ => hspan v
    have hmem : r • y ∈ M.leftOrder := fun m hm => by
      rw [smul_mul_assoc]
      exact hry _ (mem_map_of_mem hm)
    have hr' : algebraMap R F r ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hr
    convert smul_mem _ (algebraMap R F r)⁻¹ (subset_span hmem :
      r • y ∈ span F (M.leftOrder : Set E)) using 1
    rw [← algebraMap_smul F r y, smul_smul, inv_mul_cancel₀ hr', one_smul]

end IsOrder

end Submodule

namespace Subalgebra

variable {R E : Type*} [CommSemiring R] [Semiring E] [Algebra R E]

/-- **The left order of an order is itself.** The left order of a subalgebra `Λ`, viewed as an
`R`-submodule, is `Λ`: products stay in `Λ`, and `x = x * 1`. -/
@[simp]
theorem leftOrder_toSubmodule (Λ : Subalgebra R E) : (toSubmodule Λ).leftOrder = Λ :=
  le_antisymm (fun x hx => by simpa using Submodule.mem_leftOrder_iff.1 hx 1 Λ.one_mem)
    fun _ hx _ hm => Λ.mul_mem hx hm

end Subalgebra
