/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.IntegralOrder.Basic

/-!
# The left order of a lattice

Let `R` be a commutative ring and `E` an `R`-algebra, not necessarily commutative. The left order of
an `R`-submodule `M` of `E` is the `R`-subalgebra `O_l(M) = {x ∈ E | x * M ⊆ M}`, the largest
subalgebra of `E` over which `M` is a left module. When `R` is a noetherian ring with fraction field
`F`, `E` is an `F`-algebra and `M` is an `R`-lattice in `E`, the left order is an `R`-order in `E`.
This is the standard way of producing orders from lattices: for instance the associated order of a
Galois extension is the left order of the lattice corresponding to its ring of integers.

The lattice statement rests on clearing denominators: when `F` is a localization of `R` at a
submonoid `S`, every element of the `F`-span of `M`, and uniformly every finitely generated
`R`-submodule of it, has a multiple by an element of `S` lying in `M`.

## Main definitions

* `Submodule.leftOrder M`: the left order `{x ∈ E | x * M ⊆ M}` of an `R`-submodule `M` of `E`.

## Main results

* `Submodule.mem_leftOrder_iff`: `x ∈ O_l(M)` exactly when `x * m ∈ M` for all `m ∈ M`.
* `Submodule.le_leftOrder_iff`: `O_l(M)` is the largest subalgebra `Λ` with `Λ * M ≤ M`.
* `Subalgebra.leftOrder_toSubmodule`: the left order of a subalgebra, and in particular of an order,
  is itself.
* `Submodule.leftOrder_smul`: rescaling `M` by a central left-regular element, for instance a
  nonzero element of a field, does not change its left order.
* `Submodule.leftOrder_isOrder`: over a noetherian `R`, the left order of an `R`-lattice is an
  `R`-order.
* `Submodule.FG.exists_smul_mem_of_le_span`: a finitely generated `R`-submodule of the `F`-span of
  `M` is carried into `M` by a single element of the localizing submonoid.

## References

* H. Johnston, *Notes on Galois modules*, Definition 3.11 and Proposition 3.12.
* J. Voight, *Quaternion algebras*, Lemma 10.2.7.
-/

public section

open scoped Pointwise nonZeroDivisors

namespace Submodule

section ClearDenominators

variable {R F E : Type*} [CommRing R] [CommRing F] [AddCommGroup E] [Algebra R F]
  (S : Submonoid R) [IsLocalization S F] [Module F E] [Module R E] [IsScalarTower R F E]
  {M : Submodule R E}

/-- **Clearing denominators.** If `F` is the localization of `R` at `S`, every element of the
`F`-span of an `R`-submodule `M` has a multiple by an element of `S` lying in `M`. -/
theorem exists_smul_mem_of_mem_span {v : E} (hv : v ∈ span F (M : Set E)) :
    ∃ r ∈ S, r • v ∈ M := by
  -- `E` is its own localization at `S`, in which the `F`-span of `M` is the localization of `M`
  have := isLocalizedModule_id S E F
  rw [← Set.image_id (M : Set E), ← LinearMap.id_coe (R := R),
    ← localized'_eq_span F S LinearMap.id M, mem_localized'] at hv
  obtain ⟨m, hm, s, rfl⟩ := hv
  exact ⟨s, s.2, by rwa [← Submonoid.smul_def, IsLocalizedModule.mk'_cancel']⟩

/-- **Clearing denominators uniformly.** If `F` is the localization of `R` at `S`, a finitely
generated `R`-submodule `N` contained in the `F`-span of an `R`-submodule `M` is carried into `M` by
multiplication by a single element of `S`. -/
theorem FG.exists_smul_mem_of_le_span {N : Submodule R E} (hN : N.FG)
    (hle : (N : Set E) ⊆ span F (M : Set E)) : ∃ r ∈ S, ∀ v ∈ N, r • v ∈ M := by
  induction N, hN using fg_induction with
  | singleton x =>
    obtain ⟨r, hr, hrx⟩ := exists_smul_mem_of_mem_span S (hle (mem_span_singleton_self x))
    refine ⟨r, hr, fun v hv => ?_⟩
    obtain ⟨c, rfl⟩ := mem_span_singleton.1 hv
    rw [smul_comm]
    exact smul_mem _ c hrx
  | sup N₁ N₂ _ _ h₁ h₂ =>
    obtain ⟨r₁, hr₁, h₁⟩ := h₁ fun v hv => hle (mem_sup_left hv)
    obtain ⟨r₂, hr₂, h₂⟩ := h₂ fun v hv => hle (mem_sup_right hv)
    refine ⟨r₂ * r₁, mul_mem hr₂ hr₁, fun v hv => ?_⟩
    obtain ⟨v₁, hv₁, v₂, hv₂, rfl⟩ := mem_sup.1 hv
    rw [smul_add, mul_smul, mul_comm, mul_smul]
    exact add_mem (smul_mem _ r₂ (h₁ v₁ hv₁)) (smul_mem _ r₁ (h₂ v₂ hv₂))

end ClearDenominators

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
    obtain ⟨s, hs, hs1⟩ := exists_smul_mem_of_mem_span R⁰ (hspan 1)
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
