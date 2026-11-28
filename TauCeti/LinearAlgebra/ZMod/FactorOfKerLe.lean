/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.Module.Submodule.Ker

import Mathlib.Algebra.Module.ZMod
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Factoring linear and additive maps through `ZMod p`-vector spaces

Given maps `β` and `f` out of the same domain such that `ker β ≤ ker f`, `f` factors through `β`
by a linear map whenever the codomain of `β` is a vector space over a division ring (in particular
over `ZMod p` for a prime `p`).

## Main results

* `TauCeti.exists_linearMap_comp_eq_of_ker_le`: over a division ring `K`, if `β : A →ₗ[K] B` and
  `f : A →ₗ[K] V` satisfy `LinearMap.ker β ≤ LinearMap.ker f`, then `∃ v : B →ₗ[K] V, v.comp β = f`.
* `TauCeti.exists_zmod_linearMap_factor_of_ker_le`: for a prime `p`, an additive group `A`, and
  `ZMod p`-vector spaces `B` and `V`, if `β : A →+ B` and `f : A →+ V` satisfy
  `∀ y, β y = 0 → f y = 0`, then `∃ v : B →ₗ[ZMod p] V, ∀ y, v (β y) = f y`.

## References

* `grh-lean`, https://github.com/lsernau/grh-lean (commit
  `72fead102f663d5c7a407964a13dc0cf9d977207`), file
  `src/Lib/ClassField/GreenbergWiles/CocycleCounts.lean` (declaration
  `New.IsLargeLevel.exists_linearMap_factor_of_ker_le`); Apache 2.0, Copyright 2026 Anthropic, PBC.
-/

public section

namespace TauCeti

/-- Over a division ring `K`, if `β : A →ₗ[K] B` and `f : A →ₗ[K] V` satisfy
`LinearMap.ker β ≤ LinearMap.ker f`, then `f` factors as `v.comp β` for some `v : B →ₗ[K] V`. -/
theorem exists_linearMap_comp_eq_of_ker_le {K A B V : Type*} [DivisionRing K]
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup V]
    [Module K A] [Module K B] [Module K V]
    (β : A →ₗ[K] B) (f : A →ₗ[K] V) (h_ker : LinearMap.ker β ≤ LinearMap.ker f) :
    ∃ v : B →ₗ[K] V, v.comp β = f := by
  let v₀ : LinearMap.range β →ₗ[K] V :=
    (Submodule.liftQ (LinearMap.ker β) f h_ker).comp β.quotKerEquivRange.symm.toLinearMap
  obtain ⟨v, hv⟩ := LinearMap.exists_extend v₀
  refine ⟨v, LinearMap.ext fun y ↦ ?_⟩
  have h_eq : v (β y) = v₀ (β.rangeRestrict y) := LinearMap.congr_fun hv (β.rangeRestrict y)
  have hq : β.quotKerEquivRange.symm (β.rangeRestrict y) = Submodule.Quotient.mk y :=
    β.quotKerEquivRange_symm_apply_image y (LinearMap.mem_range_self β y)
  simpa [v₀, hq] using h_eq

/-- Let `β : A →+ B` and `f : A →+ V` be additive homomorphisms from an additive commutative group
`A` into vector spaces `B` and `V` over `ZMod p` (`p` prime). If `f` vanishes wherever `β` does,
then `f = v ∘ β` for some `ZMod p`-linear map `v : B →ₗ[ZMod p] V`. -/
theorem exists_zmod_linearMap_factor_of_ker_le {p : ℕ} [Fact p.Prime] {A B V : Type*}
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup V]
    [Module (ZMod p) B] [Module (ZMod p) V]
    (β : A →+ B) (f : A →+ V) (h_ker : ∀ y : A, β y = 0 → f y = 0) :
    ∃ v : B →ₗ[ZMod p] V, ∀ y : A, v (β y) = f y := by
  have h_vanish : β.rangeRestrict.ker ≤ f.ker := by
    intro y hy
    exact h_ker y (congrArg Subtype.val hy)
  let v₀ : β.range →+ V := AddMonoidHom.liftOfSurjective _ β.rangeRestrict_surjective ⟨f, h_vanish⟩
  obtain ⟨v, hv⟩ := LinearMap.exists_extend (p := β.range.toZModSubmodule p)
    (v₀.toZModLinearMap p)
  refine ⟨v, fun y ↦ ?_⟩
  have h_eq : v (β y) = v₀ (β.rangeRestrict y) := LinearMap.congr_fun hv (β.rangeRestrict y)
  rw [h_eq]
  exact AddMonoidHom.liftOfRightInverse_comp_apply ..

end TauCeti
