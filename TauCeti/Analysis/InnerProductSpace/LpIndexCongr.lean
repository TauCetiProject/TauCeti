/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# Reindexing an `ℓ²` space along an equivalence of index sets

Mathlib builds `lp E p` for a family of normed spaces `E : α → Type*` and proves a great deal
about it, but it has no statement that an equivalence `α ≃ β` induces an isometry
`lp E p ≃ₗᵢ lp (E ∘ e.symm) p`.  For the constant family this is the reindexing that a
classification of Hilbert spaces by the size of a Hilbert basis needs: two bases with
equinumerous index sets give two `ℓ²` models, and only a reindexing puts them in the same
space so that `HilbertBasis.repr` can be composed.

`TauCeti.lpIndexCongr` is that reindexing at `p = 2` and a constant scalar family, which is the
case `HilbertBasis` produces.  Everything rests on two facts about unconditional sums:
`Equiv.summable_iff` transports membership, and `Equiv.tsum_eq` transports the norm.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Extraction class: **authored in place** for the Tau Ceti staging layer.
* Spectra influence: **none** -- this module imports only Mathlib.
-/

namespace TauCeti

open scoped ENNReal

variable {𝕜 : Type*} [RCLike 𝕜] {ι ι' : Type*}

private theorem two_toReal_pos : (0 : ℝ) < (2 : ℝ≥0∞).toReal := by norm_num

/-- Membership in `ℓ²` is invariant under reindexing: the summability that defines it is a
statement about an unconditional sum. -/
public theorem memℓp_comp_equiv (e : ι ≃ ι') {f : ι → 𝕜} (hf : Memℓp f 2) :
    Memℓp (fun i' => f (e.symm i')) 2 := by
  rw [memℓp_gen_iff two_toReal_pos] at hf ⊢
  exact (e.symm.summable_iff (f := fun i => ‖f i‖ ^ (2 : ℝ≥0∞).toReal)).mpr hf

/-- **An equivalence of index sets induces a linear isometric equivalence of `ℓ²` spaces.**

Composition with `e.symm` on functions; the two `Memℓp` obligations and the norm identity are
`Equiv.summable_iff` and `Equiv.tsum_eq` respectively. -/
public noncomputable def lpIndexCongr (𝕜 : Type*) [RCLike 𝕜] (e : ι ≃ ι') :
    lp (fun _ : ι => 𝕜) 2 ≃ₗᵢ[𝕜] lp (fun _ : ι' => 𝕜) 2 where
  toFun f := ⟨fun i' => (f : ι → 𝕜) (e.symm i'), memℓp_comp_equiv e (lp.memℓp f)⟩
  invFun g := ⟨fun i => (g : ι' → 𝕜) (e i), by
      have h := memℓp_comp_equiv e.symm (lp.memℓp g)
      rw [Equiv.symm_symm] at h
      exact h⟩
  left_inv f := by ext i; simp
  right_inv g := by ext i'; simp
  map_add' f g := by ext i'; rfl
  map_smul' c f := by ext i'; rfl
  norm_map' f := by
    rw [lp.norm_eq_tsum_rpow two_toReal_pos, lp.norm_eq_tsum_rpow two_toReal_pos]
    congr 1
    exact e.symm.tsum_eq fun i => ‖(f : ι → 𝕜) i‖ ^ (2 : ℝ≥0∞).toReal

/-! ## Hilbert bases with equinumerous index sets

The reindexing is what lets two Hilbert bases be compared: each identifies its space with an
`ℓ²` model, and an equivalence of the two index sets identifies the two models. -/

/-- **Two Hilbert spaces with equinumerous Hilbert bases are linearly isometric.**

`b.repr` and `b'.repr` land in different `ℓ²` spaces; `lpIndexCongr` is what puts them in the
same one. -/
public theorem nonempty_linearIsometryEquiv_of_hilbertBasis
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
    (b : HilbertBasis ι 𝕜 E) (b' : HilbertBasis ι' 𝕜 F) (e : ι ≃ ι') :
    Nonempty (E ≃ₗᵢ[𝕜] F) :=
  ⟨b.repr.trans ((lpIndexCongr 𝕜 e).trans b'.repr.symm)⟩

end TauCeti
