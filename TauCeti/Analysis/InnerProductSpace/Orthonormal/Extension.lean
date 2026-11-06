/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Extending orthonormal families to orthonormal bases and isometries

A finite orthonormal family `v : κ → E` of a finite-dimensional inner product space extends to an
orthonormal basis indexed by any type `ι` of cardinality `finrank 𝕜 E`, along any injection
`f : κ → ι` (`Orthonormal.exists_orthonormalBasis_comp_eq`). Mathlib's
`Orthonormal.exists_orthonormalBasis_extension_of_card_eq` states this for a family indexed by `ι`
itself and orthonormal on a subset; the form here is the one used to compare two orthonormal
families indexed by the same type.

Extending two orthonormal families `v` and `w`, indexed by the same finite type, to orthonormal
bases along the same injection, the linear isometry exchanging the two bases carries `v` to `w`
(`Orthonormal.exists_linearIsometryEquiv_comp_eq`). So the linear isometry group of a
finite-dimensional inner product space acts transitively on its orthonormal families of any given
finite length.
-/

public section

open Function Module Set

namespace Orthonormal

variable {𝕜 E κ : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] {v : κ → E}

/-- A finite orthonormal family of a finite-dimensional space extends to an orthonormal basis
indexed by any type of cardinality the dimension, along any injection into that type. -/
theorem exists_orthonormalBasis_comp_eq (hv : Orthonormal 𝕜 v) {ι : Type*} [Fintype ι]
    (hι : finrank 𝕜 E = Fintype.card ι) {f : κ → ι} (hf : Injective f) :
    ∃ b : OrthonormalBasis ι 𝕜 E, b ∘ f = v := by
  classical
  -- Extend `v` by zero outside the image of `f`; on that image it is `v` reindexed.
  have hv' : Orthonormal 𝕜 ((range f).domRestrict (extend f v 0)) := by
    have : (range f).domRestrict (extend f v 0) = v ∘ (Equiv.ofInjective f hf).symm := by
      funext x
      obtain ⟨_, i, rfl⟩ := x
      simp [hf.extend_apply]
    rw [this]
    exact hv.comp _ (Equiv.injective _)
  obtain ⟨b, hb⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq hι hv'
  exact ⟨b, funext fun i ↦ (hb (f i) (mem_range_self i)).trans (hf.extend_apply _ _ i)⟩

/-- **Linear isometries act transitively on orthonormal families**: two orthonormal families of
a finite-dimensional space indexed by the same finite type differ by a linear isometry. -/
theorem exists_linearIsometryEquiv_comp_eq [Finite κ] (hv : Orthonormal 𝕜 v) {w : κ → E}
    (hw : Orthonormal 𝕜 w) : ∃ e : E ≃ₗᵢ[𝕜] E, e ∘ v = w := by
  have := Fintype.ofFinite κ
  have hκ : Fintype.card κ ≤ finrank 𝕜 E := hv.linearIndependent.fintype_card_le_finrank
  have hι : finrank 𝕜 E = Fintype.card (Fin (finrank 𝕜 E)) := (Fintype.card_fin _).symm
  have hf : Injective (Fin.castLE hκ ∘ Fintype.equivFin κ) :=
    (Fin.castLE_injective hκ).comp (Fintype.equivFin κ).injective
  obtain ⟨bv, hbv⟩ := hv.exists_orthonormalBasis_comp_eq hι hf
  obtain ⟨bw, hbw⟩ := hw.exists_orthonormalBasis_comp_eq hι hf
  refine ⟨bv.equiv bw (Equiv.refl _), ?_⟩
  rw [← hbv, ← hbw]
  funext i
  simp

end Orthonormal
