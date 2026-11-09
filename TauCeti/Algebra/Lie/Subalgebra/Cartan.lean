/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.CartanSubalgebra

/-!
# Cartan subalgebras under Lie algebra equivalences

An equivalence of Lie algebras `e : L ≃ₗ⁅R⁆ L'` carries the normalizer of a Lie subalgebra `H` to
the normalizer of its image (`LieSubalgebra.normalizer_map_lieEquiv`), and `H` to an isomorphic
Lie algebra. Hence `H` is a Cartan subalgebra exactly when its image is
(`LieSubalgebra.isCartanSubalgebra_map_lieEquiv_iff`).
-/

public section

namespace LieSubalgebra

variable {R L L' : Type*} [CommRing R] [LieRing L] [LieAlgebra R L] [LieRing L']
  [LieAlgebra R L'] (e : L ≃ₗ⁅R⁆ L') (H : LieSubalgebra R L)

private theorem mem_map_lieEquiv_iff (K : LieSubalgebra R L) (y : L') :
    y ∈ K.map (e : L →ₗ⁅R⁆ L') ↔ e.symm y ∈ K :=
  ⟨fun ⟨z, hz, hzy⟩ ↦ by simpa [← hzy] using hz, fun hy ↦ ⟨e.symm y, hy, by simp⟩⟩

/-- An equivalence of Lie algebras carries the normalizer of a Lie subalgebra to the normalizer of
its image. -/
theorem normalizer_map_lieEquiv :
    (H.map (e : L →ₗ⁅R⁆ L')).normalizer = H.normalizer.map (e : L →ₗ⁅R⁆ L') := by
  ext x
  rw [mem_map_lieEquiv_iff e, mem_normalizer_iff, mem_normalizer_iff]
  refine ⟨fun h y hy ↦ ?_, fun h y hy ↦ ?_⟩
  · have := h (e y) ((mem_map_lieEquiv_iff e H _).2 (by simpa using hy))
    rwa [mem_map_lieEquiv_iff e, LieEquiv.map_lie, LieEquiv.symm_apply_apply] at this
  · rw [mem_map_lieEquiv_iff e, LieEquiv.map_lie]
    exact h _ ((mem_map_lieEquiv_iff e H _).1 hy)

/-- **Cartan subalgebras are preserved by Lie algebra equivalences.** The image of a Lie subalgebra
`H` under an equivalence of Lie algebras is a Cartan subalgebra exactly when `H` is. -/
theorem isCartanSubalgebra_map_lieEquiv_iff :
    (H.map (e : L →ₗ⁅R⁆ L')).IsCartanSubalgebra ↔ H.IsCartanSubalgebra := by
  have hnil : LieRing.IsNilpotent (H.map (e : L →ₗ⁅R⁆ L')) ↔ LieRing.IsNilpotent H :=
    (e.lieSubalgebraMap H).nilpotent_iff_equiv_nilpotent.symm
  have hnorm : (H.map (e : L →ₗ⁅R⁆ L')).normalizer = H.map (e : L →ₗ⁅R⁆ L') ↔
      H.normalizer = H := by
    rw [normalizer_map_lieEquiv]
    refine ⟨fun h ↦ ?_, fun h ↦ by rw [h]⟩
    ext x
    simpa [mem_map_lieEquiv_iff] using SetLike.ext_iff.1 h (e x)
  exact ⟨fun ⟨h₁, h₂⟩ ↦ ⟨hnil.1 h₁, hnorm.1 h₂⟩, fun ⟨h₁, h₂⟩ ↦ ⟨hnil.2 h₁, hnorm.2 h₂⟩⟩

end LieSubalgebra
