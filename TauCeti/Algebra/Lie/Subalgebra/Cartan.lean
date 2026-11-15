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

/-- An equivalence of Lie algebras carries the normalizer of a Lie subalgebra to the normalizer of
its image. -/
theorem normalizer_map_lieEquiv :
    (H.map (e : L →ₗ⁅R⁆ L')).normalizer = H.normalizer.map (e : L →ₗ⁅R⁆ L') := by
  ext x
  rw [mem_map_submodule, Submodule.mem_map_equiv, mem_toSubmodule,
    mem_normalizer_iff, mem_normalizer_iff]
  have hsymm (y : L') : e.toLinearEquiv.symm y = e.symm y := rfl
  simp only [mem_map_submodule, Submodule.mem_map_equiv, mem_toSubmodule, hsymm]
  refine ⟨fun h y hy ↦ ?_, fun h y hy ↦ ?_⟩
  · simpa [LieEquiv.map_lie] using h (e y) (by simpa using hy)
  · simpa [LieEquiv.map_lie] using h _ hy

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
    simpa [mem_map_submodule, Submodule.mem_map_equiv] using SetLike.ext_iff.1 h (e x)
  exact ⟨fun ⟨h₁, h₂⟩ ↦ ⟨hnil.1 h₁, hnorm.1 h₂⟩, fun ⟨h₁, h₂⟩ ↦ ⟨hnil.2 h₁, hnorm.2 h₂⟩⟩

end LieSubalgebra
