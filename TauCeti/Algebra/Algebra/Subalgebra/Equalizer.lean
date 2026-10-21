/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Basic

/-!
# Transporting equalizers along isomorphisms

Mathlib's `AlgHom.equalizer f g` is the subalgebra of `A` on which two algebra maps
`f g : A →ₐ[R] B` agree. Isomorphisms `eA : A ≃ₐ[R] A'` and `eB : B ≃ₐ[R] B'` transport `f` and
`g` to maps `A' →ₐ[R] B'`, and `eA` restricts to an isomorphism between the two equalizers
(`AlgHom.equalizerCongr`). This lets an equalizer be computed after replacing the source and the
target by isomorphic models.
-/

public section

namespace AlgHom

variable {R A B A' B' : Type*} [CommSemiring R] [Semiring A] [Semiring B] [Semiring A']
  [Semiring B'] [Algebra R A] [Algebra R B] [Algebra R A'] [Algebra R B']

/-- Transport of an equalizer along isomorphisms of the source and the target: `eA` restricts to
an isomorphism from `equalizer f g` to the equalizer of the transported maps. -/
noncomputable def equalizerCongr (eA : A ≃ₐ[R] A') (eB : B ≃ₐ[R] B') (f g : A →ₐ[R] B) :
    equalizer f g ≃ₐ[R]
      equalizer ((eB : B →ₐ[R] B').comp (f.comp (eA.symm : A' →ₐ[R] A)))
        ((eB : B →ₐ[R] B').comp (g.comp (eA.symm : A' →ₐ[R] A))) :=
  (eA.subalgebraMap (equalizer f g)).trans <| Subalgebra.equivOfEq _ _ <| by
    ext x
    simp only [Subalgebra.mem_map, mem_equalizer, coe_comp, Function.comp_apply,
      AlgEquiv.coe_toAlgHom, EmbeddingLike.apply_eq_iff_eq]
    exact ⟨fun ⟨y, hy, hyx⟩ ↦ hyx ▸ by simpa using hy, fun h ↦ ⟨_, h, by simp⟩⟩

/-- The transport of an equalizer is `eA` on underlying elements. -/
@[simp]
theorem coe_equalizerCongr_apply (eA : A ≃ₐ[R] A') (eB : B ≃ₐ[R] B') (f g : A →ₐ[R] B)
    (x : equalizer f g) : (equalizerCongr eA eB f g x : A') = eA x := by
  simp [equalizerCongr]

end AlgHom
