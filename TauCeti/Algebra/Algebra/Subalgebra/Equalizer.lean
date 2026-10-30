/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.Algebra.Algebra.Subalgebra.Operations

/-!
# Transporting equalizers along isomorphisms, and invariants as an equalizer

Mathlib's `AlgHom.equalizer f g` is the subalgebra of `A` on which two algebra maps
`f g : A →ₐ[R] B` agree. Isomorphisms `eA : A ≃ₐ[R] A'` and `eB : B ≃ₐ[R] B'` transport `f` and
`g` to maps `A' →ₐ[R] B'`, and `eA` restricts to an isomorphism between the two equalizers
(`AlgEquiv.equalizerCongr`). This lets an equalizer be computed after replacing the source
and the target by isomorphic models.

The invariant subalgebra `FixedPoints.subalgebra R S G` of a monoid `G` acting on `S` is the
equalizer of the diagonal map `S → (ι → S)` and `s ↦ (σ i • s)ᵢ`, for any family `σ : ι → G`
enumerating `G` (`TauCeti.FixedPoints.subalgebra_eq_equalizer`). Properties of equalizers
therefore pass to invariant subalgebras.
-/

public section

namespace AlgEquiv

open AlgHom

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

end AlgEquiv

namespace TauCeti.FixedPoints

/-- For a family `σ : ι → G` enumerating a monoid `G`, the invariant subalgebra is the equalizer of
the diagonal map `S → (ι → S)` and `s ↦ (σ i • s)ᵢ`. -/
theorem subalgebra_eq_equalizer {R S : Type*} [CommSemiring R] [Semiring S] [Algebra R S]
    (G : Type*) [Monoid G] [MulSemiringAction G S] [SMulCommClass G R S] {ι : Type*} {σ : ι → G}
    (hσ : Function.Surjective σ) :
    FixedPoints.subalgebra R S G = AlgHom.equalizer (AlgHom.pi fun _ ↦ AlgHom.id R S)
      (AlgHom.pi fun i ↦ MulSemiringAction.toAlgHom R S (σ i)) := by
  ext s
  simp only [FixedPoints.mem_subalgebra, AlgHom.mem_equalizer, funext_iff, AlgHom.pi_apply,
    AlgHom.id_apply, MulSemiringAction.toAlgHom_apply, hσ.forall]
  exact forall_congr' fun _ ↦ eq_comm

end TauCeti.FixedPoints
