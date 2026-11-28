/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.SesquilinearForm.Orthogonal
import Mathlib.LinearAlgebra.Dual.Lemmas
import TauCeti.LinearAlgebra.Basis.Semilinear
import TauCeti.LinearAlgebra.SesquilinearForm.Separating

/-!
# Dimension of sesquilinear orthogonal complements

A left-separating pairing identifies a subspace of its first argument with a subspace of the
second argument's dual; its orthogonal complement is the coannihilator of that image.
-/

public section

open Module

namespace Submodule

/-- For a left-separating pairing semilinear in its first argument, the dimension of a subspace
and that of its orthogonal complement add up to the dimension of the second space. -/
theorem finrank_add_finrank_orthogonalBilin {K V W : Type*} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    {σ : K ≃+* K} {B : V →ₛₗ[σ.toRingHom] W →ₗ[K] K} (S : Submodule K V)
    (hB : B.SeparatingLeft) : finrank K S + finrank K (S.orthogonalBilin B) = finrank K W := by
  let _ : RingHomSurjective σ.toRingHom := ⟨σ.surjective⟩
  let _ : RingHomSurjective σ.symm.toRingHom := ⟨σ.symm.surjective⟩
  let hp : RingHomInvPair σ.toRingHom σ.symm.toRingHom :=
    ⟨RingHom.ext σ.symm_apply_apply, RingHom.ext σ.apply_symm_apply⟩
  let _ : RingHomInvPair σ.symm.toRingHom σ.toRingHom := ⟨hp.comp_eq₂, hp.comp_eq⟩
  let f : S →ₛₗ[σ.toRingHom] Module.Dual K W := B.domRestrict S
  have hrange : LinearMap.range f = S.map B := LinearMap.range_domRestrict _ _
  have hf : Function.Injective f := hB.injective.comp S.subtype_injective
  have hdim : finrank K (S.map B) = finrank K S := by
    rw [← hrange]
    exact (LinearEquiv.ofInjective (σ₂₁ := σ.symm.toRingHom) f hf).finrank_eqₛₗ.symm
  rw [← dualCoannihilator_map_eq_orthogonalBilin (B := B), ← hdim]
  exact Subspace.finrank_add_finrank_dualCoannihilator_eq (S.map B)

end Submodule
