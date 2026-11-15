/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.ExteriorPower.FreeShortExact

/-!
# Top exterior powers of a short exact sequence

For a short exact sequence `0 → U → V → W → 0` of finite-dimensional vector spaces, with maps
`f : U → V` and `g : V → W`, write `a = dim U` and `c = dim W`. There is a canonical isomorphism
of lines
`⋀ᵃ U ⊗ ⋀ᶜ W ≃ ⋀ᵃ⁺ᶜ V`, `(u₁ ∧ ⋯ ∧ uₐ) ⊗ (w₁ ∧ ⋯ ∧ w_c) ↦ f u₁ ∧ ⋯ ∧ f uₐ ∧ v₁ ∧ ⋯ ∧ v_c`,
where `vⱼ` is any lift of `wⱼ` along `g`. Since `a + c = dim V`, this identifies the tensor product
of the top exterior powers of `U` and `W` with the top exterior power of `V`. The factor of the
subspace comes first.

For the analogous comparison over a commutative ring with explicit finite bases, see
`TauCeti.exteriorPower.shortExactEquivOfBasis`.

This is the determinant-line identity `det V ≅ det U ⊗ det W`. It is the linear-algebra input for
comparing determinant lines along exact sequences, such as the kernel/cokernel sequence of a
stabilized Fredholm operator, and for orienting a vector space from orientations of a subspace and
of the quotient.

## Main declarations

* `TauCeti.exteriorPower.shortExactEquiv`: the isomorphism `⋀ᵃ U ⊗ ⋀ᶜ W ≃ ⋀ᵃ⁺ᶜ V`.
* `TauCeti.exteriorPower.shortExactEquiv_tmul_ιMulti`: its value on exterior products, for
  arbitrary lifts.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications **52**, 2012, Appendix A.2 (determinant lines of exact sequences).
-/

public section

open Module TensorProduct exteriorPower

namespace TauCeti

namespace exteriorPower

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

variable {U W : Type*} [AddCommGroup U] [Module K U] [AddCommGroup W] [Module K W]
  {f : U →ₗ[K] V} {g : V →ₗ[K] W}

/-- For a short exact sequence `0 → U → V → W → 0` of finite-dimensional vector spaces, the
canonical isomorphism `⋀ᵃ U ⊗ ⋀ᶜ W ≃ ⋀ᵃ⁺ᶜ V`, where `a = dim U` and `c = dim W`. It sends
`(u₁ ∧ ⋯ ∧ uₐ) ⊗ (w₁ ∧ ⋯ ∧ w_c)` to `f u₁ ∧ ⋯ ∧ f uₐ ∧ v₁ ∧ ⋯ ∧ v_c` for any lifts `vⱼ` of the
`wⱼ` along `g` (`TauCeti.exteriorPower.shortExactEquiv_tmul_ιMulti`). -/
noncomputable def shortExactEquiv [FiniteDimensional K U] [FiniteDimensional K W]
    (hf : Function.Injective f) (hfg : Function.Exact f g) (hg : Function.Surjective g) :
    ⋀[K]^(finrank K U) U ⊗[K] ⋀[K]^(finrank K W) W ≃ₗ[K]
      ⋀[K]^(finrank K U + finrank K W) V :=
  shortExactEquivOfBasis hf hfg hg (Module.finBasis K U) (Module.finBasis K W)

variable [FiniteDimensional K U] [FiniteDimensional K W] (hf : Function.Injective f)
  (hfg : Function.Exact f g) (hg : Function.Surjective g)

/-- `TauCeti.exteriorPower.shortExactEquiv` sends `(u₁ ∧ ⋯ ∧ uₐ) ⊗ (w₁ ∧ ⋯ ∧ w_c)` to
`f u₁ ∧ ⋯ ∧ f uₐ ∧ v₁ ∧ ⋯ ∧ v_c` for every choice of lifts `vⱼ` of the `wⱼ` along `g`. -/
theorem shortExactEquiv_tmul_ιMulti (u : Fin (finrank K U) → U) (w : Fin (finrank K W) → W)
    (v : Fin (finrank K W) → V) (hv : ∀ j, g (v j) = w j) :
    shortExactEquiv hf hfg hg (ιMulti K _ u ⊗ₜ ιMulti K _ w) =
      ιMulti K _ (Fin.append (f ∘ u) v) := by
  have hgv : g ∘ v = w := funext hv
  rw [← hgv]
  exact shortExactEquivOfBasis_tmul_ιMulti hf hfg hg
    (Module.finBasis K U) (Module.finBasis K W) u v

/-- `TauCeti.exteriorPower.shortExactEquiv` sends `(u₁ ∧ ⋯ ∧ uₐ) ⊗ (g v₁ ∧ ⋯ ∧ g v_c)` to
`f u₁ ∧ ⋯ ∧ f uₐ ∧ v₁ ∧ ⋯ ∧ v_c`. -/
@[simp]
theorem shortExactEquiv_tmul_ιMulti_comp (u : Fin (finrank K U) → U)
    (v : Fin (finrank K W) → V) :
    shortExactEquiv hf hfg hg (ιMulti K _ u ⊗ₜ ιMulti K _ (g ∘ v)) =
      ιMulti K _ (Fin.append (f ∘ u) v) :=
  shortExactEquiv_tmul_ιMulti hf hfg hg u _ v fun _ ↦ rfl

/-- The inverse of `TauCeti.exteriorPower.shortExactEquiv` splits
`f u₁ ∧ ⋯ ∧ f uₐ ∧ v₁ ∧ ⋯ ∧ v_c` as `(u₁ ∧ ⋯ ∧ uₐ) ⊗ (g v₁ ∧ ⋯ ∧ g v_c)`. -/
@[simp]
theorem shortExactEquiv_symm_ιMulti (u : Fin (finrank K U) → U) (v : Fin (finrank K W) → V) :
    (shortExactEquiv hf hfg hg).symm (ιMulti K _ (Fin.append (f ∘ u) v)) =
      ιMulti K _ u ⊗ₜ ιMulti K _ (g ∘ v) :=
  (LinearEquiv.symm_apply_eq _).2 (shortExactEquiv_tmul_ιMulti_comp hf hfg hg u v).symm

end exteriorPower

end TauCeti
