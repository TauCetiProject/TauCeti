/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.NumberTheory.ModularForms.Fricke.Involution

/-!
# The Fricke operator on nebentypus character spaces

The Fricke operator `W_N` of `TauCeti/NumberTheory/ModularForms/Fricke/Operator.lean` shifts the
diamond label by an inverse, `W_N ∘ ⟨d⟩ = ⟨d⁻¹⟩ ∘ W_N` (`frickeOperator_diamondOp`). Read on the
nebentypus relation itself, where `W_N` moves `g ∈ Γ₀(N)` across it as a matrix with the inverse
label, this is a statement about nebentypus that needs no holomorphy: the slash by `W_N` carries
the `χ`-invariant functions into the `χ⁻¹`-invariant ones, so `W_N` carries `M_k(Γ₁(N), χ)` into
`M_k(Γ₁(N), χ⁻¹)`. Since `W_N ∘ W_N` is the nonzero scalar `frickeScalar N k`
(`frickeOperator_frickeOperator_apply`), that transport is an isomorphism.

## Main definitions

* `TauCeti.frickeCharRestrict`, `TauCeti.frickeCharCuspRestrict`: `W_N` restricted to the
  `χ`-nebentypus space, landing in the `χ⁻¹`-nebentypus space, on modular and on cusp forms.
* `TauCeti.frickeCharEquiv`, `TauCeti.frickeCharCuspEquiv`: those restrictions bundled as linear
  isomorphisms `M_k(Γ₁(N), χ) ≃ₗ[ℂ] M_k(Γ₁(N), χ⁻¹)` and `S_k(Γ₁(N), χ) ≃ₗ[ℂ] S_k(Γ₁(N), χ⁻¹)`,
  with inverse `(frickeScalar N k)⁻¹ • W_N`.

## Main results

* `TauCeti.slash_frickeGL_mem_functionCharSpace`: the transport for a bare function, the slash
  by `W_N` maps the `χ`-invariant functions of weight `k` for `Γ₀(N)` into the `χ⁻¹`-invariant
  ones. It needs no holomorphy.
* `TauCeti.frickeOperator_mem_modFormCharSpace`,
  `TauCeti.frickeOperatorCusp_mem_cuspFormCharSpace`: the transport on forms, `W_N` maps the
  `χ`-nebentypus space into the `χ⁻¹`-nebentypus space; these read the function statement on
  the underlying function.

## The inverse character

The target character is mathlib's `χ⁻¹`, the inverse in the commutative group `(ZMod N)ˣ →* ℂˣ`
(`MonoidHom.instCommGroup`), for which `MonoidHom.inv_apply` gives `χ⁻¹ d = (χ d)⁻¹`. The source
introduces a named `chiConj χ = χ.comp invMonoidHom` for this; that is the same monoid hom —
`χ d⁻¹ = (χ d)⁻¹` is `map_inv` — so no definition is made here, matching the `χ⁻¹` spelling
already used in the module docstring of `Fricke/Operator.lean`.

The round trip `χ⁻¹⁻¹ = χ` that a two-sided inverse needs is `inv_inv_monoidHom` below. That is
mathlib's `inv_inv` mathematically, but `inv_inv` is stated for `InvolutiveInv` and does not match
the `Inv (M →* G)` instance path syntactically, so it is proved pointwise instead, where the
inversion happens in `ℂˣ`.

## Provenance

Ported from the AINTLIB `LeanModularForms` project
([`LeanModularForms/HeckeRIngs/GL2/Fricke.lean`](https://github.com/CBirkbeck/AINTLIB),
commit `340875adfb2`, Apache-2.0, Chris Birkbeck).

Three changes from the source. Its `chiConj` is dropped in favour of mathlib's `χ⁻¹`, as above.
Its `private frickeOperator_sq_apply` is dropped: `frickeOperator_frickeOperator_apply` of
`Fricke/Involution.lean` is that statement, already public. And the cusp-form halves, which the
source does not carry, are included here, since `cuspFormCharSpace` and
`frickeOperatorCusp_diamondOpCusp` are both available and every other result in this Fricke
development is stated on modular and on cusp forms alike.

## References

* [F. Diamond and J. Shurman, *A First Course in Modular Forms*][diamondshurman2005], §5.
-/

open Matrix Matrix.SpecialLinearGroup CongruenceSubgroup UpperHalfPlane

open scoped MatrixGroups ModularForm

namespace TauCeti

/-- The character round trip `χ⁻¹⁻¹ = χ`, proved pointwise.

This is mathlib's `inv_inv` mathematically, but that lemma is stated for `InvolutiveInv` and does
not match the `Inv (M →* G)` instance path syntactically, so neither `rw` nor `simp` closes the
goal with it. Proving it pointwise reduces to `inv_inv` in `ℂˣ`, which is a genuine group. -/
private theorem inv_inv_monoidHom {N : ℕ} (χ : (ZMod N)ˣ →* ℂˣ) : χ⁻¹⁻¹ = χ := by
  ext d
  simp

variable {N : ℕ} [NeZero N]

/-- **The Fricke slash shifts the nebentypus to its inverse, on functions**: the slash by `W`
carries a `χ`-invariant function of weight `k` for `Γ₀(N)` to a `χ⁻¹`-invariant one.

`W` moves `g ∈ Γ₀(N)` across it as `frickeConjSL g` (`frickeGL_mul_mapGL`), whose diamond label
is the inverse of that of `g` (`toHomUnits_gamma0Map_frickeConjGamma0_eq_inv`). No analytic
condition on `f` is involved. -/
public theorem slash_frickeGL_mem_functionCharSpace {k : ℤ} {χ : (ZMod N)ˣ →* ℂˣ} {f : ℍ → ℂ}
    (hf : f ∈ functionCharSpace k χ) : f ∣[k] frickeGL ℝ N ∈ functionCharSpace k χ⁻¹ := by
  refine (mem_functionCharSpace_iff _ _ _).mpr fun g ↦ ?_
  rw [← SlashAction.slash_mul, frickeGL_mul_mapGL, SlashAction.slash_mul, ← coe_frickeConjGamma0,
    slash_mapGL_eq_smul_of_mem_functionCharSpace hf,
    ModularForm.smul_slash_of_det_pos k val_det_frickeGL_pos,
    toHomUnits_gamma0Map_frickeConjGamma0_eq_inv, map_inv, MonoidHom.inv_apply]

/-- **The Fricke operator shifts the nebentypus to its inverse**: it carries `M_k(Γ₁(N), χ)` into
`M_k(Γ₁(N), χ⁻¹)`. This is `slash_frickeGL_mem_functionCharSpace` read on the underlying
function. -/
public theorem frickeOperator_mem_modFormCharSpace (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ)
    {f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k} (hf : f ∈ modFormCharSpace k χ) :
    frickeOperator k f ∈ modFormCharSpace k χ⁻¹ := by
  rw [← coe_mem_functionCharSpace_iff, coe_frickeOperator]
  exact slash_frickeGL_mem_functionCharSpace ((coe_mem_functionCharSpace_iff k χ f).mpr hf)

/-- **The Fricke operator shifts the nebentypus to its inverse, on cusp forms**: it carries
`S_k(Γ₁(N), χ)` into `S_k(Γ₁(N), χ⁻¹)`. The cusp-form counterpart of
`frickeOperator_mem_modFormCharSpace`. -/
public theorem frickeOperatorCusp_mem_cuspFormCharSpace (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ)
    {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k} (hf : f ∈ cuspFormCharSpace k χ) :
    frickeOperatorCusp k f ∈ cuspFormCharSpace k χ⁻¹ := by
  rw [← coe_mem_functionCharSpace_iff_mem_cuspFormCharSpace, coe_frickeOperatorCusp]
  exact slash_frickeGL_mem_functionCharSpace
    ((coe_mem_functionCharSpace_iff_mem_cuspFormCharSpace k χ f).mpr hf)

/-- **The Fricke operator restricted to a nebentypus space**, as a `ℂ`-linear map
`M_k(Γ₁(N), χ) →ₗ[ℂ] M_k(Γ₁(N), χ⁻¹)`.

This is `frickeOperator` cut down by `LinearMap.restrict`. -/
public noncomputable def frickeCharRestrict (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ) :
    modFormCharSpace k χ →ₗ[ℂ] modFormCharSpace k χ⁻¹ :=
  (frickeOperator k).restrict fun _ hf ↦ frickeOperator_mem_modFormCharSpace k χ hf

/-- On underlying modular forms, `frickeCharRestrict` is `frickeOperator`. -/
@[simp]
public theorem coe_frickeCharRestrict_apply (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ)
    (f : modFormCharSpace k χ) :
    ((frickeCharRestrict k χ f : modFormCharSpace k χ⁻¹) :
        ModularForm ((Gamma1 N).map (mapGL ℝ)) k) =
      frickeOperator k (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) :=
  -- Naming the restriction as a `def` destroys the `LinearMap.restrict` head symbol, so
  -- `LinearMap.coe_restrict_apply` does not fire as a `simp` lemma; it still applies by name.
  LinearMap.coe_restrict_apply _ _

/-- **The Fricke operator restricted to a nebentypus space of cusp forms**, as a `ℂ`-linear map
`S_k(Γ₁(N), χ) →ₗ[ℂ] S_k(Γ₁(N), χ⁻¹)`. The cusp-form counterpart of `frickeCharRestrict`. -/
public noncomputable def frickeCharCuspRestrict (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ) :
    cuspFormCharSpace k χ →ₗ[ℂ] cuspFormCharSpace k χ⁻¹ :=
  (frickeOperatorCusp k).restrict fun _ hf ↦ frickeOperatorCusp_mem_cuspFormCharSpace k χ hf

/-- On underlying cusp forms, `frickeCharCuspRestrict` is `frickeOperatorCusp`. The cusp-form
counterpart of `coe_frickeCharRestrict_apply`, stated for the same reason. -/
@[simp]
public theorem coe_frickeCharCuspRestrict_apply (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ)
    (f : cuspFormCharSpace k χ) :
    ((frickeCharCuspRestrict k χ f : cuspFormCharSpace k χ⁻¹) :
        CuspForm ((Gamma1 N).map (mapGL ℝ)) k) =
      frickeOperatorCusp k (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :=
  LinearMap.coe_restrict_apply _ _

/-- **The Fricke automorphism carries the `χ`-space onto the `χ⁻¹`-space.** The surjective
refinement of `frickeOperator_mem_modFormCharSpace`, which gives only the forward inclusion. -/
@[simp]
public theorem map_frickeOperatorEquiv_modFormCharSpace (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ) :
    (modFormCharSpace k χ).map (frickeOperatorEquiv (N := N) k : _ →ₗ[ℂ] _) =
      modFormCharSpace k χ⁻¹ := by
  refine le_antisymm ?_ fun g hg ↦ ?_
  · rintro _ ⟨f, hf, rfl⟩
    simpa using frickeOperator_mem_modFormCharSpace k χ hf
  -- The reverse inclusion is the same statement read at `χ⁻¹`, via `χ⁻¹⁻¹ = χ` and closure
  -- of the space under the scalar.
  · refine ⟨(frickeOperatorEquiv (N := N) k).symm g, ?_,
      by simp [smul_smul, inv_mul_cancel₀ (frickeScalar_ne_zero (N := N) k)]⟩
    have h := frickeOperator_mem_modFormCharSpace k χ⁻¹ hg
    rw [inv_inv_monoidHom] at h
    simpa using Submodule.smul_mem _ ((frickeScalar N k)⁻¹) h

/-- **The Fricke isomorphism between nebentypus spaces**
`M_k(Γ₁(N), χ) ≃ₗ[ℂ] M_k(Γ₁(N), χ⁻¹)`.

The ambient automorphism `frickeOperatorEquiv` restricted to the pair of character spaces it
matches up. -/
public noncomputable def frickeCharEquiv (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ) :
    modFormCharSpace k χ ≃ₗ[ℂ] modFormCharSpace k χ⁻¹ :=
  (frickeOperatorEquiv (N := N) k).ofSubmodules _ _
    (map_frickeOperatorEquiv_modFormCharSpace k χ)

/-- On underlying modular forms, `frickeCharEquiv` is `frickeOperator`. -/
@[simp]
public theorem coe_frickeCharEquiv_apply (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ)
    (f : modFormCharSpace k χ) :
    ((frickeCharEquiv k χ f : modFormCharSpace k χ⁻¹) :
        ModularForm ((Gamma1 N).map (mapGL ℝ)) k) =
      frickeOperator k (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) := by
  simp [frickeCharEquiv]

/-- On underlying modular forms, the inverse of `frickeCharEquiv` is
`(frickeScalar N k)⁻¹ • frickeOperator`. -/
@[simp]
public theorem coe_frickeCharEquiv_symm_apply (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ)
    (g : modFormCharSpace k χ⁻¹) :
    (((frickeCharEquiv k χ).symm g : modFormCharSpace k χ) :
        ModularForm ((Gamma1 N).map (mapGL ℝ)) k) =
      (frickeScalar N k)⁻¹ • frickeOperator k (g : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) := by
  simp [frickeCharEquiv]

/-- **The Fricke automorphism carries the `χ`-space of cusp forms onto the `χ⁻¹`-space.** The
cusp-form counterpart of `map_frickeOperatorEquiv_modFormCharSpace`. -/
@[simp]
public theorem map_frickeOperatorCuspEquiv_cuspFormCharSpace (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ) :
    (cuspFormCharSpace k χ).map (frickeOperatorCuspEquiv (N := N) k : _ →ₗ[ℂ] _) =
      cuspFormCharSpace k χ⁻¹ := by
  refine le_antisymm ?_ fun g hg ↦ ?_
  · rintro _ ⟨f, hf, rfl⟩
    simpa using frickeOperatorCusp_mem_cuspFormCharSpace k χ hf
  · refine ⟨(frickeOperatorCuspEquiv (N := N) k).symm g, ?_,
      by simp [smul_smul, inv_mul_cancel₀ (frickeScalar_ne_zero (N := N) k)]⟩
    have h := frickeOperatorCusp_mem_cuspFormCharSpace k χ⁻¹ hg
    rw [inv_inv_monoidHom] at h
    simpa using Submodule.smul_mem _ ((frickeScalar N k)⁻¹) h

/-- **The Fricke isomorphism between nebentypus spaces of cusp forms**
`S_k(Γ₁(N), χ) ≃ₗ[ℂ] S_k(Γ₁(N), χ⁻¹)`. The cusp-form counterpart of `frickeCharEquiv`. -/
public noncomputable def frickeCharCuspEquiv (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ) :
    cuspFormCharSpace k χ ≃ₗ[ℂ] cuspFormCharSpace k χ⁻¹ :=
  (frickeOperatorCuspEquiv (N := N) k).ofSubmodules _ _
    (map_frickeOperatorCuspEquiv_cuspFormCharSpace k χ)

/-- On underlying cusp forms, `frickeCharCuspEquiv` is `frickeOperatorCusp`. -/
@[simp]
public theorem coe_frickeCharCuspEquiv_apply (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ)
    (f : cuspFormCharSpace k χ) :
    ((frickeCharCuspEquiv k χ f : cuspFormCharSpace k χ⁻¹) :
        CuspForm ((Gamma1 N).map (mapGL ℝ)) k) =
      frickeOperatorCusp k (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) := by
  simp [frickeCharCuspEquiv]

/-- On underlying cusp forms, the inverse of `frickeCharCuspEquiv` is
`(frickeScalar N k)⁻¹ • frickeOperatorCusp`. -/
@[simp]
public theorem coe_frickeCharCuspEquiv_symm_apply (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ)
    (g : cuspFormCharSpace k χ⁻¹) :
    (((frickeCharCuspEquiv k χ).symm g : cuspFormCharSpace k χ) :
        CuspForm ((Gamma1 N).map (mapGL ℝ)) k) =
      (frickeScalar N k)⁻¹ • frickeOperatorCusp k (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) := by
  simp [frickeCharCuspEquiv]

end TauCeti
