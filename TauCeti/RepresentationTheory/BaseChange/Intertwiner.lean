/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.BaseChange

/-!
# Intertwiners under free scalar extension

Let `ρ` and `σ` be representations of a monoid `G` over a commutative ring `K`, with `ρ` on a
finite projective `K`-module, and let `L` be a commutative `K`-algebra that is free as a
`K`-module (for instance any field extension of a field `K`). Then scalar extension commutes
with the space of intertwining maps:

```text
L ⊗[K] Hom_G(V, W) ≃ Hom_G(L ⊗[K] V, L ⊗[K] W)
```

(`Representation.intertwiningMapBaseChangeEquivOfFree`). Unlike
`Representation.intertwiningMapBaseChangeEquiv`, the monoid `G` need not be finite. Writing an
`L`-linear map `L ⊗ V → L ⊗ W` in a `K`-basis `(bᵢ)` of `L` as `∑ bᵢ ⊗ fᵢ` with `fᵢ : V → W`, it
intertwines the base-changed actions exactly when every coefficient `fᵢ` intertwines `ρ` and `σ`,
because the coefficients of the intertwining defect at `g` are the defects of the coefficients
(`Representation.intertwiningDefectAt_homBaseChangeEquiv`).

Over a field `K`, the dimension of every intertwiner space whose source is finite-dimensional is
therefore unchanged by any nonzero commutative `K`-algebra `L`
(`Representation.finrank_intertwiningMap_baseChange`).

## Main results

* `Representation.intertwiningMapBaseChangeEquivOfFree`: free scalar extension commutes with
  intertwiner spaces, for any monoid, with `intertwiningMapBaseChangeEquivOfFree_tmul` and
  `intertwiningMapBaseChangeEquivOfFree_symm_baseChange`.
* `Representation.finrank_intertwiningMap_baseChange`: over a field, the dimension of the
  intertwiner space from a finite-dimensional representation is unchanged by scalar extension.
-/

public section

open TensorProduct

namespace Representation

section Intertwiner

variable {K L G V W : Type*} [CommRing K] [CommRing L] [Algebra K L] [Monoid G]
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

variable [Module.Projective K V] [Module.Finite K V]

/-- Scalar extension of intertwining maps, `a ⊗ f ↦ a • (L ⊗ f)`, as an `L`-linear map. -/
private noncomputable def intertwiningMapBaseChangeHom (ρ : Representation K G V)
    (σ : Representation K G W) :
    L ⊗[K] IntertwiningMap ρ σ →ₗ[L] IntertwiningMap (baseChange L ρ) (baseChange L σ) where
  toFun x :=
    { toLinearMap := (LinearMap.isBaseChange_baseChangeHom K L V W).equiv
        ((IntertwiningMap.toLinearMapl (ρ := ρ) (σ := σ)).baseChange L x)
      isIntertwining' g := by
        have h0 : intertwiningDefectAt ρ σ g ∘ₗ IntertwiningMap.toLinearMapl (ρ := ρ) (σ := σ) =
            0 := LinearMap.ext fun f => intertwiningDefectAt_eq_zero_iff.mpr (f.isIntertwining' g)
        refine intertwiningDefectAt_eq_zero_iff.mp ?_
        rw [intertwiningDefectAt_homBaseChangeEquiv,
          LinearMap.baseChange_eq_lTensor, ← LinearMap.comp_apply, ← LinearMap.lTensor_comp, h0,
          LinearMap.lTensor_zero, LinearMap.zero_apply, map_zero] }
  map_add' x y := IntertwiningMap.ext (by simp)
  map_smul' a x := IntertwiningMap.ext (by simp)

private theorem toLinearMap_intertwiningMapBaseChangeHom (ρ : Representation K G V)
    (σ : Representation K G W) (x : L ⊗[K] IntertwiningMap ρ σ) :
    (intertwiningMapBaseChangeHom ρ σ x).toLinearMap =
      (LinearMap.isBaseChange_baseChangeHom K L V W).equiv
        ((IntertwiningMap.toLinearMapl (ρ := ρ) (σ := σ)).baseChange L x) :=
  rfl

variable [Module.Free K L]

private theorem intertwiningMapBaseChangeHom_bijective (ρ : Representation K G V)
    (σ : Representation K G W) :
    Function.Bijective (intertwiningMapBaseChangeHom (L := L) ρ σ) := by
  set e := (LinearMap.isBaseChange_baseChangeHom K L V W).equiv
  refine ⟨fun x y hxy => ?_, fun F => ?_⟩
  · have h := congrArg IntertwiningMap.toLinearMap hxy
    rw [toLinearMap_intertwiningMapBaseChangeHom, toLinearMap_intertwiningMapBaseChangeHom,
      e.injective.eq_iff, LinearMap.baseChange_eq_lTensor] at h
    exact Module.Flat.lTensor_preserves_injective_linearMap _
      (IntertwiningMap.toLinearMap_injective ρ σ) h
  · -- Expand `F` in a `K`-basis of `L`; every coefficient intertwines `ρ` and `σ`.
    classical
    let b := Module.Free.chooseBasis K L
    let c := equivFinsuppOfBasisLeft (N := V →ₗ[K] W) b
    set x := e.symm F.toLinearMap with hxdef
    have hcoeff (i : Module.Free.ChooseBasisIndex K L) (g : G) :
        c x i ∘ₗ ρ g = σ g ∘ₗ c x i := by
      have h0 : (intertwiningDefectAt ρ σ g).lTensor L x = 0 := by
        apply e.injective
        rw [← intertwiningDefectAt_homBaseChangeEquiv, LinearEquiv.apply_symm_apply, map_zero]
        exact intertwiningDefectAt_eq_zero_iff.mpr (F.isIntertwining' g)
      have := (b.lTensor_eq_zero_iff_forall_equivFinsuppOfBasisLeft
        (intertwiningDefectAt ρ σ g) x).mp h0 i
      exact intertwiningDefectAt_eq_zero_iff.mp this
    let f (i : Module.Free.ChooseBasisIndex K L) : IntertwiningMap ρ σ := ⟨c x i, hcoeff i⟩
    refine ⟨∑ i ∈ (c x).support, b i ⊗ₜ[K] f i, IntertwiningMap.ext ?_⟩
    rw [toLinearMap_intertwiningMapBaseChangeHom, ← e.eq_symm_apply, map_sum, ← hxdef]
    conv_rhs => rw [← c.symm_apply_apply x, equivFinsuppOfBasisLeft_symm_apply, Finsupp.sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [LinearMap.baseChange_tmul, IntertwiningMap.toLinearMapl_apply]

/-- **Free scalar extension commutes with intertwiner spaces.** For representations `ρ` and `σ`
of a monoid over a commutative ring `K`, with `ρ` on a finite projective module, and a
commutative `K`-algebra `L` that is free over `K`, the map `a ⊗ f ↦ a • (L ⊗ f)` identifies
`L ⊗[K] Hom_G(ρ, σ)` with the intertwining maps between the base changes. The monoid need not
be finite. -/
noncomputable def intertwiningMapBaseChangeEquivOfFree (ρ : Representation K G V)
    (σ : Representation K G W) :
    L ⊗[K] IntertwiningMap ρ σ ≃ₗ[L] IntertwiningMap (baseChange L ρ) (baseChange L σ) :=
  LinearEquiv.ofBijective _ (intertwiningMapBaseChangeHom_bijective ρ σ)

/-- Scalar extension of the intertwiner space sends a pure tensor to the corresponding scalar
multiple of the base-changed intertwining map. -/
@[simp]
theorem intertwiningMapBaseChangeEquivOfFree_tmul (ρ : Representation K G V)
    (σ : Representation K G W) (a : L) (f : IntertwiningMap ρ σ) :
    intertwiningMapBaseChangeEquivOfFree ρ σ (a ⊗ₜ[K] f) = a • f.baseChange L := by
  refine IntertwiningMap.ext ?_
  simp [intertwiningMapBaseChangeEquivOfFree, toLinearMap_intertwiningMapBaseChangeHom,
    IsBaseChange.equiv_tmul]

/-- The inverse of the scalar extension of the intertwiner space sends a base-changed intertwining
map to its canonical pure tensor. -/
@[simp]
theorem intertwiningMapBaseChangeEquivOfFree_symm_baseChange (ρ : Representation K G V)
    (σ : Representation K G W) (f : IntertwiningMap ρ σ) :
    (intertwiningMapBaseChangeEquivOfFree ρ σ).symm (f.baseChange L) = 1 ⊗ₜ[K] f := by
  rw [LinearEquiv.symm_apply_eq, intertwiningMapBaseChangeEquivOfFree_tmul, one_smul]

end Intertwiner

section Field

variable {K L G V W : Type*} [Field K] [CommRing L] [Nontrivial L] [Algebra K L] [Monoid G]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V] [AddCommGroup W] [Module K W]

/-- **Intertwiner dimensions are unchanged by scalar extension.** For representations of any
monoid over a field `K`, with finite-dimensional source, and a nonzero commutative `K`-algebra
`L`, the intertwiner space of the base changes has the same dimension over `L` as the original
one over `K`. -/
theorem finrank_intertwiningMap_baseChange (ρ : Representation K G V)
    (σ : Representation K G W) :
    Module.finrank L (IntertwiningMap (baseChange L ρ) (baseChange L σ)) =
      Module.finrank K (IntertwiningMap ρ σ) := by
  rw [← (intertwiningMapBaseChangeEquivOfFree ρ σ).finrank_eq, Module.finrank_baseChange]

end Field

end Representation
