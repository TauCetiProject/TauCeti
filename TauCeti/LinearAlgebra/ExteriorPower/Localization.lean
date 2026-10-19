/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.ExteriorPower.BaseChange
public import Mathlib.RingTheory.Localization.BaseChange

/-!
# Exterior powers of localized modules

If `f : M →ₗ[R] N` exhibits `N` as an extension of scalars to an `R`-algebra `A`, the
exterior power of `N` is the scalar extension of the exterior power of `M`. The comparison
sends `a ⊗ (m₁ ∧ ⋯ ∧ mₙ)` to `a • (f m₁ ∧ ⋯ ∧ f mₙ)` and is natural in maps commuting
with `f`.

In particular, a map on exterior powers sending each wedge to the wedge of the images is a
localization when `f` is a localization. This allows the sectionwise exterior power of a
quasicoherent sheaf to be computed on basic affine opens.

The construction combines `TauCeti.exteriorPower.equivBaseChange` with Mathlib's
`IsBaseChange.equiv` and `IsLocalizedModule.isBaseChange`.

## References

* [The Stacks Project, Lemma 10.13.6](https://stacks.math.columbia.edu/tag/0C6F).
-/

public section

open scoped TensorProduct

noncomputable section

variable {R A M N : Type*} [CommRing R] [CommRing A] [Algebra R A]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [Module A N]
  [IsScalarTower R A N] {f : M →ₗ[R] N}

namespace IsBaseChange

/-- Exterior powers commute with a specified scalar extension. -/
def exteriorPowerEquiv (h : IsBaseChange A f) (n : ℕ) :
    A ⊗[R] (⋀[R]^n M) ≃ₗ[A] ⋀[A]^n N :=
  (TauCeti.exteriorPower.equivBaseChange A n).symm.trans
    (LinearEquiv.ofLinearMap (exteriorPower.map n h.equiv.toLinearMap)
      (exteriorPower.map n h.equiv.symm.toLinearMap)
      (re₁₂ := RingHomInvPair.ids) (re₂₁ := RingHomInvPair.ids)
      (by rw [← exteriorPower.map_comp]; simp)
      (by rw [← exteriorPower.map_comp]; simp))

/-- The scalar-extension comparison sends a pure tensor of a wedge to the scaled wedge of
the images. -/
@[simp]
theorem exteriorPowerEquiv_tmul_ιMulti (h : IsBaseChange A f) (n : ℕ) (a : A)
    (m : Fin n → M) :
    h.exteriorPowerEquiv n (a ⊗ₜ[R] exteriorPower.ιMulti R n m) =
      a • exteriorPower.ιMulti A n (fun i ↦ f (m i)) := by
  simp [exteriorPowerEquiv, exteriorPower.map_apply_ιMulti, Function.comp_def]

/-- The inverse comparison sends the wedge of the images to the tensor with coefficient one. -/
@[simp]
theorem exteriorPowerEquiv_symm_ιMulti (h : IsBaseChange A f) (n : ℕ) (m : Fin n → M) :
    (h.exteriorPowerEquiv n).symm (exteriorPower.ιMulti A n (fun i ↦ f (m i))) =
      1 ⊗ₜ[R] exteriorPower.ιMulti R n m := by
  apply (h.exteriorPowerEquiv n).injective
  simp

variable {M' N' : Type*} [AddCommGroup M'] [Module R M'] [AddCommGroup N']
  [Module R N'] [Module A N'] [IsScalarTower R A N'] {f' : M' →ₗ[R] N'}

/-- The exterior-power scalar-extension comparison is natural in commuting maps of the
original and extended modules. -/
theorem exteriorPowerEquiv_naturality (h : IsBaseChange A f) (h' : IsBaseChange A f')
    (n : ℕ) (g : M →ₗ[R] M') (g' : N →ₗ[A] N')
    (comm : (g'.restrictScalars R) ∘ₗ f = f' ∘ₗ g) :
    (exteriorPower.map n g') ∘ₗ (h.exteriorPowerEquiv n).toLinearMap =
      (h'.exteriorPowerEquiv n).toLinearMap ∘ₗ (exteriorPower.map n g).baseChange A := by
  -- Only the proof uses this restricted scalar action, to apply the universal properties
  -- of tensor products and exterior powers; the naturality statement is `A`-linear.
  let extR : Module R (⋀[A]^n N') := Module.compHom _ (algebraMap R A)
  let extTower : @IsScalarTower R A (⋀[A]^n N') _
      (⋀[A]^n N').module.toSMul extR.toSMul :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  -- Explicit scalar structures prevent the submodule's inherited scalar actions from
  -- replacing those of the restriction-of-scalars module.
  apply @TensorProduct.AlgebraTensorModule.ext R A A (⋀[R]^n M) (⋀[A]^n N')
    _ _ _ _ _ _ _ _ _ _ extR _ extTower
  intro a x
  have hw : (((exteriorPower.map n g') ∘ₗ (h.exteriorPowerEquiv n).toLinearMap).restrictScalars R)
      ∘ₗ TensorProduct.mk R A (⋀[R]^n M) a =
      (((h'.exteriorPowerEquiv n).toLinearMap ∘ₗ
        (exteriorPower.map n g).baseChange A).restrictScalars R)
        ∘ₗ TensorProduct.mk R A (⋀[R]^n M) a := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro m
    simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply,
      LinearMap.restrictScalars_apply, TensorProduct.mk_apply, LinearEquiv.coe_coe,
      exteriorPowerEquiv_tmul_ιMulti, LinearMap.baseChange_tmul,
      exteriorPower.map_apply_ιMulti, map_smul]
    congr 2
    exact funext fun i ↦ LinearMap.congr_fun comm (m i)
  exact LinearMap.congr_fun hw x

end IsBaseChange

namespace LinearMap

variable {S : Submonoid R} [IsLocalization S A] (f) [IsLocalizedModule S f]

/-- A map that sends wedges to the wedges of a localization map is itself a localization.
The scalar structure on the exterior power is retained as a parameter so this also applies
to restriction-of-scalars presentations of the target. Its tower uses the scalar action of
that module explicitly: the actions inferred directly from the submodule carrier need not
be the scalar projections of the caller's `Module R` instance. -/
theorem isLocalizedModule_exteriorPower (n : ℕ) [extR : Module R (⋀[A]^n N)]
    [extTower : @IsScalarTower R A (⋀[A]^n N) _ (⋀[A]^n N).module.toSMul extR.toSMul]
    (g : ⋀[R]^n M →ₗ[R] ⋀[A]^n N)
    (hg : ∀ m : Fin n → M,
      g (exteriorPower.ιMulti R n m) = exteriorPower.ιMulti A n (fun i ↦ f (m i))) :
    IsLocalizedModule S g := by
  -- Preserve `extR` and its tower when passing to the scalar-extension characterization.
  rw [@isLocalizedModule_iff_isBaseChange R _ S A _ _ _ (⋀[R]^n M) _ _
    (⋀[A]^n N) _ extR _ extTower g]
  refine @IsBaseChange.of_equiv R (⋀[R]^n M) (⋀[A]^n N) A _ _ _ _ _ _ extR _ extTower g
    ((IsLocalizedModule.isBaseChange S A f).exteriorPowerEquiv n) ?_
  have h :
      ((IsLocalizedModule.isBaseChange S A f).exteriorPowerEquiv n).toLinearMap.restrictScalars R
        ∘ₗ TensorProduct.mk R A (⋀[R]^n M) 1 = g := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro m
    simpa only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply,
      LinearMap.restrictScalars_apply, TensorProduct.mk_apply, LinearEquiv.coe_coe,
      IsBaseChange.exteriorPowerEquiv_tmul_ιMulti, one_smul] using (hg m).symm
  exact fun x ↦ LinearMap.congr_fun h x

end LinearMap
