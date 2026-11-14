/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.Topology.Algebra.Module.Compact
public import TauCeti.NumberTheory.NumberField.LocalGlobal.Semilocal.Basic
public import TauCeti.RingTheory.DedekindDomain.AdicValuation.Approximation
public import TauCeti.RingTheory.DedekindDomain.AdicValuation.IntegralClosure
import TauCeti.RingTheory.IsTensorProduct.BaseChange

/-!
# The integral semi-local decomposition of a number field

Let `L/K` be an extension of number fields and let `v` be a finite place of `K`. The scalar
extension of the ring of integers of `L` to the completed integer ring at `v` decomposes as the
product of the completed integer rings at the places above `v`:

```text
𝒪_v ⊗[𝓞 K] 𝓞 L ≃ₐ[𝒪_v] ∏_{w ∣ v} 𝒪_w.
```

The map sends a pure tensor `a ⊗ x` to `(a * x)_w`. Its scalar extension to the fraction field
is the semi-local decomposition `semilocalEquiv`. Surjectivity follows from simultaneous
approximation in the finitely many completed integer rings: the image is both dense and closed,
the latter because it is a finitely generated submodule over the compact ring `𝒪_v`.

## Main definitions

* `TauCeti.integralSemilocalHom`: the canonical homomorphism to the product of completed integer
  rings.
* `TauCeti.integralSemilocalToField`: the canonical map from the integral tensor product to the
  field tensor product.
* `TauCeti.integralSemilocalEquiv`: the integral semi-local decomposition.

## Main results

* `TauCeti.integralSemilocalEquiv_tmul`: the value of the equivalence on pure tensors.
* `TauCeti.integralSemilocalEquiv_fieldCompatibility`: after inclusion into the completions, the
  integral equivalence agrees with `semilocalEquiv`.

## References

* [J. Neukirch, *Algebraic Number Theory*][Neukirch1992], Chapter II, Proposition (8.3).
-/

public section
noncomputable section

open IsDedekindDomain NumberField
open scoped TensorProduct NumberField AdicCompletionExtension Valued

namespace TauCeti

open IsDedekindDomain.HeightOneSpectrum

local notation "𝒪" => _root_.NumberField.RingOfIntegers

variable {K : Type*} [Field K] [NumberField K]
  (L : Type*) [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝒪 K))

/-- The canonical map from the integral scalar extension at `v` to the product of the completed
integer rings at the places above `v`. -/
def integralSemilocalHom :
    v.adicCompletionIntegers K ⊗[𝓞 K] 𝒪 L →ₐ[v.adicCompletionIntegers K]
      ((w : {w : HeightOneSpectrum (𝒪 L) // w.asIdeal.LiesOver v.asIdeal}) →
        w.1.adicCompletionIntegers L) :=
  letI (w : {w : HeightOneSpectrum (𝒪 L) // w.asIdeal.LiesOver v.asIdeal}) :
      Algebra (𝒪 K) (w.1.adicCompletionIntegers L) :=
    ((algebraMap (v.adicCompletionIntegers K) (w.1.adicCompletionIntegers L)).comp
      (algebraMap (𝒪 K) (v.adicCompletionIntegers K))).toAlgebra
  letI (w : {w : HeightOneSpectrum (𝒪 L) // w.asIdeal.LiesOver v.asIdeal}) :
      IsScalarTower (𝒪 K) (v.adicCompletionIntegers K) (w.1.adicCompletionIntegers L) :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  Algebra.TensorProduct.lift (Algebra.ofId _ _)
    (AlgHom.pi fun w ↦
      { algebraMap (𝒪 L) (w.1.adicCompletionIntegers L) with
        commutes' := fun r ↦ by
          -- Expose the composite algebra structure installed just above so the two named
          -- compatibility lemmas apply.
          change algebraMap (𝒪 L) (w.1.adicCompletionIntegers L)
              (algebraMap (𝒪 K) (𝒪 L) r) =
            algebraMap (v.adicCompletionIntegers K) (w.1.adicCompletionIntegers L)
              (algebraMap (𝒪 K) (v.adicCompletionIntegers K) r)
          rw [algebraMap_adicCompletionIntegersExtensionAlgebra,
            adicCompletionIntegersExtension_algebraMap] })
    fun _ _ ↦ .all _ _

variable {L v}

/-- The integral semi-local map on a pure tensor. -/
@[simp]
theorem integralSemilocalHom_tmul (a : v.adicCompletionIntegers K) (x : 𝒪 L)
    (w : {w : HeightOneSpectrum (𝒪 L) // w.asIdeal.LiesOver v.asIdeal}) :
    integralSemilocalHom L v (a ⊗ₜ x) w =
      algebraMap (v.adicCompletionIntegers K) (w.1.adicCompletionIntegers L) a *
        algebraMap (𝒪 L) (w.1.adicCompletionIntegers L) x := by
  simp [integralSemilocalHom]

variable (L v)

omit [NumberField K] in
/-- The diagonal image of the global integers is dense in the product of the completed integer
rings at the places above `v`. -/
theorem denseRange_algebraMap_integers_pi_liesOver :
    DenseRange fun (x : 𝒪 L)
      (w : {w : HeightOneSpectrum (𝒪 L) // w.asIdeal.LiesOver v.asIdeal}) ↦
        algebraMap (𝒪 L) (w.1.adicCompletionIntegers L) x :=
  denseRange_algebraMap_pi_subtype (K := L) (fun w ↦ w.asIdeal.LiesOver v.asIdeal)

/-- The integral semi-local map is surjective. -/
theorem integralSemilocalHom_surjective : Function.Surjective (integralSemilocalHom L v) := by
  let _ (w : {w : HeightOneSpectrum (𝒪 L) // w.asIdeal.LiesOver v.asIdeal}) :
      ContinuousSMul (v.adicCompletionIntegers K) (w.1.adicCompletionIntegers L) := by
    apply continuousSMul_of_algebraMap
    apply continuous_induced_rng.mpr
    rw [algebraMap_adicCompletionIntegersExtensionAlgebra]
    exact (v.continuous_adicCompletionExtension K L w.1).comp continuous_subtype_val |>.congr
      fun x ↦ (coe_adicCompletionIntegersExtension K L v w.1 x).symm
  let s := LinearMap.range (integralSemilocalHom L v).toLinearMap
  have hsfg : s.FG := by
    simpa only [s, LinearMap.range_eq_map] using
      Module.Finite.fg_top.map (integralSemilocalHom L v).toLinearMap
  have hs : Set.range (fun (x : 𝒪 L)
      (w : {w : HeightOneSpectrum (𝒪 L) // w.asIdeal.LiesOver v.asIdeal}) ↦
        algebraMap (𝒪 L) (w.1.adicCompletionIntegers L) x) ⊆ s := by
    rintro _ ⟨x, rfl⟩
    exact ⟨1 ⊗ₜ x, funext fun w ↦ by simp⟩
  intro y
  exact (Submodule.isCompact_of_fg hsfg).isClosed.closure_subset_iff.mpr hs
    (denseRange_algebraMap_integers_pi_liesOver L v y)

omit [Field L] [NumberField L] [Algebra K L] in
local instance (v : HeightOneSpectrum (𝒪 K)) :
    IsScalarTower (𝒪 K) (v.adicCompletionIntegers K) (v.adicCompletion K) :=
  ⟨fun _ _ _ ↦ by simp only [Algebra.smul_def, map_mul]; exact mul_assoc _ _ _⟩

/-- The canonical inclusion of the integral tensor product in the field tensor product. -/
def integralSemilocalToField :
    v.adicCompletionIntegers K ⊗[𝒪 K] 𝒪 L →ₐ[𝒪 K]
      v.adicCompletion K ⊗[K] L :=
  baseChangeOfTower (𝒪 K) K (v.adicCompletionIntegers K) (v.adicCompletion K) (𝒪 L) L

variable {L v}

omit [NumberField L] in
/-- The inclusion in the field tensor product on a pure tensor. -/
@[simp]
theorem integralSemilocalToField_tmul (a : v.adicCompletionIntegers K) (x : 𝒪 L) :
    integralSemilocalToField L v (a ⊗ₜ x) =
      (a : v.adicCompletion K) ⊗ₜ (x : L) :=
  baseChangeOfTower_tmul (𝒪 K) K (v.adicCompletionIntegers K) (v.adicCompletion K) (𝒪 L) L a x

private theorem algebraMap_adicCompletionExtension_coe
    (a : v.adicCompletionIntegers K)
    (w : {w : HeightOneSpectrum (𝒪 L) // w.asIdeal.LiesOver v.asIdeal}) :
    algebraMap (v.adicCompletion K) (w.1.adicCompletion L) (a : v.adicCompletion K) =
      (algebraMap (v.adicCompletionIntegers K) (w.1.adicCompletionIntegers L) a :
        w.1.adicCompletion L) := by
  rw [algebraMap_adicCompletionIntegersExtensionAlgebra,
    algebraMap_adicCompletionExtensionAlgebra, coe_adicCompletionIntegersExtension]

private theorem algebraMap_ringOfIntegers_adicCompletion_eq_coe
    (x : 𝒪 L) (w : HeightOneSpectrum (𝒪 L)) :
    algebraMap (𝒪 L) (w.adicCompletion L) x =
      (algebraMap (𝒪 L) (w.adicCompletionIntegers L) x : w.adicCompletion L) := by
  rw [algebraMap_adicCompletionIntegers_apply,
    IsScalarTower.algebraMap_apply (𝒪 L) L (w.adicCompletion L),
    algebraMap_adicCompletion, Function.comp_apply, Algebra.algebraMap_self_apply]

/-- The integral and field semi-local maps agree after inclusion in the completions. -/
theorem integralSemilocalHom_fieldCompatibility
    (z : v.adicCompletionIntegers K ⊗[𝒪 K] 𝒪 L) :
    semilocalEquiv L v (integralSemilocalToField L v z) =
      fun w ↦ (integralSemilocalHom L v z w : w.1.adicCompletion L) := by
  induction z using TensorProduct.inductionOn with
  | add x y hx hy =>
      funext w
      simp only [map_add, Pi.add_apply]
      exact congrArg₂ (fun a b ↦ a + b) (congrFun hx w) (congrFun hy w)
  | tmul a x =>
      funext w
      simp only [integralSemilocalToField_tmul, semilocalEquiv_tmul,
        integralSemilocalHom_tmul]
      rw [← IsScalarTower.algebraMap_apply (𝒪 L) L (w.1.adicCompletion L),
        algebraMap_adicCompletionExtension_coe,
        algebraMap_ringOfIntegers_adicCompletion_eq_coe]
      rfl

variable (L v)

/-- The canonical inclusion of the integral tensor product in the field tensor product is
injective. -/
theorem integralSemilocalToField_injective : Function.Injective (integralSemilocalToField L v) :=
  baseChangeOfTower_injective (𝒪 K) K (v.adicCompletionIntegers K) (v.adicCompletion K) (𝒪 L) L

/-- The integral semi-local map is injective. -/
theorem integralSemilocalHom_injective : Function.Injective (integralSemilocalHom L v) := by
  intro x y hxy
  apply integralSemilocalToField_injective L v
  apply (semilocalEquiv L v).injective
  rw [integralSemilocalHom_fieldCompatibility,
    integralSemilocalHom_fieldCompatibility, hxy]

/-- **The integral semi-local decomposition**: scalar extension of the global integers to the
completed integer ring at `v` is the product of the completed integer rings above `v`. -/
def integralSemilocalEquiv :
    v.adicCompletionIntegers K ⊗[𝒪 K] 𝒪 L ≃ₐ[v.adicCompletionIntegers K]
      ((w : {w : HeightOneSpectrum (𝒪 L) // w.asIdeal.LiesOver v.asIdeal}) →
        w.1.adicCompletionIntegers L) :=
  -- Keep the `Bijective` ascription explicit: without it Lean exports the generated proof as a
  -- bare conjunction, which is not transparent enough when downstream lemmas unfold this def.
  AlgEquiv.ofBijective (integralSemilocalHom L v)
    (show Function.Bijective (integralSemilocalHom L v) from
      ⟨integralSemilocalHom_injective L v, integralSemilocalHom_surjective L v⟩)

variable {L v}

/-- The integral semi-local decomposition on a pure tensor. -/
@[simp]
theorem integralSemilocalEquiv_tmul (a : v.adicCompletionIntegers K) (x : 𝒪 L)
    (w : {w : HeightOneSpectrum (𝒪 L) // w.asIdeal.LiesOver v.asIdeal}) :
    integralSemilocalEquiv L v (a ⊗ₜ x) w =
      algebraMap (v.adicCompletionIntegers K) (w.1.adicCompletionIntegers L) a *
        algebraMap (𝒪 L) (w.1.adicCompletionIntegers L) x := by
  rw [integralSemilocalEquiv, AlgEquiv.ofBijective_apply]
  exact integralSemilocalHom_tmul a x w

/-- After inclusion into the completions, the integral semi-local decomposition agrees with the
field semi-local decomposition. -/
theorem integralSemilocalEquiv_fieldCompatibility
    (z : v.adicCompletionIntegers K ⊗[𝒪 K] 𝒪 L) :
    semilocalEquiv L v (integralSemilocalToField L v z) =
      fun w ↦ (integralSemilocalEquiv L v z w : w.1.adicCompletion L) := by
  rw [integralSemilocalEquiv, AlgEquiv.ofBijective_apply]
  exact integralSemilocalHom_fieldCompatibility z

/-- Projection of the integral semi-local decomposition to the completed integer ring at `w`. -/
def integralSemilocalComponent
    (w : {w : HeightOneSpectrum (𝒪 L) // w.asIdeal.LiesOver v.asIdeal}) :
    v.adicCompletionIntegers K ⊗[𝒪 K] 𝒪 L →ₐ[v.adicCompletionIntegers K]
      w.1.adicCompletionIntegers L :=
  (Pi.evalAlgHom (v.adicCompletionIntegers K) (fun w ↦
    w.1.adicCompletionIntegers L) w).comp (integralSemilocalEquiv L v).toAlgHom

/-- A component projection is evaluation of the integral semi-local decomposition. -/
@[simp]
theorem integralSemilocalComponent_apply
    (w : {w : HeightOneSpectrum (𝒪 L) // w.asIdeal.LiesOver v.asIdeal})
    (z : v.adicCompletionIntegers K ⊗[𝒪 K] 𝒪 L) :
    integralSemilocalComponent (L := L) (v := v) w z = integralSemilocalEquiv L v z w := by
  simp [integralSemilocalComponent]

/-- A component projection of the integral semi-local decomposition on a pure tensor. -/
theorem integralSemilocalComponent_tmul
    (w : {w : HeightOneSpectrum (𝒪 L) // w.asIdeal.LiesOver v.asIdeal})
    (a : v.adicCompletionIntegers K) (x : 𝒪 L) :
    integralSemilocalComponent (L := L) (v := v) w (a ⊗ₜ x) =
      algebraMap (v.adicCompletionIntegers K) (w.1.adicCompletionIntegers L) a *
        algebraMap (𝒪 L) (w.1.adicCompletionIntegers L) x := by
  exact integralSemilocalEquiv_tmul a x w

end TauCeti

end

end
