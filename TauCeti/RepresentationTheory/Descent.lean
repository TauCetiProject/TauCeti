/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import TauCeti.RepresentationTheory.BaseChange

import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import TauCeti.LinearAlgebra.LinearMap.BaseChange
import TauCeti.RepresentationTheory.Intertwining

/-!
# Algebraic descent of morphisms between representations

Let `ρ` and `σ` be representations of a monoid `G` over a commutative semiring `E`, extended along
intermediate algebras inside a faithfully flat algebra `L`. Together with the faithfulness
(`Representation.IntertwiningMap.baseChange_injective`) and scalar-tower cancellation
(`Representation.cancelBaseChangeEquiv`) in `TauCeti.RepresentationTheory.BaseChange`, this file
establishes descent and equality detection for morphisms (and isomorphisms) between objects already
defined at finite stages over an algebraic field extension (object descent itself can fail for
unrestricted algebraic extensions, and is supplied in the continuous setting by Baire descent in
`TauCeti.RepresentationTheory.Continuous.BaireDescent`):

* **Agreement over a common enlargement**
  (`Representation.IntertwiningMap.baseChange_eq_of_baseChange_eq`): given two extensions
  `E → E₁ → E'` and `E → E₂ → E'` inside a faithfully flat algebra `L / E'`, intertwining maps
  over `E₁` and `E₂` that agree after base change to `L` already agree after base change to `E'`.
* **Morphism descent** (`Representation.IntertwiningMap.exists_descent_of_baseChange`): for
  representations over a field `E` with finite-dimensional domain `V` and an algebraic extension
  `L / E`, any intertwining map between their base changes to `L` descends to a finite intermediate
  field `E' : IntermediateField E L`, obtained via `LinearMap.baseChangeTensorHomEquiv` by
  adjoining the finitely many scalar coefficients of a tensor representation of the map.
* **Isomorphism descent** (`Representation.Equiv.exists_descent_of_baseChange`): any equivalence
  over `L` with finite-dimensional domain `V` descends to an equivalence over a finite intermediate
  field `E' : IntermediateField E L`, using faithfully flat reflection of bijectivity
  (`Module.FaithfullyFlat.lTensor_bijective_iff_bijective`).

## Main results

* `Representation.IntertwiningMap.baseChange_eq_of_baseChange_eq`
* `Representation.IntertwiningMap.exists_descent_of_baseChange`
* `Representation.Equiv.exists_descent_of_baseChange`
-/

public section

open TensorProduct

namespace Representation

section Enlargement

variable {E E₁ E₂ E' L G V W : Type*}
  [CommSemiring E] [CommSemiring E₁] [CommSemiring E₂] [CommRing E'] [Ring L]
  [Algebra E E₁] [Algebra E E₂] [Algebra E E'] [Algebra E L]
  [Algebra E₁ E'] [Algebra E₁ L] [Algebra E₂ E'] [Algebra E₂ L] [Algebra E' L]
  [IsScalarTower E E₁ E'] [IsScalarTower E E₁ L] [IsScalarTower E₁ E' L]
  [IsScalarTower E E₂ E'] [IsScalarTower E E₂ L] [IsScalarTower E₂ E' L]
  [IsScalarTower E E' L]
  [Module.FaithfullyFlat E' L]
  [Monoid G] [AddCommMonoid V] [Module E V] [AddCommMonoid W] [Module E W]

/-- **Intertwining maps equal over a faithfully flat extension agree over any common enlargement.**
If `f₁` over `E₁` and `f₂` over `E₂` induce the same map `L ⊗[E] V → L ⊗[E] W` after extending
scalars to `L`, then they already induce the same map `E' ⊗[E] V → E' ⊗[E] W` over any common
enlargement `E'` over which `L` is faithfully flat. -/
theorem IntertwiningMap.baseChange_eq_of_baseChange_eq
    {ρ : Representation E G V} {σ : Representation E G W}
    (f₁ : IntertwiningMap (ρ.baseChange E₁) (σ.baseChange E₁))
    (f₂ : IntertwiningMap (ρ.baseChange E₂) (σ.baseChange E₂))
    (hL :
      (σ.cancelBaseChangeEquiv E₁ L).toIntertwiningMap.comp
          ((f₁.baseChange L).comp (ρ.cancelBaseChangeEquiv E₁ L).symm.toIntertwiningMap) =
        (σ.cancelBaseChangeEquiv E₂ L).toIntertwiningMap.comp
          ((f₂.baseChange L).comp (ρ.cancelBaseChangeEquiv E₂ L).symm.toIntertwiningMap)) :
    (σ.cancelBaseChangeEquiv E₁ E').toIntertwiningMap.comp
        ((f₁.baseChange E').comp (ρ.cancelBaseChangeEquiv E₁ E').symm.toIntertwiningMap) =
      (σ.cancelBaseChangeEquiv E₂ E').toIntertwiningMap.comp
        ((f₂.baseChange E').comp (ρ.cancelBaseChangeEquiv E₂ E').symm.toIntertwiningMap) := by
  apply IntertwiningMap.ext
  simpa only [IntertwiningMap.comp_toLinearMap, IntertwiningMap.toLinearMap_baseChange,
    toLinearMap_cancelBaseChangeEquiv, toLinearMap_cancelBaseChangeEquiv_symm] using
    LinearMap.baseChange_eq_of_baseChange_eq f₁.toLinearMap f₂.toLinearMap (by
      simpa only [IntertwiningMap.comp_toLinearMap, IntertwiningMap.toLinearMap_baseChange,
        toLinearMap_cancelBaseChangeEquiv, toLinearMap_cancelBaseChangeEquiv_symm] using
        congrArg IntertwiningMap.toLinearMap hL)

end Enlargement

section AlgebraicDescent

variable {E L G V W : Type*} [Field E] [Field L] [Algebra E L] [Algebra.IsAlgebraic E L]
  [Monoid G] [AddCommGroup V] [Module E V] [FiniteDimensional E V]
  [AddCommGroup W] [Module E W]

/-- **Morphism descent over an algebraic field extension.** Any intertwining map between the
scalar extensions to `L` of two `E`-representations, with finite-dimensional domain `V`, descends
to a finite intermediate field `E' : IntermediateField E L`. -/
theorem IntertwiningMap.exists_descent_of_baseChange
    {ρ : Representation E G V} {σ : Representation E G W}
    (f : IntertwiningMap (ρ.baseChange L) (σ.baseChange L)) :
    ∃ (E' : IntermediateField E L), FiniteDimensional E E' ∧
      ∃ f' : IntertwiningMap (ρ.baseChange E') (σ.baseChange E'),
        ∀ x : L ⊗[E'] (E' ⊗[E] V),
          AlgebraTensorModule.cancelBaseChange E E' L L W (f'.baseChange L x) =
            f (AlgebraTensorModule.cancelBaseChange E E' L L V x) := by
  -- 1. Represent `f` as a finite sum in `L ⊗[E] (V →ₗ[E] W)` and adjoin its scalar coefficients.
  let z : L ⊗[E] (V →ₗ[E] W) :=
    (LinearMap.baseChangeTensorHomEquiv (R := E) (A := L) (M := V) (N := W)).symm f.toLinearMap
  have hz : LinearMap.baseChangeTensorHom E L V W z = f.toLinearMap := by
    simpa only [LinearMap.baseChangeTensorHomEquiv_apply] using
      (LinearMap.baseChangeTensorHomEquiv (R := E) (A := L) (M := V) (N := W)).apply_symm_apply
        f.toLinearMap
  obtain ⟨s, hs⟩ := TensorProduct.exists_finset z
  let E' : IntermediateField E L :=
    IntermediateField.adjoin E (Prod.fst '' (s : Set (L × (V →ₗ[E] W))))
  have hfin : FiniteDimensional E E' := by
    have : Finite (Prod.fst '' (s : Set (L × (V →ₗ[E] W)))) :=
      (s.finite_toSet.image Prod.fst).to_subtype
    exact IntermediateField.finiteDimensional_adjoin fun x _ ↦
      (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
  -- 2. Define the descended linear map `f₀` over `E'` and check compatibility with `f` over `L`.
  have hs_mem : ∀ p ∈ s, p.1 ∈ E' := fun p hp ↦
    IntermediateField.subset_adjoin E _ ⟨p, Finset.mem_coe.mpr hp, rfl⟩
  let f₀ : (E' ⊗[E] V) →ₗ[E'] (E' ⊗[E] W) :=
    ∑ p ∈ s.attach, (⟨p.val.1, hs_mem p.val p.property⟩ : E') • p.val.2.baseChange E'
  have hcomp :
      (AlgebraTensorModule.cancelBaseChange E E' L L W).toLinearMap ∘ₗ f₀.baseChange L =
        f.toLinearMap ∘ₗ (AlgebraTensorModule.cancelBaseChange E E' L L V).toLinearMap := by
    have hf' : f.toLinearMap =
        ∑ p ∈ s.attach, algebraMap E' L (⟨p.val.1, hs_mem p.val p.property⟩ : E') •
          p.val.2.baseChange L := by
      rw [← hz, hs, map_sum, ← Finset.sum_attach s]
      refine Finset.sum_congr rfl fun p _ ↦ ?_
      rw [LinearMap.baseChangeTensorHom_tmul, IntermediateField.algebraMap_apply]
    simpa only [f₀, hf'] using
      LinearMap.cancelBaseChange_comp_sum_smul_baseChange s.attach
        (fun p ↦ (⟨p.val.1, hs_mem p.val p.property⟩ : E')) (fun p ↦ p.val.2)
  have hcompat (x : L ⊗[E'] (E' ⊗[E] V)) :
      AlgebraTensorModule.cancelBaseChange E E' L L W (f₀.baseChange L x) =
        f (AlgebraTensorModule.cancelBaseChange E E' L L V x) :=
    LinearMap.congr_fun hcomp x
  -- 3. Check `f₀` is intertwining via faithful flatness (`LinearMap.baseChange_injective`).
  have hint : ∀ g : G, f₀ ∘ₗ (ρ.baseChange E' g) = (σ.baseChange E' g) ∘ₗ f₀ := by
    intro g
    apply LinearMap.baseChange_injective (R := E') (A := L)
    apply LinearMap.ext
    intro x
    apply (AlgebraTensorModule.cancelBaseChange E E' L L W).injective
    simp only [LinearMap.baseChange_comp, LinearMap.comp_apply, ← baseChange_apply,
      hcompat, cancelBaseChange_baseChange, f.isIntertwining]
  refine ⟨E', hfin, ⟨f₀, hint⟩, fun x ↦ ?_⟩
  simpa only [← IntertwiningMap.coe_toLinearMap, IntertwiningMap.toLinearMap_baseChange] using
    hcompat x

/-- **Isomorphism descent over an algebraic field extension.** Any equivalence between the
scalar extensions to `L` of two `E`-representations, with finite-dimensional domain `V`, descends
to an equivalence over a finite intermediate field `E' : IntermediateField E L`. -/
theorem Equiv.exists_descent_of_baseChange
    {ρ : Representation E G V} {σ : Representation E G W}
    (e : (ρ.baseChange L).Equiv (σ.baseChange L)) :
    ∃ (E' : IntermediateField E L), FiniteDimensional E E' ∧
      ∃ e' : (ρ.baseChange E').Equiv (σ.baseChange E'),
        ∀ x : L ⊗[E'] (E' ⊗[E] V),
          AlgebraTensorModule.cancelBaseChange E E' L L W (e'.baseChange L x) =
            e (AlgebraTensorModule.cancelBaseChange E E' L L V x) := by
  obtain ⟨E', hfin, f', hcompat⟩ :=
    IntertwiningMap.exists_descent_of_baseChange e.toIntertwiningMap
  have hbij : Function.Bijective f' := by
    rw [← IntertwiningMap.coe_toLinearMap,
      ← Module.FaithfullyFlat.lTensor_bijective_iff_bijective E' L f'.toLinearMap]
    have heq : ⇑(f'.toLinearMap.lTensor L) =
        ⇑(AlgebraTensorModule.cancelBaseChange E E' L L W).symm ∘ ⇑e ∘
          ⇑(AlgebraTensorModule.cancelBaseChange E E' L L V) := by
      ext x
      rw [← LinearMap.baseChange_eq_lTensor]
      exact (AlgebraTensorModule.cancelBaseChange E E' L L W).eq_symm_apply.mpr
        (by simpa only [Function.comp_apply, ← IntertwiningMap.toLinearMap_baseChange,
          IntertwiningMap.coe_toLinearMap, Equiv.coe_toIntertwiningMap] using hcompat x)
    rw [heq]
    exact (AlgebraTensorModule.cancelBaseChange E E' L L W).symm.bijective.comp
      (e.bijective.comp (AlgebraTensorModule.cancelBaseChange E E' L L V).bijective)
  let e' : (ρ.baseChange E').Equiv (σ.baseChange E') := f'.ofBijective hbij
  refine ⟨E', hfin, e', fun x ↦ ?_⟩
  simpa only [e', ← Equiv.coe_toIntertwiningMap, Equiv.toIntertwiningMap_baseChange,
    IntertwiningMap.toIntertwiningMap_ofBijective] using hcompat x

end AlgebraicDescent

end Representation
