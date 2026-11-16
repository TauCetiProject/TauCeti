/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import TauCeti.RepresentationTheory.BaseChange

import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Matrix.ToLin
import TauCeti.LinearAlgebra.LinearMap.BaseChange

/-!
# Algebraic descent of morphisms between representations

Let `ρ` and `σ` be representations of a monoid `G` over a commutative ring `R`, and let `A` be a
faithfully flat `R`-algebra (for instance any field extension). This file establishes the
morphisms-and-equalities half of the filtered 2-colimit description of representations over an
algebraic extension:

* **Faithfulness** (`Representation.IntertwiningMap.baseChange_injective`): two intertwining maps
  whose base changes to `A` agree are already equal.
* **Agreement over a common enlargement**
  (`Representation.IntertwiningMap.baseChange_eq_of_baseChange_eq`): given two extensions
  `E → E₁ → E'` and `E → E₂ → E'` inside a faithfully flat algebra `L / E'`, intertwining maps
  over `E₁` and `E₂` that agree after base change to `L` already agree after base change to `E'`.
* **Morphism descent** (`Representation.IntertwiningMap.exists_descent_of_baseChange`): for
  finite-dimensional representations over a field `E` and an algebraic extension `L / E`, any
  intertwining map between their base changes to `L` descends to a finite intermediate field
  `E' : IntermediateField E L`, obtained by adjoining the finitely many matrix entries of the map.
* **Isomorphism descent** (`Representation.Equiv.exists_descent_of_baseChange`): any equivalence
  over `L` descends to an equivalence over a finite intermediate field `E' : IntermediateField E L`.

## Main results

* `Representation.IntertwiningMap.baseChange_injective`
* `Representation.cancelBaseChange_baseChange`
* `Representation.IntertwiningMap.baseChange_eq_of_baseChange_eq`
* `Representation.IntertwiningMap.exists_descent_of_baseChange`
* `Representation.Equiv.exists_descent_of_baseChange`
-/

public section

open TensorProduct

namespace Representation

section Faithfulness

variable {R A G V W : Type*} [CommRing R] [Ring A] [Algebra R A] [Module.FaithfullyFlat R A]
  [Monoid G] [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]

/-- **Base change is faithful on intertwining maps** over any faithfully flat algebra. -/
theorem IntertwiningMap.baseChange_injective {ρ : Representation R G V} {σ : Representation R G W} :
    Function.Injective (fun f : IntertwiningMap ρ σ ↦ f.baseChange A) := by
  intro f g h
  apply IntertwiningMap.ext
  have hlin : f.toLinearMap.baseChange A = g.toLinearMap.baseChange A := by
    simpa only [IntertwiningMap.toLinearMap_baseChange] using
      congrArg IntertwiningMap.toLinearMap h
  exact LinearMap.baseChange_injective (R := R) (A := A) hlin

end Faithfulness

section Tower

variable {E E' L G V : Type*} [CommRing E] [CommRing E'] [Ring L]
  [Algebra E E'] [Algebra E L] [Algebra E' L] [IsScalarTower E E' L]
  [Monoid G] [AddCommGroup V] [Module E V]

/-- **Scalar-tower compatibility for base change of representations.** For a tower `E → E' → L`,
the canonical linear equivalence `L ⊗[E'] (E' ⊗[E] V) ≃ₗ[L] L ⊗[E] V` intertwines
`(ρ.baseChange E').baseChange L` with `ρ.baseChange L`. -/
theorem cancelBaseChange_baseChange (ρ : Representation E G V) (g : G)
    (x : L ⊗[E'] (E' ⊗[E] V)) :
    AlgebraTensorModule.cancelBaseChange E E' L L V
        ((ρ.baseChange E').baseChange L g x) =
      ρ.baseChange L g (AlgebraTensorModule.cancelBaseChange E E' L L V x) := by
  have h : (AlgebraTensorModule.cancelBaseChange E E' L L V).toLinearMap ∘ₗ
        ((ρ.baseChange E').baseChange L g) =
      (ρ.baseChange L g) ∘ₗ (AlgebraTensorModule.cancelBaseChange E E' L L V).toLinearMap := by
    ext v
    simp
  exact LinearMap.congr_fun h x

end Tower

section Enlargement

variable {E E₁ E₂ E' L G V W : Type*}
  [CommRing E] [CommRing E₁] [CommRing E₂] [CommRing E'] [Ring L]
  [Algebra E E₁] [Algebra E E₂] [Algebra E E'] [Algebra E L]
  [Algebra E₁ E'] [Algebra E₁ L] [Algebra E₂ E'] [Algebra E₂ L] [Algebra E' L]
  [IsScalarTower E E₁ E'] [IsScalarTower E E₁ L] [IsScalarTower E₁ E' L]
  [IsScalarTower E E₂ E'] [IsScalarTower E E₂ L] [IsScalarTower E₂ E' L]
  [IsScalarTower E E' L]
  [Module.FaithfullyFlat E' L]
  [Monoid G] [AddCommGroup V] [Module E V] [AddCommGroup W] [Module E W]

/-- **Intertwining maps equal over a faithfully flat extension agree over any common enlargement.**
If `f₁` over `E₁` and `f₂` over `E₂` induce the same map `L ⊗[E] V → L ⊗[E] W` after extending
scalars to `L`, then they already induce the same map `E' ⊗[E] V → E' ⊗[E] W` over any common
enlargement `E'` over which `L` is faithfully flat. -/
theorem IntertwiningMap.baseChange_eq_of_baseChange_eq
    {ρ : Representation E G V} {σ : Representation E G W}
    (f₁ : IntertwiningMap (ρ.baseChange E₁) (σ.baseChange E₁))
    (f₂ : IntertwiningMap (ρ.baseChange E₂) (σ.baseChange E₂))
    (hL : ∀ x : L ⊗[E] V,
      AlgebraTensorModule.cancelBaseChange E E₁ L L W
          (f₁.baseChange L ((AlgebraTensorModule.cancelBaseChange E E₁ L L V).symm x)) =
        AlgebraTensorModule.cancelBaseChange E E₂ L L W
          (f₂.baseChange L ((AlgebraTensorModule.cancelBaseChange E E₂ L L V).symm x))) :
    ∀ x : E' ⊗[E] V,
      AlgebraTensorModule.cancelBaseChange E E₁ E' E' W
          (f₁.baseChange E' ((AlgebraTensorModule.cancelBaseChange E E₁ E' E' V).symm x)) =
        AlgebraTensorModule.cancelBaseChange E E₂ E' E' W
          (f₂.baseChange E' ((AlgebraTensorModule.cancelBaseChange E E₂ E' E' V).symm x)) := by
  let g₁ : (E' ⊗[E] V) →ₗ[E'] (E' ⊗[E] W) :=
    (AlgebraTensorModule.cancelBaseChange E E₁ E' E' W).toLinearMap ∘ₗ
      (f₁.toLinearMap.baseChange E') ∘ₗ
      (AlgebraTensorModule.cancelBaseChange E E₁ E' E' V).symm.toLinearMap
  let g₂ : (E' ⊗[E] V) →ₗ[E'] (E' ⊗[E] W) :=
    (AlgebraTensorModule.cancelBaseChange E E₂ E' E' W).toLinearMap ∘ₗ
      (f₂.toLinearMap.baseChange E') ∘ₗ
      (AlgebraTensorModule.cancelBaseChange E E₂ E' E' V).symm.toLinearMap
  suffices h : g₁ = g₂ from fun x ↦ by
    simpa only [g₁, g₂, LinearMap.comp_apply, LinearEquiv.coe_coe,
      ← IntertwiningMap.coe_toLinearMap, IntertwiningMap.toLinearMap_baseChange] using
      LinearMap.congr_fun h x
  apply LinearMap.baseChange_injective (R := E') (A := L)
  ext v
  apply (AlgebraTensorModule.cancelBaseChange E E' L L W).injective
  have h1 : ∀ y : E₁ ⊗[E] W,
      AlgebraTensorModule.cancelBaseChange E E' L L W
          ((1 : L) ⊗ₜ[E'] AlgebraTensorModule.cancelBaseChange E E₁ E' E' W ((1 : E') ⊗ₜ[E₁] y)) =
        AlgebraTensorModule.cancelBaseChange E E₁ L L W ((1 : L) ⊗ₜ[E₁] y) := fun y ↦ by
    induction y using TensorProduct.inductionOn with
    | add a b ha hb => simp only [TensorProduct.tmul_add, map_add, ha, hb]
    | tmul c w => simp
  have h2 : ∀ y : E₂ ⊗[E] W,
      AlgebraTensorModule.cancelBaseChange E E' L L W
          ((1 : L) ⊗ₜ[E'] AlgebraTensorModule.cancelBaseChange E E₂ E' E' W ((1 : E') ⊗ₜ[E₂] y)) =
        AlgebraTensorModule.cancelBaseChange E E₂ L L W ((1 : L) ⊗ₜ[E₂] y) := fun y ↦ by
    induction y using TensorProduct.inductionOn with
    | add a b ha hb => simp only [TensorProduct.tmul_add, map_add, ha, hb]
    | tmul c w => simp
  have hv := hL ((1 : L) ⊗ₜ[E] v)
  simp only [AlgebraTensorModule.cancelBaseChange_symm_tmul, IntertwiningMap.baseChange_tmul] at hv
  simp only [g₁, g₂, AlgebraTensorModule.curry_apply, TensorProduct.curry_apply,
    LinearMap.restrictScalars_apply, LinearMap.baseChange_tmul, LinearMap.comp_apply,
    LinearEquiv.coe_coe, AlgebraTensorModule.cancelBaseChange_symm_tmul,
    IntertwiningMap.coe_toLinearMap]
  exact (h1 _).trans (hv.trans (h2 _).symm)

end Enlargement

section AlgebraicDescent

variable {E L G V W : Type*} [Field E] [Field L] [Algebra E L] [Algebra.IsAlgebraic E L]
  [Monoid G] [AddCommGroup V] [Module E V] [FiniteDimensional E V]
  [AddCommGroup W] [Module E W] [FiniteDimensional E W]

/-- **Morphism descent over an algebraic field extension.** Any intertwining map between the
scalar extensions to `L` of two finite-dimensional `E`-representations descends to a finite
intermediate field `E' : IntermediateField E L`. -/
theorem IntertwiningMap.exists_descent_of_baseChange
    {ρ : Representation E G V} {σ : Representation E G W}
    (f : IntertwiningMap (ρ.baseChange L) (σ.baseChange L)) :
    ∃ (E' : IntermediateField E L), FiniteDimensional E E' ∧
      ∃ f' : IntertwiningMap (ρ.baseChange E') (σ.baseChange E'),
        ∀ x : L ⊗[E'] (E' ⊗[E] V),
          AlgebraTensorModule.cancelBaseChange E E' L L W (f'.baseChange L x) =
            f (AlgebraTensorModule.cancelBaseChange E E' L L V x) := by
  let bV := Module.finBasis E V
  let bW := Module.finBasis E W
  let M : Matrix (Fin (Module.finrank E W)) (Fin (Module.finrank E V)) L :=
    LinearMap.toMatrix (bV.baseChange L) (bW.baseChange L) f.toLinearMap
  let s : Set L := Set.range fun p : Fin (Module.finrank E W) × Fin (Module.finrank E V) ↦ M p.1 p.2
  have : Finite s := Set.finite_range _
  let E' : IntermediateField E L := IntermediateField.adjoin E s
  have hfin : FiniteDimensional E E' := IntermediateField.finiteDimensional_adjoin fun x _ ↦
    (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
  let M' : Matrix (Fin (Module.finrank E W)) (Fin (Module.finrank E V)) E' :=
    Matrix.of fun i j ↦ ⟨M i j, IntermediateField.subset_adjoin E s ⟨(i, j), rfl⟩⟩
  let f₀ : (E' ⊗[E] V) →ₗ[E'] (E' ⊗[E] W) :=
    Matrix.toLin (bV.baseChange E') (bW.baseChange E') M'
  have hcompat : ∀ x : L ⊗[E'] (E' ⊗[E] V),
      AlgebraTensorModule.cancelBaseChange E E' L L W (f₀.baseChange L x) =
        f (AlgebraTensorModule.cancelBaseChange E E' L L V x) := by
    have hlin : (AlgebraTensorModule.cancelBaseChange E E' L L W).toLinearMap ∘ₗ
        f₀.baseChange L =
      f.toLinearMap ∘ₗ (AlgebraTensorModule.cancelBaseChange E E' L L V).toLinearMap := by
      apply ((bV.baseChange E').baseChange L).ext
      intro j
      have hf₀ : f₀ (1 ⊗ₜ[E] bV j) = ∑ i, M' i j • ((1 : E') ⊗ₜ[E] bW i) := by
        simpa only [Module.Basis.baseChange_apply] using
          Matrix.toLin_self (bV.baseChange E') (bW.baseChange E') M' j
      have hf : f (1 ⊗ₜ[E] bV j) = ∑ i, M i j • ((1 : L) ⊗ₜ[E] bW i) := by
        have h := Matrix.toLin_self (bV.baseChange L) (bW.baseChange L) M j
        rw [Matrix.toLin_toMatrix] at h
        simpa only [Module.Basis.baseChange_apply, IntertwiningMap.coe_toLinearMap] using h
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Module.Basis.baseChange_apply,
        LinearMap.baseChange_tmul, hf₀, TensorProduct.tmul_sum, map_sum,
        TensorProduct.tmul_smul, AlgebraTensorModule.cancelBaseChange_tmul,
        Algebra.smul_def, map_one, mul_one, IntertwiningMap.coe_toLinearMap, hf]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      simp [M', TensorProduct.smul_tmul', Algebra.smul_def]
    exact LinearMap.congr_fun hlin
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
scalar extensions to `L` of two finite-dimensional `E`-representations descends to an equivalence
over a finite intermediate field `E' : IntermediateField E L`. -/
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
  have hinj : Function.Injective f' := by
    rw [injective_iff_map_eq_zero]
    intro v hv
    have h1 : f'.baseChange L ((1 : L) ⊗ₜ[E'] v) = 0 := by
      rw [IntertwiningMap.baseChange_tmul, hv, TensorProduct.tmul_zero]
    have h2 : AlgebraTensorModule.cancelBaseChange E E' L L V ((1 : L) ⊗ₜ[E'] v) = 0 :=
      e.injective (by simp [← hcompat, h1])
    have h3 : (1 : L) ⊗ₜ[E'] v = 0 :=
      (AlgebraTensorModule.cancelBaseChange E E' L L V).injective (by simpa using h2)
    have hlin : (LinearMap.toSpanSingleton E' (E' ⊗[E] V) v).baseChange L =
        (0 : E' →ₗ[E'] (E' ⊗[E] V)).baseChange L := by
      ext
      simp [h3]
    simpa using LinearMap.congr_fun (LinearMap.baseChange_injective (R := E') (A := L) hlin) 1
  have hVW : Module.finrank E V = Module.finrank E W := by
    simpa [Module.finrank_baseChange] using e.toLinearEquiv.finrank_eq
  have hdim : Module.finrank E' (E' ⊗[E] V) = Module.finrank E' (E' ⊗[E] W) := by
    simp [hVW]
  have hbij : Function.Bijective f'.toLinearMap :=
    ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hinj⟩
  let e' : (ρ.baseChange E').Equiv (σ.baseChange E') :=
    Equiv.mk (LinearEquiv.ofBijective f'.toLinearMap hbij) f'.isIntertwining'
  refine ⟨E', hfin, e', fun x ↦ ?_⟩
  have heq : (e'.baseChange L) x = (f'.baseChange L) x := by
    induction x using TensorProduct.inductionOn with
    | add u w hu hw => simp only [map_add, hu, hw]
    | tmul a v =>
      rw [Equiv.baseChange_tmul, IntertwiningMap.baseChange_tmul]
      rfl
  rw [heq]
  simpa only [Equiv.coe_toIntertwiningMap] using hcompat x

end AlgebraicDescent

end Representation
