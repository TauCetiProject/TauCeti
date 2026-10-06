/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.Ideles.Norm.Relative
public import TauCeti.NumberTheory.NumberField.Global.Places.Semilocal
public import TauCeti.NumberTheory.NumberField.LocalGlobal.Semilocal.NormTrace

/-!
# Norm equations in the local étale algebras

For a number-field extension `L/K`, the local norm at a place of `K` is the norm of
`K_v ⊗[K] L`, not the norm of an arbitrarily selected completion of `L`. The semilocal
comparisons identify its image with products of norms from all completions above the place.
In particular, the coordinates of an idele norm satisfy these local norm equations.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter II, (8.4), and Chapter VI, §2.

The local decompositions are `TauCeti.semilocalEquiv` and
`TauCeti.GlobalNumberFields.infiniteSemilocalEquiv`.
-/

public section
noncomputable section

open IsDedekindDomain NumberField NumberField.InfinitePlace
open scoped TensorProduct AdicCompletionExtension NumberField.LiesOver

namespace TauCeti.ClassFieldTheory

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/-- The norm on units of the local étale algebra at a finite place. -/
def finiteLocalNormMap (v : HeightOneSpectrum (𝓞 K)) :
    (v.adicCompletion K ⊗[K] L)ˣ →* (v.adicCompletion K)ˣ :=
  Algebra.normUnits (v.adicCompletion K)

/-- The norm on units of the local étale algebra at an infinite place. -/
def infiniteLocalNormMap (v : InfinitePlace K) :
    (v.Completion ⊗[K] L)ˣ →* v.Completionˣ :=
  Algebra.normUnits v.Completion

omit [NumberField L] in
/-- The finite local norm is the algebra norm on the underlying element. -/
@[simp]
theorem coe_finiteLocalNormMap (v : HeightOneSpectrum (𝓞 K))
    (u : (v.adicCompletion K ⊗[K] L)ˣ) :
    (finiteLocalNormMap K L v u : v.adicCompletion K) =
      Algebra.norm (v.adicCompletion K) (u : v.adicCompletion K ⊗[K] L) := by
  simp [finiteLocalNormMap]

omit [NumberField K] [NumberField L] in
/-- The infinite local norm is the algebra norm on the underlying element. -/
@[simp]
theorem coe_infiniteLocalNormMap (v : InfinitePlace K) (u : (v.Completion ⊗[K] L)ˣ) :
    (infiniteLocalNormMap K L v u : v.Completion) =
      Algebra.norm v.Completion (u : v.Completion ⊗[K] L) := by
  simp [infiniteLocalNormMap]

/-- Under the finite semilocal comparison the norm is the product of the component norms. -/
theorem finiteLocalNormMap_eq_prod (v : HeightOneSpectrum (𝓞 K))
    (u : (v.adicCompletion K ⊗[K] L)ˣ) :
    finiteLocalNormMap K L v u =
      ∏ᶠ w : {w : HeightOneSpectrum (𝓞 L) // w.asIdeal.LiesOver v.asIdeal},
        Algebra.normUnits (v.adicCompletion K)
          (MulEquiv.piUnits (Units.map (semilocalEquiv L v).toMonoidHom u) w) := by
  let := Fintype.ofFinite {w : HeightOneSpectrum (𝓞 L) // w.asIdeal.LiesOver v.asIdeal}
  apply Units.ext
  rw [coe_finiteLocalNormMap, ← Algebra.norm_eq_of_algEquiv (semilocalEquiv L v),
    Algebra.norm_pi, finprod_eq_prod_of_fintype]
  simp

/-- Under the infinite semilocal comparison the norm is the product of the component norms. -/
theorem infiniteLocalNormMap_eq_prod (v : InfinitePlace K) (u : (v.Completion ⊗[K] L)ˣ) :
    infiniteLocalNormMap K L v u =
      ∏ᶠ w : {w : InfinitePlace L // w.LiesOver v},
        Algebra.normUnits v.Completion
          (MulEquiv.piUnits (Units.map
            (GlobalNumberFields.infiniteSemilocalEquiv L v).toMonoidHom u) w) := by
  classical
  apply Units.ext
  rw [coe_infiniteLocalNormMap,
    ← Algebra.norm_eq_of_algEquiv (GlobalNumberFields.infiniteSemilocalEquiv L v),
    Algebra.norm_pi, finprod_eq_prod_of_fintype]
  simp

/-- A unit is a finite local norm exactly when it is a product of norms from the completions
above the place. This includes split local algebras. -/
theorem mem_range_finiteLocalNormMap_iff (v : HeightOneSpectrum (𝓞 K))
    (a : (v.adicCompletion K)ˣ) :
    a ∈ (finiteLocalNormMap K L v).range ↔
      ∃ u : (w : {w : HeightOneSpectrum (𝓞 L) // w.asIdeal.LiesOver v.asIdeal}) →
          (w.1.adicCompletion L)ˣ,
        (∏ᶠ w, Algebra.normUnits (v.adicCompletion K) (u w)) = a := by
  let e := (Units.mapEquiv (semilocalEquiv L v).toMulEquiv).trans MulEquiv.piUnits
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨e u, (finiteLocalNormMap_eq_prod K L v u).symm⟩
  · rintro ⟨u, hu⟩
    refine ⟨e.symm u, ?_⟩
    rw [finiteLocalNormMap_eq_prod]
    exact (congrArg (fun z ↦ ∏ᶠ w, Algebra.normUnits (v.adicCompletion K) (z w))
      (e.apply_symm_apply u)).trans hu

/-- A unit is an infinite local norm exactly when it is a product of norms from the completions
above the place. Real and complex places are both retained. -/
theorem mem_range_infiniteLocalNormMap_iff (v : InfinitePlace K) (a : v.Completionˣ) :
    a ∈ (infiniteLocalNormMap K L v).range ↔
      ∃ u : (w : {w : InfinitePlace L // w.LiesOver v}) → w.1.Completionˣ,
        (∏ᶠ w, Algebra.normUnits v.Completion (u w)) = a := by
  let e := (Units.mapEquiv (GlobalNumberFields.infiniteSemilocalEquiv L v).toMulEquiv).trans
    MulEquiv.piUnits
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨e u, (infiniteLocalNormMap_eq_prod K L v u).symm⟩
  · rintro ⟨u, hu⟩
    refine ⟨e.symm u, ?_⟩
    rw [infiniteLocalNormMap_eq_prod]
    exact (congrArg (fun z ↦ ∏ᶠ w, Algebra.normUnits v.Completion (z w))
      (e.apply_symm_apply u)).trans hu

/-- Every finite coordinate of an idele norm is a norm from the local étale algebra. -/
theorem ideleFiniteCoord_mem_range_finiteLocalNormMap (x : IdeleGroup (𝓞 L) L)
    (v : HeightOneSpectrum (𝓞 K)) :
    v.ideleFiniteCoord (GlobalNumberFields.ideleNormMap K L x) ∈
      (finiteLocalNormMap K L v).range := by
  rw [mem_range_finiteLocalNormMap_iff]
  exact ⟨fun w ↦ w.1.ideleFiniteCoord x,
    (GlobalNumberFields.ideleFiniteCoord_ideleNormMap v x).symm⟩

/-- Every infinite coordinate of an idele norm is a norm from the local étale algebra. -/
theorem ideleInfiniteCoord_mem_range_infiniteLocalNormMap (x : IdeleGroup (𝓞 L) L)
    (v : InfinitePlace K) :
    v.ideleInfiniteCoord (GlobalNumberFields.ideleNormMap K L x) ∈
      (infiniteLocalNormMap K L v).range := by
  rw [mem_range_infiniteLocalNormMap_iff]
  exact ⟨fun w ↦ w.1.ideleInfiniteCoord x,
    (GlobalNumberFields.ideleInfiniteCoord_ideleNormMap v x).symm⟩

end TauCeti.ClassFieldTheory
