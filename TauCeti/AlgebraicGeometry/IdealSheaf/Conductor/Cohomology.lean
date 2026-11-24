/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Artinian.Instances
public import TauCeti.AlgebraicGeometry.Cohomology.EulerCharacteristic
public import TauCeti.AlgebraicGeometry.IdealSheaf.Conductor.Cokernel
import TauCeti.AlgebraicGeometry.Cohomology.Cech.Basic
import TauCeti.AlgebraicGeometry.Cohomology.ClosedImmersion.Linear
import TauCeti.AlgebraicGeometry.Cohomology.Spec
import TauCeti.AlgebraicGeometry.IdealSheaf.Over

/-!
# Cohomology of the conductor-cokernel of a finite modification

Let `f : Y ⟶ X` be a finite modification of an irreducible Noetherian scheme `X` of Krull
dimension at most one, and let `Q = coker(𝒪_X ⟶ f_* 𝒪_Y)` be the cokernel of
`SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom`. By
`AlgebraicGeometry.Scheme.Hom.cokernelUnitToPushforwardIsoPushforward` and
`AlgebraicGeometry.Scheme.Hom.isArtinianScheme_conductor_subscheme`, `Q` is canonically pushed
forward along the closed immersion `f.conductor.subschemeι` from the Artinian (hence affine)
conductor closed subscheme `V(f.conductor)`.

Combining affine vanishing and pushforward comparison along closed immersions with the long exact
sequence of `0 ⟶ 𝒪_X ⟶ f_* 𝒪_Y ⟶ Q ⟶ 0` (when `f` is scheme-theoretically dominant) yields the
general cohomological properties of finite modifications in dimension at most one, with no curve,
regularity, or base-field assumptions where unnecessary:

## Main results

* `AlgebraicGeometry.Scheme.Hom.subsingleton_cohomology_succ_cokernel_unitToPushforwardObjUnit`:
  `Hⁿ⁺¹(X, Q) = 0` for all `n`.
* `AlgebraicGeometry.Scheme.Hom.moduleFinite_cohomology_cokernel_unitToPushforwardObjUnit` and
  `AlgebraicGeometry.Scheme.Hom.moduleFinite_globalSections_cokernel_unitToPushforwardObjUnit`:
  over an Artinian commutative ring `R` (such as a field), when `X` is locally of finite type over
  `Spec R`, every cohomology group `Hⁿ(X, Q)` and the global sections `Γ(Q, ⊤)` are finitely
  generated `R`-modules.
* `AlgebraicGeometry.Scheme.Hom.eulerCharBelow_cokernel_unitToPushforwardObjUnit`: over a field `k`,
  the truncated Euler characteristic of `Q` at any positive degree `m + 1` equals `dim_k Γ(Q, ⊤)`.
* `AlgebraicGeometry.Scheme.Hom.cohomologyMap_unitToPushforwardObjUnit_one_surjective` and
  `AlgebraicGeometry.Scheme.Hom.cohomologyMap_unitToPushforwardObjUnit_add_two_bijective`: when `f`
  is scheme-theoretically dominant, `H¹(X, 𝒪_X) → H¹(X, f_* 𝒪_Y)` is surjective and
  `Hⁿ⁺²(X, 𝒪_X) → Hⁿ⁺²(X, f_* 𝒪_Y)` is bijective for every `n`.
* `AlgebraicGeometry.Scheme.Modules.subsingleton_cohomology_unit_iff_of_two_le_of_isModification`:
  pushforward comparison along the affine morphism `f` identifies vanishing of `Hⁿ(X, 𝒪_X)` with
  vanishing of `Hⁿ(Y, 𝒪_Y)` for every `n ≥ 2`.

## References

* J.-P. Serre, *Algebraic Groups and Class Fields*, GTM 117, Chapter IV, §1, Proposition 1.
* R. Hartshorne, *Algebraic Geometry*, GTM 52, Chapter IV, Exercise 1.8.
* [Stacks Project, Lemma 33.41.1](https://stacks.math.columbia.edu/tag/0C45) and
  [Lemma 53.19.3](https://stacks.math.columbia.edu/tag/0CE4).
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules
open TauCeti TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme.Modules

universe u

namespace AlgebraicGeometry.Scheme

namespace Hom

section ConductorCohomology

variable {X Y : Scheme.{u}} (f : Y ⟶ X) [IsFinite f] [IsModification f]
  [IsNoetherian X] [IrreducibleSpace X]

/-- **Vanishing of higher cohomology of the conductor-cokernel.** For a finite modification
`f : Y ⟶ X` of an irreducible Noetherian scheme `X` of Krull dimension at most one, the
cokernel `coker(𝒪_X ⟶ f_* 𝒪_Y)` has vanishing cohomology in all positive degrees, since it is
pushed forward along a closed immersion from the Artinian (hence affine) conductor subscheme. -/
theorem subsingleton_cohomology_succ_cokernel_unitToPushforwardObjUnit
    (hX : topologicalKrullDim X ≤ 1) (n : ℕ) :
    Subsingleton (Cohomology
      (cokernel (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom) : X.Modules)
      (n + 1)) := by
  have : (cokernel (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom) :
      X.Modules).IsQuasicoherent :=
    f.isQuasicoherent_cokernel_unitToPushforwardObjUnit
  have : IsArtinianScheme f.conductor.subscheme := f.isArtinianScheme_conductor_subscheme hX
  let i := f.conductor.subschemeι
  let G : f.conductor.subscheme.Modules := (Scheme.Modules.pullback i).obj
    (cokernel (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom))
  have : Subsingleton (Cohomology G (n + 1)) := subsingleton_cohomology_succ_of_isAffine G n
  let e := ((cohomologyFunctor X (n + 1)).mapIso f.cokernelUnitToPushforwardIsoPushforward ≪≫
    cohomologyPushforwardIso i G (n + 1)).addCommGroupIsoToAddEquiv
  exact e.toEquiv.subsingleton

/-- Over an Artinian commutative ring `R` (for instance a field), if `X` is locally of finite type
over `Spec R`, then every cohomology group of `coker(𝒪_X ⟶ f_* 𝒪_Y)` is a finitely generated
`R`-module. -/
theorem moduleFinite_cohomology_cokernel_unitToPushforwardObjUnit
    (R : Type u) [CommRing R] [IsArtinianRing R] [X.Over (Spec (.of R))]
    [LocallyOfFiniteType (X ↘ Spec (.of R))]
    (hX : topologicalKrullDim X ≤ 1) (n : ℕ) :
    Module.Finite R (Cohomology
      (cokernel (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom) : X.Modules) n) := by
  have : (cokernel (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom) :
      X.Modules).IsQuasicoherent :=
    f.isQuasicoherent_cokernel_unitToPushforwardObjUnit
  let i := f.conductor.subschemeι
  let G : f.conductor.subscheme.Modules := (Scheme.Modules.pullback i).obj
    (cokernel (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom))
  have : IsFinite (f.conductor.subscheme ↘ Spec (.of R)) := by
    rw [Scheme.IdealSheafData.over_eq_subschemeι_comp]
    exact f.isFinite_conductor_subschemeι_comp hX (X ↘ Spec (.of R))
  have : Module.Finite R (Cohomology G n) :=
    moduleFinite_cohomology_of_isFinite_over_spec R G n
  have : Module.Finite R (Cohomology ((Scheme.Modules.pushforward i).obj G) n) :=
    (i.moduleFinite_cohomology_pushforward_iff R G n).mpr this
  exact Module.Finite.equiv
    (cohomologyBaseLinearEquivOfIso R f.cokernelUnitToPushforwardIsoPushforward.symm n)

/-- Over an Artinian commutative ring `R` (for instance a field), the global sections of
`coker(𝒪_X ⟶ f_* 𝒪_Y)` form a finitely generated `R`-module. -/
theorem moduleFinite_globalSections_cokernel_unitToPushforwardObjUnit
    (R : Type u) [CommRing R] [IsArtinianRing R] [X.Over (Spec (.of R))]
    [LocallyOfFiniteType (X ↘ Spec (.of R))]
    (hX : topologicalKrullDim X ≤ 1) :
    Module.Finite R
      Γ((cokernel (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom) : X.Modules),
        ⊤) := by
  have := f.moduleFinite_cohomology_cokernel_unitToPushforwardObjUnit R hX 0
  exact Module.Finite.equiv (cohomologyZeroBaseLinearEquiv R X
    (cokernel (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom)))

/-- Over a field `k`, the Euler characteristic of `coker(𝒪_X ⟶ f_* 𝒪_Y)` truncated at any positive
degree `m + 1` equals `dim_k Γ(coker(𝒪_X ⟶ f_* 𝒪_Y), ⊤)`, since all higher cohomology vanishes. -/
theorem eulerCharBelow_cokernel_unitToPushforwardObjUnit
    (k : Type u) [Field k] [X.Over (Spec (.of k))]
    (hX : topologicalKrullDim X ≤ 1) (m : ℕ) :
    eulerCharBelow k X
        (cokernel (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom) : X.Modules)
        (m + 1) =
      (Module.finrank k
        Γ((cokernel (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom) : X.Modules),
          ⊤) : ℤ) := by
  let Q : X.Modules := cokernel (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom)
  induction m with
  | zero =>
    rw [eulerCharBelow_succ, eulerCharBelow_zero, pow_zero, one_mul, zero_add,
      finrank_cohomology_zero_eq_finrank_globalSections]
  | succ m ih =>
    have := f.subsingleton_cohomology_succ_cokernel_unitToPushforwardObjUnit hX m
    rw [eulerCharBelow_succ, ih, Module.finrank_zero_of_subsingleton (M := Cohomology Q (m + 1)),
      Nat.cast_zero, mul_zero, add_zero]

/-- **Surjectivity on `H¹` along a finite modification in dimension at most one.** Because
`H¹(X, coker(𝒪_X ⟶ f_* 𝒪_Y)) = 0`, the map `H¹(X, 𝒪_X) → H¹(X, f_* 𝒪_Y)` is surjective. -/
theorem cohomologyMap_unitToPushforwardObjUnit_one_surjective
    [IsSchemeTheoreticallyDominant f] (hX : topologicalKrullDim X ≤ 1) :
    Function.Surjective (cohomologyMap
      (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom :
        (SheafOfModules.unit X.ringCatSheaf : X.Modules) ⟶
          (Scheme.Modules.pushforward f).obj (SheafOfModules.unit Y.ringCatSheaf)) 1) := by
  let φ : (SheafOfModules.unit X.ringCatSheaf : X.Modules) ⟶
      (Scheme.Modules.pushforward f).obj (SheafOfModules.unit Y.ringCatSheaf) :=
    SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom
  have : Mono φ := f.mono_unitToPushforwardObjUnit
  have hS := TauCeti.cokernelSequence_shortExact φ
  have hQ : Subsingleton (Cohomology (ShortComplex.cokernelSequence φ).X₃ 1) :=
    f.subsingleton_cohomology_succ_cokernel_unitToPushforwardObjUnit hX 0
  intro y
  exact (exact_cohomologyMap_cohomologyMap hS 1 y).mp (hQ.elim _ _)

/-- **Bijectivity in degrees `≥ 2` along a finite modification in dimension at most one.** Because
`coker(𝒪_X ⟶ f_* 𝒪_Y)` has no cohomology in positive degrees, `Hⁿ⁺²(X, 𝒪_X) → Hⁿ⁺²(X, f_* 𝒪_Y)`
is bijective for every `n`. -/
theorem cohomologyMap_unitToPushforwardObjUnit_add_two_bijective
    [IsSchemeTheoreticallyDominant f] (hX : topologicalKrullDim X ≤ 1) (n : ℕ) :
    Function.Bijective (cohomologyMap
      (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom :
        (SheafOfModules.unit X.ringCatSheaf : X.Modules) ⟶
          (Scheme.Modules.pushforward f).obj (SheafOfModules.unit Y.ringCatSheaf)) (n + 2)) := by
  let φ : (SheafOfModules.unit X.ringCatSheaf : X.Modules) ⟶
      (Scheme.Modules.pushforward f).obj (SheafOfModules.unit Y.ringCatSheaf) :=
    SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom
  have : Mono φ := f.mono_unitToPushforwardObjUnit
  have hS := TauCeti.cokernelSequence_shortExact φ
  have hQ₁ : Subsingleton (Cohomology (ShortComplex.cokernelSequence φ).X₃ (n + 1)) :=
    f.subsingleton_cohomology_succ_cokernel_unitToPushforwardObjUnit hX n
  have hQ₂ : Subsingleton (Cohomology (ShortComplex.cokernelSequence φ).X₃ (n + 2)) :=
    f.subsingleton_cohomology_succ_cokernel_unitToPushforwardObjUnit hX (n + 1)
  refine ⟨(injective_iff_map_eq_zero _).mpr fun x hx ↦ ?_,
    fun y ↦ (exact_cohomologyMap_cohomologyMap hS (n + 2) y).mp (hQ₂.elim _ _)⟩
  obtain ⟨z, rfl⟩ := (exact_cohomologyδ_cohomologyMap hS (n + 1) (n + 2) rfl x).mp hx
  exact (congrArg _ (hQ₁.elim z 0)).trans (map_zero _)

end ConductorCohomology

end Hom

namespace Modules

/-- Along a finite modification `f : Y ⟶ X` of a Noetherian irreducible scheme `X` of dimension at
most one with `[IsSchemeTheoreticallyDominant f]`, `Hⁿ(X, 𝒪_X)` vanishes if and only if
`Hⁿ(Y, 𝒪_Y)` vanishes in every degree `n ≥ 2`. -/
theorem subsingleton_cohomology_unit_iff_of_two_le_of_isModification {X Y : Scheme.{u}}
    [IsNoetherian X] [IrreducibleSpace X] (hX : topologicalKrullDim X ≤ 1)
    (f : Y ⟶ X) [IsFinite f] [IsModification f] [IsSchemeTheoreticallyDominant f]
    (n : ℕ) (hn : 2 ≤ n) :
    Subsingleton (Cohomology (SheafOfModules.unit X.ringCatSheaf : X.Modules) n) ↔
      Subsingleton (Cohomology (SheafOfModules.unit Y.ringCatSheaf : Y.Modules) n) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have : (SheafOfModules.unit Y.ringCatSheaf).IsQuasicoherent :=
    AlgebraicGeometry.isQuasicoherent_structureSheaf Y
  let ePush := (f.cohomologyPushforwardIsoOfIsAffineHom
    (SheafOfModules.unit Y.ringCatSheaf) (m + 2)).addCommGroupIsoToAddEquiv
  let eMap := Equiv.ofBijective _ (f.cohomologyMap_unitToPushforwardObjUnit_add_two_bijective hX m)
  exact (eMap.trans ePush.toEquiv).subsingleton_congr

end Modules

end AlgebraicGeometry.Scheme

end
