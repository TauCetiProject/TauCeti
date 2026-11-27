/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Artinian.Instances
public import TauCeti.AlgebraicGeometry.Cohomology.EulerCharacteristic
public import TauCeti.AlgebraicGeometry.Cohomology.Trivial
public import TauCeti.AlgebraicGeometry.IdealSheaf.Conductor.Cokernel
import TauCeti.AlgebraicGeometry.Cohomology.Cech.Basic
import TauCeti.AlgebraicGeometry.Cohomology.ClosedImmersion.Linear
import TauCeti.AlgebraicGeometry.Cohomology.Spec
import TauCeti.AlgebraicGeometry.IdealSheaf.Over

/-!
# Cohomology of the conductor-cokernel of a finite modification

Let `f : Y ⟶ X` be a finite modification of a Noetherian scheme `X` of Krull dimension at most
one, and let `Q = coker(𝒪_X ⟶ f_* 𝒪_Y)` be the cokernel of
`SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom`. By
`AlgebraicGeometry.Scheme.Hom.cokernelUnitToPushforwardIsoPushforward` and
`AlgebraicGeometry.Scheme.Hom.isArtinianScheme_conductor_subscheme`, `Q` is canonically pushed
forward along the closed immersion `f.conductor.subschemeι` from the Artinian (hence affine)
conductor closed subscheme `V(f.conductor)`. The scheme `X` need not be irreducible: no
irreducible component of `X` lies in the support of the conductor, so the conductor subscheme has
dimension zero all the same. This covers the normalization of a reducible curve, such as a nodal
curve with several components, whose source is a disjoint union of curves.

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
* `AlgebraicGeometry.Scheme.Modules.finiteDimensional_cohomology_trivial_of_isModification`: over
  a field `k`, when `X` is locally of finite type over `k`, `Hⁿ(X, 𝒪_X)` is finite-dimensional as
  soon as `Hⁿ(Y, 𝒪_Y)` is.
* `AlgebraicGeometry.Scheme.Modules.eulerCharBelow_trivial_eq_add_of_isModification`: if moreover
  `H⁰(Y, 𝒪_Y)` and `H¹(Y, 𝒪_Y)` are finite-dimensional and `H²(Y, 𝒪_Y) = 0`, then
  `χ(Y, 𝒪_Y) = χ(X, 𝒪_X) + dim_k Γ(Q, ⊤)`.

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

variable {X Y : Scheme.{u}} (f : Y ⟶ X) [IsFinite f] [IsModification f] [IsNoetherian X]

/-- **Vanishing of higher cohomology of the conductor-cokernel.** For a finite modification
`f : Y ⟶ X` of a Noetherian scheme `X` of Krull dimension at most one, the cokernel
`coker(𝒪_X ⟶ f_* 𝒪_Y)` has vanishing cohomology in all positive degrees, since it is pushed
forward along a closed immersion from the Artinian (hence affine) conductor subscheme. -/
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

/-- Along a finite modification `f : Y ⟶ X` of a Noetherian scheme `X` of dimension at most one
with `[IsSchemeTheoreticallyDominant f]`, `Hⁿ(X, 𝒪_X)` vanishes if and only if `Hⁿ(Y, 𝒪_Y)`
vanishes in every degree `n ≥ 2`. -/
theorem subsingleton_cohomology_unit_iff_of_two_le_of_isModification {X Y : Scheme.{u}}
    [IsNoetherian X] (hX : topologicalKrullDim X ≤ 1)
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

section Field

variable (k : Type u) [Field k] {X Y : Scheme.{u}} [X.Over (Spec (.of k))]
  [Y.Over (Spec (.of k))] [IsNoetherian X] [LocallyOfFiniteType (X ↘ Spec (.of k))]
  (hX : topologicalKrullDim X ≤ 1) (f : Y ⟶ X) [IsFinite f] [IsModification f]
  [IsSchemeTheoreticallyDominant f] [f.IsOver (Spec (.of k))]

include hX f in
/-- **Finite-dimensionality of structure-sheaf cohomology descends along a finite modification in
dimension at most one.** Let `f : Y ⟶ X` be a finite scheme-theoretically dominant modification
over a field `k` of a Noetherian scheme `X` of dimension at most one, locally of finite type over
`k`. If `Hⁿ(Y, 𝒪_Y)` is finite-dimensional over `k`, then so is `Hⁿ(X, 𝒪_X)`. Neither `X` nor
`Y` need be irreducible. -/
theorem finiteDimensional_cohomology_trivial_of_isModification (n : ℕ)
    [FiniteDimensional k (Cohomology (InvertibleSheaf.trivial Y).obj n)] :
    FiniteDimensional k (Cohomology (InvertibleSheaf.trivial X).obj n) := by
  let OX : X.Modules := SheafOfModules.unit X.ringCatSheaf
  let OY : Y.Modules := SheafOfModules.unit Y.ringCatSheaf
  let _ : ∀ m, Module k (Cohomology OX m) := cohomologyBaseModule k X OX
  let _ : ∀ m, Module k (Cohomology OY m) := cohomologyBaseModule k Y OY
  have : OY.IsQuasicoherent := AlgebraicGeometry.isQuasicoherent_structureSheaf Y
  let φ : OX ⟶ (pushforward f).obj OY :=
    SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom
  have : Mono φ := f.mono_unitToPushforwardObjUnit
  have hpush (m : ℕ) (_ : FiniteDimensional k (Cohomology (InvertibleSheaf.trivial Y).obj m)) :
      FiniteDimensional k (Cohomology ((pushforward f).obj OY) m) :=
    Module.Finite.equiv ((trivialCohomologyBaseLinearEquiv k Y m).trans
      (f.cohomologyPushforwardBaseLinearEquivOfIsAffineHom k OY m).symm)
  suffices FiniteDimensional k (Cohomology OX n) from
    Module.Finite.equiv (trivialCohomologyBaseLinearEquiv k X n).symm
  -- `H⁰(X, 𝒪_X)` embeds into `H⁰(X, f_* 𝒪_Y)`, `H¹(X, 𝒪_X)` sits between `Γ(Q)` and
  -- `H¹(X, f_* 𝒪_Y)`, and the higher groups embed into those of `f_* 𝒪_Y`.
  rcases n with _ | _ | m
  · have := hpush 0 ‹_›
    exact finiteDimensional_cohomology_zero_of_mono k X φ
  · have : FiniteDimensional k (Cohomology (ShortComplex.cokernelSequence φ).X₂ 1) := hpush 1 ‹_›
    have : FiniteDimensional k (Cohomology (ShortComplex.cokernelSequence φ).X₃ 0) :=
      f.moduleFinite_cohomology_cokernel_unitToPushforwardObjUnit k hX 0
    exact finiteDimensional_cohomology_X₁ k X (TauCeti.cokernelSequence_shortExact φ) 0 1 rfl
  · have := hpush (m + 2) ‹_›
    refine Module.Finite.of_injective (cohomologyMapBaseLinear k X φ (m + 2)) ?_
    rw [coe_cohomologyMapBaseLinear]
    exact (f.cohomologyMap_unitToPushforwardObjUnit_add_two_bijective hX m).1

include hX in
/-- **Euler-characteristic comparison along a finite modification in dimension at most one.** Let
`f : Y ⟶ X` be a finite scheme-theoretically dominant modification over a field `k` of a
Noetherian scheme `X` of dimension at most one, locally of finite type over `k`, and suppose that
`H⁰(Y, 𝒪_Y)` and `H¹(Y, 𝒪_Y)` are finite-dimensional and `H²(Y, 𝒪_Y) = 0`. Then the short exact
sequence `0 ⟶ 𝒪_X ⟶ f_* 𝒪_Y ⟶ Q ⟶ 0`, with `Q = coker(𝒪_X ⟶ f_* 𝒪_Y)`, gives
`χ(Y, 𝒪_Y) = χ(X, 𝒪_X) + dim_k Γ(Q, ⊤)` for the Euler characteristics truncated at degree `2`.
Neither `X` nor `Y` need be irreducible: this applies to the normalization of a reducible curve,
whose source is a disjoint union of curves. -/
theorem eulerCharBelow_trivial_eq_add_of_isModification
    [FiniteDimensional k (Cohomology (InvertibleSheaf.trivial Y).obj 0)]
    [FiniteDimensional k (Cohomology (InvertibleSheaf.trivial Y).obj 1)]
    (hY : Subsingleton (Cohomology (InvertibleSheaf.trivial Y).obj 2)) :
    eulerCharBelow k Y (InvertibleSheaf.trivial Y).obj 2 =
      eulerCharBelow k X (InvertibleSheaf.trivial X).obj 2 +
        (Module.finrank k
          Γ((cokernel (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom) : X.Modules),
            ⊤) : ℤ) := by
  let OX : X.Modules := SheafOfModules.unit X.ringCatSheaf
  let OY : Y.Modules := SheafOfModules.unit Y.ringCatSheaf
  let _ : ∀ m, Module k (Cohomology OX m) := cohomologyBaseModule k X OX
  let _ : ∀ m, Module k (Cohomology OY m) := cohomologyBaseModule k Y OY
  have : OY.IsQuasicoherent := AlgebraicGeometry.isQuasicoherent_structureSheaf Y
  let φ : OX ⟶ (pushforward f).obj OY :=
    SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom
  have : Mono φ := f.mono_unitToPushforwardObjUnit
  -- Both Euler characteristics are read off the structure sheaves, and that of `Y` through
  -- the cohomology of `f_* 𝒪_Y` on `X`, since `f` is affine.
  let eY (m : ℕ) := (trivialCohomologyBaseLinearEquiv k Y m).trans
    (f.cohomologyPushforwardBaseLinearEquivOfIsAffineHom k OY m).symm
  have hY_eq : eulerCharBelow k Y (InvertibleSheaf.trivial Y).obj 2 =
      eulerCharBelow k X ((pushforward f).obj OY) 2 := by
    rw [eulerCharBelow_two, eulerCharBelow_two, (eY 0).finrank_eq, (eY 1).finrank_eq]
  have hX_eq : eulerCharBelow k X (InvertibleSheaf.trivial X).obj 2 = eulerCharBelow k X OX 2 := by
    rw [eulerCharBelow_two, eulerCharBelow_two, (trivialCohomologyBaseLinearEquiv k X 0).finrank_eq,
      (trivialCohomologyBaseLinearEquiv k X 1).finrank_eq]
  have hX₁ : FiniteDimensional k (Cohomology OX 1) :=
    have := finiteDimensional_cohomology_trivial_of_isModification k hX f 1
    Module.Finite.equiv (trivialCohomologyBaseLinearEquiv k X 1)
  have hX₂ : Subsingleton (Cohomology OX 2) :=
    (subsingleton_cohomology_unit_iff_of_two_le_of_isModification hX f 2 le_rfl).mpr
      ((trivialCohomologyBaseLinearEquiv k Y 2).toEquiv.symm.subsingleton)
  have hadd := eulerCharBelow_eq_add k (TauCeti.cokernelSequence_shortExact φ) 2
    (fun i hi hi₀ ↦ by obtain rfl : i = 1 := (by omega); exact hX₁)
    (fun i hi ↦ by interval_cases i <;> exact Module.Finite.equiv (eY _)) hX₂
  rw [hY_eq, hX_eq]
  exact hadd.trans (congrArg _ (f.eulerCharBelow_cokernel_unitToPushforwardObjUnit k hX 1))

end Field

end Modules

end AlgebraicGeometry.Scheme

end
