/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.DeRham.Complex
public import TauCeti.RingTheory.Kaehler.MapSemilinear
import TauCeti.Data.Fin.Tuple.Basic
import TauCeti.LinearAlgebra.Alternating.RestrictScalars

/-!
# Functorial pullback on ordinary algebraic differential forms and de Rham complexes

For an `A`-algebra homomorphism `f : B →ₐ[A] C`, this file extends
`KaehlerDifferential.mapSemilinear f : Ω[B⁄A] →ₛₗ[f.toRingHom] Ω[C⁄A]` to exterior powers,
producing the `f`-semilinear pullback
`TauCeti.DeRham.pullback f n : Forms A B n →ₛₗ[f.toRingHom] Forms A C n` in every degree `n`.

Just as for `KaehlerDifferential.mapSemilinear`, no global `Algebra B C` instance is required
(which would clash with `Algebra.id` for endomorphisms such as Frobenius): the construction
installs the local `Algebra B C` structure induced by `f`, applies
`exteriorPower.alternatingMapLinearEquiv`, and exports the resulting semilinear map so that all
statements survive outside the local instance scope.

We prove that `pullback f n` sends elementary forms `c · Dv₁ ∧ ⋯ ∧ Dvₙ` to
`f c · D (f v₁) ∧ ⋯ ∧ D (f vₙ)` (`pullback_elementary`), is uniquely determined by this rule
(`pullback_unique`), identifies with `f` in degree `0` (`zeroEquiv_pullback_zeroEquiv_symm`) and
with `KaehlerDifferential.mapSemilinear f` in degree `1` (`oneEquiv_pullback`), commutes with the
de Rham differential (`pullback_d`), preserves wedge products (`pullback_wedge`), and is functorial
in `f` (`pullback_id`, `pullback_comp`). Packaging `pullback f n` as `A`-linear maps yields the
morphism of cochain complexes `TauCeti.DeRham.complexMap f : complex A B ⟶ complex A C`, which
preserves identities and composition.

## Main definitions

* `TauCeti.DeRham.pullback`: the `f`-semilinear pullback `Forms A B n →ₛₗ[f.toRingHom] Forms A C n`.
* `TauCeti.DeRham.pullbackLinearMap`: `pullback f n` packaged as an `A`-linear map.
* `TauCeti.DeRham.complexMap`: the induced cochain map `complex A B ⟶ complex A C`.

## Main results

* `TauCeti.DeRham.pullback_elementary` and `TauCeti.DeRham.pullback_unique`: characterization on
  elementary forms.
* `TauCeti.DeRham.pullback_d`: pullback commutes with `d`.
* `TauCeti.DeRham.pullback_wedge`: pullback preserves `exteriorPower.wedge`.
* `TauCeti.DeRham.pullback_id` and `TauCeti.DeRham.pullback_comp`: functoriality on forms.
* `TauCeti.DeRham.complexMap_id` and `TauCeti.DeRham.complexMap_comp`: functoriality on de Rham
  complexes.

## References

* [Stacks Project, Tag 0FKE](https://stacks.math.columbia.edu/tag/0FKE), Section 10.132.
* Joël Riou, *feat(AlgebraicGeometry): the algebraic De Rham complex*, Mathlib proposal at commit
  [`5888c0081ba867ede5c60d3060f2d674d932b53c`](https://github.com/leanprover-community/mathlib4/blob/5888c0081ba867ede5c60d3060f2d674d932b53c/Mathlib/RingTheory/DeRham/Basic.lean#L285-L432),
  `Mathlib/RingTheory/DeRham/Basic.lean`, lines 285–432.
-/

public section

noncomputable section

open CategoryTheory

namespace TauCeti.DeRham

section Pullback

variable {A B C E : Type*} [CommRing A] [CommRing B] [CommRing C] [CommRing E]
  [Algebra A B] [Algebra A C] [Algebra A E]

/-- The alternating `B`-multilinear map `(Fin n → Ω[B⁄A]) → Forms A C n` under a `B`-algebra
structure on `C` compatible with `A`. -/
private def pullbackAlt (A B C : Type*) [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] [Algebra B C] [IsScalarTower A B C] (n : ℕ) :
    AlternatingMap B (KaehlerDifferential A B) (Forms A C n) (Fin n) :=
  ((exteriorPower.ιMulti C n).restrictScalars B).compLinearMap (KaehlerDifferential.map A A B C)

private theorem pullbackAlt_apply [Algebra B C] [IsScalarTower A B C] (n : ℕ)
    (ω : Fin n → KaehlerDifferential A B) :
    pullbackAlt A B C n ω =
      exteriorPower.ιMulti C n (fun i => KaehlerDifferential.map A A B C (ω i)) := by
  rw [pullbackAlt, AlternatingMap.compLinearMap_apply, AlternatingMap.restrictScalars_apply]

/-- **Pullback of ordinary algebraic differential `n`-forms** along an `A`-algebra homomorphism
`f : B →ₐ[A] C`, extending `KaehlerDifferential.mapSemilinear f` to `n`-th exterior powers. It is
`f`-semilinear in `B`-scalars (`pullback_smul`), `A`-linear (`pullback_base_smul`), and uniquely
characterized on elementary forms by `c · Dv₁ ∧ ⋯ ∧ Dvₙ ↦ f c · D (f v₁) ∧ ⋯ ∧ D (f vₙ)`
(`pullback_elementary`, `pullback_unique`). -/
def pullback (f : B →ₐ[A] C) (n : ℕ) : Forms A B n →ₛₗ[f.toRingHom] Forms A C n :=
  letI : Algebra B C := f.toRingHom.toAlgebra
  letI : IsScalarTower A B C := IsScalarTower.of_algebraMap_eq' f.comp_algebraMap.symm
  let φ : Forms A B n →ₗ[B] Forms A C n :=
    exteriorPower.alternatingMapLinearEquiv (pullbackAlt A B C n)
  { toFun := φ
    map_add' := map_add φ
    map_smul' := fun b ω => by
      rw [LinearMap.map_smul, ← RingHom.algebraMap_toAlgebra f.toRingHom]
      exact (IsScalarTower.algebraMap_smul C b (φ ω)).symm }

private theorem pullback_apply (f : B →ₐ[A] C) (n : ℕ) (ω : Forms A B n) :
    let : Algebra B C := f.toRingHom.toAlgebra
    let : IsScalarTower A B C := IsScalarTower.of_algebraMap_eq' f.comp_algebraMap.symm
    pullback f n ω = exteriorPower.alternatingMapLinearEquiv (pullbackAlt A B C n) ω :=
  rfl

/-- The semilinearity law of `pullback`, stated with `f` applied rather than `f.toRingHom`,
matching `KaehlerDifferential.mapSemilinear_smul`. -/
@[simp]
theorem pullback_smul (f : B →ₐ[A] C) (n : ℕ) (b : B) (ω : Forms A B n) :
    pullback f n (b • ω) = f b • pullback f n ω :=
  (pullback f n).map_smulₛₗ b ω

/-- Pullback of differential forms is `A`-linear. -/
@[simp]
theorem pullback_base_smul (f : B →ₐ[A] C) (n : ℕ) (a : A) (ω : Forms A B n) :
    pullback f n (a • ω) = a • pullback f n ω := by
  rw [← algebraMap_smul B a ω, pullback_smul, f.commutes, algebraMap_smul]

/-- The pullback of ordinary algebraic differential `n`-forms packaged as an `A`-linear map. -/
def pullbackLinearMap (f : B →ₐ[A] C) (n : ℕ) : Forms A B n →ₗ[A] Forms A C n where
  toFun := pullback f n
  map_add' := map_add (pullback f n)
  map_smul' a ω := pullback_base_smul f n a ω

/-- Evaluation of `pullbackLinearMap` agrees with `pullback`. -/
@[simp]
theorem pullbackLinearMap_apply (f : B →ₐ[A] C) (n : ℕ) (ω : Forms A B n) :
    pullbackLinearMap f n ω = pullback f n ω :=
  (rfl)

/-- On pure exterior products, `pullback f n` applies `KaehlerDifferential.mapSemilinear f`
slotwise. -/
@[simp]
theorem pullback_ιMulti (f : B →ₐ[A] C) (n : ℕ) (ω : Fin n → KaehlerDifferential A B) :
    pullback f n (exteriorPower.ιMulti B n ω) =
      exteriorPower.ιMulti C n (KaehlerDifferential.mapSemilinear f ∘ ω) := by
  let : Algebra B C := f.toRingHom.toAlgebra
  have : IsScalarTower A B C := IsScalarTower.of_algebraMap_eq' f.comp_algebraMap.symm
  have hf : IsScalarTower.toAlgHom A B C = f := AlgHom.ext fun b => by
    rw [IsScalarTower.toAlgHom_apply, RingHom.algebraMap_toAlgebra, AlgHom.toRingHom_eq_coe,
      AlgHom.coe_toRingHom]
  rw [pullback_apply, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti, pullbackAlt_apply]
  congr 1
  funext i
  rw [← hf]
  exact (KaehlerDifferential.mapSemilinear_toAlgHom_apply (R := A) (A := B) (B := C) (ω i)).symm

/-- Pullback sends `c · Dv₁ ∧ ⋯ ∧ Dvₙ` to `f c · D (f v₁) ∧ ⋯ ∧ D (f vₙ)`. -/
@[simp]
theorem pullback_elementary (f : B →ₐ[A] C) (n : ℕ) (c : B) (v : Fin n → B) :
    pullback f n (elementary A c v) = elementary A (f c) (f ∘ v) := by
  simp only [elementary_def, pullback_smul, pullback_ιMulti, Function.comp_def,
    KaehlerDifferential.mapSemilinear_D]

/-- An `f`-semilinear map `Forms A B n →ₛₗ[f.toRingHom] Forms A C n` satisfying the
elementary-form formula equals `pullback f n`. -/
theorem pullback_unique (f : B →ₐ[A] C) (n : ℕ) {φ : Forms A B n →ₛₗ[f.toRingHom] Forms A C n}
    (hφ : ∀ (c : B) (v : Fin n → B),
      φ (elementary A c v) = elementary A (f c) (f ∘ v)) :
    φ = pullback f n :=
  LinearMap.ext <| addMonoidHom_eq_of_elementary φ (pullback f n) fun c v => by
    rw [hφ, pullback_elementary]

/-- In degree `0`, `pullback f 0` identifies with `f` via `exteriorPower.zeroEquiv`. -/
@[simp]
theorem zeroEquiv_pullback_zeroEquiv_symm (f : B →ₐ[A] C) (b : B) :
    exteriorPower.zeroEquiv C (KaehlerDifferential A C)
        (pullback f 0 ((exteriorPower.zeroEquiv B (KaehlerDifferential A B)).symm b)) =
      f b := by
  rw [← elementary_zero_eq_zeroEquiv_symm b Fin.elim0, pullback_elementary, zeroEquiv_elementary]

/-- In degree `1`, `pullback f 1` identifies with `KaehlerDifferential.mapSemilinear f` via
`exteriorPower.oneEquiv`. -/
@[simp]
theorem oneEquiv_pullback (f : B →ₐ[A] C) (ω : Forms A B 1) :
    exteriorPower.oneEquiv C (KaehlerDifferential A C) (pullback f 1 ω) =
      KaehlerDifferential.mapSemilinear f
        (exteriorPower.oneEquiv B (KaehlerDifferential A B) ω) :=
  addMonoidHom_eq_of_elementary
    ((exteriorPower.oneEquiv C (KaehlerDifferential A C)).toLinearMap.comp (pullback f 1))
    ((KaehlerDifferential.mapSemilinear f).comp
      (exteriorPower.oneEquiv B (KaehlerDifferential A B)).toLinearMap)
    (fun c v => by
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, pullback_elementary,
        oneEquiv_elementary, KaehlerDifferential.mapSemilinear_smul,
        KaehlerDifferential.mapSemilinear_D, Function.comp_apply])
    ω

/-- Pullback commutes with the ordinary algebraic de Rham differential:
`pullback f (n + 1) (d ω) = d (pullback f n ω)`. -/
theorem pullback_d (f : B →ₐ[A] C) (n : ℕ) (ω : Forms A B n) :
    pullback f (n + 1) (d A B n ω) = d A C n (pullback f n ω) :=
  addMonoidHom_eq_of_elementary
    ((pullbackLinearMap f (n + 1)).comp (d A B n))
    ((d A C n).comp (pullbackLinearMap f n))
    (fun c v => by
      simp only [LinearMap.comp_apply, pullbackLinearMap_apply, d_elementary, pullback_ιMulti,
        pullback_elementary, Fin.comp_cons]
      simp only [KaehlerDifferential.mapSemilinear_D, Function.comp_def])
    ω

/-- Pullback preserves the exterior wedge product of differential forms. -/
theorem pullback_wedge (f : B →ₐ[A] C) {m n : ℕ} (α : Forms A B m) (β : Forms A B n) :
    pullback f (m + n) (exteriorPower.wedge B (KaehlerDifferential A B) m n α β) =
      exteriorPower.wedge C (KaehlerDifferential A C) m n (pullback f m α) (pullback f n β) := by
  induction α using induction_elementary with
  | zero => simp only [map_zero, LinearMap.zero_apply]
  | add α₁ α₂ h₁ h₂ => simp only [map_add, LinearMap.add_apply, h₁, h₂]
  | elem c u =>
    induction β using induction_elementary with
    | zero => simp only [map_zero]
    | add β₁ β₂ h₁ h₂ => simp only [map_add, h₁, h₂]
    | elem c' v =>
      simp only [wedge_elementary, pullback_elementary, map_mul, Fin.comp_append]

/-- Pullback along the identity `A`-algebra homomorphism is the identity on `Forms A B n`. -/
theorem pullback_id (n : ℕ) :
    (pullback (AlgHom.id A B) n : Forms A B n →ₗ[B] Forms A B n) = LinearMap.id :=
  -- `(AlgHom.id A B).toRingHom` is definitionally `RingHom.id B`.
  (pullback_unique (AlgHom.id A B) n (φ := (LinearMap.id : Forms A B n →ₗ[B] Forms A B n))
    fun c v => by
      -- `rw [LinearMap.id_apply]` / `simp` fail: `LinearMap.id` has type `→ₗ[B]` (`RingHom.id B`),
      -- whereas `pullback_unique` applies `DFunLike.coe` at `→ₛₗ[(AlgHom.id A B).toRingHom]`.
      change elementary A c v = _
      simp only [AlgHom.id_apply, Function.comp_def]).symm

/-- Pullback along the identity fixes every differential `n`-form. -/
@[simp]
theorem pullback_id_apply (n : ℕ) (ω : Forms A B n) :
    pullback (AlgHom.id A B) n ω = ω :=
  DFunLike.congr_fun (pullback_id n) ω

/-- Pullback is functorial with respect to composition of `A`-algebra homomorphisms. -/
theorem pullback_comp (g : C →ₐ[A] E) (f : B →ₐ[A] C) (n : ℕ) :
    pullback (g.comp f) n = (pullback g n).comp (pullback f n) :=
  (pullback_unique (g.comp f) n fun c v => by
    simp only [LinearMap.comp_apply, pullback_elementary, AlgHom.comp_apply,
      Function.comp_def]).symm

/-- Pullback along `g.comp f` applies `pullback f` followed by `pullback g`. -/
@[simp]
theorem pullback_comp_apply (g : C →ₐ[A] E) (f : B →ₐ[A] C) (n : ℕ) (ω : Forms A B n) :
    pullback (g.comp f) n ω = pullback g n (pullback f n ω) :=
  DFunLike.congr_fun (pullback_comp g f n) ω

end Pullback

section ComplexMap

universe u v

variable {A : Type u} {B C E : Type v} [CommRing A] [CommRing B] [CommRing C] [CommRing E]
  [Algebra A B] [Algebra A C] [Algebra A E]

/-- The functorial morphism of ordinary algebraic de Rham complexes `Ω•_(B/A) ⟶ Ω•_(C/A)` induced
by an `A`-algebra homomorphism `f : B →ₐ[A] C`. -/
def complexMap (f : B →ₐ[A] C) : complex A B ⟶ complex A C :=
  CochainComplex.ofHom
    (fun n => ModuleCat.ofHom (pullbackLinearMap f n))
    (fun n => by
      simp only [complex_d, complex_X]
      refine ModuleCat.hom_ext <| LinearMap.ext fun ω => ?_
      simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.comp_apply,
        pullbackLinearMap_apply]
      exact (pullback_d f n ω).symm)

/-- In degree `n`, `complexMap f` is the `ModuleCat` morphism induced by `pullbackLinearMap f n`. -/
@[simp]
theorem complexMap_f (f : B →ₐ[A] C) (n : ℕ) :
    (complexMap f).f n = ModuleCat.ofHom (pullbackLinearMap f n) :=
  (rfl)

/-- Pointwise evaluation of `complexMap f` in degree `n` is `pullback f n`. -/
theorem complexMap_apply (f : B →ₐ[A] C) (n : ℕ) (ω : Forms A B n) :
    (complexMap f).f n ω = pullback f n ω := by
  rw [complexMap_f]
  exact (ModuleCat.ofHom_apply (pullbackLinearMap f n) ω).trans (pullbackLinearMap_apply f n ω)

/-- `complexMap` sends the identity algebra homomorphism to the identity cochain map. -/
@[simp]
theorem complexMap_id : complexMap (AlgHom.id A B) = 𝟙 (complex A B) := by
  refine HomologicalComplex.hom_ext _ _ fun n => ?_
  simp only [HomologicalComplex.id_f, complexMap_f, complex_X]
  refine ModuleCat.hom_ext <| LinearMap.ext fun ω => ?_
  simp only [ModuleCat.hom_id, LinearMap.id_apply, ModuleCat.hom_ofHom, pullbackLinearMap_apply]
  exact pullback_id_apply n ω

/-- `complexMap` is covariant with respect to composition of `A`-algebra homomorphisms. -/
@[simp]
theorem complexMap_comp (g : C →ₐ[A] E) (f : B →ₐ[A] C) :
    complexMap (g.comp f) = complexMap f ≫ complexMap g := by
  refine HomologicalComplex.hom_ext _ _ fun n => ?_
  simp only [HomologicalComplex.comp_f, complexMap_f, complex_X]
  refine ModuleCat.hom_ext <| LinearMap.ext fun ω => ?_
  simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.comp_apply, pullbackLinearMap_apply]
  exact pullback_comp_apply g f n ω

end ComplexMap

end TauCeti.DeRham
