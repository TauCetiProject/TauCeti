/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.Kaehler.Map
public import TauCeti.RingTheory.Huber.Kaehler.UniversalProperty

import TauCeti.RingTheory.Derivation.Quotient
import TauCeti.RingTheory.Huber.NoetherianType.Quotient
import TauCeti.RingTheory.Huber.TopologicallyFiniteType.Comp

/-!
# Base change and exact sequences for continuous differentials

This file establishes the three fundamental functorial properties of the module of continuous
differentials `Ωᶜ[B⁄A]` of topologically finite type Huber algebras (Huber 1996, Proposition 1.6.3),
which feed the sheafification of continuous differentials to `Ω¹_{X/Y}` on adic spaces,
rational-localisation base change (Huber 1996, Proposition 1.6.3(iv)), and the theory of
unramified, smooth, and étale morphisms of adic spaces:

* **First fundamental exact sequence (Proposition 1.6.3(i))**: for a tower `A → B → C` of adic
  homomorphisms:
  - `exact_mapBaseChange_mapTower_of_comp`: `C ⊗[B] Ωᶜ[B⁄A] → Ωᶜ[C⁄A] → Ωᶜ[C⁄B]` is exact at
    `Ωᶜ[C⁄A]` when `A, C` are Huber rings, `B, C` are complete Hausdorff nonarchimedean rings with
    `C` of noetherian type, `B → C` is continuous, and `A → C` is topologically of finite type.
  - `mapTower_surjective`: `Ωᶜ[C⁄A] → Ωᶜ[C⁄B]` is surjective when `B, C` are Huber rings, `C` is
    complete Hausdorff of noetherian type, and `B → C` is topologically of finite type.
  - `exact_mapBaseChange_mapTower`: `C ⊗[B] Ωᶜ[B⁄A] → Ωᶜ[C⁄A] → Ωᶜ[C⁄B]` is exact at `Ωᶜ[C⁄A]`
    when `A, B, C` are Huber rings, `B, C` are complete Hausdorff with `B` of noetherian type,
    `B → C` is continuous, and both `A → B` and `B → C` are topologically of finite type.
* **Conormal exact sequence (Proposition 1.6.3(ii))**: for a tower `A → B → C` with kernel
  `J = ker(B → C)`:
  - `exact_kerCotangentToTensor_mapBaseChange`: `J / J² → C ⊗[B] Ωᶜ[B⁄A] → Ωᶜ[C⁄A]` is exact at
    `C ⊗[B] Ωᶜ[B⁄A]` when `A, B` are Huber rings, `B` is complete Hausdorff of noetherian type,
    `A → B` is topologically of finite type, and `B → C` is an open quotient map into a complete
    Hausdorff nonarchimedean ring `C`.
  - `mapBaseChange_surjective`: `C ⊗[B] Ωᶜ[B⁄A] → Ωᶜ[C⁄A]` is surjective when `A, C` are Huber
    rings, `B, C` are complete Hausdorff nonarchimedean rings with `C` of noetherian type, `B → C`
    is a continuous surjection, and `A → C` is topologically of finite type.
* **Completed base change (Proposition 1.6.3(iii))**: when `A → B` is topologically of finite type
  into a complete Hausdorff Huber ring `B` of noetherian type and `A → A'` is an adic homomorphism
  into a Huber ring `A'` of noetherian type (with no completeness hypothesis on `A'`), there is a
  `B'`-linear isomorphism `Ωᶜ[B'⁄A'] ≃ₗ[B'] B' ⊗[B] Ωᶜ[B⁄A]` for `B' = B ⊗̂_A A'`
  (`baseChangeEquiv`). Here `B' = CompletedTensor A B A'` carries the non-global local instances
  `CompletedTensor.leftAlgebra` (as a `B`-algebra), `CompletedTensor.rightAlgebra` (as an
  `A'`-algebra), and `CompletedTensor.isAdicHom_rightAlgebra`.

The conormal maps (`kerToTensor`, `kerCotangentToTensor`) are adapted from
`KaehlerDifferential.kerToTensor` and `KaehlerDifferential.kerCotangentToTensor` in
`Mathlib.RingTheory.Kaehler.Basic`, and the exact-sequence and base-change API mirrors
`KaehlerDifferential.exact_mapBaseChange_map`,
`KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange`, and
`KaehlerDifferential.tensorKaehlerEquiv` in `Mathlib.RingTheory.Kaehler.Basic` and
`Mathlib.RingTheory.Kaehler.TensorProduct`.

## Main definitions and results

* `TauCeti.Huber.ContinuousKaehlerDifferential.mapTower`,
  `TauCeti.Huber.ContinuousKaehlerDifferential.mapBaseChange`: the maps in the first fundamental
  sequence `C ⊗[B] Ωᶜ[B⁄A] →ₗ[C] Ωᶜ[C⁄A] →ₗ[C] Ωᶜ[C⁄B]`.
* `TauCeti.Huber.ContinuousKaehlerDifferential.exact_mapBaseChange_mapTower_of_comp`,
  `TauCeti.Huber.ContinuousKaehlerDifferential.exact_mapBaseChange_mapTower`,
  `TauCeti.Huber.ContinuousKaehlerDifferential.mapTower_surjective`: exactness and surjectivity of
  the first fundamental sequence.
* `TauCeti.Huber.ContinuousKaehlerDifferential.kerToTensor`,
  `TauCeti.Huber.ContinuousKaehlerDifferential.kerCotangentToTensor`,
  `TauCeti.Huber.ContinuousKaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange`,
  `TauCeti.Huber.ContinuousKaehlerDifferential.mapBaseChange_surjective`: the conormal map
  `J / J² →ₗ[B] C ⊗[B] Ωᶜ[B⁄A]` and exactness of the conormal sequence.
* `TauCeti.Huber.ContinuousKaehlerDifferential.baseChangeEquiv`: the completed base-change
  isomorphism `Ωᶜ[(B ⊗̂_A A')⁄A'] ≃ₗ[B ⊗̂_A A'] (B ⊗̂_A A') ⊗[B] Ωᶜ[B⁄A]`.

## References

* R. Huber, *Étale cohomology of rigid analytic varieties and adic spaces*, Aspects of
  Mathematics E30 (1996), §1.6, Proposition 1.6.3.
-/

public section

open TensorProduct Topology

namespace TauCeti.Huber.ContinuousKaehlerDifferential

open CompletedTensor

/-! ### Maps in a tower `A → B → C` -/

section MapTower

variable (A B C : Type*) [CommRing A] [CommRing B] [CommRing C]
  [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
  [TopologicalSpace A] [IsTopologicalRing A]
  [TopologicalSpace B] [IsTopologicalRing B]
  [UniformSpace C] [IsUniformAddGroup C] [NonarchimedeanRing C] [CompleteSpace C] [T0Space C]
  [IsAdicHom (algebraMap A C)] [IsAdicHom (algebraMap B C)]

/-- The relative projection `Ωᶜ[C⁄A] →ₗ[C] Ωᶜ[C⁄B]` in a tower `A → B → C`. -/
noncomputable def mapTower :
    ContinuousKaehlerDifferential A C →ₗ[C] ContinuousKaehlerDifferential B C :=
  mapSemilinear (algebraMap A B) (RingHom.id C)
    (by ext a; exact IsScalarTower.algebraMap_apply A B C a) continuous_id

/-- `mapTower` agrees with the semilinear change-of-rings map along `A → B` and `id_C`. -/
theorem mapTower_eq_mapSemilinear :
    mapTower A B C =
      mapSemilinear (algebraMap A B) (RingHom.id C)
        (by ext a; exact IsScalarTower.algebraMap_apply A B C a) continuous_id := (rfl)

/-- `mapTower` sends a diagonal class in `ideal A C` to the class of its image in `ideal B C`. -/
@[simp]
theorem mapTower_fromIdeal (x : ideal A C) :
    mapTower A B C (fromIdeal A C x) =
      fromIdeal B C
        ⟨CompletedTensor.map (algebraMap A B) (RingHom.id C) (RingHom.id C)
            (by ext a; exact IsScalarTower.algebraMap_apply A B C a)
            (by ext a; exact IsScalarTower.algebraMap_apply A B C a)
            continuous_id continuous_id x,
          ideal_le_comap_map (algebraMap A B) (RingHom.id C) _ continuous_id x.2⟩ :=
  mapSemilinear_fromIdeal _ _ _ continuous_id x

/-- `mapTower` carries `d_A c` to `d_B c`. -/
@[simp]
theorem mapTower_D (c : C) :
    mapTower A B C (D A C c) = D B C c :=
  mapSemilinear_D _ _ _ continuous_id c

end MapTower

section MapTowerComp

variable (A B C E : Type*) [CommRing A] [CommRing B] [CommRing C] [CommRing E]
  [Algebra A B] [Algebra B C] [Algebra C E]
  [Algebra A C] [Algebra B E] [Algebra A E]
  [IsScalarTower B C E] [IsScalarTower A B E] [IsScalarTower A C E]
  [TopologicalSpace A] [IsTopologicalRing A]
  [TopologicalSpace B] [IsTopologicalRing B]
  [TopologicalSpace C] [IsTopologicalRing C]
  [UniformSpace E] [IsUniformAddGroup E] [NonarchimedeanRing E] [CompleteSpace E] [T0Space E]
  [IsAdicHom (algebraMap A E)] [IsAdicHom (algebraMap B E)] [IsAdicHom (algebraMap C E)]

/-- Applying two consecutive relative projections in a tower `A → B → C → E` equals the single
projection `Ωᶜ[E⁄A] → Ωᶜ[E⁄C]`. -/
@[simp]
theorem mapTower_mapTower (ω : ContinuousKaehlerDifferential A E) :
    mapTower B C E (mapTower A B E ω) = mapTower A C E ω := by
  rw [mapTower_eq_mapSemilinear, mapTower_eq_mapSemilinear, mapTower_eq_mapSemilinear,
    mapSemilinear_comp]
  obtain ⟨x, rfl⟩ := fromIdeal_surjective A E ω
  simp only [mapSemilinear_fromIdeal]
  congr 1
  ext
  exact congrArg (fun f : CompletedTensor A E E →+* CompletedTensor C E E ↦ f x) <|
    CompletedTensor.hom_ext (CompletedTensor.continuous_map ..)
      (CompletedTensor.continuous_map ..)
      (by ext e; simp) (by ext e; simp)

/-- Composing relative projections in a tower `A → B → C → E` equals the projection from `A` to
`C`. -/
@[simp]
theorem mapTower_comp_mapTower :
    (mapTower B C E).comp (mapTower A B E) = mapTower A C E :=
  LinearMap.ext (mapTower_mapTower A B C E)

end MapTowerComp

section MapBaseChange

variable (A B C : Type*) [CommRing A] [CommRing B] [CommRing C]
  [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
  [TopologicalSpace A] [IsTopologicalRing A]
  [UniformSpace B] [IsUniformAddGroup B] [NonarchimedeanRing B] [CompleteSpace B] [T0Space B]
  [UniformSpace C] [IsUniformAddGroup C] [NonarchimedeanRing C] [CompleteSpace C] [T0Space C]

/-- The scalar-extended map `C ⊗[B] Ωᶜ[B⁄A] →ₗ[C] Ωᶜ[C⁄A]` in a tower `A → B → C`. -/
noncomputable def mapBaseChange [IsAdicHom (algebraMap A B)] [IsAdicHom (algebraMap A C)]
    (hc : Continuous (algebraMap B C)) :
    C ⊗[B] ContinuousKaehlerDifferential A B →ₗ[C] ContinuousKaehlerDifferential A C :=
  map (RingHom.id A) (by ext a; exact (IsScalarTower.algebraMap_apply A B C a).symm) hc

/-- `mapBaseChange` is the scalar-extended change-of-rings map along `id_A` and `B → C`. -/
theorem mapBaseChange_eq_map [IsAdicHom (algebraMap A B)] [IsAdicHom (algebraMap A C)]
    (hc : Continuous (algebraMap B C)) :
    mapBaseChange A B C hc =
      map (RingHom.id A) (by ext a; exact (IsScalarTower.algebraMap_apply A B C a).symm) hc :=
  (rfl)

/-- Evaluating `mapBaseChange` on a pure tensor `c ⊗ₜ ω`. -/
@[simp]
theorem mapBaseChange_tmul [IsAdicHom (algebraMap A B)] [IsAdicHom (algebraMap A C)]
    (hc : Continuous (algebraMap B C)) (c : C) (ω : ContinuousKaehlerDifferential A B) :
    mapBaseChange A B C hc (c ⊗ₜ[B] ω) =
      c • mapSemilinear (RingHom.id A) (algebraMap B C)
        (by ext a; exact (IsScalarTower.algebraMap_apply A B C a).symm) hc ω :=
  map_tmul _ _ hc c ω

/-- Evaluating `mapBaseChange` on `c ⊗ₜ d b` yields `c • d (algebraMap B C b)`. -/
theorem mapBaseChange_tmul_D [IsAdicHom (algebraMap A B)] [IsAdicHom (algebraMap A C)]
    (hc : Continuous (algebraMap B C)) (c : C) (b : B) :
    mapBaseChange A B C hc (c ⊗ₜ[B] D A B b) = c • D A C (algebraMap B C b) := by
  rw [mapBaseChange_tmul, mapSemilinear_D]

/-- The composite `C ⊗[B] Ωᶜ[B⁄A] → Ωᶜ[C⁄A] → Ωᶜ[C⁄B]` is zero on every class, without any
noetherian or finite-type hypotheses. -/
@[simp]
theorem mapTower_mapBaseChange [IsAdicHom (algebraMap A B)] [IsAdicHom (algebraMap B C)]
    [IsAdicHom (algebraMap A C)] (hc : Continuous (algebraMap B C))
    (z : C ⊗[B] ContinuousKaehlerDifferential A B) :
    mapTower A B C (mapBaseChange A B C hc z) = 0 := by
  induction z using TensorProduct.inductionOn with
  | tmul c ω =>
    rw [mapBaseChange_tmul, map_smul, mapTower_eq_mapSemilinear, mapSemilinear_comp]
    obtain ⟨⟨x, hx⟩, rfl⟩ := fromIdeal_surjective A B ω
    rw [mapSemilinear_fromIdeal]
    have hmap : CompletedTensor.map ((algebraMap A B).comp (RingHom.id A))
        ((RingHom.id C).comp (algebraMap B C)) ((RingHom.id C).comp (algebraMap B C))
        rfl rfl (continuous_id.comp hc) (continuous_id.comp hc) =
        (inl B C C).comp ((algebraMap B C).comp (mulRingHom A B)) :=
      CompletedTensor.hom_ext (CompletedTensor.continuous_map ..)
        ((continuous_inl B C C).comp (hc.comp (continuous_mulRingHom A B)))
        (by ext b; simp) (by ext b; simp)
    have hx0 : CompletedTensor.map ((algebraMap A B).comp (RingHom.id A))
        ((RingHom.id C).comp (algebraMap B C)) ((RingHom.id C).comp (algebraMap B C))
        rfl rfl (continuous_id.comp hc) (continuous_id.comp hc) x = 0 := by
      rw [RingHom.congr_fun hmap x]
      simp [mem_ideal_iff.mp hx]
    have hzero : (⟨_, ideal_le_comap_map ((algebraMap A B).comp (RingHom.id A))
        ((RingHom.id C).comp (algebraMap B C)) _ (continuous_id.comp hc) hx⟩ : ideal B C) = 0 :=
      Subtype.ext hx0
    rw [hzero, map_zero, smul_zero]
  | add x y hx hy => rw [map_add, map_add, hx, hy, add_zero]

end MapBaseChange

section ConormalMap

variable (A B C : Type*) [CommRing A] [CommRing B] [CommRing C]
  [Algebra A B] [Algebra B C]
  [TopologicalSpace A] [IsTopologicalRing A]
  [UniformSpace B] [IsUniformAddGroup B] [NonarchimedeanRing B] [CompleteSpace B] [T0Space B]
  [IsAdicHom (algebraMap A B)]

/-- The `B`-linear map `J →ₗ[B] C ⊗[B] Ωᶜ[B⁄A]` for `J = ker(B → C)`, sending `x ↦ 1 ⊗ₜ d x`,
adapted from Mathlib's `KaehlerDifferential.kerToTensor`. -/
noncomputable def kerToTensor :
    RingHom.ker (algebraMap B C) →ₗ[B] C ⊗[B] ContinuousKaehlerDifferential A B where
  toFun x := 1 ⊗ₜ[B] D A B x.1
  map_add' x y := by simp [tmul_add]
  map_smul' b x := by
    simp only [SetLike.val_smul, smul_eq_mul, Derivation.leibniz, tmul_add, tmul_smul,
      smul_tmul', ← Algebra.algebraMap_eq_smul_one, RingHom.mem_ker.mp x.2, zero_tmul, add_zero,
      RingHom.id_apply]

/-- Evaluating `kerToTensor` on `x ∈ ker(B → C)` yields `1 ⊗ₜ d x`. -/
@[simp]
theorem kerToTensor_apply (x : RingHom.ker (algebraMap B C)) :
    kerToTensor A B C x = 1 ⊗ₜ[B] D A B x.1 := (rfl)

/-- The conormal map `J / J² →ₗ[B] C ⊗[B] Ωᶜ[B⁄A]` for `J = ker(B → C)` (Huber 1996,
Proposition 1.6.3(ii)), adapted from Mathlib's `KaehlerDifferential.kerCotangentToTensor`. -/
noncomputable def kerCotangentToTensor :
    (RingHom.ker (algebraMap B C)).Cotangent →ₗ[B] C ⊗[B] ContinuousKaehlerDifferential A B :=
  Ideal.Cotangent.lift (kerToTensor A B C) fun x y ↦ by
    simp only [kerToTensor_apply, MulMemClass.coe_mul, Derivation.leibniz, tmul_add,
      ← smul_tmul, ← Algebra.algebraMap_eq_smul_one, RingHom.mem_ker.mp x.2,
      RingHom.mem_ker.mp y.2, zero_tmul, add_zero]

/-- Evaluating `kerCotangentToTensor` on the cotangent class of `x ∈ ker(B → C)` gives
`1 ⊗ₜ d x`. -/
@[simp]
theorem kerCotangentToTensor_toCotangent (x : RingHom.ker (algebraMap B C)) :
    kerCotangentToTensor A B C ((RingHom.ker (algebraMap B C)).toCotangent x) =
      1 ⊗ₜ[B] D A B x.1 := by
  rw [kerCotangentToTensor, Ideal.Cotangent.lift_toCotangent, kerToTensor_apply]

/-- The composite `J / J² → C ⊗[B] Ωᶜ[B⁄A] → Ωᶜ[C⁄A]` vanishes identically. -/
@[simp]
theorem mapBaseChange_kerCotangentToTensor [Algebra A C] [IsScalarTower A B C]
    [UniformSpace C] [IsUniformAddGroup C] [NonarchimedeanRing C] [CompleteSpace C] [T0Space C]
    [IsAdicHom (algebraMap A C)]
    (hc : Continuous (algebraMap B C)) (u : (RingHom.ker (algebraMap B C)).Cotangent) :
    mapBaseChange A B C hc (kerCotangentToTensor A B C u) = 0 := by
  obtain ⟨x, rfl⟩ := (RingHom.ker (algebraMap B C)).toCotangent_surjective u
  rw [kerCotangentToTensor_toCotangent, mapBaseChange_tmul_D, RingHom.mem_ker.mp x.2,
    map_zero, smul_zero]

end ConormalMap

/-! ### First fundamental exact sequence (Huber 1996, Proposition 1.6.3(i)) -/

section MapTowerSurjective

variable {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
  [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
  [TopologicalSpace A] [IsTopologicalRing A]
  [TopologicalSpace B] [IsTopologicalRing B] [IsHuberRing B]
  [UniformSpace C] [IsUniformAddGroup C] [IsTopologicalRing C] [IsHuberRing C]
  [CompleteSpace C] [T0Space C] [IsNoetherianType C]
  [IsAdicHom (algebraMap A C)] [IsAdicHom (algebraMap B C)]

/-- **Surjectivity in the first fundamental sequence** (Huber 1996, Proposition 1.6.3(i)): when
`B` and `C` are Huber rings, `C` is complete Hausdorff of noetherian type, and `B → C` is
topologically of finite type, `Ωᶜ[C⁄A] → Ωᶜ[C⁄B]` is surjective. -/
theorem mapTower_surjective (hBC : IsTopologicallyFiniteType (algebraMap B C)) :
    Function.Surjective (mapTower A B C) := by
  rw [← LinearMap.range_eq_top, eq_top_iff, ← span_range_derivation hBC, Submodule.span_le]
  rintro _ ⟨c, rfl⟩
  exact ⟨D A C c, mapTower_D A B C c⟩

end MapTowerSurjective

section FirstFundamentalSequenceOfComp

variable {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
  [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
  [TopologicalSpace A] [IsTopologicalRing A] [IsHuberRing A]
  [UniformSpace B] [IsUniformAddGroup B] [NonarchimedeanRing B] [CompleteSpace B] [T0Space B]
  [UniformSpace C] [IsUniformAddGroup C] [IsTopologicalRing C] [IsHuberRing C]
  [CompleteSpace C] [T0Space C] [IsNoetherianType C]
  [IsAdicHom (algebraMap A B)] [IsAdicHom (algebraMap B C)] [IsAdicHom (algebraMap A C)]

/-- **First fundamental exact sequence from topological finite type of the composite**: when `A, C`
are Huber rings, `B, C` are complete Hausdorff nonarchimedean rings with `C` of noetherian type,
`B → C` is continuous, and `A → C` is topologically of finite type,
`C ⊗[B] Ωᶜ[B⁄A] → Ωᶜ[C⁄A] → Ωᶜ[C⁄B]` is exact. -/
theorem exact_mapBaseChange_mapTower_of_comp
    (hc : Continuous (algebraMap B C)) (hAC : IsTopologicallyFiniteType (algebraMap A C)) :
    Function.Exact (mapBaseChange A B C hc) (mapTower A B C) := by
  refine LinearMap.exact_iff.mpr (le_antisymm ?_
    (LinearMap.range_le_ker_iff.mpr (LinearMap.ext (mapTower_mapBaseChange A B C hc))))
  have : Module.Finite C (ContinuousKaehlerDifferential A C) := finite hAC
  let R : Submodule C (ContinuousKaehlerDifferential A C) :=
    LinearMap.range (mapBaseChange A B C hc)
  let Q := ContinuousKaehlerDifferential A C ⧸ R
  let : TopologicalSpace Q := moduleTopology C Q
  have : IsModuleTopology C Q := ⟨rfl⟩
  let : IsTopologicalAddGroup Q := IsModuleTopology.isTopologicalAddGroup C Q
  let : Module B Q := Module.compHom Q (algebraMap B C)
  have : IsScalarTower B C Q := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let δB : Derivation B C Q :=
    { toFun c := R.mkQ (D A C c)
      map_add' x y := by simp
      map_smul' b c := by
        rw [RingHom.id_apply, Algebra.smul_def, Derivation.leibniz, map_add, map_smul, map_smul]
        have h0 : R.mkQ (D A C (algebraMap B C b)) = 0 :=
          (Submodule.Quotient.mk_eq_zero R).mpr ⟨1 ⊗ₜ[B] D A B b, by simp⟩
        rw [h0, smul_zero, add_zero, ← algebraMap_smul C b]
      map_one_eq_zero' := by simp
      leibniz' x y := by simp [Derivation.leibniz] }
  have hδB_apply (c : C) : δB c = R.mkQ (D A C c) := rfl
  have hδB : Continuous δB :=
    (IsModuleTopology.continuous_of_linearMap R.mkQ).comp (continuous_D hAC)
  let s : ContinuousKaehlerDifferential B C →ₗ[C] Q := liftOfFinite δB hδB
  have hs : s.comp (mapTower A B C) = R.mkQ :=
    linearMap_ext hAC fun c ↦ by
      simp only [LinearMap.comp_apply, mapTower_D, s, liftOfFinite_D, hδB_apply]
  intro ω hω
  have h0 : R.mkQ ω = 0 := by rw [← hs, LinearMap.comp_apply, LinearMap.mem_ker.mp hω, map_zero]
  exact (Submodule.Quotient.mk_eq_zero R).mp h0

end FirstFundamentalSequenceOfComp

section FirstFundamentalSequence

variable {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
  [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
  [TopologicalSpace A] [IsTopologicalRing A] [IsHuberRing A]
  [UniformSpace B] [IsUniformAddGroup B] [IsTopologicalRing B] [IsHuberRing B]
  [CompleteSpace B] [T0Space B] [IsNoetherianType B]
  [UniformSpace C] [IsUniformAddGroup C] [IsTopologicalRing C] [IsHuberRing C]
  [CompleteSpace C] [T0Space C]
  [IsAdicHom (algebraMap A B)] [IsAdicHom (algebraMap B C)] [IsAdicHom (algebraMap A C)]

/-- **Huber Proposition 1.6.3(i) (First fundamental exact sequence)**: for topologically finite
type homomorphisms `A → B` and `B → C` between Huber rings with `B, C` complete Hausdorff and `B`
of noetherian type, `C ⊗[B] Ωᶜ[B⁄A] → Ωᶜ[C⁄A] → Ωᶜ[C⁄B]` is exact. -/
theorem exact_mapBaseChange_mapTower
    (hc : Continuous (algebraMap B C))
    (hAB : IsTopologicallyFiniteType (algebraMap A B))
    (hBC : IsTopologicallyFiniteType (algebraMap B C)) :
    Function.Exact (mapBaseChange A B C hc) (mapTower A B C) := by
  have : IsNoetherianType C := .of_isTopologicallyFiniteType hBC
  have hAC : IsTopologicallyFiniteType (algebraMap A C) :=
    IsScalarTower.algebraMap_eq A B C ▸ hBC.comp hAB
  exact exact_mapBaseChange_mapTower_of_comp hc hAC

end FirstFundamentalSequence

/-! ### Conormal exact sequence (Huber 1996, Proposition 1.6.3(ii)) -/

section MapBaseChangeSurjective

variable {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
  [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
  [TopologicalSpace A] [IsTopologicalRing A] [IsHuberRing A]
  [UniformSpace B] [IsUniformAddGroup B] [NonarchimedeanRing B] [CompleteSpace B] [T0Space B]
  [UniformSpace C] [IsUniformAddGroup C] [IsTopologicalRing C] [IsHuberRing C]
  [CompleteSpace C] [T0Space C] [IsNoetherianType C]
  [IsAdicHom (algebraMap A B)] [IsAdicHom (algebraMap A C)]

/-- **Surjectivity in the conormal sequence** (Huber 1996, Proposition 1.6.3(ii)): when `A, C` are
Huber rings, `B, C` are complete Hausdorff nonarchimedean rings with `C` of noetherian type, `B → C`
is a continuous surjection, and `A → C` is topologically of finite type,
`C ⊗[B] Ωᶜ[B⁄A] → Ωᶜ[C⁄A]` is surjective. -/
theorem mapBaseChange_surjective
    (hc : Continuous (algebraMap B C)) (hsurj : Function.Surjective (algebraMap B C))
    (hAC : IsTopologicallyFiniteType (algebraMap A C)) :
    Function.Surjective (mapBaseChange A B C hc) := by
  rw [← LinearMap.range_eq_top, eq_top_iff, ← span_range_derivation hAC, Submodule.span_le]
  rintro _ ⟨c, rfl⟩
  obtain ⟨b, rfl⟩ := hsurj c
  exact ⟨1 ⊗ₜ[B] D A B b, by simp⟩

end MapBaseChangeSurjective

section ConormalSequence

variable {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
  [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
  [TopologicalSpace A] [IsTopologicalRing A] [IsHuberRing A]
  [UniformSpace B] [IsUniformAddGroup B] [IsTopologicalRing B] [IsHuberRing B]
  [CompleteSpace B] [T0Space B]
  [UniformSpace C] [IsUniformAddGroup C] [NonarchimedeanRing C] [CompleteSpace C] [T0Space C]
  [IsAdicHom (algebraMap A B)] [IsAdicHom (algebraMap A C)]

omit [IsHuberRing A] [IsHuberRing B] [UniformSpace C] [IsUniformAddGroup C]
  [NonarchimedeanRing C] [CompleteSpace C] [T0Space C]
  [IsAdicHom (algebraMap A C)] in
/-- Algebraic quotient derivation `C → (C ⊗[B] Ωᶜ[B⁄A]) ⧸ L` along a surjection `B → C`, sending
the image of `b` to the class of `1 ⊗ₜ d b`. -/
private noncomputable def conormalQuotientDerivation
    (hsurj : Function.Surjective (algebraMap B C))
    (L : Submodule C (C ⊗[B] ContinuousKaehlerDifferential A B))
    (hL : ∀ x ∈ RingHom.ker (algebraMap B C), (1 : C) ⊗ₜ[B] D A B x ∈ L) :
    {δ : Derivation A C ((C ⊗[B] ContinuousKaehlerDifferential A B) ⧸ L) //
      ∀ b : B, δ (algebraMap B C b) = L.mkQ (1 ⊗ₜ[B] D A B b)} := by
  let Q := (C ⊗[B] ContinuousKaehlerDifferential A B) ⧸ L
  let f : B →ₐ[A] C := IsScalarTower.toAlgHom A B C
  let J : Ideal B := RingHom.ker f
  let e : (B ⧸ J) ≃ₐ[A] C := Ideal.quotientKerAlgEquivOfSurjective (f := f) hsurj
  letI : Module (B ⧸ J) Q := Module.compHom Q e.toRingHom
  have hsmul_e (x : B ⧸ J) (q : Q) : x • q = e x • q := rfl
  haveI : IsScalarTower B (B ⧸ J) Q := IsScalarTower.of_algebraMap_smul fun b q ↦ by
    have he : e (Ideal.Quotient.mk J b) = algebraMap B C b :=
      Ideal.quotientKerAlgEquivOfSurjective_mk (f := f) hsurj b
    rw [hsmul_e, Ideal.Quotient.algebraMap_eq, he, algebraMap_smul]
  let lB : ContinuousKaehlerDifferential A B →ₗ[B] Q :=
    (L.mkQ.restrictScalars B).comp (TensorProduct.mk B C (ContinuousKaehlerDifferential A B) 1)
  let dB : Derivation A B Q := lB.compDer (D A B)
  let dQ : Derivation A (B ⧸ J) Q :=
    dB.liftQuotient J fun b hb ↦ (Submodule.Quotient.mk_eq_zero L).mpr (hL b hb)
  letI : Algebra C (B ⧸ J) := e.symm.toRingHom.toAlgebra
  haveI : IsScalarTower A C (B ⧸ J) :=
    IsScalarTower.of_algebraMap_eq fun a ↦ (e.symm.commutes a).symm
  haveI : IsScalarTower C (B ⧸ J) Q := IsScalarTower.of_algebraMap_smul fun c q ↦ by
    simp only [hsmul_e, RingHom.algebraMap_toAlgebra, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
      AlgEquiv.coe_toRingEquiv, e.apply_symm_apply]
  refine ⟨dQ.compAlgebraMap C, fun b ↦ ?_⟩
  have hmk : e.symm (algebraMap B C b) = Ideal.Quotient.mk J b :=
    Ideal.quotientKerAlgEquivOfSurjective_symm_apply (f := f) hsurj b
  have hdQ : dQ (Ideal.Quotient.mk J b) = dB b := Derivation.liftQuotient_mk ..
  simp only [Derivation.compAlgebraMap_apply, RingHom.algebraMap_toAlgebra,
    RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, AlgEquiv.coe_toRingEquiv, hmk, hdQ, dB,
    Derivation.coe_comp, Derivation.coeFn_coe, lB, LinearMap.comp_apply,
    LinearMap.restrictScalars_apply, TensorProduct.mk_apply]

/-- **Huber Proposition 1.6.3(ii) (Conormal exact sequence)**: when `A, B` are Huber rings, `B` is
complete Hausdorff of noetherian type, `A → B` is topologically of finite type, and `B → C` is an
open quotient map into a complete Hausdorff nonarchimedean ring `C`, the sequence
`J / J² → C ⊗[B] Ωᶜ[B⁄A] → Ωᶜ[C⁄A]` is exact for `J = ker(B → C)`. -/
theorem exact_kerCotangentToTensor_mapBaseChange [IsNoetherianType B]
    (hAB : IsTopologicallyFiniteType (algebraMap A B))
    (hBC : IsOpenQuotientMap (algebraMap B C)) :
    Function.Exact (kerCotangentToTensor A B C) (mapBaseChange A B C hBC.continuous) := by
  intro z
  refine ⟨fun hz ↦ ?_, fun ⟨u, hu⟩ ↦ hu ▸ mapBaseChange_kerCotangentToTensor A B C hBC.continuous u⟩
  have : IsHuberRing C := .of_isOpenQuotientMap hBC
  have : IsNoetherianType C := .of_isOpenQuotientMap hBC
  have : Module.Finite B (ContinuousKaehlerDifferential A B) := finite hAB
  let L : Submodule C (C ⊗[B] ContinuousKaehlerDifferential A B) :=
    (Submodule.orderIsoOfAlgebraMapSurjective hBC.surjective).symm
      (LinearMap.range (kerCotangentToTensor A B C))
  let Q := (C ⊗[B] ContinuousKaehlerDifferential A B) ⧸ L
  let : TopologicalSpace Q := moduleTopology C Q
  have : IsModuleTopology C Q := ⟨rfl⟩
  let : IsTopologicalAddGroup Q := IsModuleTopology.isTopologicalAddGroup C Q
  have : ContinuousSMul B C := continuousSMul_of_algebraMap B C hBC.continuous
  have : ContinuousSMul B Q := IsScalarTower.continuousSMul C
  obtain ⟨δC, hδC_eq⟩ := conormalQuotientDerivation hBC.surjective L fun x hx ↦
    ⟨(RingHom.ker (algebraMap B C)).toCotangent ⟨x, hx⟩,
      kerCotangentToTensor_toCotangent A B C ⟨x, hx⟩⟩
  let lB : ContinuousKaehlerDifferential A B →ₗ[B] Q :=
    (L.mkQ.restrictScalars B).comp (TensorProduct.mk B C (ContinuousKaehlerDifferential A B) 1)
  have hδC : Continuous δC := hBC.isQuotientMap.continuous_iff.mpr <|
    ((IsModuleTopology.continuous_of_linearMap lB).comp (continuous_D hAB)).congr
      fun b ↦ (hδC_eq b).symm
  let s : ContinuousKaehlerDifferential A C →ₗ[C] Q := liftOfFinite δC hδC
  have hs : s.comp (mapBaseChange A B C hBC.continuous) = L.mkQ :=
    linearMap_tensor_ext hAB fun b ↦ by
      simp only [LinearMap.comp_apply, mapBaseChange_tmul_D, one_smul, s, liftOfFinite_D, hδC_eq]
  have h0 : L.mkQ z = 0 := by rw [← hs, LinearMap.comp_apply, hz, map_zero]
  exact (Submodule.Quotient.mk_eq_zero L).mp h0

end ConormalSequence

/-! ### Completed base change (Huber 1996, Proposition 1.6.3(iii)) -/

section BaseChange

variable {A B A' : Type*} [CommRing A] [CommRing B] [CommRing A']
  [Algebra A B] [Algebra A A']
  [TopologicalSpace A] [IsTopologicalRing A] [IsHuberRing A]
  [UniformSpace B] [IsUniformAddGroup B] [IsTopologicalRing B] [IsHuberRing B]
  [CompleteSpace B] [T0Space B] [IsNoetherianType B]
  [TopologicalSpace A'] [IsTopologicalRing A'] [IsHuberRing A'] [IsNoetherianType A']
  [IsAdicHom (algebraMap A B)] [IsAdicHom (algebraMap A A')]

attribute [local instance] leftAlgebra rightAlgebra isAdicHom_rightAlgebra

/-- Equip `(B ⊗̂_A A') ⊗[B] Ωᶜ[B⁄A]` with its natural `(B ⊗̂_A A')`-module topology and construct
the universal continuous `A'`-derivation `B ⊗̂_A A' → (B ⊗̂_A A') ⊗[B] Ωᶜ[B⁄A]`. -/
private noncomputable def baseChangeDerivation
    (hAB : IsTopologicallyFiniteType (algebraMap A B)) :
    let B' := CompletedTensor A B A'
    let M := B' ⊗[B] ContinuousKaehlerDifferential A B
    letI : TopologicalSpace M := moduleTopology B' M
    {δ : Derivation A' B' M // Continuous δ ∧ ∀ b : B, δ (inl A B A' b) = 1 ⊗ₜ[B] D A B b} := by
  let B' := CompletedTensor A B A'
  let M := B' ⊗[B] ContinuousKaehlerDifferential A B
  have hA'B' : IsTopologicallyFiniteType (algebraMap A' B') := by
    rw [algebraMap_rightAlgebra]; exact isTopologicallyFiniteType_inr hAB
  have : IsNoetherianType B' := .of_isTopologicallyFiniteType hA'B'
  have : Module.Finite B (ContinuousKaehlerDifferential A B) := finite hAB
  letI : TopologicalSpace M := moduleTopology B' M
  have : IsModuleTopology B' M := ⟨rfl⟩
  letI : IsTopologicalAddGroup M := IsModuleTopology.isTopologicalAddGroup B' M
  letI : UniformSpace M := IsTopologicalAddGroup.rightUniformSpace M
  obtain ⟨_, _, _, _⟩ :=
    IsNoetherianType.complete_t2_nonarchimedean_of_isModuleTopology (A := B') (M := M)
  haveI : IsScalarTower A B B' := IsScalarTower.of_algebraMap_eq fun a ↦ by simp [B']
  haveI : IsScalarTower A A' B' := IsScalarTower.of_algebraMap_eq fun a ↦ by simp [B']
  have : ContinuousSMul B B' :=
    continuousSMul_of_algebraMap B B' (by rw [algebraMap_leftAlgebra]; exact continuous_inl A B A')
  have : ContinuousSMul B M := IsScalarTower.continuousSMul B'
  let dB : Derivation A B M :=
    (TensorProduct.mk B B' (ContinuousKaehlerDifferential A B) 1).compDer (D A B)
  have hdB : Continuous dB :=
    (IsModuleTopology.continuous_of_linearMap
      (TensorProduct.mk B B' (ContinuousKaehlerDifferential A B) 1)).comp (continuous_D hAB)
  have h0 : Continuous (0 : Derivation A A' M) := continuous_const
  have hinl : (algebraMap B' B').comp (inl A B A') = algebraMap B B' := by
    rw [Algebra.algebraMap_self, RingHom.id_comp, algebraMap_leftAlgebra]
  have hinr : (algebraMap B' B').comp (inr A B A') = algebraMap A' B' := by
    rw [Algebra.algebraMap_self, RingHom.id_comp, algebraMap_rightAlgebra]
  let dA : Derivation A B' M :=
    CompletedTensor.liftDerivation (R := B') dB (0 : Derivation A A' M) hdB h0 continuous_id
      hinl hinr
  have hdA_inr (a' : A') : dA (inr A B A' a') = 0 :=
    (liftDerivation_inr (R := B') dB (0 : Derivation A A' M) hdB h0 continuous_id
      hinl hinr a').trans (zero_apply a')
  let δ : Derivation A' B' M :=
    Derivation.mk'
      { toFun := dA
        map_add' := dA.map_add
        map_smul' a' z := by
          rw [RingHom.id_apply, Algebra.smul_def, dA.leibniz, algebraMap_smul,
            algebraMap_rightAlgebra, hdA_inr, smul_zero, add_zero] }
      dA.leibniz
  exact ⟨δ, continuous_liftDerivation (R := B') dB (0 : Derivation A A' M) hdB h0 continuous_id
      hinl hinr, fun b ↦ liftDerivation_inl (R := B') dB (0 : Derivation A A' M) hdB h0
      continuous_id hinl hinr b⟩

/-- Scalar-extended comparison map `(B ⊗̂_A A') ⊗[B] Ωᶜ[B⁄A] →ₗ[B ⊗̂_A A'] Ωᶜ[(B ⊗̂_A A')⁄A']`. -/
private noncomputable def baseChangeFromTensor :
    CompletedTensor A B A' ⊗[B] ContinuousKaehlerDifferential A B →ₗ[CompletedTensor A B A']
      ContinuousKaehlerDifferential A' (CompletedTensor A B A') :=
  map (algebraMap A A') (by ext a; simp)
    (by rw [algebraMap_leftAlgebra]; exact continuous_inl A B A')

/-- Universal-property map `Ωᶜ[(B ⊗̂_A A')⁄A'] →ₗ[B ⊗̂_A A'] (B ⊗̂_A A') ⊗[B] Ωᶜ[B⁄A]`. -/
private noncomputable def baseChangeToTensor
    (hAB : IsTopologicallyFiniteType (algebraMap A B)) :
    ContinuousKaehlerDifferential A' (CompletedTensor A B A') →ₗ[CompletedTensor A B A']
      CompletedTensor A B A' ⊗[B] ContinuousKaehlerDifferential A B := by
  let B' := CompletedTensor A B A'
  let M := B' ⊗[B] ContinuousKaehlerDifferential A B
  have hA'B' : IsTopologicallyFiniteType (algebraMap A' B') := by
    rw [algebraMap_rightAlgebra]; exact isTopologicallyFiniteType_inr hAB
  have : IsNoetherianType B' := .of_isTopologicallyFiniteType hA'B'
  have : Module.Finite B (ContinuousKaehlerDifferential A B) := finite hAB
  letI : TopologicalSpace M := moduleTopology B' M
  have : IsModuleTopology B' M := ⟨rfl⟩
  exact liftOfFinite (baseChangeDerivation (A' := A') hAB).1
    (baseChangeDerivation (A' := A') hAB).2.1

private theorem baseChangeToTensor_D_inl
    (hAB : IsTopologicallyFiniteType (algebraMap A B)) (b : B) :
    baseChangeToTensor (A' := A') hAB
        (D A' (CompletedTensor A B A') (inl A B A' b)) =
      (1 : CompletedTensor A B A') ⊗ₜ[B] D A B b := by
  let B' := CompletedTensor A B A'
  let M := B' ⊗[B] ContinuousKaehlerDifferential A B
  have hA'B' : IsTopologicallyFiniteType (algebraMap A' B') := by
    rw [algebraMap_rightAlgebra]; exact isTopologicallyFiniteType_inr hAB
  have : IsNoetherianType B' := .of_isTopologicallyFiniteType hA'B'
  have : Module.Finite B (ContinuousKaehlerDifferential A B) := finite hAB
  let : TopologicalSpace M := moduleTopology B' M
  have : IsModuleTopology B' M := ⟨rfl⟩
  exact (liftOfFinite_D (baseChangeDerivation (A' := A') hAB).1
    (baseChangeDerivation (A' := A') hAB).2.1 (inl A B A' b)).trans
    ((baseChangeDerivation (A' := A') hAB).2.2 b)

private theorem baseChangeToTensor_comp_fromTensor
    (hAB : IsTopologicallyFiniteType (algebraMap A B)) :
    (baseChangeToTensor (A' := A') hAB).comp baseChangeFromTensor = LinearMap.id :=
  linearMap_tensor_ext hAB fun b ↦ by
    simp only [LinearMap.comp_apply, LinearMap.id_apply, baseChangeFromTensor, map_tmul,
      mapSemilinear_D, one_smul, algebraMap_leftAlgebra]
    exact baseChangeToTensor_D_inl (A' := A') hAB b

private theorem baseChangeFromTensor_comp_toTensor
    (hAB : IsTopologicallyFiniteType (algebraMap A B)) :
    baseChangeFromTensor.comp (baseChangeToTensor (A' := A') hAB) = LinearMap.id := by
  have hA'B' : IsTopologicallyFiniteType (algebraMap A' (CompletedTensor A B A')) := by
    rw [algebraMap_rightAlgebra]; exact isTopologicallyFiniteType_inr hAB
  have : IsNoetherianType (CompletedTensor A B A') := .of_isTopologicallyFiniteType hA'B'
  refine linearMap_ext_of_dense_adjoin hA'B' (CompletedTensor.dense_adjoin_range_inl A B A') ?_
  rintro _ ⟨b, rfl⟩
  simp only [LinearMap.comp_apply, LinearMap.id_apply, baseChangeToTensor_D_inl,
    baseChangeFromTensor, map_tmul, mapSemilinear_D, one_smul, algebraMap_leftAlgebra]

/-- **Huber Proposition 1.6.3(iii) (Base change of continuous differentials)**: when `A → B` is
topologically of finite type into a complete Hausdorff Huber ring `B` of noetherian type and
`A → A'` is an adic homomorphism into a Huber ring `A'` of noetherian type, completed base change
induces a linear equivalence
`Ωᶜ[(B ⊗̂_A A')⁄A'] ≃ₗ[B ⊗̂_A A'] (B ⊗̂_A A') ⊗[B] Ωᶜ[B⁄A]`.

Here `B ⊗̂_A A' = CompletedTensor A B A'` carries the `B`-algebra structure
`CompletedTensor.leftAlgebra` and the adic `A'`-algebra structure `CompletedTensor.rightAlgebra`
and `CompletedTensor.isAdicHom_rightAlgebra`. -/
noncomputable def baseChangeEquiv (A' : Type*) [CommRing A'] [Algebra A A']
    [TopologicalSpace A'] [IsTopologicalRing A'] [IsHuberRing A'] [IsNoetherianType A']
    [IsAdicHom (algebraMap A A')]
    (hAB : IsTopologicallyFiniteType (algebraMap A B)) :
    ContinuousKaehlerDifferential A' (CompletedTensor A B A') ≃ₗ[CompletedTensor A B A']
      CompletedTensor A B A' ⊗[B] ContinuousKaehlerDifferential A B :=
  LinearEquiv.ofLinearMap (baseChangeToTensor (A' := A') hAB) baseChangeFromTensor
    (baseChangeToTensor_comp_fromTensor (A' := A') hAB)
    (baseChangeFromTensor_comp_toTensor (A' := A') hAB)

/-- The inverse of `baseChangeEquiv` evaluates on a pure tensor `b' ⊗ₜ ω` via the semilinear
change-of-rings map along `A → A'` and `inl : B → B ⊗̂_A A'`. -/
@[simp]
theorem baseChangeEquiv_symm_tmul (hAB : IsTopologicallyFiniteType (algebraMap A B))
    (b' : CompletedTensor A B A') (ω : ContinuousKaehlerDifferential A B) :
    (baseChangeEquiv A' hAB).symm (b' ⊗ₜ[B] ω) =
      b' • mapSemilinear (algebraMap A A') (algebraMap B (CompletedTensor A B A'))
        (by ext a; simp)
        (by rw [algebraMap_leftAlgebra]; exact continuous_inl A B A') ω :=
  map_tmul _ _ _ b' ω

/-- The inverse of `baseChangeEquiv` sends `b' ⊗ₜ d b` to `b' • d (inl b)`. -/
theorem baseChangeEquiv_symm_tmul_D (hAB : IsTopologicallyFiniteType (algebraMap A B))
    (b' : CompletedTensor A B A') (b : B) :
    (baseChangeEquiv A' hAB).symm (b' ⊗ₜ[B] D A B b) =
      b' • D A' (CompletedTensor A B A') (inl A B A' b) := by
  rw [baseChangeEquiv_symm_tmul, mapSemilinear_D, algebraMap_leftAlgebra]

/-- `baseChangeEquiv` sends `d (inl b)` to `1 ⊗ₜ d b`. -/
@[simp]
theorem baseChangeEquiv_D_inl (A' : Type*) [CommRing A'] [Algebra A A']
    [TopologicalSpace A'] [IsTopologicalRing A'] [IsHuberRing A'] [IsNoetherianType A']
    [IsAdicHom (algebraMap A A')]
    (hAB : IsTopologicallyFiniteType (algebraMap A B)) (b : B) :
    baseChangeEquiv A' hAB (D A' (CompletedTensor A B A') (inl A B A' b)) =
      (1 : CompletedTensor A B A') ⊗ₜ[B] D A B b :=
  baseChangeToTensor_D_inl (A' := A') hAB b

/-- `baseChangeEquiv` annihilates `d (inr a')`. -/
@[simp]
theorem baseChangeEquiv_D_inr (hAB : IsTopologicallyFiniteType (algebraMap A B)) (a' : A') :
    baseChangeEquiv A' hAB (D A' (CompletedTensor A B A') (inr A B A' a')) = 0 := by
  rw [← algebraMap_rightAlgebra, Derivation.map_algebraMap, map_zero]

/-- `baseChangeEquiv` sends `d (toCompletion (b ⊗ₜ a'))` to `inr a' ⊗ₜ d b`. -/
theorem baseChangeEquiv_D_toCompletion_tmul (hAB : IsTopologicallyFiniteType (algebraMap A B))
    (b : B) (a' : A') :
    baseChangeEquiv A' hAB (D A' (CompletedTensor A B A') (toCompletion A B A' (b ⊗ₜ[A] a'))) =
      inr A B A' a' ⊗ₜ[B] D A B b := by
  rw [CompletedTensor.toCompletion_tmul, Derivation.leibniz, map_add, map_smul, map_smul,
    baseChangeEquiv_D_inr, smul_zero, zero_add, baseChangeEquiv_D_inl, smul_tmul', smul_eq_mul,
    mul_one]

end BaseChange

end TauCeti.Huber.ContinuousKaehlerDifferential
