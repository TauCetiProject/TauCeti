/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.Kaehler.Map
public import TauCeti.RingTheory.Huber.Kaehler.UniversalProperty

import TauCeti.RingTheory.Huber.NoetherianType.Quotient
import TauCeti.RingTheory.Huber.TopologicallyFiniteType.Comp

/-!
# Base change and exact sequences for continuous differentials

This file establishes the three fundamental functorial properties of the module of continuous
differentials `Ωᶜ[B⁄A]` of topologically finite type Huber algebras (Huber 1996, Proposition 1.6.3):

* **First fundamental exact sequence (Proposition 1.6.3(i))**: for a tower `A → B → C` of adic
  homomorphisms into complete Hausdorff rings, with `C` a Huber ring of noetherian type and
  `A → C` (or `A → B` and `B → C`) topologically of finite type,
  `C ⊗[B] Ωᶜ[B⁄A] → Ωᶜ[C⁄A] → Ωᶜ[C⁄B] → 0` is exact (`exact_mapBaseChange_mapTower`,
  `mapTower_surjective`).
* **Conormal exact sequence (Proposition 1.6.3(ii))**: when `A → B` is topologically of finite type
  into a complete Hausdorff Huber ring `B` of noetherian type and `B → C` is an open quotient map
  into a complete Hausdorff Huber ring `C` with kernel `J = ker(B → C)`,
  `J / J² → C ⊗[B] Ωᶜ[B⁄A] → Ωᶜ[C⁄A] → 0` is exact (`exact_kerCotangentToTensor_mapBaseChange`,
  `mapBaseChange_surjective`).
* **Completed base change (Proposition 1.6.3(iii))**: when `A → B` is topologically of finite type
  into a complete Hausdorff Huber ring `B` of noetherian type and `A → A'` is an adic homomorphism
  into a Huber ring `A'` of noetherian type (with no completeness hypothesis on `A'`), scalar
  extension induces a `B'`-linear isomorphism `B' ⊗[B] Ωᶜ[B⁄A] ≃ₗ[B'] Ωᶜ[B'⁄A']` for
  `B' = B ⊗̂_A A'` (`baseChangeEquiv`).

## Main definitions and results

* `TauCeti.Huber.ContinuousKaehlerDifferential.mapBaseChange`,
  `TauCeti.Huber.ContinuousKaehlerDifferential.mapTower`: the maps in the first fundamental
  sequence `C ⊗[B] Ωᶜ[B⁄A] →ₗ[C] Ωᶜ[C⁄A] →ₗ[C] Ωᶜ[C⁄B]`.
* `TauCeti.Huber.ContinuousKaehlerDifferential.exact_mapBaseChange_mapTower_of_comp`,
  `TauCeti.Huber.ContinuousKaehlerDifferential.exact_mapBaseChange_mapTower`,
  `TauCeti.Huber.ContinuousKaehlerDifferential.mapTower_surjective`: exactness and surjectivity of
  the first fundamental sequence.
* `TauCeti.Huber.ContinuousKaehlerDifferential.kerCotangentToTensor`,
  `TauCeti.Huber.ContinuousKaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange`,
  `TauCeti.Huber.ContinuousKaehlerDifferential.mapBaseChange_surjective`: the conormal map
  `J / J² →ₗ[B] C ⊗[B] Ωᶜ[B⁄A]` and exactness of the conormal sequence.
* `TauCeti.Huber.ContinuousKaehlerDifferential.baseChangeEquiv`: the completed base-change
  isomorphism `(B ⊗̂_A A') ⊗[B] Ωᶜ[B⁄A] ≃ₗ[B ⊗̂_A A'] Ωᶜ[(B ⊗̂_A A')⁄A']`.

## References

* R. Huber, *Étale cohomology of rigid analytic varieties and adic spaces*, Aspects of
  Mathematics E30 (1996), §1.6, Proposition 1.6.3.
-/

public section

open TensorProduct Topology

namespace TauCeti.Huber.ContinuousKaehlerDifferential

open CompletedTensor

/-! ### Maps in a tower `A → B → C` -/

section TowerMaps

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

@[simp]
theorem mapBaseChange_tmul [IsAdicHom (algebraMap A B)] [IsAdicHom (algebraMap A C)]
    (hc : Continuous (algebraMap B C)) (c : C) (ω : ContinuousKaehlerDifferential A B) :
    mapBaseChange A B C hc (c ⊗ₜ[B] ω) =
      c • mapSemilinear (RingHom.id A) (algebraMap B C)
        (by ext a; exact (IsScalarTower.algebraMap_apply A B C a).symm) hc ω :=
  map_tmul _ _ hc c ω

theorem mapBaseChange_tmul_D [IsAdicHom (algebraMap A B)] [IsAdicHom (algebraMap A C)]
    (hc : Continuous (algebraMap B C)) (c : C) (b : B) :
    mapBaseChange A B C hc (c ⊗ₜ[B] D A B b) = c • D A C (algebraMap B C b) := by
  rw [mapBaseChange_tmul, mapSemilinear_D]

omit [IsUniformAddGroup B] [CompleteSpace B] [T0Space B] in
/-- The relative projection `Ωᶜ[C⁄A] →ₗ[C] Ωᶜ[C⁄B]` in a tower `A → B → C`. -/
noncomputable def mapTower [IsAdicHom (algebraMap A C)] [IsAdicHom (algebraMap B C)] :
    ContinuousKaehlerDifferential A C →ₗ[C] ContinuousKaehlerDifferential B C :=
  mapSemilinear (algebraMap A B) (RingHom.id C)
    (by ext a; exact IsScalarTower.algebraMap_apply A B C a) continuous_id

omit [IsUniformAddGroup B] [CompleteSpace B] [T0Space B] in
@[simp]
theorem mapTower_D [IsAdicHom (algebraMap A C)] [IsAdicHom (algebraMap B C)] (c : C) :
    mapTower A B C (D A C c) = D B C c :=
  mapSemilinear_D _ _ _ continuous_id c

/-- The composite `C ⊗[B] Ωᶜ[B⁄A] → Ωᶜ[C⁄A] → Ωᶜ[C⁄B]` is zero on every class, without any
noetherian or finite-type hypotheses. -/
@[simp]
theorem mapTower_mapBaseChange [IsAdicHom (algebraMap A B)] [IsAdicHom (algebraMap B C)]
    [IsAdicHom (algebraMap A C)] (hc : Continuous (algebraMap B C))
    (z : C ⊗[B] ContinuousKaehlerDifferential A B) :
    mapTower A B C (mapBaseChange A B C hc z) = 0 := by
  induction z using TensorProduct.inductionOn with
  | tmul c ω =>
    rw [mapBaseChange_tmul, map_smul, mapTower, mapSemilinear_comp]
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

end TowerMaps

section ConormalMap

variable (A B C : Type*) [CommRing A] [CommRing B] [CommRing C]
  [Algebra A B] [Algebra B C]
  [TopologicalSpace A] [IsTopologicalRing A]
  [UniformSpace B] [IsUniformAddGroup B] [NonarchimedeanRing B] [CompleteSpace B] [T0Space B]
  [IsAdicHom (algebraMap A B)]

/-- The `B`-linear map `J →ₗ[B] C ⊗[B] Ωᶜ[B⁄A]` for `J = ker(B → C)`, sending `x ↦ 1 ⊗ₜ d x`. -/
noncomputable def kerToTensor :
    RingHom.ker (algebraMap B C) →ₗ[B] C ⊗[B] ContinuousKaehlerDifferential A B where
  toFun x := 1 ⊗ₜ[B] D A B x.1
  map_add' x y := by simp [tmul_add]
  map_smul' b x := by
    simp only [SetLike.val_smul, smul_eq_mul, Derivation.leibniz, tmul_add, tmul_smul,
      smul_tmul', ← Algebra.algebraMap_eq_smul_one, RingHom.mem_ker.mp x.2, zero_tmul, add_zero,
      RingHom.id_apply]

/-- The conormal map `J / J² →ₗ[B] C ⊗[B] Ωᶜ[B⁄A]` for `J = ker(B → C)` (Huber 1996,
Proposition 1.6.3(ii)). -/
noncomputable def kerCotangentToTensor :
    (RingHom.ker (algebraMap B C)).Cotangent →ₗ[B] C ⊗[B] ContinuousKaehlerDifferential A B :=
  Submodule.liftQ _ (kerToTensor A B C) <| by
    rw [Submodule.smul_eq_map₂]
    refine iSup_le_iff.mpr ?_
    simp only [Submodule.map_le_iff_le_comap, Subtype.forall]
    rintro x hx y -
    simp [kerToTensor, TensorProduct.smul_tmul', ← Algebra.algebraMap_eq_smul_one,
      RingHom.mem_ker.mp hx]

@[simp]
theorem kerCotangentToTensor_toCotangent (x : RingHom.ker (algebraMap B C)) :
    kerCotangentToTensor A B C ((RingHom.ker (algebraMap B C)).toCotangent x) =
      1 ⊗ₜ[B] D A B x.1 := (rfl)

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

section FirstFundamentalSequence

variable {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
  [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
  [TopologicalSpace A] [IsTopologicalRing A]
  [UniformSpace B] [IsUniformAddGroup B] [NonarchimedeanRing B] [CompleteSpace B] [T0Space B]
  [UniformSpace C] [IsUniformAddGroup C] [IsTopologicalRing C] [IsHuberRing C]
  [CompleteSpace C] [T0Space C]

omit [IsUniformAddGroup B] [CompleteSpace B] [T0Space B] in
/-- **Surjectivity in the first fundamental sequence** (Huber 1996, Proposition 1.6.3(i)): when
`B → C` is topologically of finite type and `C` is of noetherian type, `Ωᶜ[C⁄A] → Ωᶜ[C⁄B]` is
surjective. -/
theorem mapTower_surjective [IsHuberRing B] [IsNoetherianType C]
    [IsAdicHom (algebraMap A C)] [IsAdicHom (algebraMap B C)]
    (hBC : IsTopologicallyFiniteType (algebraMap B C)) :
    Function.Surjective (mapTower A B C) := by
  rw [← LinearMap.range_eq_top, eq_top_iff, ← span_range_derivation hBC, Submodule.span_le]
  rintro _ ⟨c, rfl⟩
  exact ⟨D A C c, mapTower_D A B C c⟩

/-- **First fundamental exact sequence from topological finite type of the composite**: if `A → C`
is topologically of finite type and `C` is of noetherian type, then
`C ⊗[B] Ωᶜ[B⁄A] → Ωᶜ[C⁄A] → Ωᶜ[C⁄B]` is exact. -/
theorem exact_mapBaseChange_mapTower_of_comp [IsHuberRing A] [IsNoetherianType C]
    [IsAdicHom (algebraMap A B)] [IsAdicHom (algebraMap B C)] [IsAdicHom (algebraMap A C)]
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
        rw [h0, smul_zero, add_zero]
        rfl
      map_one_eq_zero' := by simp
      leibniz' x y := by simp [Derivation.leibniz] }
  have hδB : Continuous δB :=
    (IsModuleTopology.continuous_of_linearMap R.mkQ).comp (continuous_D hAC)
  let s : ContinuousKaehlerDifferential B C →ₗ[C] Q := liftOfFinite δB hδB
  have hs : s.comp (mapTower A B C) = R.mkQ :=
    linearMap_ext hAC fun c ↦ by
      simp only [LinearMap.comp_apply, mapTower_D, s, liftOfFinite_D]; rfl
  intro ω hω
  have h0 : R.mkQ ω = 0 := by rw [← hs, LinearMap.comp_apply, LinearMap.mem_ker.mp hω, map_zero]
  exact (Submodule.Quotient.mk_eq_zero R).mp h0

/-- **Huber Proposition 1.6.3(i) (First fundamental exact sequence)**: for topologically finite
type homomorphisms `A → B` and `B → C` with `B` of noetherian type,
`C ⊗[B] Ωᶜ[B⁄A] → Ωᶜ[C⁄A] → Ωᶜ[C⁄B]` is exact. -/
theorem exact_mapBaseChange_mapTower [IsHuberRing A] [IsHuberRing B] [IsNoetherianType B]
    [IsAdicHom (algebraMap A B)] [IsAdicHom (algebraMap B C)] [IsAdicHom (algebraMap A C)]
    (hc : Continuous (algebraMap B C))
    (hAB : IsTopologicallyFiniteType (algebraMap A B))
    (hBC : IsTopologicallyFiniteType (algebraMap B C)) :
    Function.Exact (mapBaseChange A B C hc) (mapTower A B C) := by
  have : IsNoetherianType C := .of_isTopologicallyFiniteType hBC
  have hAC : IsTopologicallyFiniteType (algebraMap A C) :=
    IsScalarTower.algebraMap_eq A B C ▸ hBC.comp hAB
  exact exact_mapBaseChange_mapTower_of_comp hc hAC

end FirstFundamentalSequence

/-- Two `R`-linear maps out of `R ⊗[B] Ωᶜ[B⁄A]` into a scalar-tower `(B, R)`-module agreeing on
`1 ⊗ₜ d b` for all `b : B` are equal. -/
private theorem linearMap_tensor_ext {A B R : Type*} [CommRing A] [CommRing B] [CommRing R]
    [Algebra A B] [Algebra B R]
    [TopologicalSpace A] [IsTopologicalRing A] [IsHuberRing A]
    [UniformSpace B] [IsUniformAddGroup B] [IsTopologicalRing B] [IsHuberRing B]
    [CompleteSpace B] [T0Space B] [IsNoetherianType B] [IsAdicHom (algebraMap A B)]
    (hAB : IsTopologicallyFiniteType (algebraMap A B))
    {Q : Type*} [AddCommGroup Q] [Module B Q] [Module R Q] [IsScalarTower B R Q]
    {f g : R ⊗[B] ContinuousKaehlerDifferential A B →ₗ[R] Q}
    (h : ∀ b : B, f (1 ⊗ₜ[B] D A B b) = g (1 ⊗ₜ[B] D A B b)) : f = g := by
  have h1 : (f.restrictScalars B).comp (TensorProduct.mk B R _ 1) =
      (g.restrictScalars B).comp (TensorProduct.mk B R _ 1) :=
    linearMap_ext hAB fun b ↦ h b
  refine LinearMap.restrictScalars_injective B (TensorProduct.ext' fun r ω ↦ ?_)
  have hr : r ⊗ₜ[B] ω = r • ((1 : R) ⊗ₜ[B] ω) := by rw [smul_tmul', smul_eq_mul, mul_one]
  simp only [LinearMap.restrictScalars_apply, hr, map_smul]
  exact congrArg (r • ·) (DFunLike.congr_fun h1 ω)

/-! ### Conormal exact sequence (Huber 1996, Proposition 1.6.3(ii)) -/

section ConormalSequence

variable {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
  [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
  [TopologicalSpace A] [IsTopologicalRing A] [IsHuberRing A]
  [UniformSpace B] [IsUniformAddGroup B] [IsTopologicalRing B] [IsHuberRing B]
  [CompleteSpace B] [T0Space B]
  [UniformSpace C] [IsUniformAddGroup C] [IsTopologicalRing C] [IsHuberRing C]
  [CompleteSpace C] [T0Space C]
  [IsAdicHom (algebraMap A B)] [IsAdicHom (algebraMap A C)]

/-- **Surjectivity in the conormal sequence** (Huber 1996, Proposition 1.6.3(ii)): when `B → C` is
surjective and `A → C` is topologically of finite type into `C` of noetherian type,
`C ⊗[B] Ωᶜ[B⁄A] → Ωᶜ[C⁄A]` is surjective. -/
theorem mapBaseChange_surjective [IsNoetherianType C]
    (hc : Continuous (algebraMap B C)) (hsurj : Function.Surjective (algebraMap B C))
    (hAC : IsTopologicallyFiniteType (algebraMap A C)) :
    Function.Surjective (mapBaseChange A B C hc) := by
  rw [← LinearMap.range_eq_top, eq_top_iff, ← span_range_derivation hAC, Submodule.span_le]
  rintro _ ⟨c, rfl⟩
  obtain ⟨b, rfl⟩ := hsurj c
  exact ⟨1 ⊗ₜ[B] D A B b, by simp⟩

omit [IsHuberRing A] [IsHuberRing B] [UniformSpace C] [IsUniformAddGroup C]
  [IsTopologicalRing C] [IsHuberRing C] [CompleteSpace C] [T0Space C]
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
  let f : B → Q := fun b ↦ L.mkQ (1 ⊗ₜ[B] D A B b)
  have hf_eq {b₁ b₂ : B} (h : algebraMap B C b₁ = algebraMap B C b₂) : f b₁ = f b₂ := by
    rw [← sub_eq_zero]
    change L.mkQ (1 ⊗ₜ[B] D A B b₁) - L.mkQ (1 ⊗ₜ[B] D A B b₂) = 0
    rw [← map_sub, ← tmul_sub, ← map_sub, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact hL (b₁ - b₂) (by rw [RingHom.mem_ker, map_sub, h, sub_self])
  let g : C → Q := fun c ↦ f (hsurj c).choose
  have hg (b : B) : g (algebraMap B C b) = f b := hf_eq (hsurj (algebraMap B C b)).choose_spec
  refine ⟨{ toFun := g
            map_add' c₁ c₂ := by
              obtain ⟨b₁, rfl⟩ := hsurj c₁; obtain ⟨b₂, rfl⟩ := hsurj c₂
              rw [← map_add, hg, hg, hg]; simp [f, tmul_add]
            map_smul' a c := by
              obtain ⟨b, rfl⟩ := hsurj c
              rw [RingHom.id_apply, Algebra.smul_def, IsScalarTower.algebraMap_apply A B C a,
                ← map_mul, hg, hg]
              dsimp only [f]
              rw [← Algebra.smul_def, Derivation.map_smul,
                ← IsScalarTower.algebraMap_smul B a (D A B b), ← smul_tmul]
              have htmul : (algebraMap A C a • ((1 : C) ⊗ₜ[B] D A B b)) =
                  (algebraMap A B a • (1 : C)) ⊗ₜ[B] D A B b := by
                rw [smul_tmul', smul_eq_mul, Algebra.smul_def,
                  ← IsScalarTower.algebraMap_apply A B C a]
              rw [← htmul, L.mkQ.map_smul, algebraMap_smul]
            map_one_eq_zero' := by
              change g 1 = 0
              rw [← map_one (algebraMap B C), hg]; simp [f]
            leibniz' c₁ c₂ := by
              change g (c₁ * c₂) = c₁ • g c₂ + c₂ • g c₁
              obtain ⟨b₁, rfl⟩ := hsurj c₁; obtain ⟨b₂, rfl⟩ := hsurj c₂
              rw [← map_mul, hg, hg, hg]
              simp only [f, Derivation.leibniz, tmul_add, map_add, ← smul_tmul, ← smul_tmul']
              rw [← algebraMap_smul C b₁, ← algebraMap_smul C b₂, L.mkQ.map_smul,
                L.mkQ.map_smul] }, hg⟩

/-- **Huber Proposition 1.6.3(ii) (Conormal exact sequence)**: when `A → B` is topologically of
finite type into `B` of noetherian type and `B → C` is an open quotient map, the sequence
`J / J² → C ⊗[B] Ωᶜ[B⁄A] → Ωᶜ[C⁄A]` is exact for `J = ker(B → C)`. -/
theorem exact_kerCotangentToTensor_mapBaseChange [IsNoetherianType B]
    (hAB : IsTopologicallyFiniteType (algebraMap A B))
    (hBC : IsOpenQuotientMap (algebraMap B C)) :
    Function.Exact (kerCotangentToTensor A B C) (mapBaseChange A B C hBC.continuous) := by
  intro z
  refine ⟨fun hz ↦ ?_, fun ⟨u, hu⟩ ↦ hu ▸ mapBaseChange_kerCotangentToTensor A B C hBC.continuous u⟩
  have : IsNoetherianType C := .of_isOpenQuotientMap hBC
  have : Module.Finite B (ContinuousKaehlerDifferential A B) := finite hAB
  let L : Submodule C (C ⊗[B] ContinuousKaehlerDifferential A B) :=
    { carrier := Set.range (kerCotangentToTensor A B C)
      zero_mem' := ⟨0, map_zero _⟩
      add_mem' := by rintro _ _ ⟨u, rfl⟩ ⟨v, rfl⟩; exact ⟨u + v, map_add _ u v⟩
      smul_mem' := by
        rintro c _ ⟨u, rfl⟩
        obtain ⟨b, rfl⟩ := hBC.surjective c
        exact ⟨b • u, ((kerCotangentToTensor A B C).map_smul b u).trans
          (algebraMap_smul C b _).symm⟩ }
  let Q := (C ⊗[B] ContinuousKaehlerDifferential A B) ⧸ L
  let : TopologicalSpace Q := moduleTopology C Q
  have : IsModuleTopology C Q := ⟨rfl⟩
  let : IsTopologicalAddGroup Q := IsModuleTopology.isTopologicalAddGroup C Q
  have : ContinuousSMul B Q := ⟨by
    have h : (fun p : B × Q ↦ p.1 • p.2) = fun p ↦ algebraMap B C p.1 • p.2 := by
      ext ⟨b, q⟩; exact (algebraMap_smul C b q).symm
    rw [h]
    exact (hBC.continuous.comp continuous_fst).smul continuous_snd⟩
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

omit [IsHuberRing A] [IsUniformAddGroup B] [IsHuberRing B] [CompleteSpace B] [T0Space B]
  [IsNoetherianType B] [IsHuberRing A'] [IsNoetherianType A'] in
/-- The `A'`-subalgebra generated by `inl '' univ` is dense in `B ⊗̂_A A'`. -/
private theorem dense_adjoin_range_inl :
    Dense (Algebra.adjoin A' (Set.range (inl A B A')) : Set (CompletedTensor A B A')) := by
  refine (denseRange_toCompletion A B A').mono ?_
  rintro _ ⟨x, rfl⟩
  induction x using TensorProduct.inductionOn with
  | tmul b a' =>
    rw [toCompletion_tmul, mul_comm, ← algebraMap_rightAlgebra]
    exact Subalgebra.mul_mem _
      (Subalgebra.algebraMap_mem _ a') (Algebra.subset_adjoin ⟨b, rfl⟩)
  | add x y hx hy =>
    rw [map_add]
    exact Subalgebra.add_mem _ hx hy

omit [IsHuberRing A] [IsUniformAddGroup B] [IsHuberRing B] [CompleteSpace B] [T0Space B]
  [IsNoetherianType B] [IsHuberRing A'] [IsNoetherianType A'] in
/-- Lift a continuous `inl`-derivation `d₀ : B →+ M` vanishing on `A` into a complete Hausdorff
nonarchimedean `(B ⊗̂_A A')`-module `M` to a continuous `A'`-derivation `B ⊗̂_A A' → M`. -/
private noncomputable def liftBaseChangeDerivation
    {M : Type*} [AddCommGroup M] [UniformSpace M] [IsUniformAddGroup M]
    [NonarchimedeanAddGroup M] [CompleteSpace M] [T0Space M]
    [Module (CompletedTensor A B A') M] [ContinuousSMul (CompletedTensor A B A') M]
    [Module A' M] [IsScalarTower A' (CompletedTensor A B A') M]
    (d₀ : B →+ M) (hd₀_cont : Continuous d₀) (hd₀_one : d₀ 1 = 0)
    (hd₀_mul : ∀ b₁ b₂ : B, d₀ (b₁ * b₂) = inl A B A' b₁ • d₀ b₂ + inl A B A' b₂ • d₀ b₁)
    (hd₀_alg : ∀ a : A, d₀ (algebraMap A B a) = 0) :
    {δ : Derivation A' (CompletedTensor A B A') M //
      Continuous δ ∧ ∀ b : B, δ (inl A B A' b) = d₀ b} := by
  let B' := CompletedTensor A B A'
  letI : Module B'ᵐᵒᵖ M := Module.compHom M ((RingHom.id B').fromOpposite mul_comm)
  letI : IsCentralScalar B' M := ⟨fun _ _ ↦ rfl⟩
  letI : ContinuousSMul B'ᵐᵒᵖ M :=
    ⟨(MulOpposite.continuous_unop.comp continuous_fst).smul continuous_snd⟩
  letI : NonarchimedeanRing (TrivSqZeroExt B' M) :=
    { is_nonarchimedean := (inferInstance : NonarchimedeanAddGroup (B' × M)).is_nonarchimedean }
  let φB : B →+* TrivSqZeroExt B' M :=
    { toFun b := TrivSqZeroExt.inl (inl A B A' b) + TrivSqZeroExt.inr (d₀ b)
      map_one' := by simp [hd₀_one]
      map_mul' b₁ b₂ := by ext <;> simp [hd₀_mul, add_comm]
      map_zero' := by simp
      map_add' b₁ b₂ := by ext <;> simp [map_add, add_add_add_comm] }
  have hφB_cont : Continuous φB :=
    (TrivSqZeroExt.continuous_inl.comp (continuous_inl A B A')).add
      (TrivSqZeroExt.continuous_inr.comp hd₀_cont)
  let ψA' : A' →+* TrivSqZeroExt B' M := (TrivSqZeroExt.inlHom B' M).comp (inr A B A')
  have hcomm : φB.comp (algebraMap A B) = ψA'.comp (algebraMap A A') := by
    ext a
    · simp only [RingHom.comp_apply, φB, ψA', RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
        TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, add_zero,
        TrivSqZeroExt.inlHom_apply]
      exact RingHom.congr_fun (inl_comp_algebraMap A B A') a
    · simp [φB, ψA', hd₀_alg]
  let Ψ : B' →+* TrivSqZeroExt B' M :=
    CompletedTensor.lift φB ψA' hcomm hφB_cont
      (TrivSqZeroExt.continuous_inl.comp (continuous_inr A B A'))
  have Ψ_inl (b : B) : Ψ (inl A B A' b) = φB b := lift_inl _ _ hcomm _ _ b
  have Ψ_inr (a' : A') : Ψ (inr A B A' a') = ψA' a' := lift_inr _ _ hcomm _ _ a'
  let fstHom : TrivSqZeroExt B' M →+* B' := (TrivSqZeroExt.fstHom B' B' M).toRingHom
  have hfst : fstHom.comp Ψ = RingHom.id B' :=
    CompletedTensor.hom_ext (TrivSqZeroExt.continuous_fst.comp (continuous_lift ..)) continuous_id
      (RingHom.ext fun b ↦ by simp [fstHom, Ψ_inl, φB])
      (RingHom.ext fun a' ↦ by simp [fstHom, Ψ_inr, ψA'])
  have hfst_apply (z : B') : (Ψ z).fst = z := RingHom.congr_fun hfst z
  have hsnd_mul (x y : B') : (Ψ (x * y)).snd = x • (Ψ y).snd + y • (Ψ x).snd := by
    rw [map_mul, TrivSqZeroExt.snd_mul, hfst_apply, hfst_apply]; rfl
  refine ⟨{ toFun z := (Ψ z).snd
            map_add' x y := by simp [map_add]
            map_smul' a' z := by
              rw [RingHom.id_apply, Algebra.smul_def, ← algebraMap_smul B' a' (Ψ z).snd,
                algebraMap_rightAlgebra, hsnd_mul, Ψ_inr]; simp [ψA']
            map_one_eq_zero' := by simp [map_one]
            leibniz' x y := hsnd_mul x y },
    TrivSqZeroExt.continuous_snd.comp (continuous_lift ..),
    fun b ↦ by simp [Ψ_inl, φB]⟩

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
  have : IsUniformAddGroup M := isUniformAddGroup_of_addCommGroup
  obtain ⟨_, _⟩ := isNaturallyComplete_iff.mp
    (IsNoetherianType.isNaturallyComplete (A := B') (M := M))
  have : NonarchimedeanAddGroup M := by
    rw [eq_moduleTopology B' M]
    exact TauCeti.nonarchimedeanAddGroup_moduleTopology (A := B')
  have : ContinuousSMul B M := ⟨by
    have h : (fun p : B × M ↦ p.1 • p.2) = fun p ↦ inl A B A' p.1 • p.2 := by
      ext ⟨b, m⟩; rw [← algebraMap_leftAlgebra, algebraMap_smul]
    rw [h]
    exact ((continuous_inl A B A').comp continuous_fst).smul continuous_snd⟩
  exact liftBaseChangeDerivation
    (AddMonoidHom.mk' (fun b ↦ (1 : B') ⊗ₜ[B] D A B b) (fun x y ↦ by simp [tmul_add]))
    ((IsModuleTopology.continuous_of_linearMap
      (TensorProduct.mk B B' (ContinuousKaehlerDifferential A B) 1)).comp (continuous_D hAB))
    (by simp)
    (fun b₁ b₂ ↦ by
      simp only [AddMonoidHom.mk'_apply, Derivation.leibniz, tmul_add, ← smul_tmul, ← smul_tmul']
      rw [← algebraMap_smul B' b₁, ← algebraMap_smul B' b₂]
      dsimp [B']; rw [algebraMap_leftAlgebra])
    (fun a ↦ by simp)

/-- **Huber Proposition 1.6.3(iii) (Base change of continuous differentials)**: when `A → B` is
topologically of finite type into a complete Hausdorff Huber ring `B` of noetherian type and
`A → A'` is an adic homomorphism into a Huber ring `A'` of noetherian type, scalar extension
induces a linear equivalence
`(B ⊗̂_A A') ⊗[B] Ωᶜ[B⁄A] ≃ₗ[B ⊗̂_A A'] Ωᶜ[(B ⊗̂_A A')⁄A']`. -/
noncomputable def baseChangeEquiv (hAB : IsTopologicallyFiniteType (algebraMap A B)) :
    CompletedTensor A B A' ⊗[B] ContinuousKaehlerDifferential A B ≃ₗ[CompletedTensor A B A']
      ContinuousKaehlerDifferential A' (CompletedTensor A B A') := by
  let B' := CompletedTensor A B A'
  let M := B' ⊗[B] ContinuousKaehlerDifferential A B
  have hA'B' : IsTopologicallyFiniteType (algebraMap A' B') := by
    rw [algebraMap_rightAlgebra]; exact isTopologicallyFiniteType_inr hAB
  have : IsNoetherianType B' := .of_isTopologicallyFiniteType hA'B'
  have : Module.Finite B (ContinuousKaehlerDifferential A B) := finite hAB
  letI : TopologicalSpace M := moduleTopology B' M
  have : IsModuleTopology B' M := ⟨rfl⟩
  let fwd : M →ₗ[B'] ContinuousKaehlerDifferential A' B' :=
    map (algebraMap A A') (by ext a; simp [B'])
      (by dsimp [B']; rw [algebraMap_leftAlgebra]; exact continuous_inl A B A')
  obtain ⟨δ', hδ', hδ'_inl⟩ := baseChangeDerivation (A' := A') hAB
  let inv : ContinuousKaehlerDifferential A' B' →ₗ[B'] M := liftOfFinite δ' hδ'
  have hleft : inv.comp fwd = LinearMap.id :=
    linearMap_tensor_ext hAB fun b ↦ by
      simp only [LinearMap.comp_apply, LinearMap.id_apply, fwd, inv, B', M]
      rw [map_tmul, mapSemilinear_D, one_smul, algebraMap_leftAlgebra, liftOfFinite_D, hδ'_inl]
  have hright : fwd.comp inv = LinearMap.id := by
    refine linearMap_ext_of_dense_adjoin hA'B' dense_adjoin_range_inl ?_
    rintro _ ⟨b, rfl⟩
    simp only [LinearMap.comp_apply, LinearMap.id_apply, fwd, inv, B', M]
    rw [liftOfFinite_D, hδ'_inl, map_tmul, mapSemilinear_D, one_smul, algebraMap_leftAlgebra]
  exact LinearEquiv.ofLinearMap fwd inv hright hleft

@[simp]
theorem baseChangeEquiv_tmul (hAB : IsTopologicallyFiniteType (algebraMap A B))
    (b' : CompletedTensor A B A') (ω : ContinuousKaehlerDifferential A B) :
    baseChangeEquiv hAB (b' ⊗ₜ[B] ω) =
      b' • mapSemilinear (algebraMap A A') (algebraMap B (CompletedTensor A B A'))
        (by ext a; simp)
        (by rw [algebraMap_leftAlgebra]; exact continuous_inl A B A') ω := by
  dsimp [baseChangeEquiv]
  exact map_tmul _ _ _ b' ω

theorem baseChangeEquiv_tmul_D (hAB : IsTopologicallyFiniteType (algebraMap A B))
    (b' : CompletedTensor A B A') (b : B) :
    baseChangeEquiv hAB (b' ⊗ₜ[B] D A B b) =
      b' • D A' (CompletedTensor A B A') (inl A B A' b) := by
  rw [baseChangeEquiv_tmul, mapSemilinear_D, algebraMap_leftAlgebra]

@[simp]
theorem baseChangeEquiv_symm_D_inl (hAB : IsTopologicallyFiniteType (algebraMap A B)) (b : B) :
    (baseChangeEquiv (A' := A') hAB).symm (D A' (CompletedTensor A B A') (inl A B A' b)) =
      (1 : CompletedTensor A B A') ⊗ₜ[B] D A B b := by
  refine (baseChangeEquiv (A' := A') hAB).injective ?_
  rw [LinearEquiv.apply_symm_apply, baseChangeEquiv_tmul_D, one_smul]

@[simp]
theorem baseChangeEquiv_symm_D_inr (hAB : IsTopologicallyFiniteType (algebraMap A B)) (a' : A') :
    (baseChangeEquiv (A' := A') hAB).symm (D A' (CompletedTensor A B A') (inr A B A' a')) = 0 := by
  rw [← algebraMap_rightAlgebra, Derivation.map_algebraMap, map_zero]

end BaseChange

end TauCeti.Huber.ContinuousKaehlerDifferential
