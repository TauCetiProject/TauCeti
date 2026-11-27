/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.Kaehler.Basic
public import TauCeti.RingTheory.Huber.TensorProduct.Map.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Lift

import TauCeti.RingTheory.Huber.TensorProduct.Quotient.Basic

/-!
# Change of rings for continuous differentials

A commuting square of adic coefficient maps, whose map on the upper rings is continuous,
induces a semilinear map on the completed-diagonal modules of differentials. Extending scalars
gives the linear map `B' ⊗[B] Ωᶜ[B⁄A] → Ωᶜ[B'⁄A']`. These maps preserve identities and
composition on every differential, including classes not known to lie in the span of `d(B)`.
No noetherian or finite-type hypothesis is needed for this construction.

The construction uses Mathlib's `Ideal.mapCotangent` on the map of completed diagonals;
the scalar extension uses `LinearMap.liftBaseChange`. The caller's algebra structures remain
parameters in the scalar-extended map. Continuity of the map on the coefficient rings is not
needed: that map only supplies the commuting square.

This file also provides the tower specialization `mapTower : Ωᶜ[C⁄A] →ₗ[C] Ωᶜ[C⁄B]` and
base-change specialization `mapBaseChange : C ⊗[B] Ωᶜ[B⁄A] →ₗ[C] Ωᶜ[C⁄A]` together with their
functoriality (`mapTower_mapTower`, `mapTower_mapBaseChange`) and surjectivity of `mapTower`
(`mapTower_surjective`).

## References

* R. Huber, *Étale cohomology of rigid analytic varieties and adic spaces*, Aspects of
  Mathematics E30 (1996), §1.6, Definition 1.6.1, (1.6.2), and Proposition 1.6.3(i)–(ii).
-/

public section

open TensorProduct

namespace TauCeti.Huber.ContinuousKaehlerDifferential

variable {A B A' B' A'' B'' : Type*}
  [CommRing A] [CommRing B] [CommRing A'] [CommRing B'] [CommRing A''] [CommRing B'']
  [Algebra A B] [Algebra A' B'] [Algebra A'' B'']
  [TopologicalSpace A] [IsTopologicalRing A]
  [TopologicalSpace A'] [IsTopologicalRing A']
  [TopologicalSpace A''] [IsTopologicalRing A'']
  [UniformSpace B] [IsUniformAddGroup B] [NonarchimedeanRing B] [CompleteSpace B] [T0Space B]
  [UniformSpace B'] [IsUniformAddGroup B'] [NonarchimedeanRing B'] [CompleteSpace B'] [T0Space B']
  [UniformSpace B''] [IsUniformAddGroup B''] [NonarchimedeanRing B'']
  [CompleteSpace B''] [T0Space B'']
  [IsAdicHom (algebraMap A B)] [IsAdicHom (algebraMap A' B')]
  [IsAdicHom (algebraMap A'' B'')]

open CompletedTensor

variable (α : A →+* A') (φ : B →+* B')
  (hφ : φ.comp (algebraMap A B) = (algebraMap A' B').comp α) (hφc : Continuous φ)

/-- The map on completed diagonals sends the diagonal ideal into the target diagonal ideal. -/
theorem ideal_le_comap_map :
    ideal A B ≤ (ideal A' B').comap (CompletedTensor.map α φ φ hφ hφ hφc hφc) := by
  intro x hx
  exact (mem_ideal_iff).mpr (by rw [mulRingHom_map, mem_ideal_iff.mp hx, map_zero])

private noncomputable def mapCotangent :
    ContinuousKaehlerDifferential A B →ₗ[ℤ] ContinuousKaehlerDifferential A' B' :=
  ((cotangentEquiv A' B').symm.toLinearMap.restrictScalars ℤ).comp
    ((Ideal.mapCotangent (ideal A B) (ideal A' B')
      (CompletedTensor.map α φ φ hφ hφ hφc hφc).toIntAlgHom
      (ideal_le_comap_map α φ hφ hφc)).comp
      ((cotangentEquiv A B).toLinearMap.restrictScalars ℤ))

private theorem mapCotangent_fromIdeal (x : ideal A B) :
    mapCotangent α φ hφ hφc (fromIdeal A B x) =
      fromIdeal A' B' ⟨CompletedTensor.map α φ φ hφ hφ hφc hφc x,
        ideal_le_comap_map α φ hφ hφc x.property⟩ := by
  simp only [mapCotangent, LinearMap.comp_apply, LinearMap.restrictScalars_apply,
    LinearEquiv.coe_coe, cotangentEquiv_fromIdeal]
  exact (congrArg (cotangentEquiv A' B').symm
    (Ideal.mapCotangent_toCotangent (ideal A B) (ideal A' B')
      (CompletedTensor.map α φ φ hφ hφ hφc hφc).toIntAlgHom
      (ideal_le_comap_map α φ hφ hφc) x)).trans (cotangentEquiv_symm_toCotangent _ _ _)

/-- The semilinear map on continuous differentials induced by a commuting square. -/
noncomputable def mapSemilinear :
    ContinuousKaehlerDifferential A B →ₛₗ[φ] ContinuousKaehlerDifferential A' B' where
  toFun := mapCotangent α φ hφ hφc
  map_add' := (mapCotangent α φ hφ hφc).map_add
  map_smul' b ω := by
    obtain ⟨x, rfl⟩ := fromIdeal_surjective A B ω
    rw [← inl_smul, ← map_smul, mapCotangent_fromIdeal, mapCotangent_fromIdeal,
      ← inl_smul, ← map_smul]
    congr 1
    ext
    simp [smul_eq_mul]

/-- The induced map sends a diagonal class to the class of its image. -/
@[simp] theorem mapSemilinear_fromIdeal (x : ideal A B) :
    mapSemilinear α φ hφ hφc (fromIdeal A B x) =
      fromIdeal A' B' ⟨CompletedTensor.map α φ φ hφ hφ hφc hφc x,
        ideal_le_comap_map α φ hφ hφc x.property⟩ :=
  mapCotangent_fromIdeal α φ hφ hφc x

/-- Change of rings carries `d b` to `d (φ b)`. -/
@[simp] theorem mapSemilinear_D (b : B) :
    mapSemilinear α φ hφ hφc (D A B b) = D A' B' (φ b) := by
  simp only [D_apply, mapSemilinear_fromIdeal]
  congr 1
  ext
  simp

/-- The identity square induces the identity on every differential. -/
@[simp] theorem mapSemilinear_id (ω : ContinuousKaehlerDifferential A B) :
    mapSemilinear (RingHom.id A) (RingHom.id B) rfl continuous_id ω = ω := by
  obtain ⟨x, rfl⟩ := fromIdeal_surjective A B ω
  simp

/-- Composing squares composes their semilinear maps on every differential. -/
theorem mapSemilinear_comp (α' : A' →+* A'') (φ' : B' →+* B'')
    (hφ' : φ'.comp (algebraMap A' B') = (algebraMap A'' B'').comp α')
    (hφc' : Continuous φ') (ω : ContinuousKaehlerDifferential A B) :
    mapSemilinear α' φ' hφ' hφc' (mapSemilinear α φ hφ hφc ω) =
      mapSemilinear (α'.comp α) (φ'.comp φ)
        (by rw [RingHom.comp_assoc, hφ, ← RingHom.comp_assoc, hφ', RingHom.comp_assoc])
        (hφc'.comp hφc) ω := by
  obtain ⟨x, rfl⟩ := fromIdeal_surjective A B ω
  simp only [mapSemilinear_fromIdeal]
  congr 1
  ext
  exact (congrArg (fun f : CompletedTensor A B B →+* CompletedTensor A'' B'' B'' ↦ f x)
    (CompletedTensor.map_comp α φ φ hφ hφ hφc hφc α' φ' φ' hφ' hφ' hφc' hφc')).symm

section ScalarExtension

variable [Algebra B B']

/-- The scalar-extended change-of-rings map. The tensor product uses the caller's `B`-algebra
structure on `B'`; only the intermediate restricted action on the target differential module
is installed locally. -/
noncomputable def map
    (h : (algebraMap B B').comp (algebraMap A B) = (algebraMap A' B').comp α)
    (hc : Continuous (algebraMap B B')) :
    B' ⊗[B] ContinuousKaehlerDifferential A B →ₗ[B'] ContinuousKaehlerDifferential A' B' := by
  letI : Module B (ContinuousKaehlerDifferential A' B') :=
    Module.compHom _ (algebraMap B B')
  letI : IsScalarTower B B' (ContinuousKaehlerDifferential A' B') :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  exact LinearMap.liftBaseChange B'
    { toFun := mapSemilinear α (algebraMap B B') h hc
      map_add' := (mapSemilinear α (algebraMap B B') h hc).map_add
      map_smul' := fun b ω ↦ (mapSemilinear α (algebraMap B B') h hc).map_smulₛₗ b ω }

/-- On pure tensors, change of rings is scalar multiplication after the semilinear map. -/
@[simp] theorem map_tmul
    (h : (algebraMap B B').comp (algebraMap A B) = (algebraMap A' B').comp α)
    (hc : Continuous (algebraMap B B')) (b : B') (ω : ContinuousKaehlerDifferential A B) :
    map α h hc (b ⊗ₜ[B] ω) = b • mapSemilinear α (algebraMap B B') h hc ω := by
  simp [map]

end ScalarExtension

/-- The identity change-of-rings map is the canonical scalar cancellation. -/
theorem map_id :
    map (B := B) (B' := B) (RingHom.id A) rfl continuous_id =
      (TensorProduct.lid B (ContinuousKaehlerDifferential A B)).toLinearMap := by
  ext
  simp

section Composition

variable [Algebra B B'] [Algebra B' B''] [Algebra B B''] [IsScalarTower B B' B'']
  (h : (algebraMap B B').comp (algebraMap A B) = (algebraMap A' B').comp α)
  (hc : Continuous (algebraMap B B'))
  (α' : A' →+* A'')
  (h' : (algebraMap B' B'').comp (algebraMap A' B') = (algebraMap A'' B'').comp α')
  (hc' : Continuous (algebraMap B' B''))

/-- Scalar-extended change of rings respects composition, on arbitrary differential classes. -/
theorem map_comp (b'' : B'') (b' : B') (ω : ContinuousKaehlerDifferential A B) :
    map α' h' hc' (b'' ⊗ₜ[B'] map α h hc (b' ⊗ₜ[B] ω)) =
      map (α'.comp α)
        (by rw [IsScalarTower.algebraMap_eq B B' B'', RingHom.comp_assoc, h,
          ← RingHom.comp_assoc, h', RingHom.comp_assoc])
        (by rw [IsScalarTower.algebraMap_eq B B' B'']; exact hc'.comp hc)
        ((b'' * algebraMap B' B'' b') ⊗ₜ[B] ω) := by
  simp only [map_tmul, map_smulₛₗ]
  rw [mapSemilinear_comp]
  simp only [mul_smul]
  -- The ring homomorphism indexes the semilinear map's type, so transport its application.
  have H (f g : B →+* B'') (hf : f.comp (algebraMap A B) =
      (algebraMap A'' B'').comp (α'.comp α))
      (hg : g.comp (algebraMap A B) = (algebraMap A'' B'').comp (α'.comp α))
      (hfc : Continuous f) (hgc : Continuous g) (e : f = g) :
      mapSemilinear (α'.comp α) f hf hfc ω = mapSemilinear (α'.comp α) g hg hgc ω := by
    subst g
    rfl
  exact congrArg (fun z ↦ b'' • algebraMap B' B'' b' • z)
    (H _ _ _ _ _ _ (IsScalarTower.algebraMap_eq B B' B'').symm)

end Composition

/-! ### Maps in a tower `A → B → C` -/

section MapTower

variable (A B C : Type*) [CommRing A] [CommRing B] [CommRing C]
  [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
  [TopologicalSpace A] [IsTopologicalRing A] [TopologicalSpace B] [IsTopologicalRing B]
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
@[simp] theorem mapTower_fromIdeal (x : ideal A C) :
    mapTower A B C (fromIdeal A C x) =
      fromIdeal B C
        ⟨CompletedTensor.map (algebraMap A B) (RingHom.id C) (RingHom.id C)
            (by ext a; exact IsScalarTower.algebraMap_apply A B C a)
            (by ext a; exact IsScalarTower.algebraMap_apply A B C a)
            continuous_id continuous_id x,
          ideal_le_comap_map (algebraMap A B) (RingHom.id C) _ continuous_id x.property⟩ :=
  mapSemilinear_fromIdeal _ _ _ continuous_id x

/-- `mapTower` carries `d_A c` to `d_B c`. -/
@[simp] theorem mapTower_D (c : C) : mapTower A B C (D A C c) = D B C c :=
  mapSemilinear_D _ _ _ continuous_id c

/-- **Surjectivity in the first fundamental sequence** (Huber 1996, Proposition 1.6.3(i)): in a
tower `A → B → C` with `A → C` and `B → C` adic into complete Hausdorff nonarchimedean `C`,
`Ωᶜ[C⁄A] → Ωᶜ[C⁄B]` is surjective, with no finite-type, noetherian, or Huber hypotheses. -/
theorem mapTower_surjective : Function.Surjective (mapTower A B C) := by
  have h : (RingHom.id C).comp (algebraMap A C) = (algebraMap B C).comp (algebraMap A B) := by
    ext a; exact IsScalarTower.algebraMap_apply A B C a
  let F := CompletedTensor.map (algebraMap A B) (RingHom.id C) (RingHom.id C)
    h h continuous_id continuous_id
  have hF := (CompletedTensor.isOpenQuotientMap_map_base (algebraMap A B) h h).surjective
  intro ω
  obtain ⟨⟨y, hy⟩, rfl⟩ := fromIdeal_surjective B C ω
  obtain ⟨x, hxF⟩ := hF y
  have hx : x ∈ ideal A C := (mem_ideal_iff).mpr <| by
    simpa [F, hxF, mem_ideal_iff.mp hy] using
      (CompletedTensor.mulRingHom_map (algebraMap A B) (RingHom.id C) h continuous_id x).symm
  exact ⟨fromIdeal A C ⟨x, hx⟩, by simp [hxF]⟩

end MapTower

section MapTowerComp

variable (A B C E : Type*) [CommRing A] [CommRing B] [CommRing C] [CommRing E]
  [Algebra A B] [Algebra B C] [Algebra C E] [Algebra A C] [Algebra B E] [Algebra A E]
  [IsScalarTower B C E] [IsScalarTower A B E] [IsScalarTower A C E]
  [TopologicalSpace A] [IsTopologicalRing A] [TopologicalSpace B] [IsTopologicalRing B]
  [TopologicalSpace C] [IsTopologicalRing C]
  [UniformSpace E] [IsUniformAddGroup E] [NonarchimedeanRing E] [CompleteSpace E] [T0Space E]
  [IsAdicHom (algebraMap A E)] [IsAdicHom (algebraMap B E)] [IsAdicHom (algebraMap C E)]

/-- Applying two consecutive relative projections in a tower `A → B → C → E` equals the single
projection `Ωᶜ[E⁄A] → Ωᶜ[E⁄C]`. -/
@[simp] theorem mapTower_mapTower (ω : ContinuousKaehlerDifferential A E) :
    mapTower B C E (mapTower A B E ω) = mapTower A C E ω := by
  rw [mapTower_eq_mapSemilinear, mapTower_eq_mapSemilinear, mapTower_eq_mapSemilinear,
    mapSemilinear_comp]
  obtain ⟨x, rfl⟩ := fromIdeal_surjective A E ω
  simp only [mapSemilinear_fromIdeal]; congr 1; ext
  exact congrArg (fun f : CompletedTensor A E E →+* CompletedTensor C E E ↦ f x) <|
    CompletedTensor.hom_ext (CompletedTensor.continuous_map ..)
      (CompletedTensor.continuous_map ..) (by ext e; simp) (by ext e; simp)

/-- Composing relative projections in a tower `A → B → C → E` equals `mapTower A C E`. -/
@[simp] theorem mapTower_comp_mapTower : (mapTower B C E).comp (mapTower A B E) = mapTower A C E :=
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
@[simp] theorem mapBaseChange_tmul [IsAdicHom (algebraMap A B)] [IsAdicHom (algebraMap A C)]
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
@[simp] theorem mapTower_mapBaseChange [IsAdicHom (algebraMap A B)] [IsAdicHom (algebraMap B C)]
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
    have hzero : (⟨_, ideal_le_comap_map ((algebraMap A B).comp (RingHom.id A))
        ((RingHom.id C).comp (algebraMap B C)) _ (continuous_id.comp hc) hx⟩ : ideal B C) = 0 :=
      Subtype.ext <| (RingHom.congr_fun hmap x).trans (by simp [mem_ideal_iff.mp hx])
    rw [hzero, map_zero, smul_zero]
  | add x y hx hy => rw [map_add, map_add, hx, hy, add_zero]

end MapBaseChange

end TauCeti.Huber.ContinuousKaehlerDifferential
