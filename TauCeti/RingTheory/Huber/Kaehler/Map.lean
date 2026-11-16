/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.Kaehler.Basic
public import TauCeti.RingTheory.Huber.TensorProduct.Map
public import Mathlib.LinearAlgebra.TensorProduct.Lift

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

## References

* R. Huber, *Étale cohomology of rigid analytic varieties and adic spaces*, Aspects of
  Mathematics E30 (1996), §1.6, Definition 1.6.1 and (1.6.2).
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
        ideal_le_comap_map α φ hφ hφc x.2⟩ := by
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
        ideal_le_comap_map α φ hφ hφc x.2⟩ :=
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

end TauCeti.Huber.ContinuousKaehlerDifferential
