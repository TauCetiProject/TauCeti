/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.StrictHenselization.Local

/-!
# Functoriality of pointed étale colimits

A commuting square from `R → Ω` to `S → Ψ` induces a map of their pointed étale
colimits. The construction sends an étale `R`-algebra `B` to `S ⊗[R] B`, with the point
obtained by extending its original point. The induced map is local when the map
between the pointing algebras is local. It is characterized by compatibility with the base
maps and the points. Consequently these maps preserve identities and composition.

For local base rings and chosen separable closures of their residue fields, this gives
the functoriality of strict henselizations.

## References

* Stacks Project, Tag 04GU.
* Tau Ceti, `TauCeti.RingTheory.Henselization.Map`, for the functoriality interface.
-/

public section

open CategoryTheory TensorProduct

universe u

namespace TauCeti.StrictHenselization

section Construction

variable {R S Ω Ψ : Type u} [CommRing R] [CommRing S] [CommRing Ω] [CommRing Ψ]
  [Algebra R Ω] [Algebra S Ψ] [Algebra R S] [Algebra R Ψ] [IsScalarTower R S Ψ]

variable [Algebra R (algebra S Ψ)] [IsScalarTower R S (algebra S Ψ)]

private noncomputable abbrev baseChange (φ : Ω →ₐ[R] Ψ) (B : Neighbourhood R Ω) :
    Neighbourhood S Ψ :=
  let point : B.obj.left →ₐ[R] Ψ :=
    φ.comp (ULift.algEquiv.toAlgHom.comp B.obj.hom.hom)
  let extended : S ⊗[R] B.obj.left →ₐ[S] Ψ := AlgHom.liftEquiv R S _ _ point
  ⟨Over.mk (CommAlgCat.ofHom (ULift.algEquiv.symm.toAlgHom.comp extended)),
    (isPointedNeighbourhood_iff S Ψ _).mpr
      (inferInstanceAs (Algebra.Etale S (S ⊗[R] B.obj.left)))⟩

private noncomputable def baseChangeHom (φ : Ω →ₐ[R] Ψ)
    {B C : Neighbourhood R Ω} (f : B ⟶ C) :
    baseChange (S := S) φ B ⟶ baseChange (S := S) φ C :=
  ObjectProperty.homMk (Over.homMk
    (CommAlgCat.ofHom (Algebra.TensorProduct.map (AlgHom.id S S) f.hom.left.hom)) (by
      apply CommAlgCat.hom_ext
      apply Algebra.TensorProduct.ext_ring
      ext b
      have h := congrArg CommAlgCat.Hom.hom f.hom.w
      simp only [CommAlgCat.hom_comp] at h
      -- On the right tensor generators, `AlgHom.liftEquiv` evaluates the extended point
      -- as the original point, so the remaining equation is the point compatibility of `f`.
      simpa [baseChange, CommAlgCat.hom_comp] using
        congrArg φ (congrArg ULift.down (DFunLike.congr_fun h b))))

private noncomputable def stageMap (φ : Ω →ₐ[R] Ψ) (B : Neighbourhood R Ω) :
    B.obj.left →ₐ[R] algebra S Ψ :=
  -- The literal tensor carrier lets scalar restriction find its existing `R`-action.
  let leg : S ⊗[R] B.obj.left →ₐ[S] algebra S Ψ :=
    stage S Ψ (baseChange (S := S) φ B)
  (leg.restrictScalars R).comp Algebra.TensorProduct.includeRight

private theorem stageMap_comp (φ : Ω →ₐ[R] Ψ)
    {B C : Neighbourhood R Ω} (f : B ⟶ C) :
    (stageMap (S := S) φ C).comp f.hom.left.hom = stageMap (S := S) φ B := by
  ext b
  simpa [stageMap, baseChangeHom, Algebra.TensorProduct.includeRight_apply] using
    stage_hom_apply S Ψ (baseChangeHom (S := S) φ f) (1 ⊗ₜ[R] b)

private theorem toTarget_stageMap (φ : Ω →ₐ[R] Ψ) (B : Neighbourhood R Ω)
    (b : B.obj.left) :
    toTarget S Ψ (stageMap φ B b) = φ (toTarget R Ω (stage R Ω B b)) := by
  dsimp only [stageMap, AlgHom.comp_apply, AlgHom.restrictScalars_apply]
  rw [toTarget_stage_apply]
  simp [baseChange, Algebra.TensorProduct.includeRight_apply]

private noncomputable def mapAlgHom (φ : Ω →ₐ[R] Ψ) :
    algebra R Ω →ₐ[R] algebra S Ψ :=
  descOfCompatible R Ω (stageMap (S := S) φ) (stageMap_comp (S := S) φ)

private theorem toTarget_mapAlgHom (φ : Ω →ₐ[R] Ψ) (x : algebra R Ω) :
    toTarget S Ψ (mapAlgHom φ x) = φ (toTarget R Ω x) := by
  obtain ⟨B, b, rfl⟩ := exists_stage_eq R Ω x
  rw [mapAlgHom, descOfCompatible_stage_apply]
  exact toTarget_stageMap (S := S) φ B b

end Construction

section General

variable {R S Ω Ψ : Type u} [CommRing R] [CommRing S] [CommRing Ω] [CommRing Ψ]
  [Algebra R Ω] [Algebra S Ψ]

-- Keep the chosen scalar structures local, and return both equations with the map so their
-- proofs share the same construction.
private noncomputable def mapData (f : R →+* S) (φ : Ω →+* Ψ)
    (hφ : φ.comp (algebraMap R Ω) = (algebraMap S Ψ).comp f) :
    {g : algebra R Ω →+* algebra S Ψ //
      (∀ r, g (algebraMap R (algebra R Ω) r) = algebraMap S (algebra S Ψ) (f r)) ∧
      ∀ x, toTarget S Ψ (g x) = φ (toTarget R Ω x)} :=
  letI : Algebra R S := f.toAlgebra
  letI : Algebra R Ψ := ((algebraMap S Ψ).comp f).toAlgebra
  letI : IsScalarTower R S Ψ := IsScalarTower.of_algebraMap_eq' rfl
  letI : Algebra R (algebra S Ψ) := ((algebraMap S (algebra S Ψ)).comp f).toAlgebra
  letI : IsScalarTower R S (algebra S Ψ) := IsScalarTower.of_algebraMap_eq' rfl
  let φ' : Ω →ₐ[R] Ψ := { φ with commutes' := fun r => DFunLike.congr_fun hφ r }
  ⟨(mapAlgHom (S := S) φ').toRingHom,
    AlgHom.commutes (mapAlgHom (S := S) φ'), toTarget_mapAlgHom (S := S) φ'⟩

/-- A commuting square of base rings and pointing algebras induces a ring map of pointed
étale colimits. For separable closures of residue fields, this is the induced map of strict
henselizations. -/
noncomputable def map (f : R →+* S) (φ : Ω →+* Ψ)
    (hφ : φ.comp (algebraMap R Ω) = (algebraMap S Ψ).comp f) :
    algebra R Ω →+* algebra S Ψ :=
  (mapData f φ hφ).val

/-- The induced map commutes with the structure maps of the base rings. -/
@[simp]
theorem map_algebraMap (f : R →+* S) (φ : Ω →+* Ψ)
    (hφ : φ.comp (algebraMap R Ω) = (algebraMap S Ψ).comp f) (r : R) :
    map f φ hφ (algebraMap R (algebra R Ω) r) = algebraMap S (algebra S Ψ) (f r) :=
  (mapData f φ hφ).property.1 r

/-- Compatibility with base structure maps, as an equality of ring homomorphisms. -/
@[simp]
theorem map_comp_algebraMap (f : R →+* S) (φ : Ω →+* Ψ)
    (hφ : φ.comp (algebraMap R Ω) = (algebraMap S Ψ).comp f) :
    (map f φ hφ).comp (algebraMap R (algebra R Ω)) =
      (algebraMap S (algebra S Ψ)).comp f :=
  RingHom.ext (map_algebraMap f φ hφ)

/-- The point of the image is the image of the original point. -/
@[simp]
theorem toTarget_map (f : R →+* S) (φ : Ω →+* Ψ)
    (hφ : φ.comp (algebraMap R Ω) = (algebraMap S Ψ).comp f) (x : algebra R Ω) :
    toTarget S Ψ (map f φ hφ x) = φ (toTarget R Ω x) :=
  (mapData f φ hφ).property.2 x

/-- Compatibility with the points, as an equality of ring homomorphisms. -/
@[simp]
theorem toTarget_comp_map (f : R →+* S) (φ : Ω →+* Ψ)
    (hφ : φ.comp (algebraMap R Ω) = (algebraMap S Ψ).comp f) :
    (toTarget S Ψ : algebra S Ψ →+* Ψ).comp (map f φ hφ) =
      φ.comp (toTarget R Ω : algebra R Ω →+* Ω) :=
  RingHom.ext (toTarget_map f φ hφ)

/-- The induced map is local when the map between the pointing algebras is local. In particular,
this applies to every homomorphism between field-valued points. -/
instance isLocalHom_map (f : R →+* S) (φ : Ω →+* Ψ) [IsLocalHom φ]
    (hφ : φ.comp (algebraMap R Ω) = (algebraMap S Ψ).comp f) :
    IsLocalHom (map f φ hφ) := by
  have : IsLocalHom (toTarget R Ω).toRingHom := isLocalHom_toRingHom (toTarget R Ω)
  have : IsLocalHom ((toTarget S Ψ).toRingHom.comp (map f φ hφ)) :=
    toTarget_comp_map f φ hφ ▸ inferInstance
  exact isLocalHom_of_comp (map f φ hφ) (toTarget S Ψ).toRingHom

end General

section Uniqueness

variable {R S Ω Ψ : Type u} [CommRing R] [CommRing S] [CommRing Ω] [CommRing Ψ]
  [Algebra R Ω] [Algebra S Ψ]

/-- A map of pointed étale colimits is determined by its base map and its point. -/
theorem map_unique (f : R →+* S) (φ : Ω →+* Ψ)
    (hφ : φ.comp (algebraMap R Ω) = (algebraMap S Ψ).comp f)
    (g : algebra R Ω →+* algebra S Ψ)
    (hg : g.comp (algebraMap R (algebra R Ω)) = (algebraMap S (algebra S Ψ)).comp f)
    (hpoint : (toTarget S Ψ).toRingHom.comp g = φ.comp (toTarget R Ω).toRingHom) :
    g = map f φ hφ := by
  let : Algebra R (algebra S Ψ) := ((algebraMap S (algebra S Ψ)).comp f).toAlgebra
  let g' : algebra R Ω →ₐ[R] algebra S Ψ :=
    { g with commutes' := fun r => DFunLike.congr_fun hg r }
  let m : algebra R Ω →ₐ[R] algebra S Ψ :=
    { map f φ hφ with commutes' := map_algebraMap f φ hφ }
  suffices g' = m from congrArg AlgHom.toRingHom this
  let J := RingHom.ker (toTarget S Ψ).toRingHom
  have hJ : J ≤ Ideal.jacobson ⊥ := by
    intro x hx
    have hx0 : toTarget S Ψ x = 0 := RingHom.mem_ker.mp hx
    apply Ideal.mem_jacobson_bot.mpr
    intro y
    apply (isUnit_iff_isUnit_toTarget S Ψ _).mpr
    simp [hx0]
  apply hom_ext R Ω
  intro B
  apply TauCeti.Algebra.FormallyUnramified.ext_of_quotient_eq R B.obj.left J hJ
  ext b
  apply Ideal.Quotient.eq.mpr
  apply RingHom.mem_ker.mpr
  rw [map_sub]
  exact sub_eq_zero.mpr ((DFunLike.congr_fun hpoint (stage R Ω B b)).trans
    (toTarget_map f φ hφ (stage R Ω B b)).symm)

/-- A commuting square of pointed rings induces a unique local map of their colimits.
For local base rings and chosen separable closures, this is strict-henselization functoriality. -/
@[stacks 04GU "pointed-colimit form"]
theorem existsUnique_map (f : R →+* S) (φ : Ω →+* Ψ) [IsLocalHom φ]
    (hφ : φ.comp (algebraMap R Ω) = (algebraMap S Ψ).comp f) :
    ∃! g : algebra R Ω →+* algebra S Ψ,
      IsLocalHom g ∧
      g.comp (algebraMap R (algebra R Ω)) = (algebraMap S (algebra S Ψ)).comp f ∧
      (toTarget S Ψ).toRingHom.comp g = φ.comp (toTarget R Ω).toRingHom := by
  refine ⟨map f φ hφ, ⟨inferInstance, map_comp_algebraMap f φ hφ,
    toTarget_comp_map f φ hφ⟩, ?_⟩
  intro g hg
  exact map_unique f φ hφ g hg.2.1 hg.2.2

end Uniqueness

section Functoriality

variable {R S T Ω Ψ Χ : Type u} [CommRing R] [CommRing S] [CommRing T]
  [CommRing Ω] [CommRing Ψ] [CommRing Χ] [Algebra R Ω] [Algebra S Ψ] [Algebra T Χ]

/-- The identity square induces the identity of the pointed étale colimit. -/
@[simp]
theorem map_id {R Ω : Type u} [CommRing R] [CommRing Ω] [Algebra R Ω] :
    map (RingHom.id R) (RingHom.id Ω)
    (by simp) = RingHom.id (algebra R Ω) := by
  symm
  apply map_unique
  · simp
  · simp

private theorem comp_square (f : R →+* S) (g : S →+* T) (φ : Ω →+* Ψ) (ψ : Ψ →+* Χ)
    (hφ : φ.comp (algebraMap R Ω) = (algebraMap S Ψ).comp f)
    (hψ : ψ.comp (algebraMap S Ψ) = (algebraMap T Χ).comp g) :
    (ψ.comp φ).comp (algebraMap R Ω) = (algebraMap T Χ).comp (g.comp f) := by
  simpa only [RingHom.comp_assoc, hφ] using
    congrArg (fun h : S →+* Χ => h.comp f) hψ

/-- The map induced by a composite of pointed-ring squares is the composite of the induced
maps. -/
theorem map_comp (f : R →+* S) (g : S →+* T) (φ : Ω →+* Ψ) (ψ : Ψ →+* Χ)
    (hφ : φ.comp (algebraMap R Ω) = (algebraMap S Ψ).comp f)
    (hψ : ψ.comp (algebraMap S Ψ) = (algebraMap T Χ).comp g) :
    map (g.comp f) (ψ.comp φ) (by exact comp_square f g φ ψ hφ hψ) =
      (map g ψ hψ).comp (map f φ hφ) := by
  symm
  apply map_unique
  · ext r
    simp
  · ext x
    simp

/-- Successive applications of induced maps agree with the map of the composite square. -/
@[simp]
theorem map_map (f : R →+* S) (g : S →+* T) (φ : Ω →+* Ψ) (ψ : Ψ →+* Χ)
    (hφ : φ.comp (algebraMap R Ω) = (algebraMap S Ψ).comp f)
    (hψ : ψ.comp (algebraMap S Ψ) = (algebraMap T Χ).comp g) (x : algebra R Ω) :
    map g ψ hψ (map f φ hφ x) =
      map (g.comp f) (ψ.comp φ) (by exact comp_square f g φ ψ hφ hψ) x := by
  rw [map_comp, RingHom.comp_apply]

end Functoriality

end TauCeti.StrictHenselization
