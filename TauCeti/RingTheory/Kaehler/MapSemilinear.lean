/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Kaehler.Basic
public import TauCeti.Algebra.Ring.Hom

/-!
# Semilinear functoriality of Kähler differentials along algebra homomorphisms

For an `R`-algebra homomorphism `f : A →ₐ[R] B`, the induced map on Kähler differentials sends
`D x` to `D (f x)`. It is `R`-linear, since `f` fixes `R`, but it moves the `A`-action through
`f` — it is `f`-**semilinear**, `mapSemilinear f (a • ω) = f a • mapSemilinear f ω` — so it is
packaged as a semilinear map `Ω[A⁄R] →ₛₗ[f.toRingHom] Ω[B⁄R]`, following the precedent of
`LinearMap.frobenius`. The motivating special case is an algebra *endomorphism*
`f : S →ₐ[R] S` (for instance Frobenius), where this is the pullback of differentials along `f`
and where the map need not be `S`-linear.

Mathlib's `KaehlerDifferential.map` is functoriality for a *tower* `[Algebra A B]`
`[IsScalarTower R A B]`, so it cannot state this map: for an arbitrary `f : A →ₐ[R] B` no
`Algebra A B` instance exists, and for an endomorphism, installing one would clash with
`Algebra.id`. The two structures induced by `f` do exist *locally*, however, and `mapSemilinear` is
`KaehlerDifferential.map` under those local `letI` instances, repackaged with the `A`-action on
the target unfolded into `f`-semilinearity — which is exactly the statement that survives
outside the `letI` scope.

## Main definitions

* `KaehlerDifferential.mapSemilinear f : Ω[A⁄R] →ₛₗ[f.toRingHom] Ω[B⁄R]`
* `KaehlerDifferential.mapSemilinearEquiv e : Ω[A⁄R] ≃ₛₗ[e] Ω[B⁄R]`: the semilinear
  equivalence along an algebra isomorphism `e`.
* `KaehlerDifferential.mapSemilinearOfRingEquiv eR eA h : Ω[A⁄R] →ₛₗ[(eA : A →+* A')] Ω[A'⁄R']`:
  semilinear map of Kähler differentials along commuting ring isomorphisms `eR : R ≃+* R'` and
  `eA : A ≃+* A'`.
* `KaehlerDifferential.mapSemilinearEquivOfRingEquiv eR eA h`: the corresponding semilinear
  equivalence.

## Main results

* `KaehlerDifferential.mapSemilinear_D`: `mapSemilinear f (D x) = D (f x)`. This
  characterises the map: `Ω[A⁄R]` is spanned by the range of `D` (`span_range_derivation`), so
  two semilinear maps agreeing there are equal by `LinearMap.ext_on`.
* `KaehlerDifferential.mapSemilinear_toAlgHom_apply`: on a tower it agrees with Mathlib's
  `KaehlerDifferential.map`.
* `KaehlerDifferential.mapSemilinear_smul`: the semilinearity law, with `f` applied rather than
  `f.toRingHom`.
* `KaehlerDifferential.mapSemilinear_id`, `mapSemilinear_id_apply`: the identity acts as the
  identity.
* `KaehlerDifferential.mapSemilinear_comp_apply`, `mapSemilinear_comp`: compatibility with
  composition.
* `KaehlerDifferential.mapSemilinear_apply_symm_apply`, `mapSemilinear_symm_apply_apply`: along
  an algebra isomorphism the maps for `e` and `e.symm` are mutually inverse.
* `KaehlerDifferential.mapSemilinearOfRingEquiv_id`, `mapSemilinearOfRingEquiv_comp`,
  `mapSemilinearOfRingEquiv_apply_symm_apply`, `mapSemilinearEquivOfRingEquiv_refl`,
  `mapSemilinearEquivOfRingEquiv_trans`: identity, composition, inverse, and compatibility laws
  for the ring-equivalence Kähler maps and equivalences.
* `KaehlerDifferential.span_singleton_mapSemilinear_eq_top_iff`: a generating differential
  transfers along an algebra isomorphism.
* `KaehlerDifferential.nonempty_linearEquiv_pi_of_algEquiv`: freeness of the Kähler
  differentials on a given index type passes along an algebra isomorphism.

## Provenance

Ported from the AINTLIB `HasseWeil` project (Apache-2.0), revision `513e83879e2f`, file
`HasseWeil/Auxiliary/PullbackKaehler.lean`, declarations `AlgHom.pullbackKaehler`,
`pullbackKaehler_D`, `pullbackKaehler_smul_R`, `pullbackKaehler_smul_S`, `pullbackKaehler_comp`
and `pullbackKaehler_id`. The source treats an endomorphism of a fixed `S`, exports an
`AddMonoidHom` with hand-stated semilinearity lemmas, and builds the map from scratch through a
public `TwistedKaehler` module; here the map is generalised to an arbitrary `R`-algebra
homomorphism `A →ₐ[R] B`, constructed from Mathlib's `KaehlerDifferential.map`, and exported as
the semilinear map, whose type already carries the scalar law the source stated by hand.
-/

namespace KaehlerDifferential

variable {R A B C : Type*} [CommRing R] [CommRing A] [CommRing B] [CommRing C]
  [Algebra R A] [Algebra R B] [Algebra R C]

public section

/-- **The map of Kähler differentials along an `R`-algebra homomorphism** `f : A →ₐ[R] B`,
characterised by `mapSemilinear f (D x) = D (f x)`. It is `f`-semilinear:
`mapSemilinear f (a • ω) = f a • mapSemilinear f ω` (`mapSemilinear_smul`).

This is `KaehlerDifferential.map` under the local `Algebra A B` structure induced by `f`,
repackaged semilinearly so that the statement survives outside that instance's scope. -/
noncomputable def mapSemilinear (f : A →ₐ[R] B) : Ω[A⁄R] →ₛₗ[f.toRingHom] Ω[B⁄R] :=
  letI : Algebra A B := f.toRingHom.toAlgebra
  letI : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq' f.comp_algebraMap.symm
  { toFun := KaehlerDifferential.map R R A B
    map_add' := map_add _
    map_smul' := fun a ω => by
      -- The `A`-action induced by `f` on the target unfolds to acting through `f`.
      rw [LinearMap.map_smul]
      exact (IsScalarTower.algebraMap_smul B a (KaehlerDifferential.map R R A B ω)).symm }

/-- `mapSemilinear f` sends `D x` to `D (f x)`. -/
@[simp]
theorem mapSemilinear_D (f : A →ₐ[R] B) (x : A) : mapSemilinear f (D R A x) = D R B (f x) :=
  letI : Algebra A B := f.toRingHom.toAlgebra
  letI : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq' f.comp_algebraMap.symm
  KaehlerDifferential.map_D R R A B x

/-- The semilinearity law of `mapSemilinear`, stated with `f` applied rather than
`f.toRingHom`.

This is not interchangeable with the generic `map_smulₛₗ`: that lemma produces the coefficient
`f.toRingHom a`, which is only *definitionally* `f a`, and it carries no `@[simp]` attribute, so
`simp` alone leaves `mapSemilinear f (a • ω)` untouched. This is the simp-normal form. -/
@[simp]
theorem mapSemilinear_smul (f : A →ₐ[R] B) (a : A) (ω : Ω[A⁄R]) :
    mapSemilinear f (a • ω) = f a • mapSemilinear f ω :=
  (mapSemilinear f).map_smulₛₗ a ω

/-- The map along the identity is the identity, as (plainly linear) maps. -/
theorem mapSemilinear_id :
    (mapSemilinear (AlgHom.id R A) : Ω[A⁄R] →ₗ[A] Ω[A⁄R]) = LinearMap.id :=
  LinearMap.ext_on (span_range_derivation R A) <| by
    rintro _ ⟨x, rfl⟩; exact mapSemilinear_D _ x

/-- The map along the identity fixes every differential. -/
@[simp]
theorem mapSemilinear_id_apply (ω : Ω[A⁄R]) : mapSemilinear (AlgHom.id R A) ω = ω :=
  DFunLike.congr_fun mapSemilinear_id ω

/-- Functoriality of `mapSemilinear`, at map level. -/
theorem mapSemilinear_comp (f : B →ₐ[R] C) (g : A →ₐ[R] B) :
    mapSemilinear (f.comp g) = (mapSemilinear f).comp (mapSemilinear g) :=
  LinearMap.ext_on (span_range_derivation R A) <| by
    rintro _ ⟨x, rfl⟩
    rw [mapSemilinear_D, LinearMap.comp_apply, mapSemilinear_D, mapSemilinear_D, AlgHom.comp_apply]

/-- `mapSemilinear` is functorial: mapping along `f.comp g` is mapping along `g`, then along
`f`. -/
@[simp]
theorem mapSemilinear_comp_apply (f : B →ₐ[R] C) (g : A →ₐ[R] B) (ω : Ω[A⁄R]) :
    mapSemilinear (f.comp g) ω = mapSemilinear f (mapSemilinear g ω) :=
  DFunLike.congr_fun (mapSemilinear_comp f g) ω

/-- Mapping along `e.symm` and then along `e` fixes every differential. -/
@[simp]
theorem mapSemilinear_apply_symm_apply (e : A ≃ₐ[R] B) (ω : Ω[B⁄R]) :
    mapSemilinear e.toAlgHom (mapSemilinear e.symm.toAlgHom ω) = ω := by
  rw [← mapSemilinear_comp_apply, AlgEquiv.comp_symm, mapSemilinear_id_apply]

/-- Mapping along `e` and then along `e.symm` fixes every differential. -/
@[simp]
theorem mapSemilinear_symm_apply_apply (e : A ≃ₐ[R] B) (ω : Ω[A⁄R]) :
    mapSemilinear e.symm.toAlgHom (mapSemilinear e.toAlgHom ω) = ω :=
  mapSemilinear_apply_symm_apply e.symm ω

private theorem span_singleton_mapSemilinear_eq_top_of_eq_top (e : A ≃ₐ[R] B) {ω : Ω[A⁄R]}
    (h : Submodule.span A {ω} = ⊤) : Submodule.span B {mapSemilinear e.toAlgHom ω} = ⊤ := by
  rw [Submodule.span_singleton_eq_top_iff] at h ⊢
  intro ξ
  -- Write the transport of `ξ` back to `A` as a multiple of `ω`, then transport forward again.
  obtain ⟨c, hc⟩ := h (mapSemilinear e.symm.toAlgHom ξ)
  refine ⟨e c, ?_⟩
  rw [← mapSemilinear_apply_symm_apply e ξ, ← hc, mapSemilinear_smul, AlgEquiv.toAlgHom_apply]

/-- A single differential `ω` generates the Kähler differentials exactly when its transport
`mapSemilinear e ω` along an algebra isomorphism `e` does. -/
theorem span_singleton_mapSemilinear_eq_top_iff (e : A ≃ₐ[R] B) (ω : Ω[A⁄R]) :
    Submodule.span B {mapSemilinear e.toAlgHom ω} = ⊤ ↔ Submodule.span A {ω} = ⊤ :=
  ⟨fun h ↦ by
    simpa only [mapSemilinear_symm_apply_apply] using
      span_singleton_mapSemilinear_eq_top_of_eq_top e.symm h,
    span_singleton_mapSemilinear_eq_top_of_eq_top e⟩

attribute [local instance] RingHomInvPair.of_ringEquiv in
/-- **The isomorphism of Kähler differentials along an `R`-algebra isomorphism**
`e : A ≃ₐ[R] B`: `mapSemilinear e` and `mapSemilinear e.symm` are mutually inverse, so they form an
`e`-semilinear equivalence. -/
noncomputable def mapSemilinearEquiv (e : A ≃ₐ[R] B) :
    Ω[A⁄R] ≃ₛₗ[(e.toRingEquiv : A →+* B)] Ω[B⁄R] where
  __ := mapSemilinear e.toAlgHom
  invFun := mapSemilinear e.symm.toAlgHom
  left_inv := mapSemilinear_symm_apply_apply e
  right_inv := mapSemilinear_apply_symm_apply e

attribute [local instance] RingHomInvPair.of_ringEquiv in
/-- `mapSemilinearEquiv e` is `mapSemilinear e`. -/
@[simp]
theorem mapSemilinearEquiv_apply (e : A ≃ₐ[R] B) (ω : Ω[A⁄R]) :
    mapSemilinearEquiv e ω = mapSemilinear e.toAlgHom ω :=
  (rfl)

attribute [local instance] RingHomInvPair.of_ringEquiv in
/-- The inverse of `mapSemilinearEquiv e` is `mapSemilinear e.symm`. -/
@[simp]
theorem mapSemilinearEquiv_symm_apply (e : A ≃ₐ[R] B) (ω : Ω[B⁄R]) :
    (mapSemilinearEquiv e).symm ω = mapSemilinear e.symm.toAlgHom ω :=
  (rfl)

attribute [local instance] RingHomInvPair.of_ringEquiv in
/-- If the Kähler differentials of `B` over `R` are free on an index type `ι`, so are those of an
isomorphic `R`-algebra `A`: compose `mapSemilinearEquiv e` with the coordinatewise transport
along `e.symm`. -/
theorem nonempty_linearEquiv_pi_of_algEquiv {ι : Type*} (e : A ≃ₐ[R] B)
    (h : Nonempty (Ω[B⁄R] ≃ₗ[B] (ι → B))) : Nonempty (Ω[A⁄R] ≃ₗ[A] (ι → A)) := by
  obtain ⟨g⟩ := h
  let p : (ι → B) ≃ₛₗ[(e.toRingEquiv.symm : B →+* A)] (ι → A) :=
    { toFun v i := e.symm (v i)
      invFun v i := e (v i)
      map_add' _ _ := funext fun _ ↦ map_add e.symm _ _
      map_smul' _ _ := funext fun _ ↦ map_mul e.symm _ _
      left_inv _ := funext fun _ ↦ e.apply_symm_apply _
      right_inv _ := funext fun _ ↦ e.symm_apply_apply _ }
  exact ⟨((mapSemilinearEquiv e).trans g).trans p⟩

/-- On a tower, `mapSemilinear` along the structure map is Mathlib's `KaehlerDifferential.map`
— the sense in which this construction extends the tower functoriality to arbitrary algebra
homomorphisms. -/
@[simp]
theorem mapSemilinear_toAlgHom_apply [Algebra A B] [IsScalarTower R A B] (ω : Ω[A⁄R]) :
    mapSemilinear (IsScalarTower.toAlgHom R A B) ω = KaehlerDifferential.map R R A B ω := by
  -- Unlike the identity and composition laws this cannot be proved at map level: the two sides
  -- are semilinear over `algebraMap A B` and linear over `A`, i.e. the same function at different
  -- types, so `LinearMap.ext_on` has no equation to prove. Hence the induction.
  induction (span_range_derivation R A ▸ Submodule.mem_top :
      ω ∈ Submodule.span A (Set.range (D R A))) using Submodule.span_induction with
  | mem ω hω =>
    obtain ⟨x, rfl⟩ := hω
    rw [mapSemilinear_D, KaehlerDifferential.map_D, IsScalarTower.toAlgHom_apply]
  | zero => rw [map_zero, map_zero]
  | add ω₁ ω₂ _ _ ih₁ ih₂ => rw [map_add, map_add, ih₁, ih₂]
  | smul a ω _ ih =>
    rw [mapSemilinear_smul, LinearMap.map_smul, ih]
    exact IsScalarTower.algebraMap_smul B a _

section RingEquiv

variable {R' A' : Type*} [CommRing R'] [CommRing A'] [Algebra R' A']

/-- **The semilinear map on Kähler differentials along commuting ring isomorphisms**
`eR : R ≃+* R'` and `eA : A ≃+* A'`, characterised by sending `D R A x` to `D R' A' (eA x)`.

This is `KaehlerDifferential.map R R' A A'` under the local `Algebra` and `IsScalarTower`
instances induced by `eR` and `eA`, repackaged semilinearly so that the statement survives
outside those instances' scope. -/
noncomputable def mapSemilinearOfRingEquiv (eR : R ≃+* R') (eA : A ≃+* A')
    (h : ∀ r : R, algebraMap R' A' (eR r) = eA (algebraMap R A r)) :
    Ω[A⁄R] →ₛₗ[(eA : A →+* A')] Ω[A'⁄R'] :=
  letI : Algebra R R' := eR.toRingHom.toAlgebra
  letI : Algebra A A' := eA.toRingHom.toAlgebra
  letI : Algebra R A' := ((eA : A →+* A').comp (algebraMap R A)).toAlgebra
  letI : IsScalarTower R A A' := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower R R' A' := IsScalarTower.of_algebraMap_eq fun r ↦ by
    -- Unfold the local `R → A'` algebra structure (`eA ∘ algebraMap R A`) to match `h r`.
    simp only [RingHom.algebraMap_toAlgebra, RingHom.coe_comp, RingHom.coe_coe,
      Function.comp_apply]
    exact (h r).symm
  { toFun := KaehlerDifferential.map R R' A A'
    map_add' := map_add _
    map_smul' := fun a ω ↦ by
      -- Pull back the `A`-action on `Ω[A'⁄R']` along the local `IsScalarTower A A' Ω[A'⁄R']`.
      rw [LinearMap.map_smul]
      exact (IsScalarTower.algebraMap_smul A' a (KaehlerDifferential.map R R' A A' ω)).symm }

/-- `mapSemilinearOfRingEquiv` sends `D R A x` to `D R' A' (eA x)`. -/
@[simp]
theorem mapSemilinearOfRingEquiv_D (eR : R ≃+* R') (eA : A ≃+* A')
    (h : ∀ r : R, algebraMap R' A' (eR r) = eA (algebraMap R A r)) (x : A) :
    mapSemilinearOfRingEquiv eR eA h (D R A x) = D R' A' (eA x) :=
  letI : Algebra R R' := eR.toRingHom.toAlgebra
  letI : Algebra A A' := eA.toRingHom.toAlgebra
  letI : Algebra R A' := ((eA : A →+* A').comp (algebraMap R A)).toAlgebra
  letI : IsScalarTower R A A' := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower R R' A' := IsScalarTower.of_algebraMap_eq fun r ↦ by
    simp only [RingHom.algebraMap_toAlgebra, RingHom.coe_comp, RingHom.coe_coe,
      Function.comp_apply]
    exact (h r).symm
  KaehlerDifferential.map_D R R' A A' x

/-- Mapping along the identity ring equivalences is the identity map on `Ω[A⁄R]`. -/
theorem mapSemilinearOfRingEquiv_id
    (h : ∀ r : R, algebraMap R A (RingEquiv.refl R r) = RingEquiv.refl A (algebraMap R A r)) :
    (mapSemilinearOfRingEquiv (RingEquiv.refl R) (RingEquiv.refl A) h :
      Ω[A⁄R] →ₗ[A] Ω[A⁄R]) = LinearMap.id :=
  LinearMap.ext_on_range (span_range_derivation R A) fun x ↦
    mapSemilinearOfRingEquiv_D _ _ h x

/-- Mapping along the identity ring equivalences fixes every differential. -/
@[simp]
theorem mapSemilinearOfRingEquiv_id_apply
    (h : ∀ r : R, algebraMap R A (RingEquiv.refl R r) = RingEquiv.refl A (algebraMap R A r))
    (ω : Ω[A⁄R]) :
    mapSemilinearOfRingEquiv (RingEquiv.refl R) (RingEquiv.refl A) h ω = ω :=
  DFunLike.congr_fun (mapSemilinearOfRingEquiv_id h) ω

section Comp

variable {R'' A'' : Type*} [CommRing R''] [CommRing A''] [Algebra R'' A'']

/-- Composition of `mapSemilinearOfRingEquiv` along two commuting squares of ring equivalences. -/
theorem mapSemilinearOfRingEquiv_comp (eR₁ : R ≃+* R') (eA₁ : A ≃+* A')
    (h₁ : ∀ r : R, algebraMap R' A' (eR₁ r) = eA₁ (algebraMap R A r))
    (eR₂ : R' ≃+* R'') (eA₂ : A' ≃+* A'')
    (h₂ : ∀ r' : R', algebraMap R'' A'' (eR₂ r') = eA₂ (algebraMap R' A' r')) :
    letI : RingHomCompTriple (eA₁ : A →+* A') (eA₂ : A' →+* A'')
      ((eA₁.trans eA₂ : A ≃+* A'') : A →+* A'') := ⟨(RingEquiv.toRingHom_trans eA₁ eA₂).symm⟩
    (mapSemilinearOfRingEquiv eR₂ eA₂ h₂).comp (mapSemilinearOfRingEquiv eR₁ eA₁ h₁) =
      mapSemilinearOfRingEquiv (eR₁.trans eR₂) (eA₁.trans eA₂)
        (fun r ↦ by rw [RingEquiv.trans_apply, RingEquiv.trans_apply, h₂, h₁]) :=
  letI : RingHomCompTriple (eA₁ : A →+* A') (eA₂ : A' →+* A'')
    ((eA₁.trans eA₂ : A ≃+* A'') : A →+* A'') := ⟨(RingEquiv.toRingHom_trans eA₁ eA₂).symm⟩
  LinearMap.ext_on_range (span_range_derivation R A) fun x ↦ by
    simp only [LinearMap.comp_apply, mapSemilinearOfRingEquiv_D, RingEquiv.trans_apply]

/-- Applied composition of `mapSemilinearOfRingEquiv`, normalizing toward a single transport. -/
@[simp]
theorem mapSemilinearOfRingEquiv_comp_apply (eR₁ : R ≃+* R') (eA₁ : A ≃+* A')
    (h₁ : ∀ r : R, algebraMap R' A' (eR₁ r) = eA₁ (algebraMap R A r))
    (eR₂ : R' ≃+* R'') (eA₂ : A' ≃+* A'')
    (h₂ : ∀ r' : R', algebraMap R'' A'' (eR₂ r') = eA₂ (algebraMap R' A' r'))
    (ω : Ω[A⁄R]) :
    mapSemilinearOfRingEquiv eR₂ eA₂ h₂ (mapSemilinearOfRingEquiv eR₁ eA₁ h₁ ω) =
      mapSemilinearOfRingEquiv (eR₁.trans eR₂) (eA₁.trans eA₂)
        (fun r ↦ by rw [RingEquiv.trans_apply, RingEquiv.trans_apply, h₂, h₁]) ω :=
  letI : RingHomCompTriple (eA₁ : A →+* A') (eA₂ : A' →+* A'')
    ((eA₁.trans eA₂ : A ≃+* A'') : A →+* A'') := ⟨(RingEquiv.toRingHom_trans eA₁ eA₂).symm⟩
  DFunLike.congr_fun (mapSemilinearOfRingEquiv_comp eR₁ eA₁ h₁ eR₂ eA₂ h₂) ω

end Comp

/-- Mapping along `eR.symm, eA.symm` and then `eR, eA` is the identity on `Ω[A'⁄R']`. -/
theorem mapSemilinearOfRingEquiv_apply_symm_apply (eR : R ≃+* R') (eA : A ≃+* A')
    (h : ∀ r : R, algebraMap R' A' (eR r) = eA (algebraMap R A r)) (ω : Ω[A'⁄R']) :
    mapSemilinearOfRingEquiv eR eA h
        (mapSemilinearOfRingEquiv eR.symm eA.symm
          (RingEquiv.apply_symm_of_comm eR eA (algebraMap R A) (algebraMap R' A') h) ω) = ω := by
  have hcongr (eR₁ eR₂ : R' ≃+* R') (eA₁ eA₂ : A' ≃+* A') (hR : eR₁ = eR₂) (hA : eA₁ = eA₂)
      (h₁ : ∀ r' : R', algebraMap R' A' (eR₁ r') = eA₁ (algebraMap R' A' r'))
      (h₂ : ∀ r' : R', algebraMap R' A' (eR₂ r') = eA₂ (algebraMap R' A' r')) :
      mapSemilinearOfRingEquiv eR₁ eA₁ h₁ ω = mapSemilinearOfRingEquiv eR₂ eA₂ h₂ ω := by
    subst hR
    subst hA
    rfl
  refine (mapSemilinearOfRingEquiv_comp_apply eR.symm eA.symm _ eR eA h ω).trans ?_
  refine (hcongr _ _ _ _ (RingEquiv.symm_trans_self eR) (RingEquiv.symm_trans_self eA) _
    (fun _ ↦ rfl)).trans ?_
  exact mapSemilinearOfRingEquiv_id_apply _ ω

/-- Mapping along `eR, eA` and then `eR.symm, eA.symm` is the identity on `Ω[A⁄R]`. -/
theorem mapSemilinearOfRingEquiv_symm_apply_apply (eR : R ≃+* R') (eA : A ≃+* A')
    (h : ∀ r : R, algebraMap R' A' (eR r) = eA (algebraMap R A r)) (ω : Ω[A⁄R]) :
    mapSemilinearOfRingEquiv eR.symm eA.symm
        (RingEquiv.apply_symm_of_comm eR eA (algebraMap R A) (algebraMap R' A') h)
        (mapSemilinearOfRingEquiv eR eA h ω) = ω :=
  mapSemilinearOfRingEquiv_apply_symm_apply eR.symm eA.symm
    (RingEquiv.apply_symm_of_comm eR eA (algebraMap R A) (algebraMap R' A') h) ω

/-- When the base ring is fixed, `mapSemilinearOfRingEquiv` along `RingEquiv.refl R` and an
`R`-algebra equivalence `e : A ≃ₐ[R] B` agrees with `mapSemilinear e.toAlgHom`. -/
theorem mapSemilinearOfRingEquiv_refl_eq_mapSemilinear_apply (e : A ≃ₐ[R] B)
    (h : ∀ r : R, algebraMap R B (RingEquiv.refl R r) = e.toRingEquiv (algebraMap R A r))
    (ω : Ω[A⁄R]) :
    mapSemilinearOfRingEquiv (RingEquiv.refl R) e.toRingEquiv h ω = mapSemilinear e.toAlgHom ω := by
  let f' : Ω[A⁄R] →ₛₗ[(e.toRingEquiv : A →+* B)] Ω[B⁄R] :=
    { toFun := mapSemilinear e.toAlgHom
      map_add' := map_add _
      map_smul' := fun a ξ ↦ (mapSemilinear e.toAlgHom).map_smulₛₗ a ξ }
  have hf' (ξ : Ω[A⁄R]) : f' ξ = mapSemilinear e.toAlgHom ξ := rfl
  have hlin : mapSemilinearOfRingEquiv (RingEquiv.refl R) e.toRingEquiv h = f' :=
    LinearMap.ext_on_range (span_range_derivation R A) fun x ↦ by
      rw [mapSemilinearOfRingEquiv_D, hf', mapSemilinear_D, AlgEquiv.toAlgHom_apply,
        AlgEquiv.coe_toRingEquiv]
  exact DFunLike.congr_fun hlin ω

attribute [local instance] RingHomInvPair.of_ringEquiv in
/-- **The semilinear isomorphism of Kähler differentials along commuting ring isomorphisms**
`eR : R ≃+* R'` and `eA : A ≃+* A'`. -/
noncomputable def mapSemilinearEquivOfRingEquiv (eR : R ≃+* R') (eA : A ≃+* A')
    (h : ∀ r : R, algebraMap R' A' (eR r) = eA (algebraMap R A r)) :
    Ω[A⁄R] ≃ₛₗ[(eA : A →+* A')] Ω[A'⁄R'] :=
  { __ := mapSemilinearOfRingEquiv eR eA h
    invFun := mapSemilinearOfRingEquiv eR.symm eA.symm
      (RingEquiv.apply_symm_of_comm eR eA (algebraMap R A) (algebraMap R' A') h)
    left_inv := mapSemilinearOfRingEquiv_symm_apply_apply eR eA h
    right_inv := mapSemilinearOfRingEquiv_apply_symm_apply eR eA h }

attribute [local instance] RingHomInvPair.of_ringEquiv in
/-- `mapSemilinearEquivOfRingEquiv` acts as `mapSemilinearOfRingEquiv`. -/
@[simp]
theorem mapSemilinearEquivOfRingEquiv_apply (eR : R ≃+* R') (eA : A ≃+* A')
    (h : ∀ r : R, algebraMap R' A' (eR r) = eA (algebraMap R A r)) (ω : Ω[A⁄R]) :
    mapSemilinearEquivOfRingEquiv eR eA h ω = mapSemilinearOfRingEquiv eR eA h ω :=
  (rfl)

attribute [local instance] RingHomInvPair.of_ringEquiv in
/-- The inverse of `mapSemilinearEquivOfRingEquiv` acts as `mapSemilinearOfRingEquiv` along the
inverse equivalences. -/
@[simp]
theorem mapSemilinearEquivOfRingEquiv_symm_apply (eR : R ≃+* R') (eA : A ≃+* A')
    (h : ∀ r : R, algebraMap R' A' (eR r) = eA (algebraMap R A r)) (ω' : Ω[A'⁄R']) :
    (mapSemilinearEquivOfRingEquiv eR eA h).symm ω' =
      mapSemilinearOfRingEquiv eR.symm eA.symm
        (RingEquiv.apply_symm_of_comm eR eA (algebraMap R A) (algebraMap R' A') h) ω' :=
  (rfl)

attribute [local instance] RingHomInvPair.of_ringEquiv in
/-- `mapSemilinearEquivOfRingEquiv` along the identity equivalences is `LinearEquiv.refl`. -/
theorem mapSemilinearEquivOfRingEquiv_refl
    (h : ∀ r : R, algebraMap R A (RingEquiv.refl R r) = RingEquiv.refl A (algebraMap R A r)) :
    (mapSemilinearEquivOfRingEquiv (RingEquiv.refl R) (RingEquiv.refl A) h :
      Ω[A⁄R] ≃ₗ[A] Ω[A⁄R]) = LinearEquiv.refl A Ω[A⁄R] :=
  LinearEquiv.toLinearMap_injective (mapSemilinearOfRingEquiv_id h)

section EquivComp

variable {R'' A'' : Type*} [CommRing R''] [CommRing A''] [Algebra R'' A'']

attribute [local instance] RingHomInvPair.of_ringEquiv in
/-- `mapSemilinearEquivOfRingEquiv` is compatible with composition of commuting squares. -/
theorem mapSemilinearEquivOfRingEquiv_trans (eR₁ : R ≃+* R') (eA₁ : A ≃+* A')
    (h₁ : ∀ r : R, algebraMap R' A' (eR₁ r) = eA₁ (algebraMap R A r))
    (eR₂ : R' ≃+* R'') (eA₂ : A' ≃+* A'')
    (h₂ : ∀ r' : R', algebraMap R'' A'' (eR₂ r') = eA₂ (algebraMap R' A' r')) :
    letI : RingHomCompTriple (eA₁ : A →+* A') (eA₂ : A' →+* A'')
      ((eA₁.trans eA₂ : A ≃+* A'') : A →+* A'') := ⟨(RingEquiv.toRingHom_trans eA₁ eA₂).symm⟩
    letI : RingHomCompTriple (eA₂.symm : A'' →+* A') (eA₁.symm : A' →+* A)
      ((eA₁.trans eA₂ : A ≃+* A'').symm : A'' →+* A) :=
      ⟨RingHom.ext fun _ ↦ rfl⟩
    (mapSemilinearEquivOfRingEquiv eR₁ eA₁ h₁).trans (mapSemilinearEquivOfRingEquiv eR₂ eA₂ h₂) =
      mapSemilinearEquivOfRingEquiv (eR₁.trans eR₂) (eA₁.trans eA₂)
        (fun r ↦ by rw [RingEquiv.trans_apply, RingEquiv.trans_apply, h₂, h₁]) :=
  letI : RingHomCompTriple (eA₁ : A →+* A') (eA₂ : A' →+* A'')
    ((eA₁.trans eA₂ : A ≃+* A'') : A →+* A'') := ⟨(RingEquiv.toRingHom_trans eA₁ eA₂).symm⟩
  letI : RingHomCompTriple (eA₂.symm : A'' →+* A') (eA₁.symm : A' →+* A)
    ((eA₁.trans eA₂ : A ≃+* A'').symm : A'' →+* A) :=
    ⟨RingHom.ext fun _ ↦ rfl⟩
  LinearEquiv.toLinearMap_injective (mapSemilinearOfRingEquiv_comp eR₁ eA₁ h₁ eR₂ eA₂ h₂)

end EquivComp

end RingEquiv

end

end KaehlerDifferential
