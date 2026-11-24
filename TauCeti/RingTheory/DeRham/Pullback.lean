/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.DeRham.Complex
public import TauCeti.RingTheory.Kaehler.DeRham.Basic

/-!
# Pullback of ordinary differential forms

For an `A`-algebra homomorphism `f : B →ₐ[A] C`, this file constructs the pullback of
differential forms `f* : Ωⁿ_(B/A) → Ωⁿ_(C/A)`, where `Ωⁿ = ⋀[B]^n Ω[B⁄A]`. It is `f`-semilinear
and `A`-linear, and it sends the elementary form `c • dv₀ ∧ ⋯ ∧ dvₙ₋₁` to
`f c • d(f v₀) ∧ ⋯ ∧ d(f vₙ₋₁)`. In degree zero it is `f`, and in degree one it is the semilinear
map of Kähler differentials `KaehlerDifferential.mapSemilinear f`.

Pullback commutes with the de Rham differential `TauCeti.DeRham.d`, preserves the wedge product
of the graded exterior algebra, and is functorial. Hence it assembles into a morphism of ordinary
de Rham complexes `TauCeti.DeRham.complexMap f : complex A B ⟶ complex A C`, functorial in `f`.

## Main definitions

* `TauCeti.DeRham.pullback f n`: the `f`-semilinear pullback `Ωⁿ_(B/A) → Ωⁿ_(C/A)`.
* `TauCeti.DeRham.pullbackLinear f n`: the pullback as an `A`-linear map.
* `TauCeti.DeRham.complexMap f`: the induced morphism of de Rham complexes.

## Main results

* `TauCeti.DeRham.pullback_elementary`: the value of the pullback on elementary forms.
* `TauCeti.DeRham.pullback_unique`: an `A`-linear map with this value on elementary forms is the
  pullback.
* `TauCeti.DeRham.zeroEquiv_pullback`, `TauCeti.DeRham.oneEquiv_pullback`: in degrees zero and
  one the pullback is `f` and `KaehlerDifferential.mapSemilinear f`.
* `TauCeti.DeRham.pullback_d`: pullback commutes with the de Rham differential.
* `TauCeti.DeRham.pullback_wedge`: pullback preserves wedge products.
* `TauCeti.DeRham.pullback_id`, `TauCeti.DeRham.pullback_comp`,
  `TauCeti.DeRham.pullbackLinear_comp`: functoriality of pullback.
* `TauCeti.DeRham.complexMap_id`, `TauCeti.DeRham.complexMap_comp`: functoriality of the
  morphism of de Rham complexes.

## Implementation notes

The pullback is the restriction to `⋀[B]^n Ω[B⁄A]` of the morphism of de Rham differential graded
algebras `TauCeti.KaehlerDeRham.map f` on the whole exterior algebra. That map is an algebra
homomorphism preserving the grading, which gives semilinearity, compatibility with wedge
products and functoriality. Compatibility with `TauCeti.DeRham.d` is checked on elementary forms,
which span the forms over `A`.

The semilinearity homomorphism of `pullback f n` is the coercion `(f : B →+* C)`, the simp-normal
form of `f.toRingHom`, so that its simp lemmas still apply once `simp` has normalised the type of
the map. For the same reason functoriality cannot be stated as a composite of semilinear maps:
Mathlib's `RingHomCompTriple` instance for algebra homomorphisms is phrased with
`AlgHom.toRingHom`. It is stated instead for the underlying functions (`pullback_comp`) and for the
`A`-linear pullbacks (`pullbackLinear_comp`).

## References

* The Stacks Project, Section 10.132 (Tag 0FKF), the functoriality of the de Rham complex.
-/

universe u v

namespace TauCeti.DeRham

open CategoryTheory _root_.KaehlerDifferential _root_.exteriorPower

section Pullback

variable {A B C E : Type*} [CommRing A] [CommRing B] [CommRing C] [CommRing E]
  [Algebra A B] [Algebra A C] [Algebra A E]

public section

/-- **Pullback of differential forms** along an `A`-algebra homomorphism `f : B →ₐ[A] C`: the
`f`-semilinear map `Ωⁿ_(B/A) → Ωⁿ_(C/A)` sending `c • dv₀ ∧ ⋯ ∧ dvₙ₋₁` to
`f c • d(f v₀) ∧ ⋯ ∧ d(f vₙ₋₁)` (`pullback_elementary`). It is also `A`-linear
(`pullback_base_smul`). -/
noncomputable def pullback (f : B →ₐ[A] C) (n : ℕ) :
    Forms A B n →ₛₗ[(f : B →+* C)] Forms A C n where
  toFun ω := ⟨KaehlerDeRham.map f ω.val, KaehlerDeRham.mem_grading_natCast.mp <|
    GradedFunLike.map_mem (KaehlerDeRham.map f)
      (KaehlerDeRham.mem_grading_natCast.mpr ω.property)⟩
  map_add' ω η := Subtype.ext (map_add (KaehlerDeRham.map f) ω.val η.val)
  map_smul' b ω := Subtype.ext (KaehlerDeRham.map_smul f b ω.val)

variable (f : B →ₐ[A] C) {n : ℕ}

/-- In the exterior algebra, the pullback of a form is its image under the morphism of de Rham
algebras `TauCeti.KaehlerDeRham.map f`. -/
@[simp]
theorem coe_pullback (ω : Forms A B n) :
    (pullback f n ω : ExteriorAlgebra C Ω[C⁄A]) = KaehlerDeRham.map f ω :=
  (rfl)

/-- Pullback is `A`-linear: `f* (a • ω) = a • f* ω` for `a : A`. -/
@[simp]
theorem pullback_base_smul (a : A) (ω : Forms A B n) :
    pullback f n (a • ω) = a • pullback f n ω := by
  rw [← algebraMap_smul B a ω, map_smulₛₗ, RingHom.coe_coe, AlgHom.commutes, algebraMap_smul]

/-- Pullback of a wedge product of `1`-forms: `f* (ω₀ ∧ ⋯ ∧ ωₙ₋₁)` is the wedge product of the
images of the `ωᵢ` under `KaehlerDifferential.mapSemilinear f`. -/
@[simp]
theorem pullback_ιMulti (v : Fin n → Ω[B⁄A]) :
    pullback f n (ιMulti B n v) = ιMulti C n (mapSemilinear f ∘ v) := by
  ext
  simp [ExteriorAlgebra.ιMulti_apply, map_list_prod, Function.comp_def]

/-- **Pullback of elementary forms**: `f* (c • dv₀ ∧ ⋯ ∧ dvₙ₋₁) = f c • d(f v₀) ∧ ⋯ ∧ d(f vₙ₋₁)`.
-/
@[simp]
theorem pullback_elementary (c : B) (v : Fin n → B) :
    pullback f n (elementary A c v) = elementary A (f c) (f ∘ v) := by
  simp only [elementary_def, map_smulₛₗ, RingHom.coe_coe, pullback_ιMulti, Function.comp_def,
    mapSemilinear_D]

/-- Pullback as an `A`-linear map `Ωⁿ_(B/A) →ₗ[A] Ωⁿ_(C/A)`, the form in which it enters the
de Rham complexes (`complexMap_f_hom`). -/
noncomputable def pullbackLinear (n : ℕ) : Forms A B n →ₗ[A] Forms A C n where
  toFun := pullback f n
  map_add' := map_add (pullback f n)
  map_smul' := pullback_base_smul f

/-- The `A`-linear pullback agrees with `pullback f n` pointwise. -/
@[simp]
theorem pullbackLinear_apply (ω : Forms A B n) : pullbackLinear f n ω = pullback f n ω :=
  (rfl)

/-- **Uniqueness of pullback.** An `A`-linear map `Ωⁿ_(B/A) → Ωⁿ_(C/A)` sending every elementary
form `c • dv₀ ∧ ⋯ ∧ dvₙ₋₁` to `f c • d(f v₀) ∧ ⋯ ∧ d(f vₙ₋₁)` is the pullback along `f`. -/
theorem pullback_unique (g : Forms A B n →ₗ[A] Forms A C n)
    (hg : ∀ (c : B) (v : Fin n → B), g (elementary A c v) = elementary A (f c) (f ∘ v)) :
    ⇑g = pullback f n := by
  have h : g = pullbackLinear f n :=
    forms_hom_ext fun c v => by rw [hg, pullbackLinear_apply, pullback_elementary]
  exact funext fun ω => (LinearMap.congr_fun h ω).trans (pullbackLinear_apply f ω)

/-- In degree zero, pullback is `f`: under `Ω⁰_(B/A) ≃ B` and `Ω⁰_(C/A) ≃ C`, it sends `b` to
`f b`. -/
@[simp]
theorem zeroEquiv_pullback (ω : Forms A B 0) :
    zeroEquiv C Ω[C⁄A] (pullback f 0 ω) = f (zeroEquiv B Ω[B⁄A] ω) := by
  obtain ⟨b, rfl⟩ : ∃ b : B, b • ιMulti B 0 ![] = ω :=
    ⟨zeroEquiv B Ω[B⁄A] ω, (zeroEquiv B Ω[B⁄A]).injective <| by simp⟩
  simp

/-- In degree one, pullback is `KaehlerDifferential.mapSemilinear f` under `Ω¹ ≃ Ω[B⁄A]` and
`Ω¹ ≃ Ω[C⁄A]`. -/
@[simp]
theorem oneEquiv_pullback (ω : Forms A B 1) :
    oneEquiv C Ω[C⁄A] (pullback f 1 ω) = mapSemilinear f (oneEquiv B Ω[B⁄A] ω) := by
  obtain ⟨θ, rfl⟩ : ∃ θ : Ω[B⁄A], ιMulti B 1 (fun _ => θ) = ω :=
    ⟨oneEquiv B Ω[B⁄A] ω, (oneEquiv B Ω[B⁄A]).injective <| by simp⟩
  simp

/-- **Pullback commutes with the de Rham differential**: `f* (d ω) = d (f* ω)`. -/
@[simp]
theorem pullback_d (ω : Forms A B n) :
    pullback f (n + 1) (d A B n ω) = d A C n (pullback f n ω) := by
  have h : pullbackLinear f (n + 1) ∘ₗ d A B n = d A C n ∘ₗ pullbackLinear f n :=
    forms_hom_ext fun c v => by
      simp only [LinearMap.comp_apply, pullbackLinear_apply, d_elementary, pullback_ιMulti,
        pullback_elementary, Fin.comp_cons]
      simp only [Function.comp_def, mapSemilinear_D]
  exact LinearMap.congr_fun h ω

/-- **Pullback preserves wedge products**: `f* (α ∧ β) = f* α ∧ f* β`, for the graded
multiplication of the exterior algebra. -/
@[simp]
theorem pullback_wedge {m : ℕ} (α : Forms A B m) (β : Forms A B n) :
    pullback f (m + n) (GradedMonoid.GMul.mul (A := fun i => Forms A B i) α β) =
      GradedMonoid.GMul.mul (A := fun i => Forms A C i) (pullback f m α) (pullback f n β) :=
  Subtype.ext (map_mul (KaehlerDeRham.map f) α.val β.val)

/-- Pullback along the identity fixes every form. -/
@[simp]
theorem pullback_id_apply (ω : Forms A B n) : pullback (AlgHom.id A B) n ω = ω :=
  Subtype.ext <| (coe_pullback _ ω).trans <| by simp

/-- Pullback along the identity is the identity. -/
theorem pullback_id : (pullback (AlgHom.id A B) n : Forms A B n →ₗ[B] Forms A B n) =
    LinearMap.id :=
  LinearMap.ext pullback_id_apply

/-- **Functoriality of pullback**: pullback along `g ∘ f` is pullback along `f`, then along `g`.
-/
@[simp]
theorem pullback_comp_apply (g : C →ₐ[A] E) (ω : Forms A B n) :
    pullback (g.comp f) n ω = pullback g n (pullback f n ω) :=
  Subtype.ext <| (coe_pullback _ ω).trans <| by simp

/-- **Functoriality of pullback**: as functions, pullback along `g ∘ f` is `g* ∘ f*`. -/
theorem pullback_comp (g : C →ₐ[A] E) :
    ⇑(pullback (g.comp f) n) = pullback g n ∘ pullback f n :=
  funext (pullback_comp_apply f g)

/-- **Functoriality of the `A`-linear pullback**: pullback along `g ∘ f` is the composite of the
`A`-linear pullbacks along `f` and `g`. -/
theorem pullbackLinear_comp (g : C →ₐ[A] E) :
    pullbackLinear (g.comp f) n = pullbackLinear g n ∘ₗ pullbackLinear f n :=
  LinearMap.ext (pullback_comp_apply f g)

end

end Pullback

section ComplexMap

variable {A : Type u} {B C E : Type v} [CommRing A] [CommRing B] [CommRing C] [CommRing E]
  [Algebra A B] [Algebra A C] [Algebra A E]

public section

/-- **The morphism of ordinary de Rham complexes** `Ω•_(B/A) ⟶ Ω•_(C/A)` induced by an
`A`-algebra homomorphism `f : B →ₐ[A] C`; its degree-`n` component is `pullback f n`
(`complexMap_f_apply`). -/
noncomputable def complexMap (f : B →ₐ[A] C) : complex A B ⟶ complex A C :=
  CochainComplex.ofHom (fun n => ModuleCat.ofHom (pullbackLinear f n)) fun n => by
    rw [complex_d, complex_d]
    ext ω
    -- The composites typecheck only because `(complex A B).X n` unfolds to
    -- `ModuleCat.of A (Forms A B n)` (`complex_X`, by `rfl`), so `ModuleCat.hom_comp` and
    -- `ModuleCat.hom_ofHom` cannot rewrite them; pointwise they are the two sides of `pullback_d`.
    exact (pullback_d f ω).symm

/-- The degree-`n` component of `complexMap f` is `pullback f n`. The form `ω` is typed in
`(complex A B).X n`, as produced by `ext`, so that this lemma rewrites there; that type is
`Forms A B n` by `complex_X`. -/
@[simp]
theorem complexMap_f_apply (f : B →ₐ[A] C) (n : ℕ) (ω : (complex A B).X n) :
    ((complexMap f).f n).hom ω = pullback f n ω :=
  (rfl)

/-- The degree-`n` component of `complexMap f` is the `A`-linear pullback `pullbackLinear f n`. -/
theorem complexMap_f_hom (f : B →ₐ[A] C) (n : ℕ) :
    ((complexMap f).f n).hom = pullbackLinear f n :=
  (rfl)

/-- The identity of `B` induces the identity of its de Rham complex. -/
@[simp]
theorem complexMap_id : complexMap (AlgHom.id A B) = 𝟙 (complex A B) := by
  ext n ω
  simp only [HomologicalComplex.id_f, ModuleCat.id_apply, complexMap_f_apply]
  -- `ω : (complex A B).X n` is `Forms A B n` only by `complex_X`, which `simp` cannot see through
  -- when matching `pullback_id_apply`; the two types agree definitionally.
  exact pullback_id_apply ω

/-- `complexMap` is functorial: `g ∘ f` induces the composite of the morphisms of de Rham
complexes. -/
@[simp]
theorem complexMap_comp (f : B →ₐ[A] C) (g : C →ₐ[A] E) :
    complexMap (g.comp f) = complexMap f ≫ complexMap g := by
  ext n ω
  simp only [HomologicalComplex.comp_f, ModuleCat.comp_apply, complexMap_f_apply]
  -- As in `complexMap_id`, `pullback_comp_apply` matches `ω` only up to `complex_X`,
  -- definitionally.
  exact pullback_comp_apply f g ω

end

end ComplexMap

end TauCeti.DeRham
