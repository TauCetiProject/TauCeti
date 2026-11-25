/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.TensorProduct.Balanced.Extension
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.CategoryTheory.Adjunction.Unique

/-!
# Extension of scalars along a ring homomorphism of noncommutative rings, as a functor

For a ring homomorphism `f : R →+* S` of possibly noncommutative rings, the balanced extension of
scalars `P ↦ S ⊗_R P` of `TauCeti.BalancedExtension` is an additive functor
`ModuleCat R ⥤ ModuleCat S`, left adjoint to Mathlib's restriction of scalars
`ModuleCat.restrictScalars f`. When `R` and `S` are commutative it is therefore isomorphic to
Mathlib's `ModuleCat.extendScalars f`, by `s ⊗ p ↦ s ⊗ₜ p`.

## Main definitions

* `TauCeti.BalancedExtension.functor f`: the functor `ModuleCat R ⥤ ModuleCat S`.
* `TauCeti.BalancedExtension.adjunction f`: extension of scalars is left adjoint to
  restriction of scalars.
* `TauCeti.BalancedExtension.functorComp f g`: extension along `g ∘ f` is extension along `f`
  followed by extension along `g`.
* `TauCeti.BalancedExtension.functorCongr h`: extension along equal ring homomorphisms.
* `TauCeti.BalancedExtension.extendScalarsIso f`: for commutative rings, the identification with
  `ModuleCat.extendScalars f`.

## Main results

* `TauCeti.BalancedExtension.functor_map_surjective`: along a surjective ring homomorphism,
  every `S`-linear map `S ⊗_R P → S ⊗_R N` with `P` projective is the extension of an `R`-linear
  map `P → N`.

## References

* C. A. Weibel, *The K-book*, Chapter I, §2, pp. 7–8.
-/

public section

namespace TauCeti.BalancedExtension

open CategoryTheory

universe u₁ u₂ v

section Ring

variable {R : Type u₁} {S : Type u₂} [Ring R] [Ring S] (f : R →+* S)

/-- Extension of scalars `P ↦ S ⊗_R P` along a ring homomorphism `f : R →+* S`, as a functor
`ModuleCat R ⥤ ModuleCat S`. -/
-- Exposed so that elements of `(functor f).obj P` can be written as tensors in `S ⊗_R P`.
@[expose]
noncomputable def functor : ModuleCat.{v} R ⥤ ModuleCat.{max v u₂} S where
  obj P := ModuleCat.of S (BalancedExtension f P)
  map g := ModuleCat.ofHom (map f g.hom)
  map_id _ := ModuleCat.hom_ext map_id
  map_comp g g' := ModuleCat.hom_ext (map_comp g.hom g'.hom)

@[simp]
theorem functor_obj (P : ModuleCat.{v} R) :
    (functor f).obj P = ModuleCat.of S (BalancedExtension f P) := (rfl)

@[simp]
theorem functor_map_hom {P P' : ModuleCat.{v} R} (g : P ⟶ P') :
    ((functor f).map g).hom = map f g.hom := (rfl)

instance : (functor.{u₁, u₂, v} f).Additive where
  map_add {_ _ g g'} := ModuleCat.hom_ext (map_add g.hom g'.hom)

/-- Morphisms out of an extension of scalars are morphisms into a restriction of scalars: the
categorical form of `TauCeti.BalancedExtension.liftEquiv`. -/
private noncomputable def adjunctionHomEquiv (M : ModuleCat.{max v u₂} R)
    (N : ModuleCat.{max v u₂} S) :
    (ModuleCat.of S (BalancedExtension f M) ⟶ N) ≃ (M ⟶ (ModuleCat.restrictScalars f).obj N) where
  toFun φ := ModuleCat.semilinearMapAddEquiv f M N (φ.hom.comp (includeRight f M))
  invFun ψ := ModuleCat.ofHom (lift ((ModuleCat.semilinearMapAddEquiv f M N).symm ψ))
  left_inv φ := ModuleCat.hom_ext (hom_ext fun p ↦ by
    simp [-ModuleCat.semilinearMapAddEquiv_apply])
  right_inv ψ := by
    ext p
    simp [-ModuleCat.semilinearMapAddEquiv_apply]

private theorem adjunctionHomEquiv_apply {M : ModuleCat.{max v u₂} R}
    {N : ModuleCat.{max v u₂} S} (φ : ModuleCat.of S (BalancedExtension f M) ⟶ N) (m : M) :
    adjunctionHomEquiv f M N φ m = φ (tmul f 1 m) :=
  congrArg φ.hom (includeRight_apply m)

private theorem adjunctionHomEquiv_symm_apply {M : ModuleCat.{max v u₂} R}
    {N : ModuleCat.{max v u₂} S} (ψ : M ⟶ (ModuleCat.restrictScalars f).obj N) (s : S) (m : M) :
    (adjunctionHomEquiv f M N).symm ψ (tmul f s m) = s • ψ m :=
  lift_tmul _ s m

/-- **The universal property of extension of scalars**, as an adjunction: extension of scalars
along `f` is left adjoint to restriction of scalars along `f`. -/
noncomputable def adjunction :
    functor.{u₁, u₂, max v u₂} f ⊣ ModuleCat.restrictScalars.{max v u₂} f :=
  Adjunction.mkOfHomEquiv
    { homEquiv := adjunctionHomEquiv f
      homEquiv_naturality_left_symm g h := ModuleCat.hom_ext (hom_ext fun p ↦
        (adjunctionHomEquiv_symm_apply f (g ≫ h) 1 p).trans
          ((adjunctionHomEquiv_symm_apply f h 1 (g p)).symm.trans
            (congrArg _ (map_tmul g.hom 1 p).symm)))
      homEquiv_naturality_right g h := by
        ext p
        exact (adjunctionHomEquiv_apply f (g ≫ h) p).trans
          (congrArg h (adjunctionHomEquiv_apply f g p).symm) }

@[simp]
theorem adjunction_homEquiv_apply {M : ModuleCat.{max v u₂} R} {N : ModuleCat.{max v u₂} S}
    (φ : (functor f).obj M ⟶ N) (m : M) :
    (adjunction f).homEquiv M N φ m = φ (tmul f 1 m) :=
  adjunctionHomEquiv_apply f φ m

/-- The unit of the adjunction is `m ↦ 1 ⊗ m`. Not `@[simp]`: its left-hand side mentions the
composite functor, which `simp` unfolds. -/
theorem adjunction_unit_app_apply (M : ModuleCat.{max v u₂} R) (m : M) :
    (adjunction f).unit.app M m = tmul f 1 m :=
  adjunctionHomEquiv_apply f (𝟙 _) m

/-- The counit of the adjunction is `s ⊗ n ↦ s • n`. Not `@[simp]`: its left-hand side mentions
the composite functor, which `simp` unfolds. The carrier of `restrictScalars f N` is `N` itself,
but only `R` acts on it, so `n` is read back in `N` to apply the `S`-action. -/
theorem adjunction_counit_app_tmul (N : ModuleCat.{max v u₂} S) (s : S)
    (n : (ModuleCat.restrictScalars f).obj N) :
    (adjunction f).counit.app N (tmul f s n) = s • (show N from n) :=
  adjunctionHomEquiv_symm_apply f (𝟙 _) s n

@[simp]
theorem adjunction_homEquiv_symm_apply_tmul {M : ModuleCat.{max v u₂} R}
    {N : ModuleCat.{max v u₂} S} (ψ : M ⟶ (ModuleCat.restrictScalars f).obj N) (s : S) (m : M) :
    ((adjunction f).homEquiv M N).symm ψ (tmul f s m) = s • ψ m := by
  rw [Adjunction.homEquiv_counit]
  exact (congrArg ((adjunction f).counit.app N) (map_tmul (f := f) ψ.hom s m)).trans
    (adjunction_counit_app_tmul f N s (ψ m))

/-- **Extension of scalars along a surjection is full on projective sources.** If `f` is
surjective and `P` is projective, every `S`-linear map `S ⊗_R P → S ⊗_R N` is `S ⊗_R g` for an
`R`-linear map `g : P → N`. Without surjectivity this fails: along `ℤ → ℚ`, multiplication by `1/2`
on `ℚ ⊗_ℤ ℤ ≅ ℚ` is not `ℚ ⊗_ℤ g` for any `g : ℤ → ℤ`. -/
theorem functor_map_surjective (hf : Function.Surjective f) {P N : ModuleCat.{max v u₂} R}
    [Module.Projective R P] :
    Function.Surjective ((functor.{u₁, u₂, max v u₂} f).map :
      (P ⟶ N) → ((functor f).obj P ⟶ (functor f).obj N)) := by
  intro φ
  -- The adjoint `P → S ⊗_R N` of `φ` lifts along the unit `n ↦ 1 ⊗ n`, which is onto.
  obtain ⟨g, hg⟩ := Module.projective_lifting_property ((adjunction f).unit.app N).hom
    ((adjunction f).homEquiv P _ φ).hom fun x ↦
      (includeRight_surjective hf x).imp fun n hn ↦
        (adjunction_unit_app_apply f N n).trans ((includeRight_apply n).symm.trans hn)
  refine ⟨ModuleCat.ofHom g, ((adjunction f).homEquiv _ _).injective ?_⟩
  rw [Adjunction.homEquiv_unit, Adjunction.unit_naturality]
  exact ModuleCat.hom_ext hg

end Ring

section Composition

variable {R S T : Type u₁} [Ring R] [Ring S] [Ring T]

/-- Extension of scalars along equal ring homomorphisms gives isomorphic functors: the natural
isomorphism whose components are `TauCeti.BalancedExtension.congrRingHom`, `s ⊗ p ↦ s ⊗ p`. -/
noncomputable def functorCongr {f f' : R →+* S} (h : f = f') :
    functor.{u₁, u₁, max v u₁} f ≅ functor.{u₁, u₁, max v u₁} f' :=
  NatIso.ofComponents (fun P ↦ (congrRingHom (P := P) h).toModuleIso) fun φ ↦
    ModuleCat.hom_ext (congrRingHom_comp_map h (ModuleCat.Hom.hom φ))

@[simp]
theorem functorCongr_hom_app_tmul {f f' : R →+* S} (h : f = f') (P : ModuleCat.{max v u₁} R)
    (s : S) (p : P) :
    (functorCongr h).hom.app P (tmul f s p) = tmul f' s p :=
  congrRingHom_tmul h s p

@[simp]
theorem functorCongr_inv_app_tmul {f f' : R →+* S} (h : f = f') (P : ModuleCat.{max v u₁} R)
    (s : S) (p : P) :
    (functorCongr h).inv.app P (tmul f' s p) = tmul f s p :=
  (LinearEquiv.symm_apply_eq _).2 (congrRingHom_tmul h s p).symm

/-- Extension of scalars along a ring homomorphism and itself: the identity. -/
@[simp]
theorem functorCongr_refl (f : R →+* S) :
    functorCongr.{u₁, v} (rfl : f = f) = Iso.refl _ :=
  Iso.ext (NatTrans.ext (funext fun P ↦ ModuleCat.hom_ext (hom_ext fun p ↦
    functorCongr_hom_app_tmul rfl P 1 p)))

variable (f : R →+* S) (g : S →+* T)

/-- **Extension of scalars along a composite**, as a natural isomorphism: extending along `g ∘ f`
is extending along `f` and then along `g`. Its component at `P` is the inverse of
`TauCeti.BalancedExtension.cancelBaseChange`, `t ⊗ p ↦ t ⊗ (1 ⊗ p)`. This is the form of Mathlib's
`ModuleCat.extendScalarsComp` for possibly noncommutative rings. -/
noncomputable def functorComp :
    functor.{u₁, u₁, max v u₁} (g.comp f) ≅
      functor.{u₁, u₁, max v u₁} f ⋙ functor.{u₁, u₁, max v u₁} g :=
  (NatIso.ofComponents (fun P ↦ (cancelBaseChange f g (P := P)).toModuleIso) fun φ ↦
    ModuleCat.hom_ext (cancelBaseChange_comp_map f g (ModuleCat.Hom.hom φ))).symm

/-- The component of `TauCeti.BalancedExtension.functorComp` sends `t ⊗ p` to `t ⊗ (1 ⊗ p)`. Not
`@[simp]`: its left-hand side mentions the composite functor, which `simp` unfolds. -/
theorem functorComp_hom_app_tmul (P : ModuleCat.{max v u₁} R) (t : T) (p : P) :
    (functorComp f g).hom.app P (tmul (g.comp f) t p) = tmul g t (tmul f 1 p) :=
  cancelBaseChange_symm_tmul f g t p

/-- The inverse component of `TauCeti.BalancedExtension.functorComp` sends `t ⊗ (s ⊗ p)` to
`(t * g s) ⊗ p`. Not `@[simp]`: its left-hand side mentions the composite functor, which `simp`
unfolds. -/
theorem functorComp_inv_app_tmul (P : ModuleCat.{max v u₁} R) (t : T) (s : S) (p : P) :
    (functorComp f g).inv.app P (tmul g t (tmul f s p)) = tmul (g.comp f) (t * g s) p :=
  cancelBaseChange_tmul f g t s p

end Composition

section CommRing

variable {R : Type u₁} {S : Type u₂} [CommRing R] [CommRing S] (f : R →+* S)

open scoped ChangeOfRings

/-- For commutative rings, the balanced extension of scalars along `f` is Mathlib's extension of
scalars `ModuleCat.extendScalars f`, by `s ⊗ p ↦ s ⊗ₜ p`
(`TauCeti.BalancedExtension.extendScalarsIso_hom_app_tmul`). -/
noncomputable def extendScalarsIso :
    functor.{u₁, u₂, max v u₂} f ≅ ModuleCat.extendScalars.{u₁, u₂, max v u₂} f :=
  (adjunction f).leftAdjointUniq (ModuleCat.extendRestrictScalarsAdj f)

@[simp]
theorem extendScalarsIso_hom_app_tmul (M : ModuleCat.{max v u₂} R) (s : S) (m : M) :
    (extendScalarsIso f).hom.app M (tmul f s m) = s ⊗ₜ[R,f] m := by
  -- Both adjunctions have unit `m ↦ 1 ⊗ m`, and the comparison of left adjoints respects units.
  have h : (extendScalarsIso f).hom.app M (tmul f 1 m) = (1 : S) ⊗ₜ[R,f] m := by
    have := congr($(Adjunction.unit_leftAdjointUniq_hom_app (adjunction f)
      (ModuleCat.extendRestrictScalarsAdj f) M) m)
    rw [ConcreteCategory.comp_apply, adjunction_unit_app_apply] at this
    exact this
  rw [tmul_eq_smul_one_tmul]
  refine (((extendScalarsIso f).hom.app M).hom.map_smul s (tmul f 1 m)).trans ?_
  refine (congrArg (s • ·) h).trans ?_
  exact (ModuleCat.ExtendScalars.smul_tmul (f := f) s 1 m).trans
    (congrArg (· ⊗ₜ[R,f] m) (mul_one s))

@[simp]
theorem extendScalarsIso_inv_app_tmul (M : ModuleCat.{max v u₂} R) (s : S) (m : M) :
    (extendScalarsIso f).inv.app M (s ⊗ₜ[R,f] m) = tmul f s m :=
  (congrArg _ (extendScalarsIso_hom_app_tmul f M s m).symm).trans
    (ModuleCat.inv_hom_apply ((extendScalarsIso f).app M) (tmul f s m))

end CommRing

end TauCeti.BalancedExtension
