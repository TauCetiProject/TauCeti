/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.RestrictScalars
public import TauCeti.Algebra.Ring.Prod
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
* `TauCeti.BalancedExtension.functorCongr`, `functorId`, `functorComp`, `functorCompCongr`, and
  `functorRingEquivIso`: coherence and ring-equivalence natural isomorphisms for `functor`.
* `TauCeti.BalancedExtension.extendScalarsIso f`: for commutative rings, the identification with
  `ModuleCat.extendScalars f`.
* `TauCeti.BalancedExtension.restrictScalarsSelfEquiv`,
  `subsingleton_restrictScalars_of_map_eq_one_of_map_eq_zero`, and `prodModuleLinearEquiv`:
  surjective recovery, vanishing under annihilators, and `(R × S)`-module decomposition.

## References

* C. A. Weibel, *The K-book*, Chapter I, §2, pp. 7–8, and Chapter II, §2.8, pp. 12–13.
* Mathlib's `ModuleCat.extendScalars{Id,Comp}` and `ModuleCat.extendScalars_{assoc,id_comp,comp_id}`
  in `Mathlib/Algebra/Category/ModuleCat/ChangeOfRings.lean` (commutative coherence counterpart).
-/

public section

namespace TauCeti.BalancedExtension

open CategoryTheory

universe u₁ u₂ u₃ u₄ u₅ v

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

theorem functor_map_tmul {P P' : ModuleCat.{v} R} (g : P ⟶ P') (s : S) (p : P) :
    (functor f).map g (tmul f s p) = tmul f s (g p) :=
  map_tmul g.hom s p

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

end Ring

section Coherence

/-- **Extension of scalars along the identity ring homomorphism** is naturally isomorphic to the
identity functor, sending `r ⊗ m` to `r • m` (`TauCeti.BalancedExtension.lid`). -/
noncomputable def functorId (R : Type u₁) [Ring R] :
    functor.{u₁, u₁, max v u₁} (RingHom.id R) ≅ 𝟭 (ModuleCat.{max v u₁} R) :=
  NatIso.ofComponents (fun M ↦ ((lid R M).toModuleIso :
      (functor (RingHom.id R)).obj M ≅ (𝟭 (ModuleCat R)).obj M)) fun {_ _} φ ↦ by
    dsimp only [Functor.id_obj, functor]
    exact ModuleCat.hom_ext <| hom_ext fun m ↦ by simp

theorem functorId_hom_app_tmul (R : Type u₁) [Ring R] (M : ModuleCat.{max v u₁} R) (r : R) (m : M) :
    (functorId R).hom.app M (tmul (RingHom.id R) r m) = r • m := lid_tmul r m

theorem functorId_inv_app_apply (R : Type u₁) [Ring R] (M : ModuleCat.{max v u₁} R) (m : M) :
    (functorId R).inv.app M m = tmul (RingHom.id R) 1 m := lid_symm_apply m

@[simp] theorem functorId_hom_app_hom (R : Type u₁) [Ring R] (M : ModuleCat.{max v u₁} R) :
    ((functorId R).hom.app M).hom = (lid R M).toLinearMap := (rfl)

@[simp] theorem functorId_inv_app_hom (R : Type u₁) [Ring R] (M : ModuleCat.{max v u₁} R) :
    ((functorId R).inv.app M).hom = (lid R M).symm.toLinearMap := (rfl)

section Basic

variable {R : Type u₁} {S : Type u₂} {T : Type u₃} [Ring R] [Ring S] [Ring T]

/-- Morphisms out of `(functor f).obj M` agree once they agree on the pure tensors `1 ⊗ m`. -/
theorem functor_hom_ext (f : R →+* S) {M : ModuleCat.{v} R} {N : ModuleCat.{max v u₂} S}
    {φ ψ : (functor f).obj M ⟶ N} (h : ∀ m : M, φ (tmul f 1 m) = ψ (tmul f 1 m)) : φ = ψ :=
  ModuleCat.hom_ext (hom_ext h)

/-- Morphisms out of `(functor f ⋙ functor g).obj M` agree once they agree on `1 ⊗ (1 ⊗ m)`. -/
theorem functor_comp_hom_ext (f : R →+* S) (g : S →+* T) {M : ModuleCat.{v} R}
    {N : ModuleCat.{max v u₂ u₃} T} {φ ψ : (functor f ⋙ functor g).obj M ⟶ N}
    (h : ∀ m : M, φ (tmul g 1 (tmul f 1 m)) = ψ (tmul g 1 (tmul f 1 m))) : φ = ψ := by
  dsimp only [Functor.comp_obj, functor] at φ ψ h ⊢
  exact ModuleCat.hom_ext <|
    (LinearMap.cancel_right (cancelBaseChange f g (P := M)).symm.surjective).mp <|
      hom_ext fun m ↦ by
        simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, cancelBaseChange_symm_tmul]
        exact h m

/-- Equal ring homomorphisms induce naturally isomorphic balanced extension-of-scalars functors,
sending `s ⊗ m` to `s ⊗ m`. -/
noncomputable def functorCongr {f₁ f₂ : R →+* S} (h : f₁ = f₂) :
    functor.{u₁, u₂, v} f₁ ≅ functor.{u₁, u₂, v} f₂ :=
  eqToIso (congrArg (fun f ↦ functor.{u₁, u₂, v} f) h)

@[simp] theorem functorCongr_hom_app_tmul {f₁ f₂ : R →+* S} (h : f₁ = f₂) (M : ModuleCat.{v} R)
    (s : S) (m : M) : (functorCongr h).hom.app M (tmul f₁ s m) = tmul f₂ s m := by subst h; rfl

@[simp] theorem functorCongr_inv_app_tmul {f₁ f₂ : R →+* S} (h : f₁ = f₂) (M : ModuleCat.{v} R)
    (s : S) (m : M) : (functorCongr h).inv.app M (tmul f₂ s m) = tmul f₁ s m := by subst h; rfl

@[simp] theorem functorCongr_refl (f : R →+* S) :
    functorCongr (rfl : f = f) = Iso.refl (functor.{u₁, u₂, v} f) := (rfl)

@[simp] theorem functorCongr_symm {f₁ f₂ : R →+* S} (h : f₁ = f₂) :
    (functorCongr.{u₁, u₂, v} h).symm = functorCongr h.symm := by subst h; rfl

@[simp] theorem functorCongr_trans {f₁ f₂ f₃ : R →+* S} (h₁₂ : f₁ = f₂) (h₂₃ : f₂ = f₃) :
    functorCongr.{u₁, u₂, v} h₁₂ ≪≫ functorCongr h₂₃ = functorCongr (h₁₂.trans h₂₃) := by
  subst h₁₂; subst h₂₃; exact Iso.refl_trans _

/-- **Extension of scalars along a composite ring homomorphism** `g ∘ f` is naturally isomorphic
to extending along `f` and then along `g`, sending `t ⊗ m` to `t ⊗ (1 ⊗ m)` with inverse
`t ⊗ (s ⊗ m) ↦ (t * g s) ⊗ m` (`TauCeti.BalancedExtension.cancelBaseChange`). -/
noncomputable def functorComp (f : R →+* S) (g : S →+* T) :
    functor.{u₁, u₃, max v u₂} (g.comp f) ≅
      functor.{u₁, u₂, max v u₂} f ⋙ functor.{u₂, u₃, max v u₂} g :=
  NatIso.ofComponents (fun M ↦ ((cancelBaseChange f g (P := M)).symm.toModuleIso :
      (functor (g.comp f)).obj M ≅ (functor f ⋙ functor g).obj M)) fun {_ _} φ ↦ by
    dsimp only [Functor.comp_obj, functor]
    exact ModuleCat.hom_ext <| hom_ext fun m ↦ by simp

theorem functorComp_hom_app_tmul (f : R →+* S) (g : S →+* T) (M : ModuleCat.{max v u₂} R)
    (t : T) (m : M) : (functorComp f g).hom.app M (tmul (g.comp f) t m) = tmul g t (tmul f 1 m) :=
  cancelBaseChange_symm_tmul f g t m

theorem functorComp_inv_app_tmul_tmul (f : R →+* S) (g : S →+* T) (M : ModuleCat.{max v u₂} R)
    (t : T) (s : S) (m : M) :
    (functorComp f g).inv.app M (tmul g t (tmul f s m)) = tmul (g.comp f) (t * g s) m :=
  cancelBaseChange_tmul f g t s m

@[simp] theorem functorComp_hom_app_hom (f : R →+* S) (g : S →+* T) (M : ModuleCat.{max v u₂} R) :
    ((functorComp f g).hom.app M).hom = (cancelBaseChange f g).symm.toLinearMap := (rfl)

@[simp] theorem functorComp_inv_app_hom (f : R →+* S) (g : S →+* T) (M : ModuleCat.{max v u₂} R) :
    ((functorComp f g).inv.app M).hom = (cancelBaseChange f g).toLinearMap := (rfl)

end Basic

/-- **Pentagon coherence** for `TauCeti.BalancedExtension.functorComp` along three composable ring
homomorphisms. -/
@[reassoc] theorem functorComp_assoc {R₁ : Type u₁} {R₂ : Type u₂} {R₃ : Type u₃} {R₄ : Type u₄}
    [Ring R₁] [Ring R₂] [Ring R₃] [Ring R₄] (f₁₂ : R₁ →+* R₂) (f₂₃ : R₂ →+* R₃) (f₃₄ : R₃ →+* R₄) :
    (functorComp.{u₁, u₃, u₄, max v u₂ u₃} (f₂₃.comp f₁₂) f₃₄).hom ≫
      Functor.whiskerRight (functorComp.{u₁, u₂, u₃, max v u₂ u₃} f₁₂ f₂₃).hom
        (functor.{u₃, u₄, max v u₂ u₃} f₃₄) =
    (functorComp.{u₁, u₂, u₄, max v u₂ u₃} f₁₂ (f₃₄.comp f₂₃)).hom ≫
      Functor.whiskerLeft (functor.{u₁, u₂, max v u₂ u₃} f₁₂)
        (functorComp.{u₂, u₃, u₄, max v u₂ u₃} f₂₃ f₃₄).hom ≫
      (Functor.associator _ _ _).inv := by
  refine NatTrans.ext <| funext fun M ↦ ?_
  dsimp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_inv_app, Functor.comp_obj, functorComp, NatIso.ofComponents, functor]
  rw [Category.comp_id]
  refine ModuleCat.hom_ext <| hom_ext fun m ↦ ?_
  have h₁ : (cancelBaseChange f₁₂ (f₃₄.comp f₂₃) (P := M)).symm
      (tmul (f₃₄.comp (f₂₃.comp f₁₂)) 1 m) = tmul (f₃₄.comp f₂₃) 1 (tmul f₁₂ 1 m) :=
    cancelBaseChange_symm_tmul f₁₂ (f₃₄.comp f₂₃) 1 m
  simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearEquiv.toModuleIso_hom,
    LinearMap.comp_apply, LinearEquiv.coe_coe, cancelBaseChange_symm_tmul, map_tmul, h₁]

/-- **Left-unit coherence** for `TauCeti.BalancedExtension.functorId` and
`TauCeti.BalancedExtension.functorComp`. -/
@[reassoc] theorem functorComp_id_comp {R : Type u₁} {S : Type u₂} [Ring R] [Ring S] (f : R →+* S) :
    (functorComp.{u₁, u₁, u₂, max v u₁} (RingHom.id R) f).hom ≫
      Functor.whiskerRight (functorId.{u₁, max v u₁} R).hom (functor.{u₁, u₂, max v u₁} f) ≫
      (Functor.leftUnitor (functor.{u₁, u₂, max v u₁} f)).hom = 𝟙 _ := by
  refine NatTrans.ext <| funext fun M ↦ ?_
  dsimp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.leftUnitor_hom_app,
    NatTrans.id_app, Functor.comp_obj, Functor.id_obj, functorComp, functorId,
    NatIso.ofComponents, functor]
  rw [Category.comp_id]
  refine ModuleCat.hom_ext <| hom_ext fun m ↦ ?_
  simp only [ModuleCat.hom_comp, ModuleCat.hom_id, ModuleCat.hom_ofHom,
    LinearEquiv.toModuleIso_hom, LinearMap.comp_apply, LinearEquiv.coe_coe,
    cancelBaseChange_symm_tmul, map_tmul, lid_tmul, one_smul, LinearMap.id_apply]
  -- `f.comp (RingHom.id R) = f` is definitional inside the dependent return type of `tmul`.
  rfl

/-- **Right-unit coherence** for `TauCeti.BalancedExtension.functorId` and
`TauCeti.BalancedExtension.functorComp`. -/
@[reassoc] theorem functorComp_comp_id {R : Type u₁} {S : Type u₂} [Ring R] [Ring S] (f : R →+* S) :
    (functorComp.{u₁, u₂, u₂, max v u₂} f (RingHom.id S)).hom ≫
      Functor.whiskerLeft (functor.{u₁, u₂, max v u₂} f) (functorId.{u₂, max v u₂} S).hom ≫
      (Functor.rightUnitor (functor.{u₁, u₂, max v u₂} f)).hom = 𝟙 _ := by
  refine NatTrans.ext <| funext fun M ↦ ?_
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.rightUnitor_hom_app,
    NatTrans.id_app, Functor.comp_obj, Functor.id_obj, functorComp, functorId,
    NatIso.ofComponents, functor]
  rw [Category.comp_id]
  refine ModuleCat.hom_ext <| hom_ext fun m ↦ ?_
  simp only [ModuleCat.hom_comp, ModuleCat.hom_id, ModuleCat.hom_ofHom,
    LinearEquiv.toModuleIso_hom, LinearMap.comp_apply, LinearEquiv.coe_coe,
    cancelBaseChange_symm_tmul, lid_tmul, one_smul, LinearMap.id_apply]
  -- `(RingHom.id S).comp f = f` is definitional inside the dependent return type of `tmul`.
  rfl

section Square

variable {A : Type u₁} {B : Type u₂} {C : Type u₃} {D : Type u₄}
  [Ring A] [Ring B] [Ring C] [Ring D]

/-- **Coherence of balanced extension of scalars across a commutative square.** Given
`g₁.comp f₁ = g₂.comp f₂`, the two composite extension-of-scalars functors are naturally
isomorphic by `d ⊗ (b ⊗ m) ↦ (d * g₁ b) ⊗ (1 ⊗ m)`. -/
noncomputable def functorCompCongr (f₁ : A →+* B) (g₁ : B →+* D) (f₂ : A →+* C) (g₂ : C →+* D)
    (h : g₁.comp f₁ = g₂.comp f₂) :
    functor.{u₁, u₂, max v u₂ u₃} f₁ ⋙ functor.{u₂, u₄, max v u₂ u₃} g₁ ≅
      functor.{u₁, u₃, max v u₂ u₃} f₂ ⋙ functor.{u₃, u₄, max v u₂ u₃} g₂ :=
  (functorComp.{u₁, u₂, u₄, max v u₂ u₃} f₁ g₁).symm ≪≫
    functorCongr.{u₁, u₄, max v u₂ u₃} h ≪≫
    functorComp.{u₁, u₃, u₄, max v u₂ u₃} f₂ g₂

theorem functorCompCongr_def (f₁ : A →+* B) (g₁ : B →+* D) (f₂ : A →+* C) (g₂ : C →+* D)
    (h : g₁.comp f₁ = g₂.comp f₂) :
    functorCompCongr.{u₁, u₂, u₃, u₄, v} f₁ g₁ f₂ g₂ h =
      (functorComp.{u₁, u₂, u₄, max v u₂ u₃} f₁ g₁).symm ≪≫
        functorCongr.{u₁, u₄, max v u₂ u₃} h ≪≫
        functorComp.{u₁, u₃, u₄, max v u₂ u₃} f₂ g₂ := (rfl)

-- Not `@[simp]`: its left-hand side mentions the composite functor, which `Functor.comp_obj`
-- simplifies inside the coercion type parameter.
/-- The forward component of `functorCompCongr` sends `d ⊗ (b ⊗ m)` to `(d * g₁ b) ⊗ (1 ⊗ m)`. -/
theorem functorCompCongr_hom_app_tmul_tmul (f₁ : A →+* B) (g₁ : B →+* D) (f₂ : A →+* C)
    (g₂ : C →+* D) (h : g₁.comp f₁ = g₂.comp f₂) (M : ModuleCat.{max v u₂ u₃} A)
    (d : D) (b : B) (m : M) :
    (functorCompCongr.{u₁, u₂, u₃, u₄, v} f₁ g₁ f₂ g₂ h).hom.app M (tmul g₁ d (tmul f₁ b m)) =
      tmul g₂ (d * g₁ b) (tmul f₂ 1 m) := by
  rw [functorCompCongr_def, Iso.trans_hom, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    NatTrans.comp_app]
  refine (ConcreteCategory.comp_apply _ _ _).trans <| (ConcreteCategory.comp_apply _ _ _).trans ?_
  rw [functorComp_inv_app_tmul_tmul, functorCongr_hom_app_tmul, functorComp_hom_app_tmul]

-- Not `@[simp]`: its left-hand side mentions the composite functor, which `Functor.comp_obj`
-- simplifies inside the coercion type parameter.
/-- The inverse component of `functorCompCongr` sends `d ⊗ (c ⊗ m)` to `(d * g₂ c) ⊗ (1 ⊗ m)`. -/
theorem functorCompCongr_inv_app_tmul_tmul (f₁ : A →+* B) (g₁ : B →+* D) (f₂ : A →+* C)
    (g₂ : C →+* D) (h : g₁.comp f₁ = g₂.comp f₂) (M : ModuleCat.{max v u₂ u₃} A)
    (d : D) (c : C) (m : M) :
    (functorCompCongr.{u₁, u₂, u₃, u₄, v} f₁ g₁ f₂ g₂ h).inv.app M (tmul g₂ d (tmul f₂ c m)) =
      tmul g₁ (d * g₂ c) (tmul f₁ 1 m) := by
  rw [functorCompCongr_def, Iso.trans_inv, Iso.trans_inv, Iso.symm_inv, Category.assoc,
    NatTrans.comp_app, NatTrans.comp_app]
  refine (ConcreteCategory.comp_apply _ _ _).trans <| (ConcreteCategory.comp_apply _ _ _).trans ?_
  rw [functorComp_inv_app_tmul_tmul, functorCongr_inv_app_tmul, functorComp_hom_app_tmul]

@[simp] theorem functorCompCongr_self (f : A →+* B) (g : B →+* D) :
    functorCompCongr.{u₁, u₂, u₂, u₄, v} f g f g rfl =
      Iso.refl (functor.{u₁, u₂, max v u₂} f ⋙ functor.{u₂, u₄, max v u₂} g) := by
  simp [functorCompCongr_def]

@[simp] theorem functorCompCongr_symm (f₁ : A →+* B) (g₁ : B →+* D) (f₂ : A →+* C) (g₂ : C →+* D)
    (h : g₁.comp f₁ = g₂.comp f₂) :
    (functorCompCongr.{u₁, u₂, u₃, u₄, v} f₁ g₁ f₂ g₂ h).symm =
      functorCompCongr f₂ g₂ f₁ g₁ h.symm := by simp [functorCompCongr_def]

end Square

/-- Composing the coherence isomorphisms of two commutative squares sharing the intermediate path
`A → B₂ → D` yields the coherence isomorphism of the outer square. -/
theorem functorCompCongr_trans {A : Type u₁} {B₁ : Type u₂} {B₂ : Type u₃} {B₃ : Type u₄}
    {D : Type u₅} [Ring A] [Ring B₁] [Ring B₂] [Ring B₃] [Ring D]
    (f₁ : A →+* B₁) (g₁ : B₁ →+* D) (f₂ : A →+* B₂) (g₂ : B₂ →+* D)
    (f₃ : A →+* B₃) (g₃ : B₃ →+* D)
    (h₁₂ : g₁.comp f₁ = g₂.comp f₂) (h₂₃ : g₂.comp f₂ = g₃.comp f₃) :
    functorCompCongr.{u₁, u₂, u₃, u₅, max v u₄} f₁ g₁ f₂ g₂ h₁₂ ≪≫
        functorCompCongr.{u₁, u₃, u₄, u₅, max v u₂} f₂ g₂ f₃ g₃ h₂₃ =
      functorCompCongr.{u₁, u₂, u₄, u₅, max v u₃} f₁ g₁ f₃ g₃ (h₁₂.trans h₂₃) := by
  simp only [functorCompCongr_def, Iso.trans_assoc, Iso.self_symm_id_assoc]
  rw [← Iso.trans_assoc (functorCongr h₁₂), functorCongr_trans]

section RingEquiv

variable {R : Type u₁} {S : Type u₂} [Ring R] [Ring S]

/-- Along a ring isomorphism `e : R ≃+* S`, balanced extension of scalars along `e.toRingHom` is
naturally isomorphic to restriction of scalars along `e.symm`, since both functors are left adjoint
to restriction of scalars along `e.toRingHom`. -/
noncomputable def functorRingEquivIso (e : R ≃+* S) :
    functor.{u₁, u₂, max v u₂} (e : R →+* S) ≅
      ModuleCat.restrictScalars.{max v u₂} (e.symm : S →+* R) :=
  (adjunction (e : R →+* S)).leftAdjointUniq
    (ModuleCat.restrictScalarsEquivalenceOfRingEquiv e).symm.toAdjunction

/-- On pure tensors `1 ⊗ m`, `functorRingEquivIso` sends `1 ⊗ m` to `m` in the restricted module. -/
theorem functorRingEquivIso_hom_app_tmul_one (e : R ≃+* S) (M : ModuleCat.{max v u₂} R)
    (m : M) :
    (functorRingEquivIso e).hom.app M (tmul (e : R →+* S) 1 m) =
      ModuleCat.restrictScalarsAddEquiv (e.symm : S →+* R) M m := by
  let adj₂ : ModuleCat.restrictScalars.{max v u₂} (e.symm : S →+* R) ⊣
      ModuleCat.restrictScalars.{max v u₂} (e : R →+* S) :=
    (ModuleCat.restrictScalarsEquivalenceOfRingEquiv e).symm.toAdjunction
  have h := congrArg (ModuleCat.restrictScalarsAddEquiv (e : R →+* S)
      ((ModuleCat.restrictScalars (e.symm : S →+* R)).obj M)).symm
    (ConcreteCategory.congr_hom
      (Adjunction.unit_leftAdjointUniq_hom_app (adjunction (e : R →+* S)) adj₂ M) m)
  rw [ConcreteCategory.comp_apply, ModuleCat.restrictScalarsAddEquiv_symm_map_apply,
    ModuleCat.restrictScalarsAddEquiv_symm_apply, adjunction_unit_app_apply,
    ModuleCat.restrictScalarsAddEquiv_symm_apply] at h
  rw [ModuleCat.restrictScalarsAddEquiv_apply]
  refine h.trans ?_
  dsimp only [adj₂, Equivalence.toAdjunction_unit, Equivalence.symm_unit, Equivalence.counitInv]
  exact ModuleCat.restrictScalarsEquivalenceOfRingEquiv_counitIso_inv_app_apply e M m

@[simp] theorem functorRingEquivIso_hom_app_tmul (e : R ≃+* S) (M : ModuleCat.{max v u₂} R)
    (s : S) (m : M) :
    (functorRingEquivIso e).hom.app M (tmul (e : R →+* S) s m) =
      ModuleCat.restrictScalarsAddEquiv (e.symm : S →+* R) M (e.symm s • m) := by
  rw [tmul_eq_smul_one_tmul]
  refine (((functorRingEquivIso e).hom.app M).hom.map_smul s _).trans ?_
  rw [functorRingEquivIso_hom_app_tmul_one, ModuleCat.smul_restrictScalarsAddEquiv,
    RingEquiv.coe_toRingHom]

@[simp] theorem functorRingEquivIso_inv_app_apply (e : R ≃+* S) (M : ModuleCat.{max v u₂} R)
    (m : (ModuleCat.restrictScalars (e.symm : S →+* R)).obj M) :
    (functorRingEquivIso e).inv.app M m =
      tmul (e : R →+* S) 1
        ((ModuleCat.restrictScalarsAddEquiv (e.symm : S →+* R) M).symm m) := by
  have h : (functorRingEquivIso e).hom.app M (tmul (e : R →+* S) 1
      ((ModuleCat.restrictScalarsAddEquiv (e.symm : S →+* R) M).symm m)) = m := by simp
  exact (congrArg _ h.symm).trans (ModuleCat.inv_hom_apply ((functorRingEquivIso e).app M) _)

end RingEquiv

end Coherence

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

section Split

variable {E : Type u₁} {A : Type u₂} {B : Type u₃} [Ring E] [Ring A] [Ring B]

/-- Along a surjective ring homomorphism `p : E →+* A`, extending scalars along `p` after
restricting scalars along `p` recovers `M` via `a ⊗ x ↦ a • x` with inverse `m ↦ 1 ⊗ m`. -/
noncomputable def restrictScalarsSelfEquiv (p : E →+* A) (hp : Function.Surjective p)
    (M : ModuleCat.{v} A) :
    BalancedExtension p ((ModuleCat.restrictScalars.{v} p).obj M) ≃ₗ[A] M :=
  LinearEquiv.ofLinearMap (lift (p.restrictScalarsSemilinearMap M))
    { toFun m := tmul p 1 (ModuleCat.restrictScalarsAddEquiv p M m)
      map_add' _ _ := by rw [_root_.map_add, tmul_add]
      map_smul' a m := by
        obtain ⟨e, rfl⟩ := hp a
        rw [← ModuleCat.smul_restrictScalarsAddEquiv, tmul_smul, one_mul, RingHom.id_apply,
          smul_tmul, mul_one] }
    (LinearMap.ext fun m ↦ by
      simp only [LinearMap.comp_apply, LinearMap.coe_mk, AddHom.coe_mk, lift_tmul, one_smul,
        LinearMap.id_apply]
      rw [RingHom.restrictScalarsSemilinearMap_apply]
      exact ModuleCat.restrictScalarsAddEquiv_apply p M m)
    (hom_ext fun x ↦ by
      simp only [LinearMap.comp_apply, lift_tmul, one_smul, LinearMap.coe_mk, AddHom.coe_mk,
        LinearMap.id_apply]
      rw [RingHom.restrictScalarsSemilinearMap_apply]
      exact congrArg (tmul p 1) (ModuleCat.restrictScalarsAddEquiv_apply p M x))

@[simp] theorem restrictScalarsSelfEquiv_tmul (p : E →+* A) (hp : Function.Surjective p)
    (M : ModuleCat.{v} A) (a : A) (x : (ModuleCat.restrictScalars.{v} p).obj M) :
    restrictScalarsSelfEquiv p hp M (tmul p a x) =
      a • (ModuleCat.restrictScalarsAddEquiv p M).symm x := by
  simp [restrictScalarsSelfEquiv, ModuleCat.restrictScalarsAddEquiv_symm_apply]

@[simp] theorem restrictScalarsSelfEquiv_symm_apply (p : E →+* A) (hp : Function.Surjective p)
    (M : ModuleCat.{v} A) (m : M) :
    (restrictScalarsSelfEquiv p hp M).symm m =
      tmul p 1 (ModuleCat.restrictScalarsAddEquiv p M m) := (rfl)

/-- If `p : E →+* A` and `p' : E →+* B` admit an element `e : E` with `p e = 1` and `p' e = 0`,
then extending along `p` any `B`-module restricted along `p'` yields a subsingleton module. -/
theorem subsingleton_restrictScalars_of_map_eq_one_of_map_eq_zero (p : E →+* A) (p' : E →+* B)
    (e : E) (hp : p e = 1) (hp' : p' e = 0) (N : ModuleCat.{v} B) :
    Subsingleton (BalancedExtension p ((ModuleCat.restrictScalars.{v} p').obj N)) :=
  subsingleton_of_isUnit_of_smul_eq_zero p e (by rw [hp]; exact isUnit_one) fun n ↦
    (ModuleCat.restrictScalarsAddEquiv p' N).symm.injective
      (by rw [ModuleCat.restrictScalarsAddEquiv_symm_smul, hp', zero_smul, map_zero])

private noncomputable def splitInclude (p : E →+* A) (P : ModuleCat.{v} E) :
    P →ₗ[E] (ModuleCat.restrictScalars p).obj (ModuleCat.of A (BalancedExtension p P)) where
  toFun x := ModuleCat.restrictScalarsAddEquiv p (ModuleCat.of A (BalancedExtension p P))
    (tmul p 1 x)
  map_add' _ _ := by rw [tmul_add, _root_.map_add]
  map_smul' _ _ := by
    rw [tmul_smul, one_mul, RingHom.id_apply, ModuleCat.smul_restrictScalarsAddEquiv, smul_tmul,
      mul_one]

section SplitLift

variable (p : E →+* A) (j : A →+ E) (hL : ∀ e a, e * j a = j (p e * a))
  (hR : ∀ a e, j a * e = j (a * p e)) (P : ModuleCat.{v} E)

private noncomputable def splitLift :
    (ModuleCat.restrictScalars p).obj (ModuleCat.of A (BalancedExtension p P)) →ₗ[E] P :=
  let aux := BalancedTensorProduct.lift
    (LinearMap.mk₂ ℤ (fun a x ↦ j ((Scalars.of p).symm a) • x)
      (fun _ _ _ ↦ by rw [_root_.map_add, _root_.map_add, add_smul])
      (fun _ _ _ ↦ by rw [map_zsmul, map_zsmul, smul_assoc])
      (fun _ _ _ ↦ smul_add _ _ _) (fun _ _ _ ↦ smul_comm _ _ _))
    fun e a x ↦ by
      obtain ⟨a, rfl⟩ := (Scalars.of p).surjective a
      simp only [LinearMap.mk₂_apply, Scalars.op_smul_of, AddEquiv.symm_apply_apply, ← mul_smul, hR]
  { toFun q := aux ((ModuleCat.restrictScalarsAddEquiv p _).symm q)
    map_add' _ _ := by rw [_root_.map_add, _root_.map_add]
    map_smul' e q := by
      rw [ModuleCat.restrictScalarsAddEquiv_symm_smul, RingHom.id_apply]
      induction (ModuleCat.restrictScalarsAddEquiv p _).symm q using induction_on with
      | tmul a x =>
        dsimp only [aux]
        rw [smul_tmul, tmul_def, tmul_def, BalancedTensorProduct.lift_tmul,
          BalancedTensorProduct.lift_tmul]
        simp [← hL, mul_smul]
      | add _ _ hx hy => rw [smul_add, _root_.map_add, hx, hy, _root_.map_add, smul_add] }

private theorem splitLift_tmul (a : A) (x : P) :
    splitLift p j hL hR P (ModuleCat.restrictScalarsAddEquiv p
      (ModuleCat.of A (BalancedExtension p P)) (tmul p a x)) = j a • x := by
  dsimp only [splitLift, LinearMap.coe_mk, AddHom.coe_mk]
  rw [AddEquiv.symm_apply_apply, tmul_def, BalancedTensorProduct.lift_tmul]; simp

end SplitLift

private theorem tmul_splitLift_self {p : E →+* A} {j : A →+ E} (hpj : ∀ a, p (j a) = a)
    {hL : ∀ e a, e * j a = j (p e * a)} {hR : ∀ a e, j a * e = j (a * p e)} {P : ModuleCat.{v} E}
    (q : (ModuleCat.restrictScalars p).obj (ModuleCat.of A (BalancedExtension p P))) :
    tmul p 1 (splitLift p j hL hR P q) =
      (ModuleCat.restrictScalarsAddEquiv p (ModuleCat.of A (BalancedExtension p P))).symm q := by
  obtain ⟨q, rfl⟩ := (ModuleCat.restrictScalarsAddEquiv p _).surjective q
  simp only [AddEquiv.symm_apply_apply]
  induction q using induction_on with
  | tmul a x => rw [splitLift_tmul, tmul_smul, one_mul, hpj]
  | add _ _ hx hy => rw [_root_.map_add, _root_.map_add, tmul_add, hx, hy]

private theorem tmul_splitLift_eq_zero {p : E →+* A} {j : A →+ E} (p' : E →+* B)
    (horth : ∀ a, p' (j a) = 0) {hL : ∀ e a, e * j a = j (p e * a)}
    {hR : ∀ a e, j a * e = j (a * p e)} {P : ModuleCat.{v} E}
    (q : (ModuleCat.restrictScalars p).obj (ModuleCat.of A (BalancedExtension p P))) :
    tmul p' 1 (splitLift p j hL hR P q) = 0 := by
  obtain ⟨q, rfl⟩ := (ModuleCat.restrictScalarsAddEquiv p _).surjective q
  induction q using induction_on with
  | tmul a x => rw [splitLift_tmul, tmul_smul, one_mul, horth, zero_tmul]
  | add _ _ hx hy => rw [_root_.map_add, _root_.map_add, tmul_add, hx, hy, add_zero]

end Split

section Prod

variable (R : Type u₁) (S : Type u₂) [Ring R] [Ring S]

/-- **Coordinate decomposition of a module over a product ring `R × S`.** Any `(R × S)`-module `P`
is canonically isomorphic to the product of its extensions of scalars along `RingHom.fst R S` and
`RingHom.snd R S` (viewed back as `(R × S)`-modules by restriction of scalars). -/
noncomputable def prodModuleLinearEquiv (P : ModuleCat.{v} (R × S)) :
    P ≃ₗ[R × S]
      ((ModuleCat.restrictScalars (RingHom.fst R S)).obj
        (ModuleCat.of R (BalancedExtension (RingHom.fst R S) P))) ×
      ((ModuleCat.restrictScalars (RingHom.snd R S)).obj
        (ModuleCat.of S (BalancedExtension (RingHom.snd R S) P))) :=
  LinearEquiv.ofLinearMap
    ((splitInclude (RingHom.fst R S) P).prod (splitInclude (RingHom.snd R S) P))
    ((splitLift (RingHom.fst R S) (AddMonoidHom.inl R S)
        (fun e a ↦ by rw [RingHom.coe_fst]; exact AddMonoidHom.mul_inl e a)
        (fun a e ↦ by rw [RingHom.coe_fst]; exact AddMonoidHom.inl_mul a e) P).coprod
      (splitLift (RingHom.snd R S) (AddMonoidHom.inr R S)
        (fun e b ↦ by rw [RingHom.coe_snd]; exact AddMonoidHom.mul_inr e b)
        (fun b e ↦ by rw [RingHom.coe_snd]; exact AddMonoidHom.inr_mul b e) P))
    (LinearMap.ext fun ⟨q₁, q₂⟩ ↦ Prod.ext
      ((ModuleCat.restrictScalarsAddEquiv (RingHom.fst R S) _).symm.injective <| by
        simp [splitInclude, tmul_add,
          tmul_splitLift_self (p := RingHom.fst R S) (j := AddMonoidHom.inl R S) (by simp),
          tmul_splitLift_eq_zero (j := AddMonoidHom.inr R S) (RingHom.fst R S) (by simp)])
      ((ModuleCat.restrictScalarsAddEquiv (RingHom.snd R S) _).symm.injective <| by
        simp [splitInclude, tmul_add,
          tmul_splitLift_self (p := RingHom.snd R S) (j := AddMonoidHom.inr R S) (by simp),
          tmul_splitLift_eq_zero (j := AddMonoidHom.inl R S) (RingHom.snd R S) (by simp)]))
    (LinearMap.ext fun p ↦ by
      simp only [LinearMap.coprod_comp_prod, LinearMap.add_apply, LinearMap.comp_apply,
        splitInclude, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.id_apply]
      rw [splitLift_tmul, splitLift_tmul, AddMonoidHom.inl_apply, AddMonoidHom.inr_apply,
        ← add_smul, show ((1, 0) : R × S) + (0, 1) = 1 from Prod.ext (add_zero 1) (zero_add 1),
        one_smul])

@[simp] theorem prodModuleLinearEquiv_apply (P : ModuleCat.{v} (R × S)) (p : P) :
    prodModuleLinearEquiv R S P p =
      (ModuleCat.restrictScalarsAddEquiv (RingHom.fst R S)
          (ModuleCat.of R (BalancedExtension (RingHom.fst R S) P)) (tmul (RingHom.fst R S) 1 p),
        ModuleCat.restrictScalarsAddEquiv (RingHom.snd R S)
          (ModuleCat.of S (BalancedExtension (RingHom.snd R S) P)) (tmul (RingHom.snd R S) 1 p)) :=
  (rfl)

@[simp] theorem prodModuleLinearEquiv_symm_tmul (P : ModuleCat.{v} (R × S)) (r : R) (p₁ : P)
    (s : S) (p₂ : P) :
    (prodModuleLinearEquiv R S P).symm
        (ModuleCat.restrictScalarsAddEquiv (RingHom.fst R S)
          (ModuleCat.of R (BalancedExtension (RingHom.fst R S) P)) (tmul (RingHom.fst R S) r p₁),
        ModuleCat.restrictScalarsAddEquiv (RingHom.snd R S)
          (ModuleCat.of S (BalancedExtension (RingHom.snd R S) P)) (tmul (RingHom.snd R S) s p₂)) =
      (r, (0 : S)) • p₁ + ((0 : R), s) • p₂ := by
  simp only [prodModuleLinearEquiv, LinearEquiv.symm_ofLinearMap, LinearEquiv.coe_ofLinearMap,
    LinearMap.coprod_apply]
  rw [splitLift_tmul, splitLift_tmul, AddMonoidHom.inl_apply, AddMonoidHom.inr_apply]

end Prod

end TauCeti.BalancedExtension
