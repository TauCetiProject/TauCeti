/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

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

* `ModuleCat.restrictScalarsAddEquiv`: the additive equivalence
  `M ≃+ (ModuleCat.restrictScalars f).obj M` transporting elements across the shared carrier.
* `TauCeti.BalancedExtension.functor f`: the functor `ModuleCat R ⥤ ModuleCat S`.
* `TauCeti.BalancedExtension.adjunction f`: extension of scalars is left adjoint to
  restriction of scalars.
* `TauCeti.BalancedExtension.functorCongr`, `TauCeti.BalancedExtension.functorId`,
  `TauCeti.BalancedExtension.functorComp`, `TauCeti.BalancedExtension.functorCompIso`, and
  `TauCeti.BalancedExtension.functorRingEquivIso`: congruence, identity, composition,
  commutative-square, and ring-equivalence natural isomorphisms for `BalancedExtension.functor`.
* `TauCeti.BalancedExtension.extendScalarsIso f`: for commutative rings, the identification with
  `ModuleCat.extendScalars f`.
* `TauCeti.BalancedExtension.restrictScalarsSelfEquiv`,
  `TauCeti.BalancedExtension.subsingleton_restrictScalars_of_orth`, and
  `TauCeti.BalancedExtension.prodModuleLinearEquiv`: split-surjection recovery, orthogonal
  vanishing, and coordinate decomposition of `(R × S)`-modules.

## References

* C. A. Weibel, *The K-book*, Chapter I, §2, pp. 7–8, and Chapter II, §2.8, pp. 12–13.
-/

public section

namespace ModuleCat

universe u₁ u₂ v

variable {R : Type u₁} {S : Type u₂} [Ring R] [Ring S] (f : R →+* S)

/-- Restriction of scalars along `f : R →+* S` preserves the underlying additive group of an
`S`-module `M`: this additive equivalence transports elements between `M` and
`(ModuleCat.restrictScalars f).obj M`. -/
@[expose]
def restrictScalarsAddEquiv (M : ModuleCat.{v} S) : M ≃+ (restrictScalars.{v} f).obj M where
  toFun m := m
  invFun m := m
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

theorem restrictScalarsAddEquiv_smul (M : ModuleCat.{v} S) (r : R) (m : M) :
    r • restrictScalarsAddEquiv f M m = restrictScalarsAddEquiv f M (f r • m) := (rfl)

theorem restrictScalarsAddEquiv_symm_smul (M : ModuleCat.{v} S) (r : R)
    (x : (restrictScalars.{v} f).obj M) :
    (restrictScalarsAddEquiv f M).symm (r • x) = f r • (restrictScalarsAddEquiv f M).symm x := (rfl)

theorem restrictScalarsAddEquiv_symm_map_apply {M N : ModuleCat.{v} S} (g : M ⟶ N)
    (x : (restrictScalars.{v} f).obj M) :
    (restrictScalarsAddEquiv f N).symm ((restrictScalars f).map g x) =
      g ((restrictScalarsAddEquiv f M).symm x) := (rfl)

end ModuleCat

namespace TauCeti.BalancedExtension

open CategoryTheory

universe u₁ u₂ u₃ u₄ v

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
  refine functor_hom_ext g fun x ↦ ?_
  induction x using induction_on with
  | tmul s m =>
    have htmul : tmul g 1 (tmul f s m) = g s • tmul g 1 (tmul f 1 m) :=
      (congrArg (tmul g 1) (tmul_eq_smul_one_tmul s m)).trans <|
        (tmul_smul 1 s _).trans <| (congrArg (tmul g · _) (one_mul (g s))).trans <|
          tmul_eq_smul_one_tmul (g s) _
    exact ((congrArg φ htmul).trans (φ.hom.map_smul (g s) _)).trans <|
      (congrArg (g s • ·) (h m)).trans ((congrArg ψ htmul).trans (ψ.hom.map_smul (g s) _)).symm
  | add x y hx hy =>
    exact (congrArg φ (tmul_add 1 x y)).trans <| (_root_.map_add φ.hom _ _).trans <|
      (congrArg₂ (· + ·) hx hy).trans <|
        (_root_.map_add ψ.hom _ _).symm.trans (congrArg ψ (tmul_add 1 x y).symm)

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

theorem functorCongr_trans {f₁ f₂ f₃ : R →+* S} (h₁₂ : f₁ = f₂) (h₂₃ : f₂ = f₃) :
    functorCongr.{u₁, u₂, v} h₁₂ ≪≫ functorCongr h₂₃ = functorCongr (h₁₂.trans h₂₃) := by
  subst h₁₂; subst h₂₃; exact Iso.refl_trans _

end Basic

/-- **Extension of scalars along the identity ring homomorphism** is naturally isomorphic to the
identity functor, sending `r ⊗ m` to `r • m` (`TauCeti.BalancedExtension.lid`). -/
noncomputable def functorId (R : Type u₁) [Ring R] :
    functor.{u₁, u₁, max v u₁} (RingHom.id R) ≅ 𝟭 (ModuleCat.{max v u₁} R) :=
  NatIso.ofComponents (fun M ↦ ((lid R M).toModuleIso :
      (functor (RingHom.id R)).obj M ≅ (𝟭 (ModuleCat R)).obj M)) fun {_ Y} φ ↦
    functor_hom_ext (RingHom.id R) fun m ↦
      (congrArg (lid R Y) (map_tmul φ.hom 1 m)).trans <|
        (lid_tmul 1 (φ m)).trans <| (one_smul R (φ m)).trans <|
          congrArg φ ((lid_tmul 1 m).trans (one_smul R m)).symm

theorem functorId_hom_app_tmul (R : Type u₁) [Ring R] (M : ModuleCat.{max v u₁} R) (r : R) (m : M) :
    (functorId R).hom.app M (tmul (RingHom.id R) r m) = r • m := lid_tmul r m

theorem functorId_inv_app_apply (R : Type u₁) [Ring R] (M : ModuleCat.{max v u₁} R) (m : M) :
    (functorId R).inv.app M m = tmul (RingHom.id R) 1 m := lid_symm_apply m

@[simp] theorem functorId_hom_app_hom (R : Type u₁) [Ring R] (M : ModuleCat.{max v u₁} R) :
    ((functorId R).hom.app M).hom = (lid R M).toLinearMap := (rfl)

@[simp] theorem functorId_inv_app_hom (R : Type u₁) [Ring R] (M : ModuleCat.{max v u₁} R) :
    ((functorId R).inv.app M).hom = (lid R M).symm.toLinearMap := (rfl)

section Comp

variable {R : Type u₁} {S : Type u₂} {T : Type u₃} [Ring R] [Ring S] [Ring T]

/-- **Extension of scalars along a composite ring homomorphism** `g ∘ f` is naturally isomorphic
to extending along `f` and then along `g`, sending `t ⊗ m` to `t ⊗ (1 ⊗ m)` with inverse
`t ⊗ (s ⊗ m) ↦ (t * g s) ⊗ m` (`TauCeti.BalancedExtension.cancelBaseChange`). -/
noncomputable def functorComp (f : R →+* S) (g : S →+* T) :
    functor.{u₁, u₃, max v u₂} (g.comp f) ≅
      functor.{u₁, u₂, max v u₂} f ⋙ functor.{u₂, u₃, max v u₂} g :=
  NatIso.ofComponents (fun M ↦ ((cancelBaseChange f g (P := M)).symm.toModuleIso :
      (functor (g.comp f)).obj M ≅ (functor f ⋙ functor g).obj M)) fun {_ _} φ ↦
    functor_hom_ext (g.comp f) fun m ↦
      (congrArg (cancelBaseChange f g).symm (map_tmul φ.hom 1 m)).trans <|
        (cancelBaseChange_symm_tmul f g 1 (φ m)).trans <|
          (congrArg (tmul g 1) (map_tmul φ.hom 1 m).symm).trans <|
            (map_tmul (map f φ.hom) 1 (tmul f 1 m)).symm.trans <|
              congrArg (map g (map f φ.hom)) (cancelBaseChange_symm_tmul f g 1 m).symm

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

end Comp

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
      (Functor.associator _ _ _).inv :=
  NatTrans.ext <| funext fun M ↦ functor_hom_ext (f₃₄.comp (f₂₃.comp f₁₂)) fun m ↦
    let α := (functorComp.{u₁, u₂, u₃, max v u₂ u₃} f₁₂ f₂₃).hom.app M
    (congrArg ((functor f₃₄).map α)
        (functorComp_hom_app_tmul.{u₁, u₃, u₄, max v u₂ u₃} (f₂₃.comp f₁₂) f₃₄ M 1 m)).trans <|
      (functor_map_tmul f₃₄ α 1 _).trans <|
        (congrArg (tmul f₃₄ 1)
          (functorComp_hom_app_tmul.{u₁, u₂, u₃, max v u₂ u₃} f₁₂ f₂₃ M 1 m)).trans <|
          (functorComp_hom_app_tmul.{u₂, u₃, u₄, max v u₂ u₃} f₂₃ f₃₄
            ((functor f₁₂).obj M) 1 (tmul f₁₂ 1 m)).symm.trans <|
            congrArg ((functorComp.{u₂, u₃, u₄, max v u₂ u₃} f₂₃ f₃₄).hom.app
              ((functor f₁₂).obj M))
              (functorComp_hom_app_tmul.{u₁, u₂, u₄, max v u₂ u₃} f₁₂ (f₃₄.comp f₂₃) M 1 m).symm

/-- **Left-unit coherence** for `TauCeti.BalancedExtension.functorId` and
`TauCeti.BalancedExtension.functorComp`. -/
@[reassoc] theorem functorComp_id_comp {R : Type u₁} {S : Type u₂} [Ring R] [Ring S] (f : R →+* S) :
    (functorComp.{u₁, u₁, u₂, max v u₁} (RingHom.id R) f).hom ≫
      Functor.whiskerRight (functorId.{u₁, max v u₁} R).hom (functor.{u₁, u₂, max v u₁} f) ≫
      (Functor.leftUnitor (functor.{u₁, u₂, max v u₁} f)).hom = 𝟙 _ :=
  NatTrans.ext <| funext fun M ↦ functor_hom_ext (f.comp (RingHom.id R)) fun m ↦
    (congrArg ((functor f).map ((functorId R).hom.app M))
        (functorComp_hom_app_tmul.{u₁, u₁, u₂, max v u₁} (RingHom.id R) f M 1 m)).trans <|
      (functor_map_tmul f ((functorId R).hom.app M) 1 _).trans <|
        congrArg (tmul f 1) ((functorId_hom_app_tmul R M 1 m).trans (one_smul R m))

/-- **Right-unit coherence** for `TauCeti.BalancedExtension.functorId` and
`TauCeti.BalancedExtension.functorComp`. -/
@[reassoc] theorem functorComp_comp_id {R : Type u₁} {S : Type u₂} [Ring R] [Ring S] (f : R →+* S) :
    (functorComp.{u₁, u₂, u₂, max v u₂} f (RingHom.id S)).hom ≫
      Functor.whiskerLeft (functor.{u₁, u₂, max v u₂} f) (functorId.{u₂, max v u₂} S).hom ≫
      (Functor.rightUnitor (functor.{u₁, u₂, max v u₂} f)).hom = 𝟙 _ :=
  NatTrans.ext <| funext fun M ↦ functor_hom_ext ((RingHom.id S).comp f) fun m ↦
    (congrArg ((functorId S).hom.app ((functor f).obj M))
        (functorComp_hom_app_tmul.{u₁, u₂, u₂, max v u₂} f (RingHom.id S) M 1 m)).trans <|
      (functorId_hom_app_tmul S ((functor f).obj M) 1 (tmul f 1 m)).trans
        (one_smul S (tmul f 1 m))

section Square

variable {A : Type u₁} {B : Type u₂} {C : Type u₃} {D : Type u₄}
  [Ring A] [Ring B] [Ring C] [Ring D]

/-- **Coherence of balanced extension of scalars across a commutative square.** Given
`g₁.comp f₁ = g₂.comp f₂`, the two composite extension-of-scalars functors are naturally
isomorphic by `d ⊗ (b ⊗ m) ↦ (d * g₁ b) ⊗ (1 ⊗ m)`. -/
noncomputable def functorCompIso (f₁ : A →+* B) (g₁ : B →+* D) (f₂ : A →+* C) (g₂ : C →+* D)
    (h : g₁.comp f₁ = g₂.comp f₂) :
    functor.{u₁, u₂, max v u₂ u₃} f₁ ⋙ functor.{u₂, u₄, max v u₂ u₃} g₁ ≅
      functor.{u₁, u₃, max v u₂ u₃} f₂ ⋙ functor.{u₃, u₄, max v u₂ u₃} g₂ :=
  (functorComp.{u₁, u₂, u₄, max v u₂ u₃} f₁ g₁).symm ≪≫
    functorCongr.{u₁, u₄, max v u₂ u₃} h ≪≫
    functorComp.{u₁, u₃, u₄, max v u₂ u₃} f₂ g₂

theorem functorCompIso_def (f₁ : A →+* B) (g₁ : B →+* D) (f₂ : A →+* C) (g₂ : C →+* D)
    (h : g₁.comp f₁ = g₂.comp f₂) :
    functorCompIso.{u₁, u₂, u₃, u₄, v} f₁ g₁ f₂ g₂ h =
      (functorComp.{u₁, u₂, u₄, max v u₂ u₃} f₁ g₁).symm ≪≫
        functorCongr.{u₁, u₄, max v u₂ u₃} h ≪≫
        functorComp.{u₁, u₃, u₄, max v u₂ u₃} f₂ g₂ := (rfl)

theorem functorCompIso_hom_app_tmul_tmul (f₁ : A →+* B) (g₁ : B →+* D) (f₂ : A →+* C) (g₂ : C →+* D)
    (h : g₁.comp f₁ = g₂.comp f₂) (M : ModuleCat.{max v u₂ u₃} A) (d : D) (b : B) (m : M) :
    (functorCompIso f₁ g₁ f₂ g₂ h).hom.app M (tmul g₁ d (tmul f₁ b m)) =
      tmul g₂ (d * g₁ b) (tmul f₂ 1 m) :=
  (congrArg ((functorComp.{u₁, u₃, u₄, max v u₂ u₃} f₂ g₂).hom.app M)
    (congrArg ((functorCongr.{u₁, u₄, max v u₂ u₃} h).hom.app M)
      (functorComp_inv_app_tmul_tmul.{u₁, u₂, u₄, max v u₂ u₃} f₁ g₁ M d b m))).trans <|
    (congrArg ((functorComp.{u₁, u₃, u₄, max v u₂ u₃} f₂ g₂).hom.app M)
      (functorCongr_hom_app_tmul.{u₁, u₄, max v u₂ u₃} h M (d * g₁ b) m)).trans <|
      functorComp_hom_app_tmul.{u₁, u₃, u₄, max v u₂ u₃} f₂ g₂ M (d * g₁ b) m

theorem functorCompIso_inv_app_tmul_tmul (f₁ : A →+* B) (g₁ : B →+* D) (f₂ : A →+* C) (g₂ : C →+* D)
    (h : g₁.comp f₁ = g₂.comp f₂) (M : ModuleCat.{max v u₂ u₃} A) (d : D) (c : C) (m : M) :
    (functorCompIso f₁ g₁ f₂ g₂ h).inv.app M (tmul g₂ d (tmul f₂ c m)) =
      tmul g₁ (d * g₂ c) (tmul f₁ 1 m) :=
  (congrArg ((functorComp.{u₁, u₂, u₄, max v u₂ u₃} f₁ g₁).hom.app M)
    (congrArg ((functorCongr.{u₁, u₄, max v u₂ u₃} h).inv.app M)
      (functorComp_inv_app_tmul_tmul.{u₁, u₃, u₄, max v u₂ u₃} f₂ g₂ M d c m))).trans <|
    (congrArg ((functorComp.{u₁, u₂, u₄, max v u₂ u₃} f₁ g₁).hom.app M)
      (functorCongr_inv_app_tmul.{u₁, u₄, max v u₂ u₃} h M (d * g₂ c) m)).trans <|
      functorComp_hom_app_tmul.{u₁, u₂, u₄, max v u₂ u₃} f₁ g₁ M (d * g₂ c) m

@[simp] theorem functorCompIso_self (f : A →+* B) (g : B →+* D) :
    functorCompIso.{u₁, u₂, u₂, u₄, v} f g f g rfl =
      Iso.refl (functor.{u₁, u₂, max v u₂} f ⋙ functor.{u₂, u₄, max v u₂} g) := by
  simp [functorCompIso_def]

@[simp] theorem functorCompIso_symm (f₁ : A →+* B) (g₁ : B →+* D) (f₂ : A →+* C) (g₂ : C →+* D)
    (h : g₁.comp f₁ = g₂.comp f₂) :
    (functorCompIso.{u₁, u₂, u₃, u₄, v} f₁ g₁ f₂ g₂ h).symm =
      functorCompIso f₂ g₂ f₁ g₁ h.symm := by simp [functorCompIso_def]

end Square

/-- Pasting two commutative squares with a shared diagonal composes their coherence isomorphisms. -/
theorem functorCompIso_trans {A B₁ B₂ B₃ D : Type u₁} [Ring A] [Ring B₁] [Ring B₂] [Ring B₃]
    [Ring D] (f₁ : A →+* B₁) (g₁ : B₁ →+* D) (f₂ : A →+* B₂) (g₂ : B₂ →+* D)
    (f₃ : A →+* B₃) (g₃ : B₃ →+* D)
    (h₁₂ : g₁.comp f₁ = g₂.comp f₂) (h₂₃ : g₂.comp f₂ = g₃.comp f₃) :
    functorCompIso.{u₁, u₁, u₁, u₁, v} f₁ g₁ f₂ g₂ h₁₂ ≪≫
        functorCompIso.{u₁, u₁, u₁, u₁, v} f₂ g₂ f₃ g₃ h₂₃ =
      functorCompIso.{u₁, u₁, u₁, u₁, v} f₁ g₁ f₃ g₃ (h₁₂.trans h₂₃) := by
  simp only [functorCompIso_def, Iso.trans_assoc, Iso.self_symm_id_assoc]
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

private theorem restrictScalarsAddEquiv_symm_adjunction_unit_apply (f : R →+* S)
    (M : ModuleCat.{max v u₂} R) (m : M) :
    (ModuleCat.restrictScalarsAddEquiv f ((functor f).obj M)).symm
        ((adjunction f).unit.app M m) = tmul f 1 m :=
  adjunction_unit_app_apply f M m

private theorem restrictScalarsEquivalence_symm_unit_apply (e : R ≃+* S) (M : ModuleCat.{v} R)
    (m : M) :
    (ModuleCat.restrictScalarsAddEquiv (e : R →+* S)
        ((ModuleCat.restrictScalars (e.symm : S →+* R)).obj M)).symm
      ((ModuleCat.restrictScalarsEquivalenceOfRingEquiv e).symm.toAdjunction.unit.app M m) =
      ModuleCat.restrictScalarsAddEquiv (e.symm : S →+* R) M m := (rfl)

@[simp] theorem functorRingEquivIso_hom_app_tmul (e : R ≃+* S) (M : ModuleCat.{max v u₂} R)
    (s : S) (m : M) :
    (functorRingEquivIso e).hom.app M (tmul (e : R →+* S) s m) =
      ModuleCat.restrictScalarsAddEquiv (e.symm : S →+* R) M (e.symm s • m) := by
  have h1 : (functorRingEquivIso e).hom.app M (tmul (e : R →+* S) 1 m) =
      ModuleCat.restrictScalarsAddEquiv (e.symm : S →+* R) M m := by
    let adj₂ : ModuleCat.restrictScalars.{max v u₂} (e.symm : S →+* R) ⊣
        ModuleCat.restrictScalars.{max v u₂} (e : R →+* S) :=
      (ModuleCat.restrictScalarsEquivalenceOfRingEquiv e).symm.toAdjunction
    let tr := (ModuleCat.restrictScalarsAddEquiv (e : R →+* S)
      ((ModuleCat.restrictScalars (e.symm : S →+* R)).obj M)).symm
    have h := ConcreteCategory.congr_hom
      (Adjunction.unit_leftAdjointUniq_hom_app (adjunction (e : R →+* S)) adj₂ M) m
    have hlhs : tr (((adjunction (e : R →+* S)).unit.app M ≫
        (ModuleCat.restrictScalars (e : R →+* S)).map ((functorRingEquivIso e).hom.app M)) m) =
        (functorRingEquivIso e).hom.app M (tmul (e : R →+* S) 1 m) :=
      (congrArg tr (ConcreteCategory.comp_apply _ _ m)).trans <|
        (ModuleCat.restrictScalarsAddEquiv_symm_map_apply (e : R →+* S)
          ((functorRingEquivIso e).hom.app M) ((adjunction (e : R →+* S)).unit.app M m)).trans
          (congrArg ((functorRingEquivIso e).hom.app M)
            (restrictScalarsAddEquiv_symm_adjunction_unit_apply (e : R →+* S) M m))
    exact hlhs.symm.trans
      ((congrArg tr h).trans (restrictScalarsEquivalence_symm_unit_apply e M m))
  exact (congrArg ((functorRingEquivIso e).hom.app M) (tmul_eq_smul_one_tmul s m)).trans <|
    (((functorRingEquivIso e).hom.app M).hom.map_smul s (tmul (e : R →+* S) 1 m)).trans <|
      (congrArg (s • ·) h1).trans
        (ModuleCat.restrictScalarsAddEquiv_smul (e.symm : S →+* R) M s m)

@[simp] theorem functorRingEquivIso_inv_app_apply (e : R ≃+* S) (M : ModuleCat.{max v u₂} R)
    (m : (ModuleCat.restrictScalars (e.symm : S →+* R)).obj M) :
    (functorRingEquivIso e).inv.app M m =
      tmul (e : R →+* S) 1
        ((ModuleCat.restrictScalarsAddEquiv (e.symm : S →+* R) M).symm m) := by
  let m₀ : M := (ModuleCat.restrictScalarsAddEquiv (e.symm : S →+* R) M).symm m
  have h : (functorRingEquivIso e).hom.app M (tmul (e : R →+* S) 1 m₀) = m :=
    (functorRingEquivIso_hom_app_tmul e M 1 m₀).trans <|
      (congrArg (ModuleCat.restrictScalarsAddEquiv (e.symm : S →+* R) M)
        ((congrArg (· • m₀) (map_one e.symm)).trans (one_smul R m₀))).trans
        (AddEquiv.apply_symm_apply _ m)
  exact (congrArg _ h.symm).trans
    (ModuleCat.inv_hom_apply ((functorRingEquivIso e).app M) (tmul (e : R →+* S) 1 m₀))

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

section SplitAndProd

section Split

variable {E : Type u₁} {A : Type u₂} {B : Type u₃} [Ring E] [Ring A] [Ring B]

/-- Along a ring homomorphism `p : E →+* A` admitting an additive right inverse `j : A →+ E`
(`p (j a) = a`), extending scalars along `p` after restricting scalars along `p` recovers `M` via
`a ⊗ x ↦ a • x` with inverse `m ↦ 1 ⊗ m`. -/
noncomputable def restrictScalarsSelfEquiv (p : E →+* A) (j : A →+ E) (hpj : ∀ a, p (j a) = a)
    (M : ModuleCat.{v} A) :
    BalancedExtension p ((ModuleCat.restrictScalars.{v} p).obj M) ≃ₗ[A] M :=
  LinearEquiv.ofLinearMap
    (lift
      { toAddHom := (ModuleCat.restrictScalarsAddEquiv p M).symm.toAddHom
        map_smul' := ModuleCat.restrictScalarsAddEquiv_symm_smul p M })
    { toFun m := tmul p 1 (ModuleCat.restrictScalarsAddEquiv p M m)
      map_add' _ _ := by rw [_root_.map_add, tmul_add]
      map_smul' a m := by
        conv_lhs =>
          rw [← hpj a, ← ModuleCat.restrictScalarsAddEquiv_smul, tmul_smul, one_mul, hpj]
        simp [smul_tmul] }
    (by ext m; simp) (hom_ext fun x ↦ by simp)

@[simp] theorem restrictScalarsSelfEquiv_tmul (p : E →+* A) (j : A →+ E) (hpj : ∀ a, p (j a) = a)
    (M : ModuleCat.{v} A) (a : A) (x : (ModuleCat.restrictScalars.{v} p).obj M) :
    restrictScalarsSelfEquiv p j hpj M (tmul p a x) =
      a • (ModuleCat.restrictScalarsAddEquiv p M).symm x :=
  lift_tmul _ a x

@[simp] theorem restrictScalarsSelfEquiv_symm_apply (p : E →+* A) (j : A →+ E)
    (hpj : ∀ a, p (j a) = a) (M : ModuleCat.{v} A) (m : M) :
    (restrictScalarsSelfEquiv p j hpj M).symm m =
      tmul p 1 (ModuleCat.restrictScalarsAddEquiv p M m) := (rfl)

/-- If `p : E →+* A` and `p' : E →+* B` admit an element `e : E` with `p e = 1` and `p' e = 0`,
then extending along `p` any `B`-module restricted along `p'` yields a subsingleton module. -/
theorem subsingleton_restrictScalars_of_orth (p : E →+* A) (p' : E →+* B) (e : E)
    (hp : p e = 1) (hp' : p' e = 0) (N : ModuleCat.{v} B) :
    Subsingleton (BalancedExtension p ((ModuleCat.restrictScalars.{v} p').obj N)) := by
  have hzero : ∀ z : BalancedExtension p ((ModuleCat.restrictScalars.{v} p').obj N), z = 0 := by
    intro z; induction z using induction_on with
    | tmul a n =>
      have hsmul : e • n = 0 := (ModuleCat.restrictScalarsAddEquiv p' N).symm.injective
        (by rw [ModuleCat.restrictScalarsAddEquiv_symm_smul, hp', zero_smul, map_zero])
      have h := tmul_smul (f := p) a e n
      rwa [hp, mul_one, hsmul, tmul_zero, eq_comm] at h
    | add x y hx hy => rw [hx, hy, add_zero]
  exact ⟨fun x y ↦ (hzero x).trans (hzero y).symm⟩

private noncomputable def splitInclude (p : E →+* A) (P : ModuleCat.{v} E) :
    P →ₗ[E] (ModuleCat.restrictScalars p).obj (ModuleCat.of A (BalancedExtension p P)) where
  toFun x := ModuleCat.restrictScalarsAddEquiv p (ModuleCat.of A (BalancedExtension p P))
    (tmul p 1 x)
  map_add' _ _ := by rw [tmul_add, _root_.map_add]
  map_smul' _ _ := by
    rw [tmul_smul, one_mul, RingHom.id_apply, ModuleCat.restrictScalarsAddEquiv_smul, smul_tmul,
      mul_one]

private theorem splitInclude_apply (p : E →+* A) (P : ModuleCat.{v} E) (x : P) :
    splitInclude p P x =
      ModuleCat.restrictScalarsAddEquiv p (ModuleCat.of A (BalancedExtension p P)) (tmul p 1 x) :=
  (rfl)

private def splitLiftAux (p : E →+* A) (j : A →+ E) (hmul_right : ∀ a e, j a * e = j (a * p e))
    (P : Type v) [AddCommGroup P] [Module E P] : BalancedExtension p P →+ P :=
  (BalancedTensorProduct.lift
    (LinearMap.mk₂ ℤ (fun a x ↦ j ((Scalars.of p).symm a) • x)
      (fun _ _ _ ↦ by rw [_root_.map_add, _root_.map_add, add_smul])
      (fun _ _ _ ↦ by rw [map_zsmul, map_zsmul, smul_assoc])
      (fun _ _ _ ↦ smul_add _ _ _) (fun _ _ _ ↦ smul_comm _ _ _))
    fun e a x ↦ by
      obtain ⟨a, rfl⟩ := (Scalars.of p).surjective a
      simp only [LinearMap.mk₂_apply, Scalars.op_smul_of, AddEquiv.symm_apply_apply, ← mul_smul,
        hmul_right]).toAddMonoidHom

private theorem splitLiftAux_tmul (p : E →+* A) (j : A →+ E)
    (hmul_right : ∀ a e, j a * e = j (a * p e)) (P : Type v) [AddCommGroup P] [Module E P]
    (a : A) (x : P) : splitLiftAux p j hmul_right P (tmul p a x) = j a • x := by
  rw [splitLiftAux, tmul_def, LinearMap.toAddMonoidHom_coe, BalancedTensorProduct.lift_tmul]; simp

private noncomputable def splitLift (p : E →+* A) (j : A →+ E)
    (hmul_left : ∀ e a, e * j a = j (p e * a)) (hmul_right : ∀ a e, j a * e = j (a * p e))
    (P : ModuleCat.{v} E) :
    (ModuleCat.restrictScalars p).obj (ModuleCat.of A (BalancedExtension p P)) →ₗ[E] P where
  toFun q := splitLiftAux p j hmul_right P
    ((ModuleCat.restrictScalarsAddEquiv p (ModuleCat.of A (BalancedExtension p P))).symm q)
  map_add' _ _ := by rw [_root_.map_add, _root_.map_add]
  map_smul' e q := by
    rw [ModuleCat.restrictScalarsAddEquiv_symm_smul, RingHom.id_apply]
    suffices ∀ z : BalancedExtension p P,
        splitLiftAux p j hmul_right P (p e • z) = e • splitLiftAux p j hmul_right P z from this _
    intro z; induction z using induction_on with
    | tmul a x => simp only [smul_tmul, splitLiftAux_tmul, ← hmul_left, mul_smul]
    | add x y hx hy => rw [smul_add, _root_.map_add, hx, hy, _root_.map_add, smul_add]

private theorem splitLift_tmul (p : E →+* A) (j : A →+ E)
    (hmul_left : ∀ e a, e * j a = j (p e * a)) (hmul_right : ∀ a e, j a * e = j (a * p e))
    (P : ModuleCat.{v} E) (a : A) (x : P) :
    splitLift p j hmul_left hmul_right P
      (ModuleCat.restrictScalarsAddEquiv p (ModuleCat.of A (BalancedExtension p P))
        (tmul p a x)) = j a • x :=
  splitLiftAux_tmul p j hmul_right P a x

private theorem tmul_splitLift_self (p : E →+* A) (j : A →+ E) (hpj : ∀ a, p (j a) = a)
    (hmul_left : ∀ e a, e * j a = j (p e * a)) (hmul_right : ∀ a e, j a * e = j (a * p e))
    (P : ModuleCat.{v} E)
    (q : (ModuleCat.restrictScalars p).obj (ModuleCat.of A (BalancedExtension p P))) :
    tmul p 1 (splitLift p j hmul_left hmul_right P q) =
      (ModuleCat.restrictScalarsAddEquiv p (ModuleCat.of A (BalancedExtension p P))).symm q := by
  obtain ⟨q, rfl⟩ :=
    (ModuleCat.restrictScalarsAddEquiv p (ModuleCat.of A (BalancedExtension p P))).surjective q
  simp only [AddEquiv.symm_apply_apply]
  induction q using induction_on with
  | tmul a x => rw [splitLift_tmul, tmul_smul, one_mul, hpj]
  | add x y hx hy => rw [_root_.map_add, _root_.map_add, tmul_add, hx, hy]

private theorem tmul_splitLift_orth (p : E →+* A) (p' : E →+* B) (j : A →+ E)
    (horth : ∀ a, p' (j a) = 0) (hmul_left : ∀ e a, e * j a = j (p e * a))
    (hmul_right : ∀ a e, j a * e = j (a * p e)) (P : ModuleCat.{v} E)
    (q : (ModuleCat.restrictScalars p).obj (ModuleCat.of A (BalancedExtension p P))) :
    tmul p' 1 (splitLift p j hmul_left hmul_right P q) = 0 := by
  obtain ⟨q, rfl⟩ :=
    (ModuleCat.restrictScalarsAddEquiv p (ModuleCat.of A (BalancedExtension p P))).surjective q
  induction q using induction_on with
  | tmul a x => rw [splitLift_tmul, tmul_smul, one_mul, horth, zero_tmul]
  | add x y hx hy => rw [_root_.map_add, _root_.map_add, tmul_add, hx, hy, add_zero]

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
    ((splitLift (RingHom.fst R S) (AddMonoidHom.inl R S) AddMonoidHom.mul_inl AddMonoidHom.inl_mul
        P).coprod
      (splitLift (RingHom.snd R S) (AddMonoidHom.inr R S) AddMonoidHom.mul_inr
        AddMonoidHom.inr_mul P))
    (LinearMap.ext fun ⟨q₁, q₂⟩ ↦ Prod.ext
      ((ModuleCat.restrictScalarsAddEquiv (RingHom.fst R S) _).symm.injective <| by
        simp [splitInclude_apply, tmul_add,
          tmul_splitLift_self (RingHom.fst R S) (AddMonoidHom.inl R S) (by simp)
            AddMonoidHom.mul_inl AddMonoidHom.inl_mul P q₁,
          tmul_splitLift_orth (RingHom.snd R S) (RingHom.fst R S) (AddMonoidHom.inr R S) (by simp)
            AddMonoidHom.mul_inr AddMonoidHom.inr_mul P q₂])
      ((ModuleCat.restrictScalarsAddEquiv (RingHom.snd R S) _).symm.injective <| by
        simp [splitInclude_apply, tmul_add,
          tmul_splitLift_orth (RingHom.fst R S) (RingHom.snd R S) (AddMonoidHom.inl R S) (by simp)
            AddMonoidHom.mul_inl AddMonoidHom.inl_mul P q₁,
          tmul_splitLift_self (RingHom.snd R S) (AddMonoidHom.inr R S) (by simp)
            AddMonoidHom.mul_inr AddMonoidHom.inr_mul P q₂]))
    (LinearMap.ext fun p ↦ by
      simp only [LinearMap.coprod_comp_prod, LinearMap.add_apply, LinearMap.comp_apply,
        splitInclude_apply, LinearMap.id_apply]
      refine (congrArg₂ (· + ·) (splitLift_tmul _ _ _ _ P 1 p)
        (splitLift_tmul _ _ _ _ P 1 p)).trans ?_
      have h1 : ((1, (0 : S)) : R × S) + (0, 1) = 1 := by ext <;> simp
      rw [AddMonoidHom.inl_apply, AddMonoidHom.inr_apply, ← add_smul, h1, one_smul])

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
  refine (congrArg₂ (· + ·)
    (splitLift_tmul (RingHom.fst R S) (AddMonoidHom.inl R S) AddMonoidHom.mul_inl
      AddMonoidHom.inl_mul P r p₁)
    (splitLift_tmul (RingHom.snd R S) (AddMonoidHom.inr R S) AddMonoidHom.mul_inr
      AddMonoidHom.inr_mul P s p₂)).trans ?_
  rw [AddMonoidHom.inl_apply, AddMonoidHom.inr_apply]

end Prod

end SplitAndProd

end TauCeti.BalancedExtension
