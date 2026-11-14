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
* `TauCeti.BalancedExtension.functorCongr`, `TauCeti.BalancedExtension.functorId`,
  `TauCeti.BalancedExtension.functorComp`, and `TauCeti.BalancedExtension.functorCompIso`:
  congruence, identity, composition, and commutative-square coherence natural isomorphisms for
  `TauCeti.BalancedExtension.functor`, with pure-tensor formulas and unit/pentagon laws.
* `TauCeti.BalancedExtension.functorRingEquivIso`: along a ring isomorphism `e : R ≃+* S`,
  extension of scalars along `e` is naturally isomorphic to restriction of scalars along `e.symm`.
* `TauCeti.BalancedExtension.extendScalarsIso f`: for commutative rings, the identification with
  `ModuleCat.extendScalars f`.

## References

* C. A. Weibel, *The K-book*, Chapter I, §2, pp. 7–8, and Chapter II, §2.8, pp. 12–13.
-/

public section

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

/-- Morphisms out of `(functor f).obj M` agree once they agree on the pure tensors `1 ⊗ m`. -/
theorem functor_hom_ext {R : Type u₁} {S : Type u₂} [Ring R] [Ring S] (f : R →+* S)
    {M : ModuleCat.{v} R} {N : ModuleCat.{max v u₂} S} {φ ψ : (functor f).obj M ⟶ N}
    (h : ∀ m : M, φ (tmul f 1 m) = ψ (tmul f 1 m)) : φ = ψ :=
  ModuleCat.hom_ext (hom_ext h)

/-- Morphisms out of `(functor f ⋙ functor g).obj M` agree once they agree on the iterated pure
tensors `1 ⊗ (1 ⊗ m)`. -/
theorem functor_comp_hom_ext {R : Type u₁} {S : Type u₂} {T : Type u₃} [Ring R] [Ring S] [Ring T]
    (f : R →+* S) (g : S →+* T) {M : ModuleCat.{v} R} {N : ModuleCat.{max v u₂ u₃} T}
    {φ ψ : (functor f ⋙ functor g).obj M ⟶ N}
    (h : ∀ m : M, φ (tmul g 1 (tmul f 1 m)) = ψ (tmul g 1 (tmul f 1 m))) : φ = ψ := by
  refine functor_hom_ext g fun x ↦ ?_
  induction x using induction_on with
  | tmul s m =>
    have htmul : tmul g 1 (tmul f s m) = g s • tmul g 1 (tmul f 1 m) :=
      (congrArg (tmul g 1) (tmul_eq_smul_one_tmul s m)).trans
        ((tmul_smul 1 s _).trans ((congrArg (tmul g · _) (one_mul (g s))).trans
          (tmul_eq_smul_one_tmul (g s) _)))
    have hφ : φ (tmul g 1 (tmul f s m)) = g s • φ (tmul g 1 (tmul f 1 m)) :=
      (congrArg φ htmul).trans (φ.hom.map_smul (g s) _)
    have hψ : ψ (tmul g 1 (tmul f s m)) = g s • ψ (tmul g 1 (tmul f 1 m)) :=
      (congrArg ψ htmul).trans (ψ.hom.map_smul (g s) _)
    exact hφ.trans ((congrArg (g s • ·) (h m)).trans hψ.symm)
  | add x y hx hy =>
    exact (congrArg φ (tmul_add 1 x y)).trans
      ((_root_.map_add φ.hom _ _).trans
        ((congrArg₂ (· + ·) hx hy).trans
          ((_root_.map_add ψ.hom _ _).symm.trans (congrArg ψ (tmul_add 1 x y).symm))))

private def includeRightOfEq {R : Type u₁} {S : Type u₂} [Ring R] [Ring S]
    {f₁ f₂ : R →+* S} (h : f₁ = f₂) (P : Type v) [AddCommGroup P] [Module R P] :
    P →ₛₗ[f₁] BalancedExtension f₂ P where
  toFun p := tmul f₂ 1 p
  map_add' := tmul_add 1
  map_smul' r p := by simp only [h, tmul_smul, one_mul, smul_tmul, mul_one]

private def congrRingHomLinearEquiv {R : Type u₁} {S : Type u₂} [Ring R] [Ring S]
    {f₁ f₂ : R →+* S} (h : f₁ = f₂) (P : Type v) [AddCommGroup P] [Module R P] :
    BalancedExtension f₁ P ≃ₗ[S] BalancedExtension f₂ P :=
  LinearEquiv.ofLinearMap (lift (includeRightOfEq h P)) (lift (includeRightOfEq h.symm P))
    (hom_ext fun p ↦ by simp [includeRightOfEq])
    (hom_ext fun p ↦ by simp [includeRightOfEq])

/-- Equal ring homomorphisms induce naturally isomorphic balanced extension-of-scalars functors,
sending `s ⊗ m` to `s ⊗ m`. -/
noncomputable def functorCongr {R : Type u₁} {S : Type u₂} [Ring R] [Ring S]
    {f₁ f₂ : R →+* S} (h : f₁ = f₂) :
    functor.{u₁, u₂, v} f₁ ≅ functor.{u₁, u₂, v} f₂ :=
  NatIso.ofComponents (fun M ↦ ((congrRingHomLinearEquiv h M).toModuleIso :
      (functor f₁).obj M ≅ (functor f₂).obj M)) (by
    intro X Y φ
    refine functor_hom_ext f₁ fun m ↦ ?_
    exact (congrArg (lift (includeRightOfEq h Y)) (map_tmul φ.hom 1 m)).trans <|
      (lift_tmul (includeRightOfEq h Y) 1 (φ m)).trans <|
        (one_smul S (tmul f₂ 1 (φ m))).trans <|
          (map_tmul φ.hom 1 m).symm.trans <|
            congrArg (map f₂ φ.hom)
              ((lift_tmul (includeRightOfEq h X) 1 m).trans (one_smul S (tmul f₂ 1 m))).symm)

@[simp]
theorem functorCongr_hom_app_tmul {R : Type u₁} {S : Type u₂} [Ring R] [Ring S]
    {f₁ f₂ : R →+* S} (h : f₁ = f₂) (M : ModuleCat.{v} R) (s : S) (m : M) :
    (functorCongr h).hom.app M (tmul f₁ s m) = tmul f₂ s m :=
  (lift_tmul (includeRightOfEq h M) s m).trans
    ((smul_tmul s 1 m).trans (congrArg (tmul f₂ · m) (mul_one s)))

@[simp]
theorem functorCongr_inv_app_tmul {R : Type u₁} {S : Type u₂} [Ring R] [Ring S]
    {f₁ f₂ : R →+* S} (h : f₁ = f₂) (M : ModuleCat.{v} R) (s : S) (m : M) :
    (functorCongr h).inv.app M (tmul f₂ s m) = tmul f₁ s m :=
  (lift_tmul (includeRightOfEq h.symm M) s m).trans
    ((smul_tmul s 1 m).trans (congrArg (tmul f₁ · m) (mul_one s)))

@[simp]
theorem functorCongr_refl {R : Type u₁} {S : Type u₂} [Ring R] [Ring S] (f : R →+* S) :
    functorCongr (rfl : f = f) = Iso.refl (functor.{u₁, u₂, v} f) := by
  apply Iso.ext
  apply NatTrans.ext
  funext M
  exact functor_hom_ext f fun m ↦ functorCongr_hom_app_tmul rfl M 1 m

@[simp]
theorem functorCongr_symm {R : Type u₁} {S : Type u₂} [Ring R] [Ring S]
    {f₁ f₂ : R →+* S} (h : f₁ = f₂) :
    (functorCongr.{u₁, u₂, v} h).symm = functorCongr h.symm := by
  apply Iso.ext
  apply NatTrans.ext
  funext M
  exact functor_hom_ext f₂ fun m ↦
    (functorCongr_inv_app_tmul h M 1 m).trans (functorCongr_hom_app_tmul h.symm M 1 m).symm

theorem functorCongr_trans {R : Type u₁} {S : Type u₂} [Ring R] [Ring S]
    {f₁ f₂ f₃ : R →+* S} (h₁₂ : f₁ = f₂) (h₂₃ : f₂ = f₃) :
    functorCongr.{u₁, u₂, v} h₁₂ ≪≫ functorCongr h₂₃ = functorCongr (h₁₂.trans h₂₃) := by
  apply Iso.ext
  apply NatTrans.ext
  funext M
  exact functor_hom_ext f₁ fun m ↦
    (congrArg ((functorCongr h₂₃).hom.app M) (functorCongr_hom_app_tmul h₁₂ M 1 m)).trans <|
      (functorCongr_hom_app_tmul h₂₃ M 1 m).trans <|
        (functorCongr_hom_app_tmul (h₁₂.trans h₂₃) M 1 m).symm

/-- **Extension of scalars along the identity ring homomorphism** is naturally isomorphic to the
identity functor, sending `r ⊗ m` to `r • m` (`TauCeti.BalancedExtension.lid`). -/
noncomputable def functorId (R : Type u₁) [Ring R] :
    functor.{u₁, u₁, max v u₁} (RingHom.id R) ≅ 𝟭 (ModuleCat.{max v u₁} R) :=
  NatIso.ofComponents (fun M ↦ ((lid R M).toModuleIso :
      (functor (RingHom.id R)).obj M ≅ (𝟭 (ModuleCat R)).obj M)) (by
    intro X Y φ
    refine functor_hom_ext (RingHom.id R) fun m ↦ ?_
    exact (congrArg (lid R Y) (map_tmul φ.hom 1 m)).trans <|
      (lid_tmul 1 (φ m)).trans <|
        (one_smul R (φ m)).trans <|
          congrArg φ ((lid_tmul 1 m).trans (one_smul R m)).symm)

theorem functorId_hom_app_tmul (R : Type u₁) [Ring R] (M : ModuleCat.{max v u₁} R)
    (r : R) (m : M) :
    (functorId R).hom.app M (tmul (RingHom.id R) r m) = r • m :=
  lid_tmul r m

theorem functorId_inv_app_apply (R : Type u₁) [Ring R] (M : ModuleCat.{max v u₁} R) (m : M) :
    (functorId R).inv.app M m = tmul (RingHom.id R) 1 m :=
  lid_symm_apply m

@[simp]
theorem functorId_hom_app_hom (R : Type u₁) [Ring R] (M : ModuleCat.{max v u₁} R) :
    ((functorId R).hom.app M).hom = (lid R M).toLinearMap :=
  (rfl)

@[simp]
theorem functorId_inv_app_hom (R : Type u₁) [Ring R] (M : ModuleCat.{max v u₁} R) :
    ((functorId R).inv.app M).hom = (lid R M).symm.toLinearMap :=
  (rfl)

/-- **Extension of scalars along a composite ring homomorphism** `g ∘ f` is naturally isomorphic
to extending along `f` and then along `g`, sending `t ⊗ m` to `t ⊗ (1 ⊗ m)` with inverse
`t ⊗ (s ⊗ m) ↦ (t * g s) ⊗ m` (`TauCeti.BalancedExtension.cancelBaseChange`). -/
noncomputable def functorComp {R : Type u₁} {S : Type u₂} {T : Type u₃}
    [Ring R] [Ring S] [Ring T] (f : R →+* S) (g : S →+* T) :
    functor.{u₁, u₃, max v u₂} (g.comp f) ≅
      functor.{u₁, u₂, max v u₂} f ⋙ functor.{u₂, u₃, max v u₂} g :=
  NatIso.ofComponents (fun M ↦ ((cancelBaseChange f g (P := M)).symm.toModuleIso :
      (functor (g.comp f)).obj M ≅ (functor f ⋙ functor g).obj M)) (by
    intro X Y φ
    refine functor_hom_ext (g.comp f) fun m ↦ ?_
    exact (congrArg (cancelBaseChange f g).symm (map_tmul φ.hom 1 m)).trans <|
      (cancelBaseChange_symm_tmul f g 1 (φ m)).trans <|
        (congrArg (tmul g 1) (map_tmul φ.hom 1 m).symm).trans <|
          (map_tmul (map f φ.hom) 1 (tmul f 1 m)).symm.trans <|
            congrArg (map g (map f φ.hom)) (cancelBaseChange_symm_tmul f g 1 m).symm)

theorem functorComp_hom_app_tmul {R : Type u₁} {S : Type u₂} {T : Type u₃}
    [Ring R] [Ring S] [Ring T] (f : R →+* S) (g : S →+* T)
    (M : ModuleCat.{max v u₂} R) (t : T) (m : M) :
    (functorComp f g).hom.app M (tmul (g.comp f) t m) = tmul g t (tmul f 1 m) :=
  cancelBaseChange_symm_tmul f g t m

theorem functorComp_inv_app_tmul_tmul {R : Type u₁} {S : Type u₂} {T : Type u₃}
    [Ring R] [Ring S] [Ring T] (f : R →+* S) (g : S →+* T)
    (M : ModuleCat.{max v u₂} R) (t : T) (s : S) (m : M) :
    (functorComp f g).inv.app M (tmul g t (tmul f s m)) = tmul (g.comp f) (t * g s) m :=
  cancelBaseChange_tmul f g t s m

@[simp]
theorem functorComp_hom_app_hom {R : Type u₁} {S : Type u₂} {T : Type u₃}
    [Ring R] [Ring S] [Ring T] (f : R →+* S) (g : S →+* T)
    (M : ModuleCat.{max v u₂} R) :
    ((functorComp f g).hom.app M).hom = (cancelBaseChange f g).symm.toLinearMap :=
  (rfl)

@[simp]
theorem functorComp_inv_app_hom {R : Type u₁} {S : Type u₂} {T : Type u₃}
    [Ring R] [Ring S] [Ring T] (f : R →+* S) (g : S →+* T)
    (M : ModuleCat.{max v u₂} R) :
    ((functorComp f g).inv.app M).hom = (cancelBaseChange f g).toLinearMap :=
  (rfl)

/-- **Pentagon coherence** for `TauCeti.BalancedExtension.functorComp` along three composable ring
homomorphisms. -/
@[reassoc]
theorem functorComp_assoc {R₁ : Type u₁} {R₂ : Type u₂} {R₃ : Type u₃} {R₄ : Type u₄}
    [Ring R₁] [Ring R₂] [Ring R₃] [Ring R₄]
    (f₁₂ : R₁ →+* R₂) (f₂₃ : R₂ →+* R₃) (f₃₄ : R₃ →+* R₄) :
    (functorComp.{u₁, u₃, u₄, max v u₂ u₃} (f₂₃.comp f₁₂) f₃₄).hom ≫
      Functor.whiskerRight (functorComp.{u₁, u₂, u₃, max v u₂ u₃} f₁₂ f₂₃).hom
        (functor.{u₃, u₄, max v u₂ u₃} f₃₄) =
    (functorComp.{u₁, u₂, u₄, max v u₂ u₃} f₁₂ (f₃₄.comp f₂₃)).hom ≫
      Functor.whiskerLeft (functor.{u₁, u₂, max v u₂ u₃} f₁₂)
        (functorComp.{u₂, u₃, u₄, max v u₂ u₃} f₂₃ f₃₄).hom ≫
      (Functor.associator _ _ _).inv := by
  apply NatTrans.ext
  funext M
  refine functor_hom_ext (f₃₄.comp (f₂₃.comp f₁₂)) fun m ↦ ?_
  exact (congrArg ((functor f₃₄).map ((functorComp.{u₁, u₂, u₃, max v u₂ u₃} f₁₂ f₂₃).hom.app M))
      (functorComp_hom_app_tmul.{u₁, u₃, u₄, max v u₂ u₃} (f₂₃.comp f₁₂) f₃₄ M 1 m)).trans <|
    (functor_map_tmul f₃₄ ((functorComp.{u₁, u₂, u₃, max v u₂ u₃} f₁₂ f₂₃).hom.app M) 1 _).trans <|
      (congrArg (tmul f₃₄ 1)
        (functorComp_hom_app_tmul.{u₁, u₂, u₃, max v u₂ u₃} f₁₂ f₂₃ M 1 m)).trans <|
        (functorComp_hom_app_tmul.{u₂, u₃, u₄, max v u₂ u₃} f₂₃ f₃₄
          ((functor f₁₂).obj M) 1 (tmul f₁₂ 1 m)).symm.trans <|
          congrArg ((functorComp.{u₂, u₃, u₄, max v u₂ u₃} f₂₃ f₃₄).hom.app ((functor f₁₂).obj M))
            (functorComp_hom_app_tmul.{u₁, u₂, u₄, max v u₂ u₃} f₁₂ (f₃₄.comp f₂₃) M 1 m).symm

/-- **Left-unit coherence** for `TauCeti.BalancedExtension.functorId` and
`TauCeti.BalancedExtension.functorComp`. -/
@[reassoc]
theorem functorComp_id_comp {R : Type u₁} {S : Type u₂} [Ring R] [Ring S] (f : R →+* S) :
    (functorComp.{u₁, u₁, u₂, max v u₁} (RingHom.id R) f).hom ≫
      Functor.whiskerRight (functorId.{u₁, max v u₁} R).hom (functor.{u₁, u₂, max v u₁} f) ≫
      (Functor.leftUnitor (functor.{u₁, u₂, max v u₁} f)).hom = 𝟙 _ := by
  apply NatTrans.ext
  funext M
  refine functor_hom_ext (f.comp (RingHom.id R)) fun m ↦ ?_
  exact (congrArg ((functor f).map ((functorId R).hom.app M))
      (functorComp_hom_app_tmul.{u₁, u₁, u₂, max v u₁} (RingHom.id R) f M 1 m)).trans <|
    (functor_map_tmul f ((functorId R).hom.app M) 1 _).trans <|
      congrArg (tmul f 1) ((functorId_hom_app_tmul R M 1 m).trans (one_smul R m))

/-- **Right-unit coherence** for `TauCeti.BalancedExtension.functorId` and
`TauCeti.BalancedExtension.functorComp`. -/
@[reassoc]
theorem functorComp_comp_id {R : Type u₁} {S : Type u₂} [Ring R] [Ring S] (f : R →+* S) :
    (functorComp.{u₁, u₂, u₂, max v u₂} f (RingHom.id S)).hom ≫
      Functor.whiskerLeft (functor.{u₁, u₂, max v u₂} f) (functorId.{u₂, max v u₂} S).hom ≫
      (Functor.rightUnitor (functor.{u₁, u₂, max v u₂} f)).hom = 𝟙 _ := by
  apply NatTrans.ext
  funext M
  refine functor_hom_ext ((RingHom.id S).comp f) fun m ↦ ?_
  exact (congrArg ((functorId S).hom.app ((functor f).obj M))
      (functorComp_hom_app_tmul.{u₁, u₂, u₂, max v u₂} f (RingHom.id S) M 1 m)).trans <|
    (functorId_hom_app_tmul S ((functor f).obj M) 1 (tmul f 1 m)).trans <|
      one_smul S (tmul f 1 m)

/-- **Coherence of balanced extension of scalars across a commutative square.** Given ring
homomorphisms `f₁ : A →+* B`, `g₁ : B →+* D`, `f₂ : A →+* C`, and `g₂ : C →+* D` with
`g₁.comp f₁ = g₂.comp f₂`, the two composite extension-of-scalars functors are naturally
isomorphic by `d ⊗ (b ⊗ m) ↦ (d * g₁ b) ⊗ (1 ⊗ m)`. -/
noncomputable def functorCompIso {A : Type u₁} {B : Type u₂} {C : Type u₃} {D : Type u₄}
    [Ring A] [Ring B] [Ring C] [Ring D]
    (f₁ : A →+* B) (g₁ : B →+* D) (f₂ : A →+* C) (g₂ : C →+* D)
    (h : g₁.comp f₁ = g₂.comp f₂) :
    functor.{u₁, u₂, max v u₂ u₃} f₁ ⋙ functor.{u₂, u₄, max v u₂ u₃} g₁ ≅
      functor.{u₁, u₃, max v u₂ u₃} f₂ ⋙ functor.{u₃, u₄, max v u₂ u₃} g₂ :=
  (functorComp.{u₁, u₂, u₄, max v u₂ u₃} f₁ g₁).symm ≪≫
    functorCongr.{u₁, u₄, max v u₂ u₃} h ≪≫
    functorComp.{u₁, u₃, u₄, max v u₂ u₃} f₂ g₂

theorem functorCompIso_def {A : Type u₁} {B : Type u₂} {C : Type u₃} {D : Type u₄}
    [Ring A] [Ring B] [Ring C] [Ring D]
    (f₁ : A →+* B) (g₁ : B →+* D) (f₂ : A →+* C) (g₂ : C →+* D)
    (h : g₁.comp f₁ = g₂.comp f₂) :
    functorCompIso.{u₁, u₂, u₃, u₄, v} f₁ g₁ f₂ g₂ h =
      (functorComp.{u₁, u₂, u₄, max v u₂ u₃} f₁ g₁).symm ≪≫
        functorCongr.{u₁, u₄, max v u₂ u₃} h ≪≫
        functorComp.{u₁, u₃, u₄, max v u₂ u₃} f₂ g₂ :=
  (rfl)

theorem functorCompIso_hom_app_tmul_tmul {A : Type u₁} {B : Type u₂} {C : Type u₃} {D : Type u₄}
    [Ring A] [Ring B] [Ring C] [Ring D]
    (f₁ : A →+* B) (g₁ : B →+* D) (f₂ : A →+* C) (g₂ : C →+* D)
    (h : g₁.comp f₁ = g₂.comp f₂) (M : ModuleCat.{max v u₂ u₃} A) (d : D) (b : B) (m : M) :
    (functorCompIso f₁ g₁ f₂ g₂ h).hom.app M (tmul g₁ d (tmul f₁ b m)) =
      tmul g₂ (d * g₁ b) (tmul f₂ 1 m) :=
  (congrArg ((functorComp.{u₁, u₃, u₄, max v u₂ u₃} f₂ g₂).hom.app M)
    (congrArg ((functorCongr.{u₁, u₄, max v u₂ u₃} h).hom.app M)
      (functorComp_inv_app_tmul_tmul.{u₁, u₂, u₄, max v u₂ u₃} f₁ g₁ M d b m))).trans <|
    (congrArg ((functorComp.{u₁, u₃, u₄, max v u₂ u₃} f₂ g₂).hom.app M)
      (functorCongr_hom_app_tmul.{u₁, u₄, max v u₂ u₃} h M (d * g₁ b) m)).trans <|
      functorComp_hom_app_tmul.{u₁, u₃, u₄, max v u₂ u₃} f₂ g₂ M (d * g₁ b) m

theorem functorCompIso_inv_app_tmul_tmul {A : Type u₁} {B : Type u₂} {C : Type u₃} {D : Type u₄}
    [Ring A] [Ring B] [Ring C] [Ring D]
    (f₁ : A →+* B) (g₁ : B →+* D) (f₂ : A →+* C) (g₂ : C →+* D)
    (h : g₁.comp f₁ = g₂.comp f₂) (M : ModuleCat.{max v u₂ u₃} A) (d : D) (c : C) (m : M) :
    (functorCompIso f₁ g₁ f₂ g₂ h).inv.app M (tmul g₂ d (tmul f₂ c m)) =
      tmul g₁ (d * g₂ c) (tmul f₁ 1 m) :=
  (congrArg ((functorComp.{u₁, u₂, u₄, max v u₂ u₃} f₁ g₁).hom.app M)
    (congrArg ((functorCongr.{u₁, u₄, max v u₂ u₃} h).inv.app M)
      (functorComp_inv_app_tmul_tmul.{u₁, u₃, u₄, max v u₂ u₃} f₂ g₂ M d c m))).trans <|
    (congrArg ((functorComp.{u₁, u₂, u₄, max v u₂ u₃} f₁ g₁).hom.app M)
      (functorCongr_inv_app_tmul.{u₁, u₄, max v u₂ u₃} h M (d * g₂ c) m)).trans <|
      functorComp_hom_app_tmul.{u₁, u₂, u₄, max v u₂ u₃} f₁ g₁ M (d * g₂ c) m

@[simp]
theorem functorCompIso_self {A : Type u₁} {B : Type u₂} {D : Type u₄}
    [Ring A] [Ring B] [Ring D] (f : A →+* B) (g : B →+* D) :
    functorCompIso.{u₁, u₂, u₂, u₄, v} f g f g rfl =
      Iso.refl (functor.{u₁, u₂, max v u₂} f ⋙ functor.{u₂, u₄, max v u₂} g) := by
  apply Iso.ext
  apply NatTrans.ext
  funext M
  refine functor_comp_hom_ext f g fun m ↦ ?_
  exact (functorCompIso_hom_app_tmul_tmul f g f g rfl M 1 1 m).trans <|
    congrArg (fun d ↦ tmul g d (tmul f 1 m)) ((congrArg (1 * ·) (map_one g)).trans (mul_one 1))

@[simp]
theorem functorCompIso_symm {A : Type u₁} {B : Type u₂} {C : Type u₃} {D : Type u₄}
    [Ring A] [Ring B] [Ring C] [Ring D]
    (f₁ : A →+* B) (g₁ : B →+* D) (f₂ : A →+* C) (g₂ : C →+* D)
    (h : g₁.comp f₁ = g₂.comp f₂) :
    (functorCompIso.{u₁, u₂, u₃, u₄, v} f₁ g₁ f₂ g₂ h).symm =
      functorCompIso f₂ g₂ f₁ g₁ h.symm := by
  apply Iso.ext
  apply NatTrans.ext
  funext M
  refine functor_comp_hom_ext f₂ g₂ fun m ↦ ?_
  exact (functorCompIso_inv_app_tmul_tmul f₁ g₁ f₂ g₂ h M 1 1 m).trans
    (functorCompIso_hom_app_tmul_tmul f₂ g₂ f₁ g₁ h.symm M 1 1 m).symm

/-- Pasting two commutative squares with a shared diagonal composes their coherence isomorphisms. -/
theorem functorCompIso_trans {A B₁ B₂ B₃ D : Type u₁} [Ring A] [Ring B₁] [Ring B₂] [Ring B₃]
    [Ring D] (f₁ : A →+* B₁) (g₁ : B₁ →+* D) (f₂ : A →+* B₂) (g₂ : B₂ →+* D)
    (f₃ : A →+* B₃) (g₃ : B₃ →+* D)
    (h₁₂ : g₁.comp f₁ = g₂.comp f₂) (h₂₃ : g₂.comp f₂ = g₃.comp f₃) :
    functorCompIso.{u₁, u₁, u₁, u₁, v} f₁ g₁ f₂ g₂ h₁₂ ≪≫
        functorCompIso.{u₁, u₁, u₁, u₁, v} f₂ g₂ f₃ g₃ h₂₃ =
      functorCompIso.{u₁, u₁, u₁, u₁, v} f₁ g₁ f₃ g₃ (h₁₂.trans h₂₃) := by
  apply Iso.ext
  apply NatTrans.ext
  funext M
  refine functor_comp_hom_ext f₁ g₁ fun m ↦ ?_
  exact (congrArg ((functorCompIso f₂ g₂ f₃ g₃ h₂₃).hom.app M)
      (functorCompIso_hom_app_tmul_tmul f₁ g₁ f₂ g₂ h₁₂ M 1 1 m)).trans <|
    (functorCompIso_hom_app_tmul_tmul f₂ g₂ f₃ g₃ h₂₃ M (1 * g₁ 1) 1 m).trans <|
      (congrArg (fun d ↦ tmul g₃ d (tmul f₃ 1 m)) (by simp only [map_one, mul_one])).trans <|
        (functorCompIso_hom_app_tmul_tmul f₁ g₁ f₃ g₃ (h₁₂.trans h₂₃) M 1 1 m).symm

/-- Along a ring isomorphism `e : R ≃+* S`, balanced extension of scalars along `e.toRingHom` is
naturally isomorphic to restriction of scalars along `e.symm`, since both functors are left adjoint
to restriction of scalars along `e.toRingHom`. -/
noncomputable def functorRingEquivIso {R : Type u₁} {S : Type u₂} [Ring R] [Ring S]
    (e : R ≃+* S) :
    functor.{u₁, u₂, max v u₂} e.toRingHom ≅
      ModuleCat.restrictScalars.{max v u₂} e.symm.toRingHom :=
  (adjunction e.toRingHom).leftAdjointUniq
    (ModuleCat.restrictScalarsEquivalenceOfRingEquiv e).symm.toAdjunction

theorem functorRingEquivIso_hom_app_tmul {R : Type u₁} {S : Type u₂} [Ring R] [Ring S]
    (e : R ≃+* S) (M : ModuleCat.{max v u₂} R) (s : S) (m : M) :
    (functorRingEquivIso e).hom.app M (tmul e.toRingHom s m) =
      s • (show (ModuleCat.restrictScalars e.symm.toRingHom).obj M from m) := by
  have h1 : (functorRingEquivIso e).hom.app M (tmul e.toRingHom 1 m) =
      (show (ModuleCat.restrictScalars e.symm.toRingHom).obj M from m) := by
    let adj₂ : ModuleCat.restrictScalars.{max v u₂} e.symm.toRingHom ⊣
        ModuleCat.restrictScalars.{max v u₂} e.toRingHom :=
      (ModuleCat.restrictScalarsEquivalenceOfRingEquiv e).symm.toAdjunction
    have h := congr($(Adjunction.unit_leftAdjointUniq_hom_app (adjunction e.toRingHom) adj₂ M) m)
    have hlhs : ((adjunction e.toRingHom).unit.app M ≫
        (ModuleCat.restrictScalars e.toRingHom).map ((functorRingEquivIso e).hom.app M)) m =
        (functorRingEquivIso e).hom.app M (tmul e.toRingHom 1 m) :=
      (ConcreteCategory.comp_apply _ _ m).trans
        (congrArg ((functorRingEquivIso e).hom.app M) (adjunction_unit_app_apply e.toRingHom M m))
    exact hlhs.symm.trans h
  rw [tmul_eq_smul_one_tmul]
  exact (((functorRingEquivIso e).hom.app M).hom.map_smul s (tmul e.toRingHom 1 m)).trans
    (congrArg (s • ·) h1)

theorem functorRingEquivIso_inv_app_apply {R : Type u₁} {S : Type u₂} [Ring R] [Ring S]
    (e : R ≃+* S) (M : ModuleCat.{max v u₂} R)
    (m : (ModuleCat.restrictScalars e.symm.toRingHom).obj M) :
    (functorRingEquivIso e).inv.app M m = tmul e.toRingHom 1 (show M from m) := by
  have h : (functorRingEquivIso e).hom.app M (tmul e.toRingHom 1 (show M from m)) = m :=
    (functorRingEquivIso_hom_app_tmul e M 1 (show M from m)).trans (one_smul S m)
  exact (congrArg _ h.symm).trans
    (ModuleCat.inv_hom_apply ((functorRingEquivIso e).app M)
      (tmul e.toRingHom 1 (show M from m)))

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

end TauCeti.BalancedExtension
