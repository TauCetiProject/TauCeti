/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicThickeningSystem.CoherentFormalModule
public import TauCeti.AlgebraicGeometry.RelativeSpec.AffineFunctions
public import TauCeti.AlgebraicGeometry.RelativeSpec.BaseChange
import TauCeti.AlgebraicGeometry.Modules.Tensor.Product
import TauCeti.AlgebraicGeometry.RelativeSpec.Equivalence

/-!
# Algebraizing morphisms of affine schemes from formal completions

Let `X` be a scheme and `I` an ideal sheaf on `X`. When the completion functor
`Scheme.formalCompletion.completionFunctor X I`, from finitely presented `𝒪_X`-modules to coherent
formal modules on `X.formalCompletion I`, is full and faithful, compatible systems of algebra
morphisms over the infinitesimal neighbourhoods `V(I ^ (n + 1))` between finitely presented
quasicoherent `𝒪_X`-algebras come from a unique algebra morphism over `X`.

Combined with the anti-equivalence between quasicoherent `𝒪_X`-algebras and affine schemes over
`X` and with base change of relative spectra, this algebraizes morphisms of formal completions
between schemes `Y₁, Y₂` affine over `X` whose coordinate algebras `(p₁)_* 𝒪_{Y₁}` and
`(p₂)_* 𝒪_{Y₂}` are finitely presented `𝒪_X`-modules: every morphism
`Y₁.formalCompletion (I.comap p₁) ⟶ Y₂.formalCompletion (I.comap p₂)` over `X.formalCompletion I`
is induced by a unique morphism `Y₁ ⟶ Y₂` over `X`. Faithfulness of `completionFunctor X I` alone
suffices for uniqueness. Neither flatness nor Noetherian hypotheses are required.

## Main definitions and results

* `AlgebraicGeometry.Scheme.formalCompletion.quasicoherentAlgebra_hom_ext` and
  `AlgebraicGeometry.Scheme.formalCompletion.existsUnique_quasicoherentAlgebra_hom`: uniqueness
  and existence of morphisms between finitely presented quasicoherent algebras from compatible
  families over `V(I ^ (n + 1))`.
* `AlgebraicGeometry.Scheme.formalCompletion.relativeSpecFormalCompletionLevelIso`: the `n`-th
  level of the formal completion of `Spec_X A` along the preimage of `I` is the relative spectrum
  over `V(I ^ (n + 1))` of the restricted algebra.
* `AlgebraicGeometry.Scheme.formalCompletion.hom_ext_of_map_eq`: when `completionFunctor X I` is
  faithful, morphisms over `X` between affine `X`-schemes with finitely presented coordinate
  algebras are determined by the induced morphisms of formal completions.
* `AlgebraicGeometry.Scheme.formalCompletion.existsUnique_hom_of_formalCompletion` and
  `AlgebraicGeometry.Scheme.formalCompletion.liftOfFormalCompletion`: when `completionFunctor X I`
  is full and faithful, every morphism of formal completions over `X.formalCompletion I` between
  such affine `X`-schemes comes from a unique morphism of schemes over `X`.

## References

* [The Stacks Project, Lemma 58.17.1](https://stacks.math.columbia.edu/tag/0EL8), whose proof
  recovers a morphism of finite étale schemes from the corresponding compatible system of algebra
  morphisms over the infinitesimal neighbourhoods of `V(I)`.
-/

public section

open CategoryTheory Limits MonoidalCategory Opposite
open scoped MonObj
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.AdicThickeningSystem

universe u

namespace AlgebraicGeometry.Scheme.formalCompletion

/-- If `f ≫ p₂ = p₁`, the preimage of `K.comap p₂` under `f` is contained in `K.comap p₁`. -/
private lemma comap_le_of_comp {X Y Z : Scheme.{u}} {p₁ : X ⟶ Z} {p₂ : Y ⟶ Z} {f : X ⟶ Y}
    (hf : f ≫ p₂ = p₁) (K : Z.IdealSheafData) : (K.comap p₂).comap f ≤ K.comap p₁ := by
  rw [← IdealSheafData.comap_comp, hf]

/-! ### Algebraizing morphisms of finitely presented quasicoherent algebras -/

section QuasicoherentAlgebra

-- Helper cancellations on plain `Y.Modules` variables: `QuasicoherentAlgebra.pullback_obj_X`
-- relates carriers whose `Category` instances are `Y.Modules` and `SheafOfModules Y.ringCatSheaf`,
-- which agree at default transparency when applied as lemmas without invoking `erw`.
private lemma comp_eqToHom_cancel_mid {Y : Scheme.{u}} {U₁ U₂ U₃ U₄ U₅ U₆ : Y.Modules}
    (e₁ : U₁ = U₂) (f : U₂ ⟶ U₃) (e₂ : U₄ = U₃) (g : U₃ ⟶ U₅) (e₃ : U₆ = U₅) :
    (eqToHom e₁ ≫ f ≫ eqToHom e₂.symm) ≫ (eqToHom e₂ ≫ g ≫ eqToHom e₃.symm) =
      eqToHom e₁ ≫ (f ≫ g) ≫ eqToHom e₃.symm := by
  subst e₁ e₂ e₃
  simp

private lemma eqToHom_conjugate_cancel {Y : Scheme.{u}} {U₁ U₂ V₁ V₂ : Y.Modules}
    (e₂ : V₂ = U₂) (e₁ : V₁ = U₁) {f g : U₂ ⟶ U₁}
    (h : eqToHom e₂ ≫ f ≫ eqToHom e₁.symm = eqToHom e₂ ≫ g ≫ eqToHom e₁.symm) :
    f = g := by
  subst e₁ e₂
  simpa using h

private lemma eqToHom_symm_conjugate_symm {Y : Scheme.{u}} {U₁ U₂ V₁ V₂ : Y.Modules}
    (e₂ : V₂ = U₂) (e₁ : V₁ = U₁) {f : U₂ ⟶ U₁} {g : V₂ ⟶ V₁}
    (h : f = eqToHom e₂.symm ≫ g ≫ eqToHom e₁) :
    g = eqToHom e₂ ≫ f ≫ eqToHom e₁.symm := by
  subst e₁ e₂
  simpa using h.symm

private lemma cancel_unit_pullback {Y : Scheme.{u}} {U₀ U₁ U₂ V₀ V₁ V₂ : Y.Modules}
    (u : U₀ ⟶ V₀) [IsIso u] (a₂ : V₀ ⟶ U₂) (a₁ : V₀ ⟶ U₁)
    (e₂ : V₂ = U₂) (e₁ : V₁ = U₁) (m : U₂ ⟶ U₁)
    (h : (u ≫ a₂ ≫ eqToHom e₂.symm) ≫ (eqToHom e₂ ≫ m ≫ eqToHom e₁.symm) =
      u ≫ a₁ ≫ eqToHom e₁.symm) :
    a₂ ≫ m = a₁ := by
  subst e₁ e₂
  simpa using (cancel_epi u).mp h

private lemma cancel_mul_pullback {Y : Scheme.{u}} {W₁ W₂ U₁ U₂ V₁ V₂ : Y.Modules}
    (d₂ : W₂ ⟶ U₂ ⊗ U₂) [IsIso d₂] (d₁ : W₁ ⟶ U₁ ⊗ U₁) [IsIso d₁]
    (m₂ : W₂ ⟶ U₂) (m₁ : W₁ ⟶ U₁) (e₂ : V₂ = U₂) (e₁ : V₁ = U₁)
    (p : U₂ ⟶ U₁) (p₂ : W₂ ⟶ W₁) (hδ : p₂ ≫ d₁ = d₂ ≫ (p ⊗ₘ p))
    (h : ((eqToHom e₂ ⊗ₘ eqToHom e₂) ≫ inv d₂ ≫ m₂ ≫ eqToHom e₂.symm) ≫
        (eqToHom e₂ ≫ p ≫ eqToHom e₁.symm) =
      ((eqToHom e₂ ≫ p ≫ eqToHom e₁.symm) ⊗ₘ (eqToHom e₂ ≫ p ≫ eqToHom e₁.symm)) ≫
        ((eqToHom e₁ ⊗ₘ eqToHom e₁) ≫ inv d₁ ≫ m₁ ≫ eqToHom e₁.symm)) :
    m₂ ≫ p = p₂ ≫ m₁ := by
  subst e₁ e₂
  simp only [eqToHom_refl, id_tensorHom_id, Category.id_comp, Category.comp_id] at h
  have hδ' : (p ⊗ₘ p) ≫ inv d₁ = inv d₂ ≫ p₂ := by
    rw [IsIso.comp_inv_eq, Category.assoc, hδ, IsIso.inv_hom_id_assoc]
  rw [reassoc_of% hδ'] at h
  exact (cancel_epi (inv d₂)).mp h

private lemma cancel_transition_pullback {Y₁ Y₀ : Scheme.{u}} (G : Y₁.Modules ⥤ Y₀.Modules)
    {U₁ U₂ V₁ V₂ : Y₁.Modules} {W₁ W₂ X₁ X₂ Z₁ Z₂ : Y₀.Modules}
    (eA₂ : V₂ = U₂) (eA₁ : V₁ = U₁) (hA₂ : W₂ = G.obj V₂) (hA₁ : W₁ = G.obj V₁)
    (eB₂ : Z₂ = X₂) (eB₁ : Z₁ = X₁)
    (s₁ : V₂ ⟶ V₁) (s₀ : Z₂ ⟶ Z₁) (t₁ : G.obj U₁ ⟶ X₁) (t₂ : G.obj U₂ ⟶ X₂)
    (h : (eqToHom hA₂ ≫ G.map s₁ ≫ eqToHom hA₁.symm) ≫
        (eqToHom (hA₁.trans (congrArg G.obj eA₁)) ≫ t₁ ≫ eqToHom eB₁.symm) =
      (eqToHom (hA₂.trans (congrArg G.obj eA₂)) ≫ t₂ ≫ eqToHom eB₂.symm) ≫ s₀) :
    G.map (eqToHom eA₂.symm ≫ s₁ ≫ eqToHom eA₁) ≫ t₁ =
      t₂ ≫ (eqToHom eB₂.symm ≫ s₀ ≫ eqToHom eB₁) := by
  subst eA₂ eA₁ hA₂ hA₁ eB₂ eB₁
  simpa using h

variable (X : Scheme.{u}) (I : X.IdealSheafData)

/-- When `completionFunctor X I` is faithful, morphisms between finitely presented `𝒪_X`-modules
are determined by their pullbacks to all infinitesimal neighbourhoods `V(I ^ (n + 1))`. -/
theorem modules_hom_ext_of_completionFunctor_faithful [(completionFunctor X I).Faithful]
    {M N : X.Modules} [M.IsFinitePresentation] [N.IsFinitePresentation] {f g : M ⟶ N}
    (h : ∀ n, (Modules.pullback (toScheme X I n)).map f =
      (Modules.pullback (toScheme X I n)).map g) :
    f = g := by
  have hfg : (ObjectProperty.homMk f : (⟨M, inferInstance⟩ : FinitelyPresentedSheaf X) ⟶
      ⟨N, inferInstance⟩) = ObjectProperty.homMk g :=
    (completionFunctor X I).map_injective (CoherentFormalModule.hom_ext h)
  exact congrArg (fun k ↦ k.hom) hfg

/-- For a quasicoherent algebra `A` on `X`, the pullback along `V(I ^ (n + 1)) ⟶ V(I ^ (n + 2))`
of its restriction to `V(I ^ (n + 2))` is canonically its restriction to `V(I ^ (n + 1))`. -/
noncomputable def algebraTransitionIso (A : QuasicoherentAlgebra X) (n : ℕ) :
    (QuasicoherentAlgebra.pullback ((X.formalCompletion I).ι n)).obj
        ((QuasicoherentAlgebra.pullback (toScheme X I (n + 1))).obj A) ≅
      (QuasicoherentAlgebra.pullback (toScheme X I n)).obj A :=
  (QuasicoherentAlgebra.pullbackComp ((X.formalCompletion I).ι n) (toScheme X I (n + 1)) ≪≫
    QuasicoherentAlgebra.pullbackCongr (ι_toScheme X I n)).app A

/-- On underlying modules, `algebraTransitionIso` is the reduction isomorphism of
`completionFunctor X I`, up to the carrier identifications of `QuasicoherentAlgebra.pullback`. -/
theorem algebraTransitionIso_hom_hom_hom_hom (A : QuasicoherentAlgebra X)
    [A.obj.X.IsFinitePresentation] (n : ℕ) :
    ((algebraTransitionIso X I A n).hom).hom.hom.hom =
      eqToHom ((QuasicoherentAlgebra.pullback_obj_X ((X.formalCompletion I).ι n) _).trans
          (congrArg _ (QuasicoherentAlgebra.pullback_obj_X (toScheme X I (n + 1)) A))) ≫
        (((completionFunctor X I).obj ⟨A.obj.X, inferInstance⟩).transitionIso n).hom ≫
          eqToHom (QuasicoherentAlgebra.pullback_obj_X (toScheme X I n) A).symm :=
  (congrArg₂ (· ≫ ·)
    (QuasicoherentAlgebra.pullbackComp_hom_app_hom_hom_hom
      ((X.formalCompletion I).ι n) (toScheme X I (n + 1)) A)
    (QuasicoherentAlgebra.pullbackCongr_hom_app_hom_hom_hom (ι_toScheme X I n) A)).trans
    (comp_eqToHom_cancel_mid _ _ _ _ (QuasicoherentAlgebra.pullback_obj_X (toScheme X I n) A))

variable {X I}

/-- When `completionFunctor X I` is faithful, morphisms between finitely presented quasicoherent
`𝒪_X`-algebras are determined by their restrictions to all levels `V(I ^ (n + 1))`. -/
theorem quasicoherentAlgebra_hom_ext [(completionFunctor X I).Faithful]
    {A₁ A₂ : QuasicoherentAlgebra X} [A₁.obj.X.IsFinitePresentation]
    [A₂.obj.X.IsFinitePresentation] {Φ₁ Φ₂ : A₂ ⟶ A₁}
    (h : ∀ n, (QuasicoherentAlgebra.pullback (toScheme X I n)).map Φ₁ =
      (QuasicoherentAlgebra.pullback (toScheme X I n)).map Φ₂) :
    Φ₁ = Φ₂ :=
  ObjectProperty.hom_ext _ <| CommMon.hom_ext _ _ <|
    modules_hom_ext_of_completionFunctor_faithful X I (M := A₂.obj.X) (N := A₁.obj.X) fun n ↦
      eqToHom_conjugate_cancel
        (QuasicoherentAlgebra.pullback_obj_X (toScheme X I n) A₂)
        (QuasicoherentAlgebra.pullback_obj_X (toScheme X I n) A₁) <|
        (QuasicoherentAlgebra.pullback_map_hom_hom_hom (toScheme X I n) Φ₁).symm.trans <|
          (congrArg (fun ψ ↦ ψ.hom.hom.hom) (h n)).trans
            (QuasicoherentAlgebra.pullback_map_hom_hom_hom (toScheme X I n) Φ₂)

/-- If `φ : A₂.obj.X ⟶ A₁.obj.X` restricts at every level `V(I ^ (n + 1))` to the underlying map
of an algebra morphism `ψ n`, and `completionFunctor X I` is faithful, then `φ` preserves units
and multiplications. -/
private lemma isMonHom_of_pullback_eq [(completionFunctor X I).Faithful]
    {A₁ A₂ : QuasicoherentAlgebra X} [A₁.obj.X.IsFinitePresentation]
    [A₂.obj.X.IsFinitePresentation] (φ : A₂.obj.X ⟶ A₁.obj.X)
    (ψ : ∀ n, (QuasicoherentAlgebra.pullback (toScheme X I n)).obj A₂ ⟶
      (QuasicoherentAlgebra.pullback (toScheme X I n)).obj A₁)
    (hφ : ∀ n, (ψ n).hom.hom.hom =
      eqToHom (QuasicoherentAlgebra.pullback_obj_X (toScheme X I n) A₂) ≫
        (Modules.pullback (toScheme X I n)).map φ ≫
          eqToHom (QuasicoherentAlgebra.pullback_obj_X (toScheme X I n) A₁).symm) :
    IsMonHom φ where
  one_hom := modules_hom_ext_of_completionFunctor_faithful X I fun n ↦ by
    let f := toScheme X I n
    rw [Functor.map_comp]
    refine cancel_unit_pullback (Modules.pullbackObjUnitIso f).inv
      ((Modules.pullback f).map η[A₂.obj.X]) ((Modules.pullback f).map η[A₁.obj.X])
      (QuasicoherentAlgebra.pullback_obj_X f A₂) (QuasicoherentAlgebra.pullback_obj_X f A₁)
      ((Modules.pullback f).map φ) ?_
    exact (congrArg₂ (· ≫ ·) (QuasicoherentAlgebra.pullback_obj_one f A₂).symm (hφ n).symm).trans
      ((ψ n).hom.hom.isMonHom_hom.one_hom.trans (QuasicoherentAlgebra.pullback_obj_one f A₁))
  mul_hom := modules_hom_ext_of_completionFunctor_faithful X I fun n ↦ by
    let f := toScheme X I n
    let F := Modules.pullback f
    rw [Functor.map_comp, Functor.map_comp]
    refine cancel_mul_pullback (Functor.OplaxMonoidal.δ F A₂.obj.X A₂.obj.X)
      (Functor.OplaxMonoidal.δ F A₁.obj.X A₁.obj.X) (F.map μ[A₂.obj.X]) (F.map μ[A₁.obj.X])
      (QuasicoherentAlgebra.pullback_obj_X f A₂) (QuasicoherentAlgebra.pullback_obj_X f A₁)
      (F.map φ) (F.map (φ ⊗ₘ φ)) (Functor.OplaxMonoidal.δ_natural F φ φ).symm ?_
    exact (congrArg₂ (· ≫ ·) (QuasicoherentAlgebra.pullback_obj_mul f A₂).symm (hφ n).symm).trans
      ((ψ n).hom.hom.isMonHom_hom.mul_hom.trans
        (congrArg₂ (· ≫ ·) (congrArg₂ (· ⊗ₘ ·) (hφ n) (hφ n))
          (QuasicoherentAlgebra.pullback_obj_mul f A₁)))

/-- When `completionFunctor X I` is full and faithful, every compatible family of algebra maps
over the infinitesimal neighbourhoods `V(I ^ (n + 1))` between finitely presented quasicoherent
`𝒪_X`-algebras comes from a unique morphism of quasicoherent algebras on `X`. -/
theorem existsUnique_quasicoherentAlgebra_hom [(completionFunctor X I).Full]
    [(completionFunctor X I).Faithful] {A₁ A₂ : QuasicoherentAlgebra X}
    [A₁.obj.X.IsFinitePresentation] [A₂.obj.X.IsFinitePresentation]
    (ψ : ∀ n, (QuasicoherentAlgebra.pullback (toScheme X I n)).obj A₂ ⟶
      (QuasicoherentAlgebra.pullback (toScheme X I n)).obj A₁)
    (hψ : ∀ n, (QuasicoherentAlgebra.pullback ((X.formalCompletion I).ι n)).map (ψ (n + 1)) ≫
        (algebraTransitionIso X I A₁ n).hom =
      (algebraTransitionIso X I A₂ n).hom ≫ ψ n) :
    ∃! Φ : A₂ ⟶ A₁, ∀ n, (QuasicoherentAlgebra.pullback (toScheme X I n)).map Φ = ψ n := by
  let M₁ : FinitelyPresentedSheaf X := ⟨A₁.obj.X, inferInstance⟩
  let M₂ : FinitelyPresentedSheaf X := ⟨A₂.obj.X, inferInstance⟩
  let α (n : ℕ) : ((completionFunctor X I).obj M₂).obj n ⟶
      ((completionFunctor X I).obj M₁).obj n :=
    eqToHom (QuasicoherentAlgebra.pullback_obj_X (toScheme X I n) A₂).symm ≫
      (ψ n).hom.hom.hom ≫ eqToHom (QuasicoherentAlgebra.pullback_obj_X (toScheme X I n) A₁)
  have hα (n : ℕ) :
      (Modules.pullback ((X.formalCompletion I).ι n)).map (α (n + 1)) ≫
          (((completionFunctor X I).obj M₁).transitionIso n).hom =
        (((completionFunctor X I).obj M₂).transitionIso n).hom ≫ α n :=
    cancel_transition_pullback (Modules.pullback ((X.formalCompletion I).ι n))
      (QuasicoherentAlgebra.pullback_obj_X (toScheme X I (n + 1)) A₂)
      (QuasicoherentAlgebra.pullback_obj_X (toScheme X I (n + 1)) A₁)
      (QuasicoherentAlgebra.pullback_obj_X ((X.formalCompletion I).ι n) _)
      (QuasicoherentAlgebra.pullback_obj_X ((X.formalCompletion I).ι n) _)
      (QuasicoherentAlgebra.pullback_obj_X (toScheme X I n) A₂)
      (QuasicoherentAlgebra.pullback_obj_X (toScheme X I n) A₁)
      (ψ (n + 1)).hom.hom.hom (ψ n).hom.hom.hom
      (((completionFunctor X I).obj M₁).transitionIso n).hom
      (((completionFunctor X I).obj M₂).transitionIso n).hom <|
      (congrArg₂ (· ≫ ·)
        (QuasicoherentAlgebra.pullback_map_hom_hom_hom
          ((X.formalCompletion I).ι n) (ψ (n + 1))).symm
        (algebraTransitionIso_hom_hom_hom_hom X I A₁ n).symm).trans <|
        (congrArg (fun f ↦ f.hom.hom.hom) (hψ n)).trans
          (congrArg (· ≫ (ψ n).hom.hom.hom) (algebraTransitionIso_hom_hom_hom_hom X I A₂ n))
  let φ : A₂.obj.X ⟶ A₁.obj.X := ((completionFunctor X I).preimage ⟨α, hα⟩).hom
  have hφ (n : ℕ) : (ψ n).hom.hom.hom =
      eqToHom (QuasicoherentAlgebra.pullback_obj_X (toScheme X I n) A₂) ≫
        (Modules.pullback (toScheme X I n)).map φ ≫
          eqToHom (QuasicoherentAlgebra.pullback_obj_X (toScheme X I n) A₁).symm :=
    eqToHom_symm_conjugate_symm
      (QuasicoherentAlgebra.pullback_obj_X (toScheme X I n) A₂)
      (QuasicoherentAlgebra.pullback_obj_X (toScheme X I n) A₁)
      (congrArg (fun f ↦ f.app n) ((completionFunctor X I).map_preimage ⟨α, hα⟩))
  have hmon : IsMonHom φ := isMonHom_of_pullback_eq φ ψ hφ
  let Φ : A₂ ⟶ A₁ := ObjectProperty.homMk (CommMon.homMk (Mon.Hom.mk' φ hmon.one_hom hmon.mul_hom))
  have hΦ (n : ℕ) : (QuasicoherentAlgebra.pullback (toScheme X I n)).map Φ = ψ n :=
    ObjectProperty.hom_ext _ <| CommMon.hom_ext _ _ <|
      (QuasicoherentAlgebra.pullback_map_hom_hom_hom (toScheme X I n) Φ).trans (hφ n).symm
  exact ⟨Φ, hΦ, fun Φ' hΦ' ↦ quasicoherentAlgebra_hom_ext fun n ↦ (hΦ' n).trans (hΦ n).symm⟩

end QuasicoherentAlgebra

/-! ### Formal completions of relative spectra and affine morphisms -/

section RelativeSpec

variable (X : Scheme.{u}) (I : X.IdealSheafData)

/-- The `n`-th level of the formal completion of `Spec_X A` along the preimage of `I` is
canonically the relative spectrum over `V(I ^ (n + 1))` of the restricted algebra: both are
pullbacks of `Spec_X A ⟶ X` along `V(I ^ (n + 1)) ⟶ X`. -/
noncomputable def relativeSpecFormalCompletionLevelIso (A : QuasicoherentAlgebra X) (n : ℕ) :
    (A.obj.relativeSpec.formalCompletion (I.comap A.obj.relativeSpecToBase)).X n ≅
      ((QuasicoherentAlgebra.pullback (toScheme X I n)).obj A).obj.relativeSpec :=
  IsPullback.isoIsPullback _ _
    (isPullback_map_app A.obj.relativeSpecToBase rfl n)
    (isPullback_relativeSpecPullbackFst A (toScheme X I n))

@[reassoc (attr := simp)]
theorem relativeSpecFormalCompletionLevelIso_hom_fst (A : QuasicoherentAlgebra X) (n : ℕ) :
    (relativeSpecFormalCompletionLevelIso X I A n).hom ≫
        relativeSpecPullbackFst A (toScheme X I n) =
      toScheme A.obj.relativeSpec (I.comap A.obj.relativeSpecToBase) n :=
  IsPullback.isoIsPullback_hom_fst _ _ _ _

@[reassoc (attr := simp)]
theorem relativeSpecFormalCompletionLevelIso_hom_snd (A : QuasicoherentAlgebra X) (n : ℕ) :
    (relativeSpecFormalCompletionLevelIso X I A n).hom ≫
        ((QuasicoherentAlgebra.pullback (toScheme X I n)).obj A).obj.relativeSpecToBase =
      (map (I := I.comap A.obj.relativeSpecToBase) A.obj.relativeSpecToBase le_rfl).app n :=
  IsPullback.isoIsPullback_hom_snd _ _ _ _

@[reassoc (attr := simp)]
theorem relativeSpecFormalCompletionLevelIso_inv_fst (A : QuasicoherentAlgebra X) (n : ℕ) :
    (relativeSpecFormalCompletionLevelIso X I A n).inv ≫
        toScheme A.obj.relativeSpec (I.comap A.obj.relativeSpecToBase) n =
      relativeSpecPullbackFst A (toScheme X I n) :=
  IsPullback.isoIsPullback_inv_fst _ _ _ _

@[reassoc (attr := simp)]
theorem relativeSpecFormalCompletionLevelIso_inv_snd (A : QuasicoherentAlgebra X) (n : ℕ) :
    (relativeSpecFormalCompletionLevelIso X I A n).inv ≫
        (map (I := I.comap A.obj.relativeSpecToBase) A.obj.relativeSpecToBase le_rfl).app n =
      ((QuasicoherentAlgebra.pullback (toScheme X I n)).obj A).obj.relativeSpecToBase :=
  IsPullback.isoIsPullback_inv_snd _ _ _ _

variable {X I}

/-- Morphisms of quasicoherent algebras are determined by the induced morphisms of relative
spectra. -/
private lemma quasicoherentAlgebra_hom_ext_of_relativeSpecMap_eq {Y : Scheme.{u}}
    {B₁ B₂ : QuasicoherentAlgebra Y} {α β : B₂ ⟶ B₁}
    (h : CommMon.relativeSpecMap α.hom = CommMon.relativeSpecMap β.hom) : α = β :=
  Quiver.Hom.op_inj <| (relativeSpec Y).map_injective <| MorphismProperty.Over.Hom.ext h

/-- Under `relativeSpecFormalCompletionLevelIso`, the morphism of formal completions induced by
`CommMon.relativeSpecMap Φ.hom` is at level `n` the relative spectrum of the restricted algebra
morphism. -/
private lemma relativeSpecFormalCompletionLevelIso_inv_map_app_hom (I : X.IdealSheafData)
    {A₁ A₂ : QuasicoherentAlgebra X} (Φ : A₂ ⟶ A₁) (n : ℕ) :
    (relativeSpecFormalCompletionLevelIso X I A₁ n).inv ≫
        (map (I := I.comap A₁.obj.relativeSpecToBase) (J := I.comap A₂.obj.relativeSpecToBase)
          (CommMon.relativeSpecMap Φ.hom)
          (comap_le_of_comp (CommMon.relativeSpecMap_relativeSpecToBase Φ.hom) I)).app n ≫
          (relativeSpecFormalCompletionLevelIso X I A₂ n).hom =
      CommMon.relativeSpecMap
        ((QuasicoherentAlgebra.pullback (toScheme X I n)).map Φ).hom := by
  apply (isPullback_relativeSpecPullbackFst A₂ (toScheme X I n)).hom_ext
  · rw [Category.assoc, Category.assoc, relativeSpecFormalCompletionLevelIso_hom_fst,
      map_app_toScheme, relativeSpecFormalCompletionLevelIso_inv_fst_assoc,
      relativeSpecMap_pullback_map_relativeSpecPullbackFst]
  · refine Eq.trans ?_ (CommMon.relativeSpecMap_relativeSpecToBase
      ((QuasicoherentAlgebra.pullback (toScheme X I n)).map Φ).hom).symm
    have hcomp : map (I := I.comap A₁.obj.relativeSpecToBase)
        (J := I.comap A₂.obj.relativeSpecToBase) (CommMon.relativeSpecMap Φ.hom)
          (comap_le_of_comp (CommMon.relativeSpecMap_relativeSpecToBase Φ.hom) I) ≫
        map A₂.obj.relativeSpecToBase le_rfl =
        map A₁.obj.relativeSpecToBase le_rfl :=
      (map_comp _ _ _ _).trans
        (map_congr (CommMon.relativeSpecMap_relativeSpecToBase Φ.hom) _ le_rfl)
    rw [Category.assoc, Category.assoc, relativeSpecFormalCompletionLevelIso_hom_snd,
      ← AdicThickeningSystem.comp_app, hcomp, relativeSpecFormalCompletionLevelIso_inv_snd]

/-- Under `relativeSpecFormalCompletionLevelIso`, the `n`-th transition of the formal completion
of `Spec_X A` corresponds to `algebraTransitionIso` composed with `relativeSpecPullbackFst`. -/
private lemma relativeSpecFormalCompletionLevelIso_transition (A : QuasicoherentAlgebra X)
    (n : ℕ) :
    CommMon.relativeSpecMap ((algebraTransitionIso X I A n).hom).hom ≫
        relativeSpecPullbackFst
          ((QuasicoherentAlgebra.pullback (toScheme X I (n + 1))).obj A)
          ((X.formalCompletion I).ι n) =
      (relativeSpecFormalCompletionLevelIso X I A n).inv ≫
        (A.obj.relativeSpec.formalCompletion (I.comap A.obj.relativeSpecToBase)).ι n ≫
          (relativeSpecFormalCompletionLevelIso X I A (n + 1)).hom := by
  apply (isPullback_relativeSpecPullbackFst A (toScheme X I (n + 1))).hom_ext
  · have hhom : ((algebraTransitionIso X I A n).hom).hom =
        ((QuasicoherentAlgebra.pullbackComp ((X.formalCompletion I).ι n)
            (toScheme X I (n + 1))).hom.app A).hom ≫
          ((QuasicoherentAlgebra.pullbackCongr (ι_toScheme X I n)).hom.app A).hom := rfl
    rw [hhom, CommMon.relativeSpecMap_comp, Category.assoc, Category.assoc,
      ← relativeSpecPullbackFst_comp, relativeSpecPullbackFst_congr,
      Category.assoc, Category.assoc, relativeSpecFormalCompletionLevelIso_hom_fst,
      ι_toScheme, relativeSpecFormalCompletionLevelIso_inv_fst]
  · rw [Category.assoc, relativeSpecPullbackFst_relativeSpecToBase,
      CommMon.relativeSpecMap_relativeSpecToBase_assoc, Category.assoc, Category.assoc,
      relativeSpecFormalCompletionLevelIso_hom_snd, AdicThickeningSystem.Hom.naturality,
      relativeSpecFormalCompletionLevelIso_inv_snd_assoc]

/-- Every morphism over `Y` between relative spectra comes from an opposite morphism of
quasicoherent algebras. -/
private theorem exists_relativeSpecMap_eq {Y : Scheme.{u}} {B₁ B₂ : QuasicoherentAlgebra Y}
    (g : B₁.obj.relativeSpec ⟶ B₂.obj.relativeSpec)
    (hg : g ≫ B₂.obj.relativeSpecToBase = B₁.obj.relativeSpecToBase) :
    ∃ Φ : B₂ ⟶ B₁, CommMon.relativeSpecMap Φ.hom = g :=
  ⟨((relativeSpec Y).preimage (MorphismProperty.Over.homMk g hg)).unop,
    congrArg (fun f ↦ f.left) ((relativeSpec Y).map_preimage (MorphismProperty.Over.homMk g hg))⟩

/-- Uniqueness on relative spectra of finitely presented quasicoherent algebras. -/
private lemma hom_ext_of_map_eq_relativeSpec [(completionFunctor X I).Faithful]
    {A₁ A₂ : QuasicoherentAlgebra X} [A₁.obj.X.IsFinitePresentation]
    [A₂.obj.X.IsFinitePresentation] {g₁ g₂ : A₁.obj.relativeSpec ⟶ A₂.obj.relativeSpec}
    (hg₁ : g₁ ≫ A₂.obj.relativeSpecToBase = A₁.obj.relativeSpecToBase)
    (hg₂ : g₂ ≫ A₂.obj.relativeSpecToBase = A₁.obj.relativeSpecToBase)
    (hmap : map (I := I.comap A₁.obj.relativeSpecToBase)
        (J := I.comap A₂.obj.relativeSpecToBase) g₁ (comap_le_of_comp hg₁ I) =
      map (I := I.comap A₁.obj.relativeSpecToBase)
        (J := I.comap A₂.obj.relativeSpecToBase) g₂ (comap_le_of_comp hg₂ I)) :
    g₁ = g₂ := by
  obtain ⟨Φ₁, hΦ₁⟩ := exists_relativeSpecMap_eq g₁ hg₁
  obtain ⟨Φ₂, hΦ₂⟩ := exists_relativeSpecMap_eq g₂ hg₂
  have hmapΦ :
      map (I := I.comap A₁.obj.relativeSpecToBase) (J := I.comap A₂.obj.relativeSpecToBase)
        (CommMon.relativeSpecMap Φ₁.hom)
          (comap_le_of_comp (CommMon.relativeSpecMap_relativeSpecToBase Φ₁.hom) I) =
      map (I := I.comap A₁.obj.relativeSpecToBase) (J := I.comap A₂.obj.relativeSpecToBase)
        (CommMon.relativeSpecMap Φ₂.hom)
          (comap_le_of_comp (CommMon.relativeSpecMap_relativeSpecToBase Φ₂.hom) I) :=
    (map_congr hΦ₁ _ (comap_le_of_comp hg₁ I)).trans
      (hmap.trans (map_congr hΦ₂.symm (comap_le_of_comp hg₂ I) _))
  have hΦ : Φ₁ = Φ₂ := by
    apply quasicoherentAlgebra_hom_ext (I := I)
    intro n
    apply quasicoherentAlgebra_hom_ext_of_relativeSpecMap_eq
    have happ := congrArg (fun f : A₁.obj.relativeSpec.formalCompletion _ ⟶
        A₂.obj.relativeSpec.formalCompletion _ ↦
      (relativeSpecFormalCompletionLevelIso X I A₁ n).inv ≫ f.app n ≫
        (relativeSpecFormalCompletionLevelIso X I A₂ n).hom) hmapΦ
    exact (relativeSpecFormalCompletionLevelIso_inv_map_app_hom I Φ₁ n).symm.trans
      (happ.trans (relativeSpecFormalCompletionLevelIso_inv_map_app_hom I Φ₂ n))
  exact hΦ₁.symm.trans ((congrArg (fun Φ : A₂ ⟶ A₁ ↦ CommMon.relativeSpecMap Φ.hom) hΦ).trans hΦ₂)

/-- Compatibility of a family of levelwise algebra morphisms `ψ n` with `algebraTransitionIso`
when their induced relative-spectrum maps come from a morphism `a` of formal completions. -/
private lemma pullback_map_comp_algebraTransitionIso {A₁ A₂ : QuasicoherentAlgebra X}
    (a : A₁.obj.relativeSpec.formalCompletion (I.comap A₁.obj.relativeSpecToBase) ⟶
      A₂.obj.relativeSpec.formalCompletion (I.comap A₂.obj.relativeSpecToBase))
    (ha : a ≫ map A₂.obj.relativeSpecToBase le_rfl = map A₁.obj.relativeSpecToBase le_rfl)
    (ψ : ∀ n, (QuasicoherentAlgebra.pullback (toScheme X I n)).obj A₂ ⟶
      (QuasicoherentAlgebra.pullback (toScheme X I n)).obj A₁)
    (hψs : ∀ n, CommMon.relativeSpecMap (ψ n).hom =
      (relativeSpecFormalCompletionLevelIso X I A₁ n).inv ≫ a.app n ≫
        (relativeSpecFormalCompletionLevelIso X I A₂ n).hom)
    (n : ℕ) :
    (QuasicoherentAlgebra.pullback ((X.formalCompletion I).ι n)).map (ψ (n + 1)) ≫
        (algebraTransitionIso X I A₁ n).hom =
      (algebraTransitionIso X I A₂ n).hom ≫ ψ n := by
  let s (k : ℕ) := (relativeSpecFormalCompletionLevelIso X I A₁ k).inv ≫ a.app k ≫
    (relativeSpecFormalCompletionLevelIso X I A₂ k).hom
  have hs : s n ≫
      ((QuasicoherentAlgebra.pullback (toScheme X I n)).obj A₂).obj.relativeSpecToBase =
      ((QuasicoherentAlgebra.pullback (toScheme X I n)).obj A₁).obj.relativeSpecToBase := by
    simp only [s, Category.assoc, relativeSpecFormalCompletionLevelIso_hom_snd,
      ← AdicThickeningSystem.comp_app, ha, relativeSpecFormalCompletionLevelIso_inv_snd]
  apply quasicoherentAlgebra_hom_ext_of_relativeSpecMap_eq
  rw [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.FullSubcategory.comp_hom,
    CommMon.relativeSpecMap_comp, CommMon.relativeSpecMap_comp, hψs]
  apply (isPullback_relativeSpecPullbackFst
    ((QuasicoherentAlgebra.pullback (toScheme X I (n + 1))).obj A₂)
    ((X.formalCompletion I).ι n)).hom_ext
  · calc (CommMon.relativeSpecMap ((algebraTransitionIso X I A₁ n).hom).hom ≫
            CommMon.relativeSpecMap
              ((QuasicoherentAlgebra.pullback ((X.formalCompletion I).ι n)).map
                (ψ (n + 1))).hom) ≫
            relativeSpecPullbackFst _ ((X.formalCompletion I).ι n)
      _ = CommMon.relativeSpecMap ((algebraTransitionIso X I A₁ n).hom).hom ≫
            relativeSpecPullbackFst _ ((X.formalCompletion I).ι n) ≫ s (n + 1) := by
        rw [Category.assoc, relativeSpecMap_pullback_map_relativeSpecPullbackFst, hψs]
      _ = ((relativeSpecFormalCompletionLevelIso X I A₁ n).inv ≫
            (A₁.obj.relativeSpec.formalCompletion _).ι n ≫
              (relativeSpecFormalCompletionLevelIso X I A₁ (n + 1)).hom) ≫ s (n + 1) := by
        rw [← Category.assoc, relativeSpecFormalCompletionLevelIso_transition]
      _ = (relativeSpecFormalCompletionLevelIso X I A₁ n).inv ≫ a.app n ≫
            (A₂.obj.relativeSpec.formalCompletion _).ι n ≫
              (relativeSpecFormalCompletionLevelIso X I A₂ (n + 1)).hom := by
        simp only [s, Category.assoc, Iso.hom_inv_id_assoc,
          AdicThickeningSystem.Hom.naturality_assoc]
      _ = s n ≫ ((relativeSpecFormalCompletionLevelIso X I A₂ n).inv ≫
            (A₂.obj.relativeSpec.formalCompletion _).ι n ≫
              (relativeSpecFormalCompletionLevelIso X I A₂ (n + 1)).hom) := by
        simp only [s, Category.assoc, Iso.hom_inv_id_assoc]
      _ = s n ≫ CommMon.relativeSpecMap ((algebraTransitionIso X I A₂ n).hom).hom ≫
            relativeSpecPullbackFst _ ((X.formalCompletion I).ι n) := by
        rw [← relativeSpecFormalCompletionLevelIso_transition]
      _ = (s n ≫ CommMon.relativeSpecMap ((algebraTransitionIso X I A₂ n).hom).hom) ≫
            relativeSpecPullbackFst _ ((X.formalCompletion I).ι n) :=
        (Category.assoc _ _ _).symm
  · rw [Category.assoc, CommMon.relativeSpecMap_relativeSpecToBase,
      CommMon.relativeSpecMap_relativeSpecToBase, Category.assoc,
      CommMon.relativeSpecMap_relativeSpecToBase, hs]

/-- Algebraization of morphisms between relative spectra of finitely presented quasicoherent
`𝒪_X`-algebras from morphisms of their formal completions over `X.formalCompletion I`. -/
private lemma exists_relativeSpecMap_of_formalCompletion [(completionFunctor X I).Full]
    [(completionFunctor X I).Faithful] {A₁ A₂ : QuasicoherentAlgebra X}
    [A₁.obj.X.IsFinitePresentation] [A₂.obj.X.IsFinitePresentation]
    (a : A₁.obj.relativeSpec.formalCompletion (I.comap A₁.obj.relativeSpecToBase) ⟶
      A₂.obj.relativeSpec.formalCompletion (I.comap A₂.obj.relativeSpecToBase))
    (ha : a ≫ map A₂.obj.relativeSpecToBase le_rfl = map A₁.obj.relativeSpecToBase le_rfl) :
    ∃ Φ : A₂ ⟶ A₁,
      map (I := I.comap A₁.obj.relativeSpecToBase) (J := I.comap A₂.obj.relativeSpecToBase)
        (CommMon.relativeSpecMap Φ.hom)
          (comap_le_of_comp (CommMon.relativeSpecMap_relativeSpecToBase Φ.hom) I) = a := by
  let s (n : ℕ) := (relativeSpecFormalCompletionLevelIso X I A₁ n).inv ≫ a.app n ≫
    (relativeSpecFormalCompletionLevelIso X I A₂ n).hom
  have hs (n : ℕ) : s n ≫
      ((QuasicoherentAlgebra.pullback (toScheme X I n)).obj A₂).obj.relativeSpecToBase =
      ((QuasicoherentAlgebra.pullback (toScheme X I n)).obj A₁).obj.relativeSpecToBase := by
    simp only [s, Category.assoc, relativeSpecFormalCompletionLevelIso_hom_snd,
      ← AdicThickeningSystem.comp_app, ha, relativeSpecFormalCompletionLevelIso_inv_snd]
  choose ψ hψs using fun n ↦ exists_relativeSpecMap_eq (s n) (hs n)
  obtain ⟨Φ, hΦ, -⟩ := existsUnique_quasicoherentAlgebra_hom ψ
    (pullback_map_comp_algebraTransitionIso a ha ψ hψs)
  refine ⟨Φ, AdicThickeningSystem.hom_ext fun n ↦ ?_⟩
  have hn := (relativeSpecFormalCompletionLevelIso_inv_map_app_hom I Φ n).trans
    ((congrArg (fun b ↦ CommMon.relativeSpecMap b.hom) (hΦ n)).trans (hψs n))
  exact (cancel_mono (relativeSpecFormalCompletionLevelIso X I A₂ n).hom).mp
    ((cancel_epi (relativeSpecFormalCompletionLevelIso X I A₁ n).inv).mp hn)

/-- Transport uniqueness of formal-completion lifts across scheme isomorphisms over `X`. -/
private lemma hom_ext_of_iso {Z₁ Z₂ Y₁ Y₂ : Scheme.{u}} {q₁ : Z₁ ⟶ X} {q₂ : Z₂ ⟶ X}
    {p₁ : Y₁ ⟶ X} {p₂ : Y₂ ⟶ X} (u₁ : Z₁ ≅ Y₁) (u₂ : Z₂ ≅ Y₂)
    (hu₁ : u₁.hom ≫ p₁ = q₁) (hu₂ : u₂.hom ≫ p₂ = q₂)
    (hext : ∀ {g₁' g₂' : Z₁ ⟶ Z₂} (hg₁' : g₁' ≫ q₂ = q₁) (hg₂' : g₂' ≫ q₂ = q₁),
      map (I := I.comap q₁) (J := I.comap q₂) g₁' (comap_le_of_comp hg₁' I) =
        map (I := I.comap q₁) (J := I.comap q₂) g₂' (comap_le_of_comp hg₂' I) →
      g₁' = g₂')
    {g₁ g₂ : Y₁ ⟶ Y₂} (hg₁ : g₁ ≫ p₂ = p₁) (hg₂ : g₂ ≫ p₂ = p₁)
    (hmap : map (I := I.comap p₁) (J := I.comap p₂) g₁ (comap_le_of_comp hg₁ I) =
      map (I := I.comap p₁) (J := I.comap p₂) g₂ (comap_le_of_comp hg₂ I)) :
    g₁ = g₂ := by
  have hu₂' : u₂.inv ≫ q₂ = p₂ := by rw [← hu₂, Iso.inv_hom_id_assoc]
  have h₁ : (u₁.hom ≫ g₁ ≫ u₂.inv) ≫ q₂ = q₁ := by
    rw [Category.assoc, Category.assoc, hu₂', hg₁, hu₁]
  have h₂ : (u₁.hom ≫ g₂ ≫ u₂.inv) ≫ q₂ = q₁ := by
    rw [Category.assoc, Category.assoc, hu₂', hg₂, hu₁]
  have hconj : map (I := I.comap q₁) (J := I.comap q₂) (u₁.hom ≫ g₁ ≫ u₂.inv)
        (comap_le_of_comp h₁ I) =
      map (I := I.comap q₁) (J := I.comap q₂) (u₁.hom ≫ g₂ ≫ u₂.inv)
        (comap_le_of_comp h₂ I) := by
    calc _ = map u₁.hom (comap_le_of_comp hu₁ I) ≫ map g₁ (comap_le_of_comp hg₁ I) ≫
            map u₂.inv (comap_le_of_comp hu₂' I) := by
          rw [map_comp, map_comp]
      _ = map u₁.hom (comap_le_of_comp hu₁ I) ≫ map g₂ (comap_le_of_comp hg₂ I) ≫
            map u₂.inv (comap_le_of_comp hu₂' I) := by rw [hmap]
      _ = _ := by rw [map_comp, map_comp]
  exact (cancel_mono u₂.inv).mp ((cancel_epi u₁.hom).mp (hext h₁ h₂ hconj))

/-- Transport existence of formal-completion lifts across scheme isomorphisms over `X`. -/
private lemma exists_hom_of_iso {Z₁ Z₂ Y₁ Y₂ : Scheme.{u}} {q₁ : Z₁ ⟶ X} {q₂ : Z₂ ⟶ X}
    {p₁ : Y₁ ⟶ X} {p₂ : Y₂ ⟶ X} (u₁ : Z₁ ≅ Y₁) (u₂ : Z₂ ≅ Y₂)
    (hu₁ : u₁.hom ≫ p₁ = q₁) (hu₂ : u₂.hom ≫ p₂ = q₂)
    (hexists : ∀ (b : Z₁.formalCompletion (I.comap q₁) ⟶ Z₂.formalCompletion (I.comap q₂)),
      b ≫ map q₂ le_rfl = map q₁ le_rfl →
      ∃ g' : Z₁ ⟶ Z₂, ∃ hg' : g' ≫ q₂ = q₁,
        map (I := I.comap q₁) (J := I.comap q₂) g' (comap_le_of_comp hg' I) = b)
    (a : Y₁.formalCompletion (I.comap p₁) ⟶ Y₂.formalCompletion (I.comap p₂))
    (ha : a ≫ map p₂ le_rfl = map p₁ le_rfl) :
    ∃ g : Y₁ ⟶ Y₂, ∃ hg : g ≫ p₂ = p₁,
      map (I := I.comap p₁) (J := I.comap p₂) g (comap_le_of_comp hg I) = a := by
  have hu₁' : u₁.inv ≫ q₁ = p₁ := by rw [← hu₁, Iso.inv_hom_id_assoc]
  have he₁ : (I.comap p₁).comap u₁.hom = I.comap q₁ := by
    rw [← IdealSheafData.comap_comp, hu₁]
  have he₂ : (I.comap p₂).comap u₂.hom = I.comap q₂ := by
    rw [← IdealSheafData.comap_comp, hu₂]
  let e₁ := mapIso u₁ he₁
  let e₂ := mapIso u₂ he₂
  have hb : (e₁.hom ≫ a ≫ e₂.inv) ≫ map q₂ le_rfl = map q₁ le_rfl := by
    have he₂' : e₂.inv ≫ map q₂ le_rfl = map p₂ le_rfl := by
      rw [e₂.inv_comp_eq, mapIso_hom, map_comp, map_congr hu₂ _ le_rfl]
    rw [Category.assoc, Category.assoc, he₂', ha, mapIso_hom, map_comp,
      map_congr hu₁ _ le_rfl]
  obtain ⟨g', hg', hmap'⟩ := hexists (e₁.hom ≫ a ≫ e₂.inv) hb
  refine ⟨u₁.inv ≫ g' ≫ u₂.hom, ?_, ?_⟩
  · rw [Category.assoc, Category.assoc, hu₂, hg', hu₁']
  · calc _ = e₁.inv ≫ map g' (comap_le_of_comp hg' I) ≫ e₂.hom := by
          rw [mapIso_inv, mapIso_hom, map_comp, map_comp]
      _ = e₁.inv ≫ (e₁.hom ≫ a ≫ e₂.inv) ≫ e₂.hom := by rw [hmap']
      _ = a := by simp

/-- **Uniqueness of algebraized affine morphisms.** Let `p₁ : Y₁ ⟶ X` and `p₂ : Y₂ ⟶ X` be affine
morphisms whose coordinate algebras `(p₁)_* 𝒪_{Y₁}` and `(p₂)_* 𝒪_{Y₂}` are finitely presented
`𝒪_X`-modules. If `completionFunctor X I` is faithful, two morphisms `Y₁ ⟶ Y₂` over `X` inducing
the same morphism on formal completions along the preimages of `I` are equal. -/
theorem hom_ext_of_map_eq [(completionFunctor X I).Faithful] {Y₁ Y₂ : Scheme.{u}}
    (p₁ : Y₁ ⟶ X) (p₂ : Y₂ ⟶ X) [IsAffineHom p₁] [IsAffineHom p₂]
    [p₁.pushforwardStructureAlgebra.X.IsFinitePresentation]
    [p₂.pushforwardStructureAlgebra.X.IsFinitePresentation]
    {g₁ g₂ : Y₁ ⟶ Y₂} (hg₁ : g₁ ≫ p₂ = p₁) (hg₂ : g₂ ≫ p₂ = p₁)
    (hmap : map (I := I.comap p₁) (J := I.comap p₂) g₁
        (by rw [← IdealSheafData.comap_comp, hg₁]) =
      map (I := I.comap p₁) (J := I.comap p₂) g₂
        (by rw [← IdealSheafData.comap_comp, hg₂])) :
    g₁ = g₂ :=
  let A₁ : QuasicoherentAlgebra X := ⟨p₁.pushforwardStructureAlgebra, inferInstance⟩
  let A₂ : QuasicoherentAlgebra X := ⟨p₂.pushforwardStructureAlgebra, inferInstance⟩
  hom_ext_of_iso p₁.relativeSpecFunctionsIso p₂.relativeSpecFunctionsIso
    (by rw [Scheme.Hom.relativeSpecFunctionsIso_hom]; exact p₁.relativeSpecFunctionsToScheme_comp)
    (by rw [Scheme.Hom.relativeSpecFunctionsIso_hom]; exact p₂.relativeSpecFunctionsToScheme_comp)
    (hom_ext_of_map_eq_relativeSpec (A₁ := A₁) (A₂ := A₂)) hg₁ hg₂ hmap

/-- **Algebraization of morphisms between affine `X`-schemes.** Let `p₁ : Y₁ ⟶ X` and
`p₂ : Y₂ ⟶ X` be affine morphisms whose coordinate algebras `(p₁)_* 𝒪_{Y₁}` and `(p₂)_* 𝒪_{Y₂}`
are finitely presented `𝒪_X`-modules. If `completionFunctor X I` is full and faithful, every
morphism `Y₁.formalCompletion (I.comap p₁) ⟶ Y₂.formalCompletion (I.comap p₂)` over
`X.formalCompletion I` is induced by a unique morphism `g : Y₁ ⟶ Y₂` over `X`. -/
theorem existsUnique_hom_of_formalCompletion [(completionFunctor X I).Full]
    [(completionFunctor X I).Faithful] {Y₁ Y₂ : Scheme.{u}} (p₁ : Y₁ ⟶ X) (p₂ : Y₂ ⟶ X)
    [IsAffineHom p₁] [IsAffineHom p₂]
    [p₁.pushforwardStructureAlgebra.X.IsFinitePresentation]
    [p₂.pushforwardStructureAlgebra.X.IsFinitePresentation]
    (a : Y₁.formalCompletion (I.comap p₁) ⟶ Y₂.formalCompletion (I.comap p₂))
    (ha : a ≫ map p₂ le_rfl = map p₁ le_rfl) :
    ∃! g : Y₁ ⟶ Y₂, ∃ hg : g ≫ p₂ = p₁,
      map (I := I.comap p₁) (J := I.comap p₂) g
        (by rw [← IdealSheafData.comap_comp, hg]) = a := by
  let A₁ : QuasicoherentAlgebra X := ⟨p₁.pushforwardStructureAlgebra, inferInstance⟩
  let A₂ : QuasicoherentAlgebra X := ⟨p₂.pushforwardStructureAlgebra, inferInstance⟩
  obtain ⟨g, hg, hmap⟩ := exists_hom_of_iso p₁.relativeSpecFunctionsIso p₂.relativeSpecFunctionsIso
    (by rw [Scheme.Hom.relativeSpecFunctionsIso_hom]; exact p₁.relativeSpecFunctionsToScheme_comp)
    (by rw [Scheme.Hom.relativeSpecFunctionsIso_hom]; exact p₂.relativeSpecFunctionsToScheme_comp)
    (fun b hb ↦
      let ⟨Φ, hΦ⟩ := exists_relativeSpecMap_of_formalCompletion (A₁ := A₁) (A₂ := A₂) b hb
      ⟨CommMon.relativeSpecMap Φ.hom, CommMon.relativeSpecMap_relativeSpecToBase Φ.hom, hΦ⟩)
    a ha
  exact ⟨g, ⟨hg, hmap⟩, fun g' ⟨hg', hmap'⟩ ↦
    hom_ext_of_map_eq p₁ p₂ hg' hg (hmap'.trans hmap.symm)⟩

/-- The unique scheme morphism `Y₁ ⟶ Y₂` over `X` algebraizing a morphism of formal completions
`a : Y₁.formalCompletion (I.comap p₁) ⟶ Y₂.formalCompletion (I.comap p₂)` over
`X.formalCompletion I`. -/
noncomputable def liftOfFormalCompletion [(completionFunctor X I).Full]
    [(completionFunctor X I).Faithful] {Y₁ Y₂ : Scheme.{u}} (p₁ : Y₁ ⟶ X) (p₂ : Y₂ ⟶ X)
    [IsAffineHom p₁] [IsAffineHom p₂]
    [p₁.pushforwardStructureAlgebra.X.IsFinitePresentation]
    [p₂.pushforwardStructureAlgebra.X.IsFinitePresentation]
    (a : Y₁.formalCompletion (I.comap p₁) ⟶ Y₂.formalCompletion (I.comap p₂))
    (ha : a ≫ map p₂ le_rfl = map p₁ le_rfl) : Y₁ ⟶ Y₂ :=
  (existsUnique_hom_of_formalCompletion p₁ p₂ a ha).exists.choose

@[reassoc (attr := simp)]
theorem liftOfFormalCompletion_comp [(completionFunctor X I).Full]
    [(completionFunctor X I).Faithful] {Y₁ Y₂ : Scheme.{u}} (p₁ : Y₁ ⟶ X) (p₂ : Y₂ ⟶ X)
    [IsAffineHom p₁] [IsAffineHom p₂]
    [p₁.pushforwardStructureAlgebra.X.IsFinitePresentation]
    [p₂.pushforwardStructureAlgebra.X.IsFinitePresentation]
    (a : Y₁.formalCompletion (I.comap p₁) ⟶ Y₂.formalCompletion (I.comap p₂))
    (ha : a ≫ map p₂ le_rfl = map p₁ le_rfl) :
    liftOfFormalCompletion p₁ p₂ a ha ≫ p₂ = p₁ :=
  (existsUnique_hom_of_formalCompletion p₁ p₂ a ha).exists.choose_spec.1

@[simp]
theorem map_liftOfFormalCompletion [(completionFunctor X I).Full]
    [(completionFunctor X I).Faithful] {Y₁ Y₂ : Scheme.{u}} (p₁ : Y₁ ⟶ X) (p₂ : Y₂ ⟶ X)
    [IsAffineHom p₁] [IsAffineHom p₂]
    [p₁.pushforwardStructureAlgebra.X.IsFinitePresentation]
    [p₂.pushforwardStructureAlgebra.X.IsFinitePresentation]
    (a : Y₁.formalCompletion (I.comap p₁) ⟶ Y₂.formalCompletion (I.comap p₂))
    (ha : a ≫ map p₂ le_rfl = map p₁ le_rfl) :
    map (I := I.comap p₁) (J := I.comap p₂) (liftOfFormalCompletion p₁ p₂ a ha)
      (by rw [← IdealSheafData.comap_comp, liftOfFormalCompletion_comp]) = a :=
  (existsUnique_hom_of_formalCompletion p₁ p₂ a ha).exists.choose_spec.2

/-- Any morphism over `X` inducing `a` on formal completions is `liftOfFormalCompletion`. -/
theorem eq_liftOfFormalCompletion [(completionFunctor X I).Full]
    [(completionFunctor X I).Faithful] {Y₁ Y₂ : Scheme.{u}} (p₁ : Y₁ ⟶ X) (p₂ : Y₂ ⟶ X)
    [IsAffineHom p₁] [IsAffineHom p₂]
    [p₁.pushforwardStructureAlgebra.X.IsFinitePresentation]
    [p₂.pushforwardStructureAlgebra.X.IsFinitePresentation]
    (a : Y₁.formalCompletion (I.comap p₁) ⟶ Y₂.formalCompletion (I.comap p₂))
    (ha : a ≫ map p₂ le_rfl = map p₁ le_rfl) {g : Y₁ ⟶ Y₂} (hg : g ≫ p₂ = p₁)
    (hmap : map (I := I.comap p₁) (J := I.comap p₂) g
      (by rw [← IdealSheafData.comap_comp, hg]) = a) :
    g = liftOfFormalCompletion p₁ p₂ a ha :=
  (existsUnique_hom_of_formalCompletion p₁ p₂ a ha).unique ⟨hg, hmap⟩
    ⟨liftOfFormalCompletion_comp p₁ p₂ a ha, map_liftOfFormalCompletion p₁ p₂ a ha⟩

end RelativeSpec

end AlgebraicGeometry.Scheme.formalCompletion
