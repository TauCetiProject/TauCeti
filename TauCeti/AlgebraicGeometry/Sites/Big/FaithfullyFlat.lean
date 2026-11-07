/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Sites.Big.Module
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
import TauCeti.AlgebraicGeometry.AffineScheme
import TauCeti.AlgebraicGeometry.Modules.Pullback.BaseChange
import TauCeti.AlgebraicGeometry.Modules.Sheaf
import TauCeti.RingTheory.Flat.EffectiveDescent

/-!
# Faithfully flat descent of sections of the big presheaf of a quasi-coherent module

Let `S` be a scheme and `F` a quasi-coherent `𝒪_S`-module. This file proves that the presheaf
`AlgebraicGeometry.Scheme.Modules.bigPresheaf F : (T, h) ↦ Γ(T, h^* F)` on the big site `Over S`
satisfies the sheaf condition for a single flat surjective morphism `f : T' ⟶ T` of affine
`S`-schemes
(`AlgebraicGeometry.Scheme.Modules.isSheafFor_bigPresheaf_singleton_of_flat_of_surjective`).
Together with the Zariski sheaf property
(`AlgebraicGeometry.Scheme.Modules.isSheaf_bigPresheaf_zariskiTopology`) these are the two cases
to which Mathlib's `AlgebraicGeometry.isSheaf_propQCTopology_iff` (Stacks, Tag 022H) reduces the
fpqc sheaf property on schemes; this is fpqc descent of sections of quasi-coherent modules
(Stacks, Lemma 35.8.1).

The proof computes sections over affine `S`-schemes. For a morphism `f : T ⟶ T'` of affine
`S`-schemes, the restriction map identifies `Γ(T, h^* F)` with the extension of scalars
`Γ(T, 𝒪) ⊗_{Γ(T', 𝒪)} Γ(T', h'^* F)` (`AlgebraicGeometry.Scheme.Modules.bigSectionsBaseChange`),
by the affine base change of quasi-coherent sections
`AlgebraicGeometry.Scheme.Hom.pullbackSectionsEquiv`. For `A = Γ(T, 𝒪) → A' = Γ(T', 𝒪)`
faithfully flat and `M = Γ(T, h^* F)`, the sheaf condition along `f` is then compared, through
the test scheme `Spec (A' ⊗_A A')` and its two projections to `T'`, with the exactness of the
Amitsur sequence `M → A' ⊗_A M ⇉ A' ⊗_A (A' ⊗_A M)`
(`Module.FaithfullyFlat.exact_mk_one_lTensor_sub_mk_one`).

## Main declarations

* `AlgebraicGeometry.Scheme.Modules.bigSectionsBaseChange`: for a morphism `f : T ⟶ T'` of
  affine `S`-schemes, `Γ(T, 𝒪) ⊗_{Γ(T', 𝒪)} Γ(T', h'^* F) ≃ Γ(T, h^* F)`, sending `1 ⊗ s` to the
  restriction of `s` along `f`.
* `AlgebraicGeometry.Scheme.Modules.isSheafFor_bigPresheaf_singleton_of_flat_of_surjective`: the
  sheaf condition for a single flat surjective morphism of affine `S`-schemes.

## References

* The Stacks Project, Section 35.8, *Quasi-coherent sheaves and topologies*, Lemma 35.8.1, and
  Chapter *Descent*, Section *Descent for modules* (the Amitsur complex).
-/

public section

open CategoryTheory TensorProduct
open scoped ChangeOfRings

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {S : Scheme.{u}} (F : S.Modules) [F.IsQuasicoherent]

/-- For a morphism `f : T ⟶ T'` of affine `S`-schemes with structure morphisms `h`,
`h'`, the sections `Γ(T, h^* F)` of the big presheaf of a quasi-coherent `F` are the extension of
scalars of `Γ(T', h'^* F)` along `f^♯ : Γ(T', 𝒪) ⟶ Γ(T, 𝒪)`. The equivalence sends `a ⊗ s` to
`a` times the restriction of `s` along `f` (`bigSectionsBaseChange_tmul`). -/
noncomputable def bigSectionsBaseChange {T T' : Over S} (f : T ⟶ T') [IsAffine T.left]
    [IsAffine T'.left] :
    (ModuleCat.extendScalars f.left.appTop.hom).obj
        (.of Γ(T'.left, ⊤) Γ((pullback T'.hom).obj F, ⊤)) ≃ₗ[Γ(T.left, ⊤)]
      Γ((pullback T.hom).obj F, ⊤) :=
  -- The open `f.left ⁻¹ᵁ ⊤` is `⊤` by definition; the ascription records the module over `⊤`.
  ((f.left.pullbackSectionsEquiv ((pullback T'.hom).obj F) (isAffineOpen_top _)
    (by rw [Hom.preimage_top]; exact isAffineOpen_top _)).trans
    (sectionsLinearEquiv ((pullbackComp f.left T'.hom).app F ≪≫
      (pullbackCongr (Over.w f)).app F) (f.left ⁻¹ᵁ ⊤)) :)

-- These equations stay named rewrites, as for `Scheme.Hom.pullbackSectionsEquiv_one_tmul`:
-- normalising the carrier of the scalar extension can change the tensor before `simp` matches.
/-- `bigSectionsBaseChange` sends `1 ⊗ s` to the restriction of `s` along `f`. -/
lemma bigSectionsBaseChange_one_tmul {T T' : Over S} (f : T ⟶ T') [IsAffine T.left]
    [IsAffine T'.left] (s : Γ((pullback T'.hom).obj F, ⊤)) :
    bigSectionsBaseChange F f ((1 : Γ(T.left, ⊤)) ⊗ₜ[Γ(T'.left, ⊤), f.left.appTop.hom] s) =
      bigSectionsRestrict F f s := by
  have h := f.left.pullbackSectionsEquiv_one_tmul ((pullback T'.hom).obj F) (isAffineOpen_top _)
    (by rw [Hom.preimage_top]; exact isAffineOpen_top _) s
  exact (congrArg (sectionsLinearEquiv ((pullbackComp f.left T'.hom).app F ≪≫
      (pullbackCongr (Over.w f)).app F) _) h).trans
    ((sectionsLinearEquiv_apply _ _ _).trans (bigSectionsRestrict_apply F f s).symm)

/-- `bigSectionsBaseChange` sends `a ⊗ s` to `a` times the restriction of `s` along `f`. -/
lemma bigSectionsBaseChange_tmul {T T' : Over S} (f : T ⟶ T') [IsAffine T.left]
    [IsAffine T'.left] (a : Γ(T.left, ⊤)) (s : Γ((pullback T'.hom).obj F, ⊤)) :
    bigSectionsBaseChange F f (a ⊗ₜ[Γ(T'.left, ⊤), f.left.appTop.hom] s) =
      a • bigSectionsRestrict F f s := by
  have h := ModuleCat.ExtendScalars.smul_tmul (f := f.left.appTop.hom)
    (M := .of Γ(T'.left, ⊤) Γ((pullback T'.hom).obj F, ⊤)) a 1 s
  rw [mul_one] at h
  exact (congrArg (bigSectionsBaseChange F f) h.symm).trans
    (((bigSectionsBaseChange F f).map_smul a _).trans
      (congrArg (a • ·) (bigSectionsBaseChange_one_tmul F f s)))

/-- Restricting `a ⊗ s` further along `g : T₀ ⟶ T` gives `g^♯ a` times the restriction of `s`
along `g ≫ f`. -/
lemma bigSectionsRestrict_bigSectionsBaseChange_tmul {T₀ T T' : Over S} (g : T₀ ⟶ T)
    (f : T ⟶ T') [IsAffine T.left] [IsAffine T'.left] (a : Γ(T.left, ⊤))
    (s : Γ((pullback T'.hom).obj F, ⊤)) :
    bigSectionsRestrict F g (bigSectionsBaseChange F f (a ⊗ₜ[Γ(T'.left, ⊤), f.left.appTop.hom] s)) =
      g.left.appTop a • bigSectionsRestrict F (g ≫ f) s :=
  (congrArg (bigSectionsRestrict F g) (bigSectionsBaseChange_tmul F f a s)).trans
    (((bigSectionsRestrict F g).map_smulₛₗ a _).trans
      (congrArg (_ • ·) (bigSectionsRestrict_comp F g f s).symm))

/-- **Faithfully flat descent of sections along a map of affine schemes.** For a quasi-coherent
`𝒪_S`-module `F` and a flat surjective morphism `f : T' ⟶ T` of `S`-schemes with `T` and `T'`
affine, the presheaf `(T, h) ↦ Γ(T, h^* F)` underlying `bigPresheaf F` satisfies the sheaf
condition for the single morphism `f`. -/
theorem isSheafFor_bigPresheaf_singleton_of_flat_of_surjective {T T' : Over S} (f : T' ⟶ T)
    [IsAffine T.left] [IsAffine T'.left] [Flat f.left] [Surjective f.left] :
    Presieve.IsSheafFor (F.bigPresheaf.presheaf ⋙ CategoryTheory.forget AddCommGrpCat)
      (.singleton f) := by
  have hφ : f.left.appTop.hom.FaithfullyFlat :=
    (Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine f.left).mp ⟨‹_›, ‹_›⟩
  algebraize [f.left.appTop.hom]
  let A := Γ(T.left, ⊤)
  let A' := Γ(T'.left, ⊤)
  let M := Γ((pullback T.hom).obj F, ⊤)
  -- The test scheme `Z = Spec (A' ⊗[A] A')` over `S`, with the two maps `g₁`, `g₂ : Z ⟶ T'`
  -- induced by the inclusions `χ₁`, `χ₂` of the two factors.
  let B := CommRingCat.of (A' ⊗[A] A')
  let χ₁ : A' ⟶ B := CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom
  let χ₂ : A' ⟶ B := CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom
  have hχ : f.left.appTop ≫ χ₁ = f.left.appTop ≫ χ₂ := by
    ext a
    exact (Algebra.TensorProduct.algebraMap_apply (R := A) (A := A') (B := A') a).symm.trans
      (Algebra.TensorProduct.algebraMap_apply' a)
  let ι (χ : A' ⟶ B) : Spec B ⟶ T'.left := Spec.map χ ≫ T'.left.isoSpec.inv
  have hι : ι χ₁ ≫ f.left = ι χ₂ ≫ f.left := by
    simp only [ι, Category.assoc, ← Scheme.isoSpec_inv_naturality, ← Spec.map_comp_assoc, hχ]
  let κ := (Scheme.ΓSpecIso B).hom.hom
  have hκ (χ : A' ⟶ B) (a : A') : κ ((ι χ).appTop a) = χ a := by
    have h : (ι χ).appTop ≫ (Scheme.ΓSpecIso B).hom = χ := by
      rw [Scheme.Hom.comp_appTop, Scheme.isoSpec_inv_appTop, Category.assoc,
        Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]
    exact congr(($h).hom a)
  let Z : Over S := Over.mk (ι χ₁ ≫ T'.hom)
  have : IsAffine Z.left := inferInstanceAs (IsAffine (Spec B))
  let g₁ : Z ⟶ T' := Over.homMk (ι χ₁)
  let g₂ : Z ⟶ T' := Over.homMk (ι χ₂) (by
    dsimp only [Z, Over.mk_hom]
    rw [← Over.w f, reassoc_of% hι])
  have hg : g₁ ≫ f = g₂ ≫ f := by
    ext : 1
    exact hι
  -- Sections over `T'` and over `Z` are scalar extensions of `M`. The map `J` reads sections over
  -- `Z`, that is `Γ(Z, 𝒪) ⊗_A M`, in the last term `A' ⊗_A (A' ⊗_A M)` of the Amitsur sequence.
  let e := bigSectionsBaseChange F f
  let eZ := bigSectionsBaseChange F (g₁ ≫ f)
  let J₀ : Γ(Spec B, ⊤) →+ M →+ A' ⊗[A] (A' ⊗[A] M) :=
    AddMonoidHom.mk' (fun c ↦ ((TensorProduct.assoc A A' A' M).toLinearMap ∘ₗ
      TensorProduct.mk A (A' ⊗[A] A') M (κ c)).toAddMonoidHom) fun c c' ↦ by
        ext m
        simp
  have hJ₀ (c : Γ(Spec B, ⊤)) (m : M) : J₀ c m = TensorProduct.assoc A A' A' M (κ c ⊗ₜ m) :=
    rfl
  let J : (ModuleCat.extendScalars (g₁ ≫ f).left.appTop.hom).obj (.of A M) →+
      A' ⊗[A] (A' ⊗[A] M) :=
    TensorProduct.liftAddHom J₀ fun r (c : Γ(Z.left, ⊤)) m ↦ by
      have hr : κ ((g₁ ≫ f).left.appTop r) = algebraMap A (A' ⊗[A] A') r :=
        (hκ χ₁ (f.left.appTop r)).trans
          (Algebra.TensorProduct.algebraMap_apply (R := A) (A := A') (B := A') r).symm
      -- `r` acts on the scalar extension through `(g₁ ≫ f)^♯`, by definition of
      -- `ModuleCat.restrictScalars`.
      calc _ = TensorProduct.assoc A A' A' M (κ ((g₁ ≫ f).left.appTop r * c) ⊗ₜ m) := rfl
        _ = TensorProduct.assoc A A' A' M ((r • κ c) ⊗ₜ m) := by
          rw [map_mul, hr, ← Algebra.smul_def]
        _ = J₀ c (r • m) := by rw [TensorProduct.smul_tmul, hJ₀]
  -- Restriction along `g ∈ {g₁, g₂}`, read through `e`, `eZ` and `J`, is the corresponding map
  -- `L` of the Amitsur sequence.
  have key (g : Z ⟶ T') (hgf : g ≫ f = g₁ ≫ f) (L : A' ⊗[A] M →ₗ[A] A' ⊗[A] (A' ⊗[A] M))
      (hL : ∀ (a : A') (m : M),
        TensorProduct.assoc A A' A' M (κ (g.left.appTop a) ⊗ₜ m) = L (a ⊗ₜ m))
      (y : (ModuleCat.extendScalars f.left.appTop.hom).obj (.of A M)) :
      J (eZ.symm (bigSectionsRestrict F g (e y))) = L y := by
    induction y using TensorProduct.inductionOn with
    | tmul a m =>
      have h := (bigSectionsRestrict_bigSectionsBaseChange_tmul F g f a m).trans
        ((congrArg (_ • bigSectionsRestrict F · m) hgf).trans
          (bigSectionsBaseChange_tmul F (g₁ ≫ f) _ m).symm)
      exact ((congrArg (fun x ↦ J (eZ.symm x)) h).trans
        ((congrArg J (eZ.symm_apply_apply _)).trans (hJ₀ _ m))).trans (hL a m)
    | add y y' hy hy' =>
      refine ((congrArg (fun x ↦ J (eZ.symm (bigSectionsRestrict F g x))) (e.map_add y y')).trans
        ?_).trans (L.map_add y y').symm
      rw [map_add, map_add, map_add, hy, hy']
  have key₁ := key g₁ rfl ((TensorProduct.mk A A' M 1).lTensor A') fun a m ↦
    (congrArg (fun c ↦ TensorProduct.assoc A A' A' M (c ⊗ₜ m)) (hκ χ₁ a)).trans
      (TensorProduct.assoc_tmul a 1 m)
  have key₂ := key g₂ hg.symm (TensorProduct.mk A A' (A' ⊗[A] M) 1) fun a m ↦
    (congrArg (fun c ↦ TensorProduct.assoc A A' A' M (c ⊗ₜ m)) (hκ χ₂ a)).trans
      (TensorProduct.assoc_tmul 1 a m)
  rw [Presieve.isSheafFor_singleton]
  intro x hx
  obtain ⟨y, rfl⟩ := e.surjective x
  -- Compatibility on `Z` places `y` in the kernel of the Amitsur differential, so `y = 1 ⊗ m`.
  let y' : A' ⊗[A] M := y
  have hy : ((TensorProduct.mk A A' M 1).lTensor A' - TensorProduct.mk A A' (A' ⊗[A] M) 1) y' =
      0 :=
    (LinearMap.sub_apply _ _ y').trans (sub_eq_zero.mpr ((key₁ y).symm.trans
      ((congrArg (fun x ↦ J (eZ.symm x)) (hx g₁ g₂ hg)).trans (key₂ y))))
  obtain ⟨m, hm⟩ := (Module.FaithfullyFlat.exact_mk_one_lTensor_sub_mk_one A' M y').mp hy
  have hxm : bigSectionsRestrict F f m = e y :=
    (bigSectionsBaseChange_one_tmul F f m).symm.trans (congrArg e hm)
  refine ⟨m, hxm, fun (m' : M) hm' ↦ ?_⟩
  exact Module.FaithfullyFlat.tensorProduct_mk_injective (A := A) (B := A') (M := M) (e.injective
    (((bigSectionsBaseChange_one_tmul F f m').trans (hm'.trans hxm.symm)).trans
      (bigSectionsBaseChange_one_tmul F f m).symm))

end AlgebraicGeometry.Scheme.Modules
