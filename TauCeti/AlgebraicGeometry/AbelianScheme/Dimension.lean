/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AbelianScheme.Field
public import TauCeti.AlgebraicGeometry.Morphisms.Smooth.RelativeDimension
public import TauCeti.AlgebraicGeometry.Scheme.KrullDimension

/-!
# Relative dimension of abelian schemes

For an abelian scheme `A` over an arbitrary base scheme `S`, every fibre `A_s` is smooth and
geometrically integral over `κ(s)`, so its Krull dimension is a natural number
`A.relativeDimension s : ℕ`. This file develops the relative-dimension API and characterizes
dimension-zero abelian schemes over arbitrary bases:

* `AbelianScheme.relativeDimension` and `AbelianScheme.topologicalKrullDim_fiber`: the fibrewise
  dimension function `S → ℕ` and its characterization as the topological Krull dimension of each
  fibre;
* `AbelianScheme.isLocallyConstant_relativeDimension`: `A.relativeDimension` is locally constant
  on `S`;
* `AbelianScheme.smoothOfRelativeDimension_iff_forall_relativeDimension_eq`: `A.toOver.hom` is
  smooth of constant relative dimension `g` if and only if `A.relativeDimension s = g` for all
  `s : S`;
* `AbelianScheme.relativeDimension_identity`, `AbelianScheme.relativeDimension_baseChange`,
  `AbelianScheme.relativeDimension_prod`, `AbelianScheme.relativeDimension_ofAbelianVariety`:
  behaviour on the identity abelian scheme, arbitrary base change, binary products, and over a
  field;
* `AbelianScheme.isIso_zeroSection_iff`, `AbelianScheme.isIso_toOver_hom_iff`,
  `AbelianScheme.isoIdentityOfRelativeDimensionZero`,
  `AbelianScheme.isZero_iff_forall_relativeDimension_eq_zero`, and
  `AbelianScheme.mulBy_eq_id_of_forall_relativeDimension_eq_zero`: an abelian scheme of relative
  dimension zero is canonically isomorphic to `AbelianScheme.identity S`, its zero section and
  structure morphism are isomorphisms, and multiplication by every integer is the identity.
-/

public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry MonObj
open scoped CategoryTheory.MonObj

namespace TauCeti

namespace AlgebraicGeometry

universe u

namespace AbelianScheme

variable {S T : Scheme.{u}}

noncomputable section

/-- The relative dimension of an abelian scheme `A` over `S` at a point `s : S`, defined as the
Krull dimension of the fibre `A_s`. -/
def relativeDimension (A : AbelianScheme S) (s : S) : ℕ :=
  (exists_topologicalKrullDim_fiber_eq_nat A.toOver.hom s).choose

/-- The topological Krull dimension of the fibre of `A` over `s` equals `A.relativeDimension s`. -/
theorem topologicalKrullDim_fiber (A : AbelianScheme S) (s : S) :
    topologicalKrullDim (A.toOver.hom.fiber s) = A.relativeDimension s :=
  (exists_topologicalKrullDim_fiber_eq_nat A.toOver.hom s).choose_spec

/-- `A.relativeDimension s = n` if and only if the fibre over `s` has Krull dimension `n`. -/
theorem relativeDimension_eq_iff (A : AbelianScheme S) (s : S) (n : ℕ) :
    A.relativeDimension s = n ↔ topologicalKrullDim (A.toOver.hom.fiber s) = n := by
  rw [topologicalKrullDim_fiber]
  exact_mod_cast Iff.rfl

/-- The relative dimension of an abelian scheme is locally constant on the base scheme. -/
theorem isLocallyConstant_relativeDimension (A : AbelianScheme S) :
    IsLocallyConstant A.relativeDimension := by
  have h := isLocallyConstant_topologicalKrullDim_fiber A.toOver.hom
  rw [IsLocallyConstant.iff_eventually_eq] at h ⊢
  intro s
  filter_upwards [h s] with t ht
  rw [topologicalKrullDim_fiber, topologicalKrullDim_fiber] at ht
  exact_mod_cast ht

/-- The fibre of `A` over `s` is smooth over `Spec κ(s)` of relative dimension
`A.relativeDimension s`. -/
theorem smoothOfRelativeDimension_fiber (A : AbelianScheme S) (s : S) :
    SmoothOfRelativeDimension (A.relativeDimension s) (A.toOver.hom.fiberToSpecResidueField s) :=
  smoothOfRelativeDimension_of_topologicalKrullDim_eq (k := S.residueField s)
    (A.toOver.hom.fiberToSpecResidueField s) (topologicalKrullDim_fiber A s)

/-- If every fibre of `A` has relative dimension `g`, then `A.toOver.hom` is smooth of relative
dimension `g`. -/
theorem smoothOfRelativeDimension_of_forall_relativeDimension_eq (A : AbelianScheme S) {g : ℕ}
    (h : ∀ s : S, A.relativeDimension s = g) :
    SmoothOfRelativeDimension g A.toOver.hom :=
  smoothOfRelativeDimension_of_forall_topologicalKrullDim_fiber_eq A.toOver.hom fun s ↦ by
    rw [topologicalKrullDim_fiber, h s]

/-- If `A.toOver.hom` is smooth of relative dimension `g`, then `A.relativeDimension s = g` at every
point `s : S`. -/
theorem relativeDimension_eq_of_smoothOfRelativeDimension (A : AbelianScheme S) (g : ℕ)
    [SmoothOfRelativeDimension g A.toOver.hom] (s : S) :
    A.relativeDimension s = g := by
  rw [relativeDimension_eq_iff]
  exact topologicalKrullDim_eq_of_smoothOfRelativeDimension (k := S.residueField s)
    (A.toOver.hom.fiberToSpecResidueField s)

/-- `A.toOver.hom` is smooth of relative dimension `g` if and only if every fibre has relative
dimension `g`. -/
theorem smoothOfRelativeDimension_iff_forall_relativeDimension_eq (A : AbelianScheme S) (g : ℕ) :
    SmoothOfRelativeDimension g A.toOver.hom ↔ ∀ s : S, A.relativeDimension s = g :=
  ⟨fun _ ↦ relativeDimension_eq_of_smoothOfRelativeDimension A g,
    smoothOfRelativeDimension_of_forall_relativeDimension_eq A⟩

/-- Isomorphic abelian schemes have the same relative dimension at every point of the base. -/
theorem relativeDimension_eq_of_iso {A B : AbelianScheme S} (e : A ≅ B) (s : S) :
    A.relativeDimension s = B.relativeDimension s := by
  rw [relativeDimension_eq_iff, ← topologicalKrullDim_fiber B s]
  let eF : A.toOver.hom.fiber s ≅ B.toOver.hom.fiber s :=
    (Over.forget _).mapIso
      ((Over.pullback (S.fromSpecResidueField s)).mapIso (toOverFunctor.mapIso e))
  exact eF.hom.homeomorph.isHomeomorph.topologicalKrullDim_eq

/-- The identity abelian scheme over `S` has relative dimension `0` at every point of `S`. -/
@[simp]
theorem relativeDimension_identity (S : Scheme.{u}) (s : S) :
    (identity S).relativeDimension s = 0 := by
  have hiso : IsIso (identity S).toOver.hom := by
    have h1 : IsIso (𝟙_ (Over S)).hom := by
      rw [Over.tensorUnit_hom]
      exact IsIso.id S
    have h2 : IsIso (eqToHom (identity_toOver S)).left :=
      inferInstanceAs (IsIso ((Over.forget S).map (eqToHom (identity_toOver S))))
    rw [← (eqToHom (identity_toOver S)).w]
    infer_instance
  have : SmoothOfRelativeDimension 0 (identity S).toOver.hom := inferInstance
  exact relativeDimension_eq_of_smoothOfRelativeDimension (identity S) 0 s

/-- Base change pulls back the relative dimension by composition. -/
@[simp]
theorem relativeDimension_baseChange (A : AbelianScheme S) (f : T ⟶ S) (t : T) :
    (A.baseChange f).relativeDimension t = A.relativeDimension (f t) := by
  rw [relativeDimension_eq_iff, ← topologicalKrullDim_fiber A (f t)]
  let e₁ : (A.baseChange f).toOver.hom.fiber t ≅ (pullback.snd A.toOver.hom f).fiber t :=
    (Over.forget _).mapIso
      ((Over.pullback (T.fromSpecResidueField t)).mapIso (eqToIso (baseChange_toOver A f)))
  have hpb := isPullback_fiberToSpecResidueField_of_isPullback
    (IsPullback.of_hasPullback A.toOver.hom f) t
  let _ : Algebra (S.residueField (f t)) (T.residueField t) :=
    (f.residueFieldMap t).hom.toAlgebra
  let e₂ : (pullback.snd A.toOver.hom f).fiber t ≅
      pullback (A.toOver.hom.fiberToSpecResidueField (f t))
        (Spec.map (CommRingCat.ofHom
          (algebraMap (S.residueField (f t)) (T.residueField t)))) :=
    hpb.isoPullback
  exact ((e₁.trans e₂).hom.homeomorph.isHomeomorph.topologicalKrullDim_eq).trans
    (topologicalKrullDim_pullback_Spec_map_of_field (K := S.residueField (f t))
      (L := T.residueField t) (A.toOver.hom.fiberToSpecResidueField (f t)))

/-- Over a field, the relative dimension of `ofAbelianVariety A` agrees with `A.dim`. -/
theorem relativeDimension_ofAbelianVariety {K : Type u} [Field K] (A : AbelianVariety K)
    (s : Spec (.of K)) :
    ((ofAbelianVariety A).relativeDimension s : WithBot ℕ∞) = A.dim := by
  have hhom : (ofAbelianVariety A).toOver.hom =
      eqToHom (ofAbelianVariety_toScheme A) ≫ A.toOver.hom := by
    rw [← Over.eqToHom_left (ofAbelianVariety_toOver A)]
    exact (eqToHom (ofAbelianVariety_toOver A)).w.symm
  have hsm : SmoothOfRelativeDimension (Module.finrank K A.TangentSpace)
      (ofAbelianVariety A).toOver.hom := by
    rw [hhom, ← Nat.zero_add (Module.finrank K A.TangentSpace)]
    exact inferInstance
  rw [relativeDimension_eq_of_smoothOfRelativeDimension (ofAbelianVariety A)
    (Module.finrank K A.TangentSpace) s]
  exact AbelianVariety.finrank_tangentSpace_eq_dim A

/-- Over a field, the dimension of `toAbelianVariety A` agrees with `A.relativeDimension`. -/
theorem dim_toAbelianVariety {K : Type u} [Field K] (A : AbelianScheme (Spec (.of K)))
    (s : Spec (.of K)) :
    (toAbelianVariety A).dim = A.relativeDimension s := by
  have h := relativeDimension_ofAbelianVariety (toAbelianVariety A) s
  rw [ofAbelianVariety_toAbelianVariety] at h
  exact h.symm

/-- The relative dimension of a product of abelian schemes is the sum of their relative
dimensions. -/
@[simp]
theorem relativeDimension_prod (A B : AbelianScheme S) (s : S) :
    (A.prod B).relativeDimension s = A.relativeDimension s + B.relativeDimension s := by
  let i := S.fromSpecResidueField s
  obtain ⟨pt⟩ := (inferInstance : Nonempty (Spec (S.residueField s)))
  have hcast : ((A.prod B).relativeDimension s : WithBot ℕ∞) =
      (A.relativeDimension s + B.relativeDimension s : ℕ) := by
    calc
      ((A.prod B).relativeDimension s : WithBot ℕ∞)
          = ((A.prod B).relativeDimension (i pt) : WithBot ℕ∞) := by
            rw [S.fromSpecResidueField_apply s pt]
      _ = (((A.prod B).baseChange i).relativeDimension pt : WithBot ℕ∞) := by
            rw [relativeDimension_baseChange]
      _ = (((A.baseChange i).prod (B.baseChange i)).relativeDimension pt : WithBot ℕ∞) := by
            rw [relativeDimension_eq_of_iso (baseChangeProdIso A B i) pt]
      _ = (toAbelianVariety ((A.baseChange i).prod (B.baseChange i))).dim :=
            (dim_toAbelianVariety _ pt).symm
      _ = ((toAbelianVariety (A.baseChange i)).prod (toAbelianVariety (B.baseChange i))).dim :=
            AbelianVariety.dim_eq_of_iso (toAbelianVarietyProdIso _ _)
      _ = (toAbelianVariety (A.baseChange i)).dim + (toAbelianVariety (B.baseChange i)).dim :=
            AbelianVariety.dim_prod _ _
      _ = (A.relativeDimension s + B.relativeDimension s : ℕ) := by
            have hA : (A.baseChange i).relativeDimension pt = A.relativeDimension s := by
              rw [relativeDimension_baseChange, S.fromSpecResidueField_apply s pt]
            have hB : (B.baseChange i).relativeDimension pt = B.relativeDimension s := by
              rw [relativeDimension_baseChange, S.fromSpecResidueField_apply s pt]
            rw [dim_toAbelianVariety _ pt, dim_toAbelianVariety _ pt]
            exact_mod_cast congrArg₂ (· + ·) hA hB
  exact_mod_cast hcast

/-! ### Dimension-zero abelian schemes over an arbitrary base -/

/-- If an abelian scheme over `S` has relative dimension `0` everywhere, then its zero section is
an isomorphism. -/
theorem isIso_zeroSection_of_forall_relativeDimension_eq_zero (A : AbelianScheme S)
    (h : ∀ s : S, A.relativeDimension s = 0) :
    IsIso A.zeroSection :=
  isIso_of_comp_eq_id_of_topologicalKrullDim_fiber_eq_zero A.toOver.hom
    A.zeroSection_comp_toOver_hom fun s ↦ by
      rw [topologicalKrullDim_fiber, h s]
      rfl

/-- If an abelian scheme over `S` has relative dimension `0` everywhere, then its structure
morphism is an isomorphism. -/
theorem isIso_toOver_hom_of_forall_relativeDimension_eq_zero (A : AbelianScheme S)
    (h : ∀ s : S, A.relativeDimension s = 0) :
    IsIso A.toOver.hom := by
  have : IsIso A.zeroSection := isIso_zeroSection_of_forall_relativeDimension_eq_zero A h
  exact isIso_of_hom_comp_eq_id A.zeroSection A.zeroSection_comp_toOver_hom

/-- The structure morphism of an abelian scheme is an isomorphism if and only if its relative
dimension is identically `0`. -/
theorem isIso_toOver_hom_iff (A : AbelianScheme S) :
    IsIso A.toOver.hom ↔ ∀ s : S, A.relativeDimension s = 0 := by
  refine ⟨fun h s ↦ ?_, isIso_toOver_hom_of_forall_relativeDimension_eq_zero A⟩
  have : SmoothOfRelativeDimension 0 A.toOver.hom := inferInstance
  exact relativeDimension_eq_of_smoothOfRelativeDimension A 0 s

/-- The zero section of an abelian scheme is an isomorphism if and only if its relative dimension is
identically `0`. -/
theorem isIso_zeroSection_iff (A : AbelianScheme S) :
    IsIso A.zeroSection ↔ ∀ s : S, A.relativeDimension s = 0 :=
  ⟨fun _ ↦ (isIso_toOver_hom_iff A).mp
    (isIso_of_hom_comp_eq_id A.zeroSection A.zeroSection_comp_toOver_hom),
    isIso_zeroSection_of_forall_relativeDimension_eq_zero A⟩

/-- An abelian scheme of relative dimension `0` everywhere over `S` is canonically isomorphic to
`AbelianScheme.identity S`. -/
def isoIdentityOfRelativeDimensionZero (A : AbelianScheme S)
    (h : ∀ s : S, A.relativeDimension s = 0) : A ≅ identity S where
  hom := toIdentity A
  inv := fromIdentity A
  hom_inv_id := by
    have : IsIso A.zeroSection := isIso_zeroSection_of_forall_relativeDimension_eq_zero A h
    have heq : A.toOver.hom = inv A.zeroSection :=
      IsIso.eq_inv_of_hom_inv_id A.zeroSection_comp_toOver_hom
    apply hom_ext
    rw [toOverHom_comp, toOverHom_id, Over.comp_left, Over.id_left]
    calc
      toSchemeHom (toIdentity A) ≫ toSchemeHom (fromIdentity A)
          = (toSchemeHom (toIdentity A) ≫ eqToHom (identity_toScheme S)) ≫
              (eqToHom (identity_toScheme S).symm ≫ toSchemeHom (fromIdentity A)) := by
            simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
      _ = A.toOver.hom ≫ A.zeroSection := by rw [toSchemeHom_toIdentity, toSchemeHom_fromIdentity]
      _ = 𝟙 A.toScheme := by rw [heq, IsIso.inv_hom_id]
  inv_hom_id := Subsingleton.elim _ _

/-- An abelian scheme over `S` is a zero object in `AbelianScheme S` if and only if its relative
dimension is identically `0`. -/
theorem isZero_iff_forall_relativeDimension_eq_zero (A : AbelianScheme S) :
    IsZero A ↔ ∀ s : S, A.relativeDimension s = 0 := by
  constructor
  · intro hA s
    rw [relativeDimension_eq_of_iso (hA.iso (isZeroIdentity S)) s, relativeDimension_identity]
  · intro h
    exact (isZeroIdentity S).of_iso (isoIdentityOfRelativeDimensionZero A h)

/-- On an abelian scheme of relative dimension `0` everywhere, multiplication by any integer `n` is
the identity morphism. -/
theorem mulBy_eq_id_of_forall_relativeDimension_eq_zero {A : AbelianScheme S}
    (h : ∀ s : S, A.relativeDimension s = 0) (n : ℤ) :
    A.mulBy n = 𝟙 A.toOver := by
  have : IsIso A.toOver.hom := isIso_toOver_hom_of_forall_relativeDimension_eq_zero A h
  apply Over.OverMorphism.ext
  rw [← cancel_mono A.toOver.hom, Over.w, Over.id_left, Category.id_comp]

/-- On an abelian scheme of relative dimension `0` everywhere, multiplication by any integer `n` is
an isomorphism. -/
theorem isIso_mulBy_of_forall_relativeDimension_eq_zero {A : AbelianScheme S}
    (h : ∀ s : S, A.relativeDimension s = 0) (n : ℤ) :
    IsIso (A.mulBy n) := by
  rw [mulBy_eq_id_of_forall_relativeDimension_eq_zero h n]
  infer_instance

end

end AbelianScheme

end AlgebraicGeometry

end TauCeti
