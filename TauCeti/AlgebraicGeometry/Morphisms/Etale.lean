/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
import TauCeti.AlgebraicGeometry.Morphisms.Flat.Rank
import TauCeti.RingTheory.TotallySplit

/-!
# Rational points of finite schemes over a field and étaleness

Let `f : X ⟶ Spec K` be a morphism from an affine scheme to the spectrum of a field. Its points
with values in `Spec K`, that is the sections of `f`, are the characters `Γ(X, ⊤) →ₐ[K] K` of its
coordinate ring (`AlgebraicGeometry.Scheme.Hom.pointsEquivAlgHom`).

When `f` is finite, a finite-dimensional `K`-algebra has at most as many characters as its
dimension, which is the rank of `f` (`AlgebraicGeometry.Scheme.Hom.finrank_eq_finrank_of_field`).
When `X` has at least that many points over `Spec K`, its coordinate ring is a finite product of
copies of `K` (`Algebra.IsFiniteSplit.of_finrank_le_card_algHom`), so `f` is étale. Conversely,
over a separably closed field a finite étale `K`-algebra is a finite product of copies of `K`, so a
finite étale scheme over `Spec K` has exactly as many points over `Spec K` as its rank.

Points over `Spec K` are written as morphisms `𝟙_ (Over (Spec K)) ⟶ Over.mk f` of the cartesian
monoidal category `Over (Spec K)`, as for the points of group schemes over `Spec K`.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.pointsEquivAlgHom`: for affine `X`, the points of `X` over
  `Spec K` are the characters of `Γ(X, ⊤)`.

## Main results

* `AlgebraicGeometry.Scheme.Hom.etale_iff_algebraEtale`: for affine `X`, `f : X ⟶ Spec K` is
  étale exactly when `Γ(X, ⊤)` is an étale `K`-algebra.
* `AlgebraicGeometry.Scheme.Hom.etale_of_finrank_le_natCard`: a finite morphism `f : X ⟶ Spec K`
  with at least `f.finrank s` points of `X` over `Spec K` is étale.
* `AlgebraicGeometry.Scheme.Hom.natCard_eq_finrank_of_etale`: over a separably closed field `K`,
  a finite étale morphism `f : X ⟶ Spec K` has exactly `f.finrank s` points of `X` over `Spec K`.
-/

public section

open CategoryTheory MonoidalCategory

universe u

namespace AlgebraicGeometry

variable {K : Type u} [Field K] {X : Scheme.{u}}

/-- The global sections of the inverse of `X ≅ Spec Γ(X, ⊤)`, for an affine scheme `X`. -/
theorem Scheme.isoSpec_inv_appTop (X : Scheme.{u}) [IsAffine X] :
    X.isoSpec.inv.appTop = (Scheme.ΓSpecIso Γ(X, ⊤)).inv := by
  have h : X.isoSpec.inv.appTop ≫ X.isoSpec.hom.appTop = 𝟙 _ := by
    rw [← Scheme.Hom.comp_appTop, Iso.hom_inv_id, Scheme.Hom.id_appTop]
  rw [← Iso.comp_hom_eq_id]
  simpa [Scheme.isoSpec] using h

/-- **The points of an affine scheme over a field are the characters of its coordinate ring.**
Let `f : X ⟶ Spec K` be a morphism from an affine scheme, and give `Γ(X, ⊤)` the `K`-algebra
structure of the map of global sections of `f` (the hypothesis `hf`). A point `x` of `X` over
`Spec K`, that is a section of `f`, corresponds to the character of `Γ(X, ⊤)` given by pulling back
functions along `x`. -/
noncomputable def Scheme.Hom.pointsEquivAlgHom (f : X ⟶ Spec (.of K)) [IsAffine X]
    [Algebra K Γ(X, ⊤)]
    (hf : algebraMap K Γ(X, ⊤) = ((Scheme.ΓSpecIso (.of K)).inv ≫ f.appTop).hom) :
    (𝟙_ (Over (Spec (.of K))) ⟶ Over.mk f) ≃ (Γ(X, ⊤) →ₐ[K] K) where
  toFun x :=
    { toRingHom := (x.left.appTop ≫ (Scheme.ΓSpecIso (.of K)).hom).hom
      commutes' c := by
        have hx : x.left ≫ f = 𝟙 _ := by simpa using Over.w x
        have h1 : (Scheme.ΓSpecIso (.of K)).inv ≫ f.appTop ≫ x.left.appTop ≫
            (Scheme.ΓSpecIso (.of K)).hom = 𝟙 _ := by
          rw [← Category.assoc f.appTop, ← Scheme.Hom.comp_appTop, hx, Scheme.Hom.id_appTop]
          simp
        simpa [hf] using congr($h1 c) }
  invFun φ := Over.homMk (Spec.map (CommRingCat.ofHom (φ : Γ(X, ⊤) →+* K)) ≫ X.isoSpec.inv) <| by
    -- `f` is the spectrum of the map of global sections, up to `X ≅ Spec Γ(X, ⊤)`
    have e : f = X.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap K Γ(X, ⊤))) := by
      rw [hf, CommRingCat.ofHom_hom, Spec.map_comp, Scheme.isoSpec_hom,
        ← Scheme.toSpecΓ_naturality_assoc, toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]
    have hφ : CommRingCat.ofHom (algebraMap K Γ(X, ⊤)) ≫
        CommRingCat.ofHom (φ : Γ(X, ⊤) →+* K) = 𝟙 _ := by
      ext c
      simp
    simp [e, ← Spec.map_comp, hφ]
  left_inv x := by
    refine Over.OverMorphism.ext (ext_of_isAffine (Y := X) ?_)
    simp only [Over.homMk_left]
    rw [Scheme.Hom.comp_appTop, X.isoSpec_inv_appTop, Iso.inv_comp_eq,
      ← cancel_mono (Scheme.ΓSpecIso (.of K)).hom, Scheme.ΓSpecIso_naturality]
    -- the algebra homomorphism `toFun x` is the ring homomorphism `x.left.appTop ≫ ΓSpecIso.hom`
    exact (Category.assoc _ _ _).symm
  right_inv φ := AlgHom.ext fun c ↦ by
    have h : (Spec.map (CommRingCat.ofHom (φ : Γ(X, ⊤) →+* K)) ≫ X.isoSpec.inv).appTop ≫
        (Scheme.ΓSpecIso (.of K)).hom = CommRingCat.ofHom (φ : Γ(X, ⊤) →+* K) := by
      rw [Scheme.Hom.comp_appTop, Category.assoc, Scheme.ΓSpecIso_naturality, X.isoSpec_inv_appTop]
      exact Iso.inv_hom_id_assoc _ _
    exact congr(CommRingCat.Hom.hom $h c)

/-- The character attached to a point `x` of `X` over `Spec K` pulls back functions along `x`. -/
theorem Scheme.Hom.pointsEquivAlgHom_apply (f : X ⟶ Spec (.of K)) [IsAffine X] [Algebra K Γ(X, ⊤)]
    (hf : algebraMap K Γ(X, ⊤) = ((Scheme.ΓSpecIso (.of K)).inv ≫ f.appTop).hom)
    (x : 𝟙_ (Over (Spec (.of K))) ⟶ Over.mk f) (c : Γ(X, ⊤)) :
    f.pointsEquivAlgHom hf x c = (Scheme.ΓSpecIso (.of K)).hom (x.left.appTop c) :=
  (rfl)

/-- The point attached to a character `φ` of `Γ(X, ⊤)` is `Spec φ`, read through
`X ≅ Spec Γ(X, ⊤)`. -/
theorem Scheme.Hom.pointsEquivAlgHom_symm_apply_left (f : X ⟶ Spec (.of K)) [IsAffine X]
    [Algebra K Γ(X, ⊤)]
    (hf : algebraMap K Γ(X, ⊤) = ((Scheme.ΓSpecIso (.of K)).inv ≫ f.appTop).hom)
    (φ : Γ(X, ⊤) →ₐ[K] K) :
    ((f.pointsEquivAlgHom hf).symm φ).left =
      Spec.map (CommRingCat.ofHom (φ : Γ(X, ⊤) →+* K)) ≫ X.isoSpec.inv :=
  (rfl)

/-- A morphism `f : X ⟶ Spec K` from an affine scheme is étale exactly when its coordinate ring
`Γ(X, ⊤)` is an étale `K`-algebra, for the `K`-algebra structure given by the map of global
sections of `f`. -/
theorem Scheme.Hom.etale_iff_algebraEtale (f : X ⟶ Spec (.of K)) [IsAffine X] [Algebra K Γ(X, ⊤)]
    (hf : algebraMap K Γ(X, ⊤) = ((Scheme.ΓSpecIso (.of K)).inv ≫ f.appTop).hom) :
    Etale f ↔ Algebra.Etale K Γ(X, ⊤) := by
  -- the map of global sections of `f` is `algebraMap K Γ(X, ⊤)` up to `Γ(Spec K, ⊤) ≅ K`
  have hf' : f.appTop =
      (Scheme.ΓSpecIso (.of K)).hom ≫ CommRingCat.ofHom (algebraMap K Γ(X, ⊤)) := by
    simp [hf]
  rw [HasRingHomProperty.iff_of_isAffine (P := @Etale), hf', CommRingCat.hom_comp,
    RingHom.Etale.respectsIso.cancel_left_isIso, CommRingCat.hom_ofHom, RingHom.etale_algebraMap]

/-- **A finite scheme over a field with as many rational points as its degree is étale.** Let
`f : X ⟶ Spec K` be finite. If `X` has at least `f.finrank s` points over `Spec K`, then `f` is
étale: the coordinate ring of `X` is a finite product of copies of `K`. -/
theorem Scheme.Hom.etale_of_finrank_le_natCard (f : X ⟶ Spec (.of K)) [IsFinite f]
    (s : Spec (.of K)) (h : f.finrank s ≤ Nat.card (𝟙_ (Over (Spec (.of K))) ⟶ Over.mk f)) :
    Etale f := by
  have : IsAffine X := isAffine_of_isAffineHom f
  let := ((Scheme.ΓSpecIso (.of K)).inv ≫ f.appTop).hom.toAlgebra
  have hf : algebraMap K Γ(X, ⊤) = ((Scheme.ΓSpecIso (.of K)).inv ≫ f.appTop).hom := rfl
  have : Module.Finite K Γ(X, ⊤) := f.moduleFinite_appTop hf
  have : Algebra.IsFiniteSplit K Γ(X, ⊤) := .of_finrank_le_card_algHom <| by
    rw [← f.finrank_eq_finrank_of_field hf s, ← Nat.card_congr (f.pointsEquivAlgHom hf)]
    exact h
  exact (f.etale_iff_algebraEtale hf).2 inferInstance

/-- **A finite étale scheme over a separably closed field has as many rational points as its
degree.** Let `K` be separably closed and `f : X ⟶ Spec K` finite étale. Then `X` has exactly
`f.finrank s` points over `Spec K`: its coordinate ring is a finite product of copies of `K`. -/
theorem Scheme.Hom.natCard_eq_finrank_of_etale [IsSepClosed K] (f : X ⟶ Spec (.of K))
    [IsFinite f] [Etale f] (s : Spec (.of K)) :
    Nat.card (𝟙_ (Over (Spec (.of K))) ⟶ Over.mk f) = f.finrank s := by
  have : IsAffine X := isAffine_of_isAffineHom f
  let := ((Scheme.ΓSpecIso (.of K)).inv ≫ f.appTop).hom.toAlgebra
  have hf : algebraMap K Γ(X, ⊤) = ((Scheme.ΓSpecIso (.of K)).inv ≫ f.appTop).hom := rfl
  have : Module.Finite K Γ(X, ⊤) := f.moduleFinite_appTop hf
  have : Algebra.Etale K Γ(X, ⊤) := (f.etale_iff_algebraEtale hf).1 ‹_›
  -- so `Γ(X, ⊤) ≃ₐ[K] Fin m → K`, which has the `m` characters given by the coordinates
  obtain ⟨m, ⟨e⟩⟩ := Algebra.IsFiniteSplit.nonempty_algEquiv_fun K Γ(X, ⊤)
  rw [Nat.card_congr (f.pointsEquivAlgHom hf), f.finrank_eq_finrank_of_field hf s]
  refine le_antisymm (card_algHom_le_finrank K Γ(X, ⊤) K) ?_
  have := Finite.algHom K Γ(X, ⊤) K
  rw [e.toLinearEquiv.finrank_eq, Module.finrank_fin_fun]
  refine (Nat.card_fin m).symm.le.trans
    (Nat.card_le_card_of_injective (fun i ↦ (Pi.evalAlgHom K (fun _ ↦ K) i).comp e.toAlgHom) ?_)
  intro i j hij
  have := congr($hij (e.symm (Pi.single i 1)))
  by_contra hne
  simp [hne] at this

end AlgebraicGeometry
