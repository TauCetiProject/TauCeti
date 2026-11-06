/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Sites.Nisnevich.Basic
public import TauCeti.RingTheory.Henselization.IndEtale
public import TauCeti.RingTheory.Henselization.Local
import TauCeti.RingTheory.Henselian.Section

/-!
# Nisnevich coverings and henselizations of local rings

A morphism `Spec A ⟶ X` from the spectrum of a local ring `A` is a point `x` of `X` with a local
homomorphism `𝒪_{X,x} → A`. When `A` is henselian, such a morphism lifts along every étale
morphism `f : U ⟶ X` which has a point `u` over `x` with `κ(x) ≅ κ(u)`. Conversely, a lift of
`Spec 𝒪ʰ_{X,x} ⟶ X` along `f`, where `𝒪ʰ_{X,x}` is the henselization of the local ring at `x`,
produces such a point. Hence a family of étale morphisms is a Nisnevich covering exactly when
every morphism `Spec 𝒪ʰ_{X,x} ⟶ X` lifts to one of its members.

## Main definitions

* `TauCeti.AlgebraicGeometry.Scheme.henselization X x`: the henselization `𝒪ʰ_{X,x}` of the local
  ring of `X` at `x`, along its maximal ideal.
* `TauCeti.AlgebraicGeometry.Scheme.toHenselization X x`: the structure map
  `𝒪_{X,x} → 𝒪ʰ_{X,x}`.
* `TauCeti.AlgebraicGeometry.Scheme.fromSpecHenselization X x`: the canonical morphism
  `Spec 𝒪ʰ_{X,x} ⟶ X`.

## Main results

* `TauCeti.AlgebraicGeometry.Scheme.exists_lift_of_isIso_residueFieldMap`: morphisms from the
  spectrum of a henselian local ring lift along étale morphisms through a point with unchanged
  residue field.
* `TauCeti.AlgebraicGeometry.Scheme.isIso_residueFieldMap_of_lift`: a lift of a morphism
  `Spec A ⟶ X` inducing an isomorphism of residue fields passes through a point with unchanged
  residue field.
* `TauCeti.AlgebraicGeometry.Scheme.indEtale_henselization`: `𝒪ʰ_{X,x}` is ind-étale over the
  sections of every affine open containing `x`.
* `TauCeti.AlgebraicGeometry.Scheme.isNisnevichCovering_iff_henselization`: a family of étale
  morphisms is a Nisnevich covering if and only if, for every point `x`, the morphism
  `Spec 𝒪ʰ_{X,x} ⟶ X` lifts to one of its members, that is, the base change of one member to
  `Spec 𝒪ʰ_{X,x}` has a section.

## Implementation notes

The roadmap states the criterion for finite families over a Noetherian base, in terms of a
section of the base change of the family. Neither hypothesis is needed for the form proved
here, in which the section of the base change of one member is recorded as a lift.

## References

* F. Morel and V. Voevodsky, *𝔸¹-homotopy theory of schemes*, Publ. Math. IHÉS 90 (1999),
  §3.1, Proposition 1.1.
* [Stacks Project, Lemma 15.11.6](https://stacks.math.columbia.edu/tag/09XI)
-/

public section

open CategoryTheory Limits AlgebraicGeometry IsLocalRing

universe u

namespace TauCeti.AlgebraicGeometry.Scheme

variable {X U : Scheme.{u}}

/-- Morphisms from the spectrum of a henselian local ring lift along étale morphisms through a
point with unchanged residue field: if `f : U ⟶ X` is étale, `κ(f u) ≅ κ(u)`, and `A` is a
henselian local ring with a local homomorphism `φ : 𝒪_{X, f u} → A`, then the morphism
`Spec A ⟶ X` given by `φ` factors through `f`. -/
theorem exists_lift_of_isIso_residueFieldMap (f : U ⟶ X) [Etale f] (u : U)
    [IsIso (f.residueFieldMap u)] {A : Type u} [CommRing A] [HenselianLocalRing A]
    (φ : X.presheaf.stalk (f u) ⟶ CommRingCat.of A) [IsLocalHom φ.hom] :
    ∃ s : Spec (.of A) ⟶ U, s ≫ f = Spec.map φ ≫ X.fromSpecStalk (f u) := by
  -- Choose affine opens `W ∋ f u` and `V ∋ u` with `f(V) ⊆ W`.
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, -⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (f u)) isOpen_univ
  obtain ⟨_, ⟨V, hV, rfl⟩, huV, hVW⟩ := U.isBasis_affineOpens.exists_subset_of_mem_open
    (show u ∈ f ⁻¹ᵁ W from hxW) (f ⁻¹ᵁ W).isOpen
  have e : V ≤ f ⁻¹ᵁ W := hVW
  -- On sections, `f` is an étale ring map `Γ(X, W) → Γ(U, V)`.
  have ha : (f.appLE W V e).hom.Etale :=
    HasRingHomProperty.appLE (P := @Etale) f ‹_› ⟨W, hW⟩ ⟨V, hV⟩ e
  let ψ : Γ(X, W) ⟶ CommRingCat.of A := X.presheaf.germ W (f u) hxW ≫ φ
  let : Algebra Γ(X, W) Γ(U, V) := (f.appLE W V e).hom.toAlgebra
  let : Algebra Γ(X, W) A := ψ.hom.toAlgebra
  have : Algebra.Etale Γ(X, W) Γ(U, V) := ha
  -- Evaluation at `u`, followed by `κ(u) ≅ κ(f u) → κ(A)`, is a section modulo `𝔪_A`.
  let ρ : Γ(U, V) →ₐ[Γ(X, W)] A ⧸ maximalIdeal A :=
    { toRingHom := (U.evaluation V u huV ≫ inv (f.residueFieldMap u) ≫
        CommRingCat.ofHom (ResidueField.map φ.hom)).hom
      commutes' r := by
        -- Evaluation at `u` of `f^* r` is the image of the value of `r` at `f u`.
        have key : U.evaluation V u huV (f.appLE W V e r) =
            f.residueFieldMap u (X.evaluation W (f u) hxW r) := by
          rw [Scheme.evaluation_naturality_apply, Scheme.Hom.appLE]
          simp [Scheme.evaluation]
        have hinv : inv (f.residueFieldMap u) (f.residueFieldMap u (X.evaluation W (f u) hxW r)) =
            X.evaluation W (f u) hxW r := by
          rw [← CommRingCat.comp_apply, IsIso.hom_inv_id, CommRingCat.id_apply]
        -- Unfold the bundled composite defining `ρ` and the algebra map `Γ(X, W) → A ⧸ 𝔪_A`,
        -- which is `ψ` followed by the quotient map, so that `key` applies.
        change ResidueField.map φ.hom (inv (f.residueFieldMap u)
          (U.evaluation V u huV (f.appLE W V e r))) =
            Ideal.Quotient.mk _ (φ (X.presheaf.germ W (f u) hxW r))
        rw [key, hinv]
        exact ResidueField.map_residue _ _ }
  obtain ⟨χ, -⟩ := (HenselianRing.comp_bijective_of_algebra (maximalIdeal A)).2 ρ
  refine ⟨Spec.map (CommRingCat.ofHom χ.toRingHom) ≫ hV.fromSpec, ?_⟩
  rw [Category.assoc, ← IsAffineOpen.SpecMap_appLE_fromSpec f hW hV e, ← Category.assoc,
    ← Spec.map_comp, ← hW.fromSpecStalk_eq_fromSpecStalk hxW]
  unfold IsAffineOpen.fromSpecStalk
  rw [← Category.assoc, ← Spec.map_comp]
  congr 2
  ext r
  exact χ.commutes r

/-- A lift of a morphism `Spec A ⟶ X` inducing an isomorphism of residue fields passes through a
point with unchanged residue field: if `A` is local, `φ : 𝒪_{X,x} → A` is a local homomorphism
inducing an isomorphism of residue fields, and `s : Spec A ⟶ U` lifts the morphism
`Spec A ⟶ X` given by `φ` along `f`, then `s` maps the closed point to a preimage of `x` at which
`f` induces an isomorphism of residue fields. -/
theorem isIso_residueFieldMap_of_lift (f : U ⟶ X) {x : X} {A : Type u} [CommRing A]
    [IsLocalRing A] (φ : X.presheaf.stalk x ⟶ CommRingCat.of A) [IsLocalHom φ.hom]
    (hφ : Function.Bijective (ResidueField.map φ.hom)) (s : Spec (.of A) ⟶ U)
    (hs : s ≫ f = Spec.map φ ≫ X.fromSpecStalk x) :
    f (s (closedPoint A)) = x ∧ IsIso (f.residueFieldMap (s (closedPoint A))) := by
  -- Read off the point and the local homomorphism of `s ≫ f` from `Spec A`.
  have h := (AlgebraicGeometry.SpecToEquivOfLocalRing X (.of A)).apply_symm_apply
    ⟨x, φ, ‹_›⟩
  rw [show (AlgebraicGeometry.SpecToEquivOfLocalRing X (.of A)).symm ⟨x, φ, ‹_›⟩ =
    s ≫ f from hs.symm] at h
  obtain ⟨hx, hφ'⟩ := AlgebraicGeometry.SpecToEquivOfLocalRing_eq_iff.mp h
  -- The components of `SpecToEquivOfLocalRing` are by definition the image of the closed point
  -- and `stalkClosedPointTo`.
  change f (s (closedPoint A)) = x at hx
  subst hx
  change AlgebraicGeometry.Scheme.stalkClosedPointTo (s ≫ f) = _ ≫ φ at hφ'
  rw [AlgebraicGeometry.Scheme.stalkClosedPointTo_comp, TopCat.Presheaf.stalkCongr_hom] at hφ'
  -- The specialization `x ⤳ x` in `hφ'` is stated for `(s ≫ f) c` rather than `f (s c)`, so
  -- `stalkSpecializes_refl` only matches up to unfolding the composite.
  erw [TopCat.Presheaf.stalkSpecializes_refl, Category.id_comp] at hφ'
  -- `κ(f (s c)) → κ(s c) → κ(A)` is the bijection induced by `φ`.
  have key (y) : ResidueField.map (AlgebraicGeometry.Scheme.stalkClosedPointTo s).hom
      (f.residueFieldMap (s (closedPoint A)) y) = ResidueField.map φ.hom y := by
    obtain ⟨y, rfl⟩ := residue_surjective y
    -- `f.residueFieldMap` is by definition the map of residue fields induced by `f.stalkMap`.
    change ResidueField.map _ (ResidueField.map _ (residue _ y)) = ResidueField.map _ (residue _ y)
    rw [ResidueField.map_residue, ResidueField.map_residue, ResidueField.map_residue,
      ← CommRingCat.comp_apply, hφ']
  refine ⟨rfl, (ConcreteCategory.isIso_iff_bijective _).mpr ⟨RingHom.injective _, ?_⟩⟩
  refine Function.Surjective.of_comp_left (f := ResidueField.map
    (AlgebraicGeometry.Scheme.stalkClosedPointTo s).hom) (fun z ↦ ?_) (RingHom.injective _)
  obtain ⟨y, rfl⟩ := hφ.2 z
  exact ⟨y, key y⟩

/-- The henselization `𝒪ʰ_{X,x}` of the local ring `𝒪_{X,x}` of a scheme at a point, along its
maximal ideal. -/
noncomputable abbrev henselization (X : Scheme.{u}) (x : X) : CommRingCat.{u} :=
  .of (Henselization.algebra (maximalIdeal (X.presheaf.stalk x)))

/-- The structure map `𝒪_{X,x} → 𝒪ʰ_{X,x}`. -/
noncomputable abbrev toHenselization (X : Scheme.{u}) (x : X) :
    X.presheaf.stalk x ⟶ henselization X x :=
  CommRingCat.ofHom (algebraMap (X.presheaf.stalk x)
    (Henselization.algebra (maximalIdeal (X.presheaf.stalk x))))

/-- The structure map `𝒪_{X,x} → 𝒪ʰ_{X,x}` is a local homomorphism. -/
instance (X : Scheme.{u}) (x : X) : IsLocalHom (toHenselization X x).hom :=
  Henselization.isLocalHom_algebraMap _

/-- The sections of `X` over an open `W` act on the henselization at a point of `W` through the
local ring at that point. -/
noncomputable instance (W : X.Opens) (x : W) : Algebra Γ(X, W) (henselization X x) :=
  (X.presheaf.germ W x x.2 ≫ toHenselization X x).hom.toAlgebra

/-- The action of `Γ(X, W)` on `𝒪ʰ_{X,x}` factors through the local ring `𝒪_{X,x}`. -/
instance (W : X.Opens) (x : W) :
    IsScalarTower Γ(X, W) (X.presheaf.stalk x) (henselization X x) :=
  .of_algebraMap_eq fun _ ↦ rfl

/-- The henselization `𝒪ʰ_{X,x}` is ind-étale over the ring of sections of every affine open
containing `x`: it is the henselization of a localization of that ring. -/
theorem indEtale_henselization {W : X.Opens} (hW : IsAffineOpen W) (x : W) :
    Algebra.IndEtale Γ(X, W) (henselization X x) :=
  have := hW.isLocalization_stalk x
  have : Algebra.IndEtale Γ(X, W) (X.presheaf.stalk x) :=
    .of_isLocalization (hW.primeIdealOf x).asIdeal.primeCompl
  have : Algebra.IndEtale (X.presheaf.stalk x) (henselization X x) :=
    Henselization.indEtale _
  .comp (S := X.presheaf.stalk x) _

/-- The canonical morphism `Spec 𝒪ʰ_{X,x} ⟶ X`, through `Spec 𝒪_{X,x}`. -/
noncomputable def fromSpecHenselization (X : Scheme.{u}) (x : X) :
    Spec (henselization X x) ⟶ X :=
  Spec.map (toHenselization X x) ≫ X.fromSpecStalk x

/-- **The henselization criterion for Nisnevich coverings.** A family of étale morphisms
`{fᵢ : Xᵢ ⟶ S}` is a Nisnevich covering if and only if, for every point `s` of `S`, the morphism
`Spec 𝒪ʰ_{S,s} ⟶ S` lifts to some `Xᵢ`; equivalently, the base change of some `fᵢ` to
`Spec 𝒪ʰ_{S,s}` has a section. Morel–Voevodsky, §3.1, Proposition 1.1. -/
theorem isNisnevichCovering_iff_henselization {S : Scheme.{u}} {ι : Type*} {X : ι → Scheme.{u}}
    (f : ∀ i, X i ⟶ S) :
    IsNisnevichCovering f ↔ (∀ i, Etale (f i)) ∧
      ∀ s : S, ∃ i, ∃ t : Spec (henselization S s) ⟶ X i, t ≫ f i = fromSpecHenselization S s := by
  refine ⟨fun hf ↦ ⟨hf.etale, fun s ↦ ?_⟩, fun ⟨hf, h⟩ ↦ ⟨hf, fun s ↦ ?_⟩⟩
  · obtain ⟨i, x, rfl, hx⟩ := hf.exists_isIso s
    have := hf.etale i
    obtain ⟨t, ht⟩ := exists_lift_of_isIso_residueFieldMap (f i) x (toHenselization S (f i x))
    exact ⟨i, t, ht⟩
  · obtain ⟨i, t, ht⟩ := h s
    obtain ⟨hx, hiso⟩ := isIso_residueFieldMap_of_lift (f i) (toHenselization S s)
      (Henselization.residueField_map_bijective _) t ht
    exact ⟨i, _, hx, hiso⟩

end TauCeti.AlgebraicGeometry.Scheme
