/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Differentials.Basic
public import TauCeti.AlgebraicGeometry.Modules.Tilde.Basic
public import TauCeti.RingTheory.Derivation.Localization

/-!
# Relative differentials of an affine scheme

Let `A` be an algebra over a commutative ring `R`. The sheaf of relative differentials of
`Spec A` over `R` is the quasi-coherent sheaf associated with the module of Kähler differentials:
`Ω_{Spec A/R} ≅ Ω[A⁄R]~`, with `d a ↦ D a` on the sections coming from `A`. In particular
`Ω_{Spec A/R}` is quasi-coherent, and its global sections are the Kähler differentials `Ω[A⁄R]`.
This is the local computation behind the identification of `Ω_{X/k}` with a line bundle on a
smooth curve `X` over a field `k`.

Both sheaves carry an `R`-derivation of `𝒪_{Spec A}`, and the isomorphism compares them.

* The sheaf `Ω[A⁄R]~` receives a derivation `𝒪_{Spec A} → Ω[A⁄R]~` extending `D : A → Ω[A⁄R]`.
  On a basic open `D(f)` the ring of sections is the localization `A_f`, and `D` extends uniquely
  to `A_f` by the quotient rule (`Derivation.extendOfIsLocalization`). By uniqueness these
  extensions are compatible with restriction, so they glue along the basis of basic opens. The
  universal property of `Ω_{Spec A/R}` turns this derivation into a morphism
  `Ω_{Spec A/R} ⟶ Ω[A⁄R]~`.
* Conversely, the global component of the universal derivation is an `R`-derivation
  `A → Γ(Spec A, Ω_{Spec A/R})`. It corresponds to an `A`-linear map
  `Ω[A⁄R] → Γ(Spec A, Ω_{Spec A/R})`, hence by the adjunction between `M ↦ M~` and global
  sections to a morphism `Ω[A⁄R]~ ⟶ Ω_{Spec A/R}`.

The two composites are identities because an `R`-derivation of `𝒪_{Spec A}` is determined by its
values on the global sections coming from `A` (`Scheme.Modules.Derivation.Spec_ext`): on a basic
open `D(f)` every section is a fraction `a / fⁿ`, whose derivative is forced by the Leibniz rule.

## Main declarations

* `TauCeti.AlgebraicGeometry.relativeDifferentialsSpecIso R A`: the isomorphism
  `Ω_{Spec A/R} ≅ Ω[A⁄R]~`, characterized by `relativeDifferentialsSpecIso_hom_app_d` and
  `relativeDifferentialsSpecIso_inv_app_toOpen`;
* `TauCeti.AlgebraicGeometry.isQuasicoherent_relativeDifferentials_Spec`: `Ω_{Spec A/R}` is
  quasi-coherent;
* `TauCeti.AlgebraicGeometry.Scheme.Modules.Derivation.Spec_ext`: an `R`-derivation of
  `𝒪_{Spec A}` is determined by its values on the global sections coming from `A`.

## References

* R. Hartshorne, *Algebraic Geometry*, Section II.8.
* The Stacks Project, *Morphisms of Schemes*, Section *Sheaf of differential forms*.
-/

public section

open CategoryTheory Opposite TopologicalSpace

namespace TauCeti

namespace AlgebraicGeometry

open _root_.AlgebraicGeometry
open Scheme.Modules.Derivation

universe u

noncomputable section

variable (R : Type u) [CommRing R] (A : CommRingCat.{u}) [Algebra R A]


/-- The basic open `D(f)`, as an open of the scheme `Spec A`. -/
private abbrev basicOpen (f : A) : (Spec A).Opens := PrimeSpectrum.basicOpen f

private instance (f : A) : IsLocalization.Away f Γ(Spec A, basicOpen A f) := by
  -- `basicOpen A f` unfolds to Mathlib's basic open, for which the instance is stated.
  unfold basicOpen
  infer_instance

variable {R A} in
/-- An `R`-derivation of `𝒪_{Spec A}` is determined by its values on the global sections coming
from `A`. -/
theorem Scheme.Modules.Derivation.Spec_ext {M : (Spec A).Modules}
    {d₁ d₂ : M.Derivation R}
    (h : ∀ a : A, d₁.d (X := op ⊤) (algebraMap A Γ(Spec A, ⊤) a) =
      d₂.d (X := op ⊤) (algebraMap A Γ(Spec A, ⊤) a)) :
    d₁ = d₂ := by
  -- It suffices to compare the derivations on each basic open `D(f)`, where every section is a
  -- fraction `a / fⁿ` whose derivative the Leibniz rule determines from those of `a` and `f`.
  ext U s
  refine Scheme.Modules.section_ext_basicOpen (U := U.unop) fun f hf ↦ ?_
  -- `d_map` is stated with the restriction maps of the underlying presheaves of the derivations.
  erw [← d₁.d_map, ← d₂.d_map]
  refine congrFun (IsLocalization.eq_of_leibniz (.powers f)
    (T := Γ(Spec A, basicOpen A f)) (δ₁ := fun t ↦ d₁.d t)
    (δ₂ := fun t ↦ d₂.d t) (fun x y ↦ d₁.d_mul x y) (fun x y ↦ d₂.d_mul x y) fun a ↦ ?_) _
  -- The image of `a` in the sections over `D(f)` is the restriction of its global image.
  erw [d₁.d_map (homOfLE le_top).op (algebraMap A Γ(Spec A, ⊤) a),
    d₂.d_map (homOfLE le_top).op (algebraMap A Γ(Spec A, ⊤) a), h]

/-! ### The derivation of `𝒪_{Spec A}` into `Ω[A⁄R]~` -/

/-- The structure map `Ω[A⁄R] → Γ(Ω[A⁄R]~, U)`, with codomain the sections of a sheaf of
modules on `Spec A`. -/
private def toOpenₗ (U : (Spec A).Opens) : Ω[A⁄R] →ₗ[A] Γ(tilde (.of A Ω[A⁄R]), U) :=
  (tilde.toOpen (ModuleCat.of A Ω[A⁄R]) U).hom

/-- On an open `U` whose ring of sections is a localization of `A`, the derivation
`Γ(Spec A, U) → Γ(Ω[A⁄R]~, U)` extending `D : A → Ω[A⁄R]`. -/
private def localDerivation (U : (Spec A).Opens) (S : Submonoid A)
    [IsLocalization S Γ(Spec A, U)] : Derivation ℤ Γ(Spec A, U) Γ(tilde (.of A Ω[A⁄R]), U) :=
  Derivation.extendOfIsLocalization S
    ((toOpenₗ R A U).compDer ((KaehlerDifferential.D R A).restrictScalars ℤ))

private lemma localDerivation_algebraMap (U : (Spec A).Opens) (S : Submonoid A)
    [IsLocalization S Γ(Spec A, U)] (a : A) :
    localDerivation R A U S (algebraMap A _ a) =
      tilde.toOpen (ModuleCat.of A Ω[A⁄R]) U (KaehlerDifferential.D R A a) := by
  rw [localDerivation, Derivation.extendOfIsLocalization_algebraMap]
  -- The derivation of `A` being extended is `D` followed by `toOpenₗ`, which is `tilde.toOpen`.
  rfl

/-- The derivations on basic opens are compatible with restriction. -/
private lemma localDerivation_naturality {f g : A} (i : basicOpen A g ⟶ basicOpen A f)
    (t : Γ(Spec A, basicOpen A f)) :
    (tilde (.of A Ω[A⁄R])).presheaf.map i.op (localDerivation R A _ (.powers f) t) =
      localDerivation R A _ (.powers g) ((Spec A).presheaf.map i.op t) := by
  -- Both sides satisfy the Leibniz rule on `A_f`, acting on `Γ(Ω[A⁄R]~, D(g))` through
  -- restriction, and they agree on `A`.
  let : Module Γ(Spec A, basicOpen A f) Γ(tilde (.of A Ω[A⁄R]), basicOpen A g) :=
    Module.compHom _ ((Spec A).presheaf.map i.op).hom
  refine congrFun (IsLocalization.eq_of_leibniz (.powers f) (T := Γ(Spec A, basicOpen A f))
    (δ₁ := fun t ↦ (tilde (.of A Ω[A⁄R])).presheaf.map i.op (localDerivation R A _ (.powers f) t))
    (δ₂ := fun t ↦ localDerivation R A _ (.powers g) ((Spec A).presheaf.map i.op t))
    (fun x y ↦ ?_) (fun x y ↦ ?_) fun a ↦ ?_) t
  · rw [Derivation.leibniz, map_add, Scheme.Modules.map_smul, Scheme.Modules.map_smul]
    -- The action of `Γ(D(f))` on `Γ(Ω[A⁄R]~, D(g))` is through restriction.
    rfl
  · rw [map_mul, Derivation.leibniz]
    rfl
  · -- Restriction carries the image of `a` in `Γ(D(f))` to its image in `Γ(D(g))`.
    change _ = localDerivation R A _ (.powers g) (algebraMap A _ a)
    rw [localDerivation_algebraMap, localDerivation_algebraMap]
    exact congr($(tilde.toOpen_res (ModuleCat.of A Ω[A⁄R]) _ _ i) (KaehlerDifferential.D R A a))

/-- The derivations on basic opens, as a morphism of presheaves of abelian groups on the basis of
basic opens. -/
private def basicOpenNatTrans :
    (inducedFunctor (basicOpen A)).op ⋙
        ((Spec A).presheaf ⋙ forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat) ⟶
      (inducedFunctor (basicOpen A)).op ⋙ (tilde (.of A Ω[A⁄R])).presheaf where
  app f := AddCommGrpCat.ofHom
    (localDerivation R A (basicOpen A f.unop) (.powers f.unop)).toAddMonoidHom
  naturality _ _ i := by
    ext t
    exact (localDerivation_naturality R A i.unop.hom t).symm

/-- The derivations on basic opens, glued to a morphism of presheaves of abelian groups
`𝒪_{Spec A} ⟶ Ω[A⁄R]~`. -/
private def gluedHom :
    (Spec A).presheaf ⋙ forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat ⟶
      (tilde (.of A Ω[A⁄R])).presheaf :=
  TopCat.Sheaf.restrictHomEquivHom _ ⟨_, (tilde (.of A Ω[A⁄R])).isSheaf⟩
    PrimeSpectrum.isBasis_basic_opens (basicOpenNatTrans R A)

private lemma gluedHom_restrict {U : (Spec A).Opensᵒᵖ} (f : A) (hf : basicOpen A f ≤ U.unop)
    (s : (Spec A).presheaf.obj U) :
    (tilde (.of A Ω[A⁄R])).presheaf.map (homOfLE hf).op ((gluedHom R A).app U s) =
      localDerivation R A _ (.powers f) ((Spec A).presheaf.map (homOfLE hf).op s) := by
  rw [← ConcreteCategory.comp_apply, ← (gluedHom R A).naturality, ConcreteCategory.comp_apply]
  -- On a basic open, the glued morphism is the derivation it was glued from. The basis is
  -- indexed through `basicOpen A`, which `rw` does not see through.
  erw [TopCat.Sheaf.extend_hom_app]
  rfl

private lemma gluedHom_mul (U : (Spec A).Opens) (a b : Γ(Spec A, U)) :
    (gluedHom R A).app (op U) (a * b) =
      a • (gluedHom R A).app (op U) b + b • (gluedHom R A).app (op U) a := by
  refine Scheme.Modules.section_ext_basicOpen fun f hf ↦ ?_
  -- The basis lemma uses spectrum opens; `erw` identifies them with scheme opens.
  erw [gluedHom_restrict, map_add, Scheme.Modules.map_smul, Scheme.Modules.map_smul,
    gluedHom_restrict, gluedHom_restrict, map_mul, Derivation.leibniz]

private lemma gluedHom_baseRing (U : (Spec A).Opensᵒᵖ) (r : R) :
    (gluedHom R A).app U ((Scheme.baseRingToStructurePresheaf R (Spec A)).app U r) = 0 := by
  refine Scheme.Modules.section_ext_basicOpen fun f hf ↦ ?_
  -- The basis lemma uses spectrum opens; `erw` identifies them with scheme opens.
  erw [gluedHom_restrict, Scheme.baseRingToStructurePresheaf_Spec_app_apply]
  -- Restriction carries the image of `algebraMap R A r` to its image over `D(f)`.
  change localDerivation R A _ _ (algebraMap A _ _) = _
  rw [localDerivation_algebraMap]
  simp only [Derivation.map_algebraMap, map_zero]
  -- The two zeros are those of definitionally equal types of sections.
  rfl

/-- The `R`-derivation `𝒪_{Spec A} → Ω[A⁄R]~` extending `D : A → Ω[A⁄R]`. -/
private def tildeDerivation : (tilde (.of A Ω[A⁄R])).Derivation R :=
  PresheafOfModulesOfCommRing.Derivation'.mk
    (fun U ↦ ModuleCat.Derivation.mk (fun s ↦ (gluedHom R A).app U s) (fun _ _ ↦ map_add _ _ _)
      (gluedHom_mul R A U.unop) (gluedHom_baseRing R A U))
    (fun _ _ i s ↦ ConcreteCategory.congr_hom ((gluedHom R A).naturality i) s)

private lemma tildeDerivation_d_algebraMap (U : (Spec A).Opens) (a : A) :
    (tildeDerivation R A).d (X := op U) (algebraMap A Γ(Spec A, U) a) =
      tilde.toOpen (ModuleCat.of A Ω[A⁄R]) U (KaehlerDifferential.D R A a) := by
  refine Scheme.Modules.section_ext_basicOpen fun f hf ↦ ?_
  -- The derivation `tildeDerivation` is `gluedHom` on sections.
  erw [gluedHom_restrict]
  -- Restriction carries the image of `a` in `Γ(U)` to its image in `Γ(D(f))`.
  change localDerivation R A _ _ (algebraMap A _ a) = _
  rw [localDerivation_algebraMap]
  exact (congr($(tilde.toOpen_res (ModuleCat.of A Ω[A⁄R]) _ _ (homOfLE hf))
    (KaehlerDifferential.D R A a))).symm

/-! ### The comparison isomorphism -/

/-- The morphism `Ω[A⁄R]~ ⟶ Ω_{Spec A/R}` adjoint to the `A`-linear map
`Ω[A⁄R] → Γ(Spec A, Ω_{Spec A/R})` classifying the global component of the universal
derivation. -/
private def fromTilde : tilde (.of A Ω[A⁄R]) ⟶ (Spec A).relativeDifferentials R :=
  ((tilde.adjunction (R := A)).homEquiv _ _).symm
    (ModuleCat.ofHom (Y := moduleSpecΓFunctor.obj ((Spec A).relativeDifferentials R))
      (globalDerivation R A ((Spec A).universalDerivation R)).liftKaehlerDifferential)

private lemma fromTilde_toOpen (ω : Ω[A⁄R]) :
    (fromTilde R A).val.app (op ⊤) (tilde.toOpen (ModuleCat.of A Ω[A⁄R]) ⊤ ω) =
      (globalDerivation R A ((Spec A).universalDerivation R)).liftKaehlerDifferential ω := by
  have := congr($(((tilde.adjunction (R := A)).homEquiv _ _).apply_symm_apply
    (ModuleCat.ofHom (Y := moduleSpecΓFunctor.obj ((Spec A).relativeDifferentials R))
      (globalDerivation R A ((Spec A).universalDerivation R)).liftKaehlerDifferential)) ω)
  rw [Adjunction.homEquiv_unit] at this
  exact this

/-- The morphism `Ω_{Spec A/R} ⟶ Ω[A⁄R]~` classifying the derivation `𝒪_{Spec A} → Ω[A⁄R]~`
extending `D`. -/
private def toTilde : (Spec A).relativeDifferentials R ⟶ tilde (.of A Ω[A⁄R]) :=
  ((Spec A).relativeDifferentialsHomEquiv R _).symm (tildeDerivation R A)

private lemma toTilde_universalDerivation (U : (Spec A).Opensᵒᵖ) (s : (Spec A).presheaf.obj U) :
    (toTilde R A).val.app U (((Spec A).universalDerivation R).d s) = (tildeDerivation R A).d s :=
  congr($(Scheme.relativeDifferentialsHomEquiv_symm_fac R (Spec A) (tildeDerivation R A)).d s)

private lemma toTilde_liftKaehlerDifferential (ω : Ω[A⁄R]) :
    (toTilde R A).val.app (op ⊤)
      ((globalDerivation R A ((Spec A).universalDerivation R)).liftKaehlerDifferential ω) =
      tilde.toOpen (ModuleCat.of A Ω[A⁄R]) ⊤ ω := by
  have hω : ω ∈ Submodule.span A (Set.range (KaehlerDifferential.D R A)) := by
    rw [KaehlerDifferential.span_range_derivation]
    trivial
  induction hω using Submodule.span_induction with
  | mem _ h =>
    obtain ⟨a, rfl⟩ := h
    rw [Derivation.liftKaehlerDifferential_comp_D, globalDerivation_apply]
    exact (toTilde_universalDerivation R A _ _).trans (tildeDerivation_d_algebraMap R A ⊤ a)
  | zero =>
    rw [map_zero, map_zero]
    exact map_zero _
  | add x y _ _ hx hy =>
    rw [map_add, map_add, ← hx, ← hy]
    exact map_add _ _ _
  | smul c x _ hx =>
    rw [map_smul, map_smul, ← hx]
    exact Scheme.Modules.Hom.app_smul (toTilde R A) (algebraMap A Γ(Spec A, ⊤) c) _

/-- The **sheaf of relative differentials of an affine scheme**: for an `R`-algebra `A`,
`Ω_{Spec A/R}` is the quasi-coherent sheaf `Ω[A⁄R]~` associated with the Kähler differentials,
with `d a ↦ D a` for `a ∈ A`. -/
def relativeDifferentialsSpecIso :
    (Spec A).relativeDifferentials R ≅ tilde (.of A Ω[A⁄R]) where
  hom := toTilde R A
  inv := fromTilde R A
  hom_inv_id := by
    apply ((Spec A).relativeDifferentialsHomEquiv R _).injective
    rw [Scheme.relativeDifferentialsHomEquiv_comp, toTilde, Equiv.apply_symm_apply,
      Scheme.relativeDifferentialsHomEquiv_apply]
    refine Scheme.Modules.Derivation.Spec_ext fun a ↦ ?_
    have hD := Derivation.liftKaehlerDifferential_comp_D
      (globalDerivation R A ((Spec A).universalDerivation R)) a
    rw [globalDerivation_apply] at hD
    exact (congrArg _ (tildeDerivation_d_algebraMap R A ⊤ a)).trans
      ((fromTilde_toOpen R A _).trans hD)
  inv_hom_id := tilde_hom_ext fun ω ↦
    (congrArg _ (fromTilde_toOpen R A ω)).trans (toTilde_liftKaehlerDifferential R A ω)

/-- The isomorphism `Ω_{Spec A/R} ≅ Ω[A⁄R]~` sends the differential `d a` of `a ∈ A` to the
section `D a` of `Ω[A⁄R]~`. -/
@[simp]
lemma relativeDifferentialsSpecIso_hom_app_d (U : (Spec A).Opens) (a : A) :
    (relativeDifferentialsSpecIso R A).hom.val.app (op U)
        (((Spec A).universalDerivation R).d
          (((Spec A).presheaf.map (homOfLE le_top).op).hom ((Scheme.ΓSpecIso A).inv.hom a))) =
      tilde.toOpen (ModuleCat.of A Ω[A⁄R]) U (KaehlerDifferential.D R A a) := by
  dsimp only [relativeDifferentialsSpecIso]
  simpa only [IsAffineOpen.algebraMap_Spec_obj, CommRingCat.hom_comp, RingHom.coe_comp,
    Function.comp_apply] using
    (toTilde_universalDerivation R A _ _).trans (tildeDerivation_d_algebraMap R A U a)

/-- The inverse of `Ω_{Spec A/R} ≅ Ω[A⁄R]~` sends the section `D a` of `Ω[A⁄R]~` to the
differential `d a`. -/
@[simp]
lemma relativeDifferentialsSpecIso_inv_app_toOpen (U : (Spec A).Opens) (a : A) :
    (relativeDifferentialsSpecIso R A).inv.val.app (op U)
        (tilde.toOpen (ModuleCat.of A Ω[A⁄R]) U (KaehlerDifferential.D R A a)) =
      ((Spec A).universalDerivation R).d (algebraMap A Γ(Spec A, U) a) := by
  rw [← relativeDifferentialsSpecIso_hom_app_d]
  exact congr($((relativeDifferentialsSpecIso R A).hom_inv_id).val.app (op U) _)

/-- The sheaf of relative differentials of an affine scheme is quasi-coherent. -/
instance isQuasicoherent_relativeDifferentials_Spec :
    ((Spec A).relativeDifferentials R).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent (Spec A).ringCatSheaf).prop_of_iso
    (relativeDifferentialsSpecIso R A).symm (inferInstanceAs (tilde (.of A Ω[A⁄R])).IsQuasicoherent)

end

end AlgebraicGeometry

end TauCeti
