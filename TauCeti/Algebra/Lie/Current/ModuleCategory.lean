/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Current.LoopEnveloping

/-!
# Polynomial and formal smooth module categories

At every central value `a`, restriction along the polynomial embedding identifies smooth
modules over the formal-current enveloping algebra with smooth modules over the polynomial
loop enveloping algebra. Both categories are the native full subcategories defined by
`TauCeti.smoothModules` for the corresponding order left ideals. Polynomial smoothness is
equivalently the vectorwise vanishing of all sufficiently high modes.

The inverse functor extends a polynomial action by finite truncation. It preserves the
underlying additive groups and the functions underlying morphisms; the unit and counit are
identity maps on vectors. Working with central quotients enforces the same scalar action of
the distinguished central generator on both sides, including central value zero.

The constructions reuse `TauCeti.CurrentAlgebra.extendExtensionLieHom` for extension of
Lie actions, `TauCeti.CurrentAlgebra.forall_comp_extendAction_eq_iff` for morphism transport,
and `TauCeti.CurrentAlgebra.extendEnvelopingAction` for the prescribed central value.
Both functors use native `ModuleCat.restrictScalars`; extension restricts the tautological
endomorphism-module action along the extended algebra homomorphism.

## References

* E. Frenkel, *Langlands Correspondence for Loop Groups*, §1.3 and §2.1, for the
  polynomial/formal smooth-module comparison by finite truncation.
-/

public section

noncomputable section

open CategoryTheory LieAlgebra LieModule.Cohomology
open scoped ModuleCat.Algebra
open TauCeti.UniversalEnvelopingAlgebra
open LieAlgebra.ofTwoCocycle (centralElement envelopingι envelopingι_apply
  adjoin_range_envelopingι)

-- Match the coefficientwise algebra used by the formal-current tensor product.
attribute [local instance 1100] HahnSeries.instAlgebra

namespace TauCeti.CurrentAlgebra

universe v

variable {R L : Type*} [CommRing R] [HasUniqueDiv R] [LieRing L] [LieAlgebra R L]
  (Φ : LinearMap.BilinForm R L) (hΦ : Φ.lieInvariant L) (hΦs : Φ.IsSymm) (a : R)

local notation "P" => LieAlgebra.loopAlgebra R ℤ L
local notation "ZP" => TrivialLieModule R P R
local notation "cP" => LieAlgebra.LoopAlgebra.twoCocycleOfBilinear R ℤ L Φ hΦ hΦs
local notation "cC" => twoCocycleOfBilinear R L Φ hΦ hΦs
local notation "UP" => CentralQuotient R (centralElement cP) a
local notation "UC" => CentralQuotient R (centralElement cC) a
local notation "Pol" => ObjectProperty.FullSubcategory
  (smoothModules (loopOrderLeftIdeal Φ hΦ hΦs a))
local notation "For" => ObjectProperty.FullSubcategory
  (smoothModules (orderLeftIdeal Φ hΦ hΦs a))

/-- Polynomial restriction on the smooth level module categories, induced by native
restriction of scalars along `loopEnvelopingHom`. -/
@[expose]
def polynomialRestriction : For ⥤ Pol :=
  (smoothModules (loopOrderLeftIdeal Φ hΦ hΦs a)).lift
    ((smoothModules (orderLeftIdeal Φ hΦ hΦs a)).ι ⋙
      ModuleCat.restrictScalars (loopEnvelopingHom Φ hΦ hΦs a).toRingHom)
    (fun M ↦ smoothModules_restrictScalars _
      (fun N ↦ ⟨N, loopOrderLeftIdeal_le_comap N⟩) M.property)

-- These carrier annotations select the target module action, since restriction preserves
-- the underlying type and the source action is also available on its vectors.
-- Dependent module presentations make these characteristic equations named rewrites;
-- apply them explicitly instead of relying on simplifier matching across the carriers.
/-- The polynomial action on a restricted module is the formal action through the embedding. -/
theorem polynomialRestriction_smul (M : For) (b : UP) (m : M.obj) :
    b • (show ((polynomialRestriction Φ hΦ hΦs a).obj M).obj from m) =
      loopEnvelopingHom Φ hΦ hΦs a b • m :=
  (rfl)

/-- Restriction preserves the function underlying each morphism. -/
theorem polynomialRestriction_map_apply {M N : For} (f : M ⟶ N) (m : M.obj) :
    ((polynomialRestriction Φ hΦ hΦs a).map f).hom m = f.hom m :=
  (rfl)

attribute [local instance 100] LieRing.ofAssociativeRing

private abbrev polynomialRepresentation (M : ModuleCat.{v} UP) :=
  (Algebra.lsmul R R M).toLieHom.comp (CentralQuotient.ι (centralElement cP) a)

private theorem polynomialRepresentation_current (M : ModuleCat.{v} UP) (p : P) (m : M) :
    (((polynomialRepresentation Φ hΦ hΦs a M).toLinearMap ∘ₗ
      LinearEquiv.toLinearMap (ofProdLinearEquiv cP) ∘ₗ LinearMap.inl R P ZP) p) m =
        envelopingι cP a p • m := by
  simp only [polynomialRepresentation, LinearMap.comp_apply, LinearEquiv.coe_coe,
    coe_ofProdLinearEquiv, LinearMap.inl_apply, LieHom.coe_toLinearMap, LieHom.comp_apply,
    AlgHom.toLieHom_apply, Algebra.lsmul_apply, envelopingι_apply]

private theorem polynomialRepresentation_smooth (M : Pol) :
    IsLoopSmooth ((polynomialRepresentation Φ hΦ hΦs a M.obj).toLinearMap ∘ₗ
      LinearEquiv.toLinearMap (ofProdLinearEquiv cP) ∘ₗ LinearMap.inl R P ZP) := by
  apply isLoopSmooth_iff.mpr
  simpa only [polynomialRepresentation, LinearMap.comp_apply, LinearEquiv.coe_coe,
    coe_ofProdLinearEquiv, LinearMap.inl_apply, LieHom.coe_toLinearMap, LieHom.comp_apply,
    AlgHom.toLieHom_apply, Algebra.lsmul_apply, ← envelopingι_apply] using
      (smoothModules_loopOrderLeftIdeal_iff Φ hΦ hΦs a).mp M.property

private def extensionAction (M : Pol) : UC →ₐ[R] Module.End R M.obj :=
  extendEnvelopingAction Φ hΦ hΦs a (polynomialRepresentation_smooth Φ hΦ hΦs a M)

private theorem extensionAction_map {M N : Pol} (f : M ⟶ N) (b : UC) (m : M.obj) :
    f.hom (extensionAction Φ hΦ hΦs a M b m) =
      extensionAction Φ hΦ hΦs a N b (f.hom m) := by
  let fR : M.obj →ₗ[R] N.obj := f.hom.hom.restrictScalars R
  have hp (p : P) :
      fR ∘ₗ ((polynomialRepresentation Φ hΦ hΦs a M.obj).toLinearMap ∘ₗ
        LinearEquiv.toLinearMap (ofProdLinearEquiv cP) ∘ₗ LinearMap.inl R P ZP) p =
      ((polynomialRepresentation Φ hΦ hΦs a N.obj).toLinearMap ∘ₗ
        LinearEquiv.toLinearMap (ofProdLinearEquiv cP) ∘ₗ
        LinearMap.inl R P ZP) p ∘ₗ fR := by
    ext m
    exact f.hom.hom.map_smul _ m
  have hc := (forall_comp_extendAction_eq_iff _
    (polynomialRepresentation_smooth Φ hΦ hΦs a M)
    (polynomialRepresentation_smooth Φ hΦ hΦs a N) fR).mpr hp
  have hg (u : currentAlgebra R L) (m : M.obj) :
      f.hom (extensionAction Φ hΦ hΦs a M (envelopingι cC a u) m) =
        extensionAction Φ hΦ hΦs a N (envelopingι cC a u) (f.hom m) := by
    simpa only [extensionAction, extendEnvelopingAction_envelopingι,
      polynomialRepresentation, fR, LinearMap.restrictScalars_apply, LinearMap.comp_apply] using
        LinearMap.congr_fun (hc u) m
  have hb : b ∈ Algebra.adjoin R (Set.range (envelopingι cC a)) :=
    adjoin_range_envelopingι cC a ▸ Algebra.mem_top
  induction hb using Algebra.adjoin_induction generalizing m with
  | mem b hb => obtain ⟨u, rfl⟩ := hb; exact hg u m
  | algebraMap r => simpa only [AlgHom.commutes, Module.algebraMap_end_apply, fR,
      LinearMap.restrictScalars_apply] using fR.map_smul r m
  | add b c _ _ hb hc => simp [map_add, hb, hc]
  | mul b c _ _ hb hc => simp only [map_mul, mul_apply_eq_comp]; rw [hb, hc]

-- Share the native object construction between the smoothness proof and morphism transport.
-- Rebuilding its module instances inline exhausts synthesis limits.
/-- The formal level module obtained from a smooth polynomial module by finite truncation. -/
@[expose]
def formalExtensionObj (M : Pol) : ModuleCat.{v} UC :=
  let act : UC →ₐ[R] Module.End R M.obj :=
    extendEnvelopingAction (M := M.obj) Φ hΦ hΦs a (by
      exact polynomialRepresentation_smooth Φ hΦ hΦs a M)
  letI : Module (Module.End R M.obj) M.obj := Module.End.applyModule
  (ModuleCat.restrictScalars act.toRingHom).obj
    (ModuleCat.of (Module.End R M.obj) M.obj)

/-- Finite-truncation extension is a smooth formal level module. -/
theorem smoothModules_formalExtensionObj (M : Pol) :
    smoothModules (orderLeftIdeal Φ hΦ hΦs a) (formalExtensionObj Φ hΦ hΦs a M) := by
  rw [smoothModules_orderLeftIdeal_iff]
  intro m
  obtain ⟨N, hN⟩ := isSmooth_iff.mp
    (isSmooth_extendAction _ (polynomialRepresentation_smooth Φ hΦ hΦs a M)) m
  refine ⟨N, fun u hu ↦ ?_⟩
  exact (congrArg (fun e : Module.End R M.obj ↦ e m)
    (extendEnvelopingAction_envelopingι Φ hΦ hΦs a _ u)).trans (hN u hu)

/-- Extension of smooth polynomial modules by finite truncation. -/
@[expose]
def formalExtension : Pol ⥤ For where
  obj M := ⟨formalExtensionObj Φ hΦ hΦs a M,
    smoothModules_formalExtensionObj Φ hΦ hΦs a M⟩
  map {M N} f := ObjectProperty.homMk <| ModuleCat.ofHom
    (X := formalExtensionObj Φ hΦ hΦs a M) (Y := formalExtensionObj Φ hΦ hΦs a N)
    { f.hom.hom.toAddHom with map_smul' := by exact extensionAction_map Φ hΦ hΦs a f }
  map_id _ := by ext m; rfl
  map_comp _ _ := by ext m; rfl


/-- Extension preserves the function underlying each morphism. -/
theorem formalExtension_map_apply {M N : Pol} (f : M ⟶ N) (m : M.obj) :
    ((formalExtension Φ hΦ hΦs a).map f).hom m = f.hom m :=
  (rfl)

/-- The extended action agrees with the polynomial enveloping action on its image. -/
theorem formalExtension_loopEnvelopingHom_smul (M : Pol) (b : UP) (m : M.obj) :
    loopEnvelopingHom Φ hΦ hΦs a b •
      (show ((formalExtension Φ hΦ hΦs a).obj M).obj from m) = b • m :=
  congrArg (fun e : Module.End R M.obj ↦ e m)
    (extendEnvelopingAction_loopEnvelopingHom Φ hΦ hΦs a _ b)

/-- The extension acts on a polynomial current by its original polynomial generator. -/
theorem formalExtension_envelopingι_ofLoop_smul (M : Pol) (p : P) (m : M.obj) :
    envelopingι cC a (ofLoop R L p) •
      (show ((formalExtension Φ hΦ hΦs a).obj M).obj from m) =
        envelopingι cP a p • m := by
  simpa only [loopEnvelopingHom_envelopingι] using
    formalExtension_loopEnvelopingHom_smul Φ hΦ hΦs a M (envelopingι cP a p) m

/-- A formal current acts on a vector through its polynomial truncation at any cutoff
that annihilates all higher polynomial modes of that vector. -/
theorem formalExtension_envelopingι_smul (M : Pol) (u : currentAlgebra R L)
    {N : ℤ} {m : M.obj}
    (hm : ∀ n : ℤ, N ≤ n → ∀ x : L,
      envelopingι cP a (AddMonoidAlgebra.single n 1 ⊗ₜ x) • m = 0) :
    envelopingι cC a u • (show ((formalExtension Φ hΦ hΦs a).obj M).obj from m) =
      envelopingι cP a (trunc R L N u) • m := by
  have hm' : ∀ n : ℤ, N ≤ n → ∀ x : L,
      (((polynomialRepresentation Φ hΦ hΦs a M.obj).toLinearMap ∘ₗ
        LinearEquiv.toLinearMap (ofProdLinearEquiv cP) ∘ₗ LinearMap.inl R P ZP)
          (AddMonoidAlgebra.single n 1 ⊗ₜ x)) m = 0 := by
    simpa only [polynomialRepresentation_current] using hm
  exact (congrArg (fun e : Module.End R M.obj ↦ e m)
    (extendEnvelopingAction_envelopingι Φ hΦ hΦs a _ u)).trans
      ((extendAction_apply_of_forall _ _ hm' u).trans
        (polynomialRepresentation_current Φ hΦ hΦs a M.obj _ m))

private theorem extensionRestriction_current (M : For) (u : currentAlgebra R L) (m : M.obj) :
    extensionAction Φ hΦ hΦs a ((polynomialRestriction Φ hΦ hΦs a).obj M)
      (envelopingι cC a u)
      (show ((polynomialRestriction Φ hΦ hΦs a).obj M).obj from m) =
        envelopingι cC a u • m := by
  obtain ⟨N, hN⟩ := (smoothModules_orderLeftIdeal_iff).mp M.property m
  have hm (n : ℤ) (hn : N ≤ n) (x : L) :
      (((polynomialRepresentation Φ hΦ hΦs a
        ((polynomialRestriction Φ hΦ hΦs a).obj M).obj).toLinearMap ∘ₗ
        LinearEquiv.toLinearMap (ofProdLinearEquiv cP) ∘ₗ LinearMap.inl R P ZP)
          (AddMonoidAlgebra.single n 1 ⊗ₜ x))
          (show ((polynomialRestriction Φ hΦ hΦs a).obj M).obj from m) = 0 := by
    rw [polynomialRepresentation_current, polynomialRestriction_smul,
      loopEnvelopingHom_envelopingι]
    exact hN _ (orderSubmodule_antitone R L hn
      (ofLoop_single_tmul_mem_orderSubmodule R L n x))
  rw [extensionAction, extendEnvelopingAction_envelopingι,
    extendAction_apply_of_forall _ _ hm, polynomialRepresentation_current,
    polynomialRestriction_smul, loopEnvelopingHom_envelopingι]
  have hd := hN _ (ofLoop_trunc_sub_mem_orderSubmodule R L N u)
  rwa [map_sub, sub_smul, sub_eq_zero] at hd

private theorem extensionRestriction_action (M : For) (b : UC) (m : M.obj) :
    extensionAction Φ hΦ hΦs a ((polynomialRestriction Φ hΦ hΦs a).obj M) b
      (show ((polynomialRestriction Φ hΦ hΦs a).obj M).obj from m) = b • m := by
  -- The two scalar presentations need not reduce to the same endomorphism algebra.
  -- Evaluate on the native formal carrier before comparing the algebra operations.
  let Q := (polynomialRestriction Φ hΦ hΦs a).obj M
  let e := extensionAction Φ hΦ hΦs a Q
  let act : UC → M.obj → M.obj := fun b m ↦ e b (show Q.obj from m)
  have ha (b c : UC) (m : M.obj) : act (b + c) m = act b m + act c m :=
    congrArg (fun f : Module.End R Q.obj ↦ f (show Q.obj from m)) (e.map_add b c)
  have hm (b c : UC) (m : M.obj) : act (b * c) m = act b (act c m) :=
    congrArg (fun f : Module.End R Q.obj ↦ f (show Q.obj from m)) (e.map_mul b c)
  suffices h : act b m = b • m from h
  have hb : b ∈ Algebra.adjoin R (Set.range (envelopingι cC a)) :=
    adjoin_range_envelopingι cC a ▸ Algebra.mem_top
  induction hb using Algebra.adjoin_induction generalizing m with
  | mem b hb => obtain ⟨u, rfl⟩ := hb; exact extensionRestriction_current Φ hΦ hΦs a M u m
  | algebraMap r =>
    exact (congrArg (fun f : Module.End R Q.obj ↦ f (show Q.obj from m)) (e.commutes r)).trans
      (congrArg (fun b : UC ↦ b • m) ((loopEnvelopingHom Φ hΦ hΦs a).commutes r))
  | add b c _ _ hb hc => rw [ha, hb, hc, add_smul]
  | mul b c _ _ hb hc =>
    exact (hm b c m).trans ((hb (act c m)).trans
      ((congrArg (fun v : M.obj ↦ b • v) (hc m)).trans (mul_smul b c m).symm))

/-- Polynomial restriction is an equivalence on smooth modules at every central value.
Its inverse is finite-truncation extension, and both comparison isomorphisms are identity
maps on the underlying vectors. -/
-- The exposed record keeps the carrier-preserving functors visible in unit/counit types.
-- Explicit carrier types distinguish the original, restricted and extended scalar actions.
-- The action and all action-compatibility proofs remain hidden.
@[expose]
def polynomialRestrictionEquivalence : For ≌ Pol where
  functor := polynomialRestriction Φ hΦ hΦs a
  inverse := formalExtension Φ hΦ hΦs a
  unitIso := NatIso.ofComponents (fun M ↦
    ((smoothModules (orderLeftIdeal Φ hΦ hΦs a)).isoMk
      (X := (formalExtension Φ hΦ hΦs a).obj ((polynomialRestriction Φ hΦ hΦs a).obj M))
      (Y := M) <| LinearEquiv.toModuleIso
        (show ((formalExtension Φ hΦ hΦs a).obj
          ((polynomialRestriction Φ hΦ hΦs a).obj M)).obj ≃ₗ[UC] M.obj from
          { __ := AddEquiv.refl M.obj
            map_smul' := by
              exact fun b m ↦ extensionRestriction_action Φ hΦ hΦs a M b m })).symm)
    (fun _ ↦ by rfl)
  counitIso := NatIso.ofComponents (fun M ↦
    (smoothModules (loopOrderLeftIdeal Φ hΦ hΦs a)).isoMk
      (X := (polynomialRestriction Φ hΦ hΦs a).obj ((formalExtension Φ hΦ hΦs a).obj M))
      (Y := M) <| LinearEquiv.toModuleIso
        (show ((polynomialRestriction Φ hΦ hΦs a).obj
          ((formalExtension Φ hΦ hΦs a).obj M)).obj ≃ₗ[UP] M.obj from
          { __ := AddEquiv.refl M.obj
            map_smul' := fun b m ↦ formalExtension_loopEnvelopingHom_smul Φ hΦ hΦs a M b m }))
    (fun _ ↦ by rfl)
  functor_unitIso_comp _ := by rfl

/-- The forward functor is polynomial restriction. -/
@[simp]
theorem polynomialRestrictionEquivalence_functor :
    (polynomialRestrictionEquivalence Φ hΦ hΦs a).functor =
      polynomialRestriction Φ hΦ hΦs a :=
  (rfl)

/-- The inverse functor is finite-truncation extension. -/
@[simp]
theorem polynomialRestrictionEquivalence_inverse :
    (polynomialRestrictionEquivalence Φ hΦ hΦs a).inverse = formalExtension Φ hΦ hΦs a :=
  (rfl)

/-- The unit carries each vector to the same vector. -/
theorem polynomialRestrictionEquivalence_unit_hom_apply (M : For) (m : M.obj) :
    ((polynomialRestrictionEquivalence Φ hΦ hΦs a).unitIso.hom.app M).hom m = m :=
  (rfl)

/-- The inverse unit carries each vector to the same vector. -/
theorem polynomialRestrictionEquivalence_unit_inv_apply (M : For) (m : M.obj) :
    ((polynomialRestrictionEquivalence Φ hΦ hΦs a).unitIso.inv.app M).hom m = m :=
  (rfl)

/-- The counit carries each vector to the same vector. -/
theorem polynomialRestrictionEquivalence_counit_hom_apply (M : Pol) (m : M.obj) :
    ((polynomialRestrictionEquivalence Φ hΦ hΦs a).counitIso.hom.app M).hom m = m :=
  (rfl)

/-- The inverse counit carries each vector to the same vector. -/
theorem polynomialRestrictionEquivalence_counit_inv_apply (M : Pol) (m : M.obj) :
    ((polynomialRestrictionEquivalence Φ hΦ hΦs a).counitIso.inv.app M).hom m = m :=
  (rfl)

/-- Polynomial restriction is an equivalence of categories. -/
instance polynomialRestriction_isEquivalence :
    (polynomialRestriction Φ hΦ hΦs a).IsEquivalence :=
  (polynomialRestrictionEquivalence Φ hΦ hΦs a).isEquivalence_functor

/-- Finite-truncation extension is an equivalence of categories. -/
instance formalExtension_isEquivalence :
    (formalExtension Φ hΦ hΦs a).IsEquivalence :=
  (polynomialRestrictionEquivalence Φ hΦ hΦs a).isEquivalence_inverse

/-- Restriction is additive on module morphisms. -/
instance polynomialRestriction_additive : (polynomialRestriction Φ hΦ hΦs a).Additive where
  map_add := by intros; ext m; rfl

/-- Extension is additive on module morphisms. -/
instance formalExtension_additive : (formalExtension Φ hΦ hΦs a).Additive where
  map_add := by intros; ext m; rfl

/-- Restriction is linear over the coefficient ring. -/
instance polynomialRestriction_linear : (polynomialRestriction Φ hΦ hΦs a).Linear R where
  map_smul f r := by
    ext m
    exact (congrArg (fun b : UC ↦ b • f.hom m)
      ((loopEnvelopingHom Φ hΦ hΦs a).commutes r)).symm

/-- Extension is linear over the coefficient ring. -/
instance formalExtension_linear : (formalExtension Φ hΦ hΦs a).Linear R where
  map_smul {X Y} f r := by
    ext m
    exact (congrArg (fun e : Module.End R Y.obj ↦ e (f.hom m))
      ((extensionAction Φ hΦ hΦs a Y).commutes r)).symm

end TauCeti.CurrentAlgebra
