/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicThickeningSystem.Basic
public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import TauCeti.RingTheory.AdicCompletion.Algebra
public import TauCeti.RingTheory.AdicCompletion.Limit

/-!
# Adic rings and the level-preserving formal spectrum

An *adic ring* (`AdicRing`) is a commutative ring `A` bundled with a chosen finitely generated
ideal `I` with respect to which `A` is complete and separated (`IsAdicComplete I A`, Stacks,
Definition 15.37.1 (07E8)). By `IsAdicComplete.of_bijective` (`AdicCompletion.ofAlgEquiv`), `A` is
canonically isomorphic to `AdicCompletion I A`, and by `IsAdicComplete.isLimitQuotientPowSuccCone`
it is the limit in `CommRingCat` of the quotients `A ⧸ I ^ (n + 1)`.

For any commutative ring `R` and ideal `I : Ideal R`, the tower of affine schemes
`Spec (R ⧸ I ^ (n + 1))` with transitions induced by `Ideal.Quotient.factor` forms an adic
thickening system `AdicThickeningSystem.spf I` (Stacks, Definition 87.9.9 (0AIF)); for a bundled
adic ring `A`, we write `Spf A := AdicThickeningSystem.spf A.ideal`.

Unlike the ringed-space formal spectrum `TauCeti.FormalScheme.Spf` (built on topological adic rings
`TauCeti.IsAdicRing`, whose underlying space and structure sheaf are independent of the ideal of
definition), `Spf A` retains the explicit tower of levels `(Spec (A ⧸ I ^ (n + 1)))_n` in the
category `AdicThickeningSystem`. Its morphisms `Spf B ⟶ Spf A` are level-preserving, so when `B` is
`J`-adically complete they correspond bijectively to ring homomorphisms `φ : A →+* B` satisfying
`I ≤ J.comap φ` (`AdicThickeningSystem.spfHomEquiv`, `Spf.homEquiv`). Moreover,
the morphism induced by `φ` is adic (`IsAdicHom`) if and only if
`(I ^ (n + 1)).map φ ⊔ J ^ (n + 2) = J ^ (n + 1)` for every `n`
(`AdicThickeningSystem.isAdicHom_spfMap_iff`, `Spf.isAdicHom_map_iff`).

For a finitely generated ideal `I` of any commutative ring `R`, the `I`-adic completion `R̂` is an
adic ring with ideal of definition `I R̂` (`AdicRing.completion`), and `R → R̂` induces isomorphisms
`R ⧸ I ^ (n + 1) ≅ R̂ ⧸ (I R̂) ^ (n + 1)`, so that `Spf R̂ ≅ spf I` (`Spf.completionIso`).

## Main definitions

* `TauCeti.AlgebraicGeometry.AdicRing`: a commutative ring bundled with a finitely generated ideal
  with respect to which it is complete and separated.
* `TauCeti.AlgebraicGeometry.AdicThickeningSystem.spf`, `TauCeti.AlgebraicGeometry.Spf`: the adic
  thickening system `n ↦ Spec (R ⧸ I ^ (n + 1))`.
* `TauCeti.AlgebraicGeometry.AdicThickeningSystem.spfToSpec`,
  `TauCeti.AlgebraicGeometry.Spf.toSpec`: the canonical morphism `Spf A ⟶ ofScheme.obj (Spec A)`.
* `TauCeti.AlgebraicGeometry.AdicThickeningSystem.spfBotIso`,
  `TauCeti.AlgebraicGeometry.Spf.ofScheme`: for the zero ideal, `Spf A ≅ ofScheme.obj (Spec A)`.
* `TauCeti.AlgebraicGeometry.AdicThickeningSystem.spfMap`, `TauCeti.AlgebraicGeometry.Spf.map`:
  functoriality along ring maps satisfying `I ≤ J.comap φ`.
* `TauCeti.AlgebraicGeometry.AdicThickeningSystem.spfHomEquiv`,
  `TauCeti.AlgebraicGeometry.Spf.homEquiv`: equivalence between `Spf B ⟶ Spf A` and
  `{φ : A →+* B // I ≤ J.comap φ}` when `B` is `J`-adically complete.
* `TauCeti.AlgebraicGeometry.AdicThickeningSystem.uniqueSpfMaximalIdeal`: for a local ring `R`,
  every level of `spf (IsLocalRing.maximalIdeal R)` has a unique point.
* `TauCeti.AlgebraicGeometry.AdicRing.completion`: the `I`-adic completion of a ring along a
  finitely generated ideal `I`, as an adic ring.
* `TauCeti.AlgebraicGeometry.Spf.completionIso`: for `I` finitely generated, `Spf R̂ ≅ spf I`.

## Main results

* `TauCeti.AlgebraicGeometry.AdicThickeningSystem.isAdicHom_spfMap_iff`,
  `TauCeti.AlgebraicGeometry.Spf.isAdicHom_map_iff`: exact ideal-theoretic criterion for `Spf.map`
  to be an adic morphism.
* `TauCeti.AlgebraicGeometry.AdicThickeningSystem.isLocallyNoetherian_spf`,
  `TauCeti.AlgebraicGeometry.Spf.isLocallyNoetherian`: `Spf A` is locally Noetherian when `A` is a
  Noetherian ring.
* `TauCeti.AlgebraicGeometry.AdicThickeningSystem.isIso_spfMap_algebraMap`: for `I` finitely
  generated, the completion map `R → R̂` induces an isomorphism `spf (I R̂) ⟶ spf I`.

## References

* [Stacks Project, Definition 15.37.1](https://stacks.math.columbia.edu/tag/07E8).
* [Stacks Project, Section 87.2 and Definitions 87.9.7,
  87.9.9](https://stacks.math.columbia.edu/tag/0AIF).
-/

public section

open CategoryTheory Limits Opposite AlgebraicGeometry

universe u

namespace TauCeti.AlgebraicGeometry

/-- An adic ring: complete and separated for a chosen finitely generated ideal of definition.
Stacks, Definition 15.37.1 (07E8). -/
@[stacks 07E8]
structure AdicRing where
  /-- The underlying commutative ring. -/
  carrier : Type u
  [commRing : CommRing carrier]
  /-- The chosen finitely generated ideal of definition. -/
  ideal : Ideal carrier
  /-- The ideal of definition is finitely generated. -/
  fg : ideal.FG
  [complete : IsAdicComplete ideal carrier]

attribute [instance] AdicRing.commRing AdicRing.complete

namespace AdicRing

/-- Every commutative ring is an adic ring with respect to the zero ideal `⊥`. -/
abbrev ofBot (R : Type u) [CommRing R] : AdicRing.{u} where
  carrier := R
  ideal := ⊥
  fg := Submodule.fg_bot
  complete := inferInstance

@[simp]
theorem ofBot_carrier (R : Type u) [CommRing R] : (ofBot R).carrier = R :=
  (rfl)

@[simp]
theorem ofBot_ideal (R : Type u) [CommRing R] : (ofBot R).ideal = ⊥ :=
  (rfl)

/-- The `I`-adic completion `R̂` of a commutative ring `R` along a finitely generated ideal `I`, as
an adic ring with ideal of definition `I R̂` (`AdicCompletion.isAdicComplete_self`). -/
noncomputable abbrev completion {R : Type u} [CommRing R] (I : Ideal R) (fg : I.FG) :
    AdicRing.{u} where
  carrier := AdicCompletion I R
  ideal := I.map (algebraMap R (AdicCompletion I R))
  fg := fg.map _
  complete := AdicCompletion.isAdicComplete_self I fg

@[simp]
theorem completion_carrier {R : Type u} [CommRing R] (I : Ideal R) (fg : I.FG) :
    (completion I fg).carrier = AdicCompletion I R :=
  (rfl)

@[simp]
theorem completion_ideal {R : Type u} [CommRing R] (I : Ideal R) (fg : I.FG) :
    (completion I fg).ideal = I.map (algebraMap R (AdicCompletion I R)) :=
  (rfl)

end AdicRing

namespace AdicThickeningSystem

section Unbundled

variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]

private lemma spf_levelMap_eq (I : Ideal R) (n : ℕ) :
    TauCeti.AlgebraicGeometry.levelMap
        (fun k ↦ Spec (CommRingCat.of (R ⧸ I ^ (k + 1))))
        (fun k ↦ Spec.map (CommRingCat.ofHom
          (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ (k + 1)))))) n =
      Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.succ_le_succ (Nat.zero_le n))))) := by
  induction n with
  | zero =>
    rw [TauCeti.AlgebraicGeometry.levelMap_zero]
    have hid : CommRingCat.ofHom
        (Ideal.Quotient.factor (Ideal.pow_le_pow_right (I := I)
          (Nat.succ_le_succ (Nat.zero_le 0)))) = 𝟙 (CommRingCat.of (R ⧸ I ^ 1)) := by
      ext x
      rfl
    rw [hid, Spec.map_id]
  | succ n ih =>
    rw [TauCeti.AlgebraicGeometry.levelMap_succ, ih, ← Spec.map_comp]
    congr 1
    ext x
    rfl

/-- The tower of affine thickenings `Spec (R ⧸ I ^ (n + 1))` associated to any ideal `I` of a
commutative ring `R`. Stacks, Definition 87.9.9 (0AIF). -/
-- `@[expose]` is forced by dependent typing of component morphisms: without `(spf I).X n`
-- reducing definitionally to `Spec (CommRingCat.of (R ⧸ I ^ (n + 1)))`, `spf_ι`, `spf_transition`,
-- `spfToSpec_app`, `spfMap_app`, and `Spec.preimage (f.app n)` in `mk_comp_spfHomEquiv_apply` do
-- not typecheck.
@[stacks 0AIF, expose, simps X ι]
noncomputable def spf (I : Ideal R) : AdicThickeningSystem.{u} where
  X n := Spec (CommRingCat.of (R ⧸ I ^ (n + 1)))
  ι n := Spec.map (CommRingCat.ofHom
    (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)))))
  isThickening n := (IsFirstOrderThickening.SpecMap_quotient_factor_pow_succ _).isThickening
  adic n := by
    rw [spf_levelMap_eq, Scheme.Hom.ker_Spec_map, Scheme.Hom.ker_Spec_map,
      CommRingCat.hom_ofHom, CommRingCat.hom_ofHom, Ideal.Quotient.factor_ker,
      Ideal.Quotient.factor_ker, pow_one, ← Scheme.IdealSheafData.ofIdealTop_pow,
      ← Ideal.map_pow, ← Ideal.map_pow]

theorem spf_reduction (I : Ideal R) (n : ℕ) :
    (spf I).reduction n = Spec (CommRingCat.of (R ⧸ I ^ (n + 1))) := by
  rw [reduction_eq, spf_X]

/-- For `m ≤ n`, the composite transition `(spf I).transition h` is `Spec.map` of the quotient
factorization `R ⧸ I ^ (n + 1) →+* R ⧸ I ^ (m + 1)`. -/
theorem spf_transition (I : Ideal R) {m n : ℕ} (h : m ≤ n) :
    (spf I).transition h =
      Spec.map ((Ideal.quotientPowSuccDiagram I).map (homOfLE h).op) := by
  induction n with
  | zero =>
    obtain rfl : m = 0 := by omega
    rw [transition_refl]
    dsimp only [spf, Ideal.quotientPowSuccDiagram]
    rw [← Spec.map_id]
    congr 1
    ext x
    rfl
  | succ n ih =>
    by_cases h' : m ≤ n
    · rw [(spf I).transition_succ_of_le h', ih h']
      dsimp only [spf, Ideal.quotientPowSuccDiagram, unop_op]
      rw [← Spec.map_comp]
      congr 1
      ext x
      rfl
    · obtain rfl : m = n + 1 := by omega
      rw [transition_refl]
      dsimp only [spf, Ideal.quotientPowSuccDiagram]
      rw [← Spec.map_id]
      congr 1
      ext x
      rfl

/-- The canonical morphism `spf I ⟶ ofScheme.obj (Spec R)` assembled from the closed immersions
`Spec (R ⧸ I ^ (n + 1)) ⟶ Spec R`. -/
noncomputable def spfToSpec (I : Ideal R) :
    spf I ⟶ ofScheme.obj (Spec (CommRingCat.of R)) where
  app n := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))))
  naturality n := by
    dsimp only [spf, ofScheme]
    rw [Category.comp_id, ← Spec.map_comp]
    congr 1

@[simp]
theorem spfToSpec_app (I : Ideal R) (n : ℕ) :
    (spfToSpec I).app n = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1)))) :=
  (rfl)

/-- When `I = ⊥`, the formal spectrum `spf I` is canonically isomorphic to the constant system
`ofScheme.obj (Spec R)`. -/
noncomputable def spfIsoOfEqBot {I : Ideal R} (hI : I = ⊥) :
    spf I ≅ ofScheme.obj (Spec (CommRingCat.of R)) := by
  have : IsIso (spfToSpec I) := by
    rw [isIso_iff_forall_isIso_app]
    intro n
    have hpow : I ^ (n + 1) = ⊥ := by rw [hI, Ideal.bot_pow (Nat.succ_ne_zero n)]
    let e : CommRingCat.of R ≅ CommRingCat.of (R ⧸ I ^ (n + 1)) :=
      ((RingEquiv.quotientBot R).symm.trans (Ideal.quotEquivOfEq hpow.symm)).toCommRingCatIso
    have he : CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))) = e.hom := by
      ext x
      rfl
    dsimp only [spfToSpec, spf, ofScheme]
    rw [he]
    infer_instance
  exact asIso (spfToSpec I)

@[simp]
theorem spfIsoOfEqBot_hom {I : Ideal R} (hI : I = ⊥) :
    (spfIsoOfEqBot hI).hom = spfToSpec I :=
  (rfl)

/-- For the zero ideal `⊥`, `spf ⊥` is canonically isomorphic to the constant system of `Spec R`. -/
noncomputable def spfBotIso (R : Type u) [CommRing R] :
    spf (⊥ : Ideal R) ≅ ofScheme.obj (Spec (CommRingCat.of R)) :=
  spfIsoOfEqBot rfl

@[simp]
theorem spfBotIso_hom (R : Type u) [CommRing R] :
    (spfBotIso R).hom = spfToSpec (⊥ : Ideal R) :=
  (rfl)

/-- If `R` is Noetherian, then every quotient `R ⧸ I ^ (n + 1)` is Noetherian, so `spf I` is
locally Noetherian. -/
instance isLocallyNoetherian_spf (I : Ideal R) [IsNoetherianRing R] :
    (spf I).IsLocallyNoetherian where
  level n := by
    dsimp only [spf]
    infer_instance

/-- A ring homomorphism `φ : R →+* S` carrying `I` into `J` induces a level-preserving morphism of
formal spectra `spf J ⟶ spf I`. -/
noncomputable def spfMap {I : Ideal R} {J : Ideal S} (φ : R →+* S) (hφ : I ≤ J.comap φ) :
    spf J ⟶ spf I where
  app n := Spec.map (CommRingCat.ofHom
    (Ideal.quotientMap (J ^ (n + 1)) φ
      ((Ideal.pow_right_mono hφ (n + 1)).trans (Ideal.le_comap_pow φ (n + 1)))))
  naturality n := by
    dsimp only [spf]
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext x
    rfl

@[simp]
theorem spfMap_app {I : Ideal R} {J : Ideal S} (φ : R →+* S) (hφ : I ≤ J.comap φ) (n : ℕ) :
    (spfMap φ hφ).app n = Spec.map (CommRingCat.ofHom
      (Ideal.quotientMap (J ^ (n + 1)) φ
        ((Ideal.pow_right_mono hφ (n + 1)).trans (Ideal.le_comap_pow φ (n + 1))))) :=
  (rfl)

@[simp]
theorem spfMap_id (I : Ideal R) :
    spfMap (I := I) (J := I) (RingHom.id R) le_rfl = 𝟙 (spf I) := by
  ext n
  rw [id_app]
  dsimp only [spfMap, spf]
  have hid : CommRingCat.ofHom
      (Ideal.quotientMap (I ^ (n + 1)) (RingHom.id R)
        ((Ideal.pow_right_mono (I := I) (J := I.comap (RingHom.id R)) le_rfl (n + 1)).trans
          (Ideal.le_comap_pow (RingHom.id R) (n + 1)))) = 𝟙 _ := by
    ext x
    rfl
  rw [hid, Spec.map_id]

theorem spfMap_comp {I : Ideal R} {J : Ideal S} {K : Ideal T}
    (φ : R →+* S) (hφ : I ≤ J.comap φ) (ψ : S →+* T) (hψ : J ≤ K.comap ψ) :
    spfMap (ψ.comp φ) (hφ.trans (Ideal.comap_mono hψ)) = spfMap ψ hψ ≫ spfMap φ hφ := by
  ext n
  rw [comp_app]
  dsimp only [spfMap, spf]
  rw [← Spec.map_comp]
  congr 1
  ext x
  rfl

/-- The morphism `spfMap φ hφ : spf J ⟶ spf I` lies over `Spec.map φ : Spec S ⟶ Spec R`. -/
@[reassoc (attr := simp)]
theorem spfMap_spfToSpec {I : Ideal R} {J : Ideal S} (φ : R →+* S) (hφ : I ≤ J.comap φ) :
    spfMap φ hφ ≫ spfToSpec I = spfToSpec J ≫ ofScheme.map (Spec.map (CommRingCat.ofHom φ)) := by
  ext n
  rw [comp_app, comp_app]
  -- Both sides are `Spec.map` of the ring map `R → S ⧸ J ^ (n + 1)`, `x ↦ [φ x]`.
  exact (Spec.map_comp _ _).symm.trans
    (Spec.map_comp (CommRingCat.ofHom φ) (CommRingCat.ofHom (Ideal.Quotient.mk (J ^ (n + 1)))))

/-- The level-preserving morphism `spfMap φ hφ : spf J ⟶ spf I` is adic if and only if at every
level `n`, `(I ^ (n + 1)).map φ ⊔ J ^ (n + 2) = J ^ (n + 1)`. In particular, at `n = 0` an adic
morphism satisfies `I.map φ ⊔ J ^ 2 = J`. -/
theorem isAdicHom_spfMap_iff {I : Ideal R} {J : Ideal S} (φ : R →+* S) (hφ : I ≤ J.comap φ) :
    IsAdicHom (spfMap φ hφ) ↔ ∀ n, (I ^ (n + 1)).map φ ⊔ J ^ (n + 2) = J ^ (n + 1) := by
  rw [isAdicHom_iff_ker_comap]
  refine forall_congr' fun n ↦ ?_
  let S₂ := CommRingCat.of (S ⧸ J ^ (n + 2))
  let mkR := Ideal.Quotient.mk (I ^ (n + 2))
  let mkS := Ideal.Quotient.mk (J ^ (n + 2))
  let φ₂ := Ideal.quotientMap (J ^ (n + 2)) φ
    ((Ideal.pow_right_mono hφ (n + 2)).trans (Ideal.le_comap_pow φ (n + 2)))
  have hmap : ((I ^ (n + 1)).map mkR).map φ₂ = ((I ^ (n + 1)).map φ).map mkS := by
    rw [Ideal.map_map, Ideal.map_map, Ideal.quotientMap_comp_mk]
  dsimp only [spfMap, spf]
  rw [Scheme.Hom.ker_Spec_map, Scheme.Hom.ker_Spec_map,
    CommRingCat.hom_ofHom, CommRingCat.hom_ofHom, Ideal.Quotient.factor_ker,
    Ideal.Quotient.factor_ker, TauCeti.comap_ofIdealTop_map_ΓSpecIso_inv,
    CommRingCat.hom_ofHom, hmap]
  have hinj : Function.Injective (fun K : Ideal S₂ ↦
      Scheme.IdealSheafData.ofIdealTop (K.map (Scheme.ΓSpecIso S₂).inv.hom)) := by
    intro K₁ K₂ hK
    have hK' : K₁.map (Scheme.ΓSpecIso S₂).inv.hom = K₂.map (Scheme.ΓSpecIso S₂).inv.hom := by
      simpa using congrArg Scheme.IdealSheafData.equivOfIsAffine hK
    have hbij := ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso S₂).inv
    have hcomap := congrArg (Ideal.comap (Scheme.ΓSpecIso S₂).inv.hom) hK'
    rwa [Ideal.comap_map_of_bijective _ hbij, Ideal.comap_map_of_bijective _ hbij] at hcomap
  rw [hinj.eq_iff]
  constructor
  · intro h
    have hc := congrArg (Ideal.comap mkS) h
    rwa [Ideal.comap_map_of_surjective mkS Ideal.Quotient.mk_surjective,
      Ideal.comap_map_of_surjective mkS Ideal.Quotient.mk_surjective,
      ← RingHom.ker_eq_comap_bot, Ideal.mk_ker,
      sup_eq_left.mpr (Ideal.pow_le_pow_right (I := J) (Nat.le_succ (n + 1)))] at hc
  · intro h
    have hbot : (J ^ (n + 2)).map mkS = ⊥ := by
      rw [Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker]
    rw [← h, Ideal.map_sup, hbot, sup_bot_eq]

/-- Cone over `Ideal.quotientPowSuccDiagram J` with apex `R` extracted from a morphism
`f : spf J ⟶ spf I`. -/
private noncomputable def spfHomCone {I : Ideal R} {J : Ideal S} (f : spf J ⟶ spf I) :
    Cone (Ideal.quotientPowSuccDiagram J) where
  pt := CommRingCat.of R
  π.app n :=
    CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n.unop + 1))) ≫ Spec.preimage (f.app n.unop)
  π.naturality m n g := by
    have hmn : n.unop ≤ m.unop := leOfHom g.unop
    have hnat := f.transition_app hmn
    rw [spf_transition, spf_transition] at hnat
    dsimp only [spf, Ideal.quotientPowSuccDiagram, unop_op] at hnat
    rw [← Spec.map_preimage (f.app m.unop), ← Spec.map_preimage (f.app n.unop),
      ← Spec.map_comp, ← Spec.map_comp] at hnat
    have hring := Spec.map_injective hnat
    have hmk : CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (m.unop + 1))) ≫
        (Ideal.quotientPowSuccDiagram I).map (homOfLE hmn).op =
        CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n.unop + 1))) := by
      ext x
      rfl
    have hg : g = (homOfLE hmn).op := Subsingleton.elim _ _
    simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp, Category.assoc, hg]
    dsimp only [spf, Ideal.quotientPowSuccDiagram, unop_op] at hmk ⊢
    rw [hring, ← Category.assoc, hmk]

/-- When `S` is `J`-adically complete, morphisms `spf J ⟶ spf I` of adic thickening systems are in
bijection with ring homomorphisms `φ : R →+* S` carrying `I` into `J`. -/
noncomputable def spfHomEquiv (I : Ideal R) (J : Ideal S) [IsAdicComplete J S] :
    (spf J ⟶ spf I) ≃ {φ : R →+* S // I ≤ J.comap φ} where
  toFun f :=
    let φ : R →+* S := ((IsAdicComplete.isLimitQuotientPowSuccCone J).lift (spfHomCone f)).hom
    ⟨φ, fun a ha ↦ by
      have h0 := (IsAdicComplete.isLimitQuotientPowSuccCone J).fac (spfHomCone f) (op 0)
      dsimp only [spfHomCone, spf, Ideal.quotientPowSuccCone, Ideal.quotientPowSuccDiagram,
        unop_op] at h0
      have ha0 : Ideal.Quotient.mk (J ^ 1) (φ a) =
          (Spec.preimage (f.app 0)).hom (Ideal.Quotient.mk (I ^ 1) a) :=
        congr($h0 a)
      have ha1 : Ideal.Quotient.mk (I ^ 1) a = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr (by simpa using ha)
      rw [Ideal.mem_comap, ← pow_one J, ← Ideal.Quotient.eq_zero_iff_mem, ha0, ha1, map_zero]⟩
  invFun φ := spfMap φ.1 φ.2
  left_inv f := by
    ext n
    dsimp only [spfMap, spf]
    rw [← Spec.map_preimage (f.app n)]
    congr 1
    have hn := (IsAdicComplete.isLimitQuotientPowSuccCone J).fac (spfHomCone f) (op n)
    dsimp only [spfHomCone, Ideal.quotientPowSuccCone, Ideal.quotientPowSuccDiagram, unop_op] at hn
    ext x
    exact congr($hn x)
  right_inv := by
    rintro ⟨φ, hφ⟩
    ext1
    have huniq := (IsAdicComplete.isLimitQuotientPowSuccCone J).uniq
      (spfHomCone (spfMap φ hφ)) (CommRingCat.ofHom φ) fun n ↦ by
        dsimp only [spfHomCone, spfMap, spf, Ideal.quotientPowSuccCone,
          Ideal.quotientPowSuccDiagram]
        rw [Spec.preimage_map]
        ext x
        rfl
    exact congrArg CommRingCat.Hom.hom huniq.symm

@[simp]
theorem spfHomEquiv_symm_apply {I : Ideal R} {J : Ideal S} [IsAdicComplete J S]
    (φ : {φ : R →+* S // I ≤ J.comap φ}) :
    (spfHomEquiv I J).symm φ = spfMap φ.1 φ.2 :=
  (rfl)

theorem mk_comp_spfHomEquiv_apply {I : Ideal R} {J : Ideal S} [IsAdicComplete J S]
    (f : spf J ⟶ spf I) (n : ℕ) :
    (Ideal.Quotient.mk (J ^ (n + 1))).comp (spfHomEquiv I J f).1 =
      (Spec.preimage (f.app n)).hom.comp (Ideal.Quotient.mk (I ^ (n + 1))) := by
  have hn := (IsAdicComplete.isLimitQuotientPowSuccCone J).fac (spfHomCone f) (op n)
  dsimp only [spfHomEquiv, spfHomCone, Ideal.quotientPowSuccCone,
    Ideal.quotientPowSuccDiagram, unop_op] at hn ⊢
  ext x
  exact congr($hn x)

/-- For a finitely generated ideal `I` of `R`, the morphism `spf (I R̂) ⟶ spf I` induced by the
completion map `R → R̂` is an isomorphism, since `R ⧸ I ^ (n + 1) → R̂ ⧸ (I R̂) ^ (n + 1)` is
bijective at every level. -/
theorem isIso_spfMap_algebraMap (I : Ideal R) (fg : I.FG) :
    IsIso (spfMap (I := I) (J := I.map (algebraMap R (AdicCompletion I R)))
      (algebraMap R (AdicCompletion I R)) Ideal.le_comap_map) := by
  refine (isIso_iff_forall_isIso_app _).mpr fun n ↦ ?_
  rw [spfMap_app]
  have hH : I ^ (n + 1) ≤ ((I.map (algebraMap R (AdicCompletion I R))) ^ (n + 1)).comap
      (algebraMap R (AdicCompletion I R)) :=
    (Ideal.pow_right_mono Ideal.le_comap_map (n + 1)).trans (Ideal.le_comap_pow _ (n + 1))
  have := (ConcreteCategory.isIso_iff_bijective
    (CommRingCat.ofHom (Ideal.quotientMap _ (algebraMap R (AdicCompletion I R)) hH))).mpr
    (AdicCompletion.quotientMap_algebraMap_bijective fg (n + 1) (H := hH))
  -- The ascription states the instance between the affine schemes `Spec (R̂ ⧸ (I R̂) ^ (n + 1))`
  -- and `Spec (R ⧸ I ^ (n + 1))`, which instance search does not see through the levels of `spf`.
  exact (inferInstance : IsIso (Spec.map (CommRingCat.ofHom (Ideal.quotientMap _ _ hH))))

end Unbundled

/-- For a local ring `R`, every level of `spf (IsLocalRing.maximalIdeal R)` has a unique point:
level `0` is isomorphic to the spectrum of the residue field, and all levels are homeomorphic. -/
@[instance_reducible]
noncomputable def uniqueSpfMaximalIdeal (R : Type u) [CommRing R] [IsLocalRing R] (n : ℕ) :
    Unique ((spf (IsLocalRing.maximalIdeal R)).X n) := by
  let e : R ⧸ IsLocalRing.maximalIdeal R ^ 1 ≃+* IsLocalRing.ResidueField R :=
    Ideal.quotEquivOfEq (pow_one (IsLocalRing.maximalIdeal R))
  let iso₀ : (spf (IsLocalRing.maximalIdeal R)).X 0 ≅
      Spec (.of (IsLocalRing.ResidueField R)) :=
    Scheme.Spec.mapIso e.symm.toCommRingCatIso.op
  letI : Unique ((spf (IsLocalRing.maximalIdeal R)).X 0) :=
    (IsUniversalHomeomorphism.isHomeomorph iso₀.hom).homeomorph.toEquiv.unique
  exact ((spf (IsLocalRing.maximalIdeal R)).homeomorphLevel n).symm.toEquiv.unique

end AdicThickeningSystem

/-! ### Formal spectrum of a bundled `AdicRing` -/

/-- The formal spectrum of an adic ring `A` as the adic thickening system of affine reductions
`Spec (A ⧸ I ^ (n + 1))`. Stacks, Definition 87.9.9 (0AIF). -/
-- `@[expose]` is forced by dependent typing of component morphisms: without `(Spf A).X n`
-- reducing definitionally to `Spec (CommRingCat.of (A.carrier ⧸ A.ideal ^ (n + 1)))`, `Spf.ι_eq`,
-- `Spf.toSpec_app`, `Spf.map_app`, and `Spec.preimage (f.app n)` in `Spf.mk_comp_homEquiv_apply`
-- do not typecheck.
@[stacks 0AIF, expose]
noncomputable def Spf (A : AdicRing.{u}) : AdicThickeningSystem.{u} :=
  AdicThickeningSystem.spf A.ideal

namespace Spf

@[simp]
theorem X_eq (A : AdicRing.{u}) (n : ℕ) :
    (Spf A).X n = Spec (CommRingCat.of (A.carrier ⧸ A.ideal ^ (n + 1))) :=
  (rfl)

theorem reduction_eq (A : AdicRing.{u}) (n : ℕ) :
    (Spf A).reduction n = Spec (CommRingCat.of (A.carrier ⧸ A.ideal ^ (n + 1))) := by
  rw [AdicThickeningSystem.reduction_eq, X_eq]

@[simp]
theorem ι_eq (A : AdicRing.{u}) (n : ℕ) :
    (Spf A).ι n = Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ (n + 1))))) :=
  (rfl)

/-- The canonical morphism `Spf A ⟶ ofScheme.obj (Spec A)` assembled from the closed immersions of
the levels `Spec (A ⧸ I ^ (n + 1))` into `Spec A`. -/
noncomputable def toSpec (A : AdicRing.{u}) :
    Spf A ⟶ AdicThickeningSystem.ofScheme.obj (Spec (CommRingCat.of A.carrier)) :=
  AdicThickeningSystem.spfToSpec A.ideal

@[simp]
theorem toSpec_app (A : AdicRing.{u}) (n : ℕ) :
    (toSpec A).app n = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (A.ideal ^ (n + 1)))) :=
  (rfl)

/-- When the chosen ideal of `A` is `⊥`, `Spf A` is canonically isomorphic to the constant system
`ofScheme.obj (Spec A)`. -/
noncomputable def isoOfIdealEqBot (A : AdicRing.{u}) (hI : A.ideal = ⊥) :
    Spf A ≅ AdicThickeningSystem.ofScheme.obj (Spec (CommRingCat.of A.carrier)) :=
  AdicThickeningSystem.spfIsoOfEqBot hI

@[simp]
theorem isoOfIdealEqBot_hom (A : AdicRing.{u}) (hI : A.ideal = ⊥) :
    (isoOfIdealEqBot A hI).hom = toSpec A :=
  (rfl)

/-- For a discrete ring `R` equipped with the zero ideal, `Spf (AdicRing.ofBot R)` is canonically
isomorphic to `ofScheme.obj (Spec R)`. -/
noncomputable def ofScheme (R : Type u) [CommRing R] :
    Spf (AdicRing.ofBot R) ≅ AdicThickeningSystem.ofScheme.obj (Spec (CommRingCat.of R)) :=
  AdicThickeningSystem.spfBotIso R

@[simp]
theorem ofScheme_hom (R : Type u) [CommRing R] :
    (ofScheme R).hom = toSpec (AdicRing.ofBot R) :=
  (rfl)

/-- Functoriality of `Spf` along level-preserving ring homomorphisms `φ : A →+* B` with
`A.ideal ≤ B.ideal.comap φ`. -/
noncomputable def map {A B : AdicRing.{u}} (φ : A.carrier →+* B.carrier)
    (hφ : A.ideal ≤ B.ideal.comap φ) : Spf B ⟶ Spf A :=
  AdicThickeningSystem.spfMap φ hφ

@[simp]
theorem map_app {A B : AdicRing.{u}} (φ : A.carrier →+* B.carrier)
    (hφ : A.ideal ≤ B.ideal.comap φ) (n : ℕ) :
    (map φ hφ).app n = Spec.map (CommRingCat.ofHom
      (Ideal.quotientMap (B.ideal ^ (n + 1)) φ
        ((Ideal.pow_right_mono hφ (n + 1)).trans (Ideal.le_comap_pow φ (n + 1))))) :=
  (rfl)

@[simp]
theorem map_id (A : AdicRing.{u}) :
    map (A := A) (B := A) (RingHom.id A.carrier) le_rfl = 𝟙 (Spf A) :=
  AdicThickeningSystem.spfMap_id A.ideal

theorem map_comp {A B C : AdicRing.{u}} (φ : A.carrier →+* B.carrier)
    (hφ : A.ideal ≤ B.ideal.comap φ) (ψ : B.carrier →+* C.carrier)
    (hψ : B.ideal ≤ C.ideal.comap ψ) :
    map (ψ.comp φ) (hφ.trans (Ideal.comap_mono hψ)) = map ψ hψ ≫ map φ hφ :=
  AdicThickeningSystem.spfMap_comp φ hφ ψ hψ

/-- `Spf.map φ hφ : Spf B ⟶ Spf A` is adic if and only if
`(A.ideal ^ (n + 1)).map φ ⊔ B.ideal ^ (n + 2) = B.ideal ^ (n + 1)` for every `n`. -/
theorem isAdicHom_map_iff {A B : AdicRing.{u}} (φ : A.carrier →+* B.carrier)
    (hφ : A.ideal ≤ B.ideal.comap φ) :
    AdicThickeningSystem.IsAdicHom (map φ hφ) ↔
      ∀ n, (A.ideal ^ (n + 1)).map φ ⊔ B.ideal ^ (n + 2) = B.ideal ^ (n + 1) :=
  AdicThickeningSystem.isAdicHom_spfMap_iff φ hφ

/-- Level-preserving morphisms `Spf B ⟶ Spf A` between adic rings correspond bijectively to ring
homomorphisms `φ : A →+* B` carrying `A.ideal` into `B.ideal`. -/
noncomputable def homEquiv (A B : AdicRing.{u}) :
    (Spf B ⟶ Spf A) ≃ {φ : A.carrier →+* B.carrier // A.ideal ≤ B.ideal.comap φ} :=
  AdicThickeningSystem.spfHomEquiv A.ideal B.ideal

@[simp]
theorem homEquiv_symm_apply (A B : AdicRing.{u})
    (φ : {φ : A.carrier →+* B.carrier // A.ideal ≤ B.ideal.comap φ}) :
    (homEquiv A B).symm φ = map φ.1 φ.2 :=
  (rfl)

theorem mk_comp_homEquiv_apply {A B : AdicRing.{u}} (f : Spf B ⟶ Spf A) (n : ℕ) :
    (Ideal.Quotient.mk (B.ideal ^ (n + 1))).comp (homEquiv A B f).1 =
      (Spec.preimage (f.app n)).hom.comp (Ideal.Quotient.mk (A.ideal ^ (n + 1))) :=
  AdicThickeningSystem.mk_comp_spfHomEquiv_apply f n

/-- For a Noetherian adic ring `A`, `Spf A` is locally Noetherian. -/
instance isLocallyNoetherian (A : AdicRing.{u}) [IsNoetherianRing A.carrier] :
    (Spf A).IsLocallyNoetherian :=
  AdicThickeningSystem.isLocallyNoetherian_spf A.ideal

section Completion

variable {R : Type u} [CommRing R] (I : Ideal R) (fg : I.FG)

/-- For a finitely generated ideal `I` of `R`, the formal spectrum of the `I`-adic completion `R̂`
is the system `spf I` of the affine schemes `Spec (R ⧸ I ^ (n + 1))`, via the completion map
`R → R̂`. -/
noncomputable def completionIso : Spf (AdicRing.completion I fg) ≅ AdicThickeningSystem.spf I :=
  @asIso _ _ _ _
    (AdicThickeningSystem.spfMap (algebraMap R (AdicCompletion I R)) Ideal.le_comap_map)
    (AdicThickeningSystem.isIso_spfMap_algebraMap I fg)

@[simp]
theorem completionIso_hom :
    (completionIso I fg).hom =
      AdicThickeningSystem.spfMap (algebraMap R (AdicCompletion I R)) Ideal.le_comap_map :=
  (rfl)

/-- `completionIso` lies over the morphism `Spec R̂ ⟶ Spec R` induced by the completion map. -/
@[reassoc]
theorem completionIso_hom_spfToSpec :
    (completionIso I fg).hom ≫ AdicThickeningSystem.spfToSpec I =
      toSpec (AdicRing.completion I fg) ≫ AdicThickeningSystem.ofScheme.map
        (Spec.map (CommRingCat.ofHom (algebraMap R (AdicCompletion I R)))) :=
  AdicThickeningSystem.spfMap_spfToSpec _ Ideal.le_comap_map

end Completion

end Spf

end TauCeti.AlgebraicGeometry
