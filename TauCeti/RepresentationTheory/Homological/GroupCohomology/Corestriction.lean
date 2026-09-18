/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.RepresentationTheory.FiniteIndex
public import TauCeti.RepresentationTheory.Homological.GroupCohomology.Shapiro

/-!
# Corestriction in group cohomology

Let `S` be a subgroup of finite index in a group `G` and `A` a `G`-representation. The
**corestriction** (or transfer) is the map

`cor : Hⁿ(S, Res_S A) ⟶ Hⁿ(G, A)`

in every degree `n`, going the opposite way to restriction. It is defined through Shapiro's lemma
as the composite

`Hⁿ(S, Res_S A) ≅ Hⁿ(G, Coind_S^G Res_S A) ⟶ Hⁿ(G, A)`

of the inverse of Mathlib's Shapiro isomorphism `groupCohomology.coindIso` and the map induced by
the trace `Coind_S^G Res_S A ⟶ A`, `f ↦ ∑ g⁻¹ • f g` over representatives of the right cosets of
`S`, which is the counit of the finite-index adjunction `Rep.coindResAdjunction`. The finiteness of
the index is used only for the trace.

The basic properties are proved here in every degree: corestriction is natural in the
coefficients, and corestriction after restriction is multiplication by the index,
`cor ∘ res = [G : S]`. The latter is obtained by identifying Shapiro's isomorphism with
restriction followed by evaluation at `1`
(`TauCeti.groupCohomology.coindIso_hom`): restriction then becomes the map induced by the unit
`A ⟶ Coind_S^G Res_S A`, and the unit followed by the trace is `[G : S]`. Finally, corestriction
is transitive along a tower `A ↪ B ↪ C` of embeddings with images of finite index.

Corestriction is the map along which cohomological invariants are pushed from a subgroup to the
whole group; in class field theory it is the cohomological counterpart of the norm, and the
normalization `cor ∘ res = [G : S]` is what relates the invariants of a layer to those of its
restrictions.

## Main definitions

* `TauCeti.groupCohomology.corestrictionNatTrans k S n`: corestriction, as a natural
  transformation from `A ↦ Hⁿ(S, Res_S A)` to `A ↦ Hⁿ(G, A)`.
* `TauCeti.groupCohomology.corestriction S A n`: its component at `A`.

## Main results

* `TauCeti.groupCohomology.coindIso_hom_comp_corestriction`: read through Shapiro's isomorphism,
  corestriction is the map induced by the trace.
* `TauCeti.groupCohomology.map_comp_corestriction`: corestriction is natural in the coefficients.
* `TauCeti.groupCohomology.map_subtype_id_comp_corestriction`: corestriction after restriction is
  multiplication by `[G : S]`.
* `TauCeti.groupCohomology.corestriction_trans`: corestriction from `A` to `B` followed by
  corestriction from `B` to `C` is corestriction from `A` to `C`.

## Implementation notes

Transitivity is proved through Shapiro's lemma. Precomposed with Shapiro's isomorphism for `A`
in `C`, both sides become maps induced by morphisms of coefficients out of `Coind_A^C Res_A M`,
and the two morphisms agree because the right cosets of `A` in `C` are the products of the right
cosets of `A` in `B` with those of `B` in `C`.

## References

* K. S. Brown, *Cohomology of Groups*, Graduate Texts in Mathematics 87, Springer (1982),
  Chapter III, §9.
* J. Neukirch, A. Schmidt and K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Grundlehren
  der mathematischen Wissenschaften 323, Springer (2008), Chapter I, §5.
-/

public section

open CategoryTheory Rep

namespace TauCeti.groupCohomology

open _root_.groupCohomology

universe u

variable (k : Type u) {G : Type u} [CommRing k] [Group G] (S : Subgroup G) [S.FiniteIndex]

open scoped Classical in
/-- The composite of the inverse of Shapiro's isomorphism with the map induced by the trace, for a
single representation. This is the component of `corestrictionNatTrans`. -/
private noncomputable def corestrictionApp (A : Rep.{u} k G) (n : ℕ) :
    groupCohomology (res S.subtype A) n ⟶ groupCohomology A n :=
  (coindIso (res S.subtype A) n).inv ≫
    map (MonoidHom.id G) ((coindResAdjunction.{u, u, u} k S).counit.app A) n

variable {k}

private theorem map_comp_corestrictionApp {A B : Rep.{u} k G} (φ : A ⟶ B) (n : ℕ) :
    map (MonoidHom.id S) ((resFunctor S.subtype).map φ) n ≫ corestrictionApp k S B n =
      corestrictionApp k S A n ≫ map (MonoidHom.id G) φ n := by
  classical
  have hinv : map (MonoidHom.id S) ((resFunctor S.subtype).map φ) n ≫
      (coindIso (res S.subtype B) n).inv = (coindIso (res S.subtype A) n).inv ≫
        map (MonoidHom.id G) ((coindFunctor k S.subtype).map ((resFunctor S.subtype).map φ)) n := by
    rw [Iso.comp_inv_eq, Category.assoc, coindIso_hom_naturality, Iso.inv_hom_id_assoc]
  rw [corestrictionApp, corestrictionApp, ← Category.assoc, hinv, Category.assoc, Category.assoc,
    ← map_id_comp, ← map_id_comp]
  exact congrArg _ (congrArg (map (MonoidHom.id G) · n)
    ((coindResAdjunction.{u, u, u} k S).counit.naturality φ))

variable (k)

/-- **Corestriction in group cohomology**, natural in the coefficients: for a finite-index subgroup
`S ≤ G`, the map `Hⁿ(S, Res_S A) ⟶ Hⁿ(G, A)` obtained from Shapiro's isomorphism
`Hⁿ(S, Res_S A) ≅ Hⁿ(G, Coind_S^G Res_S A)` and the trace `Coind_S^G Res_S A ⟶ A`. -/
noncomputable def corestrictionNatTrans (n : ℕ) :
    resFunctor.{u} S.subtype ⋙ functor k S n ⟶ functor k G n where
  app A := corestrictionApp k S A n
  naturality _ _ φ := map_comp_corestrictionApp S φ n

variable {k}

/-- **Corestriction** `Hⁿ(S, Res_S A) ⟶ Hⁿ(G, A)` along a finite-index subgroup `S ≤ G`. -/
noncomputable def corestriction (A : Rep.{u} k G) (n : ℕ) :
    groupCohomology (res S.subtype A) n ⟶ groupCohomology A n :=
  (corestrictionNatTrans k S n).app A

@[simp]
theorem corestrictionNatTrans_app (A : Rep.{u} k G) (n : ℕ) :
    (corestrictionNatTrans k S n).app A = corestriction S A n := (rfl)

open scoped Classical in
/-- **Corestriction through Shapiro's lemma.** Precomposed with Shapiro's isomorphism
`Hⁿ(G, Coind_S^G Res_S A) ≅ Hⁿ(S, Res_S A)`, corestriction is the map induced by the trace
`Coind_S^G Res_S A ⟶ A`, the counit of `Rep.coindResAdjunction`. -/
theorem coindIso_hom_comp_corestriction (A : Rep.{u} k G) (n : ℕ) :
    (coindIso (res S.subtype A) n).hom ≫ corestriction S A n =
      map (MonoidHom.id G) ((coindResAdjunction.{u, u, u} k S).counit.app A) n :=
  Iso.hom_inv_id_assoc _ _

/-- **Corestriction is natural in the coefficients.** -/
@[reassoc, elementwise]
theorem map_comp_corestriction {A B : Rep.{u} k G} (φ : A ⟶ B) (n : ℕ) :
    map (MonoidHom.id S) ((resFunctor S.subtype).map φ) n ≫ corestriction S B n =
      corestriction S A n ≫ map (MonoidHom.id G) φ n :=
  map_comp_corestrictionApp S φ n

/-- **Corestriction after restriction is multiplication by the index**: for a finite-index
subgroup `S ≤ G`, the composite `Hⁿ(G, A) ⟶ Hⁿ(S, Res_S A) ⟶ Hⁿ(G, A)` of restriction and
corestriction is `[G : S]` times the identity, in every degree `n`. -/
@[reassoc, elementwise]
theorem map_subtype_id_comp_corestriction (A : Rep.{u} k G) (n : ℕ) :
    map S.subtype (𝟙 (res S.subtype A)) n ≫ corestriction S A n = S.index • 𝟙 _ := by
  classical
  -- The functor `Hⁿ(G, -)` is the composite of two additive functors.
  have hsmul : map (MonoidHom.id G) (S.index • 𝟙 A) n =
      (HomologicalComplex.homologyFunctor _ _ n).map ((cochainsFunctor k G).map (S.index • 𝟙 A)) :=
    rfl
  rw [← map_unit_comp_coindIso_hom, Category.assoc, coindIso_hom_comp_corestriction, ← map_id_comp,
    TauCeti.Rep.resCoindAdjunction_unit_app_comp_coindResAdjunction_counit_app, hsmul,
    Functor.map_nsmul, Functor.map_nsmul, CategoryTheory.Functor.map_id]
  exact congrArg (S.index • ·) (CategoryTheory.Functor.map_id _ _)

/-! ### Transitivity -/

section Transitivity

variable {A B C : Type u} [Group A] [Group B] [Group C] (φ₁ : A →* B) (φ₂ : B →* C)
  (M : Rep.{u} k C)

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

/-- A chosen representative of the right coset `S x` differs from `x` by an element of `S`. -/
private theorem exists_mul_out_eq {G : Type u} [Group G] (S : Subgroup G) (x : G) :
    ∃ s ∈ S, s * (Quotient.mk (QuotientGroup.rightRel S) x).out = x :=
  ⟨_, QuotientGroup.rightRel_apply.1
    (Quotient.exact (Quotient.out_eq (Quotient.mk (QuotientGroup.rightRel S) x))), by group⟩

/-- For an injective `φ₂`, the right cosets of `(φ₂.comp φ₁).range` in `C` are the products
`φ₂ b * c` of representatives `b` of the right cosets of `φ₁.range` in `B` and `c` of the right
cosets of `φ₂.range` in `C`. -/
private theorem bijective_mk_mul_out (h₂ : Function.Injective φ₂) :
    Function.Bijective fun x : Quotient (QuotientGroup.rightRel φ₂.range) ×
        Quotient (QuotientGroup.rightRel φ₁.range) =>
      Quotient.mk (QuotientGroup.rightRel (φ₂.comp φ₁).range) (φ₂ x.2.out * x.1.out) := by
  constructor
  · rintro ⟨p, q⟩ ⟨p', q'⟩ h
    obtain ⟨a, ha⟩ := QuotientGroup.rightRel_apply.1 (Quotient.exact h)
    have hp : p = p' := by
      rw [← Quotient.out_eq p, ← Quotient.out_eq p']
      refine Quotient.sound (QuotientGroup.rightRel_apply.2 ⟨q'.out⁻¹ * φ₁ a * q.out, ?_⟩)
      simp only [map_mul, map_inv]
      rw [← MonoidHom.comp_apply φ₂ φ₁, ha]
      group
    subst hp
    have hq : q = q' := by
      rw [← Quotient.out_eq q, ← Quotient.out_eq q']
      refine Quotient.sound (QuotientGroup.rightRel_apply.2 ⟨a, h₂ ?_⟩)
      rw [← MonoidHom.comp_apply φ₂ φ₁, ha]
      simp only [map_mul, map_inv]
      group
    rw [hq]
  · intro t
    induction t using Quotient.inductionOn with | h x =>
    obtain ⟨_, ⟨b, rfl⟩, hb⟩ := exists_mul_out_eq φ₂.range x
    obtain ⟨_, ⟨a, rfl⟩, ha⟩ := exists_mul_out_eq φ₁.range b
    refine ⟨(Quotient.mk _ x, Quotient.mk _ b), Quotient.sound
      (QuotientGroup.rightRel_apply.2 ⟨a, ?_⟩)⟩
    rw [eq_mul_inv_iff_mul_eq]
    conv_rhs => rw [← hb]
    conv_rhs => rw [← ha]
    simp only [MonoidHom.coe_comp, Function.comp_apply, map_mul, mul_assoc]

/-- `φ₂` maps `φ₁.range` into `(φ₂.comp φ₁).range`. -/
private def rangeHom : φ₁.range →* (φ₂.comp φ₁).range :=
  (φ₂.comp φ₁.range.subtype).codRestrict _ fun ⟨_, a, ha⟩ => ⟨a, by simp [← ha]⟩

/-- The `C`-representation `Coind_{A}^{C} Res_{A} M` along `φ₂.comp φ₁`, realized on the range. -/
private noncomputable abbrev coindComp : Rep k C :=
  coind (φ₂.comp φ₁).range.subtype (res (φ₂.comp φ₁).range.subtype M)

/-- Evaluation at `1`, the counit of restriction–coinduction along `(φ₂.comp φ₁).range`, read on
`φ₁.range`. -/
private noncomputable def evalOne : res φ₁.range.subtype (res φ₂ (coindComp φ₁ φ₂ M)) ⟶
    res φ₁.range.subtype (res φ₂ M) :=
  (resFunctor (rangeHom φ₁ φ₂)).map ((resCoindAdjunction k (φ₂.comp φ₁).range.subtype).counit.app
    (res (φ₂.comp φ₁).range.subtype M))

/-- Restriction of functions along `φ₂`, `Res_B Coind_A^C ⟶ Coind_A^B`. -/
private noncomputable def restrictCoind : res φ₂ (coindComp φ₁ φ₂ M) ⟶
    coind φ₁.range.subtype (res φ₁.range.subtype (res φ₂ M)) :=
  (resCoindAdjunction k φ₁.range.subtype).homEquiv _ _ (evalOne φ₁ φ₂ M)

private theorem res_map_restrictCoind_comp_counit :
    (resFunctor φ₁.range.subtype).map (restrictCoind φ₁ φ₂ M) ≫
      (resCoindAdjunction k φ₁.range.subtype).counit.app _ = evalOne φ₁ φ₂ M :=
  ((resCoindAdjunction k φ₁.range.subtype).homEquiv_counit _ _ _).symm.trans
    (Equiv.symm_apply_apply _ _)

private theorem restrictCoind_hom_apply_coe (f : coindComp φ₁ φ₂ M) (b : B) :
    ((restrictCoind φ₁ φ₂ M).hom f).1 b = f.1 (φ₂ b) := by
  -- `restrictCoind` evaluates `b • f` at `1`.
  have : ((restrictCoind φ₁ φ₂ M).hom f).1 b = f.1 (1 * φ₂ b) := rfl
  rw [this, one_mul]

open scoped Classical in
/-- The trace of `φ₁.range` after `restrictCoind`, a `B`-equivariant map
`Res_B Coind_A^C ⟶ Res_B M`. -/
private noncomputable def traceRestrict [φ₁.range.FiniteIndex] :
    res φ₂ (coindComp φ₁ φ₂ M) ⟶ res φ₂ M :=
  restrictCoind φ₁ φ₂ M ≫ (coindResAdjunction.{u, u, u} k φ₁.range).counit.app (res φ₂ M)

/-- `traceRestrict`, read as a map of representations of `φ₂.range`. -/
private noncomputable def traceRestrictRange [φ₁.range.FiniteIndex] :
    res φ₂.range.subtype (coindComp φ₁ φ₂ M) ⟶ res φ₂.range.subtype M :=
  Rep.ofHom ⟨(traceRestrict φ₁ φ₂ M).hom.toLinearMap, fun s => by
    obtain ⟨b, hb⟩ := s.2
    ext v
    have := hom_comm_apply (traceRestrict φ₁ φ₂ M) b v
    simp only [res_obj_ρ, MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype, ← hb,
      LinearMap.coe_comp] at this ⊢
    exact this⟩

/-- The `C`-equivariant map `Coind_A^C ⟶ Coind_B^C` adjoint to `traceRestrictRange`. -/
private noncomputable def coindTrace [φ₁.range.FiniteIndex] :
    coindComp φ₁ φ₂ M ⟶ coind φ₂.range.subtype (res φ₂.range.subtype M) :=
  (resCoindAdjunction k φ₂.range.subtype).homEquiv _ _ (traceRestrictRange φ₁ φ₂ M)

private theorem res_map_coindTrace_comp_counit [φ₁.range.FiniteIndex] :
    (resFunctor φ₂.range.subtype).map (coindTrace φ₁ φ₂ M) ≫
      (resCoindAdjunction k φ₂.range.subtype).counit.app _ = traceRestrictRange φ₁ φ₂ M :=
  ((resCoindAdjunction k φ₂.range.subtype).homEquiv_counit _ _ _).symm.trans
    (Equiv.symm_apply_apply _ _)

open scoped Classical in
private theorem coindTrace_hom_apply_coe [φ₁.range.FiniteIndex] (f : coindComp φ₁ φ₂ M)
    (c : C) : ((coindTrace φ₁ φ₂ M).hom f).1 c =
      ∑ q : Quotient (QuotientGroup.rightRel φ₁.range), M.ρ (φ₂ q.out)⁻¹ (f.1 (φ₂ q.out * c)) := by
  -- `coindTrace f` evaluated at `c` is `traceRestrict (c • f)`.
  have : ((coindTrace φ₁ φ₂ M).hom f).1 c =
      (traceRestrict φ₁ φ₂ M).hom ((coindComp φ₁ φ₂ M).ρ c f) := rfl
  rw [this, traceRestrict, Rep.hom_comp, Representation.IntertwiningMap.comp_apply,
    TauCeti.Rep.coindResAdjunction_counit_app_hom_apply]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [restrictCoind_hom_apply_coe]
  simp only [res_obj_ρ, MonoidHom.coe_comp, Function.comp_apply, map_inv]
  rfl

open scoped Classical in
/-- The trace of `(φ₂.comp φ₁).range` is the trace of `φ₂.range` after `coindTrace`: the double
sum over the cosets of `φ₁.range` in `B` and of `φ₂.range` in `C` is a sum over the cosets of
`(φ₂.comp φ₁).range` in `C`. -/
private theorem coindTrace_comp_counit [φ₁.range.FiniteIndex] [φ₂.range.FiniteIndex]
    [(φ₂.comp φ₁).range.FiniteIndex] (h₂ : Function.Injective φ₂) :
    coindTrace φ₁ φ₂ M ≫ (coindResAdjunction.{u, u, u} k φ₂.range).counit.app M =
      (coindResAdjunction.{u, u, u} k (φ₂.comp φ₁).range).counit.app M := by
  refine Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext fun f => ?_))
  simp only [Representation.IntertwiningMap.toLinearMap_apply, Rep.hom_comp,
    Representation.IntertwiningMap.comp_apply]
  rw [TauCeti.Rep.coindResAdjunction_counit_app_hom_apply,
    TauCeti.Rep.coindResAdjunction_counit_app_hom_apply]
  -- The summand `c ↦ c⁻¹ • f c` of the trace is constant on the cosets of `(φ₂.comp φ₁).range`.
  let F : C → M := fun c => M.ρ c⁻¹ (f.1 c)
  have hF (x : C) :
      F x = F (Quotient.mk (QuotientGroup.rightRel (φ₂.comp φ₁).range) x).out := by
    obtain ⟨_, ⟨a, rfl⟩, hs⟩ := exists_mul_out_eq (φ₂.comp φ₁).range x
    conv_lhs => rw [← hs]
    have := f.2 ⟨(φ₂.comp φ₁) a, MonoidHom.mem_range.2 ⟨a, rfl⟩⟩
      (Quotient.mk (QuotientGroup.rightRel (φ₂.comp φ₁).range) x).out
    simp only [F, Subgroup.coe_subtype] at this ⊢
    rw [this]
    simp only [MonoidHom.comp_apply, Subgroup.coe_subtype, ← Module.End.mul_apply, ← map_mul,
      mul_inv_rev, inv_mul_cancel_right]
  calc _ = ∑ x : Quotient (QuotientGroup.rightRel φ₂.range) ×
        Quotient (QuotientGroup.rightRel φ₁.range), F (φ₂ x.2.out * x.1.out) := by
        rw [Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [coindTrace_hom_apply_coe, map_sum]
        refine Finset.sum_congr rfl fun q _ => ?_
        simp only [F, ← Module.End.mul_apply, ← map_mul, mul_inv_rev]
    _ = _ := Fintype.sum_bijective _ (bijective_mk_mul_out φ₁ φ₂ h₂) _ _ fun _ => hF _

/-- **Transitivity of corestriction.** Let `φ₁ : A →* B` and `φ₂ : B →* C` be injective with
images of finite index, and let `φ₃ = φ₂.comp φ₁`. Identify each group with its image through
`MonoidHom.ofInjective`. Then corestriction from `A` to `B`, followed by corestriction from `B`
to `C`, is corestriction from `A` to `C`:

`Hⁿ(A, M) ⟶ Hⁿ(B, M) ⟶ Hⁿ(C, M)` equals `Hⁿ(A, M) ⟶ Hⁿ(C, M)`.

The composite `φ₃` is a separate argument, related to `φ₂.comp φ₁` by the equation `h`, so the
statement applies when the composite is only propositionally equal to a given homomorphism. -/
theorem corestriction_trans {φ₁ : A →* B} {φ₂ : B →* C} {φ₃ : A →* C}
    (h₁ : Function.Injective φ₁) (h₂ : Function.Injective φ₂) (h : φ₂.comp φ₁ = φ₃)
    [φ₁.range.FiniteIndex] [φ₂.range.FiniteIndex] [φ₃.range.FiniteIndex] (M : Rep.{u} k C)
    (n : ℕ) :
    (mapIso (B := res φ₁ (res φ₂ M)) (A := res φ₁.range.subtype (res φ₂ M))
        (MonoidHom.ofInjective h₁) (LinearEquiv.refl k M)
        (fun _ => LinearMap.ext fun _ => rfl) n).hom ≫
      corestriction φ₁.range (res φ₂ M) n ≫
      (mapIso (B := res φ₂ M) (A := res φ₂.range.subtype M)
        (MonoidHom.ofInjective h₂) (LinearEquiv.refl k M)
        (fun _ => LinearMap.ext fun _ => rfl) n).hom ≫
      corestriction φ₂.range M n =
    (mapIso (B := res φ₁ (res φ₂ M)) (A := res φ₃.range.subtype M)
        (MonoidHom.ofInjective (h ▸ h₂.comp h₁ : Function.Injective φ₃)) (LinearEquiv.refl k M)
        (fun _ => by subst h; exact LinearMap.ext fun _ => rfl) n).hom ≫
      corestriction φ₃.range M n := by
  subst h
  classical
  -- Precompose with Shapiro's isomorphism for the composite, read on `A`.
  rw [← cancel_epi ((coindIso (res (φ₂.comp φ₁).range.subtype M) n).hom ≫
    (mapIso (B := res φ₁ (res φ₂ M)) (A := res (φ₂.comp φ₁).range.subtype M)
        (MonoidHom.ofInjective (h₂.comp h₁)) (LinearEquiv.refl k M)
        (fun _ => LinearMap.ext fun _ => rfl) n).inv)]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [coindIso_hom_comp_corestriction]
  -- Read on `B`, Shapiro for the composite is Shapiro for `φ₁.range` after `restrictCoind`.
  have step₁ : (coindIso (res (φ₂.comp φ₁).range.subtype M) n).hom ≫
      (mapIso (B := res φ₁ (res φ₂ M)) (A := res (φ₂.comp φ₁).range.subtype M)
        (MonoidHom.ofInjective (h₂.comp h₁)) (LinearEquiv.refl k M)
        (fun _ => LinearMap.ext fun _ => rfl) n).inv ≫
      (mapIso (B := res φ₁ (res φ₂ M)) (A := res φ₁.range.subtype (res φ₂ M))
        (MonoidHom.ofInjective h₁) (LinearEquiv.refl k M)
        (fun _ => LinearMap.ext fun _ => rfl) n).hom =
      map φ₂ (restrictCoind φ₁ φ₂ M) n ≫
        (coindIso (res φ₁.range.subtype (res φ₂ M)) n).hom := by
    rw [coindIso_hom, coindIso_hom, mapIso_hom, mapIso_inv, ← map_comp, ← map_comp, ← map_comp,
      res_map_restrictCoind_comp_counit]
    refine map_congr ?_ ?_ n
    · ext a
      simp only [MonoidHom.coe_comp, MonoidHom.coe_coe, Function.comp_apply, Subgroup.coe_subtype,
        MonoidHom.ofInjective_apply, MonoidHom.apply_ofInjective_symm]
    · exact LinearMap.ext fun _ => rfl
  -- Then the trace of `φ₁.range`, read on `C`, is Shapiro for `φ₂.range` after `coindTrace`.
  have step₂ : map φ₂ (restrictCoind φ₁ φ₂ M) n ≫
      map (MonoidHom.id B) ((coindResAdjunction.{u, u, u} k φ₁.range).counit.app (res φ₂ M)) n ≫
      (mapIso (B := res φ₂ M) (A := res φ₂.range.subtype M)
        (MonoidHom.ofInjective h₂) (LinearEquiv.refl k M)
        (fun _ => LinearMap.ext fun _ => rfl) n).hom =
      map (MonoidHom.id C) (coindTrace φ₁ φ₂ M) n ≫ (coindIso (res φ₂.range.subtype M) n).hom := by
    rw [coindIso_hom, mapIso_hom, ← map_comp, ← map_comp, ← map_comp,
      res_map_coindTrace_comp_counit]
    refine map_congr ?_ ?_ n
    · ext a
      simp only [MonoidHom.coe_comp, MonoidHom.coe_coe, Function.comp_apply, MonoidHom.id_apply,
        Subgroup.coe_subtype, MonoidHom.apply_ofInjective_symm]
    · exact LinearMap.ext fun _ => rfl
  rw [reassoc_of% step₁, reassoc_of% (coindIso_hom_comp_corestriction φ₁.range (res φ₂ M) n),
    reassoc_of% step₂, coindIso_hom_comp_corestriction, ← map_id_comp,
    coindTrace_comp_counit φ₁ φ₂ M h₂]

end Transitivity

end TauCeti.groupCohomology
