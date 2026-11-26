/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Monoidal.Center.Induction.Adjunction
public import TauCeti.CategoryTheory.Monoidal.Center.Induction.Faithful
public import TauCeti.CategoryTheory.Monoidal.Pivotal.SquaredNorm

/-!
# The left adjunction for induction into the Drinfeld centre

Let `C` be a fusion category over an algebraically closed field `k`: a rigid `k`-linear finite
semisimple abelian monoidal category with simple unit, finitely many simple classes and
finite-dimensional morphism spaces. In `TauCeti.CategoryTheory.Monoidal.Center.Induction.Adjunction`
the induction functor `Center.induction k C : C ⥤ Center C`, `X ↦ ⨁ S, S ⊗ X ⊗ Sᘁ`, is right adjoint
to the forgetful functor. This file shows that it is also left adjoint to it, with no pivotal
structure assumed: `Center.inductionForgetAdjunction k C : Center.induction k C ⊣ Center.forget C`.

The unit `X ⟶ ⨁ S, S ⊗ X ⊗ Sᘁ` includes `X` into the summand of the class `R` of the unit object,
identified with `X` by `CategoryTheory.Center.inductionUnitSummandIso`.
The counit at an object `⟨A, b⟩` of the centre moves `A` out of each summand `S ⊗ A ⊗ Sᘁ` to the
right of `Sᘁ` with `b`, and contracts `S ⊗ Sᘁ` with an evaluation `S ⊗ Sᘁ ⟶ 𝟙_ C`. Without a
pivotal structure such an evaluation is only determined up to a scalar, and the counit commutes
with the half-braidings only for one choice of these scalars: the evaluation of
`TauCeti.normalizedExactPairing k S`, which exhibits `S` as a right dual of `Sᘁ` with closed loop
`η ≫ ε_ S Sᘁ = 𝟙 (𝟙_ C)`. For any isomorphism `a : S ≅ Sᘁᘁ`, it is the evaluation transported along
`a`, multiplied by `doubleDualTrace a.invᘁ`.

The compatibility with the half-braidings reduces, through the dual bases that define the
half-braiding of the induced object, to an identity of canonical elements: for simple `S` and `T`
and any `U`, the canonical element of `S ⟶ U ⊗ T`, moved by Frobenius reciprocity to
`Tᘁ ⟶ Sᘁ ⊗ U`, is the canonical element there. The two composition pairings agree exactly because
both pairings are normalized, by a string computation closing up both sides; summing over `T`
with the completeness relation for the right duals of the simple objects gives the compatibility.
The triangle identities are zigzag identities. The one at induced objects is checked on the unit
summand, which determines morphisms of the centre into an induced object by the right adjunction.

Composing the unit of the right adjunction with the counit of the left adjunction gives the
**averaging identity**: at `⟨A, b⟩` the composite `A ⟶ ⨁ S, S ⊗ A ⊗ Sᘁ ⟶ A` is multiplication by
the global dimension `TauCeti.normGlobalDim C a = ∑ S, squaredNorm (a S)`, the summand of `S`
contributing its squared norm. When the global dimension is nonzero (for instance in
characteristic zero when `C` admits a pivotal structure, by `TauCeti.normGlobalDim_eq_globalDim`
and `TauCeti.globalDim_ne_zero`), this splits the unit of the right adjunction, as needed by the
semisimplicity criterion `TauCeti.IsFiniteSemisimpleCategory.of_natTrans` for the centre.

## Main declarations

* `CategoryTheory.Center.inductionForgetAdjunction`: the adjunction
  `Center.induction k C ⊣ Center.forget C`, so that `Center.induction k C` is a left adjoint
  (`CategoryTheory.Center.instIsLeftAdjointInduction`);
* `CategoryTheory.Center.inductionForgetAdjunction_unit_app` and
  `CategoryTheory.Center.ι_inductionForgetAdjunction_counit_app_f`: its unit and the components of
  its counit;
* `Center.forgetInductionAdjunction_unit_app_comp_inductionForgetAdjunction_counit_app_f`:
  the averaging identity.

## References

* P. Etingof, D. Nikshych, V. Ostrik, *On fusion categories*, Ann. of Math. **162** (2005), §§2, 5
* [P. Etingof, S. Gelaki, D. Nikshych, V. Ostrik, *Tensor categories*][egno15], §§7.13, 9.3
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Module TauCeti

universe w v u

namespace CategoryTheory.Center

attribute [local instance] Abelian.hasFiniteBiproducts

section String

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
variable (k : Type w) [Field k] [Preadditive C] [Linear k C] [MonoidalPreadditive C]
  [MonoidalLinear k C]

/-- **The string identity behind the normalization of the counit.** Closing up the composite of
the Frobenius reciprocity `(S ⟶ U ⊗ T) → (Tᘁ ⟶ Sᘁ ⊗ U)` of `b` with the mate of `g` by the
pairing of `Tᘁ` and `T` is closing up `b ≫ g` by the pairing of `Sᘁ` and `S`. -/
private theorem coevaluation_comp_whiskerRight_evaluation {S T U : C} [ExactPairing Sᘁ S]
    [ExactPairing Tᘁ T] (b : S ⟶ U ⊗ T) (g : U ⊗ T ⟶ S) :
    η_ (Tᘁ : C) T ≫ (tensorLeftHomEquiv Tᘁ Sᘁ S U ((tensorRightHomEquiv S Tᘁ T U).symm b) ≫
        inductionMate k U g) ▷ T ≫ ε_ T Tᘁ =
      η_ (Sᘁ : C) S ≫ (Sᘁ : C) ◁ (b ≫ g) ≫ ε_ S Sᘁ := by
  rw [comp_whiskerRight, Category.assoc, inductionMate_whiskerRight_evaluation,
    coevaluation_whiskerRight_tensorLeftHomEquiv_assoc, Equiv.apply_symm_apply, whiskerLeft_comp,
    Category.assoc]

end String

section Counit

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]

/-- The common prefix of the two sides of the compatibility of the counit with half-braidings:
move `A` out of `S ⊗ A ⊗ Sᘁ` to the right of `Sᘁ`, then past `U`, with the half-braiding `b`. -/
private def counitPrefix {A : C} (b : HalfBraiding A) (S U : C) :
    (S ⊗ A ⊗ Sᘁ) ⊗ U ⟶ (S ⊗ Sᘁ ⊗ U) ⊗ A :=
  𝟙 _ ⊗≫ S ◁ (b.β Sᘁ).hom ▷ U ⊗≫ S ◁ (Sᘁ : C) ◁ (b.β U).hom ⊗≫ 𝟙 _

/-- The contraction of `S` with `Sᘁ`, followed by the half-braiding at `U`, factors through
`counitPrefix`. -/
private theorem contract_whiskerRight_comp {A : C} (b : HalfBraiding A) {S : C}
    [P : ExactPairing Sᘁ S] (U : C) :
    (S ◁ (b.β Sᘁ).hom ≫ (α_ _ _ _).inv ≫ ε_ (Sᘁ : C) S ▷ A ≫ (λ_ A).hom) ▷ U ≫ (b.β U).hom =
      counitPrefix b S U ≫ ((α_ _ _ _).inv ≫ ε_ (Sᘁ : C) S ▷ U ≫ (λ_ U).hom) ▷ A := by
  calc
    _ = 𝟙 _ ⊗≫ S ◁ (b.β Sᘁ).hom ▷ U ⊗≫ (ε_ (Sᘁ : C) S ▷ (A ⊗ U) ≫ 𝟙_ C ◁ (b.β U).hom) ⊗≫
          𝟙 _ := by
      simp only [comp_whiskerRight]
      monoidal
    _ = _ := by
      rw [← whisker_exchange]
      simp only [counitPrefix, comp_whiskerRight]
      monoidal

/-- A morphism `p` applied after the contraction of `S` with `Sᘁ` past `β` can be applied before
the contraction instead, on the strand of `A` after `β`. -/
private theorem contract_comp {A A' S : C} [P : ExactPairing Sᘁ S] (β : A ⊗ Sᘁ ⟶ Sᘁ ⊗ A)
    (p : A ⟶ A') :
    S ◁ β ≫ (α_ _ _ _).inv ≫ ε_ (Sᘁ : C) S ▷ A ≫ (λ_ A).hom ≫ p =
      S ◁ (β ≫ (Sᘁ : C) ◁ p) ≫ (α_ _ _ _).inv ≫ ε_ (Sᘁ : C) S ▷ A' ≫ (λ_ A').hom := by
  calc
    _ = S ◁ β ⊗≫ (ε_ (Sᘁ : C) S ▷ A ≫ 𝟙_ C ◁ p) ⊗≫ 𝟙 _ := by
      monoidal
    _ = _ := by
      rw [← whisker_exchange]
      simp only [whiskerLeft_comp]
      monoidal

section UnitSummand

variable {R : C} [P : ExactPairing Rᘁ R] (φ : R ≅ 𝟙_ C)

/-- The inclusion `X ⟶ R ⊗ X ⊗ Rᘁ` through `φ⁻¹ : 𝟙_ C ⟶ R` and `φ.homᘁ : 𝟙_ C ⟶ Rᘁ` (the inverse
of `Center.inductionUnitSummandIso` when `R` represents the class of the unit), followed by the
contraction of `R ⊗ Rᘁ` past a half-braiding through a normalized pairing, is the identity. -/
private theorem rightAdjointMate_comp_contract (hP : η_ (Rᘁ : C) R ≫ ε_ R Rᘁ = 𝟙 (𝟙_ C))
    {A : C} (b : HalfBraiding A) :
    (ρ_ A).inv ≫ (λ_ (A ⊗ 𝟙_ C)).inv ≫ 𝟙_ C ◁ A ◁ φ.homᘁ ≫ φ.inv ▷ (A ⊗ Rᘁ) ≫
        R ◁ (b.β Rᘁ).hom ≫ (α_ _ _ _).inv ≫ ε_ (Rᘁ : C) R ▷ A ≫ (λ_ A).hom =
      𝟙 A := by
  have hnat := b.naturality (φ.homᘁ)
  -- The chosen right dual of the unit is the unit itself.
  dsimp only [HasRightDual.rightDual] at hnat
  rw [HalfBraiding.β_tensorUnit_hom] at hnat
  calc
    _ = 𝟙 _ ⊗≫ φ.inv ▷ A ⊗≫ R ◁ (A ◁ φ.homᘁ ≫ (b.β Rᘁ).hom) ⊗≫
          ε_ (Rᘁ : C) R ▷ A ⊗≫ 𝟙 _ := by
      rw [whisker_exchange_assoc]
      simp only [whiskerLeft_comp]
      monoidal
    _ = 𝟙 _ ⊗≫ φ.inv ▷ A ⊗≫ (R ◁ φ.homᘁ ≫ ε_ (Rᘁ : C) R) ▷ A ⊗≫ 𝟙 _ := by
      rw [hnat]
      simp only [whiskerLeft_comp, comp_whiskerRight]
      monoidal
    _ = 𝟙 _ ⊗≫ (φ.inv ≫ φ.hom) ▷ A ⊗≫ 𝟙 _ := by
      rw [whiskerLeft_rightAdjointMate_comp_evaluation φ hP]
      simp only [comp_whiskerRight]
      monoidal
    _ = _ := by
      rw [Iso.inv_hom_id]
      monoidal

/-- The contraction behind the left triangle identity at the summand `R ⊗ X ⊗ Rᘁ`: insert
`m' : Rᘁ ⟶ 𝟙_ C` after the inclusion `ι₀` through `φ⁻¹` and `m : 𝟙_ C ⟶ Rᘁ`, then contract `R`
with `m` through the pairing. When `m'` is a left inverse of `m` and contracting `R` with `m` is
`φ`, the result is the identity. The mates of `φ` are such `m` and `m'`, whose source and target
`(𝟙_ C)ᘁ` the coherence tactic does not identify with `𝟙_ C`; this lemma is stated for morphisms
out of `𝟙_ C` itself. -/
private theorem whiskerLeft_comp_contract_eq_id {X : C} {m : 𝟙_ C ⟶ Rᘁ} {m' : Rᘁ ⟶ 𝟙_ C}
    (hmm : m' ≫ m = 𝟙 _) (hm : R ◁ m ≫ ε_ (Rᘁ : C) R = (ρ_ R).hom ≫ φ.hom)
    {ι₀ : X ⟶ R ⊗ X ⊗ Rᘁ}
    (hι : ι₀ = (ρ_ X).inv ≫ (λ_ (X ⊗ 𝟙_ C)).inv ≫ 𝟙_ C ◁ X ◁ m ≫ φ.inv ▷ (X ⊗ Rᘁ)) :
    R ◁ (ι₀ ▷ Rᘁ ≫ (R ⊗ X ⊗ Rᘁ) ◁ m' ≫ (ρ_ _).hom ≫ (λ_ _).inv ≫ m ▷ (R ⊗ X ⊗ Rᘁ)) ≫
        (α_ _ _ _).inv ≫ ε_ (Rᘁ : C) R ▷ (R ⊗ X ⊗ Rᘁ) ≫ (λ_ _).hom =
      𝟙 _ := by
  calc
    _ = 𝟙 _ ⊗≫ R ◁ (ι₀ ▷ Rᘁ ≫ (R ⊗ X ⊗ Rᘁ) ◁ m') ⊗≫
          (R ◁ m ≫ ε_ (Rᘁ : C) R) ▷ (R ⊗ X ⊗ Rᘁ) ⊗≫ 𝟙 _ := by
      simp only [whiskerLeft_comp, comp_whiskerRight]
      monoidal
    _ = 𝟙 _ ⊗≫ R ◁ (X ◁ m' ≫ ι₀ ▷ 𝟙_ C) ⊗≫ ((ρ_ R).hom ≫ φ.hom) ▷ (R ⊗ X ⊗ Rᘁ) ⊗≫ 𝟙 _ := by
      rw [← whisker_exchange, hm]
    _ = 𝟙 _ ⊗≫ R ◁ X ◁ m' ⊗≫ (R ◁ ι₀ ≫ φ.hom ▷ (R ⊗ X ⊗ Rᘁ)) ⊗≫ 𝟙 _ := by
      simp only [whiskerLeft_comp, comp_whiskerRight]
      monoidal
    _ = 𝟙 _ ⊗≫ R ◁ X ◁ m' ⊗≫ φ.hom ▷ X ⊗≫ (𝟙_ C ◁ X ◁ m ≫ φ.inv ▷ (X ⊗ Rᘁ)) ⊗≫ 𝟙 _ := by
      rw [whisker_exchange, hι]
      simp only [whiskerLeft_comp]
      monoidal
    _ = 𝟙 _ ⊗≫ (R ⊗ X) ◁ m' ⊗≫ (φ.hom ≫ φ.inv) ▷ X ⊗≫ (R ⊗ X) ◁ m ⊗≫ 𝟙 _ := by
      rw [whisker_exchange]
      simp only [comp_whiskerRight]
      monoidal
    _ = 𝟙 _ ⊗≫ (R ⊗ X) ◁ (m' ≫ m) ⊗≫ 𝟙 _ := by
      rw [Iso.hom_inv_id, id_whiskerRight]
      monoidal
    _ = _ := by
      rw [hmm, whiskerLeft_id]
      monoidal

end UnitSummand

variable (k : Type w) [Field k] [Preadditive C] [Linear k C] [MonoidalPreadditive C]
  [MonoidalLinear k C]

/-- A term of the half-braiding of the induced object, followed by the contraction of `T` with
`Tᘁ` through a pairing of `Tᘁ` and `T`, factors through `counitPrefix`. -/
private theorem inductionTerm_comp_whiskerLeft_contract {A : C} (b : HalfBraiding A) {S T U : C}
    [P : ExactPairing Tᘁ T] (g : U ⊗ T ⟶ S) (f : S ⟶ U ⊗ T) :
    inductionTerm k A g f ≫
        U ◁ (T ◁ (b.β Tᘁ).hom ≫ (α_ _ _ _).inv ≫ ε_ (Tᘁ : C) T ▷ A ≫ (λ_ A).hom) =
      counitPrefix b S U ≫
        (S ◁ inductionMate k U g ≫ (tensorRightHomEquiv S Tᘁ T U).symm f) ▷ A := by
  have hnat : A ◁ inductionMate k U g ≫ (b.β Tᘁ).hom =
      (α_ _ _ _).inv ≫ (b.β Sᘁ).hom ▷ U ≫ (α_ _ _ _).hom ≫ (Sᘁ : C) ◁ (b.β U).hom ≫
        (α_ _ _ _).inv ≫ inductionMate k U g ▷ A := by
    rw [b.naturality, b.monoidal]
    simp only [Category.assoc]
  calc
    _ = 𝟙 _ ⊗≫ f ▷ A ▷ Sᘁ ▷ U ⊗≫ U ◁ T ◁ (A ◁ inductionMate k U g ≫ (b.β Tᘁ).hom) ⊗≫
          U ◁ ε_ (Tᘁ : C) T ▷ A ⊗≫ 𝟙 _ := by
      rw [inductionTerm_apply]
      simp only [whiskerLeft_comp]
      monoidal
    _ = 𝟙 _ ⊗≫ (f ▷ ((A ⊗ Sᘁ) ⊗ U) ≫ (U ⊗ T) ◁ ((b.β Sᘁ).hom ▷ U ⊗≫
          (Sᘁ : C) ◁ (b.β U).hom ⊗≫ inductionMate k U g ▷ A)) ⊗≫ U ◁ ε_ (Tᘁ : C) T ▷ A ⊗≫
          𝟙 _ := by
      rw [hnat]
      simp only [whiskerLeft_comp]
      monoidal
    _ = 𝟙 _ ⊗≫ (S ◁ ((b.β Sᘁ).hom ▷ U ⊗≫ (Sᘁ : C) ◁ (b.β U).hom ⊗≫
          inductionMate k U g ▷ A) ≫ f ▷ (Tᘁ ⊗ A)) ⊗≫ U ◁ ε_ (Tᘁ : C) T ▷ A ⊗≫ 𝟙 _ := by
      rw [whisker_exchange]
    _ = _ := by
      simp only [counitPrefix, tensorRightHomEquiv, Equiv.coe_fn_symm_mk, comp_whiskerRight]
      monoidal

end Counit

section Fusion

variable (k : Type w) [Field k] [IsAlgClosed k]
variable {C : Type u} [Category.{v} C] [Abelian C] [Linear k C] [MonoidalCategory C]
  [MonoidalPreadditive C] [MonoidalLinear k C] [RigidCategory C] [IsFiniteSemisimpleCategory C]
  [Simple (𝟙_ C)] [∀ X Y : C, FiniteDimensional k (X ⟶ Y)]

/-- **Comparison of canonical elements.** For simple `S` and `T` with normalized pairings, the
canonical element of `S ⟶ U ⊗ T`, transported to `(Sᘁ ⊗ U ⟶ Tᘁ) × (S ⊗ Tᘁ ⟶ U)` by the mate and
by Frobenius reciprocity, is the canonical element of `Tᘁ ⟶ Sᘁ ⊗ U` contracted with the evaluation
of `S`. The normalizations make the two pairings agree, by the string identity
`coevaluation_comp_whiskerRight_evaluation`. -/
private theorem sum_whiskerLeft_inductionMate_comp {S T U : C} [Simple S] [Simple T]
    [PS : ExactPairing Sᘁ S] [PT : ExactPairing Tᘁ T] (hS : η_ (Sᘁ : C) S ≫ ε_ S Sᘁ = 𝟙 (𝟙_ C))
    (hT : η_ (Tᘁ : C) T ≫ ε_ T Tᘁ = 𝟙 (𝟙_ C))
    {ι : Type*} [Fintype ι] [DecidableEq ι] (B : Basis ι k (S ⟶ U ⊗ T))
    {ι' : Type*} [Fintype ι'] [DecidableEq ι'] (P : Basis ι' k (Tᘁ ⟶ Sᘁ ⊗ U)) :
    ∑ i, S ◁ inductionMate k U (B.homDual i) ≫ (tensorRightHomEquiv S Tᘁ T U).symm (B i) =
      ∑ j, S ◁ (P.homDual j ≫ P j) ≫ (α_ _ _ _).inv ≫ ε_ (Sᘁ : C) S ▷ U ≫ (λ_ U).hom := by
  have h1 : (𝟙 (𝟙_ C)) ≠ 0 := id_ne_zero (𝟙_ C)
  -- Frobenius reciprocity `(S ⟶ U ⊗ T) ≃ (S ⊗ Tᘁ ⟶ U) ≃ (Tᘁ ⟶ Sᘁ ⊗ U)`.
  let q : (S ⟶ U ⊗ T) ≃ₗ[k] (Tᘁ ⟶ Sᘁ ⊗ U) :=
    (tensorRightHomLinearEquiv k S Tᘁ T U).symm.trans (tensorLeftHomLinearEquiv k Tᘁ Sᘁ S U)
  -- The mates of the dual basis of `B` are the dual basis of the transported basis.
  have hQ (i : ι) : (B.map q).homDual i = inductionMate k U (B.homDual i) := by
    symm
    rw [Basis.eq_homDual_iff]
    intro j
    obtain ⟨c, hc⟩ :=
      endomorphism_simple_eq_smul_id k ((B.map q) j ≫ inductionMate k U (B.homDual i))
    have key := coevaluation_comp_whiskerRight_evaluation k (B j) (B.homDual i)
    have hq : (B.map q) j =
        tensorLeftHomEquiv Tᘁ Sᘁ S U ((tensorRightHomEquiv S Tᘁ T U).symm (B j)) := by
      simp [q]
    rw [← hq, ← hc, B.apply_comp_homDual, MonoidalLinear.smul_whiskerRight, id_whiskerRight,
      Linear.smul_comp, Linear.comp_smul, Category.id_comp, hT] at key
    rw [← hc]
    split_ifs at key ⊢ with h
    · rw [whiskerLeft_id, Category.id_comp, hS] at key
      rw [smul_left_injective k h1 (key.trans (one_smul k _).symm), one_smul]
    · simp only [MonoidalPreadditive.whiskerLeft_zero, zero_comp, comp_zero] at key
      rw [smul_left_injective k h1 (key.trans (zero_smul k _).symm), zero_smul]
  -- Contracting with the evaluation of `S` is bilinear.
  let β : (Sᘁ ⊗ U ⟶ Tᘁ) →ₗ[k] (Tᘁ ⟶ Sᘁ ⊗ U) →ₗ[k] (S ⊗ Sᘁ ⊗ U ⟶ U) :=
    LinearMap.mk₂ k (fun p r ↦ S ◁ (p ≫ r) ≫ (α_ _ _ _).inv ≫ ε_ (Sᘁ : C) S ▷ U ≫ (λ_ U).hom)
      (fun p₁ p₂ r ↦ by simp [Preadditive.add_comp])
      (fun c p r ↦ by simp)
      (fun p r₁ r₂ ↦ by simp [Preadditive.comp_add])
      (fun c p r ↦ by simp)
  have h := Basis.sum_homDual_eq (B.map q) P β
  simp only [β, LinearMap.mk₂_apply] at h
  rw [← h]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [hQ i, whiskerLeft_comp, Category.assoc]
  congr 1
  -- Moving `q (B i)` back by the second reciprocity recovers the first reciprocity of `B i`.
  have hq : (tensorLeftHomEquiv Tᘁ Sᘁ S U).symm (q (B i)) =
      (tensorRightHomEquiv S Tᘁ T U).symm (B i) := by
    simp [q]
  rw [← hq, Basis.map_apply]
  dsimp only [tensorLeftHomEquiv, Equiv.coe_fn_symm_mk]

variable [Fintype (SimpleClasses C)]

/-- The component on the summand `S ⊗ A ⊗ Sᘁ` of the counit `inductionObj A ⟶ A` at an object
`⟨A, b⟩` of the centre: move `A` to the right of `Sᘁ` with `b`, then contract `S ⊗ Sᘁ` with the
evaluation of the normalized pairing `TauCeti.normalizedExactPairing k S`. -/
private def counitSummand {A : C} (b : HalfBraiding A) (S : SimpleClasses C) :
    inductionSummand A S ⟶ A :=
  S.repr ◁ (b.β S.reprᘁ).hom ≫ (α_ _ _ _).inv ≫
    @ExactPairing.evaluation C _ _ S.reprᘁ S.repr (normalizedExactPairing k S.repr) ▷ A ≫
      (λ_ A).hom

/-- The underlying morphism `⨁ S, S ⊗ A ⊗ Sᘁ ⟶ A` of the counit at `⟨A, b⟩`. -/
private def counitF {A : C} (b : HalfBraiding A) : inductionObj A ⟶ A :=
  biproduct.desc (counitSummand k b)

/-- **The counit commutes with the half-braidings.** For `⟨A, b⟩` in the centre, the morphism
`⨁ S, S ⊗ A ⊗ Sᘁ ⟶ A` contracting each summand with the normalized evaluation intertwines the
half-braiding of the induced object with `b`. -/
private theorem counitF_comm {A : C} (b : HalfBraiding A) (U : C) :
    counitF k b ▷ U ≫ (b.β U).hom = inductionβHom k A U ≫ U ◁ counitF k b := by
  refine biproduct.hom_ext_whiskerRight fun S ↦ ?_
  let PS := normalizedExactPairing k S.repr
  have hS := normalizedExactPairing_coevaluation_comp_evaluation k S.repr
  -- Insert the decomposition of the identity of `inductionObj A` after the half-braiding.
  have hR : biproduct.ι (inductionSummand A) S ▷ U ≫ inductionβHom k A U ≫ U ◁ counitF k b =
      ∑ T, inductionβComponent k A U S T ≫ U ◁ counitSummand k b T := by
    calc
      _ = biproduct.ι (inductionSummand A) S ▷ U ≫ inductionβHom k A U ≫
            U ◁ (∑ T, biproduct.π (inductionSummand A) T ≫ biproduct.ι (inductionSummand A) T) ≫
              U ◁ counitF k b := by
        rw [biproduct.total, whiskerLeft_id, Category.id_comp]
      _ = ∑ T, (biproduct.ι (inductionSummand A) S ▷ U ≫ inductionβHom k A U ≫
            U ◁ biproduct.π (inductionSummand A) T) ≫
              U ◁ (biproduct.ι (inductionSummand A) T ≫ counitF k b) := by
        simp only [whiskerLeft_sum, Preadditive.sum_comp, Preadditive.comp_sum, Category.assoc,
          whiskerLeft_comp]
      _ = _ := by
        simp only [ι_whiskerRight_inductionβHom_whiskerLeft_π, counitF, biproduct.ι_desc]
  rw [hR, ← comp_whiskerRight_assoc, counitF, biproduct.ι_desc, counitSummand,
    contract_whiskerRight_comp (P := PS)]
  -- Each term factors through `counitPrefix`.
  have hT (T : SimpleClasses C) :
      inductionβComponent k A U S T ≫ U ◁ counitSummand k b T =
        counitPrefix b S.repr U ≫
          (∑ j, S.repr ◁ ((Module.finBasis k ((T.reprᘁ : C) ⟶ (S.reprᘁ : C) ⊗ U)).homDual j ≫
            Module.finBasis k ((T.reprᘁ : C) ⟶ (S.reprᘁ : C) ⊗ U) j) ≫ (α_ _ _ _).inv ≫
              ε_ (S.reprᘁ : C) S.repr ▷ U ≫ (λ_ U).hom) ▷ A := by
    rw [inductionβComponent_eq k A U S T (Module.finBasis k _), Preadditive.sum_comp]
    simp only [counitSummand, inductionTerm_comp_whiskerLeft_contract k b
      (P := normalizedExactPairing k T.repr)]
    rw [← sum_whiskerLeft_inductionMate_comp k (PS := PS)
      (PT := normalizedExactPairing k T.repr) hS
      (normalizedExactPairing_coevaluation_comp_evaluation k T.repr)
      (Module.finBasis k (S.repr ⟶ U ⊗ T.repr))
      (Module.finBasis k ((T.reprᘁ : C) ⟶ (S.reprᘁ : C) ⊗ U)), sum_whiskerRight,
      Preadditive.comp_sum]
  -- The completeness relation for the right duals of the representatives, which contain every
  -- simple class exactly once since duality of simple classes is an involution.
  have hc : ∑ T : SimpleClasses C, ∑ j,
      (Module.finBasis k ((T.reprᘁ : C) ⟶ (S.reprᘁ : C) ⊗ U)).homDual j ≫
        Module.finBasis k ((T.reprᘁ : C) ⟶ (S.reprᘁ : C) ⊗ U) j = 𝟙 _ :=
    sum_sum_homDual_comp_eq_id_of_bijective (k := k) (fun T : SimpleClasses C ↦ T.reprᘁ)
      (by simpa only [← SimpleClasses.dual_classOf, SimpleClasses.classOf_repr] using
        SimpleClasses.dual_involutive.bijective) _ _
  simp only [hT, ← Preadditive.comp_sum, ← sum_whiskerRight, ← Preadditive.sum_comp,
    ← whiskerLeft_sum, hc, whiskerLeft_id, Category.id_comp]

/-- The counit is natural in the object of the centre. -/
private theorem counitF_naturality {A A' : C} {b : HalfBraiding A} {b' : HalfBraiding A'}
    (f : A ⟶ A') (hf : ∀ U : C, f ▷ U ≫ (b'.β U).hom = (b.β U).hom ≫ U ◁ f) :
    inductionMap f ≫ counitF k b' = counitF k b ≫ f := by
  refine biproduct.hom_ext' _ _ fun S ↦ ?_
  simp only [counitF, biproduct.ι_map_assoc, biproduct.ι_desc, biproduct.ι_desc_assoc,
    counitSummand, Category.assoc]
  calc
    _ = 𝟙 _ ⊗≫ S.repr ◁ (f ▷ S.reprᘁ ≫ (b'.β S.reprᘁ).hom) ⊗≫
          @ExactPairing.evaluation C _ _ S.reprᘁ S.repr (normalizedExactPairing k S.repr) ▷ A' ⊗≫
            𝟙 _ := by
      simp only [whiskerLeft_comp]
      monoidal
    _ = 𝟙 _ ⊗≫ S.repr ◁ (b.β S.reprᘁ).hom ⊗≫
          ((S.repr ⊗ S.reprᘁ) ◁ f ≫
            @ExactPairing.evaluation C _ _ S.reprᘁ S.repr (normalizedExactPairing k S.repr) ▷
              A') ⊗≫ 𝟙 _ := by
      rw [hf]
      simp only [whiskerLeft_comp]
      monoidal
    _ = _ := by
      rw [whisker_exchange]
      monoidal

variable (C) in
/-- The normalized pairing of `Rᘁ` and the representative `R` of the class of the unit, whose
evaluation contracts the summand of `R` in the counit. -/
private abbrev unitClassPairing :
    ExactPairing (SimpleClasses.classOf (𝟙_ C)).reprᘁ (SimpleClasses.classOf (𝟙_ C)).repr :=
  normalizedExactPairing k _

/-- The unit `X ⟶ ⨁ S, S ⊗ X ⊗ Sᘁ`: the inclusion of the summand of the class of the unit object,
identified with `X` by `Center.inductionUnitSummandIso`. -/
private def unitF (X : C) : X ⟶ inductionObj X :=
  (inductionUnitSummandIso X).inv ≫ biproduct.ι (inductionSummand X) (SimpleClasses.classOf (𝟙_ C))

omit [MonoidalPreadditive C] [IsFiniteSemisimpleCategory C] in
/-- The unit is natural. -/
private theorem unitF_naturality {X Y : C} (f : X ⟶ Y) :
    f ≫ unitF Y = unitF X ≫ inductionMap f := by
  rw [unitF, unitF, inductionUnitSummandIso_inv_naturality_assoc, Category.assoc, biproduct.ι_map]

omit [Fintype (SimpleClasses C)] in
/-- The half-braiding of the induced object at the right dual of the representative of a simple
class `S` other than that of the unit has no component from the unit summand to itself. -/
private theorem inductionβComponent_rightDual_of_ne (X : C) {S : SimpleClasses C}
    (hS : S ≠ SimpleClasses.classOf (𝟙_ C)) :
    inductionβComponent k X (S.reprᘁ) (SimpleClasses.classOf (𝟙_ C))
      (SimpleClasses.classOf (𝟙_ C)) = 0 := by
  set φ := SimpleClasses.classOfReprIso (𝟙_ C)
  have hzero (h : (SimpleClasses.classOf (𝟙_ C)).repr ⟶
      S.reprᘁ ⊗ (SimpleClasses.classOf (𝟙_ C)).repr) : h = 0 := by
    have h0 := SimpleClasses.hom_rightDual_eq_zero (X := S.repr)
      (by rwa [SimpleClasses.classOf_repr]) (φ.inv ≫ h ≫ S.reprᘁ ◁ φ.hom ≫ (ρ_ _).hom)
    calc
      h = φ.hom ≫ (φ.inv ≫ h ≫ S.reprᘁ ◁ φ.hom ≫ (ρ_ _).hom) ≫ (ρ_ _).inv ≫
          S.reprᘁ ◁ φ.inv := by
        simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id_assoc,
          ← whiskerLeft_comp, Iso.hom_inv_id, whiskerLeft_id, Category.comp_id]
      _ = 0 := by rw [h0, zero_comp, comp_zero]
  rw [inductionβComponent_eq k X _ _ _ (Module.finBasis k _)]
  exact Finset.sum_eq_zero fun i _ ↦ by rw [hzero (Module.finBasis k _ i), map_zero]

omit [Fintype (SimpleClasses C)] in
/-- The component of the half-braiding of the induced object at the right dual `Rᘁ` of the
representative `R` of the class of the unit, from the summand of `R` to itself, computed through
the right adjoint mates of `R ≅ 𝟙_ C`. -/
private theorem inductionβComponent_rightDual_unitClass (X : C) :
    inductionβComponent k X ((SimpleClasses.classOf (𝟙_ C)).reprᘁ)
        (SimpleClasses.classOf (𝟙_ C)) (SimpleClasses.classOf (𝟙_ C)) =
      inductionSummand X (SimpleClasses.classOf (𝟙_ C)) ◁
          (SimpleClasses.classOfReprIso (𝟙_ C)).invᘁ ≫ (ρ_ _).hom ≫ (λ_ _).inv ≫
        (SimpleClasses.classOfReprIso (𝟙_ C)).homᘁ ▷
          inductionSummand X (SimpleClasses.classOf (𝟙_ C)) := by
  rw [← Category.assoc (ρ_ _).hom, ← inductionβComponent_tensorUnit_self k X,
    ← whiskerLeft_comp_inductionβComponent, ← whiskerLeft_comp_assoc, ← comp_rightAdjointMate,
    Iso.hom_inv_id, rightAdjointMate_id, whiskerLeft_id, Category.id_comp]

/-- **Left triangle identity**, after the projection onto the summand of the class of the unit. -/
private theorem inductionMap_unitF_comp_counitF_comp_π (X : C) :
    inductionMap (unitF X) ≫ counitF k (inductionHalfBraiding k X) ≫
        biproduct.π (inductionSummand X) (SimpleClasses.classOf (𝟙_ C)) =
      biproduct.π (inductionSummand X) (SimpleClasses.classOf (𝟙_ C)) := by
  refine biproduct.hom_ext' _ _ fun S ↦ ?_
  rw [biproduct.ι_map_assoc, counitF, biproduct.ι_desc_assoc, counitSummand,
    inductionHalfBraiding_β_hom]
  simp only [Category.assoc]
  -- Move the projection onto the unit summand before the contraction, next to the half-braiding.
  rw [contract_comp (P := normalizedExactPairing k S.repr), ← whiskerLeft_comp_assoc, unitF,
    comp_whiskerRight]
  simp only [Category.assoc]
  rw [ι_whiskerRight_inductionβHom_whiskerLeft_π]
  by_cases hS : S = SimpleClasses.classOf (𝟙_ C)
  · subst hS
    rw [biproduct.ι_π_self, inductionβComponent_rightDual_unitClass k X]
    exact whiskerLeft_comp_contract_eq_id (P := unitClassPairing k C)
      (SimpleClasses.classOfReprIso (𝟙_ C))
      (by rw [← comp_rightAdjointMate, Iso.hom_inv_id, rightAdjointMate_id])
      (whiskerLeft_rightAdjointMate_comp_evaluation (P := unitClassPairing k C) _
        (normalizedExactPairing_coevaluation_comp_evaluation k _))
      (inductionUnitSummandIso_inv X)
  · rw [inductionβComponent_rightDual_of_ne k X hS, comp_zero,
      MonoidalPreadditive.whiskerLeft_zero, zero_comp, biproduct.ι_π_ne _ hS]

/-- **Right triangle identity**: the unit followed by the counit is the identity. -/
private theorem unitF_comp_counitF {A : C} (b : HalfBraiding A) :
    unitF A ≫ counitF k b = 𝟙 A := by
  rw [unitF, Category.assoc, counitF, biproduct.ι_desc, counitSummand,
    inductionUnitSummandIso_inv]
  simp only [Category.assoc]
  exact rightAdjointMate_comp_contract (P := unitClassPairing k C)
    (SimpleClasses.classOfReprIso (𝟙_ C))
    (normalizedExactPairing_coevaluation_comp_evaluation k _) b

/-! ### The adjunction -/

variable (C)

/-- **Left adjunction for centre induction**: `Center.induction k C ⊣ Center.forget C`, for a
fusion category `C` over an algebraically closed field: a rigid `k`-linear finite semisimple
abelian monoidal category with simple unit, finitely many simple classes and finite-dimensional
morphism spaces. No pivotal structure is assumed. The unit includes `X` into the summand of the
class `R` of the unit object of `⨁ S, S ⊗ X ⊗ Sᘁ`, and the counit at `⟨A, b⟩` contracts each summand
`S ⊗ A ⊗ Sᘁ` with the evaluation of `TauCeti.normalizedExactPairing k S` after moving `A` to the
right of `Sᘁ` with `b`. That the counit commutes with the half-braidings is where the normalization
`η ≫ ε_ S Sᘁ = 𝟙` enters. -/
def inductionForgetAdjunction : induction k C ⊣ forget C :=
  -- The objects of the morphisms below are projections out of `Center C`, where `rw` and `simp`
  -- cannot rewrite (the abstracted motive is not type correct), so the steps that rewrite the
  -- half-braiding of the induced object or reassociate are explicit `Eq.trans` terms.
  Adjunction.mkOfUnitCounit
    { unit :=
        { app X := unitF X
          naturality _ _ f := unitF_naturality f }
      counit :=
        { app Z :=
            { f := counitF k Z.2
              comm U := (counitF_comm k Z.2 U).trans
                (congrArg (· ≫ U ◁ counitF k Z.2) (inductionHalfBraiding_β_hom k Z.1 U).symm) }
          naturality _ _ h := Center.ext _ _ (counitF_naturality k h.f h.comm) }
      left_triangle := by
        refine NatTrans.ext (funext fun X ↦ ?_)
        dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
          Functor.associator_hom_app, NatTrans.id_app, Functor.comp_obj, Functor.id_obj]
        rw [Category.id_comp]
        refine induction_hom_ext k ?_
        exact (Category.assoc _ _ _).trans
          ((inductionMap_unitF_comp_counitF_comp_π k X).trans (Category.id_comp _).symm)
      right_triangle := by
        refine NatTrans.ext (funext fun Z ↦ ?_)
        exact (congrArg (unitF Z.1 ≫ ·) (Category.id_comp (counitF k Z.2))).trans
          (unitF_comp_counitF k Z.2) }

/-- `Center.induction k C` is a left adjoint (in particular, it preserves all colimits that exist
in `C`). -/
instance instIsLeftAdjointInduction : (induction k C).IsLeftAdjoint :=
  (inductionForgetAdjunction k C).isLeftAdjoint

variable {C}

/-- The unit of `inductionForgetAdjunction` at `X` includes `X` into the summand of the class of the
unit object, identified with `X` by `Center.inductionUnitSummandIso`. -/
@[simp]
theorem inductionForgetAdjunction_unit_app (X : C) :
    (inductionForgetAdjunction k C).unit.app X =
      (inductionUnitSummandIso X).inv ≫
        biproduct.ι (inductionSummand X) (SimpleClasses.classOf (𝟙_ C)) := by
  simp only [inductionForgetAdjunction, Adjunction.mkOfUnitCounit_unit, unitF]
  -- The two sides agree except in the implicit objects of the composites, which are written
  -- `inductionObj X` on the left and `⨁ inductionSummand X`, the abbreviation it unfolds to, on
  -- the right; `simp` does not rewrite these objects.
  rfl

/-- The counit of `inductionForgetAdjunction` at `⟨A, b⟩`, on the summand `S ⊗ A ⊗ Sᘁ`: move `A`
to the right of `Sᘁ` with `b`, then contract `S ⊗ Sᘁ` with the evaluation of the normalized pairing
`TauCeti.normalizedExactPairing k S`. -/
@[reassoc, simp]
theorem ι_inductionForgetAdjunction_counit_app_f (Z : Center C) (S : SimpleClasses C) :
    biproduct.ι (inductionSummand Z.1) S ≫ ((inductionForgetAdjunction k C).counit.app Z).f =
      S.repr ◁ (Z.2.β S.reprᘁ).hom ≫ (α_ _ _ _).inv ≫
        @ExactPairing.evaluation C _ _ S.reprᘁ S.repr (normalizedExactPairing k S.repr) ▷ Z.1 ≫
          (λ_ Z.1).hom :=
  biproduct.ι_desc _ _

omit [IsAlgClosed k] [MonoidalPreadditive C] [IsFiniteSemisimpleCategory C] [Simple (𝟙_ C)]
  [∀ X Y : C, FiniteDimensional k (X ⟶ Y)] in
/-- A composite through `inductionObj A` is the sum of its composites through the summands. -/
private theorem comp_eq_sum_π_comp_ι {W V A : C} (f : W ⟶ inductionObj A)
    (g : inductionObj A ⟶ V) :
    f ≫ g = ∑ S, (f ≫ biproduct.π (inductionSummand A) S) ≫
      (biproduct.ι (inductionSummand A) S ≫ g) := by
  conv_lhs => rw [← Category.id_comp g, ← biproduct.total, Preadditive.sum_comp,
    Preadditive.comp_sum]
  simp only [Category.assoc]

/-- **The averaging identity.** For an object `⟨A, b⟩` of the centre, the unit
`A ⟶ ⨁ S, S ⊗ A ⊗ Sᘁ` of `forgetInductionAdjunction` followed by the counit of
`inductionForgetAdjunction` is multiplication by the global dimension
`TauCeti.normGlobalDim C a = ∑ S, squaredNorm (a S)`, for any isomorphisms `a S : S ≅ Sᘁᘁ`. The
summand of `S` contributes the squared norm of `S`. -/
theorem forgetInductionAdjunction_unit_app_comp_inductionForgetAdjunction_counit_app_f
    (Z : Center C) (a : ∀ S : SimpleClasses C, S.repr ≅ ((S.repr)ᘁ : C)ᘁ) :
    ((forgetInductionAdjunction k C).unit.app Z ≫ (inductionForgetAdjunction k C).counit.app Z).f =
      (λ_ Z.1).inv ≫ normGlobalDim C a ▷ Z.1 ≫ (λ_ Z.1).hom := by
  rw [normGlobalDim_congr C k a fun S ↦ normalizedDoubleDualIso k S.repr, normGlobalDim_def,
    sum_whiskerRight, Preadditive.sum_comp, Preadditive.comp_sum, Center.comp_f]
  refine (comp_eq_sum_π_comp_ι (A := Z.1) _ _).trans (Finset.sum_congr rfl fun S _ ↦ ?_)
  let := normalizedExactPairing k S.repr
  rw [ι_inductionForgetAdjunction_counit_app_f]
  refine (congrArg (· ≫ _) (forgetInductionAdjunction_unit_app_f_comp_π k C Z S)).trans ?_
  dsimp only [Functor.id_obj]
  simp only [Category.assoc]
  have hnat := Z.2.naturality (η_ S.repr S.reprᘁ)
  rw [Z.2.monoidal, HalfBraiding.β_tensorUnit_hom] at hnat
  calc
    _ = 𝟙 _ ⊗≫ (Z.1 ◁ η_ S.repr S.reprᘁ ≫ (α_ _ _ _).inv ≫ (Z.2.β S.repr).hom ▷ S.reprᘁ ≫
          (α_ _ _ _).hom ≫ S.repr ◁ (Z.2.β S.reprᘁ).hom ≫ (α_ _ _ _).inv) ⊗≫
            ε_ (S.reprᘁ : C) S.repr ▷ Z.1 ⊗≫ 𝟙 _ := by
      monoidal
    _ = 𝟙 _ ⊗≫ (η_ S.repr S.reprᘁ ≫ ε_ (S.reprᘁ : C) S.repr) ▷ Z.1 ⊗≫ 𝟙 _ := by
      rw [hnat]
      simp only [comp_whiskerRight]
      monoidal
    _ = _ := by
      rw [coevaluation_comp_normalizedExactPairing_evaluation]
      monoidal

end Fusion

end CategoryTheory.Center
