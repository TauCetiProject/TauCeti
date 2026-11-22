/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Monoidal.Center.Induction.Adjunction
public import TauCeti.CategoryTheory.Monoidal.Pivotal.SquaredNorm

/-!
# The left adjunction for induction into the Drinfeld centre

Let `C` be a fusion category over an algebraically closed field `k`: a rigid `k`-linear finite
semisimple abelian monoidal category with simple unit, finitely many simple classes and
finite-dimensional morphism spaces. In `TauCeti.CategoryTheory.Monoidal.Center.Induction.Adjunction`
the induction functor `Center.induction k C : C ⥤ Center C`, `X ↦ ⨁ S, S ⊗ X ⊗ Sᘁ`, is right adjoint
to the forgetful functor. This file shows that it is also left adjoint to it, with no pivotal
structure assumed: `Center.inductionForgetAdjunction k C : Center.induction k C ⊣ Center.forget C`.

The unit `X ⟶ ⨁ S, S ⊗ X ⊗ Sᘁ` includes `X` into the summand of the class `R` of the unit object.
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

/-- Inserting the coevaluation of `Tᘁ ⊗ T` before the Frobenius reciprocity through `Sᘁ` is
inserting the coevaluation of `Sᘁ ⊗ S` before the Frobenius reciprocity through `Tᘁ`. -/
@[reassoc]
private theorem coevaluation_whiskerRight_tensorLeftHomEquiv {S T U : C} [ExactPairing Sᘁ S]
    [ExactPairing Tᘁ T] (h : S ⊗ Tᘁ ⟶ U) :
    η_ (Tᘁ : C) T ≫ tensorLeftHomEquiv Tᘁ Sᘁ S U h ▷ T ≫ (α_ _ _ _).hom =
      η_ (Sᘁ : C) S ≫ (Sᘁ : C) ◁ tensorRightHomEquiv S Tᘁ T U h := by
  dsimp only [tensorLeftHomEquiv, tensorRightHomEquiv, Equiv.coe_fn_mk]
  calc
    _ = 𝟙 _ ⊗≫ (𝟙_ C ◁ η_ (Tᘁ : C) T ≫ η_ (Sᘁ : C) S ▷ (Tᘁ ⊗ T)) ⊗≫ (Sᘁ : C) ◁ h ▷ T ⊗≫
          𝟙 _ := by
      simp only [comp_whiskerRight, Category.assoc]
      monoidal
    _ = 𝟙 _ ⊗≫ (η_ (Sᘁ : C) S ▷ 𝟙_ C ≫ (Sᘁ ⊗ S) ◁ η_ (Tᘁ : C) T) ⊗≫ (Sᘁ : C) ◁ h ▷ T ⊗≫
          𝟙 _ := by
      rw [whisker_exchange]
    _ = _ := by
      simp only [whiskerLeft_comp]
      monoidal

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

end CategoryTheory.Center

namespace TauCeti

section DualCompleteness

open SimpleClasses

variable {k : Type w} [Field k] [IsAlgClosed k]
variable {C : Type u} [Category.{v} C] [Abelian C] [Linear k C] [MonoidalCategory C]
  [MonoidalPreadditive C] [RigidCategory C] [IsFiniteSemisimpleCategory C] [Simple (𝟙_ C)]
  [∀ X Y : C, FiniteDimensional k (X ⟶ Y)]

omit [∀ X Y : C, FiniteDimensional k (X ⟶ Y)] in
/-- There are no nonzero morphisms between the right duals of representatives of distinct simple
classes. -/
private theorem rightDual_repr_hom_eq_zero {T T' : SimpleClasses C} (h : T ≠ T')
    (f : T.reprᘁ ⟶ T'.reprᘁ) : f = 0 := by
  by_contra hf
  have := isIso_of_hom_simple hf
  obtain ⟨a⟩ := nonempty_iso_rightDual_rightDual T.repr
  obtain ⟨a'⟩ := nonempty_iso_rightDual_rightDual T'.repr
  exact h ((eq_iff_nonempty_iso T T').2 ⟨a ≪≫ (asIso f).rightAdjointMate.symm ≪≫ a'.symm⟩)

/-- **The completeness relation through right duals.** In a finite semisimple rigid category with
simple unit, choose for every simple class `T` a basis `b T` of the morphisms from the right dual
of its representative into `W`. Then the identity of `W` is the sum of the composites of the dual
basis elements with the basis elements. -/
private theorem sum_sum_homDual_comp_eq_id_rightDual [Fintype (SimpleClasses C)] (W : C)
    {ι : SimpleClasses C → Type*} [∀ T, Fintype (ι T)] [∀ T, DecidableEq (ι T)]
    (b : ∀ T : SimpleClasses C, Basis (ι T) k (T.reprᘁ ⟶ W)) :
    ∑ T, ∑ i, (b T).homDual i ≫ b T i = 𝟙 W := by
  classical
  refine (𝟭 C).hom_ext_of_simple fun V _ t ↦ ?_
  simp only [Functor.id_map]
  -- `V` is isomorphic to the right dual of the representative of the class of `Vᘁ`.
  obtain ⟨a⟩ := nonempty_iso_rightDual_rightDual V
  let θ : V ≅ (classOf (Vᘁ : C)).reprᘁ := a ≪≫ (classOfReprIso (Vᘁ : C)).rightAdjointMate
  suffices H : ∀ s : (classOf (Vᘁ : C)).reprᘁ ⟶ W, s ≫ ∑ T, ∑ i, (b T).homDual i ≫ b T i = s by
    simpa using congrArg (θ.hom ≫ ·) (H (θ.inv ≫ t))
  intro s
  simp only [Preadditive.comp_sum]
  rw [Finset.sum_eq_single (classOf (Vᘁ : C))]
  · simp only [← Category.assoc, Basis.comp_homDual, Linear.smul_comp, Category.id_comp,
      Basis.sum_repr]
  · intro T _ hT
    refine Finset.sum_eq_zero fun i _ ↦ ?_
    rw [← Category.assoc, rightDual_repr_hom_eq_zero (Ne.symm hT) (s ≫ (b T).homDual i), zero_comp]
  · simp

end DualCompleteness

end TauCeti

namespace CategoryTheory.Center

attribute [local instance] Abelian.hasFiniteBiproducts

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

section UnitSummand

variable {R : C} [P : ExactPairing Rᘁ R] (φ : R ≅ 𝟙_ C)

/-- For `R ≅ 𝟙_ C` and a pairing of `Rᘁ` and `R`, the morphism `𝟙_ C ⟶ Rᘁ` obtained from the
coevaluation. -/
private def unitDualHom : 𝟙_ C ⟶ Rᘁ :=
  η_ (Rᘁ : C) R ≫ (Rᘁ : C) ◁ φ.hom ≫ (ρ_ _).hom

/-- Contracting `R` with `unitDualHom φ` is the identification `R ≅ 𝟙_ C`, by the zigzag
identity of the pairing. -/
private theorem whiskerLeft_unitDualHom_comp_evaluation :
    R ◁ unitDualHom φ ≫ ε_ (Rᘁ : C) R = (ρ_ R).hom ≫ φ.hom := by
  calc
    _ = 𝟙 _ ⊗≫ R ◁ η_ (Rᘁ : C) R ⊗≫ ((R ⊗ Rᘁ) ◁ φ.hom ≫ ε_ (Rᘁ : C) R ▷ 𝟙_ C) ⊗≫ 𝟙 _ := by
      simp only [unitDualHom, whiskerLeft_comp]
      monoidal
    _ = 𝟙 _ ⊗≫ (R ◁ η_ (Rᘁ : C) R ⊗≫ ε_ (Rᘁ : C) R ▷ R) ⊗≫ φ.hom := by
      rw [whisker_exchange]
      monoidal
    _ = _ := by
      rw [ExactPairing.coevaluation_evaluation'']
      monoidal

/-- `unitDualHom φ` has a retraction. -/
private theorem unitDualHom_comp_retraction :
    unitDualHom φ ≫ (λ_ _).inv ≫ φ.inv ▷ _ ≫ ε_ (Rᘁ : C) R = 𝟙 (𝟙_ C) := by
  rw [leftUnitor_inv_naturality_assoc, whisker_exchange_assoc,
    whiskerLeft_unitDualHom_comp_evaluation, rightUnitor_naturality_assoc, Iso.inv_hom_id,
    Category.comp_id, ← unitors_equal, Iso.inv_hom_id]

/-- The inclusion `X ⟶ R ⊗ X ⊗ Rᘁ` through `φ⁻¹ : 𝟙_ C ⟶ R` and `unitDualHom φ`. -/
private def unitIncl (X : C) : X ⟶ R ⊗ X ⊗ Rᘁ :=
  (λ_ X).inv ≫ φ.inv ▷ X ≫ (ρ_ _).inv ≫ (R ⊗ X) ◁ unitDualHom φ ≫ (α_ _ _ _).hom

/-- `unitIncl φ` is natural. -/
private theorem unitIncl_naturality {X Y : C} (f : X ⟶ Y) :
    f ≫ unitIncl φ Y = unitIncl φ X ≫ R ◁ f ▷ Rᘁ := by
  simp only [unitIncl, Category.assoc]
  rw [leftUnitor_inv_naturality_assoc, whisker_exchange_assoc, rightUnitor_inv_naturality_assoc,
    ← whisker_exchange_assoc, associator_naturality_middle]

/-- The inclusion `unitIncl φ` followed by the contraction of `R ⊗ Rᘁ` past a half-braiding is
the identity. -/
private theorem unitIncl_comp_contract {A : C} (b : HalfBraiding A) :
    unitIncl φ A ≫ R ◁ (b.β Rᘁ).hom ≫ (α_ _ _ _).inv ≫ ε_ (Rᘁ : C) R ▷ A ≫ (λ_ A).hom =
      𝟙 A := by
  have hnat := b.naturality (unitDualHom φ)
  rw [HalfBraiding.β_tensorUnit_hom] at hnat
  calc
    _ = 𝟙 _ ⊗≫ φ.inv ▷ A ⊗≫ R ◁ (A ◁ unitDualHom φ ≫ (b.β Rᘁ).hom) ⊗≫
          ε_ (Rᘁ : C) R ▷ A ⊗≫ 𝟙 _ := by
      simp only [unitIncl, whiskerLeft_comp]
      monoidal
    _ = 𝟙 _ ⊗≫ φ.inv ▷ A ⊗≫ (R ◁ unitDualHom φ ≫ ε_ (Rᘁ : C) R) ▷ A ⊗≫ 𝟙 _ := by
      rw [hnat]
      simp only [whiskerLeft_comp, comp_whiskerRight]
      monoidal
    _ = 𝟙 _ ⊗≫ (φ.inv ≫ φ.hom) ▷ A ⊗≫ 𝟙 _ := by
      rw [whiskerLeft_unitDualHom_comp_evaluation]
      simp only [comp_whiskerRight]
      monoidal
    _ = _ := by
      rw [Iso.inv_hom_id]
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
  change _ = (tensorLeftHomEquiv Tᘁ Sᘁ S U).symm (q (B i))
  simp [q]

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

omit [IsAlgClosed k] [IsFiniteSemisimpleCategory C] [Simple (𝟙_ C)]
  [∀ X Y : C, FiniteDimensional k (X ⟶ Y)] in
/-- Morphisms out of `inductionObj X ⊗ U` are determined by their restrictions to the summands. -/
private theorem whiskerRight_hom_ext {X U Y : C}
    {f g : inductionObj X ⊗ U ⟶ Y}
    (h : ∀ S, biproduct.ι (inductionSummand X) S ▷ U ≫ f =
      biproduct.ι (inductionSummand X) S ▷ U ≫ g) : f = g := by
  have key (φ : inductionObj X ⊗ U ⟶ Y) : φ = ∑ S, biproduct.π (inductionSummand X) S ▷ U ≫
      biproduct.ι (inductionSummand X) S ▷ U ≫ φ := by
    simp only [← Preadditive.sum_comp, ← comp_whiskerRight_assoc, ← sum_whiskerRight,
      biproduct.total, id_whiskerRight, Category.id_comp]
  rw [key f, key g]
  simp only [h]

/-- **The counit commutes with the half-braidings.** For `⟨A, b⟩` in the centre, the morphism
`⨁ S, S ⊗ A ⊗ Sᘁ ⟶ A` contracting each summand with the normalized evaluation intertwines the
half-braiding of the induced object with `b`. -/
private theorem counitF_comm {A : C} (b : HalfBraiding A) (U : C) :
    counitF k b ▷ U ≫ (b.β U).hom = inductionβHom k A U ≫ U ◁ counitF k b := by
  refine whiskerRight_hom_ext fun S ↦ ?_
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
  simp only [hT, ← Preadditive.comp_sum, ← sum_whiskerRight, ← Preadditive.sum_comp,
    ← whiskerLeft_sum, sum_sum_homDual_comp_eq_id_rightDual, whiskerLeft_id, Category.id_comp]

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

/-- The unit `X ⟶ ⨁ S, S ⊗ X ⊗ Sᘁ`: the inclusion of the summand of the class `R` of the unit
object, through `R ≅ 𝟙_ C` and the coevaluation of the normalized pairing of `Rᘁ` and `R`. -/
private def unitF (X : C) : X ⟶ inductionObj X :=
  unitIncl (P := normalizedExactPairing k (SimpleClasses.classOf (𝟙_ C)).repr)
      (SimpleClasses.classOfReprIso (𝟙_ C)) X ≫
    biproduct.ι (inductionSummand X) (SimpleClasses.classOf (𝟙_ C))

/-- The unit is natural. -/
private theorem unitF_naturality {X Y : C} (f : X ⟶ Y) :
    f ≫ unitF k Y = unitF k X ≫ inductionMap f := by
  rw [unitF, unitF, reassoc_of% unitIncl_naturality
    (P := normalizedExactPairing k (SimpleClasses.classOf (𝟙_ C)).repr), Category.assoc,
    biproduct.ι_map]

omit [Fintype (SimpleClasses C)] in
/-- The morphism `𝟙_ C ⟶ Rᘁ`, for `R` the representative of the class of the unit, used in the
unit of the adjunction, is an isomorphism. -/
private theorem isIso_unitDualHom :
    IsIso (unitDualHom (P := normalizedExactPairing k (SimpleClasses.classOf (𝟙_ C)).repr)
      (SimpleClasses.classOfReprIso (𝟙_ C))) := by
  have hr := unitDualHom_comp_retraction
    (P := normalizedExactPairing k (SimpleClasses.classOf (𝟙_ C)).repr)
    (SimpleClasses.classOfReprIso (𝟙_ C))
  have : Mono (unitDualHom (P := normalizedExactPairing k (SimpleClasses.classOf (𝟙_ C)).repr)
      (SimpleClasses.classOfReprIso (𝟙_ C))) := mono_of_mono_fac hr
  exact isIso_of_mono_of_ne_zero fun h ↦ id_ne_zero (𝟙_ C) (by rw [← hr, h, zero_comp])

omit [IsFiniteSemisimpleCategory C] [Fintype (SimpleClasses C)] in
/-- There are no nonzero morphisms from the unit object to the right dual of the representative
of a simple class other than that of the unit. -/
private theorem hom_rightDual_eq_zero {S : SimpleClasses C} (hS : S ≠ SimpleClasses.classOf (𝟙_ C))
    (f : 𝟙_ C ⟶ S.reprᘁ) : f = 0 := by
  have hg (g : S.repr ⟶ 𝟙_ C) : g = 0 := by
    by_contra hg
    have := isIso_of_hom_simple hg
    exact hS (by
      rw [← SimpleClasses.classOf_repr S]
      exact (SimpleClasses.classOf_eq_iff_nonempty_iso _ _).2 ⟨asIso g⟩)
  have h0 : (tensorRightHomEquiv (𝟙_ C) S.repr S.reprᘁ (𝟙_ C)).symm (f ≫ (λ_ _).inv) = 0 := by
    rw [← cancel_epi (λ_ S.repr).inv, comp_zero]
    exact hg _
  have h1 := congrArg (tensorRightHomEquiv (𝟙_ C) S.repr S.reprᘁ (𝟙_ C)) h0
  rw [Equiv.apply_symm_apply] at h1
  simpa [tensorRightHomEquiv] using h1 =≫ (λ_ _).hom

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
    have h0 := hom_rightDual_eq_zero hS (φ.inv ≫ h ≫ S.reprᘁ ◁ φ.hom ≫ (ρ_ _).hom)
    calc
      h = φ.hom ≫ (φ.inv ≫ h ≫ S.reprᘁ ◁ φ.hom ≫ (ρ_ _).hom) ≫ (ρ_ _).inv ≫
          S.reprᘁ ◁ φ.inv := by
        simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id_assoc,
          ← whiskerLeft_comp, Iso.hom_inv_id, whiskerLeft_id, Category.comp_id]
      _ = 0 := by rw [h0, zero_comp, comp_zero]
  rw [inductionβComponent_eq k X _ _ _ (Module.finBasis k _)]
  exact Finset.sum_eq_zero fun i _ ↦ by rw [hzero (Module.finBasis k _ i), map_zero]

omit [Fintype (SimpleClasses C)] in
/-- The isomorphism `𝟙_ C ≅ Rᘁ` given by `unitDualHom`, for `R` the representative of the class
of the unit. -/
private def unitDualIso : 𝟙_ C ≅ (SimpleClasses.classOf (𝟙_ C)).reprᘁ :=
  haveI := isIso_unitDualHom k (C := C)
  asIso (unitDualHom (P := normalizedExactPairing k (SimpleClasses.classOf (𝟙_ C)).repr)
    (SimpleClasses.classOfReprIso (𝟙_ C)))

omit [Fintype (SimpleClasses C)] in
/-- The component of the half-braiding of the induced object at the right dual `Rᘁ` of the
representative `R` of the class of the unit, from the summand of `R` to itself, computed through
the isomorphism `unitDualIso : 𝟙_ C ≅ Rᘁ`. -/
private theorem inductionβComponent_rightDual_unitClass (X : C) :
    inductionβComponent k X ((SimpleClasses.classOf (𝟙_ C)).reprᘁ)
        (SimpleClasses.classOf (𝟙_ C)) (SimpleClasses.classOf (𝟙_ C)) =
      inductionSummand X (SimpleClasses.classOf (𝟙_ C)) ◁ (unitDualIso k).inv ≫
        (ρ_ _).hom ≫ (λ_ _).inv ≫
          (unitDualIso k).hom ▷ inductionSummand X (SimpleClasses.classOf (𝟙_ C)) := by
  rw [← Category.assoc (ρ_ _).hom, ← inductionβComponent_tensorUnit_self k X,
    ← whiskerLeft_comp_inductionβComponent, ← whiskerLeft_comp_assoc, Iso.inv_hom_id,
    whiskerLeft_id, Category.id_comp]

/-- Morphisms of the centre into an induced object agree once their underlying morphisms agree
after the projection onto the summand of the class of the unit. This is the uniqueness half of
the right adjunction `forgetInductionAdjunction`, whose counit factors through that projection. -/
private theorem induction_hom_ext {W : Center C} {X : C} {f g : W ⟶ (induction k C).obj X}
    (h : f.f ≫ biproduct.π (inductionSummand X) (SimpleClasses.classOf (𝟙_ C)) =
      g.f ≫ biproduct.π (inductionSummand X) (SimpleClasses.classOf (𝟙_ C))) : f = g := by
  -- The end projection at the unit factors through the projection onto the unit summand.
  obtain ⟨r, hr⟩ : ∃ r, inductionEndπ X (𝟙_ C) =
      biproduct.π (inductionSummand X) (SimpleClasses.classOf (𝟙_ C)) ≫ r := by
    have hd := inductionEndπ_dinatural k X (SimpleClasses.classOfReprIso (𝟙_ C)).inv
    rw [inductionEndπ_repr k] at hd
    have e : inductionEndπ X (𝟙_ C) = (inductionEndπ X (𝟙_ C) ≫
        (SimpleClasses.classOfReprIso (𝟙_ C)).inv ▷ _) ≫
          (SimpleClasses.classOfReprIso (𝟙_ C)).hom ▷ _ := by
      rw [Category.assoc, ← comp_whiskerRight, Iso.inv_hom_id, id_whiskerRight, Category.comp_id]
    rw [hd, Category.assoc] at e
    exact ⟨_, e⟩
  have key : f.f ≫ inductionEndπ X (𝟙_ C) = g.f ≫ inductionEndπ X (𝟙_ C) := by
    rw [hr]
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ r) h).trans (Category.assoc _ _ _))
  apply ((forgetInductionAdjunction k C).homEquiv W X).symm.injective
  simp only [Adjunction.homEquiv_counit, forgetInductionAdjunction_counit_app k, forget_map]
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) key).trans (Category.assoc _ _ _))

/-- **Left triangle identity**, after the projection onto the summand of the class of the unit. -/
private theorem inductionMap_unitF_comp_counitF_comp_π (X : C) :
    inductionMap (unitF k X) ≫ counitF k (inductionHalfBraiding k X) ≫
        biproduct.π (inductionSummand X) (SimpleClasses.classOf (𝟙_ C)) =
      biproduct.π (inductionSummand X) (SimpleClasses.classOf (𝟙_ C)) := by
  refine biproduct.hom_ext' _ _ fun S ↦ ?_
  rw [biproduct.ι_map_assoc, counitF, biproduct.ι_desc_assoc, counitSummand,
    inductionHalfBraiding_β_hom]
  simp only [Category.assoc]
  rw [← leftUnitor_naturality, ← whisker_exchange_assoc, ← associator_inv_naturality_right_assoc,
    ← whiskerLeft_comp_assoc, ← whiskerLeft_comp_assoc, unitF, comp_whiskerRight]
  simp only [Category.assoc]
  rw [ι_whiskerRight_inductionβHom_whiskerLeft_π]
  by_cases hS : S = SimpleClasses.classOf (𝟙_ C)
  · subst hS
    have := isIso_unitDualHom k (C := C)
    rw [biproduct.ι_π_self, inductionβComponent_rightDual_unitClass k X]
    simp only [unitDualIso, asIso_hom, asIso_inv]
    set R := (SimpleClasses.classOf (𝟙_ C)).repr
    set φ := SimpleClasses.classOfReprIso (𝟙_ C)
    set ζ := unitDualHom (P := normalizedExactPairing k R) φ
    let := normalizedExactPairing k R
    calc
      _ = 𝟙 _ ⊗≫ R ◁ (unitIncl φ X ▷ Rᘁ ≫ (R ⊗ X ⊗ Rᘁ) ◁ inv ζ) ⊗≫
            (R ◁ ζ ≫ ε_ (Rᘁ : C) R) ▷ (R ⊗ X ⊗ Rᘁ) ⊗≫ 𝟙 _ := by
        simp only [whiskerLeft_comp, comp_whiskerRight]
        monoidal
      _ = 𝟙 _ ⊗≫ R ◁ (X ◁ inv ζ ≫ unitIncl φ X ▷ 𝟙_ C) ⊗≫
            ((ρ_ R).hom ≫ φ.hom) ▷ (R ⊗ X ⊗ Rᘁ) ⊗≫ 𝟙 _ := by
        rw [← whisker_exchange, whiskerLeft_unitDualHom_comp_evaluation]
      _ = 𝟙 _ ⊗≫ R ◁ X ◁ inv ζ ⊗≫ (R ◁ unitIncl φ X ≫ φ.hom ▷ (R ⊗ X ⊗ Rᘁ)) ⊗≫ 𝟙 _ := by
        simp only [whiskerLeft_comp, comp_whiskerRight]
        monoidal
      _ = 𝟙 _ ⊗≫ R ◁ X ◁ inv ζ ⊗≫ (φ.hom ▷ X ≫ 𝟙_ C ◁ unitIncl φ X) ⊗≫ 𝟙 _ := by
        rw [whisker_exchange]
      _ = 𝟙 _ ⊗≫ (R ⊗ X) ◁ inv ζ ⊗≫ (φ.hom ≫ φ.inv) ▷ X ⊗≫ (R ⊗ X) ◁ ζ ⊗≫ 𝟙 _ := by
        simp only [unitIncl, whiskerLeft_comp, comp_whiskerRight]
        monoidal
      _ = 𝟙 _ ⊗≫ (R ⊗ X) ◁ (inv ζ ≫ ζ) ⊗≫ 𝟙 _ := by
        rw [Iso.hom_inv_id, id_whiskerRight]
        monoidal
      _ = _ := by
        rw [IsIso.inv_hom_id, whiskerLeft_id]
        monoidal
  · rw [inductionβComponent_rightDual_of_ne k X hS, comp_zero,
      MonoidalPreadditive.whiskerLeft_zero, zero_comp, biproduct.ι_π_ne _ hS]

/-- **Right triangle identity**: the unit followed by the counit is the identity. -/
private theorem unitF_comp_counitF {A : C} (b : HalfBraiding A) :
    unitF k A ≫ counitF k b = 𝟙 A := by
  rw [unitF, Category.assoc, counitF, biproduct.ι_desc, counitSummand]
  exact unitIncl_comp_contract (P := normalizedExactPairing k (SimpleClasses.classOf (𝟙_ C)).repr)
    (SimpleClasses.classOfReprIso (𝟙_ C)) b

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
  Adjunction.mkOfUnitCounit
    { unit :=
        { app X := unitF k X
          naturality _ _ f := unitF_naturality k f }
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
        exact (congrArg (unitF k Z.1 ≫ ·) (Category.id_comp (counitF k Z.2))).trans
          (unitF_comp_counitF k Z.2) }

/-- `Center.induction k C` is a left adjoint (in particular, it preserves all colimits that exist
in `C`). -/
instance instIsLeftAdjointInduction : (induction k C).IsLeftAdjoint :=
  (inductionForgetAdjunction k C).isLeftAdjoint

variable {C}

/-- The unit of `inductionForgetAdjunction` at `X` includes `X` into the summand of the class `R` of
the unit object, through `R ≅ 𝟙_ C` and the coevaluation of the normalized pairing of `Rᘁ` and
`R`. -/
theorem inductionForgetAdjunction_unit_app (X : C) :
    (inductionForgetAdjunction k C).unit.app X =
      (λ_ X).inv ≫ (SimpleClasses.classOfReprIso (𝟙_ C)).inv ▷ X ≫ (ρ_ _).inv ≫
        ((SimpleClasses.classOf (𝟙_ C)).repr ⊗ X) ◁
          (@ExactPairing.coevaluation C _ _ _ _
              (normalizedExactPairing k (SimpleClasses.classOf (𝟙_ C)).repr) ≫
            (SimpleClasses.classOf (𝟙_ C)).reprᘁ ◁ (SimpleClasses.classOfReprIso (𝟙_ C)).hom ≫
              (ρ_ _).hom) ≫
          (α_ _ _ _).hom ≫ biproduct.ι (inductionSummand X) (SimpleClasses.classOf (𝟙_ C)) := by
  simp only [inductionForgetAdjunction, Adjunction.mkOfUnitCounit_unit, unitF, unitIncl,
    unitDualHom, Category.assoc]
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
