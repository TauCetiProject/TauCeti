/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Monoidal.Pivotal.GlobalDim
public import TauCeti.CategoryTheory.Monoidal.Rigid.Preadditive
public import TauCeti.CategoryTheory.Monoidal.Rigid.Simple
public import TauCeti.CategoryTheory.Semisimple.Basic
public import TauCeti.CategoryTheory.Semisimple.Rigid

/-!
# Squared norms of objects, without a pivotal structure

In a right rigid monoidal category a morphism `b : X ⟶ Xᘁᘁ` can be closed up into a loop with the
coevaluation of `X` and the evaluation of `Xᘁ`, giving the scalar

`doubleDualTrace b = η_ X Xᘁ ≫ b ▷ Xᘁ ≫ ε_ Xᘁ Xᘁᘁ : 𝟙_ C ⟶ 𝟙_ C`.

When `b` is the component `φ_X` of a pivotal structure this is the right dimension of `X`, and the
left dimension of `X` is `doubleDualTrace (φ_X⁻¹)ᘁ`. For an arbitrary isomorphism
`a : X ≅ Xᘁᘁ`, Etingof, Nikshych and Ostrik define the *squared norm*

`squaredNorm a = doubleDualTrace a.hom ≫ doubleDualTrace (a.inv)ᘁ`,

which needs no pivotal structure. If the endomorphisms of `X` are the scalars of a commutative
ring `R`, in the sense that `algebraMap R (End X)` is surjective, then any two isomorphisms
`X ≅ Xᘁᘁ` differ by a scalar `r` with inverse `s`, the two factors scale by `r` and `s`, and the
squared norm does not depend on the isomorphism. For an object with more endomorphisms it does
depend on `a`: for `X = k²` in finite-dimensional vector spaces, the canonical isomorphism
`X ≅ Xᘁᘁ` gives `2 · 2 = 4`, and its composite with `diag(1, 2)` gives `3 · 3/2 = 9/2`. For the
component `φ_X` of a pivotal structure the squared norm is `leftDim X ≫ rightDim X`, so for an
object with scalar endomorphisms this product is the same for every pivotal structure.

In a finite semisimple category with simple unit over an algebraically closed field, both
factors of the squared norm of a simple object `X` with finite-dimensional endomorphisms are
invertible: the coevaluation of `X` is a split monomorphism, and Schur's lemma makes every
retraction a scalar multiple of the evaluation `b ▷ Xᘁ ≫ ε_ Xᘁ Xᘁᘁ` of the exact pairing
transported along `b`. So the squared norm of a simple object is invertible.

Since every isomorphism `X ≅ Xᘁᘁ` of a simple object is a nonzero multiple of a given one, and
`doubleDualTrace a.invᘁ` scales inversely to `a`, there is exactly one isomorphism with
`doubleDualTrace a.invᘁ = 𝟙 (𝟙_ C)`: the *normalized* one. Transporting the pairing of `Xᘁ` with
`Xᘁᘁ` along it exhibits `X` as a right dual of `Xᘁ` whose evaluation, closed up with the
coevaluation of `X`, is the squared norm. Normalized evaluations are the weights of the counit of
the left adjunction for induction into the Drinfeld centre.

Summed over the representatives of the simple classes, the squared norms give the global dimension
`normGlobalDim C a = ∑ S, squaredNorm (a S)` with no pivotal structure chosen, only a family of
isomorphisms `a S : S ≅ Sᘁᘁ`; such families exist in a finite semisimple rigid category with
simple unit by `TauCeti.nonempty_iso_rightDual_rightDual`. Over an algebraically closed field,
with finite-dimensional endomorphisms of simple objects, it does not depend on the family, and it
is the global dimension `TauCeti.globalDim C` of every pivotal structure on `C`.

## Main declarations

* `TauCeti.doubleDualTrace`: the trace of a morphism `X ⟶ Xᘁᘁ`, additive and `R`-linear, and
  cyclic by `TauCeti.doubleDualTrace_comm`;
* `TauCeti.squaredNorm`: the squared norm of `X` with respect to `a : X ≅ Xᘁᘁ`;
* `TauCeti.squaredNorm_congr`: the squared norm of an object whose endomorphisms are scalars
  does not depend on the isomorphism;
* `TauCeti.rightTrace_eq_doubleDualTrace`, `TauCeti.leftTrace_eq_doubleDualTrace` and
  `TauCeti.squaredNorm_pivotalIsoApp`: comparison with the traces and dimensions of a pivotal
  structure;
* `TauCeti.isIso_doubleDualTrace`, `TauCeti.isIso_doubleDualTrace_rightAdjointMate` and
  `TauCeti.squaredNorm_ne_zero`: nonvanishing for simple objects, from Schur's lemma for an
  exact pairing with a member with scalar endomorphisms
  (`TauCeti.comp_evaluation_ne_zero_of_surjective_right` and
  `TauCeti.comp_evaluation_ne_zero_of_surjective_left`);
* `TauCeti.normalizedDoubleDualIso` and `TauCeti.normalizedExactPairing`: for a simple object
  `X`, the isomorphism `a : X ≅ Xᘁᘁ` normalized by `doubleDualTrace a.invᘁ = 𝟙 (𝟙_ C)`, unique by
  `TauCeti.eq_normalizedDoubleDualIso`, and the
  pairing of `Xᘁ` and `X` transported along it (`TauCeti.normalizedExactPairing_evaluation` and
  `TauCeti.normalizedExactPairing_coevaluation`), whose two closed loops are `𝟙 (𝟙_ C)` and the
  squared norm of `X`;
* `TauCeti.normGlobalDim`: the global dimension as a sum of squared norms, independent of the
  isomorphisms by `TauCeti.normGlobalDim_congr` and equal to the pivotal global dimension by
  `TauCeti.normGlobalDim_eq_globalDim`.

## References

* P. Etingof, D. Nikshych, V. Ostrik, *On fusion categories*, Ann. of Math. **162** (2005),
  [arXiv:math/0203060](https://arxiv.org/abs/math/0203060), Proposition 2.1 and Definition 2.2
* [P. Etingof, S. Gelaki, D. Nikshych, V. Ostrik, *Tensor categories*][egno15], §7.21
-/

public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe w v u

namespace TauCeti

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

section RightRigid

variable [RightRigidCategory C]

/-- The *trace* `η_ X Xᘁ ≫ b ▷ Xᘁ ≫ ε_ Xᘁ Xᘁᘁ` of a morphism `b : X ⟶ Xᘁᘁ` in a right rigid
monoidal category, closed up with the coevaluation of `X` and the evaluation of `Xᘁ`. -/
noncomputable def doubleDualTrace {X : C} (b : X ⟶ (Xᘁ : C)ᘁ) : 𝟙_ C ⟶ 𝟙_ C :=
  η_ X (Xᘁ : C) ≫ b ▷ (Xᘁ : C) ≫ ε_ (Xᘁ : C) ((Xᘁ : C)ᘁ : C)

/-- The defining formula of `TauCeti.doubleDualTrace`. -/
theorem doubleDualTrace_def {X : C} (b : X ⟶ (Xᘁ : C)ᘁ) :
    doubleDualTrace b = η_ X (Xᘁ : C) ≫ b ▷ (Xᘁ : C) ≫ ε_ (Xᘁ : C) ((Xᘁ : C)ᘁ : C) :=
  (rfl)

/-- **Cyclicity**: for `f : X ⟶ Y` and `b : Y ⟶ Xᘁᘁ`, the trace of `f ≫ b` is the trace of
`b ≫ fᘁᘁ`. -/
theorem doubleDualTrace_comm {X Y : C} (f : X ⟶ Y) (b : Y ⟶ (Xᘁ : C)ᘁ) :
    doubleDualTrace (f ≫ b) = doubleDualTrace (b ≫ (fᘁ)ᘁ) := by
  rw [doubleDualTrace_def, doubleDualTrace_def, comp_whiskerRight, comp_whiskerRight,
    Category.assoc, Category.assoc]
  -- Slide `f` around the loop: at the coevaluation `f ▷ Xᘁ` becomes `Y ◁ fᘁ`, which passes `b`
  -- and reaches the evaluation of `Xᘁ` as `fᘁᘁ ▷ Yᘁ`.
  rw [← coevaluation_comp_rightAdjointMate_assoc, whisker_exchange_assoc,
    ← rightAdjointMate_comp_evaluation]

/-- The trace of the right adjoint mate of `b : Xᘁᘁ ⟶ X` closes `b` up with the coevaluation of
`Xᘁ` and the evaluation of `X`. -/
theorem doubleDualTrace_rightAdjointMate {X : C} (b : (Xᘁ : C)ᘁ ⟶ X) :
    doubleDualTrace (bᘁ) =
      η_ (Xᘁ : C) ((Xᘁ : C)ᘁ : C) ≫ (Xᘁ : C) ◁ b ≫ ε_ X (Xᘁ : C) := by
  rw [doubleDualTrace_def, rightAdjointMate_comp_evaluation]

/-- The trace of zero is zero. -/
@[simp]
theorem doubleDualTrace_zero [HasZeroMorphisms C] (X : C) :
    doubleDualTrace (0 : X ⟶ (Xᘁ : C)ᘁ) = 0 := by
  simp [doubleDualTrace_def]

section Linear

variable [Preadditive C] [MonoidalPreadditive C]

/-- The trace is additive. -/
@[simp]
theorem doubleDualTrace_add {X : C} (b c : X ⟶ (Xᘁ : C)ᘁ) :
    doubleDualTrace (b + c) = doubleDualTrace b + doubleDualTrace c := by
  simp [doubleDualTrace_def]

/-- The trace commutes with finite sums. -/
@[simp]
theorem doubleDualTrace_sum {ι : Type*} {X : C} (s : Finset ι) (b : ι → (X ⟶ (Xᘁ : C)ᘁ)) :
    doubleDualTrace (∑ i ∈ s, b i) = ∑ i ∈ s, doubleDualTrace (b i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => simp [hi, ih]

/-- The trace commutes with negation. -/
@[simp]
theorem doubleDualTrace_neg {X : C} (b : X ⟶ (Xᘁ : C)ᘁ) :
    doubleDualTrace (-b) = -doubleDualTrace b :=
  eq_neg_of_add_eq_zero_left (by rw [← doubleDualTrace_add, neg_add_cancel, doubleDualTrace_zero])

/-- The trace commutes with subtraction. -/
@[simp]
theorem doubleDualTrace_sub {X : C} (b c : X ⟶ (Xᘁ : C)ᘁ) :
    doubleDualTrace (b - c) = doubleDualTrace b - doubleDualTrace c := by
  rw [sub_eq_add_neg, doubleDualTrace_add, doubleDualTrace_neg, sub_eq_add_neg]

/-- The trace is `R`-linear in an `R`-linear monoidal category. -/
@[simp]
theorem doubleDualTrace_smul {R : Type*} [Semiring R] [Linear R C] [MonoidalLinear R C] {X : C}
    (r : R) (b : X ⟶ (Xᘁ : C)ᘁ) : doubleDualTrace (r • b) = r • doubleDualTrace b := by
  simp [doubleDualTrace_def]

end Linear

/-- The *squared norm* `Tr(a) · Tr((a⁻¹)ᘁ)` of an object `X` with respect to an isomorphism
`a : X ≅ Xᘁᘁ` (Etingof–Nikshych–Ostrik, *On fusion categories*, Definition 2.2). For a pivotal
isomorphism it is `leftDim X ≫ rightDim X` (`TauCeti.squaredNorm_pivotalIsoApp`), and when the
endomorphisms of `X` are scalars it does not depend on `a` (`TauCeti.squaredNorm_congr`). -/
noncomputable def squaredNorm {X : C} (a : X ≅ (Xᘁ : C)ᘁ) : 𝟙_ C ⟶ 𝟙_ C :=
  doubleDualTrace a.hom ≫ doubleDualTrace (a.invᘁ)

/-- The defining formula of `TauCeti.squaredNorm`. -/
theorem squaredNorm_def {X : C} (a : X ≅ (Xᘁ : C)ᘁ) :
    squaredNorm a = doubleDualTrace a.hom ≫ doubleDualTrace (a.invᘁ) :=
  (rfl)

/-- **The squared norm does not depend on the isomorphism** `X ≅ Xᘁᘁ` when every endomorphism
of `X` is a scalar of a commutative ring `R`: two such isomorphisms differ by a scalar `r`, their
inverses by its inverse `s`, and the two factors of the squared norm scale by `r` and `s`. -/
theorem squaredNorm_congr (R : Type w) [CommSemiring R] [Preadditive C] [Linear R C]
    [MonoidalPreadditive C] [MonoidalLinear R C] {X : C}
    (hX : Function.Surjective (algebraMap R (End X))) (a b : X ≅ (Xᘁ : C)ᘁ) :
    squaredNorm a = squaredNorm b := by
  have hscalar (f : X ⟶ X) : ∃ r : R, f = r • 𝟙 X := by
    obtain ⟨r, hr⟩ := hX (End.of f)
    refine ⟨r, ?_⟩
    simpa [End.algebraMap_asHom] using (congrArg End.asHom hr).symm
  obtain ⟨r, hr⟩ := hscalar (b.hom ≫ a.inv)
  obtain ⟨s, hs⟩ := hscalar (a.hom ≫ b.inv)
  have hb : b.hom = r • a.hom := by
    rw [← Category.comp_id b.hom, ← a.inv_hom_id, ← Category.assoc, hr, Linear.smul_comp,
      Category.id_comp]
  have hb' : b.inv = s • a.inv := by
    rw [← Category.id_comp b.inv, ← a.inv_hom_id, Category.assoc, hs, Linear.comp_smul,
      Category.comp_id]
  -- The scalars `r` and `s` are inverse to each other on `X`, so `(r * s) • a.hom = a.hom`.
  have hrs : (r * s) • a.hom = a.hom := by
    have h : (r • 𝟙 X) ≫ (s • 𝟙 X) = 𝟙 X := by
      rw [← hr, ← hs, Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id]
    rw [Linear.smul_comp, Linear.comp_smul, Category.id_comp, smul_smul] at h
    rw [← Category.id_comp a.hom, ← Linear.smul_comp, h]
  -- Pull both scalars out of the squared norm of `b`, then absorb their product into `a.hom`.
  rw [squaredNorm_def, squaredNorm_def, hb, hb']
  simp only [rightAdjointMate_smul, doubleDualTrace_smul, Linear.comp_smul, Linear.smul_comp,
    smul_smul]
  rw [← Linear.smul_comp, ← doubleDualTrace_smul, mul_comm, hrs]

end RightRigid

section Pivotal

variable [RigidCategory C] [PivotalCategory C]

/-- The right trace of `f : X ⟶ X` is the trace of `f` followed by the pivotal isomorphism. -/
theorem rightTrace_eq_doubleDualTrace {X : C} (f : X ⟶ X) :
    rightTrace f = doubleDualTrace (f ≫ (pivotalIsoApp X).hom) := by
  rw [rightTrace_eq_pivotalIsoApp, doubleDualTrace_def, comp_whiskerRight, Category.assoc]

/-- The left trace of `f : X ⟶ X` is the trace of the right adjoint mate of the inverse pivotal
isomorphism followed by `f`. -/
theorem leftTrace_eq_doubleDualTrace {X : C} (f : X ⟶ X) :
    leftTrace f = doubleDualTrace (((pivotalIsoApp X).inv ≫ f)ᘁ) := by
  rw [leftTrace_eq_pivotalIsoApp, doubleDualTrace_rightAdjointMate,
    MonoidalCategory.whiskerLeft_comp, Category.assoc]

/-- The trace of the pivotal isomorphism `φ_X` is the right dimension of `X`. -/
@[simp]
theorem doubleDualTrace_pivotalIsoApp_hom (X : C) :
    doubleDualTrace (pivotalIsoApp X).hom = rightDim X := by
  rw [← rightTrace_id, rightTrace_eq_doubleDualTrace, Category.id_comp]

/-- The trace of the right adjoint mate of `φ_X⁻¹` is the left dimension of `X`. -/
@[simp]
theorem doubleDualTrace_rightAdjointMate_pivotalIsoApp_inv (X : C) :
    doubleDualTrace ((pivotalIsoApp X).invᘁ) = leftDim X := by
  rw [← leftTrace_id, leftTrace_eq_doubleDualTrace, Category.comp_id]

/-- **Comparison with a pivotal structure**: the squared norm of `X` with respect to the pivotal
isomorphism `φ_X` is `leftDim X ≫ rightDim X`. -/
@[simp]
theorem squaredNorm_pivotalIsoApp (X : C) :
    squaredNorm (pivotalIsoApp X) = leftDim X ≫ rightDim X := by
  rw [squaredNorm_def, doubleDualTrace_pivotalIsoApp_hom,
    doubleDualTrace_rightAdjointMate_pivotalIsoApp_inv, scalar_comm]

end Pivotal

section Simple

variable (k : Type*) [Field k] [IsAlgClosed k]
variable [Abelian C] [MonoidalPreadditive C] [Linear k C] [MonoidalLinear k C]
  [IsFiniteSemisimpleCategory C] [Simple (𝟙_ C)]
variable {X : C} [Simple X] [FiniteDimensional k (X ⟶ X)]

include k in
/-- In a finite semisimple category with simple unit over an algebraically closed field, the
trace of an isomorphism `b : X ⟶ Xᘁᘁ` out of a simple object with finite-dimensional
endomorphisms is invertible. -/
theorem isIso_doubleDualTrace [RightRigidCategory C] (b : X ⟶ (Xᘁ : C)ᘁ) [IsIso b] :
    IsIso (doubleDualTrace b) := by
  -- `X` is a right dual of `Xᘁ` through `b`, with evaluation `b ▷ Xᘁ ≫ ε_ Xᘁ Xᘁᘁ`.
  let := exactPairingCongrRight (X := (Xᘁ : C)) (asIso b)
  have := isIso_of_hom_simple <| comp_evaluation_ne_zero_of_surjective_right (X := (Xᘁ : C))
    (bijective_algebraMap_end_of_simple k X).2
    (coevaluation_ne_zero (Y := (Xᘁ : C)) (Simple.not_isZero X))
  rwa [exactPairingCongrRight_evaluation, asIso_hom, ← doubleDualTrace_def] at this

include k in
/-- In a finite semisimple category with simple unit over an algebraically closed field, the
trace of the right adjoint mate of an isomorphism `b : Xᘁᘁ ⟶ X` into a simple object with
finite-dimensional endomorphisms is invertible. -/
theorem isIso_doubleDualTrace_rightAdjointMate [RigidCategory C] (b : (Xᘁ : C)ᘁ ⟶ X) [IsIso b] :
    IsIso (doubleDualTrace (bᘁ)) := by
  -- `X` is a right dual of `Xᘁ` through `b⁻¹`, with coevaluation `η_ Xᘁ Xᘁᘁ ≫ Xᘁ ◁ b`.
  let := exactPairingCongrRight (X := (Xᘁ : C)) (asIso b).symm
  have := isIso_of_hom_simple <| comp_evaluation_ne_zero_of_surjective_left (X := X)
    (Y := (Xᘁ : C)) (bijective_algebraMap_end_of_simple k X).2
    (coevaluation_ne_zero (Y := X) (Simple.not_isZero (Xᘁ : C)))
  rwa [exactPairingCongrRight_coevaluation, Iso.symm_inv, asIso_hom, Category.assoc,
    ← doubleDualTrace_rightAdjointMate] at this

include k in
/-- In a finite semisimple category with simple unit over an algebraically closed field, the
squared norm of a simple object with finite-dimensional endomorphisms is invertible. -/
theorem isIso_squaredNorm [RigidCategory C] (a : X ≅ (Xᘁ : C)ᘁ) : IsIso (squaredNorm a) := by
  have := isIso_doubleDualTrace k a.hom
  have := isIso_doubleDualTrace_rightAdjointMate k a.inv
  rw [squaredNorm_def]
  infer_instance

include k in
/-- In a finite semisimple category with simple unit over an algebraically closed field, the
squared norm of a simple object with finite-dimensional endomorphisms is nonzero. -/
theorem squaredNorm_ne_zero [RigidCategory C] (a : X ≅ (Xᘁ : C)ᘁ) : squaredNorm a ≠ 0 :=
  (isIso_iff_ne_zero _).mp (isIso_squaredNorm k a)

end Simple

section Normalized

variable (k : Type*) [Field k] [IsAlgClosed k]
variable [Abelian C] [MonoidalPreadditive C] [Linear k C] [MonoidalLinear k C] [RigidCategory C]
  [IsFiniteSemisimpleCategory C] [Simple (𝟙_ C)] [FiniteDimensional k (𝟙_ C ⟶ 𝟙_ C)]

include k in
private theorem exists_iso_doubleDualTrace_rightAdjointMate_inv_eq_id (X : C) [Simple X]
    [FiniteDimensional k (X ⟶ X)] :
    ∃ a : X ≅ (Xᘁ : C)ᘁ, doubleDualTrace (a.invᘁ) = 𝟙 (𝟙_ C) := by
  obtain ⟨a⟩ := nonempty_iso_rightDual_rightDual X
  have hiso := isIso_doubleDualTrace_rightAdjointMate k a.inv
  obtain ⟨γ, hγ⟩ := endomorphism_simple_eq_smul_id k (doubleDualTrace (a.invᘁ))
  have hγ0 : γ ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hγ
    exact (isIso_iff_ne_zero _).mp hiso hγ.symm
  -- Rescale `a` so that the trace of the mate of its inverse becomes one.
  refine ⟨{ hom := γ • a.hom
            inv := γ⁻¹ • a.inv
            hom_inv_id := by simp [smul_smul, hγ0]
            inv_hom_id := by simp [smul_smul, hγ0] }, ?_⟩
  simp [rightAdjointMate_smul, ← hγ, smul_smul, hγ0]

/-- The **normalized isomorphism** `X ≅ Xᘁᘁ` of a simple object `X`: the trace
`doubleDualTrace a.invᘁ` of the right adjoint mate of its inverse is `𝟙 (𝟙_ C)`
(`TauCeti.doubleDualTrace_rightAdjointMate_normalizedDoubleDualIso_inv`). Any isomorphism
`X ≅ Xᘁᘁ` is a scalar multiple of it, and rescaling it changes this trace, so the normalization
pins it down. -/
noncomputable def normalizedDoubleDualIso (X : C) [Simple X] [FiniteDimensional k (X ⟶ X)] :
    X ≅ (Xᘁ : C)ᘁ :=
  (exists_iso_doubleDualTrace_rightAdjointMate_inv_eq_id k X).choose

/-- The trace of the right adjoint mate of the inverse of the normalized isomorphism `X ≅ Xᘁᘁ` is
the identity of the unit. -/
@[simp]
theorem doubleDualTrace_rightAdjointMate_normalizedDoubleDualIso_inv (X : C) [Simple X]
    [FiniteDimensional k (X ⟶ X)] :
    doubleDualTrace ((normalizedDoubleDualIso k X).invᘁ) = 𝟙 (𝟙_ C) :=
  (exists_iso_doubleDualTrace_rightAdjointMate_inv_eq_id k X).choose_spec

/-- **Uniqueness of the normalized isomorphism**: an isomorphism `a : X ≅ Xᘁᘁ` of a simple object
with `doubleDualTrace a.invᘁ = 𝟙 (𝟙_ C)` is `TauCeti.normalizedDoubleDualIso k X`. -/
theorem eq_normalizedDoubleDualIso {X : C} [Simple X] [FiniteDimensional k (X ⟶ X)]
    (a : X ≅ (Xᘁ : C)ᘁ) (ha : doubleDualTrace (a.invᘁ) = 𝟙 (𝟙_ C)) :
    a = normalizedDoubleDualIso k X := by
  obtain ⟨s, hs⟩ := endomorphism_simple_eq_smul_id k ((normalizedDoubleDualIso k X).hom ≫ a.inv)
  have hinv : a.inv = s • (normalizedDoubleDualIso k X).inv := by
    rw [← Category.id_comp a.inv, ← (normalizedDoubleDualIso k X).inv_hom_id, Category.assoc, ← hs,
      Linear.comp_smul, Category.comp_id]
  rw [hinv, rightAdjointMate_smul, doubleDualTrace_smul,
    doubleDualTrace_rightAdjointMate_normalizedDoubleDualIso_inv] at ha
  rw [smul_left_injective k (id_ne_zero (𝟙_ C)) (ha.trans (one_smul k _).symm), one_smul] at hinv
  exact Iso.ext ((Iso.inv_eq_inv _ _).mp hinv)

/-- The **normalized exact pairing** of `Xᘁ` and a simple object `X`: the pairing of `Xᘁ` with its
right dual `Xᘁᘁ`, transported along `TauCeti.normalizedDoubleDualIso k X`. Closing up its
coevaluation with the evaluation of `X` gives `𝟙 (𝟙_ C)`
(`TauCeti.normalizedExactPairing_coevaluation_comp_evaluation`). -/
@[instance_reducible]
noncomputable def normalizedExactPairing (X : C) [Simple X] [FiniteDimensional k (X ⟶ X)] :
    ExactPairing Xᘁ X :=
  exactPairingCongrRight (normalizedDoubleDualIso k X)

/-- The evaluation `X ⊗ Xᘁ ⟶ 𝟙_ C` of `TauCeti.normalizedExactPairing k X`. -/
@[reassoc]
theorem normalizedExactPairing_evaluation (X : C) [Simple X] [FiniteDimensional k (X ⟶ X)] :
    @ExactPairing.evaluation C _ _ Xᘁ X (normalizedExactPairing k X) =
      (normalizedDoubleDualIso k X).hom ▷ Xᘁ ≫ ε_ (Xᘁ : C) ((Xᘁ : C)ᘁ : C) :=
  exactPairingCongrRight_evaluation _

/-- The coevaluation `𝟙_ C ⟶ Xᘁ ⊗ X` of `TauCeti.normalizedExactPairing k X`. -/
@[reassoc]
theorem normalizedExactPairing_coevaluation (X : C) [Simple X] [FiniteDimensional k (X ⟶ X)] :
    @ExactPairing.coevaluation C _ _ Xᘁ X (normalizedExactPairing k X) =
      η_ (Xᘁ : C) ((Xᘁ : C)ᘁ : C) ≫ Xᘁ ◁ (normalizedDoubleDualIso k X).inv :=
  exactPairingCongrRight_coevaluation _

/-- Closing up the coevaluation of `TauCeti.normalizedExactPairing k X` with the evaluation of
`X` gives the identity of the unit. -/
@[simp]
theorem normalizedExactPairing_coevaluation_comp_evaluation (X : C) [Simple X]
    [FiniteDimensional k (X ⟶ X)] :
    @ExactPairing.coevaluation C _ _ Xᘁ X (normalizedExactPairing k X) ≫ ε_ X Xᘁ = 𝟙 (𝟙_ C) := by
  rw [normalizedExactPairing_coevaluation, Category.assoc,
    ← doubleDualTrace_rightAdjointMate,
    doubleDualTrace_rightAdjointMate_normalizedDoubleDualIso_inv]

/-- Closing up the coevaluation of `X` with the evaluation of `TauCeti.normalizedExactPairing k X`
gives the squared norm of `X`. -/
@[simp]
theorem coevaluation_comp_normalizedExactPairing_evaluation (X : C) [Simple X]
    [FiniteDimensional k (X ⟶ X)] :
    η_ X Xᘁ ≫ @ExactPairing.evaluation C _ _ Xᘁ X (normalizedExactPairing k X) =
      squaredNorm (normalizedDoubleDualIso k X) := by
  rw [normalizedExactPairing_evaluation, squaredNorm_def,
    doubleDualTrace_rightAdjointMate_normalizedDoubleDualIso_inv, Category.comp_id,
    doubleDualTrace_def]

end Normalized

section GlobalDim

variable (C) [Preadditive C] [Fintype (SimpleClasses C)]

/-- The *global dimension* `∑ S, squaredNorm (a S)` of a right rigid preadditive category with
finitely many simple classes, with respect to a family of isomorphisms `a S : S ≅ Sᘁᘁ` for the
chosen representatives `S` of the simple classes (Etingof–Nikshych–Ostrik, *On fusion
categories*, Definition 2.2). Under the hypotheses of `TauCeti.normGlobalDim_congr` it does not
depend on `a`, and it is the global dimension of every pivotal structure
(`TauCeti.normGlobalDim_eq_globalDim`). -/
noncomputable def normGlobalDim [RightRigidCategory C]
    (a : ∀ S : SimpleClasses C, S.repr ≅ ((S.repr)ᘁ : C)ᘁ) : 𝟙_ C ⟶ 𝟙_ C :=
  ∑ S : SimpleClasses C, squaredNorm (a S)

/-- The defining formula of `TauCeti.normGlobalDim`. -/
theorem normGlobalDim_def [RightRigidCategory C]
    (a : ∀ S : SimpleClasses C, S.repr ≅ ((S.repr)ᘁ : C)ᘁ) :
    normGlobalDim C a = ∑ S : SimpleClasses C, squaredNorm (a S) :=
  (rfl)

variable (k : Type*) [Field k] [IsAlgClosed k] [MonoidalPreadditive C] [Linear k C]
  [MonoidalLinear k C] [HasKernels C] [∀ S : SimpleClasses C, FiniteDimensional k (S.repr ⟶ S.repr)]

include k in
/-- **The global dimension does not depend on the isomorphisms** `S ≅ Sᘁᘁ`, over an algebraically
closed field when the endomorphisms of each simple object are finite-dimensional. -/
theorem normGlobalDim_congr [RightRigidCategory C]
    (a b : ∀ S : SimpleClasses C, S.repr ≅ ((S.repr)ᘁ : C)ᘁ) :
    normGlobalDim C a = normGlobalDim C b :=
  Finset.sum_congr rfl fun S _ ↦
    squaredNorm_congr k (bijective_algebraMap_end_of_simple k S.repr).2 (a S) (b S)

include k in
/-- **Comparison with the pivotal global dimension**: for every pivotal structure, the global
dimension `∑ S, squaredNorm (a S)` is `TauCeti.globalDim C`, over an algebraically closed field
when the endomorphisms of each simple object are finite-dimensional. -/
theorem normGlobalDim_eq_globalDim [RigidCategory C] [PivotalCategory C]
    (a : ∀ S : SimpleClasses C, S.repr ≅ ((S.repr)ᘁ : C)ᘁ) :
    normGlobalDim C a = globalDim C := by
  rw [normGlobalDim_congr C k a (fun S ↦ pivotalIsoApp S.repr), normGlobalDim_def,
    globalDim_eq_sum_leftDim_comp_rightDim]
  simp only [squaredNorm_pivotalIsoApp]

end GlobalDim

end TauCeti
