/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.PDCode.FoxColoring.Basic
public import TauCeti.KnotTheory.PDCode.Alexander.Equivalence

/-!
# Fox colourings are invariants of Reidemeister equivalence

Let `M` be an abelian group, made a module over `ℤ[T;T⁻¹]` by letting `t` act as `-1`. The
Alexander relations of an oriented PD-code (`TauCeti.OrientedPDCode.alexanderRelation`) have
weight `1` on the over-strand and `t ^ (±1)` on the under-strand, so in `M` they become exactly the
relations of a Fox colouring (`TauCeti.PDCode.foxColorings`). The universal property of the
Alexander module (`TauCeti.OrientedPDCode.alexanderLift`) therefore identifies the Fox colourings
of `D` with values in `M` with the `ℤ[T;T⁻¹]`-linear maps from the Alexander module of `D` to
`M`, by evaluating a linear map on the generators (Crowell–Fox, Chapter VI; Przytycki, §2).

So a linear equivalence of Alexander modules induces one of colouring modules,
`TauCeti.OrientedPDCode.foxColoringsEquivOfAlexanderModuleEquiv`. Since Reidemeister equivalent
codes have linearly equivalent Alexander modules
(`TauCeti.OrientedPDCode.ReidemeisterEquiv.nonempty_alexanderModule_linearEquiv`), their Fox
colouring modules are linearly equivalent over every coefficient ring, and in particular the
number of colourings is an invariant of Reidemeister equivalence.

The `ℤ[T;T⁻¹]`-module structure on `M` is only used inside this file, as a local instance.

## Main definitions

* `TauCeti.OrientedPDCode.foxColoringLift`: the additive lift of a colouring to the Alexander
  module, taking the action of `t` to negation.
* `TauCeti.OrientedPDCode.foxColoringsNegOneHomEquiv`: the universal characterization by
  additive homomorphisms intertwining `t` with negation.
* `TauCeti.OrientedPDCode.foxColoringsEquivOfAlexanderModuleEquiv`: the linear equivalence of
  Fox colouring modules induced by a linear equivalence of Alexander modules.

## Main results

* `TauCeti.OrientedPDCode.ReidemeisterEquiv.nonempty_foxColorings_linearEquiv`: Reidemeister
  equivalent codes have linearly equivalent Fox colouring modules.
* `TauCeti.OrientedPDCode.ReidemeisterEquiv.natCard_foxColorings_eq`: they have the same number of
  Fox colourings.

## References

* R. H. Crowell, R. H. Fox, *Introduction to Knot Theory*, Graduate Texts in Mathematics 57,
  Springer (1977), Chapters VI and VII.
* J. H. Przytycki, *3-coloring and other elementary invariants of knots*, Banach Center
  Publications 42 (1998), 275–295.
-/

public section

noncomputable section

open LaurentPolynomial

namespace TauCeti

namespace OrientedPDCode

variable {n m : ℕ} (R M : Type*) [Semiring R] [AddCommGroup M] [Module R M]

/-- The evaluation of Laurent polynomials at `t = -1`. -/
private def evalNegOne : ℤ[T;T⁻¹] →+* ℤ :=
  LaurentPolynomial.eval₂ (RingHom.id ℤ) (-1)

/-- An abelian group as a module over `ℤ[T;T⁻¹]`, with `t` acting as `-1`. It has low priority, so
that it is never preferred to the module structure of an Alexander module. -/
private abbrev negOneModule : Module ℤ[T;T⁻¹] M :=
  Module.compHom M evalNegOne

attribute [local instance 100] negOneModule

/-- The actions of `ℤ[T;T⁻¹]` and of `R` on `M` commute, since `ℤ[T;T⁻¹]` acts through `ℤ`. This
makes the `ℤ[T;T⁻¹]`-linear maps into `M` an `R`-module. -/
private abbrev smulCommClassNegOne : SMulCommClass ℤ[T;T⁻¹] R M where
  smul_comm a c x := (smul_comm c (evalNegOne a) x).symm

attribute [local instance 100] smulCommClassNegOne

/-- In `M`, a Laurent polynomial acts through its value at `-1`. -/
private theorem smul_eq_evalNegOne_smul (a : ℤ[T;T⁻¹]) (x : M) : a • x = evalNegOne a • x :=
  (rfl)

/-- At `t = -1`, the Alexander weight of a slot is `1` on the over-strand and `-1` on the
under-strand. -/
private theorem evalNegOne_alexanderWeight (D : OrientedPDCode n) (i : Fin n) (slot : Fin 4) :
    evalNegOne (D.alexanderWeight i slot) = if D.isOver i slot then 1 else -1 := by
  have key (k : ℤ) (hk : k = 1 ∨ k = -1) : evalNegOne (T k) = -1 := by
    rcases hk with rfl | rfl <;> simp [evalNegOne, eval₂_T]
  have hsign := D.crossingSign_eq_one_or_neg_one i
  rw [alexanderWeight_def]
  split_ifs
  · exact map_one _
  · exact key _ (by rcases hsign with h | h <;> simp [h])
  · exact key _ hsign

/-- In `M`, the Alexander relation of a slot is the Fox colouring relation of that slot. -/
private theorem alexanderRelation_iff (D : OrientedPDCode n)
    (v : Fin (4 * n) ⊕ Fin D.crossinglessComponentCount → M) (i : Fin n) (slot : Fin 4) :
    v (.inl (D.crossing i (slot + 2))) =
        D.alexanderWeight i slot • v (.inl (D.crossing i slot)) +
          (1 - D.alexanderWeight i slot) • v (.inl (D.crossing i (slot + 1))) ↔
      v (.inl (D.crossing i (slot + 2))) =
        if D.isOver i slot then v (.inl (D.crossing i slot))
        else 2 • v (.inl (D.crossing i (slot + 1))) - v (.inl (D.crossing i slot)) := by
  rw [smul_eq_evalNegOne_smul, smul_eq_evalNegOne_smul, map_sub, map_one,
    evalNegOne_alexanderWeight]
  split_ifs
  · simp
  · rw [show (1 : ℤ) - -1 = (2 : ℕ) by norm_num, natCast_zsmul, neg_one_zsmul, neg_add_eq_sub]

variable {R M}

/-- The linear map out of the Alexander module defined by a Fox colouring. -/
private def toAlexanderHom (D : OrientedPDCode n) (v : D.foxColorings R M) :
    D.AlexanderModule →ₗ[ℤ[T;T⁻¹]] M :=
  D.alexanderLift v.1 (PDCode.apply_edgePair_of_mem_foxColorings v.2)
    fun i slot ↦
      (alexanderRelation_iff M D v.1 i slot).2 ((PDCode.mem_foxColorings_iff.1 v.2).2 i slot)

/-- The linear map defined by a colouring sends each generator to its label. -/
private theorem toAlexanderHom_alexanderGenerator (D : OrientedPDCode n) (v : D.foxColorings R M)
    (g : Fin (4 * n) ⊕ Fin D.crossinglessComponentCount) :
    toAlexanderHom D v (D.alexanderGenerator g) = v.1 g :=
  D.alexanderLift_alexanderGenerator _ _ _ g

/-- The Fox colouring defined by a linear map out of the Alexander module: its values on the
generators. -/
private def ofAlexanderHom (D : OrientedPDCode n) (f : D.AlexanderModule →ₗ[ℤ[T;T⁻¹]] M) :
    D.foxColorings R M :=
  ⟨fun g ↦ f (D.alexanderGenerator g), PDCode.mem_foxColorings_iff.2
    ⟨fun h ↦ by rw [alexanderGenerator_edgePair], fun i slot ↦
      (alexanderRelation_iff M D (fun g ↦ f (D.alexanderGenerator g)) i slot).1 (by
        rw [alexanderGenerator_crossing_add_two, map_add, map_smul, map_smul])⟩⟩

/-- The labels of the colouring defined by a linear map are its values on the generators. -/
private theorem ofAlexanderHom_apply (D : OrientedPDCode n) (f : D.AlexanderModule →ₗ[ℤ[T;T⁻¹]] M)
    (g : Fin (4 * n) ⊕ Fin D.crossinglessComponentCount) :
    (ofAlexanderHom D f : D.foxColorings R M).1 g = f (D.alexanderGenerator g) :=
  (rfl)

/-- A linear map is recovered from its colouring. -/
private theorem toAlexanderHom_ofAlexanderHom (D : OrientedPDCode n)
    (f : D.AlexanderModule →ₗ[ℤ[T;T⁻¹]] M) :
    toAlexanderHom D (ofAlexanderHom D f : D.foxColorings R M) = f :=
  AlexanderModule.hom_ext D fun g ↦ by
    rw [toAlexanderHom_alexanderGenerator, ofAlexanderHom_apply]

variable (R M) in
/-- The Fox colourings of `D` with values in `M` are the `ℤ[T;T⁻¹]`-linear maps from the Alexander
module of `D` into `M`, on which `t` acts as `-1`. -/
private def alexanderHomEquiv (D : OrientedPDCode n) :
    D.foxColorings R M ≃ₗ[R] (D.AlexanderModule →ₗ[ℤ[T;T⁻¹]] M) where
  toFun := toAlexanderHom D
  invFun := ofAlexanderHom D
  map_add' v w := AlexanderModule.hom_ext D fun g ↦ by
    simp [toAlexanderHom_alexanderGenerator]
  map_smul' c v := AlexanderModule.hom_ext D fun g ↦ by
    simp [toAlexanderHom_alexanderGenerator]
  left_inv v := Subtype.ext <| funext fun g ↦ by
    rw [ofAlexanderHom_apply, toAlexanderHom_alexanderGenerator]
  right_inv := toAlexanderHom_ofAlexanderHom D

variable (R M) in
/-- The additive map out of the Alexander module defined by a Fox colouring, with `t` acting
as negation. -/
def foxColoringLift (D : OrientedPDCode n) :
    D.foxColorings R M →ₗ[R] (D.AlexanderModule →+ M) where
  toFun v := (toAlexanderHom D v).toAddMonoidHom
  map_add' v w := AddMonoidHom.ext fun x ↦
    congrArg (fun f : D.AlexanderModule →ₗ[ℤ[T;T⁻¹]] M ↦ f x)
      ((alexanderHomEquiv R M D).map_add v w)
  map_smul' c v := AddMonoidHom.ext fun x ↦
    congrArg (fun f : D.AlexanderModule →ₗ[ℤ[T;T⁻¹]] M ↦ f x)
      ((alexanderHomEquiv R M D).map_smul c v)

/-- The lift takes each Alexander generator to its colour. -/
@[simp]
theorem foxColoringLift_alexanderGenerator (D : OrientedPDCode n) (v : D.foxColorings R M)
    (g : Fin (4 * n) ⊕ Fin D.crossinglessComponentCount) :
    D.foxColoringLift R M v (D.alexanderGenerator g) = v.1 g :=
  toAlexanderHom_alexanderGenerator D v g

/-- The lift intertwines the action of `t` with negation. -/
@[simp]
theorem foxColoringLift_T_smul (D : OrientedPDCode n) (v : D.foxColorings R M)
    (x : D.AlexanderModule) :
    D.foxColoringLift R M v ((T 1 : ℤ[T;T⁻¹]) • x) = -D.foxColoringLift R M v x := by
  -- Work with the linear lift before forgetting its scalar action.
  change toAlexanderHom D v ((T 1 : ℤ[T;T⁻¹]) • x) = -toAlexanderHom D v x
  rw [map_smul, smul_eq_evalNegOne_smul]
  simp [evalNegOne]

/-- An additive map intertwining `t` with negation is linear for the specialization at `-1`. -/
private def linearOfNegOneHom (D : OrientedPDCode n) (f : D.AlexanderModule →+ M)
    (hf : ∀ x, f ((T 1 : ℤ[T;T⁻¹]) • x) = -f x) : D.AlexanderModule →ₗ[ℤ[T;T⁻¹]] M where
  toAddHom := f
  map_smul' a x := by
    -- The target scalar action is evaluation at -1 by definition.
    change f (a • x) = evalNegOne a • f x
    have hneg (x : D.AlexanderModule) : f ((T (-1) : ℤ[T;T⁻¹]) • x) = -f x := by
      have h := hf ((T (-1) : ℤ[T;T⁻¹]) • x)
      rw [smul_smul, ← T_add] at h
      simpa using (congrArg Neg.neg h).symm
    have hmul (a b : ℤ[T;T⁻¹])
        (ha : ∀ x, f (a • x) = evalNegOne a • f x)
        (hb : ∀ x, f (b • x) = evalNegOne b • f x) (x : D.AlexanderModule) :
        f ((a * b) • x) = evalNegOne (a * b) • f x := by
      rw [mul_smul, ha, hb, map_mul, mul_smul]
    have hall : ∀ x, f (a • x) = evalNegOne a • f x := by
      induction a using LaurentPolynomial.induction_on with
      | h_C a =>
        intro x
        have hC : (C a : ℤ[T;T⁻¹]) = a := by simp
        rw [hC]
        simp only [map_intCast, Int.cast_id, Int.cast_smul_eq_zsmul, map_zsmul]
      | h_add hp hq =>
        intro x
        rw [add_smul, map_add, hp, hq, map_add, add_smul]
      | h_C_mul_T n a ih =>
        rw [T_add, ← mul_assoc]
        exact hmul _ _ ih (by simpa [evalNegOne] using hf)
      | h_C_mul_T_Z n a ih =>
        rw [sub_eq_add_neg, T_add, ← mul_assoc]
        exact hmul _ _ ih (by simpa [evalNegOne] using hneg)
    exact hall x

variable (R M) in
/-- Fox colourings are exactly the additive homomorphisms out of the Alexander module that
intertwine `t` with negation. -/
def foxColoringsNegOneHomEquiv (D : OrientedPDCode n) :
    D.foxColorings R M ≃ {f : D.AlexanderModule →+ M // ∀ x, f ((T 1 : ℤ[T;T⁻¹]) • x) = -f x} where
  toFun v := ⟨D.foxColoringLift R M v, foxColoringLift_T_smul D v⟩
  invFun f := ofAlexanderHom D (linearOfNegOneHom D f.1 f.2)
  left_inv v := (alexanderHomEquiv R M D).left_inv v
  right_inv f := Subtype.ext <| congrArg LinearMap.toAddMonoidHom
    (toAlexanderHom_ofAlexanderHom D (linearOfNegOneHom D f.1 f.2))

/-- The homomorphism equivalence sends a colouring to its lift. -/
@[simp]
theorem foxColoringsNegOneHomEquiv_apply (D : OrientedPDCode n) (v : D.foxColorings R M) :
    (foxColoringsNegOneHomEquiv R M D v).1 = D.foxColoringLift R M v :=
  (rfl)

/-- The inverse homomorphism equivalence labels each generator by its image. -/
@[simp]
theorem foxColoringsNegOneHomEquiv_symm_apply (D : OrientedPDCode n)
    (f : {f : D.AlexanderModule →+ M // ∀ x, f ((T 1 : ℤ[T;T⁻¹]) • x) = -f x})
    (g : Fin (4 * n) ⊕ Fin D.crossinglessComponentCount) :
    ((foxColoringsNegOneHomEquiv R M D).symm f).1 g = f.1 (D.alexanderGenerator g) :=
  (rfl)

variable (R M) in
/-- A `ℤ[T;T⁻¹]`-linear equivalence of Alexander modules induces an `R`-linear equivalence of Fox
colouring modules with values in `M`: a colouring of `D` is a linear map out of the Alexander
module of `D` into `M`, on which `t` acts as `-1`, and composing with the inverse equivalence
gives a linear map out of the Alexander module of `D'`. -/
def foxColoringsEquivOfAlexanderModuleEquiv {D : OrientedPDCode n} {D' : OrientedPDCode m}
    (e : D.AlexanderModule ≃ₗ[ℤ[T;T⁻¹]] D'.AlexanderModule) :
    D.foxColorings R M ≃ₗ[R] D'.foxColorings R M :=
  alexanderHomEquiv R M D ≪≫ₗ LinearEquiv.congrLeft M R e ≪≫ₗ (alexanderHomEquiv R M D').symm

/-- Transport evaluates the original lift on the inverse image of each generator. -/
theorem foxColoringsEquivOfAlexanderModuleEquiv_apply
    {D : OrientedPDCode n} {D' : OrientedPDCode m}
    (e : D.AlexanderModule ≃ₗ[ℤ[T;T⁻¹]] D'.AlexanderModule) (v : D.foxColorings R M)
    (g : Fin (4 * m) ⊕ Fin D'.crossinglessComponentCount) :
    (foxColoringsEquivOfAlexanderModuleEquiv R M e v).1 g =
      D.foxColoringLift R M v (e.symm (D'.alexanderGenerator g)) :=
  (rfl)

/-- Identity transport fixes every Fox colouring. -/
@[simp]
theorem foxColoringsEquivOfAlexanderModuleEquiv_refl (D : OrientedPDCode n) :
    foxColoringsEquivOfAlexanderModuleEquiv R M (LinearEquiv.refl ℤ[T;T⁻¹] D.AlexanderModule) =
      LinearEquiv.refl R (D.foxColorings R M) := by
  ext v g
  simp [foxColoringsEquivOfAlexanderModuleEquiv_apply]

/-- Reversing the Alexander equivalence reverses the colouring equivalence. -/
@[simp]
theorem foxColoringsEquivOfAlexanderModuleEquiv_symm
    {D : OrientedPDCode n} {D' : OrientedPDCode m}
    (e : D.AlexanderModule ≃ₗ[ℤ[T;T⁻¹]] D'.AlexanderModule) :
    foxColoringsEquivOfAlexanderModuleEquiv R M e.symm =
      (foxColoringsEquivOfAlexanderModuleEquiv R M e).symm := by
  ext v g
  rfl

/-- Alexander equivalence composition agrees with colouring transport composition. -/
theorem foxColoringsEquivOfAlexanderModuleEquiv_trans
    {k : ℕ} {D : OrientedPDCode n} {D' : OrientedPDCode m} {D'' : OrientedPDCode k}
    (e : D.AlexanderModule ≃ₗ[ℤ[T;T⁻¹]] D'.AlexanderModule)
    (e' : D'.AlexanderModule ≃ₗ[ℤ[T;T⁻¹]] D''.AlexanderModule) :
    foxColoringsEquivOfAlexanderModuleEquiv R M (e ≪≫ₗ e') =
      foxColoringsEquivOfAlexanderModuleEquiv R M e ≪≫ₗ
        foxColoringsEquivOfAlexanderModuleEquiv R M e' := by
  ext v g
  simp [foxColoringsEquivOfAlexanderModuleEquiv, alexanderHomEquiv,
    toAlexanderHom_ofAlexanderHom, ofAlexanderHom_apply]

/-- The equivalence induced by an equivalence `e` of Alexander modules keeps the label of a
generator that `e` sends to a generator. -/
theorem foxColoringsEquivOfAlexanderModuleEquiv_apply_of_apply_alexanderGenerator
    {D : OrientedPDCode n} {D' : OrientedPDCode m}
    (e : D.AlexanderModule ≃ₗ[ℤ[T;T⁻¹]] D'.AlexanderModule) (v : D.foxColorings R M)
    {g : Fin (4 * n) ⊕ Fin D.crossinglessComponentCount}
    {g' : Fin (4 * m) ⊕ Fin D'.crossinglessComponentCount}
    (h : e (D.alexanderGenerator g) = D'.alexanderGenerator g') :
    (foxColoringsEquivOfAlexanderModuleEquiv R M e v :
      Fin (4 * m) ⊕ Fin D'.crossinglessComponentCount → M) g' = v.1 g := by
  simp [foxColoringsEquivOfAlexanderModuleEquiv_apply, ← h]

namespace ReidemeisterEquiv

variable {D : OrientedPDCode n} {D' : OrientedPDCode m}

variable (R M) in
/-- **Fox colourings are invariants of Reidemeister equivalence**: Reidemeister equivalent codes
have linearly equivalent modules of Fox colourings, with values in any module `M` over any
semiring `R`. -/
theorem nonempty_foxColorings_linearEquiv (h : ReidemeisterEquiv D D') :
    Nonempty (D.foxColorings R M ≃ₗ[R] D'.foxColorings R M) :=
  h.nonempty_alexanderModule_linearEquiv.map (foxColoringsEquivOfAlexanderModuleEquiv R M)

variable (R M) in
/-- **The number of Fox colourings is an invariant of Reidemeister equivalence.** -/
theorem natCard_foxColorings_eq (h : ReidemeisterEquiv D D') :
    Nat.card (D.foxColorings R M) = Nat.card (D'.foxColorings R M) :=
  Nat.card_congr (h.nonempty_foxColorings_linearEquiv R M).some.toEquiv

end ReidemeisterEquiv

end OrientedPDCode

end TauCeti
