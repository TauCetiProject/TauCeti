/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.MonoidLocalization.GrothendieckGroup
public import TauCeti.Algebra.Category.ModuleCat.FiniteProjective.KZero.Defs
public import TauCeti.Algebra.Category.ModuleCat.FiniteProjective.StableEquivalent
public import TauCeti.LinearAlgebra.Matrix.Idempotent.Equivalence
public import TauCeti.RingTheory.GrothendieckRing

import TauCeti.Algebra.Category.ModuleCat.RestrictScalars

/-!
# The idempotent monoid and projective `K₀`

For a nonunital semiring `A`, the *idempotent monoid* `V(A)` is the set of idempotent square
matrices over `A`, of all sizes, modulo equivalence of idempotents (`Matrix.IdempotentEquivalent`:
`e = x * y` and `f = y * x` for rectangular `x` and `y`). Block sum `e ⊕ f = Matrix.fromBlocks e 0
0 f` makes it a commutative monoid, with the empty matrix as zero. No cancellation is assumed:
`V(A)` need not be cancellative.

Over a ring, `V(A)` models the isomorphism classes of finitely generated projective modules under
direct sum: an idempotent `e` presents the image of its action on vectors, every finitely
generated projective module is such an image, and two idempotents present isomorphic modules
exactly when they are equivalent. Accordingly, `V(R)` is isomorphic as an additive monoid to
`ObjectCode (FiniteProjectiveRight R)` (`TauCeti.IdempotentMonoid.objectCodeAddEquiv`), whose
group completion is the projective `K₀` (`TauCeti.IdempotentMonoid.kZeroEquiv`). Transposition over
the opposite ring identifies `V(R)` with `V(Rᵐᵒᵖ)` (`TauCeti.IdempotentMonoid.opEquiv`),
supplying the corresponding left-module comparison `TauCeti.IdempotentMonoid.splitK0Equiv`. As a
consequence every element of `K₀(R)` is `[eRⁿ] - m[R]` for an idempotent matrix `e` and some `m`.

## Main definitions

* `TauCeti.IdempotentMonoid A`: the idempotent monoid `V(A)`, a commutative monoid under block
  sum.
* `TauCeti.IdempotentMonoid.mk e he`: the class of an idempotent matrix `e` over any finite index
  type.
* `TauCeti.IdempotentMonoid.lift`: a function on idempotent matrices that respects equivalence of
  idempotents descends to `V(A)`.
* `TauCeti.IdempotentMonoid.opEquiv`: transposition over the opposite ring, `V(R) ≃ V(Rᵐᵒᵖ)`.
* `TauCeti.IdempotentMonoid.objectCodeAddEquiv`: the monoid isomorphism
  `IdempotentMonoid R ≃+ ObjectCode (FiniteProjectiveRight R)` before group completion.
* `TauCeti.IdempotentMonoid.kZeroEquiv`: the group completion of `V(R)` is `K₀(R)`, the split `K₀`
  of finitely generated projective right `R`-modules.
* `TauCeti.IdempotentMonoid.toSplitK0`: the class map `V(A) → K₀(A)`, `[e] ↦ [Aⁿe]`, for left
  modules.
* `TauCeti.IdempotentMonoid.splitK0Equiv`: the group completion of `V(A)` is the split `K₀` of
  finitely generated projective left `A`-modules.

## Main results

* `TauCeti.IdempotentMonoid.mk_eq_mk_iff`: two idempotents have the same class exactly when they
  are equivalent.
* `TauCeti.IdempotentMonoid.mk_add_mk`: addition is block sum.
* `TauCeti.IdempotentMonoid.mk_eq_zero_iff`: only the zero matrix has class `0`.
* `TauCeti.IdempotentMonoid.kZeroEquiv_of_mk`: the class of `e` goes to the class `[eRⁿ]`, and
  `TauCeti.IdempotentMonoid.kZeroEquiv_of_mk_one`: the class of `1ₘ` goes to `m[R]`.
* `TauCeti.IdempotentMonoid.exists_of_mk_sub_of_mk_one_eq`: every element of the group completion
  of `V(A)` is `[e] - [1ₘ]`.
* `TauCeti.IdempotentMonoid.exists_kZeroEquiv_sub_nsmul_eq`: every element of `K₀(R)` is
  `[eRⁿ] - m[R]`.
* `TauCeti.IdempotentMonoid.splitK0Equiv_of_mk`: the class of `e` goes to the class `[Aⁿe]`.

## References

* J. Rosenberg, *Algebraic K-Theory and Its Applications*, §1.2.
* C. Weibel, *The K-book*, Chapter II, §2, the definition of `K₀` by idempotent matrices.
-/

public section

noncomputable section

namespace TauCeti

open CategoryTheory Matrix LinearMap _root_.Algebra

universe u

section NonUnitalSemiring

variable (A : Type u) [NonUnitalSemiring A]

/-- Equivalence of idempotents (`Matrix.IdempotentEquivalent`), on idempotent square matrices of
every size `n`. -/
def idempotentSetoid :
    Setoid (Σ n : ℕ, {e : Matrix (Fin n) (Fin n) A // IsIdempotentElem e}) where
  r e f := IdempotentEquivalent e.snd.val f.snd.val
  iseqv := ⟨fun e ↦ .refl e.snd.property, .symm, .trans⟩

/-- **The idempotent monoid `V(A)`.** Idempotent square matrices over `A`, of every size, up to
equivalence of idempotents (`Matrix.IdempotentEquivalent`). Addition is the block sum, see
`TauCeti.IdempotentMonoid.mk_add_mk`. -/
def IdempotentMonoid : Type u :=
  Quotient (idempotentSetoid A)

namespace IdempotentMonoid

variable {A}
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- The relabelling of a matrix indexed by a finite type `ι` to `Fin (Fintype.card ι)`. -/
private abbrev toFin (e : Matrix ι ι A) : Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) A :=
  e.submatrix (Fintype.equivFin ι).symm (Fintype.equivFin ι).symm

private theorem idempotentEquivalent_toFin {e : Matrix ι ι A} (he : IsIdempotentElem e) :
    IdempotentEquivalent e (toFin e) :=
  idempotentEquivalent_submatrix he _

/-- The class in `V(A)` of an idempotent square matrix `e` indexed by a finite type. -/
def mk (e : Matrix ι ι A) (he : IsIdempotentElem e) : IdempotentMonoid A :=
  Quotient.mk _ ⟨_, toFin e, (idempotentEquivalent_toFin he).isIdempotentElem_right⟩

/-- **Equality in `V(A)`.** Two idempotent matrices have the same class exactly when they are
equivalent idempotents. -/
@[simp]
theorem mk_eq_mk_iff {e : Matrix ι ι A} {f : Matrix κ κ A} (he : IsIdempotentElem e)
    (hf : IsIdempotentElem f) : mk e he = mk f hf ↔ IdempotentEquivalent e f := by
  refine Quotient.eq.trans ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · exact (idempotentEquivalent_toFin he).trans (h.trans (idempotentEquivalent_toFin hf).symm)
  · exact (idempotentEquivalent_toFin he).symm.trans (h.trans (idempotentEquivalent_toFin hf))

/-- Equivalent idempotents have the same class in `V(A)`. -/
theorem mk_eq_mk {e : Matrix ι ι A} {f : Matrix κ κ A} (h : IdempotentEquivalent e f) :
    mk e h.isIdempotentElem_left = mk f h.isIdempotentElem_right :=
  (mk_eq_mk_iff _ _).2 h

private theorem quotient_mk_eq_mk {n : ℕ} (e : Matrix (Fin n) (Fin n) A)
    (he : IsIdempotentElem e) : Quotient.mk (idempotentSetoid A) ⟨n, e, he⟩ = mk e he :=
  Quotient.sound (idempotentEquivalent_toFin he)

/-- Induction on `V(A)`: every element is the class of an idempotent matrix indexed by `Fin n`. -/
@[elab_as_elim]
theorem ind {motive : IdempotentMonoid A → Prop}
    (mk : ∀ (n : ℕ) (e : Matrix (Fin n) (Fin n) A) (he : IsIdempotentElem e), motive (mk e he))
    (x : IdempotentMonoid A) : motive x :=
  Quotient.ind (fun ⟨n, e, he⟩ ↦ quotient_mk_eq_mk e he ▸ mk n e he) x

/-- **The eliminator of `V(A)`.** A function on idempotent square matrices over `A` that takes
equal values on equivalent idempotents descends to `V(A)`; see
`TauCeti.IdempotentMonoid.lift_mk`. -/
def lift {β : Sort*} (F : ∀ {n : ℕ} (e : Matrix (Fin n) (Fin n) A), IsIdempotentElem e → β)
    (hF : ∀ {n m : ℕ} (e : Matrix (Fin n) (Fin n) A) (f : Matrix (Fin m) (Fin m) A)
      (he : IsIdempotentElem e) (hf : IsIdempotentElem f), IdempotentEquivalent e f →
        F e he = F f hf) :
    IdempotentMonoid A → β :=
  Quotient.lift (s := idempotentSetoid A) (fun e ↦ F e.snd.val e.snd.property)
    fun _ _ h ↦ hF _ _ _ _ h

/-- `TauCeti.IdempotentMonoid.lift` computes `F` on the class of an idempotent matrix. -/
@[simp]
theorem lift_mk {β : Sort*} {F : ∀ {n : ℕ} (e : Matrix (Fin n) (Fin n) A), IsIdempotentElem e → β}
    {hF : ∀ {n m : ℕ} (e : Matrix (Fin n) (Fin n) A) (f : Matrix (Fin m) (Fin m) A)
      (he : IsIdempotentElem e) (hf : IsIdempotentElem f), IdempotentEquivalent e f →
        F e he = F f hf}
    {n : ℕ} (e : Matrix (Fin n) (Fin n) A) (he : IsIdempotentElem e) :
    lift F hF (mk e he) = F e he := by
  rw [← quotient_mk_eq_mk]
  rfl

/-- The zero of `V(A)` is the class of the empty matrix. -/
instance : Zero (IdempotentMonoid A) :=
  ⟨mk (0 : Matrix (Fin 0) (Fin 0) A) .zero⟩

/-- Every zero matrix has the class `0` in `V(A)`. -/
@[simp]
theorem mk_zero : mk (0 : Matrix ι ι A) .zero = 0 :=
  mk_eq_mk (idempotentEquivalent_zero_zero ι (Fin 0))

/-- Only the zero matrix has the class `0` in `V(A)`: an idempotent equivalent to the empty matrix
factors through it. -/
@[simp]
theorem mk_eq_zero_iff {e : Matrix ι ι A} (he : IsIdempotentElem e) : mk e he = 0 ↔ e = 0 :=
  (mk_eq_mk_iff he .zero).trans idempotentEquivalent_zero_iff

/-- The addition of `V(A)` is the block sum of idempotent matrices. -/
@[no_expose] instance : Add (IdempotentMonoid A) where
  add := Quotient.lift₂ (s₁ := idempotentSetoid A) (s₂ := idempotentSetoid A)
    (fun e f ↦ mk (fromBlocks e.snd.val 0 0 f.snd.val)
      (e.snd.property.fromBlocks_zero₁₂_zero₂₁ f.snd.property))
    fun _ _ _ _ h h' ↦ mk_eq_mk (IdempotentEquivalent.fromBlocks h h')

/-- **Addition in `V(A)` is block sum.** -/
@[simp]
theorem mk_add_mk {e : Matrix ι ι A} {f : Matrix κ κ A} (he : IsIdempotentElem e)
    (hf : IsIdempotentElem f) :
    mk e he + mk f hf = mk (fromBlocks e 0 0 f) (he.fromBlocks_zero₁₂_zero₂₁ hf) :=
  mk_eq_mk ((idempotentEquivalent_toFin he).symm.fromBlocks (idempotentEquivalent_toFin hf).symm)

/-- An idempotent is equivalent to its relabelling along a bijection `σ`, stated with the
relabelled matrix given explicitly. -/
private theorem idempotentEquivalent_of_submatrix_eq {μ : Type*} [Fintype μ] {e : Matrix ι ι A}
    (he : IsIdempotentElem e) {f : Matrix μ μ A} (σ : μ ≃ ι) (h : e.submatrix σ σ = f) :
    IdempotentEquivalent e f :=
  h ▸ idempotentEquivalent_submatrix he σ

instance : AddCommMonoid (IdempotentMonoid A) where
  add_assoc x y z := by
    induction x using ind with | mk n e he
    induction y using ind with | mk m f hf
    induction z using ind with | mk k g hg
    simp only [mk_add_mk]
    refine mk_eq_mk <| idempotentEquivalent_of_submatrix_eq
      ((he.fromBlocks_zero₁₂_zero₂₁ hf).fromBlocks_zero₁₂_zero₂₁ hg) (Equiv.sumAssoc _ _ _).symm ?_
    ext (i | i | i) (j | j | j) <;> simp
  zero_add x := by
    induction x using ind with | mk n e he
    rw [← mk_zero (ι := Fin 0), mk_add_mk]
    exact mk_eq_mk (he.idempotentEquivalent_fromBlocks_zero_left (Fin 0))
  add_zero x := by
    induction x using ind with | mk n e he
    rw [← mk_zero (ι := Fin 0), mk_add_mk]
    exact mk_eq_mk (he.idempotentEquivalent_fromBlocks_zero_right (Fin 0))
  add_comm x y := by
    induction x using ind with | mk n e he
    induction y using ind with | mk m f hf
    rw [mk_add_mk, mk_add_mk]
    exact mk_eq_mk <| idempotentEquivalent_of_submatrix_eq (he.fromBlocks_zero₁₂_zero₂₁ hf)
      (Equiv.sumComm _ _)
      (by simp)
  nsmul := nsmulRec

end IdempotentMonoid

end NonUnitalSemiring

section Opposite

namespace IdempotentMonoid

variable {ι : Type*} [Fintype ι]

/-- The class of an idempotent matrix is unchanged by rewriting the matrix. -/
private theorem mk_congr {R : Type u} [NonUnitalSemiring R] {e f : Matrix ι ι R} (h : e = f)
    (he : IsIdempotentElem e) (hf : IsIdempotentElem f) : mk e he = mk f hf := by
  subst h
  rfl

/-- Transposing over the opposite ring, on classes of idempotent matrices. -/
private def opFun (R : Type u) [NonUnitalSemiring R] : IdempotentMonoid R → IdempotentMonoid Rᵐᵒᵖ :=
  lift (fun e he ↦ mk (eᵀ.map MulOpposite.op) he.matrix_transpose_map_op)
    fun _ _ _ _ h ↦ mk_eq_mk (IdempotentEquivalent.transpose_map_op h)

/-- Transposing back from the opposite ring, on classes of idempotent matrices. -/
private def unopFun (R : Type u) [NonUnitalSemiring R] :
    IdempotentMonoid Rᵐᵒᵖ → IdempotentMonoid R :=
  lift (fun e he ↦ mk (eᵀ.map MulOpposite.unop) he.matrix_transpose_map_unop)
    fun _ _ _ _ h ↦ mk_eq_mk (IdempotentEquivalent.transpose_map_unop h)

private theorem opFun_mk {R : Type u} [NonUnitalSemiring R] {e : Matrix ι ι R}
    (he : IsIdempotentElem e) :
    opFun R (mk e he) = mk (eᵀ.map MulOpposite.op) he.matrix_transpose_map_op :=
  mk_eq_mk (idempotentEquivalent_toFin he).symm.transpose_map_op

private theorem unopFun_mk {R : Type u} [NonUnitalSemiring R] {e : Matrix ι ι Rᵐᵒᵖ}
    (he : IsIdempotentElem e) :
    unopFun R (mk e he) = mk (eᵀ.map MulOpposite.unop) he.matrix_transpose_map_unop :=
  mk_eq_mk (idempotentEquivalent_toFin he).symm.transpose_map_unop

variable (R : Type u) [NonUnitalSemiring R]

/-- **Transposition over the opposite ring.** The isomorphism `V(R) ≃ V(Rᵐᵒᵖ)` sending the class
of an idempotent matrix `e` to the class of its transpose `eᵀ` with entries in `Rᵐᵒᵖ`
(`TauCeti.IdempotentMonoid.opEquiv_mk`). It turns the column action of `e`, presenting a right
`R`-module, into the row action of `eᵀ`, presenting the same module as a left `Rᵐᵒᵖ`-module. -/
def opEquiv : IdempotentMonoid R ≃+ IdempotentMonoid Rᵐᵒᵖ where
  toFun := opFun R
  invFun := unopFun R
  left_inv x := by
    induction x using ind with | mk n e he
    rw [opFun_mk, unopFun_mk]
    exact mk_congr (transpose_map_op_transpose_map_unop e) _ _
  right_inv x := by
    induction x using ind with | mk n e he
    rw [unopFun_mk, opFun_mk]
    exact mk_congr (transpose_map_unop_transpose_map_op e) _ _
  map_add' x y := by
    induction x using ind with | mk n e he
    induction y using ind with | mk m f hf
    rw [mk_add_mk, opFun_mk, opFun_mk, opFun_mk, mk_add_mk]
    exact mk_congr (by simp [fromBlocks_transpose, fromBlocks_map]) _ _

variable {R} in
/-- `TauCeti.IdempotentMonoid.opEquiv` sends the class of `e` to the class of `eᵀ` with entries in
`Rᵐᵒᵖ`. -/
@[simp]
theorem opEquiv_mk {e : Matrix ι ι R} (he : IsIdempotentElem e) :
    opEquiv R (mk e he) = mk (eᵀ.map MulOpposite.op) he.matrix_transpose_map_op :=
  opFun_mk he

variable {R} in
/-- The inverse of `TauCeti.IdempotentMonoid.opEquiv` sends the class of an idempotent `e` over
`Rᵐᵒᵖ` to the class of `eᵀ` with entries in `R`. -/
@[simp]
theorem opEquiv_symm_mk {e : Matrix ι ι Rᵐᵒᵖ} (he : IsIdempotentElem e) :
    (opEquiv R).symm (mk e he) = mk (eᵀ.map MulOpposite.unop) he.matrix_transpose_map_unop :=
  unopFun_mk he

end IdempotentMonoid

end Opposite

section KZero

/-- The column range `e R^ι` of an idempotent matrix `e`, packaged as an object of
`FiniteProjectiveRight R` via reindexing to `Fin (Fintype.card ι)`. -/
noncomputable def FiniteProjectiveModules.ofIdempotent {R : Type u} [Ring R] {ι : Type*}
    [Fintype ι] (e : Matrix ι ι R) (he : IsIdempotentElem e) : FiniteProjectiveRight R :=
  let σ := Fintype.equivFin ι
  ⟨ModuleCat.of Rᵐᵒᵖ (range ((e.reindex σ σ).mulVecBilin R Rᵐᵒᵖ)),
    finiteProjectiveModules_iff.mpr ⟨inferInstance,
      (he.idempotentEquivalent_reindex σ).isIdempotentElem_left.projective_range_mulVecBilin⟩⟩

/-- Canonical `Rᵐᵒᵖ`-linear equivalence between the underlying module of
`FiniteProjectiveModules.ofIdempotent e he` and the original column range `e R^ι`. -/
noncomputable def FiniteProjectiveModules.ofIdempotentLinearEquiv {R : Type u} [Ring R]
    {ι : Type*} [Fintype ι] (e : Matrix ι ι R) (he : IsIdempotentElem e) :
    (ofIdempotent e he).obj ≃ₗ[Rᵐᵒᵖ] range (e.mulVecBilin R Rᵐᵒᵖ) :=
  (e.rangeMulVecBilinReindexEquiv (Fintype.equivFin ι) (Fintype.equivFin ι)).symm

namespace IdempotentMonoid

variable (R : Type u) [Ring R]

private theorem objectCode_ofIdempotent_congr {ι κ : Type*} [Fintype ι] [Fintype κ]
    {e : Matrix ι ι R} {f : Matrix κ κ R} (he : IsIdempotentElem e) (hf : IsIdempotentElem f)
    (h : IdempotentEquivalent e f) :
    objectCode.{u} (FiniteProjectiveModules.ofIdempotent e he) =
      objectCode.{u} (FiniteProjectiveModules.ofIdempotent f hf) := by
  obtain ⟨ψ⟩ := (nonempty_linearEquiv_range_mulVecBilin_iff he hf).mpr h
  exact objectCode_congr.{u} (ObjectProperty.isoMk (finiteProjectiveModules Rᵐᵒᵖ)
    (X := FiniteProjectiveModules.ofIdempotent e he)
    (Y := FiniteProjectiveModules.ofIdempotent f hf)
    ((FiniteProjectiveModules.ofIdempotentLinearEquiv e he).trans
      (ψ.trans (FiniteProjectiveModules.ofIdempotentLinearEquiv f hf).symm)).toModuleIso)

private def objectCodeFun :
    IdempotentMonoid R → ObjectCode.{u} (FiniteProjectiveRight R) :=
  lift (fun e he ↦ objectCode.{u} (FiniteProjectiveModules.ofIdempotent e he))
    fun _ _ he hg h ↦ objectCode_ofIdempotent_congr R he hg h

variable {R} in
private theorem objectCodeFun_mk_linearEquiv {ι : Type*} [Fintype ι] {e : Matrix ι ι R}
    (he : IsIdempotentElem e) {P : FiniteProjectiveRight R}
    (θ : P.obj ≃ₗ[Rᵐᵒᵖ] range (e.mulVecBilin R Rᵐᵒᵖ)) :
    objectCodeFun R (mk e he) = objectCode.{u} P := by
  let σ := Fintype.equivFin ι
  let hre := (he.idempotentEquivalent_reindex σ).isIdempotentElem_left
  let ψ := (FiniteProjectiveModules.ofIdempotentLinearEquiv (e.reindex σ σ) hre).trans
    (e.rangeMulVecBilinReindexEquiv σ σ).symm
  have hmk : mk (e.reindex σ σ) hre = mk e he := mk_eq_mk (he.idempotentEquivalent_reindex σ)
  rw [← hmk]
  exact (lift_mk (hF := fun _ _ he hg h ↦ objectCode_ofIdempotent_congr R he hg h) _ _).trans <|
    objectCode_congr.{u} (ObjectProperty.isoMk (finiteProjectiveModules Rᵐᵒᵖ)
      (X := FiniteProjectiveModules.ofIdempotent (e.reindex σ σ) hre)
      (Y := P) (ψ.trans θ.symm).toModuleIso)

variable {R} in
private theorem objectCodeFun_mk {ι : Type*} [Fintype ι] (e : Matrix ι ι R)
    (he : IsIdempotentElem e) :
    objectCodeFun R (mk e he) = objectCode.{u} (FiniteProjectiveModules.ofIdempotent e he) :=
  objectCodeFun_mk_linearEquiv (P := FiniteProjectiveModules.ofIdempotent e he) he
    (FiniteProjectiveModules.ofIdempotentLinearEquiv e he)

private def objectCodeHom :
    IdempotentMonoid R →+ ObjectCode.{u} (FiniteProjectiveRight R) where
  toFun := objectCodeFun R
  map_zero' := by
    let Z := FiniteProjectiveModules.ofIdempotent (0 : Matrix (Fin 0) (Fin 0) R)
      IsIdempotentElem.zero
    have hsub : Subsingleton ((finiteProjectiveModules Rᵐᵒᵖ).ι.obj Z) :=
      (FiniteProjectiveModules.ofIdempotentLinearEquiv
        (0 : Matrix (Fin 0) (Fin 0) R) IsIdempotentElem.zero).toEquiv.subsingleton
    have hzero : Limits.IsZero Z :=
      Limits.IsZero.of_full_of_faithful_of_isZero (finiteProjectiveModules Rᵐᵒᵖ).ι Z
        (ModuleCat.isZero_of_subsingleton _)
    exact (objectCodeFun_mk (0 : Matrix (Fin 0) (Fin 0) R) IsIdempotentElem.zero).trans
      ((objectCode_congr.{u} (hzero.iso (Limits.isZero_zero _))).trans objectCode_zero.{u})
  map_add' a b := by
    induction a using ind with | mk m e he =>
    induction b using ind with | mk n f hf =>
    rw [mk_add_mk, objectCodeFun_mk e he, objectCodeFun_mk f hf, ← objectCode_biprod.{u}]
    exact objectCodeFun_mk_linearEquiv (he.fromBlocks_zero₁₂_zero₂₁ hf)
      (((FiniteProjectiveModules.biprodLinearEquiv _ _).trans
        ((FiniteProjectiveModules.ofIdempotentLinearEquiv e he).prodCongr
          (FiniteProjectiveModules.ofIdempotentLinearEquiv f hf))).trans
        (rangeMulVecBilinFromBlocksEquiv e f).symm)

private theorem objectCodeHom_apply (x : IdempotentMonoid R) :
    objectCodeHom R x = objectCodeFun R x :=
  (rfl)

private theorem objectCodeHom_bijective : Function.Bijective (objectCodeHom R) :=
  ⟨fun a b hab ↦ by
    induction a using ind with | mk m e he =>
    induction b using ind with | mk n f hf =>
    rw [objectCodeHom_apply R, objectCodeHom_apply R, objectCodeFun_mk e he,
      objectCodeFun_mk f hf, objectCode_eq_objectCode_iff.{u}] at hab
    obtain ⟨iso⟩ := hab
    exact (mk_eq_mk_iff he hf).mpr
      ((nonempty_linearEquiv_range_mulVecBilin_iff he hf).mp
        ⟨(FiniteProjectiveModules.ofIdempotentLinearEquiv e he).symm.trans
          (((finiteProjectiveModules Rᵐᵒᵖ).ι.mapIso iso).toLinearEquiv.trans
            (FiniteProjectiveModules.ofIdempotentLinearEquiv f hf))⟩),
  fun c ↦ by
    obtain ⟨P, rfl⟩ := objectCode_surjective.{u} c
    have : Module.Finite Rᵐᵒᵖ P.obj := (finiteProjectiveModules_iff.mp P.property).1
    have : Module.Projective Rᵐᵒᵖ P.obj := (finiteProjectiveModules_iff.mp P.property).2
    obtain ⟨n, e, he, ⟨θ⟩⟩ := Module.Finite.exists_linearEquiv_range_mulVecBilin R P.obj
    exact ⟨mk e he, (objectCodeHom_apply R (mk e he)).trans (objectCodeFun_mk_linearEquiv he θ)⟩⟩

/-- **Idempotent presentation of the monoid of projective modules.** Sending the equivalence class
of `e` to the isomorphism class of its column range `e Rⁿ` is an isomorphism of additive
commutative monoids between `IdempotentMonoid R` and the isomorphism classes of finitely
generated projective right `R`-modules under binary biproducts. -/
def objectCodeAddEquiv :
    IdempotentMonoid R ≃+ ObjectCode.{u} (FiniteProjectiveRight R) :=
  AddEquiv.ofBijective (objectCodeHom R) (objectCodeHom_bijective R)

variable {R} in
/-- Evaluating `objectCodeAddEquiv` on `[e]` yields the code of any finitely generated projective
right `R`-module linearly isomorphic to `e R^ι`. -/
theorem objectCodeAddEquiv_mk_linearEquiv {ι : Type*} [Fintype ι] {e : Matrix ι ι R}
    (he : IsIdempotentElem e) {P : FiniteProjectiveRight R}
    (θ : P.obj ≃ₗ[Rᵐᵒᵖ] range (e.mulVecBilin R Rᵐᵒᵖ)) :
    objectCodeAddEquiv R (mk e he) = objectCode.{u} P := by
  rw [objectCodeAddEquiv, AddEquiv.ofBijective_apply, objectCodeHom_apply R]
  exact objectCodeFun_mk_linearEquiv he θ

variable {R} in
@[simp]
theorem objectCodeAddEquiv_mk {ι : Type*} [Fintype ι] (e : Matrix ι ι R)
    (he : IsIdempotentElem e) :
    objectCodeAddEquiv R (mk e he) = objectCode.{u} (FiniteProjectiveModules.ofIdempotent e he) :=
  objectCodeAddEquiv_mk_linearEquiv (P := FiniteProjectiveModules.ofIdempotent e he) he
    (FiniteProjectiveModules.ofIdempotentLinearEquiv e he)

/-- **`K₀(R)` is the group completion of the idempotent monoid `V(R)`.** Obtained by group
completing `TauCeti.IdempotentMonoid.objectCodeAddEquiv` and composing with
`TauCeti.SplitK0.grothendieckAddGroupEquiv`: the class of an idempotent matrix `e` goes to the
class `[eRⁿ]` of the image of its action on column vectors, a finitely generated projective right
`R`-module (`TauCeti.IdempotentMonoid.kZeroEquiv_of_mk`). -/
def kZeroEquiv : GrothendieckAddGroup (IdempotentMonoid R) ≃+ KZero R :=
  ((AddLocalization.addMonoidOf ⊤).addEquivOfAddEquiv
    (AddLocalization.addMonoidOf (M := ObjectCode.{u} (FiniteProjectiveRight R)) ⊤)
    (j := objectCodeAddEquiv R) (AddSubmonoid.map_equiv_top (objectCodeAddEquiv R))).trans
    (SplitK0.grothendieckAddGroupEquiv.{u} (FiniteProjectiveRight R))

variable {R} {ι : Type*} [Fintype ι]

/-- `TauCeti.IdempotentMonoid.kZeroEquiv` sends the class of an idempotent matrix `e` to the class
of any finitely generated projective right `R`-module isomorphic to `eRⁿ`, the image of the action
`v ↦ e *ᵥ v` of `e` on column vectors. -/
theorem kZeroEquiv_of_mk {e : Matrix ι ι R} (he : IsIdempotentElem e) (X : FiniteProjectiveRight R)
    (θ : X.obj ≃ₗ[Rᵐᵒᵖ] range (mulVecBilin R Rᵐᵒᵖ e)) :
    kZeroEquiv R (GrothendieckAddGroup.of (mk e he)) = SplitK0.of.{u} X := by
  have h : (AddLocalization.addMonoidOf ⊤).addEquivOfAddEquiv
      (AddLocalization.addMonoidOf (M := ObjectCode.{u} (FiniteProjectiveRight R)) ⊤)
      (AddSubmonoid.map_equiv_top (objectCodeAddEquiv R)) (GrothendieckAddGroup.of (mk e he)) =
        GrothendieckAddGroup.of (objectCodeAddEquiv R (mk e he)) :=
    AddSubmonoid.LocalizationMap.addEquivOfAddEquiv_eq _ _ _
  rw [kZeroEquiv, AddEquiv.trans_apply, h, objectCodeAddEquiv_mk_linearEquiv he θ,
    SplitK0.grothendieckAddGroupEquiv_of_objectCode]

-- Not `@[simp]`: the simp normal form of `GrothendieckAddGroup.of x` is
-- `AddLocalization.addMonoidOf ⊤ x`, as for `Algebra.GrothendieckAddGroup.lift_apply_of`.
/-- `TauCeti.IdempotentMonoid.kZeroEquiv` sends the class of the identity matrix of size `m` to
`m[R]`, the class of the free right module `Rᵐ`. -/
theorem kZeroEquiv_of_mk_one (m : ℕ) :
    kZeroEquiv R (GrothendieckAddGroup.of (mk (1 : Matrix (Fin m) (Fin m) R) .one)) =
      m • SplitK0.of.{u} (finiteProjectiveModulesRegular Rᵐᵒᵖ) := by
  -- `Rᵐ`, the image of the identity matrix, written as `(Rᵐᵒᵖ)ᵐ` through `unop` on coordinates.
  let L : (Fin m → Rᵐᵒᵖ) ≃ₗ[Rᵐᵒᵖ] (Fin m → R) :=
    .piCongrRight fun _ ↦ (MulOpposite.opLinearEquiv Rᵐᵒᵖ).symm
  have htop : range (mulVecBilin R Rᵐᵒᵖ (1 : Matrix (Fin m) (Fin m) R)) = ⊤ :=
    range_eq_top.2 fun v ↦ ⟨v, one_mulVec v⟩
  rw [kZeroEquiv_of_mk _ ⟨ModuleCat.of Rᵐᵒᵖ (Fin m → Rᵐᵒᵖ),
    finiteProjectiveModules_iff.2 ⟨inferInstance, inferInstance⟩⟩
    (L.trans (LinearEquiv.ofTop _ htop).symm)]
  exact SplitK0.of_eq_nsmul_of_linearEquiv_fin (.refl _ _) (.refl _ _)

/-- **Every element of the group completion of `V(A)` is `[e] - [1ₘ]`.** Adding the complement
`1 - f` of an idempotent `f` to both terms of `[e] - [f]` replaces `[f]` by the class of an
identity matrix. -/
theorem exists_of_mk_sub_of_mk_one_eq (y : GrothendieckAddGroup (IdempotentMonoid R)) :
    ∃ (n : ℕ) (e : Matrix (Fin n) (Fin n) R) (he : IsIdempotentElem e) (m : ℕ),
      GrothendieckAddGroup.of (mk e he) -
        GrothendieckAddGroup.of (mk (1 : Matrix (Fin m) (Fin m) R) .one) = y := by
  obtain ⟨a, b, rfl⟩ := GrothendieckAddGroup.exists_eq_sub_of y
  induction a using ind with | mk n e he
  induction b using ind with | mk m f hf
  have he' := he.fromBlocks_zero₁₂_zero₂₁ hf.one_sub
  have hE := idempotentEquivalent_submatrix he' finSumFinEquiv.symm
  refine ⟨n + m, reindex finSumFinEquiv finSumFinEquiv (fromBlocks e 0 0 (1 - f)),
    hE.isIdempotentElem_right, m, ?_⟩
  -- `[e ⊕ (1 - f)] - [f ⊕ (1 - f)] = [e] - [f]`, and `f ⊕ (1 - f)` is equivalent to `1`.
  have h₁ : mk (reindex finSumFinEquiv finSumFinEquiv (fromBlocks e 0 0 (1 - f)))
      hE.isIdempotentElem_right = mk e he + mk (1 - f) hf.one_sub := by
    rw [mk_add_mk]
    exact mk_eq_mk hE.symm
  have h₂ : mk (1 : Matrix (Fin m) (Fin m) R) .one = mk f hf + mk (1 - f) hf.one_sub := by
    rw [mk_add_mk]
    exact mk_eq_mk (idempotentEquivalent_fromBlocks_one_sub hf).symm
  rw [h₁, h₂, map_add, map_add, add_sub_add_right_eq_sub]

/-- **Every class in `K₀(R)` is `[eRⁿ] - m[R]`.** Every element of `K₀(R)` is the difference of
the class of the image of an idempotent matrix `e` acting on column vectors and the class of a
finite free right module `Rᵐ`. -/
theorem exists_kZeroEquiv_sub_nsmul_eq (x : KZero R) :
    ∃ (n : ℕ) (e : Matrix (Fin n) (Fin n) R) (he : IsIdempotentElem e) (m : ℕ),
      kZeroEquiv R (GrothendieckAddGroup.of (mk e he)) -
        m • SplitK0.of.{u} (finiteProjectiveModulesRegular Rᵐᵒᵖ) = x := by
  obtain ⟨n, e, he, m, h⟩ := exists_of_mk_sub_of_mk_one_eq ((kZeroEquiv R).symm x)
  refine ⟨n, e, he, m, ?_⟩
  rw [← kZeroEquiv_of_mk_one, ← map_sub, h, AddEquiv.apply_symm_apply]

end IdempotentMonoid

end KZero

section Ring

namespace IdempotentMonoid

open MulOpposite

private theorem finiteProjectiveModules_inverseImage_opOp (A : Type u) [Ring A] :
    (finiteProjectiveModules A).inverseImage
      (ModuleCat.restrictScalarsEquivalenceOfRingEquiv (RingEquiv.opOp A)).functor =
      finiteProjectiveModules Aᵐᵒᵖᵐᵒᵖ := by
  ext M
  rw [ObjectProperty.prop_inverseImage_iff, finiteProjectiveModules_iff,
    finiteProjectiveModules_iff, ModuleCat.restrictScalarsEquivalenceOfRingEquiv_functor,
    (RingEquiv.opOp A).toRingHom.finite_restrictScalars_iff
      (RingEquiv.opOp A).surjective M,
    (RingEquiv.opOp A).projective_restrictScalars_iff M]

private def opOpFullSubcategoryEquiv (A : Type u) [Ring A] :
    FiniteProjectiveRight Aᵐᵒᵖ ≌ (finiteProjectiveModules A).FullSubcategory :=
  (ModuleCat.restrictScalarsEquivalenceOfRingEquiv (RingEquiv.opOp A)).congrFullSubcategory
    (finiteProjectiveModules_inverseImage_opOp A)

variable (A : Type u) [Ring A]

/-- **`K₀` is the group completion of the idempotent monoid.** Obtained from the right-module
comparison `TauCeti.IdempotentMonoid.kZeroEquiv` via transposition over the opposite ring
(`TauCeti.IdempotentMonoid.opEquiv`): the class of an idempotent matrix `e` goes to the class of
the image `Aⁿe` of its action on row vectors (`TauCeti.IdempotentMonoid.splitK0Equiv_of_mk`). -/
def splitK0Equiv :
    GrothendieckAddGroup (IdempotentMonoid A) ≃+
      SplitK0.{u} (finiteProjectiveModules A).FullSubcategory :=
  (((AddLocalization.addMonoidOf ⊤).addEquivOfAddEquiv (AddLocalization.addMonoidOf ⊤)
    (j := opEquiv A) (AddSubmonoid.map_equiv_top (opEquiv A))).trans
    (kZeroEquiv Aᵐᵒᵖ)).trans
    (SplitK0.mapEquiv (opOpFullSubcategoryEquiv A))

variable {A}

/-- **The class map `V(A) → K₀(A)`.** The class of an idempotent matrix `e` goes to the class of
the image `Aⁿe` of its action on row vectors, a finitely generated projective left `A`-module; see
`TauCeti.IdempotentMonoid.toSplitK0_mk`. -/
def toSplitK0 : IdempotentMonoid A →+ SplitK0.{u} (finiteProjectiveModules A).FullSubcategory :=
  (splitK0Equiv A).toAddMonoidHom.comp GrothendieckAddGroup.of

-- Not `@[simp]`: the simp normal form of `GrothendieckAddGroup.of x` is
-- `AddLocalization.addMonoidOf ⊤ x`, as for `Algebra.GrothendieckAddGroup.lift_apply_of`.
/-- On `V(A)`, the isomorphism `TauCeti.IdempotentMonoid.splitK0Equiv` is the class map
`TauCeti.IdempotentMonoid.toSplitK0`. -/
theorem splitK0Equiv_of (x : IdempotentMonoid A) :
    splitK0Equiv A (GrothendieckAddGroup.of x) = toSplitK0 x := by
  rw [toSplitK0, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom]

/-- The isomorphism `TauCeti.IdempotentMonoid.splitK0Equiv` sends the class of an idempotent
matrix `e` to the class of any module isomorphic to the image `Aⁿe` of its action on row vectors. -/
theorem splitK0Equiv_of_mk {ι : Type*} [Fintype ι] {e : Matrix ι ι A} (he : IsIdempotentElem e)
    (X : (finiteProjectiveModules A).FullSubcategory) (θ : X.obj ≃ₗ[A] range e.vecMulLinear) :
    splitK0Equiv A (GrothendieckAddGroup.of (mk e he)) = SplitK0.of.{u} X := by
  have hop : (AddLocalization.addMonoidOf ⊤).addEquivOfAddEquiv (AddLocalization.addMonoidOf ⊤)
      (AddSubmonoid.map_equiv_top (opEquiv A)) (GrothendieckAddGroup.of (mk e he)) =
        GrothendieckAddGroup.of (opEquiv A (mk e he)) :=
    AddSubmonoid.LocalizationMap.addEquivOfAddEquiv_eq _ _ _
  let Y : FiniteProjectiveRight Aᵐᵒᵖ := (opOpFullSubcategoryEquiv A).inverse.obj X
  have : RingHomInvPair (RingEquiv.opOp A).toRingHom (RingEquiv.opOp A).symm.toRingHom :=
    RingHomInvPair.of_ringEquiv (RingEquiv.opOp A)
  have : RingHomInvPair (RingEquiv.opOp A).symm.toRingHom (RingEquiv.opOp A).toRingHom :=
    RingHomInvPair.of_ringEquiv_symm (RingEquiv.opOp A)
  let eY : Y.obj ≃ₛₗ[(RingEquiv.opOp A).symm.toRingHom] X.obj :=
    { toFun := fun x ↦ x
      invFun := fun x ↦ x
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  -- Transport `θ` across `opOp` and coordinatewise `MulOpposite.op`, turning row vectors `Aⁿe`
  -- into column vectors `(eᵀ.map op) (Aᵐᵒᵖ)ⁿ`.
  let ψ : range e.vecMulLinear ≃+ range ((eᵀ.map op).mulVecBilin Aᵐᵒᵖ Aᵐᵒᵖᵐᵒᵖ) :=
    { toFun := fun v ↦ ⟨op ∘ (v : ι → A), by
        obtain ⟨u, hu⟩ := v.property
        refine ⟨op ∘ u, funext fun i ↦ ?_⟩
        simpa [mulVecBilin_apply, mulVec, vecMul, dotProduct] using congrArg op (congrFun hu i)⟩
      invFun := fun w ↦ ⟨unop ∘ (w : ι → Aᵐᵒᵖ), by
        obtain ⟨u, hu⟩ := w.property
        refine ⟨unop ∘ u, funext fun i ↦ ?_⟩
        simpa [mulVecBilin_apply, mulVec, vecMul, dotProduct] using congrArg unop (congrFun hu i)⟩
      left_inv := fun _ ↦ Subtype.ext (funext fun _ ↦ rfl)
      right_inv := fun _ ↦ Subtype.ext (funext fun _ ↦ rfl)
      map_add' := fun _ _ ↦ rfl }
  let θ' : Y.obj ≃ₗ[Aᵐᵒᵖᵐᵒᵖ] range ((eᵀ.map op).mulVecBilin Aᵐᵒᵖ Aᵐᵒᵖᵐᵒᵖ) :=
    { toFun := fun x ↦ ψ (θ (eY x))
      invFun := fun y ↦ eY.symm (θ.symm (ψ.symm y))
      left_inv := fun x ↦ by
        dsimp only
        rw [ψ.symm_apply_apply, θ.symm_apply_apply, eY.symm_apply_apply]
      right_inv := fun y ↦ by
        dsimp only
        rw [eY.apply_symm_apply, θ.apply_symm_apply, ψ.apply_symm_apply]
      map_add' := fun x y ↦ by rw [eY.map_add, θ.map_add, ψ.map_add]
      map_smul' := fun c x ↦ by
        induction c using MulOpposite.rec' with | h c =>
        induction c using MulOpposite.rec' with | h a =>
        have hact : eY (op (op a) • x) = a • eY x := eY.map_smulₛₗ (op (op a)) x
        apply Subtype.ext
        ext i
        dsimp only [ψ, AddEquiv.coe_mk, Equiv.coe_fn_mk, Function.comp_apply]
        rw [hact, θ.map_smul, RingHom.id_apply]
        exact op_mul a _ }
  rw [splitK0Equiv, AddEquiv.trans_apply, AddEquiv.trans_apply, hop, opEquiv_mk,
    kZeroEquiv_of_mk he.matrix_transpose_map_op Y θ', SplitK0.mapEquiv_of]
  exact SplitK0.of_congr ((opOpFullSubcategoryEquiv A).counitIso.app X)

/-- The class of an idempotent matrix `e` goes to the class of any module `X` isomorphic to the
image `Aⁿe` of its action on row vectors. -/
theorem toSplitK0_mk {ι : Type*} [Fintype ι] {e : Matrix ι ι A} (he : IsIdempotentElem e)
    (X : (finiteProjectiveModules A).FullSubcategory) (θ : X.obj ≃ₗ[A] range e.vecMulLinear) :
    toSplitK0 (mk e he) = SplitK0.of.{u} X :=
  splitK0Equiv_of_mk he X θ

end IdempotentMonoid

end Ring

end TauCeti
