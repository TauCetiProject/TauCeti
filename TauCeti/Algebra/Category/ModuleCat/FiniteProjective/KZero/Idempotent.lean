/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.MonoidLocalization.GrothendieckGroup
public import TauCeti.Algebra.Category.ModuleCat.FiniteProjective.KZero.Defs
public import TauCeti.Algebra.Category.ModuleCat.FiniteProjective.StableEquivalent
public import TauCeti.LinearAlgebra.Matrix.Idempotent
public import TauCeti.RingTheory.GrothendieckRing

/-!
# The idempotent monoid and projective `K₀`

For a semiring `A`, the *idempotent monoid* `V(A)` is the set of idempotent square matrices over
`A`, of all sizes, modulo equivalence of idempotents (`Matrix.IdempotentEquivalent`: `e = x * y`
and `f = y * x` for rectangular `x` and `y`). Block sum `e ⊕ f = Matrix.fromBlocks e 0 0 f` makes it
a commutative monoid, with the empty matrix as zero. No cancellation is assumed: `V(A)` need not
be cancellative.

Over a ring, `V(A)` models the isomorphism classes of finitely generated projective modules under
direct sum: an idempotent `e` presents the image of its action on vectors, every finitely
generated projective module is such an image, and two idempotents present isomorphic modules
exactly when they are equivalent. Accordingly the group completion of `V(A)` is the projective
`K₀`. This file proves this for left modules over any ring, with `[e] ↦ [Aⁿe]`, and for the
projective `K₀` of right modules `TauCeti.KZero R`, with `[e] ↦ [eRⁿ]`, the image of the column
action of `e`. The two are related by transposition over the opposite ring, which identifies
`V(R)` with `V(Rᵐᵒᵖ)`. As a consequence every element of `K₀(R)` is `[eRⁿ] - m[R]` for an
idempotent matrix `e` and some `m`.

## Main definitions

* `TauCeti.IdempotentMonoid A`: the idempotent monoid `V(A)`, a commutative monoid under block
  sum.
* `TauCeti.IdempotentMonoid.mk e he`: the class of an idempotent matrix `e` over any finite index
  type.
* `TauCeti.IdempotentMonoid.lift`: a function on idempotent matrices that respects equivalence of
  idempotents descends to `V(A)`.
* `TauCeti.IdempotentMonoid.toSplitK0`: the class map `V(A) → K₀(A)`, `[e] ↦ [Aⁿe]`, for left
  modules.
* `TauCeti.IdempotentMonoid.splitK0Equiv`: the group completion of `V(A)` is the split `K₀` of
  finitely generated projective left `A`-modules.
* `TauCeti.IdempotentMonoid.opEquiv`: transposition over the opposite ring, `V(R) ≃ V(Rᵐᵒᵖ)`.
* `TauCeti.IdempotentMonoid.kZeroEquiv`: the group completion of `V(R)` is `K₀(R)`, the split `K₀`
  of finitely generated projective right `R`-modules.

## Main results

* `TauCeti.IdempotentMonoid.mk_eq_mk_iff`: two idempotents have the same class exactly when they
  are equivalent.
* `TauCeti.IdempotentMonoid.mk_add_mk`: addition is block sum.
* `TauCeti.IdempotentMonoid.mk_eq_zero_iff`: only the zero matrix has class `0`.
* `TauCeti.IdempotentMonoid.splitK0Equiv_of_mk`: the class of `e` goes to the class `[Aⁿe]`.
* `TauCeti.IdempotentMonoid.exists_of_mk_sub_of_mk_one_eq`: every element of the group completion
  of `V(A)` is `[e] - [1ₘ]`.
* `TauCeti.IdempotentMonoid.kZeroEquiv_of_mk`: the class of `e` goes to the class `[eRⁿ]`, and
  `TauCeti.IdempotentMonoid.kZeroEquiv_of_mk_one`: the class of `1ₘ` goes to `m[R]`.
* `TauCeti.IdempotentMonoid.exists_kZeroEquiv_sub_nsmul_eq`: every element of `K₀(R)` is
  `[eRⁿ] - m[R]`.

## References

* J. Rosenberg, *Algebraic K-Theory and Its Applications*, §1.2.
* C. Weibel, *The K-book*, Chapter II, §2, the definition of `K₀` by idempotent matrices.
-/

public section

noncomputable section

namespace TauCeti

open CategoryTheory Matrix _root_.LinearMap _root_.Algebra

universe u

section Semiring

variable (A : Type u) [Semiring A]

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
  mk_eq_mk ((idempotentEquivalent_iff_exists_mul_eq .zero .zero).2
    ⟨0, 0, Matrix.zero_mul _, Matrix.zero_mul _⟩)

/-- Only the zero matrix has the class `0` in `V(A)`: an idempotent equivalent to the empty matrix
factors through it. -/
@[simp]
theorem mk_eq_zero_iff {e : Matrix ι ι A} (he : IsIdempotentElem e) : mk e he = 0 ↔ e = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ by simp only [h, mk_zero]⟩
  obtain ⟨x, y, hxy, -⟩ :=
    (idempotentEquivalent_iff_exists_mul_eq he .zero).1 ((mk_eq_mk_iff he .zero).1 h)
  rw [← hxy]
  ext i j
  simp [Matrix.mul_apply]

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
    exact mk_eq_mk <| idempotentEquivalent_of_submatrix_eq
      (IsIdempotentElem.zero.fromBlocks_zero₁₂_zero₂₁ he) (Equiv.emptySum (Fin 0) (Fin n)).symm
      (by ext i j; simp)
  add_zero x := by
    induction x using ind with | mk n e he
    rw [← mk_zero (ι := Fin 0), mk_add_mk]
    exact mk_eq_mk <| idempotentEquivalent_of_submatrix_eq
      (he.fromBlocks_zero₁₂_zero₂₁ .zero) (Equiv.sumEmpty (Fin n) (Fin 0)).symm
      (by ext i j; simp)
  add_comm x y := by
    induction x using ind with | mk n e he
    induction y using ind with | mk m f hf
    rw [mk_add_mk, mk_add_mk]
    exact mk_eq_mk <| idempotentEquivalent_of_submatrix_eq (he.fromBlocks_zero₁₂_zero₂₁ hf)
      (Equiv.sumComm _ _)
      (by simp)
  nsmul := nsmulRec

end IdempotentMonoid

end Semiring

section Ring

namespace IdempotentMonoid

variable {A : Type u} [Ring A] {ι : Type*} [Fintype ι]

/-- The image `Aⁿe` of an idempotent matrix `e` acting on row vectors, as a finitely generated
projective left `A`-module. -/
private def rangeObj {n : ℕ} (e : Matrix (Fin n) (Fin n) A) (he : IsIdempotentElem e) :
    (finiteProjectiveModules A).FullSubcategory :=
  ⟨ModuleCat.of A (range e.vecMulLinear),
    finiteProjectiveModules_iff.2 ⟨inferInstance, he.projective_range_vecMulLinear⟩⟩

/-- The class in `K₀(A)` of a finitely generated projective module presented by an idempotent
matrix; it depends only on the class of the idempotent in `V(A)`. -/
private def toSplitK0Fun :
    IdempotentMonoid A → SplitK0.{u} (finiteProjectiveModules A).FullSubcategory :=
  lift (fun e he ↦ SplitK0.of (rangeObj e he))
    fun _ _ he hf h ↦ SplitK0.of_congr <| ObjectProperty.isoMk _ <| LinearEquiv.toModuleIso <|
      ((nonempty_linearEquiv_range_vecMulLinear_iff he hf).2 h).some

private theorem toSplitK0Fun_mk {e : Matrix ι ι A} (he : IsIdempotentElem e)
    (X : (finiteProjectiveModules A).FullSubcategory) (θ : X.obj ≃ₗ[A] range e.vecMulLinear) :
    toSplitK0Fun (mk e he) = SplitK0.of.{u} X := by
  have h := idempotentEquivalent_toFin he
  obtain ⟨φ⟩ := (nonempty_linearEquiv_range_vecMulLinear_iff he h.isIdempotentElem_right).2 h
  exact SplitK0.of_congr (ObjectProperty.isoMk _ (θ.trans φ).toModuleIso).symm

/-- **The class map `V(A) → K₀(A)`.** The class of an idempotent matrix `e` goes to the class of
the image `Aⁿe` of its action on row vectors, a finitely generated projective left `A`-module; see
`TauCeti.IdempotentMonoid.toSplitK0_mk`. -/
def toSplitK0 : IdempotentMonoid A →+ SplitK0.{u} (finiteProjectiveModules A).FullSubcategory where
  toFun := toSplitK0Fun
  map_zero' := by
    refine (toSplitK0Fun_mk .zero (rangeObj (0 : Matrix (Fin 0) (Fin 0) A) .zero)
      (.refl _ _)).trans (SplitK0.of_eq_zero_of_isZero ?_)
    exact Limits.IsZero.of_full_of_faithful_of_isZero (finiteProjectiveModules A).ι _
      (ModuleCat.isZero_of_subsingleton
        (ModuleCat.of A (range (0 : Matrix (Fin 0) (Fin 0) A).vecMulLinear)))
  map_add' x y := by
    induction x using ind with | mk n e he
    induction y using ind with | mk m f hf
    rw [mk_add_mk, toSplitK0Fun_mk _ (rangeObj e he ⊞ rangeObj f hf)
      ((FiniteProjectiveModules.biprodLinearEquiv _ _).trans
        (rangeVecMulLinearFromBlocksEquiv e f).symm), SplitK0.of_biprod,
      toSplitK0Fun_mk he (rangeObj e he) (.refl _ _),
      toSplitK0Fun_mk hf (rangeObj f hf) (.refl _ _)]

/-- The class of an idempotent matrix `e` goes to the class of any module `X` isomorphic to the
image `Aⁿe` of its action on row vectors. -/
theorem toSplitK0_mk {e : Matrix ι ι A} (he : IsIdempotentElem e)
    (X : (finiteProjectiveModules A).FullSubcategory) (θ : X.obj ≃ₗ[A] range e.vecMulLinear) :
    toSplitK0 (mk e he) = SplitK0.of.{u} X :=
  toSplitK0Fun_mk he X θ

/-- The class in `V(A)` of a finitely generated projective module, through a chosen presentation
by an idempotent matrix. -/
private def ofModule (X : (finiteProjectiveModules A).FullSubcategory) : IdempotentMonoid A :=
  mk _ (Module.Finite.exists_linearEquiv_range_vecMulLinear A X.obj).choose_spec.choose_spec.1

private theorem ofModule_eq {e : Matrix ι ι A} (he : IsIdempotentElem e)
    (X : (finiteProjectiveModules A).FullSubcategory) (θ : X.obj ≃ₗ[A] range e.vecMulLinear) :
    ofModule X = mk e he := by
  obtain ⟨he', ⟨θ'⟩⟩ :=
    (Module.Finite.exists_linearEquiv_range_vecMulLinear A X.obj).choose_spec.choose_spec
  exact (mk_eq_mk_iff _ _).2 ((nonempty_linearEquiv_range_vecMulLinear_iff he' he).1
    ⟨θ'.symm.trans θ⟩)

/-- The class of a finitely generated projective module in the group completion of `V(A)`, as an
additive invariant. -/
private def ofModuleInvariant :
    SplitK0.AdditiveInvariant (finiteProjectiveModules A).FullSubcategory
      (GrothendieckAddGroup (IdempotentMonoid A)) where
  obj X := GrothendieckAddGroup.of (ofModule X)
  map_iso X Y φ := by
    obtain ⟨_, _, he, ⟨θ⟩⟩ := Module.Finite.exists_linearEquiv_range_vecMulLinear A Y.obj
    rw [ofModule_eq he X (((finiteProjectiveModules A).ι.mapIso φ).toLinearEquiv.trans θ),
      ofModule_eq he Y θ]
  map_biprod X Y := by
    obtain ⟨_, _, he, ⟨θ⟩⟩ := Module.Finite.exists_linearEquiv_range_vecMulLinear A X.obj
    obtain ⟨_, _, hf, ⟨θ'⟩⟩ := Module.Finite.exists_linearEquiv_range_vecMulLinear A Y.obj
    rw [ofModule_eq he X θ, ofModule_eq hf Y θ', ← map_add, mk_add_mk,
      ofModule_eq _ (X ⊞ Y) ((FiniteProjectiveModules.biprodLinearEquiv X Y).trans
        ((θ.prodCongr θ').trans (rangeVecMulLinearFromBlocksEquiv _ _).symm))]

private theorem ofModuleInvariant_obj (X : (finiteProjectiveModules A).FullSubcategory) :
    ofModuleInvariant.obj X = GrothendieckAddGroup.of (ofModule X) :=
  (rfl)

/-- **Every element of the group completion of `V(A)` is `[e] - [1ₘ]`.** Adding the complement
`1 - f` of an idempotent `f` to both terms of `[e] - [f]` replaces `[f]` by the class of an
identity matrix. -/
theorem exists_of_mk_sub_of_mk_one_eq (y : GrothendieckAddGroup (IdempotentMonoid A)) :
    ∃ (n : ℕ) (e : Matrix (Fin n) (Fin n) A) (he : IsIdempotentElem e) (m : ℕ),
      GrothendieckAddGroup.of (mk e he) -
        GrothendieckAddGroup.of (mk (1 : Matrix (Fin m) (Fin m) A) .one) = y := by
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
  have h₂ : mk (1 : Matrix (Fin m) (Fin m) A) .one = mk f hf + mk (1 - f) hf.one_sub := by
    rw [mk_add_mk]
    exact mk_eq_mk (idempotentEquivalent_fromBlocks_one_sub hf).symm
  rw [h₁, h₂, map_add, map_add, add_sub_add_right_eq_sub]

variable (A) in
/-- **`K₀` is the group completion of the idempotent monoid.** The group completion of `V(A)` is
the split `K₀` of finitely generated projective left `A`-modules, the class of an idempotent matrix
`e` going to the class of the image `Aⁿe` of its action on row vectors
(`TauCeti.IdempotentMonoid.splitK0Equiv_of_mk`). -/
def splitK0Equiv :
    GrothendieckAddGroup (IdempotentMonoid A) ≃+
      SplitK0.{u} (finiteProjectiveModules A).FullSubcategory :=
  AddMonoidHom.toAddEquiv (GrothendieckAddGroup.lift toSplitK0) (SplitK0.lift ofModuleInvariant)
    (GrothendieckAddGroup.addHom_ext fun x ↦ by
      induction x using ind with | mk n e he
      simp only [AddMonoidHom.comp_apply, AddMonoidHom.id_apply]
      rw [GrothendieckAddGroup.lift_apply_of, toSplitK0_mk he (rangeObj e he) (.refl _ _),
        SplitK0.lift_of, ofModuleInvariant_obj, ofModule_eq he (rangeObj e he) (.refl _ _)])
    (SplitK0.hom_ext fun X ↦ by
      obtain ⟨_, _, he, ⟨θ⟩⟩ := Module.Finite.exists_linearEquiv_range_vecMulLinear A X.obj
      simp only [AddMonoidHom.comp_apply, SplitK0.lift_of, AddMonoidHom.id_apply]
      rw [ofModuleInvariant_obj, ofModule_eq he X θ, GrothendieckAddGroup.lift_apply_of,
        toSplitK0_mk he X θ])

-- Not `@[simp]`: the simp normal form of `GrothendieckAddGroup.of x` is
-- `AddLocalization.addMonoidOf ⊤ x`, as for `Algebra.GrothendieckAddGroup.lift_apply_of`.
/-- On `V(A)`, the isomorphism `TauCeti.IdempotentMonoid.splitK0Equiv` is the class map
`TauCeti.IdempotentMonoid.toSplitK0`. -/
theorem splitK0Equiv_of (x : IdempotentMonoid A) :
    splitK0Equiv A (GrothendieckAddGroup.of x) = toSplitK0 x :=
  GrothendieckAddGroup.lift_apply_of _ x

/-- The isomorphism `TauCeti.IdempotentMonoid.splitK0Equiv` sends the class of an idempotent
matrix `e` to the class of any module isomorphic to the image `Aⁿe` of its action on row vectors. -/
theorem splitK0Equiv_of_mk {e : Matrix ι ι A} (he : IsIdempotentElem e)
    (X : (finiteProjectiveModules A).FullSubcategory) (θ : X.obj ≃ₗ[A] range e.vecMulLinear) :
    splitK0Equiv A (GrothendieckAddGroup.of (mk e he)) = SplitK0.of.{u} X :=
  (splitK0Equiv_of _).trans (toSplitK0_mk he X θ)

end IdempotentMonoid

end Ring

section Opposite

namespace IdempotentMonoid

variable {ι : Type*} [Fintype ι]

/-- The class of an idempotent matrix is unchanged by rewriting the matrix. -/
private theorem mk_congr {R : Type u} [Semiring R] {e f : Matrix ι ι R} (h : e = f)
    (he : IsIdempotentElem e) (hf : IsIdempotentElem f) : mk e he = mk f hf := by
  subst h
  rfl

/-- Transposing over the opposite ring, on classes of idempotent matrices. -/
private def opFun (R : Type u) [Semiring R] : IdempotentMonoid R → IdempotentMonoid Rᵐᵒᵖ :=
  lift (fun e he ↦ mk (eᵀ.map MulOpposite.op) he.matrix_transpose_map_op)
    fun _ _ _ _ h ↦ mk_eq_mk (IdempotentEquivalent.transpose_map_op h)

/-- Transposing back from the opposite ring, on classes of idempotent matrices. -/
private def unopFun (R : Type u) [Semiring R] : IdempotentMonoid Rᵐᵒᵖ → IdempotentMonoid R :=
  lift (fun e he ↦ mk (eᵀ.map MulOpposite.unop) he.matrix_transpose_map_unop)
    fun _ _ _ _ h ↦ mk_eq_mk (IdempotentEquivalent.transpose_map_unop h)

private theorem opFun_mk {R : Type u} [Semiring R] {e : Matrix ι ι R} (he : IsIdempotentElem e) :
    opFun R (mk e he) = mk (eᵀ.map MulOpposite.op) he.matrix_transpose_map_op :=
  mk_eq_mk (idempotentEquivalent_toFin he).symm.transpose_map_op

private theorem unopFun_mk {R : Type u} [Semiring R] {e : Matrix ι ι Rᵐᵒᵖ}
    (he : IsIdempotentElem e) :
    unopFun R (mk e he) = mk (eᵀ.map MulOpposite.unop) he.matrix_transpose_map_unop :=
  mk_eq_mk (idempotentEquivalent_toFin he).symm.transpose_map_unop

variable (R : Type u) [Semiring R]

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

namespace IdempotentMonoid

variable (R : Type u) [Ring R] {ι : Type*} [Fintype ι]

/-- **`K₀(R)` is the group completion of the idempotent monoid `V(R)`.** The class of an idempotent
matrix `e` goes to the class `[eRⁿ]` of the image of its action on column vectors, a finitely
generated projective right `R`-module (`TauCeti.IdempotentMonoid.kZeroEquiv_of_mk`). -/
def kZeroEquiv : GrothendieckAddGroup (IdempotentMonoid R) ≃+ KZero R :=
  ((AddLocalization.addMonoidOf ⊤).addEquivOfAddEquiv (AddLocalization.addMonoidOf ⊤)
    (j := opEquiv R) (AddSubmonoid.map_equiv_top (opEquiv R))).trans
    (splitK0Equiv Rᵐᵒᵖ)

variable {R}

/-- `TauCeti.IdempotentMonoid.kZeroEquiv` sends the class of an idempotent matrix `e` to the class
of any finitely generated projective right `R`-module isomorphic to `eRⁿ`, the image of the action
`v ↦ e *ᵥ v` of `e` on column vectors. -/
theorem kZeroEquiv_of_mk {e : Matrix ι ι R} (he : IsIdempotentElem e) (X : FiniteProjectiveRight R)
    (θ : X.obj ≃ₗ[Rᵐᵒᵖ] range (mulVecBilin R Rᵐᵒᵖ e)) :
    kZeroEquiv R (GrothendieckAddGroup.of (mk e he)) = SplitK0.of.{u} X := by
  have h : (AddLocalization.addMonoidOf ⊤).addEquivOfAddEquiv (AddLocalization.addMonoidOf ⊤)
      (AddSubmonoid.map_equiv_top (opEquiv R)) (GrothendieckAddGroup.of (mk e he)) =
        GrothendieckAddGroup.of (opEquiv R (mk e he)) :=
    AddSubmonoid.LocalizationMap.addEquivOfAddEquiv_eq _ _ _
  rw [kZeroEquiv, AddEquiv.trans_apply, h, opEquiv_mk]
  exact splitK0Equiv_of_mk _ X (θ.trans (rangeVecMulLinearTransposeMapOpEquiv e).symm)

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
  rw [kZeroEquiv_of_mk _ (FiniteProjectiveModules.of Rᵐᵒᵖ (Fin m → Rᵐᵒᵖ))
    (L.trans (LinearEquiv.ofTop _ htop).symm)]
  exact SplitK0.of_eq_nsmul_of_linearEquiv_fin (.refl _ _) (.refl _ _)

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

end TauCeti
