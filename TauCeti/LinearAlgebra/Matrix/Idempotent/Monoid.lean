/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.MonoidLocalization.GrothendieckGroup
public import Mathlib.LinearAlgebra.Dimension.DivisionRing
public import TauCeti.LinearAlgebra.Matrix.Idempotent.Equivalence

/-!
# The commutative monoid of idempotent matrices up to rectangular equivalence

For a possibly nonunital, possibly noncommutative semiring `R`, the disjoint union
`Σ n : ℕ, {e : Matrix (Fin n) (Fin n) R // IsIdempotentElem e}` of all finite-size idempotent
matrices over `R` modulo rectangular algebraic equivalence (`Matrix.IsAlgebraicEquivalent`) forms a
small additive commutative monoid `TauCeti.IdempotentMonoid R`:

* addition is induced by the block direct sum `Matrix.fromBlocks e 0 0 f`;
* zero is the class of the empty `0 × 0` matrix (and of every finite zero matrix);
* every finite index type `ι` maps into `IdempotentMonoid R` via `IdempotentMonoid.of e he`, which
  reindexes along `Fintype.equivFin ι` so `IdempotentMonoid R` lives in the same universe as `R`.

Working over `[NonUnitalSemiring R]` accommodates idempotents in matrix algebras over nonunital
rings and operator algebras prior to unitization. Over a unital semiring, diagonal matrix units
`Eᵢᵢ` represent the class of `1 ∈ M₁(R)` and `n • [1₁] = [1ₙ]`. Over a division ring `D`, right
column-space dimension identifies `IdempotentMonoid D` with `ℕ` and its Grothendieck group
completion with `ℤ`; in particular, in `M₂(D)` (or `Mₘ(D)` for any nontrivial finite index type
`m`), `Eᵢᵢ` is equivalent to `Eⱼⱼ` while being equivalent neither to `0` nor to `1`.

## Main definitions

* `TauCeti.IdempotentMonoid R`: rectangular equivalence classes of finite idempotent matrices over
  `R`, equipped with `AddCommMonoid`.
* `TauCeti.IdempotentMonoid.of` and `TauCeti.IdempotentMonoid.lift`: the class map from any finite
  index type and descent of invariants of `Matrix.IsAlgebraicEquivalent`.
* `TauCeti.IdempotentMonoid.map` and `TauCeti.IdempotentMonoid.congr`: functoriality along
  nonunital ring homomorphisms and ring equivalences.
* `TauCeti.IdempotentMonoid.finrankAddEquiv`: the rank isomorphism `IdempotentMonoid D ≃+ ℕ` over a
  division ring `D`.
* `TauCeti.IdempotentMonoid.grothendieckAddGroupEquivInt`: the induced isomorphism
  `Algebra.GrothendieckAddGroup (IdempotentMonoid D) ≃+ ℤ`.

## Main results

* `TauCeti.IdempotentMonoid.of_eq_of_iff`: two idempotent matrices define the same class if and
  only if they are algebraically equivalent.
* `TauCeti.IdempotentMonoid.of_add_of` and `TauCeti.IdempotentMonoid.of_zero`: block direct sums
  give addition and zero matrices give `0`.
* `TauCeti.IdempotentMonoid.nsmul_of_one` and `TauCeti.IdempotentMonoid.of_one_eq_of_one_iff`:
  `n • [1₁] = [1ₙ]`, and identity classes are distinguished by size under invariant basis number.
* `Matrix.finrank_range_mulVecBilin_one` and `Matrix.finrank_range_mulVecBilin_single_one`: right
  column-range dimensions of `1ₘ` and `Eᵢᵢ` under `StrongRankCondition Rᵐᵒᵖ`.

## References

* J. Rosenberg, *Algebraic K-Theory and Its Applications*, §1.2.
* C. A. Weibel, *The K-book*, Chapter II, §2.
* B. Blackadar, *K-Theory for Operator Algebras*, §§4.2–4.6.
-/

public section

open LinearMap Matrix MulOpposite

universe u

section MatrixLemmas

/-- Whenever `Rᵐᵒᵖ` satisfies the strong rank condition, the column range of `1 : Matrix m m R`
has right `R`-rank `Fintype.card m`. -/
theorem Matrix.finrank_range_mulVecBilin_one (R : Type*) [Semiring R] [StrongRankCondition Rᵐᵒᵖ]
    (m : Type*) [Fintype m] [DecidableEq m] :
    Module.finrank Rᵐᵒᵖ (range ((1 : Matrix m m R).mulVecBilin R Rᵐᵒᵖ)) = Fintype.card m := by
  let e : range ((1 : Matrix m m R).mulVecBilin R Rᵐᵒᵖ) ≃ₗ[Rᵐᵒᵖ] (m → Rᵐᵒᵖ) :=
    (rangeMulVecBilinOneEquiv m R).trans (LinearEquiv.piCongrRight fun _ ↦ opLinearEquiv Rᵐᵒᵖ)
  exact e.finrank_eq.trans (Module.finrank_fintype_fun_eq_card Rᵐᵒᵖ)

/-- Whenever `Rᵐᵒᵖ` satisfies the strong rank condition, the column range of any diagonal matrix
unit `Eᵢᵢ` has right `R`-rank `1`. -/
theorem Matrix.finrank_range_mulVecBilin_single_one (R : Type*) [Semiring R]
    [StrongRankCondition Rᵐᵒᵖ] {m : Type*} [Fintype m] [DecidableEq m] (i : m) :
    Module.finrank Rᵐᵒᵖ (range ((single i i (1 : R)).mulVecBilin R Rᵐᵒᵖ)) = 1 := by
  have heq := isAlgebraicEquivalent_single_one_one (R := R) i
  obtain ⟨ψ⟩ := (isAlgebraicEquivalent_iff_nonempty_linearEquiv_range_mulVecBilin
    (isIdempotentElem_single_one i) IsIdempotentElem.one).mp heq
  exact ψ.finrank_eq.trans (finrank_range_mulVecBilin_one R (Fin 1))

end MatrixLemmas

namespace TauCeti

section NonUnitalSemiring

/-- Finite-size idempotent matrices over `R`, indexed by `Fin n` so the type lives in the same
universe as `R`. -/
abbrev IdempotentPresentation (R : Type u) [NonUnitalSemiring R] : Type u :=
  Σ n : ℕ, {e : Matrix (Fin n) (Fin n) R // IsIdempotentElem e}

/-- Rectangular algebraic equivalence as a setoid on `IdempotentPresentation R`. -/
instance idempotentPresentationSetoid (R : Type u) [NonUnitalSemiring R] :
    Setoid (IdempotentPresentation R) where
  r a b := a.2.1.IsAlgebraicEquivalent b.2.1
  iseqv :=
    { refl := fun a ↦ a.2.2.isAlgebraicEquivalent_self
      symm := Matrix.IsAlgebraicEquivalent.symm
      trans := Matrix.IsAlgebraicEquivalent.trans }

/-- **The monoid of idempotent matrices.** Elements of `TauCeti.IdempotentMonoid R` are rectangular
algebraic equivalence classes of finite-size idempotent square matrices over `R`, with addition
given by block direct sum. -/
abbrev IdempotentMonoid (R : Type u) [NonUnitalSemiring R] : Type u :=
  Quotient (idempotentPresentationSetoid R)

namespace IdempotentMonoid

variable {R : Type u} [NonUnitalSemiring R]

/-- The class in `IdempotentMonoid R` of an idempotent `ι × ι` matrix over `R`. -/
noncomputable def of {ι : Type*} [Fintype ι] (e : Matrix ι ι R) (he : IsIdempotentElem e) :
    IdempotentMonoid R :=
  let σ := Fintype.equivFin ι
  Quotient.mk (idempotentPresentationSetoid R)
    ⟨Fintype.card ι, e.reindex σ σ, (he.isAlgebraicEquivalent_reindex σ).isIdempotentElem_left⟩

/-- Equal matrices give equal classes in `IdempotentMonoid R` regardless of the idempotence
proof. -/
theorem of_congr_matrix {ι : Type*} [Fintype ι] {e₁ e₂ : Matrix ι ι R}
    (he₁ : IsIdempotentElem e₁) (he₂ : IsIdempotentElem e₂) (h : e₁ = e₂) :
    of e₁ he₁ = of e₂ he₂ := by
  subst h
  rfl

/-- Two idempotent matrices define the same class in `IdempotentMonoid R` if and only if they are
algebraically equivalent. -/
theorem of_eq_of_iff {ι κ : Type*} [Fintype ι] [Fintype κ] {e : Matrix ι ι R} {f : Matrix κ κ R}
    {he : IsIdempotentElem e} {hf : IsIdempotentElem f} :
    of e he = of f hf ↔ e.IsAlgebraicEquivalent f := by
  let σ := Fintype.equivFin ι
  let τ := Fintype.equivFin κ
  rw [of, of, Quotient.eq]
  change (e.reindex σ σ).IsAlgebraicEquivalent (f.reindex τ τ) ↔ e.IsAlgebraicEquivalent f
  exact ⟨fun h ↦ (he.isAlgebraicEquivalent_reindex σ).symm.trans
      (h.trans (hf.isAlgebraicEquivalent_reindex τ)),
    fun h ↦ (he.isAlgebraicEquivalent_reindex σ).trans
      (h.trans (hf.isAlgebraicEquivalent_reindex τ).symm)⟩

private theorem mk_eq_of (a : IdempotentPresentation R) :
    Quotient.mk (idempotentPresentationSetoid R) a = of a.2.1 a.2.2 :=
  Quotient.sound (a.2.2.isAlgebraicEquivalent_reindex (Fintype.equivFin (Fin a.1))).symm

/-- Induction principle for `IdempotentMonoid R` using `Fin n`-indexed idempotent matrices. -/
@[elab_as_elim]
theorem induction_on {motive : IdempotentMonoid R → Prop} (x : IdempotentMonoid R)
    (of : ∀ (n : ℕ) (e : Matrix (Fin n) (Fin n) R) (he : IsIdempotentElem e),
      motive (IdempotentMonoid.of e he)) :
    motive x := by
  refine Quotient.inductionOn x fun a ↦ ?_
  rw [mk_eq_of]
  exact of a.1 a.2.1 a.2.2

/-- Descend a function on `Fin n`-indexed idempotent matrices that is invariant under rectangular
algebraic equivalence to `IdempotentMonoid R`. -/
def lift {α : Sort*}
    (f : ∀ ⦃n : ℕ⦄ (e : Matrix (Fin n) (Fin n) R), IsIdempotentElem e → α)
    (hf : ∀ ⦃m n : ℕ⦄ {e : Matrix (Fin m) (Fin m) R} {g : Matrix (Fin n) (Fin n) R}
      (he : IsIdempotentElem e) (hg : IsIdempotentElem g),
      e.IsAlgebraicEquivalent g → f e he = f g hg) :
    IdempotentMonoid R → α :=
  Quotient.lift (fun a ↦ f a.2.1 a.2.2) fun a b h ↦ hf a.2.2 b.2.2 h

@[simp]
theorem lift_of_fin {α : Sort*}
    (f : ∀ ⦃n : ℕ⦄ (e : Matrix (Fin n) (Fin n) R), IsIdempotentElem e → α)
    (hf : ∀ ⦃m n : ℕ⦄ {e : Matrix (Fin m) (Fin m) R} {g : Matrix (Fin n) (Fin n) R}
      (he : IsIdempotentElem e) (hg : IsIdempotentElem g),
      e.IsAlgebraicEquivalent g → f e he = f g hg)
    {n : ℕ} (e : Matrix (Fin n) (Fin n) R) (he : IsIdempotentElem e) :
    lift f hf (of e he) = f e he :=
  hf _ he (he.isAlgebraicEquivalent_reindex (Fintype.equivFin (Fin n)))

/-- Reindexing an idempotent matrix along an index equivalence preserves its class. -/
theorem of_reindex {ι ι' : Type*} [Fintype ι] [Fintype ι'] (e : Matrix ι ι R)
    (he : IsIdempotentElem e) (σ : ι ≃ ι') :
    of (e.reindex σ σ) (he.isAlgebraicEquivalent_reindex σ).isIdempotentElem_left = of e he :=
  of_eq_of_iff.mpr (he.isAlgebraicEquivalent_reindex σ)

noncomputable instance : Zero (IdempotentMonoid R) :=
  ⟨of (0 : Matrix (Fin 0) (Fin 0) R) IsIdempotentElem.zero⟩

/-- Every finite zero matrix represents `0` in `IdempotentMonoid R`. -/
@[simp]
theorem of_zero {ι : Type*} [Fintype ι] :
    of (0 : Matrix ι ι R) IsIdempotentElem.zero = 0 :=
  of_eq_of_iff.mpr (Matrix.isAlgebraicEquivalent_zero_zero ι (Fin 0))

/-- A class in `IdempotentMonoid R` vanishes if and only if its representing matrix is `0`. -/
theorem of_eq_zero_iff {ι : Type*} [Fintype ι] {e : Matrix ι ι R} {he : IsIdempotentElem e} :
    of e he = 0 ↔ e = 0 :=
  of_eq_of_iff.trans Matrix.isAlgebraicEquivalent_zero_iff

/-- Padding by a lower-right zero block preserves the class in `IdempotentMonoid R`. -/
theorem of_fromBlocks_zero_right {ι κ : Type*} [Fintype ι] [Fintype κ] (e : Matrix ι ι R)
    (he : IsIdempotentElem e) :
    of (fromBlocks e 0 0 (0 : Matrix κ κ R))
      (he.fromBlocks_zero₁₂_zero₂₁ IsIdempotentElem.zero) = of e he :=
  of_eq_of_iff.mpr (he.isAlgebraicEquivalent_fromBlocks_zero_right κ)

/-- Padding by an upper-left zero block preserves the class in `IdempotentMonoid R`. -/
theorem of_fromBlocks_zero_left {ι κ : Type*} [Fintype ι] [Fintype κ] (e : Matrix κ κ R)
    (he : IsIdempotentElem e) :
    of (fromBlocks (0 : Matrix ι ι R) 0 0 e)
      (IsIdempotentElem.zero.fromBlocks_zero₁₂_zero₂₁ he) = of e he :=
  of_eq_of_iff.mpr (he.isAlgebraicEquivalent_fromBlocks_zero_left ι)

noncomputable instance : Add (IdempotentMonoid R) where
  add := Quotient.lift₂
    (fun a b ↦ of (fromBlocks a.2.1 0 0 b.2.1) (a.2.2.fromBlocks_zero₁₂_zero₂₁ b.2.2))
    fun _ _ _ _ h₁ h₂ ↦ of_eq_of_iff.mpr (h₁.fromBlocks_zero₁₂_zero₂₁ h₂)

/-- Addition in `IdempotentMonoid R` is given by the block direct sum
`Matrix.fromBlocks e 0 0 f`. -/
@[simp]
theorem of_add_of {ι κ : Type*} [Fintype ι] [Fintype κ] (e : Matrix ι ι R)
    (he : IsIdempotentElem e) (f : Matrix κ κ R) (hf : IsIdempotentElem f) :
    of e he + of f hf = of (fromBlocks e 0 0 f) (he.fromBlocks_zero₁₂_zero₂₁ hf) := by
  let σ := Fintype.equivFin ι
  let τ := Fintype.equivFin κ
  change of (fromBlocks (e.reindex σ σ) 0 0 (f.reindex τ τ))
      ((he.isAlgebraicEquivalent_reindex σ).isIdempotentElem_left.fromBlocks_zero₁₂_zero₂₁
        (hf.isAlgebraicEquivalent_reindex τ).isIdempotentElem_left) =
    of (fromBlocks e 0 0 f) (he.fromBlocks_zero₁₂_zero₂₁ hf)
  exact of_eq_of_iff.mpr
    ((he.isAlgebraicEquivalent_reindex σ).fromBlocks_zero₁₂_zero₂₁
      (hf.isAlgebraicEquivalent_reindex τ))

noncomputable instance : AddCommMonoid (IdempotentMonoid R) where
  nsmul := nsmulRec
  add_assoc a b c := by
    induction a using induction_on with | of l e he =>
    induction b using induction_on with | of m f hf =>
    induction c using induction_on with | of n g hg =>
    simp only [of_add_of]
    have hEq : fromBlocks (fromBlocks e 0 0 f) 0 0 g =
        (fromBlocks e 0 0 (fromBlocks f 0 0 g)).reindex
          (Equiv.sumAssoc (Fin l) (Fin m) (Fin n)).symm
          (Equiv.sumAssoc (Fin l) (Fin m) (Fin n)).symm := by
      ext ((_ | _) | _) ((_ | _) | _) <;> rfl
    refine of_eq_of_iff.mpr ?_
    rw [hEq]
    exact (he.fromBlocks_zero₁₂_zero₂₁
      (hf.fromBlocks_zero₁₂_zero₂₁ hg)).isAlgebraicEquivalent_reindex _
  zero_add a := by
    induction a using induction_on with | of n e he =>
    change of (0 : Matrix (Fin 0) (Fin 0) R) IsIdempotentElem.zero + of e he = of e he
    rw [of_add_of, of_fromBlocks_zero_left]
  add_zero a := by
    induction a using induction_on with | of n e he =>
    change of e he + of (0 : Matrix (Fin 0) (Fin 0) R) IsIdempotentElem.zero = of e he
    rw [of_add_of, of_fromBlocks_zero_right]
  add_comm a b := by
    induction a using induction_on with | of m e he =>
    induction b using induction_on with | of n f hf =>
    simp only [of_add_of]
    have hEq : fromBlocks e 0 0 f =
        (fromBlocks f 0 0 e).reindex (Equiv.sumComm (Fin n) (Fin m))
          (Equiv.sumComm (Fin n) (Fin m)) := by
      ext (_ | _) (_ | _) <;> rfl
    refine of_eq_of_iff.mpr ?_
    rw [hEq]
    exact (hf.fromBlocks_zero₁₂_zero₂₁ he).isAlgebraicEquivalent_reindex _

noncomputable instance [Subsingleton R] : Unique (IdempotentMonoid R) where
  default := 0
  uniq x := by
    induction x using induction_on with | of n e he =>
    exact of_eq_zero_iff.mpr (Subsingleton.elim e 0)

section Map

variable {S T F G : Type*} [NonUnitalSemiring S] [NonUnitalSemiring T]

private noncomputable def mapFun [FunLike F R S] [NonUnitalRingHomClass F R S] (φ : F) :
    IdempotentMonoid R → IdempotentMonoid S :=
  lift (fun _ e he ↦ of (e.map φ) (he.map_nonUnitalRingHom φ))
    fun _ _ _ _ _ _ h ↦ of_eq_of_iff.mpr (h.map φ)

private theorem mapFun_of {ι : Type*} [Fintype ι] [FunLike F R S] [NonUnitalRingHomClass F R S]
    (φ : F) (e : Matrix ι ι R) (he : IsIdempotentElem e) :
    mapFun φ (of e he) = of (e.map φ) (he.map_nonUnitalRingHom φ) := by
  let σ := Fintype.equivFin ι
  change of ((e.reindex σ σ).map φ)
      ((he.isAlgebraicEquivalent_reindex σ).isIdempotentElem_left.map_nonUnitalRingHom φ) =
    of (e.map φ) (he.map_nonUnitalRingHom φ)
  exact of_eq_of_iff.mpr ((he.isAlgebraicEquivalent_reindex σ).map φ)

/-- **Functoriality of `IdempotentMonoid`.** Any nonunital ring homomorphism `φ : R → S` induces an
additive monoid homomorphism `IdempotentMonoid R →+ IdempotentMonoid S` by applying `φ`
entrywise. -/
noncomputable def map [FunLike F R S] [NonUnitalRingHomClass F R S] (φ : F) :
    IdempotentMonoid R →+ IdempotentMonoid S where
  toFun := mapFun φ
  map_zero' := by
    change mapFun φ (of (0 : Matrix (Fin 0) (Fin 0) R) IsIdempotentElem.zero) = 0
    rw [mapFun_of]
    exact of_eq_zero_iff.mpr (by ext i; exact Fin.elim0 i)
  map_add' a b := by
    induction a using induction_on with | of m e he =>
    induction b using induction_on with | of n f hf =>
    rw [of_add_of, mapFun_of, mapFun_of, mapFun_of, of_add_of]
    refine of_congr_matrix _ _ ?_
    ext (_ | _) (_ | _) <;> simp

@[simp]
theorem map_of {ι : Type*} [Fintype ι] [FunLike F R S] [NonUnitalRingHomClass F R S] (φ : F)
    (e : Matrix ι ι R) (he : IsIdempotentElem e) :
    map φ (of e he) = of (e.map φ) (he.map_nonUnitalRingHom φ) :=
  mapFun_of φ e he

@[simp]
theorem map_nonUnitalRingHom_id :
    map (NonUnitalRingHom.id R) = AddMonoidHom.id (IdempotentMonoid R) := by
  ext x
  induction x using induction_on with | of n e he =>
  rw [map_of, AddMonoidHom.id_apply]
  exact of_congr_matrix _ _ (by ext; simp)

theorem map_comp [FunLike F R S] [NonUnitalRingHomClass F R S] [FunLike G S T]
    [NonUnitalRingHomClass G S T] (φ : F) (ψ : G) :
    (map ψ).comp (map φ) = map ((ψ : S →ₙ+* T).comp (φ : R →ₙ+* S)) := by
  ext x
  induction x using induction_on with | of n e he =>
  rw [AddMonoidHom.comp_apply, map_of, map_of, map_of]
  exact of_congr_matrix _ _ (by ext; rfl)

/-- A ring equivalence induces an additive isomorphism on `IdempotentMonoid`. -/
noncomputable def congr (e : R ≃+* S) :
    IdempotentMonoid R ≃+ IdempotentMonoid S where
  __ := map e.toNonUnitalRingHom
  invFun := map e.symm.toNonUnitalRingHom
  left_inv x := by
    induction x using induction_on with | of n M hM =>
    change map e.symm.toNonUnitalRingHom (map e.toNonUnitalRingHom (of M hM)) = of M hM
    rw [map_of, map_of]
    exact of_congr_matrix _ _ (by ext; simp)
  right_inv y := by
    induction y using induction_on with | of n M hM =>
    change map e.toNonUnitalRingHom (map e.symm.toNonUnitalRingHom (of M hM)) = of M hM
    rw [map_of, map_of]
    exact of_congr_matrix _ _ (by ext; simp)

@[simp]
theorem congr_of {ι : Type*} [Fintype ι] (φ : R ≃+* S)
    (e : Matrix ι ι R) (he : IsIdempotentElem e) :
    congr φ (of e he) = of (e.map φ) (he.map_nonUnitalRingHom φ) :=
  map_of φ.toNonUnitalRingHom e he

end Map

end IdempotentMonoid

end NonUnitalSemiring

section Semiring

namespace IdempotentMonoid

variable {R : Type u} [Semiring R]

@[simp]
theorem map_id : map (RingHom.id R) = AddMonoidHom.id (IdempotentMonoid R) := by
  ext x
  induction x using induction_on with | of n e he =>
  rw [map_of, AddMonoidHom.id_apply]
  exact of_congr_matrix _ _ (by ext; simp)

/-- Conjugating an idempotent matrix by an invertible matrix preserves its class in
`IdempotentMonoid R`. -/
theorem of_conj_units {ι : Type*} [Fintype ι] [DecidableEq ι] (e : Matrix ι ι R)
    (he : IsIdempotentElem e) (u : (Matrix ι ι R)ˣ) :
    of (u.val * e * u⁻¹.val) (he.isAlgebraicEquivalent_conj_units u).isIdempotentElem_left =
      of e he :=
  of_eq_of_iff.mpr (he.isAlgebraicEquivalent_conj_units u)

/-- Every diagonal matrix unit `Eᵢᵢ` represents the class of `1 ∈ M₁(R)` in `IdempotentMonoid R`. -/
theorem of_single_one_eq_of_one {ι : Type*} [Fintype ι] [DecidableEq ι] (i : ι) :
    of (single i i (1 : R)) (isIdempotentElem_single_one i) =
      of (1 : Matrix (Fin 1) (Fin 1) R) IsIdempotentElem.one :=
  of_eq_of_iff.mpr (isAlgebraicEquivalent_single_one_one i)

/-- Adding `n` copies of the `1 × 1` identity class yields the `n × n` identity class. -/
theorem nsmul_of_one (n : ℕ) :
    n • of (1 : Matrix (Fin 1) (Fin 1) R) IsIdempotentElem.one =
      of (1 : Matrix (Fin n) (Fin n) R) IsIdempotentElem.one := by
  induction n with
  | zero =>
    rw [zero_smul]
    exact (of_eq_zero_iff.mpr (Subsingleton.elim _ _)).symm
  | succ n ih =>
    rw [succ_nsmul, ih, of_add_of]
    refine of_eq_of_iff.mpr ?_
    have h1 : fromBlocks (1 : Matrix (Fin n) (Fin n) R) 0 0 (1 : Matrix (Fin 1) (Fin 1) R) =
        (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) R).reindex finSumFinEquiv.symm
          finSumFinEquiv.symm := by
      rw [fromBlocks_one]
      ext a b
      simp [Matrix.one_apply]
    rw [h1]
    exact IsIdempotentElem.one.isAlgebraicEquivalent_reindex _

/-- Over a semiring with invariant basis number, two identity matrices represent the same class in
`IdempotentMonoid R` if and only if they have the same size. -/
@[simp]
theorem of_one_eq_of_one_iff [InvariantBasisNumber R] {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] :
    of (1 : Matrix ι ι R) IsIdempotentElem.one =
      of (1 : Matrix κ κ R) IsIdempotentElem.one ↔ Fintype.card ι = Fintype.card κ :=
  of_eq_of_iff.trans isAlgebraicEquivalent_one_iff

end IdempotentMonoid

end Semiring

section DivisionRing

namespace IdempotentMonoid

variable (D : Type u) [DivisionRing D]

private theorem finrank_range_mulVecBilin_congr {ι κ : Type*} [Fintype ι] [Fintype κ]
    {e : Matrix ι ι D} {f : Matrix κ κ D} (he : IsIdempotentElem e) (hf : IsIdempotentElem f)
    (h : e.IsAlgebraicEquivalent f) :
    Module.finrank Dᵐᵒᵖ (range (e.mulVecBilin D Dᵐᵒᵖ)) =
      Module.finrank Dᵐᵒᵖ (range (f.mulVecBilin D Dᵐᵒᵖ)) := by
  obtain ⟨ψ⟩ := (isAlgebraicEquivalent_iff_nonempty_linearEquiv_range_mulVecBilin he hf).mp h
  exact ψ.finrank_eq

private noncomputable def finrankFun : IdempotentMonoid D → ℕ :=
  lift (fun _ e _ ↦ Module.finrank Dᵐᵒᵖ (range (e.mulVecBilin D Dᵐᵒᵖ)))
    fun _ _ _ _ he hg h ↦ finrank_range_mulVecBilin_congr D he hg h

private theorem finrankFun_of {ι : Type*} [Fintype ι] (e : Matrix ι ι D) (he : IsIdempotentElem e) :
    finrankFun D (of e he) = Module.finrank Dᵐᵒᵖ (range (e.mulVecBilin D Dᵐᵒᵖ)) :=
  finrank_range_mulVecBilin_congr D
    (he.isAlgebraicEquivalent_reindex (Fintype.equivFin ι)).isIdempotentElem_left he
    (he.isAlgebraicEquivalent_reindex (Fintype.equivFin ι))

/-- Right column-range dimension as an additive monoid homomorphism `IdempotentMonoid D →+ ℕ`. -/
private noncomputable def finrankHom : IdempotentMonoid D →+ ℕ where
  toFun := finrankFun D
  map_zero' :=
    (finrankFun_of D (0 : Matrix (Fin 0) (Fin 0) D) IsIdempotentElem.zero).trans
      Module.finrank_zero_of_subsingleton
  map_add' a b := by
    induction a using induction_on with | of m e he =>
    induction b using induction_on with | of n f hf =>
    rw [of_add_of, finrankFun_of, finrankFun_of, finrankFun_of]
    exact (rangeMulVecBilinFromBlocksEquiv e f).finrank_eq.trans Module.finrank_prod

/-- **Rank classification of idempotent matrices over a division ring.** Sending `[e]` to the right
`D`-dimension of its column range `e Dⁿ` is an additive monoid isomorphism
`IdempotentMonoid D ≃+ ℕ`, with inverse `n ↦ [1ₙ]`. -/
noncomputable def finrankAddEquiv : IdempotentMonoid D ≃+ ℕ where
  __ := finrankHom D
  invFun n := of (1 : Matrix (Fin n) (Fin n) D) IsIdempotentElem.one
  left_inv a := by
    induction a using induction_on with | of n e he =>
    change of (1 : Matrix (Fin (finrankFun D (of e he))) (Fin (finrankFun D (of e he))) D)
        IsIdempotentElem.one = of e he
    rw [finrankFun_of]
    set r := Module.finrank Dᵐᵒᵖ (range (e.mulVecBilin D Dᵐᵒᵖ))
    refine of_eq_of_iff.mpr ?_
    rw [isAlgebraicEquivalent_iff_nonempty_linearEquiv_range_mulVecBilin IsIdempotentElem.one he]
    refine ⟨LinearEquiv.ofFinrankEq _ _ ?_⟩
    rw [finrank_range_mulVecBilin_one D (Fin r), Fintype.card_fin]
  right_inv n :=
    (finrankFun_of D (1 : Matrix (Fin n) (Fin n) D) IsIdempotentElem.one).trans
      ((finrank_range_mulVecBilin_one D (Fin n)).trans (Fintype.card_fin n))

@[simp]
theorem finrankAddEquiv_of {ι : Type*} [Fintype ι] (e : Matrix ι ι D) (he : IsIdempotentElem e) :
    finrankAddEquiv D (of e he) = Module.finrank Dᵐᵒᵖ (range (e.mulVecBilin D Dᵐᵒᵖ)) :=
  finrankFun_of D e he

@[simp]
theorem finrankAddEquiv_symm_apply (n : ℕ) :
    (finrankAddEquiv D).symm n = of (1 : Matrix (Fin n) (Fin n) D) IsIdempotentElem.one :=
  (rfl)

/-- **Grothendieck group of idempotent matrices over a division ring.** Group completion of
`IdempotentMonoid D` is canonically isomorphic to `ℤ` via column-range dimension. -/
noncomputable def grothendieckAddGroupEquivInt :
    Algebra.GrothendieckAddGroup (IdempotentMonoid D) ≃+ ℤ :=
  let natIntLoc : (⊤ : AddSubmonoid ℕ).LocalizationMap ℤ :=
    { __ := Nat.castAddMonoidHom ℤ
      isLocalizationMap := AddSubmonoid.isLocalizationMap_top_nat_int }
  (AddLocalization.addMonoidOf (⊤ : AddSubmonoid (IdempotentMonoid D))).addEquivOfAddEquiv
    natIntLoc (AddSubmonoid.map_equiv_top (finrankAddEquiv D))

theorem grothendieckAddGroupEquivInt_of {ι : Type*} [Fintype ι] (e : Matrix ι ι D)
    (he : IsIdempotentElem e) :
    grothendieckAddGroupEquivInt D (Algebra.GrothendieckAddGroup.of (of e he)) =
      (Module.finrank Dᵐᵒᵖ (range (e.mulVecBilin D Dᵐᵒᵖ)) : ℤ) := by
  have h := (AddLocalization.addMonoidOf
    (⊤ : AddSubmonoid (IdempotentMonoid D))).addEquivOfAddEquiv_eq
    (k := { __ := Nat.castAddMonoidHom ℤ
            isLocalizationMap := AddSubmonoid.isLocalizationMap_top_nat_int })
    (AddSubmonoid.map_equiv_top (finrankAddEquiv D)) (of e he)
  exact h.trans (congrArg Nat.cast (finrankAddEquiv_of D e he))

end IdempotentMonoid

end DivisionRing

end TauCeti
