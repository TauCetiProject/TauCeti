/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dimension.DivisionRing
public import TauCeti.Algebra.Category.ModuleCat.FiniteProjective.KZero.Idempotent
public import TauCeti.LinearAlgebra.Matrix.Idempotent.Equivalence
public import TauCeti.RingTheory.Idempotents.Matrix

/-!
# Functoriality, normal forms, and rank classification of `IdempotentMonoid`

Building on `TauCeti.IdempotentMonoid` in
`TauCeti.Algebra.Category.ModuleCat.FiniteProjective.KZero.Idempotent`, this file provides:

* extensionality principles (`fun_ext`, `hom_ext`), `Unique` over a subsingleton semiring, and
  invariance of `IdempotentMonoid.mk` under reindexing, zero-block padding, unit conjugation, and
  diagonal matrix units `Eᵢᵢ`;
* `nsmul_mk_one` (`n • [1₁] = [1ₙ]`) and separation of identity classes `[1ₘ] = [1ₙ] ↔ |m| = |n|`
  under `InvariantBasisNumber`;
* functoriality along nonunital ring homomorphisms (`TauCeti.IdempotentMonoid.map`) and ring
  equivalences (`TauCeti.IdempotentMonoid.congr`);
* over a division ring `D`, the rank isomorphism `TauCeti.IdempotentMonoid.finrankAddEquiv :
  IdempotentMonoid D ≃+ ℕ` and the induced isomorphism
  `TauCeti.IdempotentMonoid.grothendieckAddGroupEquivInt :
  Algebra.GrothendieckAddGroup (IdempotentMonoid D) ≃+ ℤ`.

## References

* J. Rosenberg, *Algebraic K-Theory and Its Applications*, §1.2.
* C. A. Weibel, *The K-book*, Chapter II, §2.
* B. Blackadar, *K-Theory for Operator Algebras*, §§4.2–4.6.
-/

public section

open LinearMap Matrix MulOpposite

universe u v w

section MatrixLemmas

/-- Whenever `Rᵐᵒᵖ` satisfies the strong rank condition, the column range of `1 : Matrix m m R`
has right `R`-rank `Fintype.card m`. -/
theorem Matrix.finrank_range_mulVecBilin_one (R : Type*) [Semiring R] [StrongRankCondition Rᵐᵒᵖ]
    (m : Type*) [Fintype m] [DecidableEq m] :
    Module.finrank Rᵐᵒᵖ (range ((1 : Matrix m m R).mulVecBilin R Rᵐᵒᵖ)) = Fintype.card m :=
  (rangeMulVecBilinOneEquiv m R).finrank_eq.trans (Module.finrank_fintype_fun_eq_card Rᵐᵒᵖ)

/-- Whenever `Rᵐᵒᵖ` satisfies the strong rank condition, the column range of any diagonal matrix
unit `Eᵢᵢ` has right `R`-rank `1`. -/
theorem Matrix.finrank_range_mulVecBilin_single_one (R : Type*) [Semiring R]
    [StrongRankCondition Rᵐᵒᵖ] {m : Type*} [Fintype m] [DecidableEq m] (i : m) :
    Module.finrank Rᵐᵒᵖ (range ((single i i (1 : R)).mulVecBilin R Rᵐᵒᵖ)) = 1 :=
  (idempotentEquivalent_single_one_one (R := R) i).finrank_range_mulVecBilin_eq.trans
    (finrank_range_mulVecBilin_one R (Fin 1))

end MatrixLemmas

namespace TauCeti

section NonUnitalSemiring

namespace IdempotentMonoid

variable {R : Type u} [NonUnitalSemiring R]

/-- Equal matrices give equal classes in `IdempotentMonoid R` regardless of the idempotence
proof. -/
theorem mk_congr_matrix {ι : Type*} [Fintype ι] {e₁ e₂ : Matrix ι ι R}
    (he₁ : IsIdempotentElem e₁) (he₂ : IsIdempotentElem e₂) (h : e₁ = e₂) :
    mk e₁ he₁ = mk e₂ he₂ := by
  subst h
  rfl

/-- Two functions out of `IdempotentMonoid R` that agree on every `Fin n` representative are
equal. -/
theorem fun_ext {α : Sort*} {f g : IdempotentMonoid R → α}
    (h : ∀ (n : ℕ) (e : Matrix (Fin n) (Fin n) R) (he : IsIdempotentElem e),
      f (mk e he) = g (mk e he)) : f = g :=
  funext fun x ↦ ind h x

/-- Two additive monoid homomorphisms out of `IdempotentMonoid R` that agree on every `Fin n`
representative are equal. -/
@[ext]
theorem hom_ext {M : Type*} [AddZeroClass M] {f g : IdempotentMonoid R →+ M}
    (h : ∀ (n : ℕ) (e : Matrix (Fin n) (Fin n) R) (he : IsIdempotentElem e),
      f (mk e he) = g (mk e he)) : f = g :=
  DFunLike.coe_injective (fun_ext h)

noncomputable instance [Subsingleton R] : Unique (IdempotentMonoid R) where
  default := 0
  uniq x := by
    induction x using ind with | mk n e he =>
    exact (mk_eq_zero_iff he).mpr (Subsingleton.elim e 0)

/-- Reindexing an idempotent matrix along an index equivalence via `Matrix.submatrix` preserves its
class. This is the `simp`-normal form of `mk_reindex`, since `Matrix.reindex_apply` simplifies
`e.reindex σ σ` to `e.submatrix σ.symm σ.symm`. -/
@[simp]
theorem mk_submatrix_equiv {ι ι' : Type*} [Fintype ι] [Fintype ι'] (e : Matrix ι ι R)
    (he : IsIdempotentElem e) (σ : ι' ≃ ι) :
    mk (e.submatrix σ σ) (he.idempotentEquivalent_reindex σ.symm).isIdempotentElem_left =
      mk e he :=
  mk_eq_mk (idempotentEquivalent_submatrix he σ).symm

/-- Reindexing an idempotent matrix along an index equivalence preserves its class. Not marked
`@[simp]` because `Matrix.reindex_apply` simplifies `e.reindex σ σ` to `e.submatrix σ.symm σ.symm`,
after which `mk_submatrix_equiv` applies. -/
theorem mk_reindex {ι ι' : Type*} [Fintype ι] [Fintype ι'] (e : Matrix ι ι R)
    (he : IsIdempotentElem e) (σ : ι ≃ ι') :
    mk (e.reindex σ σ) (he.idempotentEquivalent_reindex σ).isIdempotentElem_left = mk e he :=
  mk_eq_mk (he.idempotentEquivalent_reindex σ)

/-- Padding by a lower-right zero block preserves the class in `IdempotentMonoid R`. -/
@[simp]
theorem mk_fromBlocks_zero_right {ι κ : Type*} [Fintype ι] [Fintype κ] (e : Matrix ι ι R)
    (he : IsIdempotentElem e) :
    mk (fromBlocks e 0 0 (0 : Matrix κ κ R))
      (he.fromBlocks_zero₁₂_zero₂₁ IsIdempotentElem.zero) = mk e he :=
  mk_eq_mk (he.idempotentEquivalent_fromBlocks_zero_right κ)

/-- Padding by an upper-left zero block preserves the class in `IdempotentMonoid R`. -/
@[simp]
theorem mk_fromBlocks_zero_left {ι κ : Type*} [Fintype ι] [Fintype κ] (e : Matrix κ κ R)
    (he : IsIdempotentElem e) :
    mk (fromBlocks (0 : Matrix ι ι R) 0 0 e)
      (IsIdempotentElem.zero.fromBlocks_zero₁₂_zero₂₁ he) = mk e he :=
  mk_eq_mk (he.idempotentEquivalent_fromBlocks_zero_left ι)

section Map

variable {S : Type v} {T : Type w} [NonUnitalSemiring S] [NonUnitalSemiring T]

private noncomputable def mapFun (φ : R →ₙ+* S) :
    IdempotentMonoid R → IdempotentMonoid S :=
  lift (fun e he ↦ mk (e.map φ) (he.matrix_map φ))
    fun _ _ _ _ h ↦ mk_eq_mk (h.map φ)

private theorem mapFun_mk {ι : Type*} [Fintype ι] (φ : R →ₙ+* S) (e : Matrix ι ι R)
    (he : IsIdempotentElem e) :
    mapFun φ (mk e he) = mk (e.map φ) (he.matrix_map φ) := by
  let σ := Fintype.equivFin ι
  rw [← mk_reindex e he σ, mapFun]
  exact (lift_mk (hF := fun _ _ _ _ h ↦ mk_eq_mk (h.map φ)) _ _).trans
    (mk_eq_mk ((he.idempotentEquivalent_reindex σ).map φ))

/-- **Functoriality of `IdempotentMonoid`.** Any nonunital ring homomorphism `φ : R →ₙ+* S`
induces an additive monoid homomorphism `IdempotentMonoid R →+ IdempotentMonoid S` by applying
`φ` entrywise. -/
noncomputable def map (φ : R →ₙ+* S) : IdempotentMonoid R →+ IdempotentMonoid S where
  toFun := mapFun φ
  map_zero' := by
    rw [← mk_zero (ι := Fin 0), mapFun_mk]
    exact (mk_eq_zero_iff (IsIdempotentElem.zero.matrix_map φ)).mpr
      (by ext i; exact Fin.elim0 i)
  map_add' a b := by
    induction a using ind with | mk m e he =>
    induction b using ind with | mk n f hf =>
    rw [mk_add_mk, mapFun_mk, mapFun_mk, mapFun_mk, mk_add_mk]
    refine mk_congr_matrix _ _ ?_
    ext (_ | _) (_ | _) <;> simp

@[simp]
theorem map_mk {ι : Type*} [Fintype ι] (φ : R →ₙ+* S) (e : Matrix ι ι R)
    (he : IsIdempotentElem e) :
    map φ (mk e he) = mk (e.map φ) (he.matrix_map φ) :=
  mapFun_mk φ e he

@[simp]
theorem map_id : map (NonUnitalRingHom.id R) = AddMonoidHom.id (IdempotentMonoid R) := by
  ext n e he
  rw [map_mk, AddMonoidHom.id_apply]
  exact mk_congr_matrix _ _ (by ext; simp)

theorem map_comp (φ : R →ₙ+* S) (ψ : S →ₙ+* T) :
    (map ψ).comp (map φ) = map (ψ.comp φ) := by
  ext n e he
  rw [AddMonoidHom.comp_apply, map_mk, map_mk, map_mk]
  exact mk_congr_matrix _ _ (by ext; rfl)

/-- A ring equivalence induces an additive isomorphism on `IdempotentMonoid`. -/
noncomputable def congr (e : R ≃+* S) : IdempotentMonoid R ≃+ IdempotentMonoid S where
  toFun := map e.toNonUnitalRingHom
  invFun := map e.symm.toNonUnitalRingHom
  map_add' := map_add (map e.toNonUnitalRingHom)
  left_inv x := by
    have hcomp := (map_comp e.toNonUnitalRingHom e.symm.toNonUnitalRingHom).trans
      (congrArg map (NonUnitalRingHom.ext (fun a ↦ e.symm_apply_apply a) :
        _ = NonUnitalRingHom.id R))
    exact DFunLike.congr_fun (hcomp.trans map_id) x
  right_inv y := by
    have hcomp := (map_comp e.symm.toNonUnitalRingHom e.toNonUnitalRingHom).trans
      (congrArg map (NonUnitalRingHom.ext (fun a ↦ e.apply_symm_apply a) :
        _ = NonUnitalRingHom.id S))
    exact DFunLike.congr_fun (hcomp.trans map_id) y

@[simp]
theorem congr_mk {ι : Type*} [Fintype ι] (φ : R ≃+* S) (e : Matrix ι ι R)
    (he : IsIdempotentElem e) :
    congr φ (mk e he) = mk (e.map φ.toNonUnitalRingHom) (he.matrix_map φ.toNonUnitalRingHom) :=
  map_mk φ.toNonUnitalRingHom e he

@[simp]
theorem congr_symm_mk {ι : Type*} [Fintype ι] (φ : R ≃+* S) (e : Matrix ι ι S)
    (he : IsIdempotentElem e) :
    (congr φ).symm (mk e he) =
      mk (e.map φ.symm.toNonUnitalRingHom) (he.matrix_map φ.symm.toNonUnitalRingHom) :=
  map_mk φ.symm.toNonUnitalRingHom e he

end Map

end IdempotentMonoid

end NonUnitalSemiring

section Semiring

namespace IdempotentMonoid

variable {R : Type u} [Semiring R]

/-- Conjugating an idempotent matrix by an invertible matrix preserves its class in
`IdempotentMonoid R`. -/
@[simp]
theorem mk_conj_units {ι : Type*} [Fintype ι] [DecidableEq ι] (e : Matrix ι ι R)
    (he : IsIdempotentElem e) (u : (Matrix ι ι R)ˣ) :
    mk (u.val * e * u⁻¹.val) (idempotentEquivalent_conj he u).isIdempotentElem_right =
      mk e he :=
  (mk_eq_mk (idempotentEquivalent_conj he u)).symm

/-- Every diagonal matrix unit `Eᵢᵢ` represents the class of `1 ∈ M₁(R)` in `IdempotentMonoid R`. -/
@[simp]
theorem mk_single_one_eq_mk_one {ι : Type*} [Fintype ι] [DecidableEq ι] (i : ι) :
    mk (single i i (1 : R)) (isIdempotentElem_single_one i) =
      mk (1 : Matrix (Fin 1) (Fin 1) R) IsIdempotentElem.one :=
  mk_eq_mk (idempotentEquivalent_single_one_one i)

/-- Adding `n` copies of the `1 × 1` identity class yields the `n × n` identity class. -/
theorem nsmul_mk_one (n : ℕ) :
    n • mk (1 : Matrix (Fin 1) (Fin 1) R) IsIdempotentElem.one =
      mk (1 : Matrix (Fin n) (Fin n) R) IsIdempotentElem.one := by
  induction n with
  | zero =>
    rw [zero_smul]
    exact ((mk_eq_zero_iff IsIdempotentElem.one).mpr (Subsingleton.elim _ _)).symm
  | succ n ih =>
    rw [succ_nsmul, ih, mk_add_mk]
    refine mk_eq_mk ?_
    have h1 : fromBlocks (1 : Matrix (Fin n) (Fin n) R) 0 0 (1 : Matrix (Fin 1) (Fin 1) R) =
        (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) R).reindex finSumFinEquiv.symm
          finSumFinEquiv.symm := by
      rw [fromBlocks_one]
      ext a b
      simp [Matrix.one_apply]
    rw [h1]
    exact IsIdempotentElem.one.idempotentEquivalent_reindex _

/-- Over a semiring with invariant basis number, two identity matrices represent the same class in
`IdempotentMonoid R` if and only if they have the same size. -/
theorem mk_one_eq_mk_one_iff [InvariantBasisNumber R] {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] :
    mk (1 : Matrix ι ι R) IsIdempotentElem.one =
      mk (1 : Matrix κ κ R) IsIdempotentElem.one ↔ Fintype.card ι = Fintype.card κ :=
  (mk_eq_mk_iff _ _).trans idempotentEquivalent_one_iff

end IdempotentMonoid

end Semiring

section DivisionRing

namespace IdempotentMonoid

variable (D : Type u) [DivisionRing D]

private noncomputable def finrankFun : IdempotentMonoid D → ℕ :=
  lift (fun e _ ↦ Module.finrank Dᵐᵒᵖ (range (e.mulVecBilin D Dᵐᵒᵖ)))
    fun _ _ _ _ h ↦ h.finrank_range_mulVecBilin_eq

private theorem finrankFun_mk {ι : Type*} [Fintype ι] (e : Matrix ι ι D)
    (he : IsIdempotentElem e) :
    finrankFun D (mk e he) = Module.finrank Dᵐᵒᵖ (range (e.mulVecBilin D Dᵐᵒᵖ)) := by
  let σ := Fintype.equivFin ι
  rw [← mk_reindex e he σ, finrankFun]
  exact (lift_mk (hF := fun _ _ _ _ h ↦ h.finrank_range_mulVecBilin_eq) _ _).trans
    (he.idempotentEquivalent_reindex σ).finrank_range_mulVecBilin_eq

/-- Right column-range dimension as an additive monoid homomorphism `IdempotentMonoid D →+ ℕ`. -/
private noncomputable def finrankHom : IdempotentMonoid D →+ ℕ where
  toFun := finrankFun D
  map_zero' :=
    (finrankFun_mk D (0 : Matrix (Fin 0) (Fin 0) D) IsIdempotentElem.zero).trans
      Module.finrank_zero_of_subsingleton
  map_add' a b := by
    induction a using ind with | mk m e he =>
    induction b using ind with | mk n f hf =>
    rw [mk_add_mk, finrankFun_mk, finrankFun_mk, finrankFun_mk]
    exact (rangeMulVecBilinFromBlocksEquiv e f).finrank_eq.trans Module.finrank_prod

/-- **Rank classification of idempotent matrices over a division ring.** Sending `[e]` to the right
`D`-dimension of its column range `e Dⁿ` is an additive monoid isomorphism
`IdempotentMonoid D ≃+ ℕ`, with inverse `n ↦ [1ₙ]`. -/
noncomputable def finrankAddEquiv : IdempotentMonoid D ≃+ ℕ where
  toFun := finrankFun D
  invFun n := mk (1 : Matrix (Fin n) (Fin n) D) IsIdempotentElem.one
  map_add' := (finrankHom D).map_add
  left_inv a := by
    induction a using ind with | mk n e he =>
    rw [finrankFun_mk]
    set r := Module.finrank Dᵐᵒᵖ (range (e.mulVecBilin D Dᵐᵒᵖ))
    refine (mk_eq_mk_iff _ _).mpr ?_
    rw [← nonempty_linearEquiv_range_mulVecBilin_iff IsIdempotentElem.one he]
    refine ⟨LinearEquiv.ofFinrankEq _ _ ?_⟩
    rw [finrank_range_mulVecBilin_one D (Fin r), Fintype.card_fin]
  right_inv n :=
    (finrankFun_mk D (1 : Matrix (Fin n) (Fin n) D) IsIdempotentElem.one).trans
      ((finrank_range_mulVecBilin_one D (Fin n)).trans (Fintype.card_fin n))

@[simp]
theorem finrankAddEquiv_mk {ι : Type*} [Fintype ι] (e : Matrix ι ι D) (he : IsIdempotentElem e) :
    finrankAddEquiv D (mk e he) = Module.finrank Dᵐᵒᵖ (range (e.mulVecBilin D Dᵐᵒᵖ)) :=
  finrankFun_mk D e he

@[simp]
theorem finrankAddEquiv_symm_apply (n : ℕ) :
    (finrankAddEquiv D).symm n = mk (1 : Matrix (Fin n) (Fin n) D) IsIdempotentElem.one :=
  (rfl)

/-- **Grothendieck group of idempotent matrices over a division ring.** Group completion of
`IdempotentMonoid D` is canonically isomorphic to `ℤ` via column-range dimension. -/
noncomputable def grothendieckAddGroupEquivInt :
    _root_.Algebra.GrothendieckAddGroup (IdempotentMonoid D) ≃+ ℤ :=
  let natIntLoc : (⊤ : AddSubmonoid ℕ).LocalizationMap ℤ :=
    { __ := Nat.castAddMonoidHom ℤ
      isLocalizationMap := AddSubmonoid.isLocalizationMap_top_nat_int }
  (AddLocalization.addMonoidOf (⊤ : AddSubmonoid (IdempotentMonoid D))).addEquivOfAddEquiv
    natIntLoc (AddSubmonoid.map_equiv_top (finrankAddEquiv D))

theorem grothendieckAddGroupEquivInt_mk {ι : Type*} [Fintype ι] (e : Matrix ι ι D)
    (he : IsIdempotentElem e) :
    grothendieckAddGroupEquivInt D (_root_.Algebra.GrothendieckAddGroup.of (mk e he)) =
      (Module.finrank Dᵐᵒᵖ (range (e.mulVecBilin D Dᵐᵒᵖ)) : ℤ) := by
  have h := (AddLocalization.addMonoidOf
    (⊤ : AddSubmonoid (IdempotentMonoid D))).addEquivOfAddEquiv_eq
    (k := { __ := Nat.castAddMonoidHom ℤ
            isLocalizationMap := AddSubmonoid.isLocalizationMap_top_nat_int })
    (AddSubmonoid.map_equiv_top (finrankAddEquiv D)) (mk e he)
  exact h.trans (congrArg Nat.cast (finrankAddEquiv_mk D e he))

end IdempotentMonoid

end DivisionRing

end TauCeti
