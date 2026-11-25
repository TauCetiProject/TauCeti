/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.MonoidLocalization.GrothendieckGroup
public import Mathlib.LinearAlgebra.Dimension.DivisionRing
public import TauCeti.LinearAlgebra.Matrix.Idempotent.Equivalence
public import TauCeti.RingTheory.Idempotents.Matrix

import TauCeti.RingTheory.GrothendieckRing

/-!
# The idempotent monoid `V(A)`

For a nonunital semiring `A`, the *idempotent monoid* `V(A)` (`TauCeti.IdempotentMonoid A`) is
the set of idempotent square matrices over `A`, of all sizes, modulo equivalence of idempotents
(`Matrix.IdempotentEquivalent`). Block sum `e ⊕ f = Matrix.fromBlocks e 0 0 f` makes it a
commutative monoid with zero the empty matrix. No cancellation is assumed.

## Main definitions and results

* `TauCeti.IdempotentMonoid` with `mk`, `mk_eq_mk_iff`, `ind`, `lift`, `hom_ext`,
  `Unique` over subsingletons, `nsmul_mk_one`, and `mk_one_eq_mk_one_iff` under
  `InvariantBasisNumber`.
* Functoriality (`map`, `congr`), transposition over the opposite ring (`opEquiv`), the ring
  group-completion normal form `exists_of_mk_sub_of_mk_one_eq`, and the division-ring rank
  isomorphisms `finrankAddEquiv : IdempotentMonoid D ≃+ ℕ` and `grothendieckAddGroupEquivInt`.

## References

* J. Rosenberg, *Algebraic K-Theory and Its Applications*, §1.2.
* C. A. Weibel, *The K-book*, Chapter II, §2.
* B. Blackadar, *K-Theory for Operator Algebras*, §§4.2–4.6.
-/

public section

open LinearMap Matrix MulOpposite

universe u v w

namespace TauCeti

section NonUnitalSemiring

variable (A : Type u) [NonUnitalSemiring A]

/-- Equivalence of idempotents (`Matrix.IdempotentEquivalent`), on idempotent square matrices of
every size `n`. -/
private def idempotentSetoid :
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
private noncomputable abbrev toFin (e : Matrix ι ι A) :
    Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) A :=
  e.submatrix (Fintype.equivFin ι).symm (Fintype.equivFin ι).symm

/-- The class in `V(A)` of an idempotent square matrix `e` indexed by a finite type. -/
noncomputable def mk (e : Matrix ι ι A) (he : IsIdempotentElem e) : IdempotentMonoid A :=
  Quotient.mk _ ⟨_, toFin e, (idempotentEquivalent_submatrix he _).isIdempotentElem_right⟩

/-- **Equality in `V(A)`.** Two idempotent matrices have the same class exactly when they are
equivalent idempotents. -/
@[simp]
theorem mk_eq_mk_iff {e : Matrix ι ι A} {f : Matrix κ κ A} (he : IsIdempotentElem e)
    (hf : IsIdempotentElem f) : mk e he = mk f hf ↔ IdempotentEquivalent e f := by
  refine Quotient.eq.trans ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · exact (idempotentEquivalent_submatrix he _).trans
      (h.trans (idempotentEquivalent_submatrix hf _).symm)
  · exact (idempotentEquivalent_submatrix he _).symm.trans
      (h.trans (idempotentEquivalent_submatrix hf _))

/-- Equivalent idempotents have the same class in `V(A)`. -/
theorem mk_eq_mk {e : Matrix ι ι A} {f : Matrix κ κ A} (h : IdempotentEquivalent e f) :
    mk e h.isIdempotentElem_left = mk f h.isIdempotentElem_right :=
  (mk_eq_mk_iff _ _).2 h

private theorem quotient_mk_eq_mk {n : ℕ} (e : Matrix (Fin n) (Fin n) A)
    (he : IsIdempotentElem e) : Quotient.mk (idempotentSetoid A) ⟨n, e, he⟩ = mk e he :=
  Quotient.sound (idempotentEquivalent_submatrix he _)

/-- Induction on `V(A)`: every element is the class of an idempotent matrix indexed by `Fin n`. -/
@[elab_as_elim]
theorem ind {motive : IdempotentMonoid A → Prop}
    (mk : ∀ (n : ℕ) (e : Matrix (Fin n) (Fin n) A) (he : IsIdempotentElem e), motive (mk e he))
    (x : IdempotentMonoid A) : motive x :=
  Quotient.ind (fun ⟨n, e, he⟩ ↦ quotient_mk_eq_mk e he ▸ mk n e he) x

/-- **The eliminator of `V(A)`.** A function on idempotent square matrices over `A` that takes
equal values on equivalent idempotents descends to `V(A)`; see
`TauCeti.IdempotentMonoid.lift_mk` and `TauCeti.IdempotentMonoid.lift_mk_eq`. -/
def lift {β : Sort*} (F : ∀ {n : ℕ} (e : Matrix (Fin n) (Fin n) A), IsIdempotentElem e → β)
    (hF : ∀ {n m : ℕ} (e : Matrix (Fin n) (Fin n) A) (f : Matrix (Fin m) (Fin m) A)
      (he : IsIdempotentElem e) (hf : IsIdempotentElem f), IdempotentEquivalent e f →
        F e he = F f hf) :
    IdempotentMonoid A → β :=
  Quotient.lift (s := idempotentSetoid A) (fun e ↦ F e.snd.val e.snd.property)
    fun _ _ h ↦ hF _ _ _ _ h

/-- `TauCeti.IdempotentMonoid.lift` computes `F` on the class of an idempotent matrix indexed by
`Fin n`. For arbitrary finite index types, see `TauCeti.IdempotentMonoid.lift_mk_eq`. -/
@[simp]
theorem lift_mk {β : Sort*} {F : ∀ {n : ℕ} (e : Matrix (Fin n) (Fin n) A), IsIdempotentElem e → β}
    {hF : ∀ {n m : ℕ} (e : Matrix (Fin n) (Fin n) A) (f : Matrix (Fin m) (Fin m) A)
      (he : IsIdempotentElem e) (hf : IsIdempotentElem f),
      IdempotentEquivalent e f → F e he = F f hf}
    {n : ℕ} (e : Matrix (Fin n) (Fin n) A) (he : IsIdempotentElem e) :
    lift F hF (mk e he) = F e he := by
  rw [← quotient_mk_eq_mk]; rfl

/-- Uniqueness of `TauCeti.IdempotentMonoid.lift`: any function on `IdempotentMonoid A` that
agrees with `F` on every `Fin n` representative equals `lift F hF`. -/
theorem lift_unique {β : Sort*}
    {F : ∀ {n : ℕ} (e : Matrix (Fin n) (Fin n) A), IsIdempotentElem e → β}
    {hF : ∀ {n m : ℕ} (e : Matrix (Fin n) (Fin n) A) (f : Matrix (Fin m) (Fin m) A)
      (he : IsIdempotentElem e) (hf : IsIdempotentElem f),
      IdempotentEquivalent e f → F e he = F f hf}
    {g : IdempotentMonoid A → β}
    (hg : ∀ (n : ℕ) (e : Matrix (Fin n) (Fin n) A) (he : IsIdempotentElem e),
      g (mk e he) = F e he) :
    g = lift F hF :=
  funext fun x ↦ ind (fun n e he ↦ (hg n e he).trans (lift_mk e he).symm) x

/-- `TauCeti.IdempotentMonoid.lift` computes `F` on `mk e he` for any finite index type `ι` via
`e` relabelled along the chosen `Fintype.equivFin ι`; the value of `lift` is independent of the
representative because `F` respects equivalence of idempotents. -/
theorem lift_mk_eq {β : Sort*}
    {F : ∀ {n : ℕ} (e : Matrix (Fin n) (Fin n) A), IsIdempotentElem e → β}
    {hF : ∀ {n m : ℕ} (e : Matrix (Fin n) (Fin n) A) (f : Matrix (Fin m) (Fin m) A)
      (he : IsIdempotentElem e) (hf : IsIdempotentElem f),
      IdempotentEquivalent e f → F e he = F f hf}
    (e : Matrix ι ι A) (he : IsIdempotentElem e) {b : β}
    (hb : F (e.submatrix (Fintype.equivFin ι).symm (Fintype.equivFin ι).symm)
      (idempotentEquivalent_submatrix he (Fintype.equivFin ι).symm).isIdempotentElem_right = b) :
    lift F hF (mk e he) = b :=
  hb

/-- The zero of `V(A)` is the class of the empty matrix. -/
noncomputable instance : Zero (IdempotentMonoid A) := ⟨mk (0 : Matrix (Fin 0) (Fin 0) A) .zero⟩

/-- Every zero matrix has the class `0` in `V(A)`. -/
@[simp]
theorem mk_zero : mk (0 : Matrix ι ι A) .zero = 0 :=
  mk_eq_mk (idempotentEquivalent_zero_zero ι (Fin 0))

/-- Only the zero matrix has the class `0` in `V(A)`. -/
@[simp]
theorem mk_eq_zero_iff {e : Matrix ι ι A} (he : IsIdempotentElem e) : mk e he = 0 ↔ e = 0 :=
  (mk_eq_mk_iff he .zero).trans idempotentEquivalent_zero_iff

/-- The addition of `V(A)` is the block sum of idempotent matrices. -/
@[no_expose] noncomputable instance : Add (IdempotentMonoid A) where
  add := Quotient.lift₂ (s₁ := idempotentSetoid A) (s₂ := idempotentSetoid A)
    (fun e f ↦ mk (fromBlocks e.snd.val 0 0 f.snd.val)
      (e.snd.property.fromBlocks_zero₁₂_zero₂₁ f.snd.property))
    fun _ _ _ _ h h' ↦ mk_eq_mk (IdempotentEquivalent.fromBlocks h h')

/-- **Addition in `V(A)` is block sum.** -/
@[simp]
theorem mk_add_mk {e : Matrix ι ι A} {f : Matrix κ κ A} (he : IsIdempotentElem e)
    (hf : IsIdempotentElem f) :
    mk e he + mk f hf = mk (fromBlocks e 0 0 f) (he.fromBlocks_zero₁₂_zero₂₁ hf) :=
  mk_eq_mk ((idempotentEquivalent_submatrix he _).symm.fromBlocks
    (idempotentEquivalent_submatrix hf _).symm)

private theorem idempotentEquivalent_of_submatrix_eq {μ : Type*} [Fintype μ] {e : Matrix ι ι A}
    (he : IsIdempotentElem e) {f : Matrix μ μ A} (σ : μ ≃ ι) (h : e.submatrix σ σ = f) :
    IdempotentEquivalent e f :=
  h ▸ idempotentEquivalent_submatrix he σ

noncomputable instance : AddCommMonoid (IdempotentMonoid A) where
  add_assoc x y z := by
    induction x using ind with | mk n e he =>
    induction y using ind with | mk m f hf =>
    induction z using ind with | mk k g hg =>
    simp only [mk_add_mk]
    exact mk_eq_mk <| idempotentEquivalent_of_submatrix_eq
      ((he.fromBlocks_zero₁₂_zero₂₁ hf).fromBlocks_zero₁₂_zero₂₁ hg) (Equiv.sumAssoc _ _ _).symm
      (by ext (i | i | i) (j | j | j) <;> simp)
  zero_add x := by
    induction x using ind with | mk n e he =>
    rw [← mk_zero (ι := Fin 0), mk_add_mk]
    exact mk_eq_mk (he.idempotentEquivalent_fromBlocks_zero_left (Fin 0))
  add_zero x := by
    induction x using ind with | mk n e he =>
    rw [← mk_zero (ι := Fin 0), mk_add_mk]
    exact mk_eq_mk (he.idempotentEquivalent_fromBlocks_zero_right (Fin 0))
  add_comm x y := by
    induction x using ind with | mk n e he =>
    induction y using ind with | mk m f hf =>
    rw [mk_add_mk, mk_add_mk]
    exact mk_eq_mk <| idempotentEquivalent_of_submatrix_eq (he.fromBlocks_zero₁₂_zero₂₁ hf)
      (Equiv.sumComm _ _) (by simp)
  nsmul := nsmulRec

/-- Equal matrices give equal classes in `IdempotentMonoid A` regardless of the idempotence
proof. -/
theorem mk_congr_matrix {e₁ e₂ : Matrix ι ι A}
    (he₁ : IsIdempotentElem e₁) (he₂ : IsIdempotentElem e₂) (h : e₁ = e₂) :
    mk e₁ he₁ = mk e₂ he₂ := by
  subst h; rfl

/-- Two additive monoid homomorphisms out of `IdempotentMonoid A` that agree on every `Fin n`
representative are equal. -/
@[ext]
theorem hom_ext {M : Type*} [AddZeroClass M] {f g : IdempotentMonoid A →+ M}
    (h : ∀ (n : ℕ) (e : Matrix (Fin n) (Fin n) A) (he : IsIdempotentElem e),
      f (mk e he) = g (mk e he)) : f = g :=
  DFunLike.coe_injective (funext fun x ↦ ind h x)

noncomputable instance [Subsingleton A] : Unique (IdempotentMonoid A) where
  default := 0
  uniq x := by
    induction x using ind with | mk n e he => exact (mk_eq_zero_iff he).mpr (Subsingleton.elim e 0)

/-- Reindexing an idempotent matrix along an index equivalence via `Matrix.submatrix` preserves its
class. (Since `Matrix.reindex_apply` simplifies `e.reindex σ σ` to `e.submatrix σ.symm σ.symm`,
`simp [he]` also simplifies `mk (e.reindex σ σ) _`.) -/
@[simp]
theorem mk_submatrix_equiv {ι ι' : Type*} [Fintype ι] [Fintype ι'] (e : Matrix ι ι A)
    (he : IsIdempotentElem e) (σ : ι' ≃ ι) :
    mk (e.submatrix σ σ) (idempotentEquivalent_submatrix he σ).isIdempotentElem_right =
      mk e he :=
  mk_eq_mk (idempotentEquivalent_submatrix he σ).symm

/-- Padding by a lower-right zero block preserves the class in `IdempotentMonoid A`. -/
@[simp]
theorem mk_fromBlocks_zero_right {ι κ : Type*} [Fintype ι] [Fintype κ] (e : Matrix ι ι A)
    (he : IsIdempotentElem e) :
    mk (fromBlocks e 0 0 (0 : Matrix κ κ A))
      (he.fromBlocks_zero₁₂_zero₂₁ IsIdempotentElem.zero) = mk e he :=
  mk_eq_mk (he.idempotentEquivalent_fromBlocks_zero_right κ)

/-- Padding by an upper-left zero block preserves the class in `IdempotentMonoid A`. -/
@[simp]
theorem mk_fromBlocks_zero_left {ι κ : Type*} [Fintype ι] [Fintype κ] (e : Matrix κ κ A)
    (he : IsIdempotentElem e) :
    mk (fromBlocks (0 : Matrix ι ι A) 0 0 e)
      (IsIdempotentElem.zero.fromBlocks_zero₁₂_zero₂₁ he) = mk e he :=
  mk_eq_mk (he.idempotentEquivalent_fromBlocks_zero_left ι)

section Map

variable {R : Type u} {S : Type v} {T : Type w}
  [NonUnitalSemiring R] [NonUnitalSemiring S] [NonUnitalSemiring T]

private noncomputable def mapFun (φ : R →ₙ+* S) : IdempotentMonoid R → IdempotentMonoid S :=
  lift (fun e he ↦ mk (e.map φ) (he.matrix_map φ)) fun _ _ _ _ h ↦ mk_eq_mk (h.map φ)

private theorem mapFun_mk {ι : Type*} [Fintype ι] (φ : R →ₙ+* S) (e : Matrix ι ι R)
    (he : IsIdempotentElem e) :
    mapFun φ (mk e he) = mk (e.map φ) (he.matrix_map φ) :=
  lift_mk_eq (hF := fun _ _ _ _ h ↦ mk_eq_mk (h.map φ)) e he
    (mk_eq_mk ((idempotentEquivalent_submatrix he _).symm.map φ))

/-- **Functoriality of `IdempotentMonoid`.** Any nonunital ring homomorphism `φ : R →ₙ+* S`
induces an additive monoid homomorphism `IdempotentMonoid R →+ IdempotentMonoid S` by applying
`φ` entrywise. -/
noncomputable def map (φ : R →ₙ+* S) : IdempotentMonoid R →+ IdempotentMonoid S where
  toFun := mapFun φ
  map_zero' := by
    rw [← mk_zero (ι := Fin 0), mapFun_mk]
    exact (mk_eq_zero_iff (IsIdempotentElem.zero.matrix_map φ)).mpr (Matrix.map_zero φ (map_zero φ))
  map_add' a b := by
    induction a using ind with | mk m e he =>
    induction b using ind with | mk n f hf =>
    rw [mk_add_mk, mapFun_mk, mapFun_mk, mapFun_mk, mk_add_mk]
    exact mk_congr_matrix _ _
      (by rw [fromBlocks_map, Matrix.map_zero φ (map_zero φ), Matrix.map_zero φ (map_zero φ)])

@[simp]
theorem map_mk {ι : Type*} [Fintype ι] (φ : R →ₙ+* S) (e : Matrix ι ι R)
    (he : IsIdempotentElem e) : map φ (mk e he) = mk (e.map φ) (he.matrix_map φ) :=
  mapFun_mk φ e he

@[simp]
theorem map_id : map (NonUnitalRingHom.id R) = AddMonoidHom.id (IdempotentMonoid R) := by
  ext n e he; rw [map_mk, AddMonoidHom.id_apply]; exact mk_congr_matrix _ _ (by ext; simp)

theorem map_comp (φ : R →ₙ+* S) (ψ : S →ₙ+* T) : map (ψ.comp φ) = (map ψ).comp (map φ) := by
  ext n e he; rw [AddMonoidHom.comp_apply, map_mk, map_mk, map_mk]
  exact mk_congr_matrix _ _ (by ext; rfl)

/-- A ring equivalence induces an additive isomorphism on `IdempotentMonoid`. -/
noncomputable def congr (e : R ≃+* S) : IdempotentMonoid R ≃+ IdempotentMonoid S where
  toFun := map e.toNonUnitalRingHom
  invFun := map e.symm.toNonUnitalRingHom
  map_add' := map_add (map e.toNonUnitalRingHom)
  left_inv x := DFunLike.congr_fun ((map_comp _ _).symm.trans
    ((congrArg map (NonUnitalRingHom.ext e.symm_apply_apply)).trans map_id)) x
  right_inv y := DFunLike.congr_fun ((map_comp _ _).symm.trans
    ((congrArg map (NonUnitalRingHom.ext e.apply_symm_apply)).trans map_id)) y

/-- Pointwise evaluation of `congr` as `map e.toNonUnitalRingHom`. -/
theorem congr_apply (e : R ≃+* S) (x : IdempotentMonoid R) :
    congr e x = map e.toNonUnitalRingHom x := (rfl)

/-- Pointwise evaluation of `(congr e).symm` as `map e.symm.toNonUnitalRingHom`. -/
theorem congr_symm_apply (e : R ≃+* S) (y : IdempotentMonoid S) :
    (congr e).symm y = map e.symm.toNonUnitalRingHom y := (rfl)

@[simp]
theorem coe_congr (e : R ≃+* S) :
    (congr e : IdempotentMonoid R →+ IdempotentMonoid S) = map e.toNonUnitalRingHom :=
  AddMonoidHom.ext fun x ↦ congr_apply e x

@[simp]
theorem coe_congr_symm (e : R ≃+* S) :
    ((congr e).symm : IdempotentMonoid S →+ IdempotentMonoid R) = map e.symm.toNonUnitalRingHom :=
  AddMonoidHom.ext fun y ↦ congr_symm_apply e y

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

section Opposite

private noncomputable def opFun (R : Type u) [NonUnitalSemiring R] :
    IdempotentMonoid R → IdempotentMonoid Rᵐᵒᵖ :=
  lift (fun e he ↦ mk (eᵀ.map MulOpposite.op) he.matrix_transpose_map_op)
    fun _ _ _ _ h ↦ mk_eq_mk (IdempotentEquivalent.transpose_map_op h)

private noncomputable def unopFun (R : Type u) [NonUnitalSemiring R] :
    IdempotentMonoid Rᵐᵒᵖ → IdempotentMonoid R :=
  lift (fun e he ↦ mk (eᵀ.map MulOpposite.unop) he.matrix_transpose_map_unop)
    fun _ _ _ _ h ↦ mk_eq_mk (IdempotentEquivalent.transpose_map_unop h)

private theorem opFun_mk {R : Type u} [NonUnitalSemiring R] {e : Matrix ι ι R}
    (he : IsIdempotentElem e) :
    opFun R (mk e he) = mk (eᵀ.map MulOpposite.op) he.matrix_transpose_map_op :=
  lift_mk_eq (hF := fun _ _ _ _ h ↦ mk_eq_mk (IdempotentEquivalent.transpose_map_op h)) e he
    (mk_eq_mk (idempotentEquivalent_submatrix he _).symm.transpose_map_op)

private theorem unopFun_mk {R : Type u} [NonUnitalSemiring R] {e : Matrix ι ι Rᵐᵒᵖ}
    (he : IsIdempotentElem e) :
    unopFun R (mk e he) = mk (eᵀ.map MulOpposite.unop) he.matrix_transpose_map_unop :=
  lift_mk_eq (hF := fun _ _ _ _ h ↦ mk_eq_mk (IdempotentEquivalent.transpose_map_unop h)) e he
    (mk_eq_mk (idempotentEquivalent_submatrix he _).symm.transpose_map_unop)

variable (R : Type u) [NonUnitalSemiring R]

/-- **Transposition over the opposite ring.** The isomorphism `V(R) ≃ V(Rᵐᵒᵖ)` sending `[e]` to
`[eᵀ]` over `Rᵐᵒᵖ`, turning the column action of `e` into the row action of `eᵀ` over `Rᵐᵒᵖ`. -/
noncomputable def opEquiv : IdempotentMonoid R ≃+ IdempotentMonoid Rᵐᵒᵖ where
  toFun := opFun R
  invFun := unopFun R
  left_inv x := by
    induction x using ind with | mk n e he =>
    rw [opFun_mk, unopFun_mk]; exact mk_congr_matrix _ _ (transpose_map_op_transpose_map_unop e)
  right_inv x := by
    induction x using ind with | mk n e he =>
    rw [unopFun_mk, opFun_mk]; exact mk_congr_matrix _ _ (transpose_map_unop_transpose_map_op e)
  map_add' x y := by
    induction x using ind with | mk n e he =>
    induction y using ind with | mk m f hf =>
    rw [mk_add_mk, opFun_mk, opFun_mk, opFun_mk, mk_add_mk]
    exact mk_congr_matrix _ _ (by simp [fromBlocks_transpose, fromBlocks_map])

variable {R} in
/-- `opEquiv` sends `[e]` to `[eᵀ]` with entries in `Rᵐᵒᵖ`. -/
@[simp]
theorem opEquiv_mk {e : Matrix ι ι R} (he : IsIdempotentElem e) :
    opEquiv R (mk e he) = mk (eᵀ.map MulOpposite.op) he.matrix_transpose_map_op :=
  opFun_mk he

variable {R} in
/-- `(opEquiv R).symm` sends `[e]` over `Rᵐᵒᵖ` to `[eᵀ]` with entries in `R`. -/
@[simp]
theorem opEquiv_symm_mk {e : Matrix ι ι Rᵐᵒᵖ} (he : IsIdempotentElem e) :
    (opEquiv R).symm (mk e he) = mk (eᵀ.map MulOpposite.unop) he.matrix_transpose_map_unop :=
  unopFun_mk he

end Opposite

section Semiring

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
        (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) R).submatrix finSumFinEquiv finSumFinEquiv := by
      rw [fromBlocks_one]; ext a b; simp [Matrix.one_apply]
    rw [h1]; exact (idempotentEquivalent_submatrix IsIdempotentElem.one _).symm

/-- Over a semiring with invariant basis number, `[1ₘ] = [1ₙ]` iff `|m| = |n|`. -/
theorem mk_one_eq_mk_one_iff [InvariantBasisNumber R] {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] :
    mk (1 : Matrix ι ι R) IsIdempotentElem.one =
      mk (1 : Matrix κ κ R) IsIdempotentElem.one ↔ Fintype.card ι = Fintype.card κ :=
  (mk_eq_mk_iff _ _).trans idempotentEquivalent_one_iff

end Semiring

section Ring

variable {R : Type u} [Ring R]

/-- **Every element of the group completion of `V(R)` is `[e] - [1ₘ]`.** -/
theorem exists_of_mk_sub_of_mk_one_eq
    (y : _root_.Algebra.GrothendieckAddGroup (IdempotentMonoid R)) :
    ∃ (n : ℕ) (e : Matrix (Fin n) (Fin n) R) (he : IsIdempotentElem e) (m : ℕ),
      _root_.Algebra.GrothendieckAddGroup.of (mk e he) -
        _root_.Algebra.GrothendieckAddGroup.of (mk (1 : Matrix (Fin m) (Fin m) R) .one) = y := by
  obtain ⟨a, b, rfl⟩ := _root_.Algebra.GrothendieckAddGroup.exists_eq_sub_of y
  induction a using ind with | mk n e he =>
  induction b using ind with | mk m f hf =>
  have hE := idempotentEquivalent_submatrix (he.fromBlocks_zero₁₂_zero₂₁ hf.one_sub)
    finSumFinEquiv.symm
  refine ⟨n + m, reindex finSumFinEquiv finSumFinEquiv (fromBlocks e 0 0 (1 - f)),
    hE.isIdempotentElem_right, m, ?_⟩
  have h₁ : mk (reindex finSumFinEquiv finSumFinEquiv (fromBlocks e 0 0 (1 - f)))
      hE.isIdempotentElem_right = mk e he + mk (1 - f) hf.one_sub := by
    rw [mk_add_mk]; exact mk_eq_mk hE.symm
  have h₂ : mk (1 : Matrix (Fin m) (Fin m) R) .one = mk f hf + mk (1 - f) hf.one_sub := by
    rw [mk_add_mk]; exact mk_eq_mk (idempotentEquivalent_fromBlocks_one_sub hf).symm
  rw [h₁, h₂, map_add, map_add, add_sub_add_right_eq_sub]

end Ring

section DivisionRing

variable (D : Type u) [DivisionRing D]

private noncomputable def finrankFun : IdempotentMonoid D → ℕ :=
  lift (fun e _ ↦ Module.finrank Dᵐᵒᵖ (range (e.mulVecBilin D Dᵐᵒᵖ)))
    fun _ _ _ _ h ↦ h.finrank_range_mulVecBilin_eq

private theorem finrankFun_mk {ι : Type*} [Fintype ι] (e : Matrix ι ι D)
    (he : IsIdempotentElem e) :
    finrankFun D (mk e he) = Module.finrank Dᵐᵒᵖ (range (e.mulVecBilin D Dᵐᵒᵖ)) :=
  lift_mk_eq (hF := fun _ _ _ _ h ↦ h.finrank_range_mulVecBilin_eq) e he
    (idempotentEquivalent_submatrix he _).symm.finrank_range_mulVecBilin_eq

/-- **Rank classification of idempotent matrices over a division ring.** Sending `[e]` to the
right `D`-dimension of `e Dⁿ` gives `IdempotentMonoid D ≃+ ℕ` with inverse `n ↦ [1ₙ]`. -/
noncomputable def finrankAddEquiv : IdempotentMonoid D ≃+ ℕ where
  toFun := finrankFun D
  invFun n := mk (1 : Matrix (Fin n) (Fin n) D) IsIdempotentElem.one
  map_add' a b := by
    induction a using ind with | mk m e he =>
    induction b using ind with | mk n f hf =>
    rw [mk_add_mk, finrankFun_mk, finrankFun_mk, finrankFun_mk]
    exact (rangeMulVecBilinFromBlocksEquiv e f).finrank_eq.trans Module.finrank_prod
  left_inv a := by
    induction a using ind with | mk n e he =>
    rw [finrankFun_mk, mk_eq_mk_iff, ← nonempty_linearEquiv_range_mulVecBilin_iff .one he]
    exact ⟨LinearEquiv.ofFinrankEq _ _
      (by rw [finrank_range_mulVecBilin_one D (Fin _), Fintype.card_fin])⟩
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
  _root_.Algebra.GrothendieckAddGroup.addEquivInt (finrankAddEquiv D)

theorem grothendieckAddGroupEquivInt_of_mk {ι : Type*} [Fintype ι] (e : Matrix ι ι D)
    (he : IsIdempotentElem e) :
    grothendieckAddGroupEquivInt D (_root_.Algebra.GrothendieckAddGroup.of (mk e he)) =
      (Module.finrank Dᵐᵒᵖ (range (e.mulVecBilin D Dᵐᵒᵖ)) : ℤ) := by
  rw [grothendieckAddGroupEquivInt, _root_.Algebra.GrothendieckAddGroup.addEquivInt_of,
    finrankAddEquiv_mk]

end DivisionRing

end IdempotentMonoid

end NonUnitalSemiring

end TauCeti
