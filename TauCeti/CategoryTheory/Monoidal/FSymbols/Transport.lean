/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Monoidal.FSymbols.Basic
import TauCeti.Algebra.BigOperators.Group.Finset.Equiv

/-!
# Relabeling and base change of F-symbols and R-symbols

F-symbols and R-symbols can be transported in two independent directions.

* **Relabeling.** An isomorphism of fusion rules `σ : N.Equiv N'` is a bijection `ι ≃ ι'` of the
  index sets carrying the unit index of `N` to that of `N'` and preserving the multiplicities,
  `N'_{σa σb}^{σc} = N_{ab}^c`. It identifies the index sets `Fin N_{ab}^c` of the fusion spaces,
  and with them the row and column index types `Left` and `Right` of the F-matrices. Relabeling
  F-symbols for `N` along `σ` gives F-symbols for `N'` whose entries at `σa, σb, σc, σd` are those
  of the original ones at `a, b, c, d`; likewise for R-symbols. Relabelings of `N` by itself are
  the symmetries of the fusion rules, such as inversion of an abelian group.
* **Base change.** A ring homomorphism `f : R →+* S` applied entrywise sends F-symbols over `R` to
  F-symbols over `S`, and R-symbols to R-symbols. The inverse laws, the pentagon, the triangle and
  the hexagons are polynomial identities in the entries, so they are preserved. Base change to a
  quotient ring is how one reduces a presentation modulo a prime, and base change to an extension
  can create R-symbols: the F-symbols of `ℤ/2` with `F^{111}_1 = -1` carry no R-symbols over `ℤ`,
  but carry `R^{11}_0 = ±i` over `ℤ[i]`.

## Main definitions

* `TauCeti.FusionRules.Equiv N N'`: isomorphisms of fusion rules, with `refl`, `symm` and `trans`
  and their groupoid laws.
* `TauCeti.FusionRules.Equiv.finCongr`, `TauCeti.FusionRules.Equiv.leftCongr` and
  `TauCeti.FusionRules.Equiv.rightCongr`: the identifications of index types induced by an
  isomorphism of fusion rules.
* `TauCeti.FSymbols.reindex σ P` and `TauCeti.RSymbols.reindex σ Q`: relabeling.
* `TauCeti.FSymbols.map f P` and `TauCeti.RSymbols.map f Q`: base change.

## Main results

* `TauCeti.FSymbols.reindex_F_leftCongr`: the entry of the relabeled F-matrix at `σa, σb, σc, σd`
  is the original entry at `a, b, c, d`; `TauCeti.FSymbols.reindex_Finv_rightCongr`,
  `TauCeti.RSymbols.reindex_R_finCongr` and `TauCeti.RSymbols.reindex_Rinv_finCongr` are the same
  for inverse F-matrices, R-matrices and inverse R-matrices.
* Functoriality: `TauCeti.FSymbols.reindex_refl`, `TauCeti.FSymbols.reindex_reindex`,
  `TauCeti.FSymbols.map_id`, `TauCeti.FSymbols.map_map`, and the corresponding statements for
  R-symbols, phrased through their R-matrices since their types depend on the F-symbols.
* `TauCeti.FSymbols.map_reindex`: relabeling commutes with base change.
* `TauCeti.FSymbols.map_ofMul` and `TauCeti.FSymbols.reindex_ofMul`: the trivial F-symbols of a
  monoid are stable under base change and under relabeling along a monoid isomorphism.

## References

* A. Kitaev, *Anyons in an exactly solved model and beyond*, Ann. Physics 321 (2006),
  Appendix E, §E.1 and §E.3: the F- and R-symbols and their polynomial equations.
-/

public section

namespace TauCeti

universe u u' u'' v v' v''

namespace FusionRules

variable {ι : Type u} {ι' : Type u'} {ι'' : Type u''}

/-- An **isomorphism of fusion rules** `N ≃ N'`: a bijection of the index sets sending the unit
index of `N` to that of `N'` and preserving the multiplicities, `N'_{σa σb}^{σc} = N_{ab}^c`. -/
structure Equiv (N : FusionRules ι) (N' : FusionRules ι') extends ι ≃ ι' where
  /-- The unit index is sent to the unit index. -/
  map_unit' : toFun N.unit = N'.unit
  /-- The multiplicities are preserved. -/
  map_N' : ∀ a b c, N'.N (toFun a) (toFun b) (toFun c) = N.N a b c

namespace Equiv

variable {N : FusionRules ι} {N' : FusionRules ι'} {N'' : FusionRules ι''}

instance : EquivLike (N.Equiv N') ι ι' where
  coe σ := σ.toFun
  inv σ := σ.invFun
  left_inv σ := σ.left_inv
  right_inv σ := σ.right_inv
  coe_injective' σ τ h _ := by
    cases σ
    cases τ
    congr
    exact _root_.Equiv.coe_fn_injective h

@[simp]
theorem coe_toEquiv (σ : N.Equiv N') : ⇑σ.toEquiv = σ := (rfl)

@[ext]
theorem ext {σ τ : N.Equiv N'} (h : ∀ a, σ a = τ a) : σ = τ :=
  DFunLike.ext _ _ h

theorem toEquiv_injective : Function.Injective (toEquiv : N.Equiv N' → ι ≃ ι') :=
  fun _ _ h ↦ ext (_root_.Equiv.ext_iff.mp h)

@[simp]
theorem map_unit (σ : N.Equiv N') : σ N.unit = N'.unit :=
  σ.map_unit'

@[simp]
theorem map_N (σ : N.Equiv N') (a b c : ι) : N'.N (σ a) (σ b) (σ c) = N.N a b c :=
  σ.map_N' a b c

variable (N) in
/-- The identity isomorphism of fusion rules. -/
@[refl]
protected def refl : N.Equiv N where
  toEquiv := _root_.Equiv.refl ι
  map_unit' := rfl
  map_N' _ _ _ := rfl

@[simp]
theorem refl_apply (a : ι) : Equiv.refl N a = a := (rfl)

@[simp]
theorem toEquiv_refl : (Equiv.refl N).toEquiv = _root_.Equiv.refl ι := (rfl)

/-- The inverse of an isomorphism of fusion rules. -/
@[symm]
protected def symm (σ : N.Equiv N') : N'.Equiv N where
  toEquiv := σ.toEquiv.symm
  map_unit' := by simp [_root_.Equiv.symm_apply_eq]
  map_N' a b c := by
    simpa using (σ.map_N' (σ.toEquiv.symm a) (σ.toEquiv.symm b) (σ.toEquiv.symm c)).symm

@[simp]
theorem coe_toEquiv_symm (σ : N.Equiv N') : ⇑σ.toEquiv.symm = σ.symm := (rfl)

@[simp]
theorem toEquiv_symm (σ : N.Equiv N') : σ.symm.toEquiv = σ.toEquiv.symm := (rfl)

@[simp]
theorem apply_symm_apply (σ : N.Equiv N') (a : ι') : σ (σ.symm a) = a :=
  σ.toEquiv.apply_symm_apply a

@[simp]
theorem symm_apply_apply (σ : N.Equiv N') (a : ι) : σ.symm (σ a) = a :=
  σ.toEquiv.symm_apply_apply a

@[simp]
theorem symm_symm (σ : N.Equiv N') : σ.symm.symm = σ := (rfl)

@[simp]
theorem symm_refl : (Equiv.refl N).symm = Equiv.refl N := (rfl)

/-- The composite of two isomorphisms of fusion rules. -/
@[trans]
protected def trans (σ : N.Equiv N') (τ : N'.Equiv N'') : N.Equiv N'' where
  toEquiv := σ.toEquiv.trans τ.toEquiv
  map_unit' := by simp
  map_N' a b c := by simp

@[simp]
theorem trans_apply (σ : N.Equiv N') (τ : N'.Equiv N'') (a : ι) : σ.trans τ a = τ (σ a) := (rfl)

@[simp]
theorem toEquiv_trans (σ : N.Equiv N') (τ : N'.Equiv N'') :
    (σ.trans τ).toEquiv = σ.toEquiv.trans τ.toEquiv := (rfl)

@[simp]
theorem refl_trans (σ : N.Equiv N') : (Equiv.refl N).trans σ = σ := (rfl)

@[simp]
theorem trans_refl (σ : N.Equiv N') : σ.trans (Equiv.refl N') = σ := (rfl)

@[simp]
theorem trans_assoc {ι''' : Type*} {N''' : FusionRules ι'''} (σ : N.Equiv N') (τ : N'.Equiv N'')
    (ρ : N''.Equiv N''') : (σ.trans τ).trans ρ = σ.trans (τ.trans ρ) := (rfl)

@[simp]
theorem self_trans_symm (σ : N.Equiv N') : σ.trans σ.symm = Equiv.refl N :=
  ext σ.symm_apply_apply

@[simp]
theorem symm_trans_self (σ : N.Equiv N') : σ.symm.trans σ = Equiv.refl N' :=
  ext σ.apply_symm_apply

/-- The identification `Fin N_{ab}^c ≃ Fin N'_{σa σb}^{σc}` of the index sets of the fusion
spaces induced by an isomorphism of fusion rules. -/
def finCongr (σ : N.Equiv N') (a b c : ι) : Fin (N.N a b c) ≃ Fin (N'.N (σ a) (σ b) (σ c)) :=
  _root_.finCongr (σ.map_N a b c).symm

/-- The identification `σ.finCongr a b c` is the cast along `N_{ab}^c = N'_{σa σb}^{σc}`. -/
@[simp]
theorem finCongr_apply (σ : N.Equiv N') {a b c : ι} (i : Fin (N.N a b c)) :
    σ.finCongr a b c i = Fin.cast (σ.map_N a b c).symm i := (rfl)

theorem coe_finCongr (σ : N.Equiv N') {a b c : ι} (i : Fin (N.N a b c)) :
    (σ.finCongr a b c i : ℕ) = i := (rfl)

/-- The identification of the row index types `N.Left a b c d ≃ N'.Left (σ a) (σ b) (σ c) (σ d)`
of the F-matrices induced by an isomorphism of fusion rules. -/
def leftCongr (σ : N.Equiv N') (a b c d : ι) : N.Left a b c d ≃ N'.Left (σ a) (σ b) (σ c) (σ d) :=
  _root_.Equiv.sigmaCongr σ.toEquiv fun e ↦ (σ.finCongr a b e).prodCongr (σ.finCongr e c d)

@[simp]
theorem leftCongr_mk (σ : N.Equiv N') {a b c d e : ι} (i : Fin (N.N a b e))
    (j : Fin (N.N e c d)) :
    σ.leftCongr a b c d ⟨e, i, j⟩ = ⟨σ e, σ.finCongr a b e i, σ.finCongr e c d j⟩ := (rfl)

/-- The identification of the column index types
`N.Right a b c d ≃ N'.Right (σ a) (σ b) (σ c) (σ d)` of the F-matrices induced by an isomorphism
of fusion rules. -/
def rightCongr (σ : N.Equiv N') (a b c d : ι) :
    N.Right a b c d ≃ N'.Right (σ a) (σ b) (σ c) (σ d) :=
  _root_.Equiv.sigmaCongr σ.toEquiv fun f ↦ (σ.finCongr b c f).prodCongr (σ.finCongr a f d)

@[simp]
theorem rightCongr_mk (σ : N.Equiv N') {a b c d f : ι} (k : Fin (N.N b c f))
    (l : Fin (N.N a f d)) :
    σ.rightCongr a b c d ⟨f, k, l⟩ = ⟨σ f, σ.finCongr b c f k, σ.finCongr a f d l⟩ := (rfl)

section ofMul

variable {M : Type u} {M' : Type u'} [MulOneClass M] [DecidableEq M] [MulOneClass M']
  [DecidableEq M']

/-- A multiplicative isomorphism induces an isomorphism of the group fusion rules. -/
def ofMulEquiv (e : M ≃* M') : (ofMul M).Equiv (ofMul M') where
  toEquiv := e.toEquiv
  map_unit' := by simp
  map_N' a b c := by simp [← map_mul, e.injective.eq_iff]

@[simp]
theorem ofMulEquiv_apply (e : M ≃* M') (a : M) : ofMulEquiv e a = e a := (rfl)

end ofMul

end Equiv

end FusionRules

namespace FSymbols

variable {ι : Type u} {ι' : Type u'} {ι'' : Type u''} [Fintype ι] [DecidableEq ι] [Fintype ι']
  [DecidableEq ι'] [Fintype ι''] [DecidableEq ι''] {R : Type v} {S : Type v'} {T : Type v''}
  [CommSemiring R] [CommSemiring S] [CommSemiring T] {N : FusionRules ι} {N' : FusionRules ι'}
  {N'' : FusionRules ι''}

/-- The triangle equation, with the unit index in the middle given only up to equality. -/
private theorem F_eq_ite_of_eq_unit (P : FSymbols R N) {a b c d : ι} (hb : b = N.unit)
    (i : Fin (N.N a b a)) (k : Fin (N.N b c c)) (j l : Fin (N.N a c d)) :
    P.F a b c d ⟨a, i, j⟩ ⟨c, k, l⟩ = if j = l then 1 else 0 := by
  subst hb
  rw [Subsingleton.elim i (N.unitRight a), Subsingleton.elim k (N.unitLeft c)]
  exact P.triangle a c d j l

/-- Entries of the F-matrices agree when their outer indices are equal and their inner indices have
equal values. -/
private theorem F_congr (P : FSymbols R N) {a b c d e f a' b' c' d' e' f' : ι}
    (ha : a = a') (hb : b = b') (hc : c = c') (hd : d = d') (he : e = e') (hf : f = f')
    {i : Fin (N.N a b e)} {j : Fin (N.N e c d)} {k : Fin (N.N b c f)} {l : Fin (N.N a f d)}
    {i' : Fin (N.N a' b' e')} {j' : Fin (N.N e' c' d')} {k' : Fin (N.N b' c' f')}
    {l' : Fin (N.N a' f' d')} (hi : (i : ℕ) = i') (hj : (j : ℕ) = j') (hk : (k : ℕ) = k')
    (hl : (l : ℕ) = l') :
    P.F a b c d ⟨e, i, j⟩ ⟨f, k, l⟩ = P.F a' b' c' d' ⟨e', i', j'⟩ ⟨f', k', l'⟩ := by
  subst ha hb hc hd he hf
  rw [Fin.ext hi, Fin.ext hj, Fin.ext hk, Fin.ext hl]

/-- Entries of the inverse F-matrices agree when their outer indices are equal and their inner
indices have equal values. -/
private theorem Finv_congr (P : FSymbols R N) {a b c d e f a' b' c' d' e' f' : ι}
    (ha : a = a') (hb : b = b') (hc : c = c') (hd : d = d') (he : e = e') (hf : f = f')
    {i : Fin (N.N a b e)} {j : Fin (N.N e c d)} {k : Fin (N.N b c f)} {l : Fin (N.N a f d)}
    {i' : Fin (N.N a' b' e')} {j' : Fin (N.N e' c' d')} {k' : Fin (N.N b' c' f')}
    {l' : Fin (N.N a' f' d')} (hi : (i : ℕ) = i') (hj : (j : ℕ) = j') (hk : (k : ℕ) = k')
    (hl : (l : ℕ) = l') :
    P.Finv a b c d ⟨f, k, l⟩ ⟨e, i, j⟩ = P.Finv a' b' c' d' ⟨f', k', l'⟩ ⟨e', i', j'⟩ := by
  subst ha hb hc hd he hf
  rw [Fin.ext hi, Fin.ext hj, Fin.ext hk, Fin.ext hl]

/-- **Relabeling** of F-symbols along an isomorphism of fusion rules `σ : N.Equiv N'`: the entry
of `F^{abc}_d` for `N'` is the entry of the original F-matrix at `σ⁻¹ a, σ⁻¹ b, σ⁻¹ c, σ⁻¹ d`. -/
def reindex (σ : N.Equiv N') (P : FSymbols R N) : FSymbols R N' where
  F a b c d := (P.F (σ.symm a) (σ.symm b) (σ.symm c) (σ.symm d)).submatrix
    (σ.symm.leftCongr a b c d) (σ.symm.rightCongr a b c d)
  Finv a b c d := (P.Finv (σ.symm a) (σ.symm b) (σ.symm c) (σ.symm d)).submatrix
    (σ.symm.rightCongr a b c d) (σ.symm.leftCongr a b c d)
  F_mul_Finv a b c d := by simp [P.F_mul_Finv]
  Finv_mul_F a b c d := by simp [P.Finv_mul_F]
  pentagon A B C D E p q r s i₁ i₂ i₃ k m n := by
    have h := P.pentagon (σ.symm A) (σ.symm B) (σ.symm C) (σ.symm D) (σ.symm E) (σ.symm p)
      (σ.symm q) (σ.symm r) (σ.symm s) (σ.symm.finCongr _ _ _ i₁) (σ.symm.finCongr _ _ _ i₂)
      (σ.symm.finCongr _ _ _ i₃) (σ.symm.finCongr _ _ _ k) (σ.symm.finCongr _ _ _ m)
      (σ.symm.finCongr _ _ _ n)
    simp only [Matrix.submatrix_apply, FusionRules.Equiv.leftCongr_mk,
      FusionRules.Equiv.rightCongr_mk]
    -- Both sides are the sums of `h`, reindexed along `σ⁻¹` and the identifications of the
    -- index sets of the fusion spaces.
    convert h using 1
    · exact Fintype.sum_equiv (σ.symm.finCongr _ _ _) _ _ fun _ ↦ rfl
    · exact Fintype.sum_equiv₄ σ.symm.toEquiv (fun _ ↦ σ.symm.finCongr _ _ _)
        (fun _ ↦ σ.symm.finCongr _ _ _) (fun _ ↦ σ.symm.finCongr _ _ _) fun _ _ _ _ ↦ rfl
  triangle a c d j l := by
    simp only [Matrix.submatrix_apply, FusionRules.Equiv.leftCongr_mk,
      FusionRules.Equiv.rightCongr_mk]
    rw [P.F_eq_ite_of_eq_unit σ.symm.map_unit]
    simp

@[simp]
theorem reindex_F (σ : N.Equiv N') (P : FSymbols R N) (a b c d : ι') :
    (P.reindex σ).F a b c d = (P.F (σ.symm a) (σ.symm b) (σ.symm c) (σ.symm d)).submatrix
      (σ.symm.leftCongr a b c d) (σ.symm.rightCongr a b c d) := (rfl)

@[simp]
theorem reindex_Finv (σ : N.Equiv N') (P : FSymbols R N) (a b c d : ι') :
    (P.reindex σ).Finv a b c d = (P.Finv (σ.symm a) (σ.symm b) (σ.symm c) (σ.symm d)).submatrix
      (σ.symm.rightCongr a b c d) (σ.symm.leftCongr a b c d) := (rfl)

/-- The relabeled F-matrix at `σ a, σ b, σ c, σ d` is the original F-matrix at `a, b, c, d`, with
rows and columns identified along `σ`. -/
theorem reindex_F_leftCongr (σ : N.Equiv N') (P : FSymbols R N) {a b c d : ι}
    (x : N.Left a b c d) (y : N.Right a b c d) :
    (P.reindex σ).F (σ a) (σ b) (σ c) (σ d) (σ.leftCongr a b c d x) (σ.rightCongr a b c d y) =
      P.F a b c d x y := by
  obtain ⟨e, i, j⟩ := x
  obtain ⟨f, k, l⟩ := y
  exact P.F_congr (σ.symm_apply_apply a) (σ.symm_apply_apply b) (σ.symm_apply_apply c)
    (σ.symm_apply_apply d) (σ.symm_apply_apply e) (σ.symm_apply_apply f) rfl rfl rfl rfl

/-- The relabeled inverse F-matrix at `σ a, σ b, σ c, σ d` is the original inverse F-matrix at
`a, b, c, d`, with rows and columns identified along `σ`. -/
theorem reindex_Finv_rightCongr (σ : N.Equiv N') (P : FSymbols R N) {a b c d : ι}
    (y : N.Right a b c d) (x : N.Left a b c d) :
    (P.reindex σ).Finv (σ a) (σ b) (σ c) (σ d) (σ.rightCongr a b c d y) (σ.leftCongr a b c d x) =
      P.Finv a b c d y x := by
  obtain ⟨e, i, j⟩ := x
  obtain ⟨f, k, l⟩ := y
  exact P.Finv_congr (σ.symm_apply_apply a) (σ.symm_apply_apply b) (σ.symm_apply_apply c)
    (σ.symm_apply_apply d) (σ.symm_apply_apply e) (σ.symm_apply_apply f) rfl rfl rfl rfl

/-- Relabeling along the identity does nothing. -/
@[simp]
theorem reindex_refl (P : FSymbols R N) : P.reindex (FusionRules.Equiv.refl N) = P := by
  -- the identifications of index types along the identity are the identity on elements
  ext a b c d ⟨e, i, j⟩ ⟨f, k, l⟩
  rfl

/-- Relabeling along a composite is the composite of the relabelings. -/
@[simp]
theorem reindex_reindex (σ : N.Equiv N') (τ : N'.Equiv N'') (P : FSymbols R N) :
    (P.reindex σ).reindex τ = P.reindex (σ.trans τ) := by
  -- the identifications of index types along `σ.trans τ` compose those along `σ` and `τ`
  ext a b c d ⟨e, i, j⟩ ⟨f, k, l⟩
  rfl

theorem reindex_symm_reindex (σ : N.Equiv N') (P : FSymbols R N) :
    (P.reindex σ).reindex σ.symm = P := by
  simp

theorem reindex_reindex_symm (σ : N.Equiv N') (P : FSymbols R N') :
    (P.reindex σ.symm).reindex σ = P := by
  simp

/-- **Base change** of F-symbols along a ring homomorphism, applied entrywise. -/
def map (f : R →+* S) (P : FSymbols R N) : FSymbols S N where
  F a b c d := (P.F a b c d).map f
  Finv a b c d := (P.Finv a b c d).map f
  F_mul_Finv a b c d := by
    rw [← Matrix.map_mul, P.F_mul_Finv, Matrix.map_one _ (map_zero f) (map_one f)]
  Finv_mul_F a b c d := by
    rw [← Matrix.map_mul, P.Finv_mul_F, Matrix.map_one _ (map_zero f) (map_one f)]
  pentagon A B C D E p q r s i₁ i₂ i₃ k m n := by
    simpa [map_sum, map_mul] using congrArg f (P.pentagon A B C D E p q r s i₁ i₂ i₃ k m n)
  triangle a c d j l := by
    simp [P.triangle, apply_ite f]

@[simp]
theorem map_F (f : R →+* S) (P : FSymbols R N) (a b c d : ι) :
    (P.map f).F a b c d = (P.F a b c d).map f := (rfl)

@[simp]
theorem map_Finv (f : R →+* S) (P : FSymbols R N) (a b c d : ι) :
    (P.map f).Finv a b c d = (P.Finv a b c d).map f := (rfl)

@[simp]
theorem map_id (P : FSymbols R N) : P.map (RingHom.id R) = P := by
  ext
  simp

@[simp]
theorem map_map (f : R →+* S) (g : S →+* T) (P : FSymbols R N) :
    (P.map f).map g = P.map (g.comp f) := by
  ext
  simp

/-- Relabeling commutes with base change. -/
theorem map_reindex (f : R →+* S) (σ : N.Equiv N') (P : FSymbols R N) :
    (P.reindex σ).map f = (P.map f).reindex σ := by
  ext
  simp

section ofMul

variable {M : Type u} {M' : Type u'} [Monoid M] [Fintype M] [DecidableEq M] [Monoid M']
  [Fintype M'] [DecidableEq M']

@[simp]
theorem map_ofMul (f : R →+* S) : (ofMul R M).map f = ofMul S M := by
  ext
  simp

@[simp]
theorem reindex_ofMul (e : M ≃* M') :
    (ofMul R M).reindex (FusionRules.Equiv.ofMulEquiv e) = ofMul R M' := by
  ext
  simp

end ofMul

end FSymbols

namespace RSymbols

variable {ι : Type u} {ι' : Type u'} {ι'' : Type u''} [Fintype ι] [DecidableEq ι] [Fintype ι']
  [DecidableEq ι'] [Fintype ι''] [DecidableEq ι''] {K : Type v} {L : Type v'} {L' : Type v''}
  [CommSemiring K] [CommSemiring L] [CommSemiring L'] {N : FusionRules ι} {N' : FusionRules ι'}
  {N'' : FusionRules ι''} {P : FSymbols K N}

/-- **Relabeling** of R-symbols along an isomorphism of fusion rules `σ : N.Equiv N'`: R-symbols
for the relabeled F-symbols, the entry of `R^{ab}_c` being the original entry at
`σ⁻¹ a, σ⁻¹ b, σ⁻¹ c`. -/
def reindex (σ : N.Equiv N') (Q : RSymbols P) : RSymbols (P.reindex σ) where
  R a b c := (Q.R (σ.symm a) (σ.symm b) (σ.symm c)).submatrix (σ.symm.finCongr a b c)
    (σ.symm.finCongr b a c)
  Rinv a b c := (Q.Rinv (σ.symm a) (σ.symm b) (σ.symm c)).submatrix (σ.symm.finCongr b a c)
    (σ.symm.finCongr a b c)
  R_mul_Rinv a b c := by simp [Q.R_mul_Rinv]
  Rinv_mul_R a b c := by simp [Q.Rinv_mul_R]
  hexagon_forward a b c d e g i j n o := by
    have h := Q.hexagon_forward (σ.symm a) (σ.symm b) (σ.symm c) (σ.symm d) (σ.symm e)
      (σ.symm g) (σ.symm.finCongr _ _ _ i) (σ.symm.finCongr _ _ _ j) (σ.symm.finCongr _ _ _ n)
      (σ.symm.finCongr _ _ _ o)
    simp only [FSymbols.reindex_F, Matrix.submatrix_apply, FusionRules.Equiv.leftCongr_mk,
      FusionRules.Equiv.rightCongr_mk]
    -- Both sides are the sums of `h`, reindexed along `σ⁻¹` and the identifications of the
    -- index sets of the fusion spaces.
    convert h using 1
    · exact Fintype.sum_equiv₄ σ.symm.toEquiv (fun _ ↦ σ.symm.finCongr _ _ _)
        (fun _ ↦ σ.symm.finCongr _ _ _) (fun _ ↦ σ.symm.finCongr _ _ _) fun _ _ _ _ ↦ rfl
    · exact Fintype.sum_equiv₂ (σ.symm.finCongr _ _ _) (fun _ ↦ σ.symm.finCongr _ _ _)
        fun _ _ ↦ rfl
  hexagon_reverse a b c d f g k l n o := by
    have h := Q.hexagon_reverse (σ.symm a) (σ.symm b) (σ.symm c) (σ.symm d) (σ.symm f)
      (σ.symm g) (σ.symm.finCongr _ _ _ k) (σ.symm.finCongr _ _ _ l) (σ.symm.finCongr _ _ _ n)
      (σ.symm.finCongr _ _ _ o)
    simp only [FSymbols.reindex_Finv, Matrix.submatrix_apply, FusionRules.Equiv.leftCongr_mk,
      FusionRules.Equiv.rightCongr_mk]
    -- As for the forward hexagon.
    convert h using 1
    · exact Fintype.sum_equiv₄ σ.symm.toEquiv (fun _ ↦ σ.symm.finCongr _ _ _)
        (fun _ ↦ σ.symm.finCongr _ _ _) (fun _ ↦ σ.symm.finCongr _ _ _) fun _ _ _ _ ↦ rfl
    · exact Fintype.sum_equiv₂ (σ.symm.finCongr _ _ _) (fun _ ↦ σ.symm.finCongr _ _ _)
        fun _ _ ↦ rfl

@[simp]
theorem reindex_R (σ : N.Equiv N') (Q : RSymbols P) (a b c : ι') :
    (Q.reindex σ).R a b c = (Q.R (σ.symm a) (σ.symm b) (σ.symm c)).submatrix
      (σ.symm.finCongr a b c) (σ.symm.finCongr b a c) := (rfl)

@[simp]
theorem reindex_Rinv (σ : N.Equiv N') (Q : RSymbols P) (a b c : ι') :
    (Q.reindex σ).Rinv a b c = (Q.Rinv (σ.symm a) (σ.symm b) (σ.symm c)).submatrix
      (σ.symm.finCongr b a c) (σ.symm.finCongr a b c) := (rfl)

/-- Entries of the R-matrices agree when their outer indices are equal and their inner indices
have equal values. -/
private theorem R_congr (Q : RSymbols P) {a b c a' b' c' : ι} (ha : a = a') (hb : b = b')
    (hc : c = c') {i : Fin (N.N a b c)} {j : Fin (N.N b a c)} {i' : Fin (N.N a' b' c')}
    {j' : Fin (N.N b' a' c')} (hi : (i : ℕ) = i') (hj : (j : ℕ) = j') :
    Q.R a b c i j = Q.R a' b' c' i' j' := by
  subst ha hb hc
  rw [Fin.ext hi, Fin.ext hj]

/-- The relabeled R-matrix at `σ a, σ b, σ c` is the original R-matrix at `a, b, c`, with rows and
columns identified along `σ`. -/
theorem reindex_R_finCongr (σ : N.Equiv N') (Q : RSymbols P) {a b c : ι} (i : Fin (N.N a b c))
    (j : Fin (N.N b a c)) :
    (Q.reindex σ).R (σ a) (σ b) (σ c) (σ.finCongr a b c i) (σ.finCongr b a c j) = Q.R a b c i j :=
  Q.R_congr (σ.symm_apply_apply a) (σ.symm_apply_apply b) (σ.symm_apply_apply c) rfl rfl

/-- Entries of the inverse R-matrices agree when their outer indices are equal and their inner
indices have equal values. -/
private theorem Rinv_congr (Q : RSymbols P) {a b c a' b' c' : ι} (ha : a = a') (hb : b = b')
    (hc : c = c') {i : Fin (N.N b a c)} {j : Fin (N.N a b c)} {i' : Fin (N.N b' a' c')}
    {j' : Fin (N.N a' b' c')} (hi : (i : ℕ) = i') (hj : (j : ℕ) = j') :
    Q.Rinv a b c i j = Q.Rinv a' b' c' i' j' := by
  subst ha hb hc
  rw [Fin.ext hi, Fin.ext hj]

/-- The relabeled inverse R-matrix at `σ a, σ b, σ c` is the original inverse R-matrix at
`a, b, c`, with rows and columns identified along `σ`. -/
theorem reindex_Rinv_finCongr (σ : N.Equiv N') (Q : RSymbols P) {a b c : ι}
    (i : Fin (N.N b a c)) (j : Fin (N.N a b c)) :
    (Q.reindex σ).Rinv (σ a) (σ b) (σ c) (σ.finCongr b a c i) (σ.finCongr a b c j) =
      Q.Rinv a b c i j :=
  Q.Rinv_congr (σ.symm_apply_apply a) (σ.symm_apply_apply b) (σ.symm_apply_apply c) rfl rfl

/-- Relabeling R-symbols along the identity does not change the R-matrices.

This and the two round-trip lemmas below have high simp priority so that they fire before
`reindex_R`: after unfolding, simp cannot rewrite the relabeled outer indices of `Q.R`, on which
the types of the inner indices depend. -/
@[simp high]
theorem reindex_refl_R (Q : RSymbols P) : (Q.reindex (FusionRules.Equiv.refl N)).R = Q.R := by
  -- the identifications of index sets along the identity are the identity on elements
  ext a b c i j
  rfl

/-- Relabeling R-symbols along a composite is the composite of the relabelings. -/
theorem reindex_reindex_R (σ : N.Equiv N') (τ : N'.Equiv N'') (Q : RSymbols P) :
    ((Q.reindex σ).reindex τ).R = (Q.reindex (σ.trans τ)).R := by
  -- the identifications of index sets along `σ.trans τ` compose those along `σ` and `τ`
  ext a b c i j
  rfl

/-- Relabeling R-symbols along `σ` and then along `σ⁻¹` does not change the R-matrices. -/
@[simp high]
theorem reindex_symm_reindex_R (σ : N.Equiv N') (Q : RSymbols P) :
    ((Q.reindex σ).reindex σ.symm).R = Q.R := by
  rw [reindex_reindex_R, FusionRules.Equiv.self_trans_symm, reindex_refl_R]

/-- Relabeling R-symbols along `σ⁻¹` and then along `σ` does not change the R-matrices. -/
@[simp high]
theorem reindex_reindex_symm_R (σ : N.Equiv N') {P : FSymbols K N'} (Q : RSymbols P) :
    ((Q.reindex σ.symm).reindex σ).R = Q.R := by
  rw [reindex_reindex_R, FusionRules.Equiv.symm_trans_self, reindex_refl_R]

/-- **Base change** of R-symbols along a ring homomorphism, applied entrywise: R-symbols for the
base-changed F-symbols. -/
def map (f : K →+* L) (Q : RSymbols P) : RSymbols (P.map f) where
  R a b c := (Q.R a b c).map f
  Rinv a b c := (Q.Rinv a b c).map f
  R_mul_Rinv a b c := by
    rw [← Matrix.map_mul, Q.R_mul_Rinv, Matrix.map_one _ (map_zero f) (map_one f)]
  Rinv_mul_R a b c := by
    rw [← Matrix.map_mul, Q.Rinv_mul_R, Matrix.map_one _ (map_zero f) (map_one f)]
  hexagon_forward a b c d e g i j n o := by
    simpa [map_sum, map_mul] using congrArg f (Q.hexagon_forward a b c d e g i j n o)
  hexagon_reverse a b c d e g i j n o := by
    simpa [map_sum, map_mul] using congrArg f (Q.hexagon_reverse a b c d e g i j n o)

@[simp]
theorem map_R (f : K →+* L) (Q : RSymbols P) (a b c : ι) :
    (Q.map f).R a b c = (Q.R a b c).map f := (rfl)

@[simp]
theorem map_Rinv (f : K →+* L) (Q : RSymbols P) (a b c : ι) :
    (Q.map f).Rinv a b c = (Q.Rinv a b c).map f := (rfl)

theorem map_id_R (Q : RSymbols P) : (Q.map (RingHom.id K)).R = Q.R := by
  ext
  simp

theorem map_map_R (f : K →+* L) (g : L →+* L') (Q : RSymbols P) :
    ((Q.map f).map g).R = (Q.map (g.comp f)).R := by
  ext
  simp

/-- Relabeling R-symbols commutes with base change. -/
theorem map_reindex_R (f : K →+* L) (σ : N.Equiv N') (Q : RSymbols P) :
    ((Q.reindex σ).map f).R = ((Q.map f).reindex σ).R := by
  ext
  simp

end RSymbols

end TauCeti
