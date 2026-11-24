/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.DirectSum.LinearMap
public import Mathlib.Algebra.Polynomial.Expand
public import Mathlib.Data.ZMod.Basic
public import Mathlib.LinearAlgebra.Charpoly.ToMatrix
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import TauCeti.Data.ZMod.Periodic

/-!
# The characteristic polynomial of a cyclic block endomorphism

Let `F` be an endomorphism of `M = ⨁ i : ZMod f, V i` which maps each summand `V i` into the next
one, `V (i + 1)`, through maps `A i : V i → V (i + 1)`. Then `F ^ f` preserves every summand, and
on `V 0` it is the return map `A (f - 1) ∘ ⋯ ∘ A 0`. When the summands have equal rank,

  `charpoly F = (charpoly (F ^ f restricted to V a)).comp (X ^ f)`,

that is `det (X - F) = det (X ^ f - A (f - 1) ⋯ A 0)`, for any starting summand `a`
(`LinearMap.charpoly_eq_expand_charpoly_restrict_pow`). In particular, the characteristic polynomial
of the return map does not depend on the starting summand (`LinearMap.charpoly_restrict_pow_eq`).
The formula substitutes `X ^ f` into a single polynomial rather than multiplying `f` copies of it:
for `f = 2` and the identity return map on a line, it gives `X ^ 2 - 1`, not `(X - 1) ^ 2`.

This is the linear algebra behind the local characteristic polynomial of an induced representation:
a Frobenius element permutes the summands of the induced module in cycles, one for each place above
a given place, of length the residue degree, so that the characteristic polynomial of the induced
action is a product of polynomials `P (X ^ f)`.

Without the equal-rank hypothesis the identity holds after multiplying both sides by powers of `X`,
in the same way as `LinearMap.X_pow_finrank_mul_charpoly_comp_comm`. All statements hold over an
arbitrary commutative ring.

## Main results

* `Matrix.X_pow_mul_charpoly_eq_X_pow_mul_expand`: the matrix form, for `M` mapping the block
  `b ⁻¹' {j}` into `b ⁻¹' {j + 1}`.
* `LinearMap.X_pow_mul_charpoly_eq_X_pow_mul_expand`: the form for an internal direct sum.
* `LinearMap.charpoly_eq_expand_charpoly_restrict_pow`: the equal-rank form.
* `LinearMap.charpoly_restrict_pow_eq`: independence of the starting summand.
* `Matrix.expand_charpoly`: substituting `X ^ k` into `charpoly M` gives `det (X ^ k - M)`.
-/

public section

open Polynomial

namespace Matrix

variable {R ι : Type*} [Fintype ι] [DecidableEq ι]

/-- If `M` maps the block `b ⁻¹' {j}` into the block `b ⁻¹' {j + 1}` for every `j`, then `M ^ k`
maps `b ⁻¹' {j}` into `b ⁻¹' {j + k}`. -/
theorem pow_apply_eq_zero_of_ne_add [Semiring R] {G : Type*} [AddMonoidWithOne G] {M : Matrix ι ι R}
    {b : ι → G} (hM : ∀ r c, b r ≠ b c + 1 → M r c = 0) (k : ℕ) {r c : ι}
    (h : b r ≠ b c + k) : (M ^ k) r c = 0 := by
  induction k generalizing r with
  | zero => exact one_apply_ne fun hrc ↦ h (by simp [hrc])
  | succ k ih =>
    rw [pow_succ', Matrix.mul_apply]
    refine Finset.sum_eq_zero fun m _ ↦ ?_
    by_cases hm : b m = b c + k
    · rw [hM r m fun hr ↦ h (by rw [hr, hm, Nat.cast_succ, add_assoc]), zero_mul]
    · rw [ih hm, mul_zero]

variable [CommRing R] {f : ℕ} {M : Matrix ι ι R} {b : ι → ZMod f}

/-- The block of `M` away from `b ⁻¹' {a}` has characteristic polynomial a power of `X`: it is
strictly block triangular for the order of the residues `b r - a`. -/
private lemma charpoly_toSquareBlockProp_ne [NeZero f] (hM : ∀ r c, b r ≠ b c + 1 → M r c = 0)
    (a : ZMod f) :
    (M.toSquareBlockProp fun r ↦ b r ≠ a).charpoly = X ^ Fintype.card {r // b r ≠ a} := by
  set N := M.toSquareBlockProp fun r ↦ b r ≠ a
  let β : {r // b r ≠ a} → ℕᵒᵈ := fun r ↦ OrderDual.toDual (b r - a).val
  -- an entry of `N` is nonzero only if its row is one step after its column along the cycle
  have hN : ∀ r c, N r c ≠ 0 → (b c - a).val < (b r - a).val := by
    intro r c hrc
    have hr : b r = b c + 1 := by_contra fun h ↦ hrc (hM _ _ h)
    have h1 : b c - a + 1 = b r - a := by rw [hr]; ring
    -- one step forward along `ZMod f` increases the residue `val`, as it does not land on `0`
    have hr0 : b c - a + 1 ≠ 0 := by rw [h1]; exact sub_ne_zero.mpr r.2
    rcases (b c - a).val_add_one_eq_or with h | h
    · rw [← h1, h]
      omega
    · have hlt := ZMod.val_lt (b c - a)
      exact absurd ((ZMod.val_eq_zero _).mp (by omega)) hr0
  have hβ : N.BlockTriangular β := fun r c hcr ↦ by
    by_contra h
    exact (hN r c h).not_ge (OrderDual.toDual_lt_toDual.mp hcr).le
  have hzero : ∀ k, N.toSquareBlock β k = 0 := fun k ↦ by
    ext r c
    by_contra h
    exact (hN r c h).ne (by simpa [β] using (r.2.trans c.2.symm).symm)
  simp_rw [hβ.charpoly, hzero, charpoly_zero, Finset.prod_pow_eq_pow_sum]
  congr 1
  rw [← Finset.card_univ, Finset.card_eq_sum_card_image β]
  exact Finset.sum_congr rfl fun k _ ↦ by rw [Fintype.card_subtype]

/-- Substituting `X ^ k` into the characteristic polynomial of `M` gives `det (X ^ k - M)`. -/
theorem expand_charpoly (M : Matrix ι ι R) (k : ℕ) :
    expand R k M.charpoly = (scalar ι (X ^ k : R[X]) - M.map C).det := by
  rw [charpoly, AlgHom.map_det]
  congr 1
  ext i j
  by_cases h : i = j <;> simp [h]

/-- The column operation used to compute the characteristic polynomial of a cyclic block matrix: the
columns of the block at `a` are those of `∑ X ^ i M ^ (f - 1 - i)`, and the others those of `1`. -/
private noncomputable def cyclicColumnOp (M : Matrix ι ι R) (b : ι → ZMod f) (a : ZMod f) :
    Matrix ι ι R[X] :=
  of fun r c ↦ if b c = a then
    (∑ i ∈ Finset.range f, scalar ι (X : R[X]) ^ i * M.map C ^ (f - 1 - i)) r c
  else (1 : Matrix ι ι R[X]) r c

private lemma det_cyclicColumnOp [NeZero f] (hM : ∀ r c, b r ≠ b c + 1 → M r c = 0)
    (a : ZMod f) : (cyclicColumnOp M b a).det = X ^ ((f - 1) * Fintype.card {r // b r = a}) := by
  set W := cyclicColumnOp M b a
  have hxy (k l : ℕ) (r c : ι) :
      (scalar ι (X : R[X]) ^ k * M.map C ^ l) r c = X ^ k * C ((M ^ l) r c) := by
    rw [← map_pow, ← M.map_pow]
    simp
  rw [twoBlockTriangular_det' W (b · = a) fun r hr c hc ↦ by
    simp [W, cyclicColumnOp, hc, one_apply_ne (fun h : r = c ↦ hc (h ▸ hr))]]
  have h1 : W.toSquareBlockProp (fun r ↦ ¬b r = a) = 1 := by
    ext r c : 1
    simp [W, cyclicColumnOp, toSquareBlockProp_def, c.2, Matrix.one_apply, Subtype.ext_iff]
  -- on the block at `a`, only the term `X ^ (f - 1)` of the sum survives
  have h2 : W.toSquareBlockProp (b · = a) = scalar _ (X ^ (f - 1) : R[X]) := by
    ext r c : 1
    simp only [W, cyclicColumnOp, toSquareBlockProp_def, of_apply, c.2, ite_true,
      Matrix.sum_apply, hxy]
    rw [Finset.sum_eq_single (f - 1)]
    · simp [Matrix.one_apply, diagonal_apply, Subtype.ext_iff]
    · intro i hi hne
      rw [pow_apply_eq_zero_of_ne_add hM, map_zero, mul_zero]
      rw [r.2, c.2, ne_eq, left_eq_add, ZMod.natCast_eq_zero_iff]
      have := Finset.mem_range.mp hi
      exact fun hdvd ↦ hne (by have := Nat.le_of_dvd (by omega) hdvd; omega)
    · simp [NeZero.pos f]
  rw [h1, h2, det_one, mul_one, scalar_apply, det_diagonal, Finset.prod_const,
    Finset.card_univ, ← pow_mul]

private lemma det_charmatrix_mul_cyclicColumnOp [NeZero f]
    (hM : ∀ r c, b r ≠ b c + 1 → M r c = 0) (a : ZMod f) :
    (charmatrix M * cyclicColumnOp M b a).det =
      X ^ Fintype.card {r // b r ≠ a} * expand R f ((M ^ f).toSquareBlock b a).charpoly := by
  set x : Matrix ι ι R[X] := scalar ι (X : R[X])
  set y : Matrix ι ι R[X] := M.map C
  -- `(x - y) * ∑ x ^ i y ^ (f - 1 - i) = x ^ f - y ^ f`, so that the product replaces the columns
  -- of the block at `a` by those of `x ^ f - y ^ f`
  have hG : charmatrix M * ∑ i ∈ Finset.range f, x ^ i * y ^ (f - 1 - i) = x ^ f - y ^ f :=
    (scalar_commute _ (fun _ ↦ commute_X _) _).mul_geom_sum₂ f
  have hQ : charmatrix M * cyclicColumnOp M b a =
      of fun r c ↦ if b c = a then (x ^ f - y ^ f) r c else charmatrix M r c := by
    ext r c : 1
    by_cases hc : b c = a
    · simp only [Matrix.mul_apply, cyclicColumnOp, of_apply, hc, ite_true]
      rw [← hG, Matrix.mul_apply]
    · simp [Matrix.mul_apply, cyclicColumnOp, hc, Matrix.one_apply]
  have hx : x ^ f = scalar ι (X ^ f : R[X]) := (map_pow (scalar ι) X f).symm
  have hy : y ^ f = (M ^ f).map C := (M.map_pow C f).symm
  rw [hQ, twoBlockTriangular_det _ (b · = a) fun r hr c hc ↦ ?_, mul_comm]
  · congr 1
    · rw [← charpoly_toSquareBlockProp_ne hM a]
      congr 1
      ext r c : 1
      by_cases h : r = c
      · subst h
        simp [toSquareBlockProp_def, r.2]
      · simp [toSquareBlockProp_def, c.2, charmatrix_apply_ne _ _ _ h,
          charmatrix_apply_ne _ _ _ (Subtype.coe_injective.ne h)]
    · rw [expand_charpoly]
      congr 1
      ext r c : 1
      simp [toSquareBlockProp_def, toSquareBlock_def, c.2, hx, hy, diagonal_apply,
        Subtype.ext_iff]
  · have hrc : r ≠ c := fun h ↦ hr (h ▸ hc)
    have hf : (M ^ f) r c = 0 :=
      pow_apply_eq_zero_of_ne_add hM f (by rwa [hc, ZMod.natCast_self, add_zero])
    simp [hc, hx, hy, diagonal_apply_ne _ hrc, hf]

/-- **Cyclic block determinant.** Suppose that `M` maps the block `b ⁻¹' {j}` into the block
`b ⁻¹' {j + 1}` for every `j : ZMod f`, so that `M ^ f` preserves each block. Up to powers of `X`
accounting for the sizes of the blocks, the characteristic polynomial of `M` is that of the block
of `M ^ f` at any `a`, with `X ^ f` substituted for `X`. -/
theorem X_pow_mul_charpoly_eq_X_pow_mul_expand [NeZero f]
    (hM : ∀ r c, b r ≠ b c + 1 → M r c = 0) (a : ZMod f) :
    X ^ ((f - 1) * Fintype.card {r // b r = a}) * M.charpoly =
      X ^ Fintype.card {r // b r ≠ a} * expand R f ((M ^ f).toSquareBlock b a).charpoly := by
  rw [mul_comm, charpoly, ← det_cyclicColumnOp hM a, ← det_mul,
    det_charmatrix_mul_cyclicColumnOp hM a]

end Matrix

namespace LinearMap

open Module Set

section Semiring

variable {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M] {F : Module.End R M}

/-- If `F` maps `V i` into `V (i + 1)` for every `i`, then `F ^ k` maps `V i` into `V (i + k)`. -/
theorem mapsTo_pow_add_natCast {G : Type*} [AddMonoidWithOne G] {V : G → Submodule R M}
    (hF : ∀ i, MapsTo F (V i) (V (i + 1))) (k : ℕ) (i : G) :
    MapsTo (F ^ k) (V i) (V (i + k)) := by
  induction k generalizing i with
  | zero => simpa using mapsTo_id _
  | succ k ih =>
    intro x hx
    rw [pow_succ', mul_apply_eq_comp, Nat.cast_succ, ← add_assoc]
    exact hF _ (ih i hx)

/-- If `F` maps `V i` into `V (i + 1)` for every `i : ZMod f`, then `F ^ f` maps each `V i` into
itself. -/
theorem mapsTo_pow_self {f : ℕ} {V : ZMod f → Submodule R M}
    (hF : ∀ i, MapsTo F (V i) (V (i + 1))) (i : ZMod f) :
    MapsTo (F ^ f) (V i) (V i) := by
  simpa using mapsTo_pow_add_natCast hF f i

end Semiring

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {f : ℕ}
  {V : ZMod f → Submodule R M} {F : Module.End R M} [Module.Free R M] [Module.Finite R M]
  [∀ i, Module.Free R (V i)] [∀ i, Module.Finite R (V i)]

/-- **Cyclic block determinant.** Let `M` be the internal direct sum of `V i` for `i : ZMod f`, and
let `F` map each `V i` into `V (i + 1)`. Up to powers of `X` accounting for the ranks, the
characteristic polynomial of `F` is that of the restriction of `F ^ f` to any `V a`, with `X ^ f`
substituted for `X`. -/
theorem X_pow_mul_charpoly_eq_X_pow_mul_expand [NeZero f] (hV : DirectSum.IsInternal V)
    (hF : ∀ i, MapsTo F (V i) (V (i + 1))) (a : ZMod f) :
    X ^ ((f - 1) * finrank R (V a)) * F.charpoly =
      X ^ (finrank R M - finrank R (V a)) *
        expand R f ((F ^ f).restrict (mapsTo_pow_self hF a)).charpoly := by
  nontriviality R
  let v i := Module.Free.chooseBasis R (V i)
  let B := hV.collectedBasis v
  have hM : ∀ r c, r.1 ≠ c.1 + 1 → toMatrix B B F r c = 0 := fun r c h ↦ by
    rw [toMatrix_apply]
    exact hV.collectedBasis_repr_of_mem_ne v (Ne.symm h) (hF c.1 (hV.collectedBasis_mem v c))
  have hblock : ((toMatrix B B F ^ f).toSquareBlock Sigma.fst a).charpoly =
      ((F ^ f).restrict (mapsTo_pow_self hF a)).charpoly := by
    rw [← charpoly_toMatrix _ (v a), ← Matrix.charpoly_reindex (Equiv.sigmaSubtype a), toMatrix_pow]
    congr 1
    ext p q
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.toSquareBlock_def,
      Matrix.of_apply, toMatrix_apply, B, hV.collectedBasis_coe]
    -- `(Equiv.sigmaSubtype a).symm p` unfolds to the index `⟨⟨a, p⟩, rfl⟩`
    exact (hV.collectedBasis_repr_of_mem v (mapsTo_pow_self hF a (v a q).2)).trans
      (congr_arg (fun x ↦ (v a).repr x p) (Subtype.ext (coe_restrict_apply _ _).symm))
  have hcard : Fintype.card {r : Σ i, Free.ChooseBasisIndex R (V i) // r.1 = a} =
      finrank R (V a) := by
    rw [Fintype.card_congr (Equiv.sigmaSubtype a), Module.finrank_eq_card_chooseBasisIndex]
  have hcard' : Fintype.card {r : Σ i, Free.ChooseBasisIndex R (V i) // r.1 ≠ a} =
      finrank R M - finrank R (V a) := by
    rw [Fintype.card_subtype_compl, hcard, ← finrank_eq_card_basis B]
  rw [← charpoly_toMatrix F B, ← hblock, ← hcard', ← hcard]
  exact Matrix.X_pow_mul_charpoly_eq_X_pow_mul_expand hM a

/-- **Cyclic block determinant**, equal-rank case. Let `M` be the internal direct sum of the
equal-rank submodules `V i` for `i : ZMod f`, and let `F` map each `V i` into `V (i + 1)`. Then the
characteristic polynomial of `F` is that of the restriction of `F ^ f` to any `V a`, with `X ^ f`
substituted for `X`. -/
theorem charpoly_eq_expand_charpoly_restrict_pow [NeZero f] (hV : DirectSum.IsInternal V)
    (hF : ∀ i, MapsTo F (V i) (V (i + 1))) (hrank : ∀ i j, finrank R (V i) = finrank R (V j))
    (a : ZMod f) :
    F.charpoly = expand R f ((F ^ f).restrict (mapsTo_pow_self hF a)).charpoly := by
  nontriviality R
  have hM : finrank R M = f * finrank R (V a) := by
    rw [finrank_eq_card_basis (hV.collectedBasis fun i ↦ Free.chooseBasis R (V i)),
      Fintype.card_sigma]
    simp [← Module.finrank_eq_card_chooseBasisIndex, hrank _ a]
  have h := X_pow_mul_charpoly_eq_X_pow_mul_expand hV hF a
  rw [hM, ← Nat.pred_mul, Nat.pred_eq_sub_one] at h
  exact (isRegular_X_pow _).left.eq_iff.mp h

/-- In the equal-rank case, the characteristic polynomial of the restriction of `F ^ f` to `V i`
does not depend on the starting summand `i`. -/
theorem charpoly_restrict_pow_eq [NeZero f] (hV : DirectSum.IsInternal V)
    (hF : ∀ i, MapsTo F (V i) (V (i + 1))) (hrank : ∀ i j, finrank R (V i) = finrank R (V j))
    (i j : ZMod f) :
    ((F ^ f).restrict (mapsTo_pow_self hF i)).charpoly =
      ((F ^ f).restrict (mapsTo_pow_self hF j)).charpoly :=
  expand_injective (NeZero.pos f) <| by
    rw [← charpoly_eq_expand_charpoly_restrict_pow hV hF hrank i,
      ← charpoly_eq_expand_charpoly_restrict_pow hV hF hrank j]

end LinearMap

open Matrix in
/-- A check of the cyclic formula at `f = 2` with trivial rank-one return map: the transposition
matrix has characteristic polynomial `X ^ 2 - 1`, with roots `±1`, rather than `(X - 1) ^ 2`. -/
example : (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℤ).charpoly = X ^ 2 - 1 := by
  have hM : ∀ r c : Fin 2, ((r : ℕ) : ZMod 2) ≠ ((c : ℕ) : ZMod 2) + 1 →
      (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℤ) r c = 0 := by
    simp only [Fin.forall_fin_two]
    decide
  have h := X_pow_mul_charpoly_eq_X_pow_mul_expand hM 0
  have hsq : (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℤ) ^ 2 = 1 := by decide
  have hb : (1 : Matrix (Fin 2) (Fin 2) ℤ).toSquareBlock (fun r ↦ ((r : ℕ) : ZMod 2)) 0 = 1 := by
    ext r c
    simp [toSquareBlock_def, Matrix.one_apply, Subtype.ext_iff]
  have h1 : Fintype.card {r : Fin 2 // ((r : ℕ) : ZMod 2) = 0} = 1 := by decide
  have h2 : Fintype.card {r : Fin 2 // ((r : ℕ) : ZMod 2) ≠ 0} = 1 := by decide
  rw [hsq, hb, charpoly_one, h1, h2] at h
  simpa using h
