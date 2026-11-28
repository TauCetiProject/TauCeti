/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Charpoly.ToMatrix
public import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.FieldTheory.SplittingField.Construction
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import TauCeti.Algebra.Polynomial.Bezout
import TauCeti.LinearAlgebra.Charpoly.Quotient
import TauCeti.LinearAlgebra.Matrix.ToLin

/-!
# A coprime factorisation of the characteristic polynomial

Let `f` be an endomorphism of a finite-dimensional vector space `V` over a field `K` whose
characteristic polynomial is a product `A * B` of coprime polynomials. Then `V` is the direct sum
of the kernels of `A(f)` and `B(f)`, and the restriction of `f` to the kernel of `A(f)` has
characteristic polynomial `A` up to a unit, so this kernel has dimension `deg A`. For a Bézout
relation `u * A + v * B = 1`, the polynomial `v * B` evaluated at `f` is the projection onto the
kernel of `A(f)` along the kernel of `B(f)`. No hypothesis on the characteristic of `K` is needed.

For a square matrix `y` with characteristic polynomial `A * B`, the idempotent `(v * B)(y)`
therefore has rank `deg A`. Two idempotent matrices of the same rank over a field are conjugate,
so `(v * B)(y)` is conjugate to the diagonal projector onto any set of `deg A` coordinates.

The key input is that `p(f)` is invertible exactly when `p` is coprime to the characteristic
polynomial of `f` (`LinearMap.isUnit_aeval_iff_isCoprime_charpoly`): a common root of the two in
a domain would be an eigenvalue of `f` after extension of scalars, with an eigenvector killed by
`p(f)`.

This is the linear algebra behind the slice of block diagonal elements used to show that
invariant distributions supported on elements whose characteristic polynomial has two coprime
factors vanish on test functions that are cuspidal at a split place (the simple trace formula,
after Deligne and Kazhdan). The statements `Polynomial.isIdempotentElem_aeval_mul_of_add_eq_one`,
`Matrix.rank_aeval_mul_of_charpoly_eq_mul` and `Matrix.exists_semiconjBy_diagonal_aeval_mul`
correspond to `New.isIdempotentElem_aeval_of_charpoly_eq`, `New.rank_aeval_eq_natDegree` and the
conjugation step of `New.isSlice_blockLocus` in `src/Lib/Adelic/TraceFormula/CoprimeFactors.lean`
of grh-lean (<https://github.com/lsernau/grh-lean>, Apache 2.0, Copyright 2026 Anthropic, PBC),
where the rank is computed from traces over an algebraic closure in characteristic zero. Here it is
computed as the dimension of a kernel, over any field.

## Main results

* `Matrix.isUnit_aeval_iff_isCoprime_charpoly`, `LinearMap.isUnit_aeval_iff_isCoprime_charpoly`:
  `p(f)` is invertible if and only if `p` is coprime to the characteristic polynomial of `f`.
* `Module.End.isCompl_ker_aeval_of_isCoprime`: if `(A * B)(f) = 0` with `A`, `B` coprime, the
  kernels of `A(f)` and `B(f)` are complements.
* `Module.End.range_aeval_mul_eq_ker_aeval`: for `u * A + v * B = 1` and `(A * B)(f) = 0`, the
  idempotent `(v * B)(f)` has range the kernel of `A(f)`.
* `LinearMap.associated_charpoly_restrict_ker_aeval`,
  `LinearMap.charpoly_restrict_ker_aeval`: if the characteristic polynomial of `f` is `A * B`
  with `A`, `B` coprime, the restriction of `f` to the kernel of `A(f)` has characteristic
  polynomial associated to `A`, and equal to `A` when `A` is monic.
* `LinearMap.finrank_ker_aeval_of_charpoly_eq_mul`: that kernel has dimension `deg A`.
* `Matrix.rank_aeval_mul_of_charpoly_eq_mul`: for a matrix `y` with characteristic polynomial
  `A * B`, the idempotent `(v * B)(y)` has rank `deg A`.
* `Module.End.exists_linearEquiv_semiconjBy_of_isIdempotentElem`,
  `Matrix.exists_semiconjBy_of_isIdempotentElem`: idempotents of equal rank are conjugate.
* `Matrix.exists_semiconjBy_diagonal_aeval_mul`: `(v * B)(y)` is conjugate to the diagonal
  projector onto any set of `deg A` coordinates.
-/

public section

open Polynomial Module

/-! ### Invertible values of polynomials and coprimality -/

namespace Matrix

variable {K n : Type*} [Field K] [Fintype n] [DecidableEq n]

/-- `p(M)` is invertible if and only if `p` is coprime to the characteristic polynomial of `M`. -/
theorem isUnit_aeval_iff_isCoprime_charpoly {M : Matrix n n K} {p : K[X]} :
    IsUnit (aeval M p) ↔ IsCoprime M.charpoly p := by
  refine ⟨fun hp ↦ ?_, isUnit_aeval_of_isCoprime (aeval_self_charpoly M)⟩
  -- A common root `a` of `charpoly M` and `p` in a domain `L` is an eigenvalue of `M` over `L`.
  rw [isCoprime_iff_aeval_ne_zero]
  intro L _ _ _ a
  by_contra! h
  set M' : Matrix n n L := M.map (algebraMap K L)
  have hdet : (scalar n a - M').det = 0 := by
    rw [← eval_charpoly, charpoly_map, eval_map_algebraMap, h.1]
  obtain ⟨v, hv0, hv⟩ := exists_mulVec_eq_zero_iff.2 hdet
  have heig : Module.End.HasEigenvector (toLinAlgEquiv' M') a v := by
    refine ⟨?_, hv0⟩
    rw [Module.End.mem_eigenspace_iff, toLinAlgEquiv'_apply, eq_comm, ← sub_eq_zero]
    simpa [sub_mulVec, scalar_apply, smul_eq_diagonal_mul] using hv
  -- `p` vanishes at the eigenvalue `a`, so `p(M')` kills the eigenvector `v`.
  have hker : aeval M' p *ᵥ v = 0 := by
    have hE := Module.End.aeval_apply_of_hasEigenvector (p := p.map (algebraMap K L)) heig
    rw [aeval_algHom_apply, toLinAlgEquiv'_apply, aeval_map_algebraMap] at hE
    rwa [eval_map_algebraMap, h.2, zero_smul] at hE
  -- But `p(M')` is the image of the invertible matrix `p(M)`.
  have hpM' : aeval M' p = (Algebra.ofId K L).mapMatrix (aeval M p) := by
    have hcoe : ⇑(Algebra.ofId K L) = algebraMap K L := funext fun r ↦ Algebra.ofId_apply L r
    simpa [M', hcoe] using aeval_algHom_apply (Algebra.ofId K L).mapMatrix M p
  obtain ⟨u, hu⟩ := hp.map (Algebra.ofId K L).mapMatrix
  apply hv0
  calc v = (↑u⁻¹ * ↑u : Matrix n n L) *ᵥ v := by rw [Units.inv_mul, one_mulVec]
    _ = ↑u⁻¹ *ᵥ (aeval M' p *ᵥ v) := by rw [← mulVec_mulVec, hpM', hu]
    _ = 0 := by rw [hker, mulVec_zero]

end Matrix

namespace LinearMap

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- `p(f)` is invertible if and only if `p` is coprime to the characteristic polynomial of `f`. -/
theorem isUnit_aeval_iff_isCoprime_charpoly {f : Module.End K V} {p : K[X]} :
    IsUnit (aeval f p) ↔ IsCoprime f.charpoly p := by
  refine ⟨fun hp ↦ ?_, isUnit_aeval_of_isCoprime (aeval_self_charpoly f)⟩
  let b := Module.finBasis K V
  rw [← f.charpoly_toMatrix b]
  refine Matrix.isUnit_aeval_iff_isCoprime_charpoly.1 ?_
  have hb : toMatrix b b f = toMatrixAlgEquiv b f := by
    ext i j
    rw [toMatrix_apply, toMatrixAlgEquiv_apply]
  rw [hb, aeval_algEquiv, AlgHom.comp_apply]
  exact hp.map (toMatrixAlgEquiv b)

end LinearMap

/-! ### Kernels of the two factors -/

namespace Module.End

section CommSemiring

variable {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]

/-- The kernel of `p(f)` is invariant under `f`. -/
theorem mapsTo_ker_aeval (f : End R M) (p : R[X]) :
    ∀ x ∈ LinearMap.ker (aeval f p), f x ∈ LinearMap.ker (aeval f p) := by
  intro x hx
  have hc : Commute f (aeval f p) := by simpa using (commute_X p).map (aeval f)
  rw [LinearMap.mem_ker, ← mul_apply_eq_comp, ← hc.eq, mul_apply_eq_comp, LinearMap.mem_ker.1 hx,
    map_zero]

/-- Evaluating a polynomial at the restriction of `f` to an invariant submodule is the
restriction of its value at `f`. -/
@[simp]
theorem coe_aeval_restrict_apply (f : End R M) {N : Submodule R M} (hN : ∀ x ∈ N, f x ∈ N)
    (p : R[X]) (x : N) : (aeval (f.restrict hN) p x : M) = aeval f p x := by
  revert x
  induction p using Polynomial.induction_on with
  | C a => simp [algebraMap_end_apply]
  | add p q hp hq => simp [hp, hq]
  | monomial n a ih =>
    intro x
    -- Peel off the last factor `X`, which evaluates to `f.restrict hN` and to `f`.
    rw [show C a * X ^ (n + 1) = C a * X ^ n * X by ring, map_mul (aeval (f.restrict hN)),
      map_mul (aeval f), aeval_X, aeval_X]
    rw [mul_apply_eq_comp, mul_apply_eq_comp, ih, LinearMap.coe_restrict_apply]

end CommSemiring

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {f : End R M} {A B u v : R[X]}

/-- If `(A * B)(f) = 0` with `A` and `B` coprime, the kernels of `A(f)` and `B(f)` are
complementary submodules. -/
theorem isCompl_ker_aeval_of_isCoprime (hAB : IsCoprime A B) (hf : aeval f (A * B) = 0) :
    IsCompl (LinearMap.ker (aeval f A)) (LinearMap.ker (aeval f B)) := by
  refine ⟨disjoint_ker_aeval_of_isCoprime f hAB, codisjoint_iff.2 ?_⟩
  rw [sup_ker_aeval_eq_ker_aeval_mul_of_coprime f hAB, hf, LinearMap.ker_zero]

/-- If `u * A + v * B = 1` and `(A * B)(f) = 0`, the idempotent `(v * B)(f)` has the kernel of
`A(f)` as its range: it is the projection onto that kernel along the kernel of `B(f)`. -/
theorem range_aeval_mul_eq_ker_aeval (huv : u * A + v * B = 1) (hf : aeval f (A * B) = 0) :
    LinearMap.range (aeval f (v * B)) = LinearMap.ker (aeval f A) := by
  refine le_antisymm ?_ fun x hx ↦ ⟨x, ?_⟩
  · rintro _ ⟨x, rfl⟩
    rw [LinearMap.mem_ker, ← mul_apply_eq_comp, ← map_mul, show A * (v * B) = v * (A * B) by ring]
    simp [hf]
  · simpa [LinearMap.mem_ker.1 hx] using congrArg (fun g : End R M ↦ g x) (congrArg (aeval f) huv)

end Module.End

/-! ### The characteristic polynomial on the kernel of a coprime factor -/

namespace LinearMap

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {f : Module.End K V} {A B : K[X]}

/-- If `A` and `B` are coprime, the characteristic polynomial of `f` on the kernel of `A(f)` is
coprime to `B`: there `B(f)` is invertible. -/
theorem isCoprime_charpoly_restrict_ker_aeval (hAB : IsCoprime A B) :
    IsCoprime (f.restrict (Module.End.mapsTo_ker_aeval f A)).charpoly B := by
  rw [← isUnit_aeval_iff_isCoprime_charpoly]
  refine isUnit_aeval_of_isCoprime (LinearMap.ext fun x ↦ Subtype.ext ?_) hAB
  rw [Module.End.coe_aeval_restrict_apply, LinearMap.zero_apply, ZeroMemClass.coe_zero]
  exact LinearMap.mem_ker.1 x.property

/-- If the characteristic polynomial of `f` is `A * B` with `A` and `B` coprime, then the
characteristic polynomial of `f` on the kernel of `A(f)` is associated to `A`. -/
theorem associated_charpoly_restrict_ker_aeval (hf : f.charpoly = A * B) (hAB : IsCoprime A B) :
    Associated (f.restrict (Module.End.mapsTo_ker_aeval f A)).charpoly A := by
  set F := f.restrict (Module.End.mapsTo_ker_aeval f A)
  set G := f.restrict (Module.End.mapsTo_ker_aeval f B)
  have hAB0 : A * B ≠ 0 := hf ▸ f.charpoly_monic.ne_zero
  have hA0 : A ≠ 0 := left_ne_zero_of_mul hAB0
  have hB0 : B ≠ 0 := right_ne_zero_of_mul hAB0
  -- Both restricted characteristic polynomials divide `A * B`.
  have hFdvd : F.charpoly ∣ A * B := hf ▸ charpoly_dvd_of_injective_of_comp_eq_comp F f
    (Submodule.subtype _) Subtype.val_injective (by ext; simp [F])
  have hGdvd : G.charpoly ∣ A * B := hf ▸ charpoly_dvd_of_injective_of_comp_eq_comp G f
    (Submodule.subtype _) Subtype.val_injective (by ext; simp [G])
  have hFA : F.charpoly ∣ A :=
    (isCoprime_charpoly_restrict_ker_aeval hAB).dvd_of_dvd_mul_right hFdvd
  have hGB : G.charpoly ∣ B :=
    (isCoprime_charpoly_restrict_ker_aeval hAB.symm).dvd_of_dvd_mul_left hGdvd
  -- The two kernels are complementary, so the degrees add up to `deg A + deg B`.
  have hcompl := Module.End.isCompl_ker_aeval_of_isCoprime hAB (hf ▸ aeval_self_charpoly f)
  have hdeg : F.charpoly.natDegree + G.charpoly.natDegree = A.natDegree + B.natDegree := by
    rw [charpoly_natDegree, charpoly_natDegree, Submodule.finrank_add_eq_of_isCompl hcompl,
      ← natDegree_mul hA0 hB0, ← hf, charpoly_natDegree]
  have hFle := natDegree_le_of_dvd hFA hA0
  have hGle := natDegree_le_of_dvd hGB hB0
  exact associated_of_dvd_of_natDegree_le hFA hA0 (by omega)

/-- If the characteristic polynomial of `f` is `A * B` with `A` and `B` coprime and `A` monic,
then the characteristic polynomial of `f` on the kernel of `A(f)` is `A`. -/
theorem charpoly_restrict_ker_aeval (hf : f.charpoly = A * B) (hAB : IsCoprime A B)
    (hA : A.Monic) : (f.restrict (Module.End.mapsTo_ker_aeval f A)).charpoly = A :=
  eq_of_monic_of_associated (charpoly_monic _) hA (associated_charpoly_restrict_ker_aeval hf hAB)

/-- If the characteristic polynomial of `f` is `A * B` with `A` and `B` coprime, the kernel of
`A(f)` has dimension `deg A`. -/
theorem finrank_ker_aeval_of_charpoly_eq_mul (hf : f.charpoly = A * B) (hAB : IsCoprime A B) :
    finrank K (LinearMap.ker (aeval f A)) = A.natDegree := by
  rw [← charpoly_natDegree (f.restrict (Module.End.mapsTo_ker_aeval f A)),
    natDegree_eq_of_degree_eq (degree_eq_degree_of_associated
      (associated_charpoly_restrict_ker_aeval hf hAB))]

end LinearMap

/-! ### Conjugacy of idempotents of equal rank -/

namespace Module.End

variable {K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- Two idempotent endomorphisms of a finite-dimensional vector space with ranges of the same
dimension are conjugate. -/
theorem exists_linearEquiv_semiconjBy_of_isIdempotentElem {p q : End K V} (hp : IsIdempotentElem p)
    (hq : IsIdempotentElem q) (h : finrank K (LinearMap.range q) = finrank K (LinearMap.range p)) :
    ∃ e : V ≃ₗ[K] V, SemiconjBy (e : End K V) q p := by
  have hcp := LinearMap.IsIdempotentElem.isCompl hp
  have hcq := LinearMap.IsIdempotentElem.isCompl hq
  have hk : finrank K (LinearMap.ker q) = finrank K (LinearMap.ker p) := by
    have h1 := Submodule.finrank_add_eq_of_isCompl hcp
    have h2 := Submodule.finrank_add_eq_of_isCompl hcq
    omega
  -- Bases adapted to `V = range q ⊕ ker q` and `V = range p ⊕ ker p`, with the same index type.
  let bq := ((finBasisOfFinrankEq K _ rfl).prod (finBasisOfFinrankEq K _ rfl)).map
    (Submodule.prodEquivOfIsCompl _ _ hcq)
  let bp := ((finBasisOfFinrankEq K _ h.symm).prod (finBasisOfFinrankEq K _ hk.symm)).map
    (Submodule.prodEquivOfIsCompl _ _ hcp)
  let e := bq.equiv bp (Equiv.refl _)
  have he (i) : e (bq i) = bp i := by simp [e]
  refine ⟨e, bq.ext fun i ↦ ?_⟩
  rw [mul_apply_eq_comp, mul_apply_eq_comp, LinearEquiv.coe_coe, he]
  rcases i with i | i
  · rw [(LinearMap.IsIdempotentElem.mem_range_iff hq).1 (by simp [bq]), he,
      (LinearMap.IsIdempotentElem.mem_range_iff hp).1 (by simp [bp])]
  · rw [LinearMap.mem_ker.1 (show bq (.inr i) ∈ LinearMap.ker q by simp [bq]), map_zero,
      LinearMap.mem_ker.1 (show bp (.inr i) ∈ LinearMap.ker p by simp [bp])]

end Module.End

namespace Matrix

variable {K n : Type*} [Field K] [Fintype n] [DecidableEq n]

/-- Two idempotent matrices of the same rank are conjugate: `g * q = p * g` for some invertible
`g`. -/
theorem exists_semiconjBy_of_isIdempotentElem {p q : Matrix n n K} (hp : IsIdempotentElem p)
    (hq : IsIdempotentElem q) (h : q.rank = p.rank) :
    ∃ g : GL n K, SemiconjBy (g : Matrix n n K) q p := by
  have hidem {e : Matrix n n K} (he : IsIdempotentElem e) : IsIdempotentElem e.mulVecLin := by
    rw [IsIdempotentElem, Module.End.mul_eq_comp, ← mulVecLin_mul, he.eq]
  obtain ⟨e, he⟩ := Module.End.exists_linearEquiv_semiconjBy_of_isIdempotentElem (hidem hp)
    (hidem hq) (by rw [finrank_range_mulVecLin, finrank_range_mulVecLin, h])
  set g : GL n K := TauCeti.matrixLinearEquiv.symm e
  -- The matrix `g` acts on column vectors by `e`.
  have hg : (g : Matrix n n K).mulVecLin = e := LinearMap.ext fun x ↦ by
    have := TauCeti.matrixGeneralLinearEquiv_apply g x
    rw [← MulEquiv.trans_apply, MulEquiv.apply_symm_apply] at this
    rw [mulVecLin_apply, ← this, LinearEquiv.coe_coe]
  refine ⟨g, toLin'.injective ?_⟩
  rw [toLin'_mul, toLin'_mul, toLin'_apply', toLin'_apply', toLin'_apply', hg]
  exact he

variable {y : Matrix n n K} {A B u v : K[X]}

/-- If `y` has characteristic polynomial `A * B` and `u * A + v * B = 1`, the idempotent
`(v * B)(y)` has rank `deg A`. -/
theorem rank_aeval_mul_of_charpoly_eq_mul (hy : y.charpoly = A * B) (huv : u * A + v * B = 1) :
    (aeval y (v * B)).rank = A.natDegree := by
  -- Polynomials in `y` act on column vectors through the algebra isomorphism `toLinAlgEquiv'`.
  have hlin (M : Matrix n n K) : toLinAlgEquiv' M = M.mulVecLin :=
    LinearMap.ext (toLinAlgEquiv'_apply M)
  have hf : (toLinAlgEquiv' y).charpoly = A * B := by rw [hlin, charpoly_mulVecLin, hy]
  rw [← finrank_range_mulVecLin, ← hlin, ← aeval_algHom_apply,
    Module.End.range_aeval_mul_eq_ker_aeval huv (hf ▸ LinearMap.aeval_self_charpoly _),
    LinearMap.finrank_ker_aeval_of_charpoly_eq_mul hf ⟨u, v, huv⟩]

/-- If `y` has characteristic polynomial `A * B` and `u * A + v * B = 1`, the projection
`(v * B)(y)` onto the kernel of `A(y)` is conjugate to the diagonal projector onto any set `T` of
`deg A` coordinates: `g * diagonal 1_T = (v * B)(y) * g` for some invertible `g`. -/
theorem exists_semiconjBy_diagonal_aeval_mul (hy : y.charpoly = A * B) (huv : u * A + v * B = 1)
    {T : Finset n} (hT : T.card = A.natDegree) :
    ∃ g : GL n K, SemiconjBy (g : Matrix n n K) (diagonal fun i ↦ if i ∈ T then 1 else 0)
      (aeval y (v * B)) := by
  classical
  refine exists_semiconjBy_of_isIdempotentElem
    (Polynomial.isIdempotentElem_aeval_mul_of_add_eq_one huv (hy ▸ aeval_self_charpoly y))
    (by simp [IsIdempotentElem, diagonal_mul_diagonal]) ?_
  rw [rank_aeval_mul_of_charpoly_eq_mul hy huv, rank_diagonal, ← hT]
  simp [Fintype.card_subtype]

end Matrix
