/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.AffineMonoid.UniqueSums
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import TauCeti.GroupTheory.Finiteness
public import TauCeti.RingTheory.Localization.FractionRing
public import TauCeti.RingTheory.NovikovSeries.FiniteIndex
public import TauCeti.RingTheory.NovikovSeries.LeadingTerm

/-!
# Non-zero-divisors of the group ring among Novikov series

Let `H` be a finitely generated abelian group, `N : H →+ ℝ` a period homomorphism and `R` a ring
without zero divisors. The group ring `R[H]` embeds into the Novikov ring `Nov(R, H, N)`
(`TauCeti.NovikovSeries.ofAddMonoidAlgebra`). When `H` has torsion, neither ring is a domain, so
it is not automatic that a non-zero-divisor of `R[H]` remains one in `Nov(R, H, N)`. This file
proves that it does (`TauCeti.NovikovSeries.ofAddMonoidAlgebra_mem_nonZeroDivisors`). Hence the
embedding induces an injective map from the total quotient ring of `R[H]` to that of
`Nov(R, H, N)` (`TauCeti.NovikovSeries.map_ofAddMonoidAlgebra_injective`). Torsion of a based
complex over `ℤ[H]`, which lives in the total quotient ring of `ℤ[H]`, is compared with torsion
over the Novikov ring through this map.

The proof passes to a finite-index subgroup `K ≤ H` whose group ring has no zero divisors; for
finitely generated `H`, a torsion-free subgroup of finite index exists
(`TauCeti.AddCommGroup.exists_finiteIndex_isAddTorsionFree`). Then `Nov(R, K, N|K)` is a domain
and `Nov(R, H, N)` is free over it with the basis of coset monomials
(`TauCeti.NovikovSeries.cosetBasis`). Let `a ∈ R[H]` and let `A` be the matrix of multiplication
by `a` in this basis. Its entries are finitely supported, so `A` comes from a matrix `A₀` over
`R[K]`. If `det A₀ = 0`, a nonzero vector in the kernel of `A₀` gives a nonzero element `y` of
`R[H]` with `a * y = 0`. So when `a` is a non-zero-divisor, `det A₀ ≠ 0`, and therefore
`det A ≠ 0`, since `R[K]` embeds into `Nov(R, K, N|K)`. Over the domain `Nov(R, K, N|K)`, a matrix
with nonzero determinant has trivial kernel, so multiplication by `a` is injective on
`Nov(R, H, N)`.

## Main results

* `TauCeti.NovikovSeries.ofAddMonoidAlgebra_mem_nonZeroDivisors_of_finiteIndex`: if `K` is a
  finite-index subgroup with `R[K]` free of zero divisors, the embedding of `R[H]` preserves
  non-zero-divisors.
* `TauCeti.NovikovSeries.ofAddMonoidAlgebra_mem_nonZeroDivisors`: the same for every finitely
  generated `H`.
* `TauCeti.NovikovSeries.map_ofAddMonoidAlgebra_injective`: the induced map of total quotient
  rings is injective.

## References

* V. Turaev, *Introduction to Combinatorial Torsions*, Birkhäuser 2001, Chapter I.
* M. Hutchings, *Reidemeister torsion in generalized Morse theory*, Forum Math. 14 (2002),
  Section 2.
-/

public section

noncomputable section

open scoped nonZeroDivisors

namespace TauCeti

namespace NovikovSeries

variable {R H : Type*} [CommRing R] [AddCommGroup H] {N : H →+ ℝ}

section FiniteIndex

variable (K : AddSubgroup H) [K.FiniteIndex] (s : H ⧸ K → H) (hs : ∀ q, (s q : H ⧸ K) = q)

/-- In the coset basis, the coordinates of a series from the group ring `R[H]` come from `R[K]`. -/
private theorem cosetBasis_repr_mem_range {y : NovikovSeries R H N}
    (hy : y ∈ Set.range ofAddMonoidAlgebra) (q : H ⧸ K) :
    (cosetBasis K s hs).repr y q ∈ Set.range ofAddMonoidAlgebra := by
  rw [mem_range_ofAddMonoidAlgebra_iff] at hy ⊢
  exact (finite_support_iff_forall_finite_support_cosetBasis_repr K s hs y).1 hy q

/-- A series whose coordinates in the coset basis come from `R[K]` comes from `R[H]`. -/
private theorem cosetBasis_equivFun_symm_mem_range (v : H ⧸ K → AddMonoidAlgebra R K) :
    (cosetBasis K s hs).equivFun.symm (ofAddMonoidAlgebra ∘ v) ∈
      Set.range (ofAddMonoidAlgebra : AddMonoidAlgebra R H → NovikovSeries R H N) := by
  rw [mem_range_ofAddMonoidAlgebra_iff,
    finite_support_iff_forall_finite_support_cosetBasis_repr K s hs]
  intro q
  rw [← mem_range_ofAddMonoidAlgebra_iff, ← Module.Basis.equivFun_apply,
    LinearEquiv.apply_symm_apply]
  exact Set.mem_range_self _

/-- In the coset basis, the matrix of multiplication by an element of `R[H]` is the image of a
matrix over `R[K]`. -/
private theorem exists_leftMulMatrix_cosetBasis_eq_mapMatrix [Fintype (H ⧸ K)]
    [DecidableEq (H ⧸ K)] (a : AddMonoidAlgebra R H) :
    ∃ A : Matrix (H ⧸ K) (H ⧸ K) (AddMonoidAlgebra R K),
      Algebra.leftMulMatrix (cosetBasis K s hs) (ofAddMonoidAlgebra a : NovikovSeries R H N) =
        (ofAddMonoidAlgebra : AddMonoidAlgebra R K →+* _).mapMatrix A := by
  choose A hA using fun i j => cosetBasis_repr_mem_range K s hs
    (y := (ofAddMonoidAlgebra a : NovikovSeries R H N) * cosetBasis K s hs j) (by
      rw [cosetBasis_apply, ← ofAddMonoidAlgebra_single, ← _root_.map_mul]
      exact Set.mem_range_self _) i
  refine ⟨.of A, Matrix.ext fun i j => ?_⟩
  rw [Algebra.leftMulMatrix_eq_repr_mul, RingHom.mapMatrix_apply, Matrix.map_apply,
    Matrix.of_apply, hA]

/-- If `K` is a subgroup of finite index whose group ring `R[K]` has no zero divisors, then a
non-zero-divisor of the group ring `R[H]` is still a non-zero-divisor among the Novikov series. -/
theorem ofAddMonoidAlgebra_mem_nonZeroDivisors_of_finiteIndex
    [NoZeroDivisors (AddMonoidAlgebra R K)] {a : AddMonoidAlgebra R H}
    (ha : a ∈ (AddMonoidAlgebra R H)⁰) :
    (ofAddMonoidAlgebra a : NovikovSeries R H N) ∈ (NovikovSeries R H N)⁰ := by
  classical
  refine mem_nonZeroDivisors_iff_left.2 fun x hx => ?_
  rcases subsingleton_or_nontrivial R with hR | hR
  · ext h
    exact Subsingleton.elim _ _
  have := Fintype.ofFinite (H ⧸ K)
  have : IsDomain (AddMonoidAlgebra R K) := NoZeroDivisors.to_isDomain _
  let b := cosetBasis (R := R) (N := N) K Quotient.out QuotientAddGroup.out_eq'
  let ι : AddMonoidAlgebra R K →+* NovikovSeries R K (N.comp K.subtype) := ofAddMonoidAlgebra
  obtain ⟨A, hA⟩ := exists_leftMulMatrix_cosetBasis_eq_mapMatrix (N := N) K Quotient.out
    QuotientAddGroup.out_eq' a
  -- a vector in the kernel of `A` gives an element of `R[H]` annihilated by `a`
  have hdet : A.det ≠ 0 := by
    intro h0
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    obtain ⟨y, hy⟩ := cosetBasis_equivFun_symm_mem_range (N := N) K Quotient.out
      QuotientAddGroup.out_eq' v
    have hay : a * y = 0 := by
      refine ofAddMonoidAlgebra_injective (N := N) ?_
      rw [_root_.map_mul, map_zero, hy]
      refine b.equivFun.injective ?_
      rw [map_zero, Module.Basis.equivFun_apply, ← Algebra.leftMulMatrix_mulVec_repr,
        ← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply, hA, RingHom.mapMatrix_apply]
      ext q
      rw [← RingHom.map_mulVec, hv, Pi.zero_apply, map_zero, Pi.zero_apply]
    have hy0 : ι ∘ v = 0 := b.equivFun.symm.injective
      (by rw [← hy, mem_nonZeroDivisors_iff_left.1 ha y hay, map_zero, map_zero])
    exact hv0 (funext fun q => ofAddMonoidAlgebra_injective (N := N.comp K.subtype)
      ((congrFun hy0 q).trans (map_zero ι).symm))
  -- over the domain `Nov(R, K, N|K)`, the matrix of multiplication by `a` has trivial kernel
  by_contra hx0
  refine ((injective_iff_map_eq_zero' ι).1 ofAddMonoidAlgebra_injective _).not.2 hdet ?_
  rw [RingHom.map_det, ← hA, ← Matrix.exists_mulVec_eq_zero_iff]
  exact ⟨b.repr x, by simpa using hx0,
    by rw [Algebra.leftMulMatrix_mulVec_repr, hx, map_zero, Finsupp.coe_zero]⟩

end FiniteIndex

variable [NoZeroDivisors R] [AddGroup.FG H]

/-- For a finitely generated abelian group `H` and a coefficient ring without zero divisors, a
non-zero-divisor of the group ring `R[H]` is still a non-zero-divisor among the Novikov series. -/
theorem ofAddMonoidAlgebra_mem_nonZeroDivisors {a : AddMonoidAlgebra R H}
    (ha : a ∈ (AddMonoidAlgebra R H)⁰) :
    (ofAddMonoidAlgebra a : NovikovSeries R H N) ∈ (NovikovSeries R H N)⁰ := by
  obtain ⟨K, hK, hKtf⟩ := AddCommGroup.exists_finiteIndex_isAddTorsionFree H
  have : AddMonoid.FG K := AddGroup.fg_iff_addMonoid_fg.1 inferInstance
  have : HasUniqueDiv K := IsAddTorsionFree.hasUniqueDiv
  exact ofAddMonoidAlgebra_mem_nonZeroDivisors_of_finiteIndex K ha

/-- The embedding of the group ring into the Novikov ring maps non-zero-divisors to
non-zero-divisors. -/
theorem nonZeroDivisors_le_comap_ofAddMonoidAlgebra :
    (AddMonoidAlgebra R H)⁰ ≤ (NovikovSeries R H N)⁰.comap ofAddMonoidAlgebra :=
  fun _ => ofAddMonoidAlgebra_mem_nonZeroDivisors

/-- The embedding of the group ring into the Novikov ring induces an injective map from the total
quotient ring of `R[H]` to that of `Nov(R, H, N)`. -/
theorem map_ofAddMonoidAlgebra_injective (Q Q' : Type*) [CommRing Q] [CommRing Q']
    [Algebra (AddMonoidAlgebra R H) Q] [IsFractionRing (AddMonoidAlgebra R H) Q]
    [Algebra (NovikovSeries R H N) Q'] [IsFractionRing (NovikovSeries R H N) Q'] :
    Function.Injective
      (IsLocalization.map Q' (ofAddMonoidAlgebra : AddMonoidAlgebra R H →+* NovikovSeries R H N)
        nonZeroDivisors_le_comap_ofAddMonoidAlgebra : Q →+* Q') :=
  IsLocalization.map_injective_of_injective_of_le_nonZeroDivisors Q Q'
    ofAddMonoidAlgebra_injective _ le_rfl

end NovikovSeries

end TauCeti
