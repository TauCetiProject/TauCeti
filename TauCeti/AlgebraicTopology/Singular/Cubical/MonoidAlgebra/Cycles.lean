/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Cubical.ChainComplex
public import TauCeti.AlgebraicTopology.Singular.Cubical.MonoidAlgebra.Bimodule
public import TauCeti.Algebra.Homology.ModuleCat.Basic

/-!
# Products and actions of cubical cycles

Let `G` be a topological monoid acting continuously on a space `Y` from the left. The left action of
the normalized cubical chains of `G` on those of `Y` satisfies the Leibniz rule with the Koszul sign
`(-1) ^ p` (`TauCeti.NormalizedCubicalChain.boundary_leftAct`). This file reads it on the normalized
cubical chain complexes, where it needs no reindexing: for a cycle `z` of degree `q` and a chain `c`
of degree `m + 1`, the differential of `z · c` is `(-1) ^ q • z · ∂ c`
(`TauCeti.NormalizedCubicalChain.d_leftAct_of_d_eq_zero`). In particular the Pontryagin product of
two cycles of `G` is a cycle (`TauCeti.NormalizedCubicalChain.d_mul_eq_zero`), so it is defined on
the cycles of the normalized cubical chain complex of `G`
(`TauCeti.NormalizedCubicalChain.mulCycles`).

## Main definitions and results

* `TauCeti.NormalizedCubicalChain.d_leftAct_of_d_eq_zero`: the differential of the action of a
  cycle.
* `TauCeti.NormalizedCubicalChain.d_mul_eq_zero`: the Pontryagin product of cycles is a cycle.
* `TauCeti.NormalizedCubicalChain.mulCycles`: the Pontryagin product of cycles, as a cycle.

## References

* W. S. Massey, *Singular Homology Theory*, GTM 70, Springer, 1980, Chapter VII.
-/

public noncomputable section

open CategoryTheory

universe u

namespace TauCeti.NormalizedCubicalChain

section LeftAct

variable {G Y : Type u} [TopologicalSpace G] [TopologicalSpace Y] [SMul G Y] [ContinuousSMul G Y]
  {R : Type u} [CommRing R]

/-- **The boundary of the action of a cycle**: for a cycle `z` of degree `q` and a chain `c` of
degree `m + 1`, `∂ (z · c) = (-1) ^ q • z · ∂ c`. -/
theorem d_leftAct_of_d_eq_zero {q m : ℕ} (z : NormalizedCubicalChain G R q)
    (hz : ∀ j, ((normalizedCubicalChainComplex R).obj (TopCat.of G)).d q j
      ((normalizedCubicalChainComplexXEquiv (TopCat.of G) q).symm z) = 0)
    (c : NormalizedCubicalChain Y R (m + 1)) :
    ((normalizedCubicalChainComplex R).obj (TopCat.of Y)).d (q + (m + 1)) (q + m)
        ((normalizedCubicalChainComplexXEquiv (TopCat.of Y) (q + (m + 1))).symm
          (leftAct G Y R q (m + 1) z c)) =
      (normalizedCubicalChainComplexXEquiv (TopCat.of Y) (q + m)).symm
        ((-1 : R) ^ q • leftAct G Y R q m z (boundary Y R m c)) := by
  rcases q with _ | p
  · refine (normalizedCubicalChainComplex_obj_d_apply (TopCat.of Y) (0 + m) _).trans ?_
    have h := boundary_leftAct_zero_left (G := G) (Y := Y) (R := R) z c
    -- `0 + (m + 1)` is `(0 + m) + 1` by definition, so the reindexing of `h` is the one of
    -- `boundary_cast`
    erw [boundary_cast R (Nat.zero_add m)] at h
    rw [pow_zero, one_smul]
    exact cast_injective R (Nat.zero_add m) h
  · have hz' : boundary G R p z = 0 :=
      (normalizedCubicalChainComplex_obj_d_apply (TopCat.of G) p z).symm.trans (hz p)
    refine (normalizedCubicalChainComplex_obj_d_apply (TopCat.of Y) (p + 1 + m) _).trans ?_
    have h := boundary_leftAct (G := G) (Y := Y) (R := R) z c
    rw [hz', map_zero, LinearMap.zero_apply, zero_add] at h
    -- `(p + 1) + (m + 1)` is `(p + 1 + m) + 1` by definition, so the reindexing of `h` is the one
    -- of `boundary_cast`
    erw [boundary_cast R (by omega : p + 1 + m = p + m + 1)] at h
    apply cast_injective R (by omega : p + 1 + m = p + m + 1)
    -- the identifications `normalizedCubicalChainComplexXEquiv` are the identity
    exact h.trans (map_smul _ _ _).symm

end LeftAct

section Mul

variable {G : Type u} [TopologicalSpace G] [Monoid G] [ContinuousMul G] {R : Type u} [CommRing R]

/-- **The Pontryagin product of cycles is a cycle.** -/
theorem d_mul_eq_zero {p q : ℕ} (a : NormalizedCubicalChain G R p)
    (ha : ∀ j, ((normalizedCubicalChainComplex R).obj (TopCat.of G)).d p j
      ((normalizedCubicalChainComplexXEquiv (TopCat.of G) p).symm a) = 0)
    (b : NormalizedCubicalChain G R q)
    (hb : ∀ j, ((normalizedCubicalChainComplex R).obj (TopCat.of G)).d q j
      ((normalizedCubicalChainComplexXEquiv (TopCat.of G) q).symm b) = 0) (j : ℕ) :
    ((normalizedCubicalChainComplex R).obj (TopCat.of G)).d (p + q) j
      ((normalizedCubicalChainComplexXEquiv (TopCat.of G) (p + q)).symm (mul G R p q a b)) = 0 := by
  rcases q with _ | q
  · rcases p with _ | p
    · rw [HomologicalComplex.shape _ _ _ (by simp)]
      simp
    · by_cases hj : j = p
      · subst hj
        have ha' : boundary G R j a = 0 :=
          (normalizedCubicalChainComplex_obj_d_apply (TopCat.of G) j a).symm.trans (ha j)
        refine (normalizedCubicalChainComplex_obj_d_apply (TopCat.of G) j _).trans ?_
        rw [normalizedCubicalChainComplexXEquiv_symm_apply, boundary_mul_zero_right, ha',
          map_zero, LinearMap.zero_apply]
        -- both sides are the zero chain, of degree `j + 0` and `j` respectively
        rfl
      · rw [HomologicalComplex.shape _ _ _ (by simp; omega)]
        simp
  · by_cases hj : j = p + q
    · subst hj
      have hb' : boundary G R q b = 0 :=
        (normalizedCubicalChainComplex_obj_d_apply (TopCat.of G) q b).symm.trans (hb q)
      rw [← leftAct_eq_mul, d_leftAct_of_d_eq_zero a ha b, hb', map_zero, smul_zero, map_zero]
    · rw [HomologicalComplex.shape _ _ _ (by simp; omega)]
      simp

variable (R) in
/-- The **Pontryagin product of cycles**, as a cycle. -/
def mulCycles {p q : ℕ} (a : ((normalizedCubicalChainComplex R).obj (TopCat.of G)).cycles p)
    (b : ((normalizedCubicalChainComplex R).obj (TopCat.of G)).cycles q) :
    ((normalizedCubicalChainComplex R).obj (TopCat.of G)).cycles (p + q) :=
  HomologicalComplex.moduleCatCyclesMk _
    ((normalizedCubicalChainComplexXEquiv (TopCat.of G) (p + q)).symm
      (mul G R p q (normalizedCubicalChainComplexXEquiv _ p
          ((((normalizedCubicalChainComplex R).obj (TopCat.of G)).iCycles p).hom a))
        (normalizedCubicalChainComplexXEquiv _ q
          ((((normalizedCubicalChainComplex R).obj (TopCat.of G)).iCycles q).hom b)))) _ rfl
    (d_mul_eq_zero _ (fun j ↦ HomologicalComplex.moduleCat_d_iCycles_apply _ _ j a) _
      (fun j ↦ HomologicalComplex.moduleCat_d_iCycles_apply _ _ j b) _)

@[simp]
theorem iCycles_mulCycles {p q : ℕ}
    (a : ((normalizedCubicalChainComplex R).obj (TopCat.of G)).cycles p)
    (b : ((normalizedCubicalChainComplex R).obj (TopCat.of G)).cycles q) :
    (((normalizedCubicalChainComplex R).obj (TopCat.of G)).iCycles (p + q)).hom
        (mulCycles R a b) =
      (normalizedCubicalChainComplexXEquiv (TopCat.of G) (p + q)).symm
        (mul G R p q (normalizedCubicalChainComplexXEquiv _ p
            ((((normalizedCubicalChainComplex R).obj (TopCat.of G)).iCycles p).hom a))
          (normalizedCubicalChainComplexXEquiv _ q
            ((((normalizedCubicalChainComplex R).obj (TopCat.of G)).iCycles q).hom b))) :=
  HomologicalComplex.iCycles_moduleCatCyclesMk ..

end Mul

end TauCeti.NormalizedCubicalChain
