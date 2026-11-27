/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TypeAHeckeAlgebra.Seminormal
public import TauCeti.Combinatorics.Young.StandardTableau.CornerFun

/-!
# Branching of the seminormal representations

Let `K` be a field, `q : Kˣ` and `Q = q ^ 2`, and let `μ` be a Young diagram with `n + 1` cells
whose seminormal representation `TauCeti.TypeAHeckeAlgebra.seminormalRep` is defined, that is,
with the additive contents `[d]_Q`, `0 < d ≤ n`, nonzero. This file proves the **branching rule**:
restricting the seminormal representation of `μ` along the tower map
`TauCeti.TypeAHeckeAlgebra.strandIncl : H_n(q) → H_(n+1)(q)`, which adds an uncrossed last strand,
gives the direct sum of the seminormal representations of the diagrams `erase μ c` obtained by
removing one corner `c` of `μ`, one summand for each corner. The splitting is explicit on the
tableau bases:

* for a corner `c`, extending a function on the standard tableaux of shape `erase μ c` by zero
  to the standard tableaux of shape `μ` along `TauCeti.StandardYoungTableau.extend`, which gives
  the corner `c` the largest label `n`, intertwines the two representations
  (`TauCeti.TypeAHeckeAlgebra.seminormalRep_cast_strandIncl_comp_extendByZero`), so the basis
  vectors of the tableaux carrying `n` at `c` span a copy of the seminormal representation of
  `erase μ c`;
* since every standard tableau carries its largest label at exactly one corner
  (`TauCeti.StandardYoungTableau.sigmaCornerEquiv`), these copies give a linear equivalence
  `TauCeti.StandardYoungTableau.cornerFunEquiv` from the product over the corners of the
  representation spaces of the smaller diagrams, which intertwines the restricted action of
  `H_n(q)` (`TauCeti.TypeAHeckeAlgebra.seminormalRep_cast_strandIncl_cornerFunEquiv`).

The diagrams `erase μ c` are distinct for distinct corners `c`
(`YoungDiagram.erase_inj`), so each appears once. The hypothesis on `μ` is the
split-semisimplicity criterion for the diagrams `erase μ c` with `n` cells, so every summand is a
simple module (`TauCeti.TypeAHeckeAlgebra.isSimpleModule_seminormalRep`).

## Main results

* `TauCeti.TypeAHeckeAlgebra.seminormalRep_cast_strandIncl_comp_extendByZero`: extension by zero
  from the tableaux with the largest label at a corner intertwines the restricted action.
* `TauCeti.TypeAHeckeAlgebra.seminormalRep_cast_strandIncl_cornerFunEquiv`: the branching rule.
* `TauCeti.TypeAHeckeAlgebra.additiveContent_ne_zero_of_card_le`: the hypothesis on `μ` carries
  over to every diagram with at most as many cells, such as the diagrams `erase μ c`.

## Implementation notes

The intertwining is checked on the generators: `T_i`, `i < n - 1`, acts through the contents of the
labels `i` and `i + 1` and exchanges them, and restoring a corner keeps these contents and commutes
with the exchange (`TauCeti.StandardYoungTableau.axialDistance_extend`,
`TauCeti.StandardYoungTableau.extend_swap`).

## References

* A. Ram, *Seminormal representations of Weyl groups and Iwahori-Hecke algebras*, Proc. London
  Math. Soc. 75 (1997), 99–133.
* H. Wenzl, *Hecke algebras of type A_n and subfactors*, Invent. Math. 92 (1988), 349–383,
  Section 2.
-/

public section

namespace TauCeti.TypeAHeckeAlgebra

open YoungTableau StandardYoungTableau Function.ExtendByZero

variable {K : Type*} [Field K] {q : Kˣ} {μ : YoungDiagram} {c : ℕ × ℕ}
  {hμ : ∀ d : ℕ, 0 < d → d < μ.card → additiveContent ((q : K) ^ 2) d ≠ 0}

/-- The hypothesis defining the seminormal representation of `μ` carries over to every
diagram `ν` with at most as many cells, such as the diagram `erase μ c` obtained by removing a
corner `c`. -/
theorem additiveContent_ne_zero_of_card_le {Q : K} {ν : YoungDiagram} (hνμ : ν.card ≤ μ.card)
    (hμ : ∀ d : ℕ, 0 < d → d < μ.card → additiveContent Q d ≠ 0) :
    ∀ d : ℕ, 0 < d → d < ν.card → additiveContent Q d ≠ 0 :=
  fun d hd hdν => hμ d hd (hdν.trans_le hνμ)

/-- The branching rule on a generator, at a single corner. -/
private theorem seminormalRep_cast_strandIncl_T_extendByZero (hc : YoungDiagram.IsCorner μ c)
    (i : Fin ((YoungDiagram.erase μ c).card - 1)) (ψ : StandardYoungTableau (μ.erase c) → K) :
    seminormalRep q μ hμ
        (AlgEquiv.cast (R := K) (A := TypeAHeckeAlgebra K q) hc.card_erase
          (strandIncl K q _ (T q i)))
        (linearMap K K (extend hc) ψ) =
      linearMap K K (extend hc) (seminormalRep q (μ.erase c)
        (additiveContent_ne_zero_of_card_le ((Nat.le_succ _).trans hc.card_erase.le) hμ)
        (T q i) ψ) := by
  have hcard := hc.card_erase
  have hi : (i : ℕ) + 1 < (μ.erase c).card := by omega
  rw [strandIncl_T, cast_T]
  funext U
  by_cases hU : U ∈ Set.range (extend hc)
  · obtain ⟨V, rfl⟩ := hU
    rw [linearMap_apply_of_injective K (extend_injective hc), seminormalRep_T_apply,
      seminormalRep_T_apply, linearMap_apply_of_injective K (extend_injective hc)]
    simp only [Fin.val_cast, Fin.val_castLE, axialDistance_extend hc V i hi]
    by_cases h : |axialDistance V.toTableau i hi| = 1
    · rw [dite_eq_left h, dite_eq_left h]
    · rw [dite_eq_right h, dite_eq_right h, ← extend_swap hc V i hi h,
        linearMap_apply_of_injective K (extend_injective hc)]
  · rw [linearMap_apply_of_notMem_range K _ hU, seminormalRep_T_apply,
      linearMap_apply_of_notMem_range K _ hU, mul_zero, zero_add]
    split_ifs with h
    · rw [mul_zero]
    · -- the exchanged tableau still carries its largest label away from `c`
      have hs : U.swap _ _ h ∉ Set.range (extend hc) :=
        mt (swap_mem_range_extend_iff hc U i hi h).mp hU
      rw [linearMap_apply_of_notMem_range K _ hs, mul_zero, mul_zero]

/-- **The branching rule at a corner.** For a corner `c` of `μ`, extending a function on the
standard tableaux of shape `erase μ c` by zero, along the map giving the corner `c` the largest
label, intertwines the seminormal representation of `erase μ c` with the restriction of the
seminormal representation of `μ` along the tower map `strandIncl`. -/
theorem seminormalRep_cast_strandIncl_comp_extendByZero (hc : YoungDiagram.IsCorner μ c)
    (x : TypeAHeckeAlgebra K q (μ.erase c).card) :
    seminormalRep q μ hμ
        (AlgEquiv.cast (R := K) (A := TypeAHeckeAlgebra K q) hc.card_erase (strandIncl K q _ x)) ∘ₗ
        linearMap K K (extend hc) =
      linearMap K K (extend hc) ∘ₗ seminormalRep q (μ.erase c)
        (additiveContent_ne_zero_of_card_le ((Nat.le_succ _).trans hc.card_erase.le) hμ) x := by
  have hx : x ∈ Algebra.adjoin K (Set.range (T (n := (μ.erase c).card) q)) := by
    rw [adjoin_range_T]
    trivial
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    exact LinearMap.ext (seminormalRep_cast_strandIncl_T_extendByZero hc i)
  | algebraMap r =>
    refine LinearMap.ext fun ψ => ?_
    simp only [AlgHom.commutes, AlgEquiv.commutes, LinearMap.comp_apply,
      Module.algebraMap_end_apply, map_smul]
  | add x y _ _ hx hy => simp only [map_add, LinearMap.add_comp, LinearMap.comp_add, hx, hy]
  | mul x y _ _ hx hy =>
    simp only [map_mul, Module.End.mul_eq_comp]
    rw [LinearMap.comp_assoc, hy, ← LinearMap.comp_assoc, hx, LinearMap.comp_assoc]

/-- **The branching rule for the seminormal representations.** Let `μ` have `n + 1` cells. The
restriction of the seminormal representation of `μ` along the tower map
`strandIncl : H_n(q) → H_(n+1)(q)` is the direct sum, over the corners `c` of `μ`, of the
seminormal representations of the diagrams `erase μ c`: the branching decomposition
`TauCeti.StandardYoungTableau.cornerFunEquiv` intertwines the two actions of `H_n(q)`. -/
theorem seminormalRep_cast_strandIncl_cornerFunEquiv {n : ℕ} (h : n + 1 = μ.card)
    (x : TypeAHeckeAlgebra K q n)
    (φ : Π c : {c : ℕ × ℕ // c ∈ μ.corners}, StandardYoungTableau (μ.erase c.val) → K) :
    seminormalRep q μ hμ
        (AlgEquiv.cast (R := K) (A := TypeAHeckeAlgebra K q) h (strandIncl K q n x))
        (cornerFunEquiv (R := K) (by omega) φ) =
      cornerFunEquiv (R := K) (by omega) fun c =>
        seminormalRep q (μ.erase c.val)
          (additiveContent_ne_zero_of_card_le
            ((Nat.le_succ _).trans (YoungDiagram.mem_corners.mp c.property).card_erase.le) hμ)
          (AlgEquiv.cast (R := K) (A := TypeAHeckeAlgebra K q)
            (by have := (YoungDiagram.mem_corners.mp c.property).card_erase; omega) x)
          (φ c) := by
  rw [cornerFunEquiv_eq_sum, cornerFunEquiv_eq_sum, map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  have hc := YoungDiagram.mem_corners.mp c.property
  have hn : n = (μ.erase c.val).card := by have := hc.card_erase; omega
  have key := LinearMap.congr_fun
    (seminormalRep_cast_strandIncl_comp_extendByZero (hμ := hμ) hc
      (AlgEquiv.cast (R := K) (A := TypeAHeckeAlgebra K q) hn x)) (φ c)
  rw [LinearMap.comp_apply, LinearMap.comp_apply] at key
  rw [← key]
  congr 2
  -- once the two strand counts are identified, both casts are the identity
  subst hn
  rfl

end TauCeti.TypeAHeckeAlgebra
