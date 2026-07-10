/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.FieldTheory.Finiteness
public import TauCeti.NumberTheory.Multiquadratic.SubfieldDegree
public import TauCeti.NumberTheory.Multiquadratic.CoprimeSquarefree

/-!
# The number of quadratic subfields of a multiquadratic field

For square roots `root i` of radicands `d i` over a field `K` with `2 ≠ 0`, square-class
independence makes `M = K(rootᵢ : i)` Galois with group `(ℤ/2)ⁿ`, and
`TauCeti.NumberTheory.Multiquadratic.SubfieldDegree` reads off *which* intermediate fields are
quadratic: `F` has degree `2` over `K` exactly when its attached `𝔽₂`-subspace of `ι → ℤ/2` is a
hyperplane. This file counts them: a multiquadratic field of degree `2ⁿ` has exactly `2ⁿ - 1`
quadratic subfields.

The count is the number of hyperplanes of `𝔽₂ⁿ`. Over `𝔽₂` a hyperplane is the annihilator of a
unique line of the dual space, and over `𝔽₂` a line is spanned by a unique nonzero vector, so the
hyperplanes are counted by the nonzero vectors of an `n`-dimensional `𝔽₂`-space: `2ⁿ - 1` of them.
The two private helpers below package this purely linear-algebraic fact; the public theorem
transports it across the subfield/subspace dictionary
`TauCeti.NumberTheory.Multiquadratic.SubfieldLattice`.

## Main results

* `TauCeti.Multiquadratic.card_quadratic_intermediateField_adjoin_range`: under square-class
  independence, `M = K(rootᵢ : i)` has exactly `2 ^ |ι| - 1` intermediate fields of degree `2`
  over `K`.

## Provenance

The subfield/subspace dictionary this refines is migrated, with the rest of the multiquadratic
Layer 0, from
[kim-em/erdos-unit-distance](https://github.com/kim-em/erdos-unit-distance), the formalization of
L. Alpöge's disproof of the uniform-constant Erdős unit-distance conjecture. The hyperplane count
assembles Mathlib's dual-annihilator order isomorphism (`Subspace.orderIsoFiniteDimensional`) with
the finite-field cardinality `Module.card_eq_pow_finrank`.
-/

public section

open IntermediateField Module
open scoped Function

namespace TauCeti.Multiquadratic

section LinearAlgebra

variable {M : Type*} [AddCommGroup M] [Module (ZMod 2) M] [FiniteDimensional (ZMod 2) M]

/-- **Lines of an `𝔽₂`-space are counted by its nonzero vectors.** Over `𝔽₂` the only nonzero
scalar is `1`, so distinct nonzero vectors span distinct lines and every line is spanned by a
nonzero vector; hence the `1`-dimensional subspaces of a finite `𝔽₂`-space `M` number
`|M| - 1`. -/
private theorem card_finrank_eq_one [Fintype M] :
    Nat.card {W : Submodule (ZMod 2) M // finrank (ZMod 2) W = 1} = Fintype.card M - 1 := by
  classical
  -- `v ↦ 𝔽₂ ∙ v` is a bijection from the nonzero vectors onto the lines.
  have hbij : Function.Bijective
      (fun v : {v : M // v ≠ 0} =>
        (⟨(ZMod 2) ∙ (v : M), finrank_span_singleton v.2⟩ :
          {W : Submodule (ZMod 2) M // finrank (ZMod 2) W = 1})) := by
    constructor
    · rintro ⟨v, hv⟩ ⟨w, hw⟩ hvw
      have hspan : (ZMod 2) ∙ v = (ZMod 2) ∙ w := congrArg Subtype.val hvw
      have hmem : w ∈ (ZMod 2) ∙ v := by rw [hspan]; exact Submodule.mem_span_singleton_self w
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hmem
      have hc0 : c ≠ 0 := by rintro rfl; exact hw (by simpa using hc.symm)
      have key : ∀ c : ZMod 2, c ≠ 0 → c = 1 := by decide
      have hc1 : c = 1 := key c hc0
      have hwv : w = v := by rw [← hc, hc1, one_smul]
      exact Subtype.ext hwv.symm
    · rintro ⟨W, hW⟩
      obtain ⟨v, hvW, hv0⟩ := W.exists_mem_ne_zero_of_ne_bot (by
        rintro rfl; simp [finrank_bot] at hW)
      refine ⟨⟨v, hv0⟩, Subtype.ext ?_⟩
      exact Submodule.eq_of_le_of_finrank_eq
        (Submodule.span_le.2 (Set.singleton_subset_iff.2 hvW))
        (by rw [finrank_span_singleton hv0, hW])
  rw [← Nat.card_congr (Equiv.ofBijective _ hbij), Nat.card_eq_fintype_card,
    Fintype.card_subtype_compl (p := fun v : M => v = 0), Fintype.card_subtype_eq]

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

/-- **The hyperplanes of an `n`-dimensional `𝔽₂`-space number `2ⁿ - 1`.** A subspace `U` is a
hyperplane (`dim U + 1 = dim V`) exactly when its dual annihilator is a line; the dual-annihilator
order isomorphism turns the hyperplanes of `V` into the lines of its dual, which
`card_finrank_eq_one` counts. -/
private theorem card_hyperplane (n : ℕ) (hn : finrank (ZMod 2) V = n) :
    Nat.card {U : Submodule (ZMod 2) V // finrank (ZMod 2) U + 1 = n} = 2 ^ n - 1 := by
  subst hn
  haveI : Finite (Module.Dual (ZMod 2) V) := Module.finite_of_finite (ZMod 2)
  haveI : Fintype (Module.Dual (ZMod 2) V) := Fintype.ofFinite _
  -- The dual annihilator matches hyperplanes of `V` with lines of the dual.
  have hequiv : {U : Submodule (ZMod 2) V // finrank (ZMod 2) U + 1 = finrank (ZMod 2) V}
      ≃ {W : Submodule (ZMod 2) (Module.Dual (ZMod 2) V) // finrank (ZMod 2) W = 1} :=
    Equiv.subtypeEquiv (Subspace.orderIsoFiniteDimensional.toEquiv.trans OrderDual.ofDual)
      (fun U => by
        have h := Subspace.finrank_add_finrank_dualAnnihilator_eq U
        change finrank (ZMod 2) U + 1 = finrank (ZMod 2) V ↔
          finrank (ZMod 2) U.dualAnnihilator = 1
        omega)
  rw [Nat.card_congr hequiv, card_finrank_eq_one, Module.card_eq_pow_finrank (K := ZMod 2),
    Subspace.dual_finrank_eq, ZMod.card]

end LinearAlgebra

variable {K L : Type*} [Field K] [Field L] [Algebra K L] {ι : Type*}
  {d : ι → K} {root : ι → L}

/-- **The number of quadratic subfields of a multiquadratic field is `2ⁿ - 1`.** Under
square-class independence (and `2 ≠ 0`), the multiquadratic field `M = K(rootᵢ : i)`, of degree
`2 ^ |ι|` over `K`, has exactly `2 ^ |ι| - 1` intermediate fields of degree `2` over `K`. These are
the hyperplanes of the `𝔽₂`-subspace lattice, one for each nonempty square-class of radicands. -/
theorem card_quadratic_intermediateField_adjoin_range [Finite ι] [NeZero (2 : K)]
    (hroot : ∀ i, root i ^ 2 = algebraMap K L (d i))
    (hindep : ∀ S : Finset ι, S.Nonempty → ¬ IsSquare (∏ i ∈ S, d i)) :
    Nat.card {F : IntermediateField K (adjoin K (Set.range root)) // Module.finrank K F = 2}
      = 2 ^ Nat.card ι - 1 := by
  classical
  letI := Fintype.ofFinite ι
  -- Transport the quadratic subfields to the hyperplanes of `ι → ℤ/2`.
  have hbij : {F : IntermediateField K (adjoin K (Set.range root)) // Module.finrank K F = 2}
      ≃ {U : Submodule (ZMod 2) (ι → ZMod 2) // finrank (ZMod 2) U + 1 = Nat.card ι} :=
    Equiv.subtypeEquiv
      ((intermediateFieldEquivSubmodule hroot hindep).toEquiv.trans OrderDual.ofDual)
      (fun F => finrank_intermediateField_eq_two_iff hroot hindep F)
  rw [Nat.card_congr hbij]
  exact card_hyperplane (Nat.card ι)
    (by rw [Module.finrank_fintype_fun_eq_card, Nat.card_eq_fintype_card])

/-- **Worked example: `ℚ(√2, √3)` has exactly `3` quadratic subfields.** The smallest nontrivial
multiquadratic field, of degree `4`, has `2² - 1 = 3` subfields of degree `2` over `ℚ`, namely
`ℚ(√2)`, `ℚ(√3)`, and `ℚ(√6)`. The radicands `2` and `3` are coprime, squarefree, and not units,
so `card_quadratic_intermediateField_adjoin_range` applies through
`not_isSquare_prod_of_coprime_squarefree_rat`. -/
theorem card_quadratic_subfield_sqrt_two_three :
    Nat.card {F : IntermediateField ℚ
        (adjoin ℚ {Real.sqrt 2, Real.sqrt 3} : IntermediateField ℚ ℝ) //
          Module.finrank ℚ F = 2} = 3 := by
  have hcop : Pairwise (IsCoprime on (![2, 3] : Fin 2 → ℤ)) := by
    have h : IsCoprime (2 : ℤ) 3 := Int.isCoprime_iff_gcd_eq_one.mpr (by decide)
    have h' : IsCoprime (3 : ℤ) 2 := h.symm
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [Function.onFun]
  have hsf : ∀ i, Squarefree ((![2, 3] : Fin 2 → ℤ) i) := by
    intro i
    fin_cases i
    · exact (Int.prime_iff_natAbs_prime.2 (by decide)).squarefree
    · exact (Int.prime_iff_natAbs_prime.2 (by decide)).squarefree
  have hnu : ∀ i, ¬ IsUnit ((![2, 3] : Fin 2 → ℤ) i) := by
    intro i
    fin_cases i <;> simp [Int.isUnit_iff]
  have hkey := card_quadratic_intermediateField_adjoin_range (K := ℚ) (L := ℝ)
    (d := fun i => ((![2, 3] : Fin 2 → ℤ) i : ℚ))
    (root := fun i => Real.sqrt ((![2, 3] : Fin 2 → ℤ) i))
    (fun i => by fin_cases i <;> exact sq_sqrt_intCast (by norm_num))
    (not_isSquare_prod_of_coprime_squarefree_rat ![2, 3] hcop hsf hnu)
  have hset : (Set.range fun i : Fin 2 => Real.sqrt ((![2, 3] : Fin 2 → ℤ) i))
      = {Real.sqrt 2, Real.sqrt 3} := by
    ext x
    simp [Fin.exists_fin_two, eq_comm]
  rw [hset] at hkey
  have h3 : (2 : ℕ) ^ Nat.card (Fin 2) - 1 = 3 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_fin]; rfl
  exact hkey.trans h3

end TauCeti.Multiquadratic
