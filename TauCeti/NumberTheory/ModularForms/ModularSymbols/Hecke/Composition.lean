/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.BigOperators.Finset.Fiber
public import TauCeti.NumberTheory.HeckeRing.GL2.PairCoset
public import TauCeti.NumberTheory.ModularForms.ModularSymbols.Hecke.Basic

/-!
# Composing the Hecke operators on modular symbols

`ModularSymbols/Hecke/Basic.lean` attaches to a double coset `Γ₁' δ Γ₂' = ⊔ᵥ Γ₁' aᵥ` (with
`Γᵢ' = Γᵢ.map (mapGL ℚ)` the images of subgroups of `SL(2, ℤ)`) the Hecke operator
`T_D : 𝕄_w(Γ₂; R) → 𝕄_w(Γ₁; R)`, `[x] ↦ ∑ᵥ [aᵥ · x]`, on the modules of modular symbols. This file
computes the composite of two such operators: it is the sum over the products of the two families
of representatives,

`T_{D₁} (T_{D₂} [x]) = ∑_{i, j} [(aᵢ bⱼ) · x]`,

the multiplicative half of Shimura's §3.4 transposed from functions on `ℍ` to the coinvariants.
It is the symbol-side counterpart of `HeckeSlash/Composition.lean`, and the two files share the
set-level bookkeeping of the products `aᵢ bⱼ`, none of which mentions either action: which right
cosets they cover (`DoubleCoset.doubleCoset_mul_doubleCoset_eq_iUnion_rightCosets`), how often
each is met (`HeckeRing.GL2.pairCoset` and
`HeckeRing.GL2.card_pairs_pairCoset_rightCoset_eq_multiplicity`, `HeckeRing/GL2/PairCoset.lean`),
and how a family naming each right coset `m` times is counted
(`DoubleCoset.card_filter_eq_of_rightCosetRep_smul_eq`).

Three forms of the composition law are recorded, in increasing generality of the conclusion.
*Over arbitrary representatives* (`heckeSymbol_heckeSymbol_mk_eq_sum_of_rightCosets`), the
composite is the double sum above for any two families naming the right cosets once each; here
the action is a left action, so the products appear as `aᵢ bⱼ` with the representative of the
operator applied *second* on the left, and — unlike the slash sums — no invariance hypothesis is
needed, because the coinvariants have absorbed it. *As a single operator*
(`heckeSymbol_comp_heckeSymbol_eq_heckeSymbol`): when the product set `Γ₁' δ₁ Γ₂' · Γ₂' δ₂ Γ₃'`
is one double coset and the products meet each of its right cosets exactly once, the composite
is the operator of that coset. *Multiplicity-weighted*
(`heckeSymbol_comp_heckeSymbol_eq_sum_nsmul`): in general the composite is
`∑_D m(D₁, D₂; D) • T_D` over the double cosets the products land in, the coefficient being
Shimura's multiplicity in the right-coset-indexed form
`DoubleCoset.multiplicity Γ₃' Γ₂' Γ₁' δ₂⁻¹ δ₁⁻¹ δ₃⁻¹` — the same coefficient, with the same
caveat about its relation to the Hecke ring's structure constants, as on the form side.

At level `Γ₁(N)` the single-coset criterion is applied to the upper-triangular representatives
`!![1, j; 0, n]`: at indices `n`, `m` supported on the level (every prime factor dividing `N`)
they multiply into the representatives at `n m`, so `T_{n m} = T_n T_m` on `𝕄_w(Γ₁(N); R)`
(`heckeTSymbol_mul_of_primeFactors_subset`), such operators commute, and `T_{n^r} = T_n ^ r`.
This is the first piece of the commutativity of the Hecke action on symbols, which the passage
from the period pairing to the integrality of Hecke eigenvalues needs: the transpose of a
composite reverses its order, so the operators being transported must commute among themselves.

## Main results

* `TauCeti.ModularSymbols.sum_mk_symbolIntRep_eq_nsmul_heckeSymbol_mk`: a family of matrices
  in the double coset meeting each of its right cosets `m` times sums to `m • T_D [x]`.
* `TauCeti.ModularSymbols.heckeSymbol_heckeSymbol_mk` and
  `TauCeti.ModularSymbols.heckeSymbol_heckeSymbol_mk_eq_sum_of_rightCosets`: the composite of two
  Hecke operators on the class of `x`, over the chosen and over arbitrary representatives.
* `TauCeti.ModularSymbols.heckeSymbol_comp_heckeSymbol_eq_heckeSymbol`: the composite is the
  operator of a third double coset, when the product set is that coset and the products of the
  representatives have no right-coset collisions.
* `TauCeti.ModularSymbols.heckeSymbol_comp_heckeSymbol_eq_sum_nsmul`: the multiplicity-weighted
  composition law `T_{D₁} ∘ T_{D₂} = ∑_D m(D₁, D₂; D) • T_D`.
* `TauCeti.ModularSymbols.heckeTSymbol_mul_of_primeFactors_subset`: `T_{n m} = T_n T_m` on
  `𝕄_w(Γ₁(N); R)` at indices supported on the level, with
  `TauCeti.ModularSymbols.commute_heckeTSymbol_of_primeFactors_subset` and
  `TauCeti.ModularSymbols.heckeTSymbol_pow_of_primeFactors_subset`.

## References

* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971],
  §3.4: the computation preceding Proposition 3.37, and Proposition 3.36 for the
  upper-triangular representatives.
* W. Stein, *Modular Forms: A Computational Approach*, Graduate Studies in Mathematics **79**,
  American Mathematical Society, 2007, §8.3.
-/

public section

open DoubleCoset HeckeRing.GL2 HeckeRing.GLn Matrix MulOpposite MvPolynomial Representation
  TensorProduct
open Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups Pointwise

namespace TauCeti.ModularSymbols

variable {R : Type*} [CommRing R] {w : ℕ}

attribute [local instance] Fintype.ofFinite

/-! ### Families meeting each right coset equally often -/

section Independence

variable (Γ₁ Γ₂ : Subgroup SL(2, ℤ)) {Δ : Submonoid (GL (Fin 2) ℚ)}
  (D : HeckeCoset Δ (Γ₁.map (mapGL ℚ)) (Γ₂.map (mapGL ℚ)))
  (hD : (D.out : GL (Fin 2) ℚ) ∈ intEntries 2)
  [Finite (DecompQuotient (Γ₂.map (mapGL ℚ)) (Γ₁.map (mapGL ℚ)) (D.out : GL (Fin 2) ℚ)⁻¹)]

/-- **A family meeting each right coset of the double coset `m` times sums to `m` times the Hecke
operator.** If the matrices `aᵢ` lie in `Γ₁' D.out Γ₂'` — so that they are integral,
`HeckeRing.GLn.mem_intEntries_of_mem_doubleCoset` — and, for every `x` there, exactly `m` of them
generate the right coset `Γ₁' x`, then `∑ᵢ [aᵢ · x] = m • T_D [x]`.

Covering is not a hypothesis: a right coset named by no member forces `m = 0`, and then both sides
vanish. This is the shape in which the products `aᵢ bⱼ` of two families of representatives arrive
once they are grouped by the double coset they lie in. -/
theorem sum_mk_symbolIntRep_eq_nsmul_heckeSymbol_mk {ι : Type*} [Fintype ι]
    (a : ι → GL (Fin 2) ℚ) (m : ℕ)
    (hmem : ∀ i, a i ∈ doubleCoset (D.out : GL (Fin 2) ℚ) (Γ₁.map (mapGL ℚ)) (Γ₂.map (mapGL ℚ)))
    (hcard : ∀ x ∈ doubleCoset (D.out : GL (Fin 2) ℚ) (Γ₁.map (mapGL ℚ)) (Γ₂.map (mapGL ℚ)),
      Nat.card {i // op (a i) • (Γ₁.map (mapGL ℚ) : Set (GL (Fin 2) ℚ)) =
        op x • (Γ₁.map (mapGL ℚ) : Set (GL (Fin 2) ℚ))} = m)
    (x : degreeZero R ⊗[R] homogeneousSubmodule (Fin 2) R w) :
    ∑ i, (Coinvariants.mk _ : degreeZero R ⊗[R] homogeneousSubmodule (Fin 2) R w →ₗ[R]
        ModularSymbols R Γ₁ w)
        (symbolIntRep R w ⟨a i, mem_intEntries_of_mem_doubleCoset 2 hD (hmem i)⟩ x) =
      m • heckeSymbol Γ₁ Γ₂ D hD (Coinvariants.mk _ x) := by
  classical
  choose g hg using fun i ↦ exists_rightCosetRep_smul_eq D (hmem i)
  rw [heckeSymbol_mk, Finset.smul_sum,
    ← Finset.sum_fiberwise_of_maps_to (fun i _ ↦ Finset.mem_univ (g i))
      fun i ↦ (Coinvariants.mk _ : degreeZero R ⊗[R] homogeneousSubmodule (Fin 2) R w →ₗ[R]
        ModularSymbols R Γ₁ w)
        (symbolIntRep R w ⟨a i, mem_intEntries_of_mem_doubleCoset 2 hD (hmem i)⟩ x)]
  refine Finset.sum_congr rfl fun v _ ↦ ?_
  -- On the fibre of `v` every term is the class of the translate by `v`'s representative, so the
  -- fibre contributes its cardinality times that one value.
  rw [← card_filter_eq_of_rightCosetRep_smul_eq D hcard hg v, ← Finset.sum_const]
  exact Finset.sum_congr rfl fun i hi ↦ mk_symbolIntRep_eq_of_rightCoset_eq Γ₁
    (mem_intEntries_of_mem_doubleCoset 2 hD (hmem i)) ((Finset.mem_filter.mp hi).2 ▸ hg i) x

end Independence

/-! ### The composite of two Hecke operators -/

section Composite

variable (Γ₁ Γ₂ Γ₃ : Subgroup SL(2, ℤ)) {Δ : Submonoid (GL (Fin 2) ℚ)}
  (D₁ : HeckeCoset Δ (Γ₁.map (mapGL ℚ)) (Γ₂.map (mapGL ℚ)))
  (D₂ : HeckeCoset Δ (Γ₂.map (mapGL ℚ)) (Γ₃.map (mapGL ℚ)))
  (hD₁ : (D₁.out : GL (Fin 2) ℚ) ∈ intEntries 2) (hD₂ : (D₂.out : GL (Fin 2) ℚ) ∈ intEntries 2)
  [Finite (DecompQuotient (Γ₂.map (mapGL ℚ)) (Γ₁.map (mapGL ℚ)) (D₁.out : GL (Fin 2) ℚ)⁻¹)]
  [Finite (DecompQuotient (Γ₃.map (mapGL ℚ)) (Γ₂.map (mapGL ℚ)) (D₂.out : GL (Fin 2) ℚ)⁻¹)]

/-- **The composite of two Hecke operators on the class of `x`, over the representatives they are
defined with**: `T_{D₁} (T_{D₂} [x]) = ∑_{v, u} [(aᵥ b_u) · x]`, the sum over the products of the
chosen right-coset representatives of `D₁` and of `D₂`. -/
theorem heckeSymbol_heckeSymbol_mk (x : degreeZero R ⊗[R] homogeneousSubmodule (Fin 2) R w) :
    heckeSymbol Γ₁ Γ₂ D₁ hD₁ (heckeSymbol Γ₂ Γ₃ D₂ hD₂ (Coinvariants.mk _ x)) =
      ∑ v, ∑ u, (Coinvariants.mk _ : degreeZero R ⊗[R] homogeneousSubmodule (Fin 2) R w →ₗ[R]
        ModularSymbols R Γ₁ w)
        (symbolIntRep R w ⟨rightCosetRep D₁ v * rightCosetRep D₂ u,
          mul_mem (rightCosetRep_mem D₁ hD₁ (map_mapGL_le_intEntries 2 Γ₂) v)
            (rightCosetRep_mem D₂ hD₂ (map_mapGL_le_intEntries 2 Γ₃) u)⟩ x) := by
  rw [heckeSymbol_mk, map_sum, Finset.sum_comm]
  refine Finset.sum_congr rfl fun u _ ↦ ?_
  rw [heckeSymbol_mk]
  refine Finset.sum_congr rfl fun v _ ↦ ?_
  rw [← Submonoid.mk_mul_mk, map_mul, Module.End.mul_apply]

variable {ι κ : Type*} (a : ι → GL (Fin 2) ℚ) (b : κ → GL (Fin 2) ℚ)
  (hcover₁ : doubleCoset (D₁.out : GL (Fin 2) ℚ) (Γ₁.map (mapGL ℚ)) (Γ₂.map (mapGL ℚ)) =
    ⋃ i, op (a i) • (Γ₁.map (mapGL ℚ) : Set (GL (Fin 2) ℚ)))
  (hinj₁ : Function.Injective fun i ↦ op (a i) • (Γ₁.map (mapGL ℚ) : Set (GL (Fin 2) ℚ)))
  (hcover₂ : doubleCoset (D₂.out : GL (Fin 2) ℚ) (Γ₂.map (mapGL ℚ)) (Γ₃.map (mapGL ℚ)) =
    ⋃ j, op (b j) • (Γ₂.map (mapGL ℚ) : Set (GL (Fin 2) ℚ)))
  (hinj₂ : Function.Injective fun j ↦ op (b j) • (Γ₂.map (mapGL ℚ) : Set (GL (Fin 2) ℚ)))

include hinj₁ hinj₂ in
/-- **The composite of two Hecke operators, over arbitrary representatives.** For any families
`(aᵢ)`, `(bⱼ)` naming the right cosets of `Γ₁' δ₁ Γ₂'` and of `Γ₂' δ₂ Γ₃'` once each — such
matrices are integral, `HeckeRing.GLn.mem_intEntries_of_cover` —

`T_{D₁} (T_{D₂} [x]) = ∑_{i, j} [(aᵢ bⱼ) · x]`.

This is Shimura's computation in §3.4 on the way to Proposition 3.37, on the symbol side. No
invariance hypothesis appears, in contrast to the slash sums: the classes in the coinvariants are
already invariant, which is what `heckeSymbol_mk_eq_sum_of_rightCosets` records. -/
theorem heckeSymbol_heckeSymbol_mk_eq_sum_of_rightCosets [Fintype ι] [Fintype κ]
    (x : degreeZero R ⊗[R] homogeneousSubmodule (Fin 2) R w) :
    heckeSymbol Γ₁ Γ₂ D₁ hD₁ (heckeSymbol Γ₂ Γ₃ D₂ hD₂ (Coinvariants.mk _ x)) =
      ∑ i, ∑ j, (Coinvariants.mk _ : degreeZero R ⊗[R] homogeneousSubmodule (Fin 2) R w →ₗ[R]
        ModularSymbols R Γ₁ w)
        (symbolIntRep R w ⟨a i * b j, mul_mem (mem_intEntries_of_cover 2 hD₁ hcover₁ i)
          (mem_intEntries_of_cover 2 hD₂ hcover₂ j)⟩ x) := by
  rw [heckeSymbol_mk_eq_sum_of_rightCosets Γ₂ Γ₃ D₂ hD₂ b (mem_intEntries_of_cover 2 hD₂ hcover₂)
    hcover₂ hinj₂, map_sum, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [heckeSymbol_mk_eq_sum_of_rightCosets Γ₁ Γ₂ D₁ hD₁ a (mem_intEntries_of_cover 2 hD₁ hcover₁)
    hcover₁ hinj₁]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [← Submonoid.mk_mul_mk, map_mul, Module.End.mul_apply]

variable [Finite ι] [Finite κ] (D₃ : HeckeCoset Δ (Γ₁.map (mapGL ℚ)) (Γ₃.map (mapGL ℚ)))
  [Finite (DecompQuotient (Γ₃.map (mapGL ℚ)) (Γ₁.map (mapGL ℚ)) (D₃.out : GL (Fin 2) ℚ)⁻¹)]

include hcover₁ hinj₁ hcover₂ hinj₂ in
/-- **The composite is the Hecke operator of a single double coset**, when the product set
`Γ₁' δ₁ Γ₂' · Γ₂' δ₂ Γ₃'` is that coset and the products `aᵢ bⱼ` meet each of its right cosets
exactly once: `T_{D₁} ∘ T_{D₂} = T_{D₃}`.

The hypotheses are those of `HeckeRing.GL2.heckeSlashSum_heckeSlashSum_eq_heckeSlashSum`: `hmul`
says that the product set is the single coset `D₃`, and `hinj₃` that the products have no
right-coset collisions. The covering half of what `heckeSymbol_mk_eq_sum_of_rightCosets` needs is
automatic, by `DoubleCoset.doubleCoset_mul_doubleCoset_eq_iUnion_rightCosets`, and so is the
integrality of `D₃.out`: it lies in the product of two double cosets of integral matrices
(`HeckeRing.GLn.mem_intEntries_of_mem_doubleCoset_mul_doubleCoset`). -/
theorem heckeSymbol_comp_heckeSymbol_eq_heckeSymbol
    (hmul : doubleCoset (D₃.out : GL (Fin 2) ℚ) (Γ₁.map (mapGL ℚ)) (Γ₃.map (mapGL ℚ)) =
      doubleCoset (D₁.out : GL (Fin 2) ℚ) (Γ₁.map (mapGL ℚ)) (Γ₂.map (mapGL ℚ)) *
        doubleCoset (D₂.out : GL (Fin 2) ℚ) (Γ₂.map (mapGL ℚ)) (Γ₃.map (mapGL ℚ)))
    (hinj₃ : Function.Injective
      fun p : ι × κ ↦ op (a p.1 * b p.2) • (Γ₁.map (mapGL ℚ) : Set (GL (Fin 2) ℚ))) :
    (heckeSymbol Γ₁ Γ₂ D₁ hD₁ ∘ₗ heckeSymbol Γ₂ Γ₃ D₂ hD₂ :
      ModularSymbols R Γ₃ w →ₗ[R] ModularSymbols R Γ₁ w) =
      heckeSymbol Γ₁ Γ₃ D₃ (mem_intEntries_of_mem_doubleCoset_mul_doubleCoset 2 hD₁ hD₂
        (hmul ▸ mem_doubleCoset_self _ _ _)) := by
  refine Coinvariants.hom_ext (LinearMap.ext fun x ↦ ?_)
  simp only [LinearMap.comp_apply]
  rw [heckeSymbol_heckeSymbol_mk_eq_sum_of_rightCosets Γ₁ Γ₂ Γ₃ D₁ D₂ hD₁ hD₂ a b hcover₁ hinj₁
      hcover₂ hinj₂,
    heckeSymbol_mk_eq_sum_of_rightCosets Γ₁ Γ₃ D₃ _ (fun p : ι × κ ↦ a p.1 * b p.2)
      (fun p ↦ mul_mem (mem_intEntries_of_cover 2 hD₁ hcover₁ p.1)
        (mem_intEntries_of_cover 2 hD₂ hcover₂ p.2))
      (hmul.trans (doubleCoset_mul_doubleCoset_eq_iUnion_rightCosets a b hcover₁ hcover₂)) hinj₃,
    Fintype.sum_prod_type]

end Composite

/-! ### The multiplicity-weighted composition law -/

section Assembly

variable (Γ₁ Γ₂ Γ₃ : Subgroup SL(2, ℤ)) {Δ : Submonoid (GL (Fin 2) ℚ)}
  [IsHeckeTriple Δ (Γ₁.map (mapGL ℚ)) (Γ₂.map (mapGL ℚ))]
  [IsHeckeTriple Δ (Γ₂.map (mapGL ℚ)) (Γ₃.map (mapGL ℚ))]
  (D₁ : HeckeCoset Δ (Γ₁.map (mapGL ℚ)) (Γ₂.map (mapGL ℚ)))
  (D₂ : HeckeCoset Δ (Γ₂.map (mapGL ℚ)) (Γ₃.map (mapGL ℚ)))
  (hD₁ : (D₁.out : GL (Fin 2) ℚ) ∈ intEntries 2) (hD₂ : (D₂.out : GL (Fin 2) ℚ) ∈ intEntries 2)

open Classical in
/-- **The multiplicity-weighted composition law.** For double cosets `D₁`, `D₂` of integral
matrices, the composite of the two Hecke operators is the sum, over the double cosets `D` met by
the products `aᵥ b_u` of the representatives, of Shimura's multiplicity times the operator of `D`:

`T_{D₁} ∘ T_{D₂} = ∑_D m(D₁, D₂; D) • T_D`.

The sum runs over the attached finset of output cosets, each `D` carrying its membership, from
which `mem_intEntries_of_mem_image_pairCoset` derives the integrality of `D.out` that `T_D`
needs: only the two input cosets are assumed integral, not the monoid `Δ`.

`heckeSymbol_comp_heckeSymbol_eq_heckeSymbol` is the special case where the products meet a single
double coset and meet each of its right cosets exactly once. The coefficient is
`DoubleCoset.multiplicity Γ₃' Γ₂' Γ₁' δ₂⁻¹ δ₁⁻¹ δ₃⁻¹`, exactly as for the slash sums
(`HeckeRing.GL2.heckeSlashSum_heckeSlashSum_eq_sum_nsmul`), and for the same reason: the sums are
indexed by right cosets.

No finiteness is assumed beyond the two input Hecke triples; the finiteness of each output
coset's own decomposition comes from the composite triple `IsHeckeTriple Δ Γ₁' Γ₃'`, which
`IsHeckeTriple.trans` derives from the two given ones. -/
theorem heckeSymbol_comp_heckeSymbol_eq_sum_nsmul :
    letI : IsHeckeTriple Δ (Γ₁.map (mapGL ℚ)) (Γ₃.map (mapGL ℚ)) :=
      IsHeckeTriple.trans (H₂ := Γ₂.map (mapGL ℚ))
    heckeSymbol Γ₁ Γ₂ D₁ hD₁ ∘ₗ heckeSymbol Γ₂ Γ₃ D₂ hD₂ =
      ∑ D ∈ (Finset.univ.image (pairCoset D₁ D₂)).attach,
        DoubleCoset.multiplicity (Γ₃.map (mapGL ℚ)) (Γ₂.map (mapGL ℚ)) (Γ₁.map (mapGL ℚ))
          (D₂.out : GL (Fin 2) ℚ)⁻¹ (D₁.out : GL (Fin 2) ℚ)⁻¹ (D.1.out : GL (Fin 2) ℚ)⁻¹ •
            (heckeSymbol Γ₁ Γ₃ D.1 (mem_intEntries_of_mem_image_pairCoset Γ₁ Γ₂ Γ₃ D₁ D₂ hD₁ hD₂
              D.2) : ModularSymbols R Γ₃ w →ₗ[R] ModularSymbols R Γ₁ w) := by
  -- the same composite triple the statement derives; `IsHeckeTriple.trans` cannot be an
  -- instance, since `Γ₂` does not occur in the conclusion, so it is named at both points
  let _ : IsHeckeTriple Δ (Γ₁.map (mapGL ℚ)) (Γ₃.map (mapGL ℚ)) :=
    IsHeckeTriple.trans (H₂ := Γ₂.map (mapGL ℚ))
  refine Coinvariants.hom_ext (LinearMap.ext fun x ↦ ?_)
  simp only [LinearMap.comp_apply, LinearMap.sum_apply, LinearMap.smul_apply]
  rw [heckeSymbol_heckeSymbol_mk Γ₁ Γ₂ Γ₃ D₁ D₂ hD₁ hD₂, ← Fintype.sum_prod_type',
    TauCeti.sum_eq_sum_image_fiber (pairCoset D₁ D₂) fun q ↦
      (Coinvariants.mk _ : degreeZero R ⊗[R] homogeneousSubmodule (Fin 2) R w →ₗ[R]
        ModularSymbols R Γ₁ w)
        (symbolIntRep R w ⟨rightCosetRep D₁ q.1 * rightCosetRep D₂ q.2,
          mul_mem (rightCosetRep_mem D₁ hD₁ (map_mapGL_le_intEntries 2 Γ₂) q.1)
            (rightCosetRep_mem D₂ hD₂ (map_mapGL_le_intEntries 2 Γ₃) q.2)⟩ x),
    ← Finset.sum_attach (Finset.univ.image (pairCoset D₁ D₂))]
  refine Finset.sum_congr rfl fun D _ ↦ ?_
  exact sum_mk_symbolIntRep_eq_nsmul_heckeSymbol_mk Γ₁ Γ₃ D.1
    (mem_intEntries_of_mem_image_pairCoset Γ₁ Γ₂ Γ₃ D₁ D₂ hD₁ hD₂ D.2) _ _
    (fun i ↦ pairCoset_eq_iff.mp i.2)
    (fun _ hx ↦ card_pairs_pairCoset_rightCoset_eq_multiplicity hx) x

end Assembly

/-! ### The Hecke operators `T_n` at indices supported on the level -/

section Gamma1

variable (N : ℕ) [NeZero N]

/-- **The Hecke operators on modular symbols at indices supported on the level multiply**:
`T_{n m} = T_n ∘ T_m` on `𝕄_w(Γ₁(N); R)` when every prime factor of `n` and of `m` divides `N`.

At such indices the double coset of `diag(1, n)` is the union of the `n` upper-triangular right
cosets `Γ₁(N) · !![1, j; 0, n]`, and `HeckeRing.GL2.upperTriRep_mul_upperTriRep` matches the pairs
of representatives with the representatives at index `n · m` bijectively. Nothing here is a
coprimality statement: the identity holds whether or not `n` and `m` are coprime. -/
@[simp]
theorem heckeTSymbol_mul_of_primeFactors_subset {n m : ℕ} [NeZero n] [NeZero m]
    (hn : n.primeFactors ⊆ N.primeFactors) (hm : m.primeFactors ⊆ N.primeFactors) :
    heckeTSymbol R w N (n * m) = heckeTSymbol R w N n * heckeTSymbol R w N m := by
  have hn0 : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hm0 : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  have hnm : (n * m).primeFactors ⊆ N.primeFactors := by
    rw [Nat.primeFactors_mul hn0.ne' hm0.ne']
    exact Finset.union_subset hn hm
  have hcover₁ := doubleCoset_out_diagCosetGamma1_eq_iUnion_rightCosets (N := N) hn0 hn
  have hcover₂ := doubleCoset_out_diagCosetGamma1_eq_iUnion_rightCosets (N := N) hm0 hm
  rw [Module.End.mul_eq_comp, heckeTSymbol_def, heckeTSymbol_def, heckeTSymbol_def]
  refine (heckeSymbol_comp_heckeSymbol_eq_heckeSymbol (Gamma1 N) (Gamma1 N) (Gamma1 N)
    (diagCosetGamma1 N n) (diagCosetGamma1 N m) _ _ (upperTriRep n) (upperTriRep m) hcover₁
    op_upperTriRep_smul_injective hcover₂ op_upperTriRep_smul_injective
    (diagCosetGamma1 N (n * m)) ?_ ?_).symm
  · -- the product set is the double coset at index `n · m`: both are the union of the
    -- upper-triangular right cosets, enumerated by `Fin (n * m)` and by `Fin n × Fin m`
    rw [doubleCoset_mul_doubleCoset_eq_iUnion_rightCosets _ _ hcover₁ hcover₂,
      doubleCoset_out_diagCosetGamma1_eq_iUnion_rightCosets (Nat.mul_pos hn0 hm0) hnm]
    simp only [upperTriRep_mul_upperTriRep, Prod.mk.eta]
    exact (finProdFinEquiv.surjective.iUnion_comp _).symm
  · intro p q h
    simp only [upperTriRep_mul_upperTriRep, Prod.mk.eta] at h
    exact finProdFinEquiv.injective (op_upperTriRep_smul_injective h)

/-- **The Hecke operators on modular symbols at indices supported on the level commute.** Both
orders compute the operator at the product index. -/
theorem commute_heckeTSymbol_of_primeFactors_subset {n m : ℕ} [NeZero n] [NeZero m]
    (hn : n.primeFactors ⊆ N.primeFactors) (hm : m.primeFactors ⊆ N.primeFactors) :
    Commute (heckeTSymbol R w N n) (heckeTSymbol R w N m) := by
  rw [commute_iff_eq, ← heckeTSymbol_mul_of_primeFactors_subset N hn hm,
    ← heckeTSymbol_mul_of_primeFactors_subset N hm hn]
  exact heckeTSymbol_congr N (mul_comm n m)

/-- **`T_{n^r} = T_n ^ r` on modular symbols, at an index supported on the level.** -/
@[simp]
theorem heckeTSymbol_pow_of_primeFactors_subset {n : ℕ} [NeZero n]
    (hn : n.primeFactors ⊆ N.primeFactors) (r : ℕ) :
    heckeTSymbol R w N (n ^ r) = heckeTSymbol R w N n ^ r := by
  induction r with
  | zero => rw [heckeTSymbol_congr N (pow_zero n), heckeTSymbol_one, pow_zero]
  | succ r ih =>
    have hr : (n ^ r).primeFactors ⊆ N.primeFactors := by
      rcases Nat.eq_zero_or_pos r with rfl | hr
      · simp
      · rw [Nat.primeFactors_pow n hr.ne']
        exact hn
    rw [heckeTSymbol_congr N (pow_succ n r), heckeTSymbol_mul_of_primeFactors_subset N hr hn, ih,
      pow_succ]

end Gamma1

end TauCeti.ModularSymbols

end
