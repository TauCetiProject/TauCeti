/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Field
public import TauCeti.LinearAlgebra.RootSystem.Weyl.Demazure.Basic
public import TauCeti.LinearAlgebra.RootSystem.Weyl.Subword
import TauCeti.Algebra.MonoidAlgebra.MapDomain

/-!
# The fixed-point formula for products of Demazure operators

Let `P` be a root datum with weight lattice `M`, let `Dᵢ` be the integral Demazure operator of the
root `αᵢ` on `ℤ[M]` (`RootPairing.demazureOperator`), and let `ω = i₁ ⋯ iᵣ` be any word in the
indices of the roots, reduced or not. This file proves the **fixed-point formula**

`D_{i₁} ⋯ D_{iᵣ}(e^λ) = ∑_{ε ∈ {0,1}^r} e^{w_r λ} / ∏_{j=1}^r (1 - e^{-β_j})`,

where for each `ε` we write `w_j = s_{i₁}^{ε₁} ⋯ s_{iⱼ}^{εⱼ}` and
`β_j = (-1)^{ε_j} w_{j-1} αᵢⱼ = w_j αᵢⱼ`. Geometrically, the `2^r` choices `ε` index the fixed
points of the maximal torus on the Bott–Samelson variety of the word, `β_1, …, β_r` are the
weights of the torus on the tangent space there, and `e^{w_r λ}` is its weight on the fibre of the
pulled-back line bundle `L_λ`. The right-hand side is then the Atiyah–Bott localization of the
torus-equivariant Euler characteristic of that line bundle, and the formula says that this a priori
rational expression is the element `D_{i₁} ⋯ D_{iᵣ}(e^λ)` of the group algebra.

Both sides are read after a ring homomorphism `φ : ℤ[M] →+* F` into a field under which every
denominator `1 - e^{-β_j}` survives; for instance `φ` may be the inclusion of `ℤ[M]` into its field
of fractions when `ℤ[M]` is a domain (as it is for a lattice `M`), or the evaluation of the
exponentials at a regular point of a torus. The formula
holds for every element `f` of `ℤ[M]` in place of `e^λ`, with `w_r f` in place of `e^{w_r λ}`.

## The argument

For one root it is the localization identity `(1 - e^{-α}) Dᵢ(g) = g - e^{-α} sᵢ(g)` of
`TauCeti.LinearAlgebra.RootSystem.Weyl.Demazure.Basic`, rewritten with
`-e^{-α} / (1 - e^{-α}) = 1 / (1 - e^{α})` as the two-point sum
`Dᵢ(g) = g / (1 - e^{-α}) + sᵢ(g) / (1 - e^{α})`
(`RootPairing.map_demazureOperator_eq_add_div`). For a longer word `i :: ω` apply this to
`g = D_ω(f)`, and expand both `φ(g)` and `φ(sᵢ g)` by induction, the latter for the homomorphism
`φ ∘ sᵢ`. The terms with `ε₁ = 0` come from `φ(g)` and those with `ε₁ = 1` from `φ(sᵢ g)`: moving
`sᵢ` inside multiplies every later `w_j` on the left by `sᵢ`, and so applies `sᵢ` to every later
weight `β_j`.

The subword data `w_j` (`RootPairing.subwordPrefixProd`, `RootPairing.subwordProd`) and `β_j`
(`RootPairing.subwordRoot`) are defined in `TauCeti.LinearAlgebra.RootSystem.Weyl.Subword`, and the
reindexing step uses `RootPairing.mapDomainRingEquiv_reflection_mapDomain_smul` of
`TauCeti.LinearAlgebra.RootSystem.Weyl.Invariant`.

## Main results

* `RootPairing.map_demazureOperator_eq_add_div`: the fixed-point formula for a single Demazure
  operator.
* `RootPairing.map_prod_map_demazureOperator_apply_eq_sum_div`: **the fixed-point formula** for the
  product of the Demazure operators along any word, applied to any element of `ℤ[M]`, and
  `RootPairing.map_prod_map_demazureOperator_single_eq_sum_div`: its form on a weight `e^λ`.

## References

* M. Demazure, *Désingularisation des variétés de Schubert généralisées*, Ann. Sci. École
  Norm. Sup. (4) 7 (1974), §2.
* M. F. Atiyah, R. Bott, *A Lefschetz fixed point formula for elliptic complexes. II.
  Applications*, Ann. of Math. 88 (1968), 451–491.
* S. Kumar, *Kac–Moody Groups, their Flag Varieties and Representation Theory*, Progress in
  Mathematics 204, Birkhäuser (2002), §8.1.
-/

public section

noncomputable section

namespace RootPairing

open AddMonoidAlgebra (single mapDomain mapDomainRingEquiv mapDomain_single single_mul_single
  one_def)

/-! ### The fixed-point formula -/

variable {ι M N : Type*} [AddCommGroup M] [AddCommGroup N] {P : RootPairing ι ℤ M N}
  {F : Type*} [Field F]

variable (P) in
/-- **The fixed-point formula for one Demazure operator**: for a ring homomorphism
`φ : ℤ[M] →+* F` into a field under which `1 - e^{-αᵢ}` does not vanish (and hence neither does
`1 - e^{αᵢ}`, as `e^{αᵢ}` is the inverse of `e^{-αᵢ}`),

`φ(Dᵢ g) = φ(g) / (1 - φ(e^{-αᵢ})) + φ(sᵢ g) / (1 - φ(e^{αᵢ}))`.

On `g = e^x` the right-hand side is the Atiyah–Bott two-fixed-point sum for the
degree-`⟨x, αᵢ^∨⟩` line bundle on the projective line; this result is the algebraic identity
only. -/
theorem map_demazureOperator_eq_add_div (φ : AddMonoidAlgebra ℤ M →+* F) (i : ι)
    (h : 1 - φ (single (-P.root i) 1) ≠ 0) (g : AddMonoidAlgebra ℤ M) :
    φ (P.demazureOperator i g) =
      φ g / (1 - φ (single (-P.root i) 1)) +
        φ (mapDomainRingEquiv ℤ (P.reflection i).toAddEquiv g) / (1 - φ (single (P.root i) 1)) := by
  have hloc := congr(φ $(P.one_sub_single_neg_root_mul_demazureOperator i g))
  have hunit : φ (single (-P.root i) 1) * φ (single (P.root i) 1) = 1 := by
    rw [← map_mul, single_mul_single, neg_add_cancel, mul_one, ← one_def, map_one]
  have h' : 1 - φ (single (P.root i) 1) ≠ 0 := by
    intro h0
    apply h
    linear_combination -hunit - φ (single (-P.root i) 1) * h0
  simp only [map_mul, map_sub, map_one] at hloc
  rw [div_add_div _ _ h h', eq_div_iff (mul_ne_zero h h')]
  linear_combination (1 - φ (single (P.root i) 1)) * hloc +
    φ (mapDomainRingEquiv ℤ (P.reflection i).toAddEquiv g) * hunit

/-- **The fixed-point formula for a product of Demazure operators.** Let `ω = i₁ ⋯ iᵣ` be any
word, and let `φ : ℤ[M] →+* F` be a ring homomorphism into a field under which no denominator
`1 - e^{-β_j}` vanishes, `β_j` being the roots `RootPairing.subwordRoot ω ε j` of the subwords
`ε ∈ {0,1}^r`. Then for every `f ∈ ℤ[M]`,

`φ(D_{i₁} ⋯ D_{iᵣ} f) = ∑_{ε ∈ {0,1}^r} φ(w_r f) / ∏_{j} (1 - φ(e^{-β_j}))`,

where `w_r = s_{i₁}^{ε₁} ⋯ s_{iᵣ}^{εᵣ}` is `RootPairing.subwordProd ω ε`. -/
theorem map_prod_map_demazureOperator_apply_eq_sum_div (φ : AddMonoidAlgebra ℤ M →+* F) (ω : List ι)
    (hφ : ∀ ε k, 1 - φ (single (-P.subwordRoot ω ε k) 1) ≠ 0) (f : AddMonoidAlgebra ℤ M) :
    φ ((ω.map P.demazureOperator).prod f) =
      ∑ ε : Fin ω.length → Bool, φ (mapDomain (P.subwordProd ω ε • ·) f) /
        ∏ k, (1 - φ (single (-P.subwordRoot ω ε k) 1)) := by
  induction ω generalizing φ with
  | nil =>
    have hid : mapDomain (fun x : M ↦ x) f = f := AddMonoidAlgebra.mapDomain_id f
    simp [hid]
  | cons i ω ih =>
    -- `sᵢ` as a ring endomorphism of `ℤ[M]`.
    set s := ((mapDomainRingEquiv ℤ (P.reflection i).toAddEquiv :
      AddMonoidAlgebra ℤ M →+* AddMonoidAlgebra ℤ M))
    -- The hypotheses on `ω` for `φ` and for `φ ∘ sᵢ` are those on `i :: ω` with `ε₁ = 0, 1`.
    have h₀ (ε : Fin ω.length → Bool) (k : Fin ω.length) :
        1 - φ (single (-P.subwordRoot ω ε k) 1) ≠ 0 := by
      simpa using hφ (Fin.cons false ε) k.succ
    have h₁ (ε : Fin ω.length → Bool) (k : Fin ω.length) :
        1 - (φ.comp s) (single (-P.subwordRoot ω ε k) 1) ≠ 0 := by
      simpa [s] using hφ (Fin.cons true ε) k.succ
    have hα : 1 - φ (single (-P.root i) 1) ≠ 0 := by
      simpa using hφ (Fin.cons false fun _ ↦ false) 0
    rw [List.map_cons, List.prod_cons, mul_apply_eq_comp,
      map_demazureOperator_eq_add_div P φ i hα,
      ← RingEquiv.coe_toRingHom, ← RingHom.comp_apply, ih φ h₀, ih (φ.comp s) h₁]
    -- Split `ε ∈ {0,1}^{r+1}` as `(ε₁, ε')`.
    refine Eq.trans ?_ (Fintype.sum_equiv (Fin.consEquiv (n := ω.length) fun _ ↦ Bool) _ _
      fun _ ↦ rfl)
    rw [Fintype.sum_prod_type, Fintype.sum_bool, add_comm, Finset.sum_div, Finset.sum_div]
    congr 1 <;> refine Finset.sum_congr rfl fun ε _ ↦ ?_ <;>
      simp only [Fin.consEquiv_apply, subwordProd_cons, List.length_cons, Fin.prod_univ_succ,
        subwordRoot_cons_zero, subwordRoot_cons_succ, Bool.false_eq_true, ↓reduceIte, one_mul,
        one_smul, neg_neg, div_div, RingHom.comp_apply, s, RingEquiv.coe_toRingHom,
        mapDomainRingEquiv_reflection_mapDomain_smul, AddMonoidAlgebra.mapDomainRingEquiv_single,
        map_neg]
    · simp only [LinearEquiv.coe_toAddEquiv, LinearEquiv.coe_addEquiv_apply, weylGroup.ofIdx_smul,
        Equiv.reflection_smul]
      rw [mul_comm]
    · rw [mul_comm]

/-- **The fixed-point formula on a weight**: for any word `ω = i₁ ⋯ iᵣ` and any weight `λ`,

`φ(D_{i₁} ⋯ D_{iᵣ}(e^λ)) = ∑_{ε ∈ {0,1}^r} φ(e^{w_r λ}) / ∏_{j} (1 - φ(e^{-β_j}))`,

whenever no denominator vanishes under `φ`. The right-hand side is the Atiyah–Bott localization
sum, the expected fixed-point contributions of the pullback of `L_λ` to the Bott–Samelson variety
of `ω`; identifying it with the torus-equivariant Euler characteristic is not part of this
result. -/
theorem map_prod_map_demazureOperator_single_eq_sum_div (φ : AddMonoidAlgebra ℤ M →+* F)
    (ω : List ι) (hφ : ∀ ε k, 1 - φ (single (-P.subwordRoot ω ε k) 1) ≠ 0) (lam : M) :
    φ ((ω.map P.demazureOperator).prod (single lam 1)) =
      ∑ ε : Fin ω.length → Bool, φ (single (P.subwordProd ω ε • lam) 1) /
        ∏ k, (1 - φ (single (-P.subwordRoot ω ε k) 1)) := by
  simp [map_prod_map_demazureOperator_apply_eq_sum_div φ ω hφ, mapDomain_single]

end RootPairing
