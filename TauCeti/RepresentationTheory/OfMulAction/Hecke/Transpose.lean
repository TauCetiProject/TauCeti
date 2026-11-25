/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Opposite
public import TauCeti.RepresentationTheory.OfMulAction.Hecke.Level

/-!
# The transpose anti-involution of a permutation Hecke algebra

For a group `G` acting on a set `S` and a commutative ring `A`, the **transpose**
`hᵀ(x, y) = h(y, x)` preserves the permutation Hecke module `Fun_G(S × S, A)`
(`TauCeti.permutationHeckeModule`): it is invariant under the diagonal action, and it swaps the
diagonal orbits. It is an involution, reverses the matrix product, and fixes the unit, so for
finitely many orbits it is an algebra isomorphism `Fun_G(S × S, A) ≃ₐ[A] Fun_G(S × S, A)ᵐᵒᵖ`
(`TauCeti.PermutationHecke.transposeAlgEquiv`). It sends the indicator of the orbit of `(x, y)`
to the indicator of the orbit of `(y, x)`.

For the Hecke algebra of a level `H(G, U; A)` (`TauCeti.HeckeAlgebraLevel`) the orbits of
`G ⧸ U × G ⧸ U` are the double cosets: the orbit of `(U, gU)` corresponds to `UgU`. The transpose
sends the indicator of the orbit of `(U, gU)` to that of `(U, g⁻¹U)`
(`TauCeti.HeckeAlgebraLevel.transpose_indicator_orbit`), that is `[UgU] ↦ [Ug⁻¹U]`, and identifies
`H(G, U; A)` with its opposite algebra.

## Main definitions

* `TauCeti.PermutationHecke.transpose`: the transpose, an involutive `A`-linear equivalence of
  `Fun_G(S × S, A)`.
* `TauCeti.PermutationHecke.transposeAlgEquiv`: for finitely many orbits, the transpose as an
  algebra isomorphism with the opposite algebra.

## Main results

* `TauCeti.PermutationHecke.transpose_mul`: `(h₁ * h₂)ᵀ = h₂ᵀ * h₁ᵀ`.
* `TauCeti.PermutationHecke.transpose_one`: `1ᵀ = 1`.
* `TauCeti.PermutationHecke.transpose_indicator_orbit`: the transpose of an orbit indicator.
* `TauCeti.HeckeAlgebraLevel.transpose_indicator_orbit`: `[UgU] ↦ [Ug⁻¹U]`.

## References

* D. Treumann and A. Venkatesh, *Functoriality, Smith theory, and the Brauer homomorphism*,
  Ann. of Math. 183 (2016), §2.10, (2.10.1)–(2.10.3), pp. 187–188 (arXiv:1407.2346v1 §2.10).
-/

public section
noncomputable section

open MulAction

namespace TauCeti

namespace PermutationHecke

variable {G S : Type*} [Group G] [MulAction G S] {A : Type*} [CommRing A]

/-- Swapping the coordinates maps diagonal orbits to diagonal orbits. -/
private theorem mk_swap_eq_of_mk_eq {p q : S × S}
    (h : Quotient.mk (orbitRel G (S × S)) p = Quotient.mk (orbitRel G (S × S)) q) :
    Quotient.mk (orbitRel G (S × S)) p.swap = Quotient.mk (orbitRel G (S × S)) q.swap := by
  obtain ⟨g, hg⟩ := Quotient.exact h
  exact Quotient.sound ⟨g, by rw [← hg]; rfl⟩

/-- The transpose `(x, y) ↦ h(y, x)` of an element of `Fun_G(S × S, A)` lies in
`Fun_G(S × S, A)`. -/
theorem transpose_mem (h : permutationHeckeModule G S A) :
    (fun p : S × S ↦ (h : S × S → A) p.swap) ∈ permutationHeckeModule G S A := by
  have hh := mem_iff.1 h.property
  refine mem_iff.2 ⟨fun g p ↦ hh.1 g p.swap, ?_⟩
  let f : Quotient (orbitRel G (S × S)) → Quotient (orbitRel G (S × S)) :=
    Quotient.lift (fun p ↦ Quotient.mk (orbitRel G (S × S)) p.swap)
      fun _ _ hpq ↦ mk_swap_eq_of_mk_eq (Quotient.sound hpq)
  refine (hh.2.image f).subset ?_
  rintro _ ⟨p, hp, rfl⟩
  exact ⟨Quotient.mk _ p.swap, ⟨p.swap, hp, rfl⟩, rfl⟩

variable (G S A) in
/-- The **transpose** `hᵀ(x, y) = h(y, x)` on `Fun_G(S × S, A)`, an involutive `A`-linear
equivalence. -/
def transpose : permutationHeckeModule G S A ≃ₗ[A] permutationHeckeModule G S A where
  toFun h := ⟨_, transpose_mem h⟩
  invFun h := ⟨_, transpose_mem h⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
theorem transpose_apply (h : permutationHeckeModule G S A) (x y : S) :
    ((transpose G S A h : permutationHeckeModule G S A) : S × S → A) (x, y) =
      (h : S × S → A) (y, x) :=
  (rfl)

@[simp]
theorem transpose_transpose (h : permutationHeckeModule G S A) :
    transpose G S A (transpose G S A h) = h :=
  (rfl)

@[simp]
theorem transpose_symm : (transpose G S A).symm = transpose G S A :=
  (rfl)

/-- The transpose of the indicator of the orbit of `p` is the indicator of the orbit of
`p.swap`. -/
theorem transpose_indicator_orbit (p : S × S) :
    transpose G S A ⟨_, indicator_orbit_mem p⟩ = ⟨_, indicator_orbit_mem p.swap⟩ := by
  refine Subtype.ext (funext fun q ↦ ?_)
  change Set.indicator (orbit G p) 1 q.swap = Set.indicator (orbit G p.swap) 1 q
  have hq : q.swap ∈ orbit G p ↔ q ∈ orbit G p.swap :=
    ⟨fun ⟨g, hg⟩ ↦ ⟨g, by rw [← Prod.swap_swap q, ← hg]; rfl⟩,
      fun ⟨g, hg⟩ ↦ ⟨g, by rw [← hg]; rfl⟩⟩
  by_cases h : q ∈ orbit G p.swap
  · rw [Set.indicator_of_mem (hq.2 h), Set.indicator_of_mem h]
    rfl
  · rw [Set.indicator_of_notMem (mt hq.1 h), Set.indicator_of_notMem h]

variable [FiniteStabilizerOrbits G S]

/-- **The transpose reverses the matrix product**: `(h₁ * h₂)ᵀ = h₂ᵀ * h₁ᵀ`. -/
theorem transpose_mul (h₁ h₂ : permutationHeckeModule G S A) :
    transpose G S A (h₁ * h₂) = transpose G S A h₂ * transpose G S A h₁ := by
  refine Subtype.ext (funext fun ⟨x, z⟩ ↦ ?_)
  rw [transpose_apply, mul_apply, mul_apply]
  exact finsum_congr fun y ↦ by rw [transpose_apply, transpose_apply, mul_comm]

omit [FiniteStabilizerOrbits G S] in
/-- The transpose fixes the unit. -/
@[simp]
theorem transpose_one [Finite (orbitRel.Quotient G S)] :
    transpose G S A (1 : permutationHeckeModule G S A) = 1 := by
  classical
  refine Subtype.ext (funext fun ⟨x, y⟩ ↦ ?_)
  rw [transpose_apply, one_apply, one_apply, Finsupp.single_apply, Finsupp.single_apply]
  exact if_congr eq_comm rfl rfl

variable (G S A) in
/-- **The transpose anti-involution**: for finitely many orbits, the transpose is an algebra
isomorphism of `Fun_G(S × S, A)` with its opposite algebra. -/
def transposeAlgEquiv [Finite (orbitRel.Quotient G S)] :
    permutationHeckeModule G S A ≃ₐ[A] (permutationHeckeModule G S A)ᵐᵒᵖ :=
  AlgEquiv.ofLinearEquiv ((transpose G S A).trans (MulOpposite.opLinearEquiv A))
    (by simp) fun h₁ h₂ ↦ by simp [transpose_mul]

@[simp]
theorem transposeAlgEquiv_apply [Finite (orbitRel.Quotient G S)]
    (h : permutationHeckeModule G S A) :
    transposeAlgEquiv G S A h = MulOpposite.op (transpose G S A h) :=
  (rfl)

end PermutationHecke

namespace HeckeAlgebraLevel

variable {G : Type*} [Group G] {U : Subgroup G} {A : Type*} [CommRing A]

/-- **`[UgU] ↦ [Ug⁻¹U]`**: in the Hecke algebra of level `U`, the transpose sends the indicator of
the orbit of `(U, gU)`, the basis element of the double coset `UgU`, to the indicator of the orbit
of `(U, g⁻¹U)`. -/
theorem transpose_indicator_orbit (g : G) :
    PermutationHecke.transpose G (G ⧸ U) A
        ⟨_, PermutationHecke.indicator_orbit_mem (((1 : G) : G ⧸ U), (g : G ⧸ U))⟩ =
      ⟨_, PermutationHecke.indicator_orbit_mem (((1 : G) : G ⧸ U), ((g⁻¹ : G) : G ⧸ U))⟩ := by
  rw [PermutationHecke.transpose_indicator_orbit]
  refine Subtype.ext ?_
  change Set.indicator (orbit G ((g : G ⧸ U), ((1 : G) : G ⧸ U))) 1 =
    Set.indicator (orbit G (((1 : G) : G ⧸ U), ((g⁻¹ : G) : G ⧸ U))) 1
  rw [← orbit_smul g⁻¹ ((g : G ⧸ U), ((1 : G) : G ⧸ U))]
  congr 3
  simp [Prod.smul_mk, MulAction.Quotient.smul_mk]

end HeckeAlgebraLevel

end TauCeti
