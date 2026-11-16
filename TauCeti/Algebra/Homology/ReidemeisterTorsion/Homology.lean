/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.ReidemeisterTorsion.Periodic
import Mathlib.Algebra.FiniteSupport.Basic
import TauCeti.Algebra.BigOperators.Finprod

/-!
# The torsion of a based chain complex with based homology

Let `C` be a `ℤ`-graded chain complex of vector spaces over a field `F`, with an ordered basis
`c i` of each `C.X i` and an ordered basis `h i` of each homology group `Hᵢ(C)`. Write
`Bⱼ ⊆ Zⱼ ⊆ Cⱼ` for the boundaries and the cycles. The sequences

`0 → Bⱼ₊₁ → Zⱼ₊₁ → Hⱼ₊₁ → 0` and `0 → Zⱼ₊₁ → Cⱼ₊₁ → Bⱼ → 0`

are short exact for every complex, so a basis `bⱼ₊₁` of `Bⱼ₊₁`, cycles `zⱼ₊₁` representing the
basis `hⱼ₊₁` of `Hⱼ₊₁`, and lifts `sⱼ` through `d` of a basis `bⱼ` of `Bⱼ` give an ordered basis
`(bⱼ₊₁, zⱼ₊₁, sⱼ)` of `Cⱼ₊₁`. Its determinant with respect to `cⱼ₊₁` is the *bracket*
`[bⱼ₊₁ zⱼ₊₁ sⱼ / cⱼ₊₁]` (`HomologicalComplex.torsionBracketWithHomology`), and the torsion of `C`
with respect to the bases `c` and `h` is the alternating product

`τ(C, c, h) = ∏ⱼ [bⱼ₊₁ zⱼ₊₁ sⱼ / cⱼ₊₁] ^ ((-1) ^ j)`

(`HomologicalComplex.reidemeisterTorsionWithHomology`), defined to be `0` when the complex is
unbounded. The bracket in degree `i` carries the exponent `(-1) ^ (i + 1)`, as for the torsion
`HomologicalComplex.reidemeisterTorsion` of an acyclic complex.

Unlike the torsion of an acyclic complex, `τ(C, c, h)` is nonzero for every bounded complex
(`HomologicalComplex.reidemeisterTorsionWithHomology_ne_zero`), so it retains information about
complexes that are not acyclic: it compares the volume given by the chain bases with the
alternating volume given by the homology bases. For a bounded complex it does not depend on the
boundary bases, the lifts, or the cycles chosen to represent the homology bases
(`HomologicalComplex.reidemeisterTorsionWithHomology_eq_finprod`); for an acyclic complex it is
the torsion `HomologicalComplex.reidemeisterTorsion`
(`HomologicalComplex.reidemeisterTorsionWithHomology_eq_reidemeisterTorsion`).

Replacing the chain bases `c i` by `c' i` multiplies `τ(C, c, h)` by `∏ᵢ [c'ᵢ / cᵢ] ^ ((-1) ^ i)`
(`HomologicalComplex.reidemeisterTorsionWithHomology_eq_mul_finprod_det`), and replacing the
homology bases `h i` by `h' i` multiplies it by `∏ᵢ [h'ᵢ / hᵢ] ^ ((-1) ^ (i + 1))`
(`HomologicalComplex.reidemeisterTorsionWithHomology_eq_mul_finprod_det_homology`), where `[x / y]`
denotes the determinant of the basis `x` with respect to the basis `y`.

The bracket is defined for complexes of any shape, in a degree `j` between a previous degree `i`
and a next degree `k`. It also refines the torsion of a two-periodic complex `C`, indexed by
`ZMod 2` with differentials `d₀ : C₀ → C₁` and `d₁ : C₁ → C₀`, such as a Floer complex graded only
modulo two. With bases `c 0`, `c 1` of the chain spaces and `h 0`, `h 1` of the homology, its
torsion is the quotient

`τ(C, c, h) = [b₁ z₁ s₁ / c₁] · [b₀ z₀ s₀ / c₀]⁻¹`

of the odd bracket by the even one (`HomologicalComplex.parityTorsionWithHomology`), with the
normalization of `HomologicalComplex.parityTorsion`. It needs no boundedness condition and is
never `0` (`HomologicalComplex.parityTorsionWithHomology_ne_zero`), so it keeps a nonzero scalar
for complexes that are not acyclic, where `HomologicalComplex.parityTorsion` is `0`. It does not
depend on the choices (`HomologicalComplex.parityTorsionWithHomology_eq`), it is
`HomologicalComplex.parityTorsion` for an acyclic complex
(`HomologicalComplex.parityTorsionWithHomology_eq_parityTorsion`), and replacing the bases
multiplies it by `[c'₀ / c₀] · [c'₁ / c₁]⁻¹` for the chain bases and by `[h'₁ / h₁] · [h'₀ / h₀]⁻¹`
for the homology bases. When both differentials vanish it is `[z₁ / c₁] · [z₀ / c₀]⁻¹` for cycles
`z` representing the homology bases
(`HomologicalComplex.parityTorsionWithHomology_of_d_eq_zero`).

## Main declarations

* `HomologicalComplex.torsionBracketWithHomology`: the bracket `[b z s / cⱼ]` of a degree `j`.
* `HomologicalComplex.torsionBracketWithHomology_eq_det_append`: the bracket is the determinant of
  the boundary basis followed by the homology representatives and the lifts.
* `HomologicalComplex.torsionBracketWithHomology_eq_mul`: the change of a bracket under a change
  of the boundary bases, the homology basis, the representatives and the lifts.
* `HomologicalComplex.reidemeisterTorsionWithHomology`: the torsion `τ(C, c, h)`.
* `HomologicalComplex.reidemeisterTorsionWithHomology_eq_finprod`: for a bounded complex, the
  torsion is the alternating product of the brackets for any choices.
* `HomologicalComplex.reidemeisterTorsionWithHomology_ne_zero`: the torsion of a bounded complex is
  nonzero.
* `HomologicalComplex.reidemeisterTorsionWithHomology_eq_reidemeisterTorsion`: for an acyclic
  complex it is the torsion of the based acyclic complex.
* `HomologicalComplex.reidemeisterTorsionWithHomology_eq_mul_finprod_det` and
  `HomologicalComplex.reidemeisterTorsionWithHomology_eq_mul_finprod_det_homology`: the change of
  the torsion under a change of the chain bases and of the homology bases.
* `HomologicalComplex.parityTorsionWithHomology`: the torsion `τ(C, c, h)` of a two-periodic
  complex, with `HomologicalComplex.parityTorsionWithHomology_eq` (independence of the choices),
  `HomologicalComplex.parityTorsionWithHomology_ne_zero`,
  `HomologicalComplex.parityTorsionWithHomology_eq_parityTorsion`,
  `HomologicalComplex.parityTorsionWithHomology_eq_mul_det` and
  `HomologicalComplex.parityTorsionWithHomology_eq_mul_det_homology` (basis changes), and
  `HomologicalComplex.parityTorsionWithHomology_of_d_eq_zero` (vanishing differentials).

## References

* J. Milnor, *Whitehead torsion*, Bull. Amer. Math. Soc. 72 (1966), §3.
* V. Turaev, *Introduction to combinatorial torsions*, Birkhäuser 2001, §1.
* M. Hutchings, Y.-J. Lee, *Circle-valued Morse theory, Reidemeister torsion, and Seiberg–Witten
  invariants of 3-manifolds*, Topology 38 (1999), §2.
-/

public section

noncomputable section

open CategoryTheory Module

namespace HomologicalComplex

variable {F : Type*} [Field F]

section Bracket

variable {ι : Type*} {cs : ComplexShape ι} {C : HomologicalComplex (ModuleCat F) cs} {n : ι → ℕ}
  (c : ∀ i, Basis (Fin (n i)) F (C.X i))
  {i j k : ι} (hi : cs.prev j = i) (hk : cs.next j = k) {p m q : ℕ}
  (b₁ : Basis (Fin p) F (LinearMap.range (C.d i j).hom))
  (h : Basis (Fin m) F (C.homology j))
  (y : Fin m → C.cycles j) (hy : ∀ l, C.homologyπ j (y l) = h l)
  (b₀ : Basis (Fin q) F (LinearMap.range (C.d j k).hom))
  (s : Fin q → C.X j) (hs : ∀ l, (C.d j k).hom (s l) = b₀ l)

/-- The basis `(b₁, y)` of the cycles `Zⱼ` made of a basis `b₁` of the boundaries `Bⱼ`, the image
of the differential from the previous degree `i`, followed by cycles `y` representing a basis `h`
of the homology `Hⱼ`. -/
private def cyclesBasis : Basis (Fin p ⊕ Fin m) F (LinearMap.ker (C.d j k).hom) :=
  Basis.ofExactLift (Submodule.inclusion_injective _)
    (C.exact_inclusion_moduleCatKerHomologyClass hk hi) b₁ h (C.moduleCatCyclesToKer j k ∘ y)
    fun l ↦ by rw [Function.comp_apply, moduleCatKerHomologyClass_moduleCatCyclesToKer, hy]

/-- The basis `(b₁, y, s)` of `Cⱼ` made of a basis `b₁` of the boundaries `Bⱼ`, cycles `y`
representing a basis `h` of the homology `Hⱼ`, and lifts `s` of a basis `b₀` of the image of the
differential to the next degree `k`. -/
private def bracketBasis : Basis ((Fin p ⊕ Fin m) ⊕ Fin q) F (C.X j) :=
  -- The sequence `Zⱼ → Cⱼ → Bₖ` is exact.
  Basis.ofExactLift (Submodule.injective_subtype _)
    (LinearMap.exact_iff.2 (by rw [LinearMap.ker_rangeRestrict, Submodule.range_subtype]))
    (cyclesBasis hi hk b₁ h y hy) b₀ s fun l ↦ Subtype.ext (hs l)

include c hi hk b₁ h y hy b₀ s hs in
private theorem eq_add_add : n j = p + m + q := by
  simpa using Fintype.card_congr ((c j).indexEquiv (bracketBasis hi hk b₁ h y hy b₀ s hs))

/-- The reindexing of `Fin (p + m + q)` by `(Fin p ⊕ Fin m) ⊕ Fin q`, in increasing order. -/
private def finSumSumEquiv (hn : n j = p + m + q) : Fin (n j) ≃ (Fin p ⊕ Fin m) ⊕ Fin q :=
  (finCongr hn).trans (finSumFinEquiv.symm.trans (Equiv.sumCongr finSumFinEquiv.symm (.refl _)))

/-- The bracket `[b₁ y s / cⱼ]`: the determinant, with respect to the basis `c j` of `Cⱼ`, of the
family made of a basis `b₁` of the boundaries `Bⱼ ⊆ Cⱼ`, the image of the differential from the
previous degree `i`, followed by cycles `y` representing a basis `h` of the homology `Hⱼ`, followed
by lifts `s` of a basis `b₀` of the image of the differential from `Cⱼ` to the next degree `k`. For
a chain complex graded by `ℤ` and `j + 1` in place of `j`, this is the bracket
`[bⱼ₊₁ zⱼ₊₁ sⱼ / cⱼ₊₁]`. -/
def torsionBracketWithHomology : F :=
  ((c j).reindex (finSumSumEquiv (eq_add_add c hi hk b₁ h y hy b₀ s hs))).det
    (bracketBasis hi hk b₁ h y hy b₀ s hs)

/-- The bracket `[b₁ y s / cⱼ]` is the determinant, with respect to the basis `c j` of `Cⱼ`, of
the family `(b₁, y, s)` obtained by appending to the basis `b₁` of the boundaries `Bⱼ` the cycles
`y` representing the homology basis `h` and the lifts `s`. -/
theorem torsionBracketWithHomology_eq_det_append (hn : n j = p + m + q) :
    torsionBracketWithHomology c hi hk b₁ h y hy b₀ s hs =
      (c j).det (Fin.append (Fin.append (fun l ↦ (b₁ l : C.X j))
        fun l ↦ C.iCycles j (y l)) s ∘ Fin.cast hn) := by
  rw [torsionBracketWithHomology, Basis.det_reindex]
  congr 1
  ext l
  obtain ⟨l, rfl⟩ := (finCongr hn.symm).surjective l
  induction l using Fin.addCases with
  | left l => induction l using Fin.addCases <;> simp [bracketBasis, cyclesBasis, finSumSumEquiv]
  | right l => simp [bracketBasis, finSumSumEquiv]

/-- Reindexing the boundary bases of a bracket along equalities of their lengths does not change
the bracket. -/
private theorem torsionBracketWithHomology_reindex {p' q' : ℕ} (hp : p = p') (hq : q = q') :
    torsionBracketWithHomology c hi hk (b₁.reindex (finCongr hp)) h y hy
      (b₀.reindex (finCongr hq)) (s ∘ Fin.cast hq.symm) (fun l ↦ by simp [hs]) =
      torsionBracketWithHomology c hi hk b₁ h y hy b₀ s hs := by
  subst hp hq
  congr 1 <;> simp

/-- Replacing the boundary bases, the homology basis, its representatives and the lifts in a
bracket multiplies it by the determinants of the new boundary and homology bases with respect to
the old ones; in particular the bracket does not depend on the representatives nor on the lifts. -/
theorem torsionBracketWithHomology_eq_mul
    (b₁' : Basis (Fin p) F (LinearMap.range (C.d i j).hom))
    (h' : Basis (Fin m) F (C.homology j))
    (y' : Fin m → C.cycles j) (hy' : ∀ l, C.homologyπ j (y' l) = h' l)
    (b₀' : Basis (Fin q) F (LinearMap.range (C.d j k).hom))
    (s' : Fin q → C.X j) (hs' : ∀ l, (C.d j k).hom (s' l) = b₀' l) :
    torsionBracketWithHomology c hi hk b₁' h' y' hy' b₀' s' hs' =
      torsionBracketWithHomology c hi hk b₁ h y hy b₀ s hs *
        (b₁.det b₁' * h.det h' * b₀.det b₀') := by
  simp only [torsionBracketWithHomology, bracketBasis]
  rw [Basis.det_ofExactLift _ _ (cyclesBasis hi hk b₁ h y hy) (cyclesBasis hi hk b₁' h' y' hy'),
    cyclesBasis, cyclesBasis, Basis.ofExactLift_det_ofExactLift]

/-- Replacing the basis `c j` of `Cⱼ` by `c' j` multiplies a bracket by the determinant of `c j`
with respect to `c' j`. -/
theorem torsionBracketWithHomology_eq_det_mul (c' : ∀ i, Basis (Fin (n i)) F (C.X i)) :
    torsionBracketWithHomology c' hi hk b₁ h y hy b₀ s hs =
      (c' j).det (c j) * torsionBracketWithHomology c hi hk b₁ h y hy b₀ s hs := by
  rw [torsionBracketWithHomology, torsionBracketWithHomology, ← Basis.det_mul_det _
    ((c j).reindex (finSumSumEquiv (eq_add_add c hi hk b₁ h y hy b₀ s hs)))]
  simp [Basis.det_reindex, Function.comp_assoc]

/-- A bracket is nonzero. -/
theorem torsionBracketWithHomology_ne_zero :
    torsionBracketWithHomology c hi hk b₁ h y hy b₀ s hs ≠ 0 :=
  (Basis.isUnit_det _ _).ne_zero

/-- The bracket in a degree where the complex vanishes is `1`. -/
@[simp]
theorem torsionBracketWithHomology_eq_one (hn : n j = 0) :
    torsionBracketWithHomology c hi hk b₁ h y hy b₀ s hs = 1 := by
  have : IsEmpty (Fin (n j)) := by rw [hn]; infer_instance
  simp [torsionBracketWithHomology, Basis.det_reindex]

/-- In a degree `j` where `C` is exact, the homology basis `h` is empty and the bracket
`[b₁ y s / cⱼ]` is the bracket `[b₁ s / cⱼ]` of `HomologicalComplex.torsionBracket`. -/
theorem torsionBracketWithHomology_eq_torsionBracket (hC : C.ExactAt j) :
    torsionBracketWithHomology c hi hk b₁ h y hy b₀ s hs =
      torsionBracket c hi hk hC b₁ b₀ s hs := by
  have := ModuleCat.subsingleton_of_isZero hC.isZero_homology
  obtain rfl : m = 0 := Nat.eq_zero_of_not_pos fun hm ↦ h.ne_zero ⟨0, hm⟩ (Subsingleton.elim _ _)
  have hn := eq_add_add c hi hk b₁ h y hy b₀ s hs
  rw [torsionBracketWithHomology_eq_det_append c hi hk b₁ h y hy b₀ s hs hn,
    torsionBracket_eq_det_append c hi hk hC b₁ b₀ s hs (by simpa using hn)]
  congr 1
  ext l
  obtain ⟨l, rfl⟩ := (finCongr hn.symm).surjective l
  induction l using Fin.addCases with
  | left l => simp [Fin.append_right_nil _ _ rfl, Fin.append_left]
  | right l => simp [Fin.append_right]

end Bracket

section Chosen

variable {ι : Type*} {cs : ComplexShape ι} (C : HomologicalComplex (ModuleCat F) cs) {m : ι → ℕ}
  (h : ∀ i, Basis (Fin (m i)) F (C.homology i))

/-- Cycles representing the homology basis `h i`. -/
private def chosenCycle (i : ι) (k : Fin (m i)) : C.cycles i :=
  Function.surjInv (C.moduleCat_homologyπ_surjective i) (h i k)

private theorem chosenCycle_spec (i : ι) (k : Fin (m i)) :
    C.homologyπ i (chosenCycle C h i k) = h i k :=
  Function.surjInv_eq (C.moduleCat_homologyπ_surjective i) _

end Chosen

variable {C : ChainComplex (ModuleCat F) ℤ} {n : ℤ → ℕ} (c : ∀ i, Basis (Fin (n i)) F (C.X i))

section Torsion

variable (C)

variable {m : ℤ → ℕ} (h : ∀ i, Basis (Fin (m i)) F (C.homology i))

/-- The torsion `τ(C, c, h)` of a chain complex of vector spaces with ordered bases `c i` of each
`C.X i` and ordered bases `h i` of each homology group `Hᵢ(C)`: the alternating product
`∏ⱼ [bⱼ₊₁ zⱼ₊₁ sⱼ / cⱼ₊₁] ^ ((-1) ^ j)` of the brackets when `C` is bounded (only finitely many
`n i` are nonzero), for a choice of bases `bⱼ` of the boundaries, of cycles `zⱼ` representing
`h j`, and of lifts `sⱼ` of `bⱼ`, and `0` otherwise. The product does not depend on these
choices (`reidemeisterTorsionWithHomology_eq_finprod`). -/
def reidemeisterTorsionWithHomology : F := by
  classical
  exact if {i | n i ≠ 0}.Finite then
    ∏ᶠ j : ℤ, torsionBracketWithHomology c (by simp) (by simp)
      (chosenBoundaryBasis C c (j + 1 + 1) (j + 1)) (h (j + 1)) (chosenCycle C h (j + 1))
      (chosenCycle_spec C h (j + 1))
      (chosenBoundaryBasis C c (j + 1) j) (chosenBoundaryLift C c (j + 1) j)
      (chosenBoundaryLift_spec C c (j + 1) j) ^ (j.negOnePow : ℤ)
  else 0

/-- The torsion of an unbounded complex, one with infinitely many nonzero `n i`, is `0`. -/
@[simp]
theorem reidemeisterTorsionWithHomology_of_not_finite (hn : ¬{i | n i ≠ 0}.Finite) :
    C.reidemeisterTorsionWithHomology c h = 0 := by
  simp [reidemeisterTorsionWithHomology, hn]

variable {C c h}

section Bounded

variable (hn : {i | n i ≠ 0}.Finite)

include hn in
/-- For a bounded complex, the alternating brackets have finite multiplicative support. -/
private theorem hasFiniteMulSupport_torsionBracketWithHomology {r : ℤ → ℕ}
    (b : ∀ j, Basis (Fin (r j)) F (LinearMap.range (C.d (j + 1) j).hom))
    (y : ∀ i, Fin (m i) → C.cycles i) (hy : ∀ i k, C.homologyπ i (y i k) = h i k)
    (s : ∀ j, Fin (r j) → C.X (j + 1)) (hs : ∀ j k, (C.d (j + 1) j).hom (s j k) = b j k) :
    Function.HasFiniteMulSupport fun j : ℤ ↦ torsionBracketWithHomology c (by simp) (by simp)
      (b (j + 1)) (h (j + 1)) (y (j + 1)) (hy (j + 1)) (b j) (s j) (hs j) ^ (j.negOnePow : ℤ) :=
  (hn.preimage (add_left_injective (1 : ℤ)).injOn).subset <|
    Function.mulSupport_subset_iff'.2 fun j hj ↦ by
      rw [torsionBracketWithHomology_eq_one c _ _ _ _ _ _ _ _ _ (by simpa using hj), one_zpow]

include hn in
/-- For a bounded complex, the alternating product of the brackets does not depend on the bases of
the boundaries, the representatives of the homology bases nor the lifts. -/
private theorem finprod_torsionBracketWithHomology_eq
    (b b' : ∀ j, Basis (Fin (finrank F (LinearMap.range (C.d (j + 1) j).hom))) F
      (LinearMap.range (C.d (j + 1) j).hom))
    (y y' : ∀ i, Fin (m i) → C.cycles i) (hy : ∀ i k, C.homologyπ i (y i k) = h i k)
    (hy' : ∀ i k, C.homologyπ i (y' i k) = h i k)
    (s s' : ∀ j, Fin (finrank F (LinearMap.range (C.d (j + 1) j).hom)) → C.X (j + 1))
    (hs : ∀ j k, (C.d (j + 1) j).hom (s j k) = b j k)
    (hs' : ∀ j k, (C.d (j + 1) j).hom (s' j k) = b' j k) :
    ∏ᶠ j : ℤ, torsionBracketWithHomology c (by simp) (by simp) (b' (j + 1)) (h (j + 1))
        (y' (j + 1)) (hy' (j + 1)) (b' j) (s' j) (hs' j) ^ (j.negOnePow : ℤ) =
      ∏ᶠ j : ℤ, torsionBracketWithHomology c (by simp) (by simp) (b (j + 1)) (h (j + 1))
        (y (j + 1)) (hy (j + 1)) (b j) (s j) (hs j) ^ (j.negOnePow : ℤ) := by
  -- Changing the boundary bases multiplies the bracket in degree `j + 1` by
  -- `[b'ⱼ₊₁ / bⱼ₊₁] [b'ⱼ / bⱼ]`.
  refine (finprod_congr fun j ↦ ?_).trans (TauCeti.finprod_mul_mul_add_one_zpow_negOnePow _
    (hasFiniteMulSupport_det_range_d C c hn b b') fun j ↦ (Basis.isUnit_det _ _).ne_zero)
  rw [torsionBracketWithHomology_eq_mul c _ _ (b (j + 1)) (h (j + 1)) (y (j + 1)) (hy (j + 1))
    (b j) (s j) (hs j), Basis.det_self, mul_one]

include hn in
/-- For a bounded complex, the torsion `τ(C, c, h)` is the alternating product
`∏ⱼ [bⱼ₊₁ zⱼ₊₁ sⱼ / cⱼ₊₁] ^ ((-1) ^ j)` of the brackets, for any bases `bⱼ` of the boundaries, any
cycles `zⱼ` representing the homology bases `h j` and any lifts `sⱼ` of `bⱼ`; the bases `bⱼ` may be
indexed by any `Fin (r j)`. -/
theorem reidemeisterTorsionWithHomology_eq_finprod {r : ℤ → ℕ}
    (b : ∀ j, Basis (Fin (r j)) F (LinearMap.range (C.d (j + 1) j).hom))
    (y : ∀ i, Fin (m i) → C.cycles i) (hy : ∀ i k, C.homologyπ i (y i k) = h i k)
    (s : ∀ j, Fin (r j) → C.X (j + 1)) (hs : ∀ j k, (C.d (j + 1) j).hom (s j k) = b j k) :
    C.reidemeisterTorsionWithHomology c h =
      ∏ᶠ j : ℤ, torsionBracketWithHomology c (by simp) (by simp) (b (j + 1)) (h (j + 1))
        (y (j + 1)) (hy (j + 1)) (b j) (s j) (hs j) ^ (j.negOnePow : ℤ) := by
  have hr (j : ℤ) : r j = finrank F (LinearMap.range (C.d (j + 1) j).hom) := by
    rw [finrank_eq_card_basis (b j), Fintype.card_fin]
  rw [reidemeisterTorsionWithHomology, ite_eq_left hn,
    finprod_torsionBracketWithHomology_eq hn (fun j ↦ (b j).reindex (finCongr (hr j)))
      (fun j ↦ chosenBoundaryBasis C c (j + 1) j) y (chosenCycle C h) hy (chosenCycle_spec C h)
      (fun j ↦ s j ∘ Fin.cast (hr j).symm) (fun j ↦ chosenBoundaryLift C c (j + 1) j)
      (fun j k ↦ by simp [hs]) (fun j ↦ chosenBoundaryLift_spec C c (j + 1) j)]
  exact finprod_congr fun j ↦ by rw [torsionBracketWithHomology_reindex]

include hn in
/-- The torsion `τ(C, c, h)` of a bounded complex is nonzero. -/
theorem reidemeisterTorsionWithHomology_ne_zero : C.reidemeisterTorsionWithHomology c h ≠ 0 := by
  rw [reidemeisterTorsionWithHomology, ite_eq_left hn]
  exact finprod_ne_zero fun j ↦
    zpow_ne_zero _ (torsionBracketWithHomology_ne_zero c _ _ _ _ _ _ _ _ _)

end Bounded

/-- For an acyclic complex, whose homology bases are necessarily empty, the torsion `τ(C, c, h)` is
the torsion `HomologicalComplex.reidemeisterTorsion` of the based acyclic complex. -/
theorem reidemeisterTorsionWithHomology_eq_reidemeisterTorsion (hC : C.Acyclic) :
    C.reidemeisterTorsionWithHomology c h = C.reidemeisterTorsion c := by
  by_cases hn : {i | n i ≠ 0}.Finite
  swap
  · simp [hn]
  let b (j : ℤ) := chosenBoundaryBasis C c (j + 1) j
  let s (j : ℤ) := chosenBoundaryLift C c (j + 1) j
  have hs (j : ℤ) := chosenBoundaryLift_spec C c (j + 1) j
  rw [reidemeisterTorsionWithHomology_eq_finprod hn b (chosenCycle C h) (chosenCycle_spec C h)
      s hs,
    reidemeisterTorsion_eq_finprod hn hC b s hs]
  refine finprod_congr fun j ↦ ?_
  rw [torsionBracketWithHomology_eq_torsionBracket c _ _ _ _ _ _ _ _ _ (hC (j + 1))]

section BasisChange

/-- The basis-change formula for the chain bases: replacing the bases `c i` of `C` by `c' i`
multiplies the torsion `τ(C, c, h)` by `∏ᵢ [c'ᵢ / cᵢ] ^ ((-1) ^ i)`, where `[c'ᵢ / cᵢ]` is the
determinant of `c' i` with respect to `c i`. This holds for every complex, both sides being `0`
when `C` is unbounded. -/
theorem reidemeisterTorsionWithHomology_eq_mul_finprod_det
    (c' : ∀ i, Basis (Fin (n i)) F (C.X i)) :
    C.reidemeisterTorsionWithHomology c' h =
      C.reidemeisterTorsionWithHomology c h * ∏ᶠ i : ℤ, (c i).det (c' i) ^ (i.negOnePow : ℤ) := by
  by_cases hn : {i | n i ≠ 0}.Finite
  swap
  · simp [hn]
  -- Compute both torsions with the same choices; the brackets then differ by the factors
  -- `[cⱼ₊₁ / c'ⱼ₊₁] ^ ((-1) ^ j) = [c'ⱼ₊₁ / cⱼ₊₁] ^ ((-1) ^ (j + 1))`.
  have hD : Function.HasFiniteMulSupport fun j : ℤ ↦
      (c (j + 1)).det (c' (j + 1)) ^ ((j + 1).negOnePow : ℤ) :=
    (hn.preimage (add_left_injective (1 : ℤ)).injOn).subset <|
      Function.mulSupport_subset_iff'.2 fun j hj ↦ by
        have hn0 : n (j + 1) = 0 := by simpa using hj
        have : IsEmpty (Fin (n (j + 1))) := by
          rw [hn0]; infer_instance
        simp
  have hshift : ∏ᶠ i : ℤ, (c i).det (c' i) ^ (i.negOnePow : ℤ) =
      ∏ᶠ j : ℤ, (c (j + 1)).det (c' (j + 1)) ^ ((j + 1).negOnePow : ℤ) :=
    (finprod_comp_equiv (Equiv.addRight 1)).symm
  let b (j : ℤ) := chosenBoundaryBasis C c (j + 1) j
  let s (j : ℤ) := chosenBoundaryLift C c (j + 1) j
  have hs (j : ℤ) := chosenBoundaryLift_spec C c (j + 1) j
  rw [reidemeisterTorsionWithHomology_eq_finprod (c := c) hn b (chosenCycle C h)
      (chosenCycle_spec C h) s hs,
    reidemeisterTorsionWithHomology_eq_finprod (c := c') hn b (chosenCycle C h)
      (chosenCycle_spec C h) s hs,
    hshift]
  refine (finprod_congr fun j ↦ ?_).trans
    (finprod_mul_distrib (hasFiniteMulSupport_torsionBracketWithHomology hn b _
      (chosenCycle_spec C h) s hs) hD)
  have hinv : (c (j + 1)).det (c' (j + 1)) = ((c' (j + 1)).det (c (j + 1)))⁻¹ :=
    eq_inv_of_mul_eq_one_left <| by rw [Basis.det_mul_det, Basis.det_self]
  rw [torsionBracketWithHomology_eq_det_mul c (c' := c'), hinv]
  simp [mul_zpow, Int.negOnePow_succ, mul_comm]

/-- The basis-change formula for the homology bases: replacing the bases `h i` of the homology
groups `Hᵢ(C)` by `h' i` multiplies the torsion `τ(C, c, h)` by `∏ᵢ [h'ᵢ / hᵢ] ^ ((-1) ^ (i + 1))`,
where `[h'ᵢ / hᵢ]` is the determinant of `h' i` with respect to `h i`. This holds for every
complex, both sides being `0` when `C` is unbounded. -/
theorem reidemeisterTorsionWithHomology_eq_mul_finprod_det_homology
    (h' : ∀ i, Basis (Fin (m i)) F (C.homology i)) :
    C.reidemeisterTorsionWithHomology c h' =
      C.reidemeisterTorsionWithHomology c h *
        ∏ᶠ i : ℤ, (h i).det (h' i) ^ ((i + 1).negOnePow : ℤ) := by
  by_cases hn : {i | n i ≠ 0}.Finite
  swap
  · simp [hn]
  -- Compute both torsions with the same boundary bases and lifts; the brackets in degree `j + 1`
  -- then differ by the factor `[h'ⱼ₊₁ / hⱼ₊₁] ^ ((-1) ^ j)`.
  have hD : Function.HasFiniteMulSupport fun j : ℤ ↦
      (h (j + 1)).det (h' (j + 1)) ^ ((j + 1 + 1).negOnePow : ℤ) :=
    (hn.preimage (add_left_injective (1 : ℤ)).injOn).subset <|
      Function.mulSupport_subset_iff'.2 fun j hj ↦ by
        -- The homology vanishes where the complex vanishes.
        have hn0 : n (j + 1) = 0 := by simpa using hj
        have : IsEmpty (Fin (n (j + 1))) := by
          rw [hn0]; infer_instance
        have := (c (j + 1)).repr.toEquiv.subsingleton
        have hC : C.ExactAt (j + 1) := .of_isZero (ModuleCat.isZero_of_subsingleton _)
        have := ModuleCat.subsingleton_of_isZero hC.isZero_homology
        have : IsEmpty (Fin (m (j + 1))) := ⟨fun k ↦ (h (j + 1)).ne_zero k (Subsingleton.elim _ _)⟩
        simp
  have hshift : ∏ᶠ i : ℤ, (h i).det (h' i) ^ ((i + 1).negOnePow : ℤ) =
      ∏ᶠ j : ℤ, (h (j + 1)).det (h' (j + 1)) ^ ((j + 1 + 1).negOnePow : ℤ) :=
    (finprod_comp_equiv (Equiv.addRight 1)).symm
  let b (j : ℤ) := chosenBoundaryBasis C c (j + 1) j
  let s (j : ℤ) := chosenBoundaryLift C c (j + 1) j
  have hs (j : ℤ) := chosenBoundaryLift_spec C c (j + 1) j
  rw [reidemeisterTorsionWithHomology_eq_finprod (h := h) hn b (chosenCycle C h)
      (chosenCycle_spec C h) s hs,
    reidemeisterTorsionWithHomology_eq_finprod (h := h') hn b (chosenCycle C h')
      (chosenCycle_spec C h') s hs,
    hshift]
  refine (finprod_congr fun j ↦ ?_).trans
    (finprod_mul_distrib (hasFiniteMulSupport_torsionBracketWithHomology hn b _
      (chosenCycle_spec C h) s hs) hD)
  rw [torsionBracketWithHomology_eq_mul c _ _ (b (j + 1)) (h (j + 1)) (chosenCycle C h (j + 1))
    (chosenCycle_spec C h (j + 1)) (b j) (s j) (hs j)]
  simp [Basis.det_self, mul_zpow, Int.negOnePow_succ]

end BasisChange

end Torsion

section Parity

/-! ### Two-periodic complexes -/

variable {C : HomologicalComplex (ModuleCat F) (ComplexShape.up (ZMod 2))} {n : ZMod 2 → ℕ}
  (c : ∀ i, Basis (Fin (n i)) F (C.X i)) {m : ZMod 2 → ℕ}
  (h : ∀ i, Basis (Fin (m i)) F (C.homology i))

variable (C) in
/-- The torsion `τ(C, c, h)` of a two-periodic complex of vector spaces with ordered bases `c 0`
of the even space and `c 1` of the odd space, and ordered bases `h 0`, `h 1` of its even and odd
homology: the quotient `[b₁ z₁ s₁ / c₁] · [b₀ z₀ s₀ / c₀]⁻¹` of the odd bracket by the even
bracket, for a choice of bases `b₀`, `b₁` of the boundaries, of cycles `z₀`, `z₁` representing
`h 0`, `h 1`, and of lifts `s₀`, `s₁`. The quotient does not depend on these choices
(`parityTorsionWithHomology_eq`). -/
def parityTorsionWithHomology : F :=
  torsionBracketWithHomology c ((ComplexShape.up _).prev_eq' (zero_add 1))
      ((ComplexShape.up _).next_eq' (CharTwo.add_self_eq_zero 1)) (chosenBoundaryBasis C c 0 1)
      (h 1) (chosenCycle C h 1) (chosenCycle_spec C h 1) (chosenBoundaryBasis C c 1 0)
      (chosenBoundaryLift C c 1 0) (chosenBoundaryLift_spec C c 1 0) *
    (torsionBracketWithHomology c ((ComplexShape.up _).prev_eq' (CharTwo.add_self_eq_zero 1))
      ((ComplexShape.up _).next_eq' (zero_add 1)) (chosenBoundaryBasis C c 1 0) (h 0)
      (chosenCycle C h 0) (chosenCycle_spec C h 0) (chosenBoundaryBasis C c 0 1)
      (chosenBoundaryLift C c 0 1) (chosenBoundaryLift_spec C c 0 1))⁻¹

/-- The torsion `τ(C, c, h)` of a two-periodic complex is the quotient
`[b₁ z₁ s₁ / c₁] · [b₀ z₀ s₀ / c₀]⁻¹` of its odd bracket by its even bracket, for any bases `b₀`
of the even boundaries `B₀ = im d₁` and `b₁` of the odd boundaries `B₁ = im d₀`, any cycles `z₀`,
`z₁` representing the homology bases `h 0`, `h 1`, and any lifts `s₁` of `b₀` through `d₁` and
`s₀` of `b₁` through `d₀`. -/
theorem parityTorsionWithHomology_eq {p q : ℕ}
    (b₀ : Basis (Fin p) F (LinearMap.range (C.d 1 0).hom))
    (b₁ : Basis (Fin q) F (LinearMap.range (C.d 0 1).hom))
    (z₀ : Fin (m 0) → C.cycles 0) (hz₀ : ∀ l, C.homologyπ 0 (z₀ l) = h 0 l)
    (z₁ : Fin (m 1) → C.cycles 1) (hz₁ : ∀ l, C.homologyπ 1 (z₁ l) = h 1 l)
    (s₀ : Fin q → C.X 0) (hs₀ : ∀ l, (C.d 0 1).hom (s₀ l) = b₁ l)
    (s₁ : Fin p → C.X 1) (hs₁ : ∀ l, (C.d 1 0).hom (s₁ l) = b₀ l) :
    C.parityTorsionWithHomology c h =
      torsionBracketWithHomology c ((ComplexShape.up _).prev_eq' (zero_add 1))
          ((ComplexShape.up _).next_eq' (CharTwo.add_self_eq_zero 1)) b₁ (h 1) z₁ hz₁ b₀ s₁
          hs₁ *
        (torsionBracketWithHomology c ((ComplexShape.up _).prev_eq' (CharTwo.add_self_eq_zero 1))
          ((ComplexShape.up _).next_eq' (zero_add 1)) b₀ (h 0) z₀ hz₀ b₁ s₀ hs₀)⁻¹ := by
  have hp : finrank F (LinearMap.range (C.d 1 0).hom) = p := by
    rw [finrank_eq_card_basis b₀, Fintype.card_fin]
  have hq : finrank F (LinearMap.range (C.d 0 1).hom) = q := by
    rw [finrank_eq_card_basis b₁, Fintype.card_fin]
  -- Reindex the chosen boundary bases to `Fin p` and `Fin q`, then replace them by `b₀` and `b₁`,
  -- the chosen cycles by `z₀` and `z₁`, and the chosen lifts by `s₀` and `s₁`.
  rw [parityTorsionWithHomology,
    ← torsionBracketWithHomology_reindex c _ _ _ (h 1) _ _ _ _ (chosenBoundaryLift_spec C c 1 0)
      hq hp,
    ← torsionBracketWithHomology_reindex c _ _ _ (h 0) _ _ _ _ (chosenBoundaryLift_spec C c 0 1)
      hp hq,
    torsionBracketWithHomology_eq_mul c _ _ b₁ (h 1) z₁ hz₁ b₀ s₁ hs₁,
    torsionBracketWithHomology_eq_mul c _ _ b₀ (h 0) z₀ hz₀ b₁ s₀ hs₀, Basis.det_self,
    Basis.det_self, mul_one, mul_one]
  -- Both brackets are multiplied by the same nonzero product of determinants, which cancels.
  have h₀ := (b₀.isUnit_det ((chosenBoundaryBasis C c 1 0).reindex (finCongr hp))).ne_zero
  have h₁ := (b₁.isUnit_det ((chosenBoundaryBasis C c 0 1).reindex (finCongr hq))).ne_zero
  field_simp

/-- The torsion `τ(C, c, h)` of a two-periodic complex is nonzero. -/
theorem parityTorsionWithHomology_ne_zero : C.parityTorsionWithHomology c h ≠ 0 :=
  mul_ne_zero (torsionBracketWithHomology_ne_zero c _ _ _ _ _ _ _ _ _)
    (inv_ne_zero (torsionBracketWithHomology_ne_zero c _ _ _ _ _ _ _ _ _))

/-- For an acyclic two-periodic complex, whose homology bases are necessarily empty, the torsion
`τ(C, c, h)` is the torsion `HomologicalComplex.parityTorsion` of the based acyclic complex. -/
theorem parityTorsionWithHomology_eq_parityTorsion (hC : C.Acyclic) :
    C.parityTorsionWithHomology c h = C.parityTorsion c := by
  rw [parityTorsionWithHomology, parityTorsion_eq hC (chosenBoundaryBasis C c 1 0)
      (chosenBoundaryBasis C c 0 1) (chosenBoundaryLift C c 0 1) (chosenBoundaryLift_spec C c 0 1)
      (chosenBoundaryLift C c 1 0) (chosenBoundaryLift_spec C c 1 0),
    torsionBracketWithHomology_eq_torsionBracket c _ _ _ _ _ _ _ _ _ (hC 1),
    torsionBracketWithHomology_eq_torsionBracket c _ _ _ _ _ _ _ _ _ (hC 0)]

/-- The torsion `τ(C, c, h)` of a two-periodic complex whose two differentials vanish: every
element is a cycle and the homology is the whole complex, and `τ(C, c, h)` is the quotient
`[z₁ / c₁] · [z₀ / c₀]⁻¹` of the determinants of the cycles `z₀`, `z₁` representing the homology
bases with respect to the chain bases. For instance the complex `F` placed in even degree, with
the basis `1` and the homology basis its class, has torsion `1`, whereas its torsion
`HomologicalComplex.parityTorsion` is `0`. -/
theorem parityTorsionWithHomology_of_d_eq_zero (hd₀ : C.d 0 1 = 0) (hd₁ : C.d 1 0 = 0)
    (z₀ : Fin (m 0) → C.cycles 0) (hz₀ : ∀ l, C.homologyπ 0 (z₀ l) = h 0 l)
    (z₁ : Fin (m 1) → C.cycles 1) (hz₁ : ∀ l, C.homologyπ 1 (z₁ l) = h 1 l)
    (hn₀ : n 0 = m 0) (hn₁ : n 1 = m 1) :
    C.parityTorsionWithHomology c h =
      (c 1).det (fun l ↦ C.iCycles 1 (z₁ (Fin.cast hn₁ l))) *
        ((c 0).det fun l ↦ C.iCycles 0 (z₀ (Fin.cast hn₀ l)))⁻¹ := by
  -- The boundaries vanish, so the boundary bases and the lifts are empty.
  have : Subsingleton (LinearMap.range (C.d 1 0).hom) := by
    rw [hd₁, ModuleCat.hom_zero, LinearMap.range_zero]
    infer_instance
  have : Subsingleton (LinearMap.range (C.d 0 1).hom) := by
    rw [hd₀, ModuleCat.hom_zero, LinearMap.range_zero]
    infer_instance
  rw [parityTorsionWithHomology_eq c h (Basis.empty _) (Basis.empty _) z₀ hz₀ z₁ hz₁ Fin.elim0
      (fun l ↦ l.elim0) Fin.elim0 (fun l ↦ l.elim0),
    torsionBracketWithHomology_eq_det_append c _ _ _ _ _ _ _ _ _ (by simpa using hn₁),
    torsionBracketWithHomology_eq_det_append c _ _ _ _ _ _ _ _ _ (by simpa using hn₀)]
  congr 3 <;> ext l <;> simp [Fin.append_left_nil _ _ rfl]

/-- The basis-change formula for the chain bases: replacing the bases `c i` of `C` by `c' i`
multiplies the torsion `τ(C, c, h)` by `[c'₀ / c₀] · [c'₁ / c₁]⁻¹`, where `[c'ᵢ / cᵢ]` is the
determinant of `c' i` with respect to `c i`. -/
theorem parityTorsionWithHomology_eq_mul_det (c' : ∀ i, Basis (Fin (n i)) F (C.X i)) :
    C.parityTorsionWithHomology c' h =
      C.parityTorsionWithHomology c h * ((c 0).det (c' 0) * ((c 1).det (c' 1))⁻¹) := by
  -- Compute both torsions with the same boundary bases, cycles and lifts.
  rw [parityTorsionWithHomology_eq (c := c') h (chosenBoundaryBasis C c 1 0)
      (chosenBoundaryBasis C c 0 1) (chosenCycle C h 0) (chosenCycle_spec C h 0)
      (chosenCycle C h 1) (chosenCycle_spec C h 1) (chosenBoundaryLift C c 0 1)
      (chosenBoundaryLift_spec C c 0 1) (chosenBoundaryLift C c 1 0)
      (chosenBoundaryLift_spec C c 1 0),
    parityTorsionWithHomology,
    torsionBracketWithHomology_eq_det_mul c _ _ _ _ _ _ _ _ _ c',
    torsionBracketWithHomology_eq_det_mul c _ _ _ _ _ _ _ _ _ c']
  simp only [← (c 0).det_inv (c' 0), ← (c 1).det_inv (c' 1), Units.val_inv_eq_inv_val,
    IsUnit.unit_spec, mul_inv, inv_inv]
  ring

/-- The basis-change formula for the homology bases: replacing the bases `h i` of the homology
`Hᵢ(C)` by `h' i` multiplies the torsion `τ(C, c, h)` by `[h'₁ / h₁] · [h'₀ / h₀]⁻¹`, where
`[h'ᵢ / hᵢ]` is the determinant of `h' i` with respect to `h i`. -/
theorem parityTorsionWithHomology_eq_mul_det_homology
    (h' : ∀ i, Basis (Fin (m i)) F (C.homology i)) :
    C.parityTorsionWithHomology c h' =
      C.parityTorsionWithHomology c h * ((h 1).det (h' 1) * ((h 0).det (h' 0))⁻¹) := by
  -- Compute both torsions with the same boundary bases and lifts.
  rw [parityTorsionWithHomology, parityTorsionWithHomology,
    torsionBracketWithHomology_eq_mul c _ _ (chosenBoundaryBasis C c 0 1) _ _
      (chosenCycle_spec C h 1) _ _ (chosenBoundaryLift_spec C c 1 0) _ (h' 1),
    torsionBracketWithHomology_eq_mul c _ _ (chosenBoundaryBasis C c 1 0) _ _
      (chosenCycle_spec C h 0) _ _ (chosenBoundaryLift_spec C c 0 1) _ (h' 0)]
  simp only [Basis.det_self, one_mul, mul_one, mul_inv]
  ring

end Parity

end HomologicalComplex
