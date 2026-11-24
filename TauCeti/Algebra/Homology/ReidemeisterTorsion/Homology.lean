/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.ModuleCat.Basis
public import TauCeti.Algebra.Homology.ReidemeisterTorsion.Basic
import Mathlib.Algebra.FiniteSupport.Basic
import TauCeti.Algebra.BigOperators.Finprod
import TauCeti.Algebra.Homology.ModuleCat.Finrank

/-!
# The torsion of a based chain complex with based homology

Let `C` be a `ℤ`-graded chain complex of vector spaces over a field `F`, with an ordered basis
`c i` of each `C.X i` and an ordered basis `h i` of each homology group `Hᵢ(C)`. Write
`Bⱼ ⊆ Zⱼ ⊆ Cⱼ` for the boundaries and the cycles. The sequences

`0 → Bⱼ₊₁ → Zⱼ₊₁ → Hⱼ₊₁ → 0` and `0 → Zⱼ₊₁ → Cⱼ₊₁ → Bⱼ → 0`

are short exact for every complex, so a basis `bⱼ₊₁` of `Bⱼ₊₁` and cycles `zⱼ₊₁` representing the
basis `hⱼ₊₁` of `Hⱼ₊₁` give an ordered basis `(bⱼ₊₁, zⱼ₊₁)` of `Zⱼ₊₁`
(`HomologicalComplex.kerBasisOfHomology`, from `TauCeti.Algebra.Homology.ModuleCat.Basis`), and
together with lifts `sⱼ` through `d` of a basis `bⱼ` of `Bⱼ` they give an ordered basis
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
and a next degree `k`, so that it also gives the torsion with based homology of a two-periodic
complex, `HomologicalComplex.parityTorsionWithHomology` in
`TauCeti.Algebra.Homology.ReidemeisterTorsion.Periodic.Homology`.

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

## References

* J. Milnor, *Whitehead torsion*, Bull. Amer. Math. Soc. 72 (1966), §3.
* V. Turaev, *Introduction to combinatorial torsions*, Birkhäuser 2001, §1.
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

/-- The basis `(b₁, y, s)` of `Cⱼ` made of a basis `b₁` of the boundaries `Bⱼ`, cycles `y`
representing a basis `h` of the homology `Hⱼ`, and lifts `s` of a basis `b₀` of the image of the
differential to the next degree `k`. -/
private def bracketBasis : Basis ((Fin p ⊕ Fin m) ⊕ Fin q) F (C.X j) :=
  -- The sequence `Zⱼ → Cⱼ → Bₖ` is exact.
  Basis.ofExactLift (Submodule.injective_subtype _)
    (LinearMap.exact_iff.2 (by rw [LinearMap.ker_rangeRestrict, Submodule.range_subtype]))
    (kerBasisOfHomology hi hk b₁ h y hy) b₀ s fun l ↦ Subtype.ext (hs l)

include c hi hk b₁ h y hy b₀ s hs in
/-- The dimension `n j` of `Cⱼ` is the sum of the dimensions `p`, `m` and `q` of the boundaries
`Bⱼ`, the homology `Hⱼ` and the image of the differential to the next degree `k`. -/
theorem eq_add_add_of_homology : n j = p + m + q := by
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
  ((c j).reindex (finSumSumEquiv (eq_add_add_of_homology c hi hk b₁ h y hy b₀ s hs))).det
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
  | left l => induction l using Fin.addCases <;> simp [bracketBasis, finSumSumEquiv]
  | right l => simp [bracketBasis, finSumSumEquiv]

/-- Reindexing the boundary bases of a bracket along equalities of their lengths does not change
the bracket. -/
theorem torsionBracketWithHomology_reindex {p' q' : ℕ} (hp : p = p') (hq : q = q') :
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
  rw [Basis.det_ofExactLift, kerBasisOfHomology_det_kerBasisOfHomology]

/-- Replacing the basis `c j` of `Cⱼ` by `c' j` multiplies a bracket by the determinant of `c j`
with respect to `c' j`. -/
theorem torsionBracketWithHomology_eq_det_mul (c' : ∀ i, Basis (Fin (n i)) F (C.X i)) :
    torsionBracketWithHomology c' hi hk b₁ h y hy b₀ s hs =
      (c' j).det (c j) * torsionBracketWithHomology c hi hk b₁ h y hy b₀ s hs := by
  rw [torsionBracketWithHomology, torsionBracketWithHomology, ← Basis.det_mul_det _
    ((c j).reindex (finSumSumEquiv (eq_add_add_of_homology c hi hk b₁ h y hy b₀ s hs)))]
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
  have hn := eq_add_add_of_homology c hi hk b₁ h y hy b₀ s hs
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

/-- Cycles representing the homology basis `h i`, chosen by `Function.surjInv`, used to define the
torsions with based homology. -/
def chosenCycle (i : ι) (k : Fin (m i)) : C.cycles i :=
  Function.surjInv (C.moduleCat_homologyπ_surjective i) (h i k)

/-- The cycles `chosenCycle C h i` represent the homology basis `h i`. -/
theorem chosenCycle_spec (i : ι) (k : Fin (m i)) :
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
theorem hasFiniteMulSupport_torsionBracketWithHomology {r : ℤ → ℕ}
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
    ((finite_homology_of_finite c h hn).preimage (add_left_injective (1 : ℤ)).injOn).subset <|
      Function.mulSupport_subset_iff'.2 fun j hj ↦ by
        have hm0 : m (j + 1) = 0 := by simpa using hj
        have : IsEmpty (Fin (m (j + 1))) := by rw [hm0]; infer_instance
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

/-- Reindexing the homology bases along equalities of their ranks in each degree preserves the
torsion `τ(C, c, h)`. -/
theorem reidemeisterTorsionWithHomology_reindex_homology
    (c : ∀ i, Basis (Fin (n i)) F (C.X i)) (h : ∀ i, Basis (Fin (m i)) F (C.homology i))
    {m' : ℤ → ℕ} (hm : ∀ i, m i = m' i) :
    C.reidemeisterTorsionWithHomology c (fun i ↦ (h i).reindex (finCongr (hm i))) =
      C.reidemeisterTorsionWithHomology c h := by
  have hm_eq : m = m' := funext hm
  subst hm_eq
  congr 1
  ext i k
  simp

end BasisChange

end Torsion

end HomologicalComplex
