/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.SymplecticGroup.BlockSucc
public import TauCeti.RepresentationTheory.ClassicalGroups.Symplectic

/-!
# Branching of the symplectic standard representation along the block inclusion

The symplectic block inclusion `TauCeti.symplecticBlockSucc : Sp(2n, k) →* Sp(2(n+1), k)` lets a
symplectic matrix act on the coordinates of `k^{2n}` and fixes the last hyperbolic plane pointwise,
so restricting the standard representation of `Sp(2(n+1), k)` along it leaves the two coordinates of
that plane alone.  This file proves that, in the form

`Res (stdSymplecticRep k (n + 1)) ≅ stdSymplecticRep k n ⊕ k²`,

with `k²` the trivial representation on the plane, as
`TauCeti.stdSymplecticRepBlockSuccEquiv`.  It records that the splitting is **orthogonal** for the
invariant alternating form, which restricts to the standard symplectic form of `k^{2n}` on the first
summand and to that of the plane `k²` on the second
(`TauCeti.stdSymplecticBilinForm_eq_stdSymplecticRepBlockSuccEquiv`), and derives the character
identity `TauCeti.char_stdSymplecticRep_symplecticBlockSucc`.

This is the branching problem `Sp(2(n+1)) ↓ Sp(2n)` for the standard representation, the symplectic
counterpart of `TauCeti.stdOrthogonalRepBlockSuccEquiv`.  Unlike the orthogonal case, the
complement of the smaller standard module is not a line but a plane, because a nondegenerate
alternating form lives only on even-dimensional spaces; the trivial summand is two-dimensional.  The
decomposition of the other irreducible representations along this chain is type-specific and needs
the symplectic highest-weight classification, so it is not proved here.

The splitting is the linear isomorphism that reads a vector of `(Fin (n + 1) ⊕ Fin (n + 1)) → k`
through `TauCeti.finSuccSumFinSuccEquiv` and separates its coordinates on `k^{2n}` from those on the
last hyperbolic plane.

## Main definitions

* `TauCeti.stdSymplecticRepBlockSuccEquiv`: the branching isomorphism, an equivalence of
  representations of `Matrix.symplecticGroup (Fin n) k`.

## Main results

* `TauCeti.stdSymplecticRep_symplecticBlockSucc_apply_symm_inl` and
  `TauCeti.stdSymplecticRep_symplecticBlockSucc_apply_symm_inr`: the restricted standard action
  multiplies the coordinates of `k^{2n}` by `g` and fixes those of the last hyperbolic plane.
* `TauCeti.stdSymplecticBilinForm_eq_stdSymplecticRepBlockSuccEquiv`: the branching splits the
  invariant alternating form as an orthogonal direct sum.
* `TauCeti.stdSymplecticRep_comp_symplecticBlockSucc_injective`: the restriction is still faithful.
* `TauCeti.char_stdSymplecticRep_symplecticBlockSucc`: the character of the restriction is the
  character of the standard representation plus two.

## References

* R. Goodman and N. R. Wallach, *Symmetry, Representations, and Invariants*, Springer GTM 255
  (2009), Chapter 8, on branching laws for the classical groups along this chain of subgroups.
-/

public section

open Matrix

universe u

namespace TauCeti

variable (k : Type u) (n : ℕ)

section CommRing

variable [CommRing k]

/-- **The restricted standard symplectic action on the coordinates of `k^{2n}`**: `g` multiplies
them by its matrix. -/
theorem stdSymplecticRep_symplecticBlockSucc_apply_symm_inl (g : symplecticGroup (Fin n) k)
    (v : Fin (n + 1) ⊕ Fin (n + 1) → k) (x : Fin n ⊕ Fin n) :
    stdSymplecticRep k (n + 1) (symplecticBlockSucc n k g) v
        ((finSuccSumFinSuccEquiv n).symm (Sum.inl x)) =
      ((g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) k) *ᵥ
        fun y => v ((finSuccSumFinSuccEquiv n).symm (Sum.inl y))) x := by
  rw [stdSymplecticRep_apply_apply, coe_symplecticBlockSucc, sumBlockSucc_mulVec_symm_inl]

/-- **The restricted standard symplectic action on the last hyperbolic plane** is trivial. -/
theorem stdSymplecticRep_symplecticBlockSucc_apply_symm_inr (g : symplecticGroup (Fin n) k)
    (v : Fin (n + 1) ⊕ Fin (n + 1) → k) (x : Fin 1 ⊕ Fin 1) :
    stdSymplecticRep k (n + 1) (symplecticBlockSucc n k g) v
        ((finSuccSumFinSuccEquiv n).symm (Sum.inr x)) =
      v ((finSuccSumFinSuccEquiv n).symm (Sum.inr x)) := by
  rw [stdSymplecticRep_apply_apply, coe_symplecticBlockSucc, sumBlockSucc_mulVec_symm_inr]

/-- **Branching of the standard representation of `Sp(2(n+1), k)` to `Sp(2n, k)`.**  The
restriction along the symplectic block inclusion is the standard representation of the smaller
symplectic group plus the trivial representation on the last hyperbolic plane, carried by the
splitting of a vector into its coordinates on `k^{2n}` and on that plane. -/
noncomputable def stdSymplecticRepBlockSuccEquiv :
    Representation.Equiv
      ((stdSymplecticRep k (n + 1)).comp (symplecticBlockSucc n k) :
        Representation k (symplecticGroup (Fin n) k) (Fin (n + 1) ⊕ Fin (n + 1) → k))
      ((stdSymplecticRep k n).prod
        (Representation.trivial k (symplecticGroup (Fin n) k) (Fin 1 ⊕ Fin 1 → k))) :=
  Representation.Equiv.mk
    ((LinearEquiv.funCongrLeft k k (finSuccSumFinSuccEquiv n).symm).trans
      (LinearEquiv.sumArrowLequivProdArrow _ _ k k))
    fun g => LinearMap.ext fun v => Prod.ext
      (funext fun x => by
        simp [LinearMap.funLeft, Function.comp_def, LinearEquiv.sumArrowLequivProdArrow,
          Equiv.sumArrowEquivProdArrow])
      (funext fun x => by
        simp [LinearMap.funLeft, Function.comp_def])

@[simp]
theorem stdSymplecticRepBlockSuccEquiv_apply (v : Fin (n + 1) ⊕ Fin (n + 1) → k) :
    stdSymplecticRepBlockSuccEquiv k n v =
      (fun x => v ((finSuccSumFinSuccEquiv n).symm (Sum.inl x)),
        fun x => v ((finSuccSumFinSuccEquiv n).symm (Sum.inr x))) :=
  (rfl)

@[simp]
theorem stdSymplecticRepBlockSuccEquiv_symm_apply (p : (Fin n ⊕ Fin n → k) × (Fin 1 ⊕ Fin 1 → k)) :
    (stdSymplecticRepBlockSuccEquiv k n).symm p = Sum.elim p.1 p.2 ∘ finSuccSumFinSuccEquiv n :=
  (rfl)

/-- **The branching splitting is orthogonal for the invariant form**: the symplectic pairing of two
vectors is the symplectic pairing of their images in the standard module of the smaller group plus
the symplectic pairing of their images in the last hyperbolic plane.  So the two summands are
orthogonal to each other, the trivial summand is the symplectic complement of the smaller standard
module, and the invariant form restricts to the standard symplectic forms of `k^{2n}` and of the
plane. -/
theorem stdSymplecticBilinForm_eq_stdSymplecticRepBlockSuccEquiv
    (v w : Fin (n + 1) ⊕ Fin (n + 1) → k) :
    stdSymplecticBilinForm k (n + 1) v w =
      stdSymplecticBilinForm k n (stdSymplecticRepBlockSuccEquiv k n v).1
          (stdSymplecticRepBlockSuccEquiv k n w).1 +
        stdSymplecticBilinForm k 1 (stdSymplecticRepBlockSuccEquiv k n v).2
          (stdSymplecticRepBlockSuccEquiv k n w).2 := by
  -- Coordinate transport: read through the splitting, the form has the block-diagonal matrix
  -- `fromBlocks J 0 0 J`.
  have htransport : ∀ p q : (Fin n ⊕ Fin n → k) × (Fin 1 ⊕ Fin 1 → k),
      stdSymplecticBilinForm k (n + 1) ((stdSymplecticRepBlockSuccEquiv k n).symm p)
          ((stdSymplecticRepBlockSuccEquiv k n).symm q) =
        Sum.elim p.1 p.2 ⬝ᵥ fromBlocks (J (Fin n) k) 0 0 (J (Fin 1) k) *ᵥ Sum.elim q.1 q.2 := by
    intro p q
    rw [stdSymplecticRepBlockSuccEquiv_symm_apply, stdSymplecticRepBlockSuccEquiv_symm_apply,
      stdSymplecticBilinForm_apply, ← fromBlocks_J_submatrix_finSuccSumFinSuccEquiv,
      submatrix_mulVec_equiv, comp_equiv_dotProduct_comp_equiv]
    simp [Function.comp_assoc]
  -- Block pairing: a block-diagonal form pairs the two summands separately.
  conv_lhs => rw [← (stdSymplecticRepBlockSuccEquiv k n).symm_apply_apply v,
    ← (stdSymplecticRepBlockSuccEquiv k n).symm_apply_apply w, htransport]
  simp [fromBlocks_mulVec, sumElim_dotProduct_sumElim, stdSymplecticBilinForm_apply]

/-- The standard representation of the symplectic group stays faithful after restriction along the
block inclusion. -/
theorem stdSymplecticRep_comp_symplecticBlockSucc_injective :
    Function.Injective ((stdSymplecticRep k (n + 1)).comp (symplecticBlockSucc n k)) :=
  (stdSymplecticRep_injective k (n + 1)).comp (symplecticBlockSucc_injective n k)

end CommRing

section Field

variable [Field k]

/-- The character of the restricted standard symplectic representation is the character of the
standard representation of the smaller symplectic group plus two, the dimension of the trivial
summand. -/
theorem char_stdSymplecticRep_symplecticBlockSucc (g : symplecticGroup (Fin n) k) :
    (stdSymplecticRep k (n + 1)).character (symplecticBlockSucc n k g) =
      (stdSymplecticRep k n).character g + 2 := by
  rw [char_stdSymplecticRep, char_stdSymplecticRep, coe_symplecticBlockSucc, trace_sumBlockSucc]

/-- The character identity for the bundled standard representation of the symplectic group. -/
theorem char_stdSymplecticFDRep_symplecticBlockSucc (g : symplecticGroup (Fin n) k) :
    (stdSymplecticFDRep k (n + 1)).character (symplecticBlockSucc n k g) =
      (stdSymplecticFDRep k n).character g + 2 := by
  rw [char_stdSymplecticFDRep, char_stdSymplecticFDRep, coe_symplecticBlockSucc,
    trace_sumBlockSucc]

end Field

end TauCeti
