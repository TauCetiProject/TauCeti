/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.ExteriorAlgebra.ReversalPairing
public import TauCeti.RepresentationTheory.InvariantForm
public import TauCeti.RepresentationTheory.Spin.Representation
import TauCeti.LinearAlgebra.ExteriorAlgebra.Contraction

/-!
# The reversal pairing on the spinor module

Let `P` be a polarization `V = W ⊕ W' ⊕ L` of a quadratic space and `S = ⋀ W` its Fock model.
For a functional `φ` on `S`, `ExteriorAlgebra.reversalPairing φ` is the bilinear form
`⟨s, t⟩ = φ (reverse s * t)`. When `φ` kills every contraction, and is moreover invariant under
the grade involution if the remainder `L` is nonzero, every vector of `V` acts on `S` by a
self-adjoint operator: creation by exterior multiplication, annihilation by contraction, and the
remainder by a multiple of the grade involution. Hence a Clifford element `x` is adjoint to its
reverse (`TauCeti.reversalPairing_spinAction`), and since `reverse g * g = 1` for `g` in the Spin
group, the pairing is invariant under the spin representation
(`TauCeti.reversalPairing_spinRep`).

For a basis of `W` indexed by a finite linear order, the top-degree coefficient kills every
contraction, and is involution-invariant whenever the rank is even, so its reversal pairing
`⟨s, t⟩ = [reverse s ∧ t]_top` is Spin-invariant whenever `L = 0` or `dim W` is even
(`TauCeti.reversalPairing_coord_univ_spinRep`); that is, it is an invariant form of the spin
representation (`TauCeti.isInvariantForm_reversalPairing_coord_univ`).

In dimension five `dim W = 2`, and this pairing is a symplectic form on the four-dimensional
spin representation of `Spin₅`: it is Spin-invariant by
`TauCeti.reversalPairing_coord_univ_spinRep`, alternating by
`ExteriorAlgebra.isAlt_reversalPairing_coord_univ`, since reversal acts on `⋀² W` by `-1`,
and nondegenerate by `ExteriorAlgebra.reversalPairing_nondegenerate`.

## References

* C. Chevalley, *The Algebraic Theory of Spinors* (1954), Chapter III.
* W. Fulton and J. Harris, *Representation Theory: A First Course*, Lecture 20, §20.1.
-/

public section

open CliffordAlgebra Module

namespace TauCeti

universe u v w

variable {K : Type u} [CommRing K] {V : Type v} [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V} (P : SpinPolarizationData Q)
  (φ : Module.Dual K (ExteriorAlgebra K P.W))

/-- **Vectors act self-adjointly for the reversal pairing** of a functional killing every
contraction and, unless the remainder of the polarization is zero, invariant under the grade
involution. -/
theorem reversalPairing_spinAction_ι
    (hφ : ∀ (d : Module.Dual K P.W) (x : ExteriorAlgebra K P.W), φ (contractLeft d x) = 0)
    (hline : P.line = ⊥ ∨ ∀ x : ExteriorAlgebra K P.W, φ (involute x) = φ x)
    (v : V) (s t : ExteriorAlgebra K P.W) :
    ExteriorAlgebra.reversalPairing φ (spinAction Q P (ι Q v) s) t =
      ExteriorAlgebra.reversalPairing φ s (spinAction Q P (ι Q v) t) := by
  obtain ⟨⟨⟨x, y⟩, z⟩, rfl⟩ := P.decompositionEquiv.surjective v
  have hz : ExteriorAlgebra.reversalPairing φ (P.lineCoordinate z • involute s) t =
      ExteriorAlgebra.reversalPairing φ s (P.lineCoordinate z • involute t) := by
    rcases hline with hline | hinv
    · have hz0 : z = 0 := Subtype.ext (by simpa [hline] using z.property)
      simp [hz0]
    · rw [map_smul, map_smul, LinearMap.smul_apply,
        ExteriorAlgebra.reversalPairing_involute φ hinv]
  simp only [P.decompositionEquiv_apply, map_add, LinearMap.add_apply, spinAction_ι_wedge,
    spinAction_ι_contract, spinAction_ι_lineOperator, ExteriorAlgebra.reversalPairing_ι_mul,
    fun d ↦ ExteriorAlgebra.reversalPairing_contractLeft φ d (hφ d), hz]

/-- **A Clifford element is adjoint to its reverse** for the reversal pairing of a functional
killing every contraction and, unless the remainder of the polarization is zero, invariant under
the grade involution. -/
theorem reversalPairing_spinAction
    (hφ : ∀ (d : Module.Dual K P.W) (x : ExteriorAlgebra K P.W), φ (contractLeft d x) = 0)
    (hline : P.line = ⊥ ∨ ∀ x : ExteriorAlgebra K P.W, φ (involute x) = φ x)
    (x : CliffordAlgebra Q) (s t : ExteriorAlgebra K P.W) :
    ExteriorAlgebra.reversalPairing φ (spinAction Q P x s) t =
      ExteriorAlgebra.reversalPairing φ s (spinAction Q P (reverse x) t) := by
  induction x using CliffordAlgebra.induction generalizing s t with
  | algebraMap r => simp [reverse.commutes]
  | ι v => rw [reverse_ι, reversalPairing_spinAction_ι P φ hφ hline]
  | mul a b ha hb =>
    rw [map_mul, mul_apply_eq_comp, ha, hb, reverse.map_mul, map_mul, mul_apply_eq_comp]
  | add a b ha hb => simp only [map_add, LinearMap.add_apply, ha, hb]

/-- **The reversal pairing is Spin-invariant**, for a functional killing every contraction and,
unless the remainder of the polarization is zero, invariant under the grade involution: a Spin
element `g` is even, so its reverse is its Clifford conjugate and `reverse g * g = 1`. -/
theorem reversalPairing_spinRep
    (hφ : ∀ (d : Module.Dual K P.W) (x : ExteriorAlgebra K P.W), φ (contractLeft d x) = 0)
    (hline : P.line = ⊥ ∨ ∀ x : ExteriorAlgebra K P.W, φ (involute x) = φ x)
    (g : spinGroup Q) (s t : ExteriorAlgebra K P.W) :
    ExteriorAlgebra.reversalPairing φ (spinRep Q P g s) (spinRep Q P g t) =
      ExteriorAlgebra.reversalPairing φ s t := by
  have hg : reverse (g : CliffordAlgebra Q) * g = 1 := by
    simpa only [star_def, spinGroup.involute_eq g.property] using spinGroup.star_mul_self_of_mem
        g.property
  rw [spinRep_apply, reversalPairing_spinAction P φ hφ hline, ← mul_apply_eq_comp,
    ← map_mul, hg, map_one, one_apply_eq_self]

/-- **The top-degree reversal pairing `[reverse s ∧ t]_top` is Spin-invariant** for a basis of the
isotropic summand `W`, when the remainder of the polarization is zero or `W` has even rank. In
dimension five, where `W` has rank two, it is the invariant symplectic form of the four-dimensional
spin representation. -/
theorem reversalPairing_coord_univ_spinRep {I : Type w} [LinearOrder I] [Fintype I]
    (b : Module.Basis I K P.W) (hline : P.line = ⊥ ∨ Even (Fintype.card I))
    (g : spinGroup Q) (s t : ExteriorAlgebra K P.W) :
    ExteriorAlgebra.reversalPairing (b.ExteriorAlgebra.coord Finset.univ)
        (spinRep Q P g s) (spinRep Q P g t) =
      ExteriorAlgebra.reversalPairing (b.ExteriorAlgebra.coord Finset.univ) s t :=
  reversalPairing_spinRep P _ b.exteriorAlgebra_coord_univ_contractLeft
    (hline.imp_right fun h x ↦ by
      rw [b.exteriorAlgebra_coord_univ_involute, h.neg_one_pow, one_mul]) g s t

/-- **The top-degree reversal pairing is an invariant form** of the spin representation, for a
basis of the isotropic summand `W`, when the remainder of the polarization is zero or `W` has even
rank. -/
theorem isInvariantForm_reversalPairing_coord_univ {I : Type w} [LinearOrder I] [Fintype I]
    (b : Module.Basis I K P.W) (hline : P.line = ⊥ ∨ Even (Fintype.card I)) :
    Representation.IsInvariantForm (spinRep Q P)
      (ExteriorAlgebra.reversalPairing (b.ExteriorAlgebra.coord Finset.univ)) :=
  Representation.isInvariantForm_iff.mpr (reversalPairing_coord_univ_spinRep P b hline)

end TauCeti
