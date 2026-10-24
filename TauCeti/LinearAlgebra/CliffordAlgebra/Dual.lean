/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.CliffordAlgebra.Conjugation
public import Mathlib.LinearAlgebra.Dual.Defs
import TauCeti.LinearAlgebra.CliffordAlgebra.VolumeElement

/-!
# The reverse-dual Clifford action

For an `R`-algebra `K`, a `K`-linear Clifford action `ρ` on `S` induces an action on
its `K`-linear dual by
`(a · φ)(s) = φ (ρ (CliffordAlgebra.reverse a) s)`. Reversal and transposition each reverse
multiplication, so their composite is again an algebra action. In particular, a vector acts
by the transpose of its original action. This is an algebraic dual, linear over the coefficient
ring; over the complex numbers it is distinct from conjugate-linear Hermitian adjunction.

The construction needs neither finite dimension nor a nondegenerate quadratic form. It is
contravariantly natural in intertwiners, and the canonical map to the double dual intertwines
the original action with its double reverse dual. For reflexive modules this is an equivalence.
On an orthogonal volume product of length `n`, the dual action is the transpose multiplied by
`(-1) ^ n.choose 2`; this fixes the sign needed when comparing dual chiralities.

The construction uses Mathlib's `LinearMap.dualMap` and `CliffordAlgebra.reverse`.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §5.
-/

public section

namespace TauCeti

open CliffordAlgebra Module

variable {R K V S T : Type*} [CommRing R] [CommRing K] [Algebra R K]
  [AddCommGroup V] [Module R V] {Q : QuadraticForm R V}
  [AddCommGroup S] [Module K S] [Module R S] [IsScalarTower R K S]
  [AddCommGroup T] [Module K T] [Module R T] [IsScalarTower R K T]

/-- The action on the scalar dual obtained by transposing the action after Clifford reversal.
No Hermitian conjugation of the coefficients is involved. -/
def cliffordReverseDual (ρ : CliffordAlgebra Q →ₐ[R] Module.End K S) :
    CliffordAlgebra Q →ₐ[R] Module.End K (Dual K S) where
  toFun a := (ρ (reverse a)).dualMap
  map_one' := by ext φ s; simp
  map_mul' a b := by ext φ s; simp [reverse.map_mul]
  map_zero' := by ext φ s; simp
  map_add' a b := by ext φ s; simp
  commutes' r := by ext φ s; simp

/-- The reverse-dual action is the transpose of the original action after reversal. -/
theorem cliffordReverseDual_apply (ρ : CliffordAlgebra Q →ₐ[R] Module.End K S)
    (a : CliffordAlgebra Q) :
    cliffordReverseDual ρ a = (ρ (reverse a)).dualMap :=
  (rfl)

/-- Evaluation characterizes the reverse-dual action. -/
@[simp]
theorem cliffordReverseDual_apply_apply (ρ : CliffordAlgebra Q →ₐ[R] Module.End K S)
    (a : CliffordAlgebra Q) (φ : Dual K S) (s : S) :
    cliffordReverseDual ρ a φ s = φ (ρ (reverse a) s) :=
  (rfl)

/-- Each vector acts on the reverse dual by the transpose of its action on the original module. -/
@[simp]
theorem cliffordReverseDual_ι (ρ : CliffordAlgebra Q →ₐ[R] Module.End K S) (v : V) :
    cliffordReverseDual ρ (ι Q v) = (ρ (ι Q v)).dualMap := by
  rw [cliffordReverseDual_apply, reverse_ι]

/-- The reverse-dual action is the unique Clifford algebra action with the prescribed
transposed vector action. -/
theorem cliffordReverseDual_unique (ρ : CliffordAlgebra Q →ₐ[R] Module.End K S)
    (σ : CliffordAlgebra Q →ₐ[R] Module.End K (Dual K S))
    (hσ : ∀ v, σ (ι Q v) = (ρ (ι Q v)).dualMap) :
    σ = cliffordReverseDual ρ := by
  apply CliffordAlgebra.hom_ext
  apply LinearMap.ext
  intro v
  exact (hσ v).trans (cliffordReverseDual_ι ρ v).symm

/-- Transposition sends a Clifford intertwiner to an intertwiner in the opposite direction. -/
theorem cliffordReverseDual_comp_dualMap
    (ρ : CliffordAlgebra Q →ₐ[R] Module.End K S)
    (σ : CliffordAlgebra Q →ₐ[R] Module.End K T) (f : S →ₗ[K] T)
    (hf : ∀ a, f ∘ₗ ρ a = σ a ∘ₗ f) (a : CliffordAlgebra Q) :
    cliffordReverseDual ρ a ∘ₗ f.dualMap = f.dualMap ∘ₗ cliffordReverseDual σ a := by
  ext φ s
  simp only [LinearMap.comp_apply, LinearMap.dualMap_apply, cliffordReverseDual_apply_apply]
  exact congrArg φ (LinearMap.congr_fun (hf (reverse a)) s)

/-- The canonical evaluation into the double dual is equivariant for double reverse duality. -/
theorem cliffordReverseDual_cliffordReverseDual_comp_eval
    (ρ : CliffordAlgebra Q →ₐ[R] Module.End K S) (a : CliffordAlgebra Q) :
    cliffordReverseDual (cliffordReverseDual ρ) a ∘ₗ Dual.eval K S =
      Dual.eval K S ∘ₗ ρ a := by
  ext s φ
  simp

/-- On a reflexive module, evaluation identifies the double reverse-dual action with the
original action. This includes finite-dimensional vector spaces and the zero module. -/
theorem cliffordReverseDual_cliffordReverseDual_eq_conj [Module.IsReflexive K S]
    (ρ : CliffordAlgebra Q →ₐ[R] Module.End K S) (a : CliffordAlgebra Q) :
    cliffordReverseDual (cliffordReverseDual ρ) a = (Module.evalEquiv K S).conj (ρ a) := by
  ext Φ φ
  obtain ⟨s, rfl⟩ := (Module.evalEquiv K S).surjective Φ
  rw [LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply]
  simp

/-- For an orthogonal volume product, reversal contributes the permutation sign. Scalar
normalizations, including complex ones, are transposed linearly. -/
theorem cliffordReverseDual_smul_prod_map_ι
    (ρ : CliffordAlgebra Q →ₐ[R] Module.End K S) {l : List V}
    (hl : l.Pairwise Q.IsOrtho) (r : R) :
    cliffordReverseDual ρ (r • (l.map (ι Q)).prod) =
      (r * (-1 : R) ^ l.length.choose 2) • (ρ (l.map (ι Q)).prod).dualMap := by
  ext φ s
  simp [reverse_prod_map_ι_of_pairwise_isOrtho hl, mul_smul]

end TauCeti
