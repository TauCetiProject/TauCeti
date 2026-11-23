/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import TauCeti.GroupTheory.Coxeter.Bipartite
public import TauCeti.LinearAlgebra.RootSystem.Chamber
public import TauCeti.LinearAlgebra.RootSystem.Coxeter.Bipartite
public import TauCeti.LinearAlgebra.RootSystem.Coxeter.Presentation
import Mathlib.LinearAlgebra.Complex.Module
import TauCeti.LinearAlgebra.RootSystem.Coxeter.Element.Plane

/-!
# A regular eigenvector of the bipartite Coxeter element

Let `b` be a base of a finite irreducible reduced crystallographic root system, and colour its
Dynkin diagram, which is a tree, by `Bool`. The bipartite Coxeter element `c` is the product of
the simple reflections of colour `true`, followed by those of colour `false`. Over a
field `K` containing `ℝ` and algebraically closed, such as `ℂ`, this file proves Steinberg's
theorem that `c` has a **regular eigenvector**, lying on no reflecting hyperplane, whose
eigenvalue is a primitive root of unity of order exactly the order `h` of `c`
(`RootPairing.exists_isRegularWeight_bipartiteCoxeterElement_smul_eq_smul_isPrimitiveRoot`).

This is the geometric input of the uniform identification of the eigenvalues of a Coxeter element
with `ζ ^ (dᵢ - 1)` for the invariant degrees `dᵢ`: at a regular eigenvector, the invariant
degrees compute the characteristic polynomial.

## The argument

By `RootPairing.Base.exists_eigenvector_exp_two_pi_I_div_orderOf_wordProd`, the integer matrix
of `c` in the simple-root basis already has a complex regular primitive `h`-th-root eigenvector
`v : b.support → ℂ` (constructed via Coleman's real Coxeter plane in rank ≥ 2, and `-1` on the
unique simple root in rank 1). Since `K` is an algebraically closed `ℝ`-algebra, choosing
`i : K` with `i * i = -1` gives an embedding `φ : ℂ →+* K` via `Complex.liftAux`, and
`∑ j, φ (v j) • P.root j` is the desired regular eigenvector in `M`.

## Main results

* `RootPairing.exists_isRegularWeight_bipartiteCoxeterElement_smul_eq_smul_isPrimitiveRoot`: the
  bipartite Coxeter element has a regular eigenvector whose eigenvalue is a primitive root of
  unity of order equal to the order of the element.

## References

* R. Steinberg, *Finite reflection groups*, Trans. Amer. Math. Soc. **91** (1959), 493–504.
* J. E. Humphreys, *Reflection Groups and Coxeter Groups*, Cambridge University Press (1990),
  §§3.16–3.19.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4–6*, Ch. V, §6, no. 2.
-/

public section

open TauCeti

namespace RootPairing

/-- **Steinberg's regular eigenvector of the bipartite Coxeter element.** Let `b` be a base of a
finite irreducible reduced crystallographic root system over a field `K` which contains `ℝ` and is
algebraically closed, such as `ℂ`. For every colouring of its Dynkin diagram by `Bool`, the
bipartite Coxeter element `c` has a regular eigenvector, one on which no coroot vanishes, whose
eigenvalue is a primitive root of unity of order exactly the order of `c`. -/
theorem exists_isRegularWeight_bipartiteCoxeterElement_smul_eq_smul_isPrimitiveRoot
    {ι K M N : Type*} [Field K] [CharZero K] [Algebra ℝ K] [IsAlgClosed K]
    [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
    (P : RootPairing ι K M N) (b : P.Base) [Finite ι] [Nonempty ι]
    [P.IsCrystallographic] [P.IsReduced] [P.IsIrreducible]
    (c : (coxeterMatrixOfBase P b).graph.Coloring Bool) :
    ∃ (x : M) (μ : K), P.IsRegularWeight x ∧
      (weylCoxeterSystem P b).bipartiteCoxeterElement c • x = μ • x ∧
      IsPrimitiveRoot μ (orderOf ((weylCoxeterSystem P b).bipartiteCoxeterElement c)) := by
  classical
  obtain ⟨i, hi⟩ := IsAlgClosed.exists_pow_nat_eq (-1 : K) two_pos
  let φ : ℂ →+* K := (Complex.liftAux i (sq i ▸ hi)).toRingHom
  obtain ⟨l₁, l₂, -, -, hnd, hall, hw⟩ :=
    (weylCoxeterSystem P b).exists_wordProd_eq_bipartiteCoxeterElement c
  rw [weylCoxeterSystem_wordProd] at hw
  obtain ⟨v, -, hv_eig, hprim, hv_reg, -⟩ :=
    b.exists_eigenvector_exp_two_pi_I_div_orderOf_wordProd hnd hall
      (hw ▸ b.actsBy_bipartiteCoxeterElement c)
  let x : M := ∑ j : b.support, φ (v j) • P.root j
  let μ : K := φ (Complex.exp (2 * Real.pi * Complex.I / orderOf (wordProd P b (l₁ ++ l₂))))
  refine ⟨x, μ, (P.isRegularWeight_iff x).mpr fun j ↦ ?_, ?_,
    hw ▸ hprim.map_of_injective φ.injective⟩
  · rw [b.coroot'_sum_map_smul_root φ j v]
    exact (map_ne_zero φ).mpr (hv_reg j)
  · rw [(b.actsBy_bipartiteCoxeterElement c).smul_sum_map_smul_root φ v, hv_eig, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [Pi.smul_apply, smul_eq_mul, map_mul, smul_smul]

end RootPairing
