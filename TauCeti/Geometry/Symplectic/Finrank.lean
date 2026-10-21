/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.Parity
public import TauCeti.Geometry.Symplectic.Complex.Module.Basic
public import TauCeti.LinearAlgebra.Complex.Finrank
public import TauCeti.LinearAlgebra.Eigenspace.Anticommute
public import TauCeti.LinearAlgebra.TotallyReal.Finrank

/-!
# An almost complex structure forces even real dimension

A pointwise almost complex structure `J` on a real module `V` turns `V` into a complex vector
space (`TauCeti.AlmostComplexStructure.complexModule`), where multiplication by `i` is `J`. Since
`ℂ` is a degree-two extension of `ℝ`, the tower law forces the real dimension of `V` to be twice
its complex dimension, hence even. This is the classical fact that a manifold (or vector bundle)
admitting an almost complex structure is even-dimensional (McDuff--Salamon, *J-holomorphic Curves
and Symplectic Topology*, Section 2.1), recorded here at the pointwise linear-algebra level.

The tower-law identities are stated without a finite-dimensionality hypothesis:
`Module.finrank_mul_finrank` holds for `Module.finrank` unconditionally (an infinite-dimensional
`V` has `Module.finrank ℝ V = 0 = 2 * 0`), so the identities below need no `FiniteDimensional`
assumption.

## Main declarations

* `TauCeti.AlmostComplexStructure.complexFinrank`: the `ℂ`-dimension of `V` under the complex
  module structure induced by `J`.
* `TauCeti.AlmostComplexStructure.complexFinrank_def`: `complexFinrank` is `Module.finrank ℂ V`
  under the induced complex structure.
* `TauCeti.AlmostComplexStructure.finrank_real_eq_two_mul_complexFinrank`: the real dimension is
  twice the complex dimension, `finrank ℝ V = 2 * J.complexFinrank`.
* `TauCeti.AlmostComplexStructure.even_finrank_real`: the real dimension of a module carrying an
  almost complex structure is even.
* `TauCeti.AlmostComplexStructure.even_finrank_of_forall_mem`: a `J`-invariant subspace has even
  real dimension.
* `TauCeti.AlmostComplexStructure.even_finrank_genEigenspace_zero_of_anticommute`: the generalized
  `0`-eigenspaces of an endomorphism anticommuting with `J` have even real dimension.
* `TauCeti.AlmostComplexStructure.isEmpty_of_odd_finrank`: an odd-dimensional real module admits no
  almost complex structure.
* `TauCeti.AlmostComplexStructure.finrank_eq_complexFinrank_of_isMaximalTotallyReal`: a maximal
  totally real subspace has real dimension equal to the complex dimension of the ambient space.
  This is the statement that the totally real tori `T_α`, `T_β` in the symmetric product
  `Sym^g(Σ)` of a Heegaard surface are `g`-dimensional.

The conventions follow McDuff--Salamon, *J-holomorphic Curves and Symplectic Topology*,
Section 2.1.
-/

public section

namespace TauCeti

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

namespace AlmostComplexStructure

/-- The complex dimension of `V` with respect to an almost complex structure `J`: the
`ℂ`-dimension of `V` under the complex module structure induced by `J`
(`AlmostComplexStructure.complexModule`). -/
@[expose] noncomputable def complexFinrank (J : AlmostComplexStructure V) : ℕ :=
  letI := J.complexModule
  Module.finrank ℂ V

/-- The complex dimension of `J` is the `ℂ`-dimension of `V` under the induced complex structure. -/
@[simp]
lemma complexFinrank_def (J : AlmostComplexStructure V) :
    letI := J.complexModule
    J.complexFinrank = Module.finrank ℂ V :=
  rfl

/-- The real dimension of a module carrying an almost complex structure `J` is twice its complex
dimension: `finrank ℝ V = 2 * J.complexFinrank`. This is the tower law `finrank ℝ V =
finrank ℝ ℂ * finrank ℂ V` together with `finrank ℝ ℂ = 2`. -/
theorem finrank_real_eq_two_mul_complexFinrank (J : AlmostComplexStructure V) :
    Module.finrank ℝ V = 2 * J.complexFinrank := by
  let := J.complexModule
  let := J.complexModule_isScalarTower
  rw [J.complexFinrank_def]
  exact finrank_real_eq_two_mul_finrank_complex

/-- The real dimension of a module carrying an almost complex structure is even. -/
theorem even_finrank_real (J : AlmostComplexStructure V) :
    Even (Module.finrank ℝ V) := by
  rw [J.finrank_real_eq_two_mul_complexFinrank]
  exact even_two_mul _

/-- A real subspace invariant under an almost complex structure has even real dimension: `J`
restricts to an almost complex structure on it. -/
theorem even_finrank_of_forall_mem (J : AlmostComplexStructure V) {p : Submodule ℝ V}
    (hp : ∀ v ∈ p, J v ∈ p) : Even (Module.finrank ℝ p) :=
  even_finrank_real
    { toLinearMap := J.toLinearMap.restrict hp
      square_neg := by ext v; simp }

/-- If an endomorphism `f` anticommutes with an almost complex structure `J`, then its
generalized `0`-eigenspaces, in particular its kernel, are `J`-invariant and therefore have even
real dimension. -/
theorem even_finrank_genEigenspace_zero_of_anticommute (J : AlmostComplexStructure V)
    {f : Module.End ℝ V} (h : f * J.toLinearMap + J.toLinearMap * f = 0) (k : ℕ∞) :
    Even (Module.finrank ℝ (f.genEigenspace 0 k)) :=
  J.even_finrank_of_forall_mem fun _ hv ↦ by
    simpa using Module.End.mapsTo_genEigenspace_neg_of_anticommute h 0 k hv

/-- A maximal totally real subspace `L` of a finite-dimensional almost complex module has real
dimension equal to the complex dimension of the ambient module: `L` is "half-dimensional".

For a Heegaard diagram of genus `g`, this is the statement that the totally real tori `T_α`,
`T_β` are `g`-dimensional inside the `g`-complex-dimensional symmetric product `Sym^g(Σ)`
(Ozsváth--Szabó, [arXiv:math/0101206](https://arxiv.org/abs/math/0101206), Section 2). -/
theorem finrank_eq_complexFinrank_of_isMaximalTotallyReal [FiniteDimensional ℝ V]
    {J : AlmostComplexStructure V} {L : Submodule ℝ V}
    (hL : IsMaximalTotallyReal J.toLinearMap L) :
    Module.finrank ℝ L = J.complexFinrank := by
  have h := hL.two_mul_finrank_eq (J.injective.comp L.subtype_injective)
  have h' := J.finrank_real_eq_two_mul_complexFinrank
  omega

/-- An odd-dimensional real module admits no almost complex structure. -/
theorem isEmpty_of_odd_finrank (h : Odd (Module.finrank ℝ V)) :
    IsEmpty (AlmostComplexStructure V) :=
  ⟨fun J => (Nat.not_odd_iff_even.mpr J.even_finrank_real) h⟩

end AlmostComplexStructure

end TauCeti
