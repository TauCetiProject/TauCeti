/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Cohomology.Flasque
public import TauCeti.AlgebraicGeometry.Modules.Skyscraper
public import TauCeti.AlgebraicGeometry.ResidueDegree

/-!
# Cohomology of skyscraper sheaves of residue fields

For a point `x` of a scheme `X` over a field `k`, the zeroth cohomology of the skyscraper sheaf
`κ(x)ₓ` is its residue field `κ(x)`. Its dimension over `k` is therefore the residue degree
`[κ(x) : k]`. Since `κ(x)ₓ` is flasque, its higher cohomology vanishes. Consequently all of its
cohomology is finite-dimensional when `κ(x)` is finite over `k`.

## Main declarations

* `Scheme.finrank_cohomology_zero_skyscraperResidueField`: the dimension of
  `H⁰(X, κ(x)ₓ)` is the residue degree `[κ(x) : k]`;
* `Scheme.finiteDimensional_cohomology_skyscraperResidueField`: if the residue degree is
  nonzero, the cohomology of `κ(x)ₓ` is finite-dimensional in every degree.
-/

public section

open CategoryTheory AlgebraicGeometry

namespace TauCeti

namespace AlgebraicGeometry

universe u

noncomputable section

open Scheme

variable {X : Scheme.{u}}

section Base

variable (k : Type u) [Field k] [X.Over (Spec (.of k))]

/-- **The dimension of the global sections of a skyscraper sheaf.** Over a field `k`, the zeroth
cohomology `H⁰(X, κ(x)ₓ) = κ(x)` has dimension the residue degree `[κ(x) : k]` of the structure
morphism at `x` (which is `0` by convention when `κ(x)` is infinite over `k`). -/
@[simp]
theorem _root_.AlgebraicGeometry.Scheme.finrank_cohomology_zero_skyscraperResidueField (x : X) :
    Module.finrank k (Scheme.Modules.Cohomology (skyscraperResidueField x) 0) =
      (X ↘ Spec (.of k)).residueDegree x := by
  let f := X ↘ Spec (.of k)
  let : Algebra ((Spec (.of k)).residueField (f x)) (X.residueField x) :=
    (f.residueFieldMap x).hom.toAlgebra
  rw [(Scheme.Modules.cohomologyZeroBaseLinearEquiv k X _).finrank_eq, Scheme.Hom.residueDegree,
    Module.finrank, Module.finrank]
  congr 1
  have hx : x ∈ (⊤ : X.Opens) := trivial
  refine rank_eq_of_equiv_equiv _ (skyscraperResidueFieldEquiv x hx)
    (Γevaluation_comp_ΓSpecIso_inv_bijective k (f x)) fun c s ↦ ?_
  rw [Scheme.Modules.base_smul_globalSections, skyscraperResidueFieldEquiv_smul,
    Algebra.smul_def, RingHom.algebraMap_toAlgebra, Function.comp_apply,
    Scheme.Γevaluation_naturality_apply, Scheme.Modules.baseRingToGlobalSections_apply]

/-- At a point whose residue field is finite over `k`, the skyscraper sheaf `κ(x)ₓ` has
finite-dimensional cohomology in every degree: `κ(x)` in degree zero and `0` above. -/
theorem _root_.AlgebraicGeometry.Scheme.finiteDimensional_cohomology_skyscraperResidueField {x : X}
    (hx : (X ↘ Spec (.of k)).residueDegree x ≠ 0) (i : ℕ) :
    FiniteDimensional k (Scheme.Modules.Cohomology (skyscraperResidueField x) i) := by
  cases i with
  | zero =>
    refine Module.finite_of_finrank_pos ?_
    rw [finrank_cohomology_zero_skyscraperResidueField]
    exact Nat.pos_of_ne_zero hx
  | succ i => infer_instance

end Base

end

end AlgebraicGeometry

end TauCeti
