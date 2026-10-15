/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Cohomology.MayerVietoris
public import TauCeti.AlgebraicGeometry.Cohomology.LongExactSequence
public import TauCeti.AlgebraicGeometry.Curves.AffineCover
public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Kernels

/-!
# Vanishing of quasi-coherent cohomology above degree one on a curve

Let `X` be a proper integral curve over a field `k` whose codimension-one local rings are
discrete valuation rings, for instance a smooth proper connected curve. Then `X` is covered by
two affine opens `U` and `V` (`AlgebraicGeometry.Scheme.exists_two_affine_opens`), their
intersection is affine because `X` is separated, and quasi-coherent sheaves on the Noetherian
affine schemes `U`, `V` and `U ∩ V` have no higher cohomology. The Mayer–Vietoris sequence of
the cover then shows that every quasi-coherent sheaf `M` on `X` has `Hⁿ(X, M) = 0` for all
`n ≥ 2`: cohomology vanishes above the dimension of the curve.

Through the long exact cohomology sequence, this vanishing makes `H¹(X, -)` right exact on
quasi-coherent sheaves. For a short exact sequence `0 ⟶ M₁ ⟶ M₂ ⟶ M₃ ⟶ 0` of sheaves of modules
with `M₁` quasi-coherent, the map `H¹(X, M₂) ⟶ H¹(X, M₃)` is surjective; in particular an
epimorphism of quasi-coherent sheaves is surjective on `H¹`, and a quotient of a quasi-coherent
sheaf with finite-dimensional `H¹` again has finite-dimensional `H¹`. The vanishing of `H²` is also
the hypothesis under which `Scheme.Modules.finrank_cohomology_zero_sub_one_eq_add` makes the Euler
characteristic `χ(X, M) = dim H⁰(X, M) - dim H¹(X, M)` additive on a short exact sequence whose
first term is quasi-coherent.

Neither a rational point nor a perfect base field is assumed.

## Main results

* `AlgebraicGeometry.Scheme.Modules.subsingleton_cohomology_of_two_le_of_isCurveOver`:
  `Hⁿ(X, M) = 0` for `n ≥ 2` and `M` quasi-coherent on a regular proper curve;
* `AlgebraicGeometry.Scheme.Modules.subsingleton_cohomology_of_two_le_of_smooth`: the same on a
  smooth proper connected curve of relative dimension one;
* `AlgebraicGeometry.Scheme.Modules.cohomologyMap_one_surjective_of_isCurveOver` and
  `AlgebraicGeometry.Scheme.Modules.cohomologyMap_one_surjective_of_epi_of_isCurveOver`:
  right exactness of `H¹` on such a curve;
* `AlgebraicGeometry.Scheme.Modules.finiteDimensional_cohomology_one_of_epi_of_isCurveOver`:
  finite-dimensionality of `H¹` passes to quotients.

## References

* R. Hartshorne, *Algebraic Geometry*, Chapter III, Theorem 2.7 (Grothendieck vanishing) and
  Theorem 4.5 (Čech computation of quasi-coherent cohomology on a separated Noetherian scheme).
-/

public section

open CategoryTheory Limits AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

open TauCeti TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme.Modules

universe u

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]

/-- A proper scheme over a field which is covered by two affine opens has no quasi-coherent
cohomology in degrees at least two. -/
private theorem subsingleton_cohomology_of_two_le_of_isProper [IsProper (X ↘ Spec (.of k))]
    (hcover : ∃ U V : X.Opens, IsAffineOpen U ∧ IsAffineOpen V ∧ U ⊔ V = ⊤) (M : X.Modules)
    [M.IsQuasicoherent] (n : ℕ) (hn : 2 ≤ n) : Subsingleton (Cohomology M n) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  have : IsSeparated (terminal.from X) := by
    rw [← terminal.comp_from (X ↘ Spec (.of k))]
    infer_instance
  obtain ⟨U, V, hU, hV, hUV⟩ := hcover
  exact subsingleton_cohomology_of_two_le_of_isAffineOpen_of_isAffineHom M hU hV hUV n hn

section IsCurveOver

variable (k) [X.IsCurveOver k]
  [∀ y : CodimensionOnePoint X, IsDiscreteValuationRing (X.presheaf.stalk (y : X))]

include k

/-- **Vanishing above the dimension of a curve.** On a proper integral curve over a field whose
codimension-one local rings are discrete valuation rings, a quasi-coherent sheaf of modules has
no cohomology in degrees at least two. -/
theorem subsingleton_cohomology_of_two_le_of_isCurveOver (M : X.Modules) [M.IsQuasicoherent]
    (n : ℕ) (hn : 2 ≤ n) : Subsingleton (Cohomology M n) :=
  subsingleton_cohomology_of_two_le_of_isProper (k := k) (X.exists_two_affine_opens (k := k)) M
    n hn

/-- On a proper integral curve over a field whose codimension-one local rings are discrete
valuation rings, `H¹` is right exact: for a short exact sequence `0 ⟶ M₁ ⟶ M₂ ⟶ M₃ ⟶ 0` of
sheaves of modules with `M₁` quasi-coherent, `H¹(X, M₂) ⟶ H¹(X, M₃)` is surjective. -/
theorem cohomologyMap_one_surjective_of_isCurveOver {S : ShortComplex X.Modules}
    (hS : S.ShortExact) [S.X₁.IsQuasicoherent] :
    Function.Surjective (cohomologyMap S.g 1) :=
  cohomologyMap_surjective hS 1 2 rfl
    (subsingleton_cohomology_of_two_le_of_isCurveOver k S.X₁ 2 le_rfl)

/-- On a proper integral curve over a field whose codimension-one local rings are discrete
valuation rings, an epimorphism of quasi-coherent sheaves of modules is surjective on `H¹`. -/
theorem cohomologyMap_one_surjective_of_epi_of_isCurveOver {M N : X.Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent] (f : M ⟶ N) [Epi f] :
    Function.Surjective (cohomologyMap f 1) := by
  have : (ShortComplex.kernelSequence f).X₁.IsQuasicoherent := isQuasicoherent_kernel f
  have : Epi (ShortComplex.kernelSequence f).g := ‹Epi f›
  exact cohomologyMap_one_surjective_of_isCurveOver k
    (.mk' (ShortComplex.kernelSequence_exact f) inferInstance inferInstance)

/-- On a proper integral curve over a field whose codimension-one local rings are discrete
valuation rings, a quotient of a quasi-coherent sheaf of modules with finite-dimensional `H¹`
again has finite-dimensional `H¹`. -/
theorem finiteDimensional_cohomology_one_of_epi_of_isCurveOver {M N : X.Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent] (f : M ⟶ N) [Epi f]
    [FiniteDimensional k (Cohomology M 1)] : FiniteDimensional k (Cohomology N 1) := by
  refine Module.Finite.of_surjective (cohomologyMapBaseLinear k X f 1) fun y ↦ ?_
  obtain ⟨x, hx⟩ := cohomologyMap_one_surjective_of_epi_of_isCurveOver k f y
  refine ⟨x, ?_⟩
  rw [cohomologyMapBaseLinear_apply, cohomologyFunctor_map]
  exact hx

end IsCurveOver

variable (k) in
/-- **Vanishing above the dimension of a smooth curve.** On a smooth proper connected curve of
relative dimension one over any field, a quasi-coherent sheaf of modules has no cohomology in
degrees at least two. -/
theorem subsingleton_cohomology_of_two_le_of_smooth [IsProper (X ↘ Spec (.of k))]
    [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))] [ConnectedSpace X] (M : X.Modules)
    [M.IsQuasicoherent] (n : ℕ) (hn : 2 ≤ n) : Subsingleton (Cohomology M n) :=
  subsingleton_cohomology_of_two_le_of_isProper (k := k)
    (X.exists_two_affine_opens_of_smooth (k := k)) M n hn

end AlgebraicGeometry.Scheme.Modules
