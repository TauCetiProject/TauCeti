/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import TauCeti.AlgebraicGeometry.Cohomology.Module.Base
public import TauCeti.AlgebraicGeometry.Modules.Tensor.Product
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.ProjectiveOver
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.Basic
import TauCeti.AlgebraicGeometry.Cohomology.ClosedImmersion.Linear
import TauCeti.AlgebraicGeometry.Cohomology.ClosedImmersion.ProjectionFormula
import TauCeti.AlgebraicGeometry.Cohomology.ProjectiveSpace.Coherent
import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Pushforward.Finite
import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.LocalTriviality

/-!
# Serre's finiteness and vanishing theorems for projective schemes

Pushing forward along a closed immersion into `Proj (Sym_R M)` transfers the results of
`TauCeti.AlgebraicGeometry.Cohomology.ProjectiveSpace.Coherent` to projective schemes over a
Noetherian ring `R`:
* `AlgebraicGeometry.Scheme.IsProjectiveOver.finite_cohomology`: `H^q(X, F)` is finite over `R`.
* `Scheme.Hom.exists_forall_ge_subsingleton_cohomology_tensor_pullback_twistingSheaf`: for a
  closed immersion `i : X ⟶ Proj (Sym_R M)`, `H^q(X, F ⊗ i^* 𝒪(m)) = 0` for `m ≫ 0`, `q > 0`.

## References

* J.-P. Serre, *Faisceaux algébriques cohérents*, Ann. of Math. (2) **61** (1955), §66.
* A. Grothendieck, *EGA III₁*, Publ. Math. IHÉS **11** (1961), Theorem 2.2.1.
* R. Hartshorne, *Algebraic Geometry*, GTM 52, Springer, 1977, Theorem III.5.2.
* [The Stacks Project, Tag 02O6](https://stacks.math.columbia.edu/tag/02O6).
-/

public section

open CategoryTheory MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme.Modules

universe u

namespace AlgebraicGeometry.Scheme

open TauCeti.SymmetricAlgebra

/-- **Serre's finiteness theorem for projective schemes** (Hartshorne, Theorem III.5.2(a); Stacks
Tag 02O6, projective-over-`Spec R` case): if `X` is projective over a Noetherian ring `R`, then for
every quasi-coherent `𝒪_X`-module `F` of finite type and `q : ℕ`, `H^q(X, F)` is finite over `R`. -/
instance IsProjectiveOver.finite_cohomology (R : Type u) [CommRing R] [IsNoetherianRing R]
    {X : Scheme.{u}} [X.Over (Spec (.of R))] [X.IsProjectiveOver R]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] (q : ℕ) :
    Module.Finite R (Cohomology F q) := by
  obtain ⟨M, _, _, _, i, hi, hiR⟩ := IsProjectiveOver.exists_isClosedImmersion (R := R) (X := X)
  exact (i.moduleFinite_cohomology_pushforward_iff R F q).mp
    (TauCeti.SymmetricAlgebra.finite_cohomology_proj R M ((pushforward i).obj F) q)

/-- **Serre's vanishing theorem on closed subschemes of `Proj (Sym_R M)`** (Hartshorne, Theorem
III.5.2(b)): for a closed immersion `i : X ⟶ Proj (Sym_R M)` with `R` Noetherian and `M` finite
over `R`, and quasi-coherent `F` of finite type on `X`, some `m₀ : ℤ` gives
`H^q(X, F ⊗ i^* 𝒪(m)) = 0` for all `m ≥ m₀` and `q > 0`. -/
theorem Hom.exists_forall_ge_subsingleton_cohomology_tensor_pullback_twistingSheaf
    {R M : Type u} [CommRing R] [IsNoetherianRing R] [AddCommMonoid M] [Module R M]
    [Module.Finite R M] {X : Scheme.{u}} (i : X ⟶ Proj (homogeneousSubmodule R M))
    [IsClosedImmersion i] (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] :
    ∃ m₀ : ℤ, ∀ m ≥ m₀, ∀ q > 0,
      Subsingleton (Cohomology (F ⊗ (Scheme.Modules.pullback i).obj
        (Proj.twistingSheaf (homogeneousSubmodule R M) m :
          (Proj (homogeneousSubmodule R M)).Modules)) q) := by
  obtain ⟨m₀, hm₀⟩ :=
    TauCeti.SymmetricAlgebra.exists_forall_ge_subsingleton_cohomology_tensor_twistingSheaf R M
      ((pushforward i).obj F)
  exact ⟨m₀, fun m hm q hq ↦
    (i.subsingleton_cohomology_pushforward_tensor_iff_of_isInvertible F _ q).mp (hm₀ m hm q hq)⟩

end AlgebraicGeometry.Scheme
