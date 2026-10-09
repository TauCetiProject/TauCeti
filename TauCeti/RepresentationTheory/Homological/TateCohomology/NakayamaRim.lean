/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.TateCohomology.Projective
import TauCeti.Algebra.Module.Projective.Schanuel
import TauCeti.LinearAlgebra.FreeModule.PID
import TauCeti.RepresentationTheory.Homological.TateCohomology.HomologySequence

/-!
# Cohomologically trivial representations have projective dimension at most one

Let `G` be a finite group and `k` a principal ideal domain of characteristic zero in which every
prime number is a unit or generates a maximal ideal, such as `ℤ`, `ℤ_[p]`, `ℤ_(p)` or a field of
characteristic zero. If a representation `A` of `G` over `k` is cohomologically trivial, that is,
its Tate cohomology vanishes in every degree on every subgroup of `G`, then the kernel of every
surjection onto `A` from a projective `k[G]`-module is projective (Rim, Ann. of Math. 69 (1959);
Brown, *Cohomology of Groups*, VI §8). Every module is a quotient of a free one, so every
cohomologically trivial `A` has a projective resolution of length one, with no finiteness
hypothesis on `A`. In the other direction, projective representations are cohomologically trivial
(`Rep.isZero_res_of_projective`).

For the free `k[G]`-module `F` on the elements of `A`, the kernel `R` of `F ↠ A` is a
`k`-submodule of the free `k`-module `F`, hence free over `k`
(`Submodule.free_of_isPrincipalIdealRing`). It is cohomologically trivial by the long exact
sequence, since `F` and `A` are, so it is projective by the lattice form of the theorem,
`Rep.projective_of_isZero_res`. By Schanuel's lemma
(`LinearMap.projective_ker_of_projective_ker`) the kernel of any other surjection onto `A` from a
projective module, in any universe, is then projective too.

## Main statements

* `Rep.projective_ker_of_isZero_res`: if `A` is cohomologically trivial, every
  surjection onto `A.ρ.asModule` from a projective `k[G]`-module has projective kernel.

## References

* D. S. Rim, *Modules over finite groups*, Ann. of Math. 69 (1959).
* K. S. Brown, *Cohomology of Groups*, Chapter VI, §8.
* J.-P. Serre, *Local Fields*, Chapter IX, §§3–5.
-/

public section

universe u

open CategoryTheory Limits TauCeti.TateCohomology

namespace Rep

variable {k G : Type u} [CommRing k] [Group G] [Finite G]
  [IsDomain k] [IsPrincipalIdealRing k] [CharZero k]

/-- The theorem for the free cover `F ↠ A` of `A` by the free `k[G]`-module on its elements. -/
private theorem projective_ker_linearCombination
    (hk : ∀ p : ℕ, p.Prime → IsUnit (p : k) ∨ (Ideal.span {(p : k)}).IsMaximal)
    (A : Rep k G)
    (hA : ∀ (S : Subgroup G) [Fintype S] (n : ℤ),
      IsZero (tateCohomology (res S.subtype A) n)) :
    Module.Projective (MonoidAlgebra k G)
      (LinearMap.ker (Finsupp.linearCombination (MonoidAlgebra k G) (id : A.ρ.asModule → _))) := by
  set g := Finsupp.linearCombination (MonoidAlgebra k G) (id : A.ρ.asModule → _)
  have hg : Function.Surjective g := Finsupp.linearCombination_surjective _ Function.surjective_id
  -- The short exact sequence `0 ⟶ ker g ⟶ F ⟶ A ⟶ 0`, transported to representations. Its terms
  -- are `ofModuleMonoidAlgebra.obj` of the three modules by definition of `ShortComplex.map`, so
  -- the counit and unit of `equivalenceModuleMonoidAlgebra` identify them with `ker g`, `F`, `A`.
  let S := g.shortComplexKer.map ofModuleMonoidAlgebra
  have hS : S.ShortExact := (g.shortExact_shortComplexKer hg).map_of_exact _
  have e₁ : S.X₁.ρ.asModule ≃ₗ[MonoidAlgebra k G] LinearMap.ker g :=
    (counitIso (ModuleCat.of _ (LinearMap.ker g))).toLinearEquiv
  have e₂ : S.X₂.ρ.asModule ≃ₗ[MonoidAlgebra k G] (A.ρ.asModule →₀ MonoidAlgebra k G) :=
    (counitIso (ModuleCat.of _ _)).toLinearEquiv
  have : Module.Projective (MonoidAlgebra k G) S.X₂.ρ.asModule := .of_equiv' e₂.symm
  -- `ker g` is cohomologically trivial, by the long exact sequence, since `F` and `A` are.
  have h₁ (H : Subgroup G) [Fintype H] (n : ℤ) : IsZero (tateCohomology (res H.subtype S.X₁) n) :=
    isZero_X₁_of_isZero_X₃_of_isZero_X₂ ((shortExact_res H.subtype).2 hS) (n - 1) n (by omega)
      ((hA H _).of_iso ((tateCohomologyFunctor _).mapIso ((resFunctor H.subtype).mapIso
        (unitIso A).symm))) (isZero_res_of_projective S.X₂ H n)
  -- `ker g` is a `k`-submodule of the free `k`-module `F`.
  have := ((LinearMap.ker g).restrictScalars k).free_of_isPrincipalIdealRing
  have : Module.Free k (LinearMap.ker g) :=
    .of_equiv (Submodule.restrictScalarsEquiv k _ _ (LinearMap.ker g) |>.restrictScalars k)
  have : Module.Free k S.X₁.V :=
    .of_equiv (e₁.restrictScalars k |>.symm.trans S.X₁.ρ.asModuleEquiv)
  have := Rep.projective_of_isZero_res hk S.X₁ h₁
  exact .of_equiv' e₁

/-- **Nakayama–Rim: cohomological triviality gives projective dimension at most one.** If `A` is
cohomologically trivial, the kernel of every surjection onto `A.ρ.asModule` from a projective
`k[G]`-module is projective. Here `k` is a principal ideal domain of characteristic zero in which
every prime number is a unit or generates a maximal ideal; no finiteness is assumed of `A` or of
the projective module. -/
theorem projective_ker_of_isZero_res
    (hk : ∀ p : ℕ, p.Prime → IsUnit (p : k) ∨ (Ideal.span {(p : k)}).IsMaximal)
    (A : Rep k G)
    (hA : ∀ (S : Subgroup G) [Fintype S] (n : ℤ),
      IsZero (tateCohomology (res S.subtype A) n))
    {P : Type*} [AddCommGroup P] [Module (MonoidAlgebra k G) P]
    [Module.Projective (MonoidAlgebra k G) P]
    (f : P →ₗ[MonoidAlgebra k G] A.ρ.asModule) (hf : Function.Surjective f) :
    Module.Projective (MonoidAlgebra k G) (LinearMap.ker f) :=
  have := projective_ker_linearCombination hk A hA
  f.projective_ker_of_projective_ker hf _
    (Finsupp.linearCombination_surjective _ Function.surjective_id)

end Rep
