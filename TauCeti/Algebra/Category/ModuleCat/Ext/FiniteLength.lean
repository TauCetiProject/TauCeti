/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.RingTheory.FiniteLength
public import TauCeti.CategoryTheory.Exact.Abelian
public import TauCeti.CategoryTheory.Exact.YonedaExt.BaerSum
import TauCeti.Algebra.Module.LinearMap.FiniteLength
import Mathlib.Algebra.Category.ModuleCat.Projective
import TauCeti.Algebra.Category.ModuleCat.Quotient
import TauCeti.Algebra.Module.Projective.FinitePresentation
import TauCeti.CategoryTheory.Exact.YonedaExt.LongExact
import TauCeti.CategoryTheory.Exact.YonedaExt.TrivialIdeal
import TauCeti.RingTheory.Artinian.FiniteLength

/-!
# Finite length of `Ext¹` of modules

Let `A` be an algebra over a commutative ring `R`, and `f : P₁ → P₀` a map of `A`-modules with
`P₀` projective. The presentation `range f ⟶ P₀ ⟶ P₀ ⧸ range f` makes `Ext¹(P₀ ⧸ range f, N)` a
quotient of `Hom_A(range f, N)`, which embeds in `Hom_A(P₁, N)`. Hence `Ext¹(P₀ ⧸ range f, N)` has
finite length over `R` as soon as `P₁` is finitely generated over `A` and `N` has finite length
over `R` (`LinearMap.isFiniteLength_ext1_cokernel`). Neither `f` nor `P₁` need be injective or
projective, and `A` need not be finitely generated over `R`: for instance `f` may be multiplication
by `x` on `k[x]`, with `N = k`.

The same holds for Mathlib's derived `Ext¹` (`LinearMap.isFiniteLength_ext_cokernel`, in
`TauCeti/Algebra/Category/ModuleCat/HomCocycle.lean`).

Over an Artin algebra, every finitely generated module has such a presentation, so `Ext¹` between
finitely generated modules has finite length over the base ring (`ModuleCat.isFiniteLength_ext1`).

Here `Ext¹` is the Yoneda `Ext¹` of the abelian exact structure on `ModuleCat A`, with the
`R`-linear structure of the scoped instances of `ModuleCat.Algebra`.

## References

* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*, Cambridge
  University Press (1995), Section IV.2.
-/

public section

open CategoryTheory TauCeti TauCeti.ExactStructure
open scoped ModuleCat.Algebra

universe u v w t

variable {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]

namespace LinearMap

variable {P₀ P₁ : Type t} [AddCommGroup P₀] [Module A P₀] [Module.Projective A P₀]
  [AddCommGroup P₁] [Module A P₁] [Module.Finite A P₁]

/-- **`Ext¹` of a cokernel has finite length** over the base ring when the source of the presenting
map is finitely generated and the coefficients have finite length over the base ring: for
`f : P₁ → P₀` with `P₀` projective, `Ext¹(P₀ ⧸ range f, N)` is a quotient of
`Hom_A(range f, N) ⊆ Hom_A(P₁, N)`. -/
theorem isFiniteLength_ext1_cokernel (f : P₁ →ₗ[A] P₀) {N : ModuleCat.{t} A}
    (hN : IsFiniteLength R N) :
    IsFiniteLength R ((ExactStructure.abelian (ModuleCat.{t} A)).Ext1
      (ModuleCat.of A (P₀ ⧸ range f)) N) := by
  let S := (range f).quotientShortComplex
  let e : (ExactStructure.abelian (ModuleCat.{t} A)).Extension S.X₃ S.X₁ :=
    ⟨S.X₂, S.f, S.g, S.zero, (abelian_conflation _).mpr (range f).shortExact_quotientShortComplex⟩
  have hP : (ExactStructure.abelian _).isProjective e.obj :=
    (abelian_isProjective_iff _).mpr (ModuleCat.projective_of_categoryTheory_projective _)
  -- As `P₀` is projective, every class is a cobase change of the class of `e`.
  let c : (S.X₁ ⟶ N) →ₗ[R] (ExactStructure.abelian _).Ext1 S.X₃ N :=
    { toFun a := (Ext1.mk e).pushout a
      map_add' := Ext1.pushout_add _
      map_smul' r a := Ext1.pushout_smul r _ a }
  have hc : Function.Surjective c := fun ξ ↦
    (e.exact_mk_pushout_pullback_g N ξ).mp ((isProjective_iff_forall_ext1_eq_zero _).mp hP _ _)
  -- `Hom_A(range f, N)` embeds in `Hom_A(P₁, N)`.
  let ι : (S.X₁ ⟶ N) →ₗ[R] (P₁ →ₗ[A] N) :=
    f.rangeRestrict.lcomp R N ∘ₗ (ModuleCat.homLinearEquiv (S := R)).toLinearMap
  have hι : Function.Injective ι := fun a b h ↦ ModuleCat.hom_ext
    ((cancel_right f.surjective_rangeRestrict).mp h)
  exact ((isFiniteLength_linearMap P₁ N hN).of_injective hι).of_surjective hc

end LinearMap

namespace ModuleCat

variable (R) [IsArtinianRing R] [Module.Finite R A]

/-- **`Ext¹` between finitely generated modules over an Artin algebra has finite length** over the
base ring. A finitely generated module is the cokernel of a map between finitely generated
projective modules, to which `LinearMap.isFiniteLength_ext1_cokernel` applies. -/
theorem isFiniteLength_ext1 [Small.{w} A] (M N : ModuleCat.{w} A) [Module.Finite A M]
    [Module.Finite A N] :
    IsFiniteLength R ((ExactStructure.abelian (ModuleCat.{w} A)).Ext1 M N) := by
  have : IsArtinianRing A := IsArtinianRing.of_finite R A
  have : Module.FinitePresentation A M := Module.finitePresentation_of_finite A M
  let P := FiniteProjectivePresentation.ofFinitePresentation (M := M)
  let c : M ≅ ModuleCat.of A (P.P₀ ⧸ LinearMap.range P.p) :=
    (P.exact.linearEquivOfSurjective P.surjective).toModuleIso.symm
  exact (Ext1.pullbackLinearEquiv R c).isFiniteLength
    (P.p.isFiniteLength_ext1_cokernel (isFiniteLength_of_finite_trans R A N))

end ModuleCat
