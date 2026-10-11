/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.TateCohomology.Projective
import Mathlib.RingTheory.Flat.Equalizer
import TauCeti.Algebra.Module.Projective.Schanuel
import TauCeti.LinearAlgebra.FreeModule.PID
import TauCeti.RepresentationTheory.Homological.TateCohomology.HomologySequence
import TauCeti.RepresentationTheory.Rep.TensorShortExact

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

The resolution of length one makes cohomological triviality stable under tensor products: if `A`
is cohomologically trivial and `Tor₁^k(M, A) = 0`, then `M ⊗ A`, with the diagonal action, is
cohomologically trivial (Nakayama, Ann. of Math. 65 (1957)), because tensoring
`0 → R → F → A → 0` with `M` stays exact and `M ⊗ R`, `M ⊗ F` are cohomologically trivial
(`Rep.isZero_res_tensor_of_shortExact`). This is how the theorem of Nakayama and Rim enters the
Tate–Nakayama generalization of Tate's theorem, an isomorphism from the Tate cohomology of `M` in
degree `r` to that of `M ⊗ C` in degree `r + 2`, for a class module `C` with `Tor₁^ℤ(M, C) = 0`,
whose splitting module is cohomologically trivial. The vanishing of `Tor₁^k(M, A)` is stated
without a `Tor` functor, in the equivalent form that `M ⊗ -` keeps injective the first map of
every short exact sequence `0 → X → Y → A → 0` of `k`-modules; it holds when `M` is flat over `k`
and when `A` is.

## Main statements

* `Rep.projective_ker_of_isZero_res`: if `A` is cohomologically trivial, every
  surjection onto `A.ρ.asModule` from a projective `k[G]`-module has projective kernel.
* `Rep.isZero_res_tensor_of_isZero_res`: if `A` is cohomologically trivial and
  `Tor₁^k(M, A) = 0`, then `M ⊗ A` is cohomologically trivial.
* `Rep.isZero_res_tensor_of_isZero_res_of_flat_left`,
  `Rep.isZero_res_tensor_of_isZero_res_of_flat_right`: the same when `M`, respectively `A`, is
  flat over `k`.

## References

* D. S. Rim, *Modules over finite groups*, Ann. of Math. 69 (1959).
* K. S. Brown, *Cohomology of Groups*, Chapter VI, §8.
* J.-P. Serre, *Local Fields*, Chapter IX, §§3–5.
* T. Nakayama, *Cohomology of class field theory and tensor product modules I*, Ann. of Math. 65
  (1957).
-/

public section

universe u

open CategoryTheory Limits MonoidalCategory TauCeti.TateCohomology

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

/-- **Tensoring with a cohomologically trivial module.** Let `k` be a principal ideal domain of
characteristic zero in which every prime number is a unit or generates a maximal ideal, and let
`A` be a cohomologically trivial representation of a finite group `G` over `k`. If
`Tor₁^k(M, A) = 0`, in the form that `M ⊗ X → M ⊗ Y` is injective for every short exact sequence
`0 → X → Y → A → 0` of `k`-modules, then `M ⊗ A` is cohomologically trivial. -/
theorem isZero_res_tensor_of_isZero_res
    (hk : ∀ p : ℕ, p.Prime → IsUnit (p : k) ∨ (Ideal.span {(p : k)}).IsMaximal)
    (A : Rep k G)
    (hA : ∀ (S : Subgroup G) [Fintype S] (n : ℤ),
      IsZero (tateCohomology (res S.subtype A) n))
    (M : Rep k G)
    (hM : ∀ {X Y : Type u} [AddCommGroup X] [Module k X] [AddCommGroup Y] [Module k Y]
      (f : X →ₗ[k] Y) (g : Y →ₗ[k] A.V), Function.Injective f → Function.Exact f g →
        Function.Surjective g → Function.Injective (f.lTensor M.V))
    (S : Subgroup G) [Fintype S] (n : ℤ) :
    IsZero (tateCohomology (res S.subtype (M ⊗ A)) n) := by
  -- The free cover `F ↠ A` has projective kernel `R`, by the theorem of Nakayama and Rim.
  set q := Finsupp.linearCombination (MonoidAlgebra k G) (id : A.ρ.asModule → _)
  have hq : Function.Surjective q :=
    Finsupp.linearCombination_surjective _ Function.surjective_id
  have := projective_ker_linearCombination hk A hA
  -- The resolution `0 ⟶ R ⟶ F ⟶ A ⟶ 0`, transported to representations. Its terms are
  -- `ofModuleMonoidAlgebra.obj` of the three modules by definition of `ShortComplex.map`, so the
  -- counit of `equivalenceModuleMonoidAlgebra` identifies their `k[G]`-modules with `R`, `F`, `A`.
  let T := q.shortComplexKer.map ofModuleMonoidAlgebra
  have hT : T.ShortExact := (q.shortExact_shortComplexKer hq).map_of_exact _
  have : Module.Projective (MonoidAlgebra k G) T.X₁.ρ.asModule := .of_equiv
    (equivalenceModuleMonoidAlgebra.counitIso.app q.shortComplexKer.X₁).toLinearEquiv.symm
  have : Module.Projective (MonoidAlgebra k G) T.X₂.ρ.asModule := .of_equiv
    (equivalenceModuleMonoidAlgebra.counitIso.app q.shortComplexKer.X₂).toLinearEquiv.symm
  let e : T.X₃ ≅ A := (equivalenceModuleMonoidAlgebra.unitIso.app A).symm
  -- Tensoring the resolution with `M` keeps its first map injective, by the hypothesis on `Tor₁`.
  have hinj : Function.Injective (T.f.hom.toLinearMap.lTensor M.V) := by
    have hexact := (exact_iff_function_exact T).1 hT.exact
    refine hM _ (T.g ≫ e.hom).hom.toLinearMap ((mono_iff_injective T.f).1 hT.mono_f) ?_ ?_
    · exact hexact.comp_injective _ ((mono_iff_injective e.hom).1 inferInstance) (map_zero _)
    · exact ((epi_iff_surjective e.hom).1 inferInstance).comp
        ((epi_iff_surjective T.g).1 hT.epi_g)
  exact (isZero_res_tensor_of_shortExact M hT hinj S n).of_iso
    ((tateCohomologyFunctor n).mapIso ((resFunctor S.subtype).mapIso (whiskerLeftIso M e.symm)))

/-- **Tensoring a cohomologically trivial module with a flat module.** Over `k` as in
`Rep.isZero_res_tensor_of_isZero_res`, if `A` is cohomologically trivial and `M` is flat over `k`,
then `M ⊗ A` is cohomologically trivial. -/
theorem isZero_res_tensor_of_isZero_res_of_flat_left
    (hk : ∀ p : ℕ, p.Prime → IsUnit (p : k) ∨ (Ideal.span {(p : k)}).IsMaximal)
    (A : Rep k G)
    (hA : ∀ (S : Subgroup G) [Fintype S] (n : ℤ),
      IsZero (tateCohomology (res S.subtype A) n))
    (M : Rep k G) [Module.Flat k M.V] (S : Subgroup G) [Fintype S] (n : ℤ) :
    IsZero (tateCohomology (res S.subtype (M ⊗ A)) n) :=
  isZero_res_tensor_of_isZero_res hk A hA M
    (fun f _ hf _ _ ↦ Module.Flat.lTensor_preserves_injective_linearMap f hf) S n

/-- **Tensoring a flat cohomologically trivial module.** Over `k` as in
`Rep.isZero_res_tensor_of_isZero_res`, if `A` is cohomologically trivial and flat over `k`, then
`M ⊗ A` is cohomologically trivial for every representation `M`. -/
theorem isZero_res_tensor_of_isZero_res_of_flat_right
    (hk : ∀ p : ℕ, p.Prime → IsUnit (p : k) ∨ (Ideal.span {(p : k)}).IsMaximal)
    (A : Rep k G) [Module.Flat k A.V]
    (hA : ∀ (S : Subgroup G) [Fintype S] (n : ℤ),
      IsZero (tateCohomology (res S.subtype A) n))
    (M : Rep k G) (S : Subgroup G) [Fintype S] (n : ℤ) :
    IsZero (tateCohomology (res S.subtype (M ⊗ A)) n) :=
  isZero_res_tensor_of_isZero_res hk A hA M
    (fun f g hf hfg hg ↦ LinearMap.lTensor_injective_of_exact_of_flat g hg f hf hfg M.V) S n

end Rep
