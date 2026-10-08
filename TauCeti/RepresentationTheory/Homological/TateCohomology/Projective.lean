/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.RepresentationTheory.Homological.TateCohomology.Coinduced
import TauCeti.RepresentationTheory.Homological.TateCohomology.HomologySequence

/-!
# Representations of projective dimension at most one are cohomologically trivial

Let `k` be a commutative ring and `G` a group. A representation `A` of `G` over `k` whose
`k[G]`-module is projective has vanishing Tate cohomology in every degree on every finite subgroup
of `G` (Serre, *Local Fields*, IX §5; Brown, *Cohomology of Groups*, VI §8). More generally, so
does a representation of projective dimension at most one over `k[G]`. This is the easy half of
the theorem of Nakayama and Rim, which for `k = ℤ` characterizes the cohomologically trivial
`G`-modules of a finite group `G` as those of projective dimension at most one over `ℤ[G]`.

The projection `Ind_⊥^G A → A` from the representation induced from the trivial subgroup is an
epimorphism, so a projective `A` is a retract of `Ind_⊥^G A`. The Tate cohomology of every finite
subgroup with coefficients in `Ind_⊥^G A` vanishes
(`TauCeti.TateCohomology.isZero_res_indBot`), hence so does that of its retract `A`. If
`0 → P₁ → P₀ → A → 0` is exact with `P₀` and `P₁` projective, the Tate cohomology of `A` sits in
the long exact sequence between that of `P₀` and that of `P₁`, both of which vanish.

## Main statements

* `Rep.isZero_res_of_projective`: if `A.ρ.asModule` is a projective
  `k[G]`-module, then `H-hat^n(S, A) = 0` for every finite subgroup `S` of `G` and every `n : ℤ`.
* `Rep.isZero_res_of_exact`: the same vanishing when `A.ρ.asModule` has a projective resolution
  `0 → P₁ → P₀ → A → 0` of length one.

## References

* J.-P. Serre, *Local Fields*, Chapter IX, §5.
* K. S. Brown, *Cohomology of Groups*, Chapter VI, §8.
* D. S. Rim, *Modules over finite groups*, Ann. of Math. 69 (1959).
-/

public section

universe u

open CategoryTheory Limits Rep

namespace Rep

variable {k G : Type u} [CommRing k] [Group G]

/-- **Projective modules are cohomologically trivial.** If the `k[G]`-module of a representation
`A` is projective, then the Tate cohomology of every finite subgroup `S` of `G` with coefficients
in `A` vanishes in every degree. -/
theorem isZero_res_of_projective (A : Rep k G)
    [Module.Projective (MonoidAlgebra k G) A.ρ.asModule] (S : Subgroup G) [Fintype S] (n : ℤ) :
    IsZero (tateCohomology (res S.subtype A) n) := by
  have : Projective A := by
    rwa [← equivalenceModuleMonoidAlgebra.map_projective_iff, ← IsProjective.iff_projective]
  -- `A` is a retract of `Ind_⊥^G A`, whose Tate cohomology on `S` vanishes.
  have h := (Retract.mk _ _ (Projective.factorThru_comp (𝟙 A) (indBotCounit A))).map
    (resFunctor (k := k) S.subtype) |>.map (tateCohomologyFunctor n)
  rw [IsZero.iff_id_eq_zero, ← h.retract,
    (TauCeti.TateCohomology.isZero_res_indBot S A.V n).eq_zero_of_tgt h.i, zero_comp]

/-- **Projective dimension at most one implies cohomological triviality.** Let
`0 → P₁ → P₀ → A → 0` be an exact sequence of `k[G]`-modules with `P₀` and `P₁` projective. Then
the Tate cohomology of every finite subgroup `S` of `G` with coefficients in `A` vanishes in every
degree. -/
theorem isZero_res_of_exact (A : Rep k G) {P₀ P₁ : Type u}
    [AddCommGroup P₀] [Module (MonoidAlgebra k G) P₀] [Module.Projective (MonoidAlgebra k G) P₀]
    [AddCommGroup P₁] [Module (MonoidAlgebra k G) P₁] [Module.Projective (MonoidAlgebra k G) P₁]
    {d : P₁ →ₗ[MonoidAlgebra k G] P₀} {q : P₀ →ₗ[MonoidAlgebra k G] A.ρ.asModule}
    (hd : Function.Injective d) (hdq : Function.Exact d q) (hq : Function.Surjective q)
    (S : Subgroup G) [Fintype S] (n : ℤ) :
    IsZero (tateCohomology (res S.subtype A) n) := by
  -- Carry the sequence of `k[G]`-modules to representations of `G`, then restrict to `S`.
  have hT := ((ModuleCat.shortComplex_shortExact
    (ModuleCat.shortComplexOfCompEqZero d q hdq.linearMap_comp_eq_zero) hdq hd hq).map_of_exact
      ofModuleMonoidAlgebra).map_of_exact (resFunctor S.subtype)
  -- The representation attached to a projective `k[G]`-module is cohomologically trivial.
  have hP (M : ModuleCat (MonoidAlgebra k G)) [Module.Projective (MonoidAlgebra k G) M] (m : ℤ) :
      IsZero (tateCohomology (res S.subtype (ofModuleMonoidAlgebra.obj M)) m) :=
    have : Module.Projective (MonoidAlgebra k G) (ofModuleMonoidAlgebra.obj M).ρ.asModule :=
      .of_equiv (equivalenceModuleMonoidAlgebra.counitIso.app M).toLinearEquiv.symm
    isZero_res_of_projective _ S m
  -- The terms of `hT` are, by definition of `ShortComplex.map`, the restrictions of the
  -- representations attached to `P₁`, `P₀` and `A.ρ.asModule`; the last is isomorphic to `A`.
  exact (TauCeti.TateCohomology.isZero_X₃_of_isZero_X₂_of_isZero_X₁ hT n (n + 1) rfl
    (hP (.of _ P₀) n) (hP (.of _ P₁) (n + 1))).of_iso
      ((tateCohomologyFunctor n).mapIso ((resFunctor S.subtype).mapIso
        (equivalenceModuleMonoidAlgebra.unitIso.app A)))

end Rep
