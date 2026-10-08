/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.RepresentationTheory.Homological.TateCohomology.Coinduced

/-!
# Projective representations are cohomologically trivial

Let `k` be a commutative ring and `G` a group. A representation `A` of `G` over `k` whose
`k[G]`-module is projective has vanishing Tate cohomology in every degree on every finite subgroup
of `G` (Serre, *Local Fields*, IX §5; Brown, *Cohomology of Groups*, VI §8). This is
the easy half of the theorem of Nakayama and Rim, which for `k = ℤ` characterizes the
cohomologically trivial `G`-modules of a finite group `G` as those of projective dimension at most
one over `ℤ[G]`.

The projection `Ind_⊥^G A → A` from the representation induced from the trivial subgroup is an
epimorphism, so a projective `A` is a retract of `Ind_⊥^G A`. The Tate cohomology of every finite
subgroup with coefficients in `Ind_⊥^G A` vanishes
(`TauCeti.TateCohomology.isZero_res_indBot`), hence so does that of its retract `A`.

## Main statements

* `Rep.isZero_res_of_projective`: if `A.ρ.asModule` is a projective
  `k[G]`-module, then `H-hat^n(S, A) = 0` for every finite subgroup `S` of `G` and every `n : ℤ`.

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

end Rep
