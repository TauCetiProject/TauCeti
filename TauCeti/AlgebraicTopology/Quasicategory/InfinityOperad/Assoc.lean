/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Quasicategory.InfinityOperad.Nerve
public import TauCeti.CategoryTheory.CategoryOfOperators.Assoc

/-!
# The associative `∞`-operad

The nerve of the functor `Assoc^⊗ ⥤ Fin_*` from the category of operators of the associative
operad is an `∞`-operad (`TauCeti.Assoc.infinityOperad`), the associative `∞`-operad over which
monoidal quasicategories are fibred. It satisfies the criterion `SSet.InfinityOperad.of_nerveMap`:
inert maps lift to strongly coCartesian morphisms (`TauCeti.Assoc.Hom.ofBase`), the only object
over `⟨1⟩` is `⟨1⟩`, and the morphisms over the inert projections are the projections `Assoc.ρ`,
so the Segal condition is the decomposition `TauCeti.Assoc.homLiftEquiv` of a morphism into
single-output lifts.

## Main results

* `TauCeti.Assoc.infinityOperad`: the nerve of `Assoc^⊗ ⥤ Fin_*` is an `∞`-operad.

## References

* J. Lurie, *Higher Algebra*, §2.1.1 and Definition 4.1.1.3 (the associative `∞`-operad).
-/

public section

universe u

open CategoryTheory Functor TauCeti

namespace TauCeti

namespace Assoc

/-- **The associative `∞`-operad**: the nerve of the functor `Assoc^⊗ ⥤ Fin_*` from the category
of operators of the associative operad is an `∞`-operad. Its only color is `⟨1⟩`, and its
multi-operations from `n` copies of it to it are the linear orders on `n` elements. -/
instance infinityOperad : SSet.InfinityOperad.{u} (nerveMap toFinPointed.{u}) :=
  SSet.InfinityOperad.of_nerveMap _
    (fun {x n} g hg ↦ by
      -- `g` is a map `⟨x.len⟩ ⟶ ⟨n.len⟩`, lifted by `Assoc.Hom.ofBase`.
      let g' : FinPointed.mk x.len ⟶ FinPointed.mk n.len := g
      have := isStronglyCocartesian_of_isInert (Hom.ofBase (X := x) (Y := mk n.len) g')
        (by rw [Hom.ofBase_base]; exact hg)
      rw [Hom.ofBase_base] at this
      exact ⟨mk n.len, Hom.ofBase g', this⟩)
    (fun n c hc ↦ by
      -- The objects over `⟨1⟩` are `⟨1⟩`.
      obtain rfl : c = fun _ ↦ mk 1 := funext fun i ↦ Assoc.ext (congrArg FinPointed.len (hc i))
      exact ⟨mk n.len, fun i ↦ ρ (Y := mk n.len) i, rfl, fun i ↦ by
        simpa using isStronglyCocartesian_of_isInert (ρ (Y := mk n.len) i)
          (by simpa using FinPointed.isInert_ρ i)⟩)
    (fun {x y c} φ hφ e ↦ by
      -- The morphisms over the inert projections are the projections `Assoc.ρ`, so the
      -- postcomposition is the decomposition `Assoc.homLiftEquiv` into single-output lifts.
      obtain rfl : c = fun _ ↦ mk 1 := funext fun i ↦ Assoc.ext
        (congrArg FinPointed.len (IsHomLift.codomain_eq toFinPointed (FinPointed.ρ i) (φ i)))
      obtain rfl : φ = fun i ↦ ρ (Y := y) i := funext fun i ↦ Hom.ext_of_isInert
        ((isHomLift_iff.1 (hφ i)).trans (ρ_base (Y := y) i).symm)
        (by rw [isHomLift_iff.1 (hφ i)]; exact FinPointed.isInert_ρ (n := FinPointed.mk y.len) i)
      exact ⟨homLiftEquiv e, homLiftEquiv_apply_val e⟩)

end Assoc


end TauCeti
