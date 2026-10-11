/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Global.PlacePermutation.Archimedean
public import TauCeti.NumberTheory.ClassFieldTheory.Global.SemilocalUnits
public import TauCeti.NumberTheory.NumberField.Global.Ideles.InfiniteIdeles
public import TauCeti.RepresentationTheory.Homological.TateCohomology.Pi

/-!
# The Herbrand quotient of the infinite ideles

Let `L/K` be a cyclic extension of number fields. This file computes the Herbrand quotient of the
infinite ideles `L_∞ˣ = ∏_w L_wˣ` of `L`, as a representation of `Gal(L/K)`:

```text
h(L_∞ˣ) = ∏_v [L_w : K_v],
```

the product running over the infinite places `v` of `K`, with `w` any place of `L` above `v`
(`herbrandQuotient_infiniteIdelesRep`). A factor is `2` when `v` is real and the places above it
are complex, and `1` otherwise, so this is the Herbrand quotient of the permutation lattice
`ℤ[places of L at ∞]` (`herbrandQuotient_infiniteIdelesRep_eq_herbrandQuotient_ofMulAction`).

This is the archimedean factor of the Herbrand quotient of the `S`-ideles
`I_{L,S} = L_∞ˣ × ∏_{w ∈ S} L_wˣ × ∏_{w ∉ S} 𝒪_wˣ`, which enters the computation
`h(C_L) = h(I_{L,S}) / h(U_{L,S}) = [L : K]` behind the first fundamental inequality. The
comparison with the permutation lattice matches the logarithmic computation of the `S`-units,
which embeds them in the real representation spanned by the same lattice.

The proof decomposes the infinite ideles as the product over `v` of the semi-local units
`(K_v ⊗[K] L)ˣ` (`TauCeti.GlobalNumberFields.infiniteIdelesPiIso`), takes the Herbrand quotient
factor by factor (`TauCeti.TateCohomology.herbrandQuotient_pi`), and uses the archimedean local
computation `TauCeti.ClassFieldTheory.herbrandQuotient_infiniteSemilocalUnitsRep`.

## Main results

* `TauCeti.ClassFieldTheory.herbrandQuotient_infiniteIdelesRep`: `h(L_∞ˣ) = ∏_v [L_w : K_v]`.
* `TauCeti.ClassFieldTheory.herbrandQuotient_infiniteIdelesRep_eq_herbrandQuotient_ofMulAction`:
  `h(L_∞ˣ)` is the Herbrand quotient of the permutation lattice on the infinite places of `L`.

## References

* J. S. Milne, *Class Field Theory*, Chapter VII, §2 and the proof of Theorem 4.3.
* J. Neukirch, *Algebraic Number Theory*, Chapter VI, §2.
-/

public section

noncomputable section

open NumberField NumberField.InfinitePlace Module
open scoped NumberField.LiesOver

namespace TauCeti.ClassFieldTheory

open GlobalNumberFields

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)]

/-- **The Herbrand quotient of the infinite ideles.** For a cyclic extension `L/K` of number fields,
the infinite ideles `L_∞ˣ` have Herbrand quotient `∏_v [L_w : K_v]` as a representation of
`Gal(L/K)`, the product running over the infinite places `v` of `K`. The places `w` above each
`v` may be chosen arbitrarily. -/
theorem herbrandQuotient_infiniteIdelesRep
    (w : ∀ v : InfinitePlace K, {w : InfinitePlace L // w.LiesOver v}) :
    TateCohomology.herbrandQuotient (infiniteIdelesRep K L) =
      ∏ v, (finrank v.Completion (w v).1.Completion : ℚ) := by
  rw [TateCohomology.herbrandQuotient_eq_of_iso (infiniteIdelesPiIso K L),
    TateCohomology.herbrandQuotient_pi (fun v ↦ infiniteSemilocalUnitsRep L v) Finset.univ
      (by simp) (by simp)]
  exact Finset.prod_congr rfl fun v _ ↦ herbrandQuotient_infiniteSemilocalUnitsRep v (w v).1

/-- **The infinite ideles and the archimedean place lattice** have the same Herbrand quotient: for
a cyclic extension `L/K` of number fields, `h(L_∞ˣ)` is the Herbrand quotient of the permutation
lattice on the infinite places of `L`, namely `2^r` with `r` the number of infinite places of `K`
ramified in `L` (`herbrandQuotient_ofMulAction_infinitePlace`). -/
theorem herbrandQuotient_infiniteIdelesRep_eq_herbrandQuotient_ofMulAction :
    TateCohomology.herbrandQuotient (infiniteIdelesRep K L) =
      TateCohomology.herbrandQuotient (Rep.ofMulAction ℤ (L ≃ₐ[K] L) (InfinitePlace L)) := by
  classical
  have hw (v : InfinitePlace K) : ∃ w : InfinitePlace L, w.LiesOver v := by
    obtain ⟨w, rfl⟩ := comap_surjective (K := L) v
    exact ⟨w, inferInstance⟩
  rw [herbrandQuotient_infiniteIdelesRep fun v ↦ ⟨(hw v).choose, (hw v).choose_spec⟩,
    herbrandQuotient_ofMulAction_infinitePlace_eq_prod]
  refine Finset.prod_congr rfl fun v _ ↦ ?_
  have := (hw v).choose_spec
  rw [finrank_completion_eq_ite v (hw v).choose]
  split <;> simp

end TauCeti.ClassFieldTheory
