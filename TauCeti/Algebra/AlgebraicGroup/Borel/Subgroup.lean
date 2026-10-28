/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Borel.Basic

/-!
# Borel subgroups inside closed subgroups

A Borel subgroup of an affine group that is contained in a closed subgroup is also a
Borel subgroup of that closed subgroup. More generally, a closed subgroup containing
every smooth connected solvable subgroup has exactly the same Borel subgroups as the
ambient group. This allows maximality arguments to pass to smaller ambient groups.

Coordinate morphisms of closed immersions are surjective. The candidate comparison uses
`CommHopfAlgCat.Hom.quotientIsoOfSurjective`, and the maximality comparison uses the
image/inverse-image correspondence for Hopf ideals.

## References

* A. Borel, *Linear Algebraic Groups*, 2nd ed. (1991), §11.1.
* J. S. Milne, *Algebraic Groups* (2017), §17.a.
-/

public section

open CategoryTheory

namespace TauCeti.HopfIdeal

universe u v

variable {k : Type u} [Field k]
variable {H K : FiniteTypeCommHopfAlgCat.{u, v} k}

/-- A closed subgroup of a closed subgroup is smooth, geometrically connected, and
geometrically solvable exactly when it has these properties in the ambient group. -/
theorem isBorelCandidate_comapOfSurjective_iff (f : H ⟶ K)
    (hf : Function.Surjective (FiniteTypeCommHopfAlgCat.toBialgHom f)) (J : HopfIdeal k K) :
    IsBorelCandidate k H (J.comapOfSurjective (FiniteTypeCommHopfAlgCat.toBialgHom f) hf) ↔
      IsBorelCandidate k K J := by
  rw [isBorelCandidate_iff, isBorelCandidate_iff]
  let e := f.hom.quotientIsoOfSurjective hf J
  exact (smoothCommHopfAlgProperty k ⊓
    (geometricallyConnectedCommHopfAlgProperty k ⊓
      geometricallySolvablePointsCommHopfAlgProperty k)).prop_iff_of_iso e

/-- Restricting the ambient group of a Borel subgroup to a closed subgroup containing it
preserves the Borel property. -/
theorem IsBorelOverAlgClosed.of_comapOfSurjective (f : H ⟶ K)
    (hf : Function.Surjective (FiniteTypeCommHopfAlgCat.toBialgHom f))
    {J : HopfIdeal k K}
    (hJ : IsBorelOverAlgClosed k H
      (J.comapOfSurjective (FiniteTypeCommHopfAlgCat.toBialgHom f) hf)) :
    IsBorelOverAlgClosed k K J := by
  rw [isBorelOverAlgClosed_iff] at hJ ⊢
  refine ⟨hJ.1, (isBorelCandidate_comapOfSurjective_iff f hf J).mp hJ.2.prop, ?_⟩
  intro I hI hIJ
  apply le_of_comapOfSurjective_le_comapOfSurjective _ hf
  exact hJ.2.le_of_le ((isBorelCandidate_comapOfSurjective_iff f hf I).mpr hI)
    (comapOfSurjective_mono _ hf hIJ)

/-- A Borel subgroup contained in the subgroup cut out by `I` is Borel in that subgroup.
Hopf ideal order reverses inclusion of the represented subgroups. -/
theorem IsBorelOverAlgClosed.map_of_le {I J : HopfIdeal k H}
    (hJ : IsBorelOverAlgClosed k H J) (hIJ : I ≤ J) :
    IsBorelOverAlgClosed k (FiniteTypeCommHopfAlgCat.quotient H I)
      (J.map (Bialgebra.Quotient.mkBialgHom I.toIdeal)) := by
  apply IsBorelOverAlgClosed.of_comapOfSurjective (FiniteTypeCommHopfAlgCat.mkQuotient H I)
    (CommHopfAlgCat.mkQuotient_surjective _ _)
  convert hJ using 1
  exact comapOfSurjective_map_mkBialgHom hIJ

/-- If a closed subgroup contains every Borel candidate of the ambient group, its Borel
subgroups are precisely the ambient Borel subgroups. The kernel condition expresses this
containment in coordinate Hopf ideal order. -/
theorem isBorelOverAlgClosed_comapOfSurjective_iff (f : H ⟶ K)
    (hf : Function.Surjective (FiniteTypeCommHopfAlgCat.toBialgHom f))
    (hker : ∀ I : HopfIdeal k H, IsBorelCandidate k H I →
      kerOfSurjective (FiniteTypeCommHopfAlgCat.toBialgHom f) hf ≤ I)
    (J : HopfIdeal k K) :
    IsBorelOverAlgClosed k H (J.comapOfSurjective (FiniteTypeCommHopfAlgCat.toBialgHom f) hf) ↔
      IsBorelOverAlgClosed k K J := by
  refine ⟨fun hJ ↦ hJ.of_comapOfSurjective f hf, fun hJ ↦ ?_⟩
  rw [isBorelOverAlgClosed_iff] at hJ ⊢
  refine ⟨hJ.1, (isBorelCandidate_comapOfSurjective_iff f hf J).mpr hJ.2.prop, ?_⟩
  intro I hI hIJ
  let g := FiniteTypeCommHopfAlgCat.toBialgHom f
  let _ : RingHomSurjective (g : H →+* K) := ⟨hf⟩
  have hIcomap : (I.map g).comapOfSurjective g hf = I := by
    rw [comapOfSurjective_map, sup_eq_left.mpr (hker I hI)]
  have hImap : IsBorelCandidate k K (I.map g) := by
    apply (isBorelCandidate_comapOfSurjective_iff f hf _).mp
    rwa [hIcomap]
  have hmaple : I.map g ≤ J := (map_le_iff_le_comapOfSurjective hf).mpr hIJ
  have hle := comapOfSurjective_mono g hf (hJ.2.le_of_le hImap hmaple)
  rwa [hIcomap] at hle

end TauCeti.HopfIdeal
