/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Algebra
public import TauCeti.Algebra.Category.ModuleCat.KrullSchmidt
public import TauCeti.CategoryTheory.Preadditive.Radical.Multiplicity
import TauCeti.CategoryTheory.Preadditive.Indecomposable

/-!
# The radical of the category of finitely generated modules

Let `A` be a finite-dimensional algebra over a field `k`. For finitely generated `A`-modules `X`
and `Y`, the morphisms `X ⟶ Y` and `Y ⟶ X` have the same dimension over `k` modulo the radical of
the module category (`ModuleCat.finrank_quotient_jacobsonRadicalSubmodule_comm`). Both modules
decompose into finitely many indecomposable modules (`TauCeti.exists_indecomposable_iso_biproduct`),
which have local endomorphism rings by Fitting's lemma; the dimension modulo the radical is
additive in both arguments and symmetric between objects with local endomorphism rings
(`TauCeti.finrank_quotient_jacobsonRadicalSubmodule_comm`).

## Main results

* `ModuleCat.finrank_quotient_jacobsonRadicalSubmodule_comm`: symmetry of the dimension of
  morphisms modulo the radical between finitely generated modules.
-/

public section

namespace ModuleCat

open CategoryTheory CategoryTheory.Limits TauCeti
open scoped ModuleCat.Algebra

universe u v w

variable (k : Type u) {A : Type v} [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A]

/-- **Symmetry of the radical quotient**: for finitely generated modules `X` and `Y` over a
finite-dimensional algebra, morphisms `X ⟶ Y` and `Y ⟶ X` have the same dimension modulo the
radical. -/
theorem finrank_quotient_jacobsonRadicalSubmodule_comm (X Y : ModuleCat.{w} A)
    [Module.Finite A X] [Module.Finite A Y] :
    Module.finrank k ((X ⟶ Y) ⧸ jacobsonRadicalSubmodule k X Y) =
      Module.finrank k ((Y ⟶ X) ⧸ jacobsonRadicalSubmodule k Y X) := by
  have : IsArtinianRing A := IsArtinianRing.of_finite k A
  -- Decompose both modules into indecomposable summands, which are finitely generated and have
  -- local endomorphism rings.
  obtain ⟨m, P, hP, ⟨e⟩⟩ := TauCeti.exists_indecomposable_iso_biproduct X
  obtain ⟨n, Q, hQ, ⟨f⟩⟩ := TauCeti.exists_indecomposable_iso_biproduct Y
  have (i : Fin m) : Module.Finite A (P i) :=
    Module.Finite.of_surjective (e.hom ≫ biproduct.π P i).hom
      ((ModuleCat.epi_iff_surjective _).1 inferInstance)
  have (j : Fin n) : Module.Finite A (Q j) :=
    Module.Finite.of_surjective (f.hom ≫ biproduct.π Q j).hom
      ((ModuleCat.epi_iff_surjective _).1 inferInstance)
  have (i : Fin m) : IsLocalRing (End (P i)) := isLocalRing_end_of_indecomposable (R := k) (hP i)
  have (j : Fin n) : IsLocalRing (End (Q j)) := isLocalRing_end_of_indecomposable (R := k) (hQ j)
  -- Both dimensions are sums over the summands of `X`, which are symmetric term by term.
  rw [finrank_quotient_jacobsonRadicalSubmodule_congr k e (Iso.refl Y),
    finrank_quotient_jacobsonRadicalSubmodule_congr k (Iso.refl Y) e,
    finrank_quotient_jacobsonRadicalSubmodule_biproduct,
    finrank_quotient_jacobsonRadicalSubmodule_biproduct_right]
  exact Finset.sum_congr rfl fun i _ ↦
    finrank_quotient_jacobsonRadicalSubmodule_comm_of_iso_biproduct k Q f

end ModuleCat
