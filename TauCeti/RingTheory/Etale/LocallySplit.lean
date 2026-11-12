/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Spectrum.Prime.FreeLocus

/-!
# Étale neighbourhoods splitting finite étale algebras

A finite étale algebra becomes a product of copies of the base on an étale neighbourhood of
each prime of the base. No constant-rank assumption on the original algebra is needed: first
restrict to a principal open on which the rank is constant, then use
`Algebra.IsFiniteSplit.exists_tensorProduct_of_etale`.

This is the affine form of the local splitting of finite étale morphisms, Stacks, Lemma
41.18.3 (04HN). The neighbourhood is affine, contains a point over the specified prime, and
is étale over the original base; it need not be finite over that base.

## References

* [Stacks Project, Lemma 41.18.3](https://stacks.math.columbia.edu/tag/04HN).
* H. W. Lenstra, *Galois theory for schemes*, Proposition 5.10, as formalized in Mathlib's
  `Algebra.IsFiniteSplit.exists_tensorProduct_of_etale`.
-/

public section

open scoped TensorProduct

namespace TauCeti.Algebra.Etale

universe u

/-- Every finite étale algebra splits on an affine étale neighbourhood of any given base
prime. The prime `q` ensures that this neighbourhood actually lies over `p`, including when
the algebra has rank zero there. -/
theorem exists_isFiniteSplit_etaleNeighborhood (R B : Type u) [CommRing R] [CommRing B]
    [Algebra R B] [Algebra.Etale R B] [Module.Finite R B] (p : PrimeSpectrum R) :
    ∃ (T : Type u) (_ : CommRing T) (_ : Algebra R T) (_ : Algebra.Etale R T)
      (q : PrimeSpectrum T), q.comap (algebraMap R T) = p ∧
        Algebra.IsFiniteSplit T (T ⊗[R] B) := by
  have : Module.FinitePresentation R B := .of_finite_of_finitePresentation R B
  -- The membership type specifies the rank fibre as the open set to refine.
  obtain ⟨_, ⟨_, ⟨a, rfl⟩, rfl⟩, hpa, ha⟩ :=
    PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open
    (show p ∈ {q | Module.rankAtStalk (R := R) B q = Module.rankAtStalk B p} from rfl)
    ((Module.isLocallyConstant_rankAtStalk (R := R) (M := B)).isOpen_fiber _)
  let Ra := Localization.Away a
  have hmem : p ∈ Set.range (PrimeSpectrum.comap (algebraMap R Ra)) := by
    rw [PrimeSpectrum.localization_away_comap_range Ra a]
    exact hpa
  obtain ⟨pa, hpa'⟩ := hmem
  have hrank : Module.rankAtStalk (R := Ra) (Ra ⊗[R] B) =
      (Module.rankAtStalk (R := R) B p : ℕ) := by
    ext q
    rw [Module.rankAtStalk_baseChange]
    exact ha (PrimeSpectrum.localization_away_comap_range Ra a ▸ ⟨q, rfl⟩)
  obtain ⟨T, _, _, _, _, _, hT⟩ := Algebra.IsFiniteSplit.exists_tensorProduct_of_etale hrank
  let : Algebra R T := ((algebraMap Ra T).comp (algebraMap R Ra)).toAlgebra
  have : IsScalarTower R Ra T := .of_algebraMap_eq' rfl
  have : Algebra.Etale R T := .comp R Ra T
  obtain ⟨q, hq⟩ := (PrimeSpectrum.comap_surjective_of_faithfullyFlat (A := Ra) (B := T)) pa
  refine ⟨T, inferInstance, inferInstance, inferInstance, q, ?_, ?_⟩
  · rw [IsScalarTower.algebraMap_eq R Ra T, PrimeSpectrum.comap_comp, Function.comp_apply, hq, hpa']
  · exact Algebra.IsFiniteSplit.of_algEquiv
      (Algebra.TensorProduct.cancelBaseChange R Ra T T B)

end TauCeti.Algebra.Etale
