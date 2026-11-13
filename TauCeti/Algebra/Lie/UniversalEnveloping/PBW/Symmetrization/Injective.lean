/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Free.Cover
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kernel
public import TauCeti.Algebra.Lie.UniversalEnveloping.PBW.Injective
public import TauCeti.Algebra.Lie.UniversalEnveloping.PBW.Symmetrization.Ideal
public import TauCeti.Algebra.Lie.UniversalEnveloping.PBW.Symmetrization.Map
public import TauCeti.LinearAlgebra.SymmetricAlgebra.Functoriality

import TauCeti.LinearAlgebra.SymmetricAlgebra.Powers

/-!
# Injectivity of PBW symmetrization

The symmetrization `Sym_R(L) → U_R(L)` of a Lie algebra over a commutative `ℚ`-algebra `R` is
injective, without any freeness or flatness hypothesis on `L`. Together with surjectivity, this
makes symmetrization a linear equivalence `Sym_R(L) ≃ₗ[R] U_R(L)`. The ideal comparison for Lie
ideals (`TauCeti.UniversalEnvelopingAlgebra.envelopingIdeal_le_map_symmetrization`) is what lets
injectivity pass from Lie algebras that are free as modules to arbitrary ones.

## Main results

* `TauCeti.UniversalEnvelopingAlgebra.pbwSymmetrizationMap_injective`: the general case.

## References

* F. Petracci, *Universal representations of Lie algebras by coderivations*
  (arXiv:math/0303020), §8. The statement is Corollary 8.1 there; the proof below instead reduces to
  the free case through a free cover of the Lie algebra.
-/

public section

namespace TauCeti.UniversalEnvelopingAlgebra

open TauCeti.SymmetricAlgebra

universe u v

variable (R : Type u) (L : Type v) [CommRing R] [Algebra ℚ R] [LieRing L] [LieAlgebra R L]

attribute [local instance 100] LieRing.ofAssociativeRing

local notation "U" => _root_.UniversalEnvelopingAlgebra R L
local notation "𝒮" => homogeneousSubmodule R L
local notation "F" => TauCeti.Algebra.wordFiltration (SymmetricAlgebra.ι R L)

/-- If every graded component `Sym^n(L) → gr_n U(L)` of the PBW map is injective, then an element
of the symmetric algebra which lies in word-filtration step `k` and symmetrizes to zero lies in
the preceding step. -/
private theorem mem_wordFiltrationPrevious_of_pbwSymmetrizationMap_eq_zero
    (h : ∀ n, Function.Injective (pbwHomogeneousComponentMap R L n))
    {k : ℕ} {p : SymmetricAlgebra R L} (hp : p ∈ F k)
    (h0 : pbwSymmetrizationMap R L p = 0) :
    p ∈ TauCeti.Algebra.wordFiltrationPrevious (SymmetricAlgebra.ι R L) k := by
  set q : 𝒮 k := DirectSum.decompose 𝒮 p k
  have hr := sub_decompose_mem_wordFiltrationPrevious hp
  have hsr := pbwSymmetrizationMap_mem_pbwFiltrationPrevious R L hr
  have hq : pbwSymmetrizationMap R L q ∈ pbwFiltrationPrevious R L k := by
    have : pbwSymmetrizationMap R L (q : SymmetricAlgebra R L) =
        -pbwSymmetrizationMap R L (p - q) := by
      rw [map_sub, h0, zero_sub, neg_neg]
    rw [this]
    exact neg_mem hsr
  have hk : IsUnit ((k.factorial : ℕ) : R) := IsUnit.natCast_factorial_of_algebra ℚ k
  have hmk := mk_pbwHomogeneousSymmetrization R L k hk q
  have hzero : pbwHomogeneousComponentMap R L k q = 0 := by
    rw [← hmk, Submodule.Quotient.mk_eq_zero,
      TauCeti.Algebra.wordFiltration.mem_previousRestricted_iff]
    simpa only [pbwFiltrationPrevious_def, ← pbwSymmetrizationMap_of_mem R L q.property] using hq
  have hq0 : q = 0 := h k (by rw [hzero, map_zero])
  have : p = p - q := by rw [hq0]; simp
  rw [this]
  exact hr

/-- If every graded component of the PBW map is injective, then symmetrization is injective on
each word-filtration step of the symmetric algebra, hence on the whole algebra. -/
private theorem pbwSymmetrizationMap_injective_of_forall
    (h : ∀ n, Function.Injective (pbwHomogeneousComponentMap R L n)) :
    Function.Injective (pbwSymmetrizationMap R L) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro p hp
  have hex : ∃ k, p ∈ F k :=
    TauCeti.Algebra.exists_mem_wordFiltration_of_iSup_eq_top _
      (top_unique ((iSup_homogeneousSubmodule_eq_top R L).symm.le.trans
        (iSup_le fun n => le_iSup_of_le n
          (TauCeti.Algebra.range_pow_le_wordFiltration (SymmetricAlgebra.ι R L) n)))) p
  obtain ⟨k, hk⟩ := hex
  induction k generalizing p with
  | zero =>
    have := mem_wordFiltrationPrevious_of_pbwSymmetrizationMap_eq_zero R L h hk hp
    simpa using this
  | succ k ih =>
    have := mem_wordFiltrationPrevious_of_pbwSymmetrizationMap_eq_zero R L h hk hp
    exact ih p hp (by simpa using this)

/-- Symmetrization is injective on a Lie algebra that is free as a module. -/
private theorem pbwSymmetrizationMap_injective_of_free [Module.Free R L] :
    Function.Injective (pbwSymmetrizationMap R L) :=
  pbwSymmetrizationMap_injective_of_forall R L (pbwHomogeneousComponentMap_injective R L)

/-- **PBW symmetrization is injective for every Lie algebra over a commutative `ℚ`-algebra**,
without any freeness or flatness assumption. -/
theorem pbwSymmetrizationMap_injective : Function.Injective (pbwSymmetrizationMap R L) := by
  -- Reduce to the free case along a surjection `π : F → L` from a Lie algebra free as a module:
  -- if the symmetrization of `a` vanishes, a lift `p` of `a` to `Sym(F)` symmetrizes into the
  -- kernel of `U(F) → U(L)`, which is the ideal generated by `ker π`; that ideal consists of
  -- symmetrizations of elements of the ideal of `Sym(F)` generated by `ker π`, so injectivity on
  -- `F` puts `p` in the kernel of `Sym(F) → Sym(L)`.
  obtain ⟨π, hπ⟩ := TauCeti.exists_lieHom_surjective_freeLieCover R L
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro a ha
  obtain ⟨p, rfl⟩ := SymmetricAlgebra.map_surjective R π.toLinearMap hπ a
  have hker : UniversalEnvelopingAlgebra.map R π
      (pbwSymmetrizationMap R (TauCeti.FreeLieCover R L) p) = 0 := by
    rw [map_pbwSymmetrizationMap]; exact ha
  rw [← RingHom.mem_ker, UniversalEnvelopingAlgebra.ker_map_of_surjective R π hπ] at hker
  obtain ⟨j, hj, hjp⟩ := envelopingIdeal_le_map_symmetrization π.ker hker
  have hpj := pbwSymmetrizationMap_injective_of_free R (TauCeti.FreeLieCover R L) hjp
  subst hpj
  rw [← RingHom.mem_ker, SymmetricAlgebra.ker_map_of_surjective π.toLinearMap hπ]
  exact hj

end TauCeti.UniversalEnvelopingAlgebra
