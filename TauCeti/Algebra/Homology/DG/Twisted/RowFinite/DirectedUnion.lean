/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Module.Right.Truncation
public import TauCeti.Algebra.Homology.DG.Twisted.RowFinite.DerivedTensor

/-!
# Twisted complexes of directed unions of DG modules

Let `m` be a row-finite twisting cocycle on a graded set `P`, so that every DG right module `M`
has the twisted complex `M ⊗_A K_m` (`TauCeti.RowFiniteTwistingCocycle.coefficientFunctor`) on the
finitely supported coefficient vectors `P →₀ M`. A coefficient vector has finitely many
coefficients, so the twisted complex of a directed union of sub-DG modules is the directed union
of their twisted complexes. Homology commutes with such unions, so a quasi-isomorphism can be
checked on the pieces:

* if `M` is the directed union of injective morphisms `N i ⟶ M`, a chain map between the twisted
  complexes of `M` for two cocycles is a quasi-isomorphism as soon as compatible chain maps between
  the twisted complexes of the `N i` are
  (`TauCeti.RowFiniteTwistingCocycle.quasiIso_of_forall_quasiIso_of_injective`).

Over a DG algebra concentrated in nonpositive cohomological degrees, such as the chains on Moore
loops, the canonical truncations `τ^{≤ k} M` (`TauCeti.DGRightModuleCat.truncLE`) are such a
directed union, and each has cohomology bounded above, that is, homology bounded below
(`TauCeti.DGRightModuleCat.cohomologyGrading_truncLE_eq_bot`). Hence:

* a chain map compatible with quasi-isomorphisms on the twisted complexes of all the truncations
  is a quasi-isomorphism (`TauCeti.RowFiniteTwistingCocycle.quasiIso_of_forall_quasiIso_truncLE`);
* a natural transformation between two twisted-complex functors that is a quasi-isomorphism on
  every DG module with cohomology bounded above is a quasi-isomorphism on every DG module
  (`TauCeti.RowFiniteTwistingCocycle.quasiIso_app_of_forall_cohomologyGrading_eq_bot`).

The last statement is how a comparison of twisted complexes proved through convergent spectral
sequences, which needs the homology of the coefficients bounded below, extends to arbitrary DG
local systems. Barraud–Damian–Humilière–Oancea prove their Viterbo isomorphism with DG
coefficients (Theorem K) for coefficients with homology bounded below and apply it to arbitrary
DG local systems in their Corollary 4.17; a comparison natural in the coefficients passes from the
first to the second in this way.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, Theorem K and Corollary 4.17.
-/

public section

open CategoryTheory

namespace TauCeti

namespace RowFiniteTwistingCocycle

universe uR uA uM uP uι

variable {R : Type uR} {A : Type uA} [CommRing R] [Ring A] [Algebra R A]
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {d : A →ₗ[R] A} {hA : IsDGAlgebra 𝒜 d}
  {P Q : Type uP} {indP : P → ℤ} {indQ : Q → ℤ}
  {mP : RowFiniteTwistingCocycle 𝒜 d P indP} {mQ : RowFiniteTwistingCocycle 𝒜 d Q indQ}

/-- **Quasi-isomorphisms of twisted complexes pass to directed unions of coefficient modules.**
Let `M` be the directed union of injective morphisms of DG right modules `j i : N i ⟶ M`: every
finite set of elements of `M` lies in the image of one `j i`. Let `φ` be a chain map from the
twisted complex of `M` for the cocycle `mP` to the one for `mQ`, and let `φ' i` be
quasi-isomorphisms between the twisted complexes of `N i` intertwined with `φ` by the
twisted-complex maps of `j i`. Then `φ` is a quasi-isomorphism. -/
theorem quasiIso_of_forall_quasiIso_of_injective {ι : Type uι}
    {M : DGRightModuleCat.{uR, uA, uM} hA}
    {N : ι → DGRightModuleCat.{uR, uA, uM} hA} (j : ∀ i, N i ⟶ M)
    (hj : ∀ i, Function.Injective (j i)) (hN : ∀ s : Finset M, ∃ i, ∀ x ∈ s, x ∈ Set.range (j i))
    (φ : (mP.coefficientFunctor hA).obj M ⟶ (mQ.coefficientFunctor hA).obj M)
    (φ' : ∀ i, (mP.coefficientFunctor hA).obj (N i) ⟶ (mQ.coefficientFunctor hA).obj (N i))
    (hφ' : ∀ i, QuasiIso (φ' i))
    (hcomm : ∀ i, φ' i ≫ (mQ.coefficientFunctor hA).map (j i) =
      (mP.coefficientFunctor hA).map (j i) ≫ φ) :
    QuasiIso φ := by
  classical
  refine HomologicalComplex.moduleCat_quasiIso_of_forall_exists φ φ' hφ'
    (fun i ↦ (mP.coefficientFunctor hA).map (j i)) (fun i ↦ (mQ.coefficientFunctor hA).map (j i))
    hcomm (fun i ↦ mP.injective_coefficientCochainComplexMap_f _ _ (hj i))
    (fun i ↦ mQ.injective_coefficientCochainComplexMap_f _ _ (hj i)) fun n p x y ↦ ?_
  -- The finitely many coefficients of `x` and of `y` lie in the image of one `j i`.
  set g : P →₀ M := (mP.coefficientCochainComplexXEquiv M.isDGRightModule n x : P →₀ M)
  set k : Q →₀ M := (mQ.coefficientCochainComplexXEquiv M.isDGRightModule p y : Q →₀ M)
  obtain ⟨i, hi⟩ := hN (g.support.image g ∪ k.support.image k)
  exact ⟨i, mP.exists_coefficientCochainComplexMap_f_eq _ _ (hj i) x fun z hz ↦
      hi _ (Finset.mem_union_left _ (Finset.mem_image_of_mem g hz)),
    mQ.exists_coefficientCochainComplexMap_f_eq _ _ (hj i) y fun z hz ↦
      hi _ (Finset.mem_union_right _ (Finset.mem_image_of_mem k hz))⟩

variable (h𝒜 : ∀ n, 0 < n → 𝒜 n = ⊥)

include h𝒜 in
/-- **Quasi-isomorphisms of twisted complexes pass from the truncations to the module.** Over a DG
algebra concentrated in nonpositive cohomological degrees, a chain map `φ` from the twisted complex
of a DG right module `M` for the cocycle `mP` to the one for `mQ` is a quasi-isomorphism as soon as
compatible chain maps between the twisted complexes of the canonical truncations `τ^{≤ k} M` are
quasi-isomorphisms for every `k`. -/
theorem quasiIso_of_forall_quasiIso_truncLE {M : DGRightModuleCat.{uR, uA, uM} hA}
    (φ : (mP.coefficientFunctor hA).obj M ⟶ (mQ.coefficientFunctor hA).obj M)
    (φ' : ∀ k, (mP.coefficientFunctor hA).obj (M.truncLE h𝒜 k) ⟶
      (mQ.coefficientFunctor hA).obj (M.truncLE h𝒜 k))
    (hφ' : ∀ k, QuasiIso (φ' k))
    (hcomm : ∀ k, φ' k ≫ (mQ.coefficientFunctor hA).map (M.ιTruncLE h𝒜 k) =
      (mP.coefficientFunctor hA).map (M.ιTruncLE h𝒜 k) ≫ φ) :
    QuasiIso φ :=
  quasiIso_of_forall_quasiIso_of_injective (M.ιTruncLE h𝒜)
    (fun k ↦ M.ιTruncLE_injective (h𝒜 := h𝒜) k)
    (fun s ↦ (M.exists_forall_mem_truncLESubmodule (h𝒜 := h𝒜) s).imp fun _ hk x hx ↦ by
      rw [DGRightModuleCat.range_ιTruncLE]
      exact hk x hx)
    φ φ' hφ' hcomm

include h𝒜 in
/-- **Twisted-complex comparisons extend from bounded-below to arbitrary coefficients.** Over a DG
algebra concentrated in nonpositive cohomological degrees, a natural transformation `α` between the
twisted-complex functors of two row-finite twisting cocycles which is a quasi-isomorphism on every
DG right module whose cohomology vanishes above some degree is a quasi-isomorphism on every DG
right module. -/
theorem quasiIso_app_of_forall_cohomologyGrading_eq_bot
    (α : mP.coefficientFunctor.{uR, uA, uM} hA ⟶ mQ.coefficientFunctor hA)
    (hα : ∀ N : DGRightModuleCat.{uR, uA, uM} hA,
      (∃ k, ∀ p, k < p → N.isDGRightModule.cohomologyGrading p = ⊥) → QuasiIso (α.app N))
    (M : DGRightModuleCat.{uR, uA, uM} hA) :
    QuasiIso (α.app M) :=
  quasiIso_of_forall_quasiIso_truncLE h𝒜 (α.app M) (fun k ↦ α.app (M.truncLE h𝒜 k))
    (fun k ↦ hα _ ⟨k, fun _ hp ↦ M.cohomologyGrading_truncLE_eq_bot hp⟩)
    fun k ↦ (α.naturality (M.ιTruncLE h𝒜 k)).symm

end RowFiniteTwistingCocycle

end TauCeti
