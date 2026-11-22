/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import TauCeti.AlgebraicGeometry.Cohomology.Biproduct
public import TauCeti.AlgebraicGeometry.Cohomology.ClosedImmersion.Linear
public import TauCeti.AlgebraicGeometry.Modules.Clopen
public import TauCeti.AlgebraicGeometry.Morphisms.ClosedImmersion.Basic

/-!
# Cohomology of a finite clopen partition

For a finite disjoint clopen cover `U` of a scheme `X`, the restriction units identify a module
`M` with the finite direct sum of the pushforwards of `M|U i`. Finite-biproduct cohomology and
the closed-immersion comparison therefore identify `Hⁿ(X, M)` with `∏ i, Hⁿ(U i, M|U i)`,
linearly over any base ring and naturally in `M`. No coherence or properness assumption is needed.

This comparison reduces cohomology computations to the members of a finite clopen partition.
When the cohomologies are finite-dimensional, their dimensions and truncated Euler
characteristics add over the partition.
-/

public section

open CategoryTheory Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules
open TauCeti TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme.Modules
open scoped Function

universe u

noncomputable section

variable {X : Scheme.{u}} {J : Type u} [Fintype J] (U : J → X.Opens)

/-- Finite products of modules supply the biproducts used by the clopen comparison. -/
local instance TauCeti.AlgebraicGeometry.Scheme.Modules.hasFiniteBiproducts_clopenCover :
    HasFiniteBiproducts X.Modules := .of_hasFiniteProducts

/-- Cohomology over a base ring decomposes as the finite product of the cohomologies on a
clopen partition, for arbitrary coefficient sheaves. -/
def TauCeti.AlgebraicGeometry.Scheme.Modules.cohomologyClopenCoverLinearEquiv
    (R : Type u) [CommRing R] [X.Over (Spec (.of R))]
    (hcover : ⨆ j, U j = ⊤) (hdisj : Pairwise (Disjoint on U))
    (M : X.Modules) (n : ℕ) :
    Cohomology M n ≃ₗ[R] ∀ j, Cohomology ((restrictFunctor (U j).ι).obj M) n := by
  have (j : J) := isClosedImmersion_ι_of_pairwiseDisjoint_iSup_eq_top U hcover hdisj j
  exact (cohomologyBaseLinearEquivOfIso R (clopenCoverCoefficientIso U hcover hdisj M) n).trans
    ((cohomologyBiproductLinearEquiv R
        (fun j ↦ (pushforward (U j).ι).obj ((restrictFunctor (U j).ι).obj M)) n).trans
      (LinearEquiv.piCongrRight fun j ↦
        (U j).ι.cohomologyPushforwardBaseLinearEquiv R ((restrictFunctor (U j).ι).obj M) n))


variable (R : Type u) [CommRing R] [X.Over (Spec (.of R))]
  (hcover : ⨆ j, U j = ⊤) (hdisj : Pairwise (Disjoint on U))

/-- The component of the clopen-cover comparison is the cohomology of the restriction unit,
followed by the closed-immersion comparison. -/
@[simp]
theorem TauCeti.AlgebraicGeometry.Scheme.Modules.cohomologyClopenCoverLinearEquiv_apply
    (M : X.Modules) (n : ℕ)
    (x : Cohomology M n) (j : J) :
    letI := isClosedImmersion_ι_of_pairwiseDisjoint_iSup_eq_top U hcover hdisj j
    cohomologyClopenCoverLinearEquiv U R hcover hdisj M n x j =
      (U j).ι.cohomologyPushforwardBaseLinearEquiv R ((restrictFunctor (U j).ι).obj M) n
        (cohomologyMapBaseLinear R X ((restrictAdjunction (U j).ι).unit.app M) n x) := by
  dsimp only [cohomologyClopenCoverLinearEquiv, LinearEquiv.trans_apply]
  rw [LinearEquiv.piCongrRight_apply,
    cohomologyBiproductLinearEquiv_apply, cohomologyBaseLinearEquivOfIso_apply]
  congr 1
  rw [← LinearMap.comp_apply, ← cohomologyMapBaseLinear_comp,
    clopenCoverCoefficientIso_hom_π]

/-- The clopen-cover comparison commutes with every map of coefficient sheaves. -/
theorem
  TauCeti.AlgebraicGeometry.Scheme.Modules.cohomologyClopenCoverLinearEquiv_naturality
    {M N : X.Modules}
    (f : M ⟶ N) (n : ℕ)
    (x : Cohomology M n) (j : J) :
    cohomologyClopenCoverLinearEquiv U R hcover hdisj N n
        (cohomologyMapBaseLinear R X f n x) j =
      cohomologyMapBaseLinear R (U j).toScheme ((restrictFunctor (U j).ι).map f) n
        (cohomologyClopenCoverLinearEquiv U R hcover hdisj M n x j) := by
  rw [cohomologyClopenCoverLinearEquiv_apply, cohomologyClopenCoverLinearEquiv_apply,
    ← Scheme.Hom.cohomologyPushforwardBaseLinearEquiv_naturality]
  congr 1
  have hu : f ≫ (restrictAdjunction (U j).ι).unit.app N =
      (restrictAdjunction (U j).ι).unit.app M ≫
        (pushforward (U j).ι).map ((restrictFunctor (U j).ι).map f) :=
    (restrictAdjunction (U j).ι).unit.naturality f
  have h := congrArg (fun φ : M ⟶ (pushforward (U j).ι).obj
    ((restrictFunctor (U j).ι).obj N) ↦ cohomologyMapBaseLinear R X φ n x) hu
  have hf := LinearMap.congr_fun (cohomologyMapBaseLinear_comp R X f
    ((restrictAdjunction (U j).ι).unit.app N) n) x
  have hg := LinearMap.congr_fun (cohomologyMapBaseLinear_comp R X
    ((restrictAdjunction (U j).ι).unit.app M)
    ((pushforward (U j).ι).map ((restrictFunctor (U j).ι).map f)) n) x
  exact hf.symm.trans (h.trans hg)

/-- A finite clopen partition with finite-dimensional component cohomologies gives the sum of
their dimensions in each degree. -/
theorem TauCeti.AlgebraicGeometry.Scheme.Modules.finrank_cohomology_eq_sum_clopenCover
    (k : Type u) [Field k]
    [X.Over (Spec (.of k))] (hcover : ⨆ j, U j = ⊤)
    (hdisj : Pairwise (Disjoint on U)) (M : X.Modules) (n : ℕ)
    [∀ j, FiniteDimensional k (Cohomology ((restrictFunctor (U j).ι).obj M) n)] :
    Module.finrank k (Cohomology M n) =
      ∑ j, Module.finrank k (Cohomology ((restrictFunctor (U j).ι).obj M) n) :=
  (cohomologyClopenCoverLinearEquiv U k hcover hdisj M n).finrank_eq.trans
    (Module.finrank_pi_fintype k)

/-- Truncated Euler characteristic is additive over a finite clopen partition when the
cohomologies of its members below the truncation are finite-dimensional. -/
theorem TauCeti.AlgebraicGeometry.Scheme.Modules.eulerCharBelow_eq_sum_clopenCover
    (k : Type u) [Field k] [X.Over (Spec (.of k))]
    (hcover : ⨆ j, U j = ⊤) (hdisj : Pairwise (Disjoint on U))
    (M : X.Modules) (n : ℕ)
    (hfin : ∀ i < n, ∀ j, FiniteDimensional k
      (Cohomology ((restrictFunctor (U j).ι).obj M) i)) :
    eulerCharBelow k X M n = ∑ j, eulerCharBelow k (U j).toScheme
      ((restrictFunctor (U j).ι).obj M) n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have (j : J) := hfin n n.lt_succ_self j
    rw [eulerCharBelow_succ, ih (fun i hi ↦ hfin i (hi.trans n.lt_succ_self)),
      finrank_cohomology_eq_sum_clopenCover U k hcover hdisj]
    simp_rw [eulerCharBelow_succ]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Nat.cast_sum]
