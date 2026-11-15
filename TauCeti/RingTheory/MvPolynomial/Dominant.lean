/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Monad
public import Mathlib.RingTheory.AlgebraicIndependent.Defs
public import TauCeti.RingTheory.MvPolynomial.DirectionalOrder
public import TauCeti.RingTheory.MvPolynomial.Jacobian.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.FiniteStability
import Mathlib.RingTheory.Spectrum.Prime.Chevalley
import TauCeti.RingTheory.FiniteType.FaithfullyFlatPoints
import TauCeti.RingTheory.Spectrum.Prime.Topology
import TauCeti.Topology.Constructible.Basic

/-!
# Dominant polynomial maps

Let `p : ι → R[X_j : j ∈ σ]` be a polynomial map, and suppose that its Jacobian matrix
`TauCeti.jacobiMatrixAt p v` is surjective at one point `v`. Then the components of `p` are
algebraically independent: no nonzero polynomial `q` in the variables `ι` satisfies `q(p) = 0`.
This holds over every commutative ring. Over an infinite domain, where polynomials are determined
by their values, it says that a polynomial vanishing on the image of `p` is zero, so the image of
`p` is Zariski dense.

This is the density statement behind the injectivity half of Chevalley's restriction theorem: an
invariant polynomial function on a semisimple Lie algebra that vanishes on a Cartan subalgebra
vanishes on the image of a polynomial parametrization of conjugates of the Cartan subalgebra whose
differential is surjective at a regular point, and is therefore zero.

Over an algebraically closed field, a dominant polynomial map is more than Zariski dense: its image
contains a nonempty principal open set. By Chevalley's theorem
(`PrimeSpectrum.isConstructible_comap_image`) the image of `Spec K[X_j] → Spec K[Y_i]` is
constructible, and it is dense because the pullback `aeval p` is injective, so it contains a
nonempty basic open set `D(g)`. The Nullstellensatz then lifts each closed point of `D(g)` to a
`K`-point. Applied to the polynomial parametrizations of the conjugates of two Cartan subalgebras,
this gives a point common to both families of conjugates, which is how Cartan subalgebras are shown
to be conjugate.

## Main results

* `TauCeti.algebraicIndependent_of_mulVec_surjective_jacobiMatrixAt`: a polynomial family whose
  Jacobian matrix is surjective at some point is algebraically independent.
* `TauCeti.eq_zero_of_forall_eval_eq_zero_of_mulVec_surjective_jacobiMatrixAt`: over an infinite
  domain, a polynomial vanishing on the image of such a polynomial map is zero.
* `AlgebraicIndependent.exists_ne_zero_setOf_eval_ne_zero_subset_range`: over an algebraically
  closed field, the image of a polynomial map with algebraically independent components contains
  the complement of the zero locus of a nonzero polynomial.

## References

* The Stacks Project, Tag 00FV, *Hilbert Nullstellensatz*.
-/

public section

namespace TauCeti

open MvPolynomial Matrix

variable {R σ ι : Type*} [CommRing R]

/-- **A polynomial family whose Jacobian matrix is surjective at a point is algebraically
independent.** If the Jacobian matrix of `p : ι → R[X_j : j ∈ σ]` is surjective at one point `v`,
then a polynomial `q` in the variables `ι` with `q(p) = 0` is zero. -/
theorem algebraicIndependent_of_mulVec_surjective_jacobiMatrixAt [Fintype σ] [Finite ι]
    {p : ι → MvPolynomial σ R} {v : σ → R} (hJ : (jacobiMatrixAt p v).mulVec.Surjective) :
    AlgebraicIndependent R p := by
  classical
  cases nonempty_fintype ι
  refine algebraicIndependent_iff.2 fun q hq ↦ ?_
  by_contra hq0
  -- Taylor-expand `q` at the image point `b = p(v)`, and let `q_k` be its lowest nonzero
  -- homogeneous component.
  set b : ι → R := fun i ↦ eval v (p i)
  obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.1 (orderAt_eq_top_iff.not.2 hq0 : q.orderAt b ≠ ⊤)
  have hqk : homogeneousComponent k (taylor b q) ≠ 0 :=
    homogeneousComponent_ne_zero_of_orderAt_eq q b hk.symm
  -- In Taylor coordinates the map fixes the origin and its linear part is the Jacobian matrix
  -- `J`, so the degree-`k` component of `q(p)`, which vanishes, is `q_k(J Y)`.
  set J := jacobiMatrixAt p v
  set L : ι → MvPolynomial σ R := fun i ↦ ∑ j, J i j • X j
  have hzero : aeval L (homogeneousComponent k (taylor b q)) = 0 := by
    have h := homogeneousComponent_aeval_of_le_order (hk.trans (orderAt_def q b)).le
      (h := fun i ↦ taylor v (p i) - C (b i)) fun i ↦ by simp [b]
    rw [← taylor_aeval, hq, map_zero, map_zero] at h
    simpa [L, J, homogeneousComponent_one_taylor, homogeneousComponent_eq_zero] using h.symm
  -- A right inverse `B` of `J` gives a linear substitution undoing `Y ↦ J Y`, so `q_k = 0`.
  obtain ⟨B, hB⟩ := mulVec_surjective_iff_exists_right_inverse.1 hJ
  have hinv : (aeval fun j ↦ ∑ i, B j i • X i).comp (aeval L) = AlgHom.id R _ := by
    rw [comp_aeval, ← aeval_X_left]
    congr 1
    funext i
    simp only [L, map_sum, map_smul, aeval_X, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp [← Finset.sum_smul, ← Matrix.mul_apply, hB, Matrix.one_apply]
  have h := DFunLike.congr_fun hinv (homogeneousComponent k (taylor b q))
  rw [AlgHom.comp_apply, hzero, map_zero, AlgHom.id_apply] at h
  exact hqk h.symm

/-- **A polynomial vanishing on the image of a polynomial map with surjective differential at a
point is zero.** Over an infinite domain, if `q(p(x)) = 0` at every point `x` and the Jacobian
matrix of `p` is surjective at one point `v`, then `q = 0`. -/
theorem eq_zero_of_forall_eval_eq_zero_of_mulVec_surjective_jacobiMatrixAt [IsDomain R]
    [Infinite R] [Fintype σ] [Finite ι] {p : ι → MvPolynomial σ R} {v : σ → R}
    (hJ : (jacobiMatrixAt p v).mulVec.Surjective) {q : MvPolynomial ι R}
    (hq : ∀ x : σ → R, eval (fun i ↦ eval x (p i)) q = 0) : q = 0 := by
  refine (algebraicIndependent_of_mulVec_surjective_jacobiMatrixAt hJ).eq_zero_of_aeval_eq_zero q
    (MvPolynomial.funext fun x ↦ ?_)
  rw [map_zero, aeval_eq_bind₁, ← hq x]
  simpa only [aeval_eq_eval] using aeval_bind₁ x p q

end TauCeti

namespace AlgebraicIndependent

open MvPolynomial

variable {K σ ι : Type*} [Field K] [IsAlgClosed K]

/-- **The image of a dominant polynomial map contains a nonempty principal open set.** Over an
algebraically closed field `K`, if the components of `p : ι → K[X_j : j ∈ σ]` are algebraically
independent, then there is a nonzero polynomial `g` in the variables `ι` such that every point
`y` with `g(y) ≠ 0` is a value `p(x)` of the polynomial map `p`. -/
theorem exists_ne_zero_setOf_eval_ne_zero_subset_range [Finite σ] [Finite ι]
    {p : ι → MvPolynomial σ K} (hp : AlgebraicIndependent K p) :
    ∃ g : MvPolynomial ι K, g ≠ 0 ∧
      {y | eval y g ≠ 0} ⊆ Set.range fun x i ↦ eval x (p i) := by
  set f : MvPolynomial ι K →ₐ[K] MvPolynomial σ K := aeval p
  have hft : f.FiniteType :=
    RingHom.FiniteType.of_comp_finiteType (f := algebraMap K _) (g := f.toRingHom)
      (f.comp_algebraMap.symm ▸ RingHom.finiteType_algebraMap.mpr inferInstance)
  -- Chevalley: the spectral image is constructible; it is dense, so it has dense interior
  have hU := (PrimeSpectrum.isConstructible_range_comap
    (RingHom.FinitePresentation.of_finiteType.mp hft)).dense_interior
      (RingHom.denseRange_comap_of_injective f.toRingHom hp)
  obtain ⟨P₀, hP₀⟩ := hU.nonempty
  obtain ⟨_, ⟨g, rfl⟩, hP₀g, hg⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hP₀ isOpen_interior
  refine ⟨g, fun h ↦ hP₀g (by simp [h]), fun y hy ↦ ?_⟩
  -- the closed point `y` lies in `D(g)`, hence in the image, and then lifts to a `K`-point
  have hyg : (⟨RingHom.ker (aeval y : _ →ₐ[K] K).toRingHom, RingHom.ker_isPrime _⟩ :
      PrimeSpectrum (MvPolynomial ι K)) ∈ PrimeSpectrum.basicOpen g := by
    simpa using hy
  obtain ⟨P, hP⟩ := interior_subset (hg hyg)
  obtain ⟨q, hq⟩ := AlgHom.exists_comp_eq_of_comap_eq_ker f hft (aeval y) P hP
  refine ⟨q ∘ X, funext fun i ↦ ?_⟩
  have hqi := DFunLike.congr_fun hq (X i)
  rw [AlgHom.comp_apply, aeval_X, aeval_X, aeval_unique q] at hqi
  simpa using hqi

end AlgebraicIndependent
