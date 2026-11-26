/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Cubical.MonoidAlgebra.ContinuationChainSystem
public import TauCeti.AlgebraicTopology.Singular.Cubical.MonoidAlgebra.RepresentingChainSystem
import TauCeti.Algebra.Homology.DG.Twisted.Invertible
import TauCeti.Algebra.Ring.NegOnePow
import TauCeti.Topology.ContinuousMap.CodRestrict

/-!
# Homotopies of twisting and continuation chain systems

Let `S` and `S'` be twisting chain systems (`TauCeti.TwistingChainSystem`) on the same spaces
`M x y` with the same composition maps `ι`, for instance two representing chain systems of the
compactified trajectory spaces of one Morse function. A **homotopy** from `S` to `S'`
(`TauCeti.TwistingChainSystem.Homotopy`) is a family of normalized cubical chains `h x y` of
`M x y`, of dimension `ind x - ind y` (cohomological degree `ind y - ind x`), satisfying

`∂ h x y = s x y - s' x y + Σ_z ι_* (s x z × h z y)
  + Σ_z (-1) ^ (ind x - ind z - 1) • ι_* (h x z × s' z y)`.

The last two terms form the continuation sum `TauCeti.continuationChainSum` of `h`. This is the
continuation equation for the constant homotopy of Morse functions, whose continuation
trajectories from `x` to `y ≠ x` are the trajectories of `M x y` together with a time parameter;
the identity matrix accounts for the stationary trajectories from `x` to itself.

For evaluation maps `q` into a topological monoid `G` which are multiplicative along `ι`, the
matrix `1 + q_* h` is then a continuation cocycle from the twisting cocycle of `S` to that of
`S'` (`TauCeti.TwistingChainSystem.Homotopy.continuationCocycle`), with values in the
differential graded algebra `C^□_*(G; R)`. For the Moore loops of the base, this compares the
Barraud–Cornea cocycles of the two representing chain systems.

Any two representing chain systems of the same classes are joined by a homotopy
(`TauCeti.TwistingChainSystem.IsRepresenting.nonempty_homotopy`), provided that the composition
maps are associative and take values in the subspaces `A x y`, and that the maps
`H_{ind x - ind y - 1}(M x y) → H_{ind x - ind y - 1}(M x y, A x y)` are injective. For a compact
manifold `M x y` of dimension `ind x - ind y - 1` with boundary `A x y` the last condition holds
because the boundary has no homology in that degree. The chains are constructed by induction on
`ind x - ind y`: the right-hand side of the homotopy equation is a cycle once the equation holds
at the pairs of smaller index difference
(`TauCeti.TwistingChainSystem.cubicalChainDifferential_sub_add_continuationChainSum`), and its
relative class is `μ x y - μ x y = 0`, since the continuation sum lies in `A x y`; injectivity
makes it a boundary (`TauCeti.exists_forall_cubicalChainDifferential_eq_of_injective`).

The same argument compares two continuation chain systems `T₀` and `T₁` from `S` to `S'`
(`TauCeti.ContinuationChainSystem`) on the spaces `N x y` of continuation trajectories. Let `s`,
`s'`, `t₀` and `t₁` denote the chains of `S`, `S'`, `T₀` and `T₁`. If `T₀` and `T₁` both
represent the same classes `ν x y ∈ H_{ind x - indQ y}(N x y, B x y)`, they are joined by a
parametrized chain system (`TauCeti.ParametrizedChainSystem`) on the spaces `N x y` themselves,
included by the identities
(`TauCeti.ContinuationChainSystem.IsRepresenting.nonempty_parametrizedChainSystem`): chains
`h x y` of dimension `ind x - indQ y + 1` with

`∂ h x y = t₁ x y - t₀ x y + Σ_z (-1) ^ (ind x - ind z) • κ_* (s x z × h z y)
  + Σ_z (-1) ^ (ind x - indQ z) • κ'_* (h x z × s' z y)`.

The right-hand side is a cycle once the equation holds at the pairs of smaller index difference
(`TauCeti.cubicalChainDifferential_parametrizedChainSum`), its relative class is
`ν x y - ν x y = 0`, and injectivity of
`H_{ind x - indQ y}(N x y) → H_{ind x - indQ y}(N x y, B x y)` makes it a boundary. Pushed
forward along multiplicative evaluation maps, this is a parametrized cocycle between the
continuation cocycles of `T₀` and `T₁`
(`TauCeti.ContinuationChainSystem.IsRepresenting.nonempty_parametrizedCocycle`), so the
continuation maps of twisted complexes that the two systems induce are chain homotopic
(`TauCeti.ParametrizedCocycle.homotopy`): for a homotopy of Morse functions whose continuation
trajectory spaces satisfy these hypotheses, the continuation morphism does not depend on the
representing chain system of its continuation trajectories.

## Main definitions

* `TauCeti.TwistingChainSystem.Homotopy`: a homotopy of twisting chain systems.
* `TauCeti.TwistingChainSystem.Homotopy.refl`: the zero homotopy from a chain system to itself.
* `TauCeti.TwistingChainSystem.Homotopy.continuationCocycle`: the continuation cocycle `1 + q_* h`
  of push-forwards.

## Main results

* `TauCeti.TwistingChainSystem.cubicalChainDifferential_sub_add_continuationChainSum`: the
  right-hand side of the homotopy equation is a cycle.
* `TauCeti.TwistingChainSystem.IsRepresenting.nonempty_homotopy`: two representing chain systems of
  the same classes are joined by a homotopy.
* `TopPair.injective_homologyMap_cokernel_π_of_isZero`: the injectivity hypothesis of
  `nonempty_homotopy` holds when the subspace has no homology in the relevant degree.
* `TauCeti.TwistingChainSystem.Homotopy.isUnit_continuationCocycle`: the continuation cocycle of a
  homotopy whose chains vanish on the pairs of equal index is invertible.
* `TauCeti.ContinuationChainSystem.IsRepresenting.nonempty_parametrizedChainSystem`: two
  representing continuation chain systems of the same classes are joined by a parametrized chain
  system.
* `TauCeti.ContinuationChainSystem.IsRepresenting.nonempty_parametrizedCocycle`: so their
  continuation cocycles are joined by a parametrized cocycle.

## References

* J.-F. Barraud, O. Cornea, *Lagrangian intersections and the Serre spectral sequence*, Ann. of
  Math. 166 (2007), 657–722, Section 2 and Appendix A.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, Chapters 5 and 6.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §1.4.
-/

public section

noncomputable section

open CategoryTheory Limits

universe u

namespace TauCeti

open NormalizedCubicalChain

section Homotopy

variable {P : Type*} [Fintype P] {ind : P → ℤ} {M : P → P → Type*}
  [∀ x y, TopologicalSpace (M x y)] {ι : ∀ x y z, C(M x y × M y z, M x z)} {R : Type*}
  [CommRing R]

namespace TwistingChainSystem

/-- A **homotopy** from the twisting chain system `S` to the twisting chain system `S'` on the
same spaces: chains `h x y` of `M x y`, of cohomological degree `ind y - ind x`, satisfying
`∂ h x y = s x y - s' x y + Σ_z ι_* (s x z × h z y)
  + Σ_z (-1) ^ (ind x - ind z - 1) • ι_* (h x z × s' z y)`,
the continuation equation for the constant homotopy. -/
structure Homotopy (S S' : TwistingChainSystem ind ι R) where
  /-- The chain of the space `M x y`. -/
  chain : ∀ x y, normalizedCubicalChainAlgebra (M x y) R
  /-- Each chain is homogeneous, of cohomological degree `ind y - ind x`. -/
  mem_graded : ∀ x y, chain x y ∈ cubicalChainGrading (M x y) R (ind y - ind x)
  /-- The homotopy equation. -/
  homotopy : ∀ x y, cubicalChainDifferential (M x y) R (chain x y) =
    S.chain x y - S'.chain x y + continuationChainSum ind ind ι ι R S.chain S'.chain chain x y

namespace Homotopy

variable {S S' : TwistingChainSystem ind ι R}

@[ext]
theorem ext {T₁ T₂ : S.Homotopy S'} (h : ∀ x y, T₁.chain x y = T₂.chain x y) : T₁ = T₂ := by
  cases T₁; cases T₂
  congr
  funext x y
  exact h x y

/-- The chain of `(x, y)` vanishes when `ind x < ind y`. -/
theorem chain_eq_zero_of_lt (T : S.Homotopy S') {x y : P} (hxy : ind x < ind y) :
    T.chain x y = 0 :=
  eq_zero_of_mem_cubicalChainGrading_of_pos _ _ (by omega) (T.mem_graded x y)

variable (S) in
/-- The **zero homotopy** from a twisting chain system to itself. -/
def refl : S.Homotopy S where
  chain _ _ := 0
  mem_graded _ _ := zero_mem _
  homotopy x y := by simp [continuationChainSum_def]

@[simp]
theorem refl_chain (x y : P) : (refl S).chain x y = 0 :=
  (rfl)

end Homotopy

/-- **The right-hand side of the homotopy equation is a cycle.** Let the composition maps be
associative, `ι (ι (a, b), c) = ι (a, ι (b, c))`, and let `h` be a family of chains of
cohomological degrees `ind y - ind x` satisfying the homotopy equation from `S` to `S'` at the
pairs `(z, y)` and `(x, z)` for every `z` whose index lies strictly between those of `y` and `x`.
Then `s x y - s' x y` plus the continuation sum of `h` at `(x, y)` is a cycle. -/
theorem cubicalChainDifferential_sub_add_continuationChainSum (S S' : TwistingChainSystem ind ι R)
    {h : ∀ x y, normalizedCubicalChainAlgebra (M x y) R}
    (hh : ∀ x y, h x y ∈ cubicalChainGrading (M x y) R (ind y - ind x)) {x y : P}
    (hι : ∀ w z (a : M x w) (b : M w z) (c : M z y),
      ι x z y (ι x w z (a, b), c) = ι x w y (a, ι w z y (b, c)))
    (hl : ∀ z, ind y < ind z → ind z < ind x → cubicalChainDifferential (M z y) R (h z y) =
      S.chain z y - S'.chain z y + continuationChainSum ind ind ι ι R S.chain S'.chain h z y)
    (hr : ∀ z, ind y < ind z → ind z < ind x → cubicalChainDifferential (M x z) R (h x z) =
      S.chain x z - S'.chain x z + continuationChainSum ind ind ι ι R S.chain S'.chain h x z) :
    cubicalChainDifferential (M x y) R
      (S.chain x y - S'.chain x y + continuationChainSum ind ind ι ι R S.chain S'.chain h x y) =
        0 := by
  -- The error terms `s - s'` of the continuation equation contribute `-∂ s + ∂ s'`.
  have hσ (z : P) : (ind z - ind x + 1).negOnePow = -(ind x - ind z).negOnePow :=
    Int.negOnePow_eq_neg_of_odd_sub ⟨ind z - ind x, by ring⟩
  have hε (z : P) : (ind x - ind z - 1).negOnePow = -(ind x - ind z).negOnePow :=
    Int.negOnePow_eq_neg_of_odd_sub ⟨-1, by ring⟩
  rw [map_add, map_sub, S.twisting, S'.twisting,
    cubicalChainDifferential_continuationChainSum_of_eq_add S S'
      (e := fun x y ↦ S.chain x y - S'.chain x y) hh
      (fun x y ↦ sub_mem (S.mem_graded x y) (S'.mem_graded x y)) hι hι hι hl hr]
  simp only [twistingChainSum_def, map_sub, LinearMap.sub_apply, smul_sub, Finset.sum_sub_distrib,
    hσ, hε, Units.neg_smul, Finset.sum_neg_distrib]
  abel

/-! ### The continuation cocycle of a homotopy -/

section Evaluation

variable {G : Type*} [Monoid G] [TopologicalSpace G] [ContinuousMul G] {q : ∀ x y, C(M x y, G)}
  {S S' : TwistingChainSystem ind ι R}

namespace Homotopy

variable [DecidableEq P]

variable (q) in
/-- **The continuation cocycle of a homotopy** of twisting chain systems: for evaluation maps
`q x y : M x y → G` into a topological monoid that are multiplicative,
`q x y (ι x z y (u, v)) = q x z u * q z y v`, the matrix `1 + q_* h` is a continuation cocycle from
the twisting cocycle of push-forwards of `S` to that of `S'`. -/
def continuationCocycle (T : S.Homotopy S')
    (hq : ∀ x z y (u : M x z) (v : M z y), q x y (ι x z y (u, v)) = q x z u * q z y v) :
    ContinuationCocycle (S.twistingCocycle q hq) (S'.twistingCocycle q hq) where
  ν x y := (1 : Matrix P P (normalizedCubicalChainAlgebra G R)) x y +
    cubicalChainSumMap R (q x y) (T.chain x y)
  mem_graded x y := by
    refine add_mem ?_ (cubicalChainSumMap_mem _ (T.mem_graded x y))
    -- `TauCeti.kronecker_mem_graded` does not apply: `cubicalChainGrading` consists of submodules
    -- for the module structure of the direct sum, not the one coming from the algebra structure.
    rw [Matrix.one_apply]
    split_ifs with hxy
    · subst hxy
      rw [sub_self]
      exact SetLike.one_mem_graded _
    · exact zero_mem _
  continuation x y := by
    -- The Kronecker matrix is a cycle, and contributes `m x y - m' x y` to the right-hand side.
    have hd : cubicalChainDifferential G R
        ((1 : Matrix P P (normalizedCubicalChainAlgebra G R)) x y) = 0 := by
      rw [Matrix.one_apply]
      split_ifs
      · exact (cubicalChain_isDGAlgebra G R).map_one_eq_zero
      · exact map_zero _
    have hl : ∑ z, cubicalChainSumMap R (q x z) (S.chain x z) *
        (1 : Matrix P P (normalizedCubicalChainAlgebra G R)) z y =
          cubicalChainSumMap R (q x y) (S.chain x y) := by
      simp [Matrix.one_apply]
    have hr : ∑ z, (ind x - ind z - 1).negOnePow •
        ((1 : Matrix P P (normalizedCubicalChainAlgebra G R)) x z *
          cubicalChainSumMap R (q z y) (S'.chain z y)) =
          -cubicalChainSumMap R (q x y) (S'.chain x y) := by
      simp [Matrix.one_apply]
    rw [map_add, hd, zero_add, cubicalChainDifferential_cubicalChainSumMap, T.homotopy, map_add,
      map_sub, cubicalChainSumMap_continuationChainSum (hq x · y) (hq x · y)]
    simp only [twistingCocycle_m, mul_add, add_mul, smul_add, Finset.sum_add_distrib, hl, hr]
    abel

/-- The entries of the continuation cocycle of a homotopy are `1 + q_* h`. -/
@[simp]
theorem continuationCocycle_ν (T : S.Homotopy S')
    (hq : ∀ x z y (u : M x z) (v : M z y), q x y (ι x z y (u, v)) = q x z u * q z y v)
    (x y : P) :
    (T.continuationCocycle q hq).ν x y =
      (1 : Matrix P P (normalizedCubicalChainAlgebra G R)) x y +
        cubicalChainSumMap R (q x y) (T.chain x y) :=
  (rfl)

variable (S) in
/-- The continuation cocycle of the zero homotopy is the Kronecker cocycle. -/
@[simp]
theorem continuationCocycle_refl
    (hq : ∀ x z y (u : M x z) (v : M z y), q x y (ι x z y (u, v)) = q x z u * q z y v) :
    (refl S).continuationCocycle q hq =
      .refl (cubicalChain_isDGAlgebra G R).map_one_eq_zero _ := by
  ext x y
  simp

/-- **The continuation cocycle of a homotopy is invertible** when the chains of the homotopy
vanish on the pairs of equal index, for instance when the spaces `M x y` with `ind x = ind y` are
empty: the matrix `1 + q_* h` is then unitriangular for the ranking by `ind`. Through
`TauCeti.ContinuationCocycle.continuationIsoOfIsUnit`, the twisting cocycles of push-forwards of
`S` and `S'` then have isomorphic twisted complexes. -/
theorem isUnit_continuationCocycle (T : S.Homotopy S')
    (hq : ∀ x z y (u : M x z) (v : M z y), q x y (ι x z y (u, v)) = q x z u * q z y v)
    (hT : ∀ x y, ind x = ind y → T.chain x y = 0) :
    IsUnit (Matrix.of (T.continuationCocycle q hq).ν) :=
  (T.continuationCocycle q hq).isUnit_of_eq_one_of_le fun x y hxy ↦ by
    rw [continuationCocycle_ν, hxy.lt_or_eq.elim T.chain_eq_zero_of_lt (hT x y), map_zero,
      add_zero]

end Homotopy

end Evaluation

end TwistingChainSystem

end Homotopy

/-! ### Existence of homotopies between representing chain systems -/

/-- If the subspace has no cubical homology in degree `n`, the map `Hₙ(X) ⟶ Hₙ(X, A)` to relative
homology is injective, by the exact sequence of the pair. This is how the injectivity hypothesis
of `TauCeti.TwistingChainSystem.IsRepresenting.nonempty_homotopy` is met when the boundary `A x y`
of `M x y` has no homology in degree `ind x - ind y - 1`. -/
theorem _root_.TopPair.injective_homologyMap_cokernel_π_of_isZero {k : Type u} [Ring k]
    (P : TopPair.{u}) (n : ℕ)
    (h : IsZero (((normalizedCubicalChainComplex k).obj P.snd).homology n)) :
    Function.Injective (HomologicalComplex.homologyMap
      (cokernel.π ((normalizedCubicalChainComplex k).map P.map)) n).hom :=
  (ModuleCat.mono_iff_injective _).1 ((P.cubicalHomology_exact_space k n).mono_g (h.eq_of_src _ _))

section Existence

variable {P : Type*} [Fintype P] {ind : P → ℤ} {M : P → P → TopCat.{u}}
  {ι : ∀ x y z, C(M x y × M y z, M x z)} {k : Type u} [CommRing k] {A : ∀ x y, Set (M x y)}
  {μ : ∀ x y, ((TopPair.ofSubset (A x y)).cubicalChainComplex k).homology
    (ind x - ind y - 1).toNat}

namespace TwistingChainSystem

variable {S S' : TwistingChainSystem ind ι k}

/-- The continuation sum of a family of chains, for composition maps with values in the subspaces
`A x y`, is the push-forward of a chain of `A x y` of the same cohomological degree. -/
private theorem exists_continuationChainSum_eq_cubicalChainSumMap
    (hA : ∀ x z y p, ι x z y p ∈ A x y) {h : ∀ x y, normalizedCubicalChainAlgebra (M x y) k}
    (hh : ∀ x y, h x y ∈ cubicalChainGrading (M x y) k (ind y - ind x)) (x y : P) :
    ∃ b : normalizedCubicalChainAlgebra (A x y) k,
      b ∈ cubicalChainGrading (A x y) k (ind y - ind x + 1) ∧
      cubicalChainSumMap k (ContinuousMap.subtypeVal (A x y)) b =
        continuationChainSum ind ind ι ι k S.chain S'.chain h x y := by
  -- The composition maps, corestricted to the subspaces `A x y`.
  let ιA (z : P) := (ι x z y).codRestrict (A x y) (hA x z y)
  have hιA (z : P) : (ContinuousMap.subtypeVal (A x y)).comp (ιA z) = ι x z y :=
    ContinuousMap.subtypeVal_comp_codRestrict _ _ _
  refine ⟨∑ z, cubicalChainSumPairing k (ιA z) (S.chain x z) (h z y) +
    ∑ z, (ind x - ind z - 1).negOnePow • cubicalChainSumPairing k (ιA z) (h x z) (S'.chain z y),
    add_mem (Submodule.sum_mem _ fun z _ ↦ ?_) (Submodule.sum_mem _ fun z _ ↦ ?_), ?_⟩
  · have hdeg : ind z - ind x + 1 + (ind y - ind z) = ind y - ind x + 1 := by ring
    exact hdeg ▸ cubicalChainSumPairing_mem _ (S.mem_graded x z) (hh z y)
  · have hdeg : ind z - ind x + (ind y - ind z + 1) = ind y - ind x + 1 := by ring
    rw [Units.smul_def]
    exact zsmul_mem (hdeg ▸ cubicalChainSumPairing_mem _ (hh x z) (S'.mem_graded z y)) _
  · simp only [map_add, map_sum, map_zsmul_unit, cubicalChainSumMap_cubicalChainSumPairing, hιA,
      continuationChainSum_def]

/-- **Any two representing chain systems are homotopic.** Let `S` and `S'` be twisting chain
systems representing the same classes `μ x y` of `H_{ind x - ind y - 1}(M x y, A x y)`, for
associative composition maps `ι` with values in the subspaces `A x y`. If the maps
`H_{ind x - ind y - 1}(M x y) → H_{ind x - ind y - 1}(M x y, A x y)` are injective whenever
`ind y < ind x`, then there is a homotopy from `S` to `S'`.

For the compactified trajectory spaces of a Morse function, `M x y` is a compact manifold with
corners of dimension `ind x - ind y - 1` and boundary `A x y`, which has no homology in that
degree, so the injectivity holds. The push-forwards of the homotopy then relate the
Barraud–Cornea cocycles of `S` and `S'` by a continuation cocycle
(`TauCeti.TwistingChainSystem.Homotopy.continuationCocycle`). -/
theorem IsRepresenting.nonempty_homotopy (hS : S.IsRepresenting A μ)
    (hS' : S'.IsRepresenting A μ)
    (hι : ∀ x w z y (a : M x w) (b : M w z) (c : M z y),
      ι x z y (ι x w z (a, b), c) = ι x w y (a, ι w z y (b, c)))
    (hA : ∀ x z y p, ι x z y p ∈ A x y)
    (hinj : ∀ x y, ind y < ind x → Function.Injective (HomologicalComplex.homologyMap
      (cokernel.π ((normalizedCubicalChainComplex k).map (TopPair.ofSubset (A x y)).map))
        (ind x - ind y - 1).toNat).hom) :
    Nonempty (S.Homotopy S') := by
  -- The chain of `(x, y)` is a chain of `M x y` of cohomological degree `ind y - ind x`, whose
  -- boundary is a cycle `s x y - s' x y + b` with `b` a chain of `A x y`.
  obtain ⟨h, hh, hd⟩ := exists_forall_cubicalChainDifferential_eq_of_injective
    (deg := fun x y ↦ ind y - ind x) (n := fun x y ↦ (ind x - ind y - 1).toNat) (μ := μ)
    (F := fun h x y ↦ S.chain x y - S'.chain x y +
      continuationChainSum ind ind ι ι k S.chain S'.chain h x y)
    (fun x y hxy ↦ by omega)
    (fun h h' x y _ _ hhh' ↦ by
      rw [continuationChainSum_congr (ν' := h') S.mem_graded S'.mem_graded
        (fun z _ ↦ hhh' z y (by omega)) fun z _ ↦ hhh' x z (by omega)])
    (fun h x y hh hxy ↦ by
      rw [S.chain_eq_zero_of_le (by omega), S'.chain_eq_zero_of_le (by omega),
        continuationChainSum_eq_zero_of_le S.mem_graded S'.mem_graded hh (by omega), sub_self,
        add_zero])
    (fun x y hxy ↦ hinj x y (by omega)) fun h x y hxy hh hd ↦ by
    obtain ⟨b, hb, hbsum⟩ :=
      exists_continuationChainSum_eq_cubicalChainSumMap (S := S) (S' := S') hA hh x y
    have hdeg : ind y - ind x + 1 = -(((ind x - ind y - 1).toNat : ℕ) : ℤ) := by omega
    exact ⟨cubicalChainDifferential_sub_add_continuationChainSum S S' hh (hι x · · y)
      (fun z _ h₂ ↦ hd z y (by omega)) (fun z h₁ _ ↦ hd x z (by omega)), S.chain x y,
      S'.chain x y, b, (S.isRepresenting_iff μ).1 hS x y (by omega),
      (S'.isRepresenting_iff μ).1 hS' x y (by omega), hdeg ▸ hb, by rw [hbsum]⟩
  exact ⟨⟨h, hh, hd⟩⟩

end TwistingChainSystem

end Existence

/-! ### Parametrized chain systems between representing continuation chain systems -/

section ContinuationExistence

variable {P : Type*} [Fintype P] {ind : P → ℤ} {M : P → P → Type*}
  [∀ x y, TopologicalSpace (M x y)] {Q : Type*} [Fintype Q] {indQ : Q → ℤ} {M' : Q → Q → Type*}
  [∀ x y, TopologicalSpace (M' x y)] {N : P → Q → TopCat.{u}}
  {ι : ∀ x y z, C(M x y × M y z, M x z)} {ι' : ∀ x y z, C(M' x y × M' y z, M' x z)}
  {κ : ∀ x y z, C(M x y × N y z, N x z)} {κ' : ∀ x y z, C(N x y × M' y z, N x z)}
  {k : Type u} [CommRing k] {S : TwistingChainSystem ind ι k}
  {S' : TwistingChainSystem indQ ι' k} {T₀ T₁ : ContinuationChainSystem κ κ' S S'}
  {B : ∀ x y, Set (N x y)}
  {ν : ∀ x y, ((TopPair.ofSubset (B x y)).cubicalChainComplex k).homology (ind x - indQ y).toNat}

namespace ContinuationChainSystem

/-- The parametrized sum of a family of chains of the spaces `N x y` themselves, included by the
identities, for composition maps with values in the subspaces `B x y`: the difference of the
chains of `T₁` and `T₀` plus the push-forward of a chain of `B x y` of the same cohomological
degree. -/
private theorem exists_parametrizedChainSum_eq_sub_add (hB : ∀ x z y p, κ x z y p ∈ B x y)
    (hB' : ∀ x z y p, κ' x z y p ∈ B x y) {h : ∀ x y, normalizedCubicalChainAlgebra (N x y) k}
    (hh : ∀ x y, h x y ∈ cubicalChainGrading (N x y) k (indQ y - ind x - 1)) (x : P) (y : Q) :
    ∃ b : normalizedCubicalChainAlgebra (B x y) k,
      b ∈ cubicalChainGrading (B x y) k (indQ y - ind x) ∧
      parametrizedChainSum ind indQ κ κ' (fun x y ↦ ContinuousMap.id (N x y))
          (fun x y ↦ ContinuousMap.id (N x y)) k S.chain S'.chain T₀.chain T₁.chain h x y =
        T₁.chain x y - T₀.chain x y +
          cubicalChainSumMap k (ContinuousMap.subtypeVal (B x y)) b := by
  -- The composition maps, corestricted to the subspaces `B x y`.
  let κB (z : P) := (κ x z y).codRestrict (B x y) (hB x z y)
  let κB' (z : Q) := (κ' x z y).codRestrict (B x y) (hB' x z y)
  have hκB (z : P) : (ContinuousMap.subtypeVal (B x y)).comp (κB z) = κ x z y :=
    ContinuousMap.subtypeVal_comp_codRestrict _ _ _
  have hκB' (z : Q) : (ContinuousMap.subtypeVal (B x y)).comp (κB' z) = κ' x z y :=
    ContinuousMap.subtypeVal_comp_codRestrict _ _ _
  refine ⟨∑ z, (ind x - ind z).negOnePow • cubicalChainSumPairing k (κB z) (S.chain x z) (h z y) +
    ∑ z, (ind x - indQ z).negOnePow • cubicalChainSumPairing k (κB' z) (h x z) (S'.chain z y),
    add_mem (Submodule.sum_mem _ fun z _ ↦ ?_) (Submodule.sum_mem _ fun z _ ↦ ?_), ?_⟩
  · have hdeg : ind z - ind x + 1 + (indQ y - ind z - 1) = indQ y - ind x := by ring
    rw [Units.smul_def]
    exact zsmul_mem (hdeg ▸ cubicalChainSumPairing_mem _ (S.mem_graded x z) (hh z y)) _
  · have hdeg : indQ z - ind x - 1 + (indQ y - indQ z + 1) = indQ y - ind x := by ring
    rw [Units.smul_def]
    exact zsmul_mem (hdeg ▸ cubicalChainSumPairing_mem _ (hh x z) (S'.mem_graded z y)) _
  · simp only [parametrizedChainSum_def, cubicalChainSumMap_id, LinearMap.id_apply, map_add,
      map_sum, map_zsmul_unit, cubicalChainSumMap_cubicalChainSumPairing, hκB, hκB', add_assoc]

/-- **Any two representing continuation chain systems are joined by a parametrized chain
system.** Let `T₀` and `T₁` be continuation chain systems from `S` to `S'` representing the same
classes `ν x y` of `H_{ind x - indQ y}(N x y, B x y)`, for associative composition maps `κ` and
`κ'` with values in the subspaces `B x y`. If the maps
`H_{ind x - indQ y}(N x y) → H_{ind x - indQ y}(N x y, B x y)` are injective whenever
`indQ y ≤ ind x`, then there is a parametrized chain system from `T₀` to `T₁` on the spaces
`N x y` themselves, included by the identities.

For the compactified spaces of continuation trajectories of a homotopy of Morse functions,
`N x y` is a compact manifold with corners of dimension `ind x - indQ y` and boundary `B x y`,
which has no homology in that degree, so the injectivity holds. The push-forwards of the
parametrized chain system then relate the continuation cocycles of `T₀` and `T₁` by a
parametrized cocycle
(`TauCeti.ContinuationChainSystem.IsRepresenting.nonempty_parametrizedCocycle`), so the
continuation maps of the two systems are chain homotopic: for continuation trajectory spaces
satisfying these hypotheses, the induced continuation map does not depend on the choice of
representing continuation chain system. -/
theorem IsRepresenting.nonempty_parametrizedChainSystem (hT₀ : T₀.IsRepresenting B ν)
    (hT₁ : T₁.IsRepresenting B ν)
    (hκ : ∀ x w z y (a : M x w) (b : M w z) (c : N z y),
      κ x z y (ι x w z (a, b), c) = κ x w y (a, κ w z y (b, c)))
    (hκκ' : ∀ x w z y (a : M x w) (b : N w z) (c : M' z y),
      κ' x z y (κ x w z (a, b), c) = κ x w y (a, κ' w z y (b, c)))
    (hκ' : ∀ x w z y (a : N x w) (b : M' w z) (c : M' z y),
      κ' x z y (κ' x w z (a, b), c) = κ' x w y (a, ι' w z y (b, c)))
    (hB : ∀ x z y p, κ x z y p ∈ B x y) (hB' : ∀ x z y p, κ' x z y p ∈ B x y)
    (hinj : ∀ x y, indQ y ≤ ind x → Function.Injective (HomologicalComplex.homologyMap
      (cokernel.π ((normalizedCubicalChainComplex k).map (TopPair.ofSubset (B x y)).map))
        (ind x - indQ y).toNat).hom) :
    Nonempty (ParametrizedChainSystem κ κ' (fun x y ↦ ContinuousMap.id (N x y))
      (fun x y ↦ ContinuousMap.id (N x y)) T₀ T₁) := by
  -- The chain of `(x, y)` is a chain of `N x y` of cohomological degree `indQ y - ind x - 1`,
  -- whose boundary is a cycle `t₁ x y - t₀ x y + b` with `b` a chain of `B x y`.
  obtain ⟨h, hh, hd⟩ := exists_forall_cubicalChainDifferential_eq_of_injective
    (deg := fun x y ↦ indQ y - ind x - 1) (n := fun x y ↦ (ind x - indQ y).toNat) (μ := ν)
    (F := parametrizedChainSum ind indQ κ κ' (fun x y ↦ ContinuousMap.id (N x y))
      (fun x y ↦ ContinuousMap.id (N x y)) k S.chain S'.chain T₀.chain T₁.chain)
    (fun x y hxy ↦ by omega)
    (fun h h' x y _ _ hhh' ↦ parametrizedChainSum_congr S.mem_graded S'.mem_graded
      (fun z _ ↦ hhh' z y (by omega)) fun z _ ↦ hhh' x z (by omega))
    (fun h x y hh hxy ↦ parametrizedChainSum_eq_zero_of_lt S.mem_graded S'.mem_graded
      T₀.mem_graded T₁.mem_graded hh (by omega))
    (fun x y hxy ↦ hinj x y (by omega)) fun h x y hxy hh hd ↦ by
    obtain ⟨b, hb, hsum⟩ :=
      exists_parametrizedChainSum_eq_sub_add (T₀ := T₀) (T₁ := T₁) hB hB' hh x y
    have hdeg : indQ y - ind x = -(((ind x - indQ y).toNat : ℕ) : ℤ) := by omega
    exact ⟨cubicalChainDifferential_parametrizedChainSum
      (fun x y ↦ ContinuousMap.id (N x y)) (fun x y ↦ ContinuousMap.id (N x y)) T₀ T₁ hh
      (hκ x · · y) (hκκ' x · · y) (hκ' x · · y) (fun _ _ _ ↦ rfl) (fun _ _ _ ↦ rfl)
      (fun _ _ _ ↦ rfl) (fun _ _ _ ↦ rfl) (fun z _ h₂ ↦ hd z y (by omega))
      fun z h₁ _ ↦ hd x z (by omega), T₁.chain x y, T₀.chain x y, b,
      (T₁.isRepresenting_iff ν).1 hT₁ x y (by omega),
      (T₀.isRepresenting_iff ν).1 hT₀ x y (by omega), hdeg ▸ hb, hsum⟩
  exact ⟨⟨h, hh, hd⟩⟩

section Evaluation

variable {G : Type*} [Monoid G] [TopologicalSpace G] [ContinuousMul G] {q : ∀ x y, C(M x y, G)}
  {q' : ∀ x y, C(M' x y, G)} {r : ∀ x y, C(N x y, G)}

/-- **The continuation cocycles of two representing continuation chain systems are related by a
parametrized cocycle.** Under the hypotheses of
`TauCeti.ContinuationChainSystem.IsRepresenting.nonempty_parametrizedChainSystem`, for evaluation
maps `q`, `q'` and `r` into a topological monoid that are multiplicative for all the composition
maps, the continuation cocycles of push-forwards of `T₀` and `T₁` are joined by a parametrized
cocycle. Through `TauCeti.ParametrizedCocycle.homotopy`, the continuation maps of the twisted
complexes they induce are therefore chain homotopic, for every differential graded right module
over `C^□_*(G; k)`. -/
theorem IsRepresenting.nonempty_parametrizedCocycle (hT₀ : T₀.IsRepresenting B ν)
    (hT₁ : T₁.IsRepresenting B ν)
    (hκ : ∀ x w z y (a : M x w) (b : M w z) (c : N z y),
      κ x z y (ι x w z (a, b), c) = κ x w y (a, κ w z y (b, c)))
    (hκκ' : ∀ x w z y (a : M x w) (b : N w z) (c : M' z y),
      κ' x z y (κ x w z (a, b), c) = κ x w y (a, κ' w z y (b, c)))
    (hκ' : ∀ x w z y (a : N x w) (b : M' w z) (c : M' z y),
      κ' x z y (κ' x w z (a, b), c) = κ' x w y (a, ι' w z y (b, c)))
    (hB : ∀ x z y p, κ x z y p ∈ B x y) (hB' : ∀ x z y p, κ' x z y p ∈ B x y)
    (hinj : ∀ x y, indQ y ≤ ind x → Function.Injective (HomologicalComplex.homologyMap
      (cokernel.π ((normalizedCubicalChainComplex k).map (TopPair.ofSubset (B x y)).map))
        (ind x - indQ y).toNat).hom)
    (hq : ∀ x z y (u : M x z) (v : M z y), q x y (ι x z y (u, v)) = q x z u * q z y v)
    (hq' : ∀ x z y (u : M' x z) (v : M' z y), q' x y (ι' x z y (u, v)) = q' x z u * q' z y v)
    (hrκ : ∀ x z y (u : M x z) (v : N z y), r x y (κ x z y (u, v)) = q x z u * r z y v)
    (hrκ' : ∀ x z y (u : N x z) (v : M' z y), r x y (κ' x z y (u, v)) = r x z u * q' z y v) :
    Nonempty (ParametrizedCocycle (T₀.continuationCocycle r hq hq' hrκ hrκ')
      (T₁.continuationCocycle r hq hq' hrκ hrκ')) :=
  (hT₀.nonempty_parametrizedChainSystem hT₁ hκ hκκ' hκ' hB hB' hinj).map fun η ↦
    η.parametrizedCocycle r hq hq' hrκ hrκ' hrκ hrκ' (fun _ _ ↦ ContinuousMap.comp_id _)
      (fun _ _ ↦ ContinuousMap.comp_id _) hrκ hrκ'

end Evaluation

end ContinuationChainSystem

end ContinuationExistence

end TauCeti
