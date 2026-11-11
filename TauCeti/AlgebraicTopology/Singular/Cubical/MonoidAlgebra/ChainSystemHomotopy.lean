/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Cubical.MonoidAlgebra.ContinuationChainSystem
public import TauCeti.AlgebraicTopology.Singular.Cubical.MonoidAlgebra.RepresentingChainSystem
import TauCeti.Algebra.Ring.NegOnePow
import TauCeti.Logic.Function.LevelInduction

/-!
# Homotopies of twisting chain systems

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
(`TauCeti.TwistingChainSystem.IsRepresenting.exists_homotopy`), provided that the composition
maps are associative and take values in the subspaces `A x y`, and that the maps
`H_{ind x - ind y - 1}(M x y) → H_{ind x - ind y - 1}(M x y, A x y)` are injective. For a compact
manifold `M x y` of dimension `ind x - ind y - 1` with boundary `A x y` the last condition holds
because the boundary has no homology in that degree. The chains are constructed by induction on
`ind x - ind y`: the right-hand side of the homotopy equation is a cycle once the equation holds
at the pairs of smaller index difference
(`TauCeti.TwistingChainSystem.cubicalChainDifferential_sub_add_continuationChainSum`), and its
relative class is `μ x y - μ x y = 0`, since the continuation sum lies in `A x y`; injectivity
makes it a boundary.

## Main definitions

* `TauCeti.TwistingChainSystem.Homotopy`: a homotopy of twisting chain systems.
* `TauCeti.TwistingChainSystem.Homotopy.continuationCocycle`: the continuation cocycle `1 + q_* h`
  of push-forwards.

## Main results

* `TauCeti.TwistingChainSystem.cubicalChainDifferential_sub_add_continuationChainSum`: the
  right-hand side of the homotopy equation is a cycle.
* `TauCeti.TwistingChainSystem.IsRepresenting.exists_homotopy`: two representing chain systems of
  the same classes are joined by a homotopy.

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

end Homotopy

end Evaluation

end TwistingChainSystem

end Homotopy

/-! ### Existence of homotopies between representing chain systems -/

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
  let ιA : ∀ z, C(M x z × M z y, A x y) := fun z ↦
    ⟨fun p ↦ ⟨ι x z y p, hA x z y p⟩, (ι x z y).continuous.subtype_mk _⟩
  have hιA (z : P) : (ContinuousMap.subtypeVal (A x y)).comp (ιA z) = ι x z y := rfl
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

/-- The chain of a pair `(x, y)` of index difference `d + 1` in the inductive construction of a
homotopy: a chain whose boundary is the right-hand side of the homotopy equation, which is a
cycle with vanishing relative class. -/
private theorem exists_chain_of_sub_eq (hS : S.IsRepresenting A μ) (hS' : S'.IsRepresenting A μ)
    (hι : ∀ x w z y (a : M x w) (b : M w z) (c : M z y),
      ι x z y (ι x w z (a, b), c) = ι x w y (a, ι w z y (b, c)))
    (hA : ∀ x z y p, ι x z y p ∈ A x y)
    (hinj : ∀ x y, ind y < ind x → Function.Injective (HomologicalComplex.homologyMap
      (cokernel.π ((normalizedCubicalChainComplex k).map (TopPair.ofSubset (A x y)).map))
        (ind x - ind y - 1).toNat).hom)
    {h : ∀ x y, normalizedCubicalChainAlgebra (M x y) k}
    (hh : ∀ x y, h x y ∈ cubicalChainGrading (M x y) k (ind y - ind x)) {x y : P} {d : ℕ}
    (hxy : ind x - ind y = d + 1)
    (hd : ∀ x' y', ind x' - ind y' ≤ d → cubicalChainDifferential (M x' y') k (h x' y') =
      S.chain x' y' - S'.chain x' y' +
        continuationChainSum ind ind ι ι k S.chain S'.chain h x' y') :
    ∃ e : normalizedCubicalChainAlgebra (M x y) k,
      e ∈ cubicalChainGrading (M x y) k (ind y - ind x) ∧
      cubicalChainDifferential (M x y) k e =
        S.chain x y - S'.chain x y + continuationChainSum ind ind ι ι k S.chain S'.chain h x y := by
  obtain ⟨b, hb, hbsum⟩ := exists_continuationChainSum_eq_cubicalChainSumMap (S := S) (S' := S')
    hA hh x y
  have hdeg : ind y - ind x + 1 = -(((ind x - ind y - 1).toNat : ℕ) : ℤ) := by omega
  have hcycle := cubicalChainDifferential_sub_add_continuationChainSum S S' hh (hι x · · y)
    (fun z h₁ h₂ ↦ hd z y (by omega)) (fun z h₁ h₂ ↦ hd x z (by omega))
  rw [← hbsum] at hcycle ⊢
  obtain ⟨e, he, hde⟩ := ((S.isRepresenting_iff μ).1 hS x y (by omega))
    |>.exists_cubicalChainDifferential_eq_sub_add ((S'.isRepresenting_iff μ).1 hS' x y (by omega))
      (hdeg ▸ hb) hcycle (hinj x y (by omega))
  have hdeg' : -((((ind x - ind y - 1).toNat + 1 : ℕ)) : ℤ) = ind y - ind x := by omega
  exact ⟨e, hdeg' ▸ he, hde⟩

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
theorem IsRepresenting.exists_homotopy (hS : S.IsRepresenting A μ) (hS' : S'.IsRepresenting A μ)
    (hι : ∀ x w z y (a : M x w) (b : M w z) (c : M z y),
      ι x z y (ι x w z (a, b), c) = ι x w y (a, ι w z y (b, c)))
    (hA : ∀ x z y p, ι x z y p ∈ A x y)
    (hinj : ∀ x y, ind y < ind x → Function.Injective (HomologicalComplex.homologyMap
      (cokernel.π ((normalizedCubicalChainComplex k).map (TopPair.ofSubset (A x y)).map))
        (ind x - ind y - 1).toNat).hom) :
    Nonempty (S.Homotopy S') := by
  -- Induction on the index difference.
  refine (exists_forall_of_forall_level_lt (fun x y ↦ (ind x - ind y).toNat)
    (fun x y a ↦ a ∈ cubicalChainGrading (M x y) k (ind y - ind x))
    (fun h x y ↦ cubicalChainDifferential (M x y) k (h x y) =
      S.chain x y - S'.chain x y + continuationChainSum ind ind ι ι k S.chain S'.chain h x y)
    ⟨0, fun _ _ ↦ zero_mem _⟩ fun h hh x y hlt ↦ ?_).elim fun h ⟨hh, hd⟩ ↦ ⟨⟨h, hh, hd⟩⟩
  by_cases hxy : ind x ≤ ind y
  · -- At the pairs with `ind x ≤ ind y` all terms vanish for degree reasons.
    refine ⟨0, zero_mem _, fun h' hh' _ hh'0 ↦ ?_⟩
    rw [hh'0, S.chain_eq_zero_of_le hxy, S'.chain_eq_zero_of_le hxy,
      continuationChainSum_eq_zero_of_le S.mem_graded S'.mem_graded hh' hxy]
    simp
  · obtain ⟨e, he, hde⟩ := exists_chain_of_sub_eq hS hS' hι hA hinj hh (x := x) (y := y)
      (d := (ind x - ind y - 1).toNat) (by omega) fun x' y' h ↦ hlt x' y' (by omega)
    -- The continuation sum only depends on the chains of the pairs of smaller index difference.
    refine ⟨e, he, fun h' hh' hhh' hh'e ↦ ?_⟩
    rw [hh'e, hde, continuationChainSum_congr S.mem_graded S'.mem_graded
      (fun z hzx ↦ (hhh' z y (by omega)).symm) fun z hyz ↦ (hhh' x z (by omega)).symm]

end TwistingChainSystem

end Existence

end TauCeti
