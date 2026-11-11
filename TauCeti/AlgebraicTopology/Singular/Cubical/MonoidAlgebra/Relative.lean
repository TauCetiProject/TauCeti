/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Cubical.MonoidAlgebra.DGAlgebra
public import TauCeti.AlgebraicTopology.Singular.Cubical.Comparison.Excision

/-!
# Relative classes in the algebra of cubical chains

For a subspace `A` of a space `X`, this file expresses in the algebra of normalized cubical chains
`TauCeti.normalizedCubicalChainAlgebra X k` that an element represents a class of the relative
cubical homology `Hₙ(X, A)`, or a class of the cubical homology `Hₘ(A)` of the subspace. The
prescribed-boundary lift `TopPair.exists_boundary_eq_of_cubicalHomologyδ_eq` becomes
`TauCeti.IsRepresentingCycle.exists_isRepresentingChain`: if `b` is a cycle of `A` representing
the image of `μ ∈ Hₘ₊₁(X, A)` under the connecting morphism, some chain representing `μ` has
differential `b`.

## Main definitions

* `TauCeti.IsRepresentingChain`: an element of the algebra of normalized cubical chains is a
  chain of dimension `n` which is a relative cycle with a given class of `Hₙ(X, A)`.
* `TauCeti.IsRepresentingCycle`: an element is the image of an `m`-cycle of `A` with a given
  class of `Hₘ(A)`.

## Main results

* `TauCeti.exists_isRepresentingChain`: every relative class is represented.
* `TauCeti.IsRepresentingCycle.exists_isRepresentingChain`: a relative class is represented by a
  chain with a prescribed boundary.
* `TauCeti.IsRepresentingChain.exists_cubicalChainDifferential_eq_sub_add`: when
  `Hₙ(X) → Hₙ(X, A)` is injective, a cycle `a - a' + b` with `a`, `a'` representing the same
  relative class and `b` a chain of `A` is a boundary.
-/

public section

noncomputable section

open CategoryTheory Limits

universe u

namespace TauCeti

open NormalizedCubicalChain

variable {k : Type u} [CommRing k] {X : TopCat.{u}} {A : Set X}

/-- An element `a` of the algebra of normalized cubical chains of `X` **represents** the class `μ`
of the relative cubical homology `Hₙ(X, A)` when it is a chain of dimension `n` whose image in
the relative chains is a relative cycle with class `μ`. -/
def IsRepresentingChain {n : ℕ} (a : normalizedCubicalChainAlgebra X k)
    (μ : ((TopPair.ofSubset A).cubicalChainComplex k).homology n) : Prop :=
  ∃ c : NormalizedCubicalChain X k n, cubicalChainLof X k n c = a ∧
    (TopPair.ofSubset A).IsCubicalRepresentative k c μ

theorem isRepresentingChain_iff {n : ℕ} (a : normalizedCubicalChainAlgebra X k)
    (μ : ((TopPair.ofSubset A).cubicalChainComplex k).homology n) :
    IsRepresentingChain a μ ↔ ∃ c : NormalizedCubicalChain X k n, cubicalChainLof X k n c = a ∧
      (TopPair.ofSubset A).IsCubicalRepresentative k c μ :=
  Iff.rfl

/-- A chain representing a class of `Hₙ(X, A)` has cohomological degree `-n`. -/
theorem IsRepresentingChain.mem_cubicalChainGrading {n : ℕ} {a : normalizedCubicalChainAlgebra X k}
    {μ : ((TopPair.ofSubset A).cubicalChainComplex k).homology n} (ha : IsRepresentingChain a μ) :
    a ∈ cubicalChainGrading X k (-(n : ℤ)) := by
  obtain ⟨c, rfl, -⟩ := ha
  exact cubicalChainLof_mem X k c

variable (A) in
/-- Every class of the relative cubical homology `Hₙ(X, A)` is represented by a chain. -/
theorem exists_isRepresentingChain {n : ℕ}
    (μ : ((TopPair.ofSubset A).cubicalChainComplex k).homology n) :
    ∃ a : normalizedCubicalChainAlgebra X k, IsRepresentingChain a μ := by
  obtain ⟨c, hc⟩ := (TopPair.ofSubset A).exists_isCubicalRepresentative k μ
  exact ⟨_, c, rfl, hc⟩

/-- An element `a` of the algebra of normalized cubical chains of `X` is a **cycle of `A`
representing** the class `ν` of the cubical homology `Hₘ(A)` when it is the image of an
`m`-cycle of `A` whose class is `ν`. -/
def IsRepresentingCycle {m : ℕ} (a : normalizedCubicalChainAlgebra X k)
    (ν : ((normalizedCubicalChainComplex k).obj (TopPair.ofSubset A).snd).homology m) : Prop :=
  ∃ z : ((normalizedCubicalChainComplex k).obj (TopPair.ofSubset A).snd).cycles m,
    cubicalChainLof X k m (map k (TopPair.ofSubset A).map.hom m
        ((((normalizedCubicalChainComplex k).obj (TopPair.ofSubset A).snd).iCycles m).hom z)) =
      a ∧
    (((normalizedCubicalChainComplex k).obj (TopPair.ofSubset A).snd).homologyπ m).hom z = ν

theorem isRepresentingCycle_iff {m : ℕ} (a : normalizedCubicalChainAlgebra X k)
    (ν : ((normalizedCubicalChainComplex k).obj (TopPair.ofSubset A).snd).homology m) :
    IsRepresentingCycle a ν ↔
      ∃ z : ((normalizedCubicalChainComplex k).obj (TopPair.ofSubset A).snd).cycles m,
        cubicalChainLof X k m (map k (TopPair.ofSubset A).map.hom m
            ((((normalizedCubicalChainComplex k).obj
              (TopPair.ofSubset A).snd).iCycles m).hom z)) = a ∧
        (((normalizedCubicalChainComplex k).obj (TopPair.ofSubset A).snd).homologyπ m).hom z =
          ν :=
  Iff.rfl

/-- A cycle of `A` representing a class of `Hₘ(A)` has cohomological degree `-m`. -/
theorem IsRepresentingCycle.mem_cubicalChainGrading {m : ℕ}
    {a : normalizedCubicalChainAlgebra X k}
    {ν : ((normalizedCubicalChainComplex k).obj (TopPair.ofSubset A).snd).homology m}
    (ha : IsRepresentingCycle a ν) : a ∈ cubicalChainGrading X k (-(m : ℤ)) := by
  obtain ⟨z, rfl, -⟩ := ha
  exact cubicalChainLof_mem X k _

/-- A cycle of `A` representing a class of `Hₘ(A)` has differential zero. -/
theorem IsRepresentingCycle.cubicalChainDifferential_eq_zero {m : ℕ}
    {a : normalizedCubicalChainAlgebra X k}
    {ν : ((normalizedCubicalChainComplex k).obj (TopPair.ofSubset A).snd).homology m}
    (ha : IsRepresentingCycle a ν) : cubicalChainDifferential X k a = 0 := by
  obtain ⟨z, rfl, -⟩ := ha
  rcases m with _ | j
  · exact cubicalChainDifferential_lof_zero X k _
  · have hz : boundary _ k j
        ((((normalizedCubicalChainComplex k).obj (TopPair.ofSubset A).snd).iCycles (j + 1)).hom
          z) = 0 :=
      (normalizedCubicalChainComplex_obj_d_apply _ j _).symm.trans
        (LinearMap.congr_fun (congrArg ModuleCat.Hom.hom
          (((normalizedCubicalChainComplex k).obj (TopPair.ofSubset A).snd).iCycles_d
            (j + 1) j)) z)
    refine (cubicalChainDifferential_lof_succ X k j _).trans ?_
    refine (congrArg (cubicalChainLof X k j) ?_).trans (map_zero _)
    exact (LinearMap.congr_fun (map_boundary k (TopPair.ofSubset A).map.hom j) _).symm.trans
      ((congrArg (map k (TopPair.ofSubset A).map.hom j) hz).trans (map_zero _))

/-- **A relative class is represented by a chain with a prescribed boundary**, in the algebra of
cubical chains: if `b` is a cycle of `A` representing the image of `μ ∈ Hₙ(X, A)` under the
connecting morphism `Hₙ(X, A) → Hₘ(A)`, `n = m + 1`, some chain representing `μ` has
differential `b`. -/
theorem IsRepresentingCycle.exists_isRepresentingChain {n m : ℕ} (h : m + 1 = n)
    {μ : ((TopPair.ofSubset A).cubicalChainComplex k).homology n}
    {b : normalizedCubicalChainAlgebra X k}
    (hb : IsRepresentingCycle b (((TopPair.ofSubset A).cubicalHomologyδ k n m h).hom μ)) :
    ∃ a : normalizedCubicalChainAlgebra X k,
      IsRepresentingChain a μ ∧ cubicalChainDifferential X k a = b := by
  subst h
  obtain ⟨z, rfl, hz⟩ := hb
  obtain ⟨c, r, hbd, hr, hrμ⟩ :=
    (TopPair.ofSubset A).exists_boundary_eq_of_cubicalHomologyδ_eq k m μ z hz.symm
  exact ⟨_, ⟨c, rfl, (TopPair.isCubicalRepresentative_iff c μ).2 ⟨r, hr, hrμ⟩⟩,
    (cubicalChainDifferential_lof_succ X k m c).trans (congrArg _ hbd)⟩

/-- **A cycle with vanishing relative class is a boundary** when the relative class determines
the absolute one. Let `a` and `a'` represent the same class of `Hₙ(X, A)` and let `b` be an
`n`-chain of `A`, pushed forward to `X`. If `a - a' + b` is a cycle of `X` and the map
`Hₙ(X) → Hₙ(X, A)` is injective, then `a - a' + b` is the boundary of an `(n + 1)`-chain of `X`.
The relative class of the cycle is that of `a - a'`, which vanishes. The injectivity holds for
instance when `Hₙ(A) = 0`, as for a compact `n`-manifold `X` with boundary `A`. -/
theorem IsRepresentingChain.exists_cubicalChainDifferential_eq_sub_add {n : ℕ}
    {μ : ((TopPair.ofSubset A).cubicalChainComplex k).homology n}
    {a a' : normalizedCubicalChainAlgebra X k} (ha : IsRepresentingChain a μ)
    (ha' : IsRepresentingChain a' μ)
    {b : normalizedCubicalChainAlgebra A k} (hb : b ∈ cubicalChainGrading A k (-(n : ℤ)))
    (hc : cubicalChainDifferential X k
      (a - a' + cubicalChainSumMap k (ContinuousMap.subtypeVal A) b) = 0)
    (hinj : Function.Injective (HomologicalComplex.homologyMap
      (cokernel.π ((normalizedCubicalChainComplex k).map (TopPair.ofSubset A).map)) n).hom) :
    ∃ e : normalizedCubicalChainAlgebra X k, e ∈ cubicalChainGrading X k (-((n + 1 : ℕ) : ℤ)) ∧
      cubicalChainDifferential X k e =
        a - a' + cubicalChainSumMap k (ContinuousMap.subtypeVal A) b := by
  obtain ⟨c, rfl, hcμ⟩ := ha
  obtain ⟨r, hcr, rfl⟩ :=
    (TopPair.isCubicalRepresentative_iff (P := TopPair.ofSubset A) c _).1 hcμ
  obtain ⟨c', rfl, hcμ'⟩ := ha'
  obtain ⟨r', hcr', hr'⟩ :=
    (TopPair.isCubicalRepresentative_iff (P := TopPair.ofSubset A) c' _).1 hcμ'
  obtain ⟨b, rfl⟩ : ∃ b₀ : NormalizedCubicalChain A k n, cubicalChainLof A k n b₀ = b := by
    rcases (mem_cubicalChainGrading_iff _ k).1 hb with rfl | ⟨m, y, hm, rfl⟩
    · exact ⟨0, map_zero _⟩
    · obtain rfl : m = n := by omega
      exact ⟨y, rfl⟩
  rw [cubicalChainSumMap_lof, ← map_sub, ← map_add] at hc ⊢
  -- The chain `c - c' + b` is a cycle of `X`.
  have hd : ((normalizedCubicalChainComplex k).obj X).d n (n - 1)
      (c - c' + NormalizedCubicalChain.map k (ContinuousMap.subtypeVal A) n b) = 0 := by
    rcases n with _ | m
    · rw [HomologicalComplex.shape _ 0 (0 - 1) (by simp)]
      exact LinearMap.zero_apply _
    · rw [cubicalChainDifferential_lof_succ] at hc
      exact (normalizedCubicalChainComplex_obj_d_apply X m _).trans
        (DirectSum.of_injective (β := fun i ↦ NormalizedCubicalChain X k i) m
          (hc.trans (map_zero _).symm))
  obtain ⟨y, hy⟩ := TopPair.exists_boundary_eq_sub_add_map_of_injective k (TopPair.ofSubset A) n
    c c' b hd r r' hcr hcr' hr'.symm hinj
  exact ⟨cubicalChainLof X k (n + 1) y, cubicalChainLof_mem X k y,
    (cubicalChainDifferential_lof_succ X k n y).trans (congrArg (cubicalChainLof X k n) hy)⟩

end TauCeti
