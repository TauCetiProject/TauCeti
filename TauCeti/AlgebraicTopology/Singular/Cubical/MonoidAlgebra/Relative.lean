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
* `TauCeti.exists_forall_cubicalChainDifferential_eq_and_isRepresentingChain`: under the gluing
  condition, a family of chains with prescribed boundaries representing prescribed relative
  classes exists, when the prescribed boundary of each chain only depends on the chains of
  smaller dimension.
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

/-! ### Families of chains with prescribed boundaries -/

section Induction

variable {P Q : Type*} [Finite P] [Finite Q] {N : P → Q → TopCat.{u}} {k : Type u} [CommRing k]
  {A : ∀ x y, Set (N x y)} {deg : P → Q → ℤ} {n : P → Q → ℕ}
  {F : (∀ x y, normalizedCubicalChainAlgebra (N x y) k) →
    ∀ x y, normalizedCubicalChainAlgebra (N x y) k}
  {μ : ∀ x y, ((TopPair.ofSubset (A x y)).cubicalChainComplex k).homology (n x y)}

/-- **Families of chains with prescribed boundaries representing prescribed classes.** Let
`deg x y` be the cohomological degree of the chain of the pair `(x, y)`, so that it is a chain of
dimension `-deg x y`, and let `μ x y` be a class of the relative cubical homology
`H_{n x y}(N x y, A x y)`, where `n x y = -deg x y` whenever `deg x y ≤ 0`. Let `F s x y` be the
prescribed boundary of the chain of `(x, y)` for a family `s` of chains of these degrees,
depending only on the chains of the pairs of smaller dimension and vanishing in dimension at most
zero. Suppose the **gluing condition**: whenever `s` has the prescribed boundaries and represents
the classes `μ` at the pairs of smaller dimension, and `n x y = m + 1`, `F s x y` is the image of
an `m`-cycle of `A x y` whose class is the image of `μ x y` under the connecting morphism
`H_{m+1}(N x y, A x y) → H_m(A x y)`. Then some family of chains of these degrees has the
prescribed boundaries and represents the classes `μ` at all pairs of dimension at least zero. -/
theorem exists_forall_cubicalChainDifferential_eq_and_isRepresentingChain
    (hn : ∀ x y, deg x y ≤ 0 → deg x y = -(n x y : ℤ))
    (hF : ∀ (s s' : ∀ x y, normalizedCubicalChainAlgebra (N x y) k) x y,
      (∀ x y, s x y ∈ cubicalChainGrading (N x y) k (deg x y)) →
      (∀ x y, s' x y ∈ cubicalChainGrading (N x y) k (deg x y)) →
      (∀ x' y', deg x y < deg x' y' → s x' y' = s' x' y') → F s x y = F s' x y)
    (hF₀ : ∀ (s : ∀ x y, normalizedCubicalChainAlgebra (N x y) k) x y,
      (∀ x y, s x y ∈ cubicalChainGrading (N x y) k (deg x y)) → 0 ≤ deg x y → F s x y = 0)
    (hglue : ∀ (s : ∀ x y, normalizedCubicalChainAlgebra (N x y) k) x y (m : ℕ)
      (hm : n x y = m + 1), deg x y ≤ 0 →
      (∀ x y, s x y ∈ cubicalChainGrading (N x y) k (deg x y)) →
      (∀ x' y', deg x y < deg x' y' →
        cubicalChainDifferential (N x' y') k (s x' y') = F s x' y' ∧
          (deg x' y' ≤ 0 → IsRepresentingChain (s x' y') (μ x' y'))) →
      IsRepresentingCycle (F s x y)
        (((TopPair.ofSubset (A x y)).cubicalHomologyδ k (n x y) m hm.symm).hom (μ x y))) :
    ∃ s : ∀ x y, normalizedCubicalChainAlgebra (N x y) k,
      (∀ x y, s x y ∈ cubicalChainGrading (N x y) k (deg x y)) ∧
      ∀ x y, cubicalChainDifferential (N x y) k (s x y) = F s x y ∧
        (deg x y ≤ 0 → IsRepresentingChain (s x y) (μ x y)) := by
  -- Induction on `d`: the conditions hold at the pairs of degree at least `1 - d`.
  have key (d : ℕ) : ∃ s : ∀ x y, normalizedCubicalChainAlgebra (N x y) k,
      (∀ x y, s x y ∈ cubicalChainGrading (N x y) k (deg x y)) ∧
      ∀ x y, 1 - (d : ℤ) ≤ deg x y →
        cubicalChainDifferential (N x y) k (s x y) = F s x y ∧
          (deg x y ≤ 0 → IsRepresentingChain (s x y) (μ x y)) := by
    induction d with
    | zero =>
      refine ⟨0, fun _ _ ↦ zero_mem _, fun x y hxy ↦ ⟨?_, fun h ↦ by omega⟩⟩
      rw [hF₀ 0 x y (fun _ _ ↦ zero_mem _) (by omega)]
      exact map_zero _
    | succ d ih =>
      obtain ⟨s, hs, hd⟩ := ih
      -- At the pairs of degree `-d`, choose chains with the prescribed boundary and class.
      have hnew (x : P) (y : Q) (hxy : deg x y = -d) :
          ∃ c : normalizedCubicalChainAlgebra (N x y) k,
            c ∈ cubicalChainGrading (N x y) k (deg x y) ∧
            cubicalChainDifferential (N x y) k c = F s x y ∧ IsRepresentingChain c (μ x y) := by
        have hdeg := hn x y (by omega)
        by_cases h₀ : n x y = 0
        · -- In dimension zero the prescribed boundary vanishes, and so does that of any chain.
          obtain ⟨c, hc⟩ := exists_isRepresentingChain (A x y) (μ x y)
          have hmem : c ∈ cubicalChainGrading (N x y) k (deg x y) :=
            hdeg ▸ hc.mem_cubicalChainGrading
          refine ⟨c, hmem, ?_, hc⟩
          rw [cubicalChainDifferential_eq_zero_of_nonneg _ _ (by omega) hmem,
            hF₀ s x y hs (by omega)]
        · obtain ⟨m, hm⟩ := Nat.exists_eq_add_one_of_ne_zero h₀
          obtain ⟨c, hc, hdc⟩ := IsRepresentingCycle.exists_isRepresentingChain hm.symm
            (hglue s x y m hm (by omega) hs fun x' y' h ↦ hd x' y' (by omega))
          exact ⟨c, hdeg ▸ hc.mem_cubicalChainGrading, hdc, hc⟩
      classical
      let s' : ∀ x y, normalizedCubicalChainAlgebra (N x y) k := fun x y ↦
        if hxy : deg x y = -d then (hnew x y hxy).choose else s x y
      have hs'new (x : P) (y : Q) (hxy : deg x y = -d) : s' x y = (hnew x y hxy).choose :=
        dite_eq_left hxy
      have hs's (x : P) (y : Q) (hxy : deg x y ≠ -d) : s' x y = s x y := dite_eq_right hxy
      have hs' (x : P) (y : Q) : s' x y ∈ cubicalChainGrading (N x y) k (deg x y) := by
        by_cases hxy : deg x y = -d
        · exact hs'new x y hxy ▸ (hnew x y hxy).choose_spec.1
        · exact hs's x y hxy ▸ hs x y
      refine ⟨s', hs', fun x y hxy ↦ ?_⟩
      -- The new chains only change the pairs of degree `-d`, which do not enter the prescribed
      -- boundaries of the pairs of degree at least `-d`.
      rw [hF s' s x y hs' hs fun x' y' h ↦ hs's x' y' (by omega)]
      by_cases hxy' : deg x y = -d
      · rw [hs'new x y hxy']
        exact ⟨(hnew x y hxy').choose_spec.2.1, fun _ ↦ (hnew x y hxy').choose_spec.2.2⟩
      · rw [hs's x y hxy']
        exact hd x y (by omega)
  -- The degrees of the finitely many pairs are bounded below.
  obtain ⟨L, hL⟩ := (Set.finite_range fun p : P × Q ↦ deg p.1 p.2).bddBelow
  obtain ⟨s, hs, h⟩ := key (1 - L).toNat
  exact ⟨s, hs, fun x y ↦ h x y (by have : L ≤ deg x y := hL ⟨(x, y), rfl⟩; omega)⟩

end Induction

end TauCeti
