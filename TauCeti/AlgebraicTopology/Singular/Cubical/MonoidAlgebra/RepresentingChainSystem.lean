/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Cubical.MonoidAlgebra.TwistingChainSystem
public import TauCeti.AlgebraicTopology.Singular.Cubical.Comparison.Excision

/-!
# Existence of representing chain systems

Let `P` be a finite set graded by `ind : P → ℤ`, with spaces `M x y`, subspaces `A x y ⊆ M x y`
and composition maps `ι x z y : M x z × M z y → M x y`, as for `TauCeti.TwistingChainSystem`.
In Morse theory `M x y` is the compactified space of trajectories from `x` to `y`, a manifold
with corners of dimension `ind x - ind y - 1`, `A x y` is its boundary, and `μ x y` is its
fundamental class relative to the boundary, a class of the relative homology
`H_{ind x - ind y - 1}(M x y, A x y)`.

A twisting chain system **represents** the classes `μ` when each chain `s x y` with
`ind y < ind x` is a relative cycle of `(M x y, A x y)` whose class is `μ x y`
(`TauCeti.TwistingChainSystem.IsRepresenting`). For fundamental classes these are the
representing chain systems of Barraud and Cornea, whose push-forwards into the Moore loops of
the base are the Barraud–Cornea twisting cocycle.

Such a system is constructed by induction on `ind x - ind y`
(`TauCeti.TwistingChainSystem.exists_isRepresenting`). Once the chains of the pairs of smaller
index difference are chosen, suppose that the twisting sum of `(x, y)` is a cycle of `A x y`
whose class there is the image of `μ x y` under the connecting morphism
`H_{m+1}(M x y, A x y) → H_m(A x y)`. Then the relative class lifts to a chain whose boundary is
exactly the twisting sum (`TopPair.exists_boundary_eq_of_cubicalHomologyδ_eq`). When the
composition maps are associative the twisting sum is a cycle of `M x y`
(`TauCeti.cubicalChainDifferential_twistingChainSum`), so what has to be checked is that it is
supported in `A x y` and has the right class there. This **gluing condition** is the only
input: for fundamental classes of manifolds with corners whose boundary is glued from the
products `M x z × M z y`, it says that the signed sum of the products of fundamental chains of
the faces is a fundamental cycle of the boundary, since the connecting morphism sends the
fundamental class rel boundary to the fundamental class of the boundary. In index difference one
there is no condition: every class of `H₀(M x y, A x y)` is represented by a `0`-chain, and the
twisting sum vanishes.

## Main definitions

* `TopPair.IsCubicalRepresentative`: a normalized cubical chain of the ambient space of a pair
  is a relative cycle with a given relative class.
* `TauCeti.IsRepresentingChain`: the same for an element of the algebra of normalized cubical
  chains, a chain of the dimension of the class.
* `TauCeti.TwistingChainSystem.IsRepresenting`: a twisting chain system whose chains represent
  prescribed relative classes.

## Main results

* `TauCeti.TwistingChainSystem.exists_isRepresenting`: under the gluing condition, a twisting
  chain system representing the classes `μ` exists.
* `TauCeti.TwistingChainSystem.exists_isRepresenting_of_sub_le_one`: when all index differences
  are at most one, every family of classes is represented.

## References

* J.-F. Barraud, O. Cornea, *Lagrangian intersections and the Serre spectral sequence*, Ann. of
  Math. 166 (2007), 657–722, Section 2 and Appendix A.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, Chapters 5 and 6.
-/

public section

noncomputable section

open CategoryTheory Limits TauCeti

universe u

namespace TopPair

variable (k : Type u) [Ring k] (P : TopPair.{u})

/-- A normalized cubical `n`-chain `c` of the ambient space of a pair `(X, A)` **represents** the
class `μ` of the relative cubical homology `Hₙ(X, A)` when its image in the relative chains is a
relative cycle whose class is `μ`. -/
def IsCubicalRepresentative {n : ℕ} (c : NormalizedCubicalChain P.fst k n)
    (μ : (P.cubicalChainComplex k).homology n) : Prop :=
  ∃ r : (P.cubicalChainComplex k).cycles n,
    ((cokernel.π ((normalizedCubicalChainComplex k).map P.map)).f n).hom c =
        ((P.cubicalChainComplex k).iCycles n).hom r ∧
      ((P.cubicalChainComplex k).homologyπ n).hom r = μ

variable {k P}

theorem isCubicalRepresentative_iff {n : ℕ} (c : NormalizedCubicalChain P.fst k n)
    (μ : (P.cubicalChainComplex k).homology n) :
    P.IsCubicalRepresentative k c μ ↔ ∃ r : (P.cubicalChainComplex k).cycles n,
      ((cokernel.π ((normalizedCubicalChainComplex k).map P.map)).f n).hom c =
          ((P.cubicalChainComplex k).iCycles n).hom r ∧
        ((P.cubicalChainComplex k).homologyπ n).hom r = μ :=
  Iff.rfl

variable (k P) in
/-- Every class of the relative cubical homology of a pair is represented by a chain of the
ambient space. -/
theorem exists_isCubicalRepresentative {n : ℕ} (μ : (P.cubicalChainComplex k).homology n) :
    ∃ c : NormalizedCubicalChain P.fst k n, P.IsCubicalRepresentative k c μ := by
  obtain ⟨r, rfl⟩ := (ModuleCat.epi_iff_surjective _).1
    (inferInstance : Epi ((P.cubicalChainComplex k).homologyπ n)) μ
  obtain ⟨c, hc⟩ := (ModuleCat.epi_iff_surjective _).1
    ((HomologicalComplex.shortExact_iff_degreewise_shortExact _).1
      (shortExact_cubicalChainComplexShortComplex k P) n).epi_g
    (((P.cubicalChainComplex k).iCycles n).hom r)
  exact ⟨c, r, hc, rfl⟩

end TopPair

namespace TauCeti

open NormalizedCubicalChain

/-! ### Representing chains in the algebra of cubical chains -/

section Chain

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
  exact ⟨_, ⟨c, rfl, r, hr, hrμ⟩,
    (cubicalChainDifferential_lof_succ X k m c).trans (congrArg _ hbd)⟩

end Chain

/-! ### Representing chain systems -/

variable {P : Type*} [Fintype P] {ind : P → ℤ} {M : P → P → TopCat.{u}}
  {ι : ∀ x y z, C(M x y × M y z, M x z)} {k : Type u} [CommRing k] {A : ∀ x y, Set (M x y)}

namespace TwistingChainSystem

variable (A) in
/-- A twisting chain system **represents** the classes `μ x y` of the relative cubical homology
`H_{ind x - ind y - 1}(M x y, A x y)` when the chain of every pair `(x, y)` with `ind y < ind x`
represents `μ x y`. When `A x y` is the boundary of a manifold with corners `M x y` and
`μ x y` is its fundamental class rel boundary, this is a representing chain system of
Barraud and Cornea. -/
def IsRepresenting (S : TwistingChainSystem ind ι k)
    (μ : ∀ x y, ((TopPair.ofSubset (A x y)).cubicalChainComplex k).homology
      (ind x - ind y - 1).toNat) : Prop :=
  ∀ x y, ind y < ind x → IsRepresentingChain (S.chain x y) (μ x y)

theorem isRepresenting_iff (S : TwistingChainSystem ind ι k)
    (μ : ∀ x y, ((TopPair.ofSubset (A x y)).cubicalChainComplex k).homology
      (ind x - ind y - 1).toNat) :
    S.IsRepresenting A μ ↔ ∀ x y, ind y < ind x → IsRepresentingChain (S.chain x y) (μ x y) :=
  Iff.rfl

end TwistingChainSystem

section Existence

variable {μ : ∀ x y, ((TopPair.ofSubset (A x y)).cubicalChainComplex k).homology
  (ind x - ind y - 1).toNat}

/-- The chain of a pair of index difference `d + 1` in the inductive construction: in index
difference one, any chain representing the class; above, a chain representing the class whose
differential is the twisting sum, which the gluing condition provides. -/
private theorem exists_chain_of_sub_eq (s : ∀ x y, normalizedCubicalChainAlgebra (M x y) k)
    (hs : ∀ x y, s x y ∈ cubicalChainGrading (M x y) k (ind y - ind x + 1))
    {x y : P} {d : ℕ} (hxy : ind x - ind y = d + 1)
    (hglue : ∀ m : ℕ, (hm : ind x - ind y = m + 2) →
      IsRepresentingCycle (twistingChainSum ind ι k s x y)
        (((TopPair.ofSubset (A x y)).cubicalHomologyδ k (ind x - ind y - 1).toNat m).hom
          (μ x y))) :
    ∃ a : normalizedCubicalChainAlgebra (M x y) k,
      a ∈ cubicalChainGrading (M x y) k (ind y - ind x + 1) ∧
      cubicalChainDifferential (M x y) k a = twistingChainSum ind ι k s x y ∧
      IsRepresentingChain a (μ x y) := by
  have hdeg : -(((ind x - ind y - 1).toNat : ℕ) : ℤ) = ind y - ind x + 1 := by omega
  rcases d with _ | m
  · -- Index difference one: the twisting sum vanishes, and so does the differential of a chain of
    -- cohomological degree `0`.
    obtain ⟨a, ha⟩ := exists_isRepresentingChain (A x y) (μ x y)
    have hmem := hdeg ▸ ha.mem_cubicalChainGrading
    refine ⟨a, hmem, ?_, ha⟩
    rw [eq_zero_of_mem_cubicalChainGrading_of_pos _ _ (by omega)
        (cubicalChainDifferential_mem _ _ hmem),
      twistingChainSum_congr (s' := 0) hs (fun _ _ ↦ zero_mem _) fun z h₁ h₂ ↦ by omega]
    simp [twistingChainSum_def]
  · obtain ⟨a, ha, hda⟩ := (hglue m (by omega)).exists_isRepresentingChain
    exact ⟨a, hdeg ▸ ha.mem_cubicalChainGrading, hda, ha⟩

/-- The inductive step: a family of chains satisfying the twisting equation and representing the
classes on the pairs of index difference at most `d` is modified on the pairs of index
difference `d + 1` to satisfy both there too. -/
private theorem exists_succ (d : ℕ)
    (hglue : ∀ (s : ∀ x y, normalizedCubicalChainAlgebra (M x y) k) (x y : P) (m : ℕ)
      (hm : ind x - ind y = m + 2),
      (∀ x y, s x y ∈ cubicalChainGrading (M x y) k (ind y - ind x + 1)) →
      (∀ x' y', ind x' - ind y' < ind x - ind y →
        cubicalChainDifferential (M x' y') k (s x' y') = twistingChainSum ind ι k s x' y' ∧
          (ind y' < ind x' → IsRepresentingChain (s x' y') (μ x' y'))) →
      IsRepresentingCycle (twistingChainSum ind ι k s x y)
        (((TopPair.ofSubset (A x y)).cubicalHomologyδ k (ind x - ind y - 1).toNat m).hom
          (μ x y)))
    (s : ∀ x y, normalizedCubicalChainAlgebra (M x y) k)
    (hs : ∀ x y, s x y ∈ cubicalChainGrading (M x y) k (ind y - ind x + 1))
    (hd : ∀ x y, ind x - ind y ≤ d →
      cubicalChainDifferential (M x y) k (s x y) = twistingChainSum ind ι k s x y ∧
        (ind y < ind x → IsRepresentingChain (s x y) (μ x y))) :
    ∃ s' : ∀ x y, normalizedCubicalChainAlgebra (M x y) k,
      (∀ x y, s' x y ∈ cubicalChainGrading (M x y) k (ind y - ind x + 1)) ∧
      ∀ x y, ind x - ind y ≤ d + 1 →
        cubicalChainDifferential (M x y) k (s' x y) = twistingChainSum ind ι k s' x y ∧
          (ind y < ind x → IsRepresentingChain (s' x y) (μ x y)) := by
  have hnew (x y : P) (hxy : ind x - ind y = d + 1) := exists_chain_of_sub_eq s hs hxy
    fun m hm ↦ hglue s x y m hm hs fun x' y' h ↦ hd x' y' (by omega)
  classical
  let s' : ∀ x y, normalizedCubicalChainAlgebra (M x y) k := fun x y ↦
    if hxy : ind x - ind y = d + 1 then (hnew x y hxy).choose else s x y
  have hs' (x y : P) : s' x y ∈ cubicalChainGrading (M x y) k (ind y - ind x + 1) := by
    by_cases hxy : ind x - ind y = d + 1
    · simpa only [s', hxy, ↓reduceDIte] using (hnew x y hxy).choose_spec.1
    · simpa only [s', hxy, ↓reduceDIte] using hs x y
  -- The new chains only change the pairs of index difference `d + 1`, which do not enter the
  -- twisting sums of the pairs of index difference at most `d + 1`.
  have hsum (x y : P) (hxy : ind x - ind y ≤ d + 1) :
      twistingChainSum ind ι k s' x y = twistingChainSum ind ι k s x y :=
    twistingChainSum_congr hs' hs fun z h₁ h₂ ↦ by
      have hxz : ind x - ind z ≠ d + 1 := by omega
      have hzy : ind z - ind y ≠ d + 1 := by omega
      simp only [s', hxz, hzy, ↓reduceDIte, and_self]
  refine ⟨s', hs', fun x y hxy ↦ ?_⟩
  rw [hsum x y hxy]
  by_cases hxy' : ind x - ind y = d + 1
  · simp only [s', hxy', ↓reduceDIte]
    exact ⟨(hnew x y hxy').choose_spec.2.1, fun _ ↦ (hnew x y hxy').choose_spec.2.2⟩
  · simp only [s', hxy', ↓reduceDIte]
    exact hd x y (by omega)

/-- **Existence of representing chain systems.** Let `μ x y` be classes of the relative cubical
homology `H_{ind x - ind y - 1}(M x y, A x y)` satisfying the **gluing condition**: whenever a
family of chains `s` of the cohomological degrees `ind y - ind x + 1` satisfies the twisting
equation and represents the classes `μ` on the pairs of index difference less than that of
`(x, y)`, where `ind x - ind y = m + 2`, its twisting sum at `(x, y)` is the image of an
`m`-cycle of `A x y` whose class is the image of `μ x y` under the connecting morphism
`H_{m+1}(M x y, A x y) → H_m(A x y)`. Then some twisting chain system represents the classes
`μ`.

In index difference one no condition is needed. For associative composition maps the twisting
sum is a cycle of `M x y` (`TauCeti.cubicalChainDifferential_twistingChainSum`), and for
fundamental classes rel boundary of manifolds with corners, the gluing condition says that the
signed sum of the products of the fundamental chains of the boundary faces `M x z × M z y` is a
fundamental cycle of the boundary `A x y`. -/
theorem TwistingChainSystem.exists_isRepresenting
    (hglue : ∀ (s : ∀ x y, normalizedCubicalChainAlgebra (M x y) k) (x y : P) (m : ℕ)
      (hm : ind x - ind y = m + 2),
      (∀ x y, s x y ∈ cubicalChainGrading (M x y) k (ind y - ind x + 1)) →
      (∀ x' y', ind x' - ind y' < ind x - ind y →
        cubicalChainDifferential (M x' y') k (s x' y') = twistingChainSum ind ι k s x' y' ∧
          (ind y' < ind x' → IsRepresentingChain (s x' y') (μ x' y'))) →
      IsRepresentingCycle (twistingChainSum ind ι k s x y)
        (((TopPair.ofSubset (A x y)).cubicalHomologyδ k (ind x - ind y - 1).toNat m).hom
          (μ x y))) :
    ∃ S : TwistingChainSystem ind ι k, S.IsRepresenting A μ := by
  -- Induction on the largest index difference at which the conditions hold.
  have key (d : ℕ) : ∃ s : ∀ x y, normalizedCubicalChainAlgebra (M x y) k,
      (∀ x y, s x y ∈ cubicalChainGrading (M x y) k (ind y - ind x + 1)) ∧
      ∀ x y, ind x - ind y ≤ d →
        cubicalChainDifferential (M x y) k (s x y) = twistingChainSum ind ι k s x y ∧
          (ind y < ind x → IsRepresentingChain (s x y) (μ x y)) := by
    induction d with
    | zero =>
      refine ⟨0, fun _ _ ↦ zero_mem _, fun x y hxy ↦ ⟨?_, fun h ↦ by omega⟩⟩
      simp [twistingChainSum_def]
    | succ d ih =>
      obtain ⟨s, hs, hd⟩ := ih
      exact exists_succ d hglue s hs hd
  -- The index differences of the finitely many pairs are bounded.
  obtain ⟨s, hs, h⟩ := key (Finset.univ.sup fun p : P × P ↦ (ind p.1 - ind p.2).toNat)
  have hbound (x y : P) :
      ind x - ind y ≤ ((Finset.univ.sup fun p : P × P ↦ (ind p.1 - ind p.2).toNat : ℕ) : ℤ) :=
    (Int.self_le_toNat _).trans (Int.ofNat_le.2
      (Finset.le_sup (f := fun p : P × P ↦ (ind p.1 - ind p.2).toNat) (Finset.mem_univ (x, y))))
  exact ⟨⟨s, hs, fun x y ↦ (h x y (hbound x y)).1⟩, fun x y ↦ (h x y (hbound x y)).2⟩

/-- When all index differences are at most one, every family of classes of
`H₀(M x y, A x y)` is represented by a twisting chain system: the gluing condition is vacuous. -/
theorem TwistingChainSystem.exists_isRepresenting_of_sub_le_one
    (hind : ∀ x y, ind x - ind y ≤ 1) :
    ∃ S : TwistingChainSystem ind ι k, S.IsRepresenting A μ :=
  TwistingChainSystem.exists_isRepresenting fun _ x y m hm ↦ by
    have := hind x y
    omega

end Existence

end TauCeti
