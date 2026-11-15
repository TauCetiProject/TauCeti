/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Cubical.MonoidAlgebra.ContinuationChainSystem
public import TauCeti.AlgebraicTopology.Singular.Cubical.MonoidAlgebra.Relative

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
the base are the Barraud–Cornea twisting cocycle. In the same way, continuation chain systems
(`TauCeti.ContinuationChainSystem.IsRepresenting`) and parametrized chain systems
(`TauCeti.ParametrizedChainSystem.IsRepresenting`) represent classes of the spaces of
continuation trajectories of a homotopy of Morse functions, of dimension `ind x - indQ y`, and of
the spaces of trajectories of a one-parameter family of such homotopies, of dimension
`ind x - indQ y + 1`. Their push-forwards are the continuation cocycles relating the
Barraud–Cornea cocycles of two choices of data, and the parametrized cocycles showing that the
resulting continuation maps do not depend on the homotopy, up to chain homotopy.

All three are constructed by the same induction on the dimension
(`TauCeti.exists_forall_cubicalChainDifferential_eq_and_isRepresentingChain`): the boundary of
each chain is prescribed by a sum `F s x y` of products of chains of smaller dimension. Once the
chains of the pairs of smaller dimension are chosen, suppose that `F s x y` is a cycle of
`A x y` whose class there is the image of `μ x y` under the connecting morphism
`H_{m+1}(M x y, A x y) → H_m(A x y)`. Then the relative class lifts to a chain whose boundary is
exactly `F s x y` (`TopPair.exists_boundary_eq_of_cubicalHomologyδ_eq`). When the composition
maps are associative, the twisting, continuation and parametrized sums are cycles of the ambient
space (`TauCeti.cubicalChainDifferential_twistingChainSum`,
`TauCeti.cubicalChainDifferential_continuationChainSum`,
`TauCeti.cubicalChainDifferential_parametrizedChainSum`), so what has to be checked is that they
are supported in the boundary and have the right class there. This **gluing condition** is the
only input: for fundamental classes of manifolds with corners whose boundary is glued from the
products of the lower-dimensional spaces, it says that the signed sum of the products of
fundamental chains of the faces is a fundamental cycle of the boundary, since the connecting
morphism sends the fundamental class rel boundary to the fundamental class of the boundary. In
dimension zero there is no condition: every class of `H₀` is represented by a `0`-chain, and the
prescribed boundary vanishes for degree reasons.

## Main definitions

* `TauCeti.TwistingChainSystem.IsRepresenting`,
  `TauCeti.ContinuationChainSystem.IsRepresenting`,
  `TauCeti.ParametrizedChainSystem.IsRepresenting`: a twisting, continuation or parametrized
  chain system whose chains represent prescribed relative classes, in the sense of
  `TauCeti.IsRepresentingChain`.

## Main results

* `TauCeti.TwistingChainSystem.exists_isRepresenting`,
  `TauCeti.ContinuationChainSystem.exists_isRepresenting`,
  `TauCeti.ParametrizedChainSystem.exists_isRepresenting`: under the gluing condition, a
  twisting, continuation or parametrized chain system representing the classes `μ` exists.
* `TauCeti.TwistingChainSystem.exists_isRepresenting_of_sub_le_one`: when all index differences
  are at most one, every family of classes is represented.

## References

* J.-F. Barraud, O. Cornea, *Lagrangian intersections and the Serre spectral sequence*, Ann. of
  Math. 166 (2007), 657–722, Section 2 and Appendix A.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, Chapters 5 and 6.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §1.4, Definitions 1.10 and 1.11.
-/

public section

noncomputable section

open CategoryTheory Limits TauCeti

universe u

namespace TauCeti

open NormalizedCubicalChain

/-! ### Representing twisting chain systems -/

section Twisting

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

variable {μ : ∀ x y, ((TopPair.ofSubset (A x y)).cubicalChainComplex k).homology
  (ind x - ind y - 1).toNat}

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
  obtain ⟨s, hs, h⟩ := exists_forall_cubicalChainDifferential_eq_and_isRepresentingChain
    (deg := fun x y ↦ ind y - ind x + 1) (F := twistingChainSum ind ι k) (μ := μ)
    (fun x y h ↦ by omega)
    (fun s s' x y hs hs' h ↦
      twistingChainSum_congr hs hs' fun z h₁ h₂ ↦ ⟨h x z (by omega), h z y (by omega)⟩)
    (fun s x y hs h ↦ by
      -- In index difference at most one no pair lies strictly between `y` and `x`.
      rw [twistingChainSum_congr (s' := 0) hs (fun _ _ ↦ zero_mem _) fun z h₁ h₂ ↦ by omega]
      simp [twistingChainSum_def])
    (fun s x y m hm _ hs hd ↦ hglue s x y m (by omega) hs fun x' y' h ↦
      ⟨(hd x' y' (by omega)).1, fun h' ↦ (hd x' y' (by omega)).2 (by omega)⟩)
  exact ⟨⟨s, hs, fun x y ↦ (h x y).1⟩, fun x y hxy ↦ (h x y).2 (by omega)⟩

/-- When all index differences are at most one, every family of classes of
`H₀(M x y, A x y)` is represented by a twisting chain system: the gluing condition is vacuous. -/
theorem TwistingChainSystem.exists_isRepresenting_of_sub_le_one
    (hind : ∀ x y, ind x - ind y ≤ 1) :
    ∃ S : TwistingChainSystem ind ι k, S.IsRepresenting A μ :=
  TwistingChainSystem.exists_isRepresenting fun _ x y m hm ↦ by
    have := hind x y
    omega

end Twisting

/-! ### Representing continuation chain systems -/

section Continuation

variable {P : Type*} [Fintype P] {ind : P → ℤ} {M : P → P → Type*}
  [∀ x y, TopologicalSpace (M x y)] {Q : Type*} [Fintype Q] {indQ : Q → ℤ} {M' : Q → Q → Type*}
  [∀ x y, TopologicalSpace (M' x y)] {N : P → Q → TopCat.{u}}
  {ι : ∀ x y z, C(M x y × M y z, M x z)} {ι' : ∀ x y z, C(M' x y × M' y z, M' x z)}
  {κ : ∀ x y z, C(M x y × N y z, N x z)} {κ' : ∀ x y z, C(N x y × M' y z, N x z)}
  {k : Type u} [CommRing k] {S : TwistingChainSystem ind ι k} {S' : TwistingChainSystem indQ ι' k}
  {A : ∀ x y, Set (N x y)}

namespace ContinuationChainSystem

variable (A) in
/-- A continuation chain system **represents** the classes `μ x y` of the relative cubical
homology `H_{ind x - indQ y}(N x y, A x y)` when the chain of every pair `(x, y)` with
`indQ y ≤ ind x` represents `μ x y`. When `A x y` is the boundary of a manifold with corners
`N x y` of continuation trajectories and `μ x y` is its fundamental class rel boundary, the
push-forwards of these chains form the continuation cocycle between the Barraud–Cornea cocycles
of the two ends of the homotopy. -/
def IsRepresenting (T : ContinuationChainSystem κ κ' S S')
    (μ : ∀ x y, ((TopPair.ofSubset (A x y)).cubicalChainComplex k).homology
      (ind x - indQ y).toNat) : Prop :=
  ∀ x y, indQ y ≤ ind x → IsRepresentingChain (T.chain x y) (μ x y)

theorem isRepresenting_iff (T : ContinuationChainSystem κ κ' S S')
    (μ : ∀ x y, ((TopPair.ofSubset (A x y)).cubicalChainComplex k).homology
      (ind x - indQ y).toNat) :
    T.IsRepresenting A μ ↔ ∀ x y, indQ y ≤ ind x → IsRepresentingChain (T.chain x y) (μ x y) :=
  Iff.rfl

end ContinuationChainSystem

variable {μ : ∀ x y, ((TopPair.ofSubset (A x y)).cubicalChainComplex k).homology
  (ind x - indQ y).toNat}

variable (κ κ' S S') in
/-- **Existence of representing continuation chain systems.** Let `S` and `S'` be twisting chain
systems and let `μ x y` be classes of the relative cubical homology
`H_{ind x - indQ y}(N x y, A x y)` satisfying the **gluing condition**: whenever a family of
chains `ν` of the cohomological degrees `indQ y - ind x` satisfies the continuation equation and
represents the classes `μ` on the pairs of index difference less than that of `(x, y)`, where
`ind x - indQ y = m + 1`, its continuation sum at `(x, y)` is the image of an `m`-cycle of
`A x y` whose class is the image of `μ x y` under the connecting morphism
`H_{m+1}(N x y, A x y) → H_m(A x y)`. Then some continuation chain system from `S` to `S'`
represents the classes `μ`.

In index difference zero no condition is needed. For associative composition maps the
continuation sum is a cycle of `N x y` (`TauCeti.cubicalChainDifferential_continuationChainSum`),
and for fundamental classes rel boundary of manifolds with corners, the gluing condition says that
the signed sum of the products of the chains of the boundary faces `M x z × N z y` and
`N x z × M' z y` is a fundamental cycle of the boundary `A x y`. -/
theorem ContinuationChainSystem.exists_isRepresenting
    (hglue : ∀ (ν : ∀ x y, normalizedCubicalChainAlgebra (N x y) k) (x : P) (y : Q) (m : ℕ)
      (hm : ind x - indQ y = m + 1),
      (∀ x y, ν x y ∈ cubicalChainGrading (N x y) k (indQ y - ind x)) →
      (∀ x' y', ind x' - indQ y' < ind x - indQ y →
        cubicalChainDifferential (N x' y') k (ν x' y') =
            continuationChainSum ind indQ κ κ' k S.chain S'.chain ν x' y' ∧
          (indQ y' ≤ ind x' → IsRepresentingChain (ν x' y') (μ x' y'))) →
      IsRepresentingCycle (continuationChainSum ind indQ κ κ' k S.chain S'.chain ν x y)
        (((TopPair.ofSubset (A x y)).cubicalHomologyδ k (ind x - indQ y).toNat m).hom
          (μ x y))) :
    ∃ T : ContinuationChainSystem κ κ' S S', T.IsRepresenting A μ := by
  obtain ⟨ν, hν, h⟩ := exists_forall_cubicalChainDifferential_eq_and_isRepresentingChain
    (deg := fun x y ↦ indQ y - ind x)
    (F := continuationChainSum ind indQ κ κ' k S.chain S'.chain) (μ := μ)
    (fun x y h ↦ by omega)
    (fun ν ν' x y _ _ h ↦ continuationChainSum_congr S.mem_graded S'.mem_graded
      (fun z hz ↦ h z y (by omega)) fun z hz ↦ h x z (by omega))
    (fun ν x y hν h ↦ continuationChainSum_eq_zero_of_le S.mem_graded S'.mem_graded hν
      (by omega))
    (fun ν x y m hm _ hν hd ↦ hglue ν x y m (by omega) hν fun x' y' h ↦
      ⟨(hd x' y' (by omega)).1, fun h' ↦ (hd x' y' (by omega)).2 (by omega)⟩)
  exact ⟨⟨ν, hν, fun x y ↦ (h x y).1⟩, fun x y hxy ↦ (h x y).2 (by omega)⟩

end Continuation

/-! ### Representing parametrized chain systems -/

section Parametrized

variable {P : Type*} [Fintype P] {ind : P → ℤ} {M : P → P → Type*}
  [∀ x y, TopologicalSpace (M x y)] {Q : Type*} [Fintype Q] {indQ : Q → ℤ} {M' : Q → Q → Type*}
  [∀ x y, TopologicalSpace (M' x y)] {N₀ N₁ : P → Q → Type*} [∀ x y, TopologicalSpace (N₀ x y)]
  [∀ x y, TopologicalSpace (N₁ x y)] {H : P → Q → TopCat.{u}}
  {ι : ∀ x y z, C(M x y × M y z, M x z)} {ι' : ∀ x y z, C(M' x y × M' y z, M' x z)}
  {κ₀ : ∀ x y z, C(M x y × N₀ y z, N₀ x z)} {κ₀' : ∀ x y z, C(N₀ x y × M' y z, N₀ x z)}
  {κ₁ : ∀ x y z, C(M x y × N₁ y z, N₁ x z)} {κ₁' : ∀ x y z, C(N₁ x y × M' y z, N₁ x z)}
  {κH : ∀ x y z, C(M x y × H y z, H x z)} {κH' : ∀ x y z, C(H x y × M' y z, H x z)}
  {j₀ : ∀ x y, C(N₀ x y, H x y)} {j₁ : ∀ x y, C(N₁ x y, H x y)} {k : Type u} [CommRing k]
  {S : TwistingChainSystem ind ι k} {S' : TwistingChainSystem indQ ι' k}
  {T₀ : ContinuationChainSystem κ₀ κ₀' S S'} {T₁ : ContinuationChainSystem κ₁ κ₁' S S'}
  {A : ∀ x y, Set (H x y)}

namespace ParametrizedChainSystem

variable (A) in
/-- A parametrized chain system **represents** the classes `μ x y` of the relative cubical
homology `H_{ind x - indQ y + 1}(H x y, A x y)` when the chain of every pair `(x, y)` with
`indQ y ≤ ind x + 1` represents `μ x y`. When `A x y` is the boundary of a manifold with corners
`H x y` of trajectories of a one-parameter family of homotopies and `μ x y` is its fundamental
class rel boundary, the push-forwards of these chains form the parametrized cocycle between the
continuation cocycles of the two ends of the family. -/
def IsRepresenting (η : ParametrizedChainSystem κH κH' j₀ j₁ T₀ T₁)
    (μ : ∀ x y, ((TopPair.ofSubset (A x y)).cubicalChainComplex k).homology
      (ind x - indQ y + 1).toNat) : Prop :=
  ∀ x y, indQ y ≤ ind x + 1 → IsRepresentingChain (η.chain x y) (μ x y)

theorem isRepresenting_iff (η : ParametrizedChainSystem κH κH' j₀ j₁ T₀ T₁)
    (μ : ∀ x y, ((TopPair.ofSubset (A x y)).cubicalChainComplex k).homology
      (ind x - indQ y + 1).toNat) :
    η.IsRepresenting A μ ↔
      ∀ x y, indQ y ≤ ind x + 1 → IsRepresentingChain (η.chain x y) (μ x y) :=
  Iff.rfl

end ParametrizedChainSystem

variable {μ : ∀ x y, ((TopPair.ofSubset (A x y)).cubicalChainComplex k).homology
  (ind x - indQ y + 1).toNat}

variable (κH κH' j₀ j₁ T₀ T₁) in
/-- **Existence of representing parametrized chain systems.** Let `T₀` and `T₁` be continuation
chain systems and let `μ x y` be classes of the relative cubical homology
`H_{ind x - indQ y + 1}(H x y, A x y)` satisfying the **gluing condition**: whenever a family of
chains `h` of the cohomological degrees `indQ y - ind x - 1` satisfies the parametrized equation
and represents the classes `μ` on the pairs of index difference less than that of `(x, y)`, where
`ind x - indQ y = m`, its parametrized sum at `(x, y)` is the image of an `m`-cycle of `A x y`
whose class is the image of `μ x y` under the connecting morphism
`H_{m+1}(H x y, A x y) → H_m(A x y)`. Then some parametrized chain system between `T₀` and `T₁`
represents the classes `μ`.

In index difference `-1` no condition is needed. For associative composition maps compatible with
the inclusions `j₀` and `j₁`, the parametrized sum is a cycle of `H x y`
(`TauCeti.cubicalChainDifferential_parametrizedChainSum`), and for fundamental classes rel
boundary of manifolds with corners, the gluing condition says that the images of the
continuation chains of the two ends, together with the signed sum of the products of the chains of
the boundary faces `M x z × H z y` and `H x z × M' z y`, form a fundamental cycle of the boundary
`A x y`. -/
theorem ParametrizedChainSystem.exists_isRepresenting
    (hglue : ∀ (h : ∀ x y, normalizedCubicalChainAlgebra (H x y) k) (x : P) (y : Q) (m : ℕ)
      (hm : ind x - indQ y = m),
      (∀ x y, h x y ∈ cubicalChainGrading (H x y) k (indQ y - ind x - 1)) →
      (∀ x' y', ind x' - indQ y' < ind x - indQ y →
        cubicalChainDifferential (H x' y') k (h x' y') =
            parametrizedChainSum ind indQ κH κH' j₀ j₁ k S.chain S'.chain T₀.chain T₁.chain h
              x' y' ∧
          (indQ y' ≤ ind x' + 1 → IsRepresentingChain (h x' y') (μ x' y'))) →
      IsRepresentingCycle
        (parametrizedChainSum ind indQ κH κH' j₀ j₁ k S.chain S'.chain T₀.chain T₁.chain h x y)
        (((TopPair.ofSubset (A x y)).cubicalHomologyδ k (ind x - indQ y + 1).toNat m).hom
          (μ x y))) :
    ∃ η : ParametrizedChainSystem κH κH' j₀ j₁ T₀ T₁, η.IsRepresenting A μ := by
  obtain ⟨h, hh, hd⟩ := exists_forall_cubicalChainDifferential_eq_and_isRepresentingChain
    (deg := fun x y ↦ indQ y - ind x - 1)
    (F := parametrizedChainSum ind indQ κH κH' j₀ j₁ k S.chain S'.chain T₀.chain T₁.chain)
    (μ := μ) (fun x y h ↦ by omega)
    (fun h h' x y _ _ hhh' ↦ parametrizedChainSum_congr S.mem_graded S'.mem_graded
      (fun z hz ↦ hhh' z y (by omega)) fun z hz ↦ hhh' x z (by omega))
    (fun h x y hh hxy ↦ parametrizedChainSum_eq_zero_of_lt S.mem_graded S'.mem_graded
      T₀.mem_graded T₁.mem_graded hh (by omega))
    (fun h x y m hm _ hh hd ↦ hglue h x y m (by omega) hh fun x' y' hxy ↦
      ⟨(hd x' y' (by omega)).1, fun h' ↦ (hd x' y' (by omega)).2 (by omega)⟩)
  exact ⟨⟨h, hh, fun x y ↦ (hd x y).1⟩, fun x y hxy ↦ (hd x y).2 (by omega)⟩

end Parametrized

end TauCeti
