/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Cubical.MonoidAlgebra.ChainSystemHomotopy
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Cubical

/-!
# Uniqueness of representing chain systems on spaces with collared boundaries

Two twisting chain systems representing the same relative classes `μ x y` of
`H_{ind x - ind y - 1}(M x y, A x y)` are joined by a homotopy
(`TauCeti.TwistingChainSystem.IsRepresenting.nonempty_homotopy`), provided the composition maps are
associative and land in the subspaces `A x y`, and the maps
`H_{ind x - ind y - 1}(M x y) → H_{ind x - ind y - 1}(M x y, A x y)` are injective. Likewise two
continuation chain systems representing the same classes are joined by a parametrized chain system
(`TauCeti.ContinuationChainSystem.IsRepresenting.nonempty_parametrizedChainSystem`) under the
corresponding injectivity.

This file discharges the injectivity for the spaces on which Barraud and Cornea build representing
chain systems: each `M x y` is a compact Hausdorff space containing a manifold of dimension
`ind x - ind y - 1` as an open subset, whose complement `A x y` is collared, as for a compact
topological manifold with boundary or with corners and its boundary. Then the top homology of
`M x y` embeds in its homology relative to `A x y`
(`TauCeti.injective_homologyMap_cokernel_π_of_isCollared`). So:

* any two twisting chain systems on such spaces representing the same classes are homotopic
  (`TauCeti.TwistingChainSystem.IsRepresenting.nonempty_homotopy_of_isCollared`);
* any two continuation chain systems on such spaces representing the same classes are joined by
  a parametrized chain system
  (`TauCeti.ContinuationChainSystem.IsRepresenting.nonempty_parametrizedChainSystem_of_isCollared`).

These hold in every index difference and with coefficients in every commutative ring: they are
the uniqueness statement of Barraud–Damian–Humilière–Oancea, Proposition 5.2.8, for every family
of spaces with this structure. The existence of representing chain systems of fundamental classes
on the same spaces, when `1` is the only unit of the coefficients, is
`TauCeti.TwistingChainSystem.exists_isRepresenting_of_subsingleton_units`. For the Morse
trajectory spaces in index differences at most two, uniqueness is proved directly from the
discreteness of their boundaries
(`TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.nonempty_homotopy_of_isRepresenting`).

## Main results

* `TauCeti.TwistingChainSystem.IsRepresenting.nonempty_homotopy_of_isCollared`: representing
  twisting chain systems on compact spaces with manifold interiors and collared boundaries are
  unique up to homotopy.
* `TauCeti.ContinuationChainSystem.IsRepresenting.nonempty_parametrizedChainSystem_of_isCollared`:
  representing continuation chain systems on such spaces are unique up to a parametrized chain
  system.

## References

* J.-F. Barraud, O. Cornea, *Lagrangian intersections and the Serre spectral sequence*, Ann. of
  Math. (2) 166 (2007), 657–722, Lemma 2.2.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, Propositions 5.2.6 and 5.2.8.
-/

public section

open CategoryTheory Limits Module Set Topology

universe u

namespace TauCeti

variable {P : Type*} [Fintype P] {ind : P → ℤ} {k : Type u} [CommRing k]

section Twisting

variable {M : P → P → TopCat.{u}} {ι : ∀ x y z, C(M x y × M y z, M x z)}
  [∀ x y, T2Space (M x y)] [∀ x y, CompactSpace (M x y)]
  {N : P → P → Type u} [∀ x y, TopologicalSpace (N x y)] {j : ∀ x y, N x y → M x y}
  {F : P → P → Type u} [∀ x y, NormedAddCommGroup (F x y)] [∀ x y, NormedSpace ℝ (F x y)]
  [∀ x y, FiniteDimensional ℝ (F x y)] [∀ x y, ChartedSpace (F x y) (N x y)]
  {μ : ∀ x y, ((TopPair.ofSubset (range (j x y))ᶜ).cubicalChainComplex k).homology
    (ind x - ind y - 1).toNat}
  {S S' : TwistingChainSystem ind ι k}

/-- **Representing chain systems on spaces with collared boundaries are homotopic.** Let each
`M x y` be a compact Hausdorff space and `j x y : N x y → M x y` an open embedding of a manifold
of dimension `ind x - ind y - 1` whose complement `∂M x y` is collared, whenever `ind y < ind x`.
For associative composition maps `ι` landing in the boundaries, any two twisting chain systems
representing the same classes of `H_{ind x - ind y - 1}(M x y, ∂M x y; k)` are joined by a
homotopy. -/
theorem TwistingChainSystem.IsRepresenting.nonempty_homotopy_of_isCollared
    (hS : S.IsRepresenting (fun x y ↦ (range (j x y))ᶜ) μ)
    (hS' : S'.IsRepresenting (fun x y ↦ (range (j x y))ᶜ) μ)
    (hj : ∀ x y, IsOpenEmbedding (j x y))
    (hF : ∀ x y, ind y < ind x → finrank ℝ (F x y) = (ind x - ind y - 1).toNat)
    (hcol : ∀ x y, ind y < ind x → IsCollared (Subtype.val : ↥(range (j x y))ᶜ → M x y))
    (hι : ∀ x w z y (a : M x w) (b : M w z) (c : M z y),
      ι x z y (ι x w z (a, b), c) = ι x w y (a, ι w z y (b, c)))
    (hA : ∀ x z y p, ι x z y p ∈ (range (j x y))ᶜ) :
    Nonempty (S.Homotopy S') :=
  hS.nonempty_homotopy hS' hι hA fun x y hyx ↦
    injective_homologyMap_cokernel_π_of_isCollared (hj x y) (hF x y hyx)
      (hj x y).isOpen_range.isClosed_compl.isCompact (hcol x y hyx)

end Twisting

section Continuation

variable {M : P → P → Type*} [∀ x y, TopologicalSpace (M x y)] {Q : Type*} [Fintype Q]
  {indQ : Q → ℤ} {M' : Q → Q → Type*} [∀ x y, TopologicalSpace (M' x y)]
  {N : P → Q → TopCat.{u}} [∀ x y, T2Space (N x y)] [∀ x y, CompactSpace (N x y)]
  {ι : ∀ x y z, C(M x y × M y z, M x z)} {ι' : ∀ x y z, C(M' x y × M' y z, M' x z)}
  {κ : ∀ x y z, C(M x y × N y z, N x z)} {κ' : ∀ x y z, C(N x y × M' y z, N x z)}
  {S : TwistingChainSystem ind ι k} {S' : TwistingChainSystem indQ ι' k}
  {T₀ T₁ : ContinuationChainSystem κ κ' S S'}
  {O : P → Q → Type u} [∀ x y, TopologicalSpace (O x y)] {j : ∀ x y, O x y → N x y}
  {F : P → Q → Type u} [∀ x y, NormedAddCommGroup (F x y)] [∀ x y, NormedSpace ℝ (F x y)]
  [∀ x y, FiniteDimensional ℝ (F x y)] [∀ x y, ChartedSpace (F x y) (O x y)]
  {ν : ∀ x y, ((TopPair.ofSubset (range (j x y))ᶜ).cubicalChainComplex k).homology
    (ind x - indQ y).toNat}

/-- **Representing continuation chain systems on spaces with collared boundaries are joined by a
parametrized chain system.** Let each `N x y` be a compact Hausdorff space and
`j x y : O x y → N x y` an open embedding of a manifold of dimension `ind x - indQ y` whose
complement `∂N x y` is collared, whenever `indQ y ≤ ind x`. For associative composition maps `κ`
and `κ'` landing in the boundaries, any two continuation chain systems from `S` to `S'`
representing the same classes of `H_{ind x - indQ y}(N x y, ∂N x y; k)` are joined by a
parametrized chain system on the spaces `N x y` themselves, included by the identities. -/
theorem ContinuationChainSystem.IsRepresenting.nonempty_parametrizedChainSystem_of_isCollared
    (hT₀ : T₀.IsRepresenting (fun x y ↦ (range (j x y))ᶜ) ν)
    (hT₁ : T₁.IsRepresenting (fun x y ↦ (range (j x y))ᶜ) ν)
    (hj : ∀ x y, IsOpenEmbedding (j x y))
    (hF : ∀ x y, indQ y ≤ ind x → finrank ℝ (F x y) = (ind x - indQ y).toNat)
    (hcol : ∀ x y, indQ y ≤ ind x → IsCollared (Subtype.val : ↥(range (j x y))ᶜ → N x y))
    (hκ : ∀ x w z y (a : M x w) (b : M w z) (c : N z y),
      κ x z y (ι x w z (a, b), c) = κ x w y (a, κ w z y (b, c)))
    (hκκ' : ∀ x w z y (a : M x w) (b : N w z) (c : M' z y),
      κ' x z y (κ x w z (a, b), c) = κ x w y (a, κ' w z y (b, c)))
    (hκ' : ∀ x w z y (a : N x w) (b : M' w z) (c : M' z y),
      κ' x z y (κ' x w z (a, b), c) = κ' x w y (a, ι' w z y (b, c)))
    (hB : ∀ x z y p, κ x z y p ∈ (range (j x y))ᶜ)
    (hB' : ∀ x z y p, κ' x z y p ∈ (range (j x y))ᶜ) :
    Nonempty (ParametrizedChainSystem κ κ' (fun x y ↦ ContinuousMap.id (N x y))
      (fun x y ↦ ContinuousMap.id (N x y)) T₀ T₁) :=
  hT₀.nonempty_parametrizedChainSystem hT₁ hκ hκκ' hκ' hB hB' fun x y hyx ↦
    injective_homologyMap_cokernel_π_of_isCollared (hj x y) (hF x y hyx)
      (hj x y).isOpen_range.isClosed_compl.isCompact (hcol x y hyx)

end Continuation

end TauCeti
