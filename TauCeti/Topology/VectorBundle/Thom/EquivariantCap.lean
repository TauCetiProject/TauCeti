/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Twisted.EquivariantCap
public import TauCeti.Topology.VectorBundle.Thom.Homology

/-!
# The equivariant cap product with a Thom cocycle

Let a group `G` act on a real vector bundle `E → B` of rank `r`, on its total space, on the
complement `E₀` of the zero section and on the base, compatibly with the inclusion `E₀ ⊆ E` and the
projection `π : E ⟶ B`, and let `φ` be a relative cocycle of degree `r` of the Thom pair `(E, E₀)`
which, pulled back to `E`, satisfies `φ(g • c) = χ(g) φ(c)` for a character `χ : G →* kˣ`. If the
class of `φ` is a Thom class, then the equivariant cap product with `φ`,

`C(E, E₀; k) ⟶ (k_χ ⊗ C(B; k))[r]`,  `x ↦ ± π_*(x ⌢ φ)`

(`TopPair.singularChainsRepCap`), is a quasi-isomorphism of complexes of representations of `G`
(`TauCeti.quasiIso_singularChainsRepCap_thomPair`): forgetting the action, it is the chain-level
homology Thom isomorphism `TauCeti.quasiIso_pushforwardCapChainMap_thomPair`.

This is the chain-level, equivariant form of the homology Thom isomorphism used to compute the
homology of a Thom pair with local coefficients from a covering. For the pull-back `E'` of `E` to
its orientation double cover `B'`, with `G = ℤˣ` acting by the deck involution and `χ` the sign
character, the bundle `E'` is oriented, and a cocycle representing its Thom class which the deck
involution negates is semi-invariant. When `G` acts freely on the base, the twisted chains of the
base are projective representations (`TauCeti.projective_tensorLeft_singularChainsRep_X`). If
moreover the Thom pair maps to a pair `(Q, Q₀)` by quotient covering maps `E ⟶ Q` and `E₀ ⟶ Q₀`,
as for the pull-back to the orientation double cover, this quasi-isomorphism computes the homology
of `(Q, Q₀)` with twisted coefficients (`TopPair.twistedHomologyIsoHomologyCoinvariantsTensorObj`).
If also the base maps to a space `Z` by a quotient covering map `B ⟶ Z`, this is a Thom isomorphism
of the quotient: for every representation `D` of `G`,

`H_{q + r}(Q, Q₀; L_D) ≅ H_q(Z; L_{D ⊗ k_χ})`,

where `L_D` and `L_{D ⊗ k_χ}` are the local systems associated to `D` and to `D ⊗ k_χ`
(`TauCeti.quotientTwistedHomologyThomIso`). For `D` the trivial representation `k` this reads
`H_{q + r}(Q, Q₀; k) ≅ H_q(Z; L_{k_χ})` (`TauCeti.quotientSingularHomologyThomIso`). For the
pull-back to the orientation double cover, `(Q, Q₀)` is the Thom pair of the original bundle and `Z`
its base. In this orientation-cover application (`G = ℤˣ`, `χ = sign`) the coefficient system
`L_{k_χ}` is the one associated to `Rep.of (Representation.ofLinearCharacter sign)`, while the
orientation local system is associated to `Rep.ofDistribMulAction k ℤˣ k`
(`TauCeti.VectorBundleOrientationCover.associatedLocalSystemSignIso`); the identification of these
two sign representations is not part of this file.

## Main results

* `TauCeti.quasiIso_singularChainsRepCap_thomPair`: the equivariant cap product with a
  semi-invariant cocycle representing a Thom class is a quasi-isomorphism.
* `TauCeti.quotientTwistedHomologyThomIso`: the Thom isomorphism of a quotient of the Thom pair,
  with coefficients in associated local systems.
* `TauCeti.quotientSingularHomologyThomIso`: its case of constant coefficients on the quotient,
  `H_{q + r}(Q, Q₀; k) ≅ H_q(Z; L_{k_χ})`.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §10 and §12.
* E. H. Spanier, *Algebraic Topology*, McGraw-Hill (1966), Chapter 5, Section 7.
-/

public section

noncomputable section

open Bundle CategoryTheory Limits Module MonoidalCategory

universe u

namespace TauCeti

variable {B : Type u} [TopologicalSpace B] {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type u} [TopologicalSpace (TotalSpace F E)]
  [∀ b, AddCommMonoid (E b)] [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)]
  [FiberBundle F E] [VectorBundle ℝ F E] {k : Type u} [CommRing k] {G : Type u} [Group G]
  [MulAction G (thomPair F E).fst] [ContinuousConstSMul G (thomPair F E).fst]
  [MulAction G (thomPair F E).snd] [ContinuousConstSMul G (thomPair F E).snd]
  [MulAction G (TopCat.of B)] [ContinuousConstSMul G (TopCat.of B)]

/-- **The equivariant cap product with a Thom cocycle is a quasi-isomorphism.** Let `G` act on the
Thom pair `(E, E₀)` of a real vector bundle of rank `r` and on its base, compatibly with the
inclusion and the projection, and let `φ` be a relative cocycle of degree `r` which, pulled back to
`E`, satisfies `φ(g • c) = χ(g) φ(c)` (`TopPair.IsSemiInvariantCocycle`). If the class of `φ` is a
Thom class, then the equivariant cap product `C(E, E₀; k) ⟶ (k_χ ⊗ C(B; k))[r]` with `φ` is a
quasi-isomorphism of complexes of representations of `G`. -/
theorem quasiIso_singularChainsRepCap_thomPair
    (hP : ∀ (g : G) x, (thomPair F E).map (g • x) = g • (thomPair F E).map x)
    (hp₀ : ∀ (g : G) x, thomPairProj F E (g • x) = g • thomPairProj F E x) (χ : G →* kˣ)
    {φ : ((thomPair F E).singularCochainComplex (ModuleCat.of k k) k (ModuleCat.of k k)).cycles
      (finrank ℝ F)}
    (hφ : TopPair.IsSemiInvariantCocycle χ φ)
    (hu : IsThomClass F E
      (((thomPair F E).singularCochainComplex (ModuleCat.of k k) k (ModuleCat.of k k)).homologyπ
        (finrank ℝ F) φ)) :
    QuasiIso ((thomPair F E).singularChainsRepCap hp₀ χ hφ hP) :=
  (TopPair.quasiIso_singularChainsRepCap_iff _ hp₀ χ hφ hP).2
    (quasiIso_pushforwardCapChainMap_thomPair φ hu)

/-- **The Thom isomorphism of a quotient of an equivariant vector bundle.** Let `G` act on the Thom
pair `(E, E₀)` of a real vector bundle of rank `r` and on its base, compatibly with the inclusion
and the projection, let `(E, E₀) ⟶ (Q, Q₀)` restrict to quotient covering maps `E ⟶ Q` and
`E₀ ⟶ Q₀` and let `B ⟶ Z` be a quotient covering map, all for the action of `G`. If a relative
cocycle `φ` of degree `r`, semi-invariant for a character `χ : G →* kˣ`, represents a Thom class,
then for every representation `D` of `G`, `H_{q + r}(Q, Q₀; L_D) ≅ H_q(Z; L_{D ⊗ k_χ})`, where
`L_D` and `L_{D ⊗ k_χ}` are the local systems associated to `D` and to `D ⊗ k_χ`. -/
def quotientTwistedHomologyThomIso {P : TopPair.{u}} {ψ : thomPair F E ⟶ P}
    (hfst : IsQuotientCoveringMap (TopPair.Hom.fst ψ) G)
    (hsnd : IsQuotientCoveringMap (TopPair.Hom.snd ψ) G) {Z : TopCat.{u}} {p : TopCat.of B ⟶ Z}
    (hB : IsQuotientCoveringMap p G)
    (hP : ∀ (g : G) x, (thomPair F E).map (g • x) = g • (thomPair F E).map x)
    (hp₀ : ∀ (g : G) x, thomPairProj F E (g • x) = g • thomPairProj F E x) (χ : G →* kˣ)
    {φ : ((thomPair F E).singularCochainComplex (ModuleCat.of k k) k (ModuleCat.of k k)).cycles
      (finrank ℝ F)}
    (hφ : TopPair.IsSemiInvariantCocycle χ φ)
    (hu : IsThomClass F E
      (((thomPair F E).singularCochainComplex (ModuleCat.of k k) k (ModuleCat.of k k)).homologyπ
        (finrank ℝ F) φ))
    (D : Rep.{u} k G) (q : ℕ) :
    P.twistedHomology (hfst.associatedLocalSystem k D) (q + finrank ℝ F) ≅
      LocalCoefficientSystem.twistedHomology
        (hB.associatedLocalSystem k (D ⊗ Rep.of (Representation.ofLinearCharacter χ))) q :=
  haveI := quasiIso_singularChainsRepCap_thomPair hP hp₀ χ hφ hu
  TopPair.twistedHomologyIsoTwistedHomologyOfQuasiIso hfst hsnd hP hB χ D
    ((thomPair F E).singularChainsRepCap hp₀ χ hφ hP) q

/-- The isomorphism `TauCeti.quotientTwistedHomologyThomIso` is
`TopPair.twistedHomologyIsoTwistedHomologyOfQuasiIso` for the equivariant cap product with the
Thom cocycle, which is a quasi-isomorphism by `TauCeti.quasiIso_singularChainsRepCap_thomPair`. -/
theorem quotientTwistedHomologyThomIso_def {P : TopPair.{u}} {ψ : thomPair F E ⟶ P}
    (hfst : IsQuotientCoveringMap (TopPair.Hom.fst ψ) G)
    (hsnd : IsQuotientCoveringMap (TopPair.Hom.snd ψ) G) {Z : TopCat.{u}} {p : TopCat.of B ⟶ Z}
    (hB : IsQuotientCoveringMap p G)
    (hP : ∀ (g : G) x, (thomPair F E).map (g • x) = g • (thomPair F E).map x)
    (hp₀ : ∀ (g : G) x, thomPairProj F E (g • x) = g • thomPairProj F E x) (χ : G →* kˣ)
    {φ : ((thomPair F E).singularCochainComplex (ModuleCat.of k k) k (ModuleCat.of k k)).cycles
      (finrank ℝ F)}
    (hφ : TopPair.IsSemiInvariantCocycle χ φ)
    (hu : IsThomClass F E
      (((thomPair F E).singularCochainComplex (ModuleCat.of k k) k (ModuleCat.of k k)).homologyπ
        (finrank ℝ F) φ))
    (D : Rep.{u} k G) (q : ℕ) :
    quotientTwistedHomologyThomIso hfst hsnd hB hP hp₀ χ hφ hu D q =
      haveI := quasiIso_singularChainsRepCap_thomPair hP hp₀ χ hφ hu
      TopPair.twistedHomologyIsoTwistedHomologyOfQuasiIso hfst hsnd hP hB χ D
        ((thomPair F E).singularChainsRepCap hp₀ χ hφ hP) q :=
  (rfl)

/-- **The Thom isomorphism of a quotient of an equivariant vector bundle, with constant
coefficients upstairs.** Under the hypotheses of `TauCeti.quotientTwistedHomologyThomIso`,
`H_{q + r}(Q, Q₀; k) ≅ H_q(Z; L_{k_χ})`, where `L_{k_χ}` is the local system associated to the
one-dimensional representation of `χ`. -/
def quotientSingularHomologyThomIso {P : TopPair.{u}} {ψ : thomPair F E ⟶ P}
    (hfst : IsQuotientCoveringMap (TopPair.Hom.fst ψ) G)
    (hsnd : IsQuotientCoveringMap (TopPair.Hom.snd ψ) G) {Z : TopCat.{u}} {p : TopCat.of B ⟶ Z}
    (hB : IsQuotientCoveringMap p G)
    (hP : ∀ (g : G) x, (thomPair F E).map (g • x) = g • (thomPair F E).map x)
    (hp₀ : ∀ (g : G) x, thomPairProj F E (g • x) = g • thomPairProj F E x) (χ : G →* kˣ)
    {φ : ((thomPair F E).singularCochainComplex (ModuleCat.of k k) k (ModuleCat.of k k)).cycles
      (finrank ℝ F)}
    (hφ : TopPair.IsSemiInvariantCocycle χ φ)
    (hu : IsThomClass F E
      (((thomPair F E).singularCochainComplex (ModuleCat.of k k) k (ModuleCat.of k k)).homologyπ
        (finrank ℝ F) φ))
    (q : ℕ) :
    P.singularHomology (ModuleCat.of k k) (q + finrank ℝ F) ≅
      LocalCoefficientSystem.twistedHomology
        (hB.associatedLocalSystem k (Rep.of (Representation.ofLinearCharacter χ))) q :=
  haveI := quasiIso_singularChainsRepCap_thomPair hP hp₀ χ hφ hu
  TopPair.singularHomologyIsoTwistedHomologyOfQuasiIso hfst hsnd hP hB χ
    ((thomPair F E).singularChainsRepCap hp₀ χ hφ hP) q

/-- The isomorphism `TauCeti.quotientSingularHomologyThomIso` is
`TopPair.singularHomologyIsoTwistedHomologyOfQuasiIso` for the equivariant cap product with the
Thom cocycle, which is a quasi-isomorphism by `TauCeti.quasiIso_singularChainsRepCap_thomPair`. -/
theorem quotientSingularHomologyThomIso_def {P : TopPair.{u}} {ψ : thomPair F E ⟶ P}
    (hfst : IsQuotientCoveringMap (TopPair.Hom.fst ψ) G)
    (hsnd : IsQuotientCoveringMap (TopPair.Hom.snd ψ) G) {Z : TopCat.{u}} {p : TopCat.of B ⟶ Z}
    (hB : IsQuotientCoveringMap p G)
    (hP : ∀ (g : G) x, (thomPair F E).map (g • x) = g • (thomPair F E).map x)
    (hp₀ : ∀ (g : G) x, thomPairProj F E (g • x) = g • thomPairProj F E x) (χ : G →* kˣ)
    {φ : ((thomPair F E).singularCochainComplex (ModuleCat.of k k) k (ModuleCat.of k k)).cycles
      (finrank ℝ F)}
    (hφ : TopPair.IsSemiInvariantCocycle χ φ)
    (hu : IsThomClass F E
      (((thomPair F E).singularCochainComplex (ModuleCat.of k k) k (ModuleCat.of k k)).homologyπ
        (finrank ℝ F) φ))
    (q : ℕ) :
    quotientSingularHomologyThomIso hfst hsnd hB hP hp₀ χ hφ hu q =
      haveI := quasiIso_singularChainsRepCap_thomPair hP hp₀ χ hφ hu
      TopPair.singularHomologyIsoTwistedHomologyOfQuasiIso hfst hsnd hP hB χ
        ((thomPair F E).singularChainsRepCap hp₀ χ hφ hP) q :=
  (rfl)

end TauCeti
