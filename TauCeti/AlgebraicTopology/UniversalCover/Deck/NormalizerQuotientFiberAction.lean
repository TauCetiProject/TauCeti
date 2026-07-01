/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.AlgebraicTopology.UniversalCover.Deck.SubgroupFiberOrbit

/-!
# Normalizer-quotient actions on subgroup fibre quotients

For a subgroup `H ≤ Deck p`, the normalizer of `H` acts on the quotient of a fibre by
`H`-orbits: a normalizer representative sends the class of `e` to the class of its deck
translate. Elements of `H` act trivially on this quotient, so the action descends to the
normalizer quotient `N(H) / H`.

This is the fibre-level action bookkeeping needed before the universal-covers roadmap can
identify the deck group of the cover attached to `H` with `N(H) / H`.

## Main declarations

* `TauCeti.Deck.normalizerSubgroupFiberOrbitEquiv`: the permutation of the `H`-fibre
  quotient induced by one normalizer representative.
* `TauCeti.Deck.normalizerSubgroupFiberOrbitPermHom`: the homomorphism from the normalizer
  to permutations of the `H`-fibre quotient.
* `TauCeti.Deck.normalizerQuotientSubgroupFiberOrbitPermHom`: the descended homomorphism
  from `N(H) / H`.
* `TauCeti.Deck.instNormalizerQuotientSubgroupFiberOrbitMulAction`: the resulting action of
  `N(H) / H` on `SubgroupFiberOrbitQuotient H b`.

## References

This supplies a small prerequisite for `TauCetiRoadmap/UniversalCovers/README.md`, Stage 2,
item 8: for the cover attached to `H`, the deck group is `N(H)/H`, with the regular case
specializing to `π₁(X, x₀)/H`.
-/

public section

namespace TauCeti

namespace Deck

variable {E B : Type*} [TopologicalSpace E] {p : E → B} {b : B}

private lemma normalizer_smul_mem_orbit (H : Subgroup (Deck p))
    (φ : _root_.Subgroup.normalizer (H : Set (Deck p)))
    {e e' : p ⁻¹' {b}} (hee' : e ∈ MulAction.orbit H e') :
    (φ : Deck p) • e ∈ MulAction.orbit H ((φ : Deck p) • e') := by
  rcases hee' with ⟨ψ, hψ⟩
  refine ⟨⟨(φ : Deck p) * ψ * (φ : Deck p)⁻¹, ?_⟩, ?_⟩
  · exact ((Subgroup.mem_normalizer_iff.mp φ.2) (ψ : Deck p)).1 ψ.2
  · rw [← hψ]
    simp [Subgroup.smul_def, mul_smul]

/-- A normalizer representative acts on the quotient of one fibre by `H`-orbits. -/
@[expose] def normalizerSubgroupFiberOrbitMap (H : Subgroup (Deck p))
    (φ : _root_.Subgroup.normalizer (H : Set (Deck p))) :
    SubgroupFiberOrbitQuotient H b → SubgroupFiberOrbitQuotient H b :=
  Quotient.map' (fun e : p ⁻¹' {b} => (φ : Deck p) • e) fun e e' hee' => by
    rw [MulAction.orbitRel_apply] at hee' ⊢
    exact normalizer_smul_mem_orbit H φ hee'

/-- The normalizer action on fibre quotients sends the class of a point to the class of its
deck translate. -/
@[simp]
lemma normalizerSubgroupFiberOrbitMap_apply (H : Subgroup (Deck p))
    (φ : _root_.Subgroup.normalizer (H : Set (Deck p))) (e : p ⁻¹' {b}) :
    normalizerSubgroupFiberOrbitMap H φ (subgroupFiberOrbitClass H e) =
      subgroupFiberOrbitClass H ((φ : Deck p) • e) :=
  rfl

/-- The normalizer representative `1` acts trivially on the subgroup fibre quotient. -/
@[simp]
lemma normalizerSubgroupFiberOrbitMap_one (H : Subgroup (Deck p)) :
    normalizerSubgroupFiberOrbitMap (b := b) H ⟨1, by simp⟩ = id := by
  ext x
  refine Quotient.inductionOn' x ?_
  intro e
  simp [normalizerSubgroupFiberOrbitMap]

/-- Normalizer representatives act by composition on the subgroup fibre quotient. -/
@[simp]
lemma normalizerSubgroupFiberOrbitMap_mul (H : Subgroup (Deck p))
    (φ ψ : _root_.Subgroup.normalizer (H : Set (Deck p))) :
    normalizerSubgroupFiberOrbitMap (b := b) H (φ * ψ) =
      normalizerSubgroupFiberOrbitMap H φ ∘ normalizerSubgroupFiberOrbitMap H ψ := by
  ext x
  refine Quotient.inductionOn' x ?_
  intro e
  simp [normalizerSubgroupFiberOrbitMap, mul_smul]

/-- A normalizer representative acts on the subgroup fibre quotient by a permutation. -/
@[expose] def normalizerSubgroupFiberOrbitEquiv (H : Subgroup (Deck p))
    (φ : _root_.Subgroup.normalizer (H : Set (Deck p))) :
    Equiv.Perm (SubgroupFiberOrbitQuotient H b) where
  toFun := normalizerSubgroupFiberOrbitMap H φ
  invFun := normalizerSubgroupFiberOrbitMap H φ⁻¹
  left_inv := by
    intro x
    refine Quotient.inductionOn' x ?_
    intro e
    simp [normalizerSubgroupFiberOrbitMap]
  right_inv := by
    intro x
    refine Quotient.inductionOn' x ?_
    intro e
    simp [normalizerSubgroupFiberOrbitMap]

/-- A normalizer representative permutes the subgroup fibre quotient by translating
representatives. -/
@[simp]
lemma normalizerSubgroupFiberOrbitEquiv_apply (H : Subgroup (Deck p))
    (φ : _root_.Subgroup.normalizer (H : Set (Deck p))) (e : p ⁻¹' {b}) :
    normalizerSubgroupFiberOrbitEquiv H φ (subgroupFiberOrbitClass H e) =
      subgroupFiberOrbitClass H ((φ : Deck p) • e) :=
  rfl

/-- The normalizer action on the subgroup fibre quotient as a permutation representation. -/
@[expose] noncomputable def normalizerSubgroupFiberOrbitPermHom (H : Subgroup (Deck p)) :
    _root_.Subgroup.normalizer (H : Set (Deck p)) →*
      Equiv.Perm (SubgroupFiberOrbitQuotient H b) where
  toFun := normalizerSubgroupFiberOrbitEquiv H
  map_one' := by
    ext x
    refine Quotient.inductionOn' x ?_
    intro e
    simp [normalizerSubgroupFiberOrbitEquiv, normalizerSubgroupFiberOrbitMap]
  map_mul' := by
    intro φ ψ
    ext x
    refine Quotient.inductionOn' x ?_
    intro e
    simp [normalizerSubgroupFiberOrbitEquiv, normalizerSubgroupFiberOrbitMap]

/-- The normalizer permutation homomorphism sends representatives to the expected deck
translate on fibre-orbit classes. -/
@[simp]
lemma normalizerSubgroupFiberOrbitPermHom_apply (H : Subgroup (Deck p))
    (φ : _root_.Subgroup.normalizer (H : Set (Deck p))) (e : p ⁻¹' {b}) :
    normalizerSubgroupFiberOrbitPermHom (b := b) H φ (subgroupFiberOrbitClass H e) =
      subgroupFiberOrbitClass H ((φ : Deck p) • e) :=
  rfl

lemma normalizerSubgroupFiberOrbitPermHom_eq_one_of_mem
    (H : Subgroup (Deck p)) (φ : _root_.Subgroup.normalizer (H : Set (Deck p)))
    (hφ : (φ : Deck p) ∈ H) :
    normalizerSubgroupFiberOrbitPermHom (b := b) H φ = 1 := by
  ext x
  refine Quotient.inductionOn' x ?_
  intro e
  change normalizerSubgroupFiberOrbitPermHom (b := b) H φ (subgroupFiberOrbitClass H e) =
    (1 : Equiv.Perm (SubgroupFiberOrbitQuotient H b)) (subgroupFiberOrbitClass H e)
  rw [normalizerSubgroupFiberOrbitPermHom_apply]
  exact (subgroupFiberOrbitClass_eq_iff H ((φ : Deck p) • e) e).2
    ⟨⟨(φ : Deck p), hφ⟩, rfl⟩

/-- The action of the normalizer on subgroup fibre quotients descends to `N(H) / H`. -/
@[expose] noncomputable def normalizerQuotientSubgroupFiberOrbitPermHom
    (H : Subgroup (Deck p)) :
    Subgroup.normalizerQuotient H →*
      Equiv.Perm (SubgroupFiberOrbitQuotient H b) :=
  Subgroup.normalizerQuotientLift H (normalizerSubgroupFiberOrbitPermHom (b := b) H)
    (normalizerSubgroupFiberOrbitPermHom_eq_one_of_mem (b := b) H)

/-- The descended normalizer-quotient action sends a normalizer representative to the
corresponding deck translate on fibre-orbit classes. -/
@[simp]
lemma normalizerQuotientSubgroupFiberOrbitPermHom_mk_apply (H : Subgroup (Deck p))
    (φ : _root_.Subgroup.normalizer (H : Set (Deck p))) (e : p ⁻¹' {b}) :
    normalizerQuotientSubgroupFiberOrbitPermHom (b := b) H
        (Subgroup.normalizerQuotientMk H φ) (subgroupFiberOrbitClass H e) =
      subgroupFiberOrbitClass H ((φ : Deck p) • e) :=
  rfl

/-- The normalizer quotient `N(H) / H` acts on the quotient of a fibre by `H`-orbits. -/
noncomputable instance instNormalizerQuotientSubgroupFiberOrbitMulAction
    (H : Subgroup (Deck p)) :
    MulAction (Subgroup.normalizerQuotient H) (SubgroupFiberOrbitQuotient H b) :=
  MulAction.compHom (SubgroupFiberOrbitQuotient H b)
    (normalizerQuotientSubgroupFiberOrbitPermHom (b := b) H)

/-- Representative formula for the action of `N(H) / H` on subgroup fibre quotients. -/
@[simp]
lemma normalizerQuotient_smul_subgroupFiberOrbitClass (H : Subgroup (Deck p))
    (φ : _root_.Subgroup.normalizer (H : Set (Deck p))) (e : p ⁻¹' {b}) :
    Subgroup.normalizerQuotientMk H φ • subgroupFiberOrbitClass H e =
      subgroupFiberOrbitClass H ((φ : Deck p) • e) :=
  rfl

/-- The identity class in `N(H) / H` fixes every subgroup fibre-orbit class. -/
@[simp]
lemma normalizerQuotient_one_smul_subgroupFiberOrbitClass (H : Subgroup (Deck p))
    (e : p ⁻¹' {b}) :
    (1 : Subgroup.normalizerQuotient H) • subgroupFiberOrbitClass H e =
      subgroupFiberOrbitClass H e := by
  simp

/-- A representative from `H` acts trivially through the normalizer quotient. -/
@[simp]
lemma normalizerQuotient_mk_of_mem_smul_subgroupFiberOrbitClass
    (H : Subgroup (Deck p)) (φ : Deck p) (hφ : φ ∈ H) (e : p ⁻¹' {b}) :
    Subgroup.normalizerQuotientMk H ⟨φ, _root_.Subgroup.le_normalizer hφ⟩ •
        subgroupFiberOrbitClass H e =
      subgroupFiberOrbitClass H e := by
  rw [normalizerQuotient_smul_subgroupFiberOrbitClass]
  exact (subgroupFiberOrbitClass_eq_iff H (φ • e) e).2 ⟨⟨φ, hφ⟩, rfl⟩

end Deck

end TauCeti
