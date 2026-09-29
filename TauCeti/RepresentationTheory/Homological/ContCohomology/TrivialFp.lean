/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Homological.ContCohomology.LowDegree
public import Mathlib.Topology.Instances.ZMod
public import Mathlib.Topology.Algebra.Algebra
public import TauCeti.RepresentationTheory.Continuous.Restriction
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Functoriality
public import TauCeti.RepresentationTheory.Homological.ContCohomology.SmoothDiscrete

/-!
# Trivial `ZMod p` coefficients for continuous cohomology

This file provides the trivial representation `trivialFp p G` of a group `G` on `ZMod p`.
When `p` is prime this gives the coefficient object for cohomology of pro-`p` groups over
the field `𝔽_p`. Mathlib's continuous-cohomology resolution requires coefficients in the universe
of `G`, so its carrier is the corresponding universe lift of `ZMod p`. The abbreviation
`cohomFp p G n` is continuous cohomology with these coefficients.

The coefficient object is deliberately available for an arbitrary topological group.  The
pro-`p` hypothesis belongs to the theorems which compute this cohomology, not to its definition.
The restriction map is named because later rank and cup-product arguments must change groups
without repeatedly transporting across the definitional equality of trivial representations.

## Main definitions

* `TauCeti.trivialFp`: trivial `ZMod p` coefficients in the universe of the group.
* `TauCeti.cohomFp`: continuous cohomology with trivial `ZMod p` coefficients.
* `TauCeti.trivialFpResMap`: restriction on `cohomFp`.
* `TauCeti.cohomFpMap`: the map induced by a continuous group homomorphism.
* `TauCeti.cohomFpLinearEquiv`: invariance under topological group isomorphism.

## Main results

* `TauCeti.trivialFp_ρ_apply_apply`, `TauCeti.smul_trivialFp_V`: the action is trivial.
* `TauCeti.continuousSMul_trivialFp`: the derived action on the carrier is continuous.
* `TauCeti.natCard_trivialFp_V`: the `Nat.card` of the carrier is `p`.
* `TauCeti.nontrivial_cohomFp_zero`: `H⁰(G, ZMod p)` is nontrivial.
* `TauCeti.res_trivialFp`: restriction preserves trivial coefficients on the nose;
  `TauCeti.trivialFpEquiv_eqToHom_res_trivialFp`: the transport along this equality is the identity
  on the underlying values.

## References

* J.-P. Serre, *Galois Cohomology*, I §4.
* `TauCeti.RepresentationTheory.Homological.ContCohomology.TrivialF2`, whose coefficient API
  provides the formal template for this module.
-/

public section

namespace TauCeti

universe u

attribute [local instance] DiscreteTopology.instContinuousSMul

section Monoid

variable (p : ℕ) (G : Type u) [Monoid G]

/-- Trivial `ZMod p` coefficients as an object of `TopRep (ZMod p) G` in the universe of `G`.

The universe lift is forced by Mathlib's continuous-cohomology resolution. -/
noncomputable def trivialFp : TopRep (ZMod p) G :=
  TopRep.of (ContRepresentation.trivial (ZMod p) G (ULift.{u} (ZMod p)))

/-- The carrier of `trivialFp p G` is the universe lift of `ZMod p`. -/
@[simp]
theorem trivialFp_V : (trivialFp p G).V = ULift.{u} (ZMod p) := (rfl)

/-- The `ZMod p`-linear equivalence from the lifted carrier of `trivialFp p G` to `ZMod p`. -/
noncomputable def trivialFpEquiv : (trivialFp p G).V ≃ₗ[ZMod p] ZMod p :=
  -- The carrier is definitionally `ULift.{u} (ZMod p)`; elaborate `ULift.moduleEquiv` against
  -- that unfolded carrier because `trivialFp_V` is an equality of types.
  ULift.moduleEquiv

/-- `trivialFpEquiv` sends a lifted element to its underlying value. -/
@[simp]
theorem trivialFpEquiv_apply (x : ULift.{u} (ZMod p)) :
    trivialFpEquiv p G (cast (trivialFp_V p G).symm x) = x.down :=
  -- `(rfl)` unfolds the hidden equivalence and reduces the cast; this is its public
  -- application rule.
  (rfl)

/-- The inverse of `trivialFpEquiv` lifts a value. -/
@[simp]
theorem trivialFpEquiv_symm_apply (x : ZMod p) :
    (trivialFpEquiv p G).symm x = cast (trivialFp_V p G).symm (ULift.up x) :=
  -- The inverse likewise reduces definitionally after unfolding the equivalence and cast.
  (rfl)

/-- The lifted carrier of `trivialFp p G` has the discrete topology. -/
instance : DiscreteTopology (trivialFp p G).V :=
  inferInstanceAs (DiscreteTopology (ULift.{u} (ZMod p)))

/-- The lifted carrier of `trivialFp p G` is finite, for `p ≠ 0`. -/
instance [NeZero p] : Finite (trivialFp p G).V :=
  inferInstanceAs (Finite (ULift.{u} (ZMod p)))

/-- The `Nat.card` of the carrier of `trivialFp p G` is `p`. For `p ≠ 0` this says that the carrier
has `p` elements; for `p = 0` the carrier is infinite, and `Nat.card` is `0` by convention. -/
theorem natCard_trivialFp_V : Nat.card (trivialFp p G).V = p :=
  (Nat.card_congr (trivialFpEquiv p G).toEquiv).trans (Nat.card_zmod p)

/-- Every monoid element acts trivially on `trivialFp p G`. -/
@[simp]
theorem trivialFp_ρ_apply_apply (g : G) (x : (trivialFp p G).V) :
    (trivialFp p G).ρ g x = x :=
  ContRepresentation.trivial_apply g x

attribute [local instance] TopRep.distribMulAction in
/-- The derived action of `G` on the carrier of `trivialFp p G` is trivial. Not a simp lemma:
`simp` already proves it from `TopRep.distribMulAction_smul` and `trivialFp_ρ_apply_apply`. -/
theorem smul_trivialFp_V (g : G) (x : (trivialFp p G).V) : g • x = x :=
  (TopRep.distribMulAction_smul _ g x).trans (trivialFp_ρ_apply_apply p G g x)

variable [TopologicalSpace G]

/-- The trivial `ZMod p` coefficient object is smooth discrete. -/
theorem isSmoothDiscrete_trivialFp : IsSmoothDiscrete (ZMod p) (trivialFp p G) :=
  isSmoothDiscrete_trivial (ZMod p) (ULift.{u} (ZMod p))

end Monoid

section Group

variable (p : ℕ) (G : Type u) [Group G]

/-- Restriction preserves the trivial `ZMod p` coefficient object on the nose. -/
@[simp]
theorem res_trivialFp (S : Subgroup G) :
    TopRep.res (S.subtype : S →* G) (trivialFp p G) = trivialFp p S :=
  res_trivial (ZMod p) G (ULift.{u} (ZMod p)) S.subtype

open CategoryTheory _root_.ContinuousCohomology

/-- Transport along `res_trivialFp` is the identity on the underlying values: the restricted
coefficient object and `trivialFp p S` have the same lifted carrier, and `trivialFpEquiv` reads
off the same value on both sides. -/
@[simp]
theorem trivialFpEquiv_eqToHom_res_trivialFp (S : Subgroup G)
    (x : (TopRep.res (S.subtype : S →* G) (trivialFp p G)).V) :
    trivialFpEquiv p S (eqToHom (res_trivialFp p G S) x) = trivialFpEquiv p G x :=
  -- `res_trivialFp` holds by `rfl` here, so the transport is the identity map.
  (rfl)

variable [TopologicalSpace G] [IsTopologicalGroup G]

attribute [local instance] TopRep.distribMulAction in
/-- The derived action of `G` on the carrier of `trivialFp p G` is continuous, the carrier being
discrete and the action trivial. -/
theorem continuousSMul_trivialFp : ContinuousSMul G (trivialFp p G).V :=
  (isSmoothDiscrete_iff_continuousSMul _).1 (isSmoothDiscrete_trivialFp p G)

/-- Continuous cohomology with trivial `ZMod p` coefficients. -/
noncomputable abbrev cohomFp (n : ℕ) := continuousCohomology n (trivialFp p G)

/-- `H⁰(G, ZMod p)` is nontrivial: it is the invariants of the trivial representation, that is
the whole of `ZMod p`. -/
theorem nontrivial_cohomFp_zero [Nontrivial (ZMod p)] : Nontrivial (cohomFp p G 0) := by
  refine (zeroIso (trivialFp p G)).toContinuousLinearEquiv.toEquiv.nontrivial_congr.2
    (Submodule.nontrivial_iff_ne_bot.2 fun h ↦ ?_)
  -- the lift of `1` is invariant and nonzero
  have hmem : (trivialFpEquiv p G).symm 1 ∈ (trivialFp p G).ρ.invariants := fun g ↦
    trivialFp_ρ_apply_apply p G g _
  rw [h, Submodule.mem_bot] at hmem
  exact one_ne_zero ((trivialFpEquiv p G).symm.injective (hmem.trans (map_zero _).symm))

/-- Restriction on cohomology with trivial `ZMod p` coefficients. -/
noncomputable def trivialFpResMap (S : Subgroup G) (n : ℕ) :
    cohomFp p G n ⟶ cohomFp p S n :=
  ContinuousCohomology.res S (trivialFp p G) n ≫
    eqToHom (congrArg (continuousCohomology n) (res_trivialFp p G S))

/-- The defining equation of restriction with trivial `ZMod p` coefficients. -/
theorem trivialFpResMap_def (S : Subgroup G) (n : ℕ) :
    trivialFpResMap p G S n = ContinuousCohomology.res S (trivialFp p G) n ≫
      eqToHom (congrArg (continuousCohomology n) (res_trivialFp p G S)) :=
  (rfl)

end Group

section Hom

open CategoryTheory

variable (p : ℕ) {G H K : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [Group K] [TopologicalSpace K] [IsTopologicalGroup K]

omit [IsTopologicalGroup G] [IsTopologicalGroup H] in
/-- Restriction along a continuous group homomorphism preserves trivial coefficients. -/
@[simp]
theorem res_trivialFp_hom (φ : H →ₜ* G) :
    TopRep.res (φ : H →* G) (trivialFp p G) = trivialFp p H :=
  res_trivial (ZMod p) G (ULift.{u} (ZMod p)) φ.toMonoidHom

omit [IsTopologicalGroup G] [IsTopologicalGroup H] in
/-- The transport to trivial coefficients along a homomorphism leaves coefficient values
unchanged. -/
@[simp]
theorem trivialFpEquiv_eqToHom_res_trivialFp_hom (φ : H →ₜ* G)
    (x : (TopRep.res (φ : H →* G) (trivialFp p G)).V) :
    trivialFpEquiv p H (eqToHom (res_trivialFp_hom p φ) x) =
      trivialFpEquiv p G x :=
  (rfl)

/-- The contravariant map on cohomology with trivial `ZMod p` coefficients. -/
noncomputable def cohomFpMap (φ : H →ₜ* G) (n : ℕ) :
    cohomFp p G n ⟶ cohomFp p H n :=
  ContinuousCohomology.map φ (eqToHom (res_trivialFp_hom p φ)) n

/-- The cohomology map is the general map with identity transport on trivial coefficients. -/
theorem cohomFpMap_def (φ : H →ₜ* G) (n : ℕ) :
    cohomFpMap p φ n =
      ContinuousCohomology.map φ (eqToHom (res_trivialFp_hom p φ)) n :=
  (rfl)

/-- The general cohomology map along a subgroup inclusion is the named restriction map. -/
@[simp]
theorem cohomFpMap_subgroupSubtype (S : Subgroup G) (n : ℕ) :
    cohomFpMap p (ContinuousMonoidHom.subgroupSubtype S) n =
      trivialFpResMap p G S n := by
  have hmap : eqToHom (res_trivialFp_hom p (ContinuousMonoidHom.subgroupSubtype S)) =
      𝟙 (trivialFp p S) := eqToHom_refl _ _
  have hres : eqToHom (congrArg (continuousCohomology n) (res_trivialFp p G S)) =
      𝟙 (cohomFp p S n) := eqToHom_refl _ _
  calc
    cohomFpMap p (ContinuousMonoidHom.subgroupSubtype S) n =
        _root_.ContinuousCohomology.map (ContinuousMonoidHom.subgroupSubtype S)
          (𝟙 (trivialFp p S)) n := by
      rw [cohomFpMap_def, hmap]
    _ = _root_.ContinuousCohomology.map (ContinuousMonoidHom.subgroupSubtype S)
          (𝟙 (TopRep.res (S.subtype : S →* G) (trivialFp p G))) n ≫
          𝟙 (cohomFp p S n) := by
      -- The monoid hom of `subgroupSubtype` is definitionally `S.subtype`.
      change _root_.ContinuousCohomology.map (ContinuousMonoidHom.subgroupSubtype S)
          (𝟙 _) n =
        _root_.ContinuousCohomology.map (ContinuousMonoidHom.subgroupSubtype S)
          (𝟙 _) n ≫ 𝟙 _
      simp
    _ = trivialFpResMap p G S n := by
      rw [trivialFpResMap_def, TauCeti.ContinuousCohomology.res_def, hres]

/-- The identity homomorphism induces the identity on cohomology. -/
@[simp]
theorem cohomFpMap_id (n : ℕ) :
    cohomFpMap p (ContinuousMonoidHom.id G) n = 𝟙 _ := by
  have h : (eqToHom (res_trivialFp_hom p (ContinuousMonoidHom.id G))) =
      𝟙 (trivialFp p G) := eqToHom_refl _ _
  simpa only [cohomFpMap, h] using (ContinuousCohomology.map_id (trivialFp p G) n)

omit [IsTopologicalGroup G] [IsTopologicalGroup H] [IsTopologicalGroup K] in
/-- The transports of trivial coefficients compose along continuous group homomorphisms. -/
theorem res_trivialFp_hom_comp (φ : H →ₜ* G) (ψ : K →ₜ* H) :
    (TopRep.resFunctor (ψ : K →* H)).map (eqToHom (res_trivialFp_hom p φ)) ≫
      eqToHom (res_trivialFp_hom p ψ) =
        eqToHom (res_trivialFp_hom p (φ.comp ψ)) := by
  have hφ : eqToHom (res_trivialFp_hom p φ) = 𝟙 (trivialFp p H) :=
    eqToHom_refl _ _
  have hψ : eqToHom (res_trivialFp_hom p ψ) = 𝟙 (trivialFp p K) :=
    eqToHom_refl _ _
  have hcomp : eqToHom (res_trivialFp_hom p (φ.comp ψ)) = 𝟙 (trivialFp p K) :=
    eqToHom_refl _ _
  simpa only [hφ, hψ, hcomp, Functor.map_id, Category.id_comp]

/-- Cohomology maps with trivial coefficients compose contravariantly. -/
@[simp]
theorem cohomFpMap_comp (φ : H →ₜ* G) (ψ : K →ₜ* H) (n : ℕ) :
    cohomFpMap p (φ.comp ψ) n = cohomFpMap p φ n ≫ cohomFpMap p ψ n := by
  unfold cohomFpMap
  rw [← ContinuousCohomology.map_comp]
  exact ContinuousCohomology.map_congr rfl
    (heq_of_eq (res_trivialFp_hom_comp p φ ψ).symm) n

/-- The cohomology map induced by a topological group isomorphism is a linear equivalence,
with the inverse induced by the inverse group isomorphism. -/
noncomputable def cohomFpLinearEquiv (e : G ≃ₜ* H) (n : ℕ) :
    cohomFp p G n ≃ₗ[ZMod p] cohomFp p H n := by
  let f : H →ₜ* G := ContinuousMonoidHom.toContinuousMonoidHom e.symm
  let g : G →ₜ* H := ContinuousMonoidHom.toContinuousMonoidHom e
  have hfg : f.comp g = ContinuousMonoidHom.id G := by
    ext x
    exact e.symm_apply_apply x
  have hgf : g.comp f = ContinuousMonoidHom.id H := by
    ext x
    exact e.apply_symm_apply x
  let i : cohomFp p G n ≅ cohomFp p H n :=
    { hom := cohomFpMap p f n
      inv := cohomFpMap p g n
      hom_inv_id := by rw [← cohomFpMap_comp, hfg, cohomFpMap_id]
      inv_hom_id := by rw [← cohomFpMap_comp, hgf, cohomFpMap_id] }
  exact i.toContinuousLinearEquiv.toLinearEquiv

/-- The cohomology equivalence acts by the map induced by the inverse group isomorphism. -/
@[simp]
theorem cohomFpLinearEquiv_apply (e : G ≃ₜ* H) (n : ℕ) (x : cohomFp p G n) :
    cohomFpLinearEquiv p e n x =
      cohomFpMap p (ContinuousMonoidHom.toContinuousMonoidHom e.symm) n x :=
  (rfl)

/-- The inverse cohomology equivalence acts by the map induced by the forward group
isomorphism. -/
@[simp]
theorem cohomFpLinearEquiv_symm_apply (e : G ≃ₜ* H) (n : ℕ) (x : cohomFp p H n) :
    (cohomFpLinearEquiv p e n).symm x =
      cohomFpMap p (ContinuousMonoidHom.toContinuousMonoidHom e) n x :=
  (rfl)

end Hom

end TauCeti
