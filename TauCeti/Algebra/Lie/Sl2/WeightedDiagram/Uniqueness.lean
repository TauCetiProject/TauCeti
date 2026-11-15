/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.AdjointAction.SymmetricInvariants
public import TauCeti.Algebra.Lie.Sl2.WeightedDiagram.Dominant
import TauCeti.Algebra.Lie.AdjointAction.ExpAdSubgroup
import TauCeti.Algebra.Lie.HighestWeight.ChevalleyRestriction
import TauCeti.Algebra.Lie.Sl2.JacobsonMorozov
import TauCeti.LinearAlgebra.RootSystem.Weyl.DominantIntegral
import TauCeti.LinearAlgebra.RootSystem.Weyl.Group
import TauCeti.RingTheory.Invariant.OrbitSeparation

/-!
# Uniqueness of dominant neutral elements and weighted Dynkin diagrams

Let `L` be a finite-dimensional Lie algebra with nondegenerate Killing form over an algebraically
closed field `K` of characteristic zero, let `H` be a Cartan subalgebra, and let `b` be a base of
the root system `LieAlgebra.IsKilling.rootSystem H`.

By Chevalley's restriction theorem, restricting polynomial functions on `L` to `H` maps the
`L`-invariants `S(L*)^L` onto the Weyl invariants `S(H)^W`. Since the finite Weyl group separates
orbits on `H` through its polynomial invariants, two elements of `H` take the same values on every
`p ∈ S(L*)^L` if and only if they lie in the same Weyl-group orbit
(`TauCeti.forall_mem_lieInvariants_lift_eval_eq_iff_exists_weylGroup`). Combined with uniqueness of
dominant integral points in a Weyl orbit (`TauCeti.weylGroup_smul_eq_self_of_dominantIntegral`),
at most one element of `H` where every simple root of `b` takes a natural value can realize a
given invariant character
(`RootPairing.Base.eq_of_forall_mem_lieInvariants_lift_eval_eq_of_dominant`).

For `sl₂` triples `(h₁, e₁, f₁)` and `(h₂, e₂, f₂)` whose neutral elements lie in
`RootPairing.Base.dominantNeutralElements b`, any Lie algebra automorphism `φ : L ≃ₗ⁅K⁆ L` carrying
`e₁` to `e₂` and preserving `S(L*)^L` forces `h₁ = h₂`
(`IsSl2Triple.eq_of_mem_dominantNeutralElements_of_lieEquiv_apply_eq`): Kostant's conjugacy theorem
conjugates `(φ h₁, e₂, φ f₁)` to `(h₂, e₂, f₂)` by an element of `expAdSubgroup K e₂ ≤ Int(L)`,
which also preserves `S(L*)^L`, so `h₁` and `h₂` agree on `S(L*)^L`. In particular, each
`Int(L)`-orbit of neutral elements meets `b.dominantNeutralElements` in a unique point
(`RootPairing.Base.injOn_orbit_dominantNeutralElements`), and the weighted Dynkin diagram depends
only on the `Int(L)`-orbit of the nilpositive element.

## Main results

* `TauCeti.forall_mem_lieInvariants_lift_eval_eq_iff_exists_weylGroup`: two elements of `H` agree
  on `S(L*)^L` if and only if they are conjugate under the Weyl group.
* `RootPairing.Base.eq_of_forall_mem_lieInvariants_lift_eval_eq_of_dominant`: dominant elements of
  `H` agreeing on `S(L*)^L` are equal.
* `IsSl2Triple.eq_of_mem_dominantNeutralElements_of_lieEquiv_apply_eq`: an invariant-preserving Lie
  automorphism carrying `e₁` to `e₂` identifies the dominant neutral elements `h₁` and `h₂`.
* `RootPairing.Base.injOn_orbit_dominantNeutralElements`: distinct dominant neutral elements have
  disjoint `Int(L)`-orbits.
* `IsSl2Triple.weightedDynkinDiagram_eq_of_mem_intLieAlgebra_smul_eq`: `Int(L)`-conjugate
  nilpositive elements have the same weighted Dynkin diagram.

## References

* D. H. Collingwood and W. M. McGovern, *Nilpotent Orbits in Semisimple Lie Algebras*, Van
  Nostrand Reinhold, 1993, §3.5.
* R. W. Carter, *Finite Groups of Lie Type: Conjugacy Classes and Complex Characters*, Wiley,
  1985, §5.6.
-/

public section

open LieAlgebra LieAlgebra.IsKilling LieModule Module _root_.SymmetricAlgebra
open TauCeti.SymmetricAlgebra

namespace TauCeti

section CartanSeparation

variable {K L : Type*} [Field K] [CharZero K] [IsAlgClosed K] [LieRing L] [LieAlgebra K L]
  [FiniteDimensional K L] [IsKilling K L] {H : LieSubalgebra K L} [H.IsCartanSubalgebra]

omit [CharZero K] [IsAlgClosed K] in
/-- Evaluating `killingSymmetricEquiv K L r` at `(z : L)` for `z : H` agrees with evaluating the
Cartan restriction `lieCartanRestriction H r` at `cartanEquivDual H z`. -/
private theorem lift_eval_killingSymmetricEquiv_coe (z : H) (r : _root_.SymmetricAlgebra K L) :
    lift (Dual.eval K L (z : L)) (killingSymmetricEquiv K L r) =
      lift (cartanEquivDual H z) (lieCartanRestriction H r) := by
  rw [lift_lieCartanRestriction, killingSymmetricEquiv_apply, ← AlgHom.comp_apply]
  congr 1
  refine algHom_ext (LinearMap.ext fun x ↦ ?_)
  simp [killingExtend_apply, traceForm_comm K L L x (z : L)]

/-- **Invariant polynomials detect Weyl orbits on a Cartan subalgebra.** Over an algebraically
closed field of characteristic zero, two elements `x, y : H` take the same value on every
`L`-invariant polynomial function `p ∈ S(L*)^L` if and only if some element of the Weyl group
carries `x` to `y`. -/
theorem forall_mem_lieInvariants_lift_eval_eq_iff_exists_weylGroup {x y : H} :
    (∀ p ∈ lieInvariants K L (Dual K L),
        lift (Dual.eval K L (x : L)) p = lift (Dual.eval K L (y : L)) p) ↔
      ∃ w : (rootSystem H).weylGroup, (w : (rootSystem H).Aut).coweightEquiv x = y := by
  constructor
  · intro hp
    -- Chevalley surjectivity transfers equality on `S(L*)^L` to equality on `S(H)^W`.
    have hlin : ∀ q ∈ linearInvariants H,
        lift (cartanEquivDual H x) q = lift (cartanEquivDual H y) q := by
      intro q hq
      obtain ⟨r, hr, rfl⟩ := Subalgebra.mem_map.mp
        ((LieSubalgebra.map_lieInvariants_lieCartanRestriction H).ge hq)
      have hr' : killingSymmetricEquiv K L r ∈ lieInvariants K L (Dual K L) :=
        (killingSymmetricEquiv_mem_lieInvariants_iff K L).mpr hr
      rw [← lift_eval_killingSymmetricEquiv_coe, ← lift_eval_killingSymmetricEquiv_coe]
      exact hp _ hr'
    -- Finite-group invariant separation on `S(H)` gives a Weyl group element relating `x` and `y`.
    have : Finite (rootSystem H).weylGroup := RootPairing.finite_weylGroup (rootSystem H)
    have : Finite (rootSystem H).weylGroup.op := Finite.of_equiv _ (Subgroup.equivOp _)
    let ρ := (rootSystem H).weylGroupCorootRep
    let := ρ.symmetricAlgebraMulSemiringAction
    have := ρ.smulCommClass_symmetricAlgebraMulSemiringAction
    rw [linearInvariants_eq_symmetricAlgebraInvariants,
      ρ.symmetricAlgebraInvariants_eq_fixedPoints] at hlin
    obtain ⟨g, hg⟩ := FixedPoints.forall_mem_subalgebra_eq_iff.mp hlin
    let w : (rootSystem H).weylGroup := (Subgroup.equivOp _).symm g
    have hgw : g = Subgroup.equivOp _ w := ((Subgroup.equivOp _).apply_symm_apply g).symm
    have hw : w • cartanEquivDual H x = cartanEquivDual H y := by
      ext h
      have hι := DFunLike.congr_fun hg (_root_.SymmetricAlgebra.ι K H h)
      simp only [AlgHom.comp_apply, MulSemiringAction.toAlgHom_apply,
        ρ.symmetricAlgebraMulSemiringAction_smul, Representation.symmetricAlgebra_apply,
        map_apply_ι, lift_ι_apply, hgw] at hι
      exact (RootPairing.Equiv.toLinearMap_weightEquiv (w : (rootSystem H).Aut)
        (cartanEquivDual H x) h).trans hι
    refine ⟨w⁻¹, ?_⟩
    have hsym := weylGroupCorootRep_cartanEquivDual_symm w⁻¹ (cartanEquivDual H x)
    rw [inv_inv, hw, LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply] at hsym
    exact hsym
  · rintro ⟨w, rfl⟩ p hp
    let := ratLieAlgebra K L
    obtain ⟨g, hg, hgw⟩ := exists_mem_intLieAlgebra_forall_smul_eq_coweightEquiv w
    rw [← hgw x, lift_eval_smul_of_mem_intLieAlgebra hg hp]

/-- Every coweight action of `P.weylGroup` is a weight action of `P.flip.weylGroup`. -/
private theorem exists_flip_weylGroup_smul_eq_coweightEquiv
    (w : (rootSystem H).weylGroup) :
    ∃ w' : (rootSystem H).flip.weylGroup,
      ∀ z : H, w' • z = (w : (rootSystem H).Aut).coweightEquiv z := by
  suffices ∀ u ∈ (rootSystem H).weylGroup, ∃ w' : (rootSystem H).flip.weylGroup,
      ∀ z : H, w' • z = u.coweightEquiv z from this w w.2
  intro u hu
  induction hu using RootPairing.weylGroup.induction with
  | mem i =>
    refine ⟨RootPairing.weylGroup.ofIdx (rootSystem H).flip i, fun z ↦ ?_⟩
    rw [RootPairing.weylGroup.ofIdx_smul, RootPairing.Equiv.reflection_coweightEquiv]
    rfl
  | one => exact ⟨1, fun z ↦ by simp⟩
  | mul u v _ _ ihu ihv =>
    obtain ⟨u', hu'⟩ := ihu
    obtain ⟨v', hv'⟩ := ihv
    refine ⟨v' * u', fun z ↦ ?_⟩
    rw [mul_smul, hu', hv', RootPairing.Equiv.mul_eq_comp,
      RootPairing.Equiv.coweightEquiv_comp_toLin, LinearEquiv.trans_apply]

end CartanSeparation

end TauCeti

namespace RootPairing.Base

open TauCeti

section DominantUniqueness

variable {K L : Type*} [Field K] [CharZero K] [IsAlgClosed K] [LieRing L] [LieAlgebra K L]
  [FiniteDimensional K L] [IsKilling K L] {H : LieSubalgebra K L} [H.IsCartanSubalgebra]

/-- **At most one dominant element realizes a given invariant character.** If `x, y : H` both take
natural-number values on every simple root of `b` and agree on every `L`-invariant polynomial
function `p ∈ S(L*)^L`, then `x = y`. -/
theorem eq_of_forall_mem_lieInvariants_lift_eval_eq_of_dominant (b : (rootSystem H).Base)
    {x y : H} (hx : ∀ i ∈ b.support, ∃ n : ℕ, (i : Weight K H L) x = n)
    (hy : ∀ i ∈ b.support, ∃ n : ℕ, (i : Weight K H L) y = n)
    (hp : ∀ p ∈ lieInvariants K L (Dual K L),
      lift (Dual.eval K L (x : L)) p = lift (Dual.eval K L (y : L)) p) :
    x = y := by
  obtain ⟨w, rfl⟩ := forall_mem_lieInvariants_lift_eval_eq_iff_exists_weylGroup.mp hp
  obtain ⟨w', hw'⟩ := TauCeti.exists_flip_weylGroup_smul_eq_coweightEquiv w
  have := (rootSystem H).flip_isReduced
  have hdom : w' • x = x := weylGroup_smul_eq_self_of_dominantIntegral
    (P := (rootSystem H).flip) (b := b.flip)
    (fun i hi ↦ hx i (by simpa using hi))
    (fun i hi ↦ by rw [hw']; exact hy i (by simpa using hi))
  exact hdom.symm.trans (hw' x)

end DominantUniqueness

section IntOrbits

variable {K L : Type*} [Field K] [CharZero K] [IsAlgClosed K] [LieRing L] [LieAlgebra K L]
  [LieAlgebra ℚ L] [FiniteDimensional K L] [IsKilling K L] {H : LieSubalgebra K L}
  [H.IsCartanSubalgebra]

/-- **Each `Int(L)`-orbit meets `dominantNeutralElements` in at most one point.** -/
theorem eq_of_mem_dominantNeutralElements_of_mem_intLieAlgebra_smul_eq (b : (rootSystem H).Base)
    {h₁ h₂ : H} (hh₁ : h₁ ∈ b.dominantNeutralElements) (hh₂ : h₂ ∈ b.dominantNeutralElements)
    {g : LinearMap.GeneralLinearGroup K L} (hg : g ∈ intLieAlgebra K L)
    (hgh : g • (h₁ : L) = (h₂ : L)) :
    h₁ = h₂ :=
  b.eq_of_forall_mem_lieInvariants_lift_eval_eq_of_dominant
    ((b.mem_dominantNeutralElements_iff h₁).mp hh₁).2
    ((b.mem_dominantNeutralElements_iff h₂).mp hh₂).2
    fun _ hp ↦ hgh ▸ (lift_eval_smul_of_mem_intLieAlgebra hg hp (h₁ : L)).symm

/-- **Distinct dominant neutral elements have distinct `Int(L)`-orbits.** Together with
`RootPairing.Base.image_orbit_dominantNeutralElements`, this identifies `b.dominantNeutralElements`
with the set of `Int(L)`-orbits of neutral elements of `sl₂` triples. -/
theorem injOn_orbit_dominantNeutralElements (b : (rootSystem H).Base) :
    Set.InjOn (fun h : H ↦ MulAction.orbit (intLieAlgebra K L) (h : L))
      b.dominantNeutralElements := by
  intro h₁ hh₁ h₂ hh₂ horb
  dsimp only at horb
  have hmem : (h₂ : L) ∈ MulAction.orbit (intLieAlgebra K L) (h₁ : L) := by
    rw [horb]
    exact MulAction.mem_orbit_self (h₂ : L)
  obtain ⟨⟨g, hg⟩, hgh⟩ := hmem
  exact b.eq_of_mem_dominantNeutralElements_of_mem_intLieAlgebra_smul_eq hh₁ hh₂ hg hgh

end IntOrbits

end RootPairing.Base

namespace IsSl2Triple

open TauCeti

section LieEquiv

variable {K L : Type*} [Field K] [CharZero K] [IsAlgClosed K] [LieRing L] [LieAlgebra K L]
  [FiniteDimensional K L] [IsKilling K L] {H : LieSubalgebra K L} [H.IsCartanSubalgebra]

/-- **Uniqueness of dominant neutral elements along conjugate nilpositive elements.** Let
`(h₁, e₁, f₁)` and `(h₂, e₂, f₂)` be `sl₂` triples with `h₁, h₂ ∈ b.dominantNeutralElements`. If a
Lie algebra automorphism `φ : L ≃ₗ⁅K⁆ L` carries `e₁` to `e₂` and preserves evaluation on
`S(L*)^L`, then `h₁ = h₂`. -/
theorem eq_of_mem_dominantNeutralElements_of_lieEquiv_apply_eq (b : (rootSystem H).Base)
    {h₁ h₂ : H} {e₁ f₁ e₂ f₂ : L}
    (t₁ : IsSl2Triple (h₁ : L) e₁ f₁) (t₂ : IsSl2Triple (h₂ : L) e₂ f₂)
    (hh₁ : h₁ ∈ b.dominantNeutralElements) (hh₂ : h₂ ∈ b.dominantNeutralElements)
    (φ : L ≃ₗ⁅K⁆ L) (hφe : φ e₁ = e₂)
    (hφinv : ∀ p ∈ lieInvariants K L (Dual K L), ∀ z : L,
      lift (Dual.eval K L (φ z)) p = lift (Dual.eval K L z) p) :
    h₁ = h₂ := by
  let := ratLieAlgebra K L
  have t₁' : IsSl2Triple (φ h₁) e₂ (φ f₁) :=
    hφe ▸ t₁.map φ.toLieHom ((map_ne_zero_iff φ.toLieHom φ.injective).mpr t₁.h_ne_zero)
  -- Kostant's conjugacy theorem moves `(φ h₁, e₂, φ f₁)` to `(h₂, e₂, f₂)` inside `Int(L)`.
  obtain ⟨ψ, hψ, -, hψh, -⟩ := t₁'.exists_lieEquiv_apply_eq (K := K) t₂
  let g : LinearMap.GeneralLinearGroup K L :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv K L).symm ψ.toLinearEquiv
  have hg : g ∈ intLieAlgebra K L :=
    map_expAdSubgroup_le_intLieAlgebra e₂ ⟨ψ.toLinearEquiv, hψ, rfl⟩
  have hgh : g • φ (h₁ : L) = (h₂ : L) := hψh
  refine b.eq_of_forall_mem_lieInvariants_lift_eval_eq_of_dominant
    ((b.mem_dominantNeutralElements_iff h₁).mp hh₁).2
    ((b.mem_dominantNeutralElements_iff h₂).mp hh₂).2 fun p hp ↦ ?_
  rw [← hφinv p hp (h₁ : L), ← hgh, lift_eval_smul_of_mem_intLieAlgebra hg hp]

end LieEquiv

section IntConjugacy

variable {K L : Type*} [Field K] [CharZero K] [IsAlgClosed K] [LieRing L] [LieAlgebra K L]
  [LieAlgebra ℚ L] [FiniteDimensional K L] [IsKilling K L] {H : LieSubalgebra K L}
  [H.IsCartanSubalgebra]

/-- **Conjugate nilpositive elements under `Int(L)` share the same dominant neutral element.** -/
theorem eq_of_mem_dominantNeutralElements_of_mem_intLieAlgebra_smul_eq (b : (rootSystem H).Base)
    {h₁ h₂ : H} {e₁ f₁ e₂ f₂ : L}
    (t₁ : IsSl2Triple (h₁ : L) e₁ f₁) (t₂ : IsSl2Triple (h₂ : L) e₂ f₂)
    (hh₁ : h₁ ∈ b.dominantNeutralElements) (hh₂ : h₂ ∈ b.dominantNeutralElements)
    {g : LinearMap.GeneralLinearGroup K L} (hg : g ∈ intLieAlgebra K L) (hge : g • e₁ = e₂) :
    h₁ = h₂ :=
  t₁.eq_of_mem_dominantNeutralElements_of_lieEquiv_apply_eq b t₂ hh₁ hh₂
    (intLieAlgebraLieEquiv ⟨g, hg⟩) (by simpa [intLieAlgebraLieEquiv_apply] using hge)
    fun _ hp z ↦ by
      simpa [intLieAlgebraLieEquiv_apply] using lift_eval_smul_of_mem_intLieAlgebra hg hp z

/-- **Conjugate nilpositive elements under `Int(L)` have equal weighted Dynkin diagrams.** -/
theorem weightedDynkinDiagram_eq_of_mem_intLieAlgebra_smul_eq (b : (rootSystem H).Base)
    {h₁ h₂ : H} {e₁ f₁ e₂ f₂ : L}
    (t₁ : IsSl2Triple (h₁ : L) e₁ f₁) (t₂ : IsSl2Triple (h₂ : L) e₂ f₂)
    (hh₁ : h₁ ∈ b.dominantNeutralElements) (hh₂ : h₂ ∈ b.dominantNeutralElements)
    {g : LinearMap.GeneralLinearGroup K L} (hg : g ∈ intLieAlgebra K L) (hge : g • e₁ = e₂) :
    b.weightedDynkinDiagram ⟨h₁, hh₁⟩ = b.weightedDynkinDiagram ⟨h₂, hh₂⟩ := by
  congr 1
  exact Subtype.ext (t₁.eq_of_mem_dominantNeutralElements_of_mem_intLieAlgebra_smul_eq b t₂
    hh₁ hh₂ hg hge)

end IntConjugacy

end IsSl2Triple
