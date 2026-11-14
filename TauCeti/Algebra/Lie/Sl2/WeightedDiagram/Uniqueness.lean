/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.HighestWeight.ChevalleyRestriction
public import TauCeti.Algebra.Lie.Sl2.WeightedDiagram.Dominant
import Mathlib.Data.Set.Card
import TauCeti.Algebra.Lie.AdjointAction.ExpAdSubgroup
import TauCeti.Algebra.Lie.AdjointAction.SymmetricInvariants
import TauCeti.Algebra.Lie.Sl2.JacobsonMorozov
import TauCeti.LinearAlgebra.RootSystem.IntegralCoweight

/-!
# Uniqueness of the dominant neutral element and the weighted Dynkin diagram

Let `L` be a finite-dimensional Lie algebra with non-degenerate Killing form over a field `K` of
characteristic zero, let `H` be a splitting Cartan subalgebra and fix a base `b` of the root system
`LieAlgebra.IsKilling.rootSystem H`.

Every `sl₂` triple over an algebraically closed field can be conjugated by `Int(L)` so that its
neutral element lies in `RootPairing.Base.dominantNeutralElements b`
(`IsSl2Triple.exists_mem_intLieAlgebra_smul_mem_dominantNeutralElements_of_isAlgClosed`). This file
proves the complementary uniqueness statement: the dominant neutral element—and therefore the
weighted Dynkin diagram—is uniquely determined, first by the `Int(L)`-orbit of the neutral element,
and more strongly by the orbit of the nilpositive element under any Lie automorphism preserving the
invariant polynomial functions `S(L*)^L`.

## The argument

1. **Uniqueness in a Weyl orbit.** A dominant neutral element is an integral coweight of
   `rootSystem H` at which every simple root of `b` takes a natural value, so at most one element of
   any Weyl orbit lies in `b.dominantNeutralElements`
   (`RootPairing.Base.coweightEquiv_eq_self_of_forall_exists_nat_root'_apply`).
2. **Separation by invariant polynomial functions.** Over an algebraically closed field, Chevalley's
   restriction theorem implies that two elements of `H` take equal values at every invariant
   polynomial function `p ∈ S(L*)^L` if and only if they lie in the same Weyl orbit
   (`LieSubalgebra.forall_mem_lieInvariants_lift_eval_coe_eq_iff`). Hence two dominant neutral
   elements that cannot be separated by `S(L*)^L` are equal.
3. **Passage from the nilpositive element to the neutral element.** Suppose `(h₁, e₁, f₁)` and
   `(h₂, e₂, f₂)` are `sl₂` triples with `h₁, h₂ ∈ b.dominantNeutralElements`, and `φ : L ≃ₗ⁅K⁆ L`
   is a Lie automorphism carrying `e₁` to `e₂` and preserving values on `S(L*)^L` at `h₁` (as holds
   for every element of `Int(L)` and every rational point of a connected algebraic group with Lie
   algebra `L`). Then `(φ h₁, e₂, φ f₁)` and `(h₂, e₂, f₂)` share the nilpositive element `e₂`, so
   Kostant's conjugacy theorem (`IsSl2Triple.exists_lieEquiv_apply_eq`) conjugates `φ h₁` to `h₂` by
   an element of `TauCeti.expAdSubgroup K e₂ ≤ Int(L)`. Since `Int(L)` preserves `S(L*)^L`
   (`TauCeti.SymmetricAlgebra.lift_eval_smul_of_mem_intLieAlgebra`), `h₁` and `h₂` agree on
   `S(L*)^L` and are therefore equal.

## Main results

* `RootPairing.Base.eq_of_mem_dominantNeutralElements_of_coweightEquiv_eq` and
  `RootPairing.Base.eq_of_mem_dominantNeutralElements_of_forall_mem_lieInvariants_lift_eval_eq`:
  dominant neutral elements in the same Weyl orbit, or agreeing on `S(L*)^L` over an algebraically
  closed field, coincide.
* `IsSl2Triple.eq_of_mem_dominantNeutralElements_of_lieEquiv_apply_eq` and
  `IsSl2Triple.weightedDynkinDiagram_eq_of_lieEquiv_apply_eq`: if a Lie automorphism preserving
  invariant polynomial values at `h₁` carries `e₁` to `e₂`, the dominant neutral elements `h₁` and
  `h₂` (and their weighted Dynkin diagrams) coincide.
* `RootPairing.Base.injOn_orbit_intLieAlgebra_dominantNeutralElements`,
  `IsSl2Triple.existsUnique_mem_dominantNeutralElements_mem_orbit_intLieAlgebra`, and
  `TauCeti.ncard_image_orbit_setOf_exists_isSl2Triple_eq`: each `Int(L)`-orbit of neutral elements
  contains a unique dominant neutral element, so the number of such orbits equals
  `(b.dominantNeutralElements).ncard`.
* `IsSl2Triple.eq_of_mem_dominantNeutralElements_of_mem_intLieAlgebra_smul_eq` and
  `TauCeti.existsUnique_mem_dominantNeutralElements_exists_mem_intLieAlgebra_isSl2Triple`: each
  nonzero `ad`-nilpotent element determines a unique dominant neutral element up to `Int(L)`.

## References

* D. H. Collingwood and W. M. McGovern, *Nilpotent Orbits in Semisimple Lie Algebras*, Van
  Nostrand Reinhold, 1993, Theorem 3.5.4.
* N. Bourbaki, *Lie Groups and Lie Algebras*, Chapters 7–9, Chapter VIII, §11, no. 2, Proposition 3.
-/

public section

open LieAlgebra LieAlgebra.IsKilling LieModule Module TauCeti TauCeti.SymmetricAlgebra

namespace RootPairing.Base

section Split

variable {K L : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [FiniteDimensional K L] [IsKilling K L] {H : LieSubalgebra K L} [H.IsCartanSubalgebra]
  [IsTriangularizable K H L]

/-- **At most one dominant neutral element lies in each Weyl orbit.** -/
theorem eq_of_mem_dominantNeutralElements_of_coweightEquiv_eq (b : (rootSystem H).Base)
    {h₁ h₂ : H} (hh₁ : h₁ ∈ b.dominantNeutralElements) (hh₂ : h₂ ∈ b.dominantNeutralElements)
    (hw : ∃ w : (rootSystem H).weylGroup, (w : (rootSystem H).Aut).coweightEquiv h₁ = h₂) :
    h₁ = h₂ := by
  obtain ⟨w, rfl⟩ := hw
  exact (b.coweightEquiv_eq_self_of_forall_exists_nat_root'_apply
    ((b.mem_dominantNeutralElements_iff _).mp hh₁).2
    ((b.mem_dominantNeutralElements_iff _).mp hh₂).2).symm

/-- **Weyl invariants separate dominant neutral elements** when read through
`LieAlgebra.IsKilling.cartanEquivDual`. -/
theorem eq_of_mem_dominantNeutralElements_of_forall_mem_linearInvariants_lift_eq
    (b : (rootSystem H).Base) {h₁ h₂ : H} (hh₁ : h₁ ∈ b.dominantNeutralElements)
    (hh₂ : h₂ ∈ b.dominantNeutralElements)
    (heq : ∀ p ∈ linearInvariants H,
      _root_.SymmetricAlgebra.lift (cartanEquivDual H h₁) p =
        _root_.SymmetricAlgebra.lift (cartanEquivDual H h₂) p) :
    h₁ = h₂ :=
  b.eq_of_mem_dominantNeutralElements_of_coweightEquiv_eq hh₁ hh₂
    (forall_mem_linearInvariants_lift_cartanEquivDual_eq_iff.mp heq)

end Split

section IsAlgClosed

variable {K L : Type*} [Field K] [CharZero K] [IsAlgClosed K] [LieRing L] [LieAlgebra K L]
  [FiniteDimensional K L] [IsKilling K L] {H : LieSubalgebra K L} [H.IsCartanSubalgebra]

/-- **Invariant polynomial functions separate dominant neutral elements.** Over an algebraically
closed field of characteristic zero, two dominant neutral elements taking equal values at every
invariant polynomial function `p ∈ S(L*)^L` are equal. -/
theorem eq_of_mem_dominantNeutralElements_of_forall_mem_lieInvariants_lift_eval_eq
    (b : (rootSystem H).Base) {h₁ h₂ : H} (hh₁ : h₁ ∈ b.dominantNeutralElements)
    (hh₂ : h₂ ∈ b.dominantNeutralElements)
    (heq : ∀ p ∈ lieInvariants K L (Dual K L),
      _root_.SymmetricAlgebra.lift (Dual.eval K L (h₁ : L)) p =
        _root_.SymmetricAlgebra.lift (Dual.eval K L (h₂ : L)) p) :
    h₁ = h₂ :=
  b.eq_of_mem_dominantNeutralElements_of_coweightEquiv_eq hh₁ hh₂
    (H.forall_mem_lieInvariants_lift_eval_coe_eq_iff.mp heq)

/-- **Distinct dominant neutral elements lie in distinct `Int(L)`-orbits.** -/
theorem injOn_orbit_intLieAlgebra_dominantNeutralElements [LieAlgebra ℚ L]
    (b : (rootSystem H).Base) :
    Set.InjOn (fun h : H ↦ MulAction.orbit (intLieAlgebra K L) (h : L))
      b.dominantNeutralElements := by
  intro h₁ hh₁ h₂ hh₂ horb
  dsimp only at horb
  have hmem : (h₁ : L) ∈ MulAction.orbit (intLieAlgebra K L) (h₂ : L) :=
    horb ▸ MulAction.mem_orbit_self (h₁ : L)
  obtain ⟨⟨g, hg⟩, hg12⟩ := hmem
  refine b.eq_of_mem_dominantNeutralElements_of_forall_mem_lieInvariants_lift_eval_eq hh₁ hh₂
    fun p hp ↦ ?_
  rw [← hg12]
  exact lift_eval_smul_of_mem_intLieAlgebra hg hp (h₂ : L)

end IsAlgClosed

end RootPairing.Base

namespace IsSl2Triple

section IsAlgClosed

variable {K L : Type*} [Field K] [CharZero K] [IsAlgClosed K] [LieRing L] [LieAlgebra K L]
  [FiniteDimensional K L] [IsKilling K L] {H : LieSubalgebra K L} [H.IsCartanSubalgebra]

/-- **Uniqueness of the dominant neutral element from the nilpositive element.** Over an
algebraically closed field of characteristic zero, let `(h₁, e₁, f₁)` and `(h₂, e₂, f₂)` be `sl₂`
triples with `h₁, h₂ ∈ b.dominantNeutralElements`. If a Lie automorphism `φ : L ≃ₗ⁅K⁆ L` carries
`e₁` to `e₂` and preserves the value at `h₁` of every invariant polynomial function `p ∈ S(L*)^L`,
then `h₁ = h₂`. -/
theorem eq_of_mem_dominantNeutralElements_of_lieEquiv_apply_eq (b : (rootSystem H).Base)
    {h₁ h₂ : H} {e₁ f₁ e₂ f₂ : L} (t₁ : IsSl2Triple (h₁ : L) e₁ f₁)
    (t₂ : IsSl2Triple (h₂ : L) e₂ f₂) (hh₁ : h₁ ∈ b.dominantNeutralElements)
    (hh₂ : h₂ ∈ b.dominantNeutralElements) (φ : L ≃ₗ⁅K⁆ L) (hφe : φ e₁ = e₂)
    (hφp : ∀ p ∈ lieInvariants K L (Dual K L),
      _root_.SymmetricAlgebra.lift (Dual.eval K L (φ (h₁ : L))) p =
        _root_.SymmetricAlgebra.lift (Dual.eval K L (h₁ : L)) p) :
    h₁ = h₂ := by
  let _ : Module ℚ L := Module.compHom L (algebraMap ℚ K)
  let _ : LieAlgebra ℚ L := { lie_smul := fun q x y ↦ lie_smul (algebraMap ℚ K q) x y }
  have hφh0 : φ (h₁ : L) ≠ 0 := fun hz ↦ t₁.h_ne_zero (φ.injective (hz.trans (map_zero φ).symm))
  have t₁' : IsSl2Triple (φ (h₁ : L)) e₂ (φ f₁) := hφe ▸ t₁.map φ.toLieHom hφh0
  obtain ⟨ψ, hψ, -, hψh, -⟩ := t₁'.exists_lieEquiv_apply_eq (K := K) t₂
  have hψint : LinearMap.GeneralLinearGroup.ofLinearEquiv ψ.toLinearEquiv ∈ intLieAlgebra K L :=
    map_expAdSubgroup_le_intLieAlgebra e₂ ⟨ψ.toLinearEquiv, hψ, rfl⟩
  refine b.eq_of_mem_dominantNeutralElements_of_forall_mem_lieInvariants_lift_eval_eq hh₁ hh₂
    fun p hp ↦ ?_
  have hψp := lift_eval_smul_of_mem_intLieAlgebra hψint hp (φ (h₁ : L))
  have hsmul : LinearMap.GeneralLinearGroup.ofLinearEquiv ψ.toLinearEquiv • φ (h₁ : L) =
      (h₂ : L) := by
    simpa [Units.smul_def] using hψh
  rw [hsmul] at hψp
  exact (hφp p hp).symm.trans hψp.symm

/-- **Invariance of the weighted Dynkin diagram under nilpositive conjugacy.** Under the hypotheses
of `IsSl2Triple.eq_of_mem_dominantNeutralElements_of_lieEquiv_apply_eq`, `h₁` and `h₂` have the same
weighted Dynkin diagram. -/
theorem weightedDynkinDiagram_eq_of_lieEquiv_apply_eq (b : (rootSystem H).Base)
    {h₁ h₂ : H} {e₁ f₁ e₂ f₂ : L} (t₁ : IsSl2Triple (h₁ : L) e₁ f₁)
    (t₂ : IsSl2Triple (h₂ : L) e₂ f₂) (hh₁ : h₁ ∈ b.dominantNeutralElements)
    (hh₂ : h₂ ∈ b.dominantNeutralElements) (φ : L ≃ₗ⁅K⁆ L) (hφe : φ e₁ = e₂)
    (hφp : ∀ p ∈ lieInvariants K L (Dual K L),
      _root_.SymmetricAlgebra.lift (Dual.eval K L (φ (h₁ : L))) p =
        _root_.SymmetricAlgebra.lift (Dual.eval K L (h₁ : L)) p) :
    b.weightedDynkinDiagram ⟨h₁, hh₁⟩ = b.weightedDynkinDiagram ⟨h₂, hh₂⟩ := by
  have heq := t₁.eq_of_mem_dominantNeutralElements_of_lieEquiv_apply_eq b t₂ hh₁ hh₂ φ hφe hφp
  subst heq
  rfl

end IsAlgClosed

section IntLieAlgebra

variable {K L : Type*} [Field K] [CharZero K] [IsAlgClosed K] [LieRing L] [LieAlgebra K L]
  [LieAlgebra ℚ L] [FiniteDimensional K L] [IsKilling K L] {H : LieSubalgebra K L}
  [H.IsCartanSubalgebra]

/-- **Every `sl₂` triple has a unique dominant neutral element in the `Int(L)`-orbit of `h`.** -/
theorem existsUnique_mem_dominantNeutralElements_mem_orbit_intLieAlgebra
    (b : (rootSystem H).Base) {h e f : L} (t : IsSl2Triple h e f) :
    ∃! h' : H, h' ∈ b.dominantNeutralElements ∧
      (h' : L) ∈ MulAction.orbit (intLieAlgebra K L) h := by
  obtain ⟨g, hg, h', hh', hgh, -⟩ :=
    t.exists_mem_intLieAlgebra_smul_mem_dominantNeutralElements_of_isAlgClosed b
  refine ⟨h', ⟨hh', ⟨⟨g, hg⟩, hgh⟩⟩, ?_⟩
  rintro h'' ⟨hh'', g₁, hg₁⟩
  refine b.injOn_orbit_intLieAlgebra_dominantNeutralElements hh'' hh' ?_
  dsimp only
  have hgh' : (⟨g, hg⟩ : intLieAlgebra K L) • h = (h' : L) := hgh
  have hg₁' : g₁ • h = (h'' : L) := hg₁
  rw [← hg₁', ← hgh', MulAction.orbit_smul, MulAction.orbit_smul]

/-- **Uniqueness of the dominant neutral element under `Int(L)`-conjugacy of nilpositive
elements.** If `g ∈ Int(L)` carries `e₁` to `e₂` for two `sl₂` triples with dominant neutral
elements `h₁` and `h₂`, then `h₁ = h₂`. -/
theorem eq_of_mem_dominantNeutralElements_of_mem_intLieAlgebra_smul_eq
    (b : (rootSystem H).Base) {h₁ h₂ : H} {e₁ f₁ e₂ f₂ : L}
    (t₁ : IsSl2Triple (h₁ : L) e₁ f₁) (t₂ : IsSl2Triple (h₂ : L) e₂ f₂)
    (hh₁ : h₁ ∈ b.dominantNeutralElements) (hh₂ : h₂ ∈ b.dominantNeutralElements)
    {g : LinearMap.GeneralLinearGroup K L} (hg : g ∈ intLieAlgebra K L) (hge : g • e₁ = e₂) :
    h₁ = h₂ :=
  t₁.eq_of_mem_dominantNeutralElements_of_lieEquiv_apply_eq b t₂ hh₁ hh₂
    (intLieAlgebraLieEquiv ⟨g, hg⟩) (by simpa using hge)
    (fun _ hp ↦ by simpa using lift_eval_smul_of_mem_intLieAlgebra hg hp (h₁ : L))

/-- **Invariance of the weighted Dynkin diagram under `Int(L)`-conjugacy of nilpositive
elements.** -/
theorem weightedDynkinDiagram_eq_of_mem_intLieAlgebra_smul_eq
    (b : (rootSystem H).Base) {h₁ h₂ : H} {e₁ f₁ e₂ f₂ : L}
    (t₁ : IsSl2Triple (h₁ : L) e₁ f₁) (t₂ : IsSl2Triple (h₂ : L) e₂ f₂)
    (hh₁ : h₁ ∈ b.dominantNeutralElements) (hh₂ : h₂ ∈ b.dominantNeutralElements)
    {g : LinearMap.GeneralLinearGroup K L} (hg : g ∈ intLieAlgebra K L) (hge : g • e₁ = e₂) :
    b.weightedDynkinDiagram ⟨h₁, hh₁⟩ = b.weightedDynkinDiagram ⟨h₂, hh₂⟩ := by
  have heq := t₁.eq_of_mem_dominantNeutralElements_of_mem_intLieAlgebra_smul_eq b t₂ hh₁ hh₂ hg hge
  subst heq
  rfl

end IntLieAlgebra

end IsSl2Triple

namespace TauCeti

variable {K L : Type*} [Field K] [CharZero K] [IsAlgClosed K] [LieRing L] [LieAlgebra K L]
  [LieAlgebra ℚ L] [FiniteDimensional K L] [IsKilling K L] {H : LieSubalgebra K L}
  [H.IsCartanSubalgebra]

/-- **Exact count of `Int(L)`-orbits of neutral elements.** Over an algebraically closed field of
characteristic zero, the `Int(L)`-orbits of neutral elements of `sl₂` triples are in bijection with
`b.dominantNeutralElements`, so the two sets have the same cardinality. -/
theorem ncard_image_orbit_setOf_exists_isSl2Triple_eq (b : (rootSystem H).Base) :
    (MulAction.orbit (intLieAlgebra K L) '' {h : L | ∃ e f, IsSl2Triple h e f}).ncard =
      b.dominantNeutralElements.ncard := by
  rw [← b.image_orbit_dominantNeutralElements]
  exact b.injOn_orbit_intLieAlgebra_dominantNeutralElements.ncard_image

/-- **Every nonzero `ad`-nilpotent element determines a unique dominant neutral element up to
`Int(L)`.** -/
theorem existsUnique_mem_dominantNeutralElements_exists_mem_intLieAlgebra_isSl2Triple
    (b : (rootSystem H).Base) {e : L} (he : IsNilpotent (ad K L e)) (he0 : e ≠ 0) :
    ∃! h : H, h ∈ b.dominantNeutralElements ∧
      ∃ g ∈ intLieAlgebra K L, ∃ f : L, IsSl2Triple (h : L) (g • e) f := by
  obtain ⟨g₁, hg₁, h₁, hh₁, f₁, t₁⟩ :=
    exists_mem_intLieAlgebra_isSl2Triple_smul_of_isNilpotent_ad b he he0
  refine ⟨h₁, ⟨hh₁, g₁, hg₁, f₁, t₁⟩, ?_⟩
  rintro h₂ ⟨hh₂, g₂, hg₂, f₂, t₂⟩
  exact (t₁.eq_of_mem_dominantNeutralElements_of_mem_intLieAlgebra_smul_eq b t₂ hh₁ hh₂
    (mul_mem hg₂ (inv_mem hg₁)) (by rw [mul_smul, inv_smul_smul])).symm

end TauCeti
