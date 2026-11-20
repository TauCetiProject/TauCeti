/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.AdjointAction.SymmetricInvariants
public import TauCeti.Algebra.Lie.HighestWeight.CentralCharacter.Linear
public import TauCeti.Algebra.Lie.Sl2.WeightedDiagram.Dominant
import Mathlib.Data.Set.Card
import TauCeti.Algebra.Lie.AdjointAction.ExpAdSubgroup
import TauCeti.Algebra.Lie.HighestWeight.CentralCharacter.OrbitSeparation
import TauCeti.Algebra.Lie.HighestWeight.ChevalleyRestriction
import TauCeti.Algebra.Lie.Sl2.JacobsonMorozov
import TauCeti.LinearAlgebra.RootSystem.IntegralCoweight

/-!
# Uniqueness of dominant neutral elements and weighted Dynkin diagrams

Let `L` be a finite-dimensional Lie algebra with nondegenerate Killing form over a field `K` of
characteristic zero, let `H` be a splitting Cartan subalgebra, and let `b` be a base of the root
system `LieAlgebra.IsKilling.rootSystem H`.

Every `sl₂` triple over an algebraically closed field can be conjugated by `Int(L)` so that its
neutral element lies in `RootPairing.Base.dominantNeutralElements b`
(`IsSl2Triple.exists_mem_intLieAlgebra_smul_mem_dominantNeutralElements_of_isAlgClosed`). This file
proves the complementary uniqueness statements:

1. **Uniqueness in a Weyl orbit and under Weyl invariants.** Over any field of characteristic zero
   splitting `H`, at most one dominant neutral element lies in a given Weyl orbit or realizes a
   given character on `S(H)^W`
   (`RootPairing.Base.eq_of_mem_dominantNeutralElements_of_coweightEquiv_eq`,
   `RootPairing.Base.eq_of_mem_dominantNeutralElements_of_forall_mem_linearInvariants_lift_eq`).
2. **Separation by `S(L*)^L`.** Over an algebraically closed field, Chevalley's restriction theorem
   and Weyl-chamber uniqueness
   (`RootPairing.Base.eq_of_forall_mem_lieInvariants_lift_eval_eq_of_dominant`)
   show that at most one element of `H` where every simple root of `b` takes a natural value
   realizes a given invariant character on `S(L*)^L`.
3. **Passage from the nilpositive element to the neutral element.** For `sl₂` triples
   `(h₁, e₁, f₁)` and `(h₂, e₂, f₂)` whose neutral elements lie in
   `RootPairing.Base.dominantNeutralElements b`, any Lie algebra automorphism `φ : L ≃ₗ⁅K⁆ L`
   carrying `e₁` to `e₂` and preserving `S(L*)^L` forces `h₁ = h₂`
   (`IsSl2Triple.eq_of_mem_dominantNeutralElements_of_lieEquiv_apply_eq`): Kostant's conjugacy
   theorem conjugates `(φ h₁, e₂, φ f₁)` to `(h₂, e₂, f₂)` by an element of
   `expAdSubgroup K e₂ ≤ Int(L)`, which also preserves `S(L*)^L`, so `h₁` and `h₂` agree on
   `S(L*)^L`. In particular, each `Int(L)`-orbit of neutral elements meets
   `b.dominantNeutralElements` in a unique point
   (`RootPairing.Base.injOn_orbit_dominantNeutralElements`), and the weighted Dynkin diagram depends
   only on the `Int(L)`-orbit of the nilpositive element.

## Main results

* `RootPairing.Base.eq_of_mem_dominantNeutralElements_of_coweightEquiv_eq` and
  `RootPairing.Base.eq_of_mem_dominantNeutralElements_of_forall_mem_linearInvariants_lift_eq`:
  dominant neutral elements in the same Weyl orbit, or agreeing on `S(H)^W`, coincide.
* `RootPairing.Base.eq_of_mem_dominantNeutralElements_of_mem_intLieAlgebra_smul_eq`,
  `RootPairing.Base.injOn_orbit_dominantNeutralElements`,
  `IsSl2Triple.existsUnique_mem_dominantNeutralElements_mem_orbit_intLieAlgebra`, and
  `TauCeti.ncard_image_orbit_setOf_exists_isSl2Triple_eq`: distinct dominant neutral elements have
  disjoint `Int(L)`-orbits, so the number of `Int(L)`-orbits of neutral elements equals
  `b.dominantNeutralElements.ncard`.
* `IsSl2Triple.eq_of_mem_dominantNeutralElements_of_lieEquiv_apply_eq` and
  `IsSl2Triple.weightedDynkinDiagram_eq_of_lieEquiv_apply_eq`: an invariant-preserving Lie
  automorphism carrying `e₁` to `e₂` identifies the dominant neutral elements `h₁` and `h₂` and
  their weighted Dynkin diagrams.
* `IsSl2Triple.eq_of_mem_dominantNeutralElements_of_mem_intLieAlgebra_smul_eq`,
  `IsSl2Triple.weightedDynkinDiagram_eq_of_mem_intLieAlgebra_smul_eq`, and
  `TauCeti.existsUnique_mem_dominantNeutralElements_exists_mem_intLieAlgebra_isSl2Triple`:
  `Int(L)`-conjugate nilpositive elements share a unique dominant neutral element and equal
  weighted Dynkin diagrams.

## References

* D. H. Collingwood and W. M. McGovern, *Nilpotent Orbits in Semisimple Lie Algebras*, Van
  Nostrand Reinhold, 1993, §3.5.
* R. W. Carter, *Finite Groups of Lie Type: Conjugacy Classes and Complex Characters*, Wiley,
  1985, §5.6.
* N. Bourbaki, *Lie Groups and Lie Algebras*, Chapters 7–9, Chapter VIII, §11, no. 2, Proposition 3.
-/

public section

open LieAlgebra LieAlgebra.IsKilling LieModule Module _root_.SymmetricAlgebra
open TauCeti.SymmetricAlgebra

namespace RootPairing.Base

open TauCeti

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

/-- **Invariance of the weighted Dynkin diagram under nilpositive conjugacy.** Under the hypotheses
of `IsSl2Triple.eq_of_mem_dominantNeutralElements_of_lieEquiv_apply_eq`, `h₁` and `h₂` have the same
weighted Dynkin diagram. -/
theorem weightedDynkinDiagram_eq_of_lieEquiv_apply_eq (b : (rootSystem H).Base)
    {h₁ h₂ : H} {e₁ f₁ e₂ f₂ : L}
    (t₁ : IsSl2Triple (h₁ : L) e₁ f₁) (t₂ : IsSl2Triple (h₂ : L) e₂ f₂)
    (hh₁ : h₁ ∈ b.dominantNeutralElements) (hh₂ : h₂ ∈ b.dominantNeutralElements)
    (φ : L ≃ₗ⁅K⁆ L) (hφe : φ e₁ = e₂)
    (hφinv : ∀ p ∈ lieInvariants K L (Dual K L), ∀ z : L,
      lift (Dual.eval K L (φ z)) p = lift (Dual.eval K L z) p) :
    b.weightedDynkinDiagram ⟨h₁, hh₁⟩ = b.weightedDynkinDiagram ⟨h₂, hh₂⟩ := by
  congr 1
  exact Subtype.ext (t₁.eq_of_mem_dominantNeutralElements_of_lieEquiv_apply_eq b t₂ hh₁ hh₂ φ hφe
    hφinv)

end LieEquiv

section IntConjugacy

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
  refine b.injOn_orbit_dominantNeutralElements hh'' hh' ?_
  dsimp only
  have hgh' : (⟨g, hg⟩ : intLieAlgebra K L) • h = (h' : L) := hgh
  have hg₁' : g₁ • h = (h'' : L) := hg₁
  rw [← hg₁', ← hgh', MulAction.orbit_smul, MulAction.orbit_smul]

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
  exact b.injOn_orbit_dominantNeutralElements.ncard_image

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
