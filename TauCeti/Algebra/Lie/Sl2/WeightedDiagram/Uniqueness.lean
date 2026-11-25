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

/-!
# Uniqueness of dominant neutral elements and weighted Dynkin diagrams

Let `L` be a finite-dimensional Lie algebra with nondegenerate Killing form over an algebraically
closed field `K` of characteristic zero, let `H` be a Cartan subalgebra, and let `b` be a base of
the root system `LieAlgebra.IsKilling.rootSystem H`.

By Chevalley's restriction theorem and Weyl-chamber uniqueness
(`RootPairing.Base.eq_of_forall_mem_lieInvariants_lift_eval_eq_of_dominant`), at most one element
of `H` where every simple root of `b` takes a natural value realizes a given invariant character on
`S(L*)^L`.

For `sl₂` triples `(h₁, e₁, f₁)` and `(h₂, e₂, f₂)` whose neutral elements lie in
`RootPairing.Base.dominantNeutralElements b`, any Lie algebra automorphism `φ : L ≃ₗ⁅K⁆ L` carrying
`e₁` to `e₂` and preserving `S(L*)^L` forces `h₁ = h₂`
(`IsSl2Triple.eq_of_mem_dominantNeutralElements_of_lieEquiv_apply_eq`): Kostant's conjugacy theorem
conjugates `(φ h₁, e₂, φ f₁)` to `(h₂, e₂, f₂)` by an element of `expAdSubgroup K e₂ ≤ Int(L)`,
which also preserves `S(L*)^L`, so `h₁` and `h₂` agree on `S(L*)^L`. In particular, each
`Int(L)`-orbit of neutral elements meets `b.dominantNeutralElements` in a unique point
(`RootPairing.Base.injOn_orbit_dominantNeutralElements`), so these orbits are exactly as many as
the dominant neutral elements, and the weighted Dynkin diagram depends only on the `Int(L)`-orbit
of the nilpositive element. Combined with Jacobson–Morozov, every nonzero `ad`-nilpotent element
has exactly one dominant neutral element
(`RootPairing.Base.existsUnique_mem_dominantNeutralElements_isSl2Triple_smul`).

## Main results

* `RootPairing.Base.eq_of_mem_dominantNeutralElements_of_mem_intLieAlgebra_smul_eq` and
  `RootPairing.Base.injOn_orbit_dominantNeutralElements`: distinct dominant neutral elements have
  disjoint `Int(L)`-orbits.
* `RootPairing.Base.ncard_image_orbit_setOf_exists_isSl2Triple_eq`: there are exactly as many
  `Int(L)`-orbits of neutral elements as dominant neutral elements.
* `IsSl2Triple.eq_of_mem_dominantNeutralElements_of_lieEquiv_apply_eq`: an invariant-preserving Lie
  automorphism carrying `e₁` to `e₂` identifies the dominant neutral elements `h₁` and `h₂`.
* `IsSl2Triple.eq_of_mem_dominantNeutralElements_of_mem_intLieAlgebra_smul_eq` and
  `IsSl2Triple.weightedDynkinDiagram_eq_of_mem_intLieAlgebra_smul_eq`: `Int(L)`-conjugate
  nilpositive elements share the same dominant neutral element and weighted Dynkin diagram.
* `RootPairing.Base.existsUnique_mem_dominantNeutralElements_isSl2Triple_smul`: a nonzero
  `ad`-nilpotent element has exactly one dominant neutral element.

## References

* D. H. Collingwood and W. M. McGovern, *Nilpotent Orbits in Semisimple Lie Algebras*, Van
  Nostrand Reinhold, 1993, §3.5.
* R. W. Carter, *Finite Groups of Lie Type: Conjugacy Classes and Complex Characters*, Wiley,
  1985, §5.6.
-/

public section

open LieAlgebra LieAlgebra.IsKilling LieModule Module _root_.SymmetricAlgebra
open TauCeti.SymmetricAlgebra

namespace RootPairing.Base

open TauCeti

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

/-- **Counting orbits of neutral elements exactly.** The `Int(L)`-orbits of neutral elements of
`sl₂` triples are exactly as many as the dominant neutral elements for any base `b`. -/
theorem ncard_image_orbit_setOf_exists_isSl2Triple_eq (b : (rootSystem H).Base) :
    (MulAction.orbit (intLieAlgebra K L) '' {h : L | ∃ e f, IsSl2Triple h e f}).ncard =
      b.dominantNeutralElements.ncard := by
  rw [← b.image_orbit_dominantNeutralElements, b.injOn_orbit_dominantNeutralElements.ncard_image]

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
  let g := LinearMap.GeneralLinearGroup.ofLinearEquiv ψ.toLinearEquiv
  have hg : g ∈ intLieAlgebra K L :=
    map_expAdSubgroup_le_intLieAlgebra e₂ ⟨ψ.toLinearEquiv, hψ, rfl⟩
  have hgh : g • φ (h₁ : L) = (h₂ : L) :=
    (LinearMap.GeneralLinearGroup.ofLinearEquiv_smul _ _).trans hψh
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

namespace RootPairing.Base

open TauCeti

variable {K L : Type*} [Field K] [CharZero K] [IsAlgClosed K] [LieRing L] [LieAlgebra K L]
  [LieAlgebra ℚ L] [FiniteDimensional K L] [IsKilling K L] {H : LieSubalgebra K L}
  [H.IsCartanSubalgebra]

/-- **The dominant neutral element of a nilpotent element.** For any base `b`, a nonzero
`ad`-nilpotent element `e` has exactly one dominant neutral element `h`: the neutral element of an
`sl₂` triple whose nilpositive element is an `Int(L)`-conjugate of `e`. -/
theorem existsUnique_mem_dominantNeutralElements_isSl2Triple_smul (b : (rootSystem H).Base)
    {e : L} (he : IsNilpotent (ad K L e)) (he0 : e ≠ 0) :
    ∃! h : H, h ∈ b.dominantNeutralElements ∧
      ∃ g ∈ intLieAlgebra K L, ∃ f : L, IsSl2Triple (h : L) (g • e) f := by
  obtain ⟨g, hg, h, hh, f, t⟩ :=
    exists_mem_intLieAlgebra_isSl2Triple_smul_of_isNilpotent_ad b he he0
  refine ⟨h, ⟨hh, g, hg, f, t⟩, fun h' ⟨hh', g', hg', f', t'⟩ ↦
    (t.eq_of_mem_dominantNeutralElements_of_mem_intLieAlgebra_smul_eq b t' hh hh'
      (mul_mem hg' (inv_mem hg)) ?_).symm⟩
  rw [mul_smul, inv_smul_smul]

end RootPairing.Base
