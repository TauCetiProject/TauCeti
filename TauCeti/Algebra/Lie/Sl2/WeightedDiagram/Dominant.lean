/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Sl2.Weyl.Cartan
public import TauCeti.Algebra.Lie.Sl2.WeightedDiagram.Finite
public import TauCeti.Algebra.Lie.AdjointAction.CartanConjugacy
import TauCeti.Algebra.Lie.CartanExists
import TauCeti.Algebra.Lie.Sl2.JacobsonMorozov
import TauCeti.Algebra.Lie.Sl2.Spectrum
import TauCeti.LinearAlgebra.Eigenspace.Semisimple
import TauCeti.LinearAlgebra.RootSystem.IntegralCoweight

/-!
# Conjugating the neutral element of an `sl₂` triple into the dominant chamber

Let `L` be a finite-dimensional Lie algebra with non-degenerate Killing form over a field `K` of
characteristic zero, let `H` be a splitting Cartan subalgebra and fix a base `b` of the root system
of `H`. If the neutral element `h` of an `sl₂` triple `(h, e, f)` lies in `H`, then an inner
automorphism `g ∈ Int(L)` normalizing `H` carries the triple to a triple `(g h, g e, g f)` whose
neutral element is dominant for `b`, that is a member of
`RootPairing.Base.dominantNeutralElements b`
(`IsSl2Triple.exists_mem_intLieAlgebra_smul_mem_dominantNeutralElements`). Its simple root values,
which lie in `{0, 1, 2}`, are the labels of the weighted Dynkin diagram of the triple.

The roots take integer values at `h`, because they are eigenvalues of `ad h`
(`IsSl2Triple.exists_int_weight_apply`). An integral coweight is carried by the Weyl group into
the dominant chamber of `b` (`RootPairing.Base.exists_forall_exists_nat_root'_coweightEquiv_apply`),
and the Weyl group acts on `H` by inner automorphisms
(`TauCeti.exists_mem_intLieAlgebra_forall_smul_eq_coweightEquiv`).

Over an algebraically closed field the hypothesis that `h` lies in `H` can be dropped
(`IsSl2Triple.exists_mem_intLieAlgebra_smul_mem_dominantNeutralElements_of_isAlgClosed`). The
operator `ad h` is semisimple, so `h` lies in some Cartan subalgebra
(`TauCeti.exists_isCartanSubalgebra_mem_of_isSemisimple_ad`), and an element of `Int(L)` carries
that Cartan subalgebra onto `H` (`LieSubalgebra.exists_map_intLieAlgebraLieEquiv_eq`). Applying
Jacobson–Morozov, every nonzero `ad`-nilpotent element is `Int(L)`-conjugate to the nilpositive
element of a triple whose neutral element is dominant for `b`.

Consequently every `Int(L)`-orbit of neutral elements of `sl₂` triples meets the finite set
`RootPairing.Base.dominantNeutralElements b`, so there are only finitely many such orbits, at most
`3 ^ rank`. That each orbit meets it exactly once is proved in
`TauCeti.Algebra.Lie.Sl2.WeightedDiagram.Orbit`.

## Main results

* `IsSl2Triple.exists_mem_intLieAlgebra_smul_mem_dominantNeutralElements`: a triple whose neutral
  element lies in `H` is conjugate under `Int(L)`, by an element normalizing `H`, to a triple
  whose neutral element is dominant for `b`.
* `IsSl2Triple.exists_mem_intLieAlgebra_smul_mem_dominantNeutralElements_of_isAlgClosed`: over an
  algebraically closed field, every triple is conjugate under `Int(L)` to a triple whose neutral
  element is dominant for `b`.
* `TauCeti.exists_mem_intLieAlgebra_isSl2Triple_smul_of_isNilpotent_ad`: every nonzero
  `ad`-nilpotent element is conjugate under `Int(L)` to the nilpositive element of such a triple.
* `RootPairing.Base.image_orbit_dominantNeutralElements`: the `Int(L)`-orbits of neutral elements
  are exactly the orbits of the dominant neutral elements.
* `TauCeti.finite_image_orbit_setOf_exists_isSl2Triple` and
  `TauCeti.ncard_image_orbit_setOf_exists_isSl2Triple_le`: there are finitely many `Int(L)`-orbits
  of neutral elements, at most `3 ^ finrank K H` for a Cartan subalgebra `H`.

## References

* D. H. Collingwood and W. M. McGovern, *Nilpotent Orbits in Semisimple Lie Algebras*, Van
  Nostrand Reinhold, 1993, §3.5.
* J.-P. Serre, *Complex Semisimple Lie Algebras*, Springer, 1987, Chapter III (conjugacy of Cartan
  subalgebras).
-/

public section

namespace IsSl2Triple

open LieAlgebra LieAlgebra.IsKilling LieModule TauCeti

section Split

variable {K L : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L] [LieAlgebra ℚ L]
  [FiniteDimensional K L] [IsKilling K L] {H : LieSubalgebra K L} [H.IsCartanSubalgebra]
  [IsTriangularizable K H L]

/-- **The neutral element of an `sl₂` triple can be made dominant.** If the neutral element `h` of
an `sl₂` triple `(h, e, f)` lies in the splitting Cartan subalgebra `H`, then for any base `b` some
inner automorphism `g ∈ Int(L)` maps `H` into itself and carries the triple to an `sl₂` triple
`(g h, g e, g f)` whose neutral element is a dominant neutral element for `b`. -/
theorem exists_mem_intLieAlgebra_smul_mem_dominantNeutralElements (b : (rootSystem H).Base)
    {h : H} {e f : L} (t : IsSl2Triple (h : L) e f) :
    ∃ g ∈ intLieAlgebra K L, ∃ h' ∈ b.dominantNeutralElements,
      (∀ y : H, g • (y : L) ∈ H) ∧ g • (h : L) = h' ∧ IsSl2Triple (h' : L) (g • e) (g • f) := by
  -- a Weyl group element moving `h` into the dominant chamber, realized by an inner automorphism
  obtain ⟨w, hw⟩ := b.exists_forall_exists_nat_root'_coweightEquiv_apply h
    fun i ↦ t.exists_int_weight_apply (i : Weight K H L)
  obtain ⟨g, hg, hgH⟩ := exists_mem_intLieAlgebra_forall_smul_eq_coweightEquiv w
  -- the inner automorphism `g` carries the triple to a triple
  have t' := t.smul_of_mem_intLieAlgebra hg
  rw [hgH] at t'
  exact ⟨g, hg, _, (b.mem_dominantNeutralElements_iff _).mpr ⟨⟨_, _, t'⟩, hw⟩,
    fun y ↦ hgH y ▸ SetLike.coe_mem _, hgH h, t'⟩

end Split

variable {K L : Type*} [Field K] [CharZero K] [IsAlgClosed K] [LieRing L] [LieAlgebra K L]
  [LieAlgebra ℚ L] [FiniteDimensional K L] [IsKilling K L] {H : LieSubalgebra K L}
  [H.IsCartanSubalgebra]

/-- **Every `sl₂` triple is conjugate to one with dominant neutral element.** Over an
algebraically closed field, for any Cartan subalgebra `H` and any base `b` of its root system, some
inner automorphism `g ∈ Int(L)` carries an `sl₂` triple `(h, e, f)` to an `sl₂` triple
`(g h, g e, g f)` whose neutral element lies in `H` and is a dominant neutral element for `b`. -/
theorem exists_mem_intLieAlgebra_smul_mem_dominantNeutralElements_of_isAlgClosed
    (b : (rootSystem H).Base) {h e f : L} (t : IsSl2Triple h e f) :
    ∃ g ∈ intLieAlgebra K L, ∃ h' ∈ b.dominantNeutralElements,
      g • h = h' ∧ IsSl2Triple (h' : L) (g • e) (g • f) := by
  -- `ad h` is semisimple, so `h` lies in a Cartan subalgebra `H'`
  obtain ⟨H', hH', hhH'⟩ := exists_isCartanSubalgebra_mem_of_isSemisimple_ad
    (isSemisimple_of_iSup_eigenspace_eq_top (iSup_eigenspace_toEnd_eq_top (K := K) (M := L) t))
  -- an inner automorphism `g₁` carries `H'` onto `H`, and so `h` into `H`
  obtain ⟨g₁, hg₁⟩ := H'.exists_map_intLieAlgebraLieEquiv_eq H
  have hg₁h : (g₁ : LinearMap.GeneralLinearGroup K L) • h ∈ H := by
    rw [← hg₁]
    exact ⟨h, hhH', by simp⟩
  -- then an inner automorphism `g₂` normalizing `H` makes it dominant
  obtain ⟨g₂, hg₂, h', hh', -, hg₂h, t₂⟩ :=
    exists_mem_intLieAlgebra_smul_mem_dominantNeutralElements b (h := ⟨_, hg₁h⟩)
      (t.smul_of_mem_intLieAlgebra g₁.2)
  exact ⟨g₂ * g₁, mul_mem hg₂ g₁.2, h', hh', by rwa [mul_smul],
    by simpa only [mul_smul] using t₂⟩

end IsSl2Triple

open LieAlgebra LieAlgebra.IsKilling LieModule Module

namespace RootPairing.Base

open TauCeti

variable {K L : Type*} [Field K] [CharZero K] [IsAlgClosed K] [LieRing L] [LieAlgebra K L]
  [LieAlgebra ℚ L] [FiniteDimensional K L] [IsKilling K L] {H : LieSubalgebra K L}
  [H.IsCartanSubalgebra]

/-- **Orbits of neutral elements.** Over an algebraically closed field, the `Int(L)`-orbits of
neutral elements of `sl₂` triples are exactly the orbits of the dominant neutral elements for any
base `b` of the root system of a Cartan subalgebra. -/
theorem image_orbit_dominantNeutralElements (b : (rootSystem H).Base) :
    (fun h : H ↦ MulAction.orbit (intLieAlgebra K L) (h : L)) '' b.dominantNeutralElements =
      MulAction.orbit (intLieAlgebra K L) '' {h : L | ∃ e f, IsSl2Triple h e f} := by
  refine Set.Subset.antisymm ?_ ?_
  · rintro _ ⟨h, hh, rfl⟩
    exact ⟨h, ((b.mem_dominantNeutralElements_iff h).mp hh).1, rfl⟩
  · rintro _ ⟨h, ⟨e, f, t⟩, rfl⟩
    obtain ⟨g, hg, h', hh', hgh, -⟩ :=
      t.exists_mem_intLieAlgebra_smul_mem_dominantNeutralElements_of_isAlgClosed b
    refine ⟨h', hh', ?_⟩
    dsimp only
    rw [← hgh]
    exact MulAction.orbit_smul (⟨g, hg⟩ : intLieAlgebra K L) h

end RootPairing.Base

namespace TauCeti

variable {K L : Type*} [Field K] [CharZero K] [IsAlgClosed K] [LieRing L] [LieAlgebra K L]
  [LieAlgebra ℚ L] [FiniteDimensional K L] [IsKilling K L] {H : LieSubalgebra K L}
  [H.IsCartanSubalgebra]

/-- **Nilpotent elements with dominant neutral element.** Over an algebraically closed field, for
any Cartan subalgebra `H` and any base `b` of its root system, every nonzero `ad`-nilpotent element
`e` is conjugate under `Int(L)` to the nilpositive element of an `sl₂` triple whose neutral element
lies in `H` and is a dominant neutral element for `b`. -/
theorem exists_mem_intLieAlgebra_isSl2Triple_smul_of_isNilpotent_ad (b : (rootSystem H).Base)
    {e : L} (he : IsNilpotent (ad K L e)) (he0 : e ≠ 0) :
    ∃ g ∈ intLieAlgebra K L, ∃ h ∈ b.dominantNeutralElements, ∃ f : L,
      IsSl2Triple (h : L) (g • e) f := by
  obtain ⟨h, f, t⟩ := exists_isSl2Triple_of_isNilpotent_ad he he0
  obtain ⟨g, hg, h', hh', -, t'⟩ :=
    t.exists_mem_intLieAlgebra_smul_mem_dominantNeutralElements_of_isAlgClosed b
  exact ⟨g, hg, h', hh', _, t'⟩

variable (K L) in
/-- **Finitely many orbits of neutral elements.** Over an algebraically closed field, the neutral
elements of `sl₂` triples fall into finitely many `Int(L)`-orbits. -/
theorem finite_image_orbit_setOf_exists_isSl2Triple :
    (MulAction.orbit (intLieAlgebra K L) '' {h : L | ∃ e f, IsSl2Triple h e f}).Finite := by
  obtain ⟨x, hx⟩ := exists_isCartanSubalgebra_engel K L
  let b := (rootSystem (LieSubalgebra.engel K x)).nonempty_base.some
  rw [← b.image_orbit_dominantNeutralElements]
  exact b.finite_dominantNeutralElements.image _

variable (K L H) in
/-- **Counting orbits of neutral elements.** Over an algebraically closed field, the neutral
elements of `sl₂` triples fall into at most `3 ^ finrank K H` orbits under `Int(L)`, where `H` is
any Cartan subalgebra. -/
theorem ncard_image_orbit_setOf_exists_isSl2Triple_le :
    (MulAction.orbit (intLieAlgebra K L) '' {h : L | ∃ e f, IsSl2Triple h e f}).ncard ≤
      3 ^ finrank K H := by
  let b := (rootSystem H).nonempty_base.some
  rw [← b.image_orbit_dominantNeutralElements]
  exact (Set.ncard_image_le b.finite_dominantNeutralElements).trans
    b.ncard_dominantNeutralElements_le

end TauCeti
