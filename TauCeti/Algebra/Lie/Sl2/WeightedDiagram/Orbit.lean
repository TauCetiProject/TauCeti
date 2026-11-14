/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.AdjointAction.WeylConjugacy
public import TauCeti.Algebra.Lie.Sl2.WeightedDiagram.Dominant
import TauCeti.Algebra.Lie.Sl2.JacobsonMorozov
import TauCeti.LinearAlgebra.RootSystem.IntegralCoweight

/-!
# The dominant neutral element of a nilpotent orbit

Let `L` be a finite-dimensional Lie algebra with non-degenerate Killing form over an algebraically
closed field `K` of characteristic zero, `H` a Cartan subalgebra and `b` a base of its root
system. Every `Int(L)`-orbit of neutral elements of `sl₂` triples meets the finite set
`RootPairing.Base.dominantNeutralElements b`
(`RootPairing.Base.image_orbit_dominantNeutralElements`). This file proves that it meets it
exactly once.

Two dominant elements of `H` that are conjugate under `Int(L)` are Weyl-conjugate
(`TauCeti.exists_coweightEquiv_eq_of_smul_eq`), and a dominant integral coweight is the only
dominant one in its Weyl orbit
(`RootPairing.Base.coweightEquiv_apply_eq_self_of_forall_exists_nat_root'`). So the
`Int(L)`-orbits of neutral elements are in bijection with the dominant neutral elements, and
their number is the number of dominant neutral elements.

By Kostant's conjugacy theorem, triples whose nilpositive elements are `Int(L)`-conjugate have
`Int(L)`-conjugate neutral elements (`IsSl2Triple.h_mem_orbit_of_e_mem_orbit`). Hence every
nonzero `ad`-nilpotent element `e` determines a unique dominant neutral element: the neutral
element of a triple whose nilpositive element is conjugate to `e`. Its simple-root values, the
labels `RootPairing.Base.weightedDynkinDiagram`, are the weighted Dynkin diagram of the orbit of
`e`, an invariant of that orbit. Whether nilpotent orbits with the same diagram coincide is not
addressed here.

## Main results

* `RootPairing.Base.eq_of_smul_eq_of_mem_dominantNeutralElements`: two dominant neutral elements
  conjugate under `Int(L)` are equal.
* `RootPairing.Base.injOn_orbit_dominantNeutralElements` and
  `TauCeti.ncard_image_orbit_setOf_exists_isSl2Triple_eq`: distinct dominant neutral elements
  have distinct orbits, so there are exactly as many orbits of neutral elements as dominant
  neutral elements.
* `RootPairing.Base.eq_of_isSl2Triple_of_e_mem_orbit_of_mem_dominantNeutralElements`: the
  dominant neutral element of a triple depends only on the `Int(L)`-orbit of its nilpositive
  element.
* `TauCeti.existsUnique_mem_dominantNeutralElements_isSl2Triple_smul`: a nonzero `ad`-nilpotent
  element has exactly one dominant neutral element.

## References

* D. H. Collingwood and W. M. McGovern, *Nilpotent Orbits in Semisimple Lie Algebras*, Van
  Nostrand Reinhold, 1993, §3.5.
-/

public section

open LieAlgebra LieAlgebra.IsKilling TauCeti

namespace RootPairing.Base

variable {K L : Type*} [Field K] [CharZero K] [IsAlgClosed K] [LieRing L] [LieAlgebra K L]
  [LieAlgebra ℚ L] [FiniteDimensional K L] [IsKilling K L] {H : LieSubalgebra K L}
  [H.IsCartanSubalgebra] (b : (rootSystem H).Base)

/-- **A dominant neutral element is the only one in its `Int(L)`-orbit.** Two dominant neutral
elements for the base `b` that are conjugate under an inner automorphism of `L` are equal. -/
theorem eq_of_smul_eq_of_mem_dominantNeutralElements {h h' : H}
    (hh : h ∈ b.dominantNeutralElements) (hh' : h' ∈ b.dominantNeutralElements)
    {g : LinearMap.GeneralLinearGroup K L} (hg : g ∈ intLieAlgebra K L)
    (hgh : g • (h : L) = h') : h = h' := by
  obtain ⟨w, hw⟩ := exists_coweightEquiv_eq_of_smul_eq hg hgh
  rw [← hw]
  refine (b.coweightEquiv_apply_eq_self_of_forall_exists_nat_root' w
    ((b.mem_dominantNeutralElements_iff h).mp hh).2 ?_).symm
  rw [hw]
  exact ((b.mem_dominantNeutralElements_iff h').mp hh').2

/-- Distinct dominant neutral elements lie in distinct `Int(L)`-orbits. -/
theorem injOn_orbit_dominantNeutralElements :
    Set.InjOn (fun h : H ↦ MulAction.orbit (intLieAlgebra K L) (h : L))
      b.dominantNeutralElements := by
  intro h hh h' hh' hhh'
  simp only at hhh'
  obtain ⟨g, hg⟩ : (h' : L) ∈ MulAction.orbit (intLieAlgebra K L) (h : L) :=
    hhh' ▸ MulAction.mem_orbit_self _
  exact b.eq_of_smul_eq_of_mem_dominantNeutralElements hh hh' g.2 hg

/-- **The dominant neutral element is an invariant of a nilpotent orbit.** If `(h, e, f)` and
`(h', e', f')` are `sl₂` triples whose neutral elements are dominant for `b`, and `e'` is conjugate
to `e` under `Int(L)`, then `h = h'`. -/
theorem eq_of_isSl2Triple_of_e_mem_orbit_of_mem_dominantNeutralElements {h h' : H}
    (hh : h ∈ b.dominantNeutralElements) (hh' : h' ∈ b.dominantNeutralElements) {e f e' f' : L}
    (t : IsSl2Triple (h : L) e f) (t' : IsSl2Triple (h' : L) e' f')
    (he : e' ∈ MulAction.orbit (intLieAlgebra K L) e) : h = h' := by
  obtain ⟨g, hg⟩ := t.h_mem_orbit_of_e_mem_orbit t' he
  exact b.eq_of_smul_eq_of_mem_dominantNeutralElements hh hh' g.2 hg

end RootPairing.Base

namespace TauCeti

variable {K L : Type*} [Field K] [CharZero K] [IsAlgClosed K] [LieRing L] [LieAlgebra K L]
  [LieAlgebra ℚ L] [FiniteDimensional K L] [IsKilling K L] {H : LieSubalgebra K L}
  [H.IsCartanSubalgebra]

/-- **Counting orbits of neutral elements exactly.** The `Int(L)`-orbits of neutral elements of
`sl₂` triples are exactly as many as the dominant neutral elements for any base `b`. -/
theorem ncard_image_orbit_setOf_exists_isSl2Triple_eq (b : (rootSystem H).Base) :
    (MulAction.orbit (intLieAlgebra K L) '' {h : L | ∃ e f, IsSl2Triple h e f}).ncard =
      b.dominantNeutralElements.ncard := by
  rw [← b.image_orbit_dominantNeutralElements,
    b.injOn_orbit_dominantNeutralElements.ncard_image]

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
    (b.eq_of_isSl2Triple_of_e_mem_orbit_of_mem_dominantNeutralElements hh hh' t t'
      ⟨⟨g' * g⁻¹, mul_mem hg' (inv_mem hg)⟩, ?_⟩).symm⟩
  dsimp only
  rw [Subgroup.mk_smul, mul_smul, inv_smul_smul]

end TauCeti
