/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Sl2.Weyl.Cartan
public import TauCeti.Algebra.Lie.Sl2.WeightedDiagram.Finite
import TauCeti.Algebra.Lie.Sl2.Spectrum
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

Only a triple whose neutral element already lies in the fixed Cartan subalgebra `H` is treated.
Moving the neutral element of an arbitrary triple into `H` uses the conjugacy of Cartan
subalgebras, which is not proved here.

## Main results

* `IsSl2Triple.exists_mem_intLieAlgebra_smul_mem_dominantNeutralElements`: a triple whose neutral
  element lies in `H` is conjugate under `Int(L)`, by an element normalizing `H`, to a triple
  whose neutral element is dominant for `b`.

## References

* D. H. Collingwood and W. M. McGovern, *Nilpotent Orbits in Semisimple Lie Algebras*, Van
  Nostrand Reinhold, 1993, §3.5.
-/

public section

namespace IsSl2Triple

open LieAlgebra LieAlgebra.IsKilling LieModule TauCeti

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
  have t' : IsSl2Triple (g • (h : L)) (g • e) (g • f) := by
    simpa using t.map (intLieAlgebraLieEquiv ⟨g, hg⟩).toLieHom
      (by simpa [smul_ne_zero_iff_ne] using t.h_ne_zero)
  rw [hgH] at t'
  exact ⟨g, hg, _, (b.mem_dominantNeutralElements_iff _).mpr ⟨⟨_, _, t'⟩, hw⟩,
    fun y ↦ hgH y ▸ SetLike.coe_mem _, hgH h, t'⟩

end IsSl2Triple
