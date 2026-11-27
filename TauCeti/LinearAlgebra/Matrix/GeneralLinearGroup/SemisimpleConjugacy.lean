/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import TauCeti.LinearAlgebra.Charpoly.SemisimpleConjugacy

import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Conjugation

/-!
# Conjugacy of semisimple elements in the general linear group

`Matrix.GeneralLinearGroup.isConj_iff_charpoly_eq_of_isSemisimple` transports the classification
of semisimple endomorphisms by characteristic polynomial to `GLₙ` via
`Matrix.mem_orbit_conjAct_iff_exists_linearEquiv_conj`. The theorem
`Matrix.GeneralLinearGroup.isConj_map_iff_charpoly_eq_of_isSemisimple` gives the same criterion for
conjugacy over any nontrivial commutative algebra over the base field, including an algebraic
closure.
-/

public section

open Matrix

namespace Matrix.GeneralLinearGroup

variable {n K : Type*} [Fintype n] [DecidableEq n] [Field K]

/-- Semisimple elements of `GLₙ(K)` are conjugate over `K` exactly when their characteristic
polynomials agree. Semisimplicity is taken in the sense of `Module.End.IsSemisimple`, so no
splitting or separability of the characteristic polynomial is required. -/
theorem isConj_iff_charpoly_eq_of_isSemisimple {g h : GL n K}
    (hg : Module.End.IsSemisimple (g : Matrix n n K).toLin')
    (hh : Module.End.IsSemisimple (h : Matrix n n K).toLin') :
    IsConj g h ↔ (g : Matrix n n K).charpoly = (h : Matrix n n K).charpoly := by
  refine ⟨IsConj.charpoly_eq, fun hpoly ↦ ?_⟩
  have hlin : (g : Matrix n n K).toLin'.charpoly = (h : Matrix n n K).toLin'.charpoly := by
    simpa only [Matrix.charpoly_toLin'] using hpoly
  have horbit := Matrix.mem_orbit_conjAct_iff_exists_linearEquiv_conj.mpr
    (hg.exists_linearEquiv_conj_eq_of_charpoly_eq hh hlin)
  obtain ⟨c, hc⟩ := MulAction.mem_orbit_iff.mp horbit
  refine isConj_iff.mpr ⟨ConjAct.ofConjAct c, Units.ext ?_⟩
  simpa only [ConjAct.units_smul_def, Units.val_mul] using hc

/-- After mapping to a nontrivial commutative `K`-algebra, two semisimple elements of `GLₙ(K)`
are conjugate exactly when their characteristic polynomials over `K` agree. -/
theorem isConj_map_iff_charpoly_eq_of_isSemisimple {g h : GL n K}
    {S : Type*} [CommRing S] [Nontrivial S] (i : K →+* S)
    (hg : Module.End.IsSemisimple (g : Matrix n n K).toLin')
    (hh : Module.End.IsSemisimple (h : Matrix n n K).toLin') :
    IsConj (map i g) (map i h) ↔ (g : Matrix n n K).charpoly = (h : Matrix n n K).charpoly := by
  refine ⟨fun hconj ↦ ?_,
    fun hpoly ↦ (map i).map_isConj ((isConj_iff_charpoly_eq_of_isSemisimple hg hh).mpr hpoly)⟩
  apply Polynomial.map_injective i i.injective
  have hmap (x : GL n K) : ((map i x : GL n S) : Matrix n n S) = (x : Matrix n n K).map i := by
    ext r c
    exact GeneralLinearGroup.map_apply i r c x
  simpa only [hmap, Matrix.charpoly_map] using hconj.charpoly_eq

end Matrix.GeneralLinearGroup
