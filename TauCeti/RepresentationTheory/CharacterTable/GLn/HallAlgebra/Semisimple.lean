/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.Enumerative.IncidenceAlgebra
public import Mathlib.LinearAlgebra.Semisimple
public import TauCeti.RepresentationTheory.CharacterTable.GLn.HallAlgebra.Basic
import TauCeti.Combinatorics.Enumerative.IncidenceAlgebra

/-!
# The Möbius function of the Hall algebra vanishes off semisimple classes

Over a finite field `k`, the inverse `μ = 𝟙⁻¹` of the constant function `𝟙` in the Hall algebra
(`TauCeti.HallAlgebra.moebius`) is, at the class of an endomorphism `g`, the Möbius value
`μ(⊥, ⊤)` of the finite lattice of `g`-invariant subspaces: evaluated at the restrictions of `g`
to the invariant subspaces `W`, the relation `μ ∗ 𝟙 = 1` reads
`∑_{U ≤ W} μ(g|_U) = [W = 0]` (`Module.End.sum_moebius_ofEnd_invtRestrict`), which is the
recursion defining the Möbius function.

By P. Hall's theorem (`TauCeti.exists_finset_isAtom_sup_eq_of_mu_ne_zero`), if this value
is nonzero then the whole space is a sum of minimal nonzero invariant subspaces, that is, of
simple `k[X]`-submodules, so `g` is semisimple. This route goes through Weisner's theorem and
does not use Crapo's complementation theorem.

## Main results

* `Module.End.moebius_ofEnd_eq_mu`: `μ(g)` is the Möbius value `μ(⊥, ⊤)` of the lattice
  of `g`-invariant subspaces.
* `Module.End.isSemisimple_of_moebius_ne_zero`: if `μ(g) ≠ 0`, then `g` is semisimple.

Both are stated in the namespace `Module.End` of their first explicit argument `g`, so that
dot notation `g.isSemisimple_of_moebius_ne_zero` applies; `μ` is `TauCeti.HallAlgebra.moebius`.

## References

* J. A. Green, *The characters of the finite general linear groups*, Trans. Amer. Math. Soc. 80
  (1955), 402–447.
* D. Krasula, arXiv:2403.05656, Lemma 23.
* P. Hall, *The Eulerian functions of a group*, Quart. J. Math. 7 (1936), 134–151.
* The folder `grh` of https://github.com/lsernau/grh-lean at commit
  72fead102f663d5c7a407964a13dc0cf9d977207: `New.Hall.sum_moebius_simClassOf_endOnSub` and
  `New.Hall.isSemisimple_of_moebius_ne_zero`.
-/

public section

open Module Polynomial TauCeti.HallAlgebra TauCeti.SimilarityClass

namespace Module.End

variable {k : Type*} [Field k] [Finite k] {V : Type*} [AddCommGroup V] [Module k V]
  [Module.Finite k V]

/-- At the class of `g`, the inverse `μ` of `𝟙` is the Möbius value `μ(⊥, ⊤)` of the finite
lattice of `g`-invariant subspaces. -/
theorem moebius_ofEnd_eq_mu (g : Module.End k V) [LocallyFiniteOrder g.invtSubmodule]
    [DecidableEq g.invtSubmodule] :
    moebius (ofEnd g) = IncidenceAlgebra.mu ℂ (⊥ : g.invtSubmodule) ⊤ := by
  classical
  have : Fintype g.invtSubmodule := Fintype.ofFinite _
  -- Möbius inversion of `∑_{U ≤ W} μ(g|_U) = [W = ⊥]`, evaluated at `W = ⊤`.
  have h := IncidenceAlgebra.moebius_inversion_bot (𝕜 := ℂ)
    (fun U : g.invtSubmodule ↦ moebius (ofEnd (g.invtRestrict U.prop)))
    (fun U ↦ if U = ⊥ then 1 else 0) (fun W ↦ ?_) ⊤
  · -- The restriction of `g` to `⊤` has the class of `g`; the top of the sublattice is `⊤`.
    rw [ofEnd_invtRestrict_eq_of_injective (g := g) LinearMap.id (fun _ ↦ rfl) _
      Function.injective_id (by rw [LinearMap.range_id]; rfl)] at h
    simp [h]
  · -- The two sides differ only in the decidability instances of the filter and the `if`.
    rw [← Finset.filter_ge_eq_Iic, sum_moebius_ofEnd_invtRestrict g W]
    congr 1

/-- If `μ(g) ≠ 0`, then `g` is semisimple: every `g`-invariant subspace has a `g`-invariant
complement. -/
theorem isSemisimple_of_moebius_ne_zero (g : Module.End k V) (h : moebius (ofEnd g) ≠ 0) :
    g.IsSemisimple := by
  classical
  let : Fintype g.invtSubmodule := Fintype.ofFinite _
  let : LocallyFiniteOrder g.invtSubmodule := Fintype.toLocallyFiniteOrder
  rw [moebius_ofEnd_eq_mu] at h
  -- By P. Hall's theorem `V` is a sum of atoms of the lattice of invariant subspaces, which are
  -- the simple submodules of `V` as a `k[X]`-module.
  obtain ⟨s, hs, hsup⟩ := TauCeti.exists_finset_isAtom_sup_eq_of_mu_ne_zero h
  let e : g.invtSubmodule ≃o Submodule k[X] (AEval' g) := AEval.mapSubmodule k V g
  refine IsSemisimpleModule.of_sSup_simples_eq_top (eq_top_iff.2 ?_)
  have key : s.sup id ≤ e.symm (sSup {m | IsSimpleModule k[X] m}) :=
    Finset.sup_le fun a ha ↦ e.le_symm_apply.2 <|
      le_sSup (isSimpleModule_iff_isAtom.2 ((e.isAtom_iff a).2 (hs a ha)))
  rw [hsup, top_le_iff, e.symm_apply_eq, map_top] at key
  exact key.ge

end Module.End
