/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.SimilarityClass
public import TauCeti.LinearAlgebra.Semisimple.FiniteField

/-!
# Similarity classes of semisimple primary endomorphisms over finite fields

Let `L / k` be an extension of finite fields, and let `g : Module.End k W` be a semisimple
`k`-linear endomorphism of a finite-dimensional `k`-vector space `W` with
`Module.finrank k W = Module.finrank k L` whose characteristic polynomial is a power `P ^ j` of an
irreducible polynomial `P : k[X]`. By `Module.End.IsSemisimple.exists_conj_lmul_eq`, `g` has the
same similarity class in `TauCeti.SimilarityClass k` as left multiplication `Algebra.lmul k L y`
for some `y ∈ L`.

* `Module.End.IsSemisimple.exists_ofEnd_eq_ofEnd_lmul`:
  `TauCeti.SimilarityClass.ofEnd g = TauCeti.SimilarityClass.ofEnd (Algebra.lmul k L y)`.
-/

public section

namespace Module.End.IsSemisimple

open Polynomial Module TauCeti

/-- Let `L / k` be an extension of finite fields. In `TauCeti.SimilarityClass k`, any semisimple
`k`-linear endomorphism `g` of a finite-dimensional `k`-vector space `W` with
`Module.finrank k W = Module.finrank k L` and primary characteristic polynomial `P ^ j` (`P`
irreducible) has the same similarity class as left multiplication `Algebra.lmul k L y` for some
`y ∈ L`. -/
theorem exists_ofEnd_eq_ofEnd_lmul {k L W : Type*} [Field k] [Field L] [Finite L] [Algebra k L]
    [AddCommGroup W] [Module k W] [Module.Finite k W] (hdim : finrank k W = finrank k L)
    {g : End k W} {P : k[X]} {j : ℕ} (hg : g.IsSemisimple) (hP : Irreducible P)
    (h_charpoly : g.charpoly = P ^ j) :
    ∃ y : L, SimilarityClass.ofEnd g = SimilarityClass.ofEnd (Algebra.lmul k L y) := by
  obtain ⟨e, y, rfl⟩ := hg.exists_conj_lmul_eq hdim hP h_charpoly
  exact ⟨y, SimilarityClass.ofEnd_conj e _⟩

end Module.End.IsSemisimple
