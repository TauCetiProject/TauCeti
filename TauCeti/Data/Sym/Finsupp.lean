/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Finsupp.Multiset
public import Mathlib.Data.Finsupp.Weight

/-!
# Symmetric powers and multiplicity functions

`TauCeti.symEquivFinsuppDegree` identifies unordered tuples of length `n` with finitely supported
functions to `ℕ` of total degree `n`. Its underlying function records the multiplicity of each
entry.
-/

public section

namespace TauCeti

universe w

/-- Unordered `n`-tuples in `ι` (`Sym ι n`) are equivalent to exponent vectors `ι →₀ ℕ` of
total degree `n`. -/
noncomputable def symEquivFinsuppDegree (ι : Type w) (n : ℕ) :
    Sym ι n ≃ {d : ι →₀ ℕ // d.degree = n} := by
  classical
  exact (Sym.equivNatSum ι n).trans
    (Equiv.subtypeEquiv (Equiv.refl _) (fun d => by
      simp [Finsupp.degree_eq_weight_one, Finsupp.weight_apply, Function.id_def]))

/-- The exponent vector of an unordered tuple records its multiplicities. -/
@[simp]
theorem coe_symEquivFinsuppDegree_apply (ι : Type w) [DecidableEq ι] (n : ℕ)
    (s : Sym ι n) : (symEquivFinsuppDegree ι n s).1 = (s : Multiset ι).toFinsupp := by
  ext i
  simp only [symEquivFinsuppDegree, Equiv.trans_apply, Equiv.subtypeEquiv_apply,
    Equiv.refl_apply, Sym.coe_equivNatSum_apply_apply, Multiset.toFinsupp_apply]
  -- Reconcile the classical DecidableEq used by the equivalence with the supplied instance.
  congr 1

end TauCeti
