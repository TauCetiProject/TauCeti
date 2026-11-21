/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.HolomorphicFunctions.NormalFamilies
import TauCeti.Analysis.Complex.UniformLimit
import TauCeti.Topology.ContinuousMap.Ascoli

/-!
# Montel's selection theorem

A locally bounded sequence of holomorphic maps on an open subset `Ω` of a proper (equivalently,
finite-dimensional) complex normed space, such as `ℂ` or `ℂⁿ`, into a proper complex normed space
has a subsequence converging locally uniformly on `Ω` to a holomorphic map. In one variable this
normal-family compactness supports extremal arguments such as the Riemann mapping theorem, where
the target is `ℂ`, and supplies the subsequence selection used by Vitali's theorem in
`Conformal/Vitali.lean`. In several variables it is the compactness input to the Cartan–Serre
finiteness theorem for coherent analytic cohomology.

`HolomorphicFunctions/Montel/Precompact.lean` gives the equivalent compactness form: the
continuous restrictions form a relatively compact subset of `C(↥Ω, E)` with its compact-open
topology, exactly when the family is locally bounded.

The equicontinuity theorem `TauCeti.IsLocallyBoundedOn.equicontinuousOn` and the pointwise norm
bounds of local boundedness, which lie in compact closed balls since `E` is proper, are the
hypotheses of the Arzelà–Ascoli selection theorem
`TauCeti.exists_strictMono_tendstoLocallyUniformlyOn_of_equicontinuousOn`. It extracts a locally
uniformly convergent subsequence, and
`TendstoLocallyUniformlyOn.differentiableOn_of_locallyCompactSpace` gives holomorphy of the limit.

## Main results

* `TauCeti.montel`: a locally bounded sequence of holomorphic maps on an open subset of `ℂⁿ` into
  a proper complex normed space has a locally uniformly convergent subsequence with holomorphic
  limit.

## References

* L. Ahlfors, *Complex Analysis*, Ch. 5 §5.
* J. B. Conway, *Functions of One Complex Variable I* (GTM 11), Ch. VII §2.
* J.-P. Demailly, *Complex Analytic and Differential Geometry*, Chapter I, (3.12), for several
  variables.
* The Montel equicontinuity argument in the Riemann mapping formalization
  [mathlib4#33505](https://github.com/leanprover-community/mathlib4/pull/33505).
-/

public section

open Complex Metric Filter Topology Set

namespace TauCeti

variable {V E : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [ProperSpace V]
  [NormedAddCommGroup E] [NormedSpace ℂ E] {Ω : Set V} {F : ℕ → V → E}

/-- **Montel's selection theorem.** A locally bounded sequence of holomorphic maps on an open
subset `Ω` of a proper complex normed space `V`, such as `ℂ` or `ℂⁿ`, into a proper complex normed
space `E` has a subsequence converging locally uniformly on `Ω` to a holomorphic map.

Over `ℂ`, properness of a normed space is equivalent to finite-dimensionality; in particular, the
result applies to scalar-valued holomorphic functions of finitely many complex variables. -/
theorem montel [ProperSpace E] (hΩ : IsOpen Ω) (hF : ∀ n, DifferentiableOn ℂ (F n) Ω)
    (hb : IsLocallyBoundedOn F Ω) :
    ∃ (φ : ℕ → ℕ) (g : V → E), StrictMono φ ∧ DifferentiableOn ℂ g Ω ∧
      TendstoLocallyUniformlyOn (fun n => F (φ n)) g atTop Ω := by
  obtain ⟨φ, hφ, g, -, hg⟩ := exists_strictMono_tendstoLocallyUniformlyOn_of_equicontinuousOn hΩ
    (hb.equicontinuousOn hΩ hF) fun x hx => (hb.exists_forall_norm_le hx).elim fun C hC =>
      ⟨closedBall 0 C, isCompact_closedBall _ _, fun n => mem_closedBall_zero_iff.2 (hC n)⟩
  exact ⟨φ, g, hφ, hg.differentiableOn_of_locallyCompactSpace
    (Eventually.of_forall fun n => hF (φ n)) hΩ, hg⟩

end TauCeti
