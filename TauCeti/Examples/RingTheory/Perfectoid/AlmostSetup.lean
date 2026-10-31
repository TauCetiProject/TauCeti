/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.RingTheory.Perfectoid.AlmostSetup
import TauCeti.RingTheory.Perfectoid.Padic
import TauCeti.RingTheory.Perfectoid.PseudoUniformizerRoots.Existence

/-!
# Examples of the almost setup of a perfectoid Tate ring

These examples test the almost setup `(R°, R°°)` on the perfectoid field `ℂ_p`:

* the setup is found for `ℂ_p` from its perfectoid structure alone, and its ideal is the ideal of
  topologically nilpotent elements of `𝓞_{ℂ_p}`;
* the residue module `𝓞_{ℂ_p} ⧸ 𝓞_{ℂ_p}°°` is almost zero, and so every root `ϖ ^ (1 / p ^ n)`
  of a pseudouniformiser with compatible roots, and every pseudouniformiser, acts on it by zero;
* `𝓞_{ℂ_p}` itself is not almost zero, since a pseudouniformiser does not kill `1`.

## References

* P. Scholze, *Étale cohomology of diamonds*, §3, Definition 3.21 and Example 3.22(i).
-/

open TauCeti.Huber TauCeti.Almost TauCeti.Perfectoid

variable (p : ℕ) [Fact p.Prime]

-- The almost setup of `ℂ_p` exists, and its ideal is `𝓞_{ℂ_p}°°`.
example : (almostSetup p ℂ_[p]).ideal = topologicallyNilpotentIdeal ℂ_[p] :=
  almostSetup_ideal p ℂ_[p]

-- The residue module `𝓞_{ℂ_p} ⧸ 𝓞_{ℂ_p}°°` is almost zero.
example : (almostSetup p ℂ_[p]).IsAlmostZero
    (powerBoundedSubring ℂ_[p] ⧸ (almostSetup p ℂ_[p]).ideal) :=
  (almostSetup p ℂ_[p]).isAlmostZero_quotient

-- Every root `ϖ ^ (1 / p ^ n)` acts by zero on the residue module.
example (ϖ : PseudoUniformizerRoots p ℂ_[p]) (n : ℕ)
    (x : powerBoundedSubring ℂ_[p] ⧸ (almostSetup p ℂ_[p]).ideal) :
    ϖ.rootPB n • x = 0 :=
  (almostSetup_isAlmostZero_iff_rootPB ϖ).mp (almostSetup p ℂ_[p]).isAlmostZero_quotient n x

-- `𝓞_{ℂ_p}` is not almost zero: a pseudouniformiser does not kill `1`.
example : ¬ (almostSetup p ℂ_[p]).IsAlmostZero (powerBoundedSubring ℂ_[p]) := by
  intro h
  obtain ⟨ϖ⟩ := (inferInstance : Nonempty (PseudoUniformizerRoots p ℂ_[p]))
  have h1 := (almostSetup_isAlmostZero_iff_rootPB ϖ).mp h 0 1
  rw [smul_eq_mul, mul_one] at h1
  have h2 := congrArg Subtype.val h1
  rw [PseudoUniformizerRoots.coe_rootPB, ZeroMemClass.coe_zero] at h2
  exact (ϖ.isPseudoUniformizer_root 0).isUnit.ne_zero h2
