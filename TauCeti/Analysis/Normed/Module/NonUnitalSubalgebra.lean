/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Basic

/-!
# Normed-space structure on non-unital subalgebras

Mathlib makes every subalgebra of a normed algebra a normed algebra
(`SubalgebraClass.toNormedAlgebra`), with the norm of its seminormed ring structure. For a
non-unital subalgebra `s` of a non-unital seminormed ring `E` that is a normed space over `𝕜`, the
seminormed group structure found on `s` is that of its non-unital seminormed ring structure
(`NonUnitalSubringClass.toNonUnitalSeminormedRing`), while the normed space structure of
`SubmoduleClass.toNormedSpace` is stated for the seminormed group of an additive subgroup. The two
agree only after unfolding, so bounded operators and functionals on `s` (for example
`StrongDual 𝕜 s`) cannot find their norm. `NonUnitalSubalgebraClass.toNormedSpace` supplies the
normed space structure over the ring norm, as `SubalgebraClass.toNormedAlgebra` does for unital
subalgebras.
-/

public section

variable {S 𝕜 E : Type*} [NormedField 𝕜] [NonUnitalSeminormedRing E] [NormedSpace 𝕜 E]
  [SetLike S E] [NonUnitalSubringClass S E] [SMulMemClass S 𝕜 E] (s : S)

/-- A non-unital subalgebra of a normed space is a normed space, for the norm of its non-unital
seminormed ring structure. -/
instance (priority := 75) NonUnitalSubalgebraClass.toNormedSpace : NormedSpace 𝕜 s where
  norm_smul_le c x := norm_smul_le c (x : E)
