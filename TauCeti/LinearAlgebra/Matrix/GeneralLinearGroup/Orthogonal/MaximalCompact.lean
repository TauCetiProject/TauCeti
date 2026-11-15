/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.Polar.Orthogonal
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.MaximalCompact
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Orthogonal.Unitary

/-!
# The maximal compact subgroups of the complex orthogonal groups

The real orthogonal group `O(n)` is a maximal compact subgroup of the complex orthogonal group
`O(n, ℂ) = {A ∈ GL(n, ℂ) | Aᵀ A = 1}`, and `SO(n)` is a maximal compact subgroup of `SO(n, ℂ)`.
These are the group halves of the identifications `O(n)_ℂ = O(n, ℂ)` and `SO(n)_ℂ = SO(n, ℂ)` of a
compact group with a maximal compact subgroup of its complexification.

Both statements are made for `𝕜 = ℝ` or `ℂ`, with `TauCeti.GLOrthogonal n 𝕜` and
`TauCeti.GLSpecialOrthogonal n 𝕜` in the roles of `O(n, 𝕜)` and `SO(n, 𝕜)`: their unitary elements
form a maximal compact subgroup. The unitary orthogonal matrices are exactly the real orthogonal
matrices (`TauCeti.GLOrthogonal.inf_unitarySubgroup_eq_map_real` and
`TauCeti.GLSpecialOrthogonal.inf_unitarySubgroup_eq_map_real`, in the imported module
`TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Orthogonal.Unitary`), so over `ℂ` this is the
maximal compactness of `O(n)` and `SO(n)`. Over `ℝ` it says only that `O(n)` and `SO(n)` are
compact.

The proof is the polar-factor argument of
`Matrix.GeneralLinearGroup.eq_inf_unitarySubgroup_of_isCompact_of_le_of_polarUnitary_mem`, which
applies to any subgroup of `GL n 𝕜` containing the unitary polar factors of its elements. The
orthogonal and special orthogonal groups are such subgroups by
`TauCeti.GLOrthogonal.toUnits_polarUnitary_mem` and
`TauCeti.GLSpecialOrthogonal.toUnits_polarUnitary_mem`.

## Main results

* `TauCeti.GLOrthogonal.isCompact_inf_unitarySubgroup`: the unitary orthogonal matrices form a
  compact group.
* `TauCeti.GLOrthogonal.eq_inf_unitarySubgroup_of_isCompact_of_le`: a compact subgroup of
  `O(n, 𝕜)` containing its unitary elements consists of unitary elements.
* `TauCeti.GLOrthogonal.maximal_isCompact_unitarySubgroup`: **`O(n)` is a maximal compact
  subgroup of `O(n, 𝕜)`**.
* `TauCeti.GLSpecialOrthogonal.maximal_isCompact_unitarySubgroup`: **`SO(n)` is a maximal compact
  subgroup of `SO(n, 𝕜)`**.

## References

* Anthony W. Knapp, *Lie Groups Beyond an Introduction*, second edition, Progress in Mathematics
  140, Birkhäuser, 2002, Chapter VI.
* Brian C. Hall, *Lie Groups, Lie Algebras, and Representations*, second edition, Graduate Texts
  in Mathematics 222, Springer, 2015, Section 2.5.
-/

public section

noncomputable section

open Matrix Matrix.GeneralLinearGroup

namespace TauCeti

variable {n : Type*} [Fintype n] [DecidableEq n]

namespace GLOrthogonal

variable (n) (𝕜 : Type*) [RCLike 𝕜]

/-- The unitary elements of the orthogonal group form a compact group. -/
theorem isCompact_inf_unitarySubgroup :
    IsCompact ((GLOrthogonal n 𝕜 ⊓ unitarySubgroup (GL n 𝕜) : Subgroup (GL n 𝕜)) :
      Set (GL n 𝕜)) := by
  rw [Subgroup.coe_inf]
  exact isCompact_unitarySubgroup.inter_left isClosed

variable {n 𝕜}

/-- **Maximal compactness in the orthogonal group**, in the ambient form: a compact subgroup of
`O(n, 𝕜)` containing every unitary orthogonal matrix consists of unitary orthogonal matrices. -/
theorem eq_inf_unitarySubgroup_of_isCompact_of_le {K : Subgroup (GL n 𝕜)}
    (hK : IsCompact (K : Set (GL n 𝕜))) (hKO : K ≤ GLOrthogonal n 𝕜)
    (hUK : GLOrthogonal n 𝕜 ⊓ unitarySubgroup (GL n 𝕜) ≤ K) :
    K = GLOrthogonal n 𝕜 ⊓ unitarySubgroup (GL n 𝕜) :=
  eq_inf_unitarySubgroup_of_isCompact_of_le_of_polarUnitary_mem
    (fun _ ↦ toUnits_polarUnitary_mem) hK hKO hUK

variable (n 𝕜)

/-- **`O(n)` is a maximal compact subgroup of `O(n, 𝕜)`.** The unitary orthogonal matrices form a
maximal compact subgroup of the orthogonal group, with its inherited topology. They are the real
orthogonal matrices, by `TauCeti.GLOrthogonal.inf_unitarySubgroup_eq_map_real`. -/
theorem maximal_isCompact_unitarySubgroup :
    Maximal (fun K : Subgroup (GLOrthogonal n 𝕜) ↦ IsCompact (K : Set (GLOrthogonal n 𝕜)))
      ((unitarySubgroup (GL n 𝕜)).subgroupOf (GLOrthogonal n 𝕜)) :=
  maximal_isCompact_unitarySubgroup_subgroupOf (fun _ ↦ toUnits_polarUnitary_mem) isClosed

end GLOrthogonal

namespace GLSpecialOrthogonal

variable (n) (𝕜 : Type*) [RCLike 𝕜]

/-- The unitary elements of the special orthogonal group form a compact group. -/
theorem isCompact_inf_unitarySubgroup :
    IsCompact ((GLSpecialOrthogonal n 𝕜 ⊓ unitarySubgroup (GL n 𝕜) : Subgroup (GL n 𝕜)) :
      Set (GL n 𝕜)) := by
  rw [Subgroup.coe_inf]
  exact isCompact_unitarySubgroup.inter_left isClosed

variable {n 𝕜}

/-- **Maximal compactness in the special orthogonal group**, in the ambient form: a compact
subgroup of `SO(n, 𝕜)` containing every unitary special orthogonal matrix consists of unitary
special orthogonal matrices. -/
theorem eq_inf_unitarySubgroup_of_isCompact_of_le {K : Subgroup (GL n 𝕜)}
    (hK : IsCompact (K : Set (GL n 𝕜))) (hKO : K ≤ GLSpecialOrthogonal n 𝕜)
    (hUK : GLSpecialOrthogonal n 𝕜 ⊓ unitarySubgroup (GL n 𝕜) ≤ K) :
    K = GLSpecialOrthogonal n 𝕜 ⊓ unitarySubgroup (GL n 𝕜) :=
  eq_inf_unitarySubgroup_of_isCompact_of_le_of_polarUnitary_mem
    (fun _ ↦ toUnits_polarUnitary_mem) hK hKO hUK

variable (n 𝕜)

/-- **`SO(n)` is a maximal compact subgroup of `SO(n, 𝕜)`.** The unitary special orthogonal
matrices form a maximal compact subgroup of the special orthogonal group, with its inherited
topology. They are the real special orthogonal matrices, by
`TauCeti.GLSpecialOrthogonal.inf_unitarySubgroup_eq_map_real`. -/
theorem maximal_isCompact_unitarySubgroup :
    Maximal
      (fun K : Subgroup (GLSpecialOrthogonal n 𝕜) ↦ IsCompact (K : Set (GLSpecialOrthogonal n 𝕜)))
      ((unitarySubgroup (GL n 𝕜)).subgroupOf (GLSpecialOrthogonal n 𝕜)) :=
  maximal_isCompact_unitarySubgroup_subgroupOf (fun _ ↦ toUnits_polarUnitary_mem) isClosed

end GLSpecialOrthogonal

end TauCeti
