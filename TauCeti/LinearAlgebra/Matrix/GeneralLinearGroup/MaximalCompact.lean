/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Group.Units
public import TauCeti.Analysis.Matrix.Compact
public import TauCeti.Analysis.Matrix.EuclideanLin
public import TauCeti.Analysis.Matrix.Polar
public import TauCeti.RepresentationTheory.Compact.UnitaryModel
public import TauCeti.Topology.Algebra.Group.Subgroup
public import TauCeti.Topology.Algebra.UnitaryGroup

/-!
# The maximal compact subgroups of the real and complex general linear groups

For `𝕜 = ℝ` or `ℂ` and a finite index type `ι`, the unitary subgroup `U = unitarySubgroup (GL ι 𝕜)`
(the orthogonal group `O(n)` over `ℝ`, the unitary group `U(n)` over `ℂ`) is a compact subgroup of
`GL ι 𝕜` (`Matrix.GeneralLinearGroup.isCompact_unitarySubgroup`), and it is the largest compact
subgroup up to conjugacy:

* **maximality**: a compact subgroup of `GL ι 𝕜` containing `U` is `U`;
* **conjugacy**: every compact subgroup of `GL ι 𝕜` is conjugate into `U`.

Together these say that the maximal compact subgroups of `GL ι 𝕜` are exactly the conjugates of `U`.
This is the matrix-group instance of two structural facts about a reductive group and its maximal
compact subgroup: `U(n)` is a maximal compact subgroup of its complexification `GLₙ(ℂ)`, and
`O(n)` is the maximal compact subgroup `K` of `GLₙ(ℝ)` occurring in the Cartan, Iwasawa and `KAK`
decompositions.

The two proofs are the classical ones.

For maximality, take `g` in a compact subgroup `K ⊇ U` and use its polar decomposition
`g = P V`. The unitary factor `V` belongs to `K`, so the positive factor `P = g V⁻¹` belongs to
`K` too. The real trace is bounded on `K`, whereas powers of any eigenvalue greater than one
would force the traces of powers of `P` to be unbounded. Applying this to `P` and `P⁻¹` forces
`P = 1`, hence `g` is unitary. The trace-growth argument is
`Matrix.PosSemidef.eq_one_of_mem_isCompact_subgroup`.

For conjugacy, Weyl's unitarian trick (`ContRepresentation.exists_isUnitary_congr`) applies to the
tautological representation of the compact group `K` on `EuclideanSpace 𝕜 ι`: averaging the inner
product over Haar measure of `K` and changing coordinates by the automorphism standardizing the
averaged form makes every element of `K` an isometry. The matrix of that automorphism conjugates
`K` into `U`, by `Matrix.mem_unitaryGroup_iff_inner_toEuclideanCLM`.

## Main results

* `Matrix.GeneralLinearGroup.eq_unitarySubgroup_of_isCompact_of_le`: a compact subgroup containing
  the unitary subgroup is the unitary subgroup.
* `Matrix.GeneralLinearGroup.exists_conj_smul_le_unitarySubgroup`: every compact subgroup is
  conjugate into the unitary subgroup.
* `Matrix.GeneralLinearGroup.maximal_isCompact_iff`: the maximal compact subgroups are exactly the
  conjugates of the unitary subgroup.

## References

* A. W. Knapp, *Lie Groups Beyond an Introduction*, second edition, Chapter VI.
* B. C. Hall, *Lie Groups, Lie Algebras, and Representations*, second edition, Section 2.5.
-/

public section

open Matrix Pointwise
open scoped ComplexOrder InnerProductSpace

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} [Fintype ι] [DecidableEq ι]

namespace Matrix.GeneralLinearGroup

open scoped MatrixOrder in
/-- **The unitary subgroup is a maximal compact subgroup of `GL ι 𝕜`**, in the elementwise form:
an element of a compact subgroup containing every unitary matrix is unitary. -/
theorem mem_unitarySubgroup_of_isCompact_of_le {K : Subgroup (GL ι 𝕜)}
    (hK : IsCompact (K : Set (GL ι 𝕜))) (hUK : unitarySubgroup (GL ι 𝕜) ≤ K) {g : GL ι 𝕜}
    (hg : g ∈ K) : g ∈ unitarySubgroup (GL ι 𝕜) := by
  let V := Units.polarUnitary g
  let P := g * (Unitary.toUnits V)⁻¹
  have hV : Unitary.toUnits V ∈ unitarySubgroup (GL ι 𝕜) := by simp
  have hP : (P : Matrix ι ι 𝕜) = CFC.sqrt ((g : Matrix ι ι 𝕜) * star (g : Matrix ι ι 𝕜)) := by
    apply (Unitary.mul_left_inj V).mp
    rw [Units.sqrt_mul_star_mul_polarUnitary]
    exact congrArg Units.val (inv_mul_cancel_right g (Unitary.toUnits V))
  have hPone : P = 1 :=
    (hP.symm ▸ (posDef_sqrt_mul_star g).posSemidef).eq_one_of_mem_isCompact_subgroup
      hK (K.mul_mem hg (K.inv_mem (hUK hV)))
  have hgV : g = Unitary.toUnits V := (mul_inv_eq_one.mp hPone)
  exact hgV ▸ hV

/-- **The unitary subgroup is a maximal compact subgroup of `GL ι 𝕜`.** A compact subgroup that
contains every unitary matrix is the unitary subgroup. Over `ℝ` this is the orthogonal group
`O(n)`, and over `ℂ` the unitary group `U(n)`. -/
theorem eq_unitarySubgroup_of_isCompact_of_le {K : Subgroup (GL ι 𝕜)}
    (hK : IsCompact (K : Set (GL ι 𝕜))) (hUK : unitarySubgroup (GL ι 𝕜) ≤ K) :
    K = unitarySubgroup (GL ι 𝕜) :=
  le_antisymm (fun _ hg ↦ mem_unitarySubgroup_of_isCompact_of_le hK hUK hg) hUK

/-- The tautological representation of a subgroup of `GL ι 𝕜` on `EuclideanSpace 𝕜 ι`. -/
private noncomputable def tautologicalRep (K : Subgroup (GL ι 𝕜)) :
    ContRepresentation 𝕜 K (EuclideanSpace 𝕜 ι) :=
  .ofMonoidHom <| (toEuclideanCLM (n := ι) (𝕜 := 𝕜)).toAlgEquiv.toMonoidHom.comp
    ((Units.coeHom (Matrix ι ι 𝕜)).comp K.subtype)

private theorem tautologicalRep_apply (K : Subgroup (GL ι 𝕜)) (k : K) :
    tautologicalRep K k = toEuclideanCLM (n := ι) (𝕜 := 𝕜) ((k : GL ι 𝕜) : Matrix ι ι 𝕜) :=
  (rfl)

private theorem continuous_tautologicalRep (K : Subgroup (GL ι 𝕜)) :
    Continuous (tautologicalRep K) := by
  have hc : Continuous (toEuclideanCLM (n := ι) (𝕜 := 𝕜)) :=
    LinearMap.continuous_of_finiteDimensional
      (toEuclideanCLM (n := ι) (𝕜 := 𝕜)).toAlgEquiv.toLinearEquiv.toLinearMap
  exact hc.comp (Units.continuous_val.comp continuous_subtype_val)

/-- **Every compact subgroup of `GL ι 𝕜` is conjugate into the unitary subgroup.** This is Weyl's
unitarian trick: the Haar average of the standard inner product over a compact subgroup `K` is a
`K`-invariant inner product, and an invertible matrix carrying it to the standard one conjugates `K`
into the unitary matrices. -/
theorem exists_conj_smul_le_unitarySubgroup {K : Subgroup (GL ι 𝕜)}
    (hK : IsCompact (K : Set (GL ι 𝕜))) :
    ∃ g : GL ι 𝕜, MulAut.conj g • K ≤ unitarySubgroup (GL ι 𝕜) := by
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let : MeasurableSpace K := borel K
  have : BorelSpace K := ⟨rfl⟩
  obtain ⟨e, he⟩ := (tautologicalRep K).exists_isUnitary_congr (continuous_tautologicalRep K)
  -- The invertible matrix of the automorphism `e`.
  let B : GL ι 𝕜 := Units.map
    ((toEuclideanCLM (n := ι) (𝕜 := 𝕜)).symm : (EuclideanSpace 𝕜 ι →L[𝕜] _) →* Matrix ι ι 𝕜)
    e.toUnit
  refine ⟨B, fun _ hx ↦ ?_⟩
  obtain ⟨k, hk, rfl⟩ := (Subgroup.mem_smul_pointwise_iff_exists _ _ _).mp hx
  rw [mem_unitarySubgroup_iff, TauCeti.mem_unitary_units_iff]
  refine mem_unitaryGroup_iff_inner_toEuclideanCLM.mpr fun x y ↦ ?_
  -- The Euclidean operator of `B k B⁻¹` is the transported action `e ∘ k ∘ e⁻¹`.
  have hop (z : EuclideanSpace 𝕜 ι) :
      toEuclideanCLM (n := ι) (𝕜 := 𝕜) ((MulAut.conj B • k : GL ι 𝕜) : Matrix ι ι 𝕜) z =
        ContinuousLinearEquiv.congr e (tautologicalRep K) ⟨k, hk⟩ z := by
    simp [tautologicalRep_apply, MulAut.smul_def, B, ContinuousLinearEquiv.toUnit]
  rw [hop, hop]
  exact he.inner_map_map _ x y

/-- **The maximal compact subgroups of `GL ι 𝕜` are the conjugates of the unitary subgroup.** Over
`ℝ` these are the conjugates of the orthogonal group `O(n)`, and over `ℂ` of the unitary group
`U(n)`. -/
theorem maximal_isCompact_iff {K : Subgroup (GL ι 𝕜)} :
    Maximal (fun H : Subgroup (GL ι 𝕜) ↦ IsCompact (H : Set (GL ι 𝕜))) K ↔
      ∃ g : GL ι 𝕜, K = MulAut.conj g • unitarySubgroup (GL ι 𝕜) := by
  constructor
  · intro hK
    obtain ⟨g, hg⟩ := exists_conj_smul_le_unitarySubgroup hK.1
    have hle : K ≤ MulAut.conj g⁻¹ • unitarySubgroup (GL ι 𝕜) := by
      rwa [map_inv, ← Subgroup.pointwise_smul_subset_iff]
    exact ⟨g⁻¹,
      le_antisymm hle (hK.2 (Subgroup.isCompact_conj_smul _ isCompact_unitarySubgroup) hle)⟩
  · rintro ⟨g, rfl⟩
    refine ⟨Subgroup.isCompact_conj_smul g isCompact_unitarySubgroup, fun L hL hle ↦ ?_⟩
    rw [Subgroup.pointwise_smul_subset_iff] at hle
    rw [← map_inv] at hle
    rw [← eq_unitarySubgroup_of_isCompact_of_le (Subgroup.isCompact_conj_smul _ hL) hle, map_inv,
      smul_inv_smul]

end Matrix.GeneralLinearGroup
