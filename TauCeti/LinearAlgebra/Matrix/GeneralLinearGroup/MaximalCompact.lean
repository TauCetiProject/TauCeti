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

import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs

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
`Matrix.PosSemidef.eq_one_of_mem_isCompact_subgroup`. The argument only uses that `V` lies in `K`,
so it is stated in that form (`mem_unitarySubgroup_of_isCompact_of_polarUnitary_mem`), which also
serves subgroups of `GL ι 𝕜` stable under taking unitary polar factors, such as the special linear
and the real symplectic groups.

For conjugacy, Weyl's unitarian trick (`ContRepresentation.exists_isUnitary_congr`) applies to the
tautological representation of the compact group `K` on `EuclideanSpace 𝕜 ι`: averaging the inner
product over Haar measure of `K` and changing coordinates by the automorphism standardizing the
averaged form makes every element of `K` an isometry. The matrix of that automorphism conjugates
`K` into `U`, by `Matrix.mem_unitaryGroup_iff_inner_toEuclideanCLM`.

An arbitrary compact complex matrix subgroup meets the upper triangular matrices with nonnegative
real diagonal only at the identity. More generally, its only element with nonnegative real
spectrum is the identity. The triangular intersection is the uniqueness condition in the
Iwasawa decomposition.

## Main results

* `Matrix.GeneralLinearGroup.mem_unitarySubgroup_of_isCompact_of_polarUnitary_mem`: an element of
  a compact subgroup that also contains its unitary polar factor is unitary.
* `Matrix.GeneralLinearGroup.eq_unitarySubgroup_of_isCompact_of_le`: a compact subgroup containing
  the unitary subgroup is the unitary subgroup.
* `Matrix.GeneralLinearGroup.exists_conj_smul_le_unitarySubgroup`: every compact subgroup is
  conjugate into the unitary subgroup.
* `Matrix.GeneralLinearGroup.eq_one_of_mem_isCompact_subgroup_of_nonneg_spectrum`: an element
  of a compact matrix subgroup whose complex spectrum is nonnegative real is the identity.
* `Matrix.IsUpperTriangular.eq_one_of_mem_isCompact_subgroup_of_nonneg_diag`: a compact matrix
  subgroup meets the upper triangular matrices with nonnegative real diagonal only in the identity.
* `Matrix.GeneralLinearGroup.maximal_isCompact_iff`: the maximal compact subgroups are exactly the
  conjugates of the unitary subgroup.
* `Matrix.GeneralLinearGroup.eq_inf_unitarySubgroup_of_isCompact_of_le_of_polarUnitary_mem` and
  `Matrix.GeneralLinearGroup.maximal_isCompact_unitarySubgroup_subgroupOf`: the same maximality
  inside any closed subgroup `G` containing the unitary polar factors of its elements: the unitary
  elements of `G` form a maximal compact subgroup of `G`.

## References

* A. W. Knapp, *Lie Groups Beyond an Introduction*, second edition, Chapter VI.
* A. W. Knapp, *Lie Groups Beyond an Introduction*, first edition, Birkhäuser (1996),
  Chapter VI, §4, Theorem 6.46 (the compact/triangular intersection in the Iwasawa decomposition).
* B. C. Hall, *Lie Groups, Lie Algebras, and Representations*, second edition, Section 2.5.
-/

public section

open Matrix Pointwise
open scoped ComplexOrder InnerProductSpace

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} [Fintype ι] [DecidableEq ι]

namespace Matrix.GeneralLinearGroup

open scoped MatrixOrder in
/-- **An element of a compact subgroup that also contains its unitary polar factor is unitary.**
If `g` lies in a compact subgroup `K` of `GL ι 𝕜` together with the unitary factor `V` of its polar
decomposition `g = P V`, then `g` is unitary. -/
theorem mem_unitarySubgroup_of_isCompact_of_polarUnitary_mem {K : Subgroup (GL ι 𝕜)}
    (hK : IsCompact (K : Set (GL ι 𝕜))) {g : GL ι 𝕜} (hg : g ∈ K)
    (hV : Unitary.toUnits (Units.polarUnitary g) ∈ K) : g ∈ unitarySubgroup (GL ι 𝕜) := by
  have hPone : g * (Unitary.toUnits (Units.polarUnitary g))⁻¹ = 1 :=
    ((coe_mul_inv_toUnits_polarUnitary g).symm ▸
      (posDef_sqrt_mul_star g).posSemidef).eq_one_of_mem_isCompact_subgroup
      hK (K.mul_mem hg (K.inv_mem hV))
  rw [mul_inv_eq_one.mp hPone]
  simp

/-- **The unitary subgroup is a maximal compact subgroup of `GL ι 𝕜`**, in the elementwise form:
an element of a compact subgroup containing every unitary matrix is unitary. -/
theorem mem_unitarySubgroup_of_isCompact_of_le {K : Subgroup (GL ι 𝕜)}
    (hK : IsCompact (K : Set (GL ι 𝕜))) (hUK : unitarySubgroup (GL ι 𝕜) ≤ K) {g : GL ι 𝕜}
    (hg : g ∈ K) : g ∈ unitarySubgroup (GL ι 𝕜) :=
  mem_unitarySubgroup_of_isCompact_of_polarUnitary_mem hK hg (hUK (by simp))

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
    Continuous (tautologicalRep K) :=
  continuous_toEuclideanCLM.comp (Units.continuous_val.comp continuous_subtype_val)

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

open scoped Matrix.Norms.L2Operator in
/-- An element of a compact complex matrix subgroup with nonnegative real spectrum is the
identity. The subgroup need not be unitary for the standard inner product. -/
theorem eq_one_of_mem_isCompact_subgroup_of_nonneg_spectrum (g : GL ι ℂ)
    {K : Subgroup (GL ι ℂ)} (hK : IsCompact (K : Set (GL ι ℂ))) (hg : g ∈ K)
    (hnonneg : ∀ z ∈ spectrum ℂ (g : Matrix ι ι ℂ), 0 ≤ z) : g = 1 := by
  obtain ⟨c, hc⟩ := Matrix.GeneralLinearGroup.exists_conj_smul_le_unitarySubgroup hK
  let u : GL ι ℂ := c * g * c⁻¹
  have hu : (u : Matrix ι ι ℂ) ∈ unitary (Matrix ι ι ℂ) := by
    have humem := hc ((Subgroup.mem_smul_pointwise_iff_exists _ _ _).mpr ⟨g, hg, rfl⟩)
    exact TauCeti.mem_unitary_units_iff.mp (mem_unitarySubgroup_iff.mp humem)
  have hspec : spectrum ℂ (u : Matrix ι ι ℂ) ⊆ {1} := by
    intro z hz
    have hzg : z ∈ spectrum ℂ (g : Matrix ι ι ℂ) := by
      simpa only [u, Units.val_mul, Units.val_inv_eq_inv_val,
        spectrum.units_conjugate] using hz
    have hn := spectrum.norm_eq_one_of_unitary hu hz
    obtain ⟨r, hr, hzr⟩ := RCLike.nonneg_iff_exists_ofReal.mp (hnonneg z hzg)
    rw [← hzr, RCLike.norm_ofReal, abs_of_nonneg hr] at hn
    simp only [Set.mem_singleton_iff, ← hzr, hn, RCLike.ofReal_one]
  have huone : (u : Matrix ι ι ℂ) = 1 :=
    CFC.eq_one_of_spectrum_subset_one (R := ℂ) (u : Matrix ι ι ℂ) hspec
      (isStarNormal_of_mem_unitary hu)
  have huone' : u = 1 := Units.ext huone
  apply (MulAut.conj c).injective
  simpa only [u, MulAut.conj_apply, map_one] using huone'


/-- An upper triangular element of a compact complex matrix subgroup whose diagonal entries
are nonnegative real numbers is the identity. -/
theorem _root_.Matrix.IsUpperTriangular.eq_one_of_mem_isCompact_subgroup_of_nonneg_diag
    [LinearOrder ι]
    {g : GL ι ℂ} (htri : (g : Matrix ι ι ℂ).IsUpperTriangular)
    {K : Subgroup (GL ι ℂ)} (hK : IsCompact (K : Set (GL ι ℂ))) (hg : g ∈ K)
    (hdiag : ∀ i, 0 ≤ (g : Matrix ι ι ℂ) i i) : g = 1 := by
  apply g.eq_one_of_mem_isCompact_subgroup_of_nonneg_spectrum hK hg
  intro z hz
  have hz' := (Matrix.mem_spectrum_iff_isRoot_charpoly.mp hz).eq_zero
  rw [Matrix.charpoly_of_isUpperTriangular _ htri, Polynomial.eval_prod] at hz'
  simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] at hz'
  obtain ⟨i, _, hi⟩ := Finset.prod_eq_zero_iff.mp hz'
  rw [sub_eq_zero.mp hi]
  exact hdiag i


/-- **The maximal compact subgroups of `GL ι 𝕜` are the conjugates of the unitary subgroup.** Over
`ℝ` these are the conjugates of the orthogonal group `O(n)`, and over `ℂ` of the unitary group
`U(n)`. -/
theorem maximal_isCompact_iff {K : Subgroup (GL ι 𝕜)} :
    Maximal (fun H : Subgroup (GL ι 𝕜) ↦ IsCompact (H : Set (GL ι 𝕜))) K ↔
      ∃ g : GL ι 𝕜, K = MulAut.conj g • unitarySubgroup (GL ι 𝕜) :=
  Subgroup.maximal_isCompact_iff_exists_eq_conj_smul
    ⟨isCompact_unitarySubgroup, fun _ hL hle ↦ (eq_unitarySubgroup_of_isCompact_of_le hL hle).le⟩
    fun _ ↦ exists_conj_smul_le_unitarySubgroup

/-! ### Subgroups stable under the polar decomposition -/

section PolarStable

open scoped MatrixOrder

/-- **Maximal compactness in a polar-stable subgroup.** Let `G` be a subgroup of `GL ι 𝕜` that
contains the unitary polar factor of each of its elements. Then a compact subgroup of `G`
containing the unitary elements of `G` consists of unitary elements. -/
theorem eq_inf_unitarySubgroup_of_isCompact_of_le_of_polarUnitary_mem {G K : Subgroup (GL ι 𝕜)}
    (hG : ∀ g ∈ G, Unitary.toUnits (Units.polarUnitary g) ∈ G)
    (hK : IsCompact (K : Set (GL ι 𝕜))) (hKG : K ≤ G)
    (hUK : G ⊓ unitarySubgroup (GL ι 𝕜) ≤ K) :
    K = G ⊓ unitarySubgroup (GL ι 𝕜) :=
  le_antisymm (fun g hg ↦ ⟨hKG hg, mem_unitarySubgroup_of_isCompact_of_polarUnitary_mem hK hg
    (hUK ⟨hG g (hKG hg), by simp⟩)⟩) hUK

/-- **The unitary elements form a maximal compact subgroup of a closed polar-stable subgroup.**
Let `G` be a closed subgroup of `GL ι 𝕜` that contains the unitary polar factor of each of its
elements. Then its unitary elements form a maximal compact subgroup of `G`, with the inherited
topology. -/
theorem maximal_isCompact_unitarySubgroup_subgroupOf {G : Subgroup (GL ι 𝕜)}
    (hG : ∀ g ∈ G, Unitary.toUnits (Units.polarUnitary g) ∈ G)
    (hGc : IsClosed (G : Set (GL ι 𝕜))) :
    Maximal (fun K : Subgroup G ↦ IsCompact (K : Set G))
      ((unitarySubgroup (GL ι 𝕜)).subgroupOf G) := by
  have hcompact : IsCompact (((unitarySubgroup (GL ι 𝕜)).subgroupOf G) : Set G) := by
    have h : IsCompact
        (↑(((unitarySubgroup (GL ι 𝕜)).subgroupOf G).map G.subtype) : Set (GL ι 𝕜)) := by
      rw [Subgroup.subgroupOf_map_subtype, inf_comm, Subgroup.coe_inf]
      exact isCompact_unitarySubgroup.inter_left hGc
    rw [Subgroup.coe_map] at h
    exact Subtype.isCompact_iff.mpr h
  refine ⟨hcompact, fun K hK hUK ↦ ?_⟩
  have hmap : K.map G.subtype = G ⊓ unitarySubgroup (GL ι 𝕜) := by
    apply eq_inf_unitarySubgroup_of_isCompact_of_le_of_polarUnitary_mem hG
    · exact hK.image continuous_subtype_val
    · exact Subgroup.map_subtype_le K
    · simpa only [Subgroup.subgroupOf_map_subtype, inf_comm] using
        Subgroup.map_mono (f := G.subtype) hUK
  intro g hg
  have hgmem : (g : GL ι 𝕜) ∈ K.map G.subtype := ⟨g, hg, rfl⟩
  rw [hmap] at hgmem
  exact hgmem.2

end PolarStable

end Matrix.GeneralLinearGroup
