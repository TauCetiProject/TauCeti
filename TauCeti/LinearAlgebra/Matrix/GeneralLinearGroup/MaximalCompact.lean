/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Topology.Algebra.Group.Units
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Diagonal.Basic
public import TauCeti.RepresentationTheory.Compact.UnitaryModel
public import TauCeti.Topology.Algebra.UnitaryGroup

/-!
# The maximal compact subgroups of the real and complex general linear groups

For `𝕜 = ℝ` or `ℂ` and a finite index type `ι`, the unitary subgroup `U = unitarySubgroup (GL ι 𝕜)`
(the orthogonal group `O(n)` over `ℝ`, the unitary group `U(n)` over `ℂ`) is a compact subgroup of
`GL ι 𝕜`, and it is the largest compact subgroup up to conjugacy:

* **maximality**: a compact subgroup of `GL ι 𝕜` containing `U` is `U`;
* **conjugacy**: every compact subgroup of `GL ι 𝕜` is conjugate into `U`.

Together these say that the maximal compact subgroups of `GL ι 𝕜` are exactly the conjugates of `U`.
This is the matrix-group instance of two structural facts about a reductive group and its maximal
compact subgroup: `U(n)` is a maximal compact subgroup of its complexification `GLₙ(ℂ)`, and
`O(n)` is the maximal compact subgroup `K` of `GLₙ(ℝ)` occurring in the Cartan, Iwasawa and `KAK`
decompositions.

The two proofs are the classical ones.

For maximality, take `g` in a compact subgroup `K ⊇ U`. Diagonalize the positive-definite matrix
`gᴴ g = V D Vᴴ` by a unitary `V`, with `D` the diagonal of eigenvalues. With `S = √D`, the matrix
`W = g V S⁻¹` is unitary, so `S = W⁻¹ g V` lies in `K`. All integer powers of the positive diagonal
matrix `S` then lie in the compact set `K`, so their diagonal entries are bounded; this forces
`S = 1`, hence `gᴴ g = 1` and `g` is unitary.

For conjugacy, Weyl's unitarian trick (`ContRepresentation.exists_isUnitary_congr`) applies to the
tautological representation of the compact group `K` on `EuclideanSpace 𝕜 ι`: averaging the inner
product over Haar measure of `K` and changing coordinates by the automorphism standardizing the
averaged form makes every element of `K` an isometry. The matrix of that automorphism conjugates
`K` into `U`.

## Main results

* `Matrix.mem_unitaryGroup_iff_inner_toEuclideanCLM`: a matrix is unitary exactly when its
  Euclidean operator preserves the inner product.
* `Matrix.GeneralLinearGroup.isCompact_unitarySubgroup`: the unitary subgroup is compact.
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

namespace Matrix

/-- A square matrix is unitary exactly when its Euclidean operator preserves the inner product. -/
theorem mem_unitaryGroup_iff_inner_toEuclideanCLM {M : Matrix ι ι 𝕜} :
    M ∈ unitaryGroup ι 𝕜 ↔ ∀ x y : EuclideanSpace 𝕜 ι,
      ⟪toEuclideanCLM (n := ι) (𝕜 := 𝕜) M x, toEuclideanCLM (n := ι) (𝕜 := 𝕜) M y⟫_𝕜 =
        ⟪x, y⟫_𝕜 := by
  refine ⟨fun hM ↦ ContinuousLinearMap.inner_map_map_of_mem_unitary
    (Unitary.map_mem (toEuclideanCLM (n := ι) (𝕜 := 𝕜)) hM), fun h ↦ ?_⟩
  rw [mem_unitaryGroup_iff']
  refine EquivLike.injective (toEuclideanCLM (n := ι) (𝕜 := 𝕜)) ?_
  rw [map_mul, map_star, map_one, ContinuousLinearMap.star_eq_adjoint]
  exact (ContinuousLinearMap.inner_map_map_iff_adjoint_comp_self _).mp h

end Matrix

namespace Matrix.GeneralLinearGroup

/-- An invertible matrix lies in the unitary subgroup of `GL ι 𝕜` exactly when the matrix itself is
unitary. -/
theorem mem_unitarySubgroup_iff_coe_mem_unitaryGroup {g : GL ι 𝕜} :
    g ∈ unitarySubgroup (GL ι 𝕜) ↔ (g : Matrix ι ι 𝕜) ∈ unitaryGroup ι 𝕜 := by
  rw [mem_unitarySubgroup_iff, Units.unitary_eq]
  rfl

/-- **The unitary subgroup of `GL ι 𝕜` is compact.** It is the image of the compact matrix unitary
group under the continuous map sending a unitary matrix to the unit it defines. -/
theorem isCompact_unitarySubgroup :
    IsCompact ((unitarySubgroup (GL ι 𝕜) : Subgroup (GL ι 𝕜)) : Set (GL ι 𝕜)) := by
  have hrange : ((unitarySubgroup (GL ι 𝕜) : Subgroup (GL ι 𝕜)) : Set (GL ι 𝕜)) =
      Set.range fun U : unitaryGroup ι 𝕜 ↦ Unitary.toUnits U := by
    ext g
    refine ⟨fun hg ↦ ⟨⟨g, mem_unitarySubgroup_iff_coe_mem_unitaryGroup.mp hg⟩, Units.ext rfl⟩, ?_⟩
    rintro ⟨U, rfl⟩
    exact mem_unitarySubgroup_iff_coe_mem_unitaryGroup.mpr U.property
  rw [hrange]
  exact isCompact_range <| Units.continuous_iff.mpr
    ⟨continuous_subtype_val, continuous_subtype_val.star⟩

/-- A positive diagonal matrix in a compact subgroup of `GL ι 𝕜` is the identity: its integer
powers are again in the subgroup, so their diagonal entries are bounded. -/
private theorem eq_one_of_diagGL_mem {K : Subgroup (GL ι 𝕜)} (hK : IsCompact (K : Set (GL ι 𝕜)))
    {s : ι → ℝ} (hs : ∀ i, 0 < s i)
    (hmem : TauCeti.diagGL (fun i ↦ Units.mk0 (s i : 𝕜) (by simpa using (hs i).ne')) ∈ K)
    (i : ι) : s i = 1 := by
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn
    (f := fun g : GL ι 𝕜 ↦ (g : Matrix ι ι 𝕜) i i)
    ((continuous_apply_apply i i).comp (Units.continuous_val (M := Matrix ι ι 𝕜))).continuousOn
  have hbound (k : ℤ) : s i ^ k ≤ C := by
    simpa only [← map_zpow, TauCeti.diagGL_apply, ↓reduceIte, Pi.pow_apply,
      Units.val_zpow_eq_zpow_val, Units.val_mk0, norm_zpow, RCLike.norm_ofReal,
      abs_of_pos (hs i)] using hC _ (zpow_mem hmem k)
  -- A positive real number other than `1` has integer powers tending to infinity.
  rcases lt_trichotomy (s i) 1 with hlt | heq | hgt
  · obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt C (one_lt_inv₀ (hs i) |>.mpr hlt)
    have := hbound (-(n : ℤ))
    rw [_root_.zpow_neg, zpow_natCast, ← _root_.inv_pow] at this
    linarith
  · exact heq
  · obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt C hgt
    have := hbound n
    rw [zpow_natCast] at this
    linarith

/-- **The unitary subgroup is a maximal compact subgroup of `GL ι 𝕜`**, in the elementwise form:
an element of a compact subgroup containing every unitary matrix is unitary. -/
theorem mem_unitarySubgroup_of_isCompact_of_le {K : Subgroup (GL ι 𝕜)}
    (hK : IsCompact (K : Set (GL ι 𝕜))) (hUK : unitarySubgroup (GL ι 𝕜) ≤ K) {g : GL ι 𝕜}
    (hg : g ∈ K) : g ∈ unitarySubgroup (GL ι 𝕜) := by
  -- Diagonalize the positive-definite matrix `gᴴ g = V D Vᴴ`.
  obtain ⟨A, hAdef⟩ : ∃ A, A = (g : Matrix ι ι 𝕜)ᴴ * g := ⟨_, rfl⟩
  have hpos : A.PosDef :=
    hAdef ▸ PosDef.conjTranspose_mul_self _ (mulVec_injective_iff_isUnit.mpr g.isUnit)
  have hA : A.IsHermitian := hpos.1
  set V := hA.eigenvectorUnitary
  set s : ι → ℝ := fun i ↦ √(hA.eigenvalues i) with hsdef
  have hs (i : ι) : 0 < s i := Real.sqrt_pos.mpr (PosDef.eigenvalues_pos hpos i)
  set S : GL ι 𝕜 := TauCeti.diagGL fun i ↦ Units.mk0 (s i : 𝕜) (by simpa using (hs i).ne')
  have hVU : Unitary.toUnits V ∈ unitarySubgroup (GL ι 𝕜) :=
    mem_unitarySubgroup_iff_coe_mem_unitaryGroup.mpr V.property
  -- The matrix `W = g V S⁻¹` is unitary.
  have hW : g * Unitary.toUnits V * S⁻¹ ∈ unitarySubgroup (GL ι 𝕜) := by
    rw [mem_unitarySubgroup_iff_coe_mem_unitaryGroup, mem_unitaryGroup_iff']
    have hSinv : ((S⁻¹ : GL ι 𝕜) : Matrix ι ι 𝕜) = diagonal fun i ↦ ((s i)⁻¹ : 𝕜) := by
      rw [← map_inv, TauCeti.diagGL_coe]
      simp
    have hD : star (V : Matrix ι ι 𝕜) * A * (V : Matrix ι ι 𝕜) =
        diagonal (RCLike.ofReal ∘ hA.eigenvalues) := by
      simpa [Unitary.conjStarAlgAut_apply] using hA.conjStarAlgAut_star_eigenvectorUnitary
    have hsq (i : ι) : (s i : 𝕜)⁻¹ * (hA.eigenvalues i : 𝕜) * (s i : 𝕜)⁻¹ = 1 := by
      have hsi : (s i : 𝕜) ≠ 0 := by simpa using (hs i).ne'
      rw [← Real.sq_sqrt (PosDef.eigenvalues_pos hpos i).le]
      field_simp
      simp [hsdef]
    simp only [Units.val_mul, Unitary.val_toUnits_apply, hSinv, star_mul, star_eq_conjTranspose,
      diagonal_conjTranspose]
    calc _ = diagonal (fun i ↦ ((s i)⁻¹ : 𝕜)) *
          (star (V : Matrix ι ι 𝕜) * A * (V : Matrix ι ι 𝕜)) *
          diagonal (fun i ↦ ((s i)⁻¹ : 𝕜)) := by
            simp only [hAdef, star_eq_conjTranspose, Pi.star_def, star_inv₀, RCLike.star_def,
              RCLike.conj_ofReal, Matrix.mul_assoc]
      _ = 1 := by
        rw [hD, diagonal_mul_diagonal, diagonal_mul_diagonal, ← diagonal_one]
        exact congrArg diagonal (funext fun i ↦ by simpa using hsq i)
  -- Hence `S = W⁻¹ g V` lies in `K`, which forces `S = 1`.
  have hSK : S ∈ K := by
    have : S = (g * Unitary.toUnits V * S⁻¹)⁻¹ * g * Unitary.toUnits V := by group
    rw [this]
    exact mul_mem (mul_mem (inv_mem (hUK hW)) hg) (hUK hVU)
  have hs1 : ∀ i, hA.eigenvalues i = 1 := fun i ↦ by
    have := eq_one_of_diagGL_mem hK hs hSK i
    rwa [hsdef, Real.sqrt_eq_one] at this
  -- So `gᴴ g = V Vᴴ = 1`.
  rw [mem_unitarySubgroup_iff_coe_mem_unitaryGroup, mem_unitaryGroup_iff', star_eq_conjTranspose,
    ← hAdef, hA.spectral_theorem]
  simp [hs1, Function.comp_def]

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
  -- The matrices of `e` and `e⁻¹` are mutually inverse.
  let B := (toEuclideanCLM (n := ι) (𝕜 := 𝕜)).symm (e : EuclideanSpace 𝕜 ι →L[𝕜] _)
  let B' := (toEuclideanCLM (n := ι) (𝕜 := 𝕜)).symm (e.symm : EuclideanSpace 𝕜 ι →L[𝕜] _)
  have hB : B * B' = 1 := EquivLike.injective (toEuclideanCLM (n := ι) (𝕜 := 𝕜)) <| by
    simp only [B, B', map_mul, StarAlgEquiv.apply_symm_apply, map_one]
    ext1 x
    simp
  have hB' : B' * B = 1 := EquivLike.injective (toEuclideanCLM (n := ι) (𝕜 := 𝕜)) <| by
    simp only [B, B', map_mul, StarAlgEquiv.apply_symm_apply, map_one]
    ext1 x
    simp
  refine ⟨⟨B, B', hB, hB'⟩, fun _ hx ↦ ?_⟩
  obtain ⟨k, hk, rfl⟩ := (Subgroup.mem_smul_pointwise_iff_exists _ _ _).mp hx
  rw [mem_unitarySubgroup_iff_coe_mem_unitaryGroup]
  refine mem_unitaryGroup_iff_inner_toEuclideanCLM.mpr fun x y ↦ ?_
  -- The Euclidean operator of `B k B⁻¹` is the transported action `e ∘ k ∘ e⁻¹`.
  have hop (z : EuclideanSpace 𝕜 ι) :
      toEuclideanCLM (n := ι) (𝕜 := 𝕜) (((MulAut.conj (⟨B, B', hB, hB'⟩ : GL ι 𝕜)) • k :
        GL ι 𝕜) : Matrix ι ι 𝕜) z =
        ContinuousLinearEquiv.congr e (tautologicalRep K) ⟨k, hk⟩ z := by
    simp [tautologicalRep_apply, MulAut.smul_def, B, B']
  rw [hop, hop]
  exact he.inner_map_map _ x y

/-- **The maximal compact subgroups of `GL ι 𝕜` are the conjugates of the unitary subgroup.** Over
`ℝ` these are the conjugates of the orthogonal group `O(n)`, and over `ℂ` of the unitary group
`U(n)`. -/
theorem maximal_isCompact_iff {K : Subgroup (GL ι 𝕜)} :
    Maximal (fun H : Subgroup (GL ι 𝕜) ↦ IsCompact (H : Set (GL ι 𝕜))) K ↔
      ∃ g : GL ι 𝕜, K = MulAut.conj g • unitarySubgroup (GL ι 𝕜) := by
  -- Conjugation is a homeomorphism of `GL ι 𝕜`, so conjugate subgroups of compact ones are compact.
  have hconj (g : GL ι 𝕜) {H : Subgroup (GL ι 𝕜)} (hH : IsCompact (H : Set (GL ι 𝕜))) :
      IsCompact ((MulAut.conj g • H : Subgroup (GL ι 𝕜)) : Set (GL ι 𝕜)) := by
    rw [Subgroup.coe_pointwise_smul, ← Set.image_smul]
    exact hH.image (by simp only [MulAut.smul_def, MulAut.conj_apply]; fun_prop)
  constructor
  · intro hK
    obtain ⟨g, hg⟩ := exists_conj_smul_le_unitarySubgroup hK.1
    have hle : K ≤ MulAut.conj g⁻¹ • unitarySubgroup (GL ι 𝕜) := by
      rwa [map_inv, ← Subgroup.pointwise_smul_subset_iff]
    exact ⟨g⁻¹, le_antisymm hle (hK.2 (hconj _ isCompact_unitarySubgroup) hle)⟩
  · rintro ⟨g, rfl⟩
    refine ⟨hconj g isCompact_unitarySubgroup, fun L hL hle ↦ ?_⟩
    rw [Subgroup.pointwise_smul_subset_iff] at hle
    rw [← map_inv] at hle
    rw [← eq_unitarySubgroup_of_isCompact_of_le (hconj _ hL) hle, map_inv, smul_inv_smul]

end Matrix.GeneralLinearGroup
