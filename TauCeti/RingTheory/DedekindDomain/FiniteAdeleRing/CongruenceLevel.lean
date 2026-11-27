/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.CongruenceSubgroup
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Topology
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.CongruenceLevel
public import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.CompletedIdeal
public import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.IntegralGL
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Map
import TauCeti.RingTheory.DedekindDomain.AdicValuation.ValuativeRel
import TauCeti.Topology.Instances.Matrix

/-!
# Congruence levels of `GL₂` over the integral finite adeles

For a Dedekind domain `R` with fraction field `K` (for instance the ring of integers of a number
field), write `Ô = ∏_v 𝒪_v` for the integral finite adeles and `NÔ` for the completion
`IsDedekindDomain.FiniteAdeleRing.completedIdeal K N` of an integral ideal `N`. This file defines
the three congruence levels of `GL₂(𝔸_f)`:

* the principal level `K(N)`, the image along `TauCeti.GeneralLinear.pointsContinuousMulEquiv`
  and the inclusion `Ô ⊆ 𝔸_f` of Tau Ceti's congruence subgroup of level `NÔ` of the `Ô`-points
  of `GL₂`, that is, `{g ∈ GL₂(Ô) : g ≡ 1 mod NÔ}`;
* `K₀(N) = {g ∈ GL₂(Ô) : c ∈ NÔ}` and `K₁(N) = {g ∈ GL₂(Ô) : c ∈ NÔ, d - 1 ∈ NÔ}`, where
  `g = [[a, b], [c, d]]`, the images of the levels `TauCeti.GL2K0 (NÔ)` and `TauCeti.GL2K1 (NÔ)`
  of `GL₂(Ô)`.

No generator of `N` is chosen, so nonprincipal ideals are allowed. Membership is expressed
entrywise: integral entries, integral inverse entries and the congruence conditions. The levels
satisfy `K(N) ≤ K₁(N) ≤ K₀(N)`, are monotone in `N`, and are open for `N ≠ ⊥` and compact when
the residue fields of `R` are finite.

## Main declarations

* `IsDedekindDomain.FiniteAdeleRing.principalLevel`, `level1`, `level0`: the levels `K(N)`,
  `K₁(N)` and `K₀(N)`, images of subgroups of `GL₂(Ô)` under the inclusion
  `IsDedekindDomain.FiniteAdeleRing.integralGL` of
  `TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.IntegralGL`, with entrywise membership
  criteria `mem_principalLevel_iff`, `mem_level1_iff` and `mem_level0_iff`, all instances of
  `mem_map_integralGL_iff`.
* `IsDedekindDomain.FiniteAdeleRing.principalLevel_le_level1`, `level1_le_level0` and the
  monotonicity lemmas `principalLevel_mono`, `level1_mono`, `level0_mono`.
* `IsDedekindDomain.FiniteAdeleRing.principalLevel_bot`: `K(0) = {1}`.
* `IsDedekindDomain.FiniteAdeleRing.map_algebraMap_mem_principalLevel`: the image of a matrix of
  `GL₂(R)` congruent to `1` modulo `N` lies in `K(N)`; for `N ≠ ⊥`,
  `map_algebraMap_mem_principalLevel_iff`, `map_algebraMap_mem_level1_iff` and
  `map_algebraMap_mem_level0_iff` give the congruence conditions on the entries for the three
  levels.
* `IsDedekindDomain.FiniteAdeleRing.upperRightHom_mem_level1`,
  `upperRightHom_mem_principalLevel_iff` and `upperRightHom_algebraMap_mem_principalLevel_iff`:
  the unipotent matrices `[[1, b], [0, 1]]` in `K₁(N)` and `K(N)`.
* `IsDedekindDomain.FiniteAdeleRing.isOpen_principalLevel`, `isCompact_principalLevel` and their
  analogues for `K₀(N)` and `K₁(N)`.

## References

* J. S. Milne, *Introduction to Shimura varieties*, §4, p. 42.
* A. Borel, *Automorphic L-functions*, Proc. Sympos. Pure Math. 33, Part 2 (1979), §1.7, p. 8.
-/

public section
noncomputable section

open Topology

namespace IsDedekindDomain.FiniteAdeleRing

open TauCeti TauCeti.GeneralLinear

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
variable (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]

/-! ### The levels -/

/-- The **principal congruence level** `K(N) ⊆ GL₂(𝔸_f)`: the image along
`TauCeti.GeneralLinear.pointsContinuousMulEquiv` and `Ô ⊆ 𝔸_f` of the congruence subgroup of
level `NÔ` of the `Ô`-points of `GL₂`, that is, `{g ∈ GL₂(Ô) : g - 1 ∈ M₂(NÔ)}`. -/
def principalLevel (N : Ideal R) : Subgroup (GL (Fin 2) 𝔸ᶠ[R, K]) :=
  (HopfAlgebra.congruenceSubgroup R (coordinateHopfAlgebra R 2) (completedIdeal K N)).map
    ((integralGL K (Fin 2)).comp
      (pointsContinuousMulEquiv (k := R) (R := integralAdeles R K) 2 :
        WithConv (coordinateHopfAlgebra R 2 →ₐ[R] integralAdeles R K) ≃*
          GL (Fin 2) (integralAdeles R K)).toMonoidHom)

/-- The **level `K₁(N)`** of `GL₂(𝔸_f)`: the matrices `[[a, b], [c, d]] ∈ GL₂(Ô)` with
`c ∈ NÔ` and `d - 1 ∈ NÔ`. -/
def level1 (N : Ideal R) : Subgroup (GL (Fin 2) 𝔸ᶠ[R, K]) :=
  (GL2K1 (completedIdeal K N)).map (integralGL K (Fin 2))

/-- The **level `K₀(N)`** of `GL₂(𝔸_f)`: the matrices `[[a, b], [c, d]] ∈ GL₂(Ô)` with
`c ∈ NÔ`. -/
def level0 (N : Ideal R) : Subgroup (GL (Fin 2) 𝔸ᶠ[R, K]) :=
  (GL2K0 (completedIdeal K N)).map (integralGL K (Fin 2))

/-- `K(N)` is the image of the kernel of reduction `GL₂(Ô) → GL₂(Ô ⧸ NÔ)`. -/
theorem principalLevel_eq_map_ker (N : Ideal R) :
    principalLevel K N =
      (Matrix.GeneralLinearGroup.map (n := Fin 2)
        (Ideal.Quotient.mk (completedIdeal K N))).ker.map (integralGL K (Fin 2)) := by
  rw [principalLevel, coe_pointsContinuousMulEquiv, ← Subgroup.map_map,
    ← map_congruenceSubgroup (R := R)]

/-- `K₁(N)` is the image of `K₁(NÔ) ≤ GL₂(Ô)`. -/
theorem level1_def (N : Ideal R) :
    level1 K N = (GL2K1 (completedIdeal K N)).map (integralGL K (Fin 2)) :=
  (rfl)

/-- `K₀(N)` is the image of `K₀(NÔ) ≤ GL₂(Ô)`. -/
theorem level0_def (N : Ideal R) :
    level0 K N = (GL2K0 (completedIdeal K N)).map (integralGL K (Fin 2)) :=
  (rfl)

variable {K}

/-- Entrywise membership in `K(N)`: integral entries, integral inverse entries, and every entry of
`g - 1` in `NÔ`. -/
theorem mem_principalLevel_iff {N : Ideal R} {g : GL (Fin 2) 𝔸ᶠ[R, K]} :
    g ∈ principalLevel K N ↔
      ∃ (hg : ∀ i j, (g : Matrix (Fin 2) (Fin 2) 𝔸ᶠ[R, K]) i j ∈ integralAdeles R K),
        (∀ i j, (↑g⁻¹ : Matrix (Fin 2) (Fin 2) 𝔸ᶠ[R, K]) i j ∈ integralAdeles R K) ∧
          ∀ i j, (⟨_, hg i j⟩ - (1 : Matrix (Fin 2) (Fin 2) (integralAdeles R K)) i j :
            integralAdeles R K) ∈ completedIdeal K N := by
  rw [principalLevel_eq_map_ker, mem_map_integralGL_iff (Fin 2)
    (P := fun M ↦ ∀ i j, M i j - (1 : Matrix (Fin 2) (Fin 2) _) i j ∈ completedIdeal K N)
    fun _ ↦ Matrix.GeneralLinearGroup.mem_ker_map_quotientMk_iff _]
  simp only [Matrix.of_apply]

/-- Entrywise membership in `K₁(N)`: integral entries, integral inverse entries, `c ∈ NÔ` and
`d - 1 ∈ NÔ`. -/
theorem mem_level1_iff {N : Ideal R} {g : GL (Fin 2) 𝔸ᶠ[R, K]} :
    g ∈ level1 K N ↔
      ∃ (hg : ∀ i j, (g : Matrix (Fin 2) (Fin 2) 𝔸ᶠ[R, K]) i j ∈ integralAdeles R K),
        (∀ i j, (↑g⁻¹ : Matrix (Fin 2) (Fin 2) 𝔸ᶠ[R, K]) i j ∈ integralAdeles R K) ∧
          (⟨_, hg 1 0⟩ : integralAdeles R K) ∈ completedIdeal K N ∧
            (⟨_, hg 1 1⟩ - 1 : integralAdeles R K) ∈ completedIdeal K N := by
  rw [level1_def, mem_map_integralGL_iff (Fin 2)
    (P := fun M ↦ M 1 0 ∈ completedIdeal K N ∧ M 1 1 - 1 ∈ completedIdeal K N)
    fun _ ↦ GL2K1.mem_iff]
  simp only [Matrix.of_apply]

/-- Entrywise membership in `K₀(N)`: integral entries, integral inverse entries and `c ∈ NÔ`. -/
theorem mem_level0_iff {N : Ideal R} {g : GL (Fin 2) 𝔸ᶠ[R, K]} :
    g ∈ level0 K N ↔
      ∃ (hg : ∀ i j, (g : Matrix (Fin 2) (Fin 2) 𝔸ᶠ[R, K]) i j ∈ integralAdeles R K),
        (∀ i j, (↑g⁻¹ : Matrix (Fin 2) (Fin 2) 𝔸ᶠ[R, K]) i j ∈ integralAdeles R K) ∧
          (⟨_, hg 1 0⟩ : integralAdeles R K) ∈ completedIdeal K N := by
  rw [level0_def, mem_map_integralGL_iff (Fin 2) (P := fun M ↦ M 1 0 ∈ completedIdeal K N)
    fun _ ↦ GL2K0.mem_iff]
  simp only [Matrix.of_apply]

/-- The entries of the diagonal image in `GL₂(𝔸_f)` of a matrix of `GL₂(R)` are integral. -/
private theorem map_algebraMap_apply_mem_integralAdeles (g : GL (Fin 2) R) (i j : Fin 2) :
    (Matrix.GeneralLinearGroup.map (algebraMap R 𝔸ᶠ[R, K]) g : Matrix (Fin 2) (Fin 2) 𝔸ᶠ[R, K])
      i j ∈ integralAdeles R K := by
  rw [Matrix.GeneralLinearGroup.map_apply]
  exact (integralAdeles R K).algebraMap_mem _

/-- The entries of the inverse of the diagonal image in `GL₂(𝔸_f)` of a matrix of `GL₂(R)` are
integral. -/
private theorem map_algebraMap_inv_apply_mem_integralAdeles (g : GL (Fin 2) R) (i j : Fin 2) :
    (↑(Matrix.GeneralLinearGroup.map (algebraMap R 𝔸ᶠ[R, K]) g)⁻¹ :
      Matrix (Fin 2) (Fin 2) 𝔸ᶠ[R, K]) i j ∈ integralAdeles R K := by
  rw [← map_inv]
  exact map_algebraMap_apply_mem_integralAdeles (K := K) g⁻¹ i j

/-- The diagonal image in `GL₂(𝔸_f)` of a matrix of `GL₂(R)` congruent to `1` modulo `N` lies in
the principal level `K(N)`. -/
theorem map_algebraMap_mem_principalLevel {N : Ideal R} {g : GL (Fin 2) R}
    (hg : ∀ i j, (g : Matrix (Fin 2) (Fin 2) R) i j - (1 : Matrix (Fin 2) (Fin 2) R) i j ∈ N) :
    Matrix.GeneralLinearGroup.map (algebraMap R 𝔸ᶠ[R, K]) g ∈ principalLevel K N := by
  rw [mem_principalLevel_iff]
  refine ⟨map_algebraMap_apply_mem_integralAdeles g, map_algebraMap_inv_apply_mem_integralAdeles g,
    fun i j ↦ ?_⟩
  convert algebraMap_mem_completedIdeal (K := K) (hg i j) using 1
  ext
  simp [Matrix.one_apply, apply_ite]

/-- An entry of the diagonal image of a matrix of `GL₂(R)`, read in `Ô`, is the image of the
entry. -/
private theorem mk_map_algebraMap_apply (g : GL (Fin 2) R) (i j : Fin 2) :
    (⟨_, map_algebraMap_apply_mem_integralAdeles (K := K) g i j⟩ : integralAdeles R K) =
      algebraMap R (integralAdeles R K) ((g : Matrix (Fin 2) (Fin 2) R) i j) :=
  Subtype.ext (by simp [Matrix.GeneralLinearGroup.map_apply])

/-- For `N ≠ ⊥`, the diagonal image in `GL₂(𝔸_f)` of a matrix of `GL₂(R)` lies in the principal
level `K(N)` exactly when the matrix is congruent to `1` modulo `N`. -/
theorem map_algebraMap_mem_principalLevel_iff {N : Ideal R} (hN : N ≠ ⊥) {g : GL (Fin 2) R} :
    Matrix.GeneralLinearGroup.map (algebraMap R 𝔸ᶠ[R, K]) g ∈ principalLevel K N ↔
      ∀ i j, (g : Matrix (Fin 2) (Fin 2) R) i j - (1 : Matrix (Fin 2) (Fin 2) R) i j ∈ N := by
  refine ⟨fun hg i j ↦ ?_, map_algebraMap_mem_principalLevel⟩
  obtain ⟨_, _, h⟩ := mem_principalLevel_iff.mp hg
  rw [← algebraMap_mem_completedIdeal_iff (K := K) hN, map_sub]
  convert h i j using 2
  · exact (mk_map_algebraMap_apply (K := K) g i j).symm
  · rw [← Matrix.map_one (algebraMap R (integralAdeles R K)) (map_zero _) (map_one _),
      Matrix.map_apply]

/-- For `N ≠ ⊥`, the diagonal image in `GL₂(𝔸_f)` of `[[a, b], [c, d]] ∈ GL₂(R)` lies in `K₁(N)`
exactly when `c ∈ N` and `d - 1 ∈ N`. -/
theorem map_algebraMap_mem_level1_iff {N : Ideal R} (hN : N ≠ ⊥) {g : GL (Fin 2) R} :
    Matrix.GeneralLinearGroup.map (algebraMap R 𝔸ᶠ[R, K]) g ∈ level1 K N ↔
      (g : Matrix (Fin 2) (Fin 2) R) 1 0 ∈ N ∧ (g : Matrix (Fin 2) (Fin 2) R) 1 1 - 1 ∈ N := by
  rw [mem_level1_iff, ← algebraMap_mem_completedIdeal_iff (K := K) hN,
    ← algebraMap_mem_completedIdeal_iff (K := K) hN, map_sub, map_one]
  refine ⟨fun ⟨_, _, h₀, h₁⟩ ↦ ⟨h₀, h₁⟩, fun ⟨h₀, h₁⟩ ↦
    ⟨map_algebraMap_apply_mem_integralAdeles (K := K) g,
      map_algebraMap_inv_apply_mem_integralAdeles (K := K) g, ?_, ?_⟩⟩
  · rwa [mk_map_algebraMap_apply]
  · rwa [mk_map_algebraMap_apply]

/-- For `N ≠ ⊥`, the diagonal image in `GL₂(𝔸_f)` of `[[a, b], [c, d]] ∈ GL₂(R)` lies in `K₀(N)`
exactly when `c ∈ N`. -/
theorem map_algebraMap_mem_level0_iff {N : Ideal R} (hN : N ≠ ⊥) {g : GL (Fin 2) R} :
    Matrix.GeneralLinearGroup.map (algebraMap R 𝔸ᶠ[R, K]) g ∈ level0 K N ↔
      (g : Matrix (Fin 2) (Fin 2) R) 1 0 ∈ N := by
  rw [mem_level0_iff, ← algebraMap_mem_completedIdeal_iff (K := K) hN]
  refine ⟨fun ⟨_, _, h⟩ ↦ h, fun h ↦ ⟨map_algebraMap_apply_mem_integralAdeles (K := K) g,
    map_algebraMap_inv_apply_mem_integralAdeles (K := K) g, ?_⟩⟩
  rwa [mk_map_algebraMap_apply]

variable (K)

/-- `K(N) ≤ K₁(N)`. -/
theorem principalLevel_le_level1 (N : Ideal R) : principalLevel K N ≤ level1 K N := by
  rw [principalLevel_eq_map_ker, level1]
  exact Subgroup.map_mono (GL2K1.ker_map_le _)

/-- `K₁(N) ≤ K₀(N)`. -/
theorem level1_le_level0 (N : Ideal R) : level1 K N ≤ level0 K N :=
  Subgroup.map_mono (GL2K1.le_GL2K0 _)

/-- `K(M) ≤ K(N)` whenever `M ⊆ N`. -/
theorem principalLevel_mono : Monotone (principalLevel K (R := R)) :=
  fun _ _ h ↦ Subgroup.map_mono (HopfAlgebra.congruenceSubgroup_mono R (coordinateHopfAlgebra R 2)
    (integralAdeles R K) (completedIdeal_mono K h))

/-- `K₁(M) ≤ K₁(N)` whenever `M ⊆ N`. -/
theorem level1_mono : Monotone (level1 K (R := R)) :=
  fun _ _ h ↦ Subgroup.map_mono (GL2K1_mono (completedIdeal_mono K h))

/-- `K₀(M) ≤ K₀(N)` whenever `M ⊆ N`. -/
theorem level0_mono : Monotone (level0 K (R := R)) :=
  fun _ _ h ↦ Subgroup.map_mono (GL2K0_mono (completedIdeal_mono K h))

/-- For `N = R`, `K₀(N)` is `GL₂(Ô)`. -/
@[simp]
theorem level0_top : level0 K (⊤ : Ideal R) = (integralGL K (Fin 2)).range := by
  rw [level0, completedIdeal_top, GL2K0_top, ← MonoidHom.range_eq_map]

/-- For `N = R`, `K₁(N)` is `GL₂(Ô)`. -/
@[simp]
theorem level1_top : level1 K (⊤ : Ideal R) = (integralGL K (Fin 2)).range := by
  rw [level1, completedIdeal_top, GL2K1_top, ← MonoidHom.range_eq_map]

/-- For `N = R`, `K(N)` is `GL₂(Ô)`. -/
@[simp]
theorem principalLevel_top : principalLevel K (⊤ : Ideal R) = (integralGL K (Fin 2)).range :=
  le_antisymm (principalLevel_le_level1 K ⊤ |>.trans (level1_le_level0 K ⊤) |>.trans
    (level0_top K).le) (by
      rw [principalLevel_eq_map_ker, MonoidHom.range_eq_map]
      refine Subgroup.map_mono fun g _ ↦ ?_
      rw [Matrix.GeneralLinearGroup.mem_ker_map_quotientMk_iff, completedIdeal_top]
      exact fun _ _ ↦ Submodule.mem_top)

/-- At the zero ideal the principal level is trivial: `K(0) = {1}`. -/
@[simp]
theorem principalLevel_bot : principalLevel K (⊥ : Ideal R) = ⊥ := by
  rw [principalLevel_eq_map_ker, (MonoidHom.ker_eq_bot_iff _).mpr
    (Matrix.GeneralLinearGroup.map_injective ((RingHom.injective_iff_ker_eq_bot _).mpr
      (Ideal.mk_ker.trans (completedIdeal_bot K)))), Subgroup.map_bot]

variable {K}

open Matrix.GeneralLinearGroup in
/-- The unipotent matrix `[[1, b], [0, 1]]` lies in `K₁(N)` for every integral `b` and every
ideal `N`. -/
theorem upperRightHom_mem_level1 {b : 𝔸ᶠ[R, K]} (hb : b ∈ integralAdeles R K) (N : Ideal R) :
    upperRightHom b ∈ level1 K N := by
  rw [← integralGL_upperRightHom ⟨b, hb⟩]
  exact Subgroup.mem_map_of_mem _ (GL2K1.mem_iff.mpr (by simp))

open Matrix.GeneralLinearGroup in
/-- For integral `b`, the unipotent matrix `[[1, b], [0, 1]]` lies in `K(N)` exactly when
`b ∈ NÔ`. -/
theorem upperRightHom_mem_principalLevel_iff {b : 𝔸ᶠ[R, K]} (hb : b ∈ integralAdeles R K)
    {N : Ideal R} :
    upperRightHom b ∈ principalLevel K N ↔ (⟨b, hb⟩ : integralAdeles R K) ∈ completedIdeal K N := by
  rw [principalLevel_eq_map_ker, ← integralGL_upperRightHom ⟨b, hb⟩,
    Subgroup.mem_map_iff_mem (integralGL_injective K (Fin 2)), mem_ker_map_quotientMk_iff]
  refine ⟨fun h ↦ by simpa using h 0 1, fun h i j ↦ ?_⟩
  fin_cases i <;> fin_cases j <;> simp [h]

open Matrix.GeneralLinearGroup in
/-- For a nonzero ideal `N` and `r ∈ R`, the unipotent matrix `[[1, r], [0, 1]]` lies in `K(N)`
exactly when `r ∈ N`. -/
theorem upperRightHom_algebraMap_mem_principalLevel_iff {N : Ideal R} (hN₀ : N ≠ ⊥) {r : R} :
    upperRightHom (algebraMap R 𝔸ᶠ[R, K] r) ∈ principalLevel K N ↔ r ∈ N := by
  rw [upperRightHom_mem_principalLevel_iff ((integralAdeles R K).algebraMap_mem r)]
  exact algebraMap_mem_completedIdeal_iff hN₀

variable (K)

/-! ### Topology -/

/-- For `N ≠ ⊥`, `K(N)` is open in `GL₂(𝔸_f)`: it is the image under the open embedding
`integralGL` of the kernel of reduction modulo the open ideal `NÔ`. -/
theorem isOpen_principalLevel {N : Ideal R} (hN : N ≠ ⊥) :
    IsOpen (principalLevel K N : Set (GL (Fin 2) 𝔸ᶠ[R, K])) := by
  rw [principalLevel_eq_map_ker, Subgroup.coe_map]
  exact (isOpenEmbedding_integralGL K (Fin 2)).isOpenMap _
    (isOpen_ker_map_quotientMk 2 (isOpen_completedIdeal K hN))

/-- For `N ≠ ⊥`, `K₁(N)` is open in `GL₂(𝔸_f)`. -/
theorem isOpen_level1 {N : Ideal R} (hN : N ≠ ⊥) :
    IsOpen (level1 K N : Set (GL (Fin 2) 𝔸ᶠ[R, K])) :=
  Subgroup.isOpen_mono (principalLevel_le_level1 K N) (isOpen_principalLevel K hN)

/-- For `N ≠ ⊥`, `K₀(N)` is open in `GL₂(𝔸_f)`. -/
theorem isOpen_level0 {N : Ideal R} (hN : N ≠ ⊥) :
    IsOpen (level0 K N : Set (GL (Fin 2) 𝔸ᶠ[R, K])) :=
  Subgroup.isOpen_mono (level1_le_level0 K N) (isOpen_level1 K hN)

variable [∀ v : HeightOneSpectrum R, Finite (R ⧸ v.asIdeal)]

/-- With finite residue fields and `N ≠ ⊥`, `K(N)` is compact: the kernel of reduction modulo the
open ideal `NÔ` is an open, hence closed, subgroup of the compact group `GL₂(Ô)`. -/
theorem isCompact_principalLevel {N : Ideal R} (hN : N ≠ ⊥) :
    IsCompact (principalLevel K N : Set (GL (Fin 2) 𝔸ᶠ[R, K])) := by
  rw [principalLevel_eq_map_ker, Subgroup.coe_map]
  exact (Subgroup.isClosed_of_isOpen _ (isOpen_ker_map_quotientMk 2
    (isOpen_completedIdeal K hN))).isCompact.image (continuous_integralGL K (Fin 2))

/-- With finite residue fields and `N ≠ ⊥`, `K₁(N)` is compact. -/
theorem isCompact_level1 {N : Ideal R} (hN : N ≠ ⊥) :
    IsCompact (level1 K N : Set (GL (Fin 2) 𝔸ᶠ[R, K])) := by
  rw [level1, Subgroup.coe_map]
  exact (Subgroup.isClosed_of_isOpen _ (Subgroup.isOpen_mono (GL2K1.ker_map_le _)
    (isOpen_ker_map_quotientMk 2 (isOpen_completedIdeal K hN)))).isCompact.image
      (continuous_integralGL K (Fin 2))

/-- With finite residue fields and `N ≠ ⊥`, `K₀(N)` is compact. -/
theorem isCompact_level0 {N : Ideal R} (hN : N ≠ ⊥) :
    IsCompact (level0 K N : Set (GL (Fin 2) 𝔸ᶠ[R, K])) := by
  rw [level0, Subgroup.coe_map]
  exact (Subgroup.isClosed_of_isOpen _ (Subgroup.isOpen_mono
    ((GL2K1.ker_map_le _).trans (GL2K1.le_GL2K0 _))
    (isOpen_ker_map_quotientMk 2 (isOpen_completedIdeal K hN)))).isCompact.image
      (continuous_integralGL K (Fin 2))

end IsDedekindDomain.FiniteAdeleRing
