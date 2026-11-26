/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Elementary
import Mathlib.LinearAlgebra.Matrix.Unique
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Stability.Surjective

/-!
# Gauss–Jordan factorization and normality of the elementary subgroup over a division ring

Over a division ring `D`, Gaussian elimination (obtained via Bass's surjective stability at stable
range `1`) reduces every invertible matrix to a diagonal matrix supported at a single chosen
coordinate: for any `i : n` and `g ∈ GL n D`, there exist an elementary matrix
`e ∈ TauCeti.elementarySubgroup n D` and a unit `u : Dˣ` such that
`g = e * diagGL (Pi.mulSingle i u)` (`TauCeti.exists_mem_elementarySubgroup_mul_diagGL_mulSingle`).
Consequently every invertible matrix factors as an elementary matrix times an invertible diagonal
matrix (`TauCeti.exists_mem_elementarySubgroup_mul_diagGL`), and two monoid homomorphisms out of
`GL n D` that vanish on `TauCeti.elementarySubgroup n D` agree as soon as they agree on the
single-entry diagonal matrices at one coordinate
(`Matrix.GeneralLinearGroup.hom_ext_of_elementarySubgroup_le_ker`).

Since `TauCeti.elementarySubgroup n D` is normal by
`TauCeti.elementarySubgroup_normal_of_hasStableRangeLE` for `2 ≤ Fintype.card n` and trivial for
`Fintype.card n ≤ 1`, it is normal in `GL n D` at every finite matrix size
(`TauCeti.elementarySubgroup_normal`), without stabilization.

## Main results

* `TauCeti.exists_mem_elementarySubgroup_mul_diagGL_mulSingle`: Gauss–Jordan factorization
  `g = e * diagGL (Pi.mulSingle i u)` in `GL n D`.
* `TauCeti.exists_mem_elementarySubgroup_mul_diagGL`: factorization `g = e * diagGL d` in `GL n D`.
* `TauCeti.elementarySubgroup_normal`: `TauCeti.elementarySubgroup n D` is normal in `GL n D`.
* `Matrix.GeneralLinearGroup.hom_ext_of_elementarySubgroup_le_ker`: homomorphisms out of `GL n D`
  vanishing on `TauCeti.elementarySubgroup n D` are determined by single-entry diagonal matrices at
  one coordinate.

## References

* J. Dieudonné, *Les déterminants sur un corps non commutatif*, Bull. Soc. Math. France **71**
  (1943), 27–45.
* E. Artin, *Geometric Algebra*, Interscience (1957), Chapter IV, §1–§2.
-/

public section

noncomputable section

open Matrix

namespace TauCeti

variable {D : Type*} [DivisionRing D]

/-- **Gauss–Jordan factorization over a division ring.** Given any coordinate `i : n`, every
invertible matrix `g ∈ GL n D` factors as an elementary matrix times a diagonal matrix whose only
possibly non-identity diagonal entry sits at `i`. -/
theorem exists_mem_elementarySubgroup_mul_diagGL_mulSingle {n : Type*} [Fintype n] [DecidableEq n]
    (i : n) (g : GL n D) :
    ∃ e ∈ elementarySubgroup n D, ∃ u : Dˣ, g = e * diagGL (Pi.mulSingle i u) := by
  let φ : Unit ⊕ {x : n // x ≠ i} ≃ n :=
    (Equiv.sumComm Unit {x : n // x ≠ i}).trans (Equiv.subtypeNeSumPUnit.{0} i)
  obtain ⟨h, e, he, hge⟩ :=
    surjective_stability 1 (hasStableRangeLE_one_of_isLocalRing D) Unit {x : n // x ≠ i}
      le_rfl (φ.symm.reindexGL D g)⁻¹
  have hg_inv : (φ.symm.reindexGL D g)⁻¹ = fromBlocksGL (h, (1 : GL {x : n // x ≠ i} D)) * e :=
    Units.ext (by simpa using hge)
  have hg : φ.symm.reindexGL D g = e⁻¹ * fromBlocksGL (h⁻¹, (1 : GL {x : n // x ≠ i} D)) := by
    calc φ.symm.reindexGL D g = ((φ.symm.reindexGL D g)⁻¹)⁻¹ := (inv_inv _).symm
      _ = (fromBlocksGL (h, (1 : GL {x : n // x ≠ i} D)) * e)⁻¹ := by rw [hg_inv]
      _ = e⁻¹ * fromBlocksGL (h⁻¹, (1 : GL {x : n // x ≠ i} D)) := by
        rw [_root_.mul_inv_rev, ← map_inv, Prod.inv_mk, inv_one]
  let u : Dˣ := Units.map (Matrix.uniqueRingEquiv : Matrix Unit Unit D ≃+* D).toMonoidHom h⁻¹
  have hh_inv : h⁻¹ = diagGL (fun _ : Unit ↦ u) := by
    refine Units.ext (Matrix.uniqueRingEquiv.injective ?_)
    simp [u, Matrix.uniqueRingEquiv_apply]
  have helim : Sum.elim (fun _ : Unit ↦ u) (1 : {x : n // x ≠ i} → Dˣ) =
      Pi.mulSingle (Sum.inl ()) u := by
    ext (⟨⟩ | x) <;> simp
  have hdiag : φ.reindexGL D (fromBlocksGL (h⁻¹, (1 : GL {x : n // x ≠ i} D))) =
      diagGL (Pi.mulSingle i u) := by
    rw [hh_inv, ← map_one diagGL, fromBlocksGL_diagGL, Equiv.reindexGL_diagGL, helim]
    congr 1
    simpa [φ] using Pi.mulSingle_comp_equiv φ.symm (Sum.inl ()) u
  refine ⟨φ.reindexGL D e⁻¹, (φ.reindexGL_mem_elementarySubgroup_iff).mpr (inv_mem he), u, ?_⟩
  simpa [map_mul, hdiag] using congrArg (φ.reindexGL D) hg

/-- Over a division ring, every invertible matrix factors as an elementary matrix times an
invertible diagonal matrix. -/
theorem exists_mem_elementarySubgroup_mul_diagGL {n : Type*} [Fintype n] [DecidableEq n]
    (g : GL n D) :
    ∃ e ∈ elementarySubgroup n D, ∃ d : n → Dˣ, g = e * diagGL d := by
  rcases isEmpty_or_nonempty n with hn | ⟨⟨i₀⟩⟩
  · exact ⟨1, one_mem _, 1, Subsingleton.elim _ _⟩
  · obtain ⟨e, he, u, rfl⟩ := exists_mem_elementarySubgroup_mul_diagGL_mulSingle i₀ g
    exact ⟨e, he, Pi.mulSingle i₀ u, rfl⟩

/-- **The elementary subgroup is normal over a division ring**, already at every finite matrix
size. -/
instance elementarySubgroup_normal {n : Type*} [Fintype n] [DecidableEq n] :
    (elementarySubgroup n D).Normal := by
  by_cases hn : 2 ≤ Fintype.card n
  · exact elementarySubgroup_normal_of_hasStableRangeLE (hasStableRangeLE_one_of_isLocalRing D) hn
  · have : Subsingleton n := Fintype.card_le_one_iff_subsingleton.mp (by omega)
    have hbot : elementarySubgroup n D = ⊥ :=
      le_bot_iff.mp (elementarySubgroup_le_iff.2 fun i j hij _ ↦ absurd (Subsingleton.elim i j) hij)
    rw [hbot]
    infer_instance

end TauCeti

namespace Matrix.GeneralLinearGroup

/-- Two monoid homomorphisms out of `GL n D` that vanish on `TauCeti.elementarySubgroup n D` and
agree on the single-entry diagonal matrices at a chosen index `i : n` are equal. -/
theorem hom_ext_of_elementarySubgroup_le_ker {n : Type*} [Fintype n] [DecidableEq n]
    {D : Type*} [DivisionRing D] {G : Type*} [Monoid G] {φ ψ : GL n D →* G}
    (hφ : TauCeti.elementarySubgroup n D ≤ φ.ker)
    (hψ : TauCeti.elementarySubgroup n D ≤ ψ.ker) (i : n)
    (hdiag : ∀ u : Dˣ,
      φ (TauCeti.diagGL (Pi.mulSingle i u)) = ψ (TauCeti.diagGL (Pi.mulSingle i u))) :
    φ = ψ := by
  ext g
  obtain ⟨e, he, u, rfl⟩ := TauCeti.exists_mem_elementarySubgroup_mul_diagGL_mulSingle i g
  rw [map_mul, map_mul, hφ he, hψ he, one_mul, one_mul, hdiag]

end Matrix.GeneralLinearGroup

end
