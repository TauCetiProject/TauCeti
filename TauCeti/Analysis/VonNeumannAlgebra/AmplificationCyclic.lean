/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dimension.Basic
public import TauCeti.Analysis.InnerProductSpace.Amplification
public import TauCeti.Analysis.VonNeumannAlgebra.Adjoin
public import TauCeti.Analysis.VonNeumannAlgebra.Cyclic

/-!
# Cyclicity of diagonal amplifications of `B(H)`

For a complex Hilbert space `H ≠ 0` and a finite index type `ι`, the diagonal amplification
`T ↦ T ⊕ ⋯ ⊕ T` of `B(H)` acts on the Hilbert sum `PiLp 2 (fun _ : ι ↦ H)`. Packaged as the von
Neumann algebra `VonNeumannAlgebra.diagAmpliation`, a vector `ξ` is cyclic for this action if and
only if its coordinates `(ξ i)ᵢ` are linearly independent over `ℂ`. Consequently there exists a
cyclic vector if and only if `Module.rank ℂ H` is at least `#ι`.

The obstruction direction builds a nonzero operator in the commutant from a linear dependence among
the coordinates (a closed linear-relation witness), so `ξ` fails to be separating for the
commutant. The converse uses the finite Gram construction: linear independence yields a basis of
the coordinate span, hence a bounded operator realizing any prescribed images of the coordinates
(extended by zero on the orthogonal complement), so the diagonal orbit is the whole Hilbert sum.

In particular, when `dim H ≥ 2` the amplification on two copies of `H` admits a cyclic vector.

## References

* J. Peterson, *Notes on von Neumann Algebras* (2013), §2.1.
-/

public section

open ContinuousLinearMap
open scoped InnerProductSpace Pointwise

namespace VonNeumannAlgebra

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable {ι : Type*} [Fintype ι]

variable [CompleteSpace H]

/-- The von Neumann algebra of diagonal amplifications of `B(H)` on the Hilbert sum
`PiLp 2 (fun _ : ι ↦ H)`. -/
noncomputable def diagAmpliation : VonNeumannAlgebra (PiLp 2 (fun _ : ι => H)) :=
  adjoin (Set.range (PiLp.diagStarAlgHom ℂ H ι))

/-- Every diagonal amplification of an operator on `H` lies in `diagAmpliation`. -/
theorem mem_diagAmpliation_diagStarAlgHom (T : H →L[ℂ] H) :
    PiLp.diagStarAlgHom ℂ H ι T ∈ diagAmpliation (H := H) (ι := ι) :=
  subset_adjoin _ ⟨T, rfl⟩

/-- Containedness in `diagAmpliation` is characterised by membership of every diagonal image. -/
@[simp]
theorem diagAmpliation_le_iff {M : VonNeumannAlgebra (PiLp 2 (fun _ : ι => H))} :
    diagAmpliation (H := H) (ι := ι) ≤ M ↔
      ∀ T : H →L[ℂ] H, PiLp.diagStarAlgHom ℂ H ι T ∈ M := by
  simp [diagAmpliation, adjoin_le_iff, Set.range_subset_iff, SetLike.mem_coe]

/-- A vector with linearly independent coordinates is cyclic for `diagAmpliation`. -/
theorem isCyclic_diagAmpliation_of_linearIndependent
    {ξ : PiLp 2 (fun _ : ι => H)} (hξ : LinearIndependent ℂ (fun i : ι => (ξ i : H))) :
    (diagAmpliation (H := H) (ι := ι)).IsCyclic ξ := by
  rw [isCyclic_iff]
  have h := PiLp.range_diagStarAlgHom_apply_eq_univ_of_linearIndependent hξ
  have : (fun T : PiLp 2 (fun _ : ι => H) →L[ℂ] PiLp 2 (fun _ : ι => H) => T ξ) ''
      (diagAmpliation (H := H) (ι := ι) : Set _) = Set.univ :=
    Set.Subset.antisymm (Set.subset_univ _) fun v _ => by
      obtain ⟨T, hT⟩ := (Set.ext_iff.1 h v).2 (Set.mem_univ v)
      exact ⟨_, mem_diagAmpliation_diagStarAlgHom T, hT⟩
  simp [this]

/-- The relation operator lies in the commutant of `diagAmpliation`. -/
theorem relationCLM_mem_commutant_diagAmpliation (c : ι → ℂ) :
    PiLp.relationCLM (H := H) (𝕜 := ℂ) c ∈
      (diagAmpliation (H := H) (ι := ι)).commutant := by
  rw [← SetLike.mem_coe, diagAmpliation, coe_commutant_adjoin]
  have hstar : star (Set.range (PiLp.diagStarAlgHom ℂ H ι)) =
      Set.range (PiLp.diagStarAlgHom ℂ H ι) := by
    ext S
    simp only [Set.mem_star, Set.mem_range]
    constructor
    · rintro ⟨T, hT⟩
      exact ⟨star T, by rw [map_star, hT, star_star]⟩
    · rintro ⟨T, rfl⟩
      exact ⟨star T, map_star _ _⟩
  rw [hstar, Set.union_self]
  intro T hT
  obtain ⟨t, rfl⟩ := hT
  exact (PiLp.relationCLM_mul_diagStarAlgHom (H := H) (𝕜 := ℂ) c t).symm

/-- Closed linear-relation obstruction: linearly dependent coordinates prevent cyclicity when
`H` is nontrivial, by producing a nonzero commutant element that kills `ξ`. -/
theorem not_isCyclic_diagAmpliation_of_not_linearIndependent [Nontrivial H]
    {ξ : PiLp 2 (fun _ : ι => H)} (h : ¬ LinearIndependent ℂ (fun i : ι => (ξ i : H))) :
    ¬ (diagAmpliation (H := H) (ι := ι)).IsCyclic ξ := by
  classical
  rw [isCyclic_iff_isSeparating_commutant, isSeparating_iff]
  rw [Fintype.not_linearIndependent_iff] at h
  obtain ⟨c, hsum, j, hj⟩ := h
  let R := PiLp.relationCLM (H := H) (𝕜 := ℂ) c
  have hRmem : R ∈ (diagAmpliation (H := H) (ι := ι)).commutant :=
    relationCLM_mem_commutant_diagAmpliation c
  have hRξ : R ξ = 0 := by
    ext i
    simp [R, PiLp.relationCLM_apply, hsum]
  have hRne : R ≠ 0 := by
    intro hR0
    obtain ⟨h0, hh0⟩ := exists_ne (0 : H)
    have hcoord : (R (PiLp.single 2 j h0) j : H) = 0 := by simp [hR0]
    simp only [R, PiLp.relationCLM_apply, PiLp.single_apply] at hcoord
    rw [Finset.sum_eq_single j (fun i _ hi => by simp [hi]) (by simp)] at hcoord
    simp [hj, hh0] at hcoord
  exact fun hsep => hRne (hsep R hRmem hRξ)

/-- Cyclicity of a vector for the diagonal amplification is equivalent to linear independence of
its coordinates, when `H` is nontrivial. -/
theorem isCyclic_diagAmpliation_iff_linearIndependent [Nontrivial H]
    (ξ : PiLp 2 (fun _ : ι => H)) :
    (diagAmpliation (H := H) (ι := ι)).IsCyclic ξ ↔
      LinearIndependent ℂ (fun i : ι => (ξ i : H)) :=
  ⟨fun h => not_not.1 fun hli =>
    not_isCyclic_diagAmpliation_of_not_linearIndependent hli h,
    isCyclic_diagAmpliation_of_linearIndependent⟩

/-- The diagonal amplification admits a cyclic vector if and only if `dim H ≥ #ι`. -/
theorem exists_isCyclic_diagAmpliation_iff [Nontrivial H] :
    (∃ ξ, (diagAmpliation (H := H) (ι := ι)).IsCyclic ξ) ↔
      (Fintype.card ι : Cardinal) ≤ Module.rank ℂ H := by
  refine ⟨fun ⟨ξ, hξ⟩ => ?_, fun h => ?_⟩
  · have hli := (isCyclic_diagAmpliation_iff_linearIndependent ξ).1 hξ
    simpa using hli.cardinal_lift_le_rank
  · obtain ⟨v, hv⟩ :=
      exists_linearIndependent_of_le_rank (R := ℂ) (M := H) (n := Fintype.card ι)
        (by exact_mod_cast h)
    let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
    refine ⟨WithLp.toLp 2 fun i => v (e i),
      (isCyclic_diagAmpliation_iff_linearIndependent _).2 ?_⟩
    convert hv.comp e e.injective
    rename_i i
    rfl

/-- In particular, two copies of an at-least-two-dimensional Hilbert space admit a cyclic vector
for the diagonal amplification of `B(H)`. (`Nontrivial H` is not an extra hypothesis: it follows
from `2 ≤ Module.rank ℂ H`.) -/
theorem exists_isCyclic_diagAmpliation_two
    (hdim : (2 : Cardinal) ≤ Module.rank ℂ H) :
    ∃ ξ : PiLp 2 (fun _ : Fin 2 => H), (diagAmpliation (H := H) (ι := Fin 2)).IsCyclic ξ := by
  have : Nontrivial H :=
    (rank_pos_iff_nontrivial (R := ℂ) (M := H)).1 <|
      lt_of_lt_of_le (by norm_num : (0 : Cardinal) < 2) hdim
  exact (exists_isCyclic_diagAmpliation_iff (ι := Fin 2)).2 (by simpa using hdim)

end VonNeumannAlgebra
