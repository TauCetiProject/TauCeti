/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.UltraweakTopology
public import TauCeti.Analysis.VonNeumannAlgebra.Bicommutant

/-!
# The bicommutant theorem for the ultraweak and ultrastrong topologies

For a unital star subalgebra `S` of bounded operators on a complete real or complex Hilbert
space `H`, both its ultrastrong closure and its ultraweak closure are its double commutant `S''`
(`StarSubalgebra.closure_image_ultrastrongOfCLM`, `StarSubalgebra.closure_image_ultraweakOfCLM`).
So `S` equals `S''` exactly when it is ultraweakly closed, or ultrastrongly closed, and every
concrete complex von Neumann algebra is closed in both topologies. Together with
`TauCeti.Analysis.VonNeumannAlgebra.Bicommutant`, the weak, strong, ultraweak and ultrastrong
closures of `S` all coincide.

Both topologies live on Tau Ceti's type copies `TauCeti.ContinuousLinearMapUltrastrong` and
`TauCeti.ContinuousLinearMapUltraweak`, so the closures are not taken in the operator norm.

The commutant of any set is ultraweakly closed, because the ultraweak topology is finer than the
weak operator topology, in which commutants are closed; the ultrastrong topology is finer still.
For the density of `S` in `S''`, the ultrastrong topology is the strong operator topology of the
ampliation `A ↦ ⊕ₙ A` on `ℓ²(ℕ, H)`, and the ampliation of an element of `S''` lies in the double
commutant of the ampliation of `S`. The strong operator form of the bicommutant theorem, applied to
the ampliated algebra, gives ultrastrong density, which implies ultraweak density.

## Main results

* `Set.isClosed_image_ultraweakOfCLM_centralizer`,
  `Set.isClosed_image_ultrastrongOfCLM_centralizer`: commutants are ultraweakly and
  ultrastrongly closed.
* `StarSubalgebra.closure_image_ultrastrongOfCLM`, `StarSubalgebra.closure_image_ultraweakOfCLM`:
  the ultrastrong and ultraweak closures of `S` are `S''`.
* `StarSubalgebra.double_commutant_iff_isClosed_image_ultraweakOfCLM`,
  `StarSubalgebra.double_commutant_iff_isClosed_image_ultrastrongOfCLM`: the bicommutant theorem.
* `VonNeumannAlgebra.image_ultraweakOfCLM_adjoin_eq_closure`,
  `VonNeumannAlgebra.image_ultrastrongOfCLM_adjoin_eq_closure`: a generated von Neumann algebra is
  the ultraweak and the ultrastrong closure of the generated star algebra.

## References

* C. Houdayer, *An introduction to von Neumann algebras*, lecture notes, Theorem 3.1.
* J. Peterson, *Notes on von Neumann algebras*, Theorem 2.5.6 and Lemma 2.5.5, for the
  amplification argument.
* M. Takesaki, *Theory of Operator Algebras I*, Springer, 1979, Chapter II, Theorem 3.9.
-/

public section

open TauCeti

namespace Set

variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
  [CompleteSpace H]

/-- The commutant of any set of operators is ultraweakly closed. -/
theorem isClosed_image_ultraweakOfCLM_centralizer (s : Set (H →L[𝕜] H)) :
    IsClosed (ContinuousLinearMapUltraweak.ofCLM '' s.centralizer) := by
  convert s.isClosed_image_ofCLM_centralizer.preimage ContinuousLinearMapUltraweak.continuous_toWOT
    using 1
  ext ⟨A⟩
  simp

/-- The commutant of any set of operators is ultrastrongly closed. -/
theorem isClosed_image_ultrastrongOfCLM_centralizer (s : Set (H →L[𝕜] H)) :
    IsClosed (ContinuousLinearMapUltrastrong.ofCLM '' s.centralizer) := by
  convert s.isClosed_image_ultraweakOfCLM_centralizer.preimage
    ContinuousLinearMapUltraweak.continuous_ofUltrastrong using 1
  ext ⟨A⟩
  simp

end Set

namespace StarSubalgebra

variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
  [CompleteSpace H]

/-- The ultrastrong closure of a unital star subalgebra is its double commutant. -/
theorem closure_image_ultrastrongOfCLM (S : StarSubalgebra 𝕜 (H →L[𝕜] H)) :
    closure (ContinuousLinearMapUltrastrong.ofCLM '' (S : Set (H →L[𝕜] H))) =
      ContinuousLinearMapUltrastrong.ofCLM '' (S : Set (H →L[𝕜] H)).centralizer.centralizer := by
  refine subset_antisymm (closure_minimal (Set.image_mono Set.subset_centralizer_centralizer)
    (Set.isClosed_image_ultrastrongOfCLM_centralizer _)) ?_
  rintro _ ⟨x, hx, rfl⟩
  let φ := lp.ampliationStarAlgHom ℕ 𝕜 H
  -- The ampliation of `x` lies in the double commutant of the ampliation of `S`, hence in the
  -- strong operator closure of the ampliation of `S`.
  have hφ : φ x ∈ (S.map φ : Set _).centralizer.centralizer := by
    simpa [φ, StarSubalgebra.coe_map] using
      lp.ampliation_mem_centralizer_centralizer (ι := ℕ) (p := 2) (by simp) hx
  have hcl := (S.map φ).closure_image_toPointwiseConvergenceCLM ▸ Set.mem_image_of_mem _ hφ
  rw [StarSubalgebra.coe_map, Set.image_image] at hcl
  simp only [φ, lp.coe_ampliationStarAlgHom] at hcl
  -- The ultrastrong topology is induced by the strong operator topology of the ampliation.
  rw [ContinuousLinearMapUltrastrong.isInducing_toPointwiseConvergenceCLM_ampliation
    |>.closure_eq_preimage_closure_image, Set.mem_preimage, Set.image_image]
  exact hcl

/-- The ultraweak closure of a unital star subalgebra is its double commutant. -/
theorem closure_image_ultraweakOfCLM (S : StarSubalgebra 𝕜 (H →L[𝕜] H)) :
    closure (ContinuousLinearMapUltraweak.ofCLM '' (S : Set (H →L[𝕜] H))) =
      ContinuousLinearMapUltraweak.ofCLM '' (S : Set (H →L[𝕜] H)).centralizer.centralizer := by
  refine subset_antisymm (closure_minimal (Set.image_mono Set.subset_centralizer_centralizer)
    (Set.isClosed_image_ultraweakOfCLM_centralizer _)) ?_
  rintro _ ⟨x, hx, rfl⟩
  have hx' : ContinuousLinearMapUltrastrong.ofCLM x ∈
      closure (ContinuousLinearMapUltrastrong.ofCLM '' (S : Set (H →L[𝕜] H))) :=
    S.closure_image_ultrastrongOfCLM ▸ Set.mem_image_of_mem _ hx
  simpa [Set.image_image] using mem_closure_image
    ContinuousLinearMapUltraweak.continuous_ofUltrastrong.continuousAt hx'

/-- **The bicommutant theorem, ultraweak form:** a unital star subalgebra equals its double
commutant if and only if it is ultraweakly closed. -/
theorem double_commutant_iff_isClosed_image_ultraweakOfCLM
    (S : StarSubalgebra 𝕜 (H →L[𝕜] H)) :
    (S : Set (H →L[𝕜] H)).centralizer.centralizer = S ↔
      IsClosed (ContinuousLinearMapUltraweak.ofCLM '' (S : Set (H →L[𝕜] H))) := by
  rw [← closure_eq_iff_isClosed, S.closure_image_ultraweakOfCLM,
    (Set.image_injective.mpr fun _ _ ↦ ContinuousLinearMapUltraweak.ofCLM.inj).eq_iff]

/-- **The bicommutant theorem, ultrastrong form:** a unital star subalgebra equals its double
commutant if and only if it is ultrastrongly closed. -/
theorem double_commutant_iff_isClosed_image_ultrastrongOfCLM
    (S : StarSubalgebra 𝕜 (H →L[𝕜] H)) :
    (S : Set (H →L[𝕜] H)).centralizer.centralizer = S ↔
      IsClosed (ContinuousLinearMapUltrastrong.ofCLM '' (S : Set (H →L[𝕜] H))) := by
  rw [← closure_eq_iff_isClosed, S.closure_image_ultrastrongOfCLM,
    (Set.image_injective.mpr fun _ _ ↦ ContinuousLinearMapUltrastrong.ofCLM.inj).eq_iff]

end StarSubalgebra

namespace VonNeumannAlgebra

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A concrete von Neumann algebra is ultraweakly closed. -/
theorem isClosed_image_ultraweakOfCLM (M : VonNeumannAlgebra H) :
    IsClosed (ContinuousLinearMapUltraweak.ofCLM '' (M : Set (H →L[ℂ] H))) :=
  M.toStarSubalgebra.double_commutant_iff_isClosed_image_ultraweakOfCLM.mp
    M.centralizer_centralizer

/-- A concrete von Neumann algebra is ultrastrongly closed. -/
theorem isClosed_image_ultrastrongOfCLM (M : VonNeumannAlgebra H) :
    IsClosed (ContinuousLinearMapUltrastrong.ofCLM '' (M : Set (H →L[ℂ] H))) :=
  M.toStarSubalgebra.double_commutant_iff_isClosed_image_ultrastrongOfCLM.mp
    M.centralizer_centralizer

/-- The von Neumann algebra generated by `s` is the ultraweak closure of the star algebra
generated by `s`. -/
theorem image_ultraweakOfCLM_adjoin_eq_closure (s : Set (H →L[ℂ] H)) :
    ContinuousLinearMapUltraweak.ofCLM '' (adjoin s : Set (H →L[ℂ] H)) =
      closure (ContinuousLinearMapUltraweak.ofCLM ''
        (StarAlgebra.adjoin ℂ s : Set (H →L[ℂ] H))) := by
  rw [StarSubalgebra.closure_image_ultraweakOfCLM, ← adjoin_starAlgebraAdjoin,
    coe_adjoin_of_star_subset (StarMemClass.star_coe_eq _).subset]

/-- The von Neumann algebra generated by `s` is the ultrastrong closure of the star algebra
generated by `s`. -/
theorem image_ultrastrongOfCLM_adjoin_eq_closure (s : Set (H →L[ℂ] H)) :
    ContinuousLinearMapUltrastrong.ofCLM '' (adjoin s : Set (H →L[ℂ] H)) =
      closure (ContinuousLinearMapUltrastrong.ofCLM ''
        (StarAlgebra.adjoin ℂ s : Set (H →L[ℂ] H))) := by
  rw [StarSubalgebra.closure_image_ultrastrongOfCLM, ← adjoin_starAlgebraAdjoin,
    coe_adjoin_of_star_subset (StarMemClass.star_coe_eq _).subset]

end VonNeumannAlgebra
