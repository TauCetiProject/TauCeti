/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Admissible
public import TauCeti.RepresentationTheory.GL2.CompactWeight.Orthogonal
import TauCeti.Analysis.SpecialFunctions.Complex.Exp.ZpowInjective
import TauCeti.LinearAlgebra.End.Aeval
import TauCeti.RepresentationTheory.Isotypic

/-!
# Admissibility of the module of compact weights

The action `TauCeti.CompactWeightModule.orthogonalRep k μ` of `O(2)` on the compact weights has
finite multiplicities: for every irreducible subrepresentation `U`, `Hom_{O(2)}(U, V)` is
finite-dimensional. Hence the `(𝔤𝔩₂(ℂ), O(2))`-module of all compact weights, and every
`(𝔤𝔩₂(ℂ), O(2))`-submodule of it such as the discrete series `D_k(μ)`, is admissible.

The proof uses one rotation `r` by the angle `1`, of phase `z = e^{i}`. Since `π` is irrational, `z`
is not a root of unity, so the powers `z ^ ℓ`, `ℓ ∈ ℤ`, are pairwise distinct
(`Complex.exp_I_zpow_injective`). The rotation acts on `v_ℓ` by `z ^ ℓ`, so for a finite set `S` of
weights the polynomial `q = ∏_{ℓ ∈ S} (X - z ^ ℓ)` in `r` kills exactly the vectors supported on
`S`. Fix a nonzero `u ∈ U` and let `S` be its support. An intertwining map `f : U → V` commutes with
`q(r)`, so `f u` is again supported on `S`. Since `U` is irreducible, `f` is determined by `f u`, so
`f ↦ f u` embeds `Hom_{O(2)}(U, V)` in the finite-dimensional space of vectors supported on `S`.

## Main results

* `TauCeti.CompactWeightModule.equivFinsupp_apply_mem_supported`: an intertwining map from a
  subrepresentation preserves the support of a vector in the weight basis.
* `TauCeti.CompactWeightModule.hasFiniteMultiplicities_orthogonalRep`: the action of `O(2)` on the
  compact weights has finite multiplicities.

## References

* A. W. Knapp, *Local Langlands correspondence: the Archimedean case*, in *Motives*, Proc. Sympos.
  Pure Math. 55, part 2, Amer. Math. Soc., 1994, pp. 393–410, §2, pp. 398–400.
-/

public section

noncomputable section

open Complex Matrix Polynomial Representation

namespace TauCeti

namespace CompactWeightModule

variable {k μ : ℂ}

/-- **Intertwining maps preserve supports of weights**: if `u` lies in a subrepresentation `U` and
is supported on a finite set `S` of weights, then so is `f u` for every intertwining map
`f : U → V`. -/
theorem equivFinsupp_apply_mem_supported {U : Subrepresentation (orthogonalRep k μ)}
    (f : IntertwiningMap U.toRepresentation (orthogonalRep k μ)) {S : Finset ℤ} {u : U.toSubmodule}
    (hu : equivFinsupp k μ (u : CompactWeightModule k μ) ∈ Finsupp.supported ℂ ℂ (S : Set ℤ)) :
    equivFinsupp k μ (f u) ∈ Finsupp.supported ℂ ℂ (S : Set ℤ) := by
  -- The polynomial `q = ∏_{ℓ ∈ S} (X - z ^ ℓ)` in the rotation `r` by the angle `1` kills exactly
  -- the vectors supported on `S`. It kills `u`, hence `f u`.
  let r := orthogonalRotation 1
  let q : ℂ[X] := ∏ ℓ ∈ S, (X - C (orthogonalPhase r ^ ℓ))
  have hq (j : ℤ) : q.eval (orthogonalPhase r ^ j) = 0 ↔ j ∈ (S : Set ℤ) := by
    simp only [q, r, eval_prod, eval_sub, eval_X, eval_C, Finset.prod_eq_zero_iff, sub_eq_zero,
      Finset.mem_coe, orthogonalPhase_orthogonalRotation, ofReal_one, one_mul]
    exact ⟨fun ⟨ℓ, hℓ, h⟩ ↦ exp_I_zpow_injective h ▸ hℓ,
      fun h ↦ ⟨j, h, rfl⟩⟩
  have hker := aeval_orthogonalRep_eq_zero_iff (k := k) (μ := μ) (det_orthogonalRotation 1) hq
  have hincl := Module.End.aeval_comp_of_comp_eq (U.subtype.isIntertwining' r).symm q
  rw [Subrepresentation.toLinearMap_subtype] at hincl
  have hzero : aeval (U.toRepresentation r) q u = 0 :=
    Subtype.ext ((congr($hincl u)).symm.trans ((hker _).2 hu))
  have hf := congr($(Module.End.aeval_comp_of_comp_eq (f.isIntertwining' r).symm q) u)
  simp only [LinearMap.comp_apply, hzero, map_zero] at hf
  exact (hker _).1 hf

/-- **The compact weights have finite multiplicities** under `O(2)`: for every irreducible
subrepresentation `U` of the compact weights, `Hom_{O(2)}(U, V)` is finite-dimensional. -/
theorem hasFiniteMultiplicities_orthogonalRep :
    (orthogonalRep k μ).HasFiniteMultiplicities := by
  rw [Representation.hasFiniteMultiplicities_iff]
  intro U hU
  have : Nontrivial U.toSubmodule := IsIrreducible.nontrivial hU
  obtain ⟨u, hu⟩ := exists_ne (0 : U.toSubmodule)
  let S : Finset ℤ := (equivFinsupp k μ (u : CompactWeightModule k μ)).support
  let Φ : IntertwiningMap U.toRepresentation (orthogonalRep k μ) →ₗ[ℂ]
      Finsupp.supported ℂ ℂ (S : Set ℤ) :=
    { toFun f := ⟨equivFinsupp k μ (f u),
        equivFinsupp_apply_mem_supported f (Finsupp.mem_supported_support ℂ _)⟩
      map_add' f f' := by ext; simp
      map_smul' c f := by ext; simp }
  have : FiniteDimensional ℂ (Finsupp.supported ℂ ℂ (S : Set ℤ)) :=
    (Finsupp.supportedEquivFinsupp (S : Set ℤ)).symm.finiteDimensional
  exact Module.Finite.of_injective Φ fun f f' h ↦ evalIntertwiningMap_injective
    (ρ := orthogonalRep k μ) hu
    (Subtype.ext (by simpa using (equivFinsupp k μ).injective (congrArg Subtype.val h)))

end CompactWeightModule

end TauCeti
