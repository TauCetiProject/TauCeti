/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.SesquilinearForm.Orthogonal
public import TauCeti.Analysis.Normed.Module.Dual.Bilinear
import TauCeti.Analysis.Normed.Module.Dual.Adjoint
import TauCeti.Analysis.Normed.Module.Dual.Quotient
import TauCeti.Analysis.Normed.Module.Dual.Submodule
import TauCeti.Analysis.Normed.Operator.LinearIsometry

/-!
# Biduals of submodules and kernels of bidual adjoints

For a submodule `S` of a seminormed space `E` over a field satisfying `IsRCLikeNormedField`,
Hahn–Banach identifies `S*` isometrically with `E* ⧸ Sᗮ` (`Submodule.quotientAnnihilatorEquivDual`),
and quotient duality identifies `(E* ⧸ Sᗮ)*` isometrically with the double annihilator `Sᗮᗮ` of
`S` in `E**` (`Submodule.quotientDualEquivAnnihilator`). Composing the two identifies `S**`
isometrically with `Sᗮᗮ`, with underlying map the bidual adjoint `S.subtypeL**` of the inclusion.
Neither completeness of `E` nor closedness of `S` is needed.

When `T : E →L[𝕜] F` is a bounded operator between Banach spaces with closed range, the
closed-range theorem gives `range T* = (ker T)ᗮ`, so `ker T** = (range T*)ᗮ = (ker T)ᗮᗮ`. Combined
with the submodule identification, `(ker T).subtypeL**` identifies `(ker T)**` isometrically with
`ker T**`. This pulls bidual-valued maps landing in `ker T**` (such as derivations into `ker Δ**`
in the characterization of amenable Banach algebras) back to `(ker T)**` without requiring `ker T`
to be complemented.

## Main definitions

* `Submodule.bidualEquivDoubleAnnihilator`: the isometric equivalence `S** ≃ₗᵢ[𝕜] Sᗮᗮ`.
* `ContinuousLinearMap.bidualKerEquivKerPrecompPrecomp`: the isometric equivalence
  `(ker T)** ≃ₗᵢ[𝕜] ker T**` for a closed-range operator `T` between Banach spaces.

## Main results

* `Submodule.coe_bidualEquivDoubleAnnihilator`, `Submodule.norm_comp_precomp_subtypeL`,
  `Submodule.range_precomp_precomp_subtypeL`: `S.subtypeL**` is an isometry onto `Sᗮᗮ`.
* `ContinuousLinearMap.ker_precomp_precomp_eq_orthogonalBilin_orthogonalBilin_ker`:
  `ker T** = (ker T)ᗮᗮ` when `T` has closed range.

## References

* R. E. Megginson, *An Introduction to Banach Space Theory*, §2.6.
* W. Rudin, *Functional Analysis*, 2nd ed., Chapter 4.
-/

public section

-- Shorten instance search for submodules and operators on iterated duals.
attribute [local instance] ContinuousLinearMap.strongDualSeminormedAddCommGroup
  ContinuousLinearMap.strongDualNormedSpace
  ContinuousLinearMap.strongBidualSeminormedAddCommGroup
  ContinuousLinearMap.strongBidualNormedSpace

namespace Submodule

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- The bidual of a submodule `S` is isometrically the double annihilator `Sᗮᗮ` in `E**` (the
annihilator in `E**` of the annihilator of `S` in `E*`). Its underlying map into `E**` is the
bidual adjoint of `S.subtypeL`. -/
noncomputable def bidualEquivDoubleAnnihilator (S : Submodule 𝕜 E) :
    StrongDual 𝕜 (StrongDual 𝕜 S) ≃ₗᵢ[𝕜]
      (S.orthogonalBilin (topDualPairing 𝕜 E).flip).orthogonalBilin
        (topDualPairing 𝕜 (StrongDual 𝕜 E)).flip :=
  (S.quotientAnnihilatorEquivDual.precomp 𝕜).trans
    (S.orthogonalBilin (topDualPairing 𝕜 E).flip).quotientDualEquivAnnihilator

/-- `S.bidualEquivDoubleAnnihilator` evaluates on an ambient functional `f` by restricting `f` to
`S`. -/
@[simp]
theorem bidualEquivDoubleAnnihilator_apply (S : Submodule 𝕜 E) (Φ : StrongDual 𝕜 (StrongDual 𝕜 S))
    (f : StrongDual 𝕜 E) :
    (S.bidualEquivDoubleAnnihilator Φ : StrongDual 𝕜 (StrongDual 𝕜 E)) f =
      Φ (f.comp S.subtypeL) := by
  simp [bidualEquivDoubleAnnihilator]

/-- Forgetting the double-annihilator subtype recovers the bidual adjoint of `S.subtypeL`. -/
theorem coe_bidualEquivDoubleAnnihilator (S : Submodule 𝕜 E) (Φ : StrongDual 𝕜 (StrongDual 𝕜 S)) :
    (S.bidualEquivDoubleAnnihilator Φ : StrongDual 𝕜 (StrongDual 𝕜 E)) =
      ContinuousLinearMap.precomp 𝕜 (ContinuousLinearMap.precomp 𝕜 S.subtypeL) Φ := by
  ext f
  simp

/-- Evaluating `S.bidualEquivDoubleAnnihilator.symm` on the restriction of an ambient functional `f`
applies the ambient bidual element to `f`. -/
@[simp]
theorem bidualEquivDoubleAnnihilator_symm_apply_comp_subtypeL (S : Submodule 𝕜 E)
    (Ψ : (S.orthogonalBilin (topDualPairing 𝕜 E).flip).orthogonalBilin
      (topDualPairing 𝕜 (StrongDual 𝕜 E)).flip)
    (f : StrongDual 𝕜 E) :
    S.bidualEquivDoubleAnnihilator.symm Ψ (f.comp S.subtypeL) =
      (Ψ : StrongDual 𝕜 (StrongDual 𝕜 E)) f := by
  simp [bidualEquivDoubleAnnihilator]

-- `ContinuousLinearMap.precomp_apply` simplifies `precomp 𝕜 (precomp 𝕜 S.subtypeL) Φ` to this LHS.
/-- Precomposing a bidual element of `S` with restriction `E* → S*` preserves norms. -/
@[simp]
theorem norm_comp_precomp_subtypeL (S : Submodule 𝕜 E) (Φ : StrongDual 𝕜 (StrongDual 𝕜 S)) :
    ‖Φ.comp (ContinuousLinearMap.precomp 𝕜 S.subtypeL)‖ = ‖Φ‖ := by
  rw [← ContinuousLinearMap.precomp_apply, ← coe_bidualEquivDoubleAnnihilator,
    Submodule.norm_coe, LinearIsometryEquiv.norm_map]

/-- The range of the bidual adjoint of `S.subtypeL` is the double annihilator `Sᗮᗮ` in `E**`. -/
theorem range_precomp_precomp_subtypeL (S : Submodule 𝕜 E) :
    (ContinuousLinearMap.precomp 𝕜
      (ContinuousLinearMap.precomp 𝕜 S.subtypeL : StrongDual 𝕜 E →L[𝕜] StrongDual 𝕜 S)).range =
      (S.orthogonalBilin (topDualPairing 𝕜 E).flip).orthogonalBilin
        (topDualPairing 𝕜 (StrongDual 𝕜 E)).flip := by
  ext Ψ
  constructor
  · rintro ⟨Φ, rfl⟩
    simp only [ContinuousLinearMap.coe_coe, ← coe_bidualEquivDoubleAnnihilator]
    exact (S.bidualEquivDoubleAnnihilator Φ).2
  · intro hΨ
    refine ⟨S.bidualEquivDoubleAnnihilator.symm ⟨Ψ, hΨ⟩, ?_⟩
    simp only [ContinuousLinearMap.coe_coe, ← coe_bidualEquivDoubleAnnihilator,
      LinearIsometryEquiv.apply_symm_apply]

end Submodule

namespace ContinuousLinearMap

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]

/-- If a bounded operator between Banach spaces has closed range, the kernel of its bidual adjoint
is the double annihilator `(ker T)ᗮᗮ` in `E**`. -/
theorem ker_precomp_precomp_eq_orthogonalBilin_orthogonalBilin_ker (T : E →L[𝕜] F)
    (hT : IsClosed (T.range : Set F)) :
    (precomp 𝕜 (precomp 𝕜 T : StrongDual 𝕜 F →L[𝕜] StrongDual 𝕜 E) :
        StrongDual 𝕜 (StrongDual 𝕜 E) →L[𝕜] StrongDual 𝕜 (StrongDual 𝕜 F)).ker =
      (T.ker.orthogonalBilin (topDualPairing 𝕜 E).flip).orthogonalBilin
        (topDualPairing 𝕜 (StrongDual 𝕜 E)).flip := by
  rw [ker_precomp_eq_orthogonalBilin_range, T.range_precomp_eq_orthogonalBilin_ker hT]

/-- For a bounded operator `T` between Banach spaces with closed range, the bidual adjoint of the
inclusion of `ker T` identifies `(ker T)**` isometrically with `ker T**`. -/
noncomputable def bidualKerEquivKerPrecompPrecomp (T : E →L[𝕜] F)
    (hT : IsClosed (T.range : Set F)) :
    StrongDual 𝕜 (StrongDual 𝕜 T.ker) ≃ₗᵢ[𝕜]
      (precomp 𝕜 (precomp 𝕜 T : StrongDual 𝕜 F →L[𝕜] StrongDual 𝕜 E) :
        StrongDual 𝕜 (StrongDual 𝕜 E) →L[𝕜] StrongDual 𝕜 (StrongDual 𝕜 F)).ker :=
  T.ker.bidualEquivDoubleAnnihilator.trans
    (LinearIsometryEquiv.ofEq (R' := 𝕜) _ _
      (T.ker_precomp_precomp_eq_orthogonalBilin_orthogonalBilin_ker hT).symm)

/-- `T.bidualKerEquivKerPrecompPrecomp` evaluates on an ambient functional `f` by restricting `f`
to `ker T`. -/
@[simp]
theorem bidualKerEquivKerPrecompPrecomp_apply (T : E →L[𝕜] F) (hT : IsClosed (T.range : Set F))
    (Φ : StrongDual 𝕜 (StrongDual 𝕜 T.ker)) (f : StrongDual 𝕜 E) :
    (T.bidualKerEquivKerPrecompPrecomp hT Φ : StrongDual 𝕜 (StrongDual 𝕜 E)) f =
      Φ (f.comp T.ker.subtypeL) := by
  simp [bidualKerEquivKerPrecompPrecomp]

/-- Forgetting the kernel subtype recovers the bidual adjoint of `T.ker.subtypeL`. -/
theorem coe_bidualKerEquivKerPrecompPrecomp (T : E →L[𝕜] F) (hT : IsClosed (T.range : Set F))
    (Φ : StrongDual 𝕜 (StrongDual 𝕜 T.ker)) :
    (T.bidualKerEquivKerPrecompPrecomp hT Φ : StrongDual 𝕜 (StrongDual 𝕜 E)) =
      precomp 𝕜 (precomp 𝕜 T.ker.subtypeL) Φ := by
  ext f
  simp

/-- Evaluating `(T.bidualKerEquivKerPrecompPrecomp hT).symm` on the restriction of an ambient
functional `f` applies the ambient bidual element to `f`. -/
@[simp]
theorem bidualKerEquivKerPrecompPrecomp_symm_apply_comp_subtypeL (T : E →L[𝕜] F)
    (hT : IsClosed (T.range : Set F))
    (Ψ : (precomp 𝕜 (precomp 𝕜 T : StrongDual 𝕜 F →L[𝕜] StrongDual 𝕜 E) :
      StrongDual 𝕜 (StrongDual 𝕜 E) →L[𝕜] StrongDual 𝕜 (StrongDual 𝕜 F)).ker)
    (f : StrongDual 𝕜 E) :
    (T.bidualKerEquivKerPrecompPrecomp hT).symm Ψ (f.comp T.ker.subtypeL) =
      (Ψ : StrongDual 𝕜 (StrongDual 𝕜 E)) f := by
  simp [bidualKerEquivKerPrecompPrecomp]

end ContinuousLinearMap
