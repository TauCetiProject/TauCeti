/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Orthogonal.TypeD.Killing
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.SerrePresentation
import TauCeti.Algebra.Lie.Presentation.Serre.Injective

/-!
# The pinned type-D algebra in orthogonal coordinates

`TauCeti.TypeDStd.pinnedLieEquiv` identifies the rational pinned algebra
`DynkinType.lieAlgebra (.D n)` with the split even orthogonal matrix Lie algebra. It sends the
Cartan, raising and lowering generators to the native Bourbaki-numbered matrices, including
both fork nodes. The inverse equations make the identification usable without unfolding it.

In particular, a representation of the native orthogonal algebra can be pulled back along this
map to a representation of the pinned algebra. This is the Lie-algebra input for realizing
Chevalley data on the existing spin modules; it does not identify any group schemes.

The construction uses `DynkinType.serreLiftEquiv` for the pinned algebra and
`LieAlgebra.Basis.serreLift_injective` for the native matrix basis `TypeDStd.lieBasis`.
Nondegeneracy of the latter's Killing form is supplied by `TypeDStd.isKilling_typeD`, and its
simple-root generation supplies surjectivity. Thus no dimension comparison is assumed.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras*, Chapters 4--6, Plate IV.
* J.-P. Serre, *Complex Semisimple Lie Algebras*, Chapter VI, Appendix.
-/

public section

open scoped Matrix

namespace TauCeti.TypeDStd

-- Use the commutator Lie ring on the ambient matrix algebra, as in the native generators.
attribute [local instance 100] LieRing.ofAssociativeRing

noncomputable section

variable (n : ℕ) (hn : 4 ≤ n)

private theorem pinnedSerreSystem :
    IsSerreSystem ℚ (DynkinType.D n).cartanMatrixᵀ
      (cartanGenerator (K := ℚ) n hn)
      (fun i => rootGenerator (K := ℚ) n hn (.inl i))
      (fun i => rootGenerator (K := ℚ) n hn (.inr i)) := by
  have hh := funext (lieBasis_h (K := ℚ) n hn)
  have he := funext (lieBasis_e (K := ℚ) n hn)
  have hf := funext (lieBasis_f (K := ℚ) n hn)
  simpa only [lieBasis_A_eq, hh, he, hf, DynkinType.cartanMatrix_D,
    DynkinType.rank_D] using
    isSerreSystem_lieBasis (lieBasis (K := ℚ) n hn)

private theorem matrixSerreLift_injective :
    Function.Injective (TauCeti.serreLift (pinnedSerreSystem n hn)) := by
  let _ := isKilling_typeD (K := ℚ) n hn
  -- Transport the presentation matrix, not the Lie algebra or its numbered generators.
  have key : ∀ {CM : Matrix (Fin n) (Fin n) ℤ}, (lieBasis (K := ℚ) n hn).Aᵀ = CM →
      ∀ h : IsSerreSystem ℚ CM (cartanGenerator (K := ℚ) n hn)
        (fun i => rootGenerator n hn (.inl i)) (fun i => rootGenerator n hn (.inr i)),
        Function.Injective (TauCeti.serreLift h) := by
    rintro _ rfl _
    have hh := funext (lieBasis_h (K := ℚ) n hn)
    have he := funext (lieBasis_e (K := ℚ) n hn)
    have hf := funext (lieBasis_f (K := ℚ) n hn)
    simpa only [hh, he, hf] using (lieBasis (K := ℚ) n hn).serreLift_injective
  exact key (by simp only [lieBasis_A_eq, DynkinType.cartanMatrix_D, DynkinType.rank_D]) _

private def matrixSerreEquiv :
    (DynkinType.D n).SerreLieAlgebra ≃ₗ⁅ℚ⁆ LieAlgebra.Orthogonal.typeD (Fin n) ℚ :=
  LieEquiv.ofBijective (TauCeti.serreLift (pinnedSerreSystem n hn))
    ⟨matrixSerreLift_injective n hn,
      serreLift_surjective _ (lieSpan_rootGenerator_eq_top n hn)⟩

private theorem coe_matrixSerreEquiv :
    ⇑(matrixSerreEquiv n hn) = TauCeti.serreLift (pinnedSerreSystem n hn) :=
  (rfl)

/-- The pinned rational type-`Dₙ` Lie algebra in split orthogonal matrix coordinates, matching
all numbered Cartan, raising and lowering generators. -/
def pinnedLieEquiv :
    (DynkinType.D n).lieAlgebra (DynkinType.valid_D.mpr hn) ≃ₗ⁅ℚ⁆
      LieAlgebra.Orthogonal.typeD (Fin n) ℚ :=
  ((DynkinType.D n).serreLiftEquiv (DynkinType.valid_D.mpr hn)).symm.trans
    (matrixSerreEquiv n hn)

/-- A pinned Cartan generator maps to the native diagonal simple-coroot matrix. -/
@[simp↓]
theorem pinnedLieEquiv_lieBasis_h (i : Fin n) :
    pinnedLieEquiv n hn (((DynkinType.D n).lieBasis (DynkinType.valid_D.mpr hn)).h i) =
      cartanGenerator n hn i := by
  rw [pinnedLieEquiv, LieEquiv.trans_apply,
    (DynkinType.D n).serreLiftEquiv_symm_lieBasis_h (DynkinType.valid_D.mpr hn) i,
    coe_matrixSerreEquiv]
  exact serreLift_serreH (pinnedSerreSystem n hn) i

/-- A pinned raising generator maps to the native positive simple-root matrix. -/
@[simp↓]
theorem pinnedLieEquiv_lieBasis_e (i : Fin n) :
    pinnedLieEquiv n hn (((DynkinType.D n).lieBasis (DynkinType.valid_D.mpr hn)).e i) =
      rootGenerator n hn (.inl i) := by
  rw [pinnedLieEquiv, LieEquiv.trans_apply,
    (DynkinType.D n).serreLiftEquiv_symm_lieBasis_e (DynkinType.valid_D.mpr hn) i,
    coe_matrixSerreEquiv]
  exact serreLift_serreE (pinnedSerreSystem n hn) i

/-- A pinned lowering generator maps to the native negative simple-root matrix. -/
@[simp↓]
theorem pinnedLieEquiv_lieBasis_f (i : Fin n) :
    pinnedLieEquiv n hn (((DynkinType.D n).lieBasis (DynkinType.valid_D.mpr hn)).f i) =
      rootGenerator n hn (.inr i) := by
  rw [pinnedLieEquiv, LieEquiv.trans_apply,
    (DynkinType.D n).serreLiftEquiv_symm_lieBasis_f (DynkinType.valid_D.mpr hn) i,
    coe_matrixSerreEquiv]
  exact serreLift_serreF (pinnedSerreSystem n hn) i

/-- The inverse sends a native simple-coroot matrix to the corresponding pinned Cartan
generator. -/
@[simp]
theorem pinnedLieEquiv_symm_cartanGenerator (i : Fin n) :
    (pinnedLieEquiv n hn).symm (cartanGenerator n hn i) =
      ((DynkinType.D n).lieBasis (DynkinType.valid_D.mpr hn)).h i := by
  rw [LieEquiv.symm_apply_eq, pinnedLieEquiv_lieBasis_h]

/-- The inverse sends a native raising matrix to the corresponding pinned raising generator. -/
@[simp]
theorem pinnedLieEquiv_symm_rootGenerator_inl (i : Fin n) :
    (pinnedLieEquiv n hn).symm (rootGenerator n hn (.inl i)) =
      ((DynkinType.D n).lieBasis (DynkinType.valid_D.mpr hn)).e i := by
  rw [LieEquiv.symm_apply_eq, pinnedLieEquiv_lieBasis_e]

/-- The inverse sends a native lowering matrix to the corresponding pinned lowering generator. -/
@[simp]
theorem pinnedLieEquiv_symm_rootGenerator_inr (i : Fin n) :
    (pinnedLieEquiv n hn).symm (rootGenerator n hn (.inr i)) =
      ((DynkinType.D n).lieBasis (DynkinType.valid_D.mpr hn)).f i := by
  rw [LieEquiv.symm_apply_eq, pinnedLieEquiv_lieBasis_f]

end

end TauCeti.TypeDStd
