/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Twisted.SpectralSequence.Splitting
public import TauCeti.Algebra.Homology.DG.Twisted.Filtration

/-!
# The differential between two graded pieces of the index filtration

The twisted differential of a family supported on the generators of index `p` has components at
the generators of index at most `p`: at index `p` it is `dM`, and only the twisting contribution
strictly lowers the index, because the twisting cocycle is one-sided.  Restricting it to the
generators of index `q` gives a map from the graded piece of index `p` to that of index `q`
(`TauCeti.TwistingCocycle.indexGradedPieceD1X`).  For `q + 1 = p` it sends cycles to cycles: on a
cycle of the graded piece of index `p` the component at index `p` vanishes, so the full
differential lies in the filtration stage of index `q`.  Its component between a generator `x` of
index `b + 1` and a generator `y` of index `b` is `α ↦ α · m x y`, up to the Koszul sign.

## Main definitions

* `TauCeti.TwistingCocycle.indexGradedPieceD1X`: the restriction of the twisted differential from
  the graded piece of index `p` to that of index `q`.

## Main results

* `TauCeti.TwistingCocycle.d_indexGradedPieceD1X`: for `q + 1 = p`, it sends cycles to cycles.
* `TauCeti.TwistingCocycle.shiftedModuleComplexXEquiv_indexGradedPieceEval_D1X_single`: its
  entries under the splitting of `TauCeti.indexGradedPieceHomologyIso`.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, Definition 3.38.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, Chapter 3 and Section 4.2.
-/

public section

open CategoryTheory Limits

namespace TauCeti

universe uR uA uM uP

namespace TwistingCocycle

variable {R : Type uR} {A : Type uA} {M : Type uM}
  [CommRing R] [Ring A] [Algebra R A] [AddCommGroup M] [Module R M]
  {P : Type uP} {ind : P → ℤ}
  [Fintype P] [Module Aᵐᵒᵖ M] [IsScalarTower R Aᵐᵒᵖ M] [SMulCommClass R Aᵐᵒᵖ M]
  {ℳ : ℤ → Submodule R M} [DirectSum.Decomposition ℳ] {dM : M →ₗ[R] M}
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {d : A →ₗ[R] A} {h : IsDGAlgebra 𝒜 d}
  [SetLike.GradedSMul (InternalGrading.ofDecomposition 𝒜).opposite.piece ℳ]
  (m : TwistingCocycle 𝒜 d P ind) (hM : IsDGRightModule h ℳ dM)

/-- The restriction to the generators of index `q` of the twisted differential, from the degree-`n`
term of the graded piece of index `p` to the degree-`(n + 1)` term of that of index `q`. -/
noncomputable def indexGradedPieceD1X (q p n : ℤ) :
    (indexGradedPieceComplex hM ind p).X n →ₗ[R] (indexGradedPieceComplex hM ind q).X (n + 1) :=
  (indexGradedPieceComplexXEquiv hM ind q (n + 1)).symm.toLinearMap ∘ₗ
    ((LinearMap.funLeft R M Subtype.val ∘ₗ twistedDifferential m.m ℳ dM ∘ₗ
        indexExtend R M ind p ∘ₗ
          (twistedTotalGrading ℳ (fun x : {x : P // ind x = p} ↦ ind x) n).subtype).codRestrict
        _ fun f ↦ mem_twistedTotalGrading_iff.2 fun y ↦ by
      have := mem_twistedTotalGrading_iff.1 (m.twistedDifferential_mem_twistedTotalGrading dM
        hM.isHomogeneous (indexExtend_mem_twistedTotalGrading f.2)) y.1
      exact this) ∘ₗ
    (indexGradedPieceComplexXEquiv hM ind p n).toLinearMap

/-- `indexGradedPieceD1X` restricts the twisted differential of the family extended by zero to the
generators of index `q`. -/
@[simp]
theorem indexGradedPieceComplexXEquiv_indexGradedPieceD1X (q p n : ℤ)
    (f : (indexGradedPieceComplex hM ind p).X n) :
    (indexGradedPieceComplexXEquiv hM ind q (n + 1) (m.indexGradedPieceD1X hM q p n f) :
        {x : P // ind x = q} → M) =
      LinearMap.funLeft R M Subtype.val (twistedDifferential m.m ℳ dM
        (indexExtend R M ind p (indexGradedPieceComplexXEquiv hM ind p n f))) := by
  simp only [indexGradedPieceD1X, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    LinearEquiv.apply_symm_apply]
  -- The remaining equation holds by unfolding the corestriction of the codomain.
  rfl

/-- The twisted differential of a cycle of the graded piece of index `p = q + 1`, extended by
zero, vanishes at the generators of index greater than `q`. -/
theorem twistedDifferential_indexExtend_eq_zero (q p : ℤ) (hqp : q + 1 = p) (n : ℤ)
    (f : (indexGradedPieceComplex hM ind p).X n)
    (hf : ((indexGradedPieceComplex hM ind p).d n (n + 1)).hom f = 0) :
    ∀ y, q < ind y →
      twistedDifferential m.m ℳ dM
        (indexExtend R M ind p (indexGradedPieceComplexXEquiv hM ind p n f)) y = 0 := by
  intro y hy
  have hF := indexExtend_mem_twistedIndexFiltration (R := R) (M := M) (ind := ind) (p := p)
    (indexGradedPieceComplexXEquiv hM ind p n f)
  have hD := (mem_twistedIndexFiltration_iff _).1
    (twistedDifferential_mem_twistedIndexFiltration (ℳ := ℳ) m.m
      (fun x y hxy ↦ m.one_sided x y hxy) dM hF)
  rcases lt_or_eq_of_le (show p ≤ ind y by omega) with hlt | heq
  · exact hD y hlt
  · have key := congrFun (twistedDifferential_funLeft_val (ℳ := ℳ) m.m
      (fun x y hxy ↦ m.one_sided x y hxy) dM
      (f := indexExtend R M ind p (indexGradedPieceComplexXEquiv hM ind p n f))
      (fun x hx ↦ indexExtend_apply_of_ne _ hx.ne')) ⟨y, heq.symm⟩
    rw [funLeft_indexExtend, LinearMap.funLeft_apply] at key
    rw [← key]
    have := indexGradedPieceComplexXEquiv_d hM ind p n f ⟨y, heq.symm⟩
    rw [hf] at this
    simpa [twistedDifferential_apply] using this.symm

/-- The restriction of the twisted differential sends the cycles of the graded piece of index
`p = q + 1` to cycles of the graded piece of index `q`. -/
theorem d_indexGradedPieceD1X (q p : ℤ) (hqp : q + 1 = p) (n : ℤ)
    (f : (indexGradedPieceComplex hM ind p).X n)
    (hf : ((indexGradedPieceComplex hM ind p).d n (n + 1)).hom f = 0) :
    ((indexGradedPieceComplex hM ind q).d (n + 1) (n + 1 + 1)).hom
      (m.indexGradedPieceD1X hM q p n f) = 0 := by
  refine (indexGradedPieceComplexXEquiv hM ind q (n + 1 + 1)).injective
    (Subtype.ext (funext fun y ↦ ?_))
  have key := congrFun (twistedDifferential_funLeft_val (ℳ := ℳ) m.m
    (fun x y hxy ↦ m.one_sided x y hxy) dM
    (f := twistedDifferential m.m ℳ dM
      (indexExtend R M ind p (indexGradedPieceComplexXEquiv hM ind p n f)))
    (m.twistedDifferential_indexExtend_eq_zero hM q p hqp n f hf)) y
  rw [m.twistedDifferential_sq_zero dM hM] at key
  rw [indexGradedPieceComplexXEquiv_d, indexGradedPieceComplexXEquiv_indexGradedPieceD1X]
  simpa [twistedDifferential_apply] using key

section Components

variable [DecidableEq P] {b : ℤ} (x : {x : P // ind x = b + 1}) (y : {y : P // ind y = b})

/-- **The entries of the first differential, on chains**: inserting `α` at a generator `x` of
index `b + 1`, restricting the twisted differential to the generators of index `b` and evaluating
at such a generator `y` gives `α · m x y`, up to the Koszul sign. -/
theorem shiftedModuleComplexXEquiv_indexGradedPieceEval_D1X_single (n : ℤ)
    (α : (shiftedModuleComplex.{uR, uA, uM, uP} hM (b + 1)).X n) :
    (shiftedModuleComplexXEquiv hM b (n + 1) (((indexGradedPieceEval hM ind y).f (n + 1)).hom
        (m.indexGradedPieceD1X hM b (b + 1) n
          (((indexGradedPieceSingle hM ind x).f n).hom α))) : M) =
      MulOpposite.op (m.m x y) • (InternalGrading.ofDecomposition ℳ).koszulTwist 1
        (shiftedModuleComplexXEquiv hM (b + 1) n α : M) := by
  have hyx : y.1 ≠ x.1 := fun h ↦ by
    have h₁ := x.2
    have h₂ := y.2
    rw [h] at h₂
    omega
  have hext : indexExtend R M ind (b + 1) (Pi.single x (shiftedModuleComplexXEquiv hM (b + 1) n α :
      M)) = Pi.single x.1 (shiftedModuleComplexXEquiv hM (b + 1) n α : M) := by
    funext z
    by_cases hz : ind z = b + 1
    · rw [indexExtend_apply_of_eq _ hz]
      by_cases hzx : z = x.1
      · subst hzx
        simp
      · rw [Pi.single_eq_of_ne hzx, Pi.single_eq_of_ne]
        exact fun h ↦ hzx (congrArg Subtype.val h)
    · rw [indexExtend_apply_of_ne _ hz, Pi.single_eq_of_ne]
      exact fun h ↦ hz (h ▸ x.2)
  -- The component at `y` of the twisted differential of `α ⊗ x`.
  have hcomp : (shiftedModuleComplexXEquiv hM b (n + 1) (((indexGradedPieceEval hM ind y).f
      (n + 1)).hom (m.indexGradedPieceD1X hM b (b + 1) n
        (((indexGradedPieceSingle hM ind x).f n).hom α))) : M) =
      (n + (b + 1)).negOnePow • (MulOpposite.op (m.m x y) •
        (shiftedModuleComplexXEquiv hM (b + 1) n α : M)) := by
    rw [shiftedModuleComplexXEquiv_indexGradedPieceEval_f,
      indexGradedPieceComplexXEquiv_indexGradedPieceD1X,
      indexGradedPieceComplexXEquiv_indexGradedPieceSingle_f, LinearMap.funLeft_apply, hext,
      twistedDifferential_single_apply m.m dM x.1 y.1
        (shiftedModuleComplexXEquiv hM (b + 1) n α).2, Pi.single_eq_of_ne hyx, zero_add]
  -- Normalizing the sign: it is the Koszul sign of `α`, which commutes with the action.
  rw [hcomp, koszulTwist_one_eq_negOnePow_smul (shiftedModuleComplexXEquiv hM (b + 1) n α).2]
  exact smul_comm _ _ _

end Components

end TwistingCocycle

end TauCeti
