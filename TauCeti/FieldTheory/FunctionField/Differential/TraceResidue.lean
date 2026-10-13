/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Differential.Residue

/-!
# Trace residues of Weil differentials

Let `F / k` be an algebraic function field with exact constant field `k`.
At a place `P` with separable residue field, choose a separating uniformizer `t`.
Every Weil differential has a unique expression `ω = z dt`, since the Weil differential
space is one-dimensional. Its local component at `u` is the residue-field trace of the
coefficient of `t⁻¹` in the Laurent expansion of `z u`.

Here `z` is obtained from the existing basis `weilDifferentialBasisOfSeparating`, rather
than from a new differential carrier. The formula extends
`repartitionDualComponent_weilDifferentialOfSeparating_eq_traceResidue` from `dt` to
arbitrary Weil differentials, including at nonrational places. In particular, the trace
residue is independent of the separating uniformizer, because it equals the intrinsic
local component.

For a family of separating uniformizers, these trace residues have finite support on
every repartition. Their sum on a diagonal function is zero. This is the residue theorem
with residue-field traces; no algebraic closure or infinitude of the constant field is
required. The hypotheses explicitly require separable residue fields and separating
uniformizers, both available over a perfect constant field.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, second edition, Theorem 4.3.2(d),
  Corollary 4.3.3 and Remark 4.3.7(d).
-/

public section

open scoped IntermediateField

namespace TauCeti

variable {k F : Type*} [Field k] [Field F] [Algebra k F]

/-- The local component of `ω = z dt` is the trace residue of `z u`, at a place of any
degree with separable residue field and a separating uniformizer `t`. The coefficient `z`
is the coordinate of `ω` in the basis `dt`. -/
theorem repartitionDualComponent_eq_traceResidue_coord
    (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F)
    {P : Place k F} [Algebra.IsSeparable k P.ResidueField] {t : F}
    (ht : P.ord t = 1) [Algebra.IsSeparable k⟮t⟯ F]
    (ω : ↥(weilDifferentialSpace k F)) (u : F) :
    letI := weilDifferentialSpaceModule hF
    let htr : Transcendental k t := P.transcendental_of_ord_ne_zero (by simp [ht])
    repartitionDualComponent (ω : Module.Dual k ↥(repartitionSpace k F)) P u =
      P.traceResidue ht ((weilDifferentialBasisOfSeparating hF hex htr).coord () ω * u) := by
  let := weilDifferentialSpaceModule hF
  dsimp only
  let htr : Transcendental k t := P.transcendental_of_ord_ne_zero (by simp [ht])
  have hω : (weilDifferentialBasisOfSeparating hF hex htr).coord () ω •
      weilDifferentialOfSeparating hF htr = ω := by
    simpa using (weilDifferentialBasisOfSeparating hF hex htr).sum_repr ω
  -- Translate the uniformizer by zero to use the local formula for `dt`.
  have ht₀ : P.ord (t - algebraMap k F 0) = 1 := by simpa using ht
  have hres : P.traceResidue ht₀ = P.traceResidue ht := by
    simp only [map_zero, sub_zero]
  conv_lhs => rw [← hω]
  rw [coe_weilDifferentialSpaceModule_smul, repartitionDualComponent_repartitionDualMul,
    repartitionDualComponent_weilDifferentialOfSeparating_eq_traceResidue hF htr ht₀, hres]

section Family

variable (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F)
    [∀ P : Place k F, Algebra.IsSeparable k P.ResidueField]
    (t : Place k F → F) (ht : ∀ P : Place k F, P.ord (t P) = 1)
    [∀ P : Place k F, Algebra.IsSeparable k⟮t P⟯ F]

/-- The local trace residues of a Weil differential on a repartition are nonzero at only
finitely many places, even when the places are not rational. -/
theorem finite_support_traceResidue_coord (ω : ↥(weilDifferentialSpace k F))
    (a : ↥(repartitionSpace k F)) :
    letI := weilDifferentialSpaceModule hF
    let htr : ∀ P, Transcendental k (t P) :=
      fun P ↦ P.transcendental_of_ord_ne_zero (by simp [ht P])
    (Function.support fun P : Place k F ↦ P.traceResidue (ht P)
      ((weilDifferentialBasisOfSeparating hF hex (htr P)).coord () ω *
        (a : Place k F → F) P)).Finite := by
  let := weilDifferentialSpaceModule hF
  dsimp only
  let htr : ∀ P, Transcendental k (t P) :=
    fun P ↦ P.transcendental_of_ord_ne_zero (by simp [ht P])
  have heq : (fun P : Place k F ↦ P.traceResidue (ht P)
      ((weilDifferentialBasisOfSeparating hF hex (htr P)).coord () ω *
        (a : Place k F → F) P)) =
      (fun P ↦ repartitionDualComponent (ω : Module.Dual k _) P
        ((a : Place k F → F) P)) := by
    funext P
    exact (repartitionDualComponent_eq_traceResidue_coord hF hex (ht P) ω _).symm
  rw [heq]
  exact finite_support_repartitionDualComponent_apply ω.2 a

/-- The residue theorem with residue-field traces: if `ω = z_P dt_P` at each place,
then `∑_P Tr(res_{P,t_P}(z_P u)) = 0` for every function `u`. The summands have finite
support by `finite_support_traceResidue_coord`, applied to the constant repartition. -/
theorem finsum_traceResidue_coord_eq_zero (ω : ↥(weilDifferentialSpace k F)) (u : F) :
    letI := weilDifferentialSpaceModule hF
    let htr : ∀ P, Transcendental k (t P) :=
      fun P ↦ P.transcendental_of_ord_ne_zero (by simp [ht P])
    ∑ᶠ P : Place k F, P.traceResidue (ht P)
      ((weilDifferentialBasisOfSeparating hF hex (htr P)).coord () ω * u) = 0 := by
  let := weilDifferentialSpaceModule hF
  simp_rw [← repartitionDualComponent_eq_traceResidue_coord hF hex (ht _)]
  exact finsum_repartitionDualComponent_eq_zero hF ω.2 u

end Family

end TauCeti
