/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.FormalGroup.Logarithm.AdicPoint
import TauCeti.RingTheory.FormalGroup.Hom.Additive
import TauCeti.RingTheory.Ideal.IsPrincipal

/-!
# Integral logarithms linearise homomorphisms on adic points

Suppose `n + 1` divides `sⁿ` in a commutative ring without additive torsion. The integral
logarithm of `F.rescale s` conjugates homomorphisms to multiplication by their linear
coefficient. Source and target may be rescaled by different amounts.

On an adic ideal in a complete Hausdorff linearly topologized ring, evaluating these
logarithms gives the same conjugacy between group homomorphisms. Thus the image and cokernel
of a homomorphism on a sufficiently small formal neighbourhood can be computed using scalar
multiplication on the ideal. This is the formal-group contribution to local isogeny indices.
No unit assumption on the linear coefficient is needed.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], IV.5–6.
-/

public section

open FormalGroup

namespace TauCeti.FormalGroupHom

variable {R : Type*} [CommRing R] [HasUniqueDiv R]
  {F G : FormalGroup R} {s t : R}
  (hs : ∀ n : ℕ, (n + 1 : R) ∣ s ^ n)
  (ht : ∀ n : ℕ, (n + 1 : R) ∣ t ^ n)

/-- A homomorphism from a rescaled formal group to the additive law is its linear coefficient
times the integral logarithm. -/
theorem toPowerSeries_eq_coeff_one_smul_rescaleLog (f : FormalGroupHom (F.rescale s) 𝔾ₐ) :
    f.toPowerSeries = PowerSeries.coeff 1 f.toPowerSeries • F.rescaleLog hs := by
  let e := F.rescaleLogIso hs
  have hinv : PowerSeries.coeff 1 e.invHom.toPowerSeries = 1 := by
    simpa only [FormalGroupIso.symm_toHom] using
      (FormalGroupIso.IsStrict.coeff_one (f := e.symm))
  have h := (f.comp e.invHom).toPowerSeries_eq_coeff_one_smul_X
  rw [coeff_one_comp, hinv, mul_one] at h
  have heq : (f.comp e.invHom).comp e.toHom = f := by
    rw [comp_assoc, e.invHom_comp_toHom, comp_id]
  have := congrArg toPowerSeries heq
  rw [comp_toPowerSeries, h, PowerSeries.subst_smul e.toHom.hasSubst,
    PowerSeries.subst_X e.toHom.hasSubst] at this
  simpa only [e, rescaleLogIso_toHom, rescaleLogHom_toPowerSeries] using this.symm

/-- Integral logarithms are natural along homomorphisms, including when the tangent map is
not a unit: `log_G(f(T)) = f'(0) log_F(T)`. -/
theorem subst_rescaleLog (f : FormalGroupHom (F.rescale s) (G.rescale t)) :
    PowerSeries.subst f.toPowerSeries (G.rescaleLog ht) =
      PowerSeries.coeff 1 f.toPowerSeries • F.rescaleLog hs := by
  have h := ((G.rescaleLogHom ht).comp f).toPowerSeries_eq_coeff_one_smul_rescaleLog hs
  rw [coeff_one_comp, rescaleLogHom_toPowerSeries, coeff_one_rescaleLog, one_mul,
    comp_toPowerSeries, rescaleLogHom_toPowerSeries] at h
  exact h

section Adic

variable [UniformSpace R] [IsUniformAddGroup R] [CompleteSpace R] [T2Space R]
  [IsTopologicalRing R] [IsLinearTopology R R]
  (I : Ideal R) [Fact (IsAdic I)]

/-- The evaluated integral logarithms conjugate a homomorphism on adic points to scalar
multiplication on the ideal by its linear coefficient. -/
@[simp]
theorem rescaleLogPointEquiv_toIdealPointHom
    (f : FormalGroupHom (F.rescale s) (G.rescale t))
    (x : (F.rescale s).idealPointSubgroup I) :
    G.rescaleLogPointEquiv ht I (f.toIdealPointHom I x) =
      PowerSeries.coeff 1 f.toPowerSeries • F.rescaleLogPointEquiv hs I x := by
  apply Subtype.ext
  have h := ((G.rescaleLogHom ht).comp f).hasSum_val_toTopNilpotentPointHom x.val
  have hseries := f.subst_rescaleLog hs ht
  rw [comp_toPowerSeries, rescaleLogHom_toPowerSeries, hseries] at h
  have hlog := (F.rescaleLogHom hs).hasSum_val_toTopNilpotentPointHom x.val
  have hmul := hlog.mul_left (PowerSeries.coeff 1 f.toPowerSeries)
  have heq := h.unique (by
    simpa only [PowerSeries.coeff_smul, rescaleLogHom_toPowerSeries, smul_eq_mul,
      mul_assoc] using hmul)
  have hF := hlog.unique (by
    simpa only [rescaleLogHom_toPowerSeries, smul_eq_mul] using
      (PowerSeries.hasSum_aeval (R := R) x.val.hasEval (F.rescaleLog hs)))
  have hG := ((G.rescaleLogHom ht).hasSum_val_toTopNilpotentPointHom
    (f.toTopNilpotentPointHom R x.val)).unique (by
      simpa only [rescaleLogHom_toPowerSeries, smul_eq_mul] using
        (PowerSeries.hasSum_aeval (R := R)
          (f.toTopNilpotentPointHom R x.val).hasEval (G.rescaleLog ht)))
  rw [toTopNilpotentPointHom_comp, AddMonoidHom.comp_apply, hG, hF] at heq
  simpa only [coe_rescaleLogPointEquiv, coe_toIdealPointHom,
    Submodule.coe_smul, smul_eq_mul] using heq

include hs ht

/-- A point is in the image exactly when its logarithm is a scalar multiple, inside the ideal,
of the linear coefficient. This includes noninvertible tangent maps. -/
theorem mem_range_toIdealPointHom_iff
    (f : FormalGroupHom (F.rescale s) (G.rescale t))
    (y : (G.rescale t).idealPointSubgroup I) :
    y ∈ (f.toIdealPointHom I).range ↔
      ∃ z : I, PowerSeries.coeff 1 f.toPowerSeries • z = G.rescaleLogPointEquiv ht I y := by
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨F.rescaleLogPointEquiv hs I x,
      (f.rescaleLogPointEquiv_toIdealPointHom hs ht I x).symm⟩
  · rintro ⟨z, hz⟩
    refine ⟨(F.rescaleLogPointEquiv hs I).symm z, ?_⟩
    apply (G.rescaleLogPointEquiv ht I).injective
    simpa only [f.rescaleLogPointEquiv_toIdealPointHom hs ht I, AddEquiv.apply_symm_apply]
      using hz

/-- The cokernel index on adic points is the index of scalar multiplication by the tangent
coefficient on the additive ideal. The index convention is Mathlib's, so this identity does
not assert finiteness without further assumptions on the coefficient ring and ideal. -/
theorem index_range_toIdealPointHom
    (f : FormalGroupHom (F.rescale s) (G.rescale t)) :
    (f.toIdealPointHom I).range.index =
      (DistribSMul.toAddMonoidHom I (PowerSeries.coeff 1 f.toPowerSeries)).range.index := by
  have hr : (f.toIdealPointHom I).range.map (G.rescaleLogPointEquiv ht I).toAddMonoidHom =
      (DistribSMul.toAddMonoidHom I (PowerSeries.coeff 1 f.toPowerSeries)).range := by
    ext z
    rw [AddSubgroup.mem_map_equiv, f.mem_range_toIdealPointHom_iff hs ht I,
      AddEquiv.apply_symm_apply]
    rfl
  rw [← hr, AddSubgroup.index_map_of_bijective (G.rescaleLogPointEquiv ht I).bijective]

/-- On a nonzero principal adic ideal in a domain, the cokernel index of a homomorphism
between logarithmically linearised formal groups is the order of the ring modulo its tangent
coefficient. In particular this computes the small-neighbourhood index over a complete DVR. -/
theorem index_range_toIdealPointHom_eq_natCard_quotient [IsDomain R] [I.IsPrincipal]
    (f : FormalGroupHom (F.rescale s) (G.rescale t)) (hI : I ≠ ⊥) :
    (f.toIdealPointHom I).range.index =
      Nat.card (R ⧸ Ideal.span {PowerSeries.coeff 1 f.toPowerSeries}) := by
  rw [f.index_range_toIdealPointHom hs ht I, I.index_range_smul hI]

end Adic

end TauCeti.FormalGroupHom
