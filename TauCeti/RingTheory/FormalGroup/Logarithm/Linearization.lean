/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.FormalGroup.Logarithm.AdicPoint
import TauCeti.RingTheory.Ideal.IsPrincipal

/-!
# Integral logarithms linearise homomorphisms on ideal points

Suppose `n + 1` divides `sⁿ` in a commutative ring without additive torsion. The integral
logarithm of `F.rescale s` conjugates homomorphisms to multiplication by their linear
coefficient. Source and target may be rescaled by different amounts.

On an ideal of topologically nilpotent elements in a complete Hausdorff linearly topologized
ring, evaluating these logarithms gives the same conjugacy between group homomorphisms. The image
and cokernel of a homomorphism on a sufficiently small neighbourhood can be computed using scalar
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

section IdealPoints

variable [UniformSpace R] [IsUniformAddGroup R] [CompleteSpace R] [T2Space R]
  [IsTopologicalRing R] [IsLinearTopology R R]
  (I : Ideal R) (hI : ∀ x ∈ I, IsTopologicallyNilpotent x)

/-- The evaluated integral logarithms conjugate a homomorphism on ideal points to scalar
multiplication on the ideal by its linear coefficient. -/
@[simp]
theorem rescaleLogPointEquiv_toIdealPointHom
    (f : FormalGroupHom (F.rescale s) (G.rescale t))
    (x : (F.rescale s).idealPointSubgroup I) :
    G.rescaleLogPointEquiv ht I hI (f.toIdealPointHom I x) =
      PowerSeries.coeff 1 f.toPowerSeries • F.rescaleLogPointEquiv hs I hI x := by
  apply Subtype.ext
  have h := ((G.rescaleLogHom ht).comp f).hasSum_val_toTopNilpotentPointHom x.val
  have hseries := f.subst_rescaleLog hs ht
  rw [comp_toPowerSeries, rescaleLogHom_toPowerSeries, hseries] at h
  have hlog := (F.rescaleLogHom hs).hasSum_val_toTopNilpotentPointHom x.val
  have hmul := hlog.mul_left (PowerSeries.coeff 1 f.toPowerSeries)
  have heq := h.unique (by
    simpa only [PowerSeries.coeff_smul, rescaleLogHom_toPowerSeries, smul_eq_mul,
      mul_assoc] using hmul)
  rw [toTopNilpotentPointHom_comp, AddMonoidHom.comp_apply,
    val_rescaleLogHom_toTopNilpotentPointHom,
    val_rescaleLogHom_toTopNilpotentPointHom] at heq
  simpa only [coe_rescaleLogPointEquiv, coe_toIdealPointHom,
    Submodule.coe_smul, smul_eq_mul] using heq

include hs ht hI

/-- A point is in the image exactly when its logarithm is a scalar multiple, inside the ideal,
of the linear coefficient. This includes noninvertible tangent maps. -/
theorem mem_range_toIdealPointHom_iff
    (f : FormalGroupHom (F.rescale s) (G.rescale t))
    (y : (G.rescale t).idealPointSubgroup I) :
    y ∈ (f.toIdealPointHom I).range ↔
      ∃ z : I, PowerSeries.coeff 1 f.toPowerSeries • z =
        G.rescaleLogPointEquiv ht I hI y := by
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨F.rescaleLogPointEquiv hs I hI x,
      (f.rescaleLogPointEquiv_toIdealPointHom hs ht I hI x).symm⟩
  · rintro ⟨z, hz⟩
    refine ⟨(F.rescaleLogPointEquiv hs I hI).symm z, ?_⟩
    apply (G.rescaleLogPointEquiv ht I hI).injective
    simpa only [f.rescaleLogPointEquiv_toIdealPointHom hs ht I hI, AddEquiv.apply_symm_apply]
      using hz

/-- The cokernel index on ideal points is the index of scalar multiplication by the tangent
coefficient on the additive ideal. The index convention is Mathlib's, so this identity does
not assert finiteness without further assumptions on the coefficient ring and ideal. -/
theorem index_range_toIdealPointHom
    (f : FormalGroupHom (F.rescale s) (G.rescale t)) :
    (f.toIdealPointHom I).range.index =
      (DistribSMul.toAddMonoidHom I (PowerSeries.coeff 1 f.toPowerSeries)).range.index := by
  have hr : (f.toIdealPointHom I).range.map (G.rescaleLogPointEquiv ht I hI).toAddMonoidHom =
      (DistribSMul.toAddMonoidHom I (PowerSeries.coeff 1 f.toPowerSeries)).range := by
    ext z
    rw [AddSubgroup.mem_map_equiv, f.mem_range_toIdealPointHom_iff hs ht I hI,
      AddEquiv.apply_symm_apply]
    simp only [AddMonoidHom.mem_range, DistribSMul.toAddMonoidHom_apply]
  rw [← hr, AddSubgroup.index_map_of_bijective (G.rescaleLogPointEquiv ht I hI).bijective]

/-- On a nonzero principal ideal of topologically nilpotent elements in a domain, the
cokernel index of a logarithmically linearised homomorphism is the cardinality of the ring
modulo its tangent coefficient. This applies to nonzero proper ideals of a complete DVR
without additive torsion when the two rescalings satisfy the divisibility hypotheses. -/
theorem index_range_toIdealPointHom_eq_natCard_quotient [IsDomain R] [I.IsPrincipal]
    (f : FormalGroupHom (F.rescale s) (G.rescale t)) (hne : I ≠ ⊥) :
    (f.toIdealPointHom I).range.index =
      Nat.card (R ⧸ Ideal.span {PowerSeries.coeff 1 f.toPowerSeries}) := by
  rw [f.index_range_toIdealPointHom hs ht I hI, I.index_range_smul hne]

end IdealPoints

end TauCeti.FormalGroupHom
