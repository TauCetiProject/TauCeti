/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.NodalGluing.RingedSpace
public import TauCeti.Geometry.Manifold.Complex.StructureSheaf.Domain

/-!
# Intrinsic recognition of nodes

For a curve glued from complex one-dimensional manifolds, the node set is determined by the
holomorphic structure sheaf: a point is smooth exactly when its stalk is an integral domain.
At a node, the two nonzero branch coordinates multiply to zero. Away from the nodes, the
stalk is the holomorphic stalk of the normalization, which is a domain by the identity theorem.

Consequently a map inducing an isomorphism on stalks preserves and reflects nodes. In
particular, an isomorphism of the holomorphic sheafed spaces needs no additional hypothesis
that it preserve the designated node sets. This supplies the intrinsic node recognition needed
when lifting ringed isomorphisms to the normalizations.

The proof uses the existing `quotientStalkToNodeEquiv`, `quotientStalkBranchEquiv`,
`holomorphicStructureSheaf.nodeLocalRing.not_isDomain` and
`holomorphicStructureSheaf.stalkIsDomain`.

## References

* Otto Forster, *Lectures on Riemann Surfaces*, §§1 and 6, for holomorphic local rings.
* Joel W. Robbin and Dietmar A. Salamon, *A construction of the Deligne–Mumford orbifold*,
  J. Eur. Math. Soc. 8 (2006), 611–699, for normalization and nodal isomorphisms.
-/

public noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped Manifold

namespace TauCeti.NodalGluing

open holomorphicStructureSheaf

variable {ι Flag : Type} {X : ι → Type} [∀ i, TopologicalSpace (X i)]
  [∀ i, ChartedSpace ℂ (X i)] [∀ i, IsManifold 𝓘(ℂ) 1 (X i)]
  [∀ i, T2Space (X i)] [Finite Flag] (d : FlagPairData ι Flag X)

/-- A point of the normalization quotient is not a node exactly when its holomorphic stalk
is an integral domain. No compactness or connectedness assumption is needed. -/
@[simp]
theorem isDomain_quotientStalk_iff (z : GluedCurve d) :
    IsDomain ((quotientSheaf 𝓘(ℂ) (gluedRelSetoid d)).presheaf.stalk z) ↔ z ∉ nodeSet d := by
  constructor
  · intro h hz
    obtain ⟨f, rfl⟩ := (mem_nodeSet d z).mp hz
    let := h
    let := (quotientStalkToNodeEquiv 𝓘(ℂ) d f).symm.toMulEquiv.isDomain
    exact nodeLocalRing.not_isDomain (p := fstPoint d f) (q := sndPoint d f) inferInstance
  · intro hz
    obtain ⟨x, rfl⟩ := Quotient.mk_surjective z
    have hx : x ∉ flagPointSet d := by
      simpa only [← preimage_nodeSet d, Set.mem_preimage] using hz
    exact (quotientStalkBranchEquiv 𝓘(ℂ) d hx).toMulEquiv.isDomain

variable {ι' Flag' : Type} {X' : ι' → Type} [∀ i, TopologicalSpace (X' i)]
  [∀ i, ChartedSpace ℂ (X' i)] [∀ i, IsManifold 𝓘(ℂ) 1 (X' i)]
  [∀ i, T2Space (X' i)] [Finite Flag'] {d' : FlagPairData ι' Flag' X'}

/-- Any sheafed-space map inducing an isomorphism on the stalk at a point preserves and
reflects whether that point is a node. In particular this applies to every sheafed-space
isomorphism, without a node-preservation hypothesis. -/
theorem mem_nodeSet_iff_of_isIso_stalkMap
    (f : sheafedSpace 𝓘(ℂ) d ⟶ sheafedSpace 𝓘(ℂ) d') (z : GluedCurve d)
    [IsIso (f.hom.stalkMap z)] : f.hom.base z ∈ nodeSet d' ↔ z ∈ nodeSet d := by
  have h := (asIso (f.hom.stalkMap z)).commRingCatIsoToRingEquiv.toMulEquiv.isDomain_iff
  simpa only [isDomain_quotientStalk_iff, not_not] using not_congr h

end TauCeti.NodalGluing
