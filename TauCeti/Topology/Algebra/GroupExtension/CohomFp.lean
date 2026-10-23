/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.TrivialFp.Explicit
public import TauCeti.Topology.Algebra.GroupExtension.Cohomology

/-!
# The class of a profinite extension by `𝔽_p` in `H²(G, 𝔽_p)`

The extension dictionary of `TauCeti/Topology/Algebra/GroupExtension/Cohomology.lean` classifies the
profinite extensions of a topological group `G` by a compact module `M` through the explicit
continuous cohomology group `H²(G, M)` of `TauCeti.ContCohomology`. The cohomology every dimension
count of the pro-`p` theory is stated on is instead Mathlib's `continuousCohomology` of the trivial
`𝔽_p`-representation, `TauCeti.cohomFp p G 2`, and the two are identified by
`TauCeti.cohomFpAddEquivH2Additive` for any trivial action of `G` on the multiplicatively written
`𝔽_p`. This file reads the class of a profinite extension of `G` by `𝔽_p`, on which `G` acts
trivially, in `cohomFp p G 2`, so that the extensions by `𝔽_p` and the cup products of classes of
`H¹(G, 𝔽_p)` live in one group. The class vanishes exactly when the extension has a continuous
homomorphic section, and two extensions have the same class exactly when they are continuously
equivalent, and for profinite `G` every class is the class of an extension, so that the class is a
bijection from the extensions modulo continuous equivalence onto `cohomFp p G 2`; these are the
theorems of the dictionary transported along the identification.

## Main declarations

* `TauCeti.ProfiniteGroupExtension.cohomFpClass`: **the class in `H²(G, 𝔽_p)` of a profinite
  extension of `G` by `𝔽_p`.**
* `TauCeti.ProfiniteGroupExtension.cohomFpClass_eq_zero_iff`: the class vanishes exactly when the
  extension has a continuous homomorphic section.
* `TauCeti.ProfiniteGroupExtension.exists_equiv_continuous_iff_cohomFpClass_eq`: two extensions are
  continuously equivalent exactly when their classes agree.
* `TauCeti.ProfiniteGroupExtension.exists_cohomFpClass_eq` and
  `TauCeti.ProfiniteGroupExtension.cohomFpClassEquiv`: for profinite `G`, every class is the class
  of an extension, and the class is a bijection from the extensions modulo continuous equivalence
  onto `cohomFp p G 2`.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Springer (2008),
  Ch. I, §2.
-/

public section

namespace TauCeti

open ContCohomology

universe u

variable {p : ℕ} {G : Type u} [Group G] [MulDistribMulAction G (Multiplicative (ZMod p))]
  (htriv : ∀ (g : G) (m : Multiplicative (ZMod p)), g • m = m)
include htriv

variable [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [hcont : ContinuousSMul G (Multiplicative (ZMod p))]

namespace ProfiniteGroupExtension

variable [NeZero p] [T2Space G] (X Y : ProfiniteGroupExtension G (Multiplicative (ZMod p)))

/-- **The class in `H²(G, 𝔽_p)` of a profinite extension of `G` by `𝔽_p`** with trivial action:
its class in the explicit continuous cohomology,
`TauCeti.ProfiniteGroupExtension.contCohomologyClass`, read in Mathlib's continuous cohomology of
the trivial `𝔽_p`-representation. -/
noncomputable def cohomFpClass : cohomFp p G 2 :=
  (cohomFpAddEquivH2Additive p G htriv).symm X.contCohomologyClass

theorem cohomFpClass_def :
    X.cohomFpClass htriv = (cohomFpAddEquivH2Additive p G htriv).symm X.contCohomologyClass :=
  (rfl)

/-- The class of a profinite extension by `𝔽_p` in `H²(G, 𝔽_p)` is its class in the explicit
continuous cohomology, under the identification `TauCeti.cohomFpAddEquivH2Additive`. -/
@[simp]
theorem cohomFpAddEquivH2Additive_cohomFpClass :
    cohomFpAddEquivH2Additive p G htriv (X.cohomFpClass htriv) = X.contCohomologyClass :=
  (cohomFpAddEquivH2Additive p G htriv).apply_symm_apply _

/-- **A profinite extension by `𝔽_p` has a continuous homomorphic section exactly when its class in
`H²(G, 𝔽_p)` vanishes.** -/
theorem cohomFpClass_eq_zero_iff :
    X.cohomFpClass htriv = 0 ↔ ∃ s : X.toGroupExtension.Splitting, Continuous ⇑s := by
  rw [cohomFpClass_def, map_eq_zero_iff _ (cohomFpAddEquivH2Additive p G htriv).symm.injective,
    contCohomologyClass_def,
    ← X.toGroupExtension.exists_splitting_continuous_iff_contCohomologyClass_eq_zero]

/-- **Two profinite extensions by `𝔽_p` are continuously equivalent exactly when their classes in
`H²(G, 𝔽_p)` agree.** -/
theorem exists_equiv_continuous_iff_cohomFpClass_eq :
    (∃ e : X.toGroupExtension.Equiv Y.toGroupExtension, Continuous ⇑e) ↔
      X.cohomFpClass htriv = Y.cohomFpClass htriv := by
  rw [cohomFpClass_def, cohomFpClass_def,
    (cohomFpAddEquivH2Additive p G htriv).symm.injective.eq_iff,
    exists_equiv_continuous_iff_contCohomologyClass_eq]

section Realization

variable [CompactSpace G] [TotallyDisconnectedSpace G]

/-- **Every class of `H²(G, 𝔽_p)` is the class of a profinite extension of `G` by `𝔽_p`** with
trivial action: `TauCeti.ProfiniteGroupExtension.exists_contCohomologyClass_eq` read on
`cohomFp p G 2`. -/
theorem exists_cohomFpClass_eq (c : cohomFp p G 2) :
    ∃ X : ProfiniteGroupExtension G (Multiplicative (ZMod p)), X.cohomFpClass htriv = c := by
  obtain ⟨X, hX⟩ := exists_contCohomologyClass_eq (cohomFpAddEquivH2Additive p G htriv c)
  exact ⟨X, by rw [cohomFpClass_def, hX, AddEquiv.symm_apply_apply]⟩

/-- **`H²(G, 𝔽_p)` classifies the profinite extensions of `G` by `𝔽_p`** with trivial action: the
class descends to a bijection from those extensions modulo continuous equivalence onto
`cohomFp p G 2`, the bijection `TauCeti.ProfiniteGroupExtension.contCohomologyClassEquiv` read on
`cohomFp p G 2`. -/
noncomputable def cohomFpClassEquiv :
    Quotient (continuousEquivSetoid G (Multiplicative (ZMod p))) ≃ cohomFp p G 2 :=
  (contCohomologyClassEquiv G (Multiplicative (ZMod p))).trans
    (cohomFpAddEquivH2Additive p G htriv).symm.toEquiv

@[simp]
theorem cohomFpClassEquiv_apply_mk (X : ProfiniteGroupExtension G (Multiplicative (ZMod p))) :
    cohomFpClassEquiv htriv (Quotient.mk _ X) = X.cohomFpClass htriv := by
  rw [cohomFpClassEquiv, Equiv.trans_apply, contCohomologyClassEquiv_apply_mk]
  rfl

end Realization

end ProfiniteGroupExtension

end TauCeti
