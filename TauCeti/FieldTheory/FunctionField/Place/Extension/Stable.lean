/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Place.Extension.Galois
public import TauCeti.FieldTheory.IntermediateField.Restrict

/-!
# Restriction of places along a stable intermediate field

Let `E` be an intermediate field of `L / k` carried onto itself by every `k`-automorphism of `L`,
so that automorphisms restrict to `E` through `IntermediateField.restrictAlgEquivHom`. The
restriction of places from `L / k` to `E / k` is then equivariant: the place `σ • Q` lies over
`σ|_E • (Q|_E)`, and the ramification index of `σ • Q` over `E` is that of `Q`. These are the
compatibilities needed to let `Aut(L / k)` act on the places of `E` that ramify in `L`.

These results generalize `TauCeti.Place.restrict_smul` and `TauCeti.Place.ramificationIdx_smul`
of `TauCeti/FieldTheory/FunctionField/Place/Extension/Galois.lean`, which treat automorphisms
fixing `E` pointwise, so that `σ|_E` is the identity there; the proofs follow the same order
computation.

## Main results

* `TauCeti.Place.restrict_smul_of_map_eq`: restriction to `E` is equivariant.
* `TauCeti.Place.ramificationIdx_smul_of_map_eq`: the ramification index over `E` is invariant.
-/

public section

namespace TauCeti.Place

variable {k L : Type*} [Field k] [Field L] [Algebra k L] (E : IntermediateField k L)
  [Algebra.IsIntegral E L] (hE : ∀ σ : L ≃ₐ[k] L, E.map σ.toAlgHom = E) (σ : L ≃ₐ[k] L)
  (Q : Place k L)

/-- The order at `σ • Q` of an element of `E` is `e(Q ∣ E)` times its order at
`σ|_E • (Q|_E)`. -/
theorem ord_smul_algebraMap_of_map_eq (f : E) :
    (σ • Q).ord (algebraMap E L f) =
      ramificationIdx E Q *
        ((IntermediateField.restrictAlgEquivHom E hE σ) • Q.restrict k E).ord f := by
  rw [ord_smul, ord_smul,
    IntermediateField.symm_apply_algebraMap_eq_algebraMap_restrictAlgEquivHom_symm_apply E hE,
    ord_algebraMap_restrict k E Q]

/-- **Restriction of places is equivariant**: `σ • Q` lies over `σ|_E • (Q|_E)`. -/
@[simp]
theorem restrict_smul_of_map_eq :
    (σ • Q).restrict k E = (IntermediateField.restrictAlgEquivHom E hE σ) • Q.restrict k E :=
  (restrict_eq_iff_exists_ord_eq k E (σ • Q) _).mpr
    ⟨ramificationIdx E Q, ramificationIdx_pos E Q, ord_smul_algebraMap_of_map_eq E hE σ Q⟩

include hE in
/-- **The ramification index over a stable intermediate field is invariant** under the
automorphisms of `L / k`. -/
@[simp]
theorem ramificationIdx_smul_of_map_eq : ramificationIdx E (σ • Q) = ramificationIdx E Q :=
  ramificationIdx_eq_of_forall_ord_eq k E (σ • Q) fun f ↦ by
    rw [restrict_smul_of_map_eq E hE, ord_smul_algebraMap_of_map_eq E hE σ Q]

end TauCeti.Place
