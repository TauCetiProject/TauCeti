/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.BaseChange.Basic
public import TauCeti.LinearAlgebra.RootSystem.BaseChange.Balanced.Finite
public import TauCeti.LinearAlgebra.RootSystem.BaseChange.Restrict.Basic
public import TauCeti.LinearAlgebra.RootSystem.Component.Pairing

/-!
# Irreducible components under change of scalars

Injective extension of scalars and restriction to a subfield preserve the non-orthogonality
graph of a root pairing. The induced equivalences of components and their supports retain the
original root indices. In particular, one can decompose an integral root datum on its rational
root and coroot spans and read the integer pairings of each component on the original indices.
This works even when the roots do not span the original lattices.

The graph comparisons use `RootPairing.baseChange_pairing` and
`RootPairing.restrictScalars_pairing`; component and support transport use
`SimpleGraph.Iso.connectedComponentEquiv` and `SimpleGraph.ConnectedComponent.isoEquivSupp`.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Ch. VI, §1, no. 2.
-/

public section

namespace RootPairing

section BaseChange

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] (P : RootPairing ι R M N)
  (S : Type*) [CommRing S] [Algebra R S] [FaithfulSMul R S]
  [Module.Free R N] [Module.Finite R N]

/-- Injective extension of scalars preserves and reflects orthogonality of roots. -/
@[simp]
theorem isOrthogonal_baseChange_iff (i j : ι) :
    (P.baseChange S).IsOrthogonal i j ↔ P.IsOrthogonal i j := by
  simp only [IsOrthogonal, baseChange_pairing,
    map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective R S)]

/-- The identity on root indices identifies the non-orthogonality graphs before and after
injective extension of scalars. -/
def nonorthogonalGraphBaseChangeIso :
    P.nonorthogonalGraph ≃g (P.baseChange S).nonorthogonalGraph where
  toEquiv := Equiv.refl ι
  map_rel_iff' := by simp

@[simp]
theorem nonorthogonalGraphBaseChangeIso_apply (i : ι) :
    P.nonorthogonalGraphBaseChangeIso S i = i :=
  (rfl)

/-- The equivalence of irreducible components under injective extension of scalars. -/
noncomputable def baseChangeComponentEquiv : P.Component ≃ (P.baseChange S).Component :=
  (P.nonorthogonalGraphBaseChangeIso S).connectedComponentEquiv

@[simp]
theorem baseChangeComponentEquiv_componentOf (i : ι) :
    P.baseChangeComponentEquiv S (P.componentOf i) = (P.baseChange S).componentOf i :=
  (rfl)

@[simp]
theorem baseChangeComponentEquiv_symm_componentOf (i : ι) :
    (P.baseChangeComponentEquiv S).symm ((P.baseChange S).componentOf i) = P.componentOf i :=
  (P.baseChangeComponentEquiv S).symm_apply_eq.mpr (by simp)

/-- Extension of scalars does not change the set of indices in a component. -/
@[simp]
theorem supp_baseChangeComponentEquiv (C : P.Component) :
    (P.baseChangeComponentEquiv S C).supp = C.supp := by
  ext i
  simp only [SimpleGraph.ConnectedComponent.mem_supp_iff,
    ← baseChangeComponentEquiv_componentOf, Equiv.apply_eq_iff_eq]

/-- The support equivalence under extension of scalars, preserving the original root indices. -/
noncomputable def baseChangeComponentSupportEquiv (C : P.Component) :
    C.supp ≃ (P.baseChangeComponentEquiv S C).supp :=
  SimpleGraph.ConnectedComponent.isoEquivSupp (P.nonorthogonalGraphBaseChangeIso S) C

@[simp]
theorem coe_baseChangeComponentSupportEquiv (C : P.Component) (i : C.supp) :
    (P.baseChangeComponentSupportEquiv S C i : ι) = i :=
  (rfl)

@[simp]
theorem coe_baseChangeComponentSupportEquiv_symm (C : P.Component)
    (i : (P.baseChangeComponentEquiv S C).supp) :
    ((P.baseChangeComponentSupportEquiv S C).symm i : ι) = i :=
  (rfl)

end BaseChange

section RestrictScalars

variable {ι L M N : Type*} [Field L] [AddCommGroup M] [Module L M]
  [AddCommGroup N] [Module L N] (P : RootPairing ι L M N)
  (K : Type*) [Field K] [Algebra K L] [Module K M] [Module K N]
  [IsScalarTower K L M] [IsScalarTower K L N] [P.IsBalanced] [P.IsValuedIn K]

/-- Restriction to the root and coroot spans over a subfield preserves and reflects
orthogonality of roots. -/
@[simp]
theorem isOrthogonal_restrictScalars_iff (i j : ι) :
    (P.restrictScalars' K).IsOrthogonal i j ↔ P.IsOrthogonal i j := by
  simp only [IsOrthogonal, ← restrictScalars_pairing (P := P) (K := K),
    map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective K L)]

/-- The identity on root indices identifies the non-orthogonality graphs before and after
restriction to the root and coroot spans over a subfield. -/
def nonorthogonalGraphRestrictScalarsIso :
    P.nonorthogonalGraph ≃g (P.restrictScalars' K).nonorthogonalGraph where
  toEquiv := Equiv.refl ι
  map_rel_iff' := by simp

@[simp]
theorem nonorthogonalGraphRestrictScalarsIso_apply (i : ι) :
    P.nonorthogonalGraphRestrictScalarsIso K i = i :=
  (rfl)

/-- The equivalence of components under restriction to the root and coroot spans over a
subfield. -/
noncomputable def restrictScalarsComponentEquiv : P.Component ≃ (P.restrictScalars' K).Component :=
  (P.nonorthogonalGraphRestrictScalarsIso K).connectedComponentEquiv

@[simp]
theorem restrictScalarsComponentEquiv_componentOf (i : ι) :
    P.restrictScalarsComponentEquiv K (P.componentOf i) =
      (P.restrictScalars' K).componentOf i :=
  (rfl)

@[simp]
theorem restrictScalarsComponentEquiv_symm_componentOf (i : ι) :
    (P.restrictScalarsComponentEquiv K).symm ((P.restrictScalars' K).componentOf i) =
      P.componentOf i :=
  (P.restrictScalarsComponentEquiv K).symm_apply_eq.mpr (by simp)

/-- Restriction of scalars does not change the set of indices in a component. -/
@[simp]
theorem supp_restrictScalarsComponentEquiv (C : P.Component) :
    (P.restrictScalarsComponentEquiv K C).supp = C.supp := by
  ext i
  simp only [SimpleGraph.ConnectedComponent.mem_supp_iff,
    ← restrictScalarsComponentEquiv_componentOf, Equiv.apply_eq_iff_eq]

/-- The support equivalence under restriction of scalars, preserving the original root indices. -/
noncomputable def restrictScalarsComponentSupportEquiv (C : P.Component) :
    C.supp ≃ (P.restrictScalarsComponentEquiv K C).supp :=
  SimpleGraph.ConnectedComponent.isoEquivSupp (P.nonorthogonalGraphRestrictScalarsIso K) C

@[simp]
theorem coe_restrictScalarsComponentSupportEquiv (C : P.Component) (i : C.supp) :
    (P.restrictScalarsComponentSupportEquiv K C i : ι) = i :=
  (rfl)

@[simp]
theorem coe_restrictScalarsComponentSupportEquiv_symm (C : P.Component)
    (i : (P.restrictScalarsComponentEquiv K C).supp) :
    ((P.restrictScalarsComponentSupportEquiv K C).symm i : ι) = i :=
  (rfl)

end RestrictScalars

section Rationalization

variable {ι M N : Type*} [AddCommGroup M] [Module ℤ M] [AddCommGroup N] [Module ℤ N]
  (P : RootPairing ι ℤ M N) [Finite ι] [Module.Free ℤ N] [Module.Finite ℤ N]

/-- The components of an integral root pairing are those of the root system on its rational
root and coroot spans. Central directions in the original lattices are allowed. -/
noncomputable def rationalComponentEquiv :
    P.Component ≃ ((P.baseChange ℚ).restrictScalars' ℚ).Component :=
  (P.baseChangeComponentEquiv ℚ).trans ((P.baseChange ℚ).restrictScalarsComponentEquiv ℚ)

@[simp]
theorem rationalComponentEquiv_componentOf (i : ι) :
    P.rationalComponentEquiv (P.componentOf i) =
      ((P.baseChange ℚ).restrictScalars' ℚ).componentOf i := by
  simp [rationalComponentEquiv]

@[simp]
theorem rationalComponentEquiv_symm_componentOf (i : ι) :
    P.rationalComponentEquiv.symm (((P.baseChange ℚ).restrictScalars' ℚ).componentOf i) =
      P.componentOf i :=
  P.rationalComponentEquiv.symm_apply_eq.mpr (by simp)

/-- Rationalization does not change the set of indices in a component. -/
@[simp]
theorem supp_rationalComponentEquiv (C : P.Component) :
    (P.rationalComponentEquiv C).supp = C.supp := by
  simp [rationalComponentEquiv]

/-- The equivalence from an integral component's support to the support of its rational
component, keeping each original root index. -/
noncomputable def rationalComponentSupportEquiv (C : P.Component) :
    C.supp ≃ (P.rationalComponentEquiv C).supp :=
  (P.baseChangeComponentSupportEquiv ℚ C).trans
    ((P.baseChange ℚ).restrictScalarsComponentSupportEquiv ℚ (P.baseChangeComponentEquiv ℚ C))

@[simp]
theorem coe_rationalComponentSupportEquiv (C : P.Component) (i : C.supp) :
    (P.rationalComponentSupportEquiv C i : ι) = i :=
  (rfl)

@[simp]
theorem coe_rationalComponentSupportEquiv_symm (C : P.Component)
    (i : (P.rationalComponentEquiv C).supp) :
    ((P.rationalComponentSupportEquiv C).symm i : ι) = i :=
  (rfl)

/-- Under the transported support, the integer root-coroot pairings in a rational component
are the original integer pairings. No integral splitting of the component lattices is needed. -/
-- The general component and scalar-change pairing lemmas already simplify the left-hand side.
theorem rationalComponentPairing_pairingIn (C : P.Component) (i j : C.supp) :
    (((P.baseChange ℚ).restrictScalars' ℚ).componentPairing (P.rationalComponentEquiv C)).pairingIn
        ℤ (P.rationalComponentSupportEquiv C i) (P.rationalComponentSupportEquiv C j) =
      P.pairingIn ℤ i j := by
  simp only [componentPairing_pairingIn, restrictScalars'_pairingIn, baseChange_pairingIn,
    coe_rationalComponentSupportEquiv]

end Rationalization

end RootPairing
