/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Scheme.BaseAlgebra
public import TauCeti.AlgebraicGeometry.Scheme.KrullDimension
public import TauCeti.FieldTheory.FunctionField.Basic

/-!
# The function field of an integral scheme of finite type over a field

Let `X` be an integral scheme locally of finite type over a field `k`. The function field `k(X)`
is the fraction field of `Γ(X, U)` for every nonempty affine open `U`, and `Γ(X, U)` is a finitely
generated `k`-algebra. Hence `k(X)` is essentially of finite type over `k`, and its transcendence
degree is the Krull dimension of `Γ(X, U)` (Noether normalization), which is the dimension of `U`,
which is the dimension of `X`:

`dim X = trdeg_k k(X)`.

In particular, `X` is a curve (has dimension one) exactly when `k(X)` is an algebraic function
field of one variable over `k`. This is what lets the function-field theory (places, repartitions,
Weil differentials, the Riemann–Roch theorem of function fields) be applied to integral curves.

## Main declarations

* `TauCeti.AlgebraicGeometry.essFiniteType_functionField`: `k(X)` is essentially of finite
  type over `k`;
* `TauCeti.AlgebraicGeometry.topologicalKrullDim_eq_toNat_trdeg_functionField`:
  `dim X = trdeg_k k(X)`;
* `TauCeti.AlgebraicGeometry.isFunctionField_functionField_iff`: `k(X)` is an algebraic
  function field over `k` if and only if `X` has dimension one.

## References

* R. Hartshorne, *Algebraic Geometry*, Chapter I, Proposition 1.8A and Exercise II.3.20.
* [Stacks Project, Tag 00P0](https://stacks.math.columbia.edu/tag/00P0) (dimension and
  transcendence degree of finitely generated domains)
-/

public section

open CategoryTheory AlgebraicGeometry

namespace TauCeti

namespace AlgebraicGeometry

universe u

variable (k : Type u) [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))] [IsIntegral X]
  [LocallyOfFiniteType (X ↘ Spec (.of k))]

/-- An integral scheme locally of finite type over `k` has a finitely generated `k`-algebra with
fraction field `k(X)` and Krull dimension `dim X`: the sections over any nonempty affine open. -/
private lemma exists_finiteType_isFractionRing_functionField :
    ∃ (A : Type u) (_ : CommRing A) (_ : IsDomain A) (_ : Algebra k A)
      (_ : Algebra A X.functionField) (_ : IsScalarTower k A X.functionField)
      (_ : Algebra.FiniteType k A) (_ : IsFractionRing A X.functionField),
      topologicalKrullDim X = ringKrullDim A := by
  obtain ⟨x⟩ : Nonempty X := inferInstance
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have : Nonempty U := ⟨⟨x, hxU⟩⟩
  have : Nonempty (⊤ : X.Opens) := ⟨⟨x, trivial⟩⟩
  -- The base ring maps to `Γ(X, U)` through `Γ(Spec k, ⊤)`.
  let φ : k →+* Γ(X, U) :=
    ((X ↘ Spec (.of k)).appLE ⊤ U le_top).hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom
  let _ : Algebra k Γ(X, U) := φ.toAlgebra
  have hft : Algebra.FiniteType k Γ(X, U) := by
    refine RingHom.FiniteType.comp
      (HasRingHomProperty.appLE @LocallyOfFiniteType (X ↘ Spec (.of k)) inferInstance
        ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ le_top) ?_
    exact RingHom.FiniteType.of_surjective _
      (Scheme.ΓSpecIso (.of k)).symm.commRingCatIsoToRingEquiv.surjective
  have htower : IsScalarTower k Γ(X, U) X.functionField := by
    apply IsScalarTower.of_algebraMap_eq'
    ext c
    have h : (X ↘ Spec (.of k)).appLE ⊤ U le_top ≫ X.germToFunctionField U =
        (X ↘ Spec (.of k)).appTop ≫ X.germToFunctionField ⊤ := by
      simp only [Scheme.Hom.appLE, Category.assoc, TopCat.Presheaf.germ_res]
      -- What remains compares germs on `(X ↘ Spec k) ⁻¹ᵁ ⊤` and on `⊤`, which are the same open
      -- by definition; rewriting along `Scheme.Hom.preimage_top` would need to transport the
      -- membership proof inside `germ`.
      rfl
    have := congrArg (fun f ↦ f ((Scheme.ΓSpecIso (.of k)).inv c)) h
    simpa [φ, RingHom.algebraMap_toAlgebra] using this.symm
  refine ⟨Γ(X, U), inferInstance, inferInstance, inferInstance, inferInstance, htower, hft,
    functionField_isFractionRing_of_isAffineOpen X U hU, ?_⟩
  -- The nonempty open `U` of the irreducible space `X` has the dimension of `X`, and `U` is
  -- homeomorphic to `Spec Γ(X, U)`.
  have hdim := topologicalKrullDim_inter_eq_of_locallyOfFiniteType (X ↘ Spec (.of k))
    (IrreducibleSpace.isIrreducible_univ X) isClosed_univ U.isOpen ⟨x, trivial, hxU⟩
  rw [Set.univ_inter] at hdim
  rw [(Homeomorph.Set.univ X).symm.isHomeomorph.topologicalKrullDim_eq, ← hdim]
  exact (IsAffineOpen.isoSpec hU).hom.homeomorph.isHomeomorph.topologicalKrullDim_eq.trans
    (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim _)

/-- The function field of an integral scheme locally of finite type over a field `k` is
essentially of finite type over `k`: it is a localization of a finitely generated `k`-algebra. -/
instance essFiniteType_functionField : Algebra.EssFiniteType k X.functionField := by
  obtain ⟨A, _, _, _, _, _, _, _, -⟩ := exists_finiteType_isFractionRing_functionField k (X := X)
  have : Algebra.EssFiniteType A X.functionField :=
    .of_isLocalization X.functionField (nonZeroDivisors A)
  exact .comp k A X.functionField

/-- **Dimension is transcendence degree.** An integral scheme locally of finite type over a field
`k` has dimension the transcendence degree of its function field over `k`. -/
theorem topologicalKrullDim_eq_toNat_trdeg_functionField :
    topologicalKrullDim X = (Algebra.trdeg k X.functionField).toNat := by
  obtain ⟨A, _, _, _, _, _, _, _, hdim⟩ := exists_finiteType_isFractionRing_functionField k (X := X)
  have : FaithfulSMul A X.functionField :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (IsFractionRing.injective A _)
  have := IsLocalization.isAlgebraic X.functionField (nonZeroDivisors A)
  rw [hdim, ringKrullDim_eq_toNat_trdeg k A, ← trdeg_add_eq k A (A := X.functionField),
    trdeg_eq_zero (R := A), add_zero]

/-- **Curves have algebraic function fields.** An integral scheme locally of finite type over a
field `k` has dimension one exactly when its function field is an algebraic function field of one
variable over `k`. -/
theorem isFunctionField_functionField_iff :
    IsFunctionField k X.functionField ↔ topologicalKrullDim X = 1 := by
  rw [isFunctionField_iff_trdeg_eq_one, topologicalKrullDim_eq_toNat_trdeg_functionField k,
    Nat.cast_eq_one, Cardinal.toNat_eq_one]

end AlgebraicGeometry

end TauCeti
