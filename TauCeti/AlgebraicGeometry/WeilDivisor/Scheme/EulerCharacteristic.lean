/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.LineBundle.Degree
public import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.Degree
public import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.ResidueSequence
public import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.RiemannRoch.Space

/-!
# The Euler characteristic of `𝒪_X(D)` and the degree of a line bundle

Let `X` be a Noetherian integral scheme over a field `k` whose codimension-one local rings are
discrete valuation rings, and whose codimension-one points are closed with finite residue fields
over `k`. Adding a point `y` to a Weil divisor `D` changes the Euler characteristic by the residue
degree `[κ(y) : k]` (`SchemeWeilDivisor.eulerCharBelow_sheaf_add_ofPoint`). Inducting over the
divisor gives

`χ(𝒪_X(D)) = deg D + χ(𝒪_X)`,

where `deg D = Σ_y D(y) [κ(y) : k]` is `SchemeWeilDivisor.relativeDegree (X ↘ Spec k)` and
`χ(M) = dim H⁰(X, M) - dim H¹(X, M)`. The same induction shows that whether `Hⁱ(X, 𝒪_X(D))` is
finite-dimensional does not depend on `D`, so the only finiteness input needed is that of the
cohomology of `𝒪_X` itself.

On a proper curve over `k`, `H⁰` is always finite-dimensional
(`SchemeWeilDivisor.finiteDimensional_cohomology_zero_sheaf`) and every line bundle is some
`𝒪_X(D)` (`SchemeWeilDivisor.exists_nonempty_iso_sheaf`). As soon as `H¹(X, 𝒪_X)` is
finite-dimensional, the Euler-characteristic degree `χ(L) - χ(𝒪_X)` of a line bundle therefore
agrees with the degree of any divisor of `L`, and is additive under tensor product.

## Main declarations

* `SchemeWeilDivisor.finiteDimensional_cohomology_sheaf_iff`: `Hⁱ(X, 𝒪_X(D))` is
  finite-dimensional exactly when `Hⁱ(X, 𝒪_X(E))` is;
* `SchemeWeilDivisor.eulerCharBelow_sheaf_eq_relativeDegree_add`: `χ(𝒪_X(D)) = deg D + χ(𝒪_X)`;
* `SchemeWeilDivisor.relativeDegree_eq_of_linearlyEquivalent` and
  `SchemeWeilDivisor.relativeDegree_principalDivisor`: the degree is a linear-equivalence
  invariant, and a principal divisor has degree zero;
* `SchemeWeilDivisor.finiteDimensional_cohomology_one_sheaf` and
  `InvertibleSheaf.finiteDimensional_cohomology_one`: on a proper curve with `H¹(X, 𝒪_X)`
  finite-dimensional, `H¹` of every `𝒪_X(D)` and of every line bundle is finite-dimensional;
* `InvertibleSheaf.eulerDegree_eq_relativeDegree` and
  `LineBundleClass.eulerDegree_toLineBundleClass`: the Euler-characteristic degree of `𝒪_X(D)` is
  `deg D`;
* `LineBundleClass.eulerDegree_mul`: the Euler-characteristic degree is additive under tensor
  product.

## References

* R. Hartshorne, *Algebraic Geometry*, IV, Theorem 1.3 and its proof.
* J.-P. Serre, *Algebraic Groups and Class Fields*, Chapter II, §3.
-/

public section

open CategoryTheory AlgebraicGeometry Order

namespace TauCeti

namespace AlgebraicGeometry

universe u

namespace SchemeWeilDivisor

variable {X : Scheme.{u}} [IsIntegral X]
  [∀ y : CodimensionOnePoint X, IsDiscreteValuationRing (X.presheaf.stalk (y : X))]
  (k : Type u) [Field k] [X.Over (Spec (.of k))]

section Noetherian

variable [IsNoetherian X]

/-- Adding an integer multiple of a closed point of finite degree does not change whether
`Hⁱ(X, 𝒪_X(E))` is finite-dimensional. -/
private lemma finiteDimensional_cohomology_sheaf_add_zsmul_ofPoint_iff {y : CodimensionOnePoint X}
    (hclosed : IsClosed ({(y : X)} : Set X)) (hy : (X ↘ Spec (.of k)).residueDegree y ≠ 0)
    (i : ℕ) (E : SchemeWeilDivisor X) (n : ℤ) :
    FiniteDimensional k
        (Scheme.Modules.Cohomology (sheaf (E + n • WeilDivisor.ofPoint y)) i) ↔
      FiniteDimensional k (Scheme.Modules.Cohomology (sheaf E) i) := by
  induction n using Int.induction_on with
  | zero => rw [zero_smul, add_zero]
  | succ n ih =>
    rw [add_one_zsmul, ← add_assoc,
      finiteDimensional_cohomology_sheaf_add_ofPoint_iff k hclosed hy i, ih]
  | pred n ih =>
    rw [← ih, ← finiteDimensional_cohomology_sheaf_add_ofPoint_iff k hclosed hy i, add_assoc,
      ← add_one_zsmul, sub_add_cancel]

/-- **Finite-dimensionality of `Hⁱ(X, 𝒪_X(D))` does not depend on `D`.** If every
codimension-one point of `X` is closed with finite residue field over `k`, then `Hⁱ(X, 𝒪_X(D))`
is finite-dimensional exactly when `Hⁱ(X, 𝒪_X(E))` is. -/
theorem finiteDimensional_cohomology_sheaf_iff
    (hclosed : ∀ y : CodimensionOnePoint X, IsClosed ({(y : X)} : Set X))
    (hdeg : ∀ y : CodimensionOnePoint X, (X ↘ Spec (.of k)).residueDegree y ≠ 0) (i : ℕ)
    (D E : SchemeWeilDivisor X) :
    FiniteDimensional k (Scheme.Modules.Cohomology (sheaf D) i) ↔
      FiniteDimensional k (Scheme.Modules.Cohomology (sheaf E) i) := by
  suffices h : ∀ D : SchemeWeilDivisor X,
      FiniteDimensional k (Scheme.Modules.Cohomology (sheaf D) i) ↔
        FiniteDimensional k (Scheme.Modules.Cohomology (sheaf (0 : SchemeWeilDivisor X)) i) from
    (h D).trans (h E).symm
  intro D
  induction D using Finsupp.induction with
  | zero => exact Iff.rfl
  | single_add a b f _ _ ih =>
    rw [add_comm, WeilDivisor.single_eq_zsmul_ofPoint,
      finiteDimensional_cohomology_sheaf_add_zsmul_ofPoint_iff k (hclosed a) (hdeg a), ih]

/-- Adding `n` times a closed point `y` of finite degree changes the Euler characteristic of
`𝒪_X(E)` by `n [κ(y) : k]`, provided every `𝒪_X(E')` has finite-dimensional `H⁰` and `H¹`. -/
private lemma eulerCharBelow_sheaf_add_zsmul_ofPoint {y : CodimensionOnePoint X}
    (hclosed : IsClosed ({(y : X)} : Set X)) (hy : (X ↘ Spec (.of k)).residueDegree y ≠ 0)
    (hfd₀ : ∀ E : SchemeWeilDivisor X,
      FiniteDimensional k (Scheme.Modules.Cohomology (sheaf E) 0))
    (hfd₁ : ∀ E : SchemeWeilDivisor X,
      FiniteDimensional k (Scheme.Modules.Cohomology (sheaf E) 1))
    (E : SchemeWeilDivisor X) (n : ℤ) :
    Scheme.Modules.eulerCharBelow k X (sheaf (E + n • WeilDivisor.ofPoint y)) 2 =
      Scheme.Modules.eulerCharBelow k X (sheaf E) 2 +
        n * (X ↘ Spec (.of k)).residueDegree y := by
  induction n using Int.induction_on with
  | zero => rw [zero_smul, add_zero, zero_mul, add_zero]
  | succ n ih =>
    rw [add_one_zsmul, ← add_assoc,
      eulerCharBelow_sheaf_add_ofPoint k hclosed hy (hD₀ := hfd₀ _) (hD₁ := hfd₁ _), ih]
    ring
  | pred n ih =>
    have h := eulerCharBelow_sheaf_add_ofPoint k hclosed hy
      (D := E + (-(n : ℤ) - 1) • WeilDivisor.ofPoint y) (hD₀ := hfd₀ _) (hD₁ := hfd₁ _)
    rw [add_assoc, ← add_one_zsmul, sub_add_cancel, ih] at h
    linear_combination -h

/-- **`χ(𝒪_X(D)) = deg D + χ(𝒪_X(0))`.** Let `X` be a Noetherian integral scheme over a field `k`
whose codimension-one local rings are discrete valuation rings and whose codimension-one points
are closed with finite residue fields over `k`. If `H⁰(X, 𝒪_X(0))` and `H¹(X, 𝒪_X(0))` are
finite-dimensional, then for every Weil divisor `D`

`χ(𝒪_X(D)) = Σ_y D(y) [κ(y) : k] + χ(𝒪_X(0))`,

where `χ(M) = dim H⁰(X, M) - dim H¹(X, M)`. -/
theorem eulerCharBelow_sheaf_eq_relativeDegree_add_sheaf_zero
    (hclosed : ∀ y : CodimensionOnePoint X, IsClosed ({(y : X)} : Set X))
    (hdeg : ∀ y : CodimensionOnePoint X, (X ↘ Spec (.of k)).residueDegree y ≠ 0)
    [FiniteDimensional k (Scheme.Modules.Cohomology (sheaf (0 : SchemeWeilDivisor X)) 0)]
    [FiniteDimensional k (Scheme.Modules.Cohomology (sheaf (0 : SchemeWeilDivisor X)) 1)]
    (D : SchemeWeilDivisor X) :
    Scheme.Modules.eulerCharBelow k X (sheaf D) 2 =
      relativeDegree (X ↘ Spec (.of k)) D +
        Scheme.Modules.eulerCharBelow k X (sheaf (0 : SchemeWeilDivisor X)) 2 := by
  have hfd (i : ℕ) [FiniteDimensional k
      (Scheme.Modules.Cohomology (sheaf (0 : SchemeWeilDivisor X)) i)] (E : SchemeWeilDivisor X) :
      FiniteDimensional k (Scheme.Modules.Cohomology (sheaf E) i) :=
    (finiteDimensional_cohomology_sheaf_iff k hclosed hdeg i E 0).mpr inferInstance
  induction D using Finsupp.induction with
  | zero => rw [map_zero, zero_add]
  | single_add a b f _ _ ih =>
    rw [add_comm, WeilDivisor.single_eq_zsmul_ofPoint,
      eulerCharBelow_sheaf_add_zsmul_ofPoint k (hclosed a) (hdeg a) (hfd 0) (hfd 1), ih, map_add,
      map_zsmul, relativeDegree_ofPoint, smul_eq_mul]
    ring

end Noetherian

section Curve

variable [IsLocallyNoetherian X] [IsProper (X ↘ Spec (.of k))]

omit [IsIntegral X]
  [∀ y : CodimensionOnePoint X, IsDiscreteValuationRing (X.presheaf.stalk (y : X))] in
/-- On a proper curve over `k`, codimension-one points are closed of finite degree over `k`, and
`X` is Noetherian. -/
private lemma isNoetherian_and_isClosed_and_residueDegree_ne_zero
    (hX : ∀ y : X, coheight y ≤ 1) :
    IsNoetherian X ∧ (∀ y : CodimensionOnePoint X, IsClosed ({(y : X)} : Set X)) ∧
      ∀ y : CodimensionOnePoint X, (X ↘ Spec (.of k)).residueDegree y ≠ 0 := by
  have : CompactSpace X := (quasiCompact_iff_compactSpace (X ↘ Spec (.of k))).mp inferInstance
  have hclosed (y : CodimensionOnePoint X) : IsClosed ({(y : X)} : Set X) :=
    isClosed_singleton_of_forall_coheight_le_one_of_coheight_eq_one hX y.property
  exact ⟨{}, hclosed, fun y ↦
    Scheme.Hom.residueDegree_ne_zero_of_isClosed _ (hclosed y)⟩

omit [∀ y : CodimensionOnePoint X, IsDiscreteValuationRing (X.presheaf.stalk (y : X))] in
/-- On a curve, `𝒪_X(0)` is the trivial line bundle `𝒪_X`. -/
private noncomputable def sheafZeroIsoTrivial (hX : ∀ y : X, coheight y ≤ 1) :
    sheaf (0 : SchemeWeilDivisor X) ≅ (InvertibleSheaf.trivial X).obj :=
  (unitIsoSheafZero hX).symm ≪≫ (TauCeti.SheafOfModules.freePUnitIsoUnit X.ringCatSheaf).symm ≪≫
    eqToIso (InvertibleSheaf.trivial_obj X).symm

/-- **`H¹(X, 𝒪_X(D))` is finite-dimensional once `H¹(X, 𝒪_X)` is.** On a proper integral curve
over a field `k` whose codimension-one local rings are discrete valuation rings, if
`H¹(X, 𝒪_X)` is finite-dimensional over `k`, then so is `H¹(X, 𝒪_X(D))` for every Weil
divisor `D`. -/
theorem finiteDimensional_cohomology_one_sheaf (hX : ∀ y : X, coheight y ≤ 1)
    [FiniteDimensional k
      (Scheme.Modules.Cohomology (InvertibleSheaf.trivial X).obj 1)]
    (D : SchemeWeilDivisor X) :
    FiniteDimensional k (Scheme.Modules.Cohomology (sheaf D) 1) := by
  obtain ⟨_, hclosed, hdeg⟩ := isNoetherian_and_isClosed_and_residueDegree_ne_zero k hX
  refine (finiteDimensional_cohomology_sheaf_iff k hclosed hdeg 1 D 0).mpr ?_
  exact (Scheme.Modules.finiteDimensional_cohomology_congr k (sheafZeroIsoTrivial hX) 1).mpr
    inferInstance

/-- **`χ(𝒪_X(D)) = deg D + χ(𝒪_X)`.** On a proper integral curve over a field `k` whose
codimension-one local rings are discrete valuation rings, if `H¹(X, 𝒪_X)` is finite-dimensional
over `k`, then for every Weil divisor `D`

`χ(𝒪_X(D)) = Σ_y D(y) [κ(y) : k] + χ(𝒪_X)`,

where `χ(M) = dim H⁰(X, M) - dim H¹(X, M)`. -/
theorem eulerCharBelow_sheaf_eq_relativeDegree_add (hX : ∀ y : X, coheight y ≤ 1)
    [FiniteDimensional k
      (Scheme.Modules.Cohomology (InvertibleSheaf.trivial X).obj 1)]
    (D : SchemeWeilDivisor X) :
    Scheme.Modules.eulerCharBelow k X (sheaf D) 2 =
      relativeDegree (X ↘ Spec (.of k)) D +
        Scheme.Modules.eulerCharBelow k X (InvertibleSheaf.trivial X).obj 2 := by
  obtain ⟨_, hclosed, hdeg⟩ := isNoetherian_and_isClosed_and_residueDegree_ne_zero k hX
  have := finiteDimensional_cohomology_zero_sheaf k hX 0
  have := finiteDimensional_cohomology_one_sheaf k hX 0
  rw [eulerCharBelow_sheaf_eq_relativeDegree_add_sheaf_zero k hclosed hdeg D,
    Scheme.Modules.eulerCharBelow_congr k (sheafZeroIsoTrivial hX)]

end Curve

section Degree

variable {X : Scheme.{u}} [IsIntegral X] [IsNoetherian X]
  [∀ y : CodimensionOnePoint X, IsDiscreteValuationRing (X.presheaf.stalk (y : X))]
  (k : Type u) [Field k] [X.Over (Spec (.of k))] [IsProper (X ↘ Spec (.of k))]
  [FiniteDimensional k (Scheme.Modules.Cohomology (InvertibleSheaf.trivial X).obj 1)]

/-- **The degree is a linear-equivalence invariant.** On a proper integral curve over `k` whose
codimension-one local rings are discrete valuation rings, with `H¹(X, 𝒪_X)` finite-dimensional,
linearly equivalent Weil divisors have the same degree: their sheaves are isomorphic, so their
Euler characteristics agree. -/
theorem relativeDegree_eq_of_linearlyEquivalent (hX : ∀ y : X, coheight y ≤ 1)
    {D E : SchemeWeilDivisor X}
    (h : (WeilDivisor.OrderSystem.ofScheme X).LinearlyEquivalent D E) :
    relativeDegree (X ↘ Spec (.of k)) D = relativeDegree (X ↘ Spec (.of k)) E := by
  have hχ : Scheme.Modules.eulerCharBelow k X (sheaf D) 2 =
      Scheme.Modules.eulerCharBelow k X (sheaf E) 2 :=
    Scheme.Modules.eulerCharBelow_congr k (nonempty_iso_sheaf_of_linearlyEquivalent h).some 2
  rw [eulerCharBelow_sheaf_eq_relativeDegree_add k hX D,
    eulerCharBelow_sheaf_eq_relativeDegree_add k hX E] at hχ
  exact add_right_cancel hχ

/-- **A principal divisor has degree zero.** On a proper integral curve over `k` whose
codimension-one local rings are discrete valuation rings, with `H¹(X, 𝒪_X)` finite-dimensional,
the divisor of a nonzero rational function has degree zero. -/
theorem relativeDegree_principalDivisor (hX : ∀ y : X, coheight y ≤ 1)
    (f : Additive X.functionFieldˣ) :
    relativeDegree (X ↘ Spec (.of k))
        ((WeilDivisor.OrderSystem.ofScheme X).principalDivisor f) = 0 := by
  have h := relativeDegree_eq_of_linearlyEquivalent k hX
    (D := (WeilDivisor.OrderSystem.ofScheme X).principalDivisor f) (E := 0)
    (by simpa using WeilDivisor.OrderSystem.linearlyEquivalent_add_principalDivisor _ 0 f)
  rwa [map_zero] at h

/-- **The residue-degree weights kill principal divisors.** This is
`SchemeWeilDivisor.relativeDegree_principalDivisor` in the form consumed by the abstract
degree-zero divisor class group `WeilDivisor.OrderSystem.picZero`. -/
theorem isWeightedDegreeZero_residueDegree (hX : ∀ y : X, coheight y ≤ 1) :
    (WeilDivisor.OrderSystem.ofScheme X).IsWeightedDegreeZero
      fun y : CodimensionOnePoint X ↦ ((X ↘ Spec (.of k)).residueDegree y : ℤ) := fun f ↦ by
  rw [WeilDivisor.weightedDegree_apply, ← relativeDegree_apply]
  exact relativeDegree_principalDivisor k hX f

end Degree

end SchemeWeilDivisor

namespace InvertibleSheaf

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
  [∀ y : CodimensionOnePoint X, IsDiscreteValuationRing (X.presheaf.stalk (y : X))]
  (k : Type u) [Field k] [X.Over (Spec (.of k))] [IsProper (X ↘ Spec (.of k))]

/-- **`H¹` of a line bundle on a proper curve is finite-dimensional once `H¹(X, 𝒪_X)` is.** On a
proper integral curve over a field `k` whose codimension-one local rings are discrete valuation
rings, if `H¹(X, 𝒪_X)` is finite-dimensional over `k`, then so is `H¹(X, L)` for every line
bundle `L`. -/
theorem finiteDimensional_cohomology_one (hX : ∀ y : X, coheight y ≤ 1)
    [FiniteDimensional k
      (Scheme.Modules.Cohomology (InvertibleSheaf.trivial X).obj 1)]
    (L : InvertibleSheaf X) :
    FiniteDimensional k (Scheme.Modules.Cohomology L.obj 1) := by
  have : CompactSpace X := (quasiCompact_iff_compactSpace (X ↘ Spec (.of k))).mp inferInstance
  have : IsNoetherian X := {}
  obtain ⟨D, ⟨e⟩⟩ := SchemeWeilDivisor.exists_nonempty_iso_sheaf hX L
  have := SchemeWeilDivisor.finiteDimensional_cohomology_one_sheaf k hX D
  exact (Scheme.Modules.finiteDimensional_cohomology_congr k e 1).mpr this

/-- **The Euler-characteristic degree of `𝒪_X(D)` is `deg D`.** On a proper integral curve over
a field `k` whose codimension-one local rings are discrete valuation rings, with `H¹(X, 𝒪_X)`
finite-dimensional over `k`, a line bundle `L ≅ 𝒪_X(D)` has
`χ(L) - χ(𝒪_X) = Σ_y D(y) [κ(y) : k]`. -/
theorem eulerDegree_eq_relativeDegree (hX : ∀ y : X, coheight y ≤ 1)
    [FiniteDimensional k
      (Scheme.Modules.Cohomology (InvertibleSheaf.trivial X).obj 1)]
    {L : InvertibleSheaf X} {D : SchemeWeilDivisor X} (e : L.obj ≅ SchemeWeilDivisor.sheaf D) :
    L.eulerDegree k = SchemeWeilDivisor.relativeDegree (X ↘ Spec (.of k)) D := by
  rw [eulerDegree_def, Scheme.Modules.eulerCharBelow_congr k e,
    SchemeWeilDivisor.eulerCharBelow_sheaf_eq_relativeDegree_add k hX D, add_sub_cancel_right]

end InvertibleSheaf

namespace LineBundleClass

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
  [∀ y : CodimensionOnePoint X, IsDiscreteValuationRing (X.presheaf.stalk (y : X))]
  (k : Type u) [Field k] [X.Over (Spec (.of k))] [IsProper (X ↘ Spec (.of k))]
  (hX : ∀ y : X, coheight y ≤ 1)
  [FiniteDimensional k (Scheme.Modules.Cohomology (InvertibleSheaf.trivial X).obj 1)]

/-- The Euler-characteristic degree of the line-bundle class of `𝒪_X(D)` is `deg D`, on a
proper integral curve over `k` whose codimension-one local rings are discrete valuation rings
and whose `H¹(X, 𝒪_X)` is finite-dimensional. -/
@[simp]
theorem eulerDegree_toLineBundleClass (D : SchemeWeilDivisor X) :
    eulerDegree k (@SchemeWeilDivisor.toLineBundleClass X _
      { toIsLocallyNoetherian := inferInstance
        toCompactSpace := (quasiCompact_iff_compactSpace (X ↘ Spec (.of k))).mp inferInstance }
      _ hX D) =
      SchemeWeilDivisor.relativeDegree (X ↘ Spec (.of k)) D := by
  let _ : IsNoetherian X :=
    { toIsLocallyNoetherian := inferInstance
      toCompactSpace := (quasiCompact_iff_compactSpace (X ↘ Spec (.of k))).mp inferInstance }
  rw [(SchemeWeilDivisor.toLineBundleClass_eq_mk_iff hX).mpr ⟨Iso.refl _⟩, eulerDegree_mk]
  exact InvertibleSheaf.eulerDegree_eq_relativeDegree k hX
    (eqToIso (SchemeWeilDivisor.toInvertibleSheaf_obj hX D))

include hX in
/-- **The Euler-characteristic degree is additive under tensor product**, on a proper integral
curve over `k` whose codimension-one local rings are discrete valuation rings and whose
`H¹(X, 𝒪_X)` is finite-dimensional. -/
@[simp]
theorem eulerDegree_mul (a b : LineBundleClass X) :
    eulerDegree k (a * b) = eulerDegree k a + eulerDegree k b := by
  let _ : IsNoetherian X :=
    { toIsLocallyNoetherian := inferInstance
      toCompactSpace := (quasiCompact_iff_compactSpace (X ↘ Spec (.of k))).mp inferInstance }
  obtain ⟨D, rfl⟩ := SchemeWeilDivisor.toLineBundleClass_surjective hX a
  obtain ⟨E, rfl⟩ := SchemeWeilDivisor.toLineBundleClass_surjective hX b
  rw [← SchemeWeilDivisor.toLineBundleClass_add, eulerDegree_toLineBundleClass,
    eulerDegree_toLineBundleClass, eulerDegree_toLineBundleClass, map_add]

end LineBundleClass

end AlgebraicGeometry

end TauCeti
