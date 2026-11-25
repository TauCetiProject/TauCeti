/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.CartierDivisor.BaseChange
public import TauCeti.AlgebraicGeometry.IntersectionNumber.NumericallyTrivial
import TauCeti.AlgebraicGeometry.Curves.Normalization

/-!
# The curve pairing of Cartier, `ℚ`-Cartier and `ℝ`-Cartier divisors

Let `X` be an integral scheme and `Div(X)` its group of Cartier divisors. For a proper integral
curve `C` over a field `k` with a morphism `ι : C ⟶ X`, the intersection number of a Cartier divisor
`D` with `C` is that of the invertible sheaf `𝒪_X(D)`,

`(D · C) = (𝒪_X(D) · C) = deg_k (ι^* 𝒪_X(D))`.

It restricts the sheaf `𝒪_X(D)` to `C` rather than a local equation of `D`, so curves contained in
the support of `D` are included. It is additive in `D`, and principal divisors pair to zero with
every curve, since their sheaves are trivial.

For a commutative ring `K`, write `Div(X)_K = K ⊗[ℤ] Div(X)`; the cases of interest are
`Div(X)_ℚ` and `Div(X)_ℝ`, the `ℚ`-Cartier and `ℝ`-Cartier divisors. The pairing extends
`K`-linearly to `Div(X)_K`. A `K`-Cartier divisor `D` on a proper `k`-scheme `X` is *numerically
trivial*, `D ≡ 0`, when `(D · C) = 0` for every integral closed curve `C ⊆ X`; for a proper
morphism `f : X ⟶ S` it is *relatively numerically trivial*, `D ≡_f 0`, when `(D · C) = 0` for
every integral closed curve `C` in every scheme-theoretic fibre `X_s`, with degrees over `κ(s)`.
These are the same test curves and degrees as for the numerical triviality of line-bundle classes,
`LineBundleClass.NumericallyTrivial` and `LineBundleClass.RelNumericallyTrivial`: when `K` has
characteristic zero, `1 ⊗ D ≡_f 0` exactly when `𝒪_X(D) ≡_f 0`. Two `K`-Cartier divisors are
*`K`-linearly equivalent* when their difference is a `K`-combination of principal divisors, and
`K`-linear equivalence implies numerical equivalence.

When `X` is moreover Noetherian and normal, the Cartier-to-Weil map is injective
(`Scheme.CartierDivisor.toWeilDivisorHom_injective`), and so is its extension
`Div(X)_ℚ ⟶ ℚ ⊗[ℤ] Weil(X)`, since `ℚ` is flat over `ℤ`. A Weil divisor `D` with rational
coefficients is *`ℚ`-Cartier* when `r D` is the Weil divisor of a Cartier divisor `A` for some
integer `r ≥ 1`; these form the range of that extension, a `ℚ`-subspace. The pairing transported
along this embedding is `(D · C) = (A · C) / r`, independent of the pair `(r, A)`, and
`ℚ`-linearly equivalent `ℚ`-Cartier Weil divisors have the same pairings with every curve. The
divisor-theoretic side, `K`-linear equivalence and the `ℚ`-Cartier Weil divisors, is in
`TauCeti.AlgebraicGeometry.CartierDivisor.BaseChange`.

## Main declarations

* `Scheme.CartierDivisor.intersectionNumberHom k ι`: the pairing `D ↦ (D · C)` on `Div(X)`;
* `Scheme.CartierDivisor.baseChangeIntersectionNumber K k ι`: its `K`-linear extension to
  `Div(X)_K`, with `(a ⊗ D · C) = a (D · C)`;
* `Scheme.CartierDivisor.principalSubmodule_le_ker_baseChangeIntersectionNumber`: every pairing
  vanishes on the `K`-combinations of principal divisors;
* `Scheme.CartierDivisor.NumericallyTrivial K k x` and
  `Scheme.CartierDivisor.RelNumericallyTrivial K f`: numerical and relative numerical triviality of
  `K`-Cartier divisors, forming the `K`-subspaces `numericallyTrivialSubmodule K k x` and
  `relNumericallyTrivialSubmodule K f`, which contain `principalSubmodule K X`;
* `Scheme.CartierDivisor.numericallyTrivial_one_tmul_iff` and
  `Scheme.CartierDivisor.relNumericallyTrivial_one_tmul_iff`: `1 ⊗ D ≡_f 0` iff `𝒪_X(D) ≡_f 0`;
* `Scheme.CartierDivisor.qCartierIntersectionNumber k ι`: the pairing of `ℚ`-Cartier Weil divisors
  (`Scheme.CartierDivisor.qCartierSubmodule X`) with curves, computed by
  `Scheme.CartierDivisor.qCartierIntersectionNumber_eq_div` and invariant under `ℚ`-linear
  equivalence
  (`Scheme.CartierDivisor.qCartierIntersectionNumber_eq_of_sub_mem_baseChange_principalSubgroup`);
* `projectiveLine.numericallyTrivial_one_tmul_iff_toLineBundleClass_eq_one`: on `ℙ¹_k` the
  numerically trivial Cartier divisors are those with trivial sheaf.

## References

* R. Lazarsfeld, *Positivity in Algebraic Geometry I*, Ergebnisse der Mathematik und ihrer
  Grenzgebiete 48, Springer, 2004, §1.1.C and §1.3.B: the pairing of Cartier and `ℝ`-Cartier
  divisors with curves, numerical equivalence, and `ℝ`-linear equivalence.
* [The Stacks Project, Lemma 10.157.6](https://stacks.math.columbia.edu/tag/031T): a Noetherian
  normal domain is the intersection of its localizations at height-one primes, the input to the
  injectivity of the Cartier-to-Weil map.
-/

public section

open CategoryTheory Limits AlgebraicGeometry TensorProduct

namespace TauCeti.AlgebraicGeometry.Scheme.CartierDivisor

universe u

noncomputable section

variable (K : Type*) [CommRing K] {X : Scheme.{u}} [IsIntegral X]

section Pairing

variable (k : Type u) [Field k] {C : Scheme.{u}}
  [C.Over (Spec (.of k))] (ι : C ⟶ X) [IsIntegral C] [IsProper (C ↘ Spec (.of k))]
  [RelativeDimensionLE 1 (C ↘ Spec (.of k))]

open _root_.AlgebraicGeometry.Scheme.Modules in
/-- The **intersection number** `(D · C)` of a Cartier divisor `D` with a proper integral curve `C`
over `k` mapping to `X` by `ι`, as an additive map `Div(X) →+ ℤ`: the intersection number of the
class of `𝒪_X(D)`. The curve may be singular, and may lie in the support of `D`. -/
def intersectionNumberHom : CartierDivisor X →+ ℤ where
  toFun D := LineBundleClass.intersectionNumber k ι D.toLineBundleClass
  map_zero' := by rw [toLineBundleClass_zero, LineBundleClass.intersectionNumber_one]
  map_add' D E := by
    have hC : topologicalKrullDim C ≤ 1 := (relativeDimensionLE_iff_of_field _).mp ‹_›
    have := finiteDimensional_cohomology_trivial_of_topologicalKrullDim_le_one k hC 0
    have := finiteDimensional_cohomology_trivial_of_topologicalKrullDim_le_one k hC 1
    rw [toLineBundleClass_add, LineBundleClass.intersectionNumber_mul_of_isIntegral]

/-- The intersection number of a Cartier divisor is that of the class of its sheaf. -/
@[simp]
lemma intersectionNumberHom_apply (D : CartierDivisor X) :
    intersectionNumberHom k ι D = LineBundleClass.intersectionNumber k ι D.toLineBundleClass :=
  (rfl)

/-- **Principal divisors pair to zero** with every curve. -/
theorem intersectionNumberHom_principalCartierDivisor (f : X.functionFieldˣ) :
    intersectionNumberHom k ι (principalCartierDivisor X f) = 0 := by
  rw [intersectionNumberHom_apply, toLineBundleClass_principalCartierDivisor,
    LineBundleClass.intersectionNumber_one]

/-- Every principal Cartier divisor lies in the kernel of every curve pairing; hence linearly
equivalent Cartier divisors have the same intersection number with every curve. -/
theorem principalSubgroup_le_ker_intersectionNumberHom :
    principalSubgroup X ≤ (intersectionNumberHom k ι).ker := by
  intro D hD
  obtain ⟨f, rfl⟩ := mem_principalSubgroup.mp hD
  exact intersectionNumberHom_principalCartierDivisor k ι f

/-- The **pairing of `K`-Cartier divisors** with a proper integral curve `C` over `k`: the
`K`-linear extension `Div(X)_K →ₗ[K] K` of `D ↦ (D · C)` to `Div(X)_K = K ⊗[ℤ] Div(X)`. For
`K = ℚ` and `K = ℝ` this is the pairing of `ℚ`-Cartier and `ℝ`-Cartier divisors with curves. -/
def baseChangeIntersectionNumber : K ⊗[ℤ] CartierDivisor X →ₗ[K] K :=
  ((Int.castAddHom K).comp (intersectionNumberHom k ι)).toIntLinearMap.liftBaseChange K

/-- The pairing of `a ⊗ D` with a curve is `a (D · C)`. -/
@[simp]
lemma baseChangeIntersectionNumber_tmul (a : K) (D : CartierDivisor X) :
    baseChangeIntersectionNumber K k ι (a ⊗ₜ D) = a * intersectionNumberHom k ι D := by
  rw [baseChangeIntersectionNumber, LinearMap.liftBaseChange_tmul, smul_eq_mul,
    AddMonoidHom.coe_toIntLinearMap, AddMonoidHom.comp_apply, Int.coe_castAddHom]

/-- **`K`-linearly equivalent `K`-Cartier divisors have the same intersection number** with every
curve: the pairing vanishes on `K`-combinations of principal divisors. -/
theorem principalSubmodule_le_ker_baseChangeIntersectionNumber :
    principalSubmodule K X ≤ LinearMap.ker (baseChangeIntersectionNumber K k ι) := by
  refine (principalSubmodule_le_iff K).mpr fun D hD ↦ ?_
  obtain ⟨f, rfl⟩ := mem_principalSubgroup.mp hD
  rw [LinearMap.mem_ker, baseChangeIntersectionNumber_tmul,
    intersectionNumberHom_principalCartierDivisor, Int.cast_zero, mul_zero]

end Pairing

/-- A morphism equal to a composite of proper morphisms is proper. -/
private lemma isProper_of_eq_comp {C Y S : Scheme.{u}} {f : C ⟶ S} {i : C ⟶ Y} {x : Y ⟶ S}
    [IsProper i] [IsProper x] (h : f = i ≫ x) : IsProper f := by
  rw [h]
  infer_instance

/-- A one-dimensional scheme over a field has relative dimension at most one. -/
private lemma relativeDimensionLE_one_of_topologicalKrullDim_eq_one {k : Type u} [Field k]
    {C : Scheme.{u}} (f : C ⟶ Spec (.of k)) (hC : topologicalKrullDim C = 1) :
    RelativeDimensionLE 1 f :=
  (relativeDimensionLE_iff_of_field f).mpr hC.le

section Absolute

variable (k : Type u) [Field k] (x : X ⟶ Spec (.of k)) [IsProper x]

/-- A `K`-Cartier divisor `D` on an integral proper scheme `X` over `k` with structure morphism `x`
is **numerically trivial**, `D ≡ 0`, when its intersection number over `k` with every integral
closed curve `C ⊆ X` vanishes. The test curves are those of `LineBundleClass.NumericallyTrivial`;
such a curve is proper over `k` of dimension one, which makes the pairing available. -/
def NumericallyTrivial (D : K ⊗[ℤ] CartierDivisor X) : Prop :=
  ∀ (C : Scheme.{u}) [IsIntegral C] [C.Over (Spec (.of k))] (i : C ⟶ X) [IsClosedImmersion i]
    (hi : C ↘ Spec (.of k) = i ≫ x) (hC : topologicalKrullDim C = 1),
    have := isProper_of_eq_comp hi
    have := relativeDimensionLE_one_of_topologicalKrullDim_eq_one (C ↘ Spec (.of k)) hC
    baseChangeIntersectionNumber K k i D = 0

variable {K k x}

/-- Numerical triviality of a `K`-Cartier divisor, as vanishing of its pairing with every integral
closed curve. -/
theorem numericallyTrivial_iff {D : K ⊗[ℤ] CartierDivisor X} :
    NumericallyTrivial K k x D ↔ ∀ (C : Scheme.{u}) [IsIntegral C] [C.Over (Spec (.of k))]
      [IsProper (C ↘ Spec (.of k))] [RelativeDimensionLE 1 (C ↘ Spec (.of k))] (i : C ⟶ X)
      [IsClosedImmersion i], C ↘ Spec (.of k) = i ≫ x → topologicalKrullDim C = 1 →
        baseChangeIntersectionNumber K k i D = 0 := by
  refine ⟨fun h C _ _ _ _ i _ hi hC ↦ h C i hi hC, fun h C _ _ i _ hi hC ↦ ?_⟩
  have := isProper_of_eq_comp hi
  have := relativeDimensionLE_one_of_topologicalKrullDim_eq_one (C ↘ Spec (.of k)) hC
  exact h C i hi hC

/-- The pairing of a numerically trivial `K`-Cartier divisor with an integral closed curve
vanishes. -/
theorem NumericallyTrivial.baseChangeIntersectionNumber_eq_zero {D : K ⊗[ℤ] CartierDivisor X}
    (hD : NumericallyTrivial K k x D) {C : Scheme.{u}} [IsIntegral C] [C.Over (Spec (.of k))]
    [IsProper (C ↘ Spec (.of k))] [RelativeDimensionLE 1 (C ↘ Spec (.of k))] (i : C ⟶ X)
    [IsClosedImmersion i] (hi : C ↘ Spec (.of k) = i ≫ x) (hC : topologicalKrullDim C = 1) :
    baseChangeIntersectionNumber K k i D = 0 :=
  numericallyTrivial_iff.mp hD C i hi hC

variable (K k x) in
/-- The `K`-subspace of numerically trivial `K`-Cartier divisors on an integral proper
`k`-scheme. -/
def numericallyTrivialSubmodule : Submodule K (K ⊗[ℤ] CartierDivisor X) where
  carrier := {D | NumericallyTrivial K k x D}
  add_mem' {D E} hD hE := numericallyTrivial_iff.mpr fun C _ _ _ _ i _ hi hC ↦ by
    rw [map_add, hD.baseChangeIntersectionNumber_eq_zero i hi hC,
      hE.baseChangeIntersectionNumber_eq_zero i hi hC, add_zero]
  zero_mem' := numericallyTrivial_iff.mpr fun C _ _ _ _ i _ _ _ ↦ map_zero _
  smul_mem' a D hD := numericallyTrivial_iff.mpr fun C _ _ _ _ i _ hi hC ↦ by
    rw [map_smul, hD.baseChangeIntersectionNumber_eq_zero i hi hC, smul_zero]

/-- Membership in the subspace of numerically trivial `K`-Cartier divisors. -/
@[simp]
theorem mem_numericallyTrivialSubmodule {D : K ⊗[ℤ] CartierDivisor X} :
    D ∈ numericallyTrivialSubmodule K k x ↔ NumericallyTrivial K k x D :=
  Iff.rfl

/-- **Numerical triviality of a Cartier divisor is that of its sheaf.** Over a ring `K` of
characteristic zero, `1 ⊗ D` is numerically trivial exactly when `𝒪_X(D)` is. -/
theorem numericallyTrivial_one_tmul_iff [CharZero K] (D : CartierDivisor X) :
    NumericallyTrivial K k x (1 ⊗ₜ D) ↔
      LineBundleClass.NumericallyTrivial k x D.toLineBundleClass := by
  rw [LineBundleClass.numericallyTrivial_iff]
  refine ⟨fun h C _ _ i _ hi hC ↦ by simpa using h C i hi hC,
    fun h ↦ numericallyTrivial_iff.mpr fun C _ _ _ _ i _ hi hC ↦ by simpa using h C i hi hC⟩

variable (K k x) in
/-- **`K`-linear equivalence implies numerical equivalence**: every `K`-combination of principal
divisors is numerically trivial. -/
theorem principalSubmodule_le_numericallyTrivialSubmodule :
    principalSubmodule K X ≤ numericallyTrivialSubmodule K k x := fun _ hD ↦
  numericallyTrivial_iff.mpr fun _ _ _ _ _ i _ _ _ ↦
    principalSubmodule_le_ker_baseChangeIntersectionNumber K k i hD

end Absolute

section Relative

variable {S : Scheme.{u}} (f : X ⟶ S) [IsProper f]

/-- A `K`-Cartier divisor `D` on `X` is **relatively numerically trivial** for a proper morphism
`f : X ⟶ S`, `D ≡_f 0`, when for every point `s` of `S` its intersection number over `κ(s)` with
every integral closed curve `C` of the scheme-theoretic fibre `X_s`, mapping to `X` through
`X_s ⟶ X`, vanishes. The test curves are those of `LineBundleClass.RelNumericallyTrivial`. -/
def RelNumericallyTrivial (D : K ⊗[ℤ] CartierDivisor X) : Prop :=
  ∀ (s : S) (C : Scheme.{u}) [IsIntegral C] [C.Over (Spec (S.residueField s))]
    (i : C ⟶ f.fiber s) [IsClosedImmersion i]
    (hi : C ↘ Spec (S.residueField s) = i ≫ f.fiberToSpecResidueField s)
    (hC : topologicalKrullDim C = 1),
    have := isProper_of_eq_comp hi
    have : RelativeDimensionLE 1 (C ↘ Spec (S.residueField s)) :=
      relativeDimensionLE_one_of_topologicalKrullDim_eq_one _ hC
    baseChangeIntersectionNumber K (S.residueField s) (i ≫ f.fiberι s) D = 0

variable {K f}

/-- Relative numerical triviality of a `K`-Cartier divisor, as vanishing of its pairing with every
integral closed curve in every fibre. -/
theorem relNumericallyTrivial_iff {D : K ⊗[ℤ] CartierDivisor X} :
    RelNumericallyTrivial K f D ↔ ∀ (s : S) (C : Scheme.{u}) [IsIntegral C]
      [C.Over (Spec (S.residueField s))] [IsProper (C ↘ Spec (S.residueField s))]
      [RelativeDimensionLE 1 (C ↘ Spec (S.residueField s))] (i : C ⟶ f.fiber s)
      [IsClosedImmersion i], C ↘ Spec (S.residueField s) = i ≫ f.fiberToSpecResidueField s →
        topologicalKrullDim C = 1 →
          baseChangeIntersectionNumber K (S.residueField s) (i ≫ f.fiberι s) D = 0 := by
  refine ⟨fun h s C _ _ _ _ i _ hi hC ↦ h s C i hi hC, fun h s C _ _ i _ hi hC ↦ ?_⟩
  have := isProper_of_eq_comp hi
  have : RelativeDimensionLE 1 (C ↘ Spec (S.residueField s)) :=
    relativeDimensionLE_one_of_topologicalKrullDim_eq_one _ hC
  exact h s C i hi hC

/-- The pairing of a relatively numerically trivial `K`-Cartier divisor with an integral closed
curve in a fibre vanishes. -/
theorem RelNumericallyTrivial.baseChangeIntersectionNumber_eq_zero
    {D : K ⊗[ℤ] CartierDivisor X} (hD : RelNumericallyTrivial K f D) (s : S) {C : Scheme.{u}}
    [IsIntegral C] [C.Over (Spec (S.residueField s))] [IsProper (C ↘ Spec (S.residueField s))]
    [RelativeDimensionLE 1 (C ↘ Spec (S.residueField s))] (i : C ⟶ f.fiber s)
    [IsClosedImmersion i] (hi : C ↘ Spec (S.residueField s) = i ≫ f.fiberToSpecResidueField s)
    (hC : topologicalKrullDim C = 1) :
    baseChangeIntersectionNumber K (S.residueField s) (i ≫ f.fiberι s) D = 0 :=
  relNumericallyTrivial_iff.mp hD s C i hi hC

variable (K f) in
/-- The `K`-subspace of relatively numerically trivial `K`-Cartier divisors for a proper morphism
`f`. -/
def relNumericallyTrivialSubmodule : Submodule K (K ⊗[ℤ] CartierDivisor X) where
  carrier := {D | RelNumericallyTrivial K f D}
  add_mem' {D E} hD hE := relNumericallyTrivial_iff.mpr fun s C _ _ _ _ i _ hi hC ↦ by
    rw [map_add, hD.baseChangeIntersectionNumber_eq_zero s i hi hC,
      hE.baseChangeIntersectionNumber_eq_zero s i hi hC, add_zero]
  zero_mem' := relNumericallyTrivial_iff.mpr fun _ C _ _ _ _ i _ _ _ ↦ map_zero _
  smul_mem' a D hD := relNumericallyTrivial_iff.mpr fun s C _ _ _ _ i _ hi hC ↦ by
    rw [map_smul, hD.baseChangeIntersectionNumber_eq_zero s i hi hC, smul_zero]

/-- Membership in the subspace of relatively numerically trivial `K`-Cartier divisors. -/
@[simp]
theorem mem_relNumericallyTrivialSubmodule {D : K ⊗[ℤ] CartierDivisor X} :
    D ∈ relNumericallyTrivialSubmodule K f ↔ RelNumericallyTrivial K f D :=
  Iff.rfl

/-- **Relative numerical triviality of a Cartier divisor is that of its sheaf.** Over a ring `K`
of characteristic zero, `1 ⊗ D ≡_f 0` exactly when `𝒪_X(D) ≡_f 0`. -/
theorem relNumericallyTrivial_one_tmul_iff [CharZero K] (D : CartierDivisor X) :
    RelNumericallyTrivial K f (1 ⊗ₜ D) ↔
      LineBundleClass.RelNumericallyTrivial f D.toLineBundleClass := by
  rw [relNumericallyTrivial_iff, LineBundleClass.relNumericallyTrivial_iff]
  refine ⟨fun h s ↦ (LineBundleClass.numericallyTrivial_iff _ _ _).mpr fun C _ _ i _ hi hC ↦ ?_,
    fun h s C _ _ _ _ i _ hi hC ↦ ?_⟩
  · have := isProper_of_eq_comp hi
    have : RelativeDimensionLE 1 (C ↘ Spec (S.residueField s)) :=
      relativeDimensionLE_one_of_topologicalKrullDim_eq_one _ hC
    simpa using h s C i hi hC
  · simpa using (h s).intersectionNumber_eq_zero i hi hC

variable (K f) in
/-- **`K`-linear equivalence implies relative numerical equivalence**: every `K`-combination of
principal divisors is relatively numerically trivial. -/
theorem principalSubmodule_le_relNumericallyTrivialSubmodule :
    principalSubmodule K X ≤ relNumericallyTrivialSubmodule K f := fun _ hD ↦
  relNumericallyTrivial_iff.mpr fun s _ _ _ _ _ i _ _ _ ↦
    principalSubmodule_le_ker_baseChangeIntersectionNumber K (S.residueField s) (i ≫ f.fiberι s) hD

end Relative

section Weil

variable [IsNoetherian X]

variable [IsNormalScheme X]

variable (k : Type u) [Field k] {C : Scheme.{u}} [C.Over (Spec (.of k))] (ι : C ⟶ X)
  [IsIntegral C] [IsProper (C ↘ Spec (.of k))] [RelativeDimensionLE 1 (C ↘ Spec (.of k))]

/-- The **pairing of `ℚ`-Cartier Weil divisors** with a proper integral curve `C` over `k`: the
pairing of `Div(X)_ℚ` transported along `qCartierEquiv X`. -/
def qCartierIntersectionNumber : qCartierSubmodule X →ₗ[ℚ] ℚ :=
  baseChangeIntersectionNumber ℚ k ι ∘ₗ (qCartierEquiv X).symm.toLinearMap

/-- The pairing of the Weil divisor of a `ℚ`-Cartier divisor is the pairing of the latter. -/
@[simp]
theorem qCartierIntersectionNumber_qCartierEquiv (E : ℚ ⊗[ℤ] CartierDivisor X) :
    qCartierIntersectionNumber k ι (qCartierEquiv X E) = baseChangeIntersectionNumber ℚ k ι E := by
  rw [qCartierIntersectionNumber, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply]

/-- **The pairing of a `ℚ`-Cartier Weil divisor.** If `r D` is the Weil divisor of a Cartier
divisor `A` with `r ≥ 1`, then `(D · C) = (A · C) / r`; in particular the right side does not
depend on the pair `(r, A)`. -/
theorem qCartierIntersectionNumber_eq_div (D : qCartierSubmodule X) {r : ℕ} (hr : 0 < r)
    {A : CartierDivisor X} (h : (r : ℚ) • (D : ℚ ⊗[ℤ] SchemeWeilDivisor X) = 1 ⊗ₜ A.toWeilDivisor) :
    qCartierIntersectionNumber k ι D = intersectionNumberHom k ι A / r := by
  have hD : qCartierEquiv X ((r⁻¹ : ℚ) ⊗ₜ A) = D :=
    Subtype.ext <| (coe_qCartierEquiv_apply _).trans <|
      baseChangeToWeilDivisor_inv_tmul (Nat.cast_ne_zero.mpr hr.ne') h
  rw [← hD, qCartierIntersectionNumber_qCartierEquiv, baseChangeIntersectionNumber_tmul,
    inv_mul_eq_div]

/-- **`ℚ`-linearly equivalent `ℚ`-Cartier Weil divisors have equal pairings** with every curve:
if `D - D'` is a `ℚ`-combination of principal Weil divisors, then `(D · C) = (D' · C)`. -/
theorem qCartierIntersectionNumber_eq_of_sub_mem_baseChange_principalSubgroup
    {D D' : qCartierSubmodule X}
    (h : (D - D' : ℚ ⊗[ℤ] SchemeWeilDivisor X) ∈
      (WeilDivisor.OrderSystem.ofScheme X).principalSubgroup.toIntSubmodule.baseChange ℚ) :
    qCartierIntersectionNumber k ι D = qCartierIntersectionNumber k ι D' := by
  rw [← sub_eq_zero, ← map_sub]
  exact principalSubmodule_le_ker_baseChangeIntersectionNumber ℚ k ι
    (qCartierEquiv_symm_mem_principalSubmodule h)

end Weil

end

end TauCeti.AlgebraicGeometry.Scheme.CartierDivisor

namespace TauCeti.AlgebraicGeometry.projectiveLine

universe u

/-- **Numerically trivial Cartier divisors on the projective line.** Over a ring `K` of
characteristic zero, a Cartier divisor `D` on `ℙ¹_k` is numerically trivial as a `K`-Cartier
divisor exactly when `𝒪(D)` is trivial; for instance a divisor with `𝒪(D) ≅ 𝒪(1)` is not. -/
theorem numericallyTrivial_one_tmul_iff_toLineBundleClass_eq_one (K : Type*) [CommRing K]
    [CharZero K] (k : Type u) [Field k] (D : Scheme.CartierDivisor (projectiveLine k)) :
    Scheme.CartierDivisor.NumericallyTrivial K k (projectiveLine k ↘ Spec (.of k)) (1 ⊗ₜ D) ↔
      D.toLineBundleClass = 1 := by
  rw [Scheme.CartierDivisor.numericallyTrivial_one_tmul_iff, numericallyTrivial_iff_eq_one]

end TauCeti.AlgebraicGeometry.projectiveLine
