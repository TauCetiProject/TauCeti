/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.FiniteAbelian.Duality
public import Mathlib.GroupTheory.GroupAction.Basic
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
public import TauCeti.Algebra.MonoidAlgebra.Face.Coaction
public import TauCeti.FieldTheory.IsAlgClosed.Units
public import TauCeti.GroupTheory.Divisible
public import TauCeti.GroupTheory.QuotientGroup.KerEquiv

/-!
# Torus orbits, stabilizer character groups, and orbit normalization of semigroup algebras

Let `S` be an additive submonoid of an abelian group `G` and `R` a commutative semiring. For any
commutative `R`-algebra `A`, the character group
`Multiplicative (AddSubgroup.closure (S : Set G)) →* Aˣ` of the dense torus acts on `A`-points
`AddMonoidAlgebra R S →ₐ[R] A` via `S.torusCoaction R`.

1. **Distinguished points and stabilizer quotients.** Each face `F : SaturatedAddSubmonoid S`
   defines `F.distinguishedPoint R A` sending `single s 1` to `1` on `F` and `0` outside `F`. The
   surjective bialgebra quotient `F.stabilizerBialgHom R : R[AddSubgroup.closure S] →ₐc[R]
   R[AddSubgroup.closure S ⧸ F.faceSubgroup]` induces a trivial coaction on `F.orbitMap R`, and on
   `A`-points `SaturatedAddSubmonoid.stabilizerDistinguishedPointMulEquiv` identifies the
   stabilizer of `F.distinguishedPoint R A` with
   `Multiplicative (AddSubgroup.closure S ⧸ F.faceSubgroup) →* Aˣ`.
2. **Orbit–face bijection on geometric points.** Over a nontrivial domain `A`, `S.pointSupport x :
   SaturatedAddSubmonoid S` is torus-invariant and recovers `F` on `F.distinguishedPoint R A`. Over
   any field `K`, `SaturatedAddSubmonoid.pointSupportSubtypeEquivChar` identifies the `F`-stratum
   with `Multiplicative F.faceSubgroup →* Kˣ`. Whenever `[RootableBy Kˣ ℕ]` (in particular over any
   algebraically closed field `K`), `Additive Kˣ` is Baer-injective over `ℤ`, so each support
   stratum is a single torus orbit (`SaturatedAddSubmonoid.setOf_pointSupport_eq_orbit`) and
   `S.faceOrbitEquiv R K` gives the geometric orbit–face bijection.
3. **Comparison with normalization on each orbit.** Precomposition with normalization pulls
   `pointSupport` back along `S.nsmulSaturationInfClosureFaceOrderIso` and restricts on the
   `F`-stratum to `F.orbitNormalizationCharHom A`. Whenever `[RootableBy Aˣ ℕ]`, this map is
   surjective with kernel isomorphic to characters of `Q_F = F.faceSubgroup.nsmulSaturation ⧸
   F.faceSubgroup`. Over an algebraically closed field `K` with `S.FG`, fibers have cardinality
   `Nat.card Q_F` when invertible in `K` (so in char `0`, injectivity holds iff `F.faceSubgroup` is
   saturated), while in char `p > 0` it is bijective on `K`-points when `Q_F` is `p`-primary.

## Main declarations

* `AddSubmonoid.instMulActionCharAlgHom`, `SaturatedAddSubmonoid.distinguishedPoint`,
  `SaturatedAddSubmonoid.stabilizerBialgHom`, and
  `SaturatedAddSubmonoid.stabilizerDistinguishedPointMulEquiv`: torus action and stabilizers.
* `AddSubmonoid.pointSupport`, `SaturatedAddSubmonoid.pointSupportSubtypeEquivChar`,
  `SaturatedAddSubmonoid.setOf_pointSupport_eq_orbit`, and `AddSubmonoid.faceOrbitEquiv`:
  orbit–face decomposition and bijection on geometric points.
* `SaturatedAddSubmonoid.orbitNormalizationCharHom`,
  `SaturatedAddSubmonoid.orbitNormalizationCharHom_surjective`,
  `SaturatedAddSubmonoid.card_orbitNormalizationCharHom_ker`,
  `SaturatedAddSubmonoid.orbitNormalizationCharHom_injective_iff_of_charZero`, and
  `SaturatedAddSubmonoid.orbitNormalizationCharHom_bijective_of_charP`: orbit normalization.

## References

* W. Bruns and J. Gubeladze, *Polytopes, Rings, and K-Theory*, Theorem 4.38.
* D. Cox, J. Little and H. Schenck, *Toric Varieties*, Theorem 3.2.6.
* E. Miller and B. Sturmfels, *Combinatorial Commutative Algebra*, Chapter 7.
-/

public section

open scoped TensorProduct
open AddMonoidAlgebra

namespace AddSubmonoid

section TorusAction

variable {G : Type*} [AddCommGroup G] (S : AddSubmonoid G)
  {R A : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]

/-- Scalar action of the torus character group `Multiplicative (AddSubgroup.closure S) →* Aˣ` on
`A`-points `AddMonoidAlgebra R S →ₐ[R] A` induced by `S.torusCoaction R`. -/
noncomputable instance instSMulCharAlgHom :
    SMul (Multiplicative (AddSubgroup.closure (S : Set G)) →* Aˣ)
      (AddMonoidAlgebra R S →ₐ[R] A) where
  smul χ x :=
    (Algebra.TensorProduct.lift
      (AddMonoidAlgebra.lift R A _ ((Units.coeHom A).comp χ)) x
      fun _ _ ↦ Commute.all _ _).comp (S.torusCoaction R)

/-- Explicit definition of the torus character action on `A`-points. -/
theorem smul_algHom_def {S : AddSubmonoid G}
    (χ : Multiplicative (AddSubgroup.closure (S : Set G)) →* Aˣ)
    (x : AddMonoidAlgebra R S →ₐ[R] A) :
    χ • x =
      (Algebra.TensorProduct.lift
        (AddMonoidAlgebra.lift R A _ ((Units.coeHom A).comp χ)) x
        fun _ _ ↦ Commute.all _ _).comp (S.torusCoaction R) := (rfl)

/-- Acting by a torus character `χ` scales `x (single s r)` by `χ (S.toGroupClosure s)`. -/
@[simp]
theorem smul_algHom_single_apply {S : AddSubmonoid G}
    (χ : Multiplicative (AddSubgroup.closure (S : Set G)) →* Aˣ)
    (x : AddMonoidAlgebra R S →ₐ[R] A) (s : S) (r : R) :
    (χ • x) (single s r) = (χ (.ofAdd (S.toGroupClosure s)) : A) * x (single s r) := by
  rw [smul_algHom_def, AlgHom.comp_apply]
  simp

/-- The character group `Multiplicative (AddSubgroup.closure (S : Set G)) →* Aˣ` of the dense torus
acts on `A`-points `AddMonoidAlgebra R S →ₐ[R] A` via `S.torusCoaction R`. -/
noncomputable instance instMulActionCharAlgHom :
    MulAction (Multiplicative (AddSubgroup.closure (S : Set G)) →* Aˣ)
      (AddMonoidAlgebra R S →ₐ[R] A) where
  one_smul x := by ext; simp
  mul_smul χ₁ χ₂ x := by ext; simp [mul_assoc]

end TorusAction

end AddSubmonoid

namespace SaturatedAddSubmonoid

section Stabilizer

variable {G : Type*} [AddCommGroup G] {S : AddSubmonoid G} (F : SaturatedAddSubmonoid S)

/-- The distinguished `A`-point of `Spec R[S]` associated to a face `F`, obtained by composing
`F.orbitMap R` with the bialgebra counit of `R[F.faceSubgroup]`. -/
noncomputable def distinguishedPoint (R A : Type*) [CommSemiring R] [CommSemiring A] [Algebra R A] :
    AddMonoidAlgebra R S →ₐ[R] A :=
  (Algebra.ofId R A).comp ((Bialgebra.counitAlgHom R (AddMonoidAlgebra R F.faceSubgroup)).comp
    (F.orbitMap R))

/-- Explicit definition of `SaturatedAddSubmonoid.distinguishedPoint`. -/
theorem distinguishedPoint_def (R A : Type*) [CommSemiring R] [CommSemiring A] [Algebra R A] :
    F.distinguishedPoint R A = (Algebra.ofId R A).comp
      ((Bialgebra.counitAlgHom R (AddMonoidAlgebra R F.faceSubgroup)).comp (F.orbitMap R)) := (rfl)

/-- On a monomial in `F`, `F.distinguishedPoint R A` sends `single a r` to `algebraMap R A r`. -/
theorem distinguishedPoint_single_mem (R A : Type*) [CommSemiring R] [CommSemiring A] [Algebra R A]
    (a : F) (r : R) :
    F.distinguishedPoint R A (single (a : S) r) = algebraMap R A r := by simp [distinguishedPoint]

/-- On a monomial whose exponent lies in `F`, `F.distinguishedPoint R A` sends `single s r` to
`algebraMap R A r`. -/
@[simp]
theorem distinguishedPoint_single_of_mem (R A : Type*) [CommSemiring R] [CommSemiring A]
    [Algebra R A] {s : S} (hs : s ∈ F) (r : R) :
    F.distinguishedPoint R A (single s r) = algebraMap R A r :=
  F.distinguishedPoint_single_mem R A ⟨s, hs⟩ r

/-- On a monomial outside `F`, `F.distinguishedPoint R A` vanishes. -/
@[simp]
theorem distinguishedPoint_single_of_notMem (R A : Type*) [CommSemiring R] [CommSemiring A]
    [Algebra R A] {s : S} (hs : s ∉ F) (r : R) :
    F.distinguishedPoint R A (single s r) = 0 := by
  simp [distinguishedPoint, F.orbitMap_single_of_notMem R hs]

/-- The surjective bialgebra quotient
`R[AddSubgroup.closure S] →ₐc[R] R[AddSubgroup.closure S ⧸ F.faceSubgroup]` whose `A`-points
(via `stabilizerDistinguishedPointMulEquiv`) match the stabilizer of `F.distinguishedPoint R A`
and whose coaction acts trivially on `F.orbitMap R`. -/
noncomputable def stabilizerBialgHom (R : Type*) [CommSemiring R] :
    AddMonoidAlgebra R (AddSubgroup.closure (S : Set G)) →ₐc[R]
      AddMonoidAlgebra R (AddSubgroup.closure (S : Set G) ⧸ F.faceSubgroup) :=
  mapDomainBialgHom R (QuotientAddGroup.mk' F.faceSubgroup)

/-- Explicit definition of `SaturatedAddSubmonoid.stabilizerBialgHom`. -/
theorem stabilizerBialgHom_def (R : Type*) [CommSemiring R] :
    F.stabilizerBialgHom R = mapDomainBialgHom R (QuotientAddGroup.mk' F.faceSubgroup) := (rfl)

/-- `F.stabilizerBialgHom R` sends `single g r` to `single (QuotientAddGroup.mk g) r`. -/
@[simp]
theorem stabilizerBialgHom_single (R : Type*) [CommSemiring R]
    (g : AddSubgroup.closure (S : Set G)) (r : R) :
    F.stabilizerBialgHom R (single g r) = single (QuotientAddGroup.mk g) r := mapDomain_single

/-- `F.stabilizerBialgHom R` is surjective. -/
theorem stabilizerBialgHom_surjective (R : Type*) [CommSemiring R] :
    Function.Surjective (F.stabilizerBialgHom R) := fun y ↦ by
  induction y using AddMonoidAlgebra.induction_linear with
  | zero => exact ⟨0, map_zero _⟩
  | add _ _ h₁ h₂ => rcases h₁, h₂ with ⟨⟨x₁, rfl⟩, ⟨x₂, rfl⟩⟩; exact ⟨x₁ + x₂, map_add _ _ _⟩
  | single q r =>
    obtain ⟨g, rfl⟩ := QuotientAddGroup.mk_surjective q
    exact ⟨single g r, F.stabilizerBialgHom_single R g r⟩

/-- Coaction triviality of `F.stabilizerBialgHom R` on the localized `F`-orbit:
pushing `S.torusCoaction R` forward to `R[L_S ⧸ gp(F)] ⊗[R] R[F.faceSubgroup]` factors through the
right tensor inclusion `Algebra.TensorProduct.includeRight`. -/
theorem map_stabilizerBialgHom_orbitMap_comp_torusCoaction (R : Type*) [CommSemiring R] :
    (Algebra.TensorProduct.map (F.stabilizerBialgHom R).toAlgHom (F.orbitMap R)).comp
      (S.torusCoaction R) =
      Algebra.TensorProduct.includeRight.comp (F.orbitMap R) := by
  ext s
  by_cases hs : s ∈ F
  · have hq : QuotientAddGroup.mk (S.toGroupClosure s) =
        (0 : AddSubgroup.closure (S : Set G) ⧸ F.faceSubgroup) :=
      (QuotientAddGroup.eq_zero_iff _).2 (F.toGroupClosure_mem_faceSubgroup_iff.2 hs)
    rw [AlgHom.comp_apply, AlgHom.comp_apply, S.torusCoaction_single,
      Algebra.TensorProduct.map_tmul, BialgHom.coe_toAlgHom, F.stabilizerBialgHom_single, hq,
      ← one_def, F.orbitMap_single_of_mem R hs, Algebra.TensorProduct.includeRight_apply]
  · simp [F.orbitMap_single_of_notMem R hs]

/-- A torus character `χ` fixes `F.distinguishedPoint R A` if and only if `χ` is trivial on
`F.faceSubgroup`. -/
theorem mem_stabilizer_distinguishedPoint_iff {R A : Type*} [CommSemiring R] [CommSemiring A]
    [Algebra R A] {χ : Multiplicative (AddSubgroup.closure (S : Set G)) →* Aˣ} :
    χ ∈ MulAction.stabilizer _ (F.distinguishedPoint R A) ↔
      ∀ g ∈ F.faceSubgroup, χ (.ofAdd g) = 1 := by
  rw [MulAction.mem_stabilizer_iff]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have hker : F.faceSubgroup ≤ (AddMonoidHom.ker χ.toAdditiveRight) := by
      rw [faceSubgroup_def, AddSubgroup.closure_le]
      rintro _ ⟨a, haF, rfl⟩
      have eval := AlgHom.congr_fun h (single a (1 : R))
      rw [S.smul_algHom_single_apply, F.distinguishedPoint_single_of_mem R A haF, map_one,
        mul_one] at eval
      exact Additive.toMul.injective (Units.ext eval)
    exact fun g hg ↦ Additive.toMul.injective (hker hg)
  · ext s
    by_cases hs : s ∈ F
    · rw [S.smul_algHom_single_apply, h (S.toGroupClosure s)
        (F.toGroupClosure_mem_faceSubgroup_iff.2 hs), Units.val_one, one_mul]
    · simp [F.distinguishedPoint_single_of_notMem R A hs]

/-- Canonical multiplicative isomorphism between the stabilizer of `F.distinguishedPoint R A` in
the torus character group and `Multiplicative (AddSubgroup.closure S ⧸ F.faceSubgroup) →* Aˣ`. -/
noncomputable def stabilizerDistinguishedPointMulEquiv (R A : Type*) [CommSemiring R]
    [CommSemiring A] [Algebra R A] :
    MulAction.stabilizer (Multiplicative (AddSubgroup.closure (S : Set G)) →* Aˣ)
      (F.distinguishedPoint R A) ≃*
      (Multiplicative (AddSubgroup.closure (S : Set G) ⧸ F.faceSubgroup) →* Aˣ) :=
  (MulEquiv.subgroupCongr (by
    ext χ
    rw [F.mem_stabilizer_distinguishedPoint_iff, MonoidHom.mem_ker, MonoidHom.ext_iff]
    exact ⟨fun h x ↦ h x.toAdd.val x.toAdd.property, fun h g hg ↦ h (.ofAdd ⟨g, hg⟩)⟩)).trans
    (F.faceSubgroup.kerCompHomSubtypeMulEquiv Aˣ)

/-- Applying `stabilizerDistinguishedPointMulEquiv` on the class of `g` evaluates the character at
`g`. -/
@[simp]
theorem stabilizerDistinguishedPointMulEquiv_apply (R A : Type*) [CommSemiring R] [CommSemiring A]
    [Algebra R A]
    (χ : MulAction.stabilizer (Multiplicative (AddSubgroup.closure (S : Set G)) →* Aˣ)
      (F.distinguishedPoint R A))
    (g : AddSubgroup.closure (S : Set G)) :
    F.stabilizerDistinguishedPointMulEquiv R A χ (.ofAdd (QuotientAddGroup.mk g)) =
      χ.val (.ofAdd g) := by
  simp [stabilizerDistinguishedPointMulEquiv]

/-- The inverse of `stabilizerDistinguishedPointMulEquiv` precomposes with the quotient map. -/
@[simp]
theorem stabilizerDistinguishedPointMulEquiv_symm_apply_coe (R A : Type*) [CommSemiring R]
    [CommSemiring A] [Algebra R A]
    (ψ : Multiplicative (AddSubgroup.closure (S : Set G) ⧸ F.faceSubgroup) →* Aˣ) :
    ((F.stabilizerDistinguishedPointMulEquiv R A).symm ψ :
      Multiplicative (AddSubgroup.closure (S : Set G)) →* Aˣ) =
      ψ.comp (QuotientAddGroup.mk' F.faceSubgroup).toMultiplicative := by
  simp [stabilizerDistinguishedPointMulEquiv]

end Stabilizer

end SaturatedAddSubmonoid

namespace AddSubmonoid

section PointSupport

variable {G : Type*} [AddCommGroup G] (S : AddSubmonoid G)
  {R A : Type*} [CommSemiring R] [CommSemiring A] [NoZeroDivisors A] [Nontrivial A] [Algebra R A]

/-- Over a nontrivial semiring `A` with no zero divisors, the monomials on which an `A`-point
`x : R[S] →ₐ[R] A` does not vanish form a face `S.pointSupport x : SaturatedAddSubmonoid S`. -/
def pointSupport (x : AddMonoidAlgebra R S →ₐ[R] A) : SaturatedAddSubmonoid S where
  carrier := {s : S | x (single s 1) ≠ 0}
  zero_mem' := by
    rw [Set.mem_ofPred_eq, ← one_def, map_one]
    exact one_ne_zero
  add_mem' {a b} ha hb := by
    rw [Set.mem_ofPred_eq, ← one_mul (1 : R), ← single_mul_single, map_mul]
    exact mul_ne_zero ha hb
  addSaturated {a b} hab := by
    simp only [AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, Set.mem_ofPred_eq] at hab ⊢
    rw [← one_mul (1 : R), ← single_mul_single, map_mul] at hab
    exact ⟨left_ne_zero_of_mul hab, right_ne_zero_of_mul hab⟩

/-- An element `s : S` lies in `S.pointSupport x` iff `x (single s 1) ≠ 0`. -/
@[simp]
theorem mem_pointSupport_iff {S : AddSubmonoid G} {x : AddMonoidAlgebra R S →ₐ[R] A} {s : S} :
    s ∈ S.pointSupport x ↔ x (single s 1) ≠ 0 := Iff.rfl

/-- `pointSupport` is invariant under the action of the dense torus. -/
@[simp]
theorem pointSupport_smul {S : AddSubmonoid G}
    (χ : Multiplicative (AddSubgroup.closure (S : Set G)) →* Aˣ)
    (x : AddMonoidAlgebra R S →ₐ[R] A) :
    S.pointSupport (χ • x) = S.pointSupport x :=
  SetLike.ext fun s ↦ by simp [(χ (.ofAdd (S.toGroupClosure s))).isUnit.mul_right_eq_zero]

/-- The support of `F.distinguishedPoint R A` is `F`. -/
@[simp]
theorem _root_.SaturatedAddSubmonoid.pointSupport_distinguishedPoint (F : SaturatedAddSubmonoid S) :
    S.pointSupport (F.distinguishedPoint R A) = F := SetLike.ext fun s ↦ by
  by_cases hs : s ∈ F
  · simp [hs]
  · simp [hs, F.distinguishedPoint_single_of_notMem R A hs]

/-- An `A`-point `x : R[S] →ₐ[R] A` factors through the closed face subscheme `V(F.faceIdeal R)` if
and only if `S.pointSupport x ≤ F`. -/
theorem faceIdeal_le_ker_iff_pointSupport_le (F : SaturatedAddSubmonoid S)
    (x : AddMonoidAlgebra R S →ₐ[R] A) :
    F.toAddSubmonoid.faceIdeal R ≤ RingHom.ker x ↔ S.pointSupport x ≤ F := by
  rw [F.toAddSubmonoid.faceIdeal_def, Ideal.span_le]
  refine ⟨fun h s hs ↦ by_contra fun hnot ↦ hs (h ⟨s, hnot, of'_apply s⟩), ?_⟩
  rintro h _ ⟨s, hnot, rfl⟩
  rw [SetLike.mem_coe, RingHom.mem_ker, of'_apply]
  exact by_contra fun hne ↦ hnot (h hne)

end PointSupport

end AddSubmonoid

namespace SaturatedAddSubmonoid

section OrbitParametrization

variable {G : Type*} [AddCommGroup G] {S : AddSubmonoid G} (F : SaturatedAddSubmonoid S)

/-- The `A`-point of `Spec R[S]` on the `F`-orbit attached to a character
`ψ : Multiplicative F.faceSubgroup →* Aˣ`. -/
noncomputable def pointOfChar (R : Type*) [CommSemiring R] {A : Type*} [CommSemiring A]
    [Algebra R A] (ψ : Multiplicative F.faceSubgroup →* Aˣ) :
    AddMonoidAlgebra R S →ₐ[R] A :=
  (AddMonoidAlgebra.lift R A F.faceSubgroup ((Units.coeHom A).comp ψ)).comp (F.orbitMap R)

/-- Explicit definition of `SaturatedAddSubmonoid.pointOfChar`. -/
theorem pointOfChar_def (R : Type*) [CommSemiring R] {A : Type*} [CommSemiring A] [Algebra R A]
    (ψ : Multiplicative F.faceSubgroup →* Aˣ) :
    F.pointOfChar R ψ =
      (AddMonoidAlgebra.lift R A F.faceSubgroup ((Units.coeHom A).comp ψ)).comp (F.orbitMap R) :=
  (rfl)

/-- On a monomial in `F`, `F.pointOfChar R ψ` sends `single a r` to
`r • ψ (F.toFaceSubgroup a)`. -/
theorem pointOfChar_single_mem (R : Type*) [CommSemiring R] {A : Type*} [CommSemiring A]
    [Algebra R A] (ψ : Multiplicative F.faceSubgroup →* Aˣ) (a : F) (r : R) :
    F.pointOfChar R ψ (single (a : S) r) = r • (ψ (.ofAdd (F.toFaceSubgroup a)) : A) := by
  simp [pointOfChar]

/-- On a monomial whose exponent lies in `F`, `F.pointOfChar R ψ` sends `single s r` to
`r • ψ (F.toFaceSubgroup ⟨s, hs⟩)`. -/
@[simp]
theorem pointOfChar_single_of_mem (R : Type*) [CommSemiring R] {A : Type*} [CommSemiring A]
    [Algebra R A] (ψ : Multiplicative F.faceSubgroup →* Aˣ) {s : S} (hs : s ∈ F) (r : R) :
    F.pointOfChar R ψ (single s r) = r • (ψ (.ofAdd (F.toFaceSubgroup ⟨s, hs⟩)) : A) :=
  F.pointOfChar_single_mem R ψ ⟨s, hs⟩ r

/-- On a monomial outside `F`, `F.pointOfChar R ψ` vanishes. -/
@[simp]
theorem pointOfChar_single_of_notMem (R : Type*) [CommSemiring R] {A : Type*} [CommSemiring A]
    [Algebra R A] (ψ : Multiplicative F.faceSubgroup →* Aˣ) {s : S} (hs : s ∉ F) (r : R) :
    F.pointOfChar R ψ (single s r) = 0 := by simp [pointOfChar, F.orbitMap_single_of_notMem R hs]

/-- At the trivial character `1`, `F.pointOfChar R 1` is `F.distinguishedPoint R A`. -/
@[simp]
theorem pointOfChar_one (R A : Type*) [CommSemiring R] [CommSemiring A] [Algebra R A] :
    F.pointOfChar R (1 : Multiplicative F.faceSubgroup →* Aˣ) = F.distinguishedPoint R A := by
  ext s
  by_cases hs : s ∈ F
  · simp [hs, Algebra.algebraMap_eq_smul_one]
  · simp [F.pointOfChar_single_of_notMem R _ hs, F.distinguishedPoint_single_of_notMem R A hs]

/-- Equivariance of `F.pointOfChar R` under the ambient torus character action. -/
@[simp]
theorem smul_pointOfChar (R : Type*) [CommSemiring R] {A : Type*} [CommSemiring A] [Algebra R A]
    (χ : Multiplicative (AddSubgroup.closure (S : Set G)) →* Aˣ)
    (ψ : Multiplicative F.faceSubgroup →* Aˣ) :
    χ • F.pointOfChar R ψ =
      F.pointOfChar R (χ.comp F.faceSubgroup.subtype.toMultiplicative * ψ) := by
  ext s
  by_cases hs : s ∈ F
  · rw [S.smul_algHom_single_apply, F.pointOfChar_single_of_mem R _ hs,
      F.pointOfChar_single_of_mem R _ hs]
    simp [F.coe_toFaceSubgroup]
  · simp [F.pointOfChar_single_of_notMem R _ hs]

/-- Over a nontrivial domain `A`, `F.pointOfChar R ψ` has support `F`. -/
@[simp]
theorem pointSupport_pointOfChar (R : Type*) [CommSemiring R] {A : Type*} [CommSemiring A]
    [NoZeroDivisors A] [Nontrivial A] [Algebra R A] (ψ : Multiplicative F.faceSubgroup →* Aˣ) :
    S.pointSupport (F.pointOfChar R ψ) = F := SetLike.ext fun s ↦ by
  by_cases hs : s ∈ F
  · simp [hs, (ψ _).ne_zero]
  · simp [hs, F.pointOfChar_single_of_notMem R ψ hs]

/-- `F.pointOfChar R` is injective over any commutative `R`-algebra `A`. -/
theorem pointOfChar_injective (R A : Type*) [CommSemiring R] [CommSemiring A] [Algebra R A] :
    Function.Injective (F.pointOfChar R (A := A)) := fun ψ₁ ψ₂ h ↦ by
  have honF (a : F) : ψ₁ (.ofAdd (F.toFaceSubgroup a)) = ψ₂ (.ofAdd (F.toFaceSubgroup a)) := by
    have eval := AlgHom.congr_fun h (single (a : S) (1 : R))
    rw [F.pointOfChar_single_mem, F.pointOfChar_single_mem, one_smul, one_smul] at eval
    exact Units.ext eval
  refine MonoidHom.ext fun g ↦ ?_
  obtain ⟨a, b, hab⟩ := F.exists_add_toFaceSubgroup_eq g.toAdd
  apply mul_right_cancel (b := ψ₁ (.ofAdd (F.toFaceSubgroup b)))
  rw [← ofAdd_toAdd g, ← map_mul, ← ofAdd_add, hab, honF a, ← hab, ofAdd_add, map_mul, honF b]

/-- Over any field `K` that is an `R`-algebra, every `K`-point of `Spec R[S]` with support `F`
arises from a character `Multiplicative F.faceSubgroup →* Kˣ`. -/
theorem exists_pointOfChar_eq_of_pointSupport_eq {R K : Type*} [CommSemiring R] [Field K]
    [Algebra R K] {x : AddMonoidAlgebra R S →ₐ[R] K} (hx : S.pointSupport x = F) :
    ∃ ψ : Multiplicative F.faceSubgroup →* Kˣ, F.pointOfChar R ψ = x := by
  let := (mapDomainRingHom R F.toFaceSubgroup).toAlgebra
  have := F.isLocalization_addMonoidAlgebra_faceSubgroup R
  have : IsScalarTower R (AddMonoidAlgebra R F) (AddMonoidAlgebra R F.faceSubgroup) :=
    IsScalarTower.of_algebraMap_eq fun r ↦ by rw [RingHom.algebraMap_toAlgebra]; simp
  let xF : AddMonoidAlgebra R F →ₐ[R] K :=
    x.comp (mapDomainAlgHom R R F.toAddSubmonoid.subtype)
  have hxF_unit (y : MonoidHom.mrange (of R F)) : IsUnit (xF y) := by
    obtain ⟨m, hm⟩ := y.property
    have hy : (y : AddMonoidAlgebra R F) = single m.toAdd (1 : R) := by
      rw [← hm, of_apply]
    rw [hy]
    simp only [xF, AlgHom.comp_apply, mapDomainAlgHom_apply, mapDomain_single]
    exact (S.mem_pointSupport_iff.1 (hx ▸ m.toAdd.property)).isUnit
  let xgp : AddMonoidAlgebra R F.faceSubgroup →ₐ[R] K := IsLocalization.liftAlgHom hxF_unit
  let ψ : Multiplicative F.faceSubgroup →* Kˣ :=
    ((AddMonoidAlgebra.lift R K F.faceSubgroup).symm xgp).toHomUnits
  refine ⟨ψ, ?_⟩
  ext s
  by_cases hs : s ∈ F
  · have halg : algebraMap (AddMonoidAlgebra R F) (AddMonoidAlgebra R F.faceSubgroup)
        (single (⟨s, hs⟩ : F) 1) = single (F.toFaceSubgroup ⟨s, hs⟩) 1 := by
      rw [RingHom.algebraMap_toAlgebra, mapDomainRingHom_apply, mapDomain_single]
    have hxgp : xgp (single (F.toFaceSubgroup ⟨s, hs⟩) 1) = x (single s 1) := by
      rw [← halg, IsLocalization.liftAlgHom_apply, IsLocalization.lift_eq,
        AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
      simp [xF]
      rfl
    rw [F.pointOfChar_single_of_mem R ψ hs, one_smul]
    simpa [ψ, AddMonoidAlgebra.lift_symm_apply] using hxgp
  · have hx0 : x (single s 1) = 0 := by_contra fun hne ↦ hs (hx ▸ hne)
    rw [F.pointOfChar_single_of_notMem R ψ hs, hx0]

/-- Over any field `K` that is an `R`-algebra, `K`-points of `Spec R[S]` with support `F` correspond
bijectively to characters `Multiplicative F.faceSubgroup →* Kˣ`. -/
noncomputable def pointSupportSubtypeEquivChar (R K : Type*) [CommSemiring R] [Field K]
    [Algebra R K] :
    {x : AddMonoidAlgebra R S →ₐ[R] K // S.pointSupport x = F} ≃
      (Multiplicative F.faceSubgroup →* Kˣ) :=
  (Equiv.ofBijective (fun ψ ↦ ⟨F.pointOfChar R ψ, F.pointSupport_pointOfChar R ψ⟩)
    ⟨fun _ _ h ↦ F.pointOfChar_injective R K (congrArg Subtype.val h), fun ⟨_, hx⟩ ↦ by
      obtain ⟨ψ, rfl⟩ := F.exists_pointOfChar_eq_of_pointSupport_eq hx
      exact ⟨ψ, rfl⟩⟩).symm

/-- Inverse of `pointSupportSubtypeEquivChar` evaluates to `F.pointOfChar R ψ`. -/
@[simp]
theorem coe_pointSupportSubtypeEquivChar_symm_apply (R K : Type*) [CommSemiring R] [Field K]
    [Algebra R K] (ψ : Multiplicative F.faceSubgroup →* Kˣ) :
    ((F.pointSupportSubtypeEquivChar R K).symm ψ : AddMonoidAlgebra R S →ₐ[R] K) =
      F.pointOfChar R ψ := (rfl)

/-- Evaluating `pointSupportSubtypeEquivChar` at `F.toFaceSubgroup a` recovers the value of `x` on
`single a 1`. -/
@[simp]
theorem coe_pointSupportSubtypeEquivChar_apply_toFaceSubgroup (R K : Type*) [CommSemiring R]
    [Field K] [Algebra R K] (x : {x : AddMonoidAlgebra R S →ₐ[R] K // S.pointSupport x = F})
    (a : F) :
    (F.pointSupportSubtypeEquivChar R K x (.ofAdd (F.toFaceSubgroup a)) : K) =
      x.val (single (a : S) 1) := by
  have hx : F.pointOfChar R (F.pointSupportSubtypeEquivChar R K x) = x.val :=
    congrArg Subtype.val ((F.pointSupportSubtypeEquivChar R K).symm_apply_apply x)
  simpa using AlgHom.congr_fun hx (single (a : S) 1)

/-- Over any field `K` with divisible unit group (`[RootableBy Kˣ ℕ]`, automatic when `K` is
algebraically closed), the set of `K`-points of `Spec R[S]` with support `F` equals the torus orbit
of `F.distinguishedPoint R K`. -/
theorem setOf_pointSupport_eq_orbit (R K : Type*) [CommSemiring R] [Field K] [RootableBy Kˣ ℕ]
    [Algebra R K] :
    {x : AddMonoidAlgebra R S →ₐ[R] K | S.pointSupport x = F} =
      MulAction.orbit (Multiplicative (AddSubgroup.closure (S : Set G)) →* Kˣ)
        (F.distinguishedPoint R K) := Set.ext fun x ↦ by
  rw [MulAction.mem_orbit_iff]
  refine ⟨fun hx ↦ ?_,
    fun ⟨χ, hχ⟩ ↦ hχ ▸ (S.pointSupport_smul χ _).trans F.pointSupport_distinguishedPoint⟩
  let ψ := F.pointSupportSubtypeEquivChar R K ⟨x, hx⟩
  have hx_eq : x = F.pointOfChar R ψ :=
    congrArg Subtype.val ((F.pointSupportSubtypeEquivChar R K).symm_apply_apply ⟨x, hx⟩).symm
  obtain ⟨χ, hχ⟩ :=
    RootableBy.exists_monoidHom_comp_toMultiplicative_eq F.faceSubgroup.subtype_injective ψ
  exact ⟨χ, by rw [← F.pointOfChar_one R K, F.smul_pointOfChar, hχ, mul_one ψ, hx_eq]⟩

end OrbitParametrization

end SaturatedAddSubmonoid

namespace AddSubmonoid

section OrbitBijection

variable {G : Type*} [AddCommGroup G] (S : AddSubmonoid G)

/-- **Orbit–face bijection on geometric points.** Over any field `K` that is an `R`-algebra with
`[RootableBy Kˣ ℕ]` (in particular any algebraically closed field `K`), the faces
`SaturatedAddSubmonoid S` of `S` correspond bijectively to the orbits of the dense torus
`(Multiplicative (AddSubgroup.closure S) →* Kˣ)` on `K`-points `R[S] →ₐ[R] K`, sending `F` to the
orbit of `F.distinguishedPoint R K` and an orbit `⟦x⟧` to `S.pointSupport x`. -/
noncomputable def faceOrbitEquiv (R K : Type*) [CommSemiring R] [Field K] [RootableBy Kˣ ℕ]
    [Algebra R K] :
    SaturatedAddSubmonoid S ≃
      MulAction.orbitRel.Quotient
        (Multiplicative (AddSubgroup.closure (S : Set G)) →* Kˣ)
        (AddMonoidAlgebra R S →ₐ[R] K) where
  toFun F := ⟦F.distinguishedPoint R K⟧
  invFun := Quotient.lift (S.pointSupport (R := R) (A := K)) fun _ y ⟨χ, hχ⟩ ↦
    hχ ▸ S.pointSupport_smul χ y
  left_inv F := F.pointSupport_distinguishedPoint
  right_inv q := by
    obtain ⟨x, rfl⟩ := Quotient.exists_rep q
    apply Quotient.sound
    have hx : x ∈ {y : AddMonoidAlgebra R S →ₐ[R] K | S.pointSupport y = S.pointSupport x} := rfl
    rw [(S.pointSupport x).setOf_pointSupport_eq_orbit R K] at hx
    exact MulAction.mem_orbit_symm.1 hx

/-- `S.faceOrbitEquiv R K` sends `F` to the torus orbit of `F.distinguishedPoint R K`. -/
@[simp]
theorem faceOrbitEquiv_apply (R K : Type*) [CommSemiring R] [Field K] [RootableBy Kˣ ℕ]
    [Algebra R K] (F : SaturatedAddSubmonoid S) :
    S.faceOrbitEquiv R K F = ⟦F.distinguishedPoint R K⟧ := (rfl)

/-- The inverse of `S.faceOrbitEquiv R K` sends the torus orbit of `x` to `S.pointSupport x`. -/
@[simp]
theorem faceOrbitEquiv_symm_mk (R K : Type*) [CommSemiring R] [Field K] [RootableBy Kˣ ℕ]
    [Algebra R K] (x : AddMonoidAlgebra R S →ₐ[R] K) :
    (S.faceOrbitEquiv R K).symm ⟦x⟧ = S.pointSupport x := (rfl)

end OrbitBijection

end AddSubmonoid

namespace SaturatedAddSubmonoid

section OrbitNormalization

variable {G : Type*} [AddCommGroup G] {S : AddSubmonoid G}

/-- Precomposing an `A`-point of the normalized semigroup algebra
`R[S.nsmulSaturation ⊓ AddSubgroup.closure S]` with the normalization inclusion pulls `pointSupport`
back via `S.nsmulSaturationInfClosureFaceOrderIso`. -/
@[simp]
theorem _root_.AddSubmonoid.pointSupport_comp_mapDomainAlgHom_inclusion_nsmulSaturation
    {R A : Type*} [CommSemiring R] [CommSemiring A] [NoZeroDivisors A] [Nontrivial A] [Algebra R A]
    (y : AddMonoidAlgebra R
      ↥(S.nsmulSaturation ⊓ (AddSubgroup.closure (S : Set G)).toAddSubmonoid) →ₐ[R] A) :
    S.pointSupport (y.comp (mapDomainAlgHom R R
      (AddSubmonoid.inclusion (le_inf S.le_nsmulSaturation AddSubgroup.subset_closure)))) =
      S.nsmulSaturationInfClosureFaceOrderIso
        ((S.nsmulSaturation ⊓
          (AddSubgroup.closure (S : Set G)).toAddSubmonoid).pointSupport y) :=
  SetLike.ext fun _ ↦ by simp [SaturatedAddSubmonoid.mem_comap]

/-- Character restriction from `F.faceSubgroup.nsmulSaturation` to `F.faceSubgroup`, governing the
normalization map `Spec K[S_sat] → Spec K[S]` on the `F`-orbit. -/
def orbitNormalizationCharHom (F : SaturatedAddSubmonoid S) (A : Type*) [CommSemiring A] :
    (Multiplicative F.faceSubgroup.nsmulSaturation →* Aˣ) →*
      (Multiplicative F.faceSubgroup →* Aˣ) :=
  MonoidHom.compHom' (AddSubgroup.inclusion F.faceSubgroup.le_nsmulSaturation).toMultiplicative

/-- Evaluating `orbitNormalizationCharHom` restricts a character along
`F.faceSubgroup ≤ F.faceSubgroup.nsmulSaturation`. -/
@[simp]
theorem orbitNormalizationCharHom_apply (F : SaturatedAddSubmonoid S) {A : Type*} [CommSemiring A]
    (ψ : Multiplicative F.faceSubgroup.nsmulSaturation →* Aˣ) (g : F.faceSubgroup) :
    F.orbitNormalizationCharHom A ψ (.ofAdd g) =
      ψ (.ofAdd (AddSubgroup.inclusion F.faceSubgroup.le_nsmulSaturation g)) := (rfl)

/-- Under `faceSubgroupNSMulSaturationEquiv`, precomposing a point on the normalized `F`-stratum
with the normalization map `R[S] →ₐ[R] R[S_sat]` corresponds to `F.orbitNormalizationCharHom A`. -/
theorem pointOfChar_comp_mapDomainAlgHom_inclusion_nsmulSaturation (F : SaturatedAddSubmonoid S)
    (R : Type*) [CommSemiring R] {A : Type*} [CommSemiring A] [Algebra R A]
    (ψ : Multiplicative F.faceSubgroup.nsmulSaturation →* Aˣ) :
    (((S.nsmulSaturationInfClosureFaceOrderIso).symm F).pointOfChar R
      (ψ.comp F.faceSubgroupNSMulSaturationEquiv.toAddMonoidHom.toMultiplicative)).comp
      (mapDomainAlgHom R R
        (AddSubmonoid.inclusion (le_inf S.le_nsmulSaturation AddSubgroup.subset_closure))) =
      F.pointOfChar R (F.orbitNormalizationCharHom A ψ) := by
  let inc := AddSubmonoid.inclusion (le_inf S.le_nsmulSaturation AddSubgroup.subset_closure)
  let Fsat := (S.nsmulSaturationInfClosureFaceOrderIso).symm F
  have hmem_iff (s : S) : inc s ∈ Fsat ↔ s ∈ F := by
    rw [← SaturatedAddSubmonoid.mem_comap, ← S.nsmulSaturationInfClosureFaceOrderIso_apply,
      S.nsmulSaturationInfClosureFaceOrderIso.apply_symm_apply]
  ext s
  by_cases hs : s ∈ F
  · have hs_sat : inc s ∈ Fsat := (hmem_iff s).2 hs
    have heq : F.faceSubgroupNSMulSaturationEquiv (Fsat.toFaceSubgroup ⟨inc s, hs_sat⟩) =
        AddSubgroup.inclusion F.faceSubgroup.le_nsmulSaturation (F.toFaceSubgroup ⟨s, hs⟩) :=
      Subtype.ext <| Subtype.ext <| by
        simp only [F.coe_faceSubgroupNSMulSaturationEquiv_apply, Fsat.coe_toFaceSubgroup,
          AddSubmonoid.coe_toGroupClosure, AddSubmonoid.coe_inclusion, AddSubgroup.coe_inclusion,
          F.coe_toFaceSubgroup, inc]
    rw [AlgHom.comp_apply, mapDomainAlgHom_apply, mapDomain_single,
      Fsat.pointOfChar_single_of_mem R _ hs_sat, F.pointOfChar_single_of_mem R _ hs,
      one_smul, one_smul]
    exact congrArg (fun z ↦ (ψ (.ofAdd z) : A)) heq
  · rw [AlgHom.comp_apply, mapDomainAlgHom_apply, mapDomain_single,
      Fsat.pointOfChar_single_of_notMem R _ fun h ↦ hs ((hmem_iff s).1 h),
      F.pointOfChar_single_of_notMem R _ hs]

/-- Whenever `[RootableBy Aˣ ℕ]` (in particular over any algebraically closed field), normalization
maps the `F_sat`-orbit surjectively onto the `F`-orbit in every characteristic. -/
theorem orbitNormalizationCharHom_surjective (F : SaturatedAddSubmonoid S) (A : Type*)
    [CommSemiring A] [RootableBy Aˣ ℕ] :
    Function.Surjective (F.orbitNormalizationCharHom A) :=
  fun ψ ↦ RootableBy.exists_monoidHom_comp_toMultiplicative_eq
    (AddSubgroup.inclusion_injective F.faceSubgroup.le_nsmulSaturation) ψ

/-- The kernel of `F.orbitNormalizationCharHom A` is canonically isomorphic to the character group
of the saturation quotient of `F.faceSubgroup` in `F.faceSubgroup.nsmulSaturation`. -/
def orbitNormalizationCharHomKerEquiv (F : SaturatedAddSubmonoid S) (A : Type*)
    [CommSemiring A] :
    (F.orbitNormalizationCharHom A).ker ≃*
      (Multiplicative (F.faceSubgroup.nsmulSaturation ⧸
        F.faceSubgroup.addSubgroupOf F.faceSubgroup.nsmulSaturation) →* Aˣ) :=
  AddSubgroup.kerCompHomInclusionMulEquiv F.faceSubgroup.le_nsmulSaturation Aˣ

/-- `orbitNormalizationCharHomKerEquiv` evaluates on the class of `x` as `ψ.val (.ofAdd x)`. -/
@[simp]
theorem orbitNormalizationCharHomKerEquiv_apply (F : SaturatedAddSubmonoid S) (A : Type*)
    [CommSemiring A] (ψ : (F.orbitNormalizationCharHom A).ker)
    (x : F.faceSubgroup.nsmulSaturation) :
    F.orbitNormalizationCharHomKerEquiv A ψ (.ofAdd (QuotientAddGroup.mk x)) =
      ψ.val (.ofAdd x) :=
  AddSubgroup.kerCompHomInclusionMulEquiv_apply F.faceSubgroup.le_nsmulSaturation Aˣ ψ x

/-- The inverse of `orbitNormalizationCharHomKerEquiv` precomposes with the quotient map. -/
@[simp]
theorem orbitNormalizationCharHomKerEquiv_symm_apply_coe (F : SaturatedAddSubmonoid S) (A : Type*)
    [CommSemiring A]
    (η : Multiplicative (F.faceSubgroup.nsmulSaturation ⧸
      F.faceSubgroup.addSubgroupOf F.faceSubgroup.nsmulSaturation) →* Aˣ) :
    ((F.orbitNormalizationCharHomKerEquiv A).symm η :
      Multiplicative F.faceSubgroup.nsmulSaturation →* Aˣ) =
      η.comp (QuotientAddGroup.mk'
        (F.faceSubgroup.addSubgroupOf F.faceSubgroup.nsmulSaturation)).toMultiplicative :=
  AddSubgroup.kerCompHomInclusionMulEquiv_symm_apply_coe F.faceSubgroup.le_nsmulSaturation Aˣ η

/-- When `S` is finitely generated and the order of the saturation quotient
`Q_F = F.faceSubgroup.nsmulSaturation ⧸ F.faceSubgroup` is invertible in an algebraically closed
field `K`, every fiber of normalization over the `F`-orbit has cardinality `Nat.card Q_F`. -/
theorem card_orbitNormalizationCharHom_ker (hS : S.FG) (F : SaturatedAddSubmonoid S) (K : Type*)
    [Field K] [IsAlgClosed K]
    [NeZero ((Nat.card (F.faceSubgroup.nsmulSaturation ⧸
      F.faceSubgroup.addSubgroupOf F.faceSubgroup.nsmulSaturation) : ℕ) : K)] :
    Nat.card (F.orbitNormalizationCharHom K).ker =
      Nat.card (F.faceSubgroup.nsmulSaturation ⧸
        F.faceSubgroup.addSubgroupOf F.faceSubgroup.nsmulSaturation) := by
  let Q := F.faceSubgroup.nsmulSaturation ⧸
    F.faceSubgroup.addSubgroupOf F.faceSubgroup.nsmulSaturation
  have : Finite Q := F.finite_quotient_nsmulSaturation_faceSubgroup hS
  have : Finite (Multiplicative Q) := Finite.of_equiv Q Multiplicative.ofAdd
  have hcard : Nat.card (Multiplicative Q) = Nat.card Q := Nat.card_congr Multiplicative.ofAdd
  have hdvd : Monoid.exponent (Multiplicative Q) ∣ Nat.card (Multiplicative Q) := by
    have := Fintype.ofFinite (Multiplicative Q)
    simpa [Nat.card_eq_fintype_card] using Group.exponent_dvd_card (G := Multiplicative Q)
  have : HasEnoughRootsOfUnity K (Monoid.exponent (Multiplicative Q)) :=
    HasEnoughRootsOfUnity.of_dvd K (hcard ▸ hdvd)
  rw [Nat.card_congr (F.orbitNormalizationCharHomKerEquiv K).toEquiv,
    CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity (Multiplicative Q) K, hcard]

/-- Over a characteristic-zero algebraically closed field `K`, normalization is injective (hence
bijective) on the `F`-orbit if and only if `F.faceSubgroup` equals its saturation in
`AddSubgroup.closure S`. -/
theorem orbitNormalizationCharHom_injective_iff_of_charZero (hS : S.FG)
    (F : SaturatedAddSubmonoid S) (K : Type*) [Field K] [IsAlgClosed K] [CharZero K] :
    Function.Injective (F.orbitNormalizationCharHom K) ↔
      F.faceSubgroup = F.faceSubgroup.nsmulSaturation := by
  let Q := F.faceSubgroup.nsmulSaturation ⧸
    F.faceSubgroup.addSubgroupOf F.faceSubgroup.nsmulSaturation
  have : Finite Q := F.finite_quotient_nsmulSaturation_faceSubgroup hS
  have : NeZero ((Nat.card Q : ℕ) : K) := ⟨Nat.cast_ne_zero.2 Nat.card_pos.ne'⟩
  rw [← MonoidHom.ker_eq_bot_iff]
  refine ⟨fun hbot ↦ le_antisymm F.faceSubgroup.le_nsmulSaturation fun z hz ↦ ?_,
    fun heq ↦ eq_bot_iff.2 fun ψ hψ ↦ MonoidHom.ext fun g ↦ by
      rw [← ofAdd_toAdd g]
      exact DFunLike.congr_fun hψ (.ofAdd ⟨g.toAdd.val, heq.ge g.toAdd.property⟩)⟩
  have h1 : Nat.card Q = 1 := by
    have hc := F.card_orbitNormalizationCharHom_ker hS K
    rw [hbot, Nat.card_unique] at hc; exact hc.symm
  have : Subsingleton Q := Finite.card_le_one_iff_subsingleton.1 h1.le
  exact (QuotientAddGroup.eq_zero_iff (⟨z, hz⟩ : F.faceSubgroup.nsmulSaturation)).1
    (Subsingleton.elim (QuotientAddGroup.mk ⟨z, hz⟩ : Q) 0)

/-- In prime characteristic `p`, if every element of the saturation quotient
`F.faceSubgroup.nsmulSaturation ⧸ F.faceSubgroup` is annihilated by a power of `p`, then
normalization induces a bijection on `K`-points of the `F`-orbit over any field `K` of
characteristic `p` with `[RootableBy Kˣ ℕ]` (in particular any algebraically closed field of
characteristic `p`). -/
theorem orbitNormalizationCharHom_bijective_of_charP (F : SaturatedAddSubmonoid S) (K : Type*)
    [Field K] [RootableBy Kˣ ℕ] (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : ∀ q : F.faceSubgroup.nsmulSaturation ⧸
        F.faceSubgroup.addSubgroupOf F.faceSubgroup.nsmulSaturation,
      ∃ e : ℕ, (p ^ e) • q = 0) :
    Function.Bijective (F.orbitNormalizationCharHom K) := by
  refine ⟨(MonoidHom.ker_eq_bot_iff _).1 (eq_bot_iff.2 fun ψ hψ ↦ ?_),
    F.orbitNormalizationCharHom_surjective K⟩
  let η := F.orbitNormalizationCharHomKerEquiv K ⟨ψ, hψ⟩
  have hη : η = 1 := MonoidHom.ext fun q ↦ by
    obtain ⟨e, he⟩ := hp q.toAdd
    have hpow : (η q : K) ^ p ^ e = 1 := by
      rw [← Units.val_pow_eq_pow_val, ← map_pow, ← ofAdd_toAdd q, ← ofAdd_nsmul, he, ofAdd_zero,
        map_one, Units.val_one]
    have hsub : ((η q : K) - 1) ^ p ^ e = 0 := by rw [sub_pow_char_pow, hpow, one_pow, sub_self]
    exact Units.ext (sub_eq_zero.1 (eq_zero_of_pow_eq_zero hsub))
  exact congrArg Subtype.val ((F.orbitNormalizationCharHomKerEquiv K).injective
    (hη.trans (map_one _).symm))

end OrbitNormalization

end SaturatedAddSubmonoid
