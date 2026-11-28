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
public import TauCeti.Algebra.MonoidAlgebra.IntegrallyClosed
public import TauCeti.FieldTheory.IsAlgClosed.Units
public import TauCeti.GroupTheory.Divisible.Basic
public import TauCeti.GroupTheory.QuotientGroup.KerEquiv

/-!
# Diagonalizable-group orbits, stabilizers, and orbit normalization of semigroup algebras

For an additive submonoid `S` of an abelian group `G` and a face `F : SaturatedAddSubmonoid S`,
`Multiplicative (AddSubgroup.closure (S : Set G)) →* Aˣ` acts on `AddMonoidAlgebra R S →ₐ[R] A`
via `S.diagonalizableCoaction R`.

* **Distinguished points and stabilizers:** `F.distinguishedPoint R A`, `F.stabilizerBialgHom R`,
  and `SaturatedAddSubmonoid.stabilizerDistinguishedPointMulEquiv`.
* **Orbit–face bijection:** `S.pointSupport x`, `F.pointOfChar R`,
  `SaturatedAddSubmonoid.pointSupportSubtypeEquivChar`,
  `SaturatedAddSubmonoid.setOf_pointSupport_eq_orbit`, and `AddSubmonoid.faceOrbitEquiv`.
* **Saturation comparison:** `SaturatedAddSubmonoid.orbitSaturationCharHom`,
  `SaturatedAddSubmonoid.fiberMapDomainAlgHomEquivOrbitSaturationCharHom`, and fiber cardinality /
  char-`0` / char-`p` theorems via `F.orbitMap R` and `S.nsmulSaturationInfClosureFaceOrderIso`.
* **Normalization fibers:** `AddSubmonoid.exists_ringHom_comp_algebraMap_eq_of_isIntegralClosure`,
  `SaturatedAddSubmonoid.card_fiber_ringHom_of_isIntegralClosure`,
  `SaturatedAddSubmonoid.subsingleton_fiber_ringHom_iff_of_charZero`, and
  `SaturatedAddSubmonoid.existsUnique_ringHom_of_isIntegralClosure_of_charP`.

## References

* W. Bruns and J. Gubeladze, *Polytopes, Rings, and K-Theory*, Theorem 4.38.
* D. Cox, J. Little and H. Schenck, *Toric Varieties*, Theorem 3.2.6.
* E. Miller and B. Sturmfels, *Combinatorial Commutative Algebra*, Chapter 7.
-/

public section

open scoped TensorProduct
open AddMonoidAlgebra

namespace AddSubmonoid

section DiagonalizableAction

variable {G : Type*} [AddCommGroup G] (S : AddSubmonoid G)
  {R A : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]

/-- Scalar action of `A`-points `Multiplicative (AddSubgroup.closure (S : Set G)) →* Aˣ` on
`AddMonoidAlgebra R S →ₐ[R] A` induced by `S.diagonalizableCoaction R`. -/
noncomputable instance instSMulCharAlgHom :
    SMul (Multiplicative (AddSubgroup.closure (S : Set G)) →* Aˣ)
      (AddMonoidAlgebra R S →ₐ[R] A) where
  smul χ x :=
    (Algebra.TensorProduct.lift
      (AddMonoidAlgebra.lift R A _ ((Units.coeHom A).comp χ)) x
      fun _ _ ↦ Commute.all _ _).comp (S.diagonalizableCoaction R)

/-- Explicit definition of the diagonalizable-group action on `A`-points. -/
theorem smul_algHom_def {S : AddSubmonoid G}
    (χ : Multiplicative (AddSubgroup.closure (S : Set G)) →* Aˣ)
    (x : AddMonoidAlgebra R S →ₐ[R] A) :
    χ • x =
      (Algebra.TensorProduct.lift
        (AddMonoidAlgebra.lift R A _ ((Units.coeHom A).comp χ)) x
        fun _ _ ↦ Commute.all _ _).comp (S.diagonalizableCoaction R) := (rfl)

/-- Acting by `χ` scales `x (single s r)` by `χ (S.toGroupClosure s)`. -/
@[simp]
theorem smul_algHom_single_apply {S : AddSubmonoid G}
    (χ : Multiplicative (AddSubgroup.closure (S : Set G)) →* Aˣ)
    (x : AddMonoidAlgebra R S →ₐ[R] A) (s : S) (r : R) :
    (χ • x) (single s r) = (χ (.ofAdd (S.toGroupClosure s)) : A) * x (single s r) := by
  rw [smul_algHom_def, AlgHom.comp_apply]; simp

/-- Multiplicative action of `A`-points `Multiplicative (AddSubgroup.closure (S : Set G)) →* Aˣ`
on `AddMonoidAlgebra R S →ₐ[R] A` via `S.diagonalizableCoaction R`. -/
noncomputable instance instMulActionCharAlgHom :
    MulAction (Multiplicative (AddSubgroup.closure (S : Set G)) →* Aˣ)
      (AddMonoidAlgebra R S →ₐ[R] A) where
  one_smul x := by ext; simp
  mul_smul χ₁ χ₂ x := by ext; simp [mul_assoc]

end DiagonalizableAction

end AddSubmonoid

namespace SaturatedAddSubmonoid

section Stabilizer

variable {G : Type*} [AddCommGroup G] {S : AddSubmonoid G} (F : SaturatedAddSubmonoid S)

/-- The distinguished `A`-point of `Spec R[S]` associated to `F`, obtained by composing
`F.orbitMap R` with the bialgebra counit of `R[F.faceSubgroup]`. -/
noncomputable def distinguishedPoint (R A : Type*) [CommSemiring R] [CommSemiring A] [Algebra R A] :
    AddMonoidAlgebra R S →ₐ[R] A :=
  (Algebra.ofId R A).comp ((Bialgebra.counitAlgHom R (AddMonoidAlgebra R F.faceSubgroup)).comp
    (F.orbitMap R))

/-- Explicit definition of `SaturatedAddSubmonoid.distinguishedPoint`. -/
theorem distinguishedPoint_def (R A : Type*) [CommSemiring R] [CommSemiring A] [Algebra R A] :
    F.distinguishedPoint R A = (Algebra.ofId R A).comp
      ((Bialgebra.counitAlgHom R (AddMonoidAlgebra R F.faceSubgroup)).comp (F.orbitMap R)) := (rfl)

/-- On a monomial with exponent in `F`, `F.distinguishedPoint R A` gives `algebraMap R A r`. -/
@[simp]
theorem distinguishedPoint_single_of_mem (R A : Type*) [CommSemiring R] [CommSemiring A]
    [Algebra R A] {s : S} (hs : s ∈ F) (r : R) :
    F.distinguishedPoint R A (single s r) = algebraMap R A r := by simp [distinguishedPoint, hs]

/-- On a monomial outside `F`, `F.distinguishedPoint R A` vanishes. -/
@[simp]
theorem distinguishedPoint_single_of_notMem (R A : Type*) [CommSemiring R] [CommSemiring A]
    [Algebra R A] {s : S} (hs : s ∉ F) (r : R) :
    F.distinguishedPoint R A (single s r) = 0 := by simp [distinguishedPoint, hs]

/-- The surjective bialgebra quotient
`R[AddSubgroup.closure S] →ₐc[R] R[AddSubgroup.closure S ⧸ F.faceSubgroup]`. -/
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
    Function.Surjective (F.stabilizerBialgHom R) :=
  mapDomain_surjective (QuotientAddGroup.mk'_surjective F.faceSubgroup)

/-- Pushing `S.diagonalizableCoaction R` forward via `F.stabilizerBialgHom R` and `F.orbitMap R`
factors through the right tensor inclusion `Algebra.TensorProduct.includeRight`. -/
theorem map_stabilizerBialgHom_orbitMap_comp_diagonalizableCoaction (R : Type*) [CommSemiring R] :
    (Algebra.TensorProduct.map (F.stabilizerBialgHom R).toAlgHom (F.orbitMap R)).comp
      (S.diagonalizableCoaction R) = Algebra.TensorProduct.includeRight.comp (F.orbitMap R) := by
  ext s; by_cases hs : s ∈ F
  · have hq : QuotientAddGroup.mk (S.toGroupClosure s) =
        (0 : AddSubgroup.closure (S : Set G) ⧸ F.faceSubgroup) :=
      (QuotientAddGroup.eq_zero_iff _).2 (F.toGroupClosure_mem_faceSubgroup_iff.2 hs)
    simp [hq, F.orbitMap_single_of_mem R hs, ← one_def]
  · simp [F.orbitMap_single_of_notMem R hs]

/-- An `A`-valued character fixes `F.distinguishedPoint R A` iff it is trivial on
`F.faceSubgroup`. -/
theorem mem_stabilizer_distinguishedPoint_iff {R A : Type*} [CommSemiring R] [CommSemiring A]
    [Algebra R A] {χ : Multiplicative (AddSubgroup.closure (S : Set G)) →* Aˣ} :
    χ ∈ MulAction.stabilizer _ (F.distinguishedPoint R A) ↔
      ∀ g ∈ F.faceSubgroup, χ (.ofAdd g) = 1 := by
  rw [MulAction.mem_stabilizer_iff]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have hker : F.faceSubgroup ≤ AddMonoidHom.ker χ.toAdditiveRight := by
      rw [faceSubgroup_def, AddSubgroup.closure_le]
      rintro _ ⟨a, haF, rfl⟩
      have eval := AlgHom.congr_fun h (single a (1 : R))
      rw [S.smul_algHom_single_apply, F.distinguishedPoint_single_of_mem R A haF, map_one,
        mul_one] at eval
      exact Additive.toMul.injective (Units.ext eval)
    exact fun g hg ↦ Additive.toMul.injective (hker hg)
  · ext s; by_cases hs : s ∈ F
    · rw [S.smul_algHom_single_apply,
        h (S.toGroupClosure s) (F.toGroupClosure_mem_faceSubgroup_iff.2 hs), Units.val_one, one_mul]
    · simp [F.distinguishedPoint_single_of_notMem R A hs]

/-- Canonical multiplicative isomorphism between the stabilizer of `F.distinguishedPoint R A` and
`Multiplicative (AddSubgroup.closure S ⧸ F.faceSubgroup) →* Aˣ`. -/
noncomputable def stabilizerDistinguishedPointMulEquiv (R A : Type*) [CommSemiring R]
    [CommSemiring A] [Algebra R A] :
    MulAction.stabilizer (Multiplicative (AddSubgroup.closure (S : Set G)) →* Aˣ)
      (F.distinguishedPoint R A) ≃*
      (Multiplicative (AddSubgroup.closure (S : Set G) ⧸ F.faceSubgroup) →* Aˣ) :=
  (MulEquiv.subgroupCongr (by
    ext χ; rw [F.mem_stabilizer_distinguishedPoint_iff, MonoidHom.mem_ker, MonoidHom.ext_iff]
    exact ⟨fun h x ↦ h x.toAdd.val x.toAdd.property, fun h g hg ↦ h (.ofAdd ⟨g, hg⟩)⟩)).trans
    (F.faceSubgroup.kerCompHomSubtypeMulEquiv Aˣ)

/-- Applying `stabilizerDistinguishedPointMulEquiv` on the class of `g` evaluates
`χ.val (.ofAdd g)`. -/
@[simp]
theorem stabilizerDistinguishedPointMulEquiv_apply (R A : Type*) [CommSemiring R] [CommSemiring A]
    [Algebra R A]
    (χ : MulAction.stabilizer (Multiplicative (AddSubgroup.closure (S : Set G)) →* Aˣ)
      (F.distinguishedPoint R A)) (g : AddSubgroup.closure (S : Set G)) :
    F.stabilizerDistinguishedPointMulEquiv R A χ (.ofAdd (QuotientAddGroup.mk g)) =
      χ.val (.ofAdd g) := by simp [stabilizerDistinguishedPointMulEquiv]

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
  zero_mem' := by rw [Set.mem_ofPred_eq, ← one_def, map_one]; exact one_ne_zero
  add_mem' {a b} ha hb := by
    rw [Set.mem_ofPred_eq, ← one_mul (1 : R), ← single_mul_single, map_mul]; exact mul_ne_zero ha hb
  addSaturated {a b} hab := by
    simp only [AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, Set.mem_ofPred_eq] at hab ⊢
    rw [← one_mul (1 : R), ← single_mul_single, map_mul] at hab
    exact ⟨left_ne_zero_of_mul hab, right_ne_zero_of_mul hab⟩

/-- An element `s : S` lies in `S.pointSupport x` iff `x (single s 1) ≠ 0`. -/
@[simp]
theorem mem_pointSupport_iff {S : AddSubmonoid G} {x : AddMonoidAlgebra R S →ₐ[R] A} {s : S} :
    s ∈ S.pointSupport x ↔ x (single s 1) ≠ 0 := Iff.rfl

/-- `pointSupport` is invariant under the action of `A`-points
`Multiplicative (AddSubgroup.closure S) →* Aˣ`. -/
@[simp]
theorem pointSupport_smul {S : AddSubmonoid G}
    (χ : Multiplicative (AddSubgroup.closure (S : Set G)) →* Aˣ)
    (x : AddMonoidAlgebra R S →ₐ[R] A) : S.pointSupport (χ • x) = S.pointSupport x :=
  SetLike.ext fun s ↦ by simp [(χ (.ofAdd (S.toGroupClosure s))).isUnit.mul_right_eq_zero]

/-- The support of `F.distinguishedPoint R A` is `F`. -/
@[simp]
theorem _root_.SaturatedAddSubmonoid.pointSupport_distinguishedPoint (F : SaturatedAddSubmonoid S) :
    S.pointSupport (F.distinguishedPoint R A) = F :=
  SetLike.ext fun s ↦ by by_cases hs : s ∈ F <;> simp [hs, F.distinguishedPoint_single_of_notMem]

/-- An `A`-point `x : R[S] →ₐ[R] A` factors through the closed face subscheme `V(F.faceIdeal R)` if
and only if `S.pointSupport x ≤ F`. -/
theorem faceIdeal_le_ker_iff_pointSupport_le (F : SaturatedAddSubmonoid S)
    (x : AddMonoidAlgebra R S →ₐ[R] A) :
    F.toAddSubmonoid.faceIdeal R ≤ RingHom.ker x ↔ S.pointSupport x ≤ F := by
  rw [F.toAddSubmonoid.faceIdeal_def, Ideal.span_le]
  exact ⟨fun h s hs ↦ by_contra fun hnot ↦ hs (h ⟨s, hnot, of'_apply s⟩), fun h _ ⟨s, hnot, hm⟩ ↦
    by rw [← hm, SetLike.mem_coe, RingHom.mem_ker, of'_apply]; exact by_contra (hnot <| h ·)⟩

end PointSupport

end AddSubmonoid

namespace SaturatedAddSubmonoid

section OrbitParametrization

variable {G : Type*} [AddCommGroup G] {S : AddSubmonoid G} (F : SaturatedAddSubmonoid S)

/-- The `A`-point of `Spec R[S]` factoring through `F.orbitMap R` attached to
`ψ : Multiplicative F.faceSubgroup →* Aˣ`. -/
noncomputable def pointOfChar (R : Type*) [CommSemiring R] {A : Type*} [CommSemiring A]
    [Algebra R A] (ψ : Multiplicative F.faceSubgroup →* Aˣ) : AddMonoidAlgebra R S →ₐ[R] A :=
  (AddMonoidAlgebra.lift R A F.faceSubgroup ((Units.coeHom A).comp ψ)).comp (F.orbitMap R)

/-- Explicit definition of `SaturatedAddSubmonoid.pointOfChar`. -/
theorem pointOfChar_def (R : Type*) [CommSemiring R] {A : Type*} [CommSemiring A] [Algebra R A]
    (ψ : Multiplicative F.faceSubgroup →* Aˣ) : F.pointOfChar R ψ =
      (AddMonoidAlgebra.lift R A F.faceSubgroup ((Units.coeHom A).comp ψ)).comp
        (F.orbitMap R) := (rfl)

/-- On a monomial with exponent in `F`, `F.pointOfChar R ψ` gives
`r • ψ (F.toFaceSubgroup ⟨s, hs⟩)`. -/
@[simp]
theorem pointOfChar_single_of_mem (R : Type*) [CommSemiring R] {A : Type*} [CommSemiring A]
    [Algebra R A] (ψ : Multiplicative F.faceSubgroup →* Aˣ) {s : S} (hs : s ∈ F) (r : R) :
    F.pointOfChar R ψ (single s r) = r • (ψ (.ofAdd (F.toFaceSubgroup ⟨s, hs⟩)) : A) := by
  simp [pointOfChar, hs]

/-- On a monomial outside `F`, `F.pointOfChar R ψ` vanishes. -/
@[simp]
theorem pointOfChar_single_of_notMem (R : Type*) [CommSemiring R] {A : Type*} [CommSemiring A]
    [Algebra R A] (ψ : Multiplicative F.faceSubgroup →* Aˣ) {s : S} (hs : s ∉ F) (r : R) :
    F.pointOfChar R ψ (single s r) = 0 := by simp [pointOfChar, F.orbitMap_single_of_notMem R hs]

/-- At the trivial character `1`, `F.pointOfChar R 1` is `F.distinguishedPoint R A`. -/
@[simp]
theorem pointOfChar_one (R A : Type*) [CommSemiring R] [CommSemiring A] [Algebra R A] :
    F.pointOfChar R (1 : Multiplicative F.faceSubgroup →* Aˣ) = F.distinguishedPoint R A := by
  ext s; by_cases hs : s ∈ F <;> simp [hs, Algebra.algebraMap_eq_smul_one]

/-- Equivariance of `F.pointOfChar R` under `A`-points via restriction to `F.faceSubgroup`. -/
@[simp]
theorem smul_pointOfChar (R : Type*) [CommSemiring R] {A : Type*} [CommSemiring A] [Algebra R A]
    (χ : Multiplicative (AddSubgroup.closure (S : Set G)) →* Aˣ)
    (ψ : Multiplicative F.faceSubgroup →* Aˣ) : χ • F.pointOfChar R ψ =
      F.pointOfChar R (χ.comp F.faceSubgroup.subtype.toMultiplicative * ψ) := by
  ext s; by_cases hs : s ∈ F
  · rw [S.smul_algHom_single_apply, F.pointOfChar_single_of_mem R _ hs,
      F.pointOfChar_single_of_mem R _ hs]; simp [F.coe_toFaceSubgroup]
  · simp [F.pointOfChar_single_of_notMem R _ hs]

/-- Over a nontrivial domain `A`, `F.pointOfChar R ψ` has support `F`. -/
@[simp]
theorem pointSupport_pointOfChar (R : Type*) [CommSemiring R] {A : Type*} [CommSemiring A]
    [NoZeroDivisors A] [Nontrivial A] [Algebra R A] (ψ : Multiplicative F.faceSubgroup →* Aˣ) :
    S.pointSupport (F.pointOfChar R ψ) = F :=
  SetLike.ext fun s ↦ by by_cases hs : s ∈ F <;> simp [hs, (ψ _).ne_zero]

/-- `F.pointOfChar R` is injective over any commutative `R`-algebra `A`. -/
theorem pointOfChar_injective (R A : Type*) [CommSemiring R] [CommSemiring A] [Algebra R A] :
    Function.Injective (F.pointOfChar R (A := A)) := fun ψ₁ ψ₂ h ↦ by
  have honF (a : F) : ψ₁ (.ofAdd (F.toFaceSubgroup a)) = ψ₂ (.ofAdd (F.toFaceSubgroup a)) := by
    have eval := AlgHom.congr_fun h (single (a : S) (1 : R))
    rw [F.pointOfChar_single_of_mem R _ a.property, F.pointOfChar_single_of_mem R _ a.property,
      one_smul, one_smul] at eval
    exact Units.ext eval
  refine MonoidHom.ext fun g ↦ ?_
  obtain ⟨a, b, hab⟩ := F.exists_add_toFaceSubgroup_eq g.toAdd
  apply mul_right_cancel (b := ψ₁ (.ofAdd (F.toFaceSubgroup b)))
  rw [← ofAdd_toAdd g, ← map_mul, ← ofAdd_add, hab, honF a, ← hab, ofAdd_add, map_mul, honF b]

/-- Over a field `K`, every `K`-point with support `F` arises from a character on
`F.faceSubgroup`. -/
theorem exists_pointOfChar_eq_of_pointSupport_eq {R K : Type*} [CommSemiring R] [Field K]
    [Algebra R K] {x : AddMonoidAlgebra R S →ₐ[R] K} (hx : S.pointSupport x = F) :
    ∃ ψ : Multiplicative F.faceSubgroup →* Kˣ, F.pointOfChar R ψ = x := by
  let := (mapDomainRingHom R F.toFaceSubgroup).toAlgebra
  have := F.isLocalization_addMonoidAlgebra_faceSubgroup R
  have : IsScalarTower R (AddMonoidAlgebra R F) (AddMonoidAlgebra R F.faceSubgroup) :=
    IsScalarTower.of_algebraMap_eq fun r ↦ by rw [RingHom.algebraMap_toAlgebra]; simp
  let xF : AddMonoidAlgebra R F →ₐ[R] K := x.comp (mapDomainAlgHom R R F.toAddSubmonoid.subtype)
  have hxF_unit (y : MonoidHom.mrange (of R F)) : IsUnit (xF y) := by
    obtain ⟨m, hm⟩ := y.property
    rw [show (y : AddMonoidAlgebra R F) = single m.toAdd (1 : R) by rw [← hm, of_apply]]
    simpa [xF] using (S.mem_pointSupport_iff.1 (hx ▸ m.toAdd.property)).isUnit
  let xgp : AddMonoidAlgebra R F.faceSubgroup →ₐ[R] K := IsLocalization.liftAlgHom hxF_unit
  let ψ : Multiplicative F.faceSubgroup →* Kˣ :=
    ((AddMonoidAlgebra.lift R K F.faceSubgroup).symm xgp).toHomUnits
  refine ⟨ψ, ?_⟩
  ext s; by_cases hs : s ∈ F
  · have halg : algebraMap (AddMonoidAlgebra R F) (AddMonoidAlgebra R F.faceSubgroup)
        (single (⟨s, hs⟩ : F) 1) = single (F.toFaceSubgroup ⟨s, hs⟩) 1 := by
      simp [RingHom.algebraMap_toAlgebra]
    have hxgp : xgp (single (F.toFaceSubgroup ⟨s, hs⟩) 1) = x (single s 1) := by
      have hsub : F.toAddSubmonoid.subtype ⟨s, hs⟩ = s := AddSubmonoid.subtype_apply _
      simp [← halg, xgp, xF, IsLocalization.lift_eq, hsub]
    rw [F.pointOfChar_single_of_mem R ψ hs, one_smul]
    simpa [ψ, AddMonoidAlgebra.lift_symm_apply] using hxgp
  · rw [F.pointOfChar_single_of_notMem R ψ hs, by_contra fun hne ↦ hs (hx ▸ hne)]

/-- Bijection between `K`-points of `Spec R[S]` with support `F` and characters on
`F.faceSubgroup`. -/
noncomputable def pointSupportSubtypeEquivChar (R K : Type*) [CommSemiring R] [Field K]
    [Algebra R K] : {x : AddMonoidAlgebra R S →ₐ[R] K // S.pointSupport x = F} ≃
      (Multiplicative F.faceSubgroup →* Kˣ) :=
  (Equiv.ofBijective (fun ψ ↦ ⟨F.pointOfChar R ψ, F.pointSupport_pointOfChar R ψ⟩)
    ⟨fun _ _ h ↦ F.pointOfChar_injective R K (congrArg Subtype.val h), fun ⟨_, hx⟩ ↦ by
      obtain ⟨ψ, rfl⟩ := F.exists_pointOfChar_eq_of_pointSupport_eq hx; exact ⟨ψ, rfl⟩⟩).symm

/-- Inverse of `pointSupportSubtypeEquivChar` evaluates to `F.pointOfChar R ψ`. -/
@[simp]
theorem coe_pointSupportSubtypeEquivChar_symm_apply (R K : Type*) [CommSemiring R] [Field K]
    [Algebra R K] (ψ : Multiplicative F.faceSubgroup →* Kˣ) :
    ((F.pointSupportSubtypeEquivChar R K).symm ψ : AddMonoidAlgebra R S →ₐ[R] K) =
      F.pointOfChar R ψ := (rfl)

/-- Applying `F.pointOfChar R` to `F.pointSupportSubtypeEquivChar R K x` recovers `x.val`. -/
@[simp]
theorem pointOfChar_pointSupportSubtypeEquivChar (R K : Type*) [CommSemiring R] [Field K]
    [Algebra R K] (x : {x : AddMonoidAlgebra R S →ₐ[R] K // S.pointSupport x = F}) :
    F.pointOfChar R (F.pointSupportSubtypeEquivChar R K x) = x.val :=
  congrArg Subtype.val ((F.pointSupportSubtypeEquivChar R K).symm_apply_apply x)

/-- Evaluating `pointSupportSubtypeEquivChar` at `F.toFaceSubgroup a` gives `x.val (single a 1)`. -/
@[simp]
theorem coe_pointSupportSubtypeEquivChar_apply_toFaceSubgroup (R K : Type*) [CommSemiring R]
    [Field K] [Algebra R K] (x : {x : AddMonoidAlgebra R S →ₐ[R] K // S.pointSupport x = F})
    (a : F) :
    (F.pointSupportSubtypeEquivChar R K x (.ofAdd (F.toFaceSubgroup a)) : K) =
      x.val (single (a : S) 1) := by
  have hx := AlgHom.congr_fun (F.pointOfChar_pointSupportSubtypeEquivChar R K x) (single (a : S) 1)
  rwa [F.pointOfChar_single_of_mem R _ a.property, one_smul] at hx

/-- Over a field `K` with `[RootableBy Kˣ ℕ]`, `K`-points with support `F` form the orbit of
`F.distinguishedPoint R K` under `Multiplicative (AddSubgroup.closure (S : Set G)) →* Kˣ`. -/
theorem setOf_pointSupport_eq_orbit (R K : Type*) [CommSemiring R] [Field K] [RootableBy Kˣ ℕ]
    [Algebra R K] :
    {x : AddMonoidAlgebra R S →ₐ[R] K | S.pointSupport x = F} =
      MulAction.orbit (Multiplicative (AddSubgroup.closure (S : Set G)) →* Kˣ)
        (F.distinguishedPoint R K) := Set.ext fun x ↦ by
  rw [MulAction.mem_orbit_iff]
  refine ⟨fun hx ↦ ?_,
    fun ⟨χ, hχ⟩ ↦ hχ ▸ (S.pointSupport_smul χ _).trans F.pointSupport_distinguishedPoint⟩
  let ψ := F.pointSupportSubtypeEquivChar R K ⟨x, hx⟩
  obtain ⟨χ, hχ⟩ := TauCeti.exists_monoidHom_comp_toMultiplicative_eq_of_rootableBy
    F.faceSubgroup.subtype_injective ψ
  exact ⟨χ, by
    rw [← F.pointOfChar_one R K, F.smul_pointOfChar, hχ, mul_one ψ]
    exact F.pointOfChar_pointSupportSubtypeEquivChar R K ⟨x, hx⟩⟩

end OrbitParametrization

end SaturatedAddSubmonoid

namespace AddSubmonoid

section OrbitBijection

variable {G : Type*} [AddCommGroup G] (S : AddSubmonoid G)

/-- **Orbit–face bijection on geometric points.** Over a field `K` with `[RootableBy Kˣ ℕ]`,
faces `SaturatedAddSubmonoid S` correspond bijectively to orbits of
`Multiplicative (AddSubgroup.closure (S : Set G)) →* Kˣ` on `AddMonoidAlgebra R S →ₐ[R] K`. -/
noncomputable def faceOrbitEquiv (R K : Type*) [CommSemiring R] [Field K] [RootableBy Kˣ ℕ]
    [Algebra R K] :
    SaturatedAddSubmonoid S ≃ MulAction.orbitRel.Quotient
      (Multiplicative (AddSubgroup.closure (S : Set G)) →* Kˣ) (AddMonoidAlgebra R S →ₐ[R] K) where
  toFun F := ⟦F.distinguishedPoint R K⟧
  invFun := Quotient.lift (S.pointSupport (R := R) (A := K)) fun _ y ⟨χ, hχ⟩ ↦
    hχ ▸ S.pointSupport_smul χ y
  left_inv F := F.pointSupport_distinguishedPoint
  right_inv q := by
    obtain ⟨x, rfl⟩ := Quotient.exists_rep q
    exact Quotient.sound <| MulAction.mem_orbit_symm.1 <|
      ((S.pointSupport x).setOf_pointSupport_eq_orbit R K).subset rfl

/-- `S.faceOrbitEquiv R K` sends `F` to the orbit of `F.distinguishedPoint R K`. -/
@[simp]
theorem faceOrbitEquiv_apply (R K : Type*) [CommSemiring R] [Field K] [RootableBy Kˣ ℕ]
    [Algebra R K] (F : SaturatedAddSubmonoid S) :
    S.faceOrbitEquiv R K F = ⟦F.distinguishedPoint R K⟧ := (rfl)

/-- The inverse of `S.faceOrbitEquiv R K` sends the orbit of `x` to `S.pointSupport x`. -/
@[simp]
theorem faceOrbitEquiv_symm_mk (R K : Type*) [CommSemiring R] [Field K] [RootableBy Kˣ ℕ]
    [Algebra R K] (x : AddMonoidAlgebra R S →ₐ[R] K) :
    (S.faceOrbitEquiv R K).symm ⟦x⟧ = S.pointSupport x := (rfl)

end OrbitBijection

end AddSubmonoid

namespace SaturatedAddSubmonoid

section OrbitSaturation

variable {G : Type*} [AddCommGroup G] {S : AddSubmonoid G}

/-- Precomposing an `A`-point of `R[S.nsmulSaturation ⊓ AddSubgroup.closure S]` with the
saturation inclusion pulls `pointSupport` back via `S.nsmulSaturationInfClosureFaceOrderIso`. -/
@[simp]
theorem _root_.AddSubmonoid.pointSupport_comp_mapDomainAlgHom_inclusion_nsmulSaturation
    {R A : Type*} [CommSemiring R] [CommSemiring A] [NoZeroDivisors A] [Nontrivial A] [Algebra R A]
    (y : AddMonoidAlgebra R
      ↥(S.nsmulSaturation ⊓ (AddSubgroup.closure (S : Set G)).toAddSubmonoid) →ₐ[R] A) :
    S.pointSupport (y.comp (mapDomainAlgHom R R
      (AddSubmonoid.inclusion (le_inf S.le_nsmulSaturation AddSubgroup.subset_closure)))) =
      S.nsmulSaturationInfClosureFaceOrderIso ((S.nsmulSaturation ⊓
        (AddSubgroup.closure (S : Set G)).toAddSubmonoid).pointSupport y) :=
  SetLike.ext fun _ ↦ by simp [SaturatedAddSubmonoid.mem_comap]

/-- Restriction of `U`-valued characters from `F.faceSubgroup.nsmulSaturation` to
`F.faceSubgroup`. -/
def orbitSaturationCharHom (F : SaturatedAddSubmonoid S) (U : Type*) [CommGroup U] :
    (Multiplicative F.faceSubgroup.nsmulSaturation →* U) →* (Multiplicative F.faceSubgroup →* U) :=
  MonoidHom.compHom' (AddSubgroup.inclusion F.faceSubgroup.le_nsmulSaturation).toMultiplicative

/-- Evaluating `orbitSaturationCharHom` restricts along
`F.faceSubgroup ≤ F.faceSubgroup.nsmulSaturation`. -/
@[simp]
theorem orbitSaturationCharHom_apply (F : SaturatedAddSubmonoid S) {U : Type*} [CommGroup U]
    (ψ : Multiplicative F.faceSubgroup.nsmulSaturation →* U) (g : F.faceSubgroup) :
    F.orbitSaturationCharHom U ψ (.ofAdd g) =
      ψ (.ofAdd (AddSubgroup.inclusion F.faceSubgroup.le_nsmulSaturation g)) := (rfl)

/-- Under `faceSubgroupNSMulSaturationEquiv`, `F_sat.orbitMap R` and `F.orbitMap R` commute with
the saturation inclusion `R[S] →ₐ[R] R[S_sat]` and the transported face-subgroup inclusion
`F.faceSubgroup →+ F_sat.faceSubgroup`. -/
theorem orbitMap_comp_mapDomainAlgHom_inclusion_nsmulSaturation (F : SaturatedAddSubmonoid S)
    (R : Type*) [CommSemiring R] :
    (((S.nsmulSaturationInfClosureFaceOrderIso).symm F).orbitMap R).comp (mapDomainAlgHom R R
        (AddSubmonoid.inclusion (le_inf S.le_nsmulSaturation AddSubgroup.subset_closure))) =
      (mapDomainAlgHom R R (F.faceSubgroupNSMulSaturationEquiv.symm.toAddMonoidHom.comp
        (AddSubgroup.inclusion F.faceSubgroup.le_nsmulSaturation))).comp (F.orbitMap R) := by
  let inc := AddSubmonoid.inclusion (le_inf S.le_nsmulSaturation AddSubgroup.subset_closure)
  let Fsat := (S.nsmulSaturationInfClosureFaceOrderIso).symm F
  have hmem_iff (s : S) : inc s ∈ Fsat ↔ s ∈ F := by
    rw [← SaturatedAddSubmonoid.mem_comap, ← S.nsmulSaturationInfClosureFaceOrderIso_apply,
      S.nsmulSaturationInfClosureFaceOrderIso.apply_symm_apply]
  refine AddMonoidAlgebra.algHom_ext (fun s ↦ ?_) (Subsingleton.elim _ _)
  by_cases hs : s ∈ F
  · have hs_sat : inc s ∈ Fsat := (hmem_iff s).2 hs
    have heq : Fsat.toFaceSubgroup ⟨inc s, hs_sat⟩ =
        F.faceSubgroupNSMulSaturationEquiv.symm.toAddMonoidHom
          (AddSubgroup.inclusion F.faceSubgroup.le_nsmulSaturation (F.toFaceSubgroup ⟨s, hs⟩)) :=
      F.faceSubgroupNSMulSaturationEquiv.eq_symm_apply.2 <| Subtype.ext <| Subtype.ext <| by
        rw [F.coe_faceSubgroupNSMulSaturationEquiv_apply, Fsat.coe_toFaceSubgroup,
          AddSubmonoid.coe_toGroupClosure, AddSubgroup.coe_inclusion, F.coe_toFaceSubgroup,
          AddSubmonoid.coe_toGroupClosure]; rfl
    rw [AlgHom.comp_apply, mapDomainAlgHom_apply, mapDomain_single,
      Fsat.orbitMap_single_of_mem R hs_sat, AlgHom.comp_apply, F.orbitMap_single_of_mem R hs,
      mapDomainAlgHom_apply, mapDomain_single, heq]
    rfl
  · rw [AlgHom.comp_apply, mapDomainAlgHom_apply, mapDomain_single,
      Fsat.orbitMap_single_of_notMem R (fun h ↦ hs ((hmem_iff s).1 h)), AlgHom.comp_apply,
      F.orbitMap_single_of_notMem R hs, map_zero]

/-- Under `faceSubgroupNSMulSaturationEquiv`, precomposition with the saturation inclusion on
`A`-points of `Spec R[F_sat.faceSubgroup]` corresponds to `F.orbitSaturationCharHom Aˣ`. -/
theorem pointOfChar_comp_mapDomainAlgHom_inclusion_nsmulSaturation (F : SaturatedAddSubmonoid S)
    (R : Type*) [CommSemiring R] {A : Type*} [CommSemiring A] [Algebra R A]
    (ψ : Multiplicative F.faceSubgroup.nsmulSaturation →* Aˣ) :
    (((S.nsmulSaturationInfClosureFaceOrderIso).symm F).pointOfChar R
      (ψ.comp F.faceSubgroupNSMulSaturationEquiv.toAddMonoidHom.toMultiplicative)).comp
      (mapDomainAlgHom R R
        (AddSubmonoid.inclusion (le_inf S.le_nsmulSaturation AddSubgroup.subset_closure))) =
      F.pointOfChar R (F.orbitSaturationCharHom Aˣ ψ) := by
  rw [pointOfChar_def, AlgHom.comp_assoc,
    F.orbitMap_comp_mapDomainAlgHom_inclusion_nsmulSaturation R, ← AlgHom.comp_assoc,
    pointOfChar_def]
  congr 1; ext g; simp [AddMonoidHom.toMultiplicative]

/-- Under `[RootableBy U ℕ]`, `F.orbitSaturationCharHom U` is surjective. -/
theorem orbitSaturationCharHom_surjective (F : SaturatedAddSubmonoid S) (U : Type*)
    [CommGroup U] [RootableBy U ℕ] : Function.Surjective (F.orbitSaturationCharHom U) :=
  fun ψ ↦ TauCeti.exists_monoidHom_comp_toMultiplicative_eq_of_rootableBy
    (AddSubgroup.inclusion_injective F.faceSubgroup.le_nsmulSaturation) ψ

/-- The kernel of `F.orbitSaturationCharHom U` is isomorphic to `U`-valued characters of the
saturation quotient `F.faceSubgroup.nsmulSaturation ⧸ F.faceSubgroup`. -/
def orbitSaturationCharHomKerEquiv (F : SaturatedAddSubmonoid S) (U : Type*) [CommGroup U] :
    (F.orbitSaturationCharHom U).ker ≃*
      (Multiplicative (F.faceSubgroup.nsmulSaturation ⧸
        F.faceSubgroup.addSubgroupOf F.faceSubgroup.nsmulSaturation) →* U) :=
  AddSubgroup.kerCompHomInclusionMulEquiv F.faceSubgroup.le_nsmulSaturation U

/-- `orbitSaturationCharHomKerEquiv` evaluates on the class of `x` as `ψ.val (.ofAdd x)`. -/
@[simp]
theorem orbitSaturationCharHomKerEquiv_apply (F : SaturatedAddSubmonoid S) (U : Type*)
    [CommGroup U] (ψ : (F.orbitSaturationCharHom U).ker) (x : F.faceSubgroup.nsmulSaturation) :
    F.orbitSaturationCharHomKerEquiv U ψ (.ofAdd (QuotientAddGroup.mk x)) = ψ.val (.ofAdd x) :=
  AddSubgroup.kerCompHomInclusionMulEquiv_apply F.faceSubgroup.le_nsmulSaturation U ψ x

/-- The inverse of `orbitSaturationCharHomKerEquiv` precomposes with the quotient map. -/
@[simp]
theorem orbitSaturationCharHomKerEquiv_symm_apply_coe (F : SaturatedAddSubmonoid S) (U : Type*)
    [CommGroup U] (η : Multiplicative (F.faceSubgroup.nsmulSaturation ⧸
      F.faceSubgroup.addSubgroupOf F.faceSubgroup.nsmulSaturation) →* U) :
    ((F.orbitSaturationCharHomKerEquiv U).symm η :
      Multiplicative F.faceSubgroup.nsmulSaturation →* U) = η.comp (QuotientAddGroup.mk'
        (F.faceSubgroup.addSubgroupOf F.faceSubgroup.nsmulSaturation)).toMultiplicative :=
  AddSubgroup.kerCompHomInclusionMulEquiv_symm_apply_coe F.faceSubgroup.le_nsmulSaturation U η

/-- When `S.FG` and `Nat.card Q_F` is invertible in an algebraically closed field `K`,
`(F.orbitSaturationCharHom Kˣ).ker` has cardinality `Nat.card Q_F`. -/
theorem card_orbitSaturationCharHom_ker (hS : S.FG) (F : SaturatedAddSubmonoid S) (K : Type*)
    [Field K] [IsAlgClosed K] [NeZero ((Nat.card (F.faceSubgroup.nsmulSaturation ⧸
      F.faceSubgroup.addSubgroupOf F.faceSubgroup.nsmulSaturation) : ℕ) : K)] :
    Nat.card (F.orbitSaturationCharHom Kˣ).ker = Nat.card (F.faceSubgroup.nsmulSaturation ⧸
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
  rw [Nat.card_congr (F.orbitSaturationCharHomKerEquiv Kˣ).toEquiv,
    CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity (Multiplicative Q) K, hcard]

/-- Under the hypotheses of `card_orbitSaturationCharHom_ker`, every fiber of
`F.orbitSaturationCharHom Kˣ` has cardinality `Nat.card Q_F`. -/
theorem card_fiber_orbitSaturationCharHom (hS : S.FG) (F : SaturatedAddSubmonoid S) (K : Type*)
    [Field K] [IsAlgClosed K] [NeZero ((Nat.card (F.faceSubgroup.nsmulSaturation ⧸
      F.faceSubgroup.addSubgroupOf F.faceSubgroup.nsmulSaturation) : ℕ) : K)]
    (ψ : Multiplicative F.faceSubgroup →* Kˣ) :
    Nat.card ((F.orbitSaturationCharHom Kˣ) ⁻¹' {ψ}) = Nat.card (F.faceSubgroup.nsmulSaturation ⧸
      F.faceSubgroup.addSubgroupOf F.faceSubgroup.nsmulSaturation) := by
  obtain ⟨ψ₀, rfl⟩ := F.orbitSaturationCharHom_surjective Kˣ ψ
  rw [Nat.card_congr (MonoidHom.fiberEquivKer (F.orbitSaturationCharHom Kˣ) ψ₀),
    F.card_orbitSaturationCharHom_ker hS K]

/-- Over a char-`0` algebraically closed field `K`, `F.orbitSaturationCharHom Kˣ` is injective iff
`F.faceSubgroup = F.faceSubgroup.nsmulSaturation`. -/
theorem orbitSaturationCharHom_injective_iff_of_charZero (hS : S.FG)
    (F : SaturatedAddSubmonoid S) (K : Type*) [Field K] [IsAlgClosed K] [CharZero K] :
    Function.Injective (F.orbitSaturationCharHom Kˣ) ↔
      F.faceSubgroup = F.faceSubgroup.nsmulSaturation := by
  let Q := F.faceSubgroup.nsmulSaturation ⧸
    F.faceSubgroup.addSubgroupOf F.faceSubgroup.nsmulSaturation
  have : Finite Q := F.finite_quotient_nsmulSaturation_faceSubgroup hS
  have : NeZero ((Nat.card Q : ℕ) : K) := ⟨Nat.cast_ne_zero.2 Nat.card_pos.ne'⟩
  rw [← MonoidHom.ker_eq_bot_iff, ← F.faceSubgroup.subsingleton_quotient_nsmulSaturation_iff,
    ← Finite.card_le_one_iff_subsingleton]
  refine ⟨fun hbot ↦ by rw [← F.card_orbitSaturationCharHom_ker hS K, hbot, Nat.card_unique],
    fun h1 ↦ eq_bot_iff.2 fun ψ hψ ↦ MonoidHom.ext fun g ↦ ?_⟩
  have heq := F.faceSubgroup.subsingleton_quotient_nsmulSaturation_iff.1
    (Finite.card_le_one_iff_subsingleton.1 h1)
  exact ofAdd_toAdd g ▸ DFunLike.congr_fun hψ (.ofAdd ⟨g.toAdd.val, heq.ge g.toAdd.property⟩)

/-- In char `p`, if the saturation quotient is `p`-primary, then `F.orbitSaturationCharHom Kˣ` is
bijective over any char-`p` field `K` with `[RootableBy Kˣ ℕ]`. -/
theorem orbitSaturationCharHom_bijective_of_charP (F : SaturatedAddSubmonoid S) (K : Type*)
    [Field K] [RootableBy Kˣ ℕ] (p : ℕ) [Fact p.Prime] [CharP K p] (hp : ∀ q :
      F.faceSubgroup.nsmulSaturation ⧸ F.faceSubgroup.addSubgroupOf F.faceSubgroup.nsmulSaturation,
      ∃ e : ℕ, (p ^ e) • q = 0) :
    Function.Bijective (F.orbitSaturationCharHom Kˣ) := by
  refine ⟨(MonoidHom.ker_eq_bot_iff _).1 (eq_bot_iff.2 fun ψ hψ ↦ ?_),
    F.orbitSaturationCharHom_surjective Kˣ⟩
  let η := F.orbitSaturationCharHomKerEquiv Kˣ ⟨ψ, hψ⟩
  have hη : η = 1 := MonoidHom.ext fun q ↦ by
    obtain ⟨e, he⟩ := hp q.toAdd
    have hpow : (η q : K) ^ p ^ e = 1 := by
      rw [← Units.val_pow_eq_pow_val, ← map_pow, ← ofAdd_toAdd q, ← ofAdd_nsmul, he, ofAdd_zero,
        map_one, Units.val_one]
    have hsub : ((η q : K) - 1) ^ p ^ e = 0 := by rw [sub_pow_char_pow, hpow, one_pow, sub_self]
    exact Units.ext (sub_eq_zero.1 (eq_zero_of_pow_eq_zero hsub))
  exact congrArg Subtype.val
    ((F.orbitSaturationCharHomKerEquiv Kˣ).injective (hη.trans (map_one _).symm))

/-- If `y : R[S_sat] →ₐ[R] K` restricts to `x : R[S] →ₐ[R] K` with support `F`, then `y` has
support `(S.nsmulSaturationInfClosureFaceOrderIso).symm F`. -/
theorem pointSupport_eq_of_comp_mapDomainAlgHom_inclusion_nsmulSaturation
    (F : SaturatedAddSubmonoid S) {R K : Type*} [CommSemiring R] [Field K] [Algebra R K]
    {x : AddMonoidAlgebra R S →ₐ[R] K} (hx : S.pointSupport x = F)
    {y : AddMonoidAlgebra R
      ↥(S.nsmulSaturation ⊓ (AddSubgroup.closure (S : Set G)).toAddSubmonoid) →ₐ[R] K}
    (hy : y.comp (mapDomainAlgHom R R
      (AddSubmonoid.inclusion (le_inf S.le_nsmulSaturation AddSubgroup.subset_closure))) = x) :
    (S.nsmulSaturation ⊓ (AddSubgroup.closure (S : Set G)).toAddSubmonoid).pointSupport y =
      (S.nsmulSaturationInfClosureFaceOrderIso).symm F :=
  S.nsmulSaturationInfClosureFaceOrderIso.injective <| by
    rw [S.nsmulSaturationInfClosureFaceOrderIso.apply_symm_apply,
      ← S.pointSupport_comp_mapDomainAlgHom_inclusion_nsmulSaturation y, hy, hx]

private theorem comp_faceSubgroupNSMulSaturationEquiv_symm_comp (F : SaturatedAddSubmonoid S)
    {U : Type*} [CommGroup U]
    (ψ : Multiplicative ((S.nsmulSaturationInfClosureFaceOrderIso).symm F).faceSubgroup →* U) :
    (ψ.comp F.faceSubgroupNSMulSaturationEquiv.symm.toAddMonoidHom.toMultiplicative).comp
      F.faceSubgroupNSMulSaturationEquiv.toAddMonoidHom.toMultiplicative = ψ := by ext g; simp

/-- Equivalence between the fiber of `R[S_sat] →ₐ[R] K` over `x` (with `S.pointSupport x = F`)
and the fiber of `F.orbitSaturationCharHom Kˣ` over `F.pointSupportSubtypeEquivChar R K ⟨x, hx⟩`. -/
noncomputable def fiberMapDomainAlgHomEquivOrbitSaturationCharHom
    (F : SaturatedAddSubmonoid S) (R K : Type*) [CommSemiring R] [Field K] [Algebra R K]
    {x : AddMonoidAlgebra R S →ₐ[R] K} (hx : S.pointSupport x = F) :
    {y : AddMonoidAlgebra R
        ↥(S.nsmulSaturation ⊓ (AddSubgroup.closure (S : Set G)).toAddSubmonoid) →ₐ[R] K //
      y.comp (mapDomainAlgHom R R
        (AddSubmonoid.inclusion (le_inf S.le_nsmulSaturation AddSubgroup.subset_closure))) = x} ≃
      ((F.orbitSaturationCharHom Kˣ) ⁻¹' {F.pointSupportSubtypeEquivChar R K ⟨x, hx⟩}) :=
  let Fsat := (S.nsmulSaturationInfClosureFaceOrderIso).symm F
  let eG := F.faceSubgroupNSMulSaturationEquiv.toAddMonoidHom.toMultiplicative
  let eG' := F.faceSubgroupNSMulSaturationEquiv.symm.toAddMonoidHom.toMultiplicative
  { toFun := fun y ↦ ⟨(Fsat.pointSupportSubtypeEquivChar R K
      ⟨y.val, F.pointSupport_eq_of_comp_mapDomainAlgHom_inclusion_nsmulSaturation hx
        y.property⟩).comp eG', by
      apply F.pointOfChar_injective R K
      rw [← F.pointOfChar_comp_mapDomainAlgHom_inclusion_nsmulSaturation R _,
        F.comp_faceSubgroupNSMulSaturationEquiv_symm_comp,
        Fsat.pointOfChar_pointSupportSubtypeEquivChar R K, y.property,
        F.pointOfChar_pointSupportSubtypeEquivChar R K ⟨x, hx⟩]⟩
    invFun := fun ψ ↦ ⟨Fsat.pointOfChar R (ψ.val.comp eG), by
      rw [F.pointOfChar_comp_mapDomainAlgHom_inclusion_nsmulSaturation R ψ.val, ψ.property,
        F.pointOfChar_pointSupportSubtypeEquivChar R K ⟨x, hx⟩]⟩
    left_inv := fun y ↦ Subtype.ext <| by
      dsimp only; rw [F.comp_faceSubgroupNSMulSaturationEquiv_symm_comp]
      exact Fsat.pointOfChar_pointSupportSubtypeEquivChar R K _
    right_inv := fun ψ ↦ Subtype.ext <| by
      have hsymm : Fsat.pointSupportSubtypeEquivChar R K
          ⟨Fsat.pointOfChar R (ψ.val.comp eG), Fsat.pointSupport_pointOfChar R _⟩ =
          ψ.val.comp eG :=
        (Fsat.pointSupportSubtypeEquivChar R K).apply_symm_apply (ψ.val.comp eG)
      dsimp only; rw [hsymm]; ext g; simp [eG, eG'] }

/-- Evaluating `fiberMapDomainAlgHomEquivOrbitSaturationCharHom` restricts along
`F.faceSubgroupNSMulSaturationEquiv.symm`. -/
@[simp]
theorem coe_fiberMapDomainAlgHomEquivOrbitSaturationCharHom_apply
    (F : SaturatedAddSubmonoid S) (R K : Type*) [CommSemiring R] [Field K] [Algebra R K]
    {x : AddMonoidAlgebra R S →ₐ[R] K} (hx : S.pointSupport x = F)
    (y : {y : AddMonoidAlgebra R
        ↥(S.nsmulSaturation ⊓ (AddSubgroup.closure (S : Set G)).toAddSubmonoid) →ₐ[R] K //
      y.comp (mapDomainAlgHom R R
        (AddSubmonoid.inclusion (le_inf S.le_nsmulSaturation AddSubgroup.subset_closure))) = x}) :
    (F.fiberMapDomainAlgHomEquivOrbitSaturationCharHom R K hx y :
        Multiplicative F.faceSubgroup.nsmulSaturation →* Kˣ) =
      (((S.nsmulSaturationInfClosureFaceOrderIso).symm F).pointSupportSubtypeEquivChar R K
        ⟨y.val, F.pointSupport_eq_of_comp_mapDomainAlgHom_inclusion_nsmulSaturation hx
          y.property⟩).comp
        F.faceSubgroupNSMulSaturationEquiv.symm.toAddMonoidHom.toMultiplicative := (rfl)

/-- The inverse of `fiberMapDomainAlgHomEquivOrbitSaturationCharHom` sends `ψ` to
`F_sat.pointOfChar`. -/
@[simp]
theorem coe_fiberMapDomainAlgHomEquivOrbitSaturationCharHom_symm_apply
    (F : SaturatedAddSubmonoid S) (R K : Type*) [CommSemiring R] [Field K] [Algebra R K]
    {x : AddMonoidAlgebra R S →ₐ[R] K} (hx : S.pointSupport x = F)
    (ψ : (F.orbitSaturationCharHom Kˣ) ⁻¹' {F.pointSupportSubtypeEquivChar R K ⟨x, hx⟩}) :
    ((F.fiberMapDomainAlgHomEquivOrbitSaturationCharHom R K hx).symm ψ : AddMonoidAlgebra R
        ↥(S.nsmulSaturation ⊓ (AddSubgroup.closure (S : Set G)).toAddSubmonoid) →ₐ[R] K) =
      ((S.nsmulSaturationInfClosureFaceOrderIso).symm F).pointOfChar R
        (ψ.val.comp F.faceSubgroupNSMulSaturationEquiv.toAddMonoidHom.toMultiplicative) := (rfl)

/-- When `S.FG` and `Nat.card Q_F` is invertible in an algebraically closed field `K`, the fiber
of `R[S_sat] →ₐ[R] K` over `x` with `S.pointSupport x = F` has cardinality `Nat.card Q_F`. -/
theorem card_fiber_mapDomainAlgHom_inclusion_nsmulSaturation (hS : S.FG)
    (F : SaturatedAddSubmonoid S) (R K : Type*) [CommSemiring R] [Field K] [IsAlgClosed K]
    [Algebra R K] [NeZero ((Nat.card (F.faceSubgroup.nsmulSaturation ⧸
      F.faceSubgroup.addSubgroupOf F.faceSubgroup.nsmulSaturation) : ℕ) : K)]
    {x : AddMonoidAlgebra R S →ₐ[R] K} (hx : S.pointSupport x = F) :
    Nat.card {y : AddMonoidAlgebra R
        ↥(S.nsmulSaturation ⊓ (AddSubgroup.closure (S : Set G)).toAddSubmonoid) →ₐ[R] K //
      y.comp (mapDomainAlgHom R R
        (AddSubmonoid.inclusion (le_inf S.le_nsmulSaturation AddSubgroup.subset_closure))) = x} =
      Nat.card (F.faceSubgroup.nsmulSaturation ⧸
        F.faceSubgroup.addSubgroupOf F.faceSubgroup.nsmulSaturation) := by
  rw [Nat.card_congr (F.fiberMapDomainAlgHomEquivOrbitSaturationCharHom R K hx),
    F.card_fiber_orbitSaturationCharHom hS K]

/-- Over a field `K` with `[RootableBy Kˣ ℕ]`, every `K`-point of `R[S]` lifts to `R[S_sat]`. -/
theorem _root_.AddSubmonoid.exists_comp_mapDomainAlgHom_inclusion_nsmulSaturation
    (S : AddSubmonoid G) (R K : Type*) [CommSemiring R] [Field K] [RootableBy Kˣ ℕ] [Algebra R K]
    (x : AddMonoidAlgebra R S →ₐ[R] K) :
    ∃ y : AddMonoidAlgebra R
        ↥(S.nsmulSaturation ⊓ (AddSubgroup.closure (S : Set G)).toAddSubmonoid) →ₐ[R] K,
      y.comp (mapDomainAlgHom R R
        (AddSubmonoid.inclusion (le_inf S.le_nsmulSaturation AddSubgroup.subset_closure))) = x :=
  let F := S.pointSupport x
  have ⟨ψ, hψ⟩ :=
    F.orbitSaturationCharHom_surjective Kˣ (F.pointSupportSubtypeEquivChar R K ⟨x, rfl⟩)
  ⟨_, ((F.fiberMapDomainAlgHomEquivOrbitSaturationCharHom R K rfl).symm ⟨ψ, hψ⟩).property⟩

end OrbitSaturation

section OrbitNormalization

variable {G : Type*} [AddCommGroup G] [Module.IsTorsionFree ℤ G] {S : AddSubmonoid G}

/-- Under `[RootableBy Kˣ ℕ]`, every `K`-point `x : R[S] →ₐ[R] K` lifts along `R[S] →+* B`. -/
theorem _root_.AddSubmonoid.exists_ringHom_comp_algebraMap_eq_of_isIntegralClosure
    (S : AddSubmonoid G) (R L B K : Type*) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [CommRing L] [Algebra (AddMonoidAlgebra R S) L] [IsFractionRing (AddMonoidAlgebra R S) L]
    [CommRing B] [Algebra (AddMonoidAlgebra R S) B] [Algebra B L]
    [IsScalarTower (AddMonoidAlgebra R S) B L] [IsIntegralClosure B (AddMonoidAlgebra R S) L]
    [Field K] [RootableBy Kˣ ℕ] [Algebra R K] (x : AddMonoidAlgebra R S →ₐ[R] K) :
    ∃ z : B →+* K, z.comp (algebraMap (AddMonoidAlgebra R S) B) = x.toRingHom :=
  have ⟨y, hy⟩ := S.exists_comp_mapDomainAlgHom_inclusion_nsmulSaturation R K x
  ⟨_, ((S.fiberIntegralClosureEquivMapDomainAlgHom R L B K x).symm ⟨y, hy⟩).property⟩

/-- When `S.FG` and `Nat.card Q_F` is invertible in an algebraically closed field `K`, the
normalization fiber over `x` with `S.pointSupport x = F` has cardinality `Nat.card Q_F`. -/
theorem card_fiber_ringHom_of_isIntegralClosure (hS : S.FG) (F : SaturatedAddSubmonoid S)
    (R L B K : Type*) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [CommRing L]
    [Algebra (AddMonoidAlgebra R S) L] [IsFractionRing (AddMonoidAlgebra R S) L] [CommRing B]
    [Algebra (AddMonoidAlgebra R S) B] [Algebra B L] [IsScalarTower (AddMonoidAlgebra R S) B L]
    [IsIntegralClosure B (AddMonoidAlgebra R S) L] [Field K] [IsAlgClosed K] [Algebra R K]
    [NeZero ((Nat.card (F.faceSubgroup.nsmulSaturation ⧸
      F.faceSubgroup.addSubgroupOf F.faceSubgroup.nsmulSaturation) : ℕ) : K)]
    {x : AddMonoidAlgebra R S →ₐ[R] K} (hx : S.pointSupport x = F) :
    Nat.card {z : B →+* K // z.comp (algebraMap (AddMonoidAlgebra R S) B) = x.toRingHom} =
      Nat.card (F.faceSubgroup.nsmulSaturation ⧸
        F.faceSubgroup.addSubgroupOf F.faceSubgroup.nsmulSaturation) := by
  rw [Nat.card_congr (S.fiberIntegralClosureEquivMapDomainAlgHom R L B K x),
    F.card_fiber_mapDomainAlgHom_inclusion_nsmulSaturation hS R K hx]

/-- Over a char-`0` algebraically closed field `K` with `S.FG`, the normalization fiber over `x`
with `S.pointSupport x = F` is a singleton iff `F.faceSubgroup = F.faceSubgroup.nsmulSaturation`. -/
theorem subsingleton_fiber_ringHom_iff_of_charZero (hS : S.FG) (F : SaturatedAddSubmonoid S)
    (R L B K : Type*) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [CommRing L]
    [Algebra (AddMonoidAlgebra R S) L] [IsFractionRing (AddMonoidAlgebra R S) L] [CommRing B]
    [Algebra (AddMonoidAlgebra R S) B] [Algebra B L] [IsScalarTower (AddMonoidAlgebra R S) B L]
    [IsIntegralClosure B (AddMonoidAlgebra R S) L] [Field K] [IsAlgClosed K] [CharZero K]
    [Algebra R K] {x : AddMonoidAlgebra R S →ₐ[R] K} (hx : S.pointSupport x = F) :
    Subsingleton {z : B →+* K // z.comp (algebraMap (AddMonoidAlgebra R S) B) = x.toRingHom} ↔
      F.faceSubgroup = F.faceSubgroup.nsmulSaturation := by
  let Q := F.faceSubgroup.nsmulSaturation ⧸
    F.faceSubgroup.addSubgroupOf F.faceSubgroup.nsmulSaturation
  have : Finite Q := F.finite_quotient_nsmulSaturation_faceSubgroup hS
  have : NeZero ((Nat.card Q : ℕ) : K) := ⟨Nat.cast_ne_zero.2 Nat.card_pos.ne'⟩
  have hcard := F.card_fiber_ringHom_of_isIntegralClosure hS R L B K hx
  have : Finite {z : B →+* K // z.comp (algebraMap (AddMonoidAlgebra R S) B) = x.toRingHom} :=
    Nat.finite_of_card_ne_zero (hcard ▸ Nat.card_pos.ne')
  rw [← Finite.card_le_one_iff_subsingleton, hcard, Finite.card_le_one_iff_subsingleton,
    F.faceSubgroup.subsingleton_quotient_nsmulSaturation_iff]

/-- In char `p`, if `Q_F` is `p`-primary and `[RootableBy Kˣ ℕ]`, every `K`-point `x` with
`S.pointSupport x = F` lifts uniquely along the normalization `R[S] →+* B`. -/
theorem existsUnique_ringHom_of_isIntegralClosure_of_charP (F : SaturatedAddSubmonoid S)
    (R L B K : Type*) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [CommRing L]
    [Algebra (AddMonoidAlgebra R S) L] [IsFractionRing (AddMonoidAlgebra R S) L] [CommRing B]
    [Algebra (AddMonoidAlgebra R S) B] [Algebra B L] [IsScalarTower (AddMonoidAlgebra R S) B L]
    [IsIntegralClosure B (AddMonoidAlgebra R S) L] [Field K] [RootableBy Kˣ ℕ] [Algebra R K]
    (p : ℕ) [Fact p.Prime] [CharP K p] (hp : ∀ q : F.faceSubgroup.nsmulSaturation ⧸
      F.faceSubgroup.addSubgroupOf F.faceSubgroup.nsmulSaturation, ∃ e : ℕ, (p ^ e) • q = 0)
    {x : AddMonoidAlgebra R S →ₐ[R] K} (hx : S.pointSupport x = F) :
    ∃! z : B →+* K, z.comp (algebraMap (AddMonoidAlgebra R S) B) = x.toRingHom := by
  let e := (S.fiberIntegralClosureEquivMapDomainAlgHom R L B K x).trans
    (F.fiberMapDomainAlgHomEquivOrbitSaturationCharHom R K hx)
  have hbij := F.orbitSaturationCharHom_bijective_of_charP K p hp
  obtain ⟨ψ, hψ⟩ := hbij.2 (F.pointSupportSubtypeEquivChar R K ⟨x, hx⟩)
  refine ⟨(e.symm ⟨ψ, hψ⟩).val, (e.symm ⟨ψ, hψ⟩).property, fun z hz ↦ ?_⟩
  have : Subsingleton
      ((F.orbitSaturationCharHom Kˣ) ⁻¹' {F.pointSupportSubtypeEquivChar R K ⟨x, hx⟩}) :=
    ⟨fun a b ↦ Subtype.ext (hbij.1 (a.property.trans b.property.symm))⟩
  exact congrArg Subtype.val (e.eq_symm_apply.2 (Subsingleton.elim (e ⟨z, hz⟩) ⟨ψ, hψ⟩))

end OrbitNormalization

end SaturatedAddSubmonoid
