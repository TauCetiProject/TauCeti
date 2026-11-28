/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.MonoidAlgebra.Face.Coaction
public import TauCeti.GroupTheory.Divisible.Basic
public import TauCeti.GroupTheory.QuotientGroup.KerEquiv
import TauCeti.Algebra.MonoidAlgebra.MapDomain

/-!
# Diagonalizable-group orbits and stabilizers of semigroup algebras

For an additive submonoid `S` of an abelian group `G` and a face `F : SaturatedAddSubmonoid S`,
`Multiplicative (AddSubgroup.closure (S : Set G)) →* Aˣ` acts on `AddMonoidAlgebra R S →ₐ[R] A`
via `S.diagonalizableCoaction R` (`TauCeti.Algebra.MonoidAlgebra.DiagonalizableCoaction`).

* **Distinguished points and stabilizers:** `F.distinguishedPoint R A` evaluates monomials on `F`
  to their coefficients and kills monomials outside `F`; `F.stabilizerBialgHom R` is the quotient
  coaction factor, and `SaturatedAddSubmonoid.stabilizerDistinguishedPointMulEquiv` identifies the
  stabilizer with `Multiplicative (AddSubgroup.closure (S : Set G) ⧸ F.faceSubgroup) →* Aˣ`.
* **Orbit–face parametrization:** `S.pointSupport x` is the face of nonvanishing monomials of an
  `A`-point over a nontrivial semiring with no zero divisors. `F.pointOfChar R` parametrizes
  `A`-points factoring through `F.orbitMap R` by characters on `F.faceSubgroup`, yielding
  `SaturatedAddSubmonoid.pointSupportSubtypeEquivChar` over any field `K`.
* **Orbit–face bijection:** when `Kˣ` is divisible (`[RootableBy Kˣ ℕ]`), every character on
  `F.faceSubgroup` extends to `AddSubgroup.closure (S : Set G)`, so `K`-points with support `F`
  form the orbit of `F.distinguishedPoint R K` (`SaturatedAddSubmonoid.setOf_pointSupport_eq_orbit`)
  and faces biject with orbits (`AddSubmonoid.faceOrbitEquiv`).

## References

* W. Bruns and J. Gubeladze, *Polytopes, Rings, and K-Theory*, Theorem 4.38.
* D. Cox, J. Little and H. Schenck, *Toric Varieties*, Theorem 3.2.6.
* E. Miller and B. Sturmfels, *Combinatorial Commutative Algebra*, Chapter 7.
-/

public section

open scoped TensorProduct
open AddMonoidAlgebra

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
  have hmul (ψ : Multiplicative F.faceSubgroup →* Aˣ) :
      ψ g * ψ (.ofAdd (F.toFaceSubgroup b)) = ψ (.ofAdd (F.toFaceSubgroup a)) := by
    rw [← ofAdd_toAdd g, ← map_mul, ← ofAdd_add, hab]
  exact mul_right_cancel (b := ψ₁ (.ofAdd (F.toFaceSubgroup b)))
    ((hmul ψ₁).trans ((honF a).trans ((hmul ψ₂).symm.trans (congrArg (ψ₂ g * ·) (honF b).symm))))

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
    rw [← hm, of_apply]
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
