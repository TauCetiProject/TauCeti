/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.FormalGroup.CoordinateChange.Lazard
public import TauCeti.RingTheory.FormalGroup.LazardRing.Polynomial

/-!
# The grading of the strict coordinate-change ring

The ring `Γ = L[b₁, b₂, …]` carries the combined homological grading: its coefficient ring has
its Lazard grading and `bᵢ` has degree `2i`. In particular, the coefficients of `L` are not
placed in degree zero. The inclusion `L → Γ` and the counit `Γ → L` preserve this grading.

A homomorphism out of `Γ` preserves degrees exactly when its restriction to `L` does and the
images of the `bᵢ` have degree `2i`. Applying the ungraded representing equivalence gives the
graded universal property: graded maps out of `Γ` classify a graded commutative formal group
law together with a strict coordinate whose coefficient of `Xⁿ` has degree `2(n - 1)`.

The construction transports the weighted polynomial grading along Lazard's polynomial
isomorphism. The mapping criterion characterizes it independently of that presentation.
The ring of composable pairs carries the analogous grading, with both families of coordinate
variables in degree `2i`. Its mapping criterion tests the first factor and the variables of
the second coordinate. This supplies the graded coefficient rings for strict formal-group
isomorphisms and their composition. The counit is graded here; the coproduct is graded in
`CoordinateChange.Coproduct`. The right unit and conjugation are graded in
`CoordinateChange.Homogeneous`.

## References

* D. C. Ravenel, *Complex Cobordism and Stable Homotopy Groups of Spheres*, Appendix A2.1.
-/

public section

noncomputable section

namespace TauCeti.LazardRing

open MvPolynomial

/-- The polynomial presentation with the coordinate variables first and the Lazard generators
second. -/
private def coordinatePolynomialEquiv :
    MvPolynomial (ℕ+ ⊕ ℕ+) ℤ ≃ₐ[ℤ] MvPolynomial ℕ+ LazardRing :=
  (sumAlgEquiv ℤ ℕ+ ℕ+).trans (mapAlgEquiv ℕ+ mvPolynomialEquiv)

private theorem coordinatePolynomialEquiv_X (i : ℕ+ ⊕ ℕ+) :
    coordinatePolynomialEquiv (X i) = Sum.elim X (fun j ↦ C (generator j)) i := by
  cases i <;> simp [coordinatePolynomialEquiv, mapAlgEquiv_apply]

/-- The combined homological grading on `L[b₁, b₂, …]`, with `|bᵢ| = 2i` and with the existing
Lazard grading on the coefficient ring. -/
def coordinateGrading (n : ℕ) : Submodule ℤ (MvPolynomial ℕ+ LazardRing) :=
  (weightedHomogeneousSubmodule ℤ (Sum.elim (fun i : ℕ+ ↦ 2 * (i : ℕ))
    (fun i : ℕ+ ↦ 2 * (i : ℕ))) n).map coordinatePolynomialEquiv.toLinearMap

/-- A homogeneous element of the coordinate-change ring is represented by a weighted homogeneous
polynomial in the coordinate variables and Lazard generators, both of degree `2i`. -/
private theorem mem_coordinateGrading_iff {n : ℕ} {x : MvPolynomial ℕ+ LazardRing} :
    x ∈ coordinateGrading n ↔ ∃ p : MvPolynomial (ℕ+ ⊕ ℕ+) ℤ,
      p.IsWeightedHomogeneous (Sum.elim (fun i : ℕ+ ↦ 2 * (i : ℕ))
        (fun i : ℕ+ ↦ 2 * (i : ℕ))) n ∧ coordinatePolynomialEquiv p = x :=
  Iff.rfl

private theorem coordinatePolynomialEquiv_apply (p : MvPolynomial (ℕ+ ⊕ ℕ+) ℤ) :
    coordinatePolynomialEquiv p = aeval (Sum.elim X (fun j ↦ C (generator j))) p := by
  simpa only [Function.comp_def, AlgEquiv.coe_toAlgHom, coordinatePolynomialEquiv_X] using
    DFunLike.congr_fun (aeval_unique coordinatePolynomialEquiv.toAlgHom) p

/-- A homogeneous element is a weighted homogeneous polynomial in the coordinate variables
`bᵢ` and the included Lazard generators `xᵢ`, both of degree `2i`. -/
theorem mem_coordinateGrading_iff_aeval {n : ℕ} {x : MvPolynomial ℕ+ LazardRing} :
    x ∈ coordinateGrading n ↔ ∃ p : MvPolynomial (ℕ+ ⊕ ℕ+) ℤ,
      p.IsWeightedHomogeneous (Sum.elim (fun i : ℕ+ ↦ 2 * (i : ℕ))
        (fun i : ℕ+ ↦ 2 * (i : ℕ))) n ∧
      aeval (Sum.elim X (fun j ↦ C (generator j))) p = x := by
  simp only [mem_coordinateGrading_iff, coordinatePolynomialEquiv_apply]

/-- Multiplication in the coordinate-change ring adds homological degrees. -/
instance : SetLike.GradedMonoid coordinateGrading := by
  unfold coordinateGrading
  exact WeightedHomogeneousSubmodule.gradedMonoid_map _ coordinatePolynomialEquiv

/-- The coordinate-change ring is the direct sum of its combined homogeneous pieces. -/
theorem isInternal_coordinateGrading : DirectSum.IsInternal coordinateGrading := by
  unfold coordinateGrading
  exact WeightedHomogeneousSubmodule.isInternal_map _ coordinatePolynomialEquiv

/-- The combined grading is an algebra grading over the integers. -/
instance : GradedAlgebra coordinateGrading := isInternal_coordinateGrading.gradedAlgebra

/-- The coordinate generator `bᵢ` has homological degree `2i`. -/
@[simp]
theorem X_mem_coordinateGrading (i : ℕ+) : X i ∈ coordinateGrading (2 * (i : ℕ)) := by
  exact mem_coordinateGrading_iff.mpr ⟨X (.inl i), isWeightedHomogeneous_X _ _ _,
    coordinatePolynomialEquiv_X _⟩

/-- Inclusion of coefficients preserves the Lazard grading. -/
theorem C_mem_coordinateGrading {n : ℕ} {x : LazardRing} (hx : x ∈ grading n) :
    C x ∈ coordinateGrading n := by
  obtain ⟨p, rfl⟩ := mvPolynomialEquiv.surjective x
  have hp := mvPolynomialEquiv_mem_grading_iff.mp hx
  refine mem_coordinateGrading_iff.mpr ⟨rename Sum.inr p, ?_, ?_⟩
  · rw [rename_eq_aeval]
    exact hp.aeval fun i ↦ isWeightedHomogeneous_X _ _ (Sum.inr i)
  · have he : coordinatePolynomialEquiv.toAlgHom.comp (rename Sum.inr) =
        (IsScalarTower.toAlgHom ℤ LazardRing (MvPolynomial ℕ+ LazardRing)).comp
          mvPolynomialEquiv.toAlgHom := by
      ext i
      simp [coordinatePolynomialEquiv_X]
    exact DFunLike.congr_fun he p

/-- A map from the coordinate-change ring is graded if and only if its restriction to `L` is
graded and its coordinate coefficients have the prescribed degrees. The target grading may
also be a grading by subgroups rather than submodules. -/
theorem coordinateGrading_map_mem_iff {A σ ι : Type*} [CommRing A] [SetLike σ A]
    [AddSubgroupClass σ A] [AddCommMonoid ι] (𝒜 : ι → σ) [SetLike.GradedMonoid 𝒜]
    (e : ℕ →+ ι) (f : MvPolynomial ℕ+ LazardRing →+* A) :
    (∀ ⦃n⦄ ⦃x⦄, x ∈ coordinateGrading n → f x ∈ 𝒜 (e n)) ↔
      (∀ ⦃n⦄ ⦃x⦄, x ∈ grading n → f (C x) ∈ 𝒜 (e n)) ∧
        ∀ i : ℕ+, f (X i) ∈ 𝒜 (e (2 * (i : ℕ))) := by
  refine ⟨fun h ↦ ⟨fun _ _ hx ↦ h (C_mem_coordinateGrading hx),
    fun i ↦ h (X_mem_coordinateGrading i)⟩, ?_⟩
  rintro ⟨hC, hX⟩ n x hx
  obtain ⟨p, hp, rfl⟩ := mem_coordinateGrading_iff.mp hx
  apply (WeightedHomogeneousSubmodule.map_mem_iff _ 𝒜 e
    (f.comp coordinatePolynomialEquiv.toRingHom)).mpr ?_ hp
  intro i
  simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
    AlgEquiv.coe_toRingEquiv, coordinatePolynomialEquiv_X]
  cases i with
  | inl i => exact hX i
  | inr i => exact hC (generator_mem_grading i)

/-- The counit preserves the combined homological grading. -/
theorem counit_mem_grading {n : ℕ} {x : MvPolynomial ℕ+ LazardRing}
    (hx : x ∈ coordinateGrading n) : counit x ∈ grading n :=
  (coordinateGrading_map_mem_iff grading (.id ℕ) counit).mpr
    ⟨fun _ _ hx ↦ by simpa using hx, fun i ↦ by simp⟩ hx

/-- A coefficient is homogeneous in the combined grading exactly when it is homogeneous in the
Lazard grading. -/
@[simp]
theorem C_mem_coordinateGrading_iff {n : ℕ} {x : LazardRing} :
    C x ∈ coordinateGrading n ↔ x ∈ grading n :=
  ⟨fun hx ↦ by simpa using counit_mem_grading hx, C_mem_coordinateGrading⟩

section UniversalProperty

variable {A σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  {𝒜 : ℕ → σ} [SetLike.GradedMonoid 𝒜]

/-- A classifying map preserves degrees exactly when its formal group coefficients and strict
coordinate coefficients have the homological degrees `2(i + j - 1)` and `2i`, respectively.
An additive map on degrees permits homological or cohomological regrading in the target. -/
theorem coordinateChangeLift_mem_iff {ι : Type*} [AddCommMonoid ι] (ℬ : ι → σ)
    [SetLike.GradedMonoid ℬ] (e : ℕ →+ ι)
    (p : {F : FormalGroup A // F.IsComm} × (FormalCoordinate.linearCoeff (R := A)).ker) :
    (∀ ⦃n⦄ ⦃x⦄, x ∈ coordinateGrading n → coordinateChangeLift p x ∈ ℬ (e n)) ↔
      (∀ d : Fin 2 →₀ ℕ, MvPowerSeries.coeff d p.1.1.toPowerSeries ∈
        ℬ (e (2 * (d.degree - 1)))) ∧
      ∀ i : ℕ+, PowerSeries.coeff (i + 1) p.2.1.toPowerSeries ∈ ℬ (e (2 * (i : ℕ))) := by
  rw [coordinateGrading_map_mem_iff ℬ e]
  simp only [coordinateChangeLift_C, coordinateChangeLift_X, lift_mem_iff e p.1]

/-- The graded universal property of `L[b₁, b₂, …]`: graded classifying maps correspond to
commutative graded formal group laws equipped with strict graded coordinates. -/
def gradedCoordinateChangeLift :
    {p : {F : FormalGroup A // F.IsComm} × (FormalCoordinate.linearCoeff (R := A)).ker //
      (∀ d : Fin 2 →₀ ℕ, MvPowerSeries.coeff d p.1.1.toPowerSeries ∈
        𝒜 (2 * (d.degree - 1))) ∧
      ∀ i : ℕ+, PowerSeries.coeff (i + 1) p.2.1.toPowerSeries ∈ 𝒜 (2 * (i : ℕ))} ≃
      (coordinateGrading →+*ᵍ 𝒜) where
  toFun p :=
    { toRingHom := coordinateChangeLift p.1
      map_mem := fun hx ↦ (coordinateChangeLift_mem_iff 𝒜 (.id ℕ) p.1).mpr p.2 hx }
  invFun f := ⟨coordinateChangeLift.symm f.toRingHom,
    (coordinateChangeLift_mem_iff 𝒜 (.id ℕ) _).mp (by
      rw [Equiv.apply_symm_apply]
      exact fun _ _ hx ↦ f.map_mem hx)⟩
  left_inv p := Subtype.ext (coordinateChangeLift.left_inv p.1)
  right_inv f := GradedRingHom.ext fun x ↦
    DFunLike.congr_fun (coordinateChangeLift.right_inv f.toRingHom) x

/-- Forgetting the grading recovers the original coordinate-change classifying map. -/
@[simp]
theorem toRingHom_gradedCoordinateChangeLift
    (p : {p : {F : FormalGroup A // F.IsComm} × (FormalCoordinate.linearCoeff (R := A)).ker //
      (∀ d : Fin 2 →₀ ℕ, MvPowerSeries.coeff d p.1.1.toPowerSeries ∈
        𝒜 (2 * (d.degree - 1))) ∧
      ∀ i : ℕ+, PowerSeries.coeff (i + 1) p.2.1.toPowerSeries ∈ 𝒜 (2 * (i : ℕ))}) :
    (gradedCoordinateChangeLift p).toRingHom = coordinateChangeLift p.1 :=
  (rfl)

/-- The graded representing equivalence recovers the same underlying law and coordinate as the
ungraded equivalence. -/
@[simp]
theorem coe_gradedCoordinateChangeLift_symm (f : coordinateGrading →+*ᵍ 𝒜) :
    (gradedCoordinateChangeLift.symm f).1 = coordinateChangeLift.symm f.toRingHom :=
  (rfl)

end UniversalProperty

/-! ### The grading on the ring of composable pairs -/

/-- The polynomial presentation of the ring of composable pairs, with the second coordinate
variables first, then the first coordinate variables, then the Lazard generators. -/
private def coordinateTensorPolynomialEquiv :
    MvPolynomial (ℕ+ ⊕ (ℕ+ ⊕ ℕ+)) ℤ ≃ₐ[ℤ]
      MvPolynomial ℕ+ (MvPolynomial ℕ+ LazardRing) :=
  (sumAlgEquiv ℤ ℕ+ (ℕ+ ⊕ ℕ+)).trans (mapAlgEquiv ℕ+ coordinatePolynomialEquiv)

private theorem coordinateTensorPolynomialEquiv_X (i : ℕ+ ⊕ (ℕ+ ⊕ ℕ+)) :
    coordinateTensorPolynomialEquiv (X i) =
      Sum.elim X (Sum.elim (fun j ↦ C (X j)) (fun j ↦ C (C (generator j)))) i := by
  rcases i with i | (i | i) <;>
    simp [coordinateTensorPolynomialEquiv, mapAlgEquiv_apply, coordinatePolynomialEquiv_X]

private abbrev coordinateTensorWeight : ℕ+ ⊕ (ℕ+ ⊕ ℕ+) → ℕ :=
  Sum.elim (fun i : ℕ+ ↦ 2 * (i : ℕ))
    (Sum.elim (fun i : ℕ+ ↦ 2 * (i : ℕ)) (fun i : ℕ+ ↦ 2 * (i : ℕ)))

/-- The combined homological grading on the ring of composable strict coordinate changes
`Γ ⊗_L Γ = L[b₁,b₂,…][b₁',b₂',…]`. Both families of coordinate variables have degree `2i`,
and the coefficient ring retains its Lazard grading. -/
def coordinateTensorGrading (n : ℕ) :
    Submodule ℤ (MvPolynomial ℕ+ (MvPolynomial ℕ+ LazardRing)) :=
  (weightedHomogeneousSubmodule ℤ coordinateTensorWeight n).map
    coordinateTensorPolynomialEquiv.toLinearMap

private theorem mem_coordinateTensorGrading_iff {n : ℕ}
    {x : MvPolynomial ℕ+ (MvPolynomial ℕ+ LazardRing)} :
    x ∈ coordinateTensorGrading n ↔ ∃ p : MvPolynomial (ℕ+ ⊕ (ℕ+ ⊕ ℕ+)) ℤ,
      p.IsWeightedHomogeneous coordinateTensorWeight n ∧
      coordinateTensorPolynomialEquiv p = x := Iff.rfl

/-- Multiplication adds homological degrees in the ring of composable pairs. -/
instance : SetLike.GradedMonoid coordinateTensorGrading := by
  unfold coordinateTensorGrading
  exact WeightedHomogeneousSubmodule.gradedMonoid_map _ coordinateTensorPolynomialEquiv

/-- The ring of composable pairs is the direct sum of its homogeneous pieces. -/
theorem isInternal_coordinateTensorGrading : DirectSum.IsInternal coordinateTensorGrading := by
  unfold coordinateTensorGrading
  exact WeightedHomogeneousSubmodule.isInternal_map _ coordinateTensorPolynomialEquiv

/-- The combined homological grading makes the ring of composable pairs a graded algebra. -/
instance : GradedAlgebra coordinateTensorGrading :=
  isInternal_coordinateTensorGrading.gradedAlgebra

/-- The second coordinate variable has homological degree `2i`. -/
@[simp]
theorem X_mem_coordinateTensorGrading (i : ℕ+) :
    X i ∈ coordinateTensorGrading (2 * (i : ℕ)) :=
  mem_coordinateTensorGrading_iff.mpr ⟨X (.inl i), isWeightedHomogeneous_X _ _ _,
    coordinateTensorPolynomialEquiv_X _⟩

/-- Inclusion of the first factor preserves the combined homological grading. -/
theorem C_mem_coordinateTensorGrading {n : ℕ} {x : MvPolynomial ℕ+ LazardRing}
    (hx : x ∈ coordinateGrading n) : C x ∈ coordinateTensorGrading n := by
  obtain ⟨p, hp, rfl⟩ := mem_coordinateGrading_iff.mp hx
  refine mem_coordinateTensorGrading_iff.mpr ⟨rename Sum.inr p, ?_, ?_⟩
  · rw [rename_eq_aeval]
    exact hp.aeval fun i ↦ isWeightedHomogeneous_X _ _ (Sum.inr i)
  · have he : coordinateTensorPolynomialEquiv.toAlgHom.comp (rename Sum.inr) =
        (IsScalarTower.toAlgHom ℤ (MvPolynomial ℕ+ LazardRing)
          (MvPolynomial ℕ+ (MvPolynomial ℕ+ LazardRing))).comp
            coordinatePolynomialEquiv.toAlgHom := by
      ext i
      rcases i with i | i <;> simp [coordinateTensorPolynomialEquiv_X, coordinatePolynomialEquiv_X]
    simpa only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, IsScalarTower.toAlgHom_apply,
      MvPolynomial.algebraMap_eq] using DFunLike.congr_fun he p

private theorem coordinateTensorPolynomialEquiv_apply
    (p : MvPolynomial (ℕ+ ⊕ (ℕ+ ⊕ ℕ+)) ℤ) :
    coordinateTensorPolynomialEquiv p = aeval
      (Sum.elim X (Sum.elim (fun j ↦ C (X j)) (fun j ↦ C (C (generator j))))) p := by
  simpa only [Function.comp_def, AlgEquiv.coe_toAlgHom, coordinateTensorPolynomialEquiv_X] using
    DFunLike.congr_fun (aeval_unique coordinateTensorPolynomialEquiv.toAlgHom) p

-- The public statement spells out the weights because `coordinateTensorWeight` is private.
/-- A homogeneous element of the ring of composable pairs is a weighted homogeneous polynomial
in the two families of coordinate variables and the Lazard generators, all of degree `2i`. -/
theorem mem_coordinateTensorGrading_iff_aeval {n : ℕ}
    {x : MvPolynomial ℕ+ (MvPolynomial ℕ+ LazardRing)} :
    x ∈ coordinateTensorGrading n ↔ ∃ p : MvPolynomial (ℕ+ ⊕ (ℕ+ ⊕ ℕ+)) ℤ,
      p.IsWeightedHomogeneous (Sum.elim (fun i : ℕ+ ↦ 2 * (i : ℕ))
        (Sum.elim (fun i : ℕ+ ↦ 2 * (i : ℕ)) (fun i : ℕ+ ↦ 2 * (i : ℕ)))) n ∧
      aeval (Sum.elim X (Sum.elim (fun j ↦ C (X j)) (fun j ↦ C (C (generator j))))) p = x := by
  simp only [mem_coordinateTensorGrading_iff, coordinateTensorPolynomialEquiv_apply]

/-- A ring map on composable pairs preserves degrees exactly when its restriction to the
first factor does and its second coordinate coefficients have degrees `2i`. -/
theorem coordinateTensorGrading_map_mem_iff {A σ ι : Type*} [CommRing A] [SetLike σ A]
    [AddSubgroupClass σ A] [AddCommMonoid ι] (𝒜 : ι → σ) [SetLike.GradedMonoid 𝒜]
    (e : ℕ →+ ι) (f : MvPolynomial ℕ+ (MvPolynomial ℕ+ LazardRing) →+* A) :
    (∀ ⦃n⦄ ⦃x⦄, x ∈ coordinateTensorGrading n → f x ∈ 𝒜 (e n)) ↔
      (∀ ⦃n⦄ ⦃x⦄, x ∈ coordinateGrading n → f (C x) ∈ 𝒜 (e n)) ∧
        ∀ i : ℕ+, f (X i) ∈ 𝒜 (e (2 * (i : ℕ))) := by
  refine ⟨fun h ↦ ⟨fun _ _ hx ↦ h (C_mem_coordinateTensorGrading hx),
    fun i ↦ h (X_mem_coordinateTensorGrading i)⟩, ?_⟩
  rintro ⟨hC, hX⟩ n x hx
  obtain ⟨p, hp, rfl⟩ := mem_coordinateTensorGrading_iff.mp hx
  apply (WeightedHomogeneousSubmodule.map_mem_iff _ 𝒜 e
    (f.comp coordinateTensorPolynomialEquiv.toRingHom)).mpr ?_ hp
  intro i
  simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
    AlgEquiv.coe_toRingEquiv, coordinateTensorPolynomialEquiv_X]
  rcases i with i | (i | i)
  · exact hX i
  · exact hC (X_mem_coordinateGrading i)
  · exact hC (C_mem_coordinateGrading (generator_mem_grading i))

/-- Inclusion of the first factor preserves and reflects homogeneity. -/
@[simp]
theorem C_mem_coordinateTensorGrading_iff {n : ℕ} {x : MvPolynomial ℕ+ LazardRing} :
    C x ∈ coordinateTensorGrading n ↔ x ∈ coordinateGrading n := by
  refine ⟨fun hx ↦ ?_, C_mem_coordinateTensorGrading⟩
  have h := (coordinateTensorGrading_map_mem_iff coordinateGrading (.id ℕ)
    (eval₂Hom (RingHom.id _) 0)).mpr
      ⟨fun _ _ hy ↦ by simpa using hy, fun i ↦ by simp⟩ hx
  simpa using h

end TauCeti.LazardRing
