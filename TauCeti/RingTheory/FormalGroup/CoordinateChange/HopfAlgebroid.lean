/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Monad
public import TauCeti.RingTheory.FormalGroup.CoordinateChange.Lazard

/-!
# The Hopf algebroid `(L, L[b₁, b₂, …])` of strict coordinate changes

Write `Γ = L[b₁, b₂, …] = MvPolynomial ℕ+ LazardRing`. Ring homomorphisms `Γ →+* R` classify pairs
`(F, φ)` of a commutative formal group law `F` over `R` and a strict coordinate
`φ = X + ∑ bᵢ X^(i + 1)`, that is, strict isomorphisms `φ : F → φ • F`
(`TauCeti.LazardRing.coordinateChangeLift`). The source and target of `φ` are classified by the
left unit `η_L = C` and the right unit `η_R = TauCeti.LazardRing.rightUnit`, and the identity
isomorphisms by the counit `ε`. This file constructs the remaining structure maps, which classify
composition and inversion of strict isomorphisms, and proves the Hopf algebroid equations: the pair
`(L, Γ)` is a cogroupoid object in commutative rings, corepresenting the groupoid of commutative
formal group laws and their strict isomorphisms.

Composable pairs `F → φ • F → ψ • (φ • F)` are classified by the pushout `Γ ⊗_L Γ` of `η_R` on the
left factor and `η_L` on the right factor. As `Γ` is a polynomial ring over `L` through `η_L`, this
pushout is the polynomial ring `Γ[b₁', b₂', …] = MvPolynomial ℕ+ Γ`, with left factor `C` and right
factor `MvPolynomial.map η_R`; `TauCeti.LazardRing.tensorLift` is its universal property. The
**coproduct** `Δ : Γ → Γ ⊗_L Γ` classifies the composite `ψ * φ = ψ ∘ φ`, and the
**conjugation** `c : Γ → Γ` classifies the inverse `φ⁻¹ : φ • F → F`.

The equations are proved by comparing classified data: a ring homomorphism out of `Γ` is
determined by its restriction to `L` and by its base change of the universal strict coordinate
(`TauCeti.LazardRing.ringHom_ext_universalStrictCoordinate`), and then each equation is a
groupoid law in the group of strict coordinates. In the tensor model, the composite
`μ ∘ (f ⊗ g) : Γ ⊗_L Γ → R` of a tensor product of maps with multiplication is `tensorLift (f, g)`.

## Main definitions

* `TauCeti.LazardRing.tensorLift`: the universal property of `Γ ⊗_L Γ = MvPolynomial ℕ+ Γ` as the
  pushout of `η_R` and `η_L`.
* `TauCeti.LazardRing.coproduct`: the coproduct `Δ : Γ →+* Γ ⊗_L Γ`.
* `TauCeti.LazardRing.conjugation`: the conjugation `c : Γ →+* Γ`.

## Main results

* `TauCeti.LazardRing.map_comp_coproduct_universalStrictCoordinate`,
  `TauCeti.LazardRing.comp_coproduct_comp_C`: the coproduct classifies the composite of a
  composable pair of strict isomorphisms.
* `TauCeti.LazardRing.coproduct_comp_C`, `TauCeti.LazardRing.coproduct_comp_rightUnit`:
  `Δ η_L = (η_L ⊗ 1) η_L` and `Δ η_R = (1 ⊗ η_R) η_R`.
* `TauCeti.LazardRing.tensorLift_counit_id_comp_coproduct`,
  `TauCeti.LazardRing.tensorLift_id_counit_comp_coproduct`: `(ε ⊗ id) Δ = id = (id ⊗ ε) Δ`.
* `TauCeti.LazardRing.coproduct_coassoc`: coassociativity, `(Δ ⊗ id) Δ = (id ⊗ Δ) Δ`.
* `TauCeti.LazardRing.conjugation_comp_C`, `TauCeti.LazardRing.conjugation_comp_rightUnit`,
  `TauCeti.LazardRing.conjugation_comp_conjugation`: `c η_L = η_R`, `c η_R = η_L` and `c c = id`.
* `TauCeti.LazardRing.counit_comp_conjugation`: `ε c = ε`.
* `TauCeti.LazardRing.tensorLift_conjugation_id_comp_coproduct`,
  `TauCeti.LazardRing.tensorLift_id_conjugation_comp_coproduct`: the antipode equations
  `μ (c ⊗ id) Δ = η_R ε` and `μ (id ⊗ c) Δ = η_L ε`.

## References

* D. C. Ravenel, *Complex Cobordism and Stable Homotopy Groups of Spheres*, Appendix A1.1
  (Hopf algebroids) and A2.1 (the Hopf algebroid `(L, LB)`).
* J. Lurie, *Chromatic Homotopy Theory* (Harvard lecture notes, 2010), Lecture 3.
-/

public section

noncomputable section

namespace TauCeti

namespace LazardRing

variable {R : Type*} [CommRing R]

open MvPolynomial

/-! ### The tensor square `Γ ⊗_L Γ` -/

/-- **The universal property of `Γ ⊗_L Γ`**, for `Γ = L[b₁, b₂, …]`: ring homomorphisms out of
`Γ[b₁', b₂', …] = MvPolynomial ℕ+ Γ` correspond to pairs `(f, g)` of ring homomorphisms out of `Γ`
with `f ∘ η_R = g ∘ η_L`, by restriction along the left factor `C` and the right factor
`MvPolynomial.map η_R`. Thus `MvPolynomial ℕ+ Γ` is the pushout `Γ ⊗_L Γ` of the right unit on the
left factor and the left unit on the right factor, and its homomorphisms to `R` classify
composable pairs `F → φ • F → ψ • (φ • F)` of strict isomorphisms. -/
def tensorLift :
    {p : (MvPolynomial ℕ+ LazardRing →+* R) × (MvPolynomial ℕ+ LazardRing →+* R) //
      p.1.comp rightUnit = p.2.comp C} ≃ (MvPolynomial ℕ+ (MvPolynomial ℕ+ LazardRing) →+* R) where
  toFun p := eval₂Hom p.1.1 (p.1.2 ∘ X)
  invFun k := ⟨(k.comp C, k.comp (map rightUnit)), by
    rw [RingHom.comp_assoc, RingHom.comp_assoc, map_comp_C]⟩
  left_inv p := by
    refine Subtype.ext (Prod.ext (RingHom.ext (eval₂Hom_C _ _)) ?_)
    refine ringHom_ext' ?_ fun i ↦ by simp
    ext r
    simpa using RingHom.congr_fun p.2 r
  right_inv k := ringHom_ext' (RingHom.ext fun r ↦ by simp) fun i ↦ by simp

/-- The left component of the pair classified by `k : Γ ⊗_L Γ →+* R` is its restriction along the
left factor `C`. -/
@[simp]
theorem tensorLift_symm_apply_fst (k : MvPolynomial ℕ+ (MvPolynomial ℕ+ LazardRing) →+* R) :
    (tensorLift.symm k).1.1 = k.comp C :=
  (rfl)

/-- The right component of the pair classified by `k : Γ ⊗_L Γ →+* R` is its restriction along the
right factor `MvPolynomial.map η_R`. -/
@[simp]
theorem tensorLift_symm_apply_snd (k : MvPolynomial ℕ+ (MvPolynomial ℕ+ LazardRing) →+* R) :
    (tensorLift.symm k).1.2 = k.comp (map rightUnit) :=
  (rfl)

/-- `tensorLift (f, g)` restricts to `f` on the left factor. -/
@[simp]
theorem tensorLift_comp_C
    (p : {p : (MvPolynomial ℕ+ LazardRing →+* R) × (MvPolynomial ℕ+ LazardRing →+* R) //
      p.1.comp rightUnit = p.2.comp C}) :
    (tensorLift p).comp C = p.1.1 :=
  congrArg (fun q ↦ q.1.1) (tensorLift.left_inv p)

/-- `tensorLift (f, g)` restricts to `g` on the right factor. -/
@[simp]
theorem tensorLift_comp_map_rightUnit
    (p : {p : (MvPolynomial ℕ+ LazardRing →+* R) × (MvPolynomial ℕ+ LazardRing →+* R) //
      p.1.comp rightUnit = p.2.comp C}) :
    (tensorLift p).comp (map rightUnit) = p.1.2 :=
  congrArg (fun q ↦ q.1.2) (tensorLift.left_inv p)

/-- `tensorLift (f, g)` agrees with `f` on the left factor. -/
@[simp]
theorem tensorLift_C
    (p : {p : (MvPolynomial ℕ+ LazardRing →+* R) × (MvPolynomial ℕ+ LazardRing →+* R) //
      p.1.comp rightUnit = p.2.comp C}) (x : MvPolynomial ℕ+ LazardRing) :
    tensorLift p (C x) = p.1.1 x :=
  RingHom.congr_fun (tensorLift_comp_C p) x

/-- `tensorLift (f, g)` agrees with `g` on the right factor. -/
@[simp]
theorem tensorLift_map_rightUnit
    (p : {p : (MvPolynomial ℕ+ LazardRing →+* R) × (MvPolynomial ℕ+ LazardRing →+* R) //
      p.1.comp rightUnit = p.2.comp C}) (x : MvPolynomial ℕ+ LazardRing) :
    tensorLift p (map rightUnit x) = p.1.2 x :=
  RingHom.congr_fun (tensorLift_comp_map_rightUnit p) x

/-- `tensorLift (f, g)` agrees with `g` on the generators of the right factor. -/
@[simp]
theorem tensorLift_X
    (p : {p : (MvPolynomial ℕ+ LazardRing →+* R) × (MvPolynomial ℕ+ LazardRing →+* R) //
      p.1.comp rightUnit = p.2.comp C}) (i : ℕ+) :
    tensorLift p (X i) = p.1.2 (X i) := by
  simpa using tensorLift_map_rightUnit p (X i)

/-- A ring homomorphism out of `Γ ⊗_L Γ` is determined by its restrictions to both factors. -/
theorem tensor_ringHom_ext {k k' : MvPolynomial ℕ+ (MvPolynomial ℕ+ LazardRing) →+* R}
    (h₁ : k.comp C = k'.comp C) (h₂ : k.comp (map rightUnit) = k'.comp (map rightUnit)) :
    k = k' :=
  tensorLift.symm.injective (Subtype.ext (Prod.ext h₁ h₂))

/-! ### The coproduct -/

/-- The **coproduct** `Δ : Γ →+* Γ ⊗_L Γ`, classifying the composite `ψ * φ = ψ ∘ φ` of the
universal composable pair `F → φ • F → ψ • (φ • F)` of strict isomorphisms: `F` and `φ` come from
the left factor and `ψ` from the right factor. -/
def coproduct : MvPolynomial ℕ+ LazardRing →+* MvPolynomial ℕ+ (MvPolynomial ℕ+ LazardRing) :=
  coordinateChangeLift (⟨formalGroup.map (C.comp C), inferInstance⟩,
    ⟨FormalCoordinate.map (map rightUnit) universalStrictCoordinate *
        FormalCoordinate.map C universalStrictCoordinate,
      mul_mem (map_universalStrictCoordinate_mem_ker _) (map_universalStrictCoordinate_mem_ker _)⟩)

/-- `Δ η_L = (η_L ⊗ 1) η_L`: the source of a composite is the source of its first factor. -/
@[simp]
theorem coproduct_comp_C : coproduct.comp C = C.comp C :=
  (coordinateChangeLift_comp_C _).trans (hom_ext (map_lift _))

/-- The coproduct agrees with the left factor on `L`. -/
@[simp]
theorem coproduct_C (r : LazardRing) : coproduct (C r) = C (C r) :=
  RingHom.congr_fun coproduct_comp_C r

/-- The coproduct sends the universal strict coordinate to the composite `ψ * φ` of the universal
strict coordinates `φ` of the left factor and `ψ` of the right factor. -/
@[simp]
theorem map_coproduct_universalStrictCoordinate :
    FormalCoordinate.map coproduct universalStrictCoordinate =
      FormalCoordinate.map (map rightUnit) universalStrictCoordinate *
        FormalCoordinate.map C universalStrictCoordinate :=
  map_coordinateChangeLift_universalStrictCoordinate _

/-- **The coproduct classifies composition**: if `k : Γ ⊗_L Γ →+* R` classifies the composable pair
`F → φ • F → ψ • (φ • F)`, then `k ∘ Δ` classifies the composite `ψ * φ`. This is its coordinate;
`TauCeti.LazardRing.comp_coproduct_comp_C` is its source. -/
theorem map_comp_coproduct_universalStrictCoordinate
    (k : MvPolynomial ℕ+ (MvPolynomial ℕ+ LazardRing) →+* R) :
    FormalCoordinate.map (k.comp coproduct) universalStrictCoordinate =
      FormalCoordinate.map (k.comp (map rightUnit)) universalStrictCoordinate *
        FormalCoordinate.map (k.comp C) universalStrictCoordinate := by
  rw [FormalCoordinate.map_comp, map_coproduct_universalStrictCoordinate, map_mul,
    ← FormalCoordinate.map_comp, ← FormalCoordinate.map_comp]

/-- The source of the composite classified by `k ∘ Δ` is the source classified by the left
factor of `k`. -/
theorem comp_coproduct_comp_C (k : MvPolynomial ℕ+ (MvPolynomial ℕ+ LazardRing) →+* R) :
    (k.comp coproduct).comp C = (k.comp C).comp C := by
  rw [RingHom.comp_assoc, coproduct_comp_C, RingHom.comp_assoc]

/-- `Δ η_R = (1 ⊗ η_R) η_R`: the target of a composite is the target of its second factor. -/
@[simp]
theorem coproduct_comp_rightUnit : coproduct.comp rightUnit = (map rightUnit).comp rightUnit := by
  refine hom_ext ?_
  rw [map_comp_rightUnit, map_coproduct_universalStrictCoordinate, coproduct_comp_C,
    map_comp_rightUnit, map_comp_C, map_comp_rightUnit, mul_smul]

/-- The coproduct agrees with the right factor on the image of the right unit. -/
@[simp]
theorem coproduct_rightUnit (r : LazardRing) :
    coproduct (rightUnit r) = map rightUnit (rightUnit r) :=
  RingHom.congr_fun coproduct_comp_rightUnit r

/-- **The left counit law** `(ε ⊗ id) Δ = id`: composing with an identity on the left does
nothing. Here `ε ⊗ id` is `tensorLift (η_L ε, id)`. -/
theorem tensorLift_counit_id_comp_coproduct :
    (tensorLift ⟨(C.comp counit, RingHom.id _), by
        rw [RingHom.comp_assoc, counit_comp_rightUnit, RingHom.comp_id, RingHom.id_comp]⟩).comp
          coproduct =
      RingHom.id (MvPolynomial ℕ+ LazardRing) := by
  refine ringHom_ext_universalStrictCoordinate ?_ ?_
  · rw [comp_coproduct_comp_C, tensorLift_comp_C, RingHom.comp_assoc, counit_comp_C,
      RingHom.comp_id, RingHom.id_comp]
  · rw [map_comp_coproduct_universalStrictCoordinate, tensorLift_comp_map_rightUnit,
      tensorLift_comp_C]
    simp [FormalCoordinate.map_comp]

/-- **The right counit law** `(id ⊗ ε) Δ = id`: composing with an identity on the right does
nothing. Here `id ⊗ ε` is `tensorLift (id, η_R ε)`. -/
theorem tensorLift_id_counit_comp_coproduct :
    (tensorLift ⟨(RingHom.id _, rightUnit.comp counit), by
        rw [RingHom.comp_assoc, counit_comp_C, RingHom.comp_id, RingHom.id_comp]⟩).comp
          coproduct =
      RingHom.id (MvPolynomial ℕ+ LazardRing) := by
  refine ringHom_ext_universalStrictCoordinate ?_ ?_
  · rw [comp_coproduct_comp_C, tensorLift_comp_C]
  · rw [map_comp_coproduct_universalStrictCoordinate, tensorLift_comp_map_rightUnit,
      tensorLift_comp_C]
    simp [FormalCoordinate.map_comp]

/-- **Coassociativity** `(Δ ⊗ id) Δ = (id ⊗ Δ) Δ` of the coproduct: composition of strict
isomorphisms is associative. Both sides take values in the triple tensor product
`Γ ⊗_L Γ ⊗_L Γ = MvPolynomial ℕ+ (Γ ⊗_L Γ)`, the pushout of `Γ ⊗_L Γ` along the target of its right
factor and of `Γ` along `η_L`, whose three factors are `C ∘ C`, `C ∘ MvPolynomial.map η_R` and
`MvPolynomial.map (MvPolynomial.map η_R ∘ η_R)`. In it, `Δ ⊗ id` is `tensorLift (C ∘ Δ, ι₃)` with
`ι₃` the third factor, and `id ⊗ Δ` is `tensorLift (C ∘ C, ι₂₃ ∘ Δ)` with
`ι₂₃ = MvPolynomial.map (MvPolynomial.map η_R)` the inclusion of the last two factors. -/
theorem coproduct_coassoc :
    (tensorLift (R := MvPolynomial ℕ+ (MvPolynomial ℕ+ (MvPolynomial ℕ+ LazardRing)))
        ⟨(C.comp coproduct, map ((map (σ := ℕ+) rightUnit).comp rightUnit)),
          RingHom.ext fun r ↦ by simp⟩).comp coproduct =
      (tensorLift (R := MvPolynomial ℕ+ (MvPolynomial ℕ+ (MvPolynomial ℕ+ LazardRing)))
        ⟨((C : MvPolynomial ℕ+ (MvPolynomial ℕ+ LazardRing) →+* _).comp C,
          (map (map (σ := ℕ+) rightUnit)).comp coproduct), RingHom.ext fun r ↦ by simp⟩).comp
          coproduct := by
  refine ringHom_ext_universalStrictCoordinate ?_ ?_
  · rw [comp_coproduct_comp_C, comp_coproduct_comp_C, tensorLift_comp_C, tensorLift_comp_C,
      RingHom.comp_assoc, coproduct_comp_C, RingHom.comp_assoc]
  · -- Both sides are the triple composite `χ₃ * χ₂ * χ₁` of the strict coordinates of the three
    -- factors.
    rw [map_comp_coproduct_universalStrictCoordinate, map_comp_coproduct_universalStrictCoordinate,
      tensorLift_comp_map_rightUnit, tensorLift_comp_C, tensorLift_comp_map_rightUnit,
      tensorLift_comp_C,
      map_comp_coproduct_universalStrictCoordinate
        (R := MvPolynomial ℕ+ (MvPolynomial ℕ+ (MvPolynomial ℕ+ LazardRing))) C,
      map_comp_coproduct_universalStrictCoordinate
        (R := MvPolynomial ℕ+ (MvPolynomial ℕ+ (MvPolynomial ℕ+ LazardRing)))
        (map (map (σ := ℕ+) rightUnit))]
    -- Reduce the projections `p.1.1`, `p.1.2` of the explicit pairs passed to `tensorLift`, so
    -- that the rewrites below see the factor maps themselves.
    dsimp only
    have h : (map (map (σ := ℕ+) rightUnit)).comp (map (σ := ℕ+) rightUnit) =
        map ((map rightUnit).comp rightUnit) :=
      RingHom.ext fun p ↦ map_map rightUnit (map rightUnit) p
    rw [map_comp_C (map (σ := ℕ+) rightUnit), mul_assoc, h]

/-! ### The conjugation -/

/-- The **conjugation** `c : Γ →+* Γ`, classifying the inverse `φ⁻¹ : φ • F → F` of the universal
strict isomorphism `φ : F → φ • F`. -/
def conjugation : MvPolynomial ℕ+ LazardRing →+* MvPolynomial ℕ+ LazardRing :=
  coordinateChangeLift (⟨formalGroup.map rightUnit, inferInstance⟩,
    ⟨universalStrictCoordinate⁻¹, inv_mem (by
      simpa using map_universalStrictCoordinate_mem_ker (RingHom.id _))⟩)

/-- `c η_L = η_R`: the source of the inverse is the target. -/
@[simp]
theorem conjugation_comp_C : conjugation.comp C = rightUnit :=
  (coordinateChangeLift_comp_C _).trans (hom_ext (map_lift _))

/-- The conjugation agrees with the right unit on `L`. -/
@[simp]
theorem conjugation_C (r : LazardRing) : conjugation (C r) = rightUnit r :=
  RingHom.congr_fun conjugation_comp_C r

/-- The conjugation sends the universal strict coordinate to its inverse. -/
@[simp]
theorem map_conjugation_universalStrictCoordinate :
    FormalCoordinate.map conjugation universalStrictCoordinate = universalStrictCoordinate⁻¹ :=
  map_coordinateChangeLift_universalStrictCoordinate _

/-- `c η_R = η_L`: the target of the inverse is the source. -/
@[simp]
theorem conjugation_comp_rightUnit : conjugation.comp rightUnit = C := by
  refine hom_ext ?_
  rw [map_comp_rightUnit, map_conjugation_universalStrictCoordinate, conjugation_comp_C,
    map_rightUnit, inv_smul_smul]

/-- The conjugation agrees with the left unit on the image of the right unit. -/
@[simp]
theorem conjugation_rightUnit (r : LazardRing) : conjugation (rightUnit r) = C r :=
  RingHom.congr_fun conjugation_comp_rightUnit r

/-- `c c = id`: the inverse of the inverse is the original strict isomorphism. -/
@[simp]
theorem conjugation_comp_conjugation :
    conjugation.comp conjugation = RingHom.id (MvPolynomial ℕ+ LazardRing) := by
  refine ringHom_ext_universalStrictCoordinate ?_ ?_
  · rw [RingHom.comp_assoc, conjugation_comp_C, conjugation_comp_rightUnit,
      RingHom.id_comp]
  · rw [FormalCoordinate.map_comp, map_conjugation_universalStrictCoordinate, map_inv,
      map_conjugation_universalStrictCoordinate, inv_inv]
    simp

/-- The conjugation is an involution. -/
@[simp]
theorem conjugation_conjugation (x : MvPolynomial ℕ+ LazardRing) :
    conjugation (conjugation x) = x :=
  RingHom.congr_fun conjugation_comp_conjugation x

/-- `ε c = ε`: the inverse of an identity is an identity. -/
@[simp]
theorem counit_comp_conjugation : counit.comp conjugation = counit := by
  refine ringHom_ext_universalStrictCoordinate ?_ ?_
  · rw [RingHom.comp_assoc, conjugation_comp_C, counit_comp_rightUnit, counit_comp_C]
  · rw [FormalCoordinate.map_comp, map_conjugation_universalStrictCoordinate, map_inv,
      map_counit_universalStrictCoordinate, inv_one]

/-- The counit is invariant under the conjugation. -/
@[simp]
theorem counit_conjugation (x : MvPolynomial ℕ+ LazardRing) :
    counit (conjugation x) = counit x :=
  RingHom.congr_fun counit_comp_conjugation x

/-- **The left antipode equation** `μ (c ⊗ id) Δ = η_R ε`: composing the inverse of a strict
isomorphism with it gives the identity of its target. Here `μ (c ⊗ id)` is
`tensorLift (c, id)`. -/
theorem tensorLift_conjugation_id_comp_coproduct :
    (tensorLift ⟨(conjugation, RingHom.id _), by
        rw [conjugation_comp_rightUnit, RingHom.id_comp]⟩).comp coproduct =
      rightUnit.comp counit := by
  refine ringHom_ext_universalStrictCoordinate ?_ ?_
  · rw [comp_coproduct_comp_C, tensorLift_comp_C, conjugation_comp_C, RingHom.comp_assoc,
      counit_comp_C, RingHom.comp_id]
  · rw [map_comp_coproduct_universalStrictCoordinate, tensorLift_comp_map_rightUnit,
      tensorLift_comp_C, map_conjugation_universalStrictCoordinate, FormalCoordinate.map_comp,
      map_counit_universalStrictCoordinate, map_one]
    simp

/-- **The right antipode equation** `μ (id ⊗ c) Δ = η_L ε`: composing a strict isomorphism with
its inverse gives the identity of its source. Here `μ (id ⊗ c)` is `tensorLift (id, c)`. -/
theorem tensorLift_id_conjugation_comp_coproduct :
    (tensorLift ⟨(RingHom.id _, conjugation), by
        rw [conjugation_comp_C, RingHom.id_comp]⟩).comp coproduct = C.comp counit := by
  refine ringHom_ext_universalStrictCoordinate ?_ ?_
  · rw [comp_coproduct_comp_C, tensorLift_comp_C, RingHom.comp_assoc, counit_comp_C,
      RingHom.comp_id, RingHom.id_comp]
  · rw [map_comp_coproduct_universalStrictCoordinate, tensorLift_comp_map_rightUnit,
      tensorLift_comp_C, map_conjugation_universalStrictCoordinate, FormalCoordinate.map_comp,
      map_counit_universalStrictCoordinate, map_one]
    simp

end LazardRing

end TauCeti
