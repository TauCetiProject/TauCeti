/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import TauCeti.RepresentationTheory.CharacterTable.ClassSum.Basis
public import TauCeti.RepresentationTheory.GroupAlgebra.Block
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import TauCeti.Algebra.MonoidAlgebra.Basic
import TauCeti.RingTheory.AdicCompletion.Finite
import TauCeti.RingTheory.AdicCompletion.Idempotent
import TauCeti.RingTheory.Ideal.Extended
import TauCeti.RingTheory.Ideal.GoingUp
import TauCeti.RingTheory.Idempotents.Jacobson

/-!
# Lifting central idempotents of group algebras

Let `R` be a commutative ring, complete with respect to an ideal `I`, let `φ : R →+* k` be a
surjective ring homomorphism with kernel `I`, and let `G` be a finite group. The main case is a
complete discrete valuation ring `O` with residue field `k`, and `φ` the residue map. Applying
`φ` to the coefficients maps the centre `Z(R[G])` to the centre `Z(k[G])`
(`TauCeti.centerMapRingHom`): a central element is a linear combination of class sums, and class
sums map to class sums (`TauCeti.centerMapRingHom_classSumCenter`). This reduction of centres is
surjective (`TauCeti.centerMapRingHom_surjective`), because the class sums form an `R`-basis of
`Z(R[G])` and a `k`-basis of `Z(k[G])`, and its kernel is `I • Z(R[G])`.

Being a finite free `R`-module, `Z(R[G])` is `I`-adically complete, so every idempotent of
`Z(k[G])` lifts to an idempotent of `Z(R[G])`. Since `Z(R[G])` is commutative and finite over `R`,
and `I` lies in the Jacobson radical of `R`, the extension of `I` lies in the Jacobson radical of
`Z(R[G])`, where commuting idempotents congruent modulo the radical are equal: the lift is unique
(`TauCeti.existsUnique_isIdempotentElem_centerMapRingHom_eq`). Uniqueness of lifts makes reduction
preserve and reflect primitivity on the centre
(`TauCeti.isPrimitiveIdempotent_centerMapRingHom_iff`), so reduction is a bijection between the
blocks of `R[G]` and of `k[G]` (`TauCeti.existsUnique_blockIdempotent_map_residue`).

Over `ℤ₂` and for `G = C₃`, the blocks `1 + r + r²` and `r + r²` of `𝔽₂[C₃]` lift to
`(1 + r + r²)/3` and `(2 - r - r²)/3`, while for `G = C₂` the only block of `ℤ₂[C₂]` is `1`,
matching the single block of `𝔽₂[C₂]`.

## Main definitions

* `TauCeti.centerMapRingHom φ`: the ring homomorphism `Z(R[G]) →+* Z(k[G])` applying `φ` to the
  coefficients.

## Main results

* `TauCeti.centerMapRingHom_surjective`: reduction of centres along a surjection is surjective.
* `TauCeti.centerMapRingHom_eq_zero_iff`: its kernel is `I • Z(R[G])` when `ker φ = I`.
* `TauCeti.existsUnique_isIdempotentElem_centerMapRingHom_eq`: every idempotent of `Z(k[G])` is the
  reduction of exactly one idempotent of `Z(R[G])`.
* `TauCeti.isPrimitiveIdempotent_centerMapRingHom_iff`: a central idempotent of `R[G]` is a block
  idempotent exactly when its reduction is.
* `TauCeti.existsUnique_blockIdempotent_map_residue`: for a complete local ring `O`, in particular
  a complete discrete valuation ring, every block idempotent of `k[G]` is the reduction of exactly
  one block idempotent of `O[G]`.

## References

* P. Webb, *A Course in Finite Group Representation Theory*, Proposition 9.4.3 and §12.1.
* C. W. Curtis, I. Reiner, *Methods of Representation Theory, Vol. I*, §6.
-/

public section

namespace TauCeti

variable {R k G : Type*} [CommRing R] [CommRing k] [Group G]

/-- The centre of `R[G]` is `I`-adically complete when `R` is, being a finite free `R`-module with
the class sums as basis. -/
instance instIsAdicCompleteCenterMonoidAlgebra [Finite G] (I : Ideal R) [IsAdicComplete I R] :
    IsAdicComplete I (Subalgebra.center R (MonoidAlgebra R G)) :=
  let _ := Fintype.ofFinite G
  open scoped Classical in
  have := Module.Free.of_basis (classSumBasis (k := R) (G := G))
  have := Module.Finite.of_basis (classSumBasis (k := R) (G := G))
  { toIsHausdorff := IsHausdorff.of_free I _
    toIsPrecomplete := IsPrecomplete.of_finite I _ }

/-- Idempotents of `Z(R[G])` congruent modulo `I` are equal, for `R` complete with respect to
`I`: the extension of `I` lies in the Jacobson radical of the commutative finite `R`-algebra
`Z(R[G])`. -/
private theorem eq_of_isIdempotentElem_of_sub_mem {I : Ideal R} [Finite G] [IsAdicComplete I R]
    {e e' : Subalgebra.center R (MonoidAlgebra R G)} (he : IsIdempotentElem e)
    (he' : IsIdempotentElem e')
    (h : e - e' ∈ I • (⊤ : Submodule R (Subalgebra.center R (MonoidAlgebra R G)))) : e = e' := by
  classical
  let _ := Fintype.ofFinite G
  have := Module.Finite.of_basis (classSumBasis (k := R) (G := G))
  have hjac : I.map (algebraMap R (Subalgebra.center R (MonoidAlgebra R G))) ≤
      Ring.jacobson (Subalgebra.center R (MonoidAlgebra R G)) := by
    rw [← Ideal.jacobson_bot]
    exact Ideal.map_le_jacobson_of_isIntegral bot_le
      ((IsAdicComplete.le_jacobson I).trans_eq Ideal.jacobson_bot.symm)
  exact he.eq_of_commute_of_sub_mem_jacobson he' (.all _ _)
    (hjac ((Ideal.mem_map_algebraMap_iff I).mpr h))

variable [Fintype G] [DecidableEq G]

/-- Applying `φ` to the coefficients of a central element gives the class-sum expansion with the
coefficients mapped by `φ`. -/
private theorem mapRingHom_coe_center (φ : R →+* k) (z : Subalgebra.center R (MonoidAlgebra R G)) :
    MonoidAlgebra.mapRingHom G φ (z : MonoidAlgebra R G) =
      (ofConjClassesCenter (fun C ↦ φ (centerToConjClasses z C)) : MonoidAlgebra k G) := by
  ext g
  simp [MonoidAlgebra.coeff_mapRingHom]

/-- **Reduction of centres.** Applying a ring homomorphism `φ : R →+* k` to the coefficients maps
the centre of `R[G]` to the centre of `k[G]`, since it maps class sums to class sums. -/
@[expose] noncomputable def centerMapRingHom (φ : R →+* k) :
    Subalgebra.center R (MonoidAlgebra R G) →+* Subalgebra.center k (MonoidAlgebra k G) where
  toFun z := ⟨MonoidAlgebra.mapRingHom G φ (z : MonoidAlgebra R G), by
    rw [mapRingHom_coe_center]
    exact SetLike.coe_mem _⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' z w := Subtype.ext (map_mul (MonoidAlgebra.mapRingHom G φ) (z : MonoidAlgebra R G) w)
  map_zero' := Subtype.ext (map_zero _)
  map_add' z w := Subtype.ext (map_add (MonoidAlgebra.mapRingHom G φ) (z : MonoidAlgebra R G) w)

/-- The reduction of a central element is computed in the group algebra. -/
@[simp]
theorem coe_centerMapRingHom (φ : R →+* k) (z : Subalgebra.center R (MonoidAlgebra R G)) :
    (centerMapRingHom φ z : MonoidAlgebra k G) = MonoidAlgebra.mapRingHom G φ z :=
  rfl

/-- Reduction of centres maps class sums to class sums. -/
@[simp]
theorem centerMapRingHom_classSumCenter (φ : R →+* k) (C : ConjClasses G) :
    centerMapRingHom φ (classSumCenter C) = classSumCenter C := by
  ext g
  simp [MonoidAlgebra.coeff_mapRingHom, apply_ite φ]

/-- **Reduction of centres is surjective** along a surjective ring homomorphism: lift the
coefficients of the class-sum expansion. -/
theorem centerMapRingHom_surjective {φ : R →+* k} (hφ : Function.Surjective φ) :
    Function.Surjective (centerMapRingHom (G := G) φ) := fun w ↦ by
  refine ⟨ofConjClassesCenter fun C ↦ Function.surjInv hφ (centerToConjClasses w C), ?_⟩
  ext g
  simp [MonoidAlgebra.coeff_mapRingHom, Function.surjInv_eq hφ]

/-- **The kernel of reduction of centres.** When `ker φ = I`, a central element reduces to `0`
exactly when it lies in `I • Z(R[G])`: its class-sum coefficients then lie in `I`. -/
theorem centerMapRingHom_eq_zero_iff {φ : R →+* k} {I : Ideal R} (hI : RingHom.ker φ = I)
    (z : Subalgebra.center R (MonoidAlgebra R G)) :
    centerMapRingHom φ z = 0 ↔
      z ∈ I • (⊤ : Submodule R (Subalgebra.center R (MonoidAlgebra R G))) := by
  rw [← Subtype.coe_inj, coe_centerMapRingHom, ZeroMemClass.coe_zero,
    TauCeti.MonoidAlgebra.mapRingHom_eq_zero_iff, hI,
    TauCeti.MonoidAlgebra.mem_ideal_smul_top_iff]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [← (classSumBasis (k := R) (G := G)).sum_repr z]
    refine Submodule.sum_mem _ fun C _ ↦ Submodule.smul_mem_smul ?_ Submodule.mem_top
    obtain ⟨g, rfl⟩ := ConjClasses.exists_rep C
    simpa [classSumBasis_repr_apply] using h g
  · refine Submodule.smul_induction_on h (fun r hr n _ g ↦ ?_) fun x y hx hy g ↦ ?_
    · simpa using I.mul_mem_right _ hr
    · simpa using I.add_mem (hx g) (hy g)

variable {φ : R →+* k} {I : Ideal R}

/-- **Central idempotents lift uniquely.** For `R` complete with respect to `I` and a surjection
`φ : R →+* k` with kernel `I`, every idempotent of the centre of `k[G]` is the reduction of exactly
one idempotent of the centre of `R[G]`. -/
theorem existsUnique_isIdempotentElem_centerMapRingHom_eq [IsAdicComplete I R]
    (hφ : Function.Surjective φ) (hI : RingHom.ker φ = I)
    {ε : Subalgebra.center k (MonoidAlgebra k G)} (hε : IsIdempotentElem ε) :
    ∃! e, IsIdempotentElem e ∧ centerMapRingHom φ e = ε := by
  have hrange : ε ∈ (centerMapRingHom (G := G) φ).range :=
    RingHom.mem_range.mpr (centerMapRingHom_surjective hφ ε)
  obtain ⟨e, he, hee⟩ := IsAdicComplete.exists_isIdempotentElem_eq
    (S := Subalgebra.center R (MonoidAlgebra R G)) I (centerMapRingHom φ)
    (centerMapRingHom_eq_zero_iff hI) hrange hε
  refine ⟨e, ⟨he, hee⟩, fun e' ⟨he', hee'⟩ ↦
    eq_of_isIdempotentElem_of_sub_mem (I := I) he' he ?_⟩
  rw [← centerMapRingHom_eq_zero_iff hI, map_sub, hee, hee', sub_self]

/-- An idempotent of `Z(R[G])` reducing to `0` is `0`. -/
private theorem eq_zero_of_centerMapRingHom_eq_zero [IsAdicComplete I R]
    (hφ : Function.Surjective φ) (hI : RingHom.ker φ = I)
    {e : Subalgebra.center R (MonoidAlgebra R G)} (he : IsIdempotentElem e)
    (h : centerMapRingHom φ e = 0) : e = 0 :=
  (existsUnique_isIdempotentElem_centerMapRingHom_eq hφ hI IsIdempotentElem.zero).unique
    ⟨he, h⟩ ⟨IsIdempotentElem.zero, map_zero _⟩

/-- **Blocks are detected by reduction.** For `R` complete with respect to `I` and a surjection
`φ : R →+* k` with kernel `I`, an idempotent of the centre of `R[G]` is primitive in the centre,
that is a block idempotent, exactly when its reduction in the centre of `k[G]` is. -/
theorem isPrimitiveIdempotent_centerMapRingHom_iff [IsAdicComplete I R]
    (hφ : Function.Surjective φ) (hI : RingHom.ker φ = I)
    {e : Subalgebra.center R (MonoidAlgebra R G)} (he : IsIdempotentElem e) :
    IsPrimitiveIdempotent (centerMapRingHom φ e) ↔ IsPrimitiveIdempotent e := by
  have hzero {x} := eq_zero_of_centerMapRingHom_eq_zero (G := G) hφ hI (e := x)
  refine ⟨fun h ↦ ⟨he, fun h0 ↦ h.ne_zero (by rw [h0, map_zero]), ?_⟩, fun h ↦ ?_⟩
  · intro e₁ e₂ h₁ h₂ h₁₂ h₂₁ hsum
    refine (h.eq_zero_or_eq_zero_of_add (h₁.map _) (h₂.map _) (by rw [← map_mul, h₁₂, map_zero])
      (by rw [← map_mul, h₂₁, map_zero]) (by rw [← map_add, hsum])).imp
      (hzero h₁) (hzero h₂)
  · refine isPrimitiveIdempotent_of_eq_zero_or_eq (he.map _)
      (fun h0 ↦ h.ne_zero (hzero he h0)) fun ε hε hεe _ ↦ ?_
    -- Lift `ε` to `e₁`; then `e₁ * e` is an idempotent lift of `ε` as well, so `e₁ = e₁ * e`.
    obtain ⟨e₁, ⟨he₁, rfl⟩, huniq⟩ := existsUnique_isIdempotentElem_centerMapRingHom_eq hφ hI hε
    have he₁e : e₁ * e = e₁ :=
      huniq _ ⟨he₁.mul he, by rw [map_mul, mul_comm, hεe]⟩
    rcases h.eq_zero_or_eq he₁ (by rw [mul_comm, he₁e]) he₁e with h' | h'
    · exact .inl (by rw [h', map_zero])
    · exact .inr (by rw [h'])

/-- **Blocks lift uniquely.** For `R` complete with respect to `I` and a surjection `φ : R →+* k`
with kernel `I`, every block idempotent of `k[G]` is the reduction of exactly one block idempotent
of `R[G]`. -/
theorem existsUnique_blockIdempotent_centerMapRingHom_eq [IsAdicComplete I R]
    (hφ : Function.Surjective φ) (hI : RingHom.ker φ = I)
    {ε : Subalgebra.center k (MonoidAlgebra k G)} (hε : IsBlockIdempotent ε) :
    ∃! e, IsBlockIdempotent e ∧ centerMapRingHom φ e = ε := by
  obtain ⟨e, ⟨he, rfl⟩, huniq⟩ :=
    existsUnique_isIdempotentElem_centerMapRingHom_eq hφ hI hε.isIdempotentElem
  exact ⟨e, ⟨(isPrimitiveIdempotent_centerMapRingHom_iff hφ hI he).mp hε, rfl⟩,
    fun e' ⟨he', h⟩ ↦ huniq e' ⟨he'.isIdempotentElem, h⟩⟩

/-- **Blocks of `O[G]` and of `k[G]` correspond.** For a local ring `O` complete with respect to
its maximal ideal, in particular a complete discrete valuation ring, with residue field `k`, every
block idempotent of `k[G]` is the reduction of exactly one block idempotent of `O[G]`. -/
theorem existsUnique_blockIdempotent_map_residue {O : Type*} [CommRing O] [IsLocalRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    {ε : Subalgebra.center (IsLocalRing.ResidueField O)
      (MonoidAlgebra (IsLocalRing.ResidueField O) G)} (hε : IsBlockIdempotent ε) :
    ∃! e : Subalgebra.center O (MonoidAlgebra O G),
      IsBlockIdempotent e ∧ centerMapRingHom (IsLocalRing.residue O) e = ε :=
  existsUnique_blockIdempotent_centerMapRingHom_eq IsLocalRing.residue_surjective
    IsLocalRing.ker_residue hε

end TauCeti
