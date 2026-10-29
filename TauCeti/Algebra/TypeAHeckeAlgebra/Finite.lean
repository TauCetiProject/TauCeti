/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TypeAHeckeAlgebra.Infinite

/-!
# The type-A Hecke algebra on `n` strands

For a commutative ring `R`, a unit `q : Rˣ` and a number of strands `n`, the type-A Hecke algebra
`TypeAHeckeAlgebra R q n` is the associative unital `R`-algebra on the `n - 1` generators `T i`,
`i : Fin (n - 1)`, subject to

* the quadratic relation `T i * T i = (q - q⁻¹) • T i + 1`, equivalently
  `(T i - q) * (T i + q⁻¹) = 0`,
* the braid relation `T i * T j * T i = T j * T i * T j` when `j = i + 1`, and
* distant commutation `T i * T j = T j * T i` when `|i - j| ≥ 2`.

The generator `T i` crosses the strands `i` and `i + 1` (counted from `0`), so on at most one
strand there are no generators and the algebra is `R`
(`TauCeti.TypeAHeckeAlgebra.algEquivOfLeOne`). The algebra is built as the quotient of
`FreeAlgebra R (Fin (n - 1))` by these relations, which makes the universal property
`TauCeti.TypeAHeckeAlgebra.lift` available.

The elementary braids map to the generators, giving a homomorphism from the braid group on `n`
strands to the units (`TauCeti.TypeAHeckeAlgebra.braidHom`) whose image spans the algebra. Adding
an uncrossed last strand gives the tower map `TauCeti.TypeAHeckeAlgebra.strandIncl`, `T i ↦ T i`,
compatible with the strand inclusions of the braid groups.

The finite presentation maps onto the stage of the first `n` strands of the infinite type-A Hecke
algebra (`TauCeti.TypeAHeckeAlgebra.range_toInfinite`), compatibly with the tower maps. That this
map is injective, so that the finite presentation is isomorphic to the stage, is the basis theorem
(the algebra is free of rank `n!`) and is not proved here.

## Main definitions

* `TauCeti.TypeAHeckeAlgebra.Rel`: the defining relations on the free algebra.
* `TauCeti.TypeAHeckeAlgebra`: the type-A Hecke algebra on `n` strands with parameter `q`.
* `TauCeti.TypeAHeckeAlgebra.T`: the generators, and `TauCeti.TypeAHeckeAlgebra.unitT` the same
  generators as units.
* `TauCeti.TypeAHeckeAlgebra.lift`: the universal property.
* `TauCeti.TypeAHeckeAlgebra.braidHom`: the homomorphism from the braid group on `n` strands to
  the units.
* `TauCeti.TypeAHeckeAlgebra.strandIncl`: the tower map from `n` to `n + 1` strands.
* `TauCeti.TypeAHeckeAlgebra.toInfinite`: the map to the infinite type-A Hecke algebra.

## Main results

* `TauCeti.TypeAHeckeAlgebra.T_mul_self`, `TauCeti.TypeAHeckeAlgebra.T_braid` and
  `TauCeti.TypeAHeckeAlgebra.commute_T`: the defining relations.
* `TauCeti.TypeAHeckeAlgebra.lift_T` and `TauCeti.TypeAHeckeAlgebra.hom_ext`: the universal
  property.
* `TauCeti.TypeAHeckeAlgebra.span_range_braidHom`: the images of the braids span the algebra.
* `TauCeti.TypeAHeckeAlgebra.braidHom_strandIncl`: the braid homomorphisms are compatible with the
  tower maps.
* `TauCeti.TypeAHeckeAlgebra.range_toInfinite`: the image in the infinite algebra is the stage of
  the first `n` strands.
* `TauCeti.TypeAHeckeAlgebra.algebraMap_injective`: the presentation does not collapse the
  scalars.

## References

* V. F. R. Jones, *Hecke algebra representations of braid groups and link polynomials*,
  Ann. of Math. 126 (1987), 335–388, Section 4.
* The quotient presentation and universal-property API follow the construction pattern in
  `Mathlib.LinearAlgebra.CliffordAlgebra.Basic` and in `TauCeti.InfiniteTypeAHeckeAlgebra`.
-/

public section

namespace TauCeti

variable (R : Type*) [CommRing R] (q : Rˣ) (n : ℕ)

namespace TypeAHeckeAlgebra

/-- The defining relations of the type-A Hecke algebra on `n` strands with parameter `q`, as a
relation on the free algebra over the generators `Fin (n - 1)`: the quadratic relation
`T i * T i = (q - q⁻¹) • T i + 1`, the braid relation for adjacent generators and commutation of
distant generators. The last two are imposed for one ordering of the pair, which suffices since
the quotient relation is symmetric. -/
inductive Rel : FreeAlgebra R (Fin (n - 1)) → FreeAlgebra R (Fin (n - 1)) → Prop
  | mul_self (i : Fin (n - 1)) :
      Rel (FreeAlgebra.ι R i * FreeAlgebra.ι R i) (((q : R) - ↑q⁻¹) • FreeAlgebra.ι R i + 1)
  | braid {i j : Fin (n - 1)} (h : (i : ℕ) + 1 = j) :
      Rel (FreeAlgebra.ι R i * FreeAlgebra.ι R j * FreeAlgebra.ι R i)
        (FreeAlgebra.ι R j * FreeAlgebra.ι R i * FreeAlgebra.ι R j)
  | distant {i j : Fin (n - 1)} (h : (i : ℕ) + 2 ≤ j) :
      Rel (FreeAlgebra.ι R i * FreeAlgebra.ι R j) (FreeAlgebra.ι R j * FreeAlgebra.ι R i)

end TypeAHeckeAlgebra

/-- The type-A Hecke algebra over `R` on `n` strands with parameter `q`: the free `R`-algebra on
`Fin (n - 1)` modulo `TauCeti.TypeAHeckeAlgebra.Rel`. -/
@[expose] def TypeAHeckeAlgebra : Type _ := RingQuot (TypeAHeckeAlgebra.Rel R q n)

instance : Ring (TypeAHeckeAlgebra R q n) :=
  inferInstanceAs (Ring (RingQuot (TypeAHeckeAlgebra.Rel R q n)))

/-- The type-A Hecke algebra over `R` is an algebra over every ring that `R` is an algebra
over. -/
instance (priority := 900) TypeAHeckeAlgebra.instAlgebra' {S : Type*} [CommSemiring S]
    [Algebra S R] : Algebra S (TypeAHeckeAlgebra R q n) :=
  inferInstanceAs (Algebra S (RingQuot (TypeAHeckeAlgebra.Rel R q n)))

instance : Algebra R (TypeAHeckeAlgebra R q n) := inferInstance

instance {S T : Type*} [CommSemiring S] [CommSemiring T] [SMul S T] [Algebra S R] [Algebra T R]
    [IsScalarTower S T R] : IsScalarTower S T (TypeAHeckeAlgebra R q n) :=
  inferInstanceAs (IsScalarTower S T (RingQuot (TypeAHeckeAlgebra.Rel R q n)))

namespace TypeAHeckeAlgebra

/-- The quotient map from the free algebra to the type-A Hecke algebra on `n` strands. -/
def mkAlgHom : FreeAlgebra R (Fin (n - 1)) →ₐ[R] TypeAHeckeAlgebra R q n :=
  RingQuot.mkAlgHom R (Rel R q n)

variable {R n}

/-- The generator `T i` of the type-A Hecke algebra on `n` strands, the image of the elementary
braid crossing the strands `i` and `i + 1`. -/
def T (i : Fin (n - 1)) : TypeAHeckeAlgebra R q n :=
  mkAlgHom R q n (FreeAlgebra.ι R i)

variable {q}

/-- The quotient map takes each free-algebra generator to the corresponding Hecke generator. -/
@[simp]
theorem mkAlgHom_ι (i : Fin (n - 1)) : mkAlgHom R q n (FreeAlgebra.ι R i) = T q i := (rfl)

/-- Every element of the type-A Hecke algebra is represented by a free-algebra element. -/
theorem mkAlgHom_surjective : Function.Surjective (mkAlgHom R q n) :=
  RingQuot.mkAlgHom_surjective _ _

/-- Related elements of the free algebra have the same image in the type-A Hecke algebra. -/
theorem mkAlgHom_rel {x y : FreeAlgebra R (Fin (n - 1))} (h : Rel R q n x y) :
    mkAlgHom R q n x = mkAlgHom R q n y :=
  RingQuot.mkAlgHom_rel R h

/-- The quadratic relation of a Hecke generator. -/
@[simp]
theorem T_mul_self (i : Fin (n - 1)) : T q i * T q i = ((q : R) - ↑q⁻¹) • T q i + 1 := by
  simpa only [map_mul, map_add, map_smul, map_one, mkAlgHom_ι] using
    mkAlgHom_rel (Rel.mul_self (q := q) i)

/-- The quadratic relation in factored form: each generator is annihilated by the polynomial with
roots `q` and `-q⁻¹`. -/
theorem T_sub_algebraMap_mul_T_add_algebraMap_eq_zero (i : Fin (n - 1)) :
    (T q i - algebraMap R _ (q : R)) * (T q i + algebraMap R _ (↑q⁻¹ : R)) = 0 := by
  have hq : algebraMap R (TypeAHeckeAlgebra R q n) (q : R) * algebraMap R _ (↑q⁻¹ : R) = 1 := by
    simp [← map_mul]
  simp only [sub_mul, mul_add, T_mul_self, ← Algebra.commutes _ (T q i), hq,
    Algebra.smul_def, map_sub]
  abel

/-- Two generators on adjacent pairs of strands satisfy the braid relation. -/
theorem T_braid {i j : Fin (n - 1)} (h : (i : ℕ) + 1 = j ∨ (j : ℕ) + 1 = i) :
    T q i * T q j * T q i = T q j * T q i * T q j := by
  rcases h with h | h
  · simpa only [map_mul, mkAlgHom_ι] using mkAlgHom_rel (Rel.braid (R := R) (q := q) h)
  · simpa only [map_mul, mkAlgHom_ι] using (mkAlgHom_rel (Rel.braid (R := R) (q := q) h)).symm

/-- Two generators on disjoint pairs of strands commute. -/
theorem commute_T {i j : Fin (n - 1)} (h : (i : ℕ) + 2 ≤ j ∨ (j : ℕ) + 2 ≤ i) :
    Commute (T q i) (T q j) := by
  rw [commute_iff_eq]
  rcases h with h | h
  · simpa only [map_mul, mkAlgHom_ι] using mkAlgHom_rel (Rel.distant (R := R) (q := q) h)
  · simpa only [map_mul, mkAlgHom_ι] using (mkAlgHom_rel (Rel.distant (R := R) (q := q) h)).symm

section Units

variable (q) in
/-- The generator `T i` as a unit. Its inverse is `T i - (q - q⁻¹)`, by the quadratic
relation. -/
def unitT (i : Fin (n - 1)) : (TypeAHeckeAlgebra R q n)ˣ where
  val := T q i
  inv := T q i - algebraMap R _ ((q : R) - ↑q⁻¹)
  val_inv := by
    rw [mul_sub, ← Algebra.commutes, ← Algebra.smul_def, T_mul_self, add_sub_cancel_left]
  inv_val := by
    rw [sub_mul, ← Algebra.smul_def, T_mul_self, add_sub_cancel_left]

/-- The underlying element of `unitT q i` is the generator `T q i`. -/
@[simp]
theorem val_unitT (i : Fin (n - 1)) : (unitT q i : TypeAHeckeAlgebra R q n) = T q i := (rfl)

/-- The inverse of a generator is `T i - (q - q⁻¹)`. -/
@[simp]
theorem val_inv_unitT (i : Fin (n - 1)) :
    (↑(unitT q i)⁻¹ : TypeAHeckeAlgebra R q n) = T q i - algebraMap R _ ((q : R) - ↑q⁻¹) :=
  (rfl)

/-- Each generator of the type-A Hecke algebra is a unit. -/
theorem isUnit_T (i : Fin (n - 1)) : IsUnit (T q i) := (unitT q i).isUnit

end Units

section Lift

variable {A : Type*} [Semiring A] [Algebra R A]

/-- The universal property of the type-A Hecke presentation on `n` strands: a family in an
`R`-algebra indexed by `Fin (n - 1)` satisfying the quadratic relation, the braid relation for
adjacent indices and commutation for distant indices extends to an algebra map out of
`TypeAHeckeAlgebra R q n`. -/
def lift (f : Fin (n - 1) → A) (hself : ∀ i, f i * f i = ((q : R) - ↑q⁻¹) • f i + 1)
    (hbraid : ∀ {i j : Fin (n - 1)}, (i : ℕ) + 1 = j → f i * f j * f i = f j * f i * f j)
    (hdist : ∀ {i j : Fin (n - 1)}, (i : ℕ) + 2 ≤ j → f i * f j = f j * f i) :
    TypeAHeckeAlgebra R q n →ₐ[R] A :=
  RingQuot.liftAlgHom R ⟨FreeAlgebra.lift R f, by
    rintro x y (i | @⟨i, j, h⟩ | @⟨i, j, h⟩)
    · simpa only [map_mul, map_add, map_smul, map_one, FreeAlgebra.lift_ι_apply] using hself i
    · simpa only [map_mul, FreeAlgebra.lift_ι_apply] using hbraid h
    · simpa only [map_mul, FreeAlgebra.lift_ι_apply] using hdist h⟩

/-- The algebra map built by `TauCeti.TypeAHeckeAlgebra.lift` takes each generator to its
prescribed value. -/
@[simp]
theorem lift_T (f : Fin (n - 1) → A) (hself) (hbraid) (hdist) (i : Fin (n - 1)) :
    lift (q := q) f hself hbraid hdist (T q i) = f i :=
  (RingQuot.liftAlgHom_mkAlgHom_apply R _ _ _).trans (FreeAlgebra.lift_ι_apply _ _)

/-- Two algebra maps out of the type-A Hecke algebra agreeing on the generators are equal. -/
@[ext high]
theorem hom_ext {F G : TypeAHeckeAlgebra R q n →ₐ[R] A} (h : ∀ i, F (T q i) = G (T q i)) :
    F = G :=
  RingQuot.ringQuot_ext' R F G <| FreeAlgebra.hom_ext (funext h)

end Lift

/-- The generators generate the type-A Hecke algebra as an `R`-algebra. -/
theorem adjoin_range_T : Algebra.adjoin R (Set.range (T (n := n) q)) = ⊤ := by
  have hrange : Set.range (T (n := n) q) =
      mkAlgHom R q n '' Set.range (FreeAlgebra.ι R (X := Fin (n - 1))) := by
    simp only [← Set.range_comp, Function.comp_def, mkAlgHom_ι]
  rw [hrange, ← AlgHom.map_adjoin, FreeAlgebra.adjoin_range_ι, Algebra.map_top]
  exact (AlgHom.range_eq_top _).2 mkAlgHom_surjective

section Braid

variable (R q n) in
/-- The homomorphism from the braid group on `n` strands to the units of the type-A Hecke
algebra, sending the elementary braid `σ i` to the generator `T i`. -/
def braidHom : BraidGroup n →* (TypeAHeckeAlgebra R q n)ˣ :=
  BraidGroup.lift (fun i ↦ unitT q i) (fun h ↦ Units.ext (commute_T h).eq)
    (fun h ↦ Units.ext (T_braid h))

/-- The braid homomorphism sends each elementary braid to the corresponding generator. -/
@[simp]
theorem braidHom_sigma (i : Fin (n - 1)) : braidHom R q n (BraidGroup.sigma i) = unitT q i :=
  BraidGroup.lift_sigma _ _ _ i

/-- The images of the braids on `n` strands span the type-A Hecke algebra as an `R`-module. -/
theorem span_range_braidHom :
    Submodule.span R (Set.range fun b ↦ (braidHom R q n b : TypeAHeckeAlgebra R q n)) = ⊤ := by
  set M : Submonoid (TypeAHeckeAlgebra R q n) :=
    MonoidHom.mrange ((Units.coeHom _).comp (braidHom R q n))
  have hM : (M : Set (TypeAHeckeAlgebra R q n)) =
      Set.range fun b ↦ (braidHom R q n b : TypeAHeckeAlgebra R q n) := by
    simp [M, MonoidHom.coe_mrange, Function.comp_def]
  have htop : Algebra.adjoin R (M : Set (TypeAHeckeAlgebra R q n)) = ⊤ := by
    rw [eq_top_iff, ← adjoin_range_T, Algebra.adjoin_le_iff, Set.range_subset_iff]
    exact fun i ↦ Algebra.subset_adjoin ⟨BraidGroup.sigma i, by simp⟩
  rw [← hM, ← Submonoid.closure_eq M, ← Algebra.adjoin_eq_span, htop, Algebra.top_toSubmodule]

end Braid

section StrandIncl

variable (R q n) in
/-- The tower map of the type-A Hecke algebras, adding an uncrossed last strand: the generator
`T i` on `n` strands goes to the generator `T i` on `n + 1` strands. -/
def strandIncl : TypeAHeckeAlgebra R q n →ₐ[R] TypeAHeckeAlgebra R q (n + 1) :=
  lift (fun i ↦ T q (Fin.castLE (by omega) i)) (fun _ ↦ T_mul_self _)
    (fun h ↦ T_braid (Or.inl h)) (fun h ↦ (commute_T (R := R) (q := q) (n := n + 1) (Or.inl h)).eq)

/-- The tower map sends each generator to the generator with the same index. -/
@[simp]
theorem strandIncl_T (i : Fin (n - 1)) :
    strandIncl R q n (T q i) = T q (Fin.castLE (by omega) i) := by
  rw [strandIncl, lift_T]

/-- Adding an uncrossed last strand to a braid adds an uncrossed last strand to its image: the
braid homomorphisms are compatible with the strand inclusions of the braid groups and the tower
maps. -/
@[simp]
theorem braidHom_strandIncl (b : BraidGroup (n + 1)) :
    (braidHom R q (n + 2) (BraidGroup.strandIncl b) : TypeAHeckeAlgebra R q (n + 2)) =
      strandIncl R q (n + 1) (braidHom R q (n + 1) b) := by
  have h : (braidHom R q (n + 2)).comp BraidGroup.strandIncl =
      (Units.map (strandIncl R q (n + 1) : TypeAHeckeAlgebra R q (n + 1) →* _)).comp
        (braidHom R q (n + 1)) :=
    BraidGroup.hom_ext fun i ↦ Units.ext <| by
      simp only [MonoidHom.comp_apply, BraidGroup.strandIncl_sigma, braidHom_sigma,
        Units.coe_map, val_unitT, MonoidHom.coe_ofClass, strandIncl_T]
      exact congrArg (T q) (Fin.ext (by simp))
  exact congrArg Units.val (DFunLike.congr_fun h b)

end StrandIncl

section Infinite

variable (R q n) in
/-- The map from the type-A Hecke algebra on `n` strands to the infinite type-A Hecke algebra,
sending each generator to the generator with the same index. Its image is the stage of the first
`n` strands (`TauCeti.TypeAHeckeAlgebra.range_toInfinite`); that it is injective is the basis
theorem. -/
def toInfinite : TypeAHeckeAlgebra R q n →ₐ[R] InfiniteTypeAHeckeAlgebra R q :=
  lift (fun i ↦ InfiniteTypeAHeckeAlgebra.T q i) (fun _ ↦ InfiniteTypeAHeckeAlgebra.T_mul_self _)
    (fun {i j} h ↦ by rw [← h]; exact InfiniteTypeAHeckeAlgebra.T_braid _)
    (fun h ↦ (InfiniteTypeAHeckeAlgebra.commute_T (Or.inl h)).eq)

/-- The map to the infinite type-A Hecke algebra sends each generator to the generator with the
same index. -/
@[simp]
theorem toInfinite_T (i : Fin (n - 1)) :
    toInfinite R q n (T q i) = InfiniteTypeAHeckeAlgebra.T q i := by
  rw [toInfinite, lift_T]

/-- The image of the type-A Hecke algebra on `n` strands in the infinite type-A Hecke algebra is
the stage of the first `n` strands. -/
theorem range_toInfinite :
    (toInfinite R q n).range = InfiniteTypeAHeckeAlgebra.stage R q n := by
  rw [← Algebra.map_top, ← adjoin_range_T, AlgHom.map_adjoin, ← Set.range_comp]
  refine le_antisymm ?_ (InfiniteTypeAHeckeAlgebra.stage_le_iff.2 fun i hi ↦ ?_)
  · rw [Algebra.adjoin_le_iff, Set.range_subset_iff]
    exact fun i ↦ by
      simpa using InfiniteTypeAHeckeAlgebra.T_mem_stage (R := R) (q := q) (i := i) (by omega)
  · exact Algebra.subset_adjoin ⟨⟨i, by omega⟩, by simp⟩

/-- The maps to the infinite type-A Hecke algebra are compatible with the tower maps. -/
@[simp]
theorem toInfinite_strandIncl (x : TypeAHeckeAlgebra R q n) :
    toInfinite R q (n + 1) (strandIncl R q n x) = toInfinite R q n x := by
  have h : (toInfinite R q (n + 1)).comp (strandIncl R q n) = toInfinite R q n :=
    hom_ext fun i ↦ by simp
  exact DFunLike.congr_fun h x

/-- The map to the infinite type-A Hecke algebra intertwines the two braid homomorphisms. -/
@[simp]
theorem toInfinite_braidHom (b : BraidGroup n) :
    toInfinite R q n (braidHom R q n b) = InfiniteTypeAHeckeAlgebra.braidHom R q n b := by
  have h : (Units.map (toInfinite R q n : TypeAHeckeAlgebra R q n →* _)).comp (braidHom R q n) =
      InfiniteTypeAHeckeAlgebra.braidHom R q n :=
    BraidGroup.hom_ext fun i ↦ Units.ext <| by simp
  exact congrArg Units.val (DFunLike.congr_fun h b)

/-- The presentation does not collapse the scalars: `R` embeds in the type-A Hecke algebra on any
number of strands. -/
theorem algebraMap_injective : Function.Injective (algebraMap R (TypeAHeckeAlgebra R q n)) :=
  fun x y hxy ↦ InfiniteTypeAHeckeAlgebra.algebraMap_injective (q := q) <| by
    simpa only [AlgHom.commutes] using congrArg (toInfinite R q n) hxy

instance [Nontrivial R] : Nontrivial (TypeAHeckeAlgebra R q n) :=
  algebraMap_injective.nontrivial

end Infinite

section LeOne

/-- On at most one strand there are no generators, so every element is a scalar. -/
theorem algebraMap_surjective_of_le_one (h : n ≤ 1) :
    Function.Surjective (algebraMap R (TypeAHeckeAlgebra R q n)) := by
  have : IsEmpty (Fin (n - 1)) := ⟨fun i ↦ by have := i.isLt; omega⟩
  intro x
  have hx : x ∈ (⊥ : Subalgebra R (TypeAHeckeAlgebra R q n)) := by
    rw [← Algebra.adjoin_empty, ← Set.range_eq_empty (T (n := n) q), adjoin_range_T]
    trivial
  exact Algebra.mem_bot.1 hx

variable (R q) in
/-- On at most one strand the type-A Hecke algebra is canonically the coefficient ring. -/
noncomputable def algEquivOfLeOne (h : n ≤ 1) : R ≃ₐ[R] TypeAHeckeAlgebra R q n :=
  AlgEquiv.ofBijective (Algebra.ofId R _)
    ⟨algebraMap_injective, algebraMap_surjective_of_le_one h⟩

/-- The identification of the coefficient ring with the type-A Hecke algebra on at most one
strand is the structure map. -/
@[simp]
theorem algEquivOfLeOne_apply (h : n ≤ 1) (r : R) :
    algEquivOfLeOne R q h r = algebraMap R _ r := (rfl)

end LeOne

end TypeAHeckeAlgebra

end TauCeti
