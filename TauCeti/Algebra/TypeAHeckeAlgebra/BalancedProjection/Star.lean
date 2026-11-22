/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Star.SelfAdjoint
public import TauCeti.Algebra.TypeAHeckeAlgebra.BalancedProjection.Complement
public import TauCeti.Algebra.TypeAHeckeAlgebra.Star
public import TauCeti.Algebra.TypeAHeckeAlgebra.UnitaryStar

/-!
# Star structure on the balanced projection algebra and Hecke star equivalences

When `τ : R` in a commutative star ring is self-adjoint (`Fact (IsSelfAdjoint τ)`),
`BalancedProjectionAlgebra R τ` carries a unital `⋆`-algebra structure fixing each `e i` and
conjugating scalars. Every `e i` is a star projection, the finite stages are `⋆`-invariant,
`complementEquiv` (`e i ↦ 1 - e i`) is an involutive `⋆`-automorphism, and an `R`-algebra map
preserves `⋆` iff it maps every generator to a self-adjoint element.

Whenever `τ * (q + q⁻¹) ^ 2 = 1`, `BalancedProjectionAlgebra.heckeEquiv` upgrades to a
`⋆`-algebra isomorphism `BalancedProjectionAlgebra R τ ≃⋆ₐ[R] InfiniteTypeAHeckeAlgebra R q` in
both involutive parameter fibers:
* **real-parameter fiber** (`Fact (IsSelfAdjoint (q : R))`, `star (T i) = T i`);
* **unit-circle fiber** (`Fact ((q : R) ∈ unitary R)`, `star (T i) = T i⁻¹ = T i - (q - q⁻¹)`).

## Main definitions and results

* `TauCeti.BalancedProjectionAlgebra.instStarRing`, `instStarModule`: `⋆`-algebra structure for
  self-adjoint `τ`.
* `TauCeti.BalancedProjectionAlgebra.liftStarAlgHom`, `complementStarAlgEquiv`,
  `characterStarAlgHom`: `⋆`-universal property, complement `⋆`-automorphism, and scalar characters.
* `TauCeti.BalancedProjectionAlgebra.heckeStarAlgEquiv`,
  `TauCeti.BalancedProjectionAlgebra.UnitCircle.heckeStarAlgEquiv`: real-fiber and unit-circle
  `⋆`-isomorphisms with `InfiniteTypeAHeckeAlgebra R q`.

## References

* H. Wenzl, *Hecke algebras of type A_n and subfactors*, Invent. Math. 92 (1988), 349–383, §§2–3.
* V. F. R. Jones, *Hecke algebra representations of braid groups and link polynomials*,
  Ann. of Math. 126 (1987), 335–388, §§4, 11.
-/

public section

namespace TauCeti

namespace BalancedProjectionAlgebra

open MulOpposite

section Star

variable {R : Type*} [CommRing R] [StarRing R] {τ : R} [hτ : Fact (IsSelfAdjoint τ)]

/-- The conjugate-linear anti-automorphism fixing every generator `e i`, bundled with its
generator and scalar evaluation laws so the twisted opposite algebra remains local. -/
private def conjugateReverseData :
    { f : BalancedProjectionAlgebra R τ →+* (BalancedProjectionAlgebra R τ)ᵐᵒᵖ //
      (∀ i, f (e τ i) = op (e τ i)) ∧
      (∀ r, f (algebraMap R _ r) = op (algebraMap R _ (star r))) } := by
  letI : Algebra R (BalancedProjectionAlgebra R τ)ᵐᵒᵖ := Algebra.compHom _ (starRingEnd R)
  let f : BalancedProjectionAlgebra R τ →ₐ[R] (BalancedProjectionAlgebra R τ)ᵐᵒᵖ :=
    lift (fun i ↦ op (e τ i))
      (fun i ↦ unop_injective <| by
        simpa only [unop_mul, unop_op] using e_mul_self (R := R) (τ := τ) i)
      (fun i ↦ unop_injective <| by
        simp only [unop_sub, unop_mul, unop_op, Algebra.smul_def,
          Algebra.compHom_algebraMap_apply, starRingEnd_apply, MulOpposite.algebraMap_apply,
          hτ.out.star_eq, ← Algebra.commutes]
        simpa only [Algebra.smul_def, mul_assoc] using e_balanced (R := R) (τ := τ) i)
      (fun h ↦ unop_injective <| (commute_e (R := R) (τ := τ) (Or.inl h)).eq.symm)
  refine ⟨f.toRingHom, fun i ↦ ?_, fun r ↦ ?_⟩
  · rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    exact lift_e _ _ _ _ i
  · rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes]
    simp [Algebra.compHom_algebraMap_apply, starRingEnd_apply]

private def conjugateReverse :
    BalancedProjectionAlgebra R τ →+* (BalancedProjectionAlgebra R τ)ᵐᵒᵖ :=
  (conjugateReverseData (R := R) (τ := τ)).val

private theorem conjugateReverse_e (i : ℕ) : conjugateReverse (e (R := R) τ i) = op (e τ i) :=
  (conjugateReverseData (R := R) (τ := τ)).property.left i

private theorem conjugateReverse_algebraMap (r : R) :
    conjugateReverse (algebraMap R (BalancedProjectionAlgebra R τ) r) =
      op (algebraMap R _ (star r)) :=
  (conjugateReverseData (R := R) (τ := τ)).property.right r

private theorem conjugateReverse_involutive (x : BalancedProjectionAlgebra R τ) :
    unop (conjugateReverse (unop (conjugateReverse x))) = x := by
  have hx : x ∈ Algebra.adjoin R (Set.range (e (R := R) τ)) := by simp [adjoin_range_e]
  induction hx using Algebra.adjoin_induction with
  | mem _ hx => rcases hx with ⟨i, rfl⟩; simp [conjugateReverse_e]
  | algebraMap r => simp [conjugateReverse_algebraMap]
  | add x y _ _ hx hy => simp [map_add, hx, hy]
  | mul x y _ _ hx hy => simp [map_mul, hx, hy]

/-- When `τ` is self-adjoint, `BalancedProjectionAlgebra R τ` is a star ring in which every
generator `e i` is self-adjoint and scalars are conjugated. -/
@[no_expose]
instance instStarRing : StarRing (BalancedProjectionAlgebra R τ) where
  star x := unop (conjugateReverse x)
  star_involutive := conjugateReverse_involutive
  star_mul x y := by simp [map_mul]
  star_add x y := by simp [map_add]

/-- Every generator `e i` is self-adjoint. -/
@[simp]
theorem star_e (i : ℕ) : star (e (R := R) τ i) = e τ i :=
  congrArg unop (conjugateReverse_e i)

/-- Every generator `e i` is self-adjoint as an `IsSelfAdjoint` predicate. -/
theorem isSelfAdjoint_e (i : ℕ) : IsSelfAdjoint (e (R := R) τ i) := star_e i

/-- Every generator `e i` is a star projection. -/
theorem isStarProjection_e (i : ℕ) : IsStarProjection (e (R := R) τ i) :=
  ⟨isIdempotentElem_e i, isSelfAdjoint_e i⟩

/-- Scalar multiplication is conjugate-linear with respect to `star`. -/
instance instStarModule : StarModule R (BalancedProjectionAlgebra R τ) where
  star_smul r x := by
    have h : star (algebraMap R (BalancedProjectionAlgebra R τ) r) = algebraMap R _ (star r) :=
      congrArg unop (conjugateReverse_algebraMap r)
    simp [Algebra.smul_def, star_mul, h, Algebra.commutes]

section UniversalProperty

variable {A : Type*} [Ring A] [StarRing A] [Algebra R A] [StarModule R A]

/-- An algebra map out of `BalancedProjectionAlgebra R τ` preserves `star` if and only if each
generator image is self-adjoint. -/
theorem map_star_iff {F : BalancedProjectionAlgebra R τ →ₐ[R] A} :
    (∀ x, F (star x) = star (F x)) ↔ ∀ i, IsSelfAdjoint (F (e τ i)) := by
  constructor
  · exact fun h i ↦ by simpa only [IsSelfAdjoint, star_e] using (h (e τ i)).symm
  · intro h x
    have hx : x ∈ Algebra.adjoin R (Set.range (e (R := R) τ)) := by simp [adjoin_range_e]
    induction hx using Algebra.adjoin_induction with
    | mem _ hx => rcases hx with ⟨i, rfl⟩; simp only [star_e, (h i).star_eq]
    | algebraMap r => simp [← algebraMap_star_comm]
    | add x y _ _ hx hy => simp only [star_add, map_add, hx, hy]
    | mul x y _ _ hx hy => simp only [star_mul, map_mul, hx, hy]

/-- Universal property of `BalancedProjectionAlgebra R τ` as a unital `⋆`-algebra: a sequence of
star projections satisfying the balanced and distant-commutation relations extends to a unique
`⋆`-algebra homomorphism. -/
def liftStarAlgHom (f : ℕ → A) (hf : ∀ i, IsStarProjection (f i))
    (hbal : ∀ i, f i * f (i + 1) * f i - τ • f i = f (i + 1) * f i * f (i + 1) - τ • f (i + 1))
    (hdist : ∀ {i j : ℕ}, i + 2 ≤ j → f i * f j = f j * f i) :
    BalancedProjectionAlgebra R τ →⋆ₐ[R] A :=
  { lift f (fun i ↦ (hf i).isIdempotentElem) hbal hdist with
    map_star' := map_star_iff.mpr fun i ↦ by simpa using (hf i).isSelfAdjoint }

@[simp]
theorem liftStarAlgHom_e (f : ℕ → A) (hf) (hbal) (hdist) (i : ℕ) :
    liftStarAlgHom (τ := τ) f hf hbal hdist (e τ i) = f i := lift_e _ _ _ _ i

@[simp]
theorem toAlgHom_liftStarAlgHom (f : ℕ → A) (hf) (hbal) (hdist) :
    (liftStarAlgHom (τ := τ) f hf hbal hdist).toAlgHom =
      lift f (fun i ↦ (hf i).isIdempotentElem) hbal hdist := (rfl)

/-- Two `⋆`-algebra homomorphisms out of `BalancedProjectionAlgebra R τ` agreeing on all generators
are equal. -/
@[ext high]
theorem starAlgHom_ext {B : Type*} [Semiring B] [StarRing B] [Algebra R B]
    {F G : BalancedProjectionAlgebra R τ →⋆ₐ[R] B}
    (h : ∀ i, F (e τ i) = G (e τ i)) : F = G :=
  StarAlgHom.ext fun x ↦ DFunLike.congr_fun (hom_ext (F := F.toAlgHom) (G := G.toAlgHom) h) x

end UniversalProperty

/-- Every finite stage `stage R τ n` is invariant under the involution. -/
@[simp]
theorem star_mem_stage_iff {n : ℕ} {x : BalancedProjectionAlgebra R τ} :
    star x ∈ stage R τ n ↔ x ∈ stage R τ n := by
  have h : stage R τ n ≤ star (stage R τ n) := stage_le_iff.mpr fun i hi ↦ by
    simpa only [Subalgebra.mem_star_iff, star_e] using e_mem_stage (R := R) (τ := τ) hi
  exact ⟨fun hx ↦ by simpa only [Subalgebra.mem_star_iff, star_star] using h hx,
    fun hx ↦ (Subalgebra.mem_star_iff _ _).mp (h hx)⟩

/-- The complement automorphism `e i ↦ 1 - e i` commutes with the involution. -/
@[simp]
theorem complementEquiv_star (x : BalancedProjectionAlgebra R τ) :
    complementEquiv τ (star x) = star (complementEquiv τ x) :=
  map_star_iff (F := (complementEquiv τ).toAlgHom) |>.mpr
    (fun i ↦ by simpa using (isStarProjection_e (R := R) (τ := τ) i).one_sub.isSelfAdjoint) x

variable (τ) in
/-- `complementEquiv` bundled as an involutive `⋆`-algebra equivalence. -/
def complementStarAlgEquiv :
    BalancedProjectionAlgebra R τ ≃⋆ₐ[R] BalancedProjectionAlgebra R τ :=
  { complementEquiv τ with
    map_star' := complementEquiv_star
    map_smul' := map_smul (complementEquiv τ) }

@[simp]
theorem toAlgEquiv_complementStarAlgEquiv :
    (complementStarAlgEquiv (R := R) τ).toAlgEquiv = complementEquiv τ := (rfl)

@[simp]
theorem complementStarAlgEquiv_symm :
    (complementStarAlgEquiv (R := R) τ).symm = complementStarAlgEquiv τ :=
  StarAlgEquiv.toAlgEquiv_injective (complementEquiv_symm τ)

@[simp]
theorem complementStarAlgEquiv_complementStarAlgEquiv (x : BalancedProjectionAlgebra R τ) :
    complementStarAlgEquiv (R := R) τ (complementStarAlgEquiv τ x) = x :=
  complementEquiv_complementEquiv τ x

@[simp]
theorem complementStarAlgEquiv_e (i : ℕ) :
    complementStarAlgEquiv (R := R) τ (e τ i) = 1 - e τ i := complementEquiv_e τ i

/-- A scalar character at a self-adjoint idempotent `c : R` preserves `star`. -/
@[simp]
theorem character_star {c : R} (hc : IsIdempotentElem c) (hcsa : IsSelfAdjoint c)
    (x : BalancedProjectionAlgebra R τ) :
    character c hc (star x) = star (character c hc x) :=
  map_star_iff.mpr (fun _ ↦ by simpa using hcsa) x

/-- A scalar character at a star projection `c : R`, bundled as a `⋆`-algebra homomorphism. -/
def characterStarAlgHom (c : R) (hc : IsStarProjection c) :
    BalancedProjectionAlgebra R τ →⋆ₐ[R] R :=
  { character c hc.isIdempotentElem with
    map_star' := character_star hc.isIdempotentElem hc.isSelfAdjoint }

@[simp]
theorem toAlgHom_characterStarAlgHom (c : R) (hc : IsStarProjection c) :
    (characterStarAlgHom (τ := τ) c hc).toAlgHom = character c hc.isIdempotentElem := (rfl)

@[simp]
theorem characterStarAlgHom_apply (c : R) (hc : IsStarProjection c)
    (x : BalancedProjectionAlgebra R τ) :
    characterStarAlgHom (τ := τ) c hc x = character c hc.isIdempotentElem x := (rfl)

/-- Evaluating `characterStarAlgHom` on any generator `e τ i` returns `c`. -/
theorem characterStarAlgHom_e (c : R) (hc : IsStarProjection c) (i : ℕ) :
    characterStarAlgHom (τ := τ) c hc (e τ i) = c := character_e c hc.isIdempotentElem i

private theorem heckeEquiv_star_of_eigenprojection {q : Rˣ}
    [StarRing (InfiniteTypeAHeckeAlgebra R q)] [StarModule R (InfiniteTypeAHeckeAlgebra R q)]
    (hτ : τ * ((q : R) + ↑q⁻¹) ^ 2 = 1)
    (hP : ∀ s : Rˣ, (s : R) = q + ↑q⁻¹ →
      ∀ i, IsSelfAdjoint ((↑s⁻¹ : R) • (InfiniteTypeAHeckeAlgebra.T q i + algebraMap R _ ↑q⁻¹)))
    (x : BalancedProjectionAlgebra R τ) :
    heckeEquiv q hτ (star x) = star (heckeEquiv q hτ x) :=
  map_star_iff (F := (heckeEquiv q hτ).toAlgHom) |>.mpr (fun i ↦ by
    simpa only [AlgEquiv.toAlgHom_apply, heckeEquiv_e, ← val_inv_addInvUnit hτ] using
      hP (addInvUnit hτ) (val_addInvUnit hτ) i) x

end Star

end BalancedProjectionAlgebra

/-! ### Real-parameter Hecke star compatibility -/

section RealHecke

open InfiniteTypeAHeckeAlgebra (T)

variable {R : Type*} [CommRing R] [StarRing R] {q : Rˣ} [hq : Fact (IsSelfAdjoint (q : R))]

namespace BalancedProjectionAlgebra

variable {τ : R} [Fact (IsSelfAdjoint τ)]

/-- In the real-parameter fiber, `heckeEquiv` commutes with the involutions. -/
@[simp]
theorem heckeEquiv_star (hτ : τ * ((q : R) + ↑q⁻¹) ^ 2 = 1)
    (x : BalancedProjectionAlgebra R τ) :
    heckeEquiv q hτ (star x) = star (heckeEquiv q hτ x) :=
  heckeEquiv_star_of_eigenprojection hτ
    (fun s hs i ↦ (InfiniteTypeAHeckeAlgebra.isStarProjection_eigenprojection s hs i).isSelfAdjoint)
    x

@[simp]
theorem heckeEquiv_symm_star (hτ : τ * ((q : R) + ↑q⁻¹) ^ 2 = 1)
    (x : InfiniteTypeAHeckeAlgebra R q) :
    (heckeEquiv q hτ).symm (star x) = star ((heckeEquiv q hτ).symm x) :=
  (heckeEquiv q hτ).injective <| by simp

variable (q) in
/-- In the real-parameter fiber, `BalancedProjectionAlgebra R τ` and
`InfiniteTypeAHeckeAlgebra R q` are isomorphic as `⋆`-algebras whenever `τ * (q + q⁻¹) ^ 2 = 1`. -/
def heckeStarAlgEquiv (hτ : τ * ((q : R) + ↑q⁻¹) ^ 2 = 1) :
    BalancedProjectionAlgebra R τ ≃⋆ₐ[R] InfiniteTypeAHeckeAlgebra R q :=
  { heckeEquiv q hτ with map_star' := heckeEquiv_star hτ, map_smul' := map_smul (heckeEquiv q hτ) }

@[simp]
theorem toAlgEquiv_heckeStarAlgEquiv (hτ : τ * ((q : R) + ↑q⁻¹) ^ 2 = 1) :
    (heckeStarAlgEquiv q hτ).toAlgEquiv = heckeEquiv q hτ := (rfl)

@[simp]
theorem heckeStarAlgEquiv_e (hτ : τ * ((q : R) + ↑q⁻¹) ^ 2 = 1) (i : ℕ) :
    heckeStarAlgEquiv q hτ (e τ i) =
      (τ * ((q : R) + ↑q⁻¹)) • (T q i + algebraMap R _ ↑q⁻¹) := heckeEquiv_e hτ i

@[simp]
theorem heckeStarAlgEquiv_symm_T (hτ : τ * ((q : R) + ↑q⁻¹) ^ 2 = 1) (i : ℕ) :
    (heckeStarAlgEquiv q hτ).symm (T q i) =
      ((q : R) + ↑q⁻¹) • e τ i - algebraMap R _ ↑q⁻¹ := heckeEquiv_symm_T hτ i

end BalancedProjectionAlgebra

end RealHecke

/-! ### Unit-circle Hecke star compatibility -/

section UnitCircleHecke

open InfiniteTypeAHeckeAlgebra (T)

variable {R : Type*} [CommRing R] [StarRing R] {q : Rˣ} [hq : Fact ((q : R) ∈ unitary R)]

namespace BalancedProjectionAlgebra.UnitCircle

variable {τ : R} [Fact (IsSelfAdjoint τ)]

/-- In the unit-circle fiber, `heckeEquiv` commutes with the involutions. -/
@[simp]
theorem heckeEquiv_star (hτ : τ * ((q : R) + ↑q⁻¹) ^ 2 = 1)
    (x : BalancedProjectionAlgebra R τ) :
    heckeEquiv q hτ (star x) = star (heckeEquiv q hτ x) :=
  heckeEquiv_star_of_eigenprojection hτ
    (fun s hs i ↦
      (InfiniteTypeAHeckeAlgebra.UnitCircle.isStarProjection_eigenprojection s hs i).isSelfAdjoint)
    x

@[simp]
theorem heckeEquiv_symm_star (hτ : τ * ((q : R) + ↑q⁻¹) ^ 2 = 1)
    (x : InfiniteTypeAHeckeAlgebra R q) :
    (heckeEquiv q hτ).symm (star x) = star ((heckeEquiv q hτ).symm x) :=
  (heckeEquiv q hτ).injective <| by simp

variable (q) in
/-- In the unit-circle fiber, `BalancedProjectionAlgebra R τ` and
`InfiniteTypeAHeckeAlgebra R q` are isomorphic as `⋆`-algebras whenever `τ * (q + q⁻¹) ^ 2 = 1`. -/
def heckeStarAlgEquiv (hτ : τ * ((q : R) + ↑q⁻¹) ^ 2 = 1) :
    BalancedProjectionAlgebra R τ ≃⋆ₐ[R] InfiniteTypeAHeckeAlgebra R q :=
  { heckeEquiv q hτ with map_star' := heckeEquiv_star hτ, map_smul' := map_smul (heckeEquiv q hτ) }

@[simp]
theorem toAlgEquiv_heckeStarAlgEquiv (hτ : τ * ((q : R) + ↑q⁻¹) ^ 2 = 1) :
    (heckeStarAlgEquiv q hτ).toAlgEquiv = heckeEquiv q hτ := (rfl)

@[simp]
theorem heckeStarAlgEquiv_e (hτ : τ * ((q : R) + ↑q⁻¹) ^ 2 = 1) (i : ℕ) :
    heckeStarAlgEquiv q hτ (e τ i) =
      (τ * ((q : R) + ↑q⁻¹)) • (T q i + algebraMap R _ ↑q⁻¹) := heckeEquiv_e hτ i

@[simp]
theorem heckeStarAlgEquiv_symm_T (hτ : τ * ((q : R) + ↑q⁻¹) ^ 2 = 1) (i : ℕ) :
    (heckeStarAlgEquiv q hτ).symm (T q i) =
      ((q : R) + ↑q⁻¹) • e τ i - algebraMap R _ ↑q⁻¹ := heckeEquiv_symm_T hτ i

end BalancedProjectionAlgebra.UnitCircle

end UnitCircleHecke

end TauCeti
