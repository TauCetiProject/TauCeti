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
import Mathlib.Tactic.LinearCombination

/-!
# Star structure on the balanced projection algebra and Hecke star equivalences

When the parameter `τ : R` in a commutative star ring is self-adjoint (`Fact (IsSelfAdjoint τ)`),
`BalancedProjectionAlgebra R τ` carries a unital `⋆`-algebra structure fixing every generator `e i`
and conjugating scalars. Each generator `e i` is then a star projection
(`IsStarProjection (e τ i)`), the finite stages `stage R τ n` are `⋆`-invariant, `complementEquiv`
(`e i ↦ 1 - e i`) is an involutive `⋆`-automorphism, and an `R`-algebra map preserves `⋆` if and
only if it maps every generator to a self-adjoint element (hence a star projection).

Whenever `τ * (q + q⁻¹) ^ 2 = 1`, `BalancedProjectionAlgebra.heckeEquiv` upgrades to a
`⋆`-algebra isomorphism `BalancedProjectionAlgebra R τ ≃⋆ₐ[R] InfiniteTypeAHeckeAlgebra R q` in
both involutive parameter fibers of the type-A Hecke algebra:

* in the **real-parameter fiber** (`Fact (IsSelfAdjoint (q : R))`, where `star (T i) = T i`),
  `q + q⁻¹` is self-adjoint, so `τ` is automatically self-adjoint and the eigenprojection
  `(q + q⁻¹)⁻¹ • (T i + q⁻¹)` is a star projection;
* in the **unit-circle fiber** (`Fact ((q : R) ∈ unitary R)`, where
  `star (T i) = T i⁻¹ = T i - (q - q⁻¹)`), `q + q⁻¹ = q + star q` is again self-adjoint, `τ` is
  self-adjoint, and `star (T i + q⁻¹) = (T i - (q - q⁻¹)) + q = T i + q⁻¹`, so the eigenprojection
  is again a star projection.

## Main definitions

* `TauCeti.BalancedProjectionAlgebra.instStarRing`,
  `TauCeti.BalancedProjectionAlgebra.instStarModule`: the `⋆`-algebra structure for self-adjoint
  `τ`.
* `TauCeti.BalancedProjectionAlgebra.liftStarAlgHom`: the universal property for sequences of
  balanced star projections.
* `TauCeti.BalancedProjectionAlgebra.complementStarAlgEquiv`: `e i ↦ 1 - e i` as a `⋆`-equivalence.
* `TauCeti.BalancedProjectionAlgebra.characterStarAlgHom`: scalar characters `e i ↦ c` for a star
  projection `c : R`.
* `TauCeti.BalancedProjectionAlgebra.heckeStarAlgEquiv`: the real-fiber `⋆`-isomorphism with
  `InfiniteTypeAHeckeAlgebra R q`.
* `TauCeti.BalancedProjectionAlgebra.UnitCircle.heckeStarAlgEquiv`: the unit-circle `⋆`-isomorphism
  with `InfiniteTypeAHeckeAlgebra R q`.

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

/-- The conjugate-linear anti-automorphism fixing every generator `e i`, bundled into the opposite
algebra. -/
private def conjugateReverse :
    BalancedProjectionAlgebra R τ →+* (BalancedProjectionAlgebra R τ)ᵐᵒᵖ := by
  letI : Algebra R (BalancedProjectionAlgebra R τ)ᵐᵒᵖ :=
    Algebra.compHom _ (starRingEnd R)
  exact (lift (fun i ↦ op (e τ i))
    (fun i ↦ unop_injective <| by
      simpa only [unop_mul, unop_op] using e_mul_self (R := R) (τ := τ) i)
    (fun i ↦ unop_injective <| by
      simp only [unop_sub, unop_mul, unop_op, Algebra.smul_def,
        Algebra.compHom_algebraMap_apply, starRingEnd_apply, MulOpposite.algebraMap_apply,
        hτ.out.star_eq, ← Algebra.commutes]
      simpa only [Algebra.smul_def, mul_assoc] using e_balanced (R := R) (τ := τ) i)
    (fun h ↦ unop_injective <| (commute_e (R := R) (τ := τ) (Or.inl h)).eq.symm)).toRingHom

private theorem conjugateReverse_e (i : ℕ) :
    conjugateReverse (e (R := R) τ i) = op (e τ i) :=
  @lift_e R _ τ _ _ (Algebra.compHom _ (starRingEnd R)) _ _ _ _ i

private theorem conjugateReverse_algebraMap (r : R) :
    conjugateReverse (algebraMap R (BalancedProjectionAlgebra R τ) r) =
      op (algebraMap R _ (star r)) := by
  simp [conjugateReverse, Algebra.compHom_algebraMap_apply, starRingEnd_apply]

private theorem conjugateReverse_involutive (x : BalancedProjectionAlgebra R τ) :
    unop (conjugateReverse (unop (conjugateReverse x))) = x := by
  have hx : x ∈ Algebra.adjoin R (Set.range (e (R := R) τ)) := by simp [adjoin_range_e]
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    simp [conjugateReverse_e]
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
theorem isSelfAdjoint_e (i : ℕ) : IsSelfAdjoint (e (R := R) τ i) :=
  star_e i

/-- Every generator `e i` is a star projection. -/
theorem isStarProjection_e (i : ℕ) : IsStarProjection (e (R := R) τ i) :=
  ⟨isIdempotentElem_e i, isSelfAdjoint_e i⟩

private theorem star_algebraMap (r : R) :
    star (algebraMap R (BalancedProjectionAlgebra R τ) r) = algebraMap R _ (star r) :=
  congrArg unop (conjugateReverse_algebraMap r)

/-- Scalar multiplication is conjugate-linear with respect to `star`. -/
instance instStarModule : StarModule R (BalancedProjectionAlgebra R τ) where
  star_smul r x := by simp [Algebra.smul_def, star_mul, star_algebraMap, Algebra.commutes]

section UniversalProperty

variable {A : Type*} [Ring A] [StarRing A] [Algebra R A] [StarModule R A]

/-- An algebra map out of `BalancedProjectionAlgebra R τ` preserves `star` if and only if each
generator image is self-adjoint. -/
theorem map_star_iff {F : BalancedProjectionAlgebra R τ →ₐ[R] A} :
    (∀ x, F (star x) = star (F x)) ↔ ∀ i, IsSelfAdjoint (F (e τ i)) := by
  constructor
  · intro h i
    simpa only [IsSelfAdjoint, star_e] using (h (e τ i)).symm
  · intro h x
    have hx : x ∈ Algebra.adjoin R (Set.range (e (R := R) τ)) := by simp [adjoin_range_e]
    induction hx using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      simp only [star_e, (h i).star_eq]
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
    liftStarAlgHom (τ := τ) f hf hbal hdist (e τ i) = f i :=
  lift_e _ _ _ _ i

@[simp]
theorem toAlgHom_liftStarAlgHom (f : ℕ → A) (hf) (hbal) (hdist) :
    (liftStarAlgHom (τ := τ) f hf hbal hdist).toAlgHom =
      lift f (fun i ↦ (hf i).isIdempotentElem) hbal hdist :=
  (rfl)

/-- Two `⋆`-algebra homomorphisms out of `BalancedProjectionAlgebra R τ` agreeing on all generators
are equal. -/
@[ext high]
theorem starAlgHom_ext {B : Type*} [Semiring B] [StarRing B] [Algebra R B]
    {F G : BalancedProjectionAlgebra R τ →⋆ₐ[R] B}
    (h : ∀ i, F (e τ i) = G (e τ i)) : F = G := by
  ext x
  exact DFunLike.congr_fun (hom_ext (F := F.toAlgHom) (G := G.toAlgHom) h) x

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
    (complementStarAlgEquiv (R := R) τ).toAlgEquiv = complementEquiv τ :=
  (rfl)

@[simp]
theorem complementStarAlgEquiv_e (i : ℕ) :
    complementStarAlgEquiv (R := R) τ (e τ i) = 1 - e τ i :=
  complementEquiv_e τ i

/-- A scalar character at a self-adjoint idempotent `c : R` preserves `star`. -/
@[simp]
theorem character_star {c : R} (hc : IsIdempotentElem c) (hcsa : IsSelfAdjoint c)
    (x : BalancedProjectionAlgebra R τ) :
    character c hc (star x) = star (character c hc x) :=
  map_star_iff.mpr (fun i ↦ by simpa using hcsa) x

/-- A scalar character at a star projection `c : R`, bundled as a `⋆`-algebra homomorphism. -/
def characterStarAlgHom (c : R) (hc : IsStarProjection c) :
    BalancedProjectionAlgebra R τ →⋆ₐ[R] R :=
  { character c hc.isIdempotentElem with
    map_star' := character_star hc.isIdempotentElem hc.isSelfAdjoint }

@[simp]
theorem toAlgHom_characterStarAlgHom (c : R) (hc : IsStarProjection c) :
    (characterStarAlgHom (τ := τ) c hc).toAlgHom = character c hc.isIdempotentElem :=
  (rfl)

@[simp]
theorem characterStarAlgHom_apply (c : R) (hc : IsStarProjection c)
    (x : BalancedProjectionAlgebra R τ) :
    characterStarAlgHom (τ := τ) c hc x = character c hc.isIdempotentElem x :=
  (rfl)

/-- Evaluating `characterStarAlgHom` on any generator `e τ i` returns `c`. -/
theorem characterStarAlgHom_e (c : R) (hc : IsStarProjection c) (i : ℕ) :
    characterStarAlgHom (τ := τ) c hc (e τ i) = c :=
  character_e c hc.isIdempotentElem i

end Star

end BalancedProjectionAlgebra

/-! ### Real-parameter Hecke star compatibility -/

section RealHecke

open InfiniteTypeAHeckeAlgebra (T)

variable {R : Type*} [CommRing R] [StarRing R] {q : Rˣ} [hq : Fact (IsSelfAdjoint (q : R))]

namespace InfiniteTypeAHeckeAlgebra

/-- In the real-parameter fiber, the eigenprojection `P = (q + q⁻¹)⁻¹ • (T i + q⁻¹)` is a star
projection. -/
theorem isStarProjection_eigenprojection (s : Rˣ) (hs : (s : R) = q + ↑q⁻¹) (i : ℕ) :
    IsStarProjection ((↑s⁻¹ : R) • (T q i + algebraMap R _ (↑q⁻¹ : R))) where
  isIdempotentElem := isIdempotentElem_eigenprojection s hs i
  isSelfAdjoint := by
    have hqinv : IsSelfAdjoint (↑q⁻¹ : R) := hq.out.units_inv
    have hs_sa : IsSelfAdjoint (s : R) := hs ▸ hq.out.add hqinv
    have hsinv_sa : IsSelfAdjoint (↑s⁻¹ : R) := hs_sa.units_inv
    rw [IsSelfAdjoint, star_smul, hsinv_sa.star_eq, star_add, star_T, ← algebraMap_star_comm,
      hqinv.star_eq]

end InfiniteTypeAHeckeAlgebra

namespace BalancedProjectionAlgebra

variable {τ : R} [Fact (IsSelfAdjoint τ)]

/-- In the real-parameter fiber, `heckeEquiv` commutes with the involutions. -/
@[simp]
theorem heckeEquiv_star (hτ : τ * ((q : R) + ↑q⁻¹) ^ 2 = 1)
    (x : BalancedProjectionAlgebra R τ) :
    heckeEquiv q hτ (star x) = star (heckeEquiv q hτ x) := by
  let s : Rˣ := Units.mkOfMulEqOne ((q : R) + ↑q⁻¹) (τ * ((q : R) + ↑q⁻¹))
    (by linear_combination hτ)
  have hsinv : (↑s⁻¹ : R) = τ * ((q : R) + ↑q⁻¹) := rfl
  exact map_star_iff (F := (heckeEquiv q hτ).toAlgHom) |>.mpr (fun i ↦ by
    simpa only [AlgEquiv.toAlgHom_apply, heckeEquiv_e, ← hsinv] using
      (InfiniteTypeAHeckeAlgebra.isStarProjection_eigenprojection s rfl i).isSelfAdjoint) x

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
  { heckeEquiv q hτ with
    map_star' := heckeEquiv_star hτ
    map_smul' := map_smul (heckeEquiv q hτ) }

@[simp]
theorem toAlgEquiv_heckeStarAlgEquiv (hτ : τ * ((q : R) + ↑q⁻¹) ^ 2 = 1) :
    (heckeStarAlgEquiv q hτ).toAlgEquiv = heckeEquiv q hτ :=
  (rfl)

@[simp]
theorem heckeStarAlgEquiv_e (hτ : τ * ((q : R) + ↑q⁻¹) ^ 2 = 1) (i : ℕ) :
    heckeStarAlgEquiv q hτ (e τ i) =
      (τ * ((q : R) + ↑q⁻¹)) • (T q i + algebraMap R _ ↑q⁻¹) :=
  heckeEquiv_e hτ i

@[simp]
theorem heckeStarAlgEquiv_symm_T (hτ : τ * ((q : R) + ↑q⁻¹) ^ 2 = 1) (i : ℕ) :
    (heckeStarAlgEquiv q hτ).symm (T q i) =
      ((q : R) + ↑q⁻¹) • e τ i - algebraMap R _ ↑q⁻¹ :=
  heckeEquiv_symm_T hτ i

end BalancedProjectionAlgebra

end RealHecke

/-! ### Unit-circle Hecke star compatibility -/

section UnitCircleHecke

open InfiniteTypeAHeckeAlgebra (T unitT val_inv_unitT)

variable {R : Type*} [CommRing R] [StarRing R] {q : Rˣ} [hq : Fact ((q : R) ∈ unitary R)]

namespace InfiniteTypeAHeckeAlgebra.UnitCircle

/-- In the unit-circle fiber, `star (T i + q⁻¹) = T i + q⁻¹` since
`star (T i) = T i - (q - q⁻¹)` and `star (q⁻¹) = q`, so the eigenprojection
`P = (q + q⁻¹)⁻¹ • (T i + q⁻¹)` is again a star projection whenever `s = q + q⁻¹` is a unit. -/
theorem isStarProjection_eigenprojection (s : Rˣ) (hs : (s : R) = q + ↑q⁻¹) (i : ℕ) :
    IsStarProjection ((↑s⁻¹ : R) • (T q i + algebraMap R _ (↑q⁻¹ : R))) where
  isIdempotentElem := isIdempotentElem_eigenprojection s hs i
  isSelfAdjoint := by
    have hs_sa : IsSelfAdjoint (s : R) :=
      hs ▸ Units.isSelfAdjoint_add_inv_of_mem_unitary hq.out
    have hsinv_sa : IsSelfAdjoint (↑s⁻¹ : R) := hs_sa.of_mul_eq_one s.mul_inv
    have hT : IsSelfAdjoint (T q i + algebraMap R _ (↑q⁻¹ : R)) := by
      rw [IsSelfAdjoint, star_add, UnitCircle.star_T, val_inv_unitT, ← algebraMap_star_comm,
        Units.star_inv_eq_of_mem_unitary hq.out, map_sub]
      abel
    rw [IsSelfAdjoint, star_smul, hsinv_sa.star_eq, hT.star_eq]

end InfiniteTypeAHeckeAlgebra.UnitCircle

namespace BalancedProjectionAlgebra.UnitCircle

variable {τ : R} [Fact (IsSelfAdjoint τ)]

/-- In the unit-circle fiber, `heckeEquiv` commutes with the involutions. -/
@[simp]
theorem heckeEquiv_star (hτ : τ * ((q : R) + ↑q⁻¹) ^ 2 = 1)
    (x : BalancedProjectionAlgebra R τ) :
    heckeEquiv q hτ (star x) = star (heckeEquiv q hτ x) := by
  let s : Rˣ := Units.mkOfMulEqOne ((q : R) + ↑q⁻¹) (τ * ((q : R) + ↑q⁻¹))
    (by linear_combination hτ)
  have hsinv : (↑s⁻¹ : R) = τ * ((q : R) + ↑q⁻¹) := rfl
  exact map_star_iff (F := (heckeEquiv q hτ).toAlgHom) |>.mpr (fun i ↦ by
    simpa only [AlgEquiv.toAlgHom_apply, heckeEquiv_e, ← hsinv] using
      (InfiniteTypeAHeckeAlgebra.UnitCircle.isStarProjection_eigenprojection s rfl i).isSelfAdjoint)
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
  { heckeEquiv q hτ with
    map_star' := heckeEquiv_star hτ
    map_smul' := map_smul (heckeEquiv q hτ) }

@[simp]
theorem toAlgEquiv_heckeStarAlgEquiv (hτ : τ * ((q : R) + ↑q⁻¹) ^ 2 = 1) :
    (heckeStarAlgEquiv q hτ).toAlgEquiv = heckeEquiv q hτ :=
  (rfl)

@[simp]
theorem heckeStarAlgEquiv_e (hτ : τ * ((q : R) + ↑q⁻¹) ^ 2 = 1) (i : ℕ) :
    heckeStarAlgEquiv q hτ (e τ i) =
      (τ * ((q : R) + ↑q⁻¹)) • (T q i + algebraMap R _ ↑q⁻¹) :=
  heckeEquiv_e hτ i

@[simp]
theorem heckeStarAlgEquiv_symm_T (hτ : τ * ((q : R) + ↑q⁻¹) ^ 2 = 1) (i : ℕ) :
    (heckeStarAlgEquiv q hτ).symm (T q i) =
      ((q : R) + ↑q⁻¹) • e τ i - algebraMap R _ ↑q⁻¹ :=
  heckeEquiv_symm_T hτ i

end BalancedProjectionAlgebra.UnitCircle

end UnitCircleHecke

end TauCeti
