/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TypeAHeckeAlgebra.MarkovTrace
import Mathlib.Tactic.NoncommRing

/-!
# The complement automorphism of the Hecke tower

The substitution `T i ↦ -T i⁻¹ = (q - q⁻¹) - T i` defines an involutive algebra
automorphism at the same parameter `q`. It preserves every finite stage and commutes with
strand shifts. In the convention `g i = q • T i`, it sends `g i` to `q² - 1 - g i`.
Whenever `q + q⁻¹` is invertible, it exchanges the two normalized eigenprojections.

Precomposing a Markov trace of parameter `z` with this automorphism gives a Markov trace
of parameter `q - q⁻¹ - z`. Thus the two scalar characters, and more generally
complementary projection trace parameters, are exchanged without changing the tower.
No positivity or semisimplicity hypothesis is needed for this algebraic symmetry.

## References

* H. Wenzl, *Hecke algebras of type A_n and subfactors*, Invent. Math. 92 (1988),
  349–383, Sections 2–3 (the two eigenprojection conventions).
-/

public section

namespace TauCeti.InfiniteTypeAHeckeAlgebra

variable {R : Type*} [CommRing R] (q : Rˣ)

private def complementHom : InfiniteTypeAHeckeAlgebra R q →ₐ[R]
    InfiniteTypeAHeckeAlgebra R q :=
  lift (fun i ↦ -(↑(unitT q i)⁻¹ : InfiniteTypeAHeckeAlgebra R q))
    (fun i ↦ by
      simp only [val_inv_unitT, neg_sub, sub_mul, mul_sub, T_mul_self, Algebra.smul_def]
      simp only [← Algebra.commutes]
      abel)
    (fun i ↦ by
      have h : unitT q i * unitT q (i + 1) * unitT q i =
          unitT q (i + 1) * unitT q i * unitT q (i + 1) :=
        Units.ext (by simpa only [Units.val_mul, val_unitT] using T_braid (q := q) i)
      have hi := congrArg (fun u : (InfiniteTypeAHeckeAlgebra R q)ˣ ↦
        (↑u⁻¹ : InfiniteTypeAHeckeAlgebra R q)) h
      simpa only [mul_inv_rev, Units.val_mul, mul_assoc, neg_mul, mul_neg, neg_inj]
        using hi)
    (fun h ↦ by
      have hc : Commute (unitT q _) (unitT q _) := Units.ext (by
        simpa only [Units.val_mul, val_unitT] using (commute_T (q := q) (Or.inl h)).eq)
      simpa only [Units.val_mul, neg_mul, mul_neg, neg_neg] using
        congrArg (fun u : (InfiniteTypeAHeckeAlgebra R q)ˣ ↦
          (u : InfiniteTypeAHeckeAlgebra R q)) hc.inv_inv.eq)

private theorem complementHom_T (i : ℕ) :
    complementHom q (T q i) = algebraMap R _ ((q : R) - ↑q⁻¹) - T q i := by
  simp [complementHom]

private theorem complementHom_comp_self :
    (complementHom q).comp (complementHom q) = AlgHom.id R _ := by
  ext i
  simp [complementHom_T]

/-- The involutive complement automorphism, sending `T i` to `-T i⁻¹`. -/
def complementEquiv : InfiniteTypeAHeckeAlgebra R q ≃ₐ[R] InfiniteTypeAHeckeAlgebra R q :=
  AlgEquiv.ofAlgHom (complementHom q) (complementHom q)
    (complementHom_comp_self q) (complementHom_comp_self q)

/-- The polynomial formula for the complement of a generator. -/
@[simp]
theorem complementEquiv_T (i : ℕ) :
    complementEquiv q (T q i) = algebraMap R _ ((q : R) - ↑q⁻¹) - T q i :=
  complementHom_T q i

/-- The complement of a generator is its negative inverse. -/
theorem complementEquiv_T_eq_neg_inv (i : ℕ) :
    complementEquiv q (T q i) = -(↑(unitT q i)⁻¹ : InfiniteTypeAHeckeAlgebra R q) := by
  simp

/-- The complement automorphism is its own inverse. -/
@[simp]
theorem complementEquiv_symm : (complementEquiv q).symm = complementEquiv q := by
  exact AlgEquiv.ofAlgHom_symm _ _ _ _

/-- Applying the complement twice is the identity. -/
@[simp]
theorem complementEquiv_complementEquiv (x : InfiniteTypeAHeckeAlgebra R q) :
    complementEquiv q (complementEquiv q x) = x := by
  simpa only [complementEquiv_symm] using (complementEquiv q).symm_apply_apply x

/-- Complementing preserves membership in each finite stage. -/
@[simp]
theorem complementEquiv_mem_stage_iff {n : ℕ} {x : InfiniteTypeAHeckeAlgebra R q} :
    complementEquiv q x ∈ stage R q n ↔ x ∈ stage R q n := by
  have h : ∀ x ∈ stage R q n, complementEquiv q x ∈ stage R q n := by
    have hle : stage R q n ≤ (stage R q n).comap (complementEquiv q).toAlgHom :=
      stage_le_iff.2 fun i hi ↦ by
        simpa using sub_mem ((stage R q n).algebraMap_mem ((q : R) - ↑q⁻¹))
          (T_mem_stage hi)
    exact fun x hx ↦ hle hx
  exact ⟨fun hx ↦ by simpa using h _ hx, h x⟩

/-- The complement symmetry restricted to the stage on `n` strands. -/
def stageComplementEquiv (n : ℕ) : stage R q n ≃ₐ[R] stage R q n where
  toFun x := ⟨complementEquiv q x, complementEquiv_mem_stage_iff q |>.2 x.2⟩
  invFun x := ⟨complementEquiv q x, complementEquiv_mem_stage_iff q |>.2 x.2⟩
  left_inv x := Subtype.ext (complementEquiv_complementEquiv q x)
  right_inv x := Subtype.ext (complementEquiv_complementEquiv q x)
  map_mul' x y := Subtype.ext (map_mul (complementEquiv q) (x : InfiniteTypeAHeckeAlgebra R q) y)
  map_add' x y := Subtype.ext (map_add (complementEquiv q) (x : InfiniteTypeAHeckeAlgebra R q) y)
  commutes' r := Subtype.ext ((complementEquiv q).commutes r)

/-- Restriction to a stage agrees with the ambient complement symmetry. -/
@[simp]
theorem coe_stageComplementEquiv (n : ℕ) (x : stage R q n) :
    (stageComplementEquiv q n x : InfiniteTypeAHeckeAlgebra R q) = complementEquiv q x := (rfl)

/-- The complement symmetry on a finite stage is its own inverse. -/
@[simp]
theorem stageComplementEquiv_symm (n : ℕ) :
    (stageComplementEquiv q n).symm = stageComplementEquiv q n := (rfl)

/-- Complementing commutes with every strand shift. -/
theorem complementEquiv_shift (k : ℕ) (x : InfiniteTypeAHeckeAlgebra R q) :
    complementEquiv q (shift R q k x) = shift R q k (complementEquiv q x) := by
  have h : (complementEquiv q).toAlgHom.comp (shift R q k) =
      (shift R q k).comp (complementEquiv q).toAlgHom := by
    ext i
    simp
  exact DFunLike.congr_fun h x

/-- In the `g i = q • T i` convention, complementing sends `g i` to `q² - 1 - g i`. -/
theorem complementEquiv_smul_T (i : ℕ) :
    complementEquiv q ((q : R) • T q i) =
      algebraMap R _ ((q : R) ^ 2 - 1) - (q : R) • T q i := by
  rw [map_smul, complementEquiv_T, smul_sub]
  simp [Algebra.smul_def, ← map_mul, mul_sub, pow_two]

/-- If `s = q + q⁻¹` is a unit, the normalized eigenprojection is sent to its complement.
The unit hypothesis excludes the repeated-root fibers. -/
theorem complementEquiv_eigenprojection (s : Rˣ) (hs : (s : R) = (q : R) + ↑q⁻¹) (i : ℕ) :
    complementEquiv q ((↑s⁻¹ : R) • (T q i + algebraMap R _ (↑q⁻¹ : R))) =
      1 - (↑s⁻¹ : R) • (T q i + algebraMap R _ (↑q⁻¹ : R)) := by
  have hsum : (↑s⁻¹ : R) * ((q : R) + ↑q⁻¹) = 1 := by rw [← hs]; simp
  have hscalar := congrArg (algebraMap R (InfiniteTypeAHeckeAlgebra R q)) hsum
  rw [map_smul, map_add, complementEquiv_T, AlgEquiv.commutes]
  simp only [map_mul, map_add, map_one] at hscalar
  simp only [Algebra.smul_def, map_sub]
  noncomm_ring [← hscalar]

/-- Complementing exchanges the index and sign characters. -/
@[simp]
theorem indexCharacter_complementEquiv (x : InfiniteTypeAHeckeAlgebra R q) :
    indexCharacter R q (complementEquiv q x) = signCharacter R q x := by
  have h : (indexCharacter R q).comp (complementEquiv q).toAlgHom = signCharacter R q := by
    ext i
    simp
  exact DFunLike.congr_fun h x

/-- Complementing exchanges the sign and index characters. -/
@[simp]
theorem signCharacter_complementEquiv (x : InfiniteTypeAHeckeAlgebra R q) :
    signCharacter R q (complementEquiv q x) = indexCharacter R q x := by
  rw [← indexCharacter_complementEquiv q, complementEquiv_complementEquiv]

variable {q} {z : R} {τ : InfiniteTypeAHeckeAlgebra R q →ₗ[R] R}

/-- Precomposing a Markov trace with the complement symmetry changes its parameter from `z`
to `q - q⁻¹ - z`. -/
theorem IsMarkovTrace.comp_complementEquiv (hτ : IsMarkovTrace z τ) :
    IsMarkovTrace ((q : R) - ↑q⁻¹ - z) (τ.comp (complementEquiv q).toLinearMap) where
  map_one := by simpa using hτ.map_one
  map_mul_comm x y := by simpa using hτ.map_mul_comm (complementEquiv q x) (complementEquiv q y)
  map_mul_T hx := by
    simp only [LinearMap.comp_apply, AlgEquiv.toLinearMap_apply, map_mul, complementEquiv_T,
      mul_sub, map_sub]
    rw [hτ.map_mul_T ((complementEquiv_mem_stage_iff q).2 hx)]
    simp [Algebra.algebraMap_eq_smul_one, sub_mul]

/-- The complement symmetry gives an equivalence between the two Markov-trace conditions. -/
@[simp]
theorem isMarkovTrace_comp_complementEquiv_iff :
    IsMarkovTrace ((q : R) - ↑q⁻¹ - z) (τ.comp (complementEquiv q).toLinearMap) ↔
      IsMarkovTrace z τ := by
  refine ⟨fun h ↦ ?_, IsMarkovTrace.comp_complementEquiv⟩
  have h' := h.comp_complementEquiv
  have hc : (τ.comp (complementEquiv q).toLinearMap).comp (complementEquiv q).toLinearMap = τ := by
    ext x
    simp
  simpa only [hc, sub_sub_cancel] using h'

end TauCeti.InfiniteTypeAHeckeAlgebra
