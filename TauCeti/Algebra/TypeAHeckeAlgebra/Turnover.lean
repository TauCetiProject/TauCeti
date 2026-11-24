/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TypeAHeckeAlgebra.ReducedWord
public import TauCeti.Algebra.TypeAHeckeAlgebra.Star
public import TauCeti.GroupTheory.Perm.LongestElement

/-!
# The diagram-turnover automorphism and longest-element conjugation

Reversing the order of the `n` strands sends the crossing `i` between strands `i` and `i + 1` to
the crossing `i.rev = n - 2 - i`. Since the quadratic, braid and distant-commutation relations of
`TypeAHeckeAlgebra R q n` are preserved by `i ↦ i.rev`, this defines an involutive `R`-algebra
automorphism `TauCeti.TypeAHeckeAlgebra.strandRevEquiv q n` (diagram turnover). It exchanges the
prefix inclusion `strandIncl`, which adds an uncrossed last strand, with the shifted-tail inclusion
`tailIncl`, which adds an uncrossed first strand, and commutes with the real-parameter star
involution.

In any Coxeter system `cs` of type `A_(n-1)` possessing a longest element `w₀` whose conjugation
reverses the simple reflections (`w₀ * s i = s i.rev * w₀`), the basis element `Tw q cs w₀`
implements diagram turnover as an inner automorphism:

`Tw q cs w₀ * x = strandRevEquiv q n x * Tw q cs w₀`.

Because `Tw q cs w₀` is a unit, concrete specialization to `Fin.revPerm` in
`TauCeti.permCoxeterSystem n` shows that `strandRevEquiv q n` is an inner automorphism over every
commutative ring `R` and unit parameter `q`. Consequently it fixes every central element of
`TypeAHeckeAlgebra R q n` and leaves every tracial map invariant.

## Main definitions

* `TauCeti.TypeAHeckeAlgebra.strandRevEquiv`: the involutive algebra automorphism sending `T q i`
  to `T q i.rev`.

## Main results

* `TauCeti.TypeAHeckeAlgebra.strandRevEquiv_strandIncl` and
  `TauCeti.TypeAHeckeAlgebra.strandRevEquiv_tailIncl`: diagram turnover exchanges `strandIncl` and
  `tailIncl`.
* `TauCeti.TypeAHeckeAlgebra.strandRevEquiv_star`: diagram turnover commutes with the
  real-parameter involution.
* `TauCeti.TypeAHeckeAlgebra.Tw_longest_mul` and `TauCeti.TypeAHeckeAlgebra.Tw_revPerm_mul`:
  conjugation by the longest element implements `strandRevEquiv`.
* `TauCeti.TypeAHeckeAlgebra.strandRevEquiv_Tw` and
  `TauCeti.TypeAHeckeAlgebra.strandRevEquiv_Tw_permCoxeterSystem`: action on the standard basis
  `T_w`.
* `TauCeti.TypeAHeckeAlgebra.strandRevEquiv_eq_self_of_mem_center` and
  `TauCeti.TypeAHeckeAlgebra.apply_strandRevEquiv_of_mul_comm`: diagram turnover fixes the center
  and preserves every tracial map.

## References

* M. Geck and G. Pfeiffer, *Characters of Finite Coxeter Groups and Iwahori-Hecke Algebras*,
  OUP (2000), Section 4.4 and Chapter 7.
* C. Kassel and V. Turaev, *Braid Groups*, Springer GTM 247 (2008), Section 4.2.
-/

public section

namespace TauCeti.TypeAHeckeAlgebra

variable {R : Type*} [CommRing R]

section Automorphism

variable (q : Rˣ) (n : ℕ)

private def strandRevHom : TypeAHeckeAlgebra R q n →ₐ[R] TypeAHeckeAlgebra R q n :=
  lift (fun i ↦ T q i.rev)
    (fun i ↦ T_mul_self i.rev)
    (fun {i j} h ↦ T_braid (.inr <| by
      simp only [Fin.val_rev]
      omega))
    (fun {i j} h ↦ (commute_T (.inr <| by
      simp only [Fin.val_rev]
      omega)).eq)

private theorem strandRevHom_T (i : Fin (n - 1)) :
    strandRevHom q n (T q i) = T q i.rev :=
  lift_T ..

private theorem strandRevHom_comp_self :
    (strandRevHom q n).comp (strandRevHom q n) = AlgHom.id R _ :=
  hom_ext fun i ↦ by simp [strandRevHom_T]

/-- **Diagram turnover**: the involutive algebra automorphism of `TypeAHeckeAlgebra R q n`
reversing the order of the `n` strands, sending each generator `T q i` to `T q i.rev`. -/
def strandRevEquiv : TypeAHeckeAlgebra R q n ≃ₐ[R] TypeAHeckeAlgebra R q n :=
  AlgEquiv.ofAlgHom (strandRevHom q n) (strandRevHom q n)
    (strandRevHom_comp_self q n) (strandRevHom_comp_self q n)

variable {q n}

/-- Diagram turnover sends the generator `T q i` to `T q i.rev`. -/
@[simp]
theorem strandRevEquiv_T (i : Fin (n - 1)) :
    strandRevEquiv q n (T q i) = T q i.rev :=
  strandRevHom_T q n i

/-- Diagram turnover is its own inverse. -/
@[simp]
theorem strandRevEquiv_symm :
    (strandRevEquiv q n).symm = (strandRevEquiv q n : TypeAHeckeAlgebra R q n ≃ₐ[R] _) :=
  AlgEquiv.ofAlgHom_symm ..

/-- Applying diagram turnover twice is the identity. -/
@[simp]
theorem strandRevEquiv_strandRevEquiv (x : TypeAHeckeAlgebra R q n) :
    strandRevEquiv q n (strandRevEquiv q n x) = x := by
  simpa only [strandRevEquiv_symm] using (strandRevEquiv q n).symm_apply_apply x

/-- Diagram turnover is an involution. -/
theorem strandRevEquiv_involutive :
    Function.Involutive (strandRevEquiv q n : TypeAHeckeAlgebra R q n → _) :=
  strandRevEquiv_strandRevEquiv

/-- Diagram turnover sends the inverse of `T q i` to the inverse of `T q i.rev`. -/
theorem strandRevEquiv_val_inv_unitT (i : Fin (n - 1)) :
    strandRevEquiv q n (↑(unitT q i)⁻¹ : TypeAHeckeAlgebra R q n) = ↑(unitT q i.rev)⁻¹ := by
  simp [val_inv_unitT]

/-- Diagram turnover exchanges adding a last strand (`strandIncl`) with adding a first strand
(`tailIncl`). -/
@[simp]
theorem strandRevEquiv_strandIncl (x : TypeAHeckeAlgebra R q n) :
    strandRevEquiv q (n + 1) (strandIncl R q n x) = tailIncl q n (strandRevEquiv q n x) := by
  have h : (strandRevEquiv q (n + 1)).toAlgHom.comp (strandIncl R q n) =
      (tailIncl q n).comp (strandRevEquiv q n).toAlgHom :=
    hom_ext fun i ↦ by
      simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, strandIncl_T, strandRevEquiv_T,
        tailIncl_T]
      exact congrArg (T q) (Fin.ext <| by simp only [Fin.val_rev, Fin.val_castLE]; omega)
  exact AlgHom.congr_fun h x

/-- Diagram turnover sends the shifted-tail inclusion `tailIncl` to the prefix inclusion
`strandIncl`. -/
@[simp]
theorem strandRevEquiv_tailIncl (x : TypeAHeckeAlgebra R q n) :
    strandRevEquiv q (n + 1) (tailIncl q n x) = strandIncl R q n (strandRevEquiv q n x) := by
  apply (strandRevEquiv (R := R) q (n + 1)).injective
  rw [strandRevEquiv_strandRevEquiv, strandRevEquiv_strandIncl, strandRevEquiv_strandRevEquiv]

/-- Diagram turnover carries the prefix subalgebra onto the shifted-tail subalgebra. -/
theorem range_strandIncl_map_strandRevEquiv (q : Rˣ) (n : ℕ) :
    (strandIncl R q n).range.map (strandRevEquiv q (n + 1)).toAlgHom = (tailIncl q n).range := by
  ext y
  simp only [Subalgebra.mem_map, AlgHom.mem_range, AlgEquiv.coe_toAlgHom]
  refine ⟨?_, fun ⟨x, hx⟩ ↦ ⟨strandIncl R q n (strandRevEquiv q n x),
    ⟨_, rfl⟩, by rw [strandRevEquiv_strandIncl, strandRevEquiv_strandRevEquiv, hx]⟩⟩
  rintro ⟨_, ⟨x, rfl⟩, rfl⟩
  exact ⟨strandRevEquiv q n x, (strandRevEquiv_strandIncl x).symm⟩

/-- Diagram turnover commutes with the real-parameter star involution. -/
@[simp]
theorem strandRevEquiv_star [StarRing R] [Fact (IsSelfAdjoint (q : R))]
    (x : TypeAHeckeAlgebra R q n) :
    strandRevEquiv q n (star x) = star (strandRevEquiv q n x) := by
  have hx : x ∈ Algebra.adjoin R (Set.range (T (n := n) q)) := by
    rw [adjoin_range_T]
    trivial
  induction hx using Algebra.adjoin_induction with
  | mem y hy =>
    obtain ⟨i, rfl⟩ := hy
    simp
  | algebraMap r =>
    rw [Algebra.algebraMap_eq_smul_one, star_smul, star_one, map_smul, map_one, map_smul, map_one,
      star_smul, star_one]
  | add x y _ _ hx hy => simp [star_add, hx, hy]
  | mul x y _ _ hx hy => simp [star_mul, hx, hy]

end Automorphism

section LongestElement

variable {q : Rˣ} {n : ℕ} {W : Type*} [Group W]

/-- If `w₀` is a longest element of a type-`A` Coxeter system `cs` whose conjugation reverses the
simple reflections, then `Tw q cs w₀` intertwines `T q i` with `T q i.rev`. -/
theorem Tw_longest_mul_T (cs : CoxeterSystem (CoxeterMatrix.A (n - 1)) W) {w₀ : W}
    (hw₀ : cs.IsLongest w₀) (hconj : ∀ i, w₀ * cs.simple i = cs.simple i.rev * w₀)
    (i : Fin (n - 1)) :
    Tw q cs w₀ * T q i = (T q i.rev * Tw q cs w₀ : TypeAHeckeAlgebra R q n) := by
  have hr : ¬cs.IsRightDescent (w₀ * cs.simple i) i :=
    cs.isRightDescent_iff_not_isRightDescent_mul.mp (hw₀.isRightDescent i)
  have hl : ¬cs.IsLeftDescent (cs.simple i.rev * w₀) i.rev :=
    cs.isLeftDescent_iff_not_isLeftDescent_mul.mp (hw₀.isLeftDescent i.rev)
  have hR : Tw q cs (w₀ * cs.simple i) * T q i = (Tw q cs w₀ : TypeAHeckeAlgebra R q n) := by
    rw [Tw_mul_T_of_not_isRightDescent cs hr, cs.simple_mul_simple_cancel_right]
  have hL : T q i.rev * Tw q cs (w₀ * cs.simple i) = (Tw q cs w₀ : TypeAHeckeAlgebra R q n) := by
    rw [hconj i, T_mul_Tw_of_not_isLeftDescent cs hl, cs.simple_mul_simple_cancel_left]
  calc Tw q cs w₀ * T q i
      = Tw q cs (w₀ * cs.simple i) * (T q i * T q i) := by rw [← mul_assoc, hR]
    _ = ((q : R) - ↑q⁻¹) • Tw q cs w₀ + Tw q cs (w₀ * cs.simple i) := by
        rw [T_mul_self, mul_add, mul_smul_comm, mul_one, hR]
    _ = (T q i.rev * T q i.rev) * Tw q cs (w₀ * cs.simple i) := by
        rw [T_mul_self, add_mul, smul_mul_assoc, one_mul, hL]
    _ = T q i.rev * Tw q cs w₀ := by rw [mul_assoc, hL]

/-- **Longest-element conjugation implements diagram turnover.** In any type-`A` Coxeter system
with longest element `w₀` reversing the simple reflections, `Tw q cs w₀ * x = strandRevEquiv q n x *
Tw q cs w₀` for every `x`. -/
theorem Tw_longest_mul (cs : CoxeterSystem (CoxeterMatrix.A (n - 1)) W) {w₀ : W}
    (hw₀ : cs.IsLongest w₀) (hconj : ∀ i, w₀ * cs.simple i = cs.simple i.rev * w₀)
    (x : TypeAHeckeAlgebra R q n) :
    Tw q cs w₀ * x = strandRevEquiv q n x * Tw q cs w₀ := by
  have hx : x ∈ Algebra.adjoin R (Set.range (T (n := n) q)) := by
    rw [adjoin_range_T]
    trivial
  induction hx using Algebra.adjoin_induction with
  | mem y hy =>
    obtain ⟨i, rfl⟩ := hy
    simpa using Tw_longest_mul_T cs hw₀ hconj i
  | algebraMap r =>
    rw [Algebra.algebraMap_eq_smul_one, map_smul, map_one, mul_smul_comm, mul_one, smul_mul_assoc,
      one_mul]
  | add x y _ _ hx hy => rw [mul_add, hx, hy, map_add, add_mul]
  | mul x y _ _ hx hy => rw [← mul_assoc, hx, mul_assoc, hy, ← mul_assoc, map_mul]

/-- Diagram turnover acts on the standard basis `Tw` by longest-element conjugation of the indexing
Coxeter group element. -/
theorem strandRevEquiv_Tw (cs : CoxeterSystem (CoxeterMatrix.A (n - 1)) W) {w₀ : W}
    (hw₀ : cs.IsLongest w₀) (hconj : ∀ i, w₀ * cs.simple i = cs.simple i.rev * w₀) (w : W) :
    strandRevEquiv q n (Tw q cs w) = Tw q cs (w₀ * w * w₀) := by
  obtain ⟨ω, hω, rfl⟩ := cs.exists_isReduced w
  have hprod : ∀ l : List (Fin (n - 1)), cs.wordProd (l.map Fin.rev) = w₀ * cs.wordProd l * w₀ := by
    intro l
    induction l with
    | nil => simp [hw₀.mul_self]
    | cons i l ih =>
      rw [List.map_cons, cs.wordProd_cons, cs.wordProd_cons, ih,
        ← mul_assoc _ _ (w₀ : W), ← mul_assoc (cs.simple i.rev) w₀, ← hconj i]
      simp only [mul_assoc]
  have hlen : cs.length (w₀ * cs.wordProd ω * w₀) = cs.length (cs.wordProd ω) := by
    have h₁ := hw₀.length_mul_add_length (w₀ * cs.wordProd ω)
    have h₂ := hw₀.length_mul_left_add_length (cs.wordProd ω)
    omega
  have hred : cs.IsReduced (ω.map Fin.rev) := by
    rw [CoxeterSystem.IsReduced, hprod ω, hlen, List.length_map, hω.eq]
  rw [← hprod ω, Tw_wordProd cs hred, Tw_wordProd cs hω, map_list_prod, List.map_map, List.map_map]
  exact congrArg List.prod (List.map_congr_left fun i _ ↦ strandRevEquiv_T i)

/-- Diagram turnover fixes the basis element of the longest Coxeter element. -/
@[simp]
theorem strandRevEquiv_Tw_longest (cs : CoxeterSystem (CoxeterMatrix.A (n - 1)) W) {w₀ : W}
    (hw₀ : cs.IsLongest w₀) (hconj : ∀ i, w₀ * cs.simple i = cs.simple i.rev * w₀) :
    strandRevEquiv q n (Tw q cs w₀) = Tw q cs w₀ := by
  rw [strandRevEquiv_Tw cs hw₀ hconj, hw₀.mul_self, one_mul]

/-- In `TauCeti.permCoxeterSystem n`, the basis element of `Fin.revPerm` intertwines every element
with its diagram turnover. -/
theorem Tw_revPerm_mul (x : TypeAHeckeAlgebra R q n) :
    Tw q (permCoxeterSystem n) Fin.revPerm * x =
      strandRevEquiv q n x * Tw q (permCoxeterSystem n) Fin.revPerm :=
  Tw_longest_mul (permCoxeterSystem n) (isLongest_permCoxeterSystem_revPerm n)
    (fun i ↦ by simpa using BraidGroup.revPerm_mul_transposition i) x

/-- On the permutation basis `Tw` of `TauCeti.permCoxeterSystem n`, diagram turnover conjugates the
indexing permutation by `Fin.revPerm`. -/
theorem strandRevEquiv_Tw_permCoxeterSystem (σ : Equiv.Perm (Fin n)) :
    strandRevEquiv q n (Tw q (permCoxeterSystem n) σ) =
      Tw q (permCoxeterSystem n) (Fin.revPerm * σ * Fin.revPerm) :=
  strandRevEquiv_Tw (permCoxeterSystem n) (isLongest_permCoxeterSystem_revPerm n)
    (fun i ↦ by simpa using BraidGroup.revPerm_mul_transposition i) σ

/-- Diagram turnover fixes every central element of `TypeAHeckeAlgebra R q n`. -/
theorem strandRevEquiv_eq_self_of_mem_center {x : TypeAHeckeAlgebra R q n}
    (hx : x ∈ Subalgebra.center R (TypeAHeckeAlgebra R q n)) :
    strandRevEquiv q n x = x := by
  have hcomm : Tw q (permCoxeterSystem n) Fin.revPerm * x =
      x * Tw q (permCoxeterSystem n) Fin.revPerm :=
    Subalgebra.mem_center_iff.mp hx _
  exact (isUnit_Tw (R := R) (q := q) (permCoxeterSystem n) Fin.revPerm).mul_right_cancel
    ((Tw_revPerm_mul x).symm.trans hcomm)

/-- Every tracial map out of `TypeAHeckeAlgebra R q n` is invariant under diagram turnover. -/
theorem apply_strandRevEquiv_of_mul_comm {α : Type*} {f : TypeAHeckeAlgebra R q n → α}
    (hf : ∀ x y, f (x * y) = f (y * x)) (x : TypeAHeckeAlgebra R q n) :
    f (strandRevEquiv q n x) = f x := by
  let u := (isUnit_Tw (R := R) (q := q) (permCoxeterSystem n) Fin.revPerm).unit
  have hu : strandRevEquiv q n x = ↑u * x * ↑u⁻¹ := by
    calc strandRevEquiv q n x
        = strandRevEquiv q n x * ↑u * ↑u⁻¹ := by rw [mul_assoc, Units.mul_inv, mul_one]
      _ = ↑u * x * ↑u⁻¹ := by
          congr 1
          exact (Tw_revPerm_mul x).symm
  rw [hu, hf (↑u * x) ↑u⁻¹, ← mul_assoc, Units.inv_mul, one_mul]

end LongestElement

end TauCeti.TypeAHeckeAlgebra
