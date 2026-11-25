/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import TauCeti.Algebra.Quaternion.Map
import Mathlib.Algebra.Central.Matrix
import Mathlib.RingTheory.SimpleRing.Matrix
import TauCeti.Algebra.CentralSimple.SkolemNoether
import TauCeti.Algebra.Quaternion.CentralSimple
import TauCeti.Algebra.Quaternion.SpecialLinear
import TauCeti.NumberTheory.NumberField.InfinitePlace.Basic

/-!
# Real splittings of quaternion algebras

Arithmetic Fuchsian groups come from quaternion algebras `B = ℍ[k,a,b]` over a totally real field
`k` that split at exactly one real place of `k` and ramify at all the others. The image in
`PSL(2, ℝ)` of the reduced-norm-one elements of an order of `B` is then read through a fixed
homomorphism `B → M₂(ℝ)` over that place. This file packages these data as a `RealSplitting`:
a ring homomorphism `place : k → ℝ`, the nonvanishing of `a` and `b`, the negativity of `σ a`
and `σ b` at every other ring homomorphism `σ : k → ℝ`, and a ring homomorphism
`splitting : ℍ[k,a,b] → M₂(ℝ)` sending each scalar `x` to the scalar matrix `place x`.

The splitting extends `ℝ`-linearly along `place` to an isomorphism of real algebras
`ℍ[ℝ, place a, place b] ≃ M₂(ℝ)`, `RealSplitting.realAlgEquiv`: it is injective because the real
quaternion algebra is simple, and both sides have dimension four. Everything else here is read
off from it.

* The determinant of `splitting x` is the reduced norm of `x` read through `place`, so the
  splitting carries the reduced-norm-one group `unitary ℍ[k,a,b]` into `SL(2, ℝ)`.
* The commutant of the image of the splitting is the real scalars. By the Skolem–Noether theorem
  over `ℝ`, two real splittings with the same place differ by conjugation by an element of
  `GL(2, ℝ)`, and this element is unique up to a nonzero real scalar. The comparison is made over
  `ℝ` and not over `k`: when `k` is a number field, `M₂(ℝ)` is infinite-dimensional over `k`.
* `ℍ[k,a,b]` splits at `place`: `place a` and `place b` are not both negative, since otherwise
  `ℍ[ℝ, place a, place b]` would be a definite, hence division, algebra.
* `ℍ[k,a,b]` is a division algebra as soon as `k` has a real embedding other than `place`, where
  it ramifies; this happens for every totally real number field of degree at least two.
  Consequently a quaternion algebra over a totally real number field with a real splitting is
  isomorphic to `M₂(k)` only when `k` has degree one over `ℚ`.

## Main definitions

* `TauCeti.RealSplitting k a b`: a splitting of `ℍ[k,a,b]` at exactly one real place.
* `TauCeti.RealSplitting.realAlgEquiv`: the induced isomorphism `ℍ[ℝ, place a, place b] ≃ M₂(ℝ)`.
* `TauCeti.RealSplitting.unitaryToSpecialLinear`: the splitting on reduced-norm-one elements, with
  values in `SL(2, ℝ)`.

## Main results

* `TauCeti.RealSplitting.det_splitting`: the determinant of the splitting is the reduced norm read
  through `place`.
* `TauCeti.RealSplitting.centralizer_range_splitting`: the matrices commuting with the image of the
  splitting are the real scalars.
* `TauCeti.RealSplitting.exists_conj_eq_of_place_eq` and
  `TauCeti.RealSplitting.conj_splitting_eq_iff`: real splittings with the same place are conjugate
  by an element of `GL(2, ℝ)`, unique up to `ℝ^×`.
* `TauCeti.RealSplitting.place_a_pos_or_place_b_pos`: the algebra splits at `place`.
* `TauCeti.RealSplitting.anisotropic_normForm_of_ne` and
  `TauCeti.RealSplitting.anisotropic_normForm_of_one_lt_finrank`: the algebra is a division
  algebra when `k` has another real embedding, in particular over a totally real number field of
  degree at least two.
* `TauCeti.RealSplitting.finrank_eq_one_of_algEquiv_matrix`: over a totally real number field, a
  quaternion algebra with a real splitting is split only when the field has degree one.

## References

* J. Voight, *Quaternion Algebras*, Graduate Texts in Mathematics 288, Springer, 2021: §7.7 for
  the Skolem–Noether theorem, and Chapter 38 for quaternion algebras over a totally real field
  split at exactly one real place and their arithmetic Fuchsian groups.
-/

public noncomputable section

open Matrix
open scoped Quaternion MatrixGroups

namespace TauCeti

/-- A **real splitting** of the quaternion algebra `ℍ[k,a,b]` at exactly one real place: a ring
homomorphism `place : k → ℝ`, the nonvanishing of `a` and `b`, the negativity of `a` and `b` at
every other ring homomorphism `k → ℝ`, and a ring homomorphism `ℍ[k,a,b] → M₂(ℝ)` sending each
scalar `x` to the scalar matrix `place x`. The splitting extends along `place` to an isomorphism
`ℍ[ℝ, place a, place b] ≃ M₂(ℝ)` (`RealSplitting.realAlgEquiv`), so the algebra splits at `place`,
while it ramifies at every other real place. -/
structure RealSplitting (k : Type*) [Field k] (a b : k) where
  /-- The distinguished real place, given by a ring homomorphism `k → ℝ`. -/
  place : k →+* ℝ
  /-- The first structure constant is nonzero. -/
  a_ne_zero : a ≠ 0
  /-- The second structure constant is nonzero. -/
  b_ne_zero : b ≠ 0
  /-- At every other ring homomorphism `k → ℝ` both structure constants are negative, so the
  algebra is ramified there. -/
  ramified : ∀ σ : k →+* ℝ, σ ≠ place → σ a < 0 ∧ σ b < 0
  /-- The splitting homomorphism. -/
  splitting : ℍ[k,a,b] →+* Matrix (Fin 2) (Fin 2) ℝ
  /-- The splitting sends each scalar `x` to the scalar matrix `place x`. -/
  splitting_coe (x : k) :
    splitting (x : ℍ[k,a,b]) = algebraMap ℝ (Matrix (Fin 2) (Fin 2) ℝ) (place x)

namespace RealSplitting

variable {k : Type*} [Field k] {a b : k}

attribute [simp] splitting_coe

/-- A real splitting is determined by its splitting homomorphism, which determines the place
through the images of the scalars. -/
@[ext]
theorem ext {S T : RealSplitting k a b} (h : S.splitting = T.splitting) : S = T := by
  have hplace : S.place = T.place := by
    ext x
    apply (algebraMap ℝ (Matrix (Fin 2) (Fin 2) ℝ)).injective
    rw [← S.splitting_coe, ← T.splitting_coe, h]
  cases S
  cases T
  simp only [mk.injEq] at hplace h ⊢
  exact ⟨hplace, h⟩

variable (S : RealSplitting k a b)

private theorem place_a_ne_zero : S.place a ≠ 0 := (map_ne_zero _).mpr S.a_ne_zero

private theorem place_b_ne_zero : S.place b ≠ 0 := (map_ne_zero _).mpr S.b_ne_zero

/-- The real quaternion algebra at the place of a real splitting is simple. -/
private theorem isSimpleRing : IsSimpleRing ℍ[ℝ,S.place a,S.place b] :=
  QuaternionAlgebra.instIsSimpleRing (Units.mk0 _ S.place_a_ne_zero) (Units.mk0 _ S.place_b_ne_zero)

/-- The real quaternion algebra at the place of a real splitting is central. -/
private theorem isCentral : Algebra.IsCentral ℝ ℍ[ℝ,S.place a,S.place b] :=
  QuaternionAlgebra.instIsCentral (S.place a) (Units.mk0 _ S.place_b_ne_zero)

/-- The images of `i`, `j` and `k` under the splitting, as a quaternion basis of `M₂(ℝ)` for the
real structure constants `place a` and `place b`. -/
private def realBasis :
    _root_.QuaternionAlgebra.Basis (Matrix (Fin 2) (Fin 2) ℝ) (S.place a) 0 (S.place b) where
  i := S.splitting ⟨0, 1, 0, 0⟩
  j := S.splitting ⟨0, 0, 1, 0⟩
  k := S.splitting ⟨0, 0, 0, 1⟩
  i_mul_i := by
    rw [← map_mul, zero_smul, add_zero, ← Algebra.algebraMap_eq_smul_one,
      ← S.splitting_coe]
    congr 1
    ext <;> simp
  j_mul_j := by
    rw [← map_mul, ← Algebra.algebraMap_eq_smul_one, ← S.splitting_coe]
    congr 1
    ext <;> simp
  i_mul_j := by
    rw [← map_mul]
    congr 1
    ext <;> simp
  j_mul_i := by
    rw [zero_smul, zero_sub, ← map_mul, ← map_neg]
    congr 1
    ext <;> simp

/-- The splitting is the real-linear extension of its values on `1, i, j, k`, applied to the
coefficients read through `place`. -/
private theorem lift_realBasis_map (x : ℍ[k,a,b]) :
    _root_.QuaternionAlgebra.lift S.realBasis
      (QuaternionAlgebra.map a 0 b S.place rfl (map_zero _) rfl x) = S.splitting x := by
  have hx : x = (x.re : ℍ[k,a,b]) + (x.imI : ℍ[k,a,b]) * ⟨0, 1, 0, 0⟩ +
      (x.imJ : ℍ[k,a,b]) * ⟨0, 0, 1, 0⟩ + (x.imK : ℍ[k,a,b]) * ⟨0, 0, 0, 1⟩ := by
    ext <;> simp
  conv_rhs => rw [hx]
  simp only [map_add, map_mul, S.splitting_coe, _root_.QuaternionAlgebra.lift_apply,
    _root_.QuaternionAlgebra.Basis.liftHom_apply, _root_.QuaternionAlgebra.Basis.lift,
    QuaternionAlgebra.re_map, QuaternionAlgebra.imI_map, QuaternionAlgebra.imJ_map,
    QuaternionAlgebra.imK_map, Algebra.smul_def, realBasis]

private theorem bijective_lift_realBasis :
    Function.Bijective (_root_.QuaternionAlgebra.lift S.realBasis) := by
  have := S.isSimpleRing
  have hinj : Function.Injective (_root_.QuaternionAlgebra.lift S.realBasis) :=
    (_root_.QuaternionAlgebra.lift S.realBasis).toRingHom.injective
  refine ⟨hinj, ?_⟩
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (f := (_root_.QuaternionAlgebra.lift S.realBasis).toLinearMap)
    (by simp [_root_.QuaternionAlgebra.finrank_eq_four, Module.finrank_matrix])).mp hinj

/-- The isomorphism of real algebras `ℍ[ℝ, place a, place b] ≃ M₂(ℝ)` induced by a real splitting:
the real-linear extension of the splitting along `place`. -/
def realAlgEquiv : ℍ[ℝ,S.place a,S.place b] ≃ₐ[ℝ] Matrix (Fin 2) (Fin 2) ℝ :=
  AlgEquiv.ofBijective (_root_.QuaternionAlgebra.lift S.realBasis) S.bijective_lift_realBasis

/-- The induced real isomorphism is the real-linear extension of the values of the splitting on
`i`, `j` and `k`. -/
theorem realAlgEquiv_apply (y : ℍ[ℝ,S.place a,S.place b]) :
    S.realAlgEquiv y = algebraMap ℝ (Matrix (Fin 2) (Fin 2) ℝ) y.re +
      y.imI • S.splitting ⟨0, 1, 0, 0⟩ + y.imJ • S.splitting ⟨0, 0, 1, 0⟩ +
        y.imK • S.splitting ⟨0, 0, 0, 1⟩ := by
  simp [realAlgEquiv, AlgEquiv.ofBijective_apply, _root_.QuaternionAlgebra.lift_apply,
    _root_.QuaternionAlgebra.Basis.liftHom_apply, _root_.QuaternionAlgebra.Basis.lift, realBasis]

/-- The induced real isomorphism extends the splitting: on the coefficientwise image of a
quaternion of `ℍ[k,a,b]` under `place`, it is the splitting. -/
@[simp]
theorem realAlgEquiv_map (x : ℍ[k,a,b]) :
    S.realAlgEquiv (QuaternionAlgebra.map a 0 b S.place rfl (map_zero _) rfl x) =
      S.splitting x :=
  S.lift_realBasis_map x

/-- The splitting homomorphism of a real splitting is injective. -/
theorem splitting_injective : Function.Injective S.splitting := by
  intro x y h
  rw [← S.realAlgEquiv_map, ← S.realAlgEquiv_map] at h
  simpa [_root_.QuaternionAlgebra.ext_iff, S.place.injective.eq_iff] using
    S.realAlgEquiv.injective h

/-- The determinant of the splitting is the reduced norm read through the place. -/
@[simp]
theorem det_splitting (x : ℍ[k,a,b]) :
    (S.splitting x).det = S.place (_root_.QuaternionAlgebra.normForm a 0 b x) := by
  rw [← S.realAlgEquiv_map, _root_.QuaternionAlgebra.det_apply_eq_normForm_of_algEquiv_matrix,
    QuaternionAlgebra.normForm_map]

/-- The splitting on the reduced-norm-one group `unitary ℍ[k,a,b]`, which it carries into
`SL(2, ℝ)` because its determinant is the reduced norm read through the place. -/
def unitaryToSpecialLinear : unitary ℍ[k,a,b] →* SL(2, ℝ) where
  toFun x := ⟨S.splitting x, by
    rw [det_splitting,
      (_root_.QuaternionAlgebra.mem_unitary_iff_normForm_eq_one _ _ _ _).mp x.property, map_one]⟩
  map_one' := Subtype.ext (map_one S.splitting)
  map_mul' x y := Subtype.ext (map_mul S.splitting (x : ℍ[k,a,b]) y)

@[simp]
theorem coe_unitaryToSpecialLinear_apply (x : unitary ℍ[k,a,b]) :
    (S.unitaryToSpecialLinear x : Matrix (Fin 2) (Fin 2) ℝ) = S.splitting x :=
  (rfl)

theorem unitaryToSpecialLinear_injective : Function.Injective S.unitaryToSpecialLinear :=
  fun _ _ h ↦ Subtype.ext (S.splitting_injective (congrArg Subtype.val h))

/-- **The commutant of a real splitting.** The matrices commuting with every matrix in the image of
the splitting are exactly the real scalar matrices: the image spans `M₂(ℝ)` over `ℝ`. -/
theorem centralizer_range_splitting :
    Set.centralizer (Set.range S.splitting) =
      Set.range (algebraMap ℝ (Matrix (Fin 2) (Fin 2) ℝ)) := by
  ext m
  simp only [Set.mem_centralizer_iff, Set.forall_mem_range]
  constructor
  · intro hm
    have hcenter : m ∈ Subalgebra.center ℝ (Matrix (Fin 2) (Fin 2) ℝ) := by
      rw [Subalgebra.mem_center_iff]
      intro n
      obtain ⟨y, rfl⟩ := S.realAlgEquiv.surjective n
      rw [realAlgEquiv_apply]
      simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, hm, Algebra.commutes]
    rw [Algebra.IsCentral.center_eq_bot, Algebra.mem_bot] at hcenter
    exact hcenter
  · rintro ⟨c, rfl⟩ x
    exact (Algebra.commutes c _).symm

/-- **Real splittings with the same place are conjugate** by an element of `GL(2, ℝ)`. This is the
Skolem–Noether theorem over `ℝ`, applied to the induced isomorphisms
`ℍ[ℝ, place a, place b] ≃ M₂(ℝ)`. -/
theorem exists_conj_eq_of_place_eq (S T : RealSplitting k a b) (h : S.place = T.place) :
    ∃ u : GL (Fin 2) ℝ, ∀ x,
      T.splitting x =
        (u : Matrix (Fin 2) (Fin 2) ℝ) * S.splitting x *
          ((u⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) := by
  obtain ⟨τ, ha, hb, hram, ψ, hψ⟩ := T
  dsimp only at h ⊢
  subst h
  let T : RealSplitting k a b := ⟨S.place, ha, hb, hram, ψ, hψ⟩
  have := S.isSimpleRing
  have := S.isCentral
  obtain ⟨u, hu⟩ := skolemNoether ℝ S.realAlgEquiv.toAlgHom T.realAlgEquiv.toAlgHom
  refine ⟨u, fun x ↦ ?_⟩
  simpa [T] using hu (QuaternionAlgebra.map a 0 b S.place rfl (map_zero _) rfl x)

/-- **The conjugating matrix is unique up to a real scalar.** Two elements of `GL(2, ℝ)` conjugate
a real splitting in the same way exactly when they differ by a nonzero real scalar. -/
theorem conj_splitting_eq_iff {u v : GL (Fin 2) ℝ} :
    (∀ x, (u : Matrix (Fin 2) (Fin 2) ℝ) * S.splitting x *
        ((u⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
          v * S.splitting x * ((v⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)) ↔
      ∃ c : ℝˣ, (v : Matrix (Fin 2) (Fin 2) ℝ) = (c : ℝ) • (u : Matrix (Fin 2) (Fin 2) ℝ) := by
  constructor
  · intro h
    have hw : ((u⁻¹ * v : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) ∈
        Set.centralizer (Set.range S.splitting) := by
      rw [Set.mem_centralizer_iff, Set.forall_mem_range]
      intro x
      have := congrArg (fun m ↦ ((u⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) * m * v) (h x)
      simpa [mul_assoc] using this
    rw [centralizer_range_splitting] at hw
    obtain ⟨c, hc⟩ := hw
    have hc0 : c ≠ 0 := by
      rintro rfl
      exact (u⁻¹ * v).ne_zero (by simpa using hc.symm)
    refine ⟨Units.mk0 c hc0, ?_⟩
    rw [Units.val_mk0, Algebra.smul_def, Algebra.commutes, hc]
    simp
  · rintro ⟨c, hc⟩ x
    have hinv : ((v⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
        ((c⁻¹ : ℝˣ) : ℝ) • ((u⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) :=
      Units.inv_eq_of_mul_eq_one_right (by
        rw [hc, smul_mul_smul_comm, Units.mul_inv, Units.mul_inv, one_smul])
    rw [hinv, hc]
    simp [smul_smul]

/-- **A quaternion algebra with a real splitting splits at the distinguished place**: the real
structure constants `place a` and `place b` are not both negative. Otherwise the norm form of
`ℍ[ℝ, place a, place b]` would be positive definite, which is impossible for an algebra isomorphic
to `M₂(ℝ)`. -/
theorem place_a_pos_or_place_b_pos : 0 < S.place a ∨ 0 < S.place b := by
  by_contra! h
  have hdef := (_root_.QuaternionAlgebra.posDef_normForm_of_neg
    (h.1.lt_of_ne S.place_a_ne_zero) (h.2.lt_of_ne S.place_b_ne_zero)).anisotropic
  exact (QuaternionAlgebra.nonempty_algEquiv_matrix_iff_not_anisotropic_normForm
    (Units.mk0 _ S.place_a_ne_zero) (Units.mk0 _ S.place_b_ne_zero)).mp ⟨S.realAlgEquiv⟩ hdef

/-- **A quaternion algebra with a real splitting is a division algebra when `k` has another real
embedding**: if `σ` is a real embedding of `k` other than the place, then the ramification at `σ`
required by the structure makes the norm form of `ℍ[k,a,b]` anisotropic, so that `ℍ[k,a,b]` is a
division algebra. -/
theorem anisotropic_normForm_of_ne {σ : k →+* ℝ} (hσ : σ ≠ S.place) :
    (_root_.QuaternionAlgebra.normForm a 0 b).Anisotropic := by
  obtain ⟨ha, hb⟩ := S.ramified σ hσ
  intro x hx
  have h0 := (_root_.QuaternionAlgebra.posDef_normForm_of_neg ha hb).anisotropic
    (QuaternionAlgebra.map a 0 b σ rfl (map_zero σ) rfl x)
    (by rw [QuaternionAlgebra.normForm_map, hx, map_zero])
  simpa [_root_.QuaternionAlgebra.ext_iff] using h0

include S in
/-- Over a totally real number field of degree at least two, a quaternion algebra with a real
splitting is a division algebra: it ramifies at the real places other than the distinguished
one. -/
theorem anisotropic_normForm_of_one_lt_finrank [NumberField k] [NumberField.IsTotallyReal k]
    (hk : 1 < Module.finrank ℚ k) : (_root_.QuaternionAlgebra.normForm a 0 b).Anisotropic := by
  have := NumberField.IsTotallyReal.nontrivial_ringHom_real hk
  obtain ⟨σ, hσ⟩ := exists_ne S.place
  exact S.anisotropic_normForm_of_ne hσ

include S in
/-- Over a totally real number field, a quaternion algebra with a real splitting is isomorphic to
`M₂(k)` only when `k` has degree one over `ℚ`. -/
theorem finrank_eq_one_of_algEquiv_matrix [NumberField k] [NumberField.IsTotallyReal k]
    (e : ℍ[k,a,b] ≃ₐ[k] Matrix (Fin 2) (Fin 2) k) : Module.finrank ℚ k = 1 := by
  have : Invertible (2 : k) := invertibleOfNonzero two_ne_zero
  by_contra hk
  have hk : 1 < Module.finrank ℚ k := lt_of_le_of_ne Module.finrank_pos (Ne.symm hk)
  exact (QuaternionAlgebra.nonempty_algEquiv_matrix_iff_not_anisotropic_normForm
    (Units.mk0 _ S.a_ne_zero) (Units.mk0 _ S.b_ne_zero)).mp ⟨e⟩
      (S.anisotropic_normForm_of_one_lt_finrank hk)

end RealSplitting

end TauCeti
