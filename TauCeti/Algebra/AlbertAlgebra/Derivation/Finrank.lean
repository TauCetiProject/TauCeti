/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlbertAlgebra.Derivation.Basic
public import TauCeti.Algebra.AlbertAlgebra.Jordan
public import TauCeti.Algebra.Jordan.Derivation
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.Tactic.LinearCombination

/-!
# The derivation algebra of the split Albert algebra has dimension `52`

The derivation algebra `Der J` of the split Albert algebra `J = H₃(𝕆)` is the split Lie algebra of
type `F₄`. This file proves that it has dimension `52` over every field in which `2` is invertible
(`TauCeti.AlbertAlgebra.finrank_derivationLieAlgebra`), the dimension of `F₄`. Identifying `Der J`
with the Serre-presented `LieAlgebra.f₄` needs, in addition, its simplicity and a split Cartan
subalgebra with its root system, which are not treated here.

## The argument

Write `E₀, E₁, E₂` for the diagonal idempotents of `J` and `Fⱼ(a)` for the Hermitian matrix with the
octonion `a` in the `j`-th off-diagonal slot. The count runs through the linear map
`D ↦ (D E₀, D E₁)` recording the values of a derivation on the diagonal frame.

* **Its range has dimension `24`.** A derivation sends `Eᵢ` into the two slots touching it
  (`TauCeti.AlbertAlgebra.derivation_apply_diagIdempotent_diag_eq_zero` and
  `TauCeti.AlbertAlgebra.derivation_apply_diagIdempotent_offDiag_self_eq_zero`), and kills
  `1 = E₀ + E₁ + E₂`, so `D E₀` and `D E₁` have opposite entries in their common slot. That leaves
  three free octonions. All of them occur: since `J` is a Jordan algebra, the commutators
  `⁅L_{Eᵢ}, L_{Fⱼ(x)}⁆` of multiplication operators are derivations
  (`TauCeti.lie_mulLeft_mulLeft_mem_derivationLieAlgebra`), and they realize every such pair.
* **Its kernel has dimension `28`**, the dimension of the orthogonal Lie algebra of the octonion
  norm. A derivation killing the frame commutes with the multiplications by the `Eᵢ`, so it
  preserves their joint Peirce spaces, the three slots, acting on them by linear maps `f₀, f₁, f₂`
  of `𝕆`. Each `fⱼ` is skew for the symmetric bilinear form `β` of the norm, and the products of
  adjacent slots give the relations of local triality,
  `f_{i+2} (conj (x y)) = conj (f_i x * y + x * f_{i+1} y)`.
  These force `f₀` to determine the derivation: if `f₀ = 0`, then `f₁` and `f₂` are multiplications
  by an octonion in the nucleus of `𝕆`, which is a scalar
  (`TauCeti.Octonion.exists_eq_smul_one_of_forall_mul_mul_eq`), and that scalar vanishes. Conversely
  the derivations `⁅L_{F₀(a)}, L_{F₀(b)}⁆` act on the slot `0` by the skew maps
  `c ↦ β(b, c) a - β(a, c) b`. In a basis `eₚ` of `𝕆` and the `β`-dual basis
  (`TauCeti.Octonion.nondegenerate_associated_normQuadraticForm`) the entries `β(f₀ eₚ, e_q)` with
  `p < q` are therefore coordinates on the kernel, identifying it with `R^28`.

## References

* R. D. Schafer, *An Introduction to Nonassociative Algebras*, Academic Press (1966), Chapter III
  for the principle of local triality and Chapter IV for the derivation algebra of the exceptional
  Jordan algebra.
* N. Jacobson, *Exceptional Lie Algebras*, Lecture Notes in Pure and Applied Mathematics 1,
  Marcel Dekker (1971).
-/

public section

namespace TauCeti

namespace AlbertAlgebra

variable {R : Type*}

/-- The symmetric bilinear form of the octonion norm. -/
local notation "β" => QuadraticMap.associated (Octonion.normQuadraticForm R)

section CommRing

variable [CommRing R] [Invertible (2 : R)]

variable (D : derivationLieAlgebra R (AlbertAlgebra R))

/-- A derivation kills the unit, so its values at the three diagonal idempotents sum to `0`. -/
private theorem sum_derivation_apply_diagIdempotent :
    (D : Module.End R (AlbertAlgebra R)) (diagIdempotent R 0) +
      (D : Module.End R (AlbertAlgebra R)) (diagIdempotent R 1) +
        (D : Module.End R (AlbertAlgebra R)) (diagIdempotent R 2) = 0 := by
  rw [← map_add, ← map_add, ← Fin.sum_univ_three, sum_diagIdempotent,
    derivationLieAlgebra.apply_one_eq_zero]

/-! ### The values on the diagonal frame -/

variable (R) in
/-- The values of a derivation at the first two diagonal idempotents. -/
private def frameMap :
    derivationLieAlgebra R (AlbertAlgebra R) →ₗ[R] AlbertAlgebra R × AlbertAlgebra R where
  toFun D := ((D : Module.End R (AlbertAlgebra R)) (diagIdempotent R 0),
    (D : Module.End R (AlbertAlgebra R)) (diagIdempotent R 1))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable (R) in
/-- The possible values of a derivation at `(E₀, E₁)`: `D E₀` lies in the slots `1` and `2`, `D E₁`
in the slots `2` and `0`, and their entries in the common slot `2` are opposite. -/
private def frameTarget :
    Octonion R × Octonion R × Octonion R →ₗ[R] AlbertAlgebra R × AlbertAlgebra R where
  toFun p := (offDiagSingle 1 p.1 + offDiagSingle 2 p.2.1,
    offDiagSingle 0 p.2.2 - offDiagSingle 2 p.2.1)
  map_add' p q := by
    refine Prod.ext ?_ ?_
    · simp only [Prod.fst_add, Prod.snd_add, offDiagSingle_add]
      abel
    · simp only [Prod.fst_add, Prod.snd_add, offDiagSingle_add]
      abel
  map_smul' r p := by
    ext <;> simp [offDiagSingle_smul, smul_sub]

omit [Invertible (2 : R)] in
private theorem frameTarget_injective : Function.Injective (frameTarget R) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  rintro ⟨a, b, c⟩ h
  have h1 := congrArg (fun P : AlbertAlgebra R × AlbertAlgebra R => P.1.offDiag 1) h
  have h2 := congrArg (fun P : AlbertAlgebra R × AlbertAlgebra R => P.1.offDiag 2) h
  have h0 := congrArg (fun P : AlbertAlgebra R × AlbertAlgebra R => P.2.offDiag 0) h
  simp [frameTarget] at h0 h1 h2
  simp [h0, h1, h2]

private theorem range_frameMap_le :
    LinearMap.range (frameMap R) ≤ LinearMap.range (frameTarget R) := by
  rintro _ ⟨D, rfl⟩
  have hsum := congrArg (fun X : AlbertAlgebra R => X.offDiag 2)
    (sum_derivation_apply_diagIdempotent D)
  simp only [add_offDiag, Pi.add_apply, derivation_apply_diagIdempotent_offDiag_self_eq_zero,
    add_zero, zero_offDiag, Pi.zero_apply] at hsum
  refine ⟨(((D : Module.End R (AlbertAlgebra R)) (diagIdempotent R 0)).offDiag 1,
    ((D : Module.End R (AlbertAlgebra R)) (diagIdempotent R 0)).offDiag 2,
    ((D : Module.End R (AlbertAlgebra R)) (diagIdempotent R 1)).offDiag 0), ?_⟩
  have hU := derivation_apply_diagIdempotent_diag_eq_zero D 0
  have hV := derivation_apply_diagIdempotent_diag_eq_zero D 1
  have hU0 := derivation_apply_diagIdempotent_offDiag_self_eq_zero D 0
  have hV1 := derivation_apply_diagIdempotent_offDiag_self_eq_zero D 1
  refine Prod.ext (AlbertAlgebra.ext ?_ (funext fun k => ?_))
    (AlbertAlgebra.ext ?_ (funext fun k => ?_))
  · simp [frameTarget, frameMap, hU]
  · fin_cases k <;> simp [frameTarget, frameMap, hU0]
  · simp [frameTarget, frameMap, hV]
  · fin_cases k <;> simp [frameTarget, frameMap, hV1, eq_neg_of_add_eq_zero_right hsum]

/-- The inner derivation of the idempotent `Eᵢ` and an entry `x` of the `j`-th slot, evaluated at
the idempotent `Eₘ`. -/
private theorem jordanInnerDerivation_diagIdempotent_offDiagSingle_apply (i j m : Fin 3)
    (x : Octonion R) :
    (jordanInnerDerivation R (diagIdempotent R i) (offDiagSingle j x) :
        Module.End R (AlbertAlgebra R)) (diagIdempotent R m) =
      (if m = j ∨ i = j then 0 else ⅟(2 : R) • ⅟(2 : R) • offDiagSingle j x) -
        if i = m ∧ i ≠ j then ⅟(2 : R) • offDiagSingle j x else 0 := by
  rw [jordanInnerDerivation_apply, mul_comm (offDiagSingle j x) (diagIdempotent R m),
    diagIdempotent_mul_offDiagSingle, diagIdempotent_mul_diagIdempotent]
  by_cases hmj : m = j <;> by_cases him : i = m <;> by_cases hij : i = j <;>
    simp_all [mul_smul_comm, mul_comm (offDiagSingle j x)]

private theorem range_frameTarget_le :
    LinearMap.range (frameTarget R) ≤ LinearMap.range (frameMap R) := by
  rintro _ ⟨⟨a, b, c⟩, rfl⟩
  have h2 : ⅟(2 : R) * 4 = 2 := by linear_combination (2 : R) * invOf_mul_self' (2 : R)
  refine ⟨jordanInnerDerivation R (diagIdempotent R 2) (offDiagSingle 1 ((4 : R) • a)) -
    jordanInnerDerivation R (diagIdempotent R 0) (offDiagSingle 2 ((4 : R) • b)) -
    jordanInnerDerivation R (diagIdempotent R 1) (offDiagSingle 0 ((4 : R) • c)), ?_⟩
  simp only [frameMap, frameTarget, LinearMap.coe_mk, AddHom.coe_mk, AddSubgroupClass.coe_sub,
    LinearMap.sub_apply, jordanInnerDerivation_diagIdempotent_offDiagSingle_apply]
  refine Prod.ext ?_ ?_
  · simp [offDiagSingle_smul, smul_smul, h2, two_smul]
  · simp [offDiagSingle_smul, smul_smul, h2, two_smul]
    abel

/-! ### Derivations killing the diagonal frame -/

variable {D}

/-- A derivation killing `E₀` and `E₁` kills every diagonal idempotent. -/
private theorem derivation_apply_diagIdempotent_eq_zero (hD : frameMap R D = 0) (i : Fin 3) :
    (D : Module.End R (AlbertAlgebra R)) (diagIdempotent R i) = 0 := by
  have h0 : (D : Module.End R (AlbertAlgebra R)) (diagIdempotent R 0) = 0 := congrArg Prod.fst hD
  have h1 : (D : Module.End R (AlbertAlgebra R)) (diagIdempotent R 1) = 0 := congrArg Prod.snd hD
  have h2 := sum_derivation_apply_diagIdempotent D
  rw [h0, h1, zero_add, zero_add] at h2
  fin_cases i <;> assumption

/-- **A derivation killing the diagonal frame preserves each slot**: it commutes with the
multiplications by the `Eᵢ`, so it preserves their joint Peirce spaces, which are the slots. -/
private theorem derivation_apply_offDiagSingle (hD : frameMap R D = 0) (j : Fin 3)
    (a : Octonion R) :
    (D : Module.End R (AlbertAlgebra R)) (offDiagSingle j a) =
      offDiagSingle j (((D : Module.End R (AlbertAlgebra R)) (offDiagSingle j a)).offDiag j) := by
  set X := (D : Module.End R (AlbertAlgebra R)) (offDiagSingle j a)
  have hX (i : Fin 3) : diagIdempotent R i * X = if i = j then 0 else ⅟(2 : R) • X := by
    have h := derivationLieAlgebra.leibniz D (diagIdempotent R i) (offDiagSingle j a)
    rw [derivation_apply_diagIdempotent_eq_zero hD, zero_mul, zero_add,
      diagIdempotent_mul_offDiagSingle] at h
    split_ifs at h ⊢ with hij
    · rw [← h, map_zero]
    · rw [← h, map_smul]
  refine AlbertAlgebra.ext (funext fun m => ?_) (funext fun k => ?_)
  · have h := congrArg (fun Y : AlbertAlgebra R => Y.diag m) (hX m)
    simp only [diagIdempotent_mul_diag_self] at h
    simp only [offDiagSingle_diag, Pi.zero_apply]
    split_ifs at h with hmj
    · exact h
    · rw [smul_diag, Pi.smul_apply, smul_eq_mul] at h
      linear_combination (2 : R) * h + X.diag m * invOf_mul_self' (2 : R)
  · rcases eq_or_ne k j with rfl | hkj
    · simp
    · have h : ⅟(2 : R) • X.offDiag k = 0 := by
        simpa [diagIdempotent_mul_offDiag_of_ne hkj] using
          congrArg (fun Y : AlbertAlgebra R => Y.offDiag k) (hX j)
      simp only [offDiagSingle_offDiag, Pi.single_eq_of_ne hkj]
      have h' := congrArg ((2 : R) • ·) h
      simpa [smul_smul] using h'

variable (D) in
/-- The action of a derivation on the `j`-th slot, read off in that slot. -/
private def slotMap (j : Fin 3) : Octonion R →ₗ[R] Octonion R where
  toFun a := ((D : Module.End R (AlbertAlgebra R)) (offDiagSingle j a)).offDiag j
  map_add' a b := by simp [offDiagSingle_add]
  map_smul' r a := by simp [offDiagSingle_smul]

private theorem slotMap_apply (j : Fin 3) (a : Octonion R) :
    slotMap D j a = ((D : Module.End R (AlbertAlgebra R)) (offDiagSingle j a)).offDiag j :=
  (rfl)

/-- **Local triality**: the slot actions of a derivation killing the frame are related through the
products of adjacent slots, `f_{i+2} (conj (x y)) = conj (f_i x * y + x * f_{i+1} y)`. -/
private theorem slotMap_conj_mul (hD : frameMap R D = 0) (i : Fin 3) (x y : Octonion R) :
    slotMap D (i + 2) (Octonion.conj (x * y)) =
      Octonion.conj (slotMap D i x * y + x * slotMap D (i + 1) y) := by
  have h := derivationLieAlgebra.leibniz D (offDiagSingle i x) (offDiagSingle (i + 1) y)
  rw [derivation_apply_offDiagSingle hD i x, derivation_apply_offDiagSingle hD (i + 1) y] at h
  simp only [offDiagSingle_mul_offDiagSingle_add_one, map_smul] at h
  rw [derivation_apply_offDiagSingle hD (i + 2)] at h
  have h' := congrArg (fun Y : AlbertAlgebra R => (2 : R) • Y.offDiag (i + 2)) h
  simpa [slotMap, smul_smul, map_add] using h'

/-- **The slot actions are skew** for the symmetric bilinear form of the octonion norm. -/
private theorem slotMap_skew (hD : frameMap R D = 0) (j : Fin 3) (a b : Octonion R) :
    β (slotMap D j a) b + β a (slotMap D j b) = 0 := by
  have h := derivationLieAlgebra.leibniz D (offDiagSingle j a) (offDiagSingle j b)
  rw [derivation_apply_offDiagSingle hD j a, derivation_apply_offDiagSingle hD j b] at h
  have h' := congrArg (fun Y : AlbertAlgebra R => Y.diag (j + 1)) h
  fin_cases j <;>
    simpa [slotMap, offDiagSingle_mul_offDiagSingle, derivation_apply_diagIdempotent_eq_zero hD,
      add_smul] using h'.symm

/-- **A derivation killing the frame is determined by its action on one slot**: if it kills the
slot `0`, then the local triality relations force its actions on the two other slots to be
multiplications by a common octonion in the nucleus, which is a scalar, and then that scalar is
`0`. -/
private theorem eq_zero_of_slotMap_zero (hD : frameMap R D = 0) (h0 : slotMap D 0 = 0) :
    D = 0 := by
  -- The relation through the slot `0`: `f₁ x * y + x * f₂ y = 0`.
  have r₀ (x y : Octonion R) : slotMap D 1 x * y + x * slotMap D 2 y = 0 := by
    have h := slotMap_conj_mul hD 1 x y
    simp only [Fin.reduceAdd, h0, LinearMap.zero_apply] at h
    simpa using congrArg Octonion.conj h.symm
  set c := slotMap D 1 1 with hc_def
  have hf₂ (y : Octonion R) : slotMap D 2 y = -(c * y) := by
    simpa [eq_neg_iff_add_eq_zero, add_comm] using r₀ 1 y
  have hf₁ (x : Octonion R) : slotMap D 1 x = x * c := by
    have h := r₀ x 1
    rw [mul_one, hf₂, mul_one, mul_neg, ← sub_eq_add_neg, sub_eq_zero] at h
    exact h
  obtain ⟨r, hr⟩ := Octonion.exists_eq_smul_one_of_forall_mul_mul_eq (c := c) fun x y => by
    have h := r₀ x y
    rwa [hf₁, hf₂, mul_neg, ← sub_eq_add_neg, sub_eq_zero] at h
  -- The relation through the slot `1` at `x = y = 1` gives `c = conj (f₂ 1) = -c`.
  have hc : r = 0 := by
    have h := slotMap_conj_mul hD 2 1 1
    simp only [Fin.isValue, Fin.reduceAdd, mul_one, Octonion.conj_one, ← hc_def, hr, hf₂, h0,
      LinearMap.zero_apply, mul_zero, add_zero, map_neg, map_smul] at h
    have ha : r = -r := by simpa using congrArg Octonion.a h
    have h2 : (2 : R) * r = 0 := by linear_combination ha
    simpa using congrArg (⅟(2 : R) * ·) h2
  have hslot (j : Fin 3) (a : Octonion R) :
      ((D : Module.End R (AlbertAlgebra R)) (offDiagSingle j a)).offDiag j = 0 := by
    rw [← slotMap_apply]
    fin_cases j
    · simp [h0]
    · simp [hf₁, hr, hc]
    · simp [hf₂, hr, hc]
  have hF (j : Fin 3) (a : Octonion R) :
      (D : Module.End R (AlbertAlgebra R)) (offDiagSingle j a) = 0 := by
    rw [derivation_apply_offDiagSingle hD, hslot, offDiagSingle_zero]
  refine derivationLieAlgebra.ext fun A => ?_
  rw [eq_sum_smul_diagIdempotent_add_sum_offDiagSingle A]
  simp [Fin.sum_univ_three, derivation_apply_diagIdempotent_eq_zero hD, hF]

/-- An inner derivation of two entries of the slot `0` kills the diagonal frame. -/
private theorem frameMap_jordanInnerDerivation_offDiagSingle_zero (a b : Octonion R) :
    frameMap R (jordanInnerDerivation R (offDiagSingle 0 a) (offDiagSingle 0 b)) = 0 := by
  refine Prod.ext ?_ ?_ <;>
    simp [frameMap, mul_comm (offDiagSingle 0 _) (diagIdempotent R _), mul_smul_comm,
      mul_comm (offDiagSingle 0 a) (offDiagSingle 0 b)]

/-- **The inner derivation of two entries of the slot `0` acts on that slot by a rank-two skew
map**: `⁅L_{F₀ a}, L_{F₀ b}⁆ (F₀ c) = β(b, c) F₀ a - β(a, c) F₀ b`. -/
private theorem jordanInnerDerivation_offDiagSingle_zero_apply (a b c : Octonion R) :
    (jordanInnerDerivation R (offDiagSingle 0 a) (offDiagSingle 0 b) :
        Module.End R (AlbertAlgebra R)) (offDiagSingle 0 c) =
      β b c • offDiagSingle 0 a - β a c • offDiagSingle 0 b := by
  simp only [jordanInnerDerivation_apply, offDiagSingle_mul_offDiagSingle, mul_smul_comm, mul_add,
    mul_comm (offDiagSingle 0 _) (diagIdempotent R _), diagIdempotent_mul_offDiagSingle]
  simp [← smul_add, ← two_smul R (offDiagSingle 0 _), smul_smul]

end CommRing

section Field

variable [Field R] [Invertible (2 : R)]

variable (R) in
/-- A basis of the split octonions, indexed by `Fin 8`. -/
private noncomputable def octonionBasis : Module.Basis (Fin 8) R (Octonion R) :=
  Module.finBasisOfFinrankEq R (Octonion R) (Octonion.finrank_eq_eight R)

variable (R) in
/-- The basis dual to `octonionBasis` for the symmetric bilinear form of the norm. -/
private noncomputable def octonionDualBasis : Module.Basis (Fin 8) R (Octonion R) :=
  LinearMap.BilinForm.dualBasis β Octonion.nondegenerate_associated_normQuadraticForm
    (octonionBasis R)

variable (R) in
/-- Coordinates on the derivations killing the frame: the entries `β(f₀ eₚ, e_q)`, `p < q`, of the
skew action `f₀` on the slot `0`. -/
private noncomputable def kernelCoord :
    LinearMap.ker (frameMap R) →ₗ[R] ({p : Fin 8 × Fin 8 // p.1 < p.2} → R) where
  toFun D p := β (slotMap D.1 0 (octonionBasis R p.1.1)) (octonionBasis R p.1.2)
  map_add' D E := by
    ext p
    simp [slotMap]
  map_smul' r D := by
    ext p
    simp [slotMap]

private theorem kernelCoord_apply (D : LinearMap.ker (frameMap R))
    (p : {p : Fin 8 × Fin 8 // p.1 < p.2}) :
    kernelCoord R D p = β (slotMap D.1 0 (octonionBasis R p.1.1)) (octonionBasis R p.1.2) :=
  (rfl)

private theorem kernelCoord_injective : Function.Injective (kernelCoord R) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro D hD
  have hframe : frameMap R D.1 = 0 := LinearMap.mem_ker.mp D.2
  set e := octonionBasis R
  have hsymm (x y : Octonion R) : β x y = β y x := QuadraticMap.associated_isSymm R _ x y
  have hpq (p q : Fin 8) : β (slotMap D.1 0 (e p)) (e q) = 0 := by
    rcases lt_trichotomy p q with hlt | rfl | hlt
    · exact congrFun hD ⟨(p, q), hlt⟩
    · have h := slotMap_skew hframe 0 (e p) (e p)
      rw [hsymm (e p), ← two_mul] at h
      simpa [← mul_assoc] using congrArg (⅟(2 : R) * ·) h
    · have h := slotMap_skew hframe 0 (e q) (e p)
      have hqp : β (slotMap D.1 0 (e q)) (e p) = 0 := congrFun hD ⟨(q, p), hlt⟩
      rwa [hqp, zero_add, hsymm] at h
  have hlin (p : Fin 8) : β (slotMap D.1 0 (e p)) = 0 := e.ext fun q => by simpa using hpq p q
  have hf : slotMap D.1 0 = 0 := e.ext fun p => by
    rw [LinearMap.zero_apply]
    exact Octonion.nondegenerate_associated_normQuadraticForm.1 _ fun y => by
      rw [hlin p, LinearMap.zero_apply]
  exact Subtype.ext (eq_zero_of_slotMap_zero hframe hf)

private theorem kernelCoord_surjective : Function.Surjective (kernelCoord R) := by
  rw [← LinearMap.range_eq_top, eq_top_iff, ← (Pi.basisFun R _).span_eq, Submodule.span_le]
  rintro _ ⟨⟨⟨s, t⟩, hst⟩, rfl⟩
  rw [SetLike.mem_coe, LinearMap.mem_range]
  -- The element is read off the lemma, so that its `offDiagSingle` carries the instances of the
  -- commutative-ring section rather than ones re-synthesized from `Field R`.
  refine ⟨⟨_, LinearMap.mem_ker.mpr (frameMap_jordanInnerDerivation_offDiagSingle_zero
    (octonionDualBasis R t) (octonionDualBasis R s))⟩, ?_⟩
  ext ⟨⟨p, q⟩, hpq⟩
  rw [kernelCoord_apply, slotMap_apply, jordanInnerDerivation_offDiagSingle_zero_apply]
  simp only [sub_offDiag, smul_offDiag, offDiagSingle_offDiag, Pi.sub_apply, Pi.smul_apply,
    Pi.single_eq_same, map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul,
    octonionDualBasis, LinearMap.BilinForm.apply_dualBasis_left, Pi.basisFun_apply,
    Pi.single_apply, Subtype.mk.injEq, Prod.mk.injEq]
  simp only at hpq hst
  -- The second product would need `p = t` and `q = s`, against `p < q` and `s < t`.
  have h₀ : ¬(p = t ∧ q = s) := fun ⟨hp, hq⟩ => lt_asymm hst (by rwa [hp, hq] at hpq)
  rw [ite_zero_mul_ite_zero, ite_zero_mul_ite_zero, ite_eq_right h₀, sub_zero, mul_one]

/-- **The derivation algebra of the split Albert algebra has dimension `52`**, over a field of
characteristic different from `2`: this is the dimension of the Lie algebra of type `F₄`. -/
theorem finrank_derivationLieAlgebra :
    Module.finrank R (derivationLieAlgebra R (AlbertAlgebra R)) = 52 := by
  have hrange : Module.finrank R (LinearMap.range (frameMap R)) = 24 := by
    rw [le_antisymm range_frameMap_le range_frameTarget_le,
      LinearMap.finrank_range_of_inj frameTarget_injective]
    simp [Octonion.finrank_eq_eight]
  have hker : Module.finrank R (LinearMap.ker (frameMap R)) = 28 := by
    rw [(LinearEquiv.ofBijective (kernelCoord R)
      ⟨kernelCoord_injective, kernelCoord_surjective⟩).finrank_eq,
      Module.finrank_fintype_fun_eq_card]
    decide
  rw [← LinearMap.finrank_range_add_finrank_ker (frameMap R), hrange, hker]

end Field

end AlbertAlgebra

end TauCeti
