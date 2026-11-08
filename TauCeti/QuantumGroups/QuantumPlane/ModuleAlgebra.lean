/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.QuantumGroups.QuantumInteger.Basic
public import TauCeti.QuantumGroups.QuantumPlane.Basic
public import TauCeti.QuantumGroups.UqSl2.TensorProduct
import Mathlib.LinearAlgebra.Basis.Bilinear
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# The quantum plane as a `U_q(sl₂)`-module algebra

For a nonzero complex parameter `q`, the rank-one quantum group `UqSl2 q` acts on the complex
quantum plane `ℂ⟨x, y⟩ / (x y - q y x)`, with `x` of weight `q` and `y` of weight `q⁻¹`, by

* `K (y^j x^k) = q^(k - j) y^j x^k` and `K⁻¹ (y^j x^k) = q^(j - k) y^j x^k`,
* `E (y^j x^k) = [j]_q y^(j - 1) x^(k + 1)`, and
* `F (y^j x^k) = [k]_q y^(j + 1) x^(k - 1)`,

where `[r]_q` is the symmetric quantum integer, so that `E` vanishes on `x^k` and `F` on `y^j`.
On the generators, always `E x = F y = 0`, `K x = q x`, `K y = q⁻¹ y`, `K⁻¹ x = q⁻¹ x` and
`K⁻¹ y = q y`; when `q - q⁻¹ ≠ 0` (so that `[1]_q = 1`), also `E y = x` and `F x = y`. At
`q = ±1` instead `[1]_q = 0`, so `E y = F x = 0`.

This action makes the quantum plane a module algebra for the Hopf structure
`ΔE = E ⊗ 1 + K ⊗ E`, `ΔF = F ⊗ K⁻¹ + 1 ⊗ F`, `ΔK = K ⊗ K` of `TauCeti.UqSl2.Hopf`: the
generators act by the twisted Leibniz rules

* `E (a b) = E(a) b + K(a) E(b)`,
* `F (a b) = F(a) K⁻¹(b) + a F(b)`, and
* `K (a b) = K(a) K(b)`,

and every element `u` acts on the unit through the counit. Equivalently, multiplication is a
`UqSl2 q`-module map from the coproduct tensor product of the quantum plane with itself
(`TauCeti.QuantumPlane.mulHom`). The twisted Leibniz rules pin down the factor order of the
coproduct: for `q² ≠ 1`, the opposite rule `E (a b) = E(a) K(b) + a E(b)` would send the relation
`x y - q y x` to `(1 - q²) x² ≠ 0`.

## Main definitions

* `TauCeti.QuantumPlane.rep`: the action of `UqSl2 q` as an algebra map to endomorphisms.
* `TauCeti.QuantumPlane.mulHom`: multiplication as a module map from the tensor product.

## Main results

* `TauCeti.QuantumPlane.e_smul_basis`, `f_smul_basis`, `k_smul_basis`, `kInv_smul_basis`: the
  action on the monomial basis.
* `TauCeti.QuantumPlane.e_smul_mul`, `f_smul_mul`, `k_smul_mul`, `kInv_smul_mul`: the twisted
  Leibniz rules.
* `TauCeti.QuantumPlane.smul_one_eq_counit_smul`: the unit is acted on through the counit.

## References

* C. Kassel, *Quantum Groups*, Graduate Texts in Mathematics 155, Chapter VII, Section 3, for
  the module-algebra structure of the quantum plane, here transported to the coproduct
  `ΔE = E ⊗ 1 + K ⊗ E` of A. Virelizier, *Quantum groups*, Sections 2.3--2.4.
-/

public section

noncomputable section

namespace TauCeti.QuantumPlane

open UqSl2 BialgebraModule

variable {q : ℂ}

/-! ### The generator operators -/

/-- The operator of `K`, scaling `y^j x^k` by `q^(k - j)`. -/
private def kOp (q : ℂ) : Module.End ℂ (QuantumPlane q) :=
  (basis q).constr ℂ fun i => q ^ ((i.2 : ℤ) - i.1) • basis q i

/-- The operator of `K⁻¹`, scaling `y^j x^k` by `q^(j - k)`. -/
private def kInvOp (q : ℂ) : Module.End ℂ (QuantumPlane q) :=
  (basis q).constr ℂ fun i => q ^ ((i.1 : ℤ) - i.2) • basis q i

/-- The operator of `E`, sending `y^j x^k` to `[j]_q y^(j - 1) x^(k + 1)`. -/
private def eOp (q : ℂ) : Module.End ℂ (QuantumPlane q) :=
  (basis q).constr ℂ fun i => quantumInteger q i.1 • basis q (i.1 - 1, i.2 + 1)

/-- The operator of `F`, sending `y^j x^k` to `[k]_q y^(j + 1) x^(k - 1)`. -/
private def fOp (q : ℂ) : Module.End ℂ (QuantumPlane q) :=
  (basis q).constr ℂ fun i => quantumInteger q i.2 • basis q (i.1 + 1, i.2 - 1)

private theorem kOp_basis (j k : ℕ) :
    kOp q (basis q (j, k)) = q ^ ((k : ℤ) - j) • basis q (j, k) :=
  (basis q).constr_basis ℂ _ (j, k)

private theorem kInvOp_basis (j k : ℕ) :
    kInvOp q (basis q (j, k)) = q ^ ((j : ℤ) - k) • basis q (j, k) :=
  (basis q).constr_basis ℂ _ (j, k)

private theorem eOp_basis (j k : ℕ) :
    eOp q (basis q (j, k)) = quantumInteger q j • basis q (j - 1, k + 1) :=
  (basis q).constr_basis ℂ _ (j, k)

private theorem fOp_basis (j k : ℕ) :
    fOp q (basis q (j, k)) = quantumInteger q k • basis q (j + 1, k - 1) :=
  (basis q).constr_basis ℂ _ (j, k)

/-- Moving one degree from `y` to `x` multiplies the `K`-weight `q^(k - j)` by `q²`. -/
private theorem zpow_succ_sub (hq : q ≠ 0) (j k : ℕ) :
    q ^ (((k + 1 : ℕ) : ℤ) - j) = q ^ 2 * q ^ ((k : ℤ) - (j + 1 : ℕ)) := by
  rw [← zpow_natCast q 2, ← zpow_add₀ hq]
  congr 1
  push_cast
  ring

private theorem eOp_fOp_basis (j k : ℕ) :
    eOp q (fOp q (basis q (j, k))) =
      (quantumInteger q k * quantumInteger q (j + 1)) • basis q (j, k) := by
  rcases k with _ | k
  · simp [fOp_basis]
  simp [fOp_basis, eOp_basis, smul_smul]

private theorem fOp_eOp_basis (j k : ℕ) :
    fOp q (eOp q (basis q (j, k))) =
      (quantumInteger q j * quantumInteger q (k + 1)) • basis q (j, k) := by
  rcases j with _ | j
  · simp [eOp_basis]
  simp [fOp_basis, eOp_basis, smul_smul]

/-- Multiples of basis monomials agree when their coefficients and their indices agree; this
leaves the index arithmetic to `omega`. -/
private theorem smul_basis_congr {c c' : ℂ} {i j i' j' : ℕ} (hc : c = c') (hi : i = i')
    (hj : j = j') : c • basis q (i, j) = c' • basis q (i', j') := by
  rw [hc, hi, hj]

/-- A multiple of a basis monomial is the sum of two others with the same indices when its
coefficient is the sum of theirs; this leaves the index arithmetic to `omega`. -/
private theorem smul_basis_eq_add {c c₁ c₂ : ℂ} {i j i₁ j₁ i₂ j₂ : ℕ} (hi₁ : i₁ = i)
    (hj₁ : j₁ = j) (hi₂ : i₂ = i) (hj₂ : j₂ = j) (hc : c = c₁ + c₂) :
    c • basis q (i, j) = c₁ • basis q (i₁, j₁) + c₂ • basis q (i₂, j₂) := by
  rw [hi₁, hj₁, hi₂, hj₂, hc, add_smul]

/-- The generator operators satisfy the defining relations of `UqSl2 q`. -/
private def tuple (q : ℂ) [Fact (q ≠ 0)] : GeneratorTuple q (Module.End ℂ (QuantumPlane q)) where
  e := eOp q
  f := fOp q
  k := kOp q
  kInv := kInvOp q
  k_mul_kInv := (basis q).ext fun ⟨j, k⟩ => by
    simp [kOp_basis, kInvOp_basis, smul_smul, ← zpow_add₀ (Fact.out : q ≠ 0)]
  kInv_mul_k := (basis q).ext fun ⟨j, k⟩ => by
    simp [kOp_basis, kInvOp_basis, smul_smul, ← zpow_add₀ (Fact.out : q ≠ 0)]
  k_mul_e := (basis q).ext fun ⟨j, k⟩ => by
    simp only [mul_apply_eq_comp, LinearMap.smul_apply, eOp_basis, kOp_basis, map_smul,
      smul_smul]
    congr 1
    rcases j with _ | j
    · simp
    rw [add_tsub_cancel_right, zpow_succ_sub Fact.out]
    ring
  k_mul_f := (basis q).ext fun ⟨j, k⟩ => by
    have hq : q ≠ 0 := Fact.out
    simp only [mul_apply_eq_comp, LinearMap.smul_apply, fOp_basis, kOp_basis, map_smul,
      smul_smul]
    congr 1
    rcases k with _ | k
    · simp
    rw [add_tsub_cancel_right, zpow_succ_sub hq, inv_pow]
    field_simp
  e_mul_f_sub_f_mul_e := (basis q).ext fun ⟨j, k⟩ => by
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, mul_apply_eq_comp, eOp_fOp_basis,
      fOp_eOp_basis, kOp_basis, kInvOp_basis, ← sub_smul, smul_smul]
    congr 1
    -- The scalar identity is `[k]_q [j + 1]_q - [j]_q [k + 1]_q = [k - j]_q`.
    have h := quantumInteger_sub q k j
    rw [quantumInteger_def, show -((k : ℤ) - j) = j - k by ring, div_eq_inv_mul] at h
    linear_combination -h

/-! ### The module structure -/

variable [Fact (q ≠ 0)]

variable (q) in
/-- The action of `UqSl2 q` on the quantum plane, as an algebra map to complex endomorphisms. -/
def rep : UqSl2 q →ₐ[ℂ] Module.End ℂ (QuantumPlane q) :=
  UqSl2.lift (tuple q)

/-- The `UqSl2 q`-module structure of the quantum plane, given by `QuantumPlane.rep`. -/
instance instModule : Module (UqSl2 q) (QuantumPlane q) :=
  Module.compHom _ (rep q).toRingHom

/-- An element of `UqSl2 q` acts on the quantum plane through `QuantumPlane.rep`. -/
theorem smul_def (u : UqSl2 q) (a : QuantumPlane q) : u • a = rep q u a := (rfl)

instance : IsScalarTower ℂ (UqSl2 q) (QuantumPlane q) where
  smul_assoc c u a := by
    rw [smul_def, smul_def, map_smul, LinearMap.smul_apply]

private theorem rep_e : rep q (e q) = eOp q :=
  (lift_generator (tuple q) .e).trans (GeneratorTuple.toFun_e _)

private theorem rep_f : rep q (f q) = fOp q :=
  (lift_generator (tuple q) .f).trans (GeneratorTuple.toFun_f _)

private theorem rep_k : rep q (k q) = kOp q :=
  (lift_generator (tuple q) .k).trans (GeneratorTuple.toFun_k _)

private theorem rep_kInv : rep q (kInv q) = kInvOp q :=
  (lift_generator (tuple q) .kInv).trans (GeneratorTuple.toFun_kInv _)

/-- `E (y^i x^j) = [i]_q y^(i - 1) x^(j + 1)`; this vanishes when `i = 0`. -/
@[simp]
theorem e_smul_basis (i j : ℕ) :
    e q • basis q (i, j) = quantumInteger q i • basis q (i - 1, j + 1) := by
  rw [smul_def, rep_e, eOp_basis]

/-- `F (y^i x^j) = [j]_q y^(i + 1) x^(j - 1)`; this vanishes when `j = 0`. -/
@[simp]
theorem f_smul_basis (i j : ℕ) :
    f q • basis q (i, j) = quantumInteger q j • basis q (i + 1, j - 1) := by
  rw [smul_def, rep_f, fOp_basis]

/-- `K (y^i x^j) = q^(j - i) y^i x^j`. -/
@[simp]
theorem k_smul_basis (i j : ℕ) :
    k q • basis q (i, j) = q ^ ((j : ℤ) - i) • basis q (i, j) := by
  rw [smul_def, rep_k, kOp_basis]

/-- `K⁻¹ (y^i x^j) = q^(i - j) y^i x^j`. -/
@[simp]
theorem kInv_smul_basis (i j : ℕ) :
    kInv q • basis q (i, j) = q ^ ((i : ℤ) - j) • basis q (i, j) := by
  rw [smul_def, rep_kInv, kInvOp_basis]

/-! ### The twisted Leibniz rules -/

private theorem e_smul_basis_mul_basis (i j m n : ℕ) :
    e q • (basis q (i, j) * basis q (m, n)) =
      (e q • basis q (i, j)) * basis q (m, n) +
        (k q • basis q (i, j)) * (e q • basis q (m, n)) := by
  have hq : q ≠ 0 := Fact.out
  rcases i with _ | i <;> rcases m with _ | m <;>
    simp only [basis_mul_basis, smul_comm (e q), e_smul_basis, k_smul_basis, smul_mul_assoc,
      mul_smul_comm, smul_smul, Nat.cast_zero, quantumInteger_zero, zero_smul, zero_add, add_zero,
      zero_mul, mul_zero, smul_zero]
  · refine smul_basis_congr ?_ (by omega) (by omega)
    rw [sub_zero, zpow_natCast, add_tsub_cancel_right]
    ring
  · refine smul_basis_congr ?_ (by omega) (by omega)
    ring
  · refine smul_basis_eq_add (by omega) (by omega) (by omega) (by omega) ?_
    -- The scalar identity is
    -- `[(m + 1) + (i + 1)]_q = q^(m + 1) [i + 1]_q + q^(-(i + 1)) [m + 1]_q`.
    push_cast
    rw [show (i : ℤ) + 1 + (m + 1) = (m + 1) + (i + 1) by ring, quantumInteger_add]
    simp only [zpow_add₀ hq, zpow_sub₀ hq, zpow_neg, zpow_natCast, zpow_one]
    field_simp
    ring

private theorem f_smul_basis_mul_basis (i j m n : ℕ) :
    f q • (basis q (i, j) * basis q (m, n)) =
      (f q • basis q (i, j)) * (kInv q • basis q (m, n)) +
        basis q (i, j) * (f q • basis q (m, n)) := by
  have hq : q ≠ 0 := Fact.out
  rcases j with _ | j <;> rcases n with _ | n <;>
    simp only [basis_mul_basis, smul_comm (f q), f_smul_basis, kInv_smul_basis, smul_mul_assoc,
      mul_smul_comm, smul_smul, Nat.cast_zero, quantumInteger_zero, zero_smul, zero_add, add_zero,
      zero_mul, mul_zero, smul_zero]
  · exact smul_basis_congr (mul_comm _ _) (by omega) (by omega)
  · refine smul_basis_congr ?_ (by omega) (by omega)
    rw [sub_zero, zpow_natCast, add_tsub_cancel_right]
    ring
  · refine smul_basis_eq_add (by omega) (by omega) (by omega) (by omega) ?_
    -- The scalar identity is
    -- `[(j + 1) + (n + 1)]_q = q^(j + 1) [n + 1]_q + q^(-(n + 1)) [j + 1]_q`.
    push_cast
    rw [quantumInteger_add]
    simp only [zpow_add₀ hq, zpow_sub₀ hq, zpow_neg, zpow_natCast, zpow_one]
    field_simp
    ring

/-- An element acting on each monomial `y^i x^j` by the character `c^(j - i)` is multiplicative
on monomials, since the weights `j - i` add under `basis_mul_basis`. -/
private theorem smul_basis_mul_basis_of_weight {u : UqSl2 q} {c : ℂ} (hc : c ≠ 0)
    (hu : ∀ i j : ℕ, u • basis q (i, j) = c ^ ((j : ℤ) - i) • basis q (i, j)) (i j m n : ℕ) :
    u • (basis q (i, j) * basis q (m, n)) = (u • basis q (i, j)) * (u • basis q (m, n)) := by
  simp only [basis_mul_basis, smul_comm u, hu, smul_mul_assoc, mul_smul_comm, smul_smul]
  congr 1
  push_cast
  simp only [zpow_add₀ hc, zpow_sub₀ hc, zpow_natCast]
  ring

private theorem k_smul_basis_mul_basis (i j m n : ℕ) :
    k q • (basis q (i, j) * basis q (m, n)) = (k q • basis q (i, j)) * (k q • basis q (m, n)) :=
  smul_basis_mul_basis_of_weight Fact.out k_smul_basis i j m n

private theorem kInv_smul_basis_mul_basis (i j m n : ℕ) :
    kInv q • (basis q (i, j) * basis q (m, n)) =
      (kInv q • basis q (i, j)) * (kInv q • basis q (m, n)) :=
  smul_basis_mul_basis_of_weight (inv_ne_zero Fact.out)
    (fun i j => by rw [kInv_smul_basis, inv_zpow', neg_sub]) i j m n

/-- A twisted Leibniz rule `u (a b) = A(a) B(b) + C(a) D(b)` holds for all `a` and `b` once it
holds on pairs of monomials, since both sides are bilinear in `a` and `b`. -/
private theorem smul_mul_of_basis {u : UqSl2 q} (A B C D : Module.End ℂ (QuantumPlane q))
    (h : ∀ i j m n : ℕ, u • (basis q (i, j) * basis q (m, n)) =
      A (basis q (i, j)) * B (basis q (m, n)) + C (basis q (i, j)) * D (basis q (m, n)))
    (a b : QuantumPlane q) : u • (a * b) = A a * B b + C a * D b := by
  have hext : (LinearMap.mul ℂ _).compr₂ (rep q u) =
      (LinearMap.mul ℂ _).compl₁₂ A B + (LinearMap.mul ℂ _).compl₁₂ C D :=
    LinearMap.ext_basis (basis q) (basis q) fun ⟨i, j⟩ ⟨m, n⟩ => by
      simpa only [LinearMap.compr₂_apply, LinearMap.add_apply, LinearMap.compl₁₂_apply,
        LinearMap.mul_apply', ← smul_def] using h i j m n
  simpa only [LinearMap.compr₂_apply, LinearMap.add_apply, LinearMap.compl₁₂_apply,
    LinearMap.mul_apply', ← smul_def] using LinearMap.congr_fun₂ hext a b

/-- The twisted Leibniz rule `E (a b) = E(a) b + K(a) E(b)`, from `ΔE = E ⊗ 1 + K ⊗ E`. -/
theorem e_smul_mul (a b : QuantumPlane q) :
    e q • (a * b) = (e q • a) * b + (k q • a) * (e q • b) := by
  simpa only [LinearMap.id_apply, ← smul_def] using
    smul_mul_of_basis (rep q (e q)) LinearMap.id (rep q (k q)) (rep q (e q))
      (fun i j m n => by
        simpa only [LinearMap.id_apply, ← smul_def] using e_smul_basis_mul_basis i j m n) a b

/-- The twisted Leibniz rule `F (a b) = F(a) K⁻¹(b) + a F(b)`, from `ΔF = F ⊗ K⁻¹ + 1 ⊗ F`. -/
theorem f_smul_mul (a b : QuantumPlane q) :
    f q • (a * b) = (f q • a) * (kInv q • b) + a * (f q • b) := by
  simpa only [LinearMap.id_apply, ← smul_def] using
    smul_mul_of_basis (rep q (f q)) (rep q (kInv q)) LinearMap.id (rep q (f q))
      (fun i j m n => by
        simpa only [LinearMap.id_apply, ← smul_def] using f_smul_basis_mul_basis i j m n) a b

/-- `K` acts on the quantum plane by algebra automorphisms: `K (a b) = K(a) K(b)`. -/
theorem k_smul_mul (a b : QuantumPlane q) : k q • (a * b) = (k q • a) * (k q • b) := by
  simpa only [LinearMap.zero_apply, mul_zero, add_zero, ← smul_def] using
    smul_mul_of_basis (rep q (k q)) (rep q (k q)) 0 0
      (fun i j m n => by
        simpa only [LinearMap.zero_apply, mul_zero, add_zero, ← smul_def] using
          k_smul_basis_mul_basis i j m n) a b

/-- `K⁻¹` acts on the quantum plane by algebra automorphisms: `K⁻¹ (a b) = K⁻¹(a) K⁻¹(b)`. -/
theorem kInv_smul_mul (a b : QuantumPlane q) :
    kInv q • (a * b) = (kInv q • a) * (kInv q • b) := by
  simpa only [LinearMap.zero_apply, mul_zero, add_zero, ← smul_def] using
    smul_mul_of_basis (rep q (kInv q)) (rep q (kInv q)) 0 0
      (fun i j m n => by
        simpa only [LinearMap.zero_apply, mul_zero, add_zero, ← smul_def] using
          kInv_smul_basis_mul_basis i j m n) a b

/-- Every element of `UqSl2 q` acts on the unit of the quantum plane through the counit. -/
theorem smul_one_eq_counit_smul (u : UqSl2 q) :
    u • (1 : QuantumPlane q) = Coalgebra.counit (R := ℂ) u • 1 := by
  induction u using UqSl2.induction with
  | algebraMap c => rw [algebraMap_smul, Bialgebra.counit_algebraMap, Algebra.smul_def]
  | generator g =>
    rw [← basis_zero_zero]
    cases g <;> simp [-basis_zero_zero]
  | mul u v hu hv => rw [mul_smul, hv, smul_comm, hu, smul_smul, Bialgebra.counit_mul, mul_comm]
  | add u v hu hv => rw [add_smul, hu, hv, map_add, add_smul]

/-! ### Multiplication as a module map -/

variable (q) in
/-- Multiplication of the quantum plane, as a `UqSl2 q`-module map from the tensor product of the
quantum plane with itself under the coproduct action. That it is `UqSl2 q`-linear is the
module-algebra property. -/
def mulHom :
    Tensor ℂ (UqSl2 q) (QuantumPlane q) (QuantumPlane q) →ₗ[UqSl2 q] QuantumPlane q :=
  let φ : Tensor ℂ (UqSl2 q) (QuantumPlane q) (QuantumPlane q) →ₗ[ℂ] QuantumPlane q :=
    LinearMap.mul' ℂ (QuantumPlane q) ∘ₗ (tensorEquiv ℂ (UqSl2 q) _ _).toLinearMap
  have hφ (a b : QuantumPlane q) : φ (tmul ℂ (UqSl2 q) a b) = a * b := by
    simp [φ]
  have hgen (u : UqSl2 q) (hu : ∀ a b, φ (u • tmul ℂ (UqSl2 q) a b) = u • (a * b))
      (t : Tensor ℂ (UqSl2 q) (QuantumPlane q) (QuantumPlane q)) : φ (u • t) = u • φ t := by
    induction t using Tensor.inductionOn with
    | htmul a b => rw [hu, hφ]
    | hadd s t hs ht => rw [smul_add, map_add, map_add, hs, ht, smul_add]
  { φ with
    map_smul' u t := LinearMap.map_smul_of_commute_uqSl2 (q := q) φ
      (hgen _ fun a b => by rw [e_smul_tmul, map_add, hφ, hφ, e_smul_mul])
      (hgen _ fun a b => by rw [f_smul_tmul, map_add, hφ, hφ, f_smul_mul])
      (hgen _ fun a b => by rw [k_smul_tmul, hφ, k_smul_mul]) u t }

/-- `QuantumPlane.mulHom` multiplies the two tensor factors. -/
@[simp]
theorem mulHom_tmul (a b : QuantumPlane q) : mulHom q (tmul ℂ (UqSl2 q) a b) = a * b := by
  simp [mulHom]

/-! ### The generators -/

/-- `E x = 0`. -/
@[simp]
theorem e_smul_x : e q • x q = 0 := by
  simp [x_eq_basis]

/-- `E y = x`, when `[1]_q = 1`. -/
@[simp]
theorem e_smul_y (hq : q - q⁻¹ ≠ 0) : e q • y q = x q := by
  simp [y_eq_basis, x_eq_basis, hq]

/-- `F x = y`, when `[1]_q = 1`. -/
@[simp]
theorem f_smul_x (hq : q - q⁻¹ ≠ 0) : f q • x q = y q := by
  simp [y_eq_basis, x_eq_basis, hq]

/-- `F y = 0`. -/
@[simp]
theorem f_smul_y : f q • y q = 0 := by
  simp [y_eq_basis]

/-- `K x = q x`. -/
@[simp]
theorem k_smul_x : k q • x q = q • x q := by
  simp [x_eq_basis]

/-- `K y = q⁻¹ y`. -/
@[simp]
theorem k_smul_y : k q • y q = q⁻¹ • y q := by
  simp [y_eq_basis]

/-- `K⁻¹ x = q⁻¹ x`. -/
@[simp]
theorem kInv_smul_x : kInv q • x q = q⁻¹ • x q := by
  simp [x_eq_basis]

/-- `K⁻¹ y = q y`. -/
@[simp]
theorem kInv_smul_y : kInv q • y q = q • y q := by
  simp [y_eq_basis]

end TauCeti.QuantumPlane
