/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Coalgebra.GroupLike
public import Mathlib.RingTheory.HopfAlgebra.Convolution
public import TauCeti.Algebra.HopfAlgebra.Antipode
public import TauCeti.Algebra.HopfAlgebra.InverseAntipode
public import TauCeti.QuantumGroups.QuantizedEnvelopingAlgebra.Basic

import Mathlib.Tactic

/-!
# The Hopf algebra structure on a quantized enveloping algebra

For a symmetrizable Cartan datum `D : CartanDatum ι X Y` and parameter `q : K` in a field:

* The counit `ε(Eᵢ) = 0`, `ε(Fᵢ) = 0`, `ε(K_y) = 1` and the opposite-valued antipode
  `S(Eᵢ) = -Kᵢ⁻¹ Eᵢ`, `S(Fᵢ) = -Fᵢ Kᵢ`, `S(K_y) = K_(-y)` descend through the presentation for
  every `q : K` without restriction, and `S` is an algebra anti-automorphism (`antipodeEquiv`) whose
  square rescales `Eᵢ` by `qᵢ⁻²`, `Fᵢ` by `qᵢ²`, and fixes every `K_y`.
* Under the sharp divided-power condition `HasComul D q` — namely `q = 0` or
  `[1 - aᵢⱼ]_(qᵢ)! ≠ 0` for all `i ≠ j`, which holds automatically for every generic parameter
  `IsGenericQuantumParameter q` and whenever `Subsingleton ι` — the coproduct
  `Δ(Eᵢ) = Eᵢ ⊗ 1 + Kᵢ ⊗ Eᵢ`, `Δ(Fᵢ) = Fᵢ ⊗ Kᵢ⁻¹ + 1 ⊗ Fᵢ`, `Δ(K_y) = K_y ⊗ K_y` descends
  through the presentation and equips `QuantizedEnvelopingAlgebra D q` with `Bialgebra` and
  `HopfAlgebra` instances over `K`.

## Main definitions

* `TauCeti.QuantizedEnvelopingAlgebra.counit` and `antipodeOp`: the unconditional augmentation and
  opposite-valued antipode.
* `TauCeti.QuantizedEnvelopingAlgebra.antipodeEquiv`: the antipode as an algebra isomorphism onto
  the opposite algebra.
* `TauCeti.QuantizedEnvelopingAlgebra.HasComul`: sharp parameter condition for the Drinfeld–Jimbo
  coproduct.
* `TauCeti.QuantizedEnvelopingAlgebra.comul`, `instBialgebra`, `instHopfAlgebra`: the coproduct,
  bialgebra, and Hopf algebra structures under `[Fact (HasComul D q)]`.
* `TauCeti.QuantizedEnvelopingAlgebra.normE` and `normF`: the normalized generators `Kᵢ⁻¹ Eᵢ` and
  `Fᵢ Kᵢ`.

## Main results

* `TauCeti.QuantizedEnvelopingAlgebra.comul_e_quantumDividedPower` and
  `comul_f_quantumDividedPower`: coproduct formulas for the divided powers `Eᵢ^(n)` and `Fᵢ^(n)`.
* `TauCeti.QuantizedEnvelopingAlgebra.antipode_e_quantumDividedPower` and
  `antipode_f_quantumDividedPower`: antipode formulas for the divided powers `Eᵢ^(n)` and `Fᵢ^(n)`.
* `TauCeti.QuantizedEnvelopingAlgebra.antipode_bijective`, `antipode_antipode_e`,
  `antipode_antipode_f`, and `inverseAntipode` values on generators.
* `TauCeti.QuantizedEnvelopingAlgebra.comul_normE` and `comul_normF`: skew-primitive coproducts of
  `normE` and `normF`.

## References

* G. Lusztig, *Quantum groups at roots of 1*, Geom. Dedicata 35 (1990), §1–§2; *Canonical bases
  arising from quantized enveloping algebras*, J. Amer. Math. Soc. 3 (1990), Proposition 4.8.
* G. Lusztig, *Introduction to Quantum Groups*, Progress in Mathematics 110, Birkhäuser, 1993,
  §3.1.
* J. C. Jantzen, *Lectures on Quantum Groups*, Graduate Studies in Mathematics 6, American
  Mathematical Society, 1996, §4.8–§4.9.
* S. Lentner, *Quantum groups and Nichols algebras acting on conformal field theories*, Adv. Math.
  268 (2014), Theorem 3.3.
-/

public section

open scoped TensorProduct

namespace TauCeti.QuantizedEnvelopingAlgebra

section Unconditional

variable {ι X Y K : Type*} [AddCommGroup X] [AddCommGroup Y] [Field K]

/-! ### Unconditional counit -/

/-- The augmentation `QuantizedEnvelopingAlgebra D q →ₐ[K] K` sending `Eᵢ ↦ 0`, `Fᵢ ↦ 0`, and
`K_y ↦ 1`, defined for every `q : K`. -/
def counit (D : CartanDatum ι X Y) (q : K) : QuantizedEnvelopingAlgebra D q →ₐ[K] K :=
  lift
    { e _ := 0
      f _ := 0
      k _ := 1
      k_zero := rfl
      k_add _ _ := (mul_one 1).symm
      k_mul_e _ _ := by simp
      k_mul_f _ _ := by simp
      commutator_self _ := by simp
      commutator_ne _ := by simp
      serre_e {i j} hij := by
        exact quantumSerre_zero_left _ (D.serreLength_ne_zero_of_ne hij) 0
      serre_f {i j} hij := by
        exact quantumSerre_zero_left _ (D.serreLength_ne_zero_of_ne hij) 0 }

variable {D : CartanDatum ι X Y} {q : K}

/-- `counit` sends `Eᵢ` to `0`. -/
@[simp]
theorem counit_apply_e (i : ι) : counit D q (e D q i) = 0 :=
  lift_e _ i

/-- `counit` sends `Fᵢ` to `0`. -/
@[simp]
theorem counit_apply_f (i : ι) : counit D q (f D q i) = 0 :=
  lift_f _ i

/-- `counit` sends every toral generator `K_y` to `1`. -/
@[simp]
theorem counit_apply_k (y : Y) : counit D q (k D q y) = 1 :=
  lift_k _ y

/-- `counit` sends `Kᵢ` to `1`. -/
@[simp]
theorem counit_apply_simpleK (i : ι) : counit D q (simpleK D q i) = 1 := by
  rw [simpleK_def, counit_apply_k]

/-- `counit` sends `Kᵢ⁻¹` to `1`. -/
@[simp]
theorem counit_apply_simpleKInv (i : ι) : counit D q (simpleKInv D q i) = 1 := by
  rw [simpleKInv_def, counit_apply_k]

/-- Morphisms of Cartan data commute with `counit`. -/
@[simp]
theorem counit_comp_map {X' Y' : Type*} [AddCommGroup X'] [AddCommGroup Y']
    {D' : CartanDatum ι X' Y'} (φ : D.Hom D') :
    (counit D' q).comp (map φ q) = counit D q := by
  ext <;> simp

/-! ### Normalized Chevalley operators -/

/-- The normalized raising operator `eᵢ = Kᵢ⁻¹ Eᵢ`. -/
def normE (D : CartanDatum ι X Y) (q : K) (i : ι) : QuantizedEnvelopingAlgebra D q :=
  simpleKInv D q i * e D q i

/-- The defining formula `normE D q i = Kᵢ⁻¹ * Eᵢ`. -/
theorem normE_def (D : CartanDatum ι X Y) (q : K) (i : ι) :
    normE D q i = simpleKInv D q i * e D q i :=
  (rfl)

/-- The normalized lowering operator `fᵢ = Fᵢ Kᵢ`. -/
def normF (D : CartanDatum ι X Y) (q : K) (i : ι) : QuantizedEnvelopingAlgebra D q :=
  f D q i * simpleK D q i

/-- The defining formula `normF D q i = Fᵢ * Kᵢ`. -/
theorem normF_def (D : CartanDatum ι X Y) (q : K) (i : ι) :
    normF D q i = f D q i * simpleK D q i :=
  (rfl)

/-! ### Unconditional opposite-valued antipode and its bijectivity -/

private theorem antipode_commutator_self (i : ι) :
    MulOpposite.op (-(simpleKInv D q i * e D q i)) *
        MulOpposite.op (-(f D q i * simpleK D q i)) -
      MulOpposite.op (-(f D q i * simpleK D q i)) *
        MulOpposite.op (-(simpleKInv D q i * e D q i)) =
      (q ^ D.symmetrizer i - (q ^ D.symmetrizer i)⁻¹)⁻¹ •
        (MulOpposite.op (k D q (-D.simpleTorus i)) -
          MulOpposite.op (k D q (- -D.simpleTorus i))) := by
  apply MulOpposite.unop_injective
  simp only [MulOpposite.unop_sub, MulOpposite.unop_mul, MulOpposite.unop_op,
    MulOpposite.unop_smul, neg_mul_neg, neg_neg, ← simpleK_def, ← simpleKInv_def]
  rcases eq_or_ne q 0 with rfl | hq
  · simp [zero_pow (D.symmetrizer_pos i).ne']
  have hqi : q ^ D.symmetrizer i ≠ 0 := pow_ne_zero _ hq
  have hprod : simpleKInv D q i * e D q i * (f D q i * simpleK D q i) = e D q i * f D q i := by
    rw [simpleKInv_mul_e, smul_mul_assoc, mul_assoc, ← mul_assoc (simpleKInv D q i),
      simpleKInv_mul_f, smul_mul_assoc, mul_smul_comm, smul_smul, ← zpow_add₀ hqi,
      neg_add_cancel, zpow_zero, one_smul]
    simp only [mul_assoc, simpleKInv_mul_simpleK, mul_one]
  have hprod' : f D q i * simpleK D q i * (simpleKInv D q i * e D q i) = f D q i * e D q i := by
    simp only [mul_assoc, simpleK_mul_simpleKInv_mul]
  rw [hprod, hprod', ← neg_sub (e D q i * f D q i), e_mul_f_sub_f_mul_e_self, ← smul_neg,
    neg_sub]

private theorem antipode_commutator_ne {i j : ι} (hij : i ≠ j) :
    MulOpposite.op (-(simpleKInv D q i * e D q i)) *
        MulOpposite.op (-(f D q j * simpleK D q j)) -
      MulOpposite.op (-(f D q j * simpleK D q j)) *
        MulOpposite.op (-(simpleKInv D q i * e D q i)) = 0 := by
  apply MulOpposite.unop_injective
  simp only [MulOpposite.unop_sub, MulOpposite.unop_mul, MulOpposite.unop_op,
    MulOpposite.unop_zero, neg_mul_neg]
  rcases eq_or_ne q 0 with rfl | hq
  · simp
  have hkcomm : simpleK D q j * simpleKInv D q i = simpleKInv D q i * simpleK D q j := by
    rw [simpleK_def, simpleKInv_def, ← k_add, ← k_add, add_comm]
  have hfe : f D q j * simpleKInv D q i =
      (q ^ D.symmetrizer i) ^ (-D.cartan i j) • (simpleKInv D q i * f D q j) := by
    rw [simpleKInv_def, f_mul_k, map_neg, D.pairing_root_simpleTorus, ← D.symmetrizer_mul_cartan,
      ← mul_neg, zpow_mul, zpow_natCast]
  have hek : simpleK D q j * e D q i =
      (q ^ D.symmetrizer i) ^ D.cartan i j • (e D q i * simpleK D q j) := by
    rw [simpleK_mul_e, ← zpow_natCast, ← zpow_mul, ← D.symmetrizer_mul_cartan i j, zpow_mul,
      zpow_natCast]
  have hqi : q ^ D.symmetrizer i ≠ 0 := pow_ne_zero _ hq
  calc
    f D q j * simpleK D q j * (simpleKInv D q i * e D q i) -
        simpleKInv D q i * e D q i * (f D q j * simpleK D q j) =
        (f D q j * simpleKInv D q i) * (simpleK D q j * e D q i) -
          simpleKInv D q i * (e D q i * f D q j) * simpleK D q j := by
      rw [mul_assoc (f D q j), ← mul_assoc (simpleK D q j), hkcomm]
      simp only [mul_assoc]
    _ = 0 := by
      rw [hfe, hek, smul_mul_smul_comm, ← zpow_add₀ hqi, neg_add_cancel, zpow_zero, one_smul,
        e_mul_f_of_ne hij]
      simp only [mul_assoc, sub_self]

private theorem antipode_serre_e {i j : ι} (hij : i ≠ j) :
    quantumSerre (q ^ D.symmetrizer i) (D.serreLength i j)
        (MulOpposite.op (-(simpleKInv D q i * e D q i)))
        (MulOpposite.op (-(simpleKInv D q j * e D q j))) = 0 := by
  have hcast : 1 - (D.serreLength i j : ℤ) = D.cartan i j := by
    rw [D.serreLength_cast_of_ne hij]; ring
  have hej : e D q i * simpleKInv D q j =
      (q ^ D.symmetrizer i) ^ (1 - (D.serreLength i j : ℤ)) • (simpleKInv D q j * e D q i) := by
    rw [hcast, e_mul_simpleKInv, ← zpow_natCast, ← zpow_mul, ← D.symmetrizer_mul_cartan i j,
      zpow_mul, zpow_natCast]
  have hcomm : Commute (simpleKInv D q i) (simpleKInv D q j) := by
    rw [Commute, SemiconjBy, simpleKInv_def, simpleKInv_def, ← k_add, ← k_add, add_comm]
  rw [quantumSerre_op, ← neg_one_smul K (simpleKInv D q i * e D q i),
    ← neg_one_smul K (simpleKInv D q j * e D q j), quantumSerre_smul,
    quantumSerre_mul_left (D.serreLength i j)
      (by simpa [D.cartan_apply_self] using e_mul_simpleKInv (D := D) (q := q) i i)
      hej
      (by rw [hcast]; exact e_mul_simpleKInv i j)
      hcomm,
    serre_e_eq_zero hij]
  simp

private theorem antipode_serre_f {i j : ι} (hij : i ≠ j) :
    quantumSerre (q ^ D.symmetrizer i) (D.serreLength i j)
        (MulOpposite.op (-(f D q i * simpleK D q i)))
        (MulOpposite.op (-(f D q j * simpleK D q j))) = 0 := by
  set u := (q ^ D.symmetrizer i)⁻¹
  have hcast : 1 - (D.serreLength i j : ℤ) = D.cartan i j := by
    rw [D.serreLength_cast_of_ne hij]; ring
  have h1 : MulOpposite.op (f D q i) * MulOpposite.op (simpleK D q i) =
      u ^ 2 • (MulOpposite.op (simpleK D q i) * MulOpposite.op (f D q i)) := by
    rw [← MulOpposite.op_mul, simpleK_mul_f, D.cartan_apply_self, MulOpposite.op_smul,
      MulOpposite.op_mul]
    simp [u, inv_pow]
  have h2 : MulOpposite.op (f D q i) * MulOpposite.op (simpleK D q j) =
      u ^ (1 - (D.serreLength i j : ℤ)) •
        (MulOpposite.op (simpleK D q j) * MulOpposite.op (f D q i)) := by
    rw [← MulOpposite.op_mul, simpleK_mul_f, ← zpow_natCast, ← zpow_mul, mul_neg,
      ← D.symmetrizer_mul_cartan i j, ← mul_neg, zpow_mul, zpow_natCast, hcast, inv_zpow',
      MulOpposite.op_smul, MulOpposite.op_mul]
  have h3 : MulOpposite.op (f D q j) * MulOpposite.op (simpleK D q i) =
      u ^ (1 - (D.serreLength i j : ℤ)) •
        (MulOpposite.op (simpleK D q i) * MulOpposite.op (f D q j)) := by
    rw [← MulOpposite.op_mul, simpleK_mul_f, hcast, inv_zpow', MulOpposite.op_smul,
      MulOpposite.op_mul]
  have hcomm : Commute (MulOpposite.op (simpleK D q i)) (MulOpposite.op (simpleK D q j)) := by
    rw [Commute, SemiconjBy, ← MulOpposite.op_mul, ← MulOpposite.op_mul, simpleK_def, simpleK_def,
      ← k_add, ← k_add, add_comm]
  rw [← quantumSerre_inv, ← neg_one_smul K (f D q i * simpleK D q i),
    ← neg_one_smul K (f D q j * simpleK D q j),
    MulOpposite.op_smul, MulOpposite.op_smul, MulOpposite.op_mul, MulOpposite.op_mul,
    quantumSerre_smul, quantumSerre_mul_left (D.serreLength i j) h1 h2 h3 hcomm,
    quantumSerre_inv, quantumSerre_op, serre_f_eq_zero hij]
  simp

/-- The antipode as a `K`-algebra homomorphism into the opposite algebra, sending
`Eᵢ ↦ op (-(Kᵢ⁻¹ * Eᵢ))`, `Fᵢ ↦ op (-(Fᵢ * Kᵢ))`, and `K_y ↦ op K_(-y)` for every `q : K`. -/
def antipodeOp (D : CartanDatum ι X Y) (q : K) :
    QuantizedEnvelopingAlgebra D q →ₐ[K] (QuantizedEnvelopingAlgebra D q)ᵐᵒᵖ :=
  lift
    { e i := MulOpposite.op (-(simpleKInv D q i * e D q i))
      f i := MulOpposite.op (-(f D q i * simpleK D q i))
      k y := MulOpposite.op (k D q (-y))
      k_zero := by simp
      k_add y z := by
        apply MulOpposite.unop_injective
        simp [← k_add, add_comm]
      k_mul_e i y := by
        apply MulOpposite.unop_injective
        simp only [MulOpposite.unop_mul, MulOpposite.unop_op, MulOpposite.unop_smul, neg_mul,
          mul_neg, mul_assoc]
        rw [e_mul_k i (-y), map_neg, neg_neg, mul_smul_comm, ← smul_neg,
          ← mul_assoc (simpleKInv D q i), simpleKInv_def, ← k_add, add_comm (-D.simpleTorus i),
          k_add, mul_assoc]
      k_mul_f i y := by
        apply MulOpposite.unop_injective
        simp only [MulOpposite.unop_mul, MulOpposite.unop_op, MulOpposite.unop_smul, neg_mul,
          mul_neg]
        rw [mul_assoc (f D q i), simpleK_def, ← k_add, add_comm (D.simpleTorus i), k_add,
          ← mul_assoc (f D q i), f_mul_k i (-y), map_neg, smul_mul_assoc, ← smul_neg, mul_assoc]
      commutator_self := antipode_commutator_self
      commutator_ne := antipode_commutator_ne
      serre_e := antipode_serre_e
      serre_f := antipode_serre_f }

/-- `antipodeOp` sends `Eᵢ` to `op (-(Kᵢ⁻¹ * Eᵢ))`. -/
@[simp]
theorem antipodeOp_e (i : ι) :
    antipodeOp D q (e D q i) = MulOpposite.op (-(simpleKInv D q i * e D q i)) :=
  lift_e _ i

/-- `antipodeOp` sends `Fᵢ` to `op (-(Fᵢ * Kᵢ))`. -/
@[simp]
theorem antipodeOp_f (i : ι) :
    antipodeOp D q (f D q i) = MulOpposite.op (-(f D q i * simpleK D q i)) :=
  lift_f _ i

/-- `antipodeOp` sends `K_y` to `op K_(-y)`. -/
@[simp]
theorem antipodeOp_k (y : Y) :
    antipodeOp D q (k D q y) = MulOpposite.op (k D q (-y)) :=
  lift_k _ y

/-- `antipodeOp` sends `Kᵢ` to `op Kᵢ⁻¹`. -/
@[simp]
theorem antipodeOp_simpleK (i : ι) :
    antipodeOp D q (simpleK D q i) = MulOpposite.op (simpleKInv D q i) := by
  rw [simpleK_def, simpleKInv_def, antipodeOp_k]

/-- `antipodeOp` sends `Kᵢ⁻¹` to `op Kᵢ`. -/
@[simp]
theorem antipodeOp_simpleKInv (i : ι) :
    antipodeOp D q (simpleKInv D q i) = MulOpposite.op (simpleK D q i) := by
  simp [simpleKInv_def, simpleK_def]

/-- The diagonal rescaling automorphism equal to the square of the antipode: scaling `Eᵢ` by
`qᵢ⁻²`, `Fᵢ` by `qᵢ²`, and fixing every `K_y` (reducing to the identity at `q = 0`). -/
noncomputable def antipodeSqEquiv (D : CartanDatum ι X Y) (q : K) :
    QuantizedEnvelopingAlgebra D q ≃ₐ[K] QuantizedEnvelopingAlgebra D q := by
  classical
  exact if hq : q = 0 then
    AlgEquiv.refl
  else
    rescaleAlgEquiv D q fun i => ((Units.mk0 (q ^ D.symmetrizer i) (pow_ne_zero _ hq)) ^ 2)⁻¹

/-- `antipodeSqEquiv` scales `Eᵢ` by `(qᵢ²)⁻¹`. -/
@[simp]
theorem antipodeSqEquiv_e (i : ι) :
    antipodeSqEquiv D q (e D q i) = ((q ^ D.symmetrizer i) ^ 2)⁻¹ • e D q i := by
  rcases eq_or_ne q 0 with rfl | hq <;> simp [antipodeSqEquiv, *]

/-- `antipodeSqEquiv` scales `Fᵢ` by `qᵢ²`. -/
@[simp]
theorem antipodeSqEquiv_f (i : ι) :
    antipodeSqEquiv D q (f D q i) = (q ^ D.symmetrizer i) ^ 2 • f D q i := by
  rcases eq_or_ne q 0 with rfl | hq <;> simp [antipodeSqEquiv, *]

/-- `antipodeSqEquiv` fixes every toral generator `K_y`. -/
@[simp]
theorem antipodeSqEquiv_k (y : Y) :
    antipodeSqEquiv D q (k D q y) = k D q y := by
  classical
  rw [antipodeSqEquiv]
  split_ifs <;> simp

private theorem opComm_antipodeOp_comp_antipodeOp :
    (AlgHom.opComm (antipodeOp D q)).comp (antipodeOp D q) = (antipodeSqEquiv D q).toAlgHom := by
  ext i
  · simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, antipodeSqEquiv_e, antipodeOp_e,
      AlgHom.opComm_apply_apply, MulOpposite.unop_op, map_neg, map_mul, antipodeOp_simpleKInv,
      MulOpposite.unop_neg, MulOpposite.unop_mul, neg_mul, neg_neg]
    rw [simpleKInv_mul_e, D.cartan_apply_self, zpow_neg, zpow_ofNat, smul_mul_assoc, mul_assoc,
      simpleKInv_mul_simpleK, mul_one]
  · simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, antipodeSqEquiv_f, antipodeOp_f,
      AlgHom.opComm_apply_apply, MulOpposite.unop_op, map_neg, map_mul, antipodeOp_simpleK,
      MulOpposite.unop_neg, MulOpposite.unop_mul, mul_neg, neg_neg]
    rw [← mul_assoc, simpleKInv_mul_f, D.cartan_apply_self, zpow_ofNat, smul_mul_assoc, mul_assoc,
      simpleKInv_mul_simpleK, mul_one]
  · simp

/-- `antipodeOp D q` is bijective for every `q : K`. -/
theorem antipodeOp_bijective (D : CartanDatum ι X Y) (q : K) :
    Function.Bijective (antipodeOp D q) := by
  let T : QuantizedEnvelopingAlgebra D q → QuantizedEnvelopingAlgebra D q :=
    fun x => MulOpposite.unop (antipodeOp D q x)
  have hTT : T ∘ T = antipodeSqEquiv D q := by
    funext x
    exact AlgHom.congr_fun opComm_antipodeOp_comp_antipodeOp x
  have hbijT : Function.Bijective T := by
    have hcomp : Function.Bijective (T ∘ T) := hTT ▸ (antipodeSqEquiv D q).bijective
    exact ⟨Function.Injective.of_comp hcomp.1, Function.Surjective.of_comp hcomp.2⟩
  have heq : (antipodeOp D q : QuantizedEnvelopingAlgebra D q → _) = MulOpposite.op ∘ T := by
    funext x
    simp [T]
  exact heq ▸ MulOpposite.opEquiv.bijective.comp hbijT

/-- The antipode of `QuantizedEnvelopingAlgebra D q` as an algebra isomorphism onto the opposite
algebra, valid for every `q : K`. -/
noncomputable def antipodeEquiv (D : CartanDatum ι X Y) (q : K) :
    QuantizedEnvelopingAlgebra D q ≃ₐ[K] (QuantizedEnvelopingAlgebra D q)ᵐᵒᵖ :=
  AlgEquiv.ofBijective (antipodeOp D q) (antipodeOp_bijective D q)

/-- Coercing `antipodeEquiv` to an `AlgHom` recovers `antipodeOp`. -/
@[simp]
theorem antipodeEquiv_toAlgHom : (antipodeEquiv D q).toAlgHom = antipodeOp D q :=
  (rfl)

/-- `antipodeEquiv` evaluates to `antipodeOp`. -/
@[simp]
theorem antipodeEquiv_apply (x : QuantizedEnvelopingAlgebra D q) :
    antipodeEquiv D q x = antipodeOp D q x :=
  (rfl)

end Unconditional

/-! ### Coproduct, bialgebra, and Hopf algebra structure -/

section Hopf

variable {ι X Y K : Type*} [AddCommGroup X] [AddCommGroup Y] [Field K]

/-- Sharp parameter condition under which the presentation of `QuantizedEnvelopingAlgebra D q`
admits the Drinfeld–Jimbo coproduct: either `q = 0` or `[1 - aᵢⱼ]_(qᵢ)! ≠ 0` for all `i ≠ j`. -/
def HasComul (D : CartanDatum ι X Y) (q : K) : Prop :=
  q = 0 ∨ ∀ i j, i ≠ j → quantumFactorial (q ^ D.symmetrizer i) (D.serreLength i j) ≠ 0

/-- At `q = 0`, `HasComul D 0` holds unconditionally. -/
theorem HasComul.zero (D : CartanDatum ι X Y) : HasComul D (0 : K) :=
  Or.inl rfl

/-- At a generic quantum parameter `q`, `HasComul D q` holds for every Cartan datum `D`. -/
theorem _root_.TauCeti.IsGenericQuantumParameter.hasComul {D : CartanDatum ι X Y} {q : K}
    (hq : IsGenericQuantumParameter q) : HasComul D q :=
  Or.inr fun i j _ => quantumFactorial_ne_zero (hq.pow (D.symmetrizer_pos i)) (D.serreLength i j)

/-- `Fact (HasComul D q)` synthesized from `Fact (IsGenericQuantumParameter q)`. -/
instance instFactHasComulOfGeneric (D : CartanDatum ι X Y) (q : K)
    [Fact (IsGenericQuantumParameter q)] : Fact (HasComul D q) :=
  ⟨(Fact.out : IsGenericQuantumParameter q).hasComul⟩

/-- When `ι` has at most one simple root, there are no off-diagonal Serre relations, so
`HasComul D q` holds for every `q : K`. -/
instance instFactHasComulOfSubsingleton [Subsingleton ι] (D : CartanDatum ι X Y) (q : K) :
    Fact (HasComul D q) :=
  ⟨Or.inr fun i j hij => (hij (Subsingleton.elim i j)).elim⟩

private theorem comul_commutator_self {D : CartanDatum ι X Y} {q : K} (i : ι) :
    (e D q i ⊗ₜ[K] (1 : QuantizedEnvelopingAlgebra D q) + simpleK D q i ⊗ₜ[K] e D q i) *
        (f D q i ⊗ₜ[K] simpleKInv D q i + 1 ⊗ₜ[K] f D q i) -
      (f D q i ⊗ₜ[K] simpleKInv D q i + 1 ⊗ₜ[K] f D q i) *
        (e D q i ⊗ₜ[K] 1 + simpleK D q i ⊗ₜ[K] e D q i) =
      (q ^ D.symmetrizer i - (q ^ D.symmetrizer i)⁻¹)⁻¹ •
        (k D q (D.simpleTorus i) ⊗ₜ[K] k D q (D.simpleTorus i) -
          k D q (-D.simpleTorus i) ⊗ₜ[K] k D q (-D.simpleTorus i)) := by
  rcases eq_or_ne q 0 with rfl | hq
  · simp [zero_pow (D.symmetrizer_pos i).ne']
  have hqi : q ^ D.symmetrizer i ≠ 0 := pow_ne_zero _ hq
  simp only [mul_add, add_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
  rw [simpleK_mul_f, e_mul_simpleKInv, D.cartan_apply_self]
  simp only [← TensorProduct.smul_tmul', TensorProduct.tmul_smul, smul_smul, ← zpow_add₀ hqi,
    add_neg_cancel, zpow_zero, one_smul]
  trans (e D q i * f D q i - f D q i * e D q i) ⊗ₜ[K] simpleKInv D q i +
      simpleK D q i ⊗ₜ[K] (e D q i * f D q i - f D q i * e D q i)
  · simp only [TensorProduct.sub_tmul, TensorProduct.tmul_sub]
    abel
  · rw [e_mul_f_sub_f_mul_e_self, ← simpleK_def, ← simpleKInv_def]
    simp only [← TensorProduct.smul_tmul', TensorProduct.tmul_smul, TensorProduct.sub_tmul,
      TensorProduct.tmul_sub, ← smul_add]
    congr 1
    abel

private theorem comul_commutator_ne {D : CartanDatum ι X Y} {q : K} {i j : ι} (hij : i ≠ j) :
    (e D q i ⊗ₜ[K] (1 : QuantizedEnvelopingAlgebra D q) + simpleK D q i ⊗ₜ[K] e D q i) *
        (f D q j ⊗ₜ[K] simpleKInv D q j + 1 ⊗ₜ[K] f D q j) -
      (f D q j ⊗ₜ[K] simpleKInv D q j + 1 ⊗ₜ[K] f D q j) *
        (e D q i ⊗ₜ[K] 1 + simpleK D q i ⊗ₜ[K] e D q i) = 0 := by
  rcases eq_or_ne q 0 with rfl | hq
  · simp
  have hqi : q ^ D.symmetrizer i ≠ 0 := pow_ne_zero _ hq
  have hej : e D q i * simpleKInv D q j =
      (q ^ D.symmetrizer i) ^ D.cartan i j • (simpleKInv D q j * e D q i) := by
    rw [e_mul_simpleKInv, ← zpow_natCast, ← zpow_mul, ← D.symmetrizer_mul_cartan i j, zpow_mul,
      zpow_natCast]
  simp only [mul_add, add_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
  rw [simpleK_mul_f, hej, e_mul_f_of_ne hij]
  simp only [← TensorProduct.smul_tmul', TensorProduct.tmul_smul, smul_smul, ← zpow_add₀ hqi,
    add_neg_cancel, zpow_zero, one_smul]
  abel

private theorem tmul_right_quantumDividedPower {D : CartanDatum ι X Y} {q : K}
    (u x : QuantizedEnvelopingAlgebra D q) (u' : K) (n : ℕ) :
    quantumDividedPower u' (u ⊗ₜ[K] x) n = (u ^ n) ⊗ₜ[K] quantumDividedPower u' x n := by
  rw [quantumDividedPower_def, quantumDividedPower_def, Algebra.TensorProduct.tmul_pow,
    TensorProduct.tmul_smul]

private theorem tmul_left_quantumDividedPower {D : CartanDatum ι X Y} {q : K}
    (x u : QuantizedEnvelopingAlgebra D q) (u' : K) (n : ℕ) :
    quantumDividedPower u' (x ⊗ₜ[K] u) n = quantumDividedPower u' x n ⊗ₜ[K] (u ^ n) := by
  rw [quantumDividedPower_def, quantumDividedPower_def, Algebra.TensorProduct.tmul_pow,
    TensorProduct.smul_tmul']

private theorem comul_serre_e {D : CartanDatum ι X Y} {q : K} (hcomul : HasComul D q)
    {i j : ι} (hij : i ≠ j) :
    quantumSerre (q ^ D.symmetrizer i) (D.serreLength i j)
        (e D q i ⊗ₜ[K] (1 : QuantizedEnvelopingAlgebra D q) + simpleK D q i ⊗ₜ[K] e D q i)
        (e D q j ⊗ₜ[K] 1 + simpleK D q j ⊗ₜ[K] e D q j) = 0 := by
  rcases hcomul with rfl | hfac
  · simp [quantumSerre_zero_left _ (D.serreLength_ne_zero_of_ne hij)]
  have hcast : 1 - (D.serreLength i j : ℤ) = D.cartan i j := by
    rw [D.serreLength_cast_of_ne hij]; ring
  have hs₁ : quantumSerre (q ^ D.symmetrizer i) (D.serreLength i j)
      (e D q i ⊗ₜ[K] (1 : QuantizedEnvelopingAlgebra D q)) (e D q j ⊗ₜ[K] 1) = 0 := by
    simpa only [AlgHom.map_quantumSerre, Algebra.TensorProduct.includeLeft_apply, map_zero] using
      congrArg (Algebra.TensorProduct.includeLeft :
        QuantizedEnvelopingAlgebra D q →ₐ[K]
          QuantizedEnvelopingAlgebra D q ⊗[K] QuantizedEnvelopingAlgebra D q)
        (serre_e_eq_zero hij)
  have hs₂ : quantumSerre (q ^ D.symmetrizer i) (D.serreLength i j)
      (simpleK D q i ⊗ₜ[K] e D q i) (simpleK D q j ⊗ₜ[K] e D q j) = 0 := by
    rw [quantumSerre_def]
    have hterm : ∀ r ∈ Finset.range (D.serreLength i j + 1),
        (-1 : K) ^ r • (quantumDividedPower (q ^ D.symmetrizer i) (simpleK D q i ⊗ₜ[K] e D q i) r *
            (simpleK D q j ⊗ₜ[K] e D q j) *
            quantumDividedPower (q ^ D.symmetrizer i) (simpleK D q i ⊗ₜ[K] e D q i)
              (D.serreLength i j - r)) =
          (simpleK D q i ^ D.serreLength i j * simpleK D q j) ⊗ₜ[K]
            ((-1 : K) ^ r • (quantumDividedPower (q ^ D.symmetrizer i) (e D q i) r * e D q j *
              quantumDividedPower (q ^ D.symmetrizer i) (e D q i) (D.serreLength i j - r))) := by
      intro r hr
      have hrm : r ≤ D.serreLength i j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)
      have hk : simpleK D q i ^ r * simpleK D q j * simpleK D q i ^ (D.serreLength i j - r) =
          simpleK D q i ^ D.serreLength i j * simpleK D q j := by
        have hc : Commute (simpleK D q i) (simpleK D q j) := by
          rw [Commute, SemiconjBy, simpleK_def, simpleK_def, ← k_add, ← k_add, add_comm]
        rw [mul_assoc, (hc.symm.pow_right (D.serreLength i j - r)).eq, ← mul_assoc, ← pow_add,
          Nat.add_sub_of_le hrm]
      rw [tmul_right_quantumDividedPower, tmul_right_quantumDividedPower,
        Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, hk,
        TensorProduct.tmul_smul]
    rw [Finset.sum_congr rfl hterm, ← TensorProduct.tmul_sum, ← quantumSerre_def,
      serre_e_eq_zero hij, TensorProduct.tmul_zero]
  refine quantumSerre_add_eq_zero (hfac i j hij) ?_ ?_ ?_ hs₁ hs₂
  · simp [Algebra.TensorProduct.tmul_mul_tmul, simpleK_mul_e, TensorProduct.smul_tmul']
  · simp [Algebra.TensorProduct.tmul_mul_tmul, hcast, simpleK_mul_e, TensorProduct.smul_tmul']
  · rw [Algebra.TensorProduct.tmul_mul_tmul, simpleK_mul_e, ← zpow_natCast, ← zpow_mul,
      ← D.symmetrizer_mul_cartan i j, zpow_mul, zpow_natCast, ← hcast, mul_one,
      ← TensorProduct.smul_tmul', Algebra.TensorProduct.tmul_mul_tmul, one_mul]

private theorem comul_serre_f {D : CartanDatum ι X Y} {q : K} (hcomul : HasComul D q)
    {i j : ι} (hij : i ≠ j) :
    quantumSerre (q ^ D.symmetrizer i) (D.serreLength i j)
        (f D q i ⊗ₜ[K] simpleKInv D q i + 1 ⊗ₜ[K] f D q i)
        (f D q j ⊗ₜ[K] simpleKInv D q j + 1 ⊗ₜ[K] f D q j) = 0 := by
  rcases hcomul with rfl | hfac
  · simp [quantumSerre_zero_left _ (D.serreLength_ne_zero_of_ne hij)]
  have hcast : 1 - (D.serreLength i j : ℤ) = D.cartan i j := by
    rw [D.serreLength_cast_of_ne hij]; ring
  rw [add_comm (f D q i ⊗ₜ[K] simpleKInv D q i), add_comm (f D q j ⊗ₜ[K] simpleKInv D q j)]
  have hs₁ : quantumSerre (q ^ D.symmetrizer i) (D.serreLength i j)
      ((1 : QuantizedEnvelopingAlgebra D q) ⊗ₜ[K] f D q i) (1 ⊗ₜ[K] f D q j) = 0 := by
    simpa only [AlgHom.map_quantumSerre, Algebra.TensorProduct.includeRight_apply, map_zero] using
      congrArg (Algebra.TensorProduct.includeRight :
        QuantizedEnvelopingAlgebra D q →ₐ[K]
          QuantizedEnvelopingAlgebra D q ⊗[K] QuantizedEnvelopingAlgebra D q)
        (serre_f_eq_zero hij)
  have hs₂ : quantumSerre (q ^ D.symmetrizer i) (D.serreLength i j)
      (f D q i ⊗ₜ[K] simpleKInv D q i) (f D q j ⊗ₜ[K] simpleKInv D q j) = 0 := by
    rw [quantumSerre_def]
    have hterm : ∀ r ∈ Finset.range (D.serreLength i j + 1),
        (-1 : K) ^ r •
          (quantumDividedPower (q ^ D.symmetrizer i) (f D q i ⊗ₜ[K] simpleKInv D q i) r *
            (f D q j ⊗ₜ[K] simpleKInv D q j) *
            quantumDividedPower (q ^ D.symmetrizer i) (f D q i ⊗ₜ[K] simpleKInv D q i)
              (D.serreLength i j - r)) =
          ((-1 : K) ^ r • (quantumDividedPower (q ^ D.symmetrizer i) (f D q i) r * f D q j *
            quantumDividedPower (q ^ D.symmetrizer i) (f D q i) (D.serreLength i j - r))) ⊗ₜ[K]
            (simpleKInv D q i ^ D.serreLength i j * simpleKInv D q j) := by
      intro r hr
      have hrm : r ≤ D.serreLength i j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)
      have hk : simpleKInv D q i ^ r * simpleKInv D q j *
          simpleKInv D q i ^ (D.serreLength i j - r) =
          simpleKInv D q i ^ D.serreLength i j * simpleKInv D q j := by
        have hc : Commute (simpleKInv D q i) (simpleKInv D q j) := by
          rw [Commute, SemiconjBy, simpleKInv_def, simpleKInv_def, ← k_add, ← k_add, add_comm]
        rw [mul_assoc, (hc.symm.pow_right (D.serreLength i j - r)).eq, ← mul_assoc, ← pow_add,
          Nat.add_sub_of_le hrm]
      rw [tmul_left_quantumDividedPower, tmul_left_quantumDividedPower,
        Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, hk,
        ← TensorProduct.smul_tmul']
    rw [Finset.sum_congr rfl hterm, ← TensorProduct.sum_tmul, ← quantumSerre_def,
      serre_f_eq_zero hij, TensorProduct.zero_tmul]
  refine quantumSerre_add_eq_zero (hfac i j hij) ?_ ?_ ?_ hs₁ hs₂
  · simp [Algebra.TensorProduct.tmul_mul_tmul, simpleKInv_mul_f]
  · simp [Algebra.TensorProduct.tmul_mul_tmul, hcast, simpleKInv_mul_f]
  · rw [Algebra.TensorProduct.tmul_mul_tmul, simpleKInv_mul_f, ← zpow_natCast, ← zpow_mul,
      ← D.symmetrizer_mul_cartan i j, zpow_mul, zpow_natCast, ← hcast, mul_one,
      TensorProduct.tmul_smul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]

/-- The Drinfeld–Jimbo coproduct `Δ(Eᵢ) = Eᵢ ⊗ 1 + Kᵢ ⊗ Eᵢ`, `Δ(Fᵢ) = Fᵢ ⊗ Kᵢ⁻¹ + 1 ⊗ Fᵢ`,
`Δ(K_y) = K_y ⊗ K_y` under `[Fact (HasComul D q)]`. -/
noncomputable def comul (D : CartanDatum ι X Y) (q : K) [Fact (HasComul D q)] :
    QuantizedEnvelopingAlgebra D q →ₐ[K]
      QuantizedEnvelopingAlgebra D q ⊗[K] QuantizedEnvelopingAlgebra D q :=
  lift
    { e i := e D q i ⊗ₜ[K] 1 + simpleK D q i ⊗ₜ[K] e D q i
      f i := f D q i ⊗ₜ[K] simpleKInv D q i + 1 ⊗ₜ[K] f D q i
      k y := k D q y ⊗ₜ[K] k D q y
      k_zero := by simp [Algebra.TensorProduct.one_def]
      k_add y z := by simp [k_add, Algebra.TensorProduct.tmul_mul_tmul]
      k_mul_e i y := by
        rw [mul_add, add_mul, Algebra.TensorProduct.tmul_mul_tmul,
          Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul,
          Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, k_mul_e,
          ← TensorProduct.smul_tmul', TensorProduct.tmul_smul, smul_add, simpleK_def, ← k_add,
          ← k_add, add_comm y]
      k_mul_f i y := by
        rw [mul_add, add_mul, Algebra.TensorProduct.tmul_mul_tmul,
          Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul,
          Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, k_mul_f,
          ← TensorProduct.smul_tmul', TensorProduct.tmul_smul, smul_add, simpleKInv_def, ← k_add,
          ← k_add, add_comm y]
      commutator_self := comul_commutator_self
      commutator_ne := comul_commutator_ne
      serre_e := comul_serre_e Fact.out
      serre_f := comul_serre_f Fact.out }

@[local simp]
private theorem comul_eAux (D : CartanDatum ι X Y) (q : K) [Fact (HasComul D q)] (i : ι) :
    comul D q (e D q i) = e D q i ⊗ₜ[K] 1 + simpleK D q i ⊗ₜ[K] e D q i :=
  lift_e _ i

@[local simp]
private theorem comul_fAux (D : CartanDatum ι X Y) (q : K) [Fact (HasComul D q)] (i : ι) :
    comul D q (f D q i) = f D q i ⊗ₜ[K] simpleKInv D q i + 1 ⊗ₜ[K] f D q i :=
  lift_f _ i

@[local simp]
private theorem comul_kAux (D : CartanDatum ι X Y) (q : K) [Fact (HasComul D q)] (y : Y) :
    comul D q (k D q y) = k D q y ⊗ₜ[K] k D q y :=
  lift_k _ y

/-- The `K`-bialgebra structure on `QuantizedEnvelopingAlgebra D q`. -/
noncomputable instance instBialgebra (D : CartanDatum ι X Y) (q : K) [Fact (HasComul D q)] :
    Bialgebra K (QuantizedEnvelopingAlgebra D q) :=
  Bialgebra.ofAlgHom (comul D q) (counit D q)
    (by
      ext i
      · simp [simpleK_def, TensorProduct.tmul_add, TensorProduct.add_tmul, add_assoc,
          Algebra.TensorProduct.one_def]
      · simp [simpleKInv_def, TensorProduct.tmul_add, TensorProduct.add_tmul, add_assoc,
          Algebra.TensorProduct.one_def]
      · simp)
    (by ext <;> simp [simpleK_def, simpleKInv_def])
    (by ext <;> simp [simpleK_def, simpleKInv_def])

/-- The `K`-Hopf algebra structure on `QuantizedEnvelopingAlgebra D q`. -/
noncomputable instance instHopfAlgebra (D : CartanDatum ι X Y) (q : K) [Fact (HasComul D q)] :
    HopfAlgebra K (QuantizedEnvelopingAlgebra D q) :=
  HopfAlgebra.ofAntipodeOfAdjoin (antipodeOp D q) (adjoin_range_generator D q)
    (by
      rintro _ ⟨g, rfl⟩
      cases g <;> simp [Coalgebra.comul, Coalgebra.counit, simpleK_def, simpleKInv_def, mul_assoc])
    (by
      rintro _ ⟨g, rfl⟩
      cases g <;>
        simp [Coalgebra.comul, Coalgebra.counit, simpleK_def, simpleKInv_def,
          ← mul_assoc (k D q _)])

section Simp

variable {D : CartanDatum ι X Y} {q : K} [Fact (HasComul D q)]

/-- `comul D q` agrees with `Coalgebra.comul`. -/
@[simp]
theorem comul_apply (x : QuantizedEnvelopingAlgebra D q) :
    comul D q x = Coalgebra.comul (R := K) x :=
  (rfl)

/-- `counit D q` agrees with `Coalgebra.counit`. -/
@[simp]
theorem counit_apply (x : QuantizedEnvelopingAlgebra D q) :
    counit D q x = Coalgebra.counit (R := K) x :=
  (rfl)

/-- `antipodeOp D q` agrees with `MulOpposite.op ∘ HopfAlgebra.antipode K`. -/
@[simp]
theorem antipodeOp_apply (x : QuantizedEnvelopingAlgebra D q) :
    antipodeOp D q x = MulOpposite.op (HopfAlgebra.antipode K x) :=
  (rfl)

/-- Coproduct of `Eᵢ`: `Δ(Eᵢ) = Eᵢ ⊗ 1 + Kᵢ ⊗ Eᵢ`. -/
@[simp]
theorem comul_e (i : ι) :
    Coalgebra.comul (R := K) (e D q i) = e D q i ⊗ₜ[K] 1 + simpleK D q i ⊗ₜ[K] e D q i :=
  comul_eAux D q i

/-- Coproduct of `Fᵢ`: `Δ(Fᵢ) = Fᵢ ⊗ Kᵢ⁻¹ + 1 ⊗ Fᵢ`. -/
@[simp]
theorem comul_f (i : ι) :
    Coalgebra.comul (R := K) (f D q i) = f D q i ⊗ₜ[K] simpleKInv D q i + 1 ⊗ₜ[K] f D q i :=
  comul_fAux D q i

/-- Every toral generator `K_y` has group-like coproduct `Δ(K_y) = K_y ⊗ K_y`. -/
@[simp]
theorem comul_k (y : Y) :
    Coalgebra.comul (R := K) (k D q y) = k D q y ⊗ₜ[K] k D q y :=
  comul_kAux D q y

/-- Coproduct of `Kᵢ`. -/
@[simp]
theorem comul_simpleK (i : ι) :
    Coalgebra.comul (R := K) (simpleK D q i) = simpleK D q i ⊗ₜ[K] simpleK D q i := by
  rw [simpleK_def, comul_k]

/-- Coproduct of `Kᵢ⁻¹`. -/
@[simp]
theorem comul_simpleKInv (i : ι) :
    Coalgebra.comul (R := K) (simpleKInv D q i) = simpleKInv D q i ⊗ₜ[K] simpleKInv D q i := by
  rw [simpleKInv_def, comul_k]

/-- Every toral generator `K_y` is group-like. -/
theorem isGroupLikeElem_k (y : Y) : IsGroupLikeElem K (k D q y) :=
  ⟨counit_apply_k y, comul_k y⟩

/-- Counit of `Eᵢ`. -/
@[simp]
theorem counit_e (i : ι) : Coalgebra.counit (R := K) (e D q i) = 0 :=
  counit_apply_e i

/-- Counit of `Fᵢ`. -/
@[simp]
theorem counit_f (i : ι) : Coalgebra.counit (R := K) (f D q i) = 0 :=
  counit_apply_f i

/-- Counit of `K_y`. -/
@[simp]
theorem counit_k (y : Y) : Coalgebra.counit (R := K) (k D q y) = 1 :=
  counit_apply_k y

/-- Antipode of `Eᵢ`: `S(Eᵢ) = -(Kᵢ⁻¹ * Eᵢ)`. -/
@[simp]
theorem antipode_e (i : ι) :
    HopfAlgebra.antipode K (e D q i) = -(simpleKInv D q i * e D q i) :=
  MulOpposite.op_injective ((antipodeOp_apply (e D q i)).symm.trans (antipodeOp_e i))

/-- Antipode of `Fᵢ`: `S(Fᵢ) = -(Fᵢ * Kᵢ)`. -/
@[simp]
theorem antipode_f (i : ι) :
    HopfAlgebra.antipode K (f D q i) = -(f D q i * simpleK D q i) :=
  MulOpposite.op_injective ((antipodeOp_apply (f D q i)).symm.trans (antipodeOp_f i))

/-- Antipode of `K_y`: `S(K_y) = K_(-y)`. -/
@[simp]
theorem antipode_k (y : Y) :
    HopfAlgebra.antipode K (k D q y) = k D q (-y) :=
  MulOpposite.op_injective ((antipodeOp_apply (k D q y)).symm.trans (antipodeOp_k y))

/-- Antipode of `Kᵢ`. -/
@[simp]
theorem antipode_simpleK (i : ι) :
    HopfAlgebra.antipode K (simpleK D q i) = simpleKInv D q i := by
  rw [simpleK_def, simpleKInv_def, antipode_k]

/-- Antipode of `Kᵢ⁻¹`. -/
@[simp]
theorem antipode_simpleKInv (i : ι) :
    HopfAlgebra.antipode K (simpleKInv D q i) = simpleK D q i := by
  simp [simpleKInv_def, simpleK_def]

/-! ### Normalized operators and divided-power Hopf formulas -/

/-- Skew-primitive coproduct of `normE`: `Δ(eᵢ) = eᵢ ⊗ Kᵢ⁻¹ + 1 ⊗ eᵢ`. -/
theorem comul_normE (i : ι) :
    Coalgebra.comul (R := K) (normE D q i) =
      normE D q i ⊗ₜ[K] simpleKInv D q i + 1 ⊗ₜ[K] normE D q i := by
  rw [← comul_apply, normE_def, map_mul, comul_apply, comul_apply, comul_simpleKInv, comul_e,
    mul_add, Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
    simpleKInv_mul_simpleK, ← normE_def]

/-- Skew-primitive coproduct of `normF`: `Δ(fᵢ) = fᵢ ⊗ 1 + Kᵢ ⊗ fᵢ`. -/
theorem comul_normF (i : ι) :
    Coalgebra.comul (R := K) (normF D q i) =
      normF D q i ⊗ₜ[K] 1 + simpleK D q i ⊗ₜ[K] normF D q i := by
  rw [← comul_apply, normF_def, map_mul, comul_apply, comul_apply, comul_f, comul_simpleK,
    add_mul, Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
    simpleKInv_mul_simpleK, ← normF_def]

/-- **Divided-power coproduct of `Eᵢ`**: when `[n]_(qᵢ)! ≠ 0`,
`Δ(Eᵢ^(n)) = ∑_{a = 0}^n qᵢ^(a(n - a)) • (Eᵢ^(a) Kᵢ^(n - a) ⊗ Eᵢ^(n - a))`. -/
theorem comul_e_quantumDividedPower (i : ι) {n : ℕ}
    (hn : quantumFactorial (q ^ D.symmetrizer i) n ≠ 0) :
    Coalgebra.comul (R := K) (quantumDividedPower (q ^ D.symmetrizer i) (e D q i) n) =
      ∑ a ∈ Finset.range (n + 1),
        (q ^ D.symmetrizer i) ^ (a * (n - a)) •
          ((quantumDividedPower (q ^ D.symmetrizer i) (e D q i) a * simpleK D q i ^ (n - a)) ⊗ₜ[K]
            quantumDividedPower (q ^ D.symmetrizer i) (e D q i) (n - a)) := by
  rw [← comul_apply, AlgHom.map_quantumDividedPower, comul_apply, comul_e,
    quantumDividedPower_add
      (by simp [Algebra.TensorProduct.tmul_mul_tmul, simpleK_mul_e, TensorProduct.smul_tmul']) hn]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [tmul_left_quantumDividedPower, tmul_right_quantumDividedPower, one_pow,
    Algebra.TensorProduct.tmul_mul_tmul, one_mul]

/-- **Divided-power coproduct of `Fᵢ`**: when `[n]_(qᵢ)! ≠ 0`,
`Δ(Fᵢ^(n)) = ∑_{a = 0}^n qᵢ^(a(n - a)) • (Fᵢ^(a) ⊗ Fᵢ^(n - a) Kᵢ⁻¹ ^ a)`. -/
theorem comul_f_quantumDividedPower (i : ι) {n : ℕ}
    (hn : quantumFactorial (q ^ D.symmetrizer i) n ≠ 0) :
    Coalgebra.comul (R := K) (quantumDividedPower (q ^ D.symmetrizer i) (f D q i) n) =
      ∑ a ∈ Finset.range (n + 1),
        (q ^ D.symmetrizer i) ^ (a * (n - a)) •
          (quantumDividedPower (q ^ D.symmetrizer i) (f D q i) a ⊗ₜ[K]
            (quantumDividedPower (q ^ D.symmetrizer i) (f D q i) (n - a) *
              simpleKInv D q i ^ a)) := by
  rw [← comul_apply, AlgHom.map_quantumDividedPower, comul_apply, comul_f,
    add_comm (f D q i ⊗ₜ[K] simpleKInv D q i),
    quantumDividedPower_add
      (by simp [Algebra.TensorProduct.tmul_mul_tmul, simpleKInv_mul_f]) hn,
    ← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun a ha => ?_
  have han : a ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
  rw [Nat.add_sub_cancel, Nat.sub_sub_self han, mul_comm (n - a) a,
    tmul_right_quantumDividedPower, tmul_left_quantumDividedPower, one_pow,
    Algebra.TensorProduct.tmul_mul_tmul, one_mul]

/-- **Divided-power antipode of `Eᵢ`**:
`S(Eᵢ^(n)) = (-1)^n • qᵢ^(n(n - 1)) • (Kᵢ⁻¹ ^ n * Eᵢ^(n))`. -/
theorem antipode_e_quantumDividedPower (i : ι) (n : ℕ) :
    HopfAlgebra.antipode K (quantumDividedPower (q ^ D.symmetrizer i) (e D q i) n) =
      ((-1 : K) ^ n * (q ^ D.symmetrizer i) ^ (n * (n - 1))) •
        (simpleKInv D q i ^ n * quantumDividedPower (q ^ D.symmetrizer i) (e D q i) n) := by
  apply MulOpposite.op_injective
  rw [← antipodeOp_apply, AlgHom.map_quantumDividedPower, antipodeOp_apply, antipode_e,
    quantumDividedPower_op, quantumDividedPower_neg,
    quantumDividedPower_mul_of_mul_eq_sq_smul_mul
      (by simpa [D.cartan_apply_self] using e_mul_simpleKInv (D := D) (q := q) i i) n,
    smul_smul]

/-- **Divided-power antipode of `Fᵢ`**:
`S(Fᵢ^(n)) = (-1)^n • (qᵢ⁻¹)^(n(n - 1)) • (Fᵢ^(n) * Kᵢ ^ n)`. -/
theorem antipode_f_quantumDividedPower (i : ι) (n : ℕ) :
    HopfAlgebra.antipode K (quantumDividedPower (q ^ D.symmetrizer i) (f D q i) n) =
      ((-1 : K) ^ n * (q ^ D.symmetrizer i)⁻¹ ^ (n * (n - 1))) •
        (quantumDividedPower (q ^ D.symmetrizer i) (f D q i) n * simpleK D q i ^ n) := by
  apply MulOpposite.op_injective
  have hrel : MulOpposite.op (f D q i) * MulOpposite.op (simpleK D q i) =
      ((q ^ D.symmetrizer i)⁻¹) ^ 2 •
        (MulOpposite.op (simpleK D q i) * MulOpposite.op (f D q i)) := by
    rw [← MulOpposite.op_mul, simpleK_mul_f, D.cartan_apply_self, MulOpposite.op_smul,
      MulOpposite.op_mul]
    simp [inv_pow]
  rw [← antipodeOp_apply, AlgHom.map_quantumDividedPower, antipodeOp_apply, antipode_f,
    MulOpposite.op_neg, quantumDividedPower_neg, ← quantumDividedPower_inv, MulOpposite.op_mul,
    quantumDividedPower_mul_of_mul_eq_sq_smul_mul hrel n, quantumDividedPower_inv,
    quantumDividedPower_op, ← MulOpposite.op_pow, ← MulOpposite.op_mul, ← MulOpposite.op_smul,
    ← MulOpposite.op_smul, smul_smul]

/-! ### Square, bijectivity, and inverse of the Hopf antipode -/

/-- The square of `HopfAlgebra.antipode K` equals `antipodeSqEquiv D q`. -/
theorem antipode_antipode (x : QuantizedEnvelopingAlgebra D q) :
    HopfAlgebra.antipode K (HopfAlgebra.antipode K x) = antipodeSqEquiv D q x :=
  AlgHom.congr_fun opComm_antipodeOp_comp_antipodeOp x

/-- `S²(Eᵢ) = (qᵢ²)⁻¹ • Eᵢ`. -/
theorem antipode_antipode_e (i : ι) :
    HopfAlgebra.antipode K (HopfAlgebra.antipode K (e D q i)) =
      ((q ^ D.symmetrizer i) ^ 2)⁻¹ • e D q i := by
  rw [antipode_antipode, antipodeSqEquiv_e]

/-- `S²(Fᵢ) = qᵢ² • Fᵢ`. -/
theorem antipode_antipode_f (i : ι) :
    HopfAlgebra.antipode K (HopfAlgebra.antipode K (f D q i)) =
      (q ^ D.symmetrizer i) ^ 2 • f D q i := by
  rw [antipode_antipode, antipodeSqEquiv_f]

/-- `S²` fixes every toral generator `K_y`. -/
theorem antipode_antipode_k (y : Y) :
    HopfAlgebra.antipode K (HopfAlgebra.antipode K (k D q y)) = k D q y := by
  simp

/-- The linear antipode of `QuantizedEnvelopingAlgebra D q` is bijective. -/
theorem antipode_bijective (D : CartanDatum ι X Y) (q : K) [Fact (HasComul D q)] :
    Function.Bijective (HopfAlgebra.antipode K :
      QuantizedEnvelopingAlgebra D q →ₗ[K] QuantizedEnvelopingAlgebra D q) := by
  have heq : (HopfAlgebra.antipode K : QuantizedEnvelopingAlgebra D q → _) =
      MulOpposite.unop ∘ antipodeOp D q := by
    funext x
    rfl
  exact heq ▸ MulOpposite.unop_bijective.comp (antipodeOp_bijective D q)

/-- The inverse antipode sends `Eᵢ` to `-(Eᵢ * Kᵢ⁻¹)`. -/
@[simp]
theorem inverseAntipode_e (i : ι) :
    TauCeti.HopfAlgebra.inverseAntipode (antipode_bijective D q) (e D q i) =
      -(e D q i * simpleKInv D q i) := by
  apply (antipode_bijective D q).injective
  simp [HopfAlgebra.antipode_mul_antidistrib]

/-- The inverse antipode sends `Fᵢ` to `-(Kᵢ * Fᵢ)`. -/
@[simp]
theorem inverseAntipode_f (i : ι) :
    TauCeti.HopfAlgebra.inverseAntipode (antipode_bijective D q) (f D q i) =
      -(simpleK D q i * f D q i) := by
  apply (antipode_bijective D q).injective
  simp [HopfAlgebra.antipode_mul_antidistrib, mul_assoc]

/-- The inverse antipode sends `K_y` to `K_(-y)`. -/
@[simp]
theorem inverseAntipode_k (y : Y) :
    TauCeti.HopfAlgebra.inverseAntipode (antipode_bijective D q) (k D q y) = k D q (-y) := by
  apply (antipode_bijective D q).injective
  simp

/-- Morphisms of Cartan data intertwine the coproduct. -/
theorem comul_map {X' Y' : Type*} [AddCommGroup X'] [AddCommGroup Y']
    {D' : CartanDatum ι X' Y'} (φ : D.Hom D') [Fact (HasComul D' q)]
    (x : QuantizedEnvelopingAlgebra D q) :
    Coalgebra.comul (R := K) (map φ q x) =
      Algebra.TensorProduct.map (map φ q) (map φ q) (Coalgebra.comul (R := K) x) := by
  have h : (comul D' q).comp (map φ q) =
      (Algebra.TensorProduct.map (map φ q) (map φ q)).comp (comul D q) := by
    ext <;> simp
  exact AlgHom.congr_fun h x

/-- Morphisms of Cartan data intertwine the antipode. -/
theorem antipode_map {X' Y' : Type*} [AddCommGroup X'] [AddCommGroup Y']
    {D' : CartanDatum ι X' Y'} (φ : D.Hom D') [Fact (HasComul D' q)]
    (x : QuantizedEnvelopingAlgebra D q) :
    HopfAlgebra.antipode K (map φ q x) = map φ q (HopfAlgebra.antipode K x) := by
  have h : (antipodeOp D' q).comp (map φ q) = (map φ q).op.comp (antipodeOp D q) := by
    ext i
    · apply MulOpposite.unop_injective; simp
    · apply MulOpposite.unop_injective; simp
    · apply MulOpposite.unop_injective; simp [← map_neg]
  exact MulOpposite.op_injective (AlgHom.congr_fun h x)

end Simp

end Hopf

end TauCeti.QuantizedEnvelopingAlgebra
