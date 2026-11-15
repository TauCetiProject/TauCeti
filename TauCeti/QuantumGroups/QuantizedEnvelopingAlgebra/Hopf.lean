/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Coalgebra.GroupLike
public import Mathlib.RingTheory.HopfAlgebra.Convolution
public import TauCeti.Algebra.HopfAlgebra.InverseAntipode
public import TauCeti.QuantumGroups.QuantizedEnvelopingAlgebra.Basic

import TauCeti.Algebra.HopfAlgebra.Basic

/-!
# The Hopf algebra structure on a quantized enveloping algebra

For a symmetrizable Cartan datum `D : CartanDatum ι X Y` and parameter `q : K` in a field:

* The counit `counit` (`Eᵢ, Fᵢ ↦ 0`, `K_y ↦ 1`) and opposite-valued antipode `antipodeOp` /
  `antipodeEquiv` (`Eᵢ ↦ -Kᵢ⁻¹ Eᵢ`, `Fᵢ ↦ -Fᵢ Kᵢ`, `K_y ↦ K_(-y)`) descend for all `q : K`, with
  `S² = antipodeSqEquiv` rescaling `Eᵢ` by `qᵢ⁻²`, `Fᵢ` by `qᵢ²`, and fixing `K_y`.
* Under the sufficient parameter condition `HasComul D q` (`q = 0` or `[1 - aᵢⱼ]_(qᵢ)! ≠ 0` for
  `i ≠ j`), `comul` (`Δ(Eᵢ) = Eᵢ ⊗ 1 + Kᵢ ⊗ Eᵢ`, `Δ(Fᵢ) = Fᵢ ⊗ Kᵢ⁻¹ + 1 ⊗ Fᵢ`, `Δ(K_y) = K_y ⊗ K_y`)
  equips `QuantizedEnvelopingAlgebra D q` with `Bialgebra` and `HopfAlgebra` instances, functorial
  bialgebra morphisms (`mapBialgHom`), divided-power coproduct and antipode formulas, bijective
  antipode, and skew-primitive normalized operators `normalizedE` and `normalizedF`.

## References

* G. Lusztig, *Quantum groups at roots of 1*, Geom. Dedicata 35 (1990), 89–113, §1–§2; *Finite
  dimensional Hopf algebras arising from quantized universal enveloping algebras*, J. Amer. Math.
  Soc. 3 (1990), 257–296, Proposition 4.8.
* G. Lusztig, *Introduction to Quantum Groups*, Birkhäuser, 1993, §3.1.
* J. C. Jantzen, *Lectures on Quantum Groups*, American Mathematical Society, 1996, §4.8–§4.9.
* S. D. Lentner, *A Frobenius homomorphism for Lusztig's quantum groups over arbitrary roots of
  unity*, Commun. Contemp. Math. 18 (2016), no. 3, 1550040 (arXiv:1406.0865), Theorem 3.3 (in the
  opposite coproduct tensor-factor order).
* `TauCeti.QuantumGroups.UqSl2.Hopf` and `TauCeti.QuantumGroups.UqSl2.Antipode`, from which the
  `Bialgebra.ofAlgHom`, `HopfAlgebra.ofAntipodeOfAdjoin`, and `antipodeOp`/`antipodeEquiv`
  formalization pattern is adapted.
-/

public section

open scoped TensorProduct

namespace TauCeti.QuantizedEnvelopingAlgebra

section Unconditional

variable {ι X Y X' Y' K : Type*} [AddCommGroup X] [AddCommGroup Y]
  [AddCommGroup X'] [AddCommGroup Y'] [Field K]

/-- The augmentation `QuantizedEnvelopingAlgebra D q →ₐ[K] K` sending `Eᵢ ↦ 0`, `Fᵢ ↦ 0`, and
`K_y ↦ 1`, defined for every `q : K`. -/
def counit (D : CartanDatum ι X Y) (q : K) : QuantizedEnvelopingAlgebra D q →ₐ[K] K :=
  lift
    { e _ := 0, f _ := 0, k _ := 1, k_zero := rfl, k_add _ _ := (mul_one 1).symm,
      k_mul_e _ _ := by simp, k_mul_f _ _ := by simp, commutator_self _ := by simp,
      commutator_of_ne _ := by simp
      serre_e hij := quantumSerre_zero_left _ (D.serreLength_ne_zero_of_ne hij) 0
      serre_f hij := quantumSerre_zero_left _ (D.serreLength_ne_zero_of_ne hij) 0 }

variable {D : CartanDatum ι X Y} {D' : CartanDatum ι X' Y'} {q : K}

@[simp] theorem counit_apply_e (i : ι) : counit D q (e D q i) = 0 := lift_e _ i
@[simp] theorem counit_apply_f (i : ι) : counit D q (f D q i) = 0 := lift_f _ i
@[simp] theorem counit_apply_k (y : Y) : counit D q (k D q y) = 1 := lift_k _ y
@[simp] theorem counit_apply_simpleK (i : ι) : counit D q (simpleK D q i) = 1 := by
  simp [simpleK_def]
@[simp] theorem counit_apply_simpleKInv (i : ι) : counit D q (simpleKInv D q i) = 1 := by
  simp [simpleKInv_def]
@[simp] theorem counit_comp_map (φ : D.Hom D') : (counit D' q).comp (map φ q) = counit D q := by
  ext <;> simp
@[simp] theorem counit_apply_map (φ : D.Hom D') (x : QuantizedEnvelopingAlgebra D q) :
    counit D' q (map φ q x) = counit D q x := by
  simpa only [AlgHom.comp_apply] using AlgHom.congr_fun (counit_comp_map φ) x

/-- The normalized raising operator `eᵢ = Kᵢ⁻¹ Eᵢ`. -/
def normalizedE (D : CartanDatum ι X Y) (q : K) (i : ι) : QuantizedEnvelopingAlgebra D q :=
  simpleKInv D q i * e D q i
theorem normalizedE_def (D : CartanDatum ι X Y) (q : K) (i : ι) :
    normalizedE D q i = simpleKInv D q i * e D q i := (rfl)
/-- The normalized lowering operator `fᵢ = Fᵢ Kᵢ`. -/
def normalizedF (D : CartanDatum ι X Y) (q : K) (i : ι) : QuantizedEnvelopingAlgebra D q :=
  f D q i * simpleK D q i
theorem normalizedF_def (D : CartanDatum ι X Y) (q : K) (i : ι) :
    normalizedF D q i = f D q i * simpleK D q i := (rfl)
@[simp] theorem counit_apply_normalizedE (i : ι) : counit D q (normalizedE D q i) = 0 := by
  simp [normalizedE_def]
@[simp] theorem counit_apply_normalizedF (i : ι) : counit D q (normalizedF D q i) = 0 := by
  simp [normalizedF_def]
@[simp] theorem map_normalizedE (φ : D.Hom D') (i : ι) :
    map φ q (normalizedE D q i) = normalizedE D' q i := by simp [normalizedE_def]
@[simp] theorem map_normalizedF (φ : D.Hom D') (i : ι) :
    map φ q (normalizedF D q i) = normalizedF D' q i := by simp [normalizedF_def]
theorem k_mul_normalizedE (i : ι) (y : Y) :
    k D q y * normalizedE D q i = q ^ D.pairing (D.root i) y • (normalizedE D q i * k D q y) := by
  rw [normalizedE_def, ← mul_assoc, (commute_k_simpleKInv y i).eq, mul_assoc, k_mul_e,
    mul_smul_comm, ← mul_assoc]
theorem k_mul_normalizedF (i : ι) (y : Y) :
    k D q y * normalizedF D q i =
      q ^ (-D.pairing (D.root i) y) • (normalizedF D q i * k D q y) := by
  rw [normalizedF_def, ← mul_assoc, k_mul_f, smul_mul_assoc, mul_assoc,
    (commute_k_simpleK y i).eq, ← mul_assoc]

private theorem op_f_mul_op_simpleK (i j : ι) :
    MulOpposite.op (f D q j) * MulOpposite.op (simpleK D q i) =
      ((q ^ D.symmetrizer i)⁻¹) ^ D.cartan i j •
        (MulOpposite.op (simpleK D q i) * MulOpposite.op (f D q j)) := by
  rw [← MulOpposite.op_mul, simpleK_mul_f, ← inv_zpow', MulOpposite.op_smul, MulOpposite.op_mul]
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
  rcases eq_or_ne q 0 with rfl | hq; · simp [zero_pow (D.symmetrizer_pos i).ne']
  have hprod : simpleKInv D q i * e D q i * (f D q i * simpleK D q i) = e D q i * f D q i := by
    rw [simpleKInv_mul_e, smul_mul_assoc, mul_assoc, ← mul_assoc (simpleKInv D q i),
      simpleKInv_mul_f, smul_mul_assoc, mul_smul_comm, smul_smul, ← zpow_add₀ (pow_ne_zero _ hq),
      neg_add_cancel, zpow_zero, one_smul]
    simp only [mul_assoc, simpleKInv_mul_simpleK, mul_one]
  rw [hprod, mul_assoc (f D q i), simpleK_mul_simpleKInv_mul, ← neg_sub (e D q i * f D q i),
    e_mul_f_sub_f_mul_e_self, ← smul_neg, neg_sub]
private theorem antipode_commutator_of_ne {i j : ι} (hij : i ≠ j) :
    MulOpposite.op (-(simpleKInv D q i * e D q i)) *
        MulOpposite.op (-(f D q j * simpleK D q j)) -
      MulOpposite.op (-(f D q j * simpleK D q j)) *
        MulOpposite.op (-(simpleKInv D q i * e D q i)) = 0 := by
  apply MulOpposite.unop_injective
  simp only [MulOpposite.unop_sub, MulOpposite.unop_mul, MulOpposite.unop_op,
    MulOpposite.unop_zero, neg_mul_neg]
  rcases eq_or_ne q 0 with rfl | hq; · simp
  have hek : simpleK D q j * e D q i =
      (q ^ D.symmetrizer i) ^ D.cartan i j • (e D q i * simpleK D q j) := by
    rw [simpleK_mul_e, D.pow_symmetrizer_zpow_cartan]
  have h1 : f D q j * simpleK D q j * (simpleKInv D q i * e D q i) =
      (f D q j * simpleKInv D q i) * (simpleK D q j * e D q i) := by
    rw [mul_assoc (f D q j), ← mul_assoc (simpleK D q j), (commute_simpleK_simpleKInv j i).eq]
    simp only [mul_assoc]
  rw [h1, f_mul_simpleKInv, hek, smul_mul_smul_comm, ← zpow_add₀ (pow_ne_zero _ hq), neg_add_cancel,
    zpow_zero, one_smul, mul_assoc (simpleKInv D q i), ← mul_assoc (f D q j), ← e_mul_f_of_ne hij]
  simp only [mul_assoc, sub_self]
private theorem antipode_serre_e {i j : ι} (hij : i ≠ j) :
    quantumSerre (q ^ D.symmetrizer i) (D.serreLength i j)
        (MulOpposite.op (-(simpleKInv D q i * e D q i)))
        (MulOpposite.op (-(simpleKInv D q j * e D q j))) = 0 := by
  have hcast := D.one_sub_natCast_serreLength_of_ne hij
  rw [quantumSerre_op, ← neg_one_smul K (simpleKInv D q i * e D q i),
    ← neg_one_smul K (simpleKInv D q j * e D q j), quantumSerre_smul,
    quantumSerre_mul_left (D.serreLength i j)
      (by simpa [D.cartan_apply_self] using e_mul_simpleKInv (D := D) (q := q) i i)
      (by rw [hcast, e_mul_simpleKInv, D.pow_symmetrizer_zpow_cartan])
      (by rw [hcast, e_mul_simpleKInv]) (commute_simpleKInv i j),
    quantumSerre_e_eq_zero_of_ne hij]
  simp
private theorem antipode_serre_f {i j : ι} (hij : i ≠ j) :
    quantumSerre (q ^ D.symmetrizer i) (D.serreLength i j)
        (MulOpposite.op (-(f D q i * simpleK D q i)))
        (MulOpposite.op (-(f D q j * simpleK D q j))) = 0 := by
  have hcast := D.one_sub_natCast_serreLength_of_ne hij
  rw [← quantumSerre_inv, ← neg_one_smul K (f D q i * simpleK D q i),
    ← neg_one_smul K (f D q j * simpleK D q j), MulOpposite.op_smul, MulOpposite.op_smul,
    MulOpposite.op_mul, MulOpposite.op_mul, quantumSerre_smul,
    quantumSerre_mul_left (D.serreLength i j)
      (by simpa [D.cartan_apply_self] using op_f_mul_op_simpleK (D := D) (q := q) i i)
      (by rw [op_f_mul_op_simpleK, inv_zpow', zpow_neg, D.pow_symmetrizer_zpow_cartan, ← zpow_neg,
        ← inv_zpow', hcast])
      (by rw [op_f_mul_op_simpleK, ← hcast]) ((commute_simpleK i j).op),
    quantumSerre_inv, quantumSerre_op, quantumSerre_f_eq_zero_of_ne hij]
  simp

/-- The antipode as a `K`-algebra homomorphism into the opposite algebra, sending
`Eᵢ ↦ op (-(Kᵢ⁻¹ * Eᵢ))`, `Fᵢ ↦ op (-(Fᵢ * Kᵢ))`, and `K_y ↦ op K_(-y)` for every `q : K`. -/
def antipodeOp (D : CartanDatum ι X Y) (q : K) :
    QuantizedEnvelopingAlgebra D q →ₐ[K] (QuantizedEnvelopingAlgebra D q)ᵐᵒᵖ :=
  lift
    { e i := MulOpposite.op (-(simpleKInv D q i * e D q i))
      f i := MulOpposite.op (-(f D q i * simpleK D q i))
      k y := MulOpposite.op (k D q (-y)), k_zero := by simp
      k_add y z := MulOpposite.unop_injective (by simp [← k_add, add_comm])
      k_mul_e i y := MulOpposite.unop_injective <| by
        simp only [MulOpposite.unop_mul, MulOpposite.unop_op, MulOpposite.unop_smul, neg_mul,
          mul_neg, mul_assoc]
        rw [e_mul_k i (-y), map_neg, neg_neg, mul_smul_comm, ← smul_neg,
          ← mul_assoc (simpleKInv D q i), simpleKInv_def, (commute_k _ _).eq, mul_assoc]
      k_mul_f i y := MulOpposite.unop_injective <| by
        simp only [MulOpposite.unop_mul, MulOpposite.unop_op, MulOpposite.unop_smul, neg_mul,
          mul_neg]
        rw [mul_assoc (f D q i), simpleK_def, (commute_k _ _).eq, ← mul_assoc (f D q i),
          f_mul_k i (-y), map_neg, smul_mul_assoc, ← smul_neg, mul_assoc]
      commutator_self := antipode_commutator_self, commutator_of_ne := antipode_commutator_of_ne,
      serre_e := antipode_serre_e, serre_f := antipode_serre_f }
@[simp] theorem antipodeOp_e (i : ι) :
    antipodeOp D q (e D q i) = MulOpposite.op (-(simpleKInv D q i * e D q i)) := lift_e _ i
@[simp] theorem antipodeOp_f (i : ι) :
    antipodeOp D q (f D q i) = MulOpposite.op (-(f D q i * simpleK D q i)) := lift_f _ i
@[simp] theorem antipodeOp_k (y : Y) : antipodeOp D q (k D q y) = MulOpposite.op (k D q (-y)) :=
  lift_k _ y
@[simp] theorem antipodeOp_simpleK (i : ι) :
    antipodeOp D q (simpleK D q i) = MulOpposite.op (simpleKInv D q i) := by
  simp [simpleK_def, simpleKInv_def]
@[simp] theorem antipodeOp_simpleKInv (i : ι) :
    antipodeOp D q (simpleKInv D q i) = MulOpposite.op (simpleK D q i) := by
  simp [simpleKInv_def, simpleK_def]
@[simp] theorem antipodeOp_normalizedE (i : ι) :
    antipodeOp D q (normalizedE D q i) =
      MulOpposite.op (-(((q ^ D.symmetrizer i) ^ 2)⁻¹ • e D q i)) := by
  apply MulOpposite.unop_injective
  simp only [normalizedE_def, map_mul, antipodeOp_simpleKInv, antipodeOp_e, MulOpposite.unop_mul,
    MulOpposite.unop_op, neg_mul]
  rw [simpleKInv_mul_e, D.cartan_apply_self, zpow_neg, zpow_ofNat, smul_mul_assoc, mul_assoc,
    simpleKInv_mul_simpleK, mul_one]
@[simp] theorem antipodeOp_normalizedF (i : ι) :
    antipodeOp D q (normalizedF D q i) =
      MulOpposite.op (-((q ^ D.symmetrizer i) ^ 2 • f D q i)) := by
  apply MulOpposite.unop_injective
  simp only [normalizedF_def, map_mul, antipodeOp_f, antipodeOp_simpleK, MulOpposite.unop_mul,
    MulOpposite.unop_op, mul_neg]
  rw [← mul_assoc, simpleKInv_mul_f, D.cartan_apply_self, zpow_ofNat, smul_mul_assoc, mul_assoc,
    simpleKInv_mul_simpleK, mul_one]
@[simp] theorem antipodeOp_comp_map (φ : D.Hom D') :
    (antipodeOp D' q).comp (map φ q) = (map φ q).op.comp (antipodeOp D q) := by
  ext <;> apply MulOpposite.unop_injective <;> simp
@[simp] theorem antipodeOp_map (φ : D.Hom D') (x : QuantizedEnvelopingAlgebra D q) :
    antipodeOp D' q (map φ q x) = MulOpposite.op (map φ q (antipodeOp D q x).unop) := by
  simpa only [AlgHom.comp_apply, AlgHom.op_apply_apply] using
    AlgHom.congr_fun (antipodeOp_comp_map φ) x
theorem antipodeOp_e_quantumDividedPower (i : ι) (n : ℕ) :
    antipodeOp D q (quantumDividedPower (q ^ D.symmetrizer i) (e D q i) n) =
      MulOpposite.op (((-1 : K) ^ n * (q ^ D.symmetrizer i) ^ (n * (n - 1))) •
        (simpleKInv D q i ^ n * quantumDividedPower (q ^ D.symmetrizer i) (e D q i) n)) := by
  rw [map_quantumDividedPower, antipodeOp_e, quantumDividedPower_op, quantumDividedPower_neg,
    quantumDividedPower_mul_of_mul_eq_sq_smul_mul
      (by simpa [D.cartan_apply_self] using e_mul_simpleKInv (D := D) (q := q) i i) n,
    smul_smul, MulOpposite.op_smul]
theorem antipodeOp_f_quantumDividedPower (i : ι) (n : ℕ) :
    antipodeOp D q (quantumDividedPower (q ^ D.symmetrizer i) (f D q i) n) =
      MulOpposite.op (((-1 : K) ^ n * (q ^ D.symmetrizer i)⁻¹ ^ (n * (n - 1))) •
        (quantumDividedPower (q ^ D.symmetrizer i) (f D q i) n * simpleK D q i ^ n)) := by
  rw [map_quantumDividedPower, antipodeOp_f, MulOpposite.op_neg, quantumDividedPower_neg,
    ← quantumDividedPower_inv, MulOpposite.op_mul,
    quantumDividedPower_mul_of_mul_eq_sq_smul_mul
      (by simpa [D.cartan_apply_self] using op_f_mul_op_simpleK (D := D) (q := q) i i) n,
    quantumDividedPower_inv, quantumDividedPower_op, ← MulOpposite.op_pow, ← MulOpposite.op_mul,
    ← MulOpposite.op_smul, ← MulOpposite.op_smul, smul_smul]

/-- The diagonal rescaling automorphism equal to the square of the antipode: scaling `Eᵢ` by
`qᵢ⁻²`, `Fᵢ` by `qᵢ²`, and fixing every `K_y` (reducing to the identity at `q = 0`). -/
noncomputable def antipodeSqEquiv (D : CartanDatum ι X Y) (q : K) :
    QuantizedEnvelopingAlgebra D q ≃ₐ[K] QuantizedEnvelopingAlgebra D q := by
  classical
  exact if hq : q = 0 then AlgEquiv.refl
  else rescaleAlgEquiv D q fun i => ((Units.mk0 (q ^ D.symmetrizer i) (pow_ne_zero _ hq)) ^ 2)⁻¹
@[simp] theorem antipodeSqEquiv_e (i : ι) :
    antipodeSqEquiv D q (e D q i) = ((q ^ D.symmetrizer i) ^ 2)⁻¹ • e D q i := by
  rcases eq_or_ne q 0 with rfl | hq <;> simp [antipodeSqEquiv, *]
@[simp] theorem antipodeSqEquiv_f (i : ι) :
    antipodeSqEquiv D q (f D q i) = (q ^ D.symmetrizer i) ^ 2 • f D q i := by
  rcases eq_or_ne q 0 with rfl | hq <;> simp [antipodeSqEquiv, *]
@[simp] theorem antipodeSqEquiv_k (y : Y) : antipodeSqEquiv D q (k D q y) = k D q y := by
  classical rw [antipodeSqEquiv]; split_ifs <;> simp
@[simp] theorem antipodeSqEquiv_simpleK (i : ι) :
    antipodeSqEquiv D q (simpleK D q i) = simpleK D q i := by simp [simpleK_def]
@[simp] theorem antipodeSqEquiv_simpleKInv (i : ι) :
    antipodeSqEquiv D q (simpleKInv D q i) = simpleKInv D q i := by simp [simpleKInv_def]
theorem opComm_antipodeOp_comp_antipodeOp :
    (AlgHom.opComm (antipodeOp D q)).comp (antipodeOp D q) = (antipodeSqEquiv D q).toAlgHom :=
  hom_ext (fun _ => by simp [← normalizedE_def]) (fun _ => by simp [← normalizedF_def])
    (fun _ => by simp)
theorem antipodeOp_bijective (D : CartanDatum ι X Y) (q : K) :
    Function.Bijective (antipodeOp D q) := by
  let T (x : QuantizedEnvelopingAlgebra D q) := (antipodeOp D q x).unop
  have hTT : T ∘ T = antipodeSqEquiv D q := funext fun x => by
    simpa only [Function.comp_apply, AlgHom.comp_apply, AlgHom.opComm_apply_apply,
      AlgEquiv.coe_toAlgHom] using AlgHom.congr_fun opComm_antipodeOp_comp_antipodeOp x
  have hcomp : Function.Bijective (T ∘ T) := hTT ▸ (antipodeSqEquiv D q).bijective
  have heq : (antipodeOp D q : _ → _) = MulOpposite.op ∘ T := funext fun _ => by simp [T]
  exact heq ▸ MulOpposite.opEquiv.bijective.comp
    ⟨Function.Injective.of_comp hcomp.1, Function.Surjective.of_comp hcomp.2⟩
/-- The antipode of `QuantizedEnvelopingAlgebra D q` as an algebra isomorphism onto the opposite
algebra, valid for every `q : K`. -/
noncomputable def antipodeEquiv (D : CartanDatum ι X Y) (q : K) :
    QuantizedEnvelopingAlgebra D q ≃ₐ[K] (QuantizedEnvelopingAlgebra D q)ᵐᵒᵖ :=
  AlgEquiv.ofBijective (antipodeOp D q) (antipodeOp_bijective D q)
@[simp] theorem antipodeEquiv_toAlgHom : (antipodeEquiv D q).toAlgHom = antipodeOp D q := (rfl)
@[simp] theorem antipodeEquiv_apply (x : QuantizedEnvelopingAlgebra D q) :
    antipodeEquiv D q x = antipodeOp D q x := (rfl)
theorem antipodeEquiv_symm_apply (x : (QuantizedEnvelopingAlgebra D q)ᵐᵒᵖ) :
    (antipodeEquiv D q).symm x =
      (antipodeOp D q ((antipodeSqEquiv D q).symm x.unop)).unop := by
  rw [AlgEquiv.symm_apply_eq, antipodeEquiv_apply, ← MulOpposite.unop_inj]
  simpa only [AlgHom.comp_apply, AlgHom.opComm_apply_apply, AlgEquiv.coe_toAlgHom,
    AlgEquiv.apply_symm_apply, MulOpposite.op_unop] using
    (AlgHom.congr_fun opComm_antipodeOp_comp_antipodeOp ((antipodeSqEquiv D q).symm x.unop)).symm
@[simp] theorem antipodeEquiv_symm_op_e (i : ι) :
    (antipodeEquiv D q).symm (MulOpposite.op (e D q i)) = -(e D q i * simpleKInv D q i) := by
  rw [AlgEquiv.symm_apply_eq, antipodeEquiv_apply, map_neg, map_mul, antipodeOp_e,
    antipodeOp_simpleKInv, ← MulOpposite.op_mul, ← MulOpposite.op_neg]; simp
@[simp] theorem antipodeEquiv_symm_op_f (i : ι) :
    (antipodeEquiv D q).symm (MulOpposite.op (f D q i)) = -(simpleK D q i * f D q i) := by
  rw [AlgEquiv.symm_apply_eq, antipodeEquiv_apply, map_neg, map_mul, antipodeOp_simpleK,
    antipodeOp_f, ← MulOpposite.op_mul, ← MulOpposite.op_neg]; simp [mul_assoc]
@[simp] theorem antipodeEquiv_symm_op_k (y : Y) :
    (antipodeEquiv D q).symm (MulOpposite.op (k D q y)) = k D q (-y) := by
  rw [AlgEquiv.symm_apply_eq]; simp
@[simp] theorem antipodeEquiv_symm_op_simpleK (i : ι) :
    (antipodeEquiv D q).symm (MulOpposite.op (simpleK D q i)) = simpleKInv D q i := by
  rw [AlgEquiv.symm_apply_eq]; simp
@[simp] theorem antipodeEquiv_symm_op_simpleKInv (i : ι) :
    (antipodeEquiv D q).symm (MulOpposite.op (simpleKInv D q i)) = simpleK D q i := by
  rw [AlgEquiv.symm_apply_eq]; simp

end Unconditional

section Hopf

variable {ι X Y X' Y' K : Type*} [AddCommGroup X] [AddCommGroup Y]
  [AddCommGroup X'] [AddCommGroup Y'] [Field K]
  {D : CartanDatum ι X Y} {D' : CartanDatum ι X' Y'} {q : K}

/-- Sufficient parameter condition under which `QuantizedEnvelopingAlgebra D q` admits the
Drinfeld–Jimbo coproduct: either `q = 0` or `[1 - aᵢⱼ]_(qᵢ)! ≠ 0` for all `i ≠ j`. -/
def HasComul (D : CartanDatum ι X Y) (q : K) : Prop :=
  q = 0 ∨ ∀ i j, i ≠ j → quantumFactorial (q ^ D.symmetrizer i) (D.serreLength i j) ≠ 0
theorem hasComul_iff :
    HasComul D q ↔
      q = 0 ∨ ∀ i j, i ≠ j → quantumFactorial (q ^ D.symmetrizer i) (D.serreLength i j) ≠ 0 :=
  Iff.rfl
theorem HasComul.zero (D : CartanDatum ι X Y) : HasComul D (0 : K) := Or.inl rfl
theorem HasComul.of_quantumFactorial_ne_zero
    (h : ∀ i j, i ≠ j → quantumFactorial (q ^ D.symmetrizer i) (D.serreLength i j) ≠ 0) :
    HasComul D q := Or.inr h
theorem _root_.TauCeti.IsGenericQuantumParameter.hasComul (hq : IsGenericQuantumParameter q) :
    HasComul D q :=
  .of_quantumFactorial_ne_zero fun i j _ =>
    quantumFactorial_ne_zero (hq.pow (D.symmetrizer_pos i)) (D.serreLength i j)
instance instFactHasComulOfGeneric (D : CartanDatum ι X Y) (q : K)
    [Fact (IsGenericQuantumParameter q)] : Fact (HasComul D q) :=
  ⟨(Fact.out : IsGenericQuantumParameter q).hasComul⟩
instance instFactHasComulOfSubsingleton [Subsingleton ι] (D : CartanDatum ι X Y) (q : K) :
    Fact (HasComul D q) :=
  ⟨.of_quantumFactorial_ne_zero fun i j hij => (hij (Subsingleton.elim i j)).elim⟩
theorem _root_.TauCeti.CartanDatum.Hom.hasComul_iff (φ : D.Hom D') :
    HasComul D' q ↔ HasComul D q := by
  simp only [QuantizedEnvelopingAlgebra.hasComul_iff, φ.symmetrizer_eq, φ.serreLength_eq]
theorem _root_.TauCeti.CartanDatum.Hom.fact_hasComul (φ : D.Hom D')
    [Fact (HasComul D q)] : Fact (HasComul D' q) := ⟨φ.hasComul_iff.mpr Fact.out⟩

private theorem comul_commutator_self (i : ι) :
    (e D q i ⊗ₜ[K] (1 : QuantizedEnvelopingAlgebra D q) + simpleK D q i ⊗ₜ[K] e D q i) *
        (f D q i ⊗ₜ[K] simpleKInv D q i + 1 ⊗ₜ[K] f D q i) -
      (f D q i ⊗ₜ[K] simpleKInv D q i + 1 ⊗ₜ[K] f D q i) *
        (e D q i ⊗ₜ[K] 1 + simpleK D q i ⊗ₜ[K] e D q i) =
      (q ^ D.symmetrizer i - (q ^ D.symmetrizer i)⁻¹)⁻¹ •
        (k D q (D.simpleTorus i) ⊗ₜ[K] k D q (D.simpleTorus i) -
          k D q (-D.simpleTorus i) ⊗ₜ[K] k D q (-D.simpleTorus i)) := by
  rcases eq_or_ne q 0 with rfl | hq; · simp [zero_pow (D.symmetrizer_pos i).ne']
  simp only [mul_add, add_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
  rw [simpleK_mul_f, e_mul_simpleKInv, D.cartan_apply_self]
  simp only [← TensorProduct.smul_tmul', TensorProduct.tmul_smul, smul_smul,
    ← zpow_add₀ (pow_ne_zero _ hq), add_neg_cancel, zpow_zero, one_smul]
  trans (e D q i * f D q i - f D q i * e D q i) ⊗ₜ[K] simpleKInv D q i +
      simpleK D q i ⊗ₜ[K] (e D q i * f D q i - f D q i * e D q i)
  · simp only [TensorProduct.sub_tmul, TensorProduct.tmul_sub]; abel
  · rw [e_mul_f_sub_f_mul_e_self, ← simpleK_def, ← simpleKInv_def]
    simp only [← TensorProduct.smul_tmul', TensorProduct.tmul_smul, TensorProduct.sub_tmul,
      TensorProduct.tmul_sub, ← smul_add]; congr 1; abel
private theorem comul_commutator_of_ne {i j : ι} (hij : i ≠ j) :
    (e D q i ⊗ₜ[K] (1 : QuantizedEnvelopingAlgebra D q) + simpleK D q i ⊗ₜ[K] e D q i) *
        (f D q j ⊗ₜ[K] simpleKInv D q j + 1 ⊗ₜ[K] f D q j) -
      (f D q j ⊗ₜ[K] simpleKInv D q j + 1 ⊗ₜ[K] f D q j) *
        (e D q i ⊗ₜ[K] 1 + simpleK D q i ⊗ₜ[K] e D q i) = 0 := by
  rcases eq_or_ne q 0 with rfl | hq; · simp
  simp only [mul_add, add_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
  rw [simpleK_mul_f, e_mul_simpleKInv, D.pow_symmetrizer_zpow_cartan q j i, e_mul_f_of_ne hij]
  simp only [← TensorProduct.smul_tmul', TensorProduct.tmul_smul, smul_smul,
    ← zpow_add₀ (pow_ne_zero _ hq), add_neg_cancel, zpow_zero, one_smul]; abel
private theorem comul_serre_e (hcomul : HasComul D q) {i j : ι} (hij : i ≠ j) :
    quantumSerre (q ^ D.symmetrizer i) (D.serreLength i j)
        (e D q i ⊗ₜ[K] (1 : QuantizedEnvelopingAlgebra D q) + simpleK D q i ⊗ₜ[K] e D q i)
        (e D q j ⊗ₜ[K] 1 + simpleK D q j ⊗ₜ[K] e D q j) = 0 := by
  rcases hcomul with rfl | hfac
  · simp [quantumSerre_zero_left _ (D.serreLength_ne_zero_of_ne hij)]
  have hcast := D.one_sub_natCast_serreLength_of_ne hij
  refine quantumSerre_add_eq_zero (hfac i j hij) ?_ ?_ ?_ ?_ ?_
  · simp [Algebra.TensorProduct.tmul_mul_tmul, simpleK_mul_e, TensorProduct.smul_tmul']
  · simp [Algebra.TensorProduct.tmul_mul_tmul, hcast, simpleK_mul_e, TensorProduct.smul_tmul']
  · rw [Algebra.TensorProduct.tmul_mul_tmul, simpleK_mul_e, D.pow_symmetrizer_zpow_cartan, ← hcast,
      mul_one, ← TensorProduct.smul_tmul', Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  · simpa only [map_quantumSerre, Algebra.TensorProduct.includeLeft_apply, map_zero] using
      congrArg (Algebra.TensorProduct.includeLeft : QuantizedEnvelopingAlgebra D q →ₐ[K]
        QuantizedEnvelopingAlgebra D q ⊗[K] QuantizedEnvelopingAlgebra D q)
        (quantumSerre_e_eq_zero_of_ne hij)
  · rw [quantumSerre_tmul_right _ _ (commute_simpleK i j), quantumSerre_e_eq_zero_of_ne hij,
      TensorProduct.tmul_zero]
private theorem comul_serre_f (hcomul : HasComul D q) {i j : ι} (hij : i ≠ j) :
    quantumSerre (q ^ D.symmetrizer i) (D.serreLength i j)
        (f D q i ⊗ₜ[K] simpleKInv D q i + 1 ⊗ₜ[K] f D q i)
        (f D q j ⊗ₜ[K] simpleKInv D q j + 1 ⊗ₜ[K] f D q j) = 0 := by
  rcases hcomul with rfl | hfac
  · simp [quantumSerre_zero_left _ (D.serreLength_ne_zero_of_ne hij)]
  have hcast := D.one_sub_natCast_serreLength_of_ne hij
  rw [add_comm (f D q i ⊗ₜ[K] simpleKInv D q i), add_comm (f D q j ⊗ₜ[K] simpleKInv D q j)]
  refine quantumSerre_add_eq_zero (hfac i j hij) ?_ ?_ ?_ ?_ ?_
  · simp [Algebra.TensorProduct.tmul_mul_tmul, simpleKInv_mul_f]
  · simp [Algebra.TensorProduct.tmul_mul_tmul, hcast, simpleKInv_mul_f]
  · rw [Algebra.TensorProduct.tmul_mul_tmul, simpleKInv_mul_f, D.pow_symmetrizer_zpow_cartan,
      ← hcast, mul_one, TensorProduct.tmul_smul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  · simpa only [map_quantumSerre, Algebra.TensorProduct.includeRight_apply, map_zero] using
      congrArg (Algebra.TensorProduct.includeRight : QuantizedEnvelopingAlgebra D q →ₐ[K]
        QuantizedEnvelopingAlgebra D q ⊗[K] QuantizedEnvelopingAlgebra D q)
        (quantumSerre_f_eq_zero_of_ne hij)
  · rw [quantumSerre_tmul_left _ _ (commute_simpleKInv i j), quantumSerre_f_eq_zero_of_ne hij,
      TensorProduct.zero_tmul]

/-- The Drinfeld–Jimbo coproduct `Δ(Eᵢ) = Eᵢ ⊗ 1 + Kᵢ ⊗ Eᵢ`, `Δ(Fᵢ) = Fᵢ ⊗ Kᵢ⁻¹ + 1 ⊗ Fᵢ`,
`Δ(K_y) = K_y ⊗ K_y` under `[Fact (HasComul D q)]`. -/
noncomputable def comul (D : CartanDatum ι X Y) (q : K) [Fact (HasComul D q)] :
    QuantizedEnvelopingAlgebra D q →ₐ[K]
      QuantizedEnvelopingAlgebra D q ⊗[K] QuantizedEnvelopingAlgebra D q :=
  lift
    { e i := e D q i ⊗ₜ[K] 1 + simpleK D q i ⊗ₜ[K] e D q i
      f i := f D q i ⊗ₜ[K] simpleKInv D q i + 1 ⊗ₜ[K] f D q i
      k y := k D q y ⊗ₜ[K] k D q y, k_zero := by simp [Algebra.TensorProduct.one_def]
      k_add y z := by simp [k_add, Algebra.TensorProduct.tmul_mul_tmul]
      k_mul_e i y := by
        simp only [mul_add, add_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul,
          k_mul_e, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul, smul_add]
        rw [(commute_k_simpleK y i).eq]
      k_mul_f i y := by
        simp only [mul_add, add_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul,
          k_mul_f, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul, smul_add]
        rw [(commute_k_simpleKInv y i).eq]
      commutator_self := comul_commutator_self, commutator_of_ne := comul_commutator_of_ne,
      serre_e := comul_serre_e Fact.out, serre_f := comul_serre_f Fact.out }
@[local simp] private theorem comul_eAux (D : CartanDatum ι X Y) (q : K) [Fact (HasComul D q)]
    (i : ι) : comul D q (e D q i) = e D q i ⊗ₜ[K] 1 + simpleK D q i ⊗ₜ[K] e D q i := lift_e _ i
@[local simp] private theorem comul_fAux (D : CartanDatum ι X Y) (q : K) [Fact (HasComul D q)]
    (i : ι) : comul D q (f D q i) = f D q i ⊗ₜ[K] simpleKInv D q i + 1 ⊗ₜ[K] f D q i := lift_f _ i
@[local simp] private theorem comul_kAux (D : CartanDatum ι X Y) (q : K) [Fact (HasComul D q)]
    (y : Y) : comul D q (k D q y) = k D q y ⊗ₜ[K] k D q y := lift_k _ y

noncomputable instance instBialgebra (D : CartanDatum ι X Y) (q : K) [Fact (HasComul D q)] :
    Bialgebra K (QuantizedEnvelopingAlgebra D q) :=
  Bialgebra.ofAlgHom (comul D q) (counit D q)
    (by ext <;> simp [simpleK_def, simpleKInv_def, TensorProduct.tmul_add, TensorProduct.add_tmul,
      add_assoc, Algebra.TensorProduct.one_def])
    (by ext <;> simp [simpleK_def, simpleKInv_def])
    (by ext <;> simp [simpleK_def, simpleKInv_def])
noncomputable instance instHopfAlgebra (D : CartanDatum ι X Y) (q : K) [Fact (HasComul D q)] :
    HopfAlgebra K (QuantizedEnvelopingAlgebra D q) :=
  HopfAlgebra.ofAntipodeOfAdjoin (antipodeOp D q) (adjoin_range_generator D q)
    (by rintro _ ⟨g, rfl⟩; cases g <;>
      simp [Coalgebra.comul, Coalgebra.counit, simpleK_def, simpleKInv_def, mul_assoc])
    (by rintro _ ⟨g, rfl⟩; cases g <;>
      simp [Coalgebra.comul, Coalgebra.counit, simpleK_def, simpleKInv_def, ← mul_assoc (k D q _)])

section Simp

variable [Fact (HasComul D q)]

@[simp] theorem comul_apply (x : QuantizedEnvelopingAlgebra D q) :
    comul D q x = Coalgebra.comul (R := K) x := (rfl)
@[simp] theorem counit_apply (x : QuantizedEnvelopingAlgebra D q) :
    counit D q x = Coalgebra.counit (R := K) x := (rfl)
@[simp] theorem antipodeOp_apply (x : QuantizedEnvelopingAlgebra D q) :
    antipodeOp D q x = MulOpposite.op (HopfAlgebra.antipode K x) := (rfl)
@[simp] theorem comul_e (i : ι) :
    Coalgebra.comul (R := K) (e D q i) = e D q i ⊗ₜ[K] 1 + simpleK D q i ⊗ₜ[K] e D q i :=
  comul_eAux D q i
@[simp] theorem comul_f (i : ι) :
    Coalgebra.comul (R := K) (f D q i) = f D q i ⊗ₜ[K] simpleKInv D q i + 1 ⊗ₜ[K] f D q i :=
  comul_fAux D q i
@[simp] theorem comul_k (y : Y) :
    Coalgebra.comul (R := K) (k D q y) = k D q y ⊗ₜ[K] k D q y := comul_kAux D q y
@[simp] theorem comul_simpleK (i : ι) :
    Coalgebra.comul (R := K) (simpleK D q i) = simpleK D q i ⊗ₜ[K] simpleK D q i := by
  simp [simpleK_def]
@[simp] theorem comul_simpleKInv (i : ι) :
    Coalgebra.comul (R := K) (simpleKInv D q i) = simpleKInv D q i ⊗ₜ[K] simpleKInv D q i := by
  simp [simpleKInv_def]
theorem isGroupLikeElem_k (y : Y) : IsGroupLikeElem K (k D q y) := ⟨counit_apply_k y, comul_k y⟩
@[simp] theorem counit_e (i : ι) : Coalgebra.counit (R := K) (e D q i) = 0 := counit_apply_e i
@[simp] theorem counit_f (i : ι) : Coalgebra.counit (R := K) (f D q i) = 0 := counit_apply_f i
@[simp] theorem counit_k (y : Y) : Coalgebra.counit (R := K) (k D q y) = 1 := counit_apply_k y
@[simp] theorem counit_simpleK (i : ι) : Coalgebra.counit (R := K) (simpleK D q i) = 1 :=
  counit_apply_simpleK i
@[simp] theorem counit_simpleKInv (i : ι) : Coalgebra.counit (R := K) (simpleKInv D q i) = 1 :=
  counit_apply_simpleKInv i
@[simp] theorem counit_normalizedE (i : ι) : Coalgebra.counit (R := K) (normalizedE D q i) = 0 :=
  counit_apply_normalizedE i
@[simp] theorem counit_normalizedF (i : ι) : Coalgebra.counit (R := K) (normalizedF D q i) = 0 :=
  counit_apply_normalizedF i
@[simp] theorem antipode_e (i : ι) :
    HopfAlgebra.antipode K (e D q i) = -(simpleKInv D q i * e D q i) :=
  MulOpposite.op_injective ((antipodeOp_apply (e D q i)).symm.trans (antipodeOp_e i))
@[simp] theorem antipode_f (i : ι) :
    HopfAlgebra.antipode K (f D q i) = -(f D q i * simpleK D q i) :=
  MulOpposite.op_injective ((antipodeOp_apply (f D q i)).symm.trans (antipodeOp_f i))
@[simp] theorem antipode_k (y : Y) : HopfAlgebra.antipode K (k D q y) = k D q (-y) :=
  MulOpposite.op_injective ((antipodeOp_apply (k D q y)).symm.trans (antipodeOp_k y))
@[simp] theorem antipode_simpleK (i : ι) :
    HopfAlgebra.antipode K (simpleK D q i) = simpleKInv D q i := by
  simp [simpleK_def, simpleKInv_def]
@[simp] theorem antipode_simpleKInv (i : ι) :
    HopfAlgebra.antipode K (simpleKInv D q i) = simpleK D q i := by
  simp [simpleKInv_def, simpleK_def]
@[simp] theorem antipode_normalizedE (i : ι) :
    HopfAlgebra.antipode K (normalizedE D q i) = -(((q ^ D.symmetrizer i) ^ 2)⁻¹ • e D q i) :=
  MulOpposite.op_injective ((antipodeOp_apply _).symm.trans (antipodeOp_normalizedE i))
@[simp] theorem antipode_normalizedF (i : ι) :
    HopfAlgebra.antipode K (normalizedF D q i) = -((q ^ D.symmetrizer i) ^ 2 • f D q i) :=
  MulOpposite.op_injective ((antipodeOp_apply _).symm.trans (antipodeOp_normalizedF i))
@[simp] theorem comul_normalizedE (i : ι) :
    Coalgebra.comul (R := K) (normalizedE D q i) =
      normalizedE D q i ⊗ₜ[K] simpleKInv D q i + 1 ⊗ₜ[K] normalizedE D q i := by
  rw [← comul_apply, normalizedE_def, map_mul, comul_apply, comul_apply, comul_simpleKInv, comul_e,
    mul_add, Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
    simpleKInv_mul_simpleK, ← normalizedE_def]
@[simp] theorem comul_normalizedF (i : ι) :
    Coalgebra.comul (R := K) (normalizedF D q i) =
      normalizedF D q i ⊗ₜ[K] 1 + simpleK D q i ⊗ₜ[K] normalizedF D q i := by
  rw [← comul_apply, normalizedF_def, map_mul, comul_apply, comul_apply, comul_f, comul_simpleK,
    add_mul, Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
    simpleKInv_mul_simpleK, ← normalizedF_def]
/-- **Divided-power coproduct of `Eᵢ`** when `[n]_(qᵢ)! ≠ 0`. -/
theorem comul_e_quantumDividedPower (i : ι) {n : ℕ}
    (hn : quantumFactorial (q ^ D.symmetrizer i) n ≠ 0) :
    Coalgebra.comul (R := K) (quantumDividedPower (q ^ D.symmetrizer i) (e D q i) n) =
      ∑ a ∈ Finset.range (n + 1),
        (q ^ D.symmetrizer i) ^ (a * (n - a)) •
          ((quantumDividedPower (q ^ D.symmetrizer i) (e D q i) a * simpleK D q i ^ (n - a)) ⊗ₜ[K]
            quantumDividedPower (q ^ D.symmetrizer i) (e D q i) (n - a)) := by
  rw [← comul_apply, map_quantumDividedPower, comul_apply, comul_e,
    quantumDividedPower_add
      (by simp [Algebra.TensorProduct.tmul_mul_tmul, simpleK_mul_e, TensorProduct.smul_tmul']) hn]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [quantumDividedPower_tmul_left, quantumDividedPower_tmul_right, one_pow,
    Algebra.TensorProduct.tmul_mul_tmul, one_mul]
/-- **Divided-power coproduct of `Fᵢ`** when `[n]_(qᵢ)! ≠ 0`. -/
theorem comul_f_quantumDividedPower (i : ι) {n : ℕ}
    (hn : quantumFactorial (q ^ D.symmetrizer i) n ≠ 0) :
    Coalgebra.comul (R := K) (quantumDividedPower (q ^ D.symmetrizer i) (f D q i) n) =
      ∑ a ∈ Finset.range (n + 1),
        (q ^ D.symmetrizer i) ^ (a * (n - a)) •
          (quantumDividedPower (q ^ D.symmetrizer i) (f D q i) a ⊗ₜ[K]
            (quantumDividedPower (q ^ D.symmetrizer i) (f D q i) (n - a) *
              simpleKInv D q i ^ a)) := by
  rw [← comul_apply, map_quantumDividedPower, comul_apply, comul_f,
    add_comm (f D q i ⊗ₜ[K] simpleKInv D q i),
    quantumDividedPower_add (by simp [Algebra.TensorProduct.tmul_mul_tmul, simpleKInv_mul_f]) hn,
    ← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun a ha => ?_
  have han : a ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
  rw [Nat.add_sub_cancel, Nat.sub_sub_self han, mul_comm (n - a) a,
    quantumDividedPower_tmul_right, quantumDividedPower_tmul_left, one_pow,
    Algebra.TensorProduct.tmul_mul_tmul, one_mul]
theorem antipode_e_quantumDividedPower (i : ι) (n : ℕ) :
    HopfAlgebra.antipode K (quantumDividedPower (q ^ D.symmetrizer i) (e D q i) n) =
      ((-1 : K) ^ n * (q ^ D.symmetrizer i) ^ (n * (n - 1))) •
        (simpleKInv D q i ^ n * quantumDividedPower (q ^ D.symmetrizer i) (e D q i) n) :=
  MulOpposite.op_injective <| (antipodeOp_apply _).symm.trans (antipodeOp_e_quantumDividedPower i n)
theorem antipode_f_quantumDividedPower (i : ι) (n : ℕ) :
    HopfAlgebra.antipode K (quantumDividedPower (q ^ D.symmetrizer i) (f D q i) n) =
      ((-1 : K) ^ n * (q ^ D.symmetrizer i)⁻¹ ^ (n * (n - 1))) •
        (quantumDividedPower (q ^ D.symmetrizer i) (f D q i) n * simpleK D q i ^ n) :=
  MulOpposite.op_injective <| (antipodeOp_apply _).symm.trans (antipodeOp_f_quantumDividedPower i n)
theorem antipode_antipode (x : QuantizedEnvelopingAlgebra D q) :
    HopfAlgebra.antipode K (HopfAlgebra.antipode K x) = antipodeSqEquiv D q x := by
  simpa only [AlgHom.comp_apply, AlgHom.opComm_apply_apply, AlgEquiv.coe_toAlgHom,
    antipodeOp_apply, MulOpposite.unop_op] using
    AlgHom.congr_fun opComm_antipodeOp_comp_antipodeOp x
theorem antipode_antipode_e (i : ι) :
    HopfAlgebra.antipode K (HopfAlgebra.antipode K (e D q i)) =
      ((q ^ D.symmetrizer i) ^ 2)⁻¹ • e D q i := by rw [antipode_antipode, antipodeSqEquiv_e]
theorem antipode_antipode_f (i : ι) :
    HopfAlgebra.antipode K (HopfAlgebra.antipode K (f D q i)) =
      (q ^ D.symmetrizer i) ^ 2 • f D q i := by rw [antipode_antipode, antipodeSqEquiv_f]
theorem antipode_antipode_k (y : Y) :
    HopfAlgebra.antipode K (HopfAlgebra.antipode K (k D q y)) = k D q y := by simp
theorem antipode_bijective (D : CartanDatum ι X Y) (q : K) [Fact (HasComul D q)] :
    Function.Bijective (HopfAlgebra.antipode K :
      QuantizedEnvelopingAlgebra D q →ₗ[K] QuantizedEnvelopingAlgebra D q) := by
  simpa only [Function.comp_def, antipodeOp_apply, MulOpposite.unop_op] using
    MulOpposite.unop_bijective.comp (antipodeOp_bijective D q)
@[simp] theorem inverseAntipode_e (i : ι) :
    TauCeti.HopfAlgebra.inverseAntipode (antipode_bijective D q) (e D q i) =
      -(e D q i * simpleKInv D q i) :=
  (antipode_bijective D q).injective (by simp [HopfAlgebra.antipode_mul_antidistrib])
@[simp] theorem inverseAntipode_f (i : ι) :
    TauCeti.HopfAlgebra.inverseAntipode (antipode_bijective D q) (f D q i) =
      -(simpleK D q i * f D q i) :=
  (antipode_bijective D q).injective (by simp [HopfAlgebra.antipode_mul_antidistrib, mul_assoc])
@[simp] theorem inverseAntipode_k (y : Y) :
    TauCeti.HopfAlgebra.inverseAntipode (antipode_bijective D q) (k D q y) = k D q (-y) :=
  (antipode_bijective D q).injective (by simp)
@[simp] theorem inverseAntipode_simpleK (i : ι) :
    TauCeti.HopfAlgebra.inverseAntipode (antipode_bijective D q) (simpleK D q i) =
      simpleKInv D q i := (antipode_bijective D q).injective (by simp)
@[simp] theorem inverseAntipode_simpleKInv (i : ι) :
    TauCeti.HopfAlgebra.inverseAntipode (antipode_bijective D q) (simpleKInv D q i) =
      simpleK D q i := (antipode_bijective D q).injective (by simp)

/-- A morphism of Cartan data `φ : D.Hom D'` induces a `K`-bialgebra morphism
`QuantizedEnvelopingAlgebra D q →ₐc[K] QuantizedEnvelopingAlgebra D' q`. -/
noncomputable def mapBialgHom (φ : D.Hom D') (q : K) [Fact (HasComul D q)] [Fact (HasComul D' q)] :
    QuantizedEnvelopingAlgebra D q →ₐc[K] QuantizedEnvelopingAlgebra D' q :=
  BialgHom.ofAlgHom (map φ q) (by ext <;> simp) (by ext <;> simp)
@[simp] theorem coe_mapBialgHom (φ : D.Hom D') [Fact (HasComul D' q)] :
    (mapBialgHom φ q : QuantizedEnvelopingAlgebra D q →ₐ[K] QuantizedEnvelopingAlgebra D' q) =
      map φ q := (rfl)
@[simp] theorem mapBialgHom_apply (φ : D.Hom D') [Fact (HasComul D' q)]
    (x : QuantizedEnvelopingAlgebra D q) : mapBialgHom φ q x = map φ q x := (rfl)
@[simp] theorem mapBialgHom_id (D : CartanDatum ι X Y) (q : K) [Fact (HasComul D q)] :
    mapBialgHom (CartanDatum.Hom.id D) q = BialgHom.id K (QuantizedEnvelopingAlgebra D q) := by
  ext; simp
theorem mapBialgHom_comp {X'' Y'' : Type*} [AddCommGroup X''] [AddCommGroup Y'']
    {D'' : CartanDatum ι X'' Y''} (ψ : D'.Hom D'') (φ : D.Hom D') (q : K) [Fact (HasComul D q)]
    [Fact (HasComul D' q)] [Fact (HasComul D'' q)] :
    mapBialgHom (ψ.comp φ) q = (mapBialgHom ψ q).comp (mapBialgHom φ q) := by ext; simp [map_comp]
@[simp] theorem counit_map (φ : D.Hom D') [Fact (HasComul D' q)]
    (x : QuantizedEnvelopingAlgebra D q) :
    Coalgebra.counit (R := K) (map φ q x) = Coalgebra.counit (R := K) x := by
  rw [← counit_apply, ← counit_apply, counit_apply_map]
theorem comul_map (φ : D.Hom D') [Fact (HasComul D' q)] (x : QuantizedEnvelopingAlgebra D q) :
    Coalgebra.comul (R := K) (map φ q x) =
      Algebra.TensorProduct.map (map φ q) (map φ q) (Coalgebra.comul (R := K) x) := by
  simpa only [AlgHom.comp_apply, Bialgebra.comulAlgHom_apply, coe_mapBialgHom] using
    (AlgHom.congr_fun (BialgHom.map_comp_comulAlgHom (mapBialgHom φ q)) x).symm
theorem antipode_map (φ : D.Hom D') [Fact (HasComul D' q)] (x : QuantizedEnvelopingAlgebra D q) :
    HopfAlgebra.antipode K (map φ q x) = map φ q (HopfAlgebra.antipode K x) := by
  simpa only [mapBialgHom_apply] using (BialgHomClass.map_antipode (mapBialgHom φ q) x).symm

end Simp
end Hopf
end TauCeti.QuantizedEnvelopingAlgebra
