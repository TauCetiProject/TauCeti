/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.Action.End
public import Mathlib.Algebra.SkewMonoidAlgebra.Basic
public import Mathlib.RingTheory.WittVector.Complete

/-!
# The Dieudonné ring

Let `k` be a perfect ring of characteristic `p`, let `W = W(k)` be its ring of Witt vectors and
let `σ` be the Frobenius automorphism of `W`. The *Dieudonné ring* `E = D_k` is the ring
generated over `W` by two elements `F` and `V` subject to
`F ξ = σ(ξ) F`, `V σ(ξ) = ξ V` (for `ξ ∈ W`) and `F V = V F = p`.
Left `E`-modules are the Dieudonné modules which classify finite commutative `p`-group schemes
and `p`-divisible groups over a perfect field.

We construct `E` concretely inside the skew Laurent polynomial ring `W[F, F⁻¹; σ]`, as the
subring of those `∑ aₙ Fⁿ` with `pⁿ ∣ a₋ₙ` for every `n ≥ 0`, with `V = p F⁻¹`.
Since `p` is a non-zero-divisor on `W`, this ring is spanned freely as a left `W`-module by
`…, V², V, 1, F, F², …`.

## Main definitions and results

* `TauCeti.DieudonneRing p k`: the Dieudonné ring of `k`.
* `TauCeti.DieudonneRing.C`, `TauCeti.DieudonneRing.F`, `TauCeti.DieudonneRing.V`: the
  scalars and the two generators.
* `TauCeti.DieudonneRing.F_mul_C`, `TauCeti.DieudonneRing.V_mul_C_frobenius`,
  `TauCeti.DieudonneRing.F_mul_V`, `TauCeti.DieudonneRing.V_mul_F`: the defining relations.
* `TauCeti.DieudonneRing.val`: the embedding into `W[F, F⁻¹; σ]`, with image
  `TauCeti.DieudonneRing.subring` (`TauCeti.DieudonneRing.mem_subring`,
  `TauCeti.DieudonneRing.val_mem`, `TauCeti.DieudonneRing.mk`).
* `TauCeti.DieudonneRing.basis`: the basis `n ↦ Fⁿ` (`n ≥ 0`), `n ↦ V⁻ⁿ` (`n ≤ 0`) of `E` as a
  free left `W`-module; `TauCeti.DieudonneRing.coeff_val` reads its coordinates off `val`.
* `TauCeti.DieudonneRing.lift`: the universal property: a ring homomorphism `g : W → R` with
  elements `f v : R` satisfying the defining relations extends uniquely
  (`TauCeti.DieudonneRing.ringHom_ext`) to a ring homomorphism `E → R`.
* `TauCeti.DieudonneRing.induction_on`: `E` is generated as a ring by the scalars, `F` and `V`.

## References

* R. Pink, *Finite group schemes*, lecture course WS 2004/05, ETH Zürich lecture notes,
  §23, Definition, p. 54, <https://people.math.ethz.ch/~pink/ftp/FGS/CompleteNotes.pdf>.
* C.-F. Yu, *Introduction to Dieudonné modules and supersingular abelian varieties revisited*,
  arXiv:2603.11506, §2.1, Definition 1.
-/

public section

noncomputable section

open WittVector

namespace TauCeti

variable (p : ℕ) [Fact p.Prime] (k : Type*) [CommRing k] [CharP k p] [PerfectRing k p]

local notation "𝕎" => WittVector p

namespace DieudonneRing

/-- The action of `Multiplicative ℤ` on `𝕎 k` in which `ofAdd n` acts by the `n`-th power of
the Frobenius automorphism `σ`; the integer analogue of `RingHom.powersMulSemiringAction`. It is
not an instance; it is the twist defining the skew Laurent polynomial ring `𝕎 k [F, F⁻¹; σ]`. -/
abbrev frobeniusZPowAction : MulSemiringAction (Multiplicative ℤ) (𝕎 k) :=
  MulSemiringAction.compHom (𝕎 k) (zpowersHom (RingAut (𝕎 k)) (frobeniusEquiv p k))

attribute [local instance] frobeniusZPowAction

/-- The skew Laurent polynomial ring `𝕎 k [F, F⁻¹; σ]`, in which `F ξ = σ(ξ) F`. -/
abbrev SkewLaurent := SkewMonoidAlgebra (𝕎 k) (Multiplicative ℤ)

variable {p k}

/-- In `TauCeti.DieudonneRing.frobeniusZPowAction`, `ofAdd n` acts by `σⁿ`. -/
theorem frobeniusZPowAction_smul_def (a : Multiplicative ℤ) (ξ : 𝕎 k) :
    a • ξ = (frobeniusEquiv p k ^ a.toAdd) ξ :=
  rfl

private lemma zpow_frobeniusEquiv_dvd (m : ℤ) {ξ : 𝕎 k} {j : ℕ} (h : (p : 𝕎 k) ^ j ∣ ξ) :
    (p : 𝕎 k) ^ j ∣ (frobeniusEquiv p k ^ m) ξ := by
  simpa using map_dvd (frobeniusEquiv p k ^ m) h

variable (p k) in
/-- The subring of `𝕎 k [F, F⁻¹; σ]` of those `∑ aₙ Fⁿ` with `pⁿ ∣ a₋ₙ` for `n ≥ 0`; it is the
underlying ring of the Dieudonné ring, with `V = p F⁻¹`. -/
def subring : Subring (SkewLaurent p k) where
  carrier := {f | ∀ a, (p : 𝕎 k) ^ (-a.toAdd).toNat ∣ f.coeff a}
  mul_mem' {f g} hf hg a := by
    classical
    rw [SkewMonoidAlgebra.coeff_mul]
    refine Finset.dvd_sum fun b _ ↦ Finset.dvd_sum fun c _ ↦ ?_
    dsimp only
    split_ifs with h
    · subst h
      have h := mul_dvd_mul (hf b) (zpow_frobeniusEquiv_dvd b.toAdd (hg c))
      rw [← pow_add, ← frobeniusZPowAction_smul_def] at h
      refine (pow_dvd_pow _ ?_).trans h
      simp only [toAdd_mul]
      omega
    · exact dvd_zero _
  one_mem' a := by
    classical
    rw [SkewMonoidAlgebra.coeff_one, Finsupp.single_apply]
    split_ifs with h
    · subst h
      simp
    · exact dvd_zero _
  add_mem' hf hg a := by
    rw [SkewMonoidAlgebra.coeff_add, Finsupp.add_apply]
    exact dvd_add (hf a) (hg a)
  zero_mem' a := by simp
  neg_mem' hf a := by
    rw [SkewMonoidAlgebra.coeff_neg, Finsupp.neg_apply]
    exact (hf a).neg_right

/-- Membership in `TauCeti.DieudonneRing.subring`: the coefficient of `F⁻ⁿ` is divisible by `pⁿ`
for every `n ≥ 0`. -/
theorem mem_subring {x : SkewLaurent p k} :
    x ∈ subring p k ↔ ∀ a, (p : 𝕎 k) ^ (-a.toAdd).toNat ∣ x.coeff a :=
  Iff.rfl

private lemma single_mem_subring (n : ℤ) {ξ : 𝕎 k} (h : (p : 𝕎 k) ^ (-n).toNat ∣ ξ) :
    SkewMonoidAlgebra.single (Multiplicative.ofAdd n) ξ ∈ subring p k := by
  classical
  refine mem_subring.2 fun a ↦ ?_
  rw [SkewMonoidAlgebra.coeff_single, Finsupp.single_apply]
  split_ifs with ha
  · subst ha
    simpa using h
  · exact dvd_zero _

end DieudonneRing

open DieudonneRing in
/-- The **Dieudonné ring** `D_k` of a perfect ring `k` of characteristic `p`: the ring generated
over the Witt vectors `𝕎 k` by elements `F` and `V` subject to `F ξ = σ(ξ) F`, `V σ(ξ) = ξ V` and
`F V = V F = p`, where `σ` is the Frobenius of `𝕎 k`. -/
def DieudonneRing : Type _ :=
  subring p k

namespace DieudonneRing

attribute [local instance] frobeniusZPowAction

instance : Ring (DieudonneRing p k) :=
  inferInstanceAs (Ring (subring p k))

variable {p k}

/-- The embedding of the Dieudonné ring into the skew Laurent polynomial ring `𝕎 k [F, F⁻¹; σ]`;
its image is `TauCeti.DieudonneRing.subring`. -/
def val : DieudonneRing p k →+* SkewLaurent p k :=
  (subring p k).subtype

theorem val_injective : Function.Injective (val : DieudonneRing p k → SkewLaurent p k) :=
  Subtype.val_injective

@[simp]
theorem val_inj {x y : DieudonneRing p k} : val x = val y ↔ x = y :=
  val_injective.eq_iff

/-- An element of the Dieudonné ring from a skew Laurent polynomial in the subring. -/
def mk (x : SkewLaurent p k) (hx : x ∈ subring p k) : DieudonneRing p k :=
  (⟨x, hx⟩ : subring p k)

@[simp]
theorem val_mk (x : SkewLaurent p k) (hx : x ∈ subring p k) : val (mk x hx) = x := by
  rfl

theorem val_mem (x : DieudonneRing p k) : val x ∈ subring p k :=
  Subtype.prop (p := (· ∈ subring p k)) x

@[simp]
theorem mk_val (x : DieudonneRing p k) : mk (val x) (val_mem x) = x :=
  val_injective (val_mk _ _)

variable (p k) in
/-- The Witt vectors `𝕎 k` as the scalars of the Dieudonné ring. -/
def C : 𝕎 k →+* DieudonneRing p k :=
  SkewMonoidAlgebra.singleOneRingHom.codRestrict (subring p k) fun ξ ↦
    single_mem_subring 0 (by simp)

@[simp]
theorem val_C (ξ : 𝕎 k) : val (C p k ξ) = SkewMonoidAlgebra.single 1 ξ := by
  rfl

/-- The scalars embed into the Dieudonné ring. -/
theorem C_injective : Function.Injective (C p k) := fun _ _ h ↦
  SkewMonoidAlgebra.single_injective _ (congrArg val h)

variable (p k) in
/-- The Frobenius generator `F` of the Dieudonné ring. -/
def F : DieudonneRing p k :=
  mk (SkewMonoidAlgebra.single (Multiplicative.ofAdd 1) 1) (single_mem_subring 1 (by simp))

variable (p k) in
/-- The Verschiebung generator `V` of the Dieudonné ring. -/
def V : DieudonneRing p k :=
  mk (SkewMonoidAlgebra.single (Multiplicative.ofAdd (-1)) (p : 𝕎 k))
    (single_mem_subring (-1) (by simp))

@[simp]
theorem val_F : val (F p k) = SkewMonoidAlgebra.single (Multiplicative.ofAdd 1) 1 := by
  rfl

@[simp]
theorem val_V :
    val (V p k) = SkewMonoidAlgebra.single (Multiplicative.ofAdd (-1)) (p : 𝕎 k) := by
  rfl

private lemma frobeniusEquiv_inv_frobenius (ξ : 𝕎 k) :
    (frobeniusEquiv p k)⁻¹ (frobenius ξ) = ξ :=
  (frobeniusEquiv p k).symm_apply_apply ξ

private lemma frobenius_frobeniusEquiv_inv (ξ : 𝕎 k) :
    frobenius ((frobeniusEquiv p k)⁻¹ ξ) = ξ :=
  (frobeniusEquiv p k).apply_symm_apply ξ

/-- `F ξ = σ(ξ) F`. -/
theorem F_mul_C (ξ : 𝕎 k) : F p k * C p k ξ = C p k (frobenius ξ) * F p k := by
  apply val_injective
  simp [frobeniusZPowAction_smul_def]

/-- `V σ(ξ) = ξ V`. -/
theorem V_mul_C_frobenius (ξ : 𝕎 k) : V p k * C p k (frobenius ξ) = C p k ξ * V p k := by
  apply val_injective
  simp only [map_mul, val_V, val_C, SkewMonoidAlgebra.single_mul_single,
    frobeniusZPowAction_smul_def, toAdd_ofAdd, zpow_neg, zpow_one, frobeniusEquiv_inv_frobenius,
    one_mul, one_smul, mul_comm]

/-- `F V = p`. -/
@[simp]
theorem F_mul_V : F p k * V p k = p := by
  apply val_injective
  rw [map_mul, map_natCast, val_F, val_V, SkewMonoidAlgebra.single_mul_single,
    ← SkewMonoidAlgebra.single_nat]
  congr 1
  simp [frobeniusZPowAction_smul_def]

/-- `V F = p`. -/
@[simp]
theorem V_mul_F : V p k * F p k = p := by
  apply val_injective
  rw [map_mul, map_natCast, val_F, val_V, SkewMonoidAlgebra.single_mul_single,
    ← SkewMonoidAlgebra.single_nat]
  congr 1
  simp

/-! ### Words in two generators satisfying the Dieudonné relations -/

section Words

variable {R : Type*} [Ring R]

/-- The word `fⁿ` for `n ≥ 0` and `v⁻ⁿ` for `n < 0`; for `f = F` and `v = V` these are the
basis vectors of the Dieudonné ring. -/
private def zpowFV (f v : R) (n : ℤ) : R :=
  if 0 ≤ n then f ^ n.toNat else v ^ (-n).toNat

private lemma zpowFV_natCast (f v : R) (n : ℕ) : zpowFV f v n = f ^ n := by
  simp [zpowFV]

private lemma zpowFV_neg_natCast (f v : R) (n : ℕ) : zpowFV f v (-n) = v ^ n := by
  unfold zpowFV
  split_ifs with h
  · obtain rfl : n = 0 := by omega
    simp
  · simp

private lemma zpowFV_zero (f v : R) : zpowFV f v 0 = 1 := by
  simpa using zpowFV_natCast f v 0

private lemma zpowFV_one (f v : R) : zpowFV f v 1 = f := by
  simpa using zpowFV_natCast f v 1

private lemma zpowFV_neg_one (f v : R) : zpowFV f v (-1) = v := by
  simpa using zpowFV_neg_natCast f v 1

private lemma map_zpowFV {S : Type*} [Ring S] (g : R →+* S) (f v : R) (n : ℤ) :
    g (zpowFV f v n) = zpowFV (g f) (g v) n := by
  unfold zpowFV
  split_ifs <;> simp

omit [Fact p.Prime] in
/-- If `x y = y x = p`, then `xᵃ yᵃ⁺ᶜ = pᵃ yᶜ`. -/
private lemma pow_mul_pow_add {x y : R} (hxy : x * y = p) (hyx : y * x = p) (a c : ℕ) :
    x ^ a * y ^ (a + c) = (p : R) ^ a * y ^ c := by
  rw [pow_add, ← mul_assoc, ← (show Commute x y from hxy.trans hyx.symm).mul_pow, hxy]

omit [Fact p.Prime] in
/-- If `x y = y x = p`, then `xᶜ⁺ᵇ yᵇ = pᵇ xᶜ`. -/
private lemma pow_add_mul_pow {x y : R} (hxy : x * y = p) (hyx : y * x = p) (b c : ℕ) :
    x ^ (c + b) * y ^ b = (p : R) ^ b * x ^ c := by
  rw [pow_add, mul_assoc, ← (show Commute x y from hxy.trans hyx.symm).mul_pow, hxy]
  exact ((Nat.cast_commute p _).pow_left _).eq.symm

/-- The power of `p` in the product of two basis words. -/
private def wordExp (m n : ℤ) : ℕ :=
  min m.toNat (-n).toNat + min (-m).toNat n.toNat

omit [Fact p.Prime] in
private lemma zpowFV_mul_zpowFV {f v : R} (hfv : f * v = p) (hvf : v * f = p) (m n : ℤ) :
    zpowFV f v m * zpowFV f v n = (p : R) ^ wordExp m n * zpowFV f v (m + n) := by
  obtain ⟨a, rfl | rfl⟩ := Int.eq_nat_or_neg m <;> obtain ⟨b, rfl | rfl⟩ := Int.eq_nat_or_neg n
  · rw [← Nat.cast_add, zpowFV_natCast, zpowFV_natCast, zpowFV_natCast, ← pow_add,
      show wordExp a b = 0 by unfold wordExp; omega, pow_zero, one_mul]
  · rw [zpowFV_natCast, zpowFV_neg_natCast]
    rcases le_total a b with hab | hab
    · obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hab
      rw [show (a : ℤ) + -↑(a + c) = -c by push_cast; ring, zpowFV_neg_natCast,
        show wordExp a (-↑(a + c)) = a by unfold wordExp; omega, pow_mul_pow_add hfv hvf]
    · obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le' hab
      rw [show ((c + b : ℕ) : ℤ) + -b = c by push_cast; ring, zpowFV_natCast,
        show wordExp ↑(c + b) (-b) = b by unfold wordExp; omega, pow_add_mul_pow hfv hvf]
  · rw [zpowFV_natCast, zpowFV_neg_natCast]
    rcases le_total a b with hab | hab
    · obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hab
      rw [show -(a : ℤ) + ↑(a + c) = c by push_cast; ring, zpowFV_natCast,
        show wordExp (-a) ↑(a + c) = a by unfold wordExp; omega, pow_mul_pow_add hvf hfv]
    · obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le' hab
      rw [show -((c + b : ℕ) : ℤ) + b = -c by push_cast; ring, zpowFV_neg_natCast,
        show wordExp (-↑(c + b)) b = b by unfold wordExp; omega, pow_add_mul_pow hvf hfv]
  · rw [show -(a : ℤ) + -b = -↑(a + b) by push_cast; ring, zpowFV_neg_natCast,
      zpowFV_neg_natCast, zpowFV_neg_natCast, ← pow_add,
      show wordExp (-a) (-b) = 0 by unfold wordExp; omega, pow_zero, one_mul]

omit [CharP k p] [PerfectRing k p] in
private lemma pow_mul_map {g : 𝕎 k →+* R} {x : R} {τ : RingAut (𝕎 k)}
    (h : ∀ ξ : 𝕎 k, x * g ξ = g (τ ξ) * x) (n : ℕ) (ξ : 𝕎 k) :
    x ^ n * g ξ = g ((τ ^ n) ξ) * x ^ n := by
  induction n generalizing ξ with
  | zero => simp
  | succ n ih =>
    simp only [pow_succ, ← mul_assoc]
    rw [mul_assoc, h, ← mul_assoc, ih]
    simp [mul_assoc]

private lemma zpowFV_mul_map {g : 𝕎 k →+* R} {f v : R}
    (hF : ∀ ξ : 𝕎 k, f * g ξ = g (frobenius ξ) * f)
    (hV : ∀ ξ : 𝕎 k, v * g (frobenius ξ) = g ξ * v) (m : ℤ) (ξ : 𝕎 k) :
    zpowFV f v m * g ξ = g (((frobeniusEquiv p k : RingAut (𝕎 k)) ^ m) ξ) * zpowFV f v m := by
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg m
  · rw [zpowFV_natCast, zpow_natCast]
    exact pow_mul_map hF n ξ
  · have hV' (ξ : 𝕎 k) : v * g ξ = g ((frobeniusEquiv p k)⁻¹ ξ) * v := by
      rw [← hV, frobenius_frobeniusEquiv_inv]
    rw [zpowFV_neg_natCast, zpow_neg, zpow_natCast,
      ← inv_pow (frobeniusEquiv p k : RingAut (𝕎 k))]
    exact pow_mul_map hV' n ξ

private lemma zpowFV_mul_map_mul_zpowFV {g : 𝕎 k →+* R} {f v : R}
    (hF : ∀ ξ : 𝕎 k, f * g ξ = g (frobenius ξ) * f)
    (hV : ∀ ξ : 𝕎 k, v * g (frobenius ξ) = g ξ * v) (hfv : f * v = p) (hvf : v * f = p)
    (m n : ℤ) (η : 𝕎 k) :
    zpowFV f v m * (g η * zpowFV f v n) =
      g (((frobeniusEquiv p k : RingAut (𝕎 k)) ^ m) η * (p : 𝕎 k) ^ wordExp m n) *
        zpowFV f v (m + n) := by
  rw [← mul_assoc, zpowFV_mul_map hF hV, mul_assoc, zpowFV_mul_zpowFV hfv hvf, map_mul, map_pow,
    map_natCast, mul_assoc]

end Words

/-! ### The Dieudonné ring as a free left `𝕎 k`-module -/

/-- The Witt vectors act on the Dieudonné ring by left multiplication by scalars. -/
instance : Module (𝕎 k) (DieudonneRing p k) :=
  Module.compHom _ (C p k)

/-- Scalar multiplication by `ξ` is left multiplication by `C ξ`. -/
theorem smul_def (ξ : 𝕎 k) (x : DieudonneRing p k) : ξ • x = C p k ξ * x :=
  rfl

instance : IsScalarTower (𝕎 k) (DieudonneRing p k) (DieudonneRing p k) :=
  ⟨fun ξ x y ↦ by simp only [smul_def, smul_eq_mul, mul_assoc]⟩

/-- The basis word `Fⁿ` for `n ≥ 0` and `V⁻ⁿ` for `n < 0`. -/
private def word (n : ℤ) : DieudonneRing p k :=
  zpowFV (F p k) (V p k) n

/-- The product of two basis words: `wₘ (η wₙ) = (σᵐ(η) pᵉ) wₘ₊ₙ`, with `e = wordExp m n`. -/
private lemma word_mul_smul_word (m n : ℤ) (η : 𝕎 k) :
    (word m : DieudonneRing p k) * (η • word n) =
      (((frobeniusEquiv p k : RingAut (𝕎 k)) ^ m) η * (p : 𝕎 k) ^ wordExp m n) •
        word (m + n) := by
  rw [smul_def, smul_def, word, word, word]
  exact zpowFV_mul_map_mul_zpowFV F_mul_C V_mul_C_frobenius F_mul_V V_mul_F m n η

theorem val_F_pow (n : ℕ) :
    val (F p k ^ n) = SkewMonoidAlgebra.single (Multiplicative.ofAdd (n : ℤ)) 1 := by
  induction n with
  | zero => simp
  | succ n ih => simp [pow_succ, ih, ← ofAdd_add]

theorem val_V_pow (n : ℕ) :
    val (V p k ^ n) =
      SkewMonoidAlgebra.single (Multiplicative.ofAdd (-(n : ℤ))) ((p : 𝕎 k) ^ n) := by
  induction n with
  | zero => simp
  | succ n ih => simp [pow_succ, ih, frobeniusZPowAction_smul_def, mul_comm]

private lemma val_smul_word (ξ : 𝕎 k) (n : ℤ) :
    val (ξ • word n) =
      SkewMonoidAlgebra.single (Multiplicative.ofAdd n) (ξ * (p : 𝕎 k) ^ (-n).toNat) := by
  rw [smul_def, map_mul, val_C, word]
  obtain ⟨a, rfl | rfl⟩ := Int.eq_nat_or_neg n
  · rw [zpowFV_natCast, val_F_pow, SkewMonoidAlgebra.single_mul_single, one_smul, one_mul,
      mul_one]
    simp
  · rw [zpowFV_neg_natCast, val_V_pow, SkewMonoidAlgebra.single_mul_single, one_smul, one_mul,
      neg_neg, Int.toNat_natCast]

private lemma coeff_val_linearCombination (l : ℤ →₀ 𝕎 k) (n : ℤ) :
    (val (Finsupp.linearCombination (𝕎 k) word l)).coeff (Multiplicative.ofAdd n) =
      l n * (p : 𝕎 k) ^ (-n).toNat := by
  classical
  rw [Finsupp.linearCombination_apply, map_finsuppSum]
  simp_rw [val_smul_word]
  rw [SkewMonoidAlgebra.coeff_finsuppSum, Finsupp.sum_apply]
  simp only [SkewMonoidAlgebra.coeff_single, Finsupp.single_apply,
    EmbeddingLike.apply_eq_iff_eq]
  rw [Finsupp.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [Finsupp.notMem_support_iff.1 h, zero_mul]

private lemma linearIndependent_word :
    LinearIndependent (𝕎 k) (word : ℤ → DieudonneRing p k) := by
  rw [linearIndependent_iff]
  intro l hl
  refine Finsupp.ext fun n ↦ ?_
  have h := coeff_val_linearCombination l n
  rw [hl, map_zero, SkewMonoidAlgebra.coeff_zero, Finsupp.zero_apply] at h
  have hp : IsRightRegular (p : 𝕎 k) :=
    isRightRegular_iff_left_eq_zero_of_mul.2 (eq_zero_of_p_mul_eq_zero (p := p))
  exact isRightRegular_iff_left_eq_zero_of_mul.1 (hp.pow _) _ h.symm

private lemma mem_span_word (x : DieudonneRing p k) :
    x ∈ Submodule.span (𝕎 k) (Set.range word) := by
  classical
  choose c hc using fun a ↦ dvd_def.1 (mem_subring.1 (val_mem x) a)
  have : x = ∑ a ∈ (val x).support, c a • word a.toAdd := by
    apply val_injective
    rw [map_sum]
    simp_rw [val_smul_word, ofAdd_toAdd]
    conv_lhs => rw [← SkewMonoidAlgebra.sum_coeff_single (val x)]
    rw [Finsupp.sum, SkewMonoidAlgebra.support_coeff]
    exact Finset.sum_congr rfl fun a _ ↦ by rw [hc a, mul_comm]
  rw [this]
  exact Submodule.sum_mem _ fun a _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)

variable (p k) in
/-- The Dieudonné ring is a free left `𝕎 k`-module with basis `…, V², V, 1, F, F², …`:
`basis n = Fⁿ` for `n ≥ 0` and `basis (-n) = Vⁿ`. -/
def basis : Module.Basis ℤ (𝕎 k) (DieudonneRing p k) :=
  .mk linearIndependent_word fun x _ ↦ mem_span_word x

private lemma basis_eq_word (n : ℤ) : basis p k n = word n :=
  Module.Basis.mk_apply _ _ n

@[simp]
theorem basis_natCast (n : ℕ) : basis p k n = F p k ^ n := by
  rw [basis_eq_word, word, zpowFV_natCast]

@[simp]
theorem basis_neg_natCast (n : ℕ) : basis p k (-n) = V p k ^ n := by
  rw [basis_eq_word, word, zpowFV_neg_natCast]

@[simp]
theorem basis_zero : basis p k 0 = 1 := by
  simpa using basis_natCast (p := p) (k := k) 0

@[simp]
theorem basis_one : basis p k 1 = F p k := by
  simpa using basis_natCast (p := p) (k := k) 1

@[simp]
theorem basis_neg_one : basis p k (-1) = V p k := by
  simpa using basis_neg_natCast (p := p) (k := k) 1

/-- The coefficient of `Fⁿ` in the image of `x` in `𝕎 k [F, F⁻¹; σ]` is the `n`-th coordinate of
`x` in `TauCeti.DieudonneRing.basis`, times `p⁻ⁿ` when `n ≤ 0`. -/
theorem coeff_val (x : DieudonneRing p k) (n : ℤ) :
    (val x).coeff (Multiplicative.ofAdd n) = (basis p k).repr x n * (p : 𝕎 k) ^ (-n).toNat := by
  have h : ⇑(basis p k) = word := funext basis_eq_word
  conv_lhs => rw [← (basis p k).linearCombination_repr x, h]
  exact coeff_val_linearCombination _ n

instance : Module.Free (𝕎 k) (DieudonneRing p k) :=
  .of_basis (basis p k)

/-! ### The universal property -/

/-- Two additive maps out of the Dieudonné ring agree once they agree on every `ξ • basis n`. -/
private lemma addHom_ext {M : Type*} [AddCommMonoid M] {a b : DieudonneRing p k →+ M}
    (h : ∀ (ξ : 𝕎 k) (n : ℤ), a (ξ • basis p k n) = b (ξ • basis p k n)) : a = b := by
  ext x
  rw [← (basis p k).linearCombination_repr x, Finsupp.linearCombination_apply, map_finsuppSum,
    map_finsuppSum]
  exact Finsupp.sum_congr fun n _ ↦ h _ _

section Lift

variable {R : Type*} [Ring R]

/-- The additive map `∑ ξₙ • basis n ↦ ∑ g(ξₙ) wₙ` underlying `lift`, where `wₙ = fⁿ` for
`n ≥ 0` and `wₙ = v⁻ⁿ` for `n < 0`. -/
private def liftAddHom (g : 𝕎 k →+* R) (f v : R) : DieudonneRing p k →+ R :=
  (Finsupp.liftAddHom fun n ↦ (AddMonoidHom.mulRight (zpowFV f v n)).comp g.toAddMonoidHom).comp
    (basis p k).repr.toLinearMap.toAddMonoidHom

private lemma liftAddHom_smul_basis (g : 𝕎 k →+* R) (f v : R) (ξ : 𝕎 k) (n : ℤ) :
    liftAddHom g f v (ξ • basis p k n) = g ξ * zpowFV f v n := by
  simp [liftAddHom]

private lemma liftAddHom_smul_word (g : 𝕎 k →+* R) (f v : R) (ξ : 𝕎 k) (n : ℤ) :
    liftAddHom g f v (ξ • word n) = g ξ * zpowFV f v n := by
  rw [← basis_eq_word, liftAddHom_smul_basis]

private lemma liftAddHom_smul (g : 𝕎 k →+* R) (f v : R) (ξ : 𝕎 k) (x : DieudonneRing p k) :
    liftAddHom g f v (ξ • x) = g ξ * liftAddHom g f v x := by
  have := addHom_ext (a := (liftAddHom g f v).comp (DistribSMul.toAddMonoidHom _ ξ))
    (b := (AddMonoidHom.mulLeft (g ξ)).comp (liftAddHom g f v)) fun η n ↦ by
      simp [smul_smul, liftAddHom_smul_basis, mul_assoc]
  exact DFunLike.congr_fun this x

variable {g : WittVector p k →+* R} {f v : R}

private lemma liftAddHom_word_mul (hF : ∀ ξ : 𝕎 k, f * g ξ = g (frobenius ξ) * f)
    (hV : ∀ ξ : 𝕎 k, v * g (frobenius ξ) = g ξ * v) (hfv : f * v = p) (hvf : v * f = p)
    (m : ℤ) (y : DieudonneRing p k) :
    liftAddHom g f v (word m * y) = zpowFV f v m * liftAddHom g f v y := by
  have := addHom_ext (a := (liftAddHom g f v).comp (AddMonoidHom.mulLeft (word m)))
    (b := (AddMonoidHom.mulLeft (zpowFV f v m)).comp (liftAddHom g f v)) fun η n ↦ by
      simp only [AddMonoidHom.coe_comp, Function.comp_apply, AddMonoidHom.coe_mulLeft]
      rw [basis_eq_word, word_mul_smul_word, liftAddHom_smul_word, liftAddHom_smul_word,
        zpowFV_mul_map_mul_zpowFV hF hV hfv hvf]
  exact DFunLike.congr_fun this y

private lemma liftAddHom_mul (hF : ∀ ξ : 𝕎 k, f * g ξ = g (frobenius ξ) * f)
    (hV : ∀ ξ : 𝕎 k, v * g (frobenius ξ) = g ξ * v) (hfv : f * v = p) (hvf : v * f = p)
    (x y : DieudonneRing p k) :
    liftAddHom g f v (x * y) = liftAddHom g f v x * liftAddHom g f v y := by
  have := addHom_ext (a := (liftAddHom g f v).comp (AddMonoidHom.mulRight y))
    (b := (AddMonoidHom.mulRight (liftAddHom g f v y)).comp (liftAddHom g f v)) fun ξ m ↦ by
      simp only [AddMonoidHom.coe_comp, Function.comp_apply, AddMonoidHom.coe_mulRight]
      rw [smul_mul_assoc, liftAddHom_smul, liftAddHom_smul_basis, basis_eq_word,
        liftAddHom_word_mul hF hV hfv hvf, mul_assoc]
  exact DFunLike.congr_fun this x

variable (g f v) in
/-- The **universal property of the Dieudonné ring**: a ring homomorphism `g : 𝕎 k →+* R`
together with elements `f v : R` satisfying `f g(ξ) = g(σ ξ) f`, `v g(σ ξ) = g(ξ) v` and
`f v = v f = p` extend to a ring homomorphism `D_k →+* R` sending `F ↦ f` and `V ↦ v`.
It is unique by `TauCeti.DieudonneRing.ringHom_ext`. -/
def lift (hF : ∀ ξ : 𝕎 k, f * g ξ = g (frobenius ξ) * f)
    (hV : ∀ ξ : 𝕎 k, v * g (frobenius ξ) = g ξ * v) (hfv : f * v = p) (hvf : v * f = p) :
    DieudonneRing p k →+* R where
  __ := liftAddHom g f v
  map_one' := by simpa [zpowFV_zero] using liftAddHom_smul_basis g f v 1 0
  map_mul' := liftAddHom_mul hF hV hfv hvf

variable (hF : ∀ ξ : WittVector p k, f * g ξ = g (frobenius ξ) * f)
  (hV : ∀ ξ : WittVector p k, v * g (frobenius ξ) = g ξ * v) (hfv : f * v = p) (hvf : v * f = p)

private lemma lift_apply (x : DieudonneRing p k) :
    lift g f v hF hV hfv hvf x = liftAddHom g f v x :=
  rfl

@[simp]
theorem lift_C (ξ : 𝕎 k) : lift g f v hF hV hfv hvf (C p k ξ) = g ξ := by
  simpa [lift_apply, smul_def, zpowFV_zero] using liftAddHom_smul_basis g f v ξ 0

@[simp]
theorem lift_F : lift g f v hF hV hfv hvf (F p k) = f := by
  simpa [lift_apply, zpowFV_one] using liftAddHom_smul_basis g f v 1 1

@[simp]
theorem lift_V : lift g f v hF hV hfv hvf (V p k) = v := by
  simpa [lift_apply, zpowFV_neg_one] using liftAddHom_smul_basis g f v 1 (-1)

theorem lift_comp_C : (lift g f v hF hV hfv hvf).comp (C p k) = g :=
  RingHom.ext (lift_C hF hV hfv hvf)

end Lift

/-- A ring homomorphism out of the Dieudonné ring is determined by its values on the scalars and
on the generators `F` and `V`. -/
@[ext]
theorem ringHom_ext {R : Type*} [Ring R] {a b : DieudonneRing p k →+* R}
    (hC : a.comp (C p k) = b.comp (C p k)) (hF : a (F p k) = b (F p k))
    (hV : a (V p k) = b (V p k)) : a = b := by
  refine RingHom.toAddMonoidHom_injective (addHom_ext fun ξ n ↦ ?_)
  simp only [AddMonoidHom.coe_ofClass]
  rw [smul_def, map_mul, map_mul, basis_eq_word, word, map_zpowFV, map_zpowFV, hF, hV,
    ← RingHom.comp_apply, hC, RingHom.comp_apply]

/-- **Induction principle for the Dieudonné ring**: a property of elements of `D_k` that holds
for the scalars `C ξ` and the generators `F` and `V`, and is closed under sums and products,
holds for every element. -/
@[elab_as_elim]
theorem induction_on {P : DieudonneRing p k → Prop} (x : DieudonneRing p k)
    (hC : ∀ ξ : 𝕎 k, P (C p k ξ)) (hF : P (F p k)) (hV : P (V p k))
    (hadd : ∀ x y, P x → P y → P (x + y)) (hmul : ∀ x y, P x → P y → P (x * y)) : P x := by
  have hpow {y : DieudonneRing p k} (hy : P y) (n : ℕ) : P (y ^ n) := by
    induction n with
    | zero => simpa using hC 1
    | succ n ih => simpa [pow_succ] using hmul _ _ ih hy
  induction (basis p k).mem_span x using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨n, rfl⟩ := hy
    obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg n
    · simpa using hpow hF m
    · simpa using hpow hV m
  | zero => simpa using hC 0
  | add y z _ _ hy hz => exact hadd y z hy hz
  | smul ξ y _ hy => simpa [smul_def] using hmul _ _ (hC ξ) hy

end DieudonneRing

end TauCeti
