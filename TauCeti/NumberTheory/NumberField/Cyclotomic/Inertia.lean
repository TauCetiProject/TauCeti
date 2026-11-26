/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Cyclotomic.Galois
public import TauCeti.NumberTheory.NumberField.AutomorphismAction
import Mathlib.FieldTheory.Galois.IsGaloisGroup
import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import Mathlib.NumberTheory.NumberField.Ideal.Basic
import Mathlib.RingTheory.Ideal.Int

/-!
# Frobenius at every prime in a rational cyclotomic field

If the cyclotomic level is `p ^ k * m` with `p` prime to `m`, the lifts of the `i`-th
power of arithmetic Frobenius are the automorphisms with exponent `p ^ i` modulo `m`.
This description retains the entire inertia coset when `p` ramifies. In particular, inertia
is the kernel of reduction to the units modulo `m`.

The calculation uses the integral generator of the ring of integers: in characteristic `p`,
agreement on its `p ^ k`-th power is enough to recover agreement on the generator.
For the application to primitive characters, see Levent Alpöge's
`UpperTheory.Comparison₂.prim_read`.
-/

public section

open NumberField Ideal

namespace IsCyclotomicExtension.Rat

variable {L : Type*} [Field L] [NumberField L]
variable {n p m k : ℕ} [NeZero n] [Fact p.Prime]
variable [IsCyclotomicExtension {n} ℚ L]

/-- In a cyclotomic field of level `p ^ k * m` with `p` coprime to `m`, a Galois automorphism
induces the `i`-th power of arithmetic Frobenius at `Q` exactly when its cyclotomic exponent
is `p ^ i` modulo `m`. The case `i = 0` describes inertia. -/
theorem forall_quotient_mk_smul_eq_pow_iff_galEquivZMod (hn : n = p ^ k * m)
    (hm : p.Coprime m) (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver (span {(p : ℤ)})]
    (σ : Gal(L/ℚ)) (i : ℕ) :
    (∀ x : 𝓞 L, Ideal.Quotient.mk Q (σ • x) = Ideal.Quotient.mk Q x ^ (p ^ i)) ↔
      ZMod.unitsMap (show m ∣ n from hn ▸ dvd_mul_left m (p ^ k)) (galEquivZMod n L σ) =
        ZMod.unitOfCoprime p hm ^ i := by
  have : NeZero m := ⟨by rintro rfl; exact NeZero.ne n (by simp [hn])⟩
  have hp : p.Prime := Fact.out
  have hcard : CharP (ℤ ⧸ Q.under ℤ) p := by
    rw [← Q.over_def (span {(p : ℤ)})]
    exact ringChar.of_eq (Int.ringChar_idealQuot p)
  let : CharP (𝓞 L ⧸ Q) p :=
    CharP.of_ringHom_of_ne_zero (algebraMap (ℤ ⧸ Q.under ℤ) (𝓞 L ⧸ Q)) p hp.ne_zero
  let : ExpChar (𝓞 L ⧸ Q) p := .prime hp
  let hζ := zeta_spec n ℚ L
  let z : 𝓞 L := hζ.toInteger
  have hz : IsPrimitiveRoot z n := hζ.toInteger_isPrimitiveRoot
  -- The prime-to-`p` root retains its full order in the residue field.
  have hz' : IsPrimitiveRoot (Ideal.Quotient.mk Q z ^ (p ^ k)) m := by
    rw [← map_pow]
    have hzpow := hz.pow_of_dvd (pow_ne_zero k hp.ne_zero)
      (show p ^ k ∣ n from hn ▸ dvd_mul_right (p ^ k) m)
    rw [hn, Nat.mul_div_cancel_left _ (pow_pos hp.pos _)] at hzpow
    refine hzpow.idealQuotient_mk (mt absNorm_eq_one_iff.mp Ideal.IsPrime.ne_top') ?_
    rw [← pow_inertiaDeg p]
    exact hm.pow_left _
  let f := (Ideal.Quotient.mkₐ ℤ Q).comp (MulSemiringAction.toAlgHom ℤ (𝓞 L) σ)
  let g := ((iterateFrobenius (𝓞 L ⧸ Q) p i).toIntAlgHom).comp (Ideal.Quotient.mkₐ ℤ Q)
  have hgen : (∀ x : 𝓞 L, f x = g x) ↔ f z = g z := by
    refine ⟨fun h ↦ h z, fun h ↦ DFunLike.congr_fun ?_⟩
    exact AlgHom.ext_of_adjoin_eq_top (adjoin_singleton_eq_top hζ)
      (Set.eqOn_singleton.mpr h)
  let a := (galEquivZMod n L σ).val.val
  have hf : f z = Ideal.Quotient.mk Q z ^ a := by
    simp only [f, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, MulSemiringAction.toAlgHom_apply]
    rw [galEquivZMod_smul_of_pow_eq n L σ hz.pow_eq_one, map_pow]
  have hfx (x : 𝓞 L) : f x = Ideal.Quotient.mk Q (σ • x) := (rfl)
  have hg (x : 𝓞 L) : g x = Ideal.Quotient.mk Q x ^ (p ^ i) := (rfl)
  calc
    _ ↔ f z = g z := by simpa only [hfx, hg] using hgen
    _ ↔ (Ideal.Quotient.mk Q z ^ (p ^ k)) ^ a =
        (Ideal.Quotient.mk Q z ^ (p ^ k)) ^ (p ^ i) := by
      rw [hf, hg, ← (iterateFrobenius_inj (𝓞 L ⧸ Q) p k).eq_iff]
      simp only [iterateFrobenius_def, pow_right_comm _ _ (p ^ k)]
    _ ↔ _ := by
      rw [(hz'.isOfFinOrder (NeZero.ne m)).pow_eq_pow_iff_modEq, ← hz'.eq_orderOf,
        ← ZMod.natCast_eq_natCast_iff, Units.ext_iff]
      have hcast (u : (ZMod n)ˣ) :
          ((ZMod.unitsMap (show m ∣ n from hn ▸ dvd_mul_left m (p ^ k)) u).val : ZMod m) =
            (u.val.val : ZMod m) := ZMod.cast_eq_val u.val
      simp only [a, hcast, Units.val_pow_eq_pow_val, ZMod.coe_unitOfCoprime, Nat.cast_pow]

/-- Inertia maps under the cyclotomic Galois isomorphism to the kernel of reduction modulo
the prime-to-`p` part of the level. -/
theorem galEquivZMod_map_inertia_eq_ker_unitsMap (hn : n = p ^ k * m)
    (hm : p.Coprime m) (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver (span {(p : ℤ)})] :
    (galEquivZMod n L).mapSubgroup (Q.inertia Gal(L/ℚ)) =
      (ZMod.unitsMap (show m ∣ n from hn ▸ dvd_mul_left m (p ^ k))).ker := by
  refine (galEquivZMod n L).surjective.forall.mpr ?_ |> Subgroup.ext
  intro σ
  rw [MulEquiv.coe_mapSubgroup, Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply,
    MonoidHom.mem_ker, Ideal.mem_inertia]
  simpa only [pow_zero, pow_one, Ideal.Quotient.eq] using
    forall_quotient_mk_smul_eq_pow_iff_galEquivZMod hn hm Q σ 0

/-- For an intermediate field `E` of a rational cyclotomic field, the image of the units
congruent to `p ^ i` modulo the prime-to-`p` part of the level is exactly the set of automorphisms
of `E` inducing that power of arithmetic Frobenius at the contracted prime. In particular,
this describes the whole coset at a ramified prime, not just one representative. -/
theorem image_unitsMap_fiber_eq_frobeniusCoset (hn : n = p ^ k * m) (hm : p.Coprime m)
    (E : IntermediateField ℚ L) [Normal ℚ E]
    (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver (span {(p : ℤ)})] (i : ℕ) :
    (fun u ↦ ((galEquivZMod n L).symm u).restrictNormal E) ''
        {u | ZMod.unitsMap (show m ∣ n from hn ▸ dvd_mul_left m (p ^ k)) u =
          ZMod.unitOfCoprime p hm ^ i} =
      {τ : Gal(E/ℚ) | ∀ x : 𝓞 E,
        Ideal.Quotient.mk (Q.under (𝓞 E)) (τ • x) =
          Ideal.Quotient.mk (Q.under (𝓞 E)) x ^ (p ^ i)} := by
  let P := Q.under (𝓞 E)
  have hres (σ : Gal(L/ℚ)) (hσ : ∀ x : 𝓞 L,
      Ideal.Quotient.mk Q (σ • x) = Ideal.Quotient.mk Q x ^ (p ^ i)) (x : 𝓞 E) :
      Ideal.Quotient.mk P (σ.restrictNormal E • x) = Ideal.Quotient.mk P x ^ (p ^ i) := by
    rw [← map_pow, Ideal.Quotient.eq, Ideal.mem_under, map_sub,
      NumberField.algebraMap_restrictNormal_smul, map_pow, ← Ideal.Quotient.eq, map_pow]
    exact hσ _
  ext τ
  constructor
  · rintro ⟨u, hu, rfl⟩
    apply hres
    exact (forall_quotient_mk_smul_eq_pow_iff_galEquivZMod hn hm Q _ i).2 (by simpa using hu)
  · intro hτ
    -- Start with any lift of the desired Frobenius power and correct it by inertia.
    obtain ⟨u, hu⟩ := ZMod.unitsMap_surjective
      (show m ∣ n from hn ▸ dvd_mul_left m (p ^ k)) (ZMod.unitOfCoprime p hm ^ i)
    let σ := (galEquivZMod n L).symm u
    have hσ := (forall_quotient_mk_smul_eq_pow_iff_galEquivZMod hn hm Q σ i).2
      (by simpa only [σ, MulEquiv.apply_symm_apply] using hu)
    let r := AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := L) E
    have hδ : τ * (r σ)⁻¹ ∈ P.inertia Gal(E/ℚ) := by
      rw [Ideal.mem_inertia]
      intro x
      rw [← Ideal.Quotient.eq, mul_smul]
      have hx := (hτ ((r σ)⁻¹ • x)).trans (hres σ hσ ((r σ)⁻¹ • x)).symm
      have hr : σ.restrictNormal E = r σ := (rfl)
      simpa only [hr, smul_inv_smul] using hx
    have : IsGalois ℚ L := IsCyclotomicExtension.isGalois {n} ℚ L
    have : IsGaloisGroup E.fixingSubgroup E L :=
      IsGaloisGroup.intermediateField Gal(L/ℚ) ℚ L E
    have : IsGaloisGroup E.fixingSubgroup (𝓞 E) (𝓞 L) :=
      IsGaloisGroup.of_isFractionRing E.fixingSubgroup (𝓞 E) (𝓞 L) E L
    have hmap : (Q.inertia Gal(L/ℚ)).map r = P.inertia Gal(E/ℚ) :=
      Ideal.map_inertia_of_surjective r E.fixingSubgroup P Q
        (AlgEquiv.restrictNormalHom_surjective L) E.restrictNormalHom_ker.ge
        NumberField.algebraMap_restrictNormal_smul
    rw [← hmap] at hδ
    obtain ⟨δ, hδ, hδeq⟩ := hδ
    refine ⟨galEquivZMod n L (δ * σ), ?_, ?_⟩
    · apply (forall_quotient_mk_smul_eq_pow_iff_galEquivZMod hn hm Q (δ * σ) i).1
      intro x
      rw [mul_smul, Ideal.Quotient.eq.mpr (Ideal.mem_inertia.mp hδ (σ • x)), hσ x]
    · simp only [MulEquiv.symm_apply_apply]
      calc
        (δ * σ).restrictNormal E = r (δ * σ) := (rfl)
        _ = τ := by rw [map_mul, hδeq, inv_mul_cancel_right]

/-- The inertia group in a cyclotomic subfield is the image of the kernel of reduction to the
units modulo the prime-to-`p` part of the level. -/
theorem image_ker_unitsMap_eq_inertia (hn : n = p ^ k * m) (hm : p.Coprime m)
    (E : IntermediateField ℚ L) [Normal ℚ E]
    (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver (span {(p : ℤ)})] :
    (fun u ↦ ((galEquivZMod n L).symm u).restrictNormal E) ''
        ↑(ZMod.unitsMap (show m ∣ n from hn ▸ dvd_mul_left m (p ^ k))).ker =
      ↑((Q.under (𝓞 E)).inertia Gal(E/ℚ)) := by
  convert image_unitsMap_fiber_eq_frobeniusCoset hn hm E Q 0 using 1
  · rw [MonoidHom.coe_ker, Set.preimage_singleton, pow_zero]
  · ext τ
    simp only [SetLike.mem_coe, Set.mem_ofPred_eq, Ideal.mem_inertia, pow_zero, pow_one,
      Ideal.Quotient.eq]

end IsCyclotomicExtension.Rat
