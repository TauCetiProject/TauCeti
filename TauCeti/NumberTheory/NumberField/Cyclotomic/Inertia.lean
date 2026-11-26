/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Cyclotomic.Galois
public import TauCeti.NumberTheory.NumberField.AutomorphismAction
import TauCeti.NumberTheory.NumberField.Frobenius.Restriction
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
agreement on its `p ^ k`-th power is enough to recover agreement on the generator. Passing to a
normal subfield uses the general lifting of residue powers along restriction,
`NumberField.image_restrictNormal_setOf_forall_quotient_mk_smul_eq_pow`.

The identification of inertia and of the Frobenius cosets follows Levent Alpöge's formal proof
`UpperTheory.Comparison₂.prim_read` in the Lean formalization of the Riemann hypothesis for
Dirichlet L-functions, <https://github.com/leanprover-community/riemann-hypothesis> at commit
`40e56bab026552e089d7afcfeff08d2defb9c005`, file
`src/Development/AutomorphicArithmetic/PrimitiveCosets/PrimRead.lean`, which also applies it to
primitive characters.
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
      ZMod.unitsMap (Dvd.intro_left _ hn.symm) (galEquivZMod n L σ) =
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
  let g := ((iterateFrobenius (𝓞 L ⧸ Q) p i).comp (Ideal.Quotient.mk Q)).toIntAlgHom
  have hgen : (∀ x : 𝓞 L, f x = g x) ↔ f z = g z := by
    refine ⟨fun h ↦ h z, fun h ↦ DFunLike.congr_fun ?_⟩
    exact AlgHom.ext_of_adjoin_eq_top (adjoin_singleton_eq_top hζ)
      (Set.eqOn_singleton.mpr h)
  let a := (galEquivZMod n L σ).val.val
  have hf : f z = Ideal.Quotient.mk Q z ^ a := by
    simp only [f, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, MulSemiringAction.toAlgHom_apply]
    rw [galEquivZMod_smul_of_pow_eq n L σ hz.pow_eq_one, map_pow]
  have hfx (x : 𝓞 L) : f x = Ideal.Quotient.mk Q (σ • x) := by
    simp only [f, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, MulSemiringAction.toAlgHom_apply]
  have hg (x : 𝓞 L) : g x = Ideal.Quotient.mk Q x ^ (p ^ i) := by
    simp only [g, RingHom.toIntAlgHom_apply, RingHom.comp_apply, iterateFrobenius_def]
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
          ((ZMod.unitsMap (Dvd.intro_left _ hn.symm) u).val : ZMod m) =
            (u.val.val : ZMod m) := ZMod.cast_eq_val u.val
      simp only [a, hcast, Units.val_pow_eq_pow_val, ZMod.coe_unitOfCoprime, Nat.cast_pow]

/-- Inertia maps under the cyclotomic Galois isomorphism to the kernel of reduction modulo
the prime-to-`p` part of the level. -/
theorem galEquivZMod_map_inertia_eq_ker_unitsMap (hn : n = p ^ k * m)
    (hm : p.Coprime m) (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver (span {(p : ℤ)})] :
    (galEquivZMod n L).mapSubgroup (Q.inertia Gal(L/ℚ)) =
      (ZMod.unitsMap (Dvd.intro_left _ hn.symm)).ker := by
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
theorem image_unitsMap_fiber_eq_setOf_forall_quotient_mk_smul_eq_pow (hn : n = p ^ k * m)
    (hm : p.Coprime m) (E : IntermediateField ℚ L) [Normal ℚ E]
    (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver (span {(p : ℤ)})] (i : ℕ) :
    (fun u ↦ ((galEquivZMod n L).symm u).restrictNormal E) ''
        {u | ZMod.unitsMap (Dvd.intro_left _ hn.symm) u = ZMod.unitOfCoprime p hm ^ i} =
      {τ : Gal(E/ℚ) | ∀ x : 𝓞 E,
        Ideal.Quotient.mk (Q.under (𝓞 E)) (τ • x) =
          Ideal.Quotient.mk (Q.under (𝓞 E)) x ^ (p ^ i)} := by
  have : IsGalois ℚ L := IsCyclotomicExtension.isGalois {n} ℚ L
  have hiff := forall_quotient_mk_smul_eq_pow_iff_galEquivZMod hn hm Q (i := i)
  -- Some automorphism, the preimage of any unit in the fibre, induces the Frobenius power.
  obtain ⟨u, hu⟩ := ZMod.unitsMap_surjective (Dvd.intro_left _ hn.symm)
    (ZMod.unitOfCoprime p hm ^ i)
  rw [← NumberField.image_restrictNormal_setOf_forall_quotient_mk_smul_eq_pow E Q
    ⟨_, (hiff _).2 (by rwa [MulEquiv.apply_symm_apply])⟩]
  -- The fibre corresponds to these automorphisms under `galEquivZMod`.
  ext τ
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨_, (hiff _).2 (by rwa [MulEquiv.apply_symm_apply]), rfl⟩
  · rintro ⟨σ, hσ, rfl⟩
    exact ⟨galEquivZMod n L σ, (hiff σ).1 hσ, by simp only [MulEquiv.symm_apply_apply]⟩

/-- The inertia group in a cyclotomic subfield is the image of the kernel of reduction to the
units modulo the prime-to-`p` part of the level. -/
theorem image_ker_unitsMap_eq_inertia (hn : n = p ^ k * m) (hm : p.Coprime m)
    (E : IntermediateField ℚ L) [Normal ℚ E]
    (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver (span {(p : ℤ)})] :
    (fun u ↦ ((galEquivZMod n L).symm u).restrictNormal E) ''
        ↑(ZMod.unitsMap (Dvd.intro_left _ hn.symm)).ker =
      ↑((Q.under (𝓞 E)).inertia Gal(E/ℚ)) := by
  convert image_unitsMap_fiber_eq_setOf_forall_quotient_mk_smul_eq_pow hn hm E Q 0 using 1
  · rw [MonoidHom.coe_ker, Set.preimage_singleton, pow_zero]
  · ext τ
    simp only [SetLike.mem_coe, Set.mem_ofPred_eq, Ideal.mem_inertia, pow_zero, pow_one,
      Ideal.Quotient.eq]

end IsCyclotomicExtension.Rat
