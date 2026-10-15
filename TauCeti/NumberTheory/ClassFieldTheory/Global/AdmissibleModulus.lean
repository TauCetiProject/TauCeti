/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Cyclotomic.Basic
public import TauCeti.NumberTheory.ClassFieldTheory.Global.Cyclotomic.ArtinNorm
public import TauCeti.NumberTheory.NumberField.Global.Ideles.Norm.Range
public import TauCeti.NumberTheory.NumberField.Global.Ideles.Ray.Subgroup
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import TauCeti.NumberTheory.ClassFieldTheory.Global.Cyclotomic.ProductFormula

/-!
# Admissible moduli and the real places

Let `L/K` be an extension of number fields. A modulus `𝔪` of `K` is **admissible** for `L/K`
(`IsAdmissibleModulus K L 𝔪`) when its ray subgroup lies in the idele-class norm group
`N_{L/K}(C_L)`. For an abelian extension this is the condition under which the global Artin map
factors through the ray class group of `𝔪`, which is why ray-class reciprocity is stated for
admissible moduli. Admissibility is inherited by multiples (`IsAdmissibleModulus.of_dvd`),
because ray subgroups shrink as the modulus grows.

This file shows that the real places cannot be left out of an admissible modulus when `L` contains
enough roots of unity. Let `w` be a real place of `K` and suppose that `L` contains a primitive
`pⁿ`-th root of unity with `pⁿ > 2`. Then the idele class that is `-1` at `w` and `1` everywhere
else is not a norm from `L` (`ofCompletion_neg_one_notMem_range_ideleClassNormMap`). Suppose that
`(-1)_w · α` is the norm of an idele of `L` for some `α ∈ Kˣ`. Then `α` is a local norm from
`K_v ⊗[K] L` at every place `v ≠ w` and `-α` is one at `w`, so, by
`abelianizedLocalCyclotomicCharacter_artinMap_mem_unitsPrincipal` and its archimedean
counterpart, the `p`-adic cyclotomic characters `χ_p(Art_v(α))` are `≡ 1 mod pⁿ` for `v ≠ w`,
while `χ_p(Art_w(α)) ≡ -1`, since `χ_p(Art_w(-1)) = -1` at a real place. Their product is `1` by
the cyclotomic product formula
(`finprod_mul_prod_abelianizedLocalCyclotomicCharacter_artinMap_eq_one`), which forces
`-1 ≡ 1 mod pⁿ`. No global reciprocity law is used.

That idele class lies in the ray subgroup of every modulus whose infinite part omits `w`
(`TauCeti.GlobalNumberFields.ofCompletion_mem_raySubgroup`), so no such modulus is admissible
(`not_isAdmissibleModulus_of_forall_ne`). For `ℚ(i)/ℚ` this rejects the trivial modulus
(`not_isAdmissibleModulus_one_Qi`), whose ray class group is trivial although the unramified prime
`3` does not split in `ℚ(i)`. It also rejects the modulus `(4)`, which contains the only ramified
prime: the conductor of `ℚ(i)/ℚ` is `(4) · ∞`.

## Main definitions

* `TauCeti.ClassFieldTheory.IsAdmissibleModulus`: the ray subgroup of `𝔪` lies in the idele-class
  norm group of `L/K`.

## Main results

* `TauCeti.ClassFieldTheory.ofCompletion_neg_one_notMem_range_ideleClassNormMap`: if `L` contains a
  primitive `pⁿ`-th root of unity with `pⁿ > 2`, the class of `-1` at a real place of `K` is not
  a norm from `L`.
* `TauCeti.ClassFieldTheory.not_isAdmissibleModulus_of_forall_ne`: under the same hypothesis, a
  modulus whose infinite part omits a real place is not admissible.
* `TauCeti.ClassFieldTheory.not_isAdmissibleModulus_one_Qi`: the trivial modulus is not admissible
  for `ℚ(i)/ℚ`.

## References

* J. S. Milne, *Class Field Theory*, v4.03, Chapter V (admissible moduli and the conductor of an
  abelian extension) and Chapter VII, Example 8.2 (the cyclotomic product formula).
* J. Neukirch, *Algebraic Number Theory*, Chapter VI (the conductor and the ray class fields).
-/

public section

noncomputable section

namespace TauCeti.ClassFieldTheory

open IsDedekindDomain NumberField NumberField.InfinitePlace TauCeti.GlobalNumberFields

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/-! ### The class of `-1` at a real place -/

/-- **The class of `-1` at a real place is not a norm from an extension containing `μ_{pⁿ}`.**
Let `w` be a real place of `K` and let `L/K` contain a primitive `pⁿ`-th root of unity with
`pⁿ > 2`. Then the idele class that is `-1` at `w` and `1` at every other place is not the norm of
an idele class of `L`. -/
theorem ofCompletion_neg_one_notMem_range_ideleClassNormMap (p : ℕ) [Fact p.Prime]
    {w : InfinitePlace K} (hw : w.IsReal) {n : ℕ} {ζ : L} (hζ : IsPrimitiveRoot ζ (p ^ n))
    (hpn : 2 < p ^ n) :
    IdeleClassGroup.ofCompletion (𝓞 K) K w (-1) ∉
      (ideleClassNormMap K L : IdeleClassGroup (𝓞 L) L →* IdeleClassGroup (𝓞 K) K).range := by
  classical
  rintro ⟨y, hy⟩
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
  set e := IdeleGroup.ofCompletion (𝓞 K) K w (-1)
  -- `N_{L/K}(x) = e · α⁻¹` for a principal idele `α`.
  have hy' : ((ideleNormMap K L x : IdeleGroup (𝓞 K) K) : IdeleClassGroup (𝓞 K) K) = e := by
    rw [← ideleClassNormMap_mk]
    exact hy.trans (IdeleClassGroup.ofCompletion_apply _ _ _ _)
  obtain ⟨α, hα⟩ := QuotientGroup.eq.mp hy'
  have hNx : ideleNormMap K L x = e * IdeleGroup.unitEmbedding (𝓞 K) K α⁻¹ := by
    rw [map_inv, hα, mul_inv_rev, inv_inv, mul_inv_cancel_left]
  obtain ⟨hfin, hinf⟩ := (mem_range_ideleNormMap_iff K L _).mp ⟨x, hNx⟩
  set U := unitsPrincipal p n
  -- At the finite places `α⁻¹` is a local norm.
  have hA (v : HeightOneSpectrum (𝓞 K)) :
      abelianizedLocalCyclotomicCharacter p (v.adicCompletion K)
        (artinMap (v.adicCompletion K) (Units.map (algebraMap K (v.adicCompletion K)) α⁻¹)) ∈
          U := by
    have hv := hfin v
    rw [map_mul, HeightOneSpectrum.ideleFiniteCoord_ofCompletion, one_mul,
      HeightOneSpectrum.ideleFiniteCoord_unitEmbedding] at hv
    exact abelianizedLocalCyclotomicCharacter_artinMap_mem_unitsPrincipal p hζ v hv
  -- So is it at the infinite places other than `w`.
  have hB (v : InfinitePlace K) (hv : v ≠ w) :
      abelianizedLocalCyclotomicCharacter p v.Completion
        (infiniteArtinAt v (Units.map (algebraMap K v.Completion) α⁻¹)) ∈ U := by
    have hv' := hinf v
    rw [map_mul, ideleInfiniteCoord_ofCompletion_of_ne _ hv, one_mul,
      ideleInfiniteCoord_unitEmbedding] at hv'
    exact abelianizedLocalCyclotomicCharacter_infiniteArtinAt_mem_unitsPrincipal p hζ v hv'
  -- At `w` it is `-α⁻¹` that is a local norm, and `Art_w(-1)` has character `-1`.
  have hC : abelianizedLocalCyclotomicCharacter p w.Completion
      (infiniteArtinAt w (-1 * Units.map (algebraMap K w.Completion) α⁻¹)) ∈ U := by
    have hw' := hinf w
    rw [map_mul, ideleInfiniteCoord_ofCompletion_self, ideleInfiniteCoord_unitEmbedding] at hw'
    exact abelianizedLocalCyclotomicCharacter_infiniteArtinAt_mem_unitsPrincipal p hζ w hw'
  have hneg : abelianizedLocalCyclotomicCharacter p w.Completion (infiniteArtinAt w (-1)) = -1 :=
    abelianizedLocalCyclotomicCharacter_infiniteArtinAt_eq_neg_one_of_neg w hw p (by simp)
  rw [map_mul, map_mul, hneg, neg_one_mul] at hC
  -- The product formula then puts `-1` in `U = 1 + pⁿ ℤ_p`.
  have hprod := finprod_mul_prod_abelianizedLocalCyclotomicCharacter_artinMap_eq_one p α⁻¹
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ w)] at hprod
  have hP := U.prod_mem (t := Finset.univ.erase w) fun v hv ↦ hB v (Finset.ne_of_mem_erase hv)
  have hF := finprod_induction (· ∈ U) U.one_mem (fun _ _ ↦ U.mul_mem) hA
  have key := congrArg Neg.neg hprod
  rw [← mul_neg, ← neg_mul] at key
  refine neg_one_notMem_unitsPrincipal hpn ?_
  rw [← key]
  exact U.mul_mem hF (U.mul_mem hC hP)

/-! ### Admissible moduli -/

/-- A modulus `𝔪` of `K` is **admissible** for the extension `L/K` when the ray subgroup of `𝔪`
lies in the idele-class norm group `N_{L/K}(C_L)`: every idele class satisfying the congruence
and sign conditions of `𝔪` is a norm from `L`. -/
def IsAdmissibleModulus (𝔪 : Modulus K) : Prop :=
  raySubgroup 𝔪 ≤
    (ideleClassNormMap K L : IdeleClassGroup (𝓞 L) L →* IdeleClassGroup (𝓞 K) K).range

variable {K L}

/-- The defining condition of an admissible modulus. -/
theorem isAdmissibleModulus_iff {𝔪 : Modulus K} :
    IsAdmissibleModulus K L 𝔪 ↔ raySubgroup 𝔪 ≤
      (ideleClassNormMap K L : IdeleClassGroup (𝓞 L) L →* IdeleClassGroup (𝓞 K) K).range :=
  Iff.rfl

/-- **Admissibility passes to multiples**: the ray subgroup shrinks as the modulus grows. -/
theorem IsAdmissibleModulus.of_dvd {𝔪 𝔫 : Modulus K} (h𝔪 : IsAdmissibleModulus K L 𝔪)
    (h : 𝔪 ∣ 𝔫) : IsAdmissibleModulus K L 𝔫 :=
  (raySubgroup_antitone h).trans h𝔪

/-- **A modulus omitting a real place is not admissible for an extension containing `μ_{pⁿ}`.**
If `L` contains a primitive `pⁿ`-th root of unity with `pⁿ > 2` and the real place `w` of `K` is
not in the infinite part of `𝔪`, then `𝔪` is not admissible for `L/K`. -/
theorem not_isAdmissibleModulus_of_forall_ne (p : ℕ) [Fact p.Prime] {𝔪 : Modulus K}
    {w : InfinitePlace K} (hw : w.IsReal) (hw𝔪 : ∀ w' ∈ 𝔪.infinitePart, (w' : InfinitePlace K) ≠ w)
    {n : ℕ} {ζ : L} (hζ : IsPrimitiveRoot ζ (p ^ n)) (hpn : 2 < p ^ n) :
    ¬ IsAdmissibleModulus K L 𝔪 := fun h ↦
  ofCompletion_neg_one_notMem_range_ideleClassNormMap K L p hw hζ hpn
    (h (ofCompletion_mem_raySubgroup hw𝔪 _))

/-- **The trivial modulus is not admissible for `ℚ(i)/ℚ`**, although the ray class group of `ℚ`
for the trivial modulus is trivial. -/
theorem not_isAdmissibleModulus_one_Qi (E : Type) [Field E] [NumberField E] [Algebra ℚ E]
    [IsCyclotomicExtension {4} ℚ E] :
    ¬ IsAdmissibleModulus ℚ E (Modulus.one ℚ) :=
  not_isAdmissibleModulus_of_forall_ne 2 Rat.isReal_infinitePlace (by simp)
    (n := 2) (IsCyclotomicExtension.zeta_spec 4 ℚ E) (by norm_num)

end TauCeti.ClassFieldTheory
