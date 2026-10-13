/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.Ideles.Norm.Range
public import TauCeti.NumberTheory.NumberField.Global.Ideles.Ray.ClassQuotient
import TauCeti.NumberTheory.LocalField.PowerSubgroup.Open
import TauCeti.RingTheory.DedekindDomain.AdicValuation.ValuativeRel

/-!
# Idele classes are norms from an extension that splits almost everywhere

Let `L/K` be an extension of number fields and `S` a finite set of finite places of `K`. If at
every finite place `v ∉ S` every unit of `K_v` is a norm from `K_v ⊗[K] L`, then every idele class
of `K` is a norm from `L`: the norm map `C_L → C_K` is surjective
(`ideleClassNormMap_surjective_of_forall_range_normUnits_eq_top`). This holds in particular when
every finite place outside `S` has a place of `L` above it with local degree one, for instance
when it splits completely in `L` (`ideleClassNormMap_surjective_of_forall_exists_finrank_eq_one`).

The proof is weak approximation. Every idele becomes, after multiplication by a principal idele,
an `n`-th power at the places of `S` and at every infinite place, for any `n ≠ 0`
(`exists_unitEmbedding_mul_mem_range_powMonoidHom`): the `n`-th powers of `K_v` contain the units
congruent to one to a sufficient level, a positive real number is an `n`-th power, and every
complex number is one. With `n = [L : K]` such a coordinate is the norm of its `n`-th root, and the
placewise norm criterion `mem_range_ideleNormMap_iff` assembles the local norms into an idele.

This is the norm half of Milne's Proposition 4.6, proved directly rather than through the density
of `K^× · I^S` in `I_K`. Together with the first fundamental inequality
`[C_K : N_{L/K} C_L] ≥ [L : K]` for cyclic `L/K`, it shows that a nontrivial solvable extension has
infinitely many places that do not split completely. That is how the Frobenius elements of an
abelian extension are seen to generate its Galois group without the Chebotarev density theorem, as
the Kummer-theoretic proof of the second fundamental inequality requires.

## Main results

* `NumberField.InfinitePlace.Completion.mem_range_powMonoidHom`: a unit of an archimedean
  completion that is positive at a real place is an `n`-th power.
* `TauCeti.GlobalNumberFields.exists_unitEmbedding_mul_mem_range_powMonoidHom`: every idele is,
  up to a principal idele, an `n`-th power at the places of `S` and at the infinite places.
* `TauCeti.GlobalNumberFields.range_powMonoidHom_le_range_normUnits_baseChange`: an `[L : K]`-th
  power is a norm from `F ⊗[K] L`.
* `TauCeti.GlobalNumberFields.range_normUnits_adicCompletion_eq_top_of_finrank_eq_one`: every unit
  of `K_v` is a local norm when some place above `v` has local degree one.
* `TauCeti.GlobalNumberFields.ideleClassNormMap_surjective_of_forall_range_normUnits_eq_top` and
  `TauCeti.GlobalNumberFields.ideleClassNormMap_surjective_of_forall_exists_finrank_eq_one`: the
  surjectivity of the idele-class norm map.

## References

* J. S. Milne, *Class Field Theory*, v4.03, Chapter VII, Lemma 4.5, Proposition 4.6 and
  Proposition 4.7.
-/

public section
noncomputable section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField NumberField.InfinitePlace
open scoped TensorProduct AdicCompletionExtension NumberField.LiesOver

/-! ### `n`-th powers at an infinite place -/

namespace NumberField.InfinitePlace.Completion

variable {K : Type*} [Field K] {w : InfinitePlace K}

/-- **Units of an archimedean completion that are positive at a real place are `n`-th powers.**
At a real place this is the existence of real `n`-th roots of positive numbers; at a complex place
every unit is an `n`-th power. -/
theorem mem_range_powMonoidHom {n : ℕ} (hn : n ≠ 0) (y : w.Completionˣ)
    (hy : ∀ hw : w.IsReal, 0 < extensionEmbeddingOfIsReal hw y) :
    y ∈ (powMonoidHom n : w.Completionˣ →* w.Completionˣ).range := by
  by_cases hw : w.IsReal
  · let e := ringEquivRealOfIsReal hw
    have hpos : 0 < e y := by simpa [e] using hy hw
    -- The real `n`-th root `(e y) ^ (1 / n)` of the positive number `e y`.
    have ht0 : e.symm (e y ^ ((n : ℝ)⁻¹)) ≠ 0 :=
      (map_ne_zero e.symm).2 (Real.rpow_pos_of_pos hpos _).ne'
    refine ⟨Units.mk0 _ ht0, Units.ext ?_⟩
    rw [powMonoidHom_apply, Units.val_pow_eq_pow_val, Units.val_mk0, ← map_pow,
      Real.rpow_inv_natCast_pow hpos.le hn, RingEquiv.symm_apply_apply]
  · let e := ringEquivComplexOfIsComplex (not_isReal_iff_isComplex.mp hw)
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (e y) (Nat.pos_of_ne_zero hn)
    have hz0 : e.symm z ≠ 0 := by
      refine (map_ne_zero e.symm).2 fun h ↦ ?_
      rw [h, zero_pow hn] at hz
      exact (map_ne_zero e).2 y.ne_zero hz.symm
    refine ⟨Units.mk0 _ hz0, Units.ext ?_⟩
    rw [powMonoidHom_apply, Units.val_pow_eq_pow_val, Units.val_mk0, ← map_pow, hz,
      RingEquiv.symm_apply_apply]

end NumberField.InfinitePlace.Completion

namespace TauCeti.GlobalNumberFields

/-! ### `n`-th powers at finitely many places -/

section Approximation

variable {K : Type*} [Field K] [NumberField K]

/-- **Every idele is an `n`-th power at finitely many places, up to a principal idele.** For a
finite set `S` of finite places and `n ≠ 0`, every idele times a suitable principal idele is an
`n`-th power at each place of `S` and at each infinite place. This is weak approximation at `S` and
the real places, through `exists_unitEmbedding_mul_mem_ideleCongrOneSubgroup` for a modulus deep
enough at `S` and divisible by every real place. -/
theorem exists_unitEmbedding_mul_mem_range_powMonoidHom (S : Finset (HeightOneSpectrum (𝓞 K)))
    {n : ℕ} (hn : n ≠ 0) (x : IdeleGroup (𝓞 K) K) :
    ∃ α : Kˣ,
      (∀ v ∈ S, v.ideleFiniteCoord (IdeleGroup.unitEmbedding (𝓞 K) K α * x) ∈
        (powMonoidHom n : (v.adicCompletion K)ˣ →* (v.adicCompletion K)ˣ).range) ∧
      ∀ w : InfinitePlace K, w.ideleInfiniteCoord (IdeleGroup.unitEmbedding (𝓞 K) K α * x) ∈
        (powMonoidHom n : w.Completionˣ →* w.Completionˣ).range := by
  -- At each finite place, the `n`-th powers contain the units congruent to one to a level `m v`.
  have hdeep (v : HeightOneSpectrum (𝓞 K)) :
      ∃ m : ℕ, ∀ y : (v.adicCompletion K)ˣ, Valued.v (y : v.adicCompletion K) = 1 →
        Valued.v ((y : v.adicCompletion K) - 1) ≤ WithZero.exp (-(m : ℤ)) →
          y ∈ (powMonoidHom n : (v.adicCompletion K)ˣ →* (v.adicCompletion K)ˣ).range := by
    let _ : Finite (𝓞 K ⧸ v.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient v.ne_bot
    obtain ⟨m, -, hm⟩ := TauCeti.hasBasis_nhds_one_unitFiltration.mem_iff.mp <|
      (TauCeti.isOpen_range_powMonoidHom
        ((Nat.cast_ne_zero (R := v.adicCompletion K)).2 hn)).mem_nhds (Subgroup.one_mem _)
    exact ⟨m, fun y hy1 hy ↦ hm ((mem_unitFiltration_adicCompletion_iff v).mpr ⟨hy1, hy⟩)⟩
  choose m hm using hdeep
  -- The modulus `∏_{v ∈ S} v ^ (m v + 1)`, divisible by every real place.
  let 𝔪 : Modulus K :=
    { finitePart := ∏ v ∈ S, v.asIdeal ^ (m v + 1)
      finitePart_ne_bot := by
        rw [← Ideal.zero_eq_bot, Finset.prod_ne_zero_iff]
        exact fun v _ ↦ pow_ne_zero _ (by simpa using v.ne_bot)
      infinitePart := (narrowModulus K).infinitePart }
  obtain ⟨α, hα⟩ := exists_unitEmbedding_mul_mem_ideleCongrOneSubgroup 𝔪 x
  obtain ⟨hfin, hinf⟩ := mem_ideleCongrOneSubgroup_iff.mp hα
  refine ⟨α, fun v hv ↦ ?_, fun w ↦ ?_⟩
  · have hpow : v.asIdeal ^ (m v + 1) ∣ 𝔪.finitePart := Finset.dvd_prod_of_mem _ hv
    have hdvd : v.asIdeal ∣ 𝔪.finitePart := (dvd_pow_self _ (Nat.succ_ne_zero _)).trans hpow
    have hexp : m v + 1 ≤ 𝔪.exponent v :=
      (Modulus.pow_dvd_finitePart_iff_le_exponent 𝔪 v).mp hpow
    refine hm v _ (𝔪.valued_eq_one_of_valued_sub_one_le hdvd (hfin v hdvd))
      ((hfin v hdvd).trans (WithZero.exp_le_exp.mpr ?_))
    omega
  · exact Completion.mem_range_powMonoidHom hn _ fun hw ↦
      hinf ⟨w, hw⟩ (mem_narrowModulus_infinitePart ⟨w, hw⟩)

end Approximation

/-! ### Surjectivity of the idele-class norm map -/

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

omit [NumberField K] [NumberField L] in
variable (K L) in
/-- **Powers by the degree are norms after base change.** For a field extension `L/K` and any
nontrivial commutative `K`-algebra `F`, an `[L : K]`-th power in `Fˣ` is the norm of a unit of
`F ⊗[K] L`, a free `F`-algebra of rank `[L : K]`. -/
theorem range_powMonoidHom_le_range_normUnits_baseChange (F : Type*) [CommRing F] [Nontrivial F]
    [Algebra K F] :
    (powMonoidHom (Module.finrank K L) : Fˣ →* Fˣ).range ≤
      (Algebra.normUnits F (S := F ⊗[K] L)).range := by
  rintro _ ⟨b, rfl⟩
  have hb := Algebra.pow_finrank_mem_range_normUnits F (S := F ⊗[K] L) b
  rwa [Module.finrank_baseChange] at hb

variable (L) in
/-- **Every unit of `K_v` is a local norm when some place above `v` has local degree one.** The
norm from `K_v ⊗[K] L` is then onto, the factor `L_w = K_v` alone providing every unit. -/
theorem range_normUnits_adicCompletion_eq_top_of_finrank_eq_one (v : HeightOneSpectrum (𝓞 K))
    (w : {w : HeightOneSpectrum (𝓞 L) // w.asIdeal.LiesOver v.asIdeal})
    (hw : Module.finrank (v.adicCompletion K) (w.1.adicCompletion L) = 1) :
    (Algebra.normUnits (v.adicCompletion K) (S := v.adicCompletion K ⊗[K] L)).range = ⊤ := by
  classical
  refine eq_top_iff.mpr fun a _ ↦ (mem_range_normUnits_adicCompletion_iff K L v a).mpr ?_
  obtain ⟨b, hb⟩ := Algebra.pow_finrank_mem_range_normUnits (v.adicCompletion K)
    (S := w.1.adicCompletion L) a
  refine ⟨Pi.mulSingle w b, ?_⟩
  rw [finprod_eq_single _ w fun w' hw' ↦ by rw [Pi.mulSingle_eq_of_ne hw', map_one],
    Pi.mulSingle_eq_same, hb, hw, pow_one]

/-- **The idele-class norm map is onto when local norms are onto outside finitely many places.**
If, at every finite place `v` of `K` outside a finite set `S`, every unit of `K_v` is a norm from
`K_v ⊗[K] L`, then every idele class of `K` is the norm of an idele class of `L`. -/
theorem ideleClassNormMap_surjective_of_forall_range_normUnits_eq_top
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : ∀ v ∉ S,
      (Algebra.normUnits (v.adicCompletion K) (S := v.adicCompletion K ⊗[K] L)).range = ⊤) :
    Function.Surjective (ideleClassNormMap K L) := by
  classical
  intro c
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective c
  obtain ⟨α, hfin, hinf⟩ := exists_unitEmbedding_mul_mem_range_powMonoidHom S
    (Module.finrank_pos (R := K) (M := L)).ne' x
  -- A `[L : K]`-th power of a local unit is a local norm.
  have hpow := range_powMonoidHom_le_range_normUnits_baseChange K L
  obtain ⟨z, hz⟩ := (mem_range_ideleNormMap_iff K L _).mpr
    ⟨fun v ↦ if hv : v ∈ S then hpow _ (hfin v hv) else by simp [hS v hv],
      fun w ↦ hpow _ (hinf w)⟩
  refine ⟨(z : IdeleClassGroup (𝓞 L) L), ?_⟩
  rw [ContinuousMonoidHom.coe_toMonoidHom] at hz
  have hα : IdeleGroup.unitEmbedding (𝓞 K) K α ∈ IdeleGroup.principalSubgroup (𝓞 K) K :=
    ⟨α, rfl⟩
  rw [ideleClassNormMap_mk, ← QuotientGroup.mk_mul_of_mem x hα, mul_comm]
  exact congrArg _ hz

/-- **Every idele class is a norm from an extension that splits almost everywhere.** If every
finite place `v` of `K` outside a finite set `S` has a place `w` of `L` above it with
`[L_w : K_v] = 1`, for instance because `v` splits completely in `L`, then the norm map
`C_L → C_K` is surjective. -/
theorem ideleClassNormMap_surjective_of_forall_exists_finrank_eq_one
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : ∀ v ∉ S, ∃ w : {w : HeightOneSpectrum (𝓞 L) // w.asIdeal.LiesOver v.asIdeal},
      Module.finrank (v.adicCompletion K) (w.1.adicCompletion L) = 1) :
    Function.Surjective (ideleClassNormMap K L) :=
  ideleClassNormMap_surjective_of_forall_range_normUnits_eq_top S fun v hv ↦
    (hS v hv).elim (range_normUnits_adicCompletion_eq_top_of_finrank_eq_one L v)

end TauCeti.GlobalNumberFields
