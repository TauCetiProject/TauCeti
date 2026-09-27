/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.Ideles.Norm.Basic
public import TauCeti.RingTheory.DedekindDomain.AdicValuation.Completion
public import TauCeti.NumberTheory.NumberField.Global.RayClass.Modulus

/-!
# The idele congruence subgroup of a modulus

Let `K` be a number field and `𝔪` a modulus of `K`.  The **idele congruence subgroup**
`ideleCongruenceSubgroup 𝔪` is the subgroup of the idele group cut out placewise by the
conditions that `𝔪` prescribes:

* at a finite place `v` dividing the finite part of `𝔪`, the coordinate is a principal unit of
  level `𝔪.exponent v`, that is, the `v`-adic valuation of `x_v - 1` is at most
  `exp (-𝔪.exponent v)`;
* at every other finite place, the coordinate is a unit of the valuation ring;
* at a real place selected by the infinite part of `𝔪`, the coordinate is positive;
* at every remaining infinite place, no condition at all.

A principal unit of positive level is a unit of the valuation ring, so an idele of the congruence
subgroup is a unit at *every* finite place: the fractional ideal it defines is trivial.  This is
`ideleCongruenceSubgroup.valued_ideleFiniteCoord_eq_one`, and it is what makes the principal
ideles of the congruence subgroup exactly the units of `𝓞 K` congruent to one modulo `𝔪`
(`unitEmbedding_mem_ideleCongruenceSubgroup_iff`).

Dropping the unit conditions away from `𝔪` gives the larger subgroup `ideleCongrOneSubgroup 𝔪` of
ideles **congruent to one modulo `𝔪`**, which imposes conditions only at the places of `𝔪`.  It is
the idelic counterpart of `congruenceSubgroup 𝔪`: a principal idele is congruent to one exactly
when its generator is (`unitEmbedding_mem_ideleCongrOneSubgroup_iff`).  Such an idele is still a
unit at every finite divisor of `𝔪`, so the fractional ideal it defines is prime to `𝔪`; this is
what lets it be sent to the ray class group.

The two structural facts about the family `𝔪 ↦ ideleCongruenceSubgroup 𝔪` are that each member
is open in the idele topology — the conditions at the finitely many places of `𝔪` are open, and
away from them the condition is membership in the open subgroup of everywhere-integral ideles —
and that the family is antitone: a larger modulus imposes stronger conditions.

## Main definitions

* `TauCeti.GlobalNumberFields.ideleCongrOneSubgroup`: the ideles congruent to one modulo a
  modulus.
* `TauCeti.GlobalNumberFields.ideleCongruenceSubgroup`: the idele congruence subgroup of a
  modulus.

## Main results

* `TauCeti.GlobalNumberFields.mem_ideleCongruenceSubgroup_iff`: the defining placewise
  conditions.
* `TauCeti.GlobalNumberFields.ideleCongruenceSubgroup.valued_ideleFiniteCoord_eq_one`: an idele
  of the congruence subgroup is a unit at every finite place.
* `TauCeti.GlobalNumberFields.ideleCongruenceSubgroup_antitone`: the congruence subgroups
  decrease as the modulus grows.
* `TauCeti.GlobalNumberFields.isOpen_ideleCongruenceSubgroup`: the congruence subgroup is open.
* `TauCeti.GlobalNumberFields.unitEmbedding_mem_ideleCongruenceSubgroup_iff`: the principal
  ideles lying in the congruence subgroup are the images of the units of `𝓞 K` congruent to one
  modulo `𝔪`.
* `TauCeti.GlobalNumberFields.mem_ideleCongruenceSubgroup_one_iff`: the trivial modulus gives the
  ideles that are units at every finite place.
* `TauCeti.GlobalNumberFields.unitEmbedding_mem_ideleCongrOneSubgroup_iff`: a principal idele is
  congruent to one exactly when its generator is.
* `TauCeti.GlobalNumberFields.ideleCongrOneSubgroup_inf_ideleCongruenceSubgroup_one`: the
  congruence subgroup consists of the ideles congruent to one that are units at every finite
  place.

## References

* J. W. S. Cassels and A. Fröhlich, eds., *Algebraic Number Theory*, Chapter II, §17.
* J. Neukirch, *Algebraic Number Theory*, Chapter VI, §1.
* S. Lang, *Algebraic Number Theory*, Chapter VII, §3.
-/

public section
noncomputable section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField
open scoped NumberField NumberField.AdeleRing

namespace TauCeti.GlobalNumberFields

variable {K : Type*} [Field K] [NumberField K]

/-- **The ideles congruent to one modulo a modulus**: the ideles that are principal units of the
prescribed level at the finite divisors of `𝔪` and positive at the real places selected by `𝔪`.
No condition is imposed at any other place.  This is the idelic counterpart of
`congruenceSubgroup 𝔪` (`unitEmbedding_mem_ideleCongrOneSubgroup_iff`). -/
def ideleCongrOneSubgroup (𝔪 : Modulus K) : Subgroup (IdeleGroup (𝓞 K) K) where
  carrier := {x |
    (∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ 𝔪.finitePart →
        Valued.v ((v.ideleFiniteCoord x : v.adicCompletion K) - 1) ≤
          WithZero.exp (-(𝔪.exponent v : ℤ))) ∧
      ∀ w ∈ 𝔪.infinitePart,
        0 < InfinitePlace.Completion.extensionEmbeddingOfIsReal w.2
          (w.1.ideleInfiniteCoord x : w.1.Completion)}
  one_mem' := ⟨fun v _ ↦ by simp, fun w _ ↦ by simp⟩
  mul_mem' := by
    rintro x y ⟨hx1, hx2⟩ ⟨hy1, hy2⟩
    refine ⟨fun v hv ↦ ?_, fun w hw ↦ ?_⟩
    · -- `xy - 1 = (x - 1) * y + (y - 1)`, and `y` is a unit at `v`.
      have hyone : Valued.v (v.ideleFiniteCoord y : v.adicCompletion K) = 1 :=
        𝔪.valued_eq_one_of_valued_sub_one_le hv (hy1 v hv)
      have hsub : (v.ideleFiniteCoord (x * y) : v.adicCompletion K) - 1 =
          ((v.ideleFiniteCoord x : v.adicCompletion K) - 1) *
            (v.ideleFiniteCoord y : v.adicCompletion K) +
            ((v.ideleFiniteCoord y : v.adicCompletion K) - 1) := by
        rw [map_mul, Units.val_mul]; ring
      rw [hsub]
      refine le_trans (Valuation.map_add _ _ _) (max_le ?_ (hy1 v hv))
      rw [map_mul, hyone, mul_one]
      exact hx1 v hv
    · rw [map_mul, Units.val_mul, map_mul]
      exact mul_pos (hx2 w hw) (hy2 w hw)
  inv_mem' := by
    rintro x ⟨hx1, hx2⟩
    refine ⟨fun v hv ↦ ?_, fun w hw ↦ ?_⟩
    · -- `x⁻¹ - 1 = -((x - 1) * x⁻¹)`, and `x` is a unit at `v`.
      have hxone : Valued.v (v.ideleFiniteCoord x : v.adicCompletion K) = 1 :=
        𝔪.valued_eq_one_of_valued_sub_one_le hv (hx1 v hv)
      have hne : (v.ideleFiniteCoord x : v.adicCompletion K) ≠ 0 :=
        (v.ideleFiniteCoord x).ne_zero
      have hsub : (v.ideleFiniteCoord x⁻¹ : v.adicCompletion K) - 1 =
          -(((v.ideleFiniteCoord x : v.adicCompletion K) - 1) *
            (v.ideleFiniteCoord x : v.adicCompletion K)⁻¹) := by
        rw [map_inv, Units.val_inv_eq_inv_val]
        field_simp
        ring
      rw [hsub, Valuation.map_neg, map_mul, map_inv₀, hxone, inv_one, mul_one]
      exact hx1 v hv
    · rw [map_inv, Units.val_inv_eq_inv_val, map_inv₀]
      exact inv_pos.mpr (hx2 w hw)

/-- **The placewise conditions defining the ideles congruent to one.** -/
@[simp] theorem mem_ideleCongrOneSubgroup_iff {𝔪 : Modulus K} {x : IdeleGroup (𝓞 K) K} :
    x ∈ ideleCongrOneSubgroup 𝔪 ↔
      (∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ 𝔪.finitePart →
          Valued.v ((v.ideleFiniteCoord x : v.adicCompletion K) - 1) ≤
            WithZero.exp (-(𝔪.exponent v : ℤ))) ∧
        ∀ w ∈ 𝔪.infinitePart,
          0 < InfinitePlace.Completion.extensionEmbeddingOfIsReal w.2
            (w.1.ideleInfiniteCoord x : w.1.Completion) :=
  Iff.rfl

/-- The trivial modulus imposes no congruence conditions on an idele. -/
@[simp] theorem ideleCongrOneSubgroup_one :
    ideleCongrOneSubgroup (Modulus.one K) = ⊤ := by
  apply eq_top_iff.mpr
  intro x _
  rw [mem_ideleCongrOneSubgroup_iff]
  constructor
  · intro v hv
    exact (v.prime.not_dvd_one (by
      simpa [Modulus.one_finitePart, ← Ideal.one_eq_top] using hv)).elim
  · simp [Modulus.one_infinitePart]

/-- **An idele congruent to one is a unit at every finite divisor of the modulus**, because the
prescribed exponent there is positive. -/
theorem ideleCongrOneSubgroup.valued_ideleFiniteCoord_eq_one {𝔪 : Modulus K}
    {x : IdeleGroup (𝓞 K) K} (hx : x ∈ ideleCongrOneSubgroup 𝔪) {v : HeightOneSpectrum (𝓞 K)}
    (hv : v.asIdeal ∣ 𝔪.finitePart) :
    Valued.v (v.ideleFiniteCoord x : v.adicCompletion K) = 1 :=
  𝔪.valued_eq_one_of_valued_sub_one_le hv (hx.1 v hv)

/-- **The ideles congruent to one decrease as the modulus grows.** -/
theorem ideleCongrOneSubgroup_antitone {𝔪 𝔫 : Modulus K} (h : 𝔪 ∣ 𝔫) :
    ideleCongrOneSubgroup 𝔫 ≤ ideleCongrOneSubgroup 𝔪 := by
  rintro x ⟨hx1, hx2⟩
  refine ⟨fun v hv ↦ (hx1 v (hv.trans (Modulus.dvd_iff.mp h).1)).trans ?_,
    fun w hw ↦ hx2 w ((Modulus.dvd_iff.mp h).2 hw)⟩
  exact WithZero.exp_le_exp.mpr (by
    simpa using Nat.cast_le (α := ℤ) |>.mpr (Modulus.exponent_mono h v))

/-- **The idele congruence subgroup of a modulus**: the ideles congruent to one modulo `𝔪` that
are moreover units of the valuation ring at the finite places not dividing `𝔪`.  Explicitly, they
are principal units of the prescribed level at the finite divisors of `𝔪`, units of the valuation
ring at the remaining finite places, and positive at the real places selected by `𝔪`.  No
condition is imposed at the infinite places outside `𝔪`. -/
def ideleCongruenceSubgroup (𝔪 : Modulus K) : Subgroup (IdeleGroup (𝓞 K) K) where
  carrier := {x |
    (∀ v : HeightOneSpectrum (𝓞 K), ¬ v.asIdeal ∣ 𝔪.finitePart →
        Valued.v (v.ideleFiniteCoord x : v.adicCompletion K) = 1) ∧
      x ∈ ideleCongrOneSubgroup 𝔪}
  one_mem' := ⟨fun v _ ↦ by simp, (ideleCongrOneSubgroup 𝔪).one_mem⟩
  mul_mem' := by
    rintro x y ⟨hx1, hx⟩ ⟨hy1, hy⟩
    refine ⟨fun v hv ↦ ?_, (ideleCongrOneSubgroup 𝔪).mul_mem hx hy⟩
    rw [map_mul, Units.val_mul, map_mul, hx1 v hv, hy1 v hv, one_mul]
  inv_mem' := by
    rintro x ⟨hx1, hx⟩
    refine ⟨fun v hv ↦ ?_, (ideleCongrOneSubgroup 𝔪).inv_mem hx⟩
    rw [map_inv, Units.val_inv_eq_inv_val, map_inv₀, hx1 v hv, inv_one]

/-- **The placewise conditions defining the idele congruence subgroup.** -/
@[simp] theorem mem_ideleCongruenceSubgroup_iff {𝔪 : Modulus K} {x : IdeleGroup (𝓞 K) K} :
    x ∈ ideleCongruenceSubgroup 𝔪 ↔
      (∀ v : HeightOneSpectrum (𝓞 K), ¬ v.asIdeal ∣ 𝔪.finitePart →
          Valued.v (v.ideleFiniteCoord x : v.adicCompletion K) = 1) ∧
        (∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ 𝔪.finitePart →
          Valued.v ((v.ideleFiniteCoord x : v.adicCompletion K) - 1) ≤
            WithZero.exp (-(𝔪.exponent v : ℤ))) ∧
        ∀ w ∈ 𝔪.infinitePart,
          0 < InfinitePlace.Completion.extensionEmbeddingOfIsReal w.2
            (w.1.ideleInfiniteCoord x : w.1.Completion) :=
  Iff.rfl

namespace ideleCongruenceSubgroup

variable {𝔪 : Modulus K} {x : IdeleGroup (𝓞 K) K}

theorem valued_ideleFiniteCoord_sub_one_le (hx : x ∈ ideleCongruenceSubgroup 𝔪)
    {v : HeightOneSpectrum (𝓞 K)} (hv : v.asIdeal ∣ 𝔪.finitePart) :
    Valued.v ((v.ideleFiniteCoord x : v.adicCompletion K) - 1) ≤
      WithZero.exp (-(𝔪.exponent v : ℤ)) :=
  (mem_ideleCongruenceSubgroup_iff.mp hx).2.1 v hv

theorem extensionEmbeddingOfIsReal_pos (hx : x ∈ ideleCongruenceSubgroup 𝔪)
    {w : {w : InfinitePlace K // w.IsReal}} (hw : w ∈ 𝔪.infinitePart) :
    0 < InfinitePlace.Completion.extensionEmbeddingOfIsReal w.2
      (w.1.ideleInfiniteCoord x : w.1.Completion) :=
  (mem_ideleCongruenceSubgroup_iff.mp hx).2.2 w hw

/-- **An idele of the congruence subgroup is a unit at every finite place.**  Away from the finite
part this is the defining condition, and at a divisor of the finite part it follows from the
congruence, because the prescribed exponent there is positive. -/
theorem valued_ideleFiniteCoord_eq_one (hx : x ∈ ideleCongruenceSubgroup 𝔪)
    (v : HeightOneSpectrum (𝓞 K)) :
    Valued.v (v.ideleFiniteCoord x : v.adicCompletion K) = 1 := by
  by_cases hv : v.asIdeal ∣ 𝔪.finitePart
  · exact 𝔪.valued_eq_one_of_valued_sub_one_le hv (valued_ideleFiniteCoord_sub_one_le hx hv)
  · exact (mem_ideleCongruenceSubgroup_iff.mp hx).1 v hv

/-- **The finite components of a congruence idele are integral**: at every finite place `v`, the
`v`-component of the underlying adele lies in the valuation ring. -/
theorem snd_mem_adicCompletionIntegers (hx : x ∈ ideleCongruenceSubgroup 𝔪)
    (v : HeightOneSpectrum (𝓞 K)) : (x : 𝔸[K]).2 v ∈ v.adicCompletionIntegers K := by
  rw [mem_adicCompletionIntegers, ← coe_ideleFiniteCoord]
  exact (valued_ideleFiniteCoord_eq_one hx v).le

/-- **The congruence condition on the underlying adele**: if `v ^ n` divides the finite part of
`𝔪`, then the `v`-component of a congruence idele is congruent to `1` to level `n`.  For `n = 0`
this is the integrality of the component. -/
theorem valued_snd_sub_one_le_of_pow_dvd (hx : x ∈ ideleCongruenceSubgroup 𝔪)
    {v : HeightOneSpectrum (𝓞 K)} {n : ℕ} (hn : v.asIdeal ^ n ∣ 𝔪.finitePart) :
    Valued.v ((x : 𝔸[K]).2 v - 1) ≤ WithZero.exp (-(n : ℤ)) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn0
  · have h := sub_mem (snd_mem_adicCompletionIntegers hx v) (one_mem (v.adicCompletionIntegers K))
    rw [mem_adicCompletionIntegers] at h
    simpa using h
  · rw [← coe_ideleFiniteCoord]
    refine (valued_ideleFiniteCoord_sub_one_le hx ((dvd_pow_self _ hn0.ne').trans hn)).trans
      (WithZero.exp_le_exp.mpr ?_)
    have := (𝔪.pow_dvd_finitePart_iff_le_exponent v).mp hn
    omega

end ideleCongruenceSubgroup

/-- **The idele congruence subgroups decrease as the modulus grows.** -/
theorem ideleCongruenceSubgroup_antitone {𝔪 𝔫 : Modulus K} (h : 𝔪 ∣ 𝔫) :
    ideleCongruenceSubgroup 𝔫 ≤ ideleCongruenceSubgroup 𝔪 := fun _ hx ↦
  ⟨fun v _ ↦ ideleCongruenceSubgroup.valued_ideleFiniteCoord_eq_one hx v,
    ideleCongrOneSubgroup_antitone h hx.2⟩

/-- **The idele congruence subgroup lies in the ideles congruent to one.** -/
theorem ideleCongruenceSubgroup_le_ideleCongrOneSubgroup (𝔪 : Modulus K) :
    ideleCongruenceSubgroup 𝔪 ≤ ideleCongrOneSubgroup 𝔪 := fun _ hx ↦ hx.2

/-! ### Openness -/

/-- **The idele congruence subgroup is open.**  Away from the modulus the condition is membership
in the open subring of everywhere-integral adeles, at the finitely many finite divisors of `𝔪` it
is a closed valuation ball, and at the finitely many selected real places it is a strict
inequality; imposing the same conditions on `x` and on `x⁻¹` turns the integrality conditions into
the unit conditions. -/
theorem isOpen_ideleCongruenceSubgroup (𝔪 : Modulus K) :
    IsOpen (ideleCongruenceSubgroup 𝔪 : Set (IdeleGroup (𝓞 K) K)) := by
  classical
  -- The three conditions are open on the adele ring; an idele satisfies the congruence conditions
  -- exactly when both it and its inverse satisfy the adelic ones.
  set A : Set 𝔸[K] :=
    {a | ∀ v : HeightOneSpectrum (𝓞 K), a.2 v ∈ v.adicCompletionIntegers K} ∩
      ({a | ∀ v ∈ 𝔪.support, Valued.v ((a.2 v : v.adicCompletion K) - 1) ≤
          WithZero.exp (-(𝔪.exponent v : ℤ))} ∩
        {a | ∀ w ∈ 𝔪.infinitePart,
          0 < InfinitePlace.Completion.extensionEmbeddingOfIsReal w.2 (a.1 w.1)})
  have hAopen : IsOpen A := by
    refine IsOpen.inter ?_ (IsOpen.inter ?_ ?_)
    · exact (RestrictedProduct.isOpen_forall_mem fun v ↦
        Valued.isOpen_valuationSubring _).preimage continuous_snd
    · have h : {a : 𝔸[K] | ∀ v ∈ 𝔪.support, Valued.v ((a.2 v : v.adicCompletion K) - 1) ≤
            WithZero.exp (-(𝔪.exponent v : ℤ))} =
          ⋂ v ∈ 𝔪.support, (fun a : 𝔸[K] ↦ (a.2 v : v.adicCompletion K) - 1) ⁻¹'
            {z : v.adicCompletion K | Valued.v z ≤ WithZero.exp (-(𝔪.exponent v : ℤ))} := by
        ext a; simp
      rw [h]
      exact isOpen_biInter_finset fun v _ ↦
        (v.isOpen_setOf_valued_le (K := K) WithZero.exp_ne_zero).preimage
          (((RestrictedProduct.continuous_eval v).comp continuous_snd).sub continuous_const)
    · have h : {a : 𝔸[K] | ∀ w ∈ 𝔪.infinitePart,
            0 < InfinitePlace.Completion.extensionEmbeddingOfIsReal w.2 (a.1 w.1)} =
          ⋂ w ∈ 𝔪.infinitePart, {a : 𝔸[K] |
            0 < InfinitePlace.Completion.extensionEmbeddingOfIsReal w.2 (a.1 w.1)} := by
        ext a; simp
      rw [h]
      exact isOpen_biInter_finset fun w _ ↦ isOpen_lt continuous_const
        ((InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal w.2).continuous.comp
          ((continuous_apply w.1).comp continuous_fst))
  have hmemA : ∀ x ∈ ideleCongruenceSubgroup 𝔪, (x : 𝔸[K]) ∈ A := by
    intro x hx
    refine ⟨fun v ↦ ?_, fun v hv ↦ ?_, fun w hw ↦ ?_⟩
    · exact ideleCongruenceSubgroup.snd_mem_adicCompletionIntegers hx v
    · exact ideleCongruenceSubgroup.valued_snd_sub_one_le_of_pow_dvd hx
        (𝔪.pow_exponent_dvd_finitePart v)
    · rw [← InfinitePlace.coe_ideleInfiniteCoord]
      exact ideleCongruenceSubgroup.extensionEmbeddingOfIsReal_pos hx hw
  have hset : (ideleCongruenceSubgroup 𝔪 : Set (IdeleGroup (𝓞 K) K)) =
      (fun x : IdeleGroup (𝓞 K) K ↦ (x : 𝔸[K])) ⁻¹' A ∩
        (fun x : IdeleGroup (𝓞 K) K ↦ ((x⁻¹ : IdeleGroup (𝓞 K) K) : 𝔸[K])) ⁻¹' A := by
    ext x
    refine ⟨fun hx ↦ ⟨hmemA x hx, hmemA x⁻¹ ((ideleCongruenceSubgroup 𝔪).inv_mem hx)⟩, ?_⟩
    rintro ⟨⟨hx1, hx2, hx3⟩, hy1, -, -⟩
    refine mem_ideleCongruenceSubgroup_iff.mpr ⟨fun v _ ↦ ?_, fun v hv ↦ ?_, fun w hw ↦ ?_⟩
    · -- the coordinate and its inverse are both integral, so the coordinate is a local unit
      have hne : Valued.v (v.ideleFiniteCoord x : v.adicCompletion K) ≠ 0 := by
        simpa using (v.ideleFiniteCoord x).ne_zero
      refine le_antisymm (by
        simpa [mem_adicCompletionIntegers, HeightOneSpectrum.coe_ideleFiniteCoord] using
          hx1 v) ?_
      have hinv := hy1 v
      rw [mem_adicCompletionIntegers, ← HeightOneSpectrum.coe_ideleFiniteCoord, map_inv,
        Units.val_inv_eq_inv_val, map_inv₀] at hinv
      exact (inv_le_one₀ (zero_lt_iff.mpr hne)).mp hinv
    · rw [HeightOneSpectrum.coe_ideleFiniteCoord]
      exact hx2 v ((Modulus.mem_support_iff 𝔪 v).mpr hv)
    · rw [InfinitePlace.coe_ideleInfiniteCoord]
      exact hx3 w hw
  rw [hset]
  exact (hAopen.preimage Units.continuous_val).inter
    (hAopen.preimage (Units.continuous_val.comp continuous_inv))

/-! ### Principal ideles and the trivial modulus -/

/-- **The principal ideles congruent to one are the elements congruent to one.**  At a finite
divisor of `𝔪` the coordinate of a principal idele is the global element, whose valuation in the
completion is its `v`-adic valuation, and at a real place its sign is that of the real embedding. -/
-- The placewise membership and coordinate simp lemmas already normalize the left-hand side.
theorem unitEmbedding_mem_ideleCongrOneSubgroup_iff {𝔪 : Modulus K} {x : Kˣ} :
    IdeleGroup.unitEmbedding (𝓞 K) K x ∈ ideleCongrOneSubgroup 𝔪 ↔ IsCongrOne 𝔪 x := by
  have hsub : ∀ v : HeightOneSpectrum (𝓞 K),
      Valued.v ((v.ideleFiniteCoord (IdeleGroup.unitEmbedding (𝓞 K) K x) :
          v.adicCompletion K) - 1) = v.valuation K ((x : K) - 1) := by
    intro v
    rw [HeightOneSpectrum.ideleFiniteCoord_unitEmbedding, Units.coe_map]
    simp only [MonoidHom.coe_ofClass, RingHom.toMonoidHom_eq_coe]
    rw [← map_one (algebraMap K (v.adicCompletion K)), ← map_sub]
    simp only [HeightOneSpectrum.algebraMap_adicCompletion, Function.comp_apply,
      Algebra.algebraMap_self_apply, valuedAdicCompletion_eq_valuation']
  have hinf : ∀ w : {w : InfinitePlace K // w.IsReal},
      InfinitePlace.Completion.extensionEmbeddingOfIsReal w.2
        (w.1.ideleInfiniteCoord (IdeleGroup.unitEmbedding (𝓞 K) K x) : w.1.Completion) =
        InfinitePlace.embedding_of_isReal w.2 (x : K) := by
    intro w
    rw [InfinitePlace.ideleInfiniteCoord_unitEmbedding]
    simp
  simp only [mem_ideleCongrOneSubgroup_iff, hsub, hinf, isCongrOne_iff]

/-- **The principal ideles of the congruence subgroup are the congruence units.**  A principal
idele lies in `ideleCongruenceSubgroup 𝔪` exactly when its generator is the image of a unit of
`𝓞 K` congruent to one modulo `𝔪`: the local unit conditions force the generator to be integral
together with its inverse, and what is left of the conditions is `IsCongrOne 𝔪`. -/
theorem unitEmbedding_mem_ideleCongruenceSubgroup_iff {𝔪 : Modulus K} {x : Kˣ} :
    IdeleGroup.unitEmbedding (𝓞 K) K x ∈ ideleCongruenceSubgroup 𝔪 ↔
      x ∈ (unitsCongruenceSubgroup 𝔪).map (Units.map (algebraMap (𝓞 K) K).toMonoidHom) := by
  have hcoord : ∀ v : HeightOneSpectrum (𝓞 K),
      (v.ideleFiniteCoord (IdeleGroup.unitEmbedding (𝓞 K) K x) : v.adicCompletion K) =
        algebraMap K (v.adicCompletion K) (x : K) := by
    intro v
    rw [HeightOneSpectrum.ideleFiniteCoord_unitEmbedding]
    simp
  have hval : ∀ (v : HeightOneSpectrum (𝓞 K)) (k : K),
      Valued.v (algebraMap K (v.adicCompletion K) k) = v.valuation K k := fun v k ↦ by
    simp only [HeightOneSpectrum.algebraMap_adicCompletion, Function.comp_apply,
      Algebra.algebraMap_self_apply, valuedAdicCompletion_eq_valuation']
  rw [Subgroup.mem_map]
  constructor
  · intro hx
    have hone : ∀ v : HeightOneSpectrum (𝓞 K), v.valuation K (x : K) = 1 := by
      intro v
      rw [← hval v, ← hcoord v]
      exact ideleCongruenceSubgroup.valued_ideleFiniteCoord_eq_one hx v
    obtain ⟨a, ha⟩ := mem_integers_of_valuation_le_one K (x : K) fun v ↦ (hone v).le
    obtain ⟨b, hb⟩ := mem_integers_of_valuation_le_one K ((x⁻¹ : Kˣ) : K) fun v ↦ by
      rw [Units.val_inv_eq_inv_val, map_inv₀, hone v, inv_one]
    have hinj := IsFractionRing.injective (𝓞 K) K
    have hab : a * b = 1 := hinj (by rw [map_mul, ha, hb, map_one]; simp)
    have hba : b * a = 1 := by rw [mul_comm]; exact hab
    have hu : Units.map (algebraMap (𝓞 K) K).toMonoidHom (⟨a, b, hab, hba⟩ : (𝓞 K)ˣ) = x :=
      Units.ext (by simpa using ha)
    refine ⟨⟨a, b, hab, hba⟩, ?_, hu⟩
    rw [mem_unitsCongruenceSubgroup, hu]
    exact unitEmbedding_mem_ideleCongrOneSubgroup_iff.mp hx.2
  · rintro ⟨u, hu, rfl⟩
    rw [mem_unitsCongruenceSubgroup] at hu
    refine ⟨fun v _ ↦ ?_, unitEmbedding_mem_ideleCongrOneSubgroup_iff.mpr hu⟩
    rw [hcoord v, hval]
    exact (v.valuation_eq_one_iff_notMem (K := K)).mpr fun h ↦
      v.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h u.isUnit)

/-- **The trivial modulus gives the ideles that are units at every finite place.**  No prime
divides the unit ideal and the infinite part is empty, so only the local unit conditions
survive. -/
theorem mem_ideleCongruenceSubgroup_one_iff {x : IdeleGroup (𝓞 K) K} :
    x ∈ ideleCongruenceSubgroup (Modulus.one K) ↔
      ∀ v : HeightOneSpectrum (𝓞 K),
        Valued.v (v.ideleFiniteCoord x : v.adicCompletion K) = 1 := by
  refine ⟨fun hx v ↦ ideleCongruenceSubgroup.valued_ideleFiniteCoord_eq_one hx v, fun hx ↦ ?_⟩
  refine mem_ideleCongruenceSubgroup_iff.mpr
    ⟨fun v _ ↦ hx v, fun v hv ↦ ?_, fun w hw ↦ absurd hw (by simp)⟩
  exact absurd ((Modulus.mem_support_iff _ v).mpr hv) (by simp)

/-- **The idele congruence subgroup consists of the ideles congruent to one that are units at every
finite place.** -/
theorem ideleCongrOneSubgroup_inf_ideleCongruenceSubgroup_one (𝔪 : Modulus K) :
    ideleCongrOneSubgroup 𝔪 ⊓ ideleCongruenceSubgroup (Modulus.one K) =
      ideleCongruenceSubgroup 𝔪 := by
  ext x
  rw [Subgroup.mem_inf, mem_ideleCongruenceSubgroup_one_iff]
  exact ⟨fun ⟨hx, h⟩ ↦ ⟨fun v _ ↦ h v, hx⟩,
    fun hx ↦ ⟨hx.2, ideleCongruenceSubgroup.valued_ideleFiniteCoord_eq_one hx⟩⟩

end TauCeti.GlobalNumberFields
