/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.Ideles.FiniteIdeal
public import TauCeti.NumberTheory.NumberField.Global.Ideles.Ray.Subgroup
public import Mathlib.GroupTheory.Index

/-!
# The auxiliary Kummer idele subgroup and its local index

For finite sets `S` and `T` of finite places, `auxiliaryKummerIdeleSubgroup S T n` consists of
the ideles whose coordinates are `n`-th powers at `S` and at every infinite place, and integral
units outside `S ∪ T`. Thus coordinates are unrestricted at `T \ S`, while the power condition
still applies on `S ∩ T`. At exponent one it is the full group of `(S ∪ T)`-ideles. The index of
the exponent-`n` subgroup in that group is the product of the local power-class counts over `S`
and the infinite places. No roots-of-unity hypothesis is needed for this identity.

If the primes in `S ∪ T` generate the ideal class group, every idele class has an `(S ∪ T)`-idele
representative, unique up to the principal ideles of the `(S ∪ T)`-units. Consequently the index
of the image of the auxiliary Kummer subgroup in the idele class group, multiplied by the index in
the `(S ∪ T)`-units of those whose principal ideles lie in the auxiliary subgroup, is the same
product (`index_auxiliaryKummerIdeleClassSubgroup_mul_relIndex`); in particular the index divides
it.

A subgroup of the idele class group containing the `n`-th powers and the ray subgroup of a modulus
whose finite part is supported in `S` contains the image of the exponent-`n` subgroup for `T = ∅`
(`auxiliaryKummerIdeleClassSubgroup_le_of_raySubgroup_le`): every such idele is an `n`-th power
times an idele congruent to one modulo the modulus.

## References

* J. S. Milne, *Class Field Theory*, Chapter VII, §§5--6 and 9.
-/

public noncomputable section

open IsDedekindDomain NumberField

namespace TauCeti.ClassFieldTheory

variable {K : Type*} [Field K] [NumberField K]

/-- The auxiliary Kummer idele subgroup: local `n`-th powers at `S` and all infinite places,
arbitrary coordinates at `T \ S`, and integral units outside `S ∪ T`. The power condition still
applies at places in `S ∩ T`. -/
def auxiliaryKummerIdeleSubgroup (S T : Finset (HeightOneSpectrum (𝓞 K))) (n : ℕ) :
    Subgroup (IdeleGroup (𝓞 K) K) :=
  (⨅ v : S, (powMonoidHom n).range.comap v.1.ideleFiniteCoord) ⊓
    (⨅ w : InfinitePlace K, (powMonoidHom n).range.comap w.ideleInfiniteCoord) ⊓
    ⨅ v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S ∧ v ∉ T},
      (v.1.adicCompletionIntegers K).units.comap v.1.ideleFiniteCoord

/-- Membership is given by the local power conditions at `S` and infinity and the integral-unit
condition outside `S ∪ T`. -/
@[simp]
theorem mem_auxiliaryKummerIdeleSubgroup_iff
    (S T : Finset (HeightOneSpectrum (𝓞 K))) (n : ℕ) (x : IdeleGroup (𝓞 K) K) :
    x ∈ auxiliaryKummerIdeleSubgroup S T n ↔
      (∀ v ∈ S, v.ideleFiniteCoord x ∈ (powMonoidHom n).range) ∧
      (∀ w : InfinitePlace K, w.ideleInfiniteCoord x ∈ (powMonoidHom n).range) ∧
      ∀ v ∉ S, v ∉ T → Valued.v (v.ideleFiniteCoord x : v.adicCompletion K) = 1 := by
  simp [auxiliaryKummerIdeleSubgroup, Subgroup.mem_iInf,
    HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one, and_assoc]

/-- At exponent one the auxiliary Kummer subgroup is the full group of `(S ∪ T)`-ideles. -/
theorem mem_auxiliaryKummerIdeleSubgroup_one_iff
    (S T : Finset (HeightOneSpectrum (𝓞 K))) (x : IdeleGroup (𝓞 K) K) :
    x ∈ auxiliaryKummerIdeleSubgroup S T 1 ↔
      ∀ v ∉ S, v ∉ T → Valued.v (v.ideleFiniteCoord x : v.adicCompletion K) = 1 := by
  simp

/-- At exponent one, membership in the auxiliary Kummer subgroup is the unit condition outside
the union `S ∪ T`. -/
theorem mem_auxiliaryKummerIdeleSubgroup_one_iff_union
    (S T : Finset (HeightOneSpectrum (𝓞 K))) (x : IdeleGroup (𝓞 K) K) :
    x ∈ auxiliaryKummerIdeleSubgroup S T 1 ↔
      ∀ v ∉ ((S : Set (HeightOneSpectrum (𝓞 K))) ∪ T),
        Valued.v (v.ideleFiniteCoord x : v.adicCompletion K) = 1 := by
  rw [mem_auxiliaryKummerIdeleSubgroup_one_iff]
  constructor
  · exact fun h v hv ↦ h v (fun hvS ↦ hv (Or.inl hvS)) fun hvT ↦ hv (Or.inr hvT)
  · exact fun h v hvS hvT ↦ h v fun hv ↦ hv.elim hvS hvT

/-- The principal idele of `a` lies in the exponent-one auxiliary Kummer subgroup exactly when
`a` is an `(S ∪ T)`-unit. -/
theorem unitEmbedding_mem_auxiliaryKummerIdeleSubgroup_one_iff
    (S T : Finset (HeightOneSpectrum (𝓞 K))) (a : Kˣ) :
    IdeleGroup.unitEmbedding (𝓞 K) K a ∈ auxiliaryKummerIdeleSubgroup S T 1 ↔
      a ∈ ((S : Set (HeightOneSpectrum (𝓞 K))) ∪ T).unit K := by
  rw [mem_auxiliaryKummerIdeleSubgroup_one_iff_union,
    IdeleGroup.forall_valued_ideleFiniteCoord_unitEmbedding_eq_one_iff]

/-- Every auxiliary Kummer idele is an `(S ∪ T)`-idele. -/
theorem auxiliaryKummerIdeleSubgroup_le_one
    (S T : Finset (HeightOneSpectrum (𝓞 K))) (n : ℕ) :
    auxiliaryKummerIdeleSubgroup S T n ≤ auxiliaryKummerIdeleSubgroup S T 1 := by
  intro x hx
  exact (mem_auxiliaryKummerIdeleSubgroup_one_iff S T x).mpr
    ((mem_auxiliaryKummerIdeleSubgroup_iff S T n x).mp hx).2.2

private abbrev LocalPowerClasses (S : Finset (HeightOneSpectrum (𝓞 K))) (n : ℕ) :=
  (∀ v : S, (v.1.adicCompletion K)ˣ ⧸ (powMonoidHom n).range) ×
    (∀ w : InfinitePlace K, w.Completionˣ ⧸ (powMonoidHom n).range)

private def localPowerClassMap
    (S T : Finset (HeightOneSpectrum (𝓞 K))) (n : ℕ) :
    auxiliaryKummerIdeleSubgroup S T 1 →* LocalPowerClasses S n where
  toFun x := (fun v ↦ QuotientGroup.mk (v.1.ideleFiniteCoord x.1),
    fun w ↦ QuotientGroup.mk (w.ideleInfiniteCoord x.1))
  map_one' := by ext <;> simp
  map_mul' x y := by ext <;> simp [QuotientGroup.mk_mul]

private theorem localPowerClassMap_apply
    (S T : Finset (HeightOneSpectrum (𝓞 K))) (n : ℕ)
    (x : auxiliaryKummerIdeleSubgroup S T 1) :
    localPowerClassMap S T n x =
      (fun v ↦ QuotientGroup.mk (v.1.ideleFiniteCoord x.1),
        fun w ↦ QuotientGroup.mk (w.ideleInfiniteCoord x.1)) :=
  (rfl)

private theorem localPowerClassMap_surjective
    (S T : Finset (HeightOneSpectrum (𝓞 K))) (n : ℕ) :
    Function.Surjective (localPowerClassMap S T n) := by
  classical
  rintro ⟨xf, xi⟩
  choose z hz using fun v : S ↦ QuotientGroup.mk_surjective (xf v)
  choose zi hzi using fun w : InfinitePlace K ↦ QuotientGroup.mk_surjective (xi w)
  let zf (v : HeightOneSpectrum (𝓞 K)) : (v.adicCompletion K)ˣ :=
    if hv : v ∈ S then z ⟨v, hv⟩ else 1
  have hzfu : ∀ᶠ v in Filter.cofinite, zf v ∈ (v.adicCompletionIntegers K).units :=
    S.eventually_cofinite_notMem.mono fun v hv ↦ by simp [zf, hv]
  let x := GlobalNumberFields.ideleOfUnits zi zf hzfu
  have hx : x ∈ auxiliaryKummerIdeleSubgroup S T 1 := by
    rw [mem_auxiliaryKummerIdeleSubgroup_one_iff]
    intro v hvS _
    simp [x, zf, hvS]
  refine ⟨⟨x, hx⟩, ?_⟩
  apply Prod.ext
  · funext v
    simpa [localPowerClassMap, x, zf, v.2] using hz v
  · funext w
    simpa [localPowerClassMap, x] using hzi w

private theorem ker_localPowerClassMap
    (S T : Finset (HeightOneSpectrum (𝓞 K))) (n : ℕ) :
    (localPowerClassMap S T n).ker =
      (auxiliaryKummerIdeleSubgroup S T n).subgroupOf
        (auxiliaryKummerIdeleSubgroup S T 1) := by
  ext x
  have hx := (mem_auxiliaryKummerIdeleSubgroup_one_iff S T x.1).mp x.2
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, localPowerClassMap_apply]
  simp only [mem_auxiliaryKummerIdeleSubgroup_iff, Prod.ext_iff, funext_iff, Prod.fst_one,
    Prod.snd_one, Pi.one_apply, QuotientGroup.eq_one_iff]
  constructor
  · rintro ⟨hf, hi⟩
    exact ⟨fun v hv ↦ hf ⟨v, hv⟩, hi, hx⟩
  · rintro ⟨hf, hi, -⟩
    exact ⟨fun v ↦ hf v.1 v.2, hi⟩

/-- The relative index of the auxiliary Kummer subgroup in the `(S ∪ T)`-ideles is the product
of the finite power-class counts over `S` and the infinite power-class counts. As usual,
`Nat.card` and the index are zero for an infinite quotient. -/
theorem relIndex_auxiliaryKummerIdeleSubgroup
    (S T : Finset (HeightOneSpectrum (𝓞 K))) (n : ℕ) :
    (auxiliaryKummerIdeleSubgroup S T n).relIndex
        (auxiliaryKummerIdeleSubgroup S T 1) =
      (∏ v ∈ S, Nat.card ((v.adicCompletion K)ˣ ⧸ (powMonoidHom n).range)) *
        ∏ w : InfinitePlace K, Nat.card (w.Completionˣ ⧸ (powMonoidHom n).range) := by
  rw [Subgroup.relIndex, ← ker_localPowerClassMap]
  calc
    _ = Nat.card (LocalPowerClasses S n) := Nat.card_congr
      (QuotientGroup.quotientKerEquivOfSurjective (localPowerClassMap S T n)
        (localPowerClassMap_surjective S T n)).toEquiv
    _ = _ := by
      rw [Nat.card_prod, Nat.card_pi, Nat.card_pi]
      congr 1
      exact Finset.prod_coe_sort S
        (fun v ↦ Nat.card ((v.adicCompletion K)ˣ ⧸
          (powMonoidHom n : (v.adicCompletion K)ˣ →* _).range))

/-- The image of the auxiliary Kummer idele subgroup in the idele class group. -/
def auxiliaryKummerIdeleClassSubgroup
    (S T : Finset (HeightOneSpectrum (𝓞 K))) (n : ℕ) :
    Subgroup (IdeleClassGroup (𝓞 K) K) :=
  (auxiliaryKummerIdeleSubgroup S T n).map
    (QuotientGroup.mk' (IdeleGroup.principalSubgroup (𝓞 K) K))

/-- An idele class lies in the auxiliary Kummer subgroup exactly when it has a representative
in the corresponding idele subgroup. -/
@[simp]
theorem mem_auxiliaryKummerIdeleClassSubgroup_iff
    (S T : Finset (HeightOneSpectrum (𝓞 K))) (n : ℕ)
    (c : IdeleClassGroup (𝓞 K) K) :
    c ∈ auxiliaryKummerIdeleClassSubgroup S T n ↔
      ∃ x ∈ auxiliaryKummerIdeleSubgroup S T n,
        (x : IdeleClassGroup (𝓞 K) K) = c :=
  (Iff.rfl)

/-- The principal ideles that are integral units outside `S ∪ T` are the principal ideles of the
`(S ∪ T)`-units. -/
private theorem principalSubgroup_inf_auxiliaryKummerIdeleSubgroup_one
    (S T : Finset (HeightOneSpectrum (𝓞 K))) :
    IdeleGroup.principalSubgroup (𝓞 K) K ⊓ auxiliaryKummerIdeleSubgroup S T 1 =
      (((S : Set (HeightOneSpectrum (𝓞 K))) ∪ T).unit K).map
        (IdeleGroup.unitEmbedding (𝓞 K) K) := by
  ext x
  rw [Subgroup.mem_inf, Subgroup.mem_map]
  constructor
  · rintro ⟨hP, hx⟩
    exact (IdeleGroup.mem_principalSubgroup_iff_exists_mem_unit
      ((mem_auxiliaryKummerIdeleSubgroup_one_iff_union S T x).mp hx)).1 hP
  · rintro ⟨a, ha, rfl⟩
    exact ⟨⟨a, rfl⟩, (unitEmbedding_mem_auxiliaryKummerIdeleSubgroup_one_iff S T a).2 ha⟩

/-- **The index of the auxiliary Kummer idele classes.** If the classes of `S ∪ T` generate the
ideal class group, then
`[C_K : E_{S,T} Kˣ / Kˣ] · [U_{S∪T} : U_{S∪T} ∩ E_{S,T}] = [I_{S∪T} : E_{S,T}]`,
where `I_{S∪T}` is the group of `(S ∪ T)`-ideles, `U_{S∪T}` is the group of `(S ∪ T)`-units, and
an `(S ∪ T)`-unit lies in `E_{S,T}` when its principal idele does. -/
theorem index_auxiliaryKummerIdeleClassSubgroup_mul_relIndex
    (S T : Finset (HeightOneSpectrum (𝓞 K))) (n : ℕ)
    (hST : Subgroup.closure (HeightOneSpectrum.classGroupMk (R := 𝓞 K) ''
      ((S : Set (HeightOneSpectrum (𝓞 K))) ∪ (T : Set (HeightOneSpectrum (𝓞 K))))) = ⊤) :
    (auxiliaryKummerIdeleClassSubgroup S T n).index *
        ((auxiliaryKummerIdeleSubgroup S T n).comap (IdeleGroup.unitEmbedding (𝓞 K) K)).relIndex
          (((S : Set (HeightOneSpectrum (𝓞 K))) ∪ T).unit K) =
      (auxiliaryKummerIdeleSubgroup S T n).relIndex (auxiliaryKummerIdeleSubgroup S T 1) := by
  set E := auxiliaryKummerIdeleSubgroup S T n
  set I := auxiliaryKummerIdeleSubgroup S T 1
  -- The class map on `(S ∪ T)`-ideles is onto, and its kernel is the principal `(S ∪ T)`-ideles.
  let f : I →* IdeleClassGroup (𝓞 K) K :=
    (QuotientGroup.mk' (IdeleGroup.principalSubgroup (𝓞 K) K)).comp I.subtype
  have hf : Function.Surjective f := by
    intro c
    obtain ⟨x, hx, hc⟩ :=
      IdeleClassGroup.exists_valued_ideleFiniteCoord_eq_one_and_mk_eq hST c
    exact ⟨⟨x, (mem_auxiliaryKummerIdeleSubgroup_one_iff_union S T x).mpr hx⟩, hc⟩
  have hmap : (E.subgroupOf I).map f = auxiliaryKummerIdeleClassSubgroup S T n := by
    dsimp only [f]
    rw [auxiliaryKummerIdeleClassSubgroup, ← Subgroup.map_map,
      Subgroup.subgroupOf_map_subtype]
    exact congrArg (Subgroup.map _) (inf_eq_left.mpr (auxiliaryKummerIdeleSubgroup_le_one S T n))
  have hker : f.ker = (IdeleGroup.principalSubgroup (𝓞 K) K ⊓ I).subgroupOf I := by
    rw [Subgroup.inf_subgroupOf_right, ← MonoidHom.comap_ker, QuotientGroup.ker_mk',
      Subgroup.comap_subtype]
  -- The first isomorphism theorem computes the index of the image from the kernel of `f`.
  have himage : (auxiliaryKummerIdeleClassSubgroup S T n).index =
      (E.subgroupOf I ⊔ f.ker).index := by
    rw [← hmap, Subgroup.index_map, f.range_eq_top_of_surjective hf, Subgroup.index_top, mul_one]
  -- Multiplicativity splits the index of `E` at the intermediate subgroup `E ⊔ ker f`.
  have hmul : (E.subgroupOf I).relIndex f.ker * (E.subgroupOf I ⊔ f.ker).index =
      (E.subgroupOf I).index := by
    rw [← Subgroup.relIndex_sup_left]
    exact Subgroup.relIndex_mul_index le_sup_left
  rw [Subgroup.relIndex_comap, ← principalSubgroup_inf_auxiliaryKummerIdeleSubgroup_one,
    ← Subgroup.relIndex_subgroupOf inf_le_right, ← hker, himage, mul_comm, hmul,
    Subgroup.relIndex]

/-- If the classes of `S ∪ T` generate the ideal class group, the index of the auxiliary Kummer
idele-class subgroup divides the product of the local power-class counts. -/
theorem index_auxiliaryKummerIdeleClassSubgroup_dvd
    (S T : Finset (HeightOneSpectrum (𝓞 K))) (n : ℕ)
    (hST : Subgroup.closure (HeightOneSpectrum.classGroupMk (R := 𝓞 K) ''
      ((S : Set (HeightOneSpectrum (𝓞 K))) ∪ (T : Set (HeightOneSpectrum (𝓞 K))))) = ⊤) :
    (auxiliaryKummerIdeleClassSubgroup S T n).index ∣
      (∏ v ∈ S, Nat.card ((v.adicCompletion K)ˣ ⧸ (powMonoidHom n).range)) *
        ∏ w : InfinitePlace K, Nat.card (w.Completionˣ ⧸ (powMonoidHom n).range) := by
  rw [← relIndex_auxiliaryKummerIdeleSubgroup,
    ← index_auxiliaryKummerIdeleClassSubgroup_mul_relIndex S T n hST]
  exact dvd_mul_right _ _

open GlobalNumberFields in
/-- **A subgroup containing the `n`-th powers and a ray subgroup contains a Kummer idele-class
subgroup.** Let `N ≤ C_K` contain the `n`-th powers and the ray subgroup of a modulus `𝔪` whose
finite part is supported in `S`. Then `N` contains the image in `C_K` of the Kummer idele subgroup
`E_S` of ideles that are `n`-th powers at `S` and at every infinite place and units elsewhere. -/
theorem auxiliaryKummerIdeleClassSubgroup_le_of_raySubgroup_le {n : ℕ}
    {N : Subgroup (IdeleClassGroup (𝓞 K) K)} (hpow : ∀ c, c ^ n ∈ N) {𝔪 : Modulus K}
    (h𝔪 : raySubgroup 𝔪 ≤ N) {S : Finset (HeightOneSpectrum (𝓞 K))}
    (hS : 𝔪.support ⊆ S) :
    auxiliaryKummerIdeleClassSubgroup S ∅ n ≤ N := by
  classical
  intro c hc
  obtain ⟨x, hx, rfl⟩ := (mem_auxiliaryKummerIdeleClassSubgroup_iff S ∅ n c).1 hc
  obtain ⟨hxS, hxinf, hxunit⟩ := (mem_auxiliaryKummerIdeleSubgroup_iff S ∅ n x).1 hx
  -- Write `x = z * yⁿ`, where `y` is supported on `S` and the infinite places and `z` is `1` there
  -- and a unit elsewhere, hence congruent to one modulo `𝔪`. First choose the `n`-th roots of the
  -- coordinates of `x` at `S` and at the infinite places.
  choose yS hyS using hxS
  choose yinf hyinf using hxinf
  let y : IdeleGroup (𝓞 K) K := ideleOfUnits yinf (fun v ↦ if hv : v ∈ S then yS v hv else 1)
    (Filter.eventually_cofinite.2 <| S.finite_toSet.subset fun v (hv : ¬ _) ↦
      by_contra fun (hvS : v ∉ S) ↦ hv (by simp only [hvS, dite_false]; exact one_mem _))
  -- The quotient `z = x / yⁿ` is `1` at `S` and at infinity, and agrees with `x` elsewhere.
  set z := x * (y ^ n)⁻¹ with hz
  have hzS (v : HeightOneSpectrum (𝓞 K)) (hv : v ∈ S) : v.ideleFiniteCoord z = 1 := by
    simp [hz, y, hv, ← hyS v hv]
  have hzS' (v : HeightOneSpectrum (𝓞 K)) (hv : v ∉ S) :
      v.ideleFiniteCoord z = v.ideleFiniteCoord x := by
    simp [hz, y, hv]
  have hzinf (w : InfinitePlace K) : w.ideleInfiniteCoord z = 1 := by
    simp [hz, y, ← hyinf w]
  have hzmem : z ∈ ideleCongruenceSubgroup 𝔪 := by
    refine mem_ideleCongruenceSubgroup_iff.2 ⟨fun v _ ↦ ?_, fun v hv ↦ ?_, fun w _ ↦ ?_⟩
    · by_cases hv : v ∈ S
      · simp [hzS v hv]
      · rw [hzS' v hv]
        exact hxunit v hv (Finset.notMem_empty v)
    · simp [hzS v (hS ((Modulus.mem_support_iff 𝔪 v).2 hv))]
    · simp [hzinf]
  -- Hence the class of `x = z * yⁿ` lies in `N`.
  have hxz : x = z * y ^ n := by rw [hz, inv_mul_cancel_right]
  rw [hxz, QuotientGroup.mk_mul, QuotientGroup.mk_pow]
  exact N.mul_mem (h𝔪 (mem_raySubgroup_iff.2 ⟨z, hzmem, rfl⟩)) (hpow _)

end TauCeti.ClassFieldTheory
