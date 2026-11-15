/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Perfect
public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Frobenius
public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Root.Injective

/-!
# Standard and based endomorphisms of a Chevalley datum

An endomorphism `F` of `D.points A` for a Chevalley datum `D` is **standard** (`D.IsStandard F`) if
it acts on `D.torusPoints A` through an injective linear endomorphism `φ` of the character lattice
(`IsCharacterMap (D.torusPoints A) F φ`) and maps each numbered root subgroup onto some numbered
root subgroup. It is **based** (`D.IsBased F`) if it is standard and maps each positive root
subgroup onto a positive root subgroup; over every commutative ring `A`, this is equivalent to
standardness plus `(D.borelSubgroup A).map F ≤ D.borelSubgroup A`
(`isBased_iff_isStandard_and_map_borelSubgroup_le`). Over any perfect ring of exponential
characteristic `p`, `D.frobenius p k A` is based (`isBased_frobenius`).

Over an infinite field `K` with `[RootableBy Kˣ ℕ]` (in particular over any algebraically closed
field), the pinning equation completely controls a standard endomorphism `hF : D.IsStandard F`:

* its character map `hF.characterMap` is unique (`characterMap_eq_of_isCharacterMap`);
* it permutes the root indices by `hF.rootPerm : Equiv.Perm (Fin t.numRoots)` commuting with root
  negation (`rootPerm_reflectionPerm_self`), preserving `posRoots` when based
  (`IsBased.image_rootPerm_posRoots`);
* `F (x_α(u)) = x_{hF.rootPerm α}(hF.rootUnit α * hF.fieldEnd α u)` (`map_rootSubgroupPoints`) for a
  unique unit `hF.rootUnit α : Kˣ` and bijective ring endomorphism `hF.fieldEnd α : K →+* K`
  (`eq_of_map_rootSubgroupPoints`), with `hF.fieldEnd (-α) = hF.fieldEnd α`;
* `φ (D.coordinateRoot (hF.rootPerm α))` is a positive rational multiple of `D.coordinateRoot α`
  (`exists_pos_nsmul_characterMap_coordinateRoot`), and both `hF.rootPerm` and `hF.fieldEnd` depend
  only on `φ` (`rootPerm_eq_of_isCharacterMap`, `fieldEnd_eq_of_isCharacterMap`).

## References

* R. Steinberg, *Endomorphisms of linear algebraic groups*, Mem. Amer. Math. Soc. **80** (1968),
  §§10–11.
* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 10, Theorems 28 and 29.
* R. W. Carter, *Finite Groups of Lie Type: Conjugacy Classes and Complex Characters*, §1.17.
-/

public section

namespace TauCeti.DynkinType.ChevalleyDatum

open Multiplicative

universe v

variable {t : DynkinType} {ht : t.Valid} (D : ChevalleyDatum t ht)

/-! ## Definitions and general ring properties -/

section CommRing

variable {A : Type v} [CommRing A]

/-- **A standard endomorphism of the points of a Chevalley datum**: `F` acts on the actual
character-lattice torus through an injective linear endomorphism `φ` of the character lattice and
maps each numbered root subgroup onto some numbered root subgroup. -/
def IsStandard (F : D.points A →* D.points A) : Prop :=
  (∃ φ : Module.End ℤ (Fin t.rank → ℤ),
    Function.Injective φ ∧ IsCharacterMap (D.torusPoints A) F φ) ∧
    ∀ α : Fin t.numRoots, ∃ β : Fin t.numRoots,
      (D.rootSubgroupPoints α A).range.map F = (D.rootSubgroupPoints β A).range

/-- Unfolding characterization of `D.IsStandard F`. -/
theorem isStandard_def (F : D.points A →* D.points A) :
    D.IsStandard F ↔
      (∃ φ : Module.End ℤ (Fin t.rank → ℤ),
        Function.Injective φ ∧ IsCharacterMap (D.torusPoints A) F φ) ∧
        ∀ α : Fin t.numRoots, ∃ β : Fin t.numRoots,
          (D.rootSubgroupPoints α A).range.map F = (D.rootSubgroupPoints β A).range := Iff.rfl

/-- **A based endomorphism of the points of a Chevalley datum**: a standard endomorphism that maps
each positive root subgroup onto a positive root subgroup. -/
def IsBased (F : D.points A →* D.points A) : Prop :=
  D.IsStandard F ∧
    ∀ α ∈ posRoots (t.rationalRootSystem ht) (t.rationalBase ht),
      ∃ β ∈ posRoots (t.rationalRootSystem ht) (t.rationalBase ht),
        (D.rootSubgroupPoints α A).range.map F = (D.rootSubgroupPoints β A).range

/-- Unfolding characterization of `D.IsBased F`. -/
theorem isBased_def (F : D.points A →* D.points A) :
    D.IsBased F ↔
      D.IsStandard F ∧
        ∀ α ∈ posRoots (t.rationalRootSystem ht) (t.rationalBase ht),
          ∃ β ∈ posRoots (t.rationalRootSystem ht) (t.rationalBase ht),
            (D.rootSubgroupPoints α A).range.map F = (D.rootSubgroupPoints β A).range := Iff.rfl

section BasicAPI

variable {D} {F F' : D.points A →* D.points A}

/-- Every based endomorphism is standard. -/
theorem IsBased.isStandard (h : D.IsBased F) : D.IsStandard F := h.1

/-- The identity endomorphism is standard. -/
@[simp]
theorem isStandard_id : D.IsStandard (MonoidHom.id (D.points A)) :=
  ⟨⟨1, Function.injective_id, isCharacterMap_id (D.torusPoints A)⟩, fun α => ⟨α, Subgroup.map_id _⟩⟩

/-- The identity endomorphism is based. -/
@[simp]
theorem isBased_id : D.IsBased (MonoidHom.id (D.points A)) :=
  ⟨D.isStandard_id, fun α hα => ⟨α, hα, Subgroup.map_id _⟩⟩

/-- Standard endomorphisms are closed under composition. -/
theorem IsStandard.comp (hF : D.IsStandard F) (hF' : D.IsStandard F') :
    D.IsStandard (F.comp F') := by
  rcases hF with ⟨⟨φ, hφ_inj, hφ⟩, hroot⟩
  rcases hF' with ⟨⟨ψ, hψ_inj, hψ⟩, hroot'⟩
  refine ⟨⟨ψ * φ, hψ_inj.comp hφ_inj, hφ.comp hψ⟩, fun α => ?_⟩
  obtain ⟨β, hβ⟩ := hroot' α; obtain ⟨γ, hγ⟩ := hroot β
  exact ⟨γ, by rw [← Subgroup.map_map, hβ, hγ]⟩

/-- Based endomorphisms are closed under composition. -/
theorem IsBased.comp (hF : D.IsBased F) (hF' : D.IsBased F') : D.IsBased (F.comp F') := by
  refine ⟨hF.isStandard.comp hF'.isStandard, fun α hα => ?_⟩
  obtain ⟨β, hβpos, hβ⟩ := hF'.2 α hα; obtain ⟨γ, hγpos, hγ⟩ := hF.2 β hβpos
  exact ⟨γ, hγpos, by rw [← Subgroup.map_map, hβ, hγ]⟩

/-- Powers of a standard endomorphism in `Monoid.End` are standard. -/
theorem IsStandard.pow {F : Monoid.End (D.points A)} (hF : D.IsStandard F) (n : ℕ) :
    D.IsStandard (HPow.hPow (α := Monoid.End (D.points A)) F n) := by
  induction n with
  | zero => exact D.isStandard_id
  | succ n ih => rw [pow_succ']; exact hF.comp ih

/-- Powers of a based endomorphism in `Monoid.End` are based. -/
theorem IsBased.pow {F : Monoid.End (D.points A)} (hF : D.IsBased F) (n : ℕ) :
    D.IsBased (HPow.hPow (α := Monoid.End (D.points A)) F n) := by
  induction n with
  | zero => exact D.isBased_id
  | succ n ih => rw [pow_succ']; exact hF.comp ih

/-- A standard endomorphism carries the actual torus into itself. -/
theorem IsStandard.map_range_torusPoints_le (hF : D.IsStandard F) :
    (D.torusPoints A).range.map F ≤ (D.torusPoints A).range := by
  obtain ⟨φ, _, hφ⟩ := hF.1
  rintro _ ⟨_, ⟨s, rfl⟩, rfl⟩
  exact ⟨torusPointMap φ s, (hφ.map_apply s).symm⟩

/-- Over a ring with divisible units, a standard endomorphism maps the actual torus onto itself. -/
theorem IsStandard.map_range_torusPoints_eq [RootableBy Aˣ ℕ] (hF : D.IsStandard F) :
    (D.torusPoints A).range.map F = (D.torusPoints A).range := by
  obtain ⟨φ, hφ_inj, hφ⟩ := hF.1; exact hφ.map_range_eq hφ_inj

/-- A standard endomorphism preserves the subgroup generated by all root subgroups and the actual
torus. -/
theorem IsStandard.map_rootTorusSubgroup_le (hF : D.IsStandard F) :
    (D.rootTorusSubgroup A).map F ≤ D.rootTorusSubgroup A := by
  rw [Subgroup.map_le_iff_le_comap]
  conv_lhs => rw [D.rootTorusSubgroup_def]
  rw [Subgroup.closure_le]
  rintro g (hmem | ⟨s, rfl⟩)
  · obtain ⟨α, u, rfl⟩ := Set.mem_iUnion.mp hmem
    obtain ⟨β, hβ⟩ := hF.2 α
    obtain ⟨v, hv⟩ : F (D.rootSubgroupPoints α A u) ∈ (D.rootSubgroupPoints β A).range := by
      rw [← hβ]; exact ⟨_, ⟨u, rfl⟩, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap, ← hv]
    exact D.rootSubgroupPoints_mem_rootTorusSubgroup β A v
  · obtain ⟨φ, _, hφ⟩ := hF.1
    rw [SetLike.mem_coe, Subgroup.mem_comap, hφ.map_apply]
    exact D.torusPoints_mem_rootTorusSubgroup A (torusPointMap φ s)

/-- A based endomorphism preserves the positive unipotent subgroup `D.positivePoints A`. -/
theorem IsBased.map_positivePoints_le (hF : D.IsBased F) :
    (D.positivePoints A).map F ≤ D.positivePoints A := by
  rw [Subgroup.map_le_iff_le_comap, D.positivePoints_le_iff]
  intro α hα u
  obtain ⟨β, hβpos, hβ⟩ := hF.2 α hα
  obtain ⟨v, hv⟩ : F (D.rootSubgroupPoints α A u) ∈ (D.rootSubgroupPoints β A).range := by
    rw [← hβ]; exact ⟨_, ⟨u, rfl⟩, rfl⟩
  rw [Subgroup.mem_comap, ← hv]
  exact D.rootSubgroupPoints_mem_positivePoints A hβpos v

/-- A based endomorphism preserves `D.borelSubgroup A`. -/
theorem IsBased.map_borelSubgroup_le (hF : D.IsBased F) :
    (D.borelSubgroup A).map F ≤ D.borelSubgroup A := by
  conv_lhs => rw [D.borelSubgroup_def]
  rw [Subgroup.map_sup]
  exact sup_le (hF.map_positivePoints_le.trans (D.positivePoints_le_borelSubgroup A))
    (hF.isStandard.map_range_torusPoints_le.trans (D.range_torusPoints_le_borelSubgroup A))

/-- **A character map of a standard endomorphism** on `D.torusPoints A`. Over an infinite field `K`,
`IsStandard.characterMap_eq_of_isCharacterMap` shows it is unique. -/
noncomputable def IsStandard.characterMap (hF : D.IsStandard F) :
    Module.End ℤ (Fin t.rank → ℤ) := hF.1.choose

/-- The character map of a standard endomorphism is injective. -/
theorem IsStandard.characterMap_injective (hF : D.IsStandard F) :
    Function.Injective hF.characterMap := hF.1.choose_spec.1

/-- A standard endomorphism acts on `D.torusPoints A` through `hF.characterMap`. -/
theorem IsStandard.isCharacterMap (hF : D.IsStandard F) :
    IsCharacterMap (D.torusPoints A) F hF.characterMap := hF.1.choose_spec.2

private noncomputable def IsStandard.rawRootMap (hF : D.IsStandard F) (α : Fin t.numRoots) :
    Fin t.numRoots := (hF.2 α).choose

private theorem IsStandard.map_range_rootSubgroupPoints_rawRootMap (hF : D.IsStandard F)
    (α : Fin t.numRoots) :
    (D.rootSubgroupPoints α A).range.map F = (D.rootSubgroupPoints (hF.rawRootMap α) A).range :=
  (hF.2 α).choose_spec

private theorem IsStandard.rawRootMap_eq_of_map_range [Nontrivial A] (hF : D.IsStandard F)
    {α β : Fin t.numRoots}
    (h : (D.rootSubgroupPoints α A).range.map F = (D.rootSubgroupPoints β A).range) :
    hF.rawRootMap α = β :=
  D.range_rootSubgroupPoints_injective A
    ((hF.map_range_rootSubgroupPoints_rawRootMap α).symm.trans h)

end BasicAPI

/-- **Over any commutative ring, a standard endomorphism is based if and only if it preserves
`D.borelSubgroup A`.** -/
theorem isBased_iff_isStandard_and_map_borelSubgroup_le {F : D.points A →* D.points A} :
    D.IsBased F ↔ D.IsStandard F ∧ (D.borelSubgroup A).map F ≤ D.borelSubgroup A := by
  refine ⟨fun h => ⟨h.isStandard, h.map_borelSubgroup_le⟩, fun ⟨hStd, hB⟩ => ⟨hStd, fun α hα => ?_⟩⟩
  rcases subsingleton_or_nontrivial A with _ | _
  · refine ⟨α, hα, le_antisymm ?_ ?_⟩
    · rintro _ ⟨_, ⟨u, rfl⟩, rfl⟩
      have hu : u = 1 := toAdd.injective (Subsingleton.elim (toAdd u) 0); simp [hu]
    · rintro _ ⟨u, rfl⟩
      have hu : u = 1 := toAdd.injective (Subsingleton.elim (toAdd u) 0); simp [hu]
  obtain ⟨β, hβ⟩ := hStd.2 α
  refine ⟨β, ?_, hβ⟩
  by_contra hβnot
  have hβneg := (not_mem_posRoots_iff_mem_negRoots _ _ _).mp hβnot
  obtain ⟨_, ⟨u, rfl⟩, hx⟩ : D.rootSubgroupPoints β A (ofAdd 1) ∈
      (D.rootSubgroupPoints α A).range.map F := hβ ▸ ⟨ofAdd 1, rfl⟩
  exact D.rootSubgroupPoints_ofAdd_one_ne_one A β
    ((D.rootSubgroupPoints_mem_borelSubgroup_iff_of_mem_negRoots A hβneg (ofAdd 1)).mp
      (hB ⟨_, D.positivePoints_le_borelSubgroup A
        (D.rootSubgroupPoints_mem_positivePoints A hα u), hx⟩))

/-- Over any perfect ring of exponential characteristic `p`, `D.frobenius p k A` maps each root
subgroup onto itself. -/
@[simp]
theorem map_range_rootSubgroupPoints_frobenius (p k : ℕ) [ExpChar A p] [PerfectRing A p]
    (α : Fin t.numRoots) :
    (D.rootSubgroupPoints α A).range.map (D.frobenius p k A) =
      (D.rootSubgroupPoints α A).range := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨_, ⟨u, rfl⟩, rfl⟩
    refine ⟨ofAdd (toAdd u ^ p ^ k), ?_⟩
    conv_rhs => rw [← ofAdd_toAdd u, D.frobenius_rootSubgroupPoints]
  · rintro _ ⟨u, rfl⟩
    obtain ⟨v, hv⟩ := (bijective_iterateFrobenius A p k).surjective (toAdd u)
    refine ⟨D.rootSubgroupPoints α A (ofAdd v), ⟨ofAdd v, rfl⟩, ?_⟩
    rw [D.frobenius_rootSubgroupPoints, ← iterateFrobenius_def, hv, ofAdd_toAdd]

/-- **Over any perfect ring of exponential characteristic `p`, Frobenius is based.** -/
theorem isBased_frobenius (p k : ℕ) [ExpChar A p] [PerfectRing A p] :
    D.IsBased (D.frobenius p k A) := by
  have hp : ((p ^ k : ℕ) : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr (pow_ne_zero k (expChar_pos A p).ne')
  have hinj : Function.Injective ((p ^ k : ℕ) • (1 : Module.End ℤ (Fin t.rank → ℤ))) :=
    fun x y hxy => funext fun j => by
      have hxyj : (p ^ k : ℕ) • x j = (p ^ k : ℕ) • y j := by
        simpa only [LinearMap.smul_apply, one_apply_eq_self, Pi.smul_apply] using congrFun hxy j
      rw [nsmul_eq_mul, nsmul_eq_mul] at hxyj
      exact mul_left_cancel₀ hp hxyj
  exact ⟨⟨⟨(p ^ k : ℕ) • 1, hinj, D.isCharacterMap_frobenius p k A⟩,
      fun α => ⟨α, D.map_range_rootSubgroupPoints_frobenius p k α⟩⟩,
    fun α hα => ⟨α, hα, D.map_range_rootSubgroupPoints_frobenius p k α⟩⟩

/-- Over any perfect ring of exponential characteristic `p`, Frobenius is standard. -/
theorem isStandard_frobenius (p k : ℕ) [ExpChar A p] [PerfectRing A p] :
    D.IsStandard (D.frobenius p k A) := (D.isBased_frobenius p k).isStandard

end CommRing

/-! ## Uniqueness of the character map over an infinite field -/

section InfiniteField

variable {K : Type v} [Field K] [Infinite K] {D} {F : D.points K →* D.points K}

/-- Any character map of `F` on `D.torusPoints K` equals `hF.characterMap`. -/
theorem IsStandard.characterMap_eq_of_isCharacterMap (hF : D.IsStandard F)
    {φ : Module.End ℤ (Fin t.rank → ℤ)} (hφ : IsCharacterMap (D.torusPoints K) F φ) :
    hF.characterMap = φ :=
  hF.isCharacterMap.unique (D.torusPoints_injective K) hφ

end InfiniteField

/-! ## Structure and rigidity over an infinite field with divisible units -/

section DivisibleUnits

variable {K : Type v} [Field K] {D} {F F' : D.points K →* D.points K}

private noncomputable def rootSubgroupRangeEquiv (β : Fin t.numRoots) :
    Multiplicative K ≃* (D.rootSubgroupPoints β K).range :=
  MulEquiv.ofBijective (D.rootSubgroupPoints β K).rangeRestrict
    ⟨fun _ _ h => D.rootSubgroupPoints_injective K β (congrArg Subtype.val h),
      (D.rootSubgroupPoints β K).rangeRestrict_surjective⟩

private noncomputable def IsStandard.rawParamHom (hF : D.IsStandard F) (α : Fin t.numRoots) :
    K →+ K :=
  let mα : Multiplicative K →* (D.rootSubgroupPoints (hF.rawRootMap α) K).range :=
    (F.comp (D.rootSubgroupPoints α K)).codRestrict _ fun u => by
      rw [← hF.map_range_rootSubgroupPoints_rawRootMap α]; exact ⟨_, ⟨u, rfl⟩, rfl⟩
  { toFun u := toAdd ((D.rootSubgroupRangeEquiv (hF.rawRootMap α)).symm (mα (ofAdd u)))
    map_zero' := by simp
    map_add' x y := by rw [ofAdd_add, map_mul, map_mul, toAdd_mul] }

private theorem IsStandard.rootSubgroupPoints_rawParamHom (hF : D.IsStandard F)
    (α : Fin t.numRoots) (u : K) :
    D.rootSubgroupPoints (hF.rawRootMap α) K (ofAdd (hF.rawParamHom α u)) =
      F (D.rootSubgroupPoints α K (ofAdd u)) := by
  let mα : Multiplicative K →* (D.rootSubgroupPoints (hF.rawRootMap α) K).range :=
    (F.comp (D.rootSubgroupPoints α K)).codRestrict _ fun v => by
      rw [← hF.map_range_rootSubgroupPoints_rawRootMap α]; exact ⟨_, ⟨v, rfl⟩, rfl⟩
  change D.rootSubgroupPoints (hF.rawRootMap α) K
      (ofAdd (toAdd ((D.rootSubgroupRangeEquiv (hF.rawRootMap α)).symm (mα (ofAdd u))))) =
    F (D.rootSubgroupPoints α K (ofAdd u))
  rw [ofAdd_toAdd]
  exact congrArg Subtype.val
    ((D.rootSubgroupRangeEquiv (hF.rawRootMap α)).apply_symm_apply (mα (ofAdd u)))

private theorem IsStandard.rawParamHom_surjective (hF : D.IsStandard F) (α : Fin t.numRoots) :
    Function.Surjective (hF.rawParamHom α) := fun v => by
  obtain ⟨_, ⟨u, rfl⟩, hFu⟩ : D.rootSubgroupPoints (hF.rawRootMap α) K (ofAdd v) ∈
      (D.rootSubgroupPoints α K).range.map F :=
    hF.map_range_rootSubgroupPoints_rawRootMap α ▸ ⟨ofAdd v, rfl⟩
  refine ⟨toAdd u, ?_⟩
  have h1 : D.rootSubgroupPoints (hF.rawRootMap α) K (ofAdd (hF.rawParamHom α (toAdd u))) =
      D.rootSubgroupPoints (hF.rawRootMap α) K (ofAdd v) := by
    rw [hF.rootSubgroupPoints_rawParamHom, ofAdd_toAdd, hFu]
  simpa only [toAdd_ofAdd] using congrArg toAdd (D.rootSubgroupPoints_injective K _ h1)

private theorem IsStandard.rawParamHom_torusCharacter_mul (hF : D.IsStandard F)
    (α : Fin t.numRoots) (s : Fin t.rank → Kˣ) (u : K) :
    hF.rawParamHom α ((torusCharacter s (D.coordinateRoot α) : K) * u) =
      (torusCharacter s (hF.characterMap (D.coordinateRoot (hF.rawRootMap α))) : K) *
        hF.rawParamHom α u := by
  have hconj : F (D.torusPoints K s * D.rootSubgroupPoints α K (ofAdd u) *
      (D.torusPoints K s)⁻¹) = F (D.torusPoints K s) * F (D.rootSubgroupPoints α K (ofAdd u)) *
        (F (D.torusPoints K s))⁻¹ := by rw [map_mul, map_mul, map_inv]
  rw [D.torusPoints_conj_rootSubgroupPoints, ← hF.rootSubgroupPoints_rawParamHom,
    ← hF.rootSubgroupPoints_rawParamHom, hF.isCharacterMap.map_apply,
    D.torusPoints_conj_rootSubgroupPoints, torusCharacter_torusPointMap] at hconj
  simpa only [toAdd_ofAdd] using congrArg toAdd (D.rootSubgroupPoints_injective K _ hconj)

variable [RootableBy Kˣ ℕ]

private theorem IsStandard.rawParamHom_one_ne_zero (hF : D.IsStandard F) (α : Fin t.numRoots) :
    hF.rawParamHom α 1 ≠ 0 := fun h0 => by
  obtain ⟨u, hu⟩ := hF.rawParamHom_surjective α 1
  by_cases hu0 : u = 0
  · exact (@one_ne_zero K _ _) (by simpa [hu0] using hu.symm)
  obtain ⟨s, hs⟩ := torusCharacter_surjective (D.coordinateRoot_ne_zero α) (Units.mk0 u hu0)
  have hzero : hF.rawParamHom α u = 0 := by
    simpa only [show (torusCharacter s (D.coordinateRoot α) : K) = u by
      simpa using congrArg Units.val hs, mul_one, h0, mul_zero] using
      hF.rawParamHom_torusCharacter_mul α s 1
  exact (@one_ne_zero K _ _) (hu.symm.trans hzero)

/-- **The scaling unit `c_α : Kˣ` of a standard endomorphism on the `α`-root subgroup**, defined by
`F (x_α(1)) = x_{hF.rootPerm α}(c_α)`. -/
noncomputable def IsStandard.rootUnit (hF : D.IsStandard F) (α : Fin t.numRoots) : Kˣ :=
  Units.mk0 (hF.rawParamHom α 1) (hF.rawParamHom_one_ne_zero α)

/-- **The field endomorphism `g_α : K →+* K` of a standard endomorphism on the `α`-root
subgroup**, normalized by `F (x_α(u)) = x_{hF.rootPerm α}(hF.rootUnit α * g_α u)`. -/
noncomputable def IsStandard.fieldEnd (hF : D.IsStandard F) (α : Fin t.numRoots) : K →+* K :=
  ringHomOfAddMonoidHomTorusCharacter
    (AddMonoidHom.mk' (fun u => (((hF.rootUnit α)⁻¹ : Kˣ) : K) * hF.rawParamHom α u) fun _ _ => by
      rw [map_add, mul_add])
    (D.coordinateRoot_ne_zero α)
    (by simp [IsStandard.rootUnit, inv_mul_cancel₀ (hF.rawParamHom_one_ne_zero α)])
    (fun s u => by simp only [AddMonoidHom.mk'_apply, hF.rawParamHom_torusCharacter_mul]; ring)

private theorem IsStandard.fieldEnd_apply_eq (hF : D.IsStandard F) (α : Fin t.numRoots) (u : K) :
    hF.fieldEnd α u = (((hF.rootUnit α)⁻¹ : Kˣ) : K) * hF.rawParamHom α u := by
  rw [IsStandard.fieldEnd, ringHomOfAddMonoidHomTorusCharacter_apply, AddMonoidHom.mk'_apply]

/-- Each root-subgroup field endomorphism `hF.fieldEnd α` is bijective (because `F` maps each root
subgroup *onto* its target root subgroup, while any ring endomorphism of a field is injective). -/
theorem IsStandard.fieldEnd_bijective (hF : D.IsStandard F) (α : Fin t.numRoots) :
    Function.Bijective (hF.fieldEnd α) := by
  refine ⟨(hF.fieldEnd α).injective, fun y => ?_⟩
  obtain ⟨u, hu⟩ := hF.rawParamHom_surjective α ((hF.rootUnit α : K) * y)
  exact ⟨u, by rw [hF.fieldEnd_apply_eq, hu, Units.val_inv_eq_inv_val,
    inv_mul_cancel_left₀ (Units.ne_zero _)]⟩

private theorem IsStandard.fieldEnd_torusCharacter_raw (hF : D.IsStandard F)
    (α : Fin t.numRoots) (s : Fin t.rank → Kˣ) :
    hF.fieldEnd α (torusCharacter s (D.coordinateRoot α) : K) =
      (torusCharacter s (hF.characterMap (D.coordinateRoot (hF.rawRootMap α))) : K) :=
  ringHomOfAddMonoidHomTorusCharacter_torusCharacter _ _ _ _ s

variable [Infinite K]

private theorem IsStandard.exists_pos_nsmul_rawRootMap (hF : D.IsStandard F)
    (α : Fin t.numRoots) :
    ∃ d m : ℕ, 0 < d ∧ 0 < m ∧
      d • hF.characterMap (D.coordinateRoot (hF.rawRootMap α)) = m • D.coordinateRoot α :=
  exists_pos_nsmul_eq_nsmul_of_map_torusCharacter_eq (hF.fieldEnd α)
    (hF.fieldEnd_torusCharacter_raw α)

private theorem IsStandard.rawRootMap_injective (hF : D.IsStandard F) :
    Function.Injective hF.rawRootMap := fun α₁ α₂ hβ => by
  obtain ⟨d₁, m₁, _, hm₁, hrel₁⟩ := hF.exists_pos_nsmul_rawRootMap α₁
  obtain ⟨d₂, m₂, hd₂, _, hrel₂⟩ := hF.exists_pos_nsmul_rawRootMap α₂
  rw [hβ] at hrel₁
  refine D.eq_of_nsmul_coordinateRoot_eq (d := d₁ * m₂) (Nat.mul_pos hd₂ hm₁) ?_
  rw [mul_smul, ← hrel₁, smul_comm, hrel₂, ← mul_smul]

/-- **The root permutation `σ : Equiv.Perm (Fin t.numRoots)` of a standard endomorphism**, over an
infinite field with divisible units. -/
noncomputable def IsStandard.rootPerm (hF : D.IsStandard F) : Equiv.Perm (Fin t.numRoots) :=
  Equiv.ofBijective hF.rawRootMap (Finite.injective_iff_bijective.mp hF.rawRootMap_injective)

/-- A standard endomorphism maps the `α`-root subgroup onto the `hF.rootPerm α`-root subgroup. -/
@[simp]
theorem IsStandard.map_range_rootSubgroupPoints (hF : D.IsStandard F) (α : Fin t.numRoots) :
    (D.rootSubgroupPoints α K).range.map F =
      (D.rootSubgroupPoints (hF.rootPerm α) K).range :=
  hF.map_range_rootSubgroupPoints_rawRootMap α

/-- Recognition lemma for `hF.rootPerm` from the image of a root subgroup. -/
theorem IsStandard.rootPerm_eq_of_map_range (hF : D.IsStandard F) {α β : Fin t.numRoots}
    (h : (D.rootSubgroupPoints α K).range.map F = (D.rootSubgroupPoints β K).range) :
    hF.rootPerm α = β := hF.rawRootMap_eq_of_map_range h

/-- **Explicit formula for a standard endomorphism on every root subgroup**:
`F (x_α(u)) = x_{hF.rootPerm α}(hF.rootUnit α * hF.fieldEnd α u)`. -/
theorem IsStandard.map_rootSubgroupPoints (hF : D.IsStandard F) (α : Fin t.numRoots) (u : K) :
    F (D.rootSubgroupPoints α K (ofAdd u)) =
      D.rootSubgroupPoints (hF.rootPerm α) K
        (ofAdd ((hF.rootUnit α : K) * hF.fieldEnd α u)) := by
  rw [hF.fieldEnd_apply_eq, Units.val_inv_eq_inv_val, mul_inv_cancel_left₀ (Units.ne_zero _)]
  exact (hF.rootSubgroupPoints_rawParamHom α u).symm

/-- **Intertwining of `hF.fieldEnd α` with torus characters**: evaluating `hF.fieldEnd α` on
`α(s)` gives `(φ (σ α))(s)`. -/
theorem IsStandard.fieldEnd_torusCharacter (hF : D.IsStandard F) (α : Fin t.numRoots)
    (s : Fin t.rank → Kˣ) :
    hF.fieldEnd α (torusCharacter s (D.coordinateRoot α) : K) =
      (torusCharacter s (hF.characterMap (D.coordinateRoot (hF.rootPerm α))) : K) :=
  hF.fieldEnd_torusCharacter_raw α s

/-- **Positive rational proportionality of `φ (σ α)` and `α` in the character lattice.** -/
theorem IsStandard.exists_pos_nsmul_characterMap_coordinateRoot (hF : D.IsStandard F)
    (α : Fin t.numRoots) :
    ∃ d m : ℕ, 0 < d ∧ 0 < m ∧
      d • hF.characterMap (D.coordinateRoot (hF.rootPerm α)) = m • D.coordinateRoot α :=
  hF.exists_pos_nsmul_rawRootMap α

/-- **Uniqueness of the root-subgroup presentation `F (x_α(u)) = x_β(c * g u)`**: any root index
`β`, unit `c`, and ring endomorphism `g` satisfying that identity for all `u` must equal
`hF.rootPerm α`, `hF.rootUnit α`, and `hF.fieldEnd α`. -/
theorem IsStandard.eq_of_map_rootSubgroupPoints (hF : D.IsStandard F) {α β : Fin t.numRoots}
    {c : Kˣ} {g : K →+* K}
    (h : ∀ u : K, F (D.rootSubgroupPoints α K (ofAdd u)) =
      D.rootSubgroupPoints β K (ofAdd ((c : K) * g u))) :
    β = hF.rootPerm α ∧ c = hF.rootUnit α ∧ g = hF.fieldEnd α := by
  have hle : (D.rootSubgroupPoints (hF.rootPerm α) K).range ≤
      (D.rootSubgroupPoints β K).range := by
    rw [← hF.map_range_rootSubgroupPoints α]
    rintro _ ⟨_, ⟨u, rfl⟩, rfl⟩
    exact ⟨ofAdd ((c : K) * g (toAdd u)), by conv_rhs => rw [← ofAdd_toAdd u, h]⟩
  obtain rfl : β = hF.rootPerm α := ((D.range_rootSubgroupPoints_le_iff K).mp hle).symm
  have hparam (u : K) : (c : K) * g u = (hF.rootUnit α : K) * hF.fieldEnd α u := by
    simpa only [toAdd_ofAdd] using congrArg toAdd
      (D.rootSubgroupPoints_injective K _ ((h u).symm.trans (hF.map_rootSubgroupPoints α u)))
  obtain rfl : c = hF.rootUnit α := Units.ext (by simpa using hparam 1)
  exact ⟨rfl, rfl, RingHom.ext fun u => mul_left_cancel₀ (Units.ne_zero _) (hparam u)⟩

/-- **The root permutation of a standard endomorphism commutes with root negation.** -/
@[simp]
theorem IsStandard.rootPerm_reflectionPerm_self (hF : D.IsStandard F) (α : Fin t.numRoots) :
    hF.rootPerm ((t.simplyConnectedRootDatum ht).reflectionPerm α α) =
      (t.simplyConnectedRootDatum ht).reflectionPerm (hF.rootPerm α) (hF.rootPerm α) := by
  let P := t.simplyConnectedRootDatum ht
  obtain ⟨d₁, m₁, _, hm₁, hrel₁⟩ := hF.exists_pos_nsmul_characterMap_coordinateRoot α
  obtain ⟨d₂, m₂, hd₂, _, hrel₂⟩ :=
    hF.exists_pos_nsmul_characterMap_coordinateRoot (P.reflectionPerm α α)
  rw [D.coordinateRoot_reflectionPerm_self, smul_neg] at hrel₂
  have hzero : hF.characterMap ((m₂ * d₁) • D.coordinateRoot (hF.rootPerm α) +
      (m₁ * d₂) • D.coordinateRoot (hF.rootPerm (P.reflectionPerm α α))) = 0 := by
    rw [map_add, mul_smul, map_nsmul, map_nsmul, hrel₁, mul_smul, map_nsmul, map_nsmul, hrel₂,
      smul_neg, ← mul_smul, ← mul_smul, mul_comm m₁ m₂, add_neg_cancel]
  refine D.eq_of_nsmul_coordinateRoot_eq (d := m₂ * d₁) (Nat.mul_pos hm₁ hd₂) ?_
  rw [D.coordinateRoot_reflectionPerm_self, smul_neg]
  exact eq_neg_of_add_eq_zero_right (hF.characterMap_injective (hzero.trans (map_zero _).symm))

/-- **Opposite roots carry the same field endomorphism.** -/
@[simp]
theorem IsStandard.fieldEnd_reflectionPerm_self (hF : D.IsStandard F) (α : Fin t.numRoots) :
    hF.fieldEnd ((t.simplyConnectedRootDatum ht).reflectionPerm α α) = hF.fieldEnd α := by
  refine ringHom_eq_of_torusCharacter_eq (D.coordinateRoot_ne_zero α) fun s => ?_
  have hneg := hF.fieldEnd_torusCharacter ((t.simplyConnectedRootDatum ht).reflectionPerm α α) s
  rw [D.coordinateRoot_reflectionPerm_self, torusCharacter_neg, hF.rootPerm_reflectionPerm_self,
    D.coordinateRoot_reflectionPerm_self, map_neg, torusCharacter_neg, Units.val_inv_eq_inv_val,
    Units.val_inv_eq_inv_val, map_inv₀, inv_inj] at hneg
  exact hneg.trans (hF.fieldEnd_torusCharacter α s).symm

/-- **Two standard endomorphisms with equal character maps induce the same root permutation.** -/
theorem IsStandard.rootPerm_eq_of_characterMap_eq (hF : D.IsStandard F) (hF' : D.IsStandard F')
    (hφ : hF.characterMap = hF'.characterMap) : hF.rootPerm = hF'.rootPerm := by
  refine Equiv.ext fun α => ?_
  obtain ⟨d, m, hd, _, hrel⟩ := hF.exists_pos_nsmul_characterMap_coordinateRoot α
  obtain ⟨d', m', _, hm', hrel'⟩ := hF'.exists_pos_nsmul_characterMap_coordinateRoot α
  rw [hφ] at hrel
  refine D.eq_of_nsmul_coordinateRoot_eq (d := m * d') (Nat.mul_pos hm' hd)
    (hF'.characterMap_injective ?_)
  rw [mul_smul, map_nsmul, map_nsmul, hrel, mul_smul, map_nsmul, map_nsmul, hrel',
    ← mul_smul, ← mul_smul, mul_comm m' m]

/-- **Two standard endomorphisms sharing a character map `φ` induce the same root permutation.** -/
theorem IsStandard.rootPerm_eq_of_isCharacterMap (hF : D.IsStandard F) (hF' : D.IsStandard F')
    {φ : Module.End ℤ (Fin t.rank → ℤ)}
    (hφ : IsCharacterMap (D.torusPoints K) F φ) (hφ' : IsCharacterMap (D.torusPoints K) F' φ) :
    hF.rootPerm = hF'.rootPerm :=
  hF.rootPerm_eq_of_characterMap_eq hF'
    ((hF.characterMap_eq_of_isCharacterMap hφ).trans
      (hF'.characterMap_eq_of_isCharacterMap hφ').symm)

/-- **Two standard endomorphisms with equal character maps induce the same field endomorphism on
every root subgroup.** -/
theorem IsStandard.fieldEnd_eq_of_characterMap_eq (hF : D.IsStandard F) (hF' : D.IsStandard F')
    (hφ : hF.characterMap = hF'.characterMap) (α : Fin t.numRoots) :
    hF.fieldEnd α = hF'.fieldEnd α := by
  have hperm := hF.rootPerm_eq_of_characterMap_eq hF' hφ
  refine ringHom_eq_of_torusCharacter_eq (D.coordinateRoot_ne_zero α) fun s => ?_
  rw [hF.fieldEnd_torusCharacter, hF'.fieldEnd_torusCharacter, hφ, hperm]

/-- **Two standard endomorphisms sharing a character map `φ` induce the same field endomorphism on
every root subgroup.** -/
theorem IsStandard.fieldEnd_eq_of_isCharacterMap (hF : D.IsStandard F) (hF' : D.IsStandard F')
    {φ : Module.End ℤ (Fin t.rank → ℤ)} (hφ : IsCharacterMap (D.torusPoints K) F φ)
    (hφ' : IsCharacterMap (D.torusPoints K) F' φ) (α : Fin t.numRoots) :
    hF.fieldEnd α = hF'.fieldEnd α :=
  hF.fieldEnd_eq_of_characterMap_eq hF'
    ((hF.characterMap_eq_of_isCharacterMap hφ).trans
      (hF'.characterMap_eq_of_isCharacterMap hφ').symm) α

/-- For a based endomorphism, `rootPerm` preserves the set of positive roots. -/
theorem IsBased.rootPerm_mem_posRoots (hF : D.IsBased F) {α : Fin t.numRoots}
    (hα : α ∈ posRoots (t.rationalRootSystem ht) (t.rationalBase ht)) :
    hF.isStandard.rootPerm α ∈ posRoots (t.rationalRootSystem ht) (t.rationalBase ht) := by
  obtain ⟨β, hβpos, hβ⟩ := hF.2 α hα
  rwa [hF.isStandard.rootPerm_eq_of_map_range hβ]

/-- For a based endomorphism, `rootPerm` maps the finite set of positive roots bijectively onto
itself. -/
theorem IsBased.image_rootPerm_posRoots (hF : D.IsBased F) :
    hF.isStandard.rootPerm '' posRoots (t.rationalRootSystem ht) (t.rationalBase ht) =
      posRoots (t.rationalRootSystem ht) (t.rationalBase ht) := by
  let S := posRoots (t.rationalRootSystem ht) (t.rationalBase ht)
  have hf : Function.Surjective (fun x : S =>
      (⟨hF.isStandard.rootPerm x.1, hF.rootPerm_mem_posRoots x.2⟩ : S)) :=
    Finite.surjective_of_injective fun _ _ h =>
      Subtype.ext (hF.isStandard.rootPerm.injective (congrArg Subtype.val h))
  refine Set.Subset.antisymm (by rintro _ ⟨_, hα, rfl⟩; exact hF.rootPerm_mem_posRoots hα)
    fun β hβ => ?_
  obtain ⟨⟨α, hα⟩, hαβ⟩ := hf ⟨β, hβ⟩
  exact ⟨α, hα, congrArg Subtype.val hαβ⟩

end DivisibleUnits

end TauCeti.DynkinType.ChevalleyDatum
