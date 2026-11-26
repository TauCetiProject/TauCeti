/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Data.Set.Card
public import Mathlib.GroupTheory.Index
public import TauCeti.GroupTheory.DoubleCoset.Orbits
import Mathlib.Data.Set.Card.Arithmetic
import TauCeti.Algebra.GroupAction.CosetRepresentation
import TauCeti.GroupTheory.GroupAction.Stabilizer.Basic

/-!
# Orbit weights of a subgroup relative to a subset

Let a group `G` act on `α`, let `Γ ≤ G` be a subgroup and `Y ⊆ α` a subset. For `v : α` the
elements `g : G` with `g • v ∈ Y` form a union of right cosets `Γ g` when `Y` is `Γ`-stable. The
*orbit weight* `Γ.orbitWeight Y v` counts the right cosets `Γ g` that contain such an element, and
the *orbit count* `Γ.orbitCount Y v` counts the `Γ`-orbits in `G • v ∩ Y`.

In the arithmetic of binary quartic forms, `G = PGL₂(ℚ)`, `Γ = PGL₂(ℤ)` and `Y` is the set of
integral forms; the orbit weight of an integral form `f` is then the number `m(f)` of
`PGL₂(ℤ)`-cosets of rational transformations keeping `f` integral, by which the integral orbits
are weighted when Selmer elements are counted as integral orbits (Bhargava–Shankar, §3.2). The
same construction with `PGL₂(ℚ_p)` and `PGL₂(ℤ_p)` gives the local weight `m_p(f)`.

The orbit map `g ↦ g • v` induces a map from the counted cosets onto the counted orbits, whose
fibre over the orbit of `x` has `[stabilizer G x : Γ ⊓ stabilizer G x]` elements. Hence, when
finitely many cosets are counted, the orbit weight is the sum of these relative indices over the
orbits, which is the stabilizer-sum description `Σ #Stab_G(x) / #Stab_Γ(x)` of the source when the
stabilizers are finite.

## Main definitions

* `Subgroup.orbitWeightCosets`: the right cosets `Γ g` with `g • v ∈ Y`.
* `Subgroup.orbitWeight`: their number `w_{Γ,Y}(v)` (zero when there are infinitely many).
* `Subgroup.orbitCountClasses`: the `Γ`-orbits of points of `G • v ∩ Y`.
* `Subgroup.orbitCount`: their number `n_{Γ,Y}(v)` (zero when there are infinitely many).

## Main statements

* `Subgroup.orbitWeight_smul`: the orbit weight is constant on `G`-orbits.
* `Subgroup.orbitWeight_eq_one_iff`, `Subgroup.orbitWeight_top`: the weight of a point of `Y` is
  one exactly when only elements of `Γ` keep it in `Y`, for instance when `Γ = G`.
* `Subgroup.orbitWeight_eq_finsum_relIndex`: when finitely many cosets are counted, the orbit
  weight is the sum over the counted orbits of the relative indices `Γ.relIndex (stabilizer G x)`.
* `Subgroup.orbitCount_le_orbitWeight`,
  `Subgroup.orbitWeight_le_card_stabilizer_mul_orbitCount`: `n ≤ w ≤ #Stab_G(v) · n`, the first
  inequality when finitely many cosets are counted and the second when `stabilizer G v` is finite.
* `Subgroup.orbitWeight_eq_orbitCount_iff`: when finitely many cosets are counted, `w = n` exactly
  when `Γ` contains the full stabilizer of every point of `G • v ∩ Y`.

## Implementation notes

Right cosets are the classes of `QuotientGroup.rightRel Γ`. Both counts are `Set.ncard`s, so an
infinite set of cosets or orbits has count zero, following `Nat.card`. No stability of `Y` under
`Γ` is assumed in the definitions: a coset is counted when one of its elements keeps `v` in `Y`.

The map from counted cosets to counted orbits is `Subgroup.orbitOfRightCoset`, whose fibres are
counted by `Subgroup.ncard_fiber_orbitOfRightCoset_eq_relIndex`.

## References

* M. Bhargava, A. Shankar, *Binary quartic forms having bounded invariants, and the boundedness
  of the average rank of elliptic curves*, Ann. of Math. 181 (2015), §3.2 and the proof of
  Proposition 3.6.
-/

public section

open MulAction QuotientGroup

namespace Subgroup

variable {G α : Type*} [Group G] [MulAction G α]

section Defs

variable (Γ : Subgroup G) (Y : Set α) (v : α)

/-- The right cosets `Γ g` containing an element `g` with `g • v ∈ Y`: the image in `Γ \ G` of
`{g | g • v ∈ Y}`. -/
def orbitWeightCosets : Set (Quotient (rightRel Γ)) :=
  Quotient.mk (rightRel Γ) '' {g : G | g • v ∈ Y}

/-- The orbit weight `w_{Γ,Y}(v)`: the number of right cosets `Γ g` with `g • v ∈ Y`, and zero
when there are infinitely many. -/
noncomputable def orbitWeight : ℕ :=
  (Γ.orbitWeightCosets Y v).ncard

/-- The `Γ`-orbits of the points of `G • v` that lie in `Y`. -/
def orbitCountClasses : Set (orbitRel.Quotient Γ α) :=
  Quotient.mk (orbitRel Γ α) '' (orbit G v ∩ Y)

/-- The orbit count `n_{Γ,Y}(v)`: the number of `Γ`-orbits of points of `G • v ∩ Y`, and zero
when there are infinitely many. -/
noncomputable def orbitCount : ℕ :=
  (Γ.orbitCountClasses Y v).ncard

end Defs

variable {Γ : Subgroup G} {Y : Set α} {v : α}

/-- A coset is counted when one of its elements keeps `v` in `Y`. -/
@[simp]
theorem mem_orbitWeightCosets {c : Quotient (rightRel Γ)} :
    c ∈ Γ.orbitWeightCosets Y v ↔ ∃ g : G, g • v ∈ Y ∧ Quotient.mk (rightRel Γ) g = c :=
  Iff.rfl

/-- An orbit is counted when it contains a point of `G • v ∩ Y`. -/
@[simp]
theorem mem_orbitCountClasses {o : orbitRel.Quotient Γ α} :
    o ∈ Γ.orbitCountClasses Y v ↔
      ∃ x ∈ orbit G v, x ∈ Y ∧ Quotient.mk (orbitRel Γ α) x = o := by
  simp [orbitCountClasses, and_assoc]

/-- The orbit weight is the number of counted cosets. -/
theorem orbitWeight_def : Γ.orbitWeight Y v = (Γ.orbitWeightCosets Y v).ncard :=
  (rfl)

/-- The orbit count is the number of counted orbits. -/
theorem orbitCount_def : Γ.orbitCount Y v = (Γ.orbitCountClasses Y v).ncard :=
  (rfl)

/-- When `Y` is `Γ`-stable, the coset of `g` is counted exactly when `g • v ∈ Y`. -/
theorem mk_mem_orbitWeightCosets_iff (hY : ∀ γ ∈ Γ, ∀ y ∈ Y, γ • y ∈ Y) {g : G} :
    Quotient.mk (rightRel Γ) g ∈ Γ.orbitWeightCosets Y v ↔ g • v ∈ Y := by
  refine ⟨?_, fun hg ↦ ⟨g, hg, rfl⟩⟩
  rintro ⟨h, hh, hhg⟩
  have hmem : g * h⁻¹ ∈ Γ := rightRel_apply.mp (Quotient.exact hhg)
  simpa [mul_smul] using hY _ hmem _ hh

/-! ### Invariance and normalisation -/

/-- The orbit weight is constant on `G`-orbits: right multiplication by `g` carries the cosets
counted at `g • v` onto those counted at `v`. -/
@[simp]
theorem orbitWeight_smul (g : G) : Γ.orbitWeight Y (g • v) = Γ.orbitWeight Y v := by
  have himage : Γ.rightCosetPerm g '' Γ.orbitWeightCosets Y (g • v) =
      Γ.orbitWeightCosets Y v := by
    ext c
    simp only [Set.mem_image, mem_orbitWeightCosets]
    constructor
    · rintro ⟨_, ⟨h, hh, rfl⟩, rfl⟩
      exact ⟨h * g, by rwa [mul_smul], (Γ.rightCosetPerm_mk g h).symm⟩
    · rintro ⟨h, hh, rfl⟩
      exact ⟨_, ⟨h * g⁻¹, by rwa [mul_smul, inv_smul_smul], rfl⟩,
        (Γ.rightCosetPerm_mk g _).trans (congrArg _ (inv_mul_cancel_right h g))⟩
  rw [orbitWeight_def, orbitWeight_def, ← himage,
    Set.ncard_image_of_injective _ (Γ.rightCosetPerm g).injective]

/-- The orbit count is constant on `G`-orbits. -/
@[simp]
theorem orbitCount_smul (g : G) : Γ.orbitCount Y (g • v) = Γ.orbitCount Y v := by
  simp only [orbitCount_def, orbitCountClasses, orbit_smul]

/-- The coset of the identity is counted at every point of `Y`. -/
theorem mk_one_mem_orbitWeightCosets (hv : v ∈ Y) :
    Quotient.mk (rightRel Γ) 1 ∈ Γ.orbitWeightCosets Y v :=
  ⟨1, by simpa using hv, rfl⟩

/-- The orbit weight of a point of `Y` is positive when finitely many cosets are counted. -/
theorem orbitWeight_pos (hv : v ∈ Y) (hW : (Γ.orbitWeightCosets Y v).Finite) :
    0 < Γ.orbitWeight Y v :=
  (Set.ncard_pos hW).mpr ⟨_, mk_one_mem_orbitWeightCosets hv⟩

/-- The orbit weight of a point of `Y` is one exactly when every element of `G` keeping it in `Y`
lies in `Γ`. -/
theorem orbitWeight_eq_one_iff (hv : v ∈ Y) :
    Γ.orbitWeight Y v = 1 ↔ {g : G | g • v ∈ Y} ⊆ Γ := by
  have hmk : ∀ g : G, Quotient.mk (rightRel Γ) g = Quotient.mk (rightRel Γ) 1 ↔ g ∈ Γ :=
    fun g ↦ by rw [Quotient.eq, rightRel_apply, one_mul, inv_mem_iff]
  rw [orbitWeight_def, Set.ncard_eq_one]
  constructor
  · rintro ⟨c, hc⟩ g hg
    have h1 : Quotient.mk (rightRel Γ) 1 ∈ ({c} : Set _) :=
      hc ▸ mk_one_mem_orbitWeightCosets hv
    have hg' : Quotient.mk (rightRel Γ) g ∈ ({c} : Set _) := hc ▸ ⟨g, hg, rfl⟩
    rw [Set.mem_singleton_iff] at h1 hg'
    exact (hmk g).mp (hg'.trans h1.symm)
  · intro hS
    refine ⟨Quotient.mk (rightRel Γ) 1, Set.eq_singleton_iff_unique_mem.mpr
      ⟨mk_one_mem_orbitWeightCosets hv, ?_⟩⟩
    rintro _ ⟨g, hg, rfl⟩
    exact (hmk g).mpr (hS hg)

/-- When `Y` is `Γ`-stable, the orbit weight of a point of `Y` is one exactly when the elements of
`G` keeping it in `Y` are exactly the elements of `Γ`. -/
theorem orbitWeight_eq_one_iff_eq (hY : ∀ γ ∈ Γ, ∀ y ∈ Y, γ • y ∈ Y) (hv : v ∈ Y) :
    Γ.orbitWeight Y v = 1 ↔ {g : G | g • v ∈ Y} = Γ := by
  rw [orbitWeight_eq_one_iff hv]
  exact ⟨fun h ↦ h.antisymm fun γ hγ ↦ hY γ hγ v hv, fun h ↦ h.le⟩

/-- For `Γ = G` the orbit weight of every point of `Y` is one. -/
@[simp]
theorem orbitWeight_top (hv : v ∈ Y) : (⊤ : Subgroup G).orbitWeight Y v = 1 :=
  (orbitWeight_eq_one_iff hv).mpr fun g _ ↦ mem_top g

/-! ### The orbit map on cosets -/

/-- The counted cosets are the preimage of the counted orbits: a coset whose orbit meets `Y` has
an element keeping `v` in `Y`. -/
theorem orbitWeightCosets_eq_preimage :
    Γ.orbitWeightCosets Y v = Γ.orbitOfRightCoset v ⁻¹' Γ.orbitCountClasses Y v := by
  ext c
  induction c using Quotient.inductionOn with
  | h g =>
    simp only [mem_orbitWeightCosets, Set.mem_preimage, orbitOfRightCoset_mk,
      mem_orbitCountClasses]
    constructor
    · rintro ⟨h, hh, hhg⟩
      refine ⟨h • v, mem_orbit v h, hh, ?_⟩
      rw [← orbitOfRightCoset_mk, ← orbitOfRightCoset_mk, hhg]
    · rintro ⟨x, -, hx, hxg⟩
      obtain ⟨γ, hγ⟩ := mem_orbit_iff.mp (orbitRel_apply.mp (Quotient.exact hxg))
      refine ⟨γ * g, by rwa [mul_smul, ← Subgroup.smul_def, hγ], Quotient.sound ?_⟩
      exact rightRel_apply.mpr (by simp)

/-- The counted orbits are the image of the counted cosets. -/
theorem orbitCountClasses_eq_image :
    Γ.orbitCountClasses Y v = Γ.orbitOfRightCoset v '' Γ.orbitWeightCosets Y v := by
  rw [orbitWeightCosets_eq_preimage, Set.image_preimage_eq_of_subset]
  rintro _ ⟨x, ⟨⟨g, rfl⟩, -⟩, rfl⟩
  exact ⟨Quotient.mk _ g, orbitOfRightCoset_mk g⟩

/-- A point whose orbit is counted lies in `G • v`. -/
theorem mem_orbit_of_mk_mem_orbitCountClasses {y : α}
    (hy : Quotient.mk (orbitRel Γ α) y ∈ Γ.orbitCountClasses Y v) : y ∈ orbit G v := by
  obtain ⟨x, hxv, -, hxy⟩ := mem_orbitCountClasses.mp hy
  obtain ⟨γ, hγ⟩ := mem_orbit_iff.mp (orbitRel_apply.mp (Quotient.exact hxy.symm))
  rw [← orbit_eq_iff.mpr hxv, ← hγ, Subgroup.smul_def]
  exact mem_orbit x (γ : G)

/-- When `Y` is `Γ`-stable, the orbit of `y` is counted exactly when `y ∈ G • v ∩ Y`. -/
theorem mk_mem_orbitCountClasses_iff (hY : ∀ γ ∈ Γ, ∀ y ∈ Y, γ • y ∈ Y) {y : α} :
    Quotient.mk (orbitRel Γ α) y ∈ Γ.orbitCountClasses Y v ↔ y ∈ orbit G v ∧ y ∈ Y := by
  refine ⟨fun hy ↦ ⟨mem_orbit_of_mk_mem_orbitCountClasses hy, ?_⟩,
    fun ⟨hyv, hyY⟩ ↦ ⟨y, ⟨hyv, hyY⟩, rfl⟩⟩
  obtain ⟨x, -, hxY, hxy⟩ := mem_orbitCountClasses.mp hy
  obtain ⟨γ, hγ⟩ := mem_orbit_iff.mp (orbitRel_apply.mp (Quotient.exact hxy.symm))
  rw [← hγ, Subgroup.smul_def]
  exact hY _ γ.property _ hxY

/-- The fibre of the orbit map over a counted orbit consists of counted cosets. -/
private theorem orbitOfRightCoset_fiber_subset {o : orbitRel.Quotient Γ α}
    (ho : o ∈ Γ.orbitCountClasses Y v) :
    Γ.orbitOfRightCoset v ⁻¹' {o} ⊆ Γ.orbitWeightCosets Y v := by
  rw [orbitWeightCosets_eq_preimage]
  exact Set.preimage_mono (Set.singleton_subset_iff.mpr ho)

/-- Finitely many cosets are counted only when finitely many orbits are. -/
theorem finite_orbitCountClasses (hW : (Γ.orbitWeightCosets Y v).Finite) :
    (Γ.orbitCountClasses Y v).Finite := by
  rw [orbitCountClasses_eq_image]
  exact hW.image _

/-! ### The stabilizer sum -/

/-- **The orbit weight as a stabilizer sum.** If finitely many cosets are counted, the orbit
weight is the sum, over the `Γ`-orbits of `G • v ∩ Y`, of the relative index of `Γ` in the
stabilizer of a representative `σ o` of the orbit `o`. When the stabilizers are finite, each
term is `#Stab_G(σ o) / #Stab_Γ(σ o)` by `Subgroup.relIndex_mul_card`. -/
theorem orbitWeight_eq_finsum_relIndex (hW : (Γ.orbitWeightCosets Y v).Finite)
    {σ : orbitRel.Quotient Γ α → α} (hσ : Function.LeftInverse (Quotient.mk _) σ) :
    Γ.orbitWeight Y v =
      ∑ᶠ o ∈ Γ.orbitCountClasses Y v, Γ.relIndex (stabilizer G (σ o)) := by
  have hN := finite_orbitCountClasses hW
  have hfib : ∀ o ∈ Γ.orbitCountClasses Y v,
      (Γ.orbitOfRightCoset v ⁻¹' {o}).ncard = Γ.relIndex (stabilizer G (σ o)) := by
    intro o ho
    have hσo : σ o ∈ orbit G v :=
      mem_orbit_of_mk_mem_orbitCountClasses (by rwa [hσ o])
    have h := ncard_fiber_orbitOfRightCoset_eq_relIndex (Γ := Γ) hσo
    rwa [hσ o] at h
  rw [orbitWeight_def, orbitWeightCosets_eq_preimage, ← Set.biUnion_preimage_singleton,
    hN.ncard_biUnion (fun o ho ↦ hW.subset (orbitOfRightCoset_fiber_subset ho))
      (Set.pairwiseDisjoint_fiber _ _)]
  exact finsum_mem_congr rfl hfib

/-- **The orbit count is at most the orbit weight**, when finitely many cosets are counted: the
orbit map carries the counted cosets onto the counted orbits. -/
theorem orbitCount_le_orbitWeight (hW : (Γ.orbitWeightCosets Y v).Finite) :
    Γ.orbitCount Y v ≤ Γ.orbitWeight Y v := by
  rw [orbitCount_def, orbitWeight_def, orbitCountClasses_eq_image]
  exact Set.ncard_image_le hW

/-- **The orbit weight is at most `#Stab_G(v)` times the orbit count**, when the stabilizer of `v`
is finite: each relative index in the stabilizer sum is at most the order of a stabilizer of a
point of `G • v`, which is the order of `stabilizer G v`. -/
theorem orbitWeight_le_card_stabilizer_mul_orbitCount [Finite (stabilizer G v)] :
    Γ.orbitWeight Y v ≤ Nat.card (stabilizer G v) * Γ.orbitCount Y v := by
  by_cases hW : (Γ.orbitWeightCosets Y v).Finite
  · have hN := finite_orbitCountClasses hW
    have hle : ∀ o ∈ Γ.orbitCountClasses Y v,
        Γ.relIndex (stabilizer G o.out) ≤ Nat.card (stabilizer G v) := by
      intro o ho
      have hcard : Nat.card (stabilizer G o.out) = Nat.card (stabilizer G v) :=
        TauCeti.card_stabilizer_of_orbitRel
          (orbitRel_apply.mpr (mem_orbit_of_mk_mem_orbitCountClasses (by rwa [o.out_eq])))
      rw [← hcard]
      exact Nat.le_of_dvd (by rw [hcard]; exact Nat.card_pos) (Γ.relIndex_dvd_card _)
    rw [orbitWeight_eq_finsum_relIndex hW (σ := Quotient.out) Quotient.out_eq,
      finsum_mem_eq_finite_toFinset_sum _ hN, orbitCount_def, Set.ncard_eq_toFinset_card _ hN,
      mul_comm, ← smul_eq_mul]
    exact Finset.sum_le_card_nsmul _ _ _ fun o ho ↦ hle o (hN.mem_toFinset.mp ho)
  · simp [orbitWeight_def, Set.Infinite.ncard hW]

/-- The orbit map is injective on the counted cosets exactly when `Γ` contains the stabilizer of
every point of `G • v ∩ Y`, that is, when every fibre over a counted orbit is a single coset. -/
private theorem injOn_orbitOfRightCoset_iff :
    Set.InjOn (Γ.orbitOfRightCoset v) (Γ.orbitWeightCosets Y v) ↔
      ∀ x ∈ orbit G v, x ∈ Y → stabilizer G x ≤ Γ := by
  have hmk : ∀ x ∈ orbit G v, x ∈ Y →
      Quotient.mk (orbitRel Γ α) x ∈ Γ.orbitCountClasses Y v :=
    fun x hxv hxY ↦ mem_orbitCountClasses.mpr ⟨x, hxv, hxY, rfl⟩
  constructor
  · intro hinj x hxv hxY
    obtain ⟨c, hc⟩ := nonempty_fiber_orbitOfRightCoset (Γ := Γ) hxv
    have hsub := orbitOfRightCoset_fiber_subset (hmk x hxv hxY)
    have hsingle : Γ.orbitOfRightCoset v ⁻¹' {Quotient.mk (orbitRel Γ α) x} = {c} :=
      Set.eq_singleton_iff_unique_mem.mpr ⟨hc, fun d hd ↦ hinj (hsub hd) (hsub hc)
        ((Set.mem_singleton_iff.mp hd).trans (Set.mem_singleton_iff.mp hc).symm)⟩
    rw [← relIndex_eq_one, ← ncard_fiber_orbitOfRightCoset_eq_relIndex hxv, hsingle,
      Set.ncard_singleton]
  · intro h c hc d hd hcd
    rw [orbitWeightCosets_eq_preimage] at hc
    obtain ⟨x, hxv, hxY, hx⟩ := mem_orbitCountClasses.mp hc
    have hone := ncard_fiber_orbitOfRightCoset_eq_relIndex (Γ := Γ) hxv
    rw [relIndex_eq_one.mpr (h x hxv hxY), Set.ncard_eq_one] at hone
    obtain ⟨e, he⟩ := hone
    have hce : c ∈ Γ.orbitOfRightCoset v ⁻¹' {Quotient.mk (orbitRel Γ α) x} := hx.symm
    have hde : d ∈ Γ.orbitOfRightCoset v ⁻¹' {Quotient.mk (orbitRel Γ α) x} :=
      hcd.symm.trans hx.symm
    rw [he] at hce hde
    exact hce.trans hde.symm

/-- **The orbit weight equals the orbit count** when `Γ` contains the stabilizer of every point of
`G • v ∩ Y`: then each fibre of the orbit map over a counted orbit is a single coset. No finiteness
is needed, as the orbit map is then a bijection from the counted cosets onto the counted orbits. -/
theorem orbitWeight_eq_orbitCount (h : ∀ x ∈ orbit G v, x ∈ Y → stabilizer G x ≤ Γ) :
    Γ.orbitWeight Y v = Γ.orbitCount Y v := by
  rw [orbitCount_def, orbitWeight_def, orbitCountClasses_eq_image,
    (injOn_orbitOfRightCoset_iff.mpr h).ncard_image]

/-- **Equality of orbit weight and orbit count.** When finitely many cosets are counted, the orbit
weight equals the orbit count exactly when `Γ` contains the stabilizer of every point of
`G • v ∩ Y`, that is, when `Stab_Γ(x) = Stab_G(x)` for all such `x`. -/
theorem orbitWeight_eq_orbitCount_iff (hW : (Γ.orbitWeightCosets Y v).Finite) :
    Γ.orbitWeight Y v = Γ.orbitCount Y v ↔ ∀ x ∈ orbit G v, x ∈ Y → stabilizer G x ≤ Γ := by
  refine ⟨fun h ↦ injOn_orbitOfRightCoset_iff.mp (Set.injOn_of_ncard_image_eq ?_ hW),
    orbitWeight_eq_orbitCount⟩
  rw [← orbitCountClasses_eq_image, ← orbitCount_def, ← orbitWeight_def, h]

/-- The orbit weight equals the orbit count when `G` acts freely at `v`. -/
theorem orbitWeight_eq_orbitCount_of_stabilizer_eq_bot (hv : stabilizer G v = ⊥) :
    Γ.orbitWeight Y v = Γ.orbitCount Y v := by
  refine orbitWeight_eq_orbitCount fun x hx _ ↦ ?_
  have hcard : Nat.card (stabilizer G x) = 1 := by
    rw [TauCeti.card_stabilizer_of_orbitRel (G := G) (orbitRel_apply.mpr hx), hv, card_bot]
  rw [card_eq_one.mp hcard]
  exact bot_le

end Subgroup
