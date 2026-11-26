/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.LinearDisjoint
public import TauCeti.FieldTheory.Galois.Restriction
import Mathlib.FieldTheory.Galois.Infinite
import TauCeti.Algebra.Group.Subgroup.Ker
import TauCeti.FieldTheory.Galois.FixedField
import TauCeti.GroupTheory.NormalSubgroup.SimpleQuotient

/-!
# Composita of Galois extensions with simple Galois groups

Let `K i`, for `i` in a finite index type, be Galois subextensions of `Ω / k`, each equal to `k`
or with simple Galois group. The Galois group of their compositum `⨆ i, K i` embeds into
`∏ i, Gal(K i / k)` by restriction, but the embedding need not be onto, since two of the `K i`
may coincide. This file shows that some subfamily `K j`, `j ∈ J`, already generates the
compositum and that restriction identifies `Gal((⨆ i, K i) / k)` with `∏ j ∈ J, Gal(K j / k)`.
When every nontrivial `K i` has Galois group isomorphic to one simple group `Δ`, the Galois group
of the compositum is therefore `Δ ^ J`, and, for finite Galois members, the composita of two
disjoint parts of the subfamily are linearly disjoint over `k`.

This is the field-theoretic form of `MonoidHom.exists_set_iInf_ker_eq_and_surjective_pi`. It is
used in the proof of Qian's Lemma 2.6(2), with `Δ = PSL₂(𝔽_l)`.

## Main definitions

* `IntermediateField.restrictNormalHomISupPi`: restriction
  `Gal((⨆ i, K i) / k) →* ∏ i, Gal(K i / k)` from the compositum of a family of normal
  subextensions to its members.
* `IntermediateField.restrictNormalHomBiSupPi`: its components indexed by a set `J`, that is,
  restriction `Gal((⨆ i, K i) / k) →* ∏ j ∈ J, Gal(K j / k)`.

## Main results

* `IntermediateField.ker_restrictNormalHomBiSupPi`: the kernel of restriction to the members
  `K j`, `j ∈ J`, is the intersection of the kernels of the restrictions to each `K j`.
* `IntermediateField.restrictNormalHomISupPi_injective`: an automorphism of the compositum is
  determined by its restrictions to the members.
* `IntermediateField.biSup_eq_iSup_of_injective`: Galois members `K j`, `j ∈ J`, whose
  restrictions already determine automorphisms of the compositum generate it.
* `IntermediateField.exists_biSup_eq_iSup_and_bijective_restrictNormalHomBiSupPi`: for Galois
  members that are trivial or have simple Galois group, some subfamily of nontrivial members
  generates the compositum, and restriction to it is bijective.
* `IntermediateField.linearDisjoint_biSup_of_surjective`: for finite Galois members, over a
  subfamily onto whose Galois groups restriction is surjective, the composita of disjoint parts
  are linearly disjoint.
* `IntermediateField.exists_biSup_eq_iSup_and_nonempty_mulEquiv_and_linearDisjoint`: when every
  nontrivial member is finite Galois with Galois group isomorphic to a simple group `Δ`, for such
  a subfamily `J` restriction is bijective, the Galois group of the compositum is `Δ ^ J`, and the
  composita of disjoint parts of `J` are linearly disjoint.

## References

* [L. Qian, *Potential automorphy for GL_n*, Invent. Math. 231 (2023), 1239–1275], proof of
  Lemma 2.6(2).
-/

public section

namespace IntermediateField

variable {k Ω ι : Type*} [Field k] [Field Ω] [Algebra k Ω]

section Normal

variable (K : ι → IntermediateField k Ω) [∀ i, Normal k (K i)]

/-- Restriction from the compositum `⨆ i, K i` of a family of normal subextensions to each
member `K i`. Its injectivity is `IntermediateField.restrictNormalHomISupPi_injective`; for two
fields this is Mathlib's `IntermediateField.restrictNormalHomSupProd`. -/
noncomputable def restrictNormalHomISupPi : Gal(↥(⨆ i, K i)/k) →* ((i : ι) → Gal(K i/k)) :=
  MonoidHom.pi fun i ↦ (inclusion (le_iSup K i)).restrictNormalHom

/-- The `i`-th component of `restrictNormalHomISupPi K σ` is the restriction of `σ` along the
inclusion of `K i` into the compositum. -/
theorem restrictNormalHomISupPi_apply (σ : Gal(↥(⨆ i, K i)/k)) (i : ι) :
    restrictNormalHomISupPi K σ i = (inclusion (le_iSup K i)).restrictNormalHom σ :=
  (rfl)

/-- The restriction of `σ` to `K i` agrees with `σ` on `K i`. -/
@[simp]
theorem coe_restrictNormalHomISupPi_apply_apply (σ : Gal(↥(⨆ i, K i)/k)) (i : ι) (x : K i) :
    ((restrictNormalHomISupPi K σ i x : K i) : Ω) = σ (inclusion (le_iSup K i) x) :=
  congrArg Subtype.val ((inclusion (le_iSup K i)).restrictNormalHom_commutes σ x)

/-- Restriction from the compositum `⨆ i, K i` to the members `K j` with `j` in a set `J`: the
components of `restrictNormalHomISupPi K` indexed by `J`. -/
noncomputable def restrictNormalHomBiSupPi (J : Set ι) :
    Gal(↥(⨆ i, K i)/k) →* ((j : J) → Gal(K j/k)) :=
  MonoidHom.pi fun j : J ↦ (inclusion (le_iSup K (j : ι))).restrictNormalHom

/-- The `j`-th component of `restrictNormalHomBiSupPi K J σ` is that of
`restrictNormalHomISupPi K σ`. -/
@[simp]
theorem restrictNormalHomBiSupPi_apply (J : Set ι) (σ : Gal(↥(⨆ i, K i)/k)) (j : J) :
    restrictNormalHomBiSupPi K J σ j = restrictNormalHomISupPi K σ j :=
  (rfl)

/-- The kernel of `restrictNormalHomBiSupPi K J` is the intersection of the kernels of the
restrictions to the `K j` with `j ∈ J`. -/
theorem ker_restrictNormalHomBiSupPi (J : Set ι) :
    (restrictNormalHomBiSupPi K J).ker =
      ⨅ j ∈ J, (inclusion (le_iSup K j)).restrictNormalHom.ker := by
  rw [restrictNormalHomBiSupPi, MonoidHom.ker_pi, iInf_subtype'' J fun j ↦
    (inclusion (le_iSup K j)).restrictNormalHom.ker]

variable {K}

/-- An automorphism of the compositum that restricts to the identity on `K i` for every `i ∈ I`
fixes every element of the compositum of those `K i`. -/
theorem apply_eq_self_of_restrictNormalHomISupPi_eq_one {σ : Gal(↥(⨆ i, K i)/k)} {I : Set ι}
    (hσ : ∀ i ∈ I, restrictNormalHomISupPi K σ i = 1) {z : ↥(⨆ i, K i)}
    (hz : (z : Ω) ∈ ⨆ i ∈ I, K i) : σ z = z := by
  -- The elements of the compositum fixed by `σ`, as an intermediate field of `Ω`.
  let F : IntermediateField k Ω := (fixedField (Subgroup.zpowers σ)).map (⨆ i, K i).val
  have hle : (⨆ i ∈ I, K i) ≤ F := iSup₂_le fun i hi x hx ↦ by
    refine ⟨inclusion (le_iSup K i) ⟨x, hx⟩, (mem_fixedField_zpowers_iff σ _).2 ?_, rfl⟩
    ext
    simpa [hσ i hi] using (coe_restrictNormalHomISupPi_apply_apply K σ i ⟨x, hx⟩).symm
  obtain ⟨y, hy, hyz⟩ := hle hz
  obtain rfl : y = z := Subtype.ext hyz
  exact (mem_fixedField_zpowers_iff σ y).1 hy

variable (K) in
/-- **Restriction to the members of a compositum is injective**: an automorphism of `⨆ i, K i`
is determined by its restrictions to the `K i`. -/
theorem restrictNormalHomISupPi_injective : Function.Injective (restrictNormalHomISupPi K) := by
  refine (injective_iff_map_eq_one _).2 fun σ hσ ↦ AlgEquiv.ext fun z ↦ ?_
  exact apply_eq_self_of_restrictNormalHomISupPi_eq_one (I := Set.univ)
    (fun i _ ↦ congrFun hσ i) (by simp)

end Normal

section Galois

variable {K : ι → IntermediateField k Ω} [∀ i, IsGalois k (K i)]

/-- **A determining subfamily generates the compositum.** If automorphisms of the compositum of
a family of Galois subextensions are already determined by their restrictions to the `K j` with
`j ∈ J`, then those `K j` generate the compositum. -/
theorem biSup_eq_iSup_of_injective {J : Set ι}
    (hJ : Function.Injective (restrictNormalHomBiSupPi K J)) :
    (⨆ j ∈ J, K j) = ⨆ i, K i := by
  have hJL : (⨆ j ∈ J, K j) ≤ ⨆ i, K i := iSup₂_le fun j _ ↦ le_iSup K j
  refine le_antisymm hJL fun x hx ↦ ?_
  -- Inside the Galois extension `⨆ i, K i`, the field generated by the `K j` has trivial
  -- fixing subgroup, so it is everything.
  have : IsGalois k ↥(⨆ i, K i) := ⟨⟩
  let E : IntermediateField k ↥(⨆ i, K i) := restrict hJL
  have hfix : E.fixingSubgroup = ⊥ := by
    refine (Subgroup.eq_bot_iff_forall _).2 fun σ hσ ↦ hJ (funext fun j ↦ ?_)
    rw [map_one, Pi.one_apply, restrictNormalHomBiSupPi_apply]
    refine AlgEquiv.ext fun y ↦ Subtype.ext ?_
    rw [coe_restrictNormalHomISupPi_apply_apply, AlgEquiv.one_apply]
    have hyE : inclusion (le_iSup K j) y ∈ E :=
      (mem_restrict _ _).2 (le_iSup₂ (f := fun j _ ↦ K j) j j.property y.property)
    exact congrArg Subtype.val (hσ ⟨_, hyE⟩)
  have hE : E = ⊤ := by
    rw [← InfiniteGalois.fixedField_fixingSubgroup E, hfix, fixedField_bot]
  have hxE : (⟨x, hx⟩ : ↥(⨆ i, K i)) ∈ E := by
    rw [hE]
    exact mem_top
  exact (mem_restrict hJL ⟨x, hx⟩).1 hxE

/-- **Composita of Galois extensions with simple Galois groups.** Let `K i` be finitely many
Galois subextensions of `Ω / k`, each equal to `k` or with simple Galois group. Then there is a
set `J` of indices with `K j ≠ k` for `j ∈ J` such that the `K j`, `j ∈ J`, generate the
compositum `⨆ i, K i` and restriction identifies `Gal((⨆ i, K i) / k)` with
`∏ j ∈ J, Gal(K j / k)`. -/
theorem exists_biSup_eq_iSup_and_bijective_restrictNormalHomBiSupPi [Finite ι]
    (hK : ∀ i, K i = ⊥ ∨ IsSimpleGroup Gal(K i/k)) :
    ∃ J : Set ι, (∀ j ∈ J, K j ≠ ⊥) ∧ (⨆ j ∈ J, K j) = ⨆ i, K i ∧
      Function.Bijective (restrictNormalHomBiSupPi K J) := by
  obtain ⟨J, hJnt, hJker, hJsurj⟩ := MonoidHom.exists_set_iInf_ker_eq_and_surjective_pi
    (fun i ↦ (inclusion (le_iSup K i)).restrictNormalHom)
    (fun i ↦ AlgHom.restrictNormalHom_surjective _)
    (fun i ↦ (hK i).imp subsingleton_algEquiv_of_eq_bot id)
  -- Restriction to the `K j`, `j ∈ J`, is injective: its kernel is the intersection of all the
  -- restriction kernels, which is trivial.
  have hinj : Function.Injective (restrictNormalHomBiSupPi K J) := by
    rw [injective_iff_map_eq_one]
    refine fun σ hσ ↦ restrictNormalHomISupPi_injective K (funext fun i ↦ ?_)
    have hmem : σ ∈ ⨅ i, (inclusion (le_iSup K i)).restrictNormalHom.ker := by
      rw [← hJker, ← ker_restrictNormalHomBiSupPi]
      exact hσ
    rw [map_one, Pi.one_apply, restrictNormalHomISupPi_apply]
    exact Subgroup.mem_iInf.1 hmem i
  refine ⟨J, fun j hj h ↦ ?_, biSup_eq_iSup_of_injective hinj, hinj, hJsurj⟩
  exact not_nontrivial_iff_subsingleton.2 (subsingleton_algEquiv_of_eq_bot h) (hJnt j hj)

/-- **Disjoint parts of an independent subfamily are linearly disjoint.** If restriction from the
compositum of finitely many finite Galois subextensions `K i` to the members `K j`, `j ∈ J`, is
surjective, then for disjoint `I, I' ⊆ J` the composita `⨆ i ∈ I, K i` and `⨆ i ∈ I', K i` are
linearly disjoint over `k`. -/
theorem linearDisjoint_biSup_of_surjective [Finite ι] [∀ i, FiniteDimensional k (K i)]
    {J : Set ι} (hJ : Function.Surjective (restrictNormalHomBiSupPi K J))
    {I I' : Set ι} (hI : I ⊆ J) (hI' : I' ⊆ J) (hII' : Disjoint I I') :
    (⨆ i ∈ I, K i : IntermediateField k Ω).LinearDisjoint
      (⨆ i ∈ I', K i : IntermediateField k Ω) := by
  classical
  have : IsGalois k ↥(⨆ i, K i) := ⟨⟩
  have : IsGalois k ↥(⨆ i ∈ I, K i) := iSup_subtype'' I K ▸ (⟨⟩ : IsGalois k ↥(⨆ i : I, K i))
  have hfin (S : Set ι) : FiniteDimensional k ↥(⨆ i ∈ S, K i) :=
    iSup_subtype'' S K ▸ inferInstance
  refine LinearDisjoint.of_inf_eq_bot (eq_bot_iff.2 fun x hx ↦ ?_)
  -- An element of both composita is fixed by every automorphism of the compositum.
  let z : ↥(⨆ i, K i) := ⟨x, (iSup₂_le fun i _ ↦ le_iSup K i) hx.1⟩
  suffices hz : z ∈ (⊥ : IntermediateField k ↥(⨆ i, K i)) by
    obtain ⟨c, hc⟩ := mem_bot.1 hz
    exact mem_bot.2 ⟨c, congrArg Subtype.val hc⟩
  refine (InfiniteGalois.mem_bot_iff_fixed z).2 fun σ ↦ ?_
  -- Write `σ = σ₁ * σ₂ * κ`, with `σ₁` trivial on the `K j` for `j ∈ J \ I`, `σ₂` trivial on the
  -- `K j` for `j ∈ I`, and `κ` trivial on every `K j` with `j ∈ J`.
  obtain ⟨σ₁, h₁⟩ := hJ fun j ↦ if (j : ι) ∈ I then restrictNormalHomISupPi K σ j else 1
  obtain ⟨σ₂, h₂⟩ := hJ fun j ↦ if (j : ι) ∈ I then 1 else restrictNormalHomISupPi K σ j
  have hκ (i : ι) (hi : i ∈ J) : restrictNormalHomISupPi K ((σ₁ * σ₂)⁻¹ * σ) i = 1 := by
    have h₁i := congrFun h₁ ⟨i, hi⟩
    have h₂i := congrFun h₂ ⟨i, hi⟩
    rw [restrictNormalHomBiSupPi_apply] at h₁i h₂i
    by_cases hiI : i ∈ I <;> simp [h₁i, h₂i, hiI]
  have hzκ : ((σ₁ * σ₂)⁻¹ * σ) z = z :=
    apply_eq_self_of_restrictNormalHomISupPi_eq_one (fun i hi ↦ hκ i (hI hi)) hx.1
  have hz₂ : σ₂ z = z := apply_eq_self_of_restrictNormalHomISupPi_eq_one (fun i hi ↦ by
    simpa [hi] using congrFun h₂ ⟨i, hI hi⟩) hx.1
  have hz₁ : σ₁ z = z := apply_eq_self_of_restrictNormalHomISupPi_eq_one (fun i hi ↦ by
    simpa [hII'.notMem_of_mem_right hi] using congrFun h₁ ⟨i, hI' hi⟩) hx.2
  rw [← mul_inv_cancel_left (σ₁ * σ₂) σ, AlgEquiv.mul_apply, hzκ, AlgEquiv.mul_apply, hz₂, hz₁]

/-- **The Galois group of a compositum of `Δ`-extensions is a power of `Δ`.** Let `K i` be
finitely many finite Galois subextensions of `Ω / k`, each equal to `k` or with Galois group
isomorphic to a fixed simple group `Δ`. Then for some set `J` of indices the `K j`, `j ∈ J`,
generate the compositum, restriction identifies its Galois group with `∏ j ∈ J, Gal(K j / k)`,
which is isomorphic to `Δ ^ J`, and for disjoint `I, I' ⊆ J` the composita `⨆ i ∈ I, K i` and
`⨆ i ∈ I', K i` are linearly disjoint over `k`. -/
theorem exists_biSup_eq_iSup_and_nonempty_mulEquiv_and_linearDisjoint [Finite ι]
    [∀ i, FiniteDimensional k (K i)] {Δ : Type*} [Group Δ] [IsSimpleGroup Δ]
    (hK : ∀ i, K i = ⊥ ∨ Nonempty (Gal(K i/k) ≃* Δ)) :
    ∃ J : Set ι, (⨆ j ∈ J, K j) = ⨆ i, K i ∧ Function.Bijective (restrictNormalHomBiSupPi K J) ∧
      Nonempty (Gal(↥(⨆ i, K i)/k) ≃* (J → Δ)) ∧
      ∀ I I' : Set ι, I ⊆ J → I' ⊆ J → Disjoint I I' →
        (⨆ i ∈ I, K i : IntermediateField k Ω).LinearDisjoint
          (⨆ i ∈ I', K i : IntermediateField k Ω) := by
  obtain ⟨J, hJne, hJ, hbij⟩ := exists_biSup_eq_iSup_and_bijective_restrictNormalHomBiSupPi
    fun i ↦ (hK i).imp id fun ⟨e⟩ ↦ e.isSimpleGroup
  refine ⟨J, hJ, hbij, ⟨?_⟩,
    fun I I' hI hI' hII' ↦ linearDisjoint_biSup_of_surjective hbij.2 hI hI' hII'⟩
  -- Restriction identifies the Galois group with `∏ j ∈ J, Gal(K j / k)`, and each factor with
  -- `Δ`, since `K j ≠ k`.
  exact (MulEquiv.ofBijective (restrictNormalHomBiSupPi K J) hbij).trans
    (MulEquiv.piCongrRight fun j ↦ ((hK j).resolve_left (hJne j j.property)).some)

end Galois

end IntermediateField
